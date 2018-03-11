extern crate num;
extern crate regex;

use prolog::ordered_float::*;
use prolog::parser::num::bigint::BigInt;
use prolog::parser::num::Signed;
use self::regex::Regex;

use prolog::ast::*;
use prolog::parser::fullbufreader::*;
use prolog::tabled_rc::*;

use std::io::Read;
use std::rc::Rc;
use std::str;

#[derive(PartialEq)]
pub enum Token {
    Constant(Constant),
    Var(Rc<Atom>),
    Open,           // '('
    OpenCT,         // '/*'
    Close,          // ')'
    OpenList,       // '['
    CloseList,      // ']'
    OpenCurly,      // '{'
    CloseCurly,     // '}'
    HeadTailSeparator, // '|'
    Comma,          // ','
    End
}

macro_rules! regex {
    ($expr:expr) => (
        Regex::new($expr).unwrap()
    )
}

#[inline]
fn is_layout(x: char) -> bool {
    // last two are vertical tab and formfeed respectively.
    x == ' ' || x == '\n' || x == '\t' || x == '\x0B' || x == '\x0C'
}

pub struct Lexer<R> {
    atom_tbl: TabledData<Atom>,
    reader: FullBufReader<R>,
    line_num: usize,
}

impl<R: Read> Lexer<R> {
    pub fn new(atom_tbl: TabledData<Atom>, src: R) -> Self {
        Lexer { atom_tbl,
                reader: FullBufReader::with_capacity(LEXER_BUF_SIZE, src),
                line_num: 0 }
    }

    fn skip_char(&mut self) -> Result<char, ParserError> {
        let mut c = [0];
        try!(self.reader.read(&mut c));

        if (c[0] as char) == '\n' {
            self.line_num += 1;
        }

        Ok(c[0] as char)
    }

    pub fn eof(&mut self) -> bool {
        if let Ok(buf) = self.reader.fill_buf() {
            buf.len() == 0
        } else {
            false
        }
    }

    pub fn lookahead_char(&mut self, index: usize) -> Result<char, ParserError> {
        match self.reader.fill_buf() {
            Ok(buf) if index < buf.len() => Ok(buf[index] as char),
            Ok(_)  => Err(ParserError::UnexpectedEOF),
            Err(e) => Err(ParserError::from(e))
        }
    }

    // single_line_comment and bracketed_comment have elaborate loops
    // because comments are unbounded in length (they are not tokens).
    fn single_line_comment(&mut self) -> Result<(), ParserError>
    {
        let needle;
        try!(self.skip_char());

        loop {
            {
                let buf = try!(self.reader.fill_buf());

                if buf.len() > 0 {
                    let buf = try!(str::from_utf8(&buf));

                    if let Some(n) = buf.find('\n') {
                        needle = n + 1;
                        break;
                    }
                } else {
                    return Err(ParserError::UnexpectedEOF);
                }
            }

            self.reader.consume(LEXER_BUF_SIZE);
        }

        self.reader.consume(needle);
        Ok(())
    }

    fn bracketed_comment(&mut self) -> Result<bool, ParserError> {
        let needle;

        // we know that self.lookahead_char(0) == Ok('/').
        match self.lookahead_char(1) {
            Ok(c) if c != '*' => return Ok(false),
            Err(err) => return Err(err),
            _ => {}
        };

        loop {
            {
                let buf = try!(self.reader.fill_buf());
                let buf = try!(str::from_utf8(buf));

                if buf.len() > 2 {
                    if let Some(n) = buf[2..].find("*/") {
                        needle = n + 4; // consume /* and */.
                        break;
                    }
                } else {
                    return Err(ParserError::UnexpectedEOF);
                }
            }

            self.reader.consume(LEXER_BUF_SIZE);
        }

        self.reader.consume(needle);
        Ok(true)
    }

    fn buf_to_string(&mut self) -> Result<String, ParserError> {
        self.reader.fill_buf()
            .map(|buf| buf.iter().map(|b| *b as char).collect())
            .map_err(|err| ParserError::from(err))
    }

    fn try_consume<F>(&mut self, re: &Regex, consumer: F) -> Result<Token, ParserError>
        where F: FnOnce(&str) -> Result<Token, ParserError>
    {
        let buf = try!(self.buf_to_string());

        re.find(buf.as_str())
          .map_or_else(|| Err(ParserError::FailedMatch(String::from(re.as_str()))),
                       |mat| {
                           self.reader.consume(mat.end());
                           consumer(&buf[0 .. mat.end()])
                       })
    }

    fn retry_consume<F>(&mut self, e: ParserError, r: &Regex, consumer: F)
                        -> Result<Token, ParserError>
        where F: FnOnce(&str) -> Result<Token, ParserError>
    {
        match e {
            ParserError::FailedMatch(_) => self.try_consume(r, consumer),
            e => Err(e)
        }
    }

    fn variable_token(&mut self) -> Result<Token, ParserError> {
        lazy_static! {
            static ref RE: Regex = regex!(r"^([A-Z]|_)[A-Za-z0-9]*");
        }

        self.try_consume(&RE, |s| Ok(Token::Var(rc_atom!(s))))
    }

    fn name_token(&mut self, c: char) -> Result<Token, ParserError> {
        let atom_tbl = self.atom_tbl.clone();
        
        lazy_static! {
            static ref ID_RE: Regex = regex!(r"^[a-z][A-Za-z0-9_]*");
            static ref GRAPHIC_RE: Regex = regex!(r"^[\\\-\^#$&*+o./:<=>?@~]+");
        }

        match c {
            '!' => {
                try!(self.skip_char());
                Ok(Token::Constant(atom!("!", self.atom_tbl)))
            },
            ';' => {
                try!(self.skip_char());
                Ok(Token::Constant(atom!(";", self.atom_tbl)))
            },
            _   =>
                self.try_consume(&ID_RE, |s| Ok(Token::Constant(atom!(s, atom_tbl))))
                    .or_else(|e| self.retry_consume(e, &GRAPHIC_RE, |s| {
                        Ok(Token::Constant(atom!(s.clone(), atom_tbl)))
                    }))
        }
    }

    fn char_code_list_token(&mut self) -> Result<Token, ParserError> {
        lazy_static! {
            static ref RE: Regex = regex!(r#"^"(?:[^"\\]|\\.)*""#);
        }

        self.try_consume(&RE, |s| Ok(Token::Constant(Constant::String(rc_atom!(s)))))
    }

    fn number_token(&mut self) -> Result<Token, ParserError> {
        lazy_static! {
            static ref FLOAT_NUM: Regex = regex!(r"^-?[0-9]*\.[0-9]+([eE][+-]?[0-9]+)?");
            static ref INT_NUM: Regex = regex!(r"^-?(0x[0-9A-Fa-f]+|0o[0-7]+|0b[01]+|[0-9]+)");
        }

        self.try_consume(&FLOAT_NUM, |s| {
            let s = s.parse::<f64>()?;
            Ok(Token::Constant(Constant::Number(Number::Float(OrderedFloat(s)))))
        }).or_else(|e|
            self.retry_consume(e, &INT_NUM, |s| {                
                let to_neg = s.chars().next() == Some('-');                
                let (s, radix) = if s.len() > 1 {                    
                    let offset = if s.len() > 2 {
                        if to_neg { 1 } else { 0 }
                    } else {
                        0
                    };
                    
                    match &s[0 + offset..2 + offset] {
                        "0x" => (&s[2 + offset..], 16),
                        "0o" => (&s[2 + offset..], 8),
                        "0b" => (&s[2 + offset..], 2),
                        _ => (s, 10)
                    }
                } else {
                    (s, 10)
                };
               
                match BigInt::parse_bytes(s.as_bytes(), radix) {
                    Some(num) =>
                        if to_neg && num.is_positive() {
                            Ok(Token::Constant(integer!(-num)))
                        } else {
                            Ok(Token::Constant(integer!(num)))
                        },
                    None => Err(ParserError::ParseBigInt)
                }
            }))
    }

    fn scan_for_layout(&mut self) -> Result<bool, ParserError> {
        let mut layout_inserted = false;
        let mut more_layout = true;

        loop {
            let cr = self.lookahead_char(0);

            match cr {
                Ok(c) if is_layout(c) => {
                    try!(self.skip_char());
                    layout_inserted = true;
                },
                Ok(c) if c == '%' => {
                    try!(self.single_line_comment());
                    layout_inserted = true;
                },
                Ok(c) if c == '/' => {
                    if try!(self.bracketed_comment()) {
                        layout_inserted = true;
                    } else {
                        more_layout = false;
                    }
                },
                _ => more_layout = false
            };

            if !more_layout {
                break;
            }
        }

        Ok(layout_inserted)
    }

    pub fn next_token(&mut self) -> Result<Token, ParserError> {
        let layout_inserted = try!(self.scan_for_layout());
        let cr = self.lookahead_char(0);

        match cr {
            Ok(c) => {
                if c.is_uppercase() || c == '_' {
                    return self.variable_token();
                }

                if c == ',' {
                    try!(self.skip_char());
                    return Ok(Token::Comma);
                }

                if c == ')' {
                    try!(self.skip_char());
                    return Ok(Token::Close);
                }

                if c == '(' {
                    try!(self.skip_char());
                    return Ok(if layout_inserted { Token::Open }
                              else { Token::OpenCT });
                }

                if c == '.' {
                    let c = match self.lookahead_char(1) {
                        Ok(c) => c,
                        Err(ParserError::UnexpectedEOF) => {
                            try!(self.skip_char());
                            return Ok(Token::End);
                        },
                        Err(e) => return Err(e)
                    };

                    if is_layout(c) || c == '%' {
                        try!(self.skip_char());

                        if c == '\n' {
                            try!(self.skip_char());
                        }

                        return Ok(Token::End);
                    }
                }

                if c == '-' || c.is_digit(10) {
                    return self.number_token()
                        .or_else(|e| self.name_token(c).or(Err(e)));
                }

                if c == ']' {
                    try!(self.skip_char());
                    return Ok(Token::CloseList);
                }

                if c == '[' {
                    try!(self.skip_char());
                    return Ok(Token::OpenList);
                }

                if c == '|' {
                    try!(self.skip_char());
                    return Ok(Token::HeadTailSeparator);
                }

                if c == '{' {
                    try!(self.skip_char());
                    return Ok(Token::OpenCurly);
                }

                if c == '}' {
                    try!(self.skip_char());
                    return Ok(Token::CloseCurly);
                }

                if c == '"' {
                    return self.char_code_list_token();
                }

                self.name_token(c)
            },
            Err(e) => Err(e)
        }
    }
}
