use prolog::ast::*;
use prolog::num::*;
use prolog::parser::parser::*;
use prolog::tabled_rc::*;
use prolog::similarity::*;

use std::collections::{HashSet, VecDeque, HashMap};
use std::cell::Cell;
use std::io::Read;
//use prolog::ast::Constant::String;


fn setup_fact(term: Term) -> Result<Term, ParserError>
{
    match term {
        Term::Clause(..) | Term::Constant(_, Constant::Atom(_)) =>
            Ok(term),
        _ =>
            Err(ParserError::InadmissibleFact)
    }
}

fn setup_op_decl(mut terms: Vec<Box<Term>>) -> Result<OpDecl, ParserError>
{
    let name = match *terms.pop().unwrap() {
        Term::Constant(_, Constant::Atom(name)) => name,
        _ => return Err(ParserError::InconsistentEntry)
    };

    let spec = match *terms.pop().unwrap() {
        Term::Constant(_, Constant::Atom(name)) => name,
        _ => return Err(ParserError::InconsistentEntry)
    };

    let prec = match *terms.pop().unwrap() {
        Term::Constant(_, Constant::Number(Number::Integer(bi))) =>
            match bi.to_usize() {
                Some(n) if n <= 1200 => n,
                _ => return Err(ParserError::InconsistentEntry)
            },
        _ => return Err(ParserError::InconsistentEntry)
    };

    match spec.as_str() {
        "xfx" => Ok(OpDecl(prec, XFX, name)),
        "xfy" => Ok(OpDecl(prec, XFY, name)),
        "yfx" => Ok(OpDecl(prec, YFX, name)),
        "fx"  => Ok(OpDecl(prec, FX, name)),
        "fy"  => Ok(OpDecl(prec, FY, name)),
        "xf"  => Ok(OpDecl(prec, XF, name)),
        "yf"  => Ok(OpDecl(prec, YF, name)),
        _     => Err(ParserError::InconsistentEntry)
    }
}

fn setup_predicate_export(mut term: Term) -> Result<PredicateKey, ParserError>
{
    match term {
        Term::Clause(_, ref name, ref mut terms, Some(Fixity::In))
            if name.as_str() == "/" && terms.len() == 2 => {
                let arity = *terms.pop().unwrap();
                let name  = *terms.pop().unwrap();

                let arity = arity.to_constant().and_then(|c| c.to_integer())
                    .and_then(|n| if !n.is_negative() { n.to_usize() } else { None })
                    .ok_or(ParserError::InvalidModuleExport)?;

                let name = name.to_constant().and_then(|c| c.to_atom())
                    .ok_or(ParserError::InvalidModuleExport)?;

                Ok((name, arity))
            },
        _ => Err(ParserError::InvalidModuleExport)
    }
}

fn setup_module_decl(mut terms: Vec<Box<Term>>) -> Result<ModuleDecl, ParserError>
{
    let mut export_list = *terms.pop().unwrap();
    let name = terms.pop().unwrap().to_constant().and_then(|c| c.to_atom())
        .ok_or(ParserError::InvalidModuleDecl)?;

    let mut exports = Vec::new();

    while let Term::Cons(_, t1, t2) = export_list {
        exports.push(setup_predicate_export(*t1)?);
        export_list = *t2;
    }

    if export_list.to_constant() != Some(Constant::EmptyList) {
        Err(ParserError::InvalidModuleDecl)
    } else {
        Ok(ModuleDecl { name, exports })
    }
}

fn setup_use_module_decl(mut terms: Vec<Box<Term>>) -> Result<ClauseName, ParserError>
{
    match *terms.pop().unwrap() {
        Term::Clause(_, ref name, ref mut terms, None)
            if name.as_str() == "library" && terms.len() == 1 => {
                terms.pop().unwrap().to_constant()
                    .and_then(|c| c.to_atom())
                    .ok_or(ParserError::InvalidUseModuleDecl)
            },
        _ => Err(ParserError::InvalidUseModuleDecl)
    }
}

type UseModuleExport = (ClauseName, Vec<PredicateKey>);

fn setup_qualified_import(mut terms: Vec<Box<Term>>) -> Result<UseModuleExport, ParserError>
{
    let mut export_list = *terms.pop().unwrap();
    let name = match *terms.pop().unwrap() {
        Term::Clause(_, ref name, ref mut terms, None)
            if name.as_str() == "library" && terms.len() == 1 => {
                terms.pop().unwrap().to_constant()
                    .and_then(|c| c.to_atom())
                    .ok_or(ParserError::InvalidUseModuleDecl)
            },
        _ => Err(ParserError::InvalidUseModuleDecl)
    }?;

    let mut exports = Vec::new();

    while let Term::Cons(_, t1, t2) = export_list {
        exports.push(setup_predicate_export(*t1)?);
        export_list = *t2;
    }

    if export_list.to_constant() != Some(Constant::EmptyList) {
        Err(ParserError::InvalidModuleDecl)
    } else {
        Ok((name, exports))
    }
}

fn setup_declaration(term: Term) -> Result<Declaration, ParserError>
{
    match term {
        Term::Clause(_, name, terms, _) =>
            if name.as_str() == "op" && terms.len() == 3 {
                Ok(Declaration::Op(setup_op_decl(terms)?))
            } else if name.as_str() == "module" && terms.len() == 2 {
                Ok(Declaration::Module(setup_module_decl(terms)?))
            } else if name.as_str() == "use_module" && terms.len() == 1 {
                Ok(Declaration::UseModule(setup_use_module_decl(terms)?))
            } else if name.as_str() == "use_module" && terms.len() == 2 {
                let (name, exports) = setup_qualified_import(terms)?;
                Ok(Declaration::UseQualifiedModule(name, exports))
            } else {
                Err(ParserError::InconsistentEntry)
            },
        _ => return Err(ParserError::InconsistentEntry)
    }
}

fn is_consistent(tl: &TopLevel, clauses: &Vec<PredicateClause>) -> bool
{
    match clauses.first() {
        Some(ref cl) => tl.name() == cl.name() && tl.arity() == cl.arity(),
        None => true
    }
}

pub fn deque_to_packet(mut deque: VecDeque<TopLevel>) -> Result<TopLevelPacket, ParserError>
{
    match deque.pop_front() {
        Some(head) =>
            Ok(match head {
                TopLevel::Query(query) => TopLevelPacket::Query(query, Vec::from(deque)),
                tl => TopLevelPacket::Decl(tl, Vec::from(deque))
            }),
        None => Err(ParserError::ExpectedRel)
    }
}

pub fn merge_clauses(tls: &mut VecDeque<TopLevel>) -> Result<TopLevel, ParserError>
{
    let mut clauses = vec![];
    while let Some(tl) = tls.pop_front() {
        match tl {
            TopLevel::Query(_) if clauses.is_empty() && tls.is_empty() =>
                return Ok(tl),
            TopLevel::Declaration(_) if clauses.is_empty() =>
                return Ok(tl),
            TopLevel::Query(_) =>
                return Err(ParserError::InconsistentEntry),
            TopLevel::Fact(_, _) if is_consistent(&tl, &clauses) =>
                if let TopLevel::Fact(fact, ad) = tl {
                    let clause = PredicateClause::Fact(fact, 1.0);
                    clauses.push(clause);
                },
            TopLevel::Rule(_, _) if is_consistent(&tl, &clauses) =>
                if let TopLevel::Rule(rule, ad) = tl {
                    let clause = PredicateClause::Rule(rule, 1.0);
                    clauses.push(clause);
                },
            _ => {
                tls.push_front(tl);
                break;
            }
        }
    }

    if clauses.is_empty() {
        Err(ParserError::InconsistentEntry)
    } else {
        Ok(TopLevel::Predicate(clauses))
    }
}

fn unfold_by_str_once(term: &mut Term, s: &str) -> Option<(Term, Term)>
{
    if let &mut Term::Clause(_, ref name, ref mut subterms, _) = term {
        if name.as_str() == s && subterms.len() == 2 {
            let snd = *subterms.pop().unwrap();
            let fst = *subterms.pop().unwrap();

            return Some((fst, snd));
        }
    }

    None
}

fn unfold_by_str(mut term: Term, s: &str) -> Vec<Term>
{
    let mut terms = vec![];

    while let Some((fst, snd)) = unfold_by_str_once(&mut term, s) {
        terms.push(fst);
        term = snd;
    }

    terms.push(term);
    terms
}

pub enum TopLevelPacket {
    Query(Vec<QueryTerm>, Vec<TopLevel>),
    Decl(TopLevel, Vec<TopLevel>)
}

pub struct TopLevelWorker<R> {
    queue: VecDeque<VecDeque<Term>>,
    pub parser: Parser<R>,
    similarity_tbl: SimilarityTable
}

impl<R: Read> TopLevelWorker<R> {
    pub fn new(inner: R, atom_tbl: TabledData<Atom>, similarity_tbl: SimilarityTable) -> Self {
        let parser = Parser::new(inner, atom_tbl);
        TopLevelWorker { queue: VecDeque::new(), parser, similarity_tbl}
    }

    fn compute_head(&self, term: &Term) -> Vec<Term>
    {
        let mut vars = HashSet::new();

        for term in term.post_order_iter() {
            if let TermRef::Var(_, _, v) = term {
                vars.insert(v.clone());
            }
        }

        vars.into_iter()
            .map(|v| Term::Var(Cell::default(), v))
            .collect()
    }

    fn fabricate_rule_body(&self, vars: &Vec<Term>, body_term: Term) -> Term
    {
        let vars_of_head = vars.iter().cloned().map(Box::new).collect();
        let head_term = Term::Clause(Cell::default(), clause_name!(""), vars_of_head, None);

        let rule = vec![Box::new(head_term), Box::new(body_term)];
        let turnstile = clause_name!(":-");

        Term::Clause(Cell::default(), turnstile, rule, None)
    }

    // the terms form the body of the rule. We create a head, by
    // gathering variables from the body of terms and recording them
    // in the head clause.
    fn fabricate_rule(&self, body_term: Term) -> (JumpStub, VecDeque<Term>)
    {
        // collect the vars of body_term into a head, return the num_vars
        // (the arity) as well.
        let vars = self.compute_head(&body_term);
        let rule = self.fabricate_rule_body(&vars, body_term);

        (vars, VecDeque::from(vec![rule]))
    }

    fn fabricate_predicate(&self, body_term: Term) -> (JumpStub, VecDeque<Term>)
    {
        let mut results = VecDeque::new();
        let vars = self.compute_head(&body_term);

        unfold_by_str(body_term, ";").into_iter()
            .map(|term| self.fabricate_rule_body(&vars, term))
            .fold((), |_, item| results.push_back(item));

        (vars, results)
    }

    fn fabricate_if_then(&self, prec: Term, conq: Term) -> (JumpStub, VecDeque<Term>)
    {
        let mut prec_seq = unfold_by_str(prec, ",");
        let comma_sym    = clause_name!(",");
        let cut_sym      = clause_name!("!");

        prec_seq.push(Term::Constant(Cell::default(), Constant::Atom(cut_sym)));
        prec_seq.append(&mut unfold_by_str(conq, ","));

        let back_term  = Box::new(prec_seq.pop().unwrap());
        let front_term = Box::new(prec_seq.pop().unwrap());

        let mut body_term = Term::Clause(Cell::default(), comma_sym.clone(),
                                         vec![front_term, back_term], None);

        while let Some(prec) = prec_seq.pop() {
            body_term = Term::Clause(Cell::default(), comma_sym.clone(),
                                     vec![Box::new(prec), Box::new(body_term)],
                                     None);
        }

        self.fabricate_rule(body_term)
    }

    fn to_query_term(&mut self, term: Term) -> Result<QueryTerm, ParserError>
    {
        match term {
            Term::Constant(r, Constant::Atom(name)) =>
                if name.as_str() == "!" {
                    Ok(QueryTerm::Cut)
                } else {
                    Ok(QueryTerm::Clause(r, ClauseType::Named(name), vec![]))
                },
            Term::Clause(r, name, mut terms, fixity) =>
                if let Some(inlined_ct) = InlinedClauseType::from(name.as_str(), terms.len()) {
                    Ok(QueryTerm::Clause(r, ClauseType::Inlined(inlined_ct), terms))
                } else if name.as_str() == "," {
                    if terms.len() == 2 {
                        let term = Term::Clause(r, name, terms, fixity);
                        let (stub, clause) = self.fabricate_rule(term);

                        self.queue.push_back(clause);
                        Ok(QueryTerm::Jump(stub))
                    } else {
                        Err(ParserError::BuiltInArityMismatch(","))
                    }
                } else if name.as_str() == ";" {
                    if terms.len() == 2 {
                        let term = Term::Clause(r, name, terms, fixity);
                        let (stub, clauses) = self.fabricate_predicate(term);

                        self.queue.push_back(clauses);
                        Ok(QueryTerm::Jump(stub))
                    } else {
                        Err(ParserError::BuiltInArityMismatch(";"))
                    }
                } else if name.as_str() == "->" && terms.len() == 2 {
                    if terms.len() == 2 {
                        let conq = *terms.pop().unwrap();
                        let prec = *terms.pop().unwrap();

                        let (stub, clause) = self.fabricate_if_then(prec, conq);
                        self.queue.push_back(clause);

                        Ok(QueryTerm::Jump(stub))
                    } else {
                        Err(ParserError::BuiltInArityMismatch("->"))
                    }
                } else {
                    Ok(QueryTerm::Clause(Cell::default(), ClauseType::from(name, terms.len(), fixity), terms))
                },
            Term::Var(_, _) =>
                Ok(QueryTerm::Clause(Cell::default(), ClauseType::CallN, vec![Box::new(term)])),
            _ =>
                Err(ParserError::InadmissibleQueryTerm)
        }
    }

    fn prepend_if_then(&self, prec: Term, conq: Term, queue: &mut VecDeque<Box<Term>>)
    {
        let cut_symb = atom!("!");

        let mut terms_seq = unfold_by_str(prec, ",");
        terms_seq.push(Term::Constant(Cell::default(), cut_symb));

        terms_seq.append(&mut unfold_by_str(conq, ","));

        while let Some(term) = terms_seq.pop() {
            queue.push_front(Box::new(term));
        }
    }

    fn setup_query(&mut self, terms: Vec<Box<Term>>) -> Result<Vec<QueryTerm>, ParserError>
    {
        let mut query_terms = vec![];
        let mut work_queue  = VecDeque::from(terms);

        while let Some(term) = work_queue.pop_front() {
            let mut term = *term;

            // a (->) clause makes up the entire query. That's what the test confirms.
            if query_terms.is_empty() && work_queue.is_empty() {
                // check for ->, inline it if found.
                if let &mut Term::Clause(_, ref name, ref mut subterms, _) = &mut term {
                    if name.as_str() == "->" && subterms.len() == 2 {
                        let conq = *subterms.pop().unwrap();
                        let prec = *subterms.pop().unwrap();

                        self.prepend_if_then(prec, conq, &mut work_queue);
                        continue;
                    }
                }
            }

            for subterm in unfold_by_str(term, ",") {
                query_terms.push(try!(self.to_query_term(subterm)));
            }
        }

        Ok(query_terms)
    }

    fn setup_rule(&mut self, mut terms: Vec<Box<Term>>) -> Result<Vec<Rule>, ParserError>
    {
        let mut query_terms = try!(self.setup_query(terms.drain(1 ..).collect()));
        let clauses = query_terms.drain(1 ..).collect();
        let qt = query_terms.pop().unwrap();

        match *terms.pop().unwrap() {
            Term::Clause(_, name, terms, _) => {
                println!("Setting up Clause {}", name.as_str());
                Ok(Rule { head: (name, terms, qt), clauses })
            },
            Term::Constant(_, Constant::Atom(name)) => {
                println!("Setting up Constant {}", name.as_str());
                Ok(Rule { head: (name, vec![], qt), clauses })
            },
            _ => Err(ParserError::InvalidRuleHead)
        }
    }

    pub fn try_term_to_tl(&mut self, term: Term) -> Result<Vec<TopLevel>, ParserError>
    {
        match term {
            Term::Clause(r, name, mut terms, fixity) =>
                if name.as_str() == "?-" {
                    Ok(vec![TopLevel::Query(try!(self.setup_query(terms)))])
                } else if name.as_str() == ":-" && terms.len() > 1 {
                    Ok(TopLevel::Rule(try!(self.setup_rule(terms)),1.0))
                } else if name.as_str() == ":-" && terms.len() == 1 {
                    let term = *terms.pop().unwrap();
                    Ok(vec![TopLevel::Declaration(try!(setup_declaration(term)))])
                } else {
                    Ok(TopLevel::Fact(try!(setup_fact(Term::Clause(r, name, terms, fixity))),1.0))
                },
            term => Ok(TopLevel::Fact(try!(setup_fact(term)),1.0))
        }
    }

    fn try_terms_to_tls<Iter>(&mut self, terms: Iter) -> Result<VecDeque<TopLevel>, ParserError>
        where Iter: IntoIterator<Item=Term>
    {
        let mut results = VecDeque::new();

        for term in terms.into_iter() {
            results.push_back(self.try_term_to_tl(term)?);
        }

        Ok(results)
    }

    fn parse_line(&mut self, tls: &mut VecDeque<TopLevel>) -> Result<VecDeque<TopLevel>, ParserError>
    {
        let mut queue = VecDeque::new();

        queue.push_back(try!(merge_clauses(tls)));

        while let Some(terms) = self.queue.pop_front() {
            let mut inner_tls = self.try_terms_to_tls(terms)?;
            queue.push_back(try!(merge_clauses(&mut inner_tls)));
        }

        Ok(queue)
    }

    pub fn parse_batch(&mut self, op_dir: &mut OpDir) -> Result<Vec<TopLevelPacket>, EvalError>
    {
        let mut tls = VecDeque::new();
        let mut mod_name = clause_name!("user");

        while !self.parser.eof() {
            self.parser.reset(); // empty the parser stack of token descriptions.

            let term = self.parser.read_term(&op_dir)?;
            let tl   = self.try_term_to_tl(term)?;

            match tl {
                TopLevel::Declaration(Declaration::Op(op_decl)) => {
                    op_decl.submit(mod_name.clone(), op_dir)?;
                },
                TopLevel::Declaration(Declaration::Module(actual_mod)) => {
                    mod_name = actual_mod.name.clone();
                    tls.push_back(TopLevel::Declaration(Declaration::Module(actual_mod)));
                },
                tl => tls.push_back(tl)
            };
        }

        let mut results = vec![];

        while !tls.is_empty() {
            results.push(deque_to_packet(try!(self.parse_line(&mut tls)))?);
        }

        Ok(results)
    }

    pub fn parse_code(&mut self, op_dir: &OpDir) -> Result<TopLevelPacket, ParserError>
    {
        let terms   = self.parser.read(op_dir)?;
        let mut tls = self.try_terms_to_tls(terms)?;
        let results = self.parse_line(&mut tls)?;

        if tls.is_empty() {
            deque_to_packet(results)
        } else {
            Err(ParserError::InconsistentEntry)
        }
    }
}
