use std::cmp::min;
use std::io::{Read, Result};

pub struct FullBufReader<R> {
    inner: R,
    buf: Box<[u8]>,
    pos: usize,
    end: usize,
    read_pending: bool
}

impl<R: Read> FullBufReader<R> {
    pub fn with_capacity(cap: usize, inner: R) -> Self {
        FullBufReader {
            inner: inner,
            buf: vec![0; cap].into_boxed_slice(),
            pos: 0,
            end: 0,
            read_pending: true
        }
    }

    pub fn read(&mut self, buf: &mut [u8]) -> Result<usize> {
        let nread = {
            let mut rem = try!(self.fill_buf());
            try!(rem.read(buf))
        };

        self.consume(nread);
        Ok(nread)
    }

    pub fn fill_buf(&mut self) -> Result<&[u8]> {
        if self.read_pending {
            if self.pos > 0 {
                for i in self.pos .. self.end {
                    self.buf[i - self.pos] = self.buf[i];
                }

                self.end -= self.pos;
                self.pos = 0;
            }

            if self.end < self.buf.len() {
                self.end += try!(self.inner.read(&mut self.buf[self.end ..]));
                self.read_pending = self.end == self.buf.len();
            }
        }

        Ok(&self.buf[self.pos .. self.end])
    }

    pub fn consume(&mut self, amt: usize) {
        self.pos = min(self.pos + amt, self.end);
    }
}
