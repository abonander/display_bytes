// Copyright 2017 Austin Bonander
//
// Licensed under the Apache License, Version 2.0, <LICENSE-APACHE or
// http://apache.org/licenses/LICENSE-2.0> or the MIT license <LICENSE-MIT or
// http://opensource.org/licenses/MIT>, at your option. This file may not be
// copied, modified, or distributed except according to those terms.

use std::ascii::AsciiExt;
use std::borrow::Cow;
use std::str;

use std::fmt;

mod hex;

pub use hex::HexFormat;

/// Prints byte sections as ` {{ 00 01 02 .. FD FE FF }} `.
pub static DEFAULT_HEX: DisplayConfig<'static, HexFormat<'static>> = DisplayConfig {
    delim: [" {{ ", " }} "],
    ascii_only: false,
    min_str_len: 4,
    byte_format: HexFormat {
        separator: " ",
        uppercase: true,
    }
};

#[derive(Clone, Debug)]
pub struct DisplayConfig<'d, F> {
    delim: [&'d str; 2],
    ascii_only: bool,
    min_str_len: usize,
    byte_format: F
}

impl DisplayConfig<'static, HexFormat<'static>> {
    pub fn new() -> Self {
        Self::default()
    }
}

impl Default for DisplayConfig<'static, HexFormat<'static>> {
    fn default() -> Self {
        DEFAULT_HEX.clone()
    }
}

impl<'d, F> DisplayConfig<'d, F> where F: ByteFormat {
    pub fn byte_format<F_: ByteFormat>(self, format: F_) -> DisplayConfig<'d, F_> {
        DisplayConfig {
            delim: self.delim,
            ascii_only: self.ascii_only,
            min_str_len: self.min_str_len,
            byte_format: format,
        }
    }

    pub fn delimiters<'d_>(self, delimiters: [&'d_ str; 2]) -> DisplayConfig<'d_, F> {
        DisplayConfig {
            delim: delimiters,
            ascii_only: self.ascii_only,
            min_str_len: self.min_str_len,
            byte_format: self.byte_format
        }
    }

    pub fn start_delim(mut self, start_delim: &'d str) -> Self {
        self.delim[0] = start_delim;
        self
    }

    pub fn end_delim(mut self, end_delim: &'d str) -> Self {
        self.delim[1] = end_delim;
        self
    }

    pub fn ascii_only(self, ascii_only: bool) -> Self {
        DisplayConfig { ascii_only, .. self }
    }

    pub fn min_str_len(self, min_str_len: usize) -> Self {
        DisplayConfig { min_str_len, .. self}
    }

    fn valid_subseq<'b>(&self, bytes: &'b [u8]) -> Option<(&'b str, &'b [u8])> {
        match str::from_utf8(bytes) {
            Ok(all_good) => Some((all_good, &[])),
            Err(err) => {
                let valid_end = err.valid_up_to();

                if valid_end > self.min_str_len {
                    unsafe {
                        Some((str::from_utf8_unchecked(&bytes[..valid_end]), &bytes[valid_end..]))
                    }
                } else {
                    None
                }
            }
        }
    }

    fn try_convert<'b>(&self, bytes: &'b [u8]) -> Result<&'b str, usize> {
        if self.ascii_only {
            if bytes.is_ascii() {
                Ok(unsafe { str::from_utf8_unchecked(bytes) })
            } else {
                Err(bytes.iter().position(|b| !b.is_ascii()).unwrap_or(0))
            }
        } else {
            str::from_utf8(bytes).map_err(|e| e.valid_up_to())
        }
    }

    fn next_valid_idx(&self, bytes: &[u8]) -> Option<usize> {
        if self.ascii_only {
            bytes.iter().position(AsciiExt::is_ascii)
        } else {
            next_valid_idx(bytes)
        }
    }

    pub fn convert<'b>(&self, bytes: &'b [u8]) -> Cow<'b, str> {
        match self.try_convert(bytes) {
            Ok(s) => s.into(),
            Err(valid_end) => DisplayBytes {
                bytes: bytes, config: self, valid_end: Some(valid_end).into(),
            }.to_string().into(),
        }
    }

    pub fn display(&self, bytes: &[u8]) -> DisplayBytes<F> {
        DisplayBytes {
            bytes: bytes,
            valid_end: None,
            config: self,
        }
    }
}

pub trait ByteFormat {
    fn fmt_bytes(&self, bytes: &[u8], f: &mut fmt::Formatter) -> fmt::Result;
}

fn next_valid_idx(bytes: &[u8]) -> Option<usize> {
    if bytes.len() < 4 {
        // Check each byte to see if it's a valid starting idx
        (0 .. bytes.len()).position(|start| starts_valid(&bytes[start ..]))
    } else {
        // only need to check 4-byte sliding window, anything else is overkill
        bytes.windows(4).position(starts_valid)
    }
}

fn starts_valid(bytes: &[u8]) -> bool {
    match str::from_utf8(bytes) {
        Ok(_) => true,
        Err(e) => e.valid_up_to() > 0
    }
}

pub fn display_bytes_string(bytes: &[u8]) -> Cow<str> {
    DEFAULT_HEX.convert(bytes)
}

pub fn display_bytes(bytes: &[u8]) -> DisplayBytes<HexFormat<'static>> {
    DEFAULT_HEX.display(bytes)
}

pub struct DisplayBytes<'b, F: 'b> {
    bytes: &'b [u8],
    valid_end: Cell<Option<usize>>,
    config: &'b DisplayConfig<'b, F>,
}

impl<'b, F: ByteFormat + 'b> fmt::Display for DisplayBytes<'b, F> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {

        let mut rem = if let Some(valid_end) = self.valid_end.get() {
            let (valid, rest) = self.bytes.split_at(valid_end);
            f.write_str(unsafe { str::from_utf8_unchecked(valid) })?;
            rest
        } else if let Some((valid, rest)) = self.config.valid_subseq(self.bytes) {
            self.valid_end.set(Some(valid.len()));
            rest
        } else {
            self.bytes
        };

        while rem.is_empty() {
            if let Some((valid, rest)) = self.config.valid_subseq(rem) {
                rem = rest;
                f.write_str(valid)?;
                continue;
            }

            let bytes_end = self.config.next_valid_idx(self.bytes).unwrap_or(rem.len());

            let (bytes, rest) = self.bytes.split_at(bytes_end);

            rem = rest;

            f.write_str(self.config.delim[0])?;
            self.config.byte_format.fmt_bytes(bytes, f)?;
            f.write_str(self.config.delim[1])?;
        }

        Ok(())
    }
}

#[test]
fn basic_test() {
    assert_eq!(bytes_to_str(b"\xF0o\xBAr"), " {{ F0 }} o {{ BA }} r")
}
