// Copyright 2017 Austin Bonander
//
// Licensed under the Apache License, Version 2.0, <LICENSE-APACHE or
// http://apache.org/licenses/LICENSE-2.0> or the MIT license <LICENSE-MIT or
// http://opensource.org/licenses/MIT>, at your option. This file may not be
// copied, modified, or distributed except according to those terms.

use std::ascii::AsciiExt;
use std::borrow::Cow;
use std::cell::Cell;
use std::str;

use std::fmt;

mod base64;
mod hex;

pub use base64::FormatBase64;
pub use hex::{DEFAULT_HEX, FormatHex};

/// Prints byte sections with hexadecimal bytes wrapped in ` {{ }} `. Prints only ASCII sequences.
///
/// Provided as a static so it may be used by-reference.
pub static HEX_ASCII: DisplayBytesConfig<'static, FormatHex<'static>> = DisplayBytesConfig {
    delim: [" {{ ", " }} "],
    ascii_only: true,
    min_str_len: 6,
    byte_format: DEFAULT_HEX,
};

/// Prints byte sections with hexadecimal bytes wrapped in ` {{ }} `. Prints all valid UTF-8 strings.
///
/// Provided as a static so it may be used by-reference.
pub static HEX_UTF8: DisplayBytesConfig<'static, FormatHex<'static>> = DisplayBytesConfig {
    delim: [" {{ ", " }} "],
    ascii_only: false,
    min_str_len: 6,
    byte_format: DEFAULT_HEX
};

/// Prints byte sections as Base-64 wrapped in ` {{ }} `. Prints only ASCII sequences.
///
/// Provided as a static so it may be used by-reference.
pub static BASE64_ASCII: DisplayBytesConfig<'static, FormatBase64> = DisplayBytesConfig {
    delim: [" {{ ", " }} "],
    ascii_only: true,
    min_str_len: 6,
    byte_format: FormatBase64,
};

/// Prints byte sections as Base-64 wrapped in ` {{ }} `. Prints all valid UTF-8 strings.
///
/// Provided as a static so it may be used by-reference.
pub static BASE64_UTF8: DisplayBytesConfig<'static, FormatBase64> = DisplayBytesConfig {
    delim: [" {{ ", " }} "],
    ascii_only: false,
    min_str_len: 6,
    byte_format: FormatBase64,
};

/// Configuration builder for `DisplayBytes`.
///
/// Statics with sane defaults are provided in this module.
#[derive(Clone, Debug)]
pub struct DisplayBytesConfig<'d, F: ?Sized> {
    delim: [&'d str; 2],
    ascii_only: bool,
    min_str_len: usize,
    byte_format: F
}

impl Default for DisplayBytesConfig<'static, FormatHex<'static>> {
    fn default() -> Self {
        HEX_UTF8.clone()
    }
}

impl Default for DisplayBytesConfig<'static, FormatBase64> {
    fn default() -> Self { BASE64_UTF8.clone() }
}

impl<'d, F> DisplayBytesConfig<'d, F> {
    /// Set the type used to format byte sequences.
    pub fn byte_format<F_: ByteFormat>(self, format: F_) -> DisplayBytesConfig<'d, F_> {
        DisplayBytesConfig {
            delim: self.delim,
            ascii_only: self.ascii_only,
            min_str_len: self.min_str_len,
            byte_format: format,
        }
    }

    pub fn delimiters<'d_>(self, delimiters: [&'d_ str; 2]) -> DisplayBytesConfig<'d_, F> {
        DisplayBytesConfig {
            delim: delimiters,
            ascii_only: self.ascii_only,
            min_str_len: self.min_str_len,
            byte_format: self.byte_format
        }
    }

    pub fn ascii_only(self, ascii_only: bool) -> Self {
        DisplayBytesConfig { ascii_only, ..self }
    }

    pub fn min_str_len(self, min_str_len: usize) -> Self {
        DisplayBytesConfig { min_str_len, ..self }
    }
}

impl<'d, F: ?Sized + ByteFormat> DisplayBytesConfig<'d, F> {
    fn valid_subseq<'b>(&self, bytes: &'b [u8]) -> Option<(&'b str, &'b [u8])> {
        match self.try_convert(bytes) {
            Ok(all_good) if all_good.len() >= self.min_str_len => Some((all_good, &[])),
            Err(valid_end) if valid_end >= self.min_str_len =>
                unsafe {
                    Some((str::from_utf8_unchecked(&bytes[..valid_end]), &bytes[valid_end..]))
                },
            _ => None,
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

    fn next_valid_subseq<'b>(&self, bytes: &'b [u8]) -> Option<(&'b [u8], &'b str, &'b [u8])> {
        let mut start = 0;

        while let Some(next_valid) = self.next_valid_idx(&bytes[start..]) {
            start += next_valid;

            if let Some((valid, after)) = self.valid_subseq(&bytes[start..]) {
                return Some((&bytes[..start], valid, after));
            }

            start += 1;
        }

        None
    }

    pub fn display_bytes_string<'b>(&self, bytes: &'b [u8]) -> Cow<'b, str> where 'd: 'b, F: 'b {
        match self.try_convert(bytes) {
            Ok(s) => s.into(),
            Err(valid_end) => DisplayBytes {
                bytes: bytes, config: self, valid_end: Some(valid_end).into(),
            }.to_string().into(),
        }
    }

    pub fn display_bytes<'b>(&'b self, bytes: &'b [u8]) -> DisplayBytes<'b, F> {
        DisplayBytes {
            bytes: bytes,
            valid_end: Cell::new(None),
            config: self,
        }
    }
}

pub trait ByteFormat {
    /// Encode the given byte-sequence in some human-readable format and print it to `f`.
    fn fmt_bytes(&self, bytes: &[u8], f: &mut fmt::Formatter) -> fmt::Result;

    /// Uses `fmt_bytes()` to encode the byte-sequence and print it to a `String`.
    ///
    /// Not used directly except for testing. However, you may find it useful.
    fn bytes_to_string(&self, bytes: &[u8]) -> String {
        struct DisplayAdapter<'a, F: ?Sized + 'a>(&'a [u8], &'a F);

        impl<'a, F: ByteFormat + ?Sized + 'a> fmt::Display for DisplayAdapter<'a, F> {
            fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
                self.1.fmt_bytes(self.0, f)
            }
        }

        format!("{}", DisplayAdapter(bytes, self))
    }
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


/// Attempt to convert the byte slice to a string, or else format it to a string using the default
/// `DisplayBytesConfig`.
///
/// All string-decodable sequences of useful length will be displayed as they are, and all
/// non-decodable byte sequences will be printed in a human-readable format.
///
/// The format is unspecified. If you want to specify a format, use `DisplayBytesConfig` directly
/// or one of the statics in the crate root.
pub fn display_bytes_string(bytes: &[u8]) -> Cow<str> {
    HEX_UTF8.display_bytes_string(bytes)
}

/// Wrap a byte slice in an adapter which implements `Display`.
///
/// This adapter will print any string-decodable sequences of useful length in the byte stream,
/// and all non-decodable byte sequences in a human-readable format.
///
/// The format is deliberately unspecified in the type. If you want to specify a format, use
/// `DisplayBytesConfig` directly or one of the statics in the crate root.
pub fn display_bytes(bytes: &[u8]) -> DisplayBytes<ByteFormat> {
    let hex_ascii: &DisplayBytesConfig<ByteFormat> = &HEX_UTF8;
    hex_ascii.display_bytes(bytes)
}

#[derive(Debug)]
pub struct DisplayBytes<'b, F: ?Sized + 'b> {
    bytes: &'b [u8],
    valid_end: Cell<Option<usize>>,
    config: &'b DisplayBytesConfig<'b, F>,
}

impl<'b, F: ?Sized + 'b> Clone for DisplayBytes<'b, F> {
    fn clone(&self) -> Self {
        DisplayBytes { bytes: self.bytes, valid_end: self.valid_end.clone(), config: self.config }
    }
}

impl<'b, F: ?Sized + ByteFormat + 'b> fmt::Display for DisplayBytes<'b, F> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        let mut rem = if let Some(valid_end) = self.valid_end.get() {
            // Memoize the first valid sequence of the bytes
            self.valid_end.set(Some(valid_end));
            let (valid, rest) = self.bytes.split_at(valid_end);
            f.write_str(unsafe { str::from_utf8_unchecked(valid) })?;
            rest
        } else {
            self.bytes
        };

        while let Some((before, valid, after)) = self.config.next_valid_subseq(rem) {
            f.write_str(self.config.delim[0])?;
            self.config.byte_format.fmt_bytes(before, f)?;
            f.write_str(self.config.delim[1])?;
            f.write_str(valid)?;
            rem = after;
        }

        if !rem.is_empty() {
            f.write_str(self.config.delim[0])?;
            self.config.byte_format.fmt_bytes(rem, f)?;
            f.write_str(self.config.delim[1])?;
        }

        Ok(())
    }
}

#[test]
fn basic_test() {
    assert_eq!(display_bytes_string(b"Hello, world!"), "Hello, world!");
    assert_eq!(display_bytes_string(b"\xF0o\xBAr"), " {{ F0 6F BA 72 }} ");
    assert_eq!(display_bytes_string(b"\xF0o\xBAr foobar \xAB\xCD\xEF"), " {{ F0 6F BA }} r foobar  {{ AB CD EF }} ");
}
