// Copyright 2017 Austin Bonander
//
// Licensed under the Apache License, Version 2.0, <LICENSE-APACHE or
// http://apache.org/licenses/LICENSE-2.0> or the MIT license <LICENSE-MIT or
// http://opensource.org/licenses/MIT>, at your option. This file may not be
// copied, modified, or distributed except according to those terms.
//! Human-readable display of byte sequences.
//!
//! Supports printing of both UTF-8 and ASCII-only sequences.
//!
//! For easy usage, see the free functions `display_bytes()` and `display_bytes_string()`
//! in this crate. For more control over formatting, see the statics in this crate or build
//! an instance of `DisplayBytesConfig` yourself.
//!
//! ```rust
//! extern crate display_bytes;
//! 
//! use display_bytes::{display_bytes, display_bytes_string};
//! 
//! fn main() {
//!     let bytes = b"Hello, world!\x89\x90\xAB\xCD";
//!     println!("{:?}", bytes);
//!     println!("{}", display_bytes(bytes));
//!     assert_eq!(display_bytes_string(bytes),
//!                "Hello, world! {{ 89 90 AB CD }} ");
//! }
//! ```
#![warn(missing_docs)]
use std::borrow::Cow;
use std::cell::Cell;
use std::{fmt, ops, str};

mod base64;
mod hex;

pub use base64::FormatBase64;
pub use hex::{DEFAULT_HEX, FormatHex};
use std::fmt::Write;

#[derive(Clone, Debug)]
enum MaybeOwned<'a, T: 'a> {
    Borrowed(&'a T),
    Owned(T),
}

impl<'a, T: 'a> ops::Deref for MaybeOwned<'a, T> {
    type Target = T;

    fn deref(&self) -> &T {
        match *self {
            MaybeOwned::Borrowed(b) => b,
            MaybeOwned::Owned(ref o) => o,
        }
    }
}

impl<'a, T: 'a> From<&'a T> for MaybeOwned<'a, T> {
    fn from(refr: &'a T) -> Self { MaybeOwned::Borrowed(refr) }
}

impl<'a, T: 'a> From<T> for MaybeOwned<'a, T> {
    fn from(owned: T) -> Self { MaybeOwned::Owned(owned) }
}

/// Prints byte sections with hexadecimal bytes wrapped in ` {{ }} `. Prints only ASCII sequences.
pub const HEX_ASCII: DisplayBytesConfig<'static, FormatHex<'static>> = DisplayBytesConfig {
    delim: [" {{ ", " }} "],
    ascii_only: true,
    min_str_len: 6,
    print_terms: true,
    invert_delims: false,
    escape_ctl: false,
    byte_format: DEFAULT_HEX,
};

/// Prints byte sections with hexadecimal bytes wrapped in ` {{ }} `. Prints all valid UTF-8 strings.
pub const HEX_UTF8: DisplayBytesConfig<'static, FormatHex<'static>> = DisplayBytesConfig {
    delim: [" {{ ", " }} "],
    ascii_only: false,
    min_str_len: 6,
    print_terms: true,
    invert_delims: false,
    escape_ctl: false,
    byte_format: DEFAULT_HEX
};

/// Prints byte sections as Base-64 wrapped in ` {{ }} `. Prints only ASCII sequences.
///
/// Provided as a static so it may be used by-reference.
pub const BASE64_ASCII: DisplayBytesConfig<'static, FormatBase64> = DisplayBytesConfig {
    delim: [" {{ ", " }} "],
    ascii_only: true,
    min_str_len: 6,
    print_terms: true,
    invert_delims: false,
    escape_ctl: false,
    byte_format: FormatBase64,
};

/// Prints byte sections as Base-64 wrapped in ` {{ }} `. Prints all valid UTF-8 strings.
pub const BASE64_UTF8: DisplayBytesConfig<'static, FormatBase64> = DisplayBytesConfig {
    delim: [" {{ ", " }} "],
    ascii_only: false,
    min_str_len: 6,
    print_terms: true,
    invert_delims: false,
    escape_ctl: false,
    byte_format: FormatBase64,
};

/// Configuration builder for `DisplayBytes`.
///
/// Consts with sane defaults are provided in this module.
#[derive(Clone, Debug)]
pub struct DisplayBytesConfig<'d, F> {
    delim: [&'d str; 2],
    ascii_only: bool,
    min_str_len: usize,
    print_terms: bool,
    invert_delims: bool,
    escape_ctl: bool,
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
            print_terms: self.print_terms,
            invert_delims: self.invert_delims,
            escape_ctl: self.escape_ctl,
            byte_format: format,
        }
    }

    /// Get a mutable reference to the current `ByteFormat`.
    pub fn byte_format_mut(&mut self) -> &mut F {
        &mut self.byte_format
    }

    /// Set the pair of delimiters used to wrap byte sequences in the formatted stream.
    ///
    /// Note that this can change the lifetime bound.
    pub fn delimiters<'d_>(self, delimiters: [&'d_ str; 2]) -> DisplayBytesConfig<'d_, F> {
        DisplayBytesConfig {
            delim: delimiters,
            ascii_only: self.ascii_only,
            min_str_len: self.min_str_len,
            print_terms: self.print_terms,
            invert_delims: self.invert_delims,
            escape_ctl: self.escape_ctl,
            byte_format: self.byte_format
        }
    }

    /// Get a mutable reference to the current pair of delimiters.
    pub fn delimiters_mut(&mut self) -> &mut [&'d str; 2] {
        &mut self.delim
    }

    /// If set to `true`, only displays ASCII byte sequences (bytes in `[0x00, 0x7F]`).
    ///
    /// Otherwise, displays all valid UTF-8 sequences at least `min_str_len` bytes long.
    pub fn ascii_only(self, ascii_only: bool) -> Self {
        DisplayBytesConfig { ascii_only, ..self }
    }

    /// The minimum number of *bytes* in length that a valid string sequence
    /// must be to be displayed.
    ///
    /// Strings shorter than this length will be included in the nearest byte sequence. Use this
    /// to avoid extra noise from random decodable characters splitting byte sequences.
    ///
    /// ## Note
    /// This does not affect byte sequences that can be completely decoded. If `print_terminators`
    /// is set, this also will not affect strings at the beginning or at the end of the byte
    /// slice (e.g. valid strings at the start and end will be printed regardless of length).
    pub fn min_str_len(self, min_str_len: usize) -> Self {
        DisplayBytesConfig { min_str_len, ..self }
    }

    /// If set to `true`, valid strings at the start and end of a byte slice will
    /// be printed regardless of their length relative to `min_str_len`.
    pub fn print_terminators(self, print_terminators: bool) -> Self {
        DisplayBytesConfig{ print_terms: print_terminators, .. self }
    }

    /// If set to `true`, control characters will be printed in their escaped form (`\n`)
    /// instead of printed directly.
    pub fn escape_control(self, escape_ctl: bool) -> Self {
        DisplayBytesConfig{ escape_ctl, .. self }
    }

    /// If set to `true`, wraps decoded strings in the given delimiters
    /// rather than byte sequences.
    pub fn invert_delimiters(self, invert_delimiters: bool) -> Self {
        DisplayBytesConfig { invert_delims: invert_delimiters, .. self }
    }
}

impl<'d, F: ByteFormat> DisplayBytesConfig<'d, F> {
    fn valid_subseq<'b>(&self, bytes: &'b [u8]) -> Option<(&'b str, &'b [u8])> {
        match self.try_convert(bytes) {
            Ok(all_good) => Some((all_good, &[])),
            Err(valid_end) if valid_end > 0 =>
                Some((assume_utf8(&bytes[..valid_end]), &bytes[valid_end..])),
            _ => None,
        }
    }

    fn try_convert<'b>(&self, bytes: &'b [u8]) -> Result<&'b str, usize> {
        if self.ascii_only {
            if bytes.is_ascii() {
                Ok(assume_utf8(bytes))
            } else {
                Err(bytes.iter().position(|b| !b.is_ascii()).unwrap_or(0))
            }
        } else {
            str::from_utf8(bytes).map_err(|e| e.valid_up_to())
        }
    }

    fn next_valid_idx(&self, bytes: &[u8]) -> Option<usize> {
        if self.ascii_only {
            bytes.iter().position(u8::is_ascii)
        } else {
            next_valid_idx(bytes)
        }
    }

    fn next_valid_subseq<'b>(&self, bytes: &'b [u8]) -> Option<(&'b [u8], &'b str, &'b [u8])> {
        let mut start = 0;

        while let Some(next_valid) = self.next_valid_idx(&bytes[start..]) {
            start += next_valid;

            if let Some((valid, after)) = self.valid_subseq(&bytes[start..]) {
                // We handle this here so we don't need to do special handling of delimiters
                // in `DisplayBytes::fmt()`
                if valid.len() >= self.min_str_len || (after.is_empty() && self.print_terms) {
                    return Some((&bytes[..start], valid, after));
                }
            }

            start += 1;
        }

        None
    }

    /// Attempt to convert `bytes` to a string (an ASCII-only string if `ascii_only` is set,
    /// UTF-8 otherwise), or otherwise format `bytes` to a string using the properties
    /// in this configuration.
    pub fn display_bytes_string<'b>(&self, bytes: &'b [u8]) -> Cow<'b, str> where 'd: 'b, F: 'b {
        match self.try_convert(bytes) {
            Ok(s) => s.into(),
            Err(valid_end) => DisplayBytes {
                bytes, config: self.into(), valid_end: Some(valid_end).into(),
            }.to_string().into(),
        }
    }

    /// Get a type that implements `Display` which will format `bytes` to an output stream
    /// using the properties in this configuration.
    pub fn ref_display_bytes<'b>(&'b self, bytes: &'b [u8]) -> DisplayBytes<'b, F> {
        DisplayBytes {
            bytes,
            valid_end: Cell::new(None),
            config: self.into(),
        }
    }
}


impl<'d, F: ByteFormat> DisplayBytesConfig<'d, F> {
    /// Get a type that implements `Display` which will format `bytes` to an output stream
    /// using the properties in this configuration.
    pub fn display_bytes<'b>(self, bytes: &'b [u8]) -> DisplayBytes<'b, F> where 'd: 'b {
        DisplayBytes {
            bytes,
            valid_end: Cell::new(None),
            config: self.into(),
        }
    }
}

/// Formats byte sequences in human-readable representations.
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
            // Check the last 3 bytes
            .or_else(|| next_valid_idx(&bytes[bytes.len() - 3 ..]))
    }
}

fn starts_valid(bytes: &[u8]) -> bool {
    match str::from_utf8(bytes) {
        Ok(_) => true,
        Err(e) => e.valid_up_to() > 0,
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
pub fn display_bytes<'b>(bytes: &'b [u8]) -> impl fmt::Display + 'b {
    HEX_ASCII.display_bytes(bytes)
}

/// A wrapper around a byte sequence which implements `Display`.
///
/// Non-decodable byte sequences will be printed in human-readable representation based
/// on the byte format `F`. Use `DisplayBytesConfig` to get an instance of this type.
#[derive(Debug)]
pub struct DisplayBytes<'b, F: 'b> {
    bytes: &'b [u8],
    valid_end: Cell<Option<usize>>,
    config: MaybeOwned<'b, DisplayBytesConfig<'b, F>>,
}

impl<'b, F> DisplayBytes<'b, F> {
    fn maybe_escape(&self, str: &str, f: &mut fmt::Formatter) -> fmt::Result {
        if self.config.escape_ctl {
            for c in str.chars() {
                if c.is_ascii_control() {
                    for c in c.escape_default() {
                        f.write_char(c)?;
                    }
                } else {
                    f.write_char(c)?;
                }
            }

            Ok(())
        } else {
            f.write_str(str)
        }
    }
}

impl<'b, F: ByteFormat + 'b> fmt::Display for DisplayBytes<'b, F> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        let maybe_valid = self.valid_end.get()
            .map(|valid_end| {
                let (valid, rest) = self.bytes.split_at(valid_end);
                (assume_utf8(valid), rest)
            })
            .or_else(|| self.config.valid_subseq(self.bytes));

        // We handle this here because this is the only time we *know* we're at the
        // start of the byte sequence
        let accept_start = |s: &str| self.config.print_terms ||
                                        s.len() >= self.config.min_str_len;

        let mut rem = match maybe_valid {
            Some((valid, rem)) if accept_start(valid) => {
                // Memoize the first valid sequence of the bytes
                self.valid_end.set(Some(valid.len()));

                if self.config.invert_delims {
                    f.write_str(self.config.delim[0])?;
                }

                self.maybe_escape(valid, f)?;

                if self.config.invert_delims {
                    f.write_str(self.config.delim[1])?;
                }

                rem
            },
            _ => {
                // Memoize that the byte sequence doesn't start valid
                self.valid_end.set(Some(0));
                self.bytes
            }
        };

        while let Some((before, valid, after)) = self.config.next_valid_subseq(rem) {
            if !self.config.invert_delims {
                f.write_str(self.config.delim[0])?;
                self.config.byte_format.fmt_bytes(before, f)?;
                f.write_str(self.config.delim[1])?;
                self.maybe_escape(valid, f)?;
            } else {
                self.config.byte_format.fmt_bytes(before, f)?;
                f.write_str(self.config.delim[0])?;
                self.maybe_escape(valid, f)?;
                f.write_str(self.config.delim[1])?;
            }


            rem = after;
        }

        if !rem.is_empty() {
            if !self.config.invert_delims {
                f.write_str(self.config.delim[0])?;
            }

            self.config.byte_format.fmt_bytes(rem, f)?;

            if !self.config.invert_delims {
                f.write_str(self.config.delim[1])?;
            }
        }

        Ok(())
    }
}

/// In debug mode, asserts that `bytes` is valid UTF-8; in release mode, converts it unchecked
fn assume_utf8(bytes: &[u8]) -> &str {
    if cfg!(debug) {
        str::from_utf8(bytes).unwrap_or_else(|e|
            panic!("{}; lossy conversion: {}", e, String::from_utf8_lossy(bytes))
        )
    } else {
        unsafe { str::from_utf8_unchecked(bytes) }
    }
}

#[test]
fn basic_test() {
    let format = &HEX_UTF8;
    assert_eq!(format.display_bytes_string(b"Hello, world!"), "Hello, world!");
    assert_eq!(format.display_bytes_string(b"Hello,\xAB\xCD\xEF"), "Hello, {{ AB CD EF }} ");
    assert_eq!(format.display_bytes_string(b"\xF0o\xBAr"), " {{ F0 6F BA }} r");
    // test of `min_str_len`, note that the "r" at the end of `\xF0o\xBAr` is printed
    // because it is part of a string of valid length ("r foobar "), but the "o" between
    // 0xF0 and 0xBA is considered part of the byte sequence.
    assert_eq!(format.display_bytes_string(b"\xF0o\xBAr foobar\xAB\xCD\xEF"),
               " {{ F0 6F BA }} r foobar {{ AB CD EF }} ");
}

#[test]
fn test_memoization() {
    let display = HEX_UTF8.display_bytes(b"Hello,\xAB\xCD\xEF");
    assert_eq!(display.to_string(), "Hello, {{ AB CD EF }} ");
    assert_eq!(display.to_string(), "Hello, {{ AB CD EF }} ");
}

#[test]
fn test_print_terminators() {
    let bytes = b"ab\xCD \xEFgh";
    let display = HEX_UTF8.display_bytes(bytes);
    let config = HEX_UTF8.clone().print_terminators(false);
    let display2 = config.display_bytes(bytes);

    assert_eq!(display.to_string(), "ab {{ CD 20 EF }} gh");
    assert_eq!(display2.to_string(), " {{ 61 62 CD 20 EF 67 68 }} ");
}

#[test]
fn test_invert_delims() {
    let bytes = b"\x80\x90Hello, world!\xAB\xCD";
    let config = HEX_UTF8.clone().invert_delimiters(true);

    let display = config.display_bytes(bytes);
    let display2 = HEX_UTF8.display_bytes(bytes);

    assert_eq!(display.to_string(), "80 90 {{ Hello, world! }} AB CD");
    assert_eq!(display2.to_string(), " {{ 80 90 }} Hello, world! {{ AB CD }} ")
}
