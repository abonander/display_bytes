// Copyright 2017 Austin Bonander
//
// Licensed under the Apache License, Version 2.0, <LICENSE-APACHE or
// http://apache.org/licenses/LICENSE-2.0> or the MIT license <LICENSE-MIT or
// http://opensource.org/licenses/MIT>, at your option. This file may not be
// copied, modified, or distributed except according to those terms.
use super::ByteFormat;

use std::fmt;

/// Default hexadecimal byte format used by this crate.
pub const DEFAULT_HEX: FormatHex<'static> = FormatHex {
    prefix: "",
    separator: " ",
    uppercase: true,
};

/// Formats bytes in hexadecimal pairs (`00 - FF`).
#[derive(Copy, Clone, Debug)]
pub struct FormatHex<'s> {
    /// The prefix, if any, for each byte.
    pub prefix: &'s str,
    /// The separator for individual hex-formatted bytes.
    pub separator: &'s str,
    /// Whether or not to write the hex-pairs in uppercase
    pub uppercase: bool,
}

impl<'s> ByteFormat for FormatHex<'s> {
    fn fmt_bytes(&self, bytes: &[u8], f: &mut fmt::Formatter) -> fmt::Result {
        let mut written = false;

        for b in bytes {
            if written {
                f.write_str(self.separator)?;
            }

            if self.uppercase {
                write!(f, "{}{:02X}", self.prefix, b)?;
            } else {
                write!(f, "{}{:02x}", self.prefix, b)?;
            }

            written = true;
        }

        Ok(())
    }
}

#[test]
fn test_hex() {
    assert_eq!(DEFAULT_HEX.bytes_to_string(b"\xAB\xCD\xEF\x00\x10"), "AB CD EF 00 10");
}
