// Copyright 2017 Austin Bonander
//
// Licensed under the Apache License, Version 2.0, <LICENSE-APACHE or
// http://apache.org/licenses/LICENSE-2.0> or the MIT license <LICENSE-MIT or
// http://opensource.org/licenses/MIT>, at your option. This file may not be
// copied, modified, or distributed except according to those terms.
use super::ByteFormat;

use std::fmt;

#[derive(Copy, Clone, Debug)]
pub struct HexFormat<'s> {
    /// The separator for individual hex-formatted bytes.
    pub separator: &'s str,
    pub uppercase: bool,
}

impl<'s> ByteFormat for HexFormat<'s> {
    fn fmt_bytes(&self, bytes: &[u8], f: &mut fmt::Formatter) -> fmt::Result {
        use std::fmt::Write;

        let mut written = false;

        for b in bytes {
            if written {
                f.write_str(self.separator)?;
            }

            if self.uppercase {
                write!(f, "{:02X}", b)?;
            } else {
                write!(f, "{:02x}", b)?;
            }

        }

        Ok(())
    }
}

