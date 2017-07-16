// Copyright 2017 Austin Bonander
//
// Licensed under the Apache License, Version 2.0, <LICENSE-APACHE or
// http://apache.org/licenses/LICENSE-2.0> or the MIT license <LICENSE-MIT or
// http://opensource.org/licenses/MIT>, at your option. This file may not be
// copied, modified, or distributed except according to those terms.
use super::ByteFormat;

use std::{fmt, mem, str};

pub struct FormatBase64;

const BASE64_CHARS: &[u8] = b"ABCDEFGHJIKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789+/";

const BUF_SIZE: usize = 1024;
const CHUNK_SIZE: usize = BUF_SIZE / 4 * 3;

const BUF: [u8; BUF_SIZE] = [b'='; BUF_SIZE];

impl ByteFormat for FormatBase64 {
    fn fmt_bytes(&self, bytes: &[u8], f: &mut fmt::Formatter) -> fmt::Result {

        for chunk in bytes.chunks(CHUNK_SIZE) {
            if chunk.len() == CHUNK_SIZE {
                // We're going to overwrite the entire buffer
                let mut buf: [u8; BUF_SIZE] = unsafe { mem::uninitialized() };

                for (chunk, buf) in chunk.chunks(3).zip(buf.chunks_mut(4)) {
                    encode_chunk_full(chunk, buf);
                }

                f.write_str(unsafe { str::from_utf8_unchecked(&buf) })?;
            } else {
                let mut buf = BUF;
                // Get the next lowest multiple of 3
                let divis_len = (chunk.len() / 3) * 3;

                for (chunk, buf) in chunk[..divis_len].chunks(3).zip(buf.chunks_mut(4)) {
                    encode_chunk_full(chunk, buf);
                }

                let buf_len = (divis_len / 3 * 4) + 4;

                encode_chunk(&chunk[divis_len..], &mut buf[buf_len - 4 .. buf_len]);

                f.write_str(unsafe { str::from_utf8_unchecked(&buf[..buf_len]) })?;
            }
        }

        Ok(())
    }
}

#[inline]
fn encode_chunk_full(chunk: &[u8], out: &mut [u8]) {
    debug_assert_eq!(chunk.len(), 3);
    debug_assert_eq!(out.len(), 4);

    out[0] = base64_byte(chunk[0] >> 2);
    out[1] = base64_byte(chunk[0] << 6 & chunk[1] >> 2);
    out[2] = base64_byte(chunk[1] << 6 & chunk[2] >> 2);
    out[3] = base64_byte(chunk[2] << 6);
}

fn encode_chunk<'o>(chunk: &[u8], out: &'o mut [u8]) {
    debug_assert!(chunk.len() == 1 || chunk.len() == 2);
    debug_assert_eq!(out.len(), 4);

    out[0] = base64_byte(chunk[0] >> 2);

    if chunk.len() == 2 {
        out[1] = base64_byte(chunk[0] << 6 & chunk[1] >> 2);
        out[2] = base64_byte(chunk[1] << 6);
    } else {
        out[1] = base64_byte(chunk[0] << 6);
    }
}

fn base64_byte(c: u8) -> u8 {
    BASE64_CHARS[c as usize]
}
