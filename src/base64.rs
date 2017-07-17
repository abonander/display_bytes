// Copyright 2017 Austin Bonander
//
// Licensed under the Apache License, Version 2.0, <LICENSE-APACHE or
// http://apache.org/licenses/LICENSE-2.0> or the MIT license <LICENSE-MIT or
// http://opensource.org/licenses/MIT>, at your option. This file may not be
// copied, modified, or distributed except according to those terms.
use super::ByteFormat;

use std::{fmt, mem, str};

pub struct FormatBase64;

const BASE64_CHARS: &[u8] = b"ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789+/";

const BUF_SIZE: usize = 1024;
const CHUNK_SIZE: usize = BUF_SIZE / 4 * 3;

impl ByteFormat for FormatBase64 {
    fn fmt_bytes(&self, bytes: &[u8], f: &mut fmt::Formatter) -> fmt::Result {

        for chunk in bytes.chunks(CHUNK_SIZE) {
            // We ensure that uninitialized memory isn't accessed
            let mut buf: [u8; BUF_SIZE] = unsafe { mem::uninitialized() };

            if chunk.len() == CHUNK_SIZE {
                for (chunk, buf) in chunk.chunks(3).zip(buf.chunks_mut(4)) {
                    encode_chunk_full(chunk, buf);
                }

                f.write_str(unsafe { str::from_utf8_unchecked(&buf) })?;
            } else {
                let divis_len = (chunk.len() / 3) * 3;

                for (chunk, buf) in chunk[..divis_len].chunks(3).zip(buf.chunks_mut(4)) {
                    encode_chunk_full(chunk, buf);
                }

                let buf_len = divis_len / 3 * 4;

                if divis_len == chunk.len() {
                    f.write_str(unsafe { str::from_utf8_unchecked(&buf[..buf_len])})?;
                } else {
                    let buf_full = buf_len + 4;
                    // Make sure all bytes are overwritten
                    buf[buf_len .. buf_full].copy_from_slice(&[b'='; 4]);

                    encode_chunk_partial(&chunk[divis_len..], &mut buf[buf_len .. buf_full]);

                    f.write_str(unsafe { str::from_utf8_unchecked(&buf[..buf_full]) })?;
                }
            }
        }

        Ok(())
    }
}

#[inline]
fn encode_chunk_full(chunk: &[u8], out: &mut [u8]) {
    debug_assert_eq!(chunk.len(), 3);
    debug_assert_eq!(out.len(), 4);

    // upper six bits of first byte
    out[0] = base64_byte(chunk[0] >> 2);
    // lower two bits of first byte, upper four of second
    out[1] = base64_byte(chunk[0] << 4 | chunk[1] >> 4);
    // lower four of second, upper two of third
    out[2] = base64_byte(chunk[1] << 2 | chunk[2] >> 6);
    // lower six bytes of third
    out[3] = base64_byte(chunk[2]);
}

fn encode_chunk_partial<'o>(chunk: &[u8], out: &'o mut [u8]) {
    debug_assert!(chunk.len() == 1 || chunk.len() == 2, "chunk len: {}", chunk.len());
    debug_assert_eq!(out.len(), 4);

    // upper six bits of first
    out[0] = base64_byte(chunk[0] >> 2);

    if chunk.len() == 2 {
        out[1] = base64_byte(chunk[0] << 4 | chunk[1] >> 4);
        out[2] = base64_byte(chunk[1] << 2);
    } else {
        out[1] = base64_byte(chunk[0] << 4);
    }
}

/// Use the lower six bytes of `c` as an index into `BASE64_CHARS`
fn base64_byte(c: u8) -> u8 {
    BASE64_CHARS[(c & 0x3F) as usize]
}

#[test]
fn test_base64() {
    // Lifted from https://en.wikipedia.org/wiki/Base64#Examples (Accessed July 16, 2017)
    let mut out = [0; 4];
    encode_chunk_full(b"Man", &mut out);
    assert_eq!(out, *b"TWFu");

    out = [b'='; 4];
    encode_chunk_partial(b"Ma", &mut out);
    assert_eq!(out, *b"TWE=");

    out = [b'='; 4];
    encode_chunk_partial(b"M", &mut out);
    assert_eq!(out, *b"TQ==");

    assert_eq!(
        FormatBase64.bytes_to_string(&[69, 236, 43, 138, 215, 136, 180, 137, 209, 186, 203, 75, 208, 191, 190]),
        "RewriteItInRustL0L++"
    );


}
