#![no_main]
#[macro_use] extern crate libfuzzer_sys;
extern crate display_bytes;

use std::io::{self, Write};

use display_bytes::*;

fuzz_target!(|data: &[u8]| {
    let mut sink = io::sink();

    write!(sink, "{}", HEX_ASCII.display_bytes(data)).unwrap();
    write!(sink, "{}", HEX_UTF8.display_bytes(data)).unwrap();
    write!(sink, "{}", BASE64_ASCII.display_bytes(data)).unwrap();
    write!(sink, "{}", BASE64_UTF8.display_bytes(data)).unwrap();

    let _ = HEX_ASCII.display_bytes_string(data);
    let _ = HEX_UTF8.display_bytes_string(data);
    let _ = BASE64_ASCII.display_bytes_string(data);
    let _ = BASE64_UTF8.display_bytes_string(data);
});
