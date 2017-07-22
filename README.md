`display_bytes` [![Travis](https://img.shields.io/travis/abonander/display_bytes.svg)](https://travis-ci.org/abonander/display_bytes) [![Crates.io](https://img.shields.io/crates/v/display_bytes.svg)](https://crates.io/crates/display_bytes)
-----------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------

Human-readable display of byte sequences.

Supports printing of both UTF-8 and ASCII-only sequences.

```rust
extern crate display_bytes;

use display_bytes::{display_bytes, display_bytes_string};

fn main() {
    let bytes = b"Hello, world!\x89\x90\xAB\xCD";
    println!("{:?}", bytes);
    println!("{}", display_bytes(bytes));
    assert_eq!(display_bytes_string(bytes),
               "Hello, world! {{ 89 90 AB CD }}");
}
```

## License

Licensed under either of

 * Apache License, Version 2.0, ([LICENSE-APACHE](LICENSE-APACHE) or http://www.apache.org/licenses/LICENSE-2.0)
 * MIT license ([LICENSE-MIT](LICENSE-MIT) or http://opensource.org/licenses/MIT)

at your option.

## Contribution

Unless you explicitly state otherwise, any contribution intentionally submitted
for inclusion in the work by you, as defined in the Apache-2.0 license, shall be dual licensed as above, without any
additional terms or conditions.
