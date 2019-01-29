shorter_uuid
============
[![Latest version](https://img.shields.io/crates/v/shorter_uuid.svg)][crates.io]
[![Documentation](https://docs.rs/shorter_uuid/badge.svg)][docs.rs]

[crates.io]: https://crates.io/crates/shorter_uuid
[docs.rs]: https://docs.rs/shorter_uuid

This create is a simple UUID shortener inspired by [`keiko/uuid-shortener`],
[`pascaldevink/shortuuid`] and [`skorokithakis/shortuuid`].

[`keiko/uuid-shortener`]: https://github.com/mgrajcarek/uuid-shortener
[`pascaldevink/shortuuid`]: https://github.com/pascaldevink/shortuuid
[`skorokithakis/shortuuid`]: https://github.com/skorokithakis/shortuuid

## Usage

Add this to your `Cargo.toml`:
```toml
[dependencies]
shorter_uuid = { version = "0.1", default_features = false }
```
_Note:_ Disabling of default features disables `proptest` arbitrary module.

Then use it in your project like that:
```rust
use uuid::Uuid;
use shorter_uuid::{Expand, Shorten};

fn main() -> Result<(), Error> {
    // Expands string with `BASE57` alphabet.
    let e = Uuid::expand("mavTAjNm4NVztDwh4gdSrQ")?;
    let u = Uuid::parse_str("806d0969-95b3-433b-976f-774611fdacbb")?;
    
    // Encodes `u` with `BASE57` alphabet.
    assert_eq!(format!("{}", u.shorten()), "mavTAjNm4NVztDwh4gdSrQ"); 
    assert_eq!(e, u);
    Ok(())
}
```

Check [API documentation][docs.rs] for details.
