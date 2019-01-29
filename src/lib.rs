/*
 * Copyright 2019 Alexey Shuksto.
 *
 * See the COPYRIGHT file at the top-level directory of this distribution.
 *
 * Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
 * http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
 * <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
 * option. This file may not be copied, modified, or distributed
 * except according to those terms.
 */

//! This is a simple create which allows some shortening of UUID
//! based on properties of given [`Alphabet`].
//!
//! 'Out of the box' this crate provides two alphabets:
//! 2. [`BASE62`] -- contains `0-9A-Za-z` symbols;
//! 1. [`BASE57`] -- contains [`BASE62`] symbols than a harder to mistake with one another.
//!
//! # Usage
//!
//! ```rust
//! use std::error::Error;
//! use std::io::Write;
//!
//! use uuid::Uuid;
//! use shorter_uuid::{BASE57, Expand, ShortUuid, Shorten};
//!
//! fn main() -> Result<(), Box<Error>> {
//!     let u = Uuid::parse_str("806d0969-95b3-433b-976f-774611fdacbb")?;
//!
//!     // Encodes `u` with `BASE57` alphabet.
//!     let s = ShortUuid::from_uuid(u, &BASE57);
//!     assert_eq!(format!("{}", s), "mavTAjNm4NVztDwh4gdSrQ");
//!
//!     // Expands string via `Shorten` trait
//!     // and `BASE57` alphabet (default).
//!     let e = Uuid::expand("mavTAjNm4NVztDwh4gdSrQ")?;
//!     assert_eq!(e, u);
//!     Ok(())
//! }
//! ```
//!
//! [`Alphabet`]: struct.Alphabet.html
//! [`BASE62`]: struct.BASE62.html
//! [`BASE57`]: struct.BASE57.html

// `shorten_uuid` types in rustdoc of other crates get linked to here.
#![doc(html_root_url = "https://docs.rs/shorter_uuid/0.1.0")]

use std::fmt;
use std::fmt::Write;
use std::ops::Deref;
use std::result;

use uuid::Uuid;

pub use alphabet::{Alphabet, BASE57, BASE62};
pub use error::{Error, Result};

mod alphabet;
mod error;

#[cfg(feature = "proptest")]
pub mod proptest_support;

/// Holds uuid along it's short representation as `Vec<u8>`.
#[derive(Debug, Eq, PartialEq, Clone)]
pub struct ShortUuid {
    short: Vec<u8>,
    uuid: Uuid,
}

/// Extension trait that allows expansion of uuid-like data
/// from shortened string representation.
pub trait Expand
where
    Self: Sized,
{
    /// Expands given string into `Self`. Uses [`BASE57`] alphabet for expansion.
    /// Intermediate [`ShortUuid`] is dropped immediately after expansion.
    ///
    /// # Errors
    /// * [`Error::AlphabetOverflow`]
    ///   if usage of given alphabet results into arithmetic overflow,
    ///   most likely due to wrong alphabet.
    ///
    /// # Examples
    /// ```rust
    /// # use std::error::Error;
    /// # use std::io::Write;
    /// #
    /// # use uuid::Uuid;
    /// # use shorter_uuid::{BASE57, Expand};
    /// #
    /// # fn main() -> Result<(), Box<Error>> {
    /// let u = Uuid::parse_str("806d0969-95b3-433b-976f-774611fdacbb")?;
    /// let e = Uuid::expand("mavTAjNm4NVztDwh4gdSrQ")?;
    /// assert_eq!(e, u);
    /// #     Ok(())
    /// # }
    /// ```
    /// [`BASE57`]: struct.BASE57.html
    /// [`ShortUuid`]: struct.ShortUuid.html
    /// [`Error::AlphabetOverflow`]: enum.Error.html#variant.AlphabetOverflow
    fn expand(s: &str) -> Result<Self> {
        Self::expand_with(s, &BASE57)
    }

    /// Expands string with given [`Alphabet`] into `Self`.
    /// Intermediate [`ShortUuid`] is dropped immediately after expansion.
    ///
    /// # Errors
    /// * [`Error::AlphabetOverflow`]
    ///   if usage of given alphabet results into arithmetic overflow,
    ///   most likely due to wrong alphabet.
    ///
    /// # Examples
    /// ```rust
    /// # use std::error::Error;
    /// # use std::io::Write;
    /// #
    /// # use uuid::Uuid;
    /// # use shorter_uuid::{BASE57, Expand};
    /// #
    /// # fn main() -> Result<(), Box<Error>> {
    /// let u = Uuid::parse_str("806d0969-95b3-433b-976f-774611fdacbb")?;
    /// let e = Uuid::expand_with("mavTAjNm4NVztDwh4gdSrQ", &BASE57)?;
    /// assert_eq!(e, u);
    /// #     Ok(())
    /// # }
    /// ```
    ///
    /// [`Alphabet`]: struct.Alphabet.html
    /// [`ShortUuid`]: struct.ShortUuid.html
    /// [`Error::AlphabetOverflow`]: enum.Error.html#variant.AlphabetOverflow
    fn expand_with(s: &str, abc: &Alphabet) -> Result<Self>;
}

/// Extension trait that allows shortening of uuid-like data into [`ShortUuid`].
///
/// [`ShortUuid`]: struct.ShortUuid.html
pub trait Shorten
where
    Self: Sized,
{
    /// Shortens `Self` into [`ShortUuid`]. Uses [`BASE57`] alphabet for shortening.
    ///
    /// # Examples
    /// ```rust
    /// # use std::error::Error;
    /// # use std::io::Write;
    /// #
    /// # use uuid::Uuid;
    /// # use shorter_uuid::{BASE57, Shorten};
    /// #
    /// # fn main() -> Result<(), Box<Error>> {
    /// let u = Uuid::parse_str("806d0969-95b3-433b-976f-774611fdacbb")?;
    /// assert_eq!(format!("{}", u.shorten()), "mavTAjNm4NVztDwh4gdSrQ");
    /// #     Ok(())
    /// # }
    /// ```
    ///
    /// [`BASE57`]: struct.BASE57.html
    /// [`ShortUuid`]: struct.ShortUuid.html
    fn shorten(self) -> ShortUuid {
        self.shorten_with(&BASE57)
    }

    /// Shortens `Self` into [`ShortUuid`] with given [`Alphabet`].
    ///
    /// # Examples
    /// ```rust
    /// # use std::error::Error;
    /// # use std::io::Write;
    /// #
    /// # use uuid::Uuid;
    /// # use shorter_uuid::{BASE57, Shorten};
    /// #
    /// # fn main() -> Result<(), Box<Error>> {
    /// let u = Uuid::parse_str("806d0969-95b3-433b-976f-774611fdacbb")?;
    /// assert_eq!(format!("{}", u.shorten_with(&BASE57)), "mavTAjNm4NVztDwh4gdSrQ");
    /// #     Ok(())
    /// # }
    /// ```
    ///
    /// [`Alphabet`]: struct.Alphabet.html
    /// [`ShortUuid`]: struct.ShortUuid.html
    fn shorten_with(self, abc: &Alphabet) -> ShortUuid;
}

impl ShortUuid {
    /// Creates [`ShortUuid`] uuid representation for given [`Alphabet`].
    /// Moves uuid into it.
    ///
    /// [`Alphabet`]: struct.Alphabet.html
    /// [`ShortUuid`]: struct.ShortUuid.html
    ///
    /// # Examples
    ///
    /// ```rust
    /// # use std::error::Error;
    /// # use std::io::Write;
    /// #
    /// # use uuid::Uuid;
    /// # use shorter_uuid::{BASE57, ShortUuid};
    /// #
    /// # fn main() -> Result<(), Box<Error>> {
    /// let u = Uuid::parse_str("806d0969-95b3-433b-976f-774611fdacbb")?;
    /// let s = ShortUuid::from_uuid(u, &BASE57);
    ///
    /// let mut v = Vec::new();
    /// write!(v, "{}", s);
    /// assert_eq!(v, b"mavTAjNm4NVztDwh4gdSrQ");
    /// #     Ok(())
    /// # }
    /// ```
    pub fn from_uuid(uuid: Uuid, abc: &Alphabet) -> ShortUuid {
        let len = abc.len() as u128;
        let mut div = u128::from_be_bytes(*uuid.as_bytes());
        let mut short = Vec::new();
        while div != 0 {
            short.push(abc[(div % len) as usize]);
            div /= len;
        }
        short.shrink_to_fit();
        ShortUuid { short, uuid }
    }

    /// Creates [`ShortUuid`] representation from given string and parses uuid from it with given
    /// [`Alphabet`].
    ///
    /// # Errors
    /// * [`Error::AlphabetOverflow`]
    ///   if usage of given alphabet results into arithmetic overflow, most likely due to wrong
    ///   alphabet.
    ///
    /// [`Alphabet`]: struct.Alphabet.html
    /// [`ShortUuid`]: struct.ShortUuid.html
    /// [`Error::AlphabetOverflow`]: enum.Error.html#variant.AlphabetOverflow
    ///
    /// # Examples
    ///
    /// ```rust
    /// # use std::error::Error;
    /// # use std::io::Write;
    /// #
    /// # use uuid::Uuid;
    /// # use shorter_uuid::{BASE57, ShortUuid};
    /// #
    /// # fn main() -> Result<(), Box<Error>> {
    /// let u = Uuid::parse_str("806d0969-95b3-433b-976f-774611fdacbb")?;
    /// let s = ShortUuid::from_str("mavTAjNm4NVztDwh4gdSrQ", &BASE57)?;
    ///
    /// assert_eq!(*(&s as &Uuid), u);
    /// #     Ok(())
    /// # }
    /// ```
    pub fn from_str(s: &str, abc: &Alphabet) -> Result<ShortUuid> {
        let len = abc.len() as u128;
        let short = Vec::from(s.as_bytes());
        short
            .iter()
            .rev()
            .fold(Ok(0u128), |acc, &u| {
                acc.and_then(|acc| {
                    abc.position(u).and_then(|i| {
                        acc.checked_mul(len)
                            .and_then(|acc| acc.checked_add(i as u128))
                            .map_or_else(|| Err(Error::AlphabetOverflow), Ok)
                    })
                })
            })
            .map(|u| {
                let uuid = Uuid::from_bytes(u.to_be_bytes());
                ShortUuid { short, uuid }
            })
    }

    /// Coverts current [`ShortUuid`] into given [`Alphabet`].
    ///
    /// [`ShortUuid`]: struct.ShortUuid.html
    /// [`Alphabet`]: ../alphabet/struct.Alphabet.html
    ///
    /// # Examples
    ///
    /// ```rust
    /// # use std::error::Error;
    /// # use std::io::Write;
    /// #
    /// # use uuid::Uuid;
    /// # use shorter_uuid::{BASE57, BASE62, ShortUuid};
    /// #
    /// # fn main() -> Result<(), Box<Error>> {
    /// let uid = Uuid::parse_str("806d0969-95b3-433b-976f-774611fdacbb")?;
    /// let s62 = ShortUuid::from_uuid(uid, &BASE62);
    /// let s57 = s62.clone().into_alphabet(&BASE57);
    ///
    /// let mut v = Vec::new();
    /// write!(v, "{}", s57);
    /// assert_eq!(v, b"mavTAjNm4NVztDwh4gdSrQ");
    ///
    /// assert_eq!(s57.into_alphabet(&BASE62), s62);
    /// #     Ok(())
    /// # }
    /// ```
    pub fn into_alphabet(self, abc: &Alphabet) -> ShortUuid {
        Self::from_uuid(self.uuid, abc)
    }
}

impl Deref for ShortUuid {
    type Target = Uuid;

    fn deref(&self) -> &Self::Target {
        &self.uuid
    }
}

impl fmt::Display for ShortUuid {
    fn fmt(&self, f: &mut fmt::Formatter) -> result::Result<(), fmt::Error> {
        self.short
            .iter()
            .fold(Ok(()), |acc, &u| acc.and_then(|_| f.write_char(u as char)))
    }
}

impl Expand for Uuid {
    fn expand_with(s: &str, abc: &Alphabet) -> Result<Self> {
        ShortUuid::from_str(s, abc).map(|s| s.uuid)
    }
}

impl Shorten for Uuid {
    fn shorten_with(self, abc: &Alphabet) -> ShortUuid {
        ShortUuid::from_uuid(self, abc)
    }
}

#[cfg(test)]
mod tests {
    use std::fmt::Write;

    use proptest::prelude::*;
    use proptest::*;
    use uuid::Uuid;

    use super::*;

    proptest! {
        #[test]
        fn from_uuid_shortens(bs in any::<[u8; 16]>(), abc in any::<Alphabet>()) {
            let len = abc.len() as u128;
            let uid = Uuid::from_bytes(bs);
            let mut div = u128::from_be_bytes(bs);
            let mut vec = Vec::new();

            while div != 0 {
                vec.push(abc[(div % len) as usize]);
                div /= len;
            }

            let su = ShortUuid::from_uuid(uid, &abc);
            prop_assert_eq!(su.uuid, uid);
            prop_assert_eq!(su.short, vec);
        }

        #[test]
        fn from_str_expands(bs in any::<[u8; 16]>(),
                            abc in any::<Alphabet>(),
                            cba in any::<Alphabet>()) {
            let su1 = ShortUuid::from_uuid(Uuid::from_bytes(bs), &abc);
            let str = format!("{}", su1.clone());

            let su2 = ShortUuid::from_str(&str, &abc).unwrap();
            prop_assert_eq!(su2.clone(), su1.clone());

            match ShortUuid::from_str(&str, &cba) {
                Ok(su3) => {
                    if cba == abc {
                        prop_assert_eq!(su3, su1);
                    } else {
                        prop_assert_ne!(su3, su2);
                    }
                }
                Err(Error::AlphabetOverflow) => {
                    prop_assert!(cba.len() > abc.len(),
                        "'Error::AlphabetOverflow' false positive");
                }
                Err(Error::AlphabetSymbolNotFound(u)) => {
                    prop_assert_eq!(cba.position(u), Err(Error::AlphabetSymbolNotFound(u)),
                        "'Error::AlphabetSymbolNotFound' false positive: {}", u as char);
                }
                Err(err) => prop_assert!(false, "Unexpected error variant: {}", err),
            }
        }

        #[test]
        fn into_alphabet_converts(su in any::<ShortUuid>(), abc in any::<Alphabet>()) {
            let cv = su.clone().into_alphabet(&abc);
            let fu = ShortUuid::from_uuid(su.clone().uuid, &abc);

            prop_assert_eq!(cv, fu);
        }

        #[test]
        fn into_uuid_derefs(su in any::<ShortUuid>()) {
            let &uid: &Uuid = &su;
            prop_assert_eq!(uid, su.uuid);
        }

        #[test]
        fn fmt_display_short(su in any::<ShortUuid>()) {
            let mut bytes_out = String::new();
            for u in su.short.clone() {
                write!(bytes_out, "{}", u as char).unwrap();
            }

            let short_out = format!("{}", su);
            prop_assert_eq!(short_out, bytes_out);
        }

        #[test]
        fn uuid_expand_with_eq_from(su in any::<ShortUuid>(), abc in any::<Alphabet>()) {
            let su = su.into_alphabet(&abc);
            let fs = format!("{}", su);
            prop_assert_eq!(Uuid::expand_with(&fs, &abc), Ok(*(&su as &Uuid)));
        }

        #[test]
        fn uuid_expand_with_base57(su in any::<ShortUuid>()) {
            let fs = format!("{}", su.into_alphabet(&BASE57));
            prop_assert_eq!(Uuid::expand(&fs), Uuid::expand_with(&fs, &BASE57));
        }

        #[test]
        fn uuid_shorten_with_eq_from(bs in any::<[u8; 16]>(), abc in any::<Alphabet>()) {
            let u = Uuid::from_bytes(bs);
            prop_assert_eq!(u.shorten_with(&abc), ShortUuid::from_uuid(u, &abc));
        }

        #[test]
        fn uuid_shorten_with_base57(bs in any::<[u8; 16]>()) {
            let u = Uuid::from_bytes(bs);
            prop_assert_eq!(u.shorten(), u.shorten_with(&BASE57));
        }
    }
}
