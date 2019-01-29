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

use std::ops::Index;

use lazy_static::lazy_static;

use super::{Error, Result};

/// Uuid shortening alphabet.
#[derive(Clone, Debug, Eq, Hash, PartialEq)]
pub struct Alphabet(Vec<u8>);

lazy_static! {
    /// Printable ASCII symbols that are hard to mistake with each other.
    pub static ref BASE57: Alphabet =
        Alphabet::from_bytes(b"23456789ABCDEFGHJKLMNPQRSTUVWXYZabcdefghijkmnopqrstuvwxyz").unwrap();
    /// Printable ASCII symbols.
    pub static ref BASE62: Alphabet =
        Alphabet::from_bytes(b"0123456789ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz")
            .unwrap();
}

#[allow(clippy::len_without_is_empty)]
impl Alphabet {
    /// Creates new instance of [`Alphabet`] with given byte slice.
    /// Will sort bytes and remove duplicates for consistency.
    ///
    /// # Errors
    /// * [`Error::AlphabetTooShort`]
    ///   if alphabet contains less than two symbols after deduplication;
    /// * [`Error::AlphabetSymbolNonPrintable`]
    ///   if alphabet contains some non-printable symbols.
    ///
    /// [`Alphabet`]: struct.Alphabet.html
    /// [`Error::AlphabetSymbolNonPrintable`]: enum.Error.html#variant.AlphabetSymbolNonPrintable
    /// [`Error::AlphabetTooShort`]: enum.Error.html#variant.AlphabetTooShort
    ///
    /// TODO: `impl TryFrom<&[u8]>`
    ///
    /// # Examples
    ///
    /// ```rust
    /// # use std::error;
    /// #
    /// # use shorter_uuid::{Alphabet, Error};
    /// #
    /// # fn main() -> Result<(), Box<error::Error>> {
    /// let abc = Alphabet::from_bytes(b"abc")?;
    /// let cba = Alphabet::from_bytes(b"cba")?;
    /// assert_eq!(abc, cba);
    ///
    /// let bbc = Alphabet::from_bytes(b"bbcaca")?;
    /// assert_eq!(abc, bbc);
    ///
    /// match Alphabet::from_bytes(b"a") {
    ///     Err(Error::AlphabetTooShort(u)) => assert_eq!(u, 1),
    ///     _ => panic!("should not allow alphabets with less than 2 symbols"),
    /// };
    /// #     Ok(())
    /// # }
    /// ```
    pub fn from_bytes(bytes: &[u8]) -> Result<Alphabet> {
        let mut abc = Vec::from(bytes);
        abc.sort_unstable();
        abc.dedup();

        if let Some(&np) = abc.iter().find(|&&u| 0x20 > u || u >= 0x80) {
            return Err(Error::AlphabetSymbolNonPrintable(np));
        }
        if abc.len() <= 1 {
            return Err(Error::AlphabetTooShort(abc.len()));
        }

        abc.shrink_to_fit();
        Ok(Alphabet(abc))
    }

    /// Returns the number of symbols in the [`Alphabet`].
    ///
    /// [`Alphabet`]: struct.Alphabet.html
    ///
    /// # Examples
    ///
    /// ```rust
    /// # use std::error::Error;
    /// #
    /// # use shorter_uuid::Alphabet;
    /// #
    /// # fn main() -> Result<(), Box<Error>> {
    /// let a = Alphabet::from_bytes(b"ABC")?;
    ///
    /// assert_eq!(a.len(), 3);
    /// #     Ok(())
    /// # }
    /// ```
    pub fn len(&self) -> usize {
        self.0.len()
    }

    /// Returns the index of symbol in the [`Alphabet`].
    ///
    /// # Errors
    /// * [`Error::AlphabetSymbolNotFound`]
    ///   if given symbol was not found.
    ///
    /// [`Alphabet`]: struct.Alphabet.html
    /// [`Error::AlphabetSymbolNotFound`]: enum.Error.html#variant.AlphabetSymbolNotFound
    ///
    /// # Examples
    ///
    /// ```rust
    /// # use std::error;
    /// #
    /// # use shorter_uuid::{Alphabet, Error};
    /// #
    /// # fn main() -> Result<(), Box<error::Error>> {
    /// let a = Alphabet::from_bytes(b"ABC")?;
    ///
    /// match a.position('B' as u8) {
    ///    Ok(i) => assert_eq!(i, 1),
    ///    _ => panic!("should return position of symbol in alphabet"),
    /// }
    ///
    /// match a.position('D' as u8) {
    ///    Err(Error::AlphabetSymbolNotFound(u)) => assert_eq!(u, 'D' as u8),
    ///    _ => panic!("should return error for unknown symbols"),
    /// }
    /// #     Ok(())
    /// # }
    /// ```
    pub fn position(&self, u: u8) -> Result<usize> {
        self.0
            .binary_search(&u)
            .map_err(|_| Error::AlphabetSymbolNotFound(u))
    }
}

impl Index<usize> for Alphabet {
    type Output = u8;

    fn index(&self, idx: usize) -> &Self::Output {
        &self.0[idx]
    }
}

#[cfg(test)]
mod tests {
    use proptest::prelude::*;
    use proptest::*;

    use super::Alphabet;
    use crate::Error;

    proptest! {
        #[test]
        fn from_bytes_sorted_deduped(str in ".*") {
            let mut probe = Vec::from(str.as_bytes());
            probe.sort_unstable();
            probe.dedup();

            match Alphabet::from_bytes(str.as_bytes()) {
                Ok(Alphabet(vec)) => prop_assert_eq!(vec, probe),
                Err(Error::AlphabetSymbolNonPrintable(u)) => {
                    prop_assert!(probe.contains(&u), "Probe does not contains '{}'", u as char);
                    prop_assert!((0x20 > u || u >= 0x80), "Printable character: '{}'", u as char);
                }
                Err(Error::AlphabetTooShort(u)) => {
                    prop_assert!(probe.len() <= 1, "Probe length bigger than 1: {}", probe.len());
                    prop_assert_eq!(u, probe.len());
                }
                Err(err) => prop_assert!(false, "Unexpected error variant: {}", err),
            }
        }

        #[test]
        fn len_equals_vec(abc in any::<Alphabet>()) {
            prop_assert_eq!(abc.len(), abc.0.len())
        }

        #[test]
        fn idx_equals_vec((i, abc) in any::<Alphabet>().prop_flat_map(|abc| {
            (0..abc.len(), Just(abc))
        })) {
            prop_assert_eq!(abc[i], abc.0[i])
        }

        #[test]
        fn pos_equals_vec_bs(abc in any::<Alphabet>(), u in any::<u8>()) {
            let abp = abc.position(u);
            let bsp = abc.0.binary_search(&u);
            match bsp {
                Ok(i) => {
                    prop_assert_eq!(abp, Ok(i));
                }
                Err(_) => {
                    prop_assert_eq!(abp, Err(Error::AlphabetSymbolNotFound(u)));
                }
            }
        }
    }
}
