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

use std::{error, fmt, result};

/// Alias for `std::result::Result<_, crate::Error>`.
pub type Result<T> = result::Result<T, Error>;

/// [`shorter_uuid`] crate internal error variants.
///
/// [`shorter_uuid`]: index.html
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub enum Error {
    /// Raised if arithmetic overflow error occurs during shorter uuid
    /// representation expansion.
    AlphabetOverflow,
    /// Raised in alphabet contains `non-printable` ASCII symbol.
    AlphabetSymbolNonPrintable(u8),
    /// Raised if symbol lookup during shorter uuid representation
    /// expansion fails
    AlphabetSymbolNotFound(u8),
    /// Raised for alphabets shorted that two distinct symbols.
    AlphabetTooShort(usize),
}

impl fmt::Display for Error {
    fn fmt(&self, f: &mut fmt::Formatter) -> result::Result<(), fmt::Error> {
        match self {
            Error::AlphabetOverflow => write!(f, "Arithmetic overflow (wrong alphabet?)"),
            Error::AlphabetSymbolNonPrintable(u) => {
                write!(f, "Alphabet symbol non printable: '{:x}'", u)
            }
            Error::AlphabetSymbolNotFound(u) => write!(f, "Alphabet symbol not found: '{}'", u),
            Error::AlphabetTooShort(u) => write!(f, "Alphabet is too short: {} <= 1", u),
        }
    }
}

impl error::Error for Error {
    fn source(&self) -> Option<&(dyn error::Error + 'static)> {
        None
    }
}
