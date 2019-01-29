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

//! `proptest` arbitrary implementations and parameters.

use proptest::prelude::*;
use uuid::Uuid;

use crate::{Alphabet, ShortUuid};

/// [`Alphabet`] arbitrary parameters: byte generation strategy & maximum length.
///
/// [`Alphabet`]: ../struct.Alphabet.html
#[derive(Clone, Debug)]
pub struct AlphabetParameters {
    pub byte: SBoxedStrategy<u8>,
    pub max_len: usize,
}

/// [`ShortUuid`] arbitrary parameters: [alphabet parameters] & uuid generation strategy.
///
/// [`ShortUuid`]: ../struct.ShortUuid.html
/// [alphabet parameters]: struct.AlphabetParameters.html
#[derive(Clone, Debug)]
pub struct ShortUuidParameters {
    pub alphabet: AlphabetParameters,
    pub uuid: SBoxedStrategy<Uuid>,
}

impl Default for AlphabetParameters {
    fn default() -> Self {
        let max_len = 128usize;
        let byte = any::<u8>()
            .prop_filter("Accepts only printable ASCII characters", |&u| {
                0x20 <= u && u < 0x80
            })
            .sboxed();
        AlphabetParameters { byte, max_len }
    }
}

impl Arbitrary for Alphabet {
    type Parameters = AlphabetParameters;

    fn arbitrary_with(args: Self::Parameters) -> Self::Strategy {
        prop::collection::vec(args.byte, 2..args.max_len)
            .prop_map(|mut v| {
                v.sort_unstable();
                v.dedup();
                v
            })
            .prop_filter("Accepts only vectors longer than 2 bytes", |v| v.len() >= 2)
            .prop_map(|v| Alphabet::from_bytes(&v).unwrap())
            .sboxed()
    }

    type Strategy = SBoxedStrategy<Alphabet>;
}

impl Default for ShortUuidParameters {
    fn default() -> Self {
        let uuid = any::<[u8; 16]>().prop_map(Uuid::from_bytes).sboxed();
        let alphabet = AlphabetParameters::default();
        ShortUuidParameters { alphabet, uuid }
    }
}

impl Arbitrary for ShortUuid {
    type Parameters = ShortUuidParameters;

    fn arbitrary_with(args: Self::Parameters) -> Self::Strategy {
        (args.uuid, any_with::<Alphabet>(args.alphabet))
            .prop_map(|(uid, abc)| ShortUuid::from_uuid(uid, &abc))
            .sboxed()
    }

    type Strategy = SBoxedStrategy<ShortUuid>;
}
