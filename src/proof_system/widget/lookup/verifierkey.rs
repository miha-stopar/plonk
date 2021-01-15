// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
//
// Copyright (c) DUSK NETWORK. All rights reserved.

use crate::commitment_scheme::kzg10::Commitment;
use crate::proof_system::linearisation_poly::ProofEvaluations;
use crate::fft::Polynomial;
use dusk_bls12_381::{BlsScalar, G1Affine};

#[derive(Debug, PartialEq, Eq, Clone)]
pub struct VerifierKey {
    pub q_lookup: Commitment,
    pub table_1_poly: Polynomial,
    pub table_2_poly: Polynomial,
    pub table_3_poly: Polynomial,
    pub table_4_poly: Polynomial,
}
