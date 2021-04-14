// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
//
// Copyright (c) DUSK NETWORK. All rights reserved.

#![allow(clippy::too_many_arguments)]

use crate::constraint_system::StandardComposer;
use crate::constraint_system::Variable;
use dusk_bls12_381::BlsScalar;
use std::convert::TryInto;
use std::io;
use std::io::Write;

impl StandardComposer {
    /// Generates plookup table with byte-wise XOR table,
    /// 4-bit range table, 7-bit range table, and 2-bit range table
    pub fn generate_blake_table(&mut self) {
        // 2^16 row byte-wise XOR table
        for i in 0..2u16.pow(8) {
            for j in 0..2u16.pow(8) {
                self.lookup_table.0.push([
                    BlsScalar::from(i as u64),
                    BlsScalar::from(j as u64),
                    BlsScalar::from((i ^ j) as u64),
                    BlsScalar::one(),
                ]);
            }
        }
        // 2^4 row 4-bit range table
        for i in 0..2u16.pow(4) {
            self.lookup_table.0.push([
                BlsScalar::from(i as u64),
                BlsScalar::zero(),
                BlsScalar::zero(),
                BlsScalar::from(2),
            ]);
        }
        // 2^7 row 7-bit range table
        for i in 0..2u16.pow(7) {
            self.lookup_table.0.push([
                BlsScalar::from(i as u64),
                BlsScalar::zero(),
                BlsScalar::zero(),
                BlsScalar::from(3),
            ]);
        }
        // 2^2 row 2-bit range table
        for i in 0..2u16.pow(2) {
            self.lookup_table.0.push([
                BlsScalar::from(i as u64),
                BlsScalar::zero(),
                BlsScalar::zero(),
                BlsScalar::from(4),
            ]);
        }
    }

    /// Creates a single 256-bit scalar variable from 32 byte variables
    pub fn compose_scalar_from_le_bytes(&mut self, bytes: &[Variable]) -> Variable {
        // Checks if bytes.len() is a power of two
        assert_eq!(bytes.len(), 32);

        // compose 32-bit words from 4 range-checked bytes
        let mut words = [self.zero_var; 8];
        for i in 0..8 {
            words[i] = self.compose_word_from_le_bytes(&bytes[4 * i..4 * (i + 1)]);
        }

        // compose 8-byte octs
        let mut octs = [self.zero_var; 4];
        for i in 0..4 {
            octs[i] = self.add(
                (BlsScalar::from(1 << 32), words[2 * i + 1]),
                (BlsScalar::one(), words[2 * i]),
                BlsScalar::zero(),
                BlsScalar::zero(),
            );
        }

        // compose 16-byte hexes
        let mut hexes = [self.zero_var; 2];
        for i in 0..2 {
            hexes[i] = self.add(
                (BlsScalar::from_raw([0, 1, 0, 0]), octs[2 * i + 1]),
                (BlsScalar::one(), octs[2 * i]),
                BlsScalar::zero(),
                BlsScalar::zero(),
            );
        }

        // compose 32-byte/256-bit scalar
        self.add(
            (BlsScalar::from_raw([0, 0, 1, 0]), hexes[1]),
            (BlsScalar::one(), hexes[0]),
            BlsScalar::zero(),
            BlsScalar::zero(),
        )
    }

    /// Creates a variable y = x0*2^(8*3) + x1*2^(8*2) + x2*2^(8*1) + x3
    /// such that if x0..x3 are bytes, then y is the 32-bit concatenation
    /// x0|x1|x2|x3.
    pub fn compose_word_from_le_bytes(&mut self, bytes: &[Variable]) -> Variable {
        assert_eq!(bytes.len(), 4);

        // Prove 4 pieces of word are actually bytes by looking them up in the byte-sized lookup table
        // If (A, B, A^B) is in the lookup table, then A and B are both less than 2^8
        // Uses 2 lookup gates to replace 8 gates used for a 8-bit range check

        let byte_3_xor_byte_2_var = self.add_input(BlsScalar::from(
            self.variables[&bytes[3]].reduce().0[0] ^ self.variables[&bytes[2]].reduce().0[0],
        ));

        let byte_1_xor_byte_0_var = self.add_input(BlsScalar::from(
            self.variables[&bytes[1]].reduce().0[0] ^ self.variables[&bytes[0]].reduce().0[0],
        ));

        // use the bytewise XOR table to show that all bytes are truly < 2^8
        let one_var = self.add_input(BlsScalar::one());
        self.plookup_gate(
            bytes[3],
            bytes[2],
            byte_3_xor_byte_2_var,
            Some(one_var),
            BlsScalar::zero(),
        );
        self.plookup_gate(
            bytes[1],
            bytes[0],
            byte_1_xor_byte_0_var,
            Some(one_var),
            BlsScalar::zero(),
        );

        let pair_hi = self.add(
            (BlsScalar::from(1 << 8), bytes[3]),
            (BlsScalar::one(), bytes[2]),
            BlsScalar::zero(),
            BlsScalar::zero(),
        );

        let pair_lo = self.add(
            (BlsScalar::from(1 << 8), bytes[1]),
            (BlsScalar::one(), bytes[0]),
            BlsScalar::zero(),
            BlsScalar::zero(),
        );

        self.add(
            (BlsScalar::from(1 << 16), pair_hi),
            (BlsScalar::one(), pair_lo),
            BlsScalar::zero(),
            BlsScalar::zero(),
        )
    }

    /// Modular division by 2^32
    pub fn mod_u32(&mut self, d: Variable) -> Variable {
        // Get u64 value of dividend
        let dividend = self.variables[&d].reduce().0[0];

        // Compute quotient and add as variable
        let quotient = dividend / 2_u64.pow(32);
        let quotient_var = self.add_input(BlsScalar::from(quotient));

        // dividend = quotient * 2^32 + remainder
        // each dividend comes from the sum of two or three
        // u32 words, so the quotient should be less than 4 (2 bits)

        // use the fourth partition of the table to show the quotient
        // is less than 4
        let four_var = self.add_input(BlsScalar::from(4));
        self.plookup_gate(
            quotient_var,
            self.zero_var,
            self.zero_var,
            Some(four_var),
            BlsScalar::zero(),
        );

        // Show mod has been done correctly with a single add gate
        // which returns the variable holding the remainder
        self.add(
            (BlsScalar::one(), d),
            (-BlsScalar::from(2_u64.pow(32)), quotient_var),
            BlsScalar::zero(),
            BlsScalar::zero(),
        )
    }

    /// Decomposes a variable d into 4 bytes d0, d1, d2, d3 so that
    /// d = d0|d1|d2|d3 and adds the required gates showing decomposition is correct
    pub fn decompose_word_into_le_bytes(&mut self, word: Variable) -> [Variable; 4] {
        let word_value = self.variables[&word].reduce().0[0];
        let word_bytes = word_value.to_le_bytes();
        let mut word_vars = [self.zero_var; 4];

        // create variables for each byte
        for i in 0..4 {
            word_vars[i] = self.add_input(BlsScalar::from(word_bytes[i] as u64));
        }

        // show bytes compose to input word
        self.compose_word_from_le_bytes(&word_vars);

        word_vars
    }

    /// Adds three variables by adding byte-by-byte, composing the bytes, and modding
    /// by 2**32
    pub fn add_three_mod_2_32(
        &mut self,
        v: &mut [Variable; 64],
        a: usize,
        b: usize,
        x: &[Variable],
    ) {
        // v[a] := (v[a] + v[b] + x) mod 2**w
        for i in 0..4 {
            // v[a] += v[b]
            v[4 * a + i] = self.add(
                (BlsScalar::one(), v[4 * a + i]),
                (BlsScalar::one(), v[4 * b + i]),
                BlsScalar::zero(),
                BlsScalar::zero(),
            );

            // v[a] += x
            v[4 * a + i] = self.add(
                (BlsScalar::one(), v[4 * a + i]),
                (BlsScalar::one(), x[i]),
                BlsScalar::zero(),
                BlsScalar::zero(),
            );
        }

        // compose the bytes back into a single integer
        // so we can compute the mod operation
        let sum = self.compose_word_from_le_bytes(&v[4 * a..(4 * a + 4)]);

        // compute the remainder mod 2^32
        let remainder = self.mod_u32(sum);

        // decompose remainder back into bytes and add
        // gates showing decomposition is correct
        let decomposed_bytes = self.decompose_word_into_le_bytes(remainder);
        v[4 * a] = decomposed_bytes[0];
        v[4 * a + 1] = decomposed_bytes[1];
        v[4 * a + 2] = decomposed_bytes[2];
        v[4 * a + 3] = decomposed_bytes[3];
    }

    /// Adds two variables by adding byte-by-byte, composing the bytes, and modding
    /// by 2**32
    pub fn add_two_mod_2_32(&mut self, v: &mut [Variable; 64], c: usize, d: usize) {
        // v[c] := (v[c] + v[d])     mod 2**w
        for i in 0..4 {
            // v[c] += v[d]
            v[4 * c + i] = self.add(
                (BlsScalar::one(), v[4 * c + i]),
                (BlsScalar::one(), v[4 * d + i]),
                BlsScalar::zero(),
                BlsScalar::zero(),
            );
        }

        // compose the bytes back into a single integer
        // so we can compute the mod operation
        let sum = self.compose_word_from_le_bytes(&v[4 * c..(4 * c + 4)]);

        // compute the remainder mod 2^32
        let remainder = self.mod_u32(sum);

        // decompose remainder back into bytes and add
        // gates showing decomposition is correct
        let decomposed_bytes = self.decompose_word_into_le_bytes(remainder);

        v[4 * c] = decomposed_bytes[0];
        v[4 * c + 1] = decomposed_bytes[1];
        v[4 * c + 2] = decomposed_bytes[2];
        v[4 * c + 3] = decomposed_bytes[3];
    }

    /// Rotates to the right by 16 bits by shuffling variables in the working vector
    fn rotate_16(&mut self, v: &mut [Variable; 64], n: usize) {
        // rotate bytes to the right 2 so that v[n+2] := v[n] etc.
        let mut initial = [self.zero_var; 4];
        initial.clone_from_slice(&v[4 * n..(4 * n + 4)]);
        for i in 0..4 {
            v[4 * n + (i + 2) % 4] = initial[i];
        }
    }

    /// Rotates to the right by 8 bits by shuffling variables in the working vector
    fn rotate_8(&mut self, v: &mut [Variable; 64], n: usize) {
        // rotate bytes to the right 1 so that v[n-1] := v[n] etc.
        let mut initial = [self.zero_var; 4];
        initial.clone_from_slice(&v[4 * n..(4 * n + 4)]);
        for i in 0..4 {
            v[4 * n + (i + 3) % 4] = initial[i];
        }
    }

    /// Rotates to the right by 12 bits by spltting each byte into pieces and recomposing
    fn rotate_12(&mut self, v: &mut [Variable; 64], n: usize) {
        // first split each byte into 4-bit nibbles
        let mut nibbles = [self.zero_var; 8];
        for i in (0..4).rev() {
            let current_byte = self.variables[&v[4 * n + i]].reduce().0[0];
            let hi = current_byte >> 4;
            let lo = current_byte % (1 << 4);
            nibbles[2 * i] = self.add_input(BlsScalar::from(hi));
            nibbles[2 * i + 1] = self.add_input(BlsScalar::from(lo));

            // here we use the second parition of the table as a range check that verifies that both nibbles are indeed less than 2^4
            let two_var = self.add_input(BlsScalar::from(2));
            self.plookup_gate(
                nibbles[2 * i],
                self.zero_var,
                self.zero_var,
                Some(two_var),
                BlsScalar::zero(),
            );
            self.plookup_gate(
                nibbles[2 * i + 1],
                self.zero_var,
                self.zero_var,
                Some(two_var),
                BlsScalar::zero(),
            );
        }

        // now recompose the 8 nibbles into 4 bytes, shifting the nibbles
        // by 3 spaces to the right, so that the new first byte is made from the
        // pair of nibbles at indices 5 and 6.
        for i in 0..4 {
            v[4 * n + i] = self.add(
                (BlsScalar::from(1 << 4), nibbles[(2 * i + 5) % 8]),
                (BlsScalar::one(), nibbles[(2 * i + 2) % 8]),
                BlsScalar::zero(),
                BlsScalar::zero(),
            );
        }
    }

    /// Rotates to the right by 7 bits by spltting each byte into pieces and recomposing
    fn rotate_7(&mut self, v: &mut [Variable; 64], n: usize) {
        // first split each byte into 7 high bits and 1 low bit
        let mut split_bytes = [self.zero_var; 8];
        for i in (0..4).rev() {
            let current_byte = self.variables[&v[4 * n + i]].reduce().0[0];
            // 1 high bit
            let hi = current_byte >> 7;
            // 7 low bits
            let lo = current_byte % (1 << 7);

            // high bits are on even indices, low bits are on odd indices
            split_bytes[2 * i] = self.add_input(BlsScalar::from(hi));
            split_bytes[2 * i + 1] = self.add_input(BlsScalar::from(lo));

            // here we use the third parition of the table as a range check that verifies that the low bits are indeed less than 2^7
            let three_var = self.add_input(BlsScalar::from(3));
            self.plookup_gate(
                split_bytes[2 * i + 1],
                self.zero_var,
                self.zero_var,
                Some(three_var),
                BlsScalar::zero(),
            );

            // finally, show the high bit is actually a bit
            self.boolean_gate(split_bytes[2 * i]);
        }

        // Now recompose the 4 pairs of high and low bits into 4 bytes, shifting
        // shifting 1 space to the right, so that the new first byte is lo|hi,
        // using the low bits at index 3 and the high bit at index 0.
        // We do not need to range check the resulting byte since we already
        // checked the two pieces of each byte
        for i in 0..4 {
            v[4 * n + i] = self.add(
                // 7 low bits become new high bits
                (BlsScalar::from(2), split_bytes[(2 * i + 3) % 8]),
                // 1 high bit becomes new low bit
                (BlsScalar::one(), split_bytes[(2 * i) % 8]),
                BlsScalar::zero(),
                BlsScalar::zero(),
            );
        }
    }

    /// Performs a bit rotation right by 16, 12, 8, or 7 bits on the nth word
    pub fn rotate(&mut self, v: &mut [Variable; 64], n: usize, r: usize) {
        match r {
            16 => StandardComposer::rotate_16(self, v, n),
            12 => StandardComposer::rotate_12(self, v, n),
            8 => StandardComposer::rotate_8(self, v, n),
            7 => StandardComposer::rotate_7(self, v, n),
            _ => panic!("Not a valid rotation constant for blake2s"),
        };
    }

    /// Performs a byte-by-byte XOR of two words given their indices in the working vector
    pub fn xor_by_indices(&mut self, v: &mut [Variable; 64], d: usize, a: usize) {
        // v[d] := (v[d] ^ v[a])
        let mut right = [self.zero_var; 4];
        right.clone_from_slice(&v[4 * a..(4 * a + 4)]);
        self.xor(&mut v[4 * d..(4 * d + 4)], &right);
    }

    /// Performs an XOR in place, mutating the left word
    pub fn xor(&mut self, left: &mut [Variable], right: &[Variable]) {
        // left := left ^ right
        for i in 0..left.len() {
            let left_val = self.variables[&left[i]].reduce().0[0];
            let right_val = self.variables[&right[i]].reduce().0[0];
            let out_var = self.add_input(BlsScalar::from(left_val ^ right_val));
            let one_var = self.add_input(BlsScalar::one());
            left[i] =
                self.plookup_gate(left[i], right[i], out_var, Some(one_var), BlsScalar::zero());
        }
    }

    /// Performs an XOR in place, mutating the left word
    pub fn xor_debug(&mut self, left: &mut [Variable], right: &[Variable]) {
        // left := left ^ right
        for i in 0..left.len() {
            let left_val = self.variables[&left[i]].reduce().0[0];
            let right_val = self.variables[&right[i]].reduce().0[0];
            let out_var = self.add_input(BlsScalar::from(left_val ^ right_val));
            let one_var = self.add_input(BlsScalar::one());
            left[i] =
                self.plookup_gate(left[i], right[i], out_var, Some(one_var), BlsScalar::zero());
        }
    }

    /// This function mixes two input words, "x" and "y", into
    /// four words indexed by "a", "b", "c", and "d" selected
    /// from the working vector v. The 32-bit words in v have
    /// been decomposed into 4 bytes.
    fn mixing(
        &mut self,
        v: &mut [Variable; 64],
        a: usize,
        b: usize,
        c: usize,
        d: usize,
        x: &[Variable],
        y: &[Variable],
    ) {
        println!("begin {:?}", self.circuit_size());
        // line 1: 15 gates
        // v[a] := (v[a] + v[b] + x) mod 2**32
        self.add_three_mod_2_32(v, a, b, x);
        println!("line 1 {:?}", self.circuit_size());
        // line 2: 4 gates
        // v[d] := (v[d] ^ v[a]) >>> 16
        self.xor_by_indices(v, d, a);
        self.rotate(v, d, 16);
        println!("line 2 {:?}", self.circuit_size());
        // line 3: 11 gates
        // v[c] := (v[c] + v[d]) mod 2**32
        self.add_two_mod_2_32(v, c, d);
        println!("line 3 {:?}", self.circuit_size());
        // line 4: 8 gates
        // v[b] := (v[b] ^ v[c]) >>> 12
        self.xor_by_indices(v, b, c);
        self.rotate(v, b, 12);
        println!("line 4 {:?}", self.circuit_size());
        // line 5: 15 gates
        // v[a] := (v[a] + v[b] + y) mod 2**32
        self.add_three_mod_2_32(v, a, b, y);
        println!("line 5 {:?}", self.circuit_size());
        // line 6: 4 gates
        // v[d] := (v[d] ^ v[a]) >>> 8
        self.xor_by_indices(v, d, a);
        self.rotate(v, d, 8);
        println!("line 6 {:?}", self.circuit_size());
        // line 7: 11 gates
        // v[c] := (v[c] + v[d]) mod 2**32
        self.add_two_mod_2_32(v, c, d);
        println!("line 7 {:?}", self.circuit_size());
        // line 8: 8 gates
        // v[b] := (v[b] ^ v[c]) >>> 7
        self.xor_by_indices(v, b, c);
        self.rotate(v, b, 7);
        println!("line 8 {:?}", self.circuit_size());
    }

    /// Generate initial values from fractional part of the square root
    /// of the first 8 primes
    pub fn generate_iv(&mut self) -> [Variable; 32] {
        // Since our message is <= one block in length, we can shortcut a step by
        // doubling the IV vector
        vec![2.0, 3.0, 5.0, 7.0, 11.0, 13.0, 17.0, 19.0]
            .into_iter()
            .flat_map(|p| {
                u32::to_le_bytes(f64::floor(2_f64.powi(32) * f64::fract(f64::sqrt(p))) as u32)
                    .to_vec()
            })
            .map(|b| self.add_input(BlsScalar::from(b as u64)))
            .collect::<Vec<Variable>>()
            .try_into()
            .unwrap()
    }

    fn compression(&mut self, h: &mut [Variable; 32], m: [Variable; 64], t: u8) {
        // Copied from RFC
        // 4*SIGMA[round][index]
        const SIGMA: [[usize; 16]; 10] = [
            [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15],
            [14, 10, 4, 8, 9, 15, 13, 6, 1, 12, 0, 2, 11, 7, 5, 3],
            [11, 8, 12, 0, 5, 2, 15, 13, 10, 14, 3, 6, 7, 1, 9, 4],
            [7, 9, 3, 1, 13, 12, 11, 14, 2, 6, 5, 10, 4, 0, 15, 8],
            [9, 0, 5, 7, 2, 4, 10, 15, 14, 1, 11, 12, 6, 8, 3, 13],
            [2, 12, 6, 10, 0, 11, 8, 3, 4, 13, 7, 5, 15, 14, 1, 9],
            [12, 5, 1, 15, 14, 13, 4, 10, 0, 7, 6, 3, 9, 2, 8, 11],
            [13, 11, 7, 14, 12, 1, 3, 9, 5, 0, 15, 4, 8, 6, 2, 10],
            [6, 15, 14, 9, 11, 3, 0, 8, 12, 2, 13, 7, 1, 4, 10, 5],
            [10, 2, 8, 4, 7, 6, 1, 5, 15, 11, 9, 14, 3, 12, 13, 0],
        ];

        let iv = self.generate_iv();
        let mut v: [Variable; 64] = [*h, iv].concat().try_into().unwrap();

        // Our messages will never exceed one block, so the "final block"
        // flag is always true, and we always invert the bits of v[14].

        // Invert all bits in v[14] (represented here as v[56..60])
        // by XORing with [0xFF, 0xFF, 0xFF, 0xFF]
        let ff_var = self.add_input(BlsScalar::from(0xff));
        let ff_vec = [ff_var; 4];
        println!("flip all bits");
        self.xor(&mut v[56..60], &ff_vec);

        // XOR offset counter t=32 or t=64
        // t always fits in a single byte for our purposes
        // so only a single byte of the working vector is changed
        let t_var = self.add_input(BlsScalar::from(t as u64));
        println!("xor offset counter");
        self.xor(&mut v[48..49], &[t_var]);

        // Ten rounds of mixing for blake2s
        for i in 0..10 {
            self.mixing(
                &mut v,
                0,
                4,
                8,
                12,
                &m[4 * SIGMA[i][0]..(4 * SIGMA[i][0] + 4)],
                &m[4 * SIGMA[i][1]..(4 * SIGMA[i][1] + 4)],
            );
            self.mixing(
                &mut v,
                1,
                5,
                9,
                13,
                &m[4 * SIGMA[i][2]..(4 * SIGMA[i][2] + 4)],
                &m[4 * SIGMA[i][3]..(4 * SIGMA[i][3] + 4)],
            );
            self.mixing(
                &mut v,
                2,
                6,
                10,
                14,
                &m[4 * SIGMA[i][4]..(4 * SIGMA[i][4] + 4)],
                &m[4 * SIGMA[i][5]..(4 * SIGMA[i][5] + 4)],
            );
            self.mixing(
                &mut v,
                3,
                7,
                11,
                15,
                &m[4 * SIGMA[i][6]..(4 * SIGMA[i][6] + 4)],
                &m[4 * SIGMA[i][7]..(4 * SIGMA[i][7] + 4)],
            );

            self.mixing(
                &mut v,
                0,
                5,
                10,
                15,
                &m[4 * SIGMA[i][8]..(4 * SIGMA[i][8] + 4)],
                &m[4 * SIGMA[i][9]..(4 * SIGMA[i][9] + 4)],
            );
            self.mixing(
                &mut v,
                1,
                6,
                11,
                12,
                &m[4 * SIGMA[i][10]..(4 * SIGMA[i][10] + 4)],
                &m[4 * SIGMA[i][11]..(4 * SIGMA[i][11] + 4)],
            );
            self.mixing(
                &mut v,
                2,
                7,
                8,
                13,
                &m[4 * SIGMA[i][12]..(4 * SIGMA[i][12] + 4)],
                &m[4 * SIGMA[i][13]..(4 * SIGMA[i][13] + 4)],
            );
            self.mixing(
                &mut v,
                3,
                4,
                9,
                14,
                &m[4 * SIGMA[i][14]..(4 * SIGMA[i][14] + 4)],
                &m[4 * SIGMA[i][15]..(4 * SIGMA[i][15] + 4)],
            );
        }

        for i in 0..8 {
            self.xor_by_indices(&mut v, i, i + 8);
            println!("xor in state");
            self.xor_debug(&mut h[4 * i..4 * (i + 1)], &v[4 * i..4 * (i + 1)]);
        }
    }

    /// Blake2s with input and output both 256 bits
    pub fn blake2s_256(&mut self, message: [Variable; 32]) -> [Variable; 32] {
        // initialize h
        let mut h = self.generate_iv();

        // XOR h[0] with parameter 0x01010000 ^ (kk << 8) ^ nn
        // key length kk = 0 bytes, input length nn = 32 bytes
        // 0x01010000 ^ (0x0 << 8) ^ 0x20 = 0x01010020
        let parameter_vec = vec![
            self.add_input(BlsScalar::from(32)),
            self.zero_var,
            self.add_input(BlsScalar::one()),
            self.add_input(BlsScalar::one()),
        ];
        println!("parameter");
        self.xor(&mut h[0..4], &parameter_vec);

        // pad the message to 64 bytes
        let m: [Variable; 64] = [message, [self.zero_var; 32]].concat().try_into().unwrap();

        // h := F( h, d[dd - 1], ll, TRUE )
        // ll = 32 bytes
        self.compression(&mut h, m, 32);

        h
    }

    /// Blake2s with input 512 bits and output 256 bits
    pub fn blake2s_512(&mut self, message: [Variable; 64]) -> [Variable; 32] {
        // initialize h
        let mut h = self.generate_iv();

        // XOR h[0] with parameter 0x01010000 ^ (kk << 8) ^ nn
        // kk = 0 bytes, nn = 32 bytes
        // 0x01010000 ^ (0x0 << 8) ^ 0x20 = 0x01010020
        let parameter_vec = vec![
            self.add_input(BlsScalar::from(32)),
            self.zero_var,
            self.add_input(BlsScalar::one()),
            self.add_input(BlsScalar::one()),
        ];
        println!("parameter");
        self.xor(&mut h[0..4], &parameter_vec);

        // h := F( h, d[dd - 1], ll, TRUE )
        // ll = 64 bytes
        self.compression(&mut h, message, 64);

        h
    }

    fn scalar_to_byte_vars(&mut self, scalar: BlsScalar) -> [Variable; 32] {
        scalar
            .reduce()
            .0
            .iter()
            .flat_map(|u| u.to_le_bytes().to_vec())
            .map(|b| self.add_input(BlsScalar::from(b as u64)))
            .collect::<Vec<Variable>>()
            .try_into()
            .unwrap()
    }

    /// Shows knowledge of a blake2s preimage of a hash
    fn blake2s_preimage(&mut self, preimage: BlsScalar) -> Variable {
        let message = self.scalar_to_byte_vars(preimage);
        let results = self.blake2s_256(message);
        self.compose_scalar_from_le_bytes(&results)
    }

    fn vars_to_bytes(&mut self, v: Vec<Variable>) -> Vec<u8> {
        v.iter()
            .map(|b| (self.variables[&b].reduce().0[0] % 256) as u8)
            .collect::<Vec<u8>>()
    }
}

#[cfg(test)]
mod tests {
    use crate::constraint_system::Variable;
    use crate::prelude::StandardComposer;
    use dusk_bls12_381::BlsScalar;

    #[test]
    fn test_mixer() {
        use std::convert::TryInto;
        let mut composer = StandardComposer::new();
        let message = [composer.zero_var; 64];
        let initial_v: [u32; 16] = [
            0x6b08e647, 0xbb67ae85, 0x3c6ef372, 0xa54ff53a, 0x510e527f, 0x9b05688c, 0x1f83d9ab,
            0x5be0cd19, 0x6a09e667, 0xbb67ae85, 0x3c6ef372, 0xa54ff53a, 0x510e527f, 0x9b05688c,
            0xe07c2654, 0x5be0cd19,
        ];
        let mut v = [composer.zero_var; 64];
        for i in 0..16 {
            let v_bytes = initial_v[i].to_le_bytes();
            for j in 0..4 {
                v[4 * i + j] = composer.add_input(BlsScalar::from(v_bytes[j] as u64));
            }
        }

        let comparison = [
            0xdc0f959e, 0xbb67ae85, 0x3c6ef372, 0xa54ff53a, 0x408705aa, 0x9b05688c, 0x1f83d9ab,
            0x5be0cd19, 0x5c7a89f8, 0xbb67ae85, 0x3c6ef372, 0xa54ff53a, 0x87b6b678, 0x9b05688c,
            0xe07c2654, 0x5be0cd19,
        ];

        let s0: usize = 0;
        let s1: usize = 14;
        composer.mixing(
            &mut v,
            0,
            4,
            8,
            12,
            &message[s0 * 4..(s0 * 4 + 4)],
            &message[s1 * 4..(s1 * 4 + 4)],
        );

        let mut v_bytes = [0u8; 64];
        for i in 0..64 {
            v_bytes[i] = composer.variables[&v[i]].reduce().0[0] as u8;
        }

        let mut v_u32 = [0u32; 16];
        for i in 0..16 {
            v_u32[i] = u32::from_le_bytes(
                (&v_bytes[4 * i..(4 * i + 4)])
                    .try_into()
                    .expect("Wrong length"),
            );
        }
        assert_eq!(comparison, v_u32);
    }

    #[test]
    #[ignore]
    fn test_blake2s_preimage_proof() {
        use super::super::helper::*;
        use std::convert::TryInto;

        let res = gadget_tester(
            |composer| {
                // prover's secret preimage
                let preimage = BlsScalar::zero();

                // blake2s hash of 256-bits of zeros
                let hash_bytes: [u8; 64] = [
                    0x32, 0x0b, 0x5e, 0xa9, 0x9e, 0x65, 0x3b, 0xc2, 0xb5, 0x93, 0xdb, 0x41, 0x30,
                    0xd1, 0x0a, 0x4e, 0xfd, 0x3a, 0x0b, 0x4c, 0xc2, 0xe1, 0xa6, 0x67, 0x2b, 0x67,
                    0x8d, 0x71, 0xdf, 0xbd, 0x33, 0xad, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
                    0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
                    0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
                ];

                composer.generate_blake_table();
                let hash = composer.add_input(BlsScalar::from_bytes_wide(&hash_bytes));
                composer.blake2s_preimage(preimage);
            },
            131072,
        );

        assert!(res.is_ok());
    }

    #[test]
    fn test_blake2s_hash() {
        use std::convert::TryInto;
        let mut composer = StandardComposer::new();

        // 256 bits of zeros
        let message_bytes: [u8; 32] = [
            0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
            0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
            0x00, 0x00, 0x00, 0x00,
        ];

        // blake2s hash of 256-bits of zeros
        let hash_bytes: [u8; 32] = [
            0x32, 0x0b, 0x5e, 0xa9, 0x9e, 0x65, 0x3b, 0xc2, 0xb5, 0x93, 0xdb, 0x41, 0x30, 0xd1,
            0x0a, 0x4e, 0xfd, 0x3a, 0x0b, 0x4c, 0xc2, 0xe1, 0xa6, 0x67, 0x2b, 0x67, 0x8d, 0x71,
            0xdf, 0xbd, 0x33, 0xad,
        ];

        let mut message_vars = [composer.zero_var; 32];
        for i in 0..32 {
            message_vars[i] = composer.add_input(BlsScalar::from(message_bytes[i] as u64));
        }

        let hash_vars = composer.blake2s_256(message_vars);

        for i in 0..32 {
            assert_eq!(composer.vars_to_bytes(hash_vars.to_vec())[i], hash_bytes[i]);
        }
        println!("gates: {:?}", composer.circuit_size());
    }
}
