// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
//
// Copyright (c) DUSK NETWORK. All rights reserved.

#![allow(clippy::too_many_arguments)]

use crate::constraint_system::StandardComposer;
use crate::constraint_system::Variable;
use dusk_bls12_381::BlsScalar;
use std::io;
use std::io::Write;
use std::convert::TryInto;

impl StandardComposer {
    /// Generates an XOR truth table out of 4-bit nibbles
    pub fn generate_xor_table_small(&mut self) {
        for i in 0..2u8.pow(4) {
            for j in 0..2u8.pow(4) {
                self.lookup_table.0.push([
                    BlsScalar::from(i as u64),
                    BlsScalar::from(j as u64),
                    BlsScalar::from((i^j) as u64),
                    BlsScalar::zero(),
                ]);
            }
        }
    }

    /// Generates an XOR truth table out of bytes
    pub fn generate_xor_table_big(&mut self) {
        for i in 0..2u16.pow(8) {
            for j in 0..2u16.pow(8) {
                self.lookup_table.0.push([
                    BlsScalar::from(i as u64),
                    BlsScalar::from(j as u64),
                    BlsScalar::from((i^j) as u64),
                    BlsScalar::zero(),
                ]);
            }
        }
    }

    /// Creates a single 256-bit scalar variable from 64 nibble variables 
    pub fn compose_scalar_from_le_nibbles(&mut self, nibbles: &[Variable]) -> Variable {
        // Checks if bytes.len() is a power of two
        assert_eq!(nibbles.len(), 64);

        // compose 32-bit words from 8 range-checked nibbles
        let mut words = [self.zero_var; 8];
        for i in 0..8 {
            words[i] = self.compose_word_from_le_nibbles(&nibbles[8*i..8*(i+1)]);
        }

        // compose 8-byte octs
        let mut octs = [self.zero_var; 4];
        for i in 0..4 {
            octs[i] = self.add(
                (BlsScalar::from(1 << 32), words[2*i+1]),
                (BlsScalar::one(), words[2*i]),
                BlsScalar::zero(),
                BlsScalar::zero(),
            );
        }

        // compose 16-byte hexes
        let mut hexes = [self.zero_var; 2];
        for i in 0..2 {
            hexes[i] = self.add(
                (BlsScalar::from_raw([0,1,0,0]), octs[2*i+1]),
                (BlsScalar::one(), octs[2*i]),
                BlsScalar::zero(),
                BlsScalar::zero(),
            );
        }

        // compose 32-byte/256-bit scalar
        self.add(
            (BlsScalar::from_raw([0,0,1,0]), hexes[1]),
            (BlsScalar::one(), hexes[0]),
            BlsScalar::zero(),
            BlsScalar::zero(),
        )
    }

    /// Creates a variable y = x0*2^(8*3) + x1*2^(8*2) + x2*2^(8*1) + x3
    /// such that if x0..x3 are nibbles, then y is the 32-bit concatenation
    /// x0|x1|x2|x3. 
    pub fn compose_word_from_le_nibbles(&mut self, nibbles: &[Variable]) -> Variable {
        assert_eq!(nibbles.len(), 8);

        // Prove 4 pieces of word are actually nibbles by looking them up in the nibble-sized lookup table
        // If (A, B, A^B) is in the lookup table, then A and B are both less than 2^8
        // Uses 2 lookup gates to replace 8 gates used for a 8-bit range check

        let nibble_7_xor_nibble_6_var = self.add_input(
            BlsScalar::from(
                self.variables[&nibbles[3]].reduce().0[0] ^ self.variables[&nibbles[2]].reduce().0[0]
            )
        );

        let nibble_5_xor_nibble_4_var = self.add_input(
            BlsScalar::from(
                self.variables[&nibbles[1]].reduce().0[0] ^ self.variables[&nibbles[0]].reduce().0[0]
            )
        );

        let nibble_3_xor_nibble_2_var = self.add_input(
            BlsScalar::from(
                self.variables[&nibbles[3]].reduce().0[0] ^ self.variables[&nibbles[2]].reduce().0[0]
            )
        );

        let nibble_1_xor_nibble_0_var = self.add_input(
            BlsScalar::from(
                self.variables[&nibbles[1]].reduce().0[0] ^ self.variables[&nibbles[0]].reduce().0[0]
            )
        );

        self.plookup_gate(nibbles[7], nibbles[6], nibble_7_xor_nibble_6_var, None, BlsScalar::zero());
        self.plookup_gate(nibbles[5], nibbles[4], nibble_5_xor_nibble_4_var, None, BlsScalar::zero()); 
        self.plookup_gate(nibbles[3], nibbles[2], nibble_3_xor_nibble_2_var, None, BlsScalar::zero());
        self.plookup_gate(nibbles[1], nibbles[0], nibble_1_xor_nibble_0_var, None, BlsScalar::zero()); 

        let pair_3 = self.add(
            (BlsScalar::from(1 << 4), nibbles[7]),
            (BlsScalar::one(), nibbles[6]),
            BlsScalar::zero(),
            BlsScalar::zero(),
        );

        let pair_2 = self.add(
            (BlsScalar::from(1 << 4), nibbles[5]),
            (BlsScalar::one(), nibbles[4]),
            BlsScalar::zero(),
            BlsScalar::zero(),
        );

        let pair_1 = self.add(
            (BlsScalar::from(1 << 4), nibbles[3]),
            (BlsScalar::one(), nibbles[2]),
            BlsScalar::zero(),
            BlsScalar::zero(),
        );

        let pair_0 = self.add(
            (BlsScalar::from(1 << 4), nibbles[1]),
            (BlsScalar::one(), nibbles[0]),
            BlsScalar::zero(),
            BlsScalar::zero(),
        );

        let quad_hi = self.add(
            (BlsScalar::from(1 << 8), pair_3),
            (BlsScalar::one(), pair_2),
            BlsScalar::zero(),
            BlsScalar::zero(),
        );

        let quad_lo = self.add(
            (BlsScalar::from(1 << 8), pair_1),
            (BlsScalar::one(), pair_0),
            BlsScalar::zero(),
            BlsScalar::zero(),
        );

        self.add(
            (BlsScalar::from(1 << 16), quad_hi),
            (BlsScalar::one(), quad_lo),
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
        // u32 words, and thus should be less than 4 (2 bits)
        self.range_gate(quotient_var, 2);

        // Show mod has been done correctly with a single add gate
        // which returns the variable holding the remainder
        self.add(
            (BlsScalar::one(), d),
            (-BlsScalar::from(2_u64.pow(32)), quotient_var),
            BlsScalar::zero(),
            BlsScalar::zero(),
        )
    }

    fn word_to_le_nibbles(word_input: u32)-> [u8; 8] {
        let mut word = word_input;
        let mut word_nibbles = [0u8; 8];
        for i in 0..8 {
            word_nibbles[i] = (word % 16) as u8;
            word >>= 4;
        }
        word_nibbles
    }

    /// Decomposes a variable d into 8 nibbles d0..d7 so that
    /// d = d0|d1|..|d7 and adds the required gates showing decomposition is correct
    pub fn decompose_word_into_le_nibbles(&mut self, word: Variable) -> [Variable; 8] {
        let word_value = self.variables[&word].reduce().0[0];
        let word_nibbles = StandardComposer::word_to_le_nibbles(word_value as u32);

        let mut word_vars = [self.zero_var; 8];
        // create variables for each nibbles
        for i in 0..8 {
            word_vars[i] = self.add_input(BlsScalar::from(word_nibbles[i] as u64));
        }
       
        // show bytes compose to input word
        self.compose_word_from_le_nibbles(&word_vars);

        word_vars
    }
    
    /// Adds three variables by adding nibble-by-nibble, composing the nibbles, and modding
    /// by 2**32
    pub fn add_three_mod_2_32(&mut self, v: &mut [Variable; 128], a: usize, b: usize, x: &[Variable]) {
        // v[a] := (v[a] + v[b] + x) mod 2**w
        for i in 0..8 {
            // v[a] += v[b]
            v[8*a+i] = self.add(
                (BlsScalar::one(), v[8*a+i]),
                (BlsScalar::one(), v[8*b+i]),
                BlsScalar::zero(),
                BlsScalar::zero(),
            );

            // v[a] += x
            v[8*a+i] = self.add(
                (BlsScalar::one(), v[8*a+i]),
                (BlsScalar::one(), x[i]),
                BlsScalar::zero(),
                BlsScalar::zero(),
            );
        }

        // compose the bytes back into a single integer      
        // so we can compute the mod operation
        let sum = self.compose_word_from_le_nibbles(&v[8*a..(8*a+8)]);

        // compute the remainder mod 2^32
        let remainder = self.mod_u32(sum);

        // decompose remainder back into bytes and add
        // gates showing decomposition is correct
        let decomposed_nibbles = self.decompose_word_into_le_nibbles(remainder);
        v[8*a] = decomposed_nibbles[0];
        v[8*a+1] = decomposed_nibbles[1];
        v[8*a+2] = decomposed_nibbles[2];
        v[8*a+3] = decomposed_nibbles[3];
        v[8*a+8] = decomposed_nibbles[4];
        v[8*a+5] = decomposed_nibbles[5];
        v[8*a+6] = decomposed_nibbles[6];
        v[8*a+7] = decomposed_nibbles[7];
    }

    /// Adds two variables by adding byte-by-byte, composing the bytes, and modding
    /// by 2**32
    pub fn add_two_mod_2_32(&mut self, v: &mut [Variable; 128], c: usize, d: usize) {
        // v[c] := (v[c] + v[d])     mod 2**w
        for i in 0..8 {
            // v[c] += v[d]
            v[8*c+i] = self.add(
                (BlsScalar::one(), v[8*c+i]),
                (BlsScalar::one(), v[8*d+i]),
                BlsScalar::zero(),
                BlsScalar::zero(),
            );
        }

        // compose the bytes back into a single integer      
        // so we can compute the mod operation
        let sum = self.compose_word_from_le_nibbles(&v[8*c..(8*c+8)]);

        // compute the remainder mod 2^32
        let remainder = self.mod_u32(sum);

        // decompose remainder back into bytes and add
        // gates showing decomposition is correct
        let decomposed_nibbles = self.decompose_word_into_le_nibbles(remainder);

        v[8*c] = decomposed_nibbles[0];
        v[8*c+1] = decomposed_nibbles[1];
        v[8*c+2] = decomposed_nibbles[2];
        v[8*c+3] = decomposed_nibbles[3];
        v[8*c+8] = decomposed_nibbles[4];
        v[8*c+5] = decomposed_nibbles[5];
        v[8*c+6] = decomposed_nibbles[6];
        v[8*c+7] = decomposed_nibbles[7];
    }

    /// Rotates to the right by 16 bits by shuffling variables in the working vector
    fn rotate_16(&mut self, v: &mut [Variable; 128], n: usize) {
        // rotate bytes to the right 2 so that v[n+2] := v[n] etc. 
        let mut initial = [self.zero_var; 8];
        initial.clone_from_slice(&v[8*n..(8*n+8)]);
        for i in 0..8 {
            v[8*n+(i+8)%8] = initial[i]; 
        }
    }

    /// Rotates to the right by 8 bits by shuffling variables in the working vector
    fn rotate_8(&mut self, v: &mut [Variable; 128], n: usize) {
        // rotate nibbles to the right 2 so that v[n-2] := v[n] etc.
        let mut initial = [self.zero_var; 8];
        initial.clone_from_slice(&v[8*n..(8*n+8)]);
        for i in 0..8 {
            v[8*n+(i+6)%8] = initial[i]; 
        }
    }

    /// Rotates to the right by 12 bits by shuffling variables in the working vector
    fn rotate_12(&mut self, v: &mut [Variable; 128], n: usize) {
        // rotate nibbles to the right 1 so that v[n-3] := v[n] etc.
        let mut initial = [self.zero_var; 8];
        initial.clone_from_slice(&v[8*n..(8*n+8)]);
        for i in 0..8 {
            v[8*n+(i+5)%8] = initial[i]; 
        }
    }

    /// Rotates to the right by 7 bits by spltting each nibble into pieces and recomposing
    fn rotate_7(&mut self, v: &mut [Variable; 128], n: usize) {
        
        // first split each nibble into 3 high bits and 1 low bit
        let mut split_nibbles = [self.zero_var; 16];
        for i in (0..8).rev() {
            let current_nibble = self.variables[&v[8*n+i]].reduce().0[0];
            // 1 high bit
            let hi = current_nibble >> 3;
            // 3 low bits
            let lo = current_nibble % (1 << 3);

            // high bits are on even indices, low bits are on odd indices
            split_nibbles[2*i] = self.add_input(BlsScalar::from(hi));
            split_nibbles[2*i+1] = self.add_input(BlsScalar::from(lo));

            // show that the hi bit is actually a bit
            self.boolean_gate(split_nibbles[2*i]);

            // to show that the lo bits l are less than 2^3, we need to show that 2*l < 2^4 with a plookup XOR gate
            // AND we need to show that l < 2^4 with a second plookup XOR gate (otherwise l could be between p/2 and p/2 + 2^4
            // and still pass the check)

            // we need a variable for 2*l to include in plookup
            let lo_times_2 = self.add(
                // 2*lo bits
                (BlsScalar::from(2), split_nibbles[2*i+1]),
                // right addend is zero
                (BlsScalar::one(), self.zero_var),
                BlsScalar::zero(),
                BlsScalar::zero(),
            );

            // show that l < 2^4
            self.plookup_gate(split_nibbles[2*i+1], split_nibbles[2*i+1], self.zero_var, None, BlsScalar::zero());

            // show that 2*l < 2^4
            self.plookup_gate(lo_times_2, lo_times_2, self.zero_var, None, BlsScalar::zero());

            // finally, show the high bit is actually a bit
            self.boolean_gate(split_nibbles[2*i]);
        }

        // Now recompose the 8 pairs of high and low bits into 8 nibbles, shifting 
        // shifting 3 space to the right, so that the new first nibble is lo|hi, 
        // using the low bits at index 5 and the high bit at index 2.
        // We do not need to range check the resulting byte since we already
        // checked the two pieces of each nibble
        for i in 0..8 {
            v[8*n+i] =  self.add(
                // 3 low bits become new high bits
                (BlsScalar::from(2), split_nibbles[(2*i+5)%16]),
                // 1 high bit becomes new low bit
                (BlsScalar::one(), split_nibbles[(2*i+2)%16]),
                BlsScalar::zero(),
                BlsScalar::zero(),
            );
        }
    }

    /// Performs a bit rotation right by 16, 12, 8, or 7 bits on the nth word
    pub fn rotate(&mut self, v: &mut [Variable; 128], n: usize, r: usize) {
        match r {
            16 => StandardComposer::rotate_16(self, v, n),
            12 => StandardComposer::rotate_12(self, v, n),
            8 => StandardComposer::rotate_8(self, v, n),
            7 => StandardComposer::rotate_7(self, v, n),
            _ => panic!("Not a valid rotation constant for blake2s"),
        };
    }

    /// Performs a nibble-by-nibble XOR of two words given their indices in the working vector
    pub fn xor_by_indices(&mut self, v: &mut [Variable; 128], d: usize, a: usize) {
        // v[d] := (v[d] ^ v[a])
        let mut right = [self.zero_var; 8];
        right.clone_from_slice(&v[8*a..(8*a+8)]);
        self.xor(&mut v[8*d..(8*d+8)], &right);
    }

    /// Performs an XOR in place, mutating the left word
    pub fn xor(&mut self, left: &mut [Variable], right: &[Variable]) {

        // left := left ^ right
        for i in 0..left.len() {
            let left_val = self.variables[&left[i]].reduce().0[0];
            let right_val = self.variables[&right[i]].reduce().0[0];
            let out_var = self.add_input(BlsScalar::from(left_val ^ right_val));
            left[i] = self.plookup_gate(left[i], right[i], out_var, None, BlsScalar::zero());
        }
    }

        /// Performs an XOR in place, mutating the left word
        pub fn xor_debug(&mut self, left: &mut [Variable], right: &[Variable]) {
            // left := left ^ right
            for i in 0..left.len() {
                let left_val = self.variables[&left[i]].reduce().0[0];
                let right_val = self.variables[&right[i]].reduce().0[0];
                let out_var = self.add_input(BlsScalar::from(left_val ^ right_val));
                left[i] = self.plookup_gate(left[i], right[i], out_var, None, BlsScalar::zero());
            }
        }
    

    /// This function mixes two input words, "x" and "y", into
    /// four words indexed by "a", "b", "c", and "d" selected 
    /// from the working vector v. The 32-bit words in v have
    /// been decomposed into 4 bytes.
    fn mixing (&mut self, v: &mut [Variable; 128], a: usize, b: usize, c: usize, d: usize, x: &[Variable], y: &[Variable]) {

        // line 1: 15 gates
        // v[a] := (v[a] + v[b] + x) mod 2**32
        self.add_three_mod_2_32(v, a, b, x);

        // line 2: 4 gates
        // v[d] := (v[d] ^ v[a]) >>> 16
        self.xor_by_indices(v, d, a);
        self.rotate(v, d, 16);

        // line 3: 11 gates
        // v[c] := (v[c] + v[d]) mod 2**32
        self.add_two_mod_2_32(v, c, d);

        // line 4: 8 gates
        // v[b] := (v[b] ^ v[c]) >>> 12 
        self.xor_by_indices(v, b, c);
        self.rotate(v, b, 12);

        // line 5: 15 gates
        // v[a] := (v[a] + v[b] + y) mod 2**32
        self.add_three_mod_2_32(v, a, b, y);

        // line 6: 4 gates
        // v[d] := (v[d] ^ v[a]) >>> 8
        self.xor_by_indices(v, d, a);
        self.rotate(v, d, 8);

        // line 7: 11 gates
        // v[c] := (v[c] + v[d]) mod 2**32
        self.add_two_mod_2_32(v, c, d);

        // line 8: 8 gates
        // v[b] := (v[b] ^ v[c]) >>> 7 
        self.xor_by_indices(v, b, c);
        self.rotate(v, b, 7);
    }

    /// Generate initial values from fractional part of the square root
    /// of the first 8 primes
    pub fn generate_iv(&mut self) -> [Variable; 64] {
        // Since our message is <= one block in length, we can shortcut a step by
        // doubling the IV vector
        vec![2.0, 3.0, 5.0, 7.0, 11.0, 13.0, 17.0, 19.0]
            .into_iter()
            .flat_map(|p|
                StandardComposer::word_to_le_nibbles(
                    f64::floor(2_f64.powi(32) * f64::fract(f64::sqrt(p))) as u32
                ).to_vec()
            )
            .map(|b|
                self.add_input(BlsScalar::from(b as u64))
            )
            .collect::<Vec<Variable>>()
            .try_into()
            .unwrap()
    }

    fn compression(&mut self, h: &mut [Variable; 64], m: [Variable; 128], t: u8) {

        // Copied from RFC
        // 8*SIGMA[round][index]
        const SIGMA: [[usize; 16]; 10] = [         
            [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15],
            [14,10,4,8,9,15,13,6,1,12,0,2,11,7,5,3],
            [11,8,12,0,5,2,15,13,10,14,3,6,7,1,9,4],
            [7,9,3,1,13,12,11,14,2,6,5,10,4,0,15,8],
            [9,0,5,7,2,4,10,15,14,1,11,12,6,8,3,13],
            [2,12,6,10,0,11,8,3,4,13,7,5,15,14,1,9],
            [12,5,1,15,14,13,4,10,0,7,6,3,9,2,8,11],
            [13,11,7,14,12,1,3,9,5,0,15,4,8,6,2,10],
            [6,15,14,9,11,3,0,8,12,2,13,7,1,4,10,5],
            [10,2,8,4,7,6,1,5,15,11,9,14,3,12,13,0],
        ];

        let iv = self.generate_iv();
        let mut v: [Variable; 128] = [*h, iv].concat().try_into().unwrap();

        // Our messages will never exceed one block, so the "final block"
        // flag is always true, and we always invert the bits of v[14].

        // Invert all bits in v[14] (represented here as v[112..120])
        // by XORing with [0xF, 0xF, 0xF, 0xF, 0xF, 0xF, 0xF, 0xF]
        let ff_var = self.add_input(BlsScalar::from(0xf));
        let ff_vec = [ff_var; 8];
        println!("flip all bits");
        self.xor(&mut v[112..120], &ff_vec);

        // XOR offset counter t=32 or t=64 is XORed into v[12], represented here as v[96]

        // in general, t is 16 nibbles long, but for our purposes only a single bit of
        // t is ever set, and we only need the nibble containing that bit, which is the
        // second nibble of t. Therefore only v[97] is XORed with 4 bits of t

        let t_hi_var = self.add_input(BlsScalar::from((t >> 4) as u64));
        println!("xor offset counter");
        self.xor(&mut v[97..98], &[t_hi_var]);

        // Ten rounds of mixing for blake2s
        for i in 0..10 {
            self.mixing(&mut v, 0, 4,  8, 12, &m[8*SIGMA[i][ 0]..(8*SIGMA[i][ 0]+8)], &m[8*SIGMA[i][ 1]..(8*SIGMA[i][ 1]+8)]);
            self.mixing(&mut v, 1, 5,  9, 13, &m[8*SIGMA[i][ 2]..(8*SIGMA[i][ 2]+8)], &m[8*SIGMA[i][ 3]..(8*SIGMA[i][ 3]+8)]);
            self.mixing(&mut v, 2, 6, 10, 14, &m[8*SIGMA[i][ 4]..(8*SIGMA[i][ 4]+8)], &m[8*SIGMA[i][ 5]..(8*SIGMA[i][ 5]+8)]);
            self.mixing(&mut v, 3, 7, 11, 15, &m[8*SIGMA[i][ 6]..(8*SIGMA[i][ 6]+8)], &m[8*SIGMA[i][ 7]..(8*SIGMA[i][ 7]+8)]);

            self.mixing(&mut v, 0, 5, 10, 15, &m[8*SIGMA[i][ 8]..(8*SIGMA[i][ 8]+8)], &m[8*SIGMA[i][ 9]..(8*SIGMA[i][ 9]+8)]);
            self.mixing(&mut v, 1, 6, 11, 12, &m[8*SIGMA[i][10]..(8*SIGMA[i][10]+8)], &m[8*SIGMA[i][11]..(8*SIGMA[i][11]+8)]);
            self.mixing(&mut v, 2, 7,  8, 13, &m[8*SIGMA[i][12]..(8*SIGMA[i][12]+8)], &m[8*SIGMA[i][13]..(8*SIGMA[i][13]+8)]);
            self.mixing(&mut v, 3, 4,  9, 14, &m[8*SIGMA[i][14]..(8*SIGMA[i][14]+8)], &m[8*SIGMA[i][15]..(8*SIGMA[i][15]+8)]);
        }

        for i in 0..8 {
            self.xor_by_indices(&mut v, i, i+8);
            println!("xor in state");
            self.xor_debug(&mut h[8*i..8*(i+1)], &v[8*i..8*(i+1)]);
        }
    }

    /// Blake2s with input and output both 256 bits
    pub fn blake2s_256(&mut self, message: [Variable; 64]) -> [Variable; 64] {
        // initialize h
        let mut h = self.generate_iv();

        // XOR h[0] with parameter 0x01010000 ^ (kk << 8) ^ nn
        // key length kk = 0 bytes, input length nn = 32 bytes
        // 0x01010000 ^ (0x0 << 8) ^ 0x20 = 0x01010020 = [0x0, 0x2, 0x0, 0x0, 0x1, 0x0, 0x1, 0x0] in little endian
        let parameter_vec = vec![
            self.zero_var,
            self.add_input(BlsScalar::from(2)),
            self.zero_var,
            self.zero_var,
            self.add_input(BlsScalar::one()),
            self.zero_var,
            self.add_input(BlsScalar::one()),
            self.zero_var,
            ];
        println!("parameter");
        self.xor(&mut h[0..8], &parameter_vec);

        // pad the message to 64 bytes
        let m: [Variable; 128] = [message, [self.zero_var; 64]].concat().try_into().unwrap();

        // h := F( h, d[dd - 1], ll, TRUE )
        // ll = 32 bytes
        self.compression(&mut h, m, 32);

        h
    }

    /// Blake2s with input 512 bits and output 256 bits
    pub fn blake2s_512(&mut self, message: [Variable; 128]) -> [Variable; 64] {
        // initialize h
        let mut h = self.generate_iv();

        // XOR h[0] with parameter 0x01010000 ^ (kk << 8) ^ nn
        // key length kk = 0 bytes, input length nn = 32 bytes
        // 0x01010000 ^ (0x0 << 8) ^ 0x20 = 0x01010020 = [0x20, 0x00, 0x01, 0x01] in little endian
        let parameter_vec = vec![self.add_input(BlsScalar::from(32)), self.zero_var, self.add_input(BlsScalar::one()), self.add_input(BlsScalar::one())];
        println!("parameter");
        self.xor(&mut h[0..8], &parameter_vec);
    
        // h := F( h, d[dd - 1], ll, TRUE )
        // ll = 64 bytes
        self.compression(&mut h, message, 64);

        h
    }

    fn scalar_to_nibble_vars(&mut self, scalar: BlsScalar) -> [Variable; 64] {
        scalar.reduce().0.iter()
            .flat_map(|u| StandardComposer::word_to_le_nibbles(*u as u32).to_vec())
            .map(|b| self.add_input(BlsScalar::from(b as u64)))
            .collect::<Vec<Variable>>().try_into().unwrap()
    }

    /// Shows knowledge of a blake2s preimage of a hash
    fn blake2s_preimage(&mut self, preimage: BlsScalar) -> Variable {
        let message = self.scalar_to_nibble_vars(preimage);
        let results = self.blake2s_256(message);
        self.compose_scalar_from_le_nibbles(&results)
    }

    fn vars_to_nibbles(&mut self, v: Vec<Variable>) -> Vec<u8> {
        v.iter().map(|b| (self.variables[&b].reduce().0[0] % 16) as u8).collect::<Vec<u8>>()
    }
}

#[cfg(test)]
mod tests {
    use dusk_bls12_381::BlsScalar;
    use crate::prelude::StandardComposer;
    use crate::constraint_system::Variable;

    #[test]
        fn test_mixer() {
            use std::convert::TryInto;
            let mut composer = StandardComposer::new();
            let message = [composer.zero_var; 64];
            let initial_v: [u32; 16] = [
                0x6b08e647,
                0xbb67ae85,
                0x3c6ef372,
                0xa54ff53a,
                0x510e527f,
                0x9b05688c,
                0x1f83d9ab,
                0x5be0cd19,
                0x6a09e667,
                0xbb67ae85,
                0x3c6ef372,
                0xa54ff53a,
                0x510e527f,
                0x9b05688c,
                0xe07c2654,
                0x5be0cd19
            ];
            let mut v = [composer.zero_var; 128];
            for i in 0..16 {
                let v_bytes = initial_v[i].to_le_bytes();
                for j in 0..4 {
                    v[8*i+j] = composer.add_input(BlsScalar::from(v_bytes[j] as u64));
                }
            }

            let comparison = [
                0xdc0f959e,
                0xbb67ae85,
                0x3c6ef372,
                0xa54ff53a,
                0x408705aa,
                0x9b05688c,
                0x1f83d9ab,
                0x5be0cd19,
                0x5c7a89f8,
                0xbb67ae85,
                0x3c6ef372,
                0xa54ff53a,
                0x87b6b678,
                0x9b05688c,
                0xe07c2654,
                0x5be0cd19
            ];

            let s0: usize = 0;
            let s1: usize = 14;
            composer.mixing(&mut v, 0, 4, 8, 12, &message[s0*4..(s0*4+8)], &message[s1*4..(s1*4 +8)]);

            let mut v_bytes = [0u8; 64];
            for i in 0..64 {
                v_bytes[i] = composer.variables[&v[i]].reduce().0[0] as u8;
            }

            let mut v_u32 = [0u32; 16];
            for i in 0..16 {
                v_u32[i] = u32::from_le_bytes((&v_bytes[8*i..(8*i+8)]).try_into().expect("Wrong length"));
            }
            assert_eq!(comparison, v_u32);
        }

    #[test]
    fn test_blake2s_preimage_proof() {
        use std::convert::TryInto;
        use super::super::helper::*;

        let res = gadget_tester(
            |composer| {
                // prover's secret preimage
                let preimage = BlsScalar::zero();

                // blake2s hash of 256-bits of zeros
                let hash_bytes: [u8; 64] = [
                    0x32, 0x0b, 0x5e, 0xa9,
                    0x9e, 0x65, 0x3b, 0xc2,
                    0xb5, 0x93, 0xdb, 0x41,
                    0x30, 0xd1, 0x0a, 0x4e,
                    0xfd, 0x3a, 0x0b, 0x4c,
                    0xc2, 0xe1, 0xa6, 0x67,
                    0x2b, 0x67, 0x8d, 0x71,
                    0xdf, 0xbd, 0x33, 0xad,
                    0x00, 0x00, 0x00, 0x00,
                    0x00, 0x00, 0x00, 0x00,
                    0x00, 0x00, 0x00, 0x00,
                    0x00, 0x00, 0x00, 0x00,
                    0x00, 0x00, 0x00, 0x00,
                    0x00, 0x00, 0x00, 0x00,
                    0x00, 0x00, 0x00, 0x00,
                    0x00, 0x00, 0x00, 0x00,
                ];

                composer.generate_xor_table_big();
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
        let message_nibbles: [u8; 64] = [
            0x00, 0x00, 0x00, 0x00,
            0x00, 0x00, 0x00, 0x00,
            0x00, 0x00, 0x00, 0x00,
            0x00, 0x00, 0x00, 0x00,
            0x00, 0x00, 0x00, 0x00,
            0x00, 0x00, 0x00, 0x00,
            0x00, 0x00, 0x00, 0x00,
            0x00, 0x00, 0x00, 0x00,
            0x00, 0x00, 0x00, 0x00,
            0x00, 0x00, 0x00, 0x00,
            0x00, 0x00, 0x00, 0x00,
            0x00, 0x00, 0x00, 0x00,
            0x00, 0x00, 0x00, 0x00,
            0x00, 0x00, 0x00, 0x00,
            0x00, 0x00, 0x00, 0x00,
            0x00, 0x00, 0x00, 0x00,
        ];

        // blake2s hash of 256-bits of zeros
        let hash_nibbles: [u8; 64] = [
            0x3, 0x2, 0x0, 0xb, 0x5, 0xe, 0xa, 0x9, 
            0x9, 0xe, 0x6, 0x5, 0x3, 0xb, 0xc, 0x2, 
            0xb, 0x5, 0x9, 0x3, 0xd, 0xb, 0x4, 0x1, 
            0x3, 0x0, 0xd, 0x1, 0x0, 0xa, 0x4, 0xe, 
            0xf, 0xd, 0x3, 0xa, 0x0, 0xb, 0x4, 0xc, 
            0xc, 0x2, 0xe, 0x1, 0xa, 0x6, 0x6, 0x7, 
            0x2, 0xb, 0x6, 0x7, 0x8, 0xd, 0x7, 0x1, 
            0xd, 0xf, 0xb, 0xd, 0x3, 0x3, 0xa, 0xd, 
        ];
            
        let mut message_vars = [composer.zero_var; 64];
        for i in 0..64 {
            message_vars[i] = composer.add_input(BlsScalar::from(message_nibbles[i] as u64));
        }

        let hash_vars = composer.blake2s_256(message_vars);
        println!("gates: {:?}", composer.circuit_size());
        for i in 0..64 {
            assert_eq!(composer.vars_to_nibbles(hash_vars.to_vec())[i], hash_nibbles[i]);
        }

    }
}