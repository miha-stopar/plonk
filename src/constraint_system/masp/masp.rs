#![allow(clippy::too_many_arguments)]

use crate::constraint_system::StandardComposer;
use crate::constraint_system::Variable;
use dusk_bls12_381::BlsScalar;
use crate::constraint_system::ecc::Point;
use dusk_jubjub::{JubJubAffine, JubJubExtended, JubJubScalar};
use std::convert::TryInto;
use crate::constraint_system::masp::constants;
use dusk_bytes::Serializable;

impl StandardComposer {
    /// Check that (u,v) is a point on JubJub
    pub fn check_affine_ctedwards(&mut self, u: Variable, v: Variable) {

        // u*u = uu
        let uu = self.mul(
            BlsScalar::one(),
            u,
            u,
            BlsScalar::zero(),
            BlsScalar::zero(),
        );

        // v*v = v
        let vv = self.mul(
            BlsScalar::one(),
            v,
            v,
            BlsScalar::zero(),
            BlsScalar::zero(),
        );

        // JubJub parameters
        let d_j = -BlsScalar::from(10240) * BlsScalar::from(10241).invert().unwrap();
        let a_j = -BlsScalar::one();

        // a_j * uu + vv = 1 + d_j * uuvv
        // one big Plonk constraint
        self.poly_gate(
            uu,
            vv,
            self.zero_var,
            d_j,
            -a_j,
            -BlsScalar::one(),
            BlsScalar::zero(),
            BlsScalar::one(),
            BlsScalar::zero(),        
        );
    }

    /// decompress a JubJub point and validate
    pub fn decompress_validate(&mut self, u_bit: Variable, mut u_val: BlsScalar, v: Variable) {

        // high 254 bits of u
        u_val.divn(1);
        let u_high = self.add_input(u_val);

        // range check u_high to be < 254 bits
        self.range_gate(u_high, 254);

        // check that u_bit is a bit
        self.boolean_gate(u_bit);

        // reconstruct u with high bits and u_bit
        let u = self.add(
            (BlsScalar::from(2), u_high),
            (BlsScalar::one(), u_bit),
            BlsScalar::zero(),
            BlsScalar::zero(),
        );

        self.check_affine_ctedwards(u, v);        
    }

    /// ctEdwards <--> Montgomery conversion
    fn conversion(&mut self, x: Variable, y: Variable, u: Variable, v: Variable) {

        let root = (-BlsScalar::from(40694)).sqrt().unwrap();

        // y*u = sqrt(-40964) * x
        self.big_mul_gate(
            y,
            u,
            x,
            None,
            BlsScalar::one(),
            -root,
            BlsScalar::zero(),
            BlsScalar::zero(),
            BlsScalar::zero(),
        );

        // (x + 1)*v = x - 1
        // equivalent to xv - x + v + 1 = 0
        self.poly_gate(
            x,
            v,
            self.zero_var,
            BlsScalar::one(),
            -BlsScalar::one(),
            BlsScalar::one(),
            BlsScalar::zero(),
            BlsScalar::one(),
            BlsScalar::zero(),        
        );
    }

    /// converts a ctedwards point to montgomery form
    /// should only be used if the input point is known to be on the curve
    pub fn ctedwards_to_montgomery(&mut self, u: Variable, v: Variable) -> (Variable, Variable) {
        let u_val = self.variables[&u];
        let v_val = self.variables[&v];

        let root = (-BlsScalar::from(40694)).sqrt().unwrap();

        let x_val = (BlsScalar::one()+v_val)*(BlsScalar::one()-v_val).invert().unwrap();
        let y_val = root*(BlsScalar::one()+v_val)*((BlsScalar::one()-v_val)*u_val).invert().unwrap();

        let x = self.add_input(x_val);
        let y = self.add_input(y_val);

        self.conversion(x, y, u, v);

        (x, y)
    }

    /// converts a montgomery point to ctedwards form
    /// should only be used if the input point is known to be on the curve
    pub fn montgomery_to_ctedwards(&mut self, x: Variable, y: Variable) -> (Variable, Variable) {
        let x_val = self.variables[&x];
        let y_val = self.variables[&y];

        let root = (-BlsScalar::from(40694)).sqrt().unwrap();

        let u_val = root*x_val*y_val.invert().unwrap();
        let v_val = (x_val-BlsScalar::one())*(x_val+BlsScalar::one()).invert().unwrap();

        let u = self.add_input(u_val);
        let v = self.add_input(v_val);

        self.conversion(x, y, u, v);

        (u, v)
    }

    /// checks that a point is not of small order by doubling three times and
    /// seeing that the x coordinate is not 0
    pub fn affine_ctedwards_non_small_order(&mut self, u: Variable, v: Variable) {

        let u_val = self.variables[&u];
        let v_val = self.variables[&v];

        let jubjub_point = JubJubAffine::from_raw_unchecked(u_val,v_val);

        let point = Point::from_private_affine(self, jubjub_point);

        let point_2 = point.fast_add(self, point);
        let point_4 = point_2.fast_add(self, point_2);
        let point_8 = point_4.fast_add(self, point_4);

        // check that x is non-zero by asking the prover to supply 1/x
        let x_val = self.variables[point_8.x()];
        let x_inv_val = x_val.invert().unwrap();

        let x_inv = self.add_input(x_val);

        // x * (1/x) = 1
        self.big_mul_gate(
            *point_8.x(),
            x_inv,
            self.zero_var,
            None,
            BlsScalar::one(),
            BlsScalar::zero(),
            -BlsScalar::one(),
            BlsScalar::zero(),
            BlsScalar::zero(),
        );
    }

    /// Pedersen hash using Plookup
    pub fn pedersen_hash_to_point(&mut self, personalization: &[bool], bits: &[bool]) -> Point {

        assert_eq!(personalization.len(), 6);
    
        let mut edwards_result = Point::from_private_affine(self, JubJubExtended::identity().into());
        let mut bits = personalization.iter().chain(bits.iter()).peekable();
        let mut segment_generators = constants::PEDERSEN_CIRCUIT_GENERATORS.iter();
    
        let mut segment_i = 0;
        while bits.peek().is_some() {
            let mut segment_result = Point::from_private_affine(self, JubJubExtended::identity().into());
            let mut segment_windows = &segment_generators.next().expect("enough segments")[..];
    
            let mut window_i = 0;

            // uses edwards rather than montgomery coordinates
            while let Some(a) = bits.next() {
                let b = bits.next().unwrap_or(&false);
                let c = bits.next().unwrap_or(&false);

                let s0 = self.add_input(BlsScalar::from(*a as u64));
                let s1 = self.add_input(BlsScalar::from(*b as u64));
                let s2 = self.add_input(BlsScalar::from(*c as u64));

                // constrain to bits
                self.boolean_gate(s0);
                self.boolean_gate(s1);
                self.boolean_gate(s2);

                // compute the index of the correct generator multiple: g, 2g, 3g, or 4g
                let gen_index: usize = (1 + (*a as u8) + 2 * (*b as u8)).into();

                // get coordinates of the selected generator
                let (xs_val, yr_val) = segment_windows[0][gen_index];

                // coordinates for each of g, 2g, 3g, and 4g
                let x1 = BlsScalar::from(segment_windows[0][0].0);
                let x2 = BlsScalar::from(segment_windows[0][1].0);
                let x3 = BlsScalar::from(segment_windows[0][2].0);
                let x4 = BlsScalar::from(segment_windows[0][3].0);

                let y1 = BlsScalar::from(segment_windows[0][0].1);
                let y2 = BlsScalar::from(segment_windows[0][1].1);
                let y3 = BlsScalar::from(segment_windows[0][2].1);
                let y4 = BlsScalar::from(segment_windows[0][3].1);

                // get point P_r = (xs, yr) in Point form
                let pr = Point::from_public_affine(
                    self,
                    JubJubAffine::from_raw_unchecked(xs_val, yr_val)
                );

                // compute ys
                let ys_val = match c {
                    true => -yr_val,
                    false => yr_val,
                };

                // get point P_s = (xs, ys) in Point form
                let ps = Point::from_public_affine(
                    self,
                    JubJubAffine::from_raw_unchecked(xs_val, ys_val)
                );

                // 2 bit lookup for x coordinate
                self.poly_gate(
                    s0,
                    s1,
                    *pr.x(),
                    x4 + x1 - x2 - x3,
                    x2 - x1,
                    x3 - x1,
                    BlsScalar::one(),
                    x1,
                    BlsScalar::zero(),
                );

                // 2 bit lookup for y coordinate
                self.poly_gate(
                    s0,
                    s1,
                    *pr.y(),
                    y4 + y1 - y2 - y3,
                    y2 - y1,
                    y3 - y1,
                    BlsScalar::one(),
                    y1,
                    BlsScalar::zero(),
                );

                // conditionally negate generator
                self.poly_gate(
                    *pr.y(),
                    s2,
                    *ps.y(),
                    BlsScalar::from(2),
                    -BlsScalar::one(),
                    BlsScalar::zero(),
                    BlsScalar::one(),
                    BlsScalar::zero(),
                    BlsScalar::zero(),
                );

                // add new point to previous result
                segment_result.fast_add(self, ps);

                segment_windows = &segment_windows[1..];

                if segment_windows.is_empty() {
                    break;
                }
    
                window_i += 1;
            }

        // add new point to previous result
        edwards_result.fast_add(self, segment_result);

        segment_i += 1;
        }
        
        edwards_result
    }
    
}

#[cfg(test)]
mod tests {
    use crate::constraint_system::StandardComposer;
    #[test]
    fn test_masp_components() {
        let message: [u8; 7] = [0, 1, 1, 0, 0, 1, 0];
        let mut cs = StandardComposer::new();
        cs.pedersen_hash_to_point(&message[..]);        

        assert!(0==1);
    }
}