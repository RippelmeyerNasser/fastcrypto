// Copyright (c) 2022, Mysten Labs, Inc.
// SPDX-License-Identifier: Apache-2.0

use std::mem;
use std::ops::Neg;
use dashu::integer::IBig;
use dashu::base::DivRem;
use dashu::base::Signed;
use dashu::base::Gcd;

pub struct EuclideanAlgorithmOutput {
    pub gcd: IBig,
    pub x: IBig,
    pub y: IBig,
    pub a_divided_by_gcd: IBig,
    pub b_divided_by_gcd: IBig,
}

impl EuclideanAlgorithmOutput {
    fn flip(self) -> Self {
        Self {
            gcd: self.gcd,
            x: self.y,
            y: self.x,
            a_divided_by_gcd: self.b_divided_by_gcd,
            b_divided_by_gcd: self.a_divided_by_gcd,
        }
    }
}

/// Compute the greatest common divisor gcd of a and b. The output also returns the Bezout coefficients
/// x and y such that ax + by = gcd and also the quotients a / gcd and b / gcd.
pub fn extended_euclidean_algorithm(a: &IBig, b: &IBig) -> EuclideanAlgorithmOutput {
    if b < a {
        return extended_euclidean_algorithm(b, a).flip();
    }

    let mut s = (IBig::from(0), IBig::from(1));
    let mut t = (IBig::from(1), IBig::from(0));
    let mut r = (a.clone(), b.clone());

    while !r.0.is_zero() {
        let (q, r_prime) = r.1.div_rem(&r.0);
        r.1 = r.0;
        r.0 = r_prime;

        let f = |mut x: (IBig, IBig)| {
            mem::swap(&mut x.0, &mut x.1);
            x.0 -= &q * &x.1;
            x
        };
        s = f(s);
        t = f(t);
    }

    // The last coefficients are equal to +/- a / gcd(a,b) and b / gcd(a,b) respectively.
    let a_divided_by_gcd = if a.sign() != s.0.sign() {
        s.0.neg()
    } else {
        s.0
    };
    let b_divided_by_gcd = if b.sign() != t.0.sign() {
        t.0.neg()
    } else {
        t.0
    };

    if !r.1.is_negative() {
        EuclideanAlgorithmOutput {
            gcd: r.1,
            x: t.1,
            y: s.1,
            a_divided_by_gcd,
            b_divided_by_gcd,
        }
    } else {
        EuclideanAlgorithmOutput {
            gcd: r.1.neg(),
            x: t.1.neg(),
            y: s.1.neg(),
            a_divided_by_gcd,
            b_divided_by_gcd,
        }
    }
}

#[test]
fn test_xgcd() {
    test_xgcd_single(IBig::from(240), IBig::from(46));
    test_xgcd_single(IBig::from(-240), IBig::from(46));
    test_xgcd_single(IBig::from(240), IBig::from(-46));
    test_xgcd_single(IBig::from(-240), IBig::from(-46));
}

#[cfg(test)]
fn test_xgcd_single(a: IBig, b: IBig) {
    let output = extended_euclidean_algorithm(&a, &b);
    assert_eq!(output.gcd, a.clone().gcd(&b).into());
    assert_eq!(&output.x * &a.clone() + &output.y * &b, output.gcd);
    assert_eq!(output.a_divided_by_gcd, &a / &output.gcd);
    assert_eq!(output.b_divided_by_gcd, &b / &output.gcd);
}
