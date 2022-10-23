// -*- coding: utf-8 -*-
//
// Copyright 2022 Michael Büsch <m@bues.ch>
//
// Licensed under the Apache License version 2.0
// or the MIT license, at your option.
// SPDX-License-Identifier: Apache-2.0 OR MIT
//

//! curveipo - 2D curve interpolation
//!
//! ```
//!     use curveipo::{Curve, prelude::*};
//!
//!     // Float curve.
//!     let curve = Curve::new([
//!         // (x, y) curve point
//!         (1.0_f32, -20.0_f32),
//!         (2.0, 2.0),
//!         (10.0, 20.0),
//!         (20.0, -17.0),
//!     ]);
//!
//!     // Linear interpolation in float curve with float result.
//!     let x = 3.0;
//!     let y_interpolated = curve.lin_inter(x);
//!     float_eq::assert_float_eq!(y_interpolated, 4.25, abs <= 0.001);
//!
//!     // Integer curve.
//!     let curve = Curve::new([
//!         // (x, y) curve point
//!         (1_i16, -20_i16),
//!         (2, 2),
//!         (10, 20),
//!         (20, -17),
//!     ]);
//!
//!     // Linear interpolation in integer curve with rounded integer result.
//!     let x = 3;
//!     let y_interpolated = curve.lin_inter(x);
//!     assert_eq!(y_interpolated, 4);
//! ```

#![no_std]

use core::marker::PhantomData;

pub trait CurvePoint<T> {
    /// Get the `x` coordinate of this curve point.
    fn x(&self) -> T;

    /// Get the `y` coordinate of this curve point.
    fn y(&self) -> T;
}

macro_rules! impl_curveipo_point_tuple {
    ($($type:ident),*) => {
        $(
            impl CurvePoint<$type> for ($type, $type) {
                #[inline]
                fn x(&self) -> $type {
                    self.0
                }

                #[inline]
                fn y(&self) -> $type {
                    self.1
                }
            }
        )*
    }
}

impl_curveipo_point_tuple!(f32, f64, i8, i16, i32, i64, i128, isize);

pub trait CurveIpo: Copy {
    /// Interpolate the `y` coordinate corresponding to an `x` coordiante (`self`)
    /// between the `left` hand curve point and the `right` hand curve point.
    ///
    /// This method uses linear interpolation between the support points.
    fn lin_inter(
        &self,
        left: &impl CurvePoint<Self>,
        right: &impl CurvePoint<Self>
    ) -> Self;

    /// Check if the `self` value is a finite value.
    ///
    /// This is only relevant for floating point types.
    /// Integer types are always finite.
    #[inline]
    fn is_finite(&self) -> bool {
        true
    }
}

macro_rules! impl_curveipo_t_float {
    ($($type:ty),*) => {
        $(
            impl CurveIpo for $type {
                #[inline]
                fn lin_inter(
                    &self,
                    left: &impl CurvePoint<Self>,
                    right: &impl CurvePoint<Self>
                ) -> Self {
                    let dx = right.x() - left.x();
                    let dy = right.y() - left.y();
                    if dx == 0.0 {
                        left.y()
                    } else {
                        ((*self - left.x()) * (dy / dx)) + left.y()
                    }
                }

                #[inline]
                fn is_finite(&self) -> bool {
                    <$type>::is_finite(*self)
                }
            }
        )*
    }
}

macro_rules! impl_curveipo_t_int {
    ($(($type:ty, $tmptype:ty)),*) => {
        $(
            impl CurveIpo for $type {
                #[inline]
                fn lin_inter(
                    &self,
                    left: &impl CurvePoint<Self>,
                    right: &impl CurvePoint<Self>
                ) -> Self {
                    let dx = right.x() as $tmptype - left.x() as $tmptype;
                    let dy = right.y() as $tmptype - left.y() as $tmptype;
                    if dx == 0 {
                        left.y()
                    } else {
                        let num = (*self as $tmptype - left.x() as $tmptype) * dy;
                        let den = dx;
                        let result = if (num < 0) ^ (den < 0) {
                            ((num - (den / 2)) / den) + left.y() as $tmptype
                        } else {
                            ((num + (den / 2)) / den) + left.y() as $tmptype
                        };
                        result.clamp(<$type>::MIN as $tmptype, <$type>::MAX as $tmptype) as $type
                    }
                }
            }
        )*
    }
}

impl_curveipo_t_float!(f32, f64);
impl_curveipo_t_int!((i8, i16), (i16, i32), (i32, i64), (i64, i128), (i128, i128), (isize, i128));

#[derive(Clone, Debug)]
pub struct Curve<T, P, const SIZE: usize> {
    points:     [P; SIZE],
    _phantom:   PhantomData<T>,
}

impl<T, P, const SIZE: usize> Curve<T, P, SIZE>
    where T: CurveIpo + PartialOrd + Copy,
          P: CurvePoint<T>,
{
    /// Create a new curve.
    ///
    /// The support points of the curve must be supplied as an array.
    ///
    /// The point type must implement the [CurvePoint] trait.
    ///
    /// This crate implements the [CurvePoint] trait for all tuples
    /// `(float, float)` and `(integer, integer)` for all float and integer types
    /// where `tuple.0` is the X coordinate and `tuple.1` is the Y coordinate.
    #[inline]
    pub const fn new(points: [P; SIZE]) -> Self {
        assert!(SIZE > 0);
        Self {
            points,
            _phantom: PhantomData,
        }
    }

    /// Linear interpolation.
    ///
    /// Interpolate a `y` coordinate in the curve at the `x` curve coordinate position
    /// using linear interpolation between two curve support points.
    ///
    /// This method returns the interpolated `y` coordinate.
    pub fn lin_inter(&self, x: T) -> T {
        let first: &P = &self.points[0];
        let last: &P = &self.points[self.points.len() - 1];
        if !x.is_finite() {
            x
        } else if x <= first.x() {
            first.y()
        } else if x >= last.x() {
            last.y()
        } else {
            // Find the curve points left handed and right handed to the x value.
            let mut lhp_found: Option<&P> = None;
            let mut rhp_found: &P = first;
            for rhp in &self.points {
                let rx = rhp.x();
                if let Some(lhp) = lhp_found {
                    // Curve X coordinates must be monotonically increasing.
                    debug_assert!(rx > lhp.x());
                }
                if rx > x {
                    rhp_found = rhp;
                    break;
                }
                if rx == x {
                    // Exact x match. Pick this y value.
                    return rhp.y();
                }
                lhp_found = Some(rhp);
            }
            // Linear interpolation between lhp and rhp.
            x.lin_inter(lhp_found.unwrap(), rhp_found)
        }
    }
}

pub mod prelude {
    pub use super::CurvePoint as _;
    pub use super::CurveIpo as _;
}

#[cfg(test)]
mod tests {
    use super::*;
    use float_eq::assert_float_eq;

    #[test]
    fn test_base() {
        let a = Curve::new([
            (1.0, 2.0),
        ]);
        assert_eq!(a.points.len(), 1);
        assert_eq!(a.points[0].x(), 1.0);
        assert_eq!(a.points[0].y(), 2.0);

        let a = Curve::new([
            (3.0, 4.0),
            (5.0, 6.0),
        ]);
        assert_eq!(a.points.len(), 2);
        assert_eq!(a.points[0].x(), 3.0);
        assert_eq!(a.points[0].y(), 4.0);
        assert_eq!(a.points[1].x(), 5.0);
        assert_eq!(a.points[1].y(), 6.0);
    }

    macro_rules! gen_test_float {
        ($testcase:ident, $type:ty) => {
            #[test]
            fn $testcase() {
                let a = Curve::new([
                    (1.0 as $type, 1.0 as $type),
                    (2.0 as $type, 2.0 as $type),
                    (10.0 as $type, 20.0 as $type),
                    (20.0 as $type, -17.0 as $type),
                ]);
                // out of bounds:
                assert_float_eq!(a.lin_inter(-100.0 as $type), 1.0 as $type, r2nd <= 0.001);
                assert_float_eq!(a.lin_inter(0.0 as $type), 1.0 as $type, r2nd <= 0.001);
                // in bounds:
                assert_float_eq!(a.lin_inter(1.0 as $type), 1.0 as $type, r2nd <= 0.001);
                assert_float_eq!(a.lin_inter(1.5 as $type), 1.5 as $type, r2nd <= 0.001);
                assert_float_eq!(a.lin_inter(2.0 as $type), 2.0 as $type, r2nd <= 0.001);
                assert_float_eq!(a.lin_inter(3.0 as $type), 4.25 as $type, r2nd <= 0.001);
                assert_float_eq!(a.lin_inter(3.5 as $type), 5.375 as $type, r2nd <= 0.001);
                assert_float_eq!(a.lin_inter(4.0 as $type), 6.5 as $type, r2nd <= 0.001);
                assert_float_eq!(a.lin_inter(5.0 as $type), 8.75 as $type, r2nd <= 0.001);
                assert_float_eq!(a.lin_inter(6.0 as $type), 11.0 as $type, r2nd <= 0.001);
                assert_float_eq!(a.lin_inter(7.0 as $type), 13.25 as $type, r2nd <= 0.001);
                assert_float_eq!(a.lin_inter(8.0 as $type), 15.5 as $type, r2nd <= 0.001);
                assert_float_eq!(a.lin_inter(8.5 as $type), 16.625 as $type, r2nd <= 0.001);
                assert_float_eq!(a.lin_inter(9.0 as $type), 17.75 as $type, r2nd <= 0.001);
                assert_float_eq!(a.lin_inter(10.0 as $type), 20.0 as $type, r2nd <= 0.001);
                assert_float_eq!(a.lin_inter(11.0 as $type), 16.3 as $type, r2nd <= 0.001);
                assert_float_eq!(a.lin_inter(11.3 as $type), 15.19 as $type, r2nd <= 0.001);
                assert_float_eq!(a.lin_inter(12.0 as $type), 12.6 as $type, r2nd <= 0.001);
                assert_float_eq!(a.lin_inter(16.0 as $type), -2.2 as $type, r2nd <= 0.001);
                assert_float_eq!(a.lin_inter(17.0 as $type), -5.9 as $type, r2nd <= 0.001);
                assert_float_eq!(a.lin_inter(17.4 as $type), -7.38 as $type, r2nd <= 0.001);
                assert_float_eq!(a.lin_inter(17.9 as $type), -9.23 as $type, r2nd <= 0.001);
                assert_float_eq!(a.lin_inter(18.0 as $type), -9.6 as $type, r2nd <= 0.001);
                assert_float_eq!(a.lin_inter(19.0 as $type), -13.3 as $type, r2nd <= 0.001);
                assert_float_eq!(a.lin_inter(20.0 as $type), -17.0 as $type, r2nd <= 0.001);
                // out of bounds:
                assert_float_eq!(a.lin_inter(21.0 as $type), -17.0 as $type, r2nd <= 0.001);
                assert_float_eq!(a.lin_inter(100.0 as $type), -17.0 as $type, r2nd <= 0.001);

                // Single point
                let a = Curve::new([
                    (2.0 as $type, 20.0 as $type),
                ]);
                assert_float_eq!(a.lin_inter(1.0 as $type), 20.0 as $type, r2nd <= 0.001);
                assert_float_eq!(a.lin_inter(2.0 as $type), 20.0 as $type, r2nd <= 0.001);
                assert_float_eq!(a.lin_inter(3.0 as $type), 20.0 as $type, r2nd <= 0.001);
            }
        }
    }

    macro_rules! gen_test_int {
        ($testcase:ident, $type:ty) => {
            #[test]
            fn $testcase() {
                let a = Curve::new([
                    (1 as $type, 1 as $type),
                    (2 as $type, 2 as $type),
                    (10 as $type, 20 as $type),
                    (20 as $type, -17 as $type),
                ]);
                // out of bounds:
                assert_eq!(a.lin_inter(-100 as $type), 1 as $type);
                assert_eq!(a.lin_inter(0 as $type), 1 as $type);
                // in bounds:
                assert_eq!(a.lin_inter(1 as $type), 1 as $type);
                assert_eq!(a.lin_inter(2 as $type), 2 as $type);
                assert_eq!(a.lin_inter(3 as $type), 4.25_f32.round() as $type);
                assert_eq!(a.lin_inter(4 as $type), 6.5_f32.round() as $type);
                assert_eq!(a.lin_inter(5 as $type), 8.75_f32.round() as $type);
                assert_eq!(a.lin_inter(6 as $type), 11 as $type);
                assert_eq!(a.lin_inter(7 as $type), 13.25_f32.round() as $type);
                assert_eq!(a.lin_inter(8 as $type), 15.5_f32.round() as $type);
                assert_eq!(a.lin_inter(9 as $type), 17.75_f32.round() as $type);
                assert_eq!(a.lin_inter(10 as $type), 20 as $type);
                assert_eq!(a.lin_inter(11 as $type), 16.3_f32.round() as $type);
                assert_eq!(a.lin_inter(12 as $type), 12.6_f32.round() as $type);
                assert_eq!(a.lin_inter(16 as $type), (-2.2_f32).round() as $type);
                assert_eq!(a.lin_inter(17 as $type), (-5.9_f32).round() as $type);
                assert_eq!(a.lin_inter(18 as $type), (-9.6_f32).round() as $type);
                assert_eq!(a.lin_inter(19 as $type), (-13.3_f32).round() as $type);
                assert_eq!(a.lin_inter(20 as $type), -17 as $type);
                // out of bounds:
                assert_eq!(a.lin_inter(21 as $type), -17 as $type);
                assert_eq!(a.lin_inter(100 as $type), -17 as $type);

                // Single point
                let a = Curve::new([
                    (2 as $type, 20 as $type),
                ]);
                assert_eq!(a.lin_inter(1 as $type), 20 as $type);
                assert_eq!(a.lin_inter(2 as $type), 20 as $type);
                assert_eq!(a.lin_inter(3 as $type), 20 as $type);
            }
        }
    }

    gen_test_float!(test_interpolate_f32, f32);
    gen_test_float!(test_interpolate_f64, f64);

    gen_test_int!(test_interpolate_i8, i8);
    gen_test_int!(test_interpolate_i16, i16);
    gen_test_int!(test_interpolate_i32, i32);
    gen_test_int!(test_interpolate_i64, i64);
    gen_test_int!(test_interpolate_i128, i128);
    gen_test_int!(test_interpolate_isize, isize);
}

// vim: ts=4 sw=4 expandtab
