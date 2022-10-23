# curveipo - 2D curve interpolation

<https://bues.ch/>

<https://bues.ch/cgit/curveipors.git>

<https://github.com/mbuesch/curveipors>

# Example

    use curveipo::{Curve, prelude::*};

    // Float curve.
    let curve = Curve::new([
        // (x, y) curve point
        (1.0_f32, -20.0_f32),
        (2.0, 2.0),
        (10.0, 20.0),
        (20.0, -17.0),
    ]);

    // Linear interpolation in float curve with float result.
    let x = 3.0;
    let y_interpolated = curve.lin_inter(x);
    float_eq::assert_float_eq!(y_interpolated, 4.25, abs <= 0.001);

    // Integer curve.
    let curve = Curve::new([
        // (x, y) curve point
        (1_i16, -20_i16),
        (2, 2),
        (10, 20),
        (20, -17),
    ]);

    // Linear interpolation in integer curve with rounded integer result.
    let x = 3;
    let y_interpolated = curve.lin_inter(x);
    assert_eq!(y_interpolated, 4);

# License

Copyright (c) 2022 Michael Büsch <m@bues.ch>

Licensed under the Apache License version 2.0 or the MIT license, at your option.

SPDX-License-Identifier: Apache-2.0 OR MIT
