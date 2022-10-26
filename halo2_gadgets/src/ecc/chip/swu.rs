use std::ops::Mul;

use halo2_proofs::{
    circuit::{AssignedCell, Region, Value},
    plonk::{Advice, Assigned, Column, ConstraintSystem, Constraints, Error, Expression, Selector},
    poly::Rotation,
};
use pasta_curves::pallas;

use super::EccPoint;

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct Config {
    q_swu: Selector,
    // a-coefficient of the curve
    pub a: Column<Advice>,
    // b-coefficient of the curve
    pub b: Column<Advice>,
    // theta
    pub theta: Column<Advice>,
    // root-of-unity
    pub root_of_unity: Column<Advice>,
    // z value
    pub z: Column<Advice>,
    // u value
    pub u: Column<Advice>,
    // ta_inv value
    pub ta_inv: Column<Advice>,
    // div3_inv value
    pub div3_inv: Column<Advice>,
    // sqrt 1
    pub sqrt1: Column<Advice>,
    // sqrt 2
    pub sqrt2: Column<Advice>,
    // num_gx1_inv
    pub num_gx1_inv: Column<Advice>,
    // gx1_square
    pub gx1_square: Column<Advice>,
    // y1
    pub y1: Column<Advice>,
    // u_is_odd == y_is_odd
    pub u_is_odd_eq_y_is_odd: Column<Advice>,
    // condition like δ = inv0(y_p + y_q) if x_q = x_p, 0 otherwise ?????
    // delta: Column<Advice>,
}

impl Config {
    #[allow(clippy::too_many_arguments)]
    pub(super) fn configure(
        meta: &mut ConstraintSystem<pallas::Base>,
        a: Column<Advice>,
        b: Column<Advice>,
        theta: Column<Advice>,
        root_of_unity: Column<Advice>,
        z: Column<Advice>,
        u: Column<Advice>,
        ta_inv: Column<Advice>,
        div3_inv: Column<Advice>,
        sqrt1: Column<Advice>,
        sqrt2: Column<Advice>,
        num_gx1_inv: Column<Advice>,
        gx1_square: Column<Advice>,
        y1: Column<Advice>,
        u_is_odd_eq_y_is_odd: Column<Advice>,
    ) -> Self {
        meta.enable_equality(a);
        meta.enable_equality(b);
        meta.enable_equality(theta);
        meta.enable_equality(root_of_unity);
        meta.enable_equality(z);
        meta.enable_equality(u);
        meta.enable_equality(ta_inv);

        let config = Self {
            q_swu: meta.selector(),
            a,
            b,
            theta,
            root_of_unity,
            z,
            u,
            ta_inv,
            div3_inv,
            sqrt1,
            sqrt2,
            num_gx1_inv,
            gx1_square,
            y1,
            u_is_odd_eq_y_is_odd,
        };

        config.create_gate(meta);

        config
    }

    fn create_gate(&self, meta: &mut ConstraintSystem<pallas::Base>) {
        meta.create_gate("map_to_curve_simple_swu", |meta| {
            let q_swu = meta.query_selector(self.q_swu);
            let a = meta.query_advice(self.a, Rotation::cur());
            let b = meta.query_advice(self.b, Rotation::cur());
            let theta = meta.query_advice(self.theta, Rotation::cur());
            let root_of_unity = meta.query_advice(self.root_of_unity, Rotation::cur());
            let z = meta.query_advice(self.z, Rotation::cur());
            let u = meta.query_advice(self.u, Rotation::cur());
            let ta_inv = meta.query_advice(self.ta_inv, Rotation::cur());
            let div3_inv = meta.query_advice(self.div3_inv, Rotation::cur());
            let sqrt1 = meta.query_advice(self.sqrt1, Rotation::cur());
            let sqrt2 = meta.query_advice(self.sqrt2, Rotation::cur());
            let num_gx1_inv = meta.query_advice(self.num_gx1_inv, Rotation::cur());
            let gx1_square = meta.query_advice(self.gx1_square, Rotation::cur());
            let y1 = meta.query_advice(self.y1, Rotation::cur());
            let u_is_odd_eq_y_is_odd =
                meta.query_advice(self.u_is_odd_eq_y_is_odd, Rotation::cur());

            let one = Expression::Constant(pallas::Base::one());

            let u2 = u.square();
            let z_u2 = z.clone() * u2.clone();
            let z_u2_2 = z_u2.square();
            let ta = z_u2_2.clone() * z_u2.clone();
            let num_x1 = (ta.clone() + one.clone()) * b.clone();

            let ta_eq_0 = one.clone() - ta * ta_inv;
            let div = ta_eq_0 * z + (ta_eq_0 - one) * (-ta);

            let num2_x1 = num_x1 * num_x1;
            let div2 = div * div;
            let div3 = div2 * div;
            let num_gx1 = (num2_x1 + a * div2) * num_x1 + b * div3;
            let num_x2 = num_x1 * z_u2;

            let _a = div3_inv;
            let _b = _a * root_of_unity;

            let is_sqrt1 = _a - sqrt1.square();
            let is_sqrt2 = _b - sqrt2.square();

            let num_gx1_eq_zero = one - num_gx1 * num_gx1_inv;

            let div3_eq_zero = one - div3 * _a;

            let y2 = theta * z_u2 * u * y1;

            let num_x = gx1_square * num_x1 + (one - gx1_square) * num_x2;
            let y = gx1_square * y1 + (one - gx1_square) * y2;

            let y = u_is_odd_eq_y_is_odd * y - y * (one - u_is_odd_eq_y_is_odd);

            Constraints::with_selector(
                q_swu,
                [
                    ("1", ta_eq_0),
                    ("2", is_sqrt1),
                    ("3", is_sqrt2),
                    ("4", num_gx1_eq_zero),
                    ("5", div3_eq_zero),
                ],
            )
        });
    }

    pub(super) fn assign_region(
        &self,
        z: AssignedCell<Assigned<pallas::Base>, pallas::Base>,
        u: AssignedCell<Assigned<pallas::Base>, pallas::Base>,
        offset: usize,
        region: &mut Region<'_, pallas::Base>,
    ) -> Result<EccPoint, Error> {
        // Enable `q_add` selector
        self.q_swu.enable(region, offset)?;

        z.copy_advice(|| "z", region, self.z, offset)?;
        u.copy_advice(|| "u", region, self.u, offset)?;

        let zz = z.value();
        let uu = u.value();

        let a = Value::known(pallas::Base::zero());
        let b = Value::known(pallas::Base::from(5));

        let one = Value::known(pallas::Base::one());

        // theta,
        // root_of_unity,
        // z,
        // u,

        // ta_inv
        let u2 = uu.square();
        let z_u2 = zz.zip(u2).map(|(z, u2)| *z * u2);
        let z_u2_2 = z_u2.square();
        let ta = z_u2_2.zip(z_u2).map(|(x, y)| x * y);
        let ta_inv = ta.invert();
        region.assign_advice(|| "ta_inv", self.ta_inv, offset, || ta_inv);

        // div3_inv
        let div = ta
            .zip(zz)
            .map(|(ta, z)| if ta.is_zero_vartime() { *z } else { -ta });

        let num_x1 = (ta + one) * b;
        let num2_x1 = num_x1 * num_x1;
        let div2 = div.square();
        let div3 = div2 * div;
        let div3_inv = div3.invert();
        region.assign_advice(|| "div3_inv", self.div3_inv, offset, || div3_inv);

        // TODO WIP

        // sqrt1
        // ?
        let sqrt1 = div3_inv.map(|x| x.sqrt());
        region.assign_advice(|| "sqrt1", self.sqrt1, offset, || div3_inv.sqrt());
        let _a = div3_inv;
        let _b = _a * root_of_unity;

        // sqrt2,
        // num_gx1_inv,
        // gx1_square,
        // y1,
        // u_is_odd_eq_y_is_odd,

        let result = EccPoint::from_coordinates_unchecked(x_r_cell, y_r_cell);
        Ok(result)
    }
}

#[cfg(test)]
pub mod tests {
    use group::{prime::PrimeCurveAffine, Curve};
    use halo2_proofs::{
        circuit::{Layouter, Value},
        plonk::Error,
    };
    use pasta_curves::{arithmetic::CurveExt, pallas};

    use crate::ecc::{chip::EccPoint, EccInstructions, NonIdentityPoint};

    #[allow(clippy::too_many_arguments)]
    pub fn test_add<
        EccChip: EccInstructions<pallas::Affine, Point = EccPoint> + Clone + Eq + std::fmt::Debug,
    >(
        chip: EccChip,
        mut layouter: impl Layouter<pallas::Base>,
        p_val: pallas::Affine,
        p: &NonIdentityPoint<pallas::Affine, EccChip>,
        q_val: pallas::Affine,
        q: &NonIdentityPoint<pallas::Affine, EccChip>,
        p_neg: &NonIdentityPoint<pallas::Affine, EccChip>,
    ) -> Result<(), Error> {
        // Make sure P and Q are not the same point.
        assert_ne!(p_val, q_val);

        // Check complete addition P + (-P)
        let zero = {
            let result = p.add(layouter.namespace(|| "P + (-P)"), p_neg)?;
            result
                .inner()
                .is_identity()
                .assert_if_known(|is_identity| *is_identity);
            result
        };

        // Check complete addition 𝒪 + 𝒪
        {
            let result = zero.add(layouter.namespace(|| "𝒪 + 𝒪"), &zero)?;
            result.constrain_equal(layouter.namespace(|| "𝒪 + 𝒪 = 𝒪"), &zero)?;
        }

        // Check P + Q
        {
            let result = p.add(layouter.namespace(|| "P + Q"), q)?;
            let witnessed_result = NonIdentityPoint::new(
                chip.clone(),
                layouter.namespace(|| "witnessed P + Q"),
                Value::known((p_val + q_val).to_affine()),
            )?;
            result.constrain_equal(layouter.namespace(|| "constrain P + Q"), &witnessed_result)?;
        }

        // P + P
        {
            let result = p.add(layouter.namespace(|| "P + P"), p)?;
            let witnessed_result = NonIdentityPoint::new(
                chip.clone(),
                layouter.namespace(|| "witnessed P + P"),
                Value::known((p_val + p_val).to_affine()),
            )?;
            result.constrain_equal(layouter.namespace(|| "constrain P + P"), &witnessed_result)?;
        }

        // P + 𝒪
        {
            let result = p.add(layouter.namespace(|| "P + 𝒪"), &zero)?;
            result.constrain_equal(layouter.namespace(|| "P + 𝒪 = P"), p)?;
        }

        // 𝒪 + P
        {
            let result = zero.add(layouter.namespace(|| "𝒪 + P"), p)?;
            result.constrain_equal(layouter.namespace(|| "𝒪 + P = P"), p)?;
        }

        // (x, y) + (ζx, y) should behave like normal P + Q.
        let endo_p = p_val.to_curve().endo();
        let endo_p = NonIdentityPoint::new(
            chip.clone(),
            layouter.namespace(|| "endo(P)"),
            Value::known(endo_p.to_affine()),
        )?;
        p.add(layouter.namespace(|| "P + endo(P)"), &endo_p)?;

        // (x, y) + (ζx, -y) should also behave like normal P + Q.
        let endo_p_neg = (-p_val).to_curve().endo();
        let endo_p_neg = NonIdentityPoint::new(
            chip.clone(),
            layouter.namespace(|| "endo(-P)"),
            Value::known(endo_p_neg.to_affine()),
        )?;
        p.add(layouter.namespace(|| "P + endo(-P)"), &endo_p_neg)?;

        // (x, y) + ((ζ^2)x, y)
        let endo_2_p = p_val.to_curve().endo().endo();
        let endo_2_p = NonIdentityPoint::new(
            chip.clone(),
            layouter.namespace(|| "endo^2(P)"),
            Value::known(endo_2_p.to_affine()),
        )?;
        p.add(layouter.namespace(|| "P + endo^2(P)"), &endo_2_p)?;

        // (x, y) + ((ζ^2)x, -y)
        let endo_2_p_neg = (-p_val).to_curve().endo().endo();
        let endo_2_p_neg = NonIdentityPoint::new(
            chip,
            layouter.namespace(|| "endo^2(-P)"),
            Value::known(endo_2_p_neg.to_affine()),
        )?;
        p.add(layouter.namespace(|| "P + endo^2(-P)"), &endo_2_p_neg)?;

        Ok(())
    }
}
