//! Some utilities for working with matrices. Those matrices are used for both
//! native and constraints.

use ark_ff::PrimeField;
use ark_std::{iter::FromIterator, vec::Vec};
use core::fmt::Debug;
use derivative::Derivative;
/// Specification for matrix.
pub trait MatrixSpec {
    // TODO: can matrix itself be variable?
    type MatrixField: Clone + Debug + 'static;
    type Field: Clone + Debug + 'static;

    fn field_zero() -> Self::Field;
    fn field_mul(a: Self::MatrixField, b: Self::Field) -> Self::Field;
    fn field_add(a: Self::Field, b: Self::Field) -> Self::Field;
    fn row_vec_product(a: &[Self::MatrixField], b: &[Self::Field]) -> Self::Field {
        let mut result = Self::field_zero();
        debug_assert_eq!(a.len(), b.len());
        for (a, b) in a.iter().zip(b.iter()) {
            result = Self::field_add(result, Self::field_mul(a.clone(), b.clone()));
        }
        result
    }

    /// return mat @ v
    fn matrix_vector_mul<'a>(
        mat: impl IntoIterator<Item = &'a [Self::MatrixField]>,
        v: &[Self::Field],
    ) -> Vec<Self::Field> {
        mat.into_iter()
            .map(|row| Self::row_vec_product(row, v))
            .collect()
    }

    fn transpose(input: &[Vec<Self::MatrixField>]) -> Vec<Vec<Self::MatrixField>> {
        let num_rows = input.len();
        let num_cols = input[0].len();
        let mut output = Vec::with_capacity(num_cols);
        for _ in 0..num_cols {
            output.push(Vec::with_capacity(num_rows));
        }
        for row in input.iter() {
            for (col, val) in row.iter().enumerate() {
                output[col].push(val.clone());
            }
        }
        output
    }
}

pub struct NativeMatrixSpec<F: PrimeField> {
    _field: ark_std::marker::PhantomData<F>,
}

impl<F: PrimeField> MatrixSpec for NativeMatrixSpec<F> {
    type MatrixField = F;
    type Field = F;

    fn field_zero() -> Self::Field {
        F::zero()
    }

    fn field_mul(a: Self::MatrixField, b: Self::Field) -> Self::Field {
        a * b
    }

    fn field_add(a: Self::Field, b: Self::Field) -> Self::Field {
        a + b
    }
}

#[derive(Derivative)]
#[derivative(
    PartialEq(bound = "S::MatrixField: PartialEq"),
    Eq(bound = "S::MatrixField: PartialEq"),
    Debug,
    Clone
)]
pub struct Matrix<S: MatrixSpec> {
    rows: usize,
    cols: usize,
    pub data: Vec<Vec<S::MatrixField>>,
}

impl<S: MatrixSpec> Matrix<S> {
    pub fn new(data: Vec<Vec<S::MatrixField>>) -> Self {
        let rows = data.len();
        let cols = data[0].len();
        for row in data.iter() {
            debug_assert_eq!(row.len(), cols);
        }
        Self { rows, cols, data }
    }

    pub fn num_rows(&self) -> usize {
        self.rows
    }

    pub fn num_cols(&self) -> usize {
        self.cols
    }

    pub fn mul_vector(&self, v: &[S::Field]) -> Vec<S::Field> {
        S::matrix_vector_mul(self.data.iter().map(|v| v.as_slice()), v)
    }

    pub fn transpose(&self) -> Matrix<S> {
        Matrix::new(S::transpose(&self.data))
    }
}

impl<S: MatrixSpec> From<Vec<Vec<S::MatrixField>>> for Matrix<S> {
    fn from(data: Vec<Vec<S::MatrixField>>) -> Self {
        Self::new(data)
    }
}

impl<S: MatrixSpec> FromIterator<Vec<S::MatrixField>> for Matrix<S> {
    fn from_iter<I: IntoIterator<Item = Vec<S::MatrixField>>>(iter: I) -> Self {
        Self::new(iter.into_iter().collect())
    }
}

#[cfg(test)]
mod tests {
    use crate::{Matrix, NativeMatrixSpec};
    use alloc::vec;
    use ark_bls12_381::Fr;
    use ark_ff::field_new;

    #[test]
    fn mul_vector() {
        let mat = Matrix::<NativeMatrixSpec<_>>::new(vec![
            vec![
                field_new!(Fr, "1"),
                field_new!(Fr, "2"),
                field_new!(Fr, "3"),
            ],
            vec![
                field_new!(Fr, "4"),
                field_new!(Fr, "5"),
                field_new!(Fr, "6"),
            ],
            vec![
                field_new!(Fr, "7"),
                field_new!(Fr, "8"),
                field_new!(Fr, "9"),
            ],
        ]);
        let v = vec![
            field_new!(Fr, "1"),
            field_new!(Fr, "2"),
            field_new!(Fr, "3"),
        ];

        let expected = vec![
            field_new!(Fr, "14"),
            field_new!(Fr, "32"),
            field_new!(Fr, "50"),
        ];
        let actual = mat.mul_vector(&v);

        assert_eq!(expected, actual);
    }

    #[test]
    fn transpose() {
        let mat = Matrix::<NativeMatrixSpec<_>>::new(vec![
            vec![
                field_new!(Fr, "1"),
                field_new!(Fr, "2"),
                field_new!(Fr, "3"),
            ],
            vec![
                field_new!(Fr, "4"),
                field_new!(Fr, "5"),
                field_new!(Fr, "6"),
            ],
            vec![
                field_new!(Fr, "7"),
                field_new!(Fr, "8"),
                field_new!(Fr, "9"),
            ],
        ]);
        let expected = Matrix::<NativeMatrixSpec<_>>::new(vec![
            vec![
                field_new!(Fr, "1"),
                field_new!(Fr, "4"),
                field_new!(Fr, "7"),
            ],
            vec![
                field_new!(Fr, "2"),
                field_new!(Fr, "5"),
                field_new!(Fr, "8"),
            ],
            vec![
                field_new!(Fr, "3"),
                field_new!(Fr, "6"),
                field_new!(Fr, "9"),
            ],
        ]);

        let actual = mat.transpose();

        assert_eq!(expected, actual);
    }
}
