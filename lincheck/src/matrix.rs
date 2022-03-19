//! Some utilities for working with matrices. Those matrices are used for both native and constraints.

use ark_ff::PrimeField;
use ark_std::iter::FromIterator;
use ark_std::vec::Vec;
/// Specification for matrix.
pub trait MatrixSpec {
    // TODO: can matrix itself be variable?
    type MatrixField: Clone + 'static;
    type Field: Clone + 'static;

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
