use std::ops::Mul;

use num::bigint::BigInt;

struct Vector(BigInt, BigInt);
impl<T: Into<BigInt>> From<(T, T)> for Vector {
    fn from(value: (T, T)) -> Self {
        Self(value.0.into(), value.1.into())
    }
}

struct Matrix(Vector, Vector);
impl<T: Into<Vector>> From<(T, T)> for Matrix {
    fn from(value: (T, T)) -> Self {
        Self(value.0.into(), value.1.into())
    }
}

impl Mul<&Vector> for &Matrix {
    type Output = Vector;
    fn mul(self, rhs: &Vector) -> Self::Output {
        Vector(
            &rhs.0 * &self.0 .0 + &rhs.1 * &self.1 .0,
            &rhs.0 * &self.0 .1 + &rhs.1 * &self.1 .1,
        )
    }
}
impl Mul<&Matrix> for &Matrix {
    type Output = Matrix;
    fn mul(self, rhs: &Matrix) -> Self::Output {
        Matrix(self * &rhs.0, self * &rhs.1)
    }
}

fn mat_pow(mut m: Matrix, mut n: u32) -> Matrix {
    let mut r = Matrix::from(((1, 0), (0, 1)));
    while n > 0 {
        if n & 1 == 1 {
            r = &r * &m;
        }
        m = &m * &m;
        n >>= 1;
    }
    r
}
fn fib_mat(m: Matrix, n: u32) -> BigInt {
    let m = &mat_pow(m, n) * &Vector::from((0, 1));
    m.0
}

pub fn fib(n: i32) -> BigInt {
    if n >= 0 {
        fib_mat(Matrix::from(((0, 1), (1, 1))), n as u32)
    } else {
        fib_mat(Matrix::from(((-1, 1), (1, 0))), (-n) as u32)
    }
}
