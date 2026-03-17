struct Complex {
    real: Field,
    imaginary: Field,
}

fn add(a: Complex, b: Complex) -> Complex {
    Complex {
        real: a.real + b.real,
        imaginary: a.imaginary + b.imaginary,
    }
}

fn subtract(a: Complex, b: Complex) -> Complex {
    Complex {
        real: a.real - b.real,
        imaginary: a.imaginary - b.imaginary,
    }
}

fn multiply(a: Complex, b: Complex) -> Complex {
    Complex {
        real: (a.real * b.real) - (a.imaginary * b.imaginary),
        imaginary: (a.real * b.imaginary) + (a.imaginary * b.real),
    }
}

fn divide(a: Complex, b: Complex) -> Complex {
    let denominator = (b.real * b.real) + (b.imaginary * b.imaginary);
    Complex {
        real: ((a.real * b.real) + (a.imaginary * b.imaginary)) / denominator,
        imaginary: ((a.imaginary * b.real) - (a.real * b.imaginary)) / denominator,
    }
}

fn scalar_multiply(complex: Complex, scalar: Field) -> Complex {
    Complex {
        real: complex.real * scalar,
        imaginary: complex.imaginary * scalar,
    }
}

fn conjugate(complex: Complex) -> Complex {
    Complex {
        real: complex.real,
        imaginary: -complex.imaginary,
    }
}

fn squared_magnitude(complex: Complex) -> Field {
    (complex.real * complex.real) + (complex.imaginary * complex.imaginary)
}

// needs better implementation
fn sqrt(value: Field, iterations: u32) -> Field {
    if value == 0 {
        0
    } else {
        let mut x = value / 2;
        for _ in 0..iterations {
            x = (x + value / x) / 2;
        }
        x
    }
}

// needs better implementation
fn magnitude(complex: Complex, iterations: u32) -> Field {
    let squared_mag = squared_magnitude(complex);
    sqrt(squared_mag, iterations)
}

// needs better implementation
fn evaluate_polynomial(coefficients: [Field; 10], x: Complex) -> Complex {
    let mut result = Complex { real: 0, imaginary: 0 };
    let mut current_term = Complex { real: 1, imaginary: 0 };
    for i in 0..10 {
        let coeff = coefficients[i];
        result = add(result, scalar_multiply(current_term, coeff));
        current_term = multiply(current_term, x);
    }
    result
}

#[test]
fn test_add_simple() {
    let a = Complex { real: 1, imaginary: 2 };
    let b = Complex { real: 3, imaginary: 4 };
    let result = add(a, b);
    assert(result.real == 4); 
    assert(result.imaginary == 6); 
}

#[test]
fn test_add_zero() {
    let a = Complex { real: 1, imaginary: 2 };
    let b = Complex { real: 0, imaginary: 0 };
    let result = add(a, b);
    assert(result.real == 1); 
    assert(result.imaginary == 2); 
}

#[test]
fn test_add_negative() {
    let a = Complex { real: 1, imaginary: 2 };
    let b = Complex { real: -1, imaginary: -2 };
    let result = add(a, b);
    assert(result.real == 0); 
    assert(result.imaginary == 0); 
}

#[test]
fn test_add_imaginary_only() {
    let a = Complex { real: 0, imaginary: 2 };
    let b = Complex { real: 0, imaginary: 3 };
    let result = add(a, b);
    assert(result.real == 0); 
    assert(result.imaginary == 5); 
}

#[test]
fn test_add_large_numbers() {
    let a = Complex { real: 100000, imaginary: 200000 };
    let b = Complex { real: 300000, imaginary: 400000 };
    let result = add(a, b);
    assert(result.real == 400000); 
    assert(result.imaginary == 600000);
}

#[test]
fn test_add_inverse_numbers() {
    let a = Complex { real: 5, imaginary: 10 };
    let b = Complex { real: -5, imaginary: -10 };
    let result = add(a, b);
    assert(result.real == 0); 
    assert(result.imaginary == 0); 
}

#[test]
fn test_subtract_simple() {
    let a = Complex { real: 5, imaginary: 6 };
    let b = Complex { real: 3, imaginary: 4 };
    let result = subtract(a, b);
    assert(result.real == 2); 
    assert(result.imaginary == 2); 
}

#[test]
fn test_subtract_zero() {
    let a = Complex { real: 5, imaginary: 6 };
    let b = Complex { real: 0, imaginary: 0 };
    let result = subtract(a, b);
    assert(result.real == 5); 
    assert(result.imaginary == 6); 
}

#[test]
fn test_subtract_negative() {
    let a = Complex { real: 5, imaginary: 6 };
    let b = Complex { real: -3, imaginary: -4 };
    let result = subtract(a, b);
    assert(result.real == 8); 
    assert(result.imaginary == 10); 
}

#[test]
fn test_subtract_imaginary_only() {
    let a = Complex { real: 0, imaginary: 6 };
    let b = Complex { real: 0, imaginary: 3 };
    let result = subtract(a, b);
    assert(result.real == 0); 
    assert(result.imaginary == 3); 
}

#[test]
fn test_subtract_large_numbers() {
    let a = Complex { real: 300000, imaginary: 400000 };
    let b = Complex { real: 100000, imaginary: 200000 };
    let result = subtract(a, b);
    assert(result.real == 200000); 
    assert(result.imaginary == 200000); 
}

#[test]
fn test_subtract_inverse_numbers() {
    let a = Complex { real: 5, imaginary: 10 };
    let b = Complex { real: 5, imaginary: 10 };
    let result = subtract(a, b);
    assert(result.real == 0); 
    assert(result.imaginary == 0); 
}

#[test]
fn test_multiply_simple() {
    let a = Complex { real: 1, imaginary: 2 };
    let b = Complex { real: 3, imaginary: 4 };
    let result = multiply(a, b);
    assert(result.real == -5); 
    assert(result.imaginary == 10); 
}

#[test]
fn test_multiply_zero() {
    let a = Complex { real: 1, imaginary: 2 };
    let b = Complex { real: 0, imaginary: 0 };
    let result = multiply(a, b);
    assert(result.real == 0);
    assert(result.imaginary == 0);
}

#[test]
fn test_multiply_negative() {
    let a = Complex { real: 1, imaginary: 2 };
    let b = Complex { real: -3, imaginary: -4 };
    let result = multiply(a, b);
    assert(result.real == 5); 
    assert(result.imaginary == -10); 
}

#[test]
fn test_multiply_imaginary_only() {
    let a = Complex { real: 0, imaginary: 2 };
    let b = Complex { real: 0, imaginary: 3 };
    let result = multiply(a, b);
    assert(result.real == -6); 
    assert(result.imaginary == 0); 
}

#[test]
fn test_multiply_large_numbers() {
    let a = Complex { real: 100000, imaginary: 200000 };
    let b = Complex { real: 300000, imaginary: 400000 };
    let result = multiply(a, b);
    assert(result.real == -50000000000); 
    assert(result.imaginary == 100000000000); 
}

#[test]
fn test_multiply_inverse_numbers() {
    let a = Complex { real: 1, imaginary: 1 };
    let b = Complex { real: 1, imaginary: -1 };
    let result = multiply(a, b);
    assert(result.real == 2); 
    assert(result.imaginary == 0); 
}

#[test]
fn test_divide_simple() {
    let a = Complex { real: 1, imaginary: 2 };
    let b = Complex { real: 3, imaginary: 4 };
    let result = divide(a, b);
    assert(result.real == 11/25); 
    assert(result.imaginary == 2/25); 
}

#[test]
fn test_divide_by_itself() {
    let a = Complex { real: 3, imaginary: 4 };
    let b = Complex { real: 3, imaginary: 4 };
    let result = divide(a, b);
    assert(result.real == 1);
    assert(result.imaginary == 0);
}

#[test]
fn test_divide_by_one() {
    let a = Complex { real: 5, imaginary: 6 };
    let b = Complex { real: 1, imaginary: 0 };
    let result = divide(a, b);
    assert(result.real == 5);
    assert(result.imaginary == 6);
}

#[test]
fn test_divide_by_imaginary_only() {
    let a = Complex { real: 2, imaginary: 3 };
    let b = Complex { real: 0, imaginary: 1 };
    let result = divide(a, b);
    assert(result.real == 3); 
    assert(result.imaginary == -2); 
}

#[test]
fn test_divide_large_numbers() {
    let a = Complex { real: 200000, imaginary: 300000 };
    let b = Complex { real: 400000, imaginary: 500000 };
    let result = divide(a, b);
    assert(result.real == 23/41);
    assert(result.imaginary == 2/41);
}

#[test]
fn test_divide_inverse_numbers() {
    let a = Complex { real: 5, imaginary: -10 };
    let b = Complex { real: 5, imaginary: 10 };
    let result = divide(a, b);
    assert(result.real == -3/5);
    assert(result.imaginary == -4/5);
}

#[test]
fn test_scalar_multiply_basic() {
    let complex = Complex { real: 2, imaginary: 3 };
    let scalar = 2;
    let result = scalar_multiply(complex, scalar);
    assert(result.real == 4); 
    assert(result.imaginary == 6); 
}

#[test]
fn test_scalar_multiply_zero() {
    let complex = Complex { real: 2, imaginary: 3 };
    let scalar = 0;
    let result = scalar_multiply(complex, scalar);
    assert(result.real == 0); 
    assert(result.imaginary == 0); 
}

#[test]
fn test_scalar_multiply_one() {
    let complex = Complex { real: 2, imaginary: 3 };
    let scalar = 1;
    let result = scalar_multiply(complex, scalar);
    assert(result.real == 2);
    assert(result.imaginary == 3);
}

#[test]
fn test_scalar_multiply_negative() {
    let complex = Complex { real: 2, imaginary: 3 };
    let scalar = -1;
    let result = scalar_multiply(complex, scalar);
    assert(result.real == -2); 
    assert(result.imaginary == -3);
}

#[test]
fn test_scalar_multiply_large_number() {
    let complex = Complex { real: 2, imaginary: 3 };
    let scalar = 100000;
    let result = scalar_multiply(complex, scalar);
    assert(result.real == 200000); 
    assert(result.imaginary == 300000); 
}

#[test]
fn test_scalar_multiply_fraction() {
    let complex = Complex { real: 2, imaginary: 3 };
    let scalar = 1/2;
    let result = scalar_multiply(complex, scalar);
    assert(result.real == 1); 
    assert(result.imaginary == 3/2); 
}

#[test]
fn test_conjugate_basic() {
    let complex = Complex { real: 3, imaginary: 4 };
    let result = conjugate(complex);
    assert(result.real == 3); 
    assert(result.imaginary == -4); 
}

#[test]
fn test_conjugate_zero_imaginary() {
    let complex = Complex { real: 5, imaginary: 0 };
    let result = conjugate(complex);
    assert(result.real == 5); 
    assert(result.imaginary == 0); 
}

#[test]
fn test_conjugate_negative_real() {
    let complex = Complex { real: -3, imaginary: 4 };
    let result = conjugate(complex);
    assert(result.real == -3); 
    assert(result.imaginary == -4); 
}

#[test]
fn test_conjugate_negative_imaginary() {
    let complex = Complex { real: 3, imaginary: -4 };
    let result = conjugate(complex);
    assert(result.real == 3); 
    assert(result.imaginary == 4); 
}

#[test]
fn test_conjugate_large_numbers() {
    let complex = Complex { real: 100000, imaginary: 200000 };
    let result = conjugate(complex);
    assert(result.real == 100000); 
    assert(result.imaginary == -200000); 
}

#[test]
fn test_conjugate_zero() {
    let complex = Complex { real: 0, imaginary: 0 };
    let result = conjugate(complex);
    assert(result.real == 0);
    assert(result.imaginary == 0); 
}

#[test]
fn test_squared_magnitude_basic() {
    let complex = Complex { real: 3, imaginary: 4 };
    let result = squared_magnitude(complex);
    assert(result == 25); 
}

#[test]
fn test_squared_magnitude_zero() {
    let complex = Complex { real: 0, imaginary: 0 };
    let result = squared_magnitude(complex);
    assert(result == 0); 
}

#[test]
fn test_squared_magnitude_real_only() {
    let complex = Complex { real: 5, imaginary: 0 };
    let result = squared_magnitude(complex);
    assert(result == 25); 
}

#[test]
fn test_squared_magnitude_imaginary_only() {
    let complex = Complex { real: 0, imaginary: 6 };
    let result = squared_magnitude(complex);
    assert(result == 36); 
}

#[test]
fn test_squared_magnitude_negative_values() {
    let complex = Complex { real: -3, imaginary: -4 };
    let result = squared_magnitude(complex);
    assert(result == 25);
}

#[test]
fn test_squared_magnitude_large_numbers() {
    let complex = Complex { real: 1000, imaginary: 2000 };
    let result = squared_magnitude(complex);
    assert(result == 5000000);
}

#[test]
fn test_evaluate_polynomial_constant() {
    let coefficients = [2, 0, 0, 0, 0, 0, 0, 0, 0, 0]; 
    let x = Complex { real: 1, imaginary: 1 };
    let result = evaluate_polynomial(coefficients, x);
    assert(result.real == 2);
    assert(result.imaginary == 0);
}

#[test]
fn test_evaluate_polynomial_linear() {
    let coefficients = [0, 1, 0, 0, 0, 0, 0, 0, 0, 0]; 
    let x = Complex { real: 1, imaginary: 1 };
    let result = evaluate_polynomial(coefficients, x);
    assert(result.real == 1);
    assert(result.imaginary == 1);
}

#[test]
fn test_evaluate_polynomial_quadratic() {
    let coefficients = [0, 0, 1, 0, 0, 0, 0, 0, 0, 0];
    let x = Complex { real: 1, imaginary: 1 };
    let result = evaluate_polynomial(coefficients, x);
    assert(result.real == 0);
    assert(result.imaginary == 2);
}

#[test]
fn test_evaluate_polynomial_cubic() {
    let coefficients = [0, 0, 0, 1, 0, 0, 0, 0, 0, 0]; 
    let x = Complex { real: 1, imaginary: 1 };
    let result = evaluate_polynomial(coefficients, x);
    assert(result.real == -2);
    assert(result.imaginary == 2);
}

#[test]
fn test_evaluate_polynomial_higher_order() {
    let coefficients = [1, 1, 1, 1, 1, 1, 1, 1, 1, 1]; 
    let x = Complex { real: 1, imaginary: 1 };
    let result = evaluate_polynomial(coefficients, x);
    assert(result.real == 32);
    assert(result.imaginary == 1);
}

#[test]
fn test_evaluate_polynomial_zero() {
    let coefficients = [0, 0, 0, 0, 0, 0, 0, 0, 0, 0];
    let x = Complex { real: 1, imaginary: 1 };
    let result = evaluate_polynomial(coefficients, x);
    assert(result.real == 0);
    assert(result.imaginary == 0);
}
