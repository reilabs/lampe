use dep::std;

global MAX: Fraction = Fraction { sign: true, num: 3050913689, den: 1 };
global MIN: Fraction = Fraction { sign: false, num: 3050913689, den: 1 };
global ZERO: Fraction = Fraction { sign: true, num: 0, den: 1 };
global ONE: Fraction = Fraction { sign: true, num: 1, den: 1 };
global NEGATIVE_ONE: Fraction = Fraction { sign: false, num: 1, den: 1 };

struct Fraction {
    sign: bool,
    num: u32,
    den: u32,
}


// Create a Fraction type variable without lenghtier code
fn toFraction(s: bool, n: u32, d: u32) -> Fraction {
    assert (d != 0);
    let fr = Fraction {
        sign: s,
        num: n,
        den: d,
    };
    fr
}


// Swaps the numerator and denominator
fn invertFraction(f: Fraction) -> Fraction {
    assert (f.num != 0);
    let fr = Fraction {
        sign: f.sign,
        num: f.den,
        den: f.num,
    };
    fr
}

// Changes the Sign of the Fraction
fn signChangeFraction(f: Fraction) -> Fraction {
    let fr = Fraction {
        sign: !f.sign,
        num: f.num,
        den: f.den,
    };
    fr
}


// Multiplies two fractions
fn multiplyFraction(f1: Fraction, f2: Fraction) -> Fraction {
    let mut an = U128::from_integer(f1.num);
    let mut ad = U128::from_integer(f1.den);
    let mut bn = U128::from_integer(f2.num);
    let mut bd = U128::from_integer(f2.den);
    let mut m = f1;
    let mut n = f2;
    

    if ((an*bn > U128::from_integer(2000000000)) | (ad*bd > U128::from_integer(2000000000))) {
        m = reduceFraction(m);
        n = reduceFraction(n);
    }

    an = U128::from_integer(m.num);
    ad = U128::from_integer(m.den);
    bn = U128::from_integer(n.num);
    bd = U128::from_integer(n.den);

    
    if ((an*bn > U128::from_integer(2000000000)) | (ad*bd > U128::from_integer(2000000000))) {
        let mut c = Fraction{ sign: m.sign, num: m.num, den: n.den};
        let mut d = Fraction{ sign: n.sign, num: n.num, den: m.den};
        c = reduceFraction(c);
        d = reduceFraction(d);
        an = U128::from_integer(c.num);
        ad = U128::from_integer(c.den);
        bn = U128::from_integer(d.num);
        bd = U128::from_integer(d.den);
    }

    
    let mut ddd = (an*bn)/(ad*bd);
    let mut factor = U128::from_integer(1);
    for i in 1..5{
        if ddd*U128::from_integer(10) < U128::from_integer(2000000000) {
            factor *= U128::from_integer(10);
            ddd = ddd * U128::from_integer(10);
        }
    }
    
    if ((an*bn > U128::from_integer(2000000000)) | (ad*bd > U128::from_integer(2000000000))) {
        let fx: u32 = U128::to_integer(factor);
        let np: u32 = U128::to_integer((an*bn*factor)/(ad*bd));
        let fr = Fraction{
            sign: (f1.sign == f2.sign),
            num: np,
            den: fx,
        };
        fr
        
    }
    else {
        let fr = Fraction {
            sign: (m.sign == n.sign),
            num: m.num*n.num,
            den: m.den*n.den,
        };
        fr
        
    }
    
    
}

// Divides the first fraction by the second and outputs the quotient
fn divideFraction(f1: Fraction, f2: Fraction) -> Fraction {
    assert (f2.num != 0);
    let f3 = Fraction {
        sign: f2.sign,
        num: f2.den,
        den: f2.num,
    };
    let fr = multiplyFraction(f1, f3);
    
    fr
}

// this method will only work till numerator and denominator values are under 100
// this has been set for efficiency reasons, and will be modified once the Noir team
// can implement dynamic limit for loops
fn reduceFraction(f: Fraction) -> Fraction {
    let mut a = f.num;
    let mut b = f.den;
    let mut min = 0;
    let mut j = 1;
    let mut gcd = 1;
    if a > b {
        min = b;
    }
    else {
        min = a;
    }
    
    for i in 2..100{
        j = i as u32;
        if (j <= min){
            if (a%j == 0) & (b%j == 0){
                gcd = j;
            }
        }
    }
    
    
    let fr = Fraction {
        sign: f.sign,
        num: f.num/gcd,
        den: f.den/gcd,
    };
    fr
}


// Adds two fractions
fn addFraction(f1: Fraction, f2: Fraction) -> Fraction {
    let mut an = U128::from_integer(f1.num);
    let mut ad = U128::from_integer(f1.den);
    let mut bn = U128::from_integer(f2.num);
    let mut bd = U128::from_integer(f2.den);
    let mut m = f1;
    let mut n = f2;

    if f1.sign == f2.sign {
       
        if ((ad*bd > U128::from_integer(2000000000)) | ((an*bd + ad*bn) > U128::from_integer(2000000000)) | ((an*bd) > U128::from_integer(2000000000)) | ((ad*bn) > U128::from_integer(2000000000))){
            m = reduceFraction(m);
            n = reduceFraction(n);
        }
        an = U128::from_integer(m.num);
        ad = U128::from_integer(m.den);
        bn = U128::from_integer(n.num);
        bd = U128::from_integer(n.den);
        if ((ad*bd > U128::from_integer(2000000000)) | ((an*bd + ad*bn) > U128::from_integer(2000000000)) | ((an*bd) > U128::from_integer(2000000000)) | ((ad*bn) > U128::from_integer(2000000000))){
            let mut ddd = (an*bd + ad*bn)/(ad*bd);
            let mut factor = U128::from_integer(1);
            for i in 1..5{
                if ddd*U128::from_integer(10) < U128::from_integer(2000000000) {
                    ddd *= U128::from_integer(10);
                    factor *= U128::from_integer(10);
                }
            }
            let np: u32 = U128::to_integer(((an*bd + ad*bn)*factor)/(ad*bd));
            let fx: u32 = U128::to_integer(factor);
            let fr = Fraction {
                sign: f1.sign,
                num: np,
                den: fx, 
            };
            fr
        }
        else {
            let fr = Fraction {
                sign: f1.sign,
                num: (m.num*n.den + n.num*m.den),
                den: m.den*n.den,
            };
            fr
        }
        
        
    }
    else {

        if ((an*bd) > (bn*ad)){
            if ((ad*bd > U128::from_integer(2000000000)) | ((an*bd - ad*bn) > U128::from_integer(2000000000)) | ((an*bd) > U128::from_integer(2000000000))){
                m = reduceFraction(m);
                n = reduceFraction(n);
            }
            an = U128::from_integer(m.num);
            ad = U128::from_integer(m.den);
            bn = U128::from_integer(n.num);
            bd = U128::from_integer(n.den);
            
            if ((ad*bd > U128::from_integer(2000000000)) | ((an*bd - ad*bn) > U128::from_integer(2000000000)) | ((an*bd) > U128::from_integer(2000000000))){
                let mut ddd = (an*bd - ad*bn)/(ad*bd);
                let mut factor = U128::from_integer(1);
                for i in 1..5{
                    if ddd*U128::from_integer(10) < U128::from_integer(2000000000) {
                        ddd *= U128::from_integer(10);
                        factor *= U128::from_integer(10);
                    }
                }
                let np: u32 = U128::to_integer(((an*bd - ad*bn)*factor)/(ad*bd));
                let fx: u32 = U128::to_integer(factor);
                let fr = Fraction {
                    sign: f1.sign,
                    num: np,
                    den: fx, 
                };
                fr
            }
            else {
                let fr = Fraction {
                    sign: f1.sign,
                    num: (m.num*n.den - n.num*m.den),
                    den: m.den*n.den,
                };
                fr
            }
        }
        else {
            if ((ad*bd > U128::from_integer(2000000000)) | ((bn*ad - bd*an) > U128::from_integer(2000000000)) | ((bn*ad) > U128::from_integer(2000000000))){
                m = reduceFraction(m);
                n = reduceFraction(n);
            }
            an = U128::from_integer(m.num);
            ad = U128::from_integer(m.den);
            bn = U128::from_integer(n.num);
            bd = U128::from_integer(n.den);
            if ((ad*bd > U128::from_integer(2000000000)) | ((bn*ad - bd*an) > U128::from_integer(2000000000)) | ((bn*ad) > U128::from_integer(2000000000))){
                let mut ddd = (bn*ad - bd*an)/(ad*bd);
                let mut factor = U128::from_integer(1);
                for i in 1..5{
                    if ddd*U128::from_integer(10) < U128::from_integer(2000000000) {
                        ddd *= U128::from_integer(10);
                        factor *= U128::from_integer(10);
                    }
                }
                let np: u32 = U128::to_integer(((bn*ad - bd*an)*factor)/(ad*bd));
                let fx: u32 = U128::to_integer(factor);
                let fr = Fraction {
                    sign: f2.sign,
                    num: np,
                    den: fx, 
                };
                fr
            }
            else {
                let fr = Fraction {
                    sign: f2.sign,
                    num: (n.num*m.den - m.num*n.den),
                    den: m.den*n.den,
                };
                fr
            }
        }
    }
}


// Subtracts the second fraction from the first
fn subtractFraction(f1: Fraction, f2: Fraction) -> Fraction {
    let f3 = Fraction {
        sign: !f2.sign,
        num: f2.num,
        den: f2.den,
    };
    let fr = addFraction(f1, f3);
    
    fr
}





// if a > b return 1
// if a < b return 2
// if a == b return 0
fn compareFraction(f1: Fraction, f2: Fraction) -> u32 {
    if ((f1.num == f2.num) & (f1.num == 0)){
        0
    }
    else {
        if (f1.sign != f2.sign){
            if (f1.sign){
                1
            }
            else {
                2
            }
        }
        else {
            
            if ((f1.num*f2.den) > (f2.num*f1.den)){
                if (f1.sign){
                    1
                }
                else {
                    2
                }
            }
            else {
                
                if ((f1.num*f2.den) != (f2.num*f1.den)){
                    if (f1.sign){
                        2
                    }
                    else {
                        1
                    }
                }
                else {
                    0
                }
                
            }
            
        }
    }
    
}


// Multiplies a fraction by itself
fn squareFraction(f: Fraction) -> Fraction {
    let fr = multiplyFraction(f, f);
    fr
}


// Multiplies a fraction by itself, then again by itself
fn cubeFraction(f: Fraction) -> Fraction {
    let fr = Fraction {
        sign: f.sign,
        num: f.num*f.num*f.num,
        den: f.den*f.den*f.den,
    };
    fr
}

// Only a helper function for trigonometric computations
// Warning: Do NOT fork and remove the assert limits. It will crash your machine for big values
fn powerSmallFraction(f: Fraction, k: u8) -> Fraction {
    assert (k >= 1);
    assert (k < 10);
    assert ((f.num * 7) <= (11 * f.den));
    let mut n = U128::from_integer(f.num);
    let mut d = U128::from_integer(f.den);
    if f.den > 10000 {
        n = (n*U128::from_integer(10000))/d;
        d = U128::from_integer(10000);
    }
    if n == U128::from_integer(0){
        let fr = Fraction {
            sign: true,
            num: 0,
            den: 1,
        };
        fr
    }
    else {
        let mut nprod = U128::from_integer(1);
        let mut dprod = U128::from_integer(1);
        let mut s = true;
        if ((!f.sign) & (k % 2 == 1)){
            s = false;
        }
        for i in 1..10 {
            if i as u8 <= k {
                nprod = nprod * n;
                dprod = dprod * d;
            }
        }
        let new_num: u32 = U128::to_integer((nprod*U128::from_integer(10000))/dprod);
        let fr = Fraction {
            sign: s,
            num: new_num,
            den: 10000,
        };
        fr

    }
}


// Adds 1 to the fraction
fn incrFraction(f: Fraction) -> Fraction {
    let inc = Fraction {
        sign: true,
        num: 1,
        den: 1,
    };
    let fr = addFraction(f, inc);
    fr
}


// Subtracts 1 from the fraction
fn decrFraction(f: Fraction) -> Fraction {
    let dec = Fraction {
        sign: true,
        num: 1,
        den: 1,
    };
    let fr = subtractFraction(f, dec);
    fr
}


// Returns true if the fraction can be represented as an Integer
fn isInteger(f: Fraction) -> bool {
    if f.num == 0 {
        true
    }
    else {
        if (f.num % f.den == 0) {
            true
        }
        else {
            false
        }
    }
    
}


// Returns true if the fraction can NOT be represented as an Integer
fn isNotInteger(f: Fraction) -> bool {
    if f.num == 0 {
        false
    }
    else {
        if (f.num % f.den == 0) {
            false
        }
        else {
            true
        }
    }
    
}


// Returns the closest but smaller Integer to the Given Fraction, but typecast to Fraction for convenience
fn floor(f: Fraction) -> Fraction {
    let q = f.num/f.den;
    if (q * f.den == f.num){
        let fr = Fraction{
            sign: f.sign,
            num: f.num,
            den: f.den,
        };
        fr
    }
    else {
        if f.sign {
            let fr = Fraction{
                sign: f.sign,
                num: q,
                den: 1,
            };
            fr    
        }
        else {
            let fr = Fraction{
                sign: f.sign,
                num: q + 1,
                den: 1,
            };
            fr 
        }
        
    }
}

// Returns the closest but greater Integer to the Given Fraction, but typecast to Fraction for convenience
fn ceiling(f: Fraction) -> Fraction {
    let q = f.num/f.den;
    if (q * f.den == f.num){
        let fr = Fraction{
            sign: f.sign,
            num: f.num,
            den: f.den,
        };
        fr
    }
    else {
        if f.sign {
            let fr = Fraction{
                sign: f.sign,
                num: q + 1,
                den: 1,
            };
            fr    
        }
        else {
            let fr = Fraction{
                sign: f.sign,
                num: q,
                den: 1,
            };
            fr 
        }
        
    }
}


// returns the approximate square root of the Fraction
// passes refers to the number of iterations run to add more precision
// for num and den < 10000, passes = 10 is a good choice
// for num or den > 10000, passes = 15 is reasonable
// it should be noted that more passes lead to more gas usage, hence a tradeoff 
// between precision and viability is recommended 
unconstrained fn sqrt(x: Fraction, passes: u8) -> Fraction {
    assert((x.sign != false) | (x.num == 0));
    if x.num == 0 {
        x
    }
    else {
        let mut sqrt_approx = Fraction {
            sign: true,
            num: (x.num + 1)/2,
            den: x.den,
        };
        
        let p = U128::from_integer(x.num);
        let q = U128::from_integer(x.den);

        let mut c_init = U128::from_integer(sqrt_approx.num);
        let mut d_init = U128::from_integer(sqrt_approx.den);

        let mut c = c_init;
        let mut d = d_init;


        for i in 0..passes {
            c = (q*c_init*c_init + p*d_init*d_init);
            d = U128::from_integer(2)*q*c_init*d_init;
            c_init = (c*U128::from_integer(1000000))/d;
            d_init = U128::from_integer(1000000);
        }

        let numx: u32 = U128::to_integer(c_init);
        let fr = Fraction {
            sign: true,
            num: numx,
            den: 1000000,
        };
        fr  
    }
    
}


// an approximation of the Sine function using the Taylor series
// since pi is not "exactly" equal to 22/7, the results are only an approximation (4 decimal digits)
fn sin(x: Fraction) -> Fraction {
    let max = Fraction {
        sign: true,
        num: 44,
        den: 7,
    };
    assert (compareFraction(max, x) <= 1);
    assert (compareFraction(x, ZERO) <= 1);
    let mut f = x;
    let mut flag = true;
    let quart = Fraction {
        sign: true,
        num: 11,
        den: 7,
    };
    let mid = Fraction {
        sign: true,
        num: 22,
        den: 7,
    };
    let th_quart = Fraction {
        sign: true,
        num: 33,
        den: 7,
    };
    if (compareFraction(max, x) <= 1){
        f = subtractFraction(max, x);
        flag = false;
    }
    if (compareFraction(th_quart, x) <= 1){
        let f2 = subtractFraction(th_quart, x);
        f = subtractFraction(quart, f2);
        flag = false;
    }
    if (compareFraction(mid, x) <= 1){
        f = subtractFraction(mid, x);
        flag = true;
    }
    if (compareFraction(quart, x) <= 1){
        f = x;
        flag = true;
    }
    let mut sum = ZERO;
    
    let t1 = f;
    let t2 = divideFraction(powerSmallFraction(f, 3), toFraction(true, 6, 1));
    let t3 = divideFraction(powerSmallFraction(f, 5), toFraction(true, 120, 1));
    let t4 = divideFraction(powerSmallFraction(f, 7), toFraction(true, 5040, 1));
    let t5 = divideFraction(powerSmallFraction(f, 9), toFraction(true, 362880, 1));

    let s1 = addFraction(addFraction(t3, t5), t1);
    let s2 = addFraction(t2, t4);

    sum = subtractFraction(s1, s2);

    

    if (flag != sum.sign) {
        sum = signChangeFraction(sum);
    }
    if sum.num == 0 {
        sum.sign = true;
    }
    sum
}


// an approximation of the Cosine function using the Taylor series
// since pi is not "exactly" equal to 22/7, the results are only an approximation (4 decimal digits)
fn cos(x: Fraction) -> Fraction {
    let max = Fraction {
        sign: true,
        num: 44,
        den: 7,
    };
    assert (compareFraction(max, x) <= 1);
    assert (compareFraction(x, ZERO) <= 1);
    let mut f = x;
    let mut flag = true;
    let quart = Fraction {
        sign: true,
        num: 11,
        den: 7,
    };
    let mid = Fraction {
        sign: true,
        num: 22,
        den: 7,
    };
    let th_quart = Fraction {
        sign: true,
        num: 33,
        den: 7,
    };
    if (compareFraction(max, x) <= 1){
        f = subtractFraction(max, x);
        flag = true;
    }
    if (compareFraction(th_quart, x) <= 1){
        let f2 = subtractFraction(th_quart, x);
        f = subtractFraction(quart, f2);
        flag = false;
    }
    if (compareFraction(mid, x) <= 1){
        f = subtractFraction(mid, x);
        flag = false;
    }
    if (compareFraction(quart, x) <= 1){
        f = x;
        flag = true;
    }
    
    let mut sum = ONE;
   
    let t1 = toFraction(true, 1, 1);
    let t2 = divideFraction(powerSmallFraction(f, 2), toFraction(true, 2, 1));
    let t3 = divideFraction(powerSmallFraction(f, 4), toFraction(true, 24, 1));
    let t4 = divideFraction(powerSmallFraction(f, 6), toFraction(true, 720, 1));
    let t5 = divideFraction(powerSmallFraction(f, 8), toFraction(true, 40320, 1));

    let s1 = addFraction(addFraction(t3, t1), t5);
    let s2 = addFraction(t2, t4);

    sum = subtractFraction(s1, s2);

    
    
    if (flag != sum.sign){
        sum = signChangeFraction(sum);
    }
    if sum.num == 0 {
        sum.sign = true;
    }
    sum
}


#[test]
fn test_sum() {
    let f1 = toFraction(true, 3, 5);
    let f2 = toFraction(true, 2, 5);
    let f = addFraction(f1, f2);
    assert (f.num == f.den);
}

#[test]
fn test_sum_negative() {
    let f1 = toFraction(true, 3, 5);
    let f2 = toFraction(false, 1, 5);
    let f = addFraction(f1, f2);
    let cmp = compareFraction(f, toFraction(true, 2,5));
    assert (cmp == 0);
    
}

#[test]
fn test_diff() {
    let f1 = toFraction(true, 3, 5);
    let f2 = toFraction(true, 2, 5);
    let f = subtractFraction(f1, f2);
    let cmp = compareFraction(f, toFraction(true, 1,5));
    assert (cmp == 0);
    
}

#[test]
fn test_mul() {
    let f1 = toFraction(true, 1, 5);
    let f2 = toFraction(true, 5, 1);
    let f = multiplyFraction(f1, f2);
    assert (f.num == f.den);
}

#[test]
fn test_inv() {
    let f1 = toFraction(false, 1, 5);
    let f2 = invertFraction(f1);
    let f = multiplyFraction(f1, f2);
    assert (f.num == f.den);
    
}


#[test]
fn test_div() {
    let f1 = toFraction(true, 6, 5);
    let f2 = toFraction(true, 5, 1);
    let f = divideFraction(f1, f2);
    assert (f.num == 6);
    assert (f.den == 25);
}

#[test]
fn test_not_integer() {
    let f1 = toFraction(false, 1, 5);
    
    let is_int = isInteger(f1);

    assert (!is_int);
    
}

#[test]
fn test_integer() {
    let f1 = toFraction(false, 10, 5);
    
    let is_int = isInteger(f1);

    assert (is_int);
    
}

#[test]
fn test_square() {
    let f1 = toFraction(true, 4, 5);
    
    let f = squareFraction(f1);

    assert (f.num == 16);
    
}

#[test]
fn test_cube() {
    let f1 = toFraction(false, 1, 5);
    
    let f = cubeFraction(f1);

    assert (f.num == 1);
    assert (f.den == 125);
    assert (!f.sign);
    
}

#[test]
fn test_compare() {
    let f1 = toFraction(true, 4, 5);
    let f2 = toFraction(true, 8, 10);
    let cmp = compareFraction(f1, f2);

    assert (cmp == 0);
    
}


#[test]
fn test_reduce() {
    let f1 = toFraction(true, 2, 10);
    let f2 = reduceFraction(f1);

    assert (f2.num == 1);
    
}

#[test]
fn test_zero_neutrality() {
    let f1 = toFraction(true, 0, 5);
    let f2 = toFraction(false, 0, 10);
    let cmp = compareFraction(f1, f2);

    assert (cmp == 0);
    
}

#[test]
fn test_floor() {
    let f = toFraction(true, 7, 5);
    let fl = floor(f);
    assert (fl.num == 1);
    assert (fl.den == 1);
}

#[test]
fn test_floor2() {
    let f = toFraction(false, 12, 5);
    let fl = floor(f);
    assert (fl.num == 3);
    assert (fl.den == 1);
}


#[test]
fn test_ceiling() {
    let f = toFraction(true, 7, 5);
    let ce = ceiling(f);
    assert (ce.num == 2);
    assert (ce.den == 1);
}

#[test]
fn test_ceiling2() {
    let f = toFraction(false, 12, 5);
    let ce = ceiling(f);
    assert (ce.num == 2);
    assert (ce.den == 1);
}

#[test]
fn test_globals() {
    let o = ONE;
    let no = NEGATIVE_ONE;
    let z = ZERO;
    let a = addFraction(o , no);
    assert (a.num == z.num);
}


#[test]
fn test_mul_large() {
    let f1 = toFraction(true, 33333333, 5);
    let f2 = toFraction(true, 500000, 77777);
    let m = multiplyFraction(f1, f2);
    
    let p = m.num;
    let q = m.den;
    let lm = p/q;
    assert (lm == 42857571);
    
}


#[test]
fn test_add_large() {
    let f1 = toFraction(true, 33333333, 5);
    let f2 = toFraction(true, 500000, 33333333);
    let a = addFraction(f1, f2);
    
    assert (compareFraction(floor(a), MAX) == 2);
}


#[test]
fn test_sin() {
    let f1 = toFraction(true, 11, 7);
    let res = sin(f1);
    
    let p = res.num;
    let q = res.den;
    
    let sig = res.sign;
    let mut fl = 0;
    if sig{
        fl = 1;
    }

    
    assert (fl == 1);
    assert (compareFraction(toFraction(true, 1,1), res) <= 1); 
}

#[test]
fn test_cos() {
    let f1 = toFraction(true, 3141, 2000);
    let res = cos(f1);

    let sig = res.sign;
    let mut fl = 0;
    if sig{
        fl = 1;
    }
    
    assert (fl == 1);
    let m = res.num;
    let n = res.den;
    assert (compareFraction(toFraction(true, 5, 10000), res) != 2);
    
}

#[test]
fn test_sqrt1(){
    let f1 = toFraction(true, 3, 8);
    let sqrt = sqrt(f1, 10);
    let delta = subtractFraction(f1, squareFraction(sqrt));
    let epsilon = Fraction {
        sign: true,
        num: 1,
        den: 1000,
    };
    if !delta.sign {
        assert (compareFraction(epsilon, signChangeFraction(delta)) <= 1);
    }
    else {
        assert (compareFraction(epsilon, delta) <= 1);
    }
    
}

#[test]
fn test_sqrt2(){
    let f1 = toFraction(true, 9999999, 444);
    let sqrt = sqrt(f1, 15);
    let delta = subtractFraction(f1, squareFraction(sqrt));
    let epsilon = Fraction {
        sign: true,
        num: 1,
        den: 1000,
    };
    if !delta.sign {
        assert (compareFraction(epsilon, signChangeFraction(delta)) <= 1);
    }
    else {
        assert (compareFraction(epsilon, delta) <= 1);
    }
    
}
