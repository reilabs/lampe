use std::default::Default;

pub fn my_func3(a: u8) -> u8 {
    my_func(a)
}

pub fn my_func(a: u8) -> u8 {
    a + 1
}

pub fn my_func2(arr: [u8; 8], b: u32) -> u8 {
    arr[b]
}

pub fn get_unchecked<T>(a: Option2<T>) -> T {
    a._value
}

pub fn my_fn() -> u8 {
    1 + 1
}

pub fn cast_test(a: u8) -> u64 {
    if a == 0 {
        0
    } else {
        a as u64
    }
}

pub fn tuple_test(a: u8) -> (u8, u8) {
    let _b = |c| c + a + 10;
    (a, a)
}

pub fn literal_test() -> () {
    let _a = 1;
    let b = true;
    let _c = false;
    let _d = [1; 5];
    let _e = &[1; 5];
    let _f = [1, 2, 3];
    let _h = "asdf";
    let _i = f"${b}";
}

pub fn assigns(x: u8) {
    let mut y = 3;
    y += x;

    let mut arr = [1, 2];
    arr[0] = 10;
}

pub unconstrained fn uncons(x: u8) {
    for i in 0..x {
        if i == 2 {
            continue;
        }

        if i == 5 {
            break;
        }
    }
}

pub fn check(x: u8) {
    assert(x == 5);
}

pub struct Option2<T> {
    _is_some: bool,
    _value: T,
}

impl<T> Default for Option2<T> {
    fn default() -> Self {
        Option2::none()
    }
}

impl<T> Option2<T> {
    /// Constructs a None value
    pub fn none() -> Self {
        Self { _is_some: false, _value: std::mem::zeroed() }
    }

    /// Constructs a Some wrapper around the given value
    pub fn some(_value: T) -> Self {
        Self { _is_some: true, _value }
    }

    /// True if this Option is None
    pub fn is_none(self) -> bool {
        !self.is_some()
    }

    /// True if this Option is Some
    pub fn is_some(self) -> bool {
        self._is_some
    }
}

pub trait MyTrait {
    fn foo(self) -> Self {
        self
    }
}

impl<T> MyTrait for Option2<T> {
    fn foo(self) -> Self {
        self
    }
}

impl<T> MyTrait for (T, bool)
where
    T: MyTrait,
{
    fn foo(self) -> Self {
        self
    }
}

pub fn string_test() -> str<5> {
    let x: str<5> = "Hello";
    x
}

pub fn fmtstr_test(x: Field, y: Field) -> Field {
    assert(x != y);
    let _a: fmtstr<37, (Field, Field)> = f"this is first:{x}  this is second:{y}";
    x + y
}

pub type AliasedOpt<T> = Option2<T>;

pub fn is_alias_some<T>(x: AliasedOpt<T>) -> bool {
    x.is_some()
}

pub fn main() {
    let mut op1 = Option2::some(5);
    let op2 = Option2::default();
    let _op3 = if true { op1 } else { op2 }.foo();
    let _ = op1.is_some();
    let mut l = [1, 2, 3];
    let _ = l[0];
    let t = (1, true, 3);
    let _ = t.2;
    l[1] = 4;
    op1._is_some = false;
    let mut tpl = (1, true);
    tpl.0 = 2;
}
