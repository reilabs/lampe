use std::default::Default;

fn my_func3(a: u8) -> u8 {
    my_func(a)
}

fn my_func(a: u8) -> u8 {
    a + 1
}

fn my_func2(arr: [u8; 8], b: u8) -> u8 {
    arr[b]
}

fn get_unchecked<T>(a: Option2<T>) -> T {
    a._value
}

fn my_fn() -> u8 {
    1 + 1
}

fn cast_test(a: u8) -> u64 {
    if a == 0 {
        0
    } else {
        a as u64
    }
}

fn tuple_test(a: u8) -> (u8, u8) {
    let b = |c| c + a + 10;
    (a, a)
}

fn literal_test() -> () {
    let a = 1;
    let b = true;
    let c = false;
    let d = [1; 5];
    let e = &[1; 5];
    let f = [1, 2, 3];
    let h = "asdf";
    let i = f"${b}";
}

fn assigns(x: u8) {
    let mut y = 3;
    y += x;

    let mut arr = [1, 2];
    arr[0] = 10;
}

unconstrained fn uncons(x: u8) {
    for i in 0..x {
        if i == 2 {
            continue;
        }

        if i == 5 {
            break;
        }
    }
}

fn check(x: u8) {
    assert(x == 5);
}

struct Option2<T> {
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

trait MyTrait {
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

fn string_test() -> str<5> {
    let x: str<5> = "Hello";
    x
}

fn fmtstr_test(x: Field, y: Field) -> Field {
    assert(x != y);
    let _a: fmtstr<37, (Field, Field)> = f"this is first:{x}  this is second:{y}";
    x + y
}

type AliasedOpt<T> = Option2<T>;

fn is_alias_some<T>(x: AliasedOpt<T>) -> bool {
    x.is_some()
}

fn main() {
    let mut op1 = Option2::some(5);
    let op2 = Option2::default();
    let op3 = if true { op1 } else { op2 }.foo();
    op1.is_some();
    let mut l = [1, 2, 3];
    l[0];
    let t = (1, true, 3);
    t.2;
    l[1] = 4;
    op1._is_some = false;
    let mut tpl = (1, true);
    tpl.0 = 2;
}
