pub struct Option1<T> {
    is_some: bool,
    value: T,
}

pub struct Option2<T> {
    is_some: bool,
    value: T,
}

impl<T> Option2<T> {
    /// Constructs a Some wrapper around the given value
    pub fn some(value: T) -> Self {
        Self { is_some: true, value }
    }
}

pub fn pattern_test() {
    let opt = Option2::some(true);
    let t = (1, opt, 3);
    let (_x, Option2 { is_some: _, value: _ }, mut _z) = t;
}
