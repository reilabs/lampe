struct Option1<T> {
    is_some: bool,
    value: T,
}

struct Option2<T> {
    is_some: bool,
    value: T,
}

impl<T> Option2<T> {
    /// Constructs a Some wrapper around the given value
    pub fn some(value: T) -> Self {
        Self { is_some: true, value }
    }
}

fn pattern_test() {
    let opt = Option2::some(true);
    let t = (1, opt, 3);
    let (x, mut Option2 { is_some, value }, mut z) = t;
    let lam = |(x, mut y, z): (bool, bool, bool), k: Field| -> bool { x };
}
