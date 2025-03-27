struct Option2<T> {
    _is_some: bool,
    _value: T,
}

impl <T> Option2<T> {
    /// Constructs a Some wrapper around the given value
    pub fn some(_value: T) -> Self {
       Self { _is_some: true, _value }
    }
}

fn pattern_test() {
    let opt = Option2::some(true);
    let t = (1, opt, 3);
    let (x, mut Option2 { _is_some, _value }, mut z) = t;
    let lam = |(x, mut y, z) : (bool, bool, bool), k : Field| -> bool {
        x
    };
}
