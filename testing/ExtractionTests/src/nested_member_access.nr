pub struct Inner {
    x: u32,
    y: u32,
}

pub struct Outer {
    inner: Inner,
    z: u32,
}

pub fn nested_field_access(o: Outer) -> u32 {
    o.inner.x
}

pub fn nested_field_access_second(o: Outer) -> u32 {
    o.inner.y
}

pub fn nested_field_assert() {
    let o = Outer { inner: Inner { x: 42, y: 99 }, z: 7 };
    assert(o.inner.x == 42);
    assert(o.inner.y == 99);
    assert(o.z == 7);
}
