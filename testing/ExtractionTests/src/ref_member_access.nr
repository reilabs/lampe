struct Foo {
    bar: Bar,
}
struct Bar {
    x: Field,
}

impl Bar {
    fn mutate(&mut self) {
        self.x = 42;
    }
}

pub fn ref_member_access() {
    let foo = &mut Foo { bar: Bar { x: 0 } };
    foo.bar.mutate();
    assert(foo.bar.x == 42);
}
