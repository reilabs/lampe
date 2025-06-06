pub fn foo() {
    let _x = 3;
}

pub fn bar() {
    let mut x = 3;
    x = 4;
}

pub fn baz() {
    let _x = 3;
    bar();
}
