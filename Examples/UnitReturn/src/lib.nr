fn foo() {
    let x = 3;
}

fn bar() {
    let mut x = 3;
    x = 4;
}

fn baz() {
    let x = 3;
    bar();
}
