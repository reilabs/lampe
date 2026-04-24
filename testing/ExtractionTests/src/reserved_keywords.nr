fn foo(from: u32) -> u32 {
    from + 1
}

pub fn reserved_keyword_test() -> u32 {
    let fun = foo;
    fun(0)
}
