// Issue #266: direct calls to oracles from constrained code are auto-wrapped
// by Noir into unconstrained proxies post-monomorphization. Lampe operates
// on the elaborated AST (pre-monomorphization), so it must accept and handle
// these direct oracle calls.

pub fn use_oracles(x: Field) -> Field {
    let y =
        // Safety: testing oracle handling
        unsafe {
            foo(x)
        };
    let z =
        // Safety: testing oracle handling
        unsafe {
            bar()
        };
    y + z
}

#[oracle(foo_oracle)]
unconstrained fn foo(_x: Field) -> Field {}

#[oracle(bar_oracle)]
unconstrained fn bar() -> Field {}
