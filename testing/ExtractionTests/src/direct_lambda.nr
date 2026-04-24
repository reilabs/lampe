pub fn direct_lambda_call() -> Field {
    (|x, y| x + y)(1, 2)
}

pub fn call_from_array() -> u32 {
    let lambdas = [|x| x + 1];
    lambdas[0](1)
}

pub fn two_indirect_calls() -> u32 {
    let lambdas = [|x| x + 1, |x| x + 2];
    lambdas[0](1) + lambdas[1](2)
}
