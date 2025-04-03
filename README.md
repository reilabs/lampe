# Lampe

> Lampe (/lɑ̃p/), a light to illuminate the darkness

This project contains a model of [Noir's](https://noir-lang.org) semantics in the
[Lean](https://lean-lang.org) programming language and theorem prover. The aim is to support the
formal verification of both the Noir language semantics and the properties of programs written in
Noir.

### Testing

To run rust tests you need to bump stack size. Use command:

```bash
RUST_MIN_STACK=16777216 cargo test
```