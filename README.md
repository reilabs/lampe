# Lampe

> Lampe (/lɑ̃p/), a light to illuminate the darkness

This project contains a model of [Noir's](https://noir-lang.org) semantics in the
[Lean](https://lean-lang.org) programming language and theorem prover. The aim is to support the
formal verification of both the Noir language semantics and the properties of programs written in
Noir.

## Building

In order to build this you will need to clone the Reilabs [fork](https://github.com/reilabs/noir) of
the Noir repo next to the clone of this repo. In other words, if you have this repository at
`reilabs/lampe`, then that fork needs to be at `reilabs/noir`. You will also need to check out the
`lampe-v1.0.0-beta.1` branch in the `noir` repo. This will allow the Rust project to build.

The Lean project should build on its own.
