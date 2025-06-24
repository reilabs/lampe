# Examples

This directory contains examples for how to use [Lampe](../Lampe/) the Lean library to prove
properties of extracted Noir code. Each contains one or more Noir projects (conventionally
containing a `src` directory), with each project also containing a `lampe` directory with the
extracted program within.

The examples can be described as follows:

- `SimpleProject`: An extremely simple project containing a single Noir function and a proof of its
  behavior.

To run each example, we expect that you have followed the instructions in the [README](../README.md)
to build and install the `lampe` CLI tool. You can then:

1. **Extract:** Run `lampe` in the example directory to re-run the extraction process.
2. **Check the Theorems:** Move into the `lampe` subdirectory of the example and run `lake build` to
   check whether the theorems are correct

