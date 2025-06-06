# Lampe

> Lampe (/lɑ̃p/), a light to illuminate the darkness

This project contains a model of [Noir's](https://noir-lang.org) semantics in the
[Lean](https://lean-lang.org) programming language and theorem prover. The aim is to support the
formal verification of both the Noir language semantics and the properties of programs written in
Noir.

## Installation

At the current time, Lampe can be installed by cloning this repository and building its code. In
order to do so you will need:

- **Rust:** Best installed via [rustup](https://www.rust-lang.org/tools/install) using the official
  instructions.
- **Lean:** Best installed via [elan](https://github.com/leanprover/elan) by following the
  instructions in the repository.

To install and test the `lampe` tool, please ensure that you have both Rust's `cargo` and Lean's
`lake` available on your path, and then perform the following steps.

1. **Clone the Repository:** You can clone the repository onto your local machine as follows. Use an
   HTTPS URL by default, but if you intend to contribute we recommend using an SSH remote instead.

   ```bash
   git clone https://github.com/reilabs/lampe lampe
   ```

2. **Set Up the Rust Version:** Enter the directory using `cd lampe` and run `rustup install` to set
   up the correct rust toolchain.

3. **Build the Lampe CLI:** Run `cargo install` to build the CLI and make it available on your path.

4. **Build the Lean Project:** While not strictly necessary at this stage, this will ensure that you
   have all the necessary dependencies and the correct lean toolchain. Please be aware that this
   build can take _a long time_ as the library and its dependencies are very complex.

   ```bash
   cd Lampe
   lake build
   ```

## Usage

At this stage you should be able to execute the `lampe` CLI, with the `lampe` command available on
your path.

1. **Find Your Project:** Start by entering the directory containing your Noir project. It should
   contain a `Nargo.toml` file and the standard project structure.
2. **Extract the Project:** You can run the `lampe` CLI with no arguments to extract a project in
   the current directory. For more detailed usage information of the CLI, run `lampe --help`.

Running this command will create a `lampe` directory in the same directory as your project,
containing the Lean code generated from extracting your Noir project. The generated code will follow
a structure similar to the below.

```
+- <package-name>-<package-version>-
|   |
|   +-- Extracted
|   |   |
|   |   +-- Dependencies
|   |   |   |
|   |   |   +-- Each dependency in own module
|   |   |
|   |   +-- Noir extracted code matching file paths as created by user in Noir project
|   |
|   +-- Here you should add your own Lean files
|
+-- <package-name>-<package-version>.lean
|
+-- lakefile.toml
|
+-- lean-toolchain
```

At the current time the `lampe` tool does not support re-running project extraction. If you want to
do so, please remove the `./lampe/Extracted` directory and re-run the `lampe` command.

### Creating a Simple Proof

Creating a proof of Noir code using Lampe involves using the theorem proving capabilities of the
[Lean](https://lean-lang.org) language. From a very high level, it involves stating _theorems_ about
the behavior of the Lean code, and then using _tactics_ to prove that these theorems actually do
hold. Teaching Lean is beyond the scope of this guide, but we recommend looking at
[Functional Programming in Lean](https://lean-lang.org/functional_programming_in_lean/) and
[Theorem Proving in Lean](https://lean-lang.org/theorem_proving_in_lean4/) as introductions to doing
such tasks.

A very simple example can be found in the `examples/SimpleProject` directory of this repository. It
defines a very small Noir project with a single function called `return_one` which does exactly what
its name suggests. In this project we have committed a pre-extracted Lampe project, which can be
found in the `lampe` subdirectory as described above.

By way of demonstration, we have included a small proof of a theorem that states that `return_one`
does indeed return the value `1`. You can view this proof in
[`SimpleProject-0.0.0.lean`](./Examples/SimpleProject/lampe/SimpleProject-0.0.0.lean), which is
commented to describe what it does.

## Contributing

If you would like to contribute code or documentation (non-code contributions are _always_ welcome)
to this repository, please take a look at our [contributing](./docs/CONTRIBUTING.md) documentation.
It provides an overview of how to get up and running, as well as what the contribution process looks
like for this repository.

