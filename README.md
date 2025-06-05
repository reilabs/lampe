# Lampe

> Lampe (/lɑ̃p/), a light to illuminate the darkness

This project contains a model of [Noir's](https://noir-lang.org) semantics in the
[Lean](https://lean-lang.org) programming language and theorem prover. The aim is to support the
formal verification of both the Noir language semantics and the properties of programs written in
Noir.

## Installation

Lampe is being installed by cloning repository and compiling its code. For that rust is required to be present on the
machine. To do so follow instructions on official rust website to install `rustup` tool [link](https://www.rust-lang.org/tools/install).

To install `lampe` cli standard `cargo install` command is used ([doc](https://doc.rust-lang.org/cargo/commands/cargo-install.html)). Then you can install specific rust version
used by lampe with command `rustup install`. Next steps are to download repository and install lampe with standard
`cargo install` command. To do so:

```bash
git clone https://github.com/reilabs/lampe
cd lampe
rustup install
cargo install
```

Now you should be able to call `lampe`. Next step is to install Lean to be able to run proofs. To do so follow
instructions on official Lean website [link](https://lean-lang.org/documentation/setup/). After that you are ready
to play with Lampe!

## Usage

Just go to your noir's project directory and then run `lampe` command.

Command help:

```bash
A utility to extract Noir code to Lean in order to enable the formal verification of Noir programs

Usage: lampe [OPTIONS]

Options:
      --root <PATH>  The root of the Noir project to extract [default: ./]
      --test-mode    Testing mode?
  -h, --help         Print help
```

It will generate `lampe` directory inside with generated code. The generated structure is:

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

For now, we do not yet defined flow for rerunning extraction on the project. The simplest option is to remove Extracted
directory as well as `lakefile.toml` and run `lampe` command again.

### Creating simple proof

Very simple example can be found in `examples/SimpleProject` directory. It defines very small Noir project with a small
`return_one` function that as name suggests returns `1`. In the project there is already generated Lampe project in
`lampe` directory. Main `SimpleProject-0.0.0.lean` file contains added (not generated) single proof that checks
if `return_one` function actually returns `1`.

```lean4
-- Passing proper env is very important as the struct contains inside
-- all extracted definitions from Noir project. Using wrong env may
-- result in errors that particular name cannot be found.
theorem t {lp}: STHoare lp «SimpleProject-0.0.0».Extracted.env (⟦⟧)
    («SimpleProject-0.0.0».Extracted.return_one.call h![] h![])
      fun output => output = (1 : Fp lp) := by -- here we define what we want to proof
  enter_decl
  simp only [«SimpleProject-0.0.0».Extracted.return_one]
  steps []
  subst_vars
  rfl
```

## Contributing

If you want to contribute code or documentation (non-code contributions are always welcome) to this
project, please take a look at our [contributing](./docs/CONTRIBUTING.md) documentation. It provides
an overview of how to get up and running, as well as what the contribution process looks like for
this repository.
