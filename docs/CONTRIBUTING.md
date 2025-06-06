# Contributing

This document provides a brief introduction to how you can contribute to the Lampe project. We
welcome all kinds of contributions, whether they be code or otherwise. This repository is written in
a combination of [Rust](https://www.rust-lang.org), which is used for the extraction tooling that
turns Noir programs into definitions for use in theorem proving, and [Lean](https://lean-lang.org)
which we use to verify the properties of the extracted programs.

The two main components of this library are:

- The [`lampe`](../src/) CLI, which takes Noir programs and extracts them to Lean.
- The [Lampe](../Lampe/) library, which defines the semantics of the Noir programming language, and
  provides the machinery and tools used to formally verify Noir programs.

For instructions on getting set up and building the Lampe repository, please see the
[README](../README.md#Installation). It describes both installation and basic usage of the project.
If you are new to either Rust or Lean, please see the sections [New to Rust](#new-to-rust) and
[New to Lean](#new-to-lean) for some helpful getting-started information.

## Getting Your Work on `main`

For contributions this repository works on a [Pull Request](https://github.com/reilabs/lampe/pulls)
and subsequent review model, supported by CI to check that things avoid being broken. The process
works as follows:

1. If necessary, you fork the repository, but if you have access please create a branch.
2. You make your changes on that branch.
3. Pull-request that branch against `main`.
4. The pull request will be reviewed, and CI will run on it.
5. Once reviewers accept the code, and CI has passed, it will be merged to main!

## Testing

The tests for the Lampe project are broken up into multiple major components. These aim to provide
a comprehensive picture of the functioning of the Lampe project, and to ensure that we do not break
existing functionality as we develop it.

### Rust Tests

These are typical unit tests written inline in the modules of the Noir extraction codebase. They can
be found by browsing the [`src`](../src/) directory and ensure that the Rust code works as expected.

In order to run these tests, you currently need to increase the minimum stack size used by Rust. An
example for `bash`-compatible shells is as follows, but other shells may differ.

```bash
RUST_MIN_STACK=16777216 cargo test
```

### End to End Tests

Otherwise known as the "extraction tests", these tests consist of a [set](../testing/) of Noir
projects that contain constructs that we want to ensure should work. Each of these tests takes the
Noir project and extracts it to Lean code, and then this code is compiled to ensure that it does not
produce errors and that it has the correct output. Some of these E2E tests (such as the
[Merkle](../testing/Merkle/) one) feature theorems that have been proven about the Noir code.

These tests can be executed by using the `./testing/test.sh` script. See `./testing/test.sh -h`
for usage examples, but running the script without arguments will execute all of the tests. The
test script ensures that the extraction matches the committed extraction, to ensure that we are
not running into correct extractions that have nevertheless changed without our knowledge.

Each of these tests exists in its own directory, and consists of a single Noir project. The test
script also checks the directory for two special scripts to execute:

- `clean.sh`: This script is run _before_ the extraction process, and allows for running
  pre-extraction cleanup items.
- `user_actions.sh`: This script is run after extraction but before the Lean code is compiled, and
  exists to simulate user actions on the extracted project.

An example of both can be found in the [MerkleFromScratch](../testing/MerkleFromScratch) example.

To force a re-extraction (such as to update the project with expected changes), remove the `lampe`
directory of the example(s) in question and re-run the test script. The changes can then be added to
the repository. A small helper script for doing this is as follows:

```bash
find testing -mindepth 2 -maxdepth 2 | grep lampe | xargs rm -rf
```

### Noir Frontend Tests

We periodically run extraction on a set of examples that are used by the developers of the Noir
language as [test programs](https://github.com/noir-lang/noir/tree/master/test_programs). Currently
we see only that we can successfully extract and compile these programs, and do not prove any
theorems about them.

We operate on an [allow](../testing_noir/should_succeed) and [deny](../testing_noir/should_fail)
list system for these tests. These lists state which tests we expect to succeed and which we expect
to fail, so that we always observe if anything changes with regards to extraction failures. A test
expected to succeed failing is a test failure, but so is the success of a test expected to fail.

To execute these frontend tests, you must provide a local path to a clone of the Noir
[repository](https://github.com/noir-lang/noir) to the testing script. You can run a single test
using the `--test` flag, similarly to the [E2E](#end-to-end-tests) test script.

```bash
./testing_noir/test.sh --noir-path "/home/user/noir"
```

For more usage information, run `./testing_noir/test.sh -h` to get an idea of what additional flags
it supports.

## New to Rust

If you are new to working with Rust, a great place to start is the official
[Rust Book](https://doc.rust-lang.org/book/). It gives a great overview of the language and general
style. It's also worth getting familiar with the following tools:

- [Rustup](https://rustup.rs), the Rust toolchain installer.
- [Cargo](https://doc.rust-lang.org/cargo/), the Rust build tool and package manager.
- [docs.rs](https://docs.rs), a site providing up-to-date crate (package) documentation for all
  packages published to [crates.io](https://crates.io), the official package registry.
- [Rustdoc](https://doc.rust-lang.org/rustdoc/index.html), the ecosystem's official documentation
  tool.

In terms of development tooling, there are two major options in this space.

- [Rust Analyzer](https://rust-analyzer.github.io) is the official implementation of the
  [Language Server Protocol](https://microsoft.github.io/language-server-protocol/) for Rust, and
  will work with any LSP compatible host.
- [RustRover](https://www.jetbrains.com/rust/) is the fully-featured JetBrains IDE for working with
  Rust in single- and multi-language projects. The Rust support plugin can also run in other
  JetBrains IDEs if needed.

## New to Lean

If you are new to working with Lean, a great place to start is the official guide to
[functional programming with Lean](https://lean-lang.org/functional_programming_in_lean). It gives
an excellent overview of the language and general style. To work in Lampe you will also want to
understand the process of [theorem proving in Lean](https://lean-lang.org/theorem_proving_in_lean4)
as this is core to formally verifying Noir programs or working with the Lampe library itself. It's
also worth getting familiar with the following tools:

- [Elan](https://github.com/leanprover/elan), the Lean toolchain installer.
- [Lake](https://github.com/leanprover/lean4/blob/master/src/lake/README.md), the Lean build tool
  and package manager.

For development of Lean, there are two major options in this space:

- [VSCode Lean](https://github.com/leanprover/vscode-lean4), the officially-supported extension that
  provides a language server, highlighting, and an interactive infoview for helping prove theorems.
- [lean.nvim](https://github.com/Julian/lean.nvim), a Neovim extension that provides much of the
  same functionality as VSCode Lean, but is not officially supported.
- [lean4-mode](https://github.com/leanprover-community/lean4-mode), an Emacs major mode for editing
  Lean code, which can integrate with LSP-mode and provides a similar but more-limited infoview.

