# The Noir Standard Library

The Noir [Standard Library](https://github.com/noir-lang/noir/tree/master/noir_stdlib) (stdlib) is a
collection of code that is automatically made available to all Noir programs. This availability is
either from the [prelude](https://github.com/noir-lang/noir/blob/master/noir_stdlib/src/prelude.nr),
which is automatically imported into every module, or from direct imports. This means that every
Noir crate depends on it, and hence that it becomes part of the verification surface for an
arbitrary crate. To that end, it is very important that Lampe have theorems for the standard library
that can be used to prove properties of code that _uses_ the stdlib. 

This extraction of the standard library (and its accompanying theorems) is automatically made
available to any extracted project. As a user, you can import the files containing the theorems (and
the definitions) that you need, just like you would import from the standard library in your Noir
code.

## Structure

Lampe's copy of the standard library follows the same structure as is the default for any extracted
project. For a detailed description of this structure, see the documentation on the
[extracted project structure](../docs/Extracted Project Structure.md). The extracted `lampe`
directory is located right next to the `src` directory of the standard library project.

For the stdlib, the theorems—along with the corresponding re-exported definitions—are available
under `<std-version>.Stdlib.Mod`, for the file that corresponds to `mod.nr`. The definitions are
in the namespace `Lampe.Stdlib`.

## Versioning

Each version of the `lampe` CLI tool works with a single version of the Noir compiler. This means,
in addition, that it will default to extracting with a dependency on the _stdlib version_ that comes
with that compiler.

In order to interoperate with code written against different Noir versions—and hence different
stdlib versions—Lampe is properly equipped to work in projects with multiple versions of the stdlib
in its dependency tree.

