# The Noir Standard Library

The Noir [Standard Library](https://github.com/noir-lang/noir/tree/master/noir_stdlib) (stdlib) is a
collection of code that is automatically made available to all Noir programs. This availability is
either from the [prelude](https://github.com/noir-lang/noir/blob/master/noir_stdlib/src/prelude.nr),
which is automatically imported into every module, or from direct imports. This means that every
Noir crate depends on it, and hence that it becomes part of the verification surface for an
arbitrary crate. To that end, it is very important that Lampe provide theorems for the standard
library that can be used to prove properties of any code that _uses_ the stdlib.

This extraction of the standard library (and its accompanying theorems) is automatically made
available to any extracted project by being written as a dependency into the generated
`lakefile.toml`. As a user, you can import the files containing the theorems (and the definitions)
that you need, just like you would import from the standard library in your Noir code.

> ### Unconstrained Code
>
> The standard library contains functions that are marked as `unconstrained`. The property
> verification by Lampe cannot directly verify the behavior of these functions, and so they are
> extracted with an empty body.

## Structure

Lampe's copy of the standard library follows the same structure as is the default for any extracted
project. For a detailed description of this structure, see the documentation on the
[extracted project structure](../docs/Extracted Project Structure.md). The extracted `lampe`
directory is located right next to the `src` directory of the standard library project.

For the stdlib, the theorems—along with the corresponding re-exported definitions—are available
under `<std-version>.Stdlib.Mod`, for the file that corresponds to `mod.nr`. The definitions are
in the namespace `Lampe.Stdlib`. Note that not every file in the Noir stdlib has a corresponding
file in the Lampe stdlib; this is due to having no relevant extracted definitions.

For example, if you are proving properties of code that needs the definition of `Option<T>` along
with its theorems, you can simply `import <std-version>.Stdlib.Option` and then `open Lampe.Stdlib`
to make them available in your file. This will provide the type definition for `Option<T>` and the
definitions of all relevant functions and methods, along with any theorems.

Methods that are intended to be _internal_ (those that have names starting with `__`) are not
re-exported as they are not intended (by the Noir team) to be relied upon by user code. If you
really do need to prove a theorem involving such a definition, they can be imported directly from
the relevant file in the `<std-version>.Extracted` namespace.

## Versioning

Each version of the `lampe` CLI tool works with a single version of the Noir compiler. This means,
in addition, that it will default to extracting with a dependency on the _stdlib version_ that comes
with that compiler.

In order to interoperate with code written against different Noir versions—and hence different
stdlib versions—Lampe is properly equipped to work in projects with multiple versions of the stdlib
in its dependency tree. To that end, you may prove properties in terms of your standard library
version and constructs, while code you import may use a different version. This is perfectly fine,
as the theorems statements are usually in terms of _Lean_ constructs instead of Noir ones. 

If you _do_ need to import a different standard library version, you can add a separate dependency
and the namespaces including library versions will ensure that there are no name clashes unless you
open both standard library namespaces in one place. Under such circumstances, qualified names are
very helpful.

