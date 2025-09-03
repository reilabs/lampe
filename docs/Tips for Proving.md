# Tips for Proving

This document contains some tips for stating and proving theorems about extracted Noir code, and
aims to be a compendium of useful patterns and knowledge.

## Existing Logic Over Custom Logic

> If you can write a piece of logic using existing Lean functionality, do so.

It is always possible to state program properties in Lean in terms of hand-written logic—such as
`if`, `match`, and so on—when stating theorems. However, if there is an equivalent to that logic in
terms of existing types and/or functionality it should always be preferred. This means that
downstream dependents of that theorem will have as much of the existing set of Lean theorems at 
their disposal as is possible, rather than having to manually work with the constructs.

An example would be the post-condition for `std::option::Option::map_or`. Using bare, hand-written
logic, it could be stated as follows:

```lean
fun r => r = match v with
| some x => f x
| none => default
```

This would mean that a user of the theorem would have to deal with that match explicitly every
single time it was employed. Alternatively, this can be stated in terms of operations on `Option`.

```lean
fun r => r = (v.map f).getD default
```

Constructs such as `Option.map` and `Option.getD` all have significant existing bodies of theorems
accompanying them, and are hence _much_ more useful in a theorem statement.

## Reason About Lean Types

> Wherever possible, translate the problem statement to be in terms of _Lean_ types and functions
> instead of Noir ones.

One of the major aims of Lampe is to avoid the need to reason directly about _Noir_ constructs and
types. Lean constructs have a significant base of theorems and work available with them, that does
not exist when directly reasoning about Noir's constructs.

