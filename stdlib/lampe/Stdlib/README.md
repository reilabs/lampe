# Stdlib

This directory contains the theorems that accompany the extracted version of the Noir standard
library. It also re-exports the corresponding definitions into the `Lampe.Stdlib` namespace so that
they are accessible to users without the need to also export modules from the `<..>/Extracted/<..>`
tree. In other words, if you want to work with the `Option<T>` type, it suffices to
`import <Std-Version>/Stdlib/Option` and then open the namespace `Lampe.Stdlib`
