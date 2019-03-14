constraints-deriving
==================================
[![Build Status](https://secure.travis-ci.org/achirkin/constraints-deriving.svg)](http://travis-ci.org/achirkin/constraints-deriving)

This project is based on the [constraints](http://hackage.haskell.org/package/constraints) library.
Module `Data.Constraint.Deriving` provides a GHC Core compiler plugin that generates class instances.

The main goal of this project is to make possible a sort of ad-hoc polymorphism that I wanted to
implement in [easytensor](http://hackage.haskell.org/package/easytensor) for performance reasons:
an umbrella type unifies multiple specialized type family backend instances;
if the type instance is known, GHC picks a specialized (overlapping) class instance for a required function;
otherwise, GHC resorts to a unified (overlappable) instance that is defined for the whole type family.

To use the plugin, add
```Haskell
{-# OPTIONS_GHC -fplugin Data.Constraint.Deriving #-}
```
to the header of your module.
For debugging, add a plugin option `dump-instances`:
```Haskell
{-# OPTIONS_GHC -fplugin-opt Data.Constraint.Deriving:dump-instances #-}
```
to the header of your file; it will print all instances declared in the module (hand-written and auto-generated).
To enable much more verbose debug output, use library flag `dev` (for debugging the plugin itself).

Check out `example` folder for a motivating use case (enabled with flag `examples`).

The plugin is controlled via GHC annotations; there are two types of annotations corresponding to two plugin passes.
Both passes are core-to-core, which means the plugin runs after typechecker,
which in turn means **the generated class instances are available only outside of the module**.
A sort of inconvenience you may have experienced with template haskell 😉.

### DeriveAll

`DeriveAll` plugin pass inspects a newtype declaration.
To enable `DeriveAll` for a newtype `Foo`, add an annotation as follows:
```Haskell
{-# ANN type Foo DeriveAll #-}
newtype Foo a = ...
```
check out [`test/Spec/`](https://github.com/achirkin/constraints-deriving/tree/master/test/Spec) for [more examples](https://github.com/achirkin/constraints-deriving/blob/master/test/Spec/DeriveAll04.hs#L19-L20).

`DeriveAll` plugin pass looks through all possible type instances (in the presence of type families) of the base type,
and copies all class instances for the newtype wrapper.

Sometimes, you may need to refine the relation between the base type and the newtype;
you can do this via a special `type family DeriveContext newtype :: Constraint`.
By adding equality constraints, you can specify custom dependencies between type variables present in the newtype declaration
(e.g. [`test/Spec/DeriveAll01.hs`](https://github.com/achirkin/constraints-deriving/blob/master/test/Spec/DeriveAll01.hs#L24)).
By adding class constraints, you force these class constraints for all generated class instances
(e.g. in [`test/Spec/DeriveAll02.hs`](https://github.com/achirkin/constraints-deriving/blob/master/test/Spec/DeriveAll02.hs#L37)
 all class instances of `BazTy a b c d e f` have an additional constraint `Show e`).


Note, the internal machinery is different from `GeneralizedNewtypeDeriving` approach:
rather than coercing every function in the instance definition from the base type to the newtype,
it coerces the whole instance dictionary.


### ToInstance

`ToInstance` plugin pass converts a top-level `Ctx => Dict (Class t1..tn)` value declaration into
an instance of the form `instance Ctx => Class t1..tn`.
Thus, one can write arbitrary Haskell code (returning a class dictionary) to be executed every time
an instance is looked up by the GHC machinery.
To derive an instance this way, use  `ToInstance (x :: OverlapMode)` for a declaration, e.g. as follows:
```Haskell
newtype Foo t = Foo t

{-# ANN deriveEq (ToInstance NoOverlap) #-}
deriveEq :: Eq t => Dict (Eq (Foo t))
deriveEq = mapDict (unsafeDerive Foo) Dict

-- the result of the above is equal to
-- deriving instance Eq t => Eq (Foo t)
```
You can find a more meaningful example in [`test/Spec/ToInstance01.hs`](https://github.com/achirkin/constraints-deriving/blob/master/test/Spec/ToInstance01.hs#L45-L47) or
[`example/Lib/VecBackend.hs`](https://github.com/achirkin/constraints-deriving/blob/master/example/Lib/VecBackend.hs).

## Further work

One thing the `DeriveAll` pass misses is an option to blacklist some classes to avoid generating undesired instances.
Furthermore, its derivation mechanics currently may break functional dependencies (untested).
