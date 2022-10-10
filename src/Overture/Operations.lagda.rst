.. FILE      : Overture/Operations.lagda.rst
.. AUTHOR    : William DeMeo
.. DATE      : 17 Jun 2022

.. highlight:: agda
.. role:: code

.. _overture-operations:

Operations
----------

This is the `Overture.Operations`_ module of the `Agda Universal
Algebra Library`_.

For consistency and readability, we reserve two universe variables for
special purposes. The first of these is ``𝓞`` which we used in the
`Overture.Signatures`_ as the universe of the type of *operation
symbols* of a signature. The second is ``𝓥`` which we reserve for types
representing *arities* of relations or operations.

The type ``Op`` encodes the arity of an operation as an arbitrary type
``I : Type 𝓥``, which gives us a very general way to represent an
operation as a function type with domain ``I → A`` (the type of
"tuples") and codomain ``A``. For example, the ``I``-*ary projection
operations* on ``A`` are represented as inhabitants of the type
``Op I A`` as follows.

::

  {-# OPTIONS --without-K --exact-split --safe #-}

  module Overture.Operations where

  -- Imports from Agda and the Agda Standard Library -----------------------------
  open import Agda.Primitive               using () renaming ( Set to Type )
  open import Level                        using ( Level ; _⊔_ )

  private variable α β ρ 𝓥 : Level

  -- The type of operations on A of arity I
  Op : Type α → Type 𝓥 → Type (α ⊔ 𝓥)
  Op A I = (I → A) → A

  -- Example (projections)
  π : {I : Type 𝓥} {A : Type α } → I → Op A I
  π i x = x i

  -- return the arity of a given operation symbol
  arity[_] : {I : Type 𝓥} {A : Type α } → Op A I → Type 𝓥
  arity[_] {I = I} f = I
