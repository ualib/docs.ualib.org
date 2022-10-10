.. FILE      : Overture/Signatures.lagda.rst
.. AUTHOR    : William DeMeo
.. DATE      : 17 Jun 2022
.. UPDATE    : 23 Jun 2022

.. highlight:: agda
.. role:: code

.. _overture-signatures:

Signatures
----------

This is the `Overture.Signatures`_ module of the `Agda Universal Algebra Library`_.

As usual, we begin by importing some definitions from the `Agda Standard Library`_.

::

  {-# OPTIONS --without-K --exact-split --safe #-}

  module Overture.Signatures where

  -- Imports from the Agda (Builtin) and the Agda Standard Library -----------------------
  open import Agda.Primitive  using () renaming ( Set to  Type )
  open import Data.Product    using ( Σ-syntax )
  open import Level           using ( Level ; suc ; _⊔_ )

  variable 𝓞 𝓥 : Level

The variables 𝓞 and 𝓥 are not private since, throughout the agda-algebras_
library, 𝓞 denotes the universe level of *operation symbol* types, while 𝓥
denotes the universe level of *arity* types.


.. _overture-theoretical-background:

Theoretical background
~~~~~~~~~~~~~~~~~~~~~~

In `model theory <https://en.wikipedia.org/wiki/Model_theory>`__, the *signature*
𝑆 = (𝐶, 𝐹, 𝑅, ρ) of a structure consists of three (possibly empty) sets 𝐶, 𝐹, and
𝑅---called *constant symbols*, *function symbols*, and *relation symbols*,
respectively---along with a function ρ : 𝐶 + 𝐹 + 𝑅 → 𝑁 that assigns an *arity* to
each symbol. Often (but not always) 𝑁 = ℕ, the natural numbers.

As our focus here is universal algebra, we are more concerned with the restricted
notion of an *algebraic signature* (or *signature* for algebraic structures), by
which we mean a pair 𝑆 = (𝐹, ρ) consisting of a collection 𝐹 of *operation
symbols* and an *arity function* ρ : 𝐹 → 𝑁 that maps each operation symbol to its
arity; here, 𝑁 denotes the *arity type*. Heuristically, the arity ρ𝑓 of an
operation symbol 𝑓 ∈ 𝐹 may be thought of as the "number of arguments" that 𝑓 takes
as "input."

If the arity of 𝑓 is n, then we call 𝑓 an n-*ary* operation symbol. In case n is 0
(or 1 or 2 or 3, respectively) we call the function *nullary* (or *unary* or
*binary* or *ternary*, respectively).

If A is a set and 𝑓 is a ρ𝑓-ary operation on A, we often indicate this by writing
:math:`f : \mathrm{A}^{\rho f} → \mathrm{A}`. On the other hand, the arguments of such an
operation form a ρ𝑓-tuple, say, (a 0, a 1, …, a (ρ𝑓 - 1)), which may be viewed as
the graph of the function a : ρ𝑓 → A. When the codomain of ρ is ℕ, we may view ρ𝑓
as the finite set {0, 1, …, ρ𝑓 - 1}. Thus, by identifying :math:`\mathrm{A}^{\rho f}`, the
ρ𝑓-th power of A, with the type ρ𝑓 → A of functions from {0, 1, …, ρ𝑓 - 1} to A,
we identify the function type :math:`\mathrm{A}^{\rho f} → \mathrm{A}` with the function (or
"functional") type (ρ𝑓 → A) → A.

**Example**. Suppose 𝑔 : (m → A) → A is an m-ary operation on A, and 𝑎 : m → A is
an m-tuple on A. Then 𝑔 𝑎 may be viewed as 𝑔 (𝑎 0, 𝑎 1, …, 𝑎 (m-1)), which has
type A. Suppose further that 𝑓 : (ρ𝑓 → B) → B is a ρ𝑓-ary operation on B,
𝑎 : ρ𝑓 → A is a ρ𝑓-tuple on A, and ℎ : A → B is a function. Then the following
typing judgments obtain: ℎ ∘ 𝑎 : ρ𝑓 → B and 𝑓 (ℎ ∘ 𝑎) : B.

.. _overture-the-signature-type:

The signature type
~~~~~~~~~~~~~~~~~~

In the agda-algebras_ library we represent the *signature* of an algebraic
structure using the following type.

::

  Signature : (𝓞 𝓥 : Level) → Type (suc (𝓞 ⊔ 𝓥))
  Signature 𝓞 𝓥 = Σ[ F ∈ Type 𝓞 ] (F → Type 𝓥)

  Level-of-Signature : {𝓞 𝓥 : Level} → Signature 𝓞 𝓥 → Level
  Level-of-Signature {𝓞}{𝓥} _ = suc (𝓞 ⊔ 𝓥)

In the `Base.Functions`_ module of the agda-algebras_ library, special syntax is
defined for the first and second projections—namely, ∣_∣ and ∥_∥, resp.
Consequently, if 𝑆 : Signature 𝓞 𝓥 is a signature, then

-  ``∣ 𝑆 ∣`` denotes the set of operation symbols, and
-  ``∥ 𝑆 ∥`` denotes the arity function.

If 𝑓 : ∣ 𝑆 ∣ is an operation symbol in the signature 𝑆, then ∥ 𝑆 ∥ 𝑓 is the arity
of 𝑓.

