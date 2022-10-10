.. FILE      : Examples/Structures/Signatures.lagda.rst
.. DATE      : 16 Jul 2021
.. UPDATED   : 04 Jun 2022

.. _examples-of-finite-signatures:

Examples of finite signatures
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

This is the `Examples.Structures.Signatures`_ module of the agda-algebras_ library.

::

  {-# OPTIONS --without-K --exact-split --safe #-}

  module Examples.Structures.Signatures where

  open import Agda.Primitive         using () renaming ( lzero to ℓ₀ )
  open import Data.Unit.Base         using () renaming ( ⊤ to 𝟙 ; tt to 𝟎 )
  open import Data.Empty             using () renaming ( ⊥ to 𝟘 )
  open import Overture               using ( 𝟚 ; 𝟛 )
  open import Base.Structures.Basic  using ( signature ; structure )


The signature with no symbols (used for, e.g., sets).

::

  S∅ : signature ℓ₀ ℓ₀
  S∅ = record { symbol = 𝟘 ; arity = λ () }

The signature with one nullary symbol (used for, e.g., pointed sets).

::

  S1 : signature ℓ₀ ℓ₀
  S1 = record { symbol = 𝟙 ; arity = λ _ → 𝟘 }

The signature with one unary symbol.

::

  S01 : signature ℓ₀ ℓ₀
  S01 = record { symbol = 𝟙 ; arity = λ _ → 𝟙 }

The signature with one binary symbol (used for, e.g., magmas, or semigroups, or semilattices).

::

  S001 : signature ℓ₀ ℓ₀
  S001 = record { symbol = 𝟙 ; arity = λ _ → 𝟚 }

The signature with one ternary symbol (used for, e.g., a boolean NAE-3-SAT relational structure).

::

  S0001 : signature ℓ₀ ℓ₀
  S0001 = record { symbol = 𝟙 ; arity = λ _ → 𝟛 }

The signature with 0 nullary, 2 unary, and 1 binary symbol.

::

  S021 : signature ℓ₀ ℓ₀
  S021 = record { symbol = 𝟛 ; arity = λ{ 𝟛.𝟎 → 𝟚 ; 𝟛.𝟏 → 𝟙 ; 𝟛.𝟐 → 𝟙 } }

The signature with one nullary and one binary (used for, e.g., monoids).

::

  S101 : signature ℓ₀ ℓ₀
  S101 = record { symbol = 𝟚 ; arity = λ{ 𝟚.𝟎 → 𝟘 ; 𝟚.𝟏 → 𝟚 } }

The signature with one nullary, one unary, and one binary (used for, e.g., groups).

::

  S111 : signature ℓ₀ ℓ₀
  S111 = record { symbol = 𝟛 ; arity = λ{ 𝟛.𝟎 → 𝟘 ; 𝟛.𝟏 → 𝟙 ; 𝟛.𝟐 → 𝟚 } }

