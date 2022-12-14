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

  open import Agda.Primitive         using () renaming ( lzero to āā )
  open import Data.Unit.Base         using () renaming ( ā¤ to š ; tt to š )
  open import Data.Empty             using () renaming ( ā„ to š )
  open import Overture               using ( š ; š )
  open import Base.Structures.Basic  using ( signature ; structure )


The signature with no symbols (used for, e.g., sets).

::

  Sā : signature āā āā
  Sā = record { symbol = š ; arity = Ī» () }

The signature with one nullary symbol (used for, e.g., pointed sets).

::

  S1 : signature āā āā
  S1 = record { symbol = š ; arity = Ī» _ ā š }

The signature with one unary symbol.

::

  S01 : signature āā āā
  S01 = record { symbol = š ; arity = Ī» _ ā š }

The signature with one binary symbol (used for, e.g., magmas, or semigroups, or semilattices).

::

  S001 : signature āā āā
  S001 = record { symbol = š ; arity = Ī» _ ā š }

The signature with one ternary symbol (used for, e.g., a boolean NAE-3-SAT relational structure).

::

  S0001 : signature āā āā
  S0001 = record { symbol = š ; arity = Ī» _ ā š }

The signature with 0 nullary, 2 unary, and 1 binary symbol.

::

  S021 : signature āā āā
  S021 = record { symbol = š ; arity = Ī»{ š.š ā š ; š.š ā š ; š.š ā š } }

The signature with one nullary and one binary (used for, e.g., monoids).

::

  S101 : signature āā āā
  S101 = record { symbol = š ; arity = Ī»{ š.š ā š ; š.š ā š } }

The signature with one nullary, one unary, and one binary (used for, e.g., groups).

::

  S111 : signature āā āā
  S111 = record { symbol = š ; arity = Ī»{ š.š ā š ; š.š ā š ; š.š ā š } }

