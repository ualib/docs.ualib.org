.. FILE      : Base/Structures/Terms.lagda.rst
.. DATE      : 26 Jul 2021
.. UPDATED   : 04 Jun 2022
.. COPYRIGHT : (c) 2022 Jacques Carette and William DeMeo

.. _interpretation-of-terms-in-general-structures:

Interpretation of Terms in General Structures
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

This is the `Base.Structures.Terms`_ module of the `Agda Universal Algebra Library`_.

When we interpret a term in a structure we call the resulting function a *term
operation*. Given a term ``p`` and a structure ``๐จ``, we denote by ``๐จ โฆ p โง`` the
*interpretation* of ``p`` in ``๐จ``. This is defined inductively as follows.

1. If ``p`` is a variable symbol ``x : X`` and if ``a : X โ โฃ ๐จ โฃ`` is a
   tuple of elements of ``โฃ ๐จ โฃ``, then define ``๐จ โฆ p โง a := a x``.

2. If ``p = f t``, where ``f : โฃ ๐ โฃ`` is an operation symbol, if
   ``t : (arity ๐น) f โ ๐ป X`` is a tuple of terms, and if
   ``a : X โ โฃ ๐จ โฃ`` is a tuple from ``๐จ``, then define
   ``๐จ โฆ p โง a := (f แต ๐จ) (ฮป i โ ๐จ โฆ t i โง a)``.

Thus interpretation of a term is defined by structural induction.

::

  {-# OPTIONS --without-K --exact-split --safe #-}

  module Base.Structures.Terms where

  -- Imports from Agda and the Agda Standard Library ---------------------
  open import Agda.Primitive         using ( lsuc ; _โ_ ; Level ) renaming ( Set to Type )
  open import Base.Structures.Basic  using ( signature ; structure ; _แต_ )
  open import Base.Terms.Basic

  private variable
   ๐โ ๐ฅโ ๐โ ๐ฅโ ฯ ฮฑ ฯ : Level
   ๐น : signature ๐โ ๐ฅโ
   ๐ : signature ๐โ ๐ฅโ
   X : Type ฯ

  open signature
  open structure

  _โฆ_โง : (๐จ : structure ๐น ๐ {ฮฑ} {ฯ}) โ Term X โ (X โ carrier ๐จ) โ carrier ๐จ
  ๐จ โฆ โ x โง = ฮป a โ a x
  ๐จ โฆ node f t โง = ฮป a โ (f แต ๐จ) (ฮป i โ (๐จ โฆ t i โง ) a)

--------------


