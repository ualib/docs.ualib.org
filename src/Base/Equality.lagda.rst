.. FILE      : Base/Equality/index.rst
.. AUTHOR    : William DeMeo
.. DATE      : 03 Jun 2022
.. UPDATED   : 03 Jun 2022
.. COPYRIGHT : (c) 2022 William DeMeo

.. _equality:

Equality
--------

This is the `Base.Equality`_ module of the `Agda Universal Algebra Library`_.

::

  {-# OPTIONS --without-K --exact-split --safe #-}

  module Base.Equality where

  open import Base.Equality.Welldefined     public
  open import Base.Equality.Truncation      public
  open import Base.Equality.Extensionality  public

.. toctree::
   :maxdepth: 2

   Equality/Welldefined
   Equality/Truncation
   Equality/Extensionality

