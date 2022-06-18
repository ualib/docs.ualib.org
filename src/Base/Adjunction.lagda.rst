.. FILE      : Base/Adjunction.lagda.rst
.. AUTHOR    : William DeMeo
.. DATE      : 30 Aug 2021
.. UPDATED   : 02 Jun 2022
.. COPYRIGHT : (c) 2022 Jacques Carette and William DeMeo

Adjunction
----------

This is the `Base.Adjunction`_ module of the `Agda Universal Algebra Library`_.

.. toctree::
   :maxdepth: 2

   Adjunction/Closure
   Adjunction/Galois
   Adjunction/Residuation

::

  {-# OPTIONS --without-K --exact-split --safe #-}

  module Base.Adjunction where

  open import Base.Adjunction.Closure      public
  open import Base.Adjunction.Galois       public
  open import Base.Adjunction.Residuation  public


