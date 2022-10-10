.. FILE      : Examples/Structures.lagda.rst
.. DATE      : 18 Jun 2022
.. UPDATED   : 18 Jun 2022

.. _examples-of-structures:

Examples of Structures
----------------------

This is the `Examples.Structures`_ module of the `Agda Universal Algebra Library`_.

.. toctree::
   :maxdepth: 2

   Structures/Signatures
   Structures/Basic


::

  {-# OPTIONS --without-K --exact-split --safe #-}

  module Examples.Structures where

   open import Examples.Structures.Signatures  public
   open import Examples.Structures.Basic       public

