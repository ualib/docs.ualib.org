.. FILE      : Base/Overture.lagda.rst
.. AUTHOR    : William DeMeo
.. DATE      : 02 Jun 2022
.. UPDATED   : 02 Jun 2022
.. COPYRIGHT : (c) 2022 William DeMeo

.. _overture:

Overture
--------

This is the `Base.Overture`_ module of the `Agda Universal Algebra Library`_.

The source code for this module comprises the (literate) Agda_ program that was used
to generate the html page displaying the sentence you are now reading. This source
code inhabits the file `Base/Overture.lagda.rst`_, which resides in the git repository
of the agda-algebras_ library.

.. toctree::
   :maxdepth: 2

   Overture/Preliminaries
   Overture/Inverses
   Overture/Injective
   Overture/Surjective
   Overture/Transformers
   
::

   {-# OPTIONS --without-K --exact-split --safe #-}

   module Base.Overture where

   open import Base.Overture.Preliminaries
   open import Base.Overture.Inverses
   open import Base.Overture.Injective
   open import Base.Overture.Surjective
   open import Base.Overture.Transformers


