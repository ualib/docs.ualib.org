.. FILE      : Base/Functions.lagda.rst
.. AUTHOR    : William DeMeo
.. DATE      : 02 Jun 2022
.. UPDATED   : 23 Jun 2022

.. highlight:: agda
.. role:: code

.. _base-functions:

Functions
---------

This is the `Base.Functions`_ module of the `Agda Universal Algebra Library`_.

The source code for this module comprises the (literate) Agda_ program that was used
to generate the html page displaying the sentence you are now reading. This source
code inhabits the file `Base/Functions.lagda.rst`_, which resides in the git repository
of the agda-algebras_ library.

.. toctree::
   :maxdepth: 2

   Functions/Inverses
   Functions/Injective
   Functions/Surjective
   Functions/Transformers

::

   {-# OPTIONS --without-K --exact-split --safe #-}

   module Base.Functions where

   open import Base.Functions.Inverses       public
   open import Base.Functions.Injective      public
   open import Base.Functions.Surjective     public
   open import Base.Functions.Transformers   public


