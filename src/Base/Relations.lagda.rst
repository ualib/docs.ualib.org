.. FILE      : Base/Relations.lagda.rst
.. AUTHOR    : William DeMeo
.. DATE      : 02 Jun 2022
.. UPDATED   : 02 Jun 2022
.. COPYRIGHT : (c) 2022 William DeMeo

.. _relations:

Relations
---------

This is the `Base.Relations`_ module of the `Agda Universal Algebra Library`_.

In the `Base.Relations.Discrete`_ submodule we define types that represent
*unary* and *binary relations*, which we refer to as "discrete relations"
to contrast them with the ("continuous") *general* and *dependent relations*
that we introduce in `Base.Relations.Continuous`_. We call the latter
"continuous relations" because they can have arbitrary arity (general
relations) and they can be defined over arbitrary families of types
(dependent relations). Finally, in `Base.Relations.Quotients`_ we define
quotient types.

.. toctree::
   :maxdepth: 2

   Relations/Discrete
   Relations/Continuous
   Relations/Properties
   Relations/Quotients

::

  {-# OPTIONS --without-K --exact-split --safe #-}

  module Base.Relations where

  open import Base.Relations.Discrete    public
  open import Base.Relations.Continuous  public
  open import Base.Relations.Properties  public
  open import Base.Relations.Quotients   public

