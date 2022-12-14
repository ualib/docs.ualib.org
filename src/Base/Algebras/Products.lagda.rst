.. FILE      : Base/Algebras/Products.lagda.rst
.. AUTHOR    : William DeMeo
.. DATE      : 03 Jun 2022
.. UPDATED   : 23 Jun 2022

.. highlight:: agda
.. role:: code

.. _base-algebras-products-of-algebras-and-product-algebras:

Products of Algebras and Product Algebras
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

This is the `Base.Algebras.Products`_ module of the `Agda Universal Algebra Library`_.

::

  {-# OPTIONS --without-K --exact-split --safe #-}

  open import Overture using ( ๐ ; ๐ฅ ; Signature )

  module Base.Algebras.Products {๐ : Signature ๐ ๐ฅ} where

  -- Imports from Agda and the Agda Standard Library ------------------------------
  open import Agda.Primitive  using ( lsuc ; _โ_ ; Level ) renaming ( Set to Type )
  open import Data.Product    using ( _,_ ; ฮฃ ; ฮฃ-syntax )
  open import Relation.Unary  using ( Pred ; _โ_ ; _โ_ )

  -- Imports from agda-algebras ---------------------------------------------------
  open import Overture                     using (_โปยน; ๐๐; โฃ_โฃ; โฅ_โฅ)
  open import Base.Algebras.Basic {๐ = ๐}  using ( Algebra ; _ฬ_ ; algebra )

  private variable ฮฑ ฮฒ ฯ ๐ : Level

From now on, the modules of the agda-algebras_ library will assume a fixed signature
``๐ : Signature ๐ ๐ฅ``.

Recall the informal definition of a *product* of ``๐``-algebras. Given a type
``I : Type ๐`` and a family ``๐ : I โ Algebra ฮฑ``, the *product* ``โจ ๐`` is
the algebra whose domain is the Cartesian product ``ฮ  ๐ ๊ I , โฃ ๐ ๐ โฃ`` of the
domains of the algebras in ``๐``, and whose operations are defined as follows:
if ``๐`` is a ``J``-ary operation symbol and if ``๐ : ฮ  ๐ ๊ I , J โ ๐ ๐`` is an
``I``-tuple of ``J``-tuples such that ``๐ ๐`` is a ``J``-tuple of elements of
``๐ ๐`` (for each ``๐``), then ``(๐ ฬ โจ ๐) ๐ := (i : I) โ (๐ ฬ ๐ i)(๐ i)``.

In the agda-algebras_ library a *product of* ``๐``-*algebras* is represented by
the following type.

::

  โจ : {I : Type ๐ }(๐ : I โ Algebra ฮฑ) โ Algebra (๐ โ ฮฑ)

  โจ {I = I} ๐ =  ( โ (i : I) โ โฃ ๐ i โฃ ) ,         -- domain of the product algebra
                  ฮป ๐ ๐ i โ (๐ ฬ ๐ i) ฮป x โ ๐ x i   -- basic operations of the product algebra

The type just defined is the one that will be used throughout the agda-algebras_
library whenever the product of an indexed collection of algebras (of type
``Algebra``) is required. However, for the sake of completeness, here is how one
could define a type representing the product of algebras inhabiting the record
type ``algebra``.

::

  open algebra

  โจ' : {I : Type ๐ }(๐ : I โ algebra ฮฑ) โ algebra (๐ โ ฮฑ)

  โจ' {I} ๐ = record  { carrier = โ i โ carrier (๐ i)                           -- domain
                      ; opsymbol = ฮป ๐ ๐ i โ (opsymbol (๐ i)) ๐ ฮป x โ ๐ x i }  -- basic operations

**Notation**. Given a signature ``๐ : Signature ๐ ๐ฅ``, the type ``Algebra ฮฑ``
has type ``Type(๐ โ ๐ฅ โ lsuc ฮฑ)``. Such types occur so often in the
agda-algebras_ library that we define the following shorthand for their universes.

::

  ov : Level โ Level
  ov ฮฑ = ๐ โ ๐ฅ โ lsuc ฮฑ

.. _base-algebras-products-of-classes-of-algebras:

Products of classes of algebras
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

An arbitrary class ``๐ฆ`` of algebras is represented as a predicate over the type
``Algebra ฮฑ``, for some universe level ``ฮฑ`` and signature ``๐``. That is, ``๐ฆ
: Pred (Algebra ฮฑ) ฮฒ``, for some type ``ฮฒ``. Later we will formally state and
prove that the product of all subalgebras of algebras in ``๐ฆ`` belongs to the
class ``SP(๐ฆ)`` of subalgebras of products of algebras in ``๐ฆ``. That is,
``โจ S(๐ฆ) โ SP(๐ฆ )``. This turns out to be a nontrivial exercise.

To begin, we need to define types that represent products over arbitrary
(nonindexed) families such as ``๐ฆ`` or ``S(๐ฆ)``. Observe that ``ฮ  ๐ฆ`` is
certainly not what we want. For recall that ``Pred (Algebra ฮฑ) ฮฒ`` is just an
alias for the function type ``Algebra ฮฑ โ Type ฮฒ``, and the semantics of the
latter takes ``๐ฆ ๐จ`` (and ``๐จ โ ๐ฆ``) to mean that ``๐จ`` belongs to the class
``๐ฆ``. Thus, by definition, 

.. code:: agda

   ฮ  ๐ฆ   :=   ฮ  ๐จ ๊ (Algebra ฮฑ) , ๐ฆ ๐จ   :=   โ (๐จ : Algebra ฮฑ) โ ๐จ โ ๐ฆ,

which asserts that every inhabitant of the type ``Algebra ฮฑ`` belongs to
``๐ฆ``. Evidently this is not the product algebra that we seek.

What we need is a type that serves to index the class ``๐ฆ``, and a function
``๐`` that maps an index to the inhabitant of ``๐ฆ`` at that index. But ``๐ฆ`` is
a predicate (of type ``(Algebra ฮฑ) โ Type ฮฒ``) and the type ``Algebra ฮฑ``
seems rather nebulous in that there is no natural indexing class with which to
โenumerateโ all inhabitants of ``Algebra ฮฑ`` belonging to ``๐ฆ``.

The solution is to essentially take ``๐ฆ`` itself to be the indexing type, at
least heuristically that is how one can view the type ``โ`` that we now define.

::

  module _ {๐ฆ : Pred (Algebra ฮฑ)(ov ฮฑ)} where
   โ : Type (ov ฮฑ)
   โ = ฮฃ[ ๐จ โ Algebra ฮฑ ] ๐จ โ ๐ฆ

Taking the product over the index type ``โ`` requires a function that maps an
index ``i : โ`` to the corresponding algebra. Each ``i : โ`` is a pair, ``(๐จ ,
p)``, where ``๐จ`` is an algebra and ``p`` is a proof that ``๐จ`` belongs to
``๐ฆ``, so the function mapping an index to the corresponding algebra is simply
the first projection.

::

   ๐ : โ โ Algebra ฮฑ
   ๐ i = โฃ i โฃ

Finally, we define ``class-product`` which represents the product of all members
of ๐ฆ.

::

   class-product : Algebra (ov ฮฑ)
   class-product = โจ ๐

If ``p : ๐จ โ ๐ฆ``, we view the pair ``(๐จ , p) โ โ`` as an *index* over the class,
so we can think of ``๐ (๐จ , p)`` (which is simply ``๐จ``) as the projection of
the product ``โจ ๐`` onto the ``(๐จ , p)``-th component.
