.. FILE      : Base/Categories/Functors.lagda.rst
.. AUTHOR    : William DeMeo
.. DATE      : 30 Aug 2021
.. UPDATED   : 23 Jun 2022

.. highlight:: agda
.. role:: code

.. _base-categories-functors:

Functors
~~~~~~~~

This is the `Base.Categories.Functors`_ module of the `Agda Universal Algebra Library`_.

Recall, a *functor* ``F`` is a function that maps the objects and morphisms of one
category ``π`` to the objects and morphisms of a category ``π`` in such a way that
the following *functor laws* are satisfied:

-  ``β f g, F(f β g) = F(f) β F(g)``
-  ``β A, F(id A) = id (F A)`` (where ``id X`` denotes the identity morphism on ``X``)

.. _base-categories-polynomial-functors:

Polynomial functors
^^^^^^^^^^^^^^^^^^^

The main reference for this section is `Modular Type-Safety Proofs in
Agda <https://doi.org/10.1145/2428116.2428120>`__ by Schwaab and Siek (PLPV '07).

An important class of functors for our domain is the class of so called
*polynomial functors*. These are functors that are built up using the constant,
identity, sum, and product functors. To be precise, the actions of the latter on
objects are as follows: ``β A B`` (objects), ``β F G`` (functors),

-  ``const B A = B``
-  ``Id A = A``
-  ``(F + G) A = F A + G A``
-  ``(F Γ G) A = F A Γ G A``

::

  {-# OPTIONS --without-K --exact-split --safe #-}

  module Base.Categories.Functors where

  -- Imports from Agda and the Agda Standard Library  ---------------------------------------
  open import Agda.Primitive                         using ( _β_ ; lsuc ; Level )
                                                     renaming ( Set to Type ; lzero to ββ )
  open import Data.Nat                               using ( β ; zero ; suc ; _>_ )
  open import Data.Sum.Base                          using ( _β_ ) renaming ( injβ to inl ;  injβ to inr )
  open import Data.Product                           using ( Ξ£-syntax ; _,_ ; _Γ_ )
  open import Data.Unit                              using ( tt ) renaming ( β€ to β€β )
  open import Data.Unit.Polymorphic                  using ( β€ )
  open import Relation.Binary.PropositionalEquality  using ( _β‘_ ; refl ; _β’_ )
  open import Level

  private variable Ξ± Ξ² : Level

  infixl 6 _β_
  infixr 7 _β_

  data Functorβ : Type (lsuc ββ) where
   Id : Functorβ
   Const : Type β Functorβ
   _β_ : Functorβ β Functorβ β Functorβ
   _β_ : Functorβ β Functorβ β Functorβ

  [_]β : Functorβ β Type β Type
  [ Id ]β B = B
  [ Const C ]β B = C
  [ F β G ]β B = [ F ]β B β [ G ]β B
  [ F β G ]β B = [ F ]β B Γ [ G ]β B

  data Functor {β : Level} : Type (lsuc β) where
   Id : Functor
   Const : Type β β Functor
   _β_ : Functor{β} β Functor{β} β Functor
   _β_ : Functor{β} β Functor{β} β Functor

  [_]_ : Functor β Type Ξ± β Type Ξ±
  [ Id ] B = B
  [ Const C ] B = C
  [ F β G ] B = [ F ] B β [ G ] B
  [ F β G ] B = [ F ] B Γ [ G ] B

  {- from Mimram's talk (MFPS 2021):
  record Poly (I J : Type) : Type (lsuc ββ) where
   field
    Op : J β Type
    Pm : (i : I) β {j : J} β Op j β Type
  -}

The least fixed point of a polynomial function can then be defined in Agda_ with
the following datatype declaration.

::

  data ΞΌ_ (F : Functor) : Type where
   inn : [ F ] (ΞΌ F) β ΞΌ F

An important example is the polymorphic list datatype. The standard way to define
this in Agda_ is as follows:

::

  data list (A : Type) : Type ββ where
   [] : list A
   _β·_ : A β list A β list A

We could instead define a ``List`` datatype by applying ``ΞΌ`` to a polynomial
functor ``L`` as follows:

::

  L : {β : Level}(A : Type β) β Functor{β}
  L A = Const β€ β (Const A β Id)

  List : (A : Type) β Type ββ
  List A = ΞΌ (L A)

To see some examples demonstrating that both formulations of the polymorphic list
type give what we expect, see the `Examples.Categories.Functors`_ module. The
examples will use "getter" functions, which take a list ``l`` and a natural number
``n`` and return the element of ``l`` at index ``n``. (Since such an element doesn't
always exist, we first define the ``Option`` type.)

::

  data Option (A : Type) : Type where
   some : A β Option A
   none : Option A

  _[_] : {A : Type} β List A β β β Option A
  inn (inl x) [ n ] = none
  inn (inr (x , xs)) [ zero ] = some x
  inn (inr (x , xs)) [ suc n ] = xs [ n ]

  _β¦_β§ : {A : Type} β list A β β β Option A
  [] β¦ n β§ = none
  (x β· l) β¦ zero β§ = some x
  (x β· l) β¦ suc n β§ = l β¦ n β§


