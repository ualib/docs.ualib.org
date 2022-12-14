.. FILE      : Setoid/Algebras/Basic.lagda.rst
.. AUTHOR    : William DeMeo
.. DATE      : 23 Apr 2021
.. UPDATED   : 23 Jun 2022

.. highlight:: agda
.. role:: code

.. _setoid-algebras-basic-definitions:

Basic definitions
~~~~~~~~~~~~~~~~~

This is the `Setoid.Algebras.Basic`_ module of the `Agda Universal Algebra Library`_.

::

  {-# OPTIONS --without-K --exact-split --safe #-}

  open import Overture using (π ; π₯ ; Signature )

  module Setoid.Algebras.Basic {π : Signature π π₯} where

  -- Imports from the Agda and the Agda Standard Library --------------------
  open import Agda.Primitive   using ( _β_ ; lsuc ) renaming ( Set to Type )
  open import Data.Product     using ( _,_ ; _Γ_ ; Ξ£-syntax )
  open import Function         using ( _β_ ; Func )
  open import Level            using ( Level )
  open import Relation.Binary  using ( Setoid ; IsEquivalence )

  open import Relation.Binary.PropositionalEquality as β‘ using ( _β‘_ ; refl )

  -- Imports from the Agda Universal Algebra Library ----------------------
  open import Overture    using ( β₯_β₯ ; β£_β£ )

  private variable Ξ± Ο ΞΉ : Level

  ov : Level β Level
  ov Ξ± = π β π₯ β lsuc Ξ±

Here we define algebras over a setoid, instead of a mere type with no equivalence on it.

(This approach is inspired by the one taken, e.g., by Andreas Abel in
his formalization Birkhoffβs completeness theorem; a `pdf is available
here <http://www.cse.chalmers.se/~abela/agda/MultiSortedAlgebra.pdf>`__.)

First we define an operator that translates an ordinary signature into a
signature over a setoid domain.

::

  open Setoid using (_β_ ; Carrier ) renaming  ( refl   to reflS
                                               ; sym    to symS
                                               ; trans  to transS
                                               ; isEquivalence to isEqv )

  open Func renaming ( f to _β¨$β©_ ; cong to βcong )


  EqArgs :  {π : Signature π π₯}{ΞΎ : Setoid Ξ± Ο}
   β        β{f g} β f β‘ g β (β₯ π β₯ f β Carrier ΞΎ) β (β₯ π β₯ g β Carrier ΞΎ) β Type _

  EqArgs {ΞΎ = ΞΎ} refl u v = β i β (_β_ ΞΎ) (u i) (v i)



  β¨_β© : Signature π π₯ β Setoid Ξ± Ο β Setoid _ _
  Carrier (β¨ π β© ΞΎ) = Ξ£[ f β β£ π β£ ] ((β₯ π β₯ f) β ΞΎ .Carrier)
  _β_ (β¨ π β© ΞΎ) (f , u) (g , v) = Ξ£[ eqv β f β‘ g ] EqArgs{ΞΎ = ΞΎ} eqv u v

  IsEquivalence.refl   (isEqv (β¨ π β© ΞΎ))                      = refl , Ξ» _ β reflS   ΞΎ
  IsEquivalence.sym    (isEqv (β¨ π β© ΞΎ))(refl , g)            = refl , Ξ» i β symS    ΞΎ (g i)
  IsEquivalence.trans  (isEqv (β¨ π β© ΞΎ))(refl , g)(refl , h)  = refl , Ξ» i β transS  ΞΎ (g i) (h i)

A setoid algebra is just like an algebra but we require that all basic operations
of the algebra respect the underlying setoid equality. The ``Func`` record packs a
function (``f``, aka apply, aka ``_β¨$β©_``) with a proof (cong) that the function respects
equality.

::

  record Algebra Ξ± Ο : Type (π β π₯ β lsuc (Ξ± β Ο)) where
   field
    Domain : Setoid Ξ± Ο
    Interp : Func (β¨ π β© Domain) Domain
     --      ^^^^^^^^^^^^^^^^^^^^^^^ is a record type with two fields:
     --       1. a function  f : Carrier (β¨ π β© Domain)  β Carrier Domain
     --       2. a proof cong : f Preserves _ββ_ βΆ _ββ_ (that f preserves the setoid equalities)
   -- Actually, we already have the following: (it's called "reflexive"; see Structures.IsEquivalence)
   β‘ββ : β{x}{y} β x β‘ y β (_β_ Domain) x y
   β‘ββ refl = Setoid.refl Domain

  open Algebra

The next three definitions are merely syntactic sugar, but they can be very useful
for improving readability of our code.

::

  π»[_] : Algebra Ξ± Ο β  Setoid Ξ± Ο
  π»[ π¨ ] = Domain π¨

  -- forgetful functor: returns the carrier of (the domain of) π¨, forgetting its structure
  π[_] : Algebra Ξ± Ο β  Type Ξ±
  π[ π¨ ] = Carrier π»[ π¨ ]

  -- interpretation of an operation symbol in an algebra
  _Μ_ : (f : β£ π β£)(π¨ : Algebra Ξ± Ο) β (β₯ π β₯ f  β  π[ π¨ ]) β π[ π¨ ]

  f Μ π¨ = Ξ» a β (Interp π¨) β¨$β© (f , a)

Sometimes we want to extract the universe level of a given algebra or its carrier.  The
following functions provide that information.

::

  -- The universe level of an algebra
  Level-of-Alg : {Ξ± Ο π π₯ : Level}{π : Signature π π₯} β Algebra Ξ± Ο β Level
  Level-of-Alg {Ξ± = Ξ±}{Ο}{π}{π₯} _ = π β π₯ β lsuc (Ξ± β Ο)

  -- The universe level of the carrier of an algebra
  Level-of-Carrier : {Ξ± Ο π π₯  : Level}{π : Signature π π₯} β Algebra Ξ± Ο β Level
  Level-of-Carrier {Ξ± = Ξ±} _ = Ξ±

.. _setoid-algebras-level-lifting-of-setoid-algebras:

Level lifting of setoid algebras
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

::

  module _ (π¨ : Algebra Ξ± Ο) where

   open Algebra π¨  using ( Interp )      renaming ( Domain to A )
   open Setoid A   using (sym ; trans )  renaming ( Carrier to β£Aβ£ ; _β_ to _ββ_ ; refl to reflβ )

   open Level


   Lift-AlgΛ‘ : (β : Level) β Algebra (Ξ± β β) Ο

   Domain (Lift-AlgΛ‘ β) = record  { Carrier = Lift β β£Aβ£
                                  ; _β_ = Ξ» x y β lower x ββ lower y
                                  ; isEquivalence = record  { refl = reflβ
                                                            ; sym = sym
                                                            ; trans = trans
                                                            }
                                  }

   Interp (Lift-AlgΛ‘ β) β¨$β© (f , la) = lift ((f Μ π¨) (lower β la))
   βcong (Interp (Lift-AlgΛ‘ β)) (refl , la=lb) = βcong (Interp π¨) ((refl , la=lb))

   Lift-AlgΚ³ : (β : Level) β Algebra Ξ± (Ο β β)
   Domain (Lift-AlgΚ³ β) =
    record  { Carrier = β£Aβ£
            ; _β_ = Ξ» x y β Lift β (x ββ y)
            ; isEquivalence = record  { refl = lift reflβ
                                      ; sym = Ξ» x β lift (sym (lower x))
                                      ; trans = Ξ» x y β lift (trans (lower x) (lower y))
                                      }
            }

   Interp (Lift-AlgΚ³ β ) β¨$β© (f , la) = (f Μ π¨) la
   βcong (Interp (Lift-AlgΚ³ β)) (refl , laβ‘lb) = lift (βcong (Interp π¨) (β‘.refl , Ξ» i β lower (laβ‘lb i)))

  Lift-Alg : (π¨ : Algebra Ξ± Ο)(ββ ββ : Level) β Algebra (Ξ± β ββ) (Ο β ββ)
  Lift-Alg π¨ ββ ββ = Lift-AlgΚ³ (Lift-AlgΛ‘ π¨ ββ) ββ
 
