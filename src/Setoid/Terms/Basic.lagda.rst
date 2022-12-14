.. FILE      : Setoid/Terms/Basic.lagda.rst
.. AUTHOR    : William DeMeo
.. DATE      : 18 Sep 2021
.. UPDATED   : 18 Jun 2022

.. highlight:: agda
.. role:: code

.. _setoid-terms-basic-definitions:

Basic definitions
~~~~~~~~~~~~~~~~~

This is the `Setoid.Terms.Basic`_ module of the `Agda Universal Algebra Library`_.

::

  {-# OPTIONS --without-K --exact-split --safe #-}

  open import Overture using (π ; π₯ ; Signature)

  module Setoid.Terms.Basic {π : Signature π π₯} where

  -- imports from Agda and the Agda Standard Library -------------------------------
  open import Agda.Primitive         using () renaming ( Set to Type )
  open import Data.Empty.Polymorphic using ( β₯ )
  open import Data.Product           using ( _,_ )
  open import Data.Sum               using ( _β_ )
                                     renaming ( injβ to inl ; injβ to inr )
  open import Function               using () renaming ( Func to _βΆ_ )
  open import Level                  using ( Level ; Lift ; _β_ )
  open import Relation.Binary        using ( Setoid ; IsEquivalence )
                                     using ( Reflexive ; Symmetric ; Transitive )

  open import Relation.Binary.PropositionalEquality as β‘ using ( _β‘_ )

  -- Imports from the Agda Universal Algebra Library -------------------------------
  open import Overture using ( β₯_β₯ )
  open import Setoid.Algebras  {π = π}  using ( Algebra ; ov ; _Μ_)
  open import Base.Terms       {π = π}  using ( Term )

  open _βΆ_ renaming ( f to _β¨$β©_ )
  open Term

  private variable
   Ο Ξ± β : Level
   X Y : Type Ο


.. _setoid-terms-equality-of-terms:

Equality of terms
^^^^^^^^^^^^^^^^^

We take a different approach here, using Setoids instead of quotient
types. That is, we will define the collection of terms in a signature as
a setoid with a particular equality-of-terms relation, which we must
define. Ultimately we will use this to define the (absolutely free) term
algebra as a Algebra whose carrier is the setoid of terms.

::

  module _ {X : Type Ο } where

   -- Equality of terms as an inductive datatype
   data _β_ : Term X β Term X β Type (ov Ο) where
    rfl : {x y : X} β x β‘ y β (β x) β (β y)
    gnl : β {f}{s t : β₯ π β₯ f β Term X} β (β i β (s i) β (t i)) β (node f s) β (node f t)

   -- Equality of terms is an equivalence relation
   open Level
   β-isRefl : Reflexive _β_
   β-isRefl {β _} = rfl β‘.refl
   β-isRefl {node _ _} = gnl (Ξ» _ β β-isRefl)

   β-isSym : Symmetric _β_
   β-isSym (rfl x) = rfl (β‘.sym x)
   β-isSym (gnl x) = gnl (Ξ» i β β-isSym (x i))

   β-isTrans : Transitive _β_
   β-isTrans (rfl x) (rfl y) = rfl (β‘.trans x y)
   β-isTrans (gnl x) (gnl y) = gnl (Ξ» i β β-isTrans (x i) (y i))

   β-isEquiv : IsEquivalence _β_
   β-isEquiv = record { refl = β-isRefl ; sym = β-isSym ; trans = β-isTrans }

  TermSetoid : (X : Type Ο) β Setoid (ov Ο) (ov Ο)
  TermSetoid X = record { Carrier = Term X ; _β_ = _β_ ; isEquivalence = β-isEquiv }

  open Algebra

  -- The Term Algebra
  π» : (X : Type Ο) β Algebra (ov Ο) (ov Ο)
  Domain (π» X) = TermSetoid X
  Interp (π» X) β¨$β© (f , ts) = node f ts
  cong (Interp (π» X)) (β‘.refl , ssβts) = gnl ssβts

.. _setoid-terms-interpretation-of-terms-in-setoid-algebras:

Interpretation of terms in setoid algebras
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

The approach to terms and their interpretation in this module was inspired by
`Andreas Abelβs formal proof of Birkhoff's completeness
theorem <http://www.cse.chalmers.se/~abela/agda/MultiSortedAlgebra.pdf>`__.

A substitution from ``Ξ`` to ``Ξ`` associates a term in ``Ξ`` with each
variable in ``Ξ``.

::

  -- Parallel substitutions.
  Sub : Type Ο β Type Ο β Type (ov Ο)
  Sub X Y = (y : Y) β Term X

  -- Application of a substitution.
  _[_] : (t : Term Y) (Ο : Sub X Y) β Term X
  (β x) [ Ο ] = Ο x
  (node f ts) [ Ο ] = node f (Ξ» i β ts i [ Ο ])

An environment for ``Ξ`` maps each variable ``x : Ξ`` to an element of ``A``, and
equality of environments is defined pointwise.

::

  module Environment (π¨ : Algebra Ξ± β) where
   open Algebra π¨  renaming( Domain to A ; Interp  to InterpA )  using()
   open Setoid A   renaming( _β_ to _ββ_ ; Carrier to β£Aβ£ )      using( refl ; sym ; trans )

   Env : Type Ο β Setoid _ _
   Env X = record  { Carrier = X β β£Aβ£
                   ; _β_ = Ξ» Ο Ο' β (x : X) β Ο x ββ Ο' x
                   ; isEquivalence = record  { refl = Ξ» _ β refl
                                             ; sym = Ξ» h x β sym (h x)
                                             ; trans = Ξ» g h x β trans (g x) (h x)
                                             }
                   }

   open Algebra using ( Domain ; Interp )

   EnvAlgebra : Type Ο β Algebra (Ξ± β Ο) (β β Ο)
   Domain (EnvAlgebra X) = Env X
   (Interp (EnvAlgebra X) β¨$β© (f , aΟ)) x = (f Μ π¨) (Ξ» i β aΟ i x)
   cong (Interp (EnvAlgebra X)) {f , a} {.f , b} (β‘.refl , aibi) x = cong InterpA (β‘.refl , (Ξ» i β aibi i x))

Interpretation of terms is iteration on the W-type. The standard library
offers \`iterβ (on sets), but we need this to be a setoid function.

::

   β¦_β§ : {X : Type Ο}(t : Term X) β (Env X) βΆ A
   β¦ β x β§ β¨$β© Ο = Ο x
   β¦ node f args β§ β¨$β© Ο = InterpA β¨$β© (f , Ξ» i β β¦ args i β§ β¨$β© Ο)
   cong β¦ β x β§ uβv = uβv x
   cong β¦ node f args β§ xβy = cong InterpA (β‘.refl , Ξ» i β cong β¦ args i β§ xβy )

   open Setoid using () renaming ( Carrier to β£_β£ )

   -- An equality between two terms holds in a model
   -- if the two terms are equal under all valuations of their free variables.
   Equal : β {X : Type Ο} (s t : Term X) β Type _
   Equal {X = X} s t = β (Ο : β£ Env X β£) β  β¦ s β§ β¨$β© Ο ββ β¦ t β§ β¨$β© Ο

   ββEqual : {X : Type Ο}(s t : Term X) β s β t β Equal s t
   ββEqual .(β _) .(β _) (rfl β‘.refl) = Ξ» _ β refl
   ββEqual (node _ s)(node _ t)(gnl x) =
    Ξ» Ο β cong InterpA (β‘.refl , Ξ» i β ββEqual(s i)(t i)(x i)Ο )

   -- Equal is an equivalence relation.
   isEquiv : {Ξ : Type Ο} β IsEquivalence (Equal {X = Ξ})
   IsEquivalence.refl   isEquiv = Ξ» _ β refl
   IsEquivalence.sym    isEquiv = Ξ» x=y Ο β sym (x=y Ο)
   IsEquivalence.trans  isEquiv = Ξ» ij jk Ο β trans (ij Ο) (jk Ο)

   -- Evaluation of a substitution gives an environment.
   β¦_β§s : {X Y : Type Ο} β Sub X Y β β£ Env X β£ β β£ Env Y β£
   β¦ Ο β§s Ο x = β¦ Ο x β§ β¨$β© Ο

   -- Substitution lemma: β¦t[Ο]β§Ο β β¦tβ§β¦Οβ§Ο
   substitution :  {X Y : Type Ο} β (t : Term Y) (Ο : Sub X Y) (Ο : β£ Env X β£ )
    β              β¦ t [ Ο ] β§ β¨$β© Ο  ββ  β¦ t β§ β¨$β© (β¦ Ο β§s Ο)

   substitution (β x) Ο Ο = refl
   substitution (node f ts) Ο Ο = cong InterpA (β‘.refl , Ξ» i β substitution (ts i) Ο Ο)

