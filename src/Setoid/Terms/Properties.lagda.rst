.. FILE      : Setoid/Terms/Properties.lagda.rst
.. AUTHOR    : William DeMeo
.. DATE      : 18 Sep 2021
.. UPDATED   : 23 Jun 2022

.. highlight:: agda
.. role:: code

.. _setoid-terms-properties-of-terms-on-setoids:

Properties of terms on setoids
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

This is the `Setoid.Terms.Properties`_ module of the `Agda Universal Algebra Library`_.

::

  {-# OPTIONS --without-K --exact-split --safe #-}

  open import Overture using (π ; π₯ ; Signature)

  module Setoid.Terms.Properties {π : Signature π π₯} where

  -- Imports from Agda and the Agda Standard Library ---------------------
  open import Agda.Primitive   using () renaming ( Set to Type )
  open import Data.Product     using ( _,_ )
  open import Function.Bundles using () renaming ( Func to _βΆ_ )
  open import Function.Base    using ( _β_ )
  open import Level            using ( Level )
  open import Relation.Binary  using ( Setoid )
  open import Relation.Binary.PropositionalEquality as β‘ using (_β‘_)
  import Relation.Binary.Reasoning.Setoid as SetoidReasoning

  -- Imports from the Agda Universal Algebra Library ----------------------------
  open import Overture          using ( β£_β£ ; β₯_β₯ )
  open import Setoid.Functions  using ( Img_β_ ; eq ; isSurj ; IsSurjective )
                                using ( isSurjβIsSurjective )

  open import Base.Terms            {π = π} using ( Term )
  open import Setoid.Algebras       {π = π} using ( Algebra ; π[_] ; _Μ_ )
  open import Setoid.Homomorphisms  {π = π} using ( hom ; compatible-map ; IsHom )
  open import Setoid.Terms.Basic    {π = π}  using ( π» ; _β_  ; β-isRefl )

  open Term
  open _βΆ_ using ( cong ) renaming ( f to _β¨$β©_ )

  private variable
   Ξ± Οα΅ Ξ² Οα΅ Ο Ο : Level
   X : Type Ο

The term algebra ``π» X`` is *absolutely free* (or *universal*, or
*initial*) for algebras in the signature ``π``. That is, for every
π-algebra ``π¨``, the following hold.

1.  Every function from ``π`` to ``β£ π¨ β£`` lifts to a homomorphism from
    ``π» X`` to ``π¨``.
2.  The homomorphism that exists by item 1 is unique.

We now prove this in [Agda][], starting with the fact that every map
from ``X`` to ``β£ π¨ β£`` lifts to a map from ``β£ π» X β£`` to ``β£ π¨ β£`` in
a natural way, by induction on the structure of the given term.

::

  module _ {π¨ : Algebra Ξ± Ο}(h : X β π[ π¨ ]) where
   open Algebra π¨      using ( Interp )                   renaming ( Domain to A )
   open Setoid A       using ( _β_ ; reflexive ; trans )  renaming ( Carrier to β£Aβ£ )
   open Algebra (π» X)  using ()                           renaming ( Domain to TX )
   open Setoid TX      using ()                           renaming ( Carrier to β£TXβ£ )

   free-lift : π[ π» X ] β π[ π¨ ]
   free-lift (β x) = h x
   free-lift (node f t) = (f Μ π¨) (Ξ» i β free-lift (t i))

   free-lift-of-surj-isSurj :  isSurj{π¨ = β‘.setoid X}{π© = A} h
    β                          isSurj{π¨ = TX}{π© = A} free-lift

   free-lift-of-surj-isSurj hE {y} = mp p
    where
    p : Img h β y
    p = hE
    mp : Img h β y β Img free-lift β y
    mp (eq a x) = eq (β a) x

   free-lift-func : TX βΆ A
   free-lift-func β¨$β© x = free-lift x
   cong free-lift-func = flcong
    where
    flcong : β {s t} β s β t β  free-lift s β free-lift t
    flcong (_β_.rfl x) = reflexive (β‘.cong h x)
    flcong (_β_.gnl x) = cong Interp (β‘.refl , (Ξ» i β flcong (x i)))

Naturally, at the base step of the induction, when the term has the form ``generator`` x,
the free lift of ``h`` agrees with ``h``. For the inductive step, when the given term has
the form ``node f t``, the free lift is defined as follows: Assuming (the induction
hypothesis) that we know the image of each subterm ``t i`` under the free lift of ``h``,
define the free lift at the full term by applying ``f Μ π¨`` to the images
of the subterms.

The free lift so defined is a homomorphism by construction. Indeed, here is the
trivial proof.

::

   lift-hom : hom (π» X) π¨
   lift-hom = free-lift-func , hhom
    where
    hfunc : TX βΆ A
    hfunc = free-lift-func

    hcomp : compatible-map (π» X) π¨ free-lift-func
    hcomp {f}{a} = cong Interp (β‘.refl , (Ξ» i β (cong free-lift-func){a i} β-isRefl))

    hhom : IsHom (π» X) π¨ hfunc
    hhom = record { compatible = Ξ»{f}{a} β hcomp{f}{a} }

If we further assume that each of the mappings from ``X`` to ``β£ π¨ β£``
is *surjective*, then the homomorphisms constructed with ``free-lift``
and ``lift-hom`` are *epimorphisms*, as we now prove.

::

   lift-of-epi-is-epi : isSurj{π¨ = β‘.setoid X}{π© = A} h β IsSurjective free-lift-func
   lift-of-epi-is-epi hE = isSurjβIsSurjective free-lift-func (free-lift-of-surj-isSurj hE)

Finally, we prove that the homomorphism is unique. Recall, when we proved this
in the module `Basic.Terms.Properties`_, we needed function extensionality.
Here, by using setoid equality, we can omit the ``swelldef`` hypothesis needed
previously to prove ``free-unique``.

::

  module _ {π¨ : Algebra Ξ± Ο}{gh hh : hom (π» X) π¨} where
   open Algebra π¨      using ( Interp )  renaming ( Domain to A )
   open Setoid A       using ( _β_ ; trans ; sym )
   open Algebra (π» X)  using ()          renaming ( Domain to TX )
   open _β_
   open IsHom

   private
    g = _β¨$β©_ β£ gh β£
    h = _β¨$β©_ β£ hh β£

   free-unique : (β x β g (β x) β h (β x)) β β (t : Term X) β  g t β h t
   free-unique p (β x) = p x
   free-unique p (node f t) = trans (trans geq lem3) (sym heq)
    where
    lem2 : β i β (g (t i)) β (h (t i))
    lem2 i = free-unique p (t i)

    lem3 : (f Μ π¨)(Ξ» i β (g (t i))) β (f Μ π¨)(Ξ» i β (h (t i)))
    lem3 = cong Interp (_β‘_.refl , lem2)

    geq : (g (node f t)) β (f Μ π¨)(Ξ» i β (g (t i)))
    geq = compatible β₯ gh β₯

    heq : h (node f t) β (f Μ π¨)(Ξ» i β h (t i))
    heq = compatible β₯ hh β₯

