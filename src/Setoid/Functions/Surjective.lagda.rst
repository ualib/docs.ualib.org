.. FILE      : Setoid/Functions/Surjective.lagda.rst
.. AUTHOR    : William DeMeo
.. DATE      : 13 Sep 2022
.. upDATE    : 23 Jun 2022

.. highlight:: agda
.. role:: code

.. _setoid-functions-surjective-setoid-functions:

Surjective setoid functions
~~~~~~~~~~~~~~~~~~~~~~~~~~~

This is the `Setoid.Functions.Surjective`_ module of the agda-algebras_ library.

Let ``π¨ = (A , ββ)`` and ``π© = (B , ββ)`` be setoids.  A *surjective setoid
function* from ``π¨`` to ``π©`` is a setoid function ``f : π¨ βΆ π©`` such that
``β(b : B) β(a : A) f β¨$β© a ββ b``. In other words, the range and codomain of
``f`` are the same.

::

  {-# OPTIONS --without-K --exact-split --safe #-}

  module Setoid.Functions.Surjective where

  -- Imports from Agda and the Agda Standard Library --------------------------
  open import Agda.Primitive   using () renaming ( Set to Type )
  open import Data.Product     using ( _,_ ; Ξ£-syntax )
  open import Function         using ( Surjection ; IsSurjection )
                               renaming ( Func to _βΆ_ )
  open import Level            using ( _β_ ; Level )
  open import Relation.Binary  using ( Setoid )

  open import Function.Construct.Composition renaming ( isSurjection to isOnto )
   using ()

  import Function.Definitions as FD

  -- Imports from agda-algebras -----------------------------------------------
  open import Overture                   using ( β£_β£ ; β₯_β₯ ; β-syntax ; transport )
  open import Setoid.Functions.Basic     using ( _β_ )
  open import Setoid.Functions.Inverses  using ( Img_β_ ; Image_β_ ; Inv ; InvIsInverseΚ³ )


  private variable
   Ξ± Οα΅ Ξ² Οα΅ Ξ³ ΟαΆ : Level

  open Image_β_

  module _ {π¨ : Setoid Ξ± Οα΅}{π© : Setoid Ξ² Οα΅} where

   open Setoid π¨  renaming (Carrier to A; _β_ to _ββ_; isEquivalence to isEqA ) using ()
   open Setoid π©  renaming (Carrier to B; _β_ to _ββ_; isEquivalence to isEqB )
                  using ( trans ; sym )

   open Surjection {a = Ξ±}{Οα΅}{Ξ²}{Οα΅}{From = π¨}{To = π©}  renaming (f to _β¨$β©_)
   open _βΆ_ {a = Ξ±}{Οα΅}{Ξ²}{Οα΅}{From = π¨}{To = π©}         renaming (f to _β¨$β©_ )
   open FD _ββ_ _ββ_

   isSurj : (A β B) β Type (Ξ± β Ξ² β Οα΅)
   isSurj f = β {y} β Img_β_ {π¨ = π¨}{π© = π©} f y

   IsSurjective : (π¨ βΆ π©) β Type (Ξ± β Ξ² β Οα΅)
   IsSurjective F = β {y} β Image F β y

   isSurjβIsSurjective : (F : π¨ βΆ π©) β isSurj (_β¨$β©_ F) β IsSurjective F
   isSurjβIsSurjective F isSurjF {y} = hyp isSurjF
    where
    hyp : Img (_β¨$β©_ F) β y β Image F β y
    hyp (Img_β_.eq a x) = eq a x

   open Image_β_

   SurjectionIsSurjective : (Surjection π¨ π©) β Ξ£[ g β (π¨ βΆ π©) ] (IsSurjective g)
   SurjectionIsSurjective s = g , gE
    where
    g : π¨ βΆ π©
    g = (record { f = _β¨$β©_ s ; cong = cong s })
    gE : IsSurjective g
    gE {y} = eq β£ (surjective s) y β£ (sym β₯ (surjective s) y β₯)

   SurjectionIsSurjection : (Surjection π¨ π©) β Ξ£[ g β (π¨ βΆ π©) ] (IsSurjection _ββ_ _ββ_ (_β¨$β©_ g))
   SurjectionIsSurjection s = g , gE
    where
    g : π¨ βΆ π©
    g = (record { f = _β¨$β©_ s ; cong = cong s })
    gE : IsSurjection _ββ_ _ββ_ (_β¨$β©_ g)
    IsSurjection.isCongruent gE = record  { cong = cong g
                                          ; isEquivalenceβ = isEqA
                                          ; isEquivalenceβ = isEqB
                                          }
    IsSurjection.surjective gE y = β£ (surjective s) y β£ , β₯ (surjective s) y β₯

With the next definition we represent a *right-inverse* of a surjective setoid function.

::

   SurjInv : (f : π¨ βΆ π©) β IsSurjective f β B β A
   SurjInv f fE b = Inv f (fE {b})

Thus, a right-inverse of ``f`` is obtained by applying ``Inv`` to ``f``
and a proof of ``IsSurjective f``. Next we prove that this does indeed
give the right-inverse.

::

   SurjInvIsInverseΚ³ :  (f : π¨ βΆ π©)(fE : IsSurjective f)
    β                   β {b} β (f β¨$β© ((SurjInv f fE) b)) ββ b

   SurjInvIsInverseΚ³ f fE = InvIsInverseΚ³ fE

We conclude this module by giving a formal proof of the fact that composition of two surjective surjective
setoid functions is again a surjective setoid function.

::

  module _ {π¨ : Setoid Ξ± Οα΅}{π© : Setoid Ξ² Οα΅}{πͺ : Setoid Ξ³ ΟαΆ} where

   open Setoid π¨  using ()               renaming (Carrier to A; _β_ to _ββ_)
   open Setoid π©  using ( trans ; sym )  renaming (Carrier to B; _β_ to _ββ_)
   open Setoid πͺ  using ()               renaming (Carrier to C; _β_ to _ββ_)

   open Surjection  renaming (f to _β¨$β©_)
   open _βΆ_         renaming (f to _β¨$β©_ )
   open FD _ββ_ _ββ_


   β-IsSurjective :  {G : π¨ βΆ πͺ}{H : πͺ βΆ π©}
    β                IsSurjective G β IsSurjective H β IsSurjective (H β G)

   β-IsSurjective {G} {H} gE hE {y} = Goal
    where
    mp : Image H β y β Image H β G β y
    mp (eq c p) = Ξ· gE
     where
     Ξ· : Image G β c β Image H β G β y
     Ξ· (eq a q) = eq a (trans p (cong H q))

    Goal : Image H β G β y
    Goal = mp hE


   β-epic : Surjection π¨ πͺ β Surjection πͺ π© β Surjection π¨ π©
   Surjection.f (β-epic g h) x = h β¨$β© (g β¨$β© x)
   Surjection.cong (β-epic g h) {x} {y} xy = cong h (cong g xy)
   Surjection.surjective (β-epic g h) = IsSurjection.surjective hgSurj
    where
    gSurj : Ξ£[ G β (π¨ βΆ πͺ) ] (IsSurjection _ββ_ _ββ_ (_β¨$β©_ G))
    gSurj = SurjectionIsSurjection g
    hSurj : Ξ£[ H β (πͺ βΆ π©) ] (IsSurjection _ββ_ _ββ_ (_β¨$β©_ H))
    hSurj = SurjectionIsSurjection h

    hgSurj : IsSurjection _ββ_ _ββ_ (Ξ» x β h β¨$β© (g β¨$β© x))
    hgSurj = isOnto β₯ gSurj β₯ β₯ hSurj β₯


   epic-factor :  (f : π¨ βΆ π©)(g : π¨ βΆ πͺ)(h : πͺ βΆ π©)
    β             IsSurjective f β (β i β (f β¨$β© i) ββ ((h β g) β¨$β© i)) β IsSurjective h

   epic-factor f g h fE compId {y} = Goal
    where
     finv : B β A
     finv = SurjInv f fE

     ΞΆ : y ββ (f β¨$β© (finv y))
     ΞΆ = sym (SurjInvIsInverseΚ³ f fE)

     Ξ· : y ββ ((h β g) β¨$β© (finv y))
     Ξ· = trans ΞΆ (compId (finv y))

     Goal : Image h β y
     Goal = eq (g β¨$β© (finv y)) Ξ·
