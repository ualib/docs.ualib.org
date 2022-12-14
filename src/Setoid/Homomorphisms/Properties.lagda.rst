.. FILE      : Setoid/Homomorphisms/Properties.lagda.rst
.. AUTHOR    : William DeMeo
.. DATE      : 13 Sep 2021
.. UPDATED   : 18 Jun 2022

.. highlight:: agda
.. role:: code

.. _properties-of-homomorphisms:

Properties of Homomorphisms
~~~~~~~~~~~~~~~~~~~~~~~~~~~

This is the `Setoid.Homomorphisms.Properties`_ module of the `Agda Universal Algebra Library`_.

::

  {-# OPTIONS --without-K --exact-split --safe #-}

  open import Overture using (π ; π₯ ; Signature)

  module Setoid.Homomorphisms.Properties {π : Signature π π₯} where

  -- Imports from Agda and the Agda Standard Library ------------------------------------------
  open import Data.Product     using ( _,_ ) renaming ( projβ to fst ; projβ to snd )
  open import Function         using ( id ) renaming ( Func to _βΆ_ )
  open import Level            using ( Level )
  open import Relation.Binary  using ( Setoid )

  open import Relation.Binary.PropositionalEquality as β‘ using ( _β‘_ )

  -- Imports from the Agda Universal Algebra Library ------------------------------------------
  open import Overture          using ( β£_β£ ; β₯_β₯ )
  open import Setoid.Functions  using ( _β_ ; ππ ; Image_β_ ; eq ; β-IsSurjective )

  open  import Setoid.Algebras {π = π}
        using ( Algebra ; _Μ_; Lift-AlgΛ‘; Lift-AlgΚ³; Lift-Alg; π[_])
  open  import Setoid.Homomorphisms.Basic {π = π}
        using ( hom ; IsHom ; epi ; IsEpi ; compatible-map )

  open _βΆ_ using ( cong ) renaming (f to _β¨$β©_ )

  private variable Ξ± Ξ² Ξ³ Οα΅ Οα΅ ΟαΆ β : Level

.. _composition-of-homs:

Composition of homs
^^^^^^^^^^^^^^^^^^^

::

  module _  {π¨ : Algebra Ξ± Οα΅} {π© : Algebra Ξ² Οα΅} {πͺ : Algebra Ξ³ ΟαΆ} where
    open Algebra π¨  renaming (Domain to A )   using ()
    open Algebra π©  renaming (Domain to B )   using ()
    open Algebra πͺ  renaming (Domain to C )   using ()
    open Setoid A   renaming ( _β_ to _ββ_ )  using ()
    open Setoid B   renaming ( _β_ to _ββ_ )  using ()
    open Setoid C   renaming ( _β_ to _ββ_ )  using ( trans )

    open IsHom

    -- The composition of homomorphisms is again a homomorphism
    β-is-hom :  {g : A βΆ B}{h : B βΆ C}
     β          IsHom π¨ π© g β IsHom π© πͺ h
     β          IsHom π¨ πͺ (h β g)

    β-is-hom {g} {h} ghom hhom = record { compatible = c }
     where
     c : compatible-map π¨ πͺ (h β g)
     c {f}{a} = trans lemg lemh
      where
      lemg : (h β¨$β© (g β¨$β© ((f Μ π¨) a))) ββ (h β¨$β© ((f Μ π©) (Ξ» x β g β¨$β© (a x))))
      lemg = cong h (compatible ghom)

      lemh : (h β¨$β© ((f Μ π©) (Ξ» x β g β¨$β© (a x)))) ββ ((f Μ πͺ) (Ξ» x β h β¨$β© (g β¨$β© (a x))))
      lemh = compatible hhom

    β-hom : hom π¨ π© β hom π© πͺ  β hom π¨ πͺ
    β-hom (h , hhom) (g , ghom) = (g β h) , β-is-hom hhom ghom

    -- The composition of epimorphisms is again an epimorphism
    open IsEpi

    β-is-epi :  {g : A βΆ B}{h : B βΆ C}
     β          IsEpi π¨ π© g β IsEpi π© πͺ h β IsEpi π¨ πͺ (h β g)

    β-is-epi gE hE = record  { isHom = β-is-hom (isHom gE) (isHom hE)
                             ; isSurjective = β-IsSurjective (isSurjective gE) (isSurjective hE)
                             }

    β-epi : epi π¨ π© β epi π© πͺ  β epi π¨ πͺ
    β-epi (h , hepi) (g , gepi) = (g β h) , β-is-epi hepi gepi

.. _lifting-and-lowering-of-homs:

Lifting and lowering of homs
^^^^^^^^^^^^^^^^^^^^^^^^^^^^

First we define the identity homomorphism for setoid algebras and then
we prove that the operations of lifting and lowering of a setoid algebra
are homomorphisms.

::

  module _ {π¨ : Algebra Ξ± Οα΅} where
   open Algebra π¨  renaming (Domain to A )                   using ()
   open Setoid A   renaming ( _β_ to _ββ_ ; refl to reflβ )  using ( reflexive )

   πΎπΉ :  hom π¨ π¨
   πΎπΉ = ππ , record { compatible = reflexive β‘.refl }

  module _ {π¨ : Algebra Ξ± Οα΅}{β : Level} where
   open Algebra π¨  using ()             renaming (Domain to A )
   open Setoid A   using ( reflexive )  renaming ( _β_ to _ββ_ ; refl to reflβ )

   open Algebra  using ( Domain )
   open Setoid (Domain (Lift-AlgΛ‘ π¨ β))  using () renaming ( _β_ to _βΛ‘_ ; refl to reflΛ‘)
   open Setoid (Domain (Lift-AlgΚ³ π¨ β))  using () renaming ( _β_ to _βΚ³_ ; refl to reflΚ³)

   open Level
   ToLiftΛ‘ : hom π¨ (Lift-AlgΛ‘ π¨ β)
   ToLiftΛ‘ =  record { f = lift ; cong = id } ,
              record { compatible = reflexive β‘.refl }

   FromLiftΛ‘ : hom (Lift-AlgΛ‘ π¨ β) π¨
   FromLiftΛ‘ = record { f = lower ; cong = id } , record { compatible = reflΛ‘ }

   ToFromLiftΛ‘ : β b β  (β£ ToLiftΛ‘ β£ β¨$β© (β£ FromLiftΛ‘ β£ β¨$β© b)) βΛ‘ b
   ToFromLiftΛ‘ b = reflβ

   FromToLiftΛ‘ : β a β (β£ FromLiftΛ‘ β£ β¨$β© (β£ ToLiftΛ‘ β£ β¨$β© a)) ββ a
   FromToLiftΛ‘ a = reflβ

   ToLiftΚ³ : hom π¨ (Lift-AlgΚ³ π¨ β)
   ToLiftΚ³ =  record { f = id ; cong = lift } ,
              record { compatible = lift (reflexive β‘.refl) }

   FromLiftΚ³ : hom (Lift-AlgΚ³ π¨ β) π¨
   FromLiftΚ³ =  record { f = id ; cong = lower } , record { compatible = reflΛ‘ }

   ToFromLiftΚ³ : β b β (β£ ToLiftΚ³ β£ β¨$β© (β£ FromLiftΚ³ β£ β¨$β© b)) βΚ³ b
   ToFromLiftΚ³ b = lift reflβ

   FromToLiftΚ³ : β a β (β£ FromLiftΚ³ β£ β¨$β© (β£ ToLiftΚ³ β£ β¨$β© a)) ββ a
   FromToLiftΚ³ a = reflβ

  module _ {π¨ : Algebra Ξ± Οα΅}{β r : Level} where
   open Level
   open Algebra                            using ( Domain )
   open Setoid  (Domain π¨)                 using (refl)
   open Setoid  (Domain (Lift-Alg π¨ β r))  using ( _β_ )

   ToLift : hom π¨ (Lift-Alg π¨ β r)
   ToLift = β-hom ToLiftΛ‘ ToLiftΚ³

   FromLift : hom (Lift-Alg π¨ β r) π¨
   FromLift = β-hom FromLiftΚ³ FromLiftΛ‘

   ToFromLift : β b β (β£ ToLift β£ β¨$β© (β£ FromLift β£ β¨$β© b)) β b
   ToFromLift b = lift refl


   ToLift-epi : epi π¨ (Lift-Alg π¨ β r)
   ToLift-epi = β£ ToLift β£ ,
                record  { isHom = β₯ ToLift β₯
                        ; isSurjective = Ξ» {y} β eq (β£ FromLift β£ β¨$β© y) (ToFromLift y)
                        }

Next we formalize the fact that a homomorphism from ``π¨`` to ``π©`` can
be lifted to a homomorphism from ``Lift-Alg π¨ βα΅`` to ``Lift-Alg π© βα΅``.

::

  module _ {π¨ : Algebra Ξ± Οα΅} {π© : Algebra Ξ² Οα΅} where
   open Algebra            using ( Domain )
   open Setoid (Domain π¨)  using ( reflexive )  renaming ( _β_ to _ββ_ )
   open Setoid (Domain π©)  using ()             renaming ( _β_ to _ββ_ )
   open Level

   Lift-homΛ‘ : hom π¨ π©  β (βα΅ βα΅ : Level) β  hom (Lift-AlgΛ‘ π¨ βα΅) (Lift-AlgΛ‘ π© βα΅)
   Lift-homΛ‘ (f , fhom) βα΅ βα΅ = Ο , β-is-hom lABh (snd ToLiftΛ‘)
    where
    lA lB : Algebra _ _
    lA = Lift-AlgΛ‘ π¨ βα΅
    lB = Lift-AlgΛ‘ π© βα΅

    Ο : Domain lA βΆ Domain π©
    Ο β¨$β© x = f β¨$β© (lower x)
    cong Ο = cong f

    lABh : IsHom lA π© Ο
    lABh = β-is-hom (snd FromLiftΛ‘) fhom

    Ο : Domain lA βΆ Domain lB
    Ο β¨$β© x = lift (f β¨$β© (lower x))
    cong Ο = cong f

   Lift-homΚ³ : hom π¨ π©  β (rα΅ rα΅ : Level) β  hom (Lift-AlgΚ³ π¨ rα΅) (Lift-AlgΚ³ π© rα΅)
   Lift-homΚ³ (f , fhom) rα΅ rα΅ = Ο , Goal
    where
    lA lB : Algebra _ _
    lA = Lift-AlgΚ³ π¨ rα΅
    lB = Lift-AlgΚ³ π© rα΅
    Ο : Domain lA βΆ Domain π©
    Ο β¨$β© x = f β¨$β© x
    cong Ο xy = cong f (lower xy)

    lABh : IsHom lA π© Ο
    lABh = β-is-hom (snd FromLiftΚ³) fhom

    Ο : Domain lA βΆ Domain lB
    Ο β¨$β© x = f β¨$β© x
    lower (cong Ο xy) = cong f (lower xy)

    Goal : IsHom lA lB Ο
    Goal = β-is-hom lABh (snd ToLiftΚ³)

   open Setoid using ( _β_ )

   lift-hom-lemma :  (h : hom π¨ π©)(a : π[ π¨ ])(βα΅ βα΅ : Level)
    β                (_β_ (Domain (Lift-AlgΛ‘ π© βα΅))) (lift (β£ h β£ β¨$β© a))
                     (β£ Lift-homΛ‘ h βα΅ βα΅ β£ β¨$β© lift a)

   lift-hom-lemma h a βα΅ βα΅ = Setoid.refl (Domain π©)

  module _ {π¨ : Algebra Ξ± Οα΅} {π© : Algebra Ξ² Οα΅} where

   Lift-hom :  hom π¨ π©  β (βα΅ rα΅ βα΅ rα΅ : Level)
    β          hom (Lift-Alg π¨ βα΅ rα΅) (Lift-Alg π© βα΅ rα΅)

   Lift-hom Ο βα΅ rα΅ βα΅ rα΅ = Lift-homΚ³ (Lift-homΛ‘ Ο βα΅ βα΅) rα΅ rα΅

   Lift-hom-fst : hom π¨ π©  β (β r : Level) β  hom (Lift-Alg π¨ β r) π©
   Lift-hom-fst Ο _ _ = β-hom FromLift Ο

   Lift-hom-snd : hom π¨ π©  β (β r : Level) β  hom π¨ (Lift-Alg π© β r)
   Lift-hom-snd Ο _ _ = β-hom Ο ToLift 
