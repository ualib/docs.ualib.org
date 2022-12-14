.. FILE      : Setoid/Homomorphisms/Factor.lagda.rst
.. AUTHOR    : William DeMeo
.. DATE      : 13 Sep 2021
.. UPDATED   : 09 Jun 2022

.. highlight:: agda
.. role:: code

Factoring homs of setoid algebras
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

This is the `Setoid.Homomorphisms.Factor`_ module of the `Agda Universal Algebra Library`_.

::

  {-# OPTIONS --without-K --exact-split --safe #-}

  open import Overture using (π ; π₯ ; Signature)

  module Setoid.Homomorphisms.Factor {π : Signature π π₯} where

  -- Imports from Agda and the Agda Standard Library -------------------------------------------------
  open import Data.Product     using ( _,_ ; Ξ£-syntax )  renaming ( projβ to fst ; projβ to snd )
  open import Function         using ( _β_ )             renaming ( Func to _βΆ_ )
  open import Level            using ( Level )
  open import Relation.Binary  using ( Setoid )
  open import Relation.Unary   using ( _β_ )

  open import Relation.Binary.PropositionalEquality  as β‘           using ()
  import Relation.Binary.Reasoning.Setoid            as SReasoning  using ( begin_ ; step-βΛ; step-β; _β)

  -- Imports from the Agda Universal Algebra Library ------------------------------------------------
  open import Overture         using ( β£_β£ ; β₯_β₯ )
  open import Setoid.Functions using ( Image_β_ ; IsSurjective ; SurjInv )
                               using ( SurjInvIsInverseΚ³ ; epic-factor )
  open import Base.Relations   using ( kernelRel )

  open import Setoid.Algebras {π = π}             using ( Algebra ; π[_] ; _Μ_ )
  open import Setoid.Homomorphisms.Basic {π = π}  using ( hom ; IsHom ; compatible-map ; epi ; IsEpi)

  private variable Ξ± Οα΅ Ξ² Οα΅ Ξ³ ΟαΆ : Level

If ``g : hom π¨ π©``, ``h : hom π¨ πͺ``, ``h`` is surjective, and ``ker h β ker g``,
then there exists ``Ο : hom πͺ π©`` such that ``g = Ο β h`` so the following diagram
commutes:

.. code::

   π¨ --- h -->> πͺ
    \         .
     \       .
      g     Ο
       \   .
        \ .
         V
         π©

We will prove this in case h is both surjective and injective.

::

  module _  {π¨ : Algebra Ξ± Οα΅} (π© : Algebra Ξ² Οα΅) {πͺ : Algebra Ξ³ ΟαΆ}
            (gh : hom π¨ π©)(hh : hom π¨ πͺ) where

   open Algebra π©  using ()          renaming (Domain to B )
   open Algebra πͺ  using ( Interp )  renaming (Domain to C )
   open Setoid B   using ()          renaming ( _β_ to _ββ_ ; sym to symβ )
   open Setoid C   using ( trans )   renaming ( _β_ to _ββ_ ; sym to symβ )
   open _βΆ_        using ( cong )    renaming (f to _β¨$β©_ )

   open SReasoning B

   private
    gfunc = β£ gh β£
    hfunc = β£ hh β£
    g = _β¨$β©_ gfunc
    h = _β¨$β©_ hfunc

   open IsHom
   open Image_β_

   HomFactor :  kernelRel _ββ_ h β kernelRel _ββ_ g β IsSurjective hfunc
                ---------------------------------------------------------
    β           Ξ£[ Ο β hom πͺ π© ] β a β (g a) ββ β£ Ο β£ β¨$β© (h a)

   HomFactor Khg hE = (Οmap , Οhom) , gΟh
    where
    kerpres : β aβ aβ β h aβ ββ h aβ β g aβ ββ g aβ
    kerpres aβ aβ hyp = Khg hyp

    hβ»ΒΉ : π[ πͺ ] β π[ π¨ ]
    hβ»ΒΉ = SurjInv hfunc hE

    Ξ· : β {c} β h (hβ»ΒΉ c) ββ c
    Ξ· = SurjInvIsInverseΚ³ hfunc hE

    ΞΎ : β {a} β h a ββ h (hβ»ΒΉ (h a))
    ΞΎ = symβ Ξ·

    ΞΆ : β{x y} β x ββ y β h (hβ»ΒΉ x) ββ h (hβ»ΒΉ y)
    ΞΆ xy = trans Ξ· (trans xy (symβ Ξ·))


    Οmap : C βΆ B
    _β¨$β©_ Οmap = g β hβ»ΒΉ
    cong Οmap = Khg β ΞΆ

    gΟh : (a : π[ π¨ ]) β g a ββ Οmap β¨$β© (h a)
    gΟh a = Khg ΞΎ


    open _βΆ_ Οmap using () renaming (cong to Οcong)
    Οcomp : compatible-map πͺ π© Οmap
    Οcomp {f}{c} =
     begin
      Οmap β¨$β© ((f Μ πͺ) c)              βΛβ¨ Οcong (cong Interp (β‘.refl , (Ξ» _ β Ξ·)))  β©
      g (hβ»ΒΉ ((f Μ πͺ)(h β (hβ»ΒΉ β c))))  βΛβ¨ Οcong (compatible β₯ hh β₯)                 β©
      g (hβ»ΒΉ (h ((f Μ π¨)(hβ»ΒΉ β c))))    βΛβ¨ gΟh ((f Μ π¨)(hβ»ΒΉ β c))                     β©
      g ((f Μ π¨)(hβ»ΒΉ β c))              ββ¨ compatible β₯ gh β₯                          β©
      (f Μ π©)(g β (hβ»ΒΉ β c))            β

    Οhom : IsHom πͺ π© Οmap
    compatible Οhom = Οcomp

If, in addition, ``g`` is surjective, then so will be the factor ``Ο``.

::

   HomFactorEpi :  kernelRel _ββ_ h β kernelRel _ββ_ g
    β              IsSurjective hfunc β IsSurjective gfunc
                   -------------------------------------------------
    β              Ξ£[ Ο β epi πͺ π© ] β a β (g a) ββ β£ Ο β£ β¨$β© (h a)

   HomFactorEpi Khg hE gE = (Οmap , Οepi) , gΟh
    where
    homfactor : Ξ£[ Ο β hom πͺ π© ] β a β (g a) ββ β£ Ο β£ β¨$β© (h a)
    homfactor = HomFactor Khg hE

    Οmap : C βΆ B
    Οmap = fst β£ homfactor β£

    gΟh : (a : π[ π¨ ]) β g a ββ Οmap β¨$β© (h a)
    gΟh = snd homfactor -- Khg ΞΎ

    Οhom : IsHom πͺ π© Οmap
    Οhom = snd β£ homfactor β£

    Οepi : IsEpi πͺ π© Οmap
    Οepi = record  { isHom = Οhom
                   ; isSurjective = epic-factor gfunc hfunc Οmap gE gΟh
                   }
