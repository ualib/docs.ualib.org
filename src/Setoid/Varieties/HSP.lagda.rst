.. FILE      : Setoid/Varieties/HSP.lagda.rst
.. AUTHOR    : William DeMeo
.. DATE      : 16 Oct 2021
.. UPDATED   : 22 Jun 2022

.. highlight:: agda
.. role:: code

.. _setoid-varieties-the-hsp-theorem:

The HSP Theorem
~~~~~~~~~~~~~~~

::

  {-# OPTIONS --without-K --exact-split --safe #-}

  open import Overture using (π ; π₯ ; Signature)

  module Setoid.Varieties.HSP {π : Signature π π₯} where

  -- Imports from Agda and the Agda Standard Library -------------------------------
  open import Agda.Primitive   using () renaming ( Set to Type )
  open import Data.Product     using ( _,_ ; Ξ£-syntax ; _Γ_ )
                               renaming ( projβ to fst ; projβ to snd )
  open import Function         using () renaming ( Func to _βΆ_ )
  open import Level            using ( Level ; _β_ )
  open import Relation.Binary  using ( Setoid )
  open import Relation.Unary   using ( Pred ; _β_ ; _β_ )

  -- -- Imports from the Agda Universal Algebra Library ----------------------------
  open  import Overture          using ( β£_β£ ; β₯_β₯ )
  open  import Setoid.Relations  using ( fkerPred )

  open  import Setoid.Algebras {π = π}     using ( Algebra ; ov ; Lift-Alg ; β¨ )
  open  import Setoid.Subalgebras {π = π}  using ( _β€_ ; monββ€ )
  open  import Setoid.Homomorphisms {π = π}
        using  ( hom ; mon ; IsMon ; IsHom ; epi ; epiβontohom ; β¨-hom-co
               ; HomFactor ; β-refl ; _IsHomImageOf_ )

  open  import Setoid.Terms {π = π}
        using ( module Environment ; π» ; lift-hom ; free-lift ; free-lift-interp )

  open  import Setoid.Varieties.Closure {π = π}
        using ( S ; V ; P ; S-idem ; V-β-lc )

  open  import Setoid.Varieties.Preservation {π = π}
        using ( S-id2 ; PSβSP )

  open  import Setoid.Varieties.FreeAlgebras {π = π}
        using ( module FreeHom ; π½-ModTh-epi-lift )

  open  import Setoid.Varieties.SoundAndComplete  {π = π}
        using ( module FreeAlgebra ; _β«_ ; _βΜ_ ;  _β’_βΉ_β_ ; Mod ; Th )

  open _βΆ_          using () renaming ( f to _β¨$β©_ )
  open Setoid       using ( Carrier )
  open Algebra      using ( Domain )
  open Environment  using ( Env )

  module _  {Ξ± Οα΅ β : Level}
            (π¦ : Pred(Algebra Ξ± Οα΅) (Ξ± β Οα΅ β ov β))
            {X : Type (Ξ± β Οα΅ β β)} where

   private ΞΉ = ov(Ξ± β Οα΅ β β)

   open FreeHom (Ξ± β Οα΅ β β) {Ξ±}{Οα΅}{β}{π¦}
   open FreeAlgebra {ΞΉ = ΞΉ}{I = β} β° using ( π½[_] )


We want to pair each ``(π¨ , p)`` (where p : π¨ β S π¦) with an environment
``Ο : X β β£ π¨ β£`` so that we can quantify over all algebras *and* all
assignments of values in the domain ``β£ π¨ β£`` to variables in ``X``.

::

   ββΊ : Type ΞΉ
   ββΊ = Ξ£[ π¨ β (Algebra Ξ± Οα΅) ] (π¨ β S β π¦) Γ (Carrier (Env π¨ X))

   πβΊ : ββΊ β Algebra Ξ± Οα΅
   πβΊ i = β£ i β£

   β­ : Algebra ΞΉ ΞΉ
   β­ = β¨ πβΊ

Next we define a useful type, ``skEqual``, which we use to represent a
term identity ``p β q`` for any given ``i = (π¨ , sA , Ο)`` (where ``π¨``
is an algebra, ``sA : π¨ β S π¦`` is a proof that ``π¨`` belongs to
``S π¦``, and ``Ο`` is a mapping from ``X`` to the domain of ``π¨``). Then
we prove ``AllEqualβkerπ½`` which asserts that if the identity ``p β q``
holds in all ``π¨ β S π¦`` (for all environments), then ``p β q`` holds in
the relatively free algebra ``π½[ X ]``; equivalently, the pair
``(p , q)`` belongs to the kernel of the natural homomorphism from
``π» X`` onto ``π½[ X ]``. We will use this fact below to prove that there
is a monomorphism from ``π½[ X ]`` into ``β­``, and thus ``π½[ X ]`` is a
subalgebra of β­, so belongs to ``S (P π¦)``.

::

   skEqual : (i : ββΊ) β β{p q} β Type Οα΅
   skEqual i {p}{q} = β¦ p β§ β¨$β© snd β₯ i β₯ β β¦ q β§ β¨$β© snd β₯ i β₯
    where
    open Setoid (Domain (πβΊ i)) using ( _β_ )
    open Environment (πβΊ i) using ( β¦_β§ )

   AllEqualβkerπ½ :  β {p q}
    β               (β i β skEqual i {p}{q}) β (p , q) β fkerPred β£ homπ½[ X ] β£

   AllEqualβkerπ½ {p} {q} x = Goal
    where
    open Algebra π½[ X ]  using () renaming ( Domain to F ; Interp to InterpF )
    open Setoid F        using () renaming ( _β_  to _βFβ_ ; refl to reflF )
    Sπ¦β«pq : S{Ξ² = Ξ±}{Οα΅} β π¦ β« (p βΜ q)
    Sπ¦β«pq π¨ sA Ο = x (π¨ , sA , Ο)
    Goal : p βFβ q
    Goal = π¦β«ββ°β’ (S-id2{β = β}{p = p}{q} Sπ¦β«pq)

   homβ­ : hom (π» X) β­
   homβ­ = β¨-hom-co πβΊ h
    where
    h : β i β hom (π» X) (πβΊ i)
    h i = lift-hom (snd β₯ i β₯)

   open Algebra π½[ X ]  using () renaming ( Domain to F ; Interp to InterpF )
   open Setoid F        using () renaming (refl to reflF ; _β_ to _βFβ_ ; Carrier to β£Fβ£)


   kerπ½βkerβ­ : fkerPred β£ homπ½[ X ] β£ β fkerPred β£ homβ­ β£
   kerπ½βkerβ­ {p , q} pKq (π¨ , sA , Ο) = Goal
    where
    open Setoid (Domain π¨)  using ( _β_ ; sym ; trans )
    open Environment π¨      using ( β¦_β§ )
    fl : β t β β¦ t β§ β¨$β© Ο β free-lift Ο t
    fl t = free-lift-interp {π¨ = π¨} Ο t
    subgoal : β¦ p β§ β¨$β© Ο β β¦ q β§ β¨$β© Ο
    subgoal = kerπ½βEqual{π¨ = π¨}{sA} pKq Ο
    Goal : (free-lift{π¨ = π¨} Ο p) β (free-lift{π¨ = π¨} Ο q)
    Goal = trans (sym (fl p)) (trans subgoal (fl q))


   homπ½β­ : hom π½[ X ] β­
   homπ½β­ = β£ HomFactor β­ homβ­ homπ½[ X ] kerπ½βkerβ­ homπ½[ X ]-is-epic β£

   open Environment β­

   kerβ­βkerπ½ : β{p q} β (p , q) β fkerPred β£ homβ­ β£ β (p , q) β fkerPred β£ homπ½[ X ] β£
   kerβ­βkerπ½ {p}{q} pKq = Eβ’pq
    where
    pqEqual : β i β skEqual i {p}{q}
    pqEqual i = goal
     where
     open Environment (πβΊ i)      using () renaming ( β¦_β§ to β¦_β§α΅’ )
     open Setoid (Domain (πβΊ i))  using ( _β_ ; sym ; trans )
     goal : β¦ p β§α΅’ β¨$β© snd β₯ i β₯ β β¦ q β§α΅’ β¨$β© snd β₯ i β₯
     goal = trans  (free-lift-interp{π¨ = β£ i β£}(snd β₯ i β₯) p)
                   (trans (pKq i)(sym (free-lift-interp{π¨ = β£ i β£} (snd β₯ i β₯) q)))
    Eβ’pq : β° β’ X βΉ p β q
    Eβ’pq = AllEqualβkerπ½ pqEqual


   monπ½β­ : mon π½[ X ] β­
   monπ½β­ = β£ homπ½β­ β£ , isMon
    where
    open IsMon
    open IsHom
    isMon : IsMon π½[ X ] β­ β£ homπ½β­ β£
    isHom isMon = β₯ homπ½β­ β₯
    isInjective isMon {p} {q} Οpq = kerβ­βkerπ½ Οpq

Now that we have proved the existence of a monomorphism from ``π½[ X ]``
to ``β­`` we are in a position to prove that ``π½[ X ]`` is a subalgebra
of β­, so belongs to ``S (P π¦)``. In fact, we will show that ``π½[ X ]``
is a subalgebra of the *lift* of ``β­``, denoted ``ββ­``.

::

   π½β€β­ : π½[ X ] β€ β­
   π½β€β­ = monββ€ monπ½β­

   SPπ½ : π½[ X ] β S ΞΉ (P β ΞΉ π¦)
   SPπ½ = S-idem SSPπ½
    where
    PSβ­ : β­ β P (Ξ± β Οα΅ β β) ΞΉ (S β π¦)
    PSβ­ = ββΊ , (πβΊ , ((Ξ» i β fst β₯ i β₯) , β-refl))

    SPβ­ : β­ β S ΞΉ (P β ΞΉ π¦)
    SPβ­ = PSβSP {β = β} PSβ­

    SSPπ½ : π½[ X ] β S ΞΉ (S ΞΉ (P β ΞΉ π¦))
    SSPπ½ = β­ , (SPβ­ , π½β€β­)


.. _setoid-varieties-proof-of-the-hsp-theorem:

Proof of the HSP theorem
^^^^^^^^^^^^^^^^^^^^^^^^

Finally, we are in a position to prove Birkhoff's celebrated variety
theorem.

::

  module _ {Ξ± Οα΅ β : Level}{π¦ : Pred(Algebra Ξ± Οα΅) (Ξ± β Οα΅ β ov β)} where
   private ΞΉ = ov(Ξ± β Οα΅ β β)

   open FreeHom (Ξ± β Οα΅ β β) {Ξ±}{Οα΅}{β}{π¦}
   open FreeAlgebra {ΞΉ = ΞΉ}{I = β} β° using ( π½[_] )

   Birkhoff : β π¨ β π¨ β Mod (Th (V β ΞΉ π¦)) β π¨ β V β ΞΉ π¦
   Birkhoff π¨ ModThA = V-β-lc{Ξ±}{Οα΅}{β} π¦ π¨ VlA
    where
    open Setoid (Domain π¨) using () renaming ( Carrier to β£Aβ£ )
    spπ½A : π½[ β£Aβ£ ] β S{ΞΉ} ΞΉ (P β ΞΉ π¦)
    spπ½A = SPπ½{β = β} π¦

    epiπ½lA : epi π½[ β£Aβ£ ] (Lift-Alg π¨ ΞΉ ΞΉ)
    epiπ½lA = π½-ModTh-epi-lift{β = β} (Ξ» {p q} β ModThA{p = p}{q})

    lAimgπ½A : Lift-Alg π¨ ΞΉ ΞΉ IsHomImageOf π½[ β£Aβ£ ]
    lAimgπ½A = epiβontohom π½[ β£Aβ£ ] (Lift-Alg π¨ ΞΉ ΞΉ) epiπ½lA

    VlA : Lift-Alg π¨ ΞΉ ΞΉ β V β ΞΉ π¦
    VlA = π½[ β£Aβ£ ] , spπ½A , lAimgπ½A


The converse inclusion, ``V π¦ β Mod (Th (V π¦))``, is a simple
consequence of the fact that ``Mod Th`` is a closure operator.
Nonetheless, completeness demands that we formalize this inclusion as
well, however trivial the proof.

::

   module _ {π¨ : Algebra Ξ± Οα΅} where
    open Setoid (Domain π¨) using () renaming ( Carrier to β£Aβ£ )

    Birkhoff-converse : π¨ β V{Ξ±}{Οα΅}{Ξ±}{Οα΅}{Ξ±}{Οα΅} β ΞΉ π¦ β π¨ β Mod{X = β£Aβ£} (Th (V β ΞΉ π¦))
    Birkhoff-converse vA pThq = pThq π¨ vA

We have thus proved that every variety is an equational class.

Readers familiar with the classical formulation of the Birkhoff HSP
theorem as an βif and only ifβ assertion might worry that the proof is
still incomplete. However, recall that in the
[Setoid.Varieties.Preservation][] module we proved the following
identity preservation lemma:

``V-id1 : π¦ β« p βΜ q β V π¦ β« p βΜ q``

Thus, if ``π¦`` is an equational classβthat is, if π¦ is the class of
algebras satisfying all identities in some setβthen ``V π¦ β π¦``.
On the other hand, we proved that ``V`` is expansive in the
`Setoid.Varieties.Closure`_ module:

``V-expa : π¦ β V π¦``

so ``π¦`` (= ``V π¦`` = ``HSP π¦``) is a variety.

Taken together, ``V-id1`` and ``V-expa`` constitute formal proof that
every equational class is a variety.

This completes the formal proof of Birkhoff's variety theorem.

