.. FILE      : Base/Varieties/Preservation.lagda.rst
.. AUTHOR    : William DeMeo
.. DATE      : 14 Jan 2021
.. UPDATED   : 23 Jun 2022

.. highlight:: agda
.. role:: code

.. _base-varieties-preservation-of-equations:

Preservation of equations
~~~~~~~~~~~~~~~~~~~~~~~~~

This is the `Base.Varieties.Preservation`_ module of the
`Agda Universal Algebra Library`_. In this module we show that identities are
preserved by closure operators ``H``, ``S``, and ``P``. This will establish the easy
direction of Birkhoff's HSP Theorem.

::

  {-# OPTIONS --without-K --exact-split --safe #-}

  open import Overture using ( π ; π₯ ; Signature )

  module Base.Varieties.Preservation {π : Signature π π₯} where

  -- Imports from Agda and the Agda Standard Library ----------------------
  open  import Agda.Primitive
        using () renaming  ( Set to Type )
  open  import Data.Product
        using ( _,_ ; Ξ£-syntax ; _Γ_ ) renaming  ( projβ to fst ; projβ to snd )
  open  import Data.Sum
        using ( _β_ ) renaming  ( injβ  to inl ; injβ  to inr )
  open  import Function
        using ( _β_ )
  open  import Level
        using ( Level ; _β_ ; suc )
  open  import Relation.Unary
        using ( Pred ; _β_ ; _β_ ; ο½_ο½ ; _βͺ_ )
  open  import Axiom.Extensionality.Propositional
        using () renaming (Extensionality to funext)
  open  import Relation.Binary.PropositionalEquality as β‘
        using ( _β‘_ ; module β‘-Reasoning )

  -- Imports from the Agda Universal Algebra Library ---------------------------------------------
  open import Overture        using ( β£_β£ ; β₯_β₯ ; _β»ΒΉ )
  open import Base.Functions  using ( Inv ; InvIsInverseΚ³ ; IsInjective )
  open import Base.Equality   using ( SwellDef ; hfunext ; DFunExt )

  open  import Base.Algebras {π = π}
        using ( Algebra ; Lift-Alg ; ov ; β¨ ; π ; class-product )
  open  import Base.Homomorphisms {π = π}
        using ( is-homomorphism ; _β_ ; β-sym ; Lift-β ; β-trans ; β¨β ; β-refl )
        using ( Lift-Alg-iso ; Lift-Alg-assoc )
  open  import Base.Terms {π = π}
        using ( Term ; π» ; _β¦_β§; comm-hom-term )
  open  import Base.Subalgebras {π = π}
        using ( _IsSubalgebraOfClass_ ; β€-Lift ; _IsSubalgebraOf_ ; _β€_ )
        using ( Lift-β€-Lift ; SubalgebraOfClass )
  open  import Base.Varieties.EquationalLogic {π = π}
        using ( _β«_β_ ; _β§_β_ ; Th )
  open  import Base.Varieties.Properties {π = π}
        using ( β§-Lift-invar ; β§-lower-invar ; β§-I-invar ; β§-S-invar ; β§-P-invar )
        using ( β§-S-class-invar ; β§-P-lift-invar )
  open  import Base.Varieties.Closure {π = π}
        using ( H ; S ; P ; V ; P-expa ; S-mono ; Sβsubalgebra ; Lift-Alg-subP' )
        using ( subalgebraβS ; P-idemp ; module Vlift )

  open H ; open S ; open P ; open V
  private variable Ξ± Ξ² : Level


.. _base-varieties-closure-properties:

Closure properties
^^^^^^^^^^^^^^^^^^

The types defined above represent operators with useful closure properties. We now
prove a handful of such properties that we need later.

The next lemma would be too obvious to care about were it not for the fact that
we'll need it later, so it too must be formalized.

::

  SβSP :  (π¦ : Pred (Algebra Ξ±)(ov Ξ±))
   β      S{Ξ±}{Ξ²} π¦ β S{Ξ± β Ξ²}{Ξ± β Ξ²} (P{Ξ±}{Ξ²} π¦)

  SβSP {Ξ±} {Ξ²} π¦ {.(Lift-Alg π¨ Ξ²)}(sbase{π¨} x) = siso spllA(β-sym Lift-β)
   where
   llA : Algebra (Ξ± β Ξ²)
   llA = Lift-Alg (Lift-Alg π¨ Ξ²) (Ξ± β Ξ²)

   spllA : llA β S (P π¦)
   spllA = sbase{Ξ± β Ξ²}{Ξ± β Ξ²} (pbase x)

  SβSP {Ξ±} {Ξ²} π¦ {.(Lift-Alg π¨ Ξ²)}(slift{π¨} x) = subalgebraβS lAsc
   where
   splAu : π¨ β S(P π¦)
   splAu = SβSP{Ξ±}{Ξ±} π¦ x

   Asc : π¨ IsSubalgebraOfClass (P π¦)
   Asc = Sβsubalgebra{Ξ±}{P{Ξ±}{Ξ±} π¦}{π¨} splAu

   lAsc : (Lift-Alg π¨ Ξ²) IsSubalgebraOfClass (P π¦)
   lAsc = Lift-Alg-subP' Asc

  SβSP {Ξ±} {Ξ²} π¦ {π©}(ssub{π¨} sA Bβ€A) = ssub (subalgebraβS lAsc) (β€-Lift π¨ Bβ€A )
   where
    lA : Algebra (Ξ± β Ξ²)
    lA = Lift-Alg π¨ Ξ²

    splAu : π¨ β S (P π¦)
    splAu = SβSP{Ξ±}{Ξ±} π¦ sA

    Asc : π¨ IsSubalgebraOfClass (P π¦)
    Asc = Sβsubalgebra{Ξ±}{P{Ξ±}{Ξ±} π¦}{π¨} splAu

    lAsc : lA IsSubalgebraOfClass (P π¦)
    lAsc = Lift-Alg-subP' Asc

  SβSP {Ξ± = Ξ±}{Ξ²} π¦ {π©}(siso{π¨} sA AβB) = siso{Ξ± β Ξ²}{Ξ± β Ξ²} lAsp lAβB
   where
   lA : Algebra (Ξ± β Ξ²)
   lA = Lift-Alg π¨ Ξ²

   lAsc : lA IsSubalgebraOfClass (P π¦)
   lAsc = Lift-Alg-subP' (Sβsubalgebra{Ξ±}{P{Ξ±}{Ξ±} π¦}{π¨} (SβSP π¦ sA))

   lAsp : lA β S(P π¦)
   lAsp = subalgebraβS{Ξ± β Ξ²}{Ξ± β Ξ²}{P{Ξ±}{Ξ²} π¦}{lA} lAsc

   lAβB : lA β π©
   lAβB = β-trans (β-sym Lift-β) AβB


We need to formalize one more lemma before arriving the main objective
of this section, which is the proof of the inclusion PSβSP.

::

  module _ {Ξ± Ξ² : Level} {π¦ : Pred(Algebra Ξ±)(ov Ξ±)} where

   lemPSβSP :  hfunext Ξ² Ξ± β funext Ξ² Ξ± β {I : Type Ξ²}{β¬ : I β Algebra Ξ±}
    β          (β i β (β¬ i) IsSubalgebraOfClass π¦)
    β          β¨ β¬ IsSubalgebraOfClass (P{Ξ±}{Ξ²} π¦)

   lemPSβSP hwu fwu {I}{β¬} Bβ€K =  β¨ π , (β¨ SA , β¨SAβ€β¨π) ,
                                   ΞΎ , (β¨β {fiu = fwu}{fiw = fwu} BβSA)
    where
    π : I β Algebra Ξ±
    π = Ξ» i β β£ Bβ€K i β£

    SA : I β Algebra Ξ±
    SA = Ξ» i β β£ fst β₯ Bβ€K i β₯ β£

    BβSA : β i β β¬ i β SA i
    BβSA = Ξ» i β β₯ snd β₯ Bβ€K i β₯ β₯

    SAβ€π : β i β (SA i) IsSubalgebraOf (π i)
    SAβ€π = Ξ» i β snd β£ β₯ Bβ€K i β₯ β£

    h : β i β β£ SA i β£ β β£ π i β£
    h = Ξ» i β fst β£ SAβ€π i β£

    hinj : β i β IsInjective (h i)
    hinj = Ξ» i β snd (snd β£ β₯ Bβ€K i β₯ β£)

    Ο : β£ β¨ SA β£ β β£ β¨ π β£
    Ο = Ξ» x i β (h i) (x i)
    Ξ½ : is-homomorphism (β¨ SA) (β¨ π) Ο
    Ξ½ = Ξ» π π β fwu Ξ» i β (snd β£ SAβ€π i β£) π (Ξ» x β π x i)

    Οinj : IsInjective Ο
    Οinj ΟxΟy = fwu Ξ» i β (hinj i)(β‘.cong-app ΟxΟy i)

    β¨SAβ€β¨π : β¨ SA β€ β¨ π
    β¨SAβ€β¨π = (Ο , Ξ½) , Οinj

    ΞΎ : β¨ π β P π¦
    ΞΎ = produ (Ξ» i β P-expa (β£ snd β₯ Bβ€K i β₯ β£))

.. _base-varieties-psk-in-spk:

``PS(π¦) β SP(π¦)``
^^^^^^^^^^^^^^^^^^

Finally, we are in a position to prove that a product of subalgebras of algebras
in a class ``π¦`` is a subalgebra of a product of algebras in ``π¦``.

::

  module _  {Ξ± : Level} {fovu : funext (ov Ξ±) (ov Ξ±)}
            {π¦ : Pred (Algebra Ξ±)(ov Ξ±)} where

   PSβSP :  -- extensionality assumptions:
            hfunext (ov Ξ±)(ov Ξ±)

    β       P{ov Ξ±}{ov Ξ±} (S{Ξ±}{ov Ξ±} π¦) β S{ov Ξ±}{ov Ξ±} (P{Ξ±}{ov Ξ±} π¦)

   PSβSP _ (pbase (sbase x)) = sbase (pbase x)
   PSβSP _ (pbase (slift{π¨} x)) = slift (SβSP{Ξ±}{ov Ξ±} π¦ (slift x))
   PSβSP _ (pbase{π©}(ssub{π¨} sA Bβ€A)) = siso(ssub(SβSP π¦ (slift sA))(Lift-β€-Lift (ov(Ξ±)){π¨}(ov(Ξ±))Bβ€A)) β-refl
   PSβSP _ (pbase (siso{π¨}{π©} x AβB)) = siso (SβSP π¦ (slift x)) ( Lift-Alg-iso AβB )
   PSβSP hfe (pliftu x) = slift (PSβSP hfe x)
   PSβSP hfe (pliftw x) = slift (PSβSP hfe x)

   PSβSP hfe (produ{I}{π} x) = (S-mono (P-idemp)) (subalgebraβS Ξ·)
    where
     ΞΎ : (i : I) β (π i) IsSubalgebraOfClass (P{Ξ±}{ov Ξ±} π¦)
     ΞΎ i = Sβsubalgebra (PSβSP hfe (x i))

     Ξ· : β¨ π IsSubalgebraOfClass (P{ov Ξ±}{ov Ξ±} (P{Ξ±}{ov Ξ±} π¦))
     Ξ· = lemPSβSP hfe fovu {I} {π} ΞΎ

   PSβSP hfe (prodw{I}{π} x) = (S-mono (P-idemp)) (subalgebraβS Ξ·)
    where
     ΞΎ : (i : I) β (π i) IsSubalgebraOfClass (P{Ξ±}{ov Ξ±} π¦)
     ΞΎ i = Sβsubalgebra (PSβSP hfe (x i))

     Ξ· : β¨ π IsSubalgebraOfClass (P{ov Ξ±}{ov Ξ±} (P{Ξ±}{ov Ξ±} π¦))
     Ξ· = lemPSβSP hfe fovu  {I} {π} ΞΎ

   PSβSP hfe (pisow{π¨}{π©} pA AβB) = siso (PSβSP hfe pA) AβB

.. _base-varieties-more-class-inclusions:

More class inclusions
^^^^^^^^^^^^^^^^^^^^^

We conclude this subsection with three more inclusion relations that will have bit
parts to play later (e.g., in the formal proof of Birkhoff's Theorem).

::

  PβV : {Ξ± Ξ² : Level}{π¦ : Pred (Algebra Ξ±)(ov Ξ±)} β P{Ξ±}{Ξ²} π¦ β V{Ξ±}{Ξ²} π¦

  PβV (pbase x) = vbase x
  PβV{Ξ±} (pliftu x) = vlift (PβV{Ξ±}{Ξ±} x)
  PβV{Ξ±}{Ξ²} (pliftw x) = vliftw (PβV{Ξ±}{Ξ²} x)
  PβV (produ x) = vprodu (Ξ» i β PβV (x i))
  PβV (prodw x) = vprodw (Ξ» i β PβV (x i))
  PβV (pisow x xβ) = visow (PβV x) xβ

  SPβV :  {Ξ± Ξ² : Level}{π¦ : Pred (Algebra Ξ±)(ov Ξ±)}
   β      S{Ξ± β Ξ²}{Ξ± β Ξ²} (P{Ξ±}{Ξ²} π¦) β V π¦

  SPβV (sbase{π¨} PCloA) = PβV (pisow PCloA Lift-β)
  SPβV (slift{π¨} x) = vliftw (SPβV x)
  SPβV (ssub{π¨}{π©} spA Bβ€A) = vssubw (SPβV spA) Bβ€A
  SPβV (siso x xβ) = visow (SPβV x) xβ


.. _base-varieties-v-is-closed-under-lift:

``V`` is closed under lift
^^^^^^^^^^^^^^^^^^^^^^^^^^

As mentioned earlier, a technical hurdle that must be overcome when formalizing
proofs in Agda is the proper handling of universe levels. In particular, in the
proof of the Birkhoff's theorem, for example, we will need to know that if an
algebra ``π¨`` belongs to the variety ``V π¦``, then so does the lift of ``π¨``.
Let us get the tedious proof of this technical lemma out of the way.

Above we proved that ``SP(π¦) β V(π¦)``, and we did so under fairly general
assumptions about the universe level parameters. Unfortunately, this is sometimes
not quite general enough, so we now prove the inclusion again for the specific
universe parameters that align with subsequent applications of this result.

::

  module _  {Ξ± : Level}  {feβ : funext (ov Ξ±) Ξ±}
            {feβ : funext ((ov Ξ±) β (suc (ov Ξ±))) (suc (ov Ξ±))}
            {feβ : funext (ov Ξ±) (ov Ξ±)}
            {π¦ : Pred (Algebra Ξ±)(ov Ξ±)} where
   open Vlift {Ξ±}{feβ}{feβ}{feβ}{π¦}

   SPβV' : S{ov Ξ±}{suc (ov Ξ±)} (P{Ξ±}{ov Ξ±} π¦) β V π¦
   SPβV' (sbase{π¨} x) = visow (VlA (SPβV (sbase x))) (β-sym (Lift-Alg-assoc _ _{π¨}))
   SPβV' (slift x) = VlA (SPβV x)

   SPβV' (ssub{π¨}{π©} spA Bβ€A) = vssubw (VlA (SPβV spA)) Bβ€lA
    where
     Bβ€lA : π© β€ Lift-Alg π¨ (suc (ov Ξ±))
     Bβ€lA = β€-Lift π¨ Bβ€A

   SPβV' (siso{π¨}{π©} x AβB) = visow (VlA (SPβV x)) Goal
    where
     Goal : Lift-Alg π¨ (suc (ov Ξ±)) β π©
     Goal = β-trans (β-sym Lift-β) AβB


.. _base-varieties-product-sk-in-spk:

``β¨ S(π¦) β SP(π¦)``
^^^^^^^^^^^^^^^^^^^^

As we saw in `Base.Algebras.Products`_, the (informal) product ``β¨ S(π¦)`` of all
subalgebras of algebras in π¦ is implemented (formally) in the agda-algebras_
library as ``β¨ π S(π¦)``. Our goal is to prove that this product belongs to
``SP(π¦)``. We do so by first proving that the product belongs to ``PS(π¦)`` and
then applying the ``PSβSP`` lemma.

Before doing so, we need to redefine the class product so that each factor comes
with a map from the type ``X`` of variable symbols into that factor. We will
explain the reason for this below.

::

  module class-products-with-maps {Ξ± : Level}
   {X : Type Ξ±}
   {feπΞ± : funext (ov Ξ±) Ξ±}
   {feβ : funext ((ov Ξ±) β (suc (ov Ξ±))) (suc (ov Ξ±))}
   {feβ : funext (ov Ξ±) (ov Ξ±)}
   (π¦ : Pred (Algebra Ξ±)(ov Ξ±))
   where

   β' : Type (ov Ξ±)
   β' = Ξ£[ π¨ β (Algebra Ξ±) ] ((π¨ β S{Ξ±}{Ξ±} π¦) Γ (X β β£ π¨ β£))

Notice that the second component of this dependent pair type is
``(π¨ β π¦) Γ (X β β£ π¨ β£)``. In previous versions of the
`Agda Universal Algebra Library`_ this  second component was simply ``π¨ β π¦``,
until we realized that adding the type ``X β β£ π¨ β£`` is quite useful. Later we
will see exactly why, but for now suffice it to say that a map of type
``X β β£ π¨ β£`` may be viewed abstractly as an *ambient context*, or more
concretely, as an assignment of *values* in ``β£ π¨ β£`` to *variable symbols* in
``X``. When computing with or reasoning about products, while we don't want to
rigidly impose a context in advance, want do want to lay our hands on whatever
context is ultimately assumed. Including the βcontext mapβ inside the index type
``β`` of the product turns out to be a convenient way to achieve this flexibility.

Taking the product over the index type ``β`` requires a function that maps an
index ``i : β`` to the corresponding algebra. Each ``i : β`` is a triple, say,
``(π¨ , p , h)``, where ``π¨ : Algebra Ξ± π``, ``p : π¨ β π¦``, and ``h : X β β£ π¨ β£``,
so the function mapping an index to the corresponding algebra is simply the first
projection.

::

   π' : β' β Algebra Ξ±
   π' = Ξ» (i : β') β β£ i β£

Finally, we define ``class-product`` which represents the product of all members
of ``π¦``.

::

   class-product' : Algebra (ov Ξ±)
   class-product' = β¨ π'

If ``p : π¨ β π¦`` and ``h : X β β£ π¨ β£``, we view the triple ``(π¨ , p , h) β β`` as
an index over the class, and so we can think of ``π (π¨ , p , h)`` (which is simply
``π¨``) as the projection of the product ``β¨ π`` onto the ``(π¨ , p, h)``-th
component.

::

   class-prod-s-β-ps : class-product' β P{ov Ξ±}{ov Ξ±}(S π¦)
   class-prod-s-β-ps = pisow psPllA (β¨β {fiu = feβ}{fiw = feπΞ±} llAβA)
    where
    lA llA : β' β Algebra (ov Ξ±)
    lA i =  Lift-Alg (π i) (ov Ξ±)
    llA i = Lift-Alg (lA i) (ov Ξ±)

    slA : β i β (lA i) β S π¦
    slA i = siso (fst β₯ i β₯) Lift-β

    psllA : β i β (llA i) β P (S π¦)
    psllA i = pbase (slA i)

    psPllA : β¨ llA β P (S π¦)
    psPllA = produ psllA

    llAβA : β i β (llA i) β (π' i)
    llAβA i = β-trans (β-sym Lift-β)(β-sym Lift-β)

So, since ``PSβSP``, we see that that the product of all subalgebras of a class
``π¦`` belongs to ``SP(π¦)``.

::

   class-prod-s-β-sp : hfunext (ov Ξ±) (ov Ξ±) β class-product β S(P π¦)
   class-prod-s-β-sp hfe = PSβSP {fovu = feβ} hfe class-prod-s-β-ps

.. _base-varieties-h-preserves-identities:

``H`` preserves identities
^^^^^^^^^^^^^^^^^^^^^^^^^^

First we prove that the closure operator ``H`` is compatible with identities that hold
in the given class.

::

  open β‘-Reasoning

  private variable π§ : Level
  open Term

  module _ (wd : SwellDef){X : Type π§} {π¦ : Pred (Algebra Ξ±)(ov Ξ±)} where

   H-id1 : (p q : Term X) β π¦ β« p β q β H{Ξ² = Ξ±} π¦ β« p β q
   H-id1 p q Ο (hbase x) = β§-Lift-invar wd p q (Ο x)
   H-id1 p q Ο (hhimg{π¨}{πͺ} HA (π© , ((Ο , Οh) , ΟE))) b = goal
    where
    IH : π¨ β§ p β q
    IH = (H-id1 p q Ο) HA

    preim : X β β£ π¨ β£
    preim x = Inv Ο (ΟE (b x))

    ΞΆ : β x β Ο (preim x) β‘ b x
    ΞΆ x = InvIsInverseΚ³ (ΟE (b x))

    goal : (π© β¦ p β§) b β‘ (π© β¦ q β§) b
    goal =  (π© β¦ p β§) b           β‘β¨ wd π§ Ξ± (π© β¦ p β§) b (Ο β preim )(Ξ» i β (ΞΆ i)β»ΒΉ)β©
            (π© β¦ p β§)(Ο β preim)  β‘β¨(comm-hom-term (wd π₯ Ξ±) π© (Ο , Οh) p preim)β»ΒΉ β©
            Ο((π¨ β¦ p β§) preim)    β‘β¨ β‘.cong Ο (IH preim) β©
            Ο((π¨ β¦ q β§) preim)    β‘β¨ comm-hom-term (wd π₯ Ξ±) π© (Ο , Οh) q preim β©
            (π© β¦ q β§)(Ο β preim)  β‘β¨ wd π§ Ξ± (π© β¦ q β§)(Ο β preim) b ΞΆ β©
            (π© β¦ q β§) b           β

The converse of the foregoing result is almost too obvious to bother with.
Nonetheless, we formalize it for completeness.

::

   H-id2 : β {Ξ²} β (p q : Term X) β H{Ξ² = Ξ²} π¦ β« p β q β π¦ β« p β q
   H-id2 p q Hpq KA = β§-lower-invar wd p q (Hpq (hbase KA))

.. _base-varieties-s-preserves-identities:

``S`` preserves identities
^^^^^^^^^^^^^^^^^^^^^^^^^^

::

   S-id1 : (p q : Term X) β π¦ β« p β q β S{Ξ² = Ξ±} π¦ β« p β q
   S-id1 p q Ο (sbase x) = β§-Lift-invar wd p q (Ο x)
   S-id1 p q Ο (slift x) = β§-Lift-invar wd p q ((S-id1 p q Ο) x)
   S-id1 p q Ο (ssub{π¨}{π©} sA Bβ€A) = β§-S-class-invar wd p q goal Ξ½
    where --Apply S-β§ to the class π¦ βͺ ο½ π¨ ο½
    Ο : π¨ β§ p β q
    Ο = S-id1 p q Ο sA

    Apq : ο½ π¨ ο½ β« p β q
    Apq β‘.refl = Ο

    goal : (π¦ βͺ ο½ π¨ ο½) β« p β q
    goal {π©} (inl x) = Ο x
    goal {π©} (inr y) = Apq y

    Ξ½ : SubalgebraOfClass  (Ξ» z β (π¦ βͺ ο½ π¨ ο½)
                           (Data.Product.projβ z , Data.Product.projβ z))

    Ξ½ = (π© , π¨ , (π© , Bβ€A) , _β_.injβ β‘.refl , β-refl)

   S-id1 p q Ο (siso{π¨}{π©} x xβ) = β§-I-invar wd π© p q (S-id1 p q Ο x) xβ

Again, the obvious converse is barely worth the bits needed to formalize it.

::

   S-id2 : β{Ξ²}(p q : Term X) β S{Ξ² = Ξ²}π¦ β« p β q β π¦ β« p β q
   S-id2 p q Spq {π¨} KA = β§-lower-invar wd p q (Spq (sbase KA))


.. _base-varieties-p-preserves-identities:

``P`` preserves identities
^^^^^^^^^^^^^^^^^^^^^^^^^^

::

  module _  (fe : DFunExt)(wd : SwellDef){X : Type π§}
            {π¦ : Pred (Algebra Ξ±)(ov Ξ±)} where

   P-id1 : (p q : Term X) β π¦ β« p β q β P{Ξ² = Ξ±} π¦ β« p β q

   P-id1 p q Ο (pbase x) = β§-Lift-invar wd p q (Ο x)
   P-id1 p q Ο (pliftu x) = β§-Lift-invar wd p q ((P-id1 p q Ο) x)
   P-id1 p q Ο (pliftw x) = β§-Lift-invar wd p q ((P-id1 p q Ο) x)

   P-id1 p q Ο (produ{I}{π} x) = β§-P-lift-invar fe wd π  p q IH
    where
    IH : β i β (Lift-Alg (π i) Ξ±) β§ p β q
    IH i = β§-Lift-invar wd  p q ((P-id1 p q Ο) (x i))

   P-id1 p q Ο (prodw{I}{π} x) = β§-P-lift-invar fe wd π  p q IH
    where
    IH : β i β (Lift-Alg (π i) Ξ±) β§ p β q
    IH i = β§-Lift-invar wd  p q ((P-id1 p q Ο) (x i))

   P-id1 p q Ο (pisow{π¨}{π©} x y) = β§-I-invar wd π© p q (P-id1 p q Ο x) y

β¦and converselyβ¦

::

  module _  (wd : SwellDef){X : Type π§} {π¦ : Pred (Algebra Ξ±)(ov Ξ±)} where

   P-id2 : β {Ξ²}(p q : Term X) β P{Ξ² = Ξ²} π¦ β« p β q β π¦ β« p β q
   P-id2 p q PKpq KA = β§-lower-invar wd p q (PKpq (pbase KA))

.. _base-varieties-v-preserves-identities:

``V`` preserves identities
^^^^^^^^^^^^^^^^^^^^^^^^^^

Finally, we prove the analogous preservation lemmas for the closure operator
``V``.

::

  module Vid  (fe : DFunExt)(wd : SwellDef)
              {π§ : Level} {X : Type π§}{π¦ : Pred (Algebra Ξ±)(ov Ξ±)} where

   V-id1 : (p q : Term X) β π¦ β« p β q β V{Ξ² = Ξ±} π¦ β« p β q
   V-id1 p q Ο (vbase x) = β§-Lift-invar wd p q (Ο x)
   V-id1 p q Ο (vlift{π¨} x) = β§-Lift-invar wd p q ((V-id1 p q Ο) x)
   V-id1 p q Ο (vliftw{π¨} x) = β§-Lift-invar wd p q ((V-id1 p q Ο) x)
   V-id1 p q Ο (vhimg{π¨}{πͺ}VA (π© , ((Ο , Οh) , ΟE))) b = goal
    where
    IH : π¨ β§ p β q
    IH = V-id1 p q Ο VA

    preim : X β β£ π¨ β£
    preim x = Inv Ο (ΟE (b x))

    ΞΆ : β x β Ο (preim x) β‘ b x
    ΞΆ x = InvIsInverseΚ³ (ΟE (b x))

    goal : (π© β¦ p β§) b β‘ (π© β¦ q β§) b
    goal =  (π© β¦ p β§) b           β‘β¨ wd π§ Ξ± (π© β¦ p β§) b (Ο β preim )(Ξ» i β (ΞΆ i)β»ΒΉ)β©
            (π© β¦ p β§)(Ο β preim)  β‘β¨(comm-hom-term (wd π₯ Ξ±) π© (Ο , Οh) p preim)β»ΒΉ β©
            Ο((π¨ β¦ p β§) preim)    β‘β¨ β‘.cong Ο (IH preim) β©
            Ο((π¨ β¦ q β§) preim)    β‘β¨ comm-hom-term (wd π₯ Ξ±) π© (Ο , Οh) q preim β©
            (π© β¦ q β§)(Ο β preim)  β‘β¨ wd π§ Ξ± (π© β¦ q β§)(Ο β preim) b ΞΆ β©
            (π© β¦ q β§) b           β

   V-id1 p q Ο ( vssubw {π¨}{π©} VA Bβ€A ) =
    β§-S-class-invar wd p q goal (π© , π¨ , (π© , Bβ€A) , inr β‘.refl , β-refl)
     where
     IH : π¨ β§ p β q
     IH = V-id1 p q Ο VA

     Asinglepq : ο½ π¨ ο½ β« p β q
     Asinglepq β‘.refl = IH

     goal : (π¦ βͺ ο½ π¨ ο½) β« p β q
     goal {π©} (inl x) = Ο x
     goal {π©} (inr y) = Asinglepq y

   V-id1 p q Ο (vprodu{I}{π} Vπ) = β§-P-invar fe wd π  p q Ξ» i β V-id1 p q Ο (Vπ i)
   V-id1 p q Ο (vprodw{I}{π} Vπ) = β§-P-invar fe wd π  p q Ξ» i β V-id1 p q Ο (Vπ i)
   V-id1 p q Ο (visou{π¨}{π©} VA AβB) = β§-I-invar wd π© p q (V-id1 p q Ο VA) AβB
   V-id1 p q Ο (visow{π¨}{π©} VA AβB) = β§-I-invar wd π© p q (V-id1 p q Ο VA) AβB

  module Vid'  (fe : DFunExt)(wd : SwellDef)
               {π§ : Level}{X : Type π§}{π¦ : Pred (Algebra Ξ±)(ov Ξ±)} where
   open Vid fe wd {π§}{X}{π¦} public
   V-id1' : (p q : Term X) β π¦ β« p β q β V{Ξ² = Ξ²} π¦ β« p β q
   V-id1' p q Ο (vbase x) = β§-Lift-invar wd p q (Ο x)
   V-id1' p q Ο (vlift{π¨} x) = β§-Lift-invar wd p q ((V-id1 p q Ο) x)
   V-id1' p q Ο (vliftw{π¨} x) = β§-Lift-invar wd p q ((V-id1' p q Ο) x)
   V-id1' p q Ο (vhimg{π¨}{πͺ} VA (π© , ((Ο , Οh) , ΟE))) b = goal
    where
    IH : π¨ β§ p β q
    IH = V-id1' p q Ο VA

    preim : X β β£ π¨ β£
    preim x = Inv Ο (ΟE (b x))

    ΞΆ : β x β Ο (preim x) β‘ b x
    ΞΆ x = InvIsInverseΚ³ (ΟE (b x))

    goal : (π© β¦ p β§) b β‘ (π© β¦ q β§) b
    goal =  (π© β¦ p β§) b           β‘β¨ wd π§ _ (π© β¦ p β§) b (Ο β preim )(Ξ» i β (ΞΆ i)β»ΒΉ)β©
            (π© β¦ p β§)(Ο β preim)  β‘β¨(comm-hom-term (wd π₯ _) π© (Ο , Οh) p preim)β»ΒΉ β©
            Ο((π¨ β¦ p β§) preim)    β‘β¨ β‘.cong Ο (IH preim) β©
            Ο((π¨ β¦ q β§) preim)    β‘β¨ comm-hom-term (wd π₯ _) π© (Ο , Οh) q preim β©
            (π© β¦ q β§)(Ο β preim)  β‘β¨ wd π§ _ (π© β¦ q β§)(Ο β preim) b ΞΆ β©
            (π© β¦ q β§) b           β

   V-id1' p q Ο (vssubw {π¨}{π©} VA Bβ€A) = β§-S-invar wd π© {p}{q}(V-id1' p q Ο VA) Bβ€A
   V-id1' p q Ο (vprodu{I}{π} Vπ) = β§-P-invar fe wd π  p q Ξ» i β V-id1 p q Ο (Vπ i)
   V-id1' p q Ο (vprodw{I}{π} Vπ) = β§-P-invar fe wd π  p q Ξ» i β V-id1' p q Ο (Vπ i)
   V-id1' p q Ο (visou {π¨}{π©} VA AβB) = β§-I-invar wd π© p q (V-id1 p q Ο VA) AβB
   V-id1' p q Ο (visow{π¨}{π©} VA AβB) = β§-I-invar wd π© p q (V-id1' p q Ο VA)AβB

.. _base-varieties-class-identities:

Class identities
^^^^^^^^^^^^^^^^

From ``V-id1`` it follows that if π¦ is a class of structures, then the set of
identities modeled by all structures in ``π¦`` is equivalent to the set of
identities modeled by all structures in ``V π¦``. In other terms, ``Th (V π¦)`` is
precisely the set of identities modeled by ``π¦``. We formalize this observation as
follows.

::

  module _  (fe : DFunExt)(wd : SwellDef)
            {π§ : Level}{X : Type π§} {π¦ : Pred (Algebra Ξ±)(ov Ξ±)} where
   ovu lovu : Level
   ovu = ov Ξ±
   lovu = suc (ov Ξ±)
   π : Pred (Algebra lovu) (suc lovu)
   π = V{Ξ±}{lovu} π¦
   π± : Pred (Algebra ovu) lovu
   π± = V{Ξ² = ovu} π¦

   open Vid' fe wd {π§}{X}{π¦} public
   class-ids-β : (p q : β£ π» X β£) β π¦ β« p β q  β  (p , q) β Th π±
   class-ids-β p q pKq VCloA = V-id1' p q pKq VCloA

   class-ids : (p q : β£ π» X β£) β π¦ β« p β q  β  (p , q) β Th π
   class-ids p q pKq VCloA = V-id1' p q pKq VCloA

   class-ids-β : (p q : β£ π» X β£) β (p , q) β Th π± β  π¦ β« p β q
   class-ids-β p q Thpq {π¨} KA = β§-lower-invar wd p q (Thpq (vbase KA))

Once again, and for the last time, completeness dictates that we formalize the
coverse of ``V-id1``, however obvious it may be.

::

  module _ (wd : SwellDef){X : Type π§}{π¦ : Pred (Algebra Ξ±)(ov Ξ±)} where

   V-id2 : (p q : Term X) β (V{Ξ² = Ξ²} π¦ β« p β q) β (π¦ β« p β q)
   V-id2 p q Vpq {π¨} KA = β§-lower-invar wd p q (Vpq (vbase KA))


