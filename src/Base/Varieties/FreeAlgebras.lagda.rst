.. FILE      : Base/Varieties/FreeAlgebras.lagda.rst
.. AUTHOR    : William DeMeo
.. DATE      : 01 Mar 2021
.. UPDATED   : 23 Jun 2022

.. highlight:: agda
.. role:: code

.. _base-varieties-free-algebras-and-birkhoffs-theorem:

Free Algebras and Birkhoff's Theorem
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

This is the `Base.Varieties.FreeAlgebras`_ module of the `Agda Universal Algebra Library`_.

First we will define the relatively free algebra in a variety, which is the
"freest" algebra among (universal for) those algebras that model all identities
holding in the variety. Then we give a formal proof of Birkhoff's theorem which
says that a variety is an equational class. In other terms, a class ``π¦`` of
algebras is closed under the operators ``H``, ``S``, and ``P`` if and only if
``π¦`` is the class of algebras that satisfy some set of identities.
::

  {-# OPTIONS --without-K --exact-split --safe #-}

  open import Level            using ( Level )
  open import Overture  using ( π ; π₯ ; Signature )
  module Base.Varieties.FreeAlgebras {Ξ± : Level} {π : Signature π π₯} where

  -- Imports from Agda and the Agda Standard Library ---------------------
  open  import Agda.Primitive   using ( _β_ )renaming  ( Set to Type )
  open  import Data.Product     using ( _,_ ; Ξ£-syntax ; _Γ_ )
                                renaming  ( projβ to fst ; projβ to snd )
  open  import Function         using ( _β_ )
  open  import Level            using ( suc )
  open  import Relation.Binary  using ( IsEquivalence ) renaming  ( Rel to BinRel )
  open  import Relation.Unary   using ( Pred ; _β_ ; _β_ ; ο½_ο½ ; _βͺ_ )

  open  import Axiom.Extensionality.Propositional
        using () renaming  (Extensionality to funext)
  open  import Relation.Binary.PropositionalEquality as β‘
        using ( _β‘_ ; module β‘-Reasoning )

  -- Imports from the Agda Universal Algebra Library -------------------------------------------
  open  import Overture        using ( β£_β£ ; β₯_β₯ ; _β_ ; _β»ΒΉ )
  open  import Base.Functions  using ( IsSurjective )
  open  import Base.Relations  using ( kernel ; βͺ_β« )
  open  import Base.Equality
        using ( SwellDef ; swelldef ; is-set ; blk-uip ; hfunext ; DFunExt; pred-ext )

  open  import Base.Algebras {π = π}
        using ( Algebra ; Lift-Alg ; compatible;  _Μ_ ; ov ; β¨ ; Con; mkcon ; IsCongruence )
  open  import Base.Homomorphisms {π = π}
        using ( hom ; epi ; epiβhom ; kercon ; ker-in-con ; Οker ; ker[_β_]_βΎ_ ; β-hom )
        using ( β¨-hom-co ; HomFactor ; HomFactorEpi ; _β_ ; β-refl ; β-sym ; Lift-β )
  open  import Base.Terms {π = π}
        using ( Term ; π» ; free-lift ; lift-hom ; free-unique ; _β¦_β§ )
        using ( lift-of-epi-is-epi ; comm-hom-term; free-lift-interp )
  open  import Base.Subalgebras {π = π}
        using ( _β€_ ; FirstHomCorollary|Set )

  open  import Base.Varieties.EquationalLogic {π = π}
        using ( _β«_β_; _β§_β_; Th; Mod )
  open  import Base.Varieties.Closure {π = π}
        using ( S ; P ; V )
  open  import Base.Varieties.Preservation {π = π}
        using ( module class-products-with-maps ; class-ids-β ; class-ids ; SPβV')

  open Term ; open S ; open V

  π πβΊ : Level
  π = ov Ξ±
  πβΊ = suc (ov Ξ±)    -- (this will be the level of the free algebra)

.. _base-varieties-the-free-algebra-in-theory:

The free algebra in theory
^^^^^^^^^^^^^^^^^^^^^^^^^^

Recall, we proved in the `Base.Terms.Basic`_ module that the term algebra ``π» X``
is absolutely free in the class of all ``π``-structures. In this section, we
formalize, for a given class ``π¦`` of ``π``-algebras, the (relatively) free
algebra in ``S(P π¦)`` over ``X``.

We use the next definition to take a free algebra *for* a class ``π¦`` and produce
the free algebra *in* ``π¦``. Let ``Ξ(π¦, π¨) := {ΞΈ β Con π¨ : π¨ / ΞΈ β (S π¦)}``, and
let ``Ο(π¦, π¨) := β Ξ(π¦, π¨)``. (Notice that ``Ξ(π¦, π¨)`` may be empty, in which case
``Ο(π¦, π¨) = 1`` and then ``π¨ / Ο(π¦, π¨)`` is trivial.) The free algebra is
constructed by applying the definitions of ``ΞΈ`` and ``Ο`` to the special case in
which ``π¨`` is the algebra ``π» X`` of ``π``-terms over ``X``.

Since ``π» X`` is free for (and in) the class of all ``π``-algebras, it follows
that ``π» X`` is free for every class ``π¦`` of ``π``-algebras. Of course, ``π» X``
is not necessarily a member of ``π¦``, but if we form the quotient of ``π» X``
modulo the congruence ``Ο(π¦, π» X)``, which we denote by
``π½[ X ] := (π» X) / Ο(π¦, π» X)``, then it's not hard to see that  ``π½[ X ]`` is a
subdirect product of the algebras in ``{(π» π) / ΞΈ}``, where ``ΞΈ`` ranges over
``Ξ(π¦, π» X)``, so ``π½[ X ]`` belongs to ``SP(π¦)``, and must therefore satisfy all
identities modeled by all members of ``π¦``. Indeed, for each pair ``p q : π» X``,
if ``π¦ β§ p β q``, then ``p`` and ``q`` belong to the same ``Ο(π¦, π» X)``-class, so
``p`` and ``q`` are identified in the quotient ``π½[ X ]``.

The ``π½[ X ]`` that we have just defined is called the *free algebra over* ``π¦``
*generated by* ``X`` and (because of what we just observed) we may say that ``π½[ X
]`` is free *in* ``SP(π¦)``.

**Remarks**. Since ``X`` is not a subset of ``π½[ X ]``, technically it doesn't
make sense to say "``X`` generates ``π½[ X ]``." But as long as ``π¦`` contains a
nontrivial algebra, we will have ``Ο(π¦, π» π) β© XΒ² β  β``, and we can identify ``X``
with ``X / Ο(π¦, π» X)`` which *is* a subset of ``π½[ X ]``.

.. _base-varieties-the-free-algebra-in-agda:

The free algebra in Agda
^^^^^^^^^^^^^^^^^^^^^^^^

Before we attempt to represent the free algebra in Agda we construct the
congruence ``Ο(π¦, π» π)`` described above. First, we represent the congruence
relation ``ΟCon``, modulo which ``π» X`` yields the relatively free algebra,
``π½[ X ] := π» X β± ΟCon``. We let ``Ο`` be the collection of identities ``(p, q)``
satisfied by all subalgebras of algebras in ``π¦``.

::

  module _ {X : Type Ξ±}(π¦ : Pred (Algebra Ξ±) π) where

   Ο : Pred (β£ π» X β£ Γ β£ π» X β£) π
   Ο (p , q) = β(π¨ : Algebra Ξ±)(sA : π¨ β S{Ξ±}{Ξ±} π¦)(h : X β β£ π¨ β£ )
                   β  (free-lift π¨ h) p β‘ (free-lift π¨ h) q

We convert the predicate ``Ο`` into a relation by `currying <https://en.wikipedia.org/wiki/Currying>`__.

::

   ΟRel : BinRel β£ π» X β£ π
   ΟRel p q = Ο (p , q)

To express ``ΟRel`` as a congruence of the term algebra ``π» X``, we must prove that

1. ``ΟRel`` is compatible with the operations of ``π» X`` (which are jsut the terms
   themselves) and
2. ``ΟRel`` it is an equivalence relation.

::

   open β‘-Reasoning

   Οcompatible : swelldef π₯ Ξ± β compatible (π» X) ΟRel
   Οcompatible wd π {p} {q} Οpq π¨ sA h = Ξ³
    where
    Ο : hom (π» X) π¨
    Ο = lift-hom π¨ h

    Ξ³ : β£ Ο β£ ((π Μ π» X) p) β‘ β£ Ο β£ ((π Μ π» X) q)

    Ξ³ = β£ Ο β£ ((π Μ π» X) p)  β‘β¨ β₯ Ο β₯ π p β©
        (π Μ π¨) (β£ Ο β£ β p)  β‘β¨ wd (π Μ π¨)(β£ Ο β£ β p)(β£ Ο β£ β q)(Ξ» x β Οpq x π¨ sA h) β©
        (π Μ π¨) (β£ Ο β£ β q)  β‘β¨ (β₯ Ο β₯ π q)β»ΒΉ β©
        β£ Ο β£ ((π Μ π» X) q)  β

   ΟIsEquivalence : IsEquivalence ΟRel
   ΟIsEquivalence = record  { refl = Ξ» π¨ sA h β β‘.refl
                            ; sym = Ξ» x π¨ sA h β (x π¨ sA h)β»ΒΉ
                            ; trans = Ξ» pΟq qΟr π¨ sA h β (pΟq π¨ sA h) β (qΟr π¨ sA h) }

We have collected all the pieces necessary to express the collection of identities
satisfied by all subalgebras of algebras in the class as a congruence relation of
the term algebra. We call this congruence ``ΟCon`` and define it using the
Congruence constructor ``mkcon``.

::

   ΟCon : swelldef π₯ Ξ± β Con (π» X)
   ΟCon wd = ΟRel , mkcon ΟIsEquivalence (Οcompatible wd)

.. _base-varieties-hsp-theorem:

HSP Theorem
^^^^^^^^^^^

To complete the proof of the HSP theorem, it remains to show that
``Mod X (Th (V π¦))`` is contained in ``V π¦``; that is, every algebra that models
the equations in ``Th (V π¦)`` belongs to ``V π¦``. This will prove that ``V π¦`` is
an equational class. (The converse, that every equational class is a variety was
already proved; see the remarks at the end of this module.)

We accomplish this goal by constructing an algebra ``π½`` with the following properties:

1. ``π½ β V π¦`` and

2. Every ``π¨ β Mod X (Th (V π¦))`` is a homomorphic image of ``π½``.

We denote by ``β­`` the product of all subalgebras of algebras in ``π¦``, and by
``homβ­`` the homomorphism from ``π» X`` to ``β­`` defined as follows: ``homβ­ :=
β¨-hom-co (π» X) π homπ``. Here, ``β¨-hom-co`` (defined in the
`Base.Homomorphisms.Properties`_ module) takes the term algebra ``π» X``, a family
``{π : I β Algebra Ξ± π}`` of ``π``-algebras, and a family
``homπ : β i β hom (π» X) (π i)`` of homomorphisms and constructs the natural
homomorphism ``homβ­`` from ``π» X`` to the product ``β­ := β¨ π``. The homomorphism
``homβ­ : hom (π» X) (β¨ β­)`` is "natural" in the sense that the ``i``-th component
of the image of ``t : Term X`` under ``homβ­`` is the image ``β£ homπ i β£ t`` of
``t`` under the ``i``-th homomorphism ``homπ i``.

.. _base-varieties-f-is-a-subalgebra-of-sk:

``π½ β€ β¨ S(π¦)``
^^^^^^^^^^^^^^^

Now we come to a step in our approach to formalizing the HSP theorem that turned
out to be more technically challenging than we anticipated. We must prove that the
free algebra embeds in the product ``β­`` of all subalgebras of algebras in the
class ``π¦``. This is really the only stage in the proof of Birkhoff's theorem that
requires the truncation assumption that ``β­`` be a *set* (that is, ``β­`` has the
UIP_ property). We will also need to assume several local function extensionality
postulates and, as a result, the next submodule will take as given the parameter
``fe : (β a b β funext a b)``. This allows us to postulate local function
extensionality when and where we need it in the proof. For example, if we want to
assume function extensionality at universe levels ``π₯`` and ``Ξ±``, we simply apply
``fe`` to those universes: ``fe π₯ Ξ±``. (Earlier versions of the library used just
a single *global* function extensionality postulate at the start of most modules,
but we have since decided to exchange that elegant but crude option for greater
precision and transparency.)

::

  module _ {fe : DFunExt}{wd : SwellDef}{X : Type Ξ±} {π¦ : Pred (Algebra Ξ±) π} where

   open class-products-with-maps {X = X}{fe π Ξ±}{fe πβΊ πβΊ}{fe π π} π¦

We begin by constructing ``β­``, using the techniques described in the section on
products of classes.

::

   -- β­ is the product of all subalgebras of algebras in π¦.
   β­ : Algebra π
   β­ = β¨ π'

Observe that the inhabitants of ``β­`` are maps from ``β`` to
``{π i : i β β}``. A homomorphism from ``π» X`` to ``β­`` is obtained as follows.

::

   homβ­ : hom (π» X) β­
   homβ­ = β¨-hom-co π' (fe π Ξ±){π}(π» X) Ξ» i β lift-hom (π' i)(snd β₯ i β₯)

.. _base-varieties-the-free-algebra:

The free algebra
^^^^^^^^^^^^^^^^

As mentioned, the initial version of the agda-algebras_ library used the free
algebra ``π`` developed above. However, our new, more direct proof uses the
algebra ``π½``, which we now define, along with the natural epimorphism
``epiπ½ : epi (π» X) π½`` from ``π» X`` to ``π½``.

We now define the algebra ``π½``, which plays the role of the free algebra, along
with the natural epimorphism ``epiπ½ : epi (π» X) π½`` from ``π» X`` to ``π½``.

::

   π½ : Algebra πβΊ
   π½ = ker[ π» X β β­ ] homβ­ βΎ (wd π₯ (ov Ξ±))

   epiπ½ : epi (π» X) π½
   epiπ½ = Οker (wd π₯ (ov Ξ±)) {β­} homβ­

   homπ½ : hom (π» X) π½
   homπ½ = epiβhom π½ epiπ½

   homπ½-is-epic : IsSurjective β£ homπ½ β£
   homπ½-is-epic = snd β₯ epiπ½ β₯

We will need the following facts relating ``homβ­``, ``homπ½``, ``and Ο``.

::

   Οlemma0 : β p q β  β£ homβ­ β£ p β‘ β£ homβ­ β£ q  β (p , q) β Ο π¦
   Οlemma0 p q phomβ­q π¨ sA h = β‘.cong-app phomβ­q (π¨ , sA , h)

   Οlemma0-ap : {π¨ : Algebra Ξ±}{h : X β β£ π¨ β£} β π¨ β S{Ξ±}{Ξ±} π¦
    β           kernel β£ homπ½ β£ β kernel (free-lift π¨ h)

   Οlemma0-ap {π¨}{h} skA {p , q} x = Ξ³ where

    Ξ½ : β£ homβ­ β£ p β‘ β£ homβ­ β£ q
    Ξ½ = ker-in-con {Ξ± = (ov Ξ±)}{ov Ξ±}{π» X}{wd π₯ (suc (ov Ξ±))}(kercon (wd π₯ (ov Ξ±)) {β­} homβ­) {p}{q} x

    Ξ³ : (free-lift π¨ h) p β‘ (free-lift π¨ h) q
    Ξ³ = ((Οlemma0 p q) Ξ½) π¨ skA h

We now use ``Οlemma0-ap`` to prove that every map ``h : X β β£ π¨ β£``, from ``X`` to
a subalgebra ``π¨ β S π¦`` of ``π¦``, lifts to a homomorphism from ``π½`` to ``π¨``.

::

   π½-lift-hom : (π¨ : Algebra Ξ±) β π¨ β S{Ξ±}{Ξ±} π¦ β (X β β£ π¨ β£) β hom π½ π¨
   π½-lift-hom π¨ skA h = fst(HomFactor (wd π₯ (suc (ov Ξ±)))  π¨ (lift-hom π¨ h) homπ½ (Οlemma0-ap skA) homπ½-is-epic)


.. _base-varieties-k-models-psi:

``π¦`` models ``Ο``
^^^^^^^^^^^^^^^^^^^

The goal of this subsection is to prove that ``π¦`` models ``Ο π¦``. In other terms,
for all pairs ``(p , q) β Term X Γ Term X`` of terms, if ``(p , q) β Ο π¦``, then
``π¦ β« p β q``.

Next we define the lift of the natural embedding from ``X`` into ``π½``. We denote
this homomorphism by ``π : hom (π» X) π½`` and define it as follows.

::

   open IsCongruence

   Xβͺπ½ : X β β£ π½ β£
   Xβͺπ½ x = βͺ β x β« -- (the implicit relation here is  β¨ kercon (fe π₯ π) β­ homβ­ β© )

   π : hom (π» X) π½
   π = lift-hom π½ Xβͺπ½

It turns out that the homomorphism so defined is equivalent to ``homπ½``.

::

   open β‘-Reasoning

   homπ½-is-lift-hom : β p β β£ π β£ p β‘ β£ homπ½ β£ p
   homπ½-is-lift-hom (β x) = β‘.refl
   homπ½-is-lift-hom (node π π) =
    β£ π β£ (node π π)              β‘β¨ β₯ π β₯ π π β©
    (π Μ π½)(Ξ» i β β£ π β£(π i))     β‘β¨ wd-proof β©
    (π Μ π½)(Ξ» i β β£ homπ½ β£ (π i)) β‘β¨ (β₯ homπ½ β₯ π π)β»ΒΉ β©
    β£ homπ½ β£ (node π π)           β
     where wd-proof = wd π₯ (suc (ov Ξ±))
                      (π Μ π½) (Ξ» i β β£ π β£(π i)) (Ξ» i β β£ homπ½ β£ (π i))
                      (Ξ» x β homπ½-is-lift-hom(π x))

We need a three more lemmas before we are ready to tackle our main goal.

::

   Οlemma1 : kernel β£ π β£ β Ο π¦
   Οlemma1 {p , q} πpq π¨ sA h = Ξ³
    where
     f : hom π½ π¨
     f = π½-lift-hom π¨ sA h

     h' Ο : hom (π» X) π¨
     h' = β-hom (π» X) π¨ π f
     Ο = lift-hom π¨ h

     hβ‘Ο : β t β (β£ f β£ β β£ π β£) t β‘ β£ Ο β£ t
     hβ‘Ο t = free-unique (wd π₯ Ξ±) π¨ h' Ο (Ξ» x β β‘.refl) t

     Ξ³ : β£ Ο β£ p β‘ β£ Ο β£ q
     Ξ³ = β£ Ο β£ p             β‘β¨ (hβ‘Ο p)β»ΒΉ β©
         β£ f β£ ( β£ π β£ p )   β‘β¨ β‘.cong β£ f β£ πpq β©
         β£ f β£ ( β£ π β£ q )   β‘β¨ hβ‘Ο q β©
         β£ Ο β£ q             β

   Οlemma2 : kernel β£ homπ½ β£ β Ο π¦
   Οlemma2 {p , q} x = Οlemma1 {p , q} Ξ³
     where
      Ξ³ : (free-lift π½ Xβͺπ½) p β‘ (free-lift π½ Xβͺπ½) q
      Ξ³ = (homπ½-is-lift-hom p) β x β (homπ½-is-lift-hom q)β»ΒΉ

   Οlemma3 : β p q β (p , q) β Ο{X = X} π¦ β π¦ β« p β q
   Οlemma3 p q pΟq {π¨} kA h = goal
     where
     goal : (π¨ β¦ p β§) h β‘ (π¨ β¦ q β§) h
     goal = (π¨ β¦ p β§) h       β‘β¨ free-lift-interp (wd π₯ Ξ±) π¨ h p β©
            (free-lift π¨ h) p β‘β¨ pΟq π¨ (siso (sbase kA) (β-sym Lift-β)) h β©
            (free-lift π¨ h) q β‘β¨ (free-lift-interp (wd π₯ Ξ±) π¨ h q)β»ΒΉ  β©
            (π¨ β¦ q β§) h       β

With these results in hand, it is now trivial to prove the main theorem of this
subsection.

::

   class-models-kernel : β p q β (p , q) β kernel β£ homπ½ β£ β π¦ β« p β q
   class-models-kernel p q x = Οlemma3 p q (Οlemma2 x)

   ππ¦ : Pred (Algebra πβΊ) (suc πβΊ)
   ππ¦ = V{Ξ± = Ξ±}{Ξ² = πβΊ} π¦

   kernel-in-theory' : kernel β£ homπ½ β£ β Th (V π¦)
   kernel-in-theory' {p , q} pKq = (class-ids-β fe wd p q (class-models-kernel p q pKq))

   kernel-in-theory : kernel β£ homπ½ β£ β Th ππ¦
   kernel-in-theory {p , q} pKq vkA x = class-ids fe wd p q (class-models-kernel p q pKq) vkA x

   _β _ : Type Ξ± β Algebra πβΊ β Type πβΊ
   X β  π¨ = Ξ£[ h β (X β β£ π¨ β£) ] IsSurjective h

   π½-ModTh-epi : (π¨ : Algebra πβΊ) β (X β  π¨) β π¨ β Mod (Th ππ¦) β epi π½ π¨
   π½-ModTh-epi π¨ (Ξ· , Ξ·E) AinMTV = goal
    where
    Ο : hom (π» X) π¨
    Ο = lift-hom π¨ Ξ·

    ΟE : IsSurjective β£ Ο β£
    ΟE = lift-of-epi-is-epi π¨ Ξ·E

    pqlem2 : β p q β (p , q) β kernel β£ homπ½ β£ β π¨ β§ p β q
    pqlem2 p q z = Ξ» x β AinMTV p q (kernel-in-theory z) x

    kerincl : kernel β£ homπ½ β£ β kernel β£ Ο β£
    kerincl {p , q} x = β£ Ο β£ p      β‘β¨ (free-lift-interp (wd π₯ πβΊ) π¨ Ξ· p)β»ΒΉ β©
                        (π¨ β¦ p β§) Ξ·  β‘β¨ pqlem2 p q x Ξ· β©
                        (π¨ β¦ q β§) Ξ·  β‘β¨ free-lift-interp (wd π₯ πβΊ) π¨ Ξ· q β©
                        β£ Ο β£ q      β

    goal : epi π½ π¨
    goal = fst (HomFactorEpi (wd π₯ (suc (ov Ξ±))) π¨ Ο homπ½ kerincl homπ½-is-epic ΟE)

.. _base-varieties-the-homomorphic-images-of-f:

The homomorphic images of ``π½``
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

Finally we come to one of the main theorems of this module; it asserts that every
algebra in ``Mod X (Th ππ¦)`` is a homomorphic image of ``π½``. We prove this below
as the function (or proof object) ``π½-ModTh-epi``. Before that, we prove two
auxiliary lemmas.

::

   module _ (pe : pred-ext (ov Ξ±)(ov Ξ±))(wd : SwellDef) -- extensionality assumptions
            (Cset : is-set β£ β­ β£)                       -- truncation assumptions
            (kuip : blk-uip(Term X)β£ kercon (wd π₯ (ov Ξ±)){β­}homβ­ β£)
    where

    π½β€β­ : (ker[ π» X β β­ ] homβ­ βΎ (wd π₯ (ov Ξ±))) β€ β­
    π½β€β­ = FirstHomCorollary|Set (π» X) β­ homβ­ pe (wd π₯ (ov Ξ±)) Cset kuip

The last piece we need to prove that every model of ``Th ππ¦`` is a homomorphic
image of ``π½`` is a crucial assumption that is taken for granted throughout
informal universal algebraβnamely, that our collection ``X`` of variable symbols
is arbitrarily large and that we have an *environment* which interprets the
variable symbols in every algebra under consideration. In other terms, an
environment provides, for every algebra ``π¨``, a surjective mapping
``Ξ· : X β β£ π¨ β£`` from ``X`` onto the domain of ``π¨``.

We do *not* assert that for an arbitrary type ``X`` such surjective maps exist.
Indeed, our ``X`` must is quite special to have this property. Later, we will
construct such an ``X``, but for now we simply postulate its existence. Note that
this assumption that an environment exists is only required in the proof of the
theorem ``π½-ModTh-epi``.

.. _f-in-vk:
``π½ β V(π¦)``
^^^^^^^^^^^^^

With this result in hand, along with what we proved earlierβnamely, ``PS(π¦) β
SP(π¦) β HSP(π¦) β‘ V π¦``-it is not hard to show that ``π½`` belongs to ``V π¦``.

::

    π½βSP : hfunext (ov Ξ±)(ov Ξ±) β π½ β (S{π}{πβΊ} (P{Ξ±}{π} π¦))
    π½βSP hfe = ssub (class-prod-s-β-sp hfe) π½β€β­

    π½βπ : hfunext (ov Ξ±)(ov Ξ±) β π½ β V π¦
    π½βπ hfe = SPβV' {Ξ±}{fe π Ξ±}{fe πβΊ πβΊ}{fe π π}{π¦} (π½βSP hfe)

.. _base-varieties-the-hsp-theorem:

The HSP Theorem
^^^^^^^^^^^^^^^

Now that we have all of the necessary ingredients, it is all but trivial to
combine them to prove the HSP theorem. (Note that since the proof enlists
the help of the ``π½-ModTh-epi`` theorem, we must assume an environment exists,
which is manifested in the premise ``β π¨ β X β  π¨``.

::

    Birkhoff : hfunext (ov Ξ±)(ov Ξ±) β (β π¨ β X β  π¨) β Mod (Th (V π¦)) β V π¦
    Birkhoff hfe π {π¨} Ξ± = vhimg{π© = π¨} (π½βπ hfe) (π¨ , epiβhom π¨ ΟE , snd β₯ ΟE β₯)
     where
     ΟE : epi π½ π¨
     ΟE = π½-ModTh-epi π¨ (π π¨) Ξ±

The converse inclusion, ``V π¦ β Mod X (Th (V π¦))``, is a simple consequence of the
fact that ``Mod Th`` is a closure operator. Nonetheless, completeness demands that
we formalize this inclusion as well, however trivial the proof.

::

    Birkhoff-converse : V{Ξ±}{π} π¦ β Mod{X = X} (Th (V π¦))
    Birkhoff-converse Ξ± p q pThq = pThq Ξ±

We have thus proved that every variety is an equational class. Readers familiar
with the classical formulation of the HSP theorem, as an "if and only if" result,
might worry that we haven't completed the proof. But recall that in the
`Base.Varieties.Preservation`_ module we proved the following identity
preservation lemmas:

-  ``π¦ β« p β q β H π¦ β« p β q``
-  ``π¦ β« p β q β S π¦ β« p β q``
-  ``π¦ β« p β q β P π¦ β« p β q``

From these it follows that every equational class is a variety. Thus, our formal
proof of Birkhoff's theorem is complete.



