.. FILE      : Base/Terms/Properties.lagda.rst
.. AUTHOR    : William DeMeo
.. DATE      : 03 Jul 2021
.. UPDATED   : 23 Jun 2022

.. highlight:: agda
.. role:: code

.. _base-terms-properties-of-terms-and-the-term-algebra:

Properties of Terms and the Term Algebra
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

This is the `Base.Terms.Properties`_ module of the `Agda Universal Algebra Library`_.

::

  {-# OPTIONS --without-K --exact-split --safe #-}

  open import Overture using ( π ; π₯ ; Signature )

  module Base.Terms.Properties {π : Signature π π₯} where

  -- Imports from Agda and the Agda Standard Library --------------------------------------
  open import Agda.Primitive          using () renaming ( Set to Type )
  open import Data.Product            using ( _,_ ; Ξ£-syntax )
  open import Function                using ( _β_ )
  open import Data.Empty.Polymorphic  using ( β₯ )
  open import Level                   using ( Level )
  open import Relation.Binary         using ( IsEquivalence ; Setoid ; Reflexive )
                                      using ( Symmetric ; Transitive )
  open import Relation.Binary.PropositionalEquality as β‘
                                      using ( _β‘_ ; module β‘-Reasoning )
  open import Axiom.Extensionality.Propositional
                                      using () renaming (Extensionality to funext)


  -- Imports from the Agda Universal Algebra Library ----------------------------------------
  open import Overture                using ( _β»ΒΉ ; ππ ; β£_β£ ; β₯_β₯ )
  open import Base.Functions          using ( Inv ; InvIsInverseΚ³ ; Image_β_)
                                      using ( eq ; IsSurjective )
  open  import Base.Equality          using ( swelldef )

  open  import Base.Algebras       {π = π} using ( Algebra ; _Μ_  ; ov )
  open  import Base.Homomorphisms  {π = π} using ( hom )
  open  import Base.Terms.Basic    {π = π} using ( Term ; π» )

  open Term
  private variable Ξ± Ξ² Ο : Level


.. _base-terms-the-universal-property:

The universal property
^^^^^^^^^^^^^^^^^^^^^^

The term algebra ``π» X`` is *absolutely free* (or *universal*, or *initial*) for
algebras in the signature ``π``. That is, for every ``π``-algebra ``π¨``, the
following hold.

1. Every function from ``π`` to ``β£ π¨ β£`` lifts to a homomorphism from
   ``π» X`` to ``π¨``.
2. The homomorphism that exists by item 1 is unique.

We now prove this in Agda_, starting with the fact that every map from ``X`` to
``β£ π¨ β£`` lifts to a map from ``β£ π» X β£`` to ``β£ π¨ β£`` in a natural way, by
induction on the structure of the given term.

::

  private variable X : Type Ο

  free-lift : (π¨ : Algebra Ξ±)(h : X β β£ π¨ β£) β β£ π» X β£ β β£ π¨ β£
  free-lift _ h (β x) = h x
  free-lift π¨ h (node f π‘) = (f Μ π¨) (Ξ» i β free-lift π¨ h (π‘ i))

Naturally, at the base step of the induction, when the term has the form
``generator`` x, the free lift of ``h`` agrees with ``h``. For the inductive step,
when the given term has the form ``node f π‘``, the free lift is defined as
follows: Assuming (the induction hypothesis) that we know the image of each
subterm ``π‘ i`` under the free lift of ``h``, define the free lift at the full
term by applying ``f Μ π¨`` to the images of the subterms.

The free lift so defined is a homomorphism by construction. Indeed, here is the
trivial proof.

::

  lift-hom : (π¨ : Algebra Ξ±) β (X β β£ π¨ β£) β hom (π» X) π¨
  lift-hom π¨ h = free-lift π¨ h , Ξ» f a β β‘.cong (f Μ π¨) β‘.refl

Finally, we prove that the homomorphism is unique. This requires ``funext π₯ Ξ±``
(i.e., *function extensionality* at universe levels ``π₯`` and ``Ξ±``) which we
postulate by making it part of the premise in the following function type
definition.

::

  open β‘-Reasoning

  free-unique :  swelldef π₯ Ξ± β (π¨ : Algebra Ξ±)(g h : hom (π» X) π¨)
   β             (β x β β£ g β£ (β x) β‘ β£ h β£ (β x))
   β             β(t : Term X) β  β£ g β£ t β‘ β£ h β£ t

  free-unique _ _ _ _ p (β x) = p x

  free-unique wd π¨ g h p (node π π‘) =
   β£ g β£ (node π π‘)    β‘β¨ β₯ g β₯ π π‘ β©
   (π Μ π¨)(β£ g β£ β π‘)  β‘β¨ Goal β©
   (π Μ π¨)(β£ h β£ β π‘)  β‘β¨ (β₯ h β₯ π π‘)β»ΒΉ β©
   β£ h β£ (node π π‘)    β
    where
    Goal : (π Μ π¨) (Ξ» x β β£ g β£ (π‘ x)) β‘ (π Μ π¨) (Ξ» x β β£ h β£ (π‘ x))
    Goal = wd (π Μ π¨)(β£ g β£ β π‘)(β£ h β£ β π‘)(Ξ» i β free-unique wd π¨ g h p (π‘ i))

Let's account for what we have proved thus far about the term algebra. If we
postulate a type ``X : Type Ο`` (representing an arbitrary collection of variable
symbols) such that for each ``π``-algebra ``π¨`` there is a map from ``X`` to the
domain of ``π¨``, then it follows that for every ``π``-algebra ``π¨`` there is a
homomorphism from ``π» X`` to ``β£ π¨ β£`` that "agrees with the original map on
``X``," by which we mean that for all ``x : X`` the lift evaluated at ``β x`` is
equal to the original function evaluated at ``x``.

If we further assume that each of the mappings from ``X`` to ``β£ π¨ β£`` is
*surjective*, then the homomorphisms constructed with ``free-lift`` and
``lift-hom`` are *epimorphisms*, as we now prove.

::

  lift-of-epi-is-epi :  (π¨ : Algebra Ξ±){hβ : X β β£ π¨ β£}
   β                    IsSurjective hβ β IsSurjective β£ lift-hom π¨ hβ β£

  lift-of-epi-is-epi π¨ {hβ} hE y = Goal
   where
   hββ»ΒΉy = Inv hβ (hE y)

   Ξ· : y β‘ β£ lift-hom π¨ hβ β£ (β hββ»ΒΉy)
   Ξ· = (InvIsInverseΚ³ (hE y))β»ΒΉ

   Goal : Image β£ lift-hom π¨ hβ β£ β y
   Goal = eq (β hββ»ΒΉy) Ξ·

The ``lift-hom`` and ``lift-of-epi-is-epi`` types will be called to action when
such epimorphisms are needed later (e.g., in the `Base.Varieties`_ module).




