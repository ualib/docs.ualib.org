.. FILE      : Base/Homomorphisms/HomomorphicImages.lagda.rst
.. AUTHOR    : William DeMeo
.. DATE      : 14 Jan 2021
.. UPDATED   : 23 Jun 2022

.. highlight:: agda
.. role:: code

.. _basic-homomorphisms-homomorphic-images:

Homomorphic Images
~~~~~~~~~~~~~~~~~~

This is the `Base.Homomorphisms.HomomorphicImages`_ module of the `Agda Universal Algebra Library`_.

::

  {-# OPTIONS --without-K --exact-split --safe #-}

  open import Overture using ( Signature ; π ; π₯ )

  module Base.Homomorphisms.HomomorphicImages {π : Signature π π₯} where

  -- Imports from Agda and the Agda Standard Library ------------------------------------------
  open import Agda.Primitive  using () renaming ( Set to Type )
  open import Data.Product    using ( _,_ ; Ξ£-syntax ; Ξ£ ; _Γ_ )
  open import Level           using ( Level ;  _β_ ; suc )
  open import Relation.Unary  using ( Pred ; _β_ )
  open import Relation.Binary.PropositionalEquality as β‘
                              using ( _β‘_ ; module β‘-Reasoning )

  -- Imports from the Agda Universal Algebra Library ------------------------------------------
  open import Overture  using ( ππ ; β£_β£ ; β₯_β₯ ; lowerβΌlift ; liftβΌlower )
  open import Base.Functions
                        using ( Image_β_ ; Inv ; InvIsInverseΚ³ ; eq ; IsSurjective )
  open import Base.Algebras {π = π}
                        using ( Algebra ; Level-of-Carrier ; Lift-Alg ; ov )

  open import Base.Homomorphisms.Basic       {π = π} using ( hom ; ππΎπ»π ; πβ΄πβ―π )
  open import Base.Homomorphisms.Properties  {π = π} using ( Lift-hom )

.. _basic-homomorphisms-images-of-a-single-algebra:

Images of a single algebra
^^^^^^^^^^^^^^^^^^^^^^^^^^

We begin with what seems, for our purposes, the most useful way to represent the
class of *homomorphic images* of an algebra in dependent type theory.

::

  module _ {Ξ± Ξ² : Level } where

   _IsHomImageOf_ : (π© : Algebra Ξ²)(π¨ : Algebra Ξ±) β Type _
   π© IsHomImageOf π¨ = Ξ£[ Ο β hom π¨ π© ] IsSurjective β£ Ο β£

   HomImages : Algebra Ξ± β Type(π β π₯ β Ξ± β suc Ξ²)
   HomImages π¨ = Ξ£[ π© β Algebra Ξ² ] π© IsHomImageOf π¨

These types should be self-explanatory, but just to be sure, let's describe the
Sigma type appearing in the second definition. Given an ``π``-algebra
``π¨ : Algebra Ξ±``, the type ``HomImages π¨`` denotes the class of algebras
``π© : Algebra Ξ²`` with a map ``Ο : β£ π¨ β£ β β£ π© β£`` such that ``Ο`` is a
surjective homomorphism. 

.. _basic-homomorphisms-images-of-a-class-of-algebras:

Images of a class of algebras
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

Given a class ``π¦`` of ``π``-algebras, we need a type that expresses the assertion
that a given algebra is a homomorphic image of some algebra in the class, as well
as a type that represents all such homomorphic images.

::

  module _ {Ξ± : Level} where

   IsHomImageOfClass : {π¦ : Pred (Algebra Ξ±)(suc Ξ±)} β Algebra Ξ± β Type(ov Ξ±)
   IsHomImageOfClass {π¦ = π¦} π© = Ξ£[ π¨ β Algebra Ξ± ] ((π¨ β π¦) Γ (π© IsHomImageOf π¨))

   HomImageOfClass : Pred (Algebra Ξ±) (suc Ξ±) β Type(ov Ξ±)
   HomImageOfClass π¦ = Ξ£[ π© β Algebra Ξ± ] IsHomImageOfClass{π¦} π©

.. _basic-homomorphisms-lifting-tools:

Lifting tools
^^^^^^^^^^^^^

Here are some tools that have been useful (e.g., in the road to the proof of
Birkhoff's HSP theorem). The first states and proves the simple fact that the lift
of an epimorphism is an epimorphism. 

::

  module _ {Ξ± Ξ² : Level} where

   open Level
   open β‘-Reasoning

   Lift-epi-is-epi :  {π¨ : Algebra Ξ±}(βα΅ : Level){π© : Algebra Ξ²}(βα΅ : Level)(h : hom π¨ π©)
    β                 IsSurjective β£ h β£ β IsSurjective β£ Lift-hom βα΅ {π©} βα΅ h β£

   Lift-epi-is-epi {π¨ = π¨} βα΅ {π©} βα΅ h hepi y = eq (lift a) Ξ·
    where
     lh : hom (Lift-Alg π¨ βα΅) (Lift-Alg π© βα΅)
     lh = Lift-hom βα΅ {π©} βα΅ h

     ΞΆ : Image β£ h β£ β (lower y)
     ΞΆ = hepi (lower y)

     a : β£ π¨ β£
     a = Inv β£ h β£ ΞΆ

     Ξ½ : lift (β£ h β£ a) β‘ β£ Lift-hom βα΅ {π©} βα΅ h β£ (Level.lift a)
     Ξ½ = β‘.cong (Ξ» - β lift (β£ h β£ (- a))) (lowerβΌlift {Level-of-Carrier π¨}{Ξ²})

     Ξ· :  y β‘ β£ lh β£ (lift a)
     Ξ· =  y                β‘β¨ (β‘.cong-app liftβΌlower) y              β©
          lift (lower y)   β‘β¨ β‘.cong lift (β‘.sym (InvIsInverseΚ³ ΞΆ))  β©
          lift (β£ h β£ a)   β‘β¨ Ξ½                                      β©
          β£ lh β£ (lift a)  β

   Lift-Alg-hom-image :  {π¨ : Algebra Ξ±}(βα΅ : Level){π© : Algebra Ξ²}(βα΅ : Level)
    β                    π© IsHomImageOf π¨
    β                    (Lift-Alg π© βα΅) IsHomImageOf (Lift-Alg π¨ βα΅)

   Lift-Alg-hom-image {π¨ = π¨} βα΅ {π©} βα΅ ((Ο , Οhom) , Οepic) = Goal
    where
    lΟ : hom (Lift-Alg π¨ βα΅) (Lift-Alg π© βα΅)
    lΟ = Lift-hom βα΅ {π©} βα΅ (Ο , Οhom)

    lΟepic : IsSurjective β£ lΟ β£
    lΟepic = Lift-epi-is-epi βα΅ {π©} βα΅ (Ο , Οhom) Οepic
    Goal : (Lift-Alg π© βα΅) IsHomImageOf _
    Goal = lΟ , lΟepic
