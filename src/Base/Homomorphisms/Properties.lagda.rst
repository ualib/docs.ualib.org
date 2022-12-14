.. FILE      : Base/Homomorphisms/Properties.lagda.rst
.. AUTHOR    : William DeMeo
.. DATE      : 08 Sep 2021
.. UPDATED   : 23 Jun 2022

.. highlight:: agda
.. role:: code

.. _base-homomorphisms-properties-of-homomorphisms:

Properties of Homomorphisms
~~~~~~~~~~~~~~~~~~~~~~~~~~~

This is the `Base.Homomorphisms.Properties`_ module of the `Agda Universal Algebra Library`_.

::

  {-# OPTIONS --without-K --exact-split --safe #-}

  open import Overture using (Signature ; ๐ ; ๐ฅ )

  module Base.Homomorphisms.Properties {๐ : Signature ๐ ๐ฅ} where

  -- Imports from Agda and the Agda Standard Library --------------------------------
  open import Data.Product  using ( _,_ )
  open import Function      using ( _โ_ )
  open import Level         using ( Level )

  open  import Relation.Binary.PropositionalEquality as โก
        using ( _โก_ ; module โก-Reasoning )

  -- Imports from the Agda Universal Algebras Library --------------------------------
  open import Overture                           using ( โฃ_โฃ ; โฅ_โฅ )
  open import Base.Algebras             {๐ = ๐}  using ( Algebra ; _ฬ_ ; Lift-Alg )
  open import Base.Homomorphisms.Basic  {๐ = ๐}  using ( hom ; is-homomorphism )

  private variable ฮฑ ฮฒ ฮณ ฯ : Level

.. _base-homomorphisms-homomorphism-composition:

Homomorphism composition
^^^^^^^^^^^^^^^^^^^^^^^^

The composition of homomorphisms is again a homomorphism. We formalize this in a number of alternative ways.

::

  open โก-Reasoning

  module _ (๐จ : Algebra ฮฑ){๐ฉ : Algebra ฮฒ}(๐ช : Algebra ฮณ) where

    โ-hom : hom ๐จ ๐ฉ  โ  hom ๐ฉ ๐ช  โ  hom ๐จ ๐ช
    โ-hom (g , ghom) (h , hhom) = h โ g , Goal where

     Goal : โ ๐ a โ (h โ g)((๐ ฬ ๐จ) a) โก (๐ ฬ ๐ช)(h โ g โ a)
     Goal ๐ a =  (h โ g)((๐ ฬ ๐จ) a)  โกโจ โก.cong h ( ghom ๐ a )  โฉ
                 h ((๐ ฬ ๐ฉ)(g โ a))  โกโจ hhom ๐ ( g โ a )       โฉ
                 (๐ ฬ ๐ช)(h โ g โ a)  โ

    โ-is-hom :  {f : โฃ ๐จ โฃ โ โฃ ๐ฉ โฃ}{g : โฃ ๐ฉ โฃ โ โฃ ๐ช โฃ}
     โ          is-homomorphism ๐จ ๐ฉ f โ is-homomorphism ๐ฉ ๐ช g
     โ          is-homomorphism ๐จ ๐ช (g โ f)

    โ-is-hom {f} {g} fhom ghom = โฅ โ-hom (f , fhom) (g , ghom) โฅ

A homomorphism from ``๐จ`` to ``๐ฉ`` can be lifted to a homomorphism from
``Lift-Alg ๐จ โแต`` to ``Lift-Alg ๐ฉ โแต``. 

::

  open Level

  Lift-hom :  {๐จ : Algebra ฮฑ}(โแต : Level){๐ฉ : Algebra ฮฒ} (โแต : Level)
   โ          hom ๐จ ๐ฉ  โ  hom (Lift-Alg ๐จ โแต) (Lift-Alg ๐ฉ โแต)

  Lift-hom {๐จ = ๐จ} โแต {๐ฉ} โแต (f , fhom) = lift โ f โ lower , Goal
   where
   lABh : is-homomorphism (Lift-Alg ๐จ โแต) ๐ฉ (f โ lower)
   lABh = โ-is-hom (Lift-Alg ๐จ โแต) ๐ฉ {lower}{f} (ฮป _ _ โ โก.refl) fhom

   Goal : is-homomorphism(Lift-Alg ๐จ โแต)(Lift-Alg ๐ฉ โแต) (lift โ (f โ lower))
   Goal = โ-is-hom  (Lift-Alg ๐จ โแต) (Lift-Alg ๐ฉ โแต)
                    {f โ lower}{lift} lABh ฮป _ _ โ โก.refl

We should probably point out that while the lifting and lowering homomorphisms
are important for our formal treatment of algebras in type theory, they never
ariseโin fact, they are not even definableโin classical universal algebra based
on set theory.

