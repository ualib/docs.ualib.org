.. FILE      : Base/Varieties/Properties.lagda.rst
.. AUTHOR    : William DeMeo
.. DATE      : 24 Jun 2021
.. UPDATED   : 23 Jun 2022

.. highlight:: agda
.. role:: code

.. _base-varieties-properties-of-the-models-relation:

Properties of the models relation
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

We prove some closure and invariance properties of the relation ``β§``. In
particular, we prove the following facts (which we use later in our proof of
Birkhoff's HSP Theorem).

-  `Algebraic invariance <#algebraic-invariance>`__. ``β§`` is an
   *algebraic invariant* (stable under isomorphism).

-  `Subalgebraic invariance <#subalgebraic-invariance>`__. Identities
   modeled by a class of algebras are also modeled by all subalgebras of
   algebras in the class.

-  `Product invariance <#product-invariance>`__. Identities modeled by a class
   of algebras are also modeled by all products of algebras in the class.

::

  {-# OPTIONS --without-K --exact-split --safe #-}

  open import Overture using ( π ; π₯ ; Signature )

  module Base.Varieties.Properties {π : Signature π π₯} where

  -- Imports from Agda and the Agda Standard Library -----------------------------
  open import Agda.Primitive  using () renaming ( Set to Type )
  open import Data.Product    using ( _,_ ; Ξ£-syntax ; _Γ_ )
                              renaming ( projβ to fst ; projβ to snd )
  open import Function        using ( _β_ )
  open import Level           using ( Level ; _β_ )
  open import Relation.Unary  using ( Pred ; _β_ ; _β_ ; β )
  open import Axiom.Extensionality.Propositional
                              using () renaming ( Extensionality to funext )
  open import Relation.Binary.PropositionalEquality
                              using ( _β‘_ ; refl ; module β‘-Reasoning ; cong )

  -- Imports from the Agda Universal Algebra Library -----------------------------
  open import Overture                     using ( β£_β£ ; β₯_β₯ ; _β»ΒΉ )
  open import Base.Functions               using ( IsInjective ; β-injective )
  open import Base.Equality                using ( SwellDef ; DFunExt )
  open import Base.Algebras       {π = π}  using ( Algebra ; Lift-Alg ; ov ; β¨ )
  open import Base.Homomorphisms  {π = π}  using ( hom ; β-hom ; _β_ ; mkiso )
                                           using ( Lift-β ; β-sym ; β-trans )
  open import Base.Terms          {π = π}  using ( Term ; π» ; lift-hom ; _β¦_β§ )
                                           using ( comm-hom-term ; interp-prod )
                                           using ( term-agreement )
  open import Base.Subalgebras    {π = π}  using ( _β€_ ; SubalgebraOfClass )
                                           using ( isoβinjective )
  open import Base.Varieties.EquationalLogic
                                  {π = π}  using ( _β§_β_ ; _β«_β_ )

.. _base-varieties-algebraic-invariance-of-models

Algebraic invariance of ``β§``
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

The binary relation ``β§`` would be practically useless if it were not an
*algebraic invariant* (invariant under isomorphism).

::

  open Term
  open β‘-Reasoning
  open _β_

  module _  (wd : SwellDef){Ξ± Ξ² Ο : Level}{X : Type Ο}{π¨ : Algebra Ξ±}
            (π© : Algebra Ξ²)(p q : Term X) where

   β§-I-invar : π¨ β§ p β q  β  π¨ β π©  β  π© β§ p β q

   β§-I-invar Apq (mkiso f g fβΌg gβΌf) x =
    (π© β¦ p β§) x                       β‘β¨ i p β©
    (π© β¦ p β§) ((β£ f β£ β β£ g β£) β x)   β‘β¨ (ii p) β»ΒΉ β©
    β£ f β£ ((π¨ β¦ p β§) (β£ g β£ β x))     β‘β¨ cong β£ f β£ (Apq (β£ g β£ β x))  β©
    β£ f β£ ((π¨ β¦ q β§) (β£ g β£ β x))     β‘β¨ ii q β©
    (π© β¦ q β§) ((β£ f β£ β β£ g β£) β  x)  β‘β¨ (i q)β»ΒΉ β©
    (π© β¦ q β§) x                       β
    where
    i : β t β (π© β¦ t β§) x β‘ (π© β¦ t β§) Ξ» xβ β β£ f β£ (β£ g β£ (x xβ))
    i t = wd Ο Ξ² (π© β¦ t β§) x (β£ f β£ β β£ g β£ β x) Ξ» i β ( fβΌg (x i))β»ΒΉ

    ii :  β t
     β    β£ f β£((π¨ β¦ t β§) Ξ» xβ β β£ g β£(x xβ)) β‘ (π© β¦ t β§) Ξ» xβ β β£ f β£(β£ g β£(x xβ))
    ii t = comm-hom-term (wd π₯ Ξ²) π© f t (β£ g β£ β x)


In the above proof we showed ``π© β§ p β q`` by showing that ``π© β¦ p β§ β‘ π© β¦ q β§``
holds *extensionally*, that is, ``β x, π© β¦ p β§ x β‘ π© β¦q β§ x``.

.. _base-varieties-lift-invariance-of-models:

Lift-invariance of ``β§``
^^^^^^^^^^^^^^^^^^^^^^^^

The ``β§`` relation is also invariant under the algebraic lift and lower operations.

::

  module _ (wd : SwellDef){Ξ± Ξ² Ο : Level}{X : Type Ο}{π¨ : Algebra Ξ±} where

   β§-Lift-invar : (p q : Term X) β π¨ β§ p β q β Lift-Alg π¨ Ξ² β§ p β q
   β§-Lift-invar p q Apq = β§-I-invar wd (Lift-Alg π¨ _) p q Apq Lift-β

   β§-lower-invar : (p q : Term X) β Lift-Alg π¨ Ξ² β§ p β q  β  π¨ β§ p β q
   β§-lower-invar p q lApq = β§-I-invar wd π¨ p q lApq (β-sym Lift-β)

.. _base-varieties-subalgebraic-invariance-of-models:

Subalgebraic invariance of ``β§``
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

Identities modeled by an algebra ``π¨`` are also modeled by every subalgebra of
``π¨``, which fact can be formalized as follows.

::

  module _ (wd : SwellDef){Ο : Level}{π€ π¦ : Level}{X : Type Ο} where

   β§-S-invar : {π¨ : Algebra π€}(π© : Algebra π¦){p q : Term X}
    β          π¨ β§ p β q  β  π© β€ π¨  β  π© β§ p β q
   β§-S-invar {π¨} π© {p}{q} Apq Bβ€A b = (β₯ Bβ€A β₯) (ΞΎ b)
    where
    h : hom π© π¨
    h = β£ Bβ€A β£

    ΞΎ : β b β β£ h β£ ((π© β¦ p β§) b) β‘ β£ h β£ ((π© β¦ q β§) b)
    ΞΎ b =  β£ h β£((π© β¦ p β§) b)    β‘β¨ comm-hom-term (wd π₯ π€) π¨ h p b β©
           (π¨ β¦ p β§)(β£ h β£ β b)  β‘β¨ Apq (β£ h β£ β b) β©
           (π¨ β¦ q β§)(β£ h β£ β b)  β‘β¨ (comm-hom-term (wd π₯ π€) π¨ h q b)β»ΒΉ β©
           β£ h β£((π© β¦ q β§) b)    β

Next, identities modeled by a class of algebras is also modeled by all subalgebras
of the class. In other terms, every term equation ``p β q`` that is satisfied by
all ``π¨ β π¦`` is also satisfied by every subalgebra of a member of ``π¦``.

::

   β§-S-class-invar :  {π¦ : Pred (Algebra π€)(ov π€)}(p q : Term X)
    β                 π¦ β« p β q β (π© : SubalgebraOfClass π¦) β β£ π© β£ β§ p β q

   β§-S-class-invar p q Kpq (π© , π¨ , SA , (ka , BβSA)) =
    β§-S-invar π© {p}{q}((Kpq ka)) (h , hinj)
     where
     h : hom π© π¨
     h = β-hom π© π¨ (to BβSA) β£ snd SA β£
     hinj : IsInjective β£ h β£
     hinj = β-injective (isoβinjective BβSA) β₯ snd SA β₯

.. _base-varieties-product-invariance-of-models:

Product invariance of ``β§``
^^^^^^^^^^^^^^^^^^^^^^^^^^^

An identity satisfied by all algebras in an indexed collection is also satisfied
by the product of algebras in that collection.

::

  module _  (fe : DFunExt)(wd : SwellDef)
            {Ξ± Ξ² Ο : Level}{I : Type Ξ²}
            (π : I β Algebra Ξ±){X : Type Ο} where

   β§-P-invar : (p q : Term X) β (β i β π i β§ p β q) β β¨ π β§ p β q
   β§-P-invar p q πpq a = goal
    where
    -- This is where function extensionality is used.
    ΞΎ : (Ξ» i β (π i β¦ p β§) (Ξ» x β (a x) i)) β‘ (Ξ» i β (π i β¦ q β§)  (Ξ» x β (a x) i))
    ΞΎ = fe Ξ² Ξ± Ξ» i β πpq i (Ξ» x β (a x) i)

    goal : (β¨ π β¦ p β§) a  β‘  (β¨ π β¦ q β§) a
    goal =  (β¨ π β¦ p β§) a                      β‘β¨ interp-prod (wd π₯ (Ξ± β Ξ²)) p π a β©
            (Ξ» i β (π i β¦ p β§)(Ξ» x β (a x)i))  β‘β¨ ΞΎ β©
            (Ξ» i β (π i β¦ q β§)(Ξ» x β (a x)i))  β‘β¨ (interp-prod (wd π₯ (Ξ± β Ξ²)) q π a)β»ΒΉ β©
            (β¨ π β¦ q β§) a                      β


An identity satisfied by all algebras in a class is also satisfied by the product
of algebras in the class.

::

   β§-P-class-invar :  (π¦ : Pred (Algebra Ξ±)(ov Ξ±)){p q : Term X}
    β                 π¦ β« p β q β (β i β π i β π¦) β β¨ π β§ p β q

   β§-P-class-invar π¦ {p}{q}Ο Kπ = β§-P-invar p q Ξ» i β Ο (Kπ i)

Another fact that will turn out to be useful is that a product of a collection of
algebras models p β q if the lift of each algebra in the collection models ``p β q``.

::

   β§-P-lift-invar : (p q : Term X) β (β i β Lift-Alg (π i) Ξ² β§ p β q)  β  β¨ π β§ p β q
   β§-P-lift-invar p q Ξ± = β§-P-invar p q Aipq
    where
    Aipq : β i β (π i) β§ p β q
    Aipq i = β§-lower-invar wd p q (Ξ± i)

.. _base-varieties-homomorphic-invariance-of-models:

Homomorphic invariance of ``β§``
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

If an algebra ``π¨`` models an identity ``p β q``, then the pair ``(p , q)``
belongs to the kernel of every homomorphism ``Ο : hom (π» X) π¨`` from the term
algebra to ``π¨``; that is, every homomorphism from ``π» X`` to ``π¨`` maps ``p`` and
``q`` to the same element of ``π¨``.
::

  module _ (wd : SwellDef){Ξ± Ο : Level}{X : Type Ο}{π¨ : Algebra Ξ±} where

   β§-H-invar : {p q : Term X}(Ο : hom (π» X) π¨) β π¨ β§ p β q  β  β£ Ο β£ p β‘ β£ Ο β£ q

   β§-H-invar {p}{q}Ο Ξ² =  β£ Ο β£ p                β‘β¨ i p β©
                          β£ Ο β£((π» X β¦ p β§) β)   β‘β¨ ii p β©
                          (π¨ β¦ p β§) (β£ Ο β£ β β)  β‘β¨ Ξ² (β£ Ο β£ β β ) β©
                          (π¨ β¦ q β§) (β£ Ο β£ β β)  β‘β¨ (ii q)β»ΒΉ β©
                          β£ Ο β£ ((π» X β¦ q β§) β)  β‘β¨ (i q)β»ΒΉ β©
                          β£ Ο β£ q                β

    where
    i : β t β β£ Ο β£ t β‘ β£ Ο β£ ((π» X β¦ t β§) β)
    i t = cong β£ Ο β£(term-agreement(wd π₯ (ov Ο)) t)
    ii : β t β β£ Ο β£ ((π» X β¦ t β§) β) β‘ (π¨ β¦ t β§) (Ξ» x β β£ Ο β£ (β x))
    ii t = comm-hom-term (wd π₯ Ξ±) π¨ Ο t β

More generally, an identity is satisfied by all algebras in a class if and only if
that identity is invariant under all homomorphisms from the term algebra ``π» X``
into algebras of the class. More precisely, if ``π¦`` is a class of ``π``-algebras
and ``π``, ``π`` terms in the language of ``π``, then,

.. code:: agda

   π¦ β§ p β q  β  β π¨ β π¦,  β Ο : hom (π» X) π¨,  Ο β (π» X)β¦ p β§ = Ο β (π» X)β¦ q β§.

::

  module _ (wd : SwellDef){Ξ± Ο : Level}{X : Type Ο}{π¦ : Pred (Algebra Ξ±)(ov Ξ±)}  where

   -- β (the "only if" direction)
   β§-H-class-invar :  {p q : Term X}
    β                 π¦ β« p β q β β π¨ Ο β π¨ β π¦ β β a
    β                 β£ Ο β£ ((π» X β¦ p β§) a) β‘ β£ Ο β£ ((π» X β¦ q β§) a)

   β§-H-class-invar {p = p}{q} Ο π¨ Ο ka a = ΞΎ
    where
     ΞΎ : β£ Ο β£ ((π» X β¦ p β§) a) β‘ β£ Ο β£ ((π» X β¦ q β§) a)
     ΞΎ =  β£ Ο β£ ((π» X β¦ p β§) a)  β‘β¨ comm-hom-term (wd π₯ Ξ±) π¨ Ο p a β©
          (π¨ β¦ p β§)(β£ Ο β£ β a)   β‘β¨ (Ο ka) (β£ Ο β£ β a) β©
          (π¨ β¦ q β§)(β£ Ο β£ β a)   β‘β¨ (comm-hom-term (wd π₯ Ξ±) π¨ Ο q a)β»ΒΉ β©
          β£ Ο β£ ((π» X β¦ q β§) a)  β

   -- β (the "if" direction)
   β§-H-class-coinvar :  {p q : Term X}
    β                   (β π¨ Ο β π¨ β π¦ β β a β β£ Ο β£ ((π» X β¦ p β§) a) β‘ β£ Ο β£ ((π» X β¦ q β§) a))
    β                   π¦ β« p β q

   β§-H-class-coinvar {p}{q} Ξ² {π¨} ka = goal
    where
    Ο : (a : X β β£ π¨ β£) β hom (π» X) π¨
    Ο a = lift-hom π¨ a

    goal : π¨ β§ p β q
    goal a =  (π¨ β¦ p β§)(β£ Ο a β£ β β)     β‘β¨(comm-hom-term (wd π₯ Ξ±) π¨ (Ο a) p β)β»ΒΉ β©
              (β£ Ο a β£ β (π» X β¦ p β§)) β  β‘β¨ Ξ² π¨ (Ο a) ka β β©
              (β£ Ο a β£ β (π» X β¦ q β§)) β  β‘β¨ (comm-hom-term (wd π₯ Ξ±) π¨ (Ο a) q β) β©
              (π¨ β¦ q β§)(β£ Ο a β£ β β)     β
