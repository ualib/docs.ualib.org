.. FILE      : Base/Homomorphisms/Kernels.lagda.rst
.. AUTHOR    : William DeMeo
.. DATE      : 08 Sep 2021
.. UPDATED   : 23 Jun 2022

.. highlight:: agda
.. role:: code

.. _base-homomorphisms-kernels-of-homomorphisms:

Kernels of Homomorphisms
~~~~~~~~~~~~~~~~~~~~~~~~

This is the `Base.Homomorphisms.Kernels`_ module of the `Agda Universal Algebra Library`_.

::

  {-# OPTIONS --without-K --exact-split --safe #-}

  open import Overture using ( Signature; ð ; ð¥ )

  module Base.Homomorphisms.Kernels {ð : Signature ð ð¥} where

  -- Imports from Agda and the Agda Standard Library --------------------------------
  open import Data.Product   using ( _,_ )
  open import Function.Base  using ( _â_ )
  open import Level          using ( Level ; _â_ ; suc )

  open  import Relation.Binary.PropositionalEquality
        using ( _â¡_ ; module â¡-Reasoning ; refl )

  -- Imports from the Agda Universal Algebras Library --------------------------------
  open import Overture        using ( â£_â£ ; â¥_â¥ ; _â»Â¹ )
  open import Base.Functions  using ( Image_â_ ; IsSurjective )
  open import Base.Equality   using ( swelldef )
  open import Base.Relations  using ( ker ; ker-IsEquivalence ; âª_â« ; mkblk )

  open  import Base.Algebras {ð = ð}
        using ( Algebra ; compatible ; _Ì_ ; Con ; mkcon ; _â±_ ; IsCongruence ; /-â¡ )

  open import Base.Homomorphisms.Basic {ð = ð}  using ( hom ; epi ; epiâhom )

  private variable Î± Î² : Level

.. _base-homomorphisms-definition:

Definition
^^^^^^^^^^

The kernel of a homomorphism is a congruence relation and conversely for every
congruence relation Î¸, there exists a homomorphism with kernel Î¸ (namely, that
canonical projection onto the quotient modulo Î¸). 

::

  module _ {ð¨ : Algebra Î±} where
   open â¡-Reasoning
   homker-comp :  swelldef ð¥ Î² â {ð© : Algebra Î²}(h : hom ð¨ ð©)
    â             compatible ð¨ (ker â£ h â£)

   homker-comp wd {ð©} h f {u}{v} kuv =
    â£ h â£((f Ì ð¨) u)    â¡â¨ â¥ h â¥ f u â©
    (f Ì ð©)(â£ h â£ â u)  â¡â¨ wd(f Ì ð©)(â£ h â£ â u)(â£ h â£ â v)kuv â©
    (f Ì ð©)(â£ h â£ â v)  â¡â¨ (â¥ h â¥ f v)â»Â¹ â©
    â£ h â£((f Ì ð¨) v)    â



(Notice, it is here that the ``swelldef`` postulate comes into play, and because
it is needed to prove ``homker-comp``, it is postulated by all the lemmas below
that depend upon ``homker-comp``.)

It is convenient to define a function that takes a homomorphism and constructs a
congruence from its kernel. We call this function ``kercon``.

::

   kercon : swelldef ð¥ Î² â {ð© : Algebra Î²} â hom ð¨ ð© â Con{Î±}{Î²} ð¨
   kercon wd {ð©} h = ker â£ h â£ , mkcon (ker-IsEquivalence â£ h â£)(homker-comp wd {ð©} h)


With this congruence we construct the corresponding quotient, along with some
syntactic sugar to denote it.

::

   kerquo : swelldef ð¥ Î² â {ð© : Algebra Î²} â hom ð¨ ð© â Algebra (Î± â suc Î²)
   kerquo wd {ð©} h = ð¨ â± (kercon wd {ð©} h)

::

  ker[_â_]_â¾_ :  (ð¨ : Algebra Î±)(ð© : Algebra Î²) â hom ð¨ ð© â swelldef ð¥ Î²
   â             Algebra (Î± â suc Î²)

  ker[ ð¨ â ð© ] h â¾ wd = kerquo wd {ð©} h
  
Thus, given ``h : hom ð¨ ð©``, we can construct the quotient of ``ð¨`` modulo the
kernel of ``h``, and the syntax for this quotient in the agda-algebras_ library
is ``ð¨ [ ð© ]/ker h â¾ fe``.

.. _base-homomorphisms-the-canonical-projection:

The canonical projection
^^^^^^^^^^^^^^^^^^^^^^^^

Given an algebra ``ð¨`` and a congruence ``Î¸``, the *canonical projection* is a
map from ``ð¨`` onto ``ð¨ â± Î¸`` that is constructed, and proved epimorphic, as
follows.

::

  module _ {Î± Î² : Level}{ð¨ : Algebra Î±} where
   Ïepi : (Î¸ : Con{Î±}{Î²} ð¨) â epi ð¨ (ð¨ â± Î¸)
   Ïepi Î¸ = (Î» a â âª a â«) , (Î» _ _ â refl) , cÏ-is-epic  where
    cÏ-is-epic : IsSurjective (Î» a â âª a â«)
    cÏ-is-epic (C , mkblk a refl ) =  Image_â_.eq a refl

In may happen that we donât care about the surjectivity of ``Ïepi``, in which
case would might prefer to work with the *homomorphic reduct* of ``Ïepi``. This
is obtained by applying ``epi-to-hom``, like so. 

::

   Ïhom : (Î¸ : Con{Î±}{Î²} ð¨) â hom ð¨ (ð¨ â± Î¸)
   Ïhom Î¸ = epiâhom (ð¨ â± Î¸) (Ïepi Î¸)

We combine the foregoing to define a function that takes ð-algebras ``ð¨`` and
``ð©``, and a homomorphism ``h : hom ð¨ ð©`` and returns the canonical epimorphism
from ``ð¨`` onto ``ð¨ [ ð© ]/ker h``. (Recall, the latter is the special notation
we defined above for the quotient of ``ð¨`` modulo the kernel of ``h``.)

::

   Ïker :  (wd : swelldef ð¥ Î²){ð© : Algebra Î²}(h : hom ð¨ ð©)
    â      epi ð¨ (ker[ ð¨ â ð© ] h â¾ wd)

   Ïker wd {ð©} h = Ïepi (kercon wd {ð©} h)

The kernel of the canonical projection of ``ð¨`` onto ``ð¨ / Î¸`` is equal to
``Î¸``, but since equality of inhabitants of certain types (like ``Congruence``
or ``Rel``) can be a tricky business, we settle for proving the containment ``ð¨
/ Î¸ â Î¸``. Of the two containments, this is the easier one to prove; luckily it
is also the one we need later.

::

   open IsCongruence

   ker-in-con :  {wd : swelldef ð¥ (Î± â suc Î²)}(Î¸ : Con ð¨)
    â            â {x}{y} â â£ kercon wd {ð¨ â± Î¸} (Ïhom Î¸) â£ x y â  â£ Î¸ â£ x y

   ker-in-con Î¸ hyp = /-â¡ Î¸ hyp
