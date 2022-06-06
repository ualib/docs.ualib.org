3. Fatal issue: The assumption XX (black-board X) in the module
Birkhoff.HSPTheorem is inconsistent.

Under the assumption XX, we can prove absurdity:

\begin{code}

-- Declare empty and unit type.

data ⊥ : Set where
record ⊤ : Set where

-- Every signature admits the one-point algebra.

One : Algebra _ S
One = (⊤ , λ f x → _)

-- The type of surjections from 0 to One.

Surj01 = ⊥ Algebras.Algebras.↠ One

-- Assumption XX includes such a surjection.

surj01 : Surj01
surj01 = XX {X = ⊥}  One

-- But the existence of such a surjection is absurd.

no-surj01 : Surj01 → ⊥
no-surj01 (pr₃ , pr₄) with pr₄ _
... | Relations.Unary.im x = x
... | Relations.Unary.eq _ a x = a

-- BOOM!

absurd : ⊥
absurd = no-surj01 surj01

\end{code}

