module Semantics.Groupoid where

--Groupoids
postulate Groupoid : Set
postulate Obj : Groupoid → Set

postulate ONE : Groupoid
postulate Sets : Groupoid

--Fibrations of groupoids over groupoids
postulate Groupoid-Fibration : Groupoid → Set
postulate K : ∀ G → Groupoid → Groupoid-Fibration G
postulate Sigma₂ : ∀ G → Groupoid-Fibration G → Groupoid
postulate Section : ∀ {G} → Groupoid-Fibration G → Set

--Sets
postulate Props : Obj Sets

--Fibrations of Sets over Groupoids
Set-Fibration : Groupoid → Set
Set-Fibration G = Section (K G Sets)

postulate K₀ : ∀ G → Obj Sets → Set-Fibration G
postulate Sigma₁ : ∀ G → Set-Fibration G → Groupoid
postulate Section₁ : ∀ {G} → Set-Fibration G → Set

--Fibrations of Propositions over Groupoids
Prop-Fibration : Groupoid → Set
Prop-Fibration G = Section₁ (K₀ G Props)

postulate Sigma₀ : ∀ G → Prop-Fibration G → Groupoid



