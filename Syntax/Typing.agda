module Syntax.Typing where
open import Semantics
open import Semantics.FibrationEqTwoCongThree
open import Syntax.Context
open import Syntax.Variable

data _⊢₃_gpd : ∀ Γ → Fibration₂ ⟦ Γ ⟧C → Set where
  -eq- : ∀ {Γ G H} → Γ ⊢₃ G gpd → Γ ⊢₃ H gpd → Γ ⊢₃ Fibration-Eq₂ G H gpd
  
data _⊢₂_∋_ : ∀ Γ (G : Fibration₂ ⟦ Γ ⟧C) → Section₂ G → Set where
  -var- : ∀ {Γ T ⟦x⟧} → Γ var₂ T ∋ ⟦x⟧ → Γ ⊢₂ T ∋ ⟦x⟧
  -eq*- : ∀ {Γ ⟦G⟧ ⟦G'⟧ ⟦H⟧ ⟦H'⟧ ⟦G*⟧ ⟦H*⟧} →
    Γ ⊢₂ Fibration-Eq₂ ⟦G⟧ ⟦G'⟧ ∋ ⟦G*⟧ → Γ ⊢₂ Fibration-Eq₂ ⟦H⟧ ⟦H'⟧ ∋ ⟦H*⟧ →
    Γ ⊢₂ Fibration-Eq₂ (Fibration-Eq₂ ⟦G⟧ ⟦H⟧) (Fibration-Eq₂ ⟦G'⟧ ⟦H'⟧) ∋ Fibration-Eq₂-cong ⟦G*⟧ ⟦H*⟧
  -eqp- : ∀ {Γ ⟦G⟧ ⟦H⟧ ⟦s⟧ ⟦e⟧ ⟦t⟧} → Γ ⊢₂ ⟦G⟧ ∋ ⟦s⟧ → Γ ⊢₂ Fibration-Eq₂ ⟦G⟧ ⟦H⟧ ∋ ⟦e⟧ → Γ ⊢₂ ⟦G⟧ ∋ ⟦t⟧ →
        Γ ⊢₂ Sets ∋ ?

--TODO Relabel with cubical notation
data _⊢₁_∋_ : ∀ Γ (S : Fibration₁ ⟦ Γ ⟧C) → Section₁ S → Set where
  -var- : ∀ {Γ T ⟦x⟧} → Γ var₁ T ∋ ⟦x⟧ → Γ ⊢₁ T ∋ ⟦x⟧

data _⊢₀_∋_ : ∀ Γ (P : Fibration₀ ⟦ Γ ⟧C) → Section₀ P → Set where
  -var- : ∀ {Γ P ⟦x⟧} → Γ var₀ P ∋ ⟦x⟧ → Γ ⊢₀ P ∋ ⟦x⟧
