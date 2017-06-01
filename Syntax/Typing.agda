module Syntax.Typing where
open import Semantics
open import Syntax.Context
open import Syntax.Variable

data _⊢_gpd : ∀ Γ → Fibration₂ ⟦ Γ ⟧C → Set where

data _⊢₂_∋_ : ∀ Γ (G : Fibration₂ ⟦ Γ ⟧C) → Section₂ G → Set where
  -var- : ∀ {Γ T ⟦x⟧} → Γ ∋₂ T ≡ ⟦x⟧ → Γ ⊢₂ T ∋ ⟦x⟧
--TODO Make notation consistent

data _⊢₁_∋_ : ∀ Γ (S : Fibration₁ ⟦ Γ ⟧C) → Section₁ S → Set where
  -var- : ∀ {Γ T ⟦x⟧} → Γ ∋₁ T ≡ ⟦x⟧ → Γ ⊢₁ T ∋ ⟦x⟧

data _⊢₀_∋_ : ∀ Γ (P : Fibration₀ ⟦ Γ ⟧C) → Section₀ P → Set where
  -var- : ∀ {Γ P ⟦x⟧} → Γ ∋₀ P ≡ ⟦x⟧ → Γ ⊢₀ P ∋ ⟦x⟧

