module Syntax.Typing where
open import Semantics
open import Syntax.Context
open import Syntax.Variable

data _⊢gpd : Cx → Set where

data _⊢₂_ : ∀ Γ → Fibration₂ ⟦ Γ ⟧C → Set where
  -var- : ∀ {Γ} {T} → Γ ∋₂ T → Γ ⊢₂ T

⟦_⟧₂ : ∀ {Γ} {T} → Γ ⊢₂ T → Section₂ T
⟦ -var- x ⟧₂ = ⟦ x ⟧V₂

data _⊢₁_ : ∀ Γ → Fibration₁ ⟦ Γ ⟧C → Set where
  -var- : ∀ {Γ} {T} → Γ ∋₁ T → Γ ⊢₁ T

⟦_⟧₁ : ∀ {Γ} {S} → Γ ⊢₁ S → Section₁ S
⟦ -var- x ⟧₁ = ⟦ x ⟧V₁

data _⊢₀_ : ∀ Γ → Fibration₀ ⟦ Γ ⟧C → Set where
  -var- : ∀ {Γ} {T} → Γ ∋₀ T → Γ ⊢₀ T

⟦_⟧₀ : ∀ {Γ} {S} → Γ ⊢₀ S → Section₀ S
⟦ -var- x ⟧₀ = ⟦ x ⟧V₀

