module Syntax.Variable where
open import Semantics
open import Syntax.Context

infix 10 _∋₂_
data _∋₂_ : ∀ Γ → Fibration₂ ⟦ Γ ⟧C → Set where
  top : ∀ {Γ} {H} → Γ ,₂ H ∋₂ pullback₂ p₂ H
  pop₂ : ∀ {Γ} {G} {H} → Γ ∋₂ H → Γ ,₂ G ∋₂ pullback₂ p₂ H
  pop₁ : ∀ {Γ} {S} {H} → Γ ∋₂ H → Γ ,₁ S ∋₂ pullback₂ p₁ H
  pop₀ : ∀ {Γ} {P} {H} → Γ ∋₂ H → Γ ,₀ P ∋₂ pullback₂ (p₀ P) H

⟦_⟧V₂ : ∀ {Γ} {H} → Γ ∋₂ H → Section₂ H
⟦ top ⟧V₂ = q₂
⟦ pop₂ x ⟧V₂ = section-pullback₂ p₂ ⟦ x ⟧V₂
⟦ pop₁ x ⟧V₂ = section-pullback₂ p₁ ⟦ x ⟧V₂
⟦ pop₀ {P = P} x ⟧V₂ = section-pullback₂ (p₀ P) ⟦ x ⟧V₂

infix 10 _∋₁_
data _∋₁_ : ∀ Γ → Fibration₁ ⟦ Γ ⟧C → Set where
  top : ∀ {Γ} {T} → Γ ,₁ T ∋₁ pullback₁ p₁ T
  pop₂ : ∀ {Γ} {G} {T} → Γ ∋₁ T → Γ ,₂ G ∋₁ pullback₁ p₂ T
  pop₁ : ∀ {Γ} {S} {T} → Γ ∋₁ T → Γ ,₁ S ∋₁ pullback₁ p₁ T
  pop₀ : ∀ {Γ} {P} {T} → Γ ∋₁ T → Γ ,₀ P ∋₁ pullback₁ (p₀ P) T

⟦_⟧V₁ : ∀ {Γ} {H} → Γ ∋₁ H → Section₁ H
⟦ top ⟧V₁ = q₁
⟦ pop₂ x ⟧V₁ = section-pullback₁ p₂ ⟦ x ⟧V₁
⟦ pop₁ x ⟧V₁ = section-pullback₁ p₁ ⟦ x ⟧V₁
⟦ pop₀ {P = P} x ⟧V₁ = section-pullback₁ (p₀ P) ⟦ x ⟧V₁

infix 10 _∋₀_
data _∋₀_ : ∀ Γ → Fibration₀ ⟦ Γ ⟧C → Set where
  top : ∀ {Γ} {P} → Γ ,₀ P ∋₀ pullback₀ (p₀ P) P
  pop₂ : ∀ {Γ} {G} {T} → Γ ∋₀ T → Γ ,₂ G ∋₀ pullback₀ p₂ T
  pop₁ : ∀ {Γ} {S} {T} → Γ ∋₀ T → Γ ,₁ S ∋₀ pullback₀ p₁ T
  pop₀ : ∀ {Γ} {P} {T} → Γ ∋₀ T → Γ ,₀ P ∋₀ pullback₀ (p₀ P) T

⟦_⟧V₀ : ∀ {Γ} {H} → Γ ∋₀ H → Section₀ H
⟦ top ⟧V₀ = q₀
⟦ pop₂ x ⟧V₀ = section-pullback₀ p₂ ⟦ x ⟧V₀
⟦ pop₁ x ⟧V₀ = section-pullback₀ p₁ ⟦ x ⟧V₀
⟦ pop₀ {P = P} x ⟧V₀ = section-pullback₀ (p₀ P) ⟦ x ⟧V₀

