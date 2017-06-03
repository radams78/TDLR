module Syntax.Variable where
open import Semantics
open import Syntax.Context

infix 10 _var₂_∋_
data _var₂_∋_ : ∀ Γ (G : Fibration₂ ⟦ Γ ⟧C) → Section₂ G → Set where
  top : ∀ {Γ H} → Γ ,₂ H var₂ pullback₂ (p₂ H) H ∋ q₂
  pop₂ : ∀ {Γ G H ⟦x⟧} → Γ var₂ H ∋ ⟦x⟧ → Γ ,₂ G var₂ pullback₂ (p₂ G) H ∋ section-pullback₂ (p₂ G) ⟦x⟧
  pop₁ : ∀ {Γ S H ⟦x⟧} → Γ var₂ H ∋ ⟦x⟧ → Γ ,₁ S var₂ pullback₂ (p₁ S) H ∋ section-pullback₂ (p₁ S) ⟦x⟧
  pop₀ : ∀ {Γ P H ⟦x⟧} → Γ var₂ H ∋ ⟦x⟧ → Γ ,₀ P var₂ pullback₂ (p₀ P) H ∋ section-pullback₂ (p₀ P) ⟦x⟧

infix 10 _var₁_∋_
data _var₁_∋_ : ∀ Γ (G : Fibration₁ ⟦ Γ ⟧C) → Section₁ G → Set where
  top : ∀ {Γ H} → Γ ,₁ H var₁ pullback₁ (p₁ H) H ∋ q₁
  pop₂ : ∀ {Γ G H ⟦x⟧} → Γ var₁ H ∋ ⟦x⟧ → Γ ,₂ G var₁ pullback₁ (p₂ G) H ∋ section-pullback₁ (p₂ G) ⟦x⟧
  pop₁ : ∀ {Γ S H ⟦x⟧} → Γ var₁ H ∋ ⟦x⟧ → Γ ,₁ S var₁ pullback₁ (p₁ S) H ∋ section-pullback₁ (p₁ S) ⟦x⟧
  pop₀ : ∀ {Γ P H ⟦x⟧} → Γ var₁ H ∋ ⟦x⟧ → Γ ,₀ P var₁ pullback₁ (p₀ P) H ∋ section-pullback₁ (p₀ P) ⟦x⟧

infix 10 _var₀_∋_
data _var₀_∋_ : ∀ Γ (G : Fibration₀ ⟦ Γ ⟧C) → Section₀ G → Set where
  top : ∀ {Γ H} → Γ ,₀ H var₀ pullback₀ (p₀ H) H ∋ q₀
  pop₂ : ∀ {Γ G H ⟦x⟧} → Γ var₀ H ∋ ⟦x⟧ → Γ ,₂ G var₀ pullback₀ (p₂ G) H ∋ section-pullback₀ (p₂ G) ⟦x⟧
  pop₁ : ∀ {Γ S H ⟦x⟧} → Γ var₀ H ∋ ⟦x⟧ → Γ ,₁ S var₀ pullback₀ (p₁ S) H ∋ section-pullback₀ (p₁ S) ⟦x⟧
  pop₀ : ∀ {Γ P H ⟦x⟧} → Γ var₀ H ∋ ⟦x⟧ → Γ ,₀ P var₀ pullback₀ (p₀ P) H ∋ section-pullback₀ (p₀ P) ⟦x⟧
