module Syntax.PathSub where
open import Semantics
open import Syntax.Typing
open import Syntax.Substitution

data PathSub {Γ} : ∀ {Δ} → Sub Γ Δ → Sub Γ Δ → Set
⟦_⟧PS : ∀ {Γ Δ} {ρ σ : Sub Γ Δ} → PathSub ρ σ → Groupoid-NatIso ⟦ ρ ⟧S ⟦ σ ⟧S

data PathSub {Γ} where
  • : PathSub • •
  _,₂_ : ∀ {Δ G} {ρ σ : Sub Γ Δ} {s : Γ ⊢₂ pullback₂ ⟦ ρ ⟧S G} {t : Γ ⊢₂ pullback₂ ⟦ σ ⟧S G}
    (τ : PathSub ρ σ) → Γ ⊢₁ EQ₂ ⟦ s ⟧₂ (pullback₂-congl ⟦ τ ⟧PS G) ⟦ t ⟧₂ → PathSub (ρ ,₂ s) (σ ,₂ t)
  _,₁_ : ∀ {Δ S} {ρ σ : Sub Γ Δ} {s : Γ ⊢₁ pullback₁ ⟦ ρ ⟧S S} {t : Γ ⊢₁ pullback₁ ⟦ σ ⟧S S}
    (τ : PathSub ρ σ) → Γ ⊢₀ EQ₁ ⟦ s ⟧₁ (pullback₁-congl ⟦ τ ⟧PS S) ⟦ t ⟧₁ → PathSub (ρ ,₁ s) (σ ,₁ t)
  _,₀* : ∀ {Δ P} {ρ σ : Sub Γ Δ} {s : Γ ⊢₀ pullback₀ ⟦ ρ ⟧S P} {t : Γ ⊢₀ pullback₀ ⟦ σ ⟧S P}
    (τ : PathSub ρ σ) → PathSub (_,₀_ {P = P} ρ s) (σ ,₀ t)

⟦ • ⟧PS = bang-ref
⟦ τ ,₂ e ⟧PS = pair₂-cong ⟦ τ ⟧PS ⟦ e ⟧₁
⟦ τ ,₁ e ⟧PS = pair₁-cong ⟦ τ ⟧PS ⟦ e ⟧₀
⟦ _,₀* {P = P} τ ⟧PS = pair₀-cong {P = P} ⟦ τ ⟧PS
