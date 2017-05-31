module Syntax.Substitution where
open import Semantics
open import Syntax.Context
open import Syntax.Variable
open import Syntax.Typing

data Sub Γ : Cx → Set
⟦_⟧S : ∀ {Γ} {Δ} → Sub Γ Δ → Groupoid-Functor ⟦ Γ ⟧C ⟦ Δ ⟧C

data Sub Γ where
  • : Sub Γ ε
  _,₂_ : ∀ {Δ G} (σ : Sub Γ Δ) → Γ ⊢₂ pullback₂ ⟦ σ ⟧S G → Sub Γ (Δ ,₂ G)
  _,₁_ : ∀ {Δ S} (σ : Sub Γ Δ) → Γ ⊢₁ pullback₁ ⟦ σ ⟧S S → Sub Γ (Δ ,₁ S)
  _,₀_ : ∀ {Δ P} (σ : Sub Γ Δ) → Γ ⊢₀ pullback₀ ⟦ σ ⟧S P → Sub Γ (Δ ,₀ P)

⟦ • ⟧S = bang
⟦ σ ,₂ t ⟧S = pair₂ _ ⟦ σ ⟧S ⟦ t ⟧₂
⟦ σ ,₁ a ⟧S = pair₁ ⟦ σ ⟧S ⟦ a ⟧₁
⟦ _,₀_ {P = P} σ p ⟧S = pair₀ P ⟦ σ ⟧S ⟦ p ⟧₀

apV₂ : ∀ {Γ Δ T} (σ : Sub Γ Δ) → Δ ∋₂ T → Γ ⊢₂ pullback₂ ⟦ σ ⟧S T
apV₂ (σ ,₂ t) top = t
apV₂ (σ ,₂ t) (pop₂ x) = apV₂ σ x
apV₂ (σ ,₁ t) (pop₁ x) = apV₂ σ x
apV₂ (σ ,₀ t) (pop₀ x) = apV₂ σ x

