module Syntax.PathSub where
open import Semantics
open import Syntax.Variable
open import Syntax.Typing
open import Syntax.Substitution

data PathSub {Γ} : ∀ {Δ} → Sub Γ Δ → Sub Γ Δ → Set
⟦_⟧PS : ∀ {Γ Δ} {ρ σ : Sub Γ Δ} → PathSub ρ σ → Groupoid-NatIso ⟦ ρ ⟧S ⟦ σ ⟧S

data PathSub {Γ} where
  • : PathSub • •
  _,₂_≡_ : ∀ {Δ G} {ρ σ : Sub Γ Δ} {⟦s⟧ ⟦t⟧} {s : Γ ⊢₂ pullback₂ ⟦ ρ ⟧S G ∋ ⟦s⟧} {t : Γ ⊢₂ pullback₂ ⟦ σ ⟧S G ∋ ⟦t⟧}
    (τ : PathSub ρ σ) → ∀ ⟦e⟧ → Γ ⊢₁ EQ₂ ⟦s⟧ (pullback₂-congl ⟦ τ ⟧PS G) ⟦t⟧ ∋ ⟦e⟧ → PathSub (_,₂_≡_ {G = G} ρ ⟦s⟧ s) (σ ,₂ ⟦t⟧ ≡ t)
  _,₁_≡_ : ∀ {Δ S} {ρ σ : Sub Γ Δ} {⟦s⟧ ⟦t⟧} {s : Γ ⊢₁ pullback₁ ⟦ ρ ⟧S S ∋ ⟦s⟧} {t : Γ ⊢₁ pullback₁ ⟦ σ ⟧S S ∋ ⟦t⟧}
    (τ : PathSub ρ σ) → ∀ ⟦e⟧ → Γ ⊢₀ EQ₁ ⟦s⟧ (pullback₁-congl ⟦ τ ⟧PS S) ⟦t⟧ ∋ ⟦e⟧ → PathSub (ρ ,₁ ⟦s⟧ ≡ s) (σ ,₁ ⟦t⟧ ≡ t)
  _,₀* : ∀ {Δ P} {ρ σ : Sub Γ Δ} {⟦s⟧ ⟦t⟧} {s : Γ ⊢₀ pullback₀ ⟦ ρ ⟧S P ∋ ⟦s⟧} {t : Γ ⊢₀ pullback₀ ⟦ σ ⟧S P ∋ ⟦t⟧}
    (τ : PathSub ρ σ) → PathSub (_,₀_≡_ {P = P} ρ ⟦s⟧ s) (σ ,₀ ⟦t⟧ ≡ t)

⟦ • ⟧PS = bang-ref
⟦ _,₂_≡_ {G = G} τ ⟦e⟧ e ⟧PS = pair₂-cong {K = G} ⟦ τ ⟧PS ⟦e⟧
⟦ τ ,₁ ⟦e⟧ ≡ e ⟧PS = pair₁-cong ⟦ τ ⟧PS ⟦e⟧
⟦ _,₀* {P = P} τ ⟧PS = pair₀-cong {P = P} ⟦ τ ⟧PS

appsV₂ : ∀ {Γ Δ G ⟦x⟧} {ρ σ : Sub Γ Δ} (τ : PathSub ρ σ) (x : Δ ∋₂ G ≡ ⟦x⟧) →
  Γ ⊢₁ EQ₂ (section-pullback₂ ⟦ ρ ⟧S ⟦x⟧) (pullback₂-congl ⟦ τ ⟧PS G) (section-pullback₂ ⟦ σ ⟧S ⟦x⟧) ∋
  section-pullback₂-congl ⟦ τ ⟧PS ⟦x⟧
appsV₂ (τ ,₂ ⟦e⟧ ≡ e) top = e
appsV₂ (τ ,₂ ⟦e⟧ ≡ e) (pop₂ x) = appsV₂ τ x
appsV₂ (τ ,₁ ⟦e⟧ ≡ e) (pop₁ x) = {!appsV₂ τ x!}
appsV₂ (τ ,₀*) (pop₀ x) = {!!}
