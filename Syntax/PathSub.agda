module Syntax.PathSub where
open import Semantics
open import Syntax.Variable
open import Syntax.Typing
open import Syntax.Substitution

data PathSub {Γ} : ∀ {Δ} → Sub Γ Δ → Sub Γ Δ → Set
⟦_⟧PS : ∀ {Γ Δ} {ρ σ : Sub Γ Δ} → PathSub ρ σ → Groupoid-NatIso ⟦ ρ ⟧S ⟦ σ ⟧S

data PathSub {Γ} where
  • : PathSub • •
  _,₂_∋_≡_ : ∀ {Δ} {ρ σ : Sub Γ Δ} 
    (τ : PathSub ρ σ) → ∀ G {⟦s⟧ ⟦t⟧} ⟦e⟧ {s : Γ ⊢₂ pullback₂ ⟦ ρ ⟧S G ∋ ⟦s⟧} {t : Γ ⊢₂ pullback₂ ⟦ σ ⟧S G ∋ ⟦t⟧} →
    Γ ⊢₁ EQ₂ ⟦s⟧ (pullback₂-congl ⟦ τ ⟧PS G) ⟦t⟧ ∋ ⟦e⟧ → PathSub (ρ ,₂ G ∋ ⟦s⟧ ≡ s) (σ ,₂ _ ∋ ⟦t⟧ ≡ t)
  _,₁_∋_≡_ : ∀ {Δ} {ρ σ : Sub Γ Δ} (τ : PathSub ρ σ) →
    ∀ S {⟦s⟧ ⟦t⟧} ⟦e⟧ {s : Γ ⊢₁ pullback₁ ⟦ ρ ⟧S S ∋ ⟦s⟧} {t : Γ ⊢₁ pullback₁ ⟦ σ ⟧S S ∋ ⟦t⟧} →
    Γ ⊢₀ EQ₁ ⟦s⟧ (pullback₁-congl ⟦ τ ⟧PS S) ⟦t⟧ ∋ ⟦e⟧ → PathSub (ρ ,₁ S ∋ ⟦s⟧ ≡ s) (σ ,₁ _ ∋ ⟦t⟧ ≡ t)
  _,₀* : ∀ {Δ P} {ρ σ : Sub Γ Δ} {⟦s⟧ ⟦t⟧} {s : Γ ⊢₀ pullback₀ ⟦ ρ ⟧S P ∋ ⟦s⟧} {t : Γ ⊢₀ pullback₀ ⟦ σ ⟧S P ∋ ⟦t⟧}
    (τ : PathSub ρ σ) → PathSub (ρ ,₀ P ∋ ⟦s⟧ ≡ s) (σ ,₀ _ ∋ ⟦t⟧ ≡ t)

⟦ • ⟧PS = bang-ref
⟦ τ ,₂ G ∋ ⟦e⟧ ≡ e ⟧PS = pair₂-cong {K = G} ⟦ τ ⟧PS ⟦e⟧
⟦ τ ,₁ S ∋ ⟦e⟧ ≡ e ⟧PS = pair₁-cong {S = S} ⟦ τ ⟧PS ⟦e⟧
⟦ _,₀* {P = P} τ ⟧PS = pair₀-cong {P = P} ⟦ τ ⟧PS

appsV₂ : ∀ {Γ Δ G ⟦x⟧} {ρ σ : Sub Γ Δ} (τ : PathSub ρ σ) (x : Δ var₂ G ∋ ⟦x⟧) →
  Γ ⊢₁ EQ₂ (section-pullback₂ ⟦ ρ ⟧S ⟦x⟧) (pullback₂-congl ⟦ τ ⟧PS G) (section-pullback₂ ⟦ σ ⟧S ⟦x⟧) ∋
  section-pullback₂-congl ⟦ τ ⟧PS ⟦x⟧
appsV₂ (τ ,₂ G ∋ ⟦e⟧ ≡ e) top = e
appsV₂ (τ ,₂ S ∋ ⟦e⟧ ≡ e) (pop₂ x) = appsV₂ τ x
appsV₂ (τ ,₁ P ∋ ⟦e⟧ ≡ e) (pop₁ x) = appsV₂ τ x
appsV₂ (τ ,₀*) (pop₀ x) = appsV₂ τ x

appsV₁ : ∀ {Γ Δ S ⟦x⟧} {ρ σ : Sub Γ Δ} (τ : PathSub ρ σ) (x : Δ var₁ S ∋ ⟦x⟧) →
  Γ ⊢₀ EQ₁ (section-pullback₁ ⟦ ρ ⟧S ⟦x⟧) (pullback₁-congl ⟦ τ ⟧PS S) (section-pullback₁ ⟦ σ ⟧S ⟦x⟧) ∋
  section-pullback₁-congl ⟦ τ ⟧PS ⟦x⟧
appsV₁ (τ ,₁ G ∋ ⟦e⟧ ≡ e) top = e
appsV₁ (τ ,₂ S ∋ ⟦e⟧ ≡ e) (pop₂ x) = appsV₁ τ x
appsV₁ (τ ,₁ P ∋ ⟦e⟧ ≡ e) (pop₁ x) = appsV₁ τ x
appsV₁ (τ ,₀*) (pop₀ x) = appsV₁ τ x

apps₃ : ∀  {Γ Δ ⟦G⟧} {ρ σ : Sub Γ Δ} (τ : PathSub ρ σ) (t : Δ ⊢ ⟦G⟧ gpd) →
  Γ ⊢₂ Fibration-Eq₂ (pullback₂ ⟦ ρ ⟧S ⟦G⟧) (pullback₂ ⟦ σ ⟧S ⟦G⟧) ∋ pullback₂-congl ⟦ τ ⟧PS ⟦G⟧
apps₃ τ (-eq- G H) = -eq*- (apps₃ τ G) (apps₃ τ H)

apps₂ : ∀  {Γ Δ G ⟦t⟧} {ρ σ : Sub Γ Δ} (τ : PathSub ρ σ) (t : Δ ⊢₂ G ∋ ⟦t⟧) →
  Γ ⊢₁ EQ₂ (section-pullback₂ ⟦ ρ ⟧S ⟦t⟧) (pullback₂-congl ⟦ τ ⟧PS G) (section-pullback₂ ⟦ σ ⟧S ⟦t⟧) ∋
  section-pullback₂-congl ⟦ τ ⟧PS ⟦t⟧
apps₂ τ (-var- x) = appsV₂ τ x
apps₂ τ (-eq*- G* H*) = -eq**- (apps₂ τ G*) (apps₂ τ H*)

apps₁ : ∀  {Γ Δ G ⟦t⟧} {ρ σ : Sub Γ Δ} (τ : PathSub ρ σ) (t : Δ ⊢₁ G ∋ ⟦t⟧) →
  Γ ⊢₀ EQ₁ (section-pullback₁ ⟦ ρ ⟧S ⟦t⟧) (pullback₁-congl ⟦ τ ⟧PS G) (section-pullback₁ ⟦ σ ⟧S ⟦t⟧) ∋
  section-pullback₁-congl ⟦ τ ⟧PS ⟦t⟧
apps₁ τ (-var- x) = appsV₁ τ x
apps₁ τ (-eq**- e f) = {!!}
