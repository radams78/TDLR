module Semantics.FibrationOne where
open import Semantics.Groupoid
open import Semantics.Univ
open import Semantics.FibrationZero

record Fibration₁ (G : Groupoid) : Set where
  field
    Fibre : Groupoid.Vertex G → U₁
    Fibre-cong : ∀ {x y} → Groupoid.Path G x y → T₁ (Eq₁ (Fibre x) (Fibre y))
    
postulate Fibration-Eq₁ : ∀ {G} → Fibration₁ G → Fibration₁ G → Set

pullback₁ : ∀ {G} {H} → Groupoid-Functor G H → Fibration₁ H → Fibration₁ G
pullback₁ F S = record {
  Fibre = λ x → Fibration₁.Fibre S (ap-vertex F x) ;
  Fibre-cong = λ p → Fibration₁.Fibre-cong S (ap-path F p) }

postulate pullback₁-congl : ∀ {G} {H} {F F' : Groupoid-Functor G H} →
                          Groupoid-NatIso F F' → (S : Fibration₁ H) → Fibration-Eq₁ (pullback₁ F S) (pullback₁ F' S)

record Section₁ {G} (S : Fibration₁ G) : Set where
  field
    vertex : ∀ x → T₁ (Fibration₁.Fibre S x)
    edge   : ∀ {x y} (p : Groupoid.Path G x y) → T₀ (eq₁ (vertex x) (Fibration₁.Fibre-cong S p) (vertex y))
    
postulate section-pullback₁ : ∀ {G H S} (F : Groupoid-Functor G H) → Section₁ S → Section₁ (pullback₁ F S)

postulate EQ₁ : ∀ {G S T} → Section₁ {G} S → Fibration-Eq₁ S T → Section₁ T → Fibration₀ G
