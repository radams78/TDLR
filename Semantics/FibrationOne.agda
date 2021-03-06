module Semantics.FibrationOne where
open import Semantics.Groupoid
open import Semantics.Univ
open import Semantics.FibrationZero

record Fibration₁ (G : Groupoid) : Set where
  field
    Fibre : Groupoid.Vertex G → U₁
    Fibre-cong : ∀ {x y} → Groupoid.Path G x y → T₁ (Eq₁ (Fibre x) (Fibre y))
    Fibre-cong₂ : ∀ {nw ne sw se}
      {north : Groupoid.Path G nw ne} {south : Groupoid.Path G sw se} {west : Groupoid.Path G nw sw} {east : Groupoid.Path G ne se} →
      Groupoid.Fill G north south west east →
      T₀ (eq₁ (Fibre-cong north) (Eq₁-cong (Fibre-cong west) (Fibre-cong east)) (Fibre-cong south))
    
record Section₁ {G} (S : Fibration₁ G) : Set where
  field
    vertex : ∀ x → T₁ (Fibration₁.Fibre S x)
    edge   : ∀ {x y} (p : Groupoid.Path G x y) → T₀ (eq₁ (vertex x) (Fibration₁.Fibre-cong S p) (vertex y))

Fibration-Eq₁ : ∀ {G} → Fibration₁ G → Fibration₁ G → Fibration₁ G
Fibration-Eq₁ S T = record {
  Fibre = λ x → Eq₁ (Fibration₁.Fibre S x) (Fibration₁.Fibre T x) ;
  Fibre-cong = λ p → Eq₁-cong (Fibration₁.Fibre-cong S p) (Fibration₁.Fibre-cong T p) ;
  Fibre-cong₂ = λ fill → Eq₁-cong₂ (Fibration₁.Fibre-cong₂ S fill) (Fibration₁.Fibre-cong₂ T fill) }

Fibration-Eq₁-cong : ∀ {G} {S S' T T' : Fibration₁ G} →
  Section₁ (Fibration-Eq₁ S S') → Section₁ (Fibration-Eq₁ T T') →
  Section₁ (Fibration-Eq₁ (Fibration-Eq₁ S T) (Fibration-Eq₁ S' T'))
Fibration-Eq₁-cong S* T* = record {
  vertex = λ x → Eq₁-cong (Section₁.vertex S* x) (Section₁.vertex T* x) ;
  edge = λ p → Eq₁-cong₂ (Section₁.edge S* p) (Section₁.edge T* p) }

pullback₁ : ∀ {G} {H} → Groupoid-Functor G H → Fibration₁ H → Fibration₁ G
pullback₁ F S = record {
  Fibre = λ x → Fibration₁.Fibre S (ap-vertex F x) ;
  Fibre-cong = λ p → Fibration₁.Fibre-cong S (ap-path F p);
  Fibre-cong₂ = λ fill → Fibration₁.Fibre-cong₂ S (ap-fill F fill)}

pullback₁-congl : ∀ {G} {H} {F F' : Groupoid-Functor G H} →
  Groupoid-NatIso F F' → (S : Fibration₁ H) → Section₁ (Fibration-Eq₁ (pullback₁ F S) (pullback₁ F' S))
pullback₁-congl α S = record {
  vertex = λ x → Fibration₁.Fibre-cong S (Groupoid-NatIso.comp α x) ;
  edge = λ p → Fibration₁.Fibre-cong₂ S (Groupoid-NatIso.natural α p) }

section-pullback₁ : ∀ {G H S} (F : Groupoid-Functor G H) → Section₁ S → Section₁ (pullback₁ F S)
section-pullback₁ F s = record {
  vertex = λ x → Section₁.vertex s (ap-vertex F x) ;
  edge = λ p → Section₁.edge s (ap-path F p) }

EQ₁ : ∀ {G S T} → Section₁ {G} S → Section₁ (Fibration-Eq₁ S T) → Section₁ T → Fibration₀ G
EQ₁ s e t = record {
  Fibre = λ x → eq₁ (Section₁.vertex s x) (Section₁.vertex e x) (Section₁.vertex t x) ;
  Fibre-cong = λ p → eq₁-cong (Section₁.edge s p) (Section₁.edge e p) (Section₁.edge t p) }

section-pullback₁-congl : ∀ {G H S} {F F' : Groupoid-Functor G H}
  (α : Groupoid-NatIso F F') (s : Section₁ S) →
  Section₀ (EQ₁ (section-pullback₁ F s) (pullback₁-congl α S) (section-pullback₁ F' s))
section-pullback₁-congl α s = record {
  vertex = λ x → Section₁.edge s (Groupoid-NatIso.comp α x)
  }
