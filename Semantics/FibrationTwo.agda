module Semantics.FibrationTwo where
open import Semantics.Groupoid
open import Semantics.Univ
open import Semantics.FibrationOne

record Fibration₂ (G : Groupoid) : Set where
  field
    Fibre       : Groupoid.Vertex G → U₂
    Fibre-cong  : ∀ {x y} (p : Groupoid.Path G x y) → T₂ (Eq₂ (Fibre x) (Fibre y))
    Fibre-cong₂ : ∀ {nw ne sw se} {north : Groupoid.Path G nw ne} {south : Groupoid.Path G sw se} {west : Groupoid.Path G nw sw} {east : Groupoid.Path G ne se} →
                (fill : Groupoid.Fill G north south west east) →
                T₁ (eq₂ (Fibre-cong north) (Eq₂-cong (Fibre-cong west) (Fibre-cong east)) (Fibre-cong south))
                
postulate Fibration-Eq₂ : ∀ {G} → Fibration₂ G → Fibration₂ G → Set

pullback₂ : ∀ {G} {H} → Groupoid-Functor G H → Fibration₂ H → Fibration₂ G
pullback₂ F K = record {
  Fibre = λ x → Fibration₂.Fibre K (ap-vertex F x) ;
  Fibre-cong = λ p → Fibration₂.Fibre-cong K (ap-path F p) ;
  Fibre-cong₂ = λ fill → Fibration₂.Fibre-cong₂ K (ap-fill F fill) }
  
postulate pullback₂-congl : ∀ {G} {H} {F F' : Groupoid-Functor G H} →
                          Groupoid-NatIso F F' → (K : Fibration₂ H) → Fibration-Eq₂ (pullback₂ F K) (pullback₂ F' K)

record Section₂ {G} (H : Fibration₂ G) : Set where
  open Fibration₂ H
  field
    vertex : ∀ x → T₂ (Fibre x)
    path   : ∀ {x y} (p : Groupoid.Path G x y) → T₁ (eq₂ (vertex x) (Fibre-cong p) (vertex y))
    face   : ∀ {nw ne sw se} {north : Groupoid.Path G nw ne} {south : Groupoid.Path G sw se} {west : Groupoid.Path G nw sw} {east : Groupoid.Path G ne se}
      (fill : Groupoid.Fill G north south west east) → T₀ (eq₁ (path north) (eq₂-cong (path west) (Fibre-cong₂ fill) (path east)) (path south))

vertex : ∀ {G H} → Section₂ {G} H → (x : Groupoid.Vertex G) → T₂ (Fibration₂.Fibre H x)
vertex = Section₂.vertex

path : ∀ {G H} (s : Section₂ {G} H) {x y} (p : Groupoid.Path G x y) → T₁ (eq₂ (vertex s x) (Fibration₂.Fibre-cong H p) (vertex s y))
path = Section₂.path

face : ∀ {G H} (s : Section₂ {G} H) {nw ne sw se} {north : Groupoid.Path G nw ne} {south : Groupoid.Path G sw se} {west : Groupoid.Path G nw sw} {east : Groupoid.Path G ne se} (fill : Groupoid.Fill G north south west east)→ 
               T₀ (eq₁ (path s north) (eq₂-cong (path s west) (Fibration₂.Fibre-cong₂ H fill) (path s east)) (path s south))
face = Section₂.face

postulate section-pullback₂ : ∀ {G H K} (F : Groupoid-Functor G H) → Section₂ K → Section₂ (pullback₂ F K)

postulate EQ₂ : ∀ {G H K} → Section₂ {G} H → Fibration-Eq₂ H K → Section₂ K → Fibration₁ G

