module Semantics.SectionTwo where

open import Semantics.Univ
open import Semantics.Groupoid
open import Semantics.FibrationZero
open import Semantics.FibrationOne
open import Semantics.FibrationTwo

record Section₂ {G} (H : Fibration₂ G) : Set where
  open Fibration₂ H
  field
    vertex : ∀ x → T₂ (Fibre x)
    path   : ∀ {x y} (p : Groupoid.Path G x y) → T₁ (eq₂ (vertex x) (Fibre-cong p) (vertex y))
    face   : ∀ {nw ne sw se} {north : Groupoid.Path G nw ne} {south : Groupoid.Path G sw se} {west : Groupoid.Path G nw sw} {east : Groupoid.Path G ne se}
      (fill : Groupoid.Fill G north south west east) → T₀ (eq₁ (path north) (eq₂-cong (path west) (Fibre-cong₂ fill) (path east)) (path south))

Fibration-Eq₂-cong : ∀ {G} {H H' K K' : Fibration₂ G} →
  Section₂ (Fibration-Eq₂ H H') → Section₂ (Fibration-Eq₂ K K') →
  Section₂ (Fibration-Eq₂ (Fibration-Eq₂ H K) (Fibration-Eq₂ H' K'))
Fibration-Eq₂-cong H* K* = record {
  vertex = λ x → Eq₂-cong (Section₂.vertex H* x) (Section₂.vertex K* x) ;
  path = λ p → Eq₂-cong₂ (Section₂.path H* p) (Section₂.path K* p) ;
  face = λ fill → Eq₂-cong₃ (Section₂.face H* fill) (Section₂.face K* fill) }

pullback₂-congl : ∀ {G} {H} {F F' : Groupoid-Functor G H} →
  Groupoid-NatIso F F' → (K : Fibration₂ H) → Section₂ (Fibration-Eq₂ (pullback₂ F K) (pullback₂ F' K))
pullback₂-congl α K = record {
  vertex = λ x → Fibration₂.Fibre-cong K (Groupoid-NatIso.comp α x) ;
  path = λ p → Fibration₂.Fibre-cong₂ K (Groupoid-NatIso.natural α p) ;
  face = λ fill → Fibration₂.Fibre-cong₃ K (Groupoid-NatIso.natural₂ α fill) }

section-pullback₂ : ∀ {G H K} (F : Groupoid-Functor G H) → Section₂ K → Section₂ (pullback₂ F K)
section-pullback₂ F s = record {
  vertex = λ x → Section₂.vertex s (ap-vertex F x) ;
  path = λ p → Section₂.path s (ap-path F p) ;
  face = λ fill → Section₂.face s (ap-fill F fill) }

