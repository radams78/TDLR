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
    Fibre-cong₃ : ∀ {unw une usw use bnw bne bsw bse}
                 {un : Groupoid.Path G unw une} {us : Groupoid.Path G usw use} {uw : Groupoid.Path G unw usw} {ue : Groupoid.Path G une use}
                 {bn : Groupoid.Path G bnw bne} {bs : Groupoid.Path G bsw bse} {bw : Groupoid.Path G bnw bsw} {be : Groupoid.Path G bne bse}
                 {nw : Groupoid.Path G unw bnw} {ne : Groupoid.Path G une bne} {sw : Groupoid.Path G usw bsw} {se : Groupoid.Path G use bse}
                 {top-fill : Groupoid.Fill G un us uw ue} {bottom-fill : Groupoid.Fill G bn bs bw be} {north-fill : Groupoid.Fill G un bn nw ne} {south-fill : Groupoid.Fill G us bs sw se} {west-fill : Groupoid.Fill G uw bw nw sw} {east-fill : Groupoid.Fill G ue be ne se} →
                 Groupoid.Fill₂ G top-fill bottom-fill north-fill south-fill west-fill east-fill → 
                 T₀ (eq₁ (Fibre-cong₂ top-fill)
                   (eq₂-cong (Fibre-cong₂ north-fill) (Eq₂-cong₂ (Fibre-cong₂ west-fill) (Fibre-cong₂ east-fill))
                     (Fibre-cong₂ south-fill))
                   (Fibre-cong₂ bottom-fill))
--TODO Fourth component?

record Fibration-Eq₂ {G} (H K : Fibration₂ G) : Set where
  field
    Fibre : ∀ x → T₂ (Eq₂ (Fibration₂.Fibre H x) (Fibration₂.Fibre K x))
    Fibre-cong : ∀ {x y} (p : Groupoid.Path G x y) → T₁ (eq₂ (Fibre x) (Eq₂-cong (Fibration₂.Fibre-cong H p) (Fibration₂.Fibre-cong K p)) (Fibre y))
    Fibre-cong₂ : ∀ {nw ne sw se} {north : Groupoid.Path G nw ne} {south : Groupoid.Path G sw se} {west : Groupoid.Path G nw sw} {east : Groupoid.Path G ne se} (fill : Groupoid.Fill G north south west east) →
      T₀ (eq₁ (Fibre-cong north) (eq₂-cong (Fibre-cong west)
        (Eq₂-cong₂ (Fibration₂.Fibre-cong₂ H fill) (Fibration₂.Fibre-cong₂ K fill))
        (Fibre-cong east)) (Fibre-cong south))

pullback₂ : ∀ {G} {H} → Groupoid-Functor G H → Fibration₂ H → Fibration₂ G
pullback₂ F K = record {
  Fibre = λ x → Fibration₂.Fibre K (ap-vertex F x) ;
  Fibre-cong = λ p → Fibration₂.Fibre-cong K (ap-path F p) ;
  Fibre-cong₂ = λ fill → Fibration₂.Fibre-cong₂ K (ap-fill F fill);
  Fibre-cong₃ = λ fill₂ → Fibration₂.Fibre-cong₃ K (Groupoid-Functor.ap-fill₂ F fill₂)}
  
pullback₂-congl : ∀ {G} {H} {F F' : Groupoid-Functor G H} →
  Groupoid-NatIso F F' → (K : Fibration₂ H) → Fibration-Eq₂ (pullback₂ F K) (pullback₂ F' K)
pullback₂-congl α K = record {
  Fibre = λ x → Fibration₂.Fibre-cong K (Groupoid-NatIso.comp α x) ;
  Fibre-cong = λ p → Fibration₂.Fibre-cong₂ K (Groupoid-NatIso.natural α p) ;
  Fibre-cong₂ = λ fill → Fibration₂.Fibre-cong₃ K (Groupoid-NatIso.natural₂ α fill) }

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

section-pullback₂ : ∀ {G H K} (F : Groupoid-Functor G H) → Section₂ K → Section₂ (pullback₂ F K)
section-pullback₂ F s = record {
  vertex = λ x → Section₂.vertex s (ap-vertex F x) ;
  path = λ p → Section₂.path s (ap-path F p) ;
  face = λ fill → Section₂.face s (ap-fill F fill) }

EQ₂ : ∀ {G H K} → Section₂ {G} H → Fibration-Eq₂ H K → Section₂ K → Fibration₁ G
EQ₂ s e t = record {
  Fibre = λ x → eq₂ (Section₂.vertex s x) (Fibration-Eq₂.Fibre e x) (Section₂.vertex t x) ;
  Fibre-cong = λ p → eq₂-cong (Section₂.path s p) (Fibration-Eq₂.Fibre-cong e p) (Section₂.path t p);
  Fibre-cong₂ = λ fill → {!eq₂-cong₂!} }

section-pullback₂-congl : ∀ {G H K} {F F' : Groupoid-Functor G H} →
  (α : Groupoid-NatIso F F') (s : Section₂ K) →
  Section₁ (EQ₂ (section-pullback₂ F s) (pullback₂-congl α K) (section-pullback₂ F' s))
section-pullback₂-congl α s = record {
  vertex = λ x → Section₂.path s (Groupoid-NatIso.comp α x) ;
  edge = λ p → Section₂.face s (Groupoid-NatIso.natural α p) }
