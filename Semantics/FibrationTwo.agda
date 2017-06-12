module Semantics.FibrationTwo where
open import Semantics.Groupoid
open import Semantics.Univ
open import Semantics.FibrationZero
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

Fibration-Eq₂ : ∀ {G} → Fibration₂ G → Fibration₂ G → Fibration₂ G -- TODO Fibrations over two different equivalent groupoids
Fibration-Eq₂ H K = record {
  Fibre = λ x → Eq₂ (Fibration₂.Fibre H x) (Fibration₂.Fibre K x) ;
  Fibre-cong = λ p → Eq₂-cong (Fibration₂.Fibre-cong H p) (Fibration₂.Fibre-cong K p) ;
  Fibre-cong₂ = λ fill → Eq₂-cong₂ (Fibration₂.Fibre-cong₂ H fill) (Fibration₂.Fibre-cong₂ K fill) ;
  Fibre-cong₃ = λ fill₂ → Eq₂-cong₃ (Fibration₂.Fibre-cong₃ H fill₂) (Fibration₂.Fibre-cong₃ K fill₂) }

pullback₂ : ∀ {G} {H} → Groupoid-Functor G H → Fibration₂ H → Fibration₂ G
pullback₂ F K = record {
  Fibre = λ x → Fibration₂.Fibre K (ap-vertex F x) ;
  Fibre-cong = λ p → Fibration₂.Fibre-cong K (ap-path F p) ;
  Fibre-cong₂ = λ fill → Fibration₂.Fibre-cong₂ K (ap-fill F fill);
  Fibre-cong₃ = λ fill₂ → Fibration₂.Fibre-cong₃ K (Groupoid-Functor.ap-fill₂ F fill₂)}

