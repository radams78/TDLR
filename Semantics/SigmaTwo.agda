module Semantics.SigmaTwo where
open import Data.Product

open import Semantics.Groupoid
open import Semantics.Univ
open import Semantics.FibrationTwo
open import Semantics.FibrationOne

Sigma₂ : ∀ G → Fibration₂ G → Groupoid
Sigma₂ G H = record {
  Vertex = Σ[ x ∈ Groupoid.Vertex G ] T₂ (Fibration₂.Fibre H x) ;
  Path = λ x y → Σ[ p ∈ Groupoid.Path G (proj₁ x) (proj₁ y) ] T₁ (eq₂ (proj₂ x) (Fibration₂.Fibre-cong H p) (proj₂ y)) ;
  Fill = λ north south west east → Σ[ fill ∈ Groupoid.Fill G (proj₁ north) (proj₁ south) (proj₁ west) (proj₁ east) ]
    T₀ (eq₁ (proj₂ north) (eq₂-cong (proj₂ west) (Fibration₂.Fibre-cong₂ H fill) (proj₂ east)) (proj₂ south)) }

pair₂ : ∀ {G H} K (F : Groupoid-Functor G H) → Section₂ (pullback₂ F K) → Groupoid-Functor G (Sigma₂ H K)
pair₂ K F s = record {
  ap-vertex = λ x → ap-vertex F x , vertex s x ;
  ap-path = λ p → ap-path F p , path s p ;
  ap-fill = λ fill → ap-fill F fill , face s fill }

p₂ : ∀ {G} {H} → Groupoid-Functor (Sigma₂ G H) G
p₂ {G} {H} = record {
  ap-vertex = proj₁ ;
  ap-path = proj₁ ;
  ap-fill = proj₁ }

postulate q₂ : ∀ {G} {H} → Section₂ {Sigma₂ G H} (pullback₂ p₂ H)

postulate pair₂-cong : ∀ {G H K} {F F' : Groupoid-Functor G H} {s : Section₂ (pullback₂ F K)} {t : Section₂ (pullback₂ F' K)} →
                     (α : Groupoid-NatIso F F') → Section₁ (EQ₂ s (pullback₂-congl α K) t) → Groupoid-NatIso (pair₂ K F s) (pair₂ K F' t)
