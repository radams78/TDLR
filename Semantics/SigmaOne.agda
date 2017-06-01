module Semantics.SigmaOne where
open import Data.Product

open import Semantics.Groupoid
open import Semantics.FibrationOne
open import Semantics.FibrationZero
open import Semantics.Univ

Sigma₁ : ∀ G → Fibration₁ G → Groupoid
Sigma₁ G S = record {
  Vertex = Σ[ x ∈ Groupoid.Vertex G ] T₁ (Fibration₁.Fibre S x) ;
  Path = λ x y → Σ[ p ∈ Groupoid.Path G (proj₁ x) (proj₁ y) ] T₀ (eq₁ (proj₂ x) (Fibration₁.Fibre-cong S p) (proj₂ y)) ;
  Fill = λ north south west east → Groupoid.Fill G (proj₁ north) (proj₁ south) (proj₁ west) (proj₁ east);
  Fill₂ = Groupoid.Fill₂ G }

pair₁ : ∀ {G H S} (F : Groupoid-Functor G H) → Section₁ (pullback₁ F S) → Groupoid-Functor G (Sigma₁ H S)
pair₁ F s = record {
  ap-vertex = λ x → (ap-vertex F x) , Section₁.vertex s x ;
  ap-path = λ p → (ap-path F p) , (Section₁.edge s p) ;
  ap-fill = ap-fill F;
  ap-fill₂ = Groupoid-Functor.ap-fill₂ F}

p₁ : ∀ {G} {S} → Groupoid-Functor (Sigma₁ G S) G
p₁ = record { ap-vertex = proj₁ ; ap-path = proj₁ ; ap-fill = λ fill → fill ; ap-fill₂ = λ fill₂ → fill₂}

q₁ : ∀ {G} {S} → Section₁ {Sigma₁ G S} (pullback₁ p₁ S)
q₁ = record { vertex = proj₂ ; edge = proj₂ }

pair₁-cong : ∀ {G H S} {F F' : Groupoid-Functor G H} {s : Section₁ (pullback₁ F S)} {t : Section₁ (pullback₁ F' S)} →
  (α : Groupoid-NatIso F F') → Section₀ (EQ₁ s (pullback₁-congl α S) t) → Groupoid-NatIso (pair₁ {S = S} F s) (pair₁ F' t)
pair₁-cong α e = record { comp = λ x → (Groupoid-NatIso.comp α x) , {!Section₀.vertex e x!} ; natural = {!!} ; natural₂ = {!!} }
