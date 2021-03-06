module Semantics.SigmaZero where
open import Data.Product

open import Semantics.Groupoid
open import Semantics.FibrationZero
open import Semantics.Univ

Sigma₀ : ∀ G → Fibration₀ G → Groupoid
Sigma₀ G P = record {
  Vertex = Σ[ x ∈ Groupoid.Vertex G ] T₀ (Fibration₀.Fibre P x) ;
  Path = λ x y → Groupoid.Path G (proj₁ x) (proj₁ y) ;
  Fill = Groupoid.Fill G;
  Fill₂ = Groupoid.Fill₂ G }
  
pair₀ : ∀ {G H} P (F : Groupoid-Functor G H) → Section₀ (pullback₀ F P) → Groupoid-Functor G (Sigma₀ H P)
pair₀ P F s = record {
  ap-vertex = λ x → (ap-vertex F x) , Section₀.vertex s x ;
  ap-path = ap-path F ;
  ap-fill = ap-fill F ;
  ap-fill₂ = Groupoid-Functor.ap-fill₂ F}

pair₀-cong : ∀ {G H P} {F F' : Groupoid-Functor G H} {s : Section₀ (pullback₀ F P)} {t : Section₀ (pullback₀ F' P)} →
  (α : Groupoid-NatIso F F') → Groupoid-NatIso (pair₀ P F s) (pair₀ P F' t)
pair₀-cong α = record {
  comp = Groupoid-NatIso.comp α ;
  natural = Groupoid-NatIso.natural α ;
  natural₂ = Groupoid-NatIso.natural₂ α }

p₀ : ∀ {G} P → Groupoid-Functor (Sigma₀ G P) G
p₀ P = record { ap-vertex = proj₁ ; ap-path = λ p → p ; ap-fill = λ fill → fill ; ap-fill₂ = λ fill₂ → fill₂ }

q₀ : ∀ {G} {P} → Section₀ {Sigma₀ G P} (pullback₀ (p₀ P) P)
q₀ = record { vertex = proj₂ }
