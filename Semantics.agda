--TODO Subscripts sometimes indicate h-level, sometimes repetition.  Make consistent
module Semantics where
open import Data.Product

record Groupoid : Set₁ where
  field
    Vertex : Set
    Path : Vertex → Vertex → Set
    Fill : ∀ {nw ne sw se} → Path nw ne → Path sw se → Path nw sw → Path ne se → Set
    
Vertex : Groupoid → Set
Vertex = Groupoid.Vertex

Path : ∀ G → Vertex G → Vertex G → Set
Path = Groupoid.Path

Fill : ∀ G {nw ne sw se : Vertex G} → Path G nw ne → Path G sw se → Path G nw sw → Path G ne se → Set
Fill G = Groupoid.Fill G

record Groupoid-Functor (G H : Groupoid) : Set where
  field
    ap-vertex : Vertex G → Vertex H
    ap-path   : ∀ {x y} → Path G x y → Path H (ap-vertex x) (ap-vertex y)
    ap-fill   : ∀ {nw ne sw se} {north : Path G nw ne} {south : Path G sw se} {west : Path G nw sw} {east : Path G ne se} →
      Fill G north south west east → Fill H (ap-path north) (ap-path south) (ap-path west) (ap-path east)
--TODO Respect equality

ap-vertex : ∀ {G H} → Groupoid-Functor G H → Vertex G → Vertex H
ap-vertex = Groupoid-Functor.ap-vertex

ap-path : ∀ {G H x y} (F : Groupoid-Functor G H) → Path G x y → Path H (ap-vertex F x) (ap-vertex F y)
ap-path F = Groupoid-Functor.ap-path F

ap-fill : ∀ {G H nw ne sw se} {north : Path G nw ne} {south : Path G sw se} {west : Path G nw sw} {east : Path G ne se}
                  (F : Groupoid-Functor G H) → Fill G north south west east → Fill H (ap-path F north) (ap-path F south) (ap-path F west) (ap-path F east)
ap-fill F = Groupoid-Functor.ap-fill F

postulate Groupoid-NatIso : ∀ {G H} → Groupoid-Functor G H → Groupoid-Functor G H → Set

postulate ONE : Groupoid
postulate bang : ∀ {G} → Groupoid-Functor G ONE
postulate bang-ref : ∀ {G} → Groupoid-NatIso (bang {G}) bang

postulate U₂ : Set
postulate T₂ : U₂ → Set
postulate Eq₂ : U₂ → U₂ → U₂
postulate Eq₂-cong : ∀ {A A' B B'} → T₂ (Eq₂ A A') → T₂ (Eq₂ B B') → T₂ (Eq₂ (Eq₂ A B) (Eq₂ A' B'))

postulate U₁ : Set
postulate T₁ : U₁ → Set
postulate Eq₁ : U₁ → U₁ → U₁
postulate eq₂ : ∀ {A B} → T₂ A → T₂ (Eq₂ A B) → T₂ B → U₁

postulate U₀ : Set
postulate T₀ : U₀ → Set
postulate eq₁ : ∀ {S T} → T₁ S → T₁ (Eq₁ S T) → T₁ T → U₀
postulate eq₂-cong : ∀ {A A' B B'}
                   {a : T₂ A} {a' : T₂ A'} {b : T₂ B} {b' : T₂ B'}
                   {A* : T₂ (Eq₂ A A')} {B* : T₂ (Eq₂ B B')} {e : T₂ (Eq₂ A B)} {e' : T₂ (Eq₂ A' B')}
                   (a* : T₁ (eq₂ a A* a')) (e* : T₁ (eq₂ e (Eq₂-cong A* B*) e')) (b* : T₁ (eq₂ b B* b')) →
                   T₁ (Eq₁ (eq₂ a e b) (eq₂ a' e' b'))

record Fibration₂ (G : Groupoid) : Set where
  field
    Fibre       : Vertex G → U₂
    Fibre-cong  : ∀ {x y} (p : Path G x y) → T₂ (Eq₂ (Fibre x) (Fibre y))
    Fibre-cong₂ : ∀ {nw ne sw se} {north : Path G nw ne} {south : Path G sw se} {west : Path G nw sw} {east : Path G ne se} →
                (fill : Fill G north south west east) →
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
    path   : ∀ {x y} (p : Path G x y) → T₁ (eq₂ (vertex x) (Fibre-cong p) (vertex y))
    face   : ∀ {nw ne sw se} {north : Path G nw ne} {south : Path G sw se} {west : Path G nw sw} {east : Path G ne se}
      (fill : Fill G north south west east) → T₀ (eq₁ (path north) (eq₂-cong (path west) (Fibre-cong₂ fill) (path east)) (path south))
vertex : ∀ {G H} → Section₂ {G} H → (x : Vertex G) → T₂ (Fibration₂.Fibre H x)
vertex = Section₂.vertex
path : ∀ {G H} (s : Section₂ {G} H) {x y} (p : Path G x y) → T₁ (eq₂ (vertex s x) (Fibration₂.Fibre-cong H p) (vertex s y))
path = Section₂.path
face : ∀ {G H} (s : Section₂ {G} H) {nw ne sw se} {north : Path G nw ne} {south : Path G sw se} {west : Path G nw sw} {east : Path G ne se} (fill : Fill G north south west east)→ 
               T₀ (eq₁ (path s north) (eq₂-cong (path s west) (Fibration₂.Fibre-cong₂ H fill) (path s east)) (path s south))
face = Section₂.face
postulate section-pullback₂ : ∀ {G H K} (F : Groupoid-Functor G H) → Section₂ K → Section₂ (pullback₂ F K)

Sigma₂ : ∀ G → Fibration₂ G → Groupoid
Sigma₂ G H = record {
  Vertex = Σ[ x ∈ Vertex G ] T₂ (Fibration₂.Fibre H x) ;
  Path = λ x y → Σ[ p ∈ Path G (proj₁ x) (proj₁ y) ] T₁ (eq₂ (proj₂ x) (Fibration₂.Fibre-cong H p) (proj₂ y)) ;
  Fill = λ north south west east → Σ[ fill ∈ Fill G (proj₁ north) (proj₁ south) (proj₁ west) (proj₁ east) ]
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

postulate Fibration₁ : Groupoid → Set
postulate Fibration-Eq₁ : ∀ {G} → Fibration₁ G → Fibration₁ G → Set
postulate pullback₁ : ∀ {G} {H} → Groupoid-Functor G H → Fibration₁ H → Fibration₁ G
postulate pullback₁-congl : ∀ {G} {H} {F F' : Groupoid-Functor G H} →
                          Groupoid-NatIso F F' → (S : Fibration₁ H) → Fibration-Eq₁ (pullback₁ F S) (pullback₁ F' S)
postulate Section₁ : ∀ {G} → Fibration₁ G → Set
postulate section-pullback₁ : ∀ {G H S} (F : Groupoid-Functor G H) → Section₁ S → Section₁ (pullback₁ F S)

postulate EQ₂ : ∀ {G H K} → Section₂ {G} H → Fibration-Eq₂ H K → Section₂ K → Fibration₁ G
postulate pair₂-cong : ∀ {G H K} {F F' : Groupoid-Functor G H} {s : Section₂ (pullback₂ F K)} {t : Section₂ (pullback₂ F' K)} →
                     (α : Groupoid-NatIso F F') → Section₁ (EQ₂ s (pullback₂-congl α K) t) → Groupoid-NatIso (pair₂ K F s) (pair₂ K F' t)

postulate Sigma₁ : ∀ G → Fibration₁ G → Groupoid
postulate pair₁ : ∀ {G H S} (F : Groupoid-Functor G H) → Section₁ (pullback₁ F S) → Groupoid-Functor G (Sigma₁ H S)
postulate p₁ : ∀ {G} {S} → Groupoid-Functor (Sigma₁ G S) G
postulate q₁ : ∀ {G} {S} → Section₁ {Sigma₁ G S} (pullback₁ p₁ S)

postulate Fibration₀ : Groupoid → Set
postulate pullback₀ : ∀ {G} {H} → Groupoid-Functor G H → Fibration₀ H → Fibration₀ G
postulate Section₀ : ∀ {G} → Fibration₀ G → Set
postulate section-pullback₀ : ∀ {G H S} (F : Groupoid-Functor G H) → Section₀ S → Section₀ (pullback₀ F S)

postulate EQ₁ : ∀ {G S T} → Section₁ {G} S → Fibration-Eq₁ S T → Section₁ T → Fibration₀ G
postulate pair₁-cong : ∀ {G H S} {F F' : Groupoid-Functor G H} {s : Section₁ (pullback₁ F S)} {t : Section₁ (pullback₁ F' S)} →
                     (α : Groupoid-NatIso F F') → Section₀ (EQ₁ s (pullback₁-congl α S) t) → Groupoid-NatIso (pair₁ F s) (pair₁ F' t)

postulate Sigma₀ : ∀ G → Fibration₀ G → Groupoid
postulate pair₀ : ∀ {G H P} (F : Groupoid-Functor G H) → Section₀ (pullback₀ F P) → Groupoid-Functor G (Sigma₀ H P)
postulate pair₀-cong : ∀ {G H P} {F F' : Groupoid-Functor G H} {s : Section₀ (pullback₀ F P)} {t : Section₀ (pullback₀ F' P)} →
                     (α : Groupoid-NatIso F F') → Groupoid-NatIso (pair₀ F s) (pair₀ F' t)
postulate p₀ : ∀ {G} {P} → Groupoid-Functor (Sigma₀ G P) G
postulate q₀ : ∀ {G} {S} → Section₀ {Sigma₀ G S} (pullback₀ p₀ S)
