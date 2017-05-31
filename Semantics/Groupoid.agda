module Semantics.Groupoid where

record Groupoid : Set₁ where
  field
    Vertex : Set
    Path : Vertex → Vertex → Set
    Fill : ∀ {nw ne sw se} → Path nw ne → Path sw se → Path nw sw → Path ne se → Set
    
record Groupoid-Functor (G H : Groupoid) : Set where
  field
    ap-vertex : Groupoid.Vertex G → Groupoid.Vertex H
    ap-path   : ∀ {x y} → Groupoid.Path G x y → Groupoid.Path H (ap-vertex x) (ap-vertex y)
    ap-fill   : ∀ {nw ne sw se} {north : Groupoid.Path G nw ne} {south : Groupoid.Path G sw se} {west : Groupoid.Path G nw sw} {east : Groupoid.Path G ne se} →
      Groupoid.Fill G north south west east → Groupoid.Fill H (ap-path north) (ap-path south) (ap-path west) (ap-path east)
--TODO Respect equality

ap-vertex : ∀ {G H} → Groupoid-Functor G H → Groupoid.Vertex G → Groupoid.Vertex H
ap-vertex = Groupoid-Functor.ap-vertex

ap-path : ∀ {G H x y} (F : Groupoid-Functor G H) → Groupoid.Path G x y → Groupoid.Path H (ap-vertex F x) (ap-vertex F y)
ap-path F = Groupoid-Functor.ap-path F

ap-fill : ∀ {G H nw ne sw se} {north : Groupoid.Path G nw ne} {south : Groupoid.Path G sw se} {west : Groupoid.Path G nw sw} {east : Groupoid.Path G ne se}
                  (F : Groupoid-Functor G H) → Groupoid.Fill G north south west east → Groupoid.Fill H (ap-path F north) (ap-path F south) (ap-path F west) (ap-path F east)
ap-fill F = Groupoid-Functor.ap-fill F

postulate Groupoid-NatIso : ∀ {G H} → Groupoid-Functor G H → Groupoid-Functor G H → Set

