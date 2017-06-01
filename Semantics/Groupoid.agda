module Semantics.Groupoid where

record Groupoid : Set₁ where
  field
    Vertex : Set
    Path : Vertex → Vertex → Set
    Fill : ∀ {nw ne sw se} → Path nw ne → Path sw se → Path nw sw → Path ne se → Set
    Fill₂ : ∀ {unw une usw use bnw bne bsw bse}
            {un : Path unw une} {us : Path usw use} {uw : Path unw usw} {ue : Path une use}
            {bn : Path bnw bne} {bs : Path bsw bse} {bw : Path bnw bsw} {be : Path bne bse}
            {nw : Path unw bnw} {ne : Path une bne} {sw : Path usw bsw} {se : Path use bse} →
            Fill un us uw ue → Fill bn bs bw be → Fill un bn nw ne → Fill us bs sw se → Fill uw bw nw sw → Fill ue be ne se →
            Set
    
record Groupoid-Functor (G H : Groupoid) : Set where
  field
    ap-vertex : Groupoid.Vertex G → Groupoid.Vertex H
    ap-path   : ∀ {x y} → Groupoid.Path G x y → Groupoid.Path H (ap-vertex x) (ap-vertex y)
    ap-fill   : ∀ {nw ne sw se} {north : Groupoid.Path G nw ne} {south : Groupoid.Path G sw se} {west : Groupoid.Path G nw sw} {east : Groupoid.Path G ne se} →
      Groupoid.Fill G north south west east → Groupoid.Fill H (ap-path north) (ap-path south) (ap-path west) (ap-path east)
    ap-fill₂  : ∀ {unw une usw use bnw bne bsw bse}
            {un : Groupoid.Path G unw une} {us : Groupoid.Path G usw use} {uw : Groupoid.Path G unw usw} {ue : Groupoid.Path G une use}
            {bn : Groupoid.Path G bnw bne} {bs : Groupoid.Path G bsw bse} {bw : Groupoid.Path G bnw bsw} {be : Groupoid.Path G bne bse}
            {nw : Groupoid.Path G unw bnw} {ne : Groupoid.Path G une bne} {sw : Groupoid.Path G usw bsw} {se : Groupoid.Path G use bse} →
            {top-fill : Groupoid.Fill G un us uw ue} {bottom-fill : Groupoid.Fill G bn bs bw be} {north-fill : Groupoid.Fill G un bn nw ne} {south-fill : Groupoid.Fill G us bs sw se} {west-fill : Groupoid.Fill G uw bw nw sw} {east-fill : Groupoid.Fill G ue be ne se} →
            Groupoid.Fill₂ G top-fill bottom-fill north-fill south-fill west-fill east-fill →
            Groupoid.Fill₂ H (ap-fill top-fill) (ap-fill bottom-fill) (ap-fill north-fill) (ap-fill south-fill) (ap-fill west-fill) (ap-fill east-fill)
            
ap-vertex : ∀ {G H} → Groupoid-Functor G H → Groupoid.Vertex G → Groupoid.Vertex H
ap-vertex = Groupoid-Functor.ap-vertex

ap-path : ∀ {G H x y} (F : Groupoid-Functor G H) → Groupoid.Path G x y → Groupoid.Path H (ap-vertex F x) (ap-vertex F y)
ap-path F = Groupoid-Functor.ap-path F

ap-fill : ∀ {G H nw ne sw se} {north : Groupoid.Path G nw ne} {south : Groupoid.Path G sw se} {west : Groupoid.Path G nw sw} {east : Groupoid.Path G ne se}
                  (F : Groupoid-Functor G H) → Groupoid.Fill G north south west east → Groupoid.Fill H (ap-path F north) (ap-path F south) (ap-path F west) (ap-path F east)
ap-fill F = Groupoid-Functor.ap-fill F

record Groupoid-NatIso {G H} (F F' : Groupoid-Functor G H) : Set where
  field
    comp : ∀ x → Groupoid.Path H (ap-vertex F x) (ap-vertex F' x)
    natural : ∀ {x y} (p : Groupoid.Path G x y) → Groupoid.Fill H (comp x) (comp y) (ap-path F p) (ap-path F' p)
    natural₂ : ∀ {nw ne sw se} {north : Groupoid.Path G nw ne} {south : Groupoid.Path G sw se} {west : Groupoid.Path G nw sw} {east : Groupoid.Path G ne se}
      (fill : Groupoid.Fill G north south west east) → Groupoid.Fill₂ H (natural north) (natural south) (natural west) (natural east) (ap-fill F fill) (ap-fill F' fill)
