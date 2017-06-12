module Syntax.Typing where
open import Semantics
open import Semantics.FibrationEqTwoCongThree
open import Syntax.Context
open import Syntax.Variable

data _⊢_gpd : ∀ Γ → Fibration₂ ⟦ Γ ⟧C → Set where
  -eq- : ∀ {Γ G H} → Γ ⊢ G gpd → Γ ⊢ H gpd → Γ ⊢ Fibration-Eq₂ G H gpd
  
data _⊢₂_∋_ : ∀ Γ (G : Fibration₂ ⟦ Γ ⟧C) → Section₂ G → Set where
  -var- : ∀ {Γ T ⟦x⟧} → Γ var₂ T ∋ ⟦x⟧ → Γ ⊢₂ T ∋ ⟦x⟧
  -eq*- : ∀ {Γ ⟦G⟧ ⟦G'⟧ ⟦H⟧ ⟦H'⟧ ⟦G*⟧ ⟦H*⟧} →
    Γ ⊢₂ Fibration-Eq₂ ⟦G⟧ ⟦G'⟧ ∋ ⟦G*⟧ → Γ ⊢₂ Fibration-Eq₂ ⟦H⟧ ⟦H'⟧ ∋ ⟦H*⟧ →
    Γ ⊢₂ Fibration-Eq₂ (Fibration-Eq₂ ⟦G⟧ ⟦H⟧) (Fibration-Eq₂ ⟦G'⟧ ⟦H'⟧) ∋ Fibration-Eq₂-cong ⟦G*⟧ ⟦H*⟧

--TODO Relabel with cubical notation
data _⊢₁_∋_ : ∀ Γ (S : Fibration₁ ⟦ Γ ⟧C) → Section₁ S → Set where
  -var- : ∀ {Γ T ⟦x⟧} → Γ var₁ T ∋ ⟦x⟧ → Γ ⊢₁ T ∋ ⟦x⟧
  -eq*- : ∀ {Γ}
    {A A' B B' C C' D D' : Fibration₂ ⟦ Γ ⟧C}
    (A* : Section₂ (Fibration-Eq₂ A A')) (B* : Section₂ (Fibration-Eq₂ B B'))
    (C* : Section₂ (Fibration-Eq₂ C C')) (D* : Section₂ (Fibration-Eq₂ D D'))
    {AB : Section₂ (Fibration-Eq₂ A B)} {A'B' : Section₂ (Fibration-Eq₂ A' B')}
    {CD : Section₂ (Fibration-Eq₂ C D)} {C'D' : Section₂ (Fibration-Eq₂ C' D')}
    {A*B*} {C*D*} →
    Γ ⊢₁ EQ₂ A* (Fibration-Eq₂-cong AB A'B') B* ∋ A*B* →
    Γ ⊢₁ EQ₂ C* (Fibration-Eq₂-cong CD C'D') D* ∋ C*D* →
    Γ ⊢₁ EQ₂ (Fibration-Eq₂-cong A* C*)
      (Fibration-Eq₂-cong (Fibration-Eq₂-cong AB CD) (Fibration-Eq₂-cong A'B' C'D'))
      (Fibration-Eq₂-cong B* D*)
    ∋ Fibration-Eq₂-cong₂ A* B* C* D* A*B* C*D*
data _⊢₀_∋_ : ∀ Γ (P : Fibration₀ ⟦ Γ ⟧C) → Section₀ P → Set where
  -var- : ∀ {Γ P ⟦x⟧} → Γ var₀ P ∋ ⟦x⟧ → Γ ⊢₀ P ∋ ⟦x⟧
  -eq***- : ∀ {Γ}
    {A A' B B' C C' D D' E E' F F' G G' H H' : Fibration₂ ⟦ Γ ⟧C}
    {A* : Section₂ (Fibration-Eq₂ A A')} {B* : Section₂ (Fibration-Eq₂ B B')}
    {C* : Section₂ (Fibration-Eq₂ C C')} {D* : Section₂ (Fibration-Eq₂ D D')}
    {E* : Section₂ (Fibration-Eq₂ E E')} {F* : Section₂ (Fibration-Eq₂ F F')}
    {G* : Section₂ (Fibration-Eq₂ G G')} {H* : Section₂ (Fibration-Eq₂ H H')}
    {AB : Section₂ (Fibration-Eq₂ A B)} {A'B' : Section₂ (Fibration-Eq₂ A' B')}
    {CD : Section₂ (Fibration-Eq₂ C D)} {C'D' : Section₂ (Fibration-Eq₂ C' D')}
    {EF : Section₂ (Fibration-Eq₂ E F)} {E'F' : Section₂ (Fibration-Eq₂ E' F')}
    {GH : Section₂ (Fibration-Eq₂ G H)} {G'H' : Section₂ (Fibration-Eq₂ G' H')}
    {AE : Section₂ (Fibration-Eq₂ A E)} {A'E' : Section₂ (Fibration-Eq₂ A' E')}
    {BF : Section₂ (Fibration-Eq₂ B F)} {B'F' : Section₂ (Fibration-Eq₂ B' F')}
    {CG : Section₂ (Fibration-Eq₂ C G)} {C'G' : Section₂ (Fibration-Eq₂ C' G')}
    {DH : Section₂ (Fibration-Eq₂ D H)} {D'H' : Section₂ (Fibration-Eq₂ D' H')}
    {A*B* : Section₁ (EQ₂ A* (Fibration-Eq₂-cong AB A'B') B*)}
    {C*D* : Section₁ (EQ₂ C* (Fibration-Eq₂-cong CD C'D') D*)}
    {E*F* : Section₁ (EQ₂ E* (Fibration-Eq₂-cong EF E'F') F*)}
    {G*H* : Section₁ (EQ₂ G* (Fibration-Eq₂-cong GH G'H') H*)}
    {A*E* : Section₁ (EQ₂ A* (Fibration-Eq₂-cong AE A'E') E*)}
    {B*F* : Section₁ (EQ₂ B* (Fibration-Eq₂-cong BF B'F') F*)}
    {C*G* : Section₁ (EQ₂ C* (Fibration-Eq₂-cong CG C'G') G*)}
    {D*H* : Section₁ (EQ₂ D* (Fibration-Eq₂-cong DH D'H') H*)}
    {ABEF : Section₁ (EQ₂ AB (Fibration-Eq₂-cong AE BF) EF)}
    {A'B'E'F' : Section₁ (EQ₂ A'B' (Fibration-Eq₂-cong A'E' B'F') E'F')}
    {CDGH : Section₁ (EQ₂ CD (Fibration-Eq₂-cong CG DH) GH)}
    {C'D'G'H' : Section₁ (EQ₂ C'D' (Fibration-Eq₂-cong C'G' D'H') G'H')}
    {A*B*E*F*} {C*D*G*H*}
    →
    Γ ⊢₀ EQ₁ A*B* (
      EQ₂-cong A* E* B* F* A*E* (Fibration-Eq₂-cong₂ AB EF A'B' E'F' ABEF A'B'E'F') B*F*)
        E*F*
    ∋ A*B*E*F* →
    Γ ⊢₀ EQ₁ C*D*
      (EQ₂-cong C* G* D* H* C*G*
        (Fibration-Eq₂-cong₂ CD GH C'D' G'H' CDGH C'D'G'H')
      D*H*)
    G*H*
    ∋ C*D*G*H* →
    Γ ⊢₀ EQ₁ (Fibration-Eq₂-cong₂ A* B* C* D* A*B* C*D*)
      (EQ₂-cong (Fibration-Eq₂-cong A* C*) (Fibration-Eq₂-cong E* G*)
        (Fibration-Eq₂-cong B* D*) (Fibration-Eq₂-cong F* H*)
        (Fibration-Eq₂-cong₂ A* E* C* G* A*E* C*G*)
        (Fibration-Eq₂-cong₂
          (Fibration-Eq₂-cong AB CD)
          (Fibration-Eq₂-cong EF GH)
          (Fibration-Eq₂-cong A'B' C'D')
          (Fibration-Eq₂-cong E'F' G'H')
          (Fibration-Eq₂-cong₂ AB EF CD GH ABEF CDGH)
          (Fibration-Eq₂-cong₂ A'B' E'F' C'D' G'H' A'B'E'F' C'D'G'H'))
        (Fibration-Eq₂-cong₂ B* F* D* H* B*F* D*H*))
      (Fibration-Eq₂-cong₂ E* F* G* H* E*F* G*H*)
    ∋ Fibration-Eq₂-cong₃ {⟦ Γ ⟧C} {A} {A'} {B} {B'} {C} {C'} {D} {D'} {E} {E'} {F} {F'} {G} {G'} {H} {H'}
    {A*}
    {B*}
    {C*}
    {D*}
    {E*}
    {F*}
    {G*}
    {H*}
    {AB}
    {A'B'}
    {CD}
    {C'D'}
    {EF}
    {E'F'}
    {GH}
    {G'H'}
    {AE}
    {A'E'}
    {BF}
    {B'F'}
    {CG}
    {C'G'}
    {DH}
    {D'H'}
    {A*B*}
    {C*D*}
    {E*F*}
    {G*H*}
    {A*E*}
    {B*F*}
    {C*G*}
    {D*H*}
    {ABEF}
    {A'B'E'F'}
    {CDGH}
    {C'D'G'H'}
    A*B*E*F* C*D*G*H*
