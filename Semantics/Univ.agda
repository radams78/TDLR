module Semantics.Univ where

postulate U₂ : Set
postulate T₂ : U₂ → Set
postulate Eq₂ : U₂ → U₂ → U₂
postulate Eq₂-cong : ∀ {A A' B B'} → T₂ (Eq₂ A A') → T₂ (Eq₂ B B') → T₂ (Eq₂ (Eq₂ A B) (Eq₂ A' B'))

postulate U₁ : Set
postulate T₁ : U₁ → Set
postulate Eq₁ : U₁ → U₁ → U₁
postulate Eq₁-cong : ∀ {A A' B B'} →
                   T₁ (Eq₁ A A') → T₁ (Eq₁ B B') →
                   T₁ (Eq₁ (Eq₁ A B) (Eq₁ A' B'))
postulate eq₂ : ∀ {A B} → T₂ A → T₂ (Eq₂ A B) → T₂ B → U₁
postulate eq₂-cong : ∀ {A A' B B'}
                   {a : T₂ A} {a' : T₂ A'} {b : T₂ B} {b' : T₂ B'}
                   {A* : T₂ (Eq₂ A A')} {B* : T₂ (Eq₂ B B')} {e : T₂ (Eq₂ A B)} {e' : T₂ (Eq₂ A' B')}
                   (a* : T₁ (eq₂ a A* a')) (e* : T₁ (eq₂ e (Eq₂-cong A* B*) e')) (b* : T₁ (eq₂ b B* b')) →
                   T₁ (Eq₁ (eq₂ a e b) (eq₂ a' e' b'))
postulate Eq₂-cong₂ : ∀ {A A' B B' C C' D D'}
                    {A* : T₂ (Eq₂ A A')} {B* : T₂ (Eq₂ B B')} {C* : T₂ (Eq₂ C C')} {D* : T₂ (Eq₂ D D')}
                    {AC : T₂ (Eq₂ A C)} {A'C' : T₂ (Eq₂ A' C')} {BD : T₂ (Eq₂ B D)} {B'D' : T₂ (Eq₂ B' D')} →
                    T₁ (eq₂ A* (Eq₂-cong AC A'C') C*) → T₁ (eq₂ B* (Eq₂-cong BD B'D') D*) →
                    T₁ (eq₂ (Eq₂-cong A* B*) (Eq₂-cong (Eq₂-cong AC BD) (Eq₂-cong A'C' B'D')) (Eq₂-cong C* D*))

postulate U₀ : Set
postulate T₀ : U₀ → Set
postulate Eq₀ : U₀ → U₀ → U₀
postulate eq₁ : ∀ {S T} → T₁ S → T₁ (Eq₁ S T) → T₁ T → U₀
postulate eq₁-cong : ∀ {S S' T T'}
                   {x : T₁ S} {x' : T₁ S'} {y : T₁ T} {y' : T₁ T'}
                   {S* : T₁ (Eq₁ S S')} {T* : T₁ (Eq₁ T T')} {e : T₁ (Eq₁ S T)} {e' : T₁ (Eq₁ S' T')} →
                   T₀ (eq₁ x S* x') → T₀ (eq₁ e (Eq₁-cong S* T*) e') → T₀ (eq₁ y T* y') →
                   T₀ (Eq₀ (eq₁ x e y) (eq₁ x' e' y'))
postulate eq₂-cong₂ : ∀ {A A' B B' C C' D D'}
                      {a : T₂ A} {a' : T₂ A'} {b : T₂ B} {b' : T₂ B'} {c : T₂ C} {c' : T₂ C'} {d : T₂ D} {d' : T₂ D'}
                      {A* : T₂ (Eq₂ A A')} {B* : T₂ (Eq₂ B B')} {C* : T₂ (Eq₂ C C')} {D* : T₂ (Eq₂ D D')}
                      {e : T₂ (Eq₂ A B)} {e' : T₂ (Eq₂ A' B')} {f : T₂ (Eq₂ C D)} {f' : T₂ (Eq₂ C' D')}
                      {AC : T₂ (Eq₂ A C)} {A'C' : T₂ (Eq₂ A' C')} {BD : T₂ (Eq₂ B D)} {B'D' : T₂ (Eq₂ B' D')}
                      {a* : T₁ (eq₂ a A* a')} {b* : T₁ (eq₂ b B* b')} {c* : T₁ (eq₂ c C* c')} {d* : T₁ (eq₂ d D* d')}
                      {ac : T₁ (eq₂ a AC c)} {a'c' : T₁ (eq₂ a' A'C' c')} {bd : T₁ (eq₂ b BD d)} {b'd' : T₁ (eq₂ b' B'D' d')}
                      {A*C* : T₁ (eq₂ A* (Eq₂-cong AC A'C') C*)} {B*D* : T₁ (eq₂ B* (Eq₂-cong BD B'D') D*)}
                      {e* : T₁ (eq₂ e (Eq₂-cong A* B*) e')} {f* : T₁ (eq₂ f (Eq₂-cong C* D*) f')}
                      {ef : T₁ (eq₂ e (Eq₂-cong AC BD) f)} {e'f' : T₁ (eq₂ e' (Eq₂-cong A'C' B'D') f')} →
                      T₀ (eq₁ a* (eq₂-cong ac A*C* a'c') c*) → T₀ (eq₁ e* (eq₂-cong ef (Eq₂-cong₂ A*C* B*D*) e'f') f*) →
                      T₀ (eq₁ b* (eq₂-cong bd B*D* b'd') d*) →
                      T₀ (eq₁ (eq₂-cong a* e* b*) (Eq₁-cong (eq₂-cong ac ef bd) (eq₂-cong a'c' e'f' b'd')) (eq₂-cong c* f* d*))
