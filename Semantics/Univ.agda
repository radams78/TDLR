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
postulate Eq₁-cong₂ : ∀ {NWU NWD NEU NED SWU SWD SEU SED}
                    {NW : T₁ (Eq₁ NWU NWD)} {NE : T₁ (Eq₁ NEU NED)} {SW : T₁ (Eq₁ SWU SWD)} {SE : T₁ (Eq₁ SEU SED)}
                    {WU : T₁ (Eq₁ NWU SWU)} {WD : T₁ (Eq₁ NWD SWD)} {EU : T₁ (Eq₁ NEU SEU)} {ED : T₁ (Eq₁ NED SED)} → 
                    T₀ (eq₁ NW (Eq₁-cong WU WD) SW) → T₀ (eq₁ NE (Eq₁-cong EU ED) SE) →
                    T₀ (eq₁ (Eq₁-cong NW NE) (Eq₁-cong (Eq₁-cong WU EU) (Eq₁-cong WD ED)) (Eq₁-cong SW SE))
postulate Eq₂-cong₃ : ∀ {NWU NWU' NWD NWD' NEU NEU' NED NED' SWU SWU' SWD SWD' SEU SEU' SED SED'}
                    {NWU* : T₂ (Eq₂ NWU NWU')} {NWD* : T₂ (Eq₂ NWD NWD')} {NEU* : T₂ (Eq₂ NEU NEU')} {NED* : T₂ (Eq₂ NED NED')}
                    {SWU* : T₂ (Eq₂ SWU SWU')} {SWD* : T₂ (Eq₂ SWD SWD')} {SEU* : T₂ (Eq₂ SEU SEU')} {SED* : T₂ (Eq₂ SED SED')}
                    {NW : T₂ (Eq₂ NWU NWD)} {NW' : T₂ (Eq₂ NWU' NWD')} {NE : T₂ (Eq₂ NEU NED)} {NE' : T₂ (Eq₂ NEU' NED')}
                    {SW : T₂ (Eq₂ SWU SWD)} {SW' : T₂ (Eq₂ SWU' SWD')} {SE : T₂ (Eq₂ SEU SED)} {SE' : T₂ (Eq₂ SEU' SED')}
                    {WU : T₂ (Eq₂ NWU SWU)} {WU' : T₂ (Eq₂ NWU' SWU')} {EU : T₂ (Eq₂ NEU SEU)} {EU' : T₂ (Eq₂ NEU' SEU')}
                    {WD : T₂ (Eq₂ NWD SWD)} {WD' : T₂ (Eq₂ NWD' SWD')} {ED : T₂ (Eq₂ NED SED)} {ED' : T₂ (Eq₂ NED' SED')}
                    {NW* : T₁ (eq₂ NW (Eq₂-cong NWU* NWD*) NW')} {NE* : T₁ (eq₂ NE (Eq₂-cong NEU* NED*) NE')}
                    {SW* : T₁ (eq₂ SW (Eq₂-cong SWU* SWD*) SW')} {SE* : T₁ (eq₂ SE (Eq₂-cong SEU* SED*) SE')}
                    {WU* : T₁ (eq₂ NWU* (Eq₂-cong WU WU') SWU*)} {WD* : T₁ (eq₂ NWD* (Eq₂-cong WD WD') SWD*)}
                    {EU* : T₁ (eq₂ NEU* (Eq₂-cong EU EU') SEU*)} {ED* : T₁ (eq₂ NED* (Eq₂-cong ED ED') SED*)}
                    {W : T₁ (eq₂ NW (Eq₂-cong WU WD) SW)} {E : T₁ (eq₂ NE (Eq₂-cong EU ED) SE)}
                    {W' : T₁ (eq₂ NW' (Eq₂-cong WU' WD') SW')} {E' : T₁ (eq₂ NE' (Eq₂-cong EU' ED') SE')} →
                    T₀ (eq₁ NW* (eq₂-cong W (Eq₂-cong₂ WU* WD*) W') SW*) →  T₀ (eq₁ NE* (eq₂-cong E (Eq₂-cong₂ EU* ED*) E') SE*) →
                    T₀ (eq₁ (Eq₂-cong₂ NW* NE*) (eq₂-cong (Eq₂-cong₂ W E) (Eq₂-cong₂ (Eq₂-cong₂ WU* EU*) (Eq₂-cong₂ WD* ED*)) (Eq₂-cong₂ W' E')) (Eq₂-cong₂ SW* SE*))
