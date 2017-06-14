{-# OPTIONS --rewriting #-}

module Semantics.Univ.UnivOne where

open import Semantics.Univ.UnivTwo

postulate _▷_ : ∀ {A : Set} → A → A → Set
{-# BUILTIN REWRITE _▷_ #-}

postulate u₁ : U₂
U₁ : Set
U₁ = T₂ u₁
postulate T₁ : U₁ → Set

postulate Eq₁ : U₁ → U₁ → U₁
postulate Eq₁-cong : ∀ {A A' B B'} →
                   T₁ (Eq₁ A A') → T₁ (Eq₁ B B') →
                   T₁ (Eq₁ (Eq₁ A B) (Eq₁ A' B'))

postulate Pi₁ : ∀ A → (T₂ A → U₁) → U₁
postulate Λ₁ : ∀ {A} {B} → (∀ a → T₁ (B a)) → T₁ (Pi₁ A B)
postulate App₁ : ∀ {A} {B} → T₁ (Pi₁ A B) → ∀ (a : T₂ A) → T₁ (B a)
postulate Beta₁ : ∀ {A} {B} {b} {a} → App₁ {A} {B} (Λ₁ b) a ▷ b a
{-# REWRITE Beta₁ #-}

postulate _⇒₁_ : U₁ → U₁ → U₁
postulate lam₁ : ∀ {A} {B} → (T₁ A → T₁ B) → T₁ (A ⇒₁ B)
postulate app₁ : ∀ {A} {B} → T₁ (A ⇒₁ B) → T₁ A → T₁ B
postulate beta₁ : ∀ {A} {B} {b} {a} → app₁ {A} {B} (lam₁ b) a ▷ b a
{-# REWRITE beta₁ #-}

postulate eq₂ : ∀ {A B} → T₂ A → T₂ (Eq₂ A B) → T₂ B → U₁
postulate Pi₁* : ∀ {A A' B B'} (A* : T₂ (Eq₂ A A')) →
               (∀ a a' → T₁ (eq₂ a A* a') → T₁ (Eq₁ (B a) (B' a'))) →
               T₁ (Eq₁ (Pi₁ A B) (Pi₁ A' B'))
postulate ⇒₁* : ∀ {A A' B B'} → T₁ (Eq₁ A A') → T₁ (Eq₁ B B') → T₁ (Eq₁ (A ⇒₁ B) (A' ⇒₁ B'))

postulate eq₂-Eq₂-cong : ∀ {A A' B B'}
                       (A* : T₂ (Eq₂ A A')) (B* : T₂ (Eq₂ B B')) (e : T₂ (Eq₂ A B)) (e' : T₂ (Eq₂ A' B')) →
                       eq₂ e (Eq₂-cong A* B*) e' ▷ Pi₁ A (λ a → Pi₁ A' (λ a' → Pi₁ B (λ b → Pi₁ B' (λ b' → eq₂ a A* a' ⇒₁ (eq₂ b B* b' ⇒₁ Eq₁ (eq₂ a e b) (eq₂ a' e' b'))))))
{-# REWRITE eq₂-Eq₂-cong #-}

eq₂-cong : ∀ {A A' B B'}
  {a : T₂ A} {a' : T₂ A'} {b : T₂ B} {b' : T₂ B'}
  {A* : T₂ (Eq₂ A A')} {B* : T₂ (Eq₂ B B')} {e : T₂ (Eq₂ A B)} {e' : T₂ (Eq₂ A' B')}
  (a* : T₁ (eq₂ a A* a')) (e* : T₁ (eq₂ e (Eq₂-cong A* B*) e')) (b* : T₁ (eq₂ b B* b')) →
  T₁ (Eq₁ (eq₂ a e b) (eq₂ a' e' b'))
eq₂-cong {a = a} {a'} {b} {b'} a* e* b* = app₁ (app₁ (App₁ (App₁ (App₁ (App₁ e* a) a') b) b') a*) b*

Eq₂-cong₂ : ∀ {A A' B B' C C' D D'}
  {A* : T₂ (Eq₂ A A')} {B* : T₂ (Eq₂ B B')} {C* : T₂ (Eq₂ C C')} {D* : T₂ (Eq₂ D D')}
  {AC : T₂ (Eq₂ A C)} {A'C' : T₂ (Eq₂ A' C')} {BD : T₂ (Eq₂ B D)} {B'D' : T₂ (Eq₂ B' D')}→
  T₁ (eq₂ A* (Eq₂-cong AC A'C') C*) → T₁ (eq₂ B* (Eq₂-cong BD B'D') D*) →
  T₁ (eq₂ (Eq₂-cong A* B*) (Eq₂-cong (Eq₂-cong AC BD) (Eq₂-cong A'C' B'D')) (Eq₂-cong C* D*))
Eq₂-cong₂ {AC = AC} {A'C'} {BD} {B'D'} A*C* B*D* = Λ₁ (λ AB → Λ₁ (λ CD → Λ₁ (λ A'B' → Λ₁ (λ C'D' →
  lam₁ (λ AB∼CD → lam₁ (λ A'B'∼C'D' →
  Pi₁* AC (λ a c ac →
  Pi₁* A'C' (λ a' c' a'c' →
  Pi₁* BD (λ b d bd →
  Pi₁* B'D' (λ b' d' b'd' →
  ⇒₁* (eq₂-cong ac A*C* a'c')
  (⇒₁* (eq₂-cong bd B*D* b'd')
  (Eq₁-cong (eq₂-cong ac AB∼CD bd) (eq₂-cong a'c' A'B'∼C'D' b'd')))))))))))))
