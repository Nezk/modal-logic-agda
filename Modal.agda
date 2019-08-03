module Modal where

open import Agda.Primitive

U : ∀ i → Set (lsuc i)
U i = Set i

U₀ : U (lsuc lzero)
U₀ = U lzero

U₁ : U (lsuc (lsuc lzero))
U₁ = U (lsuc lzero)

data ⊥ : U₀ where
data ⊤ : U₀ where
  ★ : ⊤

~_ : U₀ → U₀
~ A = A → ⊥

data _+_ (A : U₀) (B : U₀) : U₀ where
  Left  : A → A + B
  Right : B → A + B

data _×_ (A : U₀) (B : U₀) : U₀ where
  _,_ : A → B → A × B

data Σ {i} (A : U i) (P : A → U i) : U i where
  _,_ : (x : A) → (P x) → Σ A P

postulate
  World : U₀
  Indiv : U₀
  _~_ : World → World → U₀
  refl : (w : World) → w ~ w

ℙ : U₁
ℙ = World → U₀

¬_ : ℙ → World → U₀
¬_ p w = ~ (p w)

liftMod : (U₀ → U₀ → U₀) → ℙ → ℙ → World → U₀
liftMod f p q w = f (p w) (q w)

_∧_ : ℙ → ℙ → World → U₀
_∧_ = liftMod _×_

_∨_ : ℙ → ℙ → World → U₀
_∨_ = liftMod _+_

_⇒_ : ℙ → ℙ → World → U₀
_⇒_ = liftMod λ A B → A → B

_⇔_ : ℙ → ℙ → World → U₀
_⇔_ = liftMod λ A B → (A → B) × (B → A)

□ : ℙ → World → U₀
□ p world = (w : World) → w ~ world → p w

◇ : ℙ → World → U₀
◇ p world = Σ World λ w → w ~ world → p w

[_] : ℙ → U₀
[_] p = (w : World) → p w

th0 : (p : ℙ) → [ □ p ⇒ p ]
th0 p = λ w x → x w (refl w)

th1 : (p : ℙ) → [ p ⇒ ◇ p ]
th1 p = λ w z → w , λ _ → z

th2 : (p q : ℙ) → [ □ (p ⇒ q) ⇒ (□ p ⇒ □ q) ]
th2 p q = λ w0 □p⇒q → λ □p w1 r →
  let t = □p⇒q w1 r in t (□p w1 r)

th3 : (p : ℙ) → [ (□ (□ p)) ⇒ (□ (◇ p)) ]
th3 p = λ w0 x0 w1 x1 → w1 , x0 w1 x1 w1

th4 : (p : ℙ) → [ (□ (□ p)) ⇒ (◇ (◇ p)) ]
th4 p = λ w z → w , (λ x → w , (λ x1 → z w x1 w x1))

