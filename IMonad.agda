module IMonad where

open import Function
open import Function.Equivalence using (Equivalence; _⇔_)
open import Level
open import Relation.Binary.PropositionalEquality

infixr 10 _:→_
_:→_ : ∀ {l m} → {i : Set l} → (i → Set m) → (i → Set m) → Set (m ⊔ l)
s :→ t = ∀ {i} → s i → t i

record IFunctor {l m} {i o : Set l} (f : (i → Set m) → o → Set m) : Set (l ⊔ suc m) where
  infixl 5 _<$>_
  field
    _<$>_ : ∀ {s t} → (s :→ t) → f s :→ f t
    .<$>-id : ∀ {s t x} → id <$> x ≡ x
    .<$>-∘ : ∀ {s t x} → (s ∘ t) <$> x ≡ s <$> (t <$> x)

data _:=_ {l m} {i : Set l} : Set m → i → i → Set m where
  V : ∀ {a k} → a → (a := k) k

lemma : ∀ {k a t} → ((a := k) :→ t ⇔ (a → t k))
lemma = record {
  to = record {
    _⟨$⟩_ = to;
    cong = cong to};
  from = record {
    _⟨$⟩_ = from;
    cong = cong from}}
  where
    to : ∀ {k a t} → ((a := k) :→ t) → a → t k
    to f x = f (V x)

    from : ∀ {k a t} → (a → t k) → (a := k) :→ t
    from f (V x) = f x


Atkey : ∀ {l m n} → {i : Set l} → ((i → Set m) → i → Set n) → i → i → Set m → Set n
Atkey m i j a = m (a := j) i
