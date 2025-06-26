{-# OPTIONS --flat-split --without-K #-}
module testMod where

open import Agda.Builtin.Equality
open import Agda.Primitive

data ⟨♭|_⟩ {@♭ 𝓤} (@♭ A : Set 𝓤) : Set 𝓤 where
  mod♭ : (@♭ a : A) → ⟨♭| A ⟩

ε : ∀ {@♭ 𝓤} {@♭ A : Set 𝓤} → ⟨♭| A ⟩ → A
ε (mod♭ a) = a

♭-map : ∀ {@♭ 𝓤 𝓥} {@♭ A : Set 𝓤} {@♭ B : Set 𝓥}
        → ⟨♭| (A → B) ⟩ → ⟨♭| A ⟩ → ⟨♭| B ⟩
♭-map (mod♭ f) (mod♭ x) = mod♭ (f x)

data ⟨♯|_⟩ {𝓤} (@♯ A : Set 𝓤) : Set 𝓤 where
  mod♯ : (@♯ a : A) → ⟨♯| A ⟩

♯-map : ∀ {𝓤 𝓥} {A : Set 𝓤} {B : Set 𝓥}
        → ⟨♯| (A → B) ⟩ → ⟨♯| A ⟩ → ⟨♯| B ⟩
♯-map (mod♯ f) (mod♯ a) = mod♯ (f a)

η : ∀ {𝓤} {A : Set 𝓤} → A → ⟨♯| A ⟩
η a = mod♯ a

-- Will fail type check if uncommented
-- uh-oh : ∀ {𝓤} {A : Set 𝓤} → ⟨♯| A ⟩ → A
-- uh-oh (mod♯ a) = {!a!}

crispy : ∀ {@♭ 𝓤} {@♭ A : Set 𝓤} → @♭ ⟨♯| A ⟩ → A
crispy (mod♯ a) = a

μ : ∀ {𝓤} {A : Set 𝓤} → @♯ ⟨♯| A ⟩ → ⟨♯| A ⟩
μ a = mod♯ (crispy a)

μ' : ∀ {𝓤} {A : Set 𝓤} → ⟨♯| ⟨♯| A ⟩ ⟩ → ⟨♯| A ⟩
μ' (mod♯ a) = mod♯ (crispy a)

comul : ∀ {𝓤} {A : Set 𝓤} → ⟨♯| A ⟩ → ⟨♯| ⟨♯| A ⟩ ⟩
comul (mod♯ a) = mod♯ (mod♯ a)

♯-rfl : ∀ {𝓤} {A : Set 𝓤} (B : ⟨♯| A ⟩ → Set 𝓤)
        → (f : (a : A) → ⟨♯| B (η a) ⟩)
        → (a : ⟨♯| A ⟩) → ⟨♯| B a ⟩
♯-rfl B f (mod♯ a) = mod♯ (crispy (f a))

♯-rfl-η : ∀ {𝓤} {A : Set 𝓤} {B : ⟨♯| A ⟩ → Set 𝓤}
        → (f : (a : A) → ⟨♯| B (η a) ⟩)
        → (a : A) → ♯-rfl B f (η a) ≡ f a
♯-rfl-η f a with f a
... | mod♯ b = refl

♭-eat-♯ : ∀ {@♭ 𝓤} {@♭ A : Set 𝓤} → ⟨♭| ⟨♯| A ⟩ ⟩ → ⟨♭| A ⟩
♭-eat-♯ (mod♭ (mod♯ a)) = mod♭ a

♭-eat-♯' : ∀ {@♭ 𝓤} {@♭ A : Set 𝓤} → ⟨♭| A ⟩ → ⟨♭| ⟨♯| A ⟩ ⟩
♭-eat-♯' (mod♭ a) = mod♭ (mod♯ a)

♯-eat-♭ : ∀ {@♭ 𝓤} {@♭ A : Set 𝓤} → ⟨♯| ⟨♭| A ⟩ ⟩ → ⟨♯| A ⟩
♯-eat-♭ (mod♯ a) = mod♯ (ε a)

♯-eat-♭' : ∀ {@♭ 𝓤} {@♭ A : Set 𝓤} → ⟨♯| A ⟩ → ⟨♯| ⟨♭| A ⟩ ⟩
♯-eat-♭' m = mod♯ (mod♭ (crispy m))

♯←♭ : ∀ {@♭ 𝓤} {@♭ A : Set 𝓤} → ⟨♭| A ⟩ → ⟨♯| A ⟩
♯←♭ x = η (ε x)

-- ♭←♯ : ∀ {@♭ 𝓤} {@♭ A : Set 𝓤} → ⟨♯| A ⟩ → ⟨♭| A ⟩
-- ♭←♯ (mod♯ a) = mod♭ {!a!}

adj : ∀ {@♭ 𝓤 𝓥} {@♭ A : Set 𝓤} {B : Set 𝓥}
      → ⟨♯| (⟨♭| A ⟩ → B) ⟩ → (A → ⟨♯| B ⟩)
adj (mod♯ f) a = mod♯ (f (mod♭ a))

adj' : ∀ {@♭ 𝓤 𝓥} {@♭ A : Set 𝓤} {@♭ B : @♭ A → Set 𝓥}
       → ⟨♭| ((a : A) → ⟨♯| B a ⟩)⟩ → ⟨♭| ((@♭ a : A) → B a) ⟩
adj' (mod♭ f) = mod♭ (λ b → crispy (f b))


J-♭ : ∀ {@♭ 𝓤} {𝓥} {@♭ A : Set 𝓤} {@♭ a : A}
            (M : (@♭ b : A) → a ≡ b → Set 𝓥)
            (Mrfl : M a refl)
          → ∀ {@♭ b : A} (@♭ p : a ≡ b) → M b p
J-♭ M mrfl refl = mrfl

J-crisp : ∀ {@♭ 𝓤} {@♭ 𝓥} {@♭ A : Set 𝓤} {@♭ a : A}
            (@♭ M : (@♭ b : A) → @♭ a ≡ b → Set 𝓥)
            → @♭ M a refl
            → ∀ {@♭ b : A} (@♭ p : a ≡ b) → M b p
J-crisp M prfl = ε (adj' (mod♭ λ where refl → mod♯ prfl))

flat-subst : {@♭ A : Set} {P : A → Set} → (@♭ x y : A) (@♭ p : x ≡ y)
             → P x → P y
flat-subst x .x refl P = P

-- The following is (correctly) rejected by agda
-- flat-subst' : {@♭ A : Set} {P : A → Set} → (@♭ x y : A) (p : x ≡ y)
--              → P x → P y
-- flat-subst' x .x refl P = P

mod♭≡ : ∀ {@♭ 𝓤} {@♭ A : Set 𝓤} {@♭ a b : A}
        → ⟨♭| a ≡ b ⟩
        → mod♭ a ≡ mod♭ b
mod♭≡ (mod♭ refl) = refl

unmod♭≡ : ∀ {@♭ 𝓤} {@♭ A : Set 𝓤} {@♭ a b : A}
        → mod♭ a ≡ mod♭ b
        → ⟨♭| a ≡ b ⟩
unmod♭≡ refl = mod♭ refl

sec : ∀ {@♭ 𝓤} {@♭ A : Set 𝓤}
      → {@♭ a b : A}
      → ∀ (@♭ p : a ≡ b) → unmod♭≡ (mod♭≡ (mod♭ p)) ≡ mod♭ p
sec = ε (adj' (mod♭ (λ where refl → mod♯ refl)))

data _+_ (A B : Set) : Set where
  inl : A → A + B
  inr : B → A + B

♭⊣♯→ : ∀ {@♭ 𝓤 𝓥} {@♭ A : Set 𝓤} {@♭ B : Set 𝓥}
      → ⟨♭| (⟨♭| A ⟩ → B)⟩ → ⟨♭| (A → ⟨♯| B ⟩) ⟩
♭⊣♯→ (mod♭ f) = mod♭ (λ x → mod♯ (f (mod♭ x)))

♭⊣♯← : ∀ {@♭ 𝓤 𝓥} {@♭ A : Set 𝓤} {@♭ B : Set 𝓥}
       → ⟨♭| (A → ⟨♯| B ⟩) ⟩ → ⟨♭| (⟨♭| A ⟩ → B)⟩
♭⊣♯← (mod♭ f) = mod♭ (λ where (mod♭ x) → crispy (f x))

data ⟨Op|_⟩ {@♭ 𝓤} (@♭ A : Set 𝓤) : Set 𝓤 where
  modOp : (@op a : A) → ⟨Op| A ⟩


♭op→ : ∀ {@♭ 𝓤} {@♭ A : Set 𝓤} → @♭ ⟨Op| A ⟩ → ⟨♭| A ⟩
♭op→ (modOp a) = mod♭ a

♭op← : ∀ {@♭ 𝓤} {@♭ A : Set 𝓤} → @♭ A → ⟨♭| ⟨Op| A ⟩ ⟩
♭op← a = mod♭ (modOp a)

crispy-op : ∀ {@♭ 𝓤} {@♭ A : Set 𝓤} → @♭ ⟨Op| A ⟩ → A
crispy-op (modOp a) = a

op←♭ : ∀ {@♭ 𝓤} {@♭ A : Set 𝓤} → @♭ A → ⟨Op| A ⟩
op←♭ a = modOp a

map-op : ∀ {@♭ 𝓤 𝓥} {@♭ A : Set 𝓤} {@♭ B : Set 𝓥}
         → ⟨Op| (A → B) ⟩ → ⟨Op| A ⟩ → ⟨Op| B ⟩
map-op (modOp f) (modOp a) = modOp (f a)

♭opop : ∀ {@♭ 𝓤} {@♭ A : Set 𝓤} → @♭ ⟨Op| ⟨Op| A ⟩ ⟩ → A
♭opop {A = A} (modOp a) = crispy-op a

-- this is the main obstacle. We want to pattern match on @op ⟨Op| A ⟩
-- but cannot
opop : ∀ {@♭ 𝓤} {@♭ A : Set 𝓤} → ⟨Op| ⟨Op| A ⟩ ⟩ → A
opop (modOp op) = {!op!}

opop⁻¹ : ∀ {@♭ 𝓤} {@♭ A : Set 𝓤} → @♭ A → ⟨Op| ⟨Op| A ⟩ ⟩
opop⁻¹ {A = A} a = modOp (modOp a)

op⊣op→ : ∀ {@♭ 𝓤 𝓥} {@♭ A : Set 𝓤} {@♭ B : Set 𝓥}
        → ⟨♭| (⟨Op| A ⟩ → B) ⟩ → ⟨♭| (A → ⟨Op| B ⟩)⟩
op⊣op→ (mod♭ f) = mod♭ (λ a → map-op (modOp f) (modOp (modOp a)))

op⊣op← : ∀ {@♭ 𝓤 𝓥} {@♭ A : Set 𝓤} {@♭ B : Set 𝓥}
         → ⟨♭| (A → ⟨Op| B ⟩)⟩ → ⟨♭| (⟨Op| A ⟩ → B) ⟩
op⊣op← (mod♭ f) = mod♭ (λ x → opop (map-op (modOp f) x))


elim-op♭ : ∀ {@♭ 𝓤 𝓥} {@♭ A : Set 𝓤} {@♭ B : @♭ A → Set 𝓥}
           → ((@♭ x : A) → B x) → ((@♭ x : ⟨Op| A ⟩) → B (ε (♭op→ x)))
elim-op♭ {A = A} f (modOp a) = f a

record _×_ {𝓤 𝓥} (A : Set 𝓤) (B : Set 𝓥) : Set (𝓤 ⊔ 𝓥) where
  constructor _,_
  field
    fst : A
    snd : B

cocontra : ∀ {@♭ 𝓤} {@♭ A : Set 𝓤} → @♭ A → ⟨Op| A ⟩ × A
cocontra a = (modOp a , a)
