{-# OPTIONS --safe #-}

module MuCalc101 where

--------------
-- Preamble --
--------------

open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong)

data ℕ : Set where
  zero : ℕ
  suc : ℕ → ℕ
{-# BUILTIN NATURAL ℕ #-}

data Fin : ℕ → Set where
  zero : ∀ {n} → Fin (suc n)
  suc : ∀ {n} → Fin n → Fin (suc n)

record _≃_ (X Y : Set) : Set where
  field
    to : X → Y
    from : Y → X
    from-to : ∀ x → from (to x) ≡ x
    to-from : ∀ y → to (from y) ≡ y
open _≃_

-----------------------------
-- Simple de Bruijn Syntax --
-----------------------------

data DB (At : Set) : Set where
  var : ℕ → DB At
  atom : At → DB At
  ■ : DB At → DB At
  _∧_ : DB At → DB At → DB At
  μ : DB At → DB At


----------------------------------
-- Well-Scoped de Bruijn Syntax --
----------------------------------

data WS (At : Set) (n : ℕ) : Set where
  var : (x : Fin n) → WS At n
  atom : (x : At) → WS At n
  ■ : (ϕ : WS At n) → WS At n
  _∧_ : (ϕ ψ : WS At n) → WS At n
  μ : (ϕ : WS At (suc n)) → WS At n

data IsFP {At : Set} {n : ℕ} : WS At n → Set where
  instance μ : {ϕ : WS At (suc n)} → IsFP (μ ϕ)


---------------
-- Thinnings --
---------------

{- Everybody's Got To Be Somewhere, Conor Mc Bride, 2018-}

data Thin : ℕ → ℕ → Set where
  end : Thin 0 0                                   -- ε
  drop : ∀ {i j} → Thin i j → Thin i (suc j)       -- 0 ∷_
  keep : ∀ {i j} → Thin i j → Thin (suc i) (suc j) -- 1 ∷_

-- Composition of thinnings.
_⨾_ : ∀ {i j k} → Thin i j → Thin j k → Thin i k
θ ⨾ drop ϕ = drop (θ ⨾ ϕ)
drop θ ⨾ keep ϕ = drop (θ ⨾ ϕ)
keep θ ⨾ keep ϕ = keep (θ ⨾ ϕ)
end ⨾ end = end

-- The identity thinning; all 1's.
ones : ∀ {i} → Thin i i
ones {zero} = end
ones {suc x} = keep ones

{- Ghost of a category moans in background -}

embed : {i j : ℕ} → Thin i j → Fin i → Fin j
embed (drop θ) x = suc (embed θ x)
embed (keep θ) zero = zero
embed (keep θ) (suc x) = suc (embed θ x)

-- The identity thinning really is the identity.
embed-ones : ∀ {i} → (x : Fin i) → embed ones x ≡ x
embed-ones zero = refl
embed-ones (suc x) = cong suc (embed-ones x)

----------------------
-- Fin n ≃ Thin 1 n --
----------------------

-- The "all zeros" thinning.
zeros : ∀ {n} → Thin 0 n
zeros {zero} = end
zeros {suc n} = drop zeros

zeros-unique : ∀ {n} → (θ : Thin 0 n) → zeros ≡ θ
zeros-unique (drop θ) = cong drop (zeros-unique θ)
zeros-unique end = refl

Fin→Thin : ∀ {n} → Fin n → Thin 1 n
Fin→Thin zero = keep zeros
Fin→Thin (suc x) = drop (Fin→Thin x)

Thin→Fin : ∀ {n} → Thin 1 n → Fin n
Thin→Fin (drop x) = suc (Thin→Fin x)
Thin→Fin (keep x) = zero

FTF : ∀ {n} → (x : Fin n) → Thin→Fin (Fin→Thin x) ≡ x
FTF zero = refl
FTF (suc x) = cong suc (FTF x)

TFT : ∀ {n} → (x : Thin 1 n) → Fin→Thin (Thin→Fin x) ≡ x
TFT (drop x) = cong drop (TFT x)
TFT (keep x) = cong keep (zeros-unique x)

Fin≃Thin : ∀ {n} → Fin n ≃ Thin 1 n
to Fin≃Thin = Fin→Thin
from Fin≃Thin = Thin→Fin
from-to Fin≃Thin = FTF
to-from Fin≃Thin = TFT


-- Thus, if we wish, we are justified in defining Fin in terms of Thin:
Fin' = Thin 1

-- Then embed is just composition of thinnings.
embed' : ∀ {i j} → Thin i j → Fin' i → Fin' j
embed' θ x = x ⨾ θ

---------------
-- Weakening --
---------------




------------------
-- Substitution --
------------------

{- Exercise: Replace Fin with Fin' in the definition of WS, and reimplement the following. -}

-- A parallel substitution is a map from variables to formulae.
Subst : Set → ℕ → ℕ → Set
Subst At i j = Fin i → WS At j

-- Single substitutions are the special case where i = suc j.
single-sub : ∀ {At j} → WS At j → Subst At (suc j) j
single-sub ϕ zero = ϕ
single-sub ϕ (suc x) = var x

-- Scope extension
ext : ∀ {i j} → (Fin i → Fin j)
    → Fin (suc i) → Fin (suc j)
ext ρ zero = zero
ext ρ (suc x) = suc (ρ x)

-- Rescoping
rescope : ∀ {At i j} → (Fin i → Fin j) -- if we have an mapping of i vars to j vars...
        → WS At i → WS At j -- then we can rescope i-terms to be j-terms.
rescope ρ (var x) = var (ρ x)
rescope ρ (atom x) = atom x
rescope ρ (■ ϕ) = ■ (rescope ρ ϕ)
rescope ρ (ϕ ∧ ψ) = (rescope ρ ϕ) ∧ (rescope ρ ψ)
rescope ρ (μ ϕ) = μ (rescope (ext ρ) ϕ)


-- Substitution extension
exts : ∀ {At n m} → Subst At n m → Subst At (suc n) (suc m)
exts σ zero = var zero
exts σ (suc x) = rescope suc (σ x)


-- Executing a parallel substitution
sub : ∀ {At i j} → Subst At i j → WS At i → WS At j
sub σ (var x) = σ x
sub σ (atom x) = atom x
sub σ (■ ϕ) = ■ (sub σ ϕ)
sub σ (ϕ ∧ ψ) = sub σ ϕ ∧ sub σ ψ
sub σ (μ ϕ) = μ (sub (exts σ) ϕ)


-- Finally, the definition we always wanted, single substitution.
_[_] : ∀ {At i} → WS At (suc i) → WS At i → WS At i
ϕ [ δ ] = sub (single-sub δ) ϕ


-- And now fixpoint unfolding is a single substitution.
unfold : ∀ {At i} (ϕ : WS At i) → {{_ : IsFP ϕ}} → WS At i
unfold (μ ϕ) = ϕ [ μ ϕ ]

---------------
-- Weakening --
---------------

-- With all the work we've done so far, this is pretty much free.
weaken : ∀ {At i j} → Thin i j → WS At i → WS At j
weaken θ = rescope (embed θ)

-- Why the embedding of a thinning? Why not just any (Fin i → Fin j)?
