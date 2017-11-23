import SimplyTyped.Code

module SimplyTyped.Typed {Ty : Set} (code : SimplyTyped.Code.Code Ty) where

open import Data.List
open import Data.Nat
open import Data.List.All
open SimplyTyped.Code Ty
open import SimplyTyped.Ctx Ty public
open import Function
open import Data.Vec
open import Data.Product

_<><_ : ∀ {n} → Ctx → Vec Ty n → Ctx
Γ <>< [] = Γ
Γ <>< (t ∷ ts) = (Γ , t) <>< ts

open import SimplyTyped.Ren Ty
ren-<>< : ∀ {Γ Δ n} → Γ ⊇ Δ → (ts : Vec Ty n) → Γ <>< ts ⊇ Δ <>< ts
ren-<>< Γ⊇Δ [] = Γ⊇Δ
ren-<>< Γ⊇Δ (_ ∷ ts) = ren-<>< (keep Γ⊇Δ) ts

mutual
  data Tm (Γ : Ctx) : Ty → Set where
    var : ∀ {t} → Var t Γ → Tm Γ t
    con : ∀ {t} → Con Γ t code → Tm Γ t

  data Con (Γ : Ctx) (t : Ty) : Code → Set where
    some : ∀ {A c} x → Con Γ t (c x) → Con Γ t (some A c)
    node : ∀ {shape wt} → (es : Children Γ shape) → (_ : wt (typesOf es) t) → Con Γ t (node shape wt)

  data ChildrenSchema (Γ : Ctx) : List ℕ → Set where
    [] : ChildrenSchema Γ []
    _∷_ : ∀ {k ks} → (Vec Ty k × Ty) → ChildrenSchema Γ ks → ChildrenSchema Γ (k ∷ ks)

  data Children (Γ : Ctx) : List ℕ → Set where
    [] : Children Γ []
    _∷_ : ∀ {k ks} → (_ : Σ (Vec Ty k) λ ts → Σ Ty λ t → Tm (Γ <>< ts) t) → Children Γ ks → Children Γ (k ∷ ks)

  typesOf : ∀ {Γ shape} → Children Γ shape → All (λ k → Vec Ty k × Ty) shape
  typesOf [] = []
  typesOf ((ts , t , _) ∷ es) = (ts , t) ∷ typesOf es

  --   node : ∀ {Γ t shape wt} {ts : All (λ k → Vec Ty k × Ty) shape} (children : Children Γ ts) → {_ : wt (childrenTypes children) t} → Con (node shape wt) Γ t

  -- data Child (Γ : Ctx) {n : ℕ} : (ts : Vec Ty n) (t : Ty) → Set where
  --   child : ∀ {t} ts → Tm (Γ <>< toList ts) t → Child Γ ts t

  -- data Children (Γ : Ctx) : {shape : List ℕ} → All (λ k → Vec Ty k × Ty) shape → Set where
  --   [] :  Children Γ []
  --   _∷_ : ∀ {k ks bs t ts} → Child Γ ts t → Children Γ {ks} bs → Children Γ {k ∷ ks} ((ts , t) ∷ bs)

  -- childrenTypes : ∀ {Γ} {shape : List ℕ} {ts : All (λ k → Vec Ty k × Ty) shape} (children : Children Γ ts) → All (λ k → Vec Ty k × Ty) shape
  -- childrenTypes [] = []
  -- childrenTypes (child {t} ts _ ∷ xs) = (ts , t) ∷ childrenTypes xs
