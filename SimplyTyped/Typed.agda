import SimplyTyped.Code

module SimplyTyped.Typed {Ty : Set} (code : SimplyTyped.Code.Code Ty) where

open import Data.List
open import Data.Nat
open import Data.List.All
open SimplyTyped.Code Ty
open import SimplyTyped.Ctx Ty
open import Data.Vec
open import Data.Product
open import Function

visible : ∀ {n} → Vec Binder n → Vec Ty n → List Ty
visible []             []       = []
visible (bound ∷ bs)   (t ∷ ts) = t ∷ visible bs ts
visible (unbound ∷ bs) (_ ∷ ts) = visible bs ts

mutual
  data Tm (Γ : Ctx) : Ty → Set where
    var : ∀ {t} → Var t Γ → Tm Γ t
    con : ∀ {t} → Con Γ t code → Tm Γ t

  data Con (Γ : Ctx) (t : Ty) : Code → Set where
    sg : ∀ {A c} x → Con Γ t (c x) → Con Γ t (sg A c)
    node : ∀ {n shape wt} (ts₀ : Vec Ty n) {ts : All (const Ty) shape} (es : Children Γ ts₀ ts) →
      {{_ : wt ts₀ ts t}} → Con Γ t (node n shape wt)

  data Children (Γ : Ctx) {n : ℕ} (ts₀ : Vec Ty n) : {sh : Shape n} → All (const Ty) sh → Set where
    [] : Children Γ ts₀ []
    _∷_ : ∀ {bs sh t ts} → Tm (Γ <>< visible bs ts₀) t → Children Γ ts₀ {sh} ts → Children Γ ts₀ {bs ∷ sh} (t ∷ ts)
