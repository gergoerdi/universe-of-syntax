import SimplyTyped.Code

module SimplyTyped.Untyped {Ty : Set} (code : SimplyTyped.Code.Code Ty) where

open import Data.List using ([]; _∷_)
open import Data.Nat
open import Data.List.All
open SimplyTyped.Code Ty
open import Function
open import Data.Vec
open import Data.Product
open import Data.Fin hiding (_+_)
open import Data.Unit

visibleCount : ∀ {n} → Vec Binder n → ℕ
visibleCount []             = 0
visibleCount (bound ∷ bs)   = suc (visibleCount bs)
visibleCount (unbound ∷ bs) = visibleCount bs

mutual
  data Expr (Γ : ℕ) : Set where
    var : Fin Γ → Expr Γ
    con : Con Γ code → Expr Γ

  data Con (Γ : ℕ) : Code → Set where
    sg : ∀ {A c} x → Con Γ (c x) → Con Γ (sg A c)
    node : ∀ {n shape wt} (es : Children Γ shape) → Con Γ (node n shape wt)

  data Children (Γ : ℕ) : ∀ {n} → Shape n → Set where
    [] : ∀ {n} → Children Γ {n} []
    _∷_ : ∀ {n k ks} → Expr (visibleCount k + Γ) → Children Γ {n} ks → Children Γ (k ∷ ks)
