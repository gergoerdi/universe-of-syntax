import SimplyTyped.Code

module SimplyTyped.Untyped {Ty : Set} (code : SimplyTyped.Code.Code Ty) where

open import Data.List
open import Data.Nat
open import Data.List.All
open SimplyTyped.Code Ty
open import Function
open import Data.Vec
open import Data.Product
open import Data.Fin hiding (_+_)

mutual
  data Expr (Γ : ℕ) : Set where
    var : Fin Γ → Expr Γ
    con : Con Γ code → Expr Γ

  data Con (Γ : ℕ) : Code → Set where
    sg : ∀ {A c} x → Con Γ (c x) → Con Γ (sg A c)
    node : ∀ {shape wt} → (es : Children Γ shape) → Con Γ (node shape wt)

  data Children (Γ : ℕ) : List ℕ → Set where
    [] : Children Γ []
    _∷_ : ∀ {k ks} → Expr (k + Γ) → Children Γ ks → Children Γ (k ∷ ks)
