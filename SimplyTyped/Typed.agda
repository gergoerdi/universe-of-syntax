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

mutual
  data Tm (Γ : Ctx) : Ty → Set where
    var : ∀ {t} → Var t Γ → Tm Γ t
    con : ∀ {t} → Con Γ t code → Tm Γ t

  data Con (Γ : Ctx) (t : Ty) : Code → Set where
    some : ∀ {A c} x → Con Γ t (c x) → Con Γ t (some A c)
    node : ∀ {shape wt} (schema : Schema shape) → (es : Children Γ schema) → {{_ : wt schema t}} → Con Γ t (node shape wt)

  data Children (Γ : Ctx) : {shape : List ℕ} → Schema shape → Set where
    [] : Children Γ []
    _∷_ : ∀ {k ks ss ts t} → Tm (Γ <>< ts) t → Children Γ {ks} ss → Children Γ {k ∷ ks} ((ts , t) ∷ ss)
