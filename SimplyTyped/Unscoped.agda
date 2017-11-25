import SimplyTyped.Code

module SimplyTyped.Unscoped {Ty : Set} (Name : Set) (code : SimplyTyped.Code.Code Ty) where

open import Data.Nat
open import Data.List
open import Data.List.All
open SimplyTyped.Code Ty
open import Data.Vec
open import Function

mutual
  data Form : Set where
    var : Name → Form
    con : Con code → Form

  data Con : Code → Set where
    sg : ∀ {A c} x → Con (c x) → Con (sg A c)
    node : ∀ {n shape wt} → (Vec Name n) → (es : All (const Form) shape) → Con (node n shape wt)
