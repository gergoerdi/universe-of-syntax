import SimplyTyped.Code

module SimplyTyped.Unscoped {Ty : Set} (Name : Set) (code : SimplyTyped.Code.Code Ty) where

open import Data.Nat
open import Data.List
open SimplyTyped.Code Ty
open import Data.Vec

mutual
  data Form : Set where
    var : Name → Form
    con : Con code → Form

  data Con : Code → Set where
    sg : ∀ {A c} x → Con (c x) → Con (sg A c)
    node : ∀ {shape wt} → (es : Children shape) → Con (node shape wt)

  data Children : List ℕ → Set where
    [] : Children []
    _∣_∷_ : ∀ {k ks} → Vec Name k → Form → Children ks → Children (k ∷ ks)
