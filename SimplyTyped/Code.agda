module SimplyTyped.Code (Ty : Set) where

open import Data.Nat
open import Data.List
open import Data.List.All
open import Data.Product
open import Data.Vec

Schema : List ℕ → Set
Schema = All (λ k → Vec Ty k × Ty)

data Code : Set₁ where
  some : (A : Set) → (A → Code) → Code
  node : (shape : List ℕ) → (Schema shape → Ty → Set) → Code
