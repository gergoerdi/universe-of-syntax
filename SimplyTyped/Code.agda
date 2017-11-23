module SimplyTyped.Code (Ty : Set) where

open import Data.Nat
open import Data.List
open import Data.List.All
open import Data.Product
open import Data.Vec

data Code : Set₁ where
  some : (A : Set) → (A → Code) → Code
  node : (shape : List ℕ) → (All (λ k → Vec Ty k × Ty) shape → Ty → Set) → Code
