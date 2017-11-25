module SimplyTyped.Code (Ty : Set) where

open import Data.Nat
open import Data.List
open import Data.List.All
open import Data.Product
open import Data.Vec
open import Function

Schema : List ℕ → Set
Schema = All (λ k → Vec Ty k × Ty)

data Binder : Set where
  bound unbound : Binder

Shape : ℕ → Set
Shape n = List (Vec Binder n)

data Code : Set₁ where
  sg : (A : Set) → (A → Code) → Code
  node : (n : ℕ) (shape : Shape n) (wt : Vec Ty n → All (const Ty) shape → Ty → Set) → Code
