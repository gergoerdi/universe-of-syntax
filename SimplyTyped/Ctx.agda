module SimplyTyped.Ctx {a : _} (A : Set a) where

open import Relation.Binary.PropositionalEquality

infixr 4 _,_

data Ctx : Set a where
  ∅ : Ctx
  _,_ : Ctx → A → Ctx

data Var (t : A) : Ctx → Set where
  vz : ∀ {Γ} → Var t (Γ , t)
  vs : ∀ {u Γ} → Var t Γ → Var t (Γ , u)
