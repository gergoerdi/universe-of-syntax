module SimplyTyped.Ctx {a : _} (A : Set a) where

open import Data.List

infixr 4 _,_

data Ctx : Set a where
  ∅ : Ctx
  _,_ : Ctx → A → Ctx

data Var (t : A) : Ctx → Set where
  vz : ∀ {Γ} → Var t (Γ , t)
  vs : ∀ {u Γ} → Var t Γ → Var t (Γ , u)

_<><_ : Ctx → List A → Ctx
Γ <>< [] = Γ
Γ <>< (t ∷ ts) = (Γ , t) <>< ts
