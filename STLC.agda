module STLC where

infixr 20 _▷_
data Ty : Set where
  ∙   : Ty
  _▷_ : Ty → Ty → Ty
  Bool : Ty

open import SimplyTyped.Code Ty
open import Data.Nat
open import Data.Vec
open import Data.List
open import Data.List.All
open import Data.Product
open import Relation.Binary.PropositionalEquality

data `STLC : Set where
  `lam `app : `STLC
  `true `false `if : `STLC

STLC : Code
STLC = sg `STLC λ
  { `lam   → sg Ty λ t → node 1 ((bound ∷ []) ∷ []) λ { (t′ ∷ []) (u ∷ []) t₀ → t′ ≡ t × t₀ ≡ t ▷ u }
  ; `app   → node 0 ([] ∷ [] ∷ []) λ { [] (t₁ ∷ t₂ ∷ []) t → t₁ ≡ t₂ ▷ t }
  ; `true  → node 0 [] λ { [] [] → Bool ≡_ }
  ; `false → node 0 [] λ { [] [] → Bool ≡_ }
  ; `if    → node 0 ([] ∷ [] ∷ [] ∷ []) (λ { [] (b ∷ t₁ ∷ t₂ ∷ []) t → b ≡ Bool × t₁ ≡ t₂ × t₁ ≡ t })
  }

open import SimplyTyped.Ctx Ty public
open import SimplyTyped.Typed STLC public
open import SimplyTyped.Sub STLC public

[var] : ∀ {t Γ} → Var t Γ → Tm Γ t
[var] = var

-- [lam] : ∀ {Γ u} t → Tm (Γ , t) u → Tm Γ (t ▷ u)
pattern [lam] t e = con (sg `lam (sg t (node (_ ∷ []) (e ∷ []) {{refl , refl}})))

-- _[·]_ : ∀ {Γ u t} → Tm Γ (u ▷ t) → Tm Γ u → Tm Γ t
pattern _[·]_ f e = con (sg `app (node [] (f ∷ e ∷ []) {{refl}}))

-- [true] : ∀ {Γ} → Tm Γ Bool
pattern [true] = con (sg `true (node [] [] {{refl}}))
pattern [false] = con (sg `false (node [] [] {{refl}}))

-- [if]_[then]_[else]_ : ∀ {Γ t} → Tm Γ Bool → Tm Γ t → Tm Γ t → Tm Γ t
pattern [if]_[then]_[else]_ b thn els = con (sg `if (node [] (b ∷ thn ∷ els ∷ []) {{refl , (refl , refl)}}))
