import SimplyTyped.Code
open import Relation.Binary
open import Relation.Binary.PropositionalEquality

module SimplyTyped.ScopeCheck
  {Ty : Set} (code : SimplyTyped.Code.Code Ty)
  {Name : Set} (_≟ₙ_ : Decidable (_≡_ {A = Name}))
  where

open SimplyTyped.Code Ty
open import SimplyTyped.Untyped code
open import SimplyTyped.Unscoped code Name renaming (Con to Conₙ)
open import SimplyTyped.EraseType code using (x+sy≡sx+y)

open import Data.Nat
open import Data.Fin using (Fin; zero; suc)
open import Data.Vec using (Vec; []; _∷_)
open import Data.List
open import Data.List.All
open import Function
open import Relation.Nullary

Scope : ℕ → Set
Scope n = Vec Name n

bind : ∀ {n n′} → Scope n → Vec Name n′ → (bs : Vec Binder n′) → Scope (visibleCount bs + n)
bind     Γ [] []             = Γ
bind {n} Γ (v ∷ vs) (bound ∷ bs)   = subst (Vec Name) (x+sy≡sx+y (visibleCount bs) n) (bind (v ∷ Γ) vs bs)
bind     Γ (v ∷ vs) (unbound ∷ bs) = bind Γ vs bs

open import Category.Monad

module _ {m} {M : Set m → Set m} (Mon : RawMonad M) where
  open RawMonad Mon

  sequenceAll : ∀ {A : Set} {B : A → Set m} {xs : List A} → All (M ∘ B) xs → M (All B xs)
  sequenceAll []       = pure []
  sequenceAll (x ∷ xs) = _∷_ <$> x ⊛ sequenceAll xs

open import Data.Maybe hiding (All)

open import Level renaming (zero to lzero)
open import Category.Monad
open RawMonadPlus (Data.Maybe.monadPlus {lzero})

lookupName : ∀ {n} → Scope n → Name → Maybe (Fin n)
lookupName []      n = nothing
lookupName (x ∷ Γ) n with x ≟ₙ n
lookupName (x ∷ Γ) n | no _     = Fin.suc <$> lookupName Γ n
lookupName (n ∷ Γ) n | yes refl = pure zero

mutual
  resolveNames : ∀ {n} → Scope n → Form → Maybe (Expr n)
  resolveNames Γ (var n) = var <$> lookupName Γ n
  resolveNames Γ (con c) = con <$> resolveNamesᶜ Γ c

  resolveNamesᶜ : ∀ {c n} → Scope n → Conₙ c → Maybe (Con n c)
  resolveNamesᶜ Γ (sg x c)     = sg x <$> resolveNamesᶜ Γ c
  resolveNamesᶜ Γ (node ns es) = node <$> sequenceAll Data.Maybe.monad (resolveNamesˡ Γ ns es)

  resolveNamesˡ : ∀ {n n′ sh} → Scope n → Vec Name n′ → All (const Form) sh → All (λ bs → Maybe (Expr (visibleCount bs + n))) sh
  resolveNamesˡ               Γ ns []       = []
  resolveNamesˡ {sh = bs ∷ _} Γ ns (e ∷ es) = resolveNames (bind Γ ns bs) e ∷ resolveNamesˡ Γ ns es
