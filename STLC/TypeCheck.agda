module STLC.TypeCheck where

open import Function
open import Data.Product
open import Relation.Binary
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary
open import Data.List.All using (_∷_; [])
open import Data.Fin using (Fin; zero; suc)
open import Data.Nat

open import STLC
open import SimplyTyped.Untyped STLC
open import SimplyTyped.EraseType STLC

▷-injₗ : ∀ {t t′ u u′} → (t ▷ t′) ≡ (u ▷ u′) → t ≡ u
▷-injₗ refl = refl

▷-injᵣ : ∀ {t t′ u u′} → (t ▷ t′) ≡ (u ▷ u′) → t′ ≡ u′
▷-injᵣ refl = refl

_≟ₜ_ : Decidable (_≡_ {A = Ty})
∙        ≟ₜ ∙          = yes refl
∙        ≟ₜ (_ ▷ _)    = no (λ ())
∙        ≟ₜ Bool       = no (λ ())
(_ ▷ _)  ≟ₜ ∙          = no (λ ())
(t ▷ t′) ≟ₜ (u ▷ u′)   with t ≟ₜ u | t′ ≟ₜ u′
(t ▷ t′) ≟ₜ (.t ▷ .t′) | yes refl | yes refl = yes refl
(t ▷ t′) ≟ₜ (u ▷ u′)   | _ | no ¬p = no (¬p ∘ ▷-injᵣ)
(t ▷ t′) ≟ₜ (u ▷ u′)   | no ¬p | _ = no (¬p ∘ ▷-injₗ)
(_ ▷ _)  ≟ₜ Bool       = no (λ ())
Bool     ≟ₜ ∙          = no (λ ())
Bool     ≟ₜ (u ▷ u₁)   = no (λ ())
Bool     ≟ₜ Bool       = yes refl

lookup : ∀ Γ → Fin (size Γ) → ∃ λ t → Var t Γ
lookup ∅ ()
lookup (Γ , _) zero    = , vz
lookup (Γ , _) (suc v) = Data.Product.map _ vs (lookup Γ v)

lookup-correct : ∀ Γ v₀ → let (t , v) = lookup Γ v₀ in untypeᵛ v ≡ v₀
lookup-correct ∅       ()
lookup-correct (Γ , t) zero     = refl
lookup-correct (Γ , t) (suc v₀) rewrite lookup-correct Γ v₀ = refl

module _ where
  -- [lam]₀ : ∀ {n} → Ty → Expr (1 + n) → Expr n
  pattern [lam]₀ t e = con (sg `lam (sg t (node (e ∷ []))))

  -- _[·]₀_ : ∀ {n} → Expr n → Expr n → Expr n
  pattern _[·]₀_ f e = con (sg `app (node (f ∷ e ∷ [])))

  -- [true]₀ [false]₀ : ∀ {n} → Expr n
  pattern [true]₀ = con (sg `true (node []))
  pattern [false]₀ = con (sg `false (node []))

  -- [if]₀_[then]_[else]_ : ∀ {n} → Expr n → Expr n → Expr n → Expr n
  pattern [if]₀_[then]_[else]_ b thn els = con (sg `if (node (b ∷ thn ∷ els ∷ [])))

open import Data.Maybe
open import Level renaming (zero to lzero)
open import Category.Monad
open RawMonad (Data.Maybe.monad {lzero})

typecheck : ∀ Γ → (e : Expr (size Γ)) → Maybe (∃ λ t → Σ (Tm Γ t) λ e′ → untype e′ ≡ e)
typecheck Γ (var v) = do
  let (t , v′) = lookup Γ v
  pure (t , var v′ , cong var (lookup-correct Γ v))
typecheck Γ ([lam]₀ t e) = do
  (_ , e′ , refl) ← typecheck (Γ , t) e
  pure (, [lam] t e′ , refl)
typecheck Γ (f [·]₀ e) = do
  (u , e′ , refl) ← typecheck Γ e
  (u′ ▷ t , f′ , refl) ← typecheck Γ f
    where _ → nothing
  refl ← decToMaybe (u ≟ₜ u′)
  pure (, f′ [·] e′ , refl)
typecheck Γ [true]₀ = do
  pure (, [true] , refl)
typecheck Γ [false]₀ = do
  pure (, [false] , refl)
typecheck Γ ([if]₀ b [then] thn [else] els) = do
  (t₀ , b′ , refl) ← typecheck Γ b
  refl ← decToMaybe (t₀ ≟ₜ Bool)
  (t , thn′ , refl) ← typecheck Γ thn
  (t′ , els′ , refl) ← typecheck Γ els
  refl ← decToMaybe (t ≟ₜ t′)
  pure (, [if] b′ [then] thn′ [else] els′ , refl)

open import Data.String renaming (_≟_ to _≟ₛ_)

Name : Set
Name = String

open import SimplyTyped.Unscoped STLC Name
open import SimplyTyped.ScopeCheck STLC _≟ₛ_
open import Data.Vec using ([]; _∷_)

module _ where
  -- [lam]ₙ : Name → Ty → Form → Form
  pattern [lam]ₙ v t e = con (sg `lam (sg t (node (v ∷ []) (e ∷ []))))

  -- _[·]ₙ_ : Form → Form → Form
  pattern _[·]ₙ_ f e = con (sg `app (node [] (f ∷ e ∷ [])))

  -- [true]ₙ [false]ₙ : Form
  pattern [true]ₙ = con (sg `true (node [] []))
  pattern [false]ₙ = con (sg `false (node [] []))

  -- [if]ₙ_[then]_[else]_ : Form → Form → Form → Form
  pattern [if]ₙ_[then]_[else]_ b thn els = con (sg `if (node [] (b ∷ thn ∷ els ∷ [])))

scopeAndType : Form → Maybe (∃ (Tm ∅))
scopeAndType e = do
  e′ ← resolveNames [] e
  (t , e″ , refl) ← typecheck ∅ e′
  pure (t , e″)

ex₁ : Tm ∅ (∙ ▷ ∙)
ex₁ = proj₂ (from-just (scopeAndType ([lam]ₙ "x" ∙ (var "x"))))
