{-# OPTIONS --rewriting #-}

module MetaTypes where

open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; sym)
open import Agda.Builtin.Equality
open import Agda.Builtin.Equality.Rewrite
open import Relation.Nullary using (¬_; ¬?; Dec; yes; no)

open import EnvClassifiers
open import BaseTypes
open import ObjectTypes

infixr 6 _⇒_

{-   Γ ⊢ A   -}
data MType : ECCtx → Set where

{-
--------------- (wf-dyn)
  Γ ⊢ ?
-}
  ⋆ : ∀ {Δ} → MType Δ

{-
--------------- (wf-base)
  Γ ⊢ ι
-}
  `_ : ∀ {Δ} → Base → MType Δ

{-
  Γ ⊢ A  Γ ⊢ B
--------------- (wf-fun)
  Γ ⊢ A → B
-}
  _⇒_ : ∀ {Δ} → MType Δ → MType Δ → MType Δ

{-
  Γ ⊢ A
--------------- (wf-ref)
  Γ ⊢ Ref A
-}
  Ref_ : ∀ {Δ} → MType Δ → MType Δ

{-
  Γ ⊢ ê
--------------- (wf-code)
  Γ ⊢ ≺O≻ê
-}
  ‶_″_ : ∀ {Δ} → OType⋆ → EC⋆ Δ → MType Δ

{-
    Γ, α ⊢ A
--------------- (wf-forall)
  Γ ⊢ ∀ α. A
-}
  ∀̇_ : ∀ {Δ} → MType (Δ ,α) → MType Δ

{-
    Γ ⊢ e₁  Γ ⊢ e₂
       Γ ⊢ A
--------------------- (wf-constraint)
    Γ ⊢ e₁ <: e₂ => A
-}
  _<:_=>_ : ∀ {Δ} → EC Δ → EC Δ → MType Δ → MType Δ


-- | EC variable renaming in meta types
renᵉ : ∀ {Δ₁ Δ₂} → Δ₁ ⇒ᵉ Δ₂ → MType Δ₁ → MType Δ₂
renᵉ ρ ⋆ = ⋆
renᵉ ρ (` ι) = ` ι
renᵉ ρ (A ⇒ B) = renᵉ ρ A ⇒ renᵉ ρ B
renᵉ ρ (Ref A) = Ref (renᵉ ρ A)
renᵉ ρ (‶ O ″ ê) = ‶ O ″ renᵉ-ec⋆ ρ ê
renᵉ ρ (∀̇ A) = ∀̇ (renᵉ (extᵉ ρ) A)
renᵉ ρ (e₁ <: e₂ => A) = renᵉ-ec ρ e₁ <: renᵉ-ec ρ e₂ => renᵉ ρ A

renᵉ-id : ∀ {Δ} {A : MType Δ} → renᵉ idᵉ A ≡ A
renᵉ-id {Δ} {⋆} = refl
renᵉ-id {Δ} {` _} = refl
renᵉ-id {Δ} {A ⇒ B} rewrite renᵉ-id {Δ} {A} | renᵉ-id {Δ} {B} = refl
renᵉ-id {Δ} {Ref A} rewrite renᵉ-id {Δ} {A} = refl
renᵉ-id {Δ} {‶ O ″ ê} = refl
renᵉ-id {Δ} {∀̇ A} rewrite renᵉ-id {Δ ,α} {A} = refl
renᵉ-id {Δ} {e₁ <: e₂ => A} rewrite renᵉ-id {Δ} {A} = refl
{-# REWRITE renᵉ-id #-}

⇑ᵉ : ∀ {Δ} → MType Δ → MType (Δ ,α)
⇑ᵉ A = renᵉ S_ A


-- | EC variable substitution in meta types
subᵉ : ∀ {Δ₁ Δ₂} → (Δ₁ →ᵉ Δ₂) → MType Δ₁ → MType Δ₂
subᵉ σ ⋆ = ⋆
subᵉ σ (` ι) = ` ι
subᵉ σ (A ⇒ B) = subᵉ σ A ⇒ subᵉ σ B
subᵉ σ (Ref A) = Ref (subᵉ σ A)
subᵉ σ (‶ O ″ ê) = ‶ O ″ subᵉ-ec⋆ σ ê
subᵉ σ (∀̇ A) = ∀̇ subᵉ (extsᵉ σ) A
subᵉ σ (e₁ <: e₂ => A) = subᵉ-ec σ e₁ <: subᵉ-ec σ e₂ => subᵉ σ A

infix 6 _[_]ᵉ
_[_]ᵉ : ∀ {Δ} → MType (Δ ,α) → EC Δ → MType Δ
A [ e ]ᵉ = subᵉ (e •ᵉₛ idsᵉ) A


-- | Type matching for subtyping constrained type
data _⦊_<:_=>_ : ∀ {Δ} → MType Δ → (e₁ e₂ : EC Δ) → MType Δ → Set where

  ⦊-sub : ∀ {Δ e₁ e₂} {A : MType Δ}
    → (e₁ <: e₂ => A) ⦊ e₁ <: e₂ => A


data Ground : ∀ {Δ} → MType Δ → Set where

  gbase : ∀ {Δ ι} → Ground {Δ} (` ι)

  gfun : ∀ {Δ} → Ground {Δ} (⋆ ⇒ ⋆)

  gref : ∀ {Δ} → Ground {Δ} (Ref ⋆)

  gcode : ∀ {Δ} → Ground {Δ} (‶ ⋆ ″ ⋆)

  gforall : ∀ {Δ} → Ground {Δ} (∀̇ ⋆)

  gsub : ∀ {Δ e₁ e₂} → Ground {Δ} (e₁ <: e₂ => ⋆)


-- | Metalanguage typing context (Γᵐ)
infixl 5 _⸴_

data MCtx : ECCtx → Set where

  ∅ : ∀ {Δ} → MCtx Δ

  _⸴_ : ∀ {Δ} → MCtx Δ → MType Δ → MCtx Δ

infix 4 _∋ᵐ_

data _∋ᵐ_ : ∀ {Δ} → MCtx Δ → MType Δ → Set where

  Z : ∀ {Δ} {Γᵐ : MCtx Δ} {A} → Γᵐ ⸴ A ∋ᵐ A

  S_ : ∀ {Δ} {Γᵐ : MCtx Δ} {A B} → Γᵐ ∋ᵐ A → Γᵐ ⸴ B ∋ᵐ A


renᵉ-mctx : ∀ {Δ₁ Δ₂} → Δ₁ ⇒ᵉ Δ₂ → MCtx Δ₁ → MCtx Δ₂
renᵉ-mctx ρ ∅ = ∅
renᵉ-mctx ρ (Γᵐ ⸴ A) = (renᵉ-mctx ρ Γᵐ) ⸴ (renᵉ ρ A)

⇑ᵉ-mctx : ∀ {Δ} → MCtx Δ → MCtx (Δ ,α)
⇑ᵉ-mctx Γᵐ = renᵉ-mctx S_ Γᵐ

subᵉ-mctx : ∀ {Δ₁ Δ₂} → (Δ₁ →ᵉ Δ₂) → MCtx Δ₁ → MCtx Δ₂
subᵉ-mctx σ ∅ = ∅
subᵉ-mctx σ (Γᵐ ⸴ A) = (subᵉ-mctx σ Γᵐ) ⸴ (subᵉ σ A)

_≡?_ : ∀{Δ} → (A B : MType Δ) → Dec (A ≡ B)
⋆ ≡? ⋆ = yes refl
⋆ ≡? (` x) = no λ ()
⋆ ≡? (B ⇒ B₁) = no λ ()
⋆ ≡? (Ref B) = no λ ()
⋆ ≡? (‶ x ″ x₁) = no λ ()
⋆ ≡? (∀̇ B) = no λ ()
⋆ ≡? (x <: x₁ => B) = no λ ()
(` ι) ≡? ⋆ = no λ ()
(` ι) ≡? (` x)
    with base-eq? ι x
... | yes refl = yes refl
... | no neq = no λ {refl → neq refl}
(` ι) ≡? (B ⇒ B₁) = no λ ()
(` ι) ≡? (Ref B) = no λ ()
(` ι) ≡? (‶ x ″ x₁) = no λ ()
(` ι) ≡? (∀̇ B) = no λ ()
(` ι) ≡? (x <: x₁ => B) = no λ ()
(A ⇒ B) ≡? ⋆ = no λ ()
(A ⇒ B) ≡? (` x) = no λ ()
(A ⇒ B) ≡? (C ⇒ D)
    with A ≡? C | B ≡? D
... | yes refl | yes refl = yes refl
... | yes refl | no neq = no λ {refl → neq refl}
... | no neq | _ = no λ {refl → neq refl}
(A ⇒ B) ≡? (Ref C) = no λ ()
(A ⇒ B) ≡? (‶ x ″ x₁) = no λ ()
(A ⇒ B) ≡? (∀̇ C) = no λ ()
(A ⇒ B) ≡? (x <: x₁ => C) = no λ ()
(Ref A) ≡? ⋆ = no λ ()
(Ref A) ≡? (` x) = no λ ()
(Ref A) ≡? (B ⇒ B₁) = no λ ()
(Ref A) ≡? (Ref B)
    with A ≡? B
... | yes refl = yes refl
... | no neq = no λ {refl → neq refl}
(Ref A) ≡? (‶ x ″ x₁) = no λ ()
(Ref A) ≡? (∀̇ B) = no λ ()
(Ref A) ≡? (x <: x₁ => B) = no λ ()
(‶ C ″ e) ≡? ⋆ = no λ ()
(‶ C ″ e) ≡? (` x) = no λ ()
(‶ C ″ e) ≡? (B ⇒ B₁) = no λ ()
(‶ C ″ e) ≡? (Ref B) = no λ ()
(‶ C ″ e) ≡? (‶ D ″ e2)
    with C ≡?ᵒ D
... | yes refl
    with e ≡?ᵉ⋆ e2
... | yes refl = yes refl
... | no neq = no λ { refl → neq refl }
(‶ C ″ e) ≡? (‶ D ″ e2) | no neq = no λ {refl → neq refl}
(‶ C ″ e) ≡? (∀̇ B) = no λ ()
(‶ C ″ e) ≡? (x <: x₁ => B) = no λ ()
(∀̇ A) ≡? ⋆ = no λ ()
(∀̇ A) ≡? (` x) = no λ ()
(∀̇ A) ≡? (B ⇒ B₁) = no λ ()
(∀̇ A) ≡? (Ref B) = no λ ()
(∀̇ A) ≡? (‶ x ″ x₁) = no λ ()
(∀̇ A) ≡? (∀̇ B)
    with A ≡? B
... | yes refl = yes refl
... | no neq = no λ {refl → neq refl}
(∀̇ A) ≡? (x <: x₁ => B) = no λ ()
(e <: e′ => A) ≡? ⋆ = no λ ()
(e <: e′ => A) ≡? (` x) = no λ ()
(e <: e′ => A) ≡? (B ⇒ B₁) = no λ ()
(e <: e′ => A) ≡? (Ref B) = no λ ()
(e <: e′ => A) ≡? (‶ x ″ x₁) = no λ ()
(e <: e′ => A) ≡? (∀̇ B) = no λ ()
(e1 <: e1′ => A) ≡? (e2 <: e2′ => B)
    with A ≡? B | e1 ≡?ᵉ e2 | e1′ ≡?ᵉ e2′
... | yes refl | yes refl | yes refl = yes refl
... | yes refl | yes refl | no neq = no λ {refl → neq refl}
... | yes refl | no neq | _ = no λ {refl → neq refl}
... | no neq | _ | _ = no λ {refl → neq refl}

