{-# OPTIONS --rewriting #-}
module Hypercoercions where

  open import EnvClassifiers
  open import BlameLabels public
  open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; subst)
  open import Relation.Nullary using (¬_; Dec; yes; no)
  open import Data.Empty using (⊥; ⊥-elim)
  open import Data.Product using (Σ-syntax; ∃-syntax; _×_) renaming (_,_ to ⟨_,_⟩)
  open import ECSubtypeDecidable using (ec-<:⋆?)

  -- | Coercions between ECs (cᵉ, dᵉ)
  module ECHypercoercions where

    infix 6 _;_⊢ᵉ_⇒_
    infix 6 _⊢ᵉʰ_⇒_
    infix 6 _;_⊢ᵉᵐ_⇒_
    infix 6 _⊢ᵉᵗ_⇒_
    infix 6 _⊢_⨟ᵉᵗʰ_
    infix 6 _⨟ᵉᵐ_
    infix 6 _⊢_⨟ᵉ_
    infixr 8 _⨾_⨾_

    data _⊢ᵉʰ_⇒_ : ∀ Δ → EC⋆ Δ → EC⋆ Δ → Set where
    
      _？_ : ∀ {Δ}
        → (e : EC Δ)
        → BlameLabel
          --------------------------- ec-hc-head-proj
        → Δ ⊢ᵉʰ ⋆ ⇒ ec e

      id : ∀ {Δ}
        → (e : EC⋆ Δ)
          --------------------------- ec-hc-head-id
        → Δ ⊢ᵉʰ e ⇒ e

    data _⊢ᵉᵗ_⇒_ : ∀ Δ → EC⋆ Δ → EC⋆ Δ → Set where

      _！ : ∀ {Δ}
        → (e : EC Δ)
          --------------------------- ec-hc-tail-inj
        → Δ ⊢ᵉᵗ ec e ⇒ ⋆

      id : ∀ {Δ}
        → (e : EC⋆ Δ)
          --------------------------- ec-hc-tail-id
        → Δ ⊢ᵉᵗ e ⇒ e

    data _;_⊢ᵉᵐ_⇒_ : ∀ Δ (Θ : SubCtx Δ) → EC⋆ Δ → EC⋆ Δ → Set  where

      ↑ : ∀ {Δ Θ} {ê₁ ê₂ : EC⋆ Δ}
        → Δ ; Θ ⊢ᵉ ê₁ <:⋆ ê₂
          --------------------------- ec-hc-mid-sub
        → Δ ; Θ ⊢ᵉᵐ ê₁ ⇒ ê₂

      err : ∀ {Δ Θ}
        → (ê₁ : EC⋆ Δ)
        → (ê₂ : EC⋆ Δ)
        → BlameLabel
          --------------------------- ec-hc-mid-bot
        → Δ ; Θ ⊢ᵉᵐ ê₁ ⇒ ê₂

    data _;_⊢ᵉ_⇒_ : ∀ Δ (Θ : SubCtx Δ) → EC⋆ Δ → EC⋆ Δ → Set  where

      _⨾_⨾_ : ∀ {Δ Θ} {ê₁ ê₂ ê₃ ê₄ : EC⋆ Δ}
        → (head : Δ ⊢ᵉʰ ê₁ ⇒ ê₂)
        → (middle : Δ ; Θ ⊢ᵉᵐ ê₂ ⇒ ê₃)
        → (tail : Δ ⊢ᵉᵗ ê₃ ⇒ ê₄)
          --------------------------- ec-hc
        → Δ ; Θ ⊢ᵉ ê₁ ⇒ ê₄

    data ECHeadMiddleTail {Δ} (Θ : SubCtx Δ) (ê₁ ê₂ : EC⋆ Δ) : Set where
      head : Δ ⊢ᵉʰ ê₁ ⇒ ê₂ → ECHeadMiddleTail Θ ê₁ ê₂
      middle : Δ ; Θ ⊢ᵉᵐ ê₁ ⇒ ê₂ → ECHeadMiddleTail Θ ê₁ ê₂
      tail : Δ ⊢ᵉᵗ ê₁ ⇒ ê₂ → ECHeadMiddleTail Θ ê₁ ê₂

    _⊢_⨟ᵉᵗʰ_ : ∀ {Δ ê₁ ê₂ ê₃}
      → (Θ : SubCtx Δ)
      → Δ ⊢ᵉᵗ ê₁ ⇒ ê₂
      → Δ ⊢ᵉʰ ê₂ ⇒ ê₃
      → ECHeadMiddleTail Θ ê₁ ê₃
    Θ ⊢ e₁ ！ ⨟ᵉᵗʰ (e₂ ？ ℓ) with ec-<:⋆? Θ (ec e₁) (ec e₂)
    ... | yes e₁<:⋆e₂ = middle (↑ e₁<:⋆e₂)
    ... | no  _       = middle (err (ec e₁) (ec e₂) ℓ)
    Θ ⊢ e ！ ⨟ᵉᵗʰ id ⋆ = tail (e ！)
    Θ ⊢ id ê₁ ⨟ᵉᵗʰ h = head h

    ⨟ᵉᵗʰ-tail-id⋆ : ∀ {Δ Θ ê₂ e} {t₁ : Δ ⊢ᵉᵗ ec e ⇒ ê₂} {h₂ : Δ ⊢ᵉʰ ê₂ ⇒ ⋆}
      → Θ ⊢ t₁ ⨟ᵉᵗʰ h₂ ≡ tail (e ！)
      → Σ[ ê₂≡⋆ ∈ ê₂ ≡ ⋆ ] subst (λ ê₂′ → Δ ⊢ᵉʰ ê₂′ ⇒ ⋆) ê₂≡⋆ h₂ ≡ id ⋆
    ⨟ᵉᵗʰ-tail-id⋆ {t₁ = e ！} {h₂ = id ⋆} refl = ⟨ refl , refl ⟩

    ⨟ᵉᵗʰ-tail-id-impossible : ∀ {Δ Θ e e'} {t₁ : Δ ⊢ᵉᵗ e ⇒ e'} {h₂ : Δ ⊢ᵉʰ e' ⇒ e}
      → ¬ (Θ ⊢ t₁ ⨟ᵉᵗʰ h₂ ≡ tail (id e))
    ⨟ᵉᵗʰ-tail-id-impossible {t₁ = id e} {h₂ = h₂} ()
    ⨟ᵉᵗʰ-tail-id-impossible{Δ}{Θ} {t₁ = e ！} {h₂ = e₁ ？ ℓ} compose-eq with ec-<:⋆? Θ (ec e) (ec e)
    ⨟ᵉᵗʰ-tail-id-impossible {Δ} {Θ} {_} {_} {_ ！} {_ ？ ℓ} () | yes e<:⋆e
    ... | no e≮:e = ⊥-elim (e≮:e (<:-ec <:-refl))

    _⨟ᵉᵐ_ : ∀ {Δ Θ ê₁ ê₂ ê₃}
      → Δ ; Θ ⊢ᵉᵐ ê₁ ⇒ ê₂ → Δ ; Θ ⊢ᵉᵐ ê₂ ⇒ ê₃ → Δ ; Θ ⊢ᵉᵐ ê₁ ⇒ ê₃
    ↑ ê₁<:⋆ê₂ ⨟ᵉᵐ ↑ ê₂<:⋆ê₃ = ↑ (<:⋆-trans ê₁<:⋆ê₂ ê₂<:⋆ê₃)
    ↑ {ê₁ = ê₁} ê₁<:⋆ê₂ ⨟ᵉᵐ err ê₂ ê₃ ℓ = err ê₁ ê₃ ℓ
    _⨟ᵉᵐ_ {ê₃ = ê₃} (err ê₁ ê₂ ℓ)  m = err ê₁ ê₃ ℓ

    _⊢_⨟ᵉ_ : ∀ {Δ ê₁ ê₂ ê₃}
      → (Θ : SubCtx Δ)
      → Δ ; Θ ⊢ᵉ ê₁ ⇒ ê₂
      → Δ ; Θ ⊢ᵉ ê₂ ⇒ ê₃
      → Δ ; Θ ⊢ᵉ ê₁ ⇒ ê₃
    Θ ⊢ h₁ ⨾ err ê₂ ê₃ ℓ ⨾ t₁ ⨟ᵉ _⨾_⨾_ {ê₃ = ê₇} h₂ m₂ t₂ =
      h₁ ⨾ err ê₂ ê₇ ℓ ⨾ t₂
    Θ ⊢ h₁ ⨾ m₁ ⨾ t₁ ⨟ᵉ h₂ ⨾ err ê₅ ê₆ ℓ ⨾ t₂ with Θ ⊢ t₁ ⨟ᵉᵗʰ h₂
    ... | middle (err ê₃ ê₅ ℓ′) = h₁ ⨾ err _ ê₆ ℓ′ ⨾ t₂
    ... | _ = h₁ ⨾ err _ ê₆ ℓ ⨾ t₂
    Θ ⊢ h₁ ⨾ m₁ ⨾ t₁ ⨟ᵉ h₂ ⨾ m₂ ⨾ t₂ with Θ ⊢ t₁ ⨟ᵉᵗʰ h₂ in eq
    ... | middle (↑ ê₃<:⋆ê₂) = h₁ ⨾ (m₁ ⨟ᵉᵐ (↑ ê₃<:⋆ê₂ ⨟ᵉᵐ m₂)) ⨾ t₂
    ... | head (id _) = h₁ ⨾ (m₁ ⨟ᵉᵐ m₂) ⨾ t₂
    ... | tail (e ！) = h₁ ⨾ m₁ ⨾ {!!}
    ... | tail (id e) = ⊥-elim (⨟ᵉᵗʰ-tail-id-impossible {t₁ = t₁} {h₂ = h₂} eq)
    ... | head (e ？ ℓ) = {!!} ⨾ m₂ ⨾ t₂
    ... | middle (err ê₃ ê₅ ℓ) = h₁ ⨾ err _ _ ℓ ⨾ t₂

  open ECHypercoercions public

  -- | Coercions between gradual code types (cᵒ, dᵒ)
  module ObjectHypercoercions where
    open import ObjectTypes

    infix 6 ⊢ᵒ_⇒_
    infix 6 ⊢ᵒʰ_⇒_
    infix 6 ⊢ᵒᵐ_⇒_
    infix 6 ⊢ᵒᵗ_⇒_
    infix 6 _⨟ᵒᵗʰ_
    infix 6 _⨟ᵒᵐ_
    infix 6 _⨟ᵒ_
    infixr 8 _⨾_⨾_

    data ⊢ᵒʰ_⇒_ : OType⋆ → OType⋆ → Set where

      _？_ : ∀ Gᵒ
        → BlameLabel
        → OGround Gᵒ
          --------------------- code-hc-head-proj
        → ⊢ᵒʰ ⋆ ⇒ Gᵒ

      id : ∀ O → ⊢ᵒʰ O ⇒ O  -- code-hc-head-id

    data ⊢ᵒᵗ_⇒_ : OType⋆ → OType⋆ → Set where

      _！ : ∀ Gᵒ
        → OGround Gᵒ
          --------------------- code-hc-tail-inj
        → ⊢ᵒᵗ Gᵒ ⇒ ⋆

      id : ∀ O → ⊢ᵒᵗ O ⇒ O  -- code-hc-tail-id

    data ⊢ᵒᵐ_⇒_ : OType⋆ → OType⋆ → Set
    data ⊢ᵒ_⇒_ : OType⋆ → OType⋆ → Set

    data ⊢ᵒᵐ_⇒_ where

      _⇒_ : ∀ {O₁ O₂ O₃ O₄}
        → ⊢ᵒ O₃ ⇒ O₁
        → ⊢ᵒ O₂ ⇒ O₄
          --------------------------------- code-hc-mid-fun
        → ⊢ᵒᵐ (O₁ ⇒ O₂) ⇒ (O₃ ⇒ O₄)

      err : ∀ O₁ O₂
        → BlameLabel
          --------------- code-hc-mid-bot
        → ⊢ᵒᵐ O₁ ⇒ O₂

      id⋆ : ⊢ᵒᵐ ⋆ ⇒ ⋆  -- code-hc-mid-id⋆

      idι : ∀ ι → ⊢ᵒᵐ ` ι ⇒ ` ι  -- code-hc-mid-idι

    data ⊢ᵒ_⇒_ where

      _⨾_⨾_ : ∀ {O₁ O₂ O₃ O₄}
        → ⊢ᵒʰ O₁ ⇒ O₂
        → ⊢ᵒᵐ O₂ ⇒ O₃
        → ⊢ᵒᵗ O₃ ⇒ O₄
          --------------------- code-hc
        → ⊢ᵒ O₁ ⇒ O₄

    data OHeadMiddleTail (O₁ O₂ : OType⋆) : Set where
      head : ⊢ᵒʰ O₁ ⇒ O₂ → OHeadMiddleTail O₁ O₂
      middle : ⊢ᵒᵐ O₁ ⇒ O₂ → OHeadMiddleTail O₁ O₂
      tail : ⊢ᵒᵗ O₁ ⇒ O₂ → OHeadMiddleTail O₁ O₂

    _⨟ᵒᵗʰ_ : ∀ {O₁ O₂ O₃}
      → ⊢ᵒᵗ O₁ ⇒ O₂
      → ⊢ᵒʰ O₂ ⇒ O₃
      → OHeadMiddleTail O₁ O₃
    id O₁ ⨟ᵒᵗʰ h = head h
    ((Gᵒ ！) g₁) ⨟ᵒᵗʰ id ⋆ = tail ((Gᵒ ！) g₁)
    ((G₁ ！) g₁) ⨟ᵒᵗʰ ((G₂ ？ ℓ) g₂) with G₁ ≡?ᵒ G₂
    ... | yes refl = head (id G₁)
    ... | no _ = middle (err G₁ G₂ ℓ)

    ⨟ᵒᵗʰ-tail-id-impossible : ∀ {O O'} {t₁ : ⊢ᵒᵗ O ⇒ O'} {h₂ : ⊢ᵒʰ O' ⇒ O}
      → ¬ (t₁ ⨟ᵒᵗʰ h₂ ≡ tail (id O))
    ⨟ᵒᵗʰ-tail-id-impossible {t₁ = id O} {h₂ = h₂} ()
    ⨟ᵒᵗʰ-tail-id-impossible {t₁ = (Gᵒ ！) g} {h₂ = (Gᵒ' ？ ℓ) g'} compose-eq with Gᵒ ≡?ᵒ Gᵒ
    ⨟ᵒᵗʰ-tail-id-impossible {_} {_} {(_ ！) g} {(_ ？ ℓ) g'} () | yes refl
    ... | no Gᵒ≢Gᵒ = ⊥-elim (Gᵒ≢Gᵒ refl)

    ⨟ᵒᵗʰ-middle-err : ∀ {O₁ O₂ O₃} {t₁ : ⊢ᵒᵗ O₁ ⇒ O₂} {h₂ : ⊢ᵒʰ O₂ ⇒ O₃} {m : ⊢ᵒᵐ O₁ ⇒ O₃}
      → t₁ ⨟ᵒᵗʰ h₂ ≡ middle m
      → Σ[ ℓ ∈ BlameLabel ] m ≡ err O₁ O₃ ℓ
    ⨟ᵒᵗʰ-middle-err {t₁ = id O₁} {h₂ = h₂} ()
    ⨟ᵒᵗʰ-middle-err {t₁ = (Gᵒ ！) g} {h₂ = id ⋆} ()
    ⨟ᵒᵗʰ-middle-err {t₁ = (G₁ ！) g₁} {h₂ = (G₂ ？ ℓ) g₂} {m = m} eq with G₁ ≡?ᵒ G₂
    ⨟ᵒᵗʰ-middle-err {O₃ = _} {(_ ！) g₁} {(_ ？ ℓ) g₂} {m = m} () | yes refl
    ⨟ᵒᵗʰ-middle-err {O₃ = _} {(_ ！) g₁} {(_ ？ ℓ) g₂} {m = m} refl | no _ = ⟨ ℓ , refl ⟩

    _⨟ᵒᵐ_ : ∀ {O₁ O₂ O₃}
      → ⊢ᵒᵐ O₁ ⇒ O₂
      → ⊢ᵒᵐ O₂ ⇒ O₃
      → ⊢ᵒᵐ O₁ ⇒ O₃
    _⨟ᵒ_ : ∀ {O₁ O₂ O₃}
      → ⊢ᵒ O₁ ⇒ O₂
      → ⊢ᵒ O₂ ⇒ O₃
      → ⊢ᵒ O₁ ⇒ O₃

    id⋆ ⨟ᵒᵐ m₂ = m₂
    idι ι ⨟ᵒᵐ m₂ = m₂
    m₁ ⨟ᵒᵐ id⋆ = m₁
    m₁ ⨟ᵒᵐ idι ι = m₁
    err O₁ O₂ ℓ ⨟ᵒᵐ m₂ = err O₁ _ ℓ
    m₁ ⨟ᵒᵐ err O₂ O₃ ℓ = err _ O₃ ℓ
    _⨟ᵒᵐ_ {O₁ ⇒ O₂} {O₃ ⇒ O₄} {O₅ ⇒ O₆} (c₁ ⇒ c₂) (c₃ ⇒ c₄)
      with c₃ ⨟ᵒ c₁ | c₂ ⨟ᵒ c₄
    ... | h ⨾ err _ _ ℓ ⨾ t | _ = err (O₁ ⇒ O₂) (O₅ ⇒ O₆) ℓ
    ... | _ | h ⨾ err _ _ ℓ ⨾ t = err (O₁ ⇒ O₂) (O₅ ⇒ O₆) ℓ
    ... | c₁′ | c₂′ = c₁′ ⇒ c₂′

    h₁ ⨾ err O₂ O₃ ℓ ⨾ t₁ ⨟ᵒ h₂ ⨾ m₂ ⨾ t₂ =
      h₁ ⨾ err O₂ _ ℓ ⨾ t₂
    h₁ ⨾ m₁ ⨾ t₁ ⨟ᵒ h₂ ⨾ err O₅ O₆ ℓ ⨾ t₂ with t₁ ⨟ᵒᵗʰ h₂
    ... | middle (err O₃ O₅ ℓ′) = h₁ ⨾ err _ O₆ ℓ′ ⨾ t₂
    ... | _ = h₁ ⨾ err _ O₆ ℓ ⨾ t₂
    h₁ ⨾ m₁ ⨾ t₁ ⨟ᵒ h₂ ⨾ m₂ ⨾ t₂ with t₁ ⨟ᵒᵗʰ h₂ in eq
    ... | head (id _) = h₁ ⨾ (m₁ ⨟ᵒᵐ m₂) ⨾ t₂
    ... | tail ((Gᵒ ！) x) = h₁ ⨾ m₁ ⨾ {!!}
    ... | tail (id O) = ⊥-elim (⨟ᵒᵗʰ-tail-id-impossible {t₁ = t₁} {h₂ = h₂} eq)
    ... | head (h₃@((_ ？ _) _)) = {!!} ⨾ m₂ ⨾ t₂
    ... | middle (err O₃ O₅ ℓ) = h₁ ⨾ err _ _ ℓ ⨾ t₂
    ... | middle (O ⇒ O') with ⨟ᵒᵗʰ-middle-err {t₁ = t₁} {h₂ = h₂} {m = O ⇒ O'} eq
    ...   | ⟨ ℓ , () ⟩
    h₁ ⨾ m₁ ⨾ t₁ ⨟ᵒ h₂ ⨾ m₂ ⨾ t₂ | middle id⋆ with ⨟ᵒᵗʰ-middle-err {t₁ = t₁} {h₂ = h₂} {m = id⋆} eq
    ...   | ⟨ ℓ , () ⟩
    h₁ ⨾ m₁ ⨾ t₁ ⨟ᵒ h₂ ⨾ m₂ ⨾ t₂ | middle (idι ι) with ⨟ᵒᵗʰ-middle-err {t₁ = t₁} {h₂ = h₂} {m = idι ι} eq
    ...   | ⟨ ℓ , () ⟩

  open ObjectHypercoercions public

  -- | Coercions between metalanguage types (c, d)
  module MetaCoercions where
    open import MetaTypes

    infix 6 _;_⊢ᵐ_⇒_
    infix 6 _⊢ᵐʰ_⇒_
    infix 6 _;_⊢ᵐᵐ_⇒_
    infix 6 _⊢ᵐᵗ_⇒_
    infix 6 _⊢_⨟ᵐᵗʰ_
    infix 6 _⊢_⨟ᵐᵐ_
    infix 6 _⊢_⨟ᵐ_
    infixr 8 _⨾_⨾_

    data _⊢ᵐʰ_⇒_ : ∀ Δ → MType Δ → MType Δ → Set where

      _？_ : ∀ {Δ}
        → (G : MType Δ)
        → BlameLabel
        → Ground G
          ------------------------ meta-hc-head-proj
        → Δ ⊢ᵐʰ ⋆ ⇒ G

      id : ∀ {Δ}
        → (A : MType Δ)
          ------------------------ meta-hc-head-id
        → Δ ⊢ᵐʰ A ⇒ A

    data _⊢ᵐᵗ_⇒_ : ∀ Δ → MType Δ → MType Δ → Set where

      _！ : ∀ {Δ}
        → (G : MType Δ)
        → Ground G
          ------------------------ meta-hc-tail-inj
        → Δ ⊢ᵐᵗ G ⇒ ⋆

      id : ∀ {Δ}
        → (A : MType Δ)
          ------------------------ meta-hc-tail-id
        → Δ ⊢ᵐᵗ A ⇒ A

    data _;_⊢ᵐᵐ_⇒_ : ∀ Δ (Θ : SubCtx Δ) → MType Δ → MType Δ → Set
    data _;_⊢ᵐ_⇒_ : ∀ Δ (Θ : SubCtx Δ) → MType Δ → MType Δ → Set

    data _;_⊢ᵐᵐ_⇒_ where

      _⇒_ : ∀ {Δ Θ} {A B C D}
        → Δ ; Θ ⊢ᵐ C ⇒ A
        → Δ ; Θ ⊢ᵐ B ⇒ D
          --------------------------------- meta-hc-mid-fun
        → Δ ; Θ ⊢ᵐᵐ (A ⇒ B) ⇒ (C ⇒ D)

      ‶_″_ : ∀ {Δ Θ} {O₁ O₂ ê₁ ê₂}
        →       ⊢ᵒ O₁ ⇒ O₂
        → Δ ; Θ ⊢ᵉ ê₁ ⇒ ê₂
          --------------------------------------------- meta-hc-mid-code
        → Δ ; Θ ⊢ᵐᵐ (‶ O₁ ″ ê₁) ⇒ (‶ O₂ ″ ê₂)

      ref : ∀ {Δ Θ} {A B}
        → Δ ; Θ ⊢ᵐ B ⇒ A
        → Δ ; Θ ⊢ᵐ A ⇒ B
          ------------------------------ meta-hc-mid-ref
        → Δ ; Θ ⊢ᵐᵐ Ref A ⇒ Ref B

      ∀̇_ : ∀ {Δ Θ} {A B}
        → (Δ ,α) ; ⇑ᵉ-subctx Θ ⊢ᵐ A ⇒ B
          ------------------------------------------ meta-hc-mid-univ
        → Δ ; Θ ⊢ᵐᵐ ∀̇ A ⇒ ∀̇ B

      _<:_=>_ : ∀ {Δ Θ} {A B}
        → (e₁ e₂ : EC Δ)
        → Δ ; Θ , e₁ <: e₂ ⊢ᵐ A ⇒ B
          ------------------------------------------------ meta-hc-mid-sub
        → Δ ; Θ ⊢ᵐᵐ (e₁ <: e₂ => A) ⇒ (e₁ <: e₂ => B)

      id⋆ : ∀ {Δ Θ}
          ------------------------ meta-hc-mid-id⋆
        → Δ ; Θ ⊢ᵐᵐ ⋆ ⇒ ⋆

      idι : ∀ {Δ Θ} ι
          ------------------------ meta-hc-mid-idι
        → Δ ; Θ ⊢ᵐᵐ ` ι ⇒ ` ι

      err : ∀ {Δ Θ}
        → (A : MType Δ)
        → (B : MType Δ)
        → BlameLabel
          ------------------------ meta-hc-mid-bot
        → Δ ; Θ ⊢ᵐᵐ A ⇒ B

    data _;_⊢ᵐ_⇒_ where

      _⨾_⨾_ : ∀ {Δ Θ} {A B B′ C}
        → Δ ⊢ᵐʰ A ⇒ B
        → Δ ; Θ ⊢ᵐ B ⇒ B′
        → Δ ⊢ᵐᵗ B′ ⇒ C
          ------------------------ meta-hc
        → Δ ; Θ ⊢ᵐ A ⇒ C

    -- data MHeadMiddleTail {Δ} (Θ : SubCtx Δ) (A B : MType Δ) : Set where
    --   head : Δ ⊢ᵐʰ A ⇒ B → MHeadMiddleTail Θ A B
    --   middle : Δ ; Θ ⊢ᵐᵐ A ⇒ B → MHeadMiddleTail Θ A B
    --   tail : Δ ⊢ᵐᵗ A ⇒ B → MHeadMiddleTail Θ A B

    -- _⊢_⨟ᵐᵗʰ_ : ∀ {Δ A B C}
    --   → (Θ : SubCtx Δ)
    --   → Δ ⊢ᵐᵗ A ⇒ B
    --   → Δ ⊢ᵐʰ B ⇒ C
    --   → MHeadMiddleTail Θ A C
    -- Θ ⊢ id A ⨟ᵐᵗʰ h = head h
    -- Θ ⊢ ((G ！) g) ⨟ᵐᵗʰ id ⋆ = tail ((G ！) g)
    -- Θ ⊢ ((G₁ ！) g₁) ⨟ᵐᵗʰ ((G₂ ？ ℓ) g₂) with G₁ ≡? G₂
    -- ... | yes refl = head (id G₁)
    -- ... | no _ = middle (err G₁ G₂ ℓ)

    -- ⨟ᵐᵗʰ-tail-id-impossible : ∀ {Δ Θ A A′} {t₁ : Δ ⊢ᵐᵗ A ⇒ A′} {h₂ : Δ ⊢ᵐʰ A′ ⇒ A}
    --   → ¬ (Θ ⊢ t₁ ⨟ᵐᵗʰ h₂ ≡ tail (id A))
    -- ⨟ᵐᵗʰ-tail-id-impossible {t₁ = id A} {h₂ = h₂} ()
    -- ⨟ᵐᵗʰ-tail-id-impossible {Δ} {Θ} {t₁ = (G ！) g} {h₂ = (H ？ ℓ) h} eq with G ≡? H
    -- ... | yes refl = λ ()
    -- ... | no G≢H = λ ()

    -- ⨟ᵐᵗʰ-middle-err : ∀ {Δ Θ A B C} {t₁ : Δ ⊢ᵐᵗ A ⇒ B} {h₂ : Δ ⊢ᵐʰ B ⇒ C} {m : Δ ; Θ ⊢ᵐᵐ A ⇒ C}
    --   → Θ ⊢ t₁ ⨟ᵐᵗʰ h₂ ≡ middle m
    --   → Σ[ ℓ ∈ BlameLabel ] m ≡ err A C ℓ
    -- ⨟ᵐᵗʰ-middle-err {t₁ = id A} {h₂ = h₂} ()
    -- ⨟ᵐᵗʰ-middle-err {t₁ = (G ！) g} {h₂ = id ⋆} ()
    -- ⨟ᵐᵗʰ-middle-err {t₁ = (G₁ ！) g₁} {h₂ = (G₂ ？ ℓ) g₂} {m = m} eq with G₁ ≡? G₂
    -- ... | yes refl = λ ()
    -- ... | no _ = ⟨ ℓ , refl ⟩

    -- _⊢_⨟ᵐᵐ_ : ∀ {Δ A B C}
    --   → (Θ : SubCtx Δ)
    --   → Δ ; Θ ⊢ᵐᵐ A ⇒ B
    --   → Δ ; Θ ⊢ᵐᵐ B ⇒ C
    --   → Δ ; Θ ⊢ᵐᵐ A ⇒ C
    -- Θ ⊢ id⋆ ⨟ᵐᵐ m₂ = m₂
    -- Θ ⊢ idι ι ⨟ᵐᵐ m₂ = m₂
    -- Θ ⊢ m₁ ⨟ᵐᵐ id⋆ = m₁
    -- Θ ⊢ m₁ ⨟ᵐᵐ idι ι = m₁
    -- Θ ⊢ err A B ℓ ⨟ᵐᵐ m₂ = err A _ ℓ
    -- Θ ⊢ m₁ ⨟ᵐᵐ err B C ℓ = err _ C ℓ
    -- Θ ⊢ (c₁ ⇒ c₂) ⨟ᵐᵐ (c₃ ⇒ c₄) = (Θ ⊢ c₃ ⨟ᵐ c₁) ⇒ (Θ ⊢ c₂ ⨟ᵐ c₄)
    -- Θ ⊢ (‶ cᵒ₁ ″ cᵉ₁) ⨟ᵐᵐ (‶ cᵒ₂ ″ cᵉ₂) with cᵒ₁ ⨟ᵒ cᵒ₂ | Θ ⊢ cᵉ₁ ⨟ cᵉ₂
    -- ... | hᵒ ⨾ err _ _ ℓ ⨾ tᵒ | _ = err (‶ _ ″ _) (‶ _ ″ _) ℓ
    -- ... | _ | hᵉ ⨾ err _ _ ℓ ⨾ tᵉ = err (‶ _ ″ _) (‶ _ ″ _) ℓ
    -- ... | cᵒ | cᵉ = ‶ cᵒ ″ cᵉ
    -- Θ ⊢ ref c₁ c₂ ⨟ᵐᵐ ref c₃ c₄ = ref (Θ ⊢ c₃ ⨟ᵐ c₁) (Θ ⊢ c₂ ⨟ᵐ c₄)
    -- Θ ⊢ ∀̇ c₁ ⨟ᵐᵐ ∀̇ c₂ = ∀̇ (⇑ᵉ-subctx Θ ⊢ c₁ ⨟ᵐ c₂)
    -- Θ ⊢ (e₁ <: e₂ => c₁) ⨟ᵐᵐ (.e₁ <: .e₂ => c₂) = e₁ <: e₂ => (Θ , e₁ <: e₂ ⊢ c₁ ⨟ᵐ c₂)

    -- _⊢_⨟ᵐ_ : ∀ {Δ A B C}
    --   → (Θ : SubCtx Δ)
    --   → Δ ; Θ ⊢ᵐ A ⇒ B
    --   → Δ ; Θ ⊢ᵐ B ⇒ C
    --   → Δ ; Θ ⊢ᵐ A ⇒ C
    -- Θ ⊢ h₁ ⨾ err A B ℓ ⨾ t₁ ⨟ᵐ h₂ ⨾ m₂ ⨾ t₂ =
    --   h₁ ⨾ err A _ ℓ ⨾ t₂
    -- Θ ⊢ h₁ ⨾ m₁ ⨾ t₁ ⨟ᵐ h₂ ⨾ err B C ℓ ⨾ t₂ with Θ ⊢ t₁ ⨟ᵐᵗʰ h₂
    -- ... | middle (err A′ B′ ℓ′) = h₁ ⨾ err _ C ℓ′ ⨾ t₂
    -- ... | _ = h₁ ⨾ err _ C ℓ ⨾ t₂
    -- Θ ⊢ h₁ ⨾ m₁ ⨾ t₁ ⨟ᵐ h₂ ⨾ m₂ ⨾ t₂ with Θ ⊢ t₁ ⨟ᵐᵗʰ h₂ in eq
    -- ... | head (id _) = h₁ ⨾ (Θ ⊢ m₁ ⨟ᵐᵐ m₂) ⨾ t₂
    -- ... | tail ((G ！) g) = h₁ ⨾ m₁ ⨾ ((G ！) g)
    -- ... | tail (id A) = ⊥-elim (⨟ᵐᵗʰ-tail-id-impossible {t₁ = t₁} {h₂ = h₂} eq)
    -- ... | head (h₃@((_ ？ _) _)) = h₃ ⨾ m₂ ⨾ t₂
    -- ... | middle (c₁ ⇒ c₂) with ⨟ᵐᵗʰ-middle-err {t₁ = t₁} {h₂ = h₂} {m = c₁ ⇒ c₂} eq
    -- ...   | ⟨ ℓ , () ⟩
    -- ... | middle (‶ cᵒ ″ cᵉ) with ⨟ᵐᵗʰ-middle-err {t₁ = t₁} {h₂ = h₂} {m = ‶ cᵒ ″ cᵉ} eq
    -- ...   | ⟨ ℓ , () ⟩
    -- ... | middle (ref c₁ c₂) with ⨟ᵐᵗʰ-middle-err {t₁ = t₁} {h₂ = h₂} {m = ref c₁ c₂} eq
    -- ...   | ⟨ ℓ , () ⟩
    -- ... | middle (∀̇ c) with ⨟ᵐᵗʰ-middle-err {t₁ = t₁} {h₂ = h₂} {m = ∀̇ c} eq
    -- ...   | ⟨ ℓ , () ⟩
    -- ... | middle (e₁ <: e₂ => c) with ⨟ᵐᵗʰ-middle-err {t₁ = t₁} {h₂ = h₂} {m = e₁ <: e₂ => c} eq
    -- ...   | ⟨ ℓ , () ⟩
    -- ... | middle id⋆ with ⨟ᵐᵗʰ-middle-err {t₁ = t₁} {h₂ = h₂} {m = id⋆} eq
    -- ...   | ⟨ ℓ , () ⟩
    -- ... | middle (idι ι) with ⨟ᵐᵗʰ-middle-err {t₁ = t₁} {h₂ = h₂} {m = idι ι} eq
    -- ...   | ⟨ ℓ , () ⟩
    -- ... | middle (err A B ℓ) = h₁ ⨾ err _ _ ℓ ⨾ t₂

    -- data IsProj : ∀ {Δ Θ} {A B} → (c : Δ ; Θ ⊢ᵐ A ⇒ B) → Set where
    --   proj : ∀{Δ}{Θ}{H : MType Δ}{h : Ground H}{ℓ} → IsProj{Δ}{Θ} ((H ？ ℓ) h)

    -- data IsErr : ∀ {Δ Θ} {A B} → (c : Δ ; Θ ⊢ᵐ A ⇒ B) → Set where
    --   error : ∀{Δ}{Θ}{A B : MType Δ}{ℓ} → IsErr{Δ}{Θ} (err A B ℓ)

    -- not-star-proj : ∀ {Δ Θ} {A B}
    --   → (c : Δ ; Θ ⊢ᵐ A ⇒ B)
    --   → A ≢ ⋆
    --   → ¬ IsProj c
    -- not-star-proj {Δ} {Θ} {A} {B} (id .A) A⋆ = λ ()
    -- not-star-proj {Δ} {Θ} {A} {B} ((.A ！) x) A⋆ = λ ()
    -- not-star-proj {Δ} {Θ} {A} {B} ((.B ？ x) x₁) A⋆ = ⊥-elim (A⋆ refl)
    -- not-star-proj {Δ} {Θ} {A} {B} (c ⨾ d) A⋆ = λ ()
    -- not-star-proj {Δ} {Θ} {A} {B} (c ⇒ d) A⋆ = λ ()
    -- not-star-proj {Δ} {Θ} {A} {B} (‶ co ″ ce) A⋆ = λ ()
    -- not-star-proj {Δ} {Θ} {A} {B} (ref c d) A⋆ = λ ()
    -- not-star-proj {Δ} {Θ} {A} {B} (∀̇ c) A⋆ = λ ()
    -- not-star-proj {Δ} {Θ} {A} {B} (e₁ <: e₂ => c) A⋆ = λ ()
    -- not-star-proj {Δ} {Θ} {A} {B} (err .A .B ℓ) A⋆ = λ ()

    -- is-err : ∀ {Δ Θ} {A B} → (c : Δ ; Θ ⊢ᵐ A ⇒ B) → Dec (IsErr c)
    -- is-err (id _) = no (λ ())
    -- is-err ((_ ！) x) = no (λ ())
    -- is-err ((_ ？ x) x₁) = no (λ ())
    -- is-err (c ⨾ c₁) = no (λ ())
    -- is-err (c ⇒ c₁) = no (λ ())
    -- is-err (‶ x ″ x₁) = no (λ ())
    -- is-err (ref c c₁) = no (λ ())
    -- is-err (∀̇ c) = no (λ ())
    -- is-err (e₁ <: e₂ => c) = no (λ ())
    -- is-err (err _ _ x) = yes error

    -- Θ-swap-c : ∀ {Δ Θ A B e₁ e₂ e₃ e₄}
    --   → Δ ; Θ , e₃ <: e₄ , e₁ <: e₂ ⊢ᵐ A ⇒ B
    --   → Δ ; Θ , e₁ <: e₂ , e₃ <: e₄ ⊢ᵐ A ⇒ B
    -- Θ-swap-c (id A) = id A
    -- Θ-swap-c ((G ！) g) = (G ！) g
    -- Θ-swap-c ((G ？ ℓ) g) = (G ？ ℓ) g
    -- Θ-swap-c (c ⨾ d) = (Θ-swap-c c) ⨾ (Θ-swap-c d)
    -- Θ-swap-c (c ⇒ d) = (Θ-swap-c c) ⇒ (Θ-swap-c d)
    -- Θ-swap-c (‶ x ″ x₁) = {!!}
    -- Θ-swap-c (ref c c₁) = {!!}
    -- Θ-swap-c (∀̇ c) = {!!}
    -- Θ-swap-c {e₁ = e₁} {e₂} {e₃ } (e₁ <: e₂ => c) = {!!}
    -- Θ-swap-c (err _ _ x) = {!!}

    -- Θ-weaken-c : ∀ {Δ Θ A B e₁ e₂}
    --   → Δ ; Θ ⊢ᵐ A ⇒ B
    --   → Δ ; Θ , e₁ <: e₂ ⊢ᵐ A ⇒ B
    -- Θ-weaken-c (id _) = {!!}
    -- Θ-weaken-c ((_ ！) x) = {!!}
    -- Θ-weaken-c ((_ ？ x) x₁) = {!!}
    -- Θ-weaken-c (c ⨾ c₁) = {!!}
    -- Θ-weaken-c (c ⇒ c₁) = {!!}
    -- Θ-weaken-c (‶ x ″ x₁) = {!!}
    -- Θ-weaken-c (ref c c₁) = {!!}
    -- Θ-weaken-c (∀̇ c) = {!!}
    -- Θ-weaken-c (e₁ <: e₂ => c) = e₁ <: e₂ => {!!}
    -- Θ-weaken-c (err A B ℓ) = err A B ℓ

  open MetaCoercions public
