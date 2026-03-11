module Utils where

open import Data.List
open import Data.Product using (_×_) renaming (_,_ to ⟨_,_⟩)
open import Data.Maybe renaming (_>>=_ to _bind_)
open import Data.Nat
open import Data.Bool using (Bool; true; false; if_then_else_; _∧_)
open import Relation.Nullary using (Dec; yes; no; ¬_)
open import Relation.Nullary.Negation using (contradiction)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; cong)
open import Function using (case_of_)
open import Agda.Builtin.String


record Eq (A : Set) : Set₁ where
  field
    _==_ : A → A → Bool

open Eq ⦃...⦄ using (_==_)

nth : ∀ {A : Set} → List A → ℕ → Maybe A
nth []       _       = nothing
nth (x ∷ ls) zero    = just x
nth (x ∷ ls) (suc k) = nth ls k

index : ∀ {A : Set} ⦃ eqA : Eq A ⦄ → List A → (a : A) → Maybe ℕ
index [] a = nothing
index (a ∷ as) b =
  if a == b then just 0
    else (index as b bind λ i → just (suc i))


{- Works on association lists -}
locate : ∀ {K V : Set} → (∀ (k₁ k₂ : K) → Dec (k₁ ≡ k₂)) → List (K × V) → K → Maybe V
locate _≟_ [] _ = nothing
locate _≟_ (⟨ k₀ , v₀ ⟩ ∷ l) k =
  case k ≟ k₀ of λ where
    (yes _) → just v₀
    (no  _) → locate _≟_ l k

assoc : ∀ {A B : Set} ⦃ eqA : Eq A ⦄ → List (A × B) → A → Maybe B
assoc [] _ = nothing
assoc (⟨ a , b ⟩ ∷ rest) c = if a == c then just b else assoc rest c

snoc-here : ∀ {X} (x : X) → ∀ xs → nth (xs ∷ʳ x) (length xs) ≡ just x
snoc-here x [] = refl
snoc-here x (_ ∷ xs) = snoc-here x xs

snoc-there : ∀ {X} (x : X) → ∀ xs {n y} → nth (xs ∷ʳ y) n ≡ just x → n ≢ length xs → nth xs n ≡ just x
snoc-there x [] {zero} refl neq = contradiction refl neq
snoc-there x (y ∷ xs) {zero} eq neq = eq
snoc-there x (y ∷ xs) {suc n} eq neq = snoc-there x xs eq n≢len
  where
  n≢len : n ≢ length xs
  n≢len n≡len = contradiction (cong suc n≡len) neq


length-∷-≤ : ∀ {A : Set} (x : A) (xs : List A) → length xs ≤ length (x ∷ xs)
length-∷-≤ x [] = z≤n
length-∷-≤ x (y ∷ xs) = s≤s (length-∷-≤ x xs)

pattern ⟨_,_,_⟩ x y z = ⟨ x , ⟨ y , z ⟩ ⟩
pattern ⟨_,_,_,_⟩ x y z w = ⟨ x , ⟨ y , ⟨ z , w ⟩ ⟩ ⟩
pattern ⟨_,_,_,_,_⟩ x y z w u = ⟨ x , ⟨ y , ⟨ z , ⟨ w , u ⟩ ⟩ ⟩ ⟩
pattern ⟨_,_,_,_,_,_⟩ x y z w u v = ⟨ x , ⟨ y , ⟨ z , ⟨ w , ⟨ u , v ⟩ ⟩ ⟩ ⟩ ⟩
pattern ⟨_,_,_,_,_,_,_⟩ x y z w u v p = ⟨ x , ⟨ y , ⟨ z , ⟨ w , ⟨ u , ⟨ v , p ⟩ ⟩ ⟩ ⟩ ⟩ ⟩
pattern ⟨_,_,_,_,_,_,_,_⟩ x y z w u v p q = ⟨ x , ⟨ y , ⟨ z , ⟨ w , ⟨ u , ⟨ v , ⟨ p , q ⟩ ⟩ ⟩ ⟩ ⟩ ⟩ ⟩
pattern ⟨_,_,_,_,_,_,_,_,_⟩ x y z w u v p q i = ⟨ x , ⟨ y , ⟨ z , ⟨ w , ⟨ u , ⟨ v , ⟨ p , ⟨ q , i ⟩ ⟩ ⟩ ⟩ ⟩ ⟩ ⟩ ⟩
pattern ⟨_,_,_,_,_,_,_,_,_,_⟩ x y z w u v p q i j = ⟨ x , ⟨ y , ⟨ z , ⟨ w , ⟨ u , ⟨ v , ⟨ p , ⟨ q , ⟨ i , j ⟩ ⟩ ⟩ ⟩ ⟩ ⟩ ⟩ ⟩ ⟩
pattern ⟨_,_,_,_,_,_,_,_,_,_,_⟩ x y z w u v p q i j k = ⟨ x , ⟨ y , ⟨ z , ⟨ w , ⟨ u , ⟨ v , ⟨ p , ⟨ q , ⟨ i , ⟨ j , k ⟩ ⟩ ⟩ ⟩ ⟩ ⟩ ⟩ ⟩ ⟩ ⟩
pattern ⟨_,_,_,_,_,_,_,_,_,_,_,_⟩ x y z w u v p q i j k m = ⟨ x , ⟨ y , ⟨ z , ⟨ w , ⟨ u , ⟨ v , ⟨ p , ⟨ q , ⟨ i , ⟨ j , ⟨ k , m ⟩ ⟩ ⟩ ⟩ ⟩ ⟩ ⟩ ⟩ ⟩ ⟩ ⟩


pattern [_,_] y z = y ∷ z ∷ []
pattern [_,_,_] x y z = x ∷ y ∷ z ∷ []
pattern [_,_,_,_] w x y z = w ∷ x ∷ y ∷ z ∷ []
pattern [_,_,_,_,_] v w x y z = v ∷ w ∷ x ∷ y ∷ z ∷ []
pattern [_,_,_,_,_,_] u v w x y z = u ∷ v ∷ w ∷ x ∷ y ∷ z ∷ []
pattern [_,_,_,_,_,_,_] u v w x y z p = u ∷ v ∷ w ∷ x ∷ y ∷ z ∷ p ∷ []
pattern [_,_,_,_,_,_,_,_] u v w x y z p q = u ∷ v ∷ w ∷ x ∷ y ∷ z ∷ p ∷ q ∷ []


instance
  EqNat : Eq ℕ
  EqNat ._==_ = _≡ᵇ_

instance
  EqStr : Eq String
  EqStr ._==_ = primStringEquality

eqList : ∀ {A : Set} ⦃ eqA : Eq A ⦄ → (xs ys : List A) → Bool
eqList [] [] = true
eqList [] (x ∷ _) = false
eqList (x ∷ _) [] = false
eqList (x ∷ xs) (y ∷ ys) = (x == y) ∧ eqList xs ys

instance
  EqList : ∀ {A : Set} ⦃ eqA : Eq A ⦄ → Eq (List A)
  EqList ._==_ = eqList


postulate
  extensionality : ∀ {ℓ₁ ℓ₂} {A : Set ℓ₁} {B : Set ℓ₂} {f g : A → B}
    → (∀ (x : A) → f x ≡ g x)
      ---------------------------
    → f ≡ g
