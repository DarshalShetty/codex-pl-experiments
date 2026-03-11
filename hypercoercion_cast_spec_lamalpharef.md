# Cast Calculus for lambda alpha ref star using hypercoercions
This document specifies a space-efficient variant of the system described in
`cast_spec_lamalpharef.md` using hypercoercions. Usages of judgments/helper
functions not defined in this file can be found in either
`cast_spec_lamalpharef.md` or `elaboration.md`.

# Syntax

Overriding the syntax of coercions (`c`)

```
atomic types                       atm ::= ⋆ | ι

meta hypercoercions                  c ::= h;m;t
meta hypercoercion heads             h ::= G?ℓ | id A
meta hypercoercion middles           m ::= c → c | ‶ cᵒ ″cᵉ  | Ref c c | ∀ α. c | e <: e ⇒ c | id atm
                                         | ⊥ A ⇒ B ℓ
meta hypercoercion tails             t ::= G! | id A

code hypercoercions                  cᵒ ::= hᵒ;mᵒ;tᵒ 
code hypercoercion heads             hᵒ ::= Gᵒ?ℓ | id C
code hypercoercion middles           mᵒ ::= cᵒ → cᵒ | id atm | ⊥ C ⇒ C ℓ
code hypercoercion tails             tᵒ ::= Gᵒ! | id C

ec hypercoercions                  cᵉ ::= hᵉ;mᵉ;tᵉ
ec hypercoercion heads             hᵉ ::= e?ℓ | id ê
ec hypercoercion middles           mᵉ ::= e ↑ e | ⊥ ê ⇒ ê ℓ
ec hypercoercion tails             tᵉ ::= e! | id ê
```

# Hypercoercion Typing rules

## Meta Hypercoercion typing
```
+-------------------------------+
|       Δ;Θ ⊢ c : A ⇒ B        |
+-------------------------------+

 Δ ⊢ h : A ⇒ A'
 Δ;Θ ⊢ m : A' ⇒ B'
 Δ ⊢ t : B' ⇒ B
-------------------------(meta-hc)
 Δ;Θ ⊢ h;m;t : A ⇒ B
```

## Meta Hypercoercion head typing
```
+-----------------------------+
|       Δ ⊢ h : A ⇒ B        |
+-----------------------------+

 Δ ⊢ G
-----------------(meta-hc-head-proj)
 Δ ⊢ G? : ⋆ ⇒ G

 Δ ⊢ A
------------------(meta-hc-head-id)
 Δ ⊢ id A : A ⇒ A

```

## Meta Hypercoercion middle typing
```
+-------------------------------+
|       Δ;Θ ⊢ m : A ⇒ B        |
+-------------------------------+

 Δ;Θ ⊢ c₁ : A₂ ⇒ A₁
 Δ;Θ ⊢ c₂ : B₁ ⇒ B₂
------------------------------------(meta-hc-mid-fun)
 Δ;Θ ⊢ c₁ → c₂ : A₁ → B₁ ⇒ A₂ → B₂

  ⊢ cᵒ : C₁ ⇒ C₂
 Δ;Θ ⊢ cᵉ : ê ⇒ ê'
------------------------------------(meta-hc-mid-code)
 Δ;Θ ⊢ ‶ cᵒ ″cᵉ : ‶ C₁ ″ê ⇒ ‶ C₂ ″ê' 

 Δ;Θ ⊢ c₁ : B ⇒ A
 Δ;Θ ⊢ c₂ : A ⇒ B
----------------------------------(meta-hc-mid-ref)
 Δ;Θ ⊢ Ref c₁ c₂ : Ref A ⇒ Ref B

 Δ, α; Θ ⊢ c : A ⇒ B       α ∉ γ
------------------------------------(meta-hc-mid-univ)
 Δ;Θ ⊢ ∀ α. c : ∀ α. A ⇒ ∀ α. B

Δ ⊢ e₁  Δ ⊢ e₂
Δ; Θ, e₁ <: e₂ ⊢ c : A ⇒ B
---------------------------------------------------------(meta-hc-mid-sub)
Δ;Θ ⊢ e₁ <: e₂ ⇒ c : (e₁ <: e₂ ⇒ A) ⇒ (e₁ <: e₂ ⇒ B)

--------------------------(meta-hc-mid-id)
 Δ;Θ ⊢ id atm : atm ⇒ atm

 Δ ⊢ A     Δ ⊢ B
--------------------------(meta-hc-mid-bot)
 Δ ⊢ ⊥ A ⇒ B ℓ : A ⇒ B

```

## Meta Hypercoercion tail typing
```
+-----------------------------+
|       Δ ⊢ t : A ⇒ B        |
+-----------------------------+

 Δ ⊢ G
-----------------(meta-hc-tail-inj)
 Δ ⊢ G! : G ⇒ ⋆

 Δ ⊢ A
------------------(meta-hc-tail-id)
 Δ;Θ ⊢ id A : A ⇒ A

```

## Code Hypercoercion typing
```
+-------------------------+
|     ⊢ cᵒ : C₁ ⇒ C₂     |
+-------------------------+

  ⊢ hᵒ : C₁ ⇒ C₂
  ⊢ mᵒ : C₂ ⇒ C₃
  ⊢ tᵒ : C₃ ⇒ C₄
-------------------------(code-hc)
  ⊢ hᵒ;mᵒ;tᵒ : C₁ ⇒ C₄
```

## Code Hypercoercion head typing
```
+-----------------------+
|    ⊢ hᵒ : C₁ ⇒ C₂    |
+-----------------------+

---------------------(code-hc-head-proj)
 ⊢ Gᵒ? : ⋆ ⇒ Gᵒ

------------------(code-hc-head-id)
 ⊢ id C : C ⇒ C

```

## Code Hypercoercion middle typing
```
+-------------------------+
|     ⊢ mᵒ : C₁ ⇒ C₂     |
+-------------------------+

  ⊢ cᵒ₁ : C₃ ⇒ C₁
  ⊢ cᵒ₂ : C₂ ⇒ C₄
------------------------------------------(code-hc-mid-fun)
  ⊢ cᵒ₁ → cᵒ₂ : C₁ → C₂ ⇒ C₃ → C₄

---------------------------(code-hc-mid-id)
  ⊢ id atm : atm ⇒ atm

------------------------------(code-hc-mid-bot)
  ⊢ ⊥ C₁ ⇒ C₂ ℓ : C₁ ⇒ C₂

```

## Code Hypercoercion tail typing
```
+--------------------------+
|      ⊢ tᵒ : C₁ ⇒ C₂     |
+--------------------------+

---------------------(code-hc-tail-inj)
  ⊢ Gᵒ! : Gᵒ ⇒ ⋆

---------------------(code-hc-tail-id)
  ⊢ id C : C ⇒ C

```

## EC Hypercoercion typing
```
+------------------------------+
|     Δ;Θ ⊢ cᵉ : ê ⇒ ê'       |
+------------------------------+

 Δ ⊢ hᵉ : ê ⇒ ê''
 Δ;Θ ⊢ mᵉ : ê'' ⇒ ê'''
 Δ ⊢ tᵉ : ê''' ⇒ ê'
------------------------(ec-hc)
 Δ;Θ ⊢ hᵉ;mᵉ;tᵉ : ê ⇒ ê'
```

## EC Hypercoercion head typing
```
+-----------------------------+
|      Δ ⊢ hᵉ : ê ⇒ ê'       |
+-----------------------------+

 Δ ⊢ e
-----------------(ec-hc-head-proj)
 Δ ⊢ e? : ⋆ ⇒ e

 Δ ⊢ ê
--------------------(ec-hc-head-id)
 Δ ⊢ id ê : ê ⇒ ê
```

## EC Hypercoercion middle typing
```
+-------------------------------+
|      Δ;Θ ⊢ mᵉ : ê ⇒ ê'       |
+-------------------------------+

 Θ ⊢ e <: e'
 Δ ⊢ e     Δ ⊢ e'
-------------------------(ec-hc-mid-sub)
 Δ;Θ ⊢ e ↑ e' : e ⇒ e'

 Δ ⊢ ê    Δ ⊢ ê'
-------------------------(ec-hc-mid-bot)
 Δ;Θ ⊢ ⊥ ê ⇒ ê' ℓ : ê ⇒ ê'
```

## EC Hypercoercion tail typing
```
+----------------------------+
|      Δ ⊢ tᵉ : ê ⇒ ê'       |
+----------------------------+

 Δ ⊢ e
-----------------(ec-hc-tail-inj)
 Δ ⊢ e! : e ⇒ ⋆

 Δ ⊢ ê
--------------------(ec-hc-tail-id)
 Δ ⊢ id ê : ê ⇒ ê

```

# Metafunctions used in judgments

## Generating identity middle coercions for ground types
```
+--------------------------------------------+
|   ground-id : {G,Gᵒ} → {G,Gᵒ} → {m,mᵒ}   |
+--------------------------------------------+

let ID⋆ = id ⋆ ; id ⋆ ; id ⋆

ground-id ι             = id ι
ground-id ⋆ → ⋆         = ID⋆ → ID⋆
ground-id Ref ⋆         = Ref (ID⋆) (ID⋆)
ground-id ‶ ⋆ ″⋆        = ‶ ID⋆ ″ (id ⋆ ; ⋆ ↑ ⋆ ; id ⋆)
ground-id ∀ α. ⋆        = ∀ α. ID⋆ 
ground-id e₁ <: e₂ ⇒ ⋆  = e₁ <: e₂ ⇒ ID⋆ 
```

## Compiling implicit casts to coercions

```
+-------------------------------+
|   coerce : A → B → ℓ → c   |
+-------------------------------+
(precondition: Δ;Θ ⊢ A ≲ B)
(postcondition: Δ;Θ ⊢ coerce A B ℓ : A ⇒ B)

coerce ι ι ℓ = id ι ; id ι ; id ι 
coerce ⋆ ⋆ ℓ = id ⋆ ; id ⋆ ; id ⋆

coerce ⋆ G ℓ = G?ℓ ; ground-id G ; id G
coerce G ⋆ ℓ = id G ; ground-id G ; G!

coerce ⋆ A ℓ = G?ℓ ; (coerce G A ℓ) ; id A , where G = ground A
coerce A ⋆ ℓ = id A ; (coerce A G ℓ) ; G!, where G = ground A

coerce (A → B) (A' → B') ℓ = id ; (coerce A' A ℓ) → (coerce B B' ℓ) ; id 

coerce (Ref A) (Ref B) ℓ = id ; Ref (coerce B A ℓ) (coerce A B ℓ) ; id

coerce (‶ C₁ ″ ê) (‶ C₂ ″ ê') ℓ = id ; ‶ coerceᵒ C₁ C₂ ℓ ″(coerce-ec ê ê' ℓ) ; id

coerce (∀ α. A) (∀ α. A') ℓ = id ; ∀ α. (coerce A A' ℓ) ; id

coerce (e₁ <: e₂ ⇒ A) (e₁ <: e₂ ⇒ A') ℓ = id ; e₁ <: e₂ ⇒ (coerce A A' ℓ) ; id

+-----------------------------------+
|   coerceᵒ : C₁ → C₂ → ℓ → cᵒ   |
+-----------------------------------+
(same definition as coerce but without cases about reference, code and forall types)

+------------------------------------+
|   coerce-ec : ê → ê' → ℓ → cᵉ   |
+------------------------------------+
(precondition: Θ ⊢ ê ≲ ê')
(postcondition: Δ;Θ ⊢ coerce-ec ê ê' ℓ : ê ⇒ ê')

coerce-ec ⋆ ⋆ = id ⋆ ; ⋆ ↑ ⋆ ; id ⋆
coerce-ec e ⋆ = id e ; e ↑ e ; e!
coerce-ec ⋆ e = e?ℓ ; e ↑ e ; id e
coerce-ec e e' = id e ; e ↑ e' ; id e'
```

## Composing hypercoercions

### Meta hypercoercions

```
+-----------------------+
|   Θ ⊢ c₁ ⨟ c₂ = c     |
+-----------------------+
(precondition: Δ;Θ ⊢ c₁ : A ⇒ A' and Δ;Θ ⊢ c₂ : A' ⇒ B)
(postcondition: Δ;Θ ⊢ c : A ⇒ B)

Θ ⊢ h₁;⊥ℓ;t₁ ⨟ h₂;m₂;t₂ = h₁;⊥ℓ;t₂
Θ ⊢ h₁;m₁;t₁ ⨟ h₂;⊥ℓ;t₂ = match t₁ ⨟ h₂ with
                           case ⊥ℓ′ => h₁;⊥ℓ′;t₂
                           case _   => h₁;⊥ℓ;t₂
Θ ⊢ h₁;m₁;t₁ ⨟ h₂;m₂;t₂ = match t₁ ⨟ h₂ with
                           case id    => h₁;(Θ ⊢ m₁ ⨟ m₂);t₂
                           case G!    => h₁;m₁;G!
                           case H?ℓ   => H?ℓ;m₂;t₂
                           case ⊥ℓ    => h₁;⊥ℓ;t₂
```

```
+--------------------------+
|    t ⨟ h = t ∪ h ∪ ⊥ℓ    |
+--------------------------+
(precondition: Δ ⊢ t : A ⇒ A' and Δ ⊢ h : A' ⇒ B)
(postcondition: Δ ⊢ t ⨟ h : A ⇒ B)
 
t      ⨟ id  = t 
id     ⨟ h   = h
G!     ⨟ G?ℓ = id
G!     ⨟ H?ℓ = ⊥ℓ   , if G≠H
```

```
+---------------------+
|   Θ ⊢ m₁ ⨟ m₂ = m   |
+---------------------+
(precondition: Δ;Θ ⊢ m₁ : A ⇒ A' and Δ;Θ ⊢ m₂ : A' ⇒ B)
(postcondition: Δ;Θ ⊢ m : A ⇒ B)

Θ ⊢ m₁            ⨟ id             = m₁
Θ ⊢ id            ⨟ m₂             = m₂
Θ ⊢ c₁→c₂         ⨟ c₃→c₄          = (Θ ⊢ c₃ ⨟ c₁)→(Θ ⊢ c₂ ⨟ c₄)
Θ ⊢ ‶ cᵒ₁ ″cᵉ₁    ⨟ ‶ cᵒ₂ ″cᵉ₂     = 
   match (cᵒ₁ ⨟ cᵒ₂) (Θ ⊢ cᵉ₁ ⨟ cᵉ₂) with
     case (hᵒ ; ⊥ℓ ; tᵒ) _ => ⊥ℓ
     case _ (hᵉ ; ⊥ℓ ; tᵉ) => ⊥ℓ
     case cᵒ cᵉ          => ‶ cᵒ ″ cᵉ
Θ ⊢ Ref c₁ c₂     ⨟ Ref c₃ c₄      = Ref (Θ ⊢ c₃ ⨟ c₁) (Θ ⊢ c₂ ⨟ c₄)
Θ ⊢ ∀ α. c₁ ⨟ ∀ α. c₂              = ∀ α. (Θ ⊢ c₁ ⨟ c₂)
Θ ⊢ e₁ <: e₂ ⇒ c₁ ⨟ e₁ <: e₂ ⇒ c₂  = e₁ <: e₂ ⇒ (Θ, e₁ <: e₂ ⊢ c₁ ⨟ c₂)
Θ ⊢ ⊥ℓ            ⨟ m₂             = ⊥ℓ
Θ ⊢ m₁            ⨟ ⊥ℓ             = ⊥ℓ
```

### Code hypercoercions

Here we need to be eager about bubbling up errors. Thus, we need to case on the
result of intermediate composition calls in the definition of hypercoercion and
middle composition.

```
+-----------------------+
|     ĉᵒ₁ ⨟ ĉᵒ₂ = ĉᵒ    |
+-----------------------+
(precondition: ⊢ cᵒ₁ : C₁ ⇒ C₂ and ⊢ cᵒ₂ : C₂ ⇒ C₃)
(postcondition: ⊢ cᵒ : C₁ ⇒ C₃)

hᵒ₁;⊥ℓ;tᵒ₁ ⨟ hᵒ₂;mᵒ₂;tᵒ₂  = hᵒ₁;⊥ℓ;tᵒ₂
Θ ⊢ hᵒ₁;mᵒ₁;tᵒ₁ ⨟ hᵒ₂;⊥ℓ;tᵒ₂ = match tᵒ₁ ⨟ hᵒ₂ with
                           case ⊥ℓ′ => hᵒ₁;⊥ℓ′;tᵒ₂
                           case _   => hᵒ₁;⊥ℓ;tᵒ₂
hᵒ₁;mᵒ₁;tᵒ₁ ⨟ hᵒ₂;mᵒ₂;tᵒ₂ = match tᵒ₁ ⨟ hᵒ₂ with
                             case id     => hᵒ₁ ; (mᵒ₁ ⨟ mᵒ₂) ; tᵒ₂
                             case T'!    => hᵒ₁ ; mᵒ₁ ; T'!
                             case T'?ℓ   => T'?ℓ ; mᵒ₂ ; tᵒ₂
                             case ⊥ℓ     => hᵒ₁  ; ⊥ℓ ; tᵒ₂
```

```
+-----------------------------+
|    tᵒ ⨟ hᵒ = tᵒ ∪ hᵒ ∪ ⊥ℓ   |
+-----------------------------+
(precondition: ⊢ tᵒ : C₁ ⇒ C₂ and ⊢ hᵒ : C₂ ⇒ C₃)
(postcondition: ⊢ tᵒ ⨟ hᵒ : C₁ ⇒ C₃)
 
tᵒ  ⨟ id   = tᵒ
id  ⨟ hᵒ   = hᵒ
T!  ⨟ T?ℓ  = id
S!  ⨟ T?ℓ  = ⊥ℓ   , if T≠S
```

```
+----------------------+
|    mᵒ₁ ⨟ mᵒ₂ = mᵒ    |
+----------------------+
(precondition: ⊢ mᵒ₁ : S ⇒ S' and ⊢ mᵒ₂ : S' ⇒ T)
(postcondition: ⊢ mᵒ : S ⇒ T)

mᵒ₁      ⨟ id       = mᵒ₁
id       ⨟ mᵒ₂      = mᵒ₂
cᵒ₁→cᵒ₂  ⨟ cᵒ₃→cᵒ₄  = 
    match (cᵒ₃ ⨟ cᵒ₁) (cᵒ₂ ⨟ cᵒ₄) with
      case (hᵒ ; ⊥ℓ ; tᵒ) _ => ⊥ℓ
      case _ (hᵒ ; ⊥ℓ ; tᵒ) => ⊥ℓ
      case cᵒ₁' cᵒ₂'        => cᵒ₁' → cᵒ₂'
Θ ⊢ ⊥ℓ   ⨟ mᵒ₂      = ⊥ℓ
Θ ⊢ mᵒ₁  ⨟ ⊥ℓ       = ⊥ℓ
```

### EC hypercoercions

```
+------------------------+
|   Θ ⊢ cᵉ₁ ⨟ cᵉ₂ = cᵉ   |
+------------------------+
(precondition: Δ;Θ ⊢ cᵉ₁ : ê ⇒ ê'' and Δ;Θ ⊢ cᵉ₂ : ê'' ⇒ ê')
(postcondition: Δ;Θ ⊢ cᵉ : ê ⇒ ê')

Θ ⊢ hᵉ₁;⊥ℓ;tᵉ₁  ⨟ hᵉ₂;mᵉ₂;tᵉ₂ = hᵉ₁;⊥ℓ;tᵉ₂
Θ ⊢ hᵉ₁;mᵉ₁;tᵉ₁ ⨟ hᵉ₂;⊥ℓ;tᵉ₂ = match tᵉ₁ ⨟ hᵉ₂ with
                                 case ⊥ℓ′ => hᵉ₁;⊥ℓ′;tᵉ₂
                                 case _   => hᵉ₁;⊥ℓ;tᵉ₂
Θ ⊢ hᵉ₁;mᵉ₁;tᵉ₁ ⨟ hᵉ₂;mᵉ₂;tᵉ₂ = match Θ ⊢ tᵉ₁ ⨟ hᵉ₂ with
                             case e₁ ↑ e₂ => hᵉ₁ ; (mᵉ₁ ⨟ (e₁ ↑ e₂ ⨟ mᵉ₂)) ; tᵉ₂
                             case id       => hᵉ₁ ; (mᵉ₁ ⨟ mᵉ₂) ; tᵉ₂
                             case e!       => hᵉ₁ ; mᵉ₁         ; e!
                             case e?ℓ      => e?ℓ ; mᵉ₂         ; tᵉ₂
                             case ⊥ℓ       => hᵉ₁ ; ⊥ℓ          ; tᵉ₂
```

```
+--------------------------------+
|   Θ ⊢ tᵉ ⨟ hᵉ = tᵉ ∪ hᵉ ∪ mᵉ   |
+--------------------------------+
(precondition: Δ;Θ ⊢ tᵉ : ê ⇒ ê'' and Δ;Θ ⊢ hᵉ : ê'' ⇒ ê')
(postcondition: Δ;Θ ⊢ tᵉ ⨟ hᵉ : ê ⇒ ê')
 
Θ ⊢ tᵉ  ⨟ id   = tᵉ
Θ ⊢ id  ⨟ hᵉ   = hᵉ
Θ ⊢ e₁! ⨟ e₂?ℓ = e₁ ↑ e₂, if Θ ⊢ e₁ <: e₂ 
Θ ⊢ e₁! ⨟ e₂?ℓ = ⊥ℓ      , if Θ ⊬ e₁ <: e₂ 
```

``` 
+-----------------------+
|    mᵉ₁ ⨟ mᵉ₂ = mᵉ     |
+-----------------------+
(precondition: Δ;Θ ⊢ mᵉ₁ : ê ⇒ ê'' and Δ;Θ ⊢ mᵉ₂ : ê'' ⇒ ê')
(postcondition: Δ;Θ ⊢ mᵉ : ê ⇒ ê')

e↑e''   ⨟ e''↑e'  = e↑e'
⊥ℓ       ⨟ mᵉ₂      = ⊥ℓ
mᵉ₁      ⨟ ⊥ℓ       = ⊥ℓ
```

# Dynamic semantics for coercion calculus

# Values
```
heap addresses          a ∈ Locations
code values            Vᵒ ::= k | x | λ̅ α (x:T). Vᵒ | Vᵒ Vᵒ 
inert hypercoercions    c̅ ::= id _;m;G! | id _;m₁;id _ (m₁ shouldn't be id or ⊥, and m shouldn't be ⊥)
uncoerced values        U ::= k | λ (x:A). M | Λ α. M | e <: e ⇒ M | a | ‷ Vᵒ ‴e
values                V,W ::= U | U<c̅>
```

# Frames

```
meta frame    F ::= □ M | V □ | □[e] | □• | □•⋆ℓ
                  | ref □ | □ := M | V := □ | !□

code frame    Fᵒ ::= □ Mᵒ | Mˢ □ 

error frame   Fᵒ_b ::= Fᵒ | λ̅ α (x:S). □
```

# Reduction Context

```
ctx ::= Any | NonCast
```

# Reduction rules 

The EC context Δ, heap μ and subtype store Θ will be omitted when they don't get
updated in a rule.

F{M} represents plugging the term M into the hole of a frame F

## Meta Reduction

```
+----------------------------------+
|   ctx ⊢ ⟨Δ,Θ,μ,M⟩ ⟶ᵐ ⟨Δ,Θ,μ,M⟩   |
+----------------------------------+

-----------------------------------(λ-β)
  Any ⊢ (λ (x:A). M) V ⟶ᵐ M[x:=V]

--------------------------------(Λ-β)
  Any ⊢ (Λ α. M)[e] ⟶ᵐ M[α:=e] 

--------------------------------(<:-β)
  Any ⊢ (e₁ <: e₂ ⇒ M) • ⟶ᵐ M

  a ∉ dom(μ)
--------------------------------------------(ref)
  Any ⊢ ⟨Δ,Θ,μ,ref V⟩ ⟶ᵐ ⟨Δ,Θ,μ[a ↦ V],a⟩

------------------------------------(deref)
  Any ⊢ ⟨Δ,Θ,μ,!a⟩ ⟶ᵐ ⟨Δ,Θ,μ,μ(a)⟩
  
---------------------------------------------(assign)
  Any ⊢ ⟨Δ,Θ,μ,a := V⟩ ⟶ᵐ ⟨Δ,Θ,μ[a ↦ V],()⟩

-------------------------(quote-val)
  Any ⊢ ‶ Vᵒ ″e ⟶ᵐ ‷ Vᵒ ‴e

---------------------------------------------------------------(cast-compose)
  NonCast ⊢ ⟨Δ,Θ,μ,(M <c₁>) <c₂>⟩ ⟶ᵐ ⟨Δ,Θ,μ,M <Θ ⊢ c₁ ⨟ c₂>⟩
  
--------------------------------(cast-id)
  NonCast ⊢ U<id; id; id> ⟶ᵐ U

--------------------------------(cast-⊥)
  NonCast ⊢ U<id; ⊥ℓ; t> ⟶ᵐ blameℓ

---------------------------------------------------------(λ-β-cast)
  Any ⊢ U <id ; c₁ → c₂ ; id> W ⟶ᵐ (U (W < c₁ >)) <c₂>

---------------------------------------------(deref-cast)
  Any ⊢ !(a<id ;Ref c₁ c₂; id>) ⟶ᵐ (!a)<c₂>
  
---------------------------------------------(assign-cast)
  Any ⊢ a<id ;Ref c₁ c₂; id> := V ⟶ᵐ a:=(V<c₁>) 

--------------------------------------------------------------(Λ-β-cast)
  Any ⊢ U<id ; ∀ α. c ; id>[e] ⟶ᵐ U[e]<c[α:=e]>

------------------------------------------------------------(<:-β-cast)
  Any ⊢ (U<id ; e₁ <: e₂ ⇒ c ; id>) • ⟶ᵐ (U•)<c>

  Θ ⊢ e₁ <: e₂
----------------------------------------------------------------------------(<:-β-dyn-cast)
  Any ⊢ ⟨Δ,Θ,μ,(U<id ; m ; (e₁ <: e₂ ⇒ ⋆)!>) •⋆ℓ⟩ ⟶ᵐ ⟨Δ,Θ,μ,(U<id ; m ; id>) •⟩

  Θ ⊢ e₁ ≮: e₂
------------------------------------------------------------------(<:-β-dyn-cast-blame1)
  Any ⊢ ⟨Δ,Θ,μ,(U<id ; m ; (e₁ <: e₂ ⇒ ⋆)!>) •⋆ℓ⟩ ⟶ᵐ ⟨Δ,Θ,μ,blameℓ⟩

  ∀ e₁, e₂. G ≠ (e₁ <: e₂ ⇒ ⋆)
------------------------------------------------------------------(<:-β-dyn-cast-blame2)
  Any ⊢ ⟨Δ,Θ,μ,(U<id ; m ; G!>) •⋆ℓ⟩ ⟶ᵐ ⟨Δ,Θ,μ,blameℓ⟩

-------------------------(quote-blame)
  Any ⊢ ‶ ~blameℓ ″e ⟶ᵐ blameℓ

------------------------(cong-blame)
  Any ⊢ F{blameℓ} ⟶ᵐ blameℓ

  ⟨Δ,Θ,μ,Mᵒ⟩|e ⟶ᵒ ⟨Δ',Θ',μ',Nᵒ⟩
------------------------------------------(quote)
  Any ⊢ ⟨Δ,Θ,μ,‶ Mᵒ ″e⟩ ⟶ᵐ ⟨Δ',Θ',μ',‶ Nᵒ ″e⟩

  ctx ⊢ ⟨Δ,Θ,μ,M⟩ ⟶ᵐ ⟨Δ',Θ',μ',N⟩
-------------------------------------(cong)
  Any ⊢ ⟨Δ,Θ,μ,F{M}⟩ ⟶ᵐ ⟨Δ',Θ',μ',F{N}⟩

  Any ⊢ ⟨Δ,Θ,μ,M⟩ ⟶ᵐ ⟨Δ',Θ',μ',N⟩
-------------------------------------(cong-cast)
  NonCast ⊢ ⟨Δ,Θ,μ,M<c>⟩ ⟶ᵐ ⟨Δ',Θ',μ',N<c>⟩

```

## Code Reduction

```
+---------------------------------+
|   ⟨Δ,Θ,μ,Mᵒ⟩|e ⟶ᵒ ⟨Δ,Θ,μ,Mᵒ⟩   |
+---------------------------------+

---------------------------(splice-β)
  ~ ‷ Vᵒ ‴e |e →ᵒ  Vᵒ

----------------------------------------------------------------------(splice-code-sub)
  ~ (‷ Vᵒ ‴e₁)<id ; ‶ id ; mᵒ ; id ″(id ; e₁↑e₂ ; id) ; id> |e₂ ⟶ Vᵒ

  β ∉ Δ
-------------------------------------------------------------------------(code-λ)
  ⟨Δ,Θ,μ,λ α (x:S). Mᵒ⟩ |e →ᵒ ⟨(Δ,β),(Θ,e<:β),μ,λ̅ β (x:S). Mᵒ[α:=β]⟩

----------------------------------(code-cong-blame)
  Fᵒ_b{~ blameℓ} |e →ᵒ ~ blameℓ

  ⟨Δ,Θ,μ,Mᵒ⟩ |e →ᵒ ⟨Δ',Θ',μ',Nᵒ⟩
------------------------------------------(code-cong)
  ⟨Δ,Θ,μ,Fᵒ{Mᵒ}⟩ |e →ᵒ ⟨Δ',Θ',μ',Fᵒ{Nᵒ}⟩

  ⟨Δ,Θ,μ,Mᵒ⟩ |α ⟶ᵒ ⟨Δ',Θ',μ',Nᵒ⟩
---------------------------------------------------------(code-λ-cong)
  ⟨Δ,Θ,μ,λ̅ α (x:S). Mᵒ⟩ |e →ᵒ ⟨Δ',Θ',μ',λ̅ α (x:S). Nᵒ⟩
  
  ctx ⊢ ⟨Δ,Θ,μ,M⟩ ⟶ᵐ ⟨Δ',Θ',μ',N⟩
-------------------------------------(splice-cong)
  ⟨Δ,Θ,μ,~ M⟩ |e →ᵒ ⟨Δ',Θ',μ',~ N⟩
```
