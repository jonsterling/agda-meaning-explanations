{-# OPTIONS --no-positivity-check #-}

open import Agda.Primitive

data [0] : Set where

record [1] : Set where
  constructor ⟨⟩

record Σ (A : Set) (B : A → Set) : Set where
  constructor ⟨_,_⟩ 
  field
    π₁ : A
    π₂ : B π₁
open Σ public

_×_ : Set → Set → Set
A × B = Σ A λ _ → B
  
data sort : Set where
  + - : sort

data tm : sort → Set where
  ↑_ : tm + → tm -
  _&_ : tm - → tm - → tm +
  ⟨_,_⟩ : tm - → tm - → tm +
  fst snd : tm - → tm -
  unit ax : tm +

data _⟦=>⟧_ : tm - → tm + → Set where
  =>/↑ : ∀ {M} → ↑ M ⟦=>⟧ M
  =>/fst : ∀ {M M1 M2 M1′} → M ⟦=>⟧ ⟨ M1 , M2 ⟩ → M1 ⟦=>⟧ M1′ → fst M ⟦=>⟧ M1′
  =>/snd : ∀ {M M1 M2 M2′} → M ⟦=>⟧ ⟨ M1 , M2 ⟩ → M2 ⟦=>⟧ M2′ → snd M ⟦=>⟧ M2′

data judgement : Set
⊢_ : (J : judgement) → Set
infixl 3 ⊢_

data judgement where
  not-now triv : judgement
  _then_ : judgement → judgement → judgement

  _=>_ : tm - → tm + → judgement
  _type+ : tm + → judgement
  _type : tm - → judgement
  _∈_ : (M A : tm -) {{ _ : ⊢ A type }} → judgement

record _⟦type+⟧ (A : tm +) : Set where
  field
    type+/ver : tm + → judgement
    type+/ver= : ∀ M N → ⊢ type+/ver M → ⊢ type+/ver N → judgement

open _⟦type+⟧ public

record _⟦type⟧ (A : tm -) : Set where
  field
    {type/val} : tm +
    {{type/=>}} : ⊢ A => type/val
    {{type/type+}} : ⊢ type/val type+
open _⟦type⟧ public

record _⟦∈⟧_ (M A : tm -) {{A-type : A ⟦type⟧}} : Set

_==_∈_ : (M N A : tm -) {{_ : ⊢ A type}} {{_ : ⊢ M ∈ A}} {{_ : ⊢ N ∈ A}} → judgement

⊢ not-now = [0]
⊢ triv = [1]
⊢ (J1 then J2) = (⊢ J1) × (⊢ J2)
⊢ (A type) = A ⟦type⟧
⊢ (A type+) = A ⟦type+⟧
⊢ (M => M′) = M ⟦=>⟧ M′
⊢ (_∈_ M A {{A-type}}) = M ⟦∈⟧ A

instance
  auto-prod : ∀ {A B} → {{M : A}} {{N : B M}} → Σ A B
  auto-prod {{M}} {{N}} = ⟨ M , N ⟩

record _⟦∈⟧_ (M A : tm -) {{A-type : A ⟦type⟧}} where
  field
    {∈/val} : tm +
    {{∈/=>val}} : ⊢ M => ∈/val
    {{∈/ver+}} : ⊢ type+/ver (type/type+ A-type) ∈/val
open _⟦∈⟧_ public

_==_∈_ M N A {{A-type}} {{M∈A}} {{N∈A}} = type+/ver= (type/type+ A-type) (∈/val M∈A) (∈/val N∈A) (∈/ver+ M∈A) (∈/ver+ N∈A)



instance
  unit-type : ⊢ unit type+
  unit-type =
    record
      { type+/ver = λ {ax → triv ; x → not-now}
      ; type+/ver= = λ {ax ax ⟨⟩ ⟨⟩ → triv ; _ _ _ _ → not-now }
      }

  prod-type : ∀ {P Q} {{_ : ⊢ P type}} {{_ : ⊢ Q type}} → ⊢ (P & Q) type+
  prod-type {P} {Q} {{P-type}} {{Q-type}} =
    record
      { type+/ver = λ {⟨ M , N ⟩ → (_∈_ M P {{P-type}}) then (_∈_ N Q {{Q-type}}) ; x → not-now}
      ; type+/ver= = λ {⟨ M1 , N1 ⟩ ⟨ M2 , N2 ⟩ ⟨ M1∈P , N1∈Q ⟩ ⟨ M2∈P , N2∈Q ⟩ → (M1 == M2 ∈ P) then (N1 == N2 ∈ Q); _ _ _ _ → not-now}
      }

test : ⊢ (↑ ax) ∈ (↑ unit)
test = record {}

test2 : ⊢ (↑ ⟨ ↑ ax , ↑ ax ⟩) ∈ (↑ ((↑ unit) & (↑ unit)))
test2 = record {}

