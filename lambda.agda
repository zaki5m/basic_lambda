module lambda where

open import Data.Bool using (Bool; true; false; T; not)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.List using (List; _∷_; [])
open import Data.Nat using (ℕ; zero; suc)
open import Data.Product using (∃-syntax; _×_)
open import Data.String using (String; _≟_)
open import Data.Unit using (tt)
open import Relation.Nullary using (Dec; yes; no; ¬_)
open import Relation.Nullary.Decidable using (False; toWitnessFalse)
open import Relation.Nullary.Negation using (¬?)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl)

Id : Set
Id = String

infix  5  ƛ_⇒_
infix  5  μ_⇒_
infixl 7  _·_
infix  8  `suc_
infix  9  `_

data Term : Set where
  `_                      :  Id → Term
  ƛ_⇒_                    :  Id → Term → Term
  _·_                     :  Term → Term → Term
  `zero                   :  Term
  `suc_                   :  Term → Term
  case_[zero⇒_|suc_⇒_]    :  Term → Term → Id → Term → Term
  μ_⇒_                    :  Id → Term → Term

two : Term
two = `suc `suc `zero

plus : Term
plus = μ "+" ⇒ ƛ "m" ⇒ ƛ "n" ⇒
         case ` "m"
           [zero⇒ ` "n"
           |suc "m" ⇒ `suc (` "+" · ` "m" · ` "n") ]

twoᶜ : Term
twoᶜ = ƛ "s" ⇒ ƛ "z" ⇒ ` "s"  · (` "s" · ` "z")

plusᶜ : Term
plusᶜ = ƛ "m" ⇒ ƛ "n" ⇒ ƛ "s" ⇒ ƛ "z" ⇒ ` "m" · ` "s" · (` "n" · ` "s" · ` "z")

sucᶜ : Term
sucᶜ = ƛ "n" ⇒ `suc (` "n")

_ : Term
_ = plus · two · two

_ : Term
_ = plusᶜ · twoᶜ · twoᶜ · sucᶜ · `zero

mul : Term
mul = μ "×" ⇒ ƛ "m" ⇒ ƛ "n" ⇒
        case ` "m"
        [zero⇒ ` "z"
        |suc "m" ⇒ `suc (` "×" · ` "m" · ` "n")]

val? : (t : Term) → Bool
val? (` _) = true
val? _ = false

ƛ'_⇒_ : (t : Term) → {_ : T (val? t)} → Term → Term
ƛ'_⇒_ (` x) N = ƛ x ⇒ N

case'_[zero⇒_|suc_⇒_] : Term → Term → (t : Term) → {_ : T (val? t)} → Term → Term
case' L [zero⇒ M |suc (` x) ⇒ N ] = case L [zero⇒ M |suc x ⇒ N ]

μ'_⇒_ : (t : Term) → {_ : T (val? t)} → Term → Term
μ' (` x) ⇒ N = μ x ⇒ N

_ : Term
_ = ƛ' two ⇒ two

plus' : Term
plus' = μ' + ⇒ ƛ' m ⇒ ƛ' n ⇒
        case' m
          [zero⇒ n
          |suc m ⇒ `suc (+ · m · n)]
      where
      + = ` "+"
      m = ` "m"
      n = ` "n"

data Value : Term → Set where

  V-ƛ : ∀ {x N}
      ------------
      → Value (ƛ x ⇒ N)

  V-zero :
      -------
      Value `zero

  V-suc : ∀ {V}
    -> Value V
    ---------
    → Value (`suc V)

infix 9 _[_:=_]

_[_:=_] : Term → Id → Term → Term
(` x) [ y := V ] with x ≟ y
... | yes _ = V
... | no _ = ` x
(ƛ x ⇒ N) [ y := V ] with x ≟ y
... | yes _ = ƛ x ⇒ N
... | no _ = ƛ x ⇒ N [ y := V ]
(L · M) [ y := V ] = L [ y := V ] · M [ y := V ]
(`zero) [ y := V ] = `zero
(`suc M) [ y := V ] = `suc M [ y := V ]
(case L [zero⇒ M |suc x ⇒ N ]) [ y := V ] with x ≟ y
... | yes _ = case L [ y := V ] [zero⇒ M [ y := V ] |suc x ⇒ N ]
... | no _ = case L [ y := V ] [zero⇒ M [ y := V ] |suc x ⇒ N [ y := V ] ]
(μ x ⇒ N) [ y := V ] with x ≟ y
... | yes _ = μ x ⇒ N
... | no _ = μ x ⇒ N [ y := V ]

infix 4 _—→_

data _—→_ : Term → Term → Set where
  ξ-·₁ : ∀ {L L' M}
    → L —→ L'
    -------
    → L · M —→ L' · M

  ξ-·₂ : ∀ {V M M'}
    → Value V
    → M —→ M'
    -------
    → V · M —→ V · M'

  β-ƛ : ∀ {x N V}
    → Value V
    --------
    → (ƛ x ⇒ N) · V —→ N [ x := V ]

  ξ-suc : ∀ {M M'}
    → M —→ M'
    --------
    → `suc M —→ `suc M'

  ξ-case : ∀ {x L L' M N}
    → L —→ L'
    ---------
    → case L [zero⇒ M |suc x ⇒ N ] —→ case L' [zero⇒ M |suc x ⇒ N ]

  β-zero : ∀ {x M N}
    --------
    → case `zero [zero⇒ M |suc x ⇒ N ] —→ M

  β-suc : ∀ {x V M N}
    → Value V
    ---------
    → case `suc V [zero⇒ M |suc x ⇒ N ] —→ N [ x := V ]

  β-μ : ∀ {x M}
    --------
    → μ x ⇒ M —→ M [ x := μ x ⇒ M ]


infix 2 _—↠_
infix 1 begin_
infixr 2 _—→⟨_⟩_
infix 3 _∎

data _—↠_ : Term → Term → Set where
  _∎ : ∀ M
    -------
    → M —↠ M

  _—→⟨_⟩_ : ∀ L {M N}
    → L —→ M
    → M —↠ N
    --------
    → L —↠ N

begin_ : ∀ {M N}
  → M —↠ N
  --------
  → M —↠ N
begin M—↠N = M—↠N

data _—↠'_ : Term → Term → Set where

  step' : ∀ {M N}
    → M —→ N
    --------
    → M —↠' N

  refl' : ∀ {M}
    -------
    → M —↠' M

  trans' : ∀ {L M N}
    → L —↠' M
    → M —↠' N
    ---------
    → L —↠' N

postulate
  cofuluence : ∀ {L M N}
    → ((L —↠ M) × (L —↠ N))
    -------------------
    → ∃[ P ] ((M —↠ P) × (N —↠ P))

  diamond : ∀ {L M N}
    → ((L —→ M) × (L —→ N))
    ----------------------
    → ∃[ P ] ((M —→ P) × (N —→ P))

postulate
  determinstic : ∀ {L M N}
    → L —→ M
    → L —→ N
    --------
    → M ≡ N

_ : twoᶜ · sucᶜ · `zero —↠ `suc `suc `zero
_ =
  begin
    twoᶜ · sucᶜ · `zero
  —→⟨ ξ-·₁ (β-ƛ V-ƛ) ⟩
    (ƛ "z" ⇒ sucᶜ · (sucᶜ · ` "z")) · `zero
  —→⟨ β-ƛ V-zero ⟩
    sucᶜ · (sucᶜ · `zero)
  —→⟨ ξ-·₂ V-ƛ (β-ƛ V-zero) ⟩
    sucᶜ · `suc `zero
  —→⟨ β-ƛ (V-suc V-zero) ⟩
    `suc (`suc `zero)
  ∎



--------------------------

infixr 7 _⇒_

data Type : Set where
  _⇒_ : Type → Type → Type
  `ℕ : Type

infixl 5 _,_⦂_

data Context : Set where
  ∅ : Context
  _,_⦂_ : Context → Id → Type → Context

infix 4 _∋_⦂_

data _∋_⦂_ : Context → Id → Type → Set where

  Z : ∀ {Γ x A}
    -----------
    → Γ , x ⦂ A ∋ x ⦂ A

  S : ∀ {Γ x y A B}
    → x ≢ y
    → Γ ∋ x ⦂ A
    ----------
    → Γ , y ⦂ B ∋ x ⦂ A

  S' : ∀ {Γ x y A B}
    → {x≢y : False (x ≟ y)}
    → Γ ∋ x ⦂ A
    -----------
    → Γ , y ⦂ B ∋ x ⦂ A

infix  4  _⊢_⦂_

data _⊢_⦂_ : Context → Term → Type → Set where

  -- Axiom
  ⊢` : ∀ {Γ x A}
    → Γ ∋ x ⦂ A
      -----------
    → Γ ⊢ ` x ⦂ A

  -- ⇒-I
  ⊢ƛ : ∀ {Γ x N A B}
    → Γ , x ⦂ A ⊢ N ⦂ B
      -------------------
    → Γ ⊢ ƛ x ⇒ N ⦂ A ⇒ B

  -- ⇒-E
  _·_ : ∀ {Γ L M A B}
    → Γ ⊢ L ⦂ A ⇒ B
    → Γ ⊢ M ⦂ A
      -------------
    → Γ ⊢ L · M ⦂ B

  -- ℕ-I₁
  ⊢zero : ∀ {Γ}
      --------------
    → Γ ⊢ `zero ⦂ `ℕ

  -- ℕ-I₂
  ⊢suc : ∀ {Γ M}
    → Γ ⊢ M ⦂ `ℕ
      ---------------
    → Γ ⊢ `suc M ⦂ `ℕ

  -- ℕ-E
  ⊢case : ∀ {Γ L M x N A}
    → Γ ⊢ L ⦂ `ℕ
    → Γ ⊢ M ⦂ A
    → Γ , x ⦂ `ℕ ⊢ N ⦂ A
      -------------------------------------
    → Γ ⊢ case L [zero⇒ M |suc x ⇒ N ] ⦂ A

  ⊢μ : ∀ {Γ x M A}
    → Γ , x ⦂ A ⊢ M ⦂ A
      -----------------
    → Γ ⊢ μ x ⇒ M ⦂ A
