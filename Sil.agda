-- This is a formal development of ownership added to an augmented SIL language
-- To demonstrate references, the following syntax has been added
-- <stmt> ::= ... | <var> := ref <intexp> (alloc + init; has full ownership)
--                | <var> ::= <intexp> (ref write i.e. *var = value in C)
--                | <var> := !<var> (ref read)
--                | free <var> (release allocated memory)
--                | <var> moveto <var> (e.g. x moveto y moves ownership of memory from x to y)
module Sil where

open import Agda.Builtin.Int using (Int)
open import Data.List
  using
  (List
  ; []; _∷_
  ; sum; map; take; reverse; _++_; drop; any
  )

open import Relation.Binary.PropositionalEquality as Eq using (_≡_; _≢_; refl; sym; trans; cong)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Maybe using (Maybe; nothing; just)
open import Data.Rational using (ℚ ; mkℚ; normalize; 1ℚ; 0ℚ; _≃_)
open import Data.String using (String; _≟_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (_×_; proj₁; proj₂; _,′_)
open import Relation.Nullary using (Dec; yes; no; ¬_)
open import Relation.Nullary.Decidable using (⌊_⌋; False; toWitnessFalse)
open import Relation.Nullary.Negation using (¬?)
open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; step-≡; _∎)

Id : Set
Id = String


-- Syntax of terms.

infix 10 _i
infix  9  `_
infix  8 `-_
infix  8 `not_
infix  8 `ref_
infix  8 !_

infixl 7 _+_
infixl 7 _*_
infixl 7 _and_
infixl 7 _or_
infixl 7 _<_
infixl 7 _>_
infixl 7 _==_

infix  5 `True
infix  5 `False
infix  5 `skip
-- infix  5 `begin_`end
infix  5 `free_
infix  5 _`moveto_
infix  4 _::=_
infix  4 _:=_

data Term : Set where
  `_ : Id → Term
  _i : Int → Term
  `-_ : Term → Term
  _+_ : Term → Term → Term
  _*_ : Term → Term → Term
  _and_ : Term → Term → Term
  _or_ : Term → Term → Term
  _<_ : Term → Term → Term
  _>_ : Term → Term → Term
  _==_ : Term → Term → Term
  `not_ : Term → Term
  `True : Term
  `False : Term
  `ref_ : Term → Term
  !_ : Term → Term

-- Syntax of Statements.
data Stmt : Set

data Stmt where
  `skip : Stmt
  `free_ : Term → Stmt
  _`moveto_ : Term → Term → Stmt
  _:=_ : Term → Term → Stmt
  _::=_ : Term → Term → Stmt
  `begin_`end : List Stmt → Stmt
  `while_`do_ : Term → Stmt → Stmt
  `if_`then_`else_ : Term → Stmt → Stmt → Stmt



-- Syntax of types.

data Type : Set where
  `ℕ : Type  -- integer
  `𝔹 : Type  -- boolean

infixl 5  _,_⦂_

data Context : Set where
  ∅     : Context
  _,_⦂_ : Context → Id → Type → Context


infix  4  _∋_⦂_
infix  4  _∋̌_

-- Define in.

data _∋_⦂_ : Context → Id → Type → Set where

  Z : ∀ {Γ x A}
      ------------------
    → Γ , x ⦂ A ∋ x ⦂ A

  S : ∀ {Γ x y A B}
    → x ≢ y
    → Γ ∋ x ⦂ A
      ------------------
    → Γ , y ⦂ B ∋ x ⦂ A

-- Define belongs to.

data _∋̌_ : Context → Id → Set where

  Ž : ∀ {Γ x A}
      ------------------ axiom
    → Γ , x ⦂ A ∋̌ x

  Š : ∀ {Γ x y A}
    → x ≢ y
    → Γ ∋̌ x
      ------------------
    → Γ , y ⦂ A ∋̌ x


-- The typing judgment for expressions.

infix  4  _⊢_⦂_

data _⊢_⦂_ : Context → Term → Type → Set where

  -- Int type judgements

  -- T_VAR
  ⊢var : ∀ {Γ x A}
    → Γ ∋ x ⦂ A
      ------------
    → Γ ⊢ ` x ⦂ A

  -- T_INT
  ⊢int : ∀ {Γ N}
    -------------
    → Γ ⊢ N i ⦂ `ℕ

  -- T_NEG
  ⊢neg : ∀ {Γ M}
    → Γ ⊢ M ⦂ `ℕ
      -----------
    → Γ ⊢ `- M ⦂ `ℕ

  -- T_INTBINOP (+)
  ⊢+ : ∀ {Γ M₁ M₂}
    → Γ ⊢ M₁ ⦂ `ℕ
    → Γ ⊢ M₂ ⦂ `ℕ
      -----------
    → Γ ⊢ M₁ + M₂ ⦂ `ℕ

  -- T_INTBINOP (*)
  ⊢- : ∀ {Γ M₁ M₂}
    → Γ ⊢ M₁ ⦂ `ℕ
    → Γ ⊢ M₂ ⦂ `ℕ
      -----------
    → Γ ⊢ M₁ * M₂ ⦂ `ℕ

   -- Boolean type judgements

   -- T_NOT
  ⊢¬ : ∀ {Γ B}
    →  Γ ⊢ B ⦂ `𝔹
      ------------------
    →  Γ ⊢ `not B ⦂ `𝔹

   -- T_TRUE
  ⊢T : ∀ {Γ}
     ---------------
    → Γ ⊢ `True ⦂ `𝔹


   -- T_FALSE
  ⊢F : ∀ {Γ}
     ---------------
    → Γ ⊢ `False ⦂ `𝔹

   -- T_BINBOOL_AND
  ⊢∧ : ∀ {Γ B₁ B₂}
    → Γ ⊢ B₁ ⦂ `𝔹
    → Γ ⊢ B₂ ⦂ `𝔹
      -----------
    → Γ ⊢ B₁ and B₂ ⦂ `𝔹

   -- T_BINBOOL_OR
  ⊢∨ : ∀ {Γ B₁ B₂}
    → Γ ⊢ B₁ ⦂ `𝔹
    → Γ ⊢ B₂ ⦂ `𝔹
      -----------
    → Γ ⊢ B₁ or B₂ ⦂ `𝔹

   -- T_CMPOP (<)
  ⊢< : ∀ {Γ M₁ M₂}
    → Γ ⊢ M₁ ⦂ `ℕ
    → Γ ⊢ M₂ ⦂ `ℕ
      -----------
    → Γ ⊢ M₁ < M₂ ⦂ `𝔹

   -- T_CMPOP (>)
  ⊢> : ∀ {Γ M₁ M₂}
    → Γ ⊢ M₁ ⦂ `ℕ
    → Γ ⊢ M₂ ⦂ `ℕ
      -----------
    → Γ ⊢ M₁ > M₂ ⦂ `𝔹


   -- T_CMPOP (==)
  ⊢= : ∀ {Γ M₁ M₂}
    → Γ ⊢ M₁ ⦂ `ℕ
    → Γ ⊢ M₂ ⦂ `ℕ
      -----------
    → Γ ⊢ M₁ == M₂ ⦂ `𝔹


-- Statements typing judgement for SIL
infix  4  _⊢ₛ_

data _⊢ₛ_ : Context → List Stmt → Set where
  -- T_SKIPONLY
  ⊢ₛ§ : ∀ {Γ}
       --------
     → Γ ⊢ₛ `skip ∷ []

  -- T_SKIPREST
  ⊢ₛ§→ : ∀ {Γ L}
    → Γ ⊢ₛ L
      ------
    → Γ ⊢ₛ `skip ∷ L


  -- T_BLOCK
  ⊢ₛB : ∀ {Γ L₁ L₂}
    → Γ ⊢ₛ L₁
    → Γ ⊢ₛ L₂
    --------------
    → Γ ⊢ₛ (`begin L₁ `end) ∷  L₂


  -- T_ASSIGN
  ⊢ₛASS : ∀ {Γ M A L x}
    → Γ ⊢ M ⦂ A
    → ¬ (Γ ∋̌ x)
    → (Γ , x ⦂ A) ⊢ₛ L
    ----------------------
    → Γ ⊢ₛ (` x := M) ∷ L

  -- T_REASSIGN
  ⊢ₛRASS : ∀ {Γ M A L x}
    → Γ ⊢ M ⦂ A
    → Γ ∋ x ⦂ A
    → Γ ⊢ₛ L
    ----------------------
    → Γ ⊢ₛ (` x := M) ∷ L

  -- T_IF
  ⊢ₛIF : ∀ { Γ Q₁ Q₂ L B }
    →  Γ ⊢ B ⦂ `𝔹
    →  Γ ⊢ₛ Q₁ ∷ []
    →  Γ ⊢ₛ Q₂ ∷ []
    →  Γ ⊢ₛ L
    ----------
    →  Γ ⊢ₛ (`if B `then Q₁ `else Q₂) ∷ L

  -- T_READ
  ⊢ₛREAD : ∀ {A Γ L x y}
    → Γ ∋ x ⦂ A
    → (Γ , y ⦂ A) ⊢ₛ L
    ----------------------
    → Γ ⊢ₛ (` y := ! ` x) ∷ L

-- T_MOVETO
  ⊢ₛMOVETO : ∀ {A Γ L x y}
    → (Γ ∋ x ⦂ A)
    → ¬(Γ ∋̌ y)
    → (Γ , y ⦂ A) ⊢ₛ L
    ----------------------
    → Γ ⊢ₛ (` x `moveto ` y) ∷ L


-- Helper definitions for Ownership.

infixl 5  _,_⦂ₚ_

-- define Permission context (Ω).
-- A permission type is Id : Rational Number (ℚ)
-- Rational numbers will help us when borrow is added, which
-- is taking away some permission without ever it reaching 0, e.g. by dividing.
data PermCtx : Set where
  ∅     : PermCtx
  _,_⦂ₚ_ : PermCtx → Id → ℚ → PermCtx

infix  4  _∋ₚ_⦂ₚ_

data _∋ₚ_⦂ₚ_ : PermCtx → Id → ℚ → Set where

  Zₚ : ∀ {Ω x p q}
    → p ≡ q
      ------------------
    → Ω , x ⦂ₚ p ∋ₚ x ⦂ₚ q

  Sₚ : ∀ {Ω x y A B}
    → x ≢ y
    → Ω ∋ₚ x ⦂ₚ A
      ------------------
    → Ω , y ⦂ₚ B ∋ₚ x ⦂ₚ A


-- Ownership Typing judgements for statements
-- I imagine the typechecker will be run twice
-- First, we will run ⊢ₛ to fill up Γ
-- Second, we will use Γ and ⊢ₚ to fill up Ω
-- This typing judgement just passes Γ around,
-- occasionally looking up things but never
-- modifying it.
infix  4  _⊢ₚ_
data _⊢ₚ_ : (PermCtx × Context) → (List Stmt) → Set where

  -- T_REF (ALLOC + INIT)
  ⊢ₚREF : ∀ {Γ Ω L N x}
    → Γ ⊢ N ⦂ `ℕ
    → ¬ (Γ ∋̌ x)
    →((Ω , x ⦂ₚ 1ℚ) ,′  Γ) ⊢ₚ L
    -------------------------------------------------------
    → (Ω ,′  Γ) ⊢ₚ  (` x := `ref N) ∷ L

  ⊢ₚFREE : ∀ {Γ Ω x L}
    → (Γ ∋̌  x)
    → Ω ∋ₚ x ⦂ₚ 1ℚ
    → ((Ω , x ⦂ₚ 0ℚ) ,′ Γ) ⊢ₚ  L
    -------------------------------------
    → (Ω ,′ Γ) ⊢ₚ  (`free ` x) ∷ L

  -- T_SKIPONLY
  ⊢ₚ§ : ∀ {Ω Γ}
       --------
    → (Ω ,′ Γ) ⊢ₚ  `skip ∷ []

  -- T_SKIPREST
  ⊢ₚ§→ : ∀ {Γ Ω L}
    → (Ω ,′ Γ)  ⊢ₚ L
      ------
    → (Ω ,′ Γ) ⊢ₚ `skip ∷ L

  -- T_ASSIGN
  ⊢ₚASS : ∀ {Γ Ω L M A x}
    → Γ ⊢ M ⦂ A
    → (Ω ,′ Γ)  ⊢ₚ L
    ----------------------
    → (Ω ,′ Γ) ⊢ₚ (` x ::= M) ∷ L

  -- T_READ
  ⊢ₚREAD : ∀ {Γ Ω L x y}
    → Γ ∋̌ x
    → (Ω ,′ Γ) ⊢ₚ L
    ----------------------
    → (Ω ,′ Γ) ⊢ₚ (` y := ! ` x) ∷ L

-- T_MOVETO
-- This is a simple version of moveto.
-- We constraint that the new owner must be fresh.
-- This simplifies proofs at the cost of expressiveness.
-- Specifically it restricts passing ownership from a child context
-- (e.g. inside a begin..end block of if statement)
-- to the parent context.
  ⊢ₚMOVETO : ∀ {Γ Ω L x y}
    → (Γ ∋̌ x)
    → ¬ (Γ ∋̌ y)
    → Ω ∋ₚ x ⦂ₚ 1ℚ
    → ((Ω , x ⦂ₚ 0ℚ , y ⦂ₚ 1ℚ) ,′ Γ) ⊢ₚ L
    ----------------------
    → (Ω ,′ Γ) ⊢ₚ (` x `moveto ` y) ∷ L


notin : ∀ {Ω p q x} → ¬ (p ≡ q) → ¬ (Ω , x ⦂ₚ p ∋ₚ x ⦂ₚ q)
notin p≢q (Zₚ x) = p≢q x
notin p≢q (Sₚ x b) = x refl

zeronotone : ¬  0ℚ ≡ 1ℚ
zeronotone = λ ()

-- Lookup is injective (a helper for what follows)
∋ₚ-injective : ∀ {Ω x p q} → Ω ∋ₚ x ⦂ₚ p → Ω ∋ₚ x ⦂ₚ q → p ≡ q
∋ₚ-injective (Zₚ x) (Zₚ x₁) rewrite sym x = x₁
∋ₚ-injective (Zₚ x) (Sₚ x₁ eq) = ⊥-elim (x₁ refl)
∋ₚ-injective (Sₚ x ep) (Zₚ x₁) = ⊥-elim (x refl)
∋ₚ-injective (Sₚ x ep) (Sₚ x₁ eq) = ∋ₚ-injective ep eq

-- (Another helper for what follows)
¬∋ₚ-injective : ∀ {Ω x y p q} → p ≢ q → Ω ∋ₚ x ⦂ₚ p → Ω ∋ₚ y ⦂ₚ q → x ≢ y
¬∋ₚ-injective p≢q (Zₚ x) (Zₚ x₁) x≡y = p≢q (trans (sym x) x₁)
¬∋ₚ-injective p≢q (Zₚ x) (Sₚ x₁ ey) x≡y = ⊥-elim (x₁ (sym x≡y))
¬∋ₚ-injective p≢q (Sₚ x ex) (Zₚ x₁) x≡y = ⊥-elim (x x≡y)
¬∋ₚ-injective p≢q (Sₚ x ex) (Sₚ x₁ ey) x≡y = ¬∋ₚ-injective p≢q ex ey x≡y

data _∈ₗ_ :  Stmt → (List Stmt) → Set where

  Z : ∀ {x L}
      ------------------
    → x ∈ₗ (x ∷ L)

  S : ∀ {x y L}
    → x ≢ y
    → x ∈ₗ L
      ------------------
    → x ∈ₗ (y ∷ L)


-- sanity check
nofree : ∀ {Ω Γ L x}
 → ¬ (((Ω , x ⦂ₚ 0ℚ) ,′ Γ) ⊢ₚ (`free ` x) ∷ L)
nofree (⊢ₚFREE x x₁ x₂) = notin zeronotone x₁

-- helper functions to prove double free is caught

-- equality is symmetric for rationals
rat-eq-sym : ∀ (p q : ℚ) → p ≡ q → q ≡ p
rat-eq-sym p q x = sym x

-- equality is transitive for rationals
rat-eq-trans : ∀ (p q r : ℚ) → p ≡ q → q ≡ r → p ≡ r
rat-eq-trans p q r  p≡q q≡r = trans p≡q q≡r

yesin : ∀ {Ω p q x y} → x ≢ y  → (Ω ∋ₚ x ⦂ₚ p) → (Ω , y ⦂ₚ q ∋ₚ x ⦂ₚ p)
yesin {.(_ , x ⦂ₚ _)} {p} {q} {x} {y} x≢y (Zₚ x₁) = Sₚ x≢y (Zₚ x₁)
yesin {.(_ , _ ⦂ₚ _)} {p} {q} {x} {y} x≢y (Sₚ x₁ xin) = Sₚ x≢y (yesin x₁ xin)


diffid : ∀ {Γ x y} → Γ ∋̌ x → ¬ (Γ ∋̌ y) → x ≢ y
diffid {.(_ , x ⦂ _)} {x} {.x} Ž ¬ey refl = ¬ey Ž
diffid {.(_ , _ ⦂ _)} {x} {.x} (Š x₁ ex) ¬ey refl = ¬ey (Š x₁ ex)


diffid1 : ∀ {x y} → ` x ≢ ` y →  x ≢  y
diffid1 x refl = x refl

diffid2 : ∀ {x y} →  x ≡ y →  ` x ≡ ` y
diffid2 {x} {.x} refl = refl

difffree : ∀ {x y} → `free ` x ≢ `free ` y → x ≢ y
difffree edf refl = edf refl

-- helper for double free is caught.
-- We prove inductively the following
-- Base case: L = free x :: [] where x has zero permissions and typechecks is absurd (⊥)
-- Inductive case: L = y :: L if ⊢-no-free-without-perm on L is absurd (⊥) then
-- adding a statement y in front retains the absurdity (⊥)
-- We use case analysis for all possible y to prove this.
⊢-no-free-without-perm : ∀ {Γ Ω L x}
  → (Γ ∋̌ x)
  → (Ω ,′ Γ) ⊢ₚ L
  → Ω ∋ₚ x ⦂ₚ 0ℚ
  ----------------------
  →  ¬( (`free ` x) ∈ₗ L)

⊢-no-free-without-perm xexists (⊢ₚFREE x x₁ l) ¬permx Z = zeronotone (∋ₚ-injective ¬permx x₁)
⊢-no-free-without-perm xexists (⊢ₚREF x₂ x₃ l) ¬permx (S x x₁) =
  ⊢-no-free-without-perm xexists l (yesin (diffid xexists x₃) ¬permx) x₁
⊢-no-free-without-perm xexists (⊢ₚFREE x₂ x₃ l) ¬permx (S x x₁) =
  ⊢-no-free-without-perm xexists l (yesin (difffree x) ¬permx) x₁
⊢-no-free-without-perm xexists (⊢ₚ§→ l) ¬permx (S x x₁) =
  ⊢-no-free-without-perm xexists l ¬permx x₁
⊢-no-free-without-perm xexists (⊢ₚASS x₂ l) ¬permx (S x x₁) = ⊢-no-free-without-perm xexists l ¬permx x₁
⊢-no-free-without-perm xexists (⊢ₚREAD x₂ l) ¬permx (S x x₁) = ⊢-no-free-without-perm xexists l ¬permx x₁
⊢-no-free-without-perm xexists (⊢ₚMOVETO x₂ x₃ x₄ l) ¬permx (S x x₁) =
  ⊢-no-free-without-perm xexists l (
    yesin (diffid xexists x₃) (
      yesin (¬∋ₚ-injective zeronotone ¬permx x₄) ¬permx)) x₁

-- This is our main result
-- A free x will only typecheck if no free x is within the rest of the program.
⊢no-double-free : ∀ {Γ Ω L x q}
  → ((Ω , x ⦂ₚ q) ,′ Γ) ⊢ₚ (`free ` x) ∷ L
 ------------------------------------------------------------------------------
  → ¬ ( (`free ` x) ∈ₗ L)
⊢no-double-free (⊢ₚFREE x x₁ ef) l = ⊢-no-free-without-perm x ef (Zₚ refl) l
