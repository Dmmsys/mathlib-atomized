/-
Copyright (c) 2020 Fox Thomson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fox Thomson
-/
module

public import Mathlib.Computability.Language
public import Mathlib.Tactic.AdaptationNote

/-!
# Regular Expressions

This file contains the formal definition for regular expressions and basic lemmas. Note these are
regular expressions in terms of formal language theory. Note this is different to regexes used in
computer science such as the POSIX standard.

## TODO

Currently, we do not show that regular expressions and DFAs/NFAs are equivalent.
Multiple competing PRs towards that goal are in review.
See https://leanprover.zulipchat.com/#narrow/channel/287929-mathlib4/topic/Regular.20languages.3A.20the.20review.20queue
-/

@[expose] public section

open List Set

open Computability

universe u

variable {α β γ : Type*}

-- Disable generation of unneeded lemmas which the simpNF linter would complain about.
set_option genSizeOfSpec false in
set_option genInjectivity false in
/--
Inductive type `RegularExpression` / 归纳类型 `RegularExpression`

English:
inductive RegularExpression
  parameters: (α : Type u)
  constructors (6):
    - zero: RegularExpression α
    - epsilon: RegularExpression α
    - char: α -> RegularExpression α
    - plus: RegularExpression α -> RegularExpression α -> RegularExpression α
    - comp: RegularExpression α -> RegularExpression α -> RegularExpression α
    - star: RegularExpression α -> RegularExpression α

中文:
归纳类型 RegularExpression
  参数: (α : 类型u)
  构造子 (6 个):
    - zero: RegularExpression α
    - epsilon: RegularExpression α
    - char: α -> RegularExpression α
    - plus: RegularExpression α -> RegularExpression α -> RegularExpression α
    - comp: RegularExpression α -> RegularExpression α -> RegularExpression α
    - star: RegularExpression α -> RegularExpression α
-/
inductive RegularExpression (α : Type u) : Type u
  | zero : RegularExpression α
  | epsilon : RegularExpression α
  | char : α -> RegularExpression α
  | plus : RegularExpression α -> RegularExpression α -> RegularExpression α
  | comp : RegularExpression α -> RegularExpression α -> RegularExpression α
  | star : RegularExpression α -> RegularExpression α

namespace RegularExpression

variable {a b : α}

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Inhabited (RegularExpression α)
  body: ⟨zero⟩

中文:
实例 :
  签名: Inhabited (RegularExpression α)
  定义体: ⟨zero⟩
-/
instance : Inhabited (RegularExpression α) :=
  ⟨zero⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Add (RegularExpression α)
  body: ⟨plus⟩

中文:
实例 :
  签名: Add (RegularExpression α)
  定义体: ⟨plus⟩
-/
instance : Add (RegularExpression α) :=
  ⟨plus⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Mul (RegularExpression α)
  body: ⟨comp⟩

中文:
实例 :
  签名: Mul (RegularExpression α)
  定义体: ⟨comp⟩
-/
instance : Mul (RegularExpression α) :=
  ⟨comp⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: One (RegularExpression α)
  body: ⟨epsilon⟩

中文:
实例 :
  签名: One (RegularExpression α)
  定义体: ⟨epsilon⟩

Depends on / 依赖: epsilon
-/
instance : One (RegularExpression α) :=
  ⟨epsilon⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Zero (RegularExpression α)
  body: ⟨zero⟩

中文:
实例 :
  签名: Zero (RegularExpression α)
  定义体: ⟨zero⟩
-/
instance : Zero (RegularExpression α) :=
  ⟨zero⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Pow (RegularExpression α) Nat
  body: ⟨fun n r => npowRec r n⟩

@[simp]

中文:
实例 :
  签名: Pow (RegularExpression α) 自然数
  定义体: ⟨fun n r => npowRec r n⟩

@[simp]

Depends on / 依赖: npowRec
-/
instance : Pow (RegularExpression α) Nat :=
  ⟨fun n r => npowRec r n⟩

@[simp]
/--
theorem `zero_def` / 定理 `zero_def`

English:
theorem zero_def
  statement: (zero : RegularExpression α) = 0
  proof: rfl

@[simp]

中文:
定理 zero_def
  结论: (zero : RegularExpression α) = 0
  证明: rfl

@[simp]
-/
theorem zero_def : (zero : RegularExpression α) = 0 :=
  rfl

@[simp]
/--
theorem `one_def` / 定理 `one_def`

English:
theorem one_def
  statement: (epsilon : RegularExpression α) = 1
  proof: rfl

@[simp]

中文:
定理 one_def
  结论: (epsilon : RegularExpression α) = 1
  证明: rfl

@[simp]
-/
theorem one_def : (epsilon : RegularExpression α) = 1 :=
  rfl

@[simp]
/--
theorem `plus_def` / 定理 `plus_def`

English:
theorem plus_def
  given: (P Q : RegularExpression α)
  statement: plus P Q = P + Q
  proof: rfl

@[simp]

中文:
定理 plus_def
  条件: (P Q : RegularExpression α)
  结论: plus P Q = P + Q
  证明: rfl

@[simp]
-/
theorem plus_def (P Q : RegularExpression α) : plus P Q = P + Q :=
  rfl

@[simp]
/--
theorem `comp_def` / 定理 `comp_def`

English:
theorem comp_def
  given: (P Q : RegularExpression α)
  statement: comp P Q = P * Q
  proof: rfl

中文:
定理 comp_def
  条件: (P Q : RegularExpression α)
  结论: comp P Q = P * Q
  证明: rfl
-/
theorem comp_def (P Q : RegularExpression α) : comp P Q = P * Q :=
  rfl

/-- `matches' P` provides a language which contains all strings that `P` matches.

Not named `matches` since that is a reserved word.
-/
@[simp]
/--
Definition of `matches'` / `matches'` 的定义

English:
definition matches'
  signature: : RegularExpression α -> Language α

中文:
定义 matches'
  签名: : RegularExpression α -> Language α
-/
def matches' : RegularExpression α -> Language α
  | 0 => 0
  | 1 => 1
  | char a => {[a]}
  | P + Q => P.matches' + Q.matches'
  | P * Q => P.matches' * Q.matches'
  | star P => P.matches'∗

/--
theorem `matches'_zero` / 定理 `matches'_zero`

English:
theorem matches'_zero
  statement: (0 : RegularExpression α).matches' = 0
  proof: rfl

中文:
定理 matches'_zero
  结论: (0 : RegularExpression α).matches' = 0
  证明: rfl
-/
theorem matches'_zero : (0 : RegularExpression α).matches' = 0 :=
  rfl

/--
theorem `matches'_epsilon` / 定理 `matches'_epsilon`

English:
theorem matches'_epsilon
  statement: (1 : RegularExpression α).matches' = 1
  proof: rfl

中文:
定理 matches'_epsilon
  结论: (1 : RegularExpression α).matches' = 1
  证明: rfl
-/
theorem matches'_epsilon : (1 : RegularExpression α).matches' = 1 :=
  rfl

/--
theorem `matches'_char` / 定理 `matches'_char`

English:
theorem matches'_char
  given: (a : α)
  statement: (char a).matches' = {[a]}
  proof: rfl

中文:
定理 matches'_char
  条件: (a : α)
  结论: (char a).matches' = {[a]}
  证明: rfl
-/
theorem matches'_char (a : α) : (char a).matches' = {[a]} :=
  rfl

/--
theorem `matches'_add` / 定理 `matches'_add`

English:
theorem matches'_add
  given: (P Q : RegularExpression α)
  statement: (P + Q).matches' = P.matches' + Q.matches'
  proof: rfl

中文:
定理 matches'_add
  条件: (P Q : RegularExpression α)
  结论: (P + Q).matches' = P.matches' + Q.matches'
  证明: rfl
-/
theorem matches'_add (P Q : RegularExpression α) : (P + Q).matches' = P.matches' + Q.matches' :=
  rfl

/--
theorem `matches'_mul` / 定理 `matches'_mul`

English:
theorem matches'_mul
  given: (P Q : RegularExpression α)
  statement: (P * Q).matches' = P.matches' * Q.matches'
  proof: rfl

@[simp]

中文:
定理 matches'_mul
  条件: (P Q : RegularExpression α)
  结论: (P * Q).matches' = P.matches' * Q.matches'
  证明: rfl

@[simp]
-/
theorem matches'_mul (P Q : RegularExpression α) : (P * Q).matches' = P.matches' * Q.matches' :=
  rfl

@[simp]
/--
theorem `matches'_pow` / 定理 `matches'_pow`

English:
theorem matches'_pow
  given: (P : RegularExpression α)
  statement: forall n : Nat, (P ^ n).matches' = P.matches' ^ n

中文:
定理 matches'_pow
  条件: (P : RegularExpression α)
  结论: 对任意 n : 自然数, (P ^ n).matches' = P.matches' ^ n
-/
theorem matches'_pow (P : RegularExpression α) : forall n : Nat, (P ^ n).matches' = P.matches' ^ n
  | 0 => matches'_epsilon
| n + 1 => (matches'_mul _ _).trans Eq.trans
      (congrFun (congrArg HMul.hMul (matches'_pow P n)) (matches' P))
      (pow_succ _ n).symm

/--
theorem `matches'_star` / 定理 `matches'_star`

English:
theorem matches'_star
  given: (P : RegularExpression α)
  statement: P.star.matches' = P.matches'∗
  proof: rfl

中文:
定理 matches'_star
  条件: (P : RegularExpression α)
  结论: P.star.matches' = P.matches'∗
  证明: rfl
-/
theorem matches'_star (P : RegularExpression α) : P.star.matches' = P.matches'∗ :=
  rfl

/--
Definition of `matchEpsilon` / `matchEpsilon` 的定义

English:
definition matchEpsilon
  signature: : RegularExpression α -> Bool

中文:
定义 matchEpsilon
  签名: : RegularExpression α -> 布尔
-/
def matchEpsilon : RegularExpression α -> Bool
  | 0 => false
  | 1 => true
  | char _ => false
  | P + Q => P.matchEpsilon || Q.matchEpsilon
  | P * Q => P.matchEpsilon && Q.matchEpsilon
  | star _P => true

section DecidableEq
variable [DecidableEq α]

/--
Definition of `deriv` / `deriv` 的定义

English:
definition deriv
  signature: : RegularExpression α -> α -> RegularExpression α

中文:
定义 deriv
  签名: : RegularExpression α -> α -> RegularExpression α
-/
def deriv : RegularExpression α -> α -> RegularExpression α
  | 0, _ => 0
  | 1, _ => 0
  | char a₁, a₂ => if a₁ = a₂ then 1 else 0
  | P + Q, a => deriv P a + deriv Q a
  | P * Q, a => if P.matchEpsilon then deriv P a * Q + deriv Q a else deriv P a * Q
  | star P, a => deriv P a * star P

@[simp]
/--
theorem `deriv_zero` / 定理 `deriv_zero`

English:
theorem deriv_zero
  given: (a : α)
  statement: deriv 0 a = 0
  proof: rfl

@[simp]

中文:
定理 deriv_zero
  条件: (a : α)
  结论: deriv 0 a = 0
  证明: rfl

@[simp]
-/
theorem deriv_zero (a : α) : deriv 0 a = 0 :=
  rfl

@[simp]
/--
theorem `deriv_one` / 定理 `deriv_one`

English:
theorem deriv_one
  given: (a : α)
  statement: deriv 1 a = 0
  proof: rfl

@[simp]

中文:
定理 deriv_one
  条件: (a : α)
  结论: deriv 1 a = 0
  证明: rfl

@[simp]
-/
theorem deriv_one (a : α) : deriv 1 a = 0 :=
  rfl

@[simp]
/--
theorem `deriv_char_self` / 定理 `deriv_char_self`

English:
theorem deriv_char_self
  given: (a : α)
  statement: deriv (char a) a = 1
  proof: if_pos rfl

@[simp]

中文:
定理 deriv_char_self
  条件: (a : α)
  结论: deriv (char a) a = 1
  证明: if_pos rfl

@[simp]

Depends on / 依赖: if_pos
-/
theorem deriv_char_self (a : α) : deriv (char a) a = 1 :=
  if_pos rfl

@[simp]
/--
theorem `deriv_char_of_ne` / 定理 `deriv_char_of_ne`

English:
theorem deriv_char_of_ne
  given: (h : a != b)
  statement: deriv (char a) b = 0
  proof: if_neg h

@[simp]

中文:
定理 deriv_char_of_ne
  条件: (h : a != b)
  结论: deriv (char a) b = 0
  证明: if_neg h

@[simp]

Depends on / 依赖: if_neg
-/
theorem deriv_char_of_ne (h : a != b) : deriv (char a) b = 0 :=
  if_neg h

@[simp]
/--
theorem `deriv_add` / 定理 `deriv_add`

English:
theorem deriv_add
  given: (P Q : RegularExpression α) (a : α)
  statement: deriv (P + Q) a = deriv P a + deriv Q a
  proof: rfl

@[simp]

中文:
定理 deriv_add
  条件: (P Q : RegularExpression α) (a : α)
  结论: deriv (P + Q) a = deriv P a + deriv Q a
  证明: rfl

@[simp]
-/
theorem deriv_add (P Q : RegularExpression α) (a : α) : deriv (P + Q) a = deriv P a + deriv Q a :=
  rfl

@[simp]
/--
theorem `deriv_star` / 定理 `deriv_star`

English:
theorem deriv_star
  given: (P : RegularExpression α) (a : α)
  statement: deriv P.star a = deriv P a * star P
  proof: rfl

中文:
定理 deriv_star
  条件: (P : RegularExpression α) (a : α)
  结论: deriv P.star a = deriv P a * star P
  证明: rfl
-/
theorem deriv_star (P : RegularExpression α) (a : α) : deriv P.star a = deriv P a * star P :=
  rfl

/--
Definition of `rmatch` / `rmatch` 的定义

English:
definition rmatch
  signature: : RegularExpression α -> List α -> Bool

中文:
定义 rmatch
  签名: : RegularExpression α -> List α -> 布尔
-/
def rmatch : RegularExpression α -> List α -> Bool
  | P, [] => matchEpsilon P
  | P, a :: as => rmatch (P.deriv a) as

@[simp]
/--
theorem `zero_rmatch` / 定理 `zero_rmatch`

English:
theorem zero_rmatch
  given: (x : List α)
  statement: rmatch 0 x = false
  proof: by
  induction x <;> simp [rmatch, matchEpsilon, *]

中文:
定理 zero_rmatch
  条件: (x : List α)
  结论: rmatch 0 x = false
  证明: by
  induction x <;> simp [rmatch, matchEpsilon, *]

Depends on / 依赖: matchEpsilon, rmatch
-/
theorem zero_rmatch (x : List α) : rmatch 0 x = false := by
  induction x <;> simp [rmatch, matchEpsilon, *]

/--
theorem `one_rmatch_iff` / 定理 `one_rmatch_iff`

English:
theorem one_rmatch_iff
  given: (x : List α)
  statement: rmatch 1 x ↔ x = []
  proof: by
  induction x <;> simp [rmatch, matchEpsilon, *]

中文:
定理 one_rmatch_iff
  条件: (x : List α)
  结论: rmatch 1 x ↔ x = []
  证明: by
  induction x <;> simp [rmatch, matchEpsilon, *]

Depends on / 依赖: matchEpsilon, rmatch
-/
theorem one_rmatch_iff (x : List α) : rmatch 1 x ↔ x = [] := by
  induction x <;> simp [rmatch, matchEpsilon, *]

/--
theorem `char_rmatch_iff` / 定理 `char_rmatch_iff`

English:
theorem char_rmatch_iff
  given: (a : α) (x : List α)
  statement: rmatch (char a) x ↔ x = [a]
  proof: by
  rcases x with - | ⟨_, x⟩
  · exact of_decide_eq_true rfl
  · rcases x with - | ⟨head, tail⟩
    · rw [rmatch, deriv, List.singleton_inj]
      split <;> tauto
    · rw [rmatch, rmatch, deriv, cons.injEq]
      split
      · simp_rw [deriv_one, zero_rmatch, reduceCtorEq, and_false]
      · simp_

中文:
定理 char_rmatch_iff
  条件: (a : α) (x : List α)
  结论: rmatch (char a) x ↔ x = [a]
  证明: by
  rcases x with - | ⟨_, x⟩
  · exact of_decide_eq_true rfl
  · rcases x with - | ⟨head, tail⟩
    · rw [rmatch, deriv, List.singleton_inj]
      split <;> tauto
    · rw [rmatch, rmatch, deriv, cons.injEq]
      split
      · simp_rw [deriv_one, zero_rmatch, reduceCtorEq, and_false]
      · simp_

Depends on / 依赖: List.singleton_inj, and_false, cons.injEq, deriv_one, deriv_zero, of_decide_eq_true, reduceCtorEq, rmatch, simp_rw, singleton_inj, zero_rmatch
-/
theorem char_rmatch_iff (a : α) (x : List α) : rmatch (char a) x ↔ x = [a] := by
  rcases x with - | ⟨_, x⟩
  · exact of_decide_eq_true rfl
  · rcases x with - | ⟨head, tail⟩
    · rw [rmatch, deriv, List.singleton_inj]
      split <;> tauto
    · rw [rmatch, rmatch, deriv, cons.injEq]
      split
      · simp_rw [deriv_one, zero_rmatch, reduceCtorEq, and_false]
      · simp_rw [deriv_zero, zero_rmatch, reduceCtorEq, and_false]

/--
theorem `add_rmatch_iff` / 定理 `add_rmatch_iff`

English:
theorem add_rmatch_iff
  given: (P Q : RegularExpression α) (x : List α)
  proof: by
  induction x generalizing P Q with
  | nil => simp only [rmatch, matchEpsilon, Bool.or_eq_true_iff]
  | cons _ _ ih =>
    rw [rmatch]; rw [deriv_add]
    exact ih _ _

中文:
定理 add_rmatch_iff
  条件: (P Q : RegularExpression α) (x : List α)
  证明: by
  induction x generalizing P Q with
  | nil => simp only [rmatch, matchEpsilon, Bool.or_eq_true_iff]
  | cons _ _ ih =>
    rw [rmatch]; rw [deriv_add]
    exact ih _ _

Depends on / 依赖: Bool.or_eq_true_iff, deriv_add, generalizing, matchEpsilon, or_eq_true_iff, rmatch
-/
theorem add_rmatch_iff (P Q : RegularExpression α) (x : List α) :
    (P + Q).rmatch x ↔ P.rmatch x ∨ Q.rmatch x := by
  induction x generalizing P Q with
  | nil => simp only [rmatch, matchEpsilon, Bool.or_eq_true_iff]
  | cons _ _ ih =>
    rw [rmatch]; rw [deriv_add]
    exact ih _ _

/--
theorem `mul_rmatch_iff` / 定理 `mul_rmatch_iff`

English:
theorem mul_rmatch_iff
  given: (P Q : RegularExpression α) (x : List α)
  proof: by
  induction x generalizing P Q with
  | nil =>
    rw [rmatch]; simp only [matchEpsilon]
    constructor
    · intro h
      refine ⟨[], [], rfl, ?_⟩
      rw [rmatch]; rw [rmatch]
      rwa [Bool.and_eq_true_iff] at h
    · rintro ⟨t, u, h₁, h₂⟩
      obtain ⟨rfl, rfl⟩ := List.append_eq_nil_iff.

中文:
定理 mul_rmatch_iff
  条件: (P Q : RegularExpression α) (x : List α)
  证明: by
  induction x generalizing P Q with
  | nil =>
    rw [rmatch]; simp only [matchEpsilon]
    constructor
    · intro h
      refine ⟨[], [], rfl, ?_⟩
      rw [rmatch]; rw [rmatch]
      rwa [Bool.and_eq_true_iff] at h
    · rintro ⟨t, u, h₁, h₂⟩
      obtain ⟨rfl, rfl⟩ := List.append_eq_nil_iff.

Depends on / 依赖: Bool.and_eq_true_iff, List.append_eq_nil_iff, add_rmatch_iff, and_eq_true_iff, append_eq_nil_iff, generalizing, hepsilon, matchEpsilon, repeat, rmatch, split_ifs
-/
theorem mul_rmatch_iff (P Q : RegularExpression α) (x : List α) :
    (P * Q).rmatch x ↔ exists t u : List α, x = t ++ u ∧ P.rmatch t ∧ Q.rmatch u := by
  induction x generalizing P Q with
  | nil =>
    rw [rmatch]; simp only [matchEpsilon]
    constructor
    · intro h
      refine ⟨[], [], rfl, ?_⟩
      rw [rmatch]; rw [rmatch]
      rwa [Bool.and_eq_true_iff] at h
    · rintro ⟨t, u, h₁, h₂⟩
      obtain ⟨rfl, rfl⟩ := List.append_eq_nil_iff.1 h₁.symm
      repeat rw [rmatch] at h₂
      simp [h₂]
  | cons a x ih =>
    rw [rmatch]; simp only [deriv]
    split_ifs with hepsilon
    · rw [add_rmatch_iff, ih]
      constructor
      · rintro (⟨t, u, _⟩ | h)
        · exact ⟨a :: t, u, by tauto⟩
        · exact ⟨[], a :: x, rfl, hepsilon, h⟩
      · rintro ⟨t, u, h, hP, hQ⟩
        rcases t with - | ⟨b, t⟩
        · right
          rw [List.nil_append] at h
          rw [← h] at hQ
          exact hQ
        · left
          rw [List.cons_append]; rw [List.cons_eq_cons] at h
          refine ⟨t, u, h.2, ?_, hQ⟩
          rw [rmatch] at hP
          convert! hP
          exact h.1
    · rw [ih]
      constructor <;> rintro ⟨t, u, h, hP, hQ⟩
      · exact ⟨a :: t, u, by tauto⟩
      · rcases t with - | ⟨b, t⟩
        · contradiction
        · rw [List.cons_append, List.cons_eq_cons] at h
          refine ⟨t, u, h.2, ?_, hQ⟩
          rw [rmatch] at hP
          convert! hP
          exact h.1

/--
theorem `star_rmatch_iff` / 定理 `star_rmatch_iff`

English:
theorem star_rmatch_iff
  given: (P : RegularExpression α)
  proof: fun x => by
    have IH := fun t (_h : List.length t < List.length x) => star_rmatch_iff P t
    clear star_rmatch_iff
    constructor
    · rcases x with - | ⟨a, x⟩
      · intro _h
        use []; dsimp; tauto
      · rw [rmatch, deriv, mul_rmatch_iff]
        rintro ⟨t, u, hs, ht, hu⟩
        hav

中文:
定理 star_rmatch_iff
  条件: (P : RegularExpression α)
  证明: fun x => by
    have IH := fun t (_h : List.length t < List.length x) => star_rmatch_iff P t
    clear star_rmatch_iff
    constructor
    · rcases x with - | ⟨a, x⟩
      · intro _h
        use []; dsimp; tauto
      · rw [rmatch, deriv, mul_rmatch_iff]
        rintro ⟨t, u, hs, ht, hu⟩
        hav

Depends on / 依赖: List.cons, List.length, List.length_append, List.length_cons, length, length_append, length_cons, mul_rmatch_iff, rmatch, star_rmatch_iff, u.length
-/
theorem star_rmatch_iff (P : RegularExpression α) :
    forall x : List α, (star P).rmatch x ↔ exists S : List (List α), x
          = S.flatten ∧ forall t in S, t != [] ∧ P.rmatch t :=
  fun x => by
    have IH := fun t (_h : List.length t < List.length x) => star_rmatch_iff P t
    clear star_rmatch_iff
    constructor
    · rcases x with - | ⟨a, x⟩
      · intro _h
        use []; dsimp; tauto
      · rw [rmatch, deriv, mul_rmatch_iff]
        rintro ⟨t, u, hs, ht, hu⟩
        have hwf : u.length < (List.cons a x).length := by
          rw [hs]; rw [List.length_cons]; rw [List.length_append]
          lia
        rw [IH _ hwf] at hu
        rcases hu with ⟨S', hsum, helem⟩
        use (a :: t) :: S'
        constructor
        · simp [hs, hsum]
        · intro t' ht'
          cases ht' with
          | head ht' =>
            simp only [ne_eq, not_false_iff, true_and, rmatch, reduceCtorEq]
            exact ht
          | tail _ ht' => exact helem t' ht'
    · rintro ⟨S, hsum, helem⟩
      rcases x with - | ⟨a, x⟩
      · rfl
      · rw [rmatch, deriv, mul_rmatch_iff]
        rcases S with - | ⟨t', U⟩
        · exact ⟨[], [], by tauto⟩
        · obtain - | ⟨b, t⟩ := t'
          · simp only [forall_eq_or_imp, List.mem_cons] at helem
            simp only [not_true, Ne, false_and] at helem
          simp only [List.flatten_cons, List.cons_append, List.cons_eq_cons] at hsum
          refine ⟨t, U.flatten, hsum.2, ?_, ?_⟩
          · specialize helem (b :: t) (by simp)
            rw [rmatch] at helem
            convert! helem.2
            exact hsum.1
          · grind
  termination_by t => (P, t.length)

@[simp]
/--
theorem `rmatch_iff_matches'` / 定理 `rmatch_iff_matches'`

English:
theorem rmatch_iff_matches'
  given: (P : RegularExpression α) (x : List α)
  proof: by
  induction P generalizing x with
  | zero =>
    rw [zero_def]; rw [zero_rmatch]
    tauto
  | epsilon =>
    rw [one_def]; rw [one_rmatch_iff]; rw [matches'_epsilon]; rw [Language.mem_one]
  | char =>
    rw [char_rmatch_iff]
    rfl
  | plus _ _ ih₁ ih₂ =>
    rw [plus_def]; rw [add_rmatch_iff

中文:
定理 rmatch_iff_matches'
  条件: (P : RegularExpression α) (x : List α)
  证明: by
  induction P generalizing x with
  | zero =>
    rw [zero_def]; rw [zero_rmatch]
    tauto
  | epsilon =>
    rw [one_def]; rw [one_rmatch_iff]; rw [matches'_epsilon]; rw [Language.mem_one]
  | char =>
    rw [char_rmatch_iff]
    rfl
  | plus _ _ ih₁ ih₂ =>
    rw [plus_def]; rw [add_rmatch_iff

Depends on / 依赖: Language, Language.mem_kstar_iff_exists_nonempty, Language.mem_mul, Language.mem_one, _epsilon, _mul, _star, add_rmatch_iff, and_co, char_rmatch_iff, comp_def, epsilon, generalizing, matches, mem_kstar_iff_exists_nonempty, mem_mul, mem_one, mul_rmatch_iff, one_def, one_rmatch_iff
-/
theorem rmatch_iff_matches' (P : RegularExpression α) (x : List α) :
    P.rmatch x ↔ x in P.matches' := by
  induction P generalizing x with
  | zero =>
    rw [zero_def]; rw [zero_rmatch]
    tauto
  | epsilon =>
    rw [one_def]; rw [one_rmatch_iff]; rw [matches'_epsilon]; rw [Language.mem_one]
  | char =>
    rw [char_rmatch_iff]
    rfl
  | plus _ _ ih₁ ih₂ =>
    rw [plus_def]; rw [add_rmatch_iff]; rw [ih₁]; rw [ih₂]
    rfl
  | comp P Q ih₁ ih₂ =>
    simp only [comp_def, mul_rmatch_iff, matches'_mul, Language.mem_mul, *]
    tauto
  | star _ ih =>
    simp only [star_rmatch_iff, matches'_star, ih, Language.mem_kstar_iff_exists_nonempty, and_comm]

instance (P : RegularExpression α) : DecidablePred (· in P.matches') := fun _ =>
  decidable_of_iff _ (rmatch_iff_matches' _ _)

end DecidableEq

/-- Map the alphabet of a regular expression. -/
@[simp]
/--
Definition of `map` / `map` 的定义

English:
definition map
  signature: (f : α -> β)

中文:
定义 map
  签名: (f : α -> β)
-/
def map (f : α -> β) : RegularExpression α -> RegularExpression β
  | 0 => 0
  | 1 => 1
  | char a => char (f a)
  | R + S => map f R + map f S
  | R * S => map f R * map f S
  | star R => star (map f R)

@[simp]
/--
theorem `map_pow` / 定理 `map_pow`

English:
theorem map_pow
  given: (f : α -> β) (P : RegularExpression α)

中文:
定理 map_pow
  条件: (f : α -> β) (P : RegularExpression α)
-/
protected theorem map_pow (f : α -> β) (P : RegularExpression α) :
    forall n : Nat, map f (P ^ n) = map f P ^ n
  | 0 => by unfold map; rfl
  | n + 1 => (congr_arg (· * map f P) (RegularExpression.map_pow f P n) :)

@[simp]
/--
theorem `map_id` / 定理 `map_id`

English:
theorem map_id
  statement: forall P : RegularExpression α, P.map id = P

中文:
定理 map_id
  结论: 对任意 P : RegularExpression α, P.map id = P
-/
theorem map_id : forall P : RegularExpression α, P.map id = P
  | 0 => rfl
  | 1 => rfl
  | char _ => rfl
  | R + S => by simp_rw [map, map_id]
  | R * S => by simp_rw [map, map_id]
  | star R => by simp_rw [map, map_id]

@[simp]
/--
theorem `map_map` / 定理 `map_map`

English:
theorem map_map
  given: (g : β -> γ) (f : α -> β)
  statement: forall P : RegularExpression α, (P.map f).map g = P.map (g ∘ f)

中文:
定理 map_map
  条件: (g : β -> γ) (f : α -> β)
  结论: 对任意 P : RegularExpression α, (P.map f).map g = P.map (g ∘ f)
-/
theorem map_map (g : β -> γ) (f : α -> β) : forall P : RegularExpression α, (P.map f).map g = P.map (g ∘ f)
  | 0 => rfl
  | 1 => rfl
  | char _ => rfl
  | R + S => by simp only [map, map_map]
  | R * S => by simp only [map, map_map]
  | star R => by simp only [map, map_map]

/-- The language of the map is the map of the language. -/
@[simp]
/--
theorem `matches'_map` / 定理 `matches'_map`

English:
theorem matches'_map
  given: (f : α -> β)

中文:
定理 matches'_map
  条件: (f : α -> β)
-/
theorem matches'_map (f : α -> β) :
    forall P : RegularExpression α, (P.map f).matches' = Language.map f P.matches'
  | 0 => (map_zero _).symm
  | 1 => (map_one _).symm
  | char a => by
    rw [eq_comm]
    exact image_singleton
  | R + S => by simp only [matches'_map, map, matches'_add, map_add]
  | R * S => by simp [matches'_map]
  | star R => by simp [matches'_map]

end RegularExpression
