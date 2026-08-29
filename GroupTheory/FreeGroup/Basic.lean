/-
Copyright (c) 2018 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import Mathlib.Algebra.Group.Pi.Basic
public import Mathlib.Algebra.Group.Subgroup.Ker
public import Mathlib.Data.List.Chain
public import Mathlib.Algebra.Group.Int.Defs
public import Mathlib.Algebra.BigOperators.Group.List.Basic
public import Mathlib.Algebra.Group.Nat.Defs
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Free groups

This file defines free groups over a type. Furthermore, it is shown that the free group construction
is an instance of a monad. For the result that `FreeGroup` is the left adjoint to the forgetful
functor from groups to types, see `Mathlib/Algebra/Category/Grp/Adjunctions.lean`.

## Main definitions

* `FreeGroup`/`FreeAddGroup`: the free group (resp. free additive group) associated to a type
  `α` defined as the words over `a : α × Bool` modulo the relation `a * x * x⁻¹ * b = a * b`.
* `FreeGroup.mk`/`FreeAddGroup.mk`: the canonical quotient map `List (α × Bool) → FreeGroup α`.
* `FreeGroup.of`/`FreeAddGroup.of`: the canonical injection `α → FreeGroup α`.
* `FreeGroup.lift f`/`FreeAddGroup.lift`: the canonical group homomorphism `FreeGroup α →* G`
  given a group `G` and a function `f : α → G`.

## Main statements

* `FreeGroup.Red.church_rosser`/`FreeAddGroup.Red.church_rosser`: The Church-Rosser theorem for word
  reduction (also known as Newman's diamond lemma).
* `FreeGroup.freeGroupUnitEquivInt`: The free group over the one-point type
  is isomorphic to the integers.
* The free group construction is an instance of a monad.

## Implementation details

First we introduce the one step reduction relation `FreeGroup.Red.Step`:
`w * x * x⁻¹ * v ~> w * v`, its reflexive transitive closure `FreeGroup.Red.trans`
and prove that its join is an equivalence relation. Then we introduce `FreeGroup α` as a quotient
over `FreeGroup.Red.Step`.

For the additive version we introduce the same relation under a different name so that we can
distinguish the quotient types more easily.


## Tags

free group, Newman's diamond lemma, Church-Rosser theorem
-/

@[expose] public section

open Relation
open scoped List

universe u v w

variable {α : Type u}

attribute [local simp] List.append_eq_has_append

/- Ensure that `@[to_additive]` uses the right namespace before the definition of `FreeGroup`. -/
insert_to_additive_translation FreeGroup FreeAddGroup

/--
Inductive type `FreeAddGroup.Red.Step` / 归纳类型 `FreeAddGroup.Red.Step`

English:
inductive FreeAddGroup.Red.Step
  parameters: : List (α × Bool) -> List (α × Bool) -> Prop
  constructors (1):
    - not: {L₁ L₂ x b} : FreeAddGroup.Red.Step (L₁ ++ (x, b) :: (x, not b) :: L₂) (L₁ ++ L₂)

中文:
归纳类型 自由加法群.Red.Step
  参数: : 列表 (α × 布尔值) -> 列表 (α × 布尔值) -> 命题
  构造子 (1 个):
    - not: {L₁ L₂ x b} : 自由加法群.Red.Step (L₁ ++ (x, b) :: (x, not b) :: L₂) (L₁ ++ L₂)
-/
inductive FreeAddGroup.Red.Step : List (α × Bool) -> List (α × Bool) -> Prop
  | not {L₁ L₂ x b} : FreeAddGroup.Red.Step (L₁ ++ (x, b) :: (x, not b) :: L₂) (L₁ ++ L₂)

attribute [simp] FreeAddGroup.Red.Step.not

/-- Reduction step for the multiplicative free group relation: `w * x * x⁻¹ * v ~> w * v` -/
@[to_additive]
/--
Inductive type `FreeGroup.Red.Step` / 归纳类型 `FreeGroup.Red.Step`

English:
inductive FreeGroup.Red.Step
  parameters: : List (α × Bool) -> List (α × Bool) -> Prop
  constructors (1):
    - not: {L₁ L₂ x b} : FreeGroup.Red.Step (L₁ ++ (x, b) :: (x, not b) :: L₂) (L₁ ++ L₂)

中文:
归纳类型 自由群.Red.Step
  参数: : 列表 (α × 布尔值) -> 列表 (α × 布尔值) -> 命题
  构造子 (1 个):
    - not: {L₁ L₂ x b} : 自由群.Red.Step (L₁ ++ (x, b) :: (x, not b) :: L₂) (L₁ ++ L₂)
-/
inductive FreeGroup.Red.Step : List (α × Bool) -> List (α × Bool) -> Prop
  | not {L₁ L₂ x b} : FreeGroup.Red.Step (L₁ ++ (x, b) :: (x, not b) :: L₂) (L₁ ++ L₂)

attribute [simp] FreeGroup.Red.Step.not

namespace FreeGroup

variable {L L₁ L₂ L₃ L₄ : List (α × Bool)}

/-- Reflexive-transitive closure of `Red.Step` -/
@[to_additive /-- Reflexive-transitive closure of `Red.Step` -/]
/--
Definition of `Red` / `Red` 的定义

English:
definition Red
  signature: : List (α × Bool) -> List (α × Bool) -> Prop
  body: ReflTransGen Red.Step

@[to_additive (attr := refl)]

中文:
定义 Red
  签名: : 列表 (α × 布尔值) -> 列表 (α × 布尔值) -> 命题
  定义体: ReflTransGen Red.Step

@[to_additive (attr := refl)]

Depends on / 依赖: Red.Step, ReflTransGen
-/
def Red : List (α × Bool) -> List (α × Bool) -> Prop :=
  ReflTransGen Red.Step

@[to_additive (attr := refl)]
/--
theorem `Red.refl` / 定理 `Red.refl`

English:
theorem Red.refl
  statement: Red L L
  proof: ReflTransGen.refl

@[to_additive (attr := trans)]

中文:
定理 Red.refl
  结论: Red L L
  证明: ReflTransGen.refl

@[to_additive (attr := trans)]

Depends on / 依赖: ReflTransGen, ReflTransGen.refl
-/
theorem Red.refl : Red L L :=
  ReflTransGen.refl

@[to_additive (attr := trans)]
/--
theorem `Red.trans` / 定理 `Red.trans`

English:
theorem Red.trans
  statement: Red L₁ L₂ -> Red L₂ L₃ -> Red L₁ L₃
  proof: ReflTransGen.trans

中文:
定理 Red.trans
  结论: Red L₁ L₂ -> Red L₂ L₃ -> Red L₁ L₃
  证明: ReflTransGen.trans

Depends on / 依赖: ReflTransGen, ReflTransGen.trans
-/
theorem Red.trans : Red L₁ L₂ -> Red L₂ L₃ -> Red L₁ L₃ :=
  ReflTransGen.trans

namespace Red

/-- Predicate asserting that the word `w₁` can be reduced to `w₂` in one step, i.e. there are words
`w₃ w₄` and letter `x` such that `w₁ = w₃xx⁻¹w₄` and `w₂ = w₃w₄` -/
@[to_additive /-- Predicate asserting that the word `w₁` can be reduced to `w₂` in one step, i.e.
there are words `w₃ w₄` and letter `x` such that `w₁ = w₃ + x + (-x) + w₄` and `w₂ = w₃w₄` -/]
/--
theorem `Step.length` / 定理 `Step.length`

English:
theorem Step.length
  statement: forall {L₁ L₂ : List (α × Bool)}, Step L₁ L₂ -> L₂.length + 2 = L₁.length

中文:
定理 Step.length
  结论: 对任意 {L₁ L₂ : 列表 (α × 布尔值)}, Step L₁ L₂ -> L₂.length + 2 = L₁.length
-/
theorem Step.length : forall {L₁ L₂ : List (α × Bool)}, Step L₁ L₂ -> L₂.length + 2 = L₁.length
  | _, _, @Red.Step.not _ L1 L2 x b => by rw [List.length_append, List.length_append]; rfl

@[to_additive (attr := simp)]
/--
theorem `Step.not_rev` / 定理 `Step.not_rev`

English:
theorem Step.not_rev
  given: {x b}
  statement: Step (L₁ ++ (x, !b) :: (x, b) :: L₂) (L₁ ++ L₂)
  proof: by
  cases b <;> exact Step.not

@[to_additive (attr := simp)]

中文:
定理 Step.not_rev
  条件: {x b}
  结论: Step (L₁ ++ (x, !b) :: (x, b) :: L₂) (L₁ ++ L₂)
  证明: by
  cases b <;> exact Step.not

@[to_additive (attr := simp)]

Depends on / 依赖: Step.not
-/
theorem Step.not_rev {x b} : Step (L₁ ++ (x, !b) :: (x, b) :: L₂) (L₁ ++ L₂) := by
  cases b <;> exact Step.not

@[to_additive (attr := simp)]
/--
theorem `Step.cons_not` / 定理 `Step.cons_not`

English:
theorem Step.cons_not
  given: {x b}
  statement: Red.Step ((x, b) :: (x, !b) :: L) L
  proof: @Step.not _ [] _ _ _

@[to_additive (attr := simp)]

中文:
定理 Step.cons_not
  条件: {x b}
  结论: Red.Step ((x, b) :: (x, !b) :: L) L
  证明: @Step.not _ [] _ _ _

@[to_additive (attr := simp)]

Depends on / 依赖: Step.not
-/
theorem Step.cons_not {x b} : Red.Step ((x, b) :: (x, !b) :: L) L :=
  @Step.not _ [] _ _ _

@[to_additive (attr := simp)]
/--
theorem `Step.cons_not_rev` / 定理 `Step.cons_not_rev`

English:
theorem Step.cons_not_rev
  given: {x b}
  statement: Red.Step ((x, !b) :: (x, b) :: L) L
  proof: @Red.Step.not_rev _ [] _ _ _

@[to_additive]

中文:
定理 Step.cons_not_rev
  条件: {x b}
  结论: Red.Step ((x, !b) :: (x, b) :: L) L
  证明: @Red.Step.not_rev _ [] _ _ _

@[to_additive]

Depends on / 依赖: Red.Step.not_rev, not_rev
-/
theorem Step.cons_not_rev {x b} : Red.Step ((x, !b) :: (x, b) :: L) L :=
  @Red.Step.not_rev _ [] _ _ _

@[to_additive]
/--
theorem `Step.append_left` / 定理 `Step.append_left`

English:
theorem Step.append_left
  statement: forall {L₁ L₂ L₃ : List (α × Bool)}, Step L₂ L₃ -> Step (L₁ ++ L₂) (L₁ ++ L₃)

中文:
定理 Step.append_left
  结论: 对任意 {L₁ L₂ L₃ : 列表 (α × 布尔值)}, Step L₂ L₃ -> Step (L₁ ++ L₂) (L₁ ++ L₃)
-/
theorem Step.append_left : forall {L₁ L₂ L₃ : List (α × Bool)}, Step L₂ L₃ -> Step (L₁ ++ L₂) (L₁ ++ L₃)
  | _, _, _, Red.Step.not => by rw [← List.append_assoc, ← List.append_assoc]; constructor

@[to_additive]
/--
theorem `Step.cons` / 定理 `Step.cons`

English:
theorem Step.cons
  given: {x} (H : Red.Step L₁ L₂)
  statement: Red.Step (x :: L₁) (x :: L₂)
  proof: @Step.append_left _ [x] _ _ H

@[to_additive]

中文:
定理 Step.cons
  条件: {x} (H : Red.Step L₁ L₂)
  结论: Red.Step (x :: L₁) (x :: L₂)
  证明: @Step.append_left _ [x] _ _ H

@[to_additive]

Depends on / 依赖: Step.append_left, append_left
-/
theorem Step.cons {x} (H : Red.Step L₁ L₂) : Red.Step (x :: L₁) (x :: L₂) :=
  @Step.append_left _ [x] _ _ H

@[to_additive]
/--
theorem `Step.append_right` / 定理 `Step.append_right`

English:
theorem Step.append_right
  statement: forall {L₁ L₂ L₃ : List (α × Bool)}, Step L₁ L₂ -> Step (L₁ ++ L₃) (L₂ ++ L₃)

中文:
定理 Step.append_right
  结论: 对任意 {L₁ L₂ L₃ : 列表 (α × 布尔值)}, Step L₁ L₂ -> Step (L₁ ++ L₃) (L₂ ++ L₃)
-/
theorem Step.append_right : forall {L₁ L₂ L₃ : List (α × Bool)}, Step L₁ L₂ -> Step (L₁ ++ L₃) (L₂ ++ L₃)
  | _, _, _, Red.Step.not => by simp

@[to_additive]
/--
theorem `not_step_nil` / 定理 `not_step_nil`

English:
theorem not_step_nil
  statement: ¬Step [] L
  proof: by
  generalize h' : [] = L'
  intro h
  rcases h with - | ⟨L₁, L₂⟩
  simp at h'

@[to_additive]

中文:
定理 not_step_nil
  结论: ¬Step [] L
  证明: by
  generalize h' : [] = L'
  intro h
  rcases h with - | ⟨L₁, L₂⟩
  simp at h'

@[to_additive]

Depends on / 依赖: Fintype, Fintype.linearCombination_apply, MulEquiv, MulEquiv.trans_apply, generalize, linearCombination_apply, trans_apply
-/
theorem not_step_nil : ¬Step [] L := by
  generalize h' : [] = L'
  intro h
  rcases h with - | ⟨L₁, L₂⟩
  simp at h'

@[to_additive]
/--
theorem `Step.cons_left_iff` / 定理 `Step.cons_left_iff`

English:
theorem Step.cons_left_iff
  given: {a : α} {b : Bool}
  proof: by
  constructor
  · generalize hL : ((a, b) :: L₁ : List _) = L
    rintro @⟨_ | ⟨p, s'⟩, e, a', b'⟩ <;> simp_all
  · rintro (⟨L, h, rfl⟩ | rfl)
    · exact Step.cons h
    · exact Step.cons_not

@[to_additive]

中文:
定理 Step.cons_left_iff
  条件: {a : α} {b : 布尔值}
  证明: by
  constructor
  · generalize hL : ((a, b) :: L₁ : List _) = L
    rintro @⟨_ | ⟨p, s'⟩, e, a', b'⟩ <;> simp_all
  · rintro (⟨L, h, rfl⟩ | rfl)
    · exact Step.cons h
    · exact Step.cons_not

@[to_additive]

Depends on / 依赖: Step.cons, Step.cons_not, cons_not, generalize
-/
theorem Step.cons_left_iff {a : α} {b : Bool} :
    Step ((a, b) :: L₁) L₂ ↔ (exists L, Step L₁ L ∧ L₂ = (a, b) :: L) ∨ L₁ = (a, ! b) :: L₂ := by
  constructor
  · generalize hL : ((a, b) :: L₁ : List _) = L
    rintro @⟨_ | ⟨p, s'⟩, e, a', b'⟩ <;> simp_all
  · rintro (⟨L, h, rfl⟩ | rfl)
    · exact Step.cons h
    · exact Step.cons_not

@[to_additive]
/--
theorem `not_step_singleton` / 定理 `not_step_singleton`

English:
theorem not_step_singleton
  statement: forall {p : α × Bool}, ¬Step [p] L

中文:
定理 not_step_singleton
  结论: 对任意 {p : α × 布尔值}, ¬Step [p] L
-/
theorem not_step_singleton : forall {p : α × Bool}, ¬Step [p] L
  | (a, b) => by simp [Step.cons_left_iff, not_step_nil]

@[to_additive]
/--
theorem `Step.cons_cons_iff` / 定理 `Step.cons_cons_iff`

English:
theorem Step.cons_cons_iff
  statement: forall {p : α × Bool}, Step (p :: L₁) (p :: L₂) ↔ Step L₁ L₂
  proof: by
  simp +contextual [Step.cons_left_iff, iff_def, or_imp]

@[to_additive]

中文:
定理 Step.cons_cons_iff
  结论: 对任意 {p : α × 布尔值}, Step (p :: L₁) (p :: L₂) ↔ Step L₁ L₂
  证明: by
  simp +contextual [Step.cons_left_iff, iff_def, or_imp]

@[to_additive]

Depends on / 依赖: Step.cons_left_iff, cons_left_iff, contextual, iff_def, or_imp
-/
theorem Step.cons_cons_iff : forall {p : α × Bool}, Step (p :: L₁) (p :: L₂) ↔ Step L₁ L₂ := by
  simp +contextual [Step.cons_left_iff, iff_def, or_imp]

@[to_additive]
/--
theorem `Step.append_left_iff` / 定理 `Step.append_left_iff`

English:
theorem Step.append_left_iff
  statement: forall L, Step (L ++ L₁) (L ++ L₂) ↔ Step L₁ L₂

中文:
定理 Step.append_left_iff
  结论: 对任意 L, Step (L ++ L₁) (L ++ L₂) ↔ Step L₁ L₂
-/
theorem Step.append_left_iff : forall L, Step (L ++ L₁) (L ++ L₂) ↔ Step L₁ L₂
  | [] => by simp
  | p :: l => by simp [Step.append_left_iff l, Step.cons_cons_iff]

@[to_additive]
/--
theorem `Step.diamond_aux` / 定理 `Step.diamond_aux`

English:
theorem Step.diamond_aux
  proof: List.cons.inj H
    match Step.diamond_aux H2 with
| Or.inl H3 => Or.inl by simp [H1, H3]
    | Or.inr ⟨L₅, H3, H4⟩ => Or.inr ⟨_, Step.cons H3, by simpa [H1] using Step.cons H4⟩

@[to_additive]

中文:
定理 Step.diamond_aux
  证明: List.cons.inj H
    match Step.diamond_aux H2 with
| Or.inl H3 => Or.inl by simp [H1, H3]
    | Or.inr ⟨L₅, H3, H4⟩ => Or.inr ⟨_, Step.cons H3, by simpa [H1] using Step.cons H4⟩

@[to_additive]

Depends on / 依赖: List.cons.inj
-/
theorem Step.diamond_aux :
    forall {L₁ L₂ L₃ L₄ : List (α × Bool)} {x1 b1 x2 b2},
      L₁ ++ (x1, b1) :: (x1, !b1) :: L₂ = L₃ ++ (x2, b2) :: (x2, !b2) :: L₄ ->
        L₁ ++ L₂ = L₃ ++ L₄ ∨ exists L₅, Red.Step (L₁ ++ L₂) L₅ ∧ Red.Step (L₃ ++ L₄) L₅
  | [], _, [], _, _, _, _, _, H => by injections; subst_vars; simp
  | [], _, [(x3, b3)], _, _, _, _, _, H => by injections; subst_vars; simp
  | [(x3, b3)], _, [], _, _, _, _, _, H => by injections; subst_vars; simp
  | [], _, (x3, b3) :: (x4, b4) :: tl, _, _, _, _, _, H => by
    injections; subst_vars; right; exact ⟨_, Red.Step.not, Red.Step.cons_not⟩
  | (x3, b3) :: (x4, b4) :: tl, _, [], _, _, _, _, _, H => by
    injections; subst_vars; right; simpa using ⟨_, Red.Step.cons_not, Red.Step.not⟩
  | (x3, b3) :: tl, _, (x4, b4) :: tl2, _, _, _, _, _, H =>
    let ⟨H1, H2⟩ := List.cons.inj H
    match Step.diamond_aux H2 with
| Or.inl H3 => Or.inl by simp [H1, H3]
    | Or.inr ⟨L₅, H3, H4⟩ => Or.inr ⟨_, Step.cons H3, by simpa [H1] using Step.cons H4⟩

@[to_additive]
/--
theorem `Step.diamond` / 定理 `Step.diamond`

English:
theorem Step.diamond

中文:
定理 Step.diamond
-/
theorem Step.diamond :
    forall {L₁ L₂ L₃ L₄ : List (α × Bool)},
      Red.Step L₁ L₃ -> Red.Step L₂ L₄ -> L₁ = L₂ -> L₃ = L₄ ∨ exists L₅, Red.Step L₃ L₅ ∧ Red.Step L₄ L₅
  | _, _, _, _, Red.Step.not, Red.Step.not, H => Step.diamond_aux H

@[to_additive]
/--
theorem `Step.to_red` / 定理 `Step.to_red`

English:
theorem Step.to_red
  statement: Step L₁ L₂ -> Red L₁ L₂
  proof: ReflTransGen.single

中文:
定理 Step.to_red
  结论: Step L₁ L₂ -> Red L₁ L₂
  证明: ReflTransGen.single

Depends on / 依赖: ReflTransGen, ReflTransGen.single, single
-/
theorem Step.to_red : Step L₁ L₂ -> Red L₁ L₂ :=
  ReflTransGen.single

/-- **Church-Rosser theorem** for word reduction: If `w1 w2 w3` are words such that `w1` reduces
to `w2` and `w3` respectively, then there is a word `w4` such that `w2` and `w3` reduce to `w4`
respectively. This is also known as Newman's diamond lemma. -/
@[to_additive
  /-- **Church-Rosser theorem** for word reduction: If `w1 w2 w3` are words such that `w1` reduces
  to `w2` and `w3` respectively, then there is a word `w4` such that `w2` and `w3` reduce to `w4`
  respectively. This is also known as Newman's diamond lemma. -/]
/--
theorem `church_rosser` / 定理 `church_rosser`

English:
theorem church_rosser
  statement: Red L₁ L₂ -> Red L₁ L₃ -> Join Red L₂ L₃
  proof: Relation.church_rosser fun _ b c hab hac =>
    match b, c, Red.Step.diamond hab hac rfl with
    | b, _, Or.inl rfl => ⟨b, by rfl, by rfl⟩
    | _, _, Or.inr ⟨d, hbd, hcd⟩ => ⟨d, ReflGen.single hbd, hcd.to_red⟩

@[to_additive]

中文:
定理 church_rosser
  结论: Red L₁ L₂ -> Red L₁ L₃ -> 并 Red L₂ L₃
  证明: Relation.church_rosser fun _ b c hab hac =>
    match b, c, Red.Step.diamond hab hac rfl with
    | b, _, Or.inl rfl => ⟨b, by rfl, by rfl⟩
    | _, _, Or.inr ⟨d, hbd, hcd⟩ => ⟨d, ReflGen.single hbd, hcd.to_red⟩

@[to_additive]

Depends on / 依赖: Or.inl, Or.inr, Red.Step.diamond, ReflGen, ReflGen.single, Relation, Relation.church_rosser, church_rosser, diamond, hcd.to_red, single, to_red
-/
theorem church_rosser : Red L₁ L₂ -> Red L₁ L₃ -> Join Red L₂ L₃ :=
  Relation.church_rosser fun _ b c hab hac =>
    match b, c, Red.Step.diamond hab hac rfl with
    | b, _, Or.inl rfl => ⟨b, by rfl, by rfl⟩
    | _, _, Or.inr ⟨d, hbd, hcd⟩ => ⟨d, ReflGen.single hbd, hcd.to_red⟩

@[to_additive]
/--
theorem `cons_cons` / 定理 `cons_cons`

English:
theorem cons_cons
  given: {p}
  statement: Red L₁ L₂ -> Red (p :: L₁) (p :: L₂)
  proof: ReflTransGen.lift (List.cons p) (fun _ _ => Step.cons) L₁ L₂

@[to_additive]

中文:
定理 cons_cons
  条件: {p}
  结论: Red L₁ L₂ -> Red (p :: L₁) (p :: L₂)
  证明: ReflTransGen.lift (List.cons p) (fun _ _ => Step.cons) L₁ L₂

@[to_additive]

Depends on / 依赖: List.cons, ReflTransGen, ReflTransGen.lift, Step.cons
-/
theorem cons_cons {p} : Red L₁ L₂ -> Red (p :: L₁) (p :: L₂) :=
  ReflTransGen.lift (List.cons p) (fun _ _ => Step.cons) L₁ L₂

@[to_additive]
/--
theorem `cons_cons_iff` / 定理 `cons_cons_iff`

English:
theorem cons_cons_iff
  given: (p)
  statement: Red (p :: L₁) (p :: L₂) ↔ Red L₁ L₂
  proof: Iff.intro
    (by
      generalize eq₁ : (p :: L₁ : List _) = LL₁
      generalize eq₂ : (p :: L₂ : List _) = LL₂
      intro h
      induction h using Relation.ReflTransGen.head_induction_on generalizing L₁ L₂ with
      | refl =>
        subst_vars
        cases eq₂
        constructor
      | hea

中文:
定理 cons_cons_iff
  条件: (p)
  结论: Red (p :: L₁) (p :: L₂) ↔ Red L₁ L₂
  证明: Iff.intro
    (by
      generalize eq₁ : (p :: L₁ : List _) = LL₁
      generalize eq₂ : (p :: L₂ : List _) = LL₂
      intro h
      induction h using Relation.ReflTransGen.head_induction_on generalizing L₁ L₂ with
      | refl =>
        subst_vars
        cases eq₂
        constructor
      | hea

Depends on / 依赖: Iff.intro, ReflTransGen, Relation, Relation.ReflTransGen.head_induction_on, Step.cons_left_iff, Step.cons_not_rev, cons_cons, cons_left_iff, cons_not_rev, generalize, generalizing, head_induction_on
-/
theorem cons_cons_iff (p) : Red (p :: L₁) (p :: L₂) ↔ Red L₁ L₂ :=
  Iff.intro
    (by
      generalize eq₁ : (p :: L₁ : List _) = LL₁
      generalize eq₂ : (p :: L₂ : List _) = LL₂
      intro h
      induction h using Relation.ReflTransGen.head_induction_on generalizing L₁ L₂ with
      | refl =>
        subst_vars
        cases eq₂
        constructor
      | head h₁₂ h ih =>
        subst_vars
        obtain ⟨a, b⟩ := p
        rw [Step.cons_left_iff] at h₁₂
        rcases h₁₂ with (⟨L, h₁₂, rfl⟩ | rfl)
        · exact (ih rfl rfl).head h₁₂
        · exact (cons_cons h).tail Step.cons_not_rev)
    cons_cons

@[to_additive]
/--
theorem `append_append_left_iff` / 定理 `append_append_left_iff`

English:
theorem append_append_left_iff
  statement: forall L, Red (L ++ L₁) (L ++ L₂) ↔ Red L₁ L₂

中文:
定理 append_append_left_iff
  结论: 对任意 L, Red (L ++ L₁) (L ++ L₂) ↔ Red L₁ L₂
-/
theorem append_append_left_iff : forall L, Red (L ++ L₁) (L ++ L₂) ↔ Red L₁ L₂
  | [] => Iff.rfl
  | p :: L => by simp [append_append_left_iff L, cons_cons_iff]

@[to_additive]
/--
theorem `append_append` / 定理 `append_append`

English:
theorem append_append
  given: (h₁ : Red L₁ L₃) (h₂ : Red L₂ L₄)
  statement: Red (L₁ ++ L₂) (L₃ ++ L₄)
  proof: (h₁.lift (fun L => L ++ L₂) fun _ _ => Step.append_right).trans ((append_append_left_iff _).2 h₂)

@[to_additive]

中文:
定理 append_append
  条件: (h₁ : Red L₁ L₃) (h₂ : Red L₂ L₄)
  结论: Red (L₁ ++ L₂) (L₃ ++ L₄)
  证明: (h₁.lift (fun L => L ++ L₂) fun _ _ => Step.append_right).trans ((append_append_left_iff _).2 h₂)

@[to_additive]

Depends on / 依赖: Step.append_right, append_append_left_iff, append_right
-/
theorem append_append (h₁ : Red L₁ L₃) (h₂ : Red L₂ L₄) : Red (L₁ ++ L₂) (L₃ ++ L₄) :=
  (h₁.lift (fun L => L ++ L₂) fun _ _ => Step.append_right).trans ((append_append_left_iff _).2 h₂)

@[to_additive]
/--
theorem `to_append_iff` / 定理 `to_append_iff`

English:
theorem to_append_iff
  statement: Red L (L₁ ++ L₂) ↔ exists L₃ L₄, L = L₃ ++ L₄ ∧ Red L₃ L₁ ∧ Red L₄ L₂
  proof: Iff.intro
    (by
      generalize eq : L₁ ++ L₂ = L₁₂
      intro h
      induction h generalizing L₁ L₂ with
      | refl => exact ⟨_, _, eq.symm, by rfl, by rfl⟩
      | tail hLL' h ih =>
        obtain @⟨s, e, a, b⟩ := h
        rcases List.append_eq_append_iff.1 eq with (⟨s', rfl, rfl⟩ | ⟨e', r

中文:
定理 to_append_iff
  结论: Red L (L₁ ++ L₂) ↔ 存在 L₃ L₄, L = L₃ ++ L₄ ∧ Red L₃ L₁ ∧ Red L₄ L₂
  证明: Iff.intro
    (by
      generalize eq : L₁ ++ L₂ = L₁₂
      intro h
      induction h generalizing L₁ L₂ with
      | refl => exact ⟨_, _, eq.symm, by rfl, by rfl⟩
      | tail hLL' h ih =>
        obtain @⟨s, e, a, b⟩ := h
        rcases List.append_eq_append_iff.1 eq with (⟨s', rfl, rfl⟩ | ⟨e', r

Depends on / 依赖: Iff.intro, List.append_eq_append_iff, Step.not, append_eq_append_iff, eq.symm, generalize, generalizing
-/
theorem to_append_iff : Red L (L₁ ++ L₂) ↔ exists L₃ L₄, L = L₃ ++ L₄ ∧ Red L₃ L₁ ∧ Red L₄ L₂ :=
  Iff.intro
    (by
      generalize eq : L₁ ++ L₂ = L₁₂
      intro h
      induction h generalizing L₁ L₂ with
      | refl => exact ⟨_, _, eq.symm, by rfl, by rfl⟩
      | tail hLL' h ih =>
        obtain @⟨s, e, a, b⟩ := h
        rcases List.append_eq_append_iff.1 eq with (⟨s', rfl, rfl⟩ | ⟨e', rfl, rfl⟩)
        · have : L₁ ++ (s' ++ (a, b) :: (a, not b) :: e) =
            L₁ ++ s' ++ (a, b) :: (a, not b) :: e := by simp
          rcases ih this with ⟨w₁, w₂, rfl, h₁, h₂⟩
          exact ⟨w₁, w₂, rfl, h₁, h₂.tail Step.not⟩
        · have : s ++ (a, b) :: (a, not b) :: e' ++ L₂ =
            s ++ (a, b) :: (a, not b) :: (e' ++ L₂) := by simp
          rcases ih this with ⟨w₁, w₂, rfl, h₁, h₂⟩
          exact ⟨w₁, w₂, rfl, h₁.tail Step.not, h₂⟩)
    fun ⟨_, _, Eq, h₃, h₄⟩ => Eq.symm ▸ append_append h₃ h₄

/-- The empty word `[]` only reduces to itself. -/
@[to_additive /-- The empty word `[]` only reduces to itself. -/]
/--
theorem `nil_iff` / 定理 `nil_iff`

English:
theorem nil_iff
  statement: Red [] L ↔ L = []
  proof: reflTransGen_iff_eq fun _ => Red.not_step_nil

中文:
定理 nil_iff
  结论: Red [] L ↔ L = []
  证明: reflTransGen_iff_eq fun _ => Red.not_step_nil

Depends on / 依赖: Red.not_step_nil, not_step_nil, reflTransGen_iff_eq
-/
theorem nil_iff : Red [] L ↔ L = [] :=
  reflTransGen_iff_eq fun _ => Red.not_step_nil

/-- A letter only reduces to itself. -/
@[to_additive /-- A letter only reduces to itself. -/]
/--
theorem `singleton_iff` / 定理 `singleton_iff`

English:
theorem singleton_iff
  given: {x}
  statement: Red [x] L₁ ↔ L₁ = [x]
  proof: reflTransGen_iff_eq fun _ => not_step_singleton

中文:
定理 singleton_iff
  条件: {x}
  结论: Red [x] L₁ ↔ L₁ = [x]
  证明: reflTransGen_iff_eq fun _ => not_step_singleton

Depends on / 依赖: not_step_singleton, reflTransGen_iff_eq
-/
theorem singleton_iff {x} : Red [x] L₁ ↔ L₁ = [x] :=
  reflTransGen_iff_eq fun _ => not_step_singleton

/-- If `x` is a letter and `w` is a word such that `xw` reduces to the empty word, then `w` reduces
to `x⁻¹` -/
@[to_additive
  /-- If `x` is a letter and `w` is a word such that `x + w` reduces to the empty word, then `w`
  reduces to `-x`. -/]
/--
theorem `cons_nil_iff_singleton` / 定理 `cons_nil_iff_singleton`

English:
theorem cons_nil_iff_singleton
  given: {x b}
  statement: Red ((x, b) :: L) [] ↔ Red L [(x, not b)]
  proof: Iff.intro
    (fun h => by
      have h₁ : Red ((x, not b) :: (x, b) :: L) [(x, not b)] := cons_cons h
      have h₂ : Red ((x, not b) :: (x, b) :: L) L := ReflTransGen.single Step.cons_not_rev
      let ⟨L', h₁, h₂⟩ := church_rosser h₁ h₂
      rw [singleton_iff] at h₁
      subst L'
      assumpti

中文:
定理 cons_nil_iff_singleton
  条件: {x b}
  结论: Red ((x, b) :: L) [] ↔ Red L [(x, not b)]
  证明: Iff.intro
    (fun h => by
      have h₁ : Red ((x, not b) :: (x, b) :: L) [(x, not b)] := cons_cons h
      have h₂ : Red ((x, not b) :: (x, b) :: L) L := ReflTransGen.single Step.cons_not_rev
      let ⟨L', h₁, h₂⟩ := church_rosser h₁ h₂
      rw [singleton_iff] at h₁
      subst L'
      assumpti

Depends on / 依赖: Iff.intro, ReflTransGen, ReflTransGen.single, Step.cons_not, Step.cons_not_rev, church_rosser, cons_cons, cons_not, cons_not_rev, single, singleton_iff
-/
theorem cons_nil_iff_singleton {x b} : Red ((x, b) :: L) [] ↔ Red L [(x, not b)] :=
  Iff.intro
    (fun h => by
      have h₁ : Red ((x, not b) :: (x, b) :: L) [(x, not b)] := cons_cons h
      have h₂ : Red ((x, not b) :: (x, b) :: L) L := ReflTransGen.single Step.cons_not_rev
      let ⟨L', h₁, h₂⟩ := church_rosser h₁ h₂
      rw [singleton_iff] at h₁
      subst L'
      assumption)
    fun h => (cons_cons h).tail Step.cons_not

@[to_additive]
/--
theorem `red_iff_irreducible` / 定理 `red_iff_irreducible`

English:
theorem red_iff_irreducible
  given: {x1 b1 x2 b2} (h : (x1, b1) != (x2, b2))
  proof: by
  apply reflTransGen_iff_eq
  generalize eq : [(x1, not b1), (x2, b2)] = L'
  intro L h'
  cases h'
  simp only [List.cons_eq_append_iff, List.cons.injEq, Prod.mk.injEq, and_false,
    List.nil_eq_append_iff, exists_const, or_self, or_false, List.cons_ne_nil] at eq
  rcases eq with ⟨rfl, ⟨rfl, rf

中文:
定理 red_iff_irreducible
  条件: {x1 b1 x2 b2} (h : (x1, b1) != (x2, b2))
  证明: by
  apply reflTransGen_iff_eq
  generalize eq : [(x1, not b1), (x2, b2)] = L'
  intro L h'
  cases h'
  simp only [List.cons_eq_append_iff, List.cons.injEq, Prod.mk.injEq, and_false,
    List.nil_eq_append_iff, exists_const, or_self, or_false, List.cons_ne_nil] at eq
  rcases eq with ⟨rfl, ⟨rfl, rf

Depends on / 依赖: List.cons.injEq, List.cons_eq_append_iff, List.cons_ne_nil, List.nil_eq_append_iff, Prod.mk.injEq, and_false, cons_eq_append_iff, cons_ne_nil, exists_const, generalize, nil_eq_append_iff, or_false, or_self, reflTransGen_iff_eq
-/
theorem red_iff_irreducible {x1 b1 x2 b2} (h : (x1, b1) != (x2, b2)) :
    Red [(x1, !b1), (x2, b2)] L ↔ L = [(x1, !b1), (x2, b2)] := by
  apply reflTransGen_iff_eq
  generalize eq : [(x1, not b1), (x2, b2)] = L'
  intro L h'
  cases h'
  simp only [List.cons_eq_append_iff, List.cons.injEq, Prod.mk.injEq, and_false,
    List.nil_eq_append_iff, exists_const, or_self, or_false, List.cons_ne_nil] at eq
  rcases eq with ⟨rfl, ⟨rfl, rfl⟩, ⟨rfl, rfl⟩, rfl⟩
  simp at h

/-- If `x` and `y` are distinct letters and `w₁ w₂` are words such that `xw₁` reduces to `yw₂`, then
`w₁` reduces to `x⁻¹yw₂`. -/
@[to_additive /-- If `x` and `y` are distinct letters and `w₁ w₂` are words such that `x + w₁`
reduces to `y + w₂`, then `w₁` reduces to `-x + y + w₂`. -/]
/--
theorem `inv_of_red_of_ne` / 定理 `inv_of_red_of_ne`

English:
theorem inv_of_red_of_ne
  statement: {x1 b1 x2 b2} (H1 : (x1, b1) != (x2, b2))
  proof: by
  have : Red ((x1, b1) :: L₁) ([(x2, b2)] ++ L₂) := H2
  rcases to_append_iff.1 this with ⟨_ | ⟨p, L₃⟩, L₄, eq, h₁, h₂⟩
  · simp [nil_iff] at h₁
  · cases eq
    change Red (L₃ ++ L₄) ([(x1, not b1), (x2, b2)] ++ L₂)
    apply append_append _ h₂
    have h₁ : Red ((x1, not b1) :: (x1, b1) :: L₃) 

中文:
定理 inv_of_red_of_ne
  结论: {x1 b1 x2 b2} (H1 : (x1, b1) != (x2, b2))
  证明: by
  have : Red ((x1, b1) :: L₁) ([(x2, b2)] ++ L₂) := H2
  rcases to_append_iff.1 this with ⟨_ | ⟨p, L₃⟩, L₄, eq, h₁, h₂⟩
  · simp [nil_iff] at h₁
  · cases eq
    change Red (L₃ ++ L₄) ([(x1, not b1), (x2, b2)] ++ L₂)
    apply append_append _ h₂
    have h₁ : Red ((x1, not b1) :: (x1, b1) :: L₃) 

Depends on / 依赖: Step.cons_not_rev.to_red, append_append, church_rosser, cons_cons, cons_not_rev, nil_iff, red_iff_irreducible, to_append_iff, to_red
-/
theorem inv_of_red_of_ne {x1 b1 x2 b2} (H1 : (x1, b1) != (x2, b2))
    (H2 : Red ((x1, b1) :: L₁) ((x2, b2) :: L₂)) : Red L₁ ((x1, not b1) :: (x2, b2) :: L₂) := by
  have : Red ((x1, b1) :: L₁) ([(x2, b2)] ++ L₂) := H2
  rcases to_append_iff.1 this with ⟨_ | ⟨p, L₃⟩, L₄, eq, h₁, h₂⟩
  · simp [nil_iff] at h₁
  · cases eq
    change Red (L₃ ++ L₄) ([(x1, not b1), (x2, b2)] ++ L₂)
    apply append_append _ h₂
    have h₁ : Red ((x1, not b1) :: (x1, b1) :: L₃) [(x1, not b1), (x2, b2)] := cons_cons h₁
    have h₂ : Red ((x1, not b1) :: (x1, b1) :: L₃) L₃ := Step.cons_not_rev.to_red
    rcases church_rosser h₁ h₂ with ⟨L', h₁, h₂⟩
    rw [red_iff_irreducible H1] at h₁
    rwa [h₁] at h₂

open List -- for <+ notation

@[to_additive]
/--
theorem `Step.sublist` / 定理 `Step.sublist`

English:
theorem Step.sublist
  given: (H : Red.Step L₁ L₂)
  statement: L₂ <+ L₁
  proof: by
  cases H; simp

中文:
定理 Step.sublist
  条件: (H : Red.Step L₁ L₂)
  结论: L₂ <+ L₁
  证明: by
  cases H; simp
-/
theorem Step.sublist (H : Red.Step L₁ L₂) : L₂ <+ L₁ := by
  cases H; simp

/-- If `w₁ w₂` are words such that `w₁` reduces to `w₂`, then `w₂` is a sublist of `w₁`. -/
@[to_additive
/-- If `w₁ w₂` are words such that `w₁` reduces to `w₂`, then `w₂` is a sublist of `w₁`. -/]
/--
theorem `sublist` / 定理 `sublist`

English:
theorem sublist
  statement: Red L₁ L₂ -> L₂ <+ L₁
  proof: @reflTransGen_le_of_le _ (fun a b => b <+ a) _ ⟨List.Sublist.refl⟩
    ⟨fun _a _b _c hab hbc => List.Sublist.trans hbc hab⟩ (fun _ _ => Red.Step.sublist) L₁ L₂

@[to_additive]

中文:
定理 sublist
  结论: Red L₁ L₂ -> L₂ <+ L₁
  证明: @reflTransGen_le_of_le _ (fun a b => b <+ a) _ ⟨List.Sublist.refl⟩
    ⟨fun _a _b _c hab hbc => List.Sublist.trans hbc hab⟩ (fun _ _ => Red.Step.sublist) L₁ L₂

@[to_additive]
-/
protected theorem sublist : Red L₁ L₂ -> L₂ <+ L₁ :=
  @reflTransGen_le_of_le _ (fun a b => b <+ a) _ ⟨List.Sublist.refl⟩
    ⟨fun _a _b _c hab hbc => List.Sublist.trans hbc hab⟩ (fun _ _ => Red.Step.sublist) L₁ L₂

@[to_additive]
/--
theorem `length_le` / 定理 `length_le`

English:
theorem length_le
  given: (h : Red L₁ L₂)
  statement: L₂.length <= L₁.length
  proof: h.sublist.length_le

@[to_additive (attr := deprecated "Should not be needed." (since := "2026-04-10"))]

中文:
定理 length_le
  条件: (h : Red L₁ L₂)
  结论: L₂.length <= L₁.length
  证明: h.sublist.length_le

@[to_additive (attr := deprecated "Should not be needed." (since := "2026-04-10"))]

Depends on / 依赖: h.sublist.length_le, length_le, sublist
-/
theorem length_le (h : Red L₁ L₂) : L₂.length <= L₁.length :=
  h.sublist.length_le

@[to_additive (attr := deprecated "Should not be needed." (since := "2026-04-10"))]
/--
theorem `sizeof_of_step` / 定理 `sizeof_of_step`

English:
theorem sizeof_of_step
  statement: forall {L₁ L₂ : List (α × Bool)},

中文:
定理 sizeof_of_step
  结论: 对任意 {L₁ L₂ : 列表 (α × 布尔值)},
-/
theorem sizeof_of_step : forall {L₁ L₂ : List (α × Bool)},
    Step L₁ L₂ -> sizeOf L₂ < sizeOf L₁
  | _, _, @Step.not _ L1 L2 x b => by
    induction L1 with
    | nil =>
      rw [nil_append]; rw [nil_append]; rw [cons.sizeOf_spec]; rw [cons.sizeOf_spec]
      lia
    | cons hd tl ih =>
      dsimp
      exact Nat.add_lt_add_left ih _

@[to_additive]
/--
theorem `length` / 定理 `length`

English:
theorem length
  given: (h : Red L₁ L₂)
  statement: exists n, L₁.length = L₂.length + 2 * n
  proof: by
  induction h with
  | refl => exact ⟨0, rfl⟩
  | tail _h₁₂ h₂₃ ih =>
    rcases ih with ⟨n, eq⟩
    exists 1 + n
    simp [Nat.mul_add, eq, (Step.length h₂₃).symm, add_assoc]

@[to_additive]

中文:
定理 length
  条件: (h : Red L₁ L₂)
  结论: 存在 n, L₁.length = L₂.length + 2 * n
  证明: by
  induction h with
  | refl => exact ⟨0, rfl⟩
  | tail _h₁₂ h₂₃ ih =>
    rcases ih with ⟨n, eq⟩
    exists 1 + n
    simp [Nat.mul_add, eq, (Step.length h₂₃).symm, add_assoc]

@[to_additive]

Depends on / 依赖: Nat.mul_add, Step.length, add_assoc, length, mul_add
-/
theorem length (h : Red L₁ L₂) : exists n, L₁.length = L₂.length + 2 * n := by
  induction h with
  | refl => exact ⟨0, rfl⟩
  | tail _h₁₂ h₂₃ ih =>
    rcases ih with ⟨n, eq⟩
    exists 1 + n
    simp [Nat.mul_add, eq, (Step.length h₂₃).symm, add_assoc]

@[to_additive]
/--
theorem `antisymm` / 定理 `antisymm`

English:
theorem antisymm
  given: (h₁₂ : Red L₁ L₂) (h₂₁ : Red L₂ L₁)
  statement: L₁ = L₂
  proof: h₂₁.sublist.antisymm h₁₂.sublist

中文:
定理 antisymm
  条件: (h₁₂ : Red L₁ L₂) (h₂₁ : Red L₂ L₁)
  结论: L₁ = L₂
  证明: h₂₁.sublist.antisymm h₁₂.sublist

Depends on / 依赖: antisymm, sublist, sublist.antisymm
-/
theorem antisymm (h₁₂ : Red L₁ L₂) (h₂₁ : Red L₂ L₁) : L₁ = L₂ :=
  h₂₁.sublist.antisymm h₁₂.sublist

end Red

@[to_additive]
/--
theorem `equivalence_join_red` / 定理 `equivalence_join_red`

English:
theorem equivalence_join_red
  statement: Equivalence (Join (@Red α))
  proof: equivalence_join_reflTransGen fun _ b c hab hac =>
    match b, c, Red.Step.diamond hab hac rfl with
    | b, _, Or.inl rfl => ⟨b, by rfl, by rfl⟩
    | _, _, Or.inr ⟨d, hbd, hcd⟩ => ⟨d, ReflGen.single hbd, ReflTransGen.single hcd⟩

@[to_additive]

中文:
定理 equivalence_join_red
  结论: 等价 (并 (@Red α))
  证明: equivalence_join_reflTransGen fun _ b c hab hac =>
    match b, c, Red.Step.diamond hab hac rfl with
    | b, _, Or.inl rfl => ⟨b, by rfl, by rfl⟩
    | _, _, Or.inr ⟨d, hbd, hcd⟩ => ⟨d, ReflGen.single hbd, ReflTransGen.single hcd⟩

@[to_additive]

Depends on / 依赖: Or.inl, Or.inr, Red.Step.diamond, ReflGen, ReflGen.single, ReflTransGen, ReflTransGen.single, diamond, equivalence_join_reflTransGen, single
-/
theorem equivalence_join_red : Equivalence (Join (@Red α)) :=
  equivalence_join_reflTransGen fun _ b c hab hac =>
    match b, c, Red.Step.diamond hab hac rfl with
    | b, _, Or.inl rfl => ⟨b, by rfl, by rfl⟩
    | _, _, Or.inr ⟨d, hbd, hcd⟩ => ⟨d, ReflGen.single hbd, ReflTransGen.single hcd⟩

@[to_additive]
/--
theorem `join_red_of_step` / 定理 `join_red_of_step`

English:
theorem join_red_of_step
  given: (h : Red.Step L₁ L₂)
  statement: Join Red L₁ L₂
  proof: by
  unfold Red
  exact le_join_of_refl L₁ L₂ h.to_red

@[to_additive]

中文:
定理 join_red_of_step
  条件: (h : Red.Step L₁ L₂)
  结论: 并 Red L₁ L₂
  证明: by
  unfold Red
  exact le_join_of_refl L₁ L₂ h.to_red

@[to_additive]

Depends on / 依赖: h.to_red, le_join_of_refl, to_red
-/
theorem join_red_of_step (h : Red.Step L₁ L₂) : Join Red L₁ L₂ := by
  unfold Red
  exact le_join_of_refl L₁ L₂ h.to_red

@[to_additive]
/--
theorem `eqvGen_step_iff_join_red` / 定理 `eqvGen_step_iff_join_red`

English:
theorem eqvGen_step_iff_join_red
  statement: EqvGen Red.Step L₁ L₂ ↔ Join Red L₁ L₂
  proof: Iff.intro
    (fun h =>
      have : EqvGen (Join Red) L₁ L₂ := h.mono fun _ _ => join_red_of_step
      equivalence_join_red.eqvGen_iff.1 this)
    (join_le_of_equivalence_of_le (Relation.EqvGen.is_equivalence _)
      (reflTransGen_le_of_equivalence_of_le (Relation.EqvGen.is_equivalence _) EqvGen.

中文:
定理 eqvGen_step_iff_join_red
  结论: EqvGen Red.Step L₁ L₂ ↔ 并 Red L₁ L₂
  证明: Iff.intro
    (fun h =>
      have : EqvGen (Join Red) L₁ L₂ := h.mono fun _ _ => join_red_of_step
      equivalence_join_red.eqvGen_iff.1 this)
    (join_le_of_equivalence_of_le (Relation.EqvGen.is_equivalence _)
      (reflTransGen_le_of_equivalence_of_le (Relation.EqvGen.is_equivalence _) EqvGen.

Depends on / 依赖: EqvGen, EqvGen.rel, Iff.intro, Relation, Relation.EqvGen.is_equivalence, equivalence_join_red, equivalence_join_red.eqvGen_iff, eqvGen_iff, h.mono, is_equivalence, join_le_of_equivalence_of_le, join_red_of_step, reflTransGen_le_of_equivalence_of_le
-/
theorem eqvGen_step_iff_join_red : EqvGen Red.Step L₁ L₂ ↔ Join Red L₁ L₂ :=
  Iff.intro
    (fun h =>
      have : EqvGen (Join Red) L₁ L₂ := h.mono fun _ _ => join_red_of_step
      equivalence_join_red.eqvGen_iff.1 this)
    (join_le_of_equivalence_of_le (Relation.EqvGen.is_equivalence _)
      (reflTransGen_le_of_equivalence_of_le (Relation.EqvGen.is_equivalence _) EqvGen.rel) L₁ L₂)

/-! ### Reduced words -/

/-- Predicate asserting that the word `L` admits no reduction steps, i.e., no two neighboring
elements of the word cancel. -/
@[to_additive /-- Predicate asserting the word `L` admits no reduction steps,
i.e., no two neighboring elements of the word cancel. -/]
/--
Definition of `IsReduced` / `IsReduced` 的定义

English:
definition IsReduced
  signature: (L : List (α × Bool))
  body: L.IsChain fun a b => a.1 = b.1 -> a.2 = b.2

中文:
定义 是既约
  签名: (L : 列表 (α × 布尔值))
  定义体: L.IsChain fun a b => a.1 = b.1 -> a.2 = b.2

Depends on / 依赖: IsChain, L.IsChain
-/
def IsReduced (L : List (α × Bool)) : Prop := L.IsChain fun a b => a.1 = b.1 -> a.2 = b.2

section IsReduced

open List

@[to_additive (attr := simp)]
/--
theorem `IsReduced.nil` / 定理 `IsReduced.nil`

English:
theorem IsReduced.nil
  statement: IsReduced ([] : List (α × Bool))
  proof: isChain_nil

@[to_additive (attr := simp)]

中文:
定理 是既约.nil
  结论: 是既约 ([] : 列表 (α × 布尔值))
  证明: isChain_nil

@[to_additive (attr := simp)]

Depends on / 依赖: isChain_nil
-/
theorem IsReduced.nil : IsReduced ([] : List (α × Bool)) := isChain_nil

@[to_additive (attr := simp)]
/--
theorem `IsReduced.singleton` / 定理 `IsReduced.singleton`

English:
theorem IsReduced.singleton
  given: {a : α × Bool}
  statement: IsReduced [a]
  proof: isChain_singleton a

@[to_additive (attr := simp)]

中文:
定理 是既约.singleton
  条件: {a : α × 布尔值}
  结论: 是既约 [a]
  证明: isChain_singleton a

@[to_additive (attr := simp)]

Depends on / 依赖: isChain_singleton
-/
theorem IsReduced.singleton {a : α × Bool} : IsReduced [a] := isChain_singleton a

@[to_additive (attr := simp)]
/--
theorem `isReduced_cons_cons` / 定理 `isReduced_cons_cons`

English:
theorem isReduced_cons_cons
  given: {a b : (α × Bool)}
  proof: isChain_cons_cons

@[to_additive]

中文:
定理 isReduced_cons_cons
  条件: {a b : (α × 布尔值)}
  证明: isChain_cons_cons

@[to_additive]

Depends on / 依赖: isChain_cons_cons
-/
theorem isReduced_cons_cons {a b : (α × Bool)} :
    IsReduced (a :: b :: L) ↔ (a.1 = b.1 -> a.2 = b.2) ∧ IsReduced (b :: L) := isChain_cons_cons

@[to_additive]
/--
theorem `IsReduced.not_step` / 定理 `IsReduced.not_step`

English:
theorem IsReduced.not_step
  given: (h : IsReduced L₁)
  statement: ¬ Red.Step L₁ L₂
  proof: fun step => by
  induction step
  simp [IsReduced] at h

@[to_additive]

中文:
定理 是既约.not_step
  条件: (h : 是既约 L₁)
  结论: ¬ Red.Step L₁ L₂
  证明: fun step => by
  induction step
  simp [IsReduced] at h

@[to_additive]

Depends on / 依赖: IsReduced
-/
theorem IsReduced.not_step (h : IsReduced L₁) : ¬ Red.Step L₁ L₂ := fun step => by
  induction step
  simp [IsReduced] at h

@[to_additive]
/--
lemma `IsReduced.of_forall_not_step` / 引理 `IsReduced.of_forall_not_step`

English:
lemma IsReduced.of_forall_not_step

中文:
引理 是既约.of_对任意_not_step
-/
lemma IsReduced.of_forall_not_step :
    forall {L₁ : List (α × Bool)}, (forall L₂, ¬ Red.Step L₁ L₂) -> IsReduced L₁
  | [], _ => .nil
  | [a], _ => .singleton
  | (a₁, b₁) :: (a₂, b₂) :: L₁, hL₁ => by
    rw [isReduced_cons_cons]
    refine ⟨?_, .of_forall_not_step fun L₂ step => hL₁ _ step.cons⟩
    rintro rfl
    symm
    rw [← Bool.ne_not]
    rintro rfl
exact hL₁ L₁ .not (L₁ := [])

@[to_additive]
/--
theorem `isReduced_iff_not_step` / 定理 `isReduced_iff_not_step`

English:
theorem isReduced_iff_not_step
  statement: IsReduced L₁ ↔ forall L₂, ¬ Red.Step L₁ L₂ where
  proof: h.not_step
  mpr := .of_forall_not_step

@[to_additive]

中文:
定理 isReduced_iff_not_step
  结论: 是既约 L₁ ↔ 对任意 L₂, ¬ Red.Step L₁ L₂ where
  证明: h.not_step
  mpr := .of_forall_not_step

@[to_additive]

Depends on / 依赖: h.not_step, not_step
-/
theorem isReduced_iff_not_step : IsReduced L₁ ↔ forall L₂, ¬ Red.Step L₁ L₂ where
  mp h _ := h.not_step
  mpr := .of_forall_not_step

@[to_additive]
/--
theorem `IsReduced.red_iff_eq` / 定理 `IsReduced.red_iff_eq`

English:
theorem IsReduced.red_iff_eq
  given: (h : IsReduced L₁)
  statement: Red L₁ L₂ ↔ L₂ = L₁
  proof: Relation.reflTransGen_iff_eq fun _ => h.not_step

@[to_additive]

中文:
定理 是既约.red_iff_eq
  条件: (h : 是既约 L₁)
  结论: Red L₁ L₂ ↔ L₂ = L₁
  证明: Relation.reflTransGen_iff_eq fun _ => h.not_step

@[to_additive]

Depends on / 依赖: Relation, Relation.reflTransGen_iff_eq, h.not_step, not_step, reflTransGen_iff_eq
-/
theorem IsReduced.red_iff_eq (h : IsReduced L₁) : Red L₁ L₂ ↔ L₂ = L₁ :=
  Relation.reflTransGen_iff_eq fun _ => h.not_step

@[to_additive]
/--
theorem `IsReduced.append_overlap` / 定理 `IsReduced.append_overlap`

English:
theorem IsReduced.append_overlap
  statement: {L₁ L₂ L₃ : List (α × Bool)} (h₁ : IsReduced (L₁ ++ L₂))
  proof: IsChain.append_overlap h₁ h₂ hn

@[to_additive]

中文:
定理 是既约.append_overlap
  结论: {L₁ L₂ L₃ : 列表 (α × 布尔值)} (h₁ : 是既约 (L₁ ++ L₂))
  证明: IsChain.append_overlap h₁ h₂ hn

@[to_additive]

Depends on / 依赖: IsChain, IsChain.append_overlap, append_overlap
-/
theorem IsReduced.append_overlap {L₁ L₂ L₃ : List (α × Bool)} (h₁ : IsReduced (L₁ ++ L₂))
    (h₂ : IsReduced (L₂ ++ L₃)) (hn : L₂ != []) : IsReduced (L₁ ++ L₂ ++ L₃) :=
  IsChain.append_overlap h₁ h₂ hn

@[to_additive]
/--
theorem `IsReduced.infix` / 定理 `IsReduced.infix`

English:
theorem IsReduced.infix
  given: (h : IsReduced L₂) (h' : L₁ <:+: L₂)
  statement: IsReduced L₁
  proof: IsChain.infix h h'

中文:
定理 是既约.infix
  条件: (h : 是既约 L₂) (h' : L₁ <:+: L₂)
  结论: 是既约 L₁
  证明: IsChain.infix h h'

Depends on / 依赖: IsChain, IsChain.infix
-/
theorem IsReduced.infix (h : IsReduced L₂) (h' : L₁ <:+: L₂) : IsReduced L₁ := IsChain.infix h h'

end IsReduced
end FreeGroup

set_option linter.translateOverwrite false in
/--
If `α` is a type, then `FreeGroup α` is the free group generated by `α`.
This is a group equipped with a function `FreeGroup.of : α → FreeGroup α` which has
the following universal property: if `G` is any group, and `f : α → G` is any function,
then this function is the composite of `FreeGroup.of` and a unique group homomorphism
`FreeGroup.lift f : FreeGroup α →* G`.

A typical element of `FreeGroup α` is a formal product of
elements of `α` and their formal inverses, quotient by reduction.
For example if `x` and `y` are terms of type `α` then `x⁻¹ * y * y * x * y⁻¹` is a
"typical" element of `FreeGroup α`. In particular if `α` is empty
then `FreeGroup α` is isomorphic to the trivial group, and if `α` has one term
then `FreeGroup α` is isomorphic to `Multiplicative ℤ`.
If `α` has two or more terms then `FreeGroup α` is not commutative.
-/
@[to_additive (attr := wikidata Q431078)
/-- If `α` is a type, then `FreeAddGroup α` is the free additive group generated by `α`.
This is a group equipped with a function `FreeAddGroup.of : α → FreeAddGroup α` which has
the following universal property: if `G` is any group, and `f : α → G` is any function,
then this function is the composite of `FreeAddGroup.of` and a unique group homomorphism
`FreeAddGroup.lift f : FreeAddGroup α →+ G`.

A typical element of `FreeAddGroup α` is a formal sum of
elements of `α` and their formal inverses, quotient by reduction.
For example if `x` and `y` are terms of type `α` then `-x + y + y + x + -y` is a
"typical" element of `FreeAddGroup α`. In particular if `α` is empty
then `FreeAddGroup α` is isomorphic to the trivial group, and if `α` has one term
then `FreeAddGroup α` is isomorphic to `ℤ`.
If `α` has two or more terms then `FreeAddGroup α` is not commutative. -/]
/--
Definition of `FreeGroup` / `FreeGroup` 的定义

English:
definition FreeGroup
  signature: (α : Type u)
  body: Quot @FreeGroup.Red.Step α

中文:
定义 自由群
  签名: (α : 类型u)
  定义体: Quot @FreeGroup.Red.Step α

Depends on / 依赖: FreeGroup, FreeGroup.Red.Step
-/
def FreeGroup (α : Type u) : Type u :=
Quot @FreeGroup.Red.Step α

namespace FreeGroup

variable {L L₁ L₂ L₃ L₄ : List (α × Bool)}

/-- The canonical map from `List (α × Bool)` to the free group on `α`. -/
@[to_additive /-- The canonical map from `List (α × Bool)` to the free additive group on `α`. -/]
/--
Definition of `mk` / `mk` 的定义

English:
definition mk
  signature: (L : List (α × Bool))
  body: Quot.mk Red.Step L

@[to_additive (attr := simp)]

中文:
定义 mk
  签名: (L : 列表 (α × 布尔值))
  定义体: Quot.mk Red.Step L

@[to_additive (attr := simp)]

Depends on / 依赖: Quot.mk, Red.Step
-/
def mk (L : List (α × Bool)) : FreeGroup α :=
  Quot.mk Red.Step L

@[to_additive (attr := simp)]
/--
theorem `quot_mk_eq_mk` / 定理 `quot_mk_eq_mk`

English:
theorem quot_mk_eq_mk
  statement: Quot.mk Red.Step L = mk L
  proof: rfl

@[to_additive (attr := simp)]

中文:
定理 quot_mk_eq_mk
  结论: 商.mk Red.Step L = mk L
  证明: rfl

@[to_additive (attr := simp)]
-/
theorem quot_mk_eq_mk : Quot.mk Red.Step L = mk L :=
  rfl

@[to_additive (attr := simp)]
/--
theorem `quot_lift_mk` / 定理 `quot_lift_mk`

English:
theorem quot_lift_mk
  statement: (β : Type v) (f : List (α × Bool) -> β)
  proof: rfl

@[to_additive (attr := simp)]

中文:
定理 quot_lift_mk
  结论: (β : 类型v) (f : 列表 (α × 布尔值) -> β)
  证明: rfl

@[to_additive (attr := simp)]
-/
theorem quot_lift_mk (β : Type v) (f : List (α × Bool) -> β)
    (H : forall L₁ L₂, Red.Step L₁ L₂ -> f L₁ = f L₂) : Quot.lift f H (mk L) = f L :=
  rfl

@[to_additive (attr := simp)]
/--
theorem `quot_liftOn_mk` / 定理 `quot_liftOn_mk`

English:
theorem quot_liftOn_mk
  statement: (β : Type v) (f : List (α × Bool) -> β)
  proof: rfl

中文:
定理 quot_liftOn_mk
  结论: (β : 类型v) (f : 列表 (α × 布尔值) -> β)
  证明: rfl
-/
theorem quot_liftOn_mk (β : Type v) (f : List (α × Bool) -> β)
    (H : forall L₁ L₂, Red.Step L₁ L₂ -> f L₁ = f L₂) : Quot.liftOn (mk L) f H = f L :=
  rfl

open scoped Relator in
@[to_additive (attr := simp)]
/--
theorem `quot_map_mk` / 定理 `quot_map_mk`

English:
theorem quot_map_mk
  statement: (β : Type v) (f : List (α × Bool) -> List (β × Bool))
  proof: rfl

@[to_additive]

中文:
定理 quot_map_mk
  结论: (β : 类型v) (f : 列表 (α × 布尔值) -> 列表 (β × 布尔值))
  证明: rfl

@[to_additive]
-/
theorem quot_map_mk (β : Type v) (f : List (α × Bool) -> List (β × Bool))
    (H : (Red.Step ⇒ Red.Step) f f) : Quot.map f H (mk L) = mk (f L) :=
  rfl

@[to_additive]
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: One (FreeGroup α)
  body: ⟨mk []⟩

@[to_additive]

中文:
实例 :
  签名: 幺 (自由群 α)
  定义体: ⟨mk []⟩

@[to_additive]
-/
instance : One (FreeGroup α) :=
  ⟨mk []⟩

@[to_additive]
/--
theorem `one_eq_mk` / 定理 `one_eq_mk`

English:
theorem one_eq_mk
  statement: (1 : FreeGroup α) = mk []
  proof: rfl

@[to_additive]

中文:
定理 one_eq_mk
  结论: (1 : 自由群 α) = mk []
  证明: rfl

@[to_additive]
-/
theorem one_eq_mk : (1 : FreeGroup α) = mk [] :=
  rfl

@[to_additive]
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Inhabited (FreeGroup α)
  body: ⟨1⟩

@[to_additive]

中文:
实例 :
  签名: 可居 (自由群 α)
  定义体: ⟨1⟩

@[to_additive]
-/
instance : Inhabited (FreeGroup α) :=
  ⟨1⟩

@[to_additive]
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [IsEmpty
  signature: α] : Unique (FreeGroup α)
  body: inferInstanceAs Unique (Quot _)

@[to_additive]

中文:
实例 [是空
  签名: α] : 唯一 (自由群 α)
  定义体: inferInstanceAs Unique (Quot _)

@[to_additive]

Depends on / 依赖: Unique
-/
instance [IsEmpty α] : Unique (FreeGroup α) := inferInstanceAs Unique (Quot _)

@[to_additive]
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Mul (FreeGroup α)
  body: ⟨fun x y =>
    Quot.liftOn x
      (fun L₁ =>
        Quot.liftOn y (fun L₂ => mk <| L₁ ++ L₂) fun _L₂ _L₃ H =>
Quot.sound Red.Step.append_left H)
fun _L₁ _L₂ H => Quot.inductionOn y fun _L₃ => Quot.sound Red.Step.append_right H⟩

@[to_additive (attr := simp)]

中文:
实例 :
  签名: 乘法 (自由群 α)
  定义体: ⟨fun x y =>
    Quot.liftOn x
      (fun L₁ =>
        Quot.liftOn y (fun L₂ => mk <| L₁ ++ L₂) fun _L₂ _L₃ H =>
Quot.sound Red.Step.append_left H)
fun _L₁ _L₂ H => Quot.inductionOn y fun _L₃ => Quot.sound Red.Step.append_right H⟩

@[to_additive (attr := simp)]

Depends on / 依赖: Quot.inductionOn, Quot.liftOn, Quot.sound, Red.Step.append_left, Red.Step.append_right, append_left, append_right, inductionOn, liftOn
-/
instance : Mul (FreeGroup α) :=
  ⟨fun x y =>
    Quot.liftOn x
      (fun L₁ =>
        Quot.liftOn y (fun L₂ => mk <| L₁ ++ L₂) fun _L₂ _L₃ H =>
Quot.sound Red.Step.append_left H)
fun _L₁ _L₂ H => Quot.inductionOn y fun _L₃ => Quot.sound Red.Step.append_right H⟩

@[to_additive (attr := simp)]
/--
theorem `mul_mk` / 定理 `mul_mk`

English:
theorem mul_mk
  statement: mk L₁ * mk L₂ = mk (L₁ ++ L₂)
  proof: rfl

中文:
定理 mul_mk
  结论: mk L₁ * mk L₂ = mk (L₁ ++ L₂)
  证明: rfl
-/
theorem mul_mk : mk L₁ * mk L₂ = mk (L₁ ++ L₂) :=
  rfl

/-- Transform a word representing a free group element into a word representing its inverse. -/
@[to_additive /-- Transform a word representing a free group element into a word representing its
  negative. -/]
/--
Definition of `invRev` / `invRev` 的定义

English:
definition invRev
  signature: (w : List (α × Bool))
  body: (List.map (fun g : α × Bool => (g.1, not g.2)) w).reverse

@[to_additive (attr := simp)]

中文:
定义 invRev
  签名: (w : 列表 (α × 布尔值))
  定义体: (List.map (fun g : α × Bool => (g.1, not g.2)) w).reverse

@[to_additive (attr := simp)]

Depends on / 依赖: List.map, reverse
-/
def invRev (w : List (α × Bool)) : List (α × Bool) :=
  (List.map (fun g : α × Bool => (g.1, not g.2)) w).reverse

@[to_additive (attr := simp)]
/--
theorem `invRev_length` / 定理 `invRev_length`

English:
theorem invRev_length
  statement: (invRev L₁).length = L₁.length
  proof: by simp [invRev]

@[to_additive (attr := simp)]

中文:
定理 invRev_length
  结论: (invRev L₁).length = L₁.length
  证明: by simp [invRev]

@[to_additive (attr := simp)]

Depends on / 依赖: invRev
-/
theorem invRev_length : (invRev L₁).length = L₁.length := by simp [invRev]

@[to_additive (attr := simp)]
/--
theorem `invRev_invRev` / 定理 `invRev_invRev`

English:
theorem invRev_invRev
  statement: invRev (invRev L₁) = L₁
  proof: by
  simp [invRev, List.map_reverse, Function.comp_def]

@[to_additive (attr := simp)]

中文:
定理 invRev_invRev
  结论: invRev (invRev L₁) = L₁
  证明: by
  simp [invRev, List.map_reverse, Function.comp_def]

@[to_additive (attr := simp)]

Depends on / 依赖: Function, Function.comp_def, List.map_reverse, comp_def, invRev, map_reverse
-/
theorem invRev_invRev : invRev (invRev L₁) = L₁ := by
  simp [invRev, List.map_reverse, Function.comp_def]

@[to_additive (attr := simp)]
/--
theorem `invRev_empty` / 定理 `invRev_empty`

English:
theorem invRev_empty
  statement: invRev ([] : List (α × Bool)) = []
  proof: rfl

@[to_additive (attr := simp)]

中文:
定理 invRev_empty
  结论: invRev ([] : 列表 (α × 布尔值)) = []
  证明: rfl

@[to_additive (attr := simp)]
-/
theorem invRev_empty : invRev ([] : List (α × Bool)) = [] :=
  rfl

@[to_additive (attr := simp)]
/--
theorem `invRev_append` / 定理 `invRev_append`

English:
theorem invRev_append
  statement: invRev (L₁ ++ L₂) = invRev L₂ ++ invRev L₁
  proof: by simp [invRev]

@[to_additive]

中文:
定理 invRev_append
  结论: invRev (L₁ ++ L₂) = invRev L₂ ++ invRev L₁
  证明: by simp [invRev]

@[to_additive]

Depends on / 依赖: invRev
-/
theorem invRev_append : invRev (L₁ ++ L₂) = invRev L₂ ++ invRev L₁ := by simp [invRev]

@[to_additive]
/--
theorem `invRev_cons` / 定理 `invRev_cons`

English:
theorem invRev_cons
  given: {a : (α × Bool)}
  statement: invRev (a :: L) = invRev L ++ invRev [a]
  proof: by
  simp [invRev]

@[to_additive]

中文:
定理 invRev_cons
  条件: {a : (α × 布尔值)}
  结论: invRev (a :: L) = invRev L ++ invRev [a]
  证明: by
  simp [invRev]

@[to_additive]

Depends on / 依赖: invRev
-/
theorem invRev_cons {a : (α × Bool)} : invRev (a :: L) = invRev L ++ invRev [a] := by
  simp [invRev]

@[to_additive]
/--
theorem `invRev_involutive` / 定理 `invRev_involutive`

English:
theorem invRev_involutive
  statement: Function.Involutive (@invRev α)
  proof: fun _ => invRev_invRev

@[to_additive]

中文:
定理 invRev_involutive
  结论: 函数.对合 (@invRev α)
  证明: fun _ => invRev_invRev

@[to_additive]

Depends on / 依赖: invRev_invRev
-/
theorem invRev_involutive : Function.Involutive (@invRev α) := fun _ => invRev_invRev

@[to_additive]
/--
theorem `invRev_injective` / 定理 `invRev_injective`

English:
theorem invRev_injective
  statement: Function.Injective (@invRev α)
  proof: invRev_involutive.injective

@[to_additive]

中文:
定理 invRev_injective
  结论: 函数.单射 (@invRev α)
  证明: invRev_involutive.injective

@[to_additive]

Depends on / 依赖: injective, invRev_involutive, invRev_involutive.injective
-/
theorem invRev_injective : Function.Injective (@invRev α) :=
  invRev_involutive.injective

@[to_additive]
/--
theorem `invRev_surjective` / 定理 `invRev_surjective`

English:
theorem invRev_surjective
  statement: Function.Surjective (@invRev α)
  proof: invRev_involutive.surjective

@[to_additive]

中文:
定理 invRev_surjective
  结论: 函数.满射 (@invRev α)
  证明: invRev_involutive.surjective

@[to_additive]

Depends on / 依赖: invRev_involutive, invRev_involutive.surjective, surjective
-/
theorem invRev_surjective : Function.Surjective (@invRev α) :=
  invRev_involutive.surjective

@[to_additive]
/--
theorem `invRev_bijective` / 定理 `invRev_bijective`

English:
theorem invRev_bijective
  statement: Function.Bijective (@invRev α)
  proof: invRev_involutive.bijective

@[to_additive]

中文:
定理 invRev_bijective
  结论: 函数.双射 (@invRev α)
  证明: invRev_involutive.bijective

@[to_additive]

Depends on / 依赖: bijective, invRev_involutive, invRev_involutive.bijective
-/
theorem invRev_bijective : Function.Bijective (@invRev α) :=
  invRev_involutive.bijective

@[to_additive]
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Inv (FreeGroup α)
  body: ⟨Quot.map invRev
      (by
        intro a b h
        cases h
        simp [invRev])⟩

@[to_additive (attr := simp)]

中文:
实例 :
  签名: 取逆 (自由群 α)
  定义体: ⟨Quot.map invRev
      (by
        intro a b h
        cases h
        simp [invRev])⟩

@[to_additive (attr := simp)]

Depends on / 依赖: Quot.map, invRev
-/
instance : Inv (FreeGroup α) :=
  ⟨Quot.map invRev
      (by
        intro a b h
        cases h
        simp [invRev])⟩

@[to_additive (attr := simp)]
/--
theorem `inv_mk` / 定理 `inv_mk`

English:
theorem inv_mk
  statement: (mk L)⁻¹ = mk (invRev L)
  proof: rfl

@[to_additive]

中文:
定理 inv_mk
  结论: (mk L)⁻¹ = mk (invRev L)
  证明: rfl

@[to_additive]
-/
theorem inv_mk : (mk L)⁻¹ = mk (invRev L) :=
  rfl

@[to_additive]
/--
theorem `Red.Step.invRev` / 定理 `Red.Step.invRev`

English:
theorem Red.Step.invRev
  given: {L₁ L₂ : List (α × Bool)} (h : Red.Step L₁ L₂)
  proof: by
  obtain ⟨a, b, x, y⟩ := h
  simp [FreeGroup.invRev]

@[to_additive]

中文:
定理 Red.Step.invRev
  条件: {L₁ L₂ : 列表 (α × 布尔值)} (h : Red.Step L₁ L₂)
  证明: by
  obtain ⟨a, b, x, y⟩ := h
  simp [FreeGroup.invRev]

@[to_additive]

Depends on / 依赖: FreeGroup, FreeGroup.invRev, invRev
-/
theorem Red.Step.invRev {L₁ L₂ : List (α × Bool)} (h : Red.Step L₁ L₂) :
    Red.Step (FreeGroup.invRev L₁) (FreeGroup.invRev L₂) := by
  obtain ⟨a, b, x, y⟩ := h
  simp [FreeGroup.invRev]

@[to_additive]
/--
theorem `Red.invRev` / 定理 `Red.invRev`

English:
theorem Red.invRev
  given: {L₁ L₂ : List (α × Bool)} (h : Red L₁ L₂)
  statement: Red (invRev L₁) (invRev L₂)
  proof: Relation.ReflTransGen.lift FreeGroup.invRev (fun _a _b => Red.Step.invRev) L₁ L₂ h

@[to_additive (attr := simp)]

中文:
定理 Red.invRev
  条件: {L₁ L₂ : 列表 (α × 布尔值)} (h : Red L₁ L₂)
  结论: Red (invRev L₁) (invRev L₂)
  证明: Relation.ReflTransGen.lift FreeGroup.invRev (fun _a _b => Red.Step.invRev) L₁ L₂ h

@[to_additive (attr := simp)]

Depends on / 依赖: FreeGroup, FreeGroup.invRev, Red.Step.invRev, ReflTransGen, Relation, Relation.ReflTransGen.lift, invRev
-/
theorem Red.invRev {L₁ L₂ : List (α × Bool)} (h : Red L₁ L₂) : Red (invRev L₁) (invRev L₂) :=
  Relation.ReflTransGen.lift FreeGroup.invRev (fun _a _b => Red.Step.invRev) L₁ L₂ h

@[to_additive (attr := simp)]
/--
theorem `Red.step_invRev_iff` / 定理 `Red.step_invRev_iff`

English:
theorem Red.step_invRev_iff
  proof: ⟨fun h => by simpa only [invRev_invRev] using h.invRev, fun h => h.invRev⟩

@[to_additive (attr := simp)]

中文:
定理 Red.step_invRev_iff
  证明: ⟨fun h => by simpa only [invRev_invRev] using h.invRev, fun h => h.invRev⟩

@[to_additive (attr := simp)]

Depends on / 依赖: h.invRev, invRev, invRev_invRev
-/
theorem Red.step_invRev_iff :
    Red.Step (FreeGroup.invRev L₁) (FreeGroup.invRev L₂) ↔ Red.Step L₁ L₂ :=
  ⟨fun h => by simpa only [invRev_invRev] using h.invRev, fun h => h.invRev⟩

@[to_additive (attr := simp)]
/--
theorem `red_invRev_iff` / 定理 `red_invRev_iff`

English:
theorem red_invRev_iff
  statement: Red (invRev L₁) (invRev L₂) ↔ Red L₁ L₂
  proof: ⟨fun h => by simpa only [invRev_invRev] using h.invRev, fun h => h.invRev⟩

@[to_additive]

中文:
定理 red_invRev_iff
  结论: Red (invRev L₁) (invRev L₂) ↔ Red L₁ L₂
  证明: ⟨fun h => by simpa only [invRev_invRev] using h.invRev, fun h => h.invRev⟩

@[to_additive]

Depends on / 依赖: h.invRev, invRev, invRev_invRev
-/
theorem red_invRev_iff : Red (invRev L₁) (invRev L₂) ↔ Red L₁ L₂ :=
  ⟨fun h => by simpa only [invRev_invRev] using h.invRev, fun h => h.invRev⟩

@[to_additive]
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Group (FreeGroup α)
  body: by rintro ⟨L₁⟩ ⟨L₂⟩ ⟨L₃⟩; simp
  one_mul := by rintro ⟨L⟩; rfl
  mul_one := by rintro ⟨L⟩; simp [one_eq_mk]
  inv_mul_cancel := by
    rintro ⟨L⟩
    exact
      List.recOn L rfl fun ⟨x, b⟩ tl ih =>
          Eq.trans (Quot.sound <| by simp [invRev]) ih

@[to_additive (attr := simp)]

中文:
实例 :
  签名: 群 (自由群 α)
  定义体: by rintro ⟨L₁⟩ ⟨L₂⟩ ⟨L₃⟩; simp
  one_mul := by rintro ⟨L⟩; rfl
  mul_one := by rintro ⟨L⟩; simp [one_eq_mk]
  inv_mul_cancel := by
    rintro ⟨L⟩
    exact
      List.recOn L rfl fun ⟨x, b⟩ tl ih =>
          Eq.trans (Quot.sound <| by simp [invRev]) ih

@[to_additive (attr := simp)]

Depends on / 依赖: Eq.trans, List.recOn, Quot.sound, invRev, inv_mul_cancel, mul_one, one_eq_mk, one_mul
-/
instance : Group (FreeGroup α) where
  mul_assoc := by rintro ⟨L₁⟩ ⟨L₂⟩ ⟨L₃⟩; simp
  one_mul := by rintro ⟨L⟩; rfl
  mul_one := by rintro ⟨L⟩; simp [one_eq_mk]
  inv_mul_cancel := by
    rintro ⟨L⟩
    exact
      List.recOn L rfl fun ⟨x, b⟩ tl ih =>
          Eq.trans (Quot.sound <| by simp [invRev]) ih

@[to_additive (attr := simp)]
/--
theorem `pow_mk` / 定理 `pow_mk`

English:
theorem pow_mk
  given: (n : Nat)
  statement: mk L ^ n = mk (List.flatten <| List.replicate n L)
  proof: match n with
  | 0 => rfl
  | n + 1 => by rw [pow_succ', pow_mk, mul_mk, List.replicate_succ, List.flatten_cons]

中文:
定理 pow_mk
  条件: (n : 自然数)
  结论: mk L ^ n = mk (列表.flatten <| 列表.replicate n L)
  证明: match n with
  | 0 => rfl
  | n + 1 => by rw [pow_succ', pow_mk, mul_mk, List.replicate_succ, List.flatten_cons]

Depends on / 依赖: List.flatten_cons, List.replicate_succ, flatten_cons, mul_mk, pow_mk, pow_succ, replicate_succ
-/
theorem pow_mk (n : Nat) : mk L ^ n = mk (List.flatten <| List.replicate n L) :=
  match n with
  | 0 => rfl
  | n + 1 => by rw [pow_succ', pow_mk, mul_mk, List.replicate_succ, List.flatten_cons]

/-- `of` is the canonical injection from the type to the free group over that type by sending each
element to the equivalence class of the letter that is the element. -/
@[to_additive /-- `of` is the canonical injection from the type to the free group over that type
  by sending each element to the equivalence class of the letter that is the element. -/]
/--
Definition of `of` / `of` 的定义

English:
definition of
  signature: (x : α)
  body: mk [(x, true)]

@[to_additive (attr := elab_as_elim, induction_eliminator)]

中文:
定义 of
  签名: (x : α)
  定义体: mk [(x, true)]

@[to_additive (attr := elab_as_elim, induction_eliminator)]
-/
def of (x : α) : FreeGroup α :=
  mk [(x, true)]

@[to_additive (attr := elab_as_elim, induction_eliminator)]
/--
lemma `induction_on` / 引理 `induction_on`

English:
lemma induction_on
  statement: {C : FreeGroup α -> Prop} (z : FreeGroup α) (C1 : C 1)
  proof: Quot.inductionOn z fun L => L.recOn C1 fun ⟨x, b⟩ _tl ih =>
    b.recOn (mul _ _ (inv_of _ <| of x) ih) (mul _ _ (of x) ih)

中文:
引理 induction_on
  结论: {C : 自由群 α -> 命题} (z : 自由群 α) (C1 : C 1)
  证明: Quot.inductionOn z fun L => L.recOn C1 fun ⟨x, b⟩ _tl ih =>
    b.recOn (mul _ _ (inv_of _ <| of x) ih) (mul _ _ (of x) ih)
-/
protected lemma induction_on {C : FreeGroup α -> Prop} (z : FreeGroup α) (C1 : C 1)
    (of : forall x, C <| of x) (inv_of : forall x, C (.of x) -> C (.of x)⁻¹)
    (mul : forall x y, C x -> C y -> C (x * y)) : C z :=
  Quot.inductionOn z fun L => L.recOn C1 fun ⟨x, b⟩ _tl ih =>
    b.recOn (mul _ _ (inv_of _ <| of x) ih) (mul _ _ (of x) ih)

/-- Two homomorphisms out of a free group are equal if they are equal on generators.

See note [partially-applied ext lemmas]. -/
@[to_additive (attr := ext) /-- Two homomorphisms out of a free additive group are equal if they are
  equal on generators. See note [partially-applied ext lemmas]. -/]
/--
lemma `ext_hom` / 引理 `ext_hom`

English:
lemma ext_hom
  given: {M : Type*} [Monoid M] (f g : FreeGroup α ->* M) (h : forall a, f (of a) = g (of a))
  proof: by
  ext x
  have this (x) : f (of x)⁻¹ = g (of x)⁻¹ := by
    trans f (of x)⁻¹ * f (of x) * g (of x)⁻¹
    · simp_rw [mul_assoc, h, ← _root_.map_mul, mul_inv_cancel, _root_.map_one, mul_one]
    · simp_rw [← _root_.map_mul, inv_mul_cancel, _root_.map_one, one_mul]
  induction x <;> simp [*]

@[to_a

中文:
引理 ext_hom
  条件: {M : 类型} [幺半群 M] (f g : 自由群 α ->* M) (h : 对任意 a, f (of a) = g (of a))
  证明: by
  ext x
  have this (x) : f (of x)⁻¹ = g (of x)⁻¹ := by
    trans f (of x)⁻¹ * f (of x) * g (of x)⁻¹
    · simp_rw [mul_assoc, h, ← _root_.map_mul, mul_inv_cancel, _root_.map_one, mul_one]
    · simp_rw [← _root_.map_mul, inv_mul_cancel, _root_.map_one, one_mul]
  induction x <;> simp [*]

@[to_a

Depends on / 依赖: _root_, _root_.map_mul, _root_.map_one, inv_mul_cancel, map_mul, map_one, mul_assoc, mul_inv_cancel, mul_one, one_mul, simp_rw
-/
lemma ext_hom {M : Type*} [Monoid M] (f g : FreeGroup α ->* M) (h : forall a, f (of a) = g (of a)) :
    f = g := by
  ext x
  have this (x) : f (of x)⁻¹ = g (of x)⁻¹ := by
    trans f (of x)⁻¹ * f (of x) * g (of x)⁻¹
    · simp_rw [mul_assoc, h, ← _root_.map_mul, mul_inv_cancel, _root_.map_one, mul_one]
    · simp_rw [← _root_.map_mul, inv_mul_cancel, _root_.map_one, one_mul]
  induction x <;> simp [*]

@[to_additive]
/--
theorem `Red.exact` / 定理 `Red.exact`

English:
theorem Red.exact
  statement: mk L₁ = mk L₂ ↔ Join Red L₁ L₂
  proof: calc
    mk L₁ = mk L₂ ↔ EqvGen Red.Step L₁ L₂ := Iff.intro Quot.eqvGen_exact Quot.eqvGen_sound
    _ ↔ Join Red L₁ L₂ := eqvGen_step_iff_join_red

中文:
定理 Red.exact
  结论: mk L₁ = mk L₂ ↔ 并 Red L₁ L₂
  证明: calc
    mk L₁ = mk L₂ ↔ EqvGen Red.Step L₁ L₂ := Iff.intro Quot.eqvGen_exact Quot.eqvGen_sound
    _ ↔ Join Red L₁ L₂ := eqvGen_step_iff_join_red

Depends on / 依赖: EqvGen, Iff.intro, Quot.eqvGen_exact, Quot.eqvGen_sound, Red.Step, eqvGen_exact, eqvGen_sound, eqvGen_step_iff_join_red
-/
theorem Red.exact : mk L₁ = mk L₂ ↔ Join Red L₁ L₂ :=
  calc
    mk L₁ = mk L₂ ↔ EqvGen Red.Step L₁ L₂ := Iff.intro Quot.eqvGen_exact Quot.eqvGen_sound
    _ ↔ Join Red L₁ L₂ := eqvGen_step_iff_join_red

/-- The canonical map from the type to the free group is an injection. -/
@[to_additive /-- The canonical map from the type to the additive free group is an injection. -/]
/--
theorem `of_injective` / 定理 `of_injective`

English:
theorem of_injective
  statement: Function.Injective (@of α)
  proof: fun _ _ H => by
  let ⟨L₁, hx, hy⟩ := Red.exact.1 H
  simp [Red.singleton_iff] at hx hy; simp_all

中文:
定理 of_injective
  结论: 函数.单射 (@of α)
  证明: fun _ _ H => by
  let ⟨L₁, hx, hy⟩ := Red.exact.1 H
  simp [Red.singleton_iff] at hx hy; simp_all

Depends on / 依赖: Red.exact, Red.singleton_iff, singleton_iff
-/
theorem of_injective : Function.Injective (@of α) := fun _ _ H => by
  let ⟨L₁, hx, hy⟩ := Red.exact.1 H
  simp [Red.singleton_iff] at hx hy; simp_all

section lift

variable {β : Type v} [Group β] (f : α -> β) {x y : FreeGroup α}

/-- Given `f : α → β` with `β` a group, the canonical map `List (α × Bool) → β` -/
@[to_additive /-- Given `f : α → β` with `β` an additive group, the canonical map
  `List (α × Bool) → β` -/]
/--
Definition of `Lift.aux` / `Lift.aux` 的定义

English:
definition Lift.aux
  signature: : List (α × Bool) -> β
  body: fun L =>
List.prod L.map fun x => cond x.2 (f x.1) (f x.1)⁻¹

@[to_additive]

中文:
定义 Lift.aux
  签名: : 列表 (α × 布尔值) -> β
  定义体: fun L =>
List.prod L.map fun x => cond x.2 (f x.1) (f x.1)⁻¹

@[to_additive]
-/
def Lift.aux : List (α × Bool) -> β := fun L =>
List.prod L.map fun x => cond x.2 (f x.1) (f x.1)⁻¹

@[to_additive]
/--
theorem `Red.Step.lift` / 定理 `Red.Step.lift`

English:
theorem Red.Step.lift
  given: {f : α -> β} (H : Red.Step L₁ L₂)
  statement: Lift.aux f L₁ = Lift.aux f L₂
  proof: by
  obtain @⟨_, _, _, b⟩ := H; cases b <;> simp [Lift.aux, List.prod_append]

中文:
定理 Red.Step.lift
  条件: {f : α -> β} (H : Red.Step L₁ L₂)
  结论: Lift.aux f L₁ = Lift.aux f L₂
  证明: by
  obtain @⟨_, _, _, b⟩ := H; cases b <;> simp [Lift.aux, List.prod_append]

Depends on / 依赖: Lift.aux, List.prod_append, prod_append
-/
theorem Red.Step.lift {f : α -> β} (H : Red.Step L₁ L₂) : Lift.aux f L₁ = Lift.aux f L₂ := by
  obtain @⟨_, _, _, b⟩ := H; cases b <;> simp [Lift.aux, List.prod_append]

set_option backward.isDefEq.respectTransparency false in
/-- If `β` is a group, then any function from `α` to `β` extends uniquely to a group homomorphism
from the free group over `α` to `β` -/
@[to_additive (attr := simps symm_apply)
  /-- If `β` is an additive group, then any function from `α` to `β` extends uniquely to an
  additive group homomorphism from the free additive group over `α` to `β` -/]
/--
Definition of `lift` / `lift` 的定义

English:
definition lift
  signature: : (α -> β) ≃ (FreeGroup α ->* β) where
  body: MonoidHom.mk' (Quot.lift (Lift.aux f) fun _ _ => Red.Step.lift) by
      rintro ⟨L₁⟩ ⟨L₂⟩; simp [Lift.aux, List.prod_append]
  invFun g := g ∘ of
  left_inv f := by ext; simp [of, Lift.aux]
  right_inv g := by ext; simp [of, Lift.aux]

中文:
定义 lift
  签名: : (α -> β) ≃ (自由群 α ->* β) where
  定义体: MonoidHom.mk' (Quot.lift (Lift.aux f) fun _ _ => Red.Step.lift) by
      rintro ⟨L₁⟩ ⟨L₂⟩; simp [Lift.aux, List.prod_append]
  invFun g := g ∘ of
  left_inv f := by ext; simp [of, Lift.aux]
  right_inv g := by ext; simp [of, Lift.aux]

Depends on / 依赖: Lift.aux, List.prod_append, MonoidHom, MonoidHom.mk, Quot.lift, Red.Step.lift, invFun, left_inv, prod_append, right_inv
-/
def lift : (α -> β) ≃ (FreeGroup α ->* β) where
  toFun f :=
MonoidHom.mk' (Quot.lift (Lift.aux f) fun _ _ => Red.Step.lift) by
      rintro ⟨L₁⟩ ⟨L₂⟩; simp [Lift.aux, List.prod_append]
  invFun g := g ∘ of
  left_inv f := by ext; simp [of, Lift.aux]
  right_inv g := by ext; simp [of, Lift.aux]

variable {f}

@[to_additive (attr := simp)]
/--
theorem `lift_mk` / 定理 `lift_mk`

English:
theorem lift_mk
  statement: lift f (mk L) = List.prod (L.map fun x => cond x.2 (f x.1) (f x.1)⁻¹)
  proof: rfl

@[to_additive (attr := simp)]

中文:
定理 lift_mk
  结论: lift f (mk L) = 列表.乘积 (L.map fun x => cond x.2 (f x.1) (f x.1)⁻¹)
  证明: rfl

@[to_additive (attr := simp)]
-/
theorem lift_mk : lift f (mk L) = List.prod (L.map fun x => cond x.2 (f x.1) (f x.1)⁻¹) :=
  rfl

@[to_additive (attr := simp)]
/--
theorem `lift_apply_of` / 定理 `lift_apply_of`

English:
theorem lift_apply_of
  given: {x}
  statement: lift f (of x) = f x
  proof: by simp [of]

@[to_additive]

中文:
定理 lift_apply_of
  条件: {x}
  结论: lift f (of x) = f x
  证明: by simp [of]

@[to_additive]
-/
theorem lift_apply_of {x} : lift f (of x) = f x := by simp [of]

@[to_additive]
/--
theorem `lift_unique` / 定理 `lift_unique`

English:
theorem lift_unique
  given: (g : FreeGroup α ->* β) (hg : forall x, g (FreeGroup.of x) = f x) {x}
  proof: DFunLike.congr_fun (lift.symm_apply_eq.mp (funext hg : g ∘ FreeGroup.of = f)) x

@[to_additive]

中文:
定理 lift_unique
  条件: (g : 自由群 α ->* β) (hg : 对任意 x, g (自由群.of x) = f x) {x}
  证明: DFunLike.congr_fun (lift.symm_apply_eq.mp (funext hg : g ∘ FreeGroup.of = f)) x

@[to_additive]

Depends on / 依赖: DFunLike, DFunLike.congr_fun, FreeGroup, FreeGroup.of, congr_fun, lift.symm_apply_eq.mp, symm_apply_eq
-/
theorem lift_unique (g : FreeGroup α ->* β) (hg : forall x, g (FreeGroup.of x) = f x) {x} :
    g x = FreeGroup.lift f x :=
  DFunLike.congr_fun (lift.symm_apply_eq.mp (funext hg : g ∘ FreeGroup.of = f)) x

@[to_additive]
/--
theorem `lift_of_eq_id` / 定理 `lift_of_eq_id`

English:
theorem lift_of_eq_id
  given: (α)
  statement: lift of = MonoidHom.id (FreeGroup α)
  proof: lift.apply_symm_apply (MonoidHom.id _)

@[to_additive]

中文:
定理 lift_of_eq_id
  条件: (α)
  结论: lift of = 幺半群态射.id (自由群 α)
  证明: lift.apply_symm_apply (MonoidHom.id _)

@[to_additive]

Depends on / 依赖: MonoidHom, MonoidHom.id, apply_symm_apply, lift.apply_symm_apply
-/
theorem lift_of_eq_id (α) : lift of = MonoidHom.id (FreeGroup α) :=
  lift.apply_symm_apply (MonoidHom.id _)

@[to_additive]
/--
theorem `lift_of_apply` / 定理 `lift_of_apply`

English:
theorem lift_of_apply
  given: (x : FreeGroup α)
  statement: lift FreeGroup.of x = x
  proof: DFunLike.congr_fun (lift_of_eq_id α) x

@[to_additive]

中文:
定理 lift_of_apply
  条件: (x : 自由群 α)
  结论: lift 自由群.of x = x
  证明: DFunLike.congr_fun (lift_of_eq_id α) x

@[to_additive]

Depends on / 依赖: DFunLike, DFunLike.congr_fun, congr_fun, lift_of_eq_id
-/
theorem lift_of_apply (x : FreeGroup α) : lift FreeGroup.of x = x :=
  DFunLike.congr_fun (lift_of_eq_id α) x

@[to_additive]
/--
theorem `range_lift_le` / 定理 `range_lift_le`

English:
theorem range_lift_le
  given: {s : Subgroup β} (H : Set.range f subseteq s)
  statement: (lift f).range <= s
  proof: by
  rintro _ ⟨⟨L⟩, rfl⟩
  exact List.recOn L s.one_mem fun ⟨x, b⟩ tl ih =>
    Bool.recOn b (by simpa using s.mul_mem (s.inv_mem <| H ⟨x, rfl⟩) ih)
      (by simpa using s.mul_mem (H ⟨x, rfl⟩) ih)

@[to_additive]

中文:
定理 range_lift_le
  条件: {s : 子群 β} (H : 集合.range f subseteq s)
  结论: (lift f).range <= s
  证明: by
  rintro _ ⟨⟨L⟩, rfl⟩
  exact List.recOn L s.one_mem fun ⟨x, b⟩ tl ih =>
    Bool.recOn b (by simpa using s.mul_mem (s.inv_mem <| H ⟨x, rfl⟩) ih)
      (by simpa using s.mul_mem (H ⟨x, rfl⟩) ih)

@[to_additive]

Depends on / 依赖: Bool.recOn, List.recOn, inv_mem, mul_mem, one_mem, s.inv_mem, s.mul_mem, s.one_mem
-/
theorem range_lift_le {s : Subgroup β} (H : Set.range f subseteq s) : (lift f).range <= s := by
  rintro _ ⟨⟨L⟩, rfl⟩
  exact List.recOn L s.one_mem fun ⟨x, b⟩ tl ih =>
    Bool.recOn b (by simpa using s.mul_mem (s.inv_mem <| H ⟨x, rfl⟩) ih)
      (by simpa using s.mul_mem (H ⟨x, rfl⟩) ih)

@[to_additive]
/--
theorem `range_lift_eq_closure` / 定理 `range_lift_eq_closure`

English:
theorem range_lift_eq_closure
  statement: (lift f).range = Subgroup.closure (Set.range f)
  proof: by
  apply le_antisymm (range_lift_le Subgroup.subset_closure)
  rw [Subgroup.closure_le]
  rintro _ ⟨a, rfl⟩
  exact ⟨FreeGroup.of a, by simp only [lift_apply_of]⟩

@[to_additive]

中文:
定理 range_lift_eq_closure
  结论: (lift f).range = 子群.closure (集合.range f)
  证明: by
  apply le_antisymm (range_lift_le Subgroup.subset_closure)
  rw [Subgroup.closure_le]
  rintro _ ⟨a, rfl⟩
  exact ⟨FreeGroup.of a, by simp only [lift_apply_of]⟩

@[to_additive]

Depends on / 依赖: FreeGroup, FreeGroup.of, Subgroup, Subgroup.closure_le, Subgroup.subset_closure, closure_le, le_antisymm, lift_apply_of, range_lift_le, subset_closure
-/
theorem range_lift_eq_closure : (lift f).range = Subgroup.closure (Set.range f) := by
  apply le_antisymm (range_lift_le Subgroup.subset_closure)
  rw [Subgroup.closure_le]
  rintro _ ⟨a, rfl⟩
  exact ⟨FreeGroup.of a, by simp only [lift_apply_of]⟩

@[to_additive]
/--
theorem `lift_surjective_iff_closure_range_eq_top` / 定理 `lift_surjective_iff_closure_range_eq_top`

English:
theorem lift_surjective_iff_closure_range_eq_top
  proof: by
  rw [← MonoidHom.range_eq_top]; rw [range_lift_eq_closure]

@[to_additive]

中文:
定理 lift_surjective_iff_closure_range_eq_top
  证明: by
  rw [← MonoidHom.range_eq_top]; rw [range_lift_eq_closure]

@[to_additive]

Depends on / 依赖: MonoidHom, MonoidHom.range_eq_top, range_eq_top, range_lift_eq_closure
-/
theorem lift_surjective_iff_closure_range_eq_top :
    Function.Surjective (lift f) ↔ Subgroup.closure (Set.range f) = ⊤ := by
  rw [← MonoidHom.range_eq_top]; rw [range_lift_eq_closure]

@[to_additive]
/--
theorem `closure_eq_range` / 定理 `closure_eq_range`

English:
theorem closure_eq_range
  given: (s : Set β)
  statement: Subgroup.closure s = (lift ((↑) : s -> β)).range
  proof: by
  rw [FreeGroup.range_lift_eq_closure]; rw [Subtype.range_coe]

中文:
定理 closure_eq_range
  条件: (s : 集合 β)
  结论: 子群.closure s = (lift ((↑) : s -> β)).range
  证明: by
  rw [FreeGroup.range_lift_eq_closure]; rw [Subtype.range_coe]

Depends on / 依赖: FreeGroup, FreeGroup.range_lift_eq_closure, Subtype, Subtype.range_coe, range_coe, range_lift_eq_closure
-/
theorem closure_eq_range (s : Set β) : Subgroup.closure s = (lift ((↑) : s -> β)).range := by
  rw [FreeGroup.range_lift_eq_closure]; rw [Subtype.range_coe]

/-- The generators of `FreeGroup α` generate `FreeGroup α`. That is, the subgroup closure of the
set of generators equals `⊤`. -/
@[to_additive (attr := simp)]
/--
theorem `closure_range_of` / 定理 `closure_range_of`

English:
theorem closure_range_of
  given: (α)
  proof: by
  rw [← range_lift_eq_closure]; rw [lift_of_eq_id]
  exact MonoidHom.range_eq_top.2 Function.surjective_id

@[to_additive]

中文:
定理 closure_range_of
  条件: (α)
  证明: by
  rw [← range_lift_eq_closure]; rw [lift_of_eq_id]
  exact MonoidHom.range_eq_top.2 Function.surjective_id

@[to_additive]

Depends on / 依赖: Function, Function.surjective_id, MonoidHom, MonoidHom.range_eq_top, lift_of_eq_id, range_eq_top, range_lift_eq_closure, surjective_id
-/
theorem closure_range_of (α) :
    Subgroup.closure (Set.range (FreeGroup.of : α -> FreeGroup α)) = ⊤ := by
  rw [← range_lift_eq_closure]; rw [lift_of_eq_id]
  exact MonoidHom.range_eq_top.2 Function.surjective_id

@[to_additive]
/--
theorem `lift_surjective_of_surjective` / 定理 `lift_surjective_of_surjective`

English:
theorem lift_surjective_of_surjective
  given: (hf : Function.Surjective f)
  proof: by
  rw [← MonoidHom.range_eq_top]; rw [range_lift_eq_closure]; rw [hf.range_eq]; rw [Subgroup.closure_univ]

中文:
定理 lift_surjective_of_surjective
  条件: (hf : 函数.满射 f)
  证明: by
  rw [← MonoidHom.range_eq_top]; rw [range_lift_eq_closure]; rw [hf.range_eq]; rw [Subgroup.closure_univ]

Depends on / 依赖: MonoidHom, MonoidHom.range_eq_top, Subgroup, Subgroup.closure_univ, closure_univ, hf.range_eq, range_eq, range_eq_top, range_lift_eq_closure
-/
theorem lift_surjective_of_surjective (hf : Function.Surjective f) :
    Function.Surjective (lift f) := by
  rw [← MonoidHom.range_eq_top]; rw [range_lift_eq_closure]; rw [hf.range_eq]; rw [Subgroup.closure_univ]

end lift

section Map

variable {β : Type v} (f : α -> β) {x y : FreeGroup α}

set_option backward.isDefEq.respectTransparency false in
/-- Any function from `α` to `β` extends uniquely to a group homomorphism from the free group over
  `α` to the free group over `β`. -/
@[to_additive /-- Any function from `α` to `β` extends uniquely to an additive group homomorphism
from the additive free group over `α` to the additive free group over `β`. -/]
/--
Definition of `map` / `map` 的定义

English:
definition map
  signature: : FreeGroup α ->* FreeGroup β
  body: MonoidHom.mk'
    (Quot.map (List.map fun x => (f x.1, x.2)) fun L₁ L₂ H => by cases H; simp)
    (by rintro ⟨L₁⟩ ⟨L₂⟩; simp)

中文:
定义 map
  签名: : 自由群 α ->* 自由群 β
  定义体: MonoidHom.mk'
    (Quot.map (List.map fun x => (f x.1, x.2)) fun L₁ L₂ H => by cases H; simp)
    (by rintro ⟨L₁⟩ ⟨L₂⟩; simp)

Depends on / 依赖: List.map, MonoidHom, MonoidHom.mk, Quot.map
-/
def map : FreeGroup α ->* FreeGroup β :=
  MonoidHom.mk'
    (Quot.map (List.map fun x => (f x.1, x.2)) fun L₁ L₂ H => by cases H; simp)
    (by rintro ⟨L₁⟩ ⟨L₂⟩; simp)

variable {f}

@[to_additive (attr := simp)]
/--
theorem `map.mk` / 定理 `map.mk`

English:
theorem map.mk
  statement: map f (mk L) = mk (L.map fun x => (f x.1, x.2))
  proof: rfl

@[to_additive (attr := simp)]

中文:
定理 map.mk
  结论: map f (mk L) = mk (L.map fun x => (f x.1, x.2))
  证明: rfl

@[to_additive (attr := simp)]
-/
theorem map.mk : map f (mk L) = mk (L.map fun x => (f x.1, x.2)) :=
  rfl

@[to_additive (attr := simp)]
/--
theorem `map.id` / 定理 `map.id`

English:
theorem map.id
  given: (x : FreeGroup α)
  statement: map id x = x
  proof: by rcases x with ⟨L⟩; simp [List.map_id']

@[to_additive (attr := simp)]

中文:
定理 map.id
  条件: (x : 自由群 α)
  结论: map id x = x
  证明: by rcases x with ⟨L⟩; simp [List.map_id']

@[to_additive (attr := simp)]

Depends on / 依赖: List.map_id, map_id
-/
theorem map.id (x : FreeGroup α) : map id x = x := by rcases x with ⟨L⟩; simp [List.map_id']

@[to_additive (attr := simp)]
/--
theorem `map.id'` / 定理 `map.id'`

English:
theorem map.id'
  given: (x : FreeGroup α)
  statement: map (fun z => z) x = x
  proof: map.id x

@[to_additive]

中文:
定理 map.id'
  条件: (x : 自由群 α)
  结论: map (fun z => z) x = x
  证明: map.id x

@[to_additive]

Depends on / 依赖: map.id
-/
theorem map.id' (x : FreeGroup α) : map (fun z => z) x = x :=
  map.id x

@[to_additive]
/--
theorem `map.comp` / 定理 `map.comp`

English:
theorem map.comp
  given: {γ : Type w} (f : α -> β) (g : β -> γ) (x)
  proof: by
  rcases x with ⟨L⟩; simp [Function.comp_def]

@[to_additive (attr := simp)]

中文:
定理 map.comp
  条件: {γ : 类型 w} (f : α -> β) (g : β -> γ) (x)
  证明: by
  rcases x with ⟨L⟩; simp [Function.comp_def]

@[to_additive (attr := simp)]

Depends on / 依赖: Function, Function.comp_def, comp_def
-/
theorem map.comp {γ : Type w} (f : α -> β) (g : β -> γ) (x) :
    map g (map f x) = map (g ∘ f) x := by
  rcases x with ⟨L⟩; simp [Function.comp_def]

@[to_additive (attr := simp)]
/--
theorem `map.of` / 定理 `map.of`

English:
theorem map.of
  given: {x}
  statement: map f (of x) = of (f x)
  proof: rfl

@[to_additive]

中文:
定理 map.of
  条件: {x}
  结论: map f (of x) = of (f x)
  证明: rfl

@[to_additive]
-/
theorem map.of {x} : map f (of x) = of (f x) :=
  rfl

@[to_additive]
/--
theorem `map.unique` / 定理 `map.unique`

English:
theorem map.unique
  statement: (g : FreeGroup α ->* FreeGroup β)
  proof: by
  rintro ⟨L⟩
  exact List.recOn L g.map_one fun ⟨x, b⟩ t (ih : g (FreeGroup.mk t) = map f (FreeGroup.mk t)) =>
    Bool.recOn b
      (show g ((FreeGroup.of x)⁻¹ * FreeGroup.mk t) =
          FreeGroup.map f ((FreeGroup.of x)⁻¹ * FreeGroup.mk t) by
        simp [g.map_mul, g.map_inv, hg, ih])
   

中文:
定理 map.unique
  结论: (g : 自由群 α ->* 自由群 β)
  证明: by
  rintro ⟨L⟩
  exact List.recOn L g.map_one fun ⟨x, b⟩ t (ih : g (FreeGroup.mk t) = map f (FreeGroup.mk t)) =>
    Bool.recOn b
      (show g ((FreeGroup.of x)⁻¹ * FreeGroup.mk t) =
          FreeGroup.map f ((FreeGroup.of x)⁻¹ * FreeGroup.mk t) by
        simp [g.map_mul, g.map_inv, hg, ih])
   

Depends on / 依赖: Bool.recOn, FreeGroup, FreeGroup.map, FreeGroup.mk, FreeGroup.of, List.recOn, g.map_inv, g.map_mul, g.map_one, map_inv, map_mul, map_one
-/
theorem map.unique (g : FreeGroup α ->* FreeGroup β)
    (hg : forall x, g (FreeGroup.of x) = FreeGroup.of (f x)) :
    forall {x}, g x = map f x := by
  rintro ⟨L⟩
  exact List.recOn L g.map_one fun ⟨x, b⟩ t (ih : g (FreeGroup.mk t) = map f (FreeGroup.mk t)) =>
    Bool.recOn b
      (show g ((FreeGroup.of x)⁻¹ * FreeGroup.mk t) =
          FreeGroup.map f ((FreeGroup.of x)⁻¹ * FreeGroup.mk t) by
        simp [g.map_mul, g.map_inv, hg, ih])
      (show g (FreeGroup.of x * FreeGroup.mk t) =
          FreeGroup.map f (FreeGroup.of x * FreeGroup.mk t) by simp [g.map_mul, hg, ih])

@[to_additive]
/--
theorem `map_eq_lift` / 定理 `map_eq_lift`

English:
theorem map_eq_lift
  statement: map f = lift (of ∘ f)
  proof: by
  ext; simp

@[to_additive]

中文:
定理 map_eq_lift
  结论: map f = lift (of ∘ f)
  证明: by
  ext; simp

@[to_additive]
-/
theorem map_eq_lift : map f = lift (of ∘ f) := by
  ext; simp

@[to_additive]
/--
theorem `range_map` / 定理 `range_map`

English:
theorem range_map
  statement: (map f).range = Subgroup.closure (of '' Set.range f)
  proof: by
  rw [map_eq_lift]; rw [range_lift_eq_closure]; rw [Set.range_comp]

中文:
定理 range_map
  结论: (map f).range = 子群.closure (of '' 集合.range f)
  证明: by
  rw [map_eq_lift]; rw [range_lift_eq_closure]; rw [Set.range_comp]

Depends on / 依赖: Set.range_comp, map_eq_lift, range_comp, range_lift_eq_closure
-/
theorem range_map : (map f).range = Subgroup.closure (of '' Set.range f) := by
  rw [map_eq_lift]; rw [range_lift_eq_closure]; rw [Set.range_comp]

/-- If `α` and `β` are arbitrary types and there is a surjection between them,
then the induced map on their free groups is also surjective. -/
@[to_additive /-- If `α` and `β` are arbitrary types and there is a surjection between them,
then the induced map on their additive free groups is also surjective. -/]
/--
theorem `map_surjective` / 定理 `map_surjective`

English:
theorem map_surjective
  given: (hf : Function.Surjective f)
  statement: Function.Surjective (map f)
  proof: by
  rw [← MonoidHom.range_eq_top]; rw [range_map]; rw [hf.range_eq]; rw [Set.image_univ]; rw [closure_range_of]

中文:
定理 map_surjective
  条件: (hf : 函数.满射 f)
  结论: 函数.满射 (map f)
  证明: by
  rw [← MonoidHom.range_eq_top]; rw [range_map]; rw [hf.range_eq]; rw [Set.image_univ]; rw [closure_range_of]

Depends on / 依赖: MonoidHom, MonoidHom.range_eq_top, Set.image_univ, closure_range_of, hf.range_eq, image_univ, range_eq, range_eq_top, range_map
-/
theorem map_surjective (hf : Function.Surjective f) : Function.Surjective (map f) := by
  rw [← MonoidHom.range_eq_top]; rw [range_map]; rw [hf.range_eq]; rw [Set.image_univ]; rw [closure_range_of]

/-- If `α` and `β` are arbitrary types and there is an injection between them,
then the induced map on their free groups is also injective. -/
@[to_additive /-- If `α` and `β` are arbitrary types and there is an injection between them,
then the induced map on their additive free groups is also injective. -/]
/--
theorem `map_injective` / 定理 `map_injective`

English:
theorem map_injective
  given: (hf : Function.Injective f)
  statement: Function.Injective (map f)
  proof: by
  by_cases! h : IsEmpty α
  · exact Function.injective_of_subsingleton _
  · rw [Function.injective_iff_hasLeftInverse]
    use map (Function.invFun f)
    simp [Function.LeftInverse, map.comp, Function.invFun_comp hf]

中文:
定理 map_injective
  条件: (hf : 函数.单射 f)
  结论: 函数.单射 (map f)
  证明: by
  by_cases! h : IsEmpty α
  · exact Function.injective_of_subsingleton _
  · rw [Function.injective_iff_hasLeftInverse]
    use map (Function.invFun f)
    simp [Function.LeftInverse, map.comp, Function.invFun_comp hf]

Depends on / 依赖: Function, Function.LeftInverse, Function.injective_iff_hasLeftInverse, Function.injective_of_subsingleton, Function.invFun, Function.invFun_comp, IsEmpty, LeftInverse, injective_iff_hasLeftInverse, injective_of_subsingleton, invFun, invFun_comp, map.comp
-/
theorem map_injective (hf : Function.Injective f) : Function.Injective (map f) := by
  by_cases! h : IsEmpty α
  · exact Function.injective_of_subsingleton _
  · rw [Function.injective_iff_hasLeftInverse]
    use map (Function.invFun f)
    simp [Function.LeftInverse, map.comp, Function.invFun_comp hf]

/-- If `α` and `β` are arbitrary types and there is a bijection between them,
then the induced map on their free groups is also bijective. -/
@[to_additive /-- If `α` and `β` are arbitrary types and there is a bijection between them,
then the induced map on their additive free groups is also bijective. -/]
/--
theorem `map_bijective` / 定理 `map_bijective`

English:
theorem map_bijective
  given: (hf : Function.Bijective f)
  statement: Function.Bijective (map f)
  proof: by
  exact ⟨map_injective hf.injective, map_surjective hf.surjective⟩

中文:
定理 map_bijective
  条件: (hf : 函数.双射 f)
  结论: 函数.双射 (map f)
  证明: by
  exact ⟨map_injective hf.injective, map_surjective hf.surjective⟩

Depends on / 依赖: hf.injective, hf.surjective, injective, map_injective, map_surjective, surjective
-/
theorem map_bijective (hf : Function.Bijective f) : Function.Bijective (map f) := by
  exact ⟨map_injective hf.injective, map_surjective hf.surjective⟩

/-- Equivalent types give rise to multiplicatively equivalent free groups.

The converse can be found in `Mathlib/GroupTheory/FreeGroup/GeneratorEquiv.lean`, as
`Equiv.ofFreeGroupEquiv`. -/
@[to_additive (attr := simps apply)
  /-- Equivalent types give rise to additively equivalent additive free groups. -/]
/--
Definition of `freeGroupCongr` / `freeGroupCongr` 的定义

English:
definition freeGroupCongr
  signature: {α β} (e : α ≃ β)
  body: map e
  invFun := map e.symm
  left_inv x := by simp [map.comp]
  right_inv x := by simp [map.comp]
  map_mul' := map_mul _

@[to_additive (attr := simp)]

中文:
定义 freeGroupCongr
  签名: {α β} (e : α ≃ β)
  定义体: map e
  invFun := map e.symm
  left_inv x := by simp [map.comp]
  right_inv x := by simp [map.comp]
  map_mul' := map_mul _

@[to_additive (attr := simp)]
-/
def freeGroupCongr {α β} (e : α ≃ β) : FreeGroup α ≃* FreeGroup β where
  toFun := map e
  invFun := map e.symm
  left_inv x := by simp [map.comp]
  right_inv x := by simp [map.comp]
  map_mul' := map_mul _

@[to_additive (attr := simp)]
/--
theorem `freeGroupCongr_refl` / 定理 `freeGroupCongr_refl`

English:
theorem freeGroupCongr_refl
  statement: freeGroupCongr (Equiv.refl α) = MulEquiv.refl _
  proof: MulEquiv.ext map.id

@[to_additive (attr := simp)]

中文:
定理 freeGroupCongr_refl
  结论: freeGroupCongr (等价.refl α) = 乘法等价.refl _
  证明: MulEquiv.ext map.id

@[to_additive (attr := simp)]

Depends on / 依赖: MulEquiv, MulEquiv.ext, map.id
-/
theorem freeGroupCongr_refl : freeGroupCongr (Equiv.refl α) = MulEquiv.refl _ :=
  MulEquiv.ext map.id

@[to_additive (attr := simp)]
/--
theorem `freeGroupCongr_symm` / 定理 `freeGroupCongr_symm`

English:
theorem freeGroupCongr_symm
  given: {α β} (e : α ≃ β)
  statement: (freeGroupCongr e).symm = freeGroupCongr e.symm
  proof: rfl

@[to_additive]

中文:
定理 freeGroupCongr_symm
  条件: {α β} (e : α ≃ β)
  结论: (freeGroupCongr e).symm = freeGroupCongr e.symm
  证明: rfl

@[to_additive]
-/
theorem freeGroupCongr_symm {α β} (e : α ≃ β) : (freeGroupCongr e).symm = freeGroupCongr e.symm :=
  rfl

@[to_additive]
/--
theorem `freeGroupCongr_trans` / 定理 `freeGroupCongr_trans`

English:
theorem freeGroupCongr_trans
  given: {α β γ} (e : α ≃ β) (f : β ≃ γ)
  proof: MulEquiv.ext map.comp _ _

中文:
定理 freeGroupCongr_trans
  条件: {α β γ} (e : α ≃ β) (f : β ≃ γ)
  证明: MulEquiv.ext map.comp _ _

Depends on / 依赖: MulEquiv, MulEquiv.ext, map.comp
-/
theorem freeGroupCongr_trans {α β γ} (e : α ≃ β) (f : β ≃ γ) :
    (freeGroupCongr e).trans (freeGroupCongr f) = freeGroupCongr (e.trans f) :=
MulEquiv.ext map.comp _ _

end Map

section Prod

variable [Group α] (x y : FreeGroup α)

/-- If `α` is a group, then any function from `α` to `α` extends uniquely to a homomorphism from the
free group over `α` to `α`. This is the multiplicative version of `FreeGroup.sum`. -/
@[to_additive /-- If `α` is an additive group, then any function from `α` to `α` extends uniquely
  to an additive homomorphism from the additive free group over `α` to `α`. -/]
/--
Definition of `prod` / `prod` 的定义

English:
definition prod
  signature: : FreeGroup α ->* α
  body: lift id

中文:
定义 乘积
  签名: : 自由群 α ->* α
  定义体: lift id
-/
def prod : FreeGroup α ->* α :=
  lift id

variable {x y}

@[to_additive (attr := simp)]
/--
theorem `prod_mk` / 定理 `prod_mk`

English:
theorem prod_mk
  statement: prod (mk L) = List.prod (L.map fun x => cond x.2 x.1 x.1⁻¹)
  proof: rfl

@[to_additive (attr := simp)]

中文:
定理 prod_mk
  结论: 乘积 (mk L) = 列表.乘积 (L.map fun x => cond x.2 x.1 x.1⁻¹)
  证明: rfl

@[to_additive (attr := simp)]
-/
theorem prod_mk : prod (mk L) = List.prod (L.map fun x => cond x.2 x.1 x.1⁻¹) :=
  rfl

@[to_additive (attr := simp)]
/--
theorem `prod.of` / 定理 `prod.of`

English:
theorem prod.of
  given: {x : α}
  statement: prod (of x) = x
  proof: lift_apply_of

@[to_additive]

中文:
定理 乘积.of
  条件: {x : α}
  结论: 乘积 (of x) = x
  证明: lift_apply_of

@[to_additive]

Depends on / 依赖: lift_apply_of
-/
theorem prod.of {x : α} : prod (of x) = x :=
  lift_apply_of

@[to_additive]
/--
theorem `prod.unique` / 定理 `prod.unique`

English:
theorem prod.unique
  given: (g : FreeGroup α ->* α) (hg : forall x, g (FreeGroup.of x) = x) {x}
  statement: g x = prod x
  proof: lift_unique g hg

@[to_additive]

中文:
定理 乘积.unique
  条件: (g : 自由群 α ->* α) (hg : 对任意 x, g (自由群.of x) = x) {x}
  结论: g x = 乘积 x
  证明: lift_unique g hg

@[to_additive]

Depends on / 依赖: lift_unique
-/
theorem prod.unique (g : FreeGroup α ->* α) (hg : forall x, g (FreeGroup.of x) = x) {x} : g x = prod x :=
  lift_unique g hg

@[to_additive]
/--
theorem `prod_surjective` / 定理 `prod_surjective`

English:
theorem prod_surjective
  statement: Function.Surjective (prod : FreeGroup α ->* α)
  proof: FreeGroup.lift_surjective_of_surjective Function.surjective_id

中文:
定理 prod_surjective
  结论: 函数.满射 (乘积 : 自由群 α ->* α)
  证明: FreeGroup.lift_surjective_of_surjective Function.surjective_id

Depends on / 依赖: FreeGroup, FreeGroup.lift_surjective_of_surjective, Function, Function.surjective_id, lift_surjective_of_surjective, surjective_id
-/
theorem prod_surjective : Function.Surjective (prod : FreeGroup α ->* α) :=
  FreeGroup.lift_surjective_of_surjective Function.surjective_id

end Prod

@[to_additive]
/--
theorem `lift_eq_prod_map` / 定理 `lift_eq_prod_map`

English:
theorem lift_eq_prod_map
  given: {β : Type v} [Group β] {f : α -> β} {x}
  statement: lift f x = prod (map f x)
  proof: by
  rw [← lift_unique (prod.comp (map f)) (by simp)]; rw [MonoidHom.coe_comp]; rw [Function.comp_apply]

中文:
定理 lift_eq_prod_map
  条件: {β : 类型v} [群 β] {f : α -> β} {x}
  结论: lift f x = 乘积 (map f x)
  证明: by
  rw [← lift_unique (prod.comp (map f)) (by simp)]; rw [MonoidHom.coe_comp]; rw [Function.comp_apply]

Depends on / 依赖: Function, Function.comp_apply, MonoidHom, MonoidHom.coe_comp, coe_comp, comp_apply, lift_unique, prod.comp
-/
theorem lift_eq_prod_map {β : Type v} [Group β] {f : α -> β} {x} : lift f x = prod (map f x) := by
  rw [← lift_unique (prod.comp (map f)) (by simp)]; rw [MonoidHom.coe_comp]; rw [Function.comp_apply]

section Sum

variable [AddGroup α] (x y : FreeGroup α)

/--
Definition of `sum` / `sum` 的定义

English:
definition sum
  signature: : α
  body: @prod (Multiplicative _) _ x

中文:
定义 求和
  签名: : α
  定义体: @prod (Multiplicative _) _ x

Depends on / 依赖: Multiplicative
-/
def sum : α :=
  @prod (Multiplicative _) _ x

variable {x y}

@[simp]
/--
theorem `sum_mk` / 定理 `sum_mk`

English:
theorem sum_mk
  statement: sum (mk L) = List.sum (L.map fun x => cond x.2 x.1 (-x.1))
  proof: rfl

@[simp]

中文:
定理 sum_mk
  结论: 求和 (mk L) = 列表.求和 (L.map fun x => cond x.2 x.1 (-x.1))
  证明: rfl

@[simp]
-/
theorem sum_mk : sum (mk L) = List.sum (L.map fun x => cond x.2 x.1 (-x.1)) :=
  rfl

@[simp]
/--
theorem `sum.of` / 定理 `sum.of`

English:
theorem sum.of
  given: {x : α}
  statement: sum (of x) = x
  proof: @prod.of _ (_) _

中文:
定理 求和.of
  条件: {x : α}
  结论: 求和 (of x) = x
  证明: @prod.of _ (_) _

Depends on / 依赖: prod.of
-/
theorem sum.of {x : α} : sum (of x) = x :=
  @prod.of _ (_) _

-- note: there are no bundled homs with different notation in the domain and codomain, so we copy
-- these manually
@[simp]
/--
theorem `sum.map_mul` / 定理 `sum.map_mul`

English:
theorem sum.map_mul
  statement: sum (x * y) = sum x + sum y
  proof: (@prod (Multiplicative _) _).map_mul _ _

@[simp]

中文:
定理 求和.map_mul
  结论: 求和 (x * y) = 求和 x + 求和 y
  证明: (@prod (Multiplicative _) _).map_mul _ _

@[simp]

Depends on / 依赖: Multiplicative, map_mul
-/
theorem sum.map_mul : sum (x * y) = sum x + sum y :=
  (@prod (Multiplicative _) _).map_mul _ _

@[simp]
/--
theorem `sum.map_one` / 定理 `sum.map_one`

English:
theorem sum.map_one
  statement: sum (1 : FreeGroup α) = 0
  proof: (@prod (Multiplicative _) _).map_one

@[simp]

中文:
定理 求和.map_one
  结论: 求和 (1 : 自由群 α) = 0
  证明: (@prod (Multiplicative _) _).map_one

@[simp]

Depends on / 依赖: Multiplicative, map_one
-/
theorem sum.map_one : sum (1 : FreeGroup α) = 0 :=
  (@prod (Multiplicative _) _).map_one

@[simp]
/--
theorem `sum.map_inv` / 定理 `sum.map_inv`

English:
theorem sum.map_inv
  statement: sum x⁻¹ = -sum x
  proof: (prod : FreeGroup (Multiplicative α) ->* Multiplicative α).map_inv _

中文:
定理 求和.map_inv
  结论: 求和 x⁻¹ = -求和 x
  证明: (prod : FreeGroup (Multiplicative α) ->* Multiplicative α).map_inv _

Depends on / 依赖: FreeGroup, Multiplicative, map_inv
-/
theorem sum.map_inv : sum x⁻¹ = -sum x :=
  (prod : FreeGroup (Multiplicative α) ->* Multiplicative α).map_inv _

end Sum

/-- The bijection between the free group on the empty type, and a type with one element. -/
@[to_additive
  (attr := deprecated "Use `Equiv.ofUnique (FreeGroup Empty) Unit` instead,
or `MulEquiv.ofUnique (FreeGroup Empty) Unit` for the multiplicative version instead."
(since := "2026-02-11"))
  /-- The bijection between the additive free group on the empty type,
  and a type with one element. -/]
/--
Definition of `freeGroupEmptyEquivUnit` / `freeGroupEmptyEquivUnit` 的定义

English:
abbreviation freeGroupEmptyEquivUnit
  signature: : FreeGroup Empty ≃ Unit
  body: Equiv.ofUnique (FreeGroup Empty) Unit

中文:
缩写 freeGroupEmptyEquivUnit
  签名: : 自由群 空 ≃ 单元
  定义体: Equiv.ofUnique (FreeGroup Empty) Unit

Depends on / 依赖: Equiv.ofUnique, FreeGroup, ofUnique
-/
abbrev freeGroupEmptyEquivUnit : FreeGroup Empty ≃ Unit :=
  Equiv.ofUnique (FreeGroup Empty) Unit

/--
Definition of `freeGroupUnitEquivInt` / `freeGroupUnitEquivInt` 的定义

English:
definition freeGroupUnitEquivInt
  signature: : FreeGroup Unit ≃ Int where
  body: sum (by
    revert x
    exact ↑(map fun _ => (1 : Int)))
  invFun x := of () ^ x
  left_inv := by
    rintro ⟨L⟩
    simp only [quot_mk_eq_mk, map.mk, sum_mk, List.map_map]
    exact List.recOn L
     rfl
     (fun ⟨⟨⟩, b⟩ tl ih => by
        cases b <;> simp [zpow_add, ih] <;> rfl)
  right_inv x :

中文:
定义 freeGroupUnitEquiv整数
  签名: : 自由群 单元 ≃ 整数 where
  定义体: sum (by
    revert x
    exact ↑(map fun _ => (1 : Int)))
  invFun x := of () ^ x
  left_inv := by
    rintro ⟨L⟩
    simp only [quot_mk_eq_mk, map.mk, sum_mk, List.map_map]
    exact List.recOn L
     rfl
     (fun ⟨⟨⟩, b⟩ tl ih => by
        cases b <;> simp [zpow_add, ih] <;> rfl)
  right_inv x :

Depends on / 依赖: Int.induction_on, List.map_map, List.recOn, induction_on, invFun, left_inv, map.mk, map.of, map_inv, map_map, map_pow, neg_inj, quot_mk_eq_mk, revert, right_inv, sum.map_inv, sum_mk, zpow_add, zpow_natCast, zpow_neg
-/
def freeGroupUnitEquivInt : FreeGroup Unit ≃ Int where
  toFun x := sum (by
    revert x
    exact ↑(map fun _ => (1 : Int)))
  invFun x := of () ^ x
  left_inv := by
    rintro ⟨L⟩
    simp only [quot_mk_eq_mk, map.mk, sum_mk, List.map_map]
    exact List.recOn L
     rfl
     (fun ⟨⟨⟩, b⟩ tl ih => by
        cases b <;> simp [zpow_add, ih] <;> rfl)
  right_inv x :=
    Int.induction_on x (by simp)
      (fun i ih => by
        simp only [zpow_natCast, map_pow, map.of] at ih
        simp [zpow_add, ih])
      (fun i ih => by
        simp only [zpow_neg, zpow_natCast, map_inv, map_pow, map.of, sum.map_inv, neg_inj] at ih
        simp [zpow_add, ih, sub_eq_add_neg])

/--
Definition of `equivIntOfUnique` / `equivIntOfUnique` 的定义

English:
definition equivIntOfUnique
  signature: [Unique α]
  body: sum (map 1 x)
  invFun x := of default ^ x
  left_inv x := by
    induction x with
    | C1 => simp
    | of x => simp [Unique.default_eq x]
    | inv_of x hx => simp [Unique.default_eq x]
    | mul x y hx hy => simp [zpow_add, hx, hy]
  right_inv x := by
    induction x with
    | zero => simp
    

中文:
定义 equiv整数OfUnique
  签名: [唯一 α]
  定义体: sum (map 1 x)
  invFun x := of default ^ x
  left_inv x := by
    induction x with
    | C1 => simp
    | of x => simp [Unique.default_eq x]
    | inv_of x hx => simp [Unique.default_eq x]
    | mul x y hx hy => simp [zpow_add, hx, hy]
  right_inv x := by
    induction x with
    | zero => simp
    
-/
def equivIntOfUnique [Unique α] : FreeGroup α ≃ Int where
  toFun x := sum (map 1 x)
  invFun x := of default ^ x
  left_inv x := by
    induction x with
    | C1 => simp
    | of x => simp [Unique.default_eq x]
    | inv_of x hx => simp [Unique.default_eq x]
    | mul x y hx hy => simp [zpow_add, hx, hy]
  right_inv x := by
    induction x with
    | zero => simp
    | succ x hx => simpa [zpow_add_one] using hx
    | pred x hx => simpa [zpow_sub_one, ← sub_eq_add_neg] using hx

set_option backward.isDefEq.respectTransparency false in
/--
Definition of `mulEquivIntOfUnique` / `mulEquivIntOfUnique` 的定义

English:
definition mulEquivIntOfUnique
  signature: [Unique α]
  body: Multiplicative.ofAdd ∘ equivIntOfUnique
  invFun := equivIntOfUnique.symm ∘ Multiplicative.toAdd
  left_inv _ := by simp
  right_inv _ := by simp
  map_mul' _ _ := by simp [equivIntOfUnique]

中文:
定义 mulEquiv整数OfUnique
  签名: [唯一 α]
  定义体: Multiplicative.ofAdd ∘ equivIntOfUnique
  invFun := equivIntOfUnique.symm ∘ Multiplicative.toAdd
  left_inv _ := by simp
  right_inv _ := by simp
  map_mul' _ _ := by simp [equivIntOfUnique]

Depends on / 依赖: Multiplicative, Multiplicative.ofAdd, equivIntOfUnique
-/
def mulEquivIntOfUnique [Unique α] : FreeGroup α ≃* Multiplicative Int where
  toFun := Multiplicative.ofAdd ∘ equivIntOfUnique
  invFun := equivIntOfUnique.symm ∘ Multiplicative.toAdd
  left_inv _ := by simp
  right_inv _ := by simp
  map_mul' _ _ := by simp [equivIntOfUnique]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Unique
  signature: α] : IsCyclic (FreeGroup α)
  body: ⟨of default, fun x => ⟨equivIntOfUnique x, equivIntOfUnique.left_inv x⟩⟩

中文:
实例 [唯一
  签名: α] : 是循环 (自由群 α)
  定义体: ⟨of default, fun x => ⟨equivIntOfUnique x, equivIntOfUnique.left_inv x⟩⟩

Depends on / 依赖: equivIntOfUnique, equivIntOfUnique.left_inv, left_inv
-/
instance [Unique α] : IsCyclic (FreeGroup α) :=
  ⟨of default, fun x => ⟨equivIntOfUnique x, equivIntOfUnique.left_inv x⟩⟩

/--
Definition of `_root_.FreeAddGroup.addEquivIntOfUnique` / `_root_.FreeAddGroup.addEquivIntOfUnique` 的定义

English:
definition _root_.FreeAddGroup.addEquivIntOfUnique
  signature: [Unique α]
  body: FreeAddGroup.sum (FreeAddGroup.map 1 x)
  invFun x := x • FreeAddGroup.of default
  left_inv x := by
    induction x with
    | C1 => simp
    | of x => simp [Unique.default_eq x]
    | neg_of x hx => simp [Unique.default_eq x]
    | add x y hx hy => simp [add_zsmul, hx, hy]
  right_inv x := by indu

中文:
定义 _root_.自由加法群.addEquiv整数OfUnique
  签名: [唯一 α]
  定义体: FreeAddGroup.sum (FreeAddGroup.map 1 x)
  invFun x := x • FreeAddGroup.of default
  left_inv x := by
    induction x with
    | C1 => simp
    | of x => simp [Unique.default_eq x]
    | neg_of x hx => simp [Unique.default_eq x]
    | add x y hx hy => simp [add_zsmul, hx, hy]
  right_inv x := by indu

Depends on / 依赖: FreeAddGroup, FreeAddGroup.map, FreeAddGroup.sum
-/
def _root_.FreeAddGroup.addEquivIntOfUnique [Unique α] : FreeAddGroup α ≃+ Int where
  toFun x := FreeAddGroup.sum (FreeAddGroup.map 1 x)
  invFun x := x • FreeAddGroup.of default
  left_inv x := by
    induction x with
    | C1 => simp
    | of x => simp [Unique.default_eq x]
    | neg_of x hx => simp [Unique.default_eq x]
    | add x y hx hy => simp [add_zsmul, hx, hy]
  right_inv x := by induction x <;> simp
  map_add' x y := by simp

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Unique
  signature: α] : IsAddCyclic (FreeAddGroup α)
  body: ⟨FreeAddGroup.of default, fun x =>
  ⟨_root_.FreeAddGroup.addEquivIntOfUnique x, _root_.FreeAddGroup.addEquivIntOfUnique.left_inv x⟩⟩

中文:
实例 [唯一
  签名: α] : 是加法循环 (自由加法群 α)
  定义体: ⟨FreeAddGroup.of default, fun x =>
  ⟨_root_.FreeAddGroup.addEquivIntOfUnique x, _root_.FreeAddGroup.addEquivIntOfUnique.left_inv x⟩⟩

Depends on / 依赖: FreeAddGroup, FreeAddGroup.of, _root_, _root_.FreeAddGroup.addEquivIntOfUnique, _root_.FreeAddGroup.addEquivIntOfUnique.left_inv, addEquivIntOfUnique, left_inv
-/
instance [Unique α] : IsAddCyclic (FreeAddGroup α) :=
  ⟨FreeAddGroup.of default, fun x =>
  ⟨_root_.FreeAddGroup.addEquivIntOfUnique x, _root_.FreeAddGroup.addEquivIntOfUnique.left_inv x⟩⟩

section Category

variable {β : Type u}

@[to_additive]
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Monad FreeGroup.{u}
  body: of
  map {_α _β f} := map f
  bind {_α _β x f} := lift f x

@[to_additive]

中文:
实例 :
  签名: 单子 自由群.{u}
  定义体: of
  map {_α _β f} := map f
  bind {_α _β x f} := lift f x

@[to_additive]
-/
instance : Monad FreeGroup.{u} where
  pure {_α} := of
  map {_α _β f} := map f
  bind {_α _β x f} := lift f x

@[to_additive]
/--
theorem `map_pure` / 定理 `map_pure`

English:
theorem map_pure
  given: (f : α -> β) (x : α)
  statement: f < > (pure x : FreeGroup α) = pure (f x)
  proof: map.of

@[to_additive (attr := simp)]

中文:
定理 map_pure
  条件: (f : α -> β) (x : α)
  结论: f < > (pure x : 自由群 α) = pure (f x)
  证明: map.of

@[to_additive (attr := simp)]

Depends on / 依赖: map.of
-/
theorem map_pure (f : α -> β) (x : α) : f < > (pure x : FreeGroup α) = pure (f x) :=
  map.of

@[to_additive (attr := simp)]
/--
theorem `map_one` / 定理 `map_one`

English:
theorem map_one
  given: (f : α -> β)
  statement: f < > (1 : FreeGroup α) = 1
  proof: (map f).map_one

@[to_additive (attr := simp)]

中文:
定理 map_one
  条件: (f : α -> β)
  结论: f < > (1 : 自由群 α) = 1
  证明: (map f).map_one

@[to_additive (attr := simp)]

Depends on / 依赖: map_one
-/
theorem map_one (f : α -> β) : f < > (1 : FreeGroup α) = 1 :=
  (map f).map_one

@[to_additive (attr := simp)]
/--
theorem `map_mul` / 定理 `map_mul`

English:
theorem map_mul
  given: (f : α -> β) (x y : FreeGroup α)
  statement: f < > (x * y) = f < > x * f < > y
  proof: (map f).map_mul x y

@[to_additive (attr := simp)]

中文:
定理 map_mul
  条件: (f : α -> β) (x y : 自由群 α)
  结论: f < > (x * y) = f < > x * f < > y
  证明: (map f).map_mul x y

@[to_additive (attr := simp)]

Depends on / 依赖: map_mul
-/
theorem map_mul (f : α -> β) (x y : FreeGroup α) : f < > (x * y) = f < > x * f < > y :=
  (map f).map_mul x y

@[to_additive (attr := simp)]
/--
theorem `map_inv` / 定理 `map_inv`

English:
theorem map_inv
  given: (f : α -> β) (x : FreeGroup α)
  statement: f < > x⁻¹ = (f <$> x)⁻¹
  proof: (map f).map_inv x

@[to_additive]

中文:
定理 map_inv
  条件: (f : α -> β) (x : 自由群 α)
  结论: f < > x⁻¹ = (f <$> x)⁻¹
  证明: (map f).map_inv x

@[to_additive]

Depends on / 依赖: map_inv
-/
theorem map_inv (f : α -> β) (x : FreeGroup α) : f < > x⁻¹ = (f <$> x)⁻¹ :=
  (map f).map_inv x

@[to_additive]
/--
theorem `pure_bind` / 定理 `pure_bind`

English:
theorem pure_bind
  given: (f : α -> FreeGroup β) (x)
  statement: pure x >>= f = f x
  proof: lift_apply_of

@[to_additive (attr := simp)]

中文:
定理 pure_bind
  条件: (f : α -> 自由群 β) (x)
  结论: pure x >>= f = f x
  证明: lift_apply_of

@[to_additive (attr := simp)]

Depends on / 依赖: lift_apply_of
-/
theorem pure_bind (f : α -> FreeGroup β) (x) : pure x >>= f = f x :=
  lift_apply_of

@[to_additive (attr := simp)]
/--
theorem `one_bind` / 定理 `one_bind`

English:
theorem one_bind
  given: (f : α -> FreeGroup β)
  statement: 1 >>= f = 1
  proof: (lift f).map_one

@[to_additive (attr := simp)]

中文:
定理 one_bind
  条件: (f : α -> 自由群 β)
  结论: 1 >>= f = 1
  证明: (lift f).map_one

@[to_additive (attr := simp)]

Depends on / 依赖: map_one
-/
theorem one_bind (f : α -> FreeGroup β) : 1 >>= f = 1 :=
  (lift f).map_one

@[to_additive (attr := simp)]
/--
theorem `mul_bind` / 定理 `mul_bind`

English:
theorem mul_bind
  given: (f : α -> FreeGroup β) (x y : FreeGroup α)
  statement: x * y >>= f = (x >>= f) * (y >>= f)
  proof: (lift f).map_mul _ _

@[to_additive (attr := simp)]

中文:
定理 mul_bind
  条件: (f : α -> 自由群 β) (x y : 自由群 α)
  结论: x * y >>= f = (x >>= f) * (y >>= f)
  证明: (lift f).map_mul _ _

@[to_additive (attr := simp)]

Depends on / 依赖: map_mul
-/
theorem mul_bind (f : α -> FreeGroup β) (x y : FreeGroup α) : x * y >>= f = (x >>= f) * (y >>= f) :=
  (lift f).map_mul _ _

@[to_additive (attr := simp)]
/--
theorem `inv_bind` / 定理 `inv_bind`

English:
theorem inv_bind
  given: (f : α -> FreeGroup β) (x : FreeGroup α)
  statement: x⁻¹ >>= f = (x >>= f)⁻¹
  proof: (lift f).map_inv _

@[to_additive]

中文:
定理 inv_bind
  条件: (f : α -> 自由群 β) (x : 自由群 α)
  结论: x⁻¹ >>= f = (x >>= f)⁻¹
  证明: (lift f).map_inv _

@[to_additive]

Depends on / 依赖: map_inv
-/
theorem inv_bind (f : α -> FreeGroup β) (x : FreeGroup α) : x⁻¹ >>= f = (x >>= f)⁻¹ :=
  (lift f).map_inv _

@[to_additive]
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: LawfulMonad FreeGroup.{u}
  body: LawfulMonad.mk'
  (id_map := fun x =>
    FreeGroup.induction_on x (map_one id) (fun x => map_pure id x) (fun x ih => by rw [map_inv, ih])
      fun x y ihx ihy => by rw [map_mul, ihx, ihy])
  (pure_bind := fun x f => pure_bind f x)
  (bind_assoc := fun x => by
    refine FreeGroup.induction_on x ?_

中文:
实例 :
  签名: 合法单子 自由群.{u}
  定义体: LawfulMonad.mk'
  (id_map := fun x =>
    FreeGroup.induction_on x (map_one id) (fun x => map_pure id x) (fun x ih => by rw [map_inv, ih])
      fun x y ihx ihy => by rw [map_mul, ihx, ihy])
  (pure_bind := fun x f => pure_bind f x)
  (bind_assoc := fun x => by
    refine FreeGroup.induction_on x ?_

Depends on / 依赖: LawfulMonad, LawfulMonad.mk
-/
instance : LawfulMonad FreeGroup.{u} := LawfulMonad.mk'
  (id_map := fun x =>
    FreeGroup.induction_on x (map_one id) (fun x => map_pure id x) (fun x ih => by rw [map_inv, ih])
      fun x y ihx ihy => by rw [map_mul, ihx, ihy])
  (pure_bind := fun x f => pure_bind f x)
  (bind_assoc := fun x => by
    refine FreeGroup.induction_on x ?_ ?_ ?_ ?_ <;> simp +instances +contextual [instMonad])
  (bind_pure_comp := fun f x => by
    refine FreeGroup.induction_on x ?_ ?_ ?_ ?_ <;> simp +instances +contextual [instMonad])

end Category

end FreeGroup
