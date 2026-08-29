/-
Copyright (c) 2018 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
module

public import Mathlib.Logic.Function.Iterate
public import Mathlib.Tactic.ApplyFun
public import Mathlib.Data.List.GetD
public import Mathlib.Algebra.Group.Int.Defs
public import Mathlib.Algebra.Group.Nat.Defs
public import Mathlib.Data.List.Basic

/-!
# Turing machine tapes

This file defines the notion of a Turing machine tape, and the operations on it. A tape is a
bidirectional infinite sequence of cells, each of which stores an element of a given alphabet `Γ`.
All but finitely many of the cells are required to hold the blank symbol `default : Γ`.

## Main definitions

* `ListBlank Γ` is the type of one-directional tapes with alphabet `Γ`. Implemented as a quotient
  of `List Γ` by extension by blanks at the end.
* `Tape Γ` is the type of Turing machine tapes with alphabet `Γ`. Implemented as two
  `ListBlank Γ` instances, one for each direction, as well as a head symbol.

-/

@[expose] public section

assert_not_exists MonoidWithZero

open Function (iterate_succ iterate_succ_apply iterate_zero_apply)

namespace Turing

section ListBlank

/--
Definition of `BlankExtends` / `BlankExtends` 的定义

English:
definition BlankExtends
  signature: {Γ} [Inhabited Γ] (l₁ l₂ : List Γ)
  body: exists n, l₂ = l₁ ++ List.replicate n default

@[refl]

中文:
定义 BlankExtends
  签名: {Γ} [Inhabited Γ] (l₁ l₂ : List Γ)
  定义体: exists n, l₂ = l₁ ++ List.replicate n default

@[refl]

Depends on / 依赖: List.replicate, replicate
-/
def BlankExtends {Γ} [Inhabited Γ] (l₁ l₂ : List Γ) : Prop :=
  exists n, l₂ = l₁ ++ List.replicate n default

@[refl]
/--
theorem `BlankExtends.refl` / 定理 `BlankExtends.refl`

English:
theorem BlankExtends.refl
  given: {Γ} [Inhabited Γ] (l : List Γ)
  statement: BlankExtends l l
  proof: ⟨0, by simp⟩

@[trans]

中文:
定理 BlankExtends.refl
  条件: {Γ} [Inhabited Γ] (l : List Γ)
  结论: BlankExtends l l
  证明: ⟨0, by simp⟩

@[trans]
-/
theorem BlankExtends.refl {Γ} [Inhabited Γ] (l : List Γ) : BlankExtends l l :=
  ⟨0, by simp⟩

@[trans]
/--
theorem `BlankExtends.trans` / 定理 `BlankExtends.trans`

English:
theorem BlankExtends.trans
  given: {Γ} [Inhabited Γ] {l₁ l₂ l₃ : List Γ}
  proof: by
  rintro ⟨i, rfl⟩ ⟨j, rfl⟩
  exact ⟨i + j, by simp⟩

中文:
定理 BlankExtends.trans
  条件: {Γ} [Inhabited Γ] {l₁ l₂ l₃ : List Γ}
  证明: by
  rintro ⟨i, rfl⟩ ⟨j, rfl⟩
  exact ⟨i + j, by simp⟩
-/
theorem BlankExtends.trans {Γ} [Inhabited Γ] {l₁ l₂ l₃ : List Γ} :
    BlankExtends l₁ l₂ -> BlankExtends l₂ l₃ -> BlankExtends l₁ l₃ := by
  rintro ⟨i, rfl⟩ ⟨j, rfl⟩
  exact ⟨i + j, by simp⟩

/--
theorem `BlankExtends.below_of_le` / 定理 `BlankExtends.below_of_le`

English:
theorem BlankExtends.below_of_le
  given: {Γ} [Inhabited Γ] {l l₁ l₂ : List Γ}
  proof: by
  rintro ⟨i, rfl⟩ ⟨j, rfl⟩ h; use j - i
  simp only [List.length_append, Nat.add_le_add_iff_left, List.length_replicate] at h
  simp only [← List.replicate_add, Nat.add_sub_cancel' h, List.append_assoc]

中文:
定理 BlankExtends.below_of_le
  条件: {Γ} [Inhabited Γ] {l l₁ l₂ : List Γ}
  证明: by
  rintro ⟨i, rfl⟩ ⟨j, rfl⟩ h; use j - i
  simp only [List.length_append, Nat.add_le_add_iff_left, List.length_replicate] at h
  simp only [← List.replicate_add, Nat.add_sub_cancel' h, List.append_assoc]

Depends on / 依赖: List.append_assoc, List.length_append, List.length_replicate, List.replicate_add, Nat.add_le_add_iff_left, Nat.add_sub_cancel, add_le_add_iff_left, add_sub_cancel, append_assoc, length_append, length_replicate, replicate_add
-/
theorem BlankExtends.below_of_le {Γ} [Inhabited Γ] {l l₁ l₂ : List Γ} :
    BlankExtends l l₁ -> BlankExtends l l₂ -> l₁.length <= l₂.length -> BlankExtends l₁ l₂ := by
  rintro ⟨i, rfl⟩ ⟨j, rfl⟩ h; use j - i
  simp only [List.length_append, Nat.add_le_add_iff_left, List.length_replicate] at h
  simp only [← List.replicate_add, Nat.add_sub_cancel' h, List.append_assoc]

/--
Definition of `BlankExtends.above` / `BlankExtends.above` 的定义

English:
definition BlankExtends.above
  signature: {Γ} [Inhabited Γ] {l l₁ l₂ : List Γ} (h₁ : BlankExtends l l₁)
  body: if h : l₁.length <= l₂.length then ⟨l₂, h₁.below_of_le h₂ h, BlankExtends.refl _⟩
  else ⟨l₁, BlankExtends.refl _, h₂.below_of_le h₁ (le_of_not_ge h)⟩

中文:
定义 BlankExtends.above
  签名: {Γ} [Inhabited Γ] {l l₁ l₂ : List Γ} (h₁ : BlankExtends l l₁)
  定义体: if h : l₁.length <= l₂.length then ⟨l₂, h₁.below_of_le h₂ h, BlankExtends.refl _⟩
  else ⟨l₁, BlankExtends.refl _, h₂.below_of_le h₁ (le_of_not_ge h)⟩

Depends on / 依赖: BlankExtends, BlankExtends.refl, below_of_le, le_of_not_ge, length
-/
def BlankExtends.above {Γ} [Inhabited Γ] {l l₁ l₂ : List Γ} (h₁ : BlankExtends l l₁)
    (h₂ : BlankExtends l l₂) : { l' // BlankExtends l₁ l' ∧ BlankExtends l₂ l' } :=
  if h : l₁.length <= l₂.length then ⟨l₂, h₁.below_of_le h₂ h, BlankExtends.refl _⟩
  else ⟨l₁, BlankExtends.refl _, h₂.below_of_le h₁ (le_of_not_ge h)⟩

/--
theorem `BlankExtends.above_of_le` / 定理 `BlankExtends.above_of_le`

English:
theorem BlankExtends.above_of_le
  given: {Γ} [Inhabited Γ] {l l₁ l₂ : List Γ}
  proof: by
  rintro ⟨i, rfl⟩ ⟨j, e⟩ h; use i - j
  refine List.append_cancel_right (e.symm.trans ?_)
  rw [List.append_assoc]; rw [← List.replicate_add]; rw [Nat.sub_add_cancel]
  apply_fun List.length at e
  simp only [List.length_append, List.length_replicate] at e
  rwa [← Nat.add_le_add_iff_left, e, Nat

中文:
定理 BlankExtends.above_of_le
  条件: {Γ} [Inhabited Γ] {l l₁ l₂ : List Γ}
  证明: by
  rintro ⟨i, rfl⟩ ⟨j, e⟩ h; use i - j
  refine List.append_cancel_right (e.symm.trans ?_)
  rw [List.append_assoc]; rw [← List.replicate_add]; rw [Nat.sub_add_cancel]
  apply_fun List.length at e
  simp only [List.length_append, List.length_replicate] at e
  rwa [← Nat.add_le_add_iff_left, e, Nat

Depends on / 依赖: List.append_assoc, List.append_cancel_right, List.length, List.length_append, List.length_replicate, List.replicate_add, Nat.add_le_add_iff_left, Nat.add_le_add_iff_right, Nat.sub_add_cancel, add_le_add_iff_left, add_le_add_iff_right, append_assoc, append_cancel_right, apply_fun, e.symm.trans, length, length_append, length_replicate, replicate_add, sub_add_cancel
-/
theorem BlankExtends.above_of_le {Γ} [Inhabited Γ] {l l₁ l₂ : List Γ} :
    BlankExtends l₁ l -> BlankExtends l₂ l -> l₁.length <= l₂.length -> BlankExtends l₁ l₂ := by
  rintro ⟨i, rfl⟩ ⟨j, e⟩ h; use i - j
  refine List.append_cancel_right (e.symm.trans ?_)
  rw [List.append_assoc]; rw [← List.replicate_add]; rw [Nat.sub_add_cancel]
  apply_fun List.length at e
  simp only [List.length_append, List.length_replicate] at e
  rwa [← Nat.add_le_add_iff_left, e, Nat.add_le_add_iff_right]

/--
Definition of `BlankRel` / `BlankRel` 的定义

English:
definition BlankRel
  signature: {Γ} [Inhabited Γ] (l₁ l₂ : List Γ)
  body: BlankExtends l₁ l₂ ∨ BlankExtends l₂ l₁

@[refl]

中文:
定义 BlankRel
  签名: {Γ} [Inhabited Γ] (l₁ l₂ : List Γ)
  定义体: BlankExtends l₁ l₂ ∨ BlankExtends l₂ l₁

@[refl]

Depends on / 依赖: BlankExtends
-/
def BlankRel {Γ} [Inhabited Γ] (l₁ l₂ : List Γ) : Prop :=
  BlankExtends l₁ l₂ ∨ BlankExtends l₂ l₁

@[refl]
/--
theorem `BlankRel.refl` / 定理 `BlankRel.refl`

English:
theorem BlankRel.refl
  given: {Γ} [Inhabited Γ] (l : List Γ)
  statement: BlankRel l l
  proof: Or.inl (BlankExtends.refl _)

@[symm]

中文:
定理 BlankRel.refl
  条件: {Γ} [Inhabited Γ] (l : List Γ)
  结论: BlankRel l l
  证明: Or.inl (BlankExtends.refl _)

@[symm]

Depends on / 依赖: BlankExtends, BlankExtends.refl, Or.inl
-/
theorem BlankRel.refl {Γ} [Inhabited Γ] (l : List Γ) : BlankRel l l :=
  Or.inl (BlankExtends.refl _)

@[symm]
/--
theorem `BlankRel.symm` / 定理 `BlankRel.symm`

English:
theorem BlankRel.symm
  given: {Γ} [Inhabited Γ] {l₁ l₂ : List Γ}
  statement: BlankRel l₁ l₂ -> BlankRel l₂ l₁
  proof: Or.symm

@[trans]

中文:
定理 BlankRel.symm
  条件: {Γ} [Inhabited Γ] {l₁ l₂ : List Γ}
  结论: BlankRel l₁ l₂ -> BlankRel l₂ l₁
  证明: Or.symm

@[trans]

Depends on / 依赖: Or.symm
-/
theorem BlankRel.symm {Γ} [Inhabited Γ] {l₁ l₂ : List Γ} : BlankRel l₁ l₂ -> BlankRel l₂ l₁ :=
  Or.symm

@[trans]
/--
theorem `BlankRel.trans` / 定理 `BlankRel.trans`

English:
theorem BlankRel.trans
  given: {Γ} [Inhabited Γ] {l₁ l₂ l₃ : List Γ}
  proof: by
  grind [eq_def, BlankExtends.below_of_le, BlankExtends.above_of_le, BlankExtends.trans]

中文:
定理 BlankRel.trans
  条件: {Γ} [Inhabited Γ] {l₁ l₂ l₃ : List Γ}
  证明: by
  grind [eq_def, BlankExtends.below_of_le, BlankExtends.above_of_le, BlankExtends.trans]

Depends on / 依赖: BlankExtends, BlankExtends.above_of_le, BlankExtends.below_of_le, BlankExtends.trans, above_of_le, below_of_le, eq_def
-/
theorem BlankRel.trans {Γ} [Inhabited Γ] {l₁ l₂ l₃ : List Γ} :
    BlankRel l₁ l₂ -> BlankRel l₂ l₃ -> BlankRel l₁ l₃ := by
  grind [eq_def, BlankExtends.below_of_le, BlankExtends.above_of_le, BlankExtends.trans]

/--
Definition of `BlankRel.above` / `BlankRel.above` 的定义

English:
definition BlankRel.above
  signature: {Γ} [Inhabited Γ] {l₁ l₂ : List Γ} (h : BlankRel l₁ l₂)
  body: by
  refine
    if hl : l₁.length <= l₂.length then ⟨l₂, Or.elim h id fun h' => ?_, BlankExtends.refl _⟩
    else ⟨l₁, BlankExtends.refl _, Or.elim h (fun h' => ?_) id⟩
  · exact (BlankExtends.refl _).above_of_le h' hl
  · exact (BlankExtends.refl _).above_of_le h' (le_of_not_ge hl)

中文:
定义 BlankRel.above
  签名: {Γ} [Inhabited Γ] {l₁ l₂ : List Γ} (h : BlankRel l₁ l₂)
  定义体: by
  refine
    if hl : l₁.length <= l₂.length then ⟨l₂, Or.elim h id fun h' => ?_, BlankExtends.refl _⟩
    else ⟨l₁, BlankExtends.refl _, Or.elim h (fun h' => ?_) id⟩
  · exact (BlankExtends.refl _).above_of_le h' hl
  · exact (BlankExtends.refl _).above_of_le h' (le_of_not_ge hl)

Depends on / 依赖: BlankExtends, BlankExtends.refl, Or.elim, above_of_le, le_of_not_ge, length
-/
def BlankRel.above {Γ} [Inhabited Γ] {l₁ l₂ : List Γ} (h : BlankRel l₁ l₂) :
    { l // BlankExtends l₁ l ∧ BlankExtends l₂ l } := by
  refine
    if hl : l₁.length <= l₂.length then ⟨l₂, Or.elim h id fun h' => ?_, BlankExtends.refl _⟩
    else ⟨l₁, BlankExtends.refl _, Or.elim h (fun h' => ?_) id⟩
  · exact (BlankExtends.refl _).above_of_le h' hl
  · exact (BlankExtends.refl _).above_of_le h' (le_of_not_ge hl)

/--
Definition of `BlankRel.below` / `BlankRel.below` 的定义

English:
definition BlankRel.below
  signature: {Γ} [Inhabited Γ] {l₁ l₂ : List Γ} (h : BlankRel l₁ l₂)
  body: by
  refine
    if hl : l₁.length <= l₂.length then ⟨l₁, BlankExtends.refl _, Or.elim h id fun h' => ?_⟩
    else ⟨l₂, Or.elim h (fun h' => ?_) id, BlankExtends.refl _⟩
  · exact (BlankExtends.refl _).above_of_le h' hl
  · exact (BlankExtends.refl _).above_of_le h' (le_of_not_ge hl)

中文:
定义 BlankRel.below
  签名: {Γ} [Inhabited Γ] {l₁ l₂ : List Γ} (h : BlankRel l₁ l₂)
  定义体: by
  refine
    if hl : l₁.length <= l₂.length then ⟨l₁, BlankExtends.refl _, Or.elim h id fun h' => ?_⟩
    else ⟨l₂, Or.elim h (fun h' => ?_) id, BlankExtends.refl _⟩
  · exact (BlankExtends.refl _).above_of_le h' hl
  · exact (BlankExtends.refl _).above_of_le h' (le_of_not_ge hl)

Depends on / 依赖: BlankExtends, BlankExtends.refl, Or.elim, above_of_le, le_of_not_ge, length
-/
def BlankRel.below {Γ} [Inhabited Γ] {l₁ l₂ : List Γ} (h : BlankRel l₁ l₂) :
    { l // BlankExtends l l₁ ∧ BlankExtends l l₂ } := by
  refine
    if hl : l₁.length <= l₂.length then ⟨l₁, BlankExtends.refl _, Or.elim h id fun h' => ?_⟩
    else ⟨l₂, Or.elim h (fun h' => ?_) id, BlankExtends.refl _⟩
  · exact (BlankExtends.refl _).above_of_le h' hl
  · exact (BlankExtends.refl _).above_of_le h' (le_of_not_ge hl)

/--
theorem `BlankRel.equivalence` / 定理 `BlankRel.equivalence`

English:
theorem BlankRel.equivalence
  given: (Γ) [Inhabited Γ]
  statement: Equivalence (@BlankRel Γ _)
  proof: ⟨BlankRel.refl, @BlankRel.symm _ _, @BlankRel.trans _ _⟩

中文:
定理 BlankRel.equivalence
  条件: (Γ) [Inhabited Γ]
  结论: Equivalence (@BlankRel Γ _)
  证明: ⟨BlankRel.refl, @BlankRel.symm _ _, @BlankRel.trans _ _⟩

Depends on / 依赖: BlankRel, BlankRel.refl, BlankRel.symm, BlankRel.trans
-/
theorem BlankRel.equivalence (Γ) [Inhabited Γ] : Equivalence (@BlankRel Γ _) :=
  ⟨BlankRel.refl, @BlankRel.symm _ _, @BlankRel.trans _ _⟩

/-- Construct a setoid instance for `BlankRel`. -/
@[instance_reducible]
/--
Definition of `BlankRel.setoid` / `BlankRel.setoid` 的定义

English:
definition BlankRel.setoid
  signature: (Γ) [Inhabited Γ]
  body: ⟨_, BlankRel.equivalence _⟩

中文:
定义 BlankRel.setoid
  签名: (Γ) [Inhabited Γ]
  定义体: ⟨_, BlankRel.equivalence _⟩

Depends on / 依赖: BlankRel, BlankRel.equivalence, equivalence
-/
def BlankRel.setoid (Γ) [Inhabited Γ] : Setoid (List Γ) :=
  ⟨_, BlankRel.equivalence _⟩

/--
Definition of `ListBlank` / `ListBlank` 的定义

English:
definition ListBlank
  signature: (Γ) [Inhabited Γ]
  body: Quotient (BlankRel.setoid Γ)

中文:
定义 ListBlank
  签名: (Γ) [Inhabited Γ]
  定义体: Quotient (BlankRel.setoid Γ)

Depends on / 依赖: BlankRel, BlankRel.setoid, Quotient, setoid
-/
def ListBlank (Γ) [Inhabited Γ] :=
  Quotient (BlankRel.setoid Γ)

/--
Instance `ListBlank.inhabited` / 实例 `ListBlank.inhabited`

English:
instance ListBlank.inhabited
  signature: {Γ} [Inhabited Γ]
  body: ⟨Quotient.mk'' []⟩

中文:
实例 ListBlank.inhabited
  签名: {Γ} [Inhabited Γ]
  定义体: ⟨Quotient.mk'' []⟩

Depends on / 依赖: Quotient, Quotient.mk
-/
instance ListBlank.inhabited {Γ} [Inhabited Γ] : Inhabited (ListBlank Γ) :=
  ⟨Quotient.mk'' []⟩

/--
Instance `ListBlank.hasEmptyc` / 实例 `ListBlank.hasEmptyc`

English:
instance ListBlank.hasEmptyc
  signature: {Γ} [Inhabited Γ]
  body: ⟨Quotient.mk'' []⟩

中文:
实例 ListBlank.hasEmptyc
  签名: {Γ} [Inhabited Γ]
  定义体: ⟨Quotient.mk'' []⟩

Depends on / 依赖: Quotient, Quotient.mk
-/
instance ListBlank.hasEmptyc {Γ} [Inhabited Γ] : EmptyCollection (ListBlank Γ) :=
  ⟨Quotient.mk'' []⟩

/--
Definition of `ListBlank.liftOn` / `ListBlank.liftOn` 的定义

English:
abbreviation ListBlank.liftOn
  signature: {Γ} [Inhabited Γ] {α} (l : ListBlank Γ) (f : List Γ -> α)
  body: l.liftOn' f by rintro a b (h | h) <;> [exact H _ _ h; exact (H _ _ h).symm]

中文:
缩写 ListBlank.liftOn
  签名: {Γ} [Inhabited Γ] {α} (l : ListBlank Γ) (f : List Γ -> α)
  定义体: l.liftOn' f by rintro a b (h | h) <;> [exact H _ _ h; exact (H _ _ h).symm]
-/
protected abbrev ListBlank.liftOn {Γ} [Inhabited Γ] {α} (l : ListBlank Γ) (f : List Γ -> α)
    (H : forall a b, BlankExtends a b -> f a = f b) : α :=
l.liftOn' f by rintro a b (h | h) <;> [exact H _ _ h; exact (H _ _ h).symm]

/--
Definition of `ListBlank.mk` / `ListBlank.mk` 的定义

English:
definition ListBlank.mk
  signature: {Γ} [Inhabited Γ]
  body: Quotient.mk''

@[elab_as_elim]

中文:
定义 ListBlank.mk
  签名: {Γ} [Inhabited Γ]
  定义体: Quotient.mk''

@[elab_as_elim]

Depends on / 依赖: Quotient, Quotient.mk
-/
def ListBlank.mk {Γ} [Inhabited Γ] : List Γ -> ListBlank Γ :=
  Quotient.mk''

@[elab_as_elim]
/--
theorem `ListBlank.induction_on` / 定理 `ListBlank.induction_on`

English:
theorem ListBlank.induction_on
  statement: {Γ} [Inhabited Γ] {p : ListBlank Γ -> Prop}
  proof: Quotient.inductionOn' q h

中文:
定理 ListBlank.induction_on
  结论: {Γ} [Inhabited Γ] {p : ListBlank Γ -> 命题}
  证明: Quotient.inductionOn' q h
-/
protected theorem ListBlank.induction_on {Γ} [Inhabited Γ] {p : ListBlank Γ -> Prop}
    (q : ListBlank Γ) (h : forall a, p (ListBlank.mk a)) : p q :=
  Quotient.inductionOn' q h

/--
Definition of `ListBlank.head` / `ListBlank.head` 的定义

English:
definition ListBlank.head
  signature: {Γ} [Inhabited Γ] (l : ListBlank Γ)
  body: by
  apply l.liftOn List.headI
  rintro a _ ⟨i, rfl⟩
  cases a
  · cases i <;> rfl
  rfl

@[simp]

中文:
定义 ListBlank.head
  签名: {Γ} [Inhabited Γ] (l : ListBlank Γ)
  定义体: by
  apply l.liftOn List.headI
  rintro a _ ⟨i, rfl⟩
  cases a
  · cases i <;> rfl
  rfl

@[simp]

Depends on / 依赖: List.headI, l.liftOn, liftOn
-/
def ListBlank.head {Γ} [Inhabited Γ] (l : ListBlank Γ) : Γ := by
  apply l.liftOn List.headI
  rintro a _ ⟨i, rfl⟩
  cases a
  · cases i <;> rfl
  rfl

@[simp]
/--
theorem `ListBlank.head_mk` / 定理 `ListBlank.head_mk`

English:
theorem ListBlank.head_mk
  given: {Γ} [Inhabited Γ] (l : List Γ)
  proof: rfl

中文:
定理 ListBlank.head_mk
  条件: {Γ} [Inhabited Γ] (l : List Γ)
  证明: rfl
-/
theorem ListBlank.head_mk {Γ} [Inhabited Γ] (l : List Γ) :
    ListBlank.head (ListBlank.mk l) = l.headI :=
  rfl

/--
Definition of `ListBlank.tail` / `ListBlank.tail` 的定义

English:
definition ListBlank.tail
  signature: {Γ} [Inhabited Γ] (l : ListBlank Γ)
  body: by
  apply l.liftOn (fun l => ListBlank.mk l.tail)
  rintro a _ ⟨i, rfl⟩
  refine Quotient.sound' (Or.inl ?_)
  cases a
  · rcases i with - | i <;> [exact ⟨0, rfl⟩; exact ⟨i, rfl⟩]
  exact ⟨i, rfl⟩

@[simp]

中文:
定义 ListBlank.tail
  签名: {Γ} [Inhabited Γ] (l : ListBlank Γ)
  定义体: by
  apply l.liftOn (fun l => ListBlank.mk l.tail)
  rintro a _ ⟨i, rfl⟩
  refine Quotient.sound' (Or.inl ?_)
  cases a
  · rcases i with - | i <;> [exact ⟨0, rfl⟩; exact ⟨i, rfl⟩]
  exact ⟨i, rfl⟩

@[simp]

Depends on / 依赖: ListBlank, ListBlank.mk, Or.inl, Quotient, Quotient.sound, l.liftOn, l.tail, liftOn
-/
def ListBlank.tail {Γ} [Inhabited Γ] (l : ListBlank Γ) : ListBlank Γ := by
  apply l.liftOn (fun l => ListBlank.mk l.tail)
  rintro a _ ⟨i, rfl⟩
  refine Quotient.sound' (Or.inl ?_)
  cases a
  · rcases i with - | i <;> [exact ⟨0, rfl⟩; exact ⟨i, rfl⟩]
  exact ⟨i, rfl⟩

@[simp]
/--
theorem `ListBlank.tail_mk` / 定理 `ListBlank.tail_mk`

English:
theorem ListBlank.tail_mk
  given: {Γ} [Inhabited Γ] (l : List Γ)
  proof: rfl

中文:
定理 ListBlank.tail_mk
  条件: {Γ} [Inhabited Γ] (l : List Γ)
  证明: rfl
-/
theorem ListBlank.tail_mk {Γ} [Inhabited Γ] (l : List Γ) :
    ListBlank.tail (ListBlank.mk l) = ListBlank.mk l.tail :=
  rfl

/--
Definition of `ListBlank.cons` / `ListBlank.cons` 的定义

English:
definition ListBlank.cons
  signature: {Γ} [Inhabited Γ] (a : Γ) (l : ListBlank Γ)
  body: by
  apply l.liftOn (fun l => ListBlank.mk (List.cons a l))
  rintro _ _ ⟨i, rfl⟩
  exact Quotient.sound' (Or.inl ⟨i, rfl⟩)

@[simp]

中文:
定义 ListBlank.cons
  签名: {Γ} [Inhabited Γ] (a : Γ) (l : ListBlank Γ)
  定义体: by
  apply l.liftOn (fun l => ListBlank.mk (List.cons a l))
  rintro _ _ ⟨i, rfl⟩
  exact Quotient.sound' (Or.inl ⟨i, rfl⟩)

@[simp]

Depends on / 依赖: List.cons, ListBlank, ListBlank.mk, Or.inl, Quotient, Quotient.sound, l.liftOn, liftOn
-/
def ListBlank.cons {Γ} [Inhabited Γ] (a : Γ) (l : ListBlank Γ) : ListBlank Γ := by
  apply l.liftOn (fun l => ListBlank.mk (List.cons a l))
  rintro _ _ ⟨i, rfl⟩
  exact Quotient.sound' (Or.inl ⟨i, rfl⟩)

@[simp]
/--
theorem `ListBlank.cons_mk` / 定理 `ListBlank.cons_mk`

English:
theorem ListBlank.cons_mk
  given: {Γ} [Inhabited Γ] (a : Γ) (l : List Γ)
  proof: rfl

@[simp]

中文:
定理 ListBlank.cons_mk
  条件: {Γ} [Inhabited Γ] (a : Γ) (l : List Γ)
  证明: rfl

@[simp]
-/
theorem ListBlank.cons_mk {Γ} [Inhabited Γ] (a : Γ) (l : List Γ) :
    ListBlank.cons a (ListBlank.mk l) = ListBlank.mk (a :: l) :=
  rfl

@[simp]
/--
theorem `ListBlank.head_cons` / 定理 `ListBlank.head_cons`

English:
theorem ListBlank.head_cons
  given: {Γ} [Inhabited Γ] (a : Γ)
  statement: forall l : ListBlank Γ, (l.cons a).head = a
  proof: Quotient.ind' fun _ => rfl

@[simp]

中文:
定理 ListBlank.head_cons
  条件: {Γ} [Inhabited Γ] (a : Γ)
  结论: 对任意 l : ListBlank Γ, (l.cons a).head = a
  证明: Quotient.ind' fun _ => rfl

@[simp]

Depends on / 依赖: Quotient, Quotient.ind
-/
theorem ListBlank.head_cons {Γ} [Inhabited Γ] (a : Γ) : forall l : ListBlank Γ, (l.cons a).head = a :=
  Quotient.ind' fun _ => rfl

@[simp]
/--
theorem `ListBlank.tail_cons` / 定理 `ListBlank.tail_cons`

English:
theorem ListBlank.tail_cons
  given: {Γ} [Inhabited Γ] (a : Γ)
  statement: forall l : ListBlank Γ, (l.cons a).tail = l
  proof: Quotient.ind' fun _ => rfl

中文:
定理 ListBlank.tail_cons
  条件: {Γ} [Inhabited Γ] (a : Γ)
  结论: 对任意 l : ListBlank Γ, (l.cons a).tail = l
  证明: Quotient.ind' fun _ => rfl

Depends on / 依赖: Quotient, Quotient.ind
-/
theorem ListBlank.tail_cons {Γ} [Inhabited Γ] (a : Γ) : forall l : ListBlank Γ, (l.cons a).tail = l :=
  Quotient.ind' fun _ => rfl

/-- The `cons` and `head`/`tail` functions are mutually inverse, unlike in the case of `List` where
this only holds for nonempty lists. -/
@[simp]
/--
theorem `ListBlank.cons_head_tail` / 定理 `ListBlank.cons_head_tail`

English:
theorem ListBlank.cons_head_tail
  given: {Γ} [Inhabited Γ]
  statement: forall l : ListBlank Γ, l.tail.cons l.head = l
  proof: by
  apply Quotient.ind'
  refine fun l => Quotient.sound' (Or.inr ?_)
  cases l
  · exact ⟨1, rfl⟩
  · rfl

中文:
定理 ListBlank.cons_head_tail
  条件: {Γ} [Inhabited Γ]
  结论: 对任意 l : ListBlank Γ, l.tail.cons l.head = l
  证明: by
  apply Quotient.ind'
  refine fun l => Quotient.sound' (Or.inr ?_)
  cases l
  · exact ⟨1, rfl⟩
  · rfl

Depends on / 依赖: Or.inr, Quotient, Quotient.ind, Quotient.sound
-/
theorem ListBlank.cons_head_tail {Γ} [Inhabited Γ] : forall l : ListBlank Γ, l.tail.cons l.head = l := by
  apply Quotient.ind'
  refine fun l => Quotient.sound' (Or.inr ?_)
  cases l
  · exact ⟨1, rfl⟩
  · rfl

/--
theorem `ListBlank.exists_cons` / 定理 `ListBlank.exists_cons`

English:
theorem ListBlank.exists_cons
  given: {Γ} [Inhabited Γ] (l : ListBlank Γ)
  proof: ⟨_, _, (ListBlank.cons_head_tail _).symm⟩

中文:
定理 ListBlank.exists_cons
  条件: {Γ} [Inhabited Γ] (l : ListBlank Γ)
  证明: ⟨_, _, (ListBlank.cons_head_tail _).symm⟩

Depends on / 依赖: ListBlank, ListBlank.cons_head_tail, cons_head_tail
-/
theorem ListBlank.exists_cons {Γ} [Inhabited Γ] (l : ListBlank Γ) :
    exists a l', l = ListBlank.cons a l' :=
  ⟨_, _, (ListBlank.cons_head_tail _).symm⟩

/--
Definition of `ListBlank.nth` / `ListBlank.nth` 的定义

English:
definition ListBlank.nth
  signature: {Γ} [Inhabited Γ] (l : ListBlank Γ) (n : Nat)
  body: by
  apply l.liftOn (fun l => List.getI l n)
  rintro l _ ⟨i, rfl⟩
  rcases lt_or_ge n _ with h | h
  · rw [List.getI_append _ _ _ h]
  rw [List.getI_eq_default _ h]
  rcases le_or_gt _ n with h₂ | h₂
  · rw [List.getI_eq_default _ h₂]
  rw [List.getI_eq_getElem _ h₂]; rw [List.getElem_append_right 

中文:
定义 ListBlank.nth
  签名: {Γ} [Inhabited Γ] (l : ListBlank Γ) (n : 自然数)
  定义体: by
  apply l.liftOn (fun l => List.getI l n)
  rintro l _ ⟨i, rfl⟩
  rcases lt_or_ge n _ with h | h
  · rw [List.getI_append _ _ _ h]
  rw [List.getI_eq_default _ h]
  rcases le_or_gt _ n with h₂ | h₂
  · rw [List.getI_eq_default _ h₂]
  rw [List.getI_eq_getElem _ h₂]; rw [List.getElem_append_right 

Depends on / 依赖: List.getElem_append_right, List.getElem_replicate, List.getI, List.getI_append, List.getI_eq_default, List.getI_eq_getElem, getElem_append_right, getElem_replicate, getI_append, getI_eq_default, getI_eq_getElem, l.liftOn, le_or_gt, liftOn, lt_or_ge
-/
def ListBlank.nth {Γ} [Inhabited Γ] (l : ListBlank Γ) (n : Nat) : Γ := by
  apply l.liftOn (fun l => List.getI l n)
  rintro l _ ⟨i, rfl⟩
  rcases lt_or_ge n _ with h | h
  · rw [List.getI_append _ _ _ h]
  rw [List.getI_eq_default _ h]
  rcases le_or_gt _ n with h₂ | h₂
  · rw [List.getI_eq_default _ h₂]
  rw [List.getI_eq_getElem _ h₂]; rw [List.getElem_append_right h]; rw [List.getElem_replicate]

@[simp]
/--
theorem `ListBlank.nth_mk` / 定理 `ListBlank.nth_mk`

English:
theorem ListBlank.nth_mk
  given: {Γ} [Inhabited Γ] (l : List Γ) (n : Nat)
  proof: rfl

@[simp]

中文:
定理 ListBlank.nth_mk
  条件: {Γ} [Inhabited Γ] (l : List Γ) (n : 自然数)
  证明: rfl

@[simp]
-/
theorem ListBlank.nth_mk {Γ} [Inhabited Γ] (l : List Γ) (n : Nat) :
    (ListBlank.mk l).nth n = l.getI n :=
  rfl

@[simp]
/--
theorem `ListBlank.nth_zero` / 定理 `ListBlank.nth_zero`

English:
theorem ListBlank.nth_zero
  given: {Γ} [Inhabited Γ] (l : ListBlank Γ)
  statement: l.nth 0 = l.head
  proof: by
  rw [← ListBlank.cons_head_tail l]
  induction l.tail using Quotient.inductionOn'
  rfl

@[simp]

中文:
定理 ListBlank.nth_zero
  条件: {Γ} [Inhabited Γ] (l : ListBlank Γ)
  结论: l.nth 0 = l.head
  证明: by
  rw [← ListBlank.cons_head_tail l]
  induction l.tail using Quotient.inductionOn'
  rfl

@[simp]

Depends on / 依赖: ListBlank, ListBlank.cons_head_tail, Quotient, Quotient.inductionOn, cons_head_tail, inductionOn, l.tail
-/
theorem ListBlank.nth_zero {Γ} [Inhabited Γ] (l : ListBlank Γ) : l.nth 0 = l.head := by
  rw [← ListBlank.cons_head_tail l]
  induction l.tail using Quotient.inductionOn'
  rfl

@[simp]
/--
theorem `ListBlank.nth_succ` / 定理 `ListBlank.nth_succ`

English:
theorem ListBlank.nth_succ
  given: {Γ} [Inhabited Γ] (l : ListBlank Γ) (n : Nat)
  proof: by
  rw [← ListBlank.cons_head_tail l]
  induction l.tail using Quotient.inductionOn'
  rfl

@[ext]

中文:
定理 ListBlank.nth_succ
  条件: {Γ} [Inhabited Γ] (l : ListBlank Γ) (n : 自然数)
  证明: by
  rw [← ListBlank.cons_head_tail l]
  induction l.tail using Quotient.inductionOn'
  rfl

@[ext]

Depends on / 依赖: ListBlank, ListBlank.cons_head_tail, Quotient, Quotient.inductionOn, cons_head_tail, inductionOn, l.tail
-/
theorem ListBlank.nth_succ {Γ} [Inhabited Γ] (l : ListBlank Γ) (n : Nat) :
    l.nth (n + 1) = l.tail.nth n := by
  rw [← ListBlank.cons_head_tail l]
  induction l.tail using Quotient.inductionOn'
  rfl

@[ext]
/--
theorem `ListBlank.ext` / 定理 `ListBlank.ext`

English:
theorem ListBlank.ext
  given: {Γ} [i : Inhabited Γ] {L₁ L₂ : ListBlank Γ}
  proof: by
  refine ListBlank.induction_on L₁ fun l₁ => ListBlank.induction_on L₂ fun l₂ H => ?_
  wlog h : l₁.length <= l₂.length
  · cases le_total l₁.length l₂.length <;> [skip; symm] <;> apply this <;> try assumption
    intro
    rw [H]
  refine Quotient.sound' (Or.inl ⟨l₂.length - l₁.length, ?_⟩)
  re

中文:
定理 ListBlank.ext
  条件: {Γ} [i : Inhabited Γ] {L₁ L₂ : ListBlank Γ}
  证明: by
  refine ListBlank.induction_on L₁ fun l₁ => ListBlank.induction_on L₂ fun l₂ H => ?_
  wlog h : l₁.length <= l₂.length
  · cases le_total l₁.length l₂.length <;> [skip; symm] <;> apply this <;> try assumption
    intro
    rw [H]
  refine Quotient.sound' (Or.inl ⟨l₂.length - l₁.length, ?_⟩)
  re

Depends on / 依赖: Eq.symm, List.ext_getElem, List.length_append, List.length_replicate, ListBlank, ListBlank.induction_on, ListBlank.nth_mk, Nat.add_sub_cancel, Or.inl, Quotient, Quotient.sound, add_sub_cancel, ext_getElem, induction_on, le_total, length, length_append, length_replicate, lt_or_ge, nth_mk
-/
theorem ListBlank.ext {Γ} [i : Inhabited Γ] {L₁ L₂ : ListBlank Γ} :
    (forall i, L₁.nth i = L₂.nth i) -> L₁ = L₂ := by
  refine ListBlank.induction_on L₁ fun l₁ => ListBlank.induction_on L₂ fun l₂ H => ?_
  wlog h : l₁.length <= l₂.length
  · cases le_total l₁.length l₂.length <;> [skip; symm] <;> apply this <;> try assumption
    intro
    rw [H]
  refine Quotient.sound' (Or.inl ⟨l₂.length - l₁.length, ?_⟩)
  refine List.ext_getElem ?_ fun i h h₂ => Eq.symm ?_
  · simp only [Nat.add_sub_cancel' h, List.length_append, List.length_replicate]
  simp only [ListBlank.nth_mk] at H
  rcases lt_or_ge i l₁.length with h' | h'
  · simp [h', List.getElem_append h₂, ← List.getI_eq_getElem _ h, ← List.getI_eq_getElem _ h', H]
  · rw [List.getElem_append_right h', List.getElem_replicate,
      ← List.getI_eq_default _ h', H, List.getI_eq_getElem _ h]

/-- Apply a function to a value stored at the nth position of the list. -/
@[simp]
/--
Definition of `ListBlank.modifyNth` / `ListBlank.modifyNth` 的定义

English:
definition ListBlank.modifyNth
  signature: {Γ} [Inhabited Γ] (f : Γ -> Γ)

中文:
定义 ListBlank.modifyNth
  签名: {Γ} [Inhabited Γ] (f : Γ -> Γ)
-/
def ListBlank.modifyNth {Γ} [Inhabited Γ] (f : Γ -> Γ) : Nat -> ListBlank Γ -> ListBlank Γ
  | 0, L => L.tail.cons (f L.head)
  | n + 1, L => (L.tail.modifyNth f n).cons L.head

/--
theorem `ListBlank.nth_modifyNth` / 定理 `ListBlank.nth_modifyNth`

English:
theorem ListBlank.nth_modifyNth
  given: {Γ} [Inhabited Γ] (f : Γ -> Γ) (n i) (L : ListBlank Γ)
  proof: by
  induction n generalizing i L with
  | zero =>
    cases i <;> simp only [ListBlank.nth_zero, if_true, ListBlank.head_cons, ListBlank.modifyNth,
      ListBlank.nth_succ, if_false, ListBlank.tail_cons, reduceCtorEq]
  | succ n IH =>
    cases i
    · rw [if_neg (Nat.succ_ne_zero _).symm]
      s

中文:
定理 ListBlank.nth_modifyNth
  条件: {Γ} [Inhabited Γ] (f : Γ -> Γ) (n i) (L : ListBlank Γ)
  证明: by
  induction n generalizing i L with
  | zero =>
    cases i <;> simp only [ListBlank.nth_zero, if_true, ListBlank.head_cons, ListBlank.modifyNth,
      ListBlank.nth_succ, if_false, ListBlank.tail_cons, reduceCtorEq]
  | succ n IH =>
    cases i
    · rw [if_neg (Nat.succ_ne_zero _).symm]
      s

Depends on / 依赖: ListBlank, ListBlank.head_cons, ListBlank.modifyNth, ListBlank.nth_succ, ListBlank.nth_zero, ListBlank.tail_cons, Nat.succ.injEq, Nat.succ_ne_zero, generalizing, head_cons, if_false, if_neg, if_true, modifyNth, nth_succ, nth_zero, reduceCtorEq, succ_ne_zero, tail_cons
-/
theorem ListBlank.nth_modifyNth {Γ} [Inhabited Γ] (f : Γ -> Γ) (n i) (L : ListBlank Γ) :
    (L.modifyNth f n).nth i = if i = n then f (L.nth i) else L.nth i := by
  induction n generalizing i L with
  | zero =>
    cases i <;> simp only [ListBlank.nth_zero, if_true, ListBlank.head_cons, ListBlank.modifyNth,
      ListBlank.nth_succ, if_false, ListBlank.tail_cons, reduceCtorEq]
  | succ n IH =>
    cases i
    · rw [if_neg (Nat.succ_ne_zero _).symm]
      simp only [ListBlank.nth_zero, ListBlank.head_cons, ListBlank.modifyNth]
    · simp only [IH, ListBlank.modifyNth, ListBlank.nth_succ, ListBlank.tail_cons, Nat.succ.injEq]

/--
Definition of `PointedMap.` / `PointedMap.` 的定义

English:
structure PointedMap.{u,
  parameters: v} (Γ
  axioms and operations (2):
    - f : Γ -> Γ'
    - map_pt' : f default = default

中文:
结构 PointedMap.{u,
  参数: v} (Γ
  公理与运算 (2 个):
    - f : Γ -> Γ'
    - map_pt' : f default = default
-/
structure PointedMap.{u, v} (Γ : Type u) (Γ' : Type v) [Inhabited Γ] [Inhabited Γ'] :
    Type max u v where
  /-- The map underlying this instance. -/
  f : Γ -> Γ'
  map_pt' : f default = default

instance {Γ Γ'} [Inhabited Γ] [Inhabited Γ'] : Inhabited (PointedMap Γ Γ') :=
  ⟨⟨default, rfl⟩⟩

instance {Γ Γ'} [Inhabited Γ] [Inhabited Γ'] : CoeFun (PointedMap Γ Γ') fun _ => Γ -> Γ' :=
  ⟨PointedMap.f⟩

/--
theorem `PointedMap.mk_val` / 定理 `PointedMap.mk_val`

English:
theorem PointedMap.mk_val
  given: {Γ Γ'} [Inhabited Γ] [Inhabited Γ'] (f : Γ -> Γ') (pt)
  proof: rfl

@[simp]

中文:
定理 PointedMap.mk_val
  条件: {Γ Γ'} [Inhabited Γ] [Inhabited Γ'] (f : Γ -> Γ') (pt)
  证明: rfl

@[simp]
-/
theorem PointedMap.mk_val {Γ Γ'} [Inhabited Γ] [Inhabited Γ'] (f : Γ -> Γ') (pt) :
    (PointedMap.mk f pt : Γ -> Γ') = f :=
  rfl

@[simp]
/--
theorem `PointedMap.map_pt` / 定理 `PointedMap.map_pt`

English:
theorem PointedMap.map_pt
  given: {Γ Γ'} [Inhabited Γ] [Inhabited Γ'] (f : PointedMap Γ Γ')
  proof: PointedMap.map_pt' _

@[simp]

中文:
定理 PointedMap.map_pt
  条件: {Γ Γ'} [Inhabited Γ] [Inhabited Γ'] (f : PointedMap Γ Γ')
  证明: PointedMap.map_pt' _

@[simp]

Depends on / 依赖: PointedMap, PointedMap.map_pt, map_pt
-/
theorem PointedMap.map_pt {Γ Γ'} [Inhabited Γ] [Inhabited Γ'] (f : PointedMap Γ Γ') :
    f default = default :=
  PointedMap.map_pt' _

@[simp]
/--
theorem `PointedMap.headI_map` / 定理 `PointedMap.headI_map`

English:
theorem PointedMap.headI_map
  statement: {Γ Γ'} [Inhabited Γ] [Inhabited Γ'] (f : PointedMap Γ Γ')
  proof: by
  cases l <;> [exact (PointedMap.map_pt f).symm; rfl]

中文:
定理 PointedMap.headI_map
  结论: {Γ Γ'} [Inhabited Γ] [Inhabited Γ'] (f : PointedMap Γ Γ')
  证明: by
  cases l <;> [exact (PointedMap.map_pt f).symm; rfl]

Depends on / 依赖: PointedMap, PointedMap.map_pt, map_pt
-/
theorem PointedMap.headI_map {Γ Γ'} [Inhabited Γ] [Inhabited Γ'] (f : PointedMap Γ Γ')
    (l : List Γ) : (l.map f).headI = f l.headI := by
  cases l <;> [exact (PointedMap.map_pt f).symm; rfl]

/--
Definition of `ListBlank.map` / `ListBlank.map` 的定义

English:
definition ListBlank.map
  signature: {Γ Γ'} [Inhabited Γ] [Inhabited Γ'] (f : PointedMap Γ Γ') (l : ListBlank Γ)
  body: by
  apply l.liftOn (fun l => ListBlank.mk (List.map f l))
  rintro l _ ⟨i, rfl⟩; refine Quotient.sound' (Or.inl ⟨i, ?_⟩)
  simp only [PointedMap.map_pt, List.map_append, List.map_replicate]

@[simp]

中文:
定义 ListBlank.map
  签名: {Γ Γ'} [Inhabited Γ] [Inhabited Γ'] (f : PointedMap Γ Γ') (l : ListBlank Γ)
  定义体: by
  apply l.liftOn (fun l => ListBlank.mk (List.map f l))
  rintro l _ ⟨i, rfl⟩; refine Quotient.sound' (Or.inl ⟨i, ?_⟩)
  simp only [PointedMap.map_pt, List.map_append, List.map_replicate]

@[simp]

Depends on / 依赖: Finset, Finset.insertNone, List.map, List.map_append, List.map_replicate, ListBlank, ListBlank.mk, Or.inl, PointedMap, PointedMap.map_pt, Quotient, Quotient.sound, insertNone, l.liftOn, liftOn, map_append, map_pt, map_replicate
-/
def ListBlank.map {Γ Γ'} [Inhabited Γ] [Inhabited Γ'] (f : PointedMap Γ Γ') (l : ListBlank Γ) :
    ListBlank Γ' := by
  apply l.liftOn (fun l => ListBlank.mk (List.map f l))
  rintro l _ ⟨i, rfl⟩; refine Quotient.sound' (Or.inl ⟨i, ?_⟩)
  simp only [PointedMap.map_pt, List.map_append, List.map_replicate]

@[simp]
/--
theorem `ListBlank.map_mk` / 定理 `ListBlank.map_mk`

English:
theorem ListBlank.map_mk
  given: {Γ Γ'} [Inhabited Γ] [Inhabited Γ'] (f : PointedMap Γ Γ') (l : List Γ)
  proof: rfl

@[simp]

中文:
定理 ListBlank.map_mk
  条件: {Γ Γ'} [Inhabited Γ] [Inhabited Γ'] (f : PointedMap Γ Γ') (l : List Γ)
  证明: rfl

@[simp]

Depends on / 依赖: Finite, Finite.of_fintype, Fintype, Fintype.ofFinite, ofFinite, of_fintype
-/
theorem ListBlank.map_mk {Γ Γ'} [Inhabited Γ] [Inhabited Γ'] (f : PointedMap Γ Γ') (l : List Γ) :
    (ListBlank.mk l).map f = ListBlank.mk (l.map f) :=
  rfl

@[simp]
/--
theorem `ListBlank.head_map` / 定理 `ListBlank.head_map`

English:
theorem ListBlank.head_map
  statement: {Γ Γ'} [Inhabited Γ] [Inhabited Γ'] (f : PointedMap Γ Γ')
  proof: by
  rw [← ListBlank.cons_head_tail l]
  induction l using Quotient.inductionOn'
  rfl

@[simp]

中文:
定理 ListBlank.head_map
  结论: {Γ Γ'} [Inhabited Γ] [Inhabited Γ'] (f : PointedMap Γ Γ')
  证明: by
  rw [← ListBlank.cons_head_tail l]
  induction l using Quotient.inductionOn'
  rfl

@[simp]

Depends on / 依赖: ListBlank, ListBlank.cons_head_tail, Quotient, Quotient.inductionOn, cons_head_tail, inductionOn
-/
theorem ListBlank.head_map {Γ Γ'} [Inhabited Γ] [Inhabited Γ'] (f : PointedMap Γ Γ')
    (l : ListBlank Γ) : (l.map f).head = f l.head := by
  rw [← ListBlank.cons_head_tail l]
  induction l using Quotient.inductionOn'
  rfl

@[simp]
/--
theorem `ListBlank.tail_map` / 定理 `ListBlank.tail_map`

English:
theorem ListBlank.tail_map
  statement: {Γ Γ'} [Inhabited Γ] [Inhabited Γ'] (f : PointedMap Γ Γ')
  proof: by
  rw [← ListBlank.cons_head_tail l]
  induction l using Quotient.inductionOn'
  rfl

@[simp]

中文:
定理 ListBlank.tail_map
  结论: {Γ Γ'} [Inhabited Γ] [Inhabited Γ'] (f : PointedMap Γ Γ')
  证明: by
  rw [← ListBlank.cons_head_tail l]
  induction l using Quotient.inductionOn'
  rfl

@[simp]

Depends on / 依赖: ListBlank, ListBlank.cons_head_tail, Quotient, Quotient.inductionOn, cons_head_tail, inductionOn
-/
theorem ListBlank.tail_map {Γ Γ'} [Inhabited Γ] [Inhabited Γ'] (f : PointedMap Γ Γ')
    (l : ListBlank Γ) : (l.map f).tail = l.tail.map f := by
  rw [← ListBlank.cons_head_tail l]
  induction l using Quotient.inductionOn'
  rfl

@[simp]
/--
theorem `ListBlank.map_cons` / 定理 `ListBlank.map_cons`

English:
theorem ListBlank.map_cons
  statement: {Γ Γ'} [Inhabited Γ] [Inhabited Γ'] (f : PointedMap Γ Γ')
  proof: by
  refine (ListBlank.cons_head_tail _).symm.trans ?_
  simp only [ListBlank.head_map, ListBlank.head_cons, ListBlank.tail_map, ListBlank.tail_cons]

@[simp]

中文:
定理 ListBlank.map_cons
  结论: {Γ Γ'} [Inhabited Γ] [Inhabited Γ'] (f : PointedMap Γ Γ')
  证明: by
  refine (ListBlank.cons_head_tail _).symm.trans ?_
  simp only [ListBlank.head_map, ListBlank.head_cons, ListBlank.tail_map, ListBlank.tail_cons]

@[simp]

Depends on / 依赖: ListBlank, ListBlank.cons_head_tail, ListBlank.head_cons, ListBlank.head_map, ListBlank.tail_cons, ListBlank.tail_map, cons_head_tail, head_cons, head_map, symm.trans, tail_cons, tail_map
-/
theorem ListBlank.map_cons {Γ Γ'} [Inhabited Γ] [Inhabited Γ'] (f : PointedMap Γ Γ')
    (l : ListBlank Γ) (a : Γ) : (l.cons a).map f = (l.map f).cons (f a) := by
  refine (ListBlank.cons_head_tail _).symm.trans ?_
  simp only [ListBlank.head_map, ListBlank.head_cons, ListBlank.tail_map, ListBlank.tail_cons]

@[simp]
/--
theorem `ListBlank.nth_map` / 定理 `ListBlank.nth_map`

English:
theorem ListBlank.nth_map
  statement: {Γ Γ'} [Inhabited Γ] [Inhabited Γ'] (f : PointedMap Γ Γ')
  proof: by
  refine l.induction_on fun l => ?_
  simp only [ListBlank.map_mk, ListBlank.nth_mk, ← List.getD_default_eq_getI]
  rw [← List.getD_map _ _ f]
  simp

中文:
定理 ListBlank.nth_map
  结论: {Γ Γ'} [Inhabited Γ] [Inhabited Γ'] (f : PointedMap Γ Γ')
  证明: by
  refine l.induction_on fun l => ?_
  simp only [ListBlank.map_mk, ListBlank.nth_mk, ← List.getD_default_eq_getI]
  rw [← List.getD_map _ _ f]
  simp

Depends on / 依赖: List.getD_default_eq_getI, List.getD_map, ListBlank, ListBlank.map_mk, ListBlank.nth_mk, getD_default_eq_getI, getD_map, induction_on, l.induction_on, map_mk, nth_mk
-/
theorem ListBlank.nth_map {Γ Γ'} [Inhabited Γ] [Inhabited Γ'] (f : PointedMap Γ Γ')
    (l : ListBlank Γ) (n : Nat) : (l.map f).nth n = f (l.nth n) := by
  refine l.induction_on fun l => ?_
  simp only [ListBlank.map_mk, ListBlank.nth_mk, ← List.getD_default_eq_getI]
  rw [← List.getD_map _ _ f]
  simp

/--
Definition of `proj` / `proj` 的定义

English:
definition proj
  signature: {ι : Type*} {Γ : ι -> Type*} [forall i, Inhabited (Γ i)] (i : ι)
  body: ⟨fun a => a i, rfl⟩

中文:
定义 proj
  签名: {ι : 类型} {Γ : ι -> 类型} [对任意 i, Inhabited (Γ i)] (i : ι)
  定义体: ⟨fun a => a i, rfl⟩
-/
def proj {ι : Type*} {Γ : ι -> Type*} [forall i, Inhabited (Γ i)] (i : ι) :
    PointedMap (forall i, Γ i) (Γ i) :=
  ⟨fun a => a i, rfl⟩

/--
theorem `proj_map_nth` / 定理 `proj_map_nth`

English:
theorem proj_map_nth
  given: {ι : Type*} {Γ : ι -> Type*} [forall i, Inhabited (Γ i)] (i : ι) (L n)
  proof: by
  rw [ListBlank.nth_map]; rfl

中文:
定理 proj_map_nth
  条件: {ι : 类型} {Γ : ι -> 类型} [对任意 i, Inhabited (Γ i)] (i : ι) (L n)
  证明: by
  rw [ListBlank.nth_map]; rfl

Depends on / 依赖: ListBlank, ListBlank.nth_map, nth_map
-/
theorem proj_map_nth {ι : Type*} {Γ : ι -> Type*} [forall i, Inhabited (Γ i)] (i : ι) (L n) :
    (ListBlank.map (@proj ι Γ _ i) L).nth n = L.nth n i := by
  rw [ListBlank.nth_map]; rfl

/--
theorem `ListBlank.map_modifyNth` / 定理 `ListBlank.map_modifyNth`

English:
theorem ListBlank.map_modifyNth
  statement: {Γ Γ'} [Inhabited Γ] [Inhabited Γ'] (F : PointedMap Γ Γ')
  proof: by
  induction n generalizing L <;>
    simp only [*, ListBlank.head_map, ListBlank.modifyNth, ListBlank.map_cons, ListBlank.tail_map]

中文:
定理 ListBlank.map_modifyNth
  结论: {Γ Γ'} [Inhabited Γ] [Inhabited Γ'] (F : PointedMap Γ Γ')
  证明: by
  induction n generalizing L <;>
    simp only [*, ListBlank.head_map, ListBlank.modifyNth, ListBlank.map_cons, ListBlank.tail_map]

Depends on / 依赖: ListBlank, ListBlank.head_map, ListBlank.map_cons, ListBlank.modifyNth, ListBlank.tail_map, generalizing, head_map, map_cons, modifyNth, tail_map
-/
theorem ListBlank.map_modifyNth {Γ Γ'} [Inhabited Γ] [Inhabited Γ'] (F : PointedMap Γ Γ')
    (f : Γ -> Γ) (f' : Γ' -> Γ') (H : forall x, F (f x) = f' (F x)) (n) (L : ListBlank Γ) :
    (L.modifyNth f n).map F = (L.map F).modifyNth f' n := by
  induction n generalizing L <;>
    simp only [*, ListBlank.head_map, ListBlank.modifyNth, ListBlank.map_cons, ListBlank.tail_map]

/-- Append a list on the left side of a `ListBlank`. -/
@[simp]
/--
Definition of `ListBlank.append` / `ListBlank.append` 的定义

English:
definition ListBlank.append
  signature: {Γ} [Inhabited Γ]

中文:
定义 ListBlank.append
  签名: {Γ} [Inhabited Γ]
-/
def ListBlank.append {Γ} [Inhabited Γ] : List Γ -> ListBlank Γ -> ListBlank Γ
  | [], L => L
  | a :: l, L => ListBlank.cons a (ListBlank.append l L)

@[simp]
/--
theorem `ListBlank.append_mk` / 定理 `ListBlank.append_mk`

English:
theorem ListBlank.append_mk
  given: {Γ} [Inhabited Γ] (l₁ l₂ : List Γ)
  proof: by
  induction l₁ <;>
    simp only [*, ListBlank.append, List.nil_append, List.cons_append, ListBlank.cons_mk]

中文:
定理 ListBlank.append_mk
  条件: {Γ} [Inhabited Γ] (l₁ l₂ : List Γ)
  证明: by
  induction l₁ <;>
    simp only [*, ListBlank.append, List.nil_append, List.cons_append, ListBlank.cons_mk]

Depends on / 依赖: List.cons_append, List.nil_append, ListBlank, ListBlank.append, ListBlank.cons_mk, append, cons_append, cons_mk, nil_append
-/
theorem ListBlank.append_mk {Γ} [Inhabited Γ] (l₁ l₂ : List Γ) :
    ListBlank.append l₁ (ListBlank.mk l₂) = ListBlank.mk (l₁ ++ l₂) := by
  induction l₁ <;>
    simp only [*, ListBlank.append, List.nil_append, List.cons_append, ListBlank.cons_mk]

/--
theorem `ListBlank.append_assoc` / 定理 `ListBlank.append_assoc`

English:
theorem ListBlank.append_assoc
  given: {Γ} [Inhabited Γ] (l₁ l₂ : List Γ) (l₃ : ListBlank Γ)
  proof: by
  refine l₃.induction_on fun l => ?_
  simp only [ListBlank.append_mk, List.append_assoc]

中文:
定理 ListBlank.append_assoc
  条件: {Γ} [Inhabited Γ] (l₁ l₂ : List Γ) (l₃ : ListBlank Γ)
  证明: by
  refine l₃.induction_on fun l => ?_
  simp only [ListBlank.append_mk, List.append_assoc]

Depends on / 依赖: List.append_assoc, ListBlank, ListBlank.append_mk, append_assoc, append_mk, induction_on
-/
theorem ListBlank.append_assoc {Γ} [Inhabited Γ] (l₁ l₂ : List Γ) (l₃ : ListBlank Γ) :
    ListBlank.append (l₁ ++ l₂) l₃ = ListBlank.append l₁ (ListBlank.append l₂ l₃) := by
  refine l₃.induction_on fun l => ?_
  simp only [ListBlank.append_mk, List.append_assoc]

/--
Definition of `ListBlank.flatMap` / `ListBlank.flatMap` 的定义

English:
definition ListBlank.flatMap
  signature: {Γ Γ'} [Inhabited Γ] [Inhabited Γ'] (l : ListBlank Γ) (f : Γ -> List Γ')
  body: by
  apply l.liftOn (fun l => ListBlank.mk (l.flatMap f))
  rintro l _ ⟨i, rfl⟩; obtain ⟨n, e⟩ := hf; refine Quotient.sound' (Or.inl ⟨i * n, ?_⟩)
  rw [List.flatMap_append]; rw [mul_comm]; congr
  induction i with
  | zero => rfl
  | succ i IH =>
    simp only [IH, e, List.replicate_add, Nat.mul_suc

中文:
定义 ListBlank.flatMap
  签名: {Γ Γ'} [Inhabited Γ] [Inhabited Γ'] (l : ListBlank Γ) (f : Γ -> List Γ')
  定义体: by
  apply l.liftOn (fun l => ListBlank.mk (l.flatMap f))
  rintro l _ ⟨i, rfl⟩; obtain ⟨n, e⟩ := hf; refine Quotient.sound' (Or.inl ⟨i * n, ?_⟩)
  rw [List.flatMap_append]; rw [mul_comm]; congr
  induction i with
  | zero => rfl
  | succ i IH =>
    simp only [IH, e, List.replicate_add, Nat.mul_suc

Depends on / 依赖: List.flatMap_append, List.flatMap_cons, List.replicate_add, List.replicate_succ, ListBlank, ListBlank.mk, Nat.mul_succ, Or.inl, Quotient, Quotient.sound, add_comm, flatMap, flatMap_append, flatMap_cons, l.flatMap, l.liftOn, liftOn, mul_comm, mul_succ, replicate_add
-/
def ListBlank.flatMap {Γ Γ'} [Inhabited Γ] [Inhabited Γ'] (l : ListBlank Γ) (f : Γ -> List Γ')
    (hf : exists n, f default = List.replicate n default) : ListBlank Γ' := by
  apply l.liftOn (fun l => ListBlank.mk (l.flatMap f))
  rintro l _ ⟨i, rfl⟩; obtain ⟨n, e⟩ := hf; refine Quotient.sound' (Or.inl ⟨i * n, ?_⟩)
  rw [List.flatMap_append]; rw [mul_comm]; congr
  induction i with
  | zero => rfl
  | succ i IH =>
    simp only [IH, e, List.replicate_add, Nat.mul_succ, add_comm, List.replicate_succ,
      List.flatMap_cons]

@[simp]
/--
theorem `ListBlank.flatMap_mk` / 定理 `ListBlank.flatMap_mk`

English:
theorem ListBlank.flatMap_mk
  proof: rfl

@[simp]

中文:
定理 ListBlank.flatMap_mk
  证明: rfl

@[simp]
-/
theorem ListBlank.flatMap_mk
    {Γ Γ'} [Inhabited Γ] [Inhabited Γ'] (l : List Γ) (f : Γ -> List Γ') (hf) :
    (ListBlank.mk l).flatMap f hf = ListBlank.mk (l.flatMap f) :=
  rfl

@[simp]
/--
theorem `ListBlank.cons_flatMap` / 定理 `ListBlank.cons_flatMap`

English:
theorem ListBlank.cons_flatMap
  statement: {Γ Γ'} [Inhabited Γ] [Inhabited Γ'] (a : Γ) (l : ListBlank Γ)
  proof: by
  refine l.induction_on fun l => ?_
  simp only [ListBlank.append_mk, ListBlank.flatMap_mk, ListBlank.cons_mk, List.flatMap_cons]

中文:
定理 ListBlank.cons_flatMap
  结论: {Γ Γ'} [Inhabited Γ] [Inhabited Γ'] (a : Γ) (l : ListBlank Γ)
  证明: by
  refine l.induction_on fun l => ?_
  simp only [ListBlank.append_mk, ListBlank.flatMap_mk, ListBlank.cons_mk, List.flatMap_cons]

Depends on / 依赖: List.flatMap_cons, ListBlank, ListBlank.append_mk, ListBlank.cons_mk, ListBlank.flatMap_mk, append_mk, cons_mk, flatMap_cons, flatMap_mk, induction_on, l.induction_on
-/
theorem ListBlank.cons_flatMap {Γ Γ'} [Inhabited Γ] [Inhabited Γ'] (a : Γ) (l : ListBlank Γ)
    (f : Γ -> List Γ') (hf) : (l.cons a).flatMap f hf = (l.flatMap f hf).append (f a) := by
  refine l.induction_on fun l => ?_
  simp only [ListBlank.append_mk, ListBlank.flatMap_mk, ListBlank.cons_mk, List.flatMap_cons]

end ListBlank

section Tape

/--
Definition of `Tape` / `Tape` 的定义

English:
structure Tape
  parameters: (Γ : Type*) [Inhabited Γ]
  axioms and operations (3):
    - head : Γ
    - left : ListBlank Γ
    - right : ListBlank Γ

中文:
结构 Tape
  参数: (Γ : 类型) [Inhabited Γ]
  公理与运算 (3 个):
    - head : Γ
    - left : ListBlank Γ
    - right : ListBlank Γ
-/
structure Tape (Γ : Type*) [Inhabited Γ] where
  /-- The current position of the head. -/
  head : Γ
  /-- The portion of the tape going off to the left. -/
  left : ListBlank Γ
  /-- The portion of the tape going off to the right. -/
  right : ListBlank Γ

/--
Instance `Tape.inhabited` / 实例 `Tape.inhabited`

English:
instance Tape.inhabited
  signature: {Γ} [Inhabited Γ]
  body: ⟨by constructor <;> apply default⟩

中文:
实例 Tape.inhabited
  签名: {Γ} [Inhabited Γ]
  定义体: ⟨by constructor <;> apply default⟩
-/
instance Tape.inhabited {Γ} [Inhabited Γ] : Inhabited (Tape Γ) :=
  ⟨by constructor <;> apply default⟩

/--
Inductive type `Dir` / 归纳类型 `Dir`

English:
inductive Dir
  constructors (2):
    - left: 
    - right: 

中文:
归纳类型 Dir
  构造子 (2 个):
    - left: 
    - right: 
-/
inductive Dir
  | left
  | right
  deriving DecidableEq, Inhabited

/--
Definition of `Tape.left₀` / `Tape.left₀` 的定义

English:
definition Tape.left₀
  signature: {Γ} [Inhabited Γ] (T : Tape Γ)
  body: T.left.cons T.head

中文:
定义 Tape.left₀
  签名: {Γ} [Inhabited Γ] (T : Tape Γ)
  定义体: T.left.cons T.head

Depends on / 依赖: T.head, T.left.cons
-/
def Tape.left₀ {Γ} [Inhabited Γ] (T : Tape Γ) : ListBlank Γ :=
  T.left.cons T.head

/--
Definition of `Tape.right₀` / `Tape.right₀` 的定义

English:
definition Tape.right₀
  signature: {Γ} [Inhabited Γ] (T : Tape Γ)
  body: T.right.cons T.head

中文:
定义 Tape.right₀
  签名: {Γ} [Inhabited Γ] (T : Tape Γ)
  定义体: T.right.cons T.head

Depends on / 依赖: T.head, T.right.cons
-/
def Tape.right₀ {Γ} [Inhabited Γ] (T : Tape Γ) : ListBlank Γ :=
  T.right.cons T.head

/--
Definition of `Tape.move` / `Tape.move` 的定义

English:
definition Tape.move
  signature: {Γ} [Inhabited Γ]

中文:
定义 Tape.move
  签名: {Γ} [Inhabited Γ]
-/
def Tape.move {Γ} [Inhabited Γ] : Dir -> Tape Γ -> Tape Γ
  | Dir.left, ⟨a, L, R⟩ => ⟨L.head, L.tail, R.cons a⟩
  | Dir.right, ⟨a, L, R⟩ => ⟨R.head, L.cons a, R.tail⟩

@[simp]
/--
theorem `Tape.move_left_right` / 定理 `Tape.move_left_right`

English:
theorem Tape.move_left_right
  given: {Γ} [Inhabited Γ] (T : Tape Γ)
  proof: by
  simp [Tape.move]

@[simp]

中文:
定理 Tape.move_left_right
  条件: {Γ} [Inhabited Γ] (T : Tape Γ)
  证明: by
  simp [Tape.move]

@[simp]

Depends on / 依赖: Tape.move
-/
theorem Tape.move_left_right {Γ} [Inhabited Γ] (T : Tape Γ) :
    (T.move Dir.left).move Dir.right = T := by
  simp [Tape.move]

@[simp]
/--
theorem `Tape.move_right_left` / 定理 `Tape.move_right_left`

English:
theorem Tape.move_right_left
  given: {Γ} [Inhabited Γ] (T : Tape Γ)
  proof: by
  simp [Tape.move]

中文:
定理 Tape.move_right_left
  条件: {Γ} [Inhabited Γ] (T : Tape Γ)
  证明: by
  simp [Tape.move]

Depends on / 依赖: Tape.move
-/
theorem Tape.move_right_left {Γ} [Inhabited Γ] (T : Tape Γ) :
    (T.move Dir.right).move Dir.left = T := by
  simp [Tape.move]

/--
Definition of `Tape.mk'` / `Tape.mk'` 的定义

English:
definition Tape.mk'
  signature: {Γ} [Inhabited Γ] (L R : ListBlank Γ)
  body: ⟨R.head, L, R.tail⟩

@[simp]

中文:
定义 Tape.mk'
  签名: {Γ} [Inhabited Γ] (L R : ListBlank Γ)
  定义体: ⟨R.head, L, R.tail⟩

@[simp]

Depends on / 依赖: R.head, R.tail
-/
def Tape.mk' {Γ} [Inhabited Γ] (L R : ListBlank Γ) : Tape Γ :=
  ⟨R.head, L, R.tail⟩

@[simp]
/--
theorem `Tape.mk'_left` / 定理 `Tape.mk'_left`

English:
theorem Tape.mk'_left
  given: {Γ} [Inhabited Γ] (L R : ListBlank Γ)
  statement: (Tape.mk' L R).left = L
  proof: rfl

@[simp]

中文:
定理 Tape.mk'_left
  条件: {Γ} [Inhabited Γ] (L R : ListBlank Γ)
  结论: (Tape.mk' L R).left = L
  证明: rfl

@[simp]
-/
theorem Tape.mk'_left {Γ} [Inhabited Γ] (L R : ListBlank Γ) : (Tape.mk' L R).left = L :=
  rfl

@[simp]
/--
theorem `Tape.mk'_head` / 定理 `Tape.mk'_head`

English:
theorem Tape.mk'_head
  given: {Γ} [Inhabited Γ] (L R : ListBlank Γ)
  statement: (Tape.mk' L R).head = R.head
  proof: rfl

@[simp]

中文:
定理 Tape.mk'_head
  条件: {Γ} [Inhabited Γ] (L R : ListBlank Γ)
  结论: (Tape.mk' L R).head = R.head
  证明: rfl

@[simp]
-/
theorem Tape.mk'_head {Γ} [Inhabited Γ] (L R : ListBlank Γ) : (Tape.mk' L R).head = R.head :=
  rfl

@[simp]
/--
theorem `Tape.mk'_right` / 定理 `Tape.mk'_right`

English:
theorem Tape.mk'_right
  given: {Γ} [Inhabited Γ] (L R : ListBlank Γ)
  statement: (Tape.mk' L R).right = R.tail
  proof: rfl

@[simp]

中文:
定理 Tape.mk'_right
  条件: {Γ} [Inhabited Γ] (L R : ListBlank Γ)
  结论: (Tape.mk' L R).right = R.tail
  证明: rfl

@[simp]
-/
theorem Tape.mk'_right {Γ} [Inhabited Γ] (L R : ListBlank Γ) : (Tape.mk' L R).right = R.tail :=
  rfl

@[simp]
/--
theorem `Tape.mk'_right₀` / 定理 `Tape.mk'_right₀`

English:
theorem Tape.mk'_right₀
  given: {Γ} [Inhabited Γ] (L R : ListBlank Γ)
  statement: (Tape.mk' L R).right₀ = R
  proof: ListBlank.cons_head_tail _

@[simp]

中文:
定理 Tape.mk'_right₀
  条件: {Γ} [Inhabited Γ] (L R : ListBlank Γ)
  结论: (Tape.mk' L R).right₀ = R
  证明: ListBlank.cons_head_tail _

@[simp]
-/
theorem Tape.mk'_right₀ {Γ} [Inhabited Γ] (L R : ListBlank Γ) : (Tape.mk' L R).right₀ = R :=
  ListBlank.cons_head_tail _

@[simp]
/--
theorem `Tape.mk'_left_right₀` / 定理 `Tape.mk'_left_right₀`

English:
theorem Tape.mk'_left_right₀
  given: {Γ} [Inhabited Γ] (T : Tape Γ)
  statement: Tape.mk' T.left T.right₀ = T
  proof: by
  simp only [Tape.right₀, Tape.mk', ListBlank.head_cons, ListBlank.tail_cons]

中文:
定理 Tape.mk'_left_right₀
  条件: {Γ} [Inhabited Γ] (T : Tape Γ)
  结论: Tape.mk' T.left T.right₀ = T
  证明: by
  simp only [Tape.right₀, Tape.mk', ListBlank.head_cons, ListBlank.tail_cons]
-/
theorem Tape.mk'_left_right₀ {Γ} [Inhabited Γ] (T : Tape Γ) : Tape.mk' T.left T.right₀ = T := by
  simp only [Tape.right₀, Tape.mk', ListBlank.head_cons, ListBlank.tail_cons]

/--
theorem `Tape.exists_mk'` / 定理 `Tape.exists_mk'`

English:
theorem Tape.exists_mk'
  given: {Γ} [Inhabited Γ] (T : Tape Γ)
  statement: exists L R, T = Tape.mk' L R
  proof: ⟨_, _, (Tape.mk'_left_right₀ _).symm⟩

@[simp]

中文:
定理 Tape.exists_mk'
  条件: {Γ} [Inhabited Γ] (T : Tape Γ)
  结论: 存在 L R, T = Tape.mk' L R
  证明: ⟨_, _, (Tape.mk'_left_right₀ _).symm⟩

@[simp]

Depends on / 依赖: Tape.mk
-/
theorem Tape.exists_mk' {Γ} [Inhabited Γ] (T : Tape Γ) : exists L R, T = Tape.mk' L R :=
  ⟨_, _, (Tape.mk'_left_right₀ _).symm⟩

@[simp]
/--
theorem `Tape.move_left_mk'` / 定理 `Tape.move_left_mk'`

English:
theorem Tape.move_left_mk'
  given: {Γ} [Inhabited Γ] (L R : ListBlank Γ)
  proof: by
  simp only [Tape.move, Tape.mk', ListBlank.head_cons, ListBlank.cons_head_tail,
    ListBlank.tail_cons]

@[simp]

中文:
定理 Tape.move_left_mk'
  条件: {Γ} [Inhabited Γ] (L R : ListBlank Γ)
  证明: by
  simp only [Tape.move, Tape.mk', ListBlank.head_cons, ListBlank.cons_head_tail,
    ListBlank.tail_cons]

@[simp]

Depends on / 依赖: ListBlank, ListBlank.cons_head_tail, ListBlank.head_cons, ListBlank.tail_cons, Tape.mk, Tape.move, cons_head_tail, head_cons, tail_cons
-/
theorem Tape.move_left_mk' {Γ} [Inhabited Γ] (L R : ListBlank Γ) :
    (Tape.mk' L R).move Dir.left = Tape.mk' L.tail (R.cons L.head) := by
  simp only [Tape.move, Tape.mk', ListBlank.head_cons, ListBlank.cons_head_tail,
    ListBlank.tail_cons]

@[simp]
/--
theorem `Tape.move_right_mk'` / 定理 `Tape.move_right_mk'`

English:
theorem Tape.move_right_mk'
  given: {Γ} [Inhabited Γ] (L R : ListBlank Γ)
  proof: by
  simp only [Tape.move, Tape.mk']

中文:
定理 Tape.move_right_mk'
  条件: {Γ} [Inhabited Γ] (L R : ListBlank Γ)
  证明: by
  simp only [Tape.move, Tape.mk']

Depends on / 依赖: Tape.mk, Tape.move
-/
theorem Tape.move_right_mk' {Γ} [Inhabited Γ] (L R : ListBlank Γ) :
    (Tape.mk' L R).move Dir.right = Tape.mk' (L.cons R.head) R.tail := by
  simp only [Tape.move, Tape.mk']

/--
Definition of `Tape.mk₂` / `Tape.mk₂` 的定义

English:
definition Tape.mk₂
  signature: {Γ} [Inhabited Γ] (L R : List Γ)
  body: Tape.mk' (ListBlank.mk L) (ListBlank.mk R)

中文:
定义 Tape.mk₂
  签名: {Γ} [Inhabited Γ] (L R : List Γ)
  定义体: Tape.mk' (ListBlank.mk L) (ListBlank.mk R)

Depends on / 依赖: ListBlank, ListBlank.mk, Tape.mk
-/
def Tape.mk₂ {Γ} [Inhabited Γ] (L R : List Γ) : Tape Γ :=
  Tape.mk' (ListBlank.mk L) (ListBlank.mk R)

/--
Definition of `Tape.mk₁` / `Tape.mk₁` 的定义

English:
definition Tape.mk₁
  signature: {Γ} [Inhabited Γ] (l : List Γ)
  body: Tape.mk₂ [] l

中文:
定义 Tape.mk₁
  签名: {Γ} [Inhabited Γ] (l : List Γ)
  定义体: Tape.mk₂ [] l

Depends on / 依赖: Tape.mk
-/
def Tape.mk₁ {Γ} [Inhabited Γ] (l : List Γ) : Tape Γ :=
  Tape.mk₂ [] l

/--
Definition of `Tape.nth` / `Tape.nth` 的定义

English:
definition Tape.nth
  signature: {Γ} [Inhabited Γ] (T : Tape Γ)

中文:
定义 Tape.nth
  签名: {Γ} [Inhabited Γ] (T : Tape Γ)
-/
def Tape.nth {Γ} [Inhabited Γ] (T : Tape Γ) : Int -> Γ
  | 0 => T.head
  | (n + 1 : Nat) => T.right.nth n
  | -(n + 1 : Nat) => T.left.nth n

@[simp]
/--
theorem `Tape.nth_zero` / 定理 `Tape.nth_zero`

English:
theorem Tape.nth_zero
  given: {Γ} [Inhabited Γ] (T : Tape Γ)
  statement: T.nth 0 = T.1
  proof: rfl

中文:
定理 Tape.nth_zero
  条件: {Γ} [Inhabited Γ] (T : Tape Γ)
  结论: T.nth 0 = T.1
  证明: rfl
-/
theorem Tape.nth_zero {Γ} [Inhabited Γ] (T : Tape Γ) : T.nth 0 = T.1 :=
  rfl

/--
theorem `Tape.right₀_nth` / 定理 `Tape.right₀_nth`

English:
theorem Tape.right₀_nth
  given: {Γ} [Inhabited Γ] (T : Tape Γ) (n : Nat)
  statement: T.right₀.nth n = T.nth n
  proof: by
  cases n <;> simp only [Tape.nth, Tape.right₀, ListBlank.nth_zero,
    ListBlank.nth_succ, ListBlank.head_cons, ListBlank.tail_cons]

@[simp]

中文:
定理 Tape.right₀_nth
  条件: {Γ} [Inhabited Γ] (T : Tape Γ) (n : 自然数)
  结论: T.right₀.nth n = T.nth n
  证明: by
  cases n <;> simp only [Tape.nth, Tape.right₀, ListBlank.nth_zero,
    ListBlank.nth_succ, ListBlank.head_cons, ListBlank.tail_cons]

@[simp]

Depends on / 依赖: ListBlank, ListBlank.head_cons, ListBlank.nth_succ, ListBlank.nth_zero, ListBlank.tail_cons, Tape.nth, Tape.right, head_cons, nth_succ, nth_zero, tail_cons
-/
theorem Tape.right₀_nth {Γ} [Inhabited Γ] (T : Tape Γ) (n : Nat) : T.right₀.nth n = T.nth n := by
  cases n <;> simp only [Tape.nth, Tape.right₀, ListBlank.nth_zero,
    ListBlank.nth_succ, ListBlank.head_cons, ListBlank.tail_cons]

@[simp]
/--
theorem `Tape.mk'_nth_nat` / 定理 `Tape.mk'_nth_nat`

English:
theorem Tape.mk'_nth_nat
  given: {Γ} [Inhabited Γ] (L R : ListBlank Γ) (n : Nat)
  proof: by
  rw [← Tape.right₀_nth]; rw [Tape.mk'_right₀]

@[simp]

中文:
定理 Tape.mk'_nth_nat
  条件: {Γ} [Inhabited Γ] (L R : ListBlank Γ) (n : 自然数)
  证明: by
  rw [← Tape.right₀_nth]; rw [Tape.mk'_right₀]

@[simp]
-/
theorem Tape.mk'_nth_nat {Γ} [Inhabited Γ] (L R : ListBlank Γ) (n : Nat) :
    (Tape.mk' L R).nth n = R.nth n := by
  rw [← Tape.right₀_nth]; rw [Tape.mk'_right₀]

@[simp]
/--
theorem `Tape.move_left_nth` / 定理 `Tape.move_left_nth`

English:
theorem Tape.move_left_nth
  given: {Γ} [Inhabited Γ]

中文:
定理 Tape.move_left_nth
  条件: {Γ} [Inhabited Γ]
-/
theorem Tape.move_left_nth {Γ} [Inhabited Γ] :
    forall (T : Tape Γ) (i : Int), (T.move Dir.left).nth i = T.nth (i - 1)
  | ⟨_, _, _⟩, -(_ + 1 : Nat) => (ListBlank.nth_succ _ _).symm
  | ⟨_, _, _⟩, 0 => (ListBlank.nth_zero _).symm
  | ⟨_, _, _⟩, 1 => (ListBlank.nth_zero _).trans (ListBlank.head_cons _ _)
  | ⟨a, L, R⟩, (n + 1 : Nat) + 1 => by
    rw [add_sub_cancel_right]
    change (R.cons a).nth (n + 1) = R.nth n
    rw [ListBlank.nth_succ]; rw [ListBlank.tail_cons]

@[simp]
/--
theorem `Tape.move_right_nth` / 定理 `Tape.move_right_nth`

English:
theorem Tape.move_right_nth
  given: {Γ} [Inhabited Γ] (T : Tape Γ) (i : Int)
  proof: by
  conv => rhs; rw [← T.move_right_left]
  rw [Tape.move_left_nth]; rw [add_sub_cancel_right]

@[simp]

中文:
定理 Tape.move_right_nth
  条件: {Γ} [Inhabited Γ] (T : Tape Γ) (i : 整数)
  证明: by
  conv => rhs; rw [← T.move_right_left]
  rw [Tape.move_left_nth]; rw [add_sub_cancel_right]

@[simp]

Depends on / 依赖: T.move_right_left, Tape.move_left_nth, add_sub_cancel_right, move_left_nth, move_right_left
-/
theorem Tape.move_right_nth {Γ} [Inhabited Γ] (T : Tape Γ) (i : Int) :
    (T.move Dir.right).nth i = T.nth (i + 1) := by
  conv => rhs; rw [← T.move_right_left]
  rw [Tape.move_left_nth]; rw [add_sub_cancel_right]

@[simp]
/--
theorem `Tape.move_right_n_head` / 定理 `Tape.move_right_n_head`

English:
theorem Tape.move_right_n_head
  given: {Γ} [Inhabited Γ] (T : Tape Γ) (i : Nat)
  proof: by
  induction i generalizing T
  · rfl
  · simp only [*, Tape.move_right_nth, Int.natCast_succ, iterate_succ, Function.comp_apply]

中文:
定理 Tape.move_right_n_head
  条件: {Γ} [Inhabited Γ] (T : Tape Γ) (i : 自然数)
  证明: by
  induction i generalizing T
  · rfl
  · simp only [*, Tape.move_right_nth, Int.natCast_succ, iterate_succ, Function.comp_apply]

Depends on / 依赖: Function, Function.comp_apply, Int.natCast_succ, Tape.move_right_nth, comp_apply, generalizing, iterate_succ, move_right_nth, natCast_succ
-/
theorem Tape.move_right_n_head {Γ} [Inhabited Γ] (T : Tape Γ) (i : Nat) :
    ((Tape.move Dir.right)^[i] T).head = T.nth i := by
  induction i generalizing T
  · rfl
  · simp only [*, Tape.move_right_nth, Int.natCast_succ, iterate_succ, Function.comp_apply]

/--
Definition of `Tape.write` / `Tape.write` 的定义

English:
definition Tape.write
  signature: {Γ} [Inhabited Γ] (b : Γ) (T : Tape Γ)
  body: { T with head := b }

@[simp]

中文:
定义 Tape.write
  签名: {Γ} [Inhabited Γ] (b : Γ) (T : Tape Γ)
  定义体: { T with head := b }

@[simp]
-/
def Tape.write {Γ} [Inhabited Γ] (b : Γ) (T : Tape Γ) : Tape Γ :=
  { T with head := b }

@[simp]
/--
theorem `Tape.write_self` / 定理 `Tape.write_self`

English:
theorem Tape.write_self
  given: {Γ} [Inhabited Γ]
  statement: forall T : Tape Γ, T.write T.1 = T
  proof: by
  rintro ⟨⟩; rfl

@[simp]

中文:
定理 Tape.write_self
  条件: {Γ} [Inhabited Γ]
  结论: 对任意 T : Tape Γ, T.write T.1 = T
  证明: by
  rintro ⟨⟩; rfl

@[simp]
-/
theorem Tape.write_self {Γ} [Inhabited Γ] : forall T : Tape Γ, T.write T.1 = T := by
  rintro ⟨⟩; rfl

@[simp]
/--
theorem `Tape.write_nth` / 定理 `Tape.write_nth`

English:
theorem Tape.write_nth
  given: {Γ} [Inhabited Γ] (b : Γ)

中文:
定理 Tape.write_nth
  条件: {Γ} [Inhabited Γ] (b : Γ)
-/
theorem Tape.write_nth {Γ} [Inhabited Γ] (b : Γ) :
    forall (T : Tape Γ) {i : Int}, (T.write b).nth i = if i = 0 then b else T.nth i
  | _, 0 => rfl
  | _, (_ + 1 : Nat) => rfl
  | _, -(_ + 1 : Nat) => rfl

@[simp]
/--
theorem `Tape.write_mk` / 定理 `Tape.write_mk`

English:
theorem Tape.write_mk
  given: {Γ} [Inhabited Γ] (a b : Γ) (L R : ListBlank Γ)
  proof: rfl

@[simp]

中文:
定理 Tape.write_mk
  条件: {Γ} [Inhabited Γ] (a b : Γ) (L R : ListBlank Γ)
  证明: rfl

@[simp]
-/
theorem Tape.write_mk {Γ} [Inhabited Γ] (a b : Γ) (L R : ListBlank Γ) :
    (mk a L R).write b = mk b L R := rfl

@[simp]
/--
theorem `Tape.write_mk'` / 定理 `Tape.write_mk'`

English:
theorem Tape.write_mk'
  given: {Γ} [Inhabited Γ] (b : Γ) (L R : ListBlank Γ)
  proof: by simp [mk']

中文:
定理 Tape.write_mk'
  条件: {Γ} [Inhabited Γ] (b : Γ) (L R : ListBlank Γ)
  证明: by simp [mk']
-/
theorem Tape.write_mk' {Γ} [Inhabited Γ] (b : Γ) (L R : ListBlank Γ) :
    (mk' L R).write b = mk' L (R.tail.cons b) := by simp [mk']

/--
Definition of `Tape.map` / `Tape.map` 的定义

English:
definition Tape.map
  signature: {Γ Γ'} [Inhabited Γ] [Inhabited Γ'] (f : PointedMap Γ Γ') (T : Tape Γ)
  body: ⟨f T.1, T.2.map f, T.3.map f⟩

@[simp]

中文:
定义 Tape.map
  签名: {Γ Γ'} [Inhabited Γ] [Inhabited Γ'] (f : PointedMap Γ Γ') (T : Tape Γ)
  定义体: ⟨f T.1, T.2.map f, T.3.map f⟩

@[simp]
-/
def Tape.map {Γ Γ'} [Inhabited Γ] [Inhabited Γ'] (f : PointedMap Γ Γ') (T : Tape Γ) : Tape Γ' :=
  ⟨f T.1, T.2.map f, T.3.map f⟩

@[simp]
/--
theorem `Tape.map_fst` / 定理 `Tape.map_fst`

English:
theorem Tape.map_fst
  given: {Γ Γ'} [Inhabited Γ] [Inhabited Γ'] (f : PointedMap Γ Γ')
  proof: by
  rintro ⟨⟩; rfl

@[simp]

中文:
定理 Tape.map_fst
  条件: {Γ Γ'} [Inhabited Γ] [Inhabited Γ'] (f : PointedMap Γ Γ')
  证明: by
  rintro ⟨⟩; rfl

@[simp]
-/
theorem Tape.map_fst {Γ Γ'} [Inhabited Γ] [Inhabited Γ'] (f : PointedMap Γ Γ') :
    forall T : Tape Γ, (T.map f).1 = f T.1 := by
  rintro ⟨⟩; rfl

@[simp]
/--
theorem `Tape.map_write` / 定理 `Tape.map_write`

English:
theorem Tape.map_write
  given: {Γ Γ'} [Inhabited Γ] [Inhabited Γ'] (f : PointedMap Γ Γ') (b : Γ)
  proof: by
  rintro ⟨⟩; rfl

@[simp]

中文:
定理 Tape.map_write
  条件: {Γ Γ'} [Inhabited Γ] [Inhabited Γ'] (f : PointedMap Γ Γ') (b : Γ)
  证明: by
  rintro ⟨⟩; rfl

@[simp]
-/
theorem Tape.map_write {Γ Γ'} [Inhabited Γ] [Inhabited Γ'] (f : PointedMap Γ Γ') (b : Γ) :
    forall T : Tape Γ, (T.write b).map f = (T.map f).write (f b) := by
  rintro ⟨⟩; rfl

@[simp]
/--
theorem `Tape.write_move_right_n` / 定理 `Tape.write_move_right_n`

English:
theorem Tape.write_move_right_n
  given: {Γ} [Inhabited Γ] (f : Γ -> Γ) (L R : ListBlank Γ) (n : Nat)
  proof: by
  induction n generalizing L R <;> simp [*]

中文:
定理 Tape.write_move_right_n
  条件: {Γ} [Inhabited Γ] (f : Γ -> Γ) (L R : ListBlank Γ) (n : 自然数)
  证明: by
  induction n generalizing L R <;> simp [*]

Depends on / 依赖: generalizing
-/
theorem Tape.write_move_right_n {Γ} [Inhabited Γ] (f : Γ -> Γ) (L R : ListBlank Γ) (n : Nat) :
    ((Tape.move Dir.right)^[n] (Tape.mk' L R)).write (f (R.nth n)) =
      (Tape.move Dir.right)^[n] (Tape.mk' L (R.modifyNth f n)) := by
  induction n generalizing L R <;> simp [*]

/--
theorem `Tape.map_move` / 定理 `Tape.map_move`

English:
theorem Tape.map_move
  given: {Γ Γ'} [Inhabited Γ] [Inhabited Γ'] (f : PointedMap Γ Γ') (T : Tape Γ) (d)
  proof: by
  cases T
  cases d <;> simp only [Tape.move, Tape.map, ListBlank.head_map,
    ListBlank.map_cons, ListBlank.tail_map]

中文:
定理 Tape.map_move
  条件: {Γ Γ'} [Inhabited Γ] [Inhabited Γ'] (f : PointedMap Γ Γ') (T : Tape Γ) (d)
  证明: by
  cases T
  cases d <;> simp only [Tape.move, Tape.map, ListBlank.head_map,
    ListBlank.map_cons, ListBlank.tail_map]

Depends on / 依赖: ListBlank, ListBlank.head_map, ListBlank.map_cons, ListBlank.tail_map, Tape.map, Tape.move, head_map, map_cons, tail_map
-/
theorem Tape.map_move {Γ Γ'} [Inhabited Γ] [Inhabited Γ'] (f : PointedMap Γ Γ') (T : Tape Γ) (d) :
    (T.move d).map f = (T.map f).move d := by
  cases T
  cases d <;> simp only [Tape.move, Tape.map, ListBlank.head_map,
    ListBlank.map_cons, ListBlank.tail_map]

/--
theorem `Tape.map_mk'` / 定理 `Tape.map_mk'`

English:
theorem Tape.map_mk'
  given: {Γ Γ'} [Inhabited Γ] [Inhabited Γ'] (f : PointedMap Γ Γ') (L R : ListBlank Γ)
  proof: by
  simp only [Tape.mk', Tape.map, ListBlank.head_map,
    ListBlank.tail_map]

中文:
定理 Tape.map_mk'
  条件: {Γ Γ'} [Inhabited Γ] [Inhabited Γ'] (f : PointedMap Γ Γ') (L R : ListBlank Γ)
  证明: by
  simp only [Tape.mk', Tape.map, ListBlank.head_map,
    ListBlank.tail_map]

Depends on / 依赖: ListBlank, ListBlank.head_map, ListBlank.tail_map, Tape.map, Tape.mk, head_map, tail_map
-/
theorem Tape.map_mk' {Γ Γ'} [Inhabited Γ] [Inhabited Γ'] (f : PointedMap Γ Γ') (L R : ListBlank Γ) :
    (Tape.mk' L R).map f = Tape.mk' (L.map f) (R.map f) := by
  simp only [Tape.mk', Tape.map, ListBlank.head_map,
    ListBlank.tail_map]

/--
theorem `Tape.map_mk₂` / 定理 `Tape.map_mk₂`

English:
theorem Tape.map_mk₂
  given: {Γ Γ'} [Inhabited Γ] [Inhabited Γ'] (f : PointedMap Γ Γ') (L R : List Γ)
  proof: by
  simp only [Tape.mk₂, Tape.map_mk', ListBlank.map_mk]

中文:
定理 Tape.map_mk₂
  条件: {Γ Γ'} [Inhabited Γ] [Inhabited Γ'] (f : PointedMap Γ Γ') (L R : List Γ)
  证明: by
  simp only [Tape.mk₂, Tape.map_mk', ListBlank.map_mk]

Depends on / 依赖: ListBlank, ListBlank.map_mk, Tape.map_mk, Tape.mk, map_mk
-/
theorem Tape.map_mk₂ {Γ Γ'} [Inhabited Γ] [Inhabited Γ'] (f : PointedMap Γ Γ') (L R : List Γ) :
    (Tape.mk₂ L R).map f = Tape.mk₂ (L.map f) (R.map f) := by
  simp only [Tape.mk₂, Tape.map_mk', ListBlank.map_mk]

/--
theorem `Tape.map_mk₁` / 定理 `Tape.map_mk₁`

English:
theorem Tape.map_mk₁
  given: {Γ Γ'} [Inhabited Γ] [Inhabited Γ'] (f : PointedMap Γ Γ') (l : List Γ)
  proof: Tape.map_mk₂ _ _ _

中文:
定理 Tape.map_mk₁
  条件: {Γ Γ'} [Inhabited Γ] [Inhabited Γ'] (f : PointedMap Γ Γ') (l : List Γ)
  证明: Tape.map_mk₂ _ _ _

Depends on / 依赖: Tape.map_mk
-/
theorem Tape.map_mk₁ {Γ Γ'} [Inhabited Γ] [Inhabited Γ'] (f : PointedMap Γ Γ') (l : List Γ) :
    (Tape.mk₁ l).map f = Tape.mk₁ (l.map f) :=
  Tape.map_mk₂ _ _ _

end Tape

end Turing
