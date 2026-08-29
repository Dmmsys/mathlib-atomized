/-
Copyright (c) 2017 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
module

public import Mathlib.Logic.OpClass
public import Mathlib.Order.Lattice

/-!
# `max` and `min`

This file proves basic properties about maxima and minima on a `LinearOrder`.

## Tags

min, max
-/

public section


universe u v

variable {α : Type u} {β : Type v}

section

variable [LinearOrder α] [LinearOrder β] {f : α -> β} {s : Set α} {a b c d : α}

-- translate from lattices to linear orders (sup → max, inf → min)
@[to_dual max_le_iff]
/--
theorem `le_min_iff` / 定理 `le_min_iff`

English:
theorem le_min_iff
  statement: c <= min a b ↔ c <= a ∧ c <= b
  proof: le_inf_iff

@[to_dual min_le_iff]

中文:
定理 le_min_iff
  结论: c <= min a b ↔ c <= a ∧ c <= b
  证明: le_inf_iff

@[to_dual min_le_iff]

Depends on / 依赖: le_inf_iff
-/
theorem le_min_iff : c <= min a b ↔ c <= a ∧ c <= b :=
  le_inf_iff

@[to_dual min_le_iff]
/--
theorem `le_max_iff` / 定理 `le_max_iff`

English:
theorem le_max_iff
  statement: a <= max b c ↔ a <= b ∨ a <= c
  proof: le_sup_iff

@[to_dual]

中文:
定理 le_max_iff
  结论: a <= max b c ↔ a <= b ∨ a <= c
  证明: le_sup_iff

@[to_dual]

Depends on / 依赖: le_sup_iff
-/
theorem le_max_iff : a <= max b c ↔ a <= b ∨ a <= c :=
  le_sup_iff

@[to_dual]
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Std.LawfulOrderSup α
  body: max_le_iff

@[to_dual max_lt_iff]

中文:
实例 :
  签名: Std.LawfulOrderSup α
  定义体: max_le_iff

@[to_dual max_lt_iff]

Depends on / 依赖: max_le_iff
-/
instance : Std.LawfulOrderSup α where
  max_le_iff _ _ _ := max_le_iff

@[to_dual max_lt_iff]
/--
theorem `lt_min_iff` / 定理 `lt_min_iff`

English:
theorem lt_min_iff
  statement: a < min b c ↔ a < b ∧ a < c
  proof: lt_inf_iff

@[to_dual min_lt_iff]

中文:
定理 lt_min_iff
  结论: a < min b c ↔ a < b ∧ a < c
  证明: lt_inf_iff

@[to_dual min_lt_iff]

Depends on / 依赖: lt_inf_iff
-/
theorem lt_min_iff : a < min b c ↔ a < b ∧ a < c :=
  lt_inf_iff

@[to_dual min_lt_iff]
/--
theorem `lt_max_iff` / 定理 `lt_max_iff`

English:
theorem lt_max_iff
  statement: a < max b c ↔ a < b ∨ a < c
  proof: lt_sup_iff

@[to_dual]

中文:
定理 lt_max_iff
  结论: a < max b c ↔ a < b ∨ a < c
  证明: lt_sup_iff

@[to_dual]

Depends on / 依赖: lt_sup_iff
-/
theorem lt_max_iff : a < max b c ↔ a < b ∨ a < c :=
  lt_sup_iff

@[to_dual]
/--
theorem `max_le_max` / 定理 `max_le_max`

English:
theorem max_le_max
  statement: a <= c -> b <= d -> max a b <= max c d
  proof: sup_le_sup

@[to_dual]

中文:
定理 max_le_max
  结论: a <= c -> b <= d -> max a b <= max c d
  证明: sup_le_sup

@[to_dual]

Depends on / 依赖: sup_le_sup
-/
theorem max_le_max : a <= c -> b <= d -> max a b <= max c d :=
  sup_le_sup

@[to_dual]
/--
theorem `max_le_max_left` / 定理 `max_le_max_left`

English:
theorem max_le_max_left
  given: (c) (h : a <= b)
  statement: max c a <= max c b
  proof: sup_le_sup_left h c

@[to_dual]

中文:
定理 max_le_max_left
  条件: (c) (h : a <= b)
  结论: max c a <= max c b
  证明: sup_le_sup_left h c

@[to_dual]

Depends on / 依赖: sup_le_sup_left
-/
theorem max_le_max_left (c) (h : a <= b) : max c a <= max c b := sup_le_sup_left h c

@[to_dual]
/--
theorem `max_le_max_right` / 定理 `max_le_max_right`

English:
theorem max_le_max_right
  given: (c) (h : a <= b)
  statement: max a c <= max b c
  proof: sup_le_sup_right h c

@[to_dual min_le_of_left_le]

中文:
定理 max_le_max_right
  条件: (c) (h : a <= b)
  结论: max a c <= max b c
  证明: sup_le_sup_right h c

@[to_dual min_le_of_left_le]

Depends on / 依赖: sup_le_sup_right
-/
theorem max_le_max_right (c) (h : a <= b) : max a c <= max b c := sup_le_sup_right h c

@[to_dual min_le_of_left_le]
/--
theorem `le_max_of_le_left` / 定理 `le_max_of_le_left`

English:
theorem le_max_of_le_left
  statement: a <= b -> a <= max b c
  proof: le_sup_of_le_left

@[to_dual min_le_of_right_le]

中文:
定理 le_max_of_le_left
  结论: a <= b -> a <= max b c
  证明: le_sup_of_le_left

@[to_dual min_le_of_right_le]

Depends on / 依赖: le_sup_of_le_left
-/
theorem le_max_of_le_left : a <= b -> a <= max b c :=
  le_sup_of_le_left

@[to_dual min_le_of_right_le]
/--
theorem `le_max_of_le_right` / 定理 `le_max_of_le_right`

English:
theorem le_max_of_le_right
  statement: a <= c -> a <= max b c
  proof: le_sup_of_le_right

@[to_dual min_lt_of_left_lt]

中文:
定理 le_max_of_le_right
  结论: a <= c -> a <= max b c
  证明: le_sup_of_le_right

@[to_dual min_lt_of_left_lt]

Depends on / 依赖: le_sup_of_le_right
-/
theorem le_max_of_le_right : a <= c -> a <= max b c :=
  le_sup_of_le_right

@[to_dual min_lt_of_left_lt]
/--
theorem `lt_max_of_lt_left` / 定理 `lt_max_of_lt_left`

English:
theorem lt_max_of_lt_left
  given: (h : a < b)
  statement: a < max b c
  proof: h.trans_le (le_max_left b c)

@[to_dual min_lt_of_right_lt]

中文:
定理 lt_max_of_lt_left
  条件: (h : a < b)
  结论: a < max b c
  证明: h.trans_le (le_max_left b c)

@[to_dual min_lt_of_right_lt]

Depends on / 依赖: h.trans_le, le_max_left, trans_le
-/
theorem lt_max_of_lt_left (h : a < b) : a < max b c :=
  h.trans_le (le_max_left b c)

@[to_dual min_lt_of_right_lt]
/--
theorem `lt_max_of_lt_right` / 定理 `lt_max_of_lt_right`

English:
theorem lt_max_of_lt_right
  given: (h : a < c)
  statement: a < max b c
  proof: h.trans_le (le_max_right b c)

@[to_dual]

中文:
定理 lt_max_of_lt_right
  条件: (h : a < c)
  结论: a < max b c
  证明: h.trans_le (le_max_right b c)

@[to_dual]

Depends on / 依赖: h.trans_le, le_max_right, trans_le
-/
theorem lt_max_of_lt_right (h : a < c) : a < max b c :=
  h.trans_le (le_max_right b c)

@[to_dual]
/--
lemma `max_min_distrib_left` / 引理 `max_min_distrib_left`

English:
lemma max_min_distrib_left
  given: (a b c : α)
  statement: max a (min b c) = min (max a b) (max a c)
  proof: sup_inf_left _ _ _

@[to_dual]

中文:
引理 max_min_distrib_left
  条件: (a b c : α)
  结论: max a (min b c) = min (max a b) (max a c)
  证明: sup_inf_left _ _ _

@[to_dual]

Depends on / 依赖: sup_inf_left
-/
lemma max_min_distrib_left (a b c : α) : max a (min b c) = min (max a b) (max a c) :=
  sup_inf_left _ _ _

@[to_dual]
/--
lemma `max_min_distrib_right` / 引理 `max_min_distrib_right`

English:
lemma max_min_distrib_right
  given: (a b c : α)
  statement: max (min a b) c = min (max a c) (max b c)
  proof: sup_inf_right _ _ _

中文:
引理 max_min_distrib_right
  条件: (a b c : α)
  结论: max (min a b) c = min (max a c) (max b c)
  证明: sup_inf_right _ _ _

Depends on / 依赖: sup_inf_right
-/
lemma max_min_distrib_right (a b c : α) : max (min a b) c = min (max a c) (max b c) :=
  sup_inf_right _ _ _

/--
theorem `min_le_max` / 定理 `min_le_max`

English:
theorem min_le_max
  statement: min a b <= max a b
  proof: le_trans (min_le_left a b) (le_max_left a b)

@[to_dual]

中文:
定理 min_le_max
  结论: min a b <= max a b
  证明: le_trans (min_le_left a b) (le_max_left a b)

@[to_dual]

Depends on / 依赖: le_max_left, le_trans, min_le_left
-/
theorem min_le_max : min a b <= max a b :=
  le_trans (min_le_left a b) (le_max_left a b)

@[to_dual]
/--
theorem `min_eq_left_iff` / 定理 `min_eq_left_iff`

English:
theorem min_eq_left_iff
  statement: min a b = a ↔ a <= b
  proof: inf_eq_left

@[to_dual]

中文:
定理 min_eq_left_iff
  结论: min a b = a ↔ a <= b
  证明: inf_eq_left

@[to_dual]

Depends on / 依赖: inf_eq_left
-/
theorem min_eq_left_iff : min a b = a ↔ a <= b :=
  inf_eq_left

@[to_dual]
/--
theorem `min_eq_right_iff` / 定理 `min_eq_right_iff`

English:
theorem min_eq_right_iff
  statement: min a b = b ↔ b <= a
  proof: inf_eq_right

中文:
定理 min_eq_right_iff
  结论: min a b = b ↔ b <= a
  证明: inf_eq_right

Depends on / 依赖: inf_eq_right
-/
theorem min_eq_right_iff : min a b = b ↔ b <= a :=
  inf_eq_right

/-- For elements `a` and `b` of a linear order, either `min a b = a` and `a ≤ b`,
or `min a b = b` and `b < a`.
Use cases on this lemma to automate linarith in inequalities -/
@[to_dual
/-- For elements `a` and `b` of a linear order, either `max a b = a` and `b ≤ a`,
or `max a b = b` and `a < b`.
Use cases on this lemma to automate linarith in inequalities -/]
/--
theorem `min_cases` / 定理 `min_cases`

English:
theorem min_cases
  given: (a b : α)
  statement: min a b = a ∧ a <= b ∨ min a b = b ∧ b < a
  proof: by
  grind

@[to_dual]

中文:
定理 min_cases
  条件: (a b : α)
  结论: min a b = a ∧ a <= b ∨ min a b = b ∧ b < a
  证明: by
  grind

@[to_dual]
-/
theorem min_cases (a b : α) : min a b = a ∧ a <= b ∨ min a b = b ∧ b < a := by
  grind

@[to_dual]
/--
theorem `min_eq_iff` / 定理 `min_eq_iff`

English:
theorem min_eq_iff
  statement: min a b = c ↔ a = c ∧ a <= b ∨ b = c ∧ b <= a
  proof: by
  grind

@[to_dual]

中文:
定理 min_eq_iff
  结论: min a b = c ↔ a = c ∧ a <= b ∨ b = c ∧ b <= a
  证明: by
  grind

@[to_dual]
-/
theorem min_eq_iff : min a b = c ↔ a = c ∧ a <= b ∨ b = c ∧ b <= a := by
  grind

@[to_dual]
/--
theorem `min_lt_min_left_iff` / 定理 `min_lt_min_left_iff`

English:
theorem min_lt_min_left_iff
  statement: min a c < min b c ↔ a < b ∧ a < c
  proof: by
  grind

@[to_dual]

中文:
定理 min_lt_min_left_iff
  结论: min a c < min b c ↔ a < b ∧ a < c
  证明: by
  grind

@[to_dual]
-/
theorem min_lt_min_left_iff : min a c < min b c ↔ a < b ∧ a < c := by
  grind

@[to_dual]
/--
theorem `min_lt_min_right_iff` / 定理 `min_lt_min_right_iff`

English:
theorem min_lt_min_right_iff
  statement: min a b < min a c ↔ b < c ∧ b < a
  proof: by
  grind

中文:
定理 min_lt_min_right_iff
  结论: min a b < min a c ↔ b < c ∧ b < a
  证明: by
  grind
-/
theorem min_lt_min_right_iff : min a b < min a c ↔ b < c ∧ b < a := by
  grind

/-- An instance asserting that `max a a = a` -/
@[to_dual /-- An instance asserting that `min a a = a` -/]
/--
Instance `max_idem` / 实例 `max_idem`

English:
instance max_idem
  signature: : Std.IdempotentOp (α := α) max where
  body: by simp

中文:
实例 max_idem
  签名: : Std.IdempotentOp (α := α) max where
  定义体: by simp
-/
instance max_idem : Std.IdempotentOp (α := α) max where
  idempotent := by simp

/--
theorem `min_lt_max` / 定理 `min_lt_max`

English:
theorem min_lt_max
  statement: min a b < max a b ↔ a != b
  proof: inf_lt_sup

@[to_dual]

中文:
定理 min_lt_max
  结论: min a b < max a b ↔ a != b
  证明: inf_lt_sup

@[to_dual]

Depends on / 依赖: inf_lt_sup
-/
theorem min_lt_max : min a b < max a b ↔ a != b :=
  inf_lt_sup

@[to_dual]
/--
theorem `max_lt_max` / 定理 `max_lt_max`

English:
theorem max_lt_max
  given: (h₁ : a < c) (h₂ : b < d)
  statement: max a b < max c d
  proof: max_lt (lt_max_of_lt_left h₁) (lt_max_of_lt_right h₂)

@[to_dual]

中文:
定理 max_lt_max
  条件: (h₁ : a < c) (h₂ : b < d)
  结论: max a b < max c d
  证明: max_lt (lt_max_of_lt_left h₁) (lt_max_of_lt_right h₂)

@[to_dual]

Depends on / 依赖: lt_max_of_lt_left, lt_max_of_lt_right, max_lt
-/
theorem max_lt_max (h₁ : a < c) (h₂ : b < d) : max a b < max c d :=
  max_lt (lt_max_of_lt_left h₁) (lt_max_of_lt_right h₂)

@[to_dual]
/--
lemma `min_right_comm` / 引理 `min_right_comm`

English:
lemma min_right_comm
  given: (a b c : α)
  statement: min (min a b) c = min (min a c) b
  proof: by
  rw [min_assoc]; rw [min_comm b]; rw [← min_assoc]

@[deprecated (since := "2026-03-22")] alias Max.left_comm := max_left_comm
@[deprecated (since := "2026-03-22")] alias Max.right_comm := max_right_comm

@[to_dual]

中文:
引理 min_right_comm
  条件: (a b c : α)
  结论: min (min a b) c = min (min a c) b
  证明: by
  rw [min_assoc]; rw [min_comm b]; rw [← min_assoc]

@[deprecated (since := "2026-03-22")] alias Max.left_comm := max_left_comm
@[deprecated (since := "2026-03-22")] alias Max.right_comm := max_right_comm

@[to_dual]

Depends on / 依赖: min_assoc, min_comm
-/
lemma min_right_comm (a b c : α) : min (min a b) c = min (min a c) b := by
  rw [min_assoc]; rw [min_comm b]; rw [← min_assoc]

@[deprecated (since := "2026-03-22")] alias Max.left_comm := max_left_comm
@[deprecated (since := "2026-03-22")] alias Max.right_comm := max_right_comm

@[to_dual]
/--
theorem `MonotoneOn.map_max` / 定理 `MonotoneOn.map_max`

English:
theorem MonotoneOn.map_max
  given: (hf : MonotoneOn f s) (ha : a in s) (hb : b in s)
  statement: f (max a b) =
  proof: by
  rcases le_total a b with h | h <;>
    simp only [max_eq_right, max_eq_left, hf ha hb, hf hb ha, h]

@[to_dual]

中文:
定理 MonotoneOn.map_max
  条件: (hf : MonotoneOn f s) (ha : a in s) (hb : b in s)
  结论: f (max a b) =
  证明: by
  rcases le_total a b with h | h <;>
    simp only [max_eq_right, max_eq_left, hf ha hb, hf hb ha, h]

@[to_dual]

Depends on / 依赖: le_total, max_eq_left, max_eq_right
-/
theorem MonotoneOn.map_max (hf : MonotoneOn f s) (ha : a in s) (hb : b in s) : f (max a b) =
    max (f a) (f b) := by
  rcases le_total a b with h | h <;>
    simp only [max_eq_right, max_eq_left, hf ha hb, hf hb ha, h]

@[to_dual]
/--
theorem `AntitoneOn.map_max` / 定理 `AntitoneOn.map_max`

English:
theorem AntitoneOn.map_max
  given: (hf : AntitoneOn f s) (ha : a in s) (hb : b in s)
  statement: f (max a b) =
  proof: hf.dual_right.map_max ha hb

@[to_dual]

中文:
定理 AntitoneOn.map_max
  条件: (hf : AntitoneOn f s) (ha : a in s) (hb : b in s)
  结论: f (max a b) =
  证明: hf.dual_right.map_max ha hb

@[to_dual]

Depends on / 依赖: dual_right, hf.dual_right.map_max, map_max
-/
theorem AntitoneOn.map_max (hf : AntitoneOn f s) (ha : a in s) (hb : b in s) : f (max a b) =
    min (f a) (f b) := hf.dual_right.map_max ha hb

@[to_dual]
/--
theorem `Monotone.map_max` / 定理 `Monotone.map_max`

English:
theorem Monotone.map_max
  given: (hf : Monotone f)
  statement: f (max a b) = max (f a) (f b)
  proof: by
  rcases le_total a b with h | h <;> simp [h, hf h]

@[to_dual]

中文:
定理 Monotone.map_max
  条件: (hf : Monotone f)
  结论: f (max a b) = max (f a) (f b)
  证明: by
  rcases le_total a b with h | h <;> simp [h, hf h]

@[to_dual]

Depends on / 依赖: le_total
-/
theorem Monotone.map_max (hf : Monotone f) : f (max a b) = max (f a) (f b) := by
  rcases le_total a b with h | h <;> simp [h, hf h]

@[to_dual]
/--
theorem `Antitone.map_max` / 定理 `Antitone.map_max`

English:
theorem Antitone.map_max
  given: (hf : Antitone f)
  statement: f (max a b) = min (f a) (f b)
  proof: by
  rcases le_total a b with h | h <;> simp [h, hf h]

@[to_dual]

中文:
定理 Antitone.map_max
  条件: (hf : Antitone f)
  结论: f (max a b) = min (f a) (f b)
  证明: by
  rcases le_total a b with h | h <;> simp [h, hf h]

@[to_dual]

Depends on / 依赖: le_total
-/
theorem Antitone.map_max (hf : Antitone f) : f (max a b) = min (f a) (f b) := by
  rcases le_total a b with h | h <;> simp [h, hf h]

@[to_dual]
/--
theorem `min_choice` / 定理 `min_choice`

English:
theorem min_choice
  given: (a b : α)
  statement: min a b = a ∨ min a b = b
  proof: by cases le_total a b <;> simp [*]

@[to_dual le_of_le_min_left]

中文:
定理 min_choice
  条件: (a b : α)
  结论: min a b = a ∨ min a b = b
  证明: by cases le_total a b <;> simp [*]

@[to_dual le_of_le_min_left]

Depends on / 依赖: le_total
-/
theorem min_choice (a b : α) : min a b = a ∨ min a b = b := by cases le_total a b <;> simp [*]

@[to_dual le_of_le_min_left]
/--
theorem `le_of_max_le_left` / 定理 `le_of_max_le_left`

English:
theorem le_of_max_le_left
  given: {a b c : α} (h : max a b <= c)
  statement: a <= c
  proof: le_trans (le_max_left _ _) h

@[to_dual le_of_le_min_right]

中文:
定理 le_of_max_le_left
  条件: {a b c : α} (h : max a b <= c)
  结论: a <= c
  证明: le_trans (le_max_left _ _) h

@[to_dual le_of_le_min_right]

Depends on / 依赖: le_max_left, le_trans
-/
theorem le_of_max_le_left {a b c : α} (h : max a b <= c) : a <= c :=
  le_trans (le_max_left _ _) h

@[to_dual le_of_le_min_right]
/--
theorem `le_of_max_le_right` / 定理 `le_of_max_le_right`

English:
theorem le_of_max_le_right
  given: {a b c : α} (h : max a b <= c)
  statement: b <= c
  proof: le_trans (le_max_right _ _) h

中文:
定理 le_of_max_le_right
  条件: {a b c : α} (h : max a b <= c)
  结论: b <= c
  证明: le_trans (le_max_right _ _) h

Depends on / 依赖: le_max_right, le_trans
-/
theorem le_of_max_le_right {a b c : α} (h : max a b <= c) : b <= c :=
  le_trans (le_max_right _ _) h

/--
Instance `instCommutativeMax` / 实例 `instCommutativeMax`

English:
instance instCommutativeMax
  signature: : Std.Commutative (α := α) max where comm
  body: max_comm

中文:
实例 instCommutativeMax
  签名: : Std.Commutative (α := α) max where comm
  定义体: max_comm
-/
@[to_dual] instance instCommutativeMax : Std.Commutative (α := α) max where comm := max_comm
/--
Instance `instAssociativeMax` / 实例 `instAssociativeMax`

English:
instance instAssociativeMax
  signature: : Std.Associative (α := α) max where assoc
  body: max_assoc

@[to_dual]

中文:
实例 instAssociativeMax
  签名: : Std.Associative (α := α) max where assoc
  定义体: max_assoc

@[to_dual]
-/
@[to_dual] instance instAssociativeMax : Std.Associative (α := α) max where assoc := max_assoc

@[to_dual]
/--
theorem `max_left_commutative` / 定理 `max_left_commutative`

English:
theorem max_left_commutative
  statement: LeftCommutative (max : α -> α -> α)
  proof: ⟨max_left_comm⟩

中文:
定理 max_left_commutative
  结论: LeftCommutative (max : α -> α -> α)
  证明: ⟨max_left_comm⟩

Depends on / 依赖: max_left_comm
-/
theorem max_left_commutative : LeftCommutative (max : α -> α -> α) := ⟨max_left_comm⟩

end
