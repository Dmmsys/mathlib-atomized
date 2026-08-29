/-
Copyright (c) 2017 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
module

public import Mathlib.Data.Multiset.Dedup
public import Mathlib.Data.List.Infix

/-!
# Preparations for defining operations on `Finset`.

The operations here ignore multiplicities,
and prepare for defining the corresponding operations on `Finset`.
-/

@[expose] public section


-- Assert that we define `Finset` without the material on the set lattice.
-- Note that we cannot put this in `Data.Finset.Basic` because we proved relevant lemmas there.
assert_not_exists Set.sInter

namespace Multiset

open List

variable {α : Type*} [DecidableEq α] {s : Multiset α}

/-! ### finset insert -/


/--
Definition of `ndinsert` / `ndinsert` 的定义

English:
definition ndinsert
  signature: (a : α) (s : Multiset α)
  body: Quot.liftOn s (fun l => (l.insert a : Multiset α)) fun _ _ p => Quot.sound (p.insert a)

@[simp]

中文:
定义 ndinsert
  签名: (a : α) (s : Multiset α)
  定义体: Quot.liftOn s (fun l => (l.insert a : Multiset α)) fun _ _ p => Quot.sound (p.insert a)

@[simp]

Depends on / 依赖: Multiset, Quot.liftOn, Quot.sound, insert, l.insert, liftOn, p.insert
-/
def ndinsert (a : α) (s : Multiset α) : Multiset α :=
  Quot.liftOn s (fun l => (l.insert a : Multiset α)) fun _ _ p => Quot.sound (p.insert a)

@[simp]
/--
theorem `coe_ndinsert` / 定理 `coe_ndinsert`

English:
theorem coe_ndinsert
  given: (a : α) (l : List α)
  statement: ndinsert a l = (insert a l : List α)
  proof: rfl

@[simp]

中文:
定理 coe_ndinsert
  条件: (a : α) (l : List α)
  结论: ndinsert a l = (insert a l : List α)
  证明: rfl

@[simp]
-/
theorem coe_ndinsert (a : α) (l : List α) : ndinsert a l = (insert a l : List α) :=
  rfl

@[simp]
/--
theorem `ndinsert_zero` / 定理 `ndinsert_zero`

English:
theorem ndinsert_zero
  given: (a : α)
  statement: ndinsert a 0 = {a}
  proof: rfl

@[simp]

中文:
定理 ndinsert_zero
  条件: (a : α)
  结论: ndinsert a 0 = {a}
  证明: rfl

@[simp]
-/
theorem ndinsert_zero (a : α) : ndinsert a 0 = {a} :=
  rfl

@[simp]
/--
theorem `ndinsert_of_mem` / 定理 `ndinsert_of_mem`

English:
theorem ndinsert_of_mem
  given: {a : α} {s : Multiset α}
  statement: a in s -> ndinsert a s = s
  proof: Quot.inductionOn s fun _ h => congr_arg ((↑) : List α -> Multiset α) insert_of_mem h

@[simp]

中文:
定理 ndinsert_of_mem
  条件: {a : α} {s : Multiset α}
  结论: a in s -> ndinsert a s = s
  证明: Quot.inductionOn s fun _ h => congr_arg ((↑) : List α -> Multiset α) insert_of_mem h

@[simp]

Depends on / 依赖: Multiset, Quot.inductionOn, congr_arg, inductionOn, insert_of_mem
-/
theorem ndinsert_of_mem {a : α} {s : Multiset α} : a in s -> ndinsert a s = s :=
Quot.inductionOn s fun _ h => congr_arg ((↑) : List α -> Multiset α) insert_of_mem h

@[simp]
/--
theorem `ndinsert_of_notMem` / 定理 `ndinsert_of_notMem`

English:
theorem ndinsert_of_notMem
  given: {a : α} {s : Multiset α}
  statement: a ∉ s -> ndinsert a s = a ::ₘ s
  proof: Quot.inductionOn s fun _ h => congr_arg ((↑) : List α -> Multiset α) insert_of_not_mem h

@[simp]

中文:
定理 ndinsert_of_notMem
  条件: {a : α} {s : Multiset α}
  结论: a ∉ s -> ndinsert a s = a ::ₘ s
  证明: Quot.inductionOn s fun _ h => congr_arg ((↑) : List α -> Multiset α) insert_of_not_mem h

@[simp]

Depends on / 依赖: Multiset, Quot.inductionOn, congr_arg, inductionOn, insert_of_not_mem
-/
theorem ndinsert_of_notMem {a : α} {s : Multiset α} : a ∉ s -> ndinsert a s = a ::ₘ s :=
Quot.inductionOn s fun _ h => congr_arg ((↑) : List α -> Multiset α) insert_of_not_mem h

@[simp]
/--
theorem `mem_ndinsert` / 定理 `mem_ndinsert`

English:
theorem mem_ndinsert
  given: {a b : α} {s : Multiset α}
  statement: a in ndinsert b s ↔ a = b ∨ a in s
  proof: Quot.inductionOn s fun _ => mem_insert_iff

@[simp]

中文:
定理 mem_ndinsert
  条件: {a b : α} {s : Multiset α}
  结论: a in ndinsert b s ↔ a = b ∨ a in s
  证明: Quot.inductionOn s fun _ => mem_insert_iff

@[simp]

Depends on / 依赖: Quot.inductionOn, inductionOn, mem_insert_iff
-/
theorem mem_ndinsert {a b : α} {s : Multiset α} : a in ndinsert b s ↔ a = b ∨ a in s :=
  Quot.inductionOn s fun _ => mem_insert_iff

@[simp]
/--
theorem `le_ndinsert_self` / 定理 `le_ndinsert_self`

English:
theorem le_ndinsert_self
  given: (a : α) (s : Multiset α)
  statement: s <= ndinsert a s
  proof: Quot.inductionOn s fun _ => (sublist_insert _ _).subperm

中文:
定理 le_ndinsert_self
  条件: (a : α) (s : Multiset α)
  结论: s <= ndinsert a s
  证明: Quot.inductionOn s fun _ => (sublist_insert _ _).subperm

Depends on / 依赖: Quot.inductionOn, inductionOn, sublist_insert, subperm
-/
theorem le_ndinsert_self (a : α) (s : Multiset α) : s <= ndinsert a s :=
  Quot.inductionOn s fun _ => (sublist_insert _ _).subperm

/--
theorem `mem_ndinsert_self` / 定理 `mem_ndinsert_self`

English:
theorem mem_ndinsert_self
  given: (a : α) (s : Multiset α)
  statement: a in ndinsert a s
  proof: by simp

中文:
定理 mem_ndinsert_self
  条件: (a : α) (s : Multiset α)
  结论: a in ndinsert a s
  证明: by simp
-/
theorem mem_ndinsert_self (a : α) (s : Multiset α) : a in ndinsert a s := by simp

/--
theorem `mem_ndinsert_of_mem` / 定理 `mem_ndinsert_of_mem`

English:
theorem mem_ndinsert_of_mem
  given: {a b : α} {s : Multiset α} (h : a in s)
  statement: a in ndinsert b s
  proof: mem_ndinsert.2 (Or.inr h)

中文:
定理 mem_ndinsert_of_mem
  条件: {a b : α} {s : Multiset α} (h : a in s)
  结论: a in ndinsert b s
  证明: mem_ndinsert.2 (Or.inr h)

Depends on / 依赖: Or.inr, mem_ndinsert
-/
theorem mem_ndinsert_of_mem {a b : α} {s : Multiset α} (h : a in s) : a in ndinsert b s :=
  mem_ndinsert.2 (Or.inr h)

/--
theorem `length_ndinsert_of_mem` / 定理 `length_ndinsert_of_mem`

English:
theorem length_ndinsert_of_mem
  given: {a : α} {s : Multiset α} (h : a in s)
  proof: by simp [h]

中文:
定理 length_ndinsert_of_mem
  条件: {a : α} {s : Multiset α} (h : a in s)
  证明: by simp [h]
-/
theorem length_ndinsert_of_mem {a : α} {s : Multiset α} (h : a in s) :
    card (ndinsert a s) = card s := by simp [h]

/--
theorem `length_ndinsert_of_notMem` / 定理 `length_ndinsert_of_notMem`

English:
theorem length_ndinsert_of_notMem
  given: {a : α} {s : Multiset α} (h : a ∉ s)
  proof: by simp [h]

中文:
定理 length_ndinsert_of_notMem
  条件: {a : α} {s : Multiset α} (h : a ∉ s)
  证明: by simp [h]
-/
theorem length_ndinsert_of_notMem {a : α} {s : Multiset α} (h : a ∉ s) :
    card (ndinsert a s) = card s + 1 := by simp [h]

/--
theorem `dedup_cons` / 定理 `dedup_cons`

English:
theorem dedup_cons
  given: {a : α} {s : Multiset α}
  statement: dedup (a ::ₘ s) = ndinsert a (dedup s)
  proof: by
  by_cases h : a in s <;> simp [h]

中文:
定理 dedup_cons
  条件: {a : α} {s : Multiset α}
  结论: dedup (a ::ₘ s) = ndinsert a (dedup s)
  证明: by
  by_cases h : a in s <;> simp [h]
-/
theorem dedup_cons {a : α} {s : Multiset α} : dedup (a ::ₘ s) = ndinsert a (dedup s) := by
  by_cases h : a in s <;> simp [h]

/--
theorem `Nodup.ndinsert` / 定理 `Nodup.ndinsert`

English:
theorem Nodup.ndinsert
  given: (a : α)
  statement: Nodup s -> Nodup (ndinsert a s)
  proof: Quot.inductionOn s fun _ => Nodup.insert

中文:
定理 Nodup.ndinsert
  条件: (a : α)
  结论: Nodup s -> Nodup (ndinsert a s)
  证明: Quot.inductionOn s fun _ => Nodup.insert

Depends on / 依赖: Nodup.insert, Quot.inductionOn, inductionOn, insert
-/
theorem Nodup.ndinsert (a : α) : Nodup s -> Nodup (ndinsert a s) :=
  Quot.inductionOn s fun _ => Nodup.insert

/--
theorem `ndinsert_le` / 定理 `ndinsert_le`

English:
theorem ndinsert_le
  given: {a : α} {s t : Multiset α}
  statement: ndinsert a s <= t ↔ s <= t ∧ a in t
  proof: ⟨fun h => ⟨le_trans (le_ndinsert_self _ _) h, mem_of_le h (mem_ndinsert_self _ _)⟩, fun ⟨l, m⟩ =>
    if h : a in s then by simp [h, l]
    else by
      rw [ndinsert_of_notMem h]; rw [← cons_erase m]; rw [cons_le_cons_iff]; rw [← le_cons_of_notMem h]; rw [cons_erase m]
      exact l⟩

中文:
定理 ndinsert_le
  条件: {a : α} {s t : Multiset α}
  结论: ndinsert a s <= t ↔ s <= t ∧ a in t
  证明: ⟨fun h => ⟨le_trans (le_ndinsert_self _ _) h, mem_of_le h (mem_ndinsert_self _ _)⟩, fun ⟨l, m⟩ =>
    if h : a in s then by simp [h, l]
    else by
      rw [ndinsert_of_notMem h]; rw [← cons_erase m]; rw [cons_le_cons_iff]; rw [← le_cons_of_notMem h]; rw [cons_erase m]
      exact l⟩

Depends on / 依赖: cons_erase, cons_le_cons_iff, le_cons_of_notMem, le_ndinsert_self, le_trans, mem_ndinsert_self, mem_of_le, ndinsert_of_notMem
-/
theorem ndinsert_le {a : α} {s t : Multiset α} : ndinsert a s <= t ↔ s <= t ∧ a in t :=
  ⟨fun h => ⟨le_trans (le_ndinsert_self _ _) h, mem_of_le h (mem_ndinsert_self _ _)⟩, fun ⟨l, m⟩ =>
    if h : a in s then by simp [h, l]
    else by
      rw [ndinsert_of_notMem h]; rw [← cons_erase m]; rw [cons_le_cons_iff]; rw [← le_cons_of_notMem h]; rw [cons_erase m]
      exact l⟩

/--
theorem `attach_ndinsert` / 定理 `attach_ndinsert`

English:
theorem attach_ndinsert
  given: (a : α) (s : Multiset α)
  proof: have eq :
    forall h : forall p : { x // x in s }, p.1 in s,
      (fun p : { x // x in s } => ⟨p.val, h p⟩ : { x // x in s } -> { x // x in s }) = id :=
    fun _ => funext fun _ => Subtype.ext rfl
  have : forall (t) (eq : s.ndinsert a = t), t.attach = ndinsert ⟨a, eq ▸ mem_ndinsert_self a s⟩
  

中文:
定理 attach_ndinsert
  条件: (a : α) (s : Multiset α)
  证明: have eq :
    forall h : forall p : { x // x in s }, p.1 in s,
      (fun p : { x // x in s } => ⟨p.val, h p⟩ : { x // x in s } -> { x // x in s }) = id :=
    fun _ => funext fun _ => Subtype.ext rfl
  have : forall (t) (eq : s.ndinsert a = t), t.attach = ndinsert ⟨a, eq ▸ mem_ndinsert_self a s⟩
  

Depends on / 依赖: Subtype, Subtype.ext, attach, map_id, mem_attach, mem_ndinsert_of_mem, mem_ndinsert_self, ndinsert, ndinsert_of_mem, ndinsert_of_not, p.val, s.attach.map, s.ndinsert, t.attach
-/
theorem attach_ndinsert (a : α) (s : Multiset α) :
    (s.ndinsert a).attach =
      ndinsert ⟨a, mem_ndinsert_self a s⟩ (s.attach.map fun p => ⟨p.1, mem_ndinsert_of_mem p.2⟩) :=
  have eq :
    forall h : forall p : { x // x in s }, p.1 in s,
      (fun p : { x // x in s } => ⟨p.val, h p⟩ : { x // x in s } -> { x // x in s }) = id :=
    fun _ => funext fun _ => Subtype.ext rfl
  have : forall (t) (eq : s.ndinsert a = t), t.attach = ndinsert ⟨a, eq ▸ mem_ndinsert_self a s⟩
      (s.attach.map fun p => ⟨p.1, eq ▸ mem_ndinsert_of_mem p.2⟩) := by
    intro t ht
    by_cases h : a in s
    · rw [ndinsert_of_mem h] at ht
      subst ht
      rw [eq]; rw [map_id]; rw [ndinsert_of_mem (mem_attach _ _)]
    · rw [ndinsert_of_notMem h] at ht
      subst ht
      simp [attach_cons, h]
  this _ rfl

@[simp]
/--
theorem `disjoint_ndinsert_left` / 定理 `disjoint_ndinsert_left`

English:
theorem disjoint_ndinsert_left
  given: {a : α} {s t : Multiset α}
  proof: Iff.trans (by simp [disjoint_left]) disjoint_cons_left

@[simp]

中文:
定理 disjoint_ndinsert_left
  条件: {a : α} {s t : Multiset α}
  证明: Iff.trans (by simp [disjoint_left]) disjoint_cons_left

@[simp]

Depends on / 依赖: Iff.trans, disjoint_cons_left, disjoint_left
-/
theorem disjoint_ndinsert_left {a : α} {s t : Multiset α} :
    Disjoint (ndinsert a s) t ↔ a ∉ t ∧ Disjoint s t :=
  Iff.trans (by simp [disjoint_left]) disjoint_cons_left

@[simp]
/--
theorem `disjoint_ndinsert_right` / 定理 `disjoint_ndinsert_right`

English:
theorem disjoint_ndinsert_right
  given: {a : α} {s t : Multiset α}
  proof: by
  rw [_root_.disjoint_comm]; rw [disjoint_ndinsert_left]; tauto

中文:
定理 disjoint_ndinsert_right
  条件: {a : α} {s t : Multiset α}
  证明: by
  rw [_root_.disjoint_comm]; rw [disjoint_ndinsert_left]; tauto

Depends on / 依赖: _root_, _root_.disjoint_comm, disjoint_comm, disjoint_ndinsert_left
-/
theorem disjoint_ndinsert_right {a : α} {s t : Multiset α} :
    Disjoint s (ndinsert a t) ↔ a ∉ s ∧ Disjoint s t := by
  rw [_root_.disjoint_comm]; rw [disjoint_ndinsert_left]; tauto

/-! ### finset union -/


/--
Definition of `ndunion` / `ndunion` 的定义

English:
definition ndunion
  signature: (s t : Multiset α)
  body: (Quotient.liftOn₂ s t fun l₁ l₂ => (l₁.union l₂ : Multiset α)) fun _ _ _ _ p₁ p₂ =>
Quot.sound p₁.union p₂

@[simp]

中文:
定义 ndunion
  签名: (s t : Multiset α)
  定义体: (Quotient.liftOn₂ s t fun l₁ l₂ => (l₁.union l₂ : Multiset α)) fun _ _ _ _ p₁ p₂ =>
Quot.sound p₁.union p₂

@[simp]

Depends on / 依赖: Multiset, Quot.sound, Quotient, Quotient.liftOn
-/
def ndunion (s t : Multiset α) : Multiset α :=
  (Quotient.liftOn₂ s t fun l₁ l₂ => (l₁.union l₂ : Multiset α)) fun _ _ _ _ p₁ p₂ =>
Quot.sound p₁.union p₂

@[simp]
/--
theorem `coe_ndunion` / 定理 `coe_ndunion`

English:
theorem coe_ndunion
  given: (l₁ l₂ : List α)
  statement: @ndunion α _ l₁ l₂ = (l₁ union l₂ : List α)
  proof: rfl

中文:
定理 coe_ndunion
  条件: (l₁ l₂ : List α)
  结论: @ndunion α _ l₁ l₂ = (l₁ union l₂ : List α)
  证明: rfl
-/
theorem coe_ndunion (l₁ l₂ : List α) : @ndunion α _ l₁ l₂ = (l₁ union l₂ : List α) :=
  rfl

-- `simp` can prove this once we have `ndunion_eq_union`.
/--
theorem `zero_ndunion` / 定理 `zero_ndunion`

English:
theorem zero_ndunion
  given: (s : Multiset α)
  statement: ndunion 0 s = s
  proof: Quot.inductionOn s fun _ => rfl

@[simp]

中文:
定理 zero_ndunion
  条件: (s : Multiset α)
  结论: ndunion 0 s = s
  证明: Quot.inductionOn s fun _ => rfl

@[simp]

Depends on / 依赖: Quot.inductionOn, inductionOn
-/
theorem zero_ndunion (s : Multiset α) : ndunion 0 s = s :=
  Quot.inductionOn s fun _ => rfl

@[simp]
/--
theorem `cons_ndunion` / 定理 `cons_ndunion`

English:
theorem cons_ndunion
  given: (s t : Multiset α) (a : α)
  statement: ndunion (a ::ₘ s) t = ndinsert a (ndunion s t)
  proof: Quot.induction_on₂ s t fun _ _ => rfl

@[simp]

中文:
定理 cons_ndunion
  条件: (s t : Multiset α) (a : α)
  结论: ndunion (a ::ₘ s) t = ndinsert a (ndunion s t)
  证明: Quot.induction_on₂ s t fun _ _ => rfl

@[simp]

Depends on / 依赖: Quot.induction_on
-/
theorem cons_ndunion (s t : Multiset α) (a : α) : ndunion (a ::ₘ s) t = ndinsert a (ndunion s t) :=
  Quot.induction_on₂ s t fun _ _ => rfl

@[simp]
/--
theorem `mem_ndunion` / 定理 `mem_ndunion`

English:
theorem mem_ndunion
  given: {s t : Multiset α} {a : α}
  statement: a in ndunion s t ↔ a in s ∨ a in t
  proof: Quot.induction_on₂ s t fun _ _ => List.mem_union_iff

中文:
定理 mem_ndunion
  条件: {s t : Multiset α} {a : α}
  结论: a in ndunion s t ↔ a in s ∨ a in t
  证明: Quot.induction_on₂ s t fun _ _ => List.mem_union_iff

Depends on / 依赖: List.mem_union_iff, Quot.induction_on, mem_union_iff
-/
theorem mem_ndunion {s t : Multiset α} {a : α} : a in ndunion s t ↔ a in s ∨ a in t :=
  Quot.induction_on₂ s t fun _ _ => List.mem_union_iff

/--
theorem `le_ndunion_right` / 定理 `le_ndunion_right`

English:
theorem le_ndunion_right
  given: (s t : Multiset α)
  statement: t <= ndunion s t
  proof: Quot.induction_on₂ s t fun _ _ => (suffix_union_right _ _).sublist.subperm

中文:
定理 le_ndunion_right
  条件: (s t : Multiset α)
  结论: t <= ndunion s t
  证明: Quot.induction_on₂ s t fun _ _ => (suffix_union_right _ _).sublist.subperm

Depends on / 依赖: Quot.induction_on, sublist, sublist.subperm, subperm, suffix_union_right
-/
theorem le_ndunion_right (s t : Multiset α) : t <= ndunion s t :=
  Quot.induction_on₂ s t fun _ _ => (suffix_union_right _ _).sublist.subperm

/--
theorem `subset_ndunion_right` / 定理 `subset_ndunion_right`

English:
theorem subset_ndunion_right
  given: (s t : Multiset α)
  statement: t subseteq ndunion s t
  proof: subset_of_le (le_ndunion_right s t)

中文:
定理 subset_ndunion_right
  条件: (s t : Multiset α)
  结论: t subseteq ndunion s t
  证明: subset_of_le (le_ndunion_right s t)

Depends on / 依赖: le_ndunion_right, subset_of_le
-/
theorem subset_ndunion_right (s t : Multiset α) : t subseteq ndunion s t :=
  subset_of_le (le_ndunion_right s t)

/--
theorem `ndunion_le_add` / 定理 `ndunion_le_add`

English:
theorem ndunion_le_add
  given: (s t : Multiset α)
  statement: ndunion s t <= s + t
  proof: Quot.induction_on₂ s t fun _ _ => (union_sublist_append _ _).subperm

中文:
定理 ndunion_le_add
  条件: (s t : Multiset α)
  结论: ndunion s t <= s + t
  证明: Quot.induction_on₂ s t fun _ _ => (union_sublist_append _ _).subperm

Depends on / 依赖: Quot.induction_on, subperm, union_sublist_append
-/
theorem ndunion_le_add (s t : Multiset α) : ndunion s t <= s + t :=
  Quot.induction_on₂ s t fun _ _ => (union_sublist_append _ _).subperm

/--
theorem `ndunion_le` / 定理 `ndunion_le`

English:
theorem ndunion_le
  given: {s t u : Multiset α}
  statement: ndunion s t <= u ↔ s subseteq u ∧ t <= u
  proof: Multiset.induction_on s (by simp [zero_ndunion])
    (fun _ _ h =>
      by simp only [cons_ndunion, ndinsert_le, and_comm, cons_subset, and_left_comm, h,
        and_assoc])

中文:
定理 ndunion_le
  条件: {s t u : Multiset α}
  结论: ndunion s t <= u ↔ s subseteq u ∧ t <= u
  证明: Multiset.induction_on s (by simp [zero_ndunion])
    (fun _ _ h =>
      by simp only [cons_ndunion, ndinsert_le, and_comm, cons_subset, and_left_comm, h,
        and_assoc])

Depends on / 依赖: Multiset, Multiset.induction_on, and_assoc, and_comm, and_left_comm, cons_ndunion, cons_subset, induction_on, ndinsert_le, zero_ndunion
-/
theorem ndunion_le {s t u : Multiset α} : ndunion s t <= u ↔ s subseteq u ∧ t <= u :=
  Multiset.induction_on s (by simp [zero_ndunion])
    (fun _ _ h =>
      by simp only [cons_ndunion, ndinsert_le, and_comm, cons_subset, and_left_comm, h,
        and_assoc])

/--
theorem `subset_ndunion_left` / 定理 `subset_ndunion_left`

English:
theorem subset_ndunion_left
  given: (s t : Multiset α)
  statement: s subseteq ndunion s t
  proof: fun _ h =>
mem_ndunion.2 Or.inl h

中文:
定理 subset_ndunion_left
  条件: (s t : Multiset α)
  结论: s subseteq ndunion s t
  证明: fun _ h =>
mem_ndunion.2 Or.inl h
-/
theorem subset_ndunion_left (s t : Multiset α) : s subseteq ndunion s t := fun _ h =>
mem_ndunion.2 Or.inl h

/--
theorem `le_ndunion_left` / 定理 `le_ndunion_left`

English:
theorem le_ndunion_left
  given: {s} (t : Multiset α) (d : Nodup s)
  statement: s <= ndunion s t
  proof: (le_iff_subset d).2 subset_ndunion_left _ _

中文:
定理 le_ndunion_left
  条件: {s} (t : Multiset α) (d : Nodup s)
  结论: s <= ndunion s t
  证明: (le_iff_subset d).2 subset_ndunion_left _ _

Depends on / 依赖: le_iff_subset, subset_ndunion_left
-/
theorem le_ndunion_left {s} (t : Multiset α) (d : Nodup s) : s <= ndunion s t :=
(le_iff_subset d).2 subset_ndunion_left _ _

/--
theorem `ndunion_le_union` / 定理 `ndunion_le_union`

English:
theorem ndunion_le_union
  given: (s t : Multiset α)
  statement: ndunion s t <= s union t
  proof: ndunion_le.2 ⟨subset_of_le le_union_left, le_union_right⟩

中文:
定理 ndunion_le_union
  条件: (s t : Multiset α)
  结论: ndunion s t <= s union t
  证明: ndunion_le.2 ⟨subset_of_le le_union_left, le_union_right⟩

Depends on / 依赖: le_union_left, le_union_right, ndunion_le, subset_of_le
-/
theorem ndunion_le_union (s t : Multiset α) : ndunion s t <= s union t :=
  ndunion_le.2 ⟨subset_of_le le_union_left, le_union_right⟩

/--
theorem `Nodup.ndunion` / 定理 `Nodup.ndunion`

English:
theorem Nodup.ndunion
  given: (s : Multiset α) {t : Multiset α}
  statement: Nodup t -> Nodup (ndunion s t)
  proof: Quot.induction_on₂ s t fun _ _ => List.Nodup.union _

@[simp]

中文:
定理 Nodup.ndunion
  条件: (s : Multiset α) {t : Multiset α}
  结论: Nodup t -> Nodup (ndunion s t)
  证明: Quot.induction_on₂ s t fun _ _ => List.Nodup.union _

@[simp]

Depends on / 依赖: List.Nodup.union, Quot.induction_on
-/
theorem Nodup.ndunion (s : Multiset α) {t : Multiset α} : Nodup t -> Nodup (ndunion s t) :=
  Quot.induction_on₂ s t fun _ _ => List.Nodup.union _

@[simp]
/--
theorem `ndunion_eq_union` / 定理 `ndunion_eq_union`

English:
theorem ndunion_eq_union
  given: {s t : Multiset α} (d : Nodup s)
  statement: ndunion s t = s union t
  proof: le_antisymm (ndunion_le_union _ _) union_le (le_ndunion_left _ d) (le_ndunion_right _ _)

中文:
定理 ndunion_eq_union
  条件: {s t : Multiset α} (d : Nodup s)
  结论: ndunion s t = s union t
  证明: le_antisymm (ndunion_le_union _ _) union_le (le_ndunion_left _ d) (le_ndunion_right _ _)

Depends on / 依赖: le_antisymm, le_ndunion_left, le_ndunion_right, ndunion_le_union, union_le
-/
theorem ndunion_eq_union {s t : Multiset α} (d : Nodup s) : ndunion s t = s union t :=
le_antisymm (ndunion_le_union _ _) union_le (le_ndunion_left _ d) (le_ndunion_right _ _)

/--
theorem `dedup_add` / 定理 `dedup_add`

English:
theorem dedup_add
  given: (s t : Multiset α)
  statement: dedup (s + t) = ndunion s (dedup t)
  proof: Quot.induction_on₂ s t fun _ _ => congr_arg ((↑) : List α -> Multiset α) dedup_append _ _

中文:
定理 dedup_add
  条件: (s t : Multiset α)
  结论: dedup (s + t) = ndunion s (dedup t)
  证明: Quot.induction_on₂ s t fun _ _ => congr_arg ((↑) : List α -> Multiset α) dedup_append _ _

Depends on / 依赖: Multiset, Quot.induction_on, congr_arg, dedup_append
-/
theorem dedup_add (s t : Multiset α) : dedup (s + t) = ndunion s (dedup t) :=
Quot.induction_on₂ s t fun _ _ => congr_arg ((↑) : List α -> Multiset α) dedup_append _ _

/--
theorem `Disjoint.ndunion_eq` / 定理 `Disjoint.ndunion_eq`

English:
theorem Disjoint.ndunion_eq
  given: {s t : Multiset α} (h : Disjoint s t)
  proof: by
  induction s, t using Quot.induction_on₂
exact congr_arg ((↑) : List α -> Multiset α) List.Disjoint.union_eq by simpa using h

中文:
定理 Disjoint.ndunion_eq
  条件: {s t : Multiset α} (h : Disjoint s t)
  证明: by
  induction s, t using Quot.induction_on₂
exact congr_arg ((↑) : List α -> Multiset α) List.Disjoint.union_eq by simpa using h

Depends on / 依赖: Disjoint, List.Disjoint.union_eq, Multiset, Quot.induction_on, congr_arg, union_eq
-/
theorem Disjoint.ndunion_eq {s t : Multiset α} (h : Disjoint s t) :
    s.ndunion t = s.dedup + t := by
  induction s, t using Quot.induction_on₂
exact congr_arg ((↑) : List α -> Multiset α) List.Disjoint.union_eq by simpa using h

/--
theorem `Subset.ndunion_eq_right` / 定理 `Subset.ndunion_eq_right`

English:
theorem Subset.ndunion_eq_right
  given: {s t : Multiset α} (h : s subseteq t)
  statement: s.ndunion t = t
  proof: by
  induction s, t using Quot.induction_on₂
exact congr_arg ((↑) : List α -> Multiset α) List.Subset.union_eq_right h

中文:
定理 Subset.ndunion_eq_right
  条件: {s t : Multiset α} (h : s subseteq t)
  结论: s.ndunion t = t
  证明: by
  induction s, t using Quot.induction_on₂
exact congr_arg ((↑) : List α -> Multiset α) List.Subset.union_eq_right h

Depends on / 依赖: List.Subset.union_eq_right, Multiset, Quot.induction_on, Subset, congr_arg, union_eq_right
-/
theorem Subset.ndunion_eq_right {s t : Multiset α} (h : s subseteq t) : s.ndunion t = t := by
  induction s, t using Quot.induction_on₂
exact congr_arg ((↑) : List α -> Multiset α) List.Subset.union_eq_right h

/-! ### finset inter -/


/--
Definition of `ndinter` / `ndinter` 的定义

English:
definition ndinter
  signature: (s t : Multiset α)
  body: filter (· in t) s

@[simp]

中文:
定义 ndinter
  签名: (s t : Multiset α)
  定义体: filter (· in t) s

@[simp]

Depends on / 依赖: filter
-/
def ndinter (s t : Multiset α) : Multiset α :=
  filter (· in t) s

@[simp]
/--
theorem `coe_ndinter` / 定理 `coe_ndinter`

English:
theorem coe_ndinter
  given: (l₁ l₂ : List α)
  statement: @ndinter α _ l₁ l₂ = (l₁ inter l₂ : List α)
  proof: by
  simp only [ndinter, mem_coe, filter_coe, coe_eq_coe, ← elem_eq_mem]
  apply Perm.refl

@[simp]

中文:
定理 coe_ndinter
  条件: (l₁ l₂ : List α)
  结论: @ndinter α _ l₁ l₂ = (l₁ inter l₂ : List α)
  证明: by
  simp only [ndinter, mem_coe, filter_coe, coe_eq_coe, ← elem_eq_mem]
  apply Perm.refl

@[simp]

Depends on / 依赖: Perm.refl, coe_eq_coe, elem_eq_mem, filter_coe, mem_coe, ndinter
-/
theorem coe_ndinter (l₁ l₂ : List α) : @ndinter α _ l₁ l₂ = (l₁ inter l₂ : List α) := by
  simp only [ndinter, mem_coe, filter_coe, coe_eq_coe, ← elem_eq_mem]
  apply Perm.refl

@[simp]
/--
theorem `zero_ndinter` / 定理 `zero_ndinter`

English:
theorem zero_ndinter
  given: (s : Multiset α)
  statement: ndinter 0 s = 0
  proof: rfl

@[simp]

中文:
定理 zero_ndinter
  条件: (s : Multiset α)
  结论: ndinter 0 s = 0
  证明: rfl

@[simp]
-/
theorem zero_ndinter (s : Multiset α) : ndinter 0 s = 0 :=
  rfl

@[simp]
/--
theorem `cons_ndinter_of_mem` / 定理 `cons_ndinter_of_mem`

English:
theorem cons_ndinter_of_mem
  given: {a : α} (s : Multiset α) {t : Multiset α} (h : a in t)
  proof: by simp [ndinter, h]

@[simp]

中文:
定理 cons_ndinter_of_mem
  条件: {a : α} (s : Multiset α) {t : Multiset α} (h : a in t)
  证明: by simp [ndinter, h]

@[simp]

Depends on / 依赖: ndinter
-/
theorem cons_ndinter_of_mem {a : α} (s : Multiset α) {t : Multiset α} (h : a in t) :
    ndinter (a ::ₘ s) t = a ::ₘ ndinter s t := by simp [ndinter, h]

@[simp]
/--
theorem `ndinter_cons_of_notMem` / 定理 `ndinter_cons_of_notMem`

English:
theorem ndinter_cons_of_notMem
  given: {a : α} (s : Multiset α) {t : Multiset α} (h : a ∉ t)
  proof: by simp [ndinter, h]

@[simp]

中文:
定理 ndinter_cons_of_notMem
  条件: {a : α} (s : Multiset α) {t : Multiset α} (h : a ∉ t)
  证明: by simp [ndinter, h]

@[simp]

Depends on / 依赖: ndinter
-/
theorem ndinter_cons_of_notMem {a : α} (s : Multiset α) {t : Multiset α} (h : a ∉ t) :
    ndinter (a ::ₘ s) t = ndinter s t := by simp [ndinter, h]

@[simp]
/--
theorem `mem_ndinter` / 定理 `mem_ndinter`

English:
theorem mem_ndinter
  given: {s t : Multiset α} {a : α}
  statement: a in ndinter s t ↔ a in s ∧ a in t
  proof: by
  simp [ndinter, mem_filter]

中文:
定理 mem_ndinter
  条件: {s t : Multiset α} {a : α}
  结论: a in ndinter s t ↔ a in s ∧ a in t
  证明: by
  simp [ndinter, mem_filter]

Depends on / 依赖: mem_filter, ndinter
-/
theorem mem_ndinter {s t : Multiset α} {a : α} : a in ndinter s t ↔ a in s ∧ a in t := by
  simp [ndinter, mem_filter]

-- simp can prove this once we have `ndinter_eq_inter` and `Nodup.inter` a few lines down.
/--
theorem `Nodup.ndinter` / 定理 `Nodup.ndinter`

English:
theorem Nodup.ndinter
  given: {s : Multiset α} (t : Multiset α)
  statement: Nodup s -> Nodup (ndinter s t)
  proof: Nodup.filter _

中文:
定理 Nodup.ndinter
  条件: {s : Multiset α} (t : Multiset α)
  结论: Nodup s -> Nodup (ndinter s t)
  证明: Nodup.filter _

Depends on / 依赖: Nodup.filter, filter
-/
theorem Nodup.ndinter {s : Multiset α} (t : Multiset α) : Nodup s -> Nodup (ndinter s t) :=
  Nodup.filter _

/--
theorem `le_ndinter` / 定理 `le_ndinter`

English:
theorem le_ndinter
  given: {s t u : Multiset α}
  statement: s <= ndinter t u ↔ s <= t ∧ s subseteq u
  proof: by
  simp [ndinter, le_filter, subset_iff]

中文:
定理 le_ndinter
  条件: {s t u : Multiset α}
  结论: s <= ndinter t u ↔ s <= t ∧ s subseteq u
  证明: by
  simp [ndinter, le_filter, subset_iff]

Depends on / 依赖: le_filter, ndinter, subset_iff
-/
theorem le_ndinter {s t u : Multiset α} : s <= ndinter t u ↔ s <= t ∧ s subseteq u := by
  simp [ndinter, le_filter, subset_iff]

/--
theorem `ndinter_le_left` / 定理 `ndinter_le_left`

English:
theorem ndinter_le_left
  given: (s t : Multiset α)
  statement: ndinter s t <= s
  proof: (le_ndinter.1 le_rfl).1

中文:
定理 ndinter_le_left
  条件: (s t : Multiset α)
  结论: ndinter s t <= s
  证明: (le_ndinter.1 le_rfl).1

Depends on / 依赖: le_ndinter, le_rfl
-/
theorem ndinter_le_left (s t : Multiset α) : ndinter s t <= s :=
  (le_ndinter.1 le_rfl).1

/--
theorem `ndinter_subset_left` / 定理 `ndinter_subset_left`

English:
theorem ndinter_subset_left
  given: (s t : Multiset α)
  statement: ndinter s t subseteq s
  proof: subset_of_le (ndinter_le_left s t)

中文:
定理 ndinter_subset_left
  条件: (s t : Multiset α)
  结论: ndinter s t subseteq s
  证明: subset_of_le (ndinter_le_left s t)

Depends on / 依赖: ndinter_le_left, subset_of_le
-/
theorem ndinter_subset_left (s t : Multiset α) : ndinter s t subseteq s :=
  subset_of_le (ndinter_le_left s t)

/--
theorem `ndinter_subset_right` / 定理 `ndinter_subset_right`

English:
theorem ndinter_subset_right
  given: (s t : Multiset α)
  statement: ndinter s t subseteq t
  proof: (le_ndinter.1 le_rfl).2

中文:
定理 ndinter_subset_right
  条件: (s t : Multiset α)
  结论: ndinter s t subseteq t
  证明: (le_ndinter.1 le_rfl).2

Depends on / 依赖: le_ndinter, le_rfl
-/
theorem ndinter_subset_right (s t : Multiset α) : ndinter s t subseteq t :=
  (le_ndinter.1 le_rfl).2

/--
theorem `ndinter_le_right` / 定理 `ndinter_le_right`

English:
theorem ndinter_le_right
  given: {s} (t : Multiset α) (d : Nodup s)
  statement: ndinter s t <= t
  proof: (le_iff_subset <| d.ndinter _).2 ndinter_subset_right _ _

中文:
定理 ndinter_le_right
  条件: {s} (t : Multiset α) (d : Nodup s)
  结论: ndinter s t <= t
  证明: (le_iff_subset <| d.ndinter _).2 ndinter_subset_right _ _

Depends on / 依赖: d.ndinter, le_iff_subset, ndinter, ndinter_subset_right
-/
theorem ndinter_le_right {s} (t : Multiset α) (d : Nodup s) : ndinter s t <= t :=
(le_iff_subset <| d.ndinter _).2 ndinter_subset_right _ _

/--
theorem `inter_le_ndinter` / 定理 `inter_le_ndinter`

English:
theorem inter_le_ndinter
  given: (s t : Multiset α)
  statement: s inter t <= ndinter s t
  proof: le_ndinter.2 ⟨inter_le_left, subset_of_le inter_le_right⟩

@[simp]

中文:
定理 inter_le_ndinter
  条件: (s t : Multiset α)
  结论: s inter t <= ndinter s t
  证明: le_ndinter.2 ⟨inter_le_left, subset_of_le inter_le_right⟩

@[simp]

Depends on / 依赖: inter_le_left, inter_le_right, le_ndinter, subset_of_le
-/
theorem inter_le_ndinter (s t : Multiset α) : s inter t <= ndinter s t :=
  le_ndinter.2 ⟨inter_le_left, subset_of_le inter_le_right⟩

@[simp]
/--
theorem `ndinter_eq_inter` / 定理 `ndinter_eq_inter`

English:
theorem ndinter_eq_inter
  given: {s t : Multiset α} (d : Nodup s)
  statement: ndinter s t = s inter t
  proof: le_antisymm (le_inter (ndinter_le_left _ _) (ndinter_le_right _ d)) (inter_le_ndinter _ _)

@[simp]

中文:
定理 ndinter_eq_inter
  条件: {s t : Multiset α} (d : Nodup s)
  结论: ndinter s t = s inter t
  证明: le_antisymm (le_inter (ndinter_le_left _ _) (ndinter_le_right _ d)) (inter_le_ndinter _ _)

@[simp]

Depends on / 依赖: inter_le_ndinter, le_antisymm, le_inter, ndinter_le_left, ndinter_le_right
-/
theorem ndinter_eq_inter {s t : Multiset α} (d : Nodup s) : ndinter s t = s inter t :=
  le_antisymm (le_inter (ndinter_le_left _ _) (ndinter_le_right _ d)) (inter_le_ndinter _ _)

@[simp]
/--
theorem `Nodup.inter` / 定理 `Nodup.inter`

English:
theorem Nodup.inter
  given: {s : Multiset α} (t : Multiset α) (d : Nodup s)
  statement: Nodup (s inter t)
  proof: by
  rw [← ndinter_eq_inter d]
  exact d.filter _

中文:
定理 Nodup.inter
  条件: {s : Multiset α} (t : Multiset α) (d : Nodup s)
  结论: Nodup (s inter t)
  证明: by
  rw [← ndinter_eq_inter d]
  exact d.filter _
-/
theorem Nodup.inter {s : Multiset α} (t : Multiset α) (d : Nodup s) : Nodup (s inter t) := by
  rw [← ndinter_eq_inter d]
  exact d.filter _

/--
theorem `ndinter_eq_zero_iff_disjoint` / 定理 `ndinter_eq_zero_iff_disjoint`

English:
theorem ndinter_eq_zero_iff_disjoint
  given: {s t : Multiset α}
  statement: ndinter s t = 0 ↔ Disjoint s t
  proof: by
  rw [← subset_zero]; simp [subset_iff, disjoint_left]

alias ⟨_, Disjoint.ndinter_eq_zero⟩ := ndinter_eq_zero_iff_disjoint

中文:
定理 ndinter_eq_zero_iff_disjoint
  条件: {s t : Multiset α}
  结论: ndinter s t = 0 ↔ Disjoint s t
  证明: by
  rw [← subset_zero]; simp [subset_iff, disjoint_left]

alias ⟨_, Disjoint.ndinter_eq_zero⟩ := ndinter_eq_zero_iff_disjoint

Depends on / 依赖: disjoint_left, subset_iff, subset_zero
-/
theorem ndinter_eq_zero_iff_disjoint {s t : Multiset α} : ndinter s t = 0 ↔ Disjoint s t := by
  rw [← subset_zero]; simp [subset_iff, disjoint_left]

alias ⟨_, Disjoint.ndinter_eq_zero⟩ := ndinter_eq_zero_iff_disjoint

/--
theorem `Subset.ndinter_eq_left` / 定理 `Subset.ndinter_eq_left`

English:
theorem Subset.ndinter_eq_left
  given: {s t : Multiset α} (h : s subseteq t)
  statement: s.ndinter t = s
  proof: by
  induction s, t using Quot.induction_on₂
  rw [quot_mk_to_coe'']; rw [quot_mk_to_coe'']; rw [coe_ndinter]; rw [List.Subset.inter_eq_left h]

中文:
定理 Subset.ndinter_eq_left
  条件: {s t : Multiset α} (h : s subseteq t)
  结论: s.ndinter t = s
  证明: by
  induction s, t using Quot.induction_on₂
  rw [quot_mk_to_coe'']; rw [quot_mk_to_coe'']; rw [coe_ndinter]; rw [List.Subset.inter_eq_left h]

Depends on / 依赖: List.Subset.inter_eq_left, Quot.induction_on, Subset, coe_ndinter, inter_eq_left, quot_mk_to_coe
-/
theorem Subset.ndinter_eq_left {s t : Multiset α} (h : s subseteq t) : s.ndinter t = s := by
  induction s, t using Quot.induction_on₂
  rw [quot_mk_to_coe'']; rw [quot_mk_to_coe'']; rw [coe_ndinter]; rw [List.Subset.inter_eq_left h]

end Multiset
