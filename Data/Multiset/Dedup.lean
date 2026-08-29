/-
Copyright (c) 2017 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
module

public import Mathlib.Data.List.Dedup
public import Mathlib.Data.Multiset.UnionInter

/-!
# Erasing duplicates in a multiset.
-/

@[expose] public section

assert_not_exists Monoid

namespace Multiset

open List

variable {α β : Type*} [DecidableEq α]

/-! ### dedup -/


/--
Definition of `dedup` / `dedup` 的定义

English:
definition dedup
  signature: (s : Multiset α)
  body: Quot.liftOn s (fun l => (l.dedup : Multiset α)) fun _ _ p => Quot.sound p.dedup

@[simp]

中文:
定义 dedup
  签名: (s : Multiset α)
  定义体: Quot.liftOn s (fun l => (l.dedup : Multiset α)) fun _ _ p => Quot.sound p.dedup

@[simp]

Depends on / 依赖: Multiset, Quot.liftOn, Quot.sound, Unique, Unique.mk, l.dedup, liftOn, p.dedup
-/
def dedup (s : Multiset α) : Multiset α :=
  Quot.liftOn s (fun l => (l.dedup : Multiset α)) fun _ _ p => Quot.sound p.dedup

@[simp]
/--
theorem `coe_dedup` / 定理 `coe_dedup`

English:
theorem coe_dedup
  given: (l : List α)
  statement: @dedup α _ l = l.dedup
  proof: rfl

@[simp]

中文:
定理 coe_dedup
  条件: (l : List α)
  结论: @dedup α _ l = l.dedup
  证明: rfl

@[simp]
-/
theorem coe_dedup (l : List α) : @dedup α _ l = l.dedup :=
  rfl

@[simp]
/--
theorem `dedup_zero` / 定理 `dedup_zero`

English:
theorem dedup_zero
  statement: @dedup α _ 0 = 0
  proof: rfl

@[simp]

中文:
定理 dedup_zero
  结论: @dedup α _ 0 = 0
  证明: rfl

@[simp]
-/
theorem dedup_zero : @dedup α _ 0 = 0 :=
  rfl

@[simp]
/--
theorem `mem_dedup` / 定理 `mem_dedup`

English:
theorem mem_dedup
  given: {a : α} {s : Multiset α}
  statement: a in dedup s ↔ a in s
  proof: Quot.induction_on s fun _ => List.mem_dedup

@[simp]

中文:
定理 mem_dedup
  条件: {a : α} {s : Multiset α}
  结论: a in dedup s ↔ a in s
  证明: Quot.induction_on s fun _ => List.mem_dedup

@[simp]

Depends on / 依赖: List.mem_dedup, Quot.induction_on, induction_on, mem_dedup, n.succ_ne_zero, nontrivial, replicate_right_injective, succ_ne_zero
-/
theorem mem_dedup {a : α} {s : Multiset α} : a in dedup s ↔ a in s :=
  Quot.induction_on s fun _ => List.mem_dedup

@[simp]
/--
theorem `dedup_cons_of_mem` / 定理 `dedup_cons_of_mem`

English:
theorem dedup_cons_of_mem
  given: {a : α} {s : Multiset α}
  statement: a in s -> dedup (a ::ₘ s) = dedup s
  proof: Quot.induction_on s fun _ m => @congr_arg _ _ _ _ ofList List.dedup_cons_of_mem m

@[simp]

中文:
定理 dedup_cons_of_mem
  条件: {a : α} {s : Multiset α}
  结论: a in s -> dedup (a ::ₘ s) = dedup s
  证明: Quot.induction_on s fun _ m => @congr_arg _ _ _ _ ofList List.dedup_cons_of_mem m

@[simp]

Depends on / 依赖: List.dedup_cons_of_mem, Quot.induction_on, congr_arg, dedup_cons_of_mem, induction_on, ofList
-/
theorem dedup_cons_of_mem {a : α} {s : Multiset α} : a in s -> dedup (a ::ₘ s) = dedup s :=
Quot.induction_on s fun _ m => @congr_arg _ _ _ _ ofList List.dedup_cons_of_mem m

@[simp]
/--
theorem `dedup_cons_of_notMem` / 定理 `dedup_cons_of_notMem`

English:
theorem dedup_cons_of_notMem
  given: {a : α} {s : Multiset α}
  statement: a ∉ s -> dedup (a ::ₘ s) = a ::ₘ dedup s
  proof: Quot.induction_on s fun _ m => congr_arg ofList List.dedup_cons_of_notMem m

中文:
定理 dedup_cons_of_notMem
  条件: {a : α} {s : Multiset α}
  结论: a ∉ s -> dedup (a ::ₘ s) = a ::ₘ dedup s
  证明: Quot.induction_on s fun _ m => congr_arg ofList List.dedup_cons_of_notMem m

Depends on / 依赖: List.dedup_cons_of_notMem, Quot.induction_on, congr_arg, dedup_cons_of_notMem, induction_on, ofList
-/
theorem dedup_cons_of_notMem {a : α} {s : Multiset α} : a ∉ s -> dedup (a ::ₘ s) = a ::ₘ dedup s :=
Quot.induction_on s fun _ m => congr_arg ofList List.dedup_cons_of_notMem m

/--
theorem `dedup_le` / 定理 `dedup_le`

English:
theorem dedup_le
  given: (s : Multiset α)
  statement: dedup s <= s
  proof: Quot.induction_on s fun _ => (dedup_sublist _).subperm

中文:
定理 dedup_le
  条件: (s : Multiset α)
  结论: dedup s <= s
  证明: Quot.induction_on s fun _ => (dedup_sublist _).subperm

Depends on / 依赖: Quot.induction_on, dedup_sublist, induction_on, subperm
-/
theorem dedup_le (s : Multiset α) : dedup s <= s :=
  Quot.induction_on s fun _ => (dedup_sublist _).subperm

/--
theorem `dedup_subset` / 定理 `dedup_subset`

English:
theorem dedup_subset
  given: (s : Multiset α)
  statement: dedup s subseteq s
  proof: subset_of_le dedup_le _

中文:
定理 dedup_subset
  条件: (s : Multiset α)
  结论: dedup s subseteq s
  证明: subset_of_le dedup_le _

Depends on / 依赖: dedup_le, subset_of_le
-/
theorem dedup_subset (s : Multiset α) : dedup s subseteq s :=
subset_of_le dedup_le _

/--
theorem `subset_dedup` / 定理 `subset_dedup`

English:
theorem subset_dedup
  given: (s : Multiset α)
  statement: s subseteq dedup s
  proof: fun _ => mem_dedup.2

@[simp]

中文:
定理 subset_dedup
  条件: (s : Multiset α)
  结论: s subseteq dedup s
  证明: fun _ => mem_dedup.2

@[simp]

Depends on / 依赖: mem_dedup
-/
theorem subset_dedup (s : Multiset α) : s subseteq dedup s := fun _ => mem_dedup.2

@[simp]
/--
theorem `dedup_subset'` / 定理 `dedup_subset'`

English:
theorem dedup_subset'
  given: {s t : Multiset α}
  statement: dedup s subseteq t ↔ s subseteq t
  proof: ⟨Subset.trans (subset_dedup _), Subset.trans (dedup_subset _)⟩

@[simp]

中文:
定理 dedup_subset'
  条件: {s t : Multiset α}
  结论: dedup s subseteq t ↔ s subseteq t
  证明: ⟨Subset.trans (subset_dedup _), Subset.trans (dedup_subset _)⟩

@[simp]

Depends on / 依赖: Subset, Subset.trans, dedup_subset, subset_dedup
-/
theorem dedup_subset' {s t : Multiset α} : dedup s subseteq t ↔ s subseteq t :=
  ⟨Subset.trans (subset_dedup _), Subset.trans (dedup_subset _)⟩

@[simp]
/--
theorem `subset_dedup'` / 定理 `subset_dedup'`

English:
theorem subset_dedup'
  given: {s t : Multiset α}
  statement: s subseteq dedup t ↔ s subseteq t
  proof: ⟨fun h => Subset.trans h (dedup_subset _), fun h => Subset.trans h (subset_dedup _)⟩

@[simp]

中文:
定理 subset_dedup'
  条件: {s t : Multiset α}
  结论: s subseteq dedup t ↔ s subseteq t
  证明: ⟨fun h => Subset.trans h (dedup_subset _), fun h => Subset.trans h (subset_dedup _)⟩

@[simp]

Depends on / 依赖: Subset, Subset.trans, dedup_subset, subset_dedup
-/
theorem subset_dedup' {s t : Multiset α} : s subseteq dedup t ↔ s subseteq t :=
  ⟨fun h => Subset.trans h (dedup_subset _), fun h => Subset.trans h (subset_dedup _)⟩

@[simp]
/--
theorem `nodup_dedup` / 定理 `nodup_dedup`

English:
theorem nodup_dedup
  given: (s : Multiset α)
  statement: Nodup (dedup s)
  proof: Quot.induction_on s List.nodup_dedup

中文:
定理 nodup_dedup
  条件: (s : Multiset α)
  结论: Nodup (dedup s)
  证明: Quot.induction_on s List.nodup_dedup

Depends on / 依赖: List.nodup_dedup, Quot.induction_on, induction_on, nodup_dedup
-/
theorem nodup_dedup (s : Multiset α) : Nodup (dedup s) :=
  Quot.induction_on s List.nodup_dedup

/--
theorem `dedup_eq_self` / 定理 `dedup_eq_self`

English:
theorem dedup_eq_self
  given: {s : Multiset α}
  statement: dedup s = s ↔ Nodup s
  proof: ⟨fun e => e ▸ nodup_dedup s, Quot.induction_on s fun _ h => congr_arg ofList h.dedup⟩

alias ⟨_, Nodup.dedup⟩ := dedup_eq_self

中文:
定理 dedup_eq_self
  条件: {s : Multiset α}
  结论: dedup s = s ↔ Nodup s
  证明: ⟨fun e => e ▸ nodup_dedup s, Quot.induction_on s fun _ h => congr_arg ofList h.dedup⟩

alias ⟨_, Nodup.dedup⟩ := dedup_eq_self

Depends on / 依赖: Quot.induction_on, congr_arg, h.dedup, induction_on, nodup_dedup, ofList
-/
theorem dedup_eq_self {s : Multiset α} : dedup s = s ↔ Nodup s :=
  ⟨fun e => e ▸ nodup_dedup s, Quot.induction_on s fun _ h => congr_arg ofList h.dedup⟩

alias ⟨_, Nodup.dedup⟩ := dedup_eq_self

/--
theorem `count_dedup` / 定理 `count_dedup`

English:
theorem count_dedup
  given: (m : Multiset α) (a : α)
  statement: m.dedup.count a = if a in m then 1 else 0
  proof: Quot.induction_on m fun _ => by
    simp only [quot_mk_to_coe'', coe_dedup, mem_coe, coe_count]
    apply List.count_dedup _ _

@[simp]

中文:
定理 count_dedup
  条件: (m : Multiset α) (a : α)
  结论: m.dedup.count a = if a in m then 1 else 0
  证明: Quot.induction_on m fun _ => by
    simp only [quot_mk_to_coe'', coe_dedup, mem_coe, coe_count]
    apply List.count_dedup _ _

@[simp]

Depends on / 依赖: List.count_dedup, Quot.induction_on, coe_count, coe_dedup, count_dedup, induction_on, mem_coe, quot_mk_to_coe
-/
theorem count_dedup (m : Multiset α) (a : α) : m.dedup.count a = if a in m then 1 else 0 :=
  Quot.induction_on m fun _ => by
    simp only [quot_mk_to_coe'', coe_dedup, mem_coe, coe_count]
    apply List.count_dedup _ _

@[simp]
/--
theorem `dedup_idem` / 定理 `dedup_idem`

English:
theorem dedup_idem
  given: {m : Multiset α}
  statement: m.dedup.dedup = m.dedup
  proof: Quot.induction_on m fun _ => @congr_arg _ _ _ _ ofList List.dedup_idem

中文:
定理 dedup_idem
  条件: {m : Multiset α}
  结论: m.dedup.dedup = m.dedup
  证明: Quot.induction_on m fun _ => @congr_arg _ _ _ _ ofList List.dedup_idem

Depends on / 依赖: List.dedup_idem, Quot.induction_on, congr_arg, dedup_idem, induction_on, ofList
-/
theorem dedup_idem {m : Multiset α} : m.dedup.dedup = m.dedup :=
  Quot.induction_on m fun _ => @congr_arg _ _ _ _ ofList List.dedup_idem

/--
theorem `dedup_eq_zero` / 定理 `dedup_eq_zero`

English:
theorem dedup_eq_zero
  given: {s : Multiset α}
  statement: dedup s = 0 ↔ s = 0
  proof: ⟨fun h => eq_zero_of_subset_zero h ▸ subset_dedup _, fun h => h.symm ▸ dedup_zero⟩

@[simp]

中文:
定理 dedup_eq_zero
  条件: {s : Multiset α}
  结论: dedup s = 0 ↔ s = 0
  证明: ⟨fun h => eq_zero_of_subset_zero h ▸ subset_dedup _, fun h => h.symm ▸ dedup_zero⟩

@[simp]

Depends on / 依赖: dedup_zero, eq_zero_of_subset_zero, h.symm, subset_dedup
-/
theorem dedup_eq_zero {s : Multiset α} : dedup s = 0 ↔ s = 0 :=
⟨fun h => eq_zero_of_subset_zero h ▸ subset_dedup _, fun h => h.symm ▸ dedup_zero⟩

@[simp]
/--
theorem `dedup_singleton` / 定理 `dedup_singleton`

English:
theorem dedup_singleton
  given: {a : α}
  statement: dedup ({a} : Multiset α) = {a}
  proof: (nodup_singleton _).dedup

中文:
定理 dedup_singleton
  条件: {a : α}
  结论: dedup ({a} : Multiset α) = {a}
  证明: (nodup_singleton _).dedup

Depends on / 依赖: nodup_singleton
-/
theorem dedup_singleton {a : α} : dedup ({a} : Multiset α) = {a} :=
  (nodup_singleton _).dedup

/--
theorem `le_dedup` / 定理 `le_dedup`

English:
theorem le_dedup
  given: {s t : Multiset α}
  statement: s <= dedup t ↔ s <= t ∧ Nodup s
  proof: ⟨fun h => ⟨le_trans h (dedup_le _), nodup_of_le h (nodup_dedup _)⟩,
fun ⟨l, d⟩ => (le_iff_subset d).2 Subset.trans (subset_of_le l) (subset_dedup _)⟩

中文:
定理 le_dedup
  条件: {s t : Multiset α}
  结论: s <= dedup t ↔ s <= t ∧ Nodup s
  证明: ⟨fun h => ⟨le_trans h (dedup_le _), nodup_of_le h (nodup_dedup _)⟩,
fun ⟨l, d⟩ => (le_iff_subset d).2 Subset.trans (subset_of_le l) (subset_dedup _)⟩

Depends on / 依赖: Subset, Subset.trans, dedup_le, le_iff_subset, le_trans, nodup_dedup, nodup_of_le, subset_dedup, subset_of_le
-/
theorem le_dedup {s t : Multiset α} : s <= dedup t ↔ s <= t ∧ Nodup s :=
  ⟨fun h => ⟨le_trans h (dedup_le _), nodup_of_le h (nodup_dedup _)⟩,
fun ⟨l, d⟩ => (le_iff_subset d).2 Subset.trans (subset_of_le l) (subset_dedup _)⟩

/--
theorem `le_dedup_self` / 定理 `le_dedup_self`

English:
theorem le_dedup_self
  given: {s : Multiset α}
  statement: s <= dedup s ↔ Nodup s
  proof: by
  rw [le_dedup]; rw [and_iff_right le_rfl]

中文:
定理 le_dedup_self
  条件: {s : Multiset α}
  结论: s <= dedup s ↔ Nodup s
  证明: by
  rw [le_dedup]; rw [and_iff_right le_rfl]

Depends on / 依赖: and_iff_right, le_dedup, le_rfl
-/
theorem le_dedup_self {s : Multiset α} : s <= dedup s ↔ Nodup s := by
  rw [le_dedup]; rw [and_iff_right le_rfl]

/--
theorem `dedup_ext` / 定理 `dedup_ext`

English:
theorem dedup_ext
  given: {s t : Multiset α}
  statement: dedup s = dedup t ↔ forall a, a in s ↔ a in t
  proof: by
  simp [Nodup.ext]

中文:
定理 dedup_ext
  条件: {s t : Multiset α}
  结论: dedup s = dedup t ↔ 对任意 a, a in s ↔ a in t
  证明: by
  simp [Nodup.ext]

Depends on / 依赖: Nodup.ext
-/
theorem dedup_ext {s t : Multiset α} : dedup s = dedup t ↔ forall a, a in s ↔ a in t := by
  simp [Nodup.ext]

/--
theorem `dedup_map_of_injective` / 定理 `dedup_map_of_injective`

English:
theorem dedup_map_of_injective
  statement: [DecidableEq β] {f : α -> β} (hf : Function.Injective f)
  proof: Quot.induction_on s fun l => by simp [List.dedup_map_of_injective hf l]

中文:
定理 dedup_map_of_injective
  结论: [DecidableEq β] {f : α -> β} (hf : Function.Injective f)
  证明: Quot.induction_on s fun l => by simp [List.dedup_map_of_injective hf l]

Depends on / 依赖: List.dedup_map_of_injective, Quot.induction_on, dedup_map_of_injective, induction_on
-/
theorem dedup_map_of_injective [DecidableEq β] {f : α -> β} (hf : Function.Injective f)
    (s : Multiset α) :
    (s.map f).dedup = s.dedup.map f :=
  Quot.induction_on s fun l => by simp [List.dedup_map_of_injective hf l]

/--
theorem `dedup_map_dedup_eq` / 定理 `dedup_map_dedup_eq`

English:
theorem dedup_map_dedup_eq
  given: [DecidableEq β] (f : α -> β) (s : Multiset α)
  proof: by
  simp [dedup_ext]

中文:
定理 dedup_map_dedup_eq
  条件: [DecidableEq β] (f : α -> β) (s : Multiset α)
  证明: by
  simp [dedup_ext]

Depends on / 依赖: dedup_ext
-/
theorem dedup_map_dedup_eq [DecidableEq β] (f : α -> β) (s : Multiset α) :
    dedup (map f (dedup s)) = dedup (map f s) := by
  simp [dedup_ext]

/--
theorem `Nodup.le_dedup_iff_le` / 定理 `Nodup.le_dedup_iff_le`

English:
theorem Nodup.le_dedup_iff_le
  given: {s t : Multiset α} (hno : s.Nodup)
  statement: s <= t.dedup ↔ s <= t
  proof: by
  simp [le_dedup, hno]

中文:
定理 Nodup.le_dedup_iff_le
  条件: {s t : Multiset α} (hno : s.Nodup)
  结论: s <= t.dedup ↔ s <= t
  证明: by
  simp [le_dedup, hno]

Depends on / 依赖: le_dedup
-/
theorem Nodup.le_dedup_iff_le {s t : Multiset α} (hno : s.Nodup) : s <= t.dedup ↔ s <= t := by
  simp [le_dedup, hno]

/--
theorem `Subset.dedup_add_right` / 定理 `Subset.dedup_add_right`

English:
theorem Subset.dedup_add_right
  given: {s t : Multiset α} (h : s subseteq t)
  proof: by
  induction s, t using Quot.induction_on₂
exact congr_arg ((↑) : List α -> Multiset α) List.Subset.dedup_append_right h

中文:
定理 Subset.dedup_add_right
  条件: {s t : Multiset α} (h : s subseteq t)
  证明: by
  induction s, t using Quot.induction_on₂
exact congr_arg ((↑) : List α -> Multiset α) List.Subset.dedup_append_right h

Depends on / 依赖: List.Subset.dedup_append_right, Multiset, Quot.induction_on, Subset, congr_arg, dedup_append_right
-/
theorem Subset.dedup_add_right {s t : Multiset α} (h : s subseteq t) :
    dedup (s + t) = dedup t := by
  induction s, t using Quot.induction_on₂
exact congr_arg ((↑) : List α -> Multiset α) List.Subset.dedup_append_right h

/--
theorem `Subset.dedup_add_left` / 定理 `Subset.dedup_add_left`

English:
theorem Subset.dedup_add_left
  given: {s t : Multiset α} (h : t subseteq s)
  proof: by
  rw [s.add_comm]; rw [Subset.dedup_add_right h]

中文:
定理 Subset.dedup_add_left
  条件: {s t : Multiset α} (h : t subseteq s)
  证明: by
  rw [s.add_comm]; rw [Subset.dedup_add_right h]

Depends on / 依赖: Subset, Subset.dedup_add_right, add_comm, dedup_add_right, s.add_comm
-/
theorem Subset.dedup_add_left {s t : Multiset α} (h : t subseteq s) :
    dedup (s + t) = dedup s := by
  rw [s.add_comm]; rw [Subset.dedup_add_right h]

/--
theorem `Disjoint.dedup_add` / 定理 `Disjoint.dedup_add`

English:
theorem Disjoint.dedup_add
  given: {s t : Multiset α} (h : Disjoint s t)
  proof: by
  induction s, t using Quot.induction_on₂
exact congr_arg ((↑) : List α -> Multiset α) List.Disjoint.dedup_append (by simpa using h)

中文:
定理 Disjoint.dedup_add
  条件: {s t : Multiset α} (h : Disjoint s t)
  证明: by
  induction s, t using Quot.induction_on₂
exact congr_arg ((↑) : List α -> Multiset α) List.Disjoint.dedup_append (by simpa using h)

Depends on / 依赖: Disjoint, List.Disjoint.dedup_append, Multiset, Quot.induction_on, congr_arg, dedup_append
-/
theorem Disjoint.dedup_add {s t : Multiset α} (h : Disjoint s t) :
    dedup (s + t) = dedup s + dedup t := by
  induction s, t using Quot.induction_on₂
exact congr_arg ((↑) : List α -> Multiset α) List.Disjoint.dedup_append (by simpa using h)

/--
theorem `_root_.List.Subset.dedup_append_left` / 定理 `_root_.List.Subset.dedup_append_left`

English:
theorem _root_.List.Subset.dedup_append_left
  given: {s t : List α} (h : t subseteq s)
  proof: by
  rw [← coe_eq_coe]; rw [← coe_dedup]; rw [← coe_add]; rw [Subset.dedup_add_left h]; rw [coe_dedup]

中文:
定理 _root_.List.Subset.dedup_append_left
  条件: {s t : List α} (h : t subseteq s)
  证明: by
  rw [← coe_eq_coe]; rw [← coe_dedup]; rw [← coe_add]; rw [Subset.dedup_add_left h]; rw [coe_dedup]

Depends on / 依赖: Subset, Subset.dedup_add_left, coe_add, coe_dedup, coe_eq_coe, dedup_add_left
-/
theorem _root_.List.Subset.dedup_append_left {s t : List α} (h : t subseteq s) :
    List.dedup (s ++ t) ~ List.dedup s := by
  rw [← coe_eq_coe]; rw [← coe_dedup]; rw [← coe_add]; rw [Subset.dedup_add_left h]; rw [coe_dedup]

end Multiset
