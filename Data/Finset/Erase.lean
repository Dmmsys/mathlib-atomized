/-
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura, Jeremy Avigad, Minchao Wu, Mario Carneiro
-/
module

public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Multiset.Filter

/-!
# Erasing an element from a finite set

## Main declarations

* `Finset.erase`: For any `a : α`, `erase s a` returns `s` with the element `a` removed.

## Tags

finite sets, finset

-/

@[expose] public section

-- Assert that we define `Finset` without the material on `List.sublists`.
-- Note that we cannot use `List.sublists` itself as that is defined very early.
assert_not_exists List.sublistsLen Multiset.powerset CompleteLattice IsOrderedMonoid

open Multiset Subtype Function

universe u

variable {α : Type*} {β : Type*} {γ : Type*}

namespace Finset

-- TODO: these should be global attributes, but this will require fixing other files
attribute [local trans] Subset.trans Superset.trans

/-! ### erase -/

section Erase

variable [DecidableEq α] {s t u v : Finset α} {a b : α}

/--
Definition of `erase` / `erase` 的定义

English:
definition erase
  signature: (s : Finset α) (a : α)
  body: ⟨_, s.2.erase a⟩

@[simp]

中文:
定义 erase
  签名: (s : 有限集 α) (a : α)
  定义体: ⟨_, s.2.erase a⟩

@[simp]
-/
def erase (s : Finset α) (a : α) : Finset α :=
  ⟨_, s.2.erase a⟩

@[simp]
/--
theorem `erase_val` / 定理 `erase_val`

English:
theorem erase_val
  given: (s : Finset α) (a : α)
  statement: (erase s a).1 = s.1.erase a
  proof: rfl

@[simp, grind =]

中文:
定理 erase_val
  条件: (s : 有限集 α) (a : α)
  结论: (erase s a).1 = s.1.erase a
  证明: rfl

@[simp, grind =]
-/
theorem erase_val (s : Finset α) (a : α) : (erase s a).1 = s.1.erase a :=
  rfl

@[simp, grind =]
/--
theorem `mem_erase` / 定理 `mem_erase`

English:
theorem mem_erase
  given: {a b : α} {s : Finset α}
  statement: a in erase s b ↔ a != b ∧ a in s
  proof: s.2.mem_erase_iff

中文:
定理 mem_erase
  条件: {a b : α} {s : 有限集 α}
  结论: a in erase s b ↔ a != b ∧ a in s
  证明: s.2.mem_erase_iff

Depends on / 依赖: mem_erase_iff
-/
theorem mem_erase {a b : α} {s : Finset α} : a in erase s b ↔ a != b ∧ a in s :=
  s.2.mem_erase_iff

/--
theorem `notMem_erase` / 定理 `notMem_erase`

English:
theorem notMem_erase
  given: (a : α) (s : Finset α)
  statement: a ∉ erase s a
  proof: s.2.notMem_erase

中文:
定理 notMem_erase
  条件: (a : α) (s : 有限集 α)
  结论: a ∉ erase s a
  证明: s.2.notMem_erase

Depends on / 依赖: notMem_erase
-/
theorem notMem_erase (a : α) (s : Finset α) : a ∉ erase s a :=
  s.2.notMem_erase

/--
theorem `ne_of_mem_erase` / 定理 `ne_of_mem_erase`

English:
theorem ne_of_mem_erase
  statement: b in erase s a -> b != a
  proof: fun h => (mem_erase.1 h).1

中文:
定理 ne_of_mem_erase
  结论: b in erase s a -> b != a
  证明: fun h => (mem_erase.1 h).1

Depends on / 依赖: mem_erase
-/
theorem ne_of_mem_erase : b in erase s a -> b != a := fun h => (mem_erase.1 h).1

/--
theorem `mem_of_mem_erase` / 定理 `mem_of_mem_erase`

English:
theorem mem_of_mem_erase
  statement: b in erase s a -> b in s
  proof: Multiset.mem_of_mem_erase

中文:
定理 mem_of_mem_erase
  结论: b in erase s a -> b in s
  证明: Multiset.mem_of_mem_erase

Depends on / 依赖: Multiset, Multiset.mem_of_mem_erase, mem_of_mem_erase
-/
theorem mem_of_mem_erase : b in erase s a -> b in s :=
  Multiset.mem_of_mem_erase

/--
theorem `mem_erase_of_ne_of_mem` / 定理 `mem_erase_of_ne_of_mem`

English:
theorem mem_erase_of_ne_of_mem
  statement: a != b -> a in s -> a in erase s b
  proof: by
  simp only [mem_erase]; exact And.intro

中文:
定理 mem_erase_of_ne_of_mem
  结论: a != b -> a in s -> a in erase s b
  证明: by
  simp only [mem_erase]; exact And.intro

Depends on / 依赖: And.intro, mem_erase
-/
theorem mem_erase_of_ne_of_mem : a != b -> a in s -> a in erase s b := by
  simp only [mem_erase]; exact And.intro

/--
theorem `eq_of_mem_of_notMem_erase` / 定理 `eq_of_mem_of_notMem_erase`

English:
theorem eq_of_mem_of_notMem_erase
  given: (hs : b in s) (hsa : b ∉ s.erase a)
  statement: b = a
  proof: by grind

@[simp]

中文:
定理 eq_of_mem_of_notMem_erase
  条件: (hs : b in s) (hsa : b ∉ s.erase a)
  结论: b = a
  证明: by grind

@[simp]
-/
theorem eq_of_mem_of_notMem_erase (hs : b in s) (hsa : b ∉ s.erase a) : b = a := by grind

@[simp]
/--
theorem `erase_eq_of_notMem` / 定理 `erase_eq_of_notMem`

English:
theorem erase_eq_of_notMem
  given: {a : α} {s : Finset α} (h : a ∉ s)
  statement: erase s a = s
  proof: eq_of_veq erase_of_notMem h

@[simp]

中文:
定理 erase_eq_of_notMem
  条件: {a : α} {s : 有限集 α} (h : a ∉ s)
  结论: erase s a = s
  证明: eq_of_veq erase_of_notMem h

@[simp]

Depends on / 依赖: eq_of_veq, erase_of_notMem
-/
theorem erase_eq_of_notMem {a : α} {s : Finset α} (h : a ∉ s) : erase s a = s :=
eq_of_veq erase_of_notMem h

@[simp]
/--
theorem `erase_eq_self` / 定理 `erase_eq_self`

English:
theorem erase_eq_self
  statement: s.erase a = s ↔ a ∉ s
  proof: ⟨fun h => h ▸ notMem_erase _ _, erase_eq_of_notMem⟩

中文:
定理 erase_eq_self
  结论: s.erase a = s ↔ a ∉ s
  证明: ⟨fun h => h ▸ notMem_erase _ _, erase_eq_of_notMem⟩

Depends on / 依赖: erase_eq_of_notMem, notMem_erase
-/
theorem erase_eq_self : s.erase a = s ↔ a ∉ s :=
  ⟨fun h => h ▸ notMem_erase _ _, erase_eq_of_notMem⟩

/--
theorem `erase_ne_self` / 定理 `erase_ne_self`

English:
theorem erase_ne_self
  statement: s.erase a != s ↔ a in s
  proof: erase_eq_self.not_left

@[gcongr]

中文:
定理 erase_ne_self
  结论: s.erase a != s ↔ a in s
  证明: erase_eq_self.not_left

@[gcongr]

Depends on / 依赖: erase_eq_self, erase_eq_self.not_left, not_left
-/
theorem erase_ne_self : s.erase a != s ↔ a in s :=
  erase_eq_self.not_left

@[gcongr]
/--
theorem `erase_subset_erase` / 定理 `erase_subset_erase`

English:
theorem erase_subset_erase
  given: (a : α) {s t : Finset α} (h : s subseteq t)
  statement: erase s a subseteq erase t a
  proof: val_le_iff.1 erase_le_erase _ val_le_iff.2 h

中文:
定理 erase_subset_erase
  条件: (a : α) {s t : 有限集 α} (h : s subseteq t)
  结论: erase s a subseteq erase t a
  证明: val_le_iff.1 erase_le_erase _ val_le_iff.2 h

Depends on / 依赖: erase_le_erase, val_le_iff
-/
theorem erase_subset_erase (a : α) {s t : Finset α} (h : s subseteq t) : erase s a subseteq erase t a :=
val_le_iff.1 erase_le_erase _ val_le_iff.2 h

/--
theorem `erase_subset` / 定理 `erase_subset`

English:
theorem erase_subset
  given: (a : α) (s : Finset α)
  statement: erase s a subseteq s
  proof: Multiset.erase_subset _ _

中文:
定理 erase_subset
  条件: (a : α) (s : 有限集 α)
  结论: erase s a subseteq s
  证明: Multiset.erase_subset _ _

Depends on / 依赖: Multiset, Multiset.erase_subset, erase_subset
-/
theorem erase_subset (a : α) (s : Finset α) : erase s a subseteq s :=
  Multiset.erase_subset _ _

/--
theorem `subset_erase` / 定理 `subset_erase`

English:
theorem subset_erase
  given: {a : α} {s t : Finset α}
  statement: s subseteq t.erase a ↔ s subseteq t ∧ a ∉ s
  proof: by grind

@[simp, norm_cast]

中文:
定理 subset_erase
  条件: {a : α} {s t : 有限集 α}
  结论: s subseteq t.erase a ↔ s subseteq t ∧ a ∉ s
  证明: by grind

@[simp, norm_cast]
-/
theorem subset_erase {a : α} {s t : Finset α} : s subseteq t.erase a ↔ s subseteq t ∧ a ∉ s := by grind

@[simp, norm_cast]
/--
theorem `coe_erase` / 定理 `coe_erase`

English:
theorem coe_erase
  given: (a : α) (s : Finset α)
  statement: ↑(erase s a) = (s \ {a} : Set α)
  proof: by grind

中文:
定理 coe_erase
  条件: (a : α) (s : 有限集 α)
  结论: ↑(erase s a) = (s \ {a} : 集合 α)
  证明: by grind
-/
theorem coe_erase (a : α) (s : Finset α) : ↑(erase s a) = (s \ {a} : Set α) := by grind

/--
theorem `erase_idem` / 定理 `erase_idem`

English:
theorem erase_idem
  given: {a : α} {s : Finset α}
  statement: erase (erase s a) a = erase s a
  proof: by simp

中文:
定理 erase_idem
  条件: {a : α} {s : 有限集 α}
  结论: erase (erase s a) a = erase s a
  证明: by simp
-/
theorem erase_idem {a : α} {s : Finset α} : erase (erase s a) a = erase s a := by simp

/--
theorem `erase_right_comm` / 定理 `erase_right_comm`

English:
theorem erase_right_comm
  given: {a b : α} {s : Finset α}
  statement: erase (erase s a) b = erase (erase s b) a
  proof: by
  grind

中文:
定理 erase_right_comm
  条件: {a b : α} {s : 有限集 α}
  结论: erase (erase s a) b = erase (erase s b) a
  证明: by
  grind
-/
theorem erase_right_comm {a b : α} {s : Finset α} : erase (erase s a) b = erase (erase s b) a := by
  grind

/--
theorem `erase_inj` / 定理 `erase_inj`

English:
theorem erase_inj
  given: {x y : α} (s : Finset α) (hx : x in s)
  statement: s.erase x = s.erase y ↔ x = y
  proof: by
  grind [eq_of_mem_of_notMem_erase]

中文:
定理 erase_inj
  条件: {x y : α} (s : 有限集 α) (hx : x in s)
  结论: s.erase x = s.erase y ↔ x = y
  证明: by
  grind [eq_of_mem_of_notMem_erase]

Depends on / 依赖: eq_of_mem_of_notMem_erase
-/
theorem erase_inj {x y : α} (s : Finset α) (hx : x in s) : s.erase x = s.erase y ↔ x = y := by
  grind [eq_of_mem_of_notMem_erase]

/--
theorem `erase_injOn` / 定理 `erase_injOn`

English:
theorem erase_injOn
  given: (s : Finset α)
  statement: Set.InjOn s.erase s
  proof: fun _ _ _ _ => (erase_inj s ‹_›).mp

中文:
定理 erase_injOn
  条件: (s : 有限集 α)
  结论: 集合.单射限制 s.erase s
  证明: fun _ _ _ _ => (erase_inj s ‹_›).mp

Depends on / 依赖: erase_inj
-/
theorem erase_injOn (s : Finset α) : Set.InjOn s.erase s := fun _ _ _ _ => (erase_inj s ‹_›).mp

end Erase

end Finset
