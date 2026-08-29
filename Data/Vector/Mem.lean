/-
Copyright (c) 2022 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
module

public import Mathlib.Data.Vector.Basic

/-!
# Theorems about membership of elements in vectors

This file contains theorems for membership in a `v.toList` for a vector `v`.
Having the length available in the type allows some of the lemmas to be
  simpler and more general than the original version for lists.
In particular we can avoid some assumptions about types being `Inhabited`,
  and make more general statements about `head` and `tail`.
-/

public section

namespace List

namespace Vector

variable {α β : Type*} {n : Nat} (a a' : α)

@[simp]
/--
theorem `get_mem` / 定理 `get_mem`

English:
theorem get_mem
  given: (i : Fin n) (v : Vector α n)
  statement: v.get i in v.toList
  proof: List.get_mem _ _

中文:
定理 get_mem
  条件: (i : 有限集 n) (v : Vector α n)
  结论: v.get i in v.toList
  证明: List.get_mem _ _

Depends on / 依赖: List.get_mem, get_mem
-/
theorem get_mem (i : Fin n) (v : Vector α n) : v.get i in v.toList := List.get_mem _ _

/--
theorem `mem_iff_get` / 定理 `mem_iff_get`

English:
theorem mem_iff_get
  given: (v : Vector α n)
  statement: a in v.toList ↔ exists i, v.get i = a
  proof: by
  simp only [List.mem_iff_get, Fin.exists_iff, Vector.get_eq_get_toList]
  exact
    ⟨fun ⟨i, hi, h⟩ => ⟨i, by rwa [toList_length] at hi, h⟩, fun ⟨i, hi, h⟩ =>
      ⟨i, by rwa [toList_length], h⟩⟩

中文:
定理 mem_iff_get
  条件: (v : Vector α n)
  结论: a in v.toList ↔ 存在 i, v.get i = a
  证明: by
  simp only [List.mem_iff_get, Fin.exists_iff, Vector.get_eq_get_toList]
  exact
    ⟨fun ⟨i, hi, h⟩ => ⟨i, by rwa [toList_length] at hi, h⟩, fun ⟨i, hi, h⟩ =>
      ⟨i, by rwa [toList_length], h⟩⟩

Depends on / 依赖: Fin.exists_iff, List.mem_iff_get, Vector, Vector.get_eq_get_toList, exists_iff, get_eq_get_toList, mem_iff_get, toList_length
-/
theorem mem_iff_get (v : Vector α n) : a in v.toList ↔ exists i, v.get i = a := by
  simp only [List.mem_iff_get, Fin.exists_iff, Vector.get_eq_get_toList]
  exact
    ⟨fun ⟨i, hi, h⟩ => ⟨i, by rwa [toList_length] at hi, h⟩, fun ⟨i, hi, h⟩ =>
      ⟨i, by rwa [toList_length], h⟩⟩

/--
theorem `notMem_nil` / 定理 `notMem_nil`

English:
theorem notMem_nil
  statement: a ∉ (Vector.nil : Vector α 0).toList
  proof: by
  simp

中文:
定理 notMem_nil
  结论: a ∉ (Vector.nil : Vector α 0).toList
  证明: by
  simp
-/
theorem notMem_nil : a ∉ (Vector.nil : Vector α 0).toList := by
  simp

/--
theorem `notMem_zero` / 定理 `notMem_zero`

English:
theorem notMem_zero
  given: (v : Vector α 0)
  statement: a ∉ v.toList
  proof: (Vector.eq_nil v).symm ▸ notMem_nil a

中文:
定理 notMem_zero
  条件: (v : Vector α 0)
  结论: a ∉ v.toList
  证明: (Vector.eq_nil v).symm ▸ notMem_nil a

Depends on / 依赖: Vector, Vector.eq_nil, eq_nil, notMem_nil
-/
theorem notMem_zero (v : Vector α 0) : a ∉ v.toList :=
  (Vector.eq_nil v).symm ▸ notMem_nil a

/--
theorem `mem_cons_iff` / 定理 `mem_cons_iff`

English:
theorem mem_cons_iff
  given: (v : Vector α n)
  statement: a' in (a ::ᵥ v).toList ↔ a' = a ∨ a' in v.toList
  proof: by
  rw [Vector.toList_cons]; rw [List.mem_cons]

中文:
定理 mem_cons_iff
  条件: (v : Vector α n)
  结论: a' in (a ::ᵥ v).toList ↔ a' = a ∨ a' in v.toList
  证明: by
  rw [Vector.toList_cons]; rw [List.mem_cons]

Depends on / 依赖: List.mem_cons, Vector, Vector.toList_cons, mem_cons, toList_cons
-/
theorem mem_cons_iff (v : Vector α n) : a' in (a ::ᵥ v).toList ↔ a' = a ∨ a' in v.toList := by
  rw [Vector.toList_cons]; rw [List.mem_cons]

set_option backward.isDefEq.respectTransparency false in
/--
theorem `mem_succ_iff` / 定理 `mem_succ_iff`

English:
theorem mem_succ_iff
  given: (v : Vector α (n + 1))
  statement: a in v.toList ↔ a = v.head ∨ a in v.tail.toList
  proof: by
  obtain ⟨a', v', h⟩ := exists_eq_cons v
  simp_rw [h, Vector.mem_cons_iff, Vector.head_cons, Vector.tail_cons]

中文:
定理 mem_succ_iff
  条件: (v : Vector α (n + 1))
  结论: a in v.toList ↔ a = v.head ∨ a in v.tail.toList
  证明: by
  obtain ⟨a', v', h⟩ := exists_eq_cons v
  simp_rw [h, Vector.mem_cons_iff, Vector.head_cons, Vector.tail_cons]

Depends on / 依赖: Vector, Vector.head_cons, Vector.mem_cons_iff, Vector.tail_cons, exists_eq_cons, head_cons, mem_cons_iff, simp_rw, tail_cons
-/
theorem mem_succ_iff (v : Vector α (n + 1)) : a in v.toList ↔ a = v.head ∨ a in v.tail.toList := by
  obtain ⟨a', v', h⟩ := exists_eq_cons v
  simp_rw [h, Vector.mem_cons_iff, Vector.head_cons, Vector.tail_cons]

/--
theorem `mem_cons_self` / 定理 `mem_cons_self`

English:
theorem mem_cons_self
  given: (v : Vector α n)
  statement: a in (a ::ᵥ v).toList
  proof: (Vector.mem_iff_get a (a ::ᵥ v)).2 ⟨0, Vector.get_cons_zero a v⟩

@[simp]

中文:
定理 mem_cons_self
  条件: (v : Vector α n)
  结论: a in (a ::ᵥ v).toList
  证明: (Vector.mem_iff_get a (a ::ᵥ v)).2 ⟨0, Vector.get_cons_zero a v⟩

@[simp]

Depends on / 依赖: Vector, Vector.get_cons_zero, Vector.mem_iff_get, get_cons_zero, mem_iff_get
-/
theorem mem_cons_self (v : Vector α n) : a in (a ::ᵥ v).toList :=
  (Vector.mem_iff_get a (a ::ᵥ v)).2 ⟨0, Vector.get_cons_zero a v⟩

@[simp]
/--
theorem `head_mem` / 定理 `head_mem`

English:
theorem head_mem
  given: (v : Vector α (n + 1))
  statement: v.head in v.toList
  proof: (Vector.mem_iff_get v.head v).2 ⟨0, Vector.get_zero v⟩

中文:
定理 head_mem
  条件: (v : Vector α (n + 1))
  结论: v.head in v.toList
  证明: (Vector.mem_iff_get v.head v).2 ⟨0, Vector.get_zero v⟩

Depends on / 依赖: Vector, Vector.get_zero, Vector.mem_iff_get, get_zero, mem_iff_get, v.head
-/
theorem head_mem (v : Vector α (n + 1)) : v.head in v.toList :=
  (Vector.mem_iff_get v.head v).2 ⟨0, Vector.get_zero v⟩

/--
theorem `mem_cons_of_mem` / 定理 `mem_cons_of_mem`

English:
theorem mem_cons_of_mem
  given: (v : Vector α n) (ha' : a' in v.toList)
  statement: a' in (a ::ᵥ v).toList
  proof: (Vector.mem_cons_iff a a' v).2 (Or.inr ha')

中文:
定理 mem_cons_of_mem
  条件: (v : Vector α n) (ha' : a' in v.toList)
  结论: a' in (a ::ᵥ v).toList
  证明: (Vector.mem_cons_iff a a' v).2 (Or.inr ha')

Depends on / 依赖: Or.inr, Vector, Vector.mem_cons_iff, mem_cons_iff
-/
theorem mem_cons_of_mem (v : Vector α n) (ha' : a' in v.toList) : a' in (a ::ᵥ v).toList :=
  (Vector.mem_cons_iff a a' v).2 (Or.inr ha')

/--
theorem `mem_of_mem_tail` / 定理 `mem_of_mem_tail`

English:
theorem mem_of_mem_tail
  given: (v : Vector α n) (ha : a in v.tail.toList)
  statement: a in v.toList
  proof: by
  induction n with
  | zero => exact False.elim (Vector.notMem_zero a v.tail ha)
  | succ n _ => exact (mem_succ_iff a v).2 (Or.inr ha)

中文:
定理 mem_of_mem_tail
  条件: (v : Vector α n) (ha : a in v.tail.toList)
  结论: a in v.toList
  证明: by
  induction n with
  | zero => exact False.elim (Vector.notMem_zero a v.tail ha)
  | succ n _ => exact (mem_succ_iff a v).2 (Or.inr ha)

Depends on / 依赖: False.elim, Or.inr, Vector, Vector.notMem_zero, mem_succ_iff, notMem_zero, v.tail
-/
theorem mem_of_mem_tail (v : Vector α n) (ha : a in v.tail.toList) : a in v.toList := by
  induction n with
  | zero => exact False.elim (Vector.notMem_zero a v.tail ha)
  | succ n _ => exact (mem_succ_iff a v).2 (Or.inr ha)

/--
theorem `mem_map_iff` / 定理 `mem_map_iff`

English:
theorem mem_map_iff
  given: (b : β) (v : Vector α n) (f : α -> β)
  proof: by
  rw [Vector.toList_map]; rw [List.mem_map]

中文:
定理 mem_map_iff
  条件: (b : β) (v : Vector α n) (f : α -> β)
  证明: by
  rw [Vector.toList_map]; rw [List.mem_map]

Depends on / 依赖: List.mem_map, Vector, Vector.toList_map, mem_map, toList_map
-/
theorem mem_map_iff (b : β) (v : Vector α n) (f : α -> β) :
    b in (v.map f).toList ↔ exists a : α, a in v.toList ∧ f a = b := by
  rw [Vector.toList_map]; rw [List.mem_map]

/--
theorem `notMem_map_zero` / 定理 `notMem_map_zero`

English:
theorem notMem_map_zero
  given: (b : β) (v : Vector α 0) (f : α -> β)
  statement: b ∉ (v.map f).toList
  proof: by
  simpa only [Vector.eq_nil v, Vector.map_nil, Vector.toList_nil] using List.not_mem_nil

中文:
定理 notMem_map_zero
  条件: (b : β) (v : Vector α 0) (f : α -> β)
  结论: b ∉ (v.map f).toList
  证明: by
  simpa only [Vector.eq_nil v, Vector.map_nil, Vector.toList_nil] using List.not_mem_nil

Depends on / 依赖: List.not_mem_nil, Vector, Vector.eq_nil, Vector.map_nil, Vector.toList_nil, eq_nil, map_nil, not_mem_nil, toList_nil
-/
theorem notMem_map_zero (b : β) (v : Vector α 0) (f : α -> β) : b ∉ (v.map f).toList := by
  simpa only [Vector.eq_nil v, Vector.map_nil, Vector.toList_nil] using List.not_mem_nil

/--
theorem `mem_map_succ_iff` / 定理 `mem_map_succ_iff`

English:
theorem mem_map_succ_iff
  given: (b : β) (v : Vector α (n + 1)) (f : α -> β)
  proof: by
  rw [mem_succ_iff]; rw [head_map]; rw [tail_map]; rw [mem_map_iff]; rw [@eq_comm _ b]

中文:
定理 mem_map_succ_iff
  条件: (b : β) (v : Vector α (n + 1)) (f : α -> β)
  证明: by
  rw [mem_succ_iff]; rw [head_map]; rw [tail_map]; rw [mem_map_iff]; rw [@eq_comm _ b]

Depends on / 依赖: eq_comm, head_map, mem_map_iff, mem_succ_iff, tail_map
-/
theorem mem_map_succ_iff (b : β) (v : Vector α (n + 1)) (f : α -> β) :
    b in (v.map f).toList ↔ f v.head = b ∨ exists a : α, a in v.tail.toList ∧ f a = b := by
  rw [mem_succ_iff]; rw [head_map]; rw [tail_map]; rw [mem_map_iff]; rw [@eq_comm _ b]

end Vector

end List
