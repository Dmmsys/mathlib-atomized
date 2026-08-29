/-
Copyright (c) 2026 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
module

import Mathlib.Data.List.Count
import Mathlib.Data.List.Enum
import Mathlib.Data.List.Nodup
import Mathlib.Data.List.Perm.Basic
public import Mathlib.Data.Nat.Notation

/-!
# Definition and basic properties of `List.offDiag`

In this file we define `List.offDiag l` to be the product `l.product l`
with the diagonal removed.
The actual definition is more complicated to avoid assuming that equality on `α` is decidable.
-/

@[expose] public section

assert_not_exists Preorder

namespace List

variable {α : Type*} {l : List α}

/--
Definition of `offDiag` / `offDiag` 的定义

English:
definition offDiag
  signature: (l : List α)
  body: l.zipIdx.flatMap fun (x, n) => map (Prod.mk x) l.eraseIdx n

@[simp]

中文:
定义 offDiag
  签名: (l : 列表 α)
  定义体: l.zipIdx.flatMap fun (x, n) => map (Prod.mk x) l.eraseIdx n

@[simp]

Depends on / 依赖: Prod.mk, eraseIdx, flatMap, l.eraseIdx, l.zipIdx.flatMap, zipIdx
-/
def offDiag (l : List α) : List (α × α) :=
l.zipIdx.flatMap fun (x, n) => map (Prod.mk x) l.eraseIdx n

@[simp]
/--
theorem `offDiag_nil` / 定理 `offDiag_nil`

English:
theorem offDiag_nil
  statement: offDiag ([] : List α) = []
  proof: rfl

中文:
定理 offDiag_nil
  结论: offDiag ([] : 列表 α) = []
  证明: rfl
-/
theorem offDiag_nil : offDiag ([] : List α) = [] := rfl

/--
theorem `offDiag_cons_perm` / 定理 `offDiag_cons_perm`

English:
theorem offDiag_cons_perm
  given: (a : α) (l : List α)
  proof: by
  simp only [offDiag, zipIdx_cons']
  have : map (fun x => (x.fst, a)) l.zipIdx = map (·, a) l := by
    conv_rhs => rw [← zipIdx_map_fst 0 l, map_map, Function.comp_def]
  simp [append_assoc, perm_append_left_iff, flatMap_map,
    ← (map_append_flatMap_perm _ _ _).congr_left, this]

@[simp]

中文:
定理 offDiag_cons_perm
  条件: (a : α) (l : 列表 α)
  证明: by
  simp only [offDiag, zipIdx_cons']
  have : map (fun x => (x.fst, a)) l.zipIdx = map (·, a) l := by
    conv_rhs => rw [← zipIdx_map_fst 0 l, map_map, Function.comp_def]
  simp [append_assoc, perm_append_left_iff, flatMap_map,
    ← (map_append_flatMap_perm _ _ _).congr_left, this]

@[simp]

Depends on / 依赖: Function, Function.comp_def, append_assoc, comp_def, congr_left, conv_rhs, flatMap_map, l.zipIdx, map_append_flatMap_perm, map_map, offDiag, perm_append_left_iff, x.fst, zipIdx, zipIdx_cons, zipIdx_map_fst
-/
theorem offDiag_cons_perm (a : α) (l : List α) :
    offDiag (a :: l) ~ map (a, ·) l ++ map (·, a) l ++ l.offDiag := by
  simp only [offDiag, zipIdx_cons']
  have : map (fun x => (x.fst, a)) l.zipIdx = map (·, a) l := by
    conv_rhs => rw [← zipIdx_map_fst 0 l, map_map, Function.comp_def]
  simp [append_assoc, perm_append_left_iff, flatMap_map,
    ← (map_append_flatMap_perm _ _ _).congr_left, this]

@[simp]
/--
theorem `offDiag_singleton` / 定理 `offDiag_singleton`

English:
theorem offDiag_singleton
  given: (a : α)
  statement: offDiag [a] = []
  proof: rfl

中文:
定理 offDiag_singleton
  条件: (a : α)
  结论: offDiag [a] = []
  证明: rfl
-/
theorem offDiag_singleton (a : α) : offDiag [a] = [] := rfl

/--
theorem `length_offDiag'` / 定理 `length_offDiag'`

English:
theorem length_offDiag'
  given: (l : List α)
  statement: length l.offDiag = length l * (length l - 1)
  proof: by
  have : forall x in l.zipIdx, length (eraseIdx l x.2) = length l - 1 := fun x hx =>
length_eraseIdx_of_lt snd_lt_of_mem_zipIdx hx
  simp [offDiag, map_congr_left this]

@[simp]

中文:
定理 length_offDiag'
  条件: (l : 列表 α)
  结论: length l.offDiag = length l * (length l - 1)
  证明: by
  have : forall x in l.zipIdx, length (eraseIdx l x.2) = length l - 1 := fun x hx =>
length_eraseIdx_of_lt snd_lt_of_mem_zipIdx hx
  simp [offDiag, map_congr_left this]

@[simp]

Depends on / 依赖: eraseIdx, l.zipIdx, length, length_eraseIdx_of_lt, map_congr_left, offDiag, snd_lt_of_mem_zipIdx, zipIdx
-/
theorem length_offDiag' (l : List α) : length l.offDiag = length l * (length l - 1) := by
  have : forall x in l.zipIdx, length (eraseIdx l x.2) = length l - 1 := fun x hx =>
length_eraseIdx_of_lt snd_lt_of_mem_zipIdx hx
  simp [offDiag, map_congr_left this]

@[simp]
/--
theorem `length_offDiag` / 定理 `length_offDiag`

English:
theorem length_offDiag
  given: (l : List α)
  statement: length l.offDiag = length l ^ 2 - length l
  proof: by
  simp [length_offDiag', Nat.mul_sub, Nat.pow_two]

中文:
定理 length_offDiag
  条件: (l : 列表 α)
  结论: length l.offDiag = length l ^ 2 - length l
  证明: by
  simp [length_offDiag', Nat.mul_sub, Nat.pow_two]

Depends on / 依赖: Nat.mul_sub, Nat.pow_two, length_offDiag, mul_sub, pow_two
-/
theorem length_offDiag (l : List α) : length l.offDiag = length l ^ 2 - length l := by
  simp [length_offDiag', Nat.mul_sub, Nat.pow_two]

/--
theorem `mem_offDiag_iff_getElem` / 定理 `mem_offDiag_iff_getElem`

English:
theorem mem_offDiag_iff_getElem
  given: {x : α × α}
  proof: by
  rcases x with ⟨x, y⟩
  simp only [offDiag, exists_mem_zipIdx, mem_eraseIdx_iff_getElem, mem_flatMap, mem_map,
    Nat.zero_add, Prod.ext_iff, ← exists_and_right, exists_and_left, @exists_comm α, and_assoc,
    exists_eq_left', ne_comm]

中文:
定理 mem_offDiag_iff_getElem
  条件: {x : α × α}
  证明: by
  rcases x with ⟨x, y⟩
  simp only [offDiag, exists_mem_zipIdx, mem_eraseIdx_iff_getElem, mem_flatMap, mem_map,
    Nat.zero_add, Prod.ext_iff, ← exists_and_right, exists_and_left, @exists_comm α, and_assoc,
    exists_eq_left', ne_comm]

Depends on / 依赖: Nat.zero_add, Prod.ext_iff, and_assoc, exists_and_left, exists_and_right, exists_comm, exists_eq_left, exists_mem_zipIdx, ext_iff, mem_eraseIdx_iff_getElem, mem_flatMap, mem_map, ne_comm, offDiag, zero_add
-/
theorem mem_offDiag_iff_getElem {x : α × α} :
    x in l.offDiag ↔ exists (i : Nat) (_ : i < l.length) (j : Nat) (_ : j < l.length),
      i != j ∧ l[i] = x.1 ∧ l[j] = x.2 := by
  rcases x with ⟨x, y⟩
  simp only [offDiag, exists_mem_zipIdx, mem_eraseIdx_iff_getElem, mem_flatMap, mem_map,
    Nat.zero_add, Prod.ext_iff, ← exists_and_right, exists_and_left, @exists_comm α, and_assoc,
    exists_eq_left', ne_comm]

/--
theorem `count_offDiag_eq_mul_sub_ite` / 定理 `count_offDiag_eq_mul_sub_ite`

English:
theorem count_offDiag_eq_mul_sub_ite
  given: [DecidableEq α] (l : List α) (a b : α)
  proof: by
  induction l with
  | nil => simp
  | cons c l ihl =>
    have H₁ {x y z : α} : count (x, y) (map (z, ·) l) = if z = x then count y l else 0 := by
      split_ifs with h
      · rw [h, count_map_of_injective l (x, ·) (by simp [Function.Injective])]
      · simp [count_eq_zero, h]
    have H₂ {x y z : α} : count (x, y) (map (·, z) l) = if z = y then count x l else 0 := by
      split_ifs with h
      · rw [h, count_map_of_injective l (·, y) (by simp [Function.Injective])]
      · simp [count_eq_zero, h]
    simp only [(offDiag_cons_perm _ _).count_eq, count_append, ihl, H₁, H₂, count_cons, beq_iff_eq]
    have := Nat.le_mul_self (count c l)
    split_ifs <;> simp_all <;> grind

@[gcongr]

中文:
定理 count_offDiag_eq_mul_sub_ite
  条件: [DecidableEq α] (l : 列表 α) (a b : α)
  证明: by
  induction l with
  | nil => simp
  | cons c l ihl =>
    have H₁ {x y z : α} : count (x, y) (map (z, ·) l) = if z = x then count y l else 0 := by
      split_ifs with h
      · rw [h, count_map_of_injective l (x, ·) (by simp [Function.Injective])]
      · simp [count_eq_zero, h]
    have H₂ {x y z : α} : count (x, y) (map (·, z) l) = if z = y then count x l else 0 := by
      split_ifs with h
      · rw [h, count_map_of_injective l (·, y) (by simp [Function.Injective])]
      · simp [count_eq_zero, h]
    simp only [(offDiag_cons_perm _ _).count_eq, count_append, ihl, H₁, H₂, count_cons, beq_iff_eq]
    have := Nat.le_mul_self (count c l)
    split_ifs <;> simp_all <;> grind

@[gcongr]

Depends on / 依赖: Function, Function.Injective, Injective, count_eq_zero, count_map_of_injective, offDiag_cons_perm, split_ifs
-/
theorem count_offDiag_eq_mul_sub_ite [DecidableEq α] (l : List α) (a b : α) :
    count (a, b) l.offDiag = count a l * count b l - if a = b then count a l else 0 := by
  induction l with
  | nil => simp
  | cons c l ihl =>
    have H₁ {x y z : α} : count (x, y) (map (z, ·) l) = if z = x then count y l else 0 := by
      split_ifs with h
      · rw [h, count_map_of_injective l (x, ·) (by simp [Function.Injective])]
      · simp [count_eq_zero, h]
    have H₂ {x y z : α} : count (x, y) (map (·, z) l) = if z = y then count x l else 0 := by
      split_ifs with h
      · rw [h, count_map_of_injective l (·, y) (by simp [Function.Injective])]
      · simp [count_eq_zero, h]
    simp only [(offDiag_cons_perm _ _).count_eq, count_append, ihl, H₁, H₂, count_cons, beq_iff_eq]
    have := Nat.le_mul_self (count c l)
    split_ifs <;> simp_all <;> grind

@[gcongr]
/--
theorem `Perm.offDiag` / 定理 `Perm.offDiag`

English:
theorem Perm.offDiag
  given: {l₁ l₂ : List α} (h : l₁ ~ l₂)
  statement: l₁.offDiag ~ l₂.offDiag
  proof: by
  classical simp_all [perm_iff_count, count_offDiag_eq_mul_sub_ite]

中文:
定理 置换.offDiag
  条件: {l₁ l₂ : 列表 α} (h : l₁ ~ l₂)
  结论: l₁.offDiag ~ l₂.offDiag
  证明: by
  classical simp_all [perm_iff_count, count_offDiag_eq_mul_sub_ite]
-/
protected theorem Perm.offDiag {l₁ l₂ : List α} (h : l₁ ~ l₂) : l₁.offDiag ~ l₂.offDiag := by
  classical simp_all [perm_iff_count, count_offDiag_eq_mul_sub_ite]

/--
theorem `Nodup.offDiag` / 定理 `Nodup.offDiag`

English:
theorem Nodup.offDiag
  given: (h : l.Nodup)
  statement: l.offDiag.Nodup
  proof: by
  let := Classical.decEq α
  rw [nodup_iff_count_le_one]
  rintro ⟨x, y⟩
  rw [count_offDiag_eq_mul_sub_ite l x y]
  grind

中文:
定理 Nodup.offDiag
  条件: (h : l.Nodup)
  结论: l.offDiag.Nodup
  证明: by
  let := Classical.decEq α
  rw [nodup_iff_count_le_one]
  rintro ⟨x, y⟩
  rw [count_offDiag_eq_mul_sub_ite l x y]
  grind
-/
protected theorem Nodup.offDiag (h : l.Nodup) : l.offDiag.Nodup := by
  let := Classical.decEq α
  rw [nodup_iff_count_le_one]
  rintro ⟨x, y⟩
  rw [count_offDiag_eq_mul_sub_ite l x y]
  grind

/--
theorem `Nodup.of_offDiag` / 定理 `Nodup.of_offDiag`

English:
theorem Nodup.of_offDiag
  given: (h : l.offDiag.Nodup)
  statement: l.Nodup
  proof: by
  let := Classical.decEq α
  simp only [nodup_iff_count_le_one, Prod.forall, count_offDiag_eq_mul_sub_ite] at *
  intro a
  specialize h a a
  contrapose h
  rw [Nat.not_le] at h
  suffices 1 + l.count a < l.count a * l.count a by simpa
  calc
    1 + l.count a < l.count a + l.count a := by simpa
    _ <= l.count a * l.count a := by
      rw [← Nat.two_mul]
      exact Nat.mul_le_mul_right _ h

中文:
定理 Nodup.of_offDiag
  条件: (h : l.offDiag.Nodup)
  结论: l.Nodup
  证明: by
  let := Classical.decEq α
  simp only [nodup_iff_count_le_one, Prod.forall, count_offDiag_eq_mul_sub_ite] at *
  intro a
  specialize h a a
  contrapose h
  rw [Nat.not_le] at h
  suffices 1 + l.count a < l.count a * l.count a by simpa
  calc
    1 + l.count a < l.count a + l.count a := by simpa
    _ <= l.count a * l.count a := by
      rw [← Nat.two_mul]
      exact Nat.mul_le_mul_right _ h
-/
protected theorem Nodup.of_offDiag (h : l.offDiag.Nodup) : l.Nodup := by
  let := Classical.decEq α
  simp only [nodup_iff_count_le_one, Prod.forall, count_offDiag_eq_mul_sub_ite] at *
  intro a
  specialize h a a
  contrapose h
  rw [Nat.not_le] at h
  suffices 1 + l.count a < l.count a * l.count a by simpa
  calc
    1 + l.count a < l.count a + l.count a := by simpa
    _ <= l.count a * l.count a := by
      rw [← Nat.two_mul]
      exact Nat.mul_le_mul_right _ h

/-- `List.offDiag l` has no duplicates iff the original list has no duplicates. -/
@[simp]
/--
theorem `nodup_offDiag` / 定理 `nodup_offDiag`

English:
theorem nodup_offDiag
  statement: l.offDiag.Nodup ↔ l.Nodup
  proof: ⟨.of_offDiag, .offDiag⟩

中文:
定理 nodup_offDiag
  结论: l.offDiag.Nodup ↔ l.Nodup
  证明: ⟨.of_offDiag, .offDiag⟩

Depends on / 依赖: of_offDiag, offDiag
-/
theorem nodup_offDiag : l.offDiag.Nodup ↔ l.Nodup := ⟨.of_offDiag, .offDiag⟩

/--
theorem `Nodup.mem_offDiag` / 定理 `Nodup.mem_offDiag`

English:
theorem Nodup.mem_offDiag
  given: (h : l.Nodup) {x : α × α}
  proof: by
  rcases x with ⟨x, y⟩
  simp_rw [mem_offDiag_iff_getElem, mem_iff_getElem, Ne]
  constructor
  · rintro ⟨i, hi, j, hj, hne, rfl, rfl⟩
    exact ⟨⟨i, hi, rfl⟩, ⟨j, hj, rfl⟩, mt h.getElem_inj_iff.1 hne⟩
  · rintro ⟨⟨i, hi, rfl⟩, ⟨j, hj, rfl⟩, hne⟩
    exact ⟨i, hi, j, hj, mt h.getElem_inj_iff.2 hne, rfl, rfl⟩

中文:
定理 Nodup.mem_offDiag
  条件: (h : l.Nodup) {x : α × α}
  证明: by
  rcases x with ⟨x, y⟩
  simp_rw [mem_offDiag_iff_getElem, mem_iff_getElem, Ne]
  constructor
  · rintro ⟨i, hi, j, hj, hne, rfl, rfl⟩
    exact ⟨⟨i, hi, rfl⟩, ⟨j, hj, rfl⟩, mt h.getElem_inj_iff.1 hne⟩
  · rintro ⟨⟨i, hi, rfl⟩, ⟨j, hj, rfl⟩, hne⟩
    exact ⟨i, hi, j, hj, mt h.getElem_inj_iff.2 hne, rfl, rfl⟩

Depends on / 依赖: getElem_inj_iff, h.getElem_inj_iff, mem_iff_getElem, mem_offDiag_iff_getElem, simp_rw
-/
theorem Nodup.mem_offDiag (h : l.Nodup) {x : α × α} :
    x in l.offDiag ↔ x.1 in l ∧ x.2 in l ∧ x.1 != x.2 := by
  rcases x with ⟨x, y⟩
  simp_rw [mem_offDiag_iff_getElem, mem_iff_getElem, Ne]
  constructor
  · rintro ⟨i, hi, j, hj, hne, rfl, rfl⟩
    exact ⟨⟨i, hi, rfl⟩, ⟨j, hj, rfl⟩, mt h.getElem_inj_iff.1 hne⟩
  · rintro ⟨⟨i, hi, rfl⟩, ⟨j, hj, rfl⟩, hne⟩
    exact ⟨i, hi, j, hj, mt h.getElem_inj_iff.2 hne, rfl, rfl⟩

/--
theorem `map_prodMap_offDiag` / 定理 `map_prodMap_offDiag`

English:
theorem map_prodMap_offDiag
  given: {β : Type*} (f : α -> β) (l : List α)
  proof: by
  simp [offDiag, map_flatMap, zipIdx_map, flatMap_map, eraseIdx_map, Function.comp_def]

中文:
定理 map_prodMap_offDiag
  条件: {β : 类型} (f : α -> β) (l : 列表 α)
  证明: by
  simp [offDiag, map_flatMap, zipIdx_map, flatMap_map, eraseIdx_map, Function.comp_def]

Depends on / 依赖: Function, Function.comp_def, comp_def, eraseIdx_map, flatMap_map, map_flatMap, offDiag, zipIdx_map
-/
theorem map_prodMap_offDiag {β : Type*} (f : α -> β) (l : List α) :
    map (Prod.map f f) l.offDiag = (map f l).offDiag := by
  simp [offDiag, map_flatMap, zipIdx_map, flatMap_map, eraseIdx_map, Function.comp_def]

end List
