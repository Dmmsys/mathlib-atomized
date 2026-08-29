/-
Copyright (c) 2017 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Yakov Pechersky, Eric Wieser
-/
module

public import Mathlib.Data.List.Basic

/-!
# Properties of `List.enum`
-/

public section

namespace List

variable {α : Type*}

/--
theorem `forall_mem_zipIdx` / 定理 `forall_mem_zipIdx`

English:
theorem forall_mem_zipIdx
  given: {l : List α} {n : Nat} {p : α × Nat -> Prop}
  proof: by
  simp only [forall_mem_iff_getElem, getElem_zipIdx, length_zipIdx]

中文:
定理 forall_mem_zipIdx
  条件: {l : List α} {n : 自然数} {p : α × 自然数 -> 命题}
  证明: by
  simp only [forall_mem_iff_getElem, getElem_zipIdx, length_zipIdx]

Depends on / 依赖: forall_mem_iff_getElem, getElem_zipIdx, length_zipIdx
-/
theorem forall_mem_zipIdx {l : List α} {n : Nat} {p : α × Nat -> Prop} :
    (forall x in l.zipIdx n, p x) ↔ forall (i : Nat) (_ : i < length l), p (l[i], n + i) := by
  simp only [forall_mem_iff_getElem, getElem_zipIdx, length_zipIdx]

/--
theorem `forall_mem_zipIdx'` / 定理 `forall_mem_zipIdx'`

English:
theorem forall_mem_zipIdx'
  given: {l : List α} {p : α × Nat -> Prop}
  proof: forall_mem_zipIdx.trans by simp

中文:
定理 forall_mem_zipIdx'
  条件: {l : List α} {p : α × 自然数 -> 命题}
  证明: forall_mem_zipIdx.trans by simp

Depends on / 依赖: forall_mem_zipIdx, forall_mem_zipIdx.trans
-/
theorem forall_mem_zipIdx' {l : List α} {p : α × Nat -> Prop} :
    (forall x in l.zipIdx, p x) ↔ forall (i : Nat) (_ : i < length l), p (l[i], i) :=
forall_mem_zipIdx.trans by simp

/--
theorem `exists_mem_zipIdx` / 定理 `exists_mem_zipIdx`

English:
theorem exists_mem_zipIdx
  given: {l : List α} {n : Nat} {p : α × Nat -> Prop}
  proof: by
  simp only [exists_mem_iff_getElem, getElem_zipIdx, length_zipIdx]

中文:
定理 exists_mem_zipIdx
  条件: {l : List α} {n : 自然数} {p : α × 自然数 -> 命题}
  证明: by
  simp only [exists_mem_iff_getElem, getElem_zipIdx, length_zipIdx]

Depends on / 依赖: exists_mem_iff_getElem, getElem_zipIdx, length_zipIdx
-/
theorem exists_mem_zipIdx {l : List α} {n : Nat} {p : α × Nat -> Prop} :
    (exists x in l.zipIdx n, p x) ↔ exists (i : Nat) (_ : i < length l), p (l[i], n + i) := by
  simp only [exists_mem_iff_getElem, getElem_zipIdx, length_zipIdx]

/--
theorem `exists_mem_zipIdx'` / 定理 `exists_mem_zipIdx'`

English:
theorem exists_mem_zipIdx'
  given: {l : List α} {p : α × Nat -> Prop}
  proof: exists_mem_zipIdx.trans by simp

中文:
定理 exists_mem_zipIdx'
  条件: {l : List α} {p : α × 自然数 -> 命题}
  证明: exists_mem_zipIdx.trans by simp

Depends on / 依赖: exists_mem_zipIdx, exists_mem_zipIdx.trans
-/
theorem exists_mem_zipIdx' {l : List α} {p : α × Nat -> Prop} :
    (exists x in l.zipIdx, p x) ↔ exists (i : Nat) (_ : i < length l), p (l[i], i) :=
exists_mem_zipIdx.trans by simp

end List
