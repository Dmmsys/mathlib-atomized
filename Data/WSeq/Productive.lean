/-
Copyright (c) 2017 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
module

public import Mathlib.Data.WSeq.Relation

/-!
# Productive weak sequences

This file defines the property of a weak sequence being productive as never stalling – the next
output always comes after a finite time. Given a productive weak sequence, a regular sequence
(`Seq`) can be derived from it using `toSeq`.
-/

@[expose] public section

universe u

namespace Stream'.WSeq

variable {α : Type u}

open Function

/--
Definition of `Productive` / `Productive` 的定义

English:
class Productive
  parameters: (s : WSeq α)
  axioms and operations (1):
    - get?_terminates : forall n, (get? s n).Terminates

中文:
类 Productive
  参数: (s : WSeq α)
  公理与运算 (1 个):
    - get?_terminates : 对任意 n, (get? s n).Terminates
-/
class Productive (s : WSeq α) : Prop where
  get?_terminates : forall n, (get? s n).Terminates

/--
theorem `productive_iff` / 定理 `productive_iff`

English:
theorem productive_iff
  given: (s : WSeq α)
  statement: Productive s ↔ forall n, (get? s n).Terminates
  proof: ⟨fun h => h.1, fun h => ⟨h⟩⟩

中文:
定理 productive_iff
  条件: (s : WSeq α)
  结论: Productive s ↔ 对任意 n, (get? s n).Terminates
  证明: ⟨fun h => h.1, fun h => ⟨h⟩⟩
-/
theorem productive_iff (s : WSeq α) : Productive s ↔ forall n, (get? s n).Terminates :=
  ⟨fun h => h.1, fun h => ⟨h⟩⟩

/--
Instance `get?_terminates` / 实例 `get?_terminates`

English:
instance get?_terminates
  signature: (s : WSeq α) [h : Productive s]
  body: h.get?_terminates

中文:
实例 get?_terminates
  签名: (s : WSeq α) [h : Productive s]
  定义体: h.get?_terminates
-/
instance get?_terminates (s : WSeq α) [h : Productive s] : forall n, (get? s n).Terminates :=
  h.get?_terminates

/--
Instance `head_terminates` / 实例 `head_terminates`

English:
instance head_terminates
  signature: (s : WSeq α) [Productive s]
  body: s.get?_terminates 0

中文:
实例 head_terminates
  签名: (s : WSeq α) [Productive s]
  定义体: s.get?_terminates 0

Depends on / 依赖: _terminates, s.get
-/
instance head_terminates (s : WSeq α) [Productive s] : (head s).Terminates :=
  s.get?_terminates 0

/--
Instance `productive_tail` / 实例 `productive_tail`

English:
instance productive_tail
  signature: (s : WSeq α) [Productive s]
  body: ⟨fun n => by rw [get?_tail]; infer_instance⟩

中文:
实例 productive_tail
  签名: (s : WSeq α) [Productive s]
  定义体: ⟨fun n => by rw [get?_tail]; infer_instance⟩

Depends on / 依赖: _tail, infer_instance
-/
instance productive_tail (s : WSeq α) [Productive s] : Productive (tail s) :=
  ⟨fun n => by rw [get?_tail]; infer_instance⟩

/--
Instance `productive_dropn` / 实例 `productive_dropn`

English:
instance productive_dropn
  signature: (s : WSeq α) [Productive s] (n)
  body: ⟨fun m => by rw [← get?_add]; infer_instance⟩

中文:
实例 productive_dropn
  签名: (s : WSeq α) [Productive s] (n)
  定义体: ⟨fun m => by rw [← get?_add]; infer_instance⟩

Depends on / 依赖: _add, infer_instance
-/
instance productive_dropn (s : WSeq α) [Productive s] (n) : Productive (drop s n) :=
  ⟨fun m => by rw [← get?_add]; infer_instance⟩

open Computation

/--
Instance `productive_ofSeq` / 实例 `productive_ofSeq`

English:
instance productive_ofSeq
  signature: (s : Seq α)
  body: ⟨fun n => by rw [get?_ofSeq]; infer_instance⟩

中文:
实例 productive_ofSeq
  签名: (s : 序列 α)
  定义体: ⟨fun n => by rw [get?_ofSeq]; infer_instance⟩

Depends on / 依赖: _ofSeq, infer_instance
-/
instance productive_ofSeq (s : Seq α) : Productive (ofSeq s) :=
  ⟨fun n => by rw [get?_ofSeq]; infer_instance⟩

/--
theorem `productive_congr` / 定理 `productive_congr`

English:
theorem productive_congr
  given: {s t : WSeq α} (h : s ~ʷ t)
  statement: Productive s ↔ Productive t
  proof: by
simp only [productive_iff]; exact forall_congr' fun n => terminates_congr get?_congr h _

中文:
定理 productive_congr
  条件: {s t : WSeq α} (h : s ~ʷ t)
  结论: Productive s ↔ Productive t
  证明: by
simp only [productive_iff]; exact forall_congr' fun n => terminates_congr get?_congr h _

Depends on / 依赖: _congr, forall_congr, productive_iff, terminates_congr
-/
theorem productive_congr {s t : WSeq α} (h : s ~ʷ t) : Productive s ↔ Productive t := by
simp only [productive_iff]; exact forall_congr' fun n => terminates_congr get?_congr h _

/--
Definition of `toSeq` / `toSeq` 的定义

English:
definition toSeq
  signature: (s : WSeq α) [Productive s]
  body: ⟨fun n => (get? s n).get,
   fun {n} h => by
    cases e : Computation.get (get? s (n + 1))
    · assumption
    have := Computation.mem_of_get_eq _ e
    simp only [get?] at this h
    obtain ⟨a', h'⟩ := head_some_of_head_tail_some this
    have := mem_unique h' (@Computation.mem_of_get_eq _ _ _ _ h)
    contradiction⟩

中文:
定义 toSeq
  签名: (s : WSeq α) [Productive s]
  定义体: ⟨fun n => (get? s n).get,
   fun {n} h => by
    cases e : Computation.get (get? s (n + 1))
    · assumption
    have := Computation.mem_of_get_eq _ e
    simp only [get?] at this h
    obtain ⟨a', h'⟩ := head_some_of_head_tail_some this
    have := mem_unique h' (@Computation.mem_of_get_eq _ _ _ _ h)
    contradiction⟩

Depends on / 依赖: Computation, Computation.get, Computation.mem_of_get_eq, head_some_of_head_tail_some, mem_of_get_eq, mem_unique
-/
def toSeq (s : WSeq α) [Productive s] : Seq α :=
  ⟨fun n => (get? s n).get,
   fun {n} h => by
    cases e : Computation.get (get? s (n + 1))
    · assumption
    have := Computation.mem_of_get_eq _ e
    simp only [get?] at this h
    obtain ⟨a', h'⟩ := head_some_of_head_tail_some this
    have := mem_unique h' (@Computation.mem_of_get_eq _ _ _ _ h)
    contradiction⟩

/--
theorem `toSeq_ofSeq` / 定理 `toSeq_ofSeq`

English:
theorem toSeq_ofSeq
  given: (s : Seq α)
  statement: toSeq (ofSeq s) = s
  proof: by
  apply Subtype.ext; funext n
  dsimp [toSeq]; apply get_eq_of_mem
  rw [get?_ofSeq]; apply ret_mem

中文:
定理 toSeq_ofSeq
  条件: (s : 序列 α)
  结论: toSeq (ofSeq s) = s
  证明: by
  apply Subtype.ext; funext n
  dsimp [toSeq]; apply get_eq_of_mem
  rw [get?_ofSeq]; apply ret_mem

Depends on / 依赖: Subtype, Subtype.ext, _ofSeq, get_eq_of_mem, ret_mem
-/
theorem toSeq_ofSeq (s : Seq α) : toSeq (ofSeq s) = s := by
  apply Subtype.ext; funext n
  dsimp [toSeq]; apply get_eq_of_mem
  rw [get?_ofSeq]; apply ret_mem

end Stream'.WSeq
