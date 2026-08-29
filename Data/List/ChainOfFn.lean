/-
Copyright (c) 2024 Joseph Myers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Myers
-/
module

public import Batteries.Data.List.Lemmas
public import Mathlib.Tactic.Common
public import Mathlib.Tactic.Finiteness.Attr
public import Mathlib.Tactic.ToDual
public import Mathlib.Util.CompileInductive

/-!
# Lemmas about `IsChain` and `ofFn`

This file provides lemmas involving both `List.IsChain` and `List.ofFn`.
-/

public section

open Nat

namespace List

/--
lemma `isChain_ofFn` / 引理 `isChain_ofFn`

English:
lemma isChain_ofFn
  given: {α : Type*} {n : Nat} {f : Fin n -> α} {r : α -> α -> Prop}
  proof: by
  simp_rw [isChain_iff_getElem, List.getElem_ofFn, length_ofFn]

中文:
引理 isChain_ofFn
  条件: {α : 类型} {n : 自然数} {f : 有限集 n -> α} {r : α -> α -> 命题}
  证明: by
  simp_rw [isChain_iff_getElem, List.getElem_ofFn, length_ofFn]

Depends on / 依赖: List.getElem_ofFn, getElem_ofFn, isChain_iff_getElem, length_ofFn, simp_rw
-/
lemma isChain_ofFn {α : Type*} {n : Nat} {f : Fin n -> α} {r : α -> α -> Prop} :
    (ofFn f).IsChain r ↔ forall (i) (hi : i + 1 < n), r (f ⟨i, lt_of_succ_lt hi⟩) (f ⟨i + 1, hi⟩) := by
  simp_rw [isChain_iff_getElem, List.getElem_ofFn, length_ofFn]

end List
