/-
Copyright (c) 2022 Dagur Asgeirsson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dagur Asgeirsson, Leonardo de Moura
-/
module

public import Mathlib.Order.BooleanAlgebra.Set

/-!
# Indicator function valued in bool

See also `Set.indicator` and `Set.piecewise`.
-/

@[expose] public section

assert_not_exists RelIso

open Bool

namespace Set

variable {α : Type*} (s : Set α)

/--
Definition of `boolIndicator` / `boolIndicator` 的定义

English:
definition boolIndicator
  signature: (x : α)
  body: @ite _ (x in s) (Classical.propDecidable _) true false

中文:
定义 boolIndicator
  签名: (x : α)
  定义体: @ite _ (x in s) (Classical.propDecidable _) true false

Depends on / 依赖: Classical, Classical.propDecidable, propDecidable
-/
noncomputable def boolIndicator (x : α) :=
  @ite _ (x in s) (Classical.propDecidable _) true false

/--
theorem `mem_iff_boolIndicator` / 定理 `mem_iff_boolIndicator`

English:
theorem mem_iff_boolIndicator
  given: (x : α)
  statement: x in s ↔ s.boolIndicator x = true
  proof: by
  unfold boolIndicator
  split_ifs with h <;> simp [h]

中文:
定理 mem_iff_boolIndicator
  条件: (x : α)
  结论: x in s ↔ s.boolIndicator x = true
  证明: by
  unfold boolIndicator
  split_ifs with h <;> simp [h]

Depends on / 依赖: boolIndicator, split_ifs
-/
theorem mem_iff_boolIndicator (x : α) : x in s ↔ s.boolIndicator x = true := by
  unfold boolIndicator
  split_ifs with h <;> simp [h]

/--
theorem `notMem_iff_boolIndicator` / 定理 `notMem_iff_boolIndicator`

English:
theorem notMem_iff_boolIndicator
  given: (x : α)
  statement: x ∉ s ↔ s.boolIndicator x = false
  proof: by
  unfold boolIndicator
  split_ifs with h <;> simp [h]

中文:
定理 notMem_iff_boolIndicator
  条件: (x : α)
  结论: x ∉ s ↔ s.boolIndicator x = false
  证明: by
  unfold boolIndicator
  split_ifs with h <;> simp [h]

Depends on / 依赖: boolIndicator, split_ifs
-/
theorem notMem_iff_boolIndicator (x : α) : x ∉ s ↔ s.boolIndicator x = false := by
  unfold boolIndicator
  split_ifs with h <;> simp [h]

/--
theorem `preimage_boolIndicator_true` / 定理 `preimage_boolIndicator_true`

English:
theorem preimage_boolIndicator_true
  statement: s.boolIndicator ⁻¹' {true} = s
  proof: ext fun x => (s.mem_iff_boolIndicator x).symm

中文:
定理 preimage_boolIndicator_true
  结论: s.boolIndicator ⁻¹' {true} = s
  证明: ext fun x => (s.mem_iff_boolIndicator x).symm

Depends on / 依赖: mem_iff_boolIndicator, s.mem_iff_boolIndicator
-/
theorem preimage_boolIndicator_true : s.boolIndicator ⁻¹' {true} = s :=
  ext fun x => (s.mem_iff_boolIndicator x).symm

/--
theorem `preimage_boolIndicator_false` / 定理 `preimage_boolIndicator_false`

English:
theorem preimage_boolIndicator_false
  statement: s.boolIndicator ⁻¹' {false} = sᶜ
  proof: ext fun x => (s.notMem_iff_boolIndicator x).symm

中文:
定理 preimage_boolIndicator_false
  结论: s.boolIndicator ⁻¹' {false} = sᶜ
  证明: ext fun x => (s.notMem_iff_boolIndicator x).symm

Depends on / 依赖: notMem_iff_boolIndicator, s.notMem_iff_boolIndicator
-/
theorem preimage_boolIndicator_false : s.boolIndicator ⁻¹' {false} = sᶜ :=
  ext fun x => (s.notMem_iff_boolIndicator x).symm

open scoped Classical in
/--
theorem `preimage_boolIndicator_eq_union` / 定理 `preimage_boolIndicator_eq_union`

English:
theorem preimage_boolIndicator_eq_union
  given: (t : Set Bool)
  proof: by
  ext x
  simp only [boolIndicator, mem_preimage]
  split_ifs <;> simp [*]

中文:
定理 preimage_boolIndicator_eq_union
  条件: (t : Set 布尔)
  证明: by
  ext x
  simp only [boolIndicator, mem_preimage]
  split_ifs <;> simp [*]

Depends on / 依赖: boolIndicator, mem_preimage, split_ifs
-/
theorem preimage_boolIndicator_eq_union (t : Set Bool) :
    s.boolIndicator ⁻¹' t = (if true in t then s else ∅) union if false in t then sᶜ else ∅ := by
  ext x
  simp only [boolIndicator, mem_preimage]
  split_ifs <;> simp [*]

/--
theorem `preimage_boolIndicator` / 定理 `preimage_boolIndicator`

English:
theorem preimage_boolIndicator
  given: (t : Set Bool)
  proof: by
  simp only [preimage_boolIndicator_eq_union]
  split_ifs <;> simp [s.union_compl_self]

中文:
定理 preimage_boolIndicator
  条件: (t : Set 布尔)
  证明: by
  simp only [preimage_boolIndicator_eq_union]
  split_ifs <;> simp [s.union_compl_self]

Depends on / 依赖: preimage_boolIndicator_eq_union, s.union_compl_self, split_ifs, union_compl_self
-/
theorem preimage_boolIndicator (t : Set Bool) :
    s.boolIndicator ⁻¹' t = univ ∨
      s.boolIndicator ⁻¹' t = s ∨ s.boolIndicator ⁻¹' t = sᶜ ∨ s.boolIndicator ⁻¹' t = ∅ := by
  simp only [preimage_boolIndicator_eq_union]
  split_ifs <;> simp [s.union_compl_self]

end Set
