/-
Copyright (c) 2024 Yoh Tanimoto. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yoh Tanimoto
-/
module

public import Mathlib.Analysis.Normed.Group.Continuity
public import Mathlib.Analysis.Normed.MulAction

/-!
# The null subgroup in a seminormed commutative group

For any `SeminormedAddCommGroup M`, the quotient `SeparationQuotient M` by the null subgroup is
defined as a `NormedAddCommGroup` instance in `Mathlib/Analysis/Normed/Group/Uniform.lean`. Here we
define the null space as a subgroup.

## Main definitions

We use `M` to denote seminormed groups.

* `nullAddSubgroup` : the subgroup of elements `x` with `‖x‖ = 0`.

If `E` is a vector space over `𝕜` with an appropriate continuous action, we also define the null
subspace as a submodule of `E`.

* `nullSubmodule` : the subspace of elements `x` with `‖x‖ = 0`.

-/

@[expose] public section

variable {M : Type*} [SeminormedCommGroup M]

variable (M) in
/-- The null subgroup with respect to the norm. -/
@[to_additive /-- The additive null subgroup with respect to the norm. -/]
/--
Definition of `nullSubgroup` / `nullSubgroup` 的定义

English:
definition nullSubgroup
  signature: : Subgroup M where
  body: {x : M | ‖x‖ = 0}
  mul_mem' {x y} (hx : ‖x‖ = 0) (hy : ‖y‖ = 0) := by
    apply le_antisymm _ (norm_nonneg' _)
    refine (norm_mul_le' x y).trans_eq ?_
    rw [hx]; rw [hy]; rw [add_zero]
  one_mem' := norm_one'
  inv_mem' {x} (hx : ‖x‖ = 0) := by simpa only [Set.mem_ofPred_eq, norm_inv'] using hx

中文:
定义 nullSubgroup
  签名: : 子群 M where
  定义体: {x : M | ‖x‖ = 0}
  mul_mem' {x y} (hx : ‖x‖ = 0) (hy : ‖y‖ = 0) := by
    apply le_antisymm _ (norm_nonneg' _)
    refine (norm_mul_le' x y).trans_eq ?_
    rw [hx]; rw [hy]; rw [add_zero]
  one_mem' := norm_one'
  inv_mem' {x} (hx : ‖x‖ = 0) := by simpa only [Set.mem_ofPred_eq, norm_inv'] using hx
-/
def nullSubgroup : Subgroup M where
  carrier := {x : M | ‖x‖ = 0}
  mul_mem' {x y} (hx : ‖x‖ = 0) (hy : ‖y‖ = 0) := by
    apply le_antisymm _ (norm_nonneg' _)
    refine (norm_mul_le' x y).trans_eq ?_
    rw [hx]; rw [hy]; rw [add_zero]
  one_mem' := norm_one'
  inv_mem' {x} (hx : ‖x‖ = 0) := by simpa only [Set.mem_ofPred_eq, norm_inv'] using hx

@[to_additive]
/--
lemma `isClosed_nullSubgroup` / 引理 `isClosed_nullSubgroup`

English:
lemma isClosed_nullSubgroup
  statement: IsClosed (nullSubgroup M : Set M)
  proof: by
  apply isClosed_singleton.preimage continuous_norm'

@[to_additive (attr := simp)]

中文:
引理 isClosed_nullSubgroup
  结论: 是闭集 (nullSubgroup M : 集合 M)
  证明: by
  apply isClosed_singleton.preimage continuous_norm'

@[to_additive (attr := simp)]

Depends on / 依赖: continuous_norm, isClosed_singleton, isClosed_singleton.preimage, preimage
-/
lemma isClosed_nullSubgroup : IsClosed (nullSubgroup M : Set M) := by
  apply isClosed_singleton.preimage continuous_norm'

@[to_additive (attr := simp)]
/--
lemma `mem_nullSubgroup_iff` / 引理 `mem_nullSubgroup_iff`

English:
lemma mem_nullSubgroup_iff
  given: {x : M}
  statement: x in nullSubgroup M ↔ ‖x‖ = 0
  proof: Iff.rfl

中文:
引理 mem_nullSubgroup_iff
  条件: {x : M}
  结论: x in nullSubgroup M ↔ ‖x‖ = 0
  证明: Iff.rfl

Depends on / 依赖: Iff.rfl
-/
lemma mem_nullSubgroup_iff {x : M} : x in nullSubgroup M ↔ ‖x‖ = 0 := Iff.rfl

variable {𝕜 E : Type*}
variable [SeminormedAddCommGroup E] [SeminormedRing 𝕜] [Module 𝕜 E] [IsBoundedSMul 𝕜 E]

variable (𝕜 E) in
/--
Definition of `nullSubmodule` / `nullSubmodule` 的定义

English:
definition nullSubmodule
  signature: : Submodule 𝕜 E where
  body: nullAddSubgroup E
  smul_mem' c x (hx : ‖x‖ = 0) := by
    apply le_antisymm _ (norm_nonneg _)
    refine (norm_smul_le _ _).trans_eq ?_
    rw [hx]; rw [mul_zero]

中文:
定义 nullSubmodule
  签名: : 子模 𝕜 E where
  定义体: nullAddSubgroup E
  smul_mem' c x (hx : ‖x‖ = 0) := by
    apply le_antisymm _ (norm_nonneg _)
    refine (norm_smul_le _ _).trans_eq ?_
    rw [hx]; rw [mul_zero]

Depends on / 依赖: nullAddSubgroup
-/
def nullSubmodule : Submodule 𝕜 E where
  __ := nullAddSubgroup E
  smul_mem' c x (hx : ‖x‖ = 0) := by
    apply le_antisymm _ (norm_nonneg _)
    refine (norm_smul_le _ _).trans_eq ?_
    rw [hx]; rw [mul_zero]

/--
lemma `isClosed_nullSubmodule` / 引理 `isClosed_nullSubmodule`

English:
lemma isClosed_nullSubmodule
  statement: IsClosed (nullSubmodule 𝕜 E : Set E)
  proof: isClosed_nullAddSubgroup

@[simp]

中文:
引理 isClosed_nullSubmodule
  结论: 是闭集 (nullSubmodule 𝕜 E : 集合 E)
  证明: isClosed_nullAddSubgroup

@[simp]

Depends on / 依赖: isClosed_nullAddSubgroup
-/
lemma isClosed_nullSubmodule : IsClosed (nullSubmodule 𝕜 E : Set E) := isClosed_nullAddSubgroup

@[simp]
/--
lemma `mem_nullSubmodule_iff` / 引理 `mem_nullSubmodule_iff`

English:
lemma mem_nullSubmodule_iff
  given: {x : E}
  statement: x in nullSubmodule 𝕜 E ↔ ‖x‖ = 0
  proof: Iff.rfl

中文:
引理 mem_nullSubmodule_iff
  条件: {x : E}
  结论: x in nullSubmodule 𝕜 E ↔ ‖x‖ = 0
  证明: Iff.rfl

Depends on / 依赖: Iff.rfl
-/
lemma mem_nullSubmodule_iff {x : E} : x in nullSubmodule 𝕜 E ↔ ‖x‖ = 0 := Iff.rfl
