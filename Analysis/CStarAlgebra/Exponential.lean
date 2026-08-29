/-
Copyright (c) 2022 Jireh Loreaux. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jireh Loreaux
-/
module

public import Mathlib.Analysis.Normed.Algebra.Exponential

/-! # The exponential map from selfadjoint to unitary
In this file, we establish various properties related to the map
`fun a ↦ NormedSpace.exp ℂ A (I • a)` between the subtypes `selfAdjoint A` and `unitary A`.

## TODO

* Show that any exponential unitary is path-connected in `unitary A` to `1 : unitary A`.
* Prove any unitary whose distance to `1 : unitary A` is less than `1` can be expressed as an
  exponential unitary.
* A unitary is in the path component of `1` if and only if it is a finite product of exponential
  unitaries.
-/

@[expose] public section

open NormedSpace -- For `NormedSpace.exp`.

section Star

variable {A : Type*} [NormedRing A] [NormedAlgebra Complex A] [StarRing A] [ContinuousStar A]
  [CompleteSpace A] [StarModule Complex A]

open Complex

/-- The map from the selfadjoint real subspace to the unitary group. This map only makes sense
over ℂ. -/
@[simps]
/--
Definition of `selfAdjoint.expUnitary` / `selfAdjoint.expUnitary` 的定义

English:
definition selfAdjoint.expUnitary
  signature: (a : selfAdjoint A)
  body: ⟨exp ((I • a.val) : A),
      let +nondep : NormedAlgebra Rat A := .restrictScalars Rat Complex A
      exp_mem_unitary_of_mem_skewAdjoint (a.prop.smul_mem_skewAdjoint conj_I)⟩

中文:
定义 selfAdjoint.expUnitary
  签名: (a : selfAdjoint A)
  定义体: ⟨exp ((I • a.val) : A),
      let +nondep : NormedAlgebra Rat A := .restrictScalars Rat Complex A
      exp_mem_unitary_of_mem_skewAdjoint (a.prop.smul_mem_skewAdjoint conj_I)⟩

Depends on / 依赖: NormedAlgebra, a.prop.smul_mem_skewAdjoint, a.val, conj_I, exp_mem_unitary_of_mem_skewAdjoint, nondep, restrictScalars, smul_mem_skewAdjoint
-/
noncomputable def selfAdjoint.expUnitary (a : selfAdjoint A) : unitary A :=
  ⟨exp ((I • a.val) : A),
      let +nondep : NormedAlgebra Rat A := .restrictScalars Rat Complex A
      exp_mem_unitary_of_mem_skewAdjoint (a.prop.smul_mem_skewAdjoint conj_I)⟩

open selfAdjoint

@[simp]
/--
lemma `selfAdjoint.expUnitary_zero` / 引理 `selfAdjoint.expUnitary_zero`

English:
lemma selfAdjoint.expUnitary_zero
  statement: expUnitary (0 : selfAdjoint A) = 1
  proof: by
  ext
  simp

@[fun_prop]

中文:
引理 selfAdjoint.expUnitary_zero
  结论: expUnitary (0 : selfAdjoint A) = 1
  证明: by
  ext
  simp

@[fun_prop]
-/
lemma selfAdjoint.expUnitary_zero : expUnitary (0 : selfAdjoint A) = 1 := by
  ext
  simp

@[fun_prop]
/--
lemma `selfAdjoint.continuous_expUnitary` / 引理 `selfAdjoint.continuous_expUnitary`

English:
lemma selfAdjoint.continuous_expUnitary
  statement: Continuous (expUnitary : selfAdjoint A -> unitary A)
  proof: by
  simp only [continuous_induced_rng, Function.comp_def, selfAdjoint.expUnitary_coe]
  let +nondep : NormedAlgebra Rat A := NormedAlgebra.restrictScalars Rat Complex A
  fun_prop

中文:
引理 selfAdjoint.continuous_expUnitary
  结论: Continuous (expUnitary : selfAdjoint A -> unitary A)
  证明: by
  simp only [continuous_induced_rng, Function.comp_def, selfAdjoint.expUnitary_coe]
  let +nondep : NormedAlgebra Rat A := NormedAlgebra.restrictScalars Rat Complex A
  fun_prop

Depends on / 依赖: Function, Function.comp_def, NormedAlgebra, NormedAlgebra.restrictScalars, comp_def, continuous_induced_rng, expUnitary_coe, fun_prop, nondep, restrictScalars, selfAdjoint, selfAdjoint.expUnitary_coe
-/
lemma selfAdjoint.continuous_expUnitary : Continuous (expUnitary : selfAdjoint A -> unitary A) := by
  simp only [continuous_induced_rng, Function.comp_def, selfAdjoint.expUnitary_coe]
  let +nondep : NormedAlgebra Rat A := NormedAlgebra.restrictScalars Rat Complex A
  fun_prop

/--
theorem `Commute.expUnitary_add` / 定理 `Commute.expUnitary_add`

English:
theorem Commute.expUnitary_add
  given: {a b : selfAdjoint A} (h : Commute (a : A) (b : A))
  proof: by
  let +nondep : NormedAlgebra Rat A := .restrictScalars Rat Complex A
  simpa only [Subtype.ext_iff, expUnitary_coe, AddSubgroup.coe_add, smul_add] using!
    exp_add_of_commute ((h.smul_left I).smul_right I)

中文:
定理 Commute.expUnitary_add
  条件: {a b : selfAdjoint A} (h : Commute (a : A) (b : A))
  证明: by
  let +nondep : NormedAlgebra Rat A := .restrictScalars Rat Complex A
  simpa only [Subtype.ext_iff, expUnitary_coe, AddSubgroup.coe_add, smul_add] using!
    exp_add_of_commute ((h.smul_left I).smul_right I)

Depends on / 依赖: AddSubgroup, AddSubgroup.coe_add, NormedAlgebra, Subtype, Subtype.ext_iff, coe_add, expUnitary_coe, exp_add_of_commute, ext_iff, h.smul_left, nondep, restrictScalars, smul_add, smul_left, smul_right
-/
theorem Commute.expUnitary_add {a b : selfAdjoint A} (h : Commute (a : A) (b : A)) :
    expUnitary (a + b) = expUnitary a * expUnitary b := by
  let +nondep : NormedAlgebra Rat A := .restrictScalars Rat Complex A
  simpa only [Subtype.ext_iff, expUnitary_coe, AddSubgroup.coe_add, smul_add] using!
    exp_add_of_commute ((h.smul_left I).smul_right I)

/--
theorem `Commute.expUnitary` / 定理 `Commute.expUnitary`

English:
theorem Commute.expUnitary
  given: {a b : selfAdjoint A} (h : Commute (a : A) (b : A))
  proof: by
  rw [Commute]; rw [SemiconjBy]; rw [← h.expUnitary_add]; rw [← h.symm.expUnitary_add]; rw [add_comm]

中文:
定理 Commute.expUnitary
  条件: {a b : selfAdjoint A} (h : Commute (a : A) (b : A))
  证明: by
  rw [Commute]; rw [SemiconjBy]; rw [← h.expUnitary_add]; rw [← h.symm.expUnitary_add]; rw [add_comm]

Depends on / 依赖: Commute, SemiconjBy, add_comm, expUnitary_add, h.expUnitary_add, h.symm.expUnitary_add
-/
theorem Commute.expUnitary {a b : selfAdjoint A} (h : Commute (a : A) (b : A)) :
    Commute (expUnitary a) (expUnitary b) := by
  rw [Commute]; rw [SemiconjBy]; rw [← h.expUnitary_add]; rw [← h.symm.expUnitary_add]; rw [add_comm]

end Star
