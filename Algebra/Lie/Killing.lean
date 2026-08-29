/-
Copyright (c) 2023 Oliver Nash. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Nash
-/
module

public import Mathlib.Algebra.Lie.InvariantForm
public import Mathlib.Algebra.Lie.Semisimple.Basic
public import Mathlib.Algebra.Lie.TraceForm

/-!
# Lie algebras with non-degenerate Killing forms.

In characteristic zero, the following three conditions are equivalent:
1. The solvable radical of a Lie algebra is trivial
2. A Lie algebra is a direct sum of its simple ideals
3. A Lie algebra has non-degenerate Killing form

In positive characteristic, it is still true that 3 implies 2, and that 2 implies 1, but there are
counterexamples to the remaining implications. Thus condition 3 is the strongest assumption.
Furthermore, much of the Cartan-Killing classification of semisimple Lie algebras in characteristic
zero, continues to hold in positive characteristic (over a perfect field) if the Lie algebra has a
non-degenerate Killing form.

This file contains basic definitions and results for such Lie algebras.

## Main declarations

* `LieAlgebra.IsKilling`: a typeclass encoding the fact that a Lie algebra has a non-singular
  Killing form.
* `LieAlgebra.IsKilling.instSemisimple`: if a finite-dimensional Lie algebra over a field
  has non-singular Killing form then it is semisimple.
* `LieAlgebra.IsKilling.instHasTrivialRadical`: if a Lie algebra over a PID
  has non-singular Killing form then it has trivial radical.
* `LieIdeal.isCompl_killingCompl`: if a Lie algebra has non-singular Killing form then for all
  ideals, an ideal and its Killing orthogonal complement are complements.

-/

public section

variable (R K L : Type*) [CommRing R] [Field K] [LieRing L] [LieAlgebra R L] [LieAlgebra K L]

namespace LieAlgebra

/--
Definition of `IsKilling` / `IsKilling` 的定义

English:
class IsKilling
  parameters: : Prop where
  axioms and operations (1):
    - killingCompl_top_eq_bot : LieIdeal.killingCompl R L ⊤ = ⊥

中文:
类 IsKilling
  参数: : 命题 where
  公理与运算 (1 个):
    - killingCompl_top_eq_bot : LieIdeal.killingCompl R L ⊤ = ⊥
-/
class IsKilling : Prop where
  /-- We say a Lie algebra is Killing if its Killing form is non-singular. -/
  killingCompl_top_eq_bot : LieIdeal.killingCompl R L ⊤ = ⊥

attribute [simp] IsKilling.killingCompl_top_eq_bot

namespace IsKilling

variable [IsKilling R L]

/--
lemma `ker_killingForm_eq_bot` / 引理 `ker_killingForm_eq_bot`

English:
lemma ker_killingForm_eq_bot
  proof: by
  simp [← LieIdeal.coe_killingCompl_top, killingCompl_top_eq_bot]

中文:
引理 ker_killingForm_eq_bot
  证明: by
  simp [← LieIdeal.coe_killingCompl_top, killingCompl_top_eq_bot]
-/
@[simp] lemma ker_killingForm_eq_bot :
    LinearMap.ker (killingForm R L) = ⊥ := by
  simp [← LieIdeal.coe_killingCompl_top, killingCompl_top_eq_bot]

/--
lemma `killingForm_nondegenerate` / 引理 `killingForm_nondegenerate`

English:
lemma killingForm_nondegenerate
  proof: by
  refine (LieModule.traceForm_isSymm R L L).isRefl.nondegenerate_iff_separatingLeft.mpr ?_
  simp [LinearMap.separatingLeft_iff_ker_eq_bot]

中文:
引理 killingForm_nondegenerate
  证明: by
  refine (LieModule.traceForm_isSymm R L L).isRefl.nondegenerate_iff_separatingLeft.mpr ?_
  simp [LinearMap.separatingLeft_iff_ker_eq_bot]

Depends on / 依赖: LieModule, LieModule.traceForm_isSymm, LinearMap, LinearMap.separatingLeft_iff_ker_eq_bot, isRefl, isRefl.nondegenerate_iff_separatingLeft.mpr, nondegenerate_iff_separatingLeft, separatingLeft_iff_ker_eq_bot, traceForm_isSymm
-/
lemma killingForm_nondegenerate :
    (killingForm R L).Nondegenerate := by
  refine (LieModule.traceForm_isSymm R L L).isRefl.nondegenerate_iff_separatingLeft.mpr ?_
  simp [LinearMap.separatingLeft_iff_ker_eq_bot]

variable {R L} in
/--
lemma `ideal_eq_bot_of_isLieAbelian` / 引理 `ideal_eq_bot_of_isLieAbelian`

English:
lemma ideal_eq_bot_of_isLieAbelian
  proof: by
  rw [eq_bot_iff]; rw [← killingCompl_top_eq_bot]
  exact I.le_killingCompl_top_of_isLieAbelian

中文:
引理 ideal_eq_bot_of_isLieAbelian
  证明: by
  rw [eq_bot_iff]; rw [← killingCompl_top_eq_bot]
  exact I.le_killingCompl_top_of_isLieAbelian

Depends on / 依赖: I.le_killingCompl_top_of_isLieAbelian, eq_bot_iff, killingCompl_top_eq_bot, le_killingCompl_top_of_isLieAbelian
-/
lemma ideal_eq_bot_of_isLieAbelian
    [Module.Free R L] [Module.Finite R L] [IsDomain R] [IsPrincipalIdealRing R]
    (I : LieIdeal R L) [IsLieAbelian I] : I = ⊥ := by
  rw [eq_bot_iff]; rw [← killingCompl_top_eq_bot]
  exact I.le_killingCompl_top_of_isLieAbelian

/--
Instance `instSemisimple` / 实例 `instSemisimple`

English:
instance instSemisimple
  signature: [IsKilling K L] [Module.Finite K L]
  body: by
  apply InvariantForm.isSemisimple_of_nondegenerate (Φ := killingForm K L)
  · exact IsKilling.killingForm_nondegenerate _ _
  · exact LieModule.traceForm_lieInvariant _ _ _
  · exact (LieModule.traceForm_isSymm K L L).isRefl
  · intro I h₁ h₂
exact h₁.1 IsKilling.ideal_eq_bot_of_isLieAbelian I

中文:
实例 instSemisimple
  签名: [IsKilling K L] [Module.Finite K L]
  定义体: by
  apply InvariantForm.isSemisimple_of_nondegenerate (Φ := killingForm K L)
  · exact IsKilling.killingForm_nondegenerate _ _
  · exact LieModule.traceForm_lieInvariant _ _ _
  · exact (LieModule.traceForm_isSymm K L L).isRefl
  · intro I h₁ h₂
exact h₁.1 IsKilling.ideal_eq_bot_of_isLieAbelian I

Depends on / 依赖: InvariantForm, InvariantForm.isSemisimple_of_nondegenerate, IsKilling, IsKilling.ideal_eq_bot_of_isLieAbelian, IsKilling.killingForm_nondegenerate, LieModule, LieModule.traceForm_isSymm, LieModule.traceForm_lieInvariant, ideal_eq_bot_of_isLieAbelian, isRefl, isSemisimple_of_nondegenerate, killingForm, killingForm_nondegenerate, traceForm_isSymm, traceForm_lieInvariant
-/
instance instSemisimple [IsKilling K L] [Module.Finite K L] : IsSemisimple K L := by
  apply InvariantForm.isSemisimple_of_nondegenerate (Φ := killingForm K L)
  · exact IsKilling.killingForm_nondegenerate _ _
  · exact LieModule.traceForm_lieInvariant _ _ _
  · exact (LieModule.traceForm_isSymm K L L).isRefl
  · intro I h₁ h₂
exact h₁.1 IsKilling.ideal_eq_bot_of_isLieAbelian I

/--
Instance `instHasTrivialRadical` / 实例 `instHasTrivialRadical`

English:
instance instHasTrivialRadical
  body: (hasTrivialRadical_iff_no_abelian_ideals R L).mpr IsKilling.ideal_eq_bot_of_isLieAbelian

中文:
实例 instHasTrivialRadical
  定义体: (hasTrivialRadical_iff_no_abelian_ideals R L).mpr IsKilling.ideal_eq_bot_of_isLieAbelian

Depends on / 依赖: IsKilling, IsKilling.ideal_eq_bot_of_isLieAbelian, hasTrivialRadical_iff_no_abelian_ideals, ideal_eq_bot_of_isLieAbelian
-/
instance instHasTrivialRadical
    [Module.Free R L] [Module.Finite R L] [IsDomain R] [IsPrincipalIdealRing R] :
    HasTrivialRadical R L :=
  (hasTrivialRadical_iff_no_abelian_ideals R L).mpr IsKilling.ideal_eq_bot_of_isLieAbelian

/--
theorem `isLieAbelian_iff_subsingleton` / 定理 `isLieAbelian_iff_subsingleton`

English:
theorem isLieAbelian_iff_subsingleton
  proof: by
  constructor
  · intro h
    rw [isLieAbelian_iff_center_eq_top R] at h
    have hc : (⊤ : LieIdeal R L) = ⊥ := by rw [← center_eq_bot R L, h]
    exact (LieSubmodule.subsingleton_iff R L L).mp (subsingleton_of_top_eq_bot hc)
  · exact fun _ => inferInstance

中文:
定理 isLieAbelian_iff_subsingleton
  证明: by
  constructor
  · intro h
    rw [isLieAbelian_iff_center_eq_top R] at h
    have hc : (⊤ : LieIdeal R L) = ⊥ := by rw [← center_eq_bot R L, h]
    exact (LieSubmodule.subsingleton_iff R L L).mp (subsingleton_of_top_eq_bot hc)
  · exact fun _ => inferInstance

Depends on / 依赖: LieIdeal, LieSubmodule, LieSubmodule.subsingleton_iff, center_eq_bot, isLieAbelian_iff_center_eq_top, subsingleton_iff, subsingleton_of_top_eq_bot
-/
theorem isLieAbelian_iff_subsingleton
    [Module.Free R L] [Module.Finite R L] [IsDomain R] [IsPrincipalIdealRing R] :
    IsLieAbelian L ↔ Subsingleton L := by
  constructor
  · intro h
    rw [isLieAbelian_iff_center_eq_top R] at h
    have hc : (⊤ : LieIdeal R L) = ⊥ := by rw [← center_eq_bot R L, h]
    exact (LieSubmodule.subsingleton_iff R L L).mp (subsingleton_of_top_eq_bot hc)
  · exact fun _ => inferInstance

end IsKilling

section LieEquiv

variable {R L}
variable {L' : Type*} [LieRing L'] [LieAlgebra R L']

/--
lemma `killingForm_of_equiv_apply` / 引理 `killingForm_of_equiv_apply`

English:
lemma killingForm_of_equiv_apply
  given: (e : L ≃ₗ⁅R⁆ L') (x y : L)
  proof: by
  simp_rw [killingForm_apply_apply, ← LieAlgebra.conj_ad_apply, ← LinearEquiv.conj_comp,
    LinearMap.trace_conj']

中文:
引理 killingForm_of_equiv_apply
  条件: (e : L ≃ₗ⁅R⁆ L') (x y : L)
  证明: by
  simp_rw [killingForm_apply_apply, ← LieAlgebra.conj_ad_apply, ← LinearEquiv.conj_comp,
    LinearMap.trace_conj']
-/
@[simp] lemma killingForm_of_equiv_apply (e : L ≃ₗ⁅R⁆ L') (x y : L) :
    killingForm R L' (e x) (e y) = killingForm R L x y := by
  simp_rw [killingForm_apply_apply, ← LieAlgebra.conj_ad_apply, ← LinearEquiv.conj_comp,
    LinearMap.trace_conj']

/--
lemma `isKilling_of_equiv` / 引理 `isKilling_of_equiv`

English:
lemma isKilling_of_equiv
  given: [IsKilling R L] (e : L ≃ₗ⁅R⁆ L')
  statement: IsKilling R L'
  proof: by
  constructor
  ext x'
  simp_rw [LieIdeal.mem_killingCompl, LieModule.traceForm_comm]
  refine ⟨fun hx' => ?_, fun hx y _ => hx ▸ LinearMap.map_zero₂ (killingForm R L') y⟩
  suffices e.symm x' in LinearMap.ker (killingForm R L) by
    rw [IsKilling.ker_killingForm_eq_bot] at this
    simpa [map_

中文:
引理 isKilling_of_equiv
  条件: [IsKilling R L] (e : L ≃ₗ⁅R⁆ L')
  结论: IsKilling R L'
  证明: by
  constructor
  ext x'
  simp_rw [LieIdeal.mem_killingCompl, LieModule.traceForm_comm]
  refine ⟨fun hx' => ?_, fun hx y _ => hx ▸ LinearMap.map_zero₂ (killingForm R L') y⟩
  suffices e.symm x' in LinearMap.ker (killingForm R L) by
    rw [IsKilling.ker_killingForm_eq_bot] at this
    simpa [map_

Depends on / 依赖: IsKilling, IsKilling.ker_killingForm_eq_bot, LieIdeal, LieIdeal.mem_killingCompl, LieModule, LieModule.traceForm_comm, LinearMap, LinearMap.ker, LinearMap.map_zero, apply_symm_apply, congr_arg, e.apply_symm_apply, e.symm, ker_killingForm_eq_bot, killingForm, killingForm_of_equiv_apply, map_zero, mem_killingCompl, replace, simp_rw
-/
lemma isKilling_of_equiv [IsKilling R L] (e : L ≃ₗ⁅R⁆ L') : IsKilling R L' := by
  constructor
  ext x'
  simp_rw [LieIdeal.mem_killingCompl, LieModule.traceForm_comm]
  refine ⟨fun hx' => ?_, fun hx y _ => hx ▸ LinearMap.map_zero₂ (killingForm R L') y⟩
  suffices e.symm x' in LinearMap.ker (killingForm R L) by
    rw [IsKilling.ker_killingForm_eq_bot] at this
    simpa [map_zero] using (e : L ≃ₗ[R] L').congr_arg this
  ext y
  replace hx' : forall y', killingForm R L' x' y' = 0 := by simpa using hx'
  specialize hx' (e y)
  rwa [← e.apply_symm_apply x', killingForm_of_equiv_apply] at hx'

alias _root_.LieEquiv.isKilling := LieAlgebra.isKilling_of_equiv

end LieEquiv

end LieAlgebra

open LieAlgebra in
variable {K L} in
/--
lemma `LieIdeal.isCompl_killingCompl` / 引理 `LieIdeal.isCompl_killingCompl`

English:
lemma LieIdeal.isCompl_killingCompl
  given: [IsKilling K L] [Module.Finite K L] (I : LieIdeal K L)
  proof: by
  suffices Disjoint I I.killingCompl by
    rwa [← LieSubmodule.isCompl_toSubmodule, I.toSubmodule_killingCompl,
      LinearMap.BilinForm.isCompl_orthogonal_iff_disjoint (LieModule.traceForm_isSymm K L L).isRefl,
      ← I.toSubmodule_killingCompl, LieSubmodule.disjoint_toSubmodule]
  suffices I

中文:
引理 LieIdeal.isCompl_killingCompl
  条件: [IsKilling K L] [Module.Finite K L] (I : LieIdeal K L)
  证明: by
  suffices Disjoint I I.killingCompl by
    rwa [← LieSubmodule.isCompl_toSubmodule, I.toSubmodule_killingCompl,
      LinearMap.BilinForm.isCompl_orthogonal_iff_disjoint (LieModule.traceForm_isSymm K L L).isRefl,
      ← I.toSubmodule_killingCompl, LieSubmodule.disjoint_toSubmodule]
  suffices I

Depends on / 依赖: BilinForm, Disjoint, I.killingCompl, I.toSubmodule_killingCompl, IsKilling, IsKilling.ideal_eq_bot_of_isLieAbelian, IsLieAbelian, LieIdeal, LieModule, LieModule.traceForm, LieModule.traceForm_isSymm, LieSubmodule, LieSubmodule.disjoint_toSubmodule, LieSubmodule.isCompl_toSubmodule, LinearMap, LinearMap.BilinForm.isCompl_orthogonal_iff_disjoint, disjoint_iff, disjoint_toSubmodule, ideal_eq_bot_of_isLieAbelian, isCompl_orthogonal_iff_disjoint
-/
lemma LieIdeal.isCompl_killingCompl [IsKilling K L] [Module.Finite K L] (I : LieIdeal K L) :
    IsCompl I I.killingCompl := by
  suffices Disjoint I I.killingCompl by
    rwa [← LieSubmodule.isCompl_toSubmodule, I.toSubmodule_killingCompl,
      LinearMap.BilinForm.isCompl_orthogonal_iff_disjoint (LieModule.traceForm_isSymm K L L).isRefl,
      ← I.toSubmodule_killingCompl, LieSubmodule.disjoint_toSubmodule]
  suffices IsLieAbelian (I ⊓ I.killingCompl : LieIdeal K L) by
    rw [disjoint_iff]
    exact IsKilling.ideal_eq_bot_of_isLieAbelian _
  suffices forall (x y z : L) (hx : x in killingCompl K L I) (hy : y in I),
      LieModule.traceForm K L L ⁅x, y⁆ z = 0 by
    rw [LieSubmodule.lie_abelian_iff_lie_self_eq_bot]; rw [LieSubmodule.lie_eq_bot_iff]
    rintro x ⟨-, hx⟩ y ⟨hy, -⟩
    exact (IsKilling.killingForm_nondegenerate K L).1 _ fun z => this x y z hx hy
  intro x y z hx hy
  rw [LieModule.traceForm_apply_lie_apply K L L x y z]; rw [LieModule.traceForm_comm K L L]
exact I.mem_killingCompl.mp hx _ lie_mem_left K L I y z hy
