/-
Copyright (c) 2022 Anatole Dedecker. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Moritz Doll, Frédéric Dupuis, Heather Macbeth
-/
module

public import Mathlib.Analysis.InnerProductSpace.Subspace
public import Mathlib.Analysis.Normed.Operator.Banach
public import Mathlib.LinearAlgebra.SesquilinearForm.Basic
public import Mathlib.Analysis.InnerProductSpace.Orthogonal
public import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Idempotent

/-!
# Symmetric linear maps in an inner product space

This file defines and proves basic theorems about symmetric **not necessarily bounded** operators
on an inner product space, i.e linear maps `T : E → E` such that `∀ x y, ⟪T x, y⟫ = ⟪x, T y⟫`.

In comparison to `IsSelfAdjoint`, this definition works for non-continuous linear maps, and
doesn't rely on the definition of the adjoint, which allows it to be stated in non-complete space.

## Main definitions

* `LinearMap.IsSymmetric`: a (not necessarily bounded) operator on an inner product space is
  symmetric, if for all `x`, `y`, we have `⟪T x, y⟫ = ⟪x, T y⟫`

## Main statements

* `IsSymmetric.continuous`: if a symmetric operator is defined on a complete space, then
  it is automatically continuous.

## Tags

self-adjoint, symmetric
-/

@[expose] public section


open RCLike

open ComplexConjugate

section Seminormed

variable {𝕜 E : Type*} [RCLike 𝕜]
variable [SeminormedAddCommGroup E] [InnerProductSpace 𝕜 E]

local notation "⟪" x ", " y "⟫" => inner 𝕜 x y

namespace LinearMap

/-! ### Symmetric operators -/


/--
Definition of `IsSymmetric` / `IsSymmetric` 的定义

English:
definition IsSymmetric
  signature: (T : E ->ₗ[𝕜] E)
  body: forall x y, ⟪T x, y⟫ = ⟪x, T y⟫

中文:
定义 IsSymmetric
  签名: (T : E ->ₗ[𝕜] E)
  定义体: forall x y, ⟪T x, y⟫ = ⟪x, T y⟫
-/
def IsSymmetric (T : E ->ₗ[𝕜] E) : Prop :=
  forall x y, ⟪T x, y⟫ = ⟪x, T y⟫

section Real

/--
theorem `isSymmetric_iff_sesqForm` / 定理 `isSymmetric_iff_sesqForm`

English:
theorem isSymmetric_iff_sesqForm
  given: (T : E ->ₗ[𝕜] E)
  proof: ⟨fun h x y => (h y x).symm, fun h x y => (h y x).symm⟩

中文:
定理 isSymmetric_iff_sesqForm
  条件: (T : E ->ₗ[𝕜] E)
  证明: ⟨fun h x y => (h y x).symm, fun h x y => (h y x).symm⟩

Depends on / 依赖: LinearMap, LinearMap.flip
-/
theorem isSymmetric_iff_sesqForm (T : E ->ₗ[𝕜] E) :
    T.IsSymmetric ↔ LinearMap.IsSelfAdjoint (R := 𝕜) (M := E) (LinearMap.flip (innerₛₗ 𝕜)) T :=
  ⟨fun h x y => (h y x).symm, fun h x y => (h y x).symm⟩

end Real

/--
theorem `IsSymmetric.conj_inner_sym` / 定理 `IsSymmetric.conj_inner_sym`

English:
theorem IsSymmetric.conj_inner_sym
  given: {T : E ->ₗ[𝕜] E} (hT : IsSymmetric T) (x y : E)
  proof: by rw [hT x y, inner_conj_symm]

@[simp]

中文:
定理 IsSymmetric.conj_inner_sym
  条件: {T : E ->ₗ[𝕜] E} (hT : IsSymmetric T) (x y : E)
  证明: by rw [hT x y, inner_conj_symm]

@[simp]

Depends on / 依赖: inner_conj_symm
-/
theorem IsSymmetric.conj_inner_sym {T : E ->ₗ[𝕜] E} (hT : IsSymmetric T) (x y : E) :
    conj ⟪T x, y⟫ = ⟪T y, x⟫ := by rw [hT x y, inner_conj_symm]

@[simp]
/--
theorem `IsSymmetric.apply_clm` / 定理 `IsSymmetric.apply_clm`

English:
theorem IsSymmetric.apply_clm
  given: {T : E ->L[𝕜] E} (hT : IsSymmetric (T : E ->ₗ[𝕜] E)) (x y : E)
  proof: hT x y

@[simp]

中文:
定理 IsSymmetric.apply_clm
  条件: {T : E ->L[𝕜] E} (hT : IsSymmetric (T : E ->ₗ[𝕜] E)) (x y : E)
  证明: hT x y

@[simp]
-/
theorem IsSymmetric.apply_clm {T : E ->L[𝕜] E} (hT : IsSymmetric (T : E ->ₗ[𝕜] E)) (x y : E) :
    ⟪T x, y⟫ = ⟪x, T y⟫ :=
  hT x y

@[simp]
/--
theorem `IsSymmetric.zero` / 定理 `IsSymmetric.zero`

English:
theorem IsSymmetric.zero
  statement: (0 : E ->ₗ[𝕜] E).IsSymmetric
  proof: fun x y =>
  (inner_zero_right x : ⟪x, 0⟫ = 0).symm ▸ (inner_zero_left y : ⟪0, y⟫ = 0)

中文:
定理 IsSymmetric.zero
  结论: (0 : E ->ₗ[𝕜] E).IsSymmetric
  证明: fun x y =>
  (inner_zero_right x : ⟪x, 0⟫ = 0).symm ▸ (inner_zero_left y : ⟪0, y⟫ = 0)
-/
protected theorem IsSymmetric.zero : (0 : E ->ₗ[𝕜] E).IsSymmetric := fun x y =>
  (inner_zero_right x : ⟪x, 0⟫ = 0).symm ▸ (inner_zero_left y : ⟪0, y⟫ = 0)

/--
lemma `IsSymmetric.id` / 引理 `IsSymmetric.id`

English:
lemma IsSymmetric.id
  statement: (.id : E ->ₗ[𝕜] E).IsSymmetric
  proof: fun _ _ => rfl

中文:
引理 IsSymmetric.id
  结论: (.id : E ->ₗ[𝕜] E).IsSymmetric
  证明: fun _ _ => rfl
-/
@[simp] protected lemma IsSymmetric.id : (.id : E ->ₗ[𝕜] E).IsSymmetric := fun _ _ => rfl
/--
lemma `IsSymmetric.one` / 引理 `IsSymmetric.one`

English:
lemma IsSymmetric.one
  statement: (1 : E ->ₗ[𝕜] E).IsSymmetric
  proof: fun _ _ => rfl

@[aesop safe apply]

中文:
引理 IsSymmetric.one
  结论: (1 : E ->ₗ[𝕜] E).IsSymmetric
  证明: fun _ _ => rfl

@[aesop safe apply]
-/
@[simp] protected lemma IsSymmetric.one : (1 : E ->ₗ[𝕜] E).IsSymmetric := fun _ _ => rfl

@[aesop safe apply]
/--
theorem `IsSymmetric.add` / 定理 `IsSymmetric.add`

English:
theorem IsSymmetric.add
  given: {T S : E ->ₗ[𝕜] E} (hT : T.IsSymmetric) (hS : S.IsSymmetric)
  proof: by
  intro x y
  rw [add_apply]; rw [inner_add_left]; rw [hT x y]; rw [hS x y]; rw [← inner_add_right]; rw [add_apply]

中文:
定理 IsSymmetric.add
  条件: {T S : E ->ₗ[𝕜] E} (hT : T.IsSymmetric) (hS : S.IsSymmetric)
  证明: by
  intro x y
  rw [add_apply]; rw [inner_add_left]; rw [hT x y]; rw [hS x y]; rw [← inner_add_right]; rw [add_apply]

Depends on / 依赖: add_apply, inner_add_left, inner_add_right
-/
theorem IsSymmetric.add {T S : E ->ₗ[𝕜] E} (hT : T.IsSymmetric) (hS : S.IsSymmetric) :
    (T + S).IsSymmetric := by
  intro x y
  rw [add_apply]; rw [inner_add_left]; rw [hT x y]; rw [hS x y]; rw [← inner_add_right]; rw [add_apply]

/--
theorem `isSymmetric_sum` / 定理 `isSymmetric_sum`

English:
theorem isSymmetric_sum
  statement: {ι : Type*} {T : ι -> (E ->ₗ[𝕜] E)} (s : Finset ι)
  proof: fun _ _ => by
  simpa [sum_inner, inner_sum] using Finset.sum_congr rfl fun _ hi => hT _ hi _ _

@[aesop safe apply]

中文:
定理 isSymmetric_sum
  结论: {ι : 类型} {T : ι -> (E ->ₗ[𝕜] E)} (s : 有限集 ι)
  证明: fun _ _ => by
  simpa [sum_inner, inner_sum] using Finset.sum_congr rfl fun _ hi => hT _ hi _ _

@[aesop safe apply]

Depends on / 依赖: Finset, Finset.sum_congr, inner_sum, sum_congr, sum_inner
-/
theorem isSymmetric_sum {ι : Type*} {T : ι -> (E ->ₗ[𝕜] E)} (s : Finset ι)
    (hT : forall i in s, (T i).IsSymmetric) : (∑ i in s, T i).IsSymmetric := fun _ _ => by
  simpa [sum_inner, inner_sum] using Finset.sum_congr rfl fun _ hi => hT _ hi _ _

@[aesop safe apply]
/--
theorem `IsSymmetric.sub` / 定理 `IsSymmetric.sub`

English:
theorem IsSymmetric.sub
  given: {T S : E ->ₗ[𝕜] E} (hT : T.IsSymmetric) (hS : S.IsSymmetric)
  proof: by
  intro x y
  rw [sub_apply]; rw [inner_sub_left]; rw [hT x y]; rw [hS x y]; rw [← inner_sub_right]; rw [sub_apply]

@[aesop safe apply]

中文:
定理 IsSymmetric.sub
  条件: {T S : E ->ₗ[𝕜] E} (hT : T.IsSymmetric) (hS : S.IsSymmetric)
  证明: by
  intro x y
  rw [sub_apply]; rw [inner_sub_left]; rw [hT x y]; rw [hS x y]; rw [← inner_sub_right]; rw [sub_apply]

@[aesop safe apply]

Depends on / 依赖: inner_sub_left, inner_sub_right, sub_apply
-/
theorem IsSymmetric.sub {T S : E ->ₗ[𝕜] E} (hT : T.IsSymmetric) (hS : S.IsSymmetric) :
    (T - S).IsSymmetric := by
  intro x y
  rw [sub_apply]; rw [inner_sub_left]; rw [hT x y]; rw [hS x y]; rw [← inner_sub_right]; rw [sub_apply]

@[aesop safe apply]
/--
theorem `IsSymmetric.smul` / 定理 `IsSymmetric.smul`

English:
theorem IsSymmetric.smul
  given: {c : 𝕜} (hc : conj c = c) {T : E ->ₗ[𝕜] E} (hT : T.IsSymmetric)
  proof: by c • T
  intro x y
  simp only [smul_apply, inner_smul_left, hc, hT x y, inner_smul_right]

中文:
定理 IsSymmetric.smul
  条件: {c : 𝕜} (hc : conj c = c) {T : E ->ₗ[𝕜] E} (hT : T.IsSymmetric)
  证明: by c • T
  intro x y
  simp only [smul_apply, inner_smul_left, hc, hT x y, inner_smul_right]

Depends on / 依赖: inner_smul_left, inner_smul_right, smul_apply
-/
theorem IsSymmetric.smul {c : 𝕜} (hc : conj c = c) {T : E ->ₗ[𝕜] E} (hT : T.IsSymmetric) :
.IsSymmetric := by c • T
  intro x y
  simp only [smul_apply, inner_smul_left, hc, hT x y, inner_smul_right]

/--
theorem `IsSymmetric.natCast` / 定理 `IsSymmetric.natCast`

English:
theorem IsSymmetric.natCast
  given: (n : Nat)
  statement: IsSymmetric (n : E ->ₗ[𝕜] E)
  proof: fun x y => by
  simp [← Nat.cast_smul_eq_nsmul 𝕜, inner_smul_left, inner_smul_right]

中文:
定理 IsSymmetric.natCast
  条件: (n : 自然数)
  结论: IsSymmetric (n : E ->ₗ[𝕜] E)
  证明: fun x y => by
  simp [← Nat.cast_smul_eq_nsmul 𝕜, inner_smul_left, inner_smul_right]

Depends on / 依赖: Nat.cast_smul_eq_nsmul, cast_smul_eq_nsmul, inner_smul_left, inner_smul_right
-/
theorem IsSymmetric.natCast (n : Nat) : IsSymmetric (n : E ->ₗ[𝕜] E) := fun x y => by
  simp [← Nat.cast_smul_eq_nsmul 𝕜, inner_smul_left, inner_smul_right]

/--
theorem `IsSymmetric.intCast` / 定理 `IsSymmetric.intCast`

English:
theorem IsSymmetric.intCast
  given: (n : Int)
  statement: IsSymmetric (n : E ->ₗ[𝕜] E)
  proof: fun x y => by
  simp [← Int.cast_smul_eq_zsmul 𝕜, inner_smul_left, inner_smul_right]

@[aesop 30% apply]

中文:
定理 IsSymmetric.intCast
  条件: (n : 整数)
  结论: IsSymmetric (n : E ->ₗ[𝕜] E)
  证明: fun x y => by
  simp [← Int.cast_smul_eq_zsmul 𝕜, inner_smul_left, inner_smul_right]

@[aesop 30% apply]

Depends on / 依赖: Int.cast_smul_eq_zsmul, cast_smul_eq_zsmul, inner_smul_left, inner_smul_right
-/
theorem IsSymmetric.intCast (n : Int) : IsSymmetric (n : E ->ₗ[𝕜] E) := fun x y => by
  simp [← Int.cast_smul_eq_zsmul 𝕜, inner_smul_left, inner_smul_right]

@[aesop 30% apply]
/--
lemma `IsSymmetric.mul_of_commute` / 引理 `IsSymmetric.mul_of_commute`

English:
lemma IsSymmetric.mul_of_commute
  statement: {S T : E ->ₗ[𝕜] E} (hS : S.IsSymmetric) (hT : T.IsSymmetric)
  proof: fun _ _ => by rw [Module.End.mul_apply, hS, hT, hST, Module.End.mul_apply]

@[aesop safe apply]

中文:
引理 IsSymmetric.mul_of_commute
  结论: {S T : E ->ₗ[𝕜] E} (hS : S.IsSymmetric) (hT : T.IsSymmetric)
  证明: fun _ _ => by rw [Module.End.mul_apply, hS, hT, hST, Module.End.mul_apply]

@[aesop safe apply]

Depends on / 依赖: Module, Module.End.mul_apply, mul_apply
-/
lemma IsSymmetric.mul_of_commute {S T : E ->ₗ[𝕜] E} (hS : S.IsSymmetric) (hT : T.IsSymmetric)
    (hST : Commute S T) : (S * T).IsSymmetric :=
  fun _ _ => by rw [Module.End.mul_apply, hS, hT, hST, Module.End.mul_apply]

@[aesop safe apply]
/--
lemma `IsSymmetric.pow` / 引理 `IsSymmetric.pow`

English:
lemma IsSymmetric.pow
  given: {T : E ->ₗ[𝕜] E} (hT : T.IsSymmetric) (n : Nat)
  statement: (T ^ n).IsSymmetric
  proof: by
  refine Nat.le_induction (by simp [Module.End.one_eq_id]) (fun k _ ih => ?_) n n.zero_le
  rw [Module.End.iterate_succ]; rw [← Module.End.mul_eq_comp]
exact ih.mul_of_commute hT .pow_left rfl k

中文:
引理 IsSymmetric.pow
  条件: {T : E ->ₗ[𝕜] E} (hT : T.IsSymmetric) (n : 自然数)
  结论: (T ^ n).IsSymmetric
  证明: by
  refine Nat.le_induction (by simp [Module.End.one_eq_id]) (fun k _ ih => ?_) n n.zero_le
  rw [Module.End.iterate_succ]; rw [← Module.End.mul_eq_comp]
exact ih.mul_of_commute hT .pow_left rfl k

Depends on / 依赖: Module, Module.End.iterate_succ, Module.End.mul_eq_comp, Module.End.one_eq_id, Nat.le_induction, ih.mul_of_commute, iterate_succ, le_induction, mul_eq_comp, mul_of_commute, n.zero_le, one_eq_id, pow_left, zero_le
-/
lemma IsSymmetric.pow {T : E ->ₗ[𝕜] E} (hT : T.IsSymmetric) (n : Nat) : (T ^ n).IsSymmetric := by
  refine Nat.le_induction (by simp [Module.End.one_eq_id]) (fun k _ ih => ?_) n n.zero_le
  rw [Module.End.iterate_succ]; rw [← Module.End.mul_eq_comp]
exact ih.mul_of_commute hT .pow_left rfl k

/-- For a symmetric operator `T`, the function `fun x ↦ ⟪T x, x⟫` is real-valued. -/
@[simp]
/--
theorem `IsSymmetric.coe_reApplyInnerSelf_apply` / 定理 `IsSymmetric.coe_reApplyInnerSelf_apply`

English:
theorem IsSymmetric.coe_reApplyInnerSelf_apply
  statement: {T : E ->L[𝕜] E} (hT : IsSymmetric (T : E ->ₗ[𝕜] E))
  proof: by
  rsuffices ⟨r, hr⟩ : exists r : Real, ⟪T x, x⟫ = r
  · simp [hr, T.reApplyInnerSelf_apply]
  rw [← conj_eq_iff_real]
  exact hT.conj_inner_sym x x

中文:
定理 IsSymmetric.coe_reApplyInnerSelf_apply
  结论: {T : E ->L[𝕜] E} (hT : IsSymmetric (T : E ->ₗ[𝕜] E))
  证明: by
  rsuffices ⟨r, hr⟩ : exists r : Real, ⟪T x, x⟫ = r
  · simp [hr, T.reApplyInnerSelf_apply]
  rw [← conj_eq_iff_real]
  exact hT.conj_inner_sym x x

Depends on / 依赖: T.reApplyInnerSelf_apply, conj_eq_iff_real, conj_inner_sym, hT.conj_inner_sym, reApplyInnerSelf_apply, rsuffices
-/
theorem IsSymmetric.coe_reApplyInnerSelf_apply {T : E ->L[𝕜] E} (hT : IsSymmetric (T : E ->ₗ[𝕜] E))
    (x : E) : (T.reApplyInnerSelf x : 𝕜) = ⟪T x, x⟫ := by
  rsuffices ⟨r, hr⟩ : exists r : Real, ⟪T x, x⟫ = r
  · simp [hr, T.reApplyInnerSelf_apply]
  rw [← conj_eq_iff_real]
  exact hT.conj_inner_sym x x

/--
theorem `IsSymmetric.restrict_invariant` / 定理 `IsSymmetric.restrict_invariant`

English:
theorem IsSymmetric.restrict_invariant
  statement: {T : E ->ₗ[𝕜] E} (hT : IsSymmetric T) {V : Submodule 𝕜 E}
  proof: fun v w => hT v w

中文:
定理 IsSymmetric.restrict_invariant
  结论: {T : E ->ₗ[𝕜] E} (hT : IsSymmetric T) {V : 子模 𝕜 E}
  证明: fun v w => hT v w
-/
theorem IsSymmetric.restrict_invariant {T : E ->ₗ[𝕜] E} (hT : IsSymmetric T) {V : Submodule 𝕜 E}
    (hV : forall v in V, T v in V) : IsSymmetric (T.restrict hV) := fun v w => hT v w

/--
theorem `IsSymmetric.restrictScalars` / 定理 `IsSymmetric.restrictScalars`

English:
theorem IsSymmetric.restrictScalars
  given: {T : E ->ₗ[𝕜] E} (hT : T.IsSymmetric)
  proof: InnerProductSpace.rclikeToReal 𝕜 E
    haveI := IsScalarTower.restrictScalars Real 𝕜 E
    (T.restrictScalars Real).IsSymmetric :=
  fun x y => by simp [hT x y, real_inner_eq_re_inner, LinearMap.coe_restrictScalars Real]

@[simp]

中文:
定理 IsSymmetric.restrictScalars
  条件: {T : E ->ₗ[𝕜] E} (hT : T.IsSymmetric)
  证明: InnerProductSpace.rclikeToReal 𝕜 E
    haveI := IsScalarTower.restrictScalars Real 𝕜 E
    (T.restrictScalars Real).IsSymmetric :=
  fun x y => by simp [hT x y, real_inner_eq_re_inner, LinearMap.coe_restrictScalars Real]

@[simp]

Depends on / 依赖: InnerProductSpace, InnerProductSpace.rclikeToReal, rclikeToReal
-/
theorem IsSymmetric.restrictScalars {T : E ->ₗ[𝕜] E} (hT : T.IsSymmetric) :
    letI := InnerProductSpace.rclikeToReal 𝕜 E
    haveI := IsScalarTower.restrictScalars Real 𝕜 E
    (T.restrictScalars Real).IsSymmetric :=
  fun x y => by simp [hT x y, real_inner_eq_re_inner, LinearMap.coe_restrictScalars Real]

@[simp]
/--
theorem `IsSymmetric.im_inner_apply_self` / 定理 `IsSymmetric.im_inner_apply_self`

English:
theorem IsSymmetric.im_inner_apply_self
  given: {T : E ->ₗ[𝕜] E} (hT : T.IsSymmetric) (x : E)
  proof: conj_eq_iff_im.mp hT.conj_inner_sym x x

@[simp]

中文:
定理 IsSymmetric.im_inner_apply_self
  条件: {T : E ->ₗ[𝕜] E} (hT : T.IsSymmetric) (x : E)
  证明: conj_eq_iff_im.mp hT.conj_inner_sym x x

@[simp]

Depends on / 依赖: conj_eq_iff_im, conj_eq_iff_im.mp, conj_inner_sym, hT.conj_inner_sym
-/
theorem IsSymmetric.im_inner_apply_self {T : E ->ₗ[𝕜] E} (hT : T.IsSymmetric) (x : E) :
    im ⟪T x, x⟫ = 0 :=
conj_eq_iff_im.mp hT.conj_inner_sym x x

@[simp]
/--
theorem `IsSymmetric.im_inner_self_apply` / 定理 `IsSymmetric.im_inner_self_apply`

English:
theorem IsSymmetric.im_inner_self_apply
  given: {T : E ->ₗ[𝕜] E} (hT : T.IsSymmetric) (x : E)
  proof: by
  simp [← hT x x, hT]

@[simp]

中文:
定理 IsSymmetric.im_inner_self_apply
  条件: {T : E ->ₗ[𝕜] E} (hT : T.IsSymmetric) (x : E)
  证明: by
  simp [← hT x x, hT]

@[simp]
-/
theorem IsSymmetric.im_inner_self_apply {T : E ->ₗ[𝕜] E} (hT : T.IsSymmetric) (x : E) :
    im ⟪x, T x⟫ = 0 := by
  simp [← hT x x, hT]

@[simp]
/--
theorem `IsSymmetric.coe_re_inner_apply_self` / 定理 `IsSymmetric.coe_re_inner_apply_self`

English:
theorem IsSymmetric.coe_re_inner_apply_self
  given: {T : E ->ₗ[𝕜] E} (hT : T.IsSymmetric) (x : E)
  proof: conj_eq_iff_re.mp hT.conj_inner_sym x x

@[simp]

中文:
定理 IsSymmetric.coe_re_inner_apply_self
  条件: {T : E ->ₗ[𝕜] E} (hT : T.IsSymmetric) (x : E)
  证明: conj_eq_iff_re.mp hT.conj_inner_sym x x

@[simp]

Depends on / 依赖: conj_eq_iff_re, conj_eq_iff_re.mp, conj_inner_sym, hT.conj_inner_sym
-/
theorem IsSymmetric.coe_re_inner_apply_self {T : E ->ₗ[𝕜] E} (hT : T.IsSymmetric) (x : E) :
    re ⟪T x, x⟫ = ⟪T x, x⟫ :=
conj_eq_iff_re.mp hT.conj_inner_sym x x

@[simp]
/--
theorem `IsSymmetric.coe_re_inner_self_apply` / 定理 `IsSymmetric.coe_re_inner_self_apply`

English:
theorem IsSymmetric.coe_re_inner_self_apply
  given: {T : E ->ₗ[𝕜] E} (hT : T.IsSymmetric) (x : E)
  proof: by
  simp [← hT x x, hT]

中文:
定理 IsSymmetric.coe_re_inner_self_apply
  条件: {T : E ->ₗ[𝕜] E} (hT : T.IsSymmetric) (x : E)
  证明: by
  simp [← hT x x, hT]
-/
theorem IsSymmetric.coe_re_inner_self_apply {T : E ->ₗ[𝕜] E} (hT : T.IsSymmetric) (x : E) :
    re ⟪x, T x⟫ = ⟪x, T x⟫ := by
  simp [← hT x x, hT]

/-- A symmetric projection is a symmetric idempotent. -/
@[mk_iff]
/--
Definition of `IsSymmetricProjection` / `IsSymmetricProjection` 的定义

English:
structure IsSymmetricProjection
  parameters: (T : E ->ₗ[𝕜] E)
  axioms and operations (2):
    - isIdempotentElem : IsIdempotentElem T
    - isSymmetric : T.IsSymmetric

中文:
结构 是SymmetricProjection
  参数: (T : E ->ₗ[𝕜] E)
  公理与运算 (2 个):
    - isIdempotentElem : IsIdempotentElem T
    - isSymmetric : T.IsSymmetric
-/
structure IsSymmetricProjection (T : E ->ₗ[𝕜] E) : Prop where
  isIdempotentElem : IsIdempotentElem T
  isSymmetric : T.IsSymmetric

section Complex

variable {V : Type*} [SeminormedAddCommGroup V] [InnerProductSpace Complex V]

attribute [local simp] map_ofNat in -- use `ofNat` simp theorem with bad keys
open scoped InnerProductSpace in
/--
theorem `isSymmetric_iff_inner_map_self_real` / 定理 `isSymmetric_iff_inner_map_self_real`

English:
theorem isSymmetric_iff_inner_map_self_real
  given: (T : V ->ₗ[Complex] V)
  proof: by
  constructor
  · intro hT v
    apply IsSymmetric.conj_inner_sym hT
  · intro h x y
    rw [← inner_conj_symm x (T y)]
    rw [inner_map_polarization T x y]
    simp only [starRingEnd_apply, star_div₀, star_sub, star_add, star_mul]
    simp only [← starRingEnd_apply]
    rw [h (x + y)]; rw [h (x

中文:
定理 isSymmetric_iff_inner_map_self_real
  条件: (T : V ->ₗ[复形] V)
  证明: by
  constructor
  · intro hT v
    apply IsSymmetric.conj_inner_sym hT
  · intro h x y
    rw [← inner_conj_symm x (T y)]
    rw [inner_map_polarization T x y]
    simp only [starRingEnd_apply, star_div₀, star_sub, star_add, star_mul]
    simp only [← starRingEnd_apply]
    rw [h (x + y)]; rw [h (x

Depends on / 依赖: Complex.I, Complex.conj_I, IsSymmetric, IsSymmetric.conj_inner_sym, conj_I, conj_inner_sym, inner_conj_symm, inner_map_polarization, starRingEnd_apply, star_add, star_mul, star_sub
-/
theorem isSymmetric_iff_inner_map_self_real (T : V ->ₗ[Complex] V) :
    IsSymmetric T ↔ forall v : V, conj ⟪T v, v⟫_Complex = ⟪T v, v⟫_Complex := by
  constructor
  · intro hT v
    apply IsSymmetric.conj_inner_sym hT
  · intro h x y
    rw [← inner_conj_symm x (T y)]
    rw [inner_map_polarization T x y]
    simp only [starRingEnd_apply, star_div₀, star_sub, star_add, star_mul]
    simp only [← starRingEnd_apply]
    rw [h (x + y)]; rw [h (x - y)]; rw [h (x + Complex.I • y)]; rw [h (x - Complex.I • y)]
    simp only [Complex.conj_I]
    rw [inner_map_polarization']
    norm_num
    ring

end Complex

set_option backward.isDefEq.respectTransparency false in
/--
theorem `IsSymmetric.inner_map_polarization` / 定理 `IsSymmetric.inner_map_polarization`

English:
theorem IsSymmetric.inner_map_polarization
  given: {T : E ->ₗ[𝕜] E} (hT : T.IsSymmetric) (x y : E)
  proof: by
  rcases @I_mul_I_ax 𝕜 _ with (h | h)
  · simp_rw [h, zero_mul, sub_zero, add_zero, map_add, map_sub, inner_add_left,
      inner_add_right, inner_sub_left, inner_sub_right, hT x, ← inner_conj_symm x (T y)]
    suffices (re ⟪T y, x⟫ : 𝕜) = ⟪T y, x⟫ by
      rw [conj_eq_iff_re.mpr this]
      ring

中文:
定理 IsSymmetric.inner_map_polarization
  条件: {T : E ->ₗ[𝕜] E} (hT : T.IsSymmetric) (x y : E)
  证明: by
  rcases @I_mul_I_ax 𝕜 _ with (h | h)
  · simp_rw [h, zero_mul, sub_zero, add_zero, map_add, map_sub, inner_add_left,
      inner_add_right, inner_sub_left, inner_sub_right, hT x, ← inner_conj_symm x (T y)]
    suffices (re ⟪T y, x⟫ : 𝕜) = ⟪T y, x⟫ by
      rw [conj_eq_iff_re.mpr this]
      ring

Depends on / 依赖: I_mul_I_ax, RCLike, RCLike.conj_, add_zero, conj_, conj_eq_iff_re, conj_eq_iff_re.mpr, inner_add_left, inner_add_right, inner_conj_symm, inner_smul_left, inner_smul_right, inner_sub_left, inner_sub_right, map_add, map_smul, map_sub, mul_zero, re_add_im, simp_rw
-/
theorem IsSymmetric.inner_map_polarization {T : E ->ₗ[𝕜] E} (hT : T.IsSymmetric) (x y : E) :
    ⟪T x, y⟫ =
      (⟪T (x + y), x + y⟫ - ⟪T (x - y), x - y⟫ - I * ⟪T (x + (I : 𝕜) • y), x + (I : 𝕜) • y⟫ +
          I * ⟪T (x - (I : 𝕜) • y), x - (I : 𝕜) • y⟫) /
        4 := by
  rcases @I_mul_I_ax 𝕜 _ with (h | h)
  · simp_rw [h, zero_mul, sub_zero, add_zero, map_add, map_sub, inner_add_left,
      inner_add_right, inner_sub_left, inner_sub_right, hT x, ← inner_conj_symm x (T y)]
    suffices (re ⟪T y, x⟫ : 𝕜) = ⟪T y, x⟫ by
      rw [conj_eq_iff_re.mpr this]
      ring
    rw [← re_add_im ⟪T y]; rw [x⟫]
    simp_rw [h, mul_zero, add_zero]
    norm_cast
  · simp_rw [map_add, map_sub, inner_add_left, inner_add_right, inner_sub_left, inner_sub_right,
      map_smul, inner_smul_left, inner_smul_right, RCLike.conj_I, mul_add, mul_sub, sub_sub,
      ← mul_assoc, mul_neg, h, neg_neg, one_mul, neg_one_mul]
    ring

/--
theorem `isSymmetric_linearIsometryEquiv_conj_iff` / 定理 `isSymmetric_linearIsometryEquiv_conj_iff`

English:
theorem isSymmetric_linearIsometryEquiv_conj_iff
  statement: {F : Type*} [SeminormedAddCommGroup F]
  proof: by
  refine ⟨fun h x y => ?_, fun h x y => ?_⟩
  · simpa [LinearIsometryEquiv.inner_map_eq_flip] using h (f x) (f y)
  · simp [LinearIsometryEquiv.inner_map_eq_flip, h _ (f.symm y)]

中文:
定理 isSymmetric_linearIsometryEquiv_conj_iff
  结论: {F : 类型} [SeminormedAddComm群 F]
  证明: by
  refine ⟨fun h x y => ?_, fun h x y => ?_⟩
  · simpa [LinearIsometryEquiv.inner_map_eq_flip] using h (f x) (f y)
  · simp [LinearIsometryEquiv.inner_map_eq_flip, h _ (f.symm y)]

Depends on / 依赖: LinearIsometryEquiv, LinearIsometryEquiv.inner_map_eq_flip, f.symm, inner_map_eq_flip
-/
theorem isSymmetric_linearIsometryEquiv_conj_iff {F : Type*} [SeminormedAddCommGroup F]
    [InnerProductSpace 𝕜 F] (T : E ->ₗ[𝕜] E) (f : E ≃ₗᵢ[𝕜] F) :
    (f.toLinearMap ∘ₗ T ∘ₗ f.symm.toLinearMap).IsSymmetric ↔ T.IsSymmetric := by
  refine ⟨fun h x y => ?_, fun h x y => ?_⟩
  · simpa [LinearIsometryEquiv.inner_map_eq_flip] using h (f x) (f y)
  · simp [LinearIsometryEquiv.inner_map_eq_flip, h _ (f.symm y)]

end LinearMap

/--
theorem `InnerProductSpace.isSymmetric_rankOne_self` / 定理 `InnerProductSpace.isSymmetric_rankOne_self`

English:
theorem InnerProductSpace.isSymmetric_rankOne_self
  given: (x : E)
  proof: fun _ _ => by simp [inner_smul_left, inner_smul_right, mul_comm]

中文:
定理 内积空间.isSymmetric_rankOne_self
  条件: (x : E)
  证明: fun _ _ => by simp [inner_smul_left, inner_smul_right, mul_comm]
-/
@[simp] theorem InnerProductSpace.isSymmetric_rankOne_self (x : E) :
    (rankOne 𝕜 x x).IsSymmetric := fun _ _ => by simp [inner_smul_left, inner_smul_right, mul_comm]

open ContinuousLinearMap in
/--
theorem `InnerProductSpace.isSymmetricProjection_rankOne_self` / 定理 `InnerProductSpace.isSymmetricProjection_rankOne_self`

English:
theorem InnerProductSpace.isSymmetricProjection_rankOne_self
  given: {x : E} (hx : ‖x‖ = 1)
  proof: isSymmetric_rankOne_self x
.toLinearMap isIdempotentElem := isIdempotentElem_rankOne_self hx

中文:
定理 内积空间.isSymmetricProjection_rankOne_self
  条件: {x : E} (hx : ‖x‖ = 1)
  证明: isSymmetric_rankOne_self x
.toLinearMap isIdempotentElem := isIdempotentElem_rankOne_self hx

Depends on / 依赖: isSymmetric_rankOne_self
-/
theorem InnerProductSpace.isSymmetricProjection_rankOne_self {x : E} (hx : ‖x‖ = 1) :
    (rankOne 𝕜 x x).IsSymmetricProjection where
  isSymmetric := isSymmetric_rankOne_self x
.toLinearMap isIdempotentElem := isIdempotentElem_rankOne_self hx

/--
theorem `LinearMap.IsSymmetric.toLinearMap_symm` / 定理 `LinearMap.IsSymmetric.toLinearMap_symm`

English:
theorem LinearMap.IsSymmetric.toLinearMap_symm
  given: {T : E ≃ₗ[𝕜] E} (hT : T.IsSymmetric)
  proof: fun x y => by simpa using hT (T.symm x) (T.symm y)

中文:
定理 线性映射.IsSymmetric.toLinearMap_symm
  条件: {T : E ≃ₗ[𝕜] E} (hT : T.IsSymmetric)
  证明: fun x y => by simpa using hT (T.symm x) (T.symm y)

Depends on / 依赖: T.symm
-/
theorem LinearMap.IsSymmetric.toLinearMap_symm {T : E ≃ₗ[𝕜] E} (hT : T.IsSymmetric) :
.symm T.symm.IsSymmetric := fun x y => by simpa using hT (T.symm x) (T.symm y)

/--
theorem `LinearEquiv.isSymmetric_symm_iff` / 定理 `LinearEquiv.isSymmetric_symm_iff`

English:
theorem LinearEquiv.isSymmetric_symm_iff
  given: {T : E ≃ₗ[𝕜] E}
  proof: ⟨.toLinearMap_symm, .toLinearMap_symm⟩

中文:
定理 线性等价.isSymmetric_symm_iff
  条件: {T : E ≃ₗ[𝕜] E}
  证明: ⟨.toLinearMap_symm, .toLinearMap_symm⟩
-/
@[simp] theorem LinearEquiv.isSymmetric_symm_iff {T : E ≃ₗ[𝕜] E} :
    T.symm.IsSymmetric ↔ T.IsSymmetric := ⟨.toLinearMap_symm, .toLinearMap_symm⟩

end Seminormed

section Normed

variable {𝕜 E : Type*} [RCLike 𝕜]
variable [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]

local notation "⟪" x ", " y "⟫" => inner 𝕜 x y

namespace LinearMap

/--
theorem `IsSymmetric.continuous` / 定理 `IsSymmetric.continuous`

English:
theorem IsSymmetric.continuous
  given: [CompleteSpace E] {T : E ->ₗ[𝕜] E} (hT : IsSymmetric T)
  proof: by
  -- We prove it by using the closed graph theorem
  refine T.continuous_of_seq_closed_graph fun u x y hu hTu => ?_
  rw [← sub_eq_zero]; rw [← @inner_self_eq_zero 𝕜]
  have hlhs : forall k : Nat, ⟪T (u k) - T x, y - T x⟫ = ⟪u k - x, T (y - T x)⟫ := by
    intro k
    rw [← T.map_sub]; rw [hT]
  

中文:
定理 IsSymmetric.continuous
  条件: [完备空间 E] {T : E ->ₗ[𝕜] E} (hT : IsSymmetric T)
  证明: by
  -- We prove it by using the closed graph theorem
  refine T.continuous_of_seq_closed_graph fun u x y hu hTu => ?_
  rw [← sub_eq_zero]; rw [← @inner_self_eq_zero 𝕜]
  have hlhs : forall k : Nat, ⟪T (u k) - T x, y - T x⟫ = ⟪u k - x, T (y - T x)⟫ := by
    intro k
    rw [← T.map_sub]; rw [hT]
  
-/
theorem IsSymmetric.continuous [CompleteSpace E] {T : E ->ₗ[𝕜] E} (hT : IsSymmetric T) :
    Continuous T := by
  -- We prove it by using the closed graph theorem
  refine T.continuous_of_seq_closed_graph fun u x y hu hTu => ?_
  rw [← sub_eq_zero]; rw [← @inner_self_eq_zero 𝕜]
  have hlhs : forall k : Nat, ⟪T (u k) - T x, y - T x⟫ = ⟪u k - x, T (y - T x)⟫ := by
    intro k
    rw [← T.map_sub]; rw [hT]
  refine tendsto_nhds_unique ((hTu.sub_const _).inner tendsto_const_nhds) ?_
  simp_rw [Function.comp_apply, hlhs]
  rw [← inner_zero_left (T (y - T x))]
  refine Filter.Tendsto.inner ?_ tendsto_const_nhds
  rw [← sub_self x]
  exact hu.sub_const _

/--
theorem `IsSymmetric.inner_map_self_eq_zero` / 定理 `IsSymmetric.inner_map_self_eq_zero`

English:
theorem IsSymmetric.inner_map_self_eq_zero
  given: {T : E ->ₗ[𝕜] E} (hT : T.IsSymmetric)
  proof: by
  simp_rw [LinearMap.ext_iff, zero_apply]
  refine ⟨fun h x => ?_, fun h => by simp_rw [h, inner_zero_left, forall_const]⟩
  rw [← @inner_self_eq_zero 𝕜]; rw [hT.inner_map_polarization]
  simp_rw [h _]
  ring

中文:
定理 IsSymmetric.inner_map_self_eq_zero
  条件: {T : E ->ₗ[𝕜] E} (hT : T.IsSymmetric)
  证明: by
  simp_rw [LinearMap.ext_iff, zero_apply]
  refine ⟨fun h x => ?_, fun h => by simp_rw [h, inner_zero_left, forall_const]⟩
  rw [← @inner_self_eq_zero 𝕜]; rw [hT.inner_map_polarization]
  simp_rw [h _]
  ring

Depends on / 依赖: LinearMap, LinearMap.ext_iff, ext_iff, forall_const, hT.inner_map_polarization, inner_map_polarization, inner_self_eq_zero, inner_zero_left, simp_rw, zero_apply
-/
theorem IsSymmetric.inner_map_self_eq_zero {T : E ->ₗ[𝕜] E} (hT : T.IsSymmetric) :
    (forall x, ⟪T x, x⟫ = 0) ↔ T = 0 := by
  simp_rw [LinearMap.ext_iff, zero_apply]
  refine ⟨fun h x => ?_, fun h => by simp_rw [h, inner_zero_left, forall_const]⟩
  rw [← @inner_self_eq_zero 𝕜]; rw [hT.inner_map_polarization]
  simp_rw [h _]
  ring

/--
theorem `ker_le_ker_of_range` / 定理 `ker_le_ker_of_range`

English:
theorem ker_le_ker_of_range
  statement: {S T : E ->ₗ[𝕜] E} (hS : S.IsSymmetric) (hT : T.IsSymmetric)
  proof: by
  intro v hv
  rw [mem_ker] at hv ⊢
  obtain ⟨y, hy⟩ : exists y, T y = S (S v) := by simpa using @h (S (S v))
  rw [← inner_self_eq_zero (𝕜 := 𝕜)]; rw [← hS]; rw [← hy]; rw [hT]; rw [hv]; rw [inner_zero_right]

中文:
定理 ker_le_ker_of_range
  结论: {S T : E ->ₗ[𝕜] E} (hS : S.IsSymmetric) (hT : T.IsSymmetric)
  证明: by
  intro v hv
  rw [mem_ker] at hv ⊢
  obtain ⟨y, hy⟩ : exists y, T y = S (S v) := by simpa using @h (S (S v))
  rw [← inner_self_eq_zero (𝕜 := 𝕜)]; rw [← hS]; rw [← hy]; rw [hT]; rw [hv]; rw [inner_zero_right]

Depends on / 依赖: inner_self_eq_zero, inner_zero_right, mem_ker
-/
theorem ker_le_ker_of_range {S T : E ->ₗ[𝕜] E} (hS : S.IsSymmetric) (hT : T.IsSymmetric)
    (h : range S <= range T) : ker T <= ker S := by
  intro v hv
  rw [mem_ker] at hv ⊢
  obtain ⟨y, hy⟩ : exists y, T y = S (S v) := by simpa using @h (S (S v))
  rw [← inner_self_eq_zero (𝕜 := 𝕜)]; rw [← hS]; rw [← hy]; rw [hT]; rw [hv]; rw [inner_zero_right]

open Submodule in
/--
theorem `_root_.Submodule.isSymmetric_projection_iff` / 定理 `_root_.Submodule.isSymmetric_projection_iff`

English:
theorem _root_.Submodule.isSymmetric_projection_iff
  proof: by
  rw [projection]
  refine ⟨fun h u hu v hv => ?_, fun h x y => ?_⟩
  · rw [← Subtype.coe_mk u hu, ← Subtype.coe_mk v hv,
      ← Submodule.projectionOnto_apply_left hUV ⟨u, hu⟩, ← U.subtype_apply, ← comp_apply,
      ← h, comp_apply, Submodule.projectionOnto_apply_right hUV ⟨v, hv⟩,
      map_ze

中文:
定理 _root_.子模.isSymmetric_projection_iff
  证明: by
  rw [projection]
  refine ⟨fun h u hu v hv => ?_, fun h x y => ?_⟩
  · rw [← Subtype.coe_mk u hu, ← Subtype.coe_mk v hv,
      ← Submodule.projectionOnto_apply_left hUV ⟨u, hu⟩, ← U.subtype_apply, ← comp_apply,
      ← h, comp_apply, Submodule.projectionOnto_apply_right hUV ⟨v, hv⟩,
      map_ze

Depends on / 依赖: Submodule, Submodule.projectionOnto_apply_left, Submodule.projectionOnto_apply_right, Subtype, Subtype.coe_mk, U.subtype_apply, coe_mk, comp_apply, inner_add_left, inner_add_right, inner_eq_zero_symm, inner_zero_left, isOrtho_iff_inner_eq, map_zero, nth_rw, projection, projectionOnto_apply_left, projectionOnto_apply_right, projection_add_projection_eq_self, subtype_apply
-/
theorem _root_.Submodule.isSymmetric_projection_iff
    {U V : Submodule 𝕜 E} (hUV : IsCompl U V) :
    (U.projection V hUV).IsSymmetric ↔ U ⟂ V := by
  rw [projection]
  refine ⟨fun h u hu v hv => ?_, fun h x y => ?_⟩
  · rw [← Subtype.coe_mk u hu, ← Subtype.coe_mk v hv,
      ← Submodule.projectionOnto_apply_left hUV ⟨u, hu⟩, ← U.subtype_apply, ← comp_apply,
      ← h, comp_apply, Submodule.projectionOnto_apply_right hUV ⟨v, hv⟩,
      map_zero, inner_zero_left]
  · nth_rw 2 [← projection_add_projection_eq_self hUV x]
    nth_rw 1 [← projection_add_projection_eq_self hUV y]
    rw [isOrtho_iff_inner_eq] at h
    simp [inner_add_right, inner_add_left, h, inner_eq_zero_symm]

@[deprecated (since := "2026-05-05")] alias _root_.Submodule.IsCompl.projection_isSymmetric_iff :=
  _root_.Submodule.isSymmetric_projection_iff

open Submodule in
/--
theorem `_root_.Submodule.isSymmetricProjection_projection_iff` / 定理 `_root_.Submodule.isSymmetricProjection_projection_iff`

English:
theorem _root_.Submodule.isSymmetricProjection_projection_iff
  proof: by
  simp [isSymmetricProjection_iff, isSymmetric_projection_iff, isIdempotentElem_projection]

@[deprecated (since := "2026-05-05")] alias
  _root_.Submodule.IsCompl.projection_isSymmetricProjection_iff :=
  _root_.Submodule.isSymmetricProjection_projection_iff

alias ⟨_, _root_.Submodule.isSymmetr

中文:
定理 _root_.子模.isSymmetricProjection_projection_iff
  证明: by
  simp [isSymmetricProjection_iff, isSymmetric_projection_iff, isIdempotentElem_projection]

@[deprecated (since := "2026-05-05")] alias
  _root_.Submodule.IsCompl.projection_isSymmetricProjection_iff :=
  _root_.Submodule.isSymmetricProjection_projection_iff

alias ⟨_, _root_.Submodule.isSymmetr

Depends on / 依赖: isIdempotentElem_projection, isSymmetricProjection_iff, isSymmetric_projection_iff
-/
theorem _root_.Submodule.isSymmetricProjection_projection_iff
    {U V : Submodule 𝕜 E} (hUV : IsCompl U V) :
    (U.projection V hUV).IsSymmetricProjection ↔ U ⟂ V := by
  simp [isSymmetricProjection_iff, isSymmetric_projection_iff, isIdempotentElem_projection]

@[deprecated (since := "2026-05-05")] alias
  _root_.Submodule.IsCompl.projection_isSymmetricProjection_iff :=
  _root_.Submodule.isSymmetricProjection_projection_iff

alias ⟨_, _root_.Submodule.isSymmetricProjection_projection_of_isOrtho⟩ :=
  _root_.Submodule.isSymmetricProjection_projection_iff

@[deprecated (since := "2026-05-05")] alias
  _root_.Submodule.IsCompl.projection_isSymmetricProjection_of_isOrtho :=
  _root_.Submodule.isSymmetricProjection_projection_of_isOrtho

open Submodule LinearMap in
/--
theorem `IsIdempotentElem.isSymmetric_iff_isOrtho_range_ker` / 定理 `IsIdempotentElem.isSymmetric_iff_isOrtho_range_ker`

English:
theorem IsIdempotentElem.isSymmetric_iff_isOrtho_range_ker
  statement: {T : E ->ₗ[𝕜] E}
  proof: by
  rw [← isSymmetric_projection_iff hT.isProj_range.isCompl]; rw [← hT.eq_projection]

中文:
定理 IsIdempotentElem.isSymmetric_iff_isOrtho_range_ker
  结论: {T : E ->ₗ[𝕜] E}
  证明: by
  rw [← isSymmetric_projection_iff hT.isProj_range.isCompl]; rw [← hT.eq_projection]

Depends on / 依赖: eq_projection, hT.eq_projection, hT.isProj_range.isCompl, isCompl, isProj_range, isSymmetric_projection_iff
-/
theorem IsIdempotentElem.isSymmetric_iff_isOrtho_range_ker {T : E ->ₗ[𝕜] E}
    (hT : IsIdempotentElem T) : T.IsSymmetric ↔ (LinearMap.range T) ⟂ (LinearMap.ker T) := by
  rw [← isSymmetric_projection_iff hT.isProj_range.isCompl]; rw [← hT.eq_projection]

/--
theorem `IsSymmetric.orthogonal_range` / 定理 `IsSymmetric.orthogonal_range`

English:
theorem IsSymmetric.orthogonal_range
  given: {T : E ->ₗ[𝕜] E} (hT : LinearMap.IsSymmetric T)
  proof: by
  ext x
  constructor
  · simpa [Submodule.mem_orthogonal, hT _ x] using ext_inner_left 𝕜 (x := T x) (y := 0)
  · simp_all [Submodule.mem_orthogonal, hT _ x]

中文:
定理 IsSymmetric.orthogonal_range
  条件: {T : E ->ₗ[𝕜] E} (hT : 线性映射.IsSymmetric T)
  证明: by
  ext x
  constructor
  · simpa [Submodule.mem_orthogonal, hT _ x] using ext_inner_left 𝕜 (x := T x) (y := 0)
  · simp_all [Submodule.mem_orthogonal, hT _ x]

Depends on / 依赖: Submodule, Submodule.mem_orthogonal, ext_inner_left, mem_orthogonal
-/
theorem IsSymmetric.orthogonal_range {T : E ->ₗ[𝕜] E} (hT : LinearMap.IsSymmetric T) :
    (LinearMap.range T)ᗮ = LinearMap.ker T := by
  ext x
  constructor
  · simpa [Submodule.mem_orthogonal, hT _ x] using ext_inner_left 𝕜 (x := T x) (y := 0)
  · simp_all [Submodule.mem_orthogonal, hT _ x]

open Submodule LinearMap in
/--
theorem `IsIdempotentElem.isSymmetric_iff_orthogonal_range` / 定理 `IsIdempotentElem.isSymmetric_iff_orthogonal_range`

English:
theorem IsIdempotentElem.isSymmetric_iff_orthogonal_range
  statement: {T : E ->ₗ[𝕜] E}
  proof: ⟨fun hT => hT.orthogonal_range, fun hT =>
    h.isSymmetric_iff_isOrtho_range_ker.eq ▸ hT.symm ▸ isOrtho_orthogonal_right _⟩

中文:
定理 IsIdempotentElem.isSymmetric_iff_orthogonal_range
  结论: {T : E ->ₗ[𝕜] E}
  证明: ⟨fun hT => hT.orthogonal_range, fun hT =>
    h.isSymmetric_iff_isOrtho_range_ker.eq ▸ hT.symm ▸ isOrtho_orthogonal_right _⟩

Depends on / 依赖: h.isSymmetric_iff_isOrtho_range_ker.eq, hT.orthogonal_range, hT.symm, isOrtho_orthogonal_right, isSymmetric_iff_isOrtho_range_ker, orthogonal_range
-/
theorem IsIdempotentElem.isSymmetric_iff_orthogonal_range {T : E ->ₗ[𝕜] E}
    (h : IsIdempotentElem T) : T.IsSymmetric ↔ (LinearMap.range T)ᗮ = (LinearMap.ker T) :=
  ⟨fun hT => hT.orthogonal_range, fun hT =>
    h.isSymmetric_iff_isOrtho_range_ker.eq ▸ hT.symm ▸ isOrtho_orthogonal_right _⟩

open LinearMap in
/--
theorem `IsSymmetricProjection.ext_iff` / 定理 `IsSymmetricProjection.ext_iff`

English:
theorem IsSymmetricProjection.ext_iff
  statement: {S T : E ->ₗ[𝕜] E}
  proof: by
  refine ⟨fun h => h ▸ rfl, fun h => ?_⟩
  rw [hS.isIdempotentElem.ext_iff hT.isIdempotentElem]; rw [← hT.isIdempotentElem.isSymmetric_iff_orthogonal_range.mp hT.isSymmetric]; rw [← hS.isIdempotentElem.isSymmetric_iff_orthogonal_range.mp hS.isSymmetric]
  simp [h]

alias ⟨_, IsSymmetricProjection

中文:
定理 是SymmetricProjection.ext_iff
  结论: {S T : E ->ₗ[𝕜] E}
  证明: by
  refine ⟨fun h => h ▸ rfl, fun h => ?_⟩
  rw [hS.isIdempotentElem.ext_iff hT.isIdempotentElem]; rw [← hT.isIdempotentElem.isSymmetric_iff_orthogonal_range.mp hT.isSymmetric]; rw [← hS.isIdempotentElem.isSymmetric_iff_orthogonal_range.mp hS.isSymmetric]
  simp [h]

alias ⟨_, IsSymmetricProjection

Depends on / 依赖: ext_iff, hS.isIdempotentElem.ext_iff, hS.isIdempotentElem.isSymmetric_iff_orthogonal_range.mp, hS.isSymmetric, hT.isIdempotentElem, hT.isIdempotentElem.isSymmetric_iff_orthogonal_range.mp, hT.isSymmetric, isIdempotentElem, isSymmetric, isSymmetric_iff_orthogonal_range
-/
theorem IsSymmetricProjection.ext_iff {S T : E ->ₗ[𝕜] E}
    (hS : S.IsSymmetricProjection) (hT : T.IsSymmetricProjection) :
    S = T ↔ LinearMap.range S = LinearMap.range T := by
  refine ⟨fun h => h ▸ rfl, fun h => ?_⟩
  rw [hS.isIdempotentElem.ext_iff hT.isIdempotentElem]; rw [← hT.isIdempotentElem.isSymmetric_iff_orthogonal_range.mp hT.isSymmetric]; rw [← hS.isIdempotentElem.isSymmetric_iff_orthogonal_range.mp hS.isSymmetric]
  simp [h]

alias ⟨_, IsSymmetricProjection.ext⟩ := IsSymmetricProjection.ext_iff

open LinearMap in
/--
theorem `IsSymmetricProjection.sub_of_range_le_range` / 定理 `IsSymmetricProjection.sub_of_range_le_range`

English:
theorem IsSymmetricProjection.sub_of_range_le_range
  statement: {p q : E ->ₗ[𝕜] E}
  proof: by
  rw [← hq.isIdempotentElem.comp_eq_right_iff] at hqp
  refine ⟨hp.isIdempotentElem.sub hq.isIdempotentElem (LinearMap.ext fun x => ext_inner_left 𝕜
    fun y => ?_) hqp, hq.isSymmetric.sub hp.isSymmetric⟩
  simp_rw [Module.End.mul_apply, ← hp.isSymmetric _, ← hq.isSymmetric _, ← comp_apply, hqp]

中文:
定理 是SymmetricProjection.sub_of_range_le_range
  结论: {p q : E ->ₗ[𝕜] E}
  证明: by
  rw [← hq.isIdempotentElem.comp_eq_right_iff] at hqp
  refine ⟨hp.isIdempotentElem.sub hq.isIdempotentElem (LinearMap.ext fun x => ext_inner_left 𝕜
    fun y => ?_) hqp, hq.isSymmetric.sub hp.isSymmetric⟩
  simp_rw [Module.End.mul_apply, ← hp.isSymmetric _, ← hq.isSymmetric _, ← comp_apply, hqp]

Depends on / 依赖: LinearMap, LinearMap.ext, Module, Module.End.mul_apply, comp_apply, comp_eq_right_iff, ext_inner_left, hp.isIdempotentElem.sub, hp.isSymmetric, hq.isIdempotentElem, hq.isIdempotentElem.comp_eq_right_iff, hq.isSymmetric, hq.isSymmetric.sub, isIdempotentElem, isSymmetric, mul_apply, simp_rw
-/
theorem IsSymmetricProjection.sub_of_range_le_range {p q : E ->ₗ[𝕜] E}
    (hp : p.IsSymmetricProjection) (hq : q.IsSymmetricProjection) (hqp : range p <= range q) :
    (q - p).IsSymmetricProjection := by
  rw [← hq.isIdempotentElem.comp_eq_right_iff] at hqp
  refine ⟨hp.isIdempotentElem.sub hq.isIdempotentElem (LinearMap.ext fun x => ext_inner_left 𝕜
    fun y => ?_) hqp, hq.isSymmetric.sub hp.isSymmetric⟩
  simp_rw [Module.End.mul_apply, ← hp.isSymmetric _, ← hq.isSymmetric _, ← comp_apply, hqp]

/--
theorem `IsSymmetric.isSymmetric_smul_iff` / 定理 `IsSymmetric.isSymmetric_smul_iff`

English:
theorem IsSymmetric.isSymmetric_smul_iff
  statement: {f : E ->ₗ[𝕜] E} (hf : f.IsSymmetric) (hf' : f != 0)
  proof: by
  refine ⟨fun h => ?_, hf.smul⟩
  simp only [ne_eq, LinearMap.ext_iff, zero_apply, ext_iff_inner_left 𝕜 (E := E),
    inner_zero_right] at hf'
  simpa [IsSymmetric, inner_smul_left, inner_smul_right, hf _ _, forall_or_left,
    (forall_comm.eq ▸ hf')] using! h

中文:
定理 IsSymmetric.isSymmetric_smul_iff
  结论: {f : E ->ₗ[𝕜] E} (hf : f.IsSymmetric) (hf' : f != 0)
  证明: by
  refine ⟨fun h => ?_, hf.smul⟩
  simp only [ne_eq, LinearMap.ext_iff, zero_apply, ext_iff_inner_left 𝕜 (E := E),
    inner_zero_right] at hf'
  simpa [IsSymmetric, inner_smul_left, inner_smul_right, hf _ _, forall_or_left,
    (forall_comm.eq ▸ hf')] using! h

Depends on / 依赖: IsSymmetric, LinearMap, LinearMap.ext_iff, ext_iff, ext_iff_inner_left, forall_comm, forall_comm.eq, forall_or_left, hf.smul, inner_smul_left, inner_smul_right, inner_zero_right, ne_eq, zero_apply
-/
theorem IsSymmetric.isSymmetric_smul_iff {f : E ->ₗ[𝕜] E} (hf : f.IsSymmetric) (hf' : f != 0)
    {α : 𝕜} : (α • f).IsSymmetric ↔ IsSelfAdjoint α := by
  refine ⟨fun h => ?_, hf.smul⟩
  simp only [ne_eq, LinearMap.ext_iff, zero_apply, ext_iff_inner_left 𝕜 (E := E),
    inner_zero_right] at hf'
  simpa [IsSymmetric, inner_smul_left, inner_smul_right, hf _ _, forall_or_left,
    (forall_comm.eq ▸ hf')] using! h

end LinearMap

end Normed
