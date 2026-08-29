/-
Copyright (c) 2018 Patrick Massot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Massot, Johannes Hölzl
-/
module

public import Mathlib.Algebra.Algebra.Pi
public import Mathlib.Algebra.Algebra.Prod
public import Mathlib.Algebra.Algebra.Rat
public import Mathlib.Algebra.Algebra.RestrictScalars
public import Mathlib.Algebra.Module.Rat
public import Mathlib.Analysis.Normed.Field.Lemmas
public import Mathlib.Analysis.Normed.MulAction

/-!
# Normed spaces

In this file we define (semi)normed spaces and algebras. We also prove some theorems
about these definitions.
-/

@[expose] public section

variable {𝕜 𝕜' E F α : Type*}

open Filter Metric Function Set Topology Bornology
open scoped NNReal ENNReal uniformity

section SeminormedAddCommGroup

/-- A normed space over a normed field is a vector space endowed with a norm which satisfies the
equality `‖c • x‖ = ‖c‖ ‖x‖`. We require only `‖c • x‖ ≤ ‖c‖ ‖x‖` in the definition, then prove
`‖c • x‖ = ‖c‖ ‖x‖` in `norm_smul`.

Note that since this requires `SeminormedAddCommGroup` and not `NormedAddCommGroup`, this
typeclass can be used for "seminormed spaces" too, just as `Module` can be used for
"semimodules". -/
@[ext]
/--
Definition of `NormedSpace` / `NormedSpace` 的定义

English:
class NormedSpace
  parameters: (𝕜 : Type*) (E : Type*) [NormedField 𝕜] [SeminormedAddCommGroup E]
  extends: Module 𝕜 E
  axioms and operations (1):
    - norm_smul_le : forall (a : 𝕜) (b : E), ‖a • b‖ <= ‖a‖ * ‖b‖

中文:
类 赋范空间
  参数: (𝕜 : 类型) (E : 类型) [赋范域 𝕜] [SeminormedAddComm群 E]
  继承: 模 𝕜 E
  公理与运算 (1 个):
    - norm_smul_le : 对任意 (a : 𝕜) (b : E), ‖a • b‖ <= ‖a‖ * ‖b‖
-/
class NormedSpace (𝕜 : Type*) (E : Type*) [NormedField 𝕜] [SeminormedAddCommGroup E]
    extends Module 𝕜 E where
  protected norm_smul_le : forall (a : 𝕜) (b : E), ‖a • b‖ <= ‖a‖ * ‖b‖

attribute [inherit_doc NormedSpace] NormedSpace.norm_smul_le

variable [NormedField 𝕜] [SeminormedAddCommGroup E] [SeminormedAddCommGroup F]
variable [NormedSpace 𝕜 E] [NormedSpace 𝕜 F]

-- see Note [lower instance priority]
instance (priority := 100) NormedSpace.toNormSMulClass : NormSMulClass 𝕜 E :=
  haveI : IsBoundedSMul 𝕜 E := .of_norm_smul_le NormedSpace.norm_smul_le
  NormedDivisionRing.toNormSMulClass

/--
Instance `NormedSpace.toIsBoundedSMul` / 实例 `NormedSpace.toIsBoundedSMul`

English:
instance NormedSpace.toIsBoundedSMul
  signature: : IsBoundedSMul 𝕜 E
  body: inferInstance

中文:
实例 赋范空间.toIsBoundedSMul
  签名: : 是BoundedSMul 𝕜 E
  定义体: inferInstance
-/
instance NormedSpace.toIsBoundedSMul : IsBoundedSMul 𝕜 E := inferInstance

/--
Instance `NormedField.toNormedSpace` / 实例 `NormedField.toNormedSpace`

English:
instance NormedField.toNormedSpace
  signature: : NormedSpace 𝕜 𝕜 where norm_smul_le a b
  body: norm_mul_le a b

中文:
实例 赋范域.toNormedSpace
  签名: : 赋范空间 𝕜 𝕜 where norm_smul_le a b
  定义体: norm_mul_le a b

Depends on / 依赖: norm_mul_le
-/
instance NormedField.toNormedSpace : NormedSpace 𝕜 𝕜 where norm_smul_le a b := norm_mul_le a b

variable (𝕜) in
/--
theorem `norm_zsmul` / 定理 `norm_zsmul`

English:
theorem norm_zsmul
  given: (n : Int) (x : E)
  statement: ‖n • x‖ = ‖(n : 𝕜)‖ * ‖x‖
  proof: by
  rw [← norm_smul]; rw [← Int.smul_one_eq_cast]; rw [smul_assoc]; rw [one_smul]

中文:
定理 norm_zsmul
  条件: (n : 整数) (x : E)
  结论: ‖n • x‖ = ‖(n : 𝕜)‖ * ‖x‖
  证明: by
  rw [← norm_smul]; rw [← Int.smul_one_eq_cast]; rw [smul_assoc]; rw [one_smul]

Depends on / 依赖: Int.smul_one_eq_cast, norm_smul, one_smul, smul_assoc, smul_one_eq_cast
-/
theorem norm_zsmul (n : Int) (x : E) : ‖n • x‖ = ‖(n : 𝕜)‖ * ‖x‖ := by
  rw [← norm_smul]; rw [← Int.smul_one_eq_cast]; rw [smul_assoc]; rw [one_smul]

/--
theorem `norm_intCast_eq_abs_mul_norm_one` / 定理 `norm_intCast_eq_abs_mul_norm_one`

English:
theorem norm_intCast_eq_abs_mul_norm_one
  given: (α) [SeminormedRing α] [NormSMulClass Int α] (n : Int)
  proof: by
  rw [← zsmul_one]; rw [norm_smul]; rw [Int.norm_eq_abs]; rw [Int.cast_abs]

中文:
定理 norm_intCast_eq_abs_mul_norm_one
  条件: (α) [Seminormed环 α] [NormSMul类 整数 α] (n : 整数)
  证明: by
  rw [← zsmul_one]; rw [norm_smul]; rw [Int.norm_eq_abs]; rw [Int.cast_abs]

Depends on / 依赖: Int.cast_abs, Int.norm_eq_abs, cast_abs, norm_eq_abs, norm_smul, zsmul_one
-/
theorem norm_intCast_eq_abs_mul_norm_one (α) [SeminormedRing α] [NormSMulClass Int α] (n : Int) :
    ‖(n : α)‖ = |n| * ‖(1 : α)‖ := by
  rw [← zsmul_one]; rw [norm_smul]; rw [Int.norm_eq_abs]; rw [Int.cast_abs]

/--
theorem `norm_natCast_eq_mul_norm_one` / 定理 `norm_natCast_eq_mul_norm_one`

English:
theorem norm_natCast_eq_mul_norm_one
  given: (α) [SeminormedRing α] [NormSMulClass Int α] (n : Nat)
  proof: by
  simpa using norm_intCast_eq_abs_mul_norm_one α n

@[simp]

中文:
定理 norm_natCast_eq_mul_norm_one
  条件: (α) [Seminormed环 α] [NormSMul类 整数 α] (n : 自然数)
  证明: by
  simpa using norm_intCast_eq_abs_mul_norm_one α n

@[simp]

Depends on / 依赖: norm_intCast_eq_abs_mul_norm_one
-/
theorem norm_natCast_eq_mul_norm_one (α) [SeminormedRing α] [NormSMulClass Int α] (n : Nat) :
    ‖(n : α)‖ = n * ‖(1 : α)‖ := by
  simpa using norm_intCast_eq_abs_mul_norm_one α n

@[simp]
/--
lemma `norm_natCast` / 引理 `norm_natCast`

English:
lemma norm_natCast
  statement: {α : Type*} [SeminormedRing α] [NormOneClass α] [NormSMulClass Int α]
  proof: by
  simpa using norm_natCast_eq_mul_norm_one α a

中文:
引理 norm_natCast
  结论: {α : 类型} [Seminormed环 α] [NormOne类 α] [NormSMul类 整数 α]
  证明: by
  simpa using norm_natCast_eq_mul_norm_one α a

Depends on / 依赖: norm_natCast_eq_mul_norm_one
-/
lemma norm_natCast {α : Type*} [SeminormedRing α] [NormOneClass α] [NormSMulClass Int α]
    (a : Nat) : ‖(a : α)‖ = a := by
  simpa using norm_natCast_eq_mul_norm_one α a

/--
theorem `eventually_nhds_norm_smul_sub_lt` / 定理 `eventually_nhds_norm_smul_sub_lt`

English:
theorem eventually_nhds_norm_smul_sub_lt
  given: (c : 𝕜) (x : E) {ε : Real} (h : 0 < ε)
  proof: have : Tendsto (fun y => ‖c • (y - x)‖) (𝓝 x) (𝓝 0) :=
    Continuous.tendsto' (by fun_prop) _ _ (by simp)
  this.eventually (gt_mem_nhds h)

中文:
定理 eventually_nhds_norm_smul_sub_lt
  条件: (c : 𝕜) (x : E) {ε : 实数} (h : 0 < ε)
  证明: have : Tendsto (fun y => ‖c • (y - x)‖) (𝓝 x) (𝓝 0) :=
    Continuous.tendsto' (by fun_prop) _ _ (by simp)
  this.eventually (gt_mem_nhds h)

Depends on / 依赖: Continuous, Continuous.tendsto, Tendsto, eventually, fun_prop, gt_mem_nhds, tendsto, this.eventually
-/
theorem eventually_nhds_norm_smul_sub_lt (c : 𝕜) (x : E) {ε : Real} (h : 0 < ε) :
    forallᶠ y in 𝓝 x, ‖c • (y - x)‖ < ε :=
  have : Tendsto (fun y => ‖c • (y - x)‖) (𝓝 x) (𝓝 0) :=
    Continuous.tendsto' (by fun_prop) _ _ (by simp)
  this.eventually (gt_mem_nhds h)

/--
theorem `Filter.Tendsto.zero_smul_isBoundedUnder_le` / 定理 `Filter.Tendsto.zero_smul_isBoundedUnder_le`

English:
theorem Filter.Tendsto.zero_smul_isBoundedUnder_le
  statement: {f : α -> 𝕜} {g : α -> E} {l : Filter α}
  proof: hf.op_zero_isBoundedUnder_le hg (· • ·) norm_smul_le

中文:
定理 滤子.收敛.zero_smul_isBoundedUnder_le
  结论: {f : α -> 𝕜} {g : α -> E} {l : 滤子 α}
  证明: hf.op_zero_isBoundedUnder_le hg (· • ·) norm_smul_le

Depends on / 依赖: hf.op_zero_isBoundedUnder_le, norm_smul_le, op_zero_isBoundedUnder_le
-/
theorem Filter.Tendsto.zero_smul_isBoundedUnder_le {f : α -> 𝕜} {g : α -> E} {l : Filter α}
    (hf : Tendsto f l (𝓝 0)) (hg : IsBoundedUnder (· <= ·) l (Norm.norm ∘ g)) :
    Tendsto (fun x => f x • g x) l (𝓝 0) :=
  hf.op_zero_isBoundedUnder_le hg (· • ·) norm_smul_le

/--
theorem `Filter.IsBoundedUnder.smul_tendsto_zero` / 定理 `Filter.IsBoundedUnder.smul_tendsto_zero`

English:
theorem Filter.IsBoundedUnder.smul_tendsto_zero
  statement: {f : α -> 𝕜} {g : α -> E} {l : Filter α}
  proof: hg.op_zero_isBoundedUnder_le hf (flip (· • ·)) fun x y =>
    (norm_smul_le y x).trans_eq (mul_comm _ _)

中文:
定理 滤子.IsBoundedUnder.smul_tendsto_zero
  结论: {f : α -> 𝕜} {g : α -> E} {l : 滤子 α}
  证明: hg.op_zero_isBoundedUnder_le hf (flip (· • ·)) fun x y =>
    (norm_smul_le y x).trans_eq (mul_comm _ _)

Depends on / 依赖: hg.op_zero_isBoundedUnder_le, mul_comm, norm_smul_le, op_zero_isBoundedUnder_le, trans_eq
-/
theorem Filter.IsBoundedUnder.smul_tendsto_zero {f : α -> 𝕜} {g : α -> E} {l : Filter α}
    (hf : IsBoundedUnder (· <= ·) l (norm ∘ f)) (hg : Tendsto g l (𝓝 0)) :
    Tendsto (fun x => f x • g x) l (𝓝 0) :=
  hg.op_zero_isBoundedUnder_le hf (flip (· • ·)) fun x y =>
    (norm_smul_le y x).trans_eq (mul_comm _ _)

/--
Instance `NormedSpace.discreteTopology_zmultiples` / 实例 `NormedSpace.discreteTopology_zmultiples`

English:
instance NormedSpace.discreteTopology_zmultiples
  body: by
  have : IsAddTorsionFree E := .of_module_rat E
  rcases eq_or_ne e 0 with (rfl | he)
  · rw [AddSubgroup.zmultiples_zero_eq_bot]
    exact Subsingleton.discreteTopology (α := ↑(⊥ : Subspace Rat E))
  · rw [discreteTopology_iff_isOpen_singleton_zero, isOpen_induced_iff]
    refine ⟨Metric.ball 0 ‖e‖, Metric.isOpen_ball, ?_⟩
    ext ⟨x, hx⟩
    obtain ⟨k, rfl⟩ := AddSubgroup.mem_zmultiples_iff.mp hx
    rw [mem_preimage]; rw [mem_ball_zero_iff]; rw [AddSubgroup.coe_mk]; rw [mem_singleton_iff]; rw [Subtype.ext_iff]; rw [AddSubgroup.coe_mk]; rw [AddSubgroup.coe_zero]; rw [norm_zsmul Rat k e]; rw [Int.norm_cast_rat]; rw [Int.norm_eq_abs]; rw [mul_lt_iff_lt_one_left (norm_pos_iff.mpr he)]; rw [← @Int.cast_one Real _]; rw [← Int.cast_abs]; rw [Int.cast_lt]; rw [Int.abs_lt_one_iff]; rw [smul_eq_zero]; rw [or_iff_left he]

中文:
实例 赋范空间.discreteTopology_zmultiples
  定义体: by
  have : IsAddTorsionFree E := .of_module_rat E
  rcases eq_or_ne e 0 with (rfl | he)
  · rw [AddSubgroup.zmultiples_zero_eq_bot]
    exact Subsingleton.discreteTopology (α := ↑(⊥ : Subspace Rat E))
  · rw [discreteTopology_iff_isOpen_singleton_zero, isOpen_induced_iff]
    refine ⟨Metric.ball 0 ‖e‖, Metric.isOpen_ball, ?_⟩
    ext ⟨x, hx⟩
    obtain ⟨k, rfl⟩ := AddSubgroup.mem_zmultiples_iff.mp hx
    rw [mem_preimage]; rw [mem_ball_zero_iff]; rw [AddSubgroup.coe_mk]; rw [mem_singleton_iff]; rw [Subtype.ext_iff]; rw [AddSubgroup.coe_mk]; rw [AddSubgroup.coe_zero]; rw [norm_zsmul Rat k e]; rw [Int.norm_cast_rat]; rw [Int.norm_eq_abs]; rw [mul_lt_iff_lt_one_left (norm_pos_iff.mpr he)]; rw [← @Int.cast_one Real _]; rw [← Int.cast_abs]; rw [Int.cast_lt]; rw [Int.abs_lt_one_iff]; rw [smul_eq_zero]; rw [or_iff_left he]

Depends on / 依赖: AddSubgroup, AddSubgroup.coe_mk, AddSubgroup.mem_zmultiples_iff.mp, AddSubgroup.zmultiples_zero_eq_bot, IsAddTorsionFree, Metric, Metric.ball, Metric.isOpen_ball, Subsingleton, Subsingleton.discreteTopology, Subspace, Subtype, Subtype.ext_iff, coe_mk, discreteTopology, discreteTopology_iff_isOpen_singleton_zero, eq_or_ne, ext_iff, isOpen_ball, isOpen_induced_iff
-/
instance NormedSpace.discreteTopology_zmultiples
    {E : Type*} [NormedAddCommGroup E] [NormedSpace Rat E] (e : E) :
DiscreteTopology AddSubgroup.zmultiples e := by
  have : IsAddTorsionFree E := .of_module_rat E
  rcases eq_or_ne e 0 with (rfl | he)
  · rw [AddSubgroup.zmultiples_zero_eq_bot]
    exact Subsingleton.discreteTopology (α := ↑(⊥ : Subspace Rat E))
  · rw [discreteTopology_iff_isOpen_singleton_zero, isOpen_induced_iff]
    refine ⟨Metric.ball 0 ‖e‖, Metric.isOpen_ball, ?_⟩
    ext ⟨x, hx⟩
    obtain ⟨k, rfl⟩ := AddSubgroup.mem_zmultiples_iff.mp hx
    rw [mem_preimage]; rw [mem_ball_zero_iff]; rw [AddSubgroup.coe_mk]; rw [mem_singleton_iff]; rw [Subtype.ext_iff]; rw [AddSubgroup.coe_mk]; rw [AddSubgroup.coe_zero]; rw [norm_zsmul Rat k e]; rw [Int.norm_cast_rat]; rw [Int.norm_eq_abs]; rw [mul_lt_iff_lt_one_left (norm_pos_iff.mpr he)]; rw [← @Int.cast_one Real _]; rw [← Int.cast_abs]; rw [Int.cast_lt]; rw [Int.abs_lt_one_iff]; rw [smul_eq_zero]; rw [or_iff_left he]

section Real
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E] [Nontrivial E]

/--
lemma `Metric.diam_sphere_eq` / 引理 `Metric.diam_sphere_eq`

English:
lemma Metric.diam_sphere_eq
  given: (x : E) {r : Real} (hr : 0 <= r)
  statement: diam (sphere x r) = 2 * r
  proof: by
  apply le_antisymm
    (diam_mono sphere_subset_closedBall isBounded_closedBall |>.trans <| diam_closedBall hr)
  obtain ⟨y, hy⟩ := exists_ne (0 : E)
  calc
    2 * r = dist (x + r • ‖y‖⁻¹ • y) (x - r • ‖y‖⁻¹ • y) := by
      simp [dist_eq_norm, ← two_nsmul, ← smul_assoc, norm_smul, abs_of_nonneg hr, hy, mul_assoc]
    _ <= diam (sphere x r) := by
      apply dist_le_diam_of_mem isBounded_sphere <;> simp [norm_smul, hy, abs_of_nonneg hr]

中文:
引理 Metric.diam_sphere_eq
  条件: (x : E) {r : 实数} (hr : 0 <= r)
  结论: diam (sphere x r) = 2 * r
  证明: by
  apply le_antisymm
    (diam_mono sphere_subset_closedBall isBounded_closedBall |>.trans <| diam_closedBall hr)
  obtain ⟨y, hy⟩ := exists_ne (0 : E)
  calc
    2 * r = dist (x + r • ‖y‖⁻¹ • y) (x - r • ‖y‖⁻¹ • y) := by
      simp [dist_eq_norm, ← two_nsmul, ← smul_assoc, norm_smul, abs_of_nonneg hr, hy, mul_assoc]
    _ <= diam (sphere x r) := by
      apply dist_le_diam_of_mem isBounded_sphere <;> simp [norm_smul, hy, abs_of_nonneg hr]

Depends on / 依赖: abs_of_nonneg, diam_closedBall, diam_mono, dist_eq_norm, dist_le_diam_of_mem, exists_ne, isBounded_closedBall, isBounded_sphere, le_antisymm, mul_assoc, norm_smul, smul_assoc, sphere, sphere_subset_closedBall, two_nsmul
-/
lemma Metric.diam_sphere_eq (x : E) {r : Real} (hr : 0 <= r) : diam (sphere x r) = 2 * r := by
  apply le_antisymm
    (diam_mono sphere_subset_closedBall isBounded_closedBall |>.trans <| diam_closedBall hr)
  obtain ⟨y, hy⟩ := exists_ne (0 : E)
  calc
    2 * r = dist (x + r • ‖y‖⁻¹ • y) (x - r • ‖y‖⁻¹ • y) := by
      simp [dist_eq_norm, ← two_nsmul, ← smul_assoc, norm_smul, abs_of_nonneg hr, hy, mul_assoc]
    _ <= diam (sphere x r) := by
      apply dist_le_diam_of_mem isBounded_sphere <;> simp [norm_smul, hy, abs_of_nonneg hr]

/--
lemma `Metric.diam_closedBall_eq` / 引理 `Metric.diam_closedBall_eq`

English:
lemma Metric.diam_closedBall_eq
  given: (x : E) {r : Real} (hr : 0 <= r)
  statement: diam (closedBall x r) = 2 * r
  proof: le_antisymm (diam_closedBall hr)
.symm.le.trans diam_mono sphere_subset_closedBall isBounded_closedBall diam_sphere_eq x hr

中文:
引理 Metric.diam_closedBall_eq
  条件: (x : E) {r : 实数} (hr : 0 <= r)
  结论: diam (closedBall x r) = 2 * r
  证明: le_antisymm (diam_closedBall hr)
.symm.le.trans diam_mono sphere_subset_closedBall isBounded_closedBall diam_sphere_eq x hr

Depends on / 依赖: diam_closedBall, diam_mono, diam_sphere_eq, isBounded_closedBall, le_antisymm, sphere_subset_closedBall, symm.le.trans
-/
lemma Metric.diam_closedBall_eq (x : E) {r : Real} (hr : 0 <= r) : diam (closedBall x r) = 2 * r :=
le_antisymm (diam_closedBall hr)
.symm.le.trans diam_mono sphere_subset_closedBall isBounded_closedBall diam_sphere_eq x hr

/--
lemma `Metric.diam_ball_eq` / 引理 `Metric.diam_ball_eq`

English:
lemma Metric.diam_ball_eq
  given: (x : E) {r : Real} (hr : 0 <= r)
  statement: diam (ball x r) = 2 * r
  proof: by
  /- This proof could be simplified with `Metric.diam_closure` and `closure_ball`,
  but we opt for this proof to minimize dependencies. -/
refine le_antisymm (diam_ball hr)
    mul_le_of_forall_lt_of_nonneg (by positivity) diam_nonneg fun a ha ha' r' hr' hr'' => ?_
  calc a * r' <= 2 * r' := by gcongr
    _ <= _ := by simpa only [← Metric.diam_sphere_eq x hr'.le]
      using diam_mono (sphere_subset_ball hr'') isBounded_ball

中文:
引理 Metric.diam_ball_eq
  条件: (x : E) {r : 实数} (hr : 0 <= r)
  结论: diam (ball x r) = 2 * r
  证明: by
  /- This proof could be simplified with `Metric.diam_closure` and `closure_ball`,
  but we opt for this proof to minimize dependencies. -/
refine le_antisymm (diam_ball hr)
    mul_le_of_forall_lt_of_nonneg (by positivity) diam_nonneg fun a ha ha' r' hr' hr'' => ?_
  calc a * r' <= 2 * r' := by gcongr
    _ <= _ := by simpa only [← Metric.diam_sphere_eq x hr'.le]
      using diam_mono (sphere_subset_ball hr'') isBounded_ball
-/
lemma Metric.diam_ball_eq (x : E) {r : Real} (hr : 0 <= r) : diam (ball x r) = 2 * r := by
  /- This proof could be simplified with `Metric.diam_closure` and `closure_ball`,
  but we opt for this proof to minimize dependencies. -/
refine le_antisymm (diam_ball hr)
    mul_le_of_forall_lt_of_nonneg (by positivity) diam_nonneg fun a ha ha' r' hr' hr'' => ?_
  calc a * r' <= 2 * r' := by gcongr
    _ <= _ := by simpa only [← Metric.diam_sphere_eq x hr'.le]
      using diam_mono (sphere_subset_ball hr'') isBounded_ball

end Real

open NormedField

/--
Instance `ULift.normedSpace` / 实例 `ULift.normedSpace`

English:
instance ULift.normedSpace
  signature: : NormedSpace 𝕜 (ULift E)
  body: { __ := ULift.seminormedAddCommGroup (E := E),
    __ := ULift.module'
    norm_smul_le := fun s x => (norm_smul_le s x.down :) }

中文:
实例 类型层提升.normedSpace
  签名: : 赋范空间 𝕜 (类型层提升 E)
  定义体: { __ := ULift.seminormedAddCommGroup (E := E),
    __ := ULift.module'
    norm_smul_le := fun s x => (norm_smul_le s x.down :) }

Depends on / 依赖: ULift.module, ULift.seminormedAddCommGroup, module, norm_smul_le, seminormedAddCommGroup, x.down
-/
instance ULift.normedSpace : NormedSpace 𝕜 (ULift E) :=
  { __ := ULift.seminormedAddCommGroup (E := E),
    __ := ULift.module'
    norm_smul_le := fun s x => (norm_smul_le s x.down :) }

/--
Instance `Prod.normedSpace` / 实例 `Prod.normedSpace`

English:
instance Prod.normedSpace
  signature: : NormedSpace 𝕜 (E × F)
  body: { Prod.seminormedAddCommGroup (E := E) (F := F), Prod.instModule with
    norm_smul_le := fun s x => by
      simp only [norm_smul, Prod.norm_def, le_rfl] }

中文:
实例 积类型.normedSpace
  签名: : 赋范空间 𝕜 (E × F)
  定义体: { Prod.seminormedAddCommGroup (E := E) (F := F), Prod.instModule with
    norm_smul_le := fun s x => by
      simp only [norm_smul, Prod.norm_def, le_rfl] }

Depends on / 依赖: Prod.instModule, Prod.norm_def, Prod.seminormedAddCommGroup, instModule, le_rfl, norm_def, norm_smul, norm_smul_le, seminormedAddCommGroup
-/
instance Prod.normedSpace : NormedSpace 𝕜 (E × F) :=
  { Prod.seminormedAddCommGroup (E := E) (F := F), Prod.instModule with
    norm_smul_le := fun s x => by
      simp only [norm_smul, Prod.norm_def, le_rfl] }

/--
Instance `Pi.normedSpace` / 实例 `Pi.normedSpace`

English:
instance Pi.normedSpace
  signature: {ι : Type*} {E : ι -> Type*} [Fintype ι] [forall i, SeminormedAddCommGroup (E i)]
  body: by
    simp_rw [← coe_nnnorm, ← NNReal.coe_mul, NNReal.coe_le_coe, Pi.nnnorm_def,
      NNReal.mul_finset_sup]
    exact Finset.sup_mono_fun fun _ _ => norm_smul_le a _

中文:
实例 依赖函数类型.normedSpace
  签名: {ι : 类型} {E : ι -> 类型} [有限类型 ι] [对任意 i, SeminormedAddComm群 (E i)]
  定义体: by
    simp_rw [← coe_nnnorm, ← NNReal.coe_mul, NNReal.coe_le_coe, Pi.nnnorm_def,
      NNReal.mul_finset_sup]
    exact Finset.sup_mono_fun fun _ _ => norm_smul_le a _

Depends on / 依赖: Finset, Finset.sup_mono_fun, NNReal, NNReal.coe_le_coe, NNReal.coe_mul, NNReal.mul_finset_sup, Pi.nnnorm_def, coe_le_coe, coe_mul, coe_nnnorm, mul_finset_sup, nnnorm_def, norm_smul_le, simp_rw, sup_mono_fun
-/
instance Pi.normedSpace {ι : Type*} {E : ι -> Type*} [Fintype ι] [forall i, SeminormedAddCommGroup (E i)]
    [forall i, NormedSpace 𝕜 (E i)] : NormedSpace 𝕜 (forall i, E i) where
  norm_smul_le a f := by
    simp_rw [← coe_nnnorm, ← NNReal.coe_mul, NNReal.coe_le_coe, Pi.nnnorm_def,
      NNReal.mul_finset_sup]
    exact Finset.sup_mono_fun fun _ _ => norm_smul_le a _

/--
Instance `SeparationQuotient.instNormedSpace` / 实例 `SeparationQuotient.instNormedSpace`

English:
instance SeparationQuotient.instNormedSpace
  signature: : NormedSpace 𝕜 (SeparationQuotient E) where
  body: norm_smul_le

中文:
实例 SeparationQuotient.instNormedSpace
  签名: : 赋范空间 𝕜 (SeparationQuotient E) where
  定义体: norm_smul_le

Depends on / 依赖: norm_smul_le
-/
instance SeparationQuotient.instNormedSpace : NormedSpace 𝕜 (SeparationQuotient E) where
  norm_smul_le := norm_smul_le

/--
Instance `MulOpposite.instNormedSpace` / 实例 `MulOpposite.instNormedSpace`

English:
instance MulOpposite.instNormedSpace
  signature: : NormedSpace 𝕜 Eᵐᵒᵖ where
  body: norm_smul_le _ x.unop

中文:
实例 MulOpposite.instNormedSpace
  签名: : 赋范空间 𝕜 Eᵐᵒᵖ where
  定义体: norm_smul_le _ x.unop

Depends on / 依赖: norm_smul_le, x.unop
-/
instance MulOpposite.instNormedSpace : NormedSpace 𝕜 Eᵐᵒᵖ where
  norm_smul_le _ x := norm_smul_le _ x.unop

/--
Instance `Submodule.normedSpace` / 实例 `Submodule.normedSpace`

English:
instance Submodule.normedSpace
  signature: {𝕜 R : Type*} [SMul 𝕜 R] [NormedField 𝕜] [Ring R] {E : Type*}
  body: norm_smul_le c (x : E)

中文:
实例 子模.normedSpace
  签名: {𝕜 R : 类型} [标量乘法 𝕜 R] [赋范域 𝕜] [环 R] {E : 类型}
  定义体: norm_smul_le c (x : E)

Depends on / 依赖: norm_smul_le
-/
instance Submodule.normedSpace {𝕜 R : Type*} [SMul 𝕜 R] [NormedField 𝕜] [Ring R] {E : Type*}
    [SeminormedAddCommGroup E] [NormedSpace 𝕜 E] [Module R E] [IsScalarTower 𝕜 R E]
    (s : Submodule R E) : NormedSpace 𝕜 s where
  norm_smul_le c x := norm_smul_le c (x : E)

variable {S 𝕜 R E : Type*} [SMul 𝕜 R] [NormedField 𝕜] [Ring R] [SeminormedAddCommGroup E]
variable [NormedSpace 𝕜 E] [Module R E] [IsScalarTower 𝕜 R E] [SetLike S E] [AddSubgroupClass S E]
variable [SMulMemClass S R E] (s : S)

instance (priority := 75) SubmoduleClass.toNormedSpace : NormedSpace 𝕜 s where
  norm_smul_le c x := norm_smul_le c (x : E)

end SeminormedAddCommGroup

/--
Definition of `NormedSpace.induced` / `NormedSpace.induced` 的定义

English:
abbreviation NormedSpace.induced
  signature: {F : Type*} (𝕜 E G : Type*) [NormedField 𝕜] [AddCommGroup E] [Module 𝕜 E]
  body: letI := SeminormedAddCommGroup.induced E G f
  { norm_smul_le a b := by simpa only [← map_smul f a b] using! norm_smul_le a (f b) }

中文:
缩写 赋范空间.induced
  签名: {F : 类型} (𝕜 E G : 类型) [赋范域 𝕜] [加法交换群 E] [模 𝕜 E]
  定义体: letI := SeminormedAddCommGroup.induced E G f
  { norm_smul_le a b := by simpa only [← map_smul f a b] using! norm_smul_le a (f b) }

Depends on / 依赖: SeminormedAddCommGroup, SeminormedAddCommGroup.induced, induced, map_smul, norm_smul_le
-/
abbrev NormedSpace.induced {F : Type*} (𝕜 E G : Type*) [NormedField 𝕜] [AddCommGroup E] [Module 𝕜 E]
    [SeminormedAddCommGroup G] [NormedSpace 𝕜 G] [FunLike F E G] [LinearMapClass F 𝕜 E G] (f : F) :
    @NormedSpace 𝕜 E _ (SeminormedAddCommGroup.induced E G f) :=
  letI := SeminormedAddCommGroup.induced E G f
  { norm_smul_le a b := by simpa only [← map_smul f a b] using! norm_smul_le a (f b) }

section NontriviallyNormedSpace

variable (𝕜 E)
variable [NontriviallyNormedField 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E] [Nontrivial E]
include 𝕜

/--
theorem `NormedSpace.exists_lt_norm` / 定理 `NormedSpace.exists_lt_norm`

English:
theorem NormedSpace.exists_lt_norm
  given: (c : Real)
  statement: exists x : E, c < ‖x‖
  proof: by
  rcases exists_ne (0 : E) with ⟨x, hx⟩
  rcases NormedField.exists_lt_norm 𝕜 (c / ‖x‖) with ⟨r, hr⟩
  use r • x
  rwa [norm_smul, ← div_lt_iff₀]
  rwa [norm_pos_iff]

中文:
定理 赋范空间.存在_lt_norm
  条件: (c : 实数)
  结论: 存在 x : E, c < ‖x‖
  证明: by
  rcases exists_ne (0 : E) with ⟨x, hx⟩
  rcases NormedField.exists_lt_norm 𝕜 (c / ‖x‖) with ⟨r, hr⟩
  use r • x
  rwa [norm_smul, ← div_lt_iff₀]
  rwa [norm_pos_iff]

Depends on / 依赖: NormedField, NormedField.exists_lt_norm, exists_lt_norm, exists_ne, norm_pos_iff, norm_smul
-/
theorem NormedSpace.exists_lt_norm (c : Real) : exists x : E, c < ‖x‖ := by
  rcases exists_ne (0 : E) with ⟨x, hx⟩
  rcases NormedField.exists_lt_norm 𝕜 (c / ‖x‖) with ⟨r, hr⟩
  use r • x
  rwa [norm_smul, ← div_lt_iff₀]
  rwa [norm_pos_iff]

/--
theorem `NormedSpace.unbounded_univ` / 定理 `NormedSpace.unbounded_univ`

English:
theorem NormedSpace.unbounded_univ
  statement: ¬Bornology.IsBounded (univ : Set E)
  proof: fun h =>
  let ⟨R, hR⟩ := isBounded_iff_forall_norm_le.1 h
  let ⟨x, hx⟩ := NormedSpace.exists_lt_norm 𝕜 E R
  hx.not_ge (hR x trivial)

中文:
定理 赋范空间.unbounded_univ
  结论: ¬有界结构.IsBounded (univ : 集合 E)
  证明: fun h =>
  let ⟨R, hR⟩ := isBounded_iff_forall_norm_le.1 h
  let ⟨x, hx⟩ := NormedSpace.exists_lt_norm 𝕜 E R
  hx.not_ge (hR x trivial)
-/
protected theorem NormedSpace.unbounded_univ : ¬Bornology.IsBounded (univ : Set E) := fun h =>
  let ⟨R, hR⟩ := isBounded_iff_forall_norm_le.1 h
  let ⟨x, hx⟩ := NormedSpace.exists_lt_norm 𝕜 E R
  hx.not_ge (hR x trivial)

/--
lemma `NormedSpace.cobounded_neBot` / 引理 `NormedSpace.cobounded_neBot`

English:
lemma NormedSpace.cobounded_neBot
  statement: NeBot (cobounded E)
  proof: by
  rw [neBot_iff]; rw [Ne]; rw [cobounded_eq_bot_iff]; rw [← isBounded_univ]
  exact NormedSpace.unbounded_univ 𝕜 E

中文:
引理 赋范空间.cobounded_neBot
  结论: NeBot (cobounded E)
  证明: by
  rw [neBot_iff]; rw [Ne]; rw [cobounded_eq_bot_iff]; rw [← isBounded_univ]
  exact NormedSpace.unbounded_univ 𝕜 E
-/
protected lemma NormedSpace.cobounded_neBot : NeBot (cobounded E) := by
  rw [neBot_iff]; rw [Ne]; rw [cobounded_eq_bot_iff]; rw [← isBounded_univ]
  exact NormedSpace.unbounded_univ 𝕜 E

instance (priority := 100) NontriviallyNormedField.cobounded_neBot : NeBot (cobounded 𝕜) :=
  NormedSpace.cobounded_neBot 𝕜 𝕜

instance (priority := 80) RealNormedSpace.cobounded_neBot [NormedSpace Real E] :
    NeBot (cobounded E) := NormedSpace.cobounded_neBot Real E

instance (priority := 80) NontriviallyNormedField.infinite : Infinite 𝕜 :=
  ⟨fun _ => NormedSpace.unbounded_univ 𝕜 𝕜 (Set.toFinite _).isBounded⟩

end NontriviallyNormedSpace

section NormedSpace

variable (𝕜 E)
variable [NormedField 𝕜] [Infinite 𝕜] [NormedAddCommGroup E] [Nontrivial E] [NormedSpace 𝕜 E]
include 𝕜

/--
theorem `NormedSpace.noncompactSpace` / 定理 `NormedSpace.noncompactSpace`

English:
theorem NormedSpace.noncompactSpace
  statement: NoncompactSpace E
  proof: by
  by_cases! H : exists c : 𝕜, c != 0 ∧ ‖c‖ != 1
  · let := NontriviallyNormedField.ofNormNeOne H
    exact ⟨fun h => NormedSpace.unbounded_univ 𝕜 E h.isBounded⟩
  · rcases exists_ne (0 : E) with ⟨x, hx⟩
    suffices IsClosedEmbedding (Infinite.natEmbedding 𝕜 · • x) from this.noncompactSpace
    refine isClosedEmbedding_of_pairwise_le_dist (norm_pos_iff.2 hx) fun k n hne => ?_
    simp only [dist_eq_norm, ← sub_smul, norm_smul]
    rw [H]; rw [one_mul]
    rwa [sub_ne_zero, (Embedding.injective _).ne_iff]

中文:
定理 赋范空间.noncompactSpace
  结论: Noncompact空间 E
  证明: by
  by_cases! H : exists c : 𝕜, c != 0 ∧ ‖c‖ != 1
  · let := NontriviallyNormedField.ofNormNeOne H
    exact ⟨fun h => NormedSpace.unbounded_univ 𝕜 E h.isBounded⟩
  · rcases exists_ne (0 : E) with ⟨x, hx⟩
    suffices IsClosedEmbedding (Infinite.natEmbedding 𝕜 · • x) from this.noncompactSpace
    refine isClosedEmbedding_of_pairwise_le_dist (norm_pos_iff.2 hx) fun k n hne => ?_
    simp only [dist_eq_norm, ← sub_smul, norm_smul]
    rw [H]; rw [one_mul]
    rwa [sub_ne_zero, (Embedding.injective _).ne_iff]
-/
protected theorem NormedSpace.noncompactSpace : NoncompactSpace E := by
  by_cases! H : exists c : 𝕜, c != 0 ∧ ‖c‖ != 1
  · let := NontriviallyNormedField.ofNormNeOne H
    exact ⟨fun h => NormedSpace.unbounded_univ 𝕜 E h.isBounded⟩
  · rcases exists_ne (0 : E) with ⟨x, hx⟩
    suffices IsClosedEmbedding (Infinite.natEmbedding 𝕜 · • x) from this.noncompactSpace
    refine isClosedEmbedding_of_pairwise_le_dist (norm_pos_iff.2 hx) fun k n hne => ?_
    simp only [dist_eq_norm, ← sub_smul, norm_smul]
    rw [H]; rw [one_mul]
    rwa [sub_ne_zero, (Embedding.injective _).ne_iff]

instance (priority := 100) NormedField.noncompactSpace : NoncompactSpace 𝕜 :=
  NormedSpace.noncompactSpace 𝕜 𝕜

instance (priority := 100) RealNormedSpace.noncompactSpace [NormedSpace Real E] : NoncompactSpace E :=
  NormedSpace.noncompactSpace Real E

end NormedSpace

section NormedAlgebra

/--
Definition of `NormedAlgebra` / `NormedAlgebra` 的定义

English:
class NormedAlgebra
  parameters: (𝕜 : Type*) (𝕜' : Type*) [NormedField 𝕜] [SeminormedRing 𝕜']
  axioms and operations (1):
    - norm_smul_le : forall (r : 𝕜) (x : 𝕜'), ‖r • x‖ <= ‖r‖ * ‖x‖

中文:
类 赋范代数
  参数: (𝕜 : 类型) (𝕜' : 类型) [赋范域 𝕜] [Seminormed环 𝕜']
  公理与运算 (1 个):
    - norm_smul_le : 对任意 (r : 𝕜) (x : 𝕜'), ‖r • x‖ <= ‖r‖ * ‖x‖
-/
class NormedAlgebra (𝕜 : Type*) (𝕜' : Type*) [NormedField 𝕜] [SeminormedRing 𝕜'] extends
  Algebra 𝕜 𝕜' where
  norm_smul_le : forall (r : 𝕜) (x : 𝕜'), ‖r • x‖ <= ‖r‖ * ‖x‖

attribute [inherit_doc NormedAlgebra] NormedAlgebra.norm_smul_le

variable (𝕜')
variable [NormedField 𝕜] [SeminormedRing 𝕜'] [NormedAlgebra 𝕜 𝕜']

instance (priority := 100) NormedAlgebra.toNormedSpace : NormedSpace 𝕜 𝕜' :=
  { NormedAlgebra.toAlgebra.toModule with
  norm_smul_le := NormedAlgebra.norm_smul_le }

/--
theorem `norm_algebraMap` / 定理 `norm_algebraMap`

English:
theorem norm_algebraMap
  given: (x : 𝕜)
  statement: ‖algebraMap 𝕜 𝕜' x‖ = ‖x‖ * ‖(1 : 𝕜')‖
  proof: by
  rw [Algebra.algebraMap_eq_smul_one]
  exact norm_smul _ _

中文:
定理 norm_algebraMap
  条件: (x : 𝕜)
  结论: ‖algebraMap 𝕜 𝕜' x‖ = ‖x‖ * ‖(1 : 𝕜')‖
  证明: by
  rw [Algebra.algebraMap_eq_smul_one]
  exact norm_smul _ _

Depends on / 依赖: Algebra, Algebra.algebraMap_eq_smul_one, algebraMap_eq_smul_one, norm_smul
-/
theorem norm_algebraMap (x : 𝕜) : ‖algebraMap 𝕜 𝕜' x‖ = ‖x‖ * ‖(1 : 𝕜')‖ := by
  rw [Algebra.algebraMap_eq_smul_one]
  exact norm_smul _ _

/--
theorem `nnnorm_algebraMap` / 定理 `nnnorm_algebraMap`

English:
theorem nnnorm_algebraMap
  given: (x : 𝕜)
  statement: ‖algebraMap 𝕜 𝕜' x‖₊ = ‖x‖₊ * ‖(1 : 𝕜')‖₊
  proof: Subtype.ext norm_algebraMap 𝕜' x

中文:
定理 nnnorm_algebraMap
  条件: (x : 𝕜)
  结论: ‖algebraMap 𝕜 𝕜' x‖₊ = ‖x‖₊ * ‖(1 : 𝕜')‖₊
  证明: Subtype.ext norm_algebraMap 𝕜' x

Depends on / 依赖: Subtype, Subtype.ext, norm_algebraMap
-/
theorem nnnorm_algebraMap (x : 𝕜) : ‖algebraMap 𝕜 𝕜' x‖₊ = ‖x‖₊ * ‖(1 : 𝕜')‖₊ :=
Subtype.ext norm_algebraMap 𝕜' x

/--
theorem `dist_algebraMap` / 定理 `dist_algebraMap`

English:
theorem dist_algebraMap
  given: (x y : 𝕜)
  proof: by
  simp only [dist_eq_norm, ← map_sub, norm_algebraMap]

中文:
定理 dist_algebraMap
  条件: (x y : 𝕜)
  证明: by
  simp only [dist_eq_norm, ← map_sub, norm_algebraMap]

Depends on / 依赖: dist_eq_norm, map_sub, norm_algebraMap
-/
theorem dist_algebraMap (x y : 𝕜) :
    (dist (algebraMap 𝕜 𝕜' x) (algebraMap 𝕜 𝕜' y)) = dist x y * ‖(1 : 𝕜')‖ := by
  simp only [dist_eq_norm, ← map_sub, norm_algebraMap]

/-- This is a simpler version of `norm_algebraMap` when `‖1‖ = 1` in `𝕜'`. -/
@[simp]
/--
theorem `norm_algebraMap'` / 定理 `norm_algebraMap'`

English:
theorem norm_algebraMap'
  given: [NormOneClass 𝕜'] (x : 𝕜)
  statement: ‖algebraMap 𝕜 𝕜' x‖ = ‖x‖
  proof: by
  rw [norm_algebraMap]; rw [norm_one]; rw [mul_one]

@[simp]

中文:
定理 norm_algebraMap'
  条件: [NormOne类 𝕜'] (x : 𝕜)
  结论: ‖algebraMap 𝕜 𝕜' x‖ = ‖x‖
  证明: by
  rw [norm_algebraMap]; rw [norm_one]; rw [mul_one]

@[simp]

Depends on / 依赖: mul_one, norm_algebraMap, norm_one
-/
theorem norm_algebraMap' [NormOneClass 𝕜'] (x : 𝕜) : ‖algebraMap 𝕜 𝕜' x‖ = ‖x‖ := by
  rw [norm_algebraMap]; rw [norm_one]; rw [mul_one]

@[simp]
/--
theorem `Algebra.norm_smul_one_eq_norm` / 定理 `Algebra.norm_smul_one_eq_norm`

English:
theorem Algebra.norm_smul_one_eq_norm
  given: [NormOneClass 𝕜'] (x : 𝕜)
  statement: ‖x • (1 : 𝕜')‖ = ‖x‖
  proof: by
  simp [norm_smul]

中文:
定理 代数.norm_smul_one_eq_norm
  条件: [NormOne类 𝕜'] (x : 𝕜)
  结论: ‖x • (1 : 𝕜')‖ = ‖x‖
  证明: by
  simp [norm_smul]

Depends on / 依赖: norm_smul
-/
theorem Algebra.norm_smul_one_eq_norm [NormOneClass 𝕜'] (x : 𝕜) : ‖x • (1 : 𝕜')‖ = ‖x‖ := by
  simp [norm_smul]

/-- This is a simpler version of `nnnorm_algebraMap` when `‖1‖ = 1` in `𝕜'`. -/
@[simp]
/--
theorem `nnnorm_algebraMap'` / 定理 `nnnorm_algebraMap'`

English:
theorem nnnorm_algebraMap'
  given: [NormOneClass 𝕜'] (x : 𝕜)
  statement: ‖algebraMap 𝕜 𝕜' x‖₊ = ‖x‖₊
  proof: Subtype.ext norm_algebraMap' _ _

中文:
定理 nnnorm_algebraMap'
  条件: [NormOne类 𝕜'] (x : 𝕜)
  结论: ‖algebraMap 𝕜 𝕜' x‖₊ = ‖x‖₊
  证明: Subtype.ext norm_algebraMap' _ _

Depends on / 依赖: Subtype, Subtype.ext, norm_algebraMap
-/
theorem nnnorm_algebraMap' [NormOneClass 𝕜'] (x : 𝕜) : ‖algebraMap 𝕜 𝕜' x‖₊ = ‖x‖₊ :=
Subtype.ext norm_algebraMap' _ _

/-- This is a simpler version of `dist_algebraMap` when `‖1‖ = 1` in `𝕜'`. -/
@[simp]
/--
theorem `dist_algebraMap'` / 定理 `dist_algebraMap'`

English:
theorem dist_algebraMap'
  given: [NormOneClass 𝕜'] (x y : 𝕜)
  proof: by
  simp only [dist_eq_norm, ← map_sub, norm_algebraMap']

中文:
定理 dist_algebraMap'
  条件: [NormOne类 𝕜'] (x y : 𝕜)
  证明: by
  simp only [dist_eq_norm, ← map_sub, norm_algebraMap']

Depends on / 依赖: dist_eq_norm, map_sub, norm_algebraMap
-/
theorem dist_algebraMap' [NormOneClass 𝕜'] (x y : 𝕜) :
    (dist (algebraMap 𝕜 𝕜' x) (algebraMap 𝕜 𝕜' y)) = dist x y := by
  simp only [dist_eq_norm, ← map_sub, norm_algebraMap']

section NNReal

variable [NormOneClass 𝕜'] [NormedAlgebra Real 𝕜']

@[simp]
/--
theorem `norm_algebraMap_nnreal` / 定理 `norm_algebraMap_nnreal`

English:
theorem norm_algebraMap_nnreal
  given: (x : Real>=0)
  statement: ‖algebraMap Real>=0 𝕜' x‖ = x
  proof: (norm_algebraMap' 𝕜' (x : Real)).symm ▸ Real.norm_of_nonneg x.prop

@[simp]

中文:
定理 norm_algebraMap_nnreal
  条件: (x : 实数>=0)
  结论: ‖algebraMap 实数>=0 𝕜' x‖ = x
  证明: (norm_algebraMap' 𝕜' (x : Real)).symm ▸ Real.norm_of_nonneg x.prop

@[simp]

Depends on / 依赖: Real.norm_of_nonneg, norm_algebraMap, norm_of_nonneg, x.prop
-/
theorem norm_algebraMap_nnreal (x : Real>=0) : ‖algebraMap Real>=0 𝕜' x‖ = x :=
  (norm_algebraMap' 𝕜' (x : Real)).symm ▸ Real.norm_of_nonneg x.prop

@[simp]
/--
theorem `nnnorm_algebraMap_nnreal` / 定理 `nnnorm_algebraMap_nnreal`

English:
theorem nnnorm_algebraMap_nnreal
  given: (x : Real>=0)
  statement: ‖algebraMap Real>=0 𝕜' x‖₊ = x
  proof: Subtype.ext norm_algebraMap_nnreal 𝕜' x

中文:
定理 nnnorm_algebraMap_nnreal
  条件: (x : 实数>=0)
  结论: ‖algebraMap 实数>=0 𝕜' x‖₊ = x
  证明: Subtype.ext norm_algebraMap_nnreal 𝕜' x

Depends on / 依赖: Subtype, Subtype.ext, norm_algebraMap_nnreal
-/
theorem nnnorm_algebraMap_nnreal (x : Real>=0) : ‖algebraMap Real>=0 𝕜' x‖₊ = x :=
Subtype.ext norm_algebraMap_nnreal 𝕜' x

end NNReal

variable (𝕜)

open Filter Bornology in
/-- Preimages of cobounded sets under the algebra map are cobounded. -/
@[simp]
/--
theorem `tendsto_algebraMap_cobounded` / 定理 `tendsto_algebraMap_cobounded`

English:
theorem tendsto_algebraMap_cobounded
  statement: (𝕜 𝕜' : Type*) [NormedField 𝕜] [SeminormedRing 𝕜']
  proof: by
  intro c hc
  rw [mem_map]
  rw [← isCobounded_def]; rw [← isBounded_compl_iff]; rw [isBounded_iff_forall_norm_le] at hc ⊢
  obtain ⟨s, hs⟩ := hc
  exact ⟨s, fun x hx => by simpa using hs (algebraMap 𝕜 𝕜' x) hx⟩

中文:
定理 tendsto_algebraMap_cobounded
  结论: (𝕜 𝕜' : 类型) [赋范域 𝕜] [Seminormed环 𝕜']
  证明: by
  intro c hc
  rw [mem_map]
  rw [← isCobounded_def]; rw [← isBounded_compl_iff]; rw [isBounded_iff_forall_norm_le] at hc ⊢
  obtain ⟨s, hs⟩ := hc
  exact ⟨s, fun x hx => by simpa using hs (algebraMap 𝕜 𝕜' x) hx⟩

Depends on / 依赖: algebraMap, isBounded_compl_iff, isBounded_iff_forall_norm_le, isCobounded_def, mem_map
-/
theorem tendsto_algebraMap_cobounded (𝕜 𝕜' : Type*) [NormedField 𝕜] [SeminormedRing 𝕜']
    [NormedAlgebra 𝕜 𝕜'] [NormOneClass 𝕜'] :
    Tendsto (algebraMap 𝕜 𝕜') (cobounded 𝕜) (cobounded 𝕜') := by
  intro c hc
  rw [mem_map]
  rw [← isCobounded_def]; rw [← isBounded_compl_iff]; rw [isBounded_iff_forall_norm_le] at hc ⊢
  obtain ⟨s, hs⟩ := hc
  exact ⟨s, fun x hx => by simpa using hs (algebraMap 𝕜 𝕜' x) hx⟩

/--
theorem `algebraMap_isometry` / 定理 `algebraMap_isometry`

English:
theorem algebraMap_isometry
  given: [NormOneClass 𝕜']
  statement: Isometry (algebraMap 𝕜 𝕜')
  proof: by
  refine Isometry.of_dist_eq fun x y => ?_
  rw [dist_eq_norm]; rw [dist_eq_norm]; rw [← map_sub]; rw [norm_algebraMap']

中文:
定理 algebraMap_isometry
  条件: [NormOne类 𝕜']
  结论: 等距 (algebraMap 𝕜 𝕜')
  证明: by
  refine Isometry.of_dist_eq fun x y => ?_
  rw [dist_eq_norm]; rw [dist_eq_norm]; rw [← map_sub]; rw [norm_algebraMap']

Depends on / 依赖: Isometry, Isometry.of_dist_eq, dist_eq_norm, map_sub, norm_algebraMap, of_dist_eq
-/
theorem algebraMap_isometry [NormOneClass 𝕜'] : Isometry (algebraMap 𝕜 𝕜') := by
  refine Isometry.of_dist_eq fun x y => ?_
  rw [dist_eq_norm]; rw [dist_eq_norm]; rw [← map_sub]; rw [norm_algebraMap']

/--
Instance `NormedAlgebra.id` / 实例 `NormedAlgebra.id`

English:
instance NormedAlgebra.id
  signature: : NormedAlgebra 𝕜 𝕜
  body: { NormedField.toNormedSpace, Algebra.id 𝕜 with }

中文:
实例 赋范代数.id
  签名: : 赋范代数 𝕜 𝕜
  定义体: { NormedField.toNormedSpace, Algebra.id 𝕜 with }

Depends on / 依赖: Algebra, Algebra.id, NormedField, NormedField.toNormedSpace, toNormedSpace
-/
instance NormedAlgebra.id : NormedAlgebra 𝕜 𝕜 :=
  { NormedField.toNormedSpace, Algebra.id 𝕜 with }

/--
Instance `normedAlgebraRat` / 实例 `normedAlgebraRat`

English:
instance normedAlgebraRat
  signature: {𝕜} [NormedDivisionRing 𝕜] [CharZero 𝕜] [NormedAlgebra Real 𝕜]
  body: by
    rw [← smul_one_smul Real q x]; rw [Rat.smul_one_eq_cast]; rw [norm_smul]; rw [Rat.norm_cast_real]

中文:
实例 normedAlgebraRat
  签名: {𝕜} [NormedDivision环 𝕜] [特征零 𝕜] [赋范代数 实数 𝕜]
  定义体: by
    rw [← smul_one_smul Real q x]; rw [Rat.smul_one_eq_cast]; rw [norm_smul]; rw [Rat.norm_cast_real]

Depends on / 依赖: Rat.norm_cast_real, Rat.smul_one_eq_cast, norm_cast_real, norm_smul, smul_one_eq_cast, smul_one_smul
-/
instance normedAlgebraRat {𝕜} [NormedDivisionRing 𝕜] [CharZero 𝕜] [NormedAlgebra Real 𝕜] :
    NormedAlgebra Rat 𝕜 where
  norm_smul_le q x := by
    rw [← smul_one_smul Real q x]; rw [Rat.smul_one_eq_cast]; rw [norm_smul]; rw [Rat.norm_cast_real]

/--
Instance `PUnit.normedAlgebra` / 实例 `PUnit.normedAlgebra`

English:
instance PUnit.normedAlgebra
  signature: : NormedAlgebra 𝕜 PUnit where
  body: by simp only [norm_eq_zero, mul_zero, le_refl]

中文:
实例 命题单元.normedAlgebra
  签名: : 赋范代数 𝕜 命题单元 where
  定义体: by simp only [norm_eq_zero, mul_zero, le_refl]

Depends on / 依赖: le_refl, mul_zero, norm_eq_zero
-/
instance PUnit.normedAlgebra : NormedAlgebra 𝕜 PUnit where
  norm_smul_le q _ := by simp only [norm_eq_zero, mul_zero, le_refl]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: NormedAlgebra 𝕜 (ULift 𝕜')
  body: { ULift.normedSpace, ULift.algebra with }

中文:
实例 :
  签名: 赋范代数 𝕜 (类型层提升 𝕜')
  定义体: { ULift.normedSpace, ULift.algebra with }

Depends on / 依赖: ULift.algebra, ULift.normedSpace, algebra, normedSpace
-/
instance : NormedAlgebra 𝕜 (ULift 𝕜') :=
  { ULift.normedSpace, ULift.algebra with }

/--
Instance `Prod.normedAlgebra` / 实例 `Prod.normedAlgebra`

English:
instance Prod.normedAlgebra
  signature: {E F : Type*} [SeminormedRing E] [SeminormedRing F] [NormedAlgebra 𝕜 E]
  body: { Prod.normedSpace, Prod.algebra 𝕜 E F with }

中文:
实例 积类型.normedAlgebra
  签名: {E F : 类型} [Seminormed环 E] [Seminormed环 F] [赋范代数 𝕜 E]
  定义体: { Prod.normedSpace, Prod.algebra 𝕜 E F with }

Depends on / 依赖: Prod.algebra, Prod.normedSpace, algebra, normedSpace
-/
instance Prod.normedAlgebra {E F : Type*} [SeminormedRing E] [SeminormedRing F] [NormedAlgebra 𝕜 E]
    [NormedAlgebra 𝕜 F] : NormedAlgebra 𝕜 (E × F) :=
  { Prod.normedSpace, Prod.algebra 𝕜 E F with }

/--
Instance `Pi.normedAlgebra` / 实例 `Pi.normedAlgebra`

English:
instance Pi.normedAlgebra
  signature: {ι : Type*} {E : ι -> Type*} [Fintype ι] [forall i, SeminormedRing (E i)]
  body: { Pi.normedSpace, Pi.algebra _ E with }

中文:
实例 依赖函数类型.normedAlgebra
  签名: {ι : 类型} {E : ι -> 类型} [有限类型 ι] [对任意 i, Seminormed环 (E i)]
  定义体: { Pi.normedSpace, Pi.algebra _ E with }

Depends on / 依赖: Pi.algebra, Pi.normedSpace, algebra, normedSpace
-/
instance Pi.normedAlgebra {ι : Type*} {E : ι -> Type*} [Fintype ι] [forall i, SeminormedRing (E i)]
    [forall i, NormedAlgebra 𝕜 (E i)] : NormedAlgebra 𝕜 (forall i, E i) :=
  { Pi.normedSpace, Pi.algebra _ E with }

variable [SeminormedRing E] [NormedAlgebra 𝕜 E]

/--
Instance `SeparationQuotient.instNormedAlgebra` / 实例 `SeparationQuotient.instNormedAlgebra`

English:
instance SeparationQuotient.instNormedAlgebra
  signature: : NormedAlgebra 𝕜 (SeparationQuotient E) where
  body: inferInstance
  __ : Algebra 𝕜 (SeparationQuotient E) := inferInstance

中文:
实例 SeparationQuotient.instNormedAlgebra
  签名: : 赋范代数 𝕜 (SeparationQuotient E) where
  定义体: inferInstance
  __ : Algebra 𝕜 (SeparationQuotient E) := inferInstance
-/
instance SeparationQuotient.instNormedAlgebra : NormedAlgebra 𝕜 (SeparationQuotient E) where
  __ : NormedSpace 𝕜 (SeparationQuotient E) := inferInstance
  __ : Algebra 𝕜 (SeparationQuotient E) := inferInstance

/--
Instance `MulOpposite.instNormedAlgebra` / 实例 `MulOpposite.instNormedAlgebra`

English:
instance MulOpposite.instNormedAlgebra
  signature: {E : Type*} [SeminormedRing E] [NormedAlgebra 𝕜 E]
  body: instAlgebra
  __ := instNormedSpace

中文:
实例 MulOpposite.instNormedAlgebra
  签名: {E : 类型} [Seminormed环 E] [赋范代数 𝕜 E]
  定义体: instAlgebra
  __ := instNormedSpace

Depends on / 依赖: instAlgebra
-/
instance MulOpposite.instNormedAlgebra {E : Type*} [SeminormedRing E] [NormedAlgebra 𝕜 E] :
    NormedAlgebra 𝕜 Eᵐᵒᵖ where
  __ := instAlgebra
  __ := instNormedSpace

end NormedAlgebra

/--
Definition of `NormedAlgebra.induced` / `NormedAlgebra.induced` 的定义

English:
abbreviation NormedAlgebra.induced
  signature: {F : Type*} (𝕜 R S : Type*) [NormedField 𝕜] [Ring R] [Algebra 𝕜 R]
  body: letI := SeminormedRing.induced R S f
  ⟨fun a b => show ‖f (a • b)‖ <= ‖a‖ * ‖f b‖ from (map_smul f a b).symm ▸ norm_smul_le a (f b)⟩

中文:
缩写 赋范代数.induced
  签名: {F : 类型} (𝕜 R S : 类型) [赋范域 𝕜] [环 R] [代数 𝕜 R]
  定义体: letI := SeminormedRing.induced R S f
  ⟨fun a b => show ‖f (a • b)‖ <= ‖a‖ * ‖f b‖ from (map_smul f a b).symm ▸ norm_smul_le a (f b)⟩

Depends on / 依赖: SeminormedRing, SeminormedRing.induced, induced, map_smul, norm_smul_le
-/
abbrev NormedAlgebra.induced {F : Type*} (𝕜 R S : Type*) [NormedField 𝕜] [Ring R] [Algebra 𝕜 R]
    [SeminormedRing S] [NormedAlgebra 𝕜 S] [FunLike F R S] [NonUnitalAlgHomClass F 𝕜 R S]
    (f : F) :
    @NormedAlgebra 𝕜 R _ (SeminormedRing.induced R S f) :=
  letI := SeminormedRing.induced R S f
  ⟨fun a b => show ‖f (a • b)‖ <= ‖a‖ * ‖f b‖ from (map_smul f a b).symm ▸ norm_smul_le a (f b)⟩

/--
Instance `Subalgebra.toNormedAlgebra` / 实例 `Subalgebra.toNormedAlgebra`

English:
instance Subalgebra.toNormedAlgebra
  signature: {𝕜 A : Type*} [SeminormedRing A] [NormedField 𝕜]
  body: fast_instance% NormedAlgebra.induced 𝕜 S A S.val

中文:
实例 子代数.toNormedAlgebra
  签名: {𝕜 A : 类型} [Seminormed环 A] [赋范域 𝕜]
  定义体: fast_instance% NormedAlgebra.induced 𝕜 S A S.val

Depends on / 依赖: NormedAlgebra, NormedAlgebra.induced, S.val, fast_instance, induced
-/
instance Subalgebra.toNormedAlgebra {𝕜 A : Type*} [SeminormedRing A] [NormedField 𝕜]
    [NormedAlgebra 𝕜 A] (S : Subalgebra 𝕜 A) : NormedAlgebra 𝕜 S :=
  fast_instance% NormedAlgebra.induced 𝕜 S A S.val

section SubalgebraClass

variable {S 𝕜 E : Type*} [NormedField 𝕜] [SeminormedRing E] [NormedAlgebra 𝕜 E]
variable [SetLike S E] [SubringClass S E] [SMulMemClass S 𝕜 E] (s : S)

instance (priority := 75) SubalgebraClass.toNormedAlgebra : NormedAlgebra 𝕜 s where
  norm_smul_le c x := norm_smul_le c (x : E)

end SubalgebraClass

section RestrictScalars

section NormInstances

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [I
  signature: : SeminormedAddCommGroup E] :
  body: I

中文:
实例 [I
  签名: : SeminormedAddComm群 E] :
  定义体: I
-/
instance [I : SeminormedAddCommGroup E] :
    SeminormedAddCommGroup (RestrictScalars 𝕜 𝕜' E) :=
  I

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [I
  signature: : NormedAddCommGroup E] :
  body: I

中文:
实例 [I
  签名: : 赋范交换加群 E] :
  定义体: I
-/
instance [I : NormedAddCommGroup E] :
    NormedAddCommGroup (RestrictScalars 𝕜 𝕜' E) :=
  I

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [I
  signature: : NonUnitalSeminormedRing E] :
  body: I

中文:
实例 [I
  签名: : 非幺Seminormed环 E] :
  定义体: I
-/
instance [I : NonUnitalSeminormedRing E] :
    NonUnitalSeminormedRing (RestrictScalars 𝕜 𝕜' E) :=
  I

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [I
  signature: : NonUnitalNormedRing E] :
  body: I

中文:
实例 [I
  签名: : 非幺赋范环 E] :
  定义体: I
-/
instance [I : NonUnitalNormedRing E] :
    NonUnitalNormedRing (RestrictScalars 𝕜 𝕜' E) :=
  I

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [I
  signature: : SeminormedRing E] :
  body: I

中文:
实例 [I
  签名: : Seminormed环 E] :
  定义体: I
-/
instance [I : SeminormedRing E] :
    SeminormedRing (RestrictScalars 𝕜 𝕜' E) :=
  I

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [I
  signature: : NormedRing E] :
  body: I

中文:
实例 [I
  签名: : 赋范环 E] :
  定义体: I
-/
instance [I : NormedRing E] :
    NormedRing (RestrictScalars 𝕜 𝕜' E) :=
  I

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [I
  signature: : NonUnitalSeminormedCommRing E] :
  body: I

中文:
实例 [I
  签名: : 非幺SeminormedComm环 E] :
  定义体: I
-/
instance [I : NonUnitalSeminormedCommRing E] :
    NonUnitalSeminormedCommRing (RestrictScalars 𝕜 𝕜' E) :=
  I

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [I
  signature: : NonUnitalNormedCommRing E] :
  body: I

中文:
实例 [I
  签名: : 非幺NormedComm环 E] :
  定义体: I
-/
instance [I : NonUnitalNormedCommRing E] :
    NonUnitalNormedCommRing (RestrictScalars 𝕜 𝕜' E) :=
  I

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [I
  signature: : SeminormedCommRing E] :
  body: I

中文:
实例 [I
  签名: : SeminormedComm环 E] :
  定义体: I
-/
instance [I : SeminormedCommRing E] :
    SeminormedCommRing (RestrictScalars 𝕜 𝕜' E) :=
  I

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [I
  signature: : NormedCommRing E] :
  body: I

中文:
实例 [I
  签名: : NormedComm环 E] :
  定义体: I
-/
instance [I : NormedCommRing E] :
    NormedCommRing (RestrictScalars 𝕜 𝕜' E) :=
  I

end NormInstances

section NormedSpace

variable (𝕜 𝕜' E)
variable [NormedField 𝕜] [NormedField 𝕜'] [NormedAlgebra 𝕜 𝕜']
  [SeminormedAddCommGroup E] [NormedSpace 𝕜' E]

/-- Warning: This declaration should be used judiciously.
Please consider using `IsScalarTower` instead.

This definition allows the `RestrictScalars.normedSpace` instance to be put directly on `E`
rather on `RestrictScalars 𝕜 𝕜' E`. This would be a very bad instance; both because `𝕜'` cannot be
inferred, and because it is likely to create instance diamonds.

See Note [reducible non-instances].
-/
@[instance_reducible]
/--
Definition of `NormedSpace.restrictScalars` / `NormedSpace.restrictScalars` 的定义

English:
definition NormedSpace.restrictScalars
  signature: : NormedSpace 𝕜 E
  body: { Module.restrictScalars 𝕜 𝕜' E with
    norm_smul_le := fun c x =>
(norm_smul_le (algebraMap 𝕜 𝕜' c) (_ : E)).trans_eq by rw [norm_algebraMap'] }

中文:
定义 赋范空间.restrictScalars
  签名: : 赋范空间 𝕜 E
  定义体: { Module.restrictScalars 𝕜 𝕜' E with
    norm_smul_le := fun c x =>
(norm_smul_le (algebraMap 𝕜 𝕜' c) (_ : E)).trans_eq by rw [norm_algebraMap'] }

Depends on / 依赖: Module, Module.restrictScalars, algebraMap, norm_algebraMap, norm_smul_le, restrictScalars, trans_eq
-/
def NormedSpace.restrictScalars : NormedSpace 𝕜 E :=
  { Module.restrictScalars 𝕜 𝕜' E with
    norm_smul_le := fun c x =>
(norm_smul_le (algebraMap 𝕜 𝕜' c) (_ : E)).trans_eq by rw [norm_algebraMap'] }

/--
theorem `NormedSpace.restrictScalars_eq` / 定理 `NormedSpace.restrictScalars_eq`

English:
theorem NormedSpace.restrictScalars_eq
  statement: {E : Type*} [SeminormedAddCommGroup E]
  proof: by
  ext
  apply algebraMap_smul

中文:
定理 赋范空间.restrictScalars_eq
  结论: {E : 类型} [SeminormedAddComm群 E]
  证明: by
  ext
  apply algebraMap_smul

Depends on / 依赖: algebraMap_smul
-/
theorem NormedSpace.restrictScalars_eq {E : Type*} [SeminormedAddCommGroup E]
    [h : NormedSpace 𝕜 E] [NormedSpace 𝕜' E] [IsScalarTower 𝕜 𝕜' E] :
    NormedSpace.restrictScalars 𝕜 𝕜' E = h := by
  ext
  apply algebraMap_smul

/--
Instance `RestrictScalars.normedSpace` / 实例 `RestrictScalars.normedSpace`

English:
instance RestrictScalars.normedSpace
  signature: : NormedSpace 𝕜 (RestrictScalars 𝕜 𝕜' E)
  body: fast_instance% NormedSpace.restrictScalars 𝕜 𝕜' E

中文:
实例 RestrictScalars.normedSpace
  签名: : 赋范空间 𝕜 (RestrictScalars 𝕜 𝕜' E)
  定义体: fast_instance% NormedSpace.restrictScalars 𝕜 𝕜' E

Depends on / 依赖: NormedSpace, NormedSpace.restrictScalars, fast_instance, restrictScalars
-/
instance RestrictScalars.normedSpace : NormedSpace 𝕜 (RestrictScalars 𝕜 𝕜' E) :=
  fast_instance% NormedSpace.restrictScalars 𝕜 𝕜' E

-- If you think you need this, consider instead reproducing `RestrictScalars.lsmul`
-- appropriately modified here.
/-- The action of the original `NormedField` on `RestrictScalars 𝕜 𝕜' E`.
This is not an instance as it would be contrary to the purpose of `RestrictScalars`.
-/
@[instance_reducible]
/--
Definition of `Module.RestrictScalars.normedSpaceOrig` / `Module.RestrictScalars.normedSpaceOrig` 的定义

English:
definition Module.RestrictScalars.normedSpaceOrig
  signature: {𝕜 : Type*} {𝕜' : Type*} {E : Type*} [NormedField 𝕜']
  body: I

中文:
定义 模.RestrictScalars.normedSpaceOrig
  签名: {𝕜 : 类型} {𝕜' : 类型} {E : 类型} [赋范域 𝕜']
  定义体: I
-/
def Module.RestrictScalars.normedSpaceOrig {𝕜 : Type*} {𝕜' : Type*} {E : Type*} [NormedField 𝕜']
    [SeminormedAddCommGroup E] [I : NormedSpace 𝕜' E] : NormedSpace 𝕜' (RestrictScalars 𝕜 𝕜' E) :=
  I

end NormedSpace

section NormedAlgebra

variable (𝕜 𝕜' E)
variable [NormedField 𝕜] [NormedField 𝕜'] [NormedAlgebra 𝕜 𝕜']
  [SeminormedRing E] [NormedAlgebra 𝕜' E]

/-- Warning: This declaration should be used judiciously.
Please consider using `IsScalarTower` instead.

This definition allows the `RestrictScalars.normedAlgebra` instance to be put directly on `E`
rather on `RestrictScalars 𝕜 𝕜' E`. This would be a very bad instance; both because `𝕜'` cannot be
inferred, and because it is likely to create instance diamonds.

See Note [reducible non-instances].
-/
@[instance_reducible]
/--
Definition of `NormedAlgebra.restrictScalars` / `NormedAlgebra.restrictScalars` 的定义

English:
definition NormedAlgebra.restrictScalars
  signature: : NormedAlgebra 𝕜 E
  body: { NormedSpace.restrictScalars 𝕜 𝕜' E, Algebra.restrictScalars 𝕜 𝕜' E with }

中文:
定义 赋范代数.restrictScalars
  签名: : 赋范代数 𝕜 E
  定义体: { NormedSpace.restrictScalars 𝕜 𝕜' E, Algebra.restrictScalars 𝕜 𝕜' E with }

Depends on / 依赖: Algebra, Algebra.restrictScalars, NormedSpace, NormedSpace.restrictScalars, restrictScalars
-/
def NormedAlgebra.restrictScalars : NormedAlgebra 𝕜 E :=
  { NormedSpace.restrictScalars 𝕜 𝕜' E, Algebra.restrictScalars 𝕜 𝕜' E with }

/--
Instance `RestrictScalars.normedAlgebra` / 实例 `RestrictScalars.normedAlgebra`

English:
instance RestrictScalars.normedAlgebra
  signature: : NormedAlgebra 𝕜 (RestrictScalars 𝕜 𝕜' E)
  body: fast_instance% NormedAlgebra.restrictScalars 𝕜 𝕜' E

中文:
实例 RestrictScalars.normedAlgebra
  签名: : 赋范代数 𝕜 (RestrictScalars 𝕜 𝕜' E)
  定义体: fast_instance% NormedAlgebra.restrictScalars 𝕜 𝕜' E

Depends on / 依赖: NormedAlgebra, NormedAlgebra.restrictScalars, fast_instance, restrictScalars
-/
instance RestrictScalars.normedAlgebra : NormedAlgebra 𝕜 (RestrictScalars 𝕜 𝕜' E) :=
  fast_instance% NormedAlgebra.restrictScalars 𝕜 𝕜' E

-- If you think you need this, consider instead reproducing `RestrictScalars.lsmul`
-- appropriately modified here.
/-- The action of the original `NormedField` on `RestrictScalars 𝕜 𝕜' E`.
This is not an instance as it would be contrary to the purpose of `RestrictScalars`.
-/
@[instance_reducible]
/--
Definition of `Module.RestrictScalars.normedAlgebraOrig` / `Module.RestrictScalars.normedAlgebraOrig` 的定义

English:
definition Module.RestrictScalars.normedAlgebraOrig
  signature: {𝕜 : Type*} {𝕜' : Type*} {E : Type*} [NormedField 𝕜']
  body: I

中文:
定义 模.RestrictScalars.normedAlgebraOrig
  签名: {𝕜 : 类型} {𝕜' : 类型} {E : 类型} [赋范域 𝕜']
  定义体: I
-/
def Module.RestrictScalars.normedAlgebraOrig {𝕜 : Type*} {𝕜' : Type*} {E : Type*} [NormedField 𝕜']
    [SeminormedRing E] [I : NormedAlgebra 𝕜' E] : NormedAlgebra 𝕜' (RestrictScalars 𝕜 𝕜' E) :=
  I
end NormedAlgebra

end RestrictScalars

section Core
/-!
### Structures for constructing new normed spaces

This section contains tools meant for constructing new normed spaces. These allow one to easily
construct all the relevant instances (distances measures, etc) while proving only a minimal
set of axioms. Furthermore, tools are provided to add a norm structure to a type that already
has a preexisting uniformity or bornology: in such cases, it is necessary to keep the preexisting
instances, while ensuring that the norm induces the same uniformity/bornology.
-/

open scoped Uniformity Bornology

/--
Definition of `SeminormedSpace.Core` / `SeminormedSpace.Core` 的定义

English:
structure SeminormedSpace.Core
  parameters: (𝕜 : Type*) (E : Type*) [NormedField 𝕜] [AddCommGroup E]
  axioms and operations (3):
    - norm_nonneg((x : E)) : 0 <= ‖x‖
    - norm_smul((c : 𝕜) (x : E)) : ‖c • x‖ = ‖c‖ * ‖x‖
    - norm_triangle((x y : E)) : ‖x + y‖ <= ‖x‖ + ‖y‖

中文:
结构 半赋范空间.核
  参数: (𝕜 : 类型) (E : 类型) [赋范域 𝕜] [加法交换群 E]
  公理与运算 (3 个):
    - norm_nonneg((x : E)) : 0 <= ‖x‖
    - norm_smul((c : 𝕜) (x : E)) : ‖c • x‖ = ‖c‖ * ‖x‖
    - norm_triangle((x y : E)) : ‖x + y‖ <= ‖x‖ + ‖y‖
-/
structure SeminormedSpace.Core (𝕜 : Type*) (E : Type*) [NormedField 𝕜] [AddCommGroup E]
    [Norm E] [Module 𝕜 E] : Prop where
  norm_nonneg (x : E) : 0 <= ‖x‖
  norm_smul (c : 𝕜) (x : E) : ‖c • x‖ = ‖c‖ * ‖x‖
  norm_triangle (x y : E) : ‖x + y‖ <= ‖x‖ + ‖y‖

/--
Definition of `PseudoMetricSpace.ofSeminormedSpaceCore` / `PseudoMetricSpace.ofSeminormedSpaceCore` 的定义

English:
abbreviation PseudoMetricSpace.ofSeminormedSpaceCore
  signature: {𝕜 E : Type*} [NormedField 𝕜] [AddCommGroup E]
  body: ‖-x + y‖
  dist_self x := by
    show ‖-x + x‖ = 0
    simp only [add_comm, ← sub_eq_add_neg, sub_self]
    have : (0 : E) = (0 : 𝕜) • (0 : E) := by simp
    rw [this]; rw [core.norm_smul]
    simp
  dist_comm x y := by
    show ‖-x + y‖ = ‖-y + x‖
    have : -y + x = (-1 : 𝕜) • (-x + y) := by simp; abel
    rw [this]; rw [core.norm_smul]
    simp
  dist_triangle x y z := by
    show ‖-x + z‖ <= ‖-x + y‖ + ‖-y + z‖
    have : -x + z = (-x + y) + (-y + z) := by abel
    rw [this]
    exact core.norm_triangle _ _
  edist_dist x y := by exact (ENNReal.ofReal_eq_coe_nnreal _).symm

中文:
缩写 伪度量空间.ofSeminormedSpaceCore
  签名: {𝕜 E : 类型} [赋范域 𝕜] [加法交换群 E]
  定义体: ‖-x + y‖
  dist_self x := by
    show ‖-x + x‖ = 0
    simp only [add_comm, ← sub_eq_add_neg, sub_self]
    have : (0 : E) = (0 : 𝕜) • (0 : E) := by simp
    rw [this]; rw [core.norm_smul]
    simp
  dist_comm x y := by
    show ‖-x + y‖ = ‖-y + x‖
    have : -y + x = (-1 : 𝕜) • (-x + y) := by simp; abel
    rw [this]; rw [core.norm_smul]
    simp
  dist_triangle x y z := by
    show ‖-x + z‖ <= ‖-x + y‖ + ‖-y + z‖
    have : -x + z = (-x + y) + (-y + z) := by abel
    rw [this]
    exact core.norm_triangle _ _
  edist_dist x y := by exact (ENNReal.ofReal_eq_coe_nnreal _).symm
-/
abbrev PseudoMetricSpace.ofSeminormedSpaceCore {𝕜 E : Type*} [NormedField 𝕜] [AddCommGroup E]
    [Norm E] [Module 𝕜 E] (core : SeminormedSpace.Core 𝕜 E) :
    PseudoMetricSpace E where
  dist x y := ‖-x + y‖
  dist_self x := by
    show ‖-x + x‖ = 0
    simp only [add_comm, ← sub_eq_add_neg, sub_self]
    have : (0 : E) = (0 : 𝕜) • (0 : E) := by simp
    rw [this]; rw [core.norm_smul]
    simp
  dist_comm x y := by
    show ‖-x + y‖ = ‖-y + x‖
    have : -y + x = (-1 : 𝕜) • (-x + y) := by simp; abel
    rw [this]; rw [core.norm_smul]
    simp
  dist_triangle x y z := by
    show ‖-x + z‖ <= ‖-x + y‖ + ‖-y + z‖
    have : -x + z = (-x + y) + (-y + z) := by abel
    rw [this]
    exact core.norm_triangle _ _
  edist_dist x y := by exact (ENNReal.ofReal_eq_coe_nnreal _).symm

/--
Definition of `PseudoEMetricSpace.ofSeminormedSpaceCore` / `PseudoEMetricSpace.ofSeminormedSpaceCore` 的定义

English:
abbreviation PseudoEMetricSpace.ofSeminormedSpaceCore
  signature: {𝕜 E : Type*} [NormedField 𝕜]
  body: (PseudoMetricSpace.ofSeminormedSpaceCore core).toPseudoEMetricSpace

中文:
缩写 PseudoEMetric空间.ofSeminormedSpaceCore
  签名: {𝕜 E : 类型} [赋范域 𝕜]
  定义体: (PseudoMetricSpace.ofSeminormedSpaceCore core).toPseudoEMetricSpace

Depends on / 依赖: PseudoMetricSpace, PseudoMetricSpace.ofSeminormedSpaceCore, ofSeminormedSpaceCore, toPseudoEMetricSpace
-/
abbrev PseudoEMetricSpace.ofSeminormedSpaceCore {𝕜 E : Type*} [NormedField 𝕜]
    [AddCommGroup E] [Norm E] [Module 𝕜 E]
    (core : SeminormedSpace.Core 𝕜 E) : PseudoEMetricSpace E :=
  (PseudoMetricSpace.ofSeminormedSpaceCore core).toPseudoEMetricSpace

/--
Definition of `PseudoMetricSpace.ofSeminormedSpaceCoreReplaceUniformity` / `PseudoMetricSpace.ofSeminormedSpaceCoreReplaceUniformity` 的定义

English:
abbreviation PseudoMetricSpace.ofSeminormedSpaceCoreReplaceUniformity
  signature: {𝕜 E : Type*} [NormedField 𝕜]
  body: .replaceUniformity (.ofSeminormedSpaceCore core) H

中文:
缩写 伪度量空间.ofSeminormedSpaceCoreReplaceUniformity
  签名: {𝕜 E : 类型} [赋范域 𝕜]
  定义体: .replaceUniformity (.ofSeminormedSpaceCore core) H

Depends on / 依赖: PseudoEMetricSpace, PseudoEMetricSpace.ofSeminormedSpaceCore, ofSeminormedSpaceCore
-/
abbrev PseudoMetricSpace.ofSeminormedSpaceCoreReplaceUniformity {𝕜 E : Type*} [NormedField 𝕜]
    [AddCommGroup E] [Norm E] [Module 𝕜 E] [U : UniformSpace E]
    (core : SeminormedSpace.Core 𝕜 E)
    (H : 𝓤[U] = 𝓤[PseudoEMetricSpace.toUniformSpace
        (self := PseudoEMetricSpace.ofSeminormedSpaceCore core)]) :
    PseudoMetricSpace E :=
  .replaceUniformity (.ofSeminormedSpaceCore core) H

/--
Definition of `PseudoMetricSpace.ofSeminormedSpaceCoreReplaceTopology` / `PseudoMetricSpace.ofSeminormedSpaceCoreReplaceTopology` 的定义

English:
abbreviation PseudoMetricSpace.ofSeminormedSpaceCoreReplaceTopology
  signature: {𝕜 E : Type*} [NormedField 𝕜]
  body: .replaceTopology (.ofSeminormedSpaceCore core) H

中文:
缩写 伪度量空间.ofSeminormedSpaceCoreReplaceTopology
  签名: {𝕜 E : 类型} [赋范域 𝕜]
  定义体: .replaceTopology (.ofSeminormedSpaceCore core) H

Depends on / 依赖: ofSeminormedSpaceCore, replaceTopology
-/
abbrev PseudoMetricSpace.ofSeminormedSpaceCoreReplaceTopology {𝕜 E : Type*} [NormedField 𝕜]
    [AddCommGroup E] [Norm E] [Module 𝕜 E] [T : TopologicalSpace E]
    (core : SeminormedSpace.Core 𝕜 E)
    (H : T = (PseudoEMetricSpace.ofSeminormedSpaceCore
      core).toUniformSpace.toTopologicalSpace) :
    PseudoMetricSpace E :=
  .replaceTopology (.ofSeminormedSpaceCore core) H

open Bornology in
/--
Definition of `PseudoMetricSpace.ofSeminormedSpaceCoreReplaceAll` / `PseudoMetricSpace.ofSeminormedSpaceCoreReplaceAll` 的定义

English:
abbreviation PseudoMetricSpace.ofSeminormedSpaceCoreReplaceAll
  signature: {𝕜 E : Type*} [NormedField 𝕜]
  body: .replaceBornology (.replaceUniformity (.ofSeminormedSpaceCore core) HU) HB

中文:
缩写 伪度量空间.ofSeminormedSpaceCoreReplaceAll
  签名: {𝕜 E : 类型} [赋范域 𝕜]
  定义体: .replaceBornology (.replaceUniformity (.ofSeminormedSpaceCore core) HU) HB

Depends on / 依赖: PseudoEMetricSpace, PseudoEMetricSpace.ofSeminormedSpaceCore, ofSeminormedSpaceCore
-/
abbrev PseudoMetricSpace.ofSeminormedSpaceCoreReplaceAll {𝕜 E : Type*} [NormedField 𝕜]
    [AddCommGroup E] [Norm E] [Module 𝕜 E] [U : UniformSpace E] [B : Bornology E]
    (core : SeminormedSpace.Core 𝕜 E)
    (HU : 𝓤[U] = 𝓤[PseudoEMetricSpace.toUniformSpace
      (self := PseudoEMetricSpace.ofSeminormedSpaceCore core)])
    (HB : forall s : Set E, @IsBounded _ B s
      ↔ @IsBounded _ (PseudoMetricSpace.ofSeminormedSpaceCore core).toBornology s) :
    PseudoMetricSpace E :=
  .replaceBornology (.replaceUniformity (.ofSeminormedSpaceCore core) HU) HB

/--
Definition of `SeminormedAddCommGroup.ofCore` / `SeminormedAddCommGroup.ofCore` 的定义

English:
abbreviation SeminormedAddCommGroup.ofCore
  signature: {𝕜 : Type*} {E : Type*} [NormedField 𝕜] [AddCommGroup E]
  body: { PseudoMetricSpace.ofSeminormedSpaceCore core with }

中文:
缩写 SeminormedAddComm群.ofCore
  签名: {𝕜 : 类型} {E : 类型} [赋范域 𝕜] [加法交换群 E]
  定义体: { PseudoMetricSpace.ofSeminormedSpaceCore core with }

Depends on / 依赖: PseudoMetricSpace, PseudoMetricSpace.ofSeminormedSpaceCore, ofSeminormedSpaceCore
-/
abbrev SeminormedAddCommGroup.ofCore {𝕜 : Type*} {E : Type*} [NormedField 𝕜] [AddCommGroup E]
    [Norm E] [Module 𝕜 E] (core : SeminormedSpace.Core 𝕜 E) : SeminormedAddCommGroup E :=
  { PseudoMetricSpace.ofSeminormedSpaceCore core with }

/--
Definition of `SeminormedAddCommGroup.ofCoreReplaceUniformity` / `SeminormedAddCommGroup.ofCoreReplaceUniformity` 的定义

English:
abbreviation SeminormedAddCommGroup.ofCoreReplaceUniformity
  signature: {𝕜 : Type*} {E : Type*} [NormedField 𝕜]
  body: { PseudoMetricSpace.ofSeminormedSpaceCoreReplaceUniformity core H with }

中文:
缩写 SeminormedAddComm群.ofCoreReplaceUniformity
  签名: {𝕜 : 类型} {E : 类型} [赋范域 𝕜]
  定义体: { PseudoMetricSpace.ofSeminormedSpaceCoreReplaceUniformity core H with }

Depends on / 依赖: PseudoEMetricSpace, PseudoEMetricSpace.ofSeminormedSpaceCore, ofSeminormedSpaceCore
-/
abbrev SeminormedAddCommGroup.ofCoreReplaceUniformity {𝕜 : Type*} {E : Type*} [NormedField 𝕜]
    [AddCommGroup E] [Norm E] [Module 𝕜 E] [U : UniformSpace E]
    (core : SeminormedSpace.Core 𝕜 E)
    (H : 𝓤[U] = 𝓤[PseudoEMetricSpace.toUniformSpace
      (self := PseudoEMetricSpace.ofSeminormedSpaceCore core)]) :
    SeminormedAddCommGroup E :=
  { PseudoMetricSpace.ofSeminormedSpaceCoreReplaceUniformity core H with }

/--
Definition of `SeminormedAddCommGroup.ofCoreReplaceTopology` / `SeminormedAddCommGroup.ofCoreReplaceTopology` 的定义

English:
abbreviation SeminormedAddCommGroup.ofCoreReplaceTopology
  signature: {𝕜 : Type*} {E : Type*} [NormedField 𝕜]
  body: { PseudoMetricSpace.ofSeminormedSpaceCoreReplaceTopology core H with }

中文:
缩写 SeminormedAddComm群.ofCoreReplaceTopology
  签名: {𝕜 : 类型} {E : 类型} [赋范域 𝕜]
  定义体: { PseudoMetricSpace.ofSeminormedSpaceCoreReplaceTopology core H with }

Depends on / 依赖: PseudoMetricSpace, PseudoMetricSpace.ofSeminormedSpaceCoreReplaceTopology, ofSeminormedSpaceCoreReplaceTopology
-/
abbrev SeminormedAddCommGroup.ofCoreReplaceTopology {𝕜 : Type*} {E : Type*} [NormedField 𝕜]
    [AddCommGroup E] [Norm E] [Module 𝕜 E] [T : TopologicalSpace E]
    (core : SeminormedSpace.Core 𝕜 E)
    (H : T = (PseudoEMetricSpace.ofSeminormedSpaceCore
      core).toUniformSpace.toTopologicalSpace) :
    SeminormedAddCommGroup E :=
  { PseudoMetricSpace.ofSeminormedSpaceCoreReplaceTopology core H with }

open Bornology in
/--
Definition of `SeminormedAddCommGroup.ofCoreReplaceAll` / `SeminormedAddCommGroup.ofCoreReplaceAll` 的定义

English:
abbreviation SeminormedAddCommGroup.ofCoreReplaceAll
  signature: {𝕜 : Type*} {E : Type*} [NormedField 𝕜]
  body: { PseudoMetricSpace.ofSeminormedSpaceCoreReplaceAll core HU HB with }

中文:
缩写 SeminormedAddComm群.ofCoreReplaceAll
  签名: {𝕜 : 类型} {E : 类型} [赋范域 𝕜]
  定义体: { PseudoMetricSpace.ofSeminormedSpaceCoreReplaceAll core HU HB with }

Depends on / 依赖: PseudoEMetricSpace, PseudoEMetricSpace.ofSeminormedSpaceCore, ofSeminormedSpaceCore
-/
abbrev SeminormedAddCommGroup.ofCoreReplaceAll {𝕜 : Type*} {E : Type*} [NormedField 𝕜]
    [AddCommGroup E] [Norm E] [Module 𝕜 E] [U : UniformSpace E] [B : Bornology E]
    (core : SeminormedSpace.Core 𝕜 E)
    (HU : 𝓤[U] = 𝓤[PseudoEMetricSpace.toUniformSpace
      (self := PseudoEMetricSpace.ofSeminormedSpaceCore core)])
    (HB : forall s : Set E, @IsBounded _ B s
      ↔ @IsBounded _ (PseudoMetricSpace.ofSeminormedSpaceCore core).toBornology s) :
    SeminormedAddCommGroup E :=
  { PseudoMetricSpace.ofSeminormedSpaceCoreReplaceAll core HU HB with }

/--
Definition of `NormedSpace.Core` / `NormedSpace.Core` 的定义

English:
structure NormedSpace.Core
  parameters: (𝕜 : Type*) (E : Type*)
  extends: SeminormedSpace.Core 𝕜 E
  axioms and operations (1):
    - norm_eq_zero_iff((x : E)) : ‖x‖ = 0 ↔ x = 0

中文:
结构 赋范空间.核
  参数: (𝕜 : 类型) (E : 类型)
  继承: 半赋范空间.核 𝕜 E
  公理与运算 (1 个):
    - norm_eq_zero_iff((x : E)) : ‖x‖ = 0 ↔ x = 0
-/
structure NormedSpace.Core (𝕜 : Type*) (E : Type*)
    [NormedField 𝕜] [AddCommGroup E] [Module 𝕜 E] [Norm E] : Prop
    extends SeminormedSpace.Core 𝕜 E where
  norm_eq_zero_iff (x : E) : ‖x‖ = 0 ↔ x = 0

variable {𝕜 : Type*} {E : Type*} [NormedField 𝕜] [AddCommGroup E] [Module 𝕜 E] [Norm E]

/--
Definition of `NormedAddCommGroup.ofCore` / `NormedAddCommGroup.ofCore` 的定义

English:
abbreviation NormedAddCommGroup.ofCore
  signature: (core : NormedSpace.Core 𝕜 E)
  body: { SeminormedAddCommGroup.ofCore core.toCore with
    eq_of_dist_eq_zero := by
      let := SeminormedAddCommGroup.ofCore core.toCore
      intro x y h
      rw [← sub_eq_zero]; rw [← core.norm_eq_zero_iff]; rw [← norm_neg_add]
      exact h }

中文:
缩写 赋范交换加群.ofCore
  签名: (core : 赋范空间.核 𝕜 E)
  定义体: { SeminormedAddCommGroup.ofCore core.toCore with
    eq_of_dist_eq_zero := by
      let := SeminormedAddCommGroup.ofCore core.toCore
      intro x y h
      rw [← sub_eq_zero]; rw [← core.norm_eq_zero_iff]; rw [← norm_neg_add]
      exact h }

Depends on / 依赖: SeminormedAddCommGroup, SeminormedAddCommGroup.ofCore, core.norm_eq_zero_iff, core.toCore, eq_of_dist_eq_zero, norm_eq_zero_iff, norm_neg_add, ofCore, sub_eq_zero, toCore
-/
abbrev NormedAddCommGroup.ofCore (core : NormedSpace.Core 𝕜 E) : NormedAddCommGroup E :=
  { SeminormedAddCommGroup.ofCore core.toCore with
    eq_of_dist_eq_zero := by
      let := SeminormedAddCommGroup.ofCore core.toCore
      intro x y h
      rw [← sub_eq_zero]; rw [← core.norm_eq_zero_iff]; rw [← norm_neg_add]
      exact h }

/--
Definition of `NormedAddCommGroup.ofCoreReplaceUniformity` / `NormedAddCommGroup.ofCoreReplaceUniformity` 的定义

English:
abbreviation NormedAddCommGroup.ofCoreReplaceUniformity
  signature: [U : UniformSpace E] (core : NormedSpace.Core 𝕜 E)
  body: { SeminormedAddCommGroup.ofCoreReplaceUniformity core.toCore H with
    eq_of_dist_eq_zero := by
      let := SeminormedAddCommGroup.ofCore core.toCore
      intro x y h
      rw [← sub_eq_zero]; rw [← core.norm_eq_zero_iff]; rw [← norm_neg_add]
      exact h }

中文:
缩写 赋范交换加群.ofCoreReplaceUniformity
  签名: [U : 一致空间 E] (core : 赋范空间.核 𝕜 E)
  定义体: { SeminormedAddCommGroup.ofCoreReplaceUniformity core.toCore H with
    eq_of_dist_eq_zero := by
      let := SeminormedAddCommGroup.ofCore core.toCore
      intro x y h
      rw [← sub_eq_zero]; rw [← core.norm_eq_zero_iff]; rw [← norm_neg_add]
      exact h }

Depends on / 依赖: PseudoEMetricSpace, PseudoEMetricSpace.ofSeminormedSpaceCore, core.toCore, ofSeminormedSpaceCore, toCore
-/
abbrev NormedAddCommGroup.ofCoreReplaceUniformity [U : UniformSpace E] (core : NormedSpace.Core 𝕜 E)
    (H : 𝓤[U] = 𝓤[PseudoEMetricSpace.toUniformSpace
      (self := PseudoEMetricSpace.ofSeminormedSpaceCore core.toCore)]) :
    NormedAddCommGroup E :=
  { SeminormedAddCommGroup.ofCoreReplaceUniformity core.toCore H with
    eq_of_dist_eq_zero := by
      let := SeminormedAddCommGroup.ofCore core.toCore
      intro x y h
      rw [← sub_eq_zero]; rw [← core.norm_eq_zero_iff]; rw [← norm_neg_add]
      exact h }

/--
Definition of `NormedAddCommGroup.ofCoreReplaceTopology` / `NormedAddCommGroup.ofCoreReplaceTopology` 的定义

English:
abbreviation NormedAddCommGroup.ofCoreReplaceTopology
  signature: [T : TopologicalSpace E]
  body: { SeminormedAddCommGroup.ofCoreReplaceTopology core.toCore H with
    eq_of_dist_eq_zero := by
      let := SeminormedAddCommGroup.ofCore core.toCore
      intro x y h
      rw [← sub_eq_zero]; rw [← core.norm_eq_zero_iff]; rw [← norm_neg_add]
      exact h }

中文:
缩写 赋范交换加群.ofCoreReplaceTopology
  签名: [T : 拓扑空间 E]
  定义体: { SeminormedAddCommGroup.ofCoreReplaceTopology core.toCore H with
    eq_of_dist_eq_zero := by
      let := SeminormedAddCommGroup.ofCore core.toCore
      intro x y h
      rw [← sub_eq_zero]; rw [← core.norm_eq_zero_iff]; rw [← norm_neg_add]
      exact h }

Depends on / 依赖: SeminormedAddCommGroup, SeminormedAddCommGroup.ofCore, SeminormedAddCommGroup.ofCoreReplaceTopology, core.norm_eq_zero_iff, core.toCore, eq_of_dist_eq_zero, norm_eq_zero_iff, norm_neg_add, ofCore, ofCoreReplaceTopology, sub_eq_zero, toCore
-/
abbrev NormedAddCommGroup.ofCoreReplaceTopology [T : TopologicalSpace E]
    (core : NormedSpace.Core 𝕜 E)
    (H : T = (PseudoEMetricSpace.ofSeminormedSpaceCore
      core.toCore).toUniformSpace.toTopologicalSpace) :
    NormedAddCommGroup E :=
  { SeminormedAddCommGroup.ofCoreReplaceTopology core.toCore H with
    eq_of_dist_eq_zero := by
      let := SeminormedAddCommGroup.ofCore core.toCore
      intro x y h
      rw [← sub_eq_zero]; rw [← core.norm_eq_zero_iff]; rw [← norm_neg_add]
      exact h }

open Bornology in
/--
Definition of `NormedAddCommGroup.ofCoreReplaceAll` / `NormedAddCommGroup.ofCoreReplaceAll` 的定义

English:
abbreviation NormedAddCommGroup.ofCoreReplaceAll
  signature: [U : UniformSpace E] [B : Bornology E]
  body: { SeminormedAddCommGroup.ofCoreReplaceAll core.toCore HU HB with
    eq_of_dist_eq_zero := by
      let := SeminormedAddCommGroup.ofCore core.toCore
      intro x y h
      rw [← sub_eq_zero]; rw [← core.norm_eq_zero_iff]; rw [← norm_neg_add]
      exact h }

中文:
缩写 赋范交换加群.ofCoreReplaceAll
  签名: [U : 一致空间 E] [B : 有界结构 E]
  定义体: { SeminormedAddCommGroup.ofCoreReplaceAll core.toCore HU HB with
    eq_of_dist_eq_zero := by
      let := SeminormedAddCommGroup.ofCore core.toCore
      intro x y h
      rw [← sub_eq_zero]; rw [← core.norm_eq_zero_iff]; rw [← norm_neg_add]
      exact h }

Depends on / 依赖: PseudoEMetricSpace, PseudoEMetricSpace.ofSeminormedSpaceCore, core.toCore, ofSeminormedSpaceCore, toCore
-/
abbrev NormedAddCommGroup.ofCoreReplaceAll [U : UniformSpace E] [B : Bornology E]
    (core : NormedSpace.Core 𝕜 E)
    (HU : 𝓤[U] = 𝓤[PseudoEMetricSpace.toUniformSpace
      (self := PseudoEMetricSpace.ofSeminormedSpaceCore core.toCore)])
    (HB : forall s : Set E, @IsBounded _ B s
      ↔ @IsBounded _ (PseudoMetricSpace.ofSeminormedSpaceCore core.toCore).toBornology s) :
    NormedAddCommGroup E :=
  { SeminormedAddCommGroup.ofCoreReplaceAll core.toCore HU HB with
    eq_of_dist_eq_zero := by
      let := SeminormedAddCommGroup.ofCore core.toCore
      intro x y h
      rw [← sub_eq_zero]; rw [← core.norm_eq_zero_iff]; rw [← norm_neg_add]
      exact h }

/--
Definition of `NormedSpace.ofCore` / `NormedSpace.ofCore` 的定义

English:
abbreviation NormedSpace.ofCore
  signature: {𝕜 : Type*} {E : Type*} [NormedField 𝕜] [SeminormedAddCommGroup E]
  body: by rw [core.norm_smul r x]

中文:
缩写 赋范空间.ofCore
  签名: {𝕜 : 类型} {E : 类型} [赋范域 𝕜] [SeminormedAddComm群 E]
  定义体: by rw [core.norm_smul r x]

Depends on / 依赖: core.norm_smul, norm_smul
-/
abbrev NormedSpace.ofCore {𝕜 : Type*} {E : Type*} [NormedField 𝕜] [SeminormedAddCommGroup E]
    [Module 𝕜 E] (core : NormedSpace.Core 𝕜 E) : NormedSpace 𝕜 E where
  norm_smul_le r x := by rw [core.norm_smul r x]

end Core

variable {G H : Type*} [SeminormedAddCommGroup G] [SeminormedAddCommGroup H] [NormedSpace Real H]
  {s : Set G}

/--
lemma `AddMonoidHom.continuous_of_isBounded_nhds_zero` / 引理 `AddMonoidHom.continuous_of_isBounded_nhds_zero`

English:
lemma AddMonoidHom.continuous_of_isBounded_nhds_zero
  statement: (f : G ->+ H) (hs : s in 𝓝 (0 : G))
  proof: by
  obtain ⟨δ, hδ, hUε⟩ := Metric.mem_nhds_iff.mp hs
  obtain ⟨C, hC⟩ := (isBounded_iff_subset_ball 0).1 (hbounded.subset <| image_mono hUε)
  refine continuous_of_continuousAt_zero _ (continuousAt_iff.2 fun ε (hε : _ < _) => ?_)
  simp only [dist_zero_right, map_zero]
  simp only [subset_def, mem_image, mem_ball, dist_zero_right, forall_exists_index, and_imp,
    forall_apply_eq_imp_iff₂] at hC
have hC₀ : 0 < C := (norm_nonneg _).trans_lt hC 0 (by simpa)
  obtain ⟨n, hn⟩ := exists_nat_gt (C / ε)
  have hnpos : 0 < (n : Real) := (div_pos hC₀ hε).trans hn
  have hn₀ : n != 0 := by rintro rfl; simp at hnpos
  refine ⟨δ / n, div_pos hδ hnpos, fun {x} hxδ => ?_⟩
  calc
    ‖f x‖
    _ = ‖(n : Real)⁻¹ • f (n • x)‖ := by simp [← Nat.cast_smul_eq_nsmul Real, hn₀]
    _ <= ‖(n : Real)⁻¹‖ * ‖f (n • x)‖ := norm_smul_le ..
    _ < ‖(n : Real)⁻¹‖ * C := by
      gcongr
      · simpa [pos_iff_ne_zero]
· refine hC _ norm_nsmul_le.trans_lt ?_
        simpa only [norm_mul, Real.norm_natCast, lt_div_iff₀ hnpos, mul_comm] using hxδ
    _ = (n : Real)⁻¹ * C := by simp
    _ < (C / ε : Real)⁻¹ * C := by gcongr
    _ = ε := by simp [hC₀.ne']

中文:
引理 加法幺半群态射.continuous_of_isBounded_nhds_zero
  结论: (f : G ->+ H) (hs : s in 𝓝 (0 : G))
  证明: by
  obtain ⟨δ, hδ, hUε⟩ := Metric.mem_nhds_iff.mp hs
  obtain ⟨C, hC⟩ := (isBounded_iff_subset_ball 0).1 (hbounded.subset <| image_mono hUε)
  refine continuous_of_continuousAt_zero _ (continuousAt_iff.2 fun ε (hε : _ < _) => ?_)
  simp only [dist_zero_right, map_zero]
  simp only [subset_def, mem_image, mem_ball, dist_zero_right, forall_exists_index, and_imp,
    forall_apply_eq_imp_iff₂] at hC
have hC₀ : 0 < C := (norm_nonneg _).trans_lt hC 0 (by simpa)
  obtain ⟨n, hn⟩ := exists_nat_gt (C / ε)
  have hnpos : 0 < (n : Real) := (div_pos hC₀ hε).trans hn
  have hn₀ : n != 0 := by rintro rfl; simp at hnpos
  refine ⟨δ / n, div_pos hδ hnpos, fun {x} hxδ => ?_⟩
  calc
    ‖f x‖
    _ = ‖(n : Real)⁻¹ • f (n • x)‖ := by simp [← Nat.cast_smul_eq_nsmul Real, hn₀]
    _ <= ‖(n : Real)⁻¹‖ * ‖f (n • x)‖ := norm_smul_le ..
    _ < ‖(n : Real)⁻¹‖ * C := by
      gcongr
      · simpa [pos_iff_ne_zero]
· refine hC _ norm_nsmul_le.trans_lt ?_
        simpa only [norm_mul, Real.norm_natCast, lt_div_iff₀ hnpos, mul_comm] using hxδ
    _ = (n : Real)⁻¹ * C := by simp
    _ < (C / ε : Real)⁻¹ * C := by gcongr
    _ = ε := by simp [hC₀.ne']

Depends on / 依赖: Metric, Metric.mem_nhds_iff.mp, and_imp, continuousAt_iff, continuous_of_continuousAt_zero, dist_zero_right, exists_nat_gt, forall_exists_index, hbounded, hbounded.subset, image_mono, isBounded_iff_subset_ball, map_zero, mem_ball, mem_image, mem_nhds_iff, norm_nonneg, subset, subset_def, trans_lt
-/
lemma AddMonoidHom.continuous_of_isBounded_nhds_zero (f : G ->+ H) (hs : s in 𝓝 (0 : G))
    (hbounded : IsBounded (f '' s)) : Continuous f := by
  obtain ⟨δ, hδ, hUε⟩ := Metric.mem_nhds_iff.mp hs
  obtain ⟨C, hC⟩ := (isBounded_iff_subset_ball 0).1 (hbounded.subset <| image_mono hUε)
  refine continuous_of_continuousAt_zero _ (continuousAt_iff.2 fun ε (hε : _ < _) => ?_)
  simp only [dist_zero_right, map_zero]
  simp only [subset_def, mem_image, mem_ball, dist_zero_right, forall_exists_index, and_imp,
    forall_apply_eq_imp_iff₂] at hC
have hC₀ : 0 < C := (norm_nonneg _).trans_lt hC 0 (by simpa)
  obtain ⟨n, hn⟩ := exists_nat_gt (C / ε)
  have hnpos : 0 < (n : Real) := (div_pos hC₀ hε).trans hn
  have hn₀ : n != 0 := by rintro rfl; simp at hnpos
  refine ⟨δ / n, div_pos hδ hnpos, fun {x} hxδ => ?_⟩
  calc
    ‖f x‖
    _ = ‖(n : Real)⁻¹ • f (n • x)‖ := by simp [← Nat.cast_smul_eq_nsmul Real, hn₀]
    _ <= ‖(n : Real)⁻¹‖ * ‖f (n • x)‖ := norm_smul_le ..
    _ < ‖(n : Real)⁻¹‖ * C := by
      gcongr
      · simpa [pos_iff_ne_zero]
· refine hC _ norm_nsmul_le.trans_lt ?_
        simpa only [norm_mul, Real.norm_natCast, lt_div_iff₀ hnpos, mul_comm] using hxδ
    _ = (n : Real)⁻¹ * C := by simp
    _ < (C / ε : Real)⁻¹ * C := by gcongr
    _ = ε := by simp [hC₀.ne']
