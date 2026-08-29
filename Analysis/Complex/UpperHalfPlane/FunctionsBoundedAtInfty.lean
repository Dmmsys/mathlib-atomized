/-
Copyright (c) 2022 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck, David Loeffler
-/
module

public import Mathlib.Algebra.Module.Submodule.Basic
public import Mathlib.Analysis.Complex.UpperHalfPlane.Topology
public import Mathlib.Order.Filter.ZeroAndBoundedAtFilter

/-!
# Bounded at infinity

For complex-valued functions on the upper half plane, this file defines the filter
`UpperHalfPlane.atImInfty` required for defining when functions are bounded at infinity and zero at
infinity. Both of which are relevant for defining modular forms.
-/

@[expose] public section

open Complex Filter

open scoped Topology UpperHalfPlane

noncomputable section

namespace UpperHalfPlane

/--
Definition of `atImInfty` / `atImInfty` 的定义

English:
definition atImInfty
  body: Filter.atTop.comap UpperHalfPlane.im

中文:
定义 atImInfty
  定义体: Filter.atTop.comap UpperHalfPlane.im

Depends on / 依赖: Filter, Filter.atTop.comap, UpperHalfPlane, UpperHalfPlane.im
-/
def atImInfty :=
  Filter.atTop.comap UpperHalfPlane.im

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: atImInfty.NeBot
  body: by
  refine comap_neBot_iff_frequently.mpr (Eventually.frequently ?_)
  filter_upwards [eventually_gt_atTop 0] with t ht
    using ⟨⟨I * t, by simp [ht]⟩, by simp⟩

中文:
实例 :
  签名: atImInfty.NeBot
  定义体: by
  refine comap_neBot_iff_frequently.mpr (Eventually.frequently ?_)
  filter_upwards [eventually_gt_atTop 0] with t ht
    using ⟨⟨I * t, by simp [ht]⟩, by simp⟩

Depends on / 依赖: Eventually, Eventually.frequently, comap_neBot_iff_frequently, comap_neBot_iff_frequently.mpr, eventually_gt_atTop, filter_upwards, frequently
-/
instance : atImInfty.NeBot := by
  refine comap_neBot_iff_frequently.mpr (Eventually.frequently ?_)
  filter_upwards [eventually_gt_atTop 0] with t ht
    using ⟨⟨I * t, by simp [ht]⟩, by simp⟩

/--
theorem `atImInfty_basis` / 定理 `atImInfty_basis`

English:
theorem atImInfty_basis
  statement: atImInfty.HasBasis (fun _ => True) fun i : Real => im ⁻¹' Set.Ici i
  proof: Filter.HasBasis.comap UpperHalfPlane.im Filter.atTop_basis

中文:
定理 atImInfty_basis
  结论: atImInfty.有基 (fun _ => 真) fun i : 实数 => im ⁻¹' 集合.左闭右无界区间 i
  证明: Filter.HasBasis.comap UpperHalfPlane.im Filter.atTop_basis

Depends on / 依赖: Filter, Filter.HasBasis.comap, Filter.atTop_basis, HasBasis, UpperHalfPlane, UpperHalfPlane.im, atTop_basis
-/
theorem atImInfty_basis : atImInfty.HasBasis (fun _ => True) fun i : Real => im ⁻¹' Set.Ici i :=
  Filter.HasBasis.comap UpperHalfPlane.im Filter.atTop_basis

/--
theorem `atImInfty_mem` / 定理 `atImInfty_mem`

English:
theorem atImInfty_mem
  given: (S : Set ℍ)
  statement: S in atImInfty ↔ exists A : Real, forall z : ℍ, A <= im z -> z in S
  proof: by
  simp only [atImInfty_basis.mem_iff, true_and]; rfl

中文:
定理 atImInfty_mem
  条件: (S : 集合 ℍ)
  结论: S in atImInfty ↔ 存在 A : 实数, 对任意 z : ℍ, A <= im z -> z in S
  证明: by
  simp only [atImInfty_basis.mem_iff, true_and]; rfl

Depends on / 依赖: atImInfty_basis, atImInfty_basis.mem_iff, mem_iff, true_and
-/
theorem atImInfty_mem (S : Set ℍ) : S in atImInfty ↔ exists A : Real, forall z : ℍ, A <= im z -> z in S := by
  simp only [atImInfty_basis.mem_iff, true_and]; rfl

/--
Definition of `IsBoundedAtImInfty` / `IsBoundedAtImInfty` 的定义

English:
definition IsBoundedAtImInfty
  signature: {α : Type*} [Norm α] (f : ℍ -> α)
  body: BoundedAtFilter atImInfty f

中文:
定义 IsBoundedAtImInfty
  签名: {α : 类型} [范数 α] (f : ℍ -> α)
  定义体: BoundedAtFilter atImInfty f

Depends on / 依赖: BoundedAtFilter, atImInfty
-/
def IsBoundedAtImInfty {α : Type*} [Norm α] (f : ℍ -> α) : Prop :=
  BoundedAtFilter atImInfty f

/--
Definition of `IsZeroAtImInfty` / `IsZeroAtImInfty` 的定义

English:
definition IsZeroAtImInfty
  signature: {α : Type*} [Zero α] [TopologicalSpace α] (f : ℍ -> α)
  body: ZeroAtFilter atImInfty f

中文:
定义 IsZeroAtImInfty
  签名: {α : 类型} [零 α] [拓扑空间 α] (f : ℍ -> α)
  定义体: ZeroAtFilter atImInfty f

Depends on / 依赖: ZeroAtFilter, atImInfty
-/
def IsZeroAtImInfty {α : Type*} [Zero α] [TopologicalSpace α] (f : ℍ -> α) : Prop :=
  ZeroAtFilter atImInfty f

/--
theorem `zero_form_isBoundedAtImInfty` / 定理 `zero_form_isBoundedAtImInfty`

English:
theorem zero_form_isBoundedAtImInfty
  given: {α : Type*} [NormedField α]
  proof: const_boundedAtFilter atImInfty (0 : α)

中文:
定理 zero_form_isBoundedAtImInfty
  条件: {α : 类型} [赋范域 α]
  证明: const_boundedAtFilter atImInfty (0 : α)

Depends on / 依赖: atImInfty, const_boundedAtFilter
-/
theorem zero_form_isBoundedAtImInfty {α : Type*} [NormedField α] :
    IsBoundedAtImInfty (0 : ℍ -> α) :=
  const_boundedAtFilter atImInfty (0 : α)

/--
Definition of `zeroAtImInftySubmodule` / `zeroAtImInftySubmodule` 的定义

English:
definition zeroAtImInftySubmodule
  signature: (α : Type*) [NormedField α]
  body: zeroAtFilterSubmodule _ atImInfty

中文:
定义 zeroAtImInftySubmodule
  签名: (α : 类型) [赋范域 α]
  定义体: zeroAtFilterSubmodule _ atImInfty

Depends on / 依赖: atImInfty, zeroAtFilterSubmodule
-/
def zeroAtImInftySubmodule (α : Type*) [NormedField α] : Submodule α (ℍ -> α) :=
  zeroAtFilterSubmodule _ atImInfty

/--
Definition of `boundedAtImInftySubalgebra` / `boundedAtImInftySubalgebra` 的定义

English:
definition boundedAtImInftySubalgebra
  signature: (α : Type*) [NormedField α]
  body: boundedFilterSubalgebra _ atImInfty

中文:
定义 boundedAtImInftySubalgebra
  签名: (α : 类型) [赋范域 α]
  定义体: boundedFilterSubalgebra _ atImInfty

Depends on / 依赖: atImInfty, boundedFilterSubalgebra
-/
def boundedAtImInftySubalgebra (α : Type*) [NormedField α] : Subalgebra α (ℍ -> α) :=
  boundedFilterSubalgebra _ atImInfty

/--
theorem `isBoundedAtImInfty_iff` / 定理 `isBoundedAtImInfty_iff`

English:
theorem isBoundedAtImInfty_iff
  given: {α : Type*} [Norm α] {f : ℍ -> α}
  proof: by
  simp [IsBoundedAtImInfty, BoundedAtFilter, Asymptotics.isBigO_iff, Filter.Eventually,
    atImInfty_mem]

中文:
定理 isBoundedAtImInfty_iff
  条件: {α : 类型} [范数 α] {f : ℍ -> α}
  证明: by
  simp [IsBoundedAtImInfty, BoundedAtFilter, Asymptotics.isBigO_iff, Filter.Eventually,
    atImInfty_mem]

Depends on / 依赖: Asymptotics, Asymptotics.isBigO_iff, BoundedAtFilter, Eventually, Filter, Filter.Eventually, IsBoundedAtImInfty, atImInfty_mem, isBigO_iff
-/
theorem isBoundedAtImInfty_iff {α : Type*} [Norm α] {f : ℍ -> α} :
    IsBoundedAtImInfty f ↔ exists M A : Real, forall z : ℍ, A <= im z -> ‖f z‖ <= M := by
  simp [IsBoundedAtImInfty, BoundedAtFilter, Asymptotics.isBigO_iff, Filter.Eventually,
    atImInfty_mem]

/--
theorem `isZeroAtImInfty_iff` / 定理 `isZeroAtImInfty_iff`

English:
theorem isZeroAtImInfty_iff
  given: {α : Type*} [SeminormedAddGroup α] {f : ℍ -> α}
  proof: (atImInfty_basis.tendsto_iff Metric.nhds_basis_closedBall).trans by simp

中文:
定理 isZeroAtImInfty_iff
  条件: {α : 类型} [半赋范加群 α] {f : ℍ -> α}
  证明: (atImInfty_basis.tendsto_iff Metric.nhds_basis_closedBall).trans by simp

Depends on / 依赖: Metric, Metric.nhds_basis_closedBall, atImInfty_basis, atImInfty_basis.tendsto_iff, nhds_basis_closedBall, tendsto_iff
-/
theorem isZeroAtImInfty_iff {α : Type*} [SeminormedAddGroup α] {f : ℍ -> α} :
    IsZeroAtImInfty f ↔ forall ε : Real, 0 < ε -> exists A : Real, forall z : ℍ, A <= im z -> ‖f z‖ <= ε :=
(atImInfty_basis.tendsto_iff Metric.nhds_basis_closedBall).trans by simp

/--
theorem `IsZeroAtImInfty.isBoundedAtImInfty` / 定理 `IsZeroAtImInfty.isBoundedAtImInfty`

English:
theorem IsZeroAtImInfty.isBoundedAtImInfty
  statement: {α : Type*} [SeminormedAddGroup α] {f : ℍ -> α}
  proof: hf.boundedAtFilter

中文:
定理 IsZeroAtImInfty.isBoundedAtImInfty
  结论: {α : 类型} [半赋范加群 α] {f : ℍ -> α}
  证明: hf.boundedAtFilter

Depends on / 依赖: boundedAtFilter, hf.boundedAtFilter
-/
theorem IsZeroAtImInfty.isBoundedAtImInfty {α : Type*} [SeminormedAddGroup α] {f : ℍ -> α}
    (hf : IsZeroAtImInfty f) : IsBoundedAtImInfty f :=
  hf.boundedAtFilter

set_option backward.isDefEq.respectTransparency false in
/--
lemma `tendsto_comap_im_ofComplex` / 引理 `tendsto_comap_im_ofComplex`

English:
lemma tendsto_comap_im_ofComplex
  proof: by
  simp only [atImInfty, tendsto_comap_iff, Function.comp_def]
  refine tendsto_comap.congr' ?_
  filter_upwards [preimage_mem_comap (Ioi_mem_atTop 0)] with z hz
  simp [ofComplex_apply_of_im_pos hz]

中文:
引理 tendsto_comap_im_ofComplex
  证明: by
  simp only [atImInfty, tendsto_comap_iff, Function.comp_def]
  refine tendsto_comap.congr' ?_
  filter_upwards [preimage_mem_comap (Ioi_mem_atTop 0)] with z hz
  simp [ofComplex_apply_of_im_pos hz]

Depends on / 依赖: Function, Function.comp_def, Ioi_mem_atTop, atImInfty, comp_def, filter_upwards, ofComplex_apply_of_im_pos, preimage_mem_comap, tendsto_comap, tendsto_comap.congr, tendsto_comap_iff
-/
lemma tendsto_comap_im_ofComplex :
    Tendsto ofComplex (comap Complex.im atTop) atImInfty := by
  simp only [atImInfty, tendsto_comap_iff, Function.comp_def]
  refine tendsto_comap.congr' ?_
  filter_upwards [preimage_mem_comap (Ioi_mem_atTop 0)] with z hz
  simp [ofComplex_apply_of_im_pos hz]

/--
lemma `tendsto_coe_atImInfty` / 引理 `tendsto_coe_atImInfty`

English:
lemma tendsto_coe_atImInfty
  proof: by
  simpa only [atImInfty, tendsto_comap_iff, Function.comp_def,
    funext UpperHalfPlane.coe_im] using tendsto_comap

中文:
引理 tendsto_coe_atImInfty
  证明: by
  simpa only [atImInfty, tendsto_comap_iff, Function.comp_def,
    funext UpperHalfPlane.coe_im] using tendsto_comap

Depends on / 依赖: Function, Function.comp_def, UpperHalfPlane, UpperHalfPlane.coe_im, atImInfty, coe_im, comp_def, tendsto_comap, tendsto_comap_iff
-/
lemma tendsto_coe_atImInfty :
    Tendsto UpperHalfPlane.coe atImInfty (comap Complex.im atTop) := by
  simpa only [atImInfty, tendsto_comap_iff, Function.comp_def,
    funext UpperHalfPlane.coe_im] using tendsto_comap

/--
lemma `tendsto_smul_atImInfty` / 引理 `tendsto_smul_atImInfty`

English:
lemma tendsto_smul_atImInfty
  given: {g : GL (Fin 2) Real} (hg : g 1 0 = 0)
  proof: by
  suffices Tendsto (fun τ => |g 0 0 / g 1 1| * τ.im) atImInfty atTop by
    simpa [atImInfty, Function.comp_def, im_smul, num, denom, hg, abs_div, abs_mul,
      abs_of_pos (UpperHalfPlane.im_pos _), mul_div_right_comm]
  apply tendsto_comap.const_mul_atTop
  simpa [Matrix.det_fin_two, hg] using 

中文:
引理 tendsto_smul_atImInfty
  条件: {g : GL (有限集 2) 实数} (hg : g 1 0 = 0)
  证明: by
  suffices Tendsto (fun τ => |g 0 0 / g 1 1| * τ.im) atImInfty atTop by
    simpa [atImInfty, Function.comp_def, im_smul, num, denom, hg, abs_div, abs_mul,
      abs_of_pos (UpperHalfPlane.im_pos _), mul_div_right_comm]
  apply tendsto_comap.const_mul_atTop
  simpa [Matrix.det_fin_two, hg] using 

Depends on / 依赖: Function, Function.comp_def, Matrix, Matrix.det_fin_two, Tendsto, UpperHalfPlane, UpperHalfPlane.im_pos, abs_div, abs_mul, abs_of_pos, atImInfty, comp_def, const_mul_atTop, det_fin_two, det_ne_zero, g.det_ne_zero, im_pos, im_smul, mul_div_right_comm, tendsto_comap
-/
lemma tendsto_smul_atImInfty {g : GL (Fin 2) Real} (hg : g 1 0 = 0) :
    Tendsto (fun τ => g • τ) atImInfty atImInfty := by
  suffices Tendsto (fun τ => |g 0 0 / g 1 1| * τ.im) atImInfty atTop by
    simpa [atImInfty, Function.comp_def, im_smul, num, denom, hg, abs_div, abs_mul,
      abs_of_pos (UpperHalfPlane.im_pos _), mul_div_right_comm]
  apply tendsto_comap.const_mul_atTop
  simpa [Matrix.det_fin_two, hg] using g.det_ne_zero

end UpperHalfPlane
