/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import Mathlib.Analysis.Convex.Cone.Extension
public import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
public import Mathlib.Analysis.LocallyConvex.WeakDual
public import Mathlib.Analysis.Normed.Module.RCLike.Extend
public import Mathlib.Topology.Algebra.Module.FiniteDimension

/-!
# Hahn-Banach theorem for polynormable spaces

In this file, we prove the analytic Hahn-Banach theorem for polynormable spaces over a field
satisfying `IsRCLikeNormedField`. For any continuous linear functional on a subspace, we can extend
it to the entire space. Note that we cannot use `LocallyConvexSpace` because an
`IsRCLikeNormedField` has no order structure.

We prove
* `Module.Dual.exists_continuous_extension_of_le_seminorm`: Hahn-Banach theorem for linear
  functionals dominated by a continuous seminorm on polynormable spaces over a field satisfying
  `IsRCLikeNormedField`.
* `StrongDual.exists_extension`: Hahn-Banach theorem for continuous linear functionals on
  polynormable spaces over fields satisfying `IsRCLikeNormedField`.

-/

public section

open Module Topology RCLike

open scoped ComplexConjugate

variable {𝕜 E : Type*} [AddCommGroup E]

/--
theorem `Module.Dual.exists_extension_of_le_seminorm_real` / 定理 `Module.Dual.exists_extension_of_le_seminorm_real`

English:
theorem Module.Dual.exists_extension_of_le_seminorm_real
  statement: [Module Real E]
  proof: by
  obtain ⟨g, hg, hl⟩ := by
    refine exists_extension_of_le_sublinear ⟨S, f⟩ p (fun _ hc _ => ?_) ?_ hp
    · simp [map_smul_eq_mul, abs_of_nonneg hc.le]
    · exact fun x y => map_add_le_add p x y
  exact ⟨g, hg, p.abs_le_of_le hl⟩

中文:
定理 模.对偶.存在_extension_of_le_seminorm_real
  结论: [模 实数 E]
  证明: by
  obtain ⟨g, hg, hl⟩ := by
    refine exists_extension_of_le_sublinear ⟨S, f⟩ p (fun _ hc _ => ?_) ?_ hp
    · simp [map_smul_eq_mul, abs_of_nonneg hc.le]
    · exact fun x y => map_add_le_add p x y
  exact ⟨g, hg, p.abs_le_of_le hl⟩

Depends on / 依赖: abs_le_of_le, abs_of_nonneg, exists_extension_of_le_sublinear, hc.le, map_add_le_add, map_smul_eq_mul, p.abs_le_of_le
-/
theorem Module.Dual.exists_extension_of_le_seminorm_real [Module Real E]
    (S : Subspace Real E) (f : Dual Real S)
    {p : Seminorm Real E} (hp : forall x, f x <= p x) :
    exists g : Dual Real E, (forall x : S, g x = f x) ∧ forall x, |g x| <= p x := by
  obtain ⟨g, hg, hl⟩ := by
    refine exists_extension_of_le_sublinear ⟨S, f⟩ p (fun _ hc _ => ?_) ?_ hp
    · simp [map_smul_eq_mul, abs_of_nonneg hc.le]
    · exact fun x y => map_add_le_add p x y
  exact ⟨g, hg, p.abs_le_of_le hl⟩

variable [NormedField 𝕜] [IsRCLikeNormedField 𝕜]

/--
theorem `Module.Dual.exists_extension_of_le_seminorm` / 定理 `Module.Dual.exists_extension_of_le_seminorm`

English:
theorem Module.Dual.exists_extension_of_le_seminorm
  statement: [Module 𝕜 E] (S : Submodule 𝕜 E) (f : Dual 𝕜 S)
  proof: by
  let : RCLike 𝕜 := IsRCLikeNormedField.rclike 𝕜
  let : Module Real E := .restrictScalars Real 𝕜 E
  let : IsScalarTower Real 𝕜 E := .restrictScalars _ _ _
  let fr : Dual Real S := reLm.comp (f.restrictScalars Real)
  obtain ⟨g, (hg : forall x : S, g x = fr x), hgp⟩ :=
    fr.exists_extension_o

中文:
定理 模.对偶.存在_extension_of_le_seminorm
  结论: [模 𝕜 E] (S : 子模 𝕜 E) (f : 对偶 𝕜 S)
  证明: by
  let : RCLike 𝕜 := IsRCLikeNormedField.rclike 𝕜
  let : Module Real E := .restrictScalars Real 𝕜 E
  let : IsScalarTower Real 𝕜 E := .restrictScalars _ _ _
  let fr : Dual Real S := reLm.comp (f.restrictScalars Real)
  obtain ⟨g, (hg : forall x : S, g x = fr x), hgp⟩ :=
    fr.exists_extension_o

Depends on / 依赖: IsRCLikeNormedField, IsRCLikeNormedField.rclike, IsScalarTower, Module, RCLike, S.restrictScalars, Submodule, Submodule.coe_smul, coe_smul, exists_extension_of_le_seminorm_real, extendRCLike, extendRCLike_apply, f.restrictScalars, fr.exists_extension_of_le_seminorm_real, g.extendRCLike, g.extendRCLike_apply, p.restrictScalars, rclike, reLm.comp, re_le_norm
-/
theorem Module.Dual.exists_extension_of_le_seminorm [Module 𝕜 E] (S : Submodule 𝕜 E) (f : Dual 𝕜 S)
    {p : Seminorm 𝕜 E} (hp : forall x, ‖f x‖ <= p x) :
    exists g : Dual 𝕜 E, (forall x : S, g x = f x) ∧ forall x, ‖g x‖ <= p x := by
  let : RCLike 𝕜 := IsRCLikeNormedField.rclike 𝕜
  let : Module Real E := .restrictScalars Real 𝕜 E
  let : IsScalarTower Real 𝕜 E := .restrictScalars _ _ _
  let fr : Dual Real S := reLm.comp (f.restrictScalars Real)
  obtain ⟨g, (hg : forall x : S, g x = fr x), hgp⟩ :=
    fr.exists_extension_of_le_seminorm_real (S.restrictScalars Real) (p := p.restrictScalars Real)
      fun x => (re_le_norm (f x)).trans (hp x)
  refine ⟨g.extendRCLike, fun x => ?_, fun x => ?_⟩
  · rw [g.extendRCLike_apply, ← Submodule.coe_smul, hg, hg]
    simp [fr, mul_comm I]
  · apply norm_extendRCLike_le_seminorm
    exact hgp

variable [TopologicalSpace E]

/--
theorem `Module.Dual.exists_continuous_extension_of_le_seminorm_real` / 定理 `Module.Dual.exists_continuous_extension_of_le_seminorm_real`

English:
theorem Module.Dual.exists_continuous_extension_of_le_seminorm_real
  proof: by
  obtain ⟨g, hg, hl⟩ := f.exists_extension_of_le_seminorm_real S hp
  exact ⟨⟨g, (PolynormableSpace.withSeminorms Real E).continuous_real_rng g
    ⟨{⟨p, hp_cont⟩}, 1, fun x => by simpa using (le_abs_self _).trans (hl x)⟩⟩, hg, hl⟩

中文:
定理 模.对偶.存在_continuous_extension_of_le_seminorm_real
  证明: by
  obtain ⟨g, hg, hl⟩ := f.exists_extension_of_le_seminorm_real S hp
  exact ⟨⟨g, (PolynormableSpace.withSeminorms Real E).continuous_real_rng g
    ⟨{⟨p, hp_cont⟩}, 1, fun x => by simpa using (le_abs_self _).trans (hl x)⟩⟩, hg, hl⟩

Depends on / 依赖: PolynormableSpace, PolynormableSpace.withSeminorms, continuous_real_rng, exists_extension_of_le_seminorm_real, f.exists_extension_of_le_seminorm_real, hp_cont, le_abs_self, withSeminorms
-/
theorem Module.Dual.exists_continuous_extension_of_le_seminorm_real
    [Module Real E] [PolynormableSpace Real E] (S : Subspace Real E) (f : Dual Real S)
    {p : Seminorm Real E} (hp_cont : Continuous p) (hp : forall x, f x <= p x) :
    exists g : StrongDual Real E, (forall x : S, g x = f x) ∧ forall x, |g x| <= p x := by
  obtain ⟨g, hg, hl⟩ := f.exists_extension_of_le_seminorm_real S hp
  exact ⟨⟨g, (PolynormableSpace.withSeminorms Real E).continuous_real_rng g
    ⟨{⟨p, hp_cont⟩}, 1, fun x => by simpa using (le_abs_self _).trans (hl x)⟩⟩, hg, hl⟩

variable [Module 𝕜 E] [PolynormableSpace 𝕜 E]

/--
theorem `Module.Dual.exists_continuous_extension_of_le_seminorm` / 定理 `Module.Dual.exists_continuous_extension_of_le_seminorm`

English:
theorem Module.Dual.exists_continuous_extension_of_le_seminorm
  statement: (S : Submodule 𝕜 E) (f : Dual 𝕜 S)
  proof: by
  obtain ⟨g, hg, hle⟩ := Dual.exists_extension_of_le_seminorm S f hp
  refine ⟨⟨g, (PolynormableSpace.withSeminorms 𝕜 E).continuous_normedSpace_rng 𝕜 g ?_⟩, hg, hle⟩
  exact ⟨{⟨p, hp_cont⟩}, 1, by simpa⟩

中文:
定理 模.对偶.存在_continuous_extension_of_le_seminorm
  结论: (S : 子模 𝕜 E) (f : 对偶 𝕜 S)
  证明: by
  obtain ⟨g, hg, hle⟩ := Dual.exists_extension_of_le_seminorm S f hp
  refine ⟨⟨g, (PolynormableSpace.withSeminorms 𝕜 E).continuous_normedSpace_rng 𝕜 g ?_⟩, hg, hle⟩
  exact ⟨{⟨p, hp_cont⟩}, 1, by simpa⟩

Depends on / 依赖: Dual.exists_extension_of_le_seminorm, PolynormableSpace, PolynormableSpace.withSeminorms, continuous_normedSpace_rng, exists_extension_of_le_seminorm, hp_cont, withSeminorms
-/
theorem Module.Dual.exists_continuous_extension_of_le_seminorm (S : Submodule 𝕜 E) (f : Dual 𝕜 S)
    {p : Seminorm 𝕜 E} (hp_cont : Continuous p) (hp : forall x, ‖f x‖ <= p x) :
    exists g : StrongDual 𝕜 E, (forall x : S, g x = f x) ∧ forall x, ‖g x‖ <= p x := by
  obtain ⟨g, hg, hle⟩ := Dual.exists_extension_of_le_seminorm S f hp
  refine ⟨⟨g, (PolynormableSpace.withSeminorms 𝕜 E).continuous_normedSpace_rng 𝕜 g ?_⟩, hg, hle⟩
  exact ⟨{⟨p, hp_cont⟩}, 1, by simpa⟩

/--
theorem `StrongDual.exists_extension` / 定理 `StrongDual.exists_extension`

English:
theorem StrongDual.exists_extension
  statement: {𝕜} [NontriviallyNormedField 𝕜] [IsRCLikeNormedField 𝕜]
  proof: by
  obtain ⟨q, hq_cont, hq⟩ := Seminorm.exists_le_comp_of_isInducing (f := S.subtype)
    (p := f.toSeminorm) f.continuous.norm IsInducing.subtypeVal
  obtain ⟨g, hg, _⟩ := Dual.exists_continuous_extension_of_le_seminorm S f.toLinearMap hq_cont hq
  exact ⟨g, hg⟩

中文:
定理 StrongDual.存在_extension
  结论: {𝕜} [NontriviallyNormedField 𝕜] [是RCLikeNormedField 𝕜]
  证明: by
  obtain ⟨q, hq_cont, hq⟩ := Seminorm.exists_le_comp_of_isInducing (f := S.subtype)
    (p := f.toSeminorm) f.continuous.norm IsInducing.subtypeVal
  obtain ⟨g, hg, _⟩ := Dual.exists_continuous_extension_of_le_seminorm S f.toLinearMap hq_cont hq
  exact ⟨g, hg⟩

Depends on / 依赖: Dual.exists_continuous_extension_of_le_seminorm, IsInducing, IsInducing.subtypeVal, S.subtype, Seminorm, Seminorm.exists_le_comp_of_isInducing, continuous, exists_continuous_extension_of_le_seminorm, exists_le_comp_of_isInducing, f.continuous.norm, f.toLinearMap, f.toSeminorm, hq_cont, subtype, subtypeVal, toLinearMap, toSeminorm
-/
theorem StrongDual.exists_extension {𝕜} [NontriviallyNormedField 𝕜] [IsRCLikeNormedField 𝕜]
    [Module 𝕜 E] [PolynormableSpace 𝕜 E] (S : Submodule 𝕜 E) (f : StrongDual 𝕜 S) :
    exists g : StrongDual 𝕜 E, forall x : S, g x = f x := by
  obtain ⟨q, hq_cont, hq⟩ := Seminorm.exists_le_comp_of_isInducing (f := S.subtype)
    (p := f.toSeminorm) f.continuous.norm IsInducing.subtypeVal
  obtain ⟨g, hg, _⟩ := Dual.exists_continuous_extension_of_le_seminorm S f.toLinearMap hq_cont hq
  exact ⟨g, hg⟩

variable {F : Type*} [AddCommGroup F] [TopologicalSpace F] [IsTopologicalAddGroup F] [Module 𝕜 F]
  [ContinuousSMul 𝕜 F] [T2Space F]

set_option backward.isDefEq.respectTransparency.types false in
/--
lemma `ContinuousLinearMap.exist_extension_of_finiteDimensional_range` / 引理 `ContinuousLinearMap.exist_extension_of_finiteDimensional_range`

English:
lemma ContinuousLinearMap.exist_extension_of_finiteDimensional_range
  statement: {S : Submodule 𝕜 E}
  proof: by
  let : RCLike 𝕜 := IsRCLikeNormedField.rclike 𝕜
  let b := Module.finBasis 𝕜 f.range
  let e := b.equivFunL
  let fi := fun i => (LinearMap.toContinuousLinearMap (b.coord i)).comp
    (f.codRestrict _ <| LinearMap.mem_range_self _)
  choose gi hgf using fun i => StrongDual.exists_extension S (fi

中文:
引理 连续线性映射.exist_extension_of_finiteDimensional_range
  结论: {S : 子模 𝕜 E}
  证明: by
  let : RCLike 𝕜 := IsRCLikeNormedField.rclike 𝕜
  let b := Module.finBasis 𝕜 f.range
  let e := b.equivFunL
  let fi := fun i => (LinearMap.toContinuousLinearMap (b.coord i)).comp
    (f.codRestrict _ <| LinearMap.mem_range_self _)
  choose gi hgf using fun i => StrongDual.exists_extension S (fi

Depends on / 依赖: IsRCLikeNormedField, IsRCLikeNormedField.rclike, LinearMap, LinearMap.mem_range_self, LinearMap.toContinuousLinearMap, Module, Module.finBasis, RCLike, StrongDual, StrongDual.exists_extension, b.coord, b.equivFunL, codRestrict, e.symm.toContinuousLinearMap.comp, equivFunL, exists_extension, f.codRestrict, f.range, f.range.subtypeL.comp, finBasis
-/
lemma ContinuousLinearMap.exist_extension_of_finiteDimensional_range {S : Submodule 𝕜 E}
    (f : S ->L[𝕜] F) [FiniteDimensional 𝕜 f.range] :
    exists g : E ->L[𝕜] F, f = g.comp S.subtypeL := by
  let : RCLike 𝕜 := IsRCLikeNormedField.rclike 𝕜
  let b := Module.finBasis 𝕜 f.range
  let e := b.equivFunL
  let fi := fun i => (LinearMap.toContinuousLinearMap (b.coord i)).comp
    (f.codRestrict _ <| LinearMap.mem_range_self _)
  choose gi hgf using fun i => StrongDual.exists_extension S (fi i)
use f.range.subtypeL.comp e.symm.toContinuousLinearMap.comp (.pi gi)
  ext x
  simp [fi, e, hgf]

/--
lemma `Submodule.ClosedComplemented.of_finiteDimensional` / 引理 `Submodule.ClosedComplemented.of_finiteDimensional`

English:
lemma Submodule.ClosedComplemented.of_finiteDimensional
  statement: [PolynormableSpace 𝕜 F] (S : Submodule 𝕜 F)
  proof: by
  let ⟨g, hg⟩ := (ContinuousLinearMap.id 𝕜 S).exist_extension_of_finiteDimensional_range
  exact ⟨g, DFunLike.congr_fun hg.symm⟩

中文:
引理 子模.ClosedComplemented.of_finiteDimensional
  结论: [Polynormable空间 𝕜 F] (S : 子模 𝕜 F)
  证明: by
  let ⟨g, hg⟩ := (ContinuousLinearMap.id 𝕜 S).exist_extension_of_finiteDimensional_range
  exact ⟨g, DFunLike.congr_fun hg.symm⟩

Depends on / 依赖: ContinuousLinearMap, ContinuousLinearMap.id, DFunLike, DFunLike.congr_fun, congr_fun, exist_extension_of_finiteDimensional_range, hg.symm
-/
lemma Submodule.ClosedComplemented.of_finiteDimensional [PolynormableSpace 𝕜 F] (S : Submodule 𝕜 F)
    [FiniteDimensional 𝕜 S] : S.ClosedComplemented := by
  let ⟨g, hg⟩ := (ContinuousLinearMap.id 𝕜 S).exist_extension_of_finiteDimensional_range
  exact ⟨g, DFunLike.congr_fun hg.symm⟩
