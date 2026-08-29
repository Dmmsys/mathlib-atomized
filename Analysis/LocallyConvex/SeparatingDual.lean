/-
Copyright (c) 2023 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel, Filippo A. E. Nuccio
-/
module

public import Mathlib.Algebra.Central.Basic
public import Mathlib.Analysis.LocallyConvex.Separation
public import Mathlib.Analysis.LocallyConvex.WithSeminorms
public import Mathlib.LinearAlgebra.Dual.Lemmas
public import Mathlib.Topology.Algebra.Module.Spaces.ContinuousLinearMap

/-!
# Spaces with separating dual

We introduce a typeclass `SeparatingDual R V`, registering that the points of the topological
module `V` over `R` can be separated by continuous linear forms.

This property is satisfied for normed spaces over `ℝ` or `ℂ` (by the analytic Hahn-Banach theorem)
and for locally convex topological spaces over `ℝ` (by the geometric Hahn-Banach theorem).

We show in `SeparatingDual.exists_ne_zero` that given any non-zero vector in an `R`-module `V`
satisfying `SeparatingDual R V`, there exists a continuous linear functional whose value on `v` is
non-zero.

As a consequence of the existence of `SeparatingDual.exists_ne_zero`, a generalization of
Hahn-Banach beyond the normed setting, we show that if `V` and `W` are nontrivial topological vector
spaces over a topological field `R` that acts continuously on `W`, and if `SeparatingDual R V`,
there are nontrivial continuous `R`-linear operators between `V` and `W`. This is recorded in the
instance `SeparatingDual.instNontrivialContinuousLinearMapIdOfContinuousSMul`.

Under the assumption `SeparatingDual R V`, we show in
`SeparatingDual.exists_continuousLinearEquiv_apply_eq` that the group of continuous linear
equivalences acts transitively on the set of nonzero vectors.
-/

public section
/-- When `E` is a topological module over a topological ring `R`, the class `SeparatingDual R E`
registers that continuous linear forms on `E` separate points of `E`. -/
@[mk_iff separatingDual_def]
/--
Definition of `SeparatingDual` / `SeparatingDual` 的定义

English:
class SeparatingDual
  parameters: (R V : Type*) [Ring R] [AddCommGroup V] [TopologicalSpace V]
  axioms and operations (1):
    - exists_ne_zero' : forall (x : V), x != 0 -> exists f : StrongDual R V, f x != 0

中文:
类 SeparatingDual
  参数: (R V : 类型) [环 R] [加法交换群 V] [拓扑空间 V]
  公理与运算 (1 个):
    - exists_ne_zero' : 对任意 (x : V), x != 0 -> 存在 f : StrongDual R V, f x != 0
-/
class SeparatingDual (R V : Type*) [Ring R] [AddCommGroup V] [TopologicalSpace V]
    [TopologicalSpace R] [Module R V] : Prop where
  /-- Any nonzero vector can be mapped by a continuous linear map to a nonzero scalar. -/
  exists_ne_zero' : forall (x : V), x != 0 -> exists f : StrongDual R V, f x != 0

instance {E : Type*} [TopologicalSpace E] [AddCommGroup E] [IsTopologicalAddGroup E]
    [Module Real E] [ContinuousSMul Real E] [LocallyConvexSpace Real E] [T1Space E] : SeparatingDual Real E :=
  ⟨fun x hx => by
    rcases geometric_hahn_banach_point_point hx.symm with ⟨f, hf⟩
    simp only [map_zero] at hf
    exact ⟨f, hf.ne'⟩⟩

instance {E 𝕜 : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E] : SeparatingDual 𝕜 E :=
  ⟨fun x hx =>
    let : NormedSpace Real E := .restrictScalars Real 𝕜 E
    let : Module Real E := .restrictScalars Real 𝕜 E
    have : IsScalarTower Real 𝕜 E := .restrictScalars Real 𝕜 E
    have : LocallyConvexSpace Real E := NormedSpace.toLocallyConvexSpace' 𝕜
.imp fun f hf hf' => by simp [hf'] at hf⟩ RCLike.geometric_hahn_banach_point_point hx

namespace SeparatingDual

section Ring

variable {R V : Type*} [Ring R] [AddCommGroup V] [TopologicalSpace V]
  [TopologicalSpace R] [Module R V] [SeparatingDual R V]

/--
lemma `exists_ne_zero` / 引理 `exists_ne_zero`

English:
lemma exists_ne_zero
  given: {x : V} (hx : x != 0)
  proof: exists_ne_zero' x hx

中文:
引理 存在_ne_zero
  条件: {x : V} (hx : x != 0)
  证明: exists_ne_zero' x hx

Depends on / 依赖: exists_ne_zero
-/
lemma exists_ne_zero {x : V} (hx : x != 0) :
    exists f : StrongDual R V, f x != 0 :=
  exists_ne_zero' x hx

/--
theorem `exists_separating_of_ne` / 定理 `exists_separating_of_ne`

English:
theorem exists_separating_of_ne
  given: {x y : V} (h : x != y)
  proof: by
  rcases exists_ne_zero (R := R) (sub_ne_zero_of_ne h) with ⟨f, hf⟩
  exact ⟨f, by simpa [sub_ne_zero] using hf⟩

中文:
定理 存在_separating_of_ne
  条件: {x y : V} (h : x != y)
  证明: by
  rcases exists_ne_zero (R := R) (sub_ne_zero_of_ne h) with ⟨f, hf⟩
  exact ⟨f, by simpa [sub_ne_zero] using hf⟩

Depends on / 依赖: exists_ne_zero, sub_ne_zero, sub_ne_zero_of_ne
-/
theorem exists_separating_of_ne {x y : V} (h : x != y) :
    exists f : StrongDual R V, f x != f y := by
  rcases exists_ne_zero (R := R) (sub_ne_zero_of_ne h) with ⟨f, hf⟩
  exact ⟨f, by simpa [sub_ne_zero] using hf⟩

/--
theorem `t1Space` / 定理 `t1Space`

English:
theorem t1Space
  given: [T1Space R]
  statement: T1Space V
  proof: by
  apply t1Space_iff_exists_open.2 (fun x y hxy => ?_)
  rcases exists_separating_of_ne (R := R) hxy with ⟨f, hf⟩
  exact ⟨f ⁻¹' {f y}ᶜ, isOpen_compl_singleton.preimage f.continuous, hf, by simp⟩

中文:
定理 t1Space
  条件: [T1空间 R]
  结论: T1空间 V
  证明: by
  apply t1Space_iff_exists_open.2 (fun x y hxy => ?_)
  rcases exists_separating_of_ne (R := R) hxy with ⟨f, hf⟩
  exact ⟨f ⁻¹' {f y}ᶜ, isOpen_compl_singleton.preimage f.continuous, hf, by simp⟩
-/
protected theorem t1Space [T1Space R] : T1Space V := by
  apply t1Space_iff_exists_open.2 (fun x y hxy => ?_)
  rcases exists_separating_of_ne (R := R) hxy with ⟨f, hf⟩
  exact ⟨f ⁻¹' {f y}ᶜ, isOpen_compl_singleton.preimage f.continuous, hf, by simp⟩

/--
theorem `t2Space` / 定理 `t2Space`

English:
theorem t2Space
  given: [T2Space R]
  statement: T2Space V
  proof: by
  apply (t2Space_iff _).2 (fun {x} {y} hxy => ?_)
  rcases exists_separating_of_ne (R := R) hxy with ⟨f, hf⟩
  exact separated_by_continuous f.continuous hf

中文:
定理 t2Space
  条件: [T2空间 R]
  结论: T2空间 V
  证明: by
  apply (t2Space_iff _).2 (fun {x} {y} hxy => ?_)
  rcases exists_separating_of_ne (R := R) hxy with ⟨f, hf⟩
  exact separated_by_continuous f.continuous hf
-/
protected theorem t2Space [T2Space R] : T2Space V := by
  apply (t2Space_iff _).2 (fun {x} {y} hxy => ?_)
  rcases exists_separating_of_ne (R := R) hxy with ⟨f, hf⟩
  exact separated_by_continuous f.continuous hf

/--
theorem `eq_zero_of_forall_dual_eq_zero` / 定理 `eq_zero_of_forall_dual_eq_zero`

English:
theorem eq_zero_of_forall_dual_eq_zero
  given: {x : V} (h : forall f : StrongDual R V, f x = 0)
  statement: x = 0
  proof: by
  by_contra hx
  rcases exists_ne_zero (R := R) hx with ⟨f, hf⟩
  exact hf (h f)

中文:
定理 eq_zero_of_对任意_dual_eq_zero
  条件: {x : V} (h : 对任意 f : StrongDual R V, f x = 0)
  结论: x = 0
  证明: by
  by_contra hx
  rcases exists_ne_zero (R := R) hx with ⟨f, hf⟩
  exact hf (h f)

Depends on / 依赖: exists_ne_zero
-/
theorem eq_zero_of_forall_dual_eq_zero {x : V} (h : forall f : StrongDual R V, f x = 0) : x = 0 := by
  by_contra hx
  rcases exists_ne_zero (R := R) hx with ⟨f, hf⟩
  exact hf (h f)

/--
theorem `eq_zero_iff_forall_dual_eq_zero` / 定理 `eq_zero_iff_forall_dual_eq_zero`

English:
theorem eq_zero_iff_forall_dual_eq_zero
  given: (x : V)
  statement: x = 0 ↔ forall g : StrongDual R V, g x = 0
  proof: ⟨by simp +contextual, fun h => eq_zero_of_forall_dual_eq_zero (R := R) h⟩

中文:
定理 eq_zero_iff_对任意_dual_eq_zero
  条件: (x : V)
  结论: x = 0 ↔ 对任意 g : StrongDual R V, g x = 0
  证明: ⟨by simp +contextual, fun h => eq_zero_of_forall_dual_eq_zero (R := R) h⟩

Depends on / 依赖: contextual, eq_zero_of_forall_dual_eq_zero
-/
theorem eq_zero_iff_forall_dual_eq_zero (x : V) : x = 0 ↔ forall g : StrongDual R V, g x = 0 :=
  ⟨by simp +contextual, fun h => eq_zero_of_forall_dual_eq_zero (R := R) h⟩

/--
theorem `eq_iff_forall_dual_eq` / 定理 `eq_iff_forall_dual_eq`

English:
theorem eq_iff_forall_dual_eq
  given: {x y : V}
  statement: x = y ↔ forall g : StrongDual R V, g x = g y
  proof: by
  rw [← sub_eq_zero]; rw [eq_zero_iff_forall_dual_eq_zero (R := R) (x - y)]
  simp [sub_eq_zero]

中文:
定理 eq_iff_对任意_dual_eq
  条件: {x y : V}
  结论: x = y ↔ 对任意 g : StrongDual R V, g x = g y
  证明: by
  rw [← sub_eq_zero]; rw [eq_zero_iff_forall_dual_eq_zero (R := R) (x - y)]
  simp [sub_eq_zero]

Depends on / 依赖: eq_zero_iff_forall_dual_eq_zero, sub_eq_zero
-/
theorem eq_iff_forall_dual_eq {x y : V} : x = y ↔ forall g : StrongDual R V, g x = g y := by
  rw [← sub_eq_zero]; rw [eq_zero_iff_forall_dual_eq_zero (R := R) (x - y)]
  simp [sub_eq_zero]

end Ring

section Field

variable {R V : Type*} [Field R] [AddCommGroup V] [TopologicalSpace R] [TopologicalSpace V]
  [IsTopologicalRing R] [Module R V]

-- TODO (@alreadydone): this could generalize to CommRing R if we were to add a section
/--
theorem `_root_.separatingDual_iff_injective` / 定理 `_root_.separatingDual_iff_injective`

English:
theorem _root_.separatingDual_iff_injective
  statement: SeparatingDual R V ↔
  proof: by
  simp_rw [separatingDual_def, Ne, injective_iff_map_eq_zero]
  congrm forall v, ?_
  rw [not_imp_comm]; rw [LinearMap.ext_iff]
  push Not; rfl

中文:
定理 _root_.separatingDual_iff_injective
  结论: SeparatingDual R V ↔
  证明: by
  simp_rw [separatingDual_def, Ne, injective_iff_map_eq_zero]
  congrm forall v, ?_
  rw [not_imp_comm]; rw [LinearMap.ext_iff]
  push Not; rfl

Depends on / 依赖: LinearMap, LinearMap.ext_iff, congrm, ext_iff, injective_iff_map_eq_zero, not_imp_comm, separatingDual_def, simp_rw
-/
theorem _root_.separatingDual_iff_injective : SeparatingDual R V ↔
    Function.Injective (ContinuousLinearMap.coeLM (R := R) R (M := V) (N₃ := R)).flip := by
  simp_rw [separatingDual_def, Ne, injective_iff_map_eq_zero]
  congrm forall v, ?_
  rw [not_imp_comm]; rw [LinearMap.ext_iff]
  push Not; rfl

variable [SeparatingDual R V]

open Function

/--
theorem `dualMap_surjective_iff` / 定理 `dualMap_surjective_iff`

English:
theorem dualMap_surjective_iff
  statement: {W} [AddCommGroup W] [Module R W] [FiniteDimensional R W]
  proof: by
  constructor <;> intro hf
  · exact LinearMap.dualMap_surjective_iff.mp hf.of_comp
  have := (separatingDual_iff_injective.mp ‹_›).comp hf
  rw [← LinearMap.coe_comp] at this
  exact LinearMap.flip_surjective_iff₁.mpr this

中文:
定理 dualMap_surjective_iff
  结论: {W} [加法交换群 W] [模 R W] [有限维 R W]
  证明: by
  constructor <;> intro hf
  · exact LinearMap.dualMap_surjective_iff.mp hf.of_comp
  have := (separatingDual_iff_injective.mp ‹_›).comp hf
  rw [← LinearMap.coe_comp] at this
  exact LinearMap.flip_surjective_iff₁.mpr this

Depends on / 依赖: LinearMap, LinearMap.coe_comp, LinearMap.dualMap_surjective_iff.mp, LinearMap.flip_surjective_iff, coe_comp, dualMap_surjective_iff, hf.of_comp, of_comp, separatingDual_iff_injective, separatingDual_iff_injective.mp
-/
theorem dualMap_surjective_iff {W} [AddCommGroup W] [Module R W] [FiniteDimensional R W]
    {f : W ->ₗ[R] V} : Surjective (f.dualMap ∘ ContinuousLinearMap.toLinearMap) ↔ Injective f := by
  constructor <;> intro hf
  · exact LinearMap.dualMap_surjective_iff.mp hf.of_comp
  have := (separatingDual_iff_injective.mp ‹_›).comp hf
  rw [← LinearMap.coe_comp] at this
  exact LinearMap.flip_surjective_iff₁.mpr this

variable (V) in
open ContinuousLinearMap in
/- As a consequence of the existence of non-zero linear maps, itself a consequence of Hahn-Banach
in the normed setting, we show that if `V` and `W` are nontrivial topological vector spaces over a
topological field `R` that acts continuously on `W`, and if `SeparatingDual R V`, there are
nontrivial continuous `R`-linear operators between `V` and `W`. -/
instance (W) [AddCommGroup W] [TopologicalSpace W] [Module R W] [Nontrivial W]
    [ContinuousSMul R W] [Nontrivial V] : Nontrivial (V ->L[R] W) := by
  obtain ⟨v, hv⟩ := exists_ne (0 : V)
  obtain ⟨w, hw⟩ := exists_ne (0 : W)
  obtain ⟨ψ, hψ⟩ := exists_ne_zero (R := R) hv
  exact ⟨ψ.smulRight w, 0, DFunLike.ne_iff.mpr ⟨v, by simp_all⟩⟩

/--
lemma `exists_eq_one` / 引理 `exists_eq_one`

English:
lemma exists_eq_one
  given: {x : V} (hx : x != 0)
  proof: by
  rcases exists_ne_zero (R := R) hx with ⟨f, hf⟩
  exact ⟨(f x)⁻¹ • f, inv_mul_cancel₀ hf⟩

中文:
引理 存在_eq_one
  条件: {x : V} (hx : x != 0)
  证明: by
  rcases exists_ne_zero (R := R) hx with ⟨f, hf⟩
  exact ⟨(f x)⁻¹ • f, inv_mul_cancel₀ hf⟩

Depends on / 依赖: exists_ne_zero
-/
lemma exists_eq_one {x : V} (hx : x != 0) :
    exists f : StrongDual R V, f x = 1 := by
  rcases exists_ne_zero (R := R) hx with ⟨f, hf⟩
  exact ⟨(f x)⁻¹ • f, inv_mul_cancel₀ hf⟩

/--
theorem `exists_eq_one_ne_zero_of_ne_zero_pair` / 定理 `exists_eq_one_ne_zero_of_ne_zero_pair`

English:
theorem exists_eq_one_ne_zero_of_ne_zero_pair
  given: {x y : V} (hx : x != 0) (hy : y != 0)
  proof: by
  obtain ⟨u, ux⟩ : exists u : StrongDual R V, u x = 1 := exists_eq_one hx
  rcases ne_or_eq (u y) 0 with uy | uy
  · exact ⟨u, ux, uy⟩
  obtain ⟨v, vy⟩ : exists v : StrongDual R V, v y = 1 := exists_eq_one hy
  rcases ne_or_eq (v x) 0 with vx | vx
  · exact ⟨(v x)⁻¹ • v, inv_mul_cancel₀ vx, show (v x)⁻¹ * v y != 0 by simp [vx, vy]⟩
  · exact ⟨u + v, by simp [ux, vx], by simp [uy, vy]⟩

中文:
定理 存在_eq_one_ne_zero_of_ne_zero_pair
  条件: {x y : V} (hx : x != 0) (hy : y != 0)
  证明: by
  obtain ⟨u, ux⟩ : exists u : StrongDual R V, u x = 1 := exists_eq_one hx
  rcases ne_or_eq (u y) 0 with uy | uy
  · exact ⟨u, ux, uy⟩
  obtain ⟨v, vy⟩ : exists v : StrongDual R V, v y = 1 := exists_eq_one hy
  rcases ne_or_eq (v x) 0 with vx | vx
  · exact ⟨(v x)⁻¹ • v, inv_mul_cancel₀ vx, show (v x)⁻¹ * v y != 0 by simp [vx, vy]⟩
  · exact ⟨u + v, by simp [ux, vx], by simp [uy, vy]⟩

Depends on / 依赖: StrongDual, exists_eq_one, ne_or_eq
-/
theorem exists_eq_one_ne_zero_of_ne_zero_pair {x y : V} (hx : x != 0) (hy : y != 0) :
    exists f : StrongDual R V, f x = 1 ∧ f y != 0 := by
  obtain ⟨u, ux⟩ : exists u : StrongDual R V, u x = 1 := exists_eq_one hx
  rcases ne_or_eq (u y) 0 with uy | uy
  · exact ⟨u, ux, uy⟩
  obtain ⟨v, vy⟩ : exists v : StrongDual R V, v y = 1 := exists_eq_one hy
  rcases ne_or_eq (v x) 0 with vx | vx
  · exact ⟨(v x)⁻¹ • v, inv_mul_cancel₀ vx, show (v x)⁻¹ * v y != 0 by simp [vx, vy]⟩
  · exact ⟨u + v, by simp [ux, vx], by simp [uy, vy]⟩

variable [IsTopologicalAddGroup V] [ContinuousSMul R V]

section algebra
variable {S : Type*} [CommSemiring S] [Module S V] [SMulCommClass R S V] [Algebra S R]
  [IsScalarTower S R V] [ContinuousConstSMul S V]

/--
Instance `_root_.Algebra.IsCentral.instContinuousLinearMap` / 实例 `_root_.Algebra.IsCentral.instContinuousLinearMap`

English:
instance _root_.Algebra.IsCentral.instContinuousLinearMap
  signature: [Algebra.IsCentral S R]
  body: by
    suffices exists α in Subalgebra.center S R, f = α • .id R V from
      have ⟨_, ⟨y, _⟩, _⟩ := Algebra.IsCentral.center_eq_bot S R ▸ this
      ⟨y, by aesop⟩
    nontriviality V
    obtain ⟨x, hx⟩ := exists_ne (0 : V)
    obtain ⟨g, hg⟩ := exists_eq_one (R := R) hx
    have (y : V) := by simpa [hg] using congr($(Subalgebra.mem_center_iff.mp hf (g.smulRight y)) x)
    exact ⟨g (f x), by simp [this, ContinuousLinearMap.ext_iff]⟩

中文:
实例 _root_.代数.是中心.instContinuousLinearMap
  签名: [代数.是中心 S R]
  定义体: by
    suffices exists α in Subalgebra.center S R, f = α • .id R V from
      have ⟨_, ⟨y, _⟩, _⟩ := Algebra.IsCentral.center_eq_bot S R ▸ this
      ⟨y, by aesop⟩
    nontriviality V
    obtain ⟨x, hx⟩ := exists_ne (0 : V)
    obtain ⟨g, hg⟩ := exists_eq_one (R := R) hx
    have (y : V) := by simpa [hg] using congr($(Subalgebra.mem_center_iff.mp hf (g.smulRight y)) x)
    exact ⟨g (f x), by simp [this, ContinuousLinearMap.ext_iff]⟩

Depends on / 依赖: Algebra, Algebra.IsCentral.center_eq_bot, ContinuousLinearMap, ContinuousLinearMap.ext_iff, IsCentral, Subalgebra, Subalgebra.center, Subalgebra.mem_center_iff.mp, center, center_eq_bot, exists_eq_one, exists_ne, ext_iff, g.smulRight, mem_center_iff, nontriviality, smulRight
-/
instance _root_.Algebra.IsCentral.instContinuousLinearMap [Algebra.IsCentral S R] :
    Algebra.IsCentral S (V ->L[R] V) where
  out f hf := by
    suffices exists α in Subalgebra.center S R, f = α • .id R V from
      have ⟨_, ⟨y, _⟩, _⟩ := Algebra.IsCentral.center_eq_bot S R ▸ this
      ⟨y, by aesop⟩
    nontriviality V
    obtain ⟨x, hx⟩ := exists_ne (0 : V)
    obtain ⟨g, hg⟩ := exists_eq_one (R := R) hx
    have (y : V) := by simpa [hg] using congr($(Subalgebra.mem_center_iff.mp hf (g.smulRight y)) x)
    exact ⟨g (f x), by simp [this, ContinuousLinearMap.ext_iff]⟩

open ContinuousLinearMap ContinuousLinearEquiv in
/--
theorem `_root_.ContinuousLinearEquiv.conjContinuousAlgEquiv_ext_iff` / 定理 `_root_.ContinuousLinearEquiv.conjContinuousAlgEquiv_ext_iff`

English:
theorem _root_.ContinuousLinearEquiv.conjContinuousAlgEquiv_ext_iff
  proof: by
  conv_lhs => rw [eq_comm]
  simp_rw [ContinuousAlgEquiv.ext_iff, funext_iff, conjContinuousAlgEquiv_apply,
    ← eq_toContinuousLinearMap_symm_comp, ← ContinuousLinearMap.comp_assoc,
    eq_comp_toContinuousLinearMap_symm, ContinuousLinearMap.comp_assoc,
    ← ContinuousLinearMap.comp_assoc _ f.toContinuousLinearMap, comp_coe, ← mul_def,
    ← Subalgebra.mem_center_iff (R := R), Algebra.IsCentral.center_eq_bot, ← comp_coe,
    Algebra.mem_bot, Set.mem_range, Algebra.algebraMap_eq_smul_one, ContinuousLinearEquiv.ext_iff]
  refine ⟨fun ⟨y, h⟩ => ?_, fun ⟨y, h⟩ => ⟨(y : R), by ext; simp [h]⟩⟩
  if hy : y = 0 then exact ⟨1, funext fun x => by simp [by simpa [hy] using congr($h x).symm]⟩
  else exact ⟨.mk0 y hy, funext fun x => by simp [by simpa [eq_symm_apply] using congr($h x)]⟩

中文:
定理 _root_.连续线性等价.conjContinuousAlgEquiv_ext_iff
  证明: by
  conv_lhs => rw [eq_comm]
  simp_rw [ContinuousAlgEquiv.ext_iff, funext_iff, conjContinuousAlgEquiv_apply,
    ← eq_toContinuousLinearMap_symm_comp, ← ContinuousLinearMap.comp_assoc,
    eq_comp_toContinuousLinearMap_symm, ContinuousLinearMap.comp_assoc,
    ← ContinuousLinearMap.comp_assoc _ f.toContinuousLinearMap, comp_coe, ← mul_def,
    ← Subalgebra.mem_center_iff (R := R), Algebra.IsCentral.center_eq_bot, ← comp_coe,
    Algebra.mem_bot, Set.mem_range, Algebra.algebraMap_eq_smul_one, ContinuousLinearEquiv.ext_iff]
  refine ⟨fun ⟨y, h⟩ => ?_, fun ⟨y, h⟩ => ⟨(y : R), by ext; simp [h]⟩⟩
  if hy : y = 0 then exact ⟨1, funext fun x => by simp [by simpa [hy] using congr($h x).symm]⟩
  else exact ⟨.mk0 y hy, funext fun x => by simp [by simpa [eq_symm_apply] using congr($h x)]⟩

Depends on / 依赖: Algebra, Algebra.IsCentral.center_eq_bot, Algebra.algebraMap_eq_smul_one, Algebra.mem_bot, ContinuousAlgEquiv, ContinuousAlgEquiv.ext_iff, ContinuousLinearEquiv, ContinuousLinearEquiv.ext, ContinuousLinearMap, ContinuousLinearMap.comp_assoc, IsCentral, Set.mem_range, Subalgebra, Subalgebra.mem_center_iff, algebraMap_eq_smul_one, center_eq_bot, comp_assoc, comp_coe, conjContinuousAlgEquiv_apply, conv_lhs
-/
theorem _root_.ContinuousLinearEquiv.conjContinuousAlgEquiv_ext_iff
    {R V W : Type*} [NormedField R] [AddCommGroup V] [AddCommGroup W] [TopologicalSpace R]
    [TopologicalSpace V] [TopologicalSpace W] [IsTopologicalRing R] [Module R V] [Module R W]
    [SeparatingDual R V] [IsTopologicalAddGroup V] [IsTopologicalAddGroup W]
    [ContinuousSMul R V] [ContinuousSMul R W] (f g : V ≃L[R] W) :
    f.conjContinuousAlgEquiv = g.conjContinuousAlgEquiv ↔ exists α : Rˣ, f = α • g := by
  conv_lhs => rw [eq_comm]
  simp_rw [ContinuousAlgEquiv.ext_iff, funext_iff, conjContinuousAlgEquiv_apply,
    ← eq_toContinuousLinearMap_symm_comp, ← ContinuousLinearMap.comp_assoc,
    eq_comp_toContinuousLinearMap_symm, ContinuousLinearMap.comp_assoc,
    ← ContinuousLinearMap.comp_assoc _ f.toContinuousLinearMap, comp_coe, ← mul_def,
    ← Subalgebra.mem_center_iff (R := R), Algebra.IsCentral.center_eq_bot, ← comp_coe,
    Algebra.mem_bot, Set.mem_range, Algebra.algebraMap_eq_smul_one, ContinuousLinearEquiv.ext_iff]
  refine ⟨fun ⟨y, h⟩ => ?_, fun ⟨y, h⟩ => ⟨(y : R), by ext; simp [h]⟩⟩
  if hy : y = 0 then exact ⟨1, funext fun x => by simp [by simpa [hy] using congr($h x).symm]⟩
  else exact ⟨.mk0 y hy, funext fun x => by simp [by simpa [eq_symm_apply] using congr($h x)]⟩

end algebra

/--
theorem `exists_continuousLinearEquiv_apply_eq` / 定理 `exists_continuousLinearEquiv_apply_eq`

English:
theorem exists_continuousLinearEquiv_apply_eq
  proof: by
  obtain ⟨G, Gx, Gy⟩ : exists G : StrongDual R V, G x = 1 ∧ G y != 0 :=
    exists_eq_one_ne_zero_of_ne_zero_pair hx hy
  let A : V ≃L[R] V :=
  { toFun := fun z => z + G z • (y - x)
    invFun := fun z => z + ((G y)⁻¹ * G z) • (x - y)
    map_add' := fun a b => by simp [add_smul]; abel
    map_smul' := by simp [smul_smul]
    left_inv := fun z => by
      simp only [RingHom.id_apply, smul_eq_mul,
        -- Note: https://github.com/leanprover-community/mathlib4/pull/8386 had to change `map_smulₛₗ` into `map_smulₛₗ _`
        map_add, map_smulₛₗ _, map_sub, Gx, mul_sub, mul_one, add_sub_cancel]
      rw [mul_comm (G z)]; rw [← mul_assoc]; rw [inv_mul_cancel₀ Gy]
      simp only [smul_sub, one_mul]
      abel
    right_inv := fun z => by
        -- Note: https://github.com/leanprover-community/mathlib4/pull/8386 had to change `map_smulₛₗ` into `map_smulₛₗ _`
      simp only [map_add, map_smulₛₗ _, map_mul, map_inv₀, RingHom.id_apply, map_sub, Gx,
        smul_eq_mul, mul_sub, mul_one]
      rw [mul_comm _ (G y)]; rw [← mul_assoc]; rw [mul_inv_cancel₀ Gy]
      simp only [smul_sub, one_mul, add_sub_cancel]
      abel }
  exact ⟨A, show x + G x • (y - x) = y by simp [Gx]⟩

中文:
定理 存在_continuousLinearEquiv_apply_eq
  证明: by
  obtain ⟨G, Gx, Gy⟩ : exists G : StrongDual R V, G x = 1 ∧ G y != 0 :=
    exists_eq_one_ne_zero_of_ne_zero_pair hx hy
  let A : V ≃L[R] V :=
  { toFun := fun z => z + G z • (y - x)
    invFun := fun z => z + ((G y)⁻¹ * G z) • (x - y)
    map_add' := fun a b => by simp [add_smul]; abel
    map_smul' := by simp [smul_smul]
    left_inv := fun z => by
      simp only [RingHom.id_apply, smul_eq_mul,
        -- Note: https://github.com/leanprover-community/mathlib4/pull/8386 had to change `map_smulₛₗ` into `map_smulₛₗ _`
        map_add, map_smulₛₗ _, map_sub, Gx, mul_sub, mul_one, add_sub_cancel]
      rw [mul_comm (G z)]; rw [← mul_assoc]; rw [inv_mul_cancel₀ Gy]
      simp only [smul_sub, one_mul]
      abel
    right_inv := fun z => by
        -- Note: https://github.com/leanprover-community/mathlib4/pull/8386 had to change `map_smulₛₗ` into `map_smulₛₗ _`
      simp only [map_add, map_smulₛₗ _, map_mul, map_inv₀, RingHom.id_apply, map_sub, Gx,
        smul_eq_mul, mul_sub, mul_one]
      rw [mul_comm _ (G y)]; rw [← mul_assoc]; rw [mul_inv_cancel₀ Gy]
      simp only [smul_sub, one_mul, add_sub_cancel]
      abel }
  exact ⟨A, show x + G x • (y - x) = y by simp [Gx]⟩

Depends on / 依赖: RingHom, RingHom.id_apply, StrongDual, add_smul, exists_eq_one_ne_zero_of_ne_zero_pair, id_apply, invFun, left_inv, map_add, map_smul, smul_eq_mul, smul_smul
-/
theorem exists_continuousLinearEquiv_apply_eq
    {x y : V} (hx : x != 0) (hy : y != 0) :
    exists A : V ≃L[R] V, A x = y := by
  obtain ⟨G, Gx, Gy⟩ : exists G : StrongDual R V, G x = 1 ∧ G y != 0 :=
    exists_eq_one_ne_zero_of_ne_zero_pair hx hy
  let A : V ≃L[R] V :=
  { toFun := fun z => z + G z • (y - x)
    invFun := fun z => z + ((G y)⁻¹ * G z) • (x - y)
    map_add' := fun a b => by simp [add_smul]; abel
    map_smul' := by simp [smul_smul]
    left_inv := fun z => by
      simp only [RingHom.id_apply, smul_eq_mul,
        -- Note: https://github.com/leanprover-community/mathlib4/pull/8386 had to change `map_smulₛₗ` into `map_smulₛₗ _`
        map_add, map_smulₛₗ _, map_sub, Gx, mul_sub, mul_one, add_sub_cancel]
      rw [mul_comm (G z)]; rw [← mul_assoc]; rw [inv_mul_cancel₀ Gy]
      simp only [smul_sub, one_mul]
      abel
    right_inv := fun z => by
        -- Note: https://github.com/leanprover-community/mathlib4/pull/8386 had to change `map_smulₛₗ` into `map_smulₛₗ _`
      simp only [map_add, map_smulₛₗ _, map_mul, map_inv₀, RingHom.id_apply, map_sub, Gx,
        smul_eq_mul, mul_sub, mul_one]
      rw [mul_comm _ (G y)]; rw [← mul_assoc]; rw [mul_inv_cancel₀ Gy]
      simp only [smul_sub, one_mul, add_sub_cancel]
      abel }
  exact ⟨A, show x + G x • (y - x) = y by simp [Gx]⟩

end Field

end SeparatingDual
