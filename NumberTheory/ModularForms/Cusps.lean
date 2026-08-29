/-
Copyright (c) 2025 David Loeffler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Loeffler
-/
module

public import Mathlib.Algebra.EuclideanDomain.Int
public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.NumberTheory.ModularForms.CongruenceSubgroups
public import Mathlib.RingTheory.Localization.NumDen
public import Mathlib.Topology.Algebra.Order.ArchimedeanDiscrete
public import Mathlib.Topology.Compactification.OnePoint.ProjectiveLine

/-!
# Cusps

We define the cusps of a subgroup of `GL(2, ℝ)` as the fixed points of parabolic elements.
-/

@[expose] public section

open Matrix SpecialLinearGroup GeneralLinearGroup Filter Polynomial OnePoint

open scoped MatrixGroups LinearAlgebra.Projectivization

namespace OnePoint

variable {K : Type*} [Field K] [DecidableEq K]

/--
lemma `exists_mem_SL2` / 引理 `exists_mem_SL2`

English:
lemma exists_mem_SL2
  statement: (A : Type*) [CommRing A] [IsDomain A] [Algebra A K] [IsFractionRing A K]
  proof: by
  cases c with
  | infty => exact ⟨1, by simp⟩
  | coe q =>
    obtain ⟨g, hg0, hg1⟩ := (IsFractionRing.num_den_reduced A q).isCoprime.exists_SL2_col 0
    exact ⟨g, by simp [hg0, hg1, smul_infty_eq_ite]⟩

中文:
引理 存在_mem_SL2
  结论: (A : 类型) [交换环 A] [是整环 A] [代数 A K] [IsFractionRing A K]
  证明: by
  cases c with
  | infty => exact ⟨1, by simp⟩
  | coe q =>
    obtain ⟨g, hg0, hg1⟩ := (IsFractionRing.num_den_reduced A q).isCoprime.exists_SL2_col 0
    exact ⟨g, by simp [hg0, hg1, smul_infty_eq_ite]⟩

Depends on / 依赖: IsFractionRing, IsFractionRing.num_den_reduced, exists_SL2_col, isCoprime, isCoprime.exists_SL2_col, num_den_reduced, smul_infty_eq_ite
-/
lemma exists_mem_SL2 (A : Type*) [CommRing A] [IsDomain A] [Algebra A K] [IsFractionRing A K]
    [IsPrincipalIdealRing A] (c : OnePoint K) :
    exists g : SL(2, A), (mapGL K g) • ∞ = c := by
  cases c with
  | infty => exact ⟨1, by simp⟩
  | coe q =>
    obtain ⟨g, hg0, hg1⟩ := (IsFractionRing.num_den_reduced A q).isCoprime.exists_SL2_col 0
    exact ⟨g, by simp [hg0, hg1, smul_infty_eq_ite]⟩

end OnePoint

namespace Subgroup.HasDetPlusMinusOne

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
  {𝒢 : Subgroup (GL (Fin 2) K)} [𝒢.HasDetPlusMinusOne]

/--
lemma `isParabolic_iff_of_upperTriangular` / 引理 `isParabolic_iff_of_upperTriangular`

English:
lemma isParabolic_iff_of_upperTriangular
  given: {g} (hg : g in 𝒢) (hg10 : g 1 0 = 0)
  proof: isParabolic_iff_of_upperTriangular_of_det (HasDetPlusMinusOne.det_eq hg) hg10

中文:
引理 isParabolic_iff_of_upperTriangular
  条件: {g} (hg : g in 𝒢) (hg10 : g 1 0 = 0)
  证明: isParabolic_iff_of_upperTriangular_of_det (HasDetPlusMinusOne.det_eq hg) hg10

Depends on / 依赖: HasDetPlusMinusOne, HasDetPlusMinusOne.det_eq, det_eq, isParabolic_iff_of_upperTriangular_of_det
-/
lemma isParabolic_iff_of_upperTriangular {g} (hg : g in 𝒢) (hg10 : g 1 0 = 0) :
    g.IsParabolic ↔ (exists x != 0, g = upperRightHom x) ∨ (exists x != (0 : K), g = -upperRightHom x) :=
  isParabolic_iff_of_upperTriangular_of_det (HasDetPlusMinusOne.det_eq hg) hg10

end Subgroup.HasDetPlusMinusOne

section IsCusp

/--
Definition of `IsCusp` / `IsCusp` 的定义

English:
definition IsCusp
  signature: (c : OnePoint Real) (𝒢 : Subgroup (GL (Fin 2) Real))
  body: exists g in 𝒢, g.IsParabolic ∧ g • c = c

中文:
定义 IsCusp
  签名: (c : OnePoint 实数) (𝒢 : 子群 (GL (有限集 2) 实数))
  定义体: exists g in 𝒢, g.IsParabolic ∧ g • c = c

Depends on / 依赖: IsParabolic, g.IsParabolic
-/
def IsCusp (c : OnePoint Real) (𝒢 : Subgroup (GL (Fin 2) Real)) : Prop :=
  exists g in 𝒢, g.IsParabolic ∧ g • c = c

open scoped Pointwise in
/--
lemma `IsCusp.smul` / 引理 `IsCusp.smul`

English:
lemma IsCusp.smul
  statement: {c : OnePoint Real} {𝒢 : Subgroup (GL (Fin 2) Real)} (hc : IsCusp c 𝒢)
  proof: by
  obtain ⟨p, hp𝒢, hpp, hpc⟩ := hc
  refine ⟨_, 𝒢.smul_mem_pointwise_smul _ _ hp𝒢, ?_, ?_⟩
  · simpa [ConjAct.toConjAct_smul] using hpp
  · simp [ConjAct.toConjAct_smul, mul_smul, hpc]

中文:
引理 IsCusp.smul
  结论: {c : OnePoint 实数} {𝒢 : 子群 (GL (有限集 2) 实数)} (hc : IsCusp c 𝒢)
  证明: by
  obtain ⟨p, hp𝒢, hpp, hpc⟩ := hc
  refine ⟨_, 𝒢.smul_mem_pointwise_smul _ _ hp𝒢, ?_, ?_⟩
  · simpa [ConjAct.toConjAct_smul] using hpp
  · simp [ConjAct.toConjAct_smul, mul_smul, hpc]

Depends on / 依赖: ConjAct, ConjAct.toConjAct_smul, mul_smul, smul_mem_pointwise_smul, toConjAct_smul
-/
lemma IsCusp.smul {c : OnePoint Real} {𝒢 : Subgroup (GL (Fin 2) Real)} (hc : IsCusp c 𝒢)
    (g : GL (Fin 2) Real) : IsCusp (g • c) (ConjAct.toConjAct g • 𝒢) := by
  obtain ⟨p, hp𝒢, hpp, hpc⟩ := hc
  refine ⟨_, 𝒢.smul_mem_pointwise_smul _ _ hp𝒢, ?_, ?_⟩
  · simpa [ConjAct.toConjAct_smul] using hpp
  · simp [ConjAct.toConjAct_smul, mul_smul, hpc]

/--
lemma `IsCusp.smul_of_mem` / 引理 `IsCusp.smul_of_mem`

English:
lemma IsCusp.smul_of_mem
  statement: {c : OnePoint Real} {𝒢 : Subgroup (GL (Fin 2) Real)} (hc : IsCusp c 𝒢)
  proof: by
  convert! hc.smul g
  ext x
  rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem]; rw [← ConjAct.toConjAct_inv]; rw [ConjAct.toConjAct_smul]; rw [inv_inv]; rw [Subgroup.mul_mem_cancel_right _ hg]; rw [Subgroup.mul_mem_cancel_left _ (inv_mem hg)]

中文:
引理 IsCusp.smul_of_mem
  结论: {c : OnePoint 实数} {𝒢 : 子群 (GL (有限集 2) 实数)} (hc : IsCusp c 𝒢)
  证明: by
  convert! hc.smul g
  ext x
  rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem]; rw [← ConjAct.toConjAct_inv]; rw [ConjAct.toConjAct_smul]; rw [inv_inv]; rw [Subgroup.mul_mem_cancel_right _ hg]; rw [Subgroup.mul_mem_cancel_left _ (inv_mem hg)]

Depends on / 依赖: ConjAct, ConjAct.toConjAct_inv, ConjAct.toConjAct_smul, Subgroup, Subgroup.mem_pointwise_smul_iff_inv_smul_mem, Subgroup.mul_mem_cancel_left, Subgroup.mul_mem_cancel_right, convert, hc.smul, inv_inv, inv_mem, mem_pointwise_smul_iff_inv_smul_mem, mul_mem_cancel_left, mul_mem_cancel_right, toConjAct_inv, toConjAct_smul
-/
lemma IsCusp.smul_of_mem {c : OnePoint Real} {𝒢 : Subgroup (GL (Fin 2) Real)} (hc : IsCusp c 𝒢)
    {g : GL (Fin 2) Real} (hg : g in 𝒢) : IsCusp (g • c) 𝒢 := by
  convert! hc.smul g
  ext x
  rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem]; rw [← ConjAct.toConjAct_inv]; rw [ConjAct.toConjAct_smul]; rw [inv_inv]; rw [Subgroup.mul_mem_cancel_right _ hg]; rw [Subgroup.mul_mem_cancel_left _ (inv_mem hg)]

/--
lemma `isCusp_iff_of_relIndex_ne_zero` / 引理 `isCusp_iff_of_relIndex_ne_zero`

English:
lemma isCusp_iff_of_relIndex_ne_zero
  statement: {𝒢 𝒢' : Subgroup (GL (Fin 2) Real)}
  proof: by
  refine ⟨fun ⟨g, hg, hgp, hgc⟩ => ⟨g, h𝒢 hg, hgp, hgc⟩, fun ⟨g, hg, hgp, hgc⟩ => ?_⟩
  obtain ⟨n, hn, -, hgn⟩ := Subgroup.exists_pow_mem_of_relIndex_ne_zero h𝒢' hg
  refine ⟨g ^ n, (Subgroup.mem_inf.mpr hgn).1, hgp.pow hn.ne', ?_⟩
  rw [Nat.pos_iff_ne_zero] at hn
  rwa [(hgp.pow hn).smul_eq_self

中文:
引理 isCusp_iff_of_relIndex_ne_zero
  结论: {𝒢 𝒢' : 子群 (GL (有限集 2) 实数)}
  证明: by
  refine ⟨fun ⟨g, hg, hgp, hgc⟩ => ⟨g, h𝒢 hg, hgp, hgc⟩, fun ⟨g, hg, hgp, hgc⟩ => ?_⟩
  obtain ⟨n, hn, -, hgn⟩ := Subgroup.exists_pow_mem_of_relIndex_ne_zero h𝒢' hg
  refine ⟨g ^ n, (Subgroup.mem_inf.mpr hgn).1, hgp.pow hn.ne', ?_⟩
  rw [Nat.pos_iff_ne_zero] at hn
  rwa [(hgp.pow hn).smul_eq_self

Depends on / 依赖: Nat.pos_iff_ne_zero, Subgroup, Subgroup.exists_pow_mem_of_relIndex_ne_zero, Subgroup.mem_inf.mpr, exists_pow_mem_of_relIndex_ne_zero, hgp.parabolicFixedPoint_pow, hgp.pow, hgp.smul_eq_self_iff, hn.ne, mem_inf, parabolicFixedPoint_pow, pos_iff_ne_zero, smul_eq_self_iff
-/
lemma isCusp_iff_of_relIndex_ne_zero {𝒢 𝒢' : Subgroup (GL (Fin 2) Real)}
    (h𝒢 : 𝒢' <= 𝒢) (h𝒢' : 𝒢'.relIndex 𝒢 != 0) (c : OnePoint Real) :
    IsCusp c 𝒢' ↔ IsCusp c 𝒢 := by
  refine ⟨fun ⟨g, hg, hgp, hgc⟩ => ⟨g, h𝒢 hg, hgp, hgc⟩, fun ⟨g, hg, hgp, hgc⟩ => ?_⟩
  obtain ⟨n, hn, -, hgn⟩ := Subgroup.exists_pow_mem_of_relIndex_ne_zero h𝒢' hg
  refine ⟨g ^ n, (Subgroup.mem_inf.mpr hgn).1, hgp.pow hn.ne', ?_⟩
  rw [Nat.pos_iff_ne_zero] at hn
  rwa [(hgp.pow hn).smul_eq_self_iff, hgp.parabolicFixedPoint_pow hn, ← hgp.smul_eq_self_iff]

/--
lemma `Subgroup.Commensurable.isCusp_iff` / 引理 `Subgroup.Commensurable.isCusp_iff`

English:
lemma Subgroup.Commensurable.isCusp_iff
  statement: {𝒢 𝒢' : Subgroup (GL (Fin 2) Real)}
  proof: by
  rw [← isCusp_iff_of_relIndex_ne_zero inf_le_left]; rw [isCusp_iff_of_relIndex_ne_zero inf_le_right]
  · simpa [Subgroup.inf_relIndex_right] using h𝒢.1
  · simpa [Subgroup.inf_relIndex_left] using h𝒢.2

中文:
引理 子群.Commensurable.isCusp_iff
  结论: {𝒢 𝒢' : 子群 (GL (有限集 2) 实数)}
  证明: by
  rw [← isCusp_iff_of_relIndex_ne_zero inf_le_left]; rw [isCusp_iff_of_relIndex_ne_zero inf_le_right]
  · simpa [Subgroup.inf_relIndex_right] using h𝒢.1
  · simpa [Subgroup.inf_relIndex_left] using h𝒢.2

Depends on / 依赖: Subgroup, Subgroup.inf_relIndex_left, Subgroup.inf_relIndex_right, inf_le_left, inf_le_right, inf_relIndex_left, inf_relIndex_right, isCusp_iff_of_relIndex_ne_zero
-/
lemma Subgroup.Commensurable.isCusp_iff {𝒢 𝒢' : Subgroup (GL (Fin 2) Real)}
    (h𝒢 : Commensurable 𝒢 𝒢') {c : OnePoint Real} :
    IsCusp c 𝒢 ↔ IsCusp c 𝒢' := by
  rw [← isCusp_iff_of_relIndex_ne_zero inf_le_left]; rw [isCusp_iff_of_relIndex_ne_zero inf_le_right]
  · simpa [Subgroup.inf_relIndex_right] using h𝒢.1
  · simpa [Subgroup.inf_relIndex_left] using h𝒢.2

/--
lemma `IsCusp.mono` / 引理 `IsCusp.mono`

English:
lemma IsCusp.mono
  statement: {𝒢 ℋ : Subgroup (GL (Fin 2) Real)} {c : OnePoint Real} (hGH : 𝒢 <= ℋ)
  proof: match hc with | ⟨h, hh, hp, hc⟩ => ⟨h, hGH hh, hp, hc⟩

中文:
引理 IsCusp.mono
  结论: {𝒢 ℋ : 子群 (GL (有限集 2) 实数)} {c : OnePoint 实数} (hGH : 𝒢 <= ℋ)
  证明: match hc with | ⟨h, hh, hp, hc⟩ => ⟨h, hGH hh, hp, hc⟩
-/
lemma IsCusp.mono {𝒢 ℋ : Subgroup (GL (Fin 2) Real)} {c : OnePoint Real} (hGH : 𝒢 <= ℋ)
    (hc : IsCusp c 𝒢) : IsCusp c ℋ :=
  match hc with | ⟨h, hh, hp, hc⟩ => ⟨h, hGH hh, hp, hc⟩

/--
lemma `IsCusp.of_isFiniteRelIndex` / 引理 `IsCusp.of_isFiniteRelIndex`

English:
lemma IsCusp.of_isFiniteRelIndex
  statement: {𝒢 ℋ : Subgroup (GL (Fin 2) Real)} {c : OnePoint Real}
  proof: by
  have hGH : 𝒢.relIndex ℋ != 0 := 𝒢.relIndex_ne_zero
  rw [← Subgroup.inf_relIndex_right] at hGH
  rw [← isCusp_iff_of_relIndex_ne_zero inf_le_right hGH] at hc
  exact hc.mono inf_le_left

中文:
引理 IsCusp.of_isFiniteRelIndex
  结论: {𝒢 ℋ : 子群 (GL (有限集 2) 实数)} {c : OnePoint 实数}
  证明: by
  have hGH : 𝒢.relIndex ℋ != 0 := 𝒢.relIndex_ne_zero
  rw [← Subgroup.inf_relIndex_right] at hGH
  rw [← isCusp_iff_of_relIndex_ne_zero inf_le_right hGH] at hc
  exact hc.mono inf_le_left

Depends on / 依赖: Subgroup, Subgroup.inf_relIndex_right, hc.mono, inf_le_left, inf_le_right, inf_relIndex_right, isCusp_iff_of_relIndex_ne_zero, relIndex, relIndex_ne_zero
-/
lemma IsCusp.of_isFiniteRelIndex {𝒢 ℋ : Subgroup (GL (Fin 2) Real)} {c : OnePoint Real}
    [𝒢.IsFiniteRelIndex ℋ] (hc : IsCusp c ℋ) : IsCusp c 𝒢 := by
  have hGH : 𝒢.relIndex ℋ != 0 := 𝒢.relIndex_ne_zero
  rw [← Subgroup.inf_relIndex_right] at hGH
  rw [← isCusp_iff_of_relIndex_ne_zero inf_le_right hGH] at hc
  exact hc.mono inf_le_left

open scoped Pointwise in
/--
lemma `IsCusp.of_isFiniteRelIndex_conj` / 引理 `IsCusp.of_isFiniteRelIndex_conj`

English:
lemma IsCusp.of_isFiniteRelIndex_conj
  statement: {𝒢 ℋ : Subgroup (GL (Fin 2) Real)} {c : OnePoint Real}
  proof: by
  suffices (ConjAct.toConjAct h • 𝒢).IsFiniteRelIndex ℋ from hc.of_isFiniteRelIndex
  constructor
  rw [← ℋ.conjAct_pointwise_smul_eq_self (ℋ.le_normalizer hh)]; rw [𝒢.relIndex_pointwise_smul]
  exact 𝒢.relIndex_ne_zero

中文:
引理 IsCusp.of_isFiniteRelIndex_conj
  结论: {𝒢 ℋ : 子群 (GL (有限集 2) 实数)} {c : OnePoint 实数}
  证明: by
  suffices (ConjAct.toConjAct h • 𝒢).IsFiniteRelIndex ℋ from hc.of_isFiniteRelIndex
  constructor
  rw [← ℋ.conjAct_pointwise_smul_eq_self (ℋ.le_normalizer hh)]; rw [𝒢.relIndex_pointwise_smul]
  exact 𝒢.relIndex_ne_zero

Depends on / 依赖: ConjAct, ConjAct.toConjAct, IsFiniteRelIndex, conjAct_pointwise_smul_eq_self, hc.of_isFiniteRelIndex, le_normalizer, of_isFiniteRelIndex, relIndex_ne_zero, relIndex_pointwise_smul, toConjAct
-/
lemma IsCusp.of_isFiniteRelIndex_conj {𝒢 ℋ : Subgroup (GL (Fin 2) Real)} {c : OnePoint Real}
    [𝒢.IsFiniteRelIndex ℋ] (hc : IsCusp c ℋ) {h} (hh : h in ℋ) :
    IsCusp c (ConjAct.toConjAct h • 𝒢) := by
  suffices (ConjAct.toConjAct h • 𝒢).IsFiniteRelIndex ℋ from hc.of_isFiniteRelIndex
  constructor
  rw [← ℋ.conjAct_pointwise_smul_eq_self (ℋ.le_normalizer hh)]; rw [𝒢.relIndex_pointwise_smul]
  exact 𝒢.relIndex_ne_zero

set_option backward.isDefEq.respectTransparency false in
/--
lemma `isCusp_SL2Z_iff` / 引理 `isCusp_SL2Z_iff`

English:
lemma isCusp_SL2Z_iff
  given: {c : OnePoint Real}
  statement: IsCusp c 𝒮ℒ ↔ c in Set.range (OnePoint.map Rat.cast)
  proof: by
  constructor
  · rintro ⟨-, ⟨g, rfl⟩, hgp, hgc⟩
    simpa only [hgp.smul_eq_self_iff.mp hgc] using ⟨(mapGL Rat g).parabolicFixedPoint,
      by simp [GeneralLinearGroup.parabolicFixedPoint, apply_ite]⟩
  · rintro ⟨c, rfl⟩
    obtain ⟨a, rfl⟩ := c.exists_mem_SL2 Int
    refine ⟨_, ⟨a * ModularGro

中文:
引理 isCusp_SL2Z_iff
  条件: {c : OnePoint 实数}
  结论: IsCusp c 𝒮ℒ ↔ c in 集合.range (OnePoint.map 有理数.cast)
  证明: by
  constructor
  · rintro ⟨-, ⟨g, rfl⟩, hgp, hgc⟩
    simpa only [hgp.smul_eq_self_iff.mp hgc] using ⟨(mapGL Rat g).parabolicFixedPoint,
      by simp [GeneralLinearGroup.parabolicFixedPoint, apply_ite]⟩
  · rintro ⟨c, rfl⟩
    obtain ⟨a, rfl⟩ := c.exists_mem_SL2 Int
    refine ⟨_, ⟨a * ModularGro

Depends on / 依赖: GeneralLinearGroup, GeneralLinearGroup.parabolicFixedPoint, IsParabolic, ModularGroup, ModularGroup.T, apply_ite, c.exists_mem_SL2, det_, discr_fin_two, exists_mem_SL2, hgp.smul_eq_self_iff.mp, parabolicFixedPoint, smul_eq_self_iff, trace_fin_two, zero_ne_one
-/
lemma isCusp_SL2Z_iff {c : OnePoint Real} : IsCusp c 𝒮ℒ ↔ c in Set.range (OnePoint.map Rat.cast) := by
  constructor
  · rintro ⟨-, ⟨g, rfl⟩, hgp, hgc⟩
    simpa only [hgp.smul_eq_self_iff.mp hgc] using ⟨(mapGL Rat g).parabolicFixedPoint,
      by simp [GeneralLinearGroup.parabolicFixedPoint, apply_ite]⟩
  · rintro ⟨c, rfl⟩
    obtain ⟨a, rfl⟩ := c.exists_mem_SL2 Int
    refine ⟨_, ⟨a * ModularGroup.T * a⁻¹, rfl⟩, ?_, ?_⟩
    · suffices (mapGL Real ModularGroup.T).IsParabolic by simpa
      refine ⟨fun ⟨a, ha⟩ => zero_ne_one' Real (by simpa [ModularGroup.T] using congr_fun₂ ha 0 1), ?_⟩
      simp [discr_fin_two, trace_fin_two, det_fin_two, ModularGroup.T]
      norm_num
    · rw [← Rat.coe_castHom, ← (Rat.castHom Real).algebraMap_toAlgebra]
      simp [OnePoint.map_smul, mul_smul, smul_infty_eq_self_iff, ModularGroup.T]

set_option backward.isDefEq.respectTransparency false in
/--
lemma `isCusp_SL2Z_iff'` / 引理 `isCusp_SL2Z_iff'`

English:
lemma isCusp_SL2Z_iff'
  given: {c : OnePoint Real}
  statement: IsCusp c 𝒮ℒ ↔ exists g : SL(2, Int), c = mapGL Real g • ∞
  proof: by
  rw [isCusp_SL2Z_iff]
  constructor
  · rintro ⟨c, rfl⟩
    obtain ⟨g, rfl⟩ := c.exists_mem_SL2 Int
    refine ⟨g, ?_⟩
    rw [← Rat.coe_castHom]; rw [OnePoint.map_smul]; rw [OnePoint.map_infty]; rw [← (Rat.castHom Real).algebraMap_toAlgebra]; rw [g.map_mapGL]
  · rintro ⟨g, rfl⟩
    refine ⟨map

中文:
引理 isCusp_SL2Z_iff'
  条件: {c : OnePoint 实数}
  结论: IsCusp c 𝒮ℒ ↔ 存在 g : SL(2, 整数), c = mapGL 实数 g • ∞
  证明: by
  rw [isCusp_SL2Z_iff]
  constructor
  · rintro ⟨c, rfl⟩
    obtain ⟨g, rfl⟩ := c.exists_mem_SL2 Int
    refine ⟨g, ?_⟩
    rw [← Rat.coe_castHom]; rw [OnePoint.map_smul]; rw [OnePoint.map_infty]; rw [← (Rat.castHom Real).algebraMap_toAlgebra]; rw [g.map_mapGL]
  · rintro ⟨g, rfl⟩
    refine ⟨map

Depends on / 依赖: OnePoint, OnePoint.map_infty, OnePoint.map_smul, Rat.castHom, Rat.coe_castHom, algebraMap_toAlgebra, c.exists_mem_SL2, castHom, coe_castHom, exists_mem_SL2, g.map_mapGL, isCusp_SL2Z_iff, map_infty, map_mapGL, map_smul
-/
lemma isCusp_SL2Z_iff' {c : OnePoint Real} : IsCusp c 𝒮ℒ ↔ exists g : SL(2, Int), c = mapGL Real g • ∞ := by
  rw [isCusp_SL2Z_iff]
  constructor
  · rintro ⟨c, rfl⟩
    obtain ⟨g, rfl⟩ := c.exists_mem_SL2 Int
    refine ⟨g, ?_⟩
    rw [← Rat.coe_castHom]; rw [OnePoint.map_smul]; rw [OnePoint.map_infty]; rw [← (Rat.castHom Real).algebraMap_toAlgebra]; rw [g.map_mapGL]
  · rintro ⟨g, rfl⟩
    refine ⟨mapGL Rat g • ∞, ?_⟩
    rw [← Rat.coe_castHom]; rw [OnePoint.map_smul]; rw [OnePoint.map_infty]; rw [← (Rat.castHom Real).algebraMap_toAlgebra]; rw [g.map_mapGL]

/--
lemma `Subgroup.IsArithmetic.isCusp_iff_isCusp_SL2Z` / 引理 `Subgroup.IsArithmetic.isCusp_iff_isCusp_SL2Z`

English:
lemma Subgroup.IsArithmetic.isCusp_iff_isCusp_SL2Z
  statement: (𝒢 : Subgroup (GL (Fin 2) Real)) [𝒢.IsArithmetic]
  proof: is_commensurable.isCusp_iff

中文:
引理 子群.是Arithmetic.isCusp_iff_isCusp_SL2Z
  结论: (𝒢 : 子群 (GL (有限集 2) 实数)) [𝒢.是Arithmetic]
  证明: is_commensurable.isCusp_iff

Depends on / 依赖: isCusp_iff, is_commensurable, is_commensurable.isCusp_iff
-/
lemma Subgroup.IsArithmetic.isCusp_iff_isCusp_SL2Z (𝒢 : Subgroup (GL (Fin 2) Real)) [𝒢.IsArithmetic]
    {c : OnePoint Real} : IsCusp c 𝒢 ↔ IsCusp c 𝒮ℒ :=
  is_commensurable.isCusp_iff

end IsCusp

section CuspOrbits
/-!
## Cusp orbits

We consider the orbits for the action of `𝒢` on its own cusps. The main result is that if
`[𝒢.IsArithmetic]` holds, then this set is finite.
-/

/--
Definition of `cuspsSubMulAction` / `cuspsSubMulAction` 的定义

English:
definition cuspsSubMulAction
  signature: (𝒢 : Subgroup (GL (Fin 2) Real))
  body: {c | IsCusp c 𝒢}
  smul_mem' g _ hc := IsCusp.smul_of_mem hc g.property

中文:
定义 cuspsSubMulAction
  签名: (𝒢 : 子群 (GL (有限集 2) 实数))
  定义体: {c | IsCusp c 𝒢}
  smul_mem' g _ hc := IsCusp.smul_of_mem hc g.property

Depends on / 依赖: IsCusp
-/
noncomputable def cuspsSubMulAction (𝒢 : Subgroup (GL (Fin 2) Real)) :
    SubMulAction 𝒢 (OnePoint Real) where
  carrier := {c | IsCusp c 𝒢}
  smul_mem' g _ hc := IsCusp.smul_of_mem hc g.property

/--
Definition of `CuspOrbits` / `CuspOrbits` 的定义

English:
abbreviation CuspOrbits
  signature: (𝒢 : Subgroup (GL (Fin 2) Real))
  body: MulAction.orbitRel.Quotient 𝒢 (cuspsSubMulAction 𝒢)

中文:
缩写 CuspOrbits
  签名: (𝒢 : 子群 (GL (有限集 2) 实数))
  定义体: MulAction.orbitRel.Quotient 𝒢 (cuspsSubMulAction 𝒢)

Depends on / 依赖: MulAction, MulAction.orbitRel.Quotient, Quotient, cuspsSubMulAction, orbitRel
-/
abbrev CuspOrbits (𝒢 : Subgroup (GL (Fin 2) Real)) :=
  MulAction.orbitRel.Quotient 𝒢 (cuspsSubMulAction 𝒢)

set_option backward.isDefEq.respectTransparency false in
/--
Definition of `cosetToCuspOrbit` / `cosetToCuspOrbit` 的定义

English:
definition cosetToCuspOrbit
  signature: (𝒢 : Subgroup (GL (Fin 2) Real)) [𝒢.IsArithmetic]
  body: Quotient.lift
    (fun g => ⟦⟨mapGL Real g⁻¹ • ∞,
(Subgroup.IsArithmetic.isCusp_iff_isCusp_SL2Z 𝒢).mpr isCusp_SL2Z_iff.mpr
        ⟨mapGL Rat g⁻¹ • ∞, by rw [← Rat.coe_castHom, OnePoint.map_smul, OnePoint.map_infty,
          ← (Rat.castHom Real).algebraMap_toAlgebra, map_mapGL]⟩⟩⟧)
    (fun a b hab

中文:
定义 cosetToCuspOrbit
  签名: (𝒢 : 子群 (GL (有限集 2) 实数)) [𝒢.是Arithmetic]
  定义体: Quotient.lift
    (fun g => ⟦⟨mapGL Real g⁻¹ • ∞,
(Subgroup.IsArithmetic.isCusp_iff_isCusp_SL2Z 𝒢).mpr isCusp_SL2Z_iff.mpr
        ⟨mapGL Rat g⁻¹ • ∞, by rw [← Rat.coe_castHom, OnePoint.map_smul, OnePoint.map_infty,
          ← (Rat.castHom Real).algebraMap_toAlgebra, map_mapGL]⟩⟩⟧)
    (fun a b hab

Depends on / 依赖: IsArithmetic, OnePoint, OnePoint.map_infty, OnePoint.map_smul, Quotient, Quotient.eq, Quotient.eq.mpr, Quotient.eq_iff_equiv, Quotient.lift, QuotientGroup, QuotientGroup.leftRel_apply, Rat.castHom, Rat.coe_castHom, Subgroup, Subgroup.IsArithmetic.isCusp_iff_isCusp_SL2Z, algebraMap_toAlgebra, castHom, coe_castHom, eq_iff_equiv, isCusp_SL2Z_iff
-/
noncomputable def cosetToCuspOrbit (𝒢 : Subgroup (GL (Fin 2) Real)) [𝒢.IsArithmetic] :
    SL(2, Int) ⧸ (𝒢.comap <| mapGL Real) -> CuspOrbits 𝒢 :=
  Quotient.lift
    (fun g => ⟦⟨mapGL Real g⁻¹ • ∞,
(Subgroup.IsArithmetic.isCusp_iff_isCusp_SL2Z 𝒢).mpr isCusp_SL2Z_iff.mpr
        ⟨mapGL Rat g⁻¹ • ∞, by rw [← Rat.coe_castHom, OnePoint.map_smul, OnePoint.map_infty,
          ← (Rat.castHom Real).algebraMap_toAlgebra, map_mapGL]⟩⟩⟧)
    (fun a b hab => by
      rw [← Quotient.eq_iff_equiv]; rw [Quotient.eq]; rw [QuotientGroup.leftRel_apply] at hab
      refine Quotient.eq.mpr ⟨⟨_, hab⟩, ?_⟩
      simp [mul_smul])

set_option backward.isDefEq.respectTransparency false in
@[simp]
/--
lemma `cosetToCuspOrbit_apply_mk` / 引理 `cosetToCuspOrbit_apply_mk`

English:
lemma cosetToCuspOrbit_apply_mk
  given: {𝒢 : Subgroup (GL (Fin 2) Real)} [𝒢.IsArithmetic] (g : SL(2, Int))
  proof: rfl

中文:
引理 cosetToCuspOrbit_apply_mk
  条件: {𝒢 : 子群 (GL (有限集 2) 实数)} [𝒢.是Arithmetic] (g : SL(2, 整数))
  证明: rfl
-/
lemma cosetToCuspOrbit_apply_mk {𝒢 : Subgroup (GL (Fin 2) Real)} [𝒢.IsArithmetic] (g : SL(2, Int)) :
    cosetToCuspOrbit 𝒢 ⟦g⟧ = ⟦⟨mapGL Real g⁻¹ • ∞,
(Subgroup.IsArithmetic.isCusp_iff_isCusp_SL2Z 𝒢).mpr isCusp_SL2Z_iff.mpr
      ⟨mapGL Rat g⁻¹ • ∞, by rw [← Rat.coe_castHom, OnePoint.map_smul, OnePoint.map_infty,
        ← (Rat.castHom Real).algebraMap_toAlgebra, map_mapGL]⟩⟩⟧ :=
  rfl

/--
lemma `surjective_cosetToCuspOrbit` / 引理 `surjective_cosetToCuspOrbit`

English:
lemma surjective_cosetToCuspOrbit
  given: (𝒢 : Subgroup (GL (Fin 2) Real)) [𝒢.IsArithmetic]
  proof: by
  rintro ⟨c, (hc : IsCusp c _)⟩
  rw [Subgroup.IsArithmetic.isCusp_iff_isCusp_SL2Z]; rw [isCusp_SL2Z_iff'] at hc
  obtain ⟨g, rfl⟩ := hc
  use ⟦g⁻¹⟧
  aesop

中文:
引理 surjective_cosetToCuspOrbit
  条件: (𝒢 : 子群 (GL (有限集 2) 实数)) [𝒢.是Arithmetic]
  证明: by
  rintro ⟨c, (hc : IsCusp c _)⟩
  rw [Subgroup.IsArithmetic.isCusp_iff_isCusp_SL2Z]; rw [isCusp_SL2Z_iff'] at hc
  obtain ⟨g, rfl⟩ := hc
  use ⟦g⁻¹⟧
  aesop

Depends on / 依赖: IsArithmetic, IsCusp, Subgroup, Subgroup.IsArithmetic.isCusp_iff_isCusp_SL2Z, isCusp_SL2Z_iff, isCusp_iff_isCusp_SL2Z
-/
lemma surjective_cosetToCuspOrbit (𝒢 : Subgroup (GL (Fin 2) Real)) [𝒢.IsArithmetic] :
    (cosetToCuspOrbit 𝒢).Surjective := by
  rintro ⟨c, (hc : IsCusp c _)⟩
  rw [Subgroup.IsArithmetic.isCusp_iff_isCusp_SL2Z]; rw [isCusp_SL2Z_iff'] at hc
  obtain ⟨g, rfl⟩ := hc
  use ⟦g⁻¹⟧
  aesop

/-- An arithmetic subgroup has finitely many cusp orbits. -/
instance (𝒢 : Subgroup (GL (Fin 2) Real)) [𝒢.IsArithmetic] : Finite (CuspOrbits 𝒢) :=
  .of_surjective _ (surjective_cosetToCuspOrbit 𝒢)

end CuspOrbits

section Width
/-!
## Width of a cusp

We define the *strict width* of `𝒢` at `∞` to be the smallest `h > 0` such that `[1, h; 0, 1] ∈ 𝒢`,
or `0` if no such `h` exists; and the *width* of `𝒢` to be the strict width of the subgroup
generated by `𝒢` and `-1`, or equivalently the smallest `h > 0` such that `±[1, h; 0, 1] ∈ 𝒢`
(again, if it exists). We show both widths exist when `𝒢` is discrete and has det `± 1`.
-/

namespace Subgroup

section Ring

variable {R : Type*} [Ring R] (𝒢 : Subgroup (GL (Fin 2) R))

/--
Definition of `strictPeriods` / `strictPeriods` 的定义

English:
definition strictPeriods
  signature: : AddSubgroup R
  body: (toAddSubgroup 𝒢).comap upperRightHom.toAddMonoidHom

中文:
定义 strictPeriods
  签名: : 加法子群 R
  定义体: (toAddSubgroup 𝒢).comap upperRightHom.toAddMonoidHom

Depends on / 依赖: toAddMonoidHom, toAddSubgroup, upperRightHom, upperRightHom.toAddMonoidHom
-/
def strictPeriods : AddSubgroup R :=
  (toAddSubgroup 𝒢).comap upperRightHom.toAddMonoidHom

variable {𝒢} in
/--
lemma `mem_strictPeriods_iff` / 引理 `mem_strictPeriods_iff`

English:
lemma mem_strictPeriods_iff
  given: {x : R}
  proof: by
  simp [strictPeriods]

中文:
引理 mem_strictPeriods_iff
  条件: {x : R}
  证明: by
  simp [strictPeriods]
-/
@[simp] lemma mem_strictPeriods_iff {x : R} :
    x in 𝒢.strictPeriods ↔ upperRightHom x in 𝒢 := by
  simp [strictPeriods]

/--
Definition of `noncomputable` / `noncomputable` 的定义

English:
definition noncomputable
  signature: def periods
  body: 𝒢.adjoinNegOne.strictPeriods

中文:
定义 noncomputable
  签名: def periods
  定义体: 𝒢.adjoinNegOne.strictPeriods
-/
protected noncomputable def periods : AddSubgroup R :=
  𝒢.adjoinNegOne.strictPeriods

/--
lemma `strictPeriods_le_periods` / 引理 `strictPeriods_le_periods`

English:
lemma strictPeriods_le_periods
  statement: 𝒢.strictPeriods <= 𝒢.periods
  proof: by
  intro k
  simp only [Subgroup.periods, strictPeriods]
  apply 𝒢.le_adjoinNegOne

中文:
引理 strictPeriods_le_periods
  结论: 𝒢.strictPeriods <= 𝒢.periods
  证明: by
  intro k
  simp only [Subgroup.periods, strictPeriods]
  apply 𝒢.le_adjoinNegOne

Depends on / 依赖: Subgroup, Subgroup.periods, le_adjoinNegOne, periods, strictPeriods
-/
lemma strictPeriods_le_periods : 𝒢.strictPeriods <= 𝒢.periods := by
  intro k
  simp only [Subgroup.periods, strictPeriods]
  apply 𝒢.le_adjoinNegOne

/--
Definition of `IsRegularAtInfty` / `IsRegularAtInfty` 的定义

English:
definition IsRegularAtInfty
  signature: : Prop
  body: 𝒢.strictPeriods = 𝒢.periods

中文:
定义 IsRegularAtInfty
  签名: : 命题
  定义体: 𝒢.strictPeriods = 𝒢.periods

Depends on / 依赖: periods, strictPeriods
-/
def IsRegularAtInfty : Prop :=
  𝒢.strictPeriods = 𝒢.periods

/--
lemma `IsRegularAtInfty.eq` / 引理 `IsRegularAtInfty.eq`

English:
lemma IsRegularAtInfty.eq
  given: (h : 𝒢.IsRegularAtInfty)
  statement: 𝒢.strictPeriods = 𝒢.periods
  proof: h

中文:
引理 IsRegularAtInfty.eq
  条件: (h : 𝒢.IsRegularAtInfty)
  结论: 𝒢.strictPeriods = 𝒢.periods
  证明: h
-/
lemma IsRegularAtInfty.eq (h : 𝒢.IsRegularAtInfty) : 𝒢.strictPeriods = 𝒢.periods := h

/--
lemma `relIndex_strictPeriods` / 引理 `relIndex_strictPeriods`

English:
lemma relIndex_strictPeriods
  proof: by
  by_cases h : 𝒢.strictPeriods = 𝒢.periods
  · simp [h]
  · replace h := 𝒢.strictPeriods_le_periods.lt_of_ne h
    obtain ⟨u, hu_mem, hu_notMem⟩ := (SetLike.lt_iff_le_and_exists.mp h).2
    rw [AddSubgroup.relIndex_eq_two_iff_exists_notMem_and]
    refine .inr ⟨u, hu_mem, hu_notMem, fun b hb => ?

中文:
引理 relIndex_strictPeriods
  证明: by
  by_cases h : 𝒢.strictPeriods = 𝒢.periods
  · simp [h]
  · replace h := 𝒢.strictPeriods_le_periods.lt_of_ne h
    obtain ⟨u, hu_mem, hu_notMem⟩ := (SetLike.lt_iff_le_and_exists.mp h).2
    rw [AddSubgroup.relIndex_eq_two_iff_exists_notMem_and]
    refine .inr ⟨u, hu_mem, hu_notMem, fun b hb => ?

Depends on / 依赖: AddChar, AddChar.map_add_eq_mul, AddSubgroup, AddSubgroup.relIndex_eq_two_iff_exists_notMem_and, Or.inl, Or.inr, SetLike, SetLike.lt_iff_le_and_exists.mp, Subgroup, Subgroup.periods, hu_mem, hu_notMem, lt_iff_le_and_exists, lt_of_ne, map_add_eq_mul, mem_adjoinNegOne_iff, mem_strictPeriods_iff, mul_mem, neg_mul_neg, periods
-/
lemma relIndex_strictPeriods :
    𝒢.strictPeriods.relIndex 𝒢.periods = 1 ∨ 𝒢.strictPeriods.relIndex 𝒢.periods = 2 := by
  by_cases h : 𝒢.strictPeriods = 𝒢.periods
  · simp [h]
  · replace h := 𝒢.strictPeriods_le_periods.lt_of_ne h
    obtain ⟨u, hu_mem, hu_notMem⟩ := (SetLike.lt_iff_le_and_exists.mp h).2
    rw [AddSubgroup.relIndex_eq_two_iff_exists_notMem_and]
    refine .inr ⟨u, hu_mem, hu_notMem, fun b hb => ?_⟩
    simp only [Subgroup.periods, mem_strictPeriods_iff, mem_adjoinNegOne_iff,
      AddChar.map_add_eq_mul] at hu_mem hu_notMem hb ⊢
    rcases hb with h | h
    · exact Or.inr h
    · simpa only [neg_mul_neg] using Or.inl (mul_mem h <| hu_mem.resolve_left hu_notMem)

/--
lemma `commensurable_strictPeriods_periods` / 引理 `commensurable_strictPeriods_periods`

English:
lemma commensurable_strictPeriods_periods
  proof: by
  constructor
  · rcases 𝒢.relIndex_strictPeriods with h | h <;> simp [h]
  · simp [AddSubgroup.relIndex_eq_one.mpr 𝒢.strictPeriods_le_periods]

中文:
引理 commensurable_strictPeriods_periods
  证明: by
  constructor
  · rcases 𝒢.relIndex_strictPeriods with h | h <;> simp [h]
  · simp [AddSubgroup.relIndex_eq_one.mpr 𝒢.strictPeriods_le_periods]

Depends on / 依赖: AddSubgroup, AddSubgroup.relIndex_eq_one.mpr, relIndex_eq_one, relIndex_strictPeriods, strictPeriods_le_periods
-/
lemma commensurable_strictPeriods_periods :
    𝒢.strictPeriods.Commensurable 𝒢.periods := by
  constructor
  · rcases 𝒢.relIndex_strictPeriods with h | h <;> simp [h]
  · simp [AddSubgroup.relIndex_eq_one.mpr 𝒢.strictPeriods_le_periods]

variable {𝒢}

/--
lemma `strictPeriods_eq_periods_of_neg_one_mem` / 引理 `strictPeriods_eq_periods_of_neg_one_mem`

English:
lemma strictPeriods_eq_periods_of_neg_one_mem
  given: (h𝒢 : -1 in 𝒢)
  proof: by
  simp [Subgroup.periods, adjoinNegOne_eq_self_iff.mpr h𝒢]

中文:
引理 strictPeriods_eq_periods_of_neg_one_mem
  条件: (h𝒢 : -1 in 𝒢)
  证明: by
  simp [Subgroup.periods, adjoinNegOne_eq_self_iff.mpr h𝒢]

Depends on / 依赖: Subgroup, Subgroup.periods, adjoinNegOne_eq_self_iff, adjoinNegOne_eq_self_iff.mpr, periods
-/
lemma strictPeriods_eq_periods_of_neg_one_mem (h𝒢 : -1 in 𝒢) :
    𝒢.strictPeriods = 𝒢.periods := by
  simp [Subgroup.periods, adjoinNegOne_eq_self_iff.mpr h𝒢]

/--
lemma `isRegularAtInfty_of_neg_one_mem` / 引理 `isRegularAtInfty_of_neg_one_mem`

English:
lemma isRegularAtInfty_of_neg_one_mem
  given: (h𝒢 : -1 in 𝒢)
  statement: 𝒢.IsRegularAtInfty
  proof: 𝒢.strictPeriods_eq_periods_of_neg_one_mem h𝒢

中文:
引理 isRegularAtInfty_of_neg_one_mem
  条件: (h𝒢 : -1 in 𝒢)
  结论: 𝒢.IsRegularAtInfty
  证明: 𝒢.strictPeriods_eq_periods_of_neg_one_mem h𝒢

Depends on / 依赖: strictPeriods_eq_periods_of_neg_one_mem
-/
lemma isRegularAtInfty_of_neg_one_mem (h𝒢 : -1 in 𝒢) : 𝒢.IsRegularAtInfty :=
  𝒢.strictPeriods_eq_periods_of_neg_one_mem h𝒢

variable [TopologicalSpace R] [IsTopologicalRing R]

/--
Instance `instDiscreteTopStrictPeriods` / 实例 `instDiscreteTopStrictPeriods`

English:
instance instDiscreteTopStrictPeriods
  signature: [hG : DiscreteTopology 𝒢]
  body: by
  let H : Set (GL (Fin 2) R) := 𝒢 inter Set.range upperRightHom
  have hH : DiscreteTopology H := hG.of_subset Set.inter_subset_left
  have : Set.MapsTo upperRightHom 𝒢.strictPeriods H := fun x hx => by
    grind [SetLike.mem_coe, Subgroup.mem_strictPeriods_iff]
  exact .of_continuous_injective (

中文:
实例 instDiscreteTopStrictPeriods
  签名: [hG : 离散拓扑 𝒢]
  定义体: by
  let H : Set (GL (Fin 2) R) := 𝒢 inter Set.range upperRightHom
  have hH : DiscreteTopology H := hG.of_subset Set.inter_subset_left
  have : Set.MapsTo upperRightHom 𝒢.strictPeriods H := fun x hx => by
    grind [SetLike.mem_coe, Subgroup.mem_strictPeriods_iff]
  exact .of_continuous_injective (

Depends on / 依赖: DiscreteTopology, MapsTo, Set.MapsTo, Set.inter_subset_left, Set.range, SetLike, SetLike.mem_coe, Subgroup, Subgroup.mem_strictPeriods_iff, continuous_upperRightHom, continuous_upperRightHom.restrict, hG.of_subset, injective_upperRightHom, injective_upperRightHom.injOn, inter_subset_left, mem_coe, mem_strictPeriods_iff, of_continuous_injective, of_subset, restrict
-/
instance instDiscreteTopStrictPeriods [hG : DiscreteTopology 𝒢] :
    DiscreteTopology 𝒢.strictPeriods := by
  let H : Set (GL (Fin 2) R) := 𝒢 inter Set.range upperRightHom
  have hH : DiscreteTopology H := hG.of_subset Set.inter_subset_left
  have : Set.MapsTo upperRightHom 𝒢.strictPeriods H := fun x hx => by
    grind [SetLike.mem_coe, Subgroup.mem_strictPeriods_iff]
  exact .of_continuous_injective (continuous_upperRightHom.restrict this)
    (this.restrict_inj.mpr injective_upperRightHom.injOn)

/--
Instance `instDiscreteTopPeriods` / 实例 `instDiscreteTopPeriods`

English:
instance instDiscreteTopPeriods
  signature: [T2Space R] [hG : DiscreteTopology 𝒢]
  body: inferInstanceAs (DiscreteTopology 𝒢.adjoinNegOne.strictPeriods)

中文:
实例 instDiscreteTopPeriods
  签名: [T2空间 R] [hG : 离散拓扑 𝒢]
  定义体: inferInstanceAs (DiscreteTopology 𝒢.adjoinNegOne.strictPeriods)

Depends on / 依赖: DiscreteTopology, adjoinNegOne, adjoinNegOne.strictPeriods, strictPeriods
-/
instance instDiscreteTopPeriods [T2Space R] [hG : DiscreteTopology 𝒢] :
    DiscreteTopology 𝒢.periods :=
  inferInstanceAs (DiscreteTopology 𝒢.adjoinNegOne.strictPeriods)

end Ring

/--
lemma `strictPeriods_eq_zmultiples_one_of_T_mem` / 引理 `strictPeriods_eq_zmultiples_one_of_T_mem`

English:
lemma strictPeriods_eq_zmultiples_one_of_T_mem
  given: {Γ : Subgroup SL(2, Int)} (hΓ : ModularGroup.T in Γ)
  proof: by
  ext x
  simp only [mem_strictPeriods_iff, Subgroup.mem_map, Units.ext_iff, mapGL_coe_matrix,
    map_apply_coe]
  refine ⟨fun ⟨g, _, hg⟩ => ⟨g 0 1, by simpa using congr_fun₂ hg 0 1⟩, ?_⟩
  rintro ⟨m, rfl⟩
  refine ⟨ModularGroup.T ^ m, zpow_mem hΓ m, ?_⟩
  ext i j
  fin_cases i <;> fin_cases j <

中文:
引理 strictPeriods_eq_zmultiples_one_of_T_mem
  条件: {Γ : 子群 SL(2, 整数)} (hΓ : ModularGroup.T in Γ)
  证明: by
  ext x
  simp only [mem_strictPeriods_iff, Subgroup.mem_map, Units.ext_iff, mapGL_coe_matrix,
    map_apply_coe]
  refine ⟨fun ⟨g, _, hg⟩ => ⟨g 0 1, by simpa using congr_fun₂ hg 0 1⟩, ?_⟩
  rintro ⟨m, rfl⟩
  refine ⟨ModularGroup.T ^ m, zpow_mem hΓ m, ?_⟩
  ext i j
  fin_cases i <;> fin_cases j <

Depends on / 依赖: ModularGroup, ModularGroup.T, ModularGroup.coe_T_zpow, Subgroup, Subgroup.mem_map, Units.ext_iff, coe_T_zpow, ext_iff, fin_cases, mapGL_coe_matrix, map_apply_coe, mem_map, mem_strictPeriods_iff, zpow_mem
-/
lemma strictPeriods_eq_zmultiples_one_of_T_mem {Γ : Subgroup SL(2, Int)} (hΓ : ModularGroup.T in Γ) :
    strictPeriods (Γ : Subgroup (GL (Fin 2) Real)) = AddSubgroup.zmultiples 1 := by
  ext x
  simp only [mem_strictPeriods_iff, Subgroup.mem_map, Units.ext_iff, mapGL_coe_matrix,
    map_apply_coe]
  refine ⟨fun ⟨g, _, hg⟩ => ⟨g 0 1, by simpa using congr_fun₂ hg 0 1⟩, ?_⟩
  rintro ⟨m, rfl⟩
  refine ⟨ModularGroup.T ^ m, zpow_mem hΓ m, ?_⟩
  ext i j
  fin_cases i <;> fin_cases j <;> simp [ModularGroup.coe_T_zpow]

/--
lemma `strictPeriods_SL2Z` / 引理 `strictPeriods_SL2Z`

English:
lemma strictPeriods_SL2Z
  statement: strictPeriods 𝒮ℒ = AddSubgroup.zmultiples 1
  proof: by
  simpa [MonoidHom.range_eq_map] using strictPeriods_eq_zmultiples_one_of_T_mem (mem_top _)

中文:
引理 strictPeriods_SL2Z
  结论: strictPeriods 𝒮ℒ = 加法子群.zmultiples 1
  证明: by
  simpa [MonoidHom.range_eq_map] using strictPeriods_eq_zmultiples_one_of_T_mem (mem_top _)
-/
@[simp] lemma strictPeriods_SL2Z : strictPeriods 𝒮ℒ = AddSubgroup.zmultiples 1 := by
  simpa [MonoidHom.range_eq_map] using strictPeriods_eq_zmultiples_one_of_T_mem (mem_top _)

section Real

variable (𝒢 : Subgroup (GL (Fin 2) Real))

open scoped Classical in
/--
Definition of `strictWidthInfty` / `strictWidthInfty` 的定义

English:
definition strictWidthInfty
  signature: : Real
  body: if h : DiscreteTopology 𝒢.strictPeriods then
|Exists.choose 𝒢.strictPeriods.isAddCyclic_iff_exists_zmultiples_eq_top.mp
 AddSubgroup.discrete_iff_addCyclic.mpr h|
  else 0

中文:
定义 strictWidthInfty
  签名: : 实数
  定义体: if h : DiscreteTopology 𝒢.strictPeriods then
|Exists.choose 𝒢.strictPeriods.isAddCyclic_iff_exists_zmultiples_eq_top.mp
 AddSubgroup.discrete_iff_addCyclic.mpr h|
  else 0

Depends on / 依赖: AddSubgroup, AddSubgroup.discrete_iff_addCyclic.mpr, DiscreteTopology, Exists, Exists.choose, discrete_iff_addCyclic, isAddCyclic_iff_exists_zmultiples_eq_top, strictPeriods, strictPeriods.isAddCyclic_iff_exists_zmultiples_eq_top.mp
-/
noncomputable def strictWidthInfty : Real :=
  if h : DiscreteTopology 𝒢.strictPeriods then
|Exists.choose 𝒢.strictPeriods.isAddCyclic_iff_exists_zmultiples_eq_top.mp
 AddSubgroup.discrete_iff_addCyclic.mpr h|
  else 0

/--
lemma `strictWidthInfty_nonneg` / 引理 `strictWidthInfty_nonneg`

English:
lemma strictWidthInfty_nonneg
  statement: 0 <= 𝒢.strictWidthInfty
  proof: by
  unfold strictWidthInfty; aesop

中文:
引理 strictWidthInfty_nonneg
  结论: 0 <= 𝒢.strictWidthInfty
  证明: by
  unfold strictWidthInfty; aesop

Depends on / 依赖: strictWidthInfty
-/
lemma strictWidthInfty_nonneg : 0 <= 𝒢.strictWidthInfty := by
  unfold strictWidthInfty; aesop

/--
Definition of `widthInfty` / `widthInfty` 的定义

English:
definition widthInfty
  signature: : Real
  body: 𝒢.adjoinNegOne.strictWidthInfty

中文:
定义 widthInfty
  签名: : 实数
  定义体: 𝒢.adjoinNegOne.strictWidthInfty

Depends on / 依赖: adjoinNegOne, adjoinNegOne.strictWidthInfty, strictWidthInfty
-/
noncomputable def widthInfty : Real := 𝒢.adjoinNegOne.strictWidthInfty

/--
lemma `widthInfty_nonneg` / 引理 `widthInfty_nonneg`

English:
lemma widthInfty_nonneg
  statement: 0 <= 𝒢.widthInfty
  proof: 𝒢.adjoinNegOne.strictWidthInfty_nonneg

中文:
引理 widthInfty_nonneg
  结论: 0 <= 𝒢.widthInfty
  证明: 𝒢.adjoinNegOne.strictWidthInfty_nonneg

Depends on / 依赖: adjoinNegOne, adjoinNegOne.strictWidthInfty_nonneg, strictWidthInfty_nonneg
-/
lemma widthInfty_nonneg : 0 <= 𝒢.widthInfty := 𝒢.adjoinNegOne.strictWidthInfty_nonneg

variable {𝒢} in
/--
lemma `strictPeriods_eq_zmultiples_strictWidthInfty` / 引理 `strictPeriods_eq_zmultiples_strictWidthInfty`

English:
lemma strictPeriods_eq_zmultiples_strictWidthInfty
  given: [DiscreteTopology 𝒢.strictPeriods]
  proof: by
  simp [Subgroup.strictWidthInfty, dif_pos,
Exists.choose_spec 𝒢.strictPeriods.isAddCyclic_iff_exists_zmultiples_eq_top.mp
 AddSubgroup.discrete_iff_addCyclic.mpr inferInstance]

中文:
引理 strictPeriods_eq_zmultiples_strictWidthInfty
  条件: [离散拓扑 𝒢.strictPeriods]
  证明: by
  simp [Subgroup.strictWidthInfty, dif_pos,
Exists.choose_spec 𝒢.strictPeriods.isAddCyclic_iff_exists_zmultiples_eq_top.mp
 AddSubgroup.discrete_iff_addCyclic.mpr inferInstance]

Depends on / 依赖: AddSubgroup, AddSubgroup.discrete_iff_addCyclic.mpr, Exists, Exists.choose_spec, Subgroup, Subgroup.strictWidthInfty, choose_spec, dif_pos, discrete_iff_addCyclic, isAddCyclic_iff_exists_zmultiples_eq_top, strictPeriods, strictPeriods.isAddCyclic_iff_exists_zmultiples_eq_top.mp, strictWidthInfty
-/
lemma strictPeriods_eq_zmultiples_strictWidthInfty [DiscreteTopology 𝒢.strictPeriods] :
    𝒢.strictPeriods = AddSubgroup.zmultiples 𝒢.strictWidthInfty := by
  simp [Subgroup.strictWidthInfty, dif_pos,
Exists.choose_spec 𝒢.strictPeriods.isAddCyclic_iff_exists_zmultiples_eq_top.mp
 AddSubgroup.discrete_iff_addCyclic.mpr inferInstance]

/--
lemma `strictWidthInfty_eq_one_of_T_mem` / 引理 `strictWidthInfty_eq_one_of_T_mem`

English:
lemma strictWidthInfty_eq_one_of_T_mem
  given: {Γ : Subgroup SL(2, Int)} (hΓ : ModularGroup.T in Γ)
  proof: by
  have hsp := strictPeriods_eq_zmultiples_one_of_T_mem hΓ
  have : DiscreteTopology (Γ : Subgroup (GL (Fin 2) Real)).strictPeriods := by
    -- In fact the image of `Γ` in `GL (Fin 2) ℝ` is itself discrete, but this is quicker:
    rw [hsp]
    infer_instance
  rw [strictPeriods_eq_zmultiples_str

中文:
引理 strictWidthInfty_eq_one_of_T_mem
  条件: {Γ : 子群 SL(2, 整数)} (hΓ : ModularGroup.T in Γ)
  证明: by
  have hsp := strictPeriods_eq_zmultiples_one_of_T_mem hΓ
  have : DiscreteTopology (Γ : Subgroup (GL (Fin 2) Real)).strictPeriods := by
    -- In fact the image of `Γ` in `GL (Fin 2) ℝ` is itself discrete, but this is quicker:
    rw [hsp]
    infer_instance
  rw [strictPeriods_eq_zmultiples_str

Depends on / 依赖: DiscreteTopology, Subgroup, strictPeriods, strictPeriods_eq_zmultiples_one_of_T_mem
-/
lemma strictWidthInfty_eq_one_of_T_mem {Γ : Subgroup SL(2, Int)} (hΓ : ModularGroup.T in Γ) :
    strictWidthInfty (Γ : Subgroup (GL (Fin 2) Real)) = 1 := by
  have hsp := strictPeriods_eq_zmultiples_one_of_T_mem hΓ
  have : DiscreteTopology (Γ : Subgroup (GL (Fin 2) Real)).strictPeriods := by
    -- In fact the image of `Γ` in `GL (Fin 2) ℝ` is itself discrete, but this is quicker:
    rw [hsp]
    infer_instance
  rw [strictPeriods_eq_zmultiples_strictWidthInfty]; rw [Eq.comm]; rw [AddSubgroup.zmultiples_eq_zmultiples_iff (not_isOfFinAddOrder_of_isAddTorsionFree one_ne_zero)]
    at hsp
  grind [strictWidthInfty_nonneg]

/--
lemma `strictWidthInfty_SL2Z` / 引理 `strictWidthInfty_SL2Z`

English:
lemma strictWidthInfty_SL2Z
  statement: strictWidthInfty 𝒮ℒ = 1
  proof: by
  simpa [MonoidHom.range_eq_map] using strictWidthInfty_eq_one_of_T_mem (mem_top _)

中文:
引理 strictWidthInfty_SL2Z
  结论: strictWidthInfty 𝒮ℒ = 1
  证明: by
  simpa [MonoidHom.range_eq_map] using strictWidthInfty_eq_one_of_T_mem (mem_top _)

Depends on / 依赖: MonoidHom, MonoidHom.range_eq_map, mem_top, range_eq_map, strictWidthInfty_eq_one_of_T_mem
-/
lemma strictWidthInfty_SL2Z : strictWidthInfty 𝒮ℒ = 1 := by
  simpa [MonoidHom.range_eq_map] using strictWidthInfty_eq_one_of_T_mem (mem_top _)

/--
lemma `strictWidthInfty_mem_strictPeriods` / 引理 `strictWidthInfty_mem_strictPeriods`

English:
lemma strictWidthInfty_mem_strictPeriods
  statement: 𝒢.strictWidthInfty in 𝒢.strictPeriods
  proof: by
  by_cases h : DiscreteTopology 𝒢.strictPeriods
  · simp [strictPeriods_eq_zmultiples_strictWidthInfty]
  · simp [strictWidthInfty, dif_neg h]

中文:
引理 strictWidthInfty_mem_strictPeriods
  结论: 𝒢.strictWidthInfty in 𝒢.strictPeriods
  证明: by
  by_cases h : DiscreteTopology 𝒢.strictPeriods
  · simp [strictPeriods_eq_zmultiples_strictWidthInfty]
  · simp [strictWidthInfty, dif_neg h]

Depends on / 依赖: DiscreteTopology, dif_neg, strictPeriods, strictPeriods_eq_zmultiples_strictWidthInfty, strictWidthInfty
-/
lemma strictWidthInfty_mem_strictPeriods : 𝒢.strictWidthInfty in 𝒢.strictPeriods := by
  by_cases h : DiscreteTopology 𝒢.strictPeriods
  · simp [strictPeriods_eq_zmultiples_strictWidthInfty]
  · simp [strictWidthInfty, dif_neg h]

variable {𝒢} in
/--
lemma `periods_eq_zmultiples_widthInfty` / 引理 `periods_eq_zmultiples_widthInfty`

English:
lemma periods_eq_zmultiples_widthInfty
  given: [DiscreteTopology 𝒢.periods]
  proof: have : DiscreteTopology 𝒢.adjoinNegOne.strictPeriods := ‹_›
  𝒢.adjoinNegOne.strictPeriods_eq_zmultiples_strictWidthInfty

中文:
引理 periods_eq_zmultiples_widthInfty
  条件: [离散拓扑 𝒢.periods]
  证明: have : DiscreteTopology 𝒢.adjoinNegOne.strictPeriods := ‹_›
  𝒢.adjoinNegOne.strictPeriods_eq_zmultiples_strictWidthInfty

Depends on / 依赖: DiscreteTopology, adjoinNegOne, adjoinNegOne.strictPeriods, adjoinNegOne.strictPeriods_eq_zmultiples_strictWidthInfty, strictPeriods, strictPeriods_eq_zmultiples_strictWidthInfty
-/
lemma periods_eq_zmultiples_widthInfty [DiscreteTopology 𝒢.periods] :
    𝒢.periods = AddSubgroup.zmultiples 𝒢.widthInfty :=
  have : DiscreteTopology 𝒢.adjoinNegOne.strictPeriods := ‹_›
  𝒢.adjoinNegOne.strictPeriods_eq_zmultiples_strictWidthInfty

/--
lemma `widthInfty_mem_periods` / 引理 `widthInfty_mem_periods`

English:
lemma widthInfty_mem_periods
  statement: 𝒢.widthInfty in 𝒢.periods
  proof: 𝒢.adjoinNegOne.strictWidthInfty_mem_strictPeriods

中文:
引理 widthInfty_mem_periods
  结论: 𝒢.widthInfty in 𝒢.periods
  证明: 𝒢.adjoinNegOne.strictWidthInfty_mem_strictPeriods

Depends on / 依赖: adjoinNegOne, adjoinNegOne.strictWidthInfty_mem_strictPeriods, strictWidthInfty_mem_strictPeriods
-/
lemma widthInfty_mem_periods : 𝒢.widthInfty in 𝒢.periods :=
  𝒢.adjoinNegOne.strictWidthInfty_mem_strictPeriods

/--
lemma `two_mul_widthInfty_mem_strictPeriods` / 引理 `two_mul_widthInfty_mem_strictPeriods`

English:
lemma two_mul_widthInfty_mem_strictPeriods
  statement: 2 * 𝒢.widthInfty in 𝒢.strictPeriods
  proof: by
  have := 𝒢.widthInfty_mem_periods
  simp only [Subgroup.periods, mem_strictPeriods_iff] at this
  rcases this with (h | h) <;>
    simpa [-upperRightHom_apply, ← AddChar.map_nsmul_eq_pow] using Subgroup.pow_mem _ h 2

中文:
引理 two_mul_widthInfty_mem_strictPeriods
  结论: 2 * 𝒢.widthInfty in 𝒢.strictPeriods
  证明: by
  have := 𝒢.widthInfty_mem_periods
  simp only [Subgroup.periods, mem_strictPeriods_iff] at this
  rcases this with (h | h) <;>
    simpa [-upperRightHom_apply, ← AddChar.map_nsmul_eq_pow] using Subgroup.pow_mem _ h 2

Depends on / 依赖: AddChar, AddChar.map_nsmul_eq_pow, Subgroup, Subgroup.periods, Subgroup.pow_mem, map_nsmul_eq_pow, mem_strictPeriods_iff, periods, pow_mem, upperRightHom_apply, widthInfty_mem_periods
-/
lemma two_mul_widthInfty_mem_strictPeriods : 2 * 𝒢.widthInfty in 𝒢.strictPeriods := by
  have := 𝒢.widthInfty_mem_periods
  simp only [Subgroup.periods, mem_strictPeriods_iff] at this
  rcases this with (h | h) <;>
    simpa [-upperRightHom_apply, ← AddChar.map_nsmul_eq_pow] using Subgroup.pow_mem _ h 2

variable {𝒢} in
/--
lemma `strictWidthInfty_pos_iff` / 引理 `strictWidthInfty_pos_iff`

English:
lemma strictWidthInfty_pos_iff
  given: [DiscreteTopology 𝒢.strictPeriods] [𝒢.HasDetPlusMinusOne]
  proof: by
  constructor
  · refine fun h => ⟨_, mem_strictPeriods_iff.mpr 𝒢.strictWidthInfty_mem_strictPeriods, ?_, ?_⟩
    · rw [GeneralLinearGroup.isParabolic_iff_of_upperTriangular (by simp)]
      simpa using h.ne'
    · simp [smul_infty_eq_self_iff]
  · -- Hard implication: if `∞` is a cusp, show the 

中文:
引理 strictWidthInfty_pos_iff
  条件: [离散拓扑 𝒢.strictPeriods] [𝒢.有DetPlusMinusOne]
  证明: by
  constructor
  · refine fun h => ⟨_, mem_strictPeriods_iff.mpr 𝒢.strictWidthInfty_mem_strictPeriods, ?_, ?_⟩
    · rw [GeneralLinearGroup.isParabolic_iff_of_upperTriangular (by simp)]
      simpa using h.ne'
    · simp [smul_infty_eq_self_iff]
  · -- Hard implication: if `∞` is a cusp, show the 

Depends on / 依赖: AddSubgroup, AddSubgroup.mk_eq_z, AddSubgroup.ne_bot_iff_exists_ne_zero, AddSubgroup.zmultiples_ne_bot, GeneralLinearGroup, GeneralLinearGroup.isParabolic_iff_of_upperTriangular, Subtype, Subtype.exists, h.ne, implication, isParabolic_iff_of_upperTriangular, lt_of_ne, mem_strictPeriods_iff, mem_strictPeriods_iff.mpr, mk_eq_z, ne_bot_iff_exists_ne_zero, positive, smul_infty_eq_self_iff, strict, strictWidthInfty_mem_strictPeriods
-/
lemma strictWidthInfty_pos_iff [DiscreteTopology 𝒢.strictPeriods] [𝒢.HasDetPlusMinusOne] :
    0 < 𝒢.strictWidthInfty ↔ IsCusp ∞ 𝒢 := by
  constructor
  · refine fun h => ⟨_, mem_strictPeriods_iff.mpr 𝒢.strictWidthInfty_mem_strictPeriods, ?_, ?_⟩
    · rw [GeneralLinearGroup.isParabolic_iff_of_upperTriangular (by simp)]
      simpa using h.ne'
    · simp [smul_infty_eq_self_iff]
  · -- Hard implication: if `∞` is a cusp, show the strict width is positive.
    rintro ⟨g, hgg, hgp, hgi⟩
    apply 𝒢.strictWidthInfty_nonneg.lt_of_ne'
    rw [← AddSubgroup.zmultiples_ne_bot]
    simp only [AddSubgroup.ne_bot_iff_exists_ne_zero, Subtype.exists, Ne, AddSubgroup.mk_eq_zero,
      exists_prop, and_comm, ← strictPeriods_eq_zmultiples_strictWidthInfty, mem_strictPeriods_iff]
    -- We have some `g ∈ 𝒢` which is parabolic and fixes `∞`. So `g = ±[1, x; 0, 1]` some `x ≠ 0`.
    rw [smul_infty_eq_self_iff] at hgi
    rw [Subgroup.HasDetPlusMinusOne.isParabolic_iff_of_upperTriangular hgg hgi] at hgp
    rcases hgp with ⟨x, hx, rfl⟩ | ⟨x, hx, rfl⟩
    · -- If `g = [1, x; 0, 1]`, we're done
      exact ⟨x, hx, hgg⟩
    · -- If `g = -[1, x; 0, 1]` then `g ^ 2 = [1, 2 * x; 0, 1]`.
      exact ⟨2 • x, by grind,
        by simpa only [AddChar.map_nsmul_eq_pow, neg_sq] using pow_mem hgg 2⟩

/--
lemma `strictWidthInfty_pos` / 引理 `strictWidthInfty_pos`

English:
lemma strictWidthInfty_pos
  given: [𝒢.IsArithmetic]
  statement: 0 < 𝒢.strictWidthInfty
  proof: by
  rw [strictWidthInfty_pos_iff]
  simpa [Subgroup.IsArithmetic.isCusp_iff_isCusp_SL2Z, isCusp_SL2Z_iff]
    using ⟨_, OnePoint.map_infty _⟩

中文:
引理 strictWidthInfty_pos
  条件: [𝒢.是Arithmetic]
  结论: 0 < 𝒢.strictWidthInfty
  证明: by
  rw [strictWidthInfty_pos_iff]
  simpa [Subgroup.IsArithmetic.isCusp_iff_isCusp_SL2Z, isCusp_SL2Z_iff]
    using ⟨_, OnePoint.map_infty _⟩

Depends on / 依赖: IsArithmetic, OnePoint, OnePoint.map_infty, Subgroup, Subgroup.IsArithmetic.isCusp_iff_isCusp_SL2Z, isCusp_SL2Z_iff, isCusp_iff_isCusp_SL2Z, map_infty, strictWidthInfty_pos_iff
-/
lemma strictWidthInfty_pos [𝒢.IsArithmetic] : 0 < 𝒢.strictWidthInfty := by
  rw [strictWidthInfty_pos_iff]
  simpa [Subgroup.IsArithmetic.isCusp_iff_isCusp_SL2Z, isCusp_SL2Z_iff]
    using ⟨_, OnePoint.map_infty _⟩

variable {𝒢} in
/--
lemma `isCusp_of_mem_strictPeriods` / 引理 `isCusp_of_mem_strictPeriods`

English:
lemma isCusp_of_mem_strictPeriods
  given: {h : Real} (hh : 0 < h) (h𝒢 : h in 𝒢.strictPeriods)
  proof: by
  refine ⟨upperRightHom h, 𝒢.mem_strictPeriods_iff.mp h𝒢, ?_, smul_infty_eq_self_iff.mpr rfl⟩
  exact (GeneralLinearGroup.isParabolic_iff_of_upperTriangular rfl).mpr ⟨rfl, hh.ne'⟩

中文:
引理 isCusp_of_mem_strictPeriods
  条件: {h : 实数} (hh : 0 < h) (h𝒢 : h in 𝒢.strictPeriods)
  证明: by
  refine ⟨upperRightHom h, 𝒢.mem_strictPeriods_iff.mp h𝒢, ?_, smul_infty_eq_self_iff.mpr rfl⟩
  exact (GeneralLinearGroup.isParabolic_iff_of_upperTriangular rfl).mpr ⟨rfl, hh.ne'⟩

Depends on / 依赖: GeneralLinearGroup, GeneralLinearGroup.isParabolic_iff_of_upperTriangular, hh.ne, isParabolic_iff_of_upperTriangular, mem_strictPeriods_iff, mem_strictPeriods_iff.mp, smul_infty_eq_self_iff, smul_infty_eq_self_iff.mpr, upperRightHom
-/
lemma isCusp_of_mem_strictPeriods {h : Real} (hh : 0 < h) (h𝒢 : h in 𝒢.strictPeriods) :
    IsCusp OnePoint.infty 𝒢 := by
  refine ⟨upperRightHom h, 𝒢.mem_strictPeriods_iff.mp h𝒢, ?_, smul_infty_eq_self_iff.mpr rfl⟩
  exact (GeneralLinearGroup.isParabolic_iff_of_upperTriangular rfl).mpr ⟨rfl, hh.ne'⟩

variable {𝒢} in
/--
lemma `widthInfty_pos_iff` / 引理 `widthInfty_pos_iff`

English:
lemma widthInfty_pos_iff
  given: [DiscreteTopology 𝒢.periods] [𝒢.HasDetPlusMinusOne]
  proof: by
  have : DiscreteTopology 𝒢.adjoinNegOne.strictPeriods := ‹_›
  rw [widthInfty]; rw [strictWidthInfty_pos_iff]; rw [(commensurable_adjoinNegOne_self 𝒢).isCusp_iff]

中文:
引理 widthInfty_pos_iff
  条件: [离散拓扑 𝒢.periods] [𝒢.有DetPlusMinusOne]
  证明: by
  have : DiscreteTopology 𝒢.adjoinNegOne.strictPeriods := ‹_›
  rw [widthInfty]; rw [strictWidthInfty_pos_iff]; rw [(commensurable_adjoinNegOne_self 𝒢).isCusp_iff]

Depends on / 依赖: DiscreteTopology, adjoinNegOne, adjoinNegOne.strictPeriods, commensurable_adjoinNegOne_self, isCusp_iff, strictPeriods, strictWidthInfty_pos_iff, widthInfty
-/
lemma widthInfty_pos_iff [DiscreteTopology 𝒢.periods] [𝒢.HasDetPlusMinusOne] :
    0 < 𝒢.widthInfty ↔ IsCusp ∞ 𝒢 := by
  have : DiscreteTopology 𝒢.adjoinNegOne.strictPeriods := ‹_›
  rw [widthInfty]; rw [strictWidthInfty_pos_iff]; rw [(commensurable_adjoinNegOne_self 𝒢).isCusp_iff]

variable {𝒢} in
/--
lemma `isRegularAtInfty_iff` / 引理 `isRegularAtInfty_iff`

English:
lemma isRegularAtInfty_iff
  given: [DiscreteTopology 𝒢.periods]
  proof: by
  refine ⟨fun h => h ▸ widthInfty_mem_periods 𝒢, fun h => ?_⟩
  apply 𝒢.strictPeriods_le_periods.antisymm
  rwa [periods_eq_zmultiples_widthInfty, AddSubgroup.zmultiples_le]

中文:
引理 isRegularAtInfty_iff
  条件: [离散拓扑 𝒢.periods]
  证明: by
  refine ⟨fun h => h ▸ widthInfty_mem_periods 𝒢, fun h => ?_⟩
  apply 𝒢.strictPeriods_le_periods.antisymm
  rwa [periods_eq_zmultiples_widthInfty, AddSubgroup.zmultiples_le]

Depends on / 依赖: AddSubgroup, AddSubgroup.zmultiples_le, antisymm, periods_eq_zmultiples_widthInfty, strictPeriods_le_periods, strictPeriods_le_periods.antisymm, widthInfty_mem_periods, zmultiples_le
-/
lemma isRegularAtInfty_iff [DiscreteTopology 𝒢.periods] :
    𝒢.IsRegularAtInfty ↔ 𝒢.widthInfty in 𝒢.strictPeriods := by
  refine ⟨fun h => h ▸ widthInfty_mem_periods 𝒢, fun h => ?_⟩
  apply 𝒢.strictPeriods_le_periods.antisymm
  rwa [periods_eq_zmultiples_widthInfty, AddSubgroup.zmultiples_le]

/--
lemma `widthInfty_pos` / 引理 `widthInfty_pos`

English:
lemma widthInfty_pos
  given: [𝒢.IsArithmetic]
  statement: 0 < 𝒢.widthInfty
  proof: by
  apply strictWidthInfty_pos

中文:
引理 widthInfty_pos
  条件: [𝒢.是Arithmetic]
  结论: 0 < 𝒢.widthInfty
  证明: by
  apply strictWidthInfty_pos

Depends on / 依赖: strictWidthInfty_pos
-/
lemma widthInfty_pos [𝒢.IsArithmetic] : 0 < 𝒢.widthInfty := by
  apply strictWidthInfty_pos

end Real

end Subgroup

open Subgroup

namespace CongruenceSubgroup

set_option backward.isDefEq.respectTransparency.types false in
/--
lemma `strictPeriods_Gamma0` / 引理 `strictPeriods_Gamma0`

English:
lemma strictPeriods_Gamma0
  given: (N : Nat)
  proof: strictPeriods_eq_zmultiples_one_of_T_mem by simp [ModularGroup.T]

中文:
引理 strictPeriods_Gamma0
  条件: (N : 自然数)
  证明: strictPeriods_eq_zmultiples_one_of_T_mem by simp [ModularGroup.T]
-/
@[simp] lemma strictPeriods_Gamma0 (N : Nat) :
    strictPeriods (Gamma0 N : Subgroup (GL (Fin 2) Real)) = AddSubgroup.zmultiples 1 :=
strictPeriods_eq_zmultiples_one_of_T_mem by simp [ModularGroup.T]

set_option backward.isDefEq.respectTransparency.types false in
/--
lemma `strictPeriods_Gamma1` / 引理 `strictPeriods_Gamma1`

English:
lemma strictPeriods_Gamma1
  given: (N : Nat)
  proof: strictPeriods_eq_zmultiples_one_of_T_mem by simp [ModularGroup.T]

中文:
引理 strictPeriods_Gamma1
  条件: (N : 自然数)
  证明: strictPeriods_eq_zmultiples_one_of_T_mem by simp [ModularGroup.T]
-/
@[simp] lemma strictPeriods_Gamma1 (N : Nat) :
    strictPeriods (Gamma1 N : Subgroup (GL (Fin 2) Real)) = AddSubgroup.zmultiples 1 :=
strictPeriods_eq_zmultiples_one_of_T_mem by simp [ModularGroup.T]

set_option backward.isDefEq.respectTransparency.types false in
/--
lemma `strictWidthInfty_Gamma0` / 引理 `strictWidthInfty_Gamma0`

English:
lemma strictWidthInfty_Gamma0
  given: (N : Nat)
  proof: strictWidthInfty_eq_one_of_T_mem by simp [ModularGroup.T]

中文:
引理 strictWidthInfty_Gamma0
  条件: (N : 自然数)
  证明: strictWidthInfty_eq_one_of_T_mem by simp [ModularGroup.T]
-/
@[simp] lemma strictWidthInfty_Gamma0 (N : Nat) :
    strictWidthInfty (Gamma0 N : Subgroup (GL (Fin 2) Real)) = 1 :=
strictWidthInfty_eq_one_of_T_mem by simp [ModularGroup.T]

set_option backward.isDefEq.respectTransparency.types false in
/--
lemma `strictWidthInfty_Gamma1` / 引理 `strictWidthInfty_Gamma1`

English:
lemma strictWidthInfty_Gamma1
  given: (N : Nat)
  proof: strictWidthInfty_eq_one_of_T_mem by simp [ModularGroup.T]

中文:
引理 strictWidthInfty_Gamma1
  条件: (N : 自然数)
  证明: strictWidthInfty_eq_one_of_T_mem by simp [ModularGroup.T]
-/
@[simp] lemma strictWidthInfty_Gamma1 (N : Nat) :
    strictWidthInfty (Gamma1 N : Subgroup (GL (Fin 2) Real)) = 1 :=
strictWidthInfty_eq_one_of_T_mem by simp [ModularGroup.T]

/--
lemma `strictPeriods_Gamma` / 引理 `strictPeriods_Gamma`

English:
lemma strictPeriods_Gamma
  given: (N : Nat)
  proof: by
  ext x
  have : AddSubgroup.zmultiples ↑N = .map (Int.castAddHom Real) (.zmultiples N) := by simp
  simp only [this, mem_strictPeriods_iff, Subgroup.mem_map, Gamma_mem]
  constructor
  · rintro ⟨g, ⟨-, hg, -, -⟩, hx⟩
    rw [show x = g 0 1 by simpa using congr_arg (· 0 1) hx.symm]
    apply AddS

中文:
引理 strictPeriods_Gamma
  条件: (N : 自然数)
  证明: by
  ext x
  have : AddSubgroup.zmultiples ↑N = .map (Int.castAddHom Real) (.zmultiples N) := by simp
  simp only [this, mem_strictPeriods_iff, Subgroup.mem_map, Gamma_mem]
  constructor
  · rintro ⟨g, ⟨-, hg, -, -⟩, hx⟩
    rw [show x = g 0 1 by simpa using congr_arg (· 0 1) hx.symm]
    apply AddS
-/
@[simp] lemma strictPeriods_Gamma (N : Nat) :
    strictPeriods (Gamma N : Subgroup (GL (Fin 2) Real)) = AddSubgroup.zmultiples ↑N := by
  ext x
  have : AddSubgroup.zmultiples ↑N = .map (Int.castAddHom Real) (.zmultiples N) := by simp
  simp only [this, mem_strictPeriods_iff, Subgroup.mem_map, Gamma_mem]
  constructor
  · rintro ⟨g, ⟨-, hg, -, -⟩, hx⟩
    rw [show x = g 0 1 by simpa using congr_arg (· 0 1) hx.symm]
    apply AddSubgroup.mem_map_of_mem
    rwa [Int.mem_zmultiples_iff, ← ZMod.intCast_zmod_eq_zero_iff_dvd]
  · simp only [AddSubgroup.mem_map, AddSubgroup.mem_zmultiples_iff, existsAndEq, true_and,
      Units.ext_iff, mapGL_coe_matrix, map_apply_coe, forall_exists_index]
    refine fun a ha => ⟨ModularGroup.T ^ (a * N), by simp [ModularGroup.coe_T_zpow], ?_⟩
    ext i j
    fin_cases i <;> fin_cases j <;> simp [ModularGroup.coe_T_zpow, ← ha]

/--
lemma `strictWidthInfty_Gamma` / 引理 `strictWidthInfty_Gamma`

English:
lemma strictWidthInfty_Gamma
  given: (N : Nat) [NeZero N]
  proof: by
  have hsp := strictPeriods_Gamma N
  rw [strictPeriods_eq_zmultiples_strictWidthInfty]; rw [Eq.comm]; rw [AddSubgroup.zmultiples_eq_zmultiples_iff
      (not_isOfFinAddOrder_of_isAddTorsionFree (NeZero.ne _))] at hsp
  grind [strictWidthInfty_nonneg, Nat.cast_nonneg]

中文:
引理 strictWidthInfty_Gamma
  条件: (N : 自然数) [NeZero N]
  证明: by
  have hsp := strictPeriods_Gamma N
  rw [strictPeriods_eq_zmultiples_strictWidthInfty]; rw [Eq.comm]; rw [AddSubgroup.zmultiples_eq_zmultiples_iff
      (not_isOfFinAddOrder_of_isAddTorsionFree (NeZero.ne _))] at hsp
  grind [strictWidthInfty_nonneg, Nat.cast_nonneg]
-/
@[simp] lemma strictWidthInfty_Gamma (N : Nat) [NeZero N] :
    strictWidthInfty (Gamma N : Subgroup (GL (Fin 2) Real)) = N := by
  have hsp := strictPeriods_Gamma N
  rw [strictPeriods_eq_zmultiples_strictWidthInfty]; rw [Eq.comm]; rw [AddSubgroup.zmultiples_eq_zmultiples_iff
      (not_isOfFinAddOrder_of_isAddTorsionFree (NeZero.ne _))] at hsp
  grind [strictWidthInfty_nonneg, Nat.cast_nonneg]

end CongruenceSubgroup

end Width
