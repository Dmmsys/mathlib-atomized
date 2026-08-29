/-
Copyright (c) 2025 David Loeffler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Loeffler
-/
module

public import Mathlib.Analysis.Normed.Group.Uniform
public import Mathlib.Topology.Algebra.Group.Matrix
public import Mathlib.Topology.Algebra.IsUniformGroup.DiscreteSubgroup

/-!
# Arithmetic subgroups of `GL(2, ℝ)`

We define a subgroup of `GL (Fin 2) ℝ` to be *arithmetic* if it is commensurable with the image
of `SL(2, ℤ)`.
-/

@[expose] public section

open Matrix Matrix.SpecialLinearGroup

open scoped MatrixGroups

local notation "SL" => SpecialLinearGroup

variable {n : Type*} [Fintype n] [DecidableEq n]

namespace Subgroup

section det_typeclasses

variable {R : Type*} [CommRing R] (Γ : Subgroup (GL n R))

/--
Definition of `HasDetPlusMinusOne` / `HasDetPlusMinusOne` 的定义

English:
class HasDetPlusMinusOne
  parameters: : Prop where
  axioms and operations (1):
    - det_eq({g} (hg : g in Γ)) : g.det = 1 ∨ g.det = -1

中文:
类 有DetPlusMinusOne
  参数: : 命题 where
  公理与运算 (1 个):
    - det_eq({g} (hg : g in Γ)) : g.det = 1 ∨ g.det = -1
-/
class HasDetPlusMinusOne : Prop where
  det_eq {g} (hg : g in Γ) : g.det = 1 ∨ g.det = -1

variable {Γ} in
/--
lemma `HasDetPlusMinusOne.abs_det` / 引理 `HasDetPlusMinusOne.abs_det`

English:
lemma HasDetPlusMinusOne.abs_det
  statement: [LinearOrder R] [IsOrderedRing R] [HasDetPlusMinusOne Γ]
  proof: by
  rcases HasDetPlusMinusOne.det_eq hg with h | h <;> simp [h]

中文:
引理 有DetPlusMinusOne.abs_det
  结论: [线性序 R] [是Ordered环 R] [有DetPlusMinusOne Γ]
  证明: by
  rcases HasDetPlusMinusOne.det_eq hg with h | h <;> simp [h]

Depends on / 依赖: HasDetPlusMinusOne, HasDetPlusMinusOne.det_eq, det_eq
-/
lemma HasDetPlusMinusOne.abs_det [LinearOrder R] [IsOrderedRing R] [HasDetPlusMinusOne Γ]
    {g} (hg : g in Γ) : |g.det.val| = 1 := by
  rcases HasDetPlusMinusOne.det_eq hg with h | h <;> simp [h]

/--
lemma `hasDetPlusMinusOne_iff_abs_det` / 引理 `hasDetPlusMinusOne_iff_abs_det`

English:
lemma hasDetPlusMinusOne_iff_abs_det
  given: [LinearOrder R] [IsOrderedRing R]
  proof: by
  refine ⟨fun h {g} hg => h.abs_det hg, fun h => ⟨?_⟩⟩
  simpa [-GeneralLinearGroup.val_det_apply, abs_eq zero_le_one] using @h

中文:
引理 hasDetPlusMinusOne_iff_abs_det
  条件: [线性序 R] [是Ordered环 R]
  证明: by
  refine ⟨fun h {g} hg => h.abs_det hg, fun h => ⟨?_⟩⟩
  simpa [-GeneralLinearGroup.val_det_apply, abs_eq zero_le_one] using @h

Depends on / 依赖: GeneralLinearGroup, GeneralLinearGroup.val_det_apply, abs_det, abs_eq, h.abs_det, val_det_apply, zero_le_one
-/
lemma hasDetPlusMinusOne_iff_abs_det [LinearOrder R] [IsOrderedRing R] :
    HasDetPlusMinusOne Γ ↔ forall {g}, g in Γ -> |g.det.val| = 1 := by
  refine ⟨fun h {g} hg => h.abs_det hg, fun h => ⟨?_⟩⟩
  simpa [-GeneralLinearGroup.val_det_apply, abs_eq zero_le_one] using @h

/--
Definition of `HasDetOne` / `HasDetOne` 的定义

English:
class HasDetOne
  parameters: : Prop where
  axioms and operations (1):
    - det_eq({g} (hg : g in Γ)) : g.det = 1

中文:
类 有DetOne
  参数: : 命题 where
  公理与运算 (1 个):
    - det_eq({g} (hg : g in Γ)) : g.det = 1
-/
class HasDetOne : Prop where
  det_eq {g} (hg : g in Γ) : g.det = 1

instance (Γ : Subgroup (SL n R)) : HasDetOne (Γ.map toGL) where
  det_eq {g} hg := by rcases hg with ⟨g, hg, rfl⟩; simp

instance {S : Type*} [CommRing S] [Algebra R S] (Γ : Subgroup (SL n R)) :
    HasDetOne (Γ.map <| mapGL S) where
  det_eq {g} hg := by rcases hg with ⟨g, hg, rfl⟩; simp

instance {S : Type*} [CommRing S] [Algebra R S] :
    HasDetOne (mapGL (n := n) (R := R) S).range where
  det_eq {g} hg := by rcases hg with ⟨g, hg, rfl⟩; simp

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [HasDetOne
  signature: Γ] : HasDetPlusMinusOne Γ
  body: ⟨fun {g} hg => by simp [HasDetOne.det_eq hg]⟩

中文:
实例 [有DetOne
  签名: Γ] : 有DetPlusMinusOne Γ
  定义体: ⟨fun {g} hg => by simp [HasDetOne.det_eq hg]⟩

Depends on / 依赖: HasDetOne, HasDetOne.det_eq, det_eq
-/
instance [HasDetOne Γ] : HasDetPlusMinusOne Γ := ⟨fun {g} hg => by simp [HasDetOne.det_eq hg]⟩

instance (Γ' : Subgroup (GL n R)) [HasDetOne Γ] : HasDetOne (Γ ⊓ Γ') where
  det_eq hg := HasDetOne.det_eq hg.1

instance (Γ' : Subgroup (GL n R)) [HasDetOne Γ] : HasDetOne (Γ' ⊓ Γ) where
  det_eq hg := HasDetOne.det_eq hg.2

open scoped Pointwise in
instance (Γ : Subgroup (GL n R)) [HasDetOne Γ] (g : ConjAct <| GL n R) :
    HasDetOne (g • Γ) where
  det_eq {h} hh := by
    rw [mem_pointwise_smul_iff_inv_smul_mem] at hh
    simpa [ConjAct.smul_def] using HasDetOne.det_eq hh

open scoped Pointwise in
instance (Γ : Subgroup (GL n R)) [HasDetPlusMinusOne Γ] (g : ConjAct <| GL n R) :
    HasDetPlusMinusOne (g • Γ) where
  det_eq {h} hh := by
    rw [mem_pointwise_smul_iff_inv_smul_mem] at hh
    simpa [ConjAct.smul_def] using HasDetPlusMinusOne.det_eq hh

end det_typeclasses

section SL2Z_in_GL2R

/-- The image of the modular group `SL(2, ℤ)`, as a subgroup of `GL(2, ℝ)`. -/
scoped[MatrixGroups] notation "𝒮ℒ" => MonoidHom.range (mapGL Real : SL(2, Int) ->* GL (Fin 2) Real)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Coe (Subgroup SL(2, Int)) (Subgroup (GL (Fin 2) Real))
  body: map (mapGL Real)

中文:
实例 :
  签名: Coe (子群 SL(2, 整数)) (子群 (GL (有限集 2) 实数))
  定义体: map (mapGL Real)
-/
instance : Coe (Subgroup SL(2, Int)) (Subgroup (GL (Fin 2) Real)) where
  coe := map (mapGL Real)

/--
Definition of `IsArithmetic` / `IsArithmetic` 的定义

English:
class IsArithmetic
  parameters: (𝒢 : Subgroup (GL (Fin 2) Real))
  axioms and operations (1):
    - is_commensurable : Commensurable 𝒢 𝒮ℒ

中文:
类 是Arithmetic
  参数: (𝒢 : 子群 (GL (有限集 2) 实数))
  公理与运算 (1 个):
    - is_commensurable : Commensurable 𝒢 𝒮ℒ
-/
class IsArithmetic (𝒢 : Subgroup (GL (Fin 2) Real)) : Prop where
  is_commensurable : Commensurable 𝒢 𝒮ℒ

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: IsArithmetic 𝒮ℒ
  body: .refl 𝒮ℒ

中文:
实例 :
  签名: 是Arithmetic 𝒮ℒ
  定义体: .refl 𝒮ℒ
-/
instance : IsArithmetic 𝒮ℒ where is_commensurable := .refl 𝒮ℒ

/--
lemma `isArithmetic_iff_finiteIndex` / 引理 `isArithmetic_iff_finiteIndex`

English:
lemma isArithmetic_iff_finiteIndex
  given: {Γ : Subgroup SL(2, Int)}
  statement: IsArithmetic Γ ↔ Γ.FiniteIndex
  proof: by
  constructor <;>
  · refine fun ⟨h⟩ => ⟨?_⟩
    simpa [Commensurable, MonoidHom.range_eq_map, ← relIndex_comap,
      comap_map_eq_self_of_injective mapGL_injective] using h

中文:
引理 isArithmetic_iff_finiteIndex
  条件: {Γ : 子群 SL(2, 整数)}
  结论: 是Arithmetic Γ ↔ Γ.FiniteIndex
  证明: by
  constructor <;>
  · refine fun ⟨h⟩ => ⟨?_⟩
    simpa [Commensurable, MonoidHom.range_eq_map, ← relIndex_comap,
      comap_map_eq_self_of_injective mapGL_injective] using h

Depends on / 依赖: Commensurable, MonoidHom, MonoidHom.range_eq_map, comap_map_eq_self_of_injective, mapGL_injective, range_eq_map, relIndex_comap
-/
lemma isArithmetic_iff_finiteIndex {Γ : Subgroup SL(2, Int)} : IsArithmetic Γ ↔ Γ.FiniteIndex := by
  constructor <;>
  · refine fun ⟨h⟩ => ⟨?_⟩
    simpa [Commensurable, MonoidHom.range_eq_map, ← relIndex_comap,
      comap_map_eq_self_of_injective mapGL_injective] using h

/-- Images in `GL(2, ℝ)` of finite-index subgroups of `SL(2, ℤ)` are arithmetic. -/
instance (Γ : Subgroup SL(2, Int)) [Γ.FiniteIndex] : IsArithmetic Γ :=
  isArithmetic_iff_finiteIndex.mpr ‹_›

/--
Instance `IsArithmetic.finiteIndex_comap` / 实例 `IsArithmetic.finiteIndex_comap`

English:
instance IsArithmetic.finiteIndex_comap
  signature: (𝒢 : Subgroup (GL (Fin 2) Real)) [IsArithmetic 𝒢]
  body: ⟨𝒢.index_comap (mapGL (R := Int) Real) ▸ IsArithmetic.is_commensurable.1⟩

中文:
实例 是Arithmetic.finiteIndex_comap
  签名: (𝒢 : 子群 (GL (有限集 2) 实数)) [是Arithmetic 𝒢]
  定义体: ⟨𝒢.index_comap (mapGL (R := Int) Real) ▸ IsArithmetic.is_commensurable.1⟩

Depends on / 依赖: FiniteIndex
-/
instance IsArithmetic.finiteIndex_comap (𝒢 : Subgroup (GL (Fin 2) Real)) [IsArithmetic 𝒢] :
    (𝒢.comap (mapGL (R := Int) Real)).FiniteIndex :=
  ⟨𝒢.index_comap (mapGL (R := Int) Real) ▸ IsArithmetic.is_commensurable.1⟩

instance {Γ : Subgroup (GL (Fin 2) Real)} [h : Γ.IsArithmetic] : HasDetPlusMinusOne Γ := by
  rw [hasDetPlusMinusOne_iff_abs_det]
  intro g hg
  obtain ⟨n, hn, _, hgn⟩ := Subgroup.exists_pow_mem_of_relIndex_ne_zero
    Subgroup.IsArithmetic.is_commensurable.2 hg
  suffices |(g.det ^ n).val| = 1 by simpa [← abs_pow, abs_pow_eq_one _ (Nat.ne_zero_of_lt hn)]
  obtain ⟨t, ht⟩ := hgn.1
  have := congr_arg Matrix.GeneralLinearGroup.det ht.symm
  rw [Matrix.SpecialLinearGroup.det_mapGL]; rw [map_pow] at this
  simp [this]

/--
Instance `IsArithmetic.isFiniteRelIndexSL` / 实例 `IsArithmetic.isFiniteRelIndexSL`

English:
instance IsArithmetic.isFiniteRelIndexSL
  signature: (𝒢 : Subgroup (GL (Fin 2) Real)) [IsArithmetic 𝒢]
  body: ⟨IsArithmetic.is_commensurable.1⟩

中文:
实例 是Arithmetic.isFiniteRelIndexSL
  签名: (𝒢 : 子群 (GL (有限集 2) 实数)) [是Arithmetic 𝒢]
  定义体: ⟨IsArithmetic.is_commensurable.1⟩

Depends on / 依赖: IsArithmetic, IsArithmetic.is_commensurable, is_commensurable
-/
instance IsArithmetic.isFiniteRelIndexSL (𝒢 : Subgroup (GL (Fin 2) Real)) [IsArithmetic 𝒢] :
    𝒢.IsFiniteRelIndex 𝒮ℒ :=
  ⟨IsArithmetic.is_commensurable.1⟩

/--
Instance `IsArithmetic.inter` / 实例 `IsArithmetic.inter`

English:
instance IsArithmetic.inter
  signature: {Γ Γ'} [IsArithmetic Γ] [IsArithmetic Γ']
  body: by
  constructor
  constructor
  · apply relIndex_inf_ne_zero <;> exact IsArithmetic.is_commensurable.1
  · apply relIndex_ne_zero_trans (K := Γ) IsArithmetic.is_commensurable.2
    rw [relIndex_eq_one.mpr inf_le_left]
    simp

中文:
实例 是Arithmetic.inter
  签名: {Γ Γ'} [是Arithmetic Γ] [是Arithmetic Γ']
  定义体: by
  constructor
  constructor
  · apply relIndex_inf_ne_zero <;> exact IsArithmetic.is_commensurable.1
  · apply relIndex_ne_zero_trans (K := Γ) IsArithmetic.is_commensurable.2
    rw [relIndex_eq_one.mpr inf_le_left]
    simp

Depends on / 依赖: IsArithmetic, IsArithmetic.is_commensurable, inf_le_left, is_commensurable, relIndex_eq_one, relIndex_eq_one.mpr, relIndex_inf_ne_zero, relIndex_ne_zero_trans
-/
instance IsArithmetic.inter {Γ Γ'} [IsArithmetic Γ] [IsArithmetic Γ'] : IsArithmetic (Γ ⊓ Γ') := by
  constructor
  constructor
  · apply relIndex_inf_ne_zero <;> exact IsArithmetic.is_commensurable.1
  · apply relIndex_ne_zero_trans (K := Γ) IsArithmetic.is_commensurable.2
    rw [relIndex_eq_one.mpr inf_le_left]
    simp

end SL2Z_in_GL2R

end Subgroup

namespace Matrix.SpecialLinearGroup

/--
Instance `discreteSpecialLinearGroupIntRange` / 实例 `discreteSpecialLinearGroupIntRange`

English:
instance discreteSpecialLinearGroupIntRange
  signature: : DiscreteTopology (mapGL (n := n) (R := Int) Real).range
  body: (isEmbedding_mapGL Real.isClosedEmbedding_intCast.1).toHomeomorph.discreteTopology

中文:
实例 discreteSpecialLinearGroup整数Range
  签名: : 离散拓扑 (mapGL (n := n) (R := 整数) 实数).range
  定义体: (isEmbedding_mapGL Real.isClosedEmbedding_intCast.1).toHomeomorph.discreteTopology
-/
instance discreteSpecialLinearGroupIntRange : DiscreteTopology (mapGL (n := n) (R := Int) Real).range :=
  (isEmbedding_mapGL Real.isClosedEmbedding_intCast.1).toHomeomorph.discreteTopology

/--
Instance `discreteSpecialLinearGroupIntRangeSL` / 实例 `discreteSpecialLinearGroupIntRangeSL`

English:
instance discreteSpecialLinearGroupIntRangeSL
  signature: :
  body: by
  refine (Topology.IsEmbedding.toHomeomorph ?_).discreteTopology
  exact Real.isClosedEmbedding_intCast.specialLinearGroup_map.1

中文:
实例 discreteSpecialLinearGroup整数RangeSL
  签名: :
  定义体: by
  refine (Topology.IsEmbedding.toHomeomorph ?_).discreteTopology
  exact Real.isClosedEmbedding_intCast.specialLinearGroup_map.1

Depends on / 依赖: IsEmbedding, Real.isClosedEmbedding_intCast.specialLinearGroup_map, Topology, Topology.IsEmbedding.toHomeomorph, discreteTopology, isClosedEmbedding_intCast, specialLinearGroup_map, toHomeomorph
-/
instance discreteSpecialLinearGroupIntRangeSL :
    DiscreteTopology (SpecialLinearGroup.map (Int.castRingHom Real) (n := n)).range := by
  refine (Topology.IsEmbedding.toHomeomorph ?_).discreteTopology
  exact Real.isClosedEmbedding_intCast.specialLinearGroup_map.1

/--
lemma `isClosedEmbedding_mapGLInt` / 引理 `isClosedEmbedding_mapGLInt`

English:
lemma isClosedEmbedding_mapGLInt
  statement: Topology.IsClosedEmbedding (mapGL Real : SL n Int -> GL n Real)
  proof: isClosedEmbedding_mapGL Real.isClosedEmbedding_intCast

中文:
引理 isClosedEmbedding_mapGL整数
  结论: 拓扑.是闭嵌入 (mapGL 实数 : SL n 整数 -> GL n 实数)
  证明: isClosedEmbedding_mapGL Real.isClosedEmbedding_intCast

Depends on / 依赖: Real.isClosedEmbedding_intCast, isClosedEmbedding_intCast, isClosedEmbedding_mapGL
-/
lemma isClosedEmbedding_mapGLInt : Topology.IsClosedEmbedding (mapGL Real : SL n Int -> GL n Real) :=
  isClosedEmbedding_mapGL Real.isClosedEmbedding_intCast

end Matrix.SpecialLinearGroup

/--
Instance `Subgroup.IsArithmetic.discreteTopology` / 实例 `Subgroup.IsArithmetic.discreteTopology`

English:
instance Subgroup.IsArithmetic.discreteTopology
  signature: {𝒢 : Subgroup (GL (Fin 2) Real)} [IsArithmetic 𝒢]
  body: by
  rw [is_commensurable.discreteTopology_iff]
  infer_instance

中文:
实例 子群.是Arithmetic.discreteTopology
  签名: {𝒢 : 子群 (GL (有限集 2) 实数)} [是Arithmetic 𝒢]
  定义体: by
  rw [is_commensurable.discreteTopology_iff]
  infer_instance

Depends on / 依赖: discreteTopology_iff, infer_instance, is_commensurable, is_commensurable.discreteTopology_iff
-/
instance Subgroup.IsArithmetic.discreteTopology {𝒢 : Subgroup (GL (Fin 2) Real)} [IsArithmetic 𝒢] :
    DiscreteTopology 𝒢 := by
  rw [is_commensurable.discreteTopology_iff]
  infer_instance

section adjoinNeg

variable {R : Type*} [Ring R]

/--
Definition of `Subgroup.adjoinNegOne` / `Subgroup.adjoinNegOne` 的定义

English:
definition Subgroup.adjoinNegOne
  signature: (𝒢 : Subgroup (GL n R))
  body: {g | g in 𝒢 ∨ -g in 𝒢}
  mul_mem' ha hb := by
    rcases ha with ha | ha <;>
      rcases hb with hb | hb <;>
      · have := mul_mem ha hb
        aesop
  one_mem' := by simp
  inv_mem' ha := by
    rcases ha with (ha | ha) <;>
    · have := inv_mem ha
      aesop

中文:
定义 子群.adjoinNegOne
  签名: (𝒢 : 子群 (GL n R))
  定义体: {g | g in 𝒢 ∨ -g in 𝒢}
  mul_mem' ha hb := by
    rcases ha with ha | ha <;>
      rcases hb with hb | hb <;>
      · have := mul_mem ha hb
        aesop
  one_mem' := by simp
  inv_mem' ha := by
    rcases ha with (ha | ha) <;>
    · have := inv_mem ha
      aesop
-/
def Subgroup.adjoinNegOne (𝒢 : Subgroup (GL n R)) : Subgroup (GL n R) where
  carrier := {g | g in 𝒢 ∨ -g in 𝒢}
  mul_mem' ha hb := by
    rcases ha with ha | ha <;>
      rcases hb with hb | hb <;>
      · have := mul_mem ha hb
        aesop
  one_mem' := by simp
  inv_mem' ha := by
    rcases ha with (ha | ha) <;>
    · have := inv_mem ha
      aesop

/--
lemma `Subgroup.mem_adjoinNegOne_iff` / 引理 `Subgroup.mem_adjoinNegOne_iff`

English:
lemma Subgroup.mem_adjoinNegOne_iff
  given: {𝒢 : Subgroup (GL n R)} {g : GL n R}
  proof: Iff.rfl

中文:
引理 子群.mem_adjoinNegOne_iff
  条件: {𝒢 : 子群 (GL n R)} {g : GL n R}
  证明: Iff.rfl
-/
@[simp] lemma Subgroup.mem_adjoinNegOne_iff {𝒢 : Subgroup (GL n R)} {g : GL n R} :
    g in 𝒢.adjoinNegOne ↔ g in 𝒢 ∨ -g in 𝒢 :=
  Iff.rfl

/--
lemma `Subgroup.le_adjoinNegOne` / 引理 `Subgroup.le_adjoinNegOne`

English:
lemma Subgroup.le_adjoinNegOne
  given: (𝒢 : Subgroup (GL n R))
  statement: 𝒢 <= 𝒢.adjoinNegOne
  proof: fun _ hg => .inl hg

中文:
引理 子群.le_adjoinNegOne
  条件: (𝒢 : 子群 (GL n R))
  结论: 𝒢 <= 𝒢.adjoinNegOne
  证明: fun _ hg => .inl hg
-/
lemma Subgroup.le_adjoinNegOne (𝒢 : Subgroup (GL n R)) : 𝒢 <= 𝒢.adjoinNegOne :=
  fun _ hg => .inl hg

/--
lemma `Subgroup.negOne_mem_adjoinNegOne` / 引理 `Subgroup.negOne_mem_adjoinNegOne`

English:
lemma Subgroup.negOne_mem_adjoinNegOne
  given: (𝒢 : Subgroup (GL n R))
  statement: -1 in 𝒢.adjoinNegOne
  proof: by simp

中文:
引理 子群.negOne_mem_adjoinNegOne
  条件: (𝒢 : 子群 (GL n R))
  结论: -1 in 𝒢.adjoinNegOne
  证明: by simp
-/
lemma Subgroup.negOne_mem_adjoinNegOne (𝒢 : Subgroup (GL n R)) : -1 in 𝒢.adjoinNegOne := by simp

/--
lemma `Subgroup.adjoinNegOne_eq_self_iff` / 引理 `Subgroup.adjoinNegOne_eq_self_iff`

English:
lemma Subgroup.adjoinNegOne_eq_self_iff
  given: {𝒢 : Subgroup (GL n R)}
  proof: ⟨fun h => h ▸ negOne_mem_adjoinNegOne 𝒢, fun hG => 𝒢.le_adjoinNegOne.antisymm'
    fun g hg => hg.elim id (fun h => by simpa using mul_mem hG h)⟩

中文:
引理 子群.adjoinNegOne_eq_self_iff
  条件: {𝒢 : 子群 (GL n R)}
  证明: ⟨fun h => h ▸ negOne_mem_adjoinNegOne 𝒢, fun hG => 𝒢.le_adjoinNegOne.antisymm'
    fun g hg => hg.elim id (fun h => by simpa using mul_mem hG h)⟩
-/
@[simp] lemma Subgroup.adjoinNegOne_eq_self_iff {𝒢 : Subgroup (GL n R)} :
    𝒢.adjoinNegOne = 𝒢 ↔ -1 in 𝒢 :=
  ⟨fun h => h ▸ negOne_mem_adjoinNegOne 𝒢, fun hG => 𝒢.le_adjoinNegOne.antisymm'
    fun g hg => hg.elim id (fun h => by simpa using mul_mem hG h)⟩

/--
lemma `Subgroup.relindex_adjoinNegOne_eq_two` / 引理 `Subgroup.relindex_adjoinNegOne_eq_two`

English:
lemma Subgroup.relindex_adjoinNegOne_eq_two
  given: {𝒢 : Subgroup (GL n R)} (h𝒢 : -1 ∉ 𝒢)
  proof: by
  refine relIndex_eq_two_iff_exists_notMem_and.mpr ⟨_, 𝒢.negOne_mem_adjoinNegOne, h𝒢, ?_⟩
  simp [mem_adjoinNegOne_iff, or_comm]

中文:
引理 子群.relindex_adjoinNegOne_eq_two
  条件: {𝒢 : 子群 (GL n R)} (h𝒢 : -1 ∉ 𝒢)
  证明: by
  refine relIndex_eq_two_iff_exists_notMem_and.mpr ⟨_, 𝒢.negOne_mem_adjoinNegOne, h𝒢, ?_⟩
  simp [mem_adjoinNegOne_iff, or_comm]

Depends on / 依赖: mem_adjoinNegOne_iff, negOne_mem_adjoinNegOne, or_comm, relIndex_eq_two_iff_exists_notMem_and, relIndex_eq_two_iff_exists_notMem_and.mpr
-/
lemma Subgroup.relindex_adjoinNegOne_eq_two {𝒢 : Subgroup (GL n R)} (h𝒢 : -1 ∉ 𝒢) :
    𝒢.relIndex 𝒢.adjoinNegOne = 2 := by
  refine relIndex_eq_two_iff_exists_notMem_and.mpr ⟨_, 𝒢.negOne_mem_adjoinNegOne, h𝒢, ?_⟩
  simp [mem_adjoinNegOne_iff, or_comm]

/--
lemma `Subgroup.relIndex_adjoinNegOne_ne_zero` / 引理 `Subgroup.relIndex_adjoinNegOne_ne_zero`

English:
lemma Subgroup.relIndex_adjoinNegOne_ne_zero
  given: (𝒢 : Subgroup (GL n R))
  proof: by
  by_cases hG : -1 in 𝒢
  · simp [adjoinNegOne_eq_self_iff.mpr hG]
  · simp [𝒢.relindex_adjoinNegOne_eq_two hG]

中文:
引理 子群.relIndex_adjoinNegOne_ne_zero
  条件: (𝒢 : 子群 (GL n R))
  证明: by
  by_cases hG : -1 in 𝒢
  · simp [adjoinNegOne_eq_self_iff.mpr hG]
  · simp [𝒢.relindex_adjoinNegOne_eq_two hG]

Depends on / 依赖: adjoinNegOne_eq_self_iff, adjoinNegOne_eq_self_iff.mpr, relindex_adjoinNegOne_eq_two
-/
lemma Subgroup.relIndex_adjoinNegOne_ne_zero (𝒢 : Subgroup (GL n R)) :
    𝒢.relIndex 𝒢.adjoinNegOne != 0 := by
  by_cases hG : -1 in 𝒢
  · simp [adjoinNegOne_eq_self_iff.mpr hG]
  · simp [𝒢.relindex_adjoinNegOne_eq_two hG]

instance (𝒢 : Subgroup (GL n R)) : Subgroup.IsFiniteRelIndex 𝒢 𝒢.adjoinNegOne :=
  ⟨𝒢.relIndex_adjoinNegOne_ne_zero⟩

/--
lemma `Subgroup.commensurable_adjoinNegOne_self` / 引理 `Subgroup.commensurable_adjoinNegOne_self`

English:
lemma Subgroup.commensurable_adjoinNegOne_self
  given: (𝒢 : Subgroup (GL n R))
  proof: ⟨by simp [Subgroup.relIndex_eq_one.mpr 𝒢.le_adjoinNegOne], 𝒢.relIndex_adjoinNegOne_ne_zero⟩

中文:
引理 子群.commensurable_adjoinNegOne_self
  条件: (𝒢 : 子群 (GL n R))
  证明: ⟨by simp [Subgroup.relIndex_eq_one.mpr 𝒢.le_adjoinNegOne], 𝒢.relIndex_adjoinNegOne_ne_zero⟩

Depends on / 依赖: Subgroup, Subgroup.relIndex_eq_one.mpr, le_adjoinNegOne, relIndex_adjoinNegOne_ne_zero, relIndex_eq_one
-/
lemma Subgroup.commensurable_adjoinNegOne_self (𝒢 : Subgroup (GL n R)) :
    Commensurable 𝒢.adjoinNegOne 𝒢 :=
  ⟨by simp [Subgroup.relIndex_eq_one.mpr 𝒢.le_adjoinNegOne], 𝒢.relIndex_adjoinNegOne_ne_zero⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [TopologicalSpace
  signature: R] [IsTopologicalRing R] [T2Space R]
  body: by
  rwa [𝒢.commensurable_adjoinNegOne_self.discreteTopology_iff]

中文:
实例 [拓扑空间
  签名: R] [是拓扑环 R] [T2空间 R]
  定义体: by
  rwa [𝒢.commensurable_adjoinNegOne_self.discreteTopology_iff]

Depends on / 依赖: commensurable_adjoinNegOne_self, commensurable_adjoinNegOne_self.discreteTopology_iff, discreteTopology_iff
-/
instance [TopologicalSpace R] [IsTopologicalRing R] [T2Space R]
    (𝒢 : Subgroup (GL n R)) [DiscreteTopology 𝒢] :
    DiscreteTopology 𝒢.adjoinNegOne := by
  rwa [𝒢.commensurable_adjoinNegOne_self.discreteTopology_iff]

section CommRing

variable {R : Type*} [CommRing R]

/--
lemma `Subgroup.hasDetPlusMinusOne_adjoinNegOne_iff` / 引理 `Subgroup.hasDetPlusMinusOne_adjoinNegOne_iff`

English:
lemma Subgroup.hasDetPlusMinusOne_adjoinNegOne_iff
  given: {𝒢 : Subgroup (GL n R)}
  proof: by
  refine ⟨fun _ => ⟨fun {g} hg => HasDetPlusMinusOne.det_eq (𝒢.le_adjoinNegOne hg)⟩, fun _ => ⟨?_⟩⟩
  rintro g (hg | hg)
  · exact HasDetPlusMinusOne.det_eq hg
  · by_cases hn : Even (Fintype.card n)
    · convert! HasDetPlusMinusOne.det_eq hg using 1 <;>
        simp [Units.ext_iff, det_neg, hn]
    · convert! (HasDetPlusMinusOne.det_eq hg).symm using 1 <;>
        simp [Units.ext_iff, det_neg, Nat.not_even_iff_odd.mp hn, neg_eq_iff_eq_neg]

中文:
引理 子群.hasDetPlusMinusOne_adjoinNegOne_iff
  条件: {𝒢 : 子群 (GL n R)}
  证明: by
  refine ⟨fun _ => ⟨fun {g} hg => HasDetPlusMinusOne.det_eq (𝒢.le_adjoinNegOne hg)⟩, fun _ => ⟨?_⟩⟩
  rintro g (hg | hg)
  · exact HasDetPlusMinusOne.det_eq hg
  · by_cases hn : Even (Fintype.card n)
    · convert! HasDetPlusMinusOne.det_eq hg using 1 <;>
        simp [Units.ext_iff, det_neg, hn]
    · convert! (HasDetPlusMinusOne.det_eq hg).symm using 1 <;>
        simp [Units.ext_iff, det_neg, Nat.not_even_iff_odd.mp hn, neg_eq_iff_eq_neg]
-/
@[simp] lemma Subgroup.hasDetPlusMinusOne_adjoinNegOne_iff {𝒢 : Subgroup (GL n R)} :
    𝒢.adjoinNegOne.HasDetPlusMinusOne ↔ 𝒢.HasDetPlusMinusOne := by
  refine ⟨fun _ => ⟨fun {g} hg => HasDetPlusMinusOne.det_eq (𝒢.le_adjoinNegOne hg)⟩, fun _ => ⟨?_⟩⟩
  rintro g (hg | hg)
  · exact HasDetPlusMinusOne.det_eq hg
  · by_cases hn : Even (Fintype.card n)
    · convert! HasDetPlusMinusOne.det_eq hg using 1 <;>
        simp [Units.ext_iff, det_neg, hn]
    · convert! (HasDetPlusMinusOne.det_eq hg).symm using 1 <;>
        simp [Units.ext_iff, det_neg, Nat.not_even_iff_odd.mp hn, neg_eq_iff_eq_neg]

/--
lemma `Subgroup.hasDetOne_adjoinNegOne_iff` / 引理 `Subgroup.hasDetOne_adjoinNegOne_iff`

English:
lemma Subgroup.hasDetOne_adjoinNegOne_iff
  given: {𝒢 : Subgroup (GL n R)} (hn : Even (Fintype.card n))
  proof: by
  refine ⟨fun _ => ⟨fun {g} hg => HasDetOne.det_eq (𝒢.le_adjoinNegOne hg)⟩, fun _ => ⟨?_⟩⟩
  rintro g (hg | hg)
  · exact HasDetOne.det_eq hg
  · simpa [Units.ext_iff, det_neg, hn] using HasDetOne.det_eq hg

中文:
引理 子群.hasDetOne_adjoinNegOne_iff
  条件: {𝒢 : 子群 (GL n R)} (hn : Even (有限类型.card n))
  证明: by
  refine ⟨fun _ => ⟨fun {g} hg => HasDetOne.det_eq (𝒢.le_adjoinNegOne hg)⟩, fun _ => ⟨?_⟩⟩
  rintro g (hg | hg)
  · exact HasDetOne.det_eq hg
  · simpa [Units.ext_iff, det_neg, hn] using HasDetOne.det_eq hg

Depends on / 依赖: HasDetOne, HasDetOne.det_eq, Units.ext_iff, det_eq, det_neg, ext_iff, le_adjoinNegOne
-/
lemma Subgroup.hasDetOne_adjoinNegOne_iff {𝒢 : Subgroup (GL n R)} (hn : Even (Fintype.card n)) :
    𝒢.adjoinNegOne.HasDetOne ↔ 𝒢.HasDetOne := by
  refine ⟨fun _ => ⟨fun {g} hg => HasDetOne.det_eq (𝒢.le_adjoinNegOne hg)⟩, fun _ => ⟨?_⟩⟩
  rintro g (hg | hg)
  · exact HasDetOne.det_eq hg
  · simpa [Units.ext_iff, det_neg, hn] using HasDetOne.det_eq hg

instance {𝒢 : Subgroup (GL n R)} [𝒢.HasDetPlusMinusOne] :
    𝒢.adjoinNegOne.HasDetPlusMinusOne :=
  Subgroup.hasDetPlusMinusOne_adjoinNegOne_iff.2 ‹_›

instance {𝒢 : Subgroup (GL n R)} [𝒢.HasDetOne] [Fact (Even (Fintype.card n))] :
    𝒢.adjoinNegOne.HasDetOne :=
  (Subgroup.hasDetOne_adjoinNegOne_iff Fact.out).2 ‹_›

end CommRing

/--
Instance `Subgroup.instIsArithmeticAdjoinNegOne` / 实例 `Subgroup.instIsArithmeticAdjoinNegOne`

English:
instance Subgroup.instIsArithmeticAdjoinNegOne
  signature: {𝒢 : Subgroup (GL (Fin 2) Real)} [𝒢.IsArithmetic]
  body: ⟨(𝒢.commensurable_adjoinNegOne_self).trans IsArithmetic.is_commensurable⟩

中文:
实例 子群.instIsArithmeticAdjoinNegOne
  签名: {𝒢 : 子群 (GL (有限集 2) 实数)} [𝒢.是Arithmetic]
  定义体: ⟨(𝒢.commensurable_adjoinNegOne_self).trans IsArithmetic.is_commensurable⟩

Depends on / 依赖: IsArithmetic, IsArithmetic.is_commensurable, commensurable_adjoinNegOne_self, is_commensurable
-/
instance Subgroup.instIsArithmeticAdjoinNegOne {𝒢 : Subgroup (GL (Fin 2) Real)} [𝒢.IsArithmetic] :
    𝒢.adjoinNegOne.IsArithmetic :=
  ⟨(𝒢.commensurable_adjoinNegOne_self).trans IsArithmetic.is_commensurable⟩

end adjoinNeg
