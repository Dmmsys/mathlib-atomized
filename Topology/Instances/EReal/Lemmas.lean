/-
Copyright (c) 2021 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
module

public import Mathlib.Data.EReal.Inv
public import Mathlib.Topology.Semicontinuity.Basic

/-!
# Topological structure on `EReal`

We prove basic properties of the topology on `EReal`.

## Main results

* `Real.toEReal : ℝ → EReal` is an open embedding
* `ENNReal.toEReal : ℝ≥0∞ → EReal` is a closed embedding
* The addition on `EReal` is continuous except at `(⊥, ⊤)` and at `(⊤, ⊥)`.
* Negation is a homeomorphism on `EReal`.

## Implementation

Most proofs are adapted from the corresponding proofs on `ℝ≥0∞`.
-/

@[expose] public section

noncomputable section

open Set Filter Metric TopologicalSpace Topology
open scoped ENNReal

variable {α : Type*} [TopologicalSpace α]

namespace EReal


/--
theorem `isEmbedding_coe` / 定理 `isEmbedding_coe`

English:
theorem isEmbedding_coe
  statement: IsEmbedding ((↑) : Real -> EReal)
  proof: coe_strictMono.isEmbedding_of_ordConnected by rw [range_coe_eq_Ioo]; exact ordConnected_Ioo

中文:
定理 isEmbedding_coe
  结论: IsEmbedding ((↑) : 实数 -> E实数)
  证明: coe_strictMono.isEmbedding_of_ordConnected by rw [range_coe_eq_Ioo]; exact ordConnected_Ioo

Depends on / 依赖: coe_strictMono, coe_strictMono.isEmbedding_of_ordConnected, isEmbedding_of_ordConnected, ordConnected_Ioo, range_coe_eq_Ioo
-/
theorem isEmbedding_coe : IsEmbedding ((↑) : Real -> EReal) :=
coe_strictMono.isEmbedding_of_ordConnected by rw [range_coe_eq_Ioo]; exact ordConnected_Ioo

/--
theorem `isOpenEmbedding_coe` / 定理 `isOpenEmbedding_coe`

English:
theorem isOpenEmbedding_coe
  statement: IsOpenEmbedding ((↑) : Real -> EReal)
  proof: ⟨isEmbedding_coe, by simp only [range_coe_eq_Ioo, isOpen_Ioo]⟩

@[norm_cast]

中文:
定理 isOpenEmbedding_coe
  结论: IsOpenEmbedding ((↑) : 实数 -> E实数)
  证明: ⟨isEmbedding_coe, by simp only [range_coe_eq_Ioo, isOpen_Ioo]⟩

@[norm_cast]

Depends on / 依赖: isEmbedding_coe, isOpen_Ioo, range_coe_eq_Ioo
-/
theorem isOpenEmbedding_coe : IsOpenEmbedding ((↑) : Real -> EReal) :=
  ⟨isEmbedding_coe, by simp only [range_coe_eq_Ioo, isOpen_Ioo]⟩

@[norm_cast]
/--
theorem `tendsto_coe` / 定理 `tendsto_coe`

English:
theorem tendsto_coe
  given: {α : Type*} {f : Filter α} {m : α -> Real} {a : Real}
  proof: isEmbedding_coe.tendsto_nhds_iff.symm

中文:
定理 tendsto_coe
  条件: {α : 类型} {f : Filter α} {m : α -> 实数} {a : 实数}
  证明: isEmbedding_coe.tendsto_nhds_iff.symm

Depends on / 依赖: isEmbedding_coe, isEmbedding_coe.tendsto_nhds_iff.symm, tendsto_nhds_iff
-/
theorem tendsto_coe {α : Type*} {f : Filter α} {m : α -> Real} {a : Real} :
    Tendsto (fun a => (m a : EReal)) f (𝓝 ↑a) ↔ Tendsto m f (𝓝 a) :=
  isEmbedding_coe.tendsto_nhds_iff.symm

/--
theorem `_root_.continuous_coe_real_ereal` / 定理 `_root_.continuous_coe_real_ereal`

English:
theorem _root_.continuous_coe_real_ereal
  statement: Continuous ((↑) : Real -> EReal)
  proof: isEmbedding_coe.continuous

中文:
定理 _root_.continuous_coe_real_ereal
  结论: Continuous ((↑) : 实数 -> E实数)
  证明: isEmbedding_coe.continuous

Depends on / 依赖: continuous, isEmbedding_coe, isEmbedding_coe.continuous
-/
theorem _root_.continuous_coe_real_ereal : Continuous ((↑) : Real -> EReal) :=
  isEmbedding_coe.continuous

/--
theorem `continuous_coe_iff` / 定理 `continuous_coe_iff`

English:
theorem continuous_coe_iff
  given: {f : α -> Real}
  statement: (Continuous fun a => (f a : EReal)) ↔ Continuous f
  proof: isEmbedding_coe.continuous_iff.symm

中文:
定理 continuous_coe_iff
  条件: {f : α -> 实数}
  结论: (Continuous fun a => (f a : E实数)) ↔ Continuous f
  证明: isEmbedding_coe.continuous_iff.symm

Depends on / 依赖: continuous_iff, isEmbedding_coe, isEmbedding_coe.continuous_iff.symm
-/
theorem continuous_coe_iff {f : α -> Real} : (Continuous fun a => (f a : EReal)) ↔ Continuous f :=
  isEmbedding_coe.continuous_iff.symm

/--
theorem `nhds_coe` / 定理 `nhds_coe`

English:
theorem nhds_coe
  given: {r : Real}
  statement: 𝓝 (r : EReal) = (𝓝 r).map (↑)
  proof: (isOpenEmbedding_coe.map_nhds_eq r).symm

中文:
定理 nhds_coe
  条件: {r : 实数}
  结论: 𝓝 (r : E实数) = (𝓝 r).map (↑)
  证明: (isOpenEmbedding_coe.map_nhds_eq r).symm

Depends on / 依赖: isOpenEmbedding_coe, isOpenEmbedding_coe.map_nhds_eq, map_nhds_eq
-/
theorem nhds_coe {r : Real} : 𝓝 (r : EReal) = (𝓝 r).map (↑) :=
  (isOpenEmbedding_coe.map_nhds_eq r).symm

/--
theorem `nhds_coe_coe` / 定理 `nhds_coe_coe`

English:
theorem nhds_coe_coe
  given: {r p : Real}
  proof: ((isOpenEmbedding_coe.prodMap isOpenEmbedding_coe).map_nhds_eq (r, p)).symm

中文:
定理 nhds_coe_coe
  条件: {r p : 实数}
  证明: ((isOpenEmbedding_coe.prodMap isOpenEmbedding_coe).map_nhds_eq (r, p)).symm

Depends on / 依赖: isOpenEmbedding_coe, isOpenEmbedding_coe.prodMap, map_nhds_eq, prodMap
-/
theorem nhds_coe_coe {r p : Real} :
    𝓝 ((r : EReal), (p : EReal)) = (𝓝 (r, p)).map fun p : Real × Real => (↑p.1, ↑p.2) :=
  ((isOpenEmbedding_coe.prodMap isOpenEmbedding_coe).map_nhds_eq (r, p)).symm

/--
theorem `tendsto_toReal` / 定理 `tendsto_toReal`

English:
theorem tendsto_toReal
  given: {a : EReal} (ha : a != ⊤) (h'a : a != ⊥)
  proof: by
  lift a to Real using ⟨ha, h'a⟩
  rw [nhds_coe]; rw [tendsto_map'_iff]
  exact tendsto_id

中文:
定理 tendsto_toReal
  条件: {a : E实数} (ha : a != ⊤) (h'a : a != ⊥)
  证明: by
  lift a to Real using ⟨ha, h'a⟩
  rw [nhds_coe]; rw [tendsto_map'_iff]
  exact tendsto_id

Depends on / 依赖: _iff, nhds_coe, tendsto_id, tendsto_map
-/
theorem tendsto_toReal {a : EReal} (ha : a != ⊤) (h'a : a != ⊥) :
    Tendsto EReal.toReal (𝓝 a) (𝓝 a.toReal) := by
  lift a to Real using ⟨ha, h'a⟩
  rw [nhds_coe]; rw [tendsto_map'_iff]
  exact tendsto_id

/--
theorem `continuousOn_toReal` / 定理 `continuousOn_toReal`

English:
theorem continuousOn_toReal
  statement: ContinuousOn EReal.toReal ({⊥, ⊤}ᶜ : Set EReal)
  proof: fun _a ha =>
  ContinuousAt.continuousWithinAt (tendsto_toReal (mt Or.inr ha) (mt Or.inl ha))

中文:
定理 continuousOn_toReal
  结论: ContinuousOn E实数.to实数 ({⊥, ⊤}ᶜ : Set E实数)
  证明: fun _a ha =>
  ContinuousAt.continuousWithinAt (tendsto_toReal (mt Or.inr ha) (mt Or.inl ha))
-/
theorem continuousOn_toReal : ContinuousOn EReal.toReal ({⊥, ⊤}ᶜ : Set EReal) := fun _a ha =>
  ContinuousAt.continuousWithinAt (tendsto_toReal (mt Or.inr ha) (mt Or.inl ha))

/--
Definition of `neBotTopHomeomorphReal` / `neBotTopHomeomorphReal` 的定义

English:
definition neBotTopHomeomorphReal
  signature: : ({⊥, ⊤}ᶜ : Set EReal) ≃ₜ Real where
  body: neTopBotEquivReal
  continuous_toFun := continuousOn_iff_continuous_domRestrict.1 continuousOn_toReal
  continuous_invFun := continuous_coe_real_ereal.subtype_mk _

中文:
定义 neBotTopHomeomorphReal
  签名: : ({⊥, ⊤}ᶜ : Set E实数) ≃ₜ 实数 where
  定义体: neTopBotEquivReal
  continuous_toFun := continuousOn_iff_continuous_domRestrict.1 continuousOn_toReal
  continuous_invFun := continuous_coe_real_ereal.subtype_mk _

Depends on / 依赖: neTopBotEquivReal
-/
def neBotTopHomeomorphReal : ({⊥, ⊤}ᶜ : Set EReal) ≃ₜ Real where
  toEquiv := neTopBotEquivReal
  continuous_toFun := continuousOn_iff_continuous_domRestrict.1 continuousOn_toReal
  continuous_invFun := continuous_coe_real_ereal.subtype_mk _


/--
theorem `isEmbedding_coe_ennreal` / 定理 `isEmbedding_coe_ennreal`

English:
theorem isEmbedding_coe_ennreal
  statement: IsEmbedding ((↑) : Real>=0∞ -> EReal)
  proof: coe_ennreal_strictMono.isEmbedding_of_ordConnected by
    rw [range_coe_ennreal]; exact ordConnected_Ici

中文:
定理 isEmbedding_coe_ennreal
  结论: IsEmbedding ((↑) : 实数>=0∞ -> E实数)
  证明: coe_ennreal_strictMono.isEmbedding_of_ordConnected by
    rw [range_coe_ennreal]; exact ordConnected_Ici

Depends on / 依赖: coe_ennreal_strictMono, coe_ennreal_strictMono.isEmbedding_of_ordConnected, isEmbedding_of_ordConnected, ordConnected_Ici, range_coe_ennreal
-/
theorem isEmbedding_coe_ennreal : IsEmbedding ((↑) : Real>=0∞ -> EReal) :=
coe_ennreal_strictMono.isEmbedding_of_ordConnected by
    rw [range_coe_ennreal]; exact ordConnected_Ici

/--
theorem `isClosedEmbedding_coe_ennreal` / 定理 `isClosedEmbedding_coe_ennreal`

English:
theorem isClosedEmbedding_coe_ennreal
  statement: IsClosedEmbedding ((↑) : Real>=0∞ -> EReal)
  proof: ⟨isEmbedding_coe_ennreal, by rw [range_coe_ennreal]; exact isClosed_Ici⟩

@[norm_cast]

中文:
定理 isClosedEmbedding_coe_ennreal
  结论: IsClosedEmbedding ((↑) : 实数>=0∞ -> E实数)
  证明: ⟨isEmbedding_coe_ennreal, by rw [range_coe_ennreal]; exact isClosed_Ici⟩

@[norm_cast]

Depends on / 依赖: isClosed_Ici, isEmbedding_coe_ennreal, range_coe_ennreal
-/
theorem isClosedEmbedding_coe_ennreal : IsClosedEmbedding ((↑) : Real>=0∞ -> EReal) :=
  ⟨isEmbedding_coe_ennreal, by rw [range_coe_ennreal]; exact isClosed_Ici⟩

@[norm_cast]
/--
theorem `tendsto_coe_ennreal` / 定理 `tendsto_coe_ennreal`

English:
theorem tendsto_coe_ennreal
  given: {α : Type*} {f : Filter α} {m : α -> Real>=0∞} {a : Real>=0∞}
  proof: isEmbedding_coe_ennreal.tendsto_nhds_iff.symm

中文:
定理 tendsto_coe_ennreal
  条件: {α : 类型} {f : Filter α} {m : α -> 实数>=0∞} {a : 实数>=0∞}
  证明: isEmbedding_coe_ennreal.tendsto_nhds_iff.symm

Depends on / 依赖: isEmbedding_coe_ennreal, isEmbedding_coe_ennreal.tendsto_nhds_iff.symm, tendsto_nhds_iff
-/
theorem tendsto_coe_ennreal {α : Type*} {f : Filter α} {m : α -> Real>=0∞} {a : Real>=0∞} :
    Tendsto (fun a => (m a : EReal)) f (𝓝 ↑a) ↔ Tendsto m f (𝓝 a) :=
  isEmbedding_coe_ennreal.tendsto_nhds_iff.symm

/--
theorem `_root_.continuous_coe_ennreal_ereal` / 定理 `_root_.continuous_coe_ennreal_ereal`

English:
theorem _root_.continuous_coe_ennreal_ereal
  statement: Continuous ((↑) : Real>=0∞ -> EReal)
  proof: isEmbedding_coe_ennreal.continuous

中文:
定理 _root_.continuous_coe_ennreal_ereal
  结论: Continuous ((↑) : 实数>=0∞ -> E实数)
  证明: isEmbedding_coe_ennreal.continuous

Depends on / 依赖: continuous, isEmbedding_coe_ennreal, isEmbedding_coe_ennreal.continuous
-/
theorem _root_.continuous_coe_ennreal_ereal : Continuous ((↑) : Real>=0∞ -> EReal) :=
  isEmbedding_coe_ennreal.continuous

/--
theorem `continuous_coe_ennreal_iff` / 定理 `continuous_coe_ennreal_iff`

English:
theorem continuous_coe_ennreal_iff
  given: {f : α -> Real>=0∞}
  proof: isEmbedding_coe_ennreal.continuous_iff.symm

中文:
定理 continuous_coe_ennreal_iff
  条件: {f : α -> 实数>=0∞}
  证明: isEmbedding_coe_ennreal.continuous_iff.symm

Depends on / 依赖: continuous_iff, isEmbedding_coe_ennreal, isEmbedding_coe_ennreal.continuous_iff.symm
-/
theorem continuous_coe_ennreal_iff {f : α -> Real>=0∞} :
    (Continuous fun a => (f a : EReal)) ↔ Continuous f :=
  isEmbedding_coe_ennreal.continuous_iff.symm


/--
theorem `nhds_top` / 定理 `nhds_top`

English:
theorem nhds_top
  statement: 𝓝 (⊤ : EReal) = ⨅ (a) (_ : a != ⊤), 𝓟 (Ioi a)
  proof: nhds_top_order.trans by simp only [lt_top_iff_ne_top]

nonrec theorem nhds_top_basis : (𝓝 (⊤ : EReal)).HasBasis (fun _ : Real => True) (Ioi ·) := by
  refine (nhds_top_basis (α := EReal)).to_hasBasis (fun x hx => ?_)
    fun _ _ => ⟨_, coe_lt_top _, Subset.rfl⟩
  rcases exists_rat_btwn_of_lt hx with

中文:
定理 nhds_top
  结论: 𝓝 (⊤ : E实数) = ⨅ (a) (_ : a != ⊤), 𝓟 (Ioi a)
  证明: nhds_top_order.trans by simp only [lt_top_iff_ne_top]

nonrec theorem nhds_top_basis : (𝓝 (⊤ : EReal)).HasBasis (fun _ : Real => True) (Ioi ·) := by
  refine (nhds_top_basis (α := EReal)).to_hasBasis (fun x hx => ?_)
    fun _ _ => ⟨_, coe_lt_top _, Subset.rfl⟩
  rcases exists_rat_btwn_of_lt hx with

Depends on / 依赖: lt_top_iff_ne_top, nhds_top_order, nhds_top_order.trans
-/
theorem nhds_top : 𝓝 (⊤ : EReal) = ⨅ (a) (_ : a != ⊤), 𝓟 (Ioi a) :=
nhds_top_order.trans by simp only [lt_top_iff_ne_top]

nonrec theorem nhds_top_basis : (𝓝 (⊤ : EReal)).HasBasis (fun _ : Real => True) (Ioi ·) := by
  refine (nhds_top_basis (α := EReal)).to_hasBasis (fun x hx => ?_)
    fun _ _ => ⟨_, coe_lt_top _, Subset.rfl⟩
  rcases exists_rat_btwn_of_lt hx with ⟨y, hxy, -⟩
  exact ⟨_, trivial, Ioi_subset_Ioi hxy.le⟩

/--
theorem `nhds_top'` / 定理 `nhds_top'`

English:
theorem nhds_top'
  statement: 𝓝 (⊤ : EReal) = ⨅ a : Real, 𝓟 (Ioi ↑a)
  proof: nhds_top_basis.eq_iInf

中文:
定理 nhds_top'
  结论: 𝓝 (⊤ : E实数) = ⨅ a : 实数, 𝓟 (Ioi ↑a)
  证明: nhds_top_basis.eq_iInf

Depends on / 依赖: eq_iInf, nhds_top_basis, nhds_top_basis.eq_iInf
-/
theorem nhds_top' : 𝓝 (⊤ : EReal) = ⨅ a : Real, 𝓟 (Ioi ↑a) := nhds_top_basis.eq_iInf

/--
theorem `mem_nhds_top_iff` / 定理 `mem_nhds_top_iff`

English:
theorem mem_nhds_top_iff
  given: {s : Set EReal}
  statement: s in 𝓝 (⊤ : EReal) ↔ exists y : Real, Ioi (y : EReal) subseteq s
  proof: nhds_top_basis.mem_iff.trans by simp only [true_and]

中文:
定理 mem_nhds_top_iff
  条件: {s : Set E实数}
  结论: s in 𝓝 (⊤ : E实数) ↔ 存在 y : 实数, Ioi (y : E实数) subseteq s
  证明: nhds_top_basis.mem_iff.trans by simp only [true_and]

Depends on / 依赖: mem_iff, nhds_top_basis, nhds_top_basis.mem_iff.trans, true_and
-/
theorem mem_nhds_top_iff {s : Set EReal} : s in 𝓝 (⊤ : EReal) ↔ exists y : Real, Ioi (y : EReal) subseteq s :=
nhds_top_basis.mem_iff.trans by simp only [true_and]

/--
theorem `tendsto_nhds_top_iff_real` / 定理 `tendsto_nhds_top_iff_real`

English:
theorem tendsto_nhds_top_iff_real
  given: {α : Type*} {m : α -> EReal} {f : Filter α}
  proof: nhds_top_basis.tendsto_right_iff.trans by simp only [true_implies, mem_Ioi]

中文:
定理 tendsto_nhds_top_iff_real
  条件: {α : 类型} {m : α -> E实数} {f : Filter α}
  证明: nhds_top_basis.tendsto_right_iff.trans by simp only [true_implies, mem_Ioi]

Depends on / 依赖: mem_Ioi, nhds_top_basis, nhds_top_basis.tendsto_right_iff.trans, tendsto_right_iff, true_implies
-/
theorem tendsto_nhds_top_iff_real {α : Type*} {m : α -> EReal} {f : Filter α} :
    Tendsto m f (𝓝 ⊤) ↔ forall x : Real, forallᶠ a in f, ↑x < m a :=
nhds_top_basis.tendsto_right_iff.trans by simp only [true_implies, mem_Ioi]

/--
theorem `nhds_bot` / 定理 `nhds_bot`

English:
theorem nhds_bot
  statement: 𝓝 (⊥ : EReal) = ⨅ (a) (_ : a != ⊥), 𝓟 (Iio a)
  proof: nhds_bot_order.trans by simp only [bot_lt_iff_ne_bot]

中文:
定理 nhds_bot
  结论: 𝓝 (⊥ : E实数) = ⨅ (a) (_ : a != ⊥), 𝓟 (Iio a)
  证明: nhds_bot_order.trans by simp only [bot_lt_iff_ne_bot]

Depends on / 依赖: bot_lt_iff_ne_bot, nhds_bot_order, nhds_bot_order.trans
-/
theorem nhds_bot : 𝓝 (⊥ : EReal) = ⨅ (a) (_ : a != ⊥), 𝓟 (Iio a) :=
nhds_bot_order.trans by simp only [bot_lt_iff_ne_bot]

/--
theorem `nhds_bot_basis` / 定理 `nhds_bot_basis`

English:
theorem nhds_bot_basis
  statement: (𝓝 (⊥ : EReal)).HasBasis (fun _ : Real => True) (Iio ·)
  proof: by
  refine (_root_.nhds_bot_basis (α := EReal)).to_hasBasis (fun x hx => ?_)
    fun _ _ => ⟨_, bot_lt_coe _, Subset.rfl⟩
  rcases exists_rat_btwn_of_lt hx with ⟨y, -, hxy⟩
  exact ⟨_, trivial, Iio_subset_Iio hxy.le⟩

中文:
定理 nhds_bot_basis
  结论: (𝓝 (⊥ : E实数)).HasBasis (fun _ : 实数 => True) (Iio ·)
  证明: by
  refine (_root_.nhds_bot_basis (α := EReal)).to_hasBasis (fun x hx => ?_)
    fun _ _ => ⟨_, bot_lt_coe _, Subset.rfl⟩
  rcases exists_rat_btwn_of_lt hx with ⟨y, -, hxy⟩
  exact ⟨_, trivial, Iio_subset_Iio hxy.le⟩

Depends on / 依赖: Iio_subset_Iio, Subset, Subset.rfl, _root_, _root_.nhds_bot_basis, bot_lt_coe, exists_rat_btwn_of_lt, hxy.le, nhds_bot_basis, to_hasBasis
-/
theorem nhds_bot_basis : (𝓝 (⊥ : EReal)).HasBasis (fun _ : Real => True) (Iio ·) := by
  refine (_root_.nhds_bot_basis (α := EReal)).to_hasBasis (fun x hx => ?_)
    fun _ _ => ⟨_, bot_lt_coe _, Subset.rfl⟩
  rcases exists_rat_btwn_of_lt hx with ⟨y, -, hxy⟩
  exact ⟨_, trivial, Iio_subset_Iio hxy.le⟩

/--
theorem `nhds_bot'` / 定理 `nhds_bot'`

English:
theorem nhds_bot'
  statement: 𝓝 (⊥ : EReal) = ⨅ a : Real, 𝓟 (Iio ↑a)
  proof: nhds_bot_basis.eq_iInf

中文:
定理 nhds_bot'
  结论: 𝓝 (⊥ : E实数) = ⨅ a : 实数, 𝓟 (Iio ↑a)
  证明: nhds_bot_basis.eq_iInf

Depends on / 依赖: eq_iInf, nhds_bot_basis, nhds_bot_basis.eq_iInf
-/
theorem nhds_bot' : 𝓝 (⊥ : EReal) = ⨅ a : Real, 𝓟 (Iio ↑a) :=
  nhds_bot_basis.eq_iInf

/--
theorem `mem_nhds_bot_iff` / 定理 `mem_nhds_bot_iff`

English:
theorem mem_nhds_bot_iff
  given: {s : Set EReal}
  statement: s in 𝓝 (⊥ : EReal) ↔ exists y : Real, Iio (y : EReal) subseteq s
  proof: nhds_bot_basis.mem_iff.trans by simp only [true_and]

中文:
定理 mem_nhds_bot_iff
  条件: {s : Set E实数}
  结论: s in 𝓝 (⊥ : E实数) ↔ 存在 y : 实数, Iio (y : E实数) subseteq s
  证明: nhds_bot_basis.mem_iff.trans by simp only [true_and]

Depends on / 依赖: mem_iff, nhds_bot_basis, nhds_bot_basis.mem_iff.trans, true_and
-/
theorem mem_nhds_bot_iff {s : Set EReal} : s in 𝓝 (⊥ : EReal) ↔ exists y : Real, Iio (y : EReal) subseteq s :=
nhds_bot_basis.mem_iff.trans by simp only [true_and]

/--
theorem `tendsto_nhds_bot_iff_real` / 定理 `tendsto_nhds_bot_iff_real`

English:
theorem tendsto_nhds_bot_iff_real
  given: {α : Type*} {m : α -> EReal} {f : Filter α}
  proof: nhds_bot_basis.tendsto_right_iff.trans by simp only [true_implies, mem_Iio]

中文:
定理 tendsto_nhds_bot_iff_real
  条件: {α : 类型} {m : α -> E实数} {f : Filter α}
  证明: nhds_bot_basis.tendsto_right_iff.trans by simp only [true_implies, mem_Iio]

Depends on / 依赖: mem_Iio, nhds_bot_basis, nhds_bot_basis.tendsto_right_iff.trans, tendsto_right_iff, true_implies
-/
theorem tendsto_nhds_bot_iff_real {α : Type*} {m : α -> EReal} {f : Filter α} :
    Tendsto m f (𝓝 ⊥) ↔ forall x : Real, forallᶠ a in f, m a < x :=
nhds_bot_basis.tendsto_right_iff.trans by simp only [true_implies, mem_Iio]

/--
lemma `nhdsWithin_top` / 引理 `nhdsWithin_top`

English:
lemma nhdsWithin_top
  statement: 𝓝[!=] (⊤ : EReal) = (atTop).map Real.toEReal
  proof: by
  apply (nhdsWithin_hasBasis nhds_top_basis_Ici _).ext (atTop_basis.map Real.toEReal)
  · simp only [EReal.image_coe_Ici, true_and]
    intro x hx
    by_cases hx_bot : x = ⊥
    · simp [hx_bot]
    lift x to Real using ⟨hx.ne_top, hx_bot⟩
    refine ⟨x, fun x ⟨h1, h2⟩ => ?_⟩
    simp [h1, h2.ne_

中文:
引理 nhdsWithin_top
  结论: 𝓝[!=] (⊤ : E实数) = (atTop).map 实数.toE实数
  证明: by
  apply (nhdsWithin_hasBasis nhds_top_basis_Ici _).ext (atTop_basis.map Real.toEReal)
  · simp only [EReal.image_coe_Ici, true_and]
    intro x hx
    by_cases hx_bot : x = ⊥
    · simp [hx_bot]
    lift x to Real using ⟨hx.ne_top, hx_bot⟩
    refine ⟨x, fun x ⟨h1, h2⟩ => ?_⟩
    simp [h1, h2.ne_

Depends on / 依赖: EReal.coe_lt_top, EReal.image_coe_Ici, Ne.lt_top, Real.toEReal, a.symm, atTop_basis, atTop_basis.map, coe_lt_top, h2.ne_top, hx.ne_top, hx_bot, image_coe_Ici, lt_top, ne_top, nhdsWithin_hasBasis, nhds_top_basis_Ici, toEReal, true_and, true_implies
-/
lemma nhdsWithin_top : 𝓝[!=] (⊤ : EReal) = (atTop).map Real.toEReal := by
  apply (nhdsWithin_hasBasis nhds_top_basis_Ici _).ext (atTop_basis.map Real.toEReal)
  · simp only [EReal.image_coe_Ici, true_and]
    intro x hx
    by_cases hx_bot : x = ⊥
    · simp [hx_bot]
    lift x to Real using ⟨hx.ne_top, hx_bot⟩
    refine ⟨x, fun x ⟨h1, h2⟩ => ?_⟩
    simp [h1, h2.ne_top]
  · simp only [EReal.image_coe_Ici, true_implies]
    refine fun x => ⟨x, ⟨EReal.coe_lt_top x, fun x ⟨(h1 : _ <= x), h2⟩ => ?_⟩⟩
    simp [h1, Ne.lt_top' fun a => h2 a.symm]

/--
lemma `nhdsWithin_bot` / 引理 `nhdsWithin_bot`

English:
lemma nhdsWithin_bot
  statement: 𝓝[!=] (⊥ : EReal) = (atBot).map Real.toEReal
  proof: by
  apply (nhdsWithin_hasBasis nhds_bot_basis_Iic _).ext (atBot_basis.map Real.toEReal)
  · simp only [EReal.image_coe_Iic,
      true_and]
    intro x hx
    by_cases hx_top : x = ⊤
    · simp [hx_top]
    lift x to Real using ⟨hx_top, hx.ne_bot⟩
    refine ⟨x, fun x ⟨h1, h2⟩ => ?_⟩
    simp [h2, 

中文:
引理 nhdsWithin_bot
  结论: 𝓝[!=] (⊥ : E实数) = (atBot).map 实数.toE实数
  证明: by
  apply (nhdsWithin_hasBasis nhds_bot_basis_Iic _).ext (atBot_basis.map Real.toEReal)
  · simp only [EReal.image_coe_Iic,
      true_and]
    intro x hx
    by_cases hx_top : x = ⊤
    · simp [hx_top]
    lift x to Real using ⟨hx_top, hx.ne_bot⟩
    refine ⟨x, fun x ⟨h1, h2⟩ => ?_⟩
    simp [h2, 

Depends on / 依赖: EReal.bot_lt_coe, EReal.image_coe_Iic, Ne.bot_lt, Real.toEReal, a.symm, atBot_basis, atBot_basis.map, bot_lt, bot_lt_coe, h1.ne_bot, hx.ne_bot, hx_top, image_coe_Iic, ne_bot, nhdsWithin_hasBasis, nhds_bot_basis_Iic, toEReal, true_and, true_implies
-/
lemma nhdsWithin_bot : 𝓝[!=] (⊥ : EReal) = (atBot).map Real.toEReal := by
  apply (nhdsWithin_hasBasis nhds_bot_basis_Iic _).ext (atBot_basis.map Real.toEReal)
  · simp only [EReal.image_coe_Iic,
      true_and]
    intro x hx
    by_cases hx_top : x = ⊤
    · simp [hx_top]
    lift x to Real using ⟨hx_top, hx.ne_bot⟩
    refine ⟨x, fun x ⟨h1, h2⟩ => ?_⟩
    simp [h2, h1.ne_bot]
  · simp only [EReal.image_coe_Iic, true_implies]
    refine fun x => ⟨x, ⟨EReal.bot_lt_coe x, fun x ⟨(h1 : x <= _), h2⟩ => ?_⟩⟩
    simp [h1, Ne.bot_lt' fun a => h2 a.symm]

omit [TopologicalSpace α] in
@[simp]
/--
lemma `tendsto_coe_nhds_top_iff` / 引理 `tendsto_coe_nhds_top_iff`

English:
lemma tendsto_coe_nhds_top_iff
  given: {f : α -> Real} {l : Filter α}
  proof: by
  rw [tendsto_nhds_top_iff_real]; rw [atTop_basis_Ioi.tendsto_right_iff]; simp

中文:
引理 tendsto_coe_nhds_top_iff
  条件: {f : α -> 实数} {l : Filter α}
  证明: by
  rw [tendsto_nhds_top_iff_real]; rw [atTop_basis_Ioi.tendsto_right_iff]; simp

Depends on / 依赖: atTop_basis_Ioi, atTop_basis_Ioi.tendsto_right_iff, tendsto_nhds_top_iff_real, tendsto_right_iff
-/
lemma tendsto_coe_nhds_top_iff {f : α -> Real} {l : Filter α} :
    Tendsto (fun x => Real.toEReal (f x)) l (𝓝 ⊤) ↔ Tendsto f l atTop := by
  rw [tendsto_nhds_top_iff_real]; rw [atTop_basis_Ioi.tendsto_right_iff]; simp

/--
lemma `tendsto_coe_atTop` / 引理 `tendsto_coe_atTop`

English:
lemma tendsto_coe_atTop
  statement: Tendsto Real.toEReal atTop (𝓝 ⊤)
  proof: tendsto_coe_nhds_top_iff.2 tendsto_id

omit [TopologicalSpace α] in
@[simp]

中文:
引理 tendsto_coe_atTop
  结论: Tendsto 实数.toE实数 atTop (𝓝 ⊤)
  证明: tendsto_coe_nhds_top_iff.2 tendsto_id

omit [TopologicalSpace α] in
@[simp]

Depends on / 依赖: tendsto_coe_nhds_top_iff, tendsto_id
-/
lemma tendsto_coe_atTop : Tendsto Real.toEReal atTop (𝓝 ⊤) :=
  tendsto_coe_nhds_top_iff.2 tendsto_id

omit [TopologicalSpace α] in
@[simp]
/--
lemma `tendsto_coe_nhds_bot_iff` / 引理 `tendsto_coe_nhds_bot_iff`

English:
lemma tendsto_coe_nhds_bot_iff
  given: {f : α -> Real} {l : Filter α}
  proof: by
  rw [tendsto_nhds_bot_iff_real]; rw [atBot_basis_Iio.tendsto_right_iff]; simp

中文:
引理 tendsto_coe_nhds_bot_iff
  条件: {f : α -> 实数} {l : Filter α}
  证明: by
  rw [tendsto_nhds_bot_iff_real]; rw [atBot_basis_Iio.tendsto_right_iff]; simp

Depends on / 依赖: atBot_basis_Iio, atBot_basis_Iio.tendsto_right_iff, tendsto_nhds_bot_iff_real, tendsto_right_iff
-/
lemma tendsto_coe_nhds_bot_iff {f : α -> Real} {l : Filter α} :
    Tendsto (fun x => Real.toEReal (f x)) l (𝓝 ⊥) ↔ Tendsto f l atBot := by
  rw [tendsto_nhds_bot_iff_real]; rw [atBot_basis_Iio.tendsto_right_iff]; simp

/--
lemma `tendsto_coe_atBot` / 引理 `tendsto_coe_atBot`

English:
lemma tendsto_coe_atBot
  statement: Tendsto Real.toEReal atBot (𝓝 ⊥)
  proof: tendsto_coe_nhds_bot_iff.2 tendsto_id

中文:
引理 tendsto_coe_atBot
  结论: Tendsto 实数.toE实数 atBot (𝓝 ⊥)
  证明: tendsto_coe_nhds_bot_iff.2 tendsto_id

Depends on / 依赖: tendsto_coe_nhds_bot_iff, tendsto_id
-/
lemma tendsto_coe_atBot : Tendsto Real.toEReal atBot (𝓝 ⊥) :=
  tendsto_coe_nhds_bot_iff.2 tendsto_id


/--
lemma `tendsto_toReal_atTop` / 引理 `tendsto_toReal_atTop`

English:
lemma tendsto_toReal_atTop
  statement: Tendsto EReal.toReal (𝓝[!=] ⊤) atTop
  proof: by
  rw [nhdsWithin_top]; rw [tendsto_map'_iff]
  exact tendsto_id

中文:
引理 tendsto_toReal_atTop
  结论: Tendsto E实数.to实数 (𝓝[!=] ⊤) atTop
  证明: by
  rw [nhdsWithin_top]; rw [tendsto_map'_iff]
  exact tendsto_id

Depends on / 依赖: _iff, nhdsWithin_top, tendsto_id, tendsto_map
-/
lemma tendsto_toReal_atTop : Tendsto EReal.toReal (𝓝[!=] ⊤) atTop := by
  rw [nhdsWithin_top]; rw [tendsto_map'_iff]
  exact tendsto_id

/--
lemma `tendsto_toReal_atBot` / 引理 `tendsto_toReal_atBot`

English:
lemma tendsto_toReal_atBot
  statement: Tendsto EReal.toReal (𝓝[!=] ⊥) atBot
  proof: by
  rw [nhdsWithin_bot]; rw [tendsto_map'_iff]
  exact tendsto_id

中文:
引理 tendsto_toReal_atBot
  结论: Tendsto E实数.to实数 (𝓝[!=] ⊥) atBot
  证明: by
  rw [nhdsWithin_bot]; rw [tendsto_map'_iff]
  exact tendsto_id

Depends on / 依赖: _iff, nhdsWithin_bot, tendsto_id, tendsto_map
-/
lemma tendsto_toReal_atBot : Tendsto EReal.toReal (𝓝[!=] ⊥) atBot := by
  rw [nhdsWithin_bot]; rw [tendsto_map'_iff]
  exact tendsto_id


/--
lemma `continuous_toENNReal` / 引理 `continuous_toENNReal`

English:
lemma continuous_toENNReal
  statement: Continuous EReal.toENNReal
  proof: by
  refine continuous_iff_continuousAt.mpr fun x => ?_
  by_cases h_top : x = ⊤
  · simp only [ContinuousAt, h_top, toENNReal_top]
    refine ENNReal.tendsto_nhds_top fun n => ?_
    filter_upwards [eventually_gt_nhds (coe_lt_top n)] with y hy
    exact toENNReal_coe (x := n) ▸ toENNReal_lt_toENNRe

中文:
引理 continuous_toENNReal
  结论: Continuous E实数.toENN实数
  证明: by
  refine continuous_iff_continuousAt.mpr fun x => ?_
  by_cases h_top : x = ⊤
  · simp only [ContinuousAt, h_top, toENNReal_top]
    refine ENNReal.tendsto_nhds_top fun n => ?_
    filter_upwards [eventually_gt_nhds (coe_lt_top n)] with y hy
    exact toENNReal_coe (x := n) ▸ toENNReal_lt_toENNRe

Depends on / 依赖: ContinuousAt, ContinuousOn, ContinuousOn.continuousAt, ENNReal, ENNReal.tendsto_nhds_top, coe_ennreal_nonneg, coe_lt_top, compl_singleton_mem_nhds_iff, compl_singleton_mem_nhds_iff.mpr, continuousAt, continuousOn_of_forall_continuousAt, continuous_iff_continuousAt, continuous_iff_continuousAt.mpr, eventually_gt_nhds, filter_upwards, h_top, tendsto_nhds_top, toENNReal_coe, toENNReal_lt_toENNReal, toENNReal_of_ne_top
-/
lemma continuous_toENNReal : Continuous EReal.toENNReal := by
  refine continuous_iff_continuousAt.mpr fun x => ?_
  by_cases h_top : x = ⊤
  · simp only [ContinuousAt, h_top, toENNReal_top]
    refine ENNReal.tendsto_nhds_top fun n => ?_
    filter_upwards [eventually_gt_nhds (coe_lt_top n)] with y hy
    exact toENNReal_coe (x := n) ▸ toENNReal_lt_toENNReal (coe_ennreal_nonneg _) hy
  refine ContinuousOn.continuousAt ?_ (compl_singleton_mem_nhds_iff.mpr h_top)
  refine (continuousOn_of_forall_continuousAt fun x hx => ?_).congr (fun _ h => toENNReal_of_ne_top h)
  by_cases h_bot : x = ⊥
  · refine tendsto_nhds_of_eventually_eq ?_
    rw [h_bot]; rw [nhds_bot_basis.eventually_iff]
    simpa [toReal_bot, ENNReal.ofReal_zero, ENNReal.ofReal_eq_zero, true_and] using
      ⟨0, fun _ hx => toReal_nonpos hx.le⟩
refine ENNReal.continuous_ofReal.continuousAt.comp' continuousOn_toReal.continuousAt
 (toFinite _).isClosed.compl_mem_nhds ?_
  simp_all only [mem_compl_iff, mem_singleton_iff, mem_insert_iff, or_self, not_false_eq_true]

@[fun_prop]
/--
lemma `_root_.Continuous.ereal_toENNReal` / 引理 `_root_.Continuous.ereal_toENNReal`

English:
lemma _root_.Continuous.ereal_toENNReal
  statement: {α : Type*} [TopologicalSpace α] {f : α -> EReal}
  proof: continuous_toENNReal.comp hf

@[fun_prop]

中文:
引理 _root_.Continuous.ereal_toENNReal
  结论: {α : 类型} [TopologicalSpace α] {f : α -> E实数}
  证明: continuous_toENNReal.comp hf

@[fun_prop]

Depends on / 依赖: continuous_toENNReal, continuous_toENNReal.comp
-/
lemma _root_.Continuous.ereal_toENNReal {α : Type*} [TopologicalSpace α] {f : α -> EReal}
    (hf : Continuous f) :
    Continuous fun x => (f x).toENNReal :=
  continuous_toENNReal.comp hf

@[fun_prop]
/--
lemma `_root_.ContinuousOn.ereal_toENNReal` / 引理 `_root_.ContinuousOn.ereal_toENNReal`

English:
lemma _root_.ContinuousOn.ereal_toENNReal
  statement: {α : Type*} [TopologicalSpace α] {s : Set α}
  proof: continuous_toENNReal.comp_continuousOn hf

@[fun_prop]

中文:
引理 _root_.ContinuousOn.ereal_toENNReal
  结论: {α : 类型} [TopologicalSpace α] {s : Set α}
  证明: continuous_toENNReal.comp_continuousOn hf

@[fun_prop]

Depends on / 依赖: comp_continuousOn, continuous_toENNReal, continuous_toENNReal.comp_continuousOn
-/
lemma _root_.ContinuousOn.ereal_toENNReal {α : Type*} [TopologicalSpace α] {s : Set α}
    {f : α -> EReal} (hf : ContinuousOn f s) :
    ContinuousOn (fun x => (f x).toENNReal) s :=
  continuous_toENNReal.comp_continuousOn hf

@[fun_prop]
/--
lemma `_root_.ContinuousWithinAt.ereal_toENNReal` / 引理 `_root_.ContinuousWithinAt.ereal_toENNReal`

English:
lemma _root_.ContinuousWithinAt.ereal_toENNReal
  statement: {α : Type*} [TopologicalSpace α] {f : α -> EReal}
  proof: continuous_toENNReal.continuousAt.comp_continuousWithinAt hf

@[fun_prop]

中文:
引理 _root_.ContinuousWithinAt.ereal_toENNReal
  结论: {α : 类型} [TopologicalSpace α] {f : α -> E实数}
  证明: continuous_toENNReal.continuousAt.comp_continuousWithinAt hf

@[fun_prop]

Depends on / 依赖: comp_continuousWithinAt, continuousAt, continuous_toENNReal, continuous_toENNReal.continuousAt.comp_continuousWithinAt
-/
lemma _root_.ContinuousWithinAt.ereal_toENNReal {α : Type*} [TopologicalSpace α] {f : α -> EReal}
    {s : Set α} {x : α} (hf : ContinuousWithinAt f s x) :
    ContinuousWithinAt (fun x => (f x).toENNReal) s x :=
  continuous_toENNReal.continuousAt.comp_continuousWithinAt hf

@[fun_prop]
/--
lemma `_root_.ContinuousAt.ereal_toENNReal` / 引理 `_root_.ContinuousAt.ereal_toENNReal`

English:
lemma _root_.ContinuousAt.ereal_toENNReal
  statement: {α : Type*} [TopologicalSpace α] {f : α -> EReal}
  proof: continuous_toENNReal.continuousAt.comp hf

中文:
引理 _root_.ContinuousAt.ereal_toENNReal
  结论: {α : 类型} [TopologicalSpace α] {f : α -> E实数}
  证明: continuous_toENNReal.continuousAt.comp hf

Depends on / 依赖: continuousAt, continuous_toENNReal, continuous_toENNReal.continuousAt.comp
-/
lemma _root_.ContinuousAt.ereal_toENNReal {α : Type*} [TopologicalSpace α] {f : α -> EReal}
    {x : α} (hf : ContinuousAt f x) :
    ContinuousAt (fun x => (f x).toENNReal) x :=
  continuous_toENNReal.continuousAt.comp hf

/-! ### Infs and Sups -/

variable {α : Type*} {u v : α -> EReal}

/--
lemma `add_iInf_le_iInf_add` / 引理 `add_iInf_le_iInf_add`

English:
lemma add_iInf_le_iInf_add
  statement: (⨅ x, u x) + ⨅ x, v x <= ⨅ x, (u + v) x
  proof: le_iInf fun i => add_le_add (iInf_le u i) (iInf_le v i)

中文:
引理 add_iInf_le_iInf_add
  结论: (⨅ x, u x) + ⨅ x, v x <= ⨅ x, (u + v) x
  证明: le_iInf fun i => add_le_add (iInf_le u i) (iInf_le v i)

Depends on / 依赖: add_le_add, iInf_le, le_iInf
-/
lemma add_iInf_le_iInf_add : (⨅ x, u x) + ⨅ x, v x <= ⨅ x, (u + v) x :=
  le_iInf fun i => add_le_add (iInf_le u i) (iInf_le v i)

/--
lemma `iSup_add_le_add_iSup` / 引理 `iSup_add_le_add_iSup`

English:
lemma iSup_add_le_add_iSup
  statement: ⨆ x, (u + v) x <= (⨆ x, u x) + ⨆ x, v x
  proof: iSup_le fun i => add_le_add (le_iSup u i) (le_iSup v i)

中文:
引理 iSup_add_le_add_iSup
  结论: ⨆ x, (u + v) x <= (⨆ x, u x) + ⨆ x, v x
  证明: iSup_le fun i => add_le_add (le_iSup u i) (le_iSup v i)

Depends on / 依赖: add_le_add, iSup_le, le_iSup
-/
lemma iSup_add_le_add_iSup : ⨆ x, (u + v) x <= (⨆ x, u x) + ⨆ x, v x :=
  iSup_le fun i => add_le_add (le_iSup u i) (le_iSup v i)

/-! ### Liminfs and Limsups -/

section LimInfSup

variable {α : Type*} {f : Filter α} {u v : α -> EReal}

/--
lemma `liminf_neg` / 引理 `liminf_neg`

English:
lemma liminf_neg
  statement: liminf (-v) f = -limsup v f
  proof: EReal.negOrderIso.limsup_apply.symm

中文:
引理 liminf_neg
  结论: liminf (-v) f = -limsup v f
  证明: EReal.negOrderIso.limsup_apply.symm

Depends on / 依赖: EReal.negOrderIso.limsup_apply.symm, limsup_apply, negOrderIso
-/
lemma liminf_neg : liminf (-v) f = -limsup v f :=
  EReal.negOrderIso.limsup_apply.symm

/--
lemma `limsup_neg` / 引理 `limsup_neg`

English:
lemma limsup_neg
  statement: limsup (-v) f = -liminf v f
  proof: EReal.negOrderIso.liminf_apply.symm

中文:
引理 limsup_neg
  结论: limsup (-v) f = -liminf v f
  证明: EReal.negOrderIso.liminf_apply.symm

Depends on / 依赖: EReal.negOrderIso.liminf_apply.symm, liminf_apply, negOrderIso
-/
lemma limsup_neg : limsup (-v) f = -liminf v f :=
  EReal.negOrderIso.liminf_apply.symm

/--
lemma `le_liminf_add` / 引理 `le_liminf_add`

English:
lemma le_liminf_add
  statement: (liminf u f) + (liminf v f) <= liminf (u + v) f
  proof: by
  refine add_le_of_forall_lt fun a a_u b b_v => (le_liminf_iff).2 fun c c_ab => ?_
  filter_upwards [eventually_lt_of_lt_liminf a_u, eventually_lt_of_lt_liminf b_v] with x a_x b_x
  exact c_ab.trans (add_lt_add a_x b_x)

中文:
引理 le_liminf_add
  结论: (liminf u f) + (liminf v f) <= liminf (u + v) f
  证明: by
  refine add_le_of_forall_lt fun a a_u b b_v => (le_liminf_iff).2 fun c c_ab => ?_
  filter_upwards [eventually_lt_of_lt_liminf a_u, eventually_lt_of_lt_liminf b_v] with x a_x b_x
  exact c_ab.trans (add_lt_add a_x b_x)

Depends on / 依赖: add_le_of_forall_lt, add_lt_add, c_ab, c_ab.trans, eventually_lt_of_lt_liminf, filter_upwards, le_liminf_iff
-/
lemma le_liminf_add : (liminf u f) + (liminf v f) <= liminf (u + v) f := by
  refine add_le_of_forall_lt fun a a_u b b_v => (le_liminf_iff).2 fun c c_ab => ?_
  filter_upwards [eventually_lt_of_lt_liminf a_u, eventually_lt_of_lt_liminf b_v] with x a_x b_x
  exact c_ab.trans (add_lt_add a_x b_x)

/--
lemma `limsup_add_le` / 引理 `limsup_add_le`

English:
lemma limsup_add_le
  given: (h : limsup u f != ⊥ ∨ limsup v f != ⊤) (h' : limsup u f != ⊤ ∨ limsup v f != ⊥)
  proof: by
  refine le_add_of_forall_gt h h' fun a a_u b b_v => (limsup_le_iff).2 fun c c_ab => ?_
  filter_upwards [eventually_lt_of_limsup_lt a_u, eventually_lt_of_limsup_lt b_v] with x a_x b_x
  exact (add_lt_add a_x b_x).trans c_ab

中文:
引理 limsup_add_le
  条件: (h : limsup u f != ⊥ ∨ limsup v f != ⊤) (h' : limsup u f != ⊤ ∨ limsup v f != ⊥)
  证明: by
  refine le_add_of_forall_gt h h' fun a a_u b b_v => (limsup_le_iff).2 fun c c_ab => ?_
  filter_upwards [eventually_lt_of_limsup_lt a_u, eventually_lt_of_limsup_lt b_v] with x a_x b_x
  exact (add_lt_add a_x b_x).trans c_ab

Depends on / 依赖: add_lt_add, c_ab, eventually_lt_of_limsup_lt, filter_upwards, le_add_of_forall_gt, limsup_le_iff
-/
lemma limsup_add_le (h : limsup u f != ⊥ ∨ limsup v f != ⊤) (h' : limsup u f != ⊤ ∨ limsup v f != ⊥) :
    limsup (u + v) f <= (limsup u f) + (limsup v f) := by
  refine le_add_of_forall_gt h h' fun a a_u b b_v => (limsup_le_iff).2 fun c c_ab => ?_
  filter_upwards [eventually_lt_of_limsup_lt a_u, eventually_lt_of_limsup_lt b_v] with x a_x b_x
  exact (add_lt_add a_x b_x).trans c_ab

/--
lemma `le_limsup_add` / 引理 `le_limsup_add`

English:
lemma le_limsup_add
  statement: (limsup u f) + (liminf v f) <= limsup (u + v) f
  proof: add_le_of_forall_lt fun _ a_u _ b_v => (le_limsup_iff).2 fun _ c_ab =>
    (((frequently_lt_of_lt_limsup) a_u).and_eventually ((eventually_lt_of_lt_liminf) b_v)).mono
    fun _ ab_x => c_ab.trans (add_lt_add ab_x.1 ab_x.2)

中文:
引理 le_limsup_add
  结论: (limsup u f) + (liminf v f) <= limsup (u + v) f
  证明: add_le_of_forall_lt fun _ a_u _ b_v => (le_limsup_iff).2 fun _ c_ab =>
    (((frequently_lt_of_lt_limsup) a_u).and_eventually ((eventually_lt_of_lt_liminf) b_v)).mono
    fun _ ab_x => c_ab.trans (add_lt_add ab_x.1 ab_x.2)

Depends on / 依赖: ab_x, add_le_of_forall_lt, add_lt_add, and_eventually, c_ab, c_ab.trans, eventually_lt_of_lt_liminf, frequently_lt_of_lt_limsup, le_limsup_iff
-/
lemma le_limsup_add : (limsup u f) + (liminf v f) <= limsup (u + v) f :=
  add_le_of_forall_lt fun _ a_u _ b_v => (le_limsup_iff).2 fun _ c_ab =>
    (((frequently_lt_of_lt_limsup) a_u).and_eventually ((eventually_lt_of_lt_liminf) b_v)).mono
    fun _ ab_x => c_ab.trans (add_lt_add ab_x.1 ab_x.2)

/--
lemma `liminf_add_le` / 引理 `liminf_add_le`

English:
lemma liminf_add_le
  given: (h : limsup u f != ⊥ ∨ liminf v f != ⊤) (h' : limsup u f != ⊤ ∨ liminf v f != ⊥)
  proof: le_add_of_forall_gt h h' fun _ a_u _ b_v => (liminf_le_iff).2 fun _ c_ab =>
    (((frequently_lt_of_liminf_lt) b_v).and_eventually ((eventually_lt_of_limsup_lt) a_u)).mono
    fun _ ab_x => (add_lt_add ab_x.2 ab_x.1).trans c_ab

中文:
引理 liminf_add_le
  条件: (h : limsup u f != ⊥ ∨ liminf v f != ⊤) (h' : limsup u f != ⊤ ∨ liminf v f != ⊥)
  证明: le_add_of_forall_gt h h' fun _ a_u _ b_v => (liminf_le_iff).2 fun _ c_ab =>
    (((frequently_lt_of_liminf_lt) b_v).and_eventually ((eventually_lt_of_limsup_lt) a_u)).mono
    fun _ ab_x => (add_lt_add ab_x.2 ab_x.1).trans c_ab

Depends on / 依赖: ab_x, add_lt_add, and_eventually, c_ab, eventually_lt_of_limsup_lt, frequently_lt_of_liminf_lt, le_add_of_forall_gt, liminf_le_iff
-/
lemma liminf_add_le (h : limsup u f != ⊥ ∨ liminf v f != ⊤) (h' : limsup u f != ⊤ ∨ liminf v f != ⊥) :
    liminf (u + v) f <= (limsup u f) + (liminf v f) :=
  le_add_of_forall_gt h h' fun _ a_u _ b_v => (liminf_le_iff).2 fun _ c_ab =>
    (((frequently_lt_of_liminf_lt) b_v).and_eventually ((eventually_lt_of_limsup_lt) a_u)).mono
    fun _ ab_x => (add_lt_add ab_x.2 ab_x.1).trans c_ab

/--
lemma `limsup_add_bot_of_ne_top` / 引理 `limsup_add_bot_of_ne_top`

English:
lemma limsup_add_bot_of_ne_top
  given: (h : limsup u f = ⊥) (h' : limsup v f != ⊤)
  proof: by
  apply le_bot_iff.1 ((limsup_add_le (.inr h') _).trans _)
  · rw [h]; exact .inl bot_ne_top
  · rw [h, bot_add]

中文:
引理 limsup_add_bot_of_ne_top
  条件: (h : limsup u f = ⊥) (h' : limsup v f != ⊤)
  证明: by
  apply le_bot_iff.1 ((limsup_add_le (.inr h') _).trans _)
  · rw [h]; exact .inl bot_ne_top
  · rw [h, bot_add]

Depends on / 依赖: bot_add, bot_ne_top, le_bot_iff, limsup_add_le
-/
lemma limsup_add_bot_of_ne_top (h : limsup u f = ⊥) (h' : limsup v f != ⊤) :
    limsup (u + v) f = ⊥ := by
  apply le_bot_iff.1 ((limsup_add_le (.inr h') _).trans _)
  · rw [h]; exact .inl bot_ne_top
  · rw [h, bot_add]

/--
lemma `limsup_add_le_of_le` / 引理 `limsup_add_le_of_le`

English:
lemma limsup_add_le_of_le
  given: {a b : EReal} (ha : limsup u f < a) (hb : limsup v f <= b)
  proof: by
  rcases eq_top_or_lt_top b with rfl | h
  · rw [add_top_of_ne_bot ha.ne_bot]; exact le_top
  · exact (limsup_add_le (.inr (hb.trans_lt h).ne) (.inl ha.ne_top)).trans (add_le_add ha.le hb)

中文:
引理 limsup_add_le_of_le
  条件: {a b : E实数} (ha : limsup u f < a) (hb : limsup v f <= b)
  证明: by
  rcases eq_top_or_lt_top b with rfl | h
  · rw [add_top_of_ne_bot ha.ne_bot]; exact le_top
  · exact (limsup_add_le (.inr (hb.trans_lt h).ne) (.inl ha.ne_top)).trans (add_le_add ha.le hb)

Depends on / 依赖: add_le_add, add_top_of_ne_bot, eq_top_or_lt_top, ha.le, ha.ne_bot, ha.ne_top, hb.trans_lt, le_top, limsup_add_le, ne_bot, ne_top, trans_lt
-/
lemma limsup_add_le_of_le {a b : EReal} (ha : limsup u f < a) (hb : limsup v f <= b) :
    limsup (u + v) f <= a + b := by
  rcases eq_top_or_lt_top b with rfl | h
  · rw [add_top_of_ne_bot ha.ne_bot]; exact le_top
  · exact (limsup_add_le (.inr (hb.trans_lt h).ne) (.inl ha.ne_top)).trans (add_le_add ha.le hb)

/--
lemma `liminf_add_gt_of_gt` / 引理 `liminf_add_gt_of_gt`

English:
lemma liminf_add_gt_of_gt
  given: {a b : EReal} (ha : a < liminf u f) (hb : b < liminf v f)
  proof: (add_lt_add ha hb).trans_le le_liminf_add

中文:
引理 liminf_add_gt_of_gt
  条件: {a b : E实数} (ha : a < liminf u f) (hb : b < liminf v f)
  证明: (add_lt_add ha hb).trans_le le_liminf_add

Depends on / 依赖: add_lt_add, le_liminf_add, trans_le
-/
lemma liminf_add_gt_of_gt {a b : EReal} (ha : a < liminf u f) (hb : b < liminf v f) :
    a + b < liminf (u + v) f :=
  (add_lt_add ha hb).trans_le le_liminf_add

/--
lemma `liminf_add_top_of_ne_bot` / 引理 `liminf_add_top_of_ne_bot`

English:
lemma liminf_add_top_of_ne_bot
  given: (h : liminf u f = ⊤) (h' : liminf v f != ⊥)
  proof: by
  apply top_le_iff.1 (le_trans _ le_liminf_add)
  rw [h]; rw [top_add_of_ne_bot h']

中文:
引理 liminf_add_top_of_ne_bot
  条件: (h : liminf u f = ⊤) (h' : liminf v f != ⊥)
  证明: by
  apply top_le_iff.1 (le_trans _ le_liminf_add)
  rw [h]; rw [top_add_of_ne_bot h']

Depends on / 依赖: le_liminf_add, le_trans, top_add_of_ne_bot, top_le_iff
-/
lemma liminf_add_top_of_ne_bot (h : liminf u f = ⊤) (h' : liminf v f != ⊥) :
    liminf (u + v) f = ⊤ := by
  apply top_le_iff.1 (le_trans _ le_liminf_add)
  rw [h]; rw [top_add_of_ne_bot h']

/--
theorem `limsup_const_mul_of_nonneg_of_ne_top` / 定理 `limsup_const_mul_of_nonneg_of_ne_top`

English:
theorem limsup_const_mul_of_nonneg_of_ne_top
  given: [NeBot f] {c : EReal} (h₁ : 0 <= c) (h₂ : c != ⊤)
  proof: by
  obtain rfl | h₃ := h₁.eq_or_lt
  · simp
  simp_rw [EReal.mul_comm (x := c)]
  apply eq_of_le_of_ge
  · rw [limsup_le_iff]
    simpa [← EReal.lt_div_iff (by aesop) (by aesop)]
      using fun _ => eventually_lt_of_limsup_lt
  · rw [le_limsup_iff]
    simpa [← EReal.div_lt_iff (by aesop) (by aeso

中文:
定理 limsup_const_mul_of_nonneg_of_ne_top
  条件: [NeBot f] {c : E实数} (h₁ : 0 <= c) (h₂ : c != ⊤)
  证明: by
  obtain rfl | h₃ := h₁.eq_or_lt
  · simp
  simp_rw [EReal.mul_comm (x := c)]
  apply eq_of_le_of_ge
  · rw [limsup_le_iff]
    simpa [← EReal.lt_div_iff (by aesop) (by aesop)]
      using fun _ => eventually_lt_of_limsup_lt
  · rw [le_limsup_iff]
    simpa [← EReal.div_lt_iff (by aesop) (by aeso

Depends on / 依赖: EReal.div_lt_iff, EReal.lt_div_iff, EReal.mul_comm, div_lt_iff, eq_of_le_of_ge, eq_or_lt, eventually_lt_of_limsup_lt, frequently_lt_of_lt_limsup, le_limsup_iff, limsup_le_iff, lt_div_iff, mul_comm, simp_rw
-/
theorem limsup_const_mul_of_nonneg_of_ne_top [NeBot f] {c : EReal} (h₁ : 0 <= c) (h₂ : c != ⊤) :
    limsup (fun x => c * u x) f = c * limsup u f := by
  obtain rfl | h₃ := h₁.eq_or_lt
  · simp
  simp_rw [EReal.mul_comm (x := c)]
  apply eq_of_le_of_ge
  · rw [limsup_le_iff]
    simpa [← EReal.lt_div_iff (by aesop) (by aesop)]
      using fun _ => eventually_lt_of_limsup_lt
  · rw [le_limsup_iff]
    simpa [← EReal.div_lt_iff (by aesop) (by aesop)]
      using fun _ => frequently_lt_of_lt_limsup

/--
theorem `limsup_const_mul_of_nonpos_of_ne_bot` / 定理 `limsup_const_mul_of_nonpos_of_ne_bot`

English:
theorem limsup_const_mul_of_nonpos_of_ne_bot
  given: [NeBot f] {c : EReal} (h₁ : c <= 0) (h₂ : c != ⊥)
  proof: by
  simpa [limsup_neg] using
    limsup_const_mul_of_nonneg_of_ne_top (u := -u) (c := -c) (by aesop) (by aesop)

中文:
定理 limsup_const_mul_of_nonpos_of_ne_bot
  条件: [NeBot f] {c : E实数} (h₁ : c <= 0) (h₂ : c != ⊥)
  证明: by
  simpa [limsup_neg] using
    limsup_const_mul_of_nonneg_of_ne_top (u := -u) (c := -c) (by aesop) (by aesop)

Depends on / 依赖: limsup_const_mul_of_nonneg_of_ne_top, limsup_neg
-/
theorem limsup_const_mul_of_nonpos_of_ne_bot [NeBot f] {c : EReal} (h₁ : c <= 0) (h₂ : c != ⊥) :
    limsup (fun x => c * u x) f = c * liminf u f := by
  simpa [limsup_neg] using
    limsup_const_mul_of_nonneg_of_ne_top (u := -u) (c := -c) (by aesop) (by aesop)

/--
theorem `liminf_const_mul_of_nonneg_of_ne_top` / 定理 `liminf_const_mul_of_nonneg_of_ne_top`

English:
theorem liminf_const_mul_of_nonneg_of_ne_top
  given: [NeBot f] {c : EReal} (h₁ : 0 <= c) (h₂ : c != ⊤)
  proof: by
  simpa [mul_neg, ← Pi.neg_def, limsup_neg] using
    limsup_const_mul_of_nonneg_of_ne_top (u := -u) (by aesop) (by aesop)

中文:
定理 liminf_const_mul_of_nonneg_of_ne_top
  条件: [NeBot f] {c : E实数} (h₁ : 0 <= c) (h₂ : c != ⊤)
  证明: by
  simpa [mul_neg, ← Pi.neg_def, limsup_neg] using
    limsup_const_mul_of_nonneg_of_ne_top (u := -u) (by aesop) (by aesop)

Depends on / 依赖: Pi.neg_def, limsup_const_mul_of_nonneg_of_ne_top, limsup_neg, mul_neg, neg_def
-/
theorem liminf_const_mul_of_nonneg_of_ne_top [NeBot f] {c : EReal} (h₁ : 0 <= c) (h₂ : c != ⊤) :
    liminf (fun x => c * u x) f = c * liminf u f := by
  simpa [mul_neg, ← Pi.neg_def, limsup_neg] using
    limsup_const_mul_of_nonneg_of_ne_top (u := -u) (by aesop) (by aesop)

/--
theorem `liminf_const_mul_of_nonpos_of_ne_bot` / 定理 `liminf_const_mul_of_nonpos_of_ne_bot`

English:
theorem liminf_const_mul_of_nonpos_of_ne_bot
  given: [NeBot f] {c : EReal} (h₁ : c <= 0) (h₂ : c != ⊥)
  proof: by
  simpa [neg_mul, ← Pi.neg_def, limsup_neg] using
    limsup_const_mul_of_nonneg_of_ne_top (c := -c) (by aesop) (by aesop)

中文:
定理 liminf_const_mul_of_nonpos_of_ne_bot
  条件: [NeBot f] {c : E实数} (h₁ : c <= 0) (h₂ : c != ⊥)
  证明: by
  simpa [neg_mul, ← Pi.neg_def, limsup_neg] using
    limsup_const_mul_of_nonneg_of_ne_top (c := -c) (by aesop) (by aesop)

Depends on / 依赖: Pi.neg_def, limsup_const_mul_of_nonneg_of_ne_top, limsup_neg, neg_def, neg_mul
-/
theorem liminf_const_mul_of_nonpos_of_ne_bot [NeBot f] {c : EReal} (h₁ : c <= 0) (h₂ : c != ⊥) :
    liminf (fun x => c * u x) f = c * limsup u f := by
  simpa [neg_mul, ← Pi.neg_def, limsup_neg] using
    limsup_const_mul_of_nonneg_of_ne_top (c := -c) (by aesop) (by aesop)

/--
lemma `le_limsup_mul` / 引理 `le_limsup_mul`

English:
lemma le_limsup_mul
  given: (hu : existsᶠ x in f, 0 <= u x) (hv : 0 <=ᶠ[f] v)
  proof: by
  rcases f.eq_or_neBot with rfl | _
  · rw [limsup_bot, limsup_bot, liminf_bot, bot_mul_top]
  have u0 : 0 <= limsup u f := le_limsup_of_frequently_le hu
  have uv0 : 0 <= limsup (u * v) f :=
le_limsup_of_frequently_le (hu.and_eventually hv).mono fun _ ⟨hu, hv⟩ => mul_nonneg hu hv
  refine mul_le

中文:
引理 le_limsup_mul
  条件: (hu : 存在ᶠ x in f, 0 <= u x) (hv : 0 <=ᶠ[f] v)
  证明: by
  rcases f.eq_or_neBot with rfl | _
  · rw [limsup_bot, limsup_bot, liminf_bot, bot_mul_top]
  have u0 : 0 <= limsup u f := le_limsup_of_frequently_le hu
  have uv0 : 0 <= limsup (u * v) f :=
le_limsup_of_frequently_le (hu.and_eventually hv).mono fun _ ⟨hu, hv⟩ => mul_nonneg hu hv
  refine mul_le

Depends on / 依赖: and_eventually, bot_mul_top, c_ab, eq_or_neBot, eventually_lt_of_lt_liminf, f.eq_or_neBot, frequently_lt_of_lt_limsup, hu.and_eventually, le_limsup_iff, le_limsup_of_frequently_le, liminf_bot, limsup, limsup_bot, mem_Ioo, mul_le_of_forall_lt_of_nonneg, mul_nonneg
-/
lemma le_limsup_mul (hu : existsᶠ x in f, 0 <= u x) (hv : 0 <=ᶠ[f] v) :
    limsup u f * liminf v f <= limsup (u * v) f := by
  rcases f.eq_or_neBot with rfl | _
  · rw [limsup_bot, limsup_bot, liminf_bot, bot_mul_top]
  have u0 : 0 <= limsup u f := le_limsup_of_frequently_le hu
  have uv0 : 0 <= limsup (u * v) f :=
le_limsup_of_frequently_le (hu.and_eventually hv).mono fun _ ⟨hu, hv⟩ => mul_nonneg hu hv
  refine mul_le_of_forall_lt_of_nonneg u0 uv0 fun a ha b hb => (le_limsup_iff).2 fun c c_ab => ?_
  refine (((frequently_lt_of_lt_limsup) (mem_Ioo.1 ha).2).and_eventually
 (eventually_lt_of_lt_liminf (mem_Ioo.1 hb).2).and
 hv).mono fun x ⟨xa, ⟨xb, vx⟩⟩ => ?_
  exact c_ab.trans_le (mul_le_mul xa.le xb.le (mem_Ioo.1 hb).1.le ((mem_Ioo.1 ha).1.le.trans xa.le))

/--
lemma `limsup_mul_le` / 引理 `limsup_mul_le`

English:
lemma limsup_mul_le
  statement: (hu : existsᶠ x in f, 0 <= u x) (hv : 0 <=ᶠ[f] v)
  proof: by
  rcases f.eq_or_neBot with rfl | _
  · rw [limsup_bot]; exact bot_le
  have u_0 : 0 <= limsup u f := le_limsup_of_frequently_le hu
  replace h₁ : 0 < limsup u f ∨ limsup v f != ⊤ := h₁.imp_left fun h => lt_of_le_of_ne u_0 h.symm
  replace h₂ : limsup u f != ⊤ ∨ 0 < limsup v f :=
    h₂.imp_right

中文:
引理 limsup_mul_le
  结论: (hu : 存在ᶠ x in f, 0 <= u x) (hv : 0 <=ᶠ[f] v)
  证明: by
  rcases f.eq_or_neBot with rfl | _
  · rw [limsup_bot]; exact bot_le
  have u_0 : 0 <= limsup u f := le_limsup_of_frequently_le hu
  replace h₁ : 0 < limsup u f ∨ limsup v f != ⊤ := h₁.imp_left fun h => lt_of_le_of_ne u_0 h.symm
  replace h₂ : limsup u f != ⊤ ∨ 0 < limsup v f :=
    h₂.imp_right

Depends on / 依赖: bot_le, c_ab, eq_or_neBot, eventually_lt_of_limsup_lt, f.eq_or_neBot, filter_upwards, frequently, h.symm, hv.frequently, imp_left, imp_right, le_limsup_of_frequently_le, le_mul_of_forall_lt, limsup, limsup_bot, limsup_le_iff, lt_of_le_of_ne, replace
-/
lemma limsup_mul_le (hu : existsᶠ x in f, 0 <= u x) (hv : 0 <=ᶠ[f] v)
    (h₁ : limsup u f != 0 ∨ limsup v f != ⊤) (h₂ : limsup u f != ⊤ ∨ limsup v f != 0) :
    limsup (u * v) f <= limsup u f * limsup v f := by
  rcases f.eq_or_neBot with rfl | _
  · rw [limsup_bot]; exact bot_le
  have u_0 : 0 <= limsup u f := le_limsup_of_frequently_le hu
  replace h₁ : 0 < limsup u f ∨ limsup v f != ⊤ := h₁.imp_left fun h => lt_of_le_of_ne u_0 h.symm
  replace h₂ : limsup u f != ⊤ ∨ 0 < limsup v f :=
    h₂.imp_right fun h => lt_of_le_of_ne (le_limsup_of_frequently_le hv.frequently) h.symm
  refine le_mul_of_forall_lt h₁ h₂ fun a a_u b b_v => (limsup_le_iff).2 fun c c_ab => ?_
  filter_upwards [eventually_lt_of_limsup_lt a_u, eventually_lt_of_limsup_lt b_v, hv]
    with x x_a x_b v_0
  apply lt_of_le_of_lt _ c_ab
  rcases lt_or_ge (u x) 0 with hux | hux
  · apply (mul_nonpos_iff.2 (.inr ⟨hux.le, v_0⟩)).trans
    exact mul_nonneg (u_0.trans a_u.le) (v_0.trans x_b.le)
  · exact mul_le_mul x_a.le x_b.le v_0 (hux.trans x_a.le)

/--
lemma `le_liminf_mul` / 引理 `le_liminf_mul`

English:
lemma le_liminf_mul
  given: (hu : 0 <=ᶠ[f] u) (hv : 0 <=ᶠ[f] v)
  proof: by
  apply mul_le_of_forall_lt_of_nonneg ((le_liminf_of_le) hu)
 (le_liminf_of_le) ((hu.and hv).mono fun x ⟨u0, v0⟩ => mul_nonneg u0 v0)
  refine fun a ha b hb => (le_liminf_iff).2 fun c c_ab => ?_
  filter_upwards [eventually_lt_of_lt_liminf (mem_Ioo.1 ha).2,
    eventually_lt_of_lt_liminf (mem_Ioo

中文:
引理 le_liminf_mul
  条件: (hu : 0 <=ᶠ[f] u) (hv : 0 <=ᶠ[f] v)
  证明: by
  apply mul_le_of_forall_lt_of_nonneg ((le_liminf_of_le) hu)
 (le_liminf_of_le) ((hu.and hv).mono fun x ⟨u0, v0⟩ => mul_nonneg u0 v0)
  refine fun a ha b hb => (le_liminf_iff).2 fun c c_ab => ?_
  filter_upwards [eventually_lt_of_lt_liminf (mem_Ioo.1 ha).2,
    eventually_lt_of_lt_liminf (mem_Ioo

Depends on / 依赖: c_ab, c_ab.trans_le, eventually_lt_of_lt_liminf, filter_upwards, hu.and, le.trans, le_liminf_iff, le_liminf_of_le, mem_Ioo, mul_le_mul, mul_le_of_forall_lt_of_nonneg, mul_nonneg, trans_le, xa.le, xb.le
-/
lemma le_liminf_mul (hu : 0 <=ᶠ[f] u) (hv : 0 <=ᶠ[f] v) :
    liminf u f * liminf v f <= liminf (u * v) f := by
  apply mul_le_of_forall_lt_of_nonneg ((le_liminf_of_le) hu)
 (le_liminf_of_le) ((hu.and hv).mono fun x ⟨u0, v0⟩ => mul_nonneg u0 v0)
  refine fun a ha b hb => (le_liminf_iff).2 fun c c_ab => ?_
  filter_upwards [eventually_lt_of_lt_liminf (mem_Ioo.1 ha).2,
    eventually_lt_of_lt_liminf (mem_Ioo.1 hb).2] with x xa xb
  exact c_ab.trans_le (mul_le_mul xa.le xb.le (mem_Ioo.1 hb).1.le ((mem_Ioo.1 ha).1.le.trans xa.le))

/--
lemma `liminf_mul_le` / 引理 `liminf_mul_le`

English:
lemma liminf_mul_le
  statement: [NeBot f] (hu : 0 <=ᶠ[f] u) (hv : 0 <=ᶠ[f] v)
  proof: by
  replace h₁ : 0 < limsup u f ∨ liminf v f != ⊤ := by
    refine h₁.imp_left fun h => lt_of_le_of_ne ?_ h.symm
    exact le_of_eq_of_le (limsup_const 0).symm (limsup_le_limsup hu)
  replace h₂ : limsup u f != ⊤ ∨ 0 < liminf v f := by
    refine h₂.imp_right fun h => lt_of_le_of_ne ?_ h.symm
    e

中文:
引理 liminf_mul_le
  结论: [NeBot f] (hu : 0 <=ᶠ[f] u) (hv : 0 <=ᶠ[f] v)
  证明: by
  replace h₁ : 0 < limsup u f ∨ liminf v f != ⊤ := by
    refine h₁.imp_left fun h => lt_of_le_of_ne ?_ h.symm
    exact le_of_eq_of_le (limsup_const 0).symm (limsup_le_limsup hu)
  replace h₂ : limsup u f != ⊤ ∨ 0 < liminf v f := by
    refine h₂.imp_right fun h => lt_of_le_of_ne ?_ h.symm
    e

Depends on / 依赖: and_eventually, c_ab, eventua, frequently_lt_of_liminf_lt, h.symm, imp_left, imp_right, le_mul_of_forall_lt, le_of_eq_of_le, liminf, liminf_const, liminf_le_iff, liminf_le_liminf, limsup, limsup_const, limsup_le_limsup, lt_of_le_of_ne, replace
-/
lemma liminf_mul_le [NeBot f] (hu : 0 <=ᶠ[f] u) (hv : 0 <=ᶠ[f] v)
    (h₁ : limsup u f != 0 ∨ liminf v f != ⊤) (h₂ : limsup u f != ⊤ ∨ liminf v f != 0) :
    liminf (u * v) f <= limsup u f * liminf v f := by
  replace h₁ : 0 < limsup u f ∨ liminf v f != ⊤ := by
    refine h₁.imp_left fun h => lt_of_le_of_ne ?_ h.symm
    exact le_of_eq_of_le (limsup_const 0).symm (limsup_le_limsup hu)
  replace h₂ : limsup u f != ⊤ ∨ 0 < liminf v f := by
    refine h₂.imp_right fun h => lt_of_le_of_ne ?_ h.symm
    exact le_of_eq_of_le (liminf_const 0).symm (liminf_le_liminf hv)
  refine le_mul_of_forall_lt h₁ h₂ fun a a_u b b_v => (liminf_le_iff).2 fun c c_ab => ?_
  refine (((frequently_lt_of_liminf_lt) b_v).and_eventually <| (eventually_lt_of_limsup_lt a_u).and
 hu.and hv).mono fun x ⟨x_v, x_u, u_0, v_0⟩ => ?_
  exact (mul_le_mul x_u.le x_v.le v_0 (u_0.trans x_u.le)).trans_lt c_ab

end LimInfSup


/--
theorem `continuousAt_add_coe_coe` / 定理 `continuousAt_add_coe_coe`

English:
theorem continuousAt_add_coe_coe
  given: (a b : Real)
  proof: by
  simp only [ContinuousAt, nhds_coe_coe, ← coe_add, tendsto_map'_iff, Function.comp_def,
    tendsto_coe, tendsto_add]

中文:
定理 continuousAt_add_coe_coe
  条件: (a b : 实数)
  证明: by
  simp only [ContinuousAt, nhds_coe_coe, ← coe_add, tendsto_map'_iff, Function.comp_def,
    tendsto_coe, tendsto_add]

Depends on / 依赖: ContinuousAt, Function, Function.comp_def, _iff, coe_add, comp_def, nhds_coe_coe, tendsto_add, tendsto_coe, tendsto_map
-/
theorem continuousAt_add_coe_coe (a b : Real) :
    ContinuousAt (fun p : EReal × EReal => p.1 + p.2) (a, b) := by
  simp only [ContinuousAt, nhds_coe_coe, ← coe_add, tendsto_map'_iff, Function.comp_def,
    tendsto_coe, tendsto_add]

/--
theorem `continuousAt_add_top_coe` / 定理 `continuousAt_add_top_coe`

English:
theorem continuousAt_add_top_coe
  given: (a : Real)
  proof: by
  simp only [ContinuousAt, tendsto_nhds_top_iff_real, top_add_coe]
  refine fun r => ((lt_mem_nhds (coe_lt_top (r - (a - 1)))).prod_nhds
    (lt_mem_nhds <| EReal.coe_lt_coe_iff.2 <| sub_one_lt _)).mono fun _ h => ?_
  simpa only [← coe_add, _root_.sub_add_cancel] using add_lt_add h.1 h.2

中文:
定理 continuousAt_add_top_coe
  条件: (a : 实数)
  证明: by
  simp only [ContinuousAt, tendsto_nhds_top_iff_real, top_add_coe]
  refine fun r => ((lt_mem_nhds (coe_lt_top (r - (a - 1)))).prod_nhds
    (lt_mem_nhds <| EReal.coe_lt_coe_iff.2 <| sub_one_lt _)).mono fun _ h => ?_
  simpa only [← coe_add, _root_.sub_add_cancel] using add_lt_add h.1 h.2

Depends on / 依赖: ContinuousAt, EReal.coe_lt_coe_iff, _root_, _root_.sub_add_cancel, add_lt_add, coe_add, coe_lt_coe_iff, coe_lt_top, lt_mem_nhds, prod_nhds, sub_add_cancel, sub_one_lt, tendsto_nhds_top_iff_real, top_add_coe
-/
theorem continuousAt_add_top_coe (a : Real) :
    ContinuousAt (fun p : EReal × EReal => p.1 + p.2) (⊤, a) := by
  simp only [ContinuousAt, tendsto_nhds_top_iff_real, top_add_coe]
  refine fun r => ((lt_mem_nhds (coe_lt_top (r - (a - 1)))).prod_nhds
    (lt_mem_nhds <| EReal.coe_lt_coe_iff.2 <| sub_one_lt _)).mono fun _ h => ?_
  simpa only [← coe_add, _root_.sub_add_cancel] using add_lt_add h.1 h.2

/--
theorem `continuousAt_add_coe_top` / 定理 `continuousAt_add_coe_top`

English:
theorem continuousAt_add_coe_top
  given: (a : Real)
  proof: by
  simpa only [add_comm, Function.comp_def, ContinuousAt, Prod.swap]
    using Tendsto.comp (continuousAt_add_top_coe a) (continuous_swap.tendsto ((a : EReal), ⊤))

中文:
定理 continuousAt_add_coe_top
  条件: (a : 实数)
  证明: by
  simpa only [add_comm, Function.comp_def, ContinuousAt, Prod.swap]
    using Tendsto.comp (continuousAt_add_top_coe a) (continuous_swap.tendsto ((a : EReal), ⊤))

Depends on / 依赖: ContinuousAt, Function, Function.comp_def, Prod.swap, Tendsto, Tendsto.comp, add_comm, comp_def, continuousAt_add_top_coe, continuous_swap, continuous_swap.tendsto, tendsto
-/
theorem continuousAt_add_coe_top (a : Real) :
    ContinuousAt (fun p : EReal × EReal => p.1 + p.2) (a, ⊤) := by
  simpa only [add_comm, Function.comp_def, ContinuousAt, Prod.swap]
    using Tendsto.comp (continuousAt_add_top_coe a) (continuous_swap.tendsto ((a : EReal), ⊤))

/--
theorem `continuousAt_add_top_top` / 定理 `continuousAt_add_top_top`

English:
theorem continuousAt_add_top_top
  statement: ContinuousAt (fun p : EReal × EReal => p.1 + p.2) (⊤, ⊤)
  proof: by
  simp only [ContinuousAt, tendsto_nhds_top_iff_real, top_add_top]
  refine fun r => ((lt_mem_nhds (coe_lt_top 0)).prod_nhds
    (lt_mem_nhds <| coe_lt_top r)).mono fun _ h => ?_
  simpa only [coe_zero, zero_add] using add_lt_add h.1 h.2

中文:
定理 continuousAt_add_top_top
  结论: ContinuousAt (fun p : E实数 × E实数 => p.1 + p.2) (⊤, ⊤)
  证明: by
  simp only [ContinuousAt, tendsto_nhds_top_iff_real, top_add_top]
  refine fun r => ((lt_mem_nhds (coe_lt_top 0)).prod_nhds
    (lt_mem_nhds <| coe_lt_top r)).mono fun _ h => ?_
  simpa only [coe_zero, zero_add] using add_lt_add h.1 h.2

Depends on / 依赖: ContinuousAt, add_lt_add, coe_lt_top, coe_zero, lt_mem_nhds, prod_nhds, tendsto_nhds_top_iff_real, top_add_top, zero_add
-/
theorem continuousAt_add_top_top : ContinuousAt (fun p : EReal × EReal => p.1 + p.2) (⊤, ⊤) := by
  simp only [ContinuousAt, tendsto_nhds_top_iff_real, top_add_top]
  refine fun r => ((lt_mem_nhds (coe_lt_top 0)).prod_nhds
    (lt_mem_nhds <| coe_lt_top r)).mono fun _ h => ?_
  simpa only [coe_zero, zero_add] using add_lt_add h.1 h.2

/--
theorem `continuousAt_add_bot_coe` / 定理 `continuousAt_add_bot_coe`

English:
theorem continuousAt_add_bot_coe
  given: (a : Real)
  proof: by
  simp only [ContinuousAt, tendsto_nhds_bot_iff_real, bot_add]
  refine fun r => ((gt_mem_nhds (bot_lt_coe (r - (a + 1)))).prod_nhds
    (gt_mem_nhds <| EReal.coe_lt_coe_iff.2 <| lt_add_one _)).mono fun _ h => ?_
  simpa only [← coe_add, _root_.sub_add_cancel] using add_lt_add h.1 h.2

中文:
定理 continuousAt_add_bot_coe
  条件: (a : 实数)
  证明: by
  simp only [ContinuousAt, tendsto_nhds_bot_iff_real, bot_add]
  refine fun r => ((gt_mem_nhds (bot_lt_coe (r - (a + 1)))).prod_nhds
    (gt_mem_nhds <| EReal.coe_lt_coe_iff.2 <| lt_add_one _)).mono fun _ h => ?_
  simpa only [← coe_add, _root_.sub_add_cancel] using add_lt_add h.1 h.2

Depends on / 依赖: ContinuousAt, EReal.coe_lt_coe_iff, _root_, _root_.sub_add_cancel, add_lt_add, bot_add, bot_lt_coe, coe_add, coe_lt_coe_iff, gt_mem_nhds, lt_add_one, prod_nhds, sub_add_cancel, tendsto_nhds_bot_iff_real
-/
theorem continuousAt_add_bot_coe (a : Real) :
    ContinuousAt (fun p : EReal × EReal => p.1 + p.2) (⊥, a) := by
  simp only [ContinuousAt, tendsto_nhds_bot_iff_real, bot_add]
  refine fun r => ((gt_mem_nhds (bot_lt_coe (r - (a + 1)))).prod_nhds
    (gt_mem_nhds <| EReal.coe_lt_coe_iff.2 <| lt_add_one _)).mono fun _ h => ?_
  simpa only [← coe_add, _root_.sub_add_cancel] using add_lt_add h.1 h.2

/--
theorem `continuousAt_add_coe_bot` / 定理 `continuousAt_add_coe_bot`

English:
theorem continuousAt_add_coe_bot
  given: (a : Real)
  proof: by
  simpa only [add_comm, Function.comp_def, ContinuousAt, Prod.swap]
    using Tendsto.comp (continuousAt_add_bot_coe a) (continuous_swap.tendsto ((a : EReal), ⊥))

中文:
定理 continuousAt_add_coe_bot
  条件: (a : 实数)
  证明: by
  simpa only [add_comm, Function.comp_def, ContinuousAt, Prod.swap]
    using Tendsto.comp (continuousAt_add_bot_coe a) (continuous_swap.tendsto ((a : EReal), ⊥))

Depends on / 依赖: ContinuousAt, Function, Function.comp_def, Prod.swap, Tendsto, Tendsto.comp, add_comm, comp_def, continuousAt_add_bot_coe, continuous_swap, continuous_swap.tendsto, tendsto
-/
theorem continuousAt_add_coe_bot (a : Real) :
    ContinuousAt (fun p : EReal × EReal => p.1 + p.2) (a, ⊥) := by
  simpa only [add_comm, Function.comp_def, ContinuousAt, Prod.swap]
    using Tendsto.comp (continuousAt_add_bot_coe a) (continuous_swap.tendsto ((a : EReal), ⊥))

/--
theorem `continuousAt_add_bot_bot` / 定理 `continuousAt_add_bot_bot`

English:
theorem continuousAt_add_bot_bot
  statement: ContinuousAt (fun p : EReal × EReal => p.1 + p.2) (⊥, ⊥)
  proof: by
  simp only [ContinuousAt, tendsto_nhds_bot_iff_real, bot_add]
  refine fun r => ((gt_mem_nhds (bot_lt_coe 0)).prod_nhds
    (gt_mem_nhds <| bot_lt_coe r)).mono fun _ h => ?_
  simpa only [coe_zero, zero_add] using add_lt_add h.1 h.2

中文:
定理 continuousAt_add_bot_bot
  结论: ContinuousAt (fun p : E实数 × E实数 => p.1 + p.2) (⊥, ⊥)
  证明: by
  simp only [ContinuousAt, tendsto_nhds_bot_iff_real, bot_add]
  refine fun r => ((gt_mem_nhds (bot_lt_coe 0)).prod_nhds
    (gt_mem_nhds <| bot_lt_coe r)).mono fun _ h => ?_
  simpa only [coe_zero, zero_add] using add_lt_add h.1 h.2

Depends on / 依赖: ContinuousAt, add_lt_add, bot_add, bot_lt_coe, coe_zero, gt_mem_nhds, prod_nhds, tendsto_nhds_bot_iff_real, zero_add
-/
theorem continuousAt_add_bot_bot : ContinuousAt (fun p : EReal × EReal => p.1 + p.2) (⊥, ⊥) := by
  simp only [ContinuousAt, tendsto_nhds_bot_iff_real, bot_add]
  refine fun r => ((gt_mem_nhds (bot_lt_coe 0)).prod_nhds
    (gt_mem_nhds <| bot_lt_coe r)).mono fun _ h => ?_
  simpa only [coe_zero, zero_add] using add_lt_add h.1 h.2

/--
theorem `continuousAt_add` / 定理 `continuousAt_add`

English:
theorem continuousAt_add
  given: {p : EReal × EReal} (h : p.1 != ⊤ ∨ p.2 != ⊥) (h' : p.1 != ⊥ ∨ p.2 != ⊤)
  proof: by
  rcases p with ⟨x, y⟩
  induction x <;> induction y
  · exact continuousAt_add_bot_bot
  · exact continuousAt_add_bot_coe _
  · simp at h'
  · exact continuousAt_add_coe_bot _
  · exact continuousAt_add_coe_coe _ _
  · exact continuousAt_add_coe_top _
  · simp at h
  · exact continuousAt_add_top

中文:
定理 continuousAt_add
  条件: {p : E实数 × E实数} (h : p.1 != ⊤ ∨ p.2 != ⊥) (h' : p.1 != ⊥ ∨ p.2 != ⊤)
  证明: by
  rcases p with ⟨x, y⟩
  induction x <;> induction y
  · exact continuousAt_add_bot_bot
  · exact continuousAt_add_bot_coe _
  · simp at h'
  · exact continuousAt_add_coe_bot _
  · exact continuousAt_add_coe_coe _ _
  · exact continuousAt_add_coe_top _
  · simp at h
  · exact continuousAt_add_top

Depends on / 依赖: continuousAt_add_bot_bot, continuousAt_add_bot_coe, continuousAt_add_coe_bot, continuousAt_add_coe_coe, continuousAt_add_coe_top, continuousAt_add_top_coe, continuousAt_add_top_top
-/
theorem continuousAt_add {p : EReal × EReal} (h : p.1 != ⊤ ∨ p.2 != ⊥) (h' : p.1 != ⊥ ∨ p.2 != ⊤) :
    ContinuousAt (fun p : EReal × EReal => p.1 + p.2) p := by
  rcases p with ⟨x, y⟩
  induction x <;> induction y
  · exact continuousAt_add_bot_bot
  · exact continuousAt_add_bot_coe _
  · simp at h'
  · exact continuousAt_add_coe_bot _
  · exact continuousAt_add_coe_coe _ _
  · exact continuousAt_add_coe_top _
  · simp at h
  · exact continuousAt_add_top_coe _
  · exact continuousAt_add_top_top

/--
lemma `lowerSemicontinuous_add` / 引理 `lowerSemicontinuous_add`

English:
lemma lowerSemicontinuous_add
  statement: LowerSemicontinuous fun p : EReal × EReal => p.1 + p.2
  proof: by
  intro x y
  by_cases hx₁ : x.1 = ⊥
  · simp [hx₁]
  by_cases hx₂ : x.2 = ⊥
  · simp [hx₂]
.lowerSemicontinuousAt _ · exact continuousAt_add (.inr hx₂) (.inl hx₁)

中文:
引理 lowerSemicontinuous_add
  结论: LowerSemicontinuous fun p : E实数 × E实数 => p.1 + p.2
  证明: by
  intro x y
  by_cases hx₁ : x.1 = ⊥
  · simp [hx₁]
  by_cases hx₂ : x.2 = ⊥
  · simp [hx₂]
.lowerSemicontinuousAt _ · exact continuousAt_add (.inr hx₂) (.inl hx₁)

Depends on / 依赖: continuousAt_add, lowerSemicontinuousAt
-/
lemma lowerSemicontinuous_add : LowerSemicontinuous fun p : EReal × EReal => p.1 + p.2 := by
  intro x y
  by_cases hx₁ : x.1 = ⊥
  · simp [hx₁]
  by_cases hx₂ : x.2 = ⊥
  · simp [hx₂]
.lowerSemicontinuousAt _ · exact continuousAt_add (.inr hx₂) (.inl hx₁)

/-! ### Continuity of multiplication -/


/--
lemma `continuousAt_mul_swap` / 引理 `continuousAt_mul_swap`

English:
lemma continuousAt_mul_swap
  statement: {a b : EReal}
  proof: by
  convert! h.comp continuous_swap.continuousAt (x := (b, a))
  simp [mul_comm]

中文:
引理 continuousAt_mul_swap
  结论: {a b : E实数}
  证明: by
  convert! h.comp continuous_swap.continuousAt (x := (b, a))
  simp [mul_comm]
-/
private lemma continuousAt_mul_swap {a b : EReal}
    (h : ContinuousAt (fun p : EReal × EReal => p.1 * p.2) (a, b)) :
    ContinuousAt (fun p : EReal × EReal => p.1 * p.2) (b, a) := by
  convert! h.comp continuous_swap.continuousAt (x := (b, a))
  simp [mul_comm]

/--
lemma `continuousAt_mul_symm1` / 引理 `continuousAt_mul_symm1`

English:
lemma continuousAt_mul_symm1
  statement: {a b : EReal}
  proof: by
  have : (fun p : EReal × EReal => p.1 * p.2) = (fun x : EReal => -x)
      ∘ (fun p : EReal × EReal => p.1 * p.2) ∘ (fun p : EReal × EReal => (-p.1, p.2)) := by
    ext p
    simp
  rw [this]
  apply ContinuousAt.comp (Continuous.continuousAt continuous_neg)
 ContinuousAt.comp _ (ContinuousAt.pr

中文:
引理 continuousAt_mul_symm1
  结论: {a b : E实数}
  证明: by
  have : (fun p : EReal × EReal => p.1 * p.2) = (fun x : EReal => -x)
      ∘ (fun p : EReal × EReal => p.1 * p.2) ∘ (fun p : EReal × EReal => (-p.1, p.2)) := by
    ext p
    simp
  rw [this]
  apply ContinuousAt.comp (Continuous.continuousAt continuous_neg)
 ContinuousAt.comp _ (ContinuousAt.pr
-/
private lemma continuousAt_mul_symm1 {a b : EReal}
    (h : ContinuousAt (fun p : EReal × EReal => p.1 * p.2) (a, b)) :
    ContinuousAt (fun p : EReal × EReal => p.1 * p.2) (-a, b) := by
  have : (fun p : EReal × EReal => p.1 * p.2) = (fun x : EReal => -x)
      ∘ (fun p : EReal × EReal => p.1 * p.2) ∘ (fun p : EReal × EReal => (-p.1, p.2)) := by
    ext p
    simp
  rw [this]
  apply ContinuousAt.comp (Continuous.continuousAt continuous_neg)
 ContinuousAt.comp _ (ContinuousAt.prodMap (Continuous.continuousAt continuous_neg)
      (Continuous.continuousAt continuous_id))
  simp [h]

/--
lemma `continuousAt_mul_symm2` / 引理 `continuousAt_mul_symm2`

English:
lemma continuousAt_mul_symm2
  statement: {a b : EReal}
  proof: continuousAt_mul_swap (continuousAt_mul_symm1 (continuousAt_mul_swap h))

中文:
引理 continuousAt_mul_symm2
  结论: {a b : E实数}
  证明: continuousAt_mul_swap (continuousAt_mul_symm1 (continuousAt_mul_swap h))
-/
private lemma continuousAt_mul_symm2 {a b : EReal}
    (h : ContinuousAt (fun p : EReal × EReal => p.1 * p.2) (a, b)) :
    ContinuousAt (fun p : EReal × EReal => p.1 * p.2) (a, -b) :=
  continuousAt_mul_swap (continuousAt_mul_symm1 (continuousAt_mul_swap h))

/--
lemma `continuousAt_mul_symm3` / 引理 `continuousAt_mul_symm3`

English:
lemma continuousAt_mul_symm3
  statement: {a b : EReal}
  proof: continuousAt_mul_symm1 (continuousAt_mul_symm2 h)

中文:
引理 continuousAt_mul_symm3
  结论: {a b : E实数}
  证明: continuousAt_mul_symm1 (continuousAt_mul_symm2 h)
-/
private lemma continuousAt_mul_symm3 {a b : EReal}
    (h : ContinuousAt (fun p : EReal × EReal => p.1 * p.2) (a, b)) :
    ContinuousAt (fun p : EReal × EReal => p.1 * p.2) (-a, -b) :=
  continuousAt_mul_symm1 (continuousAt_mul_symm2 h)

/--
lemma `continuousAt_mul_coe_coe` / 引理 `continuousAt_mul_coe_coe`

English:
lemma continuousAt_mul_coe_coe
  given: (a b : Real)
  proof: by
  simp [ContinuousAt, EReal.nhds_coe_coe, ← EReal.coe_mul, Filter.tendsto_map'_iff,
    Function.comp_def, EReal.tendsto_coe, tendsto_mul]

中文:
引理 continuousAt_mul_coe_coe
  条件: (a b : 实数)
  证明: by
  simp [ContinuousAt, EReal.nhds_coe_coe, ← EReal.coe_mul, Filter.tendsto_map'_iff,
    Function.comp_def, EReal.tendsto_coe, tendsto_mul]
-/
private lemma continuousAt_mul_coe_coe (a b : Real) :
    ContinuousAt (fun p : EReal × EReal => p.1 * p.2) (a, b) := by
  simp [ContinuousAt, EReal.nhds_coe_coe, ← EReal.coe_mul, Filter.tendsto_map'_iff,
    Function.comp_def, EReal.tendsto_coe, tendsto_mul]

/--
lemma `continuousAt_mul_top_top` / 引理 `continuousAt_mul_top_top`

English:
lemma continuousAt_mul_top_top
  proof: by
  simp only [ContinuousAt, EReal.top_mul_top, EReal.tendsto_nhds_top_iff_real]
  intro x
  rw [_root_.eventually_nhds_iff]
  use (Set.Ioi ((max x 0) : EReal)) ×ˢ (Set.Ioi 1)
  split_ands
  · intro p p_in_prod
    simp only [Set.mem_prod, Set.mem_Ioi, max_lt_iff] at p_in_prod
    rcases p_in_prod 

中文:
引理 continuousAt_mul_top_top
  证明: by
  simp only [ContinuousAt, EReal.top_mul_top, EReal.tendsto_nhds_top_iff_real]
  intro x
  rw [_root_.eventually_nhds_iff]
  use (Set.Ioi ((max x 0) : EReal)) ×ˢ (Set.Ioi 1)
  split_ands
  · intro p p_in_prod
    simp only [Set.mem_prod, Set.mem_Ioi, max_lt_iff] at p_in_prod
    rcases p_in_prod 
-/
private lemma continuousAt_mul_top_top :
    ContinuousAt (fun p : EReal × EReal => p.1 * p.2) (⊤, ⊤) := by
  simp only [ContinuousAt, EReal.top_mul_top, EReal.tendsto_nhds_top_iff_real]
  intro x
  rw [_root_.eventually_nhds_iff]
  use (Set.Ioi ((max x 0) : EReal)) ×ˢ (Set.Ioi 1)
  split_ands
  · intro p p_in_prod
    simp only [Set.mem_prod, Set.mem_Ioi, max_lt_iff] at p_in_prod
    rcases p_in_prod with ⟨⟨p1_gt_x, p1_pos⟩, p2_gt_1⟩
    have := mul_le_mul_of_nonneg_left (le_of_lt p2_gt_1) (le_of_lt p1_pos)
    rw [mul_one p.1] at this
    exact lt_of_lt_of_le p1_gt_x this
  · exact IsOpen.prod isOpen_Ioi isOpen_Ioi
  · simp
  · rw [Set.mem_Ioi, ← EReal.coe_one]; exact EReal.coe_lt_top 1

/--
lemma `continuousAt_mul_top_pos` / 引理 `continuousAt_mul_top_pos`

English:
lemma continuousAt_mul_top_pos
  given: {a : Real} (h : 0 < a)
  proof: by
  simp only [ContinuousAt, EReal.top_mul_coe_of_pos h, EReal.tendsto_nhds_top_iff_real]
  intro x
  rw [_root_.eventually_nhds_iff]
  use (Set.Ioi ((2 * (max (x + 1) 0) / a : Real) : EReal)) ×ˢ (Set.Ioi ((a / 2 : Real) : EReal))
  split_ands
  · intro p p_in_prod
    simp only [Set.mem_prod, Set.

中文:
引理 continuousAt_mul_top_pos
  条件: {a : 实数} (h : 0 < a)
  证明: by
  simp only [ContinuousAt, EReal.top_mul_coe_of_pos h, EReal.tendsto_nhds_top_iff_real]
  intro x
  rw [_root_.eventually_nhds_iff]
  use (Set.Ioi ((2 * (max (x + 1) 0) / a : Real) : EReal)) ×ˢ (Set.Ioi ((a / 2 : Real) : EReal))
  split_ands
  · intro p p_in_prod
    simp only [Set.mem_prod, Set.
-/
private lemma continuousAt_mul_top_pos {a : Real} (h : 0 < a) :
    ContinuousAt (fun p : EReal × EReal => p.1 * p.2) (⊤, a) := by
  simp only [ContinuousAt, EReal.top_mul_coe_of_pos h, EReal.tendsto_nhds_top_iff_real]
  intro x
  rw [_root_.eventually_nhds_iff]
  use (Set.Ioi ((2 * (max (x + 1) 0) / a : Real) : EReal)) ×ˢ (Set.Ioi ((a / 2 : Real) : EReal))
  split_ands
  · intro p p_in_prod
    simp only [Set.mem_prod, Set.mem_Ioi] at p_in_prod
    rcases p_in_prod with ⟨p1_gt, p2_gt⟩
    have p1_pos : 0 < p.1 := by
      apply lt_of_le_of_lt _ p1_gt
      rw [EReal.coe_nonneg]
      apply mul_nonneg _ (le_of_lt (inv_pos_of_pos h))
      simp only [Nat.ofNat_pos, mul_nonneg_iff_of_pos_left, le_max_iff, le_refl, or_true]
    have a2_pos : 0 < ((a / 2 : Real) : EReal) := by rw [EReal.coe_pos]; linarith
    have lock := mul_le_mul_of_nonneg_right (le_of_lt p1_gt) (le_of_lt a2_pos)
    have key := mul_le_mul_of_nonneg_left (le_of_lt p2_gt) (le_of_lt p1_pos)
    replace lock := le_trans lock key
    apply lt_of_lt_of_le _ lock
    rw [← EReal.coe_mul]; rw [EReal.coe_lt_coe_iff]; rw [_root_.div_mul_div_comm]; rw [mul_comm]; rw [← _root_.div_mul_div_comm]; rw [mul_div_right_comm]
    simp only [ne_eq, Ne.symm (ne_of_lt h), not_false_eq_true, _root_.div_self, OfNat.ofNat_ne_zero,
      one_mul, lt_max_iff, lt_add_iff_pos_right, zero_lt_one, true_or]
  · exact IsOpen.prod isOpen_Ioi isOpen_Ioi
  · simp
  · simp [h]

/--
lemma `continuousAt_mul_top_ne_zero` / 引理 `continuousAt_mul_top_ne_zero`

English:
lemma continuousAt_mul_top_ne_zero
  given: {a : Real} (h : a != 0)
  proof: by
  rcases lt_or_gt_of_ne h with a_neg | a_pos
  · exact neg_neg a ▸ continuousAt_mul_symm2 (continuousAt_mul_top_pos (neg_pos.2 a_neg))
  · exact continuousAt_mul_top_pos a_pos

中文:
引理 continuousAt_mul_top_ne_zero
  条件: {a : 实数} (h : a != 0)
  证明: by
  rcases lt_or_gt_of_ne h with a_neg | a_pos
  · exact neg_neg a ▸ continuousAt_mul_symm2 (continuousAt_mul_top_pos (neg_pos.2 a_neg))
  · exact continuousAt_mul_top_pos a_pos
-/
private lemma continuousAt_mul_top_ne_zero {a : Real} (h : a != 0) :
    ContinuousAt (fun p : EReal × EReal => p.1 * p.2) (⊤, a) := by
  rcases lt_or_gt_of_ne h with a_neg | a_pos
  · exact neg_neg a ▸ continuousAt_mul_symm2 (continuousAt_mul_top_pos (neg_pos.2 a_neg))
  · exact continuousAt_mul_top_pos a_pos

/--
theorem `continuousAt_mul` / 定理 `continuousAt_mul`

English:
theorem continuousAt_mul
  statement: {p : EReal × EReal} (h₁ : p.1 != 0 ∨ p.2 != ⊥)
  proof: by
  rcases p with ⟨x, y⟩
  induction x <;> induction y
  · exact continuousAt_mul_symm3 continuousAt_mul_top_top
  · simp only [ne_eq, not_true_eq_false, EReal.coe_eq_zero, false_or] at h₃
    exact continuousAt_mul_symm1 (continuousAt_mul_top_ne_zero h₃)
  · exact EReal.neg_top ▸ continuousAt_mul_

中文:
定理 continuousAt_mul
  结论: {p : E实数 × E实数} (h₁ : p.1 != 0 ∨ p.2 != ⊥)
  证明: by
  rcases p with ⟨x, y⟩
  induction x <;> induction y
  · exact continuousAt_mul_symm3 continuousAt_mul_top_top
  · simp only [ne_eq, not_true_eq_false, EReal.coe_eq_zero, false_or] at h₃
    exact continuousAt_mul_symm1 (continuousAt_mul_top_ne_zero h₃)
  · exact EReal.neg_top ▸ continuousAt_mul_

Depends on / 依赖: EReal.coe_eq_zero, EReal.neg_top, coe_eq_zero, continuousAt_m, continuousAt_mul_swap, continuousAt_mul_symm1, continuousAt_mul_symm2, continuousAt_mul_symm3, continuousAt_mul_top_ne_zero, continuousAt_mul_top_top, false_or, ne_eq, neg_top, not_true_eq_false, or_false
-/
theorem continuousAt_mul {p : EReal × EReal} (h₁ : p.1 != 0 ∨ p.2 != ⊥)
    (h₂ : p.1 != 0 ∨ p.2 != ⊤) (h₃ : p.1 != ⊥ ∨ p.2 != 0) (h₄ : p.1 != ⊤ ∨ p.2 != 0) :
    ContinuousAt (fun p : EReal × EReal => p.1 * p.2) p := by
  rcases p with ⟨x, y⟩
  induction x <;> induction y
  · exact continuousAt_mul_symm3 continuousAt_mul_top_top
  · simp only [ne_eq, not_true_eq_false, EReal.coe_eq_zero, false_or] at h₃
    exact continuousAt_mul_symm1 (continuousAt_mul_top_ne_zero h₃)
  · exact EReal.neg_top ▸ continuousAt_mul_symm1 continuousAt_mul_top_top
  · simp only [ne_eq, EReal.coe_eq_zero, not_true_eq_false, or_false] at h₁
    exact continuousAt_mul_symm2 (continuousAt_mul_swap (continuousAt_mul_top_ne_zero h₁))
  · exact continuousAt_mul_coe_coe _ _
  · simp only [ne_eq, EReal.coe_eq_zero, not_true_eq_false, or_false] at h₂
    exact continuousAt_mul_swap (continuousAt_mul_top_ne_zero h₂)
  · exact continuousAt_mul_symm2 continuousAt_mul_top_top
  · simp only [ne_eq, not_true_eq_false, EReal.coe_eq_zero, false_or] at h₄
    exact continuousAt_mul_top_ne_zero h₄
  · exact continuousAt_mul_top_top

variable {a b : EReal}

/--
theorem `tendsto_mul` / 定理 `tendsto_mul`

English:
theorem tendsto_mul
  statement: (h₁ : a != 0 ∨ b != ⊥) (h₂ : a != 0 ∨ b != ⊤) (h₃ : a != ⊥ ∨ b != 0)
  proof: (continuousAt_mul h₁ h₂ h₃ h₄).tendsto

中文:
定理 tendsto_mul
  结论: (h₁ : a != 0 ∨ b != ⊥) (h₂ : a != 0 ∨ b != ⊤) (h₃ : a != ⊥ ∨ b != 0)
  证明: (continuousAt_mul h₁ h₂ h₃ h₄).tendsto
-/
protected theorem tendsto_mul (h₁ : a != 0 ∨ b != ⊥) (h₂ : a != 0 ∨ b != ⊤) (h₃ : a != ⊥ ∨ b != 0)
    (h₄ : a != ⊤ ∨ b != 0) :
    Tendsto (fun p : EReal × EReal => p.1 * p.2) (𝓝 (a, b)) (𝓝 (a * b)) :=
  (continuousAt_mul h₁ h₂ h₃ h₄).tendsto

/--
theorem `Tendsto.mul` / 定理 `Tendsto.mul`

English:
theorem Tendsto.mul
  statement: {f : Filter α} {ma : α -> EReal} {mb : α -> EReal} {a b : EReal}
  proof: (EReal.tendsto_mul h₁ h₂ h₃ h₄).comp (hma.prodMk_nhds hmb)

中文:
定理 Tendsto.mul
  结论: {f : Filter α} {ma : α -> E实数} {mb : α -> E实数} {a b : E实数}
  证明: (EReal.tendsto_mul h₁ h₂ h₃ h₄).comp (hma.prodMk_nhds hmb)
-/
protected theorem Tendsto.mul {f : Filter α} {ma : α -> EReal} {mb : α -> EReal} {a b : EReal}
    (hma : Tendsto ma f (𝓝 a)) (hmb : Tendsto mb f (𝓝 b)) (h₁ : a != 0 ∨ b != ⊥)
    (h₂ : a != 0 ∨ b != ⊤) (h₃ : a != ⊥ ∨ b != 0) (h₄ : a != ⊤ ∨ b != 0) :
    Tendsto (fun x => ma x * mb x) f (𝓝 (a * b)) :=
  (EReal.tendsto_mul h₁ h₂ h₃ h₄).comp (hma.prodMk_nhds hmb)

/--
theorem `Tendsto.const_mul` / 定理 `Tendsto.const_mul`

English:
theorem Tendsto.const_mul
  statement: {f : Filter α} {m : α -> EReal} {a b : EReal}
  proof: by_cases (fun (this : a = 0) => by simp [this, tendsto_const_nhds])
    fun ha : a != 0 => EReal.Tendsto.mul tendsto_const_nhds hm (Or.inl ha) (Or.inl ha) h₁ h₂

中文:
定理 Tendsto.const_mul
  结论: {f : Filter α} {m : α -> E实数} {a b : E实数}
  证明: by_cases (fun (this : a = 0) => by simp [this, tendsto_const_nhds])
    fun ha : a != 0 => EReal.Tendsto.mul tendsto_const_nhds hm (Or.inl ha) (Or.inl ha) h₁ h₂
-/
protected theorem Tendsto.const_mul {f : Filter α} {m : α -> EReal} {a b : EReal}
    (hm : Tendsto m f (𝓝 b)) (h₁ : a != ⊥ ∨ b != 0) (h₂ : a != ⊤ ∨ b != 0) :
    Tendsto (fun b => a * m b) f (𝓝 (a * b)) :=
  by_cases (fun (this : a = 0) => by simp [this, tendsto_const_nhds])
    fun ha : a != 0 => EReal.Tendsto.mul tendsto_const_nhds hm (Or.inl ha) (Or.inl ha) h₁ h₂

/--
theorem `Tendsto.mul_const` / 定理 `Tendsto.mul_const`

English:
theorem Tendsto.mul_const
  statement: {f : Filter α} {m : α -> EReal} {a b : EReal}
  proof: by
  simpa only [mul_comm] using EReal.Tendsto.const_mul hm h₁.symm h₂.symm

中文:
定理 Tendsto.mul_const
  结论: {f : Filter α} {m : α -> E实数} {a b : E实数}
  证明: by
  simpa only [mul_comm] using EReal.Tendsto.const_mul hm h₁.symm h₂.symm
-/
protected theorem Tendsto.mul_const {f : Filter α} {m : α -> EReal} {a b : EReal}
    (hm : Tendsto m f (𝓝 a)) (h₁ : a != 0 ∨ b != ⊥) (h₂ : a != 0 ∨ b != ⊤) :
    Tendsto (fun x => m x * b) f (𝓝 (a * b)) := by
  simpa only [mul_comm] using EReal.Tendsto.const_mul hm h₁.symm h₂.symm

end EReal
