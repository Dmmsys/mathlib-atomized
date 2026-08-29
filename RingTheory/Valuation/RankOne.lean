/-
Copyright (c) 2024 María Inés de Frutos-Fernández. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: María Inés de Frutos-Fernández, Filippo A. E. Nuccio
-/
module

public import Mathlib.Algebra.Order.Group.Units
public import Mathlib.Algebra.Order.GroupWithZero.WithZero
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Data.Real.Embedding
public import Mathlib.RingTheory.Valuation.ValuativeRel.Basic
public import Mathlib.Combinatorics.Matroid.Init
public import Mathlib.Data.Sym.Sym2
public import Mathlib.Tactic.NormNum.GCD
public import Mathlib.Tactic.Positivity

/-!
# Rank one valuations

We define rank one valuations.

## Main Definitions
* `RankOne` : A valuation has rank one if it is nontrivial and its image (defined as
  `MonoidWithZeroHom.valueGroup₀ v`) is contained in `ℝ≥0`. Note that this class includes the data
  of an inclusion morphism `MonoidWithZeroHom.valueGroup₀ v → ℝ≥0`.
* `RankOne.restrict_RankOne` is the `RankOne` instance for the restriction of a valuation to its
  image, as defined in

## Tags

valuation, rank one
-/

@[expose] public section

noncomputable section

open Function Multiplicative MonoidWithZeroHom MonoidWithZeroHom.ValueGroup₀

open scoped NNReal

variable {R Γ₀ : Type*} [Ring R] [LinearOrderedCommGroupWithZero Γ₀]

namespace Valuation

/--
Definition of `RankLeOne` / `RankLeOne` 的定义

English:
class RankLeOne
  parameters: (v : Valuation R Γ₀)
  axioms and operations (2):
    - hom'((v)) : ValueGroup₀ (.ofClass v) ->*₀ Real>=0
    - strictMono' : StrictMono hom'

中文:
类 秩不超过一
  参数: (v : 赋值 R Γ₀)
  公理与运算 (2 个):
    - hom'((v)) : ValueGroup₀ (.ofClass v) ->*₀ 实数>=0
    - strictMono' : 严格递增 hom'
-/
class RankLeOne (v : Valuation R Γ₀) where
  /-- The inclusion morphism from `Γ₀` to `ℝ≥0`. -/
  hom' (v) : ValueGroup₀ (.ofClass v) ->*₀ Real>=0
  strictMono' : StrictMono hom'

/--
Definition of `RankOne` / `RankOne` 的定义

English:
class RankOne
  parameters: (v : Valuation R Γ₀)
  extends: RankLeOne v, Valuation.IsNontrivial v
  (no additional axioms)

中文:
类 秩一
  参数: (v : 赋值 R Γ₀)
  继承: 秩不超过一 v, 赋值.是非平凡 v
  (无附加公理)
-/
class RankOne (v : Valuation R Γ₀) extends RankLeOne v, Valuation.IsNontrivial v

open WithZero

/--
lemma `nonempty_rankOne_iff_mulArchimedean` / 引理 `nonempty_rankOne_iff_mulArchimedean`

English:
lemma nonempty_rankOne_iff_mulArchimedean
  given: {v : Valuation R Γ₀} [v.IsNontrivial]
  proof: by
  constructor
  · intro h
    obtain hv := Nonempty.some h
    exact MulArchimedean.comap hv.hom'.toMonoidHom hv.strictMono'
  · intro _
    obtain ⟨f, hf⟩ :=
      Archimedean.exists_orderAddMonoidHom_real_injective (Additive (ValueGroup₀ (.ofClass v))ˣ)
    let e := AddMonoidHom.toMultiplicativ

中文:
引理 nonempty_rankOne_iff_mulArchimedean
  条件: {v : 赋值 R Γ₀} [v.是非平凡]
  证明: by
  constructor
  · intro h
    obtain hv := Nonempty.some h
    exact MulArchimedean.comap hv.hom'.toMonoidHom hv.strictMono'
  · intro _
    obtain ⟨f, hf⟩ :=
      Archimedean.exists_orderAddMonoidHom_real_injective (Additive (ValueGroup₀ (.ofClass v))ˣ)
    let e := AddMonoidHom.toMultiplicativ

Depends on / 依赖: AddMonoidHom, AddMonoidHom.coe_coe, AddMonoidHom.coe_toMultiplicativeRight, AddMonoidHom.toMultiplicativeRight, Additive, Archimedean, Archimedean.exists_orderAddMonoidHom_real_injective, MulArchimedean, MulArchimedean.comap, Nonempty, Nonempty.some, StrictMono, coe_coe, coe_toMultiplicativeRight, exists_orderAddMonoidHom_real_injective, hv.hom, hv.strictMono, ofClass, strictMono, toMonoidHom
-/
lemma nonempty_rankOne_iff_mulArchimedean {v : Valuation R Γ₀} [v.IsNontrivial] :
    Nonempty v.RankOne ↔ MulArchimedean (ValueGroup₀ (.ofClass v)) := by
  constructor
  · intro h
    obtain hv := Nonempty.some h
    exact MulArchimedean.comap hv.hom'.toMonoidHom hv.strictMono'
  · intro _
    obtain ⟨f, hf⟩ :=
      Archimedean.exists_orderAddMonoidHom_real_injective (Additive (ValueGroup₀ (.ofClass v))ˣ)
    let e := AddMonoidHom.toMultiplicativeRight (α := (ValueGroup₀ (.ofClass v))ˣ) (β := Real) f
    have he : StrictMono e := by
      simp only [AddMonoidHom.coe_toMultiplicativeRight, AddMonoidHom.coe_coe, e]
      -- toAdd_strictMono is already in an applied form, do defeq abuse instead
      exact StrictMono.comp strictMono_id (f.monotone'.strictMono_of_injective hf)
    let rf : Multiplicative Real ->* Real>=0ˣ := {
toFun x := Units.mk0 (.mk ((2 : Real) ^ (log (M := Real) x)) (by positivity)) by
        simp only [ne_eq, NNReal.eq_iff, NNReal.coe_mk, NNReal.coe_zero]
        positivity
      map_one' := by ext; simp
      map_mul' _ _ := by ext; simp [Real.rpow_add]
      }
    have H : StrictMono (map' (rf.comp e)) := by
      refine map'_strictMono ?_
      intro a b h
      simpa [← Units.val_lt_val, ← NNReal.coe_lt_coe, rf] using he h
    exact ⟨{
hom' := withZeroUnitsEquiv.toMonoidWithZeroHom.comp (map' (rf.comp e)).comp
        withZeroUnitsEquiv.symm.toMonoidWithZeroHom
strictMono' := withZeroUnitsEquiv_strictMono.comp H.comp
        withZeroUnitsEquiv_symm_strictMono
    }⟩

namespace RankOne

variable (v : Valuation R Γ₀) [hv : RankOne v]

/--
Definition of `hom` / `hom` 的定义

English:
abbreviation hom
  body: RankLeOne.hom' v

中文:
缩写 hom
  定义体: RankLeOne.hom' v

Depends on / 依赖: RankLeOne, RankLeOne.hom
-/
abbrev hom := RankLeOne.hom' v

/--
lemma `strictMono` / 引理 `strictMono`

English:
lemma strictMono
  statement: StrictMono (hom v)
  proof: hv.strictMono'

中文:
引理 strictMono
  结论: 严格递增 (hom v)
  证明: hv.strictMono'

Depends on / 依赖: hv.strictMono, strictMono
-/
lemma strictMono : StrictMono (hom v) := hv.strictMono'

/--
lemma `nontrivial` / 引理 `nontrivial`

English:
lemma nontrivial
  statement: exists r : R, v r != 0 ∧ v r != 1
  proof: IsNontrivial.exists_val_nontrivial

中文:
引理 nontrivial
  结论: 存在 r : R, v r != 0 ∧ v r != 1
  证明: IsNontrivial.exists_val_nontrivial

Depends on / 依赖: IsNontrivial, IsNontrivial.exists_val_nontrivial, exists_val_nontrivial
-/
lemma nontrivial : exists r : R, v r != 0 ∧ v r != 1 := IsNontrivial.exists_val_nontrivial

/--
theorem `zero_of_hom_zero` / 定理 `zero_of_hom_zero`

English:
theorem zero_of_hom_zero
  given: {x : ValueGroup₀ (.ofClass v)} (hx : hom v x = 0)
  statement: x = 0
  proof: by
  refine (eq_of_le_of_not_lt (zero_le (a := x)) fun h_lt => ?_).symm
  have hs := strictMono v h_lt
  rw [map_zero]; rw [hx] at hs
  exact hs.false

中文:
定理 zero_of_hom_zero
  条件: {x : ValueGroup₀ (.ofClass v)} (hx : hom v x = 0)
  结论: x = 0
  证明: by
  refine (eq_of_le_of_not_lt (zero_le (a := x)) fun h_lt => ?_).symm
  have hs := strictMono v h_lt
  rw [map_zero]; rw [hx] at hs
  exact hs.false

Depends on / 依赖: eq_of_le_of_not_lt, h_lt, hs.false, map_zero, strictMono, zero_le
-/
theorem zero_of_hom_zero {x : ValueGroup₀ (.ofClass v)} (hx : hom v x = 0) : x = 0 := by
  refine (eq_of_le_of_not_lt (zero_le (a := x)) fun h_lt => ?_).symm
  have hs := strictMono v h_lt
  rw [map_zero]; rw [hx] at hs
  exact hs.false

/--
theorem `hom_eq_zero_iff` / 定理 `hom_eq_zero_iff`

English:
theorem hom_eq_zero_iff
  given: {x : ValueGroup₀ (.ofClass v)}
  statement: hom v x = 0 ↔ x = 0
  proof: ⟨fun h => zero_of_hom_zero v h, fun h => by rw [h, map_zero]⟩

中文:
定理 hom_eq_zero_iff
  条件: {x : ValueGroup₀ (.ofClass v)}
  结论: hom v x = 0 ↔ x = 0
  证明: ⟨fun h => zero_of_hom_zero v h, fun h => by rw [h, map_zero]⟩

Depends on / 依赖: SigmaCompactSpace, map_zero, secondCountable_of_sigmaCompact, zero_of_hom_zero
-/
theorem hom_eq_zero_iff {x : ValueGroup₀ (.ofClass v)} : hom v x = 0 ↔ x = 0 :=
  ⟨fun h => zero_of_hom_zero v h, fun h => by rw [h, map_zero]⟩

/--
Definition of `unit` / `unit` 的定义

English:
definition unit
  signature: : Γ₀ˣ
  body: Units.mk0 (v (nontrivial v).choose) ((nontrivial v).choose_spec).1

中文:
定义 unit
  签名: : Γ₀ˣ
  定义体: Units.mk0 (v (nontrivial v).choose) ((nontrivial v).choose_spec).1

Depends on / 依赖: Units.mk0, choose_spec, nontrivial
-/
def unit : Γ₀ˣ :=
  Units.mk0 (v (nontrivial v).choose) ((nontrivial v).choose_spec).1

/--
theorem `unit_ne_one` / 定理 `unit_ne_one`

English:
theorem unit_ne_one
  statement: unit v != 1
  proof: by
  rw [Ne]; rw [← Units.val_inj]; rw [Units.val_one]
  exact ((nontrivial v).choose_spec).2

中文:
定理 unit_ne_one
  结论: unit v != 1
  证明: by
  rw [Ne]; rw [← Units.val_inj]; rw [Units.val_one]
  exact ((nontrivial v).choose_spec).2

Depends on / 依赖: EMetricSpace, EMetricSpace.instT0Space, T0Space, Units.val_inj, Units.val_one, choose_spec, instT0Space, nontrivial, val_inj, val_one
-/
theorem unit_ne_one : unit v != 1 := by
  rw [Ne]; rw [← Units.val_inj]; rw [Units.val_one]
  exact ((nontrivial v).choose_spec).2

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: IsNontrivial v
  body: RankOne.nontrivial v

中文:
实例 :
  签名: 是非平凡 v
  定义体: RankOne.nontrivial v

Depends on / 依赖: RankOne, RankOne.nontrivial, nontrivial
-/
instance : IsNontrivial v where
  exists_val_nontrivial := RankOne.nontrivial v

section Restrict

/--
Instance `isNontrivial_restrict` / 实例 `isNontrivial_restrict`

English:
instance isNontrivial_restrict
  signature: : (v.restrict).IsNontrivial where
  body: by
    obtain ⟨x, ⟨hx0, hx1⟩⟩ := IsNontrivial.exists_val_nontrivial (v := v)
    exact ⟨x, by simp [hx0], by simpa⟩

中文:
实例 isNontrivial_restrict
  签名: : (v.restrict).是非平凡 where
  定义体: by
    obtain ⟨x, ⟨hx0, hx1⟩⟩ := IsNontrivial.exists_val_nontrivial (v := v)
    exact ⟨x, by simp [hx0], by simpa⟩

Depends on / 依赖: IsNontrivial, IsNontrivial.exists_val_nontrivial, exists_val_nontrivial
-/
instance isNontrivial_restrict : (v.restrict).IsNontrivial where
  exists_val_nontrivial := by
    obtain ⟨x, ⟨hx0, hx1⟩⟩ := IsNontrivial.exists_val_nontrivial (v := v)
    exact ⟨x, by simp [hx0], by simpa⟩

variable (K : Type*) [DivisionRing K] (v : Valuation K Γ₀) [RankOne v]

/--
Instance `restrict_RankOne` / 实例 `restrict_RankOne`

English:
instance restrict_RankOne
  signature: : RankOne (v.restrict) where
  body: (RankOne.hom v).comp embedding
  strictMono' := (strictMono v).comp embedding_strictMono

@[simp]

中文:
实例 restrict_RankOne
  签名: : 秩一 (v.restrict) where
  定义体: (RankOne.hom v).comp embedding
  strictMono' := (strictMono v).comp embedding_strictMono

@[simp]

Depends on / 依赖: RankOne, RankOne.hom, embedding
-/
instance restrict_RankOne : RankOne (v.restrict) where
  hom' := (RankOne.hom v).comp embedding
  strictMono' := (strictMono v).comp embedding_strictMono

@[simp]
/--
lemma `restrict_RankOne_hom_eq` / 引理 `restrict_RankOne_hom_eq`

English:
lemma restrict_RankOne_hom_eq
  proof: rfl

中文:
引理 restrict_RankOne_hom_eq
  证明: rfl
-/
lemma restrict_RankOne_hom_eq :
  RankOne.hom v.restrict = (RankOne.hom v).comp embedding := rfl

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
variable {K} in
/--
theorem `exists_val_lt` / 定理 `exists_val_lt`

English:
theorem exists_val_lt
  given: {γ : Real>=0} (hγ : γ != 0)
  statement: exists x != 0, RankOne.hom v (v.restrict x) < γ
  proof: by
  have hγ_pos : 0 < γ := pos_iff_ne_zero.mpr hγ
  obtain ⟨x, h⟩ := NNReal.exists_lt_of_strictMono (RankOne.strictMono v.restrict) hγ_pos
  obtain ⟨k, hk⟩ := ValueGroup₀.restrict₀_surjective _ x.val
  refine ⟨k, ?_, ?_⟩
  · simp only [restrict₀_apply, MonoidWithZeroHom.coe_ofClass, restrict_def, m

中文:
定理 存在_val_lt
  条件: {γ : 实数>=0} (hγ : γ != 0)
  结论: 存在 x != 0, 秩一.hom v (v.restrict x) < γ
  证明: by
  have hγ_pos : 0 < γ := pos_iff_ne_zero.mpr hγ
  obtain ⟨x, h⟩ := NNReal.exists_lt_of_strictMono (RankOne.strictMono v.restrict) hγ_pos
  obtain ⟨k, hk⟩ := ValueGroup₀.restrict₀_surjective _ x.val
  refine ⟨k, ?_, ?_⟩
  · simp only [restrict₀_apply, MonoidWithZeroHom.coe_ofClass, restrict_def, m

Depends on / 依赖: MonoidWithZeroHom, MonoidWithZeroHom.coe_ofClass, NNReal, NNReal.exists_lt_of_strictMono, RankOne, RankOne.strictMono, SeparationQuotient, SeparationQuotient.lift, coe_ne_zero, coe_ofClass, convert, dif_pos, dite_eq_left_iff, eq_comm, exists_lt_of_strictMono, imp_false, map_eq_zero, not_not, pos_iff_ne_zero, pos_iff_ne_zero.mpr
-/
theorem exists_val_lt {γ : Real>=0} (hγ : γ != 0) : exists x != 0, RankOne.hom v (v.restrict x) < γ := by
  have hγ_pos : 0 < γ := pos_iff_ne_zero.mpr hγ
  obtain ⟨x, h⟩ := NNReal.exists_lt_of_strictMono (RankOne.strictMono v.restrict) hγ_pos
  obtain ⟨k, hk⟩ := ValueGroup₀.restrict₀_surjective _ x.val
  refine ⟨k, ?_, ?_⟩
  · simp only [restrict₀_apply, MonoidWithZeroHom.coe_ofClass, restrict_def, map_eq_zero,
      dite_eq_left_iff, coe_ne_zero, imp_false, not_not] at hk
    by_contra h0
    rw [dif_pos (by rw [dif_pos ((zero_iff v).mpr h0)]), eq_comm] at hk
    simp at hk
  · convert! h
    simp only [restrict_RankOne_hom_eq, coe_comp, Function.comp_apply, ← hk]
    congr 1
    exact (embedding_restrict₀ k).symm

end Restrict

end RankOne

namespace RankLeOne

variable {K : Type*} [DivisionRing K] (v : Valuation K Γ₀) [RankLeOne v]

/-- If a valuation has rank at most one and is non trivial,
then it has rank one -/
@[instance_reducible]
/--
Definition of `rankOne_of_exists` / `rankOne_of_exists` 的定义

English:
definition rankOne_of_exists
  signature: (H : exists x != 0, v x != 1)
  body: by
    by_contra! H'
    obtain ⟨x, hx, hx'⟩ := H
    exact hx' (H' x ((ne_zero_iff v).mpr hx))

中文:
定义 rankOne_of_存在
  签名: (H : 存在 x != 0, v x != 1)
  定义体: by
    by_contra! H'
    obtain ⟨x, hx, hx'⟩ := H
    exact hx' (H' x ((ne_zero_iff v).mpr hx))

Depends on / 依赖: ne_zero_iff
-/
def rankOne_of_exists (H : exists x != 0, v x != 1) : RankOne v where
  exists_val_nontrivial := by
    by_contra! H'
    obtain ⟨x, hx, hx'⟩ := H
    exact hx' (H' x ((ne_zero_iff v).mpr hx))

/-- If a valuation has rank at most one and is non trivial,
then it has rank one -/
@[instance_reducible]
/--
Definition of `rankOne_of_nontrivial` / `rankOne_of_nontrivial` 的定义

English:
definition rankOne_of_nontrivial
  signature: (H : Nontrivial (ValueGroup₀ (.ofClass v))ˣ)
  body: by
    by_contra! H'
    rw [nontrivial_iff_exists_ne 1] at H
    obtain ⟨x, hx⟩ := H
    obtain ⟨k, hk⟩ := ValueGroup₀.restrict₀_surjective _ x.val
    have h0 : v k != 0 := by
      apply_fun embedding at hk
      simp only [embedding_restrict₀, MonoidWithZeroHom.coe_ofClass] at hk
      simp [hk]

中文:
定义 rankOne_of_nontrivial
  签名: (H : 非平凡 (ValueGroup₀ (.ofClass v))ˣ)
  定义体: by
    by_contra! H'
    rw [nontrivial_iff_exists_ne 1] at H
    obtain ⟨x, hx⟩ := H
    obtain ⟨k, hk⟩ := ValueGroup₀.restrict₀_surjective _ x.val
    have h0 : v k != 0 := by
      apply_fun embedding at hk
      simp only [embedding_restrict₀, MonoidWithZeroHom.coe_ofClass] at hk
      simp [hk]

Depends on / 依赖: MonoidWithZeroHom, MonoidWithZeroHom.coe_ofClass, MonoidWithZeroHom.ofClass, Units.val, Units.val_injective, apply_fu, apply_fun, coe_ofClass, embedding, nontrivial_iff_exists_ne, ofClass, val_injective, x.val
-/
def rankOne_of_nontrivial (H : Nontrivial (ValueGroup₀ (.ofClass v))ˣ) : RankOne v where
  exists_val_nontrivial := by
    by_contra! H'
    rw [nontrivial_iff_exists_ne 1] at H
    obtain ⟨x, hx⟩ := H
    obtain ⟨k, hk⟩ := ValueGroup₀.restrict₀_surjective _ x.val
    have h0 : v k != 0 := by
      apply_fun embedding at hk
      simp only [embedding_restrict₀, MonoidWithZeroHom.coe_ofClass] at hk
      simp [hk]
    have h1 : v k != 1 := by
      apply_fun embedding at hk
      simp only [embedding_restrict₀, MonoidWithZeroHom.coe_ofClass] at hk
      apply_fun Units.val at hx using
          Units.val_injective (α := (MonoidWithZeroHom.ofClass v).ValueGroup₀)
      intro h
      apply_fun embedding at hx using embedding_injective (f := .ofClass v)
      simp [← hk, h] at hx
    exact h1 (H' k h0)

/--
theorem `exists_val_lt` / 定理 `exists_val_lt`

English:
theorem exists_val_lt
  given: {K : Type*} [DivisionRing K] (v : Valuation K Γ₀) [RankLeOne v]
  proof: by
  simp only [ne_eq, or_iff_not_imp_left, not_subsingleton_iff_nontrivial]
  exact fun H => (rankOne_of_nontrivial v H).exists_val_lt

中文:
定理 存在_val_lt
  条件: {K : 类型} [除环 K] (v : 赋值 K Γ₀) [秩不超过一 v]
  证明: by
  simp only [ne_eq, or_iff_not_imp_left, not_subsingleton_iff_nontrivial]
  exact fun H => (rankOne_of_nontrivial v H).exists_val_lt

Depends on / 依赖: exists_val_lt, ne_eq, not_subsingleton_iff_nontrivial, or_iff_not_imp_left, rankOne_of_nontrivial
-/
theorem exists_val_lt {K : Type*} [DivisionRing K] (v : Valuation K Γ₀) [RankLeOne v] :
    Subsingleton ((ValueGroup₀ (.ofClass v))ˣ) ∨
      forall {γ : Real>=0} (_ : γ != 0), exists (x : K), x != 0 ∧ (RankLeOne.hom' v) (v.restrict x) < γ := by
  simp only [ne_eq, or_iff_not_imp_left, not_subsingleton_iff_nontrivial]
  exact fun H => (rankOne_of_nontrivial v H).exists_val_lt

end RankLeOne

end Valuation

section ValuativeRel

open ValuativeRel

variable {R : Type*} [Ring R] [ValuativeRel R]

/-- A valuative relation has a rank one valuation when it is both nontrivial
and the rank is at most one. -/
@[instance_reducible]
/--
Definition of `Valuation.RankOne.ofRankLeOneStruct` / `Valuation.RankOne.ofRankLeOneStruct` 的定义

English:
definition Valuation.RankOne.ofRankLeOneStruct
  signature: [ValuativeRel.IsNontrivial R] (e : RankLeOneStruct R)
  body: e.emb.comp embedding
  strictMono' := e.strictMono.comp embedding_strictMono

中文:
定义 赋值.秩一.ofRankLeOneStruct
  签名: [ValuativeRel.是非平凡 R] (e : RankLeOneStruct R)
  定义体: e.emb.comp embedding
  strictMono' := e.strictMono.comp embedding_strictMono

Depends on / 依赖: e.emb.comp, embedding
-/
def Valuation.RankOne.ofRankLeOneStruct [ValuativeRel.IsNontrivial R] (e : RankLeOneStruct R) :
    Valuation.RankOne (valuation R) where
  hom' := e.emb.comp embedding
  strictMono' := e.strictMono.comp embedding_strictMono

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [IsNontrivial
  signature: R] [IsRankLeOne R] :
  body: Valuation.RankOne.ofRankLeOneStruct IsRankLeOne.nonempty.some

中文:
实例 [是非平凡
  签名: R] [是秩不超过一 R] :
  定义体: Valuation.RankOne.ofRankLeOneStruct IsRankLeOne.nonempty.some

Depends on / 依赖: IsRankLeOne, IsRankLeOne.nonempty.some, RankOne, Valuation, Valuation.RankOne.ofRankLeOneStruct, nonempty, ofRankLeOneStruct
-/
instance [IsNontrivial R] [IsRankLeOne R] :
    Valuation.RankOne (valuation R) :=
  Valuation.RankOne.ofRankLeOneStruct IsRankLeOne.nonempty.some

/--
Definition of `Valuation.RankOne.rankLeOneStruct` / `Valuation.RankOne.rankLeOneStruct` 的定义

English:
definition Valuation.RankOne.rankLeOneStruct
  signature: (e : Valuation.RankOne (valuation R))
  body: e.hom.comp (ValuativeRel.ValueGroupWithZero.embed (v := valuation R))
  strictMono := e.strictMono.comp (ValueGroupWithZero.embed_strictMono (valuation R))

中文:
定义 赋值.秩一.rankLeOneStruct
  签名: (e : 赋值.秩一 (valuation R))
  定义体: e.hom.comp (ValuativeRel.ValueGroupWithZero.embed (v := valuation R))
  strictMono := e.strictMono.comp (ValueGroupWithZero.embed_strictMono (valuation R))

Depends on / 依赖: ValuativeRel, ValuativeRel.ValueGroupWithZero.embed, ValueGroupWithZero, e.hom.comp, valuation
-/
def Valuation.RankOne.rankLeOneStruct (e : Valuation.RankOne (valuation R)) :
    RankLeOneStruct R where
  emb := e.hom.comp (ValuativeRel.ValueGroupWithZero.embed (v := valuation R))
  strictMono := e.strictMono.comp (ValueGroupWithZero.embed_strictMono (valuation R))

/--
lemma `ValuativeRel.isRankLeOne_of_rankOne` / 引理 `ValuativeRel.isRankLeOne_of_rankOne`

English:
lemma ValuativeRel.isRankLeOne_of_rankOne
  given: [h : (valuation R).RankOne]
  proof: ⟨⟨h.rankLeOneStruct⟩⟩

中文:
引理 ValuativeRel.isRankLeOne_of_rankOne
  条件: [h : (valuation R).秩一]
  证明: ⟨⟨h.rankLeOneStruct⟩⟩

Depends on / 依赖: h.rankLeOneStruct, rankLeOneStruct
-/
lemma ValuativeRel.isRankLeOne_of_rankOne [h : (valuation R).RankOne] :
    IsRankLeOne R := ⟨⟨h.rankLeOneStruct⟩⟩

/--
lemma `ValuativeRel.isNontrivial_of_rankOne` / 引理 `ValuativeRel.isNontrivial_of_rankOne`

English:
lemma ValuativeRel.isNontrivial_of_rankOne
  given: [h : (valuation R).RankOne]
  proof: (isNontrivial_iff_isNontrivial _).mpr h.toIsNontrivial

中文:
引理 ValuativeRel.isNontrivial_of_rankOne
  条件: [h : (valuation R).秩一]
  证明: (isNontrivial_iff_isNontrivial _).mpr h.toIsNontrivial

Depends on / 依赖: h.toIsNontrivial, isNontrivial_iff_isNontrivial, toIsNontrivial
-/
lemma ValuativeRel.isNontrivial_of_rankOne [h : (valuation R).RankOne] :
    ValuativeRel.IsNontrivial R :=
  (isNontrivial_iff_isNontrivial _).mpr h.toIsNontrivial

open WithZero

/--
lemma `ValuativeRel.isRankLeOne_iff_mulArchimedean` / 引理 `ValuativeRel.isRankLeOne_iff_mulArchimedean`

English:
lemma ValuativeRel.isRankLeOne_iff_mulArchimedean
  proof: by
  constructor
  · rintro ⟨⟨f, hf⟩⟩
    exact .comap f.toMonoidHom hf
  · intro h
    by_cases H : IsNontrivial R
    · rw [isNontrivial_iff_isNontrivial (valuation R)] at H
      have h' : MulArchimedean (ValueGroup₀ (.ofClass (valuation R))) :=
        MulArchimedean.comap embedding.toMonoidHom 

中文:
引理 ValuativeRel.isRankLeOne_iff_mulArchimedean
  证明: by
  constructor
  · rintro ⟨⟨f, hf⟩⟩
    exact .comap f.toMonoidHom hf
  · intro h
    by_cases H : IsNontrivial R
    · rw [isNontrivial_iff_isNontrivial (valuation R)] at H
      have h' : MulArchimedean (ValueGroup₀ (.ofClass (valuation R))) :=
        MulArchimedean.comap embedding.toMonoidHom 

Depends on / 依赖: IsNontrivial, MulArchimedean, MulArchimedean.comap, contrapose, embedding, embedding.toMonoidHom, embedding_strictMono, eq_or_n, f.toMonoidHom, isNontrivial_iff_isNontrivial, isRankLeOne_of_rankOne, nonempty_rankOne_iff_mulArchimedean, ofClass, strictMono, toMonoidHom, valuation
-/
lemma ValuativeRel.isRankLeOne_iff_mulArchimedean :
    IsRankLeOne R ↔ MulArchimedean (ValueGroupWithZero R) := by
  constructor
  · rintro ⟨⟨f, hf⟩⟩
    exact .comap f.toMonoidHom hf
  · intro h
    by_cases H : IsNontrivial R
    · rw [isNontrivial_iff_isNontrivial (valuation R)] at H
      have h' : MulArchimedean (ValueGroup₀ (.ofClass (valuation R))) :=
        MulArchimedean.comap embedding.toMonoidHom embedding_strictMono
      rw [← (valuation R).nonempty_rankOne_iff_mulArchimedean] at h'
      obtain ⟨f⟩ := h'
      exact isRankLeOne_of_rankOne
    · refine ⟨⟨{ emb := 1, strictMono := ?_ }⟩⟩
      intro a b
      contrapose! H
      obtain ⟨H, H'⟩ := H
      rcases eq_or_ne a 0 with rfl | ha
      · simp_all
      rcases eq_or_ne a 1 with rfl | ha'
      · exact ⟨⟨b, (H.trans' zero_lt_one).ne', H.ne'⟩⟩
      · exact ⟨⟨a, ha, ha'⟩⟩

/--
lemma `ValuativeRel.IsRankLeOne.of_compatible_mulArchimedean` / 引理 `ValuativeRel.IsRankLeOne.of_compatible_mulArchimedean`

English:
lemma ValuativeRel.IsRankLeOne.of_compatible_mulArchimedean
  statement: [MulArchimedean Γ₀]
  proof: by
  rw [isRankLeOne_iff_mulArchimedean]
  exact MulArchimedean.comap (embedding.toMonoidHom.comp (ValueGroupWithZero.embed v).toMonoidHom)
    (embedding_strictMono.comp (ValueGroupWithZero.embed_strictMono v))

中文:
引理 ValuativeRel.是秩不超过一.of_compatible_mulArchimedean
  结论: [MulArchimedean Γ₀]
  证明: by
  rw [isRankLeOne_iff_mulArchimedean]
  exact MulArchimedean.comap (embedding.toMonoidHom.comp (ValueGroupWithZero.embed v).toMonoidHom)
    (embedding_strictMono.comp (ValueGroupWithZero.embed_strictMono v))

Depends on / 依赖: MulArchimedean, MulArchimedean.comap, ValueGroupWithZero, ValueGroupWithZero.embed, ValueGroupWithZero.embed_strictMono, embed_strictMono, embedding, embedding.toMonoidHom.comp, embedding_strictMono, embedding_strictMono.comp, isRankLeOne_iff_mulArchimedean, toMonoidHom
-/
lemma ValuativeRel.IsRankLeOne.of_compatible_mulArchimedean [MulArchimedean Γ₀]
    (v : Valuation R Γ₀) [v.Compatible] :
    ValuativeRel.IsRankLeOne R := by
  rw [isRankLeOne_iff_mulArchimedean]
  exact MulArchimedean.comap (embedding.toMonoidHom.comp (ValueGroupWithZero.embed v).toMonoidHom)
    (embedding_strictMono.comp (ValueGroupWithZero.embed_strictMono v))

end ValuativeRel
