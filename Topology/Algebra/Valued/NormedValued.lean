/-
Copyright (c) 2024 María Inés de Frutos-Fernández. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: María Inés de Frutos-Fernández, Filippo A. E. Nuccio
-/
module

public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Analysis.Normed.Group.Ultra
public import Mathlib.RingTheory.Valuation.RankOne
public import Mathlib.Topology.Algebra.Valued.ValuationTopology

/-!
# Correspondence between nontrivial nonarchimedean norms and rank one valuations

Nontrivial nonarchimedean norms correspond to rank one valuations.

## Main Definitions
* `NormedField.toValued` : the valued field structure on a nonarchimedean normed field `K`,
  determined by the norm.
* `Valued.toNormedField` : the normed field structure determined by a rank one valuation.

## Main Results
* The valuation of a normed field has rank at most one.

## Tags

norm, nonarchimedean, nontrivial, valuation, rank one
-/

@[expose] public section


noncomputable section

open Filter Set Valuation MonoidWithZeroHom

open scoped NNReal

section

variable {K : Type*} [hK : NormedField K] [IsUltrametricDist K]

namespace NormedField

set_option linter.style.whitespace false in -- manual alignment is not recognised
/-- The valuation on a nonarchimedean normed field `K` defined as `nnnorm`. -/
/-
**NormedField.valuation** 是 Mathlib 中的一个定义，位于命名空间 `NormedField`。
形式化陈述：valuation : Valuation K Real>=0 where toFun
该定义给出了一等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The valuation on a nonarchimedean normed field `K` defined as `nnnorm`.
-/
def valuation : Valuation K ℝ≥0 where
  toFun           := nnnorm
  map_zero'       := nnnorm_zero
  map_one'        := nnnorm_one
  map_mul'        := nnnorm_mul
  map_add_le_max' := IsUltrametricDist.norm_add_le_max

@[simp]
/-
**NormedField.valuation_apply** 是 Mathlib 中的一个定理，位于命名空间 `NormedField`。
形式化陈述：valuation_apply (x : K) : valuation x = ‖x‖₊
参数：x : K。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem valuation_apply (x : K) : valuation x = ‖x‖₊ := rfl

open MonoidWithZeroHom MonoidWithZeroHom.ValueGroup₀

/-- The valuation of a normed field has rank at most one -/
/-
**NormedField.** 是 Mathlib 中的一个实例，位于命名空间 `NormedField`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The valuation of a normed field has rank at most one
-/
instance : RankLeOne (valuation (K := K)) where
  hom' := embedding
  strictMono' := embedding_strictMono

set_option backward.isDefEq.respectTransparency.types false in
/-- The valued field structure on a nonarchimedean normed field `K`, determined by the norm. -/
@[instance_reducible]
/-
**NormedField.toValued** 是 Mathlib 中的一个定义，位于命名空间 `NormedField`。
形式化陈述：toValued : Valued K Real>=0
该定义给出了一等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The valued field structure on a nonarchimedean normed field `K`, determined by t
he norm.
-/
def toValued : Valued K ℝ≥0 :=
  { hK.toUniformSpace,
    (inferInstance : IsUniformAddGroup K) with
    v := valuation
    is_topological_valuation := fun U => by
      rw [Metric.mem_nhds_iff]
      refine ⟨?_, ?_⟩
      · rintro ⟨ε, hε, h⟩
        rcases RankLeOne.exists_val_lt (valuation (K := K)) with H | H
        · use Units.mk0 (valuation.restrict 1) (by simp)
          intro x hx
          simp only [Units.val_mk0, mem_ofPred_eq, map_one] at hx
          by_cases hx0 : x = 0
          · exact h (hx0 ▸ Metric.mem_ball_self hε)
          · exfalso
            rw [← (valuation (K := K)).restrict.zero_iff, ← ne_eq, ← isUnit_iff_ne_zero] at hx0
            apply not_le.mpr hx
            apply le_of_eq
            rw [eq_comm]
            simpa only [Units.ext_iff, hx0.unit_spec, Units.val_one,
              Submonoid.mk_eq_one] using! H.elim hx0.unit 1
        · obtain ⟨x, hx, hxy⟩ := H (γ := ⟨ε, le_of_lt hε⟩) (pos_iff_ne_zero.mp hε)
          use Units.mk0 (valuation.restrict x) (by simp [Valuation.restrict_def, hx])
          intro y hy
          apply h
          simp only [Metric.mem_ball, dist_zero_right]
          simp only [Units.val_mk0, mem_ofPred_eq, restrict_lt_iff, ← NNReal.coe_lt_coe] at hy
          apply lt_trans hy
          simpa [RankLeOne.hom', valuation.restrict_def] using! hxy
      · rintro ⟨ε, hε⟩
        refine ⟨(embedding ε.1 : ℝ≥0), ?_, fun x hx ↦ hε ?_⟩
        · exact NNReal.coe_pos.mpr <| embedding_strictMono.lt_iff_lt.mpr ε.zero_lt
        · simpa [restrict_lt_iff_lt_embedding] using! (mem_ball_zero_iff.mp hx) }
/-
**NormedField.** 是 Mathlib 中的一个实例，位于命名空间 `NormedField`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K] :
    Valuation.RankOne (valuation (K := K)) where
  hom' := ValueGroup₀.embedding
  strictMono' := ValueGroup₀.embedding_strictMono
  exists_val_nontrivial := (exists_one_lt_norm K).imp fun x h ↦ by
    have h' : x ≠ 0 := norm_eq_zero.not.mp (h.gt.trans' (by simp)).ne'
    simp [valuation_apply, ← NNReal.coe_inj, h.ne', h']

end NormedField

end


namespace Valuation

variable {L : Type*} [Field L] {Γ₀ : Type*} [LinearOrderedCommGroupWithZero Γ₀]
  (v : Valuation L Γ₀) [hv : RankOne v]

/-- The norm function determined by a rank one valuation on a field `L`. -/
/-
**Valuation.norm** 是 Mathlib 中的一个定义，位于命名空间 `Valuation`。
形式化陈述：norm : L -> Real
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The norm function determined by a rank one valuation on a field `L`.
-/
def norm : L → ℝ := fun x : L => hv.hom _ (v.restrict x)
/-
**Valuation.norm_def** 是 Mathlib 中的一个定理，位于命名空间 `Valuation`。
形式化陈述：norm_def {x : L} : v.norm x = hv.hom _ (v.restrict x)
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem norm_def {x : L} : v.norm x = hv.hom _ (v.restrict x) := rfl
/-
**Valuation.norm_nonneg** 是 Mathlib 中的一个定理，位于命名空间 `Valuation`。
形式化陈述：norm_nonneg (x : L) : 0 <= v.norm x
参数：x : L。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
-/
theorem norm_nonneg (x : L) : 0 ≤ v.norm x := by simp only [norm, NNReal.zero_le_coe]

set_option backward.isDefEq.respectTransparency.types false in
/-
**Valuation.norm_add_le** 是 Mathlib 中的一个定理，位于命名空间 `Valuation`。
形式化陈述：norm_add_le (x y : L) : v.norm (x + y) <= max (v.norm x) (v.norm y)
参数：x y : L。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ValuationClass.toMonoidWithZeroHomClass`：∀ {F : Type u_7} {R : outParam 
(Type u_5)} {Γ₀ : outParam (Type u_6)} {inst : LinearOrderedCommMonoidWithZero Γ
₀}   {inst_1 : Ring R} {inst_…
· 使用定理 `Valuation.instValuationClass`：∀ {R : Type u_3} {Γ₀ : Type u_4} [inst : R
ing R] [inst_1 : LinearOrderedCommMonoidWithZero Γ₀],   ValuationClass (Valuatio
n R Γ₀) R Γ₀
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `StrictMono.le_iff_le`：StrictMono.le_iff_le (hf : StrictMono f) {a b : α}
 : f a <= f b ↔ a <= b
· 使用引理 `Valuation.RankOne.strictMono`：strictMono : StrictMono (hom v)
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `le_max_iff`：le_max_iff : a <= max b c ↔ a <= b ∨ a <= c
· 使用定理 `Valuation.map_add_le_max'`：∀ {R : Type u_3} {Γ₀ : Type u_4} [inst : Line
arOrderedCommMonoidWithZero Γ₀] [inst_1 : Ring R] (self : Valuation R Γ₀)   (x y
 : R),   (↑self…
-/
theorem norm_add_le (x y : L) : v.norm (x + y) ≤ max (v.norm x) (v.norm y) := by
  simp only [norm, NNReal.coe_le_coe, le_max_iff, StrictMono.le_iff_le hv.strictMono]
  exact le_max_iff.mp (Valuation.map_add_le_max' v.restrict _ _)
/-
**Valuation.norm_eq_zero** 是 Mathlib 中的一个定理，位于命名空间 `Valuation`。
形式化陈述：norm_eq_zero {x : L} (hx : v.norm x = 0) : x = 0
参数：hx : v.norm x = 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `ValuationClass.toMonoidWithZeroHomClass`：∀ {F : Type u_7} {R : outParam 
(Type u_5)} {Γ₀ : outParam (Type u_6)} {inst : LinearOrderedCommMonoidWithZero Γ
₀}   {inst_1 : Ring R} {inst_…
· 使用定理 `Valuation.instValuationClass`：∀ {R : Type u_3} {Γ₀ : Type u_4} [inst : R
ing R] [inst_1 : LinearOrderedCommMonoidWithZero Γ₀],   ValuationClass (Valuatio
n R Γ₀) R Γ₀
· 使用定理 `NNReal.instNontrivial`：Nontrivial NNReal
· 使用定理 `WithZero.instNontrivial`：∀ {α : Type u} [Nonempty α], Nontrivial (WithZe
ro α)
· 使用定理 `Nontrivial.to_nonempty`：∀ {α : Type u_1} [Nontrivial α], Nonempty α
· 使用定理 `Valuation.instNontrivialSubtypeUnitsMemSubgroupValueGroupOfClassOfIsNont
rivial`：∀ {R : Type u_3} [inst : Ring R] {Γ₀ : Type u_7} [inst_1 : LinearOrdered
CommGroupWithZero Γ₀] {v : Valuation R Γ₀}   [hv : v.IsNontrivial], …
· 使用定理 `Valuation.RankOne.instIsNontrivial`：∀ {R : Type u_1} {Γ₀ : Type u_2} [in
st : Ring R] [inst_1 : LinearOrderedCommGroupWithZero Γ₀] (v : Valuation R Γ₀)  
 [hv : v.RankOne], v.IsN…
-/
theorem norm_eq_zero {x : L} (hx : v.norm x = 0) : x = 0 := by
  simpa [v.restrict_def, norm, NNReal.coe_eq_zero, RankOne.hom_eq_zero_iff, zero_iff] using hx
/-
**Valuation.norm_pos_iff_valuation_pos** 是 Mathlib 中的一个定理，位于命名空间 `Valuation`。
形式化陈述：norm_pos_iff_valuation_pos {x : L} : 0 < v.norm x ↔ (0 : Γ₀) < v x
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ValuationClass.toMonoidWithZeroHomClass`：∀ {F : Type u_7} {R : outParam 
(Type u_5)} {Γ₀ : outParam (Type u_6)} {inst : LinearOrderedCommMonoidWithZero Γ
₀}   {inst_1 : Ring R} {inst_…
· 使用定理 `Valuation.instValuationClass`：∀ {R : Type u_3} {Γ₀ : Type u_4} [inst : R
ing R] [inst_1 : LinearOrderedCommMonoidWithZero Γ₀],   ValuationClass (Valuatio
n R Γ₀) R Γ₀
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Valuation.norm_def`：norm_def {x : L} : v.norm x = hv.hom _ (v.restrict x
)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `NNReal.coe_zero`：↑0 = 0
· 使用定理 `NNReal.coe_lt_coe`：∀ {r₁ r₂ : NNReal}, ↑r₁ < ↑r₂ ↔ r₁ < r₂
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `MonoidWithZeroHomClass.toZeroHomClass`：∀ {F : Type u_7} {α : outParam (T
ype u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : MulZe
roOneClass β} {inst_2 : Fun…
· 使用定理 `StrictMono.lt_iff_lt`：StrictMono.lt_iff_lt (hf : StrictMono f) {a b : α}
 : f a < f b ↔ a < b
· 使用引理 `Valuation.RankOne.strictMono`：strictMono : StrictMono (hom v)
· 使用引理 `Valuation.restrict_pos_iff`：restrict_pos_iff (x : R) : 0 < v.restrict x 
↔ 0 < v x
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem norm_pos_iff_valuation_pos {x : L} : 0 < v.norm x ↔ (0 : Γ₀) < v x := by
  rw [norm_def, ← NNReal.coe_zero, NNReal.coe_lt_coe, ← map_zero (RankOne.hom v),
    StrictMono.lt_iff_lt (RankOne.strictMono v)]
  rw [v.restrict_pos_iff]

end Valuation

namespace Valued

variable (L : Type*) [Field L] (Γ₀ : Type*) [LinearOrderedCommGroupWithZero Γ₀]
  [val : Valued L Γ₀] [hv : RankOne val.v]

open Valuation

/-- The normed field structure determined by a rank one valuation. -/
@[instance_reducible]
/-
**Valued.toNormedField** 是 Mathlib 中的一个定义，位于命名空间 `Valued`。
形式化陈述：toNormedField : NormedField L
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The normed field structure determined by a rank one valuation.
-/
def toNormedField : NormedField L :=
  { (inferInstance : Field L) with
    norm := val.v.norm
    dist := fun x y => val.v.norm (x - y)
    dist_self := fun x => by
      simp only [sub_self, Valuation.norm, Valuation.map_zero, hv.hom.map_zero, NNReal.coe_zero]
    dist_comm := fun x y => by simp only [Valuation.norm]; rw [← neg_sub, Valuation.map_neg]
    dist_triangle := fun x y z => by
      simp only [← sub_add_sub_cancel x y z]
      exact le_trans (val.v.norm_add_le _ _)
        (max_le_add_of_nonneg (val.v.norm_nonneg _) (val.v.norm_nonneg _))
    eq_of_dist_eq_zero := fun hxy => eq_of_sub_eq_zero (val.v.norm_eq_zero hxy)
    dist_eq := fun x y => by
      simp only [Valuation.norm]
      rw [← v.restrict.map_neg, neg_sub, sub_eq_add_neg, add_comm]
    norm_mul := fun x y => by simp only [Valuation.norm, ← NNReal.coe_mul, map_mul]
    toUniformSpace := Valued.toUniformSpace
    uniformity_dist := by
      have : Nonempty { ε : ℝ // ε > 0 } := nonempty_Ioi_subtype
      ext U
      rw [hasBasis_iff.mp (Valued.hasBasis_uniformity L Γ₀), iInf_subtype', mem_iInf_of_directed]
      · simp only [true_and, mem_principal, Subtype.exists, gt_iff_lt, exists_prop]
        refine ⟨fun ⟨ε, hε⟩ => ?_, fun ⟨r, hr_pos, hr⟩ => ?_⟩
        · set δ : ℝ≥0 := hv.hom _ ε with hδ
          have hδ_pos : 0 < δ := by
            rw [hδ, ← map_zero hv.hom]
            exact hv.strictMono _ (Units.zero_lt ε)
          use δ, hδ_pos
          apply subset_trans _ hε
          intro x hx
          simp only [mem_ofPred_eq, Valuation.norm, hδ, NNReal.coe_lt_coe] at hx
          rw [mem_ofPred, ← neg_sub, Valuation.map_neg]
          exact (RankOne.strictMono Valued.v).lt_iff_lt.mp hx
        · have : Nontrivial Γ₀ˣ := (nontrivial_iff_exists_ne (1 : Γ₀ˣ)).mpr
            ⟨RankOne.unit val.v, RankOne.unit_ne_one val.v⟩
          obtain ⟨u, hu⟩ := Real.exists_lt_of_strictMono hv.strictMono hr_pos
          use u
          apply subset_trans _ hr
          intro x hx
          simp only [Valuation.norm, mem_ofPred_eq]
          apply lt_trans _ hu
          rw [NNReal.coe_lt_coe, ← neg_sub, Valuation.map_neg]
          exact (RankOne.strictMono Valued.v).lt_iff_lt.mpr hx
      · simp only [Directed]
        intro x y
        use min x y
        simp only [le_principal_iff, mem_principal, ofPred_subset_ofPred, Prod.forall]
        exact ⟨fun a b hab => lt_of_lt_of_le hab (min_le_left _ _), fun a b hab =>
            lt_of_lt_of_le hab (min_le_right _ _)⟩ }

-- When a field is valued, one inherits a `NormedField`.
-- Scoped instance to avoid a typeclass loop or non-defeq topology or norms.
scoped[Valued] attribute [instance] Valued.toNormedField
scoped[NormedField] attribute [instance] NormedField.toValued

section NormedField

open scoped Valued

/-
**Valued.isNonarchimedean_norm** 是 Mathlib 中的一个定理，位于命名空间 `Valued`。
形式化陈述：∀ (L : Type u_1) [inst : Field L] (Γ₀ : Type u_2) [inst_1 : LinearOrderedC
ommGroupWithZero Γ₀] [val : Valued L Γ₀]   [hv : Valued.v.RankOne], IsNonarchime
dean fun x => ‖x‖
参数：L : Type u_1；Γ₀ : Type u_2。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Valuation.norm_add_le`：norm_add_le (x y : L) : v.norm (x + y) <= max (v.
norm x) (v.norm y)
-/
protected lemma isNonarchimedean_norm : IsNonarchimedean ((‖·‖) : L → ℝ) :=
  Valuation.norm_add_le _
/-
**Valued.** 是 Mathlib 中的一个实例，位于命名空间 `Valued`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : IsUltrametricDist L :=
  ⟨fun x y z ↦ by
    refine (Valuation.norm_add_le _ (x - y) (y - z)).trans_eq' ?_
    simp only [sub_add_sub_cancel]
    rfl ⟩
/-
**Valued.coe_valuation_eq_rankOne_hom_comp_valuation** 是 Mathlib 中的一个引理，位于命名空间 `
Valued`。
形式化陈述：coe_valuation_eq_rankOne_hom_comp_valuation : ⇑NormedField.valuation = hv.
hom ∘ val.v.restrict
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Valued.instIsUltrametricDist`：∀ (L : Type u_1) [inst : Field L] (Γ₀ : Ty
pe u_2) [inst_1 : LinearOrderedCommGroupWithZero Γ₀] [val : Valued L Γ₀]   [hv :
 Valued.v.RankOne]…
-/
lemma coe_valuation_eq_rankOne_hom_comp_valuation :
    ⇑NormedField.valuation = hv.hom ∘ val.v.restrict := rfl

end NormedField
namespace toNormedField

variable {L Γ₀}

variable {x x' : L}

/-
**Valued.toNormedField.norm_def** 是 Mathlib 中的一个定理，位于命名空间 `Valued.toNormedField`
。
形式化陈述：norm_def : ‖x‖ = hv.hom _ (Valued.v.restrict x)
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem norm_def : ‖x‖ = hv.hom _ (Valued.v.restrict x) := rfl

@[simp]
/-
**Valued.toNormedField.norm_le_iff** 是 Mathlib 中的一个定理，位于命名空间 `Valued.toNormedFie
ld`。
形式化陈述：norm_le_iff : ‖x‖ <= ‖x'‖ ↔ val.v x <= val.v x'
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ValuationClass.toMonoidWithZeroHomClass`：∀ {F : Type u_7} {R : outParam 
(Type u_5)} {Γ₀ : outParam (Type u_6)} {inst : LinearOrderedCommMonoidWithZero Γ
₀}   {inst_1 : Ring R} {inst_…
· 使用定理 `Valuation.instValuationClass`：∀ {R : Type u_3} {Γ₀ : Type u_4} [inst : R
ing R] [inst_1 : LinearOrderedCommMonoidWithZero Γ₀],   ValuationClass (Valuatio
n R Γ₀) R Γ₀
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `Valuation.restrict_le_iff`：restrict_le_iff {x y : R} : v.restrict x <= v
.restrict y ↔ v x <= v y
· 使用定理 `StrictMono.le_iff_le`：StrictMono.le_iff_le (hf : StrictMono f) {a b : α}
 : f a <= f b ↔ a <= b
· 使用引理 `Valuation.RankOne.strictMono`：strictMono : StrictMono (hom v)
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem norm_le_iff : ‖x‖ ≤ ‖x'‖ ↔ val.v x ≤ val.v x' := by
  rw [← v.restrict_le_iff, ← (Valuation.RankOne.strictMono val.v).le_iff_le]
  rfl

@[simp]
/-
**Valued.toNormedField.norm_lt_iff** 是 Mathlib 中的一个定理，位于命名空间 `Valued.toNormedFie
ld`。
形式化陈述：norm_lt_iff : ‖x‖ < ‖x'‖ ↔ val.v x < val.v x'
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ValuationClass.toMonoidWithZeroHomClass`：∀ {F : Type u_7} {R : outParam 
(Type u_5)} {Γ₀ : outParam (Type u_6)} {inst : LinearOrderedCommMonoidWithZero Γ
₀}   {inst_1 : Ring R} {inst_…
· 使用定理 `Valuation.instValuationClass`：∀ {R : Type u_3} {Γ₀ : Type u_4} [inst : R
ing R] [inst_1 : LinearOrderedCommMonoidWithZero Γ₀],   ValuationClass (Valuatio
n R Γ₀) R Γ₀
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `Valuation.restrict_lt_iff`：restrict_lt_iff {x y : R} : v.restrict x < v.
restrict y ↔ v x < v y
· 使用定理 `StrictMono.lt_iff_lt`：StrictMono.lt_iff_lt (hf : StrictMono f) {a b : α}
 : f a < f b ↔ a < b
· 使用引理 `Valuation.RankOne.strictMono`：strictMono : StrictMono (hom v)
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem norm_lt_iff : ‖x‖ < ‖x'‖ ↔ val.v x < val.v x' := by
  rw [← v.restrict_lt_iff, ← (Valuation.RankOne.strictMono val.v).lt_iff_lt]
  rfl

@[simp]
/-
**Valued.toNormedField.norm_le_one_iff** 是 Mathlib 中的一个定理，位于命名空间 `Valued.toNorme
dField`。
形式化陈述：norm_le_one_iff : ‖x‖ <= 1 ↔ val.v x <= 1
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `map_one`：map_one [OneHomClass F M N] (f : F) : f 1 = 1
· 使用定理 `MonoidHomClass.toOneHomClass`：∀ {F : Type u_10} {M : outParam (Type u_11
)} {N : outParam (Type u_12)} {inst : MulOne M} {inst_1 : MulOne N}   {inst_2 : 
FunLike F M N} [se…
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `ValuationClass.toMonoidWithZeroHomClass`：∀ {F : Type u_7} {R : outParam 
(Type u_5)} {Γ₀ : outParam (Type u_6)} {inst : LinearOrderedCommMonoidWithZero Γ
₀}   {inst_1 : Ring R} {inst_…
· 使用定理 `Valuation.instValuationClass`：∀ {R : Type u_3} {Γ₀ : Type u_4} [inst : R
ing R] [inst_1 : LinearOrderedCommMonoidWithZero Γ₀],   ValuationClass (Valuatio
n R Γ₀) R Γ₀
· 使用引理 `Valuation.restrict_le_iff`：restrict_le_iff {x y : R} : v.restrict x <= v
.restrict y ↔ v x <= v y
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `StrictMono.le_iff_le`：StrictMono.le_iff_le (hf : StrictMono f) {a b : α}
 : f a <= f b ↔ a <= b
· 使用引理 `Valuation.RankOne.strictMono`：strictMono : StrictMono (hom v)
-/
theorem norm_le_one_iff : ‖x‖ ≤ 1 ↔ val.v x ≤ 1 := by
  rw [← map_one val.v, ← v.restrict_le_iff]
  simpa only [map_one] using! (Valuation.RankOne.strictMono val.v).le_iff_le (b := 1)

@[simp]
/-
**Valued.toNormedField.norm_lt_one_iff** 是 Mathlib 中的一个定理，位于命名空间 `Valued.toNorme
dField`。
形式化陈述：norm_lt_one_iff : ‖x‖ < 1 ↔ val.v x < 1
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `map_one`：map_one [OneHomClass F M N] (f : F) : f 1 = 1
· 使用定理 `MonoidHomClass.toOneHomClass`：∀ {F : Type u_10} {M : outParam (Type u_11
)} {N : outParam (Type u_12)} {inst : MulOne M} {inst_1 : MulOne N}   {inst_2 : 
FunLike F M N} [se…
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `ValuationClass.toMonoidWithZeroHomClass`：∀ {F : Type u_7} {R : outParam 
(Type u_5)} {Γ₀ : outParam (Type u_6)} {inst : LinearOrderedCommMonoidWithZero Γ
₀}   {inst_1 : Ring R} {inst_…
· 使用定理 `Valuation.instValuationClass`：∀ {R : Type u_3} {Γ₀ : Type u_4} [inst : R
ing R] [inst_1 : LinearOrderedCommMonoidWithZero Γ₀],   ValuationClass (Valuatio
n R Γ₀) R Γ₀
· 使用引理 `Valuation.restrict_lt_iff`：restrict_lt_iff {x y : R} : v.restrict x < v.
restrict y ↔ v x < v y
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `StrictMono.lt_iff_lt`：StrictMono.lt_iff_lt (hf : StrictMono f) {a b : α}
 : f a < f b ↔ a < b
· 使用引理 `Valuation.RankOne.strictMono`：strictMono : StrictMono (hom v)
-/
theorem norm_lt_one_iff : ‖x‖ < 1 ↔ val.v x < 1 := by
  rw [← map_one val.v, ← v.restrict_lt_iff]
  simpa only [map_one] using! (Valuation.RankOne.strictMono val.v).lt_iff_lt (b := 1)

@[simp]
/-
**Valued.toNormedField.one_le_norm_iff** 是 Mathlib 中的一个定理，位于命名空间 `Valued.toNorme
dField`。
形式化陈述：one_le_norm_iff : 1 <= ‖x‖ ↔ 1 <= val.v x
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `map_one`：map_one [OneHomClass F M N] (f : F) : f 1 = 1
· 使用定理 `MonoidHomClass.toOneHomClass`：∀ {F : Type u_10} {M : outParam (Type u_11
)} {N : outParam (Type u_12)} {inst : MulOne M} {inst_1 : MulOne N}   {inst_2 : 
FunLike F M N} [se…
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `ValuationClass.toMonoidWithZeroHomClass`：∀ {F : Type u_7} {R : outParam 
(Type u_5)} {Γ₀ : outParam (Type u_6)} {inst : LinearOrderedCommMonoidWithZero Γ
₀}   {inst_1 : Ring R} {inst_…
· 使用定理 `Valuation.instValuationClass`：∀ {R : Type u_3} {Γ₀ : Type u_4} [inst : R
ing R] [inst_1 : LinearOrderedCommMonoidWithZero Γ₀],   ValuationClass (Valuatio
n R Γ₀) R Γ₀
· 使用引理 `Valuation.restrict_le_iff`：restrict_le_iff {x y : R} : v.restrict x <= v
.restrict y ↔ v x <= v y
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `StrictMono.le_iff_le`：StrictMono.le_iff_le (hf : StrictMono f) {a b : α}
 : f a <= f b ↔ a <= b
· 使用引理 `Valuation.RankOne.strictMono`：strictMono : StrictMono (hom v)
-/
theorem one_le_norm_iff : 1 ≤ ‖x‖ ↔ 1 ≤ val.v x := by
  rw [← map_one val.v, ← v.restrict_le_iff]
  simpa only [map_one] using! (Valuation.RankOne.strictMono val.v).le_iff_le (a := 1)

@[simp]
/-
**Valued.toNormedField.one_lt_norm_iff** 是 Mathlib 中的一个定理，位于命名空间 `Valued.toNorme
dField`。
形式化陈述：one_lt_norm_iff : 1 < ‖x‖ ↔ 1 < val.v x
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `map_one`：map_one [OneHomClass F M N] (f : F) : f 1 = 1
· 使用定理 `MonoidHomClass.toOneHomClass`：∀ {F : Type u_10} {M : outParam (Type u_11
)} {N : outParam (Type u_12)} {inst : MulOne M} {inst_1 : MulOne N}   {inst_2 : 
FunLike F M N} [se…
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `ValuationClass.toMonoidWithZeroHomClass`：∀ {F : Type u_7} {R : outParam 
(Type u_5)} {Γ₀ : outParam (Type u_6)} {inst : LinearOrderedCommMonoidWithZero Γ
₀}   {inst_1 : Ring R} {inst_…
· 使用定理 `Valuation.instValuationClass`：∀ {R : Type u_3} {Γ₀ : Type u_4} [inst : R
ing R] [inst_1 : LinearOrderedCommMonoidWithZero Γ₀],   ValuationClass (Valuatio
n R Γ₀) R Γ₀
· 使用引理 `Valuation.restrict_lt_iff`：restrict_lt_iff {x y : R} : v.restrict x < v.
restrict y ↔ v x < v y
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `StrictMono.lt_iff_lt`：StrictMono.lt_iff_lt (hf : StrictMono f) {a b : α}
 : f a < f b ↔ a < b
· 使用引理 `Valuation.RankOne.strictMono`：strictMono : StrictMono (hom v)
-/
theorem one_lt_norm_iff : 1 < ‖x‖ ↔ 1 < val.v x := by
  rw [← map_one val.v, ← v.restrict_lt_iff]
  simpa only [map_one] using! (Valuation.RankOne.strictMono val.v).lt_iff_lt (a := 1)
/-
**Valued.toNormedField.setOfPred_mem_integer_eq_closedBall** 是 Mathlib 中的一个引理，位于
命名空间 `Valued.toNormedField`。
形式化陈述：setOfPred_mem_integer_eq_closedBall : { x : L | x in Valued.v.integer } = 
Metric.closedBall 0 1
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `dist_zero_right`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (a : E),
 dist a 0 = ‖a‖
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma setOfPred_mem_integer_eq_closedBall :
    { x : L | x ∈ Valued.v.integer } = Metric.closedBall 0 1 := by
  ext x
  simp [mem_integer_iff]

@[deprecated (since := "2026-07-09")]
alias setOf_mem_integer_eq_closedBall := setOfPred_mem_integer_eq_closedBall

end toNormedField

/--
The nontrivially normed field structure determined by a rank one valuation.
-/
@[instance_reducible]
/-
**Valued.toNontriviallyNormedField** 是 Mathlib 中的一个定义，位于命名空间 `Valued`。
形式化陈述：toNontriviallyNormedField : NontriviallyNormedField L
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The nontrivially normed field structure determined by a rank one valuation.
-/
def toNontriviallyNormedField : NontriviallyNormedField L := {
  val.toNormedField with
  non_trivial := by
    obtain ⟨x, hx⟩ := Valuation.RankOne.nontrivial val.v
    rcases Valuation.val_le_one_or_val_inv_le_one val.v x with h | h
    · use x⁻¹
      simp only [toNormedField.one_lt_norm_iff, map_inv₀, one_lt_inv₀ (zero_lt_iff.mpr hx.1),
          lt_of_le_of_ne h hx.2]
    · use x
      simp only [map_inv₀, inv_le_one₀ <| zero_lt_iff.mpr hx.1] at h
      simp only [toNormedField.one_lt_norm_iff, lt_of_le_of_ne h hx.2.symm]
}

scoped[Valued] attribute [instance] Valued.toNontriviallyNormedField

end Valued

