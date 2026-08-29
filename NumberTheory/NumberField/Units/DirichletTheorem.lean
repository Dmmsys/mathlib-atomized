/-
Copyright (c) 2023 Xavier Roblot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xavier Roblot
-/
module

public import Mathlib.LinearAlgebra.Dimension.Torsion.Basic
public import Mathlib.LinearAlgebra.Matrix.Gershgorin
public import Mathlib.NumberTheory.NumberField.CanonicalEmbedding.ConvexBody
public import Mathlib.NumberTheory.NumberField.Units.Basic

/-!
# Dirichlet theorem on the group of units of a number field

This file is devoted to the proof of Dirichlet unit theorem that states that the group of
units `(𝓞 K)ˣ` of units of the ring of integers `𝓞 K` of a number field `K` modulo its torsion
subgroup is a free `ℤ`-module of rank `card (InfinitePlace K) - 1`.

## Main definitions

* `NumberField.Units.rank`: the unit rank of the number field `K`.

* `NumberField.Units.fundSystem`: a fundamental system of units of `K`.

* `NumberField.Units.basisModTorsion`: a `ℤ`-basis of `(𝓞 K)ˣ ⧸ (torsion K)`
  as an additive `ℤ`-module.

## Main results

* `NumberField.Units.rank_modTorsion`: the `ℤ`-rank of `(𝓞 K)ˣ ⧸ (torsion K)` is equal to
  `card (InfinitePlace K) - 1`.

* `NumberField.Units.exist_unique_eq_mul_prod`: **Dirichlet Unit Theorem**. Any unit of `𝓞 K`
  can be written uniquely as the product of a root of unity and powers of the units of the
  fundamental system `fundSystem`.

## Tags
number field, units, Dirichlet unit theorem
-/

@[expose] public section

noncomputable section

open Module NumberField NumberField.InfinitePlace NumberField.Units

variable (K : Type*) [Field K]

namespace NumberField.Units.dirichletUnitTheorem

/-!
### Dirichlet Unit Theorem

We define a group morphism from `(𝓞 K)ˣ` to `logSpace K`, defined as
`{w : InfinitePlace K // w ≠ w₀} → ℝ` where `w₀` is a distinguished (arbitrary) infinite place,
prove that its kernel is the torsion subgroup (see `logEmbedding_eq_zero_iff`) and that its image,
called `unitLattice`, is a full `ℤ`-lattice. It follows that `unitLattice` is a free `ℤ`-module
(see `instModuleFree_unitLattice`) of rank `card (InfinitePlace K) - 1` (see `unitLattice_rank`).
To prove that the `unitLattice` is a full `ℤ`-lattice, we need to prove that it is discrete
(see `unitLattice_inter_ball_finite`) and that it spans the full space over `ℝ`
(see `unitLattice_span_eq_top`); this is the main part of the proof, see the section `span_top`
below for more details.
-/

open Finset

variable {K}

section NumberField

variable [NumberField K]

/--
Definition of `w₀` / `w₀` 的定义

English:
definition w₀
  signature: : InfinitePlace K
  body: (inferInstance : Nonempty (InfinitePlace K)).some

中文:
定义 w₀
  签名: : InfinitePlace K
  定义体: (inferInstance : Nonempty (InfinitePlace K)).some

Depends on / 依赖: InfinitePlace, Nonempty
-/
def w₀ : InfinitePlace K := (inferInstance : Nonempty (InfinitePlace K)).some

variable (K) in
/--
Definition of `logSpace` / `logSpace` 的定义

English:
abbreviation logSpace
  body: {w : InfinitePlace K // w != w₀} -> Real

中文:
缩写 logSpace
  定义体: {w : InfinitePlace K // w != w₀} -> Real

Depends on / 依赖: InfinitePlace
-/
abbrev logSpace := {w : InfinitePlace K // w != w₀} -> Real

variable (K) in
/--
Definition of `_root_.NumberField.Units.logEmbedding` / `_root_.NumberField.Units.logEmbedding` 的定义

English:
definition _root_.NumberField.Units.logEmbedding
  signature: :
  body: { toFun := fun x w => mult w.val * Real.log (w.val ↑x.toMul)
  map_zero' := by simp; rfl
  map_add' := fun _ _ => by simp [Real.log_mul, mul_add]; rfl }

@[simp]

中文:
定义 _root_.数域.单位群.logEmbedding
  签名: :
  定义体: { toFun := fun x w => mult w.val * Real.log (w.val ↑x.toMul)
  map_zero' := by simp; rfl
  map_add' := fun _ _ => by simp [Real.log_mul, mul_add]; rfl }

@[simp]

Depends on / 依赖: Real.log, Real.log_mul, log_mul, map_add, map_zero, mul_add, w.val, x.toMul
-/
def _root_.NumberField.Units.logEmbedding :
    Additive ((𝓞 K)ˣ) ->+ logSpace K :=
{ toFun := fun x w => mult w.val * Real.log (w.val ↑x.toMul)
  map_zero' := by simp; rfl
  map_add' := fun _ _ => by simp [Real.log_mul, mul_add]; rfl }

@[simp]
/--
theorem `logEmbedding_component` / 定理 `logEmbedding_component`

English:
theorem logEmbedding_component
  given: (x : (𝓞 K)ˣ) (w : {w : InfinitePlace K // w != w₀})
  proof: rfl

中文:
定理 logEmbedding_component
  条件: (x : (𝓞 K)ˣ) (w : {w : InfinitePlace K // w != w₀})
  证明: rfl
-/
theorem logEmbedding_component (x : (𝓞 K)ˣ) (w : {w : InfinitePlace K // w != w₀}) :
    (logEmbedding K (Additive.ofMul x)) w = mult w.val * Real.log (w.val x) := rfl

open scoped Classical in
/--
theorem `sum_logEmbedding_component` / 定理 `sum_logEmbedding_component`

English:
theorem sum_logEmbedding_component
  given: (x : (𝓞 K)ˣ)
  proof: by
  have h := sum_mult_mul_log x
  rw [Fintype.sum_eq_add_sum_subtype_ne _ w₀]; rw [add_comm]; rw [add_eq_zero_iff_eq_neg]; rw [← neg_mul] at h
  simpa [logEmbedding_component] using h

中文:
定理 sum_logEmbedding_component
  条件: (x : (𝓞 K)ˣ)
  证明: by
  have h := sum_mult_mul_log x
  rw [Fintype.sum_eq_add_sum_subtype_ne _ w₀]; rw [add_comm]; rw [add_eq_zero_iff_eq_neg]; rw [← neg_mul] at h
  simpa [logEmbedding_component] using h

Depends on / 依赖: Fintype, Fintype.sum_eq_add_sum_subtype_ne, add_comm, add_eq_zero_iff_eq_neg, logEmbedding_component, neg_mul, sum_eq_add_sum_subtype_ne, sum_mult_mul_log
-/
theorem sum_logEmbedding_component (x : (𝓞 K)ˣ) :
    ∑ w, logEmbedding K (Additive.ofMul x) w =
      -mult (w₀ : InfinitePlace K) * Real.log (w₀ (x : K)) := by
  have h := sum_mult_mul_log x
  rw [Fintype.sum_eq_add_sum_subtype_ne _ w₀]; rw [add_comm]; rw [add_eq_zero_iff_eq_neg]; rw [← neg_mul] at h
  simpa [logEmbedding_component] using h

end NumberField

/--
theorem `mult_log_place_eq_zero` / 定理 `mult_log_place_eq_zero`

English:
theorem mult_log_place_eq_zero
  given: {x : (𝓞 K)ˣ} {w : InfinitePlace K}
  proof: by
  rw [mul_eq_zero]; rw [or_iff_right]; rw [Real.log_eq_zero]; rw [or_iff_right]; rw [or_iff_left]
  · linarith [(apply_nonneg _ _ : 0 <= w x)]
  · exact (Units.pos_at_place _ _).ne'
  · exact mult_coe_ne_zero

中文:
定理 mult_log_place_eq_zero
  条件: {x : (𝓞 K)ˣ} {w : InfinitePlace K}
  证明: by
  rw [mul_eq_zero]; rw [or_iff_right]; rw [Real.log_eq_zero]; rw [or_iff_right]; rw [or_iff_left]
  · linarith [(apply_nonneg _ _ : 0 <= w x)]
  · exact (Units.pos_at_place _ _).ne'
  · exact mult_coe_ne_zero

Depends on / 依赖: Real.log_eq_zero, Units.pos_at_place, apply_nonneg, log_eq_zero, mul_eq_zero, mult_coe_ne_zero, or_iff_left, or_iff_right, pos_at_place
-/
theorem mult_log_place_eq_zero {x : (𝓞 K)ˣ} {w : InfinitePlace K} :
    mult w * Real.log (w x) = 0 ↔ w x = 1 := by
  rw [mul_eq_zero]; rw [or_iff_right]; rw [Real.log_eq_zero]; rw [or_iff_right]; rw [or_iff_left]
  · linarith [(apply_nonneg _ _ : 0 <= w x)]
  · exact (Units.pos_at_place _ _).ne'
  · exact mult_coe_ne_zero

variable [NumberField K]

/--
theorem `logEmbedding_eq_zero_iff` / 定理 `logEmbedding_eq_zero_iff`

English:
theorem logEmbedding_eq_zero_iff
  given: {x : (𝓞 K)ˣ}
  proof: by
  rw [mem_torsion]
  refine ⟨fun h w => ?_, fun h => ?_⟩
  · by_cases hw : w = w₀
    · suffices -mult w₀ * Real.log (w₀ (x : K)) = 0 by
        rw [neg_mul]; rw [neg_eq_zero]; rw [← hw] at this
        exact mult_log_place_eq_zero.mp this
      rw [← sum_logEmbedding_component]; rw [sum_eq_zero]

中文:
定理 logEmbedding_eq_zero_iff
  条件: {x : (𝓞 K)ˣ}
  证明: by
  rw [mem_torsion]
  refine ⟨fun h w => ?_, fun h => ?_⟩
  · by_cases hw : w = w₀
    · suffices -mult w₀ * Real.log (w₀ (x : K)) = 0 by
        rw [neg_mul]; rw [neg_eq_zero]; rw [← hw] at this
        exact mult_log_place_eq_zero.mp this
      rw [← sum_logEmbedding_component]; rw [sum_eq_zero]

Depends on / 依赖: Pi.zero_apply, Real.log, Real.log_one, logEmbedding_component, log_one, mem_torsion, mul_zero, mult_log_place_eq_zero, mult_log_place_eq_zero.mp, neg_eq_zero, neg_mul, sum_eq_zero, sum_logEmbedding_component, w.val, zero_apply
-/
theorem logEmbedding_eq_zero_iff {x : (𝓞 K)ˣ} :
    logEmbedding K (Additive.ofMul x) = 0 ↔ x in torsion K := by
  rw [mem_torsion]
  refine ⟨fun h w => ?_, fun h => ?_⟩
  · by_cases hw : w = w₀
    · suffices -mult w₀ * Real.log (w₀ (x : K)) = 0 by
        rw [neg_mul]; rw [neg_eq_zero]; rw [← hw] at this
        exact mult_log_place_eq_zero.mp this
      rw [← sum_logEmbedding_component]; rw [sum_eq_zero]
      exact fun w _ => congrFun h w
    · exact mult_log_place_eq_zero.mp (congrFun h ⟨w, hw⟩)
  · ext w
    rw [logEmbedding_component]; rw [h w.val]; rw [Real.log_one]; rw [mul_zero]; rw [Pi.zero_apply]

/--
theorem `logEmbedding_ker` / 定理 `logEmbedding_ker`

English:
theorem logEmbedding_ker
  statement: (logEmbedding K).ker = (torsion K).toAddSubgroup
  proof: by
  ext x
  rw [AddMonoidHom.mem_ker]; rw [← ofMul_toMul x]; rw [logEmbedding_eq_zero_iff]
  simp

中文:
定理 logEmbedding_ker
  结论: (logEmbedding K).ker = (torsion K).toAddSubgroup
  证明: by
  ext x
  rw [AddMonoidHom.mem_ker]; rw [← ofMul_toMul x]; rw [logEmbedding_eq_zero_iff]
  simp

Depends on / 依赖: AddMonoidHom, AddMonoidHom.mem_ker, logEmbedding_eq_zero_iff, mem_ker, ofMul_toMul
-/
theorem logEmbedding_ker : (logEmbedding K).ker = (torsion K).toAddSubgroup := by
  ext x
  rw [AddMonoidHom.mem_ker]; rw [← ofMul_toMul x]; rw [logEmbedding_eq_zero_iff]
  simp

/--
theorem `map_logEmbedding_sup_torsion` / 定理 `map_logEmbedding_sup_torsion`

English:
theorem map_logEmbedding_sup_torsion
  given: (s : AddSubgroup (Additive (𝓞 K)ˣ))
  proof: by
  rw [← logEmbedding_ker]; rw [AddSubgroup.map_eq_map_iff]; rw [sup_right_idem]

中文:
定理 map_logEmbedding_sup_torsion
  条件: (s : 加法子群 (加性 (𝓞 K)ˣ))
  证明: by
  rw [← logEmbedding_ker]; rw [AddSubgroup.map_eq_map_iff]; rw [sup_right_idem]

Depends on / 依赖: AddSubgroup, AddSubgroup.map_eq_map_iff, logEmbedding_ker, map_eq_map_iff, sup_right_idem
-/
theorem map_logEmbedding_sup_torsion (s : AddSubgroup (Additive (𝓞 K)ˣ)) :
    (s ⊔ (torsion K).toAddSubgroup).map (logEmbedding K) = s.map (logEmbedding K) := by
  rw [← logEmbedding_ker]; rw [AddSubgroup.map_eq_map_iff]; rw [sup_right_idem]

open scoped Classical in
/--
theorem `logEmbedding_component_le` / 定理 `logEmbedding_component_le`

English:
theorem logEmbedding_component_le
  statement: {r : Real} {x : (𝓞 K)ˣ} (hr : 0 <= r) (h : ‖logEmbedding K x‖ <= r)
  proof: by
  lift r to NNReal using hr
  simp_rw [Pi.norm_def, NNReal.coe_le_coe, Finset.sup_le_iff, ← NNReal.coe_le_coe] at h
  exact h w (mem_univ _)

中文:
定理 logEmbedding_component_le
  结论: {r : 实数} {x : (𝓞 K)ˣ} (hr : 0 <= r) (h : ‖logEmbedding K x‖ <= r)
  证明: by
  lift r to NNReal using hr
  simp_rw [Pi.norm_def, NNReal.coe_le_coe, Finset.sup_le_iff, ← NNReal.coe_le_coe] at h
  exact h w (mem_univ _)

Depends on / 依赖: Finset, Finset.sup_le_iff, NNReal, NNReal.coe_le_coe, Pi.norm_def, coe_le_coe, mem_univ, norm_def, simp_rw, sup_le_iff
-/
theorem logEmbedding_component_le {r : Real} {x : (𝓞 K)ˣ} (hr : 0 <= r) (h : ‖logEmbedding K x‖ <= r)
    (w : {w : InfinitePlace K // w != w₀}) : |logEmbedding K (Additive.ofMul x) w| <= r := by
  lift r to NNReal using hr
  simp_rw [Pi.norm_def, NNReal.coe_le_coe, Finset.sup_le_iff, ← NNReal.coe_le_coe] at h
  exact h w (mem_univ _)

set_option backward.isDefEq.respectTransparency.types false in
open scoped Classical in
/--
theorem `log_le_of_logEmbedding_le` / 定理 `log_le_of_logEmbedding_le`

English:
theorem log_le_of_logEmbedding_le
  statement: {r : Real} {x : (𝓞 K)ˣ} (hr : 0 <= r)
  proof: by
  have tool : forall x : Real, 0 <= x -> x <= mult w * x := fun x hx => by
    nth_rw 1 [← one_mul x]
    refine mul_le_mul ?_ le_rfl hx ?_
    all_goals { rw [mult]; split_ifs <;> norm_num }
  by_cases hw : w = w₀
  · have hyp := congr_arg (‖·‖) (sum_logEmbedding_component x).symm
    replace hy

中文:
定理 log_le_of_logEmbedding_le
  结论: {r : 实数} {x : (𝓞 K)ˣ} (hr : 0 <= r)
  证明: by
  have tool : forall x : Real, 0 <= x -> x <= mult w * x := fun x hx => by
    nth_rw 1 [← one_mul x]
    refine mul_le_mul ?_ le_rfl hx ?_
    all_goals { rw [mult]; split_ifs <;> norm_num }
  by_cases hw : w = w₀
  · have hyp := congr_arg (‖·‖) (sum_logEmbedding_component x).symm
    replace hy

Depends on / 依赖: Nat.abs_cast, Real.norm_eq_abs, abs_cast, abs_nonneg, all_goals, congr_arg, le_of_eq, le_rfl, le_trans, mul_le_mul, norm_eq_abs, norm_mul, norm_neg, norm_sum_le, nth_rw, one_mul, replace, simp_rw, split_ifs, sum_le_card_nsmul
-/
theorem log_le_of_logEmbedding_le {r : Real} {x : (𝓞 K)ˣ} (hr : 0 <= r)
    (h : ‖logEmbedding K (Additive.ofMul x)‖ <= r) (w : InfinitePlace K) :
    |Real.log (w x)| <= (Fintype.card (InfinitePlace K)) * r := by
  have tool : forall x : Real, 0 <= x -> x <= mult w * x := fun x hx => by
    nth_rw 1 [← one_mul x]
    refine mul_le_mul ?_ le_rfl hx ?_
    all_goals { rw [mult]; split_ifs <;> norm_num }
  by_cases hw : w = w₀
  · have hyp := congr_arg (‖·‖) (sum_logEmbedding_component x).symm
    replace hyp := (le_of_eq hyp).trans (norm_sum_le _ _)
    simp_rw [norm_mul, norm_neg, Real.norm_eq_abs, Nat.abs_cast] at hyp
    refine (le_trans ?_ hyp).trans ?_
    · rw [← hw]
      exact tool _ (abs_nonneg _)
    · refine (sum_le_card_nsmul univ _ _
        (fun w _ => logEmbedding_component_le hr h w)).trans ?_
      rw [nsmul_eq_mul]
      refine mul_le_mul ?_ le_rfl hr (Fintype.card (InfinitePlace K)).cast_nonneg
      simp
  · have hyp := logEmbedding_component_le hr h ⟨w, hw⟩
    rw [logEmbedding_component]; rw [abs_mul]; rw [Nat.abs_cast] at hyp
    refine (le_trans ?_ hyp).trans ?_
    · exact tool _ (abs_nonneg _)
    · nth_rw 1 [← one_mul r]
      exact mul_le_mul (Nat.one_le_cast.mpr Fintype.card_pos) (le_of_eq rfl) hr (Nat.cast_nonneg _)

variable (K)

/--
Definition of `_root_.NumberField.Units.unitLattice` / `_root_.NumberField.Units.unitLattice` 的定义

English:
definition _root_.NumberField.Units.unitLattice
  signature: :
  body: Submodule.map (logEmbedding K).toIntLinearMap ⊤

中文:
定义 _root_.数域.单位群.unitLattice
  签名: :
  定义体: Submodule.map (logEmbedding K).toIntLinearMap ⊤

Depends on / 依赖: Submodule, Submodule.map, logEmbedding, toIntLinearMap
-/
noncomputable def _root_.NumberField.Units.unitLattice :
    Submodule Int (logSpace K) :=
  Submodule.map (logEmbedding K).toIntLinearMap ⊤

open scoped Classical in
/--
theorem `unitLattice_inter_ball_finite` / 定理 `unitLattice_inter_ball_finite`

English:
theorem unitLattice_inter_ball_finite
  given: (r : Real)
  proof: by
  obtain hr | hr := lt_or_ge r 0
  · convert! Set.finite_empty
    rw [Metric.closedBall_eq_empty.mpr hr]
    exact Set.inter_empty _
  · suffices {x : (𝓞 K)ˣ | IsIntegral Int (x : K) ∧
        forall (φ : K ->+* Complex), ‖φ x‖ <= Real.exp ((Fintype.card (InfinitePlace K)) * r)}.Finite by
      

中文:
定理 unitLattice_inter_ball_finite
  条件: (r : 实数)
  证明: by
  obtain hr | hr := lt_or_ge r 0
  · convert! Set.finite_empty
    rw [Metric.closedBall_eq_empty.mpr hr]
    exact Set.inter_empty _
  · suffices {x : (𝓞 K)ˣ | IsIntegral Int (x : K) ∧
        forall (φ : K ->+* Complex), ‖φ x‖ <= Real.exp ((Fintype.card (InfinitePlace K)) * r)}.Finite by
      

Depends on / 依赖: Finite, Fintype, Fintype.card, InfinitePlace, IsIntegral, Metric, Metric.closedBall_eq_empty.mpr, Real.exp, Real.log_le_iff_le_exp, Set.Finite.image, Set.finite_empty, Set.inter_empty, closedBall_eq_empty, coe_ne_zero, convert, finite_empty, inter_empty, le_iff_le, logEmbedding, log_le_iff_le_exp
-/
theorem unitLattice_inter_ball_finite (r : Real) :
    ((unitLattice K : Set (logSpace K)) inter Metric.closedBall 0 r).Finite := by
  obtain hr | hr := lt_or_ge r 0
  · convert! Set.finite_empty
    rw [Metric.closedBall_eq_empty.mpr hr]
    exact Set.inter_empty _
  · suffices {x : (𝓞 K)ˣ | IsIntegral Int (x : K) ∧
        forall (φ : K ->+* Complex), ‖φ x‖ <= Real.exp ((Fintype.card (InfinitePlace K)) * r)}.Finite by
      refine (Set.Finite.image (logEmbedding K) this).subset ?_
      rintro _ ⟨⟨x, ⟨_, rfl⟩⟩, hx⟩
      refine ⟨x, ⟨x.val.prop, (le_iff_le _ _).mp (fun w => (Real.log_le_iff_le_exp ?_).mp ?_)⟩, rfl⟩
      · exact pos_iff.mpr (coe_ne_zero x)
      · rw [mem_closedBall_zero_iff] at hx
        exact (le_abs_self _).trans (log_le_of_logEmbedding_le hr hx w)
    refine Set.Finite.of_finite_image ?_ (coe_injective K).injOn
    refine (Embeddings.finite_of_norm_le K Complex
        (Real.exp ((Fintype.card (InfinitePlace K)) * r))).subset ?_
    rintro _ ⟨x, ⟨⟨h_int, h_le⟩, rfl⟩⟩
    exact ⟨h_int, h_le⟩

section span_top

/-!
#### Section `span_top`

In this section, we prove that the span over `ℝ` of the `unitLattice` is equal to the full space.
For this, we construct for each infinite place `w₁ ≠ w₀` a unit `u_w₁` of `K` such that, for all
infinite places `w` such that `w ≠ w₁`, we have `Real.log w (u_w₁) < 0`
(and thus `Real.log w₁ (u_w₁) > 0`). It follows then from a determinant computation
(using `Matrix.det_ne_zero_of_sum_col_lt_diag`) that the image by `logEmbedding` of these units is
a `ℝ`-linearly independent family. The unit `u_w₁` is obtained by constructing a sequence `seq n`
of nonzero algebraic integers that is strictly decreasing at infinite places distinct from `w₁` and
of norm `≤ B`. Since there are finitely many ideals of norm `≤ B`, there exists two term in the
sequence defining the same ideal and their quotient is the desired unit `u_w₁` (see `exists_unit`).
-/

open NumberField.mixedEmbedding NNReal

variable (w₁ : InfinitePlace K) {B : Nat} (hB : minkowskiBound K 1 < (convexBodyLTFactor K) * B)

set_option backward.isDefEq.respectTransparency false in
include hB in
/--
theorem `seq_next` / 定理 `seq_next`

English:
theorem seq_next
  given: {x : 𝓞 K} (hx : x != 0)
  proof: by
  have hx' := RingOfIntegers.coe_ne_zero_iff.mpr hx
  let f : InfinitePlace K -> Real>=0 :=
    fun w => ⟨(w x) / 2, div_nonneg (AbsoluteValue.nonneg _ _) (by simp)⟩
  suffices forall w, w != w₁ -> f w != 0 by
    obtain ⟨g, h_geqf, h_gprod⟩ := adjust_f K B this
    obtain ⟨y, h_ynz, h_yle⟩ := ex

中文:
定理 seq_next
  条件: {x : 𝓞 K} (hx : x != 0)
  证明: by
  have hx' := RingOfIntegers.coe_ne_zero_iff.mpr hx
  let f : InfinitePlace K -> Real>=0 :=
    fun w => ⟨(w x) / 2, div_nonneg (AbsoluteValue.nonneg _ _) (by simp)⟩
  suffices forall w, w != w₁ -> f w != 0 by
    obtain ⟨g, h_geqf, h_gprod⟩ := adjust_f K B this
    obtain ⟨y, h_ynz, h_yle⟩ := ex

Depends on / 依赖: AbsoluteValue, AbsoluteValue.nonneg, ENNReal, InfinitePlace, NNReal, RingOfIntegers, RingOfIntegers.coe_ne_zero_iff.mpr, adjust_f, coe_ne_zero_iff, congr_arg, convert, convexBodyLT_volume, div_nonneg, exists_ne_zero_mem_ringOfIntegers_lt, h_geqf, h_gprod, h_yle, h_ynz, nonneg
-/
theorem seq_next {x : 𝓞 K} (hx : x != 0) :
    exists y : 𝓞 K, y != 0 ∧
      (forall w, w != w₁ -> w y < w x) ∧
      |Algebra.norm Rat (y : K)| <= B := by
  have hx' := RingOfIntegers.coe_ne_zero_iff.mpr hx
  let f : InfinitePlace K -> Real>=0 :=
    fun w => ⟨(w x) / 2, div_nonneg (AbsoluteValue.nonneg _ _) (by simp)⟩
  suffices forall w, w != w₁ -> f w != 0 by
    obtain ⟨g, h_geqf, h_gprod⟩ := adjust_f K B this
    obtain ⟨y, h_ynz, h_yle⟩ := exists_ne_zero_mem_ringOfIntegers_lt K (f := g)
      (by rw [convexBodyLT_volume]; convert! hB; exact congr_arg ((↑) : NNReal -> ENNReal) h_gprod)
    refine ⟨y, h_ynz, fun w hw => (h_geqf w hw ▸ h_yle w).trans ?_, ?_⟩
    · rw [← Rat.cast_le (K := Real), Rat.cast_natCast]
      calc
        _ = ∏ w : InfinitePlace K, w (algebraMap _ K y) ^ mult w :=
          (prod_eq_abs_norm (algebraMap _ K y)).symm
        _ <= ∏ w : InfinitePlace K, (g w : Real) ^ mult w := by gcongr with w; exact (h_yle w).le
        _ <= (B : Real) := by
          simp_rw [← NNReal.coe_pow, ← NNReal.coe_prod]
          exact le_of_eq (congr_arg toReal h_gprod)
    · refine div_lt_self ?_ (by simp)
      exact pos_iff.mpr hx'
  intro _ _
  rw [ne_eq]; rw [Nonneg.mk_eq_zero]; rw [div_eq_zero_iff]; rw [map_eq_zero]; rw [not_or]
  exact ⟨hx', by simp⟩

/--
Definition of `seq` / `seq` 的定义

English:
definition seq
  signature: : Nat -> { x : 𝓞 K // x != 0 }

中文:
定义 seq
  签名: : 自然数 -> { x : 𝓞 K // x != 0 }
-/
def seq : Nat -> { x : 𝓞 K // x != 0 }
  | 0 => ⟨1, by simp⟩
  | n + 1 =>
    ⟨(seq_next K w₁ hB (seq n).prop).choose, (seq_next K w₁ hB (seq n).prop).choose_spec.1⟩

/--
theorem `seq_ne_zero` / 定理 `seq_ne_zero`

English:
theorem seq_ne_zero
  given: (n : Nat)
  statement: algebraMap (𝓞 K) K (seq K w₁ hB n) != 0
  proof: RingOfIntegers.coe_ne_zero_iff.mpr (seq K w₁ hB n).prop

中文:
定理 seq_ne_zero
  条件: (n : 自然数)
  结论: algebraMap (𝓞 K) K (seq K w₁ hB n) != 0
  证明: RingOfIntegers.coe_ne_zero_iff.mpr (seq K w₁ hB n).prop

Depends on / 依赖: RingOfIntegers, RingOfIntegers.coe_ne_zero_iff.mpr, coe_ne_zero_iff
-/
theorem seq_ne_zero (n : Nat) : algebraMap (𝓞 K) K (seq K w₁ hB n) != 0 :=
  RingOfIntegers.coe_ne_zero_iff.mpr (seq K w₁ hB n).prop

/--
theorem `seq_decreasing` / 定理 `seq_decreasing`

English:
theorem seq_decreasing
  given: {n m : Nat} (h : n < m) (w : InfinitePlace K) (hw : w != w₁)
  proof: by
  induction m with
  | zero =>
      exfalso
      exact Nat.not_succ_le_zero n h
  | succ m m_ih =>
      cases eq_or_lt_of_le (Nat.le_of_lt_succ h) with
      | inl hr =>
          rw [hr]
          exact (seq_next K w₁ hB (seq K w₁ hB m).prop).choose_spec.2.1 w hw
      | inr hr =>
          r

中文:
定理 seq_decreasing
  条件: {n m : 自然数} (h : n < m) (w : InfinitePlace K) (hw : w != w₁)
  证明: by
  induction m with
  | zero =>
      exfalso
      exact Nat.not_succ_le_zero n h
  | succ m m_ih =>
      cases eq_or_lt_of_le (Nat.le_of_lt_succ h) with
      | inl hr =>
          rw [hr]
          exact (seq_next K w₁ hB (seq K w₁ hB m).prop).choose_spec.2.1 w hw
      | inr hr =>
          r

Depends on / 依赖: Nat.le_of_lt_succ, Nat.not_succ_le_zero, choose_spec, eq_or_lt_of_le, le_of_lt_succ, lt_trans, m_ih, not_succ_le_zero, seq_next
-/
theorem seq_decreasing {n m : Nat} (h : n < m) (w : InfinitePlace K) (hw : w != w₁) :
    w (algebraMap (𝓞 K) K (seq K w₁ hB m)) < w (algebraMap (𝓞 K) K (seq K w₁ hB n)) := by
  induction m with
  | zero =>
      exfalso
      exact Nat.not_succ_le_zero n h
  | succ m m_ih =>
      cases eq_or_lt_of_le (Nat.le_of_lt_succ h) with
      | inl hr =>
          rw [hr]
          exact (seq_next K w₁ hB (seq K w₁ hB m).prop).choose_spec.2.1 w hw
      | inr hr =>
          refine lt_trans ?_ (m_ih hr)
          exact (seq_next K w₁ hB (seq K w₁ hB m).prop).choose_spec.2.1 w hw

/--
theorem `seq_norm_le` / 定理 `seq_norm_le`

English:
theorem seq_norm_le
  given: (n : Nat)
  proof: by
  cases n with
  | zero =>
      have : 1 <= B := by
        contrapose! hB
        simp only [Nat.lt_one_iff.mp hB, CharP.cast_eq_zero, mul_zero, zero_le]
      simp only [ne_eq, seq, map_one, Int.natAbs_one, this]
  | succ n =>
      rw [← Nat.cast_le (α := Rat)]; rw [Nat.cast_natAbs]; rw [Int.

中文:
定理 seq_norm_le
  条件: (n : 自然数)
  证明: by
  cases n with
  | zero =>
      have : 1 <= B := by
        contrapose! hB
        simp only [Nat.lt_one_iff.mp hB, CharP.cast_eq_zero, mul_zero, zero_le]
      simp only [ne_eq, seq, map_one, Int.natAbs_one, this]
  | succ n =>
      rw [← Nat.cast_le (α := Rat)]; rw [Nat.cast_natAbs]; rw [Int.

Depends on / 依赖: Algebra, Algebra.coe_norm_int, CharP.cast_eq_zero, Int.cast_abs, Int.natAbs_one, Nat.cast_le, Nat.cast_natAbs, Nat.lt_one_iff.mp, cast_abs, cast_eq_zero, cast_le, cast_natAbs, choose_spec, coe_norm_int, contrapose, lt_one_iff, map_one, mul_zero, natAbs_one, ne_eq
-/
theorem seq_norm_le (n : Nat) :
    Int.natAbs (Algebra.norm Int (seq K w₁ hB n : 𝓞 K)) <= B := by
  cases n with
  | zero =>
      have : 1 <= B := by
        contrapose! hB
        simp only [Nat.lt_one_iff.mp hB, CharP.cast_eq_zero, mul_zero, zero_le]
      simp only [ne_eq, seq, map_one, Int.natAbs_one, this]
  | succ n =>
      rw [← Nat.cast_le (α := Rat)]; rw [Nat.cast_natAbs]; rw [Int.cast_abs]; rw [Algebra.coe_norm_int]
      exact (seq_next K w₁ hB (seq K w₁ hB n).prop).choose_spec.2.2

/--
theorem `exists_unit` / 定理 `exists_unit`

English:
theorem exists_unit
  given: (w₁ : InfinitePlace K)
  proof: by
  obtain ⟨B, hB⟩ : exists B : Nat, minkowskiBound K 1 < (convexBodyLTFactor K) * B := by
    conv => congr; ext; rw [mul_comm]
    exact ENNReal.exists_nat_mul_gt (ENNReal.coe_ne_zero.mpr (convexBodyLTFactor_ne_zero K))
      (ne_of_lt (minkowskiBound_lt_top K 1))
  rsuffices ⟨n, m, hnm, h⟩ : exi

中文:
定理 存在_unit
  条件: (w₁ : InfinitePlace K)
  证明: by
  obtain ⟨B, hB⟩ : exists B : Nat, minkowskiBound K 1 < (convexBodyLTFactor K) * B := by
    conv => congr; ext; rw [mul_comm]
    exact ENNReal.exists_nat_mul_gt (ENNReal.coe_ne_zero.mpr (convexBodyLTFactor_ne_zero K))
      (ne_of_lt (minkowskiBound_lt_top K 1))
  rsuffices ⟨n, m, hnm, h⟩ : exi

Depends on / 依赖: ENNReal, ENNReal.coe_ne_zero.mpr, ENNReal.exists_nat_mul_gt, Ideal.span, Ideal.span_singleton_eq_span_singleton.mp, Real.log_neg, coe_ne_zero, convexBodyLTFactor, convexBodyLTFactor_ne_zero, exists_nat_mul_gt, hu.c, hu.choose, log_neg, minkowskiBound, minkowskiBound_lt_top, mul_comm, ne_of_lt, pos_at_place, rsuffices, span_singleton_eq_span_singleton
-/
theorem exists_unit (w₁ : InfinitePlace K) :
    exists u : (𝓞 K)ˣ, forall w : InfinitePlace K, w != w₁ -> Real.log (w u) < 0 := by
  obtain ⟨B, hB⟩ : exists B : Nat, minkowskiBound K 1 < (convexBodyLTFactor K) * B := by
    conv => congr; ext; rw [mul_comm]
    exact ENNReal.exists_nat_mul_gt (ENNReal.coe_ne_zero.mpr (convexBodyLTFactor_ne_zero K))
      (ne_of_lt (minkowskiBound_lt_top K 1))
  rsuffices ⟨n, m, hnm, h⟩ : exists n m, n < m ∧
      (Ideal.span ({ (seq K w₁ hB n : 𝓞 K) }) = Ideal.span ({ (seq K w₁ hB m : 𝓞 K) }))
  · have hu := Ideal.span_singleton_eq_span_singleton.mp h
    refine ⟨hu.choose, fun w hw => Real.log_neg (pos_at_place hu.choose w) ?_⟩
    calc
      _ = w (algebraMap (𝓞 K) K (seq K w₁ hB m) * (algebraMap (𝓞 K) K (seq K w₁ hB n))⁻¹) := by
        rw [← congr_arg (algebraMap (𝓞 K) K) hu.choose_spec]; rw [mul_comm]; rw [map_mul (algebraMap _ _)]; rw [← mul_assoc]; rw [inv_mul_cancel₀ (seq_ne_zero K w₁ hB n)]; rw [one_mul]
      _ = w (algebraMap (𝓞 K) K (seq K w₁ hB m)) * w (algebraMap (𝓞 K) K (seq K w₁ hB n))⁻¹ :=
        map_mul _ _ _
      _ < 1 := by
        rw [map_inv₀]; rw [mul_inv_lt_iff₀' (pos_iff.mpr (seq_ne_zero K w₁ hB n))]; rw [mul_one]
        exact seq_decreasing K w₁ hB hnm w hw
  refine Set.Finite.exists_lt_map_eq_of_forall_mem (t := {I : Ideal (𝓞 K) | Ideal.absNorm I <= B})
    (fun n => ?_) (Ideal.finite_setOfPred_absNorm_le B)
  rw [Set.mem_ofPred_eq]; rw [Ideal.absNorm_span_singleton]
  exact seq_norm_le K w₁ hB n

set_option backward.isDefEq.respectTransparency.types false in
/--
theorem `unitLattice_span_eq_top` / 定理 `unitLattice_span_eq_top`

English:
theorem unitLattice_span_eq_top
  proof: by
  classical
  refine le_antisymm le_top ?_
  -- The standard basis
  let B := Pi.basisFun Real {w : InfinitePlace K // w != w₀}
  -- The image by log_embedding of the family of units constructed above
  let v := fun w : { w : InfinitePlace K // w != w₀ } =>
    logEmbedding K (Additive.ofMul (exi

中文:
定理 unitLattice_span_eq_top
  证明: by
  classical
  refine le_antisymm le_top ?_
  -- The standard basis
  let B := Pi.basisFun Real {w : InfinitePlace K // w != w₀}
  -- The image by log_embedding of the family of units constructed above
  let v := fun w : { w : InfinitePlace K // w != w₀ } =>
    logEmbedding K (Additive.ofMul (exi

Depends on / 依赖: classical, le_antisymm, le_top
-/
theorem unitLattice_span_eq_top :
    Submodule.span Real (unitLattice K : Set (logSpace K)) = ⊤ := by
  classical
  refine le_antisymm le_top ?_
  -- The standard basis
  let B := Pi.basisFun Real {w : InfinitePlace K // w != w₀}
  -- The image by log_embedding of the family of units constructed above
  let v := fun w : { w : InfinitePlace K // w != w₀ } =>
    logEmbedding K (Additive.ofMul (exists_unit K w).choose)
  -- To prove the result, it is enough to prove that the family `v` is linearly independent
  suffices B.det v != 0 by
    rw [← isUnit_iff_ne_zero]; rw [← Basis.is_basis_iff_det] at this
    rw [← this.2]
    refine Submodule.span_monotone fun _ ⟨w, hw⟩ => ⟨(exists_unit K w).choose, trivial, hw⟩
  rw [Basis.det_apply]
  -- We use a specific lemma to prove that this determinant is nonzero
  refine det_ne_zero_of_sum_col_lt_diag (fun w => ?_)
  simp_rw [Real.norm_eq_abs, B, Basis.coePiBasisFun.toMatrix_eq_transpose, Matrix.transpose_apply]
  rw [← sub_pos]; rw [sum_congr rfl (fun x hx => abs_of_neg ?_)]; rw [sum_neg_distrib]; rw [sub_neg_eq_add]; rw [sum_erase_eq_sub (mem_univ _)]; rw [← add_comm_sub]
  · refine add_pos_of_nonneg_of_pos ?_ ?_
    · rw [sub_nonneg]
      exact le_abs_self _
    · rw [sum_logEmbedding_component (exists_unit K w).choose]
      refine mul_pos_of_neg_of_neg ?_ ((exists_unit K w).choose_spec _ w.prop.symm)
      rw [mult]; split_ifs <;> norm_num
  · refine mul_neg_of_pos_of_neg ?_ ((exists_unit K w).choose_spec x ?_)
    · rw [mult]; split_ifs <;> norm_num
    · exact Subtype.ext_iff.not.mp (ne_of_mem_erase hx)

end span_top

end dirichletUnitTheorem

section statements

variable [NumberField K]

open dirichletUnitTheorem Module

/--
Definition of `rank` / `rank` 的定义

English:
definition rank
  signature: : Nat
  body: Fintype.card (InfinitePlace K) - 1

中文:
定义 rank
  签名: : 自然数
  定义体: Fintype.card (InfinitePlace K) - 1

Depends on / 依赖: Fintype, Fintype.card, InfinitePlace
-/
def rank : Nat := Fintype.card (InfinitePlace K) - 1

/--
Instance `instDiscrete_unitLattice` / 实例 `instDiscrete_unitLattice`

English:
instance instDiscrete_unitLattice
  signature: : DiscreteTopology (unitLattice K)
  body: by
  classical
  refine discreteTopology_of_isOpen_singleton_zero ?_
  refine isOpen_singleton_of_finite_mem_nhds 0 (s := Metric.closedBall 0 1) ?_ ?_
  · exact Metric.closedBall_mem_nhds _ (by simp)
  · refine Set.Finite.of_finite_image ?_ (Set.injOn_of_injective Subtype.val_injective)
    convert!

中文:
实例 instDiscrete_unitLattice
  签名: : 离散拓扑 (unitLattice K)
  定义体: by
  classical
  refine discreteTopology_of_isOpen_singleton_zero ?_
  refine isOpen_singleton_of_finite_mem_nhds 0 (s := Metric.closedBall 0 1) ?_ ?_
  · exact Metric.closedBall_mem_nhds _ (by simp)
  · refine Set.Finite.of_finite_image ?_ (Set.injOn_of_injective Subtype.val_injective)
    convert!

Depends on / 依赖: Finite, Metric, Metric.closedBall, Metric.closedBall_mem_nhds, Set.Finite.of_finite_image, Set.injOn_of_injective, Subtype, Subtype.mem, Subtype.val_injective, classical, closedBall, closedBall_mem_nhds, convert, discreteTopology_of_isOpen_singleton_zero, injOn_of_injective, isOpen_singleton_of_finite_mem_nhds, of_finite_image, unitLattice_inter_ball_finite, val_injective
-/
instance instDiscrete_unitLattice : DiscreteTopology (unitLattice K) := by
  classical
  refine discreteTopology_of_isOpen_singleton_zero ?_
  refine isOpen_singleton_of_finite_mem_nhds 0 (s := Metric.closedBall 0 1) ?_ ?_
  · exact Metric.closedBall_mem_nhds _ (by simp)
  · refine Set.Finite.of_finite_image ?_ (Set.injOn_of_injective Subtype.val_injective)
    convert! unitLattice_inter_ball_finite K 1
    ext x
    refine ⟨?_, fun ⟨hx1, hx2⟩ => ⟨⟨x, hx1⟩, hx2, rfl⟩⟩
    rintro ⟨x, hx, rfl⟩
    exact ⟨Subtype.mem x, hx⟩

open scoped Classical in
/--
Instance `instZLattice_unitLattice` / 实例 `instZLattice_unitLattice`

English:
instance instZLattice_unitLattice
  signature: : IsZLattice Real (unitLattice K) where
  body: unitLattice_span_eq_top K

中文:
实例 instZLattice_unitLattice
  签名: : 是Z格 实数 (unitLattice K) where
  定义体: unitLattice_span_eq_top K

Depends on / 依赖: unitLattice_span_eq_top
-/
instance instZLattice_unitLattice : IsZLattice Real (unitLattice K) where
  span_top := unitLattice_span_eq_top K

set_option backward.isDefEq.respectTransparency false in
/--
theorem `finrank_eq_rank` / 定理 `finrank_eq_rank`

English:
theorem finrank_eq_rank
  proof: by
  classical
  simp only [finrank_fintype_fun_eq_card, Fintype.card_subtype_compl,
    Fintype.card_ofSubsingleton, rank]

@[simp]

中文:
定理 finrank_eq_rank
  证明: by
  classical
  simp only [finrank_fintype_fun_eq_card, Fintype.card_subtype_compl,
    Fintype.card_ofSubsingleton, rank]

@[simp]
-/
protected theorem finrank_eq_rank :
    finrank Real (logSpace K) = Units.rank K := by
  classical
  simp only [finrank_fintype_fun_eq_card, Fintype.card_subtype_compl,
    Fintype.card_ofSubsingleton, rank]

@[simp]
/--
theorem `unitLattice_rank` / 定理 `unitLattice_rank`

English:
theorem unitLattice_rank
  proof: by
  classical
  rw [← Units.finrank_eq_rank]; rw [ZLattice.rank Real]

中文:
定理 unitLattice_rank
  证明: by
  classical
  rw [← Units.finrank_eq_rank]; rw [ZLattice.rank Real]

Depends on / 依赖: Units.finrank_eq_rank, ZLattice, ZLattice.rank, classical, finrank_eq_rank
-/
theorem unitLattice_rank :
    finrank Int (unitLattice K) = Units.rank K := by
  classical
  rw [← Units.finrank_eq_rank]; rw [ZLattice.rank Real]

/--
Definition of `logEmbeddingQuot` / `logEmbeddingQuot` 的定义

English:
definition logEmbeddingQuot
  signature: :
  body: MonoidHom.toAdditiveLeft
    (QuotientGroup.kerLift (AddMonoidHom.toMultiplicativeRight (logEmbedding K))).comp
      (QuotientGroup.quotientMulEquivOfEq (by
        ext
        rw [MonoidHom.mem_ker]; rw [AddMonoidHom.toMultiplicativeRight_apply_apply]; rw [ofAdd_eq_one]; rw [← logEmbedding_eq_zero

中文:
定义 logEmbeddingQuot
  签名: :
  定义体: MonoidHom.toAdditiveLeft
    (QuotientGroup.kerLift (AddMonoidHom.toMultiplicativeRight (logEmbedding K))).comp
      (QuotientGroup.quotientMulEquivOfEq (by
        ext
        rw [MonoidHom.mem_ker]; rw [AddMonoidHom.toMultiplicativeRight_apply_apply]; rw [ofAdd_eq_one]; rw [← logEmbedding_eq_zero

Depends on / 依赖: AddMonoidHom, AddMonoidHom.toMultiplicativeRight, AddMonoidHom.toMultiplicativeRight_apply_apply, MonoidHom, MonoidHom.mem_ker, MonoidHom.toAdditiveLeft, QuotientGroup, QuotientGroup.kerLift, QuotientGroup.quotientMulEquivOfEq, kerLift, logEmbedding, logEmbedding_eq_zero_iff, mem_ker, ofAdd_eq_one, quotientMulEquivOfEq, toAdditiveLeft, toMonoidHom, toMultiplicativeRight, toMultiplicativeRight_apply_apply
-/
def logEmbeddingQuot :
    Additive ((𝓞 K)ˣ ⧸ (torsion K)) ->+ logSpace K :=
MonoidHom.toAdditiveLeft
    (QuotientGroup.kerLift (AddMonoidHom.toMultiplicativeRight (logEmbedding K))).comp
      (QuotientGroup.quotientMulEquivOfEq (by
        ext
        rw [MonoidHom.mem_ker]; rw [AddMonoidHom.toMultiplicativeRight_apply_apply]; rw [ofAdd_eq_one]; rw [← logEmbedding_eq_zero_iff])).toMonoidHom

@[simp]
/--
theorem `logEmbeddingQuot_apply` / 定理 `logEmbeddingQuot_apply`

English:
theorem logEmbeddingQuot_apply
  given: (x : (𝓞 K)ˣ)
  proof: rfl

中文:
定理 logEmbeddingQuot_apply
  条件: (x : (𝓞 K)ˣ)
  证明: rfl
-/
theorem logEmbeddingQuot_apply (x : (𝓞 K)ˣ) :
    logEmbeddingQuot K (Additive.ofMul (QuotientGroup.mk x)) =
      logEmbedding K (Additive.ofMul x) := rfl

/--
theorem `logEmbeddingQuot_injective` / 定理 `logEmbeddingQuot_injective`

English:
theorem logEmbeddingQuot_injective
  proof: by
  unfold logEmbeddingQuot
  intro _ _ h
  simp_rw [MonoidHom.toAdditiveLeft_apply_apply, MonoidHom.coe_comp, MulEquiv.coe_toMonoidHom,
    Function.comp_apply, EmbeddingLike.apply_eq_iff_eq] at h
exact (EmbeddingLike.apply_eq_iff_eq _).mp (QuotientGroup.kerLift_injective _).eq_iff.mp h

中文:
定理 logEmbeddingQuot_injective
  证明: by
  unfold logEmbeddingQuot
  intro _ _ h
  simp_rw [MonoidHom.toAdditiveLeft_apply_apply, MonoidHom.coe_comp, MulEquiv.coe_toMonoidHom,
    Function.comp_apply, EmbeddingLike.apply_eq_iff_eq] at h
exact (EmbeddingLike.apply_eq_iff_eq _).mp (QuotientGroup.kerLift_injective _).eq_iff.mp h

Depends on / 依赖: EmbeddingLike, EmbeddingLike.apply_eq_iff_eq, Function, Function.comp_apply, MonoidHom, MonoidHom.coe_comp, MonoidHom.toAdditiveLeft_apply_apply, MulEquiv, MulEquiv.coe_toMonoidHom, QuotientGroup, QuotientGroup.kerLift_injective, apply_eq_iff_eq, coe_comp, coe_toMonoidHom, comp_apply, eq_iff, eq_iff.mp, kerLift_injective, logEmbeddingQuot, simp_rw
-/
theorem logEmbeddingQuot_injective :
    Function.Injective (logEmbeddingQuot K) := by
  unfold logEmbeddingQuot
  intro _ _ h
  simp_rw [MonoidHom.toAdditiveLeft_apply_apply, MonoidHom.coe_comp, MulEquiv.coe_toMonoidHom,
    Function.comp_apply, EmbeddingLike.apply_eq_iff_eq] at h
exact (EmbeddingLike.apply_eq_iff_eq _).mp (QuotientGroup.kerLift_injective _).eq_iff.mp h

set_option backward.isDefEq.respectTransparency.types false in
/--
Definition of `logEmbeddingEquiv` / `logEmbeddingEquiv` 的定义

English:
definition logEmbeddingEquiv
  signature: :
  body: LinearEquiv.ofBijective ((logEmbeddingQuot K).codRestrict (unitLattice K)
    (Quotient.ind fun _ => logEmbeddingQuot_apply K _ ▸
      Submodule.mem_map_of_mem trivial)).toIntLinearMap
    ⟨fun _ _ => by
      rw [AddMonoidHom.coe_toIntLinearMap]; rw [AddMonoidHom.codRestrict_apply]; rw [AddMonoidH

中文:
定义 logEmbeddingEquiv
  签名: :
  定义体: LinearEquiv.ofBijective ((logEmbeddingQuot K).codRestrict (unitLattice K)
    (Quotient.ind fun _ => logEmbeddingQuot_apply K _ ▸
      Submodule.mem_map_of_mem trivial)).toIntLinearMap
    ⟨fun _ _ => by
      rw [AddMonoidHom.coe_toIntLinearMap]; rw [AddMonoidHom.codRestrict_apply]; rw [AddMonoidH

Depends on / 依赖: AddMonoidHom, AddMonoidHom.codRestrict_apply, AddMonoidHom.coe_toIntLinearMap, LinearEquiv, LinearEquiv.ofBijective, Quotient, Quotient.ind, Submodule, Submodule.mem_map_of_mem, Subtype, Subtype.mk.injEq, codRestrict, codRestrict_apply, coe_toIntLinearMap, logEmbeddingQuot, logEmbeddingQuot_apply, logEmbeddingQuot_injective, mem_map_of_mem, ofBijective, toIntLinearMap
-/
def logEmbeddingEquiv :
    Additive ((𝓞 K)ˣ ⧸ (torsion K)) ≃ₗ[Int] (unitLattice K) :=
  LinearEquiv.ofBijective ((logEmbeddingQuot K).codRestrict (unitLattice K)
    (Quotient.ind fun _ => logEmbeddingQuot_apply K _ ▸
      Submodule.mem_map_of_mem trivial)).toIntLinearMap
    ⟨fun _ _ => by
      rw [AddMonoidHom.coe_toIntLinearMap]; rw [AddMonoidHom.codRestrict_apply]; rw [AddMonoidHom.codRestrict_apply]; rw [Subtype.mk.injEq]
      apply logEmbeddingQuot_injective K, fun ⟨a, ⟨b, _, ha⟩⟩ => ⟨⟦b⟧, by simpa using! ha⟩⟩

@[simp]
/--
theorem `logEmbeddingEquiv_apply` / 定理 `logEmbeddingEquiv_apply`

English:
theorem logEmbeddingEquiv_apply
  given: (x : (𝓞 K)ˣ)
  proof: rfl

中文:
定理 logEmbeddingEquiv_apply
  条件: (x : (𝓞 K)ˣ)
  证明: rfl
-/
theorem logEmbeddingEquiv_apply (x : (𝓞 K)ˣ) :
    logEmbeddingEquiv K (Additive.ofMul (QuotientGroup.mk x)) =
      logEmbedding K (Additive.ofMul x) := rfl

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Module.Free Int (Additive ((𝓞 K)ˣ ⧸ (torsion K)))
  body: by
  classical exact Module.Free.of_equiv (logEmbeddingEquiv K).symm

中文:
实例 :
  签名: 模.自由 整数 (加性 ((𝓞 K)ˣ ⧸ (torsion K)))
  定义体: by
  classical exact Module.Free.of_equiv (logEmbeddingEquiv K).symm

Depends on / 依赖: Module, Module.Free.of_equiv, classical, logEmbeddingEquiv, of_equiv
-/
instance : Module.Free Int (Additive ((𝓞 K)ˣ ⧸ (torsion K))) := by
  classical exact Module.Free.of_equiv (logEmbeddingEquiv K).symm

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Module.Finite Int (Additive ((𝓞 K)ˣ ⧸ (torsion K)))
  body: by
  classical exact Module.Finite.equiv (logEmbeddingEquiv K).symm

中文:
实例 :
  签名: 模.有限 整数 (加性 ((𝓞 K)ˣ ⧸ (torsion K)))
  定义体: by
  classical exact Module.Finite.equiv (logEmbeddingEquiv K).symm

Depends on / 依赖: Finite, Module, Module.Finite.equiv, classical, logEmbeddingEquiv
-/
instance : Module.Finite Int (Additive ((𝓞 K)ˣ ⧸ (torsion K))) := by
  classical exact Module.Finite.equiv (logEmbeddingEquiv K).symm

-- Note that we prove this instance first and then deduce from it the instance
-- `Monoid.FG (𝓞 K)ˣ`, and not the other way around, due to no `Subgroup` version
-- of `Submodule.fg_of_fg_map_of_fg_inf_ker` existing.
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Module.Finite Int (Additive (𝓞 K)ˣ)
  body: by
  rw [Module.finite_def]
  refine Submodule.fg_of_fg_map_of_fg_inf_ker
    (MonoidHom.toAdditive (QuotientGroup.mk' (torsion K))).toIntLinearMap ?_ ?_
  · rw [Submodule.map_top, LinearMap.range_eq_top.mpr
      (by exact QuotientGroup.mk'_surjective (torsion K)), ← Module.finite_def]
    infer_in

中文:
实例 :
  签名: 模.有限 整数 (加性 (𝓞 K)ˣ)
  定义体: by
  rw [Module.finite_def]
  refine Submodule.fg_of_fg_map_of_fg_inf_ker
    (MonoidHom.toAdditive (QuotientGroup.mk' (torsion K))).toIntLinearMap ?_ ?_
  · rw [Submodule.map_top, LinearMap.range_eq_top.mpr
      (by exact QuotientGroup.mk'_surjective (torsion K)), ← Module.finite_def]
    infer_in

Depends on / 依赖: AddGroup, AddGroup.fg_iff_, AddMonoidHom, AddMonoidHom.coe_toIntLinearMap_ker, AddSubgroup, AddSubgroup.toIntSubmodule_toAddSubgroup, LinearMap, LinearMap.range_eq_top.mpr, Module, Module.finite_def, MonoidHom, MonoidHom.coe_toAdditive_ker, MonoidHom.toAdditive, QuotientGroup, QuotientGroup.ker_mk, QuotientGroup.mk, Submodule, Submodule.fg_iff_addSubgroup_fg, Submodule.fg_of_fg_map_of_fg_inf_ker, Submodule.map_top
-/
instance : Module.Finite Int (Additive (𝓞 K)ˣ) := by
  rw [Module.finite_def]
  refine Submodule.fg_of_fg_map_of_fg_inf_ker
    (MonoidHom.toAdditive (QuotientGroup.mk' (torsion K))).toIntLinearMap ?_ ?_
  · rw [Submodule.map_top, LinearMap.range_eq_top.mpr
      (by exact QuotientGroup.mk'_surjective (torsion K)), ← Module.finite_def]
    infer_instance
  · rw [inf_of_le_right le_top, AddMonoidHom.coe_toIntLinearMap_ker, MonoidHom.coe_toAdditive_ker,
      QuotientGroup.ker_mk', Submodule.fg_iff_addSubgroup_fg,
      AddSubgroup.toIntSubmodule_toAddSubgroup, ← AddGroup.fg_iff_addSubgroup_fg]
    have : Finite (Subgroup.toAddSubgroup (torsion K)) := (inferInstance : Finite (torsion K))
    exact AddGroup.fg_of_finite

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Monoid.FG (𝓞 K)ˣ
  body: by
  rw [Monoid.fg_iff_add_fg]; rw [← AddGroup.fg_iff_addMonoid_fg]; rw [← Module.Finite.iff_addGroup_fg]
  infer_instance

中文:
实例 :
  签名: 幺半群.FG (𝓞 K)ˣ
  定义体: by
  rw [Monoid.fg_iff_add_fg]; rw [← AddGroup.fg_iff_addMonoid_fg]; rw [← Module.Finite.iff_addGroup_fg]
  infer_instance

Depends on / 依赖: AddGroup, AddGroup.fg_iff_addMonoid_fg, Finite, Module, Module.Finite.iff_addGroup_fg, Monoid, Monoid.fg_iff_add_fg, fg_iff_addMonoid_fg, fg_iff_add_fg, iff_addGroup_fg, infer_instance
-/
instance : Monoid.FG (𝓞 K)ˣ := by
  rw [Monoid.fg_iff_add_fg]; rw [← AddGroup.fg_iff_addMonoid_fg]; rw [← Module.Finite.iff_addGroup_fg]
  infer_instance

/--
theorem `finrank_modTorsion` / 定理 `finrank_modTorsion`

English:
theorem finrank_modTorsion
  statement: finrank Int (Additive ((𝓞 K)ˣ ⧸ (torsion K))) = rank K
  proof: by
  rw [← LinearEquiv.finrank_eq (logEmbeddingEquiv K).symm]; rw [unitLattice_rank]

@[deprecated (since := "2026-06-05")] alias rank_modTorsion := finrank_modTorsion

中文:
定理 finrank_modTorsion
  结论: finrank 整数 (加性 ((𝓞 K)ˣ ⧸ (torsion K))) = rank K
  证明: by
  rw [← LinearEquiv.finrank_eq (logEmbeddingEquiv K).symm]; rw [unitLattice_rank]

@[deprecated (since := "2026-06-05")] alias rank_modTorsion := finrank_modTorsion

Depends on / 依赖: LinearEquiv, LinearEquiv.finrank_eq, finrank_eq, logEmbeddingEquiv, unitLattice_rank
-/
theorem finrank_modTorsion : finrank Int (Additive ((𝓞 K)ˣ ⧸ (torsion K))) = rank K := by
  rw [← LinearEquiv.finrank_eq (logEmbeddingEquiv K).symm]; rw [unitLattice_rank]

@[deprecated (since := "2026-06-05")] alias rank_modTorsion := finrank_modTorsion

/--
theorem `finrank_eq` / 定理 `finrank_eq`

English:
theorem finrank_eq
  statement: finrank Int (Additive (𝓞 K)ˣ) = rank K
  proof: by
  simpa [← finrank_modTorsion] using! finrank_quotient_torsion_eq.symm

中文:
定理 finrank_eq
  结论: finrank 整数 (加性 (𝓞 K)ˣ) = rank K
  证明: by
  simpa [← finrank_modTorsion] using! finrank_quotient_torsion_eq.symm

Depends on / 依赖: finrank_modTorsion, finrank_quotient_torsion_eq, finrank_quotient_torsion_eq.symm
-/
theorem finrank_eq : finrank Int (Additive (𝓞 K)ˣ) = rank K := by
  simpa [← finrank_modTorsion] using! finrank_quotient_torsion_eq.symm

/--
Definition of `basisModTorsion` / `basisModTorsion` 的定义

English:
definition basisModTorsion
  signature: : Basis (Fin (rank K)) Int (Additive ((𝓞 K)ˣ ⧸ (torsion K)))
  body: Basis.reindex (Module.Free.chooseBasis Int _) (Fintype.equivOfCardEq <| by
    rw [← Module.finrank_eq_card_chooseBasisIndex]; rw [finrank_modTorsion]; rw [Fintype.card_fin])

中文:
定义 basisModTorsion
  签名: : 基 (有限集 (rank K)) 整数 (加性 ((𝓞 K)ˣ ⧸ (torsion K)))
  定义体: Basis.reindex (Module.Free.chooseBasis Int _) (Fintype.equivOfCardEq <| by
    rw [← Module.finrank_eq_card_chooseBasisIndex]; rw [finrank_modTorsion]; rw [Fintype.card_fin])

Depends on / 依赖: Basis.reindex, Fintype, Fintype.card_fin, Fintype.equivOfCardEq, Module, Module.Free.chooseBasis, Module.finrank_eq_card_chooseBasisIndex, card_fin, chooseBasis, equivOfCardEq, finrank_eq_card_chooseBasisIndex, finrank_modTorsion, reindex
-/
def basisModTorsion : Basis (Fin (rank K)) Int (Additive ((𝓞 K)ˣ ⧸ (torsion K))) :=
  Basis.reindex (Module.Free.chooseBasis Int _) (Fintype.equivOfCardEq <| by
    rw [← Module.finrank_eq_card_chooseBasisIndex]; rw [finrank_modTorsion]; rw [Fintype.card_fin])

/--
Definition of `basisUnitLattice` / `basisUnitLattice` 的定义

English:
definition basisUnitLattice
  signature: : Basis (Fin (rank K)) Int (unitLattice K)
  body: (basisModTorsion K).map (logEmbeddingEquiv K)

中文:
定义 basisUnitLattice
  签名: : 基 (有限集 (rank K)) 整数 (unitLattice K)
  定义体: (basisModTorsion K).map (logEmbeddingEquiv K)

Depends on / 依赖: basisModTorsion, logEmbeddingEquiv
-/
def basisUnitLattice : Basis (Fin (rank K)) Int (unitLattice K) :=
  (basisModTorsion K).map (logEmbeddingEquiv K)

/--
Definition of `fundSystem` / `fundSystem` 的定义

English:
definition fundSystem
  signature: : Fin (rank K) -> (𝓞 K)ˣ
  body: -- `:)` prevents the `⧸` decaying to a quotient by `leftRel` when we unfold this later
  fun i => Quotient.out ((basisModTorsion K i).toMul :)

中文:
定义 fundSystem
  签名: : 有限集 (rank K) -> (𝓞 K)ˣ
  定义体: -- `:)` prevents the `⧸` decaying to a quotient by `leftRel` when we unfold this later
  fun i => Quotient.out ((basisModTorsion K i).toMul :)
-/
def fundSystem : Fin (rank K) -> (𝓞 K)ˣ :=
  -- `:)` prevents the `⧸` decaying to a quotient by `leftRel` when we unfold this later
  fun i => Quotient.out ((basisModTorsion K i).toMul :)

/--
theorem `fundSystem_mk` / 定理 `fundSystem_mk`

English:
theorem fundSystem_mk
  given: (i : Fin (rank K))
  proof: by
  simp_rw [fundSystem, ← Equiv.eq_symm_apply, Additive.ofMul_symm_eq, Quotient.out_eq']

中文:
定理 fundSystem_mk
  条件: (i : 有限集 (rank K))
  证明: by
  simp_rw [fundSystem, ← Equiv.eq_symm_apply, Additive.ofMul_symm_eq, Quotient.out_eq']

Depends on / 依赖: Additive, Additive.ofMul_symm_eq, Equiv.eq_symm_apply, Quotient, Quotient.out_eq, eq_symm_apply, fundSystem, ofMul_symm_eq, out_eq, simp_rw
-/
theorem fundSystem_mk (i : Fin (rank K)) :
    Additive.ofMul (QuotientGroup.mk (fundSystem K i)) = (basisModTorsion K i) := by
  simp_rw [fundSystem, ← Equiv.eq_symm_apply, Additive.ofMul_symm_eq, Quotient.out_eq']

/--
theorem `logEmbedding_fundSystem` / 定理 `logEmbedding_fundSystem`

English:
theorem logEmbedding_fundSystem
  given: (i : Fin (rank K))
  proof: by
  rw [basisUnitLattice]; rw [Basis.map_apply]; rw [← fundSystem_mk]; rw [logEmbeddingEquiv_apply]

中文:
定理 logEmbedding_fundSystem
  条件: (i : 有限集 (rank K))
  证明: by
  rw [basisUnitLattice]; rw [Basis.map_apply]; rw [← fundSystem_mk]; rw [logEmbeddingEquiv_apply]

Depends on / 依赖: Basis.map_apply, basisUnitLattice, fundSystem_mk, logEmbeddingEquiv_apply, map_apply
-/
theorem logEmbedding_fundSystem (i : Fin (rank K)) :
    logEmbedding K (Additive.ofMul (fundSystem K i)) = basisUnitLattice K i := by
  rw [basisUnitLattice]; rw [Basis.map_apply]; rw [← fundSystem_mk]; rw [logEmbeddingEquiv_apply]

/--
theorem `fun_eq_repr` / 定理 `fun_eq_repr`

English:
theorem fun_eq_repr
  statement: {x ζ : (𝓞 K)ˣ} {f : Fin (rank K) -> Int} (hζ : ζ in torsion K)
  proof: by
  suffices Additive.ofMul ↑x = ∑ i, (f i) • (basisModTorsion K i) by
    rw [← (basisModTorsion K).repr_sum_self f]; rw [← this]
  calc
    Additive.ofMul ↑x
    _ = ∑ i, (f i) • Additive.ofMul ↑(fundSystem K i) := by
          rw [h]; rw [QuotientGroup.mk_mul]; rw [(QuotientGroup.eq_one_iff _).m

中文:
定理 fun_eq_repr
  结论: {x ζ : (𝓞 K)ˣ} {f : 有限集 (rank K) -> 整数} (hζ : ζ in torsion K)
  证明: by
  suffices Additive.ofMul ↑x = ∑ i, (f i) • (basisModTorsion K i) by
    rw [← (basisModTorsion K).repr_sum_self f]; rw [← this]
  calc
    Additive.ofMul ↑x
    _ = ∑ i, (f i) • Additive.ofMul ↑(fundSystem K i) := by
          rw [h]; rw [QuotientGroup.mk_mul]; rw [(QuotientGroup.eq_one_iff _).m

Depends on / 依赖: Additive, Additive.ofMul, QuotientGroup, QuotientGroup.eq_one_iff, QuotientGroup.mk_mul, QuotientGroup.mk_prod, QuotientGroup.out_eq, basisModTorsion, eq_one_iff, fundSystem, mk_mul, mk_prod, ofMul_prod, ofMul_toMul, one_mul, out_eq, repr_sum_self, simp_rw
-/
theorem fun_eq_repr {x ζ : (𝓞 K)ˣ} {f : Fin (rank K) -> Int} (hζ : ζ in torsion K)
    (h : x = ζ * ∏ i, (fundSystem K i) ^ (f i)) :
    f = (basisModTorsion K).repr (Additive.ofMul ↑x) := by
  suffices Additive.ofMul ↑x = ∑ i, (f i) • (basisModTorsion K i) by
    rw [← (basisModTorsion K).repr_sum_self f]; rw [← this]
  calc
    Additive.ofMul ↑x
    _ = ∑ i, (f i) • Additive.ofMul ↑(fundSystem K i) := by
          rw [h]; rw [QuotientGroup.mk_mul]; rw [(QuotientGroup.eq_one_iff _).mpr hζ]; rw [one_mul]; rw [QuotientGroup.mk_prod]; rw [ofMul_prod]; rfl
    _ = ∑ i, (f i) • (basisModTorsion K i) := by
          simp_rw [fundSystem, QuotientGroup.out_eq', ofMul_toMul]

/--
theorem `exist_unique_eq_mul_prod` / 定理 `exist_unique_eq_mul_prod`

English:
theorem exist_unique_eq_mul_prod
  given: (x : (𝓞 K)ˣ)
  statement: exists! ζe : torsion K × (Fin (rank K) -> Int),
  proof: by
  let ζ := x * (∏ i, (fundSystem K i) ^ ((basisModTorsion K).repr (Additive.ofMul ↑x) i))⁻¹
  have h_tors : ζ in torsion K := by
    rw [← QuotientGroup.eq_one_iff]; rw [QuotientGroup.mk_mul]; rw [QuotientGroup.mk_inv]; rw [← ofMul_eq_zero]; rw [ofMul_mul]; rw [ofMul_inv]; rw [QuotientGroup.mk_pr

中文:
定理 exist_unique_eq_mul_prod
  条件: (x : (𝓞 K)ˣ)
  结论: 存在! ζe : torsion K × (有限集 (rank K) -> 整数),
  证明: by
  let ζ := x * (∏ i, (fundSystem K i) ^ ((basisModTorsion K).repr (Additive.ofMul ↑x) i))⁻¹
  have h_tors : ζ in torsion K := by
    rw [← QuotientGroup.eq_one_iff]; rw [QuotientGroup.mk_mul]; rw [QuotientGroup.mk_inv]; rw [← ofMul_eq_zero]; rw [ofMul_mul]; rw [ofMul_inv]; rw [QuotientGroup.mk_pr

Depends on / 依赖: Additive, Additive.ofMul, QuotientGroup, QuotientGroup.eq_one_iff, QuotientGroup.mk_inv, QuotientGroup.mk_mul, QuotientGroup.mk_prod, QuotientGroup.mk_zpow, QuotientGroup.out_eq, add_eq_zero_iff_eq_neg, basisModTorsion, eq_one_iff, fundSystem, h_tors, mk_inv, mk_mul, mk_prod, mk_zpow, neg_neg, ofMul_eq_zero
-/
theorem exist_unique_eq_mul_prod (x : (𝓞 K)ˣ) : exists! ζe : torsion K × (Fin (rank K) -> Int),
    x = ζe.1 * ∏ i, (fundSystem K i) ^ (ζe.2 i) := by
  let ζ := x * (∏ i, (fundSystem K i) ^ ((basisModTorsion K).repr (Additive.ofMul ↑x) i))⁻¹
  have h_tors : ζ in torsion K := by
    rw [← QuotientGroup.eq_one_iff]; rw [QuotientGroup.mk_mul]; rw [QuotientGroup.mk_inv]; rw [← ofMul_eq_zero]; rw [ofMul_mul]; rw [ofMul_inv]; rw [QuotientGroup.mk_prod]; rw [ofMul_prod]
    simp_rw [QuotientGroup.mk_zpow, ofMul_zpow, fundSystem, QuotientGroup.out_eq']
    rw [add_eq_zero_iff_eq_neg]; rw [neg_neg]
    exact ((basisModTorsion K).sum_repr (Additive.ofMul ↑x)).symm
  refine ⟨⟨⟨ζ, h_tors⟩, ((basisModTorsion K).repr (Additive.ofMul ↑x) : Fin (rank K) -> Int)⟩, ?_, ?_⟩
  · simp only [ζ, _root_.inv_mul_cancel_right]
  · rintro ⟨⟨ζ', h_tors'⟩, η⟩ hf
    simp only [ζ, ← fun_eq_repr K h_tors' hf, Prod.mk.injEq, Subtype.mk.injEq, and_true]
    nth_rewrite 1 [hf]
    rw [_root_.mul_inv_cancel_right]

/--
theorem `closure_fundSystem_sup_torsion_eq_top` / 定理 `closure_fundSystem_sup_torsion_eq_top`

English:
theorem closure_fundSystem_sup_torsion_eq_top
  proof: by
  rw [Subgroup.eq_top_iff']; rw [sup_comm]
  intro x
  obtain ⟨c, rfl, _⟩ := exist_unique_eq_mul_prod K x
exact Subgroup.mul_mem_sup (SetLike.coe_mem c.1) Subgroup.prod_mem _
    fun i _ => Subgroup.zpow_mem _ (Subgroup.subset_closure (Set.mem_range_self i)) _

中文:
定理 closure_fundSystem_sup_torsion_eq_top
  证明: by
  rw [Subgroup.eq_top_iff']; rw [sup_comm]
  intro x
  obtain ⟨c, rfl, _⟩ := exist_unique_eq_mul_prod K x
exact Subgroup.mul_mem_sup (SetLike.coe_mem c.1) Subgroup.prod_mem _
    fun i _ => Subgroup.zpow_mem _ (Subgroup.subset_closure (Set.mem_range_self i)) _

Depends on / 依赖: Set.mem_range_self, SetLike, SetLike.coe_mem, Subgroup, Subgroup.eq_top_iff, Subgroup.mul_mem_sup, Subgroup.prod_mem, Subgroup.subset_closure, Subgroup.zpow_mem, coe_mem, eq_top_iff, exist_unique_eq_mul_prod, mem_range_self, mul_mem_sup, prod_mem, subset_closure, sup_comm, zpow_mem
-/
theorem closure_fundSystem_sup_torsion_eq_top :
    Subgroup.closure (Set.range (fundSystem K)) ⊔ torsion K = ⊤ := by
  rw [Subgroup.eq_top_iff']; rw [sup_comm]
  intro x
  obtain ⟨c, rfl, _⟩ := exist_unique_eq_mul_prod K x
exact Subgroup.mul_mem_sup (SetLike.coe_mem c.1) Subgroup.prod_mem _
    fun i _ => Subgroup.zpow_mem _ (Subgroup.subset_closure (Set.mem_range_self i)) _

end statements

end NumberField.Units
