/-
Copyright (c) 2025 Yakov Pechersky. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yakov Pechersky
-/
module

public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.NumberTheory.Padics.PadicIntegers
public import Mathlib.Topology.Algebra.Valued.ValuedField
public import Mathlib.Topology.Algebra.Valued.WithVal
public import Mathlib.Topology.GDelta.MetrizableSpace

/-!
# Equivalence between `ℚ_[p]` and `(Rat.padicValuation p).Completion`

The `p`-adic numbers are isomorphic as a field to the completion of the rationals at the
`p`-adic valuation. This is implemented via `Valuation.Completion` using `Rat.padicValuation`,
which is shorthand for `UniformSpace.Completion (WithVal (Rat.padicValuation p))`.

## Main definitions

* `Padic.withValRingEquiv`: the field isomorphism between
  `(Rat.padicValuation p).Completion` and `ℚ_[p]`
* `Padic.withValUniformEquiv`: the uniform space isomorphism between
  `(Rat.padicValuation p).Completion` and `ℚ_[p]`

-/

@[expose] public section

namespace Padic

variable {p : Nat} [Fact p.Prime]

open NNReal WithZero UniformSpace

set_option backward.isDefEq.respectTransparency.types false in
open MonoidWithZeroHom.ValueGroup₀ in
/--
lemma `isUniformInducing_cast_withVal` / 引理 `isUniformInducing_cast_withVal`

English:
lemma isUniformInducing_cast_withVal
  statement: IsUniformInducing ((Rat.castHom Rat_[p]).comp
  proof: by
  have hp0' : 0 < (p : Rat) := by simp [Nat.Prime.pos Fact.out]
  have hp0 : 0 < (p : Real)⁻¹ := by simp [Nat.Prime.pos Fact.out]
  have hp1' : 1 < (p : Rat) := by simp [Nat.Prime.one_lt Fact.out]
  have hp1 : (p : Real)⁻¹ < 1 := by simp [inv_lt_one_iff₀, Nat.Prime.one_lt Fact.out]
  rw [Filter.H

中文:
引理 isUniformInducing_cast_withVal
  结论: IsUniformInducing ((Rat.castHom Rat_[p]).comp
  证明: by
  have hp0' : 0 < (p : Rat) := by simp [Nat.Prime.pos Fact.out]
  have hp0 : 0 < (p : Real)⁻¹ := by simp [Nat.Prime.pos Fact.out]
  have hp1' : 1 < (p : Rat) := by simp [Nat.Prime.one_lt Fact.out]
  have hp1 : (p : Real)⁻¹ < 1 := by simp [inv_lt_one_iff₀, Nat.Prime.one_lt Fact.out]
  rw [Filter.H

Depends on / 依赖: Fact.out, Filter, Filter.HasBasis.isUniformInducing_iff, HasBasis, Metric, Metric.uniformity_basis_dist_le_pow, Nat.Prime.one_lt, Nat.Prime.pos, RingEquiv, RingEquiv.toRingHom_eq_coe, RingHom, RingHom.coe_com, Set.mem_ofPred_eq, Valued, Valued.hasBasis_uniformity, coe_com, dist_eq_norm_sub, hasBasis_uniformity, inv_pow, isUniformInducing_iff
-/
lemma isUniformInducing_cast_withVal : IsUniformInducing ((Rat.castHom Rat_[p]).comp
    (WithVal.equiv (Rat.padicValuation p)).toRingHom) := by
  have hp0' : 0 < (p : Rat) := by simp [Nat.Prime.pos Fact.out]
  have hp0 : 0 < (p : Real)⁻¹ := by simp [Nat.Prime.pos Fact.out]
  have hp1' : 1 < (p : Rat) := by simp [Nat.Prime.one_lt Fact.out]
  have hp1 : (p : Real)⁻¹ < 1 := by simp [inv_lt_one_iff₀, Nat.Prime.one_lt Fact.out]
  rw [Filter.HasBasis.isUniformInducing_iff (Valued.hasBasis_uniformity _ _)
    (Metric.uniformity_basis_dist_le_pow hp0 hp1)]
  simp only [Set.mem_ofPred_eq, dist_eq_norm_sub, inv_pow, RingEquiv.toRingHom_eq_coe,
    RingHom.coe_comp, Rat.coe_castHom, RingHom.coe_coe, Function.comp_apply, ← Rat.cast_sub,
    ← map_sub, Padic.eq_padicNorm, true_and, forall_const]
  constructor
  · intro n
    have hn : Valued.v (R := (WithVal (Rat.padicValuation p))) (p ^ n) =
      exp (-n : Int) := by
      simp only [← WithVal.val_apply_equiv, map_pow, map_natCast, Rat.padicValuation_self,
        Int.reduceNeg, exp_neg, inv_pow, ← exp_nsmul, nsmul_eq_mul, mul_one]
    use Units.mk0 (Valued.v.restrict (p ^ n)) (by
      simp [Valuation.restrict_def, Nat.Prime.ne_zero Fact.out])
    intro x y h
    set x' := (WithVal.equiv (Rat.padicValuation p)) x with hx
    set y' := (WithVal.equiv (Rat.padicValuation p)) y with hy
    rw [Valuation.map_sub_swap]; rw [Units.val_mk0]; rw [Valuation.restrict_lt_iff]; rw [hn] at h
    change Rat.padicValuation p (x' - y') < exp _ at h
    rw [← Nat.cast_pow]; rw [← Rat.cast_natCast]; rw [← Rat.cast_inv_of_ne_zero]; rw [Rat.cast_le]
    · rw [map_sub, ← hx, ← hy]
      simp only [Rat.padicValuation, Valuation.coe_mk, MonoidWithZeroHom.coe_mk, ZeroHom.coe_mk,
        padicNorm, zpow_neg, Nat.cast_pow] at h ⊢
      split_ifs with H
      · simp
      · simp only [H, ↓reduceIte, exp_lt_exp, neg_lt_neg_iff] at h
        simpa [hp0', zpow_pos, pow_pos, inv_le_inv₀] using
          zpow_right_mono₀ (by exact_mod_cast (Nat.Prime.one_le Fact.out)) h.le
    · simp [Nat.Prime.ne_zero Fact.out]
  · intro γ
    use (log ((embedding γ.val) * exp (-1))).natAbs
    intro x y h
    set x' := (WithVal.equiv (Rat.padicValuation p)) x with hx
    set y' := (WithVal.equiv (Rat.padicValuation p)) y with hy
    rw [Valuation.map_sub_swap]; rw [Valuation.restrict_lt_iff_lt_embedding]
    change Rat.padicValuation p (x' - y') < embedding γ.1
    rw [← Nat.cast_pow]; rw [← Rat.cast_natCast]; rw [← Rat.cast_inv_of_ne_zero]; rw [Rat.cast_le] at h
    · change padicNorm p (x' - y') <= _ at h
      simp only [Rat.padicValuation, Valuation.coe_mk, MonoidWithZeroHom.coe_mk, ZeroHom.coe_mk,
        padicNorm, zpow_neg, Nat.cast_pow] at h ⊢
      split_ifs with H
      · simp only [exp_neg]
        exact embedding_unit_pos _
      · rw [← lt_log_iff_exp_lt (embedding_unit_ne_zero _)]
        simp_all [← zpow_natCast, zpow_pos, inv_le_inv₀, zpow_le_zpow_iff_right₀ hp1', abs_le,
          Int.lt_iff_add_one_le]
    · simp [Nat.Prime.ne_zero Fact.out]

/--
lemma `isDenseInducing_cast_withVal` / 引理 `isDenseInducing_cast_withVal`

English:
lemma isDenseInducing_cast_withVal
  statement: IsDenseInducing ((Rat.castHom Rat_[p]).comp
  proof: by
  refine Padic.isUniformInducing_cast_withVal.isDenseInducing ?_
  intro
  -- nhds_discrete causes timeouts on TC search
  simpa [-nhds_discrete] using Padic.denseRange_ratCast p _

中文:
引理 isDenseInducing_cast_withVal
  结论: IsDenseInducing ((Rat.castHom Rat_[p]).comp
  证明: by
  refine Padic.isUniformInducing_cast_withVal.isDenseInducing ?_
  intro
  -- nhds_discrete causes timeouts on TC search
  simpa [-nhds_discrete] using Padic.denseRange_ratCast p _

Depends on / 依赖: Padic.isUniformInducing_cast_withVal.isDenseInducing, isDenseInducing, isUniformInducing_cast_withVal
-/
lemma isDenseInducing_cast_withVal : IsDenseInducing ((Rat.castHom Rat_[p]).comp
    (WithVal.equiv (Rat.padicValuation p)).toRingHom) := by
  refine Padic.isUniformInducing_cast_withVal.isDenseInducing ?_
  intro
  -- nhds_discrete causes timeouts on TC search
  simpa [-nhds_discrete] using Padic.denseRange_ratCast p _

open Completion in
open scoped Valued in
/-- The `p`-adic numbers are isomorphic as a field to the completion of the rationals at
the `p`-adic valuation. -/
noncomputable
/--
Definition of `withValRingEquiv` / `withValRingEquiv` 的定义

English:
definition withValRingEquiv
  signature: :
  body: (extensionHom ((Rat.castHom Rat_[p]).comp (WithVal.equiv (Rat.padicValuation p)).toRingHom)
    Padic.isUniformInducing_cast_withVal.uniformContinuous.continuous)
  invFun := Padic.isDenseInducing_cast_withVal.extend coe'
  left_inv y := by
    induction y using induction_on
    · generalize_proofs 

中文:
定义 withValRingEquiv
  签名: :
  定义体: (extensionHom ((Rat.castHom Rat_[p]).comp (WithVal.equiv (Rat.padicValuation p)).toRingHom)
    Padic.isUniformInducing_cast_withVal.uniformContinuous.continuous)
  invFun := Padic.isDenseInducing_cast_withVal.extend coe'
  left_inv y := by
    induction y using induction_on
    · generalize_proofs 

Depends on / 依赖: Rat.castHom, Rat.padicValuation, Rat_, WithVal, WithVal.equiv, castHom, extensionHom, padicValuation, toRingHom
-/
def withValRingEquiv :
    (Rat.padicValuation p).Completion ≃+* Rat_[p] where
  toFun := (extensionHom ((Rat.castHom Rat_[p]).comp (WithVal.equiv (Rat.padicValuation p)).toRingHom)
    Padic.isUniformInducing_cast_withVal.uniformContinuous.continuous)
  invFun := Padic.isDenseInducing_cast_withVal.extend coe'
  left_inv y := by
    induction y using induction_on
    · generalize_proofs _ _ _ H
      refine isClosed_eq ?_ continuous_id
      exact (uniformContinuous_uniformly_extend Padic.isUniformInducing_cast_withVal
        Padic.isDenseInducing_cast_withVal.dense (uniformContinuous_coe _)).continuous.comp
        (continuous_extension)
    · rw [extensionHom_coe]
      apply IsDenseInducing.extend_eq
      exact continuous_coe _
  right_inv y := by
    induction y using isClosed_property (Padic.denseRange_ratCast p)
    · refine isClosed_eq ?_ continuous_id
      refine continuous_extension.comp ?_
      exact (uniformContinuous_uniformly_extend Padic.isUniformInducing_cast_withVal
        Padic.isDenseInducing_cast_withVal.dense (uniformContinuous_coe _)).continuous
    · have : forall q : Rat, Padic.isDenseInducing_cast_withVal.extend coe' q = coe'
        ((WithVal.equiv (Rat.padicValuation p)).symm q) := by
        intro q
        apply IsDenseInducing.extend_eq
        exact continuous_coe _
      rw [this]; rw [extensionHom_coe]
      simp
  map_mul' := map_mul _
  map_add' := map_add _


@[simp]
/--
lemma `coe_withValRingEquiv` / 引理 `coe_withValRingEquiv`

English:
lemma coe_withValRingEquiv
  proof: rfl

@[simp]

中文:
引理 coe_withValRingEquiv
  证明: rfl

@[simp]

Depends on / 依赖: Completion, Completion.extension, extension
-/
lemma coe_withValRingEquiv :
    ⇑(Padic.withValRingEquiv (p := p)) = Completion.extension
      ((↑) ∘ (WithVal.equiv (Rat.padicValuation p))) := rfl

@[simp]
/--
lemma `coe_withValRingEquiv_symm` / 引理 `coe_withValRingEquiv_symm`

English:
lemma coe_withValRingEquiv_symm
  proof: rfl

中文:
引理 coe_withValRingEquiv_symm
  证明: rfl
-/
lemma coe_withValRingEquiv_symm :
    ⇑(Padic.withValRingEquiv (p := p)).symm =
      Padic.isDenseInducing_cast_withVal.extend Completion.coe' := rfl

/-- The `p`-adic numbers are isomorphic as uniform spaces to the completion of the rationals at
the `p`-adic valuation. -/
noncomputable
/--
Definition of `withValUniformEquiv` / `withValUniformEquiv` 的定义

English:
definition withValUniformEquiv
  signature: :
  body: UniformEquiv.symm Padic.withValRingEquiv.symm.toUniformEquivOfIsUniformInducing
    isDenseInducing_cast_withVal.isUniformInducing_extend isUniformInducing_cast_withVal
      (Completion.isUniformInducing_coe _)

@[simp]

中文:
定义 withValUniformEquiv
  签名: :
  定义体: UniformEquiv.symm Padic.withValRingEquiv.symm.toUniformEquivOfIsUniformInducing
    isDenseInducing_cast_withVal.isUniformInducing_extend isUniformInducing_cast_withVal
      (Completion.isUniformInducing_coe _)

@[simp]

Depends on / 依赖: Completion, Completion.isUniformInducing_coe, Padic.withValRingEquiv.symm.toUniformEquivOfIsUniformInducing, UniformEquiv, UniformEquiv.symm, isDenseInducing_cast_withVal, isDenseInducing_cast_withVal.isUniformInducing_extend, isUniformInducing_cast_withVal, isUniformInducing_coe, isUniformInducing_extend, toUniformEquivOfIsUniformInducing, withValRingEquiv
-/
def withValUniformEquiv :
    (Rat.padicValuation p).Completion ≃ᵤ Rat_[p] :=
UniformEquiv.symm Padic.withValRingEquiv.symm.toUniformEquivOfIsUniformInducing
    isDenseInducing_cast_withVal.isUniformInducing_extend isUniformInducing_cast_withVal
      (Completion.isUniformInducing_coe _)

@[simp]
/--
lemma `toEquiv_withValUniformEquiv_eq_toEquiv_withValRingEquiv` / 引理 `toEquiv_withValUniformEquiv_eq_toEquiv_withValRingEquiv`

English:
lemma toEquiv_withValUniformEquiv_eq_toEquiv_withValRingEquiv
  proof: rfl

中文:
引理 toEquiv_withValUniformEquiv_eq_toEquiv_withValRingEquiv
  证明: rfl

Depends on / 依赖: Completion, Rat.padicValuation, Rat_, padicValuation
-/
lemma toEquiv_withValUniformEquiv_eq_toEquiv_withValRingEquiv :
    (withValUniformEquiv (p := p) : (Rat.padicValuation p).Completion ≃ Rat_[p]) =
      (withValRingEquiv (p := p) :) := rfl

open UniformSpace.Completion in
@[simp]
/--
theorem `withValUniformEquiv_cast_apply` / 定理 `withValUniformEquiv_cast_apply`

English:
theorem withValUniformEquiv_cast_apply
  given: (x : WithVal (Rat.padicValuation p))
  proof: by
  simpa [Equiv.toUniformEquivOfIsUniformInducing] using!
    extension_coe (Padic.isUniformInducing_cast_withVal (p := p)).uniformContinuous _

中文:
定理 withValUniformEquiv_cast_apply
  条件: (x : WithVal (Rat.padicValuation p))
  证明: by
  simpa [Equiv.toUniformEquivOfIsUniformInducing] using!
    extension_coe (Padic.isUniformInducing_cast_withVal (p := p)).uniformContinuous _

Depends on / 依赖: Equiv.toUniformEquivOfIsUniformInducing, Padic.isUniformInducing_cast_withVal, Rat.padicValuation, WithVal, WithVal.equiv, extension_coe, isUniformInducing_cast_withVal, padicValuation, toUniformEquivOfIsUniformInducing, uniformContinuous
-/
theorem withValUniformEquiv_cast_apply (x : WithVal (Rat.padicValuation p)) :
    Padic.withValUniformEquiv (p := p) x = WithVal.equiv (Rat.padicValuation p) x := by
  simpa [Equiv.toUniformEquivOfIsUniformInducing] using!
    extension_coe (Padic.isUniformInducing_cast_withVal (p := p)).uniformContinuous _

open PadicInt in
/--
theorem `norm_rat_le_one_iff_padicValuation_le_one` / 定理 `norm_rat_le_one_iff_padicValuation_le_one`

English:
theorem norm_rat_le_one_iff_padicValuation_le_one
  given: (p : Nat) [Fact p.Prime] {x : Rat}
  proof: by
  rw [Rat.padicValuation_le_one_iff]
  refine ⟨fun h => ?_, fun h => Padic.norm_rat_le_one h⟩
simpa [Nat.Prime.coprime_iff_not_dvd Fact.out] using isUnit_iff.1 isUnit_den _ h

中文:
定理 norm_rat_le_one_iff_padicValuation_le_one
  条件: (p : 自然数) [Fact p.Prime] {x : Rat}
  证明: by
  rw [Rat.padicValuation_le_one_iff]
  refine ⟨fun h => ?_, fun h => Padic.norm_rat_le_one h⟩
simpa [Nat.Prime.coprime_iff_not_dvd Fact.out] using isUnit_iff.1 isUnit_den _ h

Depends on / 依赖: Fact.out, Nat.Prime.coprime_iff_not_dvd, Padic.norm_rat_le_one, Rat.padicValuation_le_one_iff, coprime_iff_not_dvd, isUnit_den, isUnit_iff, norm_rat_le_one, padicValuation_le_one_iff
-/
theorem norm_rat_le_one_iff_padicValuation_le_one (p : Nat) [Fact p.Prime] {x : Rat} :
    ‖(x : Rat_[p])‖ <= 1 ↔ Rat.padicValuation p x <= 1 := by
  rw [Rat.padicValuation_le_one_iff]
  refine ⟨fun h => ?_, fun h => Padic.norm_rat_le_one h⟩
simpa [Nat.Prime.coprime_iff_not_dvd Fact.out] using isUnit_iff.1 isUnit_den _ h

/--
theorem `withValUniformEquiv_norm_le_one_iff` / 定理 `withValUniformEquiv_norm_le_one_iff`

English:
theorem withValUniformEquiv_norm_le_one_iff
  statement: {p : Nat} [Fact p.Prime]
  proof: by
  induction x using UniformSpace.Completion.induction_on with
  | hp =>
    rw [Set.ext fun _ => Iff.comm]
    simp_rw [← Valuation.restrict_le_one_iff Valued.v]
    apply withValUniformEquiv.toHomeomorph.isClosed_setOfPred_iff (q := fun x => ‖x‖ <= 1)
      (Valued.isClopen_closedBall _ one_ne_z

中文:
定理 withValUniformEquiv_norm_le_one_iff
  结论: {p : 自然数} [Fact p.Prime]
  证明: by
  induction x using UniformSpace.Completion.induction_on with
  | hp =>
    rw [Set.ext fun _ => Iff.comm]
    simp_rw [← Valuation.restrict_le_one_iff Valued.v]
    apply withValUniformEquiv.toHomeomorph.isClosed_setOfPred_iff (q := fun x => ‖x‖ <= 1)
      (Valued.isClopen_closedBall _ one_ne_z

Depends on / 依赖: Completion, Iff.comm, IsUltrametricDist, IsUltrametricDist.isClopen_closedBall, Metric, Metric.closedBall, Rat_, Set.ext, UniformSpace, UniformSpace.Completion.induction_on, Valuation, Valuation.restrict_le_one_iff, Valued, Valued.isClopen_closedBall, Valued.v, Valued.valuedCompletion_apply, WithVal, WithVal.apply_ofVal, apply_ofVal, closedBall
-/
theorem withValUniformEquiv_norm_le_one_iff {p : Nat} [Fact p.Prime]
    (x : (Rat.padicValuation p).Completion) :
    ‖Padic.withValUniformEquiv x‖ <= 1 ↔ Valued.v x <= 1 := by
  induction x using UniformSpace.Completion.induction_on with
  | hp =>
    rw [Set.ext fun _ => Iff.comm]
    simp_rw [← Valuation.restrict_le_one_iff Valued.v]
    apply withValUniformEquiv.toHomeomorph.isClosed_setOfPred_iff (q := fun x => ‖x‖ <= 1)
      (Valued.isClopen_closedBall _ one_ne_zero)
    simpa [Metric.closedBall] using IsUltrametricDist.isClopen_closedBall (0 : Rat_[p]) one_ne_zero
  | ih a =>
    rw [Valued.valuedCompletion_apply]; rw [← WithVal.apply_ofVal]; rw [withValUniformEquiv_cast_apply]
    exact (norm_rat_le_one_iff_padicValuation_le_one p)

end Padic

namespace PadicInt

open Padic Valued

variable {p : Nat} [Fact p.Prime]

/--
Definition of `withValIntegersRingEquiv` / `withValIntegersRingEquiv` 的定义

English:
definition withValIntegersRingEquiv
  signature: {p : Nat} [Fact p.Prime]
  body: withValRingEquiv.restrict _ (subring p) fun _ => (withValUniformEquiv_norm_le_one_iff _).symm

中文:
定义 withValIntegersRingEquiv
  签名: {p : 自然数} [Fact p.Prime]
  定义体: withValRingEquiv.restrict _ (subring p) fun _ => (withValUniformEquiv_norm_le_one_iff _).symm

Depends on / 依赖: restrict, subring, withValRingEquiv, withValRingEquiv.restrict, withValUniformEquiv_norm_le_one_iff
-/
noncomputable def withValIntegersRingEquiv {p : Nat} [Fact p.Prime] :
    𝒪[(Rat.padicValuation p).Completion] ≃+* Int_[p] :=
  withValRingEquiv.restrict _ (subring p) fun _ => (withValUniformEquiv_norm_le_one_iff _).symm

/--
Definition of `withValIntegersUniformEquiv` / `withValIntegersUniformEquiv` 的定义

English:
definition withValIntegersUniformEquiv
  signature: : 𝒪[(Rat.padicValuation p).Completion] ≃ᵤ Int_[p]
  body: withValUniformEquiv.subtype fun _ => (withValUniformEquiv_norm_le_one_iff _).symm

中文:
定义 withValIntegersUniformEquiv
  签名: : 𝒪[(Rat.padicValuation p).Completion] ≃ᵤ 整数_[p]
  定义体: withValUniformEquiv.subtype fun _ => (withValUniformEquiv_norm_le_one_iff _).symm

Depends on / 依赖: subtype, withValUniformEquiv, withValUniformEquiv.subtype, withValUniformEquiv_norm_le_one_iff
-/
noncomputable def withValIntegersUniformEquiv : 𝒪[(Rat.padicValuation p).Completion] ≃ᵤ Int_[p] :=
  withValUniformEquiv.subtype fun _ => (withValUniformEquiv_norm_le_one_iff _).symm

end PadicInt
