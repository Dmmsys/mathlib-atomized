/-
Copyright (c) 2025 David Loeffler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Loeffler
-/
module

public import Mathlib.NumberTheory.ModularForms.LevelOne.Basic

/-!
# Norm and trace maps

Given two subgroups `𝒢, ℋ` of `GL(2, ℝ)` with `𝒢.relindex ℋ ≠ 0` (i.e. `𝒢 ⊓ ℋ` has finite index
in `ℋ`), we define a trace map from `ModularForm (𝒢 ⊓ ℋ) k` to `ModularForm ℋ k`.
-/

@[expose] public noncomputable section

open UpperHalfPlane

open scoped ModularForm Topology Filter Manifold

variable {𝒢 ℋ : Subgroup (GL (Fin 2) Real)} {F : Type*} (f : F) [FunLike F ℍ Complex] {k : Int}

local notation "𝒬" => ℋ ⧸ (𝒢.subgroupOf ℋ)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: MulAction ℋ ℋ
  body: Monoid.toMulAction ..

中文:
实例 :
  签名: 乘法作用 ℋ ℋ
  定义体: Monoid.toMulAction ..

Depends on / 依赖: Monoid, Monoid.toMulAction, toMulAction
-/
instance : MulAction ℋ ℋ := Monoid.toMulAction ..
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: MulAction ℋ 𝒬
  body: .quotient ..

中文:
实例 :
  签名: 乘法作用 ℋ 𝒬
  定义体: .quotient ..

Depends on / 依赖: quotient
-/
instance : MulAction ℋ 𝒬 := .quotient ..

namespace SlashInvariantForm

variable [SlashInvariantFormClass F 𝒢 k]

/--
Definition of `quotientFunc` / `quotientFunc` 的定义

English:
definition quotientFunc
  signature: (q : 𝒬) (τ : ℍ)
  body: q.liftOn (fun g => ((f : ℍ -> Complex) ∣[k] g.val⁻¹) τ) (fun h h' hhh' => by
    obtain ⟨j, hj, hj'⟩ : exists g in 𝒢, h' = h * g := by
      rw [← Quotient.eq_iff_equiv]; rw [Quotient.eq]; rw [QuotientGroup.leftRel_apply] at hhh'
      exact ⟨h⁻¹ * h', hhh', mod_cast (mul_inv_cancel_left h h').symm⟩
    simp [hj', SlashAction.slash_mul, SlashInvariantFormClass.slash_action_eq f j⁻¹ (inv_mem hj)])

中文:
定义 quotientFunc
  签名: (q : 𝒬) (τ : ℍ)
  定义体: q.liftOn (fun g => ((f : ℍ -> Complex) ∣[k] g.val⁻¹) τ) (fun h h' hhh' => by
    obtain ⟨j, hj, hj'⟩ : exists g in 𝒢, h' = h * g := by
      rw [← Quotient.eq_iff_equiv]; rw [Quotient.eq]; rw [QuotientGroup.leftRel_apply] at hhh'
      exact ⟨h⁻¹ * h', hhh', mod_cast (mul_inv_cancel_left h h').symm⟩
    simp [hj', SlashAction.slash_mul, SlashInvariantFormClass.slash_action_eq f j⁻¹ (inv_mem hj)])

Depends on / 依赖: Quotient, Quotient.eq, Quotient.eq_iff_equiv, QuotientGroup, QuotientGroup.leftRel_apply, SlashAction, SlashAction.slash_mul, SlashInvariantFormClass, SlashInvariantFormClass.slash_action_eq, eq_iff_equiv, g.val, inv_mem, leftRel_apply, liftOn, mod_cast, mul_inv_cancel_left, q.liftOn, slash_action_eq, slash_mul
-/
def quotientFunc (q : 𝒬) (τ : ℍ) : Complex :=
  q.liftOn (fun g => ((f : ℍ -> Complex) ∣[k] g.val⁻¹) τ) (fun h h' hhh' => by
    obtain ⟨j, hj, hj'⟩ : exists g in 𝒢, h' = h * g := by
      rw [← Quotient.eq_iff_equiv]; rw [Quotient.eq]; rw [QuotientGroup.leftRel_apply] at hhh'
      exact ⟨h⁻¹ * h', hhh', mod_cast (mul_inv_cancel_left h h').symm⟩
    simp [hj', SlashAction.slash_mul, SlashInvariantFormClass.slash_action_eq f j⁻¹ (inv_mem hj)])

/--
lemma `quotientFunc_mk` / 引理 `quotientFunc_mk`

English:
lemma quotientFunc_mk
  given: (h : ℋ)
  statement: quotientFunc f ⟦h⟧ = (f : ℍ -> Complex) ∣[k] h.val⁻¹
  proof: rfl

中文:
引理 quotientFunc_mk
  条件: (h : ℋ)
  结论: quotientFunc f ⟦h⟧ = (f : ℍ -> 复形) ∣[k] h.val⁻¹
  证明: rfl
-/
@[simp] lemma quotientFunc_mk (h : ℋ) : quotientFunc f ⟦h⟧ = (f : ℍ -> Complex) ∣[k] h.val⁻¹ :=
  rfl

/--
lemma `quotientFunc_smul` / 引理 `quotientFunc_smul`

English:
lemma quotientFunc_smul
  given: {h} (hh : h in ℋ) (q : 𝒬)
  proof: by
  induction q using Quotient.inductionOn with
  | h r => simp [SlashAction.slash_mul]

中文:
引理 quotientFunc_smul
  条件: {h} (hh : h in ℋ) (q : 𝒬)
  证明: by
  induction q using Quotient.inductionOn with
  | h r => simp [SlashAction.slash_mul]

Depends on / 依赖: Quotient, Quotient.inductionOn, SlashAction, SlashAction.slash_mul, inductionOn, slash_mul
-/
lemma quotientFunc_smul {h} (hh : h in ℋ) (q : 𝒬) :
    quotientFunc f q ∣[k] h = quotientFunc f ((⟨h, hh⟩ : ℋ)⁻¹ • q) := by
  induction q using Quotient.inductionOn with
  | h r => simp [SlashAction.slash_mul]

variable (ℋ) [𝒢.IsFiniteRelIndex ℋ]

/-- The trace of a slash-invariant form, as a slash-invariant form. -/
@[simps! -fullyApplied]
/--
Definition of `trace` / `trace` 的定义

English:
definition trace
  signature: : SlashInvariantForm ℋ k where
  body: let := Fintype.ofFinite 𝒬; ∑ q : 𝒬, quotientFunc f q
  slash_action_eq' h hh := by
    let := Fintype.ofFinite 𝒬
    simpa [SlashAction.sum_slash, quotientFunc_smul f hh]
      using Equiv.sum_comp (MulAction.toPerm (_ : ℋ)) _

中文:
定义 trace
  签名: : 斜不变形式 ℋ k where
  定义体: let := Fintype.ofFinite 𝒬; ∑ q : 𝒬, quotientFunc f q
  slash_action_eq' h hh := by
    let := Fintype.ofFinite 𝒬
    simpa [SlashAction.sum_slash, quotientFunc_smul f hh]
      using Equiv.sum_comp (MulAction.toPerm (_ : ℋ)) _
-/
protected def trace : SlashInvariantForm ℋ k where
  toFun := let := Fintype.ofFinite 𝒬; ∑ q : 𝒬, quotientFunc f q
  slash_action_eq' h hh := by
    let := Fintype.ofFinite 𝒬
    simpa [SlashAction.sum_slash, quotientFunc_smul f hh]
      using Equiv.sum_comp (MulAction.toPerm (_ : ℋ)) _

/-- The norm of a slash-invariant form, as a slash-invariant form. -/
@[simps! -fullyApplied]
/--
Definition of `norm` / `norm` 的定义

English:
definition norm
  signature: [ℋ.HasDetPlusMinusOne]
  body: let := Fintype.ofFinite 𝒬; ∏ q : 𝒬, quotientFunc f q
  slash_action_eq' h hh := by
    let := Fintype.ofFinite 𝒬
    simpa [← Finset.card_univ, ModularForm.prod_slash,
      quotientFunc_smul f hh, Subgroup.HasDetPlusMinusOne.abs_det hh,
      -Matrix.GeneralLinearGroup.val_det_apply] using Equiv.prod_comp (MulAction.toPerm (_ : ℋ)) _

中文:
定义 norm
  签名: [ℋ.有DetPlusMinusOne]
  定义体: let := Fintype.ofFinite 𝒬; ∏ q : 𝒬, quotientFunc f q
  slash_action_eq' h hh := by
    let := Fintype.ofFinite 𝒬
    simpa [← Finset.card_univ, ModularForm.prod_slash,
      quotientFunc_smul f hh, Subgroup.HasDetPlusMinusOne.abs_det hh,
      -Matrix.GeneralLinearGroup.val_det_apply] using Equiv.prod_comp (MulAction.toPerm (_ : ℋ)) _
-/
protected def norm [ℋ.HasDetPlusMinusOne] : SlashInvariantForm ℋ (k * Nat.card 𝒬) where
  toFun := let := Fintype.ofFinite 𝒬; ∏ q : 𝒬, quotientFunc f q
  slash_action_eq' h hh := by
    let := Fintype.ofFinite 𝒬
    simpa [← Finset.card_univ, ModularForm.prod_slash,
      quotientFunc_smul f hh, Subgroup.HasDetPlusMinusOne.abs_det hh,
      -Matrix.GeneralLinearGroup.val_det_apply] using Equiv.prod_comp (MulAction.toPerm (_ : ℋ)) _

end SlashInvariantForm

open SlashInvariantForm

section ModularForm

variable (ℋ) [𝒢.IsFiniteRelIndex ℋ]

/-- The trace of a modular form, as a modular form. -/
@[simps! -fullyApplied]
/--
Definition of `ModularForm.trace` / `ModularForm.trace` 的定义

English:
definition ModularForm.trace
  signature: [ModularFormClass F 𝒢 k]
  body: SlashInvariantForm.trace ℋ f
  holo' := .sum (Quotient.forall.mpr fun ⟨r, hr⟩ _ => (translate f r⁻¹).holo')
  bdd_at_cusps' h γ := by
    rintro rfl
    rw [SlashInvariantForm.trace]; rw [IsBoundedAtImInfty]; rw [Filter.BoundedAtFilter]; rw [SlashAction.sum_slash]; rw [Finset.sum_fn]
    refine .fun_sum (Quotient.forall.mpr fun ⟨r, hr⟩ _ => (translate f _).bdd_at_cusps' ?_ γ rfl)
    simpa using h.of_isFiniteRelIndex_conj hr

中文:
定义 模形式.trace
  签名: [模形式类 F 𝒢 k]
  定义体: SlashInvariantForm.trace ℋ f
  holo' := .sum (Quotient.forall.mpr fun ⟨r, hr⟩ _ => (translate f r⁻¹).holo')
  bdd_at_cusps' h γ := by
    rintro rfl
    rw [SlashInvariantForm.trace]; rw [IsBoundedAtImInfty]; rw [Filter.BoundedAtFilter]; rw [SlashAction.sum_slash]; rw [Finset.sum_fn]
    refine .fun_sum (Quotient.forall.mpr fun ⟨r, hr⟩ _ => (translate f _).bdd_at_cusps' ?_ γ rfl)
    simpa using h.of_isFiniteRelIndex_conj hr
-/
protected def ModularForm.trace [ModularFormClass F 𝒢 k] : ModularForm ℋ k where
  __ := SlashInvariantForm.trace ℋ f
  holo' := .sum (Quotient.forall.mpr fun ⟨r, hr⟩ _ => (translate f r⁻¹).holo')
  bdd_at_cusps' h γ := by
    rintro rfl
    rw [SlashInvariantForm.trace]; rw [IsBoundedAtImInfty]; rw [Filter.BoundedAtFilter]; rw [SlashAction.sum_slash]; rw [Finset.sum_fn]
    refine .fun_sum (Quotient.forall.mpr fun ⟨r, hr⟩ _ => (translate f _).bdd_at_cusps' ?_ γ rfl)
    simpa using h.of_isFiniteRelIndex_conj hr

/-- The trace of a cusp form, as a cusp form. -/
@[simps! -fullyApplied]
/--
Definition of `CuspForm.trace` / `CuspForm.trace` 的定义

English:
definition CuspForm.trace
  signature: [CuspFormClass F 𝒢 k]
  body: ModularForm.trace ℋ f
  zero_at_cusps' h γ := by
    rintro rfl
    simp_rw [ModularForm.toFun_eq_coe, ModularForm.coe_trace, IsZeroAtImInfty, Filter.ZeroAtFilter,
      SlashAction.sum_slash, Finset.sum_fn]
    let := Fintype.ofFinite 𝒬
    rw [show (0 : Complex) = ∑ c : ℋ ⧸ 𝒢.subgroupOf ℋ]; rw [0 by simp]
    refine tendsto_finsetSum _ (Quotient.forall.mpr fun ⟨r, hr⟩ _ => ?_)
    refine (translate f _).zero_at_cusps' ?_ γ rfl
    simpa using h.of_isFiniteRelIndex_conj hr

中文:
定义 尖点形式.trace
  签名: [尖点形式类 F 𝒢 k]
  定义体: ModularForm.trace ℋ f
  zero_at_cusps' h γ := by
    rintro rfl
    simp_rw [ModularForm.toFun_eq_coe, ModularForm.coe_trace, IsZeroAtImInfty, Filter.ZeroAtFilter,
      SlashAction.sum_slash, Finset.sum_fn]
    let := Fintype.ofFinite 𝒬
    rw [show (0 : Complex) = ∑ c : ℋ ⧸ 𝒢.subgroupOf ℋ]; rw [0 by simp]
    refine tendsto_finsetSum _ (Quotient.forall.mpr fun ⟨r, hr⟩ _ => ?_)
    refine (translate f _).zero_at_cusps' ?_ γ rfl
    simpa using h.of_isFiniteRelIndex_conj hr
-/
protected def CuspForm.trace [CuspFormClass F 𝒢 k] : CuspForm ℋ k where
  __ := ModularForm.trace ℋ f
  zero_at_cusps' h γ := by
    rintro rfl
    simp_rw [ModularForm.toFun_eq_coe, ModularForm.coe_trace, IsZeroAtImInfty, Filter.ZeroAtFilter,
      SlashAction.sum_slash, Finset.sum_fn]
    let := Fintype.ofFinite 𝒬
    rw [show (0 : Complex) = ∑ c : ℋ ⧸ 𝒢.subgroupOf ℋ]; rw [0 by simp]
    refine tendsto_finsetSum _ (Quotient.forall.mpr fun ⟨r, hr⟩ _ => ?_)
    refine (translate f _).zero_at_cusps' ?_ γ rfl
    simpa using h.of_isFiniteRelIndex_conj hr

/-- The norm of a modular form, as a modular form. -/
@[simps! -fullyApplied]
/--
Definition of `ModularForm.norm` / `ModularForm.norm` 的定义

English:
definition ModularForm.norm
  signature: [ℋ.HasDetPlusMinusOne] [ModularFormClass F 𝒢 k]
  body: SlashInvariantForm.norm ℋ f
  holo' := .prod (Quotient.forall.mpr fun ⟨r, hr⟩ _ => (translate f r⁻¹).holo')
  bdd_at_cusps' h γ := by
    rintro rfl
    simp_rw [SlashInvariantForm.norm, IsBoundedAtImInfty, Filter.BoundedAtFilter]
    let := Fintype.ofFinite 𝒬
    rw [Nat.card_eq_fintype_card]; rw [← Finset.card_univ]; rw [ModularForm.prod_slash]
    apply Asymptotics.IsBigO.const_smul_left
    rw [show (1 : ℍ -> Real) = (fun x => ∏ (i : 𝒬)]; rw [1) by ext; simp]; rw [Finset.prod_fn]
    refine .finsetProd (Quotient.forall.mpr fun ⟨r, hr⟩ _ => (translate f _).bdd_at_cusps' ?_ γ rfl)
    simpa using h.of_isFiniteRelIndex_conj hr

中文:
定义 模形式.norm
  签名: [ℋ.有DetPlusMinusOne] [模形式类 F 𝒢 k]
  定义体: SlashInvariantForm.norm ℋ f
  holo' := .prod (Quotient.forall.mpr fun ⟨r, hr⟩ _ => (translate f r⁻¹).holo')
  bdd_at_cusps' h γ := by
    rintro rfl
    simp_rw [SlashInvariantForm.norm, IsBoundedAtImInfty, Filter.BoundedAtFilter]
    let := Fintype.ofFinite 𝒬
    rw [Nat.card_eq_fintype_card]; rw [← Finset.card_univ]; rw [ModularForm.prod_slash]
    apply Asymptotics.IsBigO.const_smul_left
    rw [show (1 : ℍ -> Real) = (fun x => ∏ (i : 𝒬)]; rw [1) by ext; simp]; rw [Finset.prod_fn]
    refine .finsetProd (Quotient.forall.mpr fun ⟨r, hr⟩ _ => (translate f _).bdd_at_cusps' ?_ γ rfl)
    simpa using h.of_isFiniteRelIndex_conj hr
-/
protected def ModularForm.norm [ℋ.HasDetPlusMinusOne] [ModularFormClass F 𝒢 k] :
    ModularForm ℋ (k * Nat.card 𝒬) where
  __ := SlashInvariantForm.norm ℋ f
  holo' := .prod (Quotient.forall.mpr fun ⟨r, hr⟩ _ => (translate f r⁻¹).holo')
  bdd_at_cusps' h γ := by
    rintro rfl
    simp_rw [SlashInvariantForm.norm, IsBoundedAtImInfty, Filter.BoundedAtFilter]
    let := Fintype.ofFinite 𝒬
    rw [Nat.card_eq_fintype_card]; rw [← Finset.card_univ]; rw [ModularForm.prod_slash]
    apply Asymptotics.IsBigO.const_smul_left
    rw [show (1 : ℍ -> Real) = (fun x => ∏ (i : 𝒬)]; rw [1) by ext; simp]; rw [Finset.prod_fn]
    refine .finsetProd (Quotient.forall.mpr fun ⟨r, hr⟩ _ => (translate f _).bdd_at_cusps' ?_ γ rfl)
    simpa using h.of_isFiniteRelIndex_conj hr

variable {f} in
/--
lemma `ModularForm.norm_ne_zero` / 引理 `ModularForm.norm_ne_zero`

English:
lemma ModularForm.norm_ne_zero
  statement: [ℋ.HasDetPlusMinusOne] [ModularFormClass F 𝒢 k]
  proof: by
  contrapose hf
  rw [← DFunLike.coe_injective.eq_iff]; rw [coe_norm]; rw [FunLike.coe_zero]; rw [prod_eq_zero_iff] at hf
  · simpa [QuotientGroup.exists_mk] using hf
  · exact Quotient.forall.mpr fun r _ => (translate f r.val⁻¹).holo'

中文:
引理 模形式.norm_ne_zero
  结论: [ℋ.有DetPlusMinusOne] [模形式类 F 𝒢 k]
  证明: by
  contrapose hf
  rw [← DFunLike.coe_injective.eq_iff]; rw [coe_norm]; rw [FunLike.coe_zero]; rw [prod_eq_zero_iff] at hf
  · simpa [QuotientGroup.exists_mk] using hf
  · exact Quotient.forall.mpr fun r _ => (translate f r.val⁻¹).holo'

Depends on / 依赖: DFunLike, DFunLike.coe_injective.eq_iff, FunLike, FunLike.coe_zero, Quotient, Quotient.forall.mpr, QuotientGroup, QuotientGroup.exists_mk, coe_injective, coe_norm, coe_zero, contrapose, eq_iff, exists_mk, prod_eq_zero_iff, r.val, translate
-/
lemma ModularForm.norm_ne_zero [ℋ.HasDetPlusMinusOne] [ModularFormClass F 𝒢 k]
    (hf : (f : ℍ -> Complex) != 0) : ModularForm.norm ℋ f != 0 := by
  contrapose hf
  rw [← DFunLike.coe_injective.eq_iff]; rw [coe_norm]; rw [FunLike.coe_zero]; rw [prod_eq_zero_iff] at hf
  · simpa [QuotientGroup.exists_mk] using hf
  · exact Quotient.forall.mpr fun r _ => (translate f r.val⁻¹).holo'

/--
lemma `ModularForm.norm_eq_zero_iff` / 引理 `ModularForm.norm_eq_zero_iff`

English:
lemma ModularForm.norm_eq_zero_iff
  given: [ℋ.HasDetPlusMinusOne] [ModularFormClass F 𝒢 k]
  proof: by
  refine ⟨fun hn => ?_, fun hf => ?_⟩
  · contrapose! hn
    exact norm_ne_zero ℋ hn
  · ext τ
    simpa [Finset.prod_eq_zero_iff, QuotientGroup.exists_mk]
      using ⟨1, by simpa using congr_fun hf τ⟩

中文:
引理 模形式.norm_eq_zero_iff
  条件: [ℋ.有DetPlusMinusOne] [模形式类 F 𝒢 k]
  证明: by
  refine ⟨fun hn => ?_, fun hf => ?_⟩
  · contrapose! hn
    exact norm_ne_zero ℋ hn
  · ext τ
    simpa [Finset.prod_eq_zero_iff, QuotientGroup.exists_mk]
      using ⟨1, by simpa using congr_fun hf τ⟩

Depends on / 依赖: Finset, Finset.prod_eq_zero_iff, QuotientGroup, QuotientGroup.exists_mk, congr_fun, contrapose, exists_mk, norm_ne_zero, prod_eq_zero_iff
-/
lemma ModularForm.norm_eq_zero_iff [ℋ.HasDetPlusMinusOne] [ModularFormClass F 𝒢 k] :
    ModularForm.norm ℋ f = 0 ↔ (f : ℍ -> Complex) = 0 := by
  refine ⟨fun hn => ?_, fun hf => ?_⟩
  · contrapose! hn
    exact norm_ne_zero ℋ hn
  · ext τ
    simpa [Finset.prod_eq_zero_iff, QuotientGroup.exists_mk]
      using ⟨1, by simpa using congr_fun hf τ⟩

open scoped MatrixGroups

/--
lemma `ModularForm.isZero_of_neg_weight` / 引理 `ModularForm.isZero_of_neg_weight`

English:
lemma ModularForm.isZero_of_neg_weight
  statement: [𝒢.IsArithmetic]
  proof: by
  suffices ModularForm.norm 𝒮ℒ f = 0 by simpa [ModularForm.norm_eq_zero_iff]
  ext
  rw [ModularFormClass.levelOne_neg_weight_eq_zero
    (mul_neg_of_neg_of_pos hk <| mod_cast Nat.pos_of_ne_zero 𝒢.relIndex_ne_zero)
    (ModularForm.norm 𝒮ℒ f)]; rw [Pi.zero_apply]; rw [zero_apply]

中文:
引理 模形式.isZero_of_neg_weight
  结论: [𝒢.是Arithmetic]
  证明: by
  suffices ModularForm.norm 𝒮ℒ f = 0 by simpa [ModularForm.norm_eq_zero_iff]
  ext
  rw [ModularFormClass.levelOne_neg_weight_eq_zero
    (mul_neg_of_neg_of_pos hk <| mod_cast Nat.pos_of_ne_zero 𝒢.relIndex_ne_zero)
    (ModularForm.norm 𝒮ℒ f)]; rw [Pi.zero_apply]; rw [zero_apply]

Depends on / 依赖: ModularForm, ModularForm.norm, ModularForm.norm_eq_zero_iff, ModularFormClass, ModularFormClass.levelOne_neg_weight_eq_zero, Nat.pos_of_ne_zero, Pi.zero_apply, levelOne_neg_weight_eq_zero, mod_cast, mul_neg_of_neg_of_pos, norm_eq_zero_iff, pos_of_ne_zero, relIndex_ne_zero, zero_apply
-/
lemma ModularForm.isZero_of_neg_weight [𝒢.IsArithmetic]
    {k : Int} (hk : k < 0) (f : ModularForm 𝒢 k) : f = 0 := by
  suffices ModularForm.norm 𝒮ℒ f = 0 by simpa [ModularForm.norm_eq_zero_iff]
  ext
  rw [ModularFormClass.levelOne_neg_weight_eq_zero
    (mul_neg_of_neg_of_pos hk <| mod_cast Nat.pos_of_ne_zero 𝒢.relIndex_ne_zero)
    (ModularForm.norm 𝒮ℒ f)]; rw [Pi.zero_apply]; rw [zero_apply]

/--
lemma `ModularForm.eq_const_of_weight_zero₀` / 引理 `ModularForm.eq_const_of_weight_zero₀`

English:
lemma ModularForm.eq_const_of_weight_zero₀
  statement: [𝒢.IsArithmetic] [𝒢.HasDetOne]
  proof: by
  -- Consider the norm of `f - (f I)`. This must be a constant, since it's a weight 0 level 1 form.
  let : ModularFormClass (ModularForm 𝒮ℒ (0 * Nat.card (𝒮ℒ ⧸ 𝒢.subgroupOf 𝒮ℒ))) 𝒮ℒ 0 := by
    rw [zero_mul]; infer_instance
  obtain ⟨c, hc⟩ := ModularFormClass.levelOne_weight_zero_const
    (ModularForm.norm 𝒮ℒ (f - .const (f I)))
  -- But the constant must be 0, since `f - f I` vanishes at `I`.
  have : ModularForm.norm 𝒮ℒ (f - .const (f I)) I = 0 := by
    simpa [Finset.prod_eq_zero_iff, QuotientGroup.exists_mk] using ⟨1, by simp⟩
  obtain rfl : c = 0 := by simpa [hc]
  -- So `f - f I` has zero norm, hence it's the zero form.
  simp only [Function.const_zero, FunLike.coe_zero_iff, norm_eq_zero_iff, sub_eq_zero] at hc
  exact ⟨f I, by rw [hc, ModularForm.coe_const, Function.const_apply]⟩

中文:
引理 模形式.eq_const_of_weight_zero₀
  结论: [𝒢.是Arithmetic] [𝒢.有DetOne]
  证明: by
  -- Consider the norm of `f - (f I)`. This must be a constant, since it's a weight 0 level 1 form.
  let : ModularFormClass (ModularForm 𝒮ℒ (0 * Nat.card (𝒮ℒ ⧸ 𝒢.subgroupOf 𝒮ℒ))) 𝒮ℒ 0 := by
    rw [zero_mul]; infer_instance
  obtain ⟨c, hc⟩ := ModularFormClass.levelOne_weight_zero_const
    (ModularForm.norm 𝒮ℒ (f - .const (f I)))
  -- But the constant must be 0, since `f - f I` vanishes at `I`.
  have : ModularForm.norm 𝒮ℒ (f - .const (f I)) I = 0 := by
    simpa [Finset.prod_eq_zero_iff, QuotientGroup.exists_mk] using ⟨1, by simp⟩
  obtain rfl : c = 0 := by simpa [hc]
  -- So `f - f I` has zero norm, hence it's the zero form.
  simp only [Function.const_zero, FunLike.coe_zero_iff, norm_eq_zero_iff, sub_eq_zero] at hc
  exact ⟨f I, by rw [hc, ModularForm.coe_const, Function.const_apply]⟩
-/
private lemma ModularForm.eq_const_of_weight_zero₀ [𝒢.IsArithmetic] [𝒢.HasDetOne]
    (f : ModularForm 𝒢 0) : exists c, (f : ℍ -> Complex) = Function.const ℍ c := by
  -- Consider the norm of `f - (f I)`. This must be a constant, since it's a weight 0 level 1 form.
  let : ModularFormClass (ModularForm 𝒮ℒ (0 * Nat.card (𝒮ℒ ⧸ 𝒢.subgroupOf 𝒮ℒ))) 𝒮ℒ 0 := by
    rw [zero_mul]; infer_instance
  obtain ⟨c, hc⟩ := ModularFormClass.levelOne_weight_zero_const
    (ModularForm.norm 𝒮ℒ (f - .const (f I)))
  -- But the constant must be 0, since `f - f I` vanishes at `I`.
  have : ModularForm.norm 𝒮ℒ (f - .const (f I)) I = 0 := by
    simpa [Finset.prod_eq_zero_iff, QuotientGroup.exists_mk] using ⟨1, by simp⟩
  obtain rfl : c = 0 := by simpa [hc]
  -- So `f - f I` has zero norm, hence it's the zero form.
  simp only [Function.const_zero, FunLike.coe_zero_iff, norm_eq_zero_iff, sub_eq_zero] at hc
  exact ⟨f I, by rw [hc, ModularForm.coe_const, Function.const_apply]⟩

/--
lemma `ModularForm.eq_const_of_weight_zero` / 引理 `ModularForm.eq_const_of_weight_zero`

English:
lemma ModularForm.eq_const_of_weight_zero
  given: [𝒢.IsArithmetic] (f : ModularForm 𝒢 0)
  proof: eq_const_of_weight_zero₀ (𝒢 := 𝒢 ⊓ 𝒮ℒ) {
    toFun := f
    holo' := f.holo'
    bdd_at_cusps' hc := f.bdd_at_cusps' (hc.mono inf_le_left)
    slash_action_eq' γ hγ := f.slash_action_eq' γ hγ.1 }

中文:
引理 模形式.eq_const_of_weight_zero
  条件: [𝒢.是Arithmetic] (f : 模形式 𝒢 0)
  证明: eq_const_of_weight_zero₀ (𝒢 := 𝒢 ⊓ 𝒮ℒ) {
    toFun := f
    holo' := f.holo'
    bdd_at_cusps' hc := f.bdd_at_cusps' (hc.mono inf_le_left)
    slash_action_eq' γ hγ := f.slash_action_eq' γ hγ.1 }

Depends on / 依赖: bdd_at_cusps, f.bdd_at_cusps, f.holo, f.slash_action_eq, hc.mono, inf_le_left, slash_action_eq
-/
lemma ModularForm.eq_const_of_weight_zero [𝒢.IsArithmetic] (f : ModularForm 𝒢 0) :
    exists c, (f : ℍ -> Complex) = Function.const ℍ c :=
  eq_const_of_weight_zero₀ (𝒢 := 𝒢 ⊓ 𝒮ℒ) {
    toFun := f
    holo' := f.holo'
    bdd_at_cusps' hc := f.bdd_at_cusps' (hc.mono inf_le_left)
    slash_action_eq' γ hγ := f.slash_action_eq' γ hγ.1 }

end ModularForm

end
