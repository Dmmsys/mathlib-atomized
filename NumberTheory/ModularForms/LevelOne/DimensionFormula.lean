/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
module

public import Mathlib.NumberTheory.ModularForms.CuspFormSubmodule
public import Mathlib.NumberTheory.ModularForms.Discriminant

import Mathlib.Algebra.Order.Floor.Semifield

/-!
# Dimension formula and Sturm bound for level 1 modular forms

This file proves the dimension formula and the Sturm bound for the space of modular forms
for `𝒮ℒ` (= `SL(2, ℤ)`) of even weight.

## Main results

* `CuspForm.discriminantEquiv`: `CuspForm 𝒮ℒ k ≃ₗ[ℂ] ModularForm 𝒮ℒ (k - 12)`.
* `ModularForm.rank_eq_one_add_rank_cuspForm`: `rank M_k = 1 + rank S_k` for even `k ≥ 3`.
* `ModularForm.dimension_level_one`: the full dimension formula for all even `k : ℕ`.
* `ModularForm.levelOne_odd_weight_rank_zero`: modular forms of odd weight are zero.
* A `FiniteDimensional ℂ (ModularForm 𝒮ℒ k)` instance for every `k : ℤ`.
* `ModularForm.sturm_bound_levelOne`: a modular form `f : ModularForm 𝒮ℒ k` whose q-expansion
  has order strictly greater than `k / 12` is identically zero.
* `ModularForm.sturm_bound_levelOne_nat`: convenience version for `k : ℕ`.
-/

@[expose] public noncomputable section

open UpperHalfPlane ModularForm SlashInvariantForm SlashInvariantFormClass ModularFormClass
  CuspFormClass MatrixGroups OnePoint Filter EisensteinSeries Asymptotics

open scoped Topology

section DeltaIsomorphism

variable {k : Int}

local notation "Δ" => ModularForm.discriminant

namespace CuspForm

/--
Definition of `ofMulDiscriminant` / `ofMulDiscriminant` 的定义

English:
definition ofMulDiscriminant
  signature: (f : ModularForm 𝒮ℒ (k - 12))
  body: CuspForm.mcast (by ring) (CuspForm.discriminant.mulModularForm f)

@[simp]

中文:
定义 ofMulDiscriminant
  签名: (f : ModularForm 𝒮ℒ (k - 12))
  定义体: CuspForm.mcast (by ring) (CuspForm.discriminant.mulModularForm f)

@[simp]

Depends on / 依赖: CuspForm, CuspForm.discriminant.mulModularForm, CuspForm.mcast, discriminant, mulModularForm
-/
def ofMulDiscriminant (f : ModularForm 𝒮ℒ (k - 12)) : CuspForm 𝒮ℒ k :=
  CuspForm.mcast (by ring) (CuspForm.discriminant.mulModularForm f)

@[simp]
/--
lemma `ofMulDiscriminant_apply` / 引理 `ofMulDiscriminant_apply`

English:
lemma ofMulDiscriminant_apply
  given: (f : ModularForm 𝒮ℒ (k - 12)) (z : ℍ)
  proof: rfl

中文:
引理 ofMulDiscriminant_apply
  条件: (f : ModularForm 𝒮ℒ (k - 12)) (z : ℍ)
  证明: rfl
-/
lemma ofMulDiscriminant_apply (f : ModularForm 𝒮ℒ (k - 12)) (z : ℍ) :
    (ofMulDiscriminant f) z = Δ z * f z := rfl

/--
lemma `divByDiscriminant_slash_eq` / 引理 `divByDiscriminant_slash_eq`

English:
lemma divByDiscriminant_slash_eq
  given: (f : CuspForm 𝒮ℒ k) (γ : SL(2, Int))
  proof: by
  have hγ : (γ : GL (Fin 2) Real) in 𝒮ℒ := ⟨γ, rfl⟩
  change (⇑f / ⇑CuspForm.discriminant) ∣[k - 12] γ = ⇑f / ⇑CuspForm.discriminant
  simp_rw [div_slash_SL2, SL_slash, slash_action_eqn _ _ hγ]

中文:
引理 divByDiscriminant_slash_eq
  条件: (f : CuspForm 𝒮ℒ k) (γ : SL(2, 整数))
  证明: by
  have hγ : (γ : GL (Fin 2) Real) in 𝒮ℒ := ⟨γ, rfl⟩
  change (⇑f / ⇑CuspForm.discriminant) ∣[k - 12] γ = ⇑f / ⇑CuspForm.discriminant
  simp_rw [div_slash_SL2, SL_slash, slash_action_eqn _ _ hγ]

Depends on / 依赖: CuspForm, CuspForm.discriminant, SL_slash, discriminant, div_slash_SL2, simp_rw, slash_action_eqn
-/
lemma divByDiscriminant_slash_eq (f : CuspForm 𝒮ℒ k) (γ : SL(2, Int)) :
    (fun z => f z / Δ z) ∣[k - 12] γ = fun z => f z / Δ z := by
  have hγ : (γ : GL (Fin 2) Real) in 𝒮ℒ := ⟨γ, rfl⟩
  change (⇑f / ⇑CuspForm.discriminant) ∣[k - 12] γ = ⇑f / ⇑CuspForm.discriminant
  simp_rw [div_slash_SL2, SL_slash, slash_action_eqn _ _ hγ]

/--
Definition of `discriminantEquiv` / `discriminantEquiv` 的定义

English:
definition discriminantEquiv
  signature: : CuspForm 𝒮ℒ k ≃ₗ[Complex] ModularForm 𝒮ℒ (k - 12) where
  body: { toFun z := f z / Δ z
      slash_action_eq' := fun _ ⟨γ, hγ⟩ => hγ ▸ divByDiscriminant_slash_eq f γ
      holo' := f.holo'.div CuspForm.discriminant.holo' discriminant_ne_zero
      bdd_at_cusps' {c} hc := by
        rw [Subgroup.IsArithmetic.isCusp_iff_isCusp_SL2Z] at hc
        rw [isBoundedAt_i

中文:
定义 discriminantEquiv
  签名: : CuspForm 𝒮ℒ k ≃ₗ[Complex] ModularForm 𝒮ℒ (k - 12) where
  定义体: { toFun z := f z / Δ z
      slash_action_eq' := fun _ ⟨γ, hγ⟩ => hγ ▸ divByDiscriminant_slash_eq f γ
      holo' := f.holo'.div CuspForm.discriminant.holo' discriminant_ne_zero
      bdd_at_cusps' {c} hc := by
        rw [Subgroup.IsArithmetic.isCusp_iff_isCusp_SL2Z] at hc
        rw [isBoundedAt_i

Depends on / 依赖: BoundedAtFilter, CuspForm, CuspForm.discriminant.holo, IsArithmetic, IsBoundedAtImInfty, Subgroup, Subgroup.IsArithmetic.isCusp_iff_isCusp_SL2Z, bdd_at_cusps, discriminant, discriminant_ne_zero, divByDiscriminant_slash_eq, div_isBoundedUnder_of_isBigO, exp_decay_isBigO_discriminant, f.holo, isBigO_one, isBoundedAt_iff_forall_SL2Z, isCusp_iff_isCusp_SL2Z, map_add, slash_action_eq
-/
def discriminantEquiv : CuspForm 𝒮ℒ k ≃ₗ[Complex] ModularForm 𝒮ℒ (k - 12) where
  toFun f :=
    { toFun z := f z / Δ z
      slash_action_eq' := fun _ ⟨γ, hγ⟩ => hγ ▸ divByDiscriminant_slash_eq f γ
      holo' := f.holo'.div CuspForm.discriminant.holo' discriminant_ne_zero
      bdd_at_cusps' {c} hc := by
        rw [Subgroup.IsArithmetic.isCusp_iff_isCusp_SL2Z] at hc
        rw [isBoundedAt_iff_forall_SL2Z hc]
        intro γ _
        rw [divByDiscriminant_slash_eq f γ]; rw [IsBoundedAtImInfty]; rw [BoundedAtFilter]
        exact (div_isBoundedUnder_of_isBigO (exp_decay_isBigO_discriminant f)).isBigO_one Real }
  map_add' a b := by
    ext z
    change (a z + b z) / Δ z = a z / Δ z + b z / Δ z
    rw [add_div]
  map_smul' c a := by
    ext z
    change (c * a z) / Δ z = c * (a z / Δ z)
    rw [mul_div_assoc]
  invFun := ofMulDiscriminant
  left_inv f := by
    ext z
    exact mul_div_cancel₀ (f z) (discriminant_ne_zero z)
  right_inv f := by
    ext z
    exact mul_div_cancel_left₀ (f z) (discriminant_ne_zero z)

/--
lemma `discriminantEquiv_apply` / 引理 `discriminantEquiv_apply`

English:
lemma discriminantEquiv_apply
  given: (f : CuspForm 𝒮ℒ k) (z : ℍ)
  proof: rfl

中文:
引理 discriminantEquiv_apply
  条件: (f : CuspForm 𝒮ℒ k) (z : ℍ)
  证明: rfl
-/
lemma discriminantEquiv_apply (f : CuspForm 𝒮ℒ k) (z : ℍ) :
    (discriminantEquiv f) z = f z / Δ z := rfl

/-- Divide a cusp form by the discriminant to get a modular form of weight `k - 12`. -/
@[deprecated discriminantEquiv (since := "2026-05-18")]
/--
Definition of `divDiscriminant` / `divDiscriminant` 的定义

English:
definition divDiscriminant
  signature: (f : CuspForm 𝒮ℒ k)
  body: discriminantEquiv f

@[deprecated discriminantEquiv_apply (since := "2026-05-18")]

中文:
定义 divDiscriminant
  签名: (f : CuspForm 𝒮ℒ k)
  定义体: discriminantEquiv f

@[deprecated discriminantEquiv_apply (since := "2026-05-18")]

Depends on / 依赖: discriminantEquiv
-/
def divDiscriminant (f : CuspForm 𝒮ℒ k) : ModularForm 𝒮ℒ (k - 12) := discriminantEquiv f

@[deprecated discriminantEquiv_apply (since := "2026-05-18")]
/--
lemma `divDiscriminant_apply` / 引理 `divDiscriminant_apply`

English:
lemma divDiscriminant_apply
  given: (f : CuspForm 𝒮ℒ k) (z : ℍ)
  proof: rfl

中文:
引理 divDiscriminant_apply
  条件: (f : CuspForm 𝒮ℒ k) (z : ℍ)
  证明: rfl
-/
lemma divDiscriminant_apply (f : CuspForm 𝒮ℒ k) (z : ℍ) :
    (divDiscriminant f) z = f z / Δ z := rfl

end CuspForm

namespace ModularForm

@[simp]
/--
lemma `discriminant_mul_discriminantEquiv_apply` / 引理 `discriminant_mul_discriminantEquiv_apply`

English:
lemma discriminant_mul_discriminantEquiv_apply
  given: (f : CuspForm 𝒮ℒ k) (z : ℍ)
  proof: by
  rw [CuspForm.discriminantEquiv_apply]; rw [mul_div_cancel₀ _ (discriminant_ne_zero z)]

@[simp]

中文:
引理 discriminant_mul_discriminantEquiv_apply
  条件: (f : CuspForm 𝒮ℒ k) (z : ℍ)
  证明: by
  rw [CuspForm.discriminantEquiv_apply]; rw [mul_div_cancel₀ _ (discriminant_ne_zero z)]

@[simp]

Depends on / 依赖: CuspForm, CuspForm.discriminantEquiv_apply, discriminantEquiv_apply, discriminant_ne_zero
-/
lemma discriminant_mul_discriminantEquiv_apply (f : CuspForm 𝒮ℒ k) (z : ℍ) :
    Δ z * (CuspForm.discriminantEquiv f) z = f z := by
  rw [CuspForm.discriminantEquiv_apply]; rw [mul_div_cancel₀ _ (discriminant_ne_zero z)]

@[simp]
/--
lemma `discriminant_mul_discriminantEquiv` / 引理 `discriminant_mul_discriminantEquiv`

English:
lemma discriminant_mul_discriminantEquiv
  given: (f : CuspForm 𝒮ℒ k)
  proof: by
  grind [Pi.mul_apply, discriminant_mul_discriminantEquiv_apply]

中文:
引理 discriminant_mul_discriminantEquiv
  条件: (f : CuspForm 𝒮ℒ k)
  证明: by
  grind [Pi.mul_apply, discriminant_mul_discriminantEquiv_apply]

Depends on / 依赖: Pi.mul_apply, discriminant_mul_discriminantEquiv_apply, mul_apply
-/
lemma discriminant_mul_discriminantEquiv (f : CuspForm 𝒮ℒ k) :
    Δ * (CuspForm.discriminantEquiv f : ℍ -> Complex) = f := by
  grind [Pi.mul_apply, discriminant_mul_discriminantEquiv_apply]

/--
lemma `discriminant_qExpansion_order` / 引理 `discriminant_qExpansion_order`

English:
lemma discriminant_qExpansion_order
  statement: (qExpansion 1 Δ).order = 1
  proof: by
  refine PowerSeries.order_eq_nat.mpr
    ⟨discriminant_qExpansion_coeff_one ▸ one_ne_zero, fun i hi => ?_⟩
  obtain rfl : i = 0 := by lia
  simpa using CuspFormClass.qExpansion_coeff_zero CuspForm.discriminant one_pos
    one_mem_strictPeriods_SL

中文:
引理 discriminant_qExpansion_order
  结论: (qExpansion 1 Δ).order = 1
  证明: by
  refine PowerSeries.order_eq_nat.mpr
    ⟨discriminant_qExpansion_coeff_one ▸ one_ne_zero, fun i hi => ?_⟩
  obtain rfl : i = 0 := by lia
  simpa using CuspFormClass.qExpansion_coeff_zero CuspForm.discriminant one_pos
    one_mem_strictPeriods_SL

Depends on / 依赖: CuspForm, CuspForm.discriminant, CuspFormClass, CuspFormClass.qExpansion_coeff_zero, PowerSeries, PowerSeries.order_eq_nat.mpr, discriminant, discriminant_qExpansion_coeff_one, one_mem_strictPeriods_SL, one_ne_zero, one_pos, order_eq_nat, qExpansion_coeff_zero
-/
lemma discriminant_qExpansion_order : (qExpansion 1 Δ).order = 1 := by
  refine PowerSeries.order_eq_nat.mpr
    ⟨discriminant_qExpansion_coeff_one ▸ one_ne_zero, fun i hi => ?_⟩
  obtain rfl : i = 0 := by lia
  simpa using CuspFormClass.qExpansion_coeff_zero CuspForm.discriminant one_pos
    one_mem_strictPeriods_SL

/--
lemma `qExpansion_eq_qExpansion_discriminant_mul` / 引理 `qExpansion_eq_qExpansion_discriminant_mul`

English:
lemma qExpansion_eq_qExpansion_discriminant_mul
  statement: (f : ModularForm 𝒮ℒ k)
  proof: by
  rw [show (f : ℍ -> Complex) = discriminant * (toCuspForm f hcusp).discriminantEquiv from
      (discriminant_mul_discriminantEquiv (toCuspForm f hcusp)).symm]; rw [← CuspForm.coe_discriminant]
  exact ModularForm.qExpansion_mul_coe one_pos one_mem_strictPeriods_SL _ _

中文:
引理 qExpansion_eq_qExpansion_discriminant_mul
  结论: (f : ModularForm 𝒮ℒ k)
  证明: by
  rw [show (f : ℍ -> Complex) = discriminant * (toCuspForm f hcusp).discriminantEquiv from
      (discriminant_mul_discriminantEquiv (toCuspForm f hcusp)).symm]; rw [← CuspForm.coe_discriminant]
  exact ModularForm.qExpansion_mul_coe one_pos one_mem_strictPeriods_SL _ _

Depends on / 依赖: CuspForm, CuspForm.coe_discriminant, ModularForm, ModularForm.qExpansion_mul_coe, coe_discriminant, discriminant, discriminantEquiv, discriminant_mul_discriminantEquiv, one_mem_strictPeriods_SL, one_pos, qExpansion_mul_coe, toCuspForm
-/
lemma qExpansion_eq_qExpansion_discriminant_mul (f : ModularForm 𝒮ℒ k)
    (hcusp : (qExpansion 1 f).coeff 0 = 0) :
    qExpansion 1 f = qExpansion 1 discriminant *
      qExpansion 1 (CuspForm.discriminantEquiv (toCuspForm f hcusp)) := by
  rw [show (f : ℍ -> Complex) = discriminant * (toCuspForm f hcusp).discriminantEquiv from
      (discriminant_mul_discriminantEquiv (toCuspForm f hcusp)).symm]; rw [← CuspForm.coe_discriminant]
  exact ModularForm.qExpansion_mul_coe one_pos one_mem_strictPeriods_SL _ _

end ModularForm

end DeltaIsomorphism

section RankIdentity

variable {k : Int}

/--
lemma `ModularForm.levelOne_odd_weight_eq_zero` / 引理 `ModularForm.levelOne_odd_weight_eq_zero`

English:
lemma ModularForm.levelOne_odd_weight_eq_zero
  given: (hk : Odd k) (f : ModularForm 𝒮ℒ k)
  statement: f = 0
  proof: ModularForm.eq_zero_of_neg_one_mem (show (-1 : GL (Fin 2) Real) in 𝒮ℒ from ⟨-1, by ext; simp⟩) hk f

中文:
引理 ModularForm.levelOne_odd_weight_eq_zero
  条件: (hk : Odd k) (f : ModularForm 𝒮ℒ k)
  结论: f = 0
  证明: ModularForm.eq_zero_of_neg_one_mem (show (-1 : GL (Fin 2) Real) in 𝒮ℒ from ⟨-1, by ext; simp⟩) hk f

Depends on / 依赖: ModularForm, ModularForm.eq_zero_of_neg_one_mem, eq_zero_of_neg_one_mem
-/
lemma ModularForm.levelOne_odd_weight_eq_zero (hk : Odd k) (f : ModularForm 𝒮ℒ k) : f = 0 :=
  ModularForm.eq_zero_of_neg_one_mem (show (-1 : GL (Fin 2) Real) in 𝒮ℒ from ⟨-1, by ext; simp⟩) hk f

/--
lemma `ModularForm.levelOne_odd_weight_rank_zero` / 引理 `ModularForm.levelOne_odd_weight_rank_zero`

English:
lemma ModularForm.levelOne_odd_weight_rank_zero
  given: (hk : Odd k)
  proof: rank_zero_iff_forall_zero.mpr (levelOne_odd_weight_eq_zero hk)

中文:
引理 ModularForm.levelOne_odd_weight_rank_zero
  条件: (hk : Odd k)
  证明: rank_zero_iff_forall_zero.mpr (levelOne_odd_weight_eq_zero hk)

Depends on / 依赖: levelOne_odd_weight_eq_zero, rank_zero_iff_forall_zero, rank_zero_iff_forall_zero.mpr
-/
lemma ModularForm.levelOne_odd_weight_rank_zero (hk : Odd k) :
    Module.rank Complex (ModularForm 𝒮ℒ k) = 0 :=
  rank_zero_iff_forall_zero.mpr (levelOne_odd_weight_eq_zero hk)

/--
lemma `CuspForm.rank_eq_zero_of_weight_lt_twelve` / 引理 `CuspForm.rank_eq_zero_of_weight_lt_twelve`

English:
lemma CuspForm.rank_eq_zero_of_weight_lt_twelve
  given: (hk : k < 12)
  proof: CuspForm.discriminantEquiv.rank_eq.trans (levelOne_neg_weight_rank_zero (by lia))

中文:
引理 CuspForm.rank_eq_zero_of_weight_lt_twelve
  条件: (hk : k < 12)
  证明: CuspForm.discriminantEquiv.rank_eq.trans (levelOne_neg_weight_rank_zero (by lia))

Depends on / 依赖: CuspForm, CuspForm.discriminantEquiv.rank_eq.trans, discriminantEquiv, levelOne_neg_weight_rank_zero, rank_eq
-/
lemma CuspForm.rank_eq_zero_of_weight_lt_twelve (hk : k < 12) :
    Module.rank Complex (CuspForm 𝒮ℒ k) = 0 :=
  CuspForm.discriminantEquiv.rank_eq.trans (levelOne_neg_weight_rank_zero (by lia))

/--
lemma `CuspForm.rank_eq_one_of_weight_eq_twelve` / 引理 `CuspForm.rank_eq_one_of_weight_eq_twelve`

English:
lemma CuspForm.rank_eq_one_of_weight_eq_twelve
  statement: Module.rank Complex (CuspForm 𝒮ℒ 12) = 1
  proof: by
  simpa [CuspForm.discriminantEquiv.rank_eq] using! levelOne_weight_zero_rank_one

中文:
引理 CuspForm.rank_eq_one_of_weight_eq_twelve
  结论: Module.rank Complex (CuspForm 𝒮ℒ 12) = 1
  证明: by
  simpa [CuspForm.discriminantEquiv.rank_eq] using! levelOne_weight_zero_rank_one

Depends on / 依赖: CuspForm, CuspForm.discriminantEquiv.rank_eq, discriminantEquiv, levelOne_weight_zero_rank_one, rank_eq
-/
lemma CuspForm.rank_eq_one_of_weight_eq_twelve : Module.rank Complex (CuspForm 𝒮ℒ 12) = 1 := by
  simpa [CuspForm.discriminantEquiv.rank_eq] using! levelOne_weight_zero_rank_one

/--
lemma `CuspForm.exists_smul_discriminant_of_weight_eq_twelve` / 引理 `CuspForm.exists_smul_discriminant_of_weight_eq_twelve`

English:
lemma CuspForm.exists_smul_discriminant_of_weight_eq_twelve
  given: (f : CuspForm 𝒮ℒ 12)
  proof: (finrank_eq_one_iff_of_nonzero' _ (DFunLike.ne_iff.mpr ⟨I, discriminant_ne_zero _⟩)).mp
    (Module.rank_eq_one_iff_finrank_eq_one.mp CuspForm.rank_eq_one_of_weight_eq_twelve) f

中文:
引理 CuspForm.exists_smul_discriminant_of_weight_eq_twelve
  条件: (f : CuspForm 𝒮ℒ 12)
  证明: (finrank_eq_one_iff_of_nonzero' _ (DFunLike.ne_iff.mpr ⟨I, discriminant_ne_zero _⟩)).mp
    (Module.rank_eq_one_iff_finrank_eq_one.mp CuspForm.rank_eq_one_of_weight_eq_twelve) f

Depends on / 依赖: CuspForm, CuspForm.rank_eq_one_of_weight_eq_twelve, DFunLike, DFunLike.ne_iff.mpr, Module, Module.rank_eq_one_iff_finrank_eq_one.mp, discriminant_ne_zero, finrank_eq_one_iff_of_nonzero, ne_iff, rank_eq_one_iff_finrank_eq_one, rank_eq_one_of_weight_eq_twelve
-/
lemma CuspForm.exists_smul_discriminant_of_weight_eq_twelve (f : CuspForm 𝒮ℒ 12) :
    exists c : Complex, c • CuspForm.discriminant = f :=
  (finrank_eq_one_iff_of_nonzero' _ (DFunLike.ne_iff.mpr ⟨I, discriminant_ne_zero _⟩)).mp
    (Module.rank_eq_one_iff_finrank_eq_one.mp CuspForm.rank_eq_one_of_weight_eq_twelve) f

/--
lemma `ModularForm.rank_eq_one_add_rank_cuspForm` / 引理 `ModularForm.rank_eq_one_add_rank_cuspForm`

English:
lemma ModularForm.rank_eq_one_add_rank_cuspForm
  given: {k : Nat} (hk : 3 <= k) (hk2 : Even k)
  proof: by
  suffices Module.rank Complex (ModularForm 𝒮ℒ k ⧸ cuspFormSubmodule 𝒮ℒ k) = 1 by
    rw [(CuspForm.equivCuspFormSubmodule 𝒮ℒ k).rank_eq]; rw [← Submodule.rank_quotient_add_rank (cuspFormSubmodule 𝒮ℒ k)]; rw [this]
  apply rank_eq_one (Submodule.Quotient.mk (E hk))
  · intro h
    have hE := E_qE

中文:
引理 ModularForm.rank_eq_one_add_rank_cuspForm
  条件: {k : 自然数} (hk : 3 <= k) (hk2 : Even k)
  证明: by
  suffices Module.rank Complex (ModularForm 𝒮ℒ k ⧸ cuspFormSubmodule 𝒮ℒ k) = 1 by
    rw [(CuspForm.equivCuspFormSubmodule 𝒮ℒ k).rank_eq]; rw [← Submodule.rank_quotient_add_rank (cuspFormSubmodule 𝒮ℒ k)]; rw [this]
  apply rank_eq_one (Submodule.Quotient.mk (E hk))
  · intro h
    have hE := E_qE

Depends on / 依赖: CuspForm, CuspForm.equivCuspFormSubmodule, E_qExpansion_coeff_zero, ModularForm, Module, Module.rank, Quotient, Submodule, Submodule.Quotient.forall, Submodule.Quotient.mk, Submodule.Quotient.mk_eq_zero, Submodule.rank_quotient_add_rank, cuspFormSubmodule, equivCuspFormSubmodule, hE.symm.trans, isCuspForm_iff_coeffZero_eq_zero, mk_eq_zero, one_ne_zero, qExpansion, rank_eq
-/
lemma ModularForm.rank_eq_one_add_rank_cuspForm {k : Nat} (hk : 3 <= k) (hk2 : Even k) :
    Module.rank Complex (ModularForm 𝒮ℒ k) = 1 + Module.rank Complex (CuspForm 𝒮ℒ k) := by
  suffices Module.rank Complex (ModularForm 𝒮ℒ k ⧸ cuspFormSubmodule 𝒮ℒ k) = 1 by
    rw [(CuspForm.equivCuspFormSubmodule 𝒮ℒ k).rank_eq]; rw [← Submodule.rank_quotient_add_rank (cuspFormSubmodule 𝒮ℒ k)]; rw [this]
  apply rank_eq_one (Submodule.Quotient.mk (E hk))
  · intro h
    have hE := E_qExpansion_coeff_zero hk hk2
    rw [Submodule.Quotient.mk_eq_zero] at h
exact one_ne_zero hE.symm.trans (isCuspForm_iff_coeffZero_eq_zero _).mp h
  · refine (Submodule.Quotient.forall _).mpr fun f => ⟨(qExpansion 1 f).coeff 0, ?_⟩
    rw [← Submodule.Quotient.mk_smul]; rw [Submodule.Quotient.eq]; rw [mem_cuspFormSubmodule_iff]; rw [isCuspForm_iff_coeffZero_eq_zero]; rw [FunLike.coe_sub]; rw [ModularForm.qExpansion_sub]; rw [FunLike.coe_smul]; rw [ModularForm.qExpansion_smul]; rw [map_sub]; rw [PowerSeries.coeff_smul]; rw [E_qExpansion_coeff_zero hk hk2]; rw [smul_eq_mul]; rw [mul_one]; rw [sub_self]
    all_goals simp

end RankIdentity

section DimensionFormula

namespace ModularForm

/--
lemma `levelOne_weight_four_rank_one` / 引理 `levelOne_weight_four_rank_one`

English:
lemma levelOne_weight_four_rank_one
  statement: Module.rank Complex (ModularForm 𝒮ℒ 4) = 1
  proof: (rank_eq_one_add_rank_cuspForm (by norm_num) ⟨2, rfl⟩).trans
    ((congrArg (1 + ·) (CuspForm.rank_eq_zero_of_weight_lt_twelve (by norm_num))).trans
      (by norm_cast))

中文:
引理 levelOne_weight_four_rank_one
  结论: Module.rank Complex (ModularForm 𝒮ℒ 4) = 1
  证明: (rank_eq_one_add_rank_cuspForm (by norm_num) ⟨2, rfl⟩).trans
    ((congrArg (1 + ·) (CuspForm.rank_eq_zero_of_weight_lt_twelve (by norm_num))).trans
      (by norm_cast))

Depends on / 依赖: CuspForm, CuspForm.rank_eq_zero_of_weight_lt_twelve, rank_eq_one_add_rank_cuspForm, rank_eq_zero_of_weight_lt_twelve
-/
lemma levelOne_weight_four_rank_one : Module.rank Complex (ModularForm 𝒮ℒ 4) = 1 :=
  (rank_eq_one_add_rank_cuspForm (by norm_num) ⟨2, rfl⟩).trans
    ((congrArg (1 + ·) (CuspForm.rank_eq_zero_of_weight_lt_twelve (by norm_num))).trans
      (by norm_cast))

/--
lemma `levelOne_weight_six_rank_one` / 引理 `levelOne_weight_six_rank_one`

English:
lemma levelOne_weight_six_rank_one
  statement: Module.rank Complex (ModularForm 𝒮ℒ 6) = 1
  proof: (rank_eq_one_add_rank_cuspForm (by norm_num) ⟨3, rfl⟩).trans
    ((congrArg (1 + ·) (CuspForm.rank_eq_zero_of_weight_lt_twelve (by norm_num))).trans
      (by norm_cast))

中文:
引理 levelOne_weight_six_rank_one
  结论: Module.rank Complex (ModularForm 𝒮ℒ 6) = 1
  证明: (rank_eq_one_add_rank_cuspForm (by norm_num) ⟨3, rfl⟩).trans
    ((congrArg (1 + ·) (CuspForm.rank_eq_zero_of_weight_lt_twelve (by norm_num))).trans
      (by norm_cast))

Depends on / 依赖: CuspForm, CuspForm.rank_eq_zero_of_weight_lt_twelve, rank_eq_one_add_rank_cuspForm, rank_eq_zero_of_weight_lt_twelve
-/
lemma levelOne_weight_six_rank_one : Module.rank Complex (ModularForm 𝒮ℒ 6) = 1 :=
  (rank_eq_one_add_rank_cuspForm (by norm_num) ⟨3, rfl⟩).trans
    ((congrArg (1 + ·) (CuspForm.rank_eq_zero_of_weight_lt_twelve (by norm_num))).trans
      (by norm_cast))

/--
lemma `E₄_qExpansion_coeff_one` / 引理 `E₄_qExpansion_coeff_one`

English:
lemma E₄_qExpansion_coeff_one
  statement: (qExpansion 1 E₄).coeff 1 = 240
  proof: by
  norm_num [E_qExpansion_coeff _ ⟨2, rfl⟩, show bernoulli 4 = -1 / 30 by decide +kernel]

中文:
引理 E₄_qExpansion_coeff_one
  结论: (qExpansion 1 E₄).coeff 1 = 240
  证明: by
  norm_num [E_qExpansion_coeff _ ⟨2, rfl⟩, show bernoulli 4 = -1 / 30 by decide +kernel]

Depends on / 依赖: E_qExpansion_coeff, bernoulli, kernel
-/
lemma E₄_qExpansion_coeff_one : (qExpansion 1 E₄).coeff 1 = 240 := by
  norm_num [E_qExpansion_coeff _ ⟨2, rfl⟩, show bernoulli 4 = -1 / 30 by decide +kernel]

/--
lemma `E₆_qExpansion_coeff_one` / 引理 `E₆_qExpansion_coeff_one`

English:
lemma E₆_qExpansion_coeff_one
  statement: (qExpansion 1 E₆).coeff 1 = -504
  proof: by
  norm_num [E_qExpansion_coeff _ ⟨3, rfl⟩, show bernoulli 6 = 1 / 42 by decide +kernel]

中文:
引理 E₆_qExpansion_coeff_one
  结论: (qExpansion 1 E₆).coeff 1 = -504
  证明: by
  norm_num [E_qExpansion_coeff _ ⟨3, rfl⟩, show bernoulli 6 = 1 / 42 by decide +kernel]

Depends on / 依赖: E_qExpansion_coeff, bernoulli, kernel
-/
lemma E₆_qExpansion_coeff_one : (qExpansion 1 E₆).coeff 1 = -504 := by
  norm_num [E_qExpansion_coeff _ ⟨3, rfl⟩, show bernoulli 6 = 1 / 42 by decide +kernel]

/--
lemma `eq_zero_of_pow_eq_smul` / 引理 `eq_zero_of_pow_eq_smul`

English:
lemma eq_zero_of_pow_eq_smul
  statement: {p p4 p6 : PowerSeries Complex} {c4 c6 : Complex}
  proof: by
  simp_all only [PowerSeries.coeff_zero_eq_constantCoeff]
  let D := (c4 • p4) ^ 3 - (c6 • p6) ^ 2
  have hD0 : D.coeff 0 = c4 ^ 3 - c6 ^ 2 := by simp [D, hp4_0, hp6_0]
  have hD1 : D.coeff 1 = 720 * c4 ^ 3 + 1008 * c6 ^ 2 := by
    simp [D, pow_succ, PowerSeries.coeff_mul, Finset.Nat.antidiagona

中文:
引理 eq_zero_of_pow_eq_smul
  结论: {p p4 p6 : PowerSeries Complex} {c4 c6 : Complex}
  证明: by
  simp_all only [PowerSeries.coeff_zero_eq_constantCoeff]
  let D := (c4 • p4) ^ 3 - (c6 • p6) ^ 2
  have hD0 : D.coeff 0 = c4 ^ 3 - c6 ^ 2 := by simp [D, hp4_0, hp6_0]
  have hD1 : D.coeff 1 = 720 * c4 ^ 3 + 1008 * c6 ^ 2 := by
    simp [D, pow_succ, PowerSeries.coeff_mul, Finset.Nat.antidiagona
-/
private lemma eq_zero_of_pow_eq_smul {p p4 p6 : PowerSeries Complex} {c4 c6 : Complex}
    (hp4_0 : p4.coeff 0 = 1) (hp6_0 : p6.coeff 0 = 1) (hp4_1 : p4.coeff 1 = 240)
    (hp6_1 : p6.coeff 1 = -504) (hqc4 : c4 • p4 = p ^ 2)
    (hqc6 : c6 • p6 = p ^ 3) : p = 0 := by
  simp_all only [PowerSeries.coeff_zero_eq_constantCoeff]
  let D := (c4 • p4) ^ 3 - (c6 • p6) ^ 2
  have hD0 : D.coeff 0 = c4 ^ 3 - c6 ^ 2 := by simp [D, hp4_0, hp6_0]
  have hD1 : D.coeff 1 = 720 * c4 ^ 3 + 1008 * c6 ^ 2 := by
    simp [D, pow_succ, PowerSeries.coeff_mul, Finset.Nat.antidiagonal_succ]
    grind
  grind [pow_eq_zero_iff, zero_smul]

/--
lemma `weight_two_qExpansion_eq_zero` / 引理 `weight_two_qExpansion_eq_zero`

English:
lemma weight_two_qExpansion_eq_zero
  given: (f : ModularForm 𝒮ℒ 2)
  statement: qExpansion 1 f = 0
  proof: by
  obtain ⟨c4, hc4⟩ : exists c4, c4 • E₄ = f.mul f :=
    (finrank_eq_one_iff_of_nonzero' E₄ (E_ne_zero _ ⟨2, rfl⟩)).mp
      (Module.rank_eq_one_iff_finrank_eq_one.mp levelOne_weight_four_rank_one) _
  obtain ⟨c6, hc6⟩ : exists c6, c6 • E₆ = (f.mul f).mul f :=
    (finrank_eq_one_iff_of_nonzero' 

中文:
引理 weight_two_qExpansion_eq_zero
  条件: (f : ModularForm 𝒮ℒ 2)
  结论: qExpansion 1 f = 0
  证明: by
  obtain ⟨c4, hc4⟩ : exists c4, c4 • E₄ = f.mul f :=
    (finrank_eq_one_iff_of_nonzero' E₄ (E_ne_zero _ ⟨2, rfl⟩)).mp
      (Module.rank_eq_one_iff_finrank_eq_one.mp levelOne_weight_four_rank_one) _
  obtain ⟨c6, hc6⟩ : exists c6, c6 • E₆ = (f.mul f).mul f :=
    (finrank_eq_one_iff_of_nonzero' 
-/
private lemma weight_two_qExpansion_eq_zero (f : ModularForm 𝒮ℒ 2) : qExpansion 1 f = 0 := by
  obtain ⟨c4, hc4⟩ : exists c4, c4 • E₄ = f.mul f :=
    (finrank_eq_one_iff_of_nonzero' E₄ (E_ne_zero _ ⟨2, rfl⟩)).mp
      (Module.rank_eq_one_iff_finrank_eq_one.mp levelOne_weight_four_rank_one) _
  obtain ⟨c6, hc6⟩ : exists c6, c6 • E₆ = (f.mul f).mul f :=
    (finrank_eq_one_iff_of_nonzero' E₆ (E_ne_zero _ ⟨3, rfl⟩)).mp
      (Module.rank_eq_one_iff_finrank_eq_one.mp levelOne_weight_six_rank_one) _
  have hqc4 : c4 • qExpansion 1 (E₄ : ℍ -> Complex) = qExpansion 1 (f : ℍ -> Complex) ^ 2 := by
    rw [pow_two]; rw [← ModularForm.qExpansion_mul one_pos one_mem_strictPeriods_SL f f]; rw [← ModularForm.qExpansion_smul one_pos one_mem_strictPeriods_SL c4 E₄]; rw [show (c4 • E₄ : ℍ -> Complex) = (f.mul f) from congrArg DFunLike.coe hc4]
  have hqc6 : c6 • qExpansion 1 E₆ = qExpansion 1 (f : ℍ -> Complex) ^ 3 := by
    rw [pow_succ]; rw [pow_two]; rw [← ModularForm.qExpansion_mul one_pos one_mem_strictPeriods_SL f f]; rw [← ModularForm.qExpansion_mul one_pos one_mem_strictPeriods_SL (f.mul f) f]; rw [← ModularForm.qExpansion_smul one_pos one_mem_strictPeriods_SL c6 E₆]; rw [show (c6 • E₆ : ℍ -> Complex) = (f.mul f).mul f from congrArg DFunLike.coe hc6]
  exact eq_zero_of_pow_eq_smul (E_qExpansion_coeff_zero _ ⟨2, rfl⟩)
    (E_qExpansion_coeff_zero _ ⟨3, rfl⟩) E₄_qExpansion_coeff_one E₆_qExpansion_coeff_one hqc4 hqc6

/--
theorem `levelOne_weight_two_rank_zero` / 定理 `levelOne_weight_two_rank_zero`

English:
theorem levelOne_weight_two_rank_zero
  statement: Module.rank Complex (ModularForm 𝒮ℒ 2) = 0
  proof: by
  simpa [rank_zero_iff_forall_zero, ModularForm.qExpansion_eq_zero_iff]
    using weight_two_qExpansion_eq_zero

中文:
定理 levelOne_weight_two_rank_zero
  结论: Module.rank Complex (ModularForm 𝒮ℒ 2) = 0
  证明: by
  simpa [rank_zero_iff_forall_zero, ModularForm.qExpansion_eq_zero_iff]
    using weight_two_qExpansion_eq_zero

Depends on / 依赖: ModularForm, ModularForm.qExpansion_eq_zero_iff, qExpansion_eq_zero_iff, rank_zero_iff_forall_zero, weight_two_qExpansion_eq_zero
-/
theorem levelOne_weight_two_rank_zero : Module.rank Complex (ModularForm 𝒮ℒ 2) = 0 := by
  simpa [rank_zero_iff_forall_zero, ModularForm.qExpansion_eq_zero_iff]
    using weight_two_qExpansion_eq_zero

/--
theorem `dimension_level_one` / 定理 `dimension_level_one`

English:
theorem dimension_level_one
  given: (k : Nat) (hk2 : Even k)
  proof: by
  induction k using Nat.strong_induction_on with | h k ihn =>
  have : k < 3 ∨ (3 <= k ∧ k < 12) ∨ 12 <= k := by grind
  rcases this with hk | hk | hk
  · -- `k < 3`: direct case-by-case check
    interval_cases k
    · simpa using! levelOne_weight_zero_rank_one
    · grind
    · simpa [Nat.ModEq

中文:
定理 dimension_level_one
  条件: (k : 自然数) (hk2 : Even k)
  证明: by
  induction k using Nat.strong_induction_on with | h k ihn =>
  have : k < 3 ∨ (3 <= k ∧ k < 12) ∨ 12 <= k := by grind
  rcases this with hk | hk | hk
  · -- `k < 3`: direct case-by-case check
    interval_cases k
    · simpa using! levelOne_weight_zero_rank_one
    · grind
    · simpa [Nat.ModEq

Depends on / 依赖: CuspForm, CuspForm.discriminantEquiv.rank_eq, Nat.ModEq, Nat.strong_induction_on, decomposition, direct, discriminantEquiv, interval_cases, levelOne_neg_weight_ra, levelOne_weight_two_rank_zero, levelOne_weight_zero_rank_one, rank_eq, rank_eq_one_add_rank_cuspForm, strong_induction_on, weight
-/
theorem dimension_level_one (k : Nat) (hk2 : Even k) :
    Module.rank Complex (ModularForm 𝒮ℒ k) =
      if k ≡ 2 [MOD 12] then k / 12 else k / 12 + 1 := by
  induction k using Nat.strong_induction_on with | h k ihn =>
  have : k < 3 ∨ (3 <= k ∧ k < 12) ∨ 12 <= k := by grind
  rcases this with hk | hk | hk
  · -- `k < 3`: direct case-by-case check
    interval_cases k
    · simpa using! levelOne_weight_zero_rank_one
    · grind
    · simpa [Nat.ModEq] using levelOne_weight_two_rank_zero
  · -- `3 ≤ k < 12`: rank decomposition + the weight `k - 12` space is zero
    rw [rank_eq_one_add_rank_cuspForm hk.1 hk2]; rw [CuspForm.discriminantEquiv.rank_eq]; rw [levelOne_neg_weight_rank_zero (by lia)]
    have : k in (Finset.Icc 3 11).filter Even := by grind
    fin_cases this <;> simp [Nat.ModEq]
  · -- `12 ≤ k`: rank decomposition + induction hypothesis at weight `k - 12`
    rw [rank_eq_one_add_rank_cuspForm (by lia) hk2]; rw [CuspForm.discriminantEquiv.rank_eq]; rw [show ((k : Int) - 12 : Int) = ((k - 12 : Nat) : Int) by lia]; rw [ihn (k - 12) (by lia) (by grind)]
    simp only [Nat.ModEq, show k / 12 = (k - 12) / 12 + 1 by lia,
      show (k - 12) % 12 = k % 12 by lia]
    split_ifs <;> grind

instance (k : Int) : FiniteDimensional Complex (ModularForm 𝒮ℒ k) := by
  rw [FiniteDimensional]; rw [← Module.rank_lt_aleph0_iff]
  rcases lt_or_ge k 0 with hk_neg | hk_nonneg
  · rw [levelOne_neg_weight_rank_zero hk_neg]
    exact Cardinal.aleph0_pos
  rcases Int.even_or_odd k with hk_even | hk_odd
  · lift k to Nat using hk_nonneg
    rw [dimension_level_one k (mod_cast hk_even)]
    split_ifs <;> exact_mod_cast Cardinal.natCast_lt_aleph0
  · rw [levelOne_odd_weight_rank_zero hk_odd]
    exact Cardinal.aleph0_pos

/--
theorem `sturm_bound_levelOne_nat` / 定理 `sturm_bound_levelOne_nat`

English:
theorem sturm_bound_levelOne_nat
  statement: {k : Nat} {f : ModularForm 𝒮ℒ (k : Int)}
  proof: by
  induction k using Nat.strong_induction_on with | _ k ih =>
  have h0 : (qExpansion 1 f).coeff 0 = 0 :=
    PowerSeries.coeff_of_lt_order _ ((Nat.cast_nonneg _).trans_lt h)
  suffices CuspForm.discriminantEquiv (toCuspForm f h0) = 0 by
    simpa [CuspForm.discriminantEquiv.map_eq_zero_iff, DFunL

中文:
定理 sturm_bound_levelOne_nat
  结论: {k : 自然数} {f : ModularForm 𝒮ℒ (k : 整数)}
  证明: by
  induction k using Nat.strong_induction_on with | _ k ih =>
  have h0 : (qExpansion 1 f).coeff 0 = 0 :=
    PowerSeries.coeff_of_lt_order _ ((Nat.cast_nonneg _).trans_lt h)
  suffices CuspForm.discriminantEquiv (toCuspForm f h0) = 0 by
    simpa [CuspForm.discriminantEquiv.map_eq_zero_iff, DFunL

Depends on / 依赖: CuspForm, CuspForm.discriminantEquiv, CuspForm.discriminantEquiv.map_eq_zero_iff, DFunLike, DFunLike.ext_iff, Nat.cast_nonneg, Nat.strong_induction_on, PowerSeries, PowerSeries.coeff_of_lt_order, cast_nonneg, coeff_of_lt_order, discriminantEquiv, ext_iff, levelOne_neg_weight_rank_zero, lt_or_ge, map_eq_zero_iff, mcast_eq_zero_iff, qExpansion, rank_zero_iff_forall_zero, rank_zero_iff_forall_zero.mp
-/
theorem sturm_bound_levelOne_nat {k : Nat} {f : ModularForm 𝒮ℒ (k : Int)}
    (h : (↑(k / 12) : Nat∞) < (qExpansion 1 f).order) : f = 0 := by
  induction k using Nat.strong_induction_on with | _ k ih =>
  have h0 : (qExpansion 1 f).coeff 0 = 0 :=
    PowerSeries.coeff_of_lt_order _ ((Nat.cast_nonneg _).trans_lt h)
  suffices CuspForm.discriminantEquiv (toCuspForm f h0) = 0 by
    simpa [CuspForm.discriminantEquiv.map_eq_zero_iff, DFunLike.ext_iff]
  rcases lt_or_ge k 12 with hk12 | hk12
  · apply rank_zero_iff_forall_zero.mp (levelOne_neg_weight_rank_zero (by lia))
  · rw [← mcast_eq_zero_iff (b := ↑(k - 12)) (by lia) rfl]
    refine ih (k - 12) (by lia) ?_
    have hsucc : k / 12 = (k - 12) / 12 + 1 := by lia
    rw [qExpansion_eq_qExpansion_discriminant_mul f h0]; rw [PowerSeries.order_mul]; rw [discriminant_qExpansion_order]; rw [add_comm]; rw [hsucc]; rw [Nat.cast_add]; rw [Nat.cast_one] at h
    exact (ENat.add_lt_add_iff_right (ENat.natCast_ne_top 1)).mp h

/--
theorem `sturm_bound_levelOne` / 定理 `sturm_bound_levelOne`

English:
theorem sturm_bound_levelOne
  statement: {k : Int} {f : ModularForm 𝒮ℒ k}
  proof: by
  rcases lt_or_ge k 0 with hk | hk
  · exact rank_zero_iff_forall_zero.mp (levelOne_neg_weight_rank_zero hk) f
  · lift k to Nat using hk
    exact sturm_bound_levelOne_nat (mod_cast h)

中文:
定理 sturm_bound_levelOne
  结论: {k : 整数} {f : ModularForm 𝒮ℒ k}
  证明: by
  rcases lt_or_ge k 0 with hk | hk
  · exact rank_zero_iff_forall_zero.mp (levelOne_neg_weight_rank_zero hk) f
  · lift k to Nat using hk
    exact sturm_bound_levelOne_nat (mod_cast h)

Depends on / 依赖: levelOne_neg_weight_rank_zero, lt_or_ge, mod_cast, rank_zero_iff_forall_zero, rank_zero_iff_forall_zero.mp, sturm_bound_levelOne_nat
-/
theorem sturm_bound_levelOne {k : Int} {f : ModularForm 𝒮ℒ k}
    (h : (↑(k.toNat / 12) : Nat∞) < (qExpansion 1 f).order) : f = 0 := by
  rcases lt_or_ge k 0 with hk | hk
  · exact rank_zero_iff_forall_zero.mp (levelOne_neg_weight_rank_zero hk) f
  · lift k to Nat using hk
    exact sturm_bound_levelOne_nat (mod_cast h)

end ModularForm

end DimensionFormula
