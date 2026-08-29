/-
Copyright (c) 2024 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
module

public import Mathlib.NumberTheory.ModularForms.SlashInvariantForms
public import Mathlib.NumberTheory.ModularForms.CongruenceSubgroups
public import Mathlib.NumberTheory.ModularForms.Cusps

/-!
# Identities of ModularForms and SlashInvariantForms

Collection of useful identities of modular forms.
-/

public section

noncomputable section

open ModularForm UpperHalfPlane Matrix CongruenceSubgroup Matrix.SpecialLinearGroup MatrixGroups

namespace SlashInvariantForm

/--
theorem `vAdd_apply_of_mem_strictPeriods` / 定理 `vAdd_apply_of_mem_strictPeriods`

English:
theorem vAdd_apply_of_mem_strictPeriods
  statement: {Γ : Subgroup (GL (Fin 2) Real)} {k : Int}
  proof: by
  rw [← congr_fun (slash_action_eqn f _ <| Γ.mem_strictPeriods_iff.mp hH) τ]
  suffices GeneralLinearGroup.upperRightHom h • τ = h +ᵥ τ by
    simp_rw [slash_def, this]
    simp [σ, denom, GeneralLinearGroup.val_det_apply, denom]
  ext
  simp [σ, num, denom, coe_vadd, UpperHalfPlane.coe_smul, num, add_comm]

中文:
定理 vAdd_apply_of_mem_strictPeriods
  结论: {Γ : 子群 (GL (有限集 2) 实数)} {k : 整数}
  证明: by
  rw [← congr_fun (slash_action_eqn f _ <| Γ.mem_strictPeriods_iff.mp hH) τ]
  suffices GeneralLinearGroup.upperRightHom h • τ = h +ᵥ τ by
    simp_rw [slash_def, this]
    simp [σ, denom, GeneralLinearGroup.val_det_apply, denom]
  ext
  simp [σ, num, denom, coe_vadd, UpperHalfPlane.coe_smul, num, add_comm]

Depends on / 依赖: GeneralLinearGroup, GeneralLinearGroup.upperRightHom, GeneralLinearGroup.val_det_apply, UpperHalfPlane, UpperHalfPlane.coe_smul, add_comm, coe_smul, coe_vadd, congr_fun, mem_strictPeriods_iff, mem_strictPeriods_iff.mp, simp_rw, slash_action_eqn, slash_def, upperRightHom, val_det_apply
-/
theorem vAdd_apply_of_mem_strictPeriods {Γ : Subgroup (GL (Fin 2) Real)} {k : Int}
    {F : Type*} [FunLike F ℍ Complex] [SlashInvariantFormClass F Γ k]
    (f : F) (τ : ℍ) {h : Real} (hH : h in Γ.strictPeriods) :
    f (h +ᵥ τ) = f τ := by
  rw [← congr_fun (slash_action_eqn f _ <| Γ.mem_strictPeriods_iff.mp hH) τ]
  suffices GeneralLinearGroup.upperRightHom h • τ = h +ᵥ τ by
    simp_rw [slash_def, this]
    simp [σ, denom, GeneralLinearGroup.val_det_apply, denom]
  ext
  simp [σ, num, denom, coe_vadd, UpperHalfPlane.coe_smul, num, add_comm]

/--
theorem `vAdd_width_periodic` / 定理 `vAdd_width_periodic`

English:
theorem vAdd_width_periodic
  given: (N : Nat) (k n : Int) (f : SlashInvariantForm (Gamma N) k) (z : ℍ)
  proof: by
  apply vAdd_apply_of_mem_strictPeriods
  simp [strictPeriods_Gamma, AddSubgroup.mem_zmultiples_iff, mul_comm]

中文:
定理 vAdd_width_periodic
  条件: (N : 自然数) (k n : 整数) (f : 斜不变形式 (Gamma N) k) (z : ℍ)
  证明: by
  apply vAdd_apply_of_mem_strictPeriods
  simp [strictPeriods_Gamma, AddSubgroup.mem_zmultiples_iff, mul_comm]

Depends on / 依赖: AddSubgroup, AddSubgroup.mem_zmultiples_iff, mem_zmultiples_iff, mul_comm, strictPeriods_Gamma, vAdd_apply_of_mem_strictPeriods
-/
theorem vAdd_width_periodic (N : Nat) (k n : Int) (f : SlashInvariantForm (Gamma N) k) (z : ℍ) :
    f ((N * n : Real) +ᵥ z) = f z := by
  apply vAdd_apply_of_mem_strictPeriods
  simp [strictPeriods_Gamma, AddSubgroup.mem_zmultiples_iff, mul_comm]

/--
theorem `T_zpow_width_invariant` / 定理 `T_zpow_width_invariant`

English:
theorem T_zpow_width_invariant
  given: (N : Nat) (k n : Int) (f : SlashInvariantForm (Gamma N) k) (z : ℍ)
  proof: by
  rw [modular_T_zpow_smul z (N * n)]
  simpa only [Int.cast_mul, Int.cast_natCast] using vAdd_width_periodic N k n f z

中文:
定理 T_zpow_width_invariant
  条件: (N : 自然数) (k n : 整数) (f : 斜不变形式 (Gamma N) k) (z : ℍ)
  证明: by
  rw [modular_T_zpow_smul z (N * n)]
  simpa only [Int.cast_mul, Int.cast_natCast] using vAdd_width_periodic N k n f z

Depends on / 依赖: Int.cast_mul, Int.cast_natCast, cast_mul, cast_natCast, modular_T_zpow_smul, vAdd_width_periodic
-/
theorem T_zpow_width_invariant (N : Nat) (k n : Int) (f : SlashInvariantForm (Gamma N) k) (z : ℍ) :
    f (((ModularGroup.T ^ (N * n))) • z) = f z := by
  rw [modular_T_zpow_smul z (N * n)]
  simpa only [Int.cast_mul, Int.cast_natCast] using vAdd_width_periodic N k n f z

set_option backward.isDefEq.respectTransparency.types false in
/--
lemma `slash_S_apply` / 引理 `slash_S_apply`

English:
lemma slash_S_apply
  given: (f : ℍ -> Complex) (k : Int) (z : ℍ)
  proof: by
  rw [SL_slash_apply]; rw [modular_S_smul]
  simp [ModularGroup.S, denom]

中文:
引理 slash_S_apply
  条件: (f : ℍ -> 复形) (k : 整数) (z : ℍ)
  证明: by
  rw [SL_slash_apply]; rw [modular_S_smul]
  simp [ModularGroup.S, denom]

Depends on / 依赖: ModularGroup, ModularGroup.S, SL_slash_apply, modular_S_smul
-/
lemma slash_S_apply (f : ℍ -> Complex) (k : Int) (z : ℍ) :
    (f ∣[k] ModularGroup.S) z = f (.mk _ z.im_inv_neg_coe_pos) * z ^ (-k) := by
  rw [SL_slash_apply]; rw [modular_S_smul]
  simp [ModularGroup.S, denom]

section Generators

/--
theorem `slash_action_generators` / 定理 `slash_action_generators`

English:
theorem slash_action_generators
  statement: {f : ℍ -> Complex} {Γ : Subgroup (GL (Fin 2) Real)}
  proof: by
  constructor <;> intro h γ hγ
  · exact h γ (hΓ ▸ Subgroup.mem_closure_of_mem hγ)
  · apply Subgroup.closure_induction (p := fun γ _ => f ∣[k] γ = f) h (by simp)
    · simp +contextual [SlashAction.slash_mul]
    · intro x hx hf
      rw [← hf]; rw [← SlashAction.slash_mul]
      simp [hf]
    · simpa [← hΓ]

中文:
定理 slash_action_generators
  结论: {f : ℍ -> 复形} {Γ : 子群 (GL (有限集 2) 实数)}
  证明: by
  constructor <;> intro h γ hγ
  · exact h γ (hΓ ▸ Subgroup.mem_closure_of_mem hγ)
  · apply Subgroup.closure_induction (p := fun γ _ => f ∣[k] γ = f) h (by simp)
    · simp +contextual [SlashAction.slash_mul]
    · intro x hx hf
      rw [← hf]; rw [← SlashAction.slash_mul]
      simp [hf]
    · simpa [← hΓ]

Depends on / 依赖: SlashAction, SlashAction.slash_mul, Subgroup, Subgroup.closure_induction, Subgroup.mem_closure_of_mem, closure_induction, contextual, mem_closure_of_mem, slash_mul
-/
theorem slash_action_generators {f : ℍ -> Complex} {Γ : Subgroup (GL (Fin 2) Real)}
    {s : Set (GL (Fin 2) Real)} (hΓ : Γ = Subgroup.closure s) {k : Int} :
    (forall γ in Γ, f ∣[k] γ = f) ↔ (forall γ in s, f ∣[k] γ = f) := by
  constructor <;> intro h γ hγ
  · exact h γ (hΓ ▸ Subgroup.mem_closure_of_mem hγ)
  · apply Subgroup.closure_induction (p := fun γ _ => f ∣[k] γ = f) h (by simp)
    · simp +contextual [SlashAction.slash_mul]
    · intro x hx hf
      rw [← hf]; rw [← SlashAction.slash_mul]
      simp [hf]
    · simpa [← hΓ]

end Generators

end SlashInvariantForm
