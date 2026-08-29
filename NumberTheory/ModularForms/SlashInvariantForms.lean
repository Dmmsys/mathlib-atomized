/-
Copyright (c) 2022 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
module

public import Mathlib.NumberTheory.ModularForms.ArithmeticSubgroups
public import Mathlib.NumberTheory.ModularForms.SlashActions

/-!
# Slash invariant forms

This file defines functions that are invariant under a `SlashAction` which forms the basis for
defining `ModularForm` and `CuspForm`. We prove several instances for such spaces, in particular
that they form a module over `ℝ`, and over `ℂ` if the group is contained in `SL(2, ℝ)`.
-/

@[expose] public section

open Complex UpperHalfPlane ModularForm

open scoped MatrixGroups

noncomputable section

section SlashInvariantForms

open ModularForm

variable (F : Type*) (Γ : outParam <| Subgroup (GL (Fin 2) Real)) (k : outParam Int)

/--
Definition of `SlashInvariantForm` / `SlashInvariantForm` 的定义

English:
structure SlashInvariantForm
  parameters: where
  axioms and operations (2):
    - toFun : ℍ -> Complex
    - slash_action_eq' : forall γ in Γ, toFun ∣[k] γ = toFun

中文:
结构 SlashInvariantForm
  参数: where
  公理与运算 (2 个):
    - toFun : ℍ -> Complex
    - slash_action_eq' : 对任意 γ in Γ, toFun ∣[k] γ = toFun
-/
structure SlashInvariantForm where
  /-- The underlying function `ℍ → ℂ`.

  Do NOT use directly. Use the coercion instead. -/
  toFun : ℍ -> Complex
  slash_action_eq' : forall γ in Γ, toFun ∣[k] γ = toFun

/--
Definition of `SlashInvariantFormClass` / `SlashInvariantFormClass` 的定义

English:
class SlashInvariantFormClass
  parameters: [FunLike F ℍ Complex]
  axioms and operations (1):
    - slash_action_eq : forall (f : F), forall γ in Γ, (f : ℍ -> Complex) ∣[k] γ = f

中文:
类 SlashInvariantFormClass
  参数: [FunLike F ℍ Complex]
  公理与运算 (1 个):
    - slash_action_eq : 对任意 (f : F), 对任意 γ in Γ, (f : ℍ -> Complex) ∣[k] γ = f
-/
class SlashInvariantFormClass [FunLike F ℍ Complex] : Prop where
  slash_action_eq : forall (f : F), forall γ in Γ, (f : ℍ -> Complex) ∣[k] γ = f

instance (priority := 100) SlashInvariantForm.funLike :
    FunLike (SlashInvariantForm Γ k) ℍ Complex where
  coe := SlashInvariantForm.toFun
  coe_injective f g h := by cases f; cases g; congr

/--
Definition of `SlashInvariantForm.Simps.coe` / `SlashInvariantForm.Simps.coe` 的定义

English:
definition SlashInvariantForm.Simps.coe
  signature: (f : SlashInvariantForm Γ k)
  body: f

initialize_simps_projections SlashInvariantForm (toFun -> coe, as_prefix coe)

中文:
定义 SlashInvariantForm.Simps.coe
  签名: (f : SlashInvariantForm Γ k)
  定义体: f

initialize_simps_projections SlashInvariantForm (toFun -> coe, as_prefix coe)
-/
def SlashInvariantForm.Simps.coe (f : SlashInvariantForm Γ k) : ℍ -> Complex := f

initialize_simps_projections SlashInvariantForm (toFun -> coe, as_prefix coe)

instance (priority := 100) SlashInvariantFormClass.slashInvariantForm :
    SlashInvariantFormClass (SlashInvariantForm Γ k) Γ k where
  slash_action_eq := SlashInvariantForm.slash_action_eq'

variable {F Γ k}

@[simp]
/--
theorem `SlashInvariantForm.toFun_eq_coe` / 定理 `SlashInvariantForm.toFun_eq_coe`

English:
theorem SlashInvariantForm.toFun_eq_coe
  given: {f : SlashInvariantForm Γ k}
  statement: f.toFun = (f : ℍ -> Complex)
  proof: rfl

@[simp]

中文:
定理 SlashInvariantForm.toFun_eq_coe
  条件: {f : SlashInvariantForm Γ k}
  结论: f.toFun = (f : ℍ -> Complex)
  证明: rfl

@[simp]
-/
theorem SlashInvariantForm.toFun_eq_coe {f : SlashInvariantForm Γ k} : f.toFun = (f : ℍ -> Complex) :=
  rfl

@[simp]
/--
theorem `SlashInvariantForm.coe_mk` / 定理 `SlashInvariantForm.coe_mk`

English:
theorem SlashInvariantForm.coe_mk
  given: (f : ℍ -> Complex) (hf : forall γ in Γ, f ∣[k] γ = f)
  statement: ⇑(mk f hf) = f
  proof: rfl

@[ext]

中文:
定理 SlashInvariantForm.coe_mk
  条件: (f : ℍ -> Complex) (hf : 对任意 γ in Γ, f ∣[k] γ = f)
  结论: ⇑(mk f hf) = f
  证明: rfl

@[ext]
-/
theorem SlashInvariantForm.coe_mk (f : ℍ -> Complex) (hf : forall γ in Γ, f ∣[k] γ = f) : ⇑(mk f hf) = f := rfl

@[ext]
/--
theorem `SlashInvariantForm.ext` / 定理 `SlashInvariantForm.ext`

English:
theorem SlashInvariantForm.ext
  given: {f g : SlashInvariantForm Γ k} (h : forall x, f x = g x)
  statement: f = g
  proof: DFunLike.ext f g h

中文:
定理 SlashInvariantForm.ext
  条件: {f g : SlashInvariantForm Γ k} (h : 对任意 x, f x = g x)
  结论: f = g
  证明: DFunLike.ext f g h

Depends on / 依赖: DFunLike, DFunLike.ext
-/
theorem SlashInvariantForm.ext {f g : SlashInvariantForm Γ k} (h : forall x, f x = g x) : f = g :=
  DFunLike.ext f g h

/--
Definition of `SlashInvariantForm.copy` / `SlashInvariantForm.copy` 的定义

English:
definition SlashInvariantForm.copy
  signature: (f : SlashInvariantForm Γ k) (f' : ℍ -> Complex) (h : f' = ⇑f)
  body: f'
  slash_action_eq' := h.symm ▸ f.slash_action_eq'

中文:
定义 SlashInvariantForm.copy
  签名: (f : SlashInvariantForm Γ k) (f' : ℍ -> Complex) (h : f' = ⇑f)
  定义体: f'
  slash_action_eq' := h.symm ▸ f.slash_action_eq'
-/
protected def SlashInvariantForm.copy (f : SlashInvariantForm Γ k) (f' : ℍ -> Complex) (h : f' = ⇑f) :
    SlashInvariantForm Γ k where
  toFun := f'
  slash_action_eq' := h.symm ▸ f.slash_action_eq'

end SlashInvariantForms

namespace SlashInvariantForm

variable {F : Type*} {Γ : Subgroup <| GL (Fin 2) Real} {k : Int} [FunLike F ℍ Complex]

/--
theorem `slash_action_eqn` / 定理 `slash_action_eqn`

English:
theorem slash_action_eqn
  given: [SlashInvariantFormClass F Γ k] (f : F) (γ) (hγ : γ in Γ)
  proof: SlashInvariantFormClass.slash_action_eq f γ hγ

中文:
定理 slash_action_eqn
  条件: [SlashInvariantFormClass F Γ k] (f : F) (γ) (hγ : γ in Γ)
  证明: SlashInvariantFormClass.slash_action_eq f γ hγ

Depends on / 依赖: SlashInvariantFormClass, SlashInvariantFormClass.slash_action_eq, slash_action_eq
-/
theorem slash_action_eqn [SlashInvariantFormClass F Γ k] (f : F) (γ) (hγ : γ in Γ) :
    ↑f ∣[k] γ = ⇑f :=
  SlashInvariantFormClass.slash_action_eq f γ hγ

/--
theorem `slash_action_eqn'` / 定理 `slash_action_eqn'`

English:
theorem slash_action_eqn'
  statement: {k : Int} [Γ.HasDetOne] [SlashInvariantFormClass F Γ k]
  proof: by
  have : f (γ • z) = f z * denom γ z ^ k := by
    simpa [slash_def, σ, mul_inv_eq_iff_eq_mul₀ (zpow_ne_zero _ (denom_ne_zero _ _)),
      Subgroup.HasDetOne.det_eq hγ] using congr_fun (slash_action_eqn f γ hγ) z
  rw [this]; rw [denom]; rw [mul_comm]

中文:
定理 slash_action_eqn'
  结论: {k : 整数} [Γ.HasDetOne] [SlashInvariantFormClass F Γ k]
  证明: by
  have : f (γ • z) = f z * denom γ z ^ k := by
    simpa [slash_def, σ, mul_inv_eq_iff_eq_mul₀ (zpow_ne_zero _ (denom_ne_zero _ _)),
      Subgroup.HasDetOne.det_eq hγ] using congr_fun (slash_action_eqn f γ hγ) z
  rw [this]; rw [denom]; rw [mul_comm]

Depends on / 依赖: HasDetOne, Subgroup, Subgroup.HasDetOne.det_eq, congr_fun, denom_ne_zero, det_eq, mul_comm, slash_action_eqn, slash_def, zpow_ne_zero
-/
theorem slash_action_eqn' {k : Int} [Γ.HasDetOne] [SlashInvariantFormClass F Γ k]
    (f : F) {γ} (hγ : γ in Γ) (z : ℍ) :
    f (γ • z) = (γ 1 0 * z + γ 1 1) ^ k * f z := by
  have : f (γ • z) = f z * denom γ z ^ k := by
    simpa [slash_def, σ, mul_inv_eq_iff_eq_mul₀ (zpow_ne_zero _ (denom_ne_zero _ _)),
      Subgroup.HasDetOne.det_eq hγ] using congr_fun (slash_action_eqn f γ hγ) z
  rw [this]; rw [denom]; rw [mul_comm]

/--
theorem `slash_action_eqn''` / 定理 `slash_action_eqn''`

English:
theorem slash_action_eqn''
  statement: {k : Int} [Γ.HasDetOne] [SlashInvariantFormClass F Γ k]
  proof: SlashInvariantForm.slash_action_eqn' f hγ z

中文:
定理 slash_action_eqn''
  结论: {k : 整数} [Γ.HasDetOne] [SlashInvariantFormClass F Γ k]
  证明: SlashInvariantForm.slash_action_eqn' f hγ z

Depends on / 依赖: SlashInvariantForm, SlashInvariantForm.slash_action_eqn, slash_action_eqn
-/
theorem slash_action_eqn'' {k : Int} [Γ.HasDetOne] [SlashInvariantFormClass F Γ k]
    (f : F) {γ} (hγ : γ in Γ) (z : ℍ) :
    f (γ • z) = (denom γ z) ^ k * f z :=
  SlashInvariantForm.slash_action_eqn' f hγ z

/--
theorem `slash_action_eqn_SL''` / 定理 `slash_action_eqn_SL''`

English:
theorem slash_action_eqn_SL''
  statement: {k : Int} {Γ : Subgroup SL(2, Int)} [SlashInvariantFormClass F Γ k]
  proof: SlashInvariantForm.slash_action_eqn' f (by simpa using hγ) z

中文:
定理 slash_action_eqn_SL''
  结论: {k : 整数} {Γ : Subgroup SL(2, 整数)} [SlashInvariantFormClass F Γ k]
  证明: SlashInvariantForm.slash_action_eqn' f (by simpa using hγ) z

Depends on / 依赖: SlashInvariantForm, SlashInvariantForm.slash_action_eqn, slash_action_eqn
-/
theorem slash_action_eqn_SL'' {k : Int} {Γ : Subgroup SL(2, Int)} [SlashInvariantFormClass F Γ k]
    (f : F) {γ} (hγ : γ in Γ) (z : ℍ) :
    f (γ • z) = (denom γ z) ^ k * f z :=
  SlashInvariantForm.slash_action_eqn' f (by simpa using hγ) z


/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [SlashInvariantFormClass
  signature: F Γ k] : CoeTC F (SlashInvariantForm Γ k)
  body: ⟨fun f => { slash_action_eq' := slash_action_eqn f, .. }⟩

中文:
实例 [SlashInvariantFormClass
  签名: F Γ k] : CoeTC F (SlashInvariantForm Γ k)
  定义体: ⟨fun f => { slash_action_eq' := slash_action_eqn f, .. }⟩

Depends on / 依赖: slash_action_eq, slash_action_eqn
-/
instance [SlashInvariantFormClass F Γ k] : CoeTC F (SlashInvariantForm Γ k) :=
  ⟨fun f => { slash_action_eq' := slash_action_eqn f, .. }⟩

/--
Instance `instAdd` / 实例 `instAdd`

English:
instance instAdd
  signature: : Add (SlashInvariantForm Γ k)
  body: ⟨fun f g =>
    { toFun := f + g
      slash_action_eq' := fun γ hγ => by
        rw [SlashAction.add_slash]; rw [slash_action_eqn f γ hγ]; rw [slash_action_eqn g γ hγ] }⟩

中文:
实例 instAdd
  签名: : Add (SlashInvariantForm Γ k)
  定义体: ⟨fun f g =>
    { toFun := f + g
      slash_action_eq' := fun γ hγ => by
        rw [SlashAction.add_slash]; rw [slash_action_eqn f γ hγ]; rw [slash_action_eqn g γ hγ] }⟩

Depends on / 依赖: SlashAction, SlashAction.add_slash, add_slash, slash_action_eq, slash_action_eqn
-/
instance instAdd : Add (SlashInvariantForm Γ k) :=
  ⟨fun f g =>
    { toFun := f + g
      slash_action_eq' := fun γ hγ => by
        rw [SlashAction.add_slash]; rw [slash_action_eqn f γ hγ]; rw [slash_action_eqn g γ hγ] }⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: IsAddApply (SlashInvariantForm Γ k) ℍ Complex
  body: rfl

@[deprecated (since := "2026-07-10")] alias coe_add := FunLike.coe_add

@[deprecated (since := "2026-07-10")] protected alias add_apply := add_apply

中文:
实例 :
  签名: IsAddApply (SlashInvariantForm Γ k) ℍ Complex
  定义体: rfl

@[deprecated (since := "2026-07-10")] alias coe_add := FunLike.coe_add

@[deprecated (since := "2026-07-10")] protected alias add_apply := add_apply
-/
instance : IsAddApply (SlashInvariantForm Γ k) ℍ Complex where
  add_apply _ _ _ := rfl

@[deprecated (since := "2026-07-10")] alias coe_add := FunLike.coe_add

@[deprecated (since := "2026-07-10")] protected alias add_apply := add_apply

/--
Instance `instZero` / 实例 `instZero`

English:
instance instZero
  signature: : Zero (SlashInvariantForm Γ k)
  body: ⟨{toFun := 0
    slash_action_eq' := fun _ _ => SlashAction.zero_slash _ _}⟩

中文:
实例 instZero
  签名: : Zero (SlashInvariantForm Γ k)
  定义体: ⟨{toFun := 0
    slash_action_eq' := fun _ _ => SlashAction.zero_slash _ _}⟩

Depends on / 依赖: SlashAction, SlashAction.zero_slash, slash_action_eq, zero_slash
-/
instance instZero : Zero (SlashInvariantForm Γ k) :=
  ⟨{toFun := 0
    slash_action_eq' := fun _ _ => SlashAction.zero_slash _ _}⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: IsZeroApply (SlashInvariantForm Γ k) ℍ Complex
  body: rfl

@[deprecated (since := "2026-07-10")] alias coe_zero := FunLike.coe_zero

中文:
实例 :
  签名: IsZeroApply (SlashInvariantForm Γ k) ℍ Complex
  定义体: rfl

@[deprecated (since := "2026-07-10")] alias coe_zero := FunLike.coe_zero

Depends on / 依赖: Partition, Partition.parts
-/
instance : IsZeroApply (SlashInvariantForm Γ k) ℍ Complex where
  zero_apply _ := rfl

@[deprecated (since := "2026-07-10")] alias coe_zero := FunLike.coe_zero

section smul

variable [Γ.HasDetOne] {α : Type*} [SMul α Complex] [IsScalarTower α Complex Complex]

/--
Instance `instSMul` / 实例 `instSMul`

English:
instance instSMul
  signature: : SMul α (SlashInvariantForm Γ k) where
  body: { toFun := c • ↑f
    slash_action_eq' γ hγ := by
      rw [← smul_one_smul Complex]
      simp [-smul_assoc, smul_slash, slash_action_eqn _ _ hγ, σ, Subgroup.HasDetOne.det_eq hγ] }

中文:
实例 instSMul
  签名: : SMul α (SlashInvariantForm Γ k) where
  定义体: { toFun := c • ↑f
    slash_action_eq' γ hγ := by
      rw [← smul_one_smul Complex]
      simp [-smul_assoc, smul_slash, slash_action_eqn _ _ hγ, σ, Subgroup.HasDetOne.det_eq hγ] }

Depends on / 依赖: HasDetOne, Subgroup, Subgroup.HasDetOne.det_eq, det_eq, slash_action_eq, slash_action_eqn, smul_assoc, smul_one_smul, smul_slash
-/
instance instSMul : SMul α (SlashInvariantForm Γ k) where
  smul c f :=
  { toFun := c • ↑f
    slash_action_eq' γ hγ := by
      rw [← smul_one_smul Complex]
      simp [-smul_assoc, smul_slash, slash_action_eqn _ _ hγ, σ, Subgroup.HasDetOne.det_eq hγ] }

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: IsSMulApply α (SlashInvariantForm Γ k) ℍ Complex
  body: rfl

@[deprecated (since := "2026-07-10")] alias coe_smul := FunLike.coe_smul

@[deprecated (since := "2026-07-10")] protected alias smul_apply := smul_apply

中文:
实例 :
  签名: IsSMulApply α (SlashInvariantForm Γ k) ℍ Complex
  定义体: rfl

@[deprecated (since := "2026-07-10")] alias coe_smul := FunLike.coe_smul

@[deprecated (since := "2026-07-10")] protected alias smul_apply := smul_apply
-/
instance : IsSMulApply α (SlashInvariantForm Γ k) ℍ Complex where
  smul_apply _ _ _ := rfl

@[deprecated (since := "2026-07-10")] alias coe_smul := FunLike.coe_smul

@[deprecated (since := "2026-07-10")] protected alias smul_apply := smul_apply

end smul

section smulReal

variable {α : Type*} [SMul α Complex] [SMul α Real] [IsScalarTower α Real Complex]

/--
Instance `instSMulReal` / 实例 `instSMulReal`

English:
instance instSMulReal
  signature: : SMul α (SlashInvariantForm Γ k) where
  body: { toFun := c • ↑f
    slash_action_eq' γ hγ := by
      rw [← smul_one_smul Real]; rw [← smul_one_smul Complex]; rw [smul_slash]; rw [Complex.real_smul]; rw [mul_one]; rw [σ_ofReal]; rw [slash_action_eqn _ _ hγ] }

中文:
实例 instSMulReal
  签名: : SMul α (SlashInvariantForm Γ k) where
  定义体: { toFun := c • ↑f
    slash_action_eq' γ hγ := by
      rw [← smul_one_smul Real]; rw [← smul_one_smul Complex]; rw [smul_slash]; rw [Complex.real_smul]; rw [mul_one]; rw [σ_ofReal]; rw [slash_action_eqn _ _ hγ] }

Depends on / 依赖: Complex.real_smul, mul_one, real_smul, slash_action_eq, slash_action_eqn, smul_one_smul, smul_slash
-/
instance instSMulReal : SMul α (SlashInvariantForm Γ k) where
  smul c f :=
  { toFun := c • ↑f
    slash_action_eq' γ hγ := by
      rw [← smul_one_smul Real]; rw [← smul_one_smul Complex]; rw [smul_slash]; rw [Complex.real_smul]; rw [mul_one]; rw [σ_ofReal]; rw [slash_action_eqn _ _ hγ] }

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: IsSMulApply α (SlashInvariantForm Γ k) ℍ Complex
  body: rfl

@[deprecated (since := "2026-07-10")] alias coe_smulReal := FunLike.coe_smul

@[deprecated (since := "2026-07-10")] protected alias smul_applyReal := smul_apply

中文:
实例 :
  签名: IsSMulApply α (SlashInvariantForm Γ k) ℍ Complex
  定义体: rfl

@[deprecated (since := "2026-07-10")] alias coe_smulReal := FunLike.coe_smul

@[deprecated (since := "2026-07-10")] protected alias smul_applyReal := smul_apply
-/
instance : IsSMulApply α (SlashInvariantForm Γ k) ℍ Complex where
  smul_apply _ _ _ := rfl

@[deprecated (since := "2026-07-10")] alias coe_smulReal := FunLike.coe_smul

@[deprecated (since := "2026-07-10")] protected alias smul_applyReal := smul_apply

end smulReal

/--
Instance `instNeg` / 实例 `instNeg`

English:
instance instNeg
  signature: : Neg (SlashInvariantForm Γ k)
  body: ⟨fun f =>
    { toFun := -f
      slash_action_eq' := fun γ hγ => by rw [SlashAction.neg_slash, slash_action_eqn f γ hγ] }⟩

中文:
实例 instNeg
  签名: : Neg (SlashInvariantForm Γ k)
  定义体: ⟨fun f =>
    { toFun := -f
      slash_action_eq' := fun γ hγ => by rw [SlashAction.neg_slash, slash_action_eqn f γ hγ] }⟩

Depends on / 依赖: SlashAction, SlashAction.neg_slash, neg_slash, slash_action_eq, slash_action_eqn
-/
instance instNeg : Neg (SlashInvariantForm Γ k) :=
  ⟨fun f =>
    { toFun := -f
      slash_action_eq' := fun γ hγ => by rw [SlashAction.neg_slash, slash_action_eqn f γ hγ] }⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: IsNegApply (SlashInvariantForm Γ k) ℍ Complex
  body: rfl

@[deprecated (since := "2026-07-10")] alias coe_neg := FunLike.coe_neg

@[deprecated (since := "2026-07-10")] protected alias neg_apply := neg_apply

中文:
实例 :
  签名: IsNegApply (SlashInvariantForm Γ k) ℍ Complex
  定义体: rfl

@[deprecated (since := "2026-07-10")] alias coe_neg := FunLike.coe_neg

@[deprecated (since := "2026-07-10")] protected alias neg_apply := neg_apply
-/
instance : IsNegApply (SlashInvariantForm Γ k) ℍ Complex where
  neg_apply _ _ := rfl

@[deprecated (since := "2026-07-10")] alias coe_neg := FunLike.coe_neg

@[deprecated (since := "2026-07-10")] protected alias neg_apply := neg_apply

/--
Instance `instSub` / 实例 `instSub`

English:
instance instSub
  signature: : Sub (SlashInvariantForm Γ k)
  body: ⟨fun f g => f + -g⟩

中文:
实例 instSub
  签名: : Sub (SlashInvariantForm Γ k)
  定义体: ⟨fun f g => f + -g⟩
-/
instance instSub : Sub (SlashInvariantForm Γ k) :=
  ⟨fun f g => f + -g⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: IsSubApply (SlashInvariantForm Γ k) ℍ Complex
  body: rfl

@[deprecated (since := "2026-07-10")] alias coe_sub := FunLike.coe_sub

@[deprecated (since := "2026-07-10")] protected alias sub_apply := sub_apply

中文:
实例 :
  签名: IsSubApply (SlashInvariantForm Γ k) ℍ Complex
  定义体: rfl

@[deprecated (since := "2026-07-10")] alias coe_sub := FunLike.coe_sub

@[deprecated (since := "2026-07-10")] protected alias sub_apply := sub_apply
-/
instance : IsSubApply (SlashInvariantForm Γ k) ℍ Complex where
  sub_apply _ _ _ := rfl

@[deprecated (since := "2026-07-10")] alias coe_sub := FunLike.coe_sub

@[deprecated (since := "2026-07-10")] protected alias sub_apply := sub_apply

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: AddCommGroup (SlashInvariantForm Γ k)
  body: fast_instance% FunLike.addCommGroup

@[deprecated (since := "2026-07-10")] alias coeHom := FunLike.coeMonoidHom

@[deprecated (since := "2026-07-10")] alias coeHom_injective := FunLike.coeMonoidHom_injective

中文:
实例 :
  签名: AddCommGroup (SlashInvariantForm Γ k)
  定义体: fast_instance% FunLike.addCommGroup

@[deprecated (since := "2026-07-10")] alias coeHom := FunLike.coeMonoidHom

@[deprecated (since := "2026-07-10")] alias coeHom_injective := FunLike.coeMonoidHom_injective

Depends on / 依赖: FunLike, FunLike.addCommGroup, addCommGroup, fast_instance
-/
instance : AddCommGroup (SlashInvariantForm Γ k) := fast_instance% FunLike.addCommGroup

@[deprecated (since := "2026-07-10")] alias coeHom := FunLike.coeMonoidHom

@[deprecated (since := "2026-07-10")] alias coeHom_injective := FunLike.coeMonoidHom_injective

/--
Instance `instModuleComplex` / 实例 `instModuleComplex`

English:
instance instModuleComplex
  signature: [Γ.HasDetOne] {α : Type*} [Semiring α] [Module α Complex]
  body: FunLike.module

中文:
实例 instModuleComplex
  签名: [Γ.HasDetOne] {α : 类型} [Semiring α] [Module α Complex]
  定义体: FunLike.module

Depends on / 依赖: FunLike, FunLike.module, module
-/
instance instModuleComplex [Γ.HasDetOne] {α : Type*} [Semiring α] [Module α Complex]
    [IsScalarTower α Complex Complex] : Module α (SlashInvariantForm Γ k) := FunLike.module

/--
Instance `instModuleReal` / 实例 `instModuleReal`

English:
instance instModuleReal
  signature: {α : Type*} [Semiring α] [Module α Real] [Module α Complex] [IsScalarTower α Real Complex]
  body: FunLike.module

中文:
实例 instModuleReal
  签名: {α : 类型} [Semiring α] [Module α 实数] [Module α Complex] [IsScalarTower α 实数 Complex]
  定义体: FunLike.module

Depends on / 依赖: FunLike, FunLike.module, module
-/
instance instModuleReal {α : Type*} [Semiring α] [Module α Real] [Module α Complex] [IsScalarTower α Real Complex] :
    Module α (SlashInvariantForm Γ k) := FunLike.module

/-- The `SlashInvariantForm` corresponding to `Function.const _ x`. -/
@[simps -fullyApplied]
/--
Definition of `const` / `const` 的定义

English:
definition const
  signature: [Γ.HasDetOne] (x : Complex)
  body: Function.const _ x
  slash_action_eq' g hg := by ext; simp [slash_def, σ, Subgroup.HasDetOne.det_eq hg]

中文:
定义 const
  签名: [Γ.HasDetOne] (x : Complex)
  定义体: Function.const _ x
  slash_action_eq' g hg := by ext; simp [slash_def, σ, Subgroup.HasDetOne.det_eq hg]

Depends on / 依赖: Function, Function.const
-/
def const [Γ.HasDetOne] (x : Complex) : SlashInvariantForm Γ 0 where
  toFun := Function.const _ x
  slash_action_eq' g hg := by ext; simp [slash_def, σ, Subgroup.HasDetOne.det_eq hg]

/-- The `SlashInvariantForm` corresponding to `Function.const _ x`. -/
@[simps -fullyApplied]
/--
Definition of `constReal` / `constReal` 的定义

English:
definition constReal
  signature: [Γ.HasDetPlusMinusOne] (x : Real)
  body: Function.const _ x
  slash_action_eq' g hg := funext fun τ => by simp [slash_apply,
    Subgroup.HasDetPlusMinusOne.abs_det hg, -Matrix.GeneralLinearGroup.val_det_apply]

中文:
定义 constReal
  签名: [Γ.HasDetPlusMinusOne] (x : 实数)
  定义体: Function.const _ x
  slash_action_eq' g hg := funext fun τ => by simp [slash_apply,
    Subgroup.HasDetPlusMinusOne.abs_det hg, -Matrix.GeneralLinearGroup.val_det_apply]

Depends on / 依赖: Function, Function.const
-/
def constReal [Γ.HasDetPlusMinusOne] (x : Real) : SlashInvariantForm Γ 0 where
  toFun := Function.const _ x
  slash_action_eq' g hg := funext fun τ => by simp [slash_apply,
    Subgroup.HasDetPlusMinusOne.abs_det hg, -Matrix.GeneralLinearGroup.val_det_apply]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Γ.HasDetPlusMinusOne]
  signature: : One (SlashInvariantForm Γ 0) where
  body: { constReal 1 with toFun := 1 }

@[simp]

中文:
实例 [Γ.HasDetPlusMinusOne]
  签名: : One (SlashInvariantForm Γ 0) where
  定义体: { constReal 1 with toFun := 1 }

@[simp]

Depends on / 依赖: constReal
-/
instance [Γ.HasDetPlusMinusOne] : One (SlashInvariantForm Γ 0) where
  one := { constReal 1 with toFun := 1 }

@[simp]
/--
theorem `one_coe_eq_one` / 定理 `one_coe_eq_one`

English:
theorem one_coe_eq_one
  given: [Γ.HasDetPlusMinusOne]
  statement: ((1 : SlashInvariantForm Γ 0) : ℍ -> Complex) = 1
  proof: rfl

中文:
定理 one_coe_eq_one
  条件: [Γ.HasDetPlusMinusOne]
  结论: ((1 : SlashInvariantForm Γ 0) : ℍ -> Complex) = 1
  证明: rfl
-/
theorem one_coe_eq_one [Γ.HasDetPlusMinusOne] : ((1 : SlashInvariantForm Γ 0) : ℍ -> Complex) = 1 :=
  rfl

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Inhabited (SlashInvariantForm Γ k)
  body: ⟨0⟩

中文:
实例 :
  签名: Inhabited (SlashInvariantForm Γ k)
  定义体: ⟨0⟩
-/
instance : Inhabited (SlashInvariantForm Γ k) :=
  ⟨0⟩

/--
Definition of `mul` / `mul` 的定义

English:
definition mul
  signature: [Γ.HasDetPlusMinusOne] {k₁ k₂ : Int} (f : SlashInvariantForm Γ k₁)
  body: f * g
  slash_action_eq' A hA := by simp [mul_slash, Subgroup.HasDetPlusMinusOne.abs_det hA,
    -Matrix.GeneralLinearGroup.val_det_apply, slash_action_eqn f A hA, slash_action_eqn g A hA]

@[simp]

中文:
定义 mul
  签名: [Γ.HasDetPlusMinusOne] {k₁ k₂ : 整数} (f : SlashInvariantForm Γ k₁)
  定义体: f * g
  slash_action_eq' A hA := by simp [mul_slash, Subgroup.HasDetPlusMinusOne.abs_det hA,
    -Matrix.GeneralLinearGroup.val_det_apply, slash_action_eqn f A hA, slash_action_eqn g A hA]

@[simp]
-/
def mul [Γ.HasDetPlusMinusOne] {k₁ k₂ : Int} (f : SlashInvariantForm Γ k₁)
    (g : SlashInvariantForm Γ k₂) : SlashInvariantForm Γ (k₁ + k₂) where
  toFun := f * g
  slash_action_eq' A hA := by simp [mul_slash, Subgroup.HasDetPlusMinusOne.abs_det hA,
    -Matrix.GeneralLinearGroup.val_det_apply, slash_action_eqn f A hA, slash_action_eqn g A hA]

@[simp]
/--
theorem `coe_mul` / 定理 `coe_mul`

English:
theorem coe_mul
  statement: [Γ.HasDetPlusMinusOne] {k₁ k₂ : Int} (f : SlashInvariantForm Γ k₁)
  proof: rfl

中文:
定理 coe_mul
  结论: [Γ.HasDetPlusMinusOne] {k₁ k₂ : 整数} (f : SlashInvariantForm Γ k₁)
  证明: rfl
-/
theorem coe_mul [Γ.HasDetPlusMinusOne] {k₁ k₂ : Int} (f : SlashInvariantForm Γ k₁)
    (g : SlashInvariantForm Γ k₂) : ⇑(f.mul g) = ⇑f * ⇑g :=
  rfl

/-- Given `SlashInvariantForm`'s `f i` of weight `k i` for `i : ι`, define the form which as a
function is a product of those indexed by `s : Finset ι` with weight `m = ∑ i ∈ s, k i`. -/
@[simps -fullyApplied]
/--
Definition of `prod` / `prod` 的定义

English:
definition prod
  signature: {ι : Type} {s : Finset ι} {k : ι -> Int} (m : Int)
  body: ∏ i in s, (f i)
  slash_action_eq' A hA := by
    simp [hm, prod_slash_sum_weights, -Matrix.GeneralLinearGroup.val_det_apply,
       Subgroup.HasDetPlusMinusOne.abs_det hA, SlashInvariantForm.slash_action_eqn (f _) A hA]

中文:
定义 prod
  签名: {ι : Type} {s : Finset ι} {k : ι -> 整数} (m : 整数)
  定义体: ∏ i in s, (f i)
  slash_action_eq' A hA := by
    simp [hm, prod_slash_sum_weights, -Matrix.GeneralLinearGroup.val_det_apply,
       Subgroup.HasDetPlusMinusOne.abs_det hA, SlashInvariantForm.slash_action_eqn (f _) A hA]
-/
def prod {ι : Type} {s : Finset ι} {k : ι -> Int} (m : Int)
    (hm : m = ∑ i in s, k i) {Γ : Subgroup (GL (Fin 2) Real)} [Γ.HasDetPlusMinusOne]
    (f : (i : ι) -> SlashInvariantForm Γ (k i)) : SlashInvariantForm Γ m where
  toFun := ∏ i in s, (f i)
  slash_action_eq' A hA := by
    simp [hm, prod_slash_sum_weights, -Matrix.GeneralLinearGroup.val_det_apply,
       Subgroup.HasDetPlusMinusOne.abs_det hA, SlashInvariantForm.slash_action_eqn (f _) A hA]

/-- Given `SlashInvariantForm`'s `f i` of weight `k`, define the form which as a
function is a product of those indexed by `s : Finset ι` with weight `#s * k`. -/
@[simps! -fullyApplied]
/--
Definition of `prodEqualWeights` / `prodEqualWeights` 的定义

English:
definition prodEqualWeights
  signature: {ι : Type} {s : Finset ι} {k : Int}
  body: prod (k := fun i => k) (s := s) (s.card * k) (by simp) f

中文:
定义 prodEqualWeights
  签名: {ι : Type} {s : Finset ι} {k : 整数}
  定义体: prod (k := fun i => k) (s := s) (s.card * k) (by simp) f

Depends on / 依赖: s.card
-/
def prodEqualWeights {ι : Type} {s : Finset ι} {k : Int}
    {Γ : Subgroup (GL (Fin 2) Real)} [Γ.HasDetPlusMinusOne]
    (f : (i : ι) -> SlashInvariantForm Γ k) : SlashInvariantForm Γ (s.card * k) :=
  prod (k := fun i => k) (s := s) (s.card * k) (by simp) f

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Γ.HasDetPlusMinusOne]
  signature: : NatCast (SlashInvariantForm Γ 0) where
  body: constReal n

@[simp, norm_cast]

中文:
实例 [Γ.HasDetPlusMinusOne]
  签名: : 自然数Cast (SlashInvariantForm Γ 0) where
  定义体: constReal n

@[simp, norm_cast]

Depends on / 依赖: constReal
-/
instance [Γ.HasDetPlusMinusOne] : NatCast (SlashInvariantForm Γ 0) where
  natCast n := constReal n

@[simp, norm_cast]
/--
theorem `coe_natCast` / 定理 `coe_natCast`

English:
theorem coe_natCast
  given: [Γ.HasDetPlusMinusOne] (n : Nat)
  statement: ⇑(n : SlashInvariantForm Γ 0) = n
  proof: rfl

中文:
定理 coe_natCast
  条件: [Γ.HasDetPlusMinusOne] (n : 自然数)
  结论: ⇑(n : SlashInvariantForm Γ 0) = n
  证明: rfl
-/
theorem coe_natCast [Γ.HasDetPlusMinusOne] (n : Nat) : ⇑(n : SlashInvariantForm Γ 0) = n := rfl

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Γ.HasDetPlusMinusOne]
  signature: : IntCast (SlashInvariantForm Γ 0) where
  body: constReal z

@[simp, norm_cast]

中文:
实例 [Γ.HasDetPlusMinusOne]
  签名: : 整数Cast (SlashInvariantForm Γ 0) where
  定义体: constReal z

@[simp, norm_cast]

Depends on / 依赖: constReal
-/
instance [Γ.HasDetPlusMinusOne] : IntCast (SlashInvariantForm Γ 0) where
  intCast z := constReal z

@[simp, norm_cast]
/--
theorem `coe_intCast` / 定理 `coe_intCast`

English:
theorem coe_intCast
  given: [Γ.HasDetPlusMinusOne] (z : Int)
  statement: ⇑(z : SlashInvariantForm Γ 0) = z
  proof: rfl

中文:
定理 coe_intCast
  条件: [Γ.HasDetPlusMinusOne] (z : 整数)
  结论: ⇑(z : SlashInvariantForm Γ 0) = z
  证明: rfl
-/
theorem coe_intCast [Γ.HasDetPlusMinusOne] (z : Int) : ⇑(z : SlashInvariantForm Γ 0) = z := rfl

open ConjAct Pointwise in
/--
Definition of `translate` / `translate` 的定义

English:
definition translate
  signature: [SlashInvariantFormClass F Γ k] (f : F) (g : GL (Fin 2) Real)
  body: f ∣[k] g
  slash_action_eq' j hj := by
    rw [map_inv]; rw [Γ.mem_inv_pointwise_smul_iff]; rw [toConjAct_smul] at hj
    simpa [← SlashAction.slash_mul] using congr_arg (· ∣[k] g) (slash_action_eqn f _ hj)

@[simp]

中文:
定义 translate
  签名: [SlashInvariantFormClass F Γ k] (f : F) (g : GL (Fin 2) 实数)
  定义体: f ∣[k] g
  slash_action_eq' j hj := by
    rw [map_inv]; rw [Γ.mem_inv_pointwise_smul_iff]; rw [toConjAct_smul] at hj
    simpa [← SlashAction.slash_mul] using congr_arg (· ∣[k] g) (slash_action_eqn f _ hj)

@[simp]
-/
noncomputable def translate [SlashInvariantFormClass F Γ k] (f : F) (g : GL (Fin 2) Real) :
    SlashInvariantForm (toConjAct g⁻¹ • Γ) k where
  toFun := f ∣[k] g
  slash_action_eq' j hj := by
    rw [map_inv]; rw [Γ.mem_inv_pointwise_smul_iff]; rw [toConjAct_smul] at hj
    simpa [← SlashAction.slash_mul] using congr_arg (· ∣[k] g) (slash_action_eqn f _ hj)

@[simp]
/--
lemma `coe_translate` / 引理 `coe_translate`

English:
lemma coe_translate
  given: [SlashInvariantFormClass F Γ k] (f : F) (g : GL (Fin 2) Real)
  proof: rfl

中文:
引理 coe_translate
  条件: [SlashInvariantFormClass F Γ k] (f : F) (g : GL (Fin 2) 实数)
  证明: rfl
-/
lemma coe_translate [SlashInvariantFormClass F Γ k] (f : F) (g : GL (Fin 2) Real) :
    translate f g = ⇑f ∣[k] g :=
  rfl

end SlashInvariantForm
