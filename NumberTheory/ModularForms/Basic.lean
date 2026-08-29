/-
Copyright (c) 2022 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
module

public import Mathlib.Algebra.DirectSum.Algebra
public import Mathlib.Analysis.Calculus.FDeriv.Star
public import Mathlib.Analysis.Complex.UpperHalfPlane.Manifold
public import Mathlib.Geometry.Manifold.MFDeriv.SpecificFunctions
public import Mathlib.NumberTheory.ModularForms.BoundedAtCusp
public import Mathlib.NumberTheory.ModularForms.SlashInvariantForms
import Mathlib.Geometry.Manifold.Notation

/-!
# Modular forms

This file defines modular forms and proves some basic properties about them. Including constructing
the graded ring of modular forms.

We begin by defining modular forms and cusp forms as extension of `SlashInvariantForm`s then we
define the space of modular forms, cusp forms and prove that the product of two modular forms is a
modular form.
-/

@[expose] public section

open Complex UpperHalfPlane Matrix.SpecialLinearGroup

open scoped Topology Manifold MatrixGroups ComplexConjugate

noncomputable section

section ModularForm

open ModularForm

/--
lemma `MDifferentiable.slash_of_pos` / 引理 `MDifferentiable.slash_of_pos`

English:
lemma MDifferentiable.slash_of_pos
  statement: {f : ℍ -> Complex} (hf : MDiff f)
  proof: by
  refine .mul (.mul ?_ mdifferentiable_const) (mdifferentiable_denom_zpow g _)
  simpa only [σ, hg, ↓reduceIte] using! hf.comp (mdifferentiable_smul hg)

中文:
引理 MDifferentiable.slash_of_pos
  结论: {f : ℍ -> Complex} (hf : MDiff f)
  证明: by
  refine .mul (.mul ?_ mdifferentiable_const) (mdifferentiable_denom_zpow g _)
  simpa only [σ, hg, ↓reduceIte] using! hf.comp (mdifferentiable_smul hg)
-/
private lemma MDifferentiable.slash_of_pos {f : ℍ -> Complex} (hf : MDiff f)
    (k : Int) {g : GL (Fin 2) Real} (hg : 0 < g.det.val) :
    MDiff (f ∣[k] g) := by
  refine .mul (.mul ?_ mdifferentiable_const) (mdifferentiable_denom_zpow g _)
  simpa only [σ, hg, ↓reduceIte] using! hf.comp (mdifferentiable_smul hg)

/--
lemma `slash_J` / 引理 `slash_J`

English:
lemma slash_J
  given: (f : ℍ -> Complex) (k : Int)
  proof: by
  simp [slash_def, J_smul]

中文:
引理 slash_J
  条件: (f : ℍ -> Complex) (k : 整数)
  证明: by
  simp [slash_def, J_smul]
-/
private lemma slash_J (f : ℍ -> Complex) (k : Int) :
    f ∣[k] J = fun τ : ℍ => conj (f <| ofComplex <| -(conj ↑τ)) := by
  simp [slash_def, J_smul]

/--
lemma `MDifferentiable.slashJ` / 引理 `MDifferentiable.slashJ`

English:
lemma MDifferentiable.slashJ
  given: {f : ℍ -> Complex} (hf : MDiff f) (k : Int)
  proof: by
  simp only [mdifferentiable_iff, slash_J, Function.comp_def] at hf ⊢
  have : {z | 0 < z.im}.EqOn (fun x => conj (f <| ofComplex <| -conj ↑(ofComplex x)))
      (fun x => conj (f <| ofComplex <| -conj x)) := fun z h => by simp [ofComplex_apply_of_im_pos h]
  refine .congr (fun z hz => Differenti

中文:
引理 MDifferentiable.slashJ
  条件: {f : ℍ -> Complex} (hf : MDiff f) (k : 整数)
  证明: by
  simp only [mdifferentiable_iff, slash_J, Function.comp_def] at hf ⊢
  have : {z | 0 < z.im}.EqOn (fun x => conj (f <| ofComplex <| -conj ↑(ofComplex x)))
      (fun x => conj (f <| ofComplex <| -conj x)) := fun z h => by simp [ofComplex_apply_of_im_pos h]
  refine .congr (fun z hz => Differenti
-/
private lemma MDifferentiable.slashJ {f : ℍ -> Complex} (hf : MDiff f) (k : Int) :
    MDiff (f ∣[k] J) := by
  simp only [mdifferentiable_iff, slash_J, Function.comp_def] at hf ⊢
  have : {z | 0 < z.im}.EqOn (fun x => conj (f <| ofComplex <| -conj ↑(ofComplex x)))
      (fun x => conj (f <| ofComplex <| -conj x)) := fun z h => by simp [ofComplex_apply_of_im_pos h]
  refine .congr (fun z hz => DifferentiableAt.differentiableWithinAt ?_) this
  have : 0 < (-conj z).im := by simpa using! hz
  have := hf.differentiableAt (isOpen_upperHalfPlaneSet.mem_nhds this)
  simpa using! (this.comp _ differentiable_neg.differentiableAt).star_star.neg

/--
lemma `MDifferentiable.slash` / 引理 `MDifferentiable.slash`

English:
lemma MDifferentiable.slash
  statement: {f : ℍ -> Complex} (hf : MDiff f)
  proof: by
  refine g.det_ne_zero.lt_or_gt.elim (fun hg => ?_) (hf.slash_of_pos k)
  rw [show g = J * (J * g) by simp [← mul_assoc]; rw [← sq], SlashAction.slash_mul]
  exact (hf.slashJ k).slash_of_pos _ (by simpa using hg)

中文:
引理 MDifferentiable.slash
  结论: {f : ℍ -> Complex} (hf : MDiff f)
  证明: by
  refine g.det_ne_zero.lt_or_gt.elim (fun hg => ?_) (hf.slash_of_pos k)
  rw [show g = J * (J * g) by simp [← mul_assoc]; rw [← sq], SlashAction.slash_mul]
  exact (hf.slashJ k).slash_of_pos _ (by simpa using hg)

Depends on / 依赖: SlashAction, SlashAction.slash_mul, det_ne_zero, g.det_ne_zero.lt_or_gt.elim, hf.slashJ, hf.slash_of_pos, lt_or_gt, mul_assoc, slashJ, slash_mul, slash_of_pos
-/
lemma MDifferentiable.slash {f : ℍ -> Complex} (hf : MDiff f)
    (k : Int) (g : GL (Fin 2) Real) : MDiff (f ∣[k] g) := by
  refine g.det_ne_zero.lt_or_gt.elim (fun hg => ?_) (hf.slash_of_pos k)
  rw [show g = J * (J * g) by simp [← mul_assoc]; rw [← sq], SlashAction.slash_mul]
  exact (hf.slashJ k).slash_of_pos _ (by simpa using hg)

variable (F : Type*) (Γ : Subgroup (GL (Fin 2) Real)) (k : Int)

open scoped ModularForm

/--
Definition of `ModularForm` / `ModularForm` 的定义

English:
structure ModularForm
  parameters: extends SlashInvariantForm Γ k
  extends: SlashInvariantForm Γ k
  axioms and operations (2):
    - holo' : MDiff (toSlashInvariantForm : ℍ -> Complex)
    - bdd_at_cusps'({c : OnePoint Real} (hc : IsCusp c Γ)) : c.IsBoundedAt toFun k

中文:
结构 ModularForm
  参数: extends SlashInvariantForm Γ k
  继承: SlashInvariantForm Γ k
  公理与运算 (2 个):
    - holo' : MDiff (toSlashInvariantForm : ℍ -> Complex)
    - bdd_at_cusps'({c : OnePoint 实数} (hc : IsCusp c Γ)) : c.IsBoundedAt toFun k
-/
structure ModularForm extends SlashInvariantForm Γ k where
  holo' : MDiff (toSlashInvariantForm : ℍ -> Complex)
  bdd_at_cusps' {c : OnePoint Real} (hc : IsCusp c Γ) : c.IsBoundedAt toFun k

/-- The `SlashInvariantForm` associated to a `ModularForm`. -/
add_decl_doc ModularForm.toSlashInvariantForm

/--
Definition of `CuspForm` / `CuspForm` 的定义

English:
structure CuspForm
  parameters: extends SlashInvariantForm Γ k
  extends: SlashInvariantForm Γ k
  axioms and operations (2):
    - holo' : MDiff (toSlashInvariantForm : ℍ -> Complex)
    - zero_at_cusps'({c : OnePoint Real} (hc : IsCusp c Γ)) : c.IsZeroAt toFun k

中文:
结构 CuspForm
  参数: extends SlashInvariantForm Γ k
  继承: SlashInvariantForm Γ k
  公理与运算 (2 个):
    - holo' : MDiff (toSlashInvariantForm : ℍ -> Complex)
    - zero_at_cusps'({c : OnePoint 实数} (hc : IsCusp c Γ)) : c.IsZeroAt toFun k
-/
structure CuspForm extends SlashInvariantForm Γ k where
  holo' : MDiff (toSlashInvariantForm : ℍ -> Complex)
  zero_at_cusps' {c : OnePoint Real} (hc : IsCusp c Γ) : c.IsZeroAt toFun k

/-- The `SlashInvariantForm` associated to a `CuspForm`. -/
add_decl_doc CuspForm.toSlashInvariantForm

/--
Definition of `ModularFormClass` / `ModularFormClass` 的定义

English:
class ModularFormClass
  parameters: (F : Type*) (Γ : outParam <| Subgroup (GL (Fin 2) Real)) (k : outParam Int)
  extends: SlashInvariantFormClass F Γ k
  axioms and operations (2):
    - holo : forall f : F, MDiff (f : ℍ -> Complex)
    - bdd_at_cusps((f : F) {c : OnePoint Real} (hc : IsCusp c Γ)) : c.IsBoundedAt f k

中文:
类 ModularFormClass
  参数: (F : 类型) (Γ : outParam <| Subgroup (GL (Fin 2) 实数)) (k : outParam 整数)
  继承: SlashInvariantFormClass F Γ k
  公理与运算 (2 个):
    - holo : 对任意 f : F, MDiff (f : ℍ -> Complex)
    - bdd_at_cusps((f : F) {c : OnePoint 实数} (hc : IsCusp c Γ)) : c.IsBoundedAt f k
-/
class ModularFormClass (F : Type*) (Γ : outParam <| Subgroup (GL (Fin 2) Real)) (k : outParam Int)
    [FunLike F ℍ Complex] : Prop extends SlashInvariantFormClass F Γ k where
  holo : forall f : F, MDiff (f : ℍ -> Complex)
  bdd_at_cusps (f : F) {c : OnePoint Real} (hc : IsCusp c Γ) : c.IsBoundedAt f k

/--
Definition of `CuspFormClass` / `CuspFormClass` 的定义

English:
class CuspFormClass
  parameters: (F : Type*) (Γ : outParam <| Subgroup (GL (Fin 2) Real)) (k : outParam Int)
  extends: SlashInvariantFormClass F Γ k
  axioms and operations (2):
    - holo : forall f : F, MDiff (f : ℍ -> Complex)
    - zero_at_cusps((f : F) {c : OnePoint Real} (hc : IsCusp c Γ)) : c.IsZeroAt f k

中文:
类 CuspFormClass
  参数: (F : 类型) (Γ : outParam <| Subgroup (GL (Fin 2) 实数)) (k : outParam 整数)
  继承: SlashInvariantFormClass F Γ k
  公理与运算 (2 个):
    - holo : 对任意 f : F, MDiff (f : ℍ -> Complex)
    - zero_at_cusps((f : F) {c : OnePoint 实数} (hc : IsCusp c Γ)) : c.IsZeroAt f k
-/
class CuspFormClass (F : Type*) (Γ : outParam <| Subgroup (GL (Fin 2) Real)) (k : outParam Int)
    [FunLike F ℍ Complex] : Prop extends SlashInvariantFormClass F Γ k where
  holo : forall f : F, MDiff (f : ℍ -> Complex)
  zero_at_cusps (f : F) {c : OnePoint Real} (hc : IsCusp c Γ) : c.IsZeroAt f k

instance (priority := 100) ModularForm.funLike :
    FunLike (ModularForm Γ k) ℍ Complex where
  coe f := f.toFun
  coe_injective f g h := by cases f; cases g; congr; exact DFunLike.ext' h

instance (priority := 100) ModularForm.instModularFormClass :
    ModularFormClass (ModularForm Γ k) Γ k where
  slash_action_eq f := f.slash_action_eq'
  holo := ModularForm.holo'
  bdd_at_cusps := ModularForm.bdd_at_cusps'

@[fun_prop]
/--
lemma `ModularFormClass.continuous` / 引理 `ModularFormClass.continuous`

English:
lemma ModularFormClass.continuous
  statement: {k : Int} {Γ : Subgroup (GL (Fin 2) Real)}
  proof: (ModularFormClass.holo f).continuous

中文:
引理 ModularFormClass.continuous
  结论: {k : 整数} {Γ : Subgroup (GL (Fin 2) 实数)}
  证明: (ModularFormClass.holo f).continuous

Depends on / 依赖: ModularFormClass, ModularFormClass.holo, continuous
-/
lemma ModularFormClass.continuous {k : Int} {Γ : Subgroup (GL (Fin 2) Real)}
    {F : Type*} [FunLike F ℍ Complex] [ModularFormClass F Γ k] (f : F) :
    Continuous f :=
  (ModularFormClass.holo f).continuous

instance (priority := 100) CuspForm.funLike : FunLike (CuspForm Γ k) ℍ Complex where
  coe f := f.toFun
  coe_injective f g h := by cases f; cases g; congr; exact DFunLike.ext' h

instance (priority := 100) CuspFormClass.cuspForm : CuspFormClass (CuspForm Γ k) Γ k where
  slash_action_eq f := f.slash_action_eq'
  holo := CuspForm.holo'
  zero_at_cusps := CuspForm.zero_at_cusps'

initialize_simps_projections ModularForm (toFun -> coe, as_prefix coe)

initialize_simps_projections CuspForm (toFun -> coe, as_prefix coe)

variable {F Γ k}

/-- Build a `ModularForm Γ k` from any element of a type carrying a `ModularFormClass Γ k`
instance. -/
@[simps -fullyApplied]
/--
Definition of `ModularFormClass.modularForm` / `ModularFormClass.modularForm` 的定义

English:
definition ModularFormClass.modularForm
  signature: [FunLike F ℍ Complex] [ModularFormClass F Γ k] (f : F)
  body: f
  slash_action_eq' := SlashInvariantFormClass.slash_action_eq f
  holo' := ModularFormClass.holo f
  bdd_at_cusps' := ModularFormClass.bdd_at_cusps f

中文:
定义 ModularFormClass.modularForm
  签名: [FunLike F ℍ Complex] [ModularFormClass F Γ k] (f : F)
  定义体: f
  slash_action_eq' := SlashInvariantFormClass.slash_action_eq f
  holo' := ModularFormClass.holo f
  bdd_at_cusps' := ModularFormClass.bdd_at_cusps f
-/
def ModularFormClass.modularForm [FunLike F ℍ Complex] [ModularFormClass F Γ k] (f : F) :
    ModularForm Γ k where
  toFun := f
  slash_action_eq' := SlashInvariantFormClass.slash_action_eq f
  holo' := ModularFormClass.holo f
  bdd_at_cusps' := ModularFormClass.bdd_at_cusps f

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [FunLike
  signature: F ℍ Complex] [ModularFormClass F Γ k] : CoeTC F (ModularForm Γ k)
  body: ⟨ModularFormClass.modularForm⟩

中文:
实例 [FunLike
  签名: F ℍ Complex] [ModularFormClass F Γ k] : CoeTC F (ModularForm Γ k)
  定义体: ⟨ModularFormClass.modularForm⟩

Depends on / 依赖: ModularFormClass, ModularFormClass.modularForm, modularForm
-/
instance [FunLike F ℍ Complex] [ModularFormClass F Γ k] : CoeTC F (ModularForm Γ k) :=
  ⟨ModularFormClass.modularForm⟩

/--
theorem `ModularForm.toFun_eq_coe` / 定理 `ModularForm.toFun_eq_coe`

English:
theorem ModularForm.toFun_eq_coe
  given: (f : ModularForm Γ k)
  statement: f.toFun = (f : ℍ -> Complex)
  proof: rfl

@[simp]

中文:
定理 ModularForm.toFun_eq_coe
  条件: (f : ModularForm Γ k)
  结论: f.toFun = (f : ℍ -> Complex)
  证明: rfl

@[simp]
-/
theorem ModularForm.toFun_eq_coe (f : ModularForm Γ k) : f.toFun = (f : ℍ -> Complex) :=
  rfl

@[simp]
/--
theorem `ModularForm.toSlashInvariantForm_coe` / 定理 `ModularForm.toSlashInvariantForm_coe`

English:
theorem ModularForm.toSlashInvariantForm_coe
  given: (f : ModularForm Γ k)
  statement: ⇑f.1 = f
  proof: rfl

中文:
定理 ModularForm.toSlashInvariantForm_coe
  条件: (f : ModularForm Γ k)
  结论: ⇑f.1 = f
  证明: rfl
-/
theorem ModularForm.toSlashInvariantForm_coe (f : ModularForm Γ k) : ⇑f.1 = f :=
  rfl

/--
theorem `CuspForm.toFun_eq_coe` / 定理 `CuspForm.toFun_eq_coe`

English:
theorem CuspForm.toFun_eq_coe
  given: {f : CuspForm Γ k}
  statement: f.toFun = (f : ℍ -> Complex)
  proof: rfl

@[simp]

中文:
定理 CuspForm.toFun_eq_coe
  条件: {f : CuspForm Γ k}
  结论: f.toFun = (f : ℍ -> Complex)
  证明: rfl

@[simp]
-/
theorem CuspForm.toFun_eq_coe {f : CuspForm Γ k} : f.toFun = (f : ℍ -> Complex) :=
  rfl

@[simp]
/--
theorem `CuspForm.toSlashInvariantForm_coe` / 定理 `CuspForm.toSlashInvariantForm_coe`

English:
theorem CuspForm.toSlashInvariantForm_coe
  given: (f : CuspForm Γ k)
  statement: ⇑f.1 = f
  proof: rfl

@[ext]

中文:
定理 CuspForm.toSlashInvariantForm_coe
  条件: (f : CuspForm Γ k)
  结论: ⇑f.1 = f
  证明: rfl

@[ext]
-/
theorem CuspForm.toSlashInvariantForm_coe (f : CuspForm Γ k) : ⇑f.1 = f := rfl

@[ext]
/--
theorem `ModularForm.ext` / 定理 `ModularForm.ext`

English:
theorem ModularForm.ext
  given: {f g : ModularForm Γ k} (h : forall x, f x = g x)
  statement: f = g
  proof: DFunLike.ext f g h

@[ext]

中文:
定理 ModularForm.ext
  条件: {f g : ModularForm Γ k} (h : 对任意 x, f x = g x)
  结论: f = g
  证明: DFunLike.ext f g h

@[ext]

Depends on / 依赖: DFunLike, DFunLike.ext
-/
theorem ModularForm.ext {f g : ModularForm Γ k} (h : forall x, f x = g x) : f = g :=
  DFunLike.ext f g h

@[ext]
/--
theorem `CuspForm.ext` / 定理 `CuspForm.ext`

English:
theorem CuspForm.ext
  given: {f g : CuspForm Γ k} (h : forall x, f x = g x)
  statement: f = g
  proof: DFunLike.ext f g h

中文:
定理 CuspForm.ext
  条件: {f g : CuspForm Γ k} (h : 对任意 x, f x = g x)
  结论: f = g
  证明: DFunLike.ext f g h

Depends on / 依赖: DFunLike, DFunLike.ext
-/
theorem CuspForm.ext {f g : CuspForm Γ k} (h : forall x, f x = g x) : f = g :=
  DFunLike.ext f g h

/--
Definition of `ModularForm.copy` / `ModularForm.copy` 的定义

English:
definition ModularForm.copy
  signature: {Γ' : Subgroup (GL (Fin 2) Real)} (f : ModularForm Γ k) (f' : ℍ -> Complex)
  body: f'
  slash_action_eq' A hA := h.symm ▸ f.slash_action_eq' A (hΓ ▸ hA)
  holo' := h.symm ▸ f.holo'
  bdd_at_cusps' hc := h.symm ▸ f.bdd_at_cusps' (hΓ ▸ hc)

中文:
定义 ModularForm.copy
  签名: {Γ' : Subgroup (GL (Fin 2) 实数)} (f : ModularForm Γ k) (f' : ℍ -> Complex)
  定义体: f'
  slash_action_eq' A hA := h.symm ▸ f.slash_action_eq' A (hΓ ▸ hA)
  holo' := h.symm ▸ f.holo'
  bdd_at_cusps' hc := h.symm ▸ f.bdd_at_cusps' (hΓ ▸ hc)
-/
protected def ModularForm.copy {Γ' : Subgroup (GL (Fin 2) Real)} (f : ModularForm Γ k) (f' : ℍ -> Complex)
    (h : f' = ⇑f) (hΓ : Γ' = Γ := by rfl) : ModularForm Γ' k where
  toFun := f'
  slash_action_eq' A hA := h.symm ▸ f.slash_action_eq' A (hΓ ▸ hA)
  holo' := h.symm ▸ f.holo'
  bdd_at_cusps' hc := h.symm ▸ f.bdd_at_cusps' (hΓ ▸ hc)

/--
Definition of `CuspForm.copy` / `CuspForm.copy` 的定义

English:
definition CuspForm.copy
  signature: {Γ' : Subgroup (GL (Fin 2) Real)} (f : CuspForm Γ k) (f' : ℍ -> Complex)
  body: f'
  slash_action_eq' A hA := h.symm ▸ f.slash_action_eq' A (hΓ ▸ hA)
  holo' := h.symm ▸ f.holo'
  zero_at_cusps' hc := h.symm ▸ f.zero_at_cusps' (hΓ ▸ hc)

中文:
定义 CuspForm.copy
  签名: {Γ' : Subgroup (GL (Fin 2) 实数)} (f : CuspForm Γ k) (f' : ℍ -> Complex)
  定义体: f'
  slash_action_eq' A hA := h.symm ▸ f.slash_action_eq' A (hΓ ▸ hA)
  holo' := h.symm ▸ f.holo'
  zero_at_cusps' hc := h.symm ▸ f.zero_at_cusps' (hΓ ▸ hc)
-/
protected def CuspForm.copy {Γ' : Subgroup (GL (Fin 2) Real)} (f : CuspForm Γ k) (f' : ℍ -> Complex)
    (h : f' = ⇑f) (hΓ : Γ' = Γ := by rfl) : CuspForm Γ' k where
  toFun := f'
  slash_action_eq' A hA := h.symm ▸ f.slash_action_eq' A (hΓ ▸ hA)
  holo' := h.symm ▸ f.holo'
  zero_at_cusps' hc := h.symm ▸ f.zero_at_cusps' (hΓ ▸ hc)

end ModularForm

namespace ModularForm

open SlashInvariantForm

variable {Γ : Subgroup (GL (Fin 2) Real)} {k : Int}

/--
Instance `add` / 实例 `add`

English:
instance add
  signature: : Add (ModularForm Γ k) where add f g
  body: { toSlashInvariantForm := f + g
    holo' := f.holo'.add g.holo'
    bdd_at_cusps' hc := by simpa using (f.bdd_at_cusps' hc).add (g.bdd_at_cusps' hc) }

中文:
实例 add
  签名: : Add (ModularForm Γ k) where add f g
  定义体: { toSlashInvariantForm := f + g
    holo' := f.holo'.add g.holo'
    bdd_at_cusps' hc := by simpa using (f.bdd_at_cusps' hc).add (g.bdd_at_cusps' hc) }

Depends on / 依赖: bdd_at_cusps, f.bdd_at_cusps, f.holo, g.bdd_at_cusps, g.holo, toSlashInvariantForm
-/
instance add : Add (ModularForm Γ k) where add f g :=
  { toSlashInvariantForm := f + g
    holo' := f.holo'.add g.holo'
    bdd_at_cusps' hc := by simpa using (f.bdd_at_cusps' hc).add (g.bdd_at_cusps' hc) }

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: IsAddApply (ModularForm Γ k) ℍ Complex
  body: rfl

@[deprecated (since := "2026-07-10")] alias coe_add := FunLike.coe_add

@[deprecated (since := "2026-07-10")] protected alias add_apply := add_apply

中文:
实例 :
  签名: IsAddApply (ModularForm Γ k) ℍ Complex
  定义体: rfl

@[deprecated (since := "2026-07-10")] alias coe_add := FunLike.coe_add

@[deprecated (since := "2026-07-10")] protected alias add_apply := add_apply
-/
instance : IsAddApply (ModularForm Γ k) ℍ Complex where
  add_apply _ _ _ := rfl

@[deprecated (since := "2026-07-10")] alias coe_add := FunLike.coe_add

@[deprecated (since := "2026-07-10")] protected alias add_apply := add_apply

/--
Instance `instZero` / 实例 `instZero`

English:
instance instZero
  signature: : Zero (ModularForm Γ k)
  body: ⟨ { toSlashInvariantForm := 0
      holo' := fun _ => mdifferentiableAt_const
      bdd_at_cusps' hc g hg := by simpa using zero_form_isBoundedAtImInfty } ⟩

中文:
实例 instZero
  签名: : Zero (ModularForm Γ k)
  定义体: ⟨ { toSlashInvariantForm := 0
      holo' := fun _ => mdifferentiableAt_const
      bdd_at_cusps' hc g hg := by simpa using zero_form_isBoundedAtImInfty } ⟩

Depends on / 依赖: bdd_at_cusps, mdifferentiableAt_const, toSlashInvariantForm, zero_form_isBoundedAtImInfty
-/
instance instZero : Zero (ModularForm Γ k) :=
  ⟨ { toSlashInvariantForm := 0
      holo' := fun _ => mdifferentiableAt_const
      bdd_at_cusps' hc g hg := by simpa using zero_form_isBoundedAtImInfty } ⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: IsZeroApply (ModularForm Γ k) ℍ Complex
  body: rfl

@[deprecated (since := "2026-07-10")] alias coe_zero := FunLike.coe_zero

@[deprecated (since := "2026-07-10")] protected alias zero_apply := zero_apply

@[deprecated (since := "2026-07-10")] alias coe_eq_zero_iff := FunLike.coe_zero_iff

中文:
实例 :
  签名: IsZeroApply (ModularForm Γ k) ℍ Complex
  定义体: rfl

@[deprecated (since := "2026-07-10")] alias coe_zero := FunLike.coe_zero

@[deprecated (since := "2026-07-10")] protected alias zero_apply := zero_apply

@[deprecated (since := "2026-07-10")] alias coe_eq_zero_iff := FunLike.coe_zero_iff
-/
instance : IsZeroApply (ModularForm Γ k) ℍ Complex where
  zero_apply _ := rfl

@[deprecated (since := "2026-07-10")] alias coe_zero := FunLike.coe_zero

@[deprecated (since := "2026-07-10")] protected alias zero_apply := zero_apply

@[deprecated (since := "2026-07-10")] alias coe_eq_zero_iff := FunLike.coe_zero_iff

/--
lemma `eq_zero_of_neg_one_mem` / 引理 `eq_zero_of_neg_one_mem`

English:
lemma eq_zero_of_neg_one_mem
  statement: [Γ.HasDetOne] (h_neg_one : -1 in Γ) (hk : Odd k)
  proof: by
  ext z
  have hf := slash_action_eqn'' f h_neg_one z
  rw [neg_smul]; rw [one_smul]; rw [denom_neg]; rw [denom_one]; rw [hk.neg_one_zpow] at hf
  have h2 : (2 : Complex) * f z = 0 := by linear_combination hf
  exact (mul_eq_zero.mp h2).resolve_left (by norm_num)

中文:
引理 eq_zero_of_neg_one_mem
  结论: [Γ.HasDetOne] (h_neg_one : -1 in Γ) (hk : Odd k)
  证明: by
  ext z
  have hf := slash_action_eqn'' f h_neg_one z
  rw [neg_smul]; rw [one_smul]; rw [denom_neg]; rw [denom_one]; rw [hk.neg_one_zpow] at hf
  have h2 : (2 : Complex) * f z = 0 := by linear_combination hf
  exact (mul_eq_zero.mp h2).resolve_left (by norm_num)

Depends on / 依赖: denom_neg, denom_one, h_neg_one, hk.neg_one_zpow, linear_combination, mul_eq_zero, mul_eq_zero.mp, neg_one_zpow, neg_smul, one_smul, resolve_left, slash_action_eqn
-/
lemma eq_zero_of_neg_one_mem [Γ.HasDetOne] (h_neg_one : -1 in Γ) (hk : Odd k)
    (f : ModularForm Γ k) : f = 0 := by
  ext z
  have hf := slash_action_eqn'' f h_neg_one z
  rw [neg_smul]; rw [one_smul]; rw [denom_neg]; rw [denom_one]; rw [hk.neg_one_zpow] at hf
  have h2 : (2 : Complex) * f z = 0 := by linear_combination hf
  exact (mul_eq_zero.mp h2).resolve_left (by norm_num)

section
-- scalar multiplication by real types (no assumption on `Γ`)

variable {α : Type*} [SMul α Real] [SMul α Complex] [IsScalarTower α Real Complex]

local instance : IsScalarTower α Complex Complex where
  smul_assoc a y z := by simpa using smul_assoc (a • (1 : Real)) y z

/--
Instance `instSMulReal` / 实例 `instSMulReal`

English:
instance instSMulReal
  signature: : SMul α (ModularForm Γ k) where
  body: { toSlashInvariantForm := c • f.1
    holo' := by simpa using f.holo'.const_smul (c • (1 : Complex))
    bdd_at_cusps' hc g hg := by
      simpa only [IsBoundedAtImInfty, Filter.BoundedAtFilter, SlashInvariantForm.toFun_eq_coe,
        FunLike.coe_smul, toSlashInvariantForm_coe, ← smul_one_smul Comp

中文:
实例 instSMulReal
  签名: : SMul α (ModularForm Γ k) where
  定义体: { toSlashInvariantForm := c • f.1
    holo' := by simpa using f.holo'.const_smul (c • (1 : Complex))
    bdd_at_cusps' hc g hg := by
      simpa only [IsBoundedAtImInfty, Filter.BoundedAtFilter, SlashInvariantForm.toFun_eq_coe,
        FunLike.coe_smul, toSlashInvariantForm_coe, ← smul_one_smul Comp

Depends on / 依赖: BoundedAtFilter, Filter, Filter.BoundedAtFilter, FunLike, FunLike.coe_smul, IsBoundedAtImInfty, SlashInvariantForm, SlashInvariantForm.toFun_eq_coe, bdd_at_cusps, coe_smul, const_smul, const_smul_left, f.bdd_at_cusps, f.holo, smul_one_smul, smul_slash, toFun_eq_coe, toSlashInvariantForm, toSlashInvariantForm_coe
-/
instance instSMulReal : SMul α (ModularForm Γ k) where
  smul c f :=
  { toSlashInvariantForm := c • f.1
    holo' := by simpa using f.holo'.const_smul (c • (1 : Complex))
    bdd_at_cusps' hc g hg := by
      simpa only [IsBoundedAtImInfty, Filter.BoundedAtFilter, SlashInvariantForm.toFun_eq_coe,
        FunLike.coe_smul, toSlashInvariantForm_coe, ← smul_one_smul Complex c ⇑f, smul_slash]
        using (f.bdd_at_cusps' hc g hg).const_smul_left _ }

/--
Instance `instIsSMulApplyReal` / 实例 `instIsSMulApplyReal`

English:
instance instIsSMulApplyReal
  signature: : IsSMulApply α (ModularForm Γ k) ℍ Complex where
  body: rfl

@[deprecated (since := "2026-07-10")] alias coe_smul := FunLike.coe_smul

@[deprecated (since := "2026-07-10")] protected alias smul_apply := smul_apply

中文:
实例 instIsSMulApplyReal
  签名: : IsSMulApply α (ModularForm Γ k) ℍ Complex where
  定义体: rfl

@[deprecated (since := "2026-07-10")] alias coe_smul := FunLike.coe_smul

@[deprecated (since := "2026-07-10")] protected alias smul_apply := smul_apply
-/
instance instIsSMulApplyReal : IsSMulApply α (ModularForm Γ k) ℍ Complex where
  smul_apply _ _ _ := rfl

@[deprecated (since := "2026-07-10")] alias coe_smul := FunLike.coe_smul

@[deprecated (since := "2026-07-10")] protected alias smul_apply := smul_apply

end

section

variable {α : Type*} [SMul α Complex] [IsScalarTower α Complex Complex] [Γ.HasDetOne]

/--
Instance `instSMulComplex` / 实例 `instSMulComplex`

English:
instance instSMulComplex
  signature: : SMul α (ModularForm Γ k) where
  body: { toSlashInvariantForm := c • f.1
    holo' := by simpa using f.holo'.const_smul (c • (1 : Complex))
    bdd_at_cusps' hc g hg := by
      simp_rw [IsBoundedAtImInfty, Filter.BoundedAtFilter, SlashInvariantForm.toFun_eq_coe,
        FunLike.coe_smul, toSlashInvariantForm_coe, ← smul_one_smul Complex

中文:
实例 instSMulComplex
  签名: : SMul α (ModularForm Γ k) where
  定义体: { toSlashInvariantForm := c • f.1
    holo' := by simpa using f.holo'.const_smul (c • (1 : Complex))
    bdd_at_cusps' hc g hg := by
      simp_rw [IsBoundedAtImInfty, Filter.BoundedAtFilter, SlashInvariantForm.toFun_eq_coe,
        FunLike.coe_smul, toSlashInvariantForm_coe, ← smul_one_smul Complex

Depends on / 依赖: BoundedAtFilter, Filter, Filter.BoundedAtFilter, FunLike, FunLike.coe_smul, IsBoundedAtImInfty, SlashInvariantForm, SlashInvariantForm.toFun_eq_coe, bdd_at_cusps, coe_smul, const_smul, const_smul_left, f.bdd_at_cusps, f.holo, simp_rw, smul_one_smul, smul_slash, toFun_eq_coe, toSlashInvariantForm, toSlashInvariantForm_coe
-/
instance instSMulComplex : SMul α (ModularForm Γ k) where
  smul c f :=
  { toSlashInvariantForm := c • f.1
    holo' := by simpa using f.holo'.const_smul (c • (1 : Complex))
    bdd_at_cusps' hc g hg := by
      simp_rw [IsBoundedAtImInfty, Filter.BoundedAtFilter, SlashInvariantForm.toFun_eq_coe,
        FunLike.coe_smul, toSlashInvariantForm_coe, ← smul_one_smul Complex c ⇑f, smul_slash]
      exact (f.bdd_at_cusps' hc g hg).const_smul_left (σ g (c • (1 : Complex))) }

/--
Instance `instIsSMulApplyComplex` / 实例 `instIsSMulApplyComplex`

English:
instance instIsSMulApplyComplex
  signature: : IsSMulApply α (ModularForm Γ k) ℍ Complex where
  body: rfl

@[deprecated (since := "2026-07-10")] alias IsGLPos.coe_smul := FunLike.coe_smul

@[deprecated (since := "2026-07-10")] protected alias IsGLPos.smul_apply := smul_apply

中文:
实例 instIsSMulApplyComplex
  签名: : IsSMulApply α (ModularForm Γ k) ℍ Complex where
  定义体: rfl

@[deprecated (since := "2026-07-10")] alias IsGLPos.coe_smul := FunLike.coe_smul

@[deprecated (since := "2026-07-10")] protected alias IsGLPos.smul_apply := smul_apply
-/
instance instIsSMulApplyComplex : IsSMulApply α (ModularForm Γ k) ℍ Complex where
  smul_apply _ _ _ := rfl

@[deprecated (since := "2026-07-10")] alias IsGLPos.coe_smul := FunLike.coe_smul

@[deprecated (since := "2026-07-10")] protected alias IsGLPos.smul_apply := smul_apply

end

/--
Instance `instNeg` / 实例 `instNeg`

English:
instance instNeg
  signature: : Neg (ModularForm Γ k)
  body: ⟨fun f =>
    { toSlashInvariantForm := -f.1
      holo' := f.holo'.neg
      bdd_at_cusps' hc g hg := by simpa using! (f.bdd_at_cusps' hc g hg).neg }⟩

中文:
实例 instNeg
  签名: : Neg (ModularForm Γ k)
  定义体: ⟨fun f =>
    { toSlashInvariantForm := -f.1
      holo' := f.holo'.neg
      bdd_at_cusps' hc g hg := by simpa using! (f.bdd_at_cusps' hc g hg).neg }⟩

Depends on / 依赖: bdd_at_cusps, f.bdd_at_cusps, f.holo, toSlashInvariantForm
-/
instance instNeg : Neg (ModularForm Γ k) :=
  ⟨fun f =>
    { toSlashInvariantForm := -f.1
      holo' := f.holo'.neg
      bdd_at_cusps' hc g hg := by simpa using! (f.bdd_at_cusps' hc g hg).neg }⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: IsNegApply (ModularForm Γ k) ℍ Complex
  body: rfl

@[deprecated (since := "2026-07-10")] alias coe_neg := FunLike.coe_neg

@[deprecated (since := "2026-07-10")] protected alias neg_apply := neg_apply

中文:
实例 :
  签名: IsNegApply (ModularForm Γ k) ℍ Complex
  定义体: rfl

@[deprecated (since := "2026-07-10")] alias coe_neg := FunLike.coe_neg

@[deprecated (since := "2026-07-10")] protected alias neg_apply := neg_apply
-/
instance : IsNegApply (ModularForm Γ k) ℍ Complex where
  neg_apply _ _ := rfl

@[deprecated (since := "2026-07-10")] alias coe_neg := FunLike.coe_neg

@[deprecated (since := "2026-07-10")] protected alias neg_apply := neg_apply

/--
Instance `instSub` / 实例 `instSub`

English:
instance instSub
  signature: : Sub (ModularForm Γ k)
  body: ⟨fun f g => f + -g⟩

中文:
实例 instSub
  签名: : Sub (ModularForm Γ k)
  定义体: ⟨fun f g => f + -g⟩
-/
instance instSub : Sub (ModularForm Γ k) :=
  ⟨fun f g => f + -g⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: IsSubApply (ModularForm Γ k) ℍ Complex
  body: rfl

@[deprecated (since := "2026-07-10")] alias coe_sub := FunLike.coe_sub

@[deprecated (since := "2026-07-10")] protected alias sub_apply := sub_apply

中文:
实例 :
  签名: IsSubApply (ModularForm Γ k) ℍ Complex
  定义体: rfl

@[deprecated (since := "2026-07-10")] alias coe_sub := FunLike.coe_sub

@[deprecated (since := "2026-07-10")] protected alias sub_apply := sub_apply
-/
instance : IsSubApply (ModularForm Γ k) ℍ Complex where
  sub_apply _ _ _ := rfl

@[deprecated (since := "2026-07-10")] alias coe_sub := FunLike.coe_sub

@[deprecated (since := "2026-07-10")] protected alias sub_apply := sub_apply

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: AddCommGroup (ModularForm Γ k)
  body: fast_instance% FunLike.addCommGroup

@[deprecated (since := "2026-07-10")] alias coeHom := FunLike.coeMonoidHom

中文:
实例 :
  签名: AddCommGroup (ModularForm Γ k)
  定义体: fast_instance% FunLike.addCommGroup

@[deprecated (since := "2026-07-10")] alias coeHom := FunLike.coeMonoidHom

Depends on / 依赖: FunLike, FunLike.addCommGroup, addCommGroup, fast_instance
-/
instance : AddCommGroup (ModularForm Γ k) := fast_instance% FunLike.addCommGroup

@[deprecated (since := "2026-07-10")] alias coeHom := FunLike.coeMonoidHom

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Module Real (ModularForm Γ k)
  body: fast_instance% FunLike.module

中文:
实例 :
  签名: Module 实数 (ModularForm Γ k)
  定义体: fast_instance% FunLike.module

Depends on / 依赖: FunLike, FunLike.module, fast_instance, module
-/
instance : Module Real (ModularForm Γ k) := fast_instance% FunLike.module

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Γ.HasDetOne]
  signature: : Module Complex (ModularForm Γ k)
  body: fast_instance% FunLike.module

中文:
实例 [Γ.HasDetOne]
  签名: : Module Complex (ModularForm Γ k)
  定义体: fast_instance% FunLike.module

Depends on / 依赖: FunLike, FunLike.module, fast_instance, module
-/
instance [Γ.HasDetOne] : Module Complex (ModularForm Γ k) := fast_instance% FunLike.module

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Inhabited (ModularForm Γ k)
  body: ⟨0⟩

中文:
实例 :
  签名: Inhabited (ModularForm Γ k)
  定义体: ⟨0⟩
-/
instance : Inhabited (ModularForm Γ k) :=
  ⟨0⟩

/-- The modular form of weight `k_1 + k_2` given by the product of two modular forms of weights
`k_1` and `k_2`. -/
@[simps! -fullyApplied coe]
/--
Definition of `mul` / `mul` 的定义

English:
definition mul
  signature: {k_1 k_2 : Int} [Γ.HasDetPlusMinusOne] (f : ModularForm Γ k_1) (g : ModularForm Γ k_2)
  body: f.1.mul g.1
  holo' := f.holo'.mul g.holo'
  bdd_at_cusps' hc γ hγ := by
    simpa [mul_slash] using! ((f.bdd_at_cusps' hc γ hγ).mul (g.bdd_at_cusps' hc γ hγ)).smul _

中文:
定义 mul
  签名: {k_1 k_2 : 整数} [Γ.HasDetPlusMinusOne] (f : ModularForm Γ k_1) (g : ModularForm Γ k_2)
  定义体: f.1.mul g.1
  holo' := f.holo'.mul g.holo'
  bdd_at_cusps' hc γ hγ := by
    simpa [mul_slash] using! ((f.bdd_at_cusps' hc γ hγ).mul (g.bdd_at_cusps' hc γ hγ)).smul _
-/
def mul {k_1 k_2 : Int} [Γ.HasDetPlusMinusOne] (f : ModularForm Γ k_1) (g : ModularForm Γ k_2) :
    ModularForm Γ (k_1 + k_2) where
  toSlashInvariantForm := f.1.mul g.1
  holo' := f.holo'.mul g.holo'
  bdd_at_cusps' hc γ hγ := by
    simpa [mul_slash] using! ((f.bdd_at_cusps' hc γ hγ).mul (g.bdd_at_cusps' hc γ hγ)).smul _

/--
Definition of `const` / `const` 的定义

English:
definition const
  signature: (x : Complex) [Γ.HasDetOne]
  body: .const x
  holo' _ := mdifferentiableAt_const
  bdd_at_cusps' hc g hg := by simpa only [coe_const, slash_def, SlashInvariantForm.toFun_eq_coe,
      Function.const_apply, neg_zero, zpow_zero] using! atImInfty.const_boundedAtFilter _

@[simp]

中文:
定义 const
  签名: (x : Complex) [Γ.HasDetOne]
  定义体: .const x
  holo' _ := mdifferentiableAt_const
  bdd_at_cusps' hc g hg := by simpa only [coe_const, slash_def, SlashInvariantForm.toFun_eq_coe,
      Function.const_apply, neg_zero, zpow_zero] using! atImInfty.const_boundedAtFilter _

@[simp]
-/
@[simps! -fullyApplied] def const (x : Complex) [Γ.HasDetOne] : ModularForm Γ 0 where
  toSlashInvariantForm := .const x
  holo' _ := mdifferentiableAt_const
  bdd_at_cusps' hc g hg := by simpa only [coe_const, slash_def, SlashInvariantForm.toFun_eq_coe,
      Function.const_apply, neg_zero, zpow_zero] using! atImInfty.const_boundedAtFilter _

@[simp]
/--
lemma `const_apply` / 引理 `const_apply`

English:
lemma const_apply
  given: [Γ.HasDetOne] (x : Complex) (τ : ℍ)
  statement: (const x : ModularForm Γ 0) τ = x
  proof: rfl

中文:
引理 const_apply
  条件: [Γ.HasDetOne] (x : Complex) (τ : ℍ)
  结论: (const x : ModularForm Γ 0) τ = x
  证明: rfl
-/
lemma const_apply [Γ.HasDetOne] (x : Complex) (τ : ℍ) : (const x : ModularForm Γ 0) τ = x := rfl

/--
Definition of `constReal` / `constReal` 的定义

English:
definition constReal
  signature: (x : Real) [Γ.HasDetPlusMinusOne]
  body: .constReal x
  holo' _ := mdifferentiableAt_const
  bdd_at_cusps' hc g hg := by simpa only [coe_constReal, slash_def, SlashInvariantForm.toFun_eq_coe,
      Function.const_apply, neg_zero, zpow_zero] using! atImInfty.const_boundedAtFilter _

@[simp]

中文:
定义 constReal
  签名: (x : 实数) [Γ.HasDetPlusMinusOne]
  定义体: .constReal x
  holo' _ := mdifferentiableAt_const
  bdd_at_cusps' hc g hg := by simpa only [coe_constReal, slash_def, SlashInvariantForm.toFun_eq_coe,
      Function.const_apply, neg_zero, zpow_zero] using! atImInfty.const_boundedAtFilter _

@[simp]
-/
@[simps! -fullyApplied coe] def constReal (x : Real) [Γ.HasDetPlusMinusOne] : ModularForm Γ 0 where
  toSlashInvariantForm := .constReal x
  holo' _ := mdifferentiableAt_const
  bdd_at_cusps' hc g hg := by simpa only [coe_constReal, slash_def, SlashInvariantForm.toFun_eq_coe,
      Function.const_apply, neg_zero, zpow_zero] using! atImInfty.const_boundedAtFilter _

@[simp]
/--
lemma `constReal_apply` / 引理 `constReal_apply`

English:
lemma constReal_apply
  given: [Γ.HasDetPlusMinusOne] (x : Real) (τ : ℍ)
  proof: rfl

中文:
引理 constReal_apply
  条件: [Γ.HasDetPlusMinusOne] (x : 实数) (τ : ℍ)
  证明: rfl
-/
lemma constReal_apply [Γ.HasDetPlusMinusOne] (x : Real) (τ : ℍ) :
    (constReal x : ModularForm Γ 0) τ = x :=
  rfl

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Γ.HasDetPlusMinusOne]
  signature: : One (ModularForm Γ 0) where
  body: { constReal 1 with toSlashInvariantForm := 1 }

@[simp]

中文:
实例 [Γ.HasDetPlusMinusOne]
  签名: : One (ModularForm Γ 0) where
  定义体: { constReal 1 with toSlashInvariantForm := 1 }

@[simp]

Depends on / 依赖: constReal, toSlashInvariantForm
-/
instance [Γ.HasDetPlusMinusOne] : One (ModularForm Γ 0) where
  one := { constReal 1 with toSlashInvariantForm := 1 }

@[simp]
/--
theorem `one_coe_eq_one` / 定理 `one_coe_eq_one`

English:
theorem one_coe_eq_one
  given: [Γ.HasDetPlusMinusOne]
  statement: ⇑(1 : ModularForm Γ 0) = 1
  proof: rfl

中文:
定理 one_coe_eq_one
  条件: [Γ.HasDetPlusMinusOne]
  结论: ⇑(1 : ModularForm Γ 0) = 1
  证明: rfl
-/
theorem one_coe_eq_one [Γ.HasDetPlusMinusOne] : ⇑(1 : ModularForm Γ 0) = 1 :=
  rfl

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Γ.HasDetPlusMinusOne]
  signature: : NatCast (ModularForm Γ 0) where
  body: constReal n

@[simp, norm_cast]

中文:
实例 [Γ.HasDetPlusMinusOne]
  签名: : 自然数Cast (ModularForm Γ 0) where
  定义体: constReal n

@[simp, norm_cast]

Depends on / 依赖: constReal
-/
instance [Γ.HasDetPlusMinusOne] : NatCast (ModularForm Γ 0) where
  natCast n := constReal n

@[simp, norm_cast]
/--
lemma `coe_natCast` / 引理 `coe_natCast`

English:
lemma coe_natCast
  given: [Γ.HasDetPlusMinusOne] (n : Nat)
  proof: rfl

中文:
引理 coe_natCast
  条件: [Γ.HasDetPlusMinusOne] (n : 自然数)
  证明: rfl
-/
lemma coe_natCast [Γ.HasDetPlusMinusOne] (n : Nat) :
    ⇑(n : ModularForm Γ 0) = n := rfl

/--
lemma `toSlashInvariantForm_natCast` / 引理 `toSlashInvariantForm_natCast`

English:
lemma toSlashInvariantForm_natCast
  given: [Γ.HasDetPlusMinusOne] (n : Nat)
  proof: rfl

中文:
引理 toSlashInvariantForm_natCast
  条件: [Γ.HasDetPlusMinusOne] (n : 自然数)
  证明: rfl
-/
lemma toSlashInvariantForm_natCast [Γ.HasDetPlusMinusOne] (n : Nat) :
    (n : ModularForm Γ 0).toSlashInvariantForm = n := rfl

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Γ.HasDetPlusMinusOne]
  signature: : IntCast (ModularForm Γ 0) where
  body: constReal z

@[simp, norm_cast]

中文:
实例 [Γ.HasDetPlusMinusOne]
  签名: : 整数Cast (ModularForm Γ 0) where
  定义体: constReal z

@[simp, norm_cast]

Depends on / 依赖: constReal
-/
instance [Γ.HasDetPlusMinusOne] : IntCast (ModularForm Γ 0) where
  intCast z := constReal z

@[simp, norm_cast]
/--
lemma `coe_intCast` / 引理 `coe_intCast`

English:
lemma coe_intCast
  given: [Γ.HasDetPlusMinusOne] (z : Int)
  proof: rfl

中文:
引理 coe_intCast
  条件: [Γ.HasDetPlusMinusOne] (z : 整数)
  证明: rfl
-/
lemma coe_intCast [Γ.HasDetPlusMinusOne] (z : Int) :
    ⇑(z : ModularForm Γ 0) = z := rfl

/--
lemma `toSlashInvariantForm_intCast` / 引理 `toSlashInvariantForm_intCast`

English:
lemma toSlashInvariantForm_intCast
  given: [Γ.HasDetPlusMinusOne] (z : Int)
  proof: rfl

中文:
引理 toSlashInvariantForm_intCast
  条件: [Γ.HasDetPlusMinusOne] (z : 整数)
  证明: rfl
-/
lemma toSlashInvariantForm_intCast [Γ.HasDetPlusMinusOne] (z : Int) :
    (z : ModularForm Γ 0).toSlashInvariantForm = z := rfl

end ModularForm

namespace CuspForm

open ModularForm

variable {F : Type*} {Γ : Subgroup (GL (Fin 2) Real)} {k : Int}

/--
Instance `hasAdd` / 实例 `hasAdd`

English:
instance hasAdd
  signature: : Add (CuspForm Γ k)
  body: ⟨fun f g =>
    { toSlashInvariantForm := f + g
      holo' := f.holo'.add g.holo'
      zero_at_cusps' A := by simpa using (f.zero_at_cusps' A).add (g.zero_at_cusps' A) }⟩

中文:
实例 hasAdd
  签名: : Add (CuspForm Γ k)
  定义体: ⟨fun f g =>
    { toSlashInvariantForm := f + g
      holo' := f.holo'.add g.holo'
      zero_at_cusps' A := by simpa using (f.zero_at_cusps' A).add (g.zero_at_cusps' A) }⟩

Depends on / 依赖: f.holo, f.zero_at_cusps, g.holo, g.zero_at_cusps, toSlashInvariantForm, zero_at_cusps
-/
instance hasAdd : Add (CuspForm Γ k) :=
  ⟨fun f g =>
    { toSlashInvariantForm := f + g
      holo' := f.holo'.add g.holo'
      zero_at_cusps' A := by simpa using (f.zero_at_cusps' A).add (g.zero_at_cusps' A) }⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: IsAddApply (CuspForm Γ k) ℍ Complex
  body: rfl

@[deprecated (since := "2026-07-10")] alias coe_add := FunLike.coe_add

@[deprecated (since := "2026-07-10")] protected alias add_apply := add_apply

中文:
实例 :
  签名: IsAddApply (CuspForm Γ k) ℍ Complex
  定义体: rfl

@[deprecated (since := "2026-07-10")] alias coe_add := FunLike.coe_add

@[deprecated (since := "2026-07-10")] protected alias add_apply := add_apply
-/
instance : IsAddApply (CuspForm Γ k) ℍ Complex where
  add_apply _ _ _ := rfl

@[deprecated (since := "2026-07-10")] alias coe_add := FunLike.coe_add

@[deprecated (since := "2026-07-10")] protected alias add_apply := add_apply

/--
Instance `instZero` / 实例 `instZero`

English:
instance instZero
  signature: : Zero (CuspForm Γ k)
  body: ⟨ { toSlashInvariantForm := 0
      holo' := fun _ => mdifferentiableAt_const
      zero_at_cusps' hc g hg := by simpa using! Filter.zero_zeroAtFilter _ } ⟩

中文:
实例 instZero
  签名: : Zero (CuspForm Γ k)
  定义体: ⟨ { toSlashInvariantForm := 0
      holo' := fun _ => mdifferentiableAt_const
      zero_at_cusps' hc g hg := by simpa using! Filter.zero_zeroAtFilter _ } ⟩

Depends on / 依赖: Filter, Filter.zero_zeroAtFilter, mdifferentiableAt_const, toSlashInvariantForm, zero_at_cusps, zero_zeroAtFilter
-/
instance instZero : Zero (CuspForm Γ k) :=
  ⟨ { toSlashInvariantForm := 0
      holo' := fun _ => mdifferentiableAt_const
      zero_at_cusps' hc g hg := by simpa using! Filter.zero_zeroAtFilter _ } ⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: IsZeroApply (CuspForm Γ k) ℍ Complex
  body: rfl

@[deprecated (since := "2026-07-10")] alias coe_zero := FunLike.coe_zero

@[deprecated (since := "2026-07-10")] protected alias zero_apply := zero_apply

中文:
实例 :
  签名: IsZeroApply (CuspForm Γ k) ℍ Complex
  定义体: rfl

@[deprecated (since := "2026-07-10")] alias coe_zero := FunLike.coe_zero

@[deprecated (since := "2026-07-10")] protected alias zero_apply := zero_apply
-/
instance : IsZeroApply (CuspForm Γ k) ℍ Complex where
  zero_apply _ := rfl

@[deprecated (since := "2026-07-10")] alias coe_zero := FunLike.coe_zero

@[deprecated (since := "2026-07-10")] protected alias zero_apply := zero_apply

section
-- scalar multiplication by real types (no assumption on `Γ`)

variable {α : Type*} [SMul α Real] [SMul α Complex] [IsScalarTower α Real Complex]

local instance : IsScalarTower α Complex Complex where
  smul_assoc a y z := by simpa using smul_assoc (a • (1 : Real)) y z

/--
Instance `instSMul` / 实例 `instSMul`

English:
instance instSMul
  signature: : SMul α (CuspForm Γ k) where smul c f
  body: { toSlashInvariantForm := c • f.1
    holo' := by simpa using f.holo'.const_smul (c • (1 : Complex))
    zero_at_cusps' hc g hg := by
      simp_rw [IsZeroAtImInfty, Filter.ZeroAtFilter, SlashInvariantForm.toFun_eq_coe,
        FunLike.coe_smul, toSlashInvariantForm_coe, ← smul_one_smul Complex c ⇑f

中文:
实例 instSMul
  签名: : SMul α (CuspForm Γ k) where smul c f
  定义体: { toSlashInvariantForm := c • f.1
    holo' := by simpa using f.holo'.const_smul (c • (1 : Complex))
    zero_at_cusps' hc g hg := by
      simp_rw [IsZeroAtImInfty, Filter.ZeroAtFilter, SlashInvariantForm.toFun_eq_coe,
        FunLike.coe_smul, toSlashInvariantForm_coe, ← smul_one_smul Complex c ⇑f

Depends on / 依赖: Filter, Filter.ZeroAtFilter, FunLike, FunLike.coe_smul, IsZeroAtImInfty, SlashInvariantForm, SlashInvariantForm.toFun_eq_coe, ZeroAtFilter, coe_smul, const_smul, f.holo, f.zero_at_cusps, simp_rw, smul_one_smul, smul_slash, toFun_eq_coe, toSlashInvariantForm, toSlashInvariantForm_coe, zero_at_cusps
-/
instance instSMul : SMul α (CuspForm Γ k) where smul c f :=
  { toSlashInvariantForm := c • f.1
    holo' := by simpa using f.holo'.const_smul (c • (1 : Complex))
    zero_at_cusps' hc g hg := by
      simp_rw [IsZeroAtImInfty, Filter.ZeroAtFilter, SlashInvariantForm.toFun_eq_coe,
        FunLike.coe_smul, toSlashInvariantForm_coe, ← smul_one_smul Complex c ⇑f, smul_slash]
      exact (f.zero_at_cusps' hc g hg).smul _ }

/--
Instance `instSMulApply` / 实例 `instSMulApply`

English:
instance instSMulApply
  signature: : IsSMulApply α (CuspForm Γ k) ℍ Complex where
  body: rfl

@[deprecated (since := "2026-07-10")] alias coe_smul := FunLike.coe_smul

@[deprecated (since := "2026-07-10")] protected alias smul_apply := smul_apply

中文:
实例 instSMulApply
  签名: : IsSMulApply α (CuspForm Γ k) ℍ Complex where
  定义体: rfl

@[deprecated (since := "2026-07-10")] alias coe_smul := FunLike.coe_smul

@[deprecated (since := "2026-07-10")] protected alias smul_apply := smul_apply
-/
instance instSMulApply : IsSMulApply α (CuspForm Γ k) ℍ Complex where
  smul_apply _ _ _ := rfl

@[deprecated (since := "2026-07-10")] alias coe_smul := FunLike.coe_smul

@[deprecated (since := "2026-07-10")] protected alias smul_apply := smul_apply

end

section
-- scalar multiplication by complex types (assuming `IsGLPos Γ`)

variable {α : Type*} [SMul α Complex] [IsScalarTower α Complex Complex] [Γ.HasDetOne]

/--
Instance `IsGLPos.instSMul` / 实例 `IsGLPos.instSMul`

English:
instance IsGLPos.instSMul
  signature: : SMul α (CuspForm Γ k) where smul c f
  body: { toSlashInvariantForm := c • f.1
    holo' := by simpa using f.holo'.const_smul (c • (1 : Complex))
    zero_at_cusps' hc g hg := by
      simp_rw [IsZeroAtImInfty, Filter.ZeroAtFilter, SlashInvariantForm.toFun_eq_coe,
        FunLike.coe_smul, toSlashInvariantForm_coe, ← smul_one_smul Complex c ⇑f

中文:
实例 IsGLPos.instSMul
  签名: : SMul α (CuspForm Γ k) where smul c f
  定义体: { toSlashInvariantForm := c • f.1
    holo' := by simpa using f.holo'.const_smul (c • (1 : Complex))
    zero_at_cusps' hc g hg := by
      simp_rw [IsZeroAtImInfty, Filter.ZeroAtFilter, SlashInvariantForm.toFun_eq_coe,
        FunLike.coe_smul, toSlashInvariantForm_coe, ← smul_one_smul Complex c ⇑f

Depends on / 依赖: Filter, Filter.ZeroAtFilter, FunLike, FunLike.coe_smul, IsZeroAtImInfty, SlashInvariantForm, SlashInvariantForm.toFun_eq_coe, ZeroAtFilter, coe_smul, const_smul, f.holo, f.zero_at_cusps, simp_rw, smul_one_smul, smul_slash, toFun_eq_coe, toSlashInvariantForm, toSlashInvariantForm_coe, zero_at_cusps
-/
instance IsGLPos.instSMul : SMul α (CuspForm Γ k) where smul c f :=
  { toSlashInvariantForm := c • f.1
    holo' := by simpa using f.holo'.const_smul (c • (1 : Complex))
    zero_at_cusps' hc g hg := by
      simp_rw [IsZeroAtImInfty, Filter.ZeroAtFilter, SlashInvariantForm.toFun_eq_coe,
        FunLike.coe_smul, toSlashInvariantForm_coe, ← smul_one_smul Complex c ⇑f,
        smul_slash]
      exact (f.zero_at_cusps' hc g hg).smul _ }

/--
Instance `IsGLPos.instSMulApply` / 实例 `IsGLPos.instSMulApply`

English:
instance IsGLPos.instSMulApply
  signature: : IsSMulApply α (CuspForm Γ k) ℍ Complex where
  body: rfl

@[deprecated (since := "2026-07-10")] alias IsGLPos.coe_smul := FunLike.coe_smul

@[deprecated (since := "2026-07-10")] protected alias IsGLPos.smul_apply := smul_apply

中文:
实例 IsGLPos.instSMulApply
  签名: : IsSMulApply α (CuspForm Γ k) ℍ Complex where
  定义体: rfl

@[deprecated (since := "2026-07-10")] alias IsGLPos.coe_smul := FunLike.coe_smul

@[deprecated (since := "2026-07-10")] protected alias IsGLPos.smul_apply := smul_apply
-/
instance IsGLPos.instSMulApply : IsSMulApply α (CuspForm Γ k) ℍ Complex where
  smul_apply _ _ _ := rfl

@[deprecated (since := "2026-07-10")] alias IsGLPos.coe_smul := FunLike.coe_smul

@[deprecated (since := "2026-07-10")] protected alias IsGLPos.smul_apply := smul_apply

end

/--
Instance `instNeg` / 实例 `instNeg`

English:
instance instNeg
  signature: : Neg (CuspForm Γ k)
  body: ⟨fun f =>
    { toSlashInvariantForm := -f.1
      holo' := f.holo'.neg
      zero_at_cusps' hc g hg := by simpa using! (f.zero_at_cusps' hc g hg).neg }⟩

中文:
实例 instNeg
  签名: : Neg (CuspForm Γ k)
  定义体: ⟨fun f =>
    { toSlashInvariantForm := -f.1
      holo' := f.holo'.neg
      zero_at_cusps' hc g hg := by simpa using! (f.zero_at_cusps' hc g hg).neg }⟩

Depends on / 依赖: f.holo, f.zero_at_cusps, toSlashInvariantForm, zero_at_cusps
-/
instance instNeg : Neg (CuspForm Γ k) :=
  ⟨fun f =>
    { toSlashInvariantForm := -f.1
      holo' := f.holo'.neg
      zero_at_cusps' hc g hg := by simpa using! (f.zero_at_cusps' hc g hg).neg }⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: IsNegApply (CuspForm Γ k) ℍ Complex
  body: rfl

@[deprecated (since := "2026-07-10")] alias coe_neg := FunLike.coe_neg

@[deprecated (since := "2026-07-10")] protected alias neg_apply := neg_apply

中文:
实例 :
  签名: IsNegApply (CuspForm Γ k) ℍ Complex
  定义体: rfl

@[deprecated (since := "2026-07-10")] alias coe_neg := FunLike.coe_neg

@[deprecated (since := "2026-07-10")] protected alias neg_apply := neg_apply
-/
instance : IsNegApply (CuspForm Γ k) ℍ Complex where
  neg_apply _ _ := rfl

@[deprecated (since := "2026-07-10")] alias coe_neg := FunLike.coe_neg

@[deprecated (since := "2026-07-10")] protected alias neg_apply := neg_apply

/--
Instance `instSub` / 实例 `instSub`

English:
instance instSub
  signature: : Sub (CuspForm Γ k)
  body: ⟨fun f g => f + -g⟩

中文:
实例 instSub
  签名: : Sub (CuspForm Γ k)
  定义体: ⟨fun f g => f + -g⟩
-/
instance instSub : Sub (CuspForm Γ k) :=
  ⟨fun f g => f + -g⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: IsSubApply (CuspForm Γ k) ℍ Complex
  body: rfl

@[deprecated (since := "2026-07-10")] alias coe_sub := FunLike.coe_sub

@[deprecated (since := "2026-07-10")] protected alias sub_apply := sub_apply

中文:
实例 :
  签名: IsSubApply (CuspForm Γ k) ℍ Complex
  定义体: rfl

@[deprecated (since := "2026-07-10")] alias coe_sub := FunLike.coe_sub

@[deprecated (since := "2026-07-10")] protected alias sub_apply := sub_apply
-/
instance : IsSubApply (CuspForm Γ k) ℍ Complex where
  sub_apply _ _ _ := rfl

@[deprecated (since := "2026-07-10")] alias coe_sub := FunLike.coe_sub

@[deprecated (since := "2026-07-10")] protected alias sub_apply := sub_apply

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: AddCommGroup (CuspForm Γ k)
  body: fast_instance% FunLike.addCommGroup

@[deprecated (since := "2026-07-10")] alias coeHom := FunLike.coeMonoidHom

@[deprecated (since := "2026-07-10")] alias coeHom_apply := FunLike.coeMonoidHom_apply

中文:
实例 :
  签名: AddCommGroup (CuspForm Γ k)
  定义体: fast_instance% FunLike.addCommGroup

@[deprecated (since := "2026-07-10")] alias coeHom := FunLike.coeMonoidHom

@[deprecated (since := "2026-07-10")] alias coeHom_apply := FunLike.coeMonoidHom_apply

Depends on / 依赖: FunLike, FunLike.addCommGroup, addCommGroup, fast_instance
-/
instance : AddCommGroup (CuspForm Γ k) := fast_instance% FunLike.addCommGroup

@[deprecated (since := "2026-07-10")] alias coeHom := FunLike.coeMonoidHom

@[deprecated (since := "2026-07-10")] alias coeHom_apply := FunLike.coeMonoidHom_apply

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Module Real (CuspForm Γ k)
  body: fast_instance% FunLike.module

中文:
实例 :
  签名: Module 实数 (CuspForm Γ k)
  定义体: fast_instance% FunLike.module

Depends on / 依赖: FunLike, FunLike.module, fast_instance, module
-/
instance : Module Real (CuspForm Γ k) := fast_instance% FunLike.module

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Γ.HasDetOne]
  signature: : Module Complex (CuspForm Γ k)
  body: fast_instance% FunLike.module

中文:
实例 [Γ.HasDetOne]
  签名: : Module Complex (CuspForm Γ k)
  定义体: fast_instance% FunLike.module

Depends on / 依赖: FunLike, FunLike.module, fast_instance, module
-/
instance [Γ.HasDetOne] : Module Complex (CuspForm Γ k) := fast_instance% FunLike.module

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Inhabited (CuspForm Γ k)
  body: ⟨0⟩

中文:
实例 :
  签名: Inhabited (CuspForm Γ k)
  定义体: ⟨0⟩
-/
instance : Inhabited (CuspForm Γ k) :=
  ⟨0⟩

instance (priority := 99) [FunLike F ℍ Complex] [CuspFormClass F Γ k] : ModularFormClass F Γ k where
  slash_action_eq := SlashInvariantFormClass.slash_action_eq
  holo := CuspFormClass.holo
  bdd_at_cusps f _ hc g hg := (CuspFormClass.zero_at_cusps f hc g hg).boundedAtFilter

/-- Multiplying a `CuspForm` by a `ModularForm` gives a `CuspForm` (the cusp condition is
preserved since a function tending to zero times a bounded function tends to zero). -/
@[simps! -fullyApplied coe]
/--
Definition of `mulModularForm` / `mulModularForm` 的定义

English:
definition mulModularForm
  signature: [Γ.HasDetPlusMinusOne] {k₁ k₂ : Int} (f : CuspForm Γ k₁) (g : ModularForm Γ k₂)
  body: f.1.mul g.1
  holo' := f.holo'.mul g.holo'
  zero_at_cusps' hc γ hγ := by
    simpa [mul_slash] using!
      ((f.zero_at_cusps' hc γ hγ).mul_boundedAtFilter (g.bdd_at_cusps' hc γ hγ)).smul _

中文:
定义 mulModularForm
  签名: [Γ.HasDetPlusMinusOne] {k₁ k₂ : 整数} (f : CuspForm Γ k₁) (g : ModularForm Γ k₂)
  定义体: f.1.mul g.1
  holo' := f.holo'.mul g.holo'
  zero_at_cusps' hc γ hγ := by
    simpa [mul_slash] using!
      ((f.zero_at_cusps' hc γ hγ).mul_boundedAtFilter (g.bdd_at_cusps' hc γ hγ)).smul _
-/
def mulModularForm [Γ.HasDetPlusMinusOne] {k₁ k₂ : Int} (f : CuspForm Γ k₁) (g : ModularForm Γ k₂) :
    CuspForm Γ (k₁ + k₂) where
  toSlashInvariantForm := f.1.mul g.1
  holo' := f.holo'.mul g.holo'
  zero_at_cusps' hc γ hγ := by
    simpa [mul_slash] using!
      ((f.zero_at_cusps' hc γ hγ).mul_boundedAtFilter (g.bdd_at_cusps' hc γ hγ)).smul _

/--
Definition of `mcast` / `mcast` 的定义

English:
definition mcast
  signature: {a b : Int} {Γ Γ' : Subgroup (GL (Fin 2) Real)} (h : a = b) (f : CuspForm Γ a)
  body: (f : ℍ -> Complex)
  slash_action_eq' A hA := h ▸ f.slash_action_eq' A (hΓ ▸ hA)
  holo' := f.holo'
  zero_at_cusps' hc := h ▸ f.zero_at_cusps' (hΓ ▸ hc)

中文:
定义 mcast
  签名: {a b : 整数} {Γ Γ' : Subgroup (GL (Fin 2) 实数)} (h : a = b) (f : CuspForm Γ a)
  定义体: (f : ℍ -> Complex)
  slash_action_eq' A hA := h ▸ f.slash_action_eq' A (hΓ ▸ hA)
  holo' := f.holo'
  zero_at_cusps' hc := h ▸ f.zero_at_cusps' (hΓ ▸ hc)

Depends on / 依赖: CuspForm, f.holo, f.slash_action_eq, f.zero_at_cusps, slash_action_eq, zero_at_cusps
-/
def mcast {a b : Int} {Γ Γ' : Subgroup (GL (Fin 2) Real)} (h : a = b) (f : CuspForm Γ a)
    (hΓ : Γ' = Γ := by rfl) : CuspForm Γ' b where
  toFun := (f : ℍ -> Complex)
  slash_action_eq' A hA := h ▸ f.slash_action_eq' A (hΓ ▸ hA)
  holo' := f.holo'
  zero_at_cusps' hc := h ▸ f.zero_at_cusps' (hΓ ▸ hc)

end CuspForm

namespace ModularForm

section GradedRing

/-- Cast for modular forms, which is useful for avoiding `Heq`s. Optionally transports along
an equality of subgroups. -/
@[simps -fullyApplied coe]
/--
Definition of `mcast` / `mcast` 的定义

English:
definition mcast
  signature: {a b : Int} {Γ Γ' : Subgroup (GL (Fin 2) Real)} (h : a = b) (f : ModularForm Γ a)
  body: (f : ℍ -> Complex)
  slash_action_eq' A hA := h ▸ f.slash_action_eq' A (hΓ ▸ hA)
  holo' := f.holo'
  bdd_at_cusps' hc := h ▸ f.bdd_at_cusps' (hΓ ▸ hc)

中文:
定义 mcast
  签名: {a b : 整数} {Γ Γ' : Subgroup (GL (Fin 2) 实数)} (h : a = b) (f : ModularForm Γ a)
  定义体: (f : ℍ -> Complex)
  slash_action_eq' A hA := h ▸ f.slash_action_eq' A (hΓ ▸ hA)
  holo' := f.holo'
  bdd_at_cusps' hc := h ▸ f.bdd_at_cusps' (hΓ ▸ hc)

Depends on / 依赖: ModularForm, bdd_at_cusps, f.bdd_at_cusps, f.holo, f.slash_action_eq, slash_action_eq
-/
def mcast {a b : Int} {Γ Γ' : Subgroup (GL (Fin 2) Real)} (h : a = b) (f : ModularForm Γ a)
    (hΓ : Γ' = Γ := by rfl) : ModularForm Γ' b where
  toFun := (f : ℍ -> Complex)
  slash_action_eq' A hA := h ▸ f.slash_action_eq' A (hΓ ▸ hA)
  holo' := f.holo'
  bdd_at_cusps' hc := h ▸ f.bdd_at_cusps' (hΓ ▸ hc)

/--
theorem `mcast_apply` / 定理 `mcast_apply`

English:
theorem mcast_apply
  statement: {a b : Int} {Γ Γ' : Subgroup (GL (Fin 2) Real)} (h : a = b) (f : ModularForm Γ a)
  proof: rfl

@[simp]

中文:
定理 mcast_apply
  结论: {a b : 整数} {Γ Γ' : Subgroup (GL (Fin 2) 实数)} (h : a = b) (f : ModularForm Γ a)
  证明: rfl

@[simp]
-/
theorem mcast_apply {a b : Int} {Γ Γ' : Subgroup (GL (Fin 2) Real)} (h : a = b) (f : ModularForm Γ a)
    (hΓ : Γ' = Γ := by rfl) (z : ℍ) : mcast h f hΓ z = f z := rfl

@[simp]
/--
lemma `mcast_eq_zero_iff` / 引理 `mcast_eq_zero_iff`

English:
lemma mcast_eq_zero_iff
  statement: {a b : Int} {Γ Γ' : Subgroup (GL (Fin 2) Real)} (h : a = b)
  proof: by
  simp [← FunLike.coe_zero_iff]

@[ext (iff := false)]

中文:
引理 mcast_eq_zero_iff
  结论: {a b : 整数} {Γ Γ' : Subgroup (GL (Fin 2) 实数)} (h : a = b)
  证明: by
  simp [← FunLike.coe_zero_iff]

@[ext (iff := false)]

Depends on / 依赖: FunLike, FunLike.coe_zero_iff, coe_zero_iff
-/
lemma mcast_eq_zero_iff {a b : Int} {Γ Γ' : Subgroup (GL (Fin 2) Real)} (h : a = b)
    (hΓ : Γ' = Γ) (f : ModularForm Γ a) : mcast h f hΓ = 0 ↔ f = 0 := by
  simp [← FunLike.coe_zero_iff]

@[ext (iff := false)]
/--
theorem `gradedMonoid_eq_of_cast` / 定理 `gradedMonoid_eq_of_cast`

English:
theorem gradedMonoid_eq_of_cast
  statement: {Γ : Subgroup (GL (Fin 2) Real)} {a b : GradedMonoid (ModularForm Γ)}
  proof: by
  obtain ⟨i, a⟩ := a
  cases h
  exact congr_arg _ h2

中文:
定理 gradedMonoid_eq_of_cast
  结论: {Γ : Subgroup (GL (Fin 2) 实数)} {a b : GradedMonoid (ModularForm Γ)}
  证明: by
  obtain ⟨i, a⟩ := a
  cases h
  exact congr_arg _ h2

Depends on / 依赖: congr_arg
-/
theorem gradedMonoid_eq_of_cast {Γ : Subgroup (GL (Fin 2) Real)} {a b : GradedMonoid (ModularForm Γ)}
    (h : a.fst = b.fst) (h2 : mcast h a.snd = b.snd) : a = b := by
  obtain ⟨i, a⟩ := a
  cases h
  exact congr_arg _ h2

/--
Definition of `pow` / `pow` 的定义

English:
definition pow
  signature: {Γ : Subgroup (GL (Fin 2) Real)} [Γ.HasDetPlusMinusOne] {k : Int} (f : ModularForm Γ k)
  body: n.rec (mcast (by simp) (1 : ModularForm Γ 0)) (fun n g => (g.mul f).mcast (by grind))

@[simp]

中文:
定义 pow
  签名: {Γ : Subgroup (GL (Fin 2) 实数)} [Γ.HasDetPlusMinusOne] {k : 整数} (f : ModularForm Γ k)
  定义体: n.rec (mcast (by simp) (1 : ModularForm Γ 0)) (fun n g => (g.mul f).mcast (by grind))

@[simp]

Depends on / 依赖: ModularForm, g.mul, n.rec
-/
def pow {Γ : Subgroup (GL (Fin 2) Real)} [Γ.HasDetPlusMinusOne] {k : Int} (f : ModularForm Γ k)
    (n : Nat) : ModularForm Γ (n * k) :=
  n.rec (mcast (by simp) (1 : ModularForm Γ 0)) (fun n g => (g.mul f).mcast (by grind))

@[simp]
/--
lemma `coe_pow` / 引理 `coe_pow`

English:
lemma coe_pow
  statement: {Γ : Subgroup (GL (Fin 2) Real)} [Γ.HasDetPlusMinusOne] {k : Int}
  proof: by
  induction n with
  | zero => simp [pow]
  | succ n ih => simp_all only [pow, coe_mcast, coe_mul, pow_succ]

中文:
引理 coe_pow
  结论: {Γ : Subgroup (GL (Fin 2) 实数)} [Γ.HasDetPlusMinusOne] {k : 整数}
  证明: by
  induction n with
  | zero => simp [pow]
  | succ n ih => simp_all only [pow, coe_mcast, coe_mul, pow_succ]

Depends on / 依赖: coe_mcast, coe_mul, pow_succ
-/
lemma coe_pow {Γ : Subgroup (GL (Fin 2) Real)} [Γ.HasDetPlusMinusOne] {k : Int}
    (f : ModularForm Γ k) (n : Nat) : ⇑(f.pow n) = (⇑f) ^ n := by
  induction n with
  | zero => simp [pow]
  | succ n ih => simp_all only [pow, coe_mcast, coe_mul, pow_succ]

instance (Γ : Subgroup (GL (Fin 2) Real)) [Γ.HasDetPlusMinusOne] :
    GradedMonoid.GOne (ModularForm Γ) where
  one := 1

instance (Γ : Subgroup (GL (Fin 2) Real)) [Γ.HasDetPlusMinusOne] :
    GradedMonoid.GMul (ModularForm Γ) where
  mul f g := f.mul g

/--
Instance `instGCommRing` / 实例 `instGCommRing`

English:
instance instGCommRing
  signature: (Γ : Subgroup (GL (Fin 2) Real)) [Γ.HasDetPlusMinusOne]
  body: gradedMonoid_eq_of_cast (zero_add _) (ext fun _ => one_mul _)
  mul_one _ := gradedMonoid_eq_of_cast (add_zero _) (ext fun _ => mul_one _)
  mul_assoc _ _ _ := gradedMonoid_eq_of_cast (add_assoc _ _ _) (ext fun _ => mul_assoc _ _ _)
  mul_zero {_ _} _ := ext fun _ => mul_zero _
  zero_mul {_ _} _ :=

中文:
实例 instGCommRing
  签名: (Γ : Subgroup (GL (Fin 2) 实数)) [Γ.HasDetPlusMinusOne]
  定义体: gradedMonoid_eq_of_cast (zero_add _) (ext fun _ => one_mul _)
  mul_one _ := gradedMonoid_eq_of_cast (add_zero _) (ext fun _ => mul_one _)
  mul_assoc _ _ _ := gradedMonoid_eq_of_cast (add_assoc _ _ _) (ext fun _ => mul_assoc _ _ _)
  mul_zero {_ _} _ := ext fun _ => mul_zero _
  zero_mul {_ _} _ :=

Depends on / 依赖: gradedMonoid_eq_of_cast, one_mul, zero_add
-/
instance instGCommRing (Γ : Subgroup (GL (Fin 2) Real)) [Γ.HasDetPlusMinusOne] :
    DirectSum.GCommRing (ModularForm Γ) where
  one_mul _ := gradedMonoid_eq_of_cast (zero_add _) (ext fun _ => one_mul _)
  mul_one _ := gradedMonoid_eq_of_cast (add_zero _) (ext fun _ => mul_one _)
  mul_assoc _ _ _ := gradedMonoid_eq_of_cast (add_assoc _ _ _) (ext fun _ => mul_assoc _ _ _)
  mul_zero {_ _} _ := ext fun _ => mul_zero _
  zero_mul {_ _} _ := ext fun _ => zero_mul _
  mul_add {_ _} _ _ _ := ext fun _ => mul_add _ _ _
  add_mul {_ _} _ _ _ := ext fun _ => add_mul _ _ _
  mul_comm _ _ := gradedMonoid_eq_of_cast (add_comm _ _) (ext fun _ => mul_comm _ _)
  natCast := Nat.cast
  natCast_zero := ext fun _ => Nat.cast_zero
  natCast_succ _ := ext fun _ => Nat.cast_succ _
  intCast := Int.cast
  intCast_ofNat _ := ext fun _ => AddGroupWithOne.intCast_ofNat _
  intCast_negSucc_ofNat _ := ext fun _ => AddGroupWithOne.intCast_negSucc _

/--
Instance `instGAlgebra` / 实例 `instGAlgebra`

English:
instance instGAlgebra
  signature: (Γ : Subgroup (GL (Fin 2) Real)) [Γ.HasDetOne]
  body: { toFun z := const z, map_zero' := rfl, map_add' := fun _ _ => rfl }
  map_one := rfl
  map_mul _x _y := rfl
  commutes _c _x := gradedMonoid_eq_of_cast (add_comm _ _) (ext fun _ => mul_comm _ _)
  smul_def _x _x := gradedMonoid_eq_of_cast (zero_add _).symm (ext fun _ => rfl)

中文:
实例 instGAlgebra
  签名: (Γ : Subgroup (GL (Fin 2) 实数)) [Γ.HasDetOne]
  定义体: { toFun z := const z, map_zero' := rfl, map_add' := fun _ _ => rfl }
  map_one := rfl
  map_mul _x _y := rfl
  commutes _c _x := gradedMonoid_eq_of_cast (add_comm _ _) (ext fun _ => mul_comm _ _)
  smul_def _x _x := gradedMonoid_eq_of_cast (zero_add _).symm (ext fun _ => rfl)

Depends on / 依赖: map_add, map_zero
-/
instance instGAlgebra (Γ : Subgroup (GL (Fin 2) Real)) [Γ.HasDetOne] :
    DirectSum.GAlgebra Complex (ModularForm Γ) where
  toFun := { toFun z := const z, map_zero' := rfl, map_add' := fun _ _ => rfl }
  map_one := rfl
  map_mul _x _y := rfl
  commutes _c _x := gradedMonoid_eq_of_cast (add_comm _ _) (ext fun _ => mul_comm _ _)
  smul_def _x _x := gradedMonoid_eq_of_cast (zero_add _).symm (ext fun _ => rfl)

open scoped DirectSum in
example (Γ : Subgroup (GL (Fin 2) Real)) [Γ.HasDetOne] : Algebra Complex (⨁ i, ModularForm Γ i) :=
inferInstance

/--
theorem `gnpow_eq_pow` / 定理 `gnpow_eq_pow`

English:
theorem gnpow_eq_pow
  statement: {Γ : Subgroup (GL (Fin 2) Real)} [Γ.HasDetPlusMinusOne]
  proof: by
  induction n with
  | zero =>
    refine (GradedMonoid.GMonoid.gnpow_zero' ⟨k, f⟩).trans ?_
    exact gradedMonoid_eq_of_cast (zero_mul k).symm (ModularForm.ext fun _ => rfl)
  | succ n ih =>
    refine (GradedMonoid.GMonoid.gnpow_succ' n ⟨k, f⟩).trans ?_
    refine (congrArg (fun x : GradedMono

中文:
定理 gnpow_eq_pow
  结论: {Γ : Subgroup (GL (Fin 2) 实数)} [Γ.HasDetPlusMinusOne]
  证明: by
  induction n with
  | zero =>
    refine (GradedMonoid.GMonoid.gnpow_zero' ⟨k, f⟩).trans ?_
    exact gradedMonoid_eq_of_cast (zero_mul k).symm (ModularForm.ext fun _ => rfl)
  | succ n ih =>
    refine (GradedMonoid.GMonoid.gnpow_succ' n ⟨k, f⟩).trans ?_
    refine (congrArg (fun x : GradedMono

Depends on / 依赖: GMonoid, GradedMonoid, GradedMonoid.GMonoid.gnpow_succ, GradedMonoid.GMonoid.gnpow_zero, ModularForm, ModularForm.ext, gnpow_succ, gnpow_zero, gradedMonoid_eq_of_cast, zero_mul
-/
theorem gnpow_eq_pow {Γ : Subgroup (GL (Fin 2) Real)} [Γ.HasDetPlusMinusOne]
    {k : Int} (f : ModularForm Γ k) (n : Nat) :
    (⟨n • k, GradedMonoid.GMonoid.gnpow n f⟩ : GradedMonoid (ModularForm Γ)) =
      ⟨(n : Int) * k, f.pow n⟩ := by
  induction n with
  | zero =>
    refine (GradedMonoid.GMonoid.gnpow_zero' ⟨k, f⟩).trans ?_
    exact gradedMonoid_eq_of_cast (zero_mul k).symm (ModularForm.ext fun _ => rfl)
  | succ n ih =>
    refine (GradedMonoid.GMonoid.gnpow_succ' n ⟨k, f⟩).trans ?_
    refine (congrArg (fun x : GradedMonoid (ModularForm Γ) => x * ⟨k, f⟩) ih).trans ?_
    exact gradedMonoid_eq_of_cast (show ((n : Int) * k + k = (n + 1) * k) by ring)
      (ModularForm.ext fun _ => rfl)

/--
lemma `directSum_of_pow` / 引理 `directSum_of_pow`

English:
lemma directSum_of_pow
  statement: {Γ : Subgroup (GL (Fin 2) Real)} [Γ.HasDetPlusMinusOne]
  proof: by
  grind [DirectSum.ofPow, DirectSum.of_eq_of_gradedMonoid_eq (gnpow_eq_pow f n)]

中文:
引理 directSum_of_pow
  结论: {Γ : Subgroup (GL (Fin 2) 实数)} [Γ.HasDetPlusMinusOne]
  证明: by
  grind [DirectSum.ofPow, DirectSum.of_eq_of_gradedMonoid_eq (gnpow_eq_pow f n)]

Depends on / 依赖: DirectSum, DirectSum.ofPow, DirectSum.of_eq_of_gradedMonoid_eq, gnpow_eq_pow, of_eq_of_gradedMonoid_eq
-/
lemma directSum_of_pow {Γ : Subgroup (GL (Fin 2) Real)} [Γ.HasDetPlusMinusOne]
    {k : Int} (f : ModularForm Γ k) (n : Nat) :
    (DirectSum.of (ModularForm Γ) k f) ^ n = .of (ModularForm Γ) ((n : Int) * k) (f.pow n) := by
  grind [DirectSum.ofPow, DirectSum.of_eq_of_gradedMonoid_eq (gnpow_eq_pow f n)]

open Filter SlashInvariantForm

/-- Given `ModularForm`'s `F i` of weight `k i` for `i : ι`, define the form which as a
function is a product of those indexed by `s : Finset ι` with weight `m = ∑ i ∈ s, k i`. -/
@[simps! -fullyApplied]
/--
Definition of `prod` / `prod` 的定义

English:
definition prod
  signature: {ι : Type} {s : Finset ι} {k : ι -> Int} (m : Int)
  body: SlashInvariantForm.prod m hm (fun i => (F i))
  holo' := MDifferentiable.prod (t := s) (f := fun (i : ι) => (F i).1)
      (by intro (i : ι) hi; simpa using! (F i).holo')
  bdd_at_cusps' hc γ hγ := by
    simp only [SlashInvariantForm.toFun_eq_coe, coe_prod, SlashInvariantForm.coe_mk, hm,
      prod

中文:
定义 prod
  签名: {ι : Type} {s : Finset ι} {k : ι -> 整数} (m : 整数)
  定义体: SlashInvariantForm.prod m hm (fun i => (F i))
  holo' := MDifferentiable.prod (t := s) (f := fun (i : ι) => (F i).1)
      (by intro (i : ι) hi; simpa using! (F i).holo')
  bdd_at_cusps' hc γ hγ := by
    simp only [SlashInvariantForm.toFun_eq_coe, coe_prod, SlashInvariantForm.coe_mk, hm,
      prod

Depends on / 依赖: SlashInvariantForm, SlashInvariantForm.prod
-/
def prod {ι : Type} {s : Finset ι} {k : ι -> Int} (m : Int)
    (hm : m = ∑ i in s, k i) {Γ : Subgroup (GL (Fin 2) Real)} [Γ.HasDetPlusMinusOne]
    (F : (i : ι) -> ModularForm Γ (k i)) : ModularForm Γ m where
  toSlashInvariantForm := SlashInvariantForm.prod m hm (fun i => (F i))
  holo' := MDifferentiable.prod (t := s) (f := fun (i : ι) => (F i).1)
      (by intro (i : ι) hi; simpa using! (F i).holo')
  bdd_at_cusps' hc γ hγ := by
    simp only [SlashInvariantForm.toFun_eq_coe, coe_prod, SlashInvariantForm.coe_mk, hm,
      prod_slash_sum_weights, IsBoundedAtImInfty]
    refine BoundedAtFilter.smul _ (BoundedAtFilter.prod (s := s) ?_)
    intro i hi
    simpa using! (F i).bdd_at_cusps' hc γ hγ

/-- Given `ModularForm`'s `F i` of weight `k`, define the form which as a function is a product of
those indexed by `s : Finset ι` with weight `#s * k`. -/
@[simps! -fullyApplied]
/--
Definition of `prodEqualWeights` / `prodEqualWeights` 的定义

English:
definition prodEqualWeights
  signature: {ι : Type} {s : Finset ι} {k : Int}
  body: prod (s := s) (s.card * k) (by simp) F

中文:
定义 prodEqualWeights
  签名: {ι : Type} {s : Finset ι} {k : 整数}
  定义体: prod (s := s) (s.card * k) (by simp) F

Depends on / 依赖: s.card
-/
def prodEqualWeights {ι : Type} {s : Finset ι} {k : Int}
    {Γ : Subgroup (GL (Fin 2) Real)} [Γ.HasDetPlusMinusOne]
    (F : (i : ι) -> ModularForm Γ k) : ModularForm Γ (s.card * k) :=
  prod (s := s) (s.card * k) (by simp) F

end GradedRing

end ModularForm

section translate

open ModularForm OnePoint

variable {k : Int} {Γ : Subgroup (GL (Fin 2) Real)} {F : Type*} [FunLike F ℍ Complex] (f : F)

open ConjAct Pointwise in
/--
Definition of `ModularForm.translate` / `ModularForm.translate` 的定义

English:
definition ModularForm.translate
  signature: [ModularFormClass F Γ k] (g : GL (Fin 2) Real)
  body: SlashInvariantForm.translate f g
  bdd_at_cusps' {c} hc γ hγ := by
    rw [SlashInvariantForm.toFun_eq_coe]; rw [SlashInvariantForm.coe_translate]; rw [← SlashAction.slash_mul]; rw [← isBoundedAt_infty_iff]; rw [← OnePoint.IsBoundedAt.smul_iff]
    apply ModularFormClass.bdd_at_cusps f
    simpa [mu

中文:
定义 ModularForm.translate
  签名: [ModularFormClass F Γ k] (g : GL (Fin 2) 实数)
  定义体: SlashInvariantForm.translate f g
  bdd_at_cusps' {c} hc γ hγ := by
    rw [SlashInvariantForm.toFun_eq_coe]; rw [SlashInvariantForm.coe_translate]; rw [← SlashAction.slash_mul]; rw [← isBoundedAt_infty_iff]; rw [← OnePoint.IsBoundedAt.smul_iff]
    apply ModularFormClass.bdd_at_cusps f
    simpa [mu

Depends on / 依赖: SlashInvariantForm, SlashInvariantForm.translate, translate
-/
noncomputable def ModularForm.translate [ModularFormClass F Γ k] (g : GL (Fin 2) Real) :
    ModularForm (toConjAct g⁻¹ • Γ) k where
  __ := SlashInvariantForm.translate f g
  bdd_at_cusps' {c} hc γ hγ := by
    rw [SlashInvariantForm.toFun_eq_coe]; rw [SlashInvariantForm.coe_translate]; rw [← SlashAction.slash_mul]; rw [← isBoundedAt_infty_iff]; rw [← OnePoint.IsBoundedAt.smul_iff]
    apply ModularFormClass.bdd_at_cusps f
    simpa [mul_smul, hγ] using hc.smul g
  holo' := (ModularFormClass.holo f).slash k g

@[simp]
/--
lemma `ModularForm.coe_translate` / 引理 `ModularForm.coe_translate`

English:
lemma ModularForm.coe_translate
  given: [ModularFormClass F Γ k] (g : GL (Fin 2) Real)
  proof: rfl

中文:
引理 ModularForm.coe_translate
  条件: [ModularFormClass F Γ k] (g : GL (Fin 2) 实数)
  证明: rfl
-/
lemma ModularForm.coe_translate [ModularFormClass F Γ k] (g : GL (Fin 2) Real) :
    translate f g = ⇑f ∣[k] g :=
  rfl

open ConjAct Pointwise in
/--
Definition of `CuspForm.translate` / `CuspForm.translate` 的定义

English:
definition CuspForm.translate
  signature: [CuspFormClass F Γ k] (g : GL (Fin 2) Real)
  body: ModularForm.translate f g
  zero_at_cusps' {c} hc γ hγ := by
    rw [SlashInvariantForm.toFun_eq_coe]; rw [ModularForm.toSlashInvariantForm_coe]; rw [ModularForm.coe_translate]; rw [← SlashAction.slash_mul]; rw [← isZeroAt_infty_iff]; rw [← OnePoint.IsZeroAt.smul_iff]
    apply CuspFormClass.zero_at

中文:
定义 CuspForm.translate
  签名: [CuspFormClass F Γ k] (g : GL (Fin 2) 实数)
  定义体: ModularForm.translate f g
  zero_at_cusps' {c} hc γ hγ := by
    rw [SlashInvariantForm.toFun_eq_coe]; rw [ModularForm.toSlashInvariantForm_coe]; rw [ModularForm.coe_translate]; rw [← SlashAction.slash_mul]; rw [← isZeroAt_infty_iff]; rw [← OnePoint.IsZeroAt.smul_iff]
    apply CuspFormClass.zero_at

Depends on / 依赖: ModularForm, ModularForm.translate, translate
-/
noncomputable def CuspForm.translate [CuspFormClass F Γ k] (g : GL (Fin 2) Real) :
    CuspForm (toConjAct g⁻¹ • Γ) k where
  __ := ModularForm.translate f g
  zero_at_cusps' {c} hc γ hγ := by
    rw [SlashInvariantForm.toFun_eq_coe]; rw [ModularForm.toSlashInvariantForm_coe]; rw [ModularForm.coe_translate]; rw [← SlashAction.slash_mul]; rw [← isZeroAt_infty_iff]; rw [← OnePoint.IsZeroAt.smul_iff]
    apply CuspFormClass.zero_at_cusps f
    simpa [mul_smul, hγ] using hc.smul g

@[simp]
/--
lemma `CuspForm.coe_translate` / 引理 `CuspForm.coe_translate`

English:
lemma CuspForm.coe_translate
  given: [CuspFormClass F Γ k] (g : SL(2, Int))
  proof: rfl

中文:
引理 CuspForm.coe_translate
  条件: [CuspFormClass F Γ k] (g : SL(2, 整数))
  证明: rfl
-/
lemma CuspForm.coe_translate [CuspFormClass F Γ k] (g : SL(2, Int)) :
    translate f g = ⇑f ∣[k] g :=
  rfl

end translate

section SL2Z

open ModularForm CuspForm OnePoint

variable {k F} {Γ : Subgroup (GL (Fin 2) Real)} [FunLike F ℍ Complex] (f : F)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Γ.IsArithmetic]
  signature: : Fact (IsCusp ∞ Γ)
  body: ⟨by simpa [Subgroup.IsArithmetic.isCusp_iff_isCusp_SL2Z, isCusp_SL2Z_iff]
    using ⟨_, OnePoint.map_infty _⟩⟩

中文:
实例 [Γ.IsArithmetic]
  签名: : Fact (IsCusp ∞ Γ)
  定义体: ⟨by simpa [Subgroup.IsArithmetic.isCusp_iff_isCusp_SL2Z, isCusp_SL2Z_iff]
    using ⟨_, OnePoint.map_infty _⟩⟩

Depends on / 依赖: IsArithmetic, OnePoint, OnePoint.map_infty, Subgroup, Subgroup.IsArithmetic.isCusp_iff_isCusp_SL2Z, isCusp_SL2Z_iff, isCusp_iff_isCusp_SL2Z, map_infty
-/
instance [Γ.IsArithmetic] : Fact (IsCusp ∞ Γ) :=
  ⟨by simpa [Subgroup.IsArithmetic.isCusp_iff_isCusp_SL2Z, isCusp_SL2Z_iff]
    using ⟨_, OnePoint.map_infty _⟩⟩

/--
lemma `ModularFormClass.bdd_at_infty` / 引理 `ModularFormClass.bdd_at_infty`

English:
lemma ModularFormClass.bdd_at_infty
  given: [ModularFormClass F Γ k] [Fact (IsCusp ∞ Γ)]
  proof: isBoundedAt_infty_iff.mp bdd_at_cusps f Fact.out

中文:
引理 ModularFormClass.bdd_at_infty
  条件: [ModularFormClass F Γ k] [Fact (IsCusp ∞ Γ)]
  证明: isBoundedAt_infty_iff.mp bdd_at_cusps f Fact.out

Depends on / 依赖: Fact.out, bdd_at_cusps, isBoundedAt_infty_iff, isBoundedAt_infty_iff.mp
-/
lemma ModularFormClass.bdd_at_infty [ModularFormClass F Γ k] [Fact (IsCusp ∞ Γ)] :
    IsBoundedAtImInfty f :=
isBoundedAt_infty_iff.mp bdd_at_cusps f Fact.out

/--
lemma `CuspFormClass.zero_at_infty` / 引理 `CuspFormClass.zero_at_infty`

English:
lemma CuspFormClass.zero_at_infty
  given: [CuspFormClass F Γ k] [Fact (IsCusp ∞ Γ)]
  proof: isZeroAt_infty_iff.mp zero_at_cusps f Fact.out

中文:
引理 CuspFormClass.zero_at_infty
  条件: [CuspFormClass F Γ k] [Fact (IsCusp ∞ Γ)]
  证明: isZeroAt_infty_iff.mp zero_at_cusps f Fact.out

Depends on / 依赖: Fact.out, isZeroAt_infty_iff, isZeroAt_infty_iff.mp, zero_at_cusps
-/
lemma CuspFormClass.zero_at_infty [CuspFormClass F Γ k] [Fact (IsCusp ∞ Γ)] :
    IsZeroAtImInfty f :=
isZeroAt_infty_iff.mp zero_at_cusps f Fact.out

variable [Γ.IsArithmetic] (g : SL(2, Int))

/--
lemma `ModularFormClass.bdd_at_infty_slash` / 引理 `ModularFormClass.bdd_at_infty_slash`

English:
lemma ModularFormClass.bdd_at_infty_slash
  given: [ModularFormClass F Γ k]
  proof: by
  rw [← OnePoint.isBoundedAt_infty_iff]; rw [SL_slash]; rw [← OnePoint.IsBoundedAt.smul_iff]
  apply bdd_at_cusps f
  rw [Subgroup.IsArithmetic.isCusp_iff_isCusp_SL2Z]; rw [isCusp_SL2Z_iff']
  exact ⟨g, by simp [mapGL]⟩

中文:
引理 ModularFormClass.bdd_at_infty_slash
  条件: [ModularFormClass F Γ k]
  证明: by
  rw [← OnePoint.isBoundedAt_infty_iff]; rw [SL_slash]; rw [← OnePoint.IsBoundedAt.smul_iff]
  apply bdd_at_cusps f
  rw [Subgroup.IsArithmetic.isCusp_iff_isCusp_SL2Z]; rw [isCusp_SL2Z_iff']
  exact ⟨g, by simp [mapGL]⟩

Depends on / 依赖: IsArithmetic, IsBoundedAt, OnePoint, OnePoint.IsBoundedAt.smul_iff, OnePoint.isBoundedAt_infty_iff, SL_slash, Subgroup, Subgroup.IsArithmetic.isCusp_iff_isCusp_SL2Z, bdd_at_cusps, isBoundedAt_infty_iff, isCusp_SL2Z_iff, isCusp_iff_isCusp_SL2Z, smul_iff
-/
lemma ModularFormClass.bdd_at_infty_slash [ModularFormClass F Γ k] :
    IsBoundedAtImInfty (f ∣[k] g) := by
  rw [← OnePoint.isBoundedAt_infty_iff]; rw [SL_slash]; rw [← OnePoint.IsBoundedAt.smul_iff]
  apply bdd_at_cusps f
  rw [Subgroup.IsArithmetic.isCusp_iff_isCusp_SL2Z]; rw [isCusp_SL2Z_iff']
  exact ⟨g, by simp [mapGL]⟩

/--
lemma `CuspFormClass.zero_at_infty_slash` / 引理 `CuspFormClass.zero_at_infty_slash`

English:
lemma CuspFormClass.zero_at_infty_slash
  given: [CuspFormClass F Γ k]
  proof: by
  rw [← OnePoint.isZeroAt_infty_iff]; rw [SL_slash]; rw [← OnePoint.IsZeroAt.smul_iff]
  apply zero_at_cusps f
  rw [Subgroup.IsArithmetic.isCusp_iff_isCusp_SL2Z]; rw [isCusp_SL2Z_iff']
  exact ⟨g, by simp [mapGL]⟩

中文:
引理 CuspFormClass.zero_at_infty_slash
  条件: [CuspFormClass F Γ k]
  证明: by
  rw [← OnePoint.isZeroAt_infty_iff]; rw [SL_slash]; rw [← OnePoint.IsZeroAt.smul_iff]
  apply zero_at_cusps f
  rw [Subgroup.IsArithmetic.isCusp_iff_isCusp_SL2Z]; rw [isCusp_SL2Z_iff']
  exact ⟨g, by simp [mapGL]⟩

Depends on / 依赖: IsArithmetic, IsZeroAt, OnePoint, OnePoint.IsZeroAt.smul_iff, OnePoint.isZeroAt_infty_iff, SL_slash, Subgroup, Subgroup.IsArithmetic.isCusp_iff_isCusp_SL2Z, isCusp_SL2Z_iff, isCusp_iff_isCusp_SL2Z, isZeroAt_infty_iff, smul_iff, zero_at_cusps
-/
lemma CuspFormClass.zero_at_infty_slash [CuspFormClass F Γ k] :
    IsZeroAtImInfty (f ∣[k] g) := by
  rw [← OnePoint.isZeroAt_infty_iff]; rw [SL_slash]; rw [← OnePoint.IsZeroAt.smul_iff]
  apply zero_at_cusps f
  rw [Subgroup.IsArithmetic.isCusp_iff_isCusp_SL2Z]; rw [isCusp_SL2Z_iff']
  exact ⟨g, by simp [mapGL]⟩

end SL2Z
