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

/-- The weight `k` slash action of `GL(2, ℝ)⁺` preserves holomorphic functions. This is private,
since it is a step towards the proof of `MDifferentiable.slash` which is more general. -/
/-
**MDifferentiable.slash_of_pos** 是 Mathlib 中的一个引理，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The weight `k` slash action of `GL(2, ℝ)⁺` preserves holomorphic functions. This
 is private,
since it is a step towards the proof of `MDifferentiable.slash` which is more ge
neral.
-/
private lemma MDifferentiable.slash_of_pos {f : ℍ → ℂ} (hf : MDiff f)
    (k : ℤ) {g : GL (Fin 2) ℝ} (hg : 0 < g.det.val) :
    MDiff (f ∣[k] g) := by
  refine .mul (.mul ?_ mdifferentiable_const) (mdifferentiable_denom_zpow g _)
  simpa only [σ, hg, ↓reduceIte] using! hf.comp (mdifferentiable_smul hg)
/-
**slash_J** 是 Mathlib 中的一个引理，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private lemma slash_J (f : ℍ → ℂ) (k : ℤ) :
    f ∣[k] J = fun τ : ℍ ↦ conj (f <| ofComplex <| -(conj ↑τ)) := by
  simp [slash_def, J_smul]

/-- The weight `k` slash action of the negative-determinant matrix `J` preserves holomorphic
functions. -/
/-
**MDifferentiable.slashJ** 是 Mathlib 中的一个引理，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The weight `k` slash action of the negative-determinant matrix `J` preserves hol
omorphic
functions.
-/
private lemma MDifferentiable.slashJ {f : ℍ → ℂ} (hf : MDiff f) (k : ℤ) :
    MDiff (f ∣[k] J) := by
  simp only [mdifferentiable_iff, slash_J, Function.comp_def] at hf ⊢
  have : {z | 0 < z.im}.EqOn (fun x ↦ conj (f <| ofComplex <| -conj ↑(ofComplex x)))
      (fun x ↦ conj (f <| ofComplex <| -conj x)) := fun z h ↦ by simp [ofComplex_apply_of_im_pos h]
  refine .congr (fun z hz ↦ DifferentiableAt.differentiableWithinAt ?_) this
  have : 0 < (-conj z).im := by simpa using! hz
  have := hf.differentiableAt (isOpen_upperHalfPlaneSet.mem_nhds this)
  simpa using! (this.comp _ differentiable_neg.differentiableAt).star_star.neg

/-- The weight `k` slash action of `GL(2, ℝ)` preserves holomorphic functions. -/
/-
**MDifferentiable.slash** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：MDifferentiable.slash {f : ℍ -> Complex} (hf : MDiff f) (k : Int) (g : GL 
(Fin 2) Real) : MDiff (f ∣[k] g)
参数：hf : MDiff f；k : Int；g : GL (Fin 2) Real。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Or.elim`：∀ {a b c : Prop}, a ∨ b → (a → c) → (b → c) → c
· 使用定理 `Ne.lt_or_gt`：Ne.lt_or_gt (h : a != b) : a < b ∨ b < a
· 使用引理 `Matrix.GeneralLinearGroup.det_ne_zero`：det_ne_zero [Nontrivial R] (g : G
L n R) : g.val.det != 0
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `UpperHalfPlane.J_sq`：UpperHalfPlane.J ^ 2 = 1
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `SlashAction.slash_mul`：∀ {β : Type u_1} {G : Type u_2} {α : Type u_3} {i
nst : Monoid G} {inst_1 : AddMonoid α} [self : SlashAction β G α]   (k : β) (g h
 : G) (a : …
· 使用定理 `_private.Mathlib.NumberTheory.ModularForms.Basic.0.MDifferentiable.slash
_of_pos`：∀ {f : UpperHalfPlane → ℂ},   MDiff f → ∀ (k : ℤ) {g : GL (Fin 2) ℝ}, 0
 < ↑(Matrix.GeneralLinearGroup.det g) → MDiff (SlashAction.map k g f)
· 使用定理 `_private.Mathlib.NumberTheory.ModularForms.Basic.0.MDifferentiable.slash
J`：∀ {f : UpperHalfPlane → ℂ}, MDiff f → ∀ (k : ℤ), MDiff (SlashAction.map k Upp
erHalfPlane.J f)
· 使用定理 `map_mul`：map_mul [MulHomClass F M N] (f : F) (x y : M) : f (x * y) = f x
 * f y
· 使用定理 `MonoidHomClass.toMulHomClass`：∀ {F : Type u_10} {M : outParam (Type u_11
)} {N : outParam (Type u_12)} {inst : MulOne M} {inst_1 : MulOne N}   {inst_2 : 
FunLike F M N} [se…
· 使用定理 `UpperHalfPlane.det_J`：Matrix.GeneralLinearGroup.det UpperHalfPlane.J = -
1
· 使用定理 `neg_mul`：neg_mul (a b : α) : -a * b = -(a * b)
· 使用定理 `Matrix.GeneralLinearGroup.val_det_apply`：∀ {n : Type u} [inst : Decidabl
eEq n] [inst_1 : Fintype n] {R : Type v} [inst_2 : CommRing R] (A : GL n R),   ↑
(Matrix.GeneralLinearGroup.de…
· 使用定理 `IsLeftCancelAdd.addLeftStrictMono_of_addLeftMono`：∀ (N : Type u_2) [inst
 : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftMono N], AddLeft
StrictMono N
· 使用定理 `instIsLeftCancelAddOfAddLeftReflectLE`：∀ {α : Type u_1} [inst : Add α] [
inst_1 : PartialOrder α] [AddLeftReflectLE α], IsLeftCancelAdd α
· 使用定理 `AddGroup.addLeftReflectLE_of_addLeftMono`：∀ {N : Type u_2} [inst : AddGr
oup N] [inst_1 : LE N] [AddLeftMono N], AddLeftReflectLE N
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α

--- 原说明 ---
The weight `k` slash action of `GL(2, ℝ)` preserves holomorphic functions.
-/
lemma MDifferentiable.slash {f : ℍ → ℂ} (hf : MDiff f)
    (k : ℤ) (g : GL (Fin 2) ℝ) : MDiff (f ∣[k] g) := by
  refine g.det_ne_zero.lt_or_gt.elim (fun hg ↦ ?_) (hf.slash_of_pos k)
  rw [show g = J * (J * g) by simp [← mul_assoc, ← sq], SlashAction.slash_mul]
  exact (hf.slashJ k).slash_of_pos _ (by simpa using hg)

variable (F : Type*) (Γ : Subgroup (GL (Fin 2) ℝ)) (k : ℤ)

open scoped ModularForm

/-- These are `SlashInvariantForm`'s that are holomorphic and bounded at infinity. -/
/-
**ModularForm** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：Subgroup (GL (Fin 2) ℝ) → ℤ → Type
参数：GL (Fin 2) ℝ。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
These are `SlashInvariantForm`'s that are holomorphic and bounded at infinity.
-/
structure ModularForm extends SlashInvariantForm Γ k where
  holo' : MDiff (toSlashInvariantForm : ℍ → ℂ)
  bdd_at_cusps' {c : OnePoint ℝ} (hc : IsCusp c Γ) : c.IsBoundedAt toFun k

/-- The `SlashInvariantForm` associated to a `ModularForm`. -/
add_decl_doc ModularForm.toSlashInvariantForm

/-- These are `SlashInvariantForm`s that are holomorphic and zero at infinity. -/
/-
**CuspForm** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：Subgroup (GL (Fin 2) ℝ) → ℤ → Type
参数：GL (Fin 2) ℝ。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
These are `SlashInvariantForm`s that are holomorphic and zero at infinity.
-/
structure CuspForm extends SlashInvariantForm Γ k where
  holo' : MDiff (toSlashInvariantForm : ℍ → ℂ)
  zero_at_cusps' {c : OnePoint ℝ} (hc : IsCusp c Γ) : c.IsZeroAt toFun k

/-- The `SlashInvariantForm` associated to a `CuspForm`. -/
add_decl_doc CuspForm.toSlashInvariantForm

/-- `ModularFormClass F Γ k` says that `F` is a type of bundled functions that extend
`SlashInvariantFormClass` by requiring that the functions be holomorphic and bounded
at all cusps. -/
/-
**ModularFormClass** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：(F : Type u_2) → outParam (Subgroup (GL (Fin 2) ℝ)) → outParam ℤ → [FunLik
e F UpperHalfPlane ℂ] → Prop
参数：GL (Fin 2) ℝ。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`ModularFormClass F Γ k` says that `F` is a type of bundled functions that exten
d
`SlashInvariantFormClass` by requiring that the functions be holomorphic and bou
nded
at all cusps.
-/
class ModularFormClass (F : Type*) (Γ : outParam <| Subgroup (GL (Fin 2) ℝ)) (k : outParam ℤ)
    [FunLike F ℍ ℂ] : Prop extends SlashInvariantFormClass F Γ k where
  holo : ∀ f : F, MDiff (f : ℍ → ℂ)
  bdd_at_cusps (f : F) {c : OnePoint ℝ} (hc : IsCusp c Γ) : c.IsBoundedAt f k

/-- `CuspFormClass F Γ k` says that `F` is a type of bundled functions that extend
`SlashInvariantFormClass` by requiring that the functions be holomorphic and zero
at all cusps. -/
/-
**CuspFormClass** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：(F : Type u_2) → outParam (Subgroup (GL (Fin 2) ℝ)) → outParam ℤ → [FunLik
e F UpperHalfPlane ℂ] → Prop
参数：GL (Fin 2) ℝ。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`CuspFormClass F Γ k` says that `F` is a type of bundled functions that extend
`SlashInvariantFormClass` by requiring that the functions be holomorphic and zer
o
at all cusps.
-/
class CuspFormClass (F : Type*) (Γ : outParam <| Subgroup (GL (Fin 2) ℝ)) (k : outParam ℤ)
    [FunLike F ℍ ℂ] : Prop extends SlashInvariantFormClass F Γ k where
  holo : ∀ f : F, MDiff (f : ℍ → ℂ)
  zero_at_cusps (f : F) {c : OnePoint ℝ} (hc : IsCusp c Γ) : c.IsZeroAt f k
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 100) ModularForm.funLike :
    FunLike (ModularForm Γ k) ℍ ℂ where
  coe f := f.toFun
  coe_injective f g h := by cases f; cases g; congr; exact DFunLike.ext' h
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 100) ModularForm.instModularFormClass :
    ModularFormClass (ModularForm Γ k) Γ k where
  slash_action_eq f := f.slash_action_eq'
  holo := ModularForm.holo'
  bdd_at_cusps := ModularForm.bdd_at_cusps'

@[fun_prop]
/-
**ModularFormClass.continuous** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：ModularFormClass.continuous {k : Int} {Γ : Subgroup (GL (Fin 2) Real)} {F 
: Type*} [FunLike F ℍ Complex] [ModularFormClass F Γ k] (f : F) : Continuous f
参数：GL (Fin 2) Real；f : F。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MDifferentiable.continuous`：MDifferentiable.continuous (h : MDiff f) : C
ontinuous f
· 使用定理 `ModularFormClass.holo`：∀ {F : Type u_2} {Γ : outParam (Subgroup (GL (Fin
 2) ℝ))} {k : outParam ℤ} {inst : FunLike F UpperHalfPlane ℂ}   [self : ModularF
ormClass F …
-/
lemma ModularFormClass.continuous {k : ℤ} {Γ : Subgroup (GL (Fin 2) ℝ)}
    {F : Type*} [FunLike F ℍ ℂ] [ModularFormClass F Γ k] (f : F) :
    Continuous f :=
  (ModularFormClass.holo f).continuous
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 100) CuspForm.funLike : FunLike (CuspForm Γ k) ℍ ℂ where
  coe f := f.toFun
  coe_injective f g h := by cases f; cases g; congr; exact DFunLike.ext' h
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 100) CuspFormClass.cuspForm : CuspFormClass (CuspForm Γ k) Γ k where
  slash_action_eq f := f.slash_action_eq'
  holo := CuspForm.holo'
  zero_at_cusps := CuspForm.zero_at_cusps'

initialize_simps_projections ModularForm (toFun → coe, as_prefix coe)

initialize_simps_projections CuspForm (toFun → coe, as_prefix coe)

variable {F Γ k}

/-- Build a `ModularForm Γ k` from any element of a type carrying a `ModularFormClass Γ k`
instance. -/
@[simps -fullyApplied]
/-
**ModularFormClass.modularForm** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：ModularFormClass.modularForm [FunLike F ℍ Complex] [ModularFormClass F Γ k
] (f : F) : ModularForm Γ k where toFun
参数：f : F。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `ModularFormClass.holo`：∀ {F : Type u_2} {Γ : outParam (Subgroup (GL (Fin
 2) ℝ))} {k : outParam ℤ} {inst : FunLike F UpperHalfPlane ℂ}   [self : ModularF
ormClass F …
· 使用定理 `ModularFormClass.bdd_at_cusps`：∀ {F : Type u_2} {Γ : outParam (Subgroup 
(GL (Fin 2) ℝ))} {k : outParam ℤ} {inst : FunLike F UpperHalfPlane ℂ}   [self : 
ModularFormClass F …

--- 原说明 ---
Build a `ModularForm Γ k` from any element of a type carrying a `ModularFormClas
s Γ k`
instance.
-/
def ModularFormClass.modularForm [FunLike F ℍ ℂ] [ModularFormClass F Γ k] (f : F) :
    ModularForm Γ k where
  toFun := f
  slash_action_eq' := SlashInvariantFormClass.slash_action_eq f
  holo' := ModularFormClass.holo f
  bdd_at_cusps' := ModularFormClass.bdd_at_cusps f
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [FunLike F ℍ ℂ] [ModularFormClass F Γ k] : CoeTC F (ModularForm Γ k) :=
  ⟨ModularFormClass.modularForm⟩
/-
**ModularForm.toFun_eq_coe** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ModularForm.toFun_eq_coe (f : ModularForm Γ k) : f.toFun = (f : ℍ -> Compl
ex)
参数：f : ModularForm Γ k。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem ModularForm.toFun_eq_coe (f : ModularForm Γ k) : f.toFun = (f : ℍ → ℂ) :=
  rfl

@[simp]
/-
**ModularForm.toSlashInvariantForm_coe** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ModularForm.toSlashInvariantForm_coe (f : ModularForm Γ k) : ⇑f.1 = f
参数：f : ModularForm Γ k。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem ModularForm.toSlashInvariantForm_coe (f : ModularForm Γ k) : ⇑f.1 = f :=
  rfl
/-
**CuspForm.toFun_eq_coe** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：CuspForm.toFun_eq_coe {f : CuspForm Γ k} : f.toFun = (f : ℍ -> Complex)
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem CuspForm.toFun_eq_coe {f : CuspForm Γ k} : f.toFun = (f : ℍ → ℂ) :=
  rfl

@[simp]
/-
**CuspForm.toSlashInvariantForm_coe** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：CuspForm.toSlashInvariantForm_coe (f : CuspForm Γ k) : ⇑f.1 = f
参数：f : CuspForm Γ k。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem CuspForm.toSlashInvariantForm_coe (f : CuspForm Γ k) : ⇑f.1 = f := rfl

@[ext]
/-
**ModularForm.ext** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ModularForm.ext {f g : ModularForm Γ k} (h : forall x, f x = g x) : f = g
参数：h : forall x, f x = g x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DFunLike.ext`：ext (f g : F) (h : forall x : α, f x = g x) : f = g
-/
theorem ModularForm.ext {f g : ModularForm Γ k} (h : ∀ x, f x = g x) : f = g :=
  DFunLike.ext f g h

@[ext]
/-
**CuspForm.ext** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：CuspForm.ext {f g : CuspForm Γ k} (h : forall x, f x = g x) : f = g
参数：h : forall x, f x = g x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DFunLike.ext`：ext (f g : F) (h : forall x : α, f x = g x) : f = g
-/
theorem CuspForm.ext {f g : CuspForm Γ k} (h : ∀ x, f x = g x) : f = g :=
  DFunLike.ext f g h

/-- Copy of a `ModularForm` with a new `toFun` equal to the old one, optionally transporting
along an equality of subgroups. Useful to fix definitional equalities. -/
/-
**ModularForm.copy** 是 Mathlib 中的一个定义，位于命名空间 `ModularForm`。
形式化陈述：{Γ : Subgroup (GL (Fin 2) ℝ)} →   {k : ℤ} →     {Γ' : Subgroup (GL (Fin 2)
 ℝ)} →       (f : ModularForm Γ k) →         (f' : UpperHalfPlane → ℂ) → f' = ⇑f
 → autoParam (Γ' = Γ) ModularForm.copy._auto_1 → ModularForm Γ' k
参数：GL (Fin 2) ℝ；GL (Fin 2) ℝ；f : ModularForm Γ k；f' : UpperHalfPlane → ℂ；Γ' = Γ。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Copy of a `ModularForm` with a new `toFun` equal to the old one, optionally tran
sporting
along an equality of subgroups. Useful to fix definitional equalities.
-/
protected def ModularForm.copy {Γ' : Subgroup (GL (Fin 2) ℝ)} (f : ModularForm Γ k) (f' : ℍ → ℂ)
    (h : f' = ⇑f) (hΓ : Γ' = Γ := by rfl) : ModularForm Γ' k where
  toFun := f'
  slash_action_eq' A hA := h.symm ▸ f.slash_action_eq' A (hΓ ▸ hA)
  holo' := h.symm ▸ f.holo'
  bdd_at_cusps' hc := h.symm ▸ f.bdd_at_cusps' (hΓ ▸ hc)

/-- Copy of a `CuspForm` with a new `toFun` equal to the old one, optionally transporting
along an equality of subgroups. Useful to fix definitional equalities. -/
/-
**CuspForm.copy** 是 Mathlib 中的一个定义，位于命名空间 `CuspForm`。
形式化陈述：{Γ : Subgroup (GL (Fin 2) ℝ)} →   {k : ℤ} →     {Γ' : Subgroup (GL (Fin 2)
 ℝ)} →       (f : CuspForm Γ k) →         (f' : UpperHalfPlane → ℂ) → f' = ⇑f → 
autoParam (Γ' = Γ) CuspForm.copy._auto_1 → CuspForm Γ' k
参数：GL (Fin 2) ℝ；GL (Fin 2) ℝ；f : CuspForm Γ k；f' : UpperHalfPlane → ℂ；Γ' = Γ。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Copy of a `CuspForm` with a new `toFun` equal to the old one, optionally transpo
rting
along an equality of subgroups. Useful to fix definitional equalities.
-/
protected def CuspForm.copy {Γ' : Subgroup (GL (Fin 2) ℝ)} (f : CuspForm Γ k) (f' : ℍ → ℂ)
    (h : f' = ⇑f) (hΓ : Γ' = Γ := by rfl) : CuspForm Γ' k where
  toFun := f'
  slash_action_eq' A hA := h.symm ▸ f.slash_action_eq' A (hΓ ▸ hA)
  holo' := h.symm ▸ f.holo'
  zero_at_cusps' hc := h.symm ▸ f.zero_at_cusps' (hΓ ▸ hc)

end ModularForm

namespace ModularForm

open SlashInvariantForm

variable {Γ : Subgroup (GL (Fin 2) ℝ)} {k : ℤ}

/-
**ModularForm.add** 是 Mathlib 中的一个实例，位于命名空间 `ModularForm`。
形式化陈述：add : Add (ModularForm Γ k) where add f g
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance add : Add (ModularForm Γ k) where add f g :=
  { toSlashInvariantForm := f + g
    holo' := f.holo'.add g.holo'
    bdd_at_cusps' hc := by simpa using (f.bdd_at_cusps' hc).add (g.bdd_at_cusps' hc) }
/-
**ModularForm.** 是 Mathlib 中的一个实例，位于命名空间 `ModularForm`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : IsAddApply (ModularForm Γ k) ℍ ℂ where
  add_apply _ _ _ := rfl

@[deprecated (since := "2026-07-10")] alias coe_add := FunLike.coe_add

@[deprecated (since := "2026-07-10")] protected alias add_apply := add_apply
/-
**ModularForm.instZero** 是 Mathlib 中的一个实例，位于命名空间 `ModularForm`。
形式化陈述：instZero : Zero (ModularForm Γ k)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instZero : Zero (ModularForm Γ k) :=
  ⟨ { toSlashInvariantForm := 0
      holo' := fun _ => mdifferentiableAt_const
      bdd_at_cusps' hc g hg := by simpa using zero_form_isBoundedAtImInfty } ⟩
/-
**ModularForm.** 是 Mathlib 中的一个实例，位于命名空间 `ModularForm`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : IsZeroApply (ModularForm Γ k) ℍ ℂ where
  zero_apply _ := rfl

@[deprecated (since := "2026-07-10")] alias coe_zero := FunLike.coe_zero

@[deprecated (since := "2026-07-10")] protected alias zero_apply := zero_apply

@[deprecated (since := "2026-07-10")] alias coe_eq_zero_iff := FunLike.coe_zero_iff

/-- If `-1 ∈ Γ` and `k` is odd, then every modular form of weight `k` for `Γ` is zero. -/
/-
**ModularForm.eq_zero_of_neg_one_mem** 是 Mathlib 中的一个引理，位于命名空间 `ModularForm`。
形式化陈述：eq_zero_of_neg_one_mem [Γ.HasDetOne] (h_neg_one : -1 in Γ) (hk : Odd k) (f
 : ModularForm Γ k) : f = 0
参数：h_neg_one : -1 in Γ；hk : Odd k；f : ModularForm Γ k。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ModularForm.ext`：ModularForm.ext {f g : ModularForm Γ k} (h : forall x, 
f x = g x) : f = g
· 使用定理 `SlashInvariantForm.slash_action_eqn''`：slash_action_eqn'' {k : Int} [Γ.H
asDetOne] [SlashInvariantFormClass F Γ k] (f : F) {γ} (hγ : γ in Γ) (z : ℍ) : f 
(γ • z) = (denom γ z) ^ k *…
· 使用定理 `ModularFormClass.toSlashInvariantFormClass`：∀ {F : Type u_2} {Γ : outPar
am (Subgroup (GL (Fin 2) ℝ))} {k : outParam ℤ} {inst : FunLike F UpperHalfPlane 
ℂ}   [self : ModularFormClass F …
· 使用定理 `ModularForm.instModularFormClass`：∀ (Γ : Subgroup (GL (Fin 2) ℝ)) (k : ℤ
), ModularFormClass (ModularForm Γ k) Γ k
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Mathlib.Tactic.LinearCombination.eq_of_eq`：eq_of_eq [Add α] [IsRightCanc
elAdd α] (p : (a : α) = b) (H : a' + b = b' + a) : a' = b'
· 使用定理 `AddRightCancelSemigroup.toIsRightCancelAdd`：∀ {G : Type u} [self : AddRi
ghtCancelSemigroup G], IsRightCancelAdd G
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Odd.neg_one_zpow`：Odd.neg_one_zpow (h : Odd n) : (-1 : α) ^ n = -1
· 使用引理 `UpperHalfPlane.denom_one`：denom_one : denom 1 z = 1
· 使用引理 `UpperHalfPlane.denom_neg`：denom_neg (g : GL (Fin 2) Real) (z : Complex) 
: denom (-g) z = -(denom g z)
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用定理 `UpperHalfPlane.neg_smul`：neg_smul : -g • z = g • z
· 使用定理 `Mathlib.Tactic.LinearCombination.eq_rearrange`：∀ {G : Type u_3} [inst : 
AddGroup G] {a b : G}, a - b = 0 → a = b
· 使用定理 `Mathlib.Tactic.Ring.of_eq`：∀ {α : Sort u_2} {a b c : α}, a = c → b = c →
 a = b
· 使用定理 `Mathlib.Tactic.Ring.Common.sub_congr`：∀ {R : Type u_2} [inst : CommRing 
R] {a a' b b' c : R}, a = a' → b = b' → a' - b' = c → a - b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.add_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' + b' = c → a + b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' * b' = c → a * b = c
· 使用定理 `Mathlib.Tactic.Ring.cast_pos`：∀ {R : Type u_1} [inst : CommSemiring R] {
a : R} {n : ℕ}, Mathlib.Meta.NormNum.IsNat a n → a = n.rawCast + 0
· 使用定理 `Mathlib.Meta.NormNum.isNat_ofNat`：isNat_ofNat (α : Type u) [AddMonoidWit
hOne α] {a : α} {n : Nat} (h : n = a) : IsNat a n
· 使用引理 `Mathlib.Meta.NormNum.instAtLeastTwo`：instAtLeastTwo (n : Nat) : Nat.AtLe
astTwo (n + 2)
· 使用定理 `Mathlib.Tactic.Ring.Common.atom_pf`：∀ {R : Type u_1} [inst : CommSemirin
g R] {b : R} (a : R) {e : ℕ},   Nat.rawCast 1 = e → a ^ e * Nat.rawCast 1 = b → 
a = b + 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Mathlib.Tactic.Ring.Common.add_mul`：∀ {R : Type u_1} [inst : CommSemirin
g R] {a₁ a₂ b c₁ c₂ d : R},   a₁ * b = c₁ → a₂ * b = c₂ → c₁ + c₂ = d → (a₁ + a₂
) * b = d
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_add`：∀ {R : Type u_1} [inst : CommSemirin
g R] {a b₁ b₂ c₁ c₂ d : R},   a * b₁ = c₁ → a * b₂ = c₂ → c₁ + 0 + c₂ = d → a * 
(b₁ + b₂) = d
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_pf_right`：∀ {R : Type u_1} [inst : CommSe
miring R] {a b₃ c : R} (b₁ : R) (b₂ : ℕ), a * b₃ = c → a * (b₁ ^ b₂ * b₃) = b₁ ^
 b₂ * c
· 使用定理 `Mathlib.Meta.NormNum.IsNat.to_raw_eq`：∀ {α : Type u} {a : α} {n : ℕ} [in
st : AddMonoidWithOne α], Mathlib.Meta.NormNum.IsNat a n → a = n.rawCast
· 使用定理 `Mathlib.Meta.NormNum.isNat_mul`：∀ {α : Type u_1} [inst : Semiring α] {f 
: α → α → α} {a b : α} {a' b' c : ℕ},   f = HMul.hMul →     Mathlib.Meta.NormNum
.IsNat a a' →       …
· 使用定理 `Mathlib.Meta.NormNum.IsNat.of_raw`：∀ (α : Type u_1) [inst : AddMonoidWit
hOne α] (n : ℕ), Mathlib.Meta.NormNum.IsNat n.rawCast n
（共 58 条，此处仅展示前 30 条）

--- 原说明 ---
If `-1 ∈ Γ` and `k` is odd, then every modular form of weight `k` for `Γ` is zer
o.
-/
lemma eq_zero_of_neg_one_mem [Γ.HasDetOne] (h_neg_one : -1 ∈ Γ) (hk : Odd k)
    (f : ModularForm Γ k) : f = 0 := by
  ext z
  have hf := slash_action_eqn'' f h_neg_one z
  rw [neg_smul, one_smul, denom_neg, denom_one, hk.neg_one_zpow] at hf
  have h2 : (2 : ℂ) * f z = 0 := by linear_combination hf
  exact (mul_eq_zero.mp h2).resolve_left (by norm_num)

section
-- scalar multiplication by real types (no assumption on `Γ`)

variable {α : Type*} [SMul α ℝ] [SMul α ℂ] [IsScalarTower α ℝ ℂ]

local instance : IsScalarTower α ℂ ℂ where
  smul_assoc a y z := by simpa using smul_assoc (a • (1 : ℝ)) y z

/-
**ModularForm.instSMul** 是 Mathlib 中的一个实例，位于命名空间 `ModularForm`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instSMulℝ : SMul α (ModularForm Γ k) where
  smul c f :=
  { toSlashInvariantForm := c • f.1
    holo' := by simpa using f.holo'.const_smul (c • (1 : ℂ))
    bdd_at_cusps' hc g hg := by
      simpa only [IsBoundedAtImInfty, Filter.BoundedAtFilter, SlashInvariantForm.toFun_eq_coe,
        FunLike.coe_smul, toSlashInvariantForm_coe, ← smul_one_smul ℂ c ⇑f, smul_slash]
        using (f.bdd_at_cusps' hc g hg).const_smul_left _ }
/-
**ModularForm.instIsSMulApply** 是 Mathlib 中的一个实例，位于命名空间 `ModularForm`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instIsSMulApplyℝ : IsSMulApply α (ModularForm Γ k) ℍ ℂ where
  smul_apply _ _ _ := rfl

@[deprecated (since := "2026-07-10")] alias coe_smul := FunLike.coe_smul

@[deprecated (since := "2026-07-10")] protected alias smul_apply := smul_apply

end

section

variable {α : Type*} [SMul α ℂ] [IsScalarTower α ℂ ℂ] [Γ.HasDetOne]

/-
**ModularForm.instSMul** 是 Mathlib 中的一个实例，位于命名空间 `ModularForm`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instSMulℂ : SMul α (ModularForm Γ k) where
  smul c f :=
  { toSlashInvariantForm := c • f.1
    holo' := by simpa using f.holo'.const_smul (c • (1 : ℂ))
    bdd_at_cusps' hc g hg := by
      simp_rw [IsBoundedAtImInfty, Filter.BoundedAtFilter, SlashInvariantForm.toFun_eq_coe,
        FunLike.coe_smul, toSlashInvariantForm_coe, ← smul_one_smul ℂ c ⇑f, smul_slash]
      exact (f.bdd_at_cusps' hc g hg).const_smul_left (σ g (c • (1 : ℂ))) }
/-
**ModularForm.instIsSMulApply** 是 Mathlib 中的一个实例，位于命名空间 `ModularForm`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instIsSMulApplyℂ : IsSMulApply α (ModularForm Γ k) ℍ ℂ where
  smul_apply _ _ _ := rfl

@[deprecated (since := "2026-07-10")] alias IsGLPos.coe_smul := FunLike.coe_smul

@[deprecated (since := "2026-07-10")] protected alias IsGLPos.smul_apply := smul_apply

end

/-
**ModularForm.instNeg** 是 Mathlib 中的一个实例，位于命名空间 `ModularForm`。
形式化陈述：instNeg : Neg (ModularForm Γ k)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instNeg : Neg (ModularForm Γ k) :=
  ⟨fun f =>
    { toSlashInvariantForm := -f.1
      holo' := f.holo'.neg
      bdd_at_cusps' hc g hg := by simpa using! (f.bdd_at_cusps' hc g hg).neg }⟩
/-
**ModularForm.** 是 Mathlib 中的一个实例，位于命名空间 `ModularForm`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : IsNegApply (ModularForm Γ k) ℍ ℂ where
  neg_apply _ _ := rfl

@[deprecated (since := "2026-07-10")] alias coe_neg := FunLike.coe_neg

@[deprecated (since := "2026-07-10")] protected alias neg_apply := neg_apply
/-
**ModularForm.instSub** 是 Mathlib 中的一个实例，位于命名空间 `ModularForm`。
形式化陈述：instSub : Sub (ModularForm Γ k)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instSub : Sub (ModularForm Γ k) :=
  ⟨fun f g => f + -g⟩
/-
**ModularForm.** 是 Mathlib 中的一个实例，位于命名空间 `ModularForm`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : IsSubApply (ModularForm Γ k) ℍ ℂ where
  sub_apply _ _ _ := rfl

@[deprecated (since := "2026-07-10")] alias coe_sub := FunLike.coe_sub

@[deprecated (since := "2026-07-10")] protected alias sub_apply := sub_apply
/-
**ModularForm.** 是 Mathlib 中的一个实例，位于命名空间 `ModularForm`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : AddCommGroup (ModularForm Γ k) := fast_instance% FunLike.addCommGroup

@[deprecated (since := "2026-07-10")] alias coeHom := FunLike.coeMonoidHom
/-
**ModularForm.** 是 Mathlib 中的一个实例，位于命名空间 `ModularForm`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Module ℝ (ModularForm Γ k) := fast_instance% FunLike.module
/-
**ModularForm.** 是 Mathlib 中的一个实例，位于命名空间 `ModularForm`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Γ.HasDetOne] : Module ℂ (ModularForm Γ k) := fast_instance% FunLike.module
/-
**ModularForm.** 是 Mathlib 中的一个实例，位于命名空间 `ModularForm`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Inhabited (ModularForm Γ k) :=
  ⟨0⟩

/-- The modular form of weight `k_1 + k_2` given by the product of two modular forms of weights
`k_1` and `k_2`. -/
@[simps! -fullyApplied coe]
/-
**ModularForm.mul** 是 Mathlib 中的一个定义，位于命名空间 `ModularForm`。
形式化陈述：mul {k_1 k_2 : Int} [Γ.HasDetPlusMinusOne] (f : ModularForm Γ k_1) (g : Mo
dularForm Γ k_2) : ModularForm Γ (k_1 + k_2) where toSlashInvariantForm
参数：f : ModularForm Γ k_1；g : ModularForm Γ k_2。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The modular form of weight `k_1 + k_2` given by the product of two modular forms
 of weights
`k_1` and `k_2`.
-/
def mul {k_1 k_2 : ℤ} [Γ.HasDetPlusMinusOne] (f : ModularForm Γ k_1) (g : ModularForm Γ k_2) :
    ModularForm Γ (k_1 + k_2) where
  toSlashInvariantForm := f.1.mul g.1
  holo' := f.holo'.mul g.holo'
  bdd_at_cusps' hc γ hγ := by
    simpa [mul_slash] using! ((f.bdd_at_cusps' hc γ hγ).mul (g.bdd_at_cusps' hc γ hγ)).smul _

/-- The constant function with value `x : ℂ` as a modular form of weight 0 and any level. -/
/-
**ModularForm.const** 是 Mathlib 中的一个定义，位于命名空间 `ModularForm`。
形式化陈述：{Γ : Subgroup (GL (Fin 2) ℝ)} → ℂ → [Γ.HasDetOne] → ModularForm Γ 0
参数：GL (Fin 2) ℝ。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The constant function with value `x : ℂ` as a modular form of weight 0 and any l
evel.
-/
@[simps! -fullyApplied] def const (x : ℂ) [Γ.HasDetOne] : ModularForm Γ 0 where
  toSlashInvariantForm := .const x
  holo' _ := mdifferentiableAt_const
  bdd_at_cusps' hc g hg := by simpa only [coe_const, slash_def, SlashInvariantForm.toFun_eq_coe,
      Function.const_apply, neg_zero, zpow_zero] using! atImInfty.const_boundedAtFilter _

@[simp]
/-
**ModularForm.const_apply** 是 Mathlib 中的一个引理，位于命名空间 `ModularForm`。
形式化陈述：const_apply [Γ.HasDetOne] (x : Complex) (τ : ℍ) : (const x : ModularForm Γ
 0) τ = x
参数：x : Complex；τ : ℍ。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma const_apply [Γ.HasDetOne] (x : ℂ) (τ : ℍ) : (const x : ModularForm Γ 0) τ = x := rfl

/-- The constant function with value `x : ℂ` as a modular form of weight 0 and any level. -/
/-
**ModularForm.const** 是 Mathlib 中的一个定义，位于命名空间 `ModularForm`。
形式化陈述：{Γ : Subgroup (GL (Fin 2) ℝ)} → ℂ → [Γ.HasDetOne] → ModularForm Γ 0
参数：GL (Fin 2) ℝ。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The constant function with value `x : ℂ` as a modular form of weight 0 and any l
evel.
-/
@[simps! -fullyApplied coe] def constℝ (x : ℝ) [Γ.HasDetPlusMinusOne] : ModularForm Γ 0 where
  toSlashInvariantForm := .constℝ x
  holo' _ := mdifferentiableAt_const
  bdd_at_cusps' hc g hg := by simpa only [coe_constℝ, slash_def, SlashInvariantForm.toFun_eq_coe,
      Function.const_apply, neg_zero, zpow_zero] using! atImInfty.const_boundedAtFilter _

@[simp]
/-
**ModularForm.const** 是 Mathlib 中的一个定义，位于命名空间 `ModularForm`。
形式化陈述：{Γ : Subgroup (GL (Fin 2) ℝ)} → ℂ → [Γ.HasDetOne] → ModularForm Γ 0
参数：GL (Fin 2) ℝ。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma constℝ_apply [Γ.HasDetPlusMinusOne] (x : ℝ) (τ : ℍ) :
    (constℝ x : ModularForm Γ 0) τ = x :=
  rfl
/-
**ModularForm.** 是 Mathlib 中的一个实例，位于命名空间 `ModularForm`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Γ.HasDetPlusMinusOne] : One (ModularForm Γ 0) where
  one := { constℝ 1 with toSlashInvariantForm := 1 }

@[simp]
/-
**ModularForm.one_coe_eq_one** 是 Mathlib 中的一个定理，位于命名空间 `ModularForm`。
形式化陈述：one_coe_eq_one [Γ.HasDetPlusMinusOne] : ⇑(1 : ModularForm Γ 0) = 1
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem one_coe_eq_one [Γ.HasDetPlusMinusOne] : ⇑(1 : ModularForm Γ 0) = 1 :=
  rfl
/-
**ModularForm.** 是 Mathlib 中的一个实例，位于命名空间 `ModularForm`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Γ.HasDetPlusMinusOne] : NatCast (ModularForm Γ 0) where
  natCast n := constℝ n

@[simp, norm_cast]
/-
**ModularForm.coe_natCast** 是 Mathlib 中的一个引理，位于命名空间 `ModularForm`。
形式化陈述：coe_natCast [Γ.HasDetPlusMinusOne] (n : Nat) : ⇑(n : ModularForm Γ 0) = n
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma coe_natCast [Γ.HasDetPlusMinusOne] (n : ℕ) :
    ⇑(n : ModularForm Γ 0) = n := rfl
/-
**ModularForm.toSlashInvariantForm_natCast** 是 Mathlib 中的一个引理，位于命名空间 `ModularFor
m`。
形式化陈述：toSlashInvariantForm_natCast [Γ.HasDetPlusMinusOne] (n : Nat) : (n : Modul
arForm Γ 0).toSlashInvariantForm = n
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma toSlashInvariantForm_natCast [Γ.HasDetPlusMinusOne] (n : ℕ) :
    (n : ModularForm Γ 0).toSlashInvariantForm = n := rfl
/-
**ModularForm.** 是 Mathlib 中的一个实例，位于命名空间 `ModularForm`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Γ.HasDetPlusMinusOne] : IntCast (ModularForm Γ 0) where
  intCast z := constℝ z

@[simp, norm_cast]
/-
**ModularForm.coe_intCast** 是 Mathlib 中的一个引理，位于命名空间 `ModularForm`。
形式化陈述：coe_intCast [Γ.HasDetPlusMinusOne] (z : Int) : ⇑(z : ModularForm Γ 0) = z
参数：z : Int。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma coe_intCast [Γ.HasDetPlusMinusOne] (z : ℤ) :
    ⇑(z : ModularForm Γ 0) = z := rfl
/-
**ModularForm.toSlashInvariantForm_intCast** 是 Mathlib 中的一个引理，位于命名空间 `ModularFor
m`。
形式化陈述：toSlashInvariantForm_intCast [Γ.HasDetPlusMinusOne] (z : Int) : (z : Modul
arForm Γ 0).toSlashInvariantForm = z
参数：z : Int。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma toSlashInvariantForm_intCast [Γ.HasDetPlusMinusOne] (z : ℤ) :
    (z : ModularForm Γ 0).toSlashInvariantForm = z := rfl

end ModularForm

namespace CuspForm

open ModularForm

variable {F : Type*} {Γ : Subgroup (GL (Fin 2) ℝ)} {k : ℤ}

/-
**CuspForm.hasAdd** 是 Mathlib 中的一个实例，位于命名空间 `CuspForm`。
形式化陈述：hasAdd : Add (CuspForm Γ k)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance hasAdd : Add (CuspForm Γ k) :=
  ⟨fun f g =>
    { toSlashInvariantForm := f + g
      holo' := f.holo'.add g.holo'
      zero_at_cusps' A := by simpa using (f.zero_at_cusps' A).add (g.zero_at_cusps' A) }⟩
/-
**CuspForm.** 是 Mathlib 中的一个实例，位于命名空间 `CuspForm`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : IsAddApply (CuspForm Γ k) ℍ ℂ where
  add_apply _ _ _ := rfl

@[deprecated (since := "2026-07-10")] alias coe_add := FunLike.coe_add

@[deprecated (since := "2026-07-10")] protected alias add_apply := add_apply
/-
**CuspForm.instZero** 是 Mathlib 中的一个实例，位于命名空间 `CuspForm`。
形式化陈述：instZero : Zero (CuspForm Γ k)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instZero : Zero (CuspForm Γ k) :=
  ⟨ { toSlashInvariantForm := 0
      holo' := fun _ => mdifferentiableAt_const
      zero_at_cusps' hc g hg := by simpa using! Filter.zero_zeroAtFilter _ } ⟩
/-
**CuspForm.** 是 Mathlib 中的一个实例，位于命名空间 `CuspForm`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : IsZeroApply (CuspForm Γ k) ℍ ℂ where
  zero_apply _ := rfl

@[deprecated (since := "2026-07-10")] alias coe_zero := FunLike.coe_zero

@[deprecated (since := "2026-07-10")] protected alias zero_apply := zero_apply

section
-- scalar multiplication by real types (no assumption on `Γ`)

variable {α : Type*} [SMul α ℝ] [SMul α ℂ] [IsScalarTower α ℝ ℂ]

local instance : IsScalarTower α ℂ ℂ where
  smul_assoc a y z := by simpa using smul_assoc (a • (1 : ℝ)) y z

/-
**CuspForm.instSMul** 是 Mathlib 中的一个实例，位于命名空间 `CuspForm`。
形式化陈述：instSMul : SMul α (CuspForm Γ k) where smul c f
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instSMul : SMul α (CuspForm Γ k) where smul c f :=
  { toSlashInvariantForm := c • f.1
    holo' := by simpa using f.holo'.const_smul (c • (1 : ℂ))
    zero_at_cusps' hc g hg := by
      simp_rw [IsZeroAtImInfty, Filter.ZeroAtFilter, SlashInvariantForm.toFun_eq_coe,
        FunLike.coe_smul, toSlashInvariantForm_coe, ← smul_one_smul ℂ c ⇑f, smul_slash]
      exact (f.zero_at_cusps' hc g hg).smul _ }
/-
**CuspForm.instSMulApply** 是 Mathlib 中的一个实例，位于命名空间 `CuspForm`。
形式化陈述：instSMulApply : IsSMulApply α (CuspForm Γ k) ℍ Complex where smul_apply _ 
_ _
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instSMulApply : IsSMulApply α (CuspForm Γ k) ℍ ℂ where
  smul_apply _ _ _ := rfl

@[deprecated (since := "2026-07-10")] alias coe_smul := FunLike.coe_smul

@[deprecated (since := "2026-07-10")] protected alias smul_apply := smul_apply

end

section
-- scalar multiplication by complex types (assuming `IsGLPos Γ`)

variable {α : Type*} [SMul α ℂ] [IsScalarTower α ℂ ℂ] [Γ.HasDetOne]

/-
**CuspForm.IsGLPos.instSMul** 是 Mathlib 中的一个定义，位于命名空间 `CuspForm.IsGLPos`。
形式化陈述：{Γ : Subgroup (GL (Fin 2) ℝ)} →   {k : ℤ} → {α : Type u_2} → [inst : SMul 
α ℂ] → [IsScalarTower α ℂ ℂ] → [Γ.HasDetOne] → SMul α (CuspForm Γ k)
参数：GL (Fin 2) ℝ；CuspForm Γ k。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance IsGLPos.instSMul : SMul α (CuspForm Γ k) where smul c f :=
  { toSlashInvariantForm := c • f.1
    holo' := by simpa using f.holo'.const_smul (c • (1 : ℂ))
    zero_at_cusps' hc g hg := by
      simp_rw [IsZeroAtImInfty, Filter.ZeroAtFilter, SlashInvariantForm.toFun_eq_coe,
        FunLike.coe_smul, toSlashInvariantForm_coe, ← smul_one_smul ℂ c ⇑f,
        smul_slash]
      exact (f.zero_at_cusps' hc g hg).smul _ }
/-
**CuspForm.IsGLPos.instSMulApply** 是 Mathlib 中的一个定理，位于命名空间 `CuspForm.IsGLPos`。
形式化陈述：∀ {Γ : Subgroup (GL (Fin 2) ℝ)} {k : ℤ} {α : Type u_2} [inst : SMul α ℂ] [
inst_1 : IsScalarTower α ℂ ℂ]   [inst_2 : Γ.HasDetOne], IsSMulApply α (CuspForm 
Γ k) UpperHalfPlane ℂ
参数：GL (Fin 2) ℝ；CuspForm Γ k。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance IsGLPos.instSMulApply : IsSMulApply α (CuspForm Γ k) ℍ ℂ where
  smul_apply _ _ _ := rfl

@[deprecated (since := "2026-07-10")] alias IsGLPos.coe_smul := FunLike.coe_smul

@[deprecated (since := "2026-07-10")] protected alias IsGLPos.smul_apply := smul_apply

end

/-
**CuspForm.instNeg** 是 Mathlib 中的一个实例，位于命名空间 `CuspForm`。
形式化陈述：instNeg : Neg (CuspForm Γ k)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instNeg : Neg (CuspForm Γ k) :=
  ⟨fun f =>
    { toSlashInvariantForm := -f.1
      holo' := f.holo'.neg
      zero_at_cusps' hc g hg := by simpa using! (f.zero_at_cusps' hc g hg).neg }⟩
/-
**CuspForm.** 是 Mathlib 中的一个实例，位于命名空间 `CuspForm`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : IsNegApply (CuspForm Γ k) ℍ ℂ where
  neg_apply _ _ := rfl

@[deprecated (since := "2026-07-10")] alias coe_neg := FunLike.coe_neg

@[deprecated (since := "2026-07-10")] protected alias neg_apply := neg_apply
/-
**CuspForm.instSub** 是 Mathlib 中的一个实例，位于命名空间 `CuspForm`。
形式化陈述：instSub : Sub (CuspForm Γ k)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instSub : Sub (CuspForm Γ k) :=
  ⟨fun f g => f + -g⟩
/-
**CuspForm.** 是 Mathlib 中的一个实例，位于命名空间 `CuspForm`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : IsSubApply (CuspForm Γ k) ℍ ℂ where
  sub_apply _ _ _ := rfl

@[deprecated (since := "2026-07-10")] alias coe_sub := FunLike.coe_sub

@[deprecated (since := "2026-07-10")] protected alias sub_apply := sub_apply
/-
**CuspForm.** 是 Mathlib 中的一个实例，位于命名空间 `CuspForm`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : AddCommGroup (CuspForm Γ k) := fast_instance% FunLike.addCommGroup

@[deprecated (since := "2026-07-10")] alias coeHom := FunLike.coeMonoidHom

@[deprecated (since := "2026-07-10")] alias coeHom_apply := FunLike.coeMonoidHom_apply
/-
**CuspForm.** 是 Mathlib 中的一个实例，位于命名空间 `CuspForm`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Module ℝ (CuspForm Γ k) := fast_instance% FunLike.module
/-
**CuspForm.** 是 Mathlib 中的一个实例，位于命名空间 `CuspForm`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Γ.HasDetOne] : Module ℂ (CuspForm Γ k) := fast_instance% FunLike.module
/-
**CuspForm.** 是 Mathlib 中的一个实例，位于命名空间 `CuspForm`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Inhabited (CuspForm Γ k) :=
  ⟨0⟩
/-
**CuspForm.** 是 Mathlib 中的一个实例，位于命名空间 `CuspForm`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 99) [FunLike F ℍ ℂ] [CuspFormClass F Γ k] : ModularFormClass F Γ k where
  slash_action_eq := SlashInvariantFormClass.slash_action_eq
  holo := CuspFormClass.holo
  bdd_at_cusps f _ hc g hg := (CuspFormClass.zero_at_cusps f hc g hg).boundedAtFilter

/-- Multiplying a `CuspForm` by a `ModularForm` gives a `CuspForm` (the cusp condition is
preserved since a function tending to zero times a bounded function tends to zero). -/
@[simps! -fullyApplied coe]
/-
**CuspForm.mulModularForm** 是 Mathlib 中的一个定义，位于命名空间 `CuspForm`。
形式化陈述：mulModularForm [Γ.HasDetPlusMinusOne] {k₁ k₂ : Int} (f : CuspForm Γ k₁) (g
 : ModularForm Γ k₂) : CuspForm Γ (k₁ + k₂) where toSlashInvariantForm
参数：f : CuspForm Γ k₁；g : ModularForm Γ k₂。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Multiplying a `CuspForm` by a `ModularForm` gives a `CuspForm` (the cusp conditi
on is
preserved since a function tending to zero times a bounded function tends to zer
o).
-/
def mulModularForm [Γ.HasDetPlusMinusOne] {k₁ k₂ : ℤ} (f : CuspForm Γ k₁) (g : ModularForm Γ k₂) :
    CuspForm Γ (k₁ + k₂) where
  toSlashInvariantForm := f.1.mul g.1
  holo' := f.holo'.mul g.holo'
  zero_at_cusps' hc γ hγ := by
    simpa [mul_slash] using!
      ((f.zero_at_cusps' hc γ hγ).mul_boundedAtFilter (g.bdd_at_cusps' hc γ hγ)).smul _

/-- Cast for cusp forms, which is useful for avoiding `Heq`s. Optionally transports along
an equality of subgroups. -/
/-
**CuspForm.mcast** 是 Mathlib 中的一个定义，位于命名空间 `CuspForm`。
形式化陈述：mcast {a b : Int} {Γ Γ' : Subgroup (GL (Fin 2) Real)} (h : a = b) (f : Cus
pForm Γ a) (hΓ : Γ' = Γ
参数：GL (Fin 2) Real；h : a = b；f : CuspForm Γ a。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CuspForm.holo'`：∀ {Γ : Subgroup (GL (Fin 2) ℝ)} {k : ℤ} (self : CuspForm
 Γ k), MDiff ⇑self.toSlashInvariantForm

--- 原说明 ---
Cast for cusp forms, which is useful for avoiding `Heq`s. Optionally transports 
along
an equality of subgroups.
-/
def mcast {a b : ℤ} {Γ Γ' : Subgroup (GL (Fin 2) ℝ)} (h : a = b) (f : CuspForm Γ a)
    (hΓ : Γ' = Γ := by rfl) : CuspForm Γ' b where
  toFun := (f : ℍ → ℂ)
  slash_action_eq' A hA := h ▸ f.slash_action_eq' A (hΓ ▸ hA)
  holo' := f.holo'
  zero_at_cusps' hc := h ▸ f.zero_at_cusps' (hΓ ▸ hc)

end CuspForm

namespace ModularForm

section GradedRing

/-- Cast for modular forms, which is useful for avoiding `Heq`s. Optionally transports along
an equality of subgroups. -/
@[simps -fullyApplied coe]
/-
**ModularForm.mcast** 是 Mathlib 中的一个定义，位于命名空间 `ModularForm`。
形式化陈述：mcast {a b : Int} {Γ Γ' : Subgroup (GL (Fin 2) Real)} (h : a = b) (f : Mod
ularForm Γ a) (hΓ : Γ' = Γ
参数：GL (Fin 2) Real；h : a = b；f : ModularForm Γ a。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `ModularForm.holo'`：∀ {Γ : Subgroup (GL (Fin 2) ℝ)} {k : ℤ} (self : Modul
arForm Γ k), MDiff ⇑self.toSlashInvariantForm

--- 原说明 ---
Cast for modular forms, which is useful for avoiding `Heq`s. Optionally transpor
ts along
an equality of subgroups.
-/
def mcast {a b : ℤ} {Γ Γ' : Subgroup (GL (Fin 2) ℝ)} (h : a = b) (f : ModularForm Γ a)
    (hΓ : Γ' = Γ := by rfl) : ModularForm Γ' b where
  toFun := (f : ℍ → ℂ)
  slash_action_eq' A hA := h ▸ f.slash_action_eq' A (hΓ ▸ hA)
  holo' := f.holo'
  bdd_at_cusps' hc := h ▸ f.bdd_at_cusps' (hΓ ▸ hc)

/-- `mcast` does not change the pointwise values of a modular form. -/
/-
**ModularForm.mcast_apply** 是 Mathlib 中的一个定理，位于命名空间 `ModularForm`。
形式化陈述：mcast_apply {a b : Int} {Γ Γ' : Subgroup (GL (Fin 2) Real)} (h : a = b) (f
 : ModularForm Γ a) (hΓ : Γ' = Γ
参数：GL (Fin 2) Real；h : a = b；f : ModularForm Γ a。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`mcast` does not change the pointwise values of a modular form.
-/
theorem mcast_apply {a b : ℤ} {Γ Γ' : Subgroup (GL (Fin 2) ℝ)} (h : a = b) (f : ModularForm Γ a)
    (hΓ : Γ' = Γ := by rfl) (z : ℍ) : mcast h f hΓ z = f z := rfl

@[simp]
/-
**ModularForm.mcast_eq_zero_iff** 是 Mathlib 中的一个引理，位于命名空间 `ModularForm`。
形式化陈述：mcast_eq_zero_iff {a b : Int} {Γ Γ' : Subgroup (GL (Fin 2) Real)} (h : a =
 b) (hΓ : Γ' = Γ) (f : ModularForm Γ a) : mcast h f hΓ = 0 ↔ f = 0
参数：GL (Fin 2) Real；h : a = b；hΓ : Γ' = Γ；f : ModularForm Γ a。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ModularForm.instIsZeroApplyUpperHalfPlaneComplex`：∀ {Γ : Subgroup (GL (F
in 2) ℝ)} {k : ℤ}, IsZeroApply (ModularForm Γ k) UpperHalfPlane ℂ
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `ModularForm.coe_mcast`：∀ {a b : ℤ} {Γ Γ' : Subgroup (GL (Fin 2) ℝ)} (h :
 a = b) (f : ModularForm Γ a)   (hΓ : autoParam (Γ' = Γ) ModularForm.mcast._auto
_1), ⇑(Modu…
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma mcast_eq_zero_iff {a b : ℤ} {Γ Γ' : Subgroup (GL (Fin 2) ℝ)} (h : a = b)
    (hΓ : Γ' = Γ) (f : ModularForm Γ a) : mcast h f hΓ = 0 ↔ f = 0 := by
  simp [← FunLike.coe_zero_iff]

@[ext (iff := false)]
/-
**ModularForm.gradedMonoid_eq_of_cast** 是 Mathlib 中的一个定理，位于命名空间 `ModularForm`。
形式化陈述：gradedMonoid_eq_of_cast {Γ : Subgroup (GL (Fin 2) Real)} {a b : GradedMono
id (ModularForm Γ)} (h : a.fst = b.fst) (h2 : mcast h a.snd = b.snd) : a = b
参数：GL (Fin 2) Real；ModularForm Γ；h : a.fst = b.fst；h2 : mcast h a.snd = b.snd。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
-/
theorem gradedMonoid_eq_of_cast {Γ : Subgroup (GL (Fin 2) ℝ)} {a b : GradedMonoid (ModularForm Γ)}
    (h : a.fst = b.fst) (h2 : mcast h a.snd = b.snd) : a = b := by
  obtain ⟨i, a⟩ := a
  cases h
  exact congr_arg _ h2

/-- The `n`-th power of a modular form, as a modular form of weight `n * k`. -/
/-
**ModularForm.pow** 是 Mathlib 中的一个定义，位于命名空间 `ModularForm`。
形式化陈述：pow {Γ : Subgroup (GL (Fin 2) Real)} [Γ.HasDetPlusMinusOne] {k : Int} (f :
 ModularForm Γ k) (n : Nat) : ModularForm Γ (n * k)
参数：GL (Fin 2) Real；f : ModularForm Γ k；n : Nat。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The `n`-th power of a modular form, as a modular form of weight `n * k`.
-/
def pow {Γ : Subgroup (GL (Fin 2) ℝ)} [Γ.HasDetPlusMinusOne] {k : ℤ} (f : ModularForm Γ k)
    (n : ℕ) : ModularForm Γ (n * k) :=
  n.rec (mcast (by simp) (1 : ModularForm Γ 0)) (fun n g ↦ (g.mul f).mcast (by grind))

@[simp]
/-
**ModularForm.coe_pow** 是 Mathlib 中的一个引理，位于命名空间 `ModularForm`。
形式化陈述：coe_pow {Γ : Subgroup (GL (Fin 2) Real)} [Γ.HasDetPlusMinusOne] {k : Int} 
(f : ModularForm Γ k) (n : Nat) : ⇑(f.pow n) = (⇑f) ^ n
参数：GL (Fin 2) Real；f : ModularForm Γ k；n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ModularForm.coe_mcast`：∀ {a b : ℤ} {Γ Γ' : Subgroup (GL (Fin 2) ℝ)} (h :
 a = b) (f : ModularForm Γ a)   (hΓ : autoParam (Γ' = Γ) ModularForm.mcast._auto
_1), ⇑(Modu…
· 使用定理 `pow_zero`：pow_zero (a : M) : a ^ 0 = 1
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `ModularForm.coe_mul`：∀ {Γ : Subgroup (GL (Fin 2) ℝ)} {k_1 k_2 : ℤ} [inst
 : Γ.HasDetPlusMinusOne] (f : ModularForm Γ k_1)   (g : ModularForm Γ k_2), ⇑(f.
mul g) = …
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `pow_succ`：pow_succ (a : M) (n : Nat) : a ^ (n + 1) = a ^ n * a
-/
lemma coe_pow {Γ : Subgroup (GL (Fin 2) ℝ)} [Γ.HasDetPlusMinusOne] {k : ℤ}
    (f : ModularForm Γ k) (n : ℕ) : ⇑(f.pow n) = (⇑f) ^ n := by
  induction n with
  | zero => simp [pow]
  | succ n ih => simp_all only [pow, coe_mcast, coe_mul, pow_succ]
/-
**ModularForm.** 是 Mathlib 中的一个实例，位于命名空间 `ModularForm`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (Γ : Subgroup (GL (Fin 2) ℝ)) [Γ.HasDetPlusMinusOne] :
    GradedMonoid.GOne (ModularForm Γ) where
  one := 1
/-
**ModularForm.** 是 Mathlib 中的一个实例，位于命名空间 `ModularForm`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (Γ : Subgroup (GL (Fin 2) ℝ)) [Γ.HasDetPlusMinusOne] :
    GradedMonoid.GMul (ModularForm Γ) where
  mul f g := f.mul g
/-
**ModularForm.instGCommRing** 是 Mathlib 中的一个实例，位于命名空间 `ModularForm`。
形式化陈述：instGCommRing (Γ : Subgroup (GL (Fin 2) Real)) [Γ.HasDetPlusMinusOne] : Di
rectSum.GCommRing (ModularForm Γ) where one_mul _
参数：Γ : Subgroup (GL (Fin 2) Real)。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instGCommRing (Γ : Subgroup (GL (Fin 2) ℝ)) [Γ.HasDetPlusMinusOne] :
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
/-
**ModularForm.instGAlgebra** 是 Mathlib 中的一个实例，位于命名空间 `ModularForm`。
形式化陈述：instGAlgebra (Γ : Subgroup (GL (Fin 2) Real)) [Γ.HasDetOne] : DirectSum.GA
lgebra Complex (ModularForm Γ) where toFun
参数：Γ : Subgroup (GL (Fin 2) Real)。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instGAlgebra (Γ : Subgroup (GL (Fin 2) ℝ)) [Γ.HasDetOne] :
    DirectSum.GAlgebra ℂ (ModularForm Γ) where
  toFun := { toFun z := const z, map_zero' := rfl, map_add' := fun _ _ => rfl }
  map_one := rfl
  map_mul _x _y := rfl
  commutes _c _x := gradedMonoid_eq_of_cast (add_comm _ _) (ext fun _ => mul_comm _ _)
  smul_def _x _x := gradedMonoid_eq_of_cast (zero_add _).symm (ext fun _ => rfl)

open scoped DirectSum in
/-
**ModularForm.** 是 Mathlib 中的一个示例，位于命名空间 `ModularForm`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
example (Γ : Subgroup (GL (Fin 2) ℝ)) [Γ.HasDetOne] : Algebra ℂ (⨁ i, ModularForm Γ i) :=
inferInstance

/-- Bridge between the auto-derived graded-monoid power `GradedMonoid.GMonoid.gnpow` and the
bespoke `ModularForm.pow`: as elements of `GradedMonoid (ModularForm Γ)`, the pair
`⟨n • k, gnpow n f⟩` agrees with `⟨n * k, f.pow n⟩`. -/
/-
**ModularForm.gnpow_eq_pow** 是 Mathlib 中的一个定理，位于命名空间 `ModularForm`。
形式化陈述：gnpow_eq_pow {Γ : Subgroup (GL (Fin 2) Real)} [Γ.HasDetPlusMinusOne] {k : 
Int} (f : ModularForm Γ k) (n : Nat) : (⟨n • k, GradedMonoid.GMonoid.gnpow n f⟩ 
: GradedMonoid (ModularForm Γ)) = ⟨(n : Int) * k, f.pow n⟩
参数：GL (Fin 2) Real；f : ModularForm Γ k；n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `GradedMonoid.GMonoid.gnpow_zero'`：∀ {ι : Type u_1} {A : ι → Type u_2} {i
nst : AddMonoid ι} [self : GradedMonoid.GMonoid A] (a : GradedMonoid A),   Grade
dMonoid.mk (0 • a.fst)…
· 使用定理 `ModularForm.gradedMonoid_eq_of_cast`：gradedMonoid_eq_of_cast {Γ : Subgro
up (GL (Fin 2) Real)} {a b : GradedMonoid (ModularForm Γ)} (h : a.fst = b.fst) (
h2 : mcast h a.snd = b.sn…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `ModularForm.ext`：ModularForm.ext {f g : ModularForm Γ k} (h : forall x, 
f x = g x) : f = g
· 使用定理 `GradedMonoid.GMonoid.gnpow_succ'`：∀ {ι : Type u_1} {A : ι → Type u_2} {i
nst : AddMonoid ι} [self : GradedMonoid.GMonoid A] (n : ℕ) (a : GradedMonoid A),
   GradedMonoid.mk (n.…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Mathlib.Tactic.Ring.of_eq`：∀ {α : Sort u_2} {a b c : α}, a = c → b = c →
 a = b
· 使用定理 `Mathlib.Tactic.Ring.Common.add_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' + b' = c → a + b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' * b' = c → a * b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.atom_pf`：∀ {R : Type u_1} [inst : CommSemirin
g R] {b : R} (a : R) {e : ℕ},   Nat.rawCast 1 = e → a ^ e * Nat.rawCast 1 = b → 
a = b + 0
· 使用定理 `Mathlib.Tactic.Ring.Common.add_mul`：∀ {R : Type u_1} [inst : CommSemirin
g R] {a₁ a₂ b c₁ c₂ d : R},   a₁ * b = c₁ → a₂ * b = c₂ → c₁ + c₂ = d → (a₁ + a₂
) * b = d
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_add`：∀ {R : Type u_1} [inst : CommSemirin
g R] {a b₁ b₂ c₁ c₂ d : R},   a * b₁ = c₁ → a * b₂ = c₂ → c₁ + 0 + c₂ = d → a * 
(b₁ + b₂) = d
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_pf_left`：∀ {R : Type u_1} [inst : CommSem
iring R] {a₃ b c : R} (a₁ : R) (a₂ : ℕ), a₃ * b = c → a₁ ^ a₂ * a₃ * b = a₁ ^ a₂
 * c
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_pf_right`：∀ {R : Type u_1} [inst : CommSe
miring R] {a b₃ c : R} (b₁ : R) (b₂ : ℕ), a * b₃ = c → a * (b₁ ^ b₂ * b₃) = b₁ ^
 b₂ * c
· 使用定理 `Mathlib.Meta.NormNum.IsNat.to_raw_eq`：∀ {α : Type u} {a : α} {n : ℕ} [in
st : AddMonoidWithOne α], Mathlib.Meta.NormNum.IsNat a n → a = n.rawCast
· 使用定理 `Mathlib.Meta.NormNum.isNat_mul`：∀ {α : Type u_1} [inst : Semiring α] {f 
: α → α → α} {a b : α} {a' b' c : ℕ},   f = HMul.hMul →     Mathlib.Meta.NormNum
.IsNat a a' →       …
· 使用定理 `Mathlib.Meta.NormNum.IsNat.of_raw`：∀ (α : Type u_1) [inst : AddMonoidWit
hOne α] (n : ℕ), Mathlib.Meta.NormNum.IsNat n.rawCast n
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_zero`：∀ {R : Type u_1} [inst : CommSemiri
ng R] (a : R), a * 0 = 0
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_add_zero`：∀ {R : Type u_1} [inst : Com
mSemiring R] (a : R), a + 0 = a
· 使用定理 `Mathlib.Tactic.Ring.Common.zero_mul`：∀ {R : Type u_1} [inst : CommSemiri
ng R] (b : R), 0 * b = 0
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_add_lt`：∀ {R : Type u_1} [inst : CommS
emiring R] {a₂ b c : R} (a₁ : R), a₂ + b = c → a₁ + a₂ + b = a₁ + c
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_zero_add`：∀ {R : Type u_1} [inst : Com
mSemiring R] (b : R), 0 + b = b
· 使用定理 `Mathlib.Tactic.Ring.cast_pos`：∀ {R : Type u_1} [inst : CommSemiring R] {
a : R} {n : ℕ}, Mathlib.Meta.NormNum.IsNat a n → a = n.rawCast + 0
· 使用定理 `Mathlib.Meta.NormNum.isNat_ofNat`：isNat_ofNat (α : Type u) [AddMonoidWit
hOne α] {a : α} {n : Nat} (h : n = a) : IsNat a n
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_add_gt`：∀ {R : Type u_1} [inst : CommS
emiring R] {a b₂ c : R} (b₁ : R), a + b₂ = c → a + (b₁ + b₂) = b₁ + c

--- 原说明 ---
Bridge between the auto-derived graded-monoid power `GradedMonoid.GMonoid.gnpow`
 and the
bespoke `ModularForm.pow`: as elements of `GradedMonoid (ModularForm Γ)`, the pa
ir
`⟨n • k, gnpow n f⟩` agrees with `⟨n * k, f.pow n⟩`.
-/
theorem gnpow_eq_pow {Γ : Subgroup (GL (Fin 2) ℝ)} [Γ.HasDetPlusMinusOne]
    {k : ℤ} (f : ModularForm Γ k) (n : ℕ) :
    (⟨n • k, GradedMonoid.GMonoid.gnpow n f⟩ : GradedMonoid (ModularForm Γ)) =
      ⟨(n : ℤ) * k, f.pow n⟩ := by
  induction n with
  | zero =>
    refine (GradedMonoid.GMonoid.gnpow_zero' ⟨k, f⟩).trans ?_
    exact gradedMonoid_eq_of_cast (zero_mul k).symm (ModularForm.ext fun _ ↦ rfl)
  | succ n ih =>
    refine (GradedMonoid.GMonoid.gnpow_succ' n ⟨k, f⟩).trans ?_
    refine (congrArg (fun x : GradedMonoid (ModularForm Γ) ↦ x * ⟨k, f⟩) ih).trans ?_
    exact gradedMonoid_eq_of_cast (show ((n : ℤ) * k + k = (n + 1) * k) by ring)
      (ModularForm.ext fun _ ↦ rfl)

/-- The `n`-th power of `DirectSum.of _ k f` lands in grade `n * k` and is given by `f.pow n`. -/
/-
**ModularForm.directSum_of_pow** 是 Mathlib 中的一个引理，位于命名空间 `ModularForm`。
形式化陈述：directSum_of_pow {Γ : Subgroup (GL (Fin 2) Real)} [Γ.HasDetPlusMinusOne] {
k : Int} (f : ModularForm Γ k) (n : Nat) : (DirectSum.of (ModularForm Γ) k f) ^ 
n = .of (ModularForm Γ) ((n : Int) * k) (f.pow n)
参数：GL (Fin 2) Real；f : ModularForm Γ k；n : Nat。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The `n`-th power of `DirectSum.of _ k f` lands in grade `n * k` and is given by 
`f.pow n`.
-/
lemma directSum_of_pow {Γ : Subgroup (GL (Fin 2) ℝ)} [Γ.HasDetPlusMinusOne]
    {k : ℤ} (f : ModularForm Γ k) (n : ℕ) :
    (DirectSum.of (ModularForm Γ) k f) ^ n = .of (ModularForm Γ) ((n : ℤ) * k) (f.pow n) := by
  grind [DirectSum.ofPow, DirectSum.of_eq_of_gradedMonoid_eq (gnpow_eq_pow f n)]

open Filter SlashInvariantForm

/-- Given `ModularForm`'s `F i` of weight `k i` for `i : ι`, define the form which as a
function is a product of those indexed by `s : Finset ι` with weight `m = ∑ i ∈ s, k i`. -/
@[simps! -fullyApplied]
/-
**ModularForm.prod** 是 Mathlib 中的一个定义，位于命名空间 `ModularForm`。
形式化陈述：prod {ι : Type} {s : Finset ι} {k : ι -> Int} (m : Int) (hm : m = ∑ i in s
, k i) {Γ : Subgroup (GL (Fin 2) Real)} [Γ.HasDetPlusMinusOne] (F : (i : ι) -> M
odularForm Γ (k i)) : ModularForm Γ m where toSlashInvariantForm
参数：m : Int；hm : m = ∑ i in s, k i；GL (Fin 2) Real；F : (i : ι) -> ModularForm Γ (
k i)。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given `ModularForm`'s `F i` of weight `k i` for `i : ι`, define the form which a
s a
function is a product of those indexed by `s : Finset ι` with weight `m = ∑ i ∈ 
s, k i`.
-/
def prod {ι : Type} {s : Finset ι} {k : ι → ℤ} (m : ℤ)
    (hm : m = ∑ i ∈ s, k i) {Γ : Subgroup (GL (Fin 2) ℝ)} [Γ.HasDetPlusMinusOne]
    (F : (i : ι) → ModularForm Γ (k i)) : ModularForm Γ m where
  toSlashInvariantForm := SlashInvariantForm.prod m hm (fun i ↦ (F i))
  holo' := MDifferentiable.prod (t := s) (f := fun (i : ι) ↦ (F i).1)
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
/-
**ModularForm.prodEqualWeights** 是 Mathlib 中的一个定义，位于命名空间 `ModularForm`。
形式化陈述：prodEqualWeights {ι : Type} {s : Finset ι} {k : Int} {Γ : Subgroup (GL (Fi
n 2) Real)} [Γ.HasDetPlusMinusOne] (F : (i : ι) -> ModularForm Γ k) : ModularFor
m Γ (s.card * k)
参数：GL (Fin 2) Real；F : (i : ι) -> ModularForm Γ k。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given `ModularForm`'s `F i` of weight `k`, define the form which as a function i
s a product of
those indexed by `s : Finset ι` with weight `#s * k`.
-/
def prodEqualWeights {ι : Type} {s : Finset ι} {k : ℤ}
    {Γ : Subgroup (GL (Fin 2) ℝ)} [Γ.HasDetPlusMinusOne]
    (F : (i : ι) → ModularForm Γ k) : ModularForm Γ (s.card * k) :=
  prod (s := s) (s.card * k) (by simp) F

end GradedRing

end ModularForm

section translate

open ModularForm OnePoint

variable {k : ℤ} {Γ : Subgroup (GL (Fin 2) ℝ)} {F : Type*} [FunLike F ℍ ℂ] (f : F)

open ConjAct Pointwise in
/-- Translating a `ModularForm` by `GL(2, ℝ)`, to obtain a new `ModularForm`. -/
/-
**ModularForm.translate** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：ModularForm.translate [ModularFormClass F Γ k] (g : GL (Fin 2) Real) : Mod
ularForm (toConjAct g⁻¹ • Γ) k where __
参数：g : GL (Fin 2) Real。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `ModularFormClass.toSlashInvariantFormClass`：∀ {F : Type u_2} {Γ : outPar
am (Subgroup (GL (Fin 2) ℝ))} {k : outParam ℤ} {inst : FunLike F UpperHalfPlane 
ℂ}   [self : ModularFormClass F …

--- 原说明 ---
Translating a `ModularForm` by `GL(2, ℝ)`, to obtain a new `ModularForm`.
-/
noncomputable def ModularForm.translate [ModularFormClass F Γ k] (g : GL (Fin 2) ℝ) :
    ModularForm (toConjAct g⁻¹ • Γ) k where
  __ := SlashInvariantForm.translate f g
  bdd_at_cusps' {c} hc γ hγ := by
    rw [SlashInvariantForm.toFun_eq_coe, SlashInvariantForm.coe_translate,
      ← SlashAction.slash_mul, ← isBoundedAt_infty_iff, ← OnePoint.IsBoundedAt.smul_iff]
    apply ModularFormClass.bdd_at_cusps f
    simpa [mul_smul, hγ] using hc.smul g
  holo' := (ModularFormClass.holo f).slash k g

@[simp]
/-
**ModularForm.coe_translate** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：ModularForm.coe_translate [ModularFormClass F Γ k] (g : GL (Fin 2) Real) :
 translate f g = ⇑f ∣[k] g
参数：g : GL (Fin 2) Real。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma ModularForm.coe_translate [ModularFormClass F Γ k] (g : GL (Fin 2) ℝ) :
    translate f g = ⇑f ∣[k] g :=
  rfl

open ConjAct Pointwise in
/-- Translating a `CuspForm` by `SL(2, ℤ)`, to obtain a new `CuspForm`. -/
/-
**CuspForm.translate** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：CuspForm.translate [CuspFormClass F Γ k] (g : GL (Fin 2) Real) : CuspForm 
(toConjAct g⁻¹ • Γ) k where __
参数：g : GL (Fin 2) Real。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CuspForm.instModularFormClassOfCuspFormClass`：∀ {F : Type u_1} {Γ : Subg
roup (GL (Fin 2) ℝ)} {k : ℤ} [inst : FunLike F UpperHalfPlane ℂ] [CuspFormClass 
F Γ k],   ModularFormClass F Γ k

--- 原说明 ---
Translating a `CuspForm` by `SL(2, ℤ)`, to obtain a new `CuspForm`.
-/
noncomputable def CuspForm.translate [CuspFormClass F Γ k] (g : GL (Fin 2) ℝ) :
    CuspForm (toConjAct g⁻¹ • Γ) k where
  __ := ModularForm.translate f g
  zero_at_cusps' {c} hc γ hγ := by
    rw [SlashInvariantForm.toFun_eq_coe, ModularForm.toSlashInvariantForm_coe,
      ModularForm.coe_translate, ← SlashAction.slash_mul, ← isZeroAt_infty_iff,
      ← OnePoint.IsZeroAt.smul_iff]
    apply CuspFormClass.zero_at_cusps f
    simpa [mul_smul, hγ] using hc.smul g

@[simp]
/-
**CuspForm.coe_translate** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：CuspForm.coe_translate [CuspFormClass F Γ k] (g : SL(2, Int)) : translate 
f g = ⇑f ∣[k] g
参数：g : SL(2, Int)。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma CuspForm.coe_translate [CuspFormClass F Γ k] (g : SL(2, ℤ)) :
    translate f g = ⇑f ∣[k] g :=
  rfl

end translate

section SL2Z

open ModularForm CuspForm OnePoint

variable {k F} {Γ : Subgroup (GL (Fin 2) ℝ)} [FunLike F ℍ ℂ] (f : F)

/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Γ.IsArithmetic] : Fact (IsCusp ∞ Γ) :=
  ⟨by simpa [Subgroup.IsArithmetic.isCusp_iff_isCusp_SL2Z, isCusp_SL2Z_iff]
    using ⟨_, OnePoint.map_infty _⟩⟩
/-
**ModularFormClass.bdd_at_infty** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：ModularFormClass.bdd_at_infty [ModularFormClass F Γ k] [Fact (IsCusp ∞ Γ)]
 : IsBoundedAtImInfty f
参数：IsCusp ∞ Γ。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `OnePoint.isBoundedAt_infty_iff`：isBoundedAt_infty_iff : IsBoundedAt ∞ f 
k ↔ IsBoundedAtImInfty f
· 使用定理 `ModularFormClass.bdd_at_cusps`：∀ {F : Type u_2} {Γ : outParam (Subgroup 
(GL (Fin 2) ℝ))} {k : outParam ℤ} {inst : FunLike F UpperHalfPlane ℂ}   [self : 
ModularFormClass F …
· 使用定理 `Fact.out`：∀ {p : Prop} [self : Fact p], p
-/
lemma ModularFormClass.bdd_at_infty [ModularFormClass F Γ k] [Fact (IsCusp ∞ Γ)] :
    IsBoundedAtImInfty f :=
  isBoundedAt_infty_iff.mp <| bdd_at_cusps f Fact.out
/-
**CuspFormClass.zero_at_infty** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：CuspFormClass.zero_at_infty [CuspFormClass F Γ k] [Fact (IsCusp ∞ Γ)] : Is
ZeroAtImInfty f
参数：IsCusp ∞ Γ。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `OnePoint.isZeroAt_infty_iff`：isZeroAt_infty_iff : IsZeroAt ∞ f k ↔ IsZer
oAtImInfty f
· 使用定理 `CuspFormClass.zero_at_cusps`：∀ {F : Type u_2} {Γ : outParam (Subgroup (G
L (Fin 2) ℝ))} {k : outParam ℤ} {inst : FunLike F UpperHalfPlane ℂ}   [self : Cu
spFormClass F Γ k…
· 使用定理 `Fact.out`：∀ {p : Prop} [self : Fact p], p
-/
lemma CuspFormClass.zero_at_infty [CuspFormClass F Γ k] [Fact (IsCusp ∞ Γ)] :
    IsZeroAtImInfty f :=
  isZeroAt_infty_iff.mp <| zero_at_cusps f Fact.out

variable [Γ.IsArithmetic] (g : SL(2, ℤ))
/-
**ModularFormClass.bdd_at_infty_slash** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：ModularFormClass.bdd_at_infty_slash [ModularFormClass F Γ k] : IsBoundedAt
ImInfty (f ∣[k] g)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `OnePoint.isBoundedAt_infty_iff`：isBoundedAt_infty_iff : IsBoundedAt ∞ f 
k ↔ IsBoundedAtImInfty f
· 使用定理 `ModularForm.SL_slash`：SL_slash (γ : SL(2, Int)) : f ∣[k] γ = f ∣[k] (γ :
 GL (Fin 2) Real)
· 使用定理 `OnePoint.IsBoundedAt.smul_iff`：∀ {c : OnePoint ℝ} {f : UpperHalfPlane → 
ℂ} {k : ℤ} {g : GL (Fin 2) ℝ},   (g • c).IsBoundedAt f k ↔ c.IsBoundedAt (SlashA
ction.map k g f) k
· 使用定理 `ModularFormClass.bdd_at_cusps`：∀ {F : Type u_2} {Γ : outParam (Subgroup 
(GL (Fin 2) ℝ))} {k : outParam ℤ} {inst : FunLike F UpperHalfPlane ℂ}   [self : 
ModularFormClass F …
· 使用引理 `Subgroup.IsArithmetic.isCusp_iff_isCusp_SL2Z`：Subgroup.IsArithmetic.isCu
sp_iff_isCusp_SL2Z (𝒢 : Subgroup (GL (Fin 2) Real)) [𝒢.IsArithmetic] {c : OnePoi
nt Real} : IsCusp c 𝒢 ↔ IsCusp c 𝒮…
· 使用引理 `isCusp_SL2Z_iff'`：isCusp_SL2Z_iff' {c : OnePoint Real} : IsCusp c 𝒮ℒ ↔ e
xists g : SL(2, Int), c = mapGL Real g • ∞
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma ModularFormClass.bdd_at_infty_slash [ModularFormClass F Γ k] :
    IsBoundedAtImInfty (f ∣[k] g) := by
  rw [← OnePoint.isBoundedAt_infty_iff, SL_slash, ← OnePoint.IsBoundedAt.smul_iff]
  apply bdd_at_cusps f
  rw [Subgroup.IsArithmetic.isCusp_iff_isCusp_SL2Z, isCusp_SL2Z_iff']
  exact ⟨g, by simp [mapGL]⟩
/-
**CuspFormClass.zero_at_infty_slash** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：CuspFormClass.zero_at_infty_slash [CuspFormClass F Γ k] : IsZeroAtImInfty 
(f ∣[k] g)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `OnePoint.isZeroAt_infty_iff`：isZeroAt_infty_iff : IsZeroAt ∞ f k ↔ IsZer
oAtImInfty f
· 使用定理 `ModularForm.SL_slash`：SL_slash (γ : SL(2, Int)) : f ∣[k] γ = f ∣[k] (γ :
 GL (Fin 2) Real)
· 使用定理 `OnePoint.IsZeroAt.smul_iff`：∀ {c : OnePoint ℝ} {f : UpperHalfPlane → ℂ} 
{k : ℤ} {g : GL (Fin 2) ℝ},   (g • c).IsZeroAt f k ↔ c.IsZeroAt (SlashAction.map
 k g f) k
· 使用定理 `CuspFormClass.zero_at_cusps`：∀ {F : Type u_2} {Γ : outParam (Subgroup (G
L (Fin 2) ℝ))} {k : outParam ℤ} {inst : FunLike F UpperHalfPlane ℂ}   [self : Cu
spFormClass F Γ k…
· 使用引理 `Subgroup.IsArithmetic.isCusp_iff_isCusp_SL2Z`：Subgroup.IsArithmetic.isCu
sp_iff_isCusp_SL2Z (𝒢 : Subgroup (GL (Fin 2) Real)) [𝒢.IsArithmetic] {c : OnePoi
nt Real} : IsCusp c 𝒢 ↔ IsCusp c 𝒮…
· 使用引理 `isCusp_SL2Z_iff'`：isCusp_SL2Z_iff' {c : OnePoint Real} : IsCusp c 𝒮ℒ ↔ e
xists g : SL(2, Int), c = mapGL Real g • ∞
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma CuspFormClass.zero_at_infty_slash [CuspFormClass F Γ k] :
    IsZeroAtImInfty (f ∣[k] g) := by
  rw [← OnePoint.isZeroAt_infty_iff, SL_slash, ← OnePoint.IsZeroAt.smul_iff]
  apply zero_at_cusps f
  rw [Subgroup.IsArithmetic.isCusp_iff_isCusp_SL2Z, isCusp_SL2Z_iff']
  exact ⟨g, by simp [mapGL]⟩

end SL2Z

