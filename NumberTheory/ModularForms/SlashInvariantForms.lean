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

variable (F : Type*) (Γ : outParam <| Subgroup (GL (Fin 2) ℝ)) (k : outParam ℤ)

/-- Functions `ℍ → ℂ` that are invariant under the `SlashAction`. -/
/-
**SlashInvariantForm** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：outParam (Subgroup (GL (Fin 2) ℝ)) → outParam ℤ → Type
参数：Subgroup (GL (Fin 2) ℝ)。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Functions `ℍ → ℂ` that are invariant under the `SlashAction`.
-/
structure SlashInvariantForm where
  /-- The underlying function `ℍ → ℂ`.

  Do NOT use directly. Use the coercion instead. -/
  toFun : ℍ → ℂ
  slash_action_eq' : ∀ γ ∈ Γ, toFun ∣[k] γ = toFun

/-- `SlashInvariantFormClass F Γ k` asserts `F` is a type of bundled functions that are invariant
under the `SlashAction`. -/
/-
**SlashInvariantFormClass** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：(F : Type u_1) → outParam (Subgroup (GL (Fin 2) ℝ)) → outParam ℤ → [FunLik
e F UpperHalfPlane ℂ] → Prop
参数：GL (Fin 2) ℝ。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`SlashInvariantFormClass F Γ k` asserts `F` is a type of bundled functions that 
are invariant
under the `SlashAction`.
-/
class SlashInvariantFormClass [FunLike F ℍ ℂ] : Prop where
  slash_action_eq : ∀ (f : F), ∀ γ ∈ Γ, (f : ℍ → ℂ) ∣[k] γ = f
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 100) SlashInvariantForm.funLike :
    FunLike (SlashInvariantForm Γ k) ℍ ℂ where
  coe := SlashInvariantForm.toFun
  coe_injective f g h := by cases f; cases g; congr

/-- See note [custom simps projection]. -/
/-
**SlashInvariantForm.Simps.coe** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：SlashInvariantForm.Simps.coe (f : SlashInvariantForm Γ k) : ℍ -> Complex
参数：f : SlashInvariantForm Γ k。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
See note [custom simps projection].
-/
def SlashInvariantForm.Simps.coe (f : SlashInvariantForm Γ k) : ℍ → ℂ := f

initialize_simps_projections SlashInvariantForm (toFun → coe, as_prefix coe)
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 100) SlashInvariantFormClass.slashInvariantForm :
    SlashInvariantFormClass (SlashInvariantForm Γ k) Γ k where
  slash_action_eq := SlashInvariantForm.slash_action_eq'

variable {F Γ k}

@[simp]
/-
**SlashInvariantForm.toFun_eq_coe** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：SlashInvariantForm.toFun_eq_coe {f : SlashInvariantForm Γ k} : f.toFun = (
f : ℍ -> Complex)
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem SlashInvariantForm.toFun_eq_coe {f : SlashInvariantForm Γ k} : f.toFun = (f : ℍ → ℂ) :=
  rfl

@[simp]
/-
**SlashInvariantForm.coe_mk** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：SlashInvariantForm.coe_mk (f : ℍ -> Complex) (hf : forall γ in Γ, f ∣[k] γ
 = f) : ⇑(mk f hf) = f
参数：f : ℍ -> Complex；hf : forall γ in Γ, f ∣[k] γ = f。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem SlashInvariantForm.coe_mk (f : ℍ → ℂ) (hf : ∀ γ ∈ Γ, f ∣[k] γ = f) : ⇑(mk f hf) = f := rfl

@[ext]
/-
**SlashInvariantForm.ext** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：SlashInvariantForm.ext {f g : SlashInvariantForm Γ k} (h : forall x, f x =
 g x) : f = g
参数：h : forall x, f x = g x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DFunLike.ext`：ext (f g : F) (h : forall x : α, f x = g x) : f = g
-/
theorem SlashInvariantForm.ext {f g : SlashInvariantForm Γ k} (h : ∀ x, f x = g x) : f = g :=
  DFunLike.ext f g h

/-- Copy of a `SlashInvariantForm` with a new `toFun` equal to the old one.
Useful to fix definitional equalities. -/
/-
**SlashInvariantForm.copy** 是 Mathlib 中的一个定义，位于命名空间 `SlashInvariantForm`。
形式化陈述：{Γ : outParam (Subgroup (GL (Fin 2) ℝ))} →   {k : outParam ℤ} → (f : Slash
InvariantForm Γ k) → (f' : UpperHalfPlane → ℂ) → f' = ⇑f → SlashInvariantForm Γ 
k
参数：Subgroup (GL (Fin 2) ℝ)；f : SlashInvariantForm Γ k；f' : UpperHalfPlane → ℂ。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Copy of a `SlashInvariantForm` with a new `toFun` equal to the old one.
Useful to fix definitional equalities.
-/
protected def SlashInvariantForm.copy (f : SlashInvariantForm Γ k) (f' : ℍ → ℂ) (h : f' = ⇑f) :
    SlashInvariantForm Γ k where
  toFun := f'
  slash_action_eq' := h.symm ▸ f.slash_action_eq'

end SlashInvariantForms

namespace SlashInvariantForm

variable {F : Type*} {Γ : Subgroup <| GL (Fin 2) ℝ} {k : ℤ} [FunLike F ℍ ℂ]

/-
**SlashInvariantForm.slash_action_eqn** 是 Mathlib 中的一个定理，位于命名空间 `SlashInvariantF
orm`。
形式化陈述：slash_action_eqn [SlashInvariantFormClass F Γ k] (f : F) (γ) (hγ : γ in Γ)
 : ↑f ∣[k] γ = ⇑f
参数：f : F；γ；hγ : γ in Γ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SlashInvariantFormClass.slash_action_eq`：∀ {F : Type u_1} {Γ : outParam 
(Subgroup (GL (Fin 2) ℝ))} {k : outParam ℤ} {inst : FunLike F UpperHalfPlane ℂ} 
  [self : SlashInvariantFormC…
-/
theorem slash_action_eqn [SlashInvariantFormClass F Γ k] (f : F) (γ) (hγ : γ ∈ Γ) :
    ↑f ∣[k] γ = ⇑f :=
  SlashInvariantFormClass.slash_action_eq f γ hγ
/-
**SlashInvariantForm.slash_action_eqn'** 是 Mathlib 中的一个定理，位于命名空间 `SlashInvariant
Form`。
形式化陈述：slash_action_eqn' {k : Int} [Γ.HasDetOne] [SlashInvariantFormClass F Γ k] 
(f : F) {γ} (hγ : γ in Γ) (z : ℍ) : f (γ • z) = (γ 1 0 * z + γ 1 1) ^ k * f z
参数：f : F；hγ : γ in Γ；z : ℍ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `ite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α),
 c = True → (if c then a else b) = a
· 使用定理 `Subgroup.HasDetOne.det_eq`：∀ {n : Type u_1} {inst : Fintype n} {inst_1 :
 DecidableEq n} {R : Type u_2} {inst_2 : CommRing R}   {Γ : Subgroup (GL n R)} [
self : Γ.HasDet…
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `abs_one`：∀ {α : Type u_1} [inst : Ring α] [inst_1 : LinearOrder α] [IsOr
deredRing α], |1| = 1
· 使用定理 `one_zpow`：∀ {α : Type u_1} [inst : DivisionMonoid α] (n : ℤ), 1 ^ n = 1
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `zpow_neg`：∀ {α : Type u_1} [inst : DivisionMonoid α] (a : α) (n : ℤ), a 
^ (-n) = (a ^ n)⁻¹
· 使用引理 `mul_inv_eq_iff_eq_mul₀`：mul_inv_eq_iff_eq_mul₀ (hb : b != 0) : a * b⁻¹ =
 c ↔ a = c * b
· 使用定理 `zpow_ne_zero`：∀ {G₀ : Type u_3} [inst : GroupWithZero G₀] {a : G₀} (n : 
ℤ), a ≠ 0 → a ^ n ≠ 0
· 使用定理 `UpperHalfPlane.denom_ne_zero`：denom_ne_zero (g : GL (Fin 2) Real) (z : ℍ
) : denom g z != 0
· 使用定理 `congr_fun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g 
→ ∀ (a : α), f a = g a
· 使用定理 `SlashInvariantForm.slash_action_eqn`：slash_action_eqn [SlashInvariantFor
mClass F Γ k] (f : F) (γ) (hγ : γ in Γ) : ↑f ∣[k] γ = ⇑f
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `UpperHalfPlane.denom.eq_1`：∀ (g : GL (Fin 2) ℝ) (z : ℂ), UpperHalfPlane.
denom g z = ↑(↑g 1 0) * z + ↑(↑g 1 1)
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
-/
theorem slash_action_eqn' {k : ℤ} [Γ.HasDetOne] [SlashInvariantFormClass F Γ k]
    (f : F) {γ} (hγ : γ ∈ Γ) (z : ℍ) :
    f (γ • z) = (γ 1 0 * z + γ 1 1) ^ k * f z := by
  have : f (γ • z) = f z * denom γ z ^ k := by
    simpa [slash_def, σ, mul_inv_eq_iff_eq_mul₀ (zpow_ne_zero _ (denom_ne_zero _ _)),
      Subgroup.HasDetOne.det_eq hγ] using congr_fun (slash_action_eqn f γ hγ) z
  rw [this, denom, mul_comm]

/-- Every `SlashInvariantForm` `f` satisfies ` f (γ • z) = (denom γ z) ^ k * f z`. -/
/-
**SlashInvariantForm.slash_action_eqn''** 是 Mathlib 中的一个定理，位于命名空间 `SlashInvarian
tForm`。
形式化陈述：slash_action_eqn'' {k : Int} [Γ.HasDetOne] [SlashInvariantFormClass F Γ k]
 (f : F) {γ} (hγ : γ in Γ) (z : ℍ) : f (γ • z) = (denom γ z) ^ k * f z
参数：f : F；hγ : γ in Γ；z : ℍ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SlashInvariantForm.slash_action_eqn'`：slash_action_eqn' {k : Int} [Γ.Has
DetOne] [SlashInvariantFormClass F Γ k] (f : F) {γ} (hγ : γ in Γ) (z : ℍ) : f (γ
 • z) = (γ 1 0 * z + γ 1 1…

--- 原说明 ---
Every `SlashInvariantForm` `f` satisfies ` f (γ • z) = (denom γ z) ^ k * f z`.
-/
theorem slash_action_eqn'' {k : ℤ} [Γ.HasDetOne] [SlashInvariantFormClass F Γ k]
    (f : F) {γ} (hγ : γ ∈ Γ) (z : ℍ) :
    f (γ • z) = (denom γ z) ^ k * f z :=
  SlashInvariantForm.slash_action_eqn' f hγ z

/-- Every `SlashInvariantForm` `f` satisfies ` f (γ • z) = (denom γ z) ^ k * f z`. -/
/-
**SlashInvariantForm.slash_action_eqn_SL''** 是 Mathlib 中的一个定理，位于命名空间 `SlashInvar
iantForm`。
形式化陈述：slash_action_eqn_SL'' {k : Int} {Γ : Subgroup SL(2, Int)} [SlashInvariantF
ormClass F Γ k] (f : F) {γ} (hγ : γ in Γ) (z : ℍ) : f (γ • z) = (denom γ z) ^ k 
* f z
参数：2, Int；f : F；hγ : γ in Γ；z : ℍ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SlashInvariantForm.slash_action_eqn'`：slash_action_eqn' {k : Int} [Γ.Has
DetOne] [SlashInvariantFormClass F Γ k] (f : F) {γ} (hγ : γ in Γ) (z : ℍ) : f (γ
 • z) = (γ 1 0 * z + γ 1 1…
· 使用定理 `Subgroup.instHasDetOneMapSpecialLinearGroupGeneralLinearGroupMapGL`：∀ {n
 : Type u_1} [inst : Fintype n] [inst_1 : DecidableEq n] {R : Type u_2} [inst_2 
: CommRing R] {S : Type u_3}   [inst_3 : CommRing S] [in…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `instFaithfulSMulIntOfCharZero`：∀ (R : Type u_3) [inst : Ring R] [CharZer
o R], FaithfulSMul ℤ R
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α

--- 原说明 ---
Every `SlashInvariantForm` `f` satisfies ` f (γ • z) = (denom γ z) ^ k * f z`.
-/
theorem slash_action_eqn_SL'' {k : ℤ} {Γ : Subgroup SL(2, ℤ)} [SlashInvariantFormClass F Γ k]
    (f : F) {γ} (hγ : γ ∈ Γ) (z : ℍ) :
    f (γ • z) = (denom γ z) ^ k * f z :=
  SlashInvariantForm.slash_action_eqn' f (by simpa using hγ) z
/-
**SlashInvariantForm.** 是 Mathlib 中的一个实例，位于命名空间 `SlashInvariantForm`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [SlashInvariantFormClass F Γ k] : CoeTC F (SlashInvariantForm Γ k) :=
  ⟨fun f ↦ { slash_action_eq' := slash_action_eqn f, .. }⟩
/-
**SlashInvariantForm.instAdd** 是 Mathlib 中的一个实例，位于命名空间 `SlashInvariantForm`。
形式化陈述：instAdd : Add (SlashInvariantForm Γ k)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instAdd : Add (SlashInvariantForm Γ k) :=
  ⟨fun f g ↦
    { toFun := f + g
      slash_action_eq' := fun γ hγ ↦ by
        rw [SlashAction.add_slash, slash_action_eqn f γ hγ, slash_action_eqn g γ hγ] }⟩
/-
**SlashInvariantForm.** 是 Mathlib 中的一个实例，位于命名空间 `SlashInvariantForm`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : IsAddApply (SlashInvariantForm Γ k) ℍ ℂ where
  add_apply _ _ _ := rfl

@[deprecated (since := "2026-07-10")] alias coe_add := FunLike.coe_add

@[deprecated (since := "2026-07-10")] protected alias add_apply := add_apply
/-
**SlashInvariantForm.instZero** 是 Mathlib 中的一个实例，位于命名空间 `SlashInvariantForm`。
形式化陈述：instZero : Zero (SlashInvariantForm Γ k)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instZero : Zero (SlashInvariantForm Γ k) :=
  ⟨{toFun := 0
    slash_action_eq' := fun _ _ ↦ SlashAction.zero_slash _ _}⟩
/-
**SlashInvariantForm.** 是 Mathlib 中的一个实例，位于命名空间 `SlashInvariantForm`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : IsZeroApply (SlashInvariantForm Γ k) ℍ ℂ where
  zero_apply _ := rfl

@[deprecated (since := "2026-07-10")] alias coe_zero := FunLike.coe_zero

section smul

variable [Γ.HasDetOne] {α : Type*} [SMul α ℂ] [IsScalarTower α ℂ ℂ]

/-- Scalar multiplication by `ℂ`, assuming that `Γ ⊆ SL(2, ℝ)`. -/
/-
**SlashInvariantForm.instSMul** 是 Mathlib 中的一个实例，位于命名空间 `SlashInvariantForm`。
形式化陈述：instSMul : SMul α (SlashInvariantForm Γ k) where smul c f
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Scalar multiplication by `ℂ`, assuming that `Γ ⊆ SL(2, ℝ)`.
-/
instance instSMul : SMul α (SlashInvariantForm Γ k) where
  smul c f :=
  { toFun := c • ↑f
    slash_action_eq' γ hγ := by
      rw [← smul_one_smul ℂ]
      simp [-smul_assoc, smul_slash, slash_action_eqn _ _ hγ, σ, Subgroup.HasDetOne.det_eq hγ] }
/-
**SlashInvariantForm.** 是 Mathlib 中的一个实例，位于命名空间 `SlashInvariantForm`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : IsSMulApply α (SlashInvariantForm Γ k) ℍ ℂ where
  smul_apply _ _ _ := rfl

@[deprecated (since := "2026-07-10")] alias coe_smul := FunLike.coe_smul

@[deprecated (since := "2026-07-10")] protected alias smul_apply := smul_apply

end smul

section smulℝ

variable {α : Type*} [SMul α ℂ] [SMul α ℝ] [IsScalarTower α ℝ ℂ]

/-- Scalar multiplication by `ℝ`, valid without restrictions on the determinant. -/
/-
**SlashInvariantForm.instSMul** 是 Mathlib 中的一个实例，位于命名空间 `SlashInvariantForm`。
形式化陈述：instSMul : SMul α (SlashInvariantForm Γ k) where smul c f
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Scalar multiplication by `ℝ`, valid without restrictions on the determinant.
-/
instance instSMulℝ : SMul α (SlashInvariantForm Γ k) where
  smul c f :=
  { toFun := c • ↑f
    slash_action_eq' γ hγ := by
      rw [← smul_one_smul ℝ, ← smul_one_smul ℂ, smul_slash,
        Complex.real_smul, mul_one, σ_ofReal, slash_action_eqn _ _ hγ] }
/-
**SlashInvariantForm.** 是 Mathlib 中的一个实例，位于命名空间 `SlashInvariantForm`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : IsSMulApply α (SlashInvariantForm Γ k) ℍ ℂ where
  smul_apply _ _ _ := rfl

@[deprecated (since := "2026-07-10")] alias coe_smulℝ := FunLike.coe_smul

@[deprecated (since := "2026-07-10")] protected alias smul_applyℝ := smul_apply

end smulℝ

/-
**SlashInvariantForm.instNeg** 是 Mathlib 中的一个实例，位于命名空间 `SlashInvariantForm`。
形式化陈述：instNeg : Neg (SlashInvariantForm Γ k)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instNeg : Neg (SlashInvariantForm Γ k) :=
  ⟨fun f =>
    { toFun := -f
      slash_action_eq' := fun γ hγ => by rw [SlashAction.neg_slash, slash_action_eqn f γ hγ] }⟩
/-
**SlashInvariantForm.** 是 Mathlib 中的一个实例，位于命名空间 `SlashInvariantForm`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : IsNegApply (SlashInvariantForm Γ k) ℍ ℂ where
  neg_apply _ _ := rfl

@[deprecated (since := "2026-07-10")] alias coe_neg := FunLike.coe_neg

@[deprecated (since := "2026-07-10")] protected alias neg_apply := neg_apply
/-
**SlashInvariantForm.instSub** 是 Mathlib 中的一个实例，位于命名空间 `SlashInvariantForm`。
形式化陈述：instSub : Sub (SlashInvariantForm Γ k)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instSub : Sub (SlashInvariantForm Γ k) :=
  ⟨fun f g => f + -g⟩
/-
**SlashInvariantForm.** 是 Mathlib 中的一个实例，位于命名空间 `SlashInvariantForm`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : IsSubApply (SlashInvariantForm Γ k) ℍ ℂ where
  sub_apply _ _ _ := rfl

@[deprecated (since := "2026-07-10")] alias coe_sub := FunLike.coe_sub

@[deprecated (since := "2026-07-10")] protected alias sub_apply := sub_apply
/-
**SlashInvariantForm.** 是 Mathlib 中的一个实例，位于命名空间 `SlashInvariantForm`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : AddCommGroup (SlashInvariantForm Γ k) := fast_instance% FunLike.addCommGroup

@[deprecated (since := "2026-07-10")] alias coeHom := FunLike.coeMonoidHom

@[deprecated (since := "2026-07-10")] alias coeHom_injective := FunLike.coeMonoidHom_injective
/-
**SlashInvariantForm.instModuleComplex** 是 Mathlib 中的一个实例，位于命名空间 `SlashInvariant
Form`。
形式化陈述：instModuleComplex [Γ.HasDetOne] {α : Type*} [Semiring α] [Module α Complex
] [IsScalarTower α Complex Complex] : Module α (SlashInvariantForm Γ k)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `SlashInvariantForm.instIsZeroApplyUpperHalfPlaneComplex`：∀ {Γ : Subgroup
 (GL (Fin 2) ℝ)} {k : ℤ}, IsZeroApply (SlashInvariantForm Γ k) UpperHalfPlane ℂ
· 使用定理 `SlashInvariantForm.instIsAddApplyUpperHalfPlaneComplex`：∀ {Γ : Subgroup 
(GL (Fin 2) ℝ)} {k : ℤ}, IsAddApply (SlashInvariantForm Γ k) UpperHalfPlane ℂ
-/
instance instModuleComplex [Γ.HasDetOne] {α : Type*} [Semiring α] [Module α ℂ]
    [IsScalarTower α ℂ ℂ] : Module α (SlashInvariantForm Γ k) := FunLike.module
/-
**SlashInvariantForm.instModuleReal** 是 Mathlib 中的一个实例，位于命名空间 `SlashInvariantFor
m`。
形式化陈述：instModuleReal {α : Type*} [Semiring α] [Module α Real] [Module α Complex]
 [IsScalarTower α Real Complex] : Module α (SlashInvariantForm Γ k)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `SlashInvariantForm.instIsZeroApplyUpperHalfPlaneComplex`：∀ {Γ : Subgroup
 (GL (Fin 2) ℝ)} {k : ℤ}, IsZeroApply (SlashInvariantForm Γ k) UpperHalfPlane ℂ
· 使用定理 `SlashInvariantForm.instIsAddApplyUpperHalfPlaneComplex`：∀ {Γ : Subgroup 
(GL (Fin 2) ℝ)} {k : ℤ}, IsAddApply (SlashInvariantForm Γ k) UpperHalfPlane ℂ
-/
instance instModuleReal {α : Type*} [Semiring α] [Module α ℝ] [Module α ℂ] [IsScalarTower α ℝ ℂ] :
    Module α (SlashInvariantForm Γ k) := FunLike.module

/-- The `SlashInvariantForm` corresponding to `Function.const _ x`. -/
@[simps -fullyApplied]
/-
**SlashInvariantForm.const** 是 Mathlib 中的一个定义，位于命名空间 `SlashInvariantForm`。
形式化陈述：const [Γ.HasDetOne] (x : Complex) : SlashInvariantForm Γ 0 where toFun
参数：x : Complex。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The `SlashInvariantForm` corresponding to `Function.const _ x`.
-/
def const [Γ.HasDetOne] (x : ℂ) : SlashInvariantForm Γ 0 where
  toFun := Function.const _ x
  slash_action_eq' g hg := by ext; simp [slash_def, σ, Subgroup.HasDetOne.det_eq hg]

/-- The `SlashInvariantForm` corresponding to `Function.const _ x`. -/
@[simps -fullyApplied]
/-
**SlashInvariantForm.const** 是 Mathlib 中的一个定义，位于命名空间 `SlashInvariantForm`。
形式化陈述：const [Γ.HasDetOne] (x : Complex) : SlashInvariantForm Γ 0 where toFun
参数：x : Complex。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The `SlashInvariantForm` corresponding to `Function.const _ x`.
-/
def constℝ [Γ.HasDetPlusMinusOne] (x : ℝ) : SlashInvariantForm Γ 0 where
  toFun := Function.const _ x
  slash_action_eq' g hg := funext fun τ ↦ by simp [slash_apply,
    Subgroup.HasDetPlusMinusOne.abs_det hg, -Matrix.GeneralLinearGroup.val_det_apply]
/-
**SlashInvariantForm.** 是 Mathlib 中的一个实例，位于命名空间 `SlashInvariantForm`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Γ.HasDetPlusMinusOne] : One (SlashInvariantForm Γ 0) where
  one := { constℝ 1 with toFun := 1 }

@[simp]
/-
**SlashInvariantForm.one_coe_eq_one** 是 Mathlib 中的一个定理，位于命名空间 `SlashInvariantFor
m`。
形式化陈述：one_coe_eq_one [Γ.HasDetPlusMinusOne] : ((1 : SlashInvariantForm Γ 0) : ℍ 
-> Complex) = 1
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem one_coe_eq_one [Γ.HasDetPlusMinusOne] : ((1 : SlashInvariantForm Γ 0) : ℍ → ℂ) = 1 :=
  rfl
/-
**SlashInvariantForm.** 是 Mathlib 中的一个实例，位于命名空间 `SlashInvariantForm`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Inhabited (SlashInvariantForm Γ k) :=
  ⟨0⟩

/-- The slash invariant form of weight `k₁ + k₂` given by the product of two slash-invariant forms
of weights `k₁` and `k₂`. -/
/-
**SlashInvariantForm.mul** 是 Mathlib 中的一个定义，位于命名空间 `SlashInvariantForm`。
形式化陈述：mul [Γ.HasDetPlusMinusOne] {k₁ k₂ : Int} (f : SlashInvariantForm Γ k₁) (g 
: SlashInvariantForm Γ k₂) : SlashInvariantForm Γ (k₁ + k₂) where toFun
参数：f : SlashInvariantForm Γ k₁；g : SlashInvariantForm Γ k₂。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The slash invariant form of weight `k₁ + k₂` given by the product of two slash-i
nvariant forms
of weights `k₁` and `k₂`.
-/
def mul [Γ.HasDetPlusMinusOne] {k₁ k₂ : ℤ} (f : SlashInvariantForm Γ k₁)
    (g : SlashInvariantForm Γ k₂) : SlashInvariantForm Γ (k₁ + k₂) where
  toFun := f * g
  slash_action_eq' A hA := by simp [mul_slash, Subgroup.HasDetPlusMinusOne.abs_det hA,
    -Matrix.GeneralLinearGroup.val_det_apply, slash_action_eqn f A hA, slash_action_eqn g A hA]

@[simp]
/-
**SlashInvariantForm.coe_mul** 是 Mathlib 中的一个定理，位于命名空间 `SlashInvariantForm`。
形式化陈述：coe_mul [Γ.HasDetPlusMinusOne] {k₁ k₂ : Int} (f : SlashInvariantForm Γ k₁)
 (g : SlashInvariantForm Γ k₂) : ⇑(f.mul g) = ⇑f * ⇑g
参数：f : SlashInvariantForm Γ k₁；g : SlashInvariantForm Γ k₂。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_mul [Γ.HasDetPlusMinusOne] {k₁ k₂ : ℤ} (f : SlashInvariantForm Γ k₁)
    (g : SlashInvariantForm Γ k₂) : ⇑(f.mul g) = ⇑f * ⇑g :=
  rfl

/-- Given `SlashInvariantForm`'s `f i` of weight `k i` for `i : ι`, define the form which as a
function is a product of those indexed by `s : Finset ι` with weight `m = ∑ i ∈ s, k i`. -/
@[simps -fullyApplied]
/-
**SlashInvariantForm.prod** 是 Mathlib 中的一个定义，位于命名空间 `SlashInvariantForm`。
形式化陈述：prod {ι : Type} {s : Finset ι} {k : ι -> Int} (m : Int) (hm : m = ∑ i in s
, k i) {Γ : Subgroup (GL (Fin 2) Real)} [Γ.HasDetPlusMinusOne] (f : (i : ι) -> S
lashInvariantForm Γ (k i)) : SlashInvariantForm Γ m where toFun
参数：m : Int；hm : m = ∑ i in s, k i；GL (Fin 2) Real；f : (i : ι) -> SlashInvariantF
orm Γ (k i)。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given `SlashInvariantForm`'s `f i` of weight `k i` for `i : ι`, define the form 
which as a
function is a product of those indexed by `s : Finset ι` with weight `m = ∑ i ∈ 
s, k i`.
-/
def prod {ι : Type} {s : Finset ι} {k : ι → ℤ} (m : ℤ)
    (hm : m = ∑ i ∈ s, k i) {Γ : Subgroup (GL (Fin 2) ℝ)} [Γ.HasDetPlusMinusOne]
    (f : (i : ι) → SlashInvariantForm Γ (k i)) : SlashInvariantForm Γ m where
  toFun := ∏ i ∈ s, (f i)
  slash_action_eq' A hA := by
    simp [hm, prod_slash_sum_weights, -Matrix.GeneralLinearGroup.val_det_apply,
       Subgroup.HasDetPlusMinusOne.abs_det hA, SlashInvariantForm.slash_action_eqn (f _) A hA]

/-- Given `SlashInvariantForm`'s `f i` of weight `k`, define the form which as a
function is a product of those indexed by `s : Finset ι` with weight `#s * k`. -/
@[simps! -fullyApplied]
/-
**SlashInvariantForm.prodEqualWeights** 是 Mathlib 中的一个定义，位于命名空间 `SlashInvariantF
orm`。
形式化陈述：prodEqualWeights {ι : Type} {s : Finset ι} {k : Int} {Γ : Subgroup (GL (Fi
n 2) Real)} [Γ.HasDetPlusMinusOne] (f : (i : ι) -> SlashInvariantForm Γ k) : Sla
shInvariantForm Γ (s.card * k)
参数：GL (Fin 2) Real；f : (i : ι) -> SlashInvariantForm Γ k。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given `SlashInvariantForm`'s `f i` of weight `k`, define the form which as a
function is a product of those indexed by `s : Finset ι` with weight `#s * k`.
-/
def prodEqualWeights {ι : Type} {s : Finset ι} {k : ℤ}
    {Γ : Subgroup (GL (Fin 2) ℝ)} [Γ.HasDetPlusMinusOne]
    (f : (i : ι) → SlashInvariantForm Γ k) : SlashInvariantForm Γ (s.card * k) :=
  prod (k := fun i ↦ k) (s := s) (s.card * k) (by simp) f
/-
**SlashInvariantForm.** 是 Mathlib 中的一个实例，位于命名空间 `SlashInvariantForm`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Γ.HasDetPlusMinusOne] : NatCast (SlashInvariantForm Γ 0) where
  natCast n := constℝ n

@[simp, norm_cast]
/-
**SlashInvariantForm.coe_natCast** 是 Mathlib 中的一个定理，位于命名空间 `SlashInvariantForm`。
形式化陈述：coe_natCast [Γ.HasDetPlusMinusOne] (n : Nat) : ⇑(n : SlashInvariantForm Γ 
0) = n
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_natCast [Γ.HasDetPlusMinusOne] (n : ℕ) : ⇑(n : SlashInvariantForm Γ 0) = n := rfl
/-
**SlashInvariantForm.** 是 Mathlib 中的一个实例，位于命名空间 `SlashInvariantForm`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Γ.HasDetPlusMinusOne] : IntCast (SlashInvariantForm Γ 0) where
  intCast z := constℝ z

@[simp, norm_cast]
/-
**SlashInvariantForm.coe_intCast** 是 Mathlib 中的一个定理，位于命名空间 `SlashInvariantForm`。
形式化陈述：coe_intCast [Γ.HasDetPlusMinusOne] (z : Int) : ⇑(z : SlashInvariantForm Γ 
0) = z
参数：z : Int。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_intCast [Γ.HasDetPlusMinusOne] (z : ℤ) : ⇑(z : SlashInvariantForm Γ 0) = z := rfl

open ConjAct Pointwise in
/-- Translating a `SlashInvariantForm` by `g : GL (Fin 2) ℝ`, to obtain a new
`SlashInvariantForm` of level `g⁻¹ Γ g`. -/
/-
**SlashInvariantForm.translate** 是 Mathlib 中的一个定义，位于命名空间 `SlashInvariantForm`。
形式化陈述：translate [SlashInvariantFormClass F Γ k] (f : F) (g : GL (Fin 2) Real) : 
SlashInvariantForm (toConjAct g⁻¹ • Γ) k where toFun
参数：f : F；g : GL (Fin 2) Real。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Translating a `SlashInvariantForm` by `g : GL (Fin 2) ℝ`, to obtain a new
`SlashInvariantForm` of level `g⁻¹ Γ g`.
-/
noncomputable def translate [SlashInvariantFormClass F Γ k] (f : F) (g : GL (Fin 2) ℝ) :
    SlashInvariantForm (toConjAct g⁻¹ • Γ) k where
  toFun := f ∣[k] g
  slash_action_eq' j hj := by
    rw [map_inv, Γ.mem_inv_pointwise_smul_iff, toConjAct_smul] at hj
    simpa [← SlashAction.slash_mul] using congr_arg (· ∣[k] g) (slash_action_eqn f _ hj)

@[simp]
/-
**SlashInvariantForm.coe_translate** 是 Mathlib 中的一个引理，位于命名空间 `SlashInvariantForm
`。
形式化陈述：coe_translate [SlashInvariantFormClass F Γ k] (f : F) (g : GL (Fin 2) Real
) : translate f g = ⇑f ∣[k] g
参数：f : F；g : GL (Fin 2) Real。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma coe_translate [SlashInvariantFormClass F Γ k] (f : F) (g : GL (Fin 2) ℝ) :
    translate f g = ⇑f ∣[k] g :=
  rfl

end SlashInvariantForm

