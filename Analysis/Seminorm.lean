/-
Copyright (c) 2019 Jean Lo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jean Lo, Yaël Dillies, Moritz Doll
-/
module

public import Mathlib.Algebra.Order.AddTorsor
public import Mathlib.Algebra.Order.Pi
public import Mathlib.Analysis.Convex.Function
public import Mathlib.Analysis.LocallyConvex.Basic
public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.Data.Real.Pointwise

/-!
# Seminorms

This file defines seminorms.

A seminorm is a function to the reals which is positive-semidefinite, absolutely homogeneous, and
subadditive. They are closely related to convex sets, and a topological vector space is locally
convex if and only if its topology is induced by a family of seminorms.

## Main declarations

For a module over a normed ring:
* `Seminorm`: A function to the reals that is positive-semidefinite, absolutely homogeneous, and
  subadditive.
* `normSeminorm 𝕜 E`: The norm on `E` as a seminorm.

## References

* [H. H. Schaefer, *Topological Vector Spaces*][schaefer1966]

## Tags

seminorm, locally convex, LCTVS
-/

@[expose] public section

assert_not_exists balancedCore

open NormedField Set Filter

open scoped NNReal Pointwise Topology Uniformity

variable {R R' 𝕜 𝕜₂ 𝕜₃ 𝕝 E E₂ E₃ F ι : Type*}

/-- A seminorm on a module over a normed ring is a function to the reals that is positive
semidefinite, positive homogeneous, and subadditive. -/
/-
**Seminorm** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：(𝕜 : Type u_12) → (E : Type u_13) → [SeminormedRing 𝕜] → [AddGroup E] → [S
Mul 𝕜 E] → Type u_13
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A seminorm on a module over a normed ring is a function to the reals that is pos
itive
semidefinite, positive homogeneous, and subadditive.
-/
structure Seminorm (𝕜 : Type*) (E : Type*) [SeminormedRing 𝕜] [AddGroup E] [SMul 𝕜 E] extends
  AddGroupSeminorm E where
  /-- The seminorm of a scalar multiplication is the product of the absolute value of the scalar
  and the original seminorm. -/
  smul' : ∀ (a : 𝕜) (x : E), toFun (a • x) = ‖a‖ * toFun x

attribute [nolint docBlame] Seminorm.toAddGroupSeminorm

/-- `SeminormClass F 𝕜 E` states that `F` is a type of seminorms on the `𝕜`-module `E`.

You should extend this class when you extend `Seminorm`. -/
/-
**SeminormClass** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：(F : Type u_12) →   (𝕜 : outParam (Type u_13)) →     (E : outParam (Type u
_14)) → [SeminormedRing 𝕜] → [AddGroup E] → [SMul 𝕜 E] → [FunLike F E ℝ] → Prop
参数：Type u_13；Type u_14。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`SeminormClass F 𝕜 E` states that `F` is a type of seminorms on the `𝕜`-module `
E`.

You should extend this class when you extend `Seminorm`.
-/
class SeminormClass (F : Type*) (𝕜 E : outParam Type*) [SeminormedRing 𝕜] [AddGroup E]
  [SMul 𝕜 E] [FunLike F E ℝ] : Prop extends AddGroupSeminormClass F E ℝ where
  /-- The seminorm of a scalar multiplication is the product of the absolute value of the scalar
  and the original seminorm. -/
  map_smul_eq_mul (f : F) (a : 𝕜) (x : E) : f (a • x) = ‖a‖ * f x

export SeminormClass (map_smul_eq_mul)

section Of

/-- Alternative constructor for a `Seminorm` on an `AddCommGroup E` that is a module over a
`SeminormedRing 𝕜`. -/
/-
**Seminorm.of** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：Seminorm.of [SeminormedRing 𝕜] [AddCommGroup E] [Module 𝕜 E] (f : E -> Rea
l) (add_le : forall x y : E, f (x + y) <= f x + f y) (smul : forall (a : 𝕜) (x :
 E), f (a • x) = ‖a‖ * f x) : Seminorm 𝕜 E where toFun
参数：f : E -> Real；add_le : forall x y : E, f (x + y) <= f x + f y；smul : forall (
a : 𝕜) (x : E), f (a • x) = ‖a‖ * f x。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Alternative constructor for a `Seminorm` on an `AddCommGroup E` that is a module
 over a
`SeminormedRing 𝕜`.
-/
def Seminorm.of [SeminormedRing 𝕜] [AddCommGroup E] [Module 𝕜 E] (f : E → ℝ)
    (add_le : ∀ x y : E, f (x + y) ≤ f x + f y) (smul : ∀ (a : 𝕜) (x : E), f (a • x) = ‖a‖ * f x) :
    Seminorm 𝕜 E where
  toFun := f
  map_zero' := by rw [← zero_smul 𝕜 (0 : E), smul, norm_zero, zero_mul]
  add_le' := add_le
  smul' := smul
  neg' x := by rw [← neg_one_smul 𝕜, smul, norm_neg, ← smul, one_smul]

/-- Alternative constructor for a `Seminorm` over a normed field `𝕜` that only assumes `f 0 = 0`
and an inequality for the scalar multiplication. -/
/-
**Seminorm.ofSMulLE** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：Seminorm.ofSMulLE [NormedField 𝕜] [AddCommGroup E] [Module 𝕜 E] (f : E -> 
Real) (map_zero : f 0 = 0) (add_le : forall x y, f (x + y) <= f x + f y) (smul_l
e : forall (r : 𝕜) (x), f (r • x) <= ‖r‖ * f x) : Seminorm 𝕜 E
参数：f : E -> Real；map_zero : f 0 = 0；add_le : forall x y, f (x + y) <= f x + f y；
smul_le : forall (r : 𝕜) (x), f (r • x) <= ‖r‖ * f x。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Alternative constructor for a `Seminorm` over a normed field `𝕜` that only assum
es `f 0 = 0`
and an inequality for the scalar multiplication.
-/
def Seminorm.ofSMulLE [NormedField 𝕜] [AddCommGroup E] [Module 𝕜 E] (f : E → ℝ) (map_zero : f 0 = 0)
    (add_le : ∀ x y, f (x + y) ≤ f x + f y) (smul_le : ∀ (r : 𝕜) (x), f (r • x) ≤ ‖r‖ * f x) :
    Seminorm 𝕜 E :=
  Seminorm.of f add_le fun r x => by
    refine le_antisymm (smul_le r x) ?_
    by_cases h : r = 0
    · simp [h, map_zero]
    rw [← mul_le_mul_iff_right₀ (inv_pos.mpr (norm_pos_iff.mpr h))]
    rw [inv_mul_cancel_left₀ (norm_ne_zero_iff.mpr h)]
    specialize smul_le r⁻¹ (r • x)
    rw [norm_inv] at smul_le
    convert! smul_le
    simp [h]

end Of

namespace Seminorm

section SeminormedRing

variable [SeminormedRing 𝕜]

section AddGroup

variable [AddGroup E]

section SMul

variable [SMul 𝕜 E]

/-
**Seminorm.instFunLike** 是 Mathlib 中的一个实例，位于命名空间 `Seminorm`。
形式化陈述：instFunLike : FunLike (Seminorm 𝕜 E) E Real where coe f
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instFunLike : FunLike (Seminorm 𝕜 E) E ℝ where
  coe f := f.toFun
  coe_injective f g h := by
    rcases f with ⟨⟨_⟩⟩
    rcases g with ⟨⟨_⟩⟩
    congr
/-
**Seminorm.instSeminormClass** 是 Mathlib 中的一个实例，位于命名空间 `Seminorm`。
形式化陈述：instSeminormClass : SeminormClass (Seminorm 𝕜 E) 𝕜 E where map_zero f
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `AddGroupSeminorm.add_le'`：∀ {G : Type u_6} [inst : AddGroup G] (self : A
ddGroupSeminorm G) (r s : G),   self.toFun (r + s) ≤ self.toFun r + self.toFun s
· 使用定理 `AddGroupSeminorm.map_zero'`：∀ {G : Type u_6} [inst : AddGroup G] (self :
 AddGroupSeminorm G), self.toFun 0 = 0
· 使用定理 `AddGroupSeminorm.neg'`：∀ {G : Type u_6} [inst : AddGroup G] (self : AddG
roupSeminorm G) (r : G), self.toFun (-r) = self.toFun r
· 使用定理 `Seminorm.smul'`：∀ {𝕜 : Type u_12} {E : Type u_13} [inst : SeminormedRing
 𝕜] [inst_1 : AddGroup E] [inst_2 : SMul 𝕜 E]   (self : Seminorm 𝕜 E) (a : 𝕜) (x
 : E…
-/
instance instSeminormClass : SeminormClass (Seminorm 𝕜 E) 𝕜 E where
  map_zero f := f.map_zero'
  map_add_le_add f := f.add_le'
  map_neg_eq_map f := f.neg'
  map_smul_eq_mul f := f.smul'

@[ext]
/-
**Seminorm.ext** 是 Mathlib 中的一个定理，位于命名空间 `Seminorm`。
形式化陈述：ext {p q : Seminorm 𝕜 E} (h : forall x, (p : E -> Real) x = q x) : p = q
参数：h : forall x, (p : E -> Real) x = q x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DFunLike.ext`：ext (f g : F) (h : forall x : α, f x = g x) : f = g
-/
theorem ext {p q : Seminorm 𝕜 E} (h : ∀ x, (p : E → ℝ) x = q x) : p = q :=
  DFunLike.ext p q h
/-
**Seminorm.instZero** 是 Mathlib 中的一个实例，位于命名空间 `Seminorm`。
形式化陈述：instZero : Zero (Seminorm 𝕜 E)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instZero : Zero (Seminorm 𝕜 E) :=
  ⟨{ AddGroupSeminorm.instZeroAddGroupSeminorm.zero with
    smul' := fun _ _ => (mul_zero _).symm }⟩
/-
**Seminorm.** 是 Mathlib 中的一个实例，位于命名空间 `Seminorm`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : IsZeroApply (Seminorm 𝕜 E) E ℝ where
  zero_apply _ := rfl

@[deprecated (since := "2026-06-22")] alias coe_zero := FunLike.coe_zero

@[deprecated (since := "2026-06-22")] protected alias zero_apply := zero_apply
/-
**Seminorm.** 是 Mathlib 中的一个实例，位于命名空间 `Seminorm`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Inhabited (Seminorm 𝕜 E) :=
  ⟨0⟩

variable (p : Seminorm 𝕜 E) (x : E) (r : ℝ)

/-- Any action on `ℝ` which factors through `ℝ≥0` applies to a seminorm. -/
/-
**Seminorm.instSMul** 是 Mathlib 中的一个实例，位于命名空间 `Seminorm`。
形式化陈述：instSMul [SMul R Real] [SMul R Real>=0] [IsScalarTower R Real>=0 Real] : S
Mul R (Seminorm 𝕜 E) where smul r p
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `AddGroupSeminorm.map_zero'`：∀ {G : Type u_6} [inst : AddGroup G] (self :
 AddGroupSeminorm G), self.toFun 0 = 0
· 使用定理 `AddGroupSeminorm.add_le'`：∀ {G : Type u_6} [inst : AddGroup G] (self : A
ddGroupSeminorm G) (r s : G),   self.toFun (r + s) ≤ self.toFun r + self.toFun s
· 使用定理 `AddGroupSeminorm.neg'`：∀ {G : Type u_6} [inst : AddGroup G] (self : AddG
roupSeminorm G) (r : G), self.toFun (-r) = self.toFun r

--- 原说明 ---
Any action on `ℝ` which factors through `ℝ≥0` applies to a seminorm.
-/
instance instSMul [SMul R ℝ] [SMul R ℝ≥0] [IsScalarTower R ℝ≥0 ℝ] : SMul R (Seminorm 𝕜 E) where
  smul r p :=
    { r • p.toAddGroupSeminorm with
      toFun := fun x => r • p x
      smul' := fun _ _ => by
        simp only [← smul_one_smul ℝ≥0 r (_ : ℝ), NNReal.smul_def, smul_eq_mul]
        rw [map_smul_eq_mul, mul_left_comm] }
/-
**Seminorm.** 是 Mathlib 中的一个实例，位于命名空间 `Seminorm`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [SMul R ℝ] [SMul R ℝ≥0] [IsScalarTower R ℝ≥0 ℝ] : IsSMulApply R (Seminorm 𝕜 E) E ℝ where
  smul_apply _ _ _ := rfl
/-
**Seminorm.** 是 Mathlib 中的一个实例，位于命名空间 `Seminorm`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [SMul R ℝ] [SMul R ℝ≥0] [IsScalarTower R ℝ≥0 ℝ] [SMul R' ℝ] [SMul R' ℝ≥0]
    [IsScalarTower R' ℝ≥0 ℝ] [SMul R R'] [IsScalarTower R R' ℝ] :
    IsScalarTower R R' (Seminorm 𝕜 E) := FunLike.isScalarTower

@[deprecated (since := "2026-06-22")] alias coe_smul := FunLike.coe_smul

@[deprecated (since := "2026-06-22")] protected alias smul_apply := smul_apply
/-
**Seminorm.instAdd** 是 Mathlib 中的一个实例，位于命名空间 `Seminorm`。
形式化陈述：instAdd : Add (Seminorm 𝕜 E) where add p q
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `AddGroupSeminorm.map_zero'`：∀ {G : Type u_6} [inst : AddGroup G] (self :
 AddGroupSeminorm G), self.toFun 0 = 0
· 使用定理 `AddGroupSeminorm.add_le'`：∀ {G : Type u_6} [inst : AddGroup G] (self : A
ddGroupSeminorm G) (r s : G),   self.toFun (r + s) ≤ self.toFun r + self.toFun s
· 使用定理 `AddGroupSeminorm.neg'`：∀ {G : Type u_6} [inst : AddGroup G] (self : AddG
roupSeminorm G) (r : G), self.toFun (-r) = self.toFun r
-/
instance instAdd : Add (Seminorm 𝕜 E) where
  add p q :=
    { p.toAddGroupSeminorm + q.toAddGroupSeminorm with
      toFun := fun x => p x + q x
      smul' := fun a x => by simp only [map_smul_eq_mul, map_smul_eq_mul, mul_add] }
/-
**Seminorm.** 是 Mathlib 中的一个实例，位于命名空间 `Seminorm`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : IsAddApply (Seminorm 𝕜 E) E ℝ where
  add_apply _ _ _ := rfl

@[deprecated (since := "2026-06-22")] alias coe_add := FunLike.coe_add

@[deprecated (since := "2026-06-22")] protected alias add_apply := add_apply
/-
**Seminorm.instAddMonoid** 是 Mathlib 中的一个实例，位于命名空间 `Seminorm`。
形式化陈述：instAddMonoid : AddMonoid (Seminorm 𝕜 E)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instAddMonoid : AddMonoid (Seminorm 𝕜 E) := fast_instance% FunLike.addMonoid
/-
**Seminorm.instAddCommMonoid** 是 Mathlib 中的一个实例，位于命名空间 `Seminorm`。
形式化陈述：instAddCommMonoid : AddCommMonoid (Seminorm 𝕜 E)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instAddCommMonoid : AddCommMonoid (Seminorm 𝕜 E) := fast_instance% FunLike.addCommMonoid
/-
**Seminorm.instPartialOrder** 是 Mathlib 中的一个实例，位于命名空间 `Seminorm`。
形式化陈述：instPartialOrder : PartialOrder (Seminorm 𝕜 E)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instPartialOrder : PartialOrder (Seminorm 𝕜 E) :=
  PartialOrder.lift _ DFunLike.coe_injective
/-
**Seminorm.instIsOrderedCancelAddMonoid** 是 Mathlib 中的一个实例，位于命名空间 `Seminorm`。
形式化陈述：instIsOrderedCancelAddMonoid : IsOrderedCancelAddMonoid (Seminorm 𝕜 E)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Injective.isOrderedCancelAddMonoid`：∀ {α : Type u} {β : Type u_
1} [inst : AddCommMonoid α] [inst_1 : Preorder α] [IsOrderedCancelAddMonoid α]  
 [inst_3 : AddCommMonoid β] [inst…
· 使用定理 `Pi.isOrderedAddCancelMonoid`：∀ {I : Type u_1} {f : I → Type u_5} [inst :
 (i : I) → AddCommMonoid (f i)] [inst_1 : (i : I) → Preorder (f i)]   [∀ (i : I)
, IsOrderedCancel…
· 使用定理 `FunLike.coe_add`：∀ {F : Type u_3} {α : Type u_5} {β : Type u_6} [inst : 
FunLike F α β] [inst_1 : Add F] [inst_2 : Add β]   [IsAddApply F α β] (f g : F),
 ⇑(f …
· 使用定理 `Seminorm.instIsAddApplyReal`：∀ {𝕜 : Type u_3} {E : Type u_7} [inst : Sem
inormedRing 𝕜] [inst_1 : AddGroup E] [inst_2 : SMul 𝕜 E],   IsAddApply (Seminorm
 𝕜 E) E ℝ
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
instance instIsOrderedCancelAddMonoid : IsOrderedCancelAddMonoid (Seminorm 𝕜 E) :=
  Function.Injective.isOrderedCancelAddMonoid DFunLike.coe FunLike.coe_add .rfl
/-
**Seminorm.instMulAction** 是 Mathlib 中的一个实例，位于命名空间 `Seminorm`。
形式化陈述：instMulAction [Monoid R] [MulAction R Real] [SMul R Real>=0] [IsScalarTowe
r R Real>=0 Real] : MulAction R (Seminorm 𝕜 E)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instMulAction [Monoid R] [MulAction R ℝ] [SMul R ℝ≥0] [IsScalarTower R ℝ≥0 ℝ] :
    MulAction R (Seminorm 𝕜 E) := fast_instance% FunLike.mulAction

variable (𝕜 E)

@[deprecated (since := "2026-06-22")] alias coeFnAddMonoidHom := FunLike.coeAddMonoidHom

@[deprecated (since := "2026-06-22")] alias coeFnAddMonoidHom_apply := FunLike.coeAddMonoidHom_apply

@[deprecated (since := "2026-06-22")] alias coeFnAddMonoidHom_injective :=
  FunLike.coeAddMonoidHom_injective

variable {𝕜 E}
/-
**Seminorm.instDistribMulAction** 是 Mathlib 中的一个实例，位于命名空间 `Seminorm`。
形式化陈述：instDistribMulAction [Monoid R] [DistribMulAction R Real] [SMul R Real>=0]
 [IsScalarTower R Real>=0 Real] : DistribMulAction R (Seminorm 𝕜 E)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instDistribMulAction [Monoid R] [DistribMulAction R ℝ] [SMul R ℝ≥0]
    [IsScalarTower R ℝ≥0 ℝ] : DistribMulAction R (Seminorm 𝕜 E) := fast_instance%
  FunLike.distribMulAction
/-
**Seminorm.instModule** 是 Mathlib 中的一个实例，位于命名空间 `Seminorm`。
形式化陈述：instModule [Semiring R] [Module R Real] [SMul R Real>=0] [IsScalarTower R 
Real>=0 Real] : Module R (Seminorm 𝕜 E)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instModule [Semiring R] [Module R ℝ] [SMul R ℝ≥0] [IsScalarTower R ℝ≥0 ℝ] :
    Module R (Seminorm 𝕜 E) := fast_instance% FunLike.module
/-
**Seminorm.instSup** 是 Mathlib 中的一个实例，位于命名空间 `Seminorm`。
形式化陈述：instSup : Max (Seminorm 𝕜 E) where max p q
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `AddGroupSeminorm.map_zero'`：∀ {G : Type u_6} [inst : AddGroup G] (self :
 AddGroupSeminorm G), self.toFun 0 = 0
· 使用定理 `AddGroupSeminorm.add_le'`：∀ {G : Type u_6} [inst : AddGroup G] (self : A
ddGroupSeminorm G) (r s : G),   self.toFun (r + s) ≤ self.toFun r + self.toFun s
· 使用定理 `AddGroupSeminorm.neg'`：∀ {G : Type u_6} [inst : AddGroup G] (self : AddG
roupSeminorm G) (r : G), self.toFun (-r) = self.toFun r
-/
instance instSup : Max (Seminorm 𝕜 E) where
  max p q :=
    { p.toAddGroupSeminorm ⊔ q.toAddGroupSeminorm with
      toFun := p ⊔ q
      smul' := fun x v =>
        (congr_arg₂ max (map_smul_eq_mul p x v) (map_smul_eq_mul q x v)).trans <|
          (mul_max_of_nonneg _ _ <| norm_nonneg x).symm }

@[simp]
/-
**Seminorm.coe_sup** 是 Mathlib 中的一个定理，位于命名空间 `Seminorm`。
形式化陈述：coe_sup (p q : Seminorm 𝕜 E) : ⇑(p ⊔ q) = (p : E -> Real) ⊔ (q : E -> Real
)
参数：p q : Seminorm 𝕜 E。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_sup (p q : Seminorm 𝕜 E) : ⇑(p ⊔ q) = (p : E → ℝ) ⊔ (q : E → ℝ) :=
  rfl
/-
**Seminorm.sup_apply** 是 Mathlib 中的一个定理，位于命名空间 `Seminorm`。
形式化陈述：sup_apply (p q : Seminorm 𝕜 E) (x : E) : (p ⊔ q) x = p x ⊔ q x
参数：p q : Seminorm 𝕜 E；x : E。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem sup_apply (p q : Seminorm 𝕜 E) (x : E) : (p ⊔ q) x = p x ⊔ q x :=
  rfl
/-
**Seminorm.smul_sup** 是 Mathlib 中的一个定理，位于命名空间 `Seminorm`。
形式化陈述：smul_sup [SMul R Real] [SMul R Real>=0] [IsScalarTower R Real>=0 Real] (r 
: R) (p q : Seminorm 𝕜 E) : r • (p ⊔ q) = r • p ⊔ r • q
参数：r : R；p q : Seminorm 𝕜 E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `smul_one_smul`：smul_one_smul {M} (N) [Monoid N] [SMul M N] [MulAction N 
α] [SMul M α] [IsScalarTower M N α] (x : M) (y : α) : (x • (1 : N)) • y = x • y
· 使用定理 `mul_max_of_nonneg`：mul_max_of_nonneg [PosMulMono R] (b c : R) (ha : 0 <=
 a) : a * max b c = max (a * b) (a * c)
· 使用定理 `IsOrderedRing.toPosMulMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], PosMulMono R
· 使用定理 `NNReal.coe_nonneg`：∀ (r : NNReal), 0 ≤ ↑r
· 使用定理 `Seminorm.ext`：ext {p q : Seminorm 𝕜 E} (h : forall x, (p : E -> Real) x 
= q x) : p = q
-/
theorem smul_sup [SMul R ℝ] [SMul R ℝ≥0] [IsScalarTower R ℝ≥0 ℝ] (r : R) (p q : Seminorm 𝕜 E) :
    r • (p ⊔ q) = r • p ⊔ r • q :=
  have real.smul_max : ∀ x y : ℝ, r • max x y = max (r • x) (r • y) := fun x y => by
    simpa only [← smul_eq_mul, ← NNReal.smul_def, smul_one_smul ℝ≥0 r (_ : ℝ)] using
      mul_max_of_nonneg x y (r • (1 : ℝ≥0) : ℝ≥0).coe_nonneg
  ext fun _ => real.smul_max _ _

@[simp, norm_cast]
/-
**Seminorm.coe_le_coe** 是 Mathlib 中的一个定理，位于命名空间 `Seminorm`。
形式化陈述：coe_le_coe {p q : Seminorm 𝕜 E} : (p : E -> Real) <= q ↔ p <= q
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem coe_le_coe {p q : Seminorm 𝕜 E} : (p : E → ℝ) ≤ q ↔ p ≤ q :=
  Iff.rfl

@[simp, norm_cast]
/-
**Seminorm.coe_lt_coe** 是 Mathlib 中的一个定理，位于命名空间 `Seminorm`。
形式化陈述：coe_lt_coe {p q : Seminorm 𝕜 E} : (p : E -> Real) < q ↔ p < q
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem coe_lt_coe {p q : Seminorm 𝕜 E} : (p : E → ℝ) < q ↔ p < q :=
  Iff.rfl
/-
**Seminorm.le_def** 是 Mathlib 中的一个定理，位于命名空间 `Seminorm`。
形式化陈述：le_def {p q : Seminorm 𝕜 E} : p <= q ↔ forall x, p x <= q x
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem le_def {p q : Seminorm 𝕜 E} : p ≤ q ↔ ∀ x, p x ≤ q x :=
  Iff.rfl
/-
**Seminorm.lt_def** 是 Mathlib 中的一个定理，位于命名空间 `Seminorm`。
形式化陈述：lt_def {p q : Seminorm 𝕜 E} : p < q ↔ p <= q ∧ exists x, p x < q x
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Pi.lt_def`：Pi.lt_def [forall i, Preorder (π i)] {x y : forall i, π i} : 
x < y ↔ x <= y ∧ exists i, x i < y i
-/
theorem lt_def {p q : Seminorm 𝕜 E} : p < q ↔ p ≤ q ∧ ∃ x, p x < q x :=
  @Pi.lt_def _ _ _ p q
/-
**Seminorm.instSemilatticeSup** 是 Mathlib 中的一个实例，位于命名空间 `Seminorm`。
形式化陈述：instSemilatticeSup : SemilatticeSup (Seminorm 𝕜 E)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Seminorm.coe_sup`：coe_sup (p q : Seminorm 𝕜 E) : ⇑(p ⊔ q) = (p : E -> Re
al) ⊔ (q : E -> Real)
-/
instance instSemilatticeSup : SemilatticeSup (Seminorm 𝕜 E) :=
  DFunLike.coe_injective.semilatticeSup _ .rfl .rfl coe_sup
/-
**Seminorm.** 是 Mathlib 中的一个实例，位于命名空间 `Seminorm`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [SMul R ℝ] [SMul R ℝ≥0] [IsScalarTower R ℝ≥0 ℝ] [Preorder R] [Zero R]
    [IsOrderedModule R ℝ] : IsOrderedSMul R (Seminorm 𝕜 E) where
  smul_le_smul_left p q hpq c x := calc
    _ ≤ (c • (1 : ℝ≥0)) • p x := by simp
    _ ≤ _ := by grw [hpq x]; simp
  smul_le_smul_right a b hab p x := by
    grw [smul_apply, hab, smul_apply]

end SMul

end AddGroup

section Module

variable [SeminormedRing 𝕜₂] [SeminormedRing 𝕜₃]
variable {σ₁₂ : 𝕜 →+* 𝕜₂} [RingHomIsometric σ₁₂]
variable {σ₂₃ : 𝕜₂ →+* 𝕜₃} [RingHomIsometric σ₂₃]
variable {σ₁₃ : 𝕜 →+* 𝕜₃} [RingHomIsometric σ₁₃]
variable [AddCommGroup E] [AddCommGroup E₂] [AddCommGroup E₃]
variable [Module 𝕜 E] [Module 𝕜₂ E₂] [Module 𝕜₃ E₃]
variable [SMul R ℝ] [SMul R ℝ≥0] [IsScalarTower R ℝ≥0 ℝ]

/-- Composition of a seminorm with a linear map is a seminorm. -/
/-
**Seminorm.comp** 是 Mathlib 中的一个定义，位于命名空间 `Seminorm`。
形式化陈述：comp (p : Seminorm 𝕜₂ E₂) (f : E ->ₛₗ[σ₁₂] E₂) : Seminorm 𝕜 E
参数：p : Seminorm 𝕜₂ E₂；f : E ->ₛₗ[σ₁₂] E₂。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Composition of a seminorm with a linear map is a seminorm.
-/
def comp (p : Seminorm 𝕜₂ E₂) (f : E →ₛₗ[σ₁₂] E₂) : Seminorm 𝕜 E :=
  { p.toAddGroupSeminorm.comp f.toAddMonoidHom with
    toFun := fun x => p (f x)
    -- Note: https://github.com/leanprover-community/mathlib4/pull/8386 had to change `map_smulₛₗ` to `map_smulₛₗ _`
    smul' _ _ := by simp only [map_smulₛₗ _, map_smul_eq_mul, RingHomIsometric.norm_map] }
/-
**Seminorm.coe_comp** 是 Mathlib 中的一个定理，位于命名空间 `Seminorm`。
形式化陈述：coe_comp (p : Seminorm 𝕜₂ E₂) (f : E ->ₛₗ[σ₁₂] E₂) : ⇑(p.comp f) = p ∘ f
参数：p : Seminorm 𝕜₂ E₂；f : E ->ₛₗ[σ₁₂] E₂。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_comp (p : Seminorm 𝕜₂ E₂) (f : E →ₛₗ[σ₁₂] E₂) : ⇑(p.comp f) = p ∘ f :=
  rfl

@[simp]
/-
**Seminorm.comp_apply** 是 Mathlib 中的一个定理，位于命名空间 `Seminorm`。
形式化陈述：comp_apply (p : Seminorm 𝕜₂ E₂) (f : E ->ₛₗ[σ₁₂] E₂) (x : E) : (p.comp f) 
x = p (f x)
参数：p : Seminorm 𝕜₂ E₂；f : E ->ₛₗ[σ₁₂] E₂；x : E。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem comp_apply (p : Seminorm 𝕜₂ E₂) (f : E →ₛₗ[σ₁₂] E₂) (x : E) : (p.comp f) x = p (f x) :=
  rfl

@[simp]
/-
**Seminorm.comp_id** 是 Mathlib 中的一个定理，位于命名空间 `Seminorm`。
形式化陈述：comp_id (p : Seminorm 𝕜 E) : p.comp LinearMap.id = p
参数：p : Seminorm 𝕜 E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Seminorm.ext`：ext {p q : Seminorm 𝕜 E} (h : forall x, (p : E -> Real) x 
= q x) : p = q
-/
theorem comp_id (p : Seminorm 𝕜 E) : p.comp LinearMap.id = p :=
  ext fun _ => rfl

@[simp]
/-
**Seminorm.comp_zero** 是 Mathlib 中的一个定理，位于命名空间 `Seminorm`。
形式化陈述：comp_zero (p : Seminorm 𝕜₂ E₂) : p.comp (0 : E ->ₛₗ[σ₁₂] E₂) = 0
参数：p : Seminorm 𝕜₂ E₂。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Seminorm.ext`：ext {p q : Seminorm 𝕜 E} (h : forall x, (p : E -> Real) x 
= q x) : p = q
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `AddGroupSeminormClass.toZeroHomClass`：∀ {F : Type u_2} {α : Type u_3} {β
 : Type u_4} [inst : FunLike F α β] [inst_1 : AddGroup α] [inst_2 : AddCommMonoi
d β]   [inst_3 : PartialOr…
· 使用定理 `SeminormClass.toAddGroupSeminormClass`：∀ {F : Type u_12} {𝕜 : outParam (
Type u_13)} {E : outParam (Type u_14)} {inst : SeminormedRing 𝕜} {inst_1 : AddGr
oup E}   {inst_2 : SMul 𝕜 E…
-/
theorem comp_zero (p : Seminorm 𝕜₂ E₂) : p.comp (0 : E →ₛₗ[σ₁₂] E₂) = 0 :=
  ext fun _ => map_zero p

@[simp]
/-
**Seminorm.zero_comp** 是 Mathlib 中的一个定理，位于命名空间 `Seminorm`。
形式化陈述：zero_comp (f : E ->ₛₗ[σ₁₂] E₂) : (0 : Seminorm 𝕜₂ E₂).comp f = 0
参数：f : E ->ₛₗ[σ₁₂] E₂。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Seminorm.ext`：ext {p q : Seminorm 𝕜 E} (h : forall x, (p : E -> Real) x 
= q x) : p = q
-/
theorem zero_comp (f : E →ₛₗ[σ₁₂] E₂) : (0 : Seminorm 𝕜₂ E₂).comp f = 0 :=
  ext fun _ => rfl
/-
**Seminorm.comp_comp** 是 Mathlib 中的一个定理，位于命名空间 `Seminorm`。
形式化陈述：comp_comp [RingHomCompTriple σ₁₂ σ₂₃ σ₁₃] (p : Seminorm 𝕜₃ E₃) (g : E₂ ->ₛ
ₗ[σ₂₃] E₃) (f : E ->ₛₗ[σ₁₂] E₂) : p.comp (g.comp f) = (p.comp g).comp f
参数：p : Seminorm 𝕜₃ E₃；g : E₂ ->ₛₗ[σ₂₃] E₃；f : E ->ₛₗ[σ₁₂] E₂。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Seminorm.ext`：ext {p q : Seminorm 𝕜 E} (h : forall x, (p : E -> Real) x 
= q x) : p = q
-/
theorem comp_comp [RingHomCompTriple σ₁₂ σ₂₃ σ₁₃] (p : Seminorm 𝕜₃ E₃) (g : E₂ →ₛₗ[σ₂₃] E₃)
    (f : E →ₛₗ[σ₁₂] E₂) : p.comp (g.comp f) = (p.comp g).comp f :=
  ext fun _ => rfl
/-
**Seminorm.add_comp** 是 Mathlib 中的一个定理，位于命名空间 `Seminorm`。
形式化陈述：add_comp (p q : Seminorm 𝕜₂ E₂) (f : E ->ₛₗ[σ₁₂] E₂) : (p + q).comp f = p.
comp f + q.comp f
参数：p q : Seminorm 𝕜₂ E₂；f : E ->ₛₗ[σ₁₂] E₂。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Seminorm.ext`：ext {p q : Seminorm 𝕜 E} (h : forall x, (p : E -> Real) x 
= q x) : p = q
-/
theorem add_comp (p q : Seminorm 𝕜₂ E₂) (f : E →ₛₗ[σ₁₂] E₂) :
    (p + q).comp f = p.comp f + q.comp f :=
  ext fun _ => rfl
/-
**Seminorm.comp_add_le** 是 Mathlib 中的一个定理，位于命名空间 `Seminorm`。
形式化陈述：comp_add_le (p : Seminorm 𝕜₂ E₂) (f g : E ->ₛₗ[σ₁₂] E₂) : p.comp (f + g) <
= p.comp f + p.comp g
参数：p : Seminorm 𝕜₂ E₂；f g : E ->ₛₗ[σ₁₂] E₂。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SubadditiveHomClass.map_add_le_add`：∀ {F : Type u_7} {α : outParam (Type
 u_8)} {β : outParam (Type u_9)} {inst : Add α} {inst_1 : Add β} {inst_2 : LE β}
   {inst_3 : FunLike F α…
· 使用定理 `AddGroupSeminormClass.toSubadditiveHomClass`：∀ {F : Type u_7} {α : outPa
ram (Type u_8)} {β : outParam (Type u_9)} {inst : AddGroup α} {inst_1 : AddCommM
onoid β}   {inst_2 : PartialOrder…
· 使用定理 `SeminormClass.toAddGroupSeminormClass`：∀ {F : Type u_12} {𝕜 : outParam (
Type u_13)} {E : outParam (Type u_14)} {inst : SeminormedRing 𝕜} {inst_1 : AddGr
oup E}   {inst_2 : SMul 𝕜 E…
-/
theorem comp_add_le (p : Seminorm 𝕜₂ E₂) (f g : E →ₛₗ[σ₁₂] E₂) :
    p.comp (f + g) ≤ p.comp f + p.comp g := fun _ => map_add_le_add p _ _
/-
**Seminorm.smul_comp** 是 Mathlib 中的一个定理，位于命名空间 `Seminorm`。
形式化陈述：smul_comp (p : Seminorm 𝕜₂ E₂) (f : E ->ₛₗ[σ₁₂] E₂) (c : R) : (c • p).comp
 f = c • p.comp f
参数：p : Seminorm 𝕜₂ E₂；f : E ->ₛₗ[σ₁₂] E₂；c : R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Seminorm.ext`：ext {p q : Seminorm 𝕜 E} (h : forall x, (p : E -> Real) x 
= q x) : p = q
-/
theorem smul_comp (p : Seminorm 𝕜₂ E₂) (f : E →ₛₗ[σ₁₂] E₂) (c : R) :
    (c • p).comp f = c • p.comp f :=
  ext fun _ => rfl
/-
**Seminorm.comp_mono** 是 Mathlib 中的一个定理，位于命名空间 `Seminorm`。
形式化陈述：comp_mono {p q : Seminorm 𝕜₂ E₂} (f : E ->ₛₗ[σ₁₂] E₂) (hp : p <= q) : p.co
mp f <= q.comp f
参数：f : E ->ₛₗ[σ₁₂] E₂；hp : p <= q。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem comp_mono {p q : Seminorm 𝕜₂ E₂} (f : E →ₛₗ[σ₁₂] E₂) (hp : p ≤ q) : p.comp f ≤ q.comp f :=
  fun _ => hp _

/-- The composition as an `AddMonoidHom`. -/
@[simps]
/-
**Seminorm.pullback** 是 Mathlib 中的一个定义，位于命名空间 `Seminorm`。
形式化陈述：pullback (f : E ->ₛₗ[σ₁₂] E₂) : Seminorm 𝕜₂ E₂ ->+ Seminorm 𝕜 E where toFu
n
参数：f : E ->ₛₗ[σ₁₂] E₂。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Seminorm.zero_comp`：zero_comp (f : E ->ₛₗ[σ₁₂] E₂) : (0 : Seminorm 𝕜₂ E₂
).comp f = 0
· 使用定理 `Seminorm.add_comp`：add_comp (p q : Seminorm 𝕜₂ E₂) (f : E ->ₛₗ[σ₁₂] E₂) 
: (p + q).comp f = p.comp f + q.comp f

--- 原说明 ---
The composition as an `AddMonoidHom`.
-/
def pullback (f : E →ₛₗ[σ₁₂] E₂) : Seminorm 𝕜₂ E₂ →+ Seminorm 𝕜 E where
  toFun := fun p => p.comp f
  map_zero' := zero_comp f
  map_add' := fun p q => add_comp p q f
/-
**Seminorm.instOrderBot** 是 Mathlib 中的一个实例，位于命名空间 `Seminorm`。
形式化陈述：instOrderBot : OrderBot (Seminorm 𝕜 E) where bot
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instOrderBot : OrderBot (Seminorm 𝕜 E) where
  bot := 0
  bot_le := apply_nonneg

@[simp]
/-
**Seminorm.coe_bot** 是 Mathlib 中的一个定理，位于命名空间 `Seminorm`。
形式化陈述：coe_bot : ⇑(⊥ : Seminorm 𝕜 E) = 0
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_bot : ⇑(⊥ : Seminorm 𝕜 E) = 0 :=
  rfl
/-
**Seminorm.bot_eq_zero** 是 Mathlib 中的一个定理，位于命名空间 `Seminorm`。
形式化陈述：bot_eq_zero : (⊥ : Seminorm 𝕜 E) = 0
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem bot_eq_zero : (⊥ : Seminorm 𝕜 E) = 0 :=
  rfl

@[deprecated IsOrderedSMul.smul_le_smul (since := "2026-07-31")]
/-
**Seminorm.smul_le_smul** 是 Mathlib 中的一个定理，位于命名空间 `Seminorm`。
形式化陈述：∀ {𝕜 : Type u_3} {E : Type u_7} [inst : SeminormedRing 𝕜] [inst_1 : AddCom
mGroup E] [inst_2 : _root_.Module 𝕜 E]   {p q : Seminorm 𝕜 E} {a b : NNReal}, p 
≤ q → a ≤ b → a • p ≤ b • q
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `mul_le_mul`：∀ {α : Type u_1} [inst : Mul α] [inst_1 : Zero α] [inst_2 : 
Preorder α] {a b c d : α} [PosMulMono α] [MulPosMono α],   a ≤ b → c ≤ d → 0 ≤ c
…
· 使用定理 `IsOrderedRing.toPosMulMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], PosMulMono R
· 使用定理 `IsOrderedRing.toMulPosMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], MulPosMono R
· 使用定理 `NonnegHomClass.apply_nonneg`：∀ {F : Type u_7} {α : outParam (Type u_8)} 
{β : outParam (Type u_9)} {inst : Zero β} {inst_1 : LE β}   {inst_2 : FunLike F 
α β} [self : Nonn…
· 使用定理 `AddGroupSeminormClass.toNonnegHomClass`：∀ {F : Type u_2} {α : Type u_3} 
{β : Type u_4} [inst : FunLike F α β] [inst_1 : AddGroup α] [inst_2 : AddCommMon
oid β]   [inst_3 : LinearOrd…
· 使用定理 `SeminormClass.toAddGroupSeminormClass`：∀ {F : Type u_12} {𝕜 : outParam (
Type u_13)} {E : outParam (Type u_14)} {inst : SeminormedRing 𝕜} {inst_1 : AddGr
oup E}   {inst_2 : SMul 𝕜 E…
· 使用定理 `NNReal.coe_nonneg`：∀ (r : NNReal), 0 ≤ ↑r
-/
protected theorem smul_le_smul {p q : Seminorm 𝕜 E} {a b : ℝ≥0} (hpq : p ≤ q) (hab : a ≤ b) :
    a • p ≤ b • q := by
  simp_rw [le_def]
  intro x
  exact mul_le_mul hab (hpq x) (apply_nonneg p x) (NNReal.coe_nonneg b)
/-
**Seminorm.finset_sup_apply** 是 Mathlib 中的一个定理，位于命名空间 `Seminorm`。
形式化陈述：finset_sup_apply (p : ι -> Seminorm 𝕜 E) (s : Finset ι) (x : E) : s.sup p 
x = ↑(s.sup fun i => NNReal.mk (p i x) (apply_nonneg (p i) x))
参数：p : ι -> Seminorm 𝕜 E；s : Finset ι；x : E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.cons_induction_on`：cons_induction_on {α : Type*} {motive : Finset
 α -> Prop} (s : Finset α) (empty : motive ∅) (cons : forall (a : α) (s : Finset
 α) (h : a ∉ s…
· 使用定理 `NonnegHomClass.apply_nonneg`：∀ {F : Type u_7} {α : outParam (Type u_8)} 
{β : outParam (Type u_9)} {inst : Zero β} {inst_1 : LE β}   {inst_2 : FunLike F 
α β} [self : Nonn…
· 使用定理 `AddGroupSeminormClass.toNonnegHomClass`：∀ {F : Type u_2} {α : Type u_3} 
{β : Type u_4} [inst : FunLike F α β] [inst_1 : AddGroup α] [inst_2 : AddCommMon
oid β]   [inst_3 : LinearOrd…
· 使用定理 `SeminormClass.toAddGroupSeminormClass`：∀ {F : Type u_12} {𝕜 : outParam (
Type u_13)} {E : outParam (Type u_14)} {inst : SeminormedRing 𝕜} {inst_1 : AddGr
oup E}   {inst_2 : SMul 𝕜 E…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.sup_empty`：sup_empty : (∅ : Finset β).sup f = ⊥
· 使用定理 `Seminorm.coe_bot`：coe_bot : ⇑(⊥ : Seminorm 𝕜 E) = 0
· 使用定理 `bot_eq_zero`：∀ {α : Type u_1} [inst : PartialOrder α] [inst_1 : Zero α] 
[IsBotZeroClass α] [inst_3 : OrderBot α], ⊥ = 0
· 使用定理 `LinearOrderedCommMonoidWithZero.toIsBotZeroClass`：∀ {α : Type u_3} [self
 : LinearOrderedCommMonoidWithZero α], IsBotZeroClass α
· 使用定理 `Pi.zero_apply`：∀ {ι : Type u_1} {M : ι → Type u_5} [inst : (i : ι) → Zer
o (M i)] (i : ι), 0 i = 0
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.cast_zero`：cast_zero : ((0 : Nat) : R) = 0
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `of_decide_eq_true`：∀ {p : Prop} [inst : Decidable p], decide p = true → 
p
· 使用定理 `Finset.sup_cons`：sup_cons {b : β} (h : b ∉ s) : (cons b s h).sup f = f b
 ⊔ s.sup f
· 使用定理 `Seminorm.coe_sup`：coe_sup (p q : Seminorm 𝕜 E) : ⇑(p ⊔ q) = (p : E -> Re
al) ⊔ (q : E -> Real)
· 使用定理 `Pi.sup_apply`：sup_apply [forall i, Max (α' i)] (f g : forall i, α' i) (i
 : ι) : (f ⊔ g) i = f i ⊔ g i
· 使用定理 `NNReal.coe_max`：coe_max (x y : Real>=0) : ((max x y : Real>=0) : Real) =
 max (x : Real) (y : Real)
· 使用定理 `NNReal.coe_mk`：∀ (a : ℝ) (ha : 0 ≤ a), ↑(NNReal.mk a ha) = a
-/
theorem finset_sup_apply (p : ι → Seminorm 𝕜 E) (s : Finset ι) (x : E) :
    s.sup p x = ↑(s.sup fun i => NNReal.mk (p i x) (apply_nonneg (p i) x)) := by
  induction s using Finset.cons_induction_on with
  | empty =>
    rw [Finset.sup_empty, Finset.sup_empty, coe_bot, _root_.bot_eq_zero, Pi.zero_apply]
    norm_cast
  | cons a s ha ih =>
    rw [Finset.sup_cons, Finset.sup_cons, coe_sup, Pi.sup_apply, NNReal.coe_max, NNReal.coe_mk, ih]
/-
**Seminorm.exists_apply_eq_finset_sup** 是 Mathlib 中的一个定理，位于命名空间 `Seminorm`。
形式化陈述：exists_apply_eq_finset_sup (p : ι -> Seminorm 𝕜 E) {s : Finset ι} (hs : s.
Nonempty) (x : E) : exists i in s, s.sup p x = p i x
参数：p : ι -> Seminorm 𝕜 E；hs : s.Nonempty；x : E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `NonnegHomClass.apply_nonneg`：∀ {F : Type u_7} {α : outParam (Type u_8)} 
{β : outParam (Type u_9)} {inst : Zero β} {inst_1 : LE β}   {inst_2 : FunLike F 
α β} [self : Nonn…
· 使用定理 `AddGroupSeminormClass.toNonnegHomClass`：∀ {F : Type u_2} {α : Type u_3} 
{β : Type u_4} [inst : FunLike F α β] [inst_1 : AddGroup α] [inst_2 : AddCommMon
oid β]   [inst_3 : LinearOrd…
· 使用定理 `SeminormClass.toAddGroupSeminormClass`：∀ {F : Type u_12} {𝕜 : outParam (
Type u_13)} {E : outParam (Type u_14)} {inst : SeminormedRing 𝕜} {inst_1 : AddGr
oup E}   {inst_2 : SMul 𝕜 E…
· 使用定理 `Finset.exists_mem_eq_sup`：exists_mem_eq_sup [OrderBot α] (s : Finset ι) 
(h : s.Nonempty) (f : ι -> α) : exists i, i in s ∧ s.sup f = f i
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Seminorm.finset_sup_apply`：finset_sup_apply (p : ι -> Seminorm 𝕜 E) (s :
 Finset ι) (x : E) : s.sup p x = ↑(s.sup fun i => NNReal.mk (p i x) (apply_nonne
g (p i) x))
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
-/
theorem exists_apply_eq_finset_sup (p : ι → Seminorm 𝕜 E) {s : Finset ι} (hs : s.Nonempty) (x : E) :
    ∃ i ∈ s, s.sup p x = p i x := by
  rcases Finset.exists_mem_eq_sup s hs (fun i ↦ (⟨p i x, apply_nonneg _ _⟩ : ℝ≥0)) with ⟨i, hi, hix⟩
  rw [finset_sup_apply]
  exact ⟨i, hi, congr_arg _ hix⟩
/-
**Seminorm.zero_or_exists_apply_eq_finset_sup** 是 Mathlib 中的一个定理，位于命名空间 `Seminor
m`。
形式化陈述：zero_or_exists_apply_eq_finset_sup (p : ι -> Seminorm 𝕜 E) (s : Finset ι) 
(x : E) : s.sup p x = 0 ∨ exists i in s, s.sup p x = p i x
参数：p : ι -> Seminorm 𝕜 E；s : Finset ι；x : E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.eq_empty_or_nonempty`：eq_empty_or_nonempty (s : Finset α) : s = ∅
 ∨ s.Nonempty
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Seminorm.exists_apply_eq_finset_sup`：exists_apply_eq_finset_sup (p : ι -
> Seminorm 𝕜 E) {s : Finset ι} (hs : s.Nonempty) (x : E) : exists i in s, s.sup 
p x = p i x
-/
theorem zero_or_exists_apply_eq_finset_sup (p : ι → Seminorm 𝕜 E) (s : Finset ι) (x : E) :
    s.sup p x = 0 ∨ ∃ i ∈ s, s.sup p x = p i x := by
  rcases Finset.eq_empty_or_nonempty s with (rfl | hs)
  · left; rfl
  · right; exact exists_apply_eq_finset_sup p hs x
/-
**Seminorm.finset_sup_smul** 是 Mathlib 中的一个定理，位于命名空间 `Seminorm`。
形式化陈述：finset_sup_smul (p : ι -> Seminorm 𝕜 E) (s : Finset ι) (C : Real>=0) : s.s
up (C • p) = C • s.sup p
参数：p : ι -> Seminorm 𝕜 E；s : Finset ι；C : Real>=0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Seminorm.ext`：ext {p q : Seminorm 𝕜 E} (h : forall x, (p : E -> Real) x 
= q x) : p = q
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `smul_apply`：∀ {M : Type u_1} {F : Type u_2} {α : outParam (Type u_3)} {β
 : outParam (Type u_4)} {inst : FunLike F α β}   {inst_1 : SMul M β} {inst_2 : S
…
· 使用定理 `Seminorm.instIsSMulApplyReal`：∀ {R : Type u_1} {𝕜 : Type u_3} {E : Type 
u_7} [inst : SeminormedRing 𝕜] [inst_1 : AddGroup E] [inst_2 : SMul 𝕜 E]   [inst
_3 : SMul R ℝ] [in…
· 使用定理 `NonnegHomClass.apply_nonneg`：∀ {F : Type u_7} {α : outParam (Type u_8)} 
{β : outParam (Type u_9)} {inst : Zero β} {inst_1 : LE β}   {inst_2 : FunLike F 
α β} [self : Nonn…
· 使用定理 `AddGroupSeminormClass.toNonnegHomClass`：∀ {F : Type u_2} {α : Type u_3} 
{β : Type u_4} [inst : FunLike F α β] [inst_1 : AddGroup α] [inst_2 : AddCommMon
oid β]   [inst_3 : LinearOrd…
· 使用定理 `SeminormClass.toAddGroupSeminormClass`：∀ {F : Type u_12} {𝕜 : outParam (
Type u_13)} {E : outParam (Type u_14)} {inst : SeminormedRing 𝕜} {inst_1 : AddGr
oup E}   {inst_2 : SMul 𝕜 E…
· 使用定理 `Seminorm.finset_sup_apply`：finset_sup_apply (p : ι -> Seminorm 𝕜 E) (s :
 Finset ι) (x : E) : s.sup p x = ↑(s.sup fun i => NNReal.mk (p i x) (apply_nonne
g (p i) x))
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `NNReal.mul_finset_sup`：mul_finset_sup {α} (r : Real>=0) (s : Finset α) (
f : α -> Real>=0) : r * s.sup f = s.sup fun a => r * f a
-/
theorem finset_sup_smul (p : ι → Seminorm 𝕜 E) (s : Finset ι) (C : ℝ≥0) :
    s.sup (C • p) = C • s.sup p := by
  ext x
  rw [smul_apply, finset_sup_apply, finset_sup_apply]
  symm
  exact congr_arg ((↑) : ℝ≥0 → ℝ) (NNReal.mul_finset_sup C s (fun i ↦ ⟨p i x, apply_nonneg _ _⟩))
/-
**Seminorm.finset_sup_le_sum** 是 Mathlib 中的一个定理，位于命名空间 `Seminorm`。
形式化陈述：finset_sup_le_sum (p : ι -> Seminorm 𝕜 E) (s : Finset ι) : s.sup p <= ∑ i 
in s, p i
参数：p : ι -> Seminorm 𝕜 E；s : Finset ι。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Finset.sup_le_iff`：∀ {α : Type u_2} {β : Type u_3} [inst : SemilatticeSu
p α] [inst_1 : OrderBot α] {s : Finset β} {f : β → α} {a : α},   s.sup f ≤ a ↔ ∀
 b ∈ s,…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.sum_eq_sum_sdiff_singleton_add`：∀ {ι : Type u_1} {M : Type u_3} [
inst : AddCommMonoid M] [inst_1 : DecidableEq ι] {s : Finset ι} {i : ι},   i ∈ s
 → ∀ (f : ι → M), ∑ x ∈ s, …
· 使用定理 `le_add_iff_nonneg_left`：∀ {α : Type u_1} [inst : AddZeroClass α] [inst_1
 : LE α] [AddRightMono α] [AddRightReflectLE α] (a : α) {b : α},   a ≤ b + a ↔ 0
 ≤ b
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `IsOrderedCancelAddMonoid.toIsOrderedAddMonoid`：∀ {α : Type u_2} {inst : 
AddCommMonoid α} {inst_1 : Preorder α} [self : IsOrderedCancelAddMonoid α],   Is
OrderedAddMonoid α
· 使用定理 `IsRightCancelAdd.addRightReflectLE_of_addRightReflectLT`：∀ (N : Type u_2
) [inst : Add N] [IsRightCancelAdd N] [inst_2 : PartialOrder N] [AddRightReflect
LT N],   AddRightReflectLE N
· 使用定理 `instIsRightCancelAddOfAddRightReflectLE`：∀ {α : Type u_1} [inst : Add α]
 [inst_1 : PartialOrder α] [AddRightReflectLE α], IsRightCancelAdd α
· 使用定理 `addRightReflectLE_of_addLeftReflectLE`：∀ (N : Type u_2) [inst : AddCommS
emigroup N] [inst_1 : LE N] [AddLeftReflectLE N], AddRightReflectLE N
· 使用定理 `IsLeftCancelAdd.addLeftReflectLE_of_addLeftReflectLT`：∀ (N : Type u_2) [
inst : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftReflectLT N]
, AddLeftReflectLE N
· 使用定理 `IsCancelAdd.toIsLeftCancelAdd`：∀ {G : Type u} {inst : Add G} [self : IsC
ancelAdd G], IsLeftCancelAdd G
· 使用定理 `IsOrderedCancelAddMonoid.toIsCancelAdd`：∀ {α : Type u_1} [inst : AddComm
Monoid α] [inst_1 : PartialOrder α] [IsOrderedCancelAddMonoid α], IsCancelAdd α
· 使用定理 `IsOrderedCancelAddMonoid.toAddLeftReflectLT`：∀ {α : Type u_1} [inst : Ad
dCommMonoid α] [inst_1 : PartialOrder α] [IsOrderedCancelAddMonoid α], AddLeftRe
flectLT α
· 使用定理 `contravariant_swap_add_of_contravariant_add`：∀ (N : Type u_2) (r : N → N
 → Prop) [inst : AddCommSemigroup N] [ContravariantClass N N (fun x1 x2 => x1 + 
x2) r],   ContravariantClass N N …
· 使用定理 `bot_le`：∀ {α : Type u} [inst : LE α] [inst_1 : OrderBot α] {a : α}, ⊥ ≤ 
a
-/
theorem finset_sup_le_sum (p : ι → Seminorm 𝕜 E) (s : Finset ι) : s.sup p ≤ ∑ i ∈ s, p i := by
  classical
  refine Finset.sup_le_iff.mpr ?_
  intro i hi
  rw [Finset.sum_eq_sum_sdiff_singleton_add hi, le_add_iff_nonneg_left]
  exact bot_le
/-
**Seminorm.finset_sup_apply_le** 是 Mathlib 中的一个定理，位于命名空间 `Seminorm`。
形式化陈述：finset_sup_apply_le {p : ι -> Seminorm 𝕜 E} {s : Finset ι} {x : E} {a : Re
al} (ha : 0 <= a) (h : forall i, i in s -> p i x <= a) : s.sup p x <= a
参数：ha : 0 <= a；h : forall i, i in s -> p i x <= a。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CanLift.prf`：∀ {α : Sort u_1} {β : Sort u_2} {coe : outParam (β → α)} {c
ond : outParam (α → Prop)} [self : CanLift α β coe cond]   (x : α), cond x → ∃ y
,…
· 使用定理 `NonnegHomClass.apply_nonneg`：∀ {F : Type u_7} {α : outParam (Type u_8)} 
{β : outParam (Type u_9)} {inst : Zero β} {inst_1 : LE β}   {inst_2 : FunLike F 
α β} [self : Nonn…
· 使用定理 `AddGroupSeminormClass.toNonnegHomClass`：∀ {F : Type u_2} {α : Type u_3} 
{β : Type u_4} [inst : FunLike F α β] [inst_1 : AddGroup α] [inst_2 : AddCommMon
oid β]   [inst_3 : LinearOrd…
· 使用定理 `SeminormClass.toAddGroupSeminormClass`：∀ {F : Type u_12} {𝕜 : outParam (
Type u_13)} {E : outParam (Type u_14)} {inst : SeminormedRing 𝕜} {inst_1 : AddGr
oup E}   {inst_2 : SMul 𝕜 E…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Seminorm.finset_sup_apply`：finset_sup_apply (p : ι -> Seminorm 𝕜 E) (s :
 Finset ι) (x : E) : s.sup p x = ↑(s.sup fun i => NNReal.mk (p i x) (apply_nonne
g (p i) x))
· 使用定理 `NNReal.coe_le_coe`：∀ {r₁ r₂ : NNReal}, ↑r₁ ≤ ↑r₂ ↔ r₁ ≤ r₂
· 使用定理 `Finset.sup_le`：∀ {α : Type u_2} {β : Type u_3} [inst : SemilatticeSup α]
 [inst_1 : OrderBot α] {s : Finset β} {f : β → α} {a : α},   (∀ b ∈ s, f b ≤ a) 
→ s…
-/
theorem finset_sup_apply_le {p : ι → Seminorm 𝕜 E} {s : Finset ι} {x : E} {a : ℝ} (ha : 0 ≤ a)
    (h : ∀ i, i ∈ s → p i x ≤ a) : s.sup p x ≤ a := by
  lift a to ℝ≥0 using ha
  rw [finset_sup_apply, NNReal.coe_le_coe]
  exact Finset.sup_le h
/-
**Seminorm.le_finset_sup_apply** 是 Mathlib 中的一个定理，位于命名空间 `Seminorm`。
形式化陈述：le_finset_sup_apply {p : ι -> Seminorm 𝕜 E} {s : Finset ι} {x : E} {i : ι}
 (hi : i in s) : p i x <= s.sup p x
参数：hi : i in s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.le_sup`：le_sup {b : β} (hb : b in s) : f b <= s.sup f
-/
theorem le_finset_sup_apply {p : ι → Seminorm 𝕜 E} {s : Finset ι} {x : E} {i : ι}
    (hi : i ∈ s) : p i x ≤ s.sup p x :=
  (Finset.le_sup hi : p i ≤ s.sup p) x
/-
**Seminorm.finset_sup_apply_lt** 是 Mathlib 中的一个定理，位于命名空间 `Seminorm`。
形式化陈述：finset_sup_apply_lt {p : ι -> Seminorm 𝕜 E} {s : Finset ι} {x : E} {a : Re
al} (ha : 0 < a) (h : forall i, i in s -> p i x < a) : s.sup p x < a
参数：ha : 0 < a；h : forall i, i in s -> p i x < a。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CanLift.prf`：∀ {α : Sort u_1} {β : Sort u_2} {coe : outParam (β → α)} {c
ond : outParam (α → Prop)} [self : CanLift α β coe cond]   (x : α), cond x → ∃ y
,…
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `NonnegHomClass.apply_nonneg`：∀ {F : Type u_7} {α : outParam (Type u_8)} 
{β : outParam (Type u_9)} {inst : Zero β} {inst_1 : LE β}   {inst_2 : FunLike F 
α β} [self : Nonn…
· 使用定理 `AddGroupSeminormClass.toNonnegHomClass`：∀ {F : Type u_2} {α : Type u_3} 
{β : Type u_4} [inst : FunLike F α β] [inst_1 : AddGroup α] [inst_2 : AddCommMon
oid β]   [inst_3 : LinearOrd…
· 使用定理 `SeminormClass.toAddGroupSeminormClass`：∀ {F : Type u_12} {𝕜 : outParam (
Type u_13)} {E : outParam (Type u_14)} {inst : SeminormedRing 𝕜} {inst_1 : AddGr
oup E}   {inst_2 : SMul 𝕜 E…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Seminorm.finset_sup_apply`：finset_sup_apply (p : ι -> Seminorm 𝕜 E) (s :
 Finset ι) (x : E) : s.sup p x = ↑(s.sup fun i => NNReal.mk (p i x) (apply_nonne
g (p i) x))
· 使用定理 `NNReal.coe_lt_coe`：∀ {r₁ r₂ : NNReal}, ↑r₁ < ↑r₂ ↔ r₁ < r₂
· 使用定理 `Finset.sup_lt_iff`：∀ {α : Type u_2} {ι : Type u_5} [inst : LinearOrder α
] [inst_1 : OrderBot α] {s : Finset ι} {f : ι → α} {a : α},   ⊥ < a → (s.sup f <
 a ↔ ∀ …
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `NNReal.coe_pos`：∀ {r : NNReal}, 0 < ↑r ↔ 0 < r
-/
theorem finset_sup_apply_lt {p : ι → Seminorm 𝕜 E} {s : Finset ι} {x : E} {a : ℝ} (ha : 0 < a)
    (h : ∀ i, i ∈ s → p i x < a) : s.sup p x < a := by
  lift a to ℝ≥0 using ha.le
  rw [finset_sup_apply, NNReal.coe_lt_coe, Finset.sup_lt_iff]
  · exact h
  · exact NNReal.coe_pos.mpr ha
/-
**Seminorm.norm_sub_map_le_sub** 是 Mathlib 中的一个定理，位于命名空间 `Seminorm`。
形式化陈述：norm_sub_map_le_sub (p : Seminorm 𝕜 E) (x y : E) : ‖p x - p y‖ <= p (x - y
)
参数：p : Seminorm 𝕜 E；x y : E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `abs_sub_map_le_sub`：∀ {F : Type u_2} {α : Type u_3} {β : Type u_4} [inst
 : FunLike F α β] [inst_1 : AddGroup α] [inst_2 : AddCommGroup β]   [inst_3 : Li
nearOrde…
· 使用定理 `SeminormClass.toAddGroupSeminormClass`：∀ {F : Type u_12} {𝕜 : outParam (
Type u_13)} {E : outParam (Type u_14)} {inst : SeminormedRing 𝕜} {inst_1 : AddGr
oup E}   {inst_2 : SMul 𝕜 E…
-/
theorem norm_sub_map_le_sub (p : Seminorm 𝕜 E) (x y : E) : ‖p x - p y‖ ≤ p (x - y) :=
  abs_sub_map_le_sub p x y

end Module

end SeminormedRing

section SeminormedCommRing

variable [SeminormedRing 𝕜] [SeminormedCommRing 𝕜₂]
variable {σ₁₂ : 𝕜 →+* 𝕜₂} [RingHomIsometric σ₁₂]
variable [AddCommGroup E] [AddCommGroup E₂] [Module 𝕜 E] [Module 𝕜₂ E₂]

/-
**Seminorm.comp_smul** 是 Mathlib 中的一个定理，位于命名空间 `Seminorm`。
形式化陈述：comp_smul (p : Seminorm 𝕜₂ E₂) (f : E ->ₛₗ[σ₁₂] E₂) (c : 𝕜₂) : p.comp (c •
 f) = ‖c‖₊ • p.comp f
参数：p : Seminorm 𝕜₂ E₂；f : E ->ₛₗ[σ₁₂] E₂；c : 𝕜₂。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Seminorm.ext`：ext {p q : Seminorm 𝕜 E} (h : forall x, (p : E -> Real) x 
= q x) : p = q
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `SeminormClass.map_smul_eq_mul`：∀ {F : Type u_12} {𝕜 : outParam (Type u_1
3)} {E : outParam (Type u_14)} {inst : SeminormedRing 𝕜} {inst_1 : AddGroup E}  
 {inst_2 : SMul 𝕜 E…
· 使用定理 `smul_apply`：∀ {M : Type u_1} {F : Type u_2} {α : outParam (Type u_3)} {β
 : outParam (Type u_4)} {inst : FunLike F α β}   {inst_1 : SMul M β} {inst_2 : S
…
· 使用定理 `Seminorm.instIsSMulApplyReal`：∀ {R : Type u_1} {𝕜 : Type u_3} {E : Type 
u_7} [inst : SeminormedRing 𝕜] [inst_1 : AddGroup E] [inst_2 : SMul 𝕜 E]   [inst
_3 : SMul R ℝ] [in…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem comp_smul (p : Seminorm 𝕜₂ E₂) (f : E →ₛₗ[σ₁₂] E₂) (c : 𝕜₂) :
    p.comp (c • f) = ‖c‖₊ • p.comp f := by
  ext; simp [NNReal.smul_def, map_smul_eq_mul]
/-
**Seminorm.comp_smul_apply** 是 Mathlib 中的一个定理，位于命名空间 `Seminorm`。
形式化陈述：comp_smul_apply (p : Seminorm 𝕜₂ E₂) (f : E ->ₛₗ[σ₁₂] E₂) (c : 𝕜₂) (x : E)
 : p.comp (c • f) x = ‖c‖ * p (f x)
参数：p : Seminorm 𝕜₂ E₂；f : E ->ₛₗ[σ₁₂] E₂；c : 𝕜₂；x : E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormClass.map_smul_eq_mul`：∀ {F : Type u_12} {𝕜 : outParam (Type u_1
3)} {E : outParam (Type u_14)} {inst : SeminormedRing 𝕜} {inst_1 : AddGroup E}  
 {inst_2 : SMul 𝕜 E…
-/
theorem comp_smul_apply (p : Seminorm 𝕜₂ E₂) (f : E →ₛₗ[σ₁₂] E₂) (c : 𝕜₂) (x : E) :
    p.comp (c • f) x = ‖c‖ * p (f x) :=
  map_smul_eq_mul p _ _

end SeminormedCommRing

section NormedField

variable [NormedField 𝕜] [AddCommGroup E] [Module 𝕜 E] {p q : Seminorm 𝕜 E} {x : E}

/-- Auxiliary lemma to show that the infimum of seminorms is well-defined. -/
/-
**Seminorm.bddBelow_range_add** 是 Mathlib 中的一个定理，位于命名空间 `Seminorm`。
形式化陈述：bddBelow_range_add : BddBelow (range fun u => p u + q (x - u))
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `add_nonneg`：∀ {α : Type u_1} [inst : AddZeroClass α] [inst_1 : Preorder 
α] [AddLeftMono α] {a b : α}, 0 ≤ a → 0 ≤ b → 0 ≤ a + b
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `NonnegHomClass.apply_nonneg`：∀ {F : Type u_7} {α : outParam (Type u_8)} 
{β : outParam (Type u_9)} {inst : Zero β} {inst_1 : LE β}   {inst_2 : FunLike F 
α β} [self : Nonn…
· 使用定理 `AddGroupSeminormClass.toNonnegHomClass`：∀ {F : Type u_2} {α : Type u_3} 
{β : Type u_4} [inst : FunLike F α β] [inst_1 : AddGroup α] [inst_2 : AddCommMon
oid β]   [inst_3 : LinearOrd…
· 使用定理 `SeminormClass.toAddGroupSeminormClass`：∀ {F : Type u_12} {𝕜 : outParam (
Type u_13)} {E : outParam (Type u_14)} {inst : SeminormedRing 𝕜} {inst_1 : AddGr
oup E}   {inst_2 : SMul 𝕜 E…

--- 原说明 ---
Auxiliary lemma to show that the infimum of seminorms is well-defined.
-/
theorem bddBelow_range_add : BddBelow (range fun u => p u + q (x - u)) :=
  ⟨0, by
    rintro _ ⟨x, rfl⟩
    dsimp; positivity⟩
/-
**Seminorm.instInf** 是 Mathlib 中的一个实例，位于命名空间 `Seminorm`。
形式化陈述：instInf : Min (Seminorm 𝕜 E) where min p q
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
noncomputable instance instInf : Min (Seminorm 𝕜 E) where
  min p q :=
    { p.toAddGroupSeminorm ⊓ q.toAddGroupSeminorm with
      toFun := fun x => ⨅ u : E, p u + q (x - u)
      smul' := by
        intro a x
        obtain rfl | ha := eq_or_ne a 0
        · rw [norm_zero, zero_mul, zero_smul]
          refine
            ciInf_eq_of_forall_ge_of_forall_gt_exists_lt
              (fun i => by positivity)
              fun x hx => ⟨0, by rwa [map_zero, sub_zero, map_zero, add_zero]⟩
        simp_rw [Real.mul_iInf_of_nonneg (norm_nonneg a), mul_add, ← map_smul_eq_mul p, ←
          map_smul_eq_mul q, smul_sub]
        refine
          Function.Surjective.iInf_congr ((a⁻¹ • ·) : E → E)
            (fun u => ⟨a • u, inv_smul_smul₀ ha u⟩) fun u => ?_
        rw [smul_inv_smul₀ ha] }

@[simp]
/-
**Seminorm.inf_apply** 是 Mathlib 中的一个定理，位于命名空间 `Seminorm`。
形式化陈述：inf_apply (p q : Seminorm 𝕜 E) (x : E) : (p ⊓ q) x = ⨅ u : E, p u + q (x -
 u)
参数：p q : Seminorm 𝕜 E；x : E。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem inf_apply (p q : Seminorm 𝕜 E) (x : E) : (p ⊓ q) x = ⨅ u : E, p u + q (x - u) :=
  rfl
/-
**Seminorm.instLattice** 是 Mathlib 中的一个实例，位于命名空间 `Seminorm`。
形式化陈述：instLattice : Lattice (Seminorm 𝕜 E)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
noncomputable instance instLattice : Lattice (Seminorm 𝕜 E) :=
  { Seminorm.instSemilatticeSup with
    inf := (· ⊓ ·)
    inf_le_left := fun p q x =>
      ciInf_le_of_le bddBelow_range_add x <| by
        simp only [sub_self, map_zero, add_zero]; rfl
    inf_le_right := fun p q x =>
      ciInf_le_of_le bddBelow_range_add 0 <| by
        simp only [map_zero, zero_add, sub_zero]; rfl
    le_inf := fun a _ _ hab hac _ =>
      le_ciInf fun _ => (le_map_add_map_sub a _ _).trans <| add_le_add (hab _) (hac _) }
/-
**Seminorm.smul_inf** 是 Mathlib 中的一个定理，位于命名空间 `Seminorm`。
形式化陈述：smul_inf [SMul R Real] [SMul R Real>=0] [IsScalarTower R Real>=0 Real] (r 
: R) (p q : Seminorm 𝕜 E) : r • (p ⊓ q) = r • p ⊓ r • q
参数：r : R；p q : Seminorm 𝕜 E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Seminorm.ext`：ext {p q : Seminorm 𝕜 E} (h : forall x, (p : E -> Real) x 
= q x) : p = q
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `smul_apply`：∀ {M : Type u_1} {F : Type u_2} {α : outParam (Type u_3)} {β
 : outParam (Type u_4)} {inst : FunLike F α β}   {inst_1 : SMul M β} {inst_2 : S
…
· 使用定理 `Seminorm.instIsSMulApplyReal`：∀ {R : Type u_1} {𝕜 : Type u_3} {E : Type 
u_7} [inst : SeminormedRing 𝕜] [inst_1 : AddGroup E] [inst_2 : SMul 𝕜 E]   [inst
_3 : SMul R ℝ] [in…
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `smul_one_smul`：smul_one_smul {M} (N) [Monoid N] [SMul M N] [MulAction N 
α] [SMul M α] [IsScalarTower M N α] (x : M) (y : α) : (x • (1 : N)) • y = x • y
· 使用定理 `Real.mul_iInf_of_nonneg`：Real.mul_iInf_of_nonneg (ha : 0 <= r) (f : ι ->
 Real) : (r * ⨅ i, f i) = ⨅ i, r * f i
· 使用定理 `NNReal.coe_nonneg`：∀ (r : NNReal), 0 ≤ ↑r
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `mul_add`：mul_add {d : R} (_ : (a : R) * b₁ = c₁) (_ : a * b₂ = c₂) (_ : 
c₁ + 0 + c₂ = d) : a * (b₁ + b₂) = d
· 使用定理 `Distrib.leftDistribClass`：∀ (R : Type u_1) [inst : Distrib R], LeftDistr
ibClass R
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem smul_inf [SMul R ℝ] [SMul R ℝ≥0] [IsScalarTower R ℝ≥0 ℝ] (r : R) (p q : Seminorm 𝕜 E) :
    r • (p ⊓ q) = r • p ⊓ r • q := by
  ext
  simp_rw [smul_apply, inf_apply, smul_apply, ← smul_one_smul ℝ≥0 r (_ : ℝ), NNReal.smul_def,
    smul_eq_mul, Real.mul_iInf_of_nonneg (NNReal.coe_nonneg _), mul_add]

section Classical

open scoped Classical in
/-- We define the supremum of an arbitrary subset of `Seminorm 𝕜 E` as follows:
* if `s` is `BddAbove` *as a set of functions `E → ℝ`* (that is, if `s` is pointwise bounded
  above), we take the pointwise supremum of all elements of `s`, and we prove that it is indeed a
  seminorm.
* otherwise, we take the zero seminorm `⊥`.

There are two things worth mentioning here:
* First, it is not trivial at first that `s` being bounded above *by a function* implies
  being bounded above *as a seminorm*. We show this in `Seminorm.bddAbove_iff` by using
  that the `Sup s` as defined here is then a bounding seminorm for `s`. So it is important to make
  the case disjunction on `BddAbove ((↑) '' s : Set (E → ℝ))` and not `BddAbove s`.
* Since the pointwise `Sup` already gives `0` at points where a family of functions is
  not bounded above, one could hope that just using the pointwise `Sup` would work here, without the
  need for an additional case disjunction. As discussed on Zulip, this doesn't work because this can
  give a function which does *not* satisfy the seminorm axioms (typically sub-additivity).
-/
/-
**Seminorm.instSupSet** 是 Mathlib 中的一个实例，位于命名空间 `Seminorm`。
形式化陈述：instSupSet : SupSet (Seminorm 𝕜 E) where sSup s
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
We define the supremum of an arbitrary subset of `Seminorm 𝕜 E` as follows:
* if `s` is `BddAbove` *as a set of functions `E → ℝ`* (that is, if `s` is point
wise bounded
  above), we take the pointwise supremum of all elements of `s`, and we prove th
at it is indeed a
  seminorm.
* otherwise, we take the zero seminorm `⊥`.

There are two things worth mentioning here:
* First, it is not trivial at first that `s` being bounded above *by a function*
 implies
  being bounded above *as a seminorm*. We show this in `Seminorm.bddAbove_iff` b
y using
  that the `Sup s` as defined here is then a bounding seminorm for `s`. So it is
 important to make
  the case disjunction on `BddAbove ((↑) '' s : Set (E → ℝ))` and not `BddAbove 
s`.
* Since the pointwise `Sup` already gives `0` at points where a family of functi
ons is
  not bounded above, one could hope that just using the pointwise `Sup` would wo
rk here, without the
  need for an additional case disjunction. As discussed on Zulip, this doesn't w
ork because this can
  give a function which does *not* satisfy the seminorm axioms (typically sub-ad
ditivity).
-/
noncomputable instance instSupSet : SupSet (Seminorm 𝕜 E) where
  sSup s :=
    if h : BddAbove ((↑) '' s : Set (E → ℝ)) then
      { toFun := ⨆ p : s, ((p : Seminorm 𝕜 E) : E → ℝ)
        map_zero' := by
          rw [iSup_apply, ← @Real.iSup_const_zero s]
          congr!
          rename_i _ _ _ i
          exact map_zero i.1
        add_le' := fun x y => by
          rcases h with ⟨q, hq⟩
          obtain rfl | h := s.eq_empty_or_nonempty
          · simp [Real.iSup_of_isEmpty]
          have : Nonempty ↑s := h.coe_sort
          simp only [iSup_apply]
          refine ciSup_le fun i =>
            ((i : Seminorm 𝕜 E).add_le' x y).trans <| add_le_add
              -- Porting note: `f` is provided to force `Subtype.val` to appear.
              -- A type ascription on `_` would have also worked, but would have been more verbose.
              (le_ciSup (f := fun i => (Subtype.val i : Seminorm 𝕜 E).toFun x) ⟨q x, ?_⟩ i)
              (le_ciSup (f := fun i => (Subtype.val i : Seminorm 𝕜 E).toFun y) ⟨q y, ?_⟩ i)
          <;> rw [mem_upperBounds, forall_mem_range]
          <;> exact fun j => hq (mem_image_of_mem _ j.2) _
        neg' := fun x => by
          simp only [iSup_apply]
          congr! 2
          rename_i _ _ _ i
          exact i.1.neg' _
        smul' := fun a x => by
          simp only [iSup_apply]
          rw [← smul_eq_mul,
            Real.smul_iSup_of_nonneg (norm_nonneg a) fun i : s => (i : Seminorm 𝕜 E) x]
          congr!
          rename_i _ _ _ i
          exact i.1.smul' a x }
    else ⊥
/-
**Seminorm.coe_sSup_eq'** 是 Mathlib 中的一个定理，位于命名空间 `Seminorm`。
形式化陈述：∀ {𝕜 : Type u_3} {E : Type u_7} [inst : NormedField 𝕜] [inst_1 : AddCommGr
oup E] [inst_2 : _root_.Module 𝕜 E]   {s : Set (Seminorm 𝕜 E)}, BddAbove (DFunLi
ke.coe '' s) → ⇑(sSup s) = ⨆ p, ⇑↑p
参数：Seminorm 𝕜 E；DFunLike.coe '' s；sSup s。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `dif_pos`：∀ {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t : c → α
} {e : ¬c → α}, dite c t e = t hc
-/
protected theorem coe_sSup_eq' {s : Set <| Seminorm 𝕜 E}
    (hs : BddAbove ((↑) '' s : Set (E → ℝ))) : ↑(sSup s) = ⨆ p : s, ((p : Seminorm 𝕜 E) : E → ℝ) :=
  congr_arg _ (dif_pos hs)
/-
**Seminorm.bddAbove_iff** 是 Mathlib 中的一个定理，位于命名空间 `Seminorm`。
形式化陈述：∀ {𝕜 : Type u_3} {E : Type u_7} [inst : NormedField 𝕜] [inst_1 : AddCommGr
oup E] [inst_2 : _root_.Module 𝕜 E]   {s : Set (Seminorm 𝕜 E)}, BddAbove s ↔ Bdd
Above (DFunLike.coe '' s)
参数：Seminorm 𝕜 E；DFunLike.coe '' s。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.forall_mem_image`：forall_mem_image {f : α -> β} {s : Set α} {p : β -
> Prop} : (forall y in f '' s, p y) ↔ forall ⦃x⦄, x in s -> p (f x)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Seminorm.coe_sSup_eq'`：∀ {𝕜 : Type u_3} {E : Type u_7} [inst : NormedFie
ld 𝕜] [inst_1 : AddCommGroup E] [inst_2 : _root_.Module 𝕜 E]   {s : Set (Seminor
m 𝕜 E)}, Bd…
· 使用定理 `iSup_apply`：iSup_apply {α : Type*} {β : α -> Type*} {ι : Sort*} [forall 
i, SupSet (β i)] {f : ι -> forall a, β a} {a : α} : (⨆ i, f i) a = ⨆ i, f i a
· 使用定理 `le_ciSup`：le_ciSup {f : ι -> α} (H : BddAbove (range f)) (c : ι) : f c <
= iSup f
· 使用定理 `Set.forall_mem_range`：forall_mem_range {p : α -> Prop} : (forall a in ra
nge f, p a) ↔ forall i, p (f i)
· 使用定理 `Set.mem_image_of_mem`：mem_image_of_mem (f : α -> β) {x : α} {a : Set α} 
(h : x in a) : f x in f '' a
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
-/
protected theorem bddAbove_iff {s : Set <| Seminorm 𝕜 E} :
    BddAbove s ↔ BddAbove ((↑) '' s : Set (E → ℝ)) :=
  ⟨fun ⟨q, hq⟩ => ⟨q, forall_mem_image.2 fun _ hp => hq hp⟩, fun H =>
    ⟨sSup s, fun p hp x => by
      dsimp
      rw [Seminorm.coe_sSup_eq' H, iSup_apply]
      rcases H with ⟨q, hq⟩
      exact
        le_ciSup ⟨q x, forall_mem_range.mpr fun i : s => hq (mem_image_of_mem _ i.2) x⟩ ⟨p, hp⟩⟩⟩
/-
**Seminorm.bddAbove_range_iff** 是 Mathlib 中的一个定理，位于命名空间 `Seminorm`。
形式化陈述：∀ {𝕜 : Type u_3} {E : Type u_7} [inst : NormedField 𝕜] [inst_1 : AddCommGr
oup E] [inst_2 : _root_.Module 𝕜 E]   {ι : Sort u_12} {p : ι → Seminorm 𝕜 E}, Bd
dAbove (Set.range p) ↔ ∀ (x : E), BddAbove (Set.range fun i => (p i) x)
参数：Set.range p；x : E；Set.range fun i => (p i) x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Seminorm.bddAbove_iff`：∀ {𝕜 : Type u_3} {E : Type u_7} [inst : NormedFie
ld 𝕜] [inst_1 : AddCommGroup E] [inst_2 : _root_.Module 𝕜 E]   {s : Set (Seminor
m 𝕜 E)}, Bd…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.range_comp`：range_comp (g : α -> β) (f : ι -> α) : range (g ∘ f) = g
 '' range f
· 使用引理 `bddAbove_range_pi`：bddAbove_range_pi {F : ι -> forall a, π a} : BddAbove
 (range F) ↔ forall a, BddAbove (range fun i => F i a)
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
protected theorem bddAbove_range_iff {ι : Sort*} {p : ι → Seminorm 𝕜 E} :
    BddAbove (range p) ↔ ∀ x, BddAbove (range fun i ↦ p i x) := by
  rw [Seminorm.bddAbove_iff, ← range_comp, bddAbove_range_pi]; rfl
/-
**Seminorm.coe_sSup_eq** 是 Mathlib 中的一个定理，位于命名空间 `Seminorm`。
形式化陈述：∀ {𝕜 : Type u_3} {E : Type u_7} [inst : NormedField 𝕜] [inst_1 : AddCommGr
oup E] [inst_2 : _root_.Module 𝕜 E]   {s : Set (Seminorm 𝕜 E)}, BddAbove s → ⇑(s
Sup s) = ⨆ p, ⇑↑p
参数：Seminorm 𝕜 E；sSup s。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Seminorm.coe_sSup_eq'`：∀ {𝕜 : Type u_3} {E : Type u_7} [inst : NormedFie
ld 𝕜] [inst_1 : AddCommGroup E] [inst_2 : _root_.Module 𝕜 E]   {s : Set (Seminor
m 𝕜 E)}, Bd…
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Seminorm.bddAbove_iff`：∀ {𝕜 : Type u_3} {E : Type u_7} [inst : NormedFie
ld 𝕜] [inst_1 : AddCommGroup E] [inst_2 : _root_.Module 𝕜 E]   {s : Set (Seminor
m 𝕜 E)}, Bd…
-/
protected theorem coe_sSup_eq {s : Set <| Seminorm 𝕜 E} (hs : BddAbove s) :
    ↑(sSup s) = ⨆ p : s, ((p : Seminorm 𝕜 E) : E → ℝ) :=
  Seminorm.coe_sSup_eq' (Seminorm.bddAbove_iff.mp hs)
/-
**Seminorm.coe_iSup_eq** 是 Mathlib 中的一个定理，位于命名空间 `Seminorm`。
形式化陈述：∀ {𝕜 : Type u_3} {E : Type u_7} [inst : NormedField 𝕜] [inst_1 : AddCommGr
oup E] [inst_2 : _root_.Module 𝕜 E]   {ι : Sort u_12} {p : ι → Seminorm 𝕜 E}, Bd
dAbove (Set.range p) → ⇑(⨆ i, p i) = ⨆ i, ⇑(p i)
参数：Set.range p；⨆ i, p i；p i。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `sSup_range`：sSup_range : sSup (range f) = iSup f
· 使用定理 `Seminorm.coe_sSup_eq`：∀ {𝕜 : Type u_3} {E : Type u_7} [inst : NormedFiel
d 𝕜] [inst_1 : AddCommGroup E] [inst_2 : _root_.Module 𝕜 E]   {s : Set (Seminorm
 𝕜 E)}, Bd…
· 使用定理 `iSup_range'`：iSup_range' (g : β -> α) (f : ι -> β) : ⨆ b : range f, g b 
= ⨆ i, g (f i)
-/
protected theorem coe_iSup_eq {ι : Sort*} {p : ι → Seminorm 𝕜 E} (hp : BddAbove (range p)) :
    ↑(⨆ i, p i) = ⨆ i, ((p i : Seminorm 𝕜 E) : E → ℝ) := by
  rw [← sSup_range, Seminorm.coe_sSup_eq hp]
  exact iSup_range' (fun p : Seminorm 𝕜 E => (p : E → ℝ)) p
/-
**Seminorm.sSup_apply** 是 Mathlib 中的一个定理，位于命名空间 `Seminorm`。
形式化陈述：∀ {𝕜 : Type u_3} {E : Type u_7} [inst : NormedField 𝕜] [inst_1 : AddCommGr
oup E] [inst_2 : _root_.Module 𝕜 E]   {s : Set (Seminorm 𝕜 E)}, BddAbove s → ∀ {
x : E}, (sSup s) x = ⨆ p, ↑p x
参数：Seminorm 𝕜 E；sSup s。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Seminorm.coe_sSup_eq`：∀ {𝕜 : Type u_3} {E : Type u_7} [inst : NormedFiel
d 𝕜] [inst_1 : AddCommGroup E] [inst_2 : _root_.Module 𝕜 E]   {s : Set (Seminorm
 𝕜 E)}, Bd…
· 使用定理 `iSup_apply`：iSup_apply {α : Type*} {β : α -> Type*} {ι : Sort*} [forall 
i, SupSet (β i)] {f : ι -> forall a, β a} {a : α} : (⨆ i, f i) a = ⨆ i, f i a
-/
protected theorem sSup_apply {s : Set (Seminorm 𝕜 E)} (hp : BddAbove s) {x : E} :
    (sSup s) x = ⨆ p : s, (p : E → ℝ) x := by
  rw [Seminorm.coe_sSup_eq hp, iSup_apply]
/-
**Seminorm.iSup_apply** 是 Mathlib 中的一个定理，位于命名空间 `Seminorm`。
形式化陈述：∀ {𝕜 : Type u_3} {E : Type u_7} [inst : NormedField 𝕜] [inst_1 : AddCommGr
oup E] [inst_2 : _root_.Module 𝕜 E]   {ι : Sort u_12} {p : ι → Seminorm 𝕜 E}, Bd
dAbove (Set.range p) → ∀ {x : E}, (⨆ i, p i) x = ⨆ i, (p i) x
参数：Set.range p；⨆ i, p i；p i。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Seminorm.coe_iSup_eq`：∀ {𝕜 : Type u_3} {E : Type u_7} [inst : NormedFiel
d 𝕜] [inst_1 : AddCommGroup E] [inst_2 : _root_.Module 𝕜 E]   {ι : Sort u_12} {p
 : ι → Sem…
· 使用定理 `iSup_apply`：iSup_apply {α : Type*} {β : α -> Type*} {ι : Sort*} [forall 
i, SupSet (β i)] {f : ι -> forall a, β a} {a : α} : (⨆ i, f i) a = ⨆ i, f i a
-/
protected theorem iSup_apply {ι : Sort*} {p : ι → Seminorm 𝕜 E}
    (hp : BddAbove (range p)) {x : E} : (⨆ i, p i) x = ⨆ i, p i x := by
  rw [Seminorm.coe_iSup_eq hp, iSup_apply]
/-
**Seminorm.sSup_empty** 是 Mathlib 中的一个定理，位于命名空间 `Seminorm`。
形式化陈述：∀ {𝕜 : Type u_3} {E : Type u_7} [inst : NormedField 𝕜] [inst_1 : AddCommGr
oup E] [inst_2 : _root_.Module 𝕜 E],   sSup ∅ = ⊥
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Seminorm.ext`：ext {p q : Seminorm 𝕜 E} (h : forall x, (p : E -> Real) x 
= q x) : p = q
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Seminorm.sSup_apply`：∀ {𝕜 : Type u_3} {E : Type u_7} [inst : NormedField
 𝕜] [inst_1 : AddCommGroup E] [inst_2 : _root_.Module 𝕜 E]   {s : Set (Seminorm 
𝕜 E)}, Bd…
· 使用定理 `bddAbove_empty`：bddAbove_empty [Nonempty α] : BddAbove (∅ : Set α)
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `Real.iSup_of_isEmpty`：∀ {ι : Sort u_1} [IsEmpty ι] (f : ι → ℝ), ⨆ i, f i
 = 0
· 使用定理 `Set.instIsEmptyElemEmptyCollection`：∀ (α : Type u), IsEmpty ↑∅
-/
protected theorem sSup_empty : sSup (∅ : Set (Seminorm 𝕜 E)) = ⊥ := by
  ext
  rw [Seminorm.sSup_apply bddAbove_empty, Real.iSup_of_isEmpty]
  rfl

set_option backward.privateInPublic true in
/-
**Seminorm.isLUB_sSup** 是 Mathlib 中的一个定理，位于命名空间 `Seminorm`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private theorem isLUB_sSup (s : Set (Seminorm 𝕜 E)) (hs₁ : BddAbove s) (hs₂ : s.Nonempty) :
    IsLUB s (sSup s) := by
  refine ⟨fun p hp x => ?_, fun p hp x => ?_⟩ <;> have : Nonempty ↑s := hs₂.coe_sort <;>
    dsimp <;> rw [Seminorm.coe_sSup_eq hs₁, iSup_apply]
  · rcases hs₁ with ⟨q, hq⟩
    exact le_ciSup ⟨q x, forall_mem_range.mpr fun i : s => hq i.2 x⟩ ⟨p, hp⟩
  · exact ciSup_le fun q => hp q.2 x

set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
/-- `Seminorm 𝕜 E` is a conditionally complete lattice.

Note that, while `inf`, `sup` and `sSup` have good definitional properties (corresponding to
the instances given here for `Inf`, `Sup` and `SupSet` respectively), `sInf s` is just
defined as the supremum of the lower bounds of `s`, which is not really useful in practice. If you
need to use `sInf` on seminorms, then you should probably provide a more workable definition first,
but this is unlikely to happen so we keep the "bad" definition for now. -/
/-
**Seminorm.instConditionallyCompleteLattice** 是 Mathlib 中的一个实例，位于命名空间 `Seminorm`
。
形式化陈述：instConditionallyCompleteLattice : ConditionallyCompleteLattice (Seminorm 
𝕜 E)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `_private.Mathlib.Analysis.Seminorm.0.Seminorm.isLUB_sSup`：∀ {𝕜 : Type u_
3} {E : Type u_7} [inst : NormedField 𝕜] [inst_1 : AddCommGroup E] [inst_2 : _ro
ot_.Module 𝕜 E]   (s : Set (Seminorm 𝕜 E)), Bd…

--- 原说明 ---
`Seminorm 𝕜 E` is a conditionally complete lattice.

Note that, while `inf`, `sup` and `sSup` have good definitional properties (corr
esponding to
the instances given here for `Inf`, `Sup` and `SupSet` respectively), `sInf s` i
s just
defined as the supremum of the lower bounds of `s`, which is not really useful i
n practice. If you
need to use `sInf` on seminorms, then you should probably provide a more workabl
e definition first,
but this is unlikely to happen so we keep the "bad" definition for now.
-/
noncomputable instance instConditionallyCompleteLattice :
    ConditionallyCompleteLattice (Seminorm 𝕜 E) :=
  conditionallyCompleteLatticeOfLatticeOfsSup (Seminorm 𝕜 E) Seminorm.isLUB_sSup

end Classical

end NormedField

/-! ### Seminorm ball -/


section SeminormedRing

variable [SeminormedRing 𝕜]

section AddCommGroup

variable [AddCommGroup E]

section SMul

variable [SMul 𝕜 E] (p : Seminorm 𝕜 E)

/-- The ball of radius `r` at `x` with respect to seminorm `p` is the set of elements `y` with
`p (y - x) < r`. -/
/-
**Seminorm.ball** 是 Mathlib 中的一个定义，位于命名空间 `Seminorm`。
形式化陈述：ball (x : E) (r : Real)
参数：x : E；r : Real。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The ball of radius `r` at `x` with respect to seminorm `p` is the set of element
s `y` with
`p (y - x) < r`.
-/
def ball (x : E) (r : ℝ) :=
  { y : E | p (y - x) < r }

/-- The closed ball of radius `r` at `x` with respect to seminorm `p` is the set of elements `y`
with `p (y - x) ≤ r`. -/
/-
**Seminorm.closedBall** 是 Mathlib 中的一个定义，位于命名空间 `Seminorm`。
形式化陈述：closedBall (x : E) (r : Real)
参数：x : E；r : Real。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The closed ball of radius `r` at `x` with respect to seminorm `p` is the set of 
elements `y`
with `p (y - x) ≤ r`.
-/
def closedBall (x : E) (r : ℝ) :=
  { y : E | p (y - x) ≤ r }

variable {x y : E} {r : ℝ}

@[simp]
/-
**Seminorm.mem_ball** 是 Mathlib 中的一个定理，位于命名空间 `Seminorm`。
形式化陈述：mem_ball : y in ball p x r ↔ p (y - x) < r
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem mem_ball : y ∈ ball p x r ↔ p (y - x) < r :=
  Iff.rfl

@[simp]
/-
**Seminorm.mem_closedBall** 是 Mathlib 中的一个定理，位于命名空间 `Seminorm`。
形式化陈述：mem_closedBall : y in closedBall p x r ↔ p (y - x) <= r
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem mem_closedBall : y ∈ closedBall p x r ↔ p (y - x) ≤ r :=
  Iff.rfl
/-
**Seminorm.mem_ball_self** 是 Mathlib 中的一个定理，位于命名空间 `Seminorm`。
形式化陈述：mem_ball_self (hr : 0 < r) : x in ball p x r
参数：hr : 0 < r。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `sub_self`：∀ {G : Type u_1} [inst : AddGroup G] (a : G), a - a = 0
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `AddGroupSeminormClass.toZeroHomClass`：∀ {F : Type u_2} {α : Type u_3} {β
 : Type u_4} [inst : FunLike F α β] [inst_1 : AddGroup α] [inst_2 : AddCommMonoi
d β]   [inst_3 : PartialOr…
· 使用定理 `SeminormClass.toAddGroupSeminormClass`：∀ {F : Type u_12} {𝕜 : outParam (
Type u_13)} {E : outParam (Type u_14)} {inst : SeminormedRing 𝕜} {inst_1 : AddGr
oup E}   {inst_2 : SMul 𝕜 E…
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
-/
theorem mem_ball_self (hr : 0 < r) : x ∈ ball p x r := by simp [hr]
/-
**Seminorm.mem_closedBall_self** 是 Mathlib 中的一个定理，位于命名空间 `Seminorm`。
形式化陈述：mem_closedBall_self (hr : 0 <= r) : x in closedBall p x r
参数：hr : 0 <= r。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `sub_self`：∀ {G : Type u_1} [inst : AddGroup G] (a : G), a - a = 0
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `AddGroupSeminormClass.toZeroHomClass`：∀ {F : Type u_2} {α : Type u_3} {β
 : Type u_4} [inst : FunLike F α β] [inst_1 : AddGroup α] [inst_2 : AddCommMonoi
d β]   [inst_3 : PartialOr…
· 使用定理 `SeminormClass.toAddGroupSeminormClass`：∀ {F : Type u_12} {𝕜 : outParam (
Type u_13)} {E : outParam (Type u_14)} {inst : SeminormedRing 𝕜} {inst_1 : AddGr
oup E}   {inst_2 : SMul 𝕜 E…
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
-/
theorem mem_closedBall_self (hr : 0 ≤ r) : x ∈ closedBall p x r := by simp [hr]
/-
**Seminorm.mem_ball_zero** 是 Mathlib 中的一个定理，位于命名空间 `Seminorm`。
形式化陈述：mem_ball_zero : y in ball p 0 r ↔ p y < r
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Seminorm.mem_ball`：mem_ball : y in ball p x r ↔ p (y - x) < r
· 使用定理 `sub_zero`：∀ {G : Type u_3} [inst : SubNegZeroMonoid G] (a : G), a - 0 = 
a
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem mem_ball_zero : y ∈ ball p 0 r ↔ p y < r := by rw [mem_ball, sub_zero]
/-
**Seminorm.mem_closedBall_zero** 是 Mathlib 中的一个定理，位于命名空间 `Seminorm`。
形式化陈述：mem_closedBall_zero : y in closedBall p 0 r ↔ p y <= r
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Seminorm.mem_closedBall`：mem_closedBall : y in closedBall p x r ↔ p (y -
 x) <= r
· 使用定理 `sub_zero`：∀ {G : Type u_3} [inst : SubNegZeroMonoid G] (a : G), a - 0 = 
a
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem mem_closedBall_zero : y ∈ closedBall p 0 r ↔ p y ≤ r := by rw [mem_closedBall, sub_zero]
/-
**Seminorm.ball_zero_eq** 是 Mathlib 中的一个定理，位于命名空间 `Seminorm`。
形式化陈述：ball_zero_eq : ball p 0 r = { y : E | p y < r }
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `Seminorm.mem_ball_zero`：mem_ball_zero : y in ball p 0 r ↔ p y < r
-/
theorem ball_zero_eq : ball p 0 r = { y : E | p y < r } :=
  Set.ext fun _ => p.mem_ball_zero
/-
**Seminorm.closedBall_zero_eq** 是 Mathlib 中的一个定理，位于命名空间 `Seminorm`。
形式化陈述：closedBall_zero_eq : closedBall p 0 r = { y : E | p y <= r }
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `Seminorm.mem_closedBall_zero`：mem_closedBall_zero : y in closedBall p 0 
r ↔ p y <= r
-/
theorem closedBall_zero_eq : closedBall p 0 r = { y : E | p y ≤ r } :=
  Set.ext fun _ => p.mem_closedBall_zero
/-
**Seminorm.ball_subset_closedBall** 是 Mathlib 中的一个定理，位于命名空间 `Seminorm`。
形式化陈述：ball_subset_closedBall (x r) : ball p x r subseteq closedBall p x r
参数：x r。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Seminorm.mem_closedBall`：mem_closedBall : y in closedBall p x r ↔ p (y -
 x) <= r
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Seminorm.mem_ball`：mem_ball : y in ball p x r ↔ p (y - x) < r
-/
theorem ball_subset_closedBall (x r) : ball p x r ⊆ closedBall p x r := fun _ h =>
  (mem_closedBall _).mpr ((mem_ball _).mp h).le
/-
**Seminorm.closedBall_eq_biInter_ball** 是 Mathlib 中的一个定理，位于命名空间 `Seminorm`。
形式化陈述：closedBall_eq_biInter_ball (x r) : closedBall p x r = ⋂ ρ > r, ball p x ρ
参数：x r。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem closedBall_eq_biInter_ball (x r) : closedBall p x r = ⋂ ρ > r, ball p x ρ := by
  ext y; simp_rw [mem_closedBall, mem_iInter₂, mem_ball, ← forall_gt_iff_le]

@[simp]
/-
**Seminorm.ball_zero'** 是 Mathlib 中的一个定理，位于命名空间 `Seminorm`。
形式化陈述：ball_zero' (x : E) (hr : 0 < r) : ball (0 : Seminorm 𝕜 E) x r = Set.univ
参数：x : E；hr : 0 < r。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.eq_univ_iff_forall`：eq_univ_iff_forall {s : Set α} : s = univ ↔ fora
ll x, x in s
· 使用定理 `Seminorm.ball.eq_1`：∀ {𝕜 : Type u_3} {E : Type u_7} [inst : SeminormedRi
ng 𝕜] [inst_1 : AddCommGroup E] [inst_2 : SMul 𝕜 E]   (p : Seminorm 𝕜 E) (x : E)
 (r : ℝ)…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `zero_apply`：∀ {F : Type u_1} {α : outParam (Type u_2)} {β : outParam (Ty
pe u_3)} {inst : FunLike F α β} {inst_1 : Zero β}   {inst_2 : Zero F} [self : Is
…
· 使用定理 `Seminorm.instIsZeroApplyReal`：∀ {𝕜 : Type u_3} {E : Type u_7} [inst : Se
minormedRing 𝕜] [inst_1 : AddGroup E] [inst_2 : SMul 𝕜 E],   IsZeroApply (Semino
rm 𝕜 E) E ℝ
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
theorem ball_zero' (x : E) (hr : 0 < r) : ball (0 : Seminorm 𝕜 E) x r = Set.univ := by
  rw [Set.eq_univ_iff_forall, ball]
  simp [hr]

@[simp]
/-
**Seminorm.closedBall_zero'** 是 Mathlib 中的一个定理，位于命名空间 `Seminorm`。
形式化陈述：closedBall_zero' (x : E) (hr : 0 < r) : closedBall (0 : Seminorm 𝕜 E) x r 
= Set.univ
参数：x : E；hr : 0 < r。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.eq_univ_of_subset`：eq_univ_of_subset {s t : Set α} (h : s subseteq t
) (hs : s = univ) : t = univ
· 使用定理 `Seminorm.ball_subset_closedBall`：ball_subset_closedBall (x r) : ball p x
 r subseteq closedBall p x r
· 使用定理 `Seminorm.ball_zero'`：ball_zero' (x : E) (hr : 0 < r) : ball (0 : Seminor
m 𝕜 E) x r = Set.univ
-/
theorem closedBall_zero' (x : E) (hr : 0 < r) : closedBall (0 : Seminorm 𝕜 E) x r = Set.univ :=
  eq_univ_of_subset (ball_subset_closedBall _ _ _) (ball_zero' x hr)
/-
**Seminorm.ball_smul** 是 Mathlib 中的一个定理，位于命名空间 `Seminorm`。
形式化陈述：ball_smul (p : Seminorm 𝕜 E) {c : NNReal} (hc : 0 < c) (r : Real) (x : E) 
: (c • p).ball x r = p.ball x (r / c)
参数：p : Seminorm 𝕜 E；hc : 0 < c；r : Real；x : E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Seminorm.mem_ball`：mem_ball : y in ball p x r ↔ p (y - x) < r
· 使用定理 `smul_apply`：∀ {M : Type u_1} {F : Type u_2} {α : outParam (Type u_3)} {β
 : outParam (Type u_4)} {inst : FunLike F α β}   {inst_1 : SMul M β} {inst_2 : S
…
· 使用定理 `Seminorm.instIsSMulApplyReal`：∀ {R : Type u_1} {𝕜 : Type u_3} {E : Type 
u_7} [inst : SeminormedRing 𝕜] [inst_1 : AddGroup E] [inst_2 : SMul 𝕜 E]   [inst
_3 : SMul R ℝ] [in…
· 使用定理 `NNReal.smul_def`：smul_def {M : Type*} [SMul Real M] (c : Real>=0) (x : M
) : c • x = (c : Real) • x
· 使用引理 `smul_eq_mul`：smul_eq_mul {α : Type*} [Mul α] (a b : α) : a • b = a * b
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用引理 `lt_div_iff₀`：lt_div_iff₀ (hc : 0 < c) : a < b / c ↔ a * c < b
· 使用定理 `MulPosReflectLE.toMulPosReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [MulPosReflectLE α], MulPosReflectLT α
· 使用定理 `MulPosStrictMono.toMulPosReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [MulPosStrictMono α], MulPosReflectLE α
· 使用定理 `IsStrictOrderedRing.toMulPosStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], MulPosStrictMono 
R
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `NNReal.coe_pos`：∀ {r : NNReal}, 0 < ↑r ↔ 0 < r
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem ball_smul (p : Seminorm 𝕜 E) {c : NNReal} (hc : 0 < c) (r : ℝ) (x : E) :
    (c • p).ball x r = p.ball x (r / c) := by
  ext
  rw [mem_ball, mem_ball, smul_apply, NNReal.smul_def, smul_eq_mul, mul_comm,
    lt_div_iff₀ (NNReal.coe_pos.mpr hc)]
/-
**Seminorm.closedBall_smul** 是 Mathlib 中的一个定理，位于命名空间 `Seminorm`。
形式化陈述：closedBall_smul (p : Seminorm 𝕜 E) {c : NNReal} (hc : 0 < c) (r : Real) (x
 : E) : (c • p).closedBall x r = p.closedBall x (r / c)
参数：p : Seminorm 𝕜 E；hc : 0 < c；r : Real；x : E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Seminorm.mem_closedBall`：mem_closedBall : y in closedBall p x r ↔ p (y -
 x) <= r
· 使用定理 `smul_apply`：∀ {M : Type u_1} {F : Type u_2} {α : outParam (Type u_3)} {β
 : outParam (Type u_4)} {inst : FunLike F α β}   {inst_1 : SMul M β} {inst_2 : S
…
· 使用定理 `Seminorm.instIsSMulApplyReal`：∀ {R : Type u_1} {𝕜 : Type u_3} {E : Type 
u_7} [inst : SeminormedRing 𝕜] [inst_1 : AddGroup E] [inst_2 : SMul 𝕜 E]   [inst
_3 : SMul R ℝ] [in…
· 使用定理 `NNReal.smul_def`：smul_def {M : Type*} [SMul Real M] (c : Real>=0) (x : M
) : c • x = (c : Real) • x
· 使用引理 `smul_eq_mul`：smul_eq_mul {α : Type*} [Mul α] (a b : α) : a • b = a * b
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用引理 `le_div_iff₀`：le_div_iff₀ (hc : 0 < c) : a <= b / c ↔ a * c <= b
· 使用定理 `MulPosReflectLE.toMulPosReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [MulPosReflectLE α], MulPosReflectLT α
· 使用定理 `MulPosStrictMono.toMulPosReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [MulPosStrictMono α], MulPosReflectLE α
· 使用定理 `IsStrictOrderedRing.toMulPosStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], MulPosStrictMono 
R
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `NNReal.coe_pos`：∀ {r : NNReal}, 0 < ↑r ↔ 0 < r
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem closedBall_smul (p : Seminorm 𝕜 E) {c : NNReal} (hc : 0 < c) (r : ℝ) (x : E) :
    (c • p).closedBall x r = p.closedBall x (r / c) := by
  ext
  rw [mem_closedBall, mem_closedBall, smul_apply, NNReal.smul_def, smul_eq_mul, mul_comm,
    le_div_iff₀ (NNReal.coe_pos.mpr hc)]
/-
**Seminorm.ball_sup** 是 Mathlib 中的一个定理，位于命名空间 `Seminorm`。
形式化陈述：ball_sup (p : Seminorm 𝕜 E) (q : Seminorm 𝕜 E) (e : E) (r : Real) : ball (
p ⊔ q) e r = ball p e r inter ball q e r
参数：p : Seminorm 𝕜 E；q : Seminorm 𝕜 E；e : E；r : Real。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem ball_sup (p : Seminorm 𝕜 E) (q : Seminorm 𝕜 E) (e : E) (r : ℝ) :
    ball (p ⊔ q) e r = ball p e r ∩ ball q e r := by
  simp_rw [ball, ← Set.ofPred_and, coe_sup, Pi.sup_apply, sup_lt_iff]
/-
**Seminorm.closedBall_sup** 是 Mathlib 中的一个定理，位于命名空间 `Seminorm`。
形式化陈述：closedBall_sup (p : Seminorm 𝕜 E) (q : Seminorm 𝕜 E) (e : E) (r : Real) : 
closedBall (p ⊔ q) e r = closedBall p e r inter closedBall q e r
参数：p : Seminorm 𝕜 E；q : Seminorm 𝕜 E；e : E；r : Real。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem closedBall_sup (p : Seminorm 𝕜 E) (q : Seminorm 𝕜 E) (e : E) (r : ℝ) :
    closedBall (p ⊔ q) e r = closedBall p e r ∩ closedBall q e r := by
  simp_rw [closedBall, ← Set.ofPred_and, coe_sup, Pi.sup_apply, sup_le_iff]
/-
**Seminorm.ball_finset_sup'** 是 Mathlib 中的一个定理，位于命名空间 `Seminorm`。
形式化陈述：ball_finset_sup' (p : ι -> Seminorm 𝕜 E) (s : Finset ι) (H : s.Nonempty) (
e : E) (r : Real) : ball (s.sup' H p) e r = s.inf' H fun i => ball (p i) e r
参数：p : ι -> Seminorm 𝕜 E；s : Finset ι；H : s.Nonempty；e : E；r : Real。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.Nonempty.cons_induction`：∀ {α : Type u_3} {motive : (s : Finset α
) → s.Nonempty → Prop},   (∀ (a : α), motive {a} ⋯) →     (∀ (a : α) (s : Finset
 α) (h : a ∉ s) (hs …
· 使用引理 `Finset.sup'`：sup'_one [SemilatticeSup β] (f : α -> β) : sup' 1 one_nonem
pty f = f 1
· 使用引理 `Finset.inf'`：inf'_one [SemilatticeInf β] (f : α -> β) : inf' 1 one_nonem
pty f = f 1
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Finset.cons_nonempty`：cons_nonempty (h : a ∉ s) : (cons a s h).Nonempty
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Finset.sup'_cons`：∀ {α : Type u_2} {β : Type u_3} [inst : SemilatticeSup
 α] {s : Finset β} (H : s.Nonempty) (f : β → α) {b : β}   {hb : b ∉ s}, (Finset.
cons b…
· 使用定理 `Seminorm.ball_sup`：ball_sup (p : Seminorm 𝕜 E) (q : Seminorm 𝕜 E) (e : E
) (r : Real) : ball (p ⊔ q) e r = ball p e r inter ball q e r
· 使用定理 `Finset.inf'_cons`：∀ {α : Type u_2} {β : Type u_3} [inst : SemilatticeInf
 α] {s : Finset β} (H : s.Nonempty) (f : β → α) {b : β}   {hb : b ∉ s}, (Finset.
cons b…
-/
theorem ball_finset_sup' (p : ι → Seminorm 𝕜 E) (s : Finset ι) (H : s.Nonempty) (e : E) (r : ℝ) :
    ball (s.sup' H p) e r = s.inf' H fun i => ball (p i) e r := by
  induction H using Finset.Nonempty.cons_induction with
  | singleton => simp
  | cons _ _ _ hs ih =>
    simp only [Finset.sup'_cons hs, Finset.inf'_cons hs, ball_sup, inf_eq_inter, ih]
/-
**Seminorm.closedBall_finset_sup'** 是 Mathlib 中的一个定理，位于命名空间 `Seminorm`。
形式化陈述：closedBall_finset_sup' (p : ι -> Seminorm 𝕜 E) (s : Finset ι) (H : s.Nonem
pty) (e : E) (r : Real) : closedBall (s.sup' H p) e r = s.inf' H fun i => closed
Ball (p i) e r
参数：p : ι -> Seminorm 𝕜 E；s : Finset ι；H : s.Nonempty；e : E；r : Real。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.Nonempty.cons_induction`：∀ {α : Type u_3} {motive : (s : Finset α
) → s.Nonempty → Prop},   (∀ (a : α), motive {a} ⋯) →     (∀ (a : α) (s : Finset
 α) (h : a ∉ s) (hs …
· 使用引理 `Finset.sup'`：sup'_one [SemilatticeSup β] (f : α -> β) : sup' 1 one_nonem
pty f = f 1
· 使用引理 `Finset.inf'`：inf'_one [SemilatticeInf β] (f : α -> β) : inf' 1 one_nonem
pty f = f 1
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Finset.cons_nonempty`：cons_nonempty (h : a ∉ s) : (cons a s h).Nonempty
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Finset.sup'_cons`：∀ {α : Type u_2} {β : Type u_3} [inst : SemilatticeSup
 α] {s : Finset β} (H : s.Nonempty) (f : β → α) {b : β}   {hb : b ∉ s}, (Finset.
cons b…
· 使用定理 `Seminorm.closedBall_sup`：closedBall_sup (p : Seminorm 𝕜 E) (q : Seminorm
 𝕜 E) (e : E) (r : Real) : closedBall (p ⊔ q) e r = closedBall p e r inter close
dBall q e r
· 使用定理 `Finset.inf'_cons`：∀ {α : Type u_2} {β : Type u_3} [inst : SemilatticeInf
 α] {s : Finset β} (H : s.Nonempty) (f : β → α) {b : β}   {hb : b ∉ s}, (Finset.
cons b…
-/
theorem closedBall_finset_sup' (p : ι → Seminorm 𝕜 E) (s : Finset ι) (H : s.Nonempty) (e : E)
    (r : ℝ) : closedBall (s.sup' H p) e r = s.inf' H fun i => closedBall (p i) e r := by
  induction H using Finset.Nonempty.cons_induction with
  | singleton => simp
  | cons _ _ _ hs ih =>
    simp only [Finset.sup'_cons hs, Finset.inf'_cons hs, closedBall_sup, inf_eq_inter, ih]

@[gcongr]
/-
**Seminorm.ball_mono** 是 Mathlib 中的一个定理，位于命名空间 `Seminorm`。
形式化陈述：ball_mono {p : Seminorm 𝕜 E} {r₁ r₂ : Real} (h : r₁ <= r₂) : p.ball x r₁ s
ubseteq p.ball x r₂
参数：h : r₁ <= r₂。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LT.lt.trans_le`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a < b 
→ b ≤ c → a < c
-/
theorem ball_mono {p : Seminorm 𝕜 E} {r₁ r₂ : ℝ} (h : r₁ ≤ r₂) : p.ball x r₁ ⊆ p.ball x r₂ :=
  fun _ (hx : _ < _) => hx.trans_le h

@[gcongr]
/-
**Seminorm.closedBall_mono** 是 Mathlib 中的一个定理，位于命名空间 `Seminorm`。
形式化陈述：closedBall_mono {p : Seminorm 𝕜 E} {r₁ r₂ : Real} (h : r₁ <= r₂) : p.close
dBall x r₁ subseteq p.closedBall x r₂
参数：h : r₁ <= r₂。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
-/
theorem closedBall_mono {p : Seminorm 𝕜 E} {r₁ r₂ : ℝ} (h : r₁ ≤ r₂) :
    p.closedBall x r₁ ⊆ p.closedBall x r₂ := fun _ (hx : _ ≤ _) => hx.trans h
/-
**Seminorm.ball_antitone** 是 Mathlib 中的一个定理，位于命名空间 `Seminorm`。
形式化陈述：ball_antitone {p q : Seminorm 𝕜 E} (h : q <= p) : p.ball x r subseteq q.ba
ll x r
参数：h : q <= p。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.trans_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b 
→ b < c → a < c
-/
theorem ball_antitone {p q : Seminorm 𝕜 E} (h : q ≤ p) : p.ball x r ⊆ q.ball x r := fun _ =>
  (h _).trans_lt
/-
**Seminorm.closedBall_antitone** 是 Mathlib 中的一个定理，位于命名空间 `Seminorm`。
形式化陈述：closedBall_antitone {p q : Seminorm 𝕜 E} (h : q <= p) : p.closedBall x r s
ubseteq q.closedBall x r
参数：h : q <= p。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
-/
theorem closedBall_antitone {p q : Seminorm 𝕜 E} (h : q ≤ p) :
    p.closedBall x r ⊆ q.closedBall x r := fun _ => (h _).trans
/-
**Seminorm.ball_add_ball_subset** 是 Mathlib 中的一个定理，位于命名空间 `Seminorm`。
形式化陈述：ball_add_ball_subset (p : Seminorm 𝕜 E) (r₁ r₂ : Real) (x₁ x₂ : E) : p.bal
l (x₁ : E) r₁ + p.ball (x₂ : E) r₂ subseteq p.ball (x₁ + x₂) (r₁ + r₂)
参数：p : Seminorm 𝕜 E；r₁ r₂ : Real；x₁ x₂ : E。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Seminorm.mem_ball`：mem_ball : y in ball p x r ↔ p (y - x) < r
· 使用定理 `add_sub_add_comm`：∀ {α : Type u_1} [inst : SubtractionCommMonoid α] (a b
 c d : α), a + b - (c + d) = a - c + (b - d)
· 使用定理 `LE.le.trans_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b 
→ b < c → a < c
· 使用定理 `SubadditiveHomClass.map_add_le_add`：∀ {F : Type u_7} {α : outParam (Type
 u_8)} {β : outParam (Type u_9)} {inst : Add α} {inst_1 : Add β} {inst_2 : LE β}
   {inst_3 : FunLike F α…
· 使用定理 `AddGroupSeminormClass.toSubadditiveHomClass`：∀ {F : Type u_7} {α : outPa
ram (Type u_8)} {β : outParam (Type u_9)} {inst : AddGroup α} {inst_1 : AddCommM
onoid β}   {inst_2 : PartialOrder…
· 使用定理 `SeminormClass.toAddGroupSeminormClass`：∀ {F : Type u_12} {𝕜 : outParam (
Type u_13)} {E : outParam (Type u_14)} {inst : SeminormedRing 𝕜} {inst_1 : AddGr
oup E}   {inst_2 : SMul 𝕜 E…
· 使用定理 `add_lt_add`：∀ {α : Type u_1} [inst : Add α] [inst_1 : Preorder α] [AddLe
ftStrictMono α] [AddRightStrictMono α] {a b c d : α},   a < b → c < d → a + c < 
…
· 使用定理 `IsLeftCancelAdd.addLeftStrictMono_of_addLeftMono`：∀ (N : Type u_2) [inst
 : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftMono N], AddLeft
StrictMono N
· 使用定理 `instIsLeftCancelAddOfAddLeftReflectLE`：∀ {α : Type u_1} [inst : Add α] [
inst_1 : PartialOrder α] [AddLeftReflectLE α], IsLeftCancelAdd α
· 使用定理 `AddGroup.addLeftReflectLE_of_addLeftMono`：∀ {N : Type u_2} [inst : AddGr
oup N] [inst_1 : LE N] [AddLeftMono N], AddLeftReflectLE N
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `IsRightCancelAdd.addRightStrictMono_of_addRightMono`：∀ (N : Type u_2) [i
nst : Add N] [IsRightCancelAdd N] [inst_2 : PartialOrder N] [AddRightMono N], Ad
dRightStrictMono N
· 使用定理 `instIsRightCancelAddOfAddRightReflectLE`：∀ {α : Type u_1} [inst : Add α]
 [inst_1 : PartialOrder α] [AddRightReflectLE α], IsRightCancelAdd α
· 使用定理 `addRightReflectLE_of_addLeftReflectLE`：∀ (N : Type u_2) [inst : AddCommS
emigroup N] [inst_1 : LE N] [AddLeftReflectLE N], AddRightReflectLE N
· 使用定理 `IsLeftCancelAdd.addLeftReflectLE_of_addLeftReflectLT`：∀ (N : Type u_2) [
inst : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftReflectLT N]
, AddLeftReflectLE N
· 使用定理 `AddLeftCancelSemigroup.toIsLeftCancelAdd`：∀ {G : Type u} [self : AddLeft
CancelSemigroup G], IsLeftCancelAdd G
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
-/
theorem ball_add_ball_subset (p : Seminorm 𝕜 E) (r₁ r₂ : ℝ) (x₁ x₂ : E) :
    p.ball (x₁ : E) r₁ + p.ball (x₂ : E) r₂ ⊆ p.ball (x₁ + x₂) (r₁ + r₂) := by
  rintro x ⟨y₁, hy₁, y₂, hy₂, rfl⟩
  rw [mem_ball, add_sub_add_comm]
  exact (map_add_le_add p _ _).trans_lt (add_lt_add hy₁ hy₂)
/-
**Seminorm.closedBall_add_closedBall_subset** 是 Mathlib 中的一个定理，位于命名空间 `Seminorm`
。
形式化陈述：closedBall_add_closedBall_subset (p : Seminorm 𝕜 E) (r₁ r₂ : Real) (x₁ x₂ 
: E) : p.closedBall (x₁ : E) r₁ + p.closedBall (x₂ : E) r₂ subseteq p.closedBall
 (x₁ + x₂) (r₁ + r₂)
参数：p : Seminorm 𝕜 E；r₁ r₂ : Real；x₁ x₂ : E。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Seminorm.mem_closedBall`：mem_closedBall : y in closedBall p x r ↔ p (y -
 x) <= r
· 使用定理 `add_sub_add_comm`：∀ {α : Type u_1} [inst : SubtractionCommMonoid α] (a b
 c d : α), a + b - (c + d) = a - c + (b - d)
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `SubadditiveHomClass.map_add_le_add`：∀ {F : Type u_7} {α : outParam (Type
 u_8)} {β : outParam (Type u_9)} {inst : Add α} {inst_1 : Add β} {inst_2 : LE β}
   {inst_3 : FunLike F α…
· 使用定理 `AddGroupSeminormClass.toSubadditiveHomClass`：∀ {F : Type u_7} {α : outPa
ram (Type u_8)} {β : outParam (Type u_9)} {inst : AddGroup α} {inst_1 : AddCommM
onoid β}   {inst_2 : PartialOrder…
· 使用定理 `SeminormClass.toAddGroupSeminormClass`：∀ {F : Type u_12} {𝕜 : outParam (
Type u_13)} {E : outParam (Type u_14)} {inst : SeminormedRing 𝕜} {inst_1 : AddGr
oup E}   {inst_2 : SMul 𝕜 E…
· 使用定理 `add_le_add`：∀ {α : Type u_1} [inst : Add α] [inst_1 : Preorder α] [AddLe
ftMono α] [AddRightMono α] {a b c d : α},   a ≤ b → c ≤ d → a + c ≤ b + d
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
-/
theorem closedBall_add_closedBall_subset (p : Seminorm 𝕜 E) (r₁ r₂ : ℝ) (x₁ x₂ : E) :
    p.closedBall (x₁ : E) r₁ + p.closedBall (x₂ : E) r₂ ⊆ p.closedBall (x₁ + x₂) (r₁ + r₂) := by
  rintro x ⟨y₁, hy₁, y₂, hy₂, rfl⟩
  rw [mem_closedBall, add_sub_add_comm]
  exact (map_add_le_add p _ _).trans (add_le_add hy₁ hy₂)
/-
**Seminorm.sub_mem_ball** 是 Mathlib 中的一个定理，位于命名空间 `Seminorm`。
形式化陈述：sub_mem_ball (p : Seminorm 𝕜 E) (x₁ x₂ y : E) (r : Real) : x₁ - x₂ in p.ba
ll y r ↔ x₁ in p.ball (x₂ + y) r
参数：p : Seminorm 𝕜 E；x₁ x₂ y : E；r : Real。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `sub_sub`：∀ {α : Type u_1} [inst : SubtractionCommMonoid α] (a b c : α), 
a - b - c = a - (b + c)
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem sub_mem_ball (p : Seminorm 𝕜 E) (x₁ x₂ y : E) (r : ℝ) :
    x₁ - x₂ ∈ p.ball y r ↔ x₁ ∈ p.ball (x₂ + y) r := by simp_rw [mem_ball, sub_sub]
/-
**Seminorm.sub_mem_closedBall** 是 Mathlib 中的一个定理，位于命名空间 `Seminorm`。
形式化陈述：sub_mem_closedBall (p : Seminorm 𝕜 E) (x₁ x₂ y : E) (r : Real) : x₁ - x₂ i
n p.closedBall y r ↔ x₁ in p.closedBall (x₂ + y) r
参数：p : Seminorm 𝕜 E；x₁ x₂ y : E；r : Real。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `sub_sub`：∀ {α : Type u_1} [inst : SubtractionCommMonoid α] (a b c : α), 
a - b - c = a - (b + c)
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem sub_mem_closedBall (p : Seminorm 𝕜 E) (x₁ x₂ y : E) (r : ℝ) :
    x₁ - x₂ ∈ p.closedBall y r ↔ x₁ ∈ p.closedBall (x₂ + y) r := by
  simp_rw [mem_closedBall, sub_sub]
/-
**Seminorm.ball_eq_metric** 是 Mathlib 中的一个引理，位于命名空间 `Seminorm`。
形式化陈述：ball_eq_metric : letI
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma ball_eq_metric :
    letI := AddGroupSeminorm.toSeminormedAddCommGroup p.toAddGroupSeminorm
    p.ball x r = Metric.ball x r := by
  ext
  simp only [mem_ball_iff_norm]
  rfl
/-
**Seminorm.closedBall_eq_metric** 是 Mathlib 中的一个引理，位于命名空间 `Seminorm`。
形式化陈述：closedBall_eq_metric : letI
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma closedBall_eq_metric :
    letI := AddGroupSeminorm.toSeminormedAddCommGroup p.toAddGroupSeminorm
    p.closedBall x r = Metric.closedBall x r := by
  ext
  simp only [mem_closedBall_iff_norm]
  rfl

/-- The image of a ball under addition with a singleton is another ball. -/
/-
**Seminorm.vadd_ball** 是 Mathlib 中的一个定理，位于命名空间 `Seminorm`。
形式化陈述：vadd_ball (p : Seminorm 𝕜 E) : x +ᵥ p.ball y r = p.ball (x +ᵥ y) r
参数：p : Seminorm 𝕜 E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Seminorm.ball_eq_metric`：ball_eq_metric : letI
· 使用定理 `Metric.vadd_ball`：∀ {G : Type v} {X : Type w} [inst : PseudoMetricSpace 
X] [inst_1 : AddGroup G] [inst_2 : AddAction G X]   [IsIsometricVAdd G X] (c : G
) (x :…
· 使用定理 `NormedAddGroup.to_isIsometricVAdd`：∀ {E : Type u_2} [inst : SeminormedAd
dGroup E], IsIsometricVAdd E E
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
The image of a ball under addition with a singleton is another ball.
-/
theorem vadd_ball (p : Seminorm 𝕜 E) : x +ᵥ p.ball y r = p.ball (x +ᵥ y) r := by
  let := AddGroupSeminorm.toSeminormedAddCommGroup p.toAddGroupSeminorm
  simp [ball_eq_metric]

/-- The image of a closed ball under addition with a singleton is another closed ball. -/
/-
**Seminorm.vadd_closedBall** 是 Mathlib 中的一个定理，位于命名空间 `Seminorm`。
形式化陈述：vadd_closedBall (p : Seminorm 𝕜 E) : x +ᵥ p.closedBall y r = p.closedBall 
(x +ᵥ y) r
参数：p : Seminorm 𝕜 E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Seminorm.closedBall_eq_metric`：closedBall_eq_metric : letI
· 使用定理 `Metric.vadd_closedBall`：∀ {G : Type v} {X : Type w} [inst : PseudoMetric
Space X] [inst_1 : AddGroup G] [inst_2 : AddAction G X]   [IsIsometricVAdd G X] 
(c : G) (x :…
· 使用定理 `NormedAddGroup.to_isIsometricVAdd`：∀ {E : Type u_2} [inst : SeminormedAd
dGroup E], IsIsometricVAdd E E
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
The image of a closed ball under addition with a singleton is another closed bal
l.
-/
theorem vadd_closedBall (p : Seminorm 𝕜 E) : x +ᵥ p.closedBall y r = p.closedBall (x +ᵥ y) r := by
  let := AddGroupSeminorm.toSeminormedAddCommGroup p.toAddGroupSeminorm
  simp [closedBall_eq_metric]

end SMul

section Module

variable [Module 𝕜 E]
variable [SeminormedRing 𝕜₂] [AddCommGroup E₂] [Module 𝕜₂ E₂]
variable {σ₁₂ : 𝕜 →+* 𝕜₂} [RingHomIsometric σ₁₂]

/-
**Seminorm.ball_comp** 是 Mathlib 中的一个定理，位于命名空间 `Seminorm`。
形式化陈述：ball_comp (p : Seminorm 𝕜₂ E₂) (f : E ->ₛₗ[σ₁₂] E₂) (x : E) (r : Real) : (
p.comp f).ball x r = f ⁻¹' p.ball (f x) r
参数：p : Seminorm 𝕜₂ E₂；f : E ->ₛₗ[σ₁₂] E₂；x : E；r : Real。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `map_sub`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLike 
F G H] [inst_1 : AddGroup G]   [inst_2 : SubtractionMonoid H] [AddMonoidHomCl…
· 使用定理 `DistribMulActionSemiHomClass.toAddMonoidHomClass`：∀ {F : Type u_10} {M :
 outParam (Type u_11)} {N : outParam (Type u_12)} {φ : outParam (M → N)}   {A : 
outParam (Type u_13)} {B : outParam (T…
· 使用定理 `SemilinearMapClass.distribMulActionSemiHomClass`：∀ {R : Type u_1} {S : T
ype u_5} {M : Type u_8} {M₃ : Type u_11} (F : Type u_14) [inst : Semiring R]   [
inst_1 : Semiring S] [inst_2 : AddCom…
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem ball_comp (p : Seminorm 𝕜₂ E₂) (f : E →ₛₗ[σ₁₂] E₂) (x : E) (r : ℝ) :
    (p.comp f).ball x r = f ⁻¹' p.ball (f x) r := by
  ext
  simp_rw [ball, mem_preimage, comp_apply, Set.mem_ofPred_eq, map_sub]
/-
**Seminorm.closedBall_comp** 是 Mathlib 中的一个定理，位于命名空间 `Seminorm`。
形式化陈述：closedBall_comp (p : Seminorm 𝕜₂ E₂) (f : E ->ₛₗ[σ₁₂] E₂) (x : E) (r : Rea
l) : (p.comp f).closedBall x r = f ⁻¹' p.closedBall (f x) r
参数：p : Seminorm 𝕜₂ E₂；f : E ->ₛₗ[σ₁₂] E₂；x : E；r : Real。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `map_sub`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLike 
F G H] [inst_1 : AddGroup G]   [inst_2 : SubtractionMonoid H] [AddMonoidHomCl…
· 使用定理 `DistribMulActionSemiHomClass.toAddMonoidHomClass`：∀ {F : Type u_10} {M :
 outParam (Type u_11)} {N : outParam (Type u_12)} {φ : outParam (M → N)}   {A : 
outParam (Type u_13)} {B : outParam (T…
· 使用定理 `SemilinearMapClass.distribMulActionSemiHomClass`：∀ {R : Type u_1} {S : T
ype u_5} {M : Type u_8} {M₃ : Type u_11} (F : Type u_14) [inst : Semiring R]   [
inst_1 : Semiring S] [inst_2 : AddCom…
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem closedBall_comp (p : Seminorm 𝕜₂ E₂) (f : E →ₛₗ[σ₁₂] E₂) (x : E) (r : ℝ) :
    (p.comp f).closedBall x r = f ⁻¹' p.closedBall (f x) r := by
  ext
  simp_rw [closedBall, mem_preimage, comp_apply, Set.mem_ofPred_eq, map_sub]

variable (p : Seminorm 𝕜 E)
/-
**Seminorm.preimage_metric_ball** 是 Mathlib 中的一个定理，位于命名空间 `Seminorm`。
形式化陈述：preimage_metric_ball {r : Real} : p ⁻¹' Metric.ball 0 r = { x | p x < r }
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
· 使用定理 `Real.norm_of_nonneg`：norm_of_nonneg (hr : 0 <= r) : ‖r‖ = r
· 使用定理 `NonnegHomClass.apply_nonneg`：∀ {F : Type u_7} {α : outParam (Type u_8)} 
{β : outParam (Type u_9)} {inst : Zero β} {inst_1 : LE β}   {inst_2 : FunLike F 
α β} [self : Nonn…
· 使用定理 `AddGroupSeminormClass.toNonnegHomClass`：∀ {F : Type u_2} {α : Type u_3} 
{β : Type u_4} [inst : FunLike F α β] [inst_1 : AddGroup α] [inst_2 : AddCommMon
oid β]   [inst_3 : LinearOrd…
· 使用定理 `SeminormClass.toAddGroupSeminormClass`：∀ {F : Type u_12} {𝕜 : outParam (
Type u_13)} {E : outParam (Type u_14)} {inst : SeminormedRing 𝕜} {inst_1 : AddGr
oup E}   {inst_2 : SMul 𝕜 E…
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem preimage_metric_ball {r : ℝ} : p ⁻¹' Metric.ball 0 r = { x | p x < r } := by
  ext x
  simp only [mem_ofPred, mem_preimage, mem_ball_zero_iff, Real.norm_of_nonneg (apply_nonneg p _)]
/-
**Seminorm.preimage_metric_closedBall** 是 Mathlib 中的一个定理，位于命名空间 `Seminorm`。
形式化陈述：preimage_metric_closedBall {r : Real} : p ⁻¹' Metric.closedBall 0 r = { x 
| p x <= r }
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
· 使用定理 `Real.norm_of_nonneg`：norm_of_nonneg (hr : 0 <= r) : ‖r‖ = r
· 使用定理 `NonnegHomClass.apply_nonneg`：∀ {F : Type u_7} {α : outParam (Type u_8)} 
{β : outParam (Type u_9)} {inst : Zero β} {inst_1 : LE β}   {inst_2 : FunLike F 
α β} [self : Nonn…
· 使用定理 `AddGroupSeminormClass.toNonnegHomClass`：∀ {F : Type u_2} {α : Type u_3} 
{β : Type u_4} [inst : FunLike F α β] [inst_1 : AddGroup α] [inst_2 : AddCommMon
oid β]   [inst_3 : LinearOrd…
· 使用定理 `SeminormClass.toAddGroupSeminormClass`：∀ {F : Type u_12} {𝕜 : outParam (
Type u_13)} {E : outParam (Type u_14)} {inst : SeminormedRing 𝕜} {inst_1 : AddGr
oup E}   {inst_2 : SMul 𝕜 E…
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem preimage_metric_closedBall {r : ℝ} : p ⁻¹' Metric.closedBall 0 r = { x | p x ≤ r } := by
  ext x
  simp only [mem_ofPred, mem_preimage, mem_closedBall_zero_iff,
    Real.norm_of_nonneg (apply_nonneg p _)]
/-
**Seminorm.ball_zero_eq_preimage_ball** 是 Mathlib 中的一个定理，位于命名空间 `Seminorm`。
形式化陈述：ball_zero_eq_preimage_ball {r : Real} : p.ball 0 r = p ⁻¹' Metric.ball 0 r
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Seminorm.ball_zero_eq`：ball_zero_eq : ball p 0 r = { y : E | p y < r }
· 使用定理 `Seminorm.preimage_metric_ball`：preimage_metric_ball {r : Real} : p ⁻¹' M
etric.ball 0 r = { x | p x < r }
-/
theorem ball_zero_eq_preimage_ball {r : ℝ} : p.ball 0 r = p ⁻¹' Metric.ball 0 r := by
  rw [ball_zero_eq, preimage_metric_ball]
/-
**Seminorm.closedBall_zero_eq_preimage_closedBall** 是 Mathlib 中的一个定理，位于命名空间 `Sem
inorm`。
形式化陈述：closedBall_zero_eq_preimage_closedBall {r : Real} : p.closedBall 0 r = p ⁻
¹' Metric.closedBall 0 r
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Seminorm.closedBall_zero_eq`：closedBall_zero_eq : closedBall p 0 r = { y
 : E | p y <= r }
· 使用定理 `Seminorm.preimage_metric_closedBall`：preimage_metric_closedBall {r : Rea
l} : p ⁻¹' Metric.closedBall 0 r = { x | p x <= r }
-/
theorem closedBall_zero_eq_preimage_closedBall {r : ℝ} :
    p.closedBall 0 r = p ⁻¹' Metric.closedBall 0 r := by
  rw [closedBall_zero_eq, preimage_metric_closedBall]

@[simp]
/-
**Seminorm.ball_bot** 是 Mathlib 中的一个定理，位于命名空间 `Seminorm`。
形式化陈述：ball_bot {r : Real} (x : E) (hr : 0 < r) : ball (⊥ : Seminorm 𝕜 E) x r = S
et.univ
参数：x : E；hr : 0 < r。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Seminorm.ball_zero'`：ball_zero' (x : E) (hr : 0 < r) : ball (0 : Seminor
m 𝕜 E) x r = Set.univ
-/
theorem ball_bot {r : ℝ} (x : E) (hr : 0 < r) : ball (⊥ : Seminorm 𝕜 E) x r = Set.univ :=
  ball_zero' x hr

@[simp]
/-
**Seminorm.closedBall_bot** 是 Mathlib 中的一个定理，位于命名空间 `Seminorm`。
形式化陈述：closedBall_bot {r : Real} (x : E) (hr : 0 < r) : closedBall (⊥ : Seminorm 
𝕜 E) x r = Set.univ
参数：x : E；hr : 0 < r。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Seminorm.closedBall_zero'`：closedBall_zero' (x : E) (hr : 0 < r) : close
dBall (0 : Seminorm 𝕜 E) x r = Set.univ
-/
theorem closedBall_bot {r : ℝ} (x : E) (hr : 0 < r) :
    closedBall (⊥ : Seminorm 𝕜 E) x r = Set.univ :=
  closedBall_zero' x hr

/-- Seminorm-balls at the origin are balanced. -/
/-
**Seminorm.balanced_ball_zero** 是 Mathlib 中的一个定理，位于命名空间 `Seminorm`。
形式化陈述：balanced_ball_zero (r : Real) : Balanced 𝕜 (ball p 0 r)
参数：r : Real。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Seminorm.mem_ball_zero`：mem_ball_zero : y in ball p 0 r ↔ p y < r
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `SeminormClass.map_smul_eq_mul`：∀ {F : Type u_12} {𝕜 : outParam (Type u_1
3)} {E : outParam (Type u_14)} {inst : SeminormedRing 𝕜} {inst_1 : AddGroup E}  
 {inst_2 : SMul 𝕜 E…
· 使用定理 `mul_le_of_le_one_left`：mul_le_of_le_one_left [MulPosMono α] (hb : 0 <= b
) (h : a <= 1) : a * b <= b
· 使用定理 `IsOrderedRing.toMulPosMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], MulPosMono R
· 使用定理 `NonnegHomClass.apply_nonneg`：∀ {F : Type u_7} {α : outParam (Type u_8)} 
{β : outParam (Type u_9)} {inst : Zero β} {inst_1 : LE β}   {inst_2 : FunLike F 
α β} [self : Nonn…
· 使用定理 `AddGroupSeminormClass.toNonnegHomClass`：∀ {F : Type u_2} {α : Type u_3} 
{β : Type u_4} [inst : FunLike F α β] [inst_1 : AddGroup α] [inst_2 : AddCommMon
oid β]   [inst_3 : LinearOrd…
· 使用定理 `SeminormClass.toAddGroupSeminormClass`：∀ {F : Type u_12} {𝕜 : outParam (
Type u_13)} {E : outParam (Type u_14)} {inst : SeminormedRing 𝕜} {inst_1 : AddGr
oup E}   {inst_2 : SMul 𝕜 E…

--- 原说明 ---
Seminorm-balls at the origin are balanced.
-/
theorem balanced_ball_zero (r : ℝ) : Balanced 𝕜 (ball p 0 r) := by
  rintro a ha x ⟨y, hy, hx⟩
  rw [mem_ball_zero, ← hx, map_smul_eq_mul]
  calc
    _ ≤ p y := mul_le_of_le_one_left (apply_nonneg p _) ha
    _ < r := by rwa [mem_ball_zero] at hy

/-- Closed seminorm-balls at the origin are balanced. -/
/-
**Seminorm.balanced_closedBall_zero** 是 Mathlib 中的一个定理，位于命名空间 `Seminorm`。
形式化陈述：balanced_closedBall_zero (r : Real) : Balanced 𝕜 (closedBall p 0 r)
参数：r : Real。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Seminorm.mem_closedBall_zero`：mem_closedBall_zero : y in closedBall p 0 
r ↔ p y <= r
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `SeminormClass.map_smul_eq_mul`：∀ {F : Type u_12} {𝕜 : outParam (Type u_1
3)} {E : outParam (Type u_14)} {inst : SeminormedRing 𝕜} {inst_1 : AddGroup E}  
 {inst_2 : SMul 𝕜 E…
· 使用定理 `mul_le_of_le_one_left`：mul_le_of_le_one_left [MulPosMono α] (hb : 0 <= b
) (h : a <= 1) : a * b <= b
· 使用定理 `IsOrderedRing.toMulPosMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], MulPosMono R
· 使用定理 `NonnegHomClass.apply_nonneg`：∀ {F : Type u_7} {α : outParam (Type u_8)} 
{β : outParam (Type u_9)} {inst : Zero β} {inst_1 : LE β}   {inst_2 : FunLike F 
α β} [self : Nonn…
· 使用定理 `AddGroupSeminormClass.toNonnegHomClass`：∀ {F : Type u_2} {α : Type u_3} 
{β : Type u_4} [inst : FunLike F α β] [inst_1 : AddGroup α] [inst_2 : AddCommMon
oid β]   [inst_3 : LinearOrd…
· 使用定理 `SeminormClass.toAddGroupSeminormClass`：∀ {F : Type u_12} {𝕜 : outParam (
Type u_13)} {E : outParam (Type u_14)} {inst : SeminormedRing 𝕜} {inst_1 : AddGr
oup E}   {inst_2 : SMul 𝕜 E…

--- 原说明 ---
Closed seminorm-balls at the origin are balanced.
-/
theorem balanced_closedBall_zero (r : ℝ) : Balanced 𝕜 (closedBall p 0 r) := by
  rintro a ha x ⟨y, hy, hx⟩
  rw [mem_closedBall_zero, ← hx, map_smul_eq_mul]
  calc
    _ ≤ p y := mul_le_of_le_one_left (apply_nonneg p _) ha
    _ ≤ r := by rwa [mem_closedBall_zero] at hy
/-
**Seminorm.ball_finset_sup_eq_iInter** 是 Mathlib 中的一个定理，位于命名空间 `Seminorm`。
形式化陈述：ball_finset_sup_eq_iInter (p : ι -> Seminorm 𝕜 E) (s : Finset ι) (x : E) {
r : Real} (hr : 0 < r) : ball (s.sup p) x r = ⋂ i in s, ball (p i) x r
参数：p : ι -> Seminorm 𝕜 E；s : Finset ι；x : E；hr : 0 < r。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CanLift.prf`：∀ {α : Sort u_1} {β : Sort u_2} {coe : outParam (β → α)} {c
ond : outParam (α → Prop)} [self : CanLift α β coe cond]   (x : α), cond x → ∃ y
,…
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Set.iInter_ofPred`：iInter_ofPred (P : ι -> α -> Prop) : ⋂ i, { x : α | P
 i x } = { x : α | forall i, P i x }
· 使用定理 `NonnegHomClass.apply_nonneg`：∀ {F : Type u_7} {α : outParam (Type u_8)} 
{β : outParam (Type u_9)} {inst : Zero β} {inst_1 : LE β}   {inst_2 : FunLike F 
α β} [self : Nonn…
· 使用定理 `AddGroupSeminormClass.toNonnegHomClass`：∀ {F : Type u_2} {α : Type u_3} 
{β : Type u_4} [inst : FunLike F α β] [inst_1 : AddGroup α] [inst_2 : AddCommMon
oid β]   [inst_3 : LinearOrd…
· 使用定理 `SeminormClass.toAddGroupSeminormClass`：∀ {F : Type u_12} {𝕜 : outParam (
Type u_13)} {E : outParam (Type u_14)} {inst : SeminormedRing 𝕜} {inst_1 : AddGr
oup E}   {inst_2 : SMul 𝕜 E…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Seminorm.finset_sup_apply`：finset_sup_apply (p : ι -> Seminorm 𝕜 E) (s :
 Finset ι) (x : E) : s.sup p x = ↑(s.sup fun i => NNReal.mk (p i x) (apply_nonne
g (p i) x))
· 使用定理 `Finset.sup_lt_iff`：∀ {α : Type u_2} {ι : Type u_5} [inst : LinearOrder α
] [inst_1 : OrderBot α] {s : Finset ι} {f : ι → α} {a : α},   ⊥ < a → (s.sup f <
 a ↔ ∀ …
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem ball_finset_sup_eq_iInter (p : ι → Seminorm 𝕜 E) (s : Finset ι) (x : E) {r : ℝ}
    (hr : 0 < r) : ball (s.sup p) x r = ⋂ i ∈ s, ball (p i) x r := by
  lift r to NNReal using hr.le
  simp_rw [ball, iInter_ofPred, finset_sup_apply, NNReal.coe_lt_coe,
    Finset.sup_lt_iff (show ⊥ < r from hr), ← NNReal.coe_lt_coe, NNReal.coe_mk]
/-
**Seminorm.closedBall_finset_sup_eq_iInter** 是 Mathlib 中的一个定理，位于命名空间 `Seminorm`。
形式化陈述：closedBall_finset_sup_eq_iInter (p : ι -> Seminorm 𝕜 E) (s : Finset ι) (x 
: E) {r : Real} (hr : 0 <= r) : closedBall (s.sup p) x r = ⋂ i in s, closedBall 
(p i) x r
参数：p : ι -> Seminorm 𝕜 E；s : Finset ι；x : E；hr : 0 <= r。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CanLift.prf`：∀ {α : Sort u_1} {β : Sort u_2} {coe : outParam (β → α)} {c
ond : outParam (α → Prop)} [self : CanLift α β coe cond]   (x : α), cond x → ∃ y
,…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Set.iInter_ofPred`：iInter_ofPred (P : ι -> α -> Prop) : ⋂ i, { x : α | P
 i x } = { x : α | forall i, P i x }
· 使用定理 `NonnegHomClass.apply_nonneg`：∀ {F : Type u_7} {α : outParam (Type u_8)} 
{β : outParam (Type u_9)} {inst : Zero β} {inst_1 : LE β}   {inst_2 : FunLike F 
α β} [self : Nonn…
· 使用定理 `AddGroupSeminormClass.toNonnegHomClass`：∀ {F : Type u_2} {α : Type u_3} 
{β : Type u_4} [inst : FunLike F α β] [inst_1 : AddGroup α] [inst_2 : AddCommMon
oid β]   [inst_3 : LinearOrd…
· 使用定理 `SeminormClass.toAddGroupSeminormClass`：∀ {F : Type u_12} {𝕜 : outParam (
Type u_13)} {E : outParam (Type u_14)} {inst : SeminormedRing 𝕜} {inst_1 : AddGr
oup E}   {inst_2 : SMul 𝕜 E…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Seminorm.finset_sup_apply`：finset_sup_apply (p : ι -> Seminorm 𝕜 E) (s :
 Finset ι) (x : E) : s.sup p x = ↑(s.sup fun i => NNReal.mk (p i x) (apply_nonne
g (p i) x))
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem closedBall_finset_sup_eq_iInter (p : ι → Seminorm 𝕜 E) (s : Finset ι) (x : E) {r : ℝ}
    (hr : 0 ≤ r) : closedBall (s.sup p) x r = ⋂ i ∈ s, closedBall (p i) x r := by
  lift r to NNReal using hr
  simp_rw [closedBall, iInter_ofPred, finset_sup_apply, NNReal.coe_le_coe, Finset.sup_le_iff, ←
    NNReal.coe_le_coe, NNReal.coe_mk]
/-
**Seminorm.ball_finset_sup** 是 Mathlib 中的一个定理，位于命名空间 `Seminorm`。
形式化陈述：ball_finset_sup (p : ι -> Seminorm 𝕜 E) (s : Finset ι) (x : E) {r : Real} 
(hr : 0 < r) : ball (s.sup p) x r = s.inf fun i => ball (p i) x r
参数：p : ι -> Seminorm 𝕜 E；s : Finset ι；x : E；hr : 0 < r。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.inf_eq_iInf`：∀ {α : Type u_2} {β : Type u_3} [inst : CompleteLatt
ice β] (s : Finset α) (f : α → β), s.inf f = ⨅ a ∈ s, f a
· 使用定理 `Seminorm.ball_finset_sup_eq_iInter`：ball_finset_sup_eq_iInter (p : ι -> 
Seminorm 𝕜 E) (s : Finset ι) (x : E) {r : Real} (hr : 0 < r) : ball (s.sup p) x 
r = ⋂ i in s, ball (p i)…
-/
theorem ball_finset_sup (p : ι → Seminorm 𝕜 E) (s : Finset ι) (x : E) {r : ℝ} (hr : 0 < r) :
    ball (s.sup p) x r = s.inf fun i => ball (p i) x r := by
  rw [Finset.inf_eq_iInf]
  exact ball_finset_sup_eq_iInter _ _ _ hr
/-
**Seminorm.closedBall_finset_sup** 是 Mathlib 中的一个定理，位于命名空间 `Seminorm`。
形式化陈述：closedBall_finset_sup (p : ι -> Seminorm 𝕜 E) (s : Finset ι) (x : E) {r : 
Real} (hr : 0 <= r) : closedBall (s.sup p) x r = s.inf fun i => closedBall (p i)
 x r
参数：p : ι -> Seminorm 𝕜 E；s : Finset ι；x : E；hr : 0 <= r。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.inf_eq_iInf`：∀ {α : Type u_2} {β : Type u_3} [inst : CompleteLatt
ice β] (s : Finset α) (f : α → β), s.inf f = ⨅ a ∈ s, f a
· 使用定理 `Seminorm.closedBall_finset_sup_eq_iInter`：closedBall_finset_sup_eq_iInte
r (p : ι -> Seminorm 𝕜 E) (s : Finset ι) (x : E) {r : Real} (hr : 0 <= r) : clos
edBall (s.sup p) x r = ⋂ i in …
-/
theorem closedBall_finset_sup (p : ι → Seminorm 𝕜 E) (s : Finset ι) (x : E) {r : ℝ} (hr : 0 ≤ r) :
    closedBall (s.sup p) x r = s.inf fun i => closedBall (p i) x r := by
  rw [Finset.inf_eq_iInf]
  exact closedBall_finset_sup_eq_iInter _ _ _ hr

@[simp]
/-
**Seminorm.ball_eq_emptyset** 是 Mathlib 中的一个定理，位于命名空间 `Seminorm`。
形式化陈述：ball_eq_emptyset (p : Seminorm 𝕜 E) {x : E} {r : Real} (hr : r <= 0) : p.b
all x r = ∅
参数：p : Seminorm 𝕜 E；hr : r <= 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Seminorm.mem_ball`：mem_ball : y in ball p x r ↔ p (y - x) < r
· 使用定理 `Set.mem_empty_iff_false`：mem_empty_iff_false (x : α) : x in (∅ : Set α) 
↔ False
· 使用定理 `iff_false`：∀ (p : Prop), (p ↔ False) = ¬p
· 使用定理 `not_lt`：∀ {α : Type u_1} [inst : LinearOrder α] {a b : α}, ¬a < b ↔ b ≤ 
a
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `NonnegHomClass.apply_nonneg`：∀ {F : Type u_7} {α : outParam (Type u_8)} 
{β : outParam (Type u_9)} {inst : Zero β} {inst_1 : LE β}   {inst_2 : FunLike F 
α β} [self : Nonn…
· 使用定理 `AddGroupSeminormClass.toNonnegHomClass`：∀ {F : Type u_2} {α : Type u_3} 
{β : Type u_4} [inst : FunLike F α β] [inst_1 : AddGroup α] [inst_2 : AddCommMon
oid β]   [inst_3 : LinearOrd…
· 使用定理 `SeminormClass.toAddGroupSeminormClass`：∀ {F : Type u_12} {𝕜 : outParam (
Type u_13)} {E : outParam (Type u_14)} {inst : SeminormedRing 𝕜} {inst_1 : AddGr
oup E}   {inst_2 : SMul 𝕜 E…
-/
theorem ball_eq_emptyset (p : Seminorm 𝕜 E) {x : E} {r : ℝ} (hr : r ≤ 0) : p.ball x r = ∅ := by
  ext
  rw [Seminorm.mem_ball, Set.mem_empty_iff_false, iff_false, not_lt]
  exact hr.trans (apply_nonneg p _)

@[simp]
/-
**Seminorm.closedBall_eq_emptyset** 是 Mathlib 中的一个定理，位于命名空间 `Seminorm`。
形式化陈述：closedBall_eq_emptyset (p : Seminorm 𝕜 E) {x : E} {r : Real} (hr : r < 0) 
: p.closedBall x r = ∅
参数：p : Seminorm 𝕜 E；hr : r < 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Seminorm.mem_closedBall`：mem_closedBall : y in closedBall p x r ↔ p (y -
 x) <= r
· 使用定理 `Set.mem_empty_iff_false`：mem_empty_iff_false (x : α) : x in (∅ : Set α) 
↔ False
· 使用定理 `iff_false`：∀ (p : Prop), (p ↔ False) = ¬p
· 使用定理 `not_le`：∀ {α : Type u_1} [inst : LinearOrder α] {a b : α}, ¬a ≤ b ↔ b < 
a
· 使用定理 `LT.lt.trans_le`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a < b 
→ b ≤ c → a < c
· 使用定理 `NonnegHomClass.apply_nonneg`：∀ {F : Type u_7} {α : outParam (Type u_8)} 
{β : outParam (Type u_9)} {inst : Zero β} {inst_1 : LE β}   {inst_2 : FunLike F 
α β} [self : Nonn…
· 使用定理 `AddGroupSeminormClass.toNonnegHomClass`：∀ {F : Type u_2} {α : Type u_3} 
{β : Type u_4} [inst : FunLike F α β] [inst_1 : AddGroup α] [inst_2 : AddCommMon
oid β]   [inst_3 : LinearOrd…
· 使用定理 `SeminormClass.toAddGroupSeminormClass`：∀ {F : Type u_12} {𝕜 : outParam (
Type u_13)} {E : outParam (Type u_14)} {inst : SeminormedRing 𝕜} {inst_1 : AddGr
oup E}   {inst_2 : SMul 𝕜 E…
-/
theorem closedBall_eq_emptyset (p : Seminorm 𝕜 E) {x : E} {r : ℝ} (hr : r < 0) :
    p.closedBall x r = ∅ := by
  ext
  rw [Seminorm.mem_closedBall, Set.mem_empty_iff_false, iff_false, not_le]
  exact hr.trans_le (apply_nonneg _ _)
/-
**Seminorm.closedBall_smul_ball** 是 Mathlib 中的一个定理，位于命名空间 `Seminorm`。
形式化陈述：closedBall_smul_ball (p : Seminorm 𝕜 E) {r₁ : Real} (hr₁ : r₁ != 0) (r₂ : 
Real) : Metric.closedBall (0 : 𝕜) r₁ • p.ball 0 r₂ subseteq p.ball 0 (r₁ * r₂)
参数：p : Seminorm 𝕜 E；hr₁ : r₁ != 0；r₂ : Real。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `SeminormClass.map_smul_eq_mul`：∀ {F : Type u_12} {𝕜 : outParam (Type u_1
3)} {E : outParam (Type u_14)} {inst : SeminormedRing 𝕜} {inst_1 : AddGroup E}  
 {inst_2 : SMul 𝕜 E…
· 使用定理 `mul_lt_mul'`：∀ {α : Type u_1} [inst : Mul α] [inst_1 : Zero α] [inst_2 :
 Preorder α] {a b c d : α} [PosMulStrictMono α]   [MulPosMono α], a ≤ b → c < d 
→…
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `IsOrderedRing.toMulPosMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], MulPosMono R
· 使用定理 `NonnegHomClass.apply_nonneg`：∀ {F : Type u_7} {α : outParam (Type u_8)} 
{β : outParam (Type u_9)} {inst : Zero β} {inst_1 : LE β}   {inst_2 : FunLike F 
α β} [self : Nonn…
· 使用定理 `AddGroupSeminormClass.toNonnegHomClass`：∀ {F : Type u_2} {α : Type u_3} 
{β : Type u_4} [inst : FunLike F α β] [inst_1 : AddGroup α] [inst_2 : AddCommMon
oid β]   [inst_3 : LinearOrd…
· 使用定理 `SeminormClass.toAddGroupSeminormClass`：∀ {F : Type u_12} {𝕜 : outParam (
Type u_13)} {E : outParam (Type u_14)} {inst : SeminormedRing 𝕜} {inst_1 : AddGr
oup E}   {inst_2 : SMul 𝕜 E…
· 使用定理 `Or.resolve_left`：∀ {a b : Prop}, a ∨ b → ¬a → b
· 使用定理 `Ne.lt_or_gt`：Ne.lt_or_gt (h : a != b) : a < b ∨ b < a
· 使用定理 `LE.le.not_gt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a ≤ b → ¬b
 < a
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `norm_nonneg`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (a : E), 0 ≤
 ‖a‖
-/
theorem closedBall_smul_ball (p : Seminorm 𝕜 E) {r₁ : ℝ} (hr₁ : r₁ ≠ 0) (r₂ : ℝ) :
    Metric.closedBall (0 : 𝕜) r₁ • p.ball 0 r₂ ⊆ p.ball 0 (r₁ * r₂) := by
  simp only [smul_subset_iff, mem_ball_zero, mem_closedBall_zero_iff, map_smul_eq_mul]
  refine fun a ha b hb ↦ mul_lt_mul' ha hb (apply_nonneg _ _) ?_
  exact hr₁.lt_or_gt.resolve_left <| ((norm_nonneg a).trans ha).not_gt
/-
**Seminorm.ball_smul_closedBall** 是 Mathlib 中的一个定理，位于命名空间 `Seminorm`。
形式化陈述：ball_smul_closedBall (p : Seminorm 𝕜 E) (r₁ : Real) {r₂ : Real} (hr₂ : r₂ 
!= 0) : Metric.ball (0 : 𝕜) r₁ • p.closedBall 0 r₂ subseteq p.ball 0 (r₁ * r₂)
参数：p : Seminorm 𝕜 E；r₁ : Real；hr₂ : r₂ != 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `SeminormClass.map_smul_eq_mul`：∀ {F : Type u_12} {𝕜 : outParam (Type u_1
3)} {E : outParam (Type u_14)} {inst : SeminormedRing 𝕜} {inst_1 : AddGroup E}  
 {inst_2 : SMul 𝕜 E…
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `mul_lt_mul'`：∀ {α : Type u_1} [inst : Mul α] [inst_1 : Zero α] [inst_2 :
 Preorder α] {a b c d : α} [PosMulStrictMono α]   [MulPosMono α], a ≤ b → c < d 
→…
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `IsOrderedRing.toMulPosMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], MulPosMono R
· 使用定理 `norm_nonneg`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (a : E), 0 ≤
 ‖a‖
· 使用定理 `Or.resolve_left`：∀ {a b : Prop}, a ∨ b → ¬a → b
· 使用定理 `Ne.lt_or_gt`：Ne.lt_or_gt (h : a != b) : a < b ∨ b < a
· 使用定理 `LE.le.not_gt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a ≤ b → ¬b
 < a
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `NonnegHomClass.apply_nonneg`：∀ {F : Type u_7} {α : outParam (Type u_8)} 
{β : outParam (Type u_9)} {inst : Zero β} {inst_1 : LE β}   {inst_2 : FunLike F 
α β} [self : Nonn…
· 使用定理 `AddGroupSeminormClass.toNonnegHomClass`：∀ {F : Type u_2} {α : Type u_3} 
{β : Type u_4} [inst : FunLike F α β] [inst_1 : AddGroup α] [inst_2 : AddCommMon
oid β]   [inst_3 : LinearOrd…
· 使用定理 `SeminormClass.toAddGroupSeminormClass`：∀ {F : Type u_12} {𝕜 : outParam (
Type u_13)} {E : outParam (Type u_14)} {inst : SeminormedRing 𝕜} {inst_1 : AddGr
oup E}   {inst_2 : SMul 𝕜 E…
-/
theorem ball_smul_closedBall (p : Seminorm 𝕜 E) (r₁ : ℝ) {r₂ : ℝ} (hr₂ : r₂ ≠ 0) :
    Metric.ball (0 : 𝕜) r₁ • p.closedBall 0 r₂ ⊆ p.ball 0 (r₁ * r₂) := by
  simp only [smul_subset_iff, mem_ball_zero, mem_closedBall_zero, mem_ball_zero_iff,
    map_smul_eq_mul]
  intro a ha b hb
  rw [mul_comm, mul_comm r₁]
  refine mul_lt_mul' hb ha (norm_nonneg _) (hr₂.lt_or_gt.resolve_left ?_)
  exact ((apply_nonneg p b).trans hb).not_gt
/-
**Seminorm.ball_smul_ball** 是 Mathlib 中的一个定理，位于命名空间 `Seminorm`。
形式化陈述：ball_smul_ball (p : Seminorm 𝕜 E) (r₁ r₂ : Real) : Metric.ball (0 : 𝕜) r₁ 
• p.ball 0 r₂ subseteq p.ball 0 (r₁ * r₂)
参数：p : Seminorm 𝕜 E；r₁ r₂ : Real。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Seminorm.ball_eq_emptyset`：ball_eq_emptyset (p : Seminorm 𝕜 E) {x : E} {
r : Real} (hr : r <= 0) : p.ball x r = ∅
· 使用定理 `Set.smul_empty`：∀ {α : Type u_2} {β : Type u_3} [inst : SMul α β] {s : S
et α}, s • ∅ = ∅
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用引理 `Set.smul_subset_smul_left`：smul_subset_smul_left : t₁ subseteq t₂ -> s •
 t₁ subseteq s • t₂
· 使用定理 `Seminorm.ball_subset_closedBall`：ball_subset_closedBall (x r) : ball p x
 r subseteq closedBall p x r
· 使用定理 `Seminorm.ball_smul_closedBall`：ball_smul_closedBall (p : Seminorm 𝕜 E) (
r₁ : Real) {r₂ : Real} (hr₂ : r₂ != 0) : Metric.ball (0 : 𝕜) r₁ • p.closedBall 0
 r₂ subseteq p.ball…
-/
theorem ball_smul_ball (p : Seminorm 𝕜 E) (r₁ r₂ : ℝ) :
    Metric.ball (0 : 𝕜) r₁ • p.ball 0 r₂ ⊆ p.ball 0 (r₁ * r₂) := by
  rcases eq_or_ne r₂ 0 with rfl | hr₂
  · simp
  · exact (smul_subset_smul_left (ball_subset_closedBall _ _ _)).trans
      (ball_smul_closedBall _ _ hr₂)
/-
**Seminorm.closedBall_smul_closedBall** 是 Mathlib 中的一个定理，位于命名空间 `Seminorm`。
形式化陈述：closedBall_smul_closedBall (p : Seminorm 𝕜 E) (r₁ r₂ : Real) : Metric.clos
edBall (0 : 𝕜) r₁ • p.closedBall 0 r₂ subseteq p.closedBall 0 (r₁ * r₂)
参数：p : Seminorm 𝕜 E；r₁ r₂ : Real。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `SeminormClass.map_smul_eq_mul`：∀ {F : Type u_12} {𝕜 : outParam (Type u_1
3)} {E : outParam (Type u_14)} {inst : SeminormedRing 𝕜} {inst_1 : AddGroup E}  
 {inst_2 : SMul 𝕜 E…
· 使用定理 `mul_le_mul`：∀ {α : Type u_1} [inst : Mul α] [inst_1 : Zero α] [inst_2 : 
Preorder α] {a b c d : α} [PosMulMono α] [MulPosMono α],   a ≤ b → c ≤ d → 0 ≤ c
…
· 使用定理 `IsOrderedRing.toPosMulMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], PosMulMono R
· 使用定理 `IsOrderedRing.toMulPosMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], MulPosMono R
· 使用定理 `NonnegHomClass.apply_nonneg`：∀ {F : Type u_7} {α : outParam (Type u_8)} 
{β : outParam (Type u_9)} {inst : Zero β} {inst_1 : LE β}   {inst_2 : FunLike F 
α β} [self : Nonn…
· 使用定理 `AddGroupSeminormClass.toNonnegHomClass`：∀ {F : Type u_2} {α : Type u_3} 
{β : Type u_4} [inst : FunLike F α β] [inst_1 : AddGroup α] [inst_2 : AddCommMon
oid β]   [inst_3 : LinearOrd…
· 使用定理 `SeminormClass.toAddGroupSeminormClass`：∀ {F : Type u_12} {𝕜 : outParam (
Type u_13)} {E : outParam (Type u_14)} {inst : SeminormedRing 𝕜} {inst_1 : AddGr
oup E}   {inst_2 : SMul 𝕜 E…
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `norm_nonneg`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (a : E), 0 ≤
 ‖a‖
-/
theorem closedBall_smul_closedBall (p : Seminorm 𝕜 E) (r₁ r₂ : ℝ) :
    Metric.closedBall (0 : 𝕜) r₁ • p.closedBall 0 r₂ ⊆ p.closedBall 0 (r₁ * r₂) := by
  simp only [smul_subset_iff, mem_closedBall_zero, mem_closedBall_zero_iff, map_smul_eq_mul]
  intro a ha b hb
  gcongr
  exact (norm_nonneg _).trans ha
/-
**Seminorm.neg_mem_ball_zero** 是 Mathlib 中的一个定理，位于命名空间 `Seminorm`。
形式化陈述：neg_mem_ball_zero {r : Real} {x : E} : -x in ball p 0 r ↔ x in ball p 0 r
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `AddGroupSeminormClass.map_neg_eq_map`：∀ {F : Type u_7} {α : outParam (Ty
pe u_8)} {β : outParam (Type u_9)} {inst : AddGroup α} {inst_1 : AddCommMonoid β
}   {inst_2 : PartialOrder…
· 使用定理 `SeminormClass.toAddGroupSeminormClass`：∀ {F : Type u_12} {𝕜 : outParam (
Type u_13)} {E : outParam (Type u_14)} {inst : SeminormedRing 𝕜} {inst_1 : AddGr
oup E}   {inst_2 : SMul 𝕜 E…
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem neg_mem_ball_zero {r : ℝ} {x : E} : -x ∈ ball p 0 r ↔ x ∈ ball p 0 r := by
  simp only [mem_ball_zero, map_neg_eq_map]
/-
**Seminorm.neg_mem_closedBall_zero** 是 Mathlib 中的一个定理，位于命名空间 `Seminorm`。
形式化陈述：neg_mem_closedBall_zero {r : Real} {x : E} : -x in closedBall p 0 r ↔ x in
 closedBall p 0 r
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `AddGroupSeminormClass.map_neg_eq_map`：∀ {F : Type u_7} {α : outParam (Ty
pe u_8)} {β : outParam (Type u_9)} {inst : AddGroup α} {inst_1 : AddCommMonoid β
}   {inst_2 : PartialOrder…
· 使用定理 `SeminormClass.toAddGroupSeminormClass`：∀ {F : Type u_12} {𝕜 : outParam (
Type u_13)} {E : outParam (Type u_14)} {inst : SeminormedRing 𝕜} {inst_1 : AddGr
oup E}   {inst_2 : SMul 𝕜 E…
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem neg_mem_closedBall_zero {r : ℝ} {x : E} : -x ∈ closedBall p 0 r ↔ x ∈ closedBall p 0 r := by
  simp only [mem_closedBall_zero, map_neg_eq_map]

@[simp]
/-
**Seminorm.neg_ball** 是 Mathlib 中的一个定理，位于命名空间 `Seminorm`。
形式化陈述：neg_ball (p : Seminorm 𝕜 E) (r : Real) (x : E) : -ball p x r = ball p (-x)
 r
参数：p : Seminorm 𝕜 E；r : Real；x : E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.mem_neg`：∀ {α : Type u_2} [inst : Neg α] {s : Set α} {a : α}, a ∈ -s
 ↔ -a ∈ s
· 使用定理 `Seminorm.mem_ball`：mem_ball : y in ball p x r ↔ p (y - x) < r
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `neg_add'`：∀ {α : Type u_1} [inst : SubtractionCommMonoid α] (a b : α), -
(a + b) = -a - b
· 使用定理 `sub_neg_eq_add`：∀ {α : Type u_1} [inst : SubtractionMonoid α] (a b : α),
 a - -b = a + b
· 使用定理 `AddGroupSeminormClass.map_neg_eq_map`：∀ {F : Type u_7} {α : outParam (Ty
pe u_8)} {β : outParam (Type u_9)} {inst : AddGroup α} {inst_1 : AddCommMonoid β
}   {inst_2 : PartialOrder…
· 使用定理 `SeminormClass.toAddGroupSeminormClass`：∀ {F : Type u_12} {𝕜 : outParam (
Type u_13)} {E : outParam (Type u_14)} {inst : SeminormedRing 𝕜} {inst_1 : AddGr
oup E}   {inst_2 : SMul 𝕜 E…
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem neg_ball (p : Seminorm 𝕜 E) (r : ℝ) (x : E) : -ball p x r = ball p (-x) r := by
  ext
  rw [Set.mem_neg, mem_ball, mem_ball, ← neg_add', sub_neg_eq_add, map_neg_eq_map]

@[simp]
/-
**Seminorm.neg_closedBall** 是 Mathlib 中的一个定理，位于命名空间 `Seminorm`。
形式化陈述：neg_closedBall (p : Seminorm 𝕜 E) (r : Real) (x : E) : -closedBall p x r =
 closedBall p (-x) r
参数：p : Seminorm 𝕜 E；r : Real；x : E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.mem_neg`：∀ {α : Type u_2} [inst : Neg α] {s : Set α} {a : α}, a ∈ -s
 ↔ -a ∈ s
· 使用定理 `Seminorm.mem_closedBall`：mem_closedBall : y in closedBall p x r ↔ p (y -
 x) <= r
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `neg_add'`：∀ {α : Type u_1} [inst : SubtractionCommMonoid α] (a b : α), -
(a + b) = -a - b
· 使用定理 `sub_neg_eq_add`：∀ {α : Type u_1} [inst : SubtractionMonoid α] (a b : α),
 a - -b = a + b
· 使用定理 `AddGroupSeminormClass.map_neg_eq_map`：∀ {F : Type u_7} {α : outParam (Ty
pe u_8)} {β : outParam (Type u_9)} {inst : AddGroup α} {inst_1 : AddCommMonoid β
}   {inst_2 : PartialOrder…
· 使用定理 `SeminormClass.toAddGroupSeminormClass`：∀ {F : Type u_12} {𝕜 : outParam (
Type u_13)} {E : outParam (Type u_14)} {inst : SeminormedRing 𝕜} {inst_1 : AddGr
oup E}   {inst_2 : SMul 𝕜 E…
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem neg_closedBall (p : Seminorm 𝕜 E) (r : ℝ) (x : E) :
    -closedBall p x r = closedBall p (-x) r := by
  ext
  rw [Set.mem_neg, mem_closedBall, mem_closedBall, ← neg_add', sub_neg_eq_add, map_neg_eq_map]

end Module

end AddCommGroup

end SeminormedRing

section NormedDivisionRing

variable [NormedDivisionRing 𝕜] [AddCommGroup E] [Module 𝕜 E] (p : Seminorm 𝕜 E) {r : ℝ} {x : E}

/-
**Seminorm.ball_norm_mul_subset** 是 Mathlib 中的一个定理，位于命名空间 `Seminorm`。
形式化陈述：ball_norm_mul_subset {p : Seminorm 𝕜 E} {k : 𝕜} {r : Real} : p.ball 0 (‖k‖
 * r) subseteq k • p.ball 0 r
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `norm_zero`：∀ {E : Type u_5} [inst : SeminormedAddGroup E], ‖0‖ = 0
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `Seminorm.ball_eq_emptyset`：ball_eq_emptyset (p : Seminorm 𝕜 E) {x : E} {
r : Real} (hr : r <= 0) : p.ball x r = ∅
· 使用引理 `le_rfl`：le_rfl : a <= a
· 使用定理 `Set.empty_subset`：empty_subset (s : Set α) : ∅ subseteq s
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.mem_smul_set`：∀ {α : Type u_2} {β : Type u_3} [inst : SMul α β] {t :
 Set β} {a : α} {x : β}, x ∈ a • t ↔ ∃ y ∈ t, a • y = x
· 使用定理 `Seminorm.mem_ball_zero`：mem_ball_zero : y in ball p 0 r ↔ p y < r
· 使用定理 `SeminormClass.map_smul_eq_mul`：∀ {F : Type u_12} {𝕜 : outParam (Type u_1
3)} {E : outParam (Type u_14)} {inst : SeminormedRing 𝕜} {inst_1 : AddGroup E}  
 {inst_2 : SMul 𝕜 E…
· 使用定理 `norm_inv`：norm_inv (a : α) : ‖a⁻¹‖ = ‖a‖⁻¹
· 使用定理 `mul_lt_mul_iff_right₀`：mul_lt_mul_iff_right₀ [PosMulStrictMono α] [PosMu
lReflectLT α] (a0 : 0 < a) : a * b < a * c ↔ b < c where mp h
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `norm_pos_iff`：∀ {E : Type u_5} [inst : NormedAddGroup E] {a : E}, 0 < ‖a
‖ ↔ a ≠ 0
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `div_eq_mul_inv`：div_eq_mul_inv (a b : G) : a / b = a * b⁻¹
· 使用定理 `div_self`：∀ {G₀ : Type u_3} [inst : GroupWithZero G₀] {a : G₀}, a ≠ 0 → 
a / a = 1
· 使用定理 `ne_of_gt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用引理 `smul_assoc`：smul_assoc {M N} [SMul M N] [SMul N α] [SMul M α] [IsScalarT
ower M N α] (x : M) (y : N) (z : α) : (x • y) • z = x • y • z
· 使用引理 `smul_eq_mul`：smul_eq_mul {α : Type*} [Mul α] (a b : α) : a • b = a * b
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
-/
theorem ball_norm_mul_subset {p : Seminorm 𝕜 E} {k : 𝕜} {r : ℝ} :
    p.ball 0 (‖k‖ * r) ⊆ k • p.ball 0 r := by
  rcases eq_or_ne k 0 with (rfl | hk)
  · rw [norm_zero, zero_mul, ball_eq_emptyset _ le_rfl]
    exact empty_subset _
  · intro x
    rw [Set.mem_smul_set, Seminorm.mem_ball_zero]
    refine fun hx => ⟨k⁻¹ • x, ?_, ?_⟩
    · rwa [Seminorm.mem_ball_zero, map_smul_eq_mul, norm_inv, ←
        mul_lt_mul_iff_right₀ <| norm_pos_iff.mpr hk, ← mul_assoc, ← div_eq_mul_inv ‖k‖ ‖k‖,
        div_self (ne_of_gt <| norm_pos_iff.mpr hk), one_mul]
    rw [← smul_assoc, smul_eq_mul, ← div_eq_mul_inv, div_self hk, one_smul]
/-
**Seminorm.smul_ball_zero** 是 Mathlib 中的一个定理，位于命名空间 `Seminorm`。
形式化陈述：smul_ball_zero {p : Seminorm 𝕜 E} {k : 𝕜} {r : Real} (hk : k != 0) : k • p
.ball 0 r = p.ball 0 (‖k‖ * r)
参数：hk : k != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Set.mem_smul_set_iff_inv_smul_mem₀`：mem_smul_set_iff_inv_smul_mem₀ (ha :
 a != 0) (A : Set β) (x : β) : x in a • A ↔ a⁻¹ • x in A
· 使用定理 `Seminorm.mem_ball_zero`：mem_ball_zero : y in ball p 0 r ↔ p y < r
· 使用定理 `SeminormClass.map_smul_eq_mul`：∀ {F : Type u_12} {𝕜 : outParam (Type u_1
3)} {E : outParam (Type u_14)} {inst : SeminormedRing 𝕜} {inst_1 : AddGroup E}  
 {inst_2 : SMul 𝕜 E…
· 使用定理 `norm_inv`：norm_inv (a : α) : ‖a⁻¹‖ = ‖a‖⁻¹
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `div_eq_inv_mul`：div_eq_inv_mul : a / b = b⁻¹ * a
· 使用引理 `div_lt_iff₀`：div_lt_iff₀ (hc : 0 < c) : b / c < a ↔ b < a * c
· 使用定理 `MulPosReflectLE.toMulPosReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [MulPosReflectLE α], MulPosReflectLT α
· 使用定理 `MulPosStrictMono.toMulPosReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [MulPosStrictMono α], MulPosReflectLE α
· 使用定理 `IsStrictOrderedRing.toMulPosStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], MulPosStrictMono 
R
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `norm_pos_iff`：∀ {E : Type u_5} [inst : NormedAddGroup E] {a : E}, 0 < ‖a
‖ ↔ a ≠ 0
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem smul_ball_zero {p : Seminorm 𝕜 E} {k : 𝕜} {r : ℝ} (hk : k ≠ 0) :
    k • p.ball 0 r = p.ball 0 (‖k‖ * r) := by
  ext
  rw [mem_smul_set_iff_inv_smul_mem₀ hk, p.mem_ball_zero, p.mem_ball_zero, map_smul_eq_mul,
    norm_inv, ← div_eq_inv_mul, div_lt_iff₀ (norm_pos_iff.2 hk), mul_comm]
/-
**Seminorm.smul_closedBall_subset** 是 Mathlib 中的一个定理，位于命名空间 `Seminorm`。
形式化陈述：smul_closedBall_subset {p : Seminorm 𝕜 E} {k : 𝕜} {r : Real} : k • p.close
dBall 0 r subseteq p.closedBall 0 (‖k‖ * r)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Seminorm.mem_closedBall_zero`：mem_closedBall_zero : y in closedBall p 0 
r ↔ p y <= r
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `SeminormClass.map_smul_eq_mul`：∀ {F : Type u_12} {𝕜 : outParam (Type u_1
3)} {E : outParam (Type u_14)} {inst : SeminormedRing 𝕜} {inst_1 : AddGroup E}  
 {inst_2 : SMul 𝕜 E…
· 使用定理 `mul_le_mul_of_nonneg_left`：mul_le_mul_of_nonneg_left [PosMulMono α] (hbc
 : b <= c) (ha : 0 <= a) : a * b <= a * c
· 使用定理 `IsOrderedRing.toPosMulMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], PosMulMono R
· 使用定理 `norm_nonneg`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (a : E), 0 ≤
 ‖a‖
-/
theorem smul_closedBall_subset {p : Seminorm 𝕜 E} {k : 𝕜} {r : ℝ} :
    k • p.closedBall 0 r ⊆ p.closedBall 0 (‖k‖ * r) := by
  rintro x ⟨y, hy, h⟩
  rw [Seminorm.mem_closedBall_zero, ← h, map_smul_eq_mul]
  rw [Seminorm.mem_closedBall_zero] at hy
  gcongr
/-
**Seminorm.smul_closedBall_zero** 是 Mathlib 中的一个定理，位于命名空间 `Seminorm`。
形式化陈述：smul_closedBall_zero {p : Seminorm 𝕜 E} {k : 𝕜} {r : Real} (hk : 0 < ‖k‖) 
: k • p.closedBall 0 r = p.closedBall 0 (‖k‖ * r)
参数：hk : 0 < ‖k‖。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `subset_antisymm`：∀ {α : Type u_1} [UsesSetNotationForOrder α] [inst : Pa
rtialOrder α] {a b : α}, a ⊆ b → b ⊆ a → a = b
· 使用定理 `Seminorm.smul_closedBall_subset`：smul_closedBall_subset {p : Seminorm 𝕜 
E} {k : 𝕜} {r : Real} : k • p.closedBall 0 r subseteq p.closedBall 0 (‖k‖ * r)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.mem_smul_set`：∀ {α : Type u_2} {β : Type u_3} [inst : SMul α β] {t :
 Set β} {a : α} {x : β}, x ∈ a • t ↔ ∃ y ∈ t, a • y = x
· 使用定理 `Seminorm.mem_closedBall_zero`：mem_closedBall_zero : y in closedBall p 0 
r ↔ p y <= r
· 使用定理 `SeminormClass.map_smul_eq_mul`：∀ {F : Type u_12} {𝕜 : outParam (Type u_1
3)} {E : outParam (Type u_14)} {inst : SeminormedRing 𝕜} {inst_1 : AddGroup E}  
 {inst_2 : SMul 𝕜 E…
· 使用定理 `norm_inv`：norm_inv (a : α) : ‖a⁻¹‖ = ‖a‖⁻¹
· 使用引理 `inv_mul_le_iff₀`：inv_mul_le_iff₀ (hc : 0 < c) : c⁻¹ * b <= a ↔ b <= c * 
a
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `smul_assoc`：smul_assoc {M N} [SMul M N] [SMul N α] [SMul M α] [IsScalarT
ower M N α] (x : M) (y : N) (z : α) : (x • y) • z = x • y • z
· 使用引理 `smul_eq_mul`：smul_eq_mul {α : Type*} [Mul α] (a b : α) : a • b = a * b
· 使用定理 `div_eq_mul_inv`：div_eq_mul_inv (a b : G) : a / b = a * b⁻¹
· 使用定理 `div_self`：∀ {G₀ : Type u_3} [inst : GroupWithZero G₀] {a : G₀}, a ≠ 0 → 
a / a = 1
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `norm_pos_iff`：∀ {E : Type u_5} [inst : NormedAddGroup E] {a : E}, 0 < ‖a
‖ ↔ a ≠ 0
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
-/
theorem smul_closedBall_zero {p : Seminorm 𝕜 E} {k : 𝕜} {r : ℝ} (hk : 0 < ‖k‖) :
    k • p.closedBall 0 r = p.closedBall 0 (‖k‖ * r) := by
  refine subset_antisymm smul_closedBall_subset ?_
  intro x
  rw [Set.mem_smul_set, Seminorm.mem_closedBall_zero]
  refine fun hx => ⟨k⁻¹ • x, ?_, ?_⟩
  · rwa [Seminorm.mem_closedBall_zero, map_smul_eq_mul, norm_inv, inv_mul_le_iff₀ hk]
  rw [← smul_assoc, smul_eq_mul, ← div_eq_mul_inv, div_self (norm_pos_iff.mp hk), one_smul]
/-
**Seminorm.ball_zero_absorbs_ball_zero** 是 Mathlib 中的一个定理，位于命名空间 `Seminorm`。
形式化陈述：ball_zero_absorbs_ball_zero (p : Seminorm 𝕜 E) {r₁ r₂ : Real} (hr₁ : 0 < r
₁) : Absorbs 𝕜 (p.ball 0 r₁) (p.ball 0 r₂)
参数：p : Seminorm 𝕜 E；hr₁ : 0 < r₁。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `exists_pos_lt_mul`：exists_pos_lt_mul {a : α} (h : 0 < a) (b : α) : exist
s c : α, 0 < c ∧ b < c * a
· 使用定理 `Absorbs.of_norm`：∀ {𝕜 : Type u_1} {E : Type u_3} [inst : SeminormedRing 
𝕜] [inst_1 : SMul 𝕜 E] {A B : Set E},   (∃ r, ∀ (c : 𝕜), r ≤ ‖c‖ → B ⊆ c • A) → 
Absor…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Seminorm.smul_ball_zero`：smul_ball_zero {p : Seminorm 𝕜 E} {k : 𝕜} {r : 
Real} (hk : k != 0) : k • p.ball 0 r = p.ball 0 (‖k‖ * r)
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `norm_pos_iff`：∀ {E : Type u_5} [inst : NormedAddGroup E] {a : E}, 0 < ‖a
‖ ↔ a ≠ 0
· 使用定理 `LT.lt.trans_le`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a < b 
→ b ≤ c → a < c
· 使用定理 `Seminorm.mem_ball_zero`：mem_ball_zero : y in ball p 0 r ↔ p y < r
· 使用定理 `LT.lt.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a < b → b
 < c → a < c
· 使用定理 `mul_le_mul_of_nonneg_right`：mul_le_mul_of_nonneg_right [MulPosMono α] (h
bc : b <= c) (ha : 0 <= a) : b * a <= c * a
· 使用定理 `IsOrderedRing.toMulPosMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], MulPosMono R
· 使用定理 `le_of_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
-/
theorem ball_zero_absorbs_ball_zero (p : Seminorm 𝕜 E) {r₁ r₂ : ℝ} (hr₁ : 0 < r₁) :
    Absorbs 𝕜 (p.ball 0 r₁) (p.ball 0 r₂) := by
  rcases exists_pos_lt_mul hr₁ r₂ with ⟨r, hr₀, hr⟩
  refine .of_norm ⟨r, fun a ha x hx => ?_⟩
  rw [smul_ball_zero (norm_pos_iff.1 <| hr₀.trans_le ha), p.mem_ball_zero]
  rw [p.mem_ball_zero] at hx
  exact hx.trans (hr.trans_le <| by gcongr)

/-- Seminorm-balls at the origin are absorbent. -/
/-
**Seminorm.absorbent_ball_zero** 是 Mathlib 中的一个定理，位于命名空间 `Seminorm`。
形式化陈述：∀ {𝕜 : Type u_3} {E : Type u_7} [inst : NormedDivisionRing 𝕜] [inst_1 : Ad
dCommGroup E] [inst_2 : _root_.Module 𝕜 E]   (p : Seminorm 𝕜 E) {r : ℝ}, 0 < r →
 Absorbent 𝕜 (p.ball 0 r)
参数：p : Seminorm 𝕜 E；p.ball 0 r。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `absorbent_iff_forall_absorbs_singleton`：∀ {M : Type u_1} {α : Type u_2} 
[inst : Bornology M] [inst_1 : SMul M α] {s : Set α},   Absorbent M s ↔ ∀ (x : α
), Absorbs M s {x}
· 使用引理 `Absorbs.mono_right`：mono_right (h : Absorbs M s t₁) (ht : t₂ subseteq t₁
) : Absorbs M s t₂
· 使用定理 `Seminorm.ball_zero_absorbs_ball_zero`：ball_zero_absorbs_ball_zero (p : S
eminorm 𝕜 E) {r₁ r₂ : Real} (hr₁ : 0 < r₁) : Absorbs 𝕜 (p.ball 0 r₁) (p.ball 0 r
₂)
· 使用定理 `Set.singleton_subset_iff`：singleton_subset_iff {a : α} {s : Set α} : {a}
 subseteq s ↔ a in s
· 使用定理 `Seminorm.mem_ball_zero`：mem_ball_zero : y in ball p 0 r ↔ p y < r
· 使用引理 `lt_add_one`：lt_add_one [One α] [AddZeroClass α] [PartialOrder α] [ZeroLE
OneClass α] [NeZero (1 : α)] [AddLeftStrictMono α] (a : α) : a < a + 1
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
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
Seminorm-balls at the origin are absorbent.
-/
protected theorem absorbent_ball_zero (hr : 0 < r) : Absorbent 𝕜 (ball p (0 : E) r) :=
  absorbent_iff_forall_absorbs_singleton.2 fun _ =>
    (p.ball_zero_absorbs_ball_zero hr).mono_right <|
      singleton_subset_iff.2 <| p.mem_ball_zero.2 <| lt_add_one _

/-- Closed seminorm-balls at the origin are absorbent. -/
/-
**Seminorm.absorbent_closedBall_zero** 是 Mathlib 中的一个定理，位于命名空间 `Seminorm`。
形式化陈述：∀ {𝕜 : Type u_3} {E : Type u_7} [inst : NormedDivisionRing 𝕜] [inst_1 : Ad
dCommGroup E] [inst_2 : _root_.Module 𝕜 E]   (p : Seminorm 𝕜 E) {r : ℝ}, 0 < r →
 Absorbent 𝕜 (p.closedBall 0 r)
参数：p : Seminorm 𝕜 E；p.closedBall 0 r。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Absorbent.mono`：∀ {M : Type u_1} {α : Type u_2} [inst : Bornology M] [in
st_1 : SMul M α] {s t : Set α},   Absorbent M s → s ⊆ t → Absorbent M t
· 使用定理 `Seminorm.absorbent_ball_zero`：∀ {𝕜 : Type u_3} {E : Type u_7} [inst : No
rmedDivisionRing 𝕜] [inst_1 : AddCommGroup E] [inst_2 : _root_.Module 𝕜 E]   (p 
: Seminorm 𝕜 E) {r…
· 使用定理 `Seminorm.ball_subset_closedBall`：ball_subset_closedBall (x r) : ball p x
 r subseteq closedBall p x r

--- 原说明 ---
Closed seminorm-balls at the origin are absorbent.
-/
protected theorem absorbent_closedBall_zero (hr : 0 < r) : Absorbent 𝕜 (closedBall p (0 : E) r) :=
  (p.absorbent_ball_zero hr).mono (p.ball_subset_closedBall _ _)

/-- Seminorm-balls containing the origin are absorbent. -/
/-
**Seminorm.absorbent_ball** 是 Mathlib 中的一个定理，位于命名空间 `Seminorm`。
形式化陈述：∀ {𝕜 : Type u_3} {E : Type u_7} [inst : NormedDivisionRing 𝕜] [inst_1 : Ad
dCommGroup E] [inst_2 : _root_.Module 𝕜 E]   (p : Seminorm 𝕜 E) {r : ℝ} {x : E},
 p x < r → Absorbent 𝕜 (p.ball x r)
参数：p : Seminorm 𝕜 E；p.ball x r。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Absorbent.mono`：∀ {M : Type u_1} {α : Type u_2} [inst : Bornology M] [in
st_1 : SMul M α] {s t : Set α},   Absorbent M s → s ⊆ t → Absorbent M t
· 使用定理 `Seminorm.absorbent_ball_zero`：∀ {𝕜 : Type u_3} {E : Type u_7} [inst : No
rmedDivisionRing 𝕜] [inst_1 : AddCommGroup E] [inst_2 : _root_.Module 𝕜 E]   (p 
: Seminorm 𝕜 E) {r…
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `sub_pos`：∀ {α : Type u} [inst : AddGroup α] [inst_1 : LT α] [AddRightStr
ictMono α] {a b : α}, 0 < a - b ↔ b < a
· 使用定理 `IsRightCancelAdd.addRightStrictMono_of_addRightMono`：∀ (N : Type u_2) [i
nst : Add N] [IsRightCancelAdd N] [inst_2 : PartialOrder N] [AddRightMono N], Ad
dRightStrictMono N
· 使用定理 `instIsRightCancelAddOfAddRightReflectLE`：∀ {α : Type u_1} [inst : Add α]
 [inst_1 : PartialOrder α] [AddRightReflectLE α], IsRightCancelAdd α
· 使用定理 `addRightReflectLE_of_addLeftReflectLE`：∀ (N : Type u_2) [inst : AddCommS
emigroup N] [inst_1 : LE N] [AddLeftReflectLE N], AddRightReflectLE N
· 使用定理 `IsLeftCancelAdd.addLeftReflectLE_of_addLeftReflectLT`：∀ (N : Type u_2) [
inst : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftReflectLT N]
, AddLeftReflectLE N
· 使用定理 `AddLeftCancelSemigroup.toIsLeftCancelAdd`：∀ {G : Type u} [self : AddLeft
CancelSemigroup G], IsLeftCancelAdd G
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `Seminorm.mem_ball`：mem_ball : y in ball p x r ↔ p (y - x) < r
· 使用定理 `LE.le.trans_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b 
→ b < c → a < c
· 使用定理 `map_sub_le_add`：∀ {F : Type u_2} {α : Type u_3} {β : Type u_4} [inst : F
unLike F α β] [inst_1 : AddGroup α] [inst_2 : AddCommMonoid β]   [inst_3 : Parti
alOr…
· 使用定理 `SeminormClass.toAddGroupSeminormClass`：∀ {F : Type u_12} {𝕜 : outParam (
Type u_13)} {E : outParam (Type u_14)} {inst : SeminormedRing 𝕜} {inst_1 : AddGr
oup E}   {inst_2 : SMul 𝕜 E…
· 使用定理 `add_lt_of_lt_sub_right`：∀ {α : Type u} [inst : AddGroup α] [inst_1 : LT 
α] [AddRightStrictMono α] {a b c : α}, a < c - b → a + b < c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Seminorm.mem_ball_zero`：mem_ball_zero : y in ball p 0 r ↔ p y < r

--- 原说明 ---
Seminorm-balls containing the origin are absorbent.
-/
protected theorem absorbent_ball (hpr : p x < r) : Absorbent 𝕜 (ball p x r) := by
  refine (p.absorbent_ball_zero <| sub_pos.2 hpr).mono fun y hy => ?_
  rw [p.mem_ball_zero] at hy
  exact p.mem_ball.2 ((map_sub_le_add p _ _).trans_lt <| add_lt_of_lt_sub_right hy)

/-- Seminorm-balls containing the origin are absorbent. -/
/-
**Seminorm.absorbent_closedBall** 是 Mathlib 中的一个定理，位于命名空间 `Seminorm`。
形式化陈述：∀ {𝕜 : Type u_3} {E : Type u_7} [inst : NormedDivisionRing 𝕜] [inst_1 : Ad
dCommGroup E] [inst_2 : _root_.Module 𝕜 E]   (p : Seminorm 𝕜 E) {r : ℝ} {x : E},
 p x < r → Absorbent 𝕜 (p.closedBall x r)
参数：p : Seminorm 𝕜 E；p.closedBall x r。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Absorbent.mono`：∀ {M : Type u_1} {α : Type u_2} [inst : Bornology M] [in
st_1 : SMul M α] {s t : Set α},   Absorbent M s → s ⊆ t → Absorbent M t
· 使用定理 `Seminorm.absorbent_closedBall_zero`：∀ {𝕜 : Type u_3} {E : Type u_7} [ins
t : NormedDivisionRing 𝕜] [inst_1 : AddCommGroup E] [inst_2 : _root_.Module 𝕜 E]
   (p : Seminorm 𝕜 E) {r…
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `sub_pos`：∀ {α : Type u} [inst : AddGroup α] [inst_1 : LT α] [AddRightStr
ictMono α] {a b : α}, 0 < a - b ↔ b < a
· 使用定理 `IsRightCancelAdd.addRightStrictMono_of_addRightMono`：∀ (N : Type u_2) [i
nst : Add N] [IsRightCancelAdd N] [inst_2 : PartialOrder N] [AddRightMono N], Ad
dRightStrictMono N
· 使用定理 `instIsRightCancelAddOfAddRightReflectLE`：∀ {α : Type u_1} [inst : Add α]
 [inst_1 : PartialOrder α] [AddRightReflectLE α], IsRightCancelAdd α
· 使用定理 `addRightReflectLE_of_addLeftReflectLE`：∀ (N : Type u_2) [inst : AddCommS
emigroup N] [inst_1 : LE N] [AddLeftReflectLE N], AddRightReflectLE N
· 使用定理 `IsLeftCancelAdd.addLeftReflectLE_of_addLeftReflectLT`：∀ (N : Type u_2) [
inst : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftReflectLT N]
, AddLeftReflectLE N
· 使用定理 `AddLeftCancelSemigroup.toIsLeftCancelAdd`：∀ {G : Type u} [self : AddLeft
CancelSemigroup G], IsLeftCancelAdd G
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `Seminorm.mem_closedBall`：mem_closedBall : y in closedBall p x r ↔ p (y -
 x) <= r
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `map_sub_le_add`：∀ {F : Type u_2} {α : Type u_3} {β : Type u_4} [inst : F
unLike F α β] [inst_1 : AddGroup α] [inst_2 : AddCommMonoid β]   [inst_3 : Parti
alOr…
· 使用定理 `SeminormClass.toAddGroupSeminormClass`：∀ {F : Type u_12} {𝕜 : outParam (
Type u_13)} {E : outParam (Type u_14)} {inst : SeminormedRing 𝕜} {inst_1 : AddGr
oup E}   {inst_2 : SMul 𝕜 E…
· 使用定理 `add_le_of_le_sub_right`：∀ {α : Type u} [inst : AddGroup α] [inst_1 : LE 
α] [AddRightMono α] {a b c : α}, a ≤ c - b → a + b ≤ c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Seminorm.mem_closedBall_zero`：mem_closedBall_zero : y in closedBall p 0 
r ↔ p y <= r

--- 原说明 ---
Seminorm-balls containing the origin are absorbent.
-/
protected theorem absorbent_closedBall (hpr : p x < r) : Absorbent 𝕜 (closedBall p x r) := by
  refine (p.absorbent_closedBall_zero <| sub_pos.2 hpr).mono fun y hy => ?_
  rw [p.mem_closedBall_zero] at hy
  exact p.mem_closedBall.2 ((map_sub_le_add p _ _).trans <| add_le_of_le_sub_right hy)

@[simp]
/-
**Seminorm.smul_ball_preimage** 是 Mathlib 中的一个定理，位于命名空间 `Seminorm`。
形式化陈述：smul_ball_preimage (p : Seminorm 𝕜 E) (y : E) (r : Real) (a : 𝕜) (ha : a !
= 0) : (a • ·) ⁻¹' p.ball y r = p.ball (a⁻¹ • y) (r / ‖a‖)
参数：p : Seminorm 𝕜 E；y : E；r : Real；a : 𝕜；ha : a != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.mem_preimage`：mem_preimage {f : α -> β} {s : Set β} {a : α} : a in f
 ⁻¹' s ↔ f a in s
· 使用定理 `Seminorm.mem_ball`：mem_ball : y in ball p x r ↔ p (y - x) < r
· 使用引理 `lt_div_iff₀`：lt_div_iff₀ (hc : 0 < c) : a < b / c ↔ a * c < b
· 使用定理 `MulPosReflectLE.toMulPosReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [MulPosReflectLE α], MulPosReflectLT α
· 使用定理 `MulPosStrictMono.toMulPosReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [MulPosStrictMono α], MulPosReflectLE α
· 使用定理 `IsStrictOrderedRing.toMulPosStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], MulPosStrictMono 
R
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `norm_pos_iff`：∀ {E : Type u_5} [inst : NormedAddGroup E] {a : E}, 0 < ‖a
‖ ↔ a ≠ 0
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `SeminormClass.map_smul_eq_mul`：∀ {F : Type u_12} {𝕜 : outParam (Type u_1
3)} {E : outParam (Type u_14)} {inst : SeminormedRing 𝕜} {inst_1 : AddGroup E}  
 {inst_2 : SMul 𝕜 E…
· 使用定理 `smul_sub`：smul_sub (r : M) (x y : A) : r • (x - y) = r • x - r • y
· 使用引理 `smul_inv_smul₀`：smul_inv_smul₀ (ha : a != 0) (x : β) : a • a⁻¹ • x = x
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem smul_ball_preimage (p : Seminorm 𝕜 E) (y : E) (r : ℝ) (a : 𝕜) (ha : a ≠ 0) :
    (a • ·) ⁻¹' p.ball y r = p.ball (a⁻¹ • y) (r / ‖a‖) :=
  Set.ext fun _ => by
    rw [mem_preimage, mem_ball, mem_ball, lt_div_iff₀ (norm_pos_iff.mpr ha), mul_comm, ←
      map_smul_eq_mul p, smul_sub, smul_inv_smul₀ ha]

@[simp]
/-
**Seminorm.smul_closedBall_preimage** 是 Mathlib 中的一个定理，位于命名空间 `Seminorm`。
形式化陈述：smul_closedBall_preimage (p : Seminorm 𝕜 E) (y : E) (r : Real) (a : 𝕜) (ha
 : a != 0) : (a • ·) ⁻¹' p.closedBall y r = p.closedBall (a⁻¹ • y) (r / ‖a‖)
参数：p : Seminorm 𝕜 E；y : E；r : Real；a : 𝕜；ha : a != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.mem_preimage`：mem_preimage {f : α -> β} {s : Set β} {a : α} : a in f
 ⁻¹' s ↔ f a in s
· 使用定理 `Seminorm.mem_closedBall`：mem_closedBall : y in closedBall p x r ↔ p (y -
 x) <= r
· 使用引理 `le_div_iff₀`：le_div_iff₀ (hc : 0 < c) : a <= b / c ↔ a * c <= b
· 使用定理 `MulPosReflectLE.toMulPosReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [MulPosReflectLE α], MulPosReflectLT α
· 使用定理 `MulPosStrictMono.toMulPosReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [MulPosStrictMono α], MulPosReflectLE α
· 使用定理 `IsStrictOrderedRing.toMulPosStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], MulPosStrictMono 
R
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `norm_pos_iff`：∀ {E : Type u_5} [inst : NormedAddGroup E] {a : E}, 0 < ‖a
‖ ↔ a ≠ 0
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `SeminormClass.map_smul_eq_mul`：∀ {F : Type u_12} {𝕜 : outParam (Type u_1
3)} {E : outParam (Type u_14)} {inst : SeminormedRing 𝕜} {inst_1 : AddGroup E}  
 {inst_2 : SMul 𝕜 E…
· 使用定理 `smul_sub`：smul_sub (r : M) (x y : A) : r • (x - y) = r • x - r • y
· 使用引理 `smul_inv_smul₀`：smul_inv_smul₀ (ha : a != 0) (x : β) : a • a⁻¹ • x = x
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem smul_closedBall_preimage (p : Seminorm 𝕜 E) (y : E) (r : ℝ) (a : 𝕜) (ha : a ≠ 0) :
    (a • ·) ⁻¹' p.closedBall y r = p.closedBall (a⁻¹ • y) (r / ‖a‖) :=
  Set.ext fun _ => by
    rw [mem_preimage, mem_closedBall, mem_closedBall, le_div_iff₀ (norm_pos_iff.mpr ha), mul_comm, ←
      map_smul_eq_mul p, smul_sub, smul_inv_smul₀ ha]

end NormedDivisionRing

section NormedField

variable [NormedField 𝕜] [AddCommGroup E] [Module 𝕜 E] (p : Seminorm 𝕜 E) {r : ℝ} {x : E}

/-
**Seminorm.closedBall_iSup** 是 Mathlib 中的一个定理，位于命名空间 `Seminorm`。
形式化陈述：closedBall_iSup {ι : Sort*} {p : ι -> Seminorm 𝕜 E} (hp : BddAbove (range 
p)) (e : E) {r : Real} (hr : 0 < r) : closedBall (⨆ i, p i) e r = ⋂ i, closedBal
l (p i) e r
参数：hp : BddAbove (range p)；e : E；hr : 0 < r。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `isEmpty_or_nonempty`：isEmpty_or_nonempty : IsEmpty α ∨ Nonempty α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iSup_of_empty'`：iSup_of_empty' {α ι} [SupSet α] [IsEmpty ι] (f : ι -> α)
 : iSup f = sSup (∅ : Set α)
· 使用定理 `Set.iInter_of_empty`：iInter_of_empty [IsEmpty ι] (s : ι -> Set α) : ⋂ i,
 s i = univ
· 使用定理 `Seminorm.sSup_empty`：∀ {𝕜 : Type u_3} {E : Type u_7} [inst : NormedField
 𝕜] [inst_1 : AddCommGroup E] [inst_2 : _root_.Module 𝕜 E],   sSup ∅ = ⊥
· 使用定理 `Seminorm.closedBall_bot`：closedBall_bot {r : Real} (x : E) (hr : 0 < r) 
: closedBall (⊥ : Seminorm 𝕜 E) x r = Set.univ
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Seminorm.bddAbove_range_iff`：∀ {𝕜 : Type u_3} {E : Type u_7} [inst : Nor
medField 𝕜] [inst_1 : AddCommGroup E] [inst_2 : _root_.Module 𝕜 E]   {ι : Sort u
_12} {p : ι → Sem…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Seminorm.iSup_apply`：∀ {𝕜 : Type u_3} {E : Type u_7} [inst : NormedField
 𝕜] [inst_1 : AddCommGroup E] [inst_2 : _root_.Module 𝕜 E]   {ι : Sort u_12} {p 
: ι → Sem…
· 使用定理 `ciSup_le_iff`：ciSup_le_iff [Nonempty ι] {f : ι -> α} {a : α} (hf : BddAb
ove (range f)) : iSup f <= a ↔ forall i, f i <= a
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem closedBall_iSup {ι : Sort*} {p : ι → Seminorm 𝕜 E} (hp : BddAbove (range p)) (e : E)
    {r : ℝ} (hr : 0 < r) : closedBall (⨆ i, p i) e r = ⋂ i, closedBall (p i) e r := by
  cases isEmpty_or_nonempty ι
  · rw [iSup_of_empty', iInter_of_empty, Seminorm.sSup_empty]
    exact closedBall_bot _ hr
  · ext x
    have := Seminorm.bddAbove_range_iff.mp hp (x - e)
    simp only [mem_closedBall, mem_iInter, Seminorm.iSup_apply hp, ciSup_le_iff this]

end NormedField

section Convex

variable [NormedField 𝕜] [AddCommGroup E] [SMul ℝ 𝕜] [NormSMulClass ℝ 𝕜] [Module 𝕜 E]

section SMul

variable [SMul ℝ E] [IsScalarTower ℝ 𝕜 E] (p : Seminorm 𝕜 E)

/-- A seminorm is convex. Also see `convexOn_norm`. -/
/-
**Seminorm.convexOn** 是 Mathlib 中的一个定理，位于命名空间 `Seminorm`。
形式化陈述：∀ {𝕜 : Type u_3} {E : Type u_7} [inst : NormedField 𝕜] [inst_1 : AddCommGr
oup E] [inst_2 : SMul ℝ 𝕜] [NormSMulClass ℝ 𝕜]   [inst_4 : _root_.Module 𝕜 E] [i
nst_5 : SMul ℝ E] [IsScalarTower ℝ 𝕜 E] (p : Seminorm 𝕜 E), ConvexOn ℝ Set.univ 
⇑p
参数：p : Seminorm 𝕜 E。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `convex_univ`：convex_univ : Convex 𝕜 (Set.univ : Set E)
· 使用定理 `SubadditiveHomClass.map_add_le_add`：∀ {F : Type u_7} {α : outParam (Type
 u_8)} {β : outParam (Type u_9)} {inst : Add α} {inst_1 : Add β} {inst_2 : LE β}
   {inst_3 : FunLike F α…
· 使用定理 `AddGroupSeminormClass.toSubadditiveHomClass`：∀ {F : Type u_7} {α : outPa
ram (Type u_8)} {β : outParam (Type u_9)} {inst : AddGroup α} {inst_1 : AddCommM
onoid β}   {inst_2 : PartialOrder…
· 使用定理 `SeminormClass.toAddGroupSeminormClass`：∀ {F : Type u_12} {𝕜 : outParam (
Type u_13)} {E : outParam (Type u_14)} {inst : SeminormedRing 𝕜} {inst_1 : AddGr
oup E}   {inst_2 : SMul 𝕜 E…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `SeminormClass.map_smul_eq_mul`：∀ {F : Type u_12} {𝕜 : outParam (Type u_1
3)} {E : outParam (Type u_14)} {inst : SeminormedRing 𝕜} {inst_1 : AddGroup E}  
 {inst_2 : SMul 𝕜 E…
· 使用引理 `smul_one_smul`：smul_one_smul {M} (N) [Monoid N] [SMul M N] [MulAction N 
α] [SMul M α] [IsScalarTower M N α] (x : M) (y : α) : (x • (1 : N)) • y = x • y
· 使用引理 `norm_smul`：norm_smul [Norm α] [Norm β] [SMul α β] [NormSMulClass α β] (r
 : α) (x : β) : ‖r • x‖ = ‖r‖ * ‖x‖
· 使用定理 `NormOneClass.norm_one`：∀ {α : Type u_5} {inst : Norm α} {inst_1 : One α}
 [self : NormOneClass α], ‖1‖ = 1
· 使用定理 `NormedDivisionRing.to_normOneClass`：∀ {α : Type u_2} [inst : NormedDivis
ionRing α], NormOneClass α
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `Real.norm_of_nonneg`：norm_of_nonneg (hr : 0 <= r) : ‖r‖ = r

--- 原说明 ---
A seminorm is convex. Also see `convexOn_norm`.
-/
protected theorem convexOn : ConvexOn ℝ univ p := by
  refine ⟨convex_univ, fun x _ y _ a b ha hb _ => ?_⟩
  calc
    p (a • x + b • y) ≤ p (a • x) + p (b • y) := map_add_le_add p _ _
    _ = ‖a • (1 : 𝕜)‖ * p x + ‖b • (1 : 𝕜)‖ * p y := by
      rw [← map_smul_eq_mul p, ← map_smul_eq_mul p, smul_one_smul, smul_one_smul]
    _ = a * p x + b * p y := by
      rw [norm_smul, norm_smul, norm_one, mul_one, mul_one, Real.norm_of_nonneg ha,
        Real.norm_of_nonneg hb]

end SMul

section Module

variable [Module ℝ E] [IsScalarTower ℝ 𝕜 E] (p : Seminorm 𝕜 E) (x : E) (r : ℝ)

/-- Seminorm-balls are convex. -/
/-
**Seminorm.convex_ball** 是 Mathlib 中的一个定理，位于命名空间 `Seminorm`。
形式化陈述：convex_ball : Convex Real (ball p x r)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.preimage_univ`：preimage_univ : f ⁻¹' univ = univ
· 使用定理 `Set.sep_univ`：sep_univ : { x in (univ : Set α) | p x } = { x | p x }
· 使用定理 `Seminorm.mem_ball`：mem_ball : y in ball p x r ↔ p (y - x) < r
· 使用定理 `sub_eq_add_neg`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a b : G), a - 
b = a + -b
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
· 使用定理 `ConvexOn.convex_lt`：ConvexOn.convex_lt (hf : ConvexOn 𝕜 s f) (r : β) : C
onvex 𝕜 ({ x in s | f x < r })
· 使用定理 `IsStrictOrderedModule.toPosSMulStrictMono`：∀ {α : Type u_1} {β : Type u_
2} {inst : SMul α β} {inst_1 : Preorder α} {inst_2 : Preorder β} {inst_3 : Zero 
α}   {inst_4 : Zero β} [self : …
· 使用定理 `IsStrictOrderedRing.toIsStrictOrderedModule`：∀ {α : Type u_1} [inst : Se
miring α] [inst_1 : PartialOrder α] [IsStrictOrderedRing α], IsStrictOrderedModu
le α α
· 使用定理 `ConvexOn.translate_left`：ConvexOn.translate_left (hf : ConvexOn 𝕜 s f) (
c : E) : ConvexOn 𝕜 ((fun z => c + z) ⁻¹' s) (f ∘ fun z => z + c)
· 使用定理 `Seminorm.convexOn`：∀ {𝕜 : Type u_3} {E : Type u_7} [inst : NormedField 𝕜
] [inst_1 : AddCommGroup E] [inst_2 : SMul ℝ 𝕜] [NormSMulClass ℝ 𝕜]   [inst_4 : 
_root_.…

--- 原说明 ---
Seminorm-balls are convex.
-/
theorem convex_ball : Convex ℝ (ball p x r) := by
  convert! (p.convexOn.translate_left (-x)).convex_lt r
  ext y
  rw [preimage_univ, sep_univ, p.mem_ball, sub_eq_add_neg]
  rfl

/-- Closed seminorm-balls are convex. -/
/-
**Seminorm.convex_closedBall** 是 Mathlib 中的一个定理，位于命名空间 `Seminorm`。
形式化陈述：convex_closedBall : Convex Real (closedBall p x r)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Seminorm.closedBall_eq_biInter_ball`：closedBall_eq_biInter_ball (x r) : 
closedBall p x r = ⋂ ρ > r, ball p x ρ
· 使用定理 `convex_iInter₂`：convex_iInter₂ {ι : Sort*} {κ : ι -> Sort*} {s : (i : ι)
 -> κ i -> Set E} (h : forall i j, Convex 𝕜 (s i j)) : Convex 𝕜 (⋂ (i) (j), s i 
j)
· 使用定理 `Seminorm.convex_ball`：convex_ball : Convex Real (ball p x r)

--- 原说明 ---
Closed seminorm-balls are convex.
-/
theorem convex_closedBall : Convex ℝ (closedBall p x r) := by
  rw [closedBall_eq_biInter_ball]
  exact convex_iInter₂ fun _ _ => convex_ball _ _ _

end Module

end Convex

section RestrictScalars

variable (𝕜) {𝕜' : Type*} [NormedField 𝕜] [SeminormedRing 𝕜'] [SMul 𝕜 𝕜'] [NormSMulClass 𝕜 𝕜']
  [NormOneClass 𝕜'] [AddCommGroup E] [Module 𝕜' E] [SMul 𝕜 E] [IsScalarTower 𝕜 𝕜' E]

/-- Reinterpret a seminorm over a field `𝕜'` as a seminorm over a smaller field `𝕜`. This will
typically be used with `RCLike 𝕜'` and `𝕜 = ℝ`. -/
/-
**Seminorm.restrictScalars** 是 Mathlib 中的一个定义，位于命名空间 `Seminorm`。
形式化陈述：(𝕜 : Type u_3) →   {E : Type u_7} →     {𝕜' : Type u_12} →       [inst : N
ormedField 𝕜] →         [inst_1 : SeminormedRing 𝕜'] →           [inst_2 : SMul 
𝕜 𝕜'] →             [NormSMulClass 𝕜 𝕜'] →               [NormOneClass 𝕜'] →    
             [inst_5 : AddCommGroup E] →                   [inst_6 : _root_.Modu
le 𝕜' E] →                     [inst_7 : SMul 𝕜 E] → [IsScalarTower 𝕜 𝕜' E] → Se
minorm 𝕜' E → Seminorm 𝕜 E
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Reinterpret a seminorm over a field `𝕜'` as a seminorm over a smaller field `𝕜`.
 This will
typically be used with `RCLike 𝕜'` and `𝕜 = ℝ`.
-/
protected def restrictScalars (p : Seminorm 𝕜' E) : Seminorm 𝕜 E :=
  { p with
    smul' := fun a x => by rw [← smul_one_smul 𝕜' a x, p.smul', norm_smul, norm_one, mul_one] }

@[simp]
/-
**Seminorm.coe_restrictScalars** 是 Mathlib 中的一个定理，位于命名空间 `Seminorm`。
形式化陈述：coe_restrictScalars (p : Seminorm 𝕜' E) : (p.restrictScalars 𝕜 : E -> Real
) = p
参数：p : Seminorm 𝕜' E。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_restrictScalars (p : Seminorm 𝕜' E) : (p.restrictScalars 𝕜 : E → ℝ) = p :=
  rfl

@[simp]
/-
**Seminorm.restrictScalars_ball** 是 Mathlib 中的一个定理，位于命名空间 `Seminorm`。
形式化陈述：restrictScalars_ball (p : Seminorm 𝕜' E) : (p.restrictScalars 𝕜).ball = p.
ball
参数：p : Seminorm 𝕜' E。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem restrictScalars_ball (p : Seminorm 𝕜' E) : (p.restrictScalars 𝕜).ball = p.ball :=
  rfl

@[simp]
/-
**Seminorm.restrictScalars_closedBall** 是 Mathlib 中的一个定理，位于命名空间 `Seminorm`。
形式化陈述：restrictScalars_closedBall (p : Seminorm 𝕜' E) : (p.restrictScalars 𝕜).clo
sedBall = p.closedBall
参数：p : Seminorm 𝕜' E。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem restrictScalars_closedBall (p : Seminorm 𝕜' E) :
    (p.restrictScalars 𝕜).closedBall = p.closedBall :=
  rfl

end RestrictScalars

/-! ### Continuity criteria for seminorms -/


section Continuity

variable [NontriviallyNormedField 𝕜] [SeminormedRing 𝕝] [AddCommGroup E] [Module 𝕜 E]
variable [Module 𝕝 E]

/-- A seminorm is continuous at `0` if `p.closedBall 0 r ∈ 𝓝 0` for *all* `r > 0`.
Over a `NontriviallyNormedField` it is actually enough to check that this is true
for *some* `r`, see `Seminorm.continuousAt_zero'`. -/
/-
**Seminorm.continuousAt_zero_of_forall'** 是 Mathlib 中的一个定理，位于命名空间 `Seminorm`。
形式化陈述：continuousAt_zero_of_forall' [TopologicalSpace E] {p : Seminorm 𝕝 E} (hp :
 forall r > 0, p.closedBall 0 r in (𝓝 0 : Filter E)) : ContinuousAt p 0
参数：hp : forall r > 0, p.closedBall 0 r in (𝓝 0 : Filter E)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ContinuousAt.eq_1`：∀ {X : Type u_1} {Y : Type u_2} [inst : TopologicalSp
ace X] [inst_1 : TopologicalSpace Y] (f : X → Y) (x : X),   ContinuousAt f x = F
ilter.T…
· 使用定理 `Filter.HasBasis.tendsto_right_iff`：∀ {α : Type u_1} {β : Type u_2} {ι' :
 Sort u_5} {la : Filter α} {lb : Filter β} {pb : ι' → Prop} {sb : ι' → Set β}   
{f : α → β}, lb.HasBasi…
· 使用定理 `Metric.nhds_basis_closedBall`：nhds_basis_closedBall : (𝓝 x).HasBasis (fu
n ε : Real => 0 < ε) (closedBall x)
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `AddGroupSeminormClass.toZeroHomClass`：∀ {F : Type u_2} {α : Type u_3} {β
 : Type u_4} [inst : FunLike F α β] [inst_1 : AddGroup α] [inst_2 : AddCommMonoi
d β]   [inst_3 : PartialOr…
· 使用定理 `SeminormClass.toAddGroupSeminormClass`：∀ {F : Type u_12} {𝕜 : outParam (
Type u_13)} {E : outParam (Type u_14)} {inst : SeminormedRing 𝕜} {inst_1 : AddGr
oup E}   {inst_2 : SMul 𝕜 E…
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Seminorm.closedBall_zero_eq_preimage_closedBall`：closedBall_zero_eq_prei
mage_closedBall {r : Real} : p.closedBall 0 r = p ⁻¹' Metric.closedBall 0 r

--- 原说明 ---
A seminorm is continuous at `0` if `p.closedBall 0 r ∈ 𝓝 0` for *all* `r > 0`.
Over a `NontriviallyNormedField` it is actually enough to check that this is tru
e
for *some* `r`, see `Seminorm.continuousAt_zero'`.
-/
theorem continuousAt_zero_of_forall' [TopologicalSpace E] {p : Seminorm 𝕝 E}
    (hp : ∀ r > 0, p.closedBall 0 r ∈ (𝓝 0 : Filter E)) :
    ContinuousAt p 0 := by
  simp_rw [Seminorm.closedBall_zero_eq_preimage_closedBall] at hp
  rwa [ContinuousAt, Metric.nhds_basis_closedBall.tendsto_right_iff, map_zero]
/-
**Seminorm.continuousAt_zero'** 是 Mathlib 中的一个定理，位于命名空间 `Seminorm`。
形式化陈述：continuousAt_zero' [TopologicalSpace E] [ContinuousConstSMul 𝕜 E] {p : Sem
inorm 𝕜 E} {r : Real} (hp : p.closedBall 0 r in (𝓝 0 : Filter E)) : ContinuousAt
 p 0
参数：hp : p.closedBall 0 r in (𝓝 0 : Filter E)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Seminorm.continuousAt_zero_of_forall'`：continuousAt_zero_of_forall' [Top
ologicalSpace E] {p : Seminorm 𝕝 E} (hp : forall r > 0, p.closedBall 0 r in (𝓝 0
 : Filter E)) : ContinuousA…
· 使用定理 `le_or_gt`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), a ≤ b ∨ b <
 a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `NormOneClass.norm_one`：∀ {α : Type u_5} {inst : Norm α} {inst_1 : One α}
 [self : NormOneClass α], ‖1‖ = 1
· 使用定理 `NormedDivisionRing.to_normOneClass`：∀ {α : Type u_2} [inst : NormedDivis
ionRing α], NormOneClass α
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `LE.le.trans_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b 
→ b < c → a < c
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用引理 `lt_div_iff₀`：lt_div_iff₀ (hc : 0 < c) : a < b / c ↔ a * c < b
· 使用定理 `MulPosReflectLE.toMulPosReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [MulPosReflectLE α], MulPosReflectLT α
· 使用定理 `MulPosStrictMono.toMulPosReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [MulPosStrictMono α], MulPosReflectLE α
· 使用定理 `IsStrictOrderedRing.toMulPosStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], MulPosStrictMono 
R
· 使用定理 `NormedField.exists_norm_lt`：exists_norm_lt {r : Real} (hr : 0 < r) : exi
sts x : α, 0 < ‖x‖ ∧ ‖x‖ < r
· 使用引理 `div_pos`：div_pos (ha : 0 < a) (hb : 0 < b) : 0 < a / b
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `Filter.mem_of_superset._gcongr_1`：∀ {α : Type u_1} {f : Filter α} {x y :
 Set α}, x ⊆ y → x ∈ f → y ∈ f
· 使用定理 `Seminorm.closedBall_mono`：closedBall_mono {p : Seminorm 𝕜 E} {r₁ r₂ : Re
al} (h : r₁ <= r₂) : p.closedBall x r₁ subseteq p.closedBall x r₂
· 使用定理 `le_of_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `Seminorm.smul_closedBall_zero`：smul_closedBall_zero {p : Seminorm 𝕜 E} {
k : 𝕜} {r : Real} (hk : 0 < ‖k‖) : k • p.closedBall 0 r = p.closedBall 0 (‖k‖ * 
r)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `set_smul_mem_nhds_zero_iff`：set_smul_mem_nhds_zero_iff {s : Set α} {c : 
G₀} (hc : c != 0) : c • s in 𝓝 (0 : α) ↔ s in 𝓝 (0 : α)
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `norm_pos_iff`：∀ {E : Type u_5} [inst : NormedAddGroup E] {a : E}, 0 < ‖a
‖ ↔ a ≠ 0
-/
theorem continuousAt_zero' [TopologicalSpace E] [ContinuousConstSMul 𝕜 E] {p : Seminorm 𝕜 E}
    {r : ℝ} (hp : p.closedBall 0 r ∈ (𝓝 0 : Filter E)) : ContinuousAt p 0 := by
  refine continuousAt_zero_of_forall' fun ε hε ↦ ?_
  obtain ⟨k, hk₀, hk⟩ : ∃ k : 𝕜, 0 < ‖k‖ ∧ ‖k‖ * r < ε := by
    rcases le_or_gt r 0 with hr | hr
    · use 1; simpa using hr.trans_lt hε
    · simpa [lt_div_iff₀ hr] using exists_norm_lt 𝕜 (div_pos hε hr)
  grw [← hk]
  rwa [← set_smul_mem_nhds_zero_iff (norm_pos_iff.1 hk₀), smul_closedBall_zero hk₀] at hp

/-- A seminorm is continuous at `0` if `p.ball 0 r ∈ 𝓝 0` for *all* `r > 0`.
Over a `NontriviallyNormedField` it is actually enough to check that this is true
for *some* `r`, see `Seminorm.continuousAt_zero'`. -/
/-
**Seminorm.continuousAt_zero_of_forall** 是 Mathlib 中的一个定理，位于命名空间 `Seminorm`。
形式化陈述：continuousAt_zero_of_forall [TopologicalSpace E] {p : Seminorm 𝕝 E} (hp : 
forall r > 0, p.ball 0 r in (𝓝 0 : Filter E)) : ContinuousAt p 0
参数：hp : forall r > 0, p.ball 0 r in (𝓝 0 : Filter E)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Seminorm.continuousAt_zero_of_forall'`：continuousAt_zero_of_forall' [Top
ologicalSpace E] {p : Seminorm 𝕝 E} (hp : forall r > 0, p.closedBall 0 r in (𝓝 0
 : Filter E)) : ContinuousA…
· 使用定理 `Filter.mem_of_superset`：mem_of_superset {x y : Set α} (hx : x in f) (hxy
 : x subseteq y) : y in f
· 使用定理 `Seminorm.ball_subset_closedBall`：ball_subset_closedBall (x r) : ball p x
 r subseteq closedBall p x r

--- 原说明 ---
A seminorm is continuous at `0` if `p.ball 0 r ∈ 𝓝 0` for *all* `r > 0`.
Over a `NontriviallyNormedField` it is actually enough to check that this is tru
e
for *some* `r`, see `Seminorm.continuousAt_zero'`.
-/
theorem continuousAt_zero_of_forall [TopologicalSpace E] {p : Seminorm 𝕝 E}
    (hp : ∀ r > 0, p.ball 0 r ∈ (𝓝 0 : Filter E)) :
    ContinuousAt p 0 :=
  continuousAt_zero_of_forall'
    (fun r hr ↦ Filter.mem_of_superset (hp r hr) <| p.ball_subset_closedBall _ _)
/-
**Seminorm.continuousAt_zero** 是 Mathlib 中的一个定理，位于命名空间 `Seminorm`。
形式化陈述：continuousAt_zero [TopologicalSpace E] [ContinuousConstSMul 𝕜 E] {p : Semi
norm 𝕜 E} {r : Real} (hp : p.ball 0 r in (𝓝 0 : Filter E)) : ContinuousAt p 0
参数：hp : p.ball 0 r in (𝓝 0 : Filter E)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Seminorm.continuousAt_zero'`：continuousAt_zero' [TopologicalSpace E] [Co
ntinuousConstSMul 𝕜 E] {p : Seminorm 𝕜 E} {r : Real} (hp : p.closedBall 0 r in (
𝓝 0 : Filter E)) …
· 使用定理 `Filter.mem_of_superset`：mem_of_superset {x y : Set α} (hx : x in f) (hxy
 : x subseteq y) : y in f
· 使用定理 `Seminorm.ball_subset_closedBall`：ball_subset_closedBall (x r) : ball p x
 r subseteq closedBall p x r
-/
theorem continuousAt_zero [TopologicalSpace E] [ContinuousConstSMul 𝕜 E] {p : Seminorm 𝕜 E} {r : ℝ}
    (hp : p.ball 0 r ∈ (𝓝 0 : Filter E)) : ContinuousAt p 0 :=
  continuousAt_zero' (Filter.mem_of_superset hp <| p.ball_subset_closedBall _ _)
/-
**Seminorm.uniformContinuous_of_continuousAt_zero** 是 Mathlib 中的一个定理，位于命名空间 `Sem
inorm`。
形式化陈述：∀ {𝕝 : Type u_6} {E : Type u_7} [inst : SeminormedRing 𝕝] [inst_1 : AddCom
mGroup E] [inst_2 : _root_.Module 𝕝 E]   [inst_3 : UniformSpace E] [IsUniformAdd
Group E] {p : Seminorm 𝕝 E}, ContinuousAt (⇑p) 0 → UniformContinuous ⇑p
参数：⇑p。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `AddGroupSeminormClass.toZeroHomClass`：∀ {F : Type u_2} {α : Type u_3} {β
 : Type u_4} [inst : FunLike F α β] [inst_1 : AddGroup α] [inst_2 : AddCommMonoi
d β]   [inst_3 : PartialOr…
· 使用定理 `SeminormClass.toAddGroupSeminormClass`：∀ {F : Type u_12} {𝕜 : outParam (
Type u_13)} {E : outParam (Type u_14)} {inst : SeminormedRing 𝕜} {inst_1 : AddGr
oup E}   {inst_2 : SMul 𝕜 E…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `UniformContinuous.eq_1`：∀ {α : Type ua} {β : Type ub} [inst : UniformSpa
ce α] [inst_1 : UniformSpace β] (f : α → β),   UniformContinuous f = Filter.Tend
sto (fun x =…
· 使用定理 `uniformity_eq_comap_nhds_zero_swapped`：∀ (Gᵣ : Type u_3) [inst : Uniform
Space Gᵣ] [inst_1 : AddGroup Gᵣ] [IsRightUniformAddGroup Gᵣ],   uniformity Gᵣ = 
Filter.comap (fun x => x.1 …
· 使用定理 `IsUniformAddGroup.isRightUniformAddGroup`：∀ (α : Type u_1) [inst : Unifo
rmSpace α] [inst_1 : AddGroup α] [IsUniformAddGroup α], IsRightUniformAddGroup α
· 使用定理 `Metric.uniformity_eq_comap_nhds_zero`：Metric.uniformity_eq_comap_nhds_ze
ro : 𝓤 α = comap (fun p : α × α => dist p.1 p.2) (𝓝 (0 : Real))
· 使用定理 `Filter.tendsto_comap_iff`：tendsto_comap_iff {f : α -> β} {g : β -> γ} {a
 : Filter α} {c : Filter γ} : Tendsto f a (c.comap g) ↔ Tendsto (g ∘ f) a c
· 使用定理 `tendsto_of_tendsto_of_tendsto_of_le_of_le`：tendsto_of_tendsto_of_tendsto
_of_le_of_le [OrderTopology α] {f g h : β -> α} {b : Filter β} {a : α} (hg : Ten
dsto g b (𝓝 a)) (hh : Tendsto h…
· 使用定理 `instOrderTopologyReal`：OrderTopology ℝ
· 使用定理 `tendsto_const_nhds`：tendsto_const_nhds {f : Filter α} : Tendsto (fun _ :
 α => x) f (𝓝 x)
· 使用定理 `Filter.Tendsto.comp`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {f :
 α → β} {g : β → γ} {x : Filter α} {y : Filter β} {z : Filter γ},   Filter.Tends
to g y z …
· 使用定理 `Filter.tendsto_comap`：tendsto_comap {f : α -> β} {x : Filter β} : Tendst
o f (comap f x) x
· 使用定理 `dist_nonneg`：dist_nonneg {x y : α} : 0 <= dist x y
· 使用定理 `Seminorm.norm_sub_map_le_sub`：norm_sub_map_le_sub (p : Seminorm 𝕜 E) (x 
y : E) : ‖p x - p y‖ <= p (x - y)
-/
protected theorem uniformContinuous_of_continuousAt_zero [UniformSpace E] [IsUniformAddGroup E]
    {p : Seminorm 𝕝 E} (hp : ContinuousAt p 0) : UniformContinuous p := by
  have hp : Filter.Tendsto p (𝓝 0) (𝓝 0) := map_zero p ▸ hp
  rw [UniformContinuous, uniformity_eq_comap_nhds_zero_swapped,
    Metric.uniformity_eq_comap_nhds_zero, Filter.tendsto_comap_iff]
  exact
    tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds (hp.comp Filter.tendsto_comap)
      (fun xy => dist_nonneg) fun xy => p.norm_sub_map_le_sub _ _
/-
**Seminorm.continuous_of_continuousAt_zero** 是 Mathlib 中的一个定理，位于命名空间 `Seminorm`。
形式化陈述：∀ {𝕝 : Type u_6} {E : Type u_7} [inst : SeminormedRing 𝕝] [inst_1 : AddCom
mGroup E] [inst_2 : _root_.Module 𝕝 E]   [inst_3 : TopologicalSpace E] [IsTopolo
gicalAddGroup E] {p : Seminorm 𝕝 E}, ContinuousAt (⇑p) 0 → Continuous ⇑p
参数：⇑p。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `isUniformAddGroup_of_addCommGroup`：∀ {G : Type u_1} [inst : AddCommGroup
 G] [inst_1 : TopologicalSpace G] [inst_2 : IsTopologicalAddGroup G],   IsUnifor
mAddGroup G
· 使用定理 `UniformContinuous.continuous`：UniformContinuous.continuous (hf : Uniform
Continuous f) : Continuous f
· 使用定理 `Seminorm.uniformContinuous_of_continuousAt_zero`：∀ {𝕝 : Type u_6} {E : T
ype u_7} [inst : SeminormedRing 𝕝] [inst_1 : AddCommGroup E] [inst_2 : _root_.Mo
dule 𝕝 E]   [inst_3 : UniformSpace E]…
-/
protected theorem continuous_of_continuousAt_zero [TopologicalSpace E] [IsTopologicalAddGroup E]
    {p : Seminorm 𝕝 E} (hp : ContinuousAt p 0) : Continuous p := by
  let := IsTopologicalAddGroup.rightUniformSpace E
  have : IsUniformAddGroup E := isUniformAddGroup_of_addCommGroup
  exact (Seminorm.uniformContinuous_of_continuousAt_zero hp).continuous

/-- A seminorm is uniformly continuous if `p.ball 0 r ∈ 𝓝 0` for *all* `r > 0`.
Over a `NontriviallyNormedField` it is actually enough to check that this is true
for *some* `r`, see `Seminorm.uniformContinuous`. -/
/-
**Seminorm.uniformContinuous_of_forall** 是 Mathlib 中的一个定理，位于命名空间 `Seminorm`。
形式化陈述：∀ {𝕝 : Type u_6} {E : Type u_7} [inst : SeminormedRing 𝕝] [inst_1 : AddCom
mGroup E] [inst_2 : _root_.Module 𝕝 E]   [inst_3 : UniformSpace E] [IsUniformAdd
Group E] {p : Seminorm 𝕝 E},   (∀ r > 0, p.ball 0 r ∈ nhds 0) → UniformContinuou
s ⇑p
参数：∀ r > 0, p.ball 0 r ∈ nhds 0。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Seminorm.uniformContinuous_of_continuousAt_zero`：∀ {𝕝 : Type u_6} {E : T
ype u_7} [inst : SeminormedRing 𝕝] [inst_1 : AddCommGroup E] [inst_2 : _root_.Mo
dule 𝕝 E]   [inst_3 : UniformSpace E]…
· 使用定理 `Seminorm.continuousAt_zero_of_forall`：continuousAt_zero_of_forall [Topol
ogicalSpace E] {p : Seminorm 𝕝 E} (hp : forall r > 0, p.ball 0 r in (𝓝 0 : Filte
r E)) : ContinuousAt p 0

--- 原说明 ---
A seminorm is uniformly continuous if `p.ball 0 r ∈ 𝓝 0` for *all* `r > 0`.
Over a `NontriviallyNormedField` it is actually enough to check that this is tru
e
for *some* `r`, see `Seminorm.uniformContinuous`.
-/
protected theorem uniformContinuous_of_forall [UniformSpace E] [IsUniformAddGroup E]
    {p : Seminorm 𝕝 E} (hp : ∀ r > 0, p.ball 0 r ∈ (𝓝 0 : Filter E)) :
    UniformContinuous p :=
  Seminorm.uniformContinuous_of_continuousAt_zero (continuousAt_zero_of_forall hp)
/-
**Seminorm.uniformContinuous** 是 Mathlib 中的一个定理，位于命名空间 `Seminorm`。
形式化陈述：∀ {𝕜 : Type u_3} {E : Type u_7} [inst : NontriviallyNormedField 𝕜] [inst_1
 : AddCommGroup E]   [inst_2 : _root_.Module 𝕜 E] [inst_3 : UniformSpace E] [IsU
niformAddGroup E] [ContinuousConstSMul 𝕜 E]   {p : Seminorm 𝕜 E} {r : ℝ}, p.ball
 0 r ∈ nhds 0 → UniformContinuous ⇑p
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Seminorm.uniformContinuous_of_continuousAt_zero`：∀ {𝕝 : Type u_6} {E : T
ype u_7} [inst : SeminormedRing 𝕝] [inst_1 : AddCommGroup E] [inst_2 : _root_.Mo
dule 𝕝 E]   [inst_3 : UniformSpace E]…
· 使用定理 `Seminorm.continuousAt_zero`：continuousAt_zero [TopologicalSpace E] [Cont
inuousConstSMul 𝕜 E] {p : Seminorm 𝕜 E} {r : Real} (hp : p.ball 0 r in (𝓝 0 : Fi
lter E)) : Conti…
-/
protected theorem uniformContinuous [UniformSpace E] [IsUniformAddGroup E]
    [ContinuousConstSMul 𝕜 E] {p : Seminorm 𝕜 E} {r : ℝ} (hp : p.ball 0 r ∈ (𝓝 0 : Filter E)) :
    UniformContinuous p :=
  Seminorm.uniformContinuous_of_continuousAt_zero (continuousAt_zero hp)

/-- A seminorm is uniformly continuous if `p.closedBall 0 r ∈ 𝓝 0` for *all* `r > 0`.
Over a `NontriviallyNormedField` it is actually enough to check that this is true
for *some* `r`, see `Seminorm.uniformContinuous'`. -/
/-
**Seminorm.uniformContinuous_of_forall'** 是 Mathlib 中的一个定理，位于命名空间 `Seminorm`。
形式化陈述：∀ {𝕝 : Type u_6} {E : Type u_7} [inst : SeminormedRing 𝕝] [inst_1 : AddCom
mGroup E] [inst_2 : _root_.Module 𝕝 E]   [inst_3 : UniformSpace E] [IsUniformAdd
Group E] {p : Seminorm 𝕝 E},   (∀ r > 0, p.closedBall 0 r ∈ nhds 0) → UniformCon
tinuous ⇑p
参数：∀ r > 0, p.closedBall 0 r ∈ nhds 0。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Seminorm.uniformContinuous_of_continuousAt_zero`：∀ {𝕝 : Type u_6} {E : T
ype u_7} [inst : SeminormedRing 𝕝] [inst_1 : AddCommGroup E] [inst_2 : _root_.Mo
dule 𝕝 E]   [inst_3 : UniformSpace E]…
· 使用定理 `Seminorm.continuousAt_zero_of_forall'`：continuousAt_zero_of_forall' [Top
ologicalSpace E] {p : Seminorm 𝕝 E} (hp : forall r > 0, p.closedBall 0 r in (𝓝 0
 : Filter E)) : ContinuousA…

--- 原说明 ---
A seminorm is uniformly continuous if `p.closedBall 0 r ∈ 𝓝 0` for *all* `r > 0`
.
Over a `NontriviallyNormedField` it is actually enough to check that this is tru
e
for *some* `r`, see `Seminorm.uniformContinuous'`.
-/
protected theorem uniformContinuous_of_forall' [UniformSpace E] [IsUniformAddGroup E]
    {p : Seminorm 𝕝 E} (hp : ∀ r > 0, p.closedBall 0 r ∈ (𝓝 0 : Filter E)) :
    UniformContinuous p :=
  Seminorm.uniformContinuous_of_continuousAt_zero (continuousAt_zero_of_forall' hp)
/-
**Seminorm.uniformContinuous'** 是 Mathlib 中的一个定理，位于命名空间 `Seminorm`。
形式化陈述：∀ {𝕜 : Type u_3} {E : Type u_7} [inst : NontriviallyNormedField 𝕜] [inst_1
 : AddCommGroup E]   [inst_2 : _root_.Module 𝕜 E] [inst_3 : UniformSpace E] [IsU
niformAddGroup E] [ContinuousConstSMul 𝕜 E]   {p : Seminorm 𝕜 E} {r : ℝ}, p.clos
edBall 0 r ∈ nhds 0 → UniformContinuous ⇑p
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Seminorm.uniformContinuous_of_continuousAt_zero`：∀ {𝕝 : Type u_6} {E : T
ype u_7} [inst : SeminormedRing 𝕝] [inst_1 : AddCommGroup E] [inst_2 : _root_.Mo
dule 𝕝 E]   [inst_3 : UniformSpace E]…
· 使用定理 `Seminorm.continuousAt_zero'`：continuousAt_zero' [TopologicalSpace E] [Co
ntinuousConstSMul 𝕜 E] {p : Seminorm 𝕜 E} {r : Real} (hp : p.closedBall 0 r in (
𝓝 0 : Filter E)) …
-/
protected theorem uniformContinuous' [UniformSpace E] [IsUniformAddGroup E]
    [ContinuousConstSMul 𝕜 E] {p : Seminorm 𝕜 E} {r : ℝ}
    (hp : p.closedBall 0 r ∈ (𝓝 0 : Filter E)) : UniformContinuous p :=
  Seminorm.uniformContinuous_of_continuousAt_zero (continuousAt_zero' hp)

/-- A seminorm is continuous if `p.ball 0 r ∈ 𝓝 0` for *all* `r > 0`.
Over a `NontriviallyNormedField` it is actually enough to check that this is true
for *some* `r`, see `Seminorm.continuous`. -/
/-
**Seminorm.continuous_of_forall** 是 Mathlib 中的一个定理，位于命名空间 `Seminorm`。
形式化陈述：∀ {𝕝 : Type u_6} {E : Type u_7} [inst : SeminormedRing 𝕝] [inst_1 : AddCom
mGroup E] [inst_2 : _root_.Module 𝕝 E]   [inst_3 : TopologicalSpace E] [IsTopolo
gicalAddGroup E] {p : Seminorm 𝕝 E},   (∀ r > 0, p.ball 0 r ∈ nhds 0) → Continuo
us ⇑p
参数：∀ r > 0, p.ball 0 r ∈ nhds 0。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Seminorm.continuous_of_continuousAt_zero`：∀ {𝕝 : Type u_6} {E : Type u_7
} [inst : SeminormedRing 𝕝] [inst_1 : AddCommGroup E] [inst_2 : _root_.Module 𝕝 
E]   [inst_3 : TopologicalSpac…
· 使用定理 `Seminorm.continuousAt_zero_of_forall`：continuousAt_zero_of_forall [Topol
ogicalSpace E] {p : Seminorm 𝕝 E} (hp : forall r > 0, p.ball 0 r in (𝓝 0 : Filte
r E)) : ContinuousAt p 0

--- 原说明 ---
A seminorm is continuous if `p.ball 0 r ∈ 𝓝 0` for *all* `r > 0`.
Over a `NontriviallyNormedField` it is actually enough to check that this is tru
e
for *some* `r`, see `Seminorm.continuous`.
-/
protected theorem continuous_of_forall [TopologicalSpace E] [IsTopologicalAddGroup E]
    {p : Seminorm 𝕝 E} (hp : ∀ r > 0, p.ball 0 r ∈ (𝓝 0 : Filter E)) :
    Continuous p :=
  Seminorm.continuous_of_continuousAt_zero (continuousAt_zero_of_forall hp)
/-
**Seminorm.continuous** 是 Mathlib 中的一个定理，位于命名空间 `Seminorm`。
形式化陈述：∀ {𝕜 : Type u_3} {E : Type u_7} [inst : NontriviallyNormedField 𝕜] [inst_1
 : AddCommGroup E]   [inst_2 : _root_.Module 𝕜 E] [inst_3 : TopologicalSpace E] 
[IsTopologicalAddGroup E] [ContinuousConstSMul 𝕜 E]   {p : Seminorm 𝕜 E} {r : ℝ}
, p.ball 0 r ∈ nhds 0 → Continuous ⇑p
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Seminorm.continuous_of_continuousAt_zero`：∀ {𝕝 : Type u_6} {E : Type u_7
} [inst : SeminormedRing 𝕝] [inst_1 : AddCommGroup E] [inst_2 : _root_.Module 𝕝 
E]   [inst_3 : TopologicalSpac…
· 使用定理 `Seminorm.continuousAt_zero`：continuousAt_zero [TopologicalSpace E] [Cont
inuousConstSMul 𝕜 E] {p : Seminorm 𝕜 E} {r : Real} (hp : p.ball 0 r in (𝓝 0 : Fi
lter E)) : Conti…
-/
protected theorem continuous [TopologicalSpace E] [IsTopologicalAddGroup E]
    [ContinuousConstSMul 𝕜 E] {p : Seminorm 𝕜 E} {r : ℝ} (hp : p.ball 0 r ∈ (𝓝 0 : Filter E)) :
    Continuous p :=
  Seminorm.continuous_of_continuousAt_zero (continuousAt_zero hp)
/-
**Seminorm.continuous_iff** 是 Mathlib 中的一个定理，位于命名空间 `Seminorm`。
形式化陈述：∀ {𝕜 : Type u_3} {E : Type u_7} [inst : NontriviallyNormedField 𝕜] [inst_1
 : AddCommGroup E]   [inst_2 : _root_.Module 𝕜 E] [inst_3 : TopologicalSpace E] 
[IsTopologicalAddGroup E] [ContinuousConstSMul 𝕜 E]   {p : Seminorm 𝕜 E} {r : ℝ}
, 0 < r → (Continuous ⇑p ↔ p.ball 0 r ∈ nhds 0)
参数：Continuous ⇑p ↔ p.ball 0 r ∈ nhds 0。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.Tendsto.eventually_lt_const`：∀ {α : Type u} {γ : Type w} [inst : 
TopologicalSpace α] [inst_1 : LinearOrder α] [ClosedIciTopology α] {l : Filter γ
}   {f : γ → α} {u v : α…
· 使用定理 `instClosedIciTopology`：∀ {α : Type u} [inst : TopologicalSpace α] [inst_
1 : Preorder α] [t : OrderClosedTopology α], ClosedIciTopology α
· 使用定理 `OrderTopology.to_orderClosedTopology`：∀ {α : Type u} [inst : Topological
Space α] [inst_1 : LinearOrder α] [OrderTopology α], OrderClosedTopology α
· 使用定理 `instOrderTopologyReal`：OrderTopology ℝ
· 使用定理 `Continuous.tendsto'`：Continuous.tendsto' (hf : Continuous f) (x : X) (y 
: Y) (h : f x = y) : Tendsto f (𝓝 x) (𝓝 y)
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `AddGroupSeminormClass.toZeroHomClass`：∀ {F : Type u_2} {α : Type u_3} {β
 : Type u_4} [inst : FunLike F α β] [inst_1 : AddGroup α] [inst_2 : AddCommMonoi
d β]   [inst_3 : PartialOr…
· 使用定理 `SeminormClass.toAddGroupSeminormClass`：∀ {F : Type u_12} {𝕜 : outParam (
Type u_13)} {E : outParam (Type u_14)} {inst : SeminormedRing 𝕜} {inst_1 : AddGr
oup E}   {inst_2 : SMul 𝕜 E…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Seminorm.ball_zero_eq`：ball_zero_eq : ball p 0 r = { y : E | p y < r }
· 使用定理 `Seminorm.continuous`：∀ {𝕜 : Type u_3} {E : Type u_7} [inst : Nontriviall
yNormedField 𝕜] [inst_1 : AddCommGroup E]   [inst_2 : _root_.Module 𝕜 E] [inst_3
 : Topolo…
-/
protected theorem continuous_iff [TopologicalSpace E] [IsTopologicalAddGroup E]
    [ContinuousConstSMul 𝕜 E] {p : Seminorm 𝕜 E} {r : ℝ} (hr : 0 < r) :
    Continuous p ↔ p.ball 0 r ∈ 𝓝 0 :=
  ⟨fun H ↦ p.ball_zero_eq ▸ (H.tendsto' 0 0 (map_zero p)).eventually_lt_const hr, p.continuous⟩

/-- A seminorm is continuous if `p.closedBall 0 r ∈ 𝓝 0` for *all* `r > 0`.
Over a `NontriviallyNormedField` it is actually enough to check that this is true
for *some* `r`, see `Seminorm.continuous'`. -/
/-
**Seminorm.continuous_of_forall'** 是 Mathlib 中的一个定理，位于命名空间 `Seminorm`。
形式化陈述：∀ {𝕝 : Type u_6} {E : Type u_7} [inst : SeminormedRing 𝕝] [inst_1 : AddCom
mGroup E] [inst_2 : _root_.Module 𝕝 E]   [inst_3 : TopologicalSpace E] [IsTopolo
gicalAddGroup E] {p : Seminorm 𝕝 E},   (∀ r > 0, p.closedBall 0 r ∈ nhds 0) → Co
ntinuous ⇑p
参数：∀ r > 0, p.closedBall 0 r ∈ nhds 0。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Seminorm.continuous_of_continuousAt_zero`：∀ {𝕝 : Type u_6} {E : Type u_7
} [inst : SeminormedRing 𝕝] [inst_1 : AddCommGroup E] [inst_2 : _root_.Module 𝕝 
E]   [inst_3 : TopologicalSpac…
· 使用定理 `Seminorm.continuousAt_zero_of_forall'`：continuousAt_zero_of_forall' [Top
ologicalSpace E] {p : Seminorm 𝕝 E} (hp : forall r > 0, p.closedBall 0 r in (𝓝 0
 : Filter E)) : ContinuousA…

--- 原说明 ---
A seminorm is continuous if `p.closedBall 0 r ∈ 𝓝 0` for *all* `r > 0`.
Over a `NontriviallyNormedField` it is actually enough to check that this is tru
e
for *some* `r`, see `Seminorm.continuous'`.
-/
protected theorem continuous_of_forall' [TopologicalSpace E] [IsTopologicalAddGroup E]
    {p : Seminorm 𝕝 E} (hp : ∀ r > 0, p.closedBall 0 r ∈ (𝓝 0 : Filter E)) :
    Continuous p :=
  Seminorm.continuous_of_continuousAt_zero (continuousAt_zero_of_forall' hp)
/-
**Seminorm.continuous'** 是 Mathlib 中的一个定理，位于命名空间 `Seminorm`。
形式化陈述：∀ {𝕜 : Type u_3} {E : Type u_7} [inst : NontriviallyNormedField 𝕜] [inst_1
 : AddCommGroup E]   [inst_2 : _root_.Module 𝕜 E] [inst_3 : TopologicalSpace E] 
[IsTopologicalAddGroup E] [ContinuousConstSMul 𝕜 E]   {p : Seminorm 𝕜 E} {r : ℝ}
, p.closedBall 0 r ∈ nhds 0 → Continuous ⇑p
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Seminorm.continuous_of_continuousAt_zero`：∀ {𝕝 : Type u_6} {E : Type u_7
} [inst : SeminormedRing 𝕝] [inst_1 : AddCommGroup E] [inst_2 : _root_.Module 𝕝 
E]   [inst_3 : TopologicalSpac…
· 使用定理 `Seminorm.continuousAt_zero'`：continuousAt_zero' [TopologicalSpace E] [Co
ntinuousConstSMul 𝕜 E] {p : Seminorm 𝕜 E} {r : Real} (hp : p.closedBall 0 r in (
𝓝 0 : Filter E)) …
-/
protected theorem continuous' [TopologicalSpace E] [IsTopologicalAddGroup E]
    [ContinuousConstSMul 𝕜 E] {p : Seminorm 𝕜 E} {r : ℝ}
    (hp : p.closedBall 0 r ∈ (𝓝 0 : Filter E)) : Continuous p :=
  Seminorm.continuous_of_continuousAt_zero (continuousAt_zero' hp)
/-
**Seminorm.continuous_of_le** 是 Mathlib 中的一个定理，位于命名空间 `Seminorm`。
形式化陈述：continuous_of_le [TopologicalSpace E] [IsTopologicalAddGroup E] {p q : Sem
inorm 𝕝 E} (hq : Continuous q) (hpq : p <= q) : Continuous p
参数：hq : Continuous q；hpq : p <= q。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Seminorm.continuous_of_forall`：∀ {𝕝 : Type u_6} {E : Type u_7} [inst : S
eminormedRing 𝕝] [inst_1 : AddCommGroup E] [inst_2 : _root_.Module 𝕝 E]   [inst_
3 : TopologicalSpac…
· 使用定理 `Filter.mem_of_superset`：mem_of_superset {x y : Set α} (hx : x in f) (hxy
 : x subseteq y) : y in f
· 使用定理 `IsOpen.mem_nhds`：IsOpen.mem_nhds (hs : IsOpen s) (hx : x in s) : s in 𝓝 
x
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Seminorm.ball_zero_eq`：ball_zero_eq : ball p 0 r = { y : E | p y < r }
· 使用定理 `isOpen_lt`：isOpen_lt [TopologicalSpace β] {f g : β -> α} (hf : Continuou
s f) (hg : Continuous g) : IsOpen { b | f b < g b }
· 使用定理 `OrderTopology.to_orderClosedTopology`：∀ {α : Type u} [inst : Topological
Space α] [inst_1 : LinearOrder α] [OrderTopology α], OrderClosedTopology α
· 使用定理 `instOrderTopologyReal`：OrderTopology ℝ
· 使用定理 `continuous_const`：continuous_const (y : Y) : Continuous (fun x ↦ y)
· 使用定理 `Seminorm.mem_ball_self`：mem_ball_self (hr : 0 < r) : x in ball p x r
· 使用定理 `Seminorm.ball_antitone`：ball_antitone {p q : Seminorm 𝕜 E} (h : q <= p) 
: p.ball x r subseteq q.ball x r
-/
theorem continuous_of_le [TopologicalSpace E] [IsTopologicalAddGroup E]
    {p q : Seminorm 𝕝 E} (hq : Continuous q) (hpq : p ≤ q) : Continuous p := by
  refine Seminorm.continuous_of_forall (fun r hr ↦ Filter.mem_of_superset
    (IsOpen.mem_nhds ?_ <| q.mem_ball_self hr) (ball_antitone hpq))
  rw [ball_zero_eq]
  exact isOpen_lt hq continuous_const

/-- The sum over a finite set of continuous seminorms is continuous. -/
/-
**Seminorm.continuous_finsetSum** 是 Mathlib 中的一个定理，位于命名空间 `Seminorm`。
形式化陈述：continuous_finsetSum [TopologicalSpace E] {p : ι -> Seminorm 𝕝 E} {s : Fin
set ι} (hp : forall i in s, Continuous (p i)) : Continuous ((∑ i in s, p i : Sem
inorm 𝕝 E) : E -> Real)
参数：hp : forall i in s, Continuous (p i)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Seminorm.instIsZeroApplyReal`：∀ {𝕜 : Type u_3} {E : Type u_7} [inst : Se
minormedRing 𝕜] [inst_1 : AddGroup E] [inst_2 : SMul 𝕜 E],   IsZeroApply (Semino
rm 𝕜 E) E ℝ
· 使用定理 `Seminorm.instIsAddApplyReal`：∀ {𝕜 : Type u_3} {E : Type u_7} [inst : Sem
inormedRing 𝕜] [inst_1 : AddGroup E] [inst_2 : SMul 𝕜 E],   IsAddApply (Seminorm
 𝕜 E) E ℝ
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `map_sum`：∀ {ι : Type u_1} {M : Type u_3} {N : Type u_4} [inst : AddCommM
onoid M] [inst_1 : AddCommMonoid N] {G : Type u_7}   [inst_2 : FunLike G M N]…
· 使用定理 `AddMonoidHom.instAddMonoidHomClass`：∀ {M : Type u_4} {N : Type u_5} [ins
t : AddZero M] [inst_1 : AddZero N], AddMonoidHomClass (M →+ N) M N
· 使用定理 `Finset.sum_apply`：∀ {ι : Type u_1} {α : Type u_7} {M : α → Type u_8} [in
st : (a : α) → AddCommMonoid (M a)] (a : α) (s : Finset ι)   (g : ι → (a : α) → 
M a), …
· 使用定理 `continuous_finsetSum`：∀ {ι : Type u_1} {M : Type u_3} {X : Type u_5} [in
st : TopologicalSpace X] [inst_1 : TopologicalSpace M]   [inst_2 : AddCommMonoid
 M] [Conti…
· 使用定理 `IsSemitopologicalSemiring.toContinuousAdd`：∀ {R : Type u_2} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSemitopologic
alSemiring R], ContinuousAdd R
· 使用定理 `IsSemitopologicalRing.toIsSemitopologicalSemiring`：∀ {R : Type u_2} {ins
t : TopologicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopolog
icalRing R],   IsSemitopologicalSemirin…
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ

--- 原说明 ---
The sum over a finite set of continuous seminorms is continuous.
-/
theorem continuous_finsetSum [TopologicalSpace E]
    {p : ι → Seminorm 𝕝 E} {s : Finset ι} (hp : ∀ i ∈ s, Continuous (p i)) :
    Continuous ((∑ i ∈ s, p i : Seminorm 𝕝 E) : E → ℝ) := by
  change Continuous (fun x ↦ FunLike.coeAddMonoidHom _ _ _ (∑ i ∈ s, p i) x)
  simp_rw [map_sum, Finset.sum_apply]
  exact _root_.continuous_finsetSum s hp

/-- The supremum over a finite set of continuous seminorms is continuous. -/
/-
**Seminorm.continuous_finsetSup** 是 Mathlib 中的一个定理，位于命名空间 `Seminorm`。
形式化陈述：continuous_finsetSup [TopologicalSpace E] [IsTopologicalAddGroup E] {p : ι
 -> Seminorm 𝕝 E} {s : Finset ι} (hp : forall i in s, Continuous (p i)) : Contin
uous ((s.sup p : Seminorm 𝕝 E) : E -> Real)
参数：hp : forall i in s, Continuous (p i)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Seminorm.continuous_of_le`：continuous_of_le [TopologicalSpace E] [IsTopo
logicalAddGroup E] {p q : Seminorm 𝕝 E} (hq : Continuous q) (hpq : p <= q) : Con
tinuous p
· 使用定理 `Seminorm.continuous_finsetSum`：continuous_finsetSum [TopologicalSpace E]
 {p : ι -> Seminorm 𝕝 E} {s : Finset ι} (hp : forall i in s, Continuous (p i)) :
 Continuous ((∑ i i…
· 使用定理 `Seminorm.finset_sup_le_sum`：finset_sup_le_sum (p : ι -> Seminorm 𝕜 E) (s
 : Finset ι) : s.sup p <= ∑ i in s, p i

--- 原说明 ---
The supremum over a finite set of continuous seminorms is continuous.
-/
theorem continuous_finsetSup [TopologicalSpace E] [IsTopologicalAddGroup E]
    {p : ι → Seminorm 𝕝 E} {s : Finset ι} (hp : ∀ i ∈ s, Continuous (p i)) :
    Continuous ((s.sup p : Seminorm 𝕝 E) : E → ℝ) := by
  exact continuous_of_le (continuous_finsetSum hp) (finset_sup_le_sum p s)
/-
**Seminorm.ball_mem_nhds** 是 Mathlib 中的一个引理，位于命名空间 `Seminorm`。
形式化陈述：ball_mem_nhds [TopologicalSpace E] {p : Seminorm 𝕝 E} (hp : Continuous p) 
{r : Real} (hr : 0 < r) : p.ball 0 r in (𝓝 0 : Filter E)
参数：hp : Continuous p；hr : 0 < r。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Continuous.tendsto`：Continuous.tendsto (hf : Continuous f) (x) : Tendsto
 f (𝓝 x) (𝓝 (f x))
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `AddGroupSeminormClass.toZeroHomClass`：∀ {F : Type u_2} {α : Type u_3} {β
 : Type u_4} [inst : FunLike F α β] [inst_1 : AddGroup α] [inst_2 : AddCommMonoi
d β]   [inst_3 : PartialOr…
· 使用定理 `SeminormClass.toAddGroupSeminormClass`：∀ {F : Type u_12} {𝕜 : outParam (
Type u_13)} {E : outParam (Type u_14)} {inst : SeminormedRing 𝕜} {inst_1 : AddGr
oup E}   {inst_2 : SMul 𝕜 E…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Seminorm.ball_zero_eq`：ball_zero_eq : ball p 0 r = { y : E | p y < r }
· 使用定理 `Iio_mem_nhds`：∀ {α : Type u} [inst : TopologicalSpace α] [inst_1 : Linea
rOrder α] [ClosedIciTopology α] {a b : α},   b < a → Set.Iio a ∈ nhds b
· 使用定理 `instClosedIciTopology`：∀ {α : Type u} [inst : TopologicalSpace α] [inst_
1 : Preorder α] [t : OrderClosedTopology α], ClosedIciTopology α
· 使用定理 `OrderTopology.to_orderClosedTopology`：∀ {α : Type u} [inst : Topological
Space α] [inst_1 : LinearOrder α] [OrderTopology α], OrderClosedTopology α
· 使用定理 `instOrderTopologyReal`：OrderTopology ℝ
-/
lemma ball_mem_nhds [TopologicalSpace E] {p : Seminorm 𝕝 E} (hp : Continuous p) {r : ℝ}
    (hr : 0 < r) : p.ball 0 r ∈ (𝓝 0 : Filter E) := by
  have : Tendsto p (𝓝 0) (𝓝 0) := map_zero p ▸ hp.tendsto 0
  simpa only [p.ball_zero_eq] using! this (Iio_mem_nhds hr)
/-
**Seminorm.uniformSpace_eq_of_hasBasis** 是 Mathlib 中的一个引理，位于命名空间 `Seminorm`。
形式化陈述：uniformSpace_eq_of_hasBasis {ι} [UniformSpace E] [IsUniformAddGroup E] [Co
ntinuousConstSMul 𝕜 E] {p' : ι -> Prop} {s : ι -> Set E} (p : Seminorm 𝕜 E) (hb 
: (𝓝 0 : Filter E).HasBasis p' s) (h₁ : exists r, p.closedBall 0 r in 𝓝 0) (h₂ :
 forall i, p' i -> exists r > 0, p.ball 0 r subseteq s i) : ‹UniformSpace E› = p
.toAddGroupSeminorm.toSeminormedAddGroup.toUniformSpace
参数：p : Seminorm 𝕜 E；hb : (𝓝 0 : Filter E).HasBasis p' s；h₁ : exists r, p.closedB
all 0 r in 𝓝 0；h₂ : forall i, p' i -> exists r > 0, p.ball 0 r subseteq s i。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsUniformAddGroup.ext`：∀ {G : Type u_3} [inst : AddGroup G] {u v : Unifo
rmSpace G},   IsUniformAddGroup G → IsUniformAddGroup G → nhds 0 = nhds 0 → u = 
v
· 使用定理 `SeminormedAddCommGroup.to_isUniformAddGroup`：∀ {E : Type u_2} [inst : Se
minormedAddCommGroup E], IsUniformAddGroup E
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `comap_norm_nhds_zero`：∀ {E : Type u_4} [inst : SeminormedAddGroup E], Fi
lter.comap norm (nhds 0) = nhds 0
· 使用定理 `Filter.tendsto_iff_comap`：tendsto_iff_comap {f : α -> β} {l₁ : Filter α}
 {l₂ : Filter β} : Tendsto f l₁ l₂ ↔ l₁ <= l₂.comap f
· 使用定理 `Seminorm.continuous'`：∀ {𝕜 : Type u_3} {E : Type u_7} [inst : Nontrivial
lyNormedField 𝕜] [inst_1 : AddCommGroup E]   [inst_2 : _root_.Module 𝕜 E] [inst_
3 : Topolo…
· 使用定理 `IsUniformAddGroup.to_topologicalAddGroup`：∀ {α : Type u_1} [inst : Unifo
rmSpace α] [inst_1 : AddGroup α] [IsUniformAddGroup α], IsTopologicalAddGroup α
· 使用定理 `Continuous.tendsto'`：Continuous.tendsto' (hf : Continuous f) (x : X) (y 
: Y) (h : f x = y) : Tendsto f (𝓝 x) (𝓝 y)
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `AddGroupSeminormClass.toZeroHomClass`：∀ {F : Type u_2} {α : Type u_3} {β
 : Type u_4} [inst : FunLike F α β] [inst_1 : AddGroup α] [inst_2 : AddCommMonoi
d β]   [inst_3 : PartialOr…
· 使用定理 `SeminormClass.toAddGroupSeminormClass`：∀ {F : Type u_12} {𝕜 : outParam (
Type u_13)} {E : outParam (Type u_14)} {inst : SeminormedRing 𝕜} {inst_1 : AddGr
oup E}   {inst_2 : SMul 𝕜 E…
· 使用定理 `Filter.HasBasis.le_basis_iff`：∀ {α : Type u_1} {ι : Sort u_4} {ι' : Sort
 u_5} {l l' : Filter α} {p : ι → Prop} {s : ι → Set α} {p' : ι' → Prop}   {s' : 
ι' → Set α}, l.Has…
· 使用定理 `NormedAddGroup.nhds_zero_basis_norm_lt`：∀ {E : Type u_5} [inst : Seminor
medAddGroup E], (nhds 0).HasBasis (fun ε => 0 < ε) fun ε => {y | ‖y‖ < ε}
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
-/
lemma uniformSpace_eq_of_hasBasis
    {ι} [UniformSpace E] [IsUniformAddGroup E] [ContinuousConstSMul 𝕜 E]
    {p' : ι → Prop} {s : ι → Set E} (p : Seminorm 𝕜 E) (hb : (𝓝 0 : Filter E).HasBasis p' s)
    (h₁ : ∃ r, p.closedBall 0 r ∈ 𝓝 0) (h₂ : ∀ i, p' i → ∃ r > 0, p.ball 0 r ⊆ s i) :
    ‹UniformSpace E› = p.toAddGroupSeminorm.toSeminormedAddGroup.toUniformSpace := by
  refine IsUniformAddGroup.ext ‹_›
    p.toAddGroupSeminorm.toSeminormedAddCommGroup.to_isUniformAddGroup ?_
  apply le_antisymm
  · rw [← @comap_norm_nhds_zero E p.toAddGroupSeminorm.toSeminormedAddGroup, ← tendsto_iff_comap]
    suffices Continuous p from this.tendsto' 0 _ (map_zero p)
    rcases h₁ with ⟨r, hr⟩
    exact p.continuous' hr
  · rw [(@NormedAddGroup.nhds_zero_basis_norm_lt E
      p.toAddGroupSeminorm.toSeminormedAddGroup).le_basis_iff hb]
    simpa only [subset_def, mem_ball_zero] using! h₂
/-
**Seminorm.uniformity_eq_of_hasBasis** 是 Mathlib 中的一个引理，位于命名空间 `Seminorm`。
形式化陈述：uniformity_eq_of_hasBasis {ι} [UniformSpace E] [IsUniformAddGroup E] [Cont
inuousConstSMul 𝕜 E] {p' : ι -> Prop} {s : ι -> Set E} (p : Seminorm 𝕜 E) (hb : 
(𝓝 0 : Filter E).HasBasis p' s) (h₁ : exists r, p.closedBall 0 r in 𝓝 0) (h₂ : f
orall i, p' i -> exists r > 0, p.ball 0 r subseteq s i) : 𝓤 E = ⨅ r > 0, 𝓟 {x | 
p (x.1 - x.2) < r}
参数：p : Seminorm 𝕜 E；hb : (𝓝 0 : Filter E).HasBasis p' s；h₁ : exists r, p.closedB
all 0 r in 𝓝 0；h₂ : forall i, p' i -> exists r > 0, p.ball 0 r subseteq s i。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Seminorm.uniformSpace_eq_of_hasBasis`：uniformSpace_eq_of_hasBasis {ι} [U
niformSpace E] [IsUniformAddGroup E] [ContinuousConstSMul 𝕜 E] {p' : ι -> Prop} 
{s : ι -> Set E} (p : Semi…
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `iInf_congr_Prop`：∀ {α : Type u_1} [inst : InfSet α] {p q : Prop} {f₁ : p
 → α} {f₂ : q → α} (pq : p ↔ q),   (∀ (x : q), f₁ ⋯ = f₂ x) → iInf f₁ = iInf f₂
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `sub_eq_add_neg`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a b : G), a - 
b = a + -b
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `map_neg_add`：∀ {F : Type u_2} {β : Type u_4} [inst : AddCommMonoid β] [i
nst_1 : PartialOrder β] (f : F) {α : Type u_7}   [inst_2 : FunLike F α β] [inst_
3…
· 使用定理 `SeminormClass.toAddGroupSeminormClass`：∀ {F : Type u_12} {𝕜 : outParam (
Type u_13)} {E : outParam (Type u_14)} {inst : SeminormedRing 𝕜} {inst_1 : AddGr
oup E}   {inst_2 : SMul 𝕜 E…
-/
lemma uniformity_eq_of_hasBasis
    {ι} [UniformSpace E] [IsUniformAddGroup E] [ContinuousConstSMul 𝕜 E]
    {p' : ι → Prop} {s : ι → Set E} (p : Seminorm 𝕜 E) (hb : (𝓝 0 : Filter E).HasBasis p' s)
    (h₁ : ∃ r, p.closedBall 0 r ∈ 𝓝 0) (h₂ : ∀ i, p' i → ∃ r > 0, p.ball 0 r ⊆ s i) :
    𝓤 E = ⨅ r > 0, 𝓟 {x | p (x.1 - x.2) < r} := by
  rw [uniformSpace_eq_of_hasBasis p hb h₁ h₂]
  simp only [sub_eq_add_neg, ← map_neg_add p]
  rfl

end Continuity

section ShellLemmas

variable [NormedField 𝕜] [AddCommGroup E] [Module 𝕜 E]

/-- Let `p` be a seminorm on a vector space over a `NormedField`.
If there is a scalar `c` with `‖c‖>1`, then any `x` such that `p x ≠ 0` can be
moved by scalar multiplication to any `p`-shell of width `‖c‖`. Also recap information on the
value of `p` on the rescaling element that shows up in applications. -/
/-
**Seminorm.rescale_to_shell_zpow** 是 Mathlib 中的一个引理，位于命名空间 `Seminorm`。
形式化陈述：rescale_to_shell_zpow (p : Seminorm 𝕜 E) {c : 𝕜} (hc : 1 < ‖c‖) {ε : Real}
 (εpos : 0 < ε) {x : E} (hx : p x != 0) : exists n : Int, c ^ n != 0 ∧ p (c ^ n 
• x) < ε ∧ (ε / ‖c‖ <= p (c ^ n • x)) ∧ (‖c ^ n‖⁻¹ <= ε⁻¹ * ‖c‖ * p x)
参数：p : Seminorm 𝕜 E；hc : 1 < ‖c‖；εpos : 0 < ε；hx : p x != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `div_pos`：div_pos (ha : 0 < a) (hb : 0 < b) : 0 < a / b
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `lt_of_le_of_ne'`：∀ {α : Type u_1} [inst : PartialOrder α] {a b : α}, b ≤
 a → a ≠ b → b < a
· 使用定理 `NonnegHomClass.apply_nonneg`：∀ {F : Type u_7} {α : outParam (Type u_8)} 
{β : outParam (Type u_9)} {inst : Zero β} {inst_1 : LE β}   {inst_2 : FunLike F 
α β} [self : Nonn…
· 使用定理 `AddGroupSeminormClass.toNonnegHomClass`：∀ {F : Type u_2} {α : Type u_3} 
{β : Type u_4} [inst : FunLike F α β] [inst_1 : AddGroup α] [inst_2 : AddCommMon
oid β]   [inst_3 : LinearOrd…
· 使用定理 `SeminormClass.toAddGroupSeminormClass`：∀ {F : Type u_12} {𝕜 : outParam (
Type u_13)} {E : outParam (Type u_14)} {inst : SeminormedRing 𝕜} {inst_1 : AddGr
oup E}   {inst_2 : SMul 𝕜 E…
· 使用定理 `exists_mem_Ico_zpow`：exists_mem_Ico_zpow (hx : 0 < x) (hy : 1 < y) : exi
sts n : Int, x in Ico (y ^ n) (y ^ (n + 1))
· 使用定理 `AddGroup.existsAddOfLE`：∀ (α : Type u) [inst : AddGroup α] [inst_1 : LE 
α], ExistsAddOfLE α
· 使用引理 `lt_trans`：lt_trans : a < b -> b < c -> a < c
· 使用引理 `Mathlib.Meta.Positivity.pos_of_isNat`：pos_of_isNat {n : Nat} [Semiring A
] [PartialOrder A] [IsOrderedRing A] [Nontrivial A] (h : NormNum.IsNat e n) (w :
 Nat.ble 1 n = true) : 0 <…
· 使用定理 `Mathlib.Meta.NormNum.isNat_ofNat`：isNat_ofNat (α : Type u) [AddMonoidWit
hOne α] {a : α} {n : Nat} (h : n = a) : IsNat a n
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `norm_zpow`：norm_zpow : forall (a : α) (n : Int), ‖a ^ n‖ = ‖a‖ ^ n
· 使用定理 `LT.lt.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a < b → b
 < c → a < c
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `zpow_ne_zero`：∀ {G₀ : Type u_3} [inst : GroupWithZero G₀] {a : G₀} (n : 
ℤ), a ≠ 0 → a ^ n ≠ 0
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `norm_pos_iff`：∀ {E : Type u_5} [inst : NormedAddGroup E] {a : E}, 0 < ‖a
‖ ↔ a ≠ 0
· 使用定理 `SeminormClass.map_smul_eq_mul`：∀ {F : Type u_12} {𝕜 : outParam (Type u_1
3)} {E : outParam (Type u_14)} {inst : SeminormedRing 𝕜} {inst_1 : AddGroup E}  
 {inst_2 : SMul 𝕜 E…
· 使用定理 `zpow_neg`：∀ {α : Type u_1} [inst : DivisionMonoid α] (a : α) (n : ℤ), a 
^ (-n) = (a ^ n)⁻¹
· 使用定理 `norm_inv`：norm_inv (a : α) : ‖a⁻¹‖ = ‖a‖⁻¹
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `div_eq_inv_mul`：div_eq_inv_mul : a / b = b⁻¹ * a
· 使用引理 `div_lt_iff₀`：div_lt_iff₀ (hc : 0 < c) : b / c < a ↔ b < a * c
· 使用定理 `MulPosReflectLE.toMulPosReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [MulPosReflectLE α], MulPosReflectLT α
· 使用定理 `MulPosStrictMono.toMulPosReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [MulPosStrictMono α], MulPosReflectLE α
· 使用定理 `IsStrictOrderedRing.toMulPosStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], MulPosStrictMono 
R
（共 66 条，此处仅展示前 30 条）

--- 原说明 ---
Let `p` be a seminorm on a vector space over a `NormedField`.
If there is a scalar `c` with `‖c‖>1`, then any `x` such that `p x ≠ 0` can be
moved by scalar multiplication to any `p`-shell of width `‖c‖`. Also recap infor
mation on the
value of `p` on the rescaling element that shows up in applications.
-/
lemma rescale_to_shell_zpow (p : Seminorm 𝕜 E) {c : 𝕜} (hc : 1 < ‖c‖) {ε : ℝ}
    (εpos : 0 < ε) {x : E} (hx : p x ≠ 0) : ∃ n : ℤ, c ^ n ≠ 0 ∧
    p (c ^ n • x) < ε ∧ (ε / ‖c‖ ≤ p (c ^ n • x)) ∧ (‖c ^ n‖⁻¹ ≤ ε⁻¹ * ‖c‖ * p x) := by
  have xεpos : 0 < (p x) / ε := by positivity
  rcases exists_mem_Ico_zpow xεpos hc with ⟨n, hn⟩
  have cpos : 0 < ‖c‖ := by positivity
  have cnpos : 0 < ‖c ^ (n + 1)‖ := by rw [norm_zpow]; exact xεpos.trans hn.2
  refine ⟨-(n + 1), ?_, ?_, ?_, ?_⟩
  · show c ^ (-(n + 1)) ≠ 0; exact zpow_ne_zero _ (norm_pos_iff.1 cpos)
  · show p ((c ^ (-(n + 1))) • x) < ε
    rw [map_smul_eq_mul, zpow_neg, norm_inv, ← div_eq_inv_mul, div_lt_iff₀ cnpos, mul_comm,
        norm_zpow]
    exact (div_lt_iff₀ εpos).1 (hn.2)
  · show ε / ‖c‖ ≤ p (c ^ (-(n + 1)) • x)
    rw [zpow_neg, div_le_iff₀ cpos, map_smul_eq_mul, norm_inv, norm_zpow, zpow_add₀ (ne_of_gt cpos),
        zpow_one, mul_inv_rev, mul_comm, ← mul_assoc, ← mul_assoc, mul_inv_cancel₀ (ne_of_gt cpos),
        one_mul, ← div_eq_inv_mul, le_div_iff₀ (zpow_pos cpos _), mul_comm]
    exact (le_div_iff₀ εpos).1 hn.1
  · show ‖(c ^ (-(n + 1)))‖⁻¹ ≤ ε⁻¹ * ‖c‖ * p x
    have : ε⁻¹ * ‖c‖ * p x = ε⁻¹ * p x * ‖c‖ := by ring
    rw [zpow_neg, norm_inv, inv_inv, norm_zpow, zpow_add₀ (ne_of_gt cpos), zpow_one, this,
        ← div_eq_inv_mul]
    gcongr; exact hn.1

/-- Let `p` be a seminorm on a vector space over a `NormedField`.
If there is a scalar `c` with `‖c‖>1`, then any `x` such that `p x ≠ 0` can be
moved by scalar multiplication to any `p`-shell of width `‖c‖`. Also recap information on the
value of `p` on the rescaling element that shows up in applications. -/
/-
**Seminorm.rescale_to_shell** 是 Mathlib 中的一个引理，位于命名空间 `Seminorm`。
形式化陈述：rescale_to_shell (p : Seminorm 𝕜 E) {c : 𝕜} (hc : 1 < ‖c‖) {ε : Real} (εpo
s : 0 < ε) {x : E} (hx : p x != 0) : exists d : 𝕜, d != 0 ∧ p (d • x) < ε ∧ (ε /
 ‖c‖ <= p (d • x)) ∧ (‖d‖⁻¹ <= ε⁻¹ * ‖c‖ * p x)
参数：p : Seminorm 𝕜 E；hc : 1 < ‖c‖；εpos : 0 < ε；hx : p x != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Seminorm.rescale_to_shell_zpow`：rescale_to_shell_zpow (p : Seminorm 𝕜 E)
 {c : 𝕜} (hc : 1 < ‖c‖) {ε : Real} (εpos : 0 < ε) {x : E} (hx : p x != 0) : exis
ts n : Int, c ^ n !=…

--- 原说明 ---
Let `p` be a seminorm on a vector space over a `NormedField`.
If there is a scalar `c` with `‖c‖>1`, then any `x` such that `p x ≠ 0` can be
moved by scalar multiplication to any `p`-shell of width `‖c‖`. Also recap infor
mation on the
value of `p` on the rescaling element that shows up in applications.
-/
lemma rescale_to_shell (p : Seminorm 𝕜 E) {c : 𝕜} (hc : 1 < ‖c‖) {ε : ℝ} (εpos : 0 < ε) {x : E}
    (hx : p x ≠ 0) :
    ∃ d : 𝕜, d ≠ 0 ∧ p (d • x) < ε ∧ (ε / ‖c‖ ≤ p (d • x)) ∧ (‖d‖⁻¹ ≤ ε⁻¹ * ‖c‖ * p x) :=
let ⟨_, hn⟩ := p.rescale_to_shell_zpow hc εpos hx; ⟨_, hn⟩

/-- Let `p` and `q` be two seminorms on a vector space over a `NontriviallyNormedField`.
If we have `q x ≤ C * p x` on some shell of the form `{x | ε/‖c‖ ≤ p x < ε}` (where `ε > 0`
and `‖c‖ > 1`), then we also have `q x ≤ C * p x` for all `x` such that `p x ≠ 0`. -/
/-
**Seminorm.bound_of_shell** 是 Mathlib 中的一个引理，位于命名空间 `Seminorm`。
形式化陈述：bound_of_shell (p q : Seminorm 𝕜 E) {ε C : Real} (ε_pos : 0 < ε) {c : 𝕜} (
hc : 1 < ‖c‖) (hf : forall x, ε / ‖c‖ <= p x -> p x < ε -> q x <= C * p x) {x : 
E} (hx : p x != 0) : q x <= C * p x
参数：p q : Seminorm 𝕜 E；ε_pos : 0 < ε；hc : 1 < ‖c‖；hf : forall x, ε / ‖c‖ <= p x -
> p x < ε -> q x <= C * p x；hx : p x != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Seminorm.rescale_to_shell`：rescale_to_shell (p : Seminorm 𝕜 E) {c : 𝕜} (
hc : 1 < ‖c‖) {ε : Real} (εpos : 0 < ε) {x : E} (hx : p x != 0) : exists d : 𝕜, 
d != 0 ∧ p (d •…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `SeminormClass.map_smul_eq_mul`：∀ {F : Type u_12} {𝕜 : outParam (Type u_1
3)} {E : outParam (Type u_14)} {inst : SeminormedRing 𝕜} {inst_1 : AddGroup E}  
 {inst_2 : SMul 𝕜 E…
· 使用定理 `mul_left_comm`：mul_left_comm (a b c : G) : a * (b * c) = b * (a * c)
· 使用定理 `mul_le_mul_iff_right₀`：mul_le_mul_iff_right₀ [PosMulMono α] [PosMulRefle
ctLE α] (a0 : 0 < a) : a * b <= a * c ↔ b <= c
· 使用定理 `IsOrderedRing.toPosMulMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], PosMulMono R
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `norm_pos_iff`：∀ {E : Type u_5} [inst : NormedAddGroup E] {a : E}, 0 < ‖a
‖ ↔ a ≠ 0

--- 原说明 ---
Let `p` and `q` be two seminorms on a vector space over a `NontriviallyNormedFie
ld`.
If we have `q x ≤ C * p x` on some shell of the form `{x | ε/‖c‖ ≤ p x < ε}` (wh
ere `ε > 0`
and `‖c‖ > 1`), then we also have `q x ≤ C * p x` for all `x` such that `p x ≠ 0
`.
-/
lemma bound_of_shell
    (p q : Seminorm 𝕜 E) {ε C : ℝ} (ε_pos : 0 < ε) {c : 𝕜} (hc : 1 < ‖c‖)
    (hf : ∀ x, ε / ‖c‖ ≤ p x → p x < ε → q x ≤ C * p x) {x : E} (hx : p x ≠ 0) :
    q x ≤ C * p x := by
  rcases p.rescale_to_shell hc ε_pos hx with ⟨δ, hδ, δxle, leδx, -⟩
  simpa only [map_smul_eq_mul, mul_left_comm C, mul_le_mul_iff_right₀ (norm_pos_iff.2 hδ)]
    using hf (δ • x) leδx δxle

/-- A version of `Seminorm.bound_of_shell` expressed using pointwise scalar multiplication of
seminorms. -/
/-
**Seminorm.bound_of_shell_smul** 是 Mathlib 中的一个引理，位于命名空间 `Seminorm`。
形式化陈述：bound_of_shell_smul (p q : Seminorm 𝕜 E) {ε : Real} {C : Real>=0} (ε_pos :
 0 < ε) {c : 𝕜} (hc : 1 < ‖c‖) (hf : forall x, ε / ‖c‖ <= p x -> p x < ε -> q x 
<= (C • p) x) {x : E} (hx : p x != 0) : q x <= (C • p) x
参数：p q : Seminorm 𝕜 E；ε_pos : 0 < ε；hc : 1 < ‖c‖；hf : forall x, ε / ‖c‖ <= p x -
> p x < ε -> q x <= (C • p) x；hx : p x != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Seminorm.bound_of_shell`：bound_of_shell (p q : Seminorm 𝕜 E) {ε C : Real
} (ε_pos : 0 < ε) {c : 𝕜} (hc : 1 < ‖c‖) (hf : forall x, ε / ‖c‖ <= p x -> p x <
 ε -> q x <= …

--- 原说明 ---
A version of `Seminorm.bound_of_shell` expressed using pointwise scalar multipli
cation of
seminorms.
-/
lemma bound_of_shell_smul
    (p q : Seminorm 𝕜 E) {ε : ℝ} {C : ℝ≥0} (ε_pos : 0 < ε) {c : 𝕜} (hc : 1 < ‖c‖)
    (hf : ∀ x, ε / ‖c‖ ≤ p x → p x < ε → q x ≤ (C • p) x) {x : E} (hx : p x ≠ 0) :
    q x ≤ (C • p) x :=
  Seminorm.bound_of_shell p q ε_pos hc hf hx
/-
**Seminorm.bound_of_shell_sup** 是 Mathlib 中的一个引理，位于命名空间 `Seminorm`。
形式化陈述：bound_of_shell_sup (p : ι -> Seminorm 𝕜 E) (s : Finset ι) (q : Seminorm 𝕜 
E) {ε : Real} {C : Real>=0} (ε_pos : 0 < ε) {c : 𝕜} (hc : 1 < ‖c‖) (hf : forall 
x, (forall i in s, p i x < ε) -> forall j in s, ε / ‖c‖ <= p j x -> q x <= (C • 
p j) x) {x : E} (hx : exists j, j in s ∧ p j x != 0) : q x <= (C • s.sup p) x
参数：p : ι -> Seminorm 𝕜 E；s : Finset ι；q : Seminorm 𝕜 E；ε_pos : 0 < ε；hc : 1 < ‖c
‖；hf : forall x, (forall i in s, p i x < ε) -> forall j in s, ε / ‖c‖ <= p j x -
> q x <= (C • p j) x；hx : exists j, j in s ∧ p j x != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ne_of_gt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `LT.lt.trans_le`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a < b 
→ b ≤ c → a < c
· 使用定理 `Ne.lt_of_le`：Ne.lt_of_le : a != b -> a <= b -> a < b
· 使用定理 `Ne.symm`：∀ {α : Sort u} {a b : α}, a ≠ b → b ≠ a
· 使用定理 `NonnegHomClass.apply_nonneg`：∀ {F : Type u_7} {α : outParam (Type u_8)} 
{β : outParam (Type u_9)} {inst : Zero β} {inst_1 : LE β}   {inst_2 : FunLike F 
α β} [self : Nonn…
· 使用定理 `AddGroupSeminormClass.toNonnegHomClass`：∀ {F : Type u_2} {α : Type u_3} 
{β : Type u_4} [inst : FunLike F α β] [inst_1 : AddGroup α] [inst_2 : AddCommMon
oid β]   [inst_3 : LinearOrd…
· 使用定理 `SeminormClass.toAddGroupSeminormClass`：∀ {F : Type u_12} {𝕜 : outParam (
Type u_13)} {E : outParam (Type u_14)} {inst : SeminormedRing 𝕜} {inst_1 : AddGr
oup E}   {inst_2 : SMul 𝕜 E…
· 使用定理 `Seminorm.le_finset_sup_apply`：le_finset_sup_apply {p : ι -> Seminorm 𝕜 E
} {s : Finset ι} {x : E} {i : ι} (hi : i in s) : p i x <= s.sup p x
· 使用引理 `Seminorm.bound_of_shell_smul`：bound_of_shell_smul (p q : Seminorm 𝕜 E) {
ε : Real} {C : Real>=0} (ε_pos : 0 < ε) {c : 𝕜} (hc : 1 < ‖c‖) (hf : forall x, ε
 / ‖c‖ <= p x -> p…
· 使用定理 `Seminorm.exists_apply_eq_finset_sup`：exists_apply_eq_finset_sup (p : ι -
> Seminorm 𝕜 E) {s : Finset ι} (hs : s.Nonempty) (x : E) : exists i in s, s.sup 
p x = p i x
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `smul_apply`：∀ {M : Type u_1} {F : Type u_2} {α : outParam (Type u_3)} {β
 : outParam (Type u_4)} {inst : FunLike F α β}   {inst_1 : SMul M β} {inst_2 : S
…
· 使用定理 `Seminorm.instIsSMulApplyReal`：∀ {R : Type u_1} {𝕜 : Type u_3} {E : Type 
u_7} [inst : SeminormedRing 𝕜] [inst_1 : AddGroup E] [inst_2 : SMul 𝕜 E]   [inst
_3 : SMul R ℝ] [in…
· 使用定理 `LE.le.trans_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b 
→ b < c → a < c
-/
lemma bound_of_shell_sup (p : ι → Seminorm 𝕜 E) (s : Finset ι)
    (q : Seminorm 𝕜 E) {ε : ℝ} {C : ℝ≥0} (ε_pos : 0 < ε) {c : 𝕜} (hc : 1 < ‖c‖)
    (hf : ∀ x, (∀ i ∈ s, p i x < ε) → ∀ j ∈ s, ε / ‖c‖ ≤ p j x → q x ≤ (C • p j) x)
    {x : E} (hx : ∃ j, j ∈ s ∧ p j x ≠ 0) :
    q x ≤ (C • s.sup p) x := by
  rcases hx with ⟨j, hj, hjx⟩
  have : (s.sup p) x ≠ 0 :=
    ne_of_gt ((hjx.symm.lt_of_le <| apply_nonneg _ _).trans_le (le_finset_sup_apply hj))
  refine (s.sup p).bound_of_shell_smul q ε_pos hc (fun y hle hlt ↦ ?_) this
  rcases exists_apply_eq_finset_sup p ⟨j, hj⟩ y with ⟨i, hi, hiy⟩
  rw [smul_apply, hiy]
  exact hf y (fun k hk ↦ (le_finset_sup_apply hk).trans_lt hlt) i hi (hiy ▸ hle)

end ShellLemmas

section NontriviallyNormedField

variable [NontriviallyNormedField 𝕜] [AddCommGroup E] [Module 𝕜 E]

/-- Let `p i` be a family of seminorms on `E`. Let `s` be an absorbent set in `𝕜`.
If all seminorms are uniformly bounded at every point of `s`,
then they are bounded in the space of seminorms. -/
/-
**Seminorm.bddAbove_of_absorbent** 是 Mathlib 中的一个引理，位于命名空间 `Seminorm`。
形式化陈述：bddAbove_of_absorbent {ι : Sort*} {p : ι -> Seminorm 𝕜 E} {s : Set E} (hs 
: Absorbent 𝕜 s) (h : forall x in s, BddAbove (range (p · x))) : BddAbove (range
 p)
参数：hs : Absorbent 𝕜 s；h : forall x in s, BddAbove (range (p · x))。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Seminorm.bddAbove_range_iff`：∀ {𝕜 : Type u_3} {E : Type u_7} [inst : Nor
medField 𝕜] [inst_1 : AddCommGroup E] [inst_2 : _root_.Module 𝕜 E]   {ι : Sort u
_12} {p : ι → Sem…
· 使用定理 `Filter.Eventually.exists`：∀ {α : Type u} {p : α → Prop} {f : Filter α} [
f.NeBot], (∀ᶠ (x : α) in f, p x) → ∃ x, p x
· 使用定理 `NormedField.nhdsNE_neBot`：nhdsNE_neBot (x : α) : NeBot (𝓝[!=] x)
· 使用定理 `Filter.Eventually.and`：∀ {α : Type u} {p q : α → Prop} {f : Filter α},  
 Filter.Eventually p f → Filter.Eventually q f → ∀ᶠ (x : α) in f, p x ∧ q x
· 使用定理 `eventually_mem_nhdsWithin`：eventually_mem_nhdsWithin {a : α} {s : Set α}
 : forallᶠ x in 𝓝[s] a, x in s
· 使用定理 `Absorbent.eventually_nhdsNE_zero`：∀ {𝕜 : Type u_1} {E : Type u_3} [inst 
: NormedDivisionRing 𝕜] [inst_1 : AddCommGroup E] [inst_2 : _root_.Module 𝕜 E]  
 {s : Set E}, Absorben…
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.forall_mem_range`：forall_mem_range {p : α -> Prop} : (forall a in ra
nge f, p a) ↔ forall i, p (f i)
· 使用引理 `le_div_iff₀'`：le_div_iff₀' (hc : 0 < c) : a <= b / c ↔ c * a <= b
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `norm_pos_iff`：∀ {E : Type u_5} [inst : NormedAddGroup E] {a : E}, 0 < ‖a
‖ ↔ a ≠ 0
· 使用定理 `SeminormClass.map_smul_eq_mul`：∀ {F : Type u_12} {𝕜 : outParam (Type u_1
3)} {E : outParam (Type u_14)} {inst : SeminormedRing 𝕜} {inst_1 : AddGroup E}  
 {inst_2 : SMul 𝕜 E…

--- 原说明 ---
Let `p i` be a family of seminorms on `E`. Let `s` be an absorbent set in `𝕜`.
If all seminorms are uniformly bounded at every point of `s`,
then they are bounded in the space of seminorms.
-/
lemma bddAbove_of_absorbent {ι : Sort*} {p : ι → Seminorm 𝕜 E} {s : Set E} (hs : Absorbent 𝕜 s)
    (h : ∀ x ∈ s, BddAbove (range (p · x))) : BddAbove (range p) := by
  rw [Seminorm.bddAbove_range_iff]
  intro x
  obtain ⟨c, hc₀, hc⟩ : ∃ c ≠ 0, (c : 𝕜) • x ∈ s :=
    (eventually_mem_nhdsWithin.and (hs.eventually_nhdsNE_zero x)).exists
  rcases h _ hc with ⟨M, hM⟩
  refine ⟨M / ‖c‖, forall_mem_range.mpr fun i ↦ (le_div_iff₀' (norm_pos_iff.2 hc₀)).2 ?_⟩
  exact hM ⟨i, map_smul_eq_mul ..⟩

end NontriviallyNormedField

end Seminorm

/-! ### The norm as a seminorm -/


section normSeminorm

variable (𝕜) (E) [NormedField 𝕜] [SeminormedAddCommGroup E] [NormedSpace 𝕜 E] {r : ℝ}

/-- The norm of a seminormed group as a seminorm. -/
/-
**normSeminorm** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：normSeminorm : Seminorm 𝕜 E
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The norm of a seminormed group as a seminorm.
-/
def normSeminorm : Seminorm 𝕜 E :=
  { normAddGroupSeminorm E with smul' := norm_smul }

@[simp]
/-
**coe_normSeminorm** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：coe_normSeminorm : ⇑(normSeminorm 𝕜 E) = norm
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_normSeminorm : ⇑(normSeminorm 𝕜 E) = norm :=
  rfl

@[simp]
/-
**ball_normSeminorm** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ball_normSeminorm : (normSeminorm 𝕜 E).ball = Metric.ball
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `dist_eq_norm`：∀ {E : Type u_5} [inst : SeminormedAddCommGroup E] (a b : 
E), dist a b = ‖a - b‖
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem ball_normSeminorm : (normSeminorm 𝕜 E).ball = Metric.ball := by
  ext x r y
  simp only [Seminorm.mem_ball, Metric.mem_ball, coe_normSeminorm, dist_eq_norm]

@[simp]
/-
**closedBall_normSeminorm** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：closedBall_normSeminorm : (normSeminorm 𝕜 E).closedBall = Metric.closedBal
l
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `dist_eq_norm`：∀ {E : Type u_5} [inst : SeminormedAddCommGroup E] (a b : 
E), dist a b = ‖a - b‖
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem closedBall_normSeminorm : (normSeminorm 𝕜 E).closedBall = Metric.closedBall := by
  ext x r y
  simp only [Seminorm.mem_closedBall, Metric.mem_closedBall, coe_normSeminorm, dist_eq_norm]

variable {𝕜 E} {x : E}

/-- Balls at the origin are absorbent. -/
/-
**absorbent_ball_zero** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：absorbent_ball_zero (hr : 0 < r) : Absorbent 𝕜 (Metric.ball (0 : E) r)
参数：hr : 0 < r。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `ball_normSeminorm`：ball_normSeminorm : (normSeminorm 𝕜 E).ball = Metric.
ball
· 使用定理 `Seminorm.absorbent_ball_zero`：∀ {𝕜 : Type u_3} {E : Type u_7} [inst : No
rmedDivisionRing 𝕜] [inst_1 : AddCommGroup E] [inst_2 : _root_.Module 𝕜 E]   (p 
: Seminorm 𝕜 E) {r…

--- 原说明 ---
Balls at the origin are absorbent.
-/
theorem absorbent_ball_zero (hr : 0 < r) : Absorbent 𝕜 (Metric.ball (0 : E) r) := by
  rw [← ball_normSeminorm 𝕜]
  exact (normSeminorm 𝕜 _).absorbent_ball_zero hr

/-- Balls containing the origin are absorbent. -/
/-
**absorbent_ball** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：absorbent_ball (hx : ‖x‖ < r) : Absorbent 𝕜 (Metric.ball x r)
参数：hx : ‖x‖ < r。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `ball_normSeminorm`：ball_normSeminorm : (normSeminorm 𝕜 E).ball = Metric.
ball
· 使用定理 `Seminorm.absorbent_ball`：∀ {𝕜 : Type u_3} {E : Type u_7} [inst : NormedD
ivisionRing 𝕜] [inst_1 : AddCommGroup E] [inst_2 : _root_.Module 𝕜 E]   (p : Sem
inorm 𝕜 E) {r…

--- 原说明 ---
Balls containing the origin are absorbent.
-/
theorem absorbent_ball (hx : ‖x‖ < r) : Absorbent 𝕜 (Metric.ball x r) := by
  rw [← ball_normSeminorm 𝕜]
  exact (normSeminorm 𝕜 _).absorbent_ball hx

/-- Balls at the origin are balanced. -/
/-
**balanced_ball_zero** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：balanced_ball_zero : Balanced 𝕜 (Metric.ball (0 : E) r)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `ball_normSeminorm`：ball_normSeminorm : (normSeminorm 𝕜 E).ball = Metric.
ball
· 使用定理 `Seminorm.balanced_ball_zero`：balanced_ball_zero (r : Real) : Balanced 𝕜 
(ball p 0 r)

--- 原说明 ---
Balls at the origin are balanced.
-/
theorem balanced_ball_zero : Balanced 𝕜 (Metric.ball (0 : E) r) := by
  rw [← ball_normSeminorm 𝕜]
  exact (normSeminorm _ _).balanced_ball_zero r

/-- Closed balls at the origin are balanced. -/
/-
**balanced_closedBall_zero** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：balanced_closedBall_zero : Balanced 𝕜 (Metric.closedBall (0 : E) r)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `closedBall_normSeminorm`：closedBall_normSeminorm : (normSeminorm 𝕜 E).cl
osedBall = Metric.closedBall
· 使用定理 `Seminorm.balanced_closedBall_zero`：balanced_closedBall_zero (r : Real) :
 Balanced 𝕜 (closedBall p 0 r)

--- 原说明 ---
Closed balls at the origin are balanced.
-/
theorem balanced_closedBall_zero : Balanced 𝕜 (Metric.closedBall (0 : E) r) := by
  rw [← closedBall_normSeminorm 𝕜]
  exact (normSeminorm _ _).balanced_closedBall_zero r

/-- If there is a scalar `c` with `‖c‖>1`, then any element with nonzero norm can be
moved by scalar multiplication to any shell of width `‖c‖`. Also recap information on the norm of
the rescaling element that shows up in applications. -/
/-
**rescale_to_shell_semi_normed_zpow** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：rescale_to_shell_semi_normed_zpow {c : 𝕜} (hc : 1 < ‖c‖) {ε : Real} (εpos 
: 0 < ε) {x : E} (hx : ‖x‖ != 0) : exists n : Int, c ^ n != 0 ∧ ‖c ^ n • x‖ < ε 
∧ (ε / ‖c‖ <= ‖c ^ n • x‖) ∧ (‖c ^ n‖⁻¹ <= ε⁻¹ * ‖c‖ * ‖x‖)
参数：hc : 1 < ‖c‖；εpos : 0 < ε；hx : ‖x‖ != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Seminorm.rescale_to_shell_zpow`：rescale_to_shell_zpow (p : Seminorm 𝕜 E)
 {c : 𝕜} (hc : 1 < ‖c‖) {ε : Real} (εpos : 0 < ε) {x : E} (hx : p x != 0) : exis
ts n : Int, c ^ n !=…

--- 原说明 ---
If there is a scalar `c` with `‖c‖>1`, then any element with nonzero norm can be
moved by scalar multiplication to any shell of width `‖c‖`. Also recap informati
on on the norm of
the rescaling element that shows up in applications.
-/
lemma rescale_to_shell_semi_normed_zpow {c : 𝕜} (hc : 1 < ‖c‖) {ε : ℝ} (εpos : 0 < ε) {x : E}
    (hx : ‖x‖ ≠ 0) :
    ∃ n : ℤ, c ^ n ≠ 0 ∧ ‖c ^ n • x‖ < ε ∧ (ε / ‖c‖ ≤ ‖c ^ n • x‖) ∧
      (‖c ^ n‖⁻¹ ≤ ε⁻¹ * ‖c‖ * ‖x‖) :=
  (normSeminorm 𝕜 E).rescale_to_shell_zpow hc εpos hx

/-- If there is a scalar `c` with `‖c‖>1`, then any element with nonzero norm can be
moved by scalar multiplication to any shell of width `‖c‖`. Also recap information on the norm of
the rescaling element that shows up in applications. -/
/-
**rescale_to_shell_semi_normed** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：rescale_to_shell_semi_normed {c : 𝕜} (hc : 1 < ‖c‖) {ε : Real} (εpos : 0 <
 ε) {x : E} (hx : ‖x‖ != 0) : exists d : 𝕜, d != 0 ∧ ‖d • x‖ < ε ∧ (ε / ‖c‖ <= ‖
d • x‖) ∧ (‖d‖⁻¹ <= ε⁻¹ * ‖c‖ * ‖x‖)
参数：hc : 1 < ‖c‖；εpos : 0 < ε；hx : ‖x‖ != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Seminorm.rescale_to_shell`：rescale_to_shell (p : Seminorm 𝕜 E) {c : 𝕜} (
hc : 1 < ‖c‖) {ε : Real} (εpos : 0 < ε) {x : E} (hx : p x != 0) : exists d : 𝕜, 
d != 0 ∧ p (d •…

--- 原说明 ---
If there is a scalar `c` with `‖c‖>1`, then any element with nonzero norm can be
moved by scalar multiplication to any shell of width `‖c‖`. Also recap informati
on on the norm of
the rescaling element that shows up in applications.
-/
lemma rescale_to_shell_semi_normed {c : 𝕜} (hc : 1 < ‖c‖) {ε : ℝ} (εpos : 0 < ε)
    {x : E} (hx : ‖x‖ ≠ 0) :
    ∃ d : 𝕜, d ≠ 0 ∧ ‖d • x‖ < ε ∧ (ε / ‖c‖ ≤ ‖d • x‖) ∧ (‖d‖⁻¹ ≤ ε⁻¹ * ‖c‖ * ‖x‖) :=
  (normSeminorm 𝕜 E).rescale_to_shell hc εpos hx
/-
**rescale_to_shell_zpow** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：rescale_to_shell_zpow [NormedAddCommGroup F] [NormedSpace 𝕜 F] {c : 𝕜} (hc
 : 1 < ‖c‖) {ε : Real} (εpos : 0 < ε) {x : F} (hx : x != 0) : exists n : Int, c 
^ n != 0 ∧ ‖c ^ n • x‖ < ε ∧ (ε / ‖c‖ <= ‖c ^ n • x‖) ∧ (‖c ^ n‖⁻¹ <= ε⁻¹ * ‖c‖ 
* ‖x‖)
参数：hc : 1 < ‖c‖；εpos : 0 < ε；hx : x != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `rescale_to_shell_semi_normed_zpow`：rescale_to_shell_semi_normed_zpow {c 
: 𝕜} (hc : 1 < ‖c‖) {ε : Real} (εpos : 0 < ε) {x : E} (hx : ‖x‖ != 0) : exists n
 : Int, c ^ n != 0 ∧ ‖c…
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `norm_ne_zero_iff`：∀ {E : Type u_5} [inst : NormedAddGroup E] {a : E}, ‖a
‖ ≠ 0 ↔ a ≠ 0
-/
lemma rescale_to_shell_zpow [NormedAddCommGroup F] [NormedSpace 𝕜 F] {c : 𝕜} (hc : 1 < ‖c‖)
    {ε : ℝ} (εpos : 0 < ε) {x : F} (hx : x ≠ 0) :
    ∃ n : ℤ, c ^ n ≠ 0 ∧ ‖c ^ n • x‖ < ε ∧ (ε / ‖c‖ ≤ ‖c ^ n • x‖) ∧
      (‖c ^ n‖⁻¹ ≤ ε⁻¹ * ‖c‖ * ‖x‖) :=
  rescale_to_shell_semi_normed_zpow hc εpos (norm_ne_zero_iff.mpr hx)

/-- If there is a scalar `c` with `‖c‖>1`, then any element can be moved by scalar multiplication to
any shell of width `‖c‖`. Also recap information on the norm of the rescaling element that shows
up in applications. -/
/-
**rescale_to_shell** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：rescale_to_shell [NormedAddCommGroup F] [NormedSpace 𝕜 F] {c : 𝕜} (hc : 1 
< ‖c‖) {ε : Real} (εpos : 0 < ε) {x : F} (hx : x != 0) : exists d : 𝕜, d != 0 ∧ 
‖d • x‖ < ε ∧ (ε / ‖c‖ <= ‖d • x‖) ∧ (‖d‖⁻¹ <= ε⁻¹ * ‖c‖ * ‖x‖)
参数：hc : 1 < ‖c‖；εpos : 0 < ε；hx : x != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `rescale_to_shell_semi_normed`：rescale_to_shell_semi_normed {c : 𝕜} (hc :
 1 < ‖c‖) {ε : Real} (εpos : 0 < ε) {x : E} (hx : ‖x‖ != 0) : exists d : 𝕜, d !=
 0 ∧ ‖d • x‖ < ε ∧…
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `norm_ne_zero_iff`：∀ {E : Type u_5} [inst : NormedAddGroup E] {a : E}, ‖a
‖ ≠ 0 ↔ a ≠ 0

--- 原说明 ---
If there is a scalar `c` with `‖c‖>1`, then any element can be moved by scalar m
ultiplication to
any shell of width `‖c‖`. Also recap information on the norm of the rescaling el
ement that shows
up in applications.
-/
lemma rescale_to_shell [NormedAddCommGroup F] [NormedSpace 𝕜 F] {c : 𝕜} (hc : 1 < ‖c‖)
    {ε : ℝ} (εpos : 0 < ε) {x : F} (hx : x ≠ 0) :
    ∃ d : 𝕜, d ≠ 0 ∧ ‖d • x‖ < ε ∧ (ε / ‖c‖ ≤ ‖d • x‖) ∧ (‖d‖⁻¹ ≤ ε⁻¹ * ‖c‖ * ‖x‖) :=
  rescale_to_shell_semi_normed hc εpos (norm_ne_zero_iff.mpr hx)

end normSeminorm

