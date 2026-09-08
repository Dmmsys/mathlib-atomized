/-
Copyright (c) 2026 Jon Bannon, Monica Omar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Bannon, Monica Omar
-/
module

public import Mathlib.Analysis.CStarAlgebra.Basic

/-! # Unitary maps in C⋆-algebras

This file defines some basic maps by unitaries in C⋆-algebras. -/

@[expose] public section

namespace Unitary
variable {R A : Type*} [NormedRing A] [StarRing A] [CStarRing A] [Ring R] [Module R A]

section mulLeft
variable [SMulCommClass R A A]

set_option backward.isDefEq.respectTransparency false in
variable (R A) in
/-- Left multiplication by a unitary as a linear isometric equivalence. -/
/-
**Unitary.mulLeft** 是 Mathlib 中的一个定义，位于命名空间 `Unitary`。
形式化陈述：mulLeft : unitary A ->* A ≃ₗᵢ[R] A where toFun u
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CStarRing.norm_coe_unitary_mul`：norm_coe_unitary_mul (U : unitary E) (A 
: E) : ‖(U : E) * A‖ = ‖A‖

--- 原说明 ---
Left multiplication by a unitary as a linear isometric equivalence.
-/
noncomputable def mulLeft : unitary A →* A ≃ₗᵢ[R] A where
  toFun u :=
    { __ := (toUnits u).mulLeftLinearEquiv R A
      norm_map' _ := CStarRing.norm_coe_unitary_mul _ _ }
  map_one' := by ext; simp
  map_mul' _ _ := by ext; simp

variable (R) in
/-
**Unitary.mulLeft_apply** 是 Mathlib 中的一个定理，位于命名空间 `Unitary`。
形式化陈述：∀ (R : Type u_1) {A : Type u_2} [inst : NormedRing A] [inst_1 : StarRing A
] [inst_2 : CStarRing A] [inst_3 : Ring R]   [inst_4 : _root_.Module R A] [inst_
5 : SMulCommClass R A A] (u : ↥(unitary A)) (x : A),   ((Unitary.mulLeft R A) u)
 x = ↑u * x
参数：R : Type u_1；u : ↥(unitary A)；x : A；(Unitary.mulLeft R A) u。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma mulLeft_apply (u : unitary A) (x : A) :
    mulLeft R A u x = u * x := rfl

variable (R) in
/-
**Unitary.symm_mulLeft_apply** 是 Mathlib 中的一个引理，位于命名空间 `Unitary`。
形式化陈述：symm_mulLeft_apply (u : unitary A) (x : A) : (mulLeft R A u).symm x = (sta
r u : A) * x
参数：u : unitary A；x : A。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma symm_mulLeft_apply (u : unitary A) (x : A) :
    (mulLeft R A u).symm x = (star u : A) * x := rfl
/-
**Unitary.symm_mulLeft** 是 Mathlib 中的一个定理，位于命名空间 `Unitary`。
形式化陈述：∀ {R : Type u_1} {A : Type u_2} [inst : NormedRing A] [inst_1 : StarRing A
] [inst_2 : CStarRing A] [inst_3 : Ring R]   [inst_4 : _root_.Module R A] [inst_
5 : SMulCommClass R A A] (u : ↥(unitary A)),   ((Unitary.mulLeft R A) u).symm = 
(Unitary.mulLeft R A) (star u)
参数：u : ↥(unitary A)；(Unitary.mulLeft R A) u；Unitary.mulLeft R A；star u。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearIsometryEquiv.ext`：ext {e e' : E ≃ₛₗᵢ[σ₁₂] E₂} (h : forall x, e x 
= e' x) : e = e'
-/
@[simp] lemma symm_mulLeft (u : unitary A) :
    (mulLeft R A u).symm = mulLeft R A (star u) := by ext; rfl
/-
**Unitary.mulLeft_trans_mulLeft** 是 Mathlib 中的一个引理，位于命名空间 `Unitary`。
形式化陈述：mulLeft_trans_mulLeft (u v : unitary A) : .symm (mulLeft R A u).trans (mul
Left R A v) = mulLeft R A (v * u)
参数：u v : unitary A。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `map_mul`：map_mul [MulHomClass F M N] (f : F) (x y : M) : f (x * y) = f x
 * f y
· 使用定理 `MonoidHomClass.toMulHomClass`：∀ {F : Type u_10} {M : outParam (Type u_11
)} {N : outParam (Type u_12)} {inst : MulOne M} {inst_1 : MulOne N}   {inst_2 : 
FunLike F M N} [se…
-/
lemma mulLeft_trans_mulLeft (u v : unitary A) :
    (mulLeft R A u).trans (mulLeft R A v) = mulLeft R A (v * u) := map_mul _ _ _ |>.symm
/-
**Unitary.mulLeft_mul_apply** 是 Mathlib 中的一个引理，位于命名空间 `Unitary`。
形式化陈述：mulLeft_mul_apply (u v : unitary A) (x : A) : mulLeft R A (u * v) x = mulL
eft R A u (mulLeft R A v x)
参数：u v : unitary A；x : A。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `map_mul`：map_mul [MulHomClass F M N] (f : F) (x y : M) : f (x * y) = f x
 * f y
· 使用定理 `MonoidHomClass.toMulHomClass`：∀ {F : Type u_10} {M : outParam (Type u_11
)} {N : outParam (Type u_12)} {inst : MulOne M} {inst_1 : MulOne N}   {inst_2 : 
FunLike F M N} [se…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma mulLeft_mul_apply (u v : unitary A) (x : A) :
    mulLeft R A (u * v) x = mulLeft R A u (mulLeft R A v x) := by simp
/-
**Unitary.toLinearEquiv_mulLeft** 是 Mathlib 中的一个定理，位于命名空间 `Unitary`。
形式化陈述：∀ {R : Type u_1} {A : Type u_2} [inst : NormedRing A] [inst_1 : StarRing A
] [inst_2 : CStarRing A] [inst_3 : Ring R]   [inst_4 : _root_.Module R A] [inst_
5 : SMulCommClass R A A] (u : ↥(unitary A)),   ((Unitary.mulLeft R A) u).toLinea
rEquiv = (Units.mulLeftLinearEquiv R A) (Unitary.toUnits u)
参数：u : ↥(unitary A)；(Unitary.mulLeft R A) u；Units.mulLeftLinearEquiv R A；Unitary
.toUnits u。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma toLinearEquiv_mulLeft (u : unitary A) :
    (mulLeft R A u).toLinearEquiv = (toUnits u).mulLeftLinearEquiv R A := rfl

end mulLeft

section mulRight
variable [IsScalarTower R A A]

variable (R) in
/-- Right multiplication by a unitary as a linear isometric equivalence. -/
/-
**Unitary.mulRight** 是 Mathlib 中的一个定义，位于命名空间 `Unitary`。
形式化陈述：mulRight (u : unitary A) : A ≃ₗᵢ[R] A where toLinearEquiv
参数：u : unitary A。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CStarRing.norm_mul_coe_unitary`：norm_mul_coe_unitary (A : E) (U : unitar
y E) : ‖A * U‖ = ‖A‖

--- 原说明 ---
Right multiplication by a unitary as a linear isometric equivalence.
-/
noncomputable def mulRight (u : unitary A) : A ≃ₗᵢ[R] A where
  toLinearEquiv := (toUnits u).mulRightLinearEquiv R
  norm_map' _ := CStarRing.norm_mul_coe_unitary _ _

variable (R) in
/-
**Unitary.mulRight_apply** 是 Mathlib 中的一个定理，位于命名空间 `Unitary`。
形式化陈述：∀ (R : Type u_1) {A : Type u_2} [inst : NormedRing A] [inst_1 : StarRing A
] [inst_2 : CStarRing A] [inst_3 : Ring R]   [inst_4 : _root_.Module R A] [inst_
5 : IsScalarTower R A A] (u : ↥(unitary A)) (x : A),   (Unitary.mulRight R u) x 
= x * ↑u
参数：R : Type u_1；u : ↥(unitary A)；x : A；Unitary.mulRight R u。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma mulRight_apply (u : unitary A) (x : A) :
    mulRight R u x = x * u := rfl

variable (R) in
/-
**Unitary.symm_mulRight_apply** 是 Mathlib 中的一个引理，位于命名空间 `Unitary`。
形式化陈述：symm_mulRight_apply (u : unitary A) (x : A) : (mulRight R u).symm x = x * 
(star u : A)
参数：u : unitary A；x : A。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma symm_mulRight_apply (u : unitary A) (x : A) :
    (mulRight R u).symm x = x * (star u : A) := rfl
/-
**Unitary.symm_mulRight** 是 Mathlib 中的一个定理，位于命名空间 `Unitary`。
形式化陈述：∀ {R : Type u_1} {A : Type u_2} [inst : NormedRing A] [inst_1 : StarRing A
] [inst_2 : CStarRing A] [inst_3 : Ring R]   [inst_4 : _root_.Module R A] [inst_
5 : IsScalarTower R A A] (u : ↥(unitary A)),   (Unitary.mulRight R u).symm = Uni
tary.mulRight R (star u)
参数：u : ↥(unitary A)；Unitary.mulRight R u；star u。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearIsometryEquiv.ext`：ext {e e' : E ≃ₛₗᵢ[σ₁₂] E₂} (h : forall x, e x 
= e' x) : e = e'
-/
@[simp] lemma symm_mulRight (u : unitary A) :
    (mulRight R u).symm = mulRight R (star u) := by
  ext; rfl
/-
**Unitary.mulRight_trans_mulRight** 是 Mathlib 中的一个引理，位于命名空间 `Unitary`。
形式化陈述：mulRight_trans_mulRight (u v : unitary A) : (mulRight R u).trans (mulRight
 R v) = mulRight R (u * v)
参数：u v : unitary A。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearIsometryEquiv.ext`：ext {e e' : E ≃ₛₗᵢ[σ₁₂] E₂} (h : forall x, e x 
= e' x) : e = e'
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma mulRight_trans_mulRight (u v : unitary A) :
    (mulRight R u).trans (mulRight R v) = mulRight R (u * v) := by ext; simp [mul_assoc]
/-
**Unitary.mulRight_mul_apply** 是 Mathlib 中的一个引理，位于命名空间 `Unitary`。
形式化陈述：mulRight_mul_apply (u v : unitary A) (x : A) : mulRight R (u * v) x = mulR
ight R v (mulRight R u x)
参数：u v : unitary A；x : A。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma mulRight_mul_apply (u v : unitary A) (x : A) :
    mulRight R (u * v) x = mulRight R v (mulRight R u x) := by simp [mul_assoc]
/-
**Unitary.toLinearMap_mulRight** 是 Mathlib 中的一个引理，位于命名空间 `Unitary`。
形式化陈述：toLinearMap_mulRight (u : unitary A) : (mulRight R u).toLinearMap = Linear
Map.mulRight R (u : A)
参数：u : unitary A。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma toLinearMap_mulRight (u : unitary A) :
    (mulRight R u).toLinearMap = LinearMap.mulRight R (u : A) := rfl
/-
**Unitary.mulRight_one** 是 Mathlib 中的一个定理，位于命名空间 `Unitary`。
形式化陈述：∀ {R : Type u_1} {A : Type u_2} [inst : NormedRing A] [inst_1 : StarRing A
] [inst_2 : CStarRing A] [inst_3 : Ring R]   [inst_4 : _root_.Module R A] [inst_
5 : IsScalarTower R A A], Unitary.mulRight R 1 = LinearIsometryEquiv.refl R A
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearIsometryEquiv.ext`：ext {e e' : E ≃ₛₗᵢ[σ₁₂] E₂} (h : forall x, e x 
= e' x) : e = e'
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
@[simp] lemma mulRight_one : mulRight R 1 = .refl R A := by
  ext; simp
/-
**Unitary.toLinearEquiv_mulRight** 是 Mathlib 中的一个定理，位于命名空间 `Unitary`。
形式化陈述：∀ {R : Type u_1} {A : Type u_2} [inst : NormedRing A] [inst_1 : StarRing A
] [inst_2 : CStarRing A] [inst_3 : Ring R]   [inst_4 : _root_.Module R A] [inst_
5 : IsScalarTower R A A] (u : ↥(unitary A)),   (Unitary.mulRight R u).toLinearEq
uiv = Units.mulRightLinearEquiv R (Unitary.toUnits u)
参数：u : ↥(unitary A)；Unitary.mulRight R u；Unitary.toUnits u。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma toLinearEquiv_mulRight (u : unitary A) :
    (mulRight R u).toLinearEquiv = (toUnits u).mulRightLinearEquiv R := rfl

end mulRight

end Unitary

