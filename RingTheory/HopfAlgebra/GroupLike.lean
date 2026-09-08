/-
Copyright (c) 2025 Yaël Dillies, Michał Mrugała. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Michał Mrugała
-/
module

public import Mathlib.RingTheory.HopfAlgebra.Basic
public import Mathlib.RingTheory.Bialgebra.GroupLike

/-!
# Group-like elements in a Hopf algebra

This file proves that group-like elements in a Hopf algebra form a group.
-/

@[expose] public section

open HopfAlgebra

variable {R A : Type*}

section Semiring
variable [CommSemiring R] [Semiring A] [HopfAlgebra R A] {a b : A}

/-
**IsGroupLikeElem.antipode_mul_cancel** 是 Mathlib 中的一个定理，位于命名空间 `IsGroupLikeElem
`。
形式化陈述：∀ {R : Type u_1} {A : Type u_2} [inst : CommSemiring R] [inst_1 : Semiring
 A] [inst_2 : HopfAlgebra R A] {a : A},   IsGroupLikeElem R a → (HopfAlgebraStru
ct.antipode R) a * a = 1
参数：HopfAlgebraStruct.antipode R。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `IsGroupLikeElem.comul_eq_tmul_self`：∀ {R : Type u_2} {A : Type u_3} [ins
t : CommSemiring R] [inst_1 : AddCommMonoid A] [inst_2 : _root_.Module R A]   [i
nst_3 : Coalgebra R A] {…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `IsGroupLikeElem.counit_eq_one`：∀ {R : Type u_2} {A : Type u_3} [inst : C
ommSemiring R] [inst_1 : AddCommMonoid A] [inst_2 : _root_.Module R A]   [inst_3
 : Coalgebra R A] {…
· 使用定理 `map_one`：map_one [OneHomClass F M N] (f : F) : f 1 = 1
· 使用定理 `MonoidHomClass.toOneHomClass`：∀ {F : Type u_10} {M : outParam (Type u_11
)} {N : outParam (Type u_12)} {inst : MulOne M} {inst_1 : MulOne N}   {inst_2 : 
FunLike F M N} [se…
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `HopfAlgebra.mul_antipode_rTensor_comul_apply`：mul_antipode_rTensor_comul
_apply (a : A) : LinearMap.mul' R A ((antipode R).rTensor A (Coalgebra.comul a))
 = algebraMap R A (Coalgebra.couni…
-/
@[simp] lemma IsGroupLikeElem.antipode_mul_cancel (ha : IsGroupLikeElem R a) :
    antipode R a * a = 1 := by
  simpa [ha, -mul_antipode_lTensor_comul_apply] using mul_antipode_rTensor_comul_apply (R := R) a
/-
**IsGroupLikeElem.mul_antipode_cancel** 是 Mathlib 中的一个定理，位于命名空间 `IsGroupLikeElem
`。
形式化陈述：∀ {R : Type u_1} {A : Type u_2} [inst : CommSemiring R] [inst_1 : Semiring
 A] [inst_2 : HopfAlgebra R A] {a : A},   IsGroupLikeElem R a → a * (HopfAlgebra
Struct.antipode R) a = 1
参数：HopfAlgebraStruct.antipode R。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `IsGroupLikeElem.comul_eq_tmul_self`：∀ {R : Type u_2} {A : Type u_3} [ins
t : CommSemiring R] [inst_1 : AddCommMonoid A] [inst_2 : _root_.Module R A]   [i
nst_3 : Coalgebra R A] {…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `IsGroupLikeElem.counit_eq_one`：∀ {R : Type u_2} {A : Type u_3} [inst : C
ommSemiring R] [inst_1 : AddCommMonoid A] [inst_2 : _root_.Module R A]   [inst_3
 : Coalgebra R A] {…
· 使用定理 `map_one`：map_one [OneHomClass F M N] (f : F) : f 1 = 1
· 使用定理 `MonoidHomClass.toOneHomClass`：∀ {F : Type u_10} {M : outParam (Type u_11
)} {N : outParam (Type u_12)} {inst : MulOne M} {inst_1 : MulOne N}   {inst_2 : 
FunLike F M N} [se…
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `HopfAlgebra.mul_antipode_lTensor_comul_apply`：mul_antipode_lTensor_comul
_apply (a : A) : LinearMap.mul' R A ((antipode R).lTensor A (Coalgebra.comul a))
 = algebraMap R A (Coalgebra.couni…
-/
@[simp] lemma IsGroupLikeElem.mul_antipode_cancel (ha : IsGroupLikeElem R a) :
    a * antipode R a = 1 := by
  simpa [ha, -mul_antipode_lTensor_comul_apply] using mul_antipode_lTensor_comul_apply (R := R) a

variable (R) in
/-- Turn a group-like element `a` into a unit with inverse its antipode. -/
@[simps]
/-
**GroupLike.toUnits** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：GroupLike.toUnits : GroupLike R A ->* Aˣ where toFun a
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Turn a group-like element `a` into a unit with inverse its antipode.
-/
def GroupLike.toUnits : GroupLike R A →* Aˣ where
  toFun a := {
    val := a
    inv := antipode R a
    val_inv := a.2.mul_antipode_cancel
    inv_val := a.2.antipode_mul_cancel
  }
  map_one' := by ext; rfl
  map_mul' a b := by ext; rfl
/-
**IsGroupLikeElem.isUnit** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：IsGroupLikeElem.isUnit (ha : IsGroupLikeElem R a) : IsUnit a
参数：ha : IsGroupLikeElem R a。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Units.isUnit`：∀ {M : Type u_1} [inst : Monoid M] (u : Mˣ), IsUnit ↑u
-/
lemma IsGroupLikeElem.isUnit (ha : IsGroupLikeElem R a) : IsUnit a :=
  (GroupLike.toUnits R ⟨a, ha⟩).isUnit
/-
**IsGroupLikeElem.antipode** 是 Mathlib 中的一个定理，位于命名空间 `IsGroupLikeElem`。
形式化陈述：∀ {R : Type u_1} {A : Type u_2} [inst : CommSemiring R] [inst_1 : Semiring
 A] [inst_2 : HopfAlgebra R A] {a : A},   IsGroupLikeElem R a → IsGroupLikeElem 
R ((HopfAlgebraStruct.antipode R) a)
参数：(HopfAlgebraStruct.antipode R) a。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `IsGroupLikeElem.of_mul_eq_one`：IsGroupLikeElem.of_mul_eq_one (hab : a * 
b = 1) (hba : b * a = 1) (ha : IsGroupLikeElem R a) : IsGroupLikeElem R b where 
counit_eq_one
· 使用定理 `IsGroupLikeElem.mul_antipode_cancel`：∀ {R : Type u_1} {A : Type u_2} [in
st : CommSemiring R] [inst_1 : Semiring A] [inst_2 : HopfAlgebra R A] {a : A},  
 IsGroupLikeElem R a → a …
· 使用定理 `IsGroupLikeElem.antipode_mul_cancel`：∀ {R : Type u_1} {A : Type u_2} [in
st : CommSemiring R] [inst_1 : Semiring A] [inst_2 : HopfAlgebra R A] {a : A},  
 IsGroupLikeElem R a → (H…
-/
@[simp] protected lemma IsGroupLikeElem.antipode (ha : IsGroupLikeElem R a) :
    IsGroupLikeElem R (antipode R a) :=
  ha.of_mul_eq_one ha.mul_antipode_cancel ha.antipode_mul_cancel
/-
**IsGroupLikeElem.antipode_antipode** 是 Mathlib 中的一个定理，位于命名空间 `IsGroupLikeElem`。
形式化陈述：∀ {R : Type u_1} {A : Type u_2} [inst : CommSemiring R] [inst_1 : Semiring
 A] [inst_2 : HopfAlgebra R A] {a : A},   IsGroupLikeElem R a → (HopfAlgebraStru
ct.antipode R) ((HopfAlgebraStruct.antipode R) a) = a
参数：HopfAlgebraStruct.antipode R；(HopfAlgebraStruct.antipode R) a。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `left_inv_eq_right_inv`：∀ {M : Type u_2} [inst : Monoid M] {a b c : M}, b
 * a = 1 → a * c = 1 → b = c
· 使用定理 `IsGroupLikeElem.antipode_mul_cancel`：∀ {R : Type u_1} {A : Type u_2} [in
st : CommSemiring R] [inst_1 : Semiring A] [inst_2 : HopfAlgebra R A] {a : A},  
 IsGroupLikeElem R a → (H…
· 使用定理 `IsGroupLikeElem.antipode`：∀ {R : Type u_1} {A : Type u_2} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : HopfAlgebra R A] {a : A},   IsGroupLik
eElem R a → Is…
-/
@[simp] lemma IsGroupLikeElem.antipode_antipode (ha : IsGroupLikeElem R a) :
    antipode R (antipode R a) = a :=
  left_inv_eq_right_inv ha.antipode.antipode_mul_cancel ha.antipode_mul_cancel

namespace GroupLike

/-
**GroupLike.** 是 Mathlib 中的一个实例，位于命名空间 `GroupLike`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Inv (GroupLike R A) where inv a := ⟨antipode R a, a.2.antipode⟩
/-
**GroupLike.val_inv** 是 Mathlib 中的一个定理，位于命名空间 `GroupLike`。
形式化陈述：∀ {R : Type u_1} {A : Type u_2} [inst : CommSemiring R] [inst_1 : Semiring
 A] [inst_2 : HopfAlgebra R A]   (a : GroupLike R A), ↑a⁻¹ = (HopfAlgebraStruct.
antipode R) ↑a
参数：a : GroupLike R A；HopfAlgebraStruct.antipode R。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma val_inv (a : GroupLike R A) : ↑(a⁻¹) = (antipode R a : A) := rfl
/-
**GroupLike.** 是 Mathlib 中的一个实例，位于命名空间 `GroupLike`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Group (GroupLike R A) where
  inv_mul_cancel a := by ext; simp

end GroupLike
end Semiring

variable [CommSemiring R] [CommSemiring A] [HopfAlgebra R A] {a b : A}

/-
**GroupLike.instCommGroup** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：GroupLike.instCommGroup : CommGroup (GroupLike R A) where __
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance GroupLike.instCommGroup : CommGroup (GroupLike R A) where
  __ := instCommMonoid
  __ := instGroup
