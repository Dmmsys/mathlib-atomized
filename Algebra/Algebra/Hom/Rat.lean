/-
Copyright (c) 2018 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau, Yury Kudryashov
-/
module

public import Mathlib.Algebra.Algebra.Equiv
public import Mathlib.Algebra.Algebra.Hom
public import Mathlib.Algebra.Algebra.Rat

/-!
# Homomorphisms of `ℚ`-algebras

-/

@[expose] public section

variable {R S : Type*} [Ring R] [Ring S] [Algebra ℚ R] [Algebra ℚ S]

namespace RingHom

/-- Reinterpret a `RingHom` as a `ℚ`-algebra homomorphism. This actually yields an equivalence,
see `RingHom.equivRatAlgHom`. -/
/-
**RingHom.toRatAlgHom** 是 Mathlib 中的一个定义，位于命名空间 `RingHom`。
形式化陈述：toRatAlgHom (f : R ->+* S) : R ->ₐ[Rat] S
参数：f : R ->+* S。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Reinterpret a `RingHom` as a `ℚ`-algebra homomorphism. This actually yields an e
quivalence,
see `RingHom.equivRatAlgHom`.
-/
def toRatAlgHom (f : R →+* S) : R →ₐ[ℚ] S :=
  { f with commutes' := f.map_rat_algebraMap }

@[simp]
/-
**RingHom.toRatAlgHom_toRingHom** 是 Mathlib 中的一个定理，位于命名空间 `RingHom`。
形式化陈述：toRatAlgHom_toRingHom (f : R ->+* S) : ↑f.toRatAlgHom = f
参数：f : R ->+* S。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RingHom.ext`：ext ⦃f g : α ->+* β⦄ : (forall x, f x = g x) -> f = g
· 使用定理 `AlgHomClass.toRingHomClass`：∀ {F : Type u_1} {R : outParam (Type u_2)} {
A : outParam (Type u_3)} {B : outParam (Type u_4)} {inst : CommSemiring R}   {in
st_1 : Semiring …
-/
theorem toRatAlgHom_toRingHom (f : R →+* S) :
    ↑f.toRatAlgHom = f :=
  RingHom.ext fun _x => rfl

@[simp]
/-
**RingHom.toRatAlgHom_apply** 是 Mathlib 中的一个定理，位于命名空间 `RingHom`。
形式化陈述：toRatAlgHom_apply (f : R ->+* S) (x : R) : f.toRatAlgHom x = f x
参数：f : R ->+* S；x : R。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem toRatAlgHom_apply (f : R →+* S) (x : R) :
    f.toRatAlgHom x = f x :=
  rfl

end RingHom

@[simp]
/-
**AlgHom.toRingHom_toRatAlgHom** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：AlgHom.toRingHom_toRatAlgHom (f : R ->ₐ[Rat] S) : (f : R ->+* S).toRatAlgH
om = f
参数：f : R ->ₐ[Rat] S。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AlgHom.ext`：ext {φ₁ φ₂ : A ->ₐ[R] B} (H : forall x, φ₁ x = φ₂ x) : φ₁ = 
φ₂
· 使用定理 `AlgHomClass.toRingHomClass`：∀ {F : Type u_1} {R : outParam (Type u_2)} {
A : outParam (Type u_3)} {B : outParam (Type u_4)} {inst : CommSemiring R}   {in
st_1 : Semiring …
-/
theorem AlgHom.toRingHom_toRatAlgHom (f : R →ₐ[ℚ] S) : (f : R →+* S).toRatAlgHom = f :=
  AlgHom.ext fun _x => rfl

variable (R) (S) in
/-- The equivalence between `RingHom` and `ℚ`-algebra homomorphisms. -/
@[simps]
/-
**RingHom.equivRatAlgHom** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：RingHom.equivRatAlgHom : (R ->+* S) ≃ (R ->ₐ[Rat] S) where toFun
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The equivalence between `RingHom` and `ℚ`-algebra homomorphisms.
-/
def RingHom.equivRatAlgHom : (R →+* S) ≃ (R →ₐ[ℚ] S) where
  toFun := RingHom.toRatAlgHom
  invFun := AlgHom.toRingHom

namespace RingEquiv

/-- Reinterpret a `RingEquiv` as a `ℚ`-algebra isomorphism. This actually yields an
equivalence, see `RingEquiv.equivRatAlgEquiv`. -/
@[simps! -isSimp apply]
/-
**RingEquiv.toRatAlgEquiv** 是 Mathlib 中的一个定义，位于命名空间 `RingEquiv`。
形式化陈述：toRatAlgEquiv (f : R ≃+* S) : R ≃ₐ[Rat] S where toEquiv
参数：f : R ≃+* S。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Reinterpret a `RingEquiv` as a `ℚ`-algebra isomorphism. This actually yields an
equivalence, see `RingEquiv.equivRatAlgEquiv`.
-/
def toRatAlgEquiv (f : R ≃+* S) : R ≃ₐ[ℚ] S where
  toEquiv := f
  __ := f.toRingHom.toRatAlgHom

@[simp]
/-
**RingEquiv.coe_toRatAlgEquiv** 是 Mathlib 中的一个定理，位于命名空间 `RingEquiv`。
形式化陈述：coe_toRatAlgEquiv (f : R ≃+* S) : ⇑f.toRatAlgEquiv = ⇑f
参数：f : R ≃+* S。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_toRatAlgEquiv (f : R ≃+* S) : ⇑f.toRatAlgEquiv = ⇑f := rfl

@[simp]
/-
**RingEquiv.toRingEquiv_toRatAlgEquiv** 是 Mathlib 中的一个定理，位于命名空间 `RingEquiv`。
形式化陈述：toRingEquiv_toRatAlgEquiv (f : R ≃+* S) : f.toRatAlgEquiv = f
参数：f : R ≃+* S。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem toRingEquiv_toRatAlgEquiv (f : R ≃+* S) :
    f.toRatAlgEquiv = f :=
  rfl
/-
**RingEquiv.toAlgHom_toRatAlgEquiv** 是 Mathlib 中的一个定理，位于命名空间 `RingEquiv`。
形式化陈述：toAlgHom_toRatAlgEquiv (f : R ≃+* S) : f.toRatAlgEquiv.toAlgHom = (f : R -
>+* S).toRatAlgHom
参数：f : R ≃+* S。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem toAlgHom_toRatAlgEquiv (f : R ≃+* S) :
    f.toRatAlgEquiv.toAlgHom = (f : R →+* S).toRatAlgHom :=
  rfl

@[simp]
/-
**RingEquiv.symm_toRatAlgEquiv** 是 Mathlib 中的一个定理，位于命名空间 `RingEquiv`。
形式化陈述：symm_toRatAlgEquiv (f : R ≃+* S) : f.toRatAlgEquiv.symm = f.symm.toRatAlgE
quiv
参数：f : R ≃+* S。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem symm_toRatAlgEquiv (f : R ≃+* S) :
    f.toRatAlgEquiv.symm = f.symm.toRatAlgEquiv :=
  rfl

end RingEquiv

@[simp]
/-
**AlgEquiv.toRatAlgEquiv_toRingEquiv** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：AlgEquiv.toRatAlgEquiv_toRingEquiv (f : R ≃ₐ[Rat] S) : (f : R ≃+* S).toRat
AlgEquiv = f
参数：f : R ≃ₐ[Rat] S。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem AlgEquiv.toRatAlgEquiv_toRingEquiv (f : R ≃ₐ[ℚ] S) : (f : R ≃+* S).toRatAlgEquiv = f :=
  rfl

variable (R) (S) in
/-- The equivalence between `RingEquiv` and `ℚ`-algebra isomorphisms. -/
@[simps apply symm_apply]
/-
**RingEquiv.equivRatAlgEquiv** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：RingEquiv.equivRatAlgEquiv : (R ≃+* S) ≃ (R ≃ₐ[Rat] S) where toFun
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The equivalence between `RingEquiv` and `ℚ`-algebra isomorphisms.
-/
def RingEquiv.equivRatAlgEquiv : (R ≃+* S) ≃ (R ≃ₐ[ℚ] S) where
  toFun := RingEquiv.toRatAlgEquiv
  invFun := AlgEquiv.toRingEquiv
/-
**RingEquiv.toRatAlgEquiv_injective** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：RingEquiv.toRatAlgEquiv_injective : Function.Injective (RingEquiv.toRatAlg
Equiv : (R ≃+* S) -> _)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.injective`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β), Function.Injec
tive ⇑e
-/
lemma RingEquiv.toRatAlgEquiv_injective :
    Function.Injective (RingEquiv.toRatAlgEquiv : (R ≃+* S) → _) :=
  (RingEquiv.equivRatAlgEquiv R S).injective
