/-
Copyright (c) 2023 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser
-/
module

public import Mathlib.Algebra.Algebra.Equiv
public import Mathlib.Algebra.Module.Opposite
public import Mathlib.Algebra.Ring.Opposite

/-!
# Algebra structures on the multiplicative opposite

## Main definitions

* `MulOpposite.instAlgebra`: the algebra on `Aᵐᵒᵖ`
* `AlgHom.op`/`AlgHom.unop`: simultaneously convert the domain and codomain of a morphism to the
  opposite algebra.
* `AlgHom.opComm`: swap which side of a morphism lies in the opposite algebra.
* `AlgEquiv.op`/`AlgEquiv.unop`: simultaneously convert the source and target of an isomorphism to
  the opposite algebra.
* `AlgEquiv.opOp`: any algebra is isomorphic to the opposite of its opposite.
* `AlgEquiv.toOpposite`: in a commutative algebra, the opposite algebra is isomorphic to the
  original algebra.
* `AlgEquiv.opComm`: swap which side of an isomorphism lies in the opposite algebra.
-/

@[expose] public section


variable {R S A B : Type*}

open MulOpposite

section Semiring

variable [CommSemiring R] [CommSemiring S] [Semiring A] [Semiring B]
variable [Algebra R S] [Algebra R A] [Algebra R B] [Algebra S A] [SMulCommClass R S A]
variable [IsScalarTower R S A]

namespace MulOpposite

set_option backward.isDefEq.respectTransparency false in
/-
**MulOpposite.instAlgebra** 是 Mathlib 中的一个实例，位于命名空间 `MulOpposite`。
形式化陈述：instAlgebra : Algebra R Aᵐᵒᵖ where algebraMap
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instAlgebra : Algebra R Aᵐᵒᵖ where
  algebraMap := (algebraMap R A).toOpposite fun _ _ => Algebra.commutes _ _
  smul_def' c x := unop_injective <| by
    simp only [unop_smul, RingHom.toOpposite_apply, Function.comp_apply, unop_mul,
      Algebra.smul_def, Algebra.commutes, unop_op]
  commutes' r := MulOpposite.rec' fun x => by
    simp only [RingHom.toOpposite_apply, Function.comp_apply, ← op_mul, Algebra.commutes]

@[simp]
/-
**MulOpposite.algebraMap_apply** 是 Mathlib 中的一个定理，位于命名空间 `MulOpposite`。
形式化陈述：algebraMap_apply (c : R) : algebraMap R Aᵐᵒᵖ c = op (algebraMap R A c)
参数：c : R。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem algebraMap_apply (c : R) : algebraMap R Aᵐᵒᵖ c = op (algebraMap R A c) :=
  rfl

end MulOpposite

namespace AlgEquiv
variable (R A)

/-- An algebra is isomorphic to the opposite of its opposite. -/
@[simps!]
/-
**AlgEquiv.opOp** 是 Mathlib 中的一个定义，位于命名空间 `AlgEquiv`。
形式化陈述：opOp : A ≃ₐ[R] Aᵐᵒᵖᵐᵒᵖ where __
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An algebra is isomorphic to the opposite of its opposite.
-/
def opOp : A ≃ₐ[R] Aᵐᵒᵖᵐᵒᵖ where
  __ := RingEquiv.opOp A
  commutes' _ := rfl
/-
**AlgEquiv.toRingEquiv_opOp** 是 Mathlib 中的一个定理，位于命名空间 `AlgEquiv`。
形式化陈述：∀ (R : Type u_1) (A : Type u_3) [inst : CommSemiring R] [inst_1 : Semiring
 A] [inst_2 : Algebra R A],   (AlgEquiv.opOp R A).toRingEquiv = RingEquiv.opOp A
参数：R : Type u_1；A : Type u_3；AlgEquiv.opOp R A。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] theorem toRingEquiv_opOp : (opOp R A : A ≃+* Aᵐᵒᵖᵐᵒᵖ) = RingEquiv.opOp A := rfl

end AlgEquiv

namespace AlgHom

/--
An algebra homomorphism `f : A →ₐ[R] B` such that `f x` commutes with `f y` for all `x, y` defines
an algebra homomorphism from `Aᵐᵒᵖ`. -/
@[simps -fullyApplied]
/-
**AlgHom.fromOpposite** 是 Mathlib 中的一个定义，位于命名空间 `AlgHom`。
形式化陈述：fromOpposite (f : A ->ₐ[R] B) (hf : forall x y, Commute (f x) (f y)) : Aᵐᵒ
ᵖ ->ₐ[R] B
参数：f : A ->ₐ[R] B；hf : forall x y, Commute (f x) (f y)。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `AlgHom.commutes`：commutes (r : R) : φ (algebraMap R A r) = algebraMap R 
B r

--- 原说明 ---
An algebra homomorphism `f : A →ₐ[R] B` such that `f x` commutes with `f y` for 
all `x, y` defines
an algebra homomorphism from `Aᵐᵒᵖ`.
-/
def fromOpposite (f : A →ₐ[R] B) (hf : ∀ x y, Commute (f x) (f y)) : Aᵐᵒᵖ →ₐ[R] B :=
  { f.toRingHom.fromOpposite hf with
    toFun := f ∘ unop
    commutes' := fun r => f.commutes r }

@[simp]
/-
**AlgHom.toLinearMap_fromOpposite** 是 Mathlib 中的一个定理，位于命名空间 `AlgHom`。
形式化陈述：toLinearMap_fromOpposite (f : A ->ₐ[R] B) (hf : forall x y, Commute (f x) 
(f y)) : (f.fromOpposite hf).toLinearMap = f.toLinearMap ∘ₗ (opLinearEquiv R (M
参数：f : A ->ₐ[R] B；hf : forall x y, Commute (f x) (f y)。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem toLinearMap_fromOpposite (f : A →ₐ[R] B) (hf : ∀ x y, Commute (f x) (f y)) :
    (f.fromOpposite hf).toLinearMap = f.toLinearMap ∘ₗ (opLinearEquiv R (M := A)).symm :=
  rfl

@[simp]
/-
**AlgHom.toRingHom_fromOpposite** 是 Mathlib 中的一个定理，位于命名空间 `AlgHom`。
形式化陈述：toRingHom_fromOpposite (f : A ->ₐ[R] B) (hf : forall x y, Commute (f x) (f
 y)) : (f.fromOpposite hf : Aᵐᵒᵖ ->+* B) = (f : A ->+* B).fromOpposite hf
参数：f : A ->ₐ[R] B；hf : forall x y, Commute (f x) (f y)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AlgHomClass.toRingHomClass`：∀ {F : Type u_1} {R : outParam (Type u_2)} {
A : outParam (Type u_3)} {B : outParam (Type u_4)} {inst : CommSemiring R}   {in
st_1 : Semiring …
-/
theorem toRingHom_fromOpposite (f : A →ₐ[R] B) (hf : ∀ x y, Commute (f x) (f y)) :
    (f.fromOpposite hf : Aᵐᵒᵖ →+* B) = (f : A →+* B).fromOpposite hf :=
  rfl

/--
An algebra homomorphism `f : A →ₐ[R] B` such that `f x` commutes with `f y` for all `x, y` defines
an algebra homomorphism to `Bᵐᵒᵖ`. -/
@[simps -fullyApplied]
/-
**AlgHom.toOpposite** 是 Mathlib 中的一个定义，位于命名空间 `AlgHom`。
形式化陈述：toOpposite (f : A ->ₐ[R] B) (hf : forall x y, Commute (f x) (f y)) : A ->ₐ
[R] Bᵐᵒᵖ
参数：f : A ->ₐ[R] B；hf : forall x y, Commute (f x) (f y)。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An algebra homomorphism `f : A →ₐ[R] B` such that `f x` commutes with `f y` for 
all `x, y` defines
an algebra homomorphism to `Bᵐᵒᵖ`.
-/
def toOpposite (f : A →ₐ[R] B) (hf : ∀ x y, Commute (f x) (f y)) : A →ₐ[R] Bᵐᵒᵖ :=
  { f.toRingHom.toOpposite hf with
    toFun := op ∘ f
    commutes' := fun r => unop_injective <| f.commutes r }

@[simp]
/-
**AlgHom.toLinearMap_toOpposite** 是 Mathlib 中的一个定理，位于命名空间 `AlgHom`。
形式化陈述：toLinearMap_toOpposite (f : A ->ₐ[R] B) (hf : forall x y, Commute (f x) (f
 y)) : (f.toOpposite hf).toLinearMap = (opLinearEquiv R : B ≃ₗ[R] Bᵐᵒᵖ) ∘ₗ f.toL
inearMap
参数：f : A ->ₐ[R] B；hf : forall x y, Commute (f x) (f y)。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem toLinearMap_toOpposite (f : A →ₐ[R] B) (hf : ∀ x y, Commute (f x) (f y)) :
    (f.toOpposite hf).toLinearMap = (opLinearEquiv R : B ≃ₗ[R] Bᵐᵒᵖ) ∘ₗ f.toLinearMap :=
  rfl

@[simp]
/-
**AlgHom.toRingHom_toOpposite** 是 Mathlib 中的一个定理，位于命名空间 `AlgHom`。
形式化陈述：toRingHom_toOpposite (f : A ->ₐ[R] B) (hf : forall x y, Commute (f x) (f y
)) : (f.toOpposite hf : A ->+* Bᵐᵒᵖ) = (f : A ->+* B).toOpposite hf
参数：f : A ->ₐ[R] B；hf : forall x y, Commute (f x) (f y)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AlgHomClass.toRingHomClass`：∀ {F : Type u_1} {R : outParam (Type u_2)} {
A : outParam (Type u_3)} {B : outParam (Type u_4)} {inst : CommSemiring R}   {in
st_1 : Semiring …
-/
theorem toRingHom_toOpposite (f : A →ₐ[R] B) (hf : ∀ x y, Commute (f x) (f y)) :
    (f.toOpposite hf : A →+* Bᵐᵒᵖ) = (f : A →+* B).toOpposite hf :=
  rfl

/-- An algebra hom `A →ₐ[R] B` can equivalently be viewed as an algebra hom `Aᵐᵒᵖ →ₐ[R] Bᵐᵒᵖ`.
This is the action of the (fully faithful) `ᵐᵒᵖ`-functor on morphisms. -/
@[simps!]
/-
**AlgHom.op** 是 Mathlib 中的一个定义，位于命名空间 `AlgHom`。
形式化陈述：{R : Type u_1} →   {A : Type u_3} →     {B : Type u_4} →       [inst : Com
mSemiring R] →         [inst_1 : Semiring A] →           [inst_2 : Semiring B] →
 [inst_3 : Algebra R A] → [inst_4 : Algebra R B] → (A →ₐ[R] B) ≃ (Aᵐᵒᵖ →ₐ[R] Bᵐᵒ
ᵖ)
参数：A →ₐ[R] B；Aᵐᵒᵖ →ₐ[R] Bᵐᵒᵖ。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An algebra hom `A →ₐ[R] B` can equivalently be viewed as an algebra hom `Aᵐᵒᵖ →ₐ
[R] Bᵐᵒᵖ`.
This is the action of the (fully faithful) `ᵐᵒᵖ`-functor on morphisms.
-/
protected def op : (A →ₐ[R] B) ≃ (Aᵐᵒᵖ →ₐ[R] Bᵐᵒᵖ) where
  toFun f := { RingHom.op f.toRingHom with commutes' := fun r => unop_injective <| f.commutes r }
  invFun f := { RingHom.unop f.toRingHom with commutes' := fun r => op_injective <| f.commutes r }
/-
**AlgHom.toRingHom_op** 是 Mathlib 中的一个定理，位于命名空间 `AlgHom`。
形式化陈述：toRingHom_op (f : A ->ₐ[R] B) : f.op.toRingHom = RingHom.op f.toRingHom
参数：f : A ->ₐ[R] B。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem toRingHom_op (f : A →ₐ[R] B) : f.op.toRingHom = RingHom.op f.toRingHom :=
  rfl

/-- The 'unopposite' of an algebra hom `Aᵐᵒᵖ →ₐ[R] Bᵐᵒᵖ`. Inverse to `RingHom.op`. -/
/-
**AlgHom.unop** 是 Mathlib 中的一个缩写定义，位于命名空间 `AlgHom`。
形式化陈述：unop : (Aᵐᵒᵖ ->ₐ[R] Bᵐᵒᵖ) ≃ (A ->ₐ[R] B)
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s

--- 原说明 ---
The 'unopposite' of an algebra hom `Aᵐᵒᵖ →ₐ[R] Bᵐᵒᵖ`. Inverse to `RingHom.op`.
-/
abbrev unop : (Aᵐᵒᵖ →ₐ[R] Bᵐᵒᵖ) ≃ (A →ₐ[R] B) := AlgHom.op.symm
/-
**AlgHom.toRingHom_unop** 是 Mathlib 中的一个定理，位于命名空间 `AlgHom`。
形式化陈述：toRingHom_unop (f : Aᵐᵒᵖ ->ₐ[R] Bᵐᵒᵖ) : f.unop.toRingHom = RingHom.unop f.
toRingHom
参数：f : Aᵐᵒᵖ ->ₐ[R] Bᵐᵒᵖ。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem toRingHom_unop (f : Aᵐᵒᵖ →ₐ[R] Bᵐᵒᵖ) : f.unop.toRingHom = RingHom.unop f.toRingHom :=
  rfl

/-- Swap the `ᵐᵒᵖ` on an algebra hom to the opposite side. -/
@[simps!]
/-
**AlgHom.opComm** 是 Mathlib 中的一个定义，位于命名空间 `AlgHom`。
形式化陈述：opComm : (A ->ₐ[R] Bᵐᵒᵖ) ≃ (Aᵐᵒᵖ ->ₐ[R] B)
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.trans`：Equiv.trans {s t u : Computation α} : s ~ t -> t ~ u -> s ~
 u

--- 原说明 ---
Swap the `ᵐᵒᵖ` on an algebra hom to the opposite side.
-/
def opComm : (A →ₐ[R] Bᵐᵒᵖ) ≃ (Aᵐᵒᵖ →ₐ[R] B) :=
  AlgHom.op.trans <| AlgEquiv.refl.arrowCongr (AlgEquiv.opOp R B).symm

end AlgHom

namespace AlgEquiv

#adaptation_note
/-- `respectTransparency.types true` changes the auto-generated lemmas' signature -/
set_option backward.isDefEq.respectTransparency.types false in
/-- An algebra iso `A ≃ₐ[R] B` can equivalently be viewed as an algebra iso `Aᵐᵒᵖ ≃ₐ[R] Bᵐᵒᵖ`.
This is the action of the (fully faithful) `ᵐᵒᵖ`-functor on morphisms. -/
@[simps!]
/-
**AlgEquiv.op** 是 Mathlib 中的一个定义，位于命名空间 `AlgEquiv`。
形式化陈述：op : (A ≃ₐ[R] B) ≃ Aᵐᵒᵖ ≃ₐ[R] Bᵐᵒᵖ where toFun f
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An algebra iso `A ≃ₐ[R] B` can equivalently be viewed as an algebra iso `Aᵐᵒᵖ ≃ₐ
[R] Bᵐᵒᵖ`.
This is the action of the (fully faithful) `ᵐᵒᵖ`-functor on morphisms.
-/
def op : (A ≃ₐ[R] B) ≃ Aᵐᵒᵖ ≃ₐ[R] Bᵐᵒᵖ where
  toFun f :=
    { RingEquiv.op f.toRingEquiv with
      commutes' := fun r => MulOpposite.unop_injective <| f.commutes r }
  invFun f :=
    { RingEquiv.unop f.toRingEquiv with
      commutes' := fun r => MulOpposite.op_injective <| f.commutes r }
/-
**AlgEquiv.toAlgHom_op** 是 Mathlib 中的一个定理，位于命名空间 `AlgEquiv`。
形式化陈述：toAlgHom_op (f : A ≃ₐ[R] B) : (AlgEquiv.op f).toAlgHom = AlgHom.op f.toAlg
Hom
参数：f : A ≃ₐ[R] B。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem toAlgHom_op (f : A ≃ₐ[R] B) :
    (AlgEquiv.op f).toAlgHom = AlgHom.op f.toAlgHom :=
  rfl
/-
**AlgEquiv.toRingEquiv_op** 是 Mathlib 中的一个定理，位于命名空间 `AlgEquiv`。
形式化陈述：toRingEquiv_op (f : A ≃ₐ[R] B) : (AlgEquiv.op f).toRingEquiv = RingEquiv.o
p f.toRingEquiv
参数：f : A ≃ₐ[R] B。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem toRingEquiv_op (f : A ≃ₐ[R] B) :
    (AlgEquiv.op f).toRingEquiv = RingEquiv.op f.toRingEquiv :=
  rfl

/-- The 'unopposite' of an algebra iso `Aᵐᵒᵖ ≃ₐ[R] Bᵐᵒᵖ`. Inverse to `AlgEquiv.op`. -/
/-
**AlgEquiv.unop** 是 Mathlib 中的一个缩写定义，位于命名空间 `AlgEquiv`。
形式化陈述：unop : (Aᵐᵒᵖ ≃ₐ[R] Bᵐᵒᵖ) ≃ A ≃ₐ[R] B
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s

--- 原说明 ---
The 'unopposite' of an algebra iso `Aᵐᵒᵖ ≃ₐ[R] Bᵐᵒᵖ`. Inverse to `AlgEquiv.op`.
-/
abbrev unop : (Aᵐᵒᵖ ≃ₐ[R] Bᵐᵒᵖ) ≃ A ≃ₐ[R] B := AlgEquiv.op.symm
/-
**AlgEquiv.toAlgHom_unop** 是 Mathlib 中的一个定理，位于命名空间 `AlgEquiv`。
形式化陈述：toAlgHom_unop (f : Aᵐᵒᵖ ≃ₐ[R] Bᵐᵒᵖ) : f.unop.toAlgHom = AlgHom.unop f.toAl
gHom
参数：f : Aᵐᵒᵖ ≃ₐ[R] Bᵐᵒᵖ。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem toAlgHom_unop (f : Aᵐᵒᵖ ≃ₐ[R] Bᵐᵒᵖ) : f.unop.toAlgHom = AlgHom.unop f.toAlgHom :=
  rfl
/-
**AlgEquiv.toRingEquiv_unop** 是 Mathlib 中的一个定理，位于命名空间 `AlgEquiv`。
形式化陈述：toRingEquiv_unop (f : Aᵐᵒᵖ ≃ₐ[R] Bᵐᵒᵖ) : (AlgEquiv.unop f).toRingEquiv = R
ingEquiv.unop f.toRingEquiv
参数：f : Aᵐᵒᵖ ≃ₐ[R] Bᵐᵒᵖ。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem toRingEquiv_unop (f : Aᵐᵒᵖ ≃ₐ[R] Bᵐᵒᵖ) :
    (AlgEquiv.unop f).toRingEquiv = RingEquiv.unop f.toRingEquiv :=
  rfl

#adaptation_note
/-- `respectTransparency.types true` changes the auto-generated lemmas' signature -/
set_option backward.isDefEq.respectTransparency.types false in
/-- Swap the `ᵐᵒᵖ` on an algebra isomorphism to the opposite side. -/
@[simps!]
/-
**AlgEquiv.opComm** 是 Mathlib 中的一个定义，位于命名空间 `AlgEquiv`。
形式化陈述：opComm : (A ≃ₐ[R] Bᵐᵒᵖ) ≃ (Aᵐᵒᵖ ≃ₐ[R] B)
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.trans`：Equiv.trans {s t u : Computation α} : s ~ t -> t ~ u -> s ~
 u

--- 原说明 ---
Swap the `ᵐᵒᵖ` on an algebra isomorphism to the opposite side.
-/
def opComm : (A ≃ₐ[R] Bᵐᵒᵖ) ≃ (Aᵐᵒᵖ ≃ₐ[R] B) :=
  AlgEquiv.op.trans <| AlgEquiv.refl.equivCongr (opOp R B).symm

variable (R S)

/-- The canonical algebra isomorphism from `Aᵐᵒᵖ` to `Module.End A A` induced by the right
multiplication. -/
/-
**AlgEquiv.moduleEndSelf** 是 Mathlib 中的一个定义，位于命名空间 `AlgEquiv`。
形式化陈述：(R : Type u_1) →   {A : Type u_3} → [inst : CommSemiring R] → [inst_1 : Se
miring A] → [inst_2 : Algebra R A] → Aᵐᵒᵖ ≃ₐ[R] Module.End A A
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A

--- 原说明 ---
The canonical algebra isomorphism from `Aᵐᵒᵖ` to `Module.End A A` induced by the
 right
multiplication.
-/
@[simps!] def moduleEndSelf : Aᵐᵒᵖ ≃ₐ[R] Module.End A A where
  __ := RingEquiv.moduleEndSelf A
  commutes' _ := by ext; simp [Algebra.algebraMap_eq_smul_one]

/-- The canonical algebra isomorphism from `A` to `Module.End Aᵐᵒᵖ A` induced by the left
multiplication. -/
/-
**AlgEquiv.moduleEndSelfOp** 是 Mathlib 中的一个定义，位于命名空间 `AlgEquiv`。
形式化陈述：(R : Type u_1) →   {A : Type u_3} → [inst : CommSemiring R] → [inst_1 : Se
miring A] → [inst_2 : Algebra R A] → A ≃ₐ[R] Module.End Aᵐᵒᵖ A
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The canonical algebra isomorphism from `A` to `Module.End Aᵐᵒᵖ A` induced by the
 left
multiplication.
-/
@[simps!] def moduleEndSelfOp : A ≃ₐ[R] Module.End Aᵐᵒᵖ A where
  __ := RingEquiv.moduleEndSelfOp A
  commutes' _ := by ext; simp [Algebra.algebraMap_eq_smul_one]

end AlgEquiv

end Semiring

section CommSemiring
variable (R A) [CommSemiring R] [CommSemiring A] [Algebra R A]

namespace AlgEquiv

/-- A commutative algebra is isomorphic to its opposite. -/
@[simps!]
/-
**AlgEquiv.toOpposite** 是 Mathlib 中的一个定义，位于命名空间 `AlgEquiv`。
形式化陈述：toOpposite : A ≃ₐ[R] Aᵐᵒᵖ where __
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A commutative algebra is isomorphic to its opposite.
-/
def toOpposite : A ≃ₐ[R] Aᵐᵒᵖ where
  __ := RingEquiv.toOpposite A
  commutes' _r := rfl
/-
**AlgEquiv.toRingEquiv_toOpposite** 是 Mathlib 中的一个定理，位于命名空间 `AlgEquiv`。
形式化陈述：∀ (R : Type u_1) (A : Type u_3) [inst : CommSemiring R] [inst_1 : CommSemi
ring A] [inst_2 : Algebra R A],   (AlgEquiv.toOpposite R A).toRingEquiv = RingEq
uiv.toOpposite A
参数：R : Type u_1；A : Type u_3；AlgEquiv.toOpposite R A。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma toRingEquiv_toOpposite : (toOpposite R A : A ≃+* Aᵐᵒᵖ) = RingEquiv.toOpposite A := rfl
/-
**AlgEquiv.toLinearEquiv_toOpposite** 是 Mathlib 中的一个定理，位于命名空间 `AlgEquiv`。
形式化陈述：∀ (R : Type u_1) (A : Type u_3) [inst : CommSemiring R] [inst_1 : CommSemi
ring A] [inst_2 : Algebra R A],   ↑(AlgEquiv.toOpposite R A) = MulOpposite.opLin
earEquiv R
参数：R : Type u_1；A : Type u_3；AlgEquiv.toOpposite R A。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma toLinearEquiv_toOpposite : toLinearEquiv (toOpposite R A) = opLinearEquiv R := rfl

end AlgEquiv

end CommSemiring

