/-
Copyright (c) 2018 Andreas Swerdlow. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andreas Swerdlow, Kenny Lau
-/
module

public import Mathlib.Algebra.Ring.Equiv
public import Mathlib.Algebra.Ring.Opposite

/-!
# Ring involutions

This file defines a ring involution as a structure extending `R ≃+* Rᵐᵒᵖ`,
with the additional fact `f.involution : (f (f x).unop).unop = x`.

## Notation

We provide a coercion to a function `R → Rᵐᵒᵖ`.

## References

* <https://en.wikipedia.org/wiki/Involution_(mathematics)#Ring_theory>

## Tags

Ring involution
-/

@[expose] public section

variable {F : Type*} (R : Type*)

/-- A ring involution -/
/-
**RingInvo** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：(R : Type u_2) → [Semiring R] → Type u_2
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A ring involution
-/
structure RingInvo [Semiring R] extends R ≃+* Rᵐᵒᵖ where
  /-- The requirement that the ring homomorphism is its own inverse -/
  involution' : ∀ x, (toFun (toFun x).unop).unop = x

/-- The equivalence of rings underlying a ring involution. -/
add_decl_doc RingInvo.toRingEquiv

/-- `RingInvoClass F R` states that `F` is a type of ring involutions.
You should extend this class when you extend `RingInvo`. -/
/-
**RingInvoClass** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：(F : Type u_3) → (R : Type u_4) → [Semiring R] → [EquivLike F R Rᵐᵒᵖ] → Pr
op
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`RingInvoClass F R` states that `F` is a type of ring involutions.
You should extend this class when you extend `RingInvo`.
-/
class RingInvoClass (F R : Type*) [Semiring R] [EquivLike F R Rᵐᵒᵖ] : Prop
  extends RingEquivClass F R Rᵐᵒᵖ where
  /-- Every ring involution must be its own inverse -/
  involution : ∀ (f : F) (x), (f (f x).unop).unop = x


/-- Turn an element of a type `F` satisfying `RingInvoClass F R` into an actual
`RingInvo`. This is declared as the default coercion from `F` to `RingInvo R`. -/
@[coe]
/-
**RingInvoClass.toRingInvo** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：RingInvoClass.toRingInvo {R} [Semiring R] [EquivLike F R Rᵐᵒᵖ] [RingInvoCl
ass F R] (f : F) : RingInvo R
参数：f : F。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `RingInvoClass.toRingEquivClass`：∀ {F : Type u_3} {R : Type u_4} {inst : 
Semiring R} {inst_1 : EquivLike F R Rᵐᵒᵖ} [self : RingInvoClass F R],   RingEqui
vClass F R Rᵐᵒᵖ
· 使用定理 `RingInvoClass.involution`：∀ {F : Type u_3} {R : Type u_4} {inst : Semiri
ng R} {inst_1 : EquivLike F R Rᵐᵒᵖ} [self : RingInvoClass F R] (f : F)   (x : R)
, MulOpposite.…

--- 原说明 ---
Turn an element of a type `F` satisfying `RingInvoClass F R` into an actual
`RingInvo`. This is declared as the default coercion from `F` to `RingInvo R`.
-/
def RingInvoClass.toRingInvo {R} [Semiring R] [EquivLike F R Rᵐᵒᵖ] [RingInvoClass F R] (f : F) :
    RingInvo R :=
  { (RingEquivClass.toRingEquiv f : R ≃+* Rᵐᵒᵖ) with involution' := RingInvoClass.involution f }

namespace RingInvo

variable {R} [Semiring R] [EquivLike F R Rᵐᵒᵖ]

/-- Any type satisfying `RingInvoClass` can be cast into `RingInvo` via
`RingInvoClass.toRingInvo`. -/
/-
**RingInvo.** 是 Mathlib 中的一个实例，位于命名空间 `RingInvo`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Any type satisfying `RingInvoClass` can be cast into `RingInvo` via
`RingInvoClass.toRingInvo`.
-/
instance [RingInvoClass F R] : CoeTC F (RingInvo R) :=
  ⟨RingInvoClass.toRingInvo⟩
/-
**RingInvo.** 是 Mathlib 中的一个实例，位于命名空间 `RingInvo`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : EquivLike (RingInvo R) R Rᵐᵒᵖ where
  coe f := f.toFun
  inv f := f.invFun
  coe_injective' e f h₁ h₂ := by
    rcases e with ⟨⟨tE, _⟩, _⟩; rcases f with ⟨⟨tF, _⟩, _⟩
    cases tE
    cases tF
    congr
  left_inv f := f.left_inv
  right_inv f := f.right_inv
/-
**RingInvo.** 是 Mathlib 中的一个实例，位于命名空间 `RingInvo`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : RingInvoClass (RingInvo R) R where
  map_add f := f.map_add'
  map_mul f := f.map_mul'
  involution f := f.involution'
/-
**RingInvo.** 是 Mathlib 中的一个实例，位于命名空间 `RingInvo`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : CoeOut (RingInvo R) (R ≃+* Rᵐᵒᵖ) where coe := toRingEquiv

/-- Construct a ring involution from a ring homomorphism. -/
/-
**RingInvo.mk'** 是 Mathlib 中的一个定义，位于命名空间 `RingInvo`。
形式化陈述：mk' (f : R ->+* Rᵐᵒᵖ) (involution : forall r, (f (f r).unop).unop = r) : R
ingInvo R
参数：f : R ->+* Rᵐᵒᵖ；involution : forall r, (f (f r).unop).unop = r。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Construct a ring involution from a ring homomorphism.
-/
def mk' (f : R →+* Rᵐᵒᵖ) (involution : ∀ r, (f (f r).unop).unop = r) : RingInvo R :=
  { f with
    invFun := fun r => (f r.unop).unop
    left_inv := fun r => involution r
    right_inv := fun _ => MulOpposite.unop_injective <| involution _
    involution' := involution }

@[simp]
/-
**RingInvo.involution** 是 Mathlib 中的一个定理，位于命名空间 `RingInvo`。
形式化陈述：involution (f : RingInvo R) (x : R) : (f (f x).unop).unop = x
参数：f : RingInvo R；x : R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RingInvo.involution'`：∀ {R : Type u_2} [inst : Semiring R] (self : RingI
nvo R) (x : R),   MulOpposite.unop (self.toFun (MulOpposite.unop (self.toFun x))
) = x
-/
theorem involution (f : RingInvo R) (x : R) : (f (f x).unop).unop = x :=
  f.involution' x
/-
**RingInvo.coe_ringEquiv** 是 Mathlib 中的一个定理，位于命名空间 `RingInvo`。
形式化陈述：coe_ringEquiv (f : RingInvo R) (a : R) : (f : R ≃+* Rᵐᵒᵖ) a = f a
参数：f : RingInvo R；a : R。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_ringEquiv (f : RingInvo R) (a : R) : (f : R ≃+* Rᵐᵒᵖ) a = f a :=
  rfl
/-
**RingInvo.map_eq_zero_iff** 是 Mathlib 中的一个定理，位于命名空间 `RingInvo`。
形式化陈述：map_eq_zero_iff (f : RingInvo R) {x : R} : f x = 0 ↔ x = 0
参数：f : RingInvo R。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RingEquiv.map_eq_zero_iff`：∀ {R : Type u_4} {S : Type u_5} [inst : NonUn
italNonAssocSemiring R] [inst_1 : NonUnitalNonAssocSemiring S]   (f : R ≃+* S) {
x : R}, f x = 0…
-/
theorem map_eq_zero_iff (f : RingInvo R) {x : R} : f x = 0 ↔ x = 0 :=
  f.toRingEquiv.map_eq_zero_iff

end RingInvo

open RingInvo

section CommRing

variable [CommRing R]

/-- The identity function of a `CommRing` is a ring involution. -/
/-
**RingInvo.id** 是 Mathlib 中的一个定义，位于命名空间 `RingInvo`。
形式化陈述：(R : Type u_2) → [inst : CommRing R] → RingInvo R
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The identity function of a `CommRing` is a ring involution.
-/
protected def RingInvo.id : RingInvo R :=
  { RingEquiv.toOpposite R with involution' := fun _ => rfl }
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Inhabited (RingInvo R) :=
  ⟨RingInvo.id _⟩

end CommRing

