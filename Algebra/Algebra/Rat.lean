/-
Copyright (c) 2018 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau, Yury Kudryashov
-/
module

public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Module.Equiv.Defs
public import Mathlib.Data.Rat.Cast.CharZero

/-!
# Further basic results about `Algebra`'s over `ℚ`.

This file could usefully be split further.
-/

public section

assert_not_exists Subgroup

variable {F R S : Type*}

namespace RingHom

@[simp]
/-
**RingHom.map_rat_algebraMap** 是 Mathlib 中的一个定理，位于命名空间 `RingHom`。
形式化陈述：map_rat_algebraMap [Semiring R] [Semiring S] [Algebra Rat R] [Algebra Rat 
S] (f : R ->+* S) (r : Rat) : f (algebraMap Rat R r) = algebraMap Rat S r
参数：f : R ->+* S；r : Rat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `RingHom.ext_iff`：∀ {α : Type u_2} {β : Type u_3} {x : NonAssocSemiring α
} {x_1 : NonAssocSemiring β} {f g : α →+* β},   f = g ↔ ∀ (x_2 : α), f x_2 = g x
_2
· 使用定理 `Subsingleton.elim`：∀ {α : Sort u} [h : Subsingleton α] (a b : α), a = b
-/
theorem map_rat_algebraMap [Semiring R] [Semiring S] [Algebra ℚ R] [Algebra ℚ S] (f : R →+* S)
    (r : ℚ) : f (algebraMap ℚ R r) = algebraMap ℚ S r :=
  RingHom.ext_iff.1 (Subsingleton.elim (f.comp (algebraMap ℚ R)) (algebraMap ℚ S)) r

end RingHom

namespace NNRat
variable [DivisionSemiring R] [CharZero R] [DivisionSemiring S] [CharZero S]

/-
**NNRat._root_.DivisionSemiring.toNNRatAlgebra** 是 Mathlib 中的一个实例，位于命名空间 `NNRat`
。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance _root_.DivisionSemiring.toNNRatAlgebra : Algebra ℚ≥0 R where
  smul_def' := smul_def
  algebraMap := castHom _
  commutes' := cast_commute
/-
**NNRat._root_.RingHomClass.toLinearMapClassNNRat** 是 Mathlib 中的一个实例，位于命名空间 `NNR
at`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance _root_.RingHomClass.toLinearMapClassNNRat [FunLike F R S] [RingHomClass F R S] :
    LinearMapClass F ℚ≥0 R S where
  map_smulₛₗ f q a := by simp [smul_def, cast_id]

variable [SMul R S]
/-
**NNRat.instSMulCommClass** 是 Mathlib 中的一个实例，位于命名空间 `NNRat`。
形式化陈述：instSMulCommClass [SMulCommClass R S S] : SMulCommClass Rat>=0 R S where s
mul_comm q a b
该定义给出了一等式。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `NNRat.smul_def`：smul_def (q : Rat>=0) (a : K) : q • a = q * a
· 使用引理 `mul_smul_comm`：mul_smul_comm [Mul β] [SMul α β] [SMulCommClass α β β] (s
 : α) (x y : β) : x * s • y = s • (x * y)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
instance instSMulCommClass [SMulCommClass R S S] : SMulCommClass ℚ≥0 R S where
  smul_comm q a b := by simp [smul_def, mul_smul_comm]
/-
**NNRat.instSMulCommClass'** 是 Mathlib 中的一个实例，位于命名空间 `NNRat`。
形式化陈述：instSMulCommClass' [SMulCommClass S R S] : SMulCommClass R Rat>=0 S
该定义给出了一等式。
本声明引用了以下数学事实（定理与引理）：
· 使用引理 `SMulCommClass.symm`：SMulCommClass.symm (M N α : Type*) [SMul M α] [SMul 
N α] [SMulCommClass M N α] : SMulCommClass N M α where smul_comm a' a b
-/
instance instSMulCommClass' [SMulCommClass S R S] : SMulCommClass R ℚ≥0 S :=
  have := SMulCommClass.symm S R S; SMulCommClass.symm _ _ _

end NNRat

namespace Rat
variable [DivisionRing R] [CharZero R] [DivisionRing S] [CharZero S]

/-
**Rat._root_.DivisionRing.toRatAlgebra** 是 Mathlib 中的一个实例，位于命名空间 `Rat`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance _root_.DivisionRing.toRatAlgebra : Algebra ℚ R where
  smul_def' := smul_def
  algebraMap := castHom _
  commutes' := cast_commute
/-
**Rat._root_.RingHomClass.toLinearMapClassRat** 是 Mathlib 中的一个实例，位于命名空间 `Rat`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance _root_.RingHomClass.toLinearMapClassRat [FunLike F R S] [RingHomClass F R S] :
    LinearMapClass F ℚ R S where
  map_smulₛₗ f q a := by simp [smul_def, cast_id]
/-
**Rat._root_.RingEquivClass.toLinearEquivClassRat** 是 Mathlib 中的一个实例，位于命名空间 `Rat
`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance _root_.RingEquivClass.toLinearEquivClassRat [EquivLike F R S] [RingEquivClass F R S] :
    LinearEquivClass F ℚ R S where
  map_smulₛₗ f c x := by simp [Algebra.smul_def]

variable [SMul R S]
/-
**Rat.instSMulCommClass** 是 Mathlib 中的一个实例，位于命名空间 `Rat`。
形式化陈述：instSMulCommClass [SMulCommClass R S S] : SMulCommClass Rat R S where smul
_comm q a b
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Rat.smul_def`：smul_def (a : Rat) (x : K) : a • x = ↑a * x
· 使用引理 `mul_smul_comm`：mul_smul_comm [Mul β] [SMul α β] [SMulCommClass α β β] (s
 : α) (x y : β) : x * s • y = s • (x * y)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
instance instSMulCommClass [SMulCommClass R S S] : SMulCommClass ℚ R S where
  smul_comm q a b := by simp [smul_def, mul_smul_comm]
/-
**Rat.instSMulCommClass'** 是 Mathlib 中的一个实例，位于命名空间 `Rat`。
形式化陈述：instSMulCommClass' [SMulCommClass S R S] : SMulCommClass R Rat S
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用引理 `SMulCommClass.symm`：SMulCommClass.symm (M N α : Type*) [SMul M α] [SMul 
N α] [SMulCommClass M N α] : SMulCommClass N M α where smul_comm a' a b
-/
instance instSMulCommClass' [SMulCommClass S R S] : SMulCommClass R ℚ S :=
  have := SMulCommClass.symm S R S; SMulCommClass.symm _ _ _
/-
**Rat.algebra_rat_subsingleton** 是 Mathlib 中的一个实例，位于命名空间 `Rat`。
形式化陈述：algebra_rat_subsingleton {R} [Semiring R] : Subsingleton (Algebra Rat R)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.algebra_ext`：algebra_ext {R : Type*} [CommSemiring R] {A : Type*
} [Semiring A] (P Q : Algebra R A) (h : forall r : R, (haveI
· 使用定理 `RingHom.congr_fun`：∀ {α : Type u_2} {β : Type u_3} {x : NonAssocSemiring
 α} {x_1 : NonAssocSemiring β} {f g : α →+* β},   f = g → ∀ (x_2 : α), f x_2 = g
 x_2
· 使用定理 `Subsingleton.elim`：∀ {α : Sort u} [h : Subsingleton α] (a b : α), a = b
-/
instance algebra_rat_subsingleton {R} [Semiring R] : Subsingleton (Algebra ℚ R) :=
  ⟨fun x y => Algebra.algebra_ext x y <| RingHom.congr_fun <| Subsingleton.elim _ _⟩

end Rat

