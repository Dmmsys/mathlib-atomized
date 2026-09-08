/-
Copyright (c) 2026 Monica Omar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Monica Omar
-/
module

public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.Module.Equiv.Defs
public import Mathlib.Algebra.Module.TransferInstance

/-! # Type synonym for linear map convolutive ring and intrinsic star

This files provides the type synonym `WithConv` which we will use in later files
to put the convolutive product on linear maps instance and the intrinsic star instance.
This is to ensure that we only have one multiplication, one unit, and one star.

This is given for any type `A` so that we can have `WithConv (A →ₗ[R] B)`,
`WithConv (A →L[R] B)`, `WithConv (Matrix m n R)`, etc.
-/

@[expose] public section

/-- A type synonym for the convolutive product of linear maps and intrinsic star.

The instances for the convolutive product and intrinsic star are only available with this type.

Use `WithConv.linearEquiv` to coerce into this type. -/
/-
**WithConv** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：Sort u_1 → Sort (max 1 u_1)
参数：max 1 u_1。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A type synonym for the convolutive product of linear maps and intrinsic star.

The instances for the convolutive product and intrinsic star are only available 
with this type.

Use `WithConv.linearEquiv` to coerce into this type.
-/
structure WithConv A where
  /-- Converts an element of `A` to `WithConv A`. -/ toConv ::
  /-- Converts an element of `WithConv A` back to `A`. -/ ofConv : A

namespace WithConv

open Lean.PrettyPrinter.Delaborator in
/-- This prevents `toConv x` being printed as `{ ofConv := x }` by `delabStructureInstance`. -/
@[app_delab toConv]
meta def delabToConv : Delab := delabApp

variable {R A B C : Type*}

/-
**WithConv.ofConv_toConv** 是 Mathlib 中的一个引理，位于命名空间 `WithConv`。
形式化陈述：ofConv_toConv (x : A) : ofConv (toConv x) = x
参数：x : A。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma ofConv_toConv (x : A) : ofConv (toConv x) = x := rfl
/-
**WithConv.toConv_ofConv** 是 Mathlib 中的一个定理，位于命名空间 `WithConv`。
形式化陈述：∀ {A : Type u_2} (x : WithConv A), WithConv.toConv x.ofConv = x
参数：x : WithConv A。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma toConv_ofConv (x : WithConv A) : toConv (ofConv x) = x := rfl
/-
**WithConv.ofConv_surjective** 是 Mathlib 中的一个引理，位于命名空间 `WithConv`。
形式化陈述：ofConv_surjective : Function.Surjective (@ofConv A)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.RightInverse.surjective`：∀ {α : Sort u_1} {β : Sort u_2} {f : α
 → β} {g : β → α}, Function.RightInverse g f → Function.Surjective f
· 使用引理 `WithConv.ofConv_toConv`：ofConv_toConv (x : A) : ofConv (toConv x) = x
-/
lemma ofConv_surjective : Function.Surjective (@ofConv A) :=
  Function.RightInverse.surjective ofConv_toConv
/-
**WithConv.toConv_surjective** 是 Mathlib 中的一个引理，位于命名空间 `WithConv`。
形式化陈述：toConv_surjective : Function.Surjective (@toConv A)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.RightInverse.surjective`：∀ {α : Sort u_1} {β : Sort u_2} {f : α
 → β} {g : β → α}, Function.RightInverse g f → Function.Surjective f
· 使用定理 `WithConv.toConv_ofConv`：∀ {A : Type u_2} (x : WithConv A), WithConv.toCo
nv x.ofConv = x
-/
lemma toConv_surjective : Function.Surjective (@toConv A) :=
  Function.RightInverse.surjective toConv_ofConv
/-
**WithConv.ofConv_injective** 是 Mathlib 中的一个引理，位于命名空间 `WithConv`。
形式化陈述：ofConv_injective : Function.Injective (@ofConv A)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.LeftInverse.injective`：∀ {α : Sort u_1} {β : Sort u_2} {g : β →
 α} {f : α → β}, Function.LeftInverse g f → Function.Injective f
· 使用定理 `WithConv.toConv_ofConv`：∀ {A : Type u_2} (x : WithConv A), WithConv.toCo
nv x.ofConv = x
-/
lemma ofConv_injective : Function.Injective (@ofConv A) :=
  Function.LeftInverse.injective toConv_ofConv
/-
**WithConv.toConv_injective** 是 Mathlib 中的一个引理，位于命名空间 `WithConv`。
形式化陈述：toConv_injective : Function.Injective (@toConv A)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.LeftInverse.injective`：∀ {α : Sort u_1} {β : Sort u_2} {g : β →
 α} {f : α → β}, Function.LeftInverse g f → Function.Injective f
· 使用引理 `WithConv.ofConv_toConv`：ofConv_toConv (x : A) : ofConv (toConv x) = x
-/
lemma toConv_injective : Function.Injective (@toConv A) :=
  Function.LeftInverse.injective ofConv_toConv
/-
**WithConv.ofConv_bijective** 是 Mathlib 中的一个引理，位于命名空间 `WithConv`。
形式化陈述：ofConv_bijective : Function.Bijective (@ofConv A)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `WithConv.ofConv_injective`：ofConv_injective : Function.Injective (@ofCon
v A)
· 使用引理 `WithConv.ofConv_surjective`：ofConv_surjective : Function.Surjective (@of
Conv A)
-/
lemma ofConv_bijective : Function.Bijective (@ofConv A) := ⟨ofConv_injective, ofConv_surjective⟩
/-
**WithConv.toConv_bijective** 是 Mathlib 中的一个引理，位于命名空间 `WithConv`。
形式化陈述：toConv_bijective : Function.Bijective (@toConv A)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `WithConv.toConv_injective`：toConv_injective : Function.Injective (@toCon
v A)
· 使用引理 `WithConv.toConv_surjective`：toConv_surjective : Function.Surjective (@to
Conv A)
-/
lemma toConv_bijective : Function.Bijective (@toConv A) := ⟨toConv_injective, toConv_surjective⟩
/-
**WithConv.** 是 Mathlib 中的一个实例，位于命名空间 `WithConv`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [CoeFun A (fun _ ↦ B → C)] : CoeFun (WithConv A) (fun _ ↦ B → C) where coe f := ⇑f.ofConv
/-
**WithConv.ext** 是 Mathlib 中的一个定理，位于命名空间 `WithConv`。
形式化陈述：∀ {A : Type u_2} {x y : WithConv A}, x.ofConv = y.ofConv → x = y
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `WithConv.ofConv_injective`：ofConv_injective : Function.Injective (@ofCon
v A)
-/
@[ext] protected theorem ext {x y : WithConv A}
    (h : x.ofConv = y.ofConv) : x = y := ofConv_injective h

variable (A) in
/-- `WithConv.ofConv` and `WithConv.toConv` as an equivalence. -/
/-
**WithConv.equiv** 是 Mathlib 中的一个定义，位于命名空间 `WithConv`。
形式化陈述：(A : Type u_2) → WithConv A ≃ A
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`WithConv.ofConv` and `WithConv.toConv` as an equivalence.
-/
protected def equiv : WithConv A ≃ A where
  toFun := ofConv
  invFun := toConv
  left_inv _ := rfl
  right_inv _ := rfl
/-
**WithConv.equiv_apply** 是 Mathlib 中的一个定理，位于命名空间 `WithConv`。
形式化陈述：∀ {A : Type u_2} (x : WithConv A), (WithConv.equiv A) x = x.ofConv
参数：x : WithConv A；WithConv.equiv A。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma equiv_apply (x : WithConv A) : WithConv.equiv A x = x.ofConv := rfl
/-
**WithConv.symm_equiv_apply** 是 Mathlib 中的一个定理，位于命名空间 `WithConv`。
形式化陈述：∀ {A : Type u_2} (x : A), (WithConv.equiv A).symm x = WithConv.toConv x
参数：x : A；WithConv.equiv A。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
-/
@[simp] lemma symm_equiv_apply (x : A) : (WithConv.equiv A).symm x = toConv x := rfl
/-
**WithConv.** 是 Mathlib 中的一个实例，位于命名空间 `WithConv`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Nontrivial A] : Nontrivial (WithConv A) := (WithConv.equiv A).nontrivial
/-
**WithConv.** 是 Mathlib 中的一个实例，位于命名空间 `WithConv`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Unique A] : Unique (WithConv A) := (WithConv.equiv A).unique
/-
**WithConv.** 是 Mathlib 中的一个实例，位于命名空间 `WithConv`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [DecidableEq A] : DecidableEq (WithConv A) := (WithConv.equiv A).decidableEq
/-
**WithConv.** 是 Mathlib 中的一个实例，位于命名空间 `WithConv`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [AddMonoid A] : AddMonoid (WithConv A) := (WithConv.equiv A).addMonoid
/-
**WithConv.** 是 Mathlib 中的一个实例，位于命名空间 `WithConv`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [AddCommMonoid A] : AddCommMonoid (WithConv A) := (WithConv.equiv A).addCommMonoid
/-
**WithConv.** 是 Mathlib 中的一个实例，位于命名空间 `WithConv`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [AddGroup A] : AddGroup (WithConv A) := (WithConv.equiv A).addGroup
/-
**WithConv.** 是 Mathlib 中的一个实例，位于命名空间 `WithConv`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [AddCommGroup A] : AddCommGroup (WithConv A) := (WithConv.equiv A).addCommGroup
/-
**WithConv.** 是 Mathlib 中的一个实例，位于命名空间 `WithConv`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[to_additive] instance [Monoid R] [MulAction R A] : MulAction R (WithConv A) :=
  fast_instance% (WithConv.equiv A).mulAction R
/-
**WithConv.** 是 Mathlib 中的一个实例，位于命名空间 `WithConv`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Monoid R] [AddCommMonoid A] [DistribMulAction R A] : DistribMulAction R (WithConv A) :=
  fast_instance% (WithConv.equiv A).distribMulAction R
/-
**WithConv.** 是 Mathlib 中的一个实例，位于命名空间 `WithConv`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Semiring R] [AddCommMonoid A] [Module R A] : Module R (WithConv A) :=
  fast_instance% (WithConv.equiv A).module R

/-- Lift an equivalence between `A` and `B` to `WithConv A` and `WithConv B`. -/
/-
**WithConv.congr** 是 Mathlib 中的一个定义，位于命名空间 `WithConv`。
形式化陈述：{A : Type u_2} → {B : Type u_3} → A ≃ B → WithConv A ≃ WithConv B
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.trans`：Equiv.trans {s t u : Computation α} : s ~ t -> t ~ u -> s ~
 u
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s

--- 原说明 ---
Lift an equivalence between `A` and `B` to `WithConv A` and `WithConv B`.
-/
protected def congr (f : A ≃ B) : WithConv A ≃ WithConv B :=
  (WithConv.equiv A).trans (f.trans (WithConv.equiv B).symm)
/-
**WithConv.congr_apply** 是 Mathlib 中的一个定理，位于命名空间 `WithConv`。
形式化陈述：∀ {A : Type u_2} {B : Type u_3} (f : A ≃ B) (x : WithConv A), (WithConv.co
ngr f) x = WithConv.toConv (f x.ofConv)
参数：f : A ≃ B；x : WithConv A；WithConv.congr f；f x.ofConv。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma congr_apply (f : A ≃ B) (x : WithConv A) :
    WithConv.congr f x = toConv (f x.ofConv) := rfl
/-
**WithConv.symm_congr** 是 Mathlib 中的一个定理，位于命名空间 `WithConv`。
形式化陈述：∀ {A : Type u_2} {B : Type u_3} (f : A ≃ B), (WithConv.congr f).symm = Wit
hConv.congr f.symm
参数：f : A ≃ B；WithConv.congr f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
-/
@[simp] lemma symm_congr (f : A ≃ B) : (WithConv.congr f).symm = WithConv.congr f.symm := rfl
/-
**WithConv.symm_congr_apply** 是 Mathlib 中的一个引理，位于命名空间 `WithConv`。
形式化陈述：symm_congr_apply (f : A ≃ B) (x : WithConv B) : (WithConv.congr f).symm x 
= toConv (f.symm x.ofConv)
参数：f : A ≃ B；x : WithConv B。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma symm_congr_apply (f : A ≃ B) (x : WithConv B) :
    (WithConv.congr f).symm x = toConv (f.symm x.ofConv) := by simp

section AddGroup
variable [AddGroup A]

/-
**WithConv.toConv_sub** 是 Mathlib 中的一个定理，位于命名空间 `WithConv`。
形式化陈述：∀ {A : Type u_2} [inst : AddGroup A] (x y : A), WithConv.toConv (x - y) = 
WithConv.toConv x - WithConv.toConv y
参数：x y : A；x - y。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma toConv_sub (x y : A) : toConv (x - y) = toConv x - toConv y := rfl
/-
**WithConv.ofConv_sub** 是 Mathlib 中的一个定理，位于命名空间 `WithConv`。
形式化陈述：∀ {A : Type u_2} [inst : AddGroup A] (x y : WithConv A), (x - y).ofConv = 
x.ofConv - y.ofConv
参数：x y : WithConv A；x - y。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma ofConv_sub (x y : WithConv A) : ofConv (x - y) = ofConv x - ofConv y := rfl
/-
**WithConv.ofConv_neg** 是 Mathlib 中的一个定理，位于命名空间 `WithConv`。
形式化陈述：∀ {A : Type u_2} [inst : AddGroup A] (x : WithConv A), (-x).ofConv = -x.of
Conv
参数：x : WithConv A；-x。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma ofConv_neg (x : WithConv A) : ofConv (-x) = -ofConv x := rfl
/-
**WithConv.toConv_neg** 是 Mathlib 中的一个定理，位于命名空间 `WithConv`。
形式化陈述：∀ {A : Type u_2} [inst : AddGroup A] (x : A), WithConv.toConv (-x) = -With
Conv.toConv x
参数：x : A；-x。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma toConv_neg (x : A) : toConv (-x) = -toConv x := rfl

end AddGroup

/-
**WithConv.ofConv_smul** 是 Mathlib 中的一个定理，位于命名空间 `WithConv`。
形式化陈述：∀ {R : Type u_1} {A : Type u_2} [inst : Monoid R] [inst_1 : MulAction R A]
 (c : R) (x : WithConv A),   (c • x).ofConv = c • x.ofConv
参数：c : R；x : WithConv A；c • x。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma ofConv_smul [Monoid R] [MulAction R A] (c : R) (x : WithConv A) :
    ofConv (c • x) = c • ofConv x := rfl
/-
**WithConv.toConv_smul** 是 Mathlib 中的一个定理，位于命名空间 `WithConv`。
形式化陈述：∀ {R : Type u_1} {A : Type u_2} [inst : Monoid R] [inst_1 : MulAction R A]
 (c : R) (x : A),   WithConv.toConv (c • x) = c • WithConv.toConv x
参数：c : R；x : A；c • x。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma toConv_smul [Monoid R] [MulAction R A] (c : R) (x : A) :
    toConv (c • x) = c • toConv x := rfl

section
variable [AddMonoid A]

/-
**WithConv.ofConv_zero** 是 Mathlib 中的一个定理，位于命名空间 `WithConv`。
形式化陈述：∀ {A : Type u_2} [inst : AddMonoid A], WithConv.ofConv 0 = 0
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma ofConv_zero : ofConv (0 : WithConv A) = 0 := rfl
/-
**WithConv.toConv_zero** 是 Mathlib 中的一个定理，位于命名空间 `WithConv`。
形式化陈述：∀ {A : Type u_2} [inst : AddMonoid A], WithConv.toConv 0 = 0
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma toConv_zero : toConv (0 : A) = 0 := rfl
/-
**WithConv.ofConv_add** 是 Mathlib 中的一个定理，位于命名空间 `WithConv`。
形式化陈述：∀ {A : Type u_2} [inst : AddMonoid A] (x y : WithConv A), (x + y).ofConv =
 x.ofConv + y.ofConv
参数：x y : WithConv A；x + y。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma ofConv_add (x y : WithConv A) : ofConv (x + y) = ofConv x + ofConv y := rfl
/-
**WithConv.toConv_add** 是 Mathlib 中的一个定理，位于命名空间 `WithConv`。
形式化陈述：∀ {A : Type u_2} [inst : AddMonoid A] (x y : A), WithConv.toConv (x + y) =
 WithConv.toConv x + WithConv.toConv y
参数：x y : A；x + y。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma toConv_add (x y : A) : toConv (x + y) = toConv x + toConv y := rfl
/-
**WithConv.ofConv_eq_zero** 是 Mathlib 中的一个定理，位于命名空间 `WithConv`。
形式化陈述：∀ {A : Type u_2} [inst : AddMonoid A] {x : WithConv A}, x.ofConv = 0 ↔ x =
 0
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Injective.eq_iff`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β}, 
Function.Injective f → ∀ {a b : α}, f a = f b ↔ a = b
· 使用引理 `WithConv.ofConv_injective`：ofConv_injective : Function.Injective (@ofCon
v A)
-/
@[simp] lemma ofConv_eq_zero {x : WithConv A} : ofConv x = 0 ↔ x = 0 := ofConv_injective.eq_iff
/-
**WithConv.toConv_eq_zero** 是 Mathlib 中的一个定理，位于命名空间 `WithConv`。
形式化陈述：∀ {A : Type u_2} [inst : AddMonoid A] {x : A}, WithConv.toConv x = 0 ↔ x =
 0
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Injective.eq_iff`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β}, 
Function.Injective f → ∀ {a b : α}, f a = f b ↔ a = b
· 使用引理 `WithConv.toConv_injective`：toConv_injective : Function.Injective (@toCon
v A)
-/
@[simp] lemma toConv_eq_zero {x : A} : toConv x = 0 ↔ x = 0 := toConv_injective.eq_iff

variable (A) in
/-- The additive equivalence between `WithConv A` and `A`. -/
/-
**WithConv.addEquiv** 是 Mathlib 中的一个定义，位于命名空间 `WithConv`。
形式化陈述：(A : Type u_2) → [inst : AddMonoid A] → WithConv A ≃+ A
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The additive equivalence between `WithConv A` and `A`.
-/
@[simps!] protected def addEquiv : WithConv A ≃+ A where
  __ := WithConv.equiv A
  map_add' := by simp
/-
**WithConv.toEquiv_addEquiv** 是 Mathlib 中的一个定理，位于命名空间 `WithConv`。
形式化陈述：∀ {A : Type u_2} [inst : AddMonoid A], ↑(WithConv.addEquiv A) = WithConv.e
quiv A
参数：WithConv.addEquiv A。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] theorem toEquiv_addEquiv : (WithConv.addEquiv A : WithConv A ≃ A) = WithConv.equiv A := rfl

end

variable [AddCommMonoid A]

variable (R A) in
/-- The linear equivalence between `WithConv A` and `A`. -/
/-
**WithConv.linearEquiv** 是 Mathlib 中的一个定义，位于命名空间 `WithConv`。
形式化陈述：(R : Type u_1) →   (A : Type u_2) → [inst : AddCommMonoid A] → [inst_1 : S
emiring R] → [inst_2 : _root_.Module R A] → WithConv A ≃ₗ[R] A
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The linear equivalence between `WithConv A` and `A`.
-/
protected def linearEquiv [Semiring R] [Module R A] : WithConv A ≃ₗ[R] A where
  __ := WithConv.addEquiv A
  map_smul' := by simp
/-
**WithConv.linearEquiv_apply** 是 Mathlib 中的一个定理，位于命名空间 `WithConv`。
形式化陈述：∀ {R : Type u_1} {A : Type u_2} [inst : AddCommMonoid A] [inst_1 : Semirin
g R] [inst_2 : _root_.Module R A]   (a : WithConv A), (WithConv.linearEquiv R A)
 a = a.ofConv
参数：a : WithConv A；WithConv.linearEquiv R A。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma linearEquiv_apply [Semiring R] [Module R A]
    (a : WithConv A) : WithConv.linearEquiv R A a = ofConv a := rfl
/-
**WithConv.symm_linearEquiv_apply** 是 Mathlib 中的一个定理，位于命名空间 `WithConv`。
形式化陈述：∀ {R : Type u_1} {A : Type u_2} [inst : AddCommMonoid A] [inst_1 : Semirin
g R] [inst_2 : _root_.Module R A] (a : A),   (WithConv.linearEquiv R A).symm a =
 WithConv.toConv a
参数：a : A；WithConv.linearEquiv R A。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma symm_linearEquiv_apply [Semiring R] [Module R A]
    (a : A) : (WithConv.linearEquiv R A).symm a = toConv a := rfl
/-
**WithConv.toAddEquiv_linearEquiv** 是 Mathlib 中的一个定理，位于命名空间 `WithConv`。
形式化陈述：∀ {R : Type u_1} {A : Type u_2} [inst : AddCommMonoid A] [inst_1 : Semirin
g R] [inst_2 : _root_.Module R A],   (WithConv.linearEquiv R A).toAddEquiv = Wit
hConv.addEquiv A
参数：WithConv.linearEquiv R A。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma toAddEquiv_linearEquiv [Semiring R] [Module R A] :
    (WithConv.linearEquiv R A).toAddEquiv = WithConv.addEquiv A := rfl
/-
**WithConv.ofConv_sum** 是 Mathlib 中的一个定理，位于命名空间 `WithConv`。
形式化陈述：∀ {A : Type u_2} [inst : AddCommMonoid A] {ι : Type u_5} (s : Finset ι) (f
 : ι → WithConv A),   (∑ i ∈ s, f i).ofConv = ∑ i ∈ s, (f i).ofConv
参数：s : Finset ι；f : ι → WithConv A；∑ i ∈ s, f i；f i。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `map_sum`：∀ {ι : Type u_1} {M : Type u_3} {N : Type u_4} [inst : AddCommM
onoid M] [inst_1 : AddCommMonoid N] {G : Type u_7}   [inst_2 : FunLike G M N]…
· 使用定理 `AddEquivClass.instAddMonoidHomClass`：∀ (F : Type u_1) {M : Type u_4} {N 
: Type u_5} [inst : EquivLike F M N] [inst_1 : AddZeroClass M]   [inst_2 : AddZe
roClass N] [AddEquivClass…
· 使用定理 `AddEquiv.instAddEquivClass`：∀ {M : Type u_4} {N : Type u_5} [inst : Add 
M] [inst_1 : Add N], AddEquivClass (M ≃+ N) M N
-/
@[simp] lemma ofConv_sum {ι : Type*} (s : Finset ι) (f : ι → WithConv A) :
    (∑ i ∈ s, f i).ofConv = ∑ i ∈ s, (f i).ofConv := map_sum (WithConv.addEquiv _) _ _
/-
**WithConv.toConv_sum** 是 Mathlib 中的一个定理，位于命名空间 `WithConv`。
形式化陈述：∀ {A : Type u_2} [inst : AddCommMonoid A] {ι : Type u_5} (s : Finset ι) (f
 : ι → A),   WithConv.toConv (∑ i ∈ s, f i) = ∑ i ∈ s, WithConv.toConv (f i)
参数：s : Finset ι；f : ι → A；∑ i ∈ s, f i；f i。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `map_sum`：∀ {ι : Type u_1} {M : Type u_3} {N : Type u_4} [inst : AddCommM
onoid M] [inst_1 : AddCommMonoid N] {G : Type u_7}   [inst_2 : FunLike G M N]…
· 使用定理 `AddEquivClass.instAddMonoidHomClass`：∀ (F : Type u_1) {M : Type u_4} {N 
: Type u_5} [inst : EquivLike F M N] [inst_1 : AddZeroClass M]   [inst_2 : AddZe
roClass N] [AddEquivClass…
· 使用定理 `AddEquiv.instAddEquivClass`：∀ {M : Type u_4} {N : Type u_5} [inst : Add 
M] [inst_1 : Add N], AddEquivClass (M ≃+ N) M N
-/
@[simp] lemma toConv_sum {ι : Type*} (s : Finset ι) (f : ι → A) :
    toConv (∑ i ∈ s, f i) = ∑ i ∈ s, toConv (f i) := map_sum (WithConv.addEquiv _).symm _ _
/-
**WithConv.ofConv_listSum** 是 Mathlib 中的一个定理，位于命名空间 `WithConv`。
形式化陈述：∀ {A : Type u_2} [inst : AddCommMonoid A] (l : List (WithConv A)), l.sum.o
fConv = (List.map WithConv.ofConv l).sum
参数：l : List (WithConv A)；List.map WithConv.ofConv l。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `map_list_sum`：∀ {M : Type u_4} {N : Type u_5} [inst : AddMonoid M] [inst
_1 : AddMonoid N] {F : Type u_8} [inst_2 : FunLike F M N]   [AddMonoidHomClass F
 M…
· 使用定理 `AddEquivClass.instAddMonoidHomClass`：∀ (F : Type u_1) {M : Type u_4} {N 
: Type u_5} [inst : EquivLike F M N] [inst_1 : AddZeroClass M]   [inst_2 : AddZe
roClass N] [AddEquivClass…
· 使用定理 `AddEquiv.instAddEquivClass`：∀ {M : Type u_4} {N : Type u_5} [inst : Add 
M] [inst_1 : Add N], AddEquivClass (M ≃+ N) M N
-/
@[simp] lemma ofConv_listSum (l : List (WithConv A)) :
    l.sum.ofConv = (l.map ofConv).sum := map_list_sum (WithConv.addEquiv _) _
/-
**WithConv.toConv_listSum** 是 Mathlib 中的一个定理，位于命名空间 `WithConv`。
形式化陈述：∀ {A : Type u_2} [inst : AddCommMonoid A] (l : List A), WithConv.toConv l.
sum = (List.map WithConv.toConv l).sum
参数：l : List A；List.map WithConv.toConv l。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `map_list_sum`：∀ {M : Type u_4} {N : Type u_5} [inst : AddMonoid M] [inst
_1 : AddMonoid N] {F : Type u_8} [inst_2 : FunLike F M N]   [AddMonoidHomClass F
 M…
· 使用定理 `AddEquivClass.instAddMonoidHomClass`：∀ (F : Type u_1) {M : Type u_4} {N 
: Type u_5} [inst : EquivLike F M N] [inst_1 : AddZeroClass M]   [inst_2 : AddZe
roClass N] [AddEquivClass…
· 使用定理 `AddEquiv.instAddEquivClass`：∀ {M : Type u_4} {N : Type u_5} [inst : Add 
M] [inst_1 : Add N], AddEquivClass (M ≃+ N) M N
-/
@[simp] lemma toConv_listSum (l : List A) :
    toConv l.sum = (l.map toConv).sum := map_list_sum (WithConv.addEquiv _).symm _
/-
**WithConv.ofConv_multisetSum** 是 Mathlib 中的一个定理，位于命名空间 `WithConv`。
形式化陈述：∀ {A : Type u_2} [inst : AddCommMonoid A] (s : Multiset (WithConv A)),   s
.sum.ofConv = (Multiset.map WithConv.ofConv s).sum
参数：s : Multiset (WithConv A)；Multiset.map WithConv.ofConv s。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `map_multiset_sum`：∀ {F : Type u_1} {M : Type u_5} {N : Type u_6} [inst :
 AddCommMonoid M] [inst_1 : AddCommMonoid N]   [inst_2 : FunLike F M N] [AddMono
idHomC…
· 使用定理 `AddEquivClass.instAddMonoidHomClass`：∀ (F : Type u_1) {M : Type u_4} {N 
: Type u_5} [inst : EquivLike F M N] [inst_1 : AddZeroClass M]   [inst_2 : AddZe
roClass N] [AddEquivClass…
· 使用定理 `AddEquiv.instAddEquivClass`：∀ {M : Type u_4} {N : Type u_5} [inst : Add 
M] [inst_1 : Add N], AddEquivClass (M ≃+ N) M N
-/
@[simp] lemma ofConv_multisetSum (s : Multiset (WithConv A)) :
    s.sum.ofConv = (s.map ofConv).sum := map_multiset_sum (WithConv.addEquiv _) _
/-
**WithConv.toConv_multisetSum** 是 Mathlib 中的一个定理，位于命名空间 `WithConv`。
形式化陈述：∀ {A : Type u_2} [inst : AddCommMonoid A] (s : Multiset A), WithConv.toCon
v s.sum = (Multiset.map WithConv.toConv s).sum
参数：s : Multiset A；Multiset.map WithConv.toConv s。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `map_multiset_sum`：∀ {F : Type u_1} {M : Type u_5} {N : Type u_6} [inst :
 AddCommMonoid M] [inst_1 : AddCommMonoid N]   [inst_2 : FunLike F M N] [AddMono
idHomC…
· 使用定理 `AddEquivClass.instAddMonoidHomClass`：∀ (F : Type u_1) {M : Type u_4} {N 
: Type u_5} [inst : EquivLike F M N] [inst_1 : AddZeroClass M]   [inst_2 : AddZe
roClass N] [AddEquivClass…
· 使用定理 `AddEquiv.instAddEquivClass`：∀ {M : Type u_4} {N : Type u_5} [inst : Add 
M] [inst_1 : Add N], AddEquivClass (M ≃+ N) M N
-/
@[simp] lemma toConv_multisetSum (s : Multiset A) :
    toConv s.sum = (s.map toConv).sum := map_multiset_sum (WithConv.addEquiv _).symm _

section
variable [Semiring R] [Module R A] [AddCommMonoid B] [Module R B]

/-- Lift a linear equivalence between `A` and `B` to `WithConv A` and `WithConv B`. -/
/-
**WithConv.congrLinearEquiv** 是 Mathlib 中的一个定义，位于命名空间 `WithConv`。
形式化陈述：congrLinearEquiv (f : A ≃ₗ[R] B) : WithConv A ≃ₗ[R] WithConv B
参数：f : A ≃ₗ[R] B。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Lift a linear equivalence between `A` and `B` to `WithConv A` and `WithConv B`.
-/
def congrLinearEquiv (f : A ≃ₗ[R] B) : WithConv A ≃ₗ[R] WithConv B :=
  (WithConv.linearEquiv R A).trans (f.trans (WithConv.linearEquiv R B).symm)
/-
**WithConv.congrLinearEquiv_apply** 是 Mathlib 中的一个定理，位于命名空间 `WithConv`。
形式化陈述：∀ {R : Type u_1} {A : Type u_2} {B : Type u_3} [inst : AddCommMonoid A] [i
nst_1 : Semiring R]   [inst_2 : _root_.Module R A] [inst_3 : AddCommMonoid B] [i
nst_4 : _root_.Module R B] (f : A ≃ₗ[R] B) (x : WithConv A),   (WithConv.congrLi
nearEquiv f) x = WithConv.toConv (f x.ofConv)
参数：f : A ≃ₗ[R] B；x : WithConv A；WithConv.congrLinearEquiv f；f x.ofConv。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma congrLinearEquiv_apply (f : A ≃ₗ[R] B) (x : WithConv A) :
    congrLinearEquiv f x = toConv (f x.ofConv) := rfl
/-
**WithConv.symm_congrLinearEquiv** 是 Mathlib 中的一个定理，位于命名空间 `WithConv`。
形式化陈述：∀ {R : Type u_1} {A : Type u_2} {B : Type u_3} [inst : AddCommMonoid A] [i
nst_1 : Semiring R]   [inst_2 : _root_.Module R A] [inst_3 : AddCommMonoid B] [i
nst_4 : _root_.Module R B] (f : A ≃ₗ[R] B),   (WithConv.congrLinearEquiv f).symm
 = WithConv.congrLinearEquiv f.symm
参数：f : A ≃ₗ[R] B；WithConv.congrLinearEquiv f。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma symm_congrLinearEquiv (f : A ≃ₗ[R] B) :
    (congrLinearEquiv f).symm = congrLinearEquiv f.symm := rfl
/-
**WithConv.symm_congrLinearEquiv_apply** 是 Mathlib 中的一个引理，位于命名空间 `WithConv`。
形式化陈述：symm_congrLinearEquiv_apply (f : A ≃ₗ[R] B) (x : WithConv B) : (congrLinea
rEquiv f).symm x = toConv (f.symm x.ofConv)
参数：f : A ≃ₗ[R] B；x : WithConv B。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma symm_congrLinearEquiv_apply (f : A ≃ₗ[R] B) (x : WithConv B) :
    (congrLinearEquiv f).symm x = toConv (f.symm x.ofConv) := by simp
/-
**WithConv.toEquiv_congrLinearEquiv** 是 Mathlib 中的一个定理，位于命名空间 `WithConv`。
形式化陈述：∀ {R : Type u_1} {A : Type u_2} {B : Type u_3} [inst : AddCommMonoid A] [i
nst_1 : Semiring R]   [inst_2 : _root_.Module R A] [inst_3 : AddCommMonoid B] [i
nst_4 : _root_.Module R B] (f : A ≃ₗ[R] B),   (WithConv.congrLinearEquiv f).toEq
uiv = WithConv.congr f.toEquiv
参数：f : A ≃ₗ[R] B；WithConv.congrLinearEquiv f。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] theorem toEquiv_congrLinearEquiv (f : A ≃ₗ[R] B) :
    (congrLinearEquiv f).toEquiv = WithConv.congr f.toEquiv := rfl

end

end WithConv

