/-
Copyright (c) 2020 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
module

public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Notation.Support

/-!
# Support of a function

In this file we prove basic properties of `Function.support f = {x | f x ≠ 0}`, and similarly for
`Function.mulSupport f = {x | f x ≠ 1}`.
-/

public section

assert_not_exists CompleteLattice MonoidWithZero

open Set

variable {α M G : Type*}

namespace Function

@[to_additive]
/-
**Function.mulSupport_mul** 是 Mathlib 中的一个定理，位于命名空间 `Function`。
形式化陈述：mulSupport_mul [MulOneClass M] (f g : α -> M) : (mulSupport fun x => f x *
 g x) subseteq mulSupport f union mulSupport g
参数：f g : α -> M。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Function.mulSupport_binop_subset`：mulSupport_binop_subset (op : M -> N -
> P) (op1 : op 1 1 = 1) (f : ι -> M) (g : ι -> N) : mulSupport (fun x => op (f x
) (g x)) subseteq mulS…
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
-/
theorem mulSupport_mul [MulOneClass M] (f g : α → M) :
    (mulSupport fun x ↦ f x * g x) ⊆ mulSupport f ∪ mulSupport g :=
  mulSupport_binop_subset (· * ·) (one_mul _) f g

@[to_additive]
/-
**Function.mulSupport_pow** 是 Mathlib 中的一个定理，位于命名空间 `Function`。
形式化陈述：mulSupport_pow [Monoid M] (f : α -> M) (n : Nat) : (mulSupport fun x => f 
x ^ n) subseteq mulSupport f
参数：f : α -> M；n : Nat。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `pow_zero`：pow_zero (a : M) : a ^ 0 = 1
· 使用引理 `Function.mulSupport_fun_one`：mulSupport_fun_one : mulSupport (fun _ => 1
 : ι -> M) = ∅
· 使用定理 `pow_succ'`：∀ {M : Type u_2} [inst : Monoid M] (a : M) (n : ℕ), a ^ (n + 
1) = a * a ^ n
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `Function.mulSupport_mul`：mulSupport_mul [MulOneClass M] (f g : α -> M) :
 (mulSupport fun x => f x * g x) subseteq mulSupport f union mulSupport g
· 使用定理 `Set.union_subset`：union_subset {s t r : Set α} (sr : s subseteq r) (tr :
 t subseteq r) : s union t subseteq r
· 使用定理 `Set.Subset.rfl`：∀ {α : Type u} {s : Set α}, s ⊆ s
-/
theorem mulSupport_pow [Monoid M] (f : α → M) (n : ℕ) :
    (mulSupport fun x => f x ^ n) ⊆ mulSupport f := by
  induction n with
  | zero => simp [pow_zero]
  | succ n hfn =>
    simpa only [pow_succ'] using (mulSupport_mul f _).trans (union_subset Subset.rfl hfn)

section DivisionMonoid

variable [DivisionMonoid G] (f g : α → G)

@[to_additive (attr := simp)]
/-
**Function.mulSupport_fun_inv** 是 Mathlib 中的一个定理，位于命名空间 `Function`。
形式化陈述：mulSupport_fun_inv : (mulSupport fun x => (f x)⁻¹) = mulSupport f
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `inv_ne_one`：inv_ne_one : a⁻¹ != 1 ↔ a != 1
-/
theorem mulSupport_fun_inv : (mulSupport fun x => (f x)⁻¹) = mulSupport f :=
  ext fun _ => inv_ne_one

@[to_additive (attr := simp)]
/-
**Function.mulSupport_inv** 是 Mathlib 中的一个定理，位于命名空间 `Function`。
形式化陈述：mulSupport_inv : mulSupport f⁻¹ = mulSupport f
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.mulSupport_fun_inv`：mulSupport_fun_inv : (mulSupport fun x => (
f x)⁻¹) = mulSupport f
-/
theorem mulSupport_inv : mulSupport f⁻¹ = mulSupport f :=
  mulSupport_fun_inv f

@[to_additive]
/-
**Function.mulSupport_mul_inv** 是 Mathlib 中的一个定理，位于命名空间 `Function`。
形式化陈述：mulSupport_mul_inv : (mulSupport fun x => f x * (g x)⁻¹) subseteq mulSuppo
rt f union mulSupport g
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Function.mulSupport_binop_subset`：mulSupport_binop_subset (op : M -> N -
> P) (op1 : op 1 1 = 1) (f : ι -> M) (g : ι -> N) : mulSupport (fun x => op (f x
) (g x)) subseteq mulS…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `inv_one`：inv_one : (1 : G)⁻¹ = 1
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem mulSupport_mul_inv : (mulSupport fun x => f x * (g x)⁻¹) ⊆ mulSupport f ∪ mulSupport g :=
  mulSupport_binop_subset (fun a b => a * b⁻¹) (by simp) f g

@[to_additive]
/-
**Function.mulSupport_div** 是 Mathlib 中的一个定理，位于命名空间 `Function`。
形式化陈述：mulSupport_div : (mulSupport fun x => f x / g x) subseteq mulSupport f uni
on mulSupport g
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Function.mulSupport_binop_subset`：mulSupport_binop_subset (op : M -> N -
> P) (op1 : op 1 1 = 1) (f : ι -> M) (g : ι -> N) : mulSupport (fun x => op (f x
) (g x)) subseteq mulS…
· 使用定理 `one_div_one`：one_div_one : (1 : G) / 1 = 1
-/
theorem mulSupport_div : (mulSupport fun x => f x / g x) ⊆ mulSupport f ∪ mulSupport g :=
  mulSupport_binop_subset (· / ·) one_div_one f g

end DivisionMonoid

end Function

