/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl
-/
module

public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Data.Finset.Prod
public import Mathlib.Data.Finset.Sum

/-!
# Big operators

In this file we prove theorems about products and sums indexed by a `Finset`.
-/

public section

assert_not_exists AddCommMonoidWithOne
assert_not_exists MonoidWithZero MulAction IsOrderedMonoid
assert_not_exists Finset.preimage Finset.sigma Fintype.piFinset
assert_not_exists Finset.piecewise Set.indicator MonoidHom.coeFn Function.support IsSquare

open Fin Function

variable {ι κ G M : Type*} {s s₁ s₂ : Finset ι} {a : ι}

namespace Finset

section CommMonoid
variable [CommMonoid M] {f g : ι → M}

@[to_additive]
/-
**Finset.prod_eq_fold** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
形式化陈述：prod_eq_fold (s : Finset ι) (f : ι -> M) : ∏ i in s, f i = s.fold (β
参数：s : Finset ι；f : ι -> M。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma prod_eq_fold (s : Finset ι) (f : ι → M) : ∏ i ∈ s, f i = s.fold (β := M) (· * ·) 1 f := rfl

@[to_additive (attr := simp)]
/-
**Finset.prod_cons** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：prod_cons (h : a ∉ s) : ∏ x in cons a s h, f x = f a * ∏ x in s, f x
参数：h : a ∉ s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.fold_cons`：fold_cons (h : a ∉ s) : (cons a s h).fold op b f = f a
 * s.fold op b f
· 使用定理 `IsMulCommutative.is_comm`：∀ {M : Type u_2} {inst : Mul M} [self : IsMulC
ommutative M], Std.Commutative fun x1 x2 => x1 * x2
-/
theorem prod_cons (h : a ∉ s) : ∏ x ∈ cons a s h, f x = f a * ∏ x ∈ s, f x :=
  fold_cons h

/-- Variant of `prod_cons` not applied to a function. -/
@[to_additive (attr := grind =)]
/-
**Finset.prod_cons'** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：prod_cons' (h : a ∉ s) : Finset.prod (cons a s h) = fun (f : ι -> M) => f 
a * ∏ x in s, f x
参数：h : a ∉ s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.prod_cons`：prod_cons (h : a ∉ s) : ∏ x in cons a s h, f x = f a *
 ∏ x in s, f x

--- 原说明 ---
Variant of `prod_cons` not applied to a function.
-/
theorem prod_cons' (h : a ∉ s) :
    Finset.prod (cons a s h) = fun (f : ι → M) => f a * ∏ x ∈ s, f x := by
  funext f
  rw [Finset.prod_cons h]

@[to_additive (attr := simp)]
/-
**Finset.prod_insert** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：prod_insert [DecidableEq ι] : a ∉ s -> ∏ x in insert a s, f x = f a * ∏ x 
in s, f x
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.fold_insert`：fold_insert [DecidableEq α] (h : a ∉ s) : (insert a 
s).fold op b f = f a * s.fold op b f
· 使用定理 `IsMulCommutative.is_comm`：∀ {M : Type u_2} {inst : Mul M} [self : IsMulC
ommutative M], Std.Commutative fun x1 x2 => x1 * x2
-/
theorem prod_insert [DecidableEq ι] : a ∉ s → ∏ x ∈ insert a s, f x = f a * ∏ x ∈ s, f x :=
  fold_insert

/-- Variant of `prod_insert` not applied to a function. -/
@[to_additive (attr := grind =)]
/-
**Finset.prod_insert'** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：prod_insert' [DecidableEq ι] (h : a ∉ s) : Finset.prod (insert a s) = fun 
(f : ι -> M) => f a * ∏ x in s, f x
参数：h : a ∉ s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.prod_insert`：prod_insert [DecidableEq ι] : a ∉ s -> ∏ x in insert
 a s, f x = f a * ∏ x in s, f x

--- 原说明 ---
Variant of `prod_insert` not applied to a function.
-/
theorem prod_insert' [DecidableEq ι] (h : a ∉ s) :
    Finset.prod (insert a s) = fun (f : ι → M) => f a * ∏ x ∈ s, f x := by
  funext f
  rw [Finset.prod_insert h]

/-- The product of `f` over `insert a s` is the same as
the product over `s`, as long as `a` is in `s` or `f a = 1`. -/
@[to_additive (attr := simp) /-- The sum of `f` over `insert a s` is the same as
the sum over `s`, as long as `a` is in `s` or `f a = 0`. -/]
/-
**Finset.prod_insert_of_eq_one_if_notMem** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：prod_insert_of_eq_one_if_notMem [DecidableEq ι] (h : a ∉ s -> f a = 1) : ∏
 x in insert a s, f x = ∏ x in s, f x
参数：h : a ∉ s -> f a = 1。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem prod_insert_of_eq_one_if_notMem [DecidableEq ι] (h : a ∉ s → f a = 1) :
    ∏ x ∈ insert a s, f x = ∏ x ∈ s, f x := by
  by_cases a ∈ s <;> grind

/-- The product of `f` over `insert a s` is the same as
the product over `s`, as long as `f a = 1`. -/
@[to_additive /-- The sum of `f` over `insert a s` is the same as
the sum over `s`, as long as `f a = 0`. -/]
/-
**Finset.prod_insert_one** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：prod_insert_one [DecidableEq ι] (h : f a = 1) : ∏ x in insert a s, f x = ∏
 x in s, f x
参数：h : f a = 1。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.prod_insert_of_eq_one_if_notMem`：prod_insert_of_eq_one_if_notMem 
[DecidableEq ι] (h : a ∉ s -> f a = 1) : ∏ x in insert a s, f x = ∏ x in s, f x
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
theorem prod_insert_one [DecidableEq ι] (h : f a = 1) : ∏ x ∈ insert a s, f x = ∏ x ∈ s, f x := by
  simp [h]

@[to_additive (attr := simp)]
/-
**Finset.prod_singleton** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：prod_singleton (f : ι -> M) (a : ι) : ∏ x in singleton a, f x = f a
参数：f : ι -> M；a : ι。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Finset.fold_singleton`：fold_singleton : ({a} : Finset α).fold op b f = f
 a * b
· 使用定理 `IsMulCommutative.is_comm`：∀ {M : Type u_2} {inst : Mul M} [self : IsMulC
ommutative M], Std.Commutative fun x1 x2 => x1 * x2
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
-/
theorem prod_singleton (f : ι → M) (a : ι) : ∏ x ∈ singleton a, f x = f a :=
  Eq.trans fold_singleton <| mul_one _

/-- Variant of `prod_singleton` not applied to a function. -/
@[to_additive (attr := grind =)]
/-
**Finset.prod_singleton'** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：prod_singleton' (a : ι) : Finset.prod (singleton a) = fun (f : ι -> M) => 
f a
参数：a : ι。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.prod_singleton`：prod_singleton (f : ι -> M) (a : ι) : ∏ x in sing
leton a, f x = f a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
Variant of `prod_singleton` not applied to a function.
-/
theorem prod_singleton' (a : ι) :
    Finset.prod (singleton a) = fun (f : ι → M) => f a := by
  funext f
  simp

@[to_additive]
/-
**Finset.prod_pair** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：prod_pair [DecidableEq ι] {a b : ι} (h : a != b) : (∏ x in ({a, b} : Finse
t ι), f x) = f a * f b
参数：h : a != b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.prod_insert`：prod_insert [DecidableEq ι] : a ∉ s -> ∏ x in insert
 a s, f x = f a * ∏ x in s, f x
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Finset.notMem_singleton`：notMem_singleton {a b : α} : a ∉ ({b} : Finset 
α) ↔ a != b
· 使用定理 `Finset.prod_singleton`：prod_singleton (f : ι -> M) (a : ι) : ∏ x in sing
leton a, f x = f a
-/
theorem prod_pair [DecidableEq ι] {a b : ι} (h : a ≠ b) :
    (∏ x ∈ ({a, b} : Finset ι), f x) = f a * f b := by
  rw [prod_insert (notMem_singleton.2 h), prod_singleton]

/-- If a function is injective on a finset, products over the original finset or its image coincide.
See also `prod_image_of_pairwise_eq_one` for a version with weaker assumptions. -/
@[to_additive (attr := simp) /-- If a function is injective on a finset, sums over the original
finset or its image coincide.
See also `sum_image_of_pairwise_eq_zero` for a version with weaker assumptions. -/]
/-
**Finset.prod_image** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：prod_image [DecidableEq ι] {s : Finset κ} {g : κ -> ι} : Set.InjOn g s -> 
∏ x in s.image g, f x = ∏ x in s, f (g x)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.fold_image`：fold_image [DecidableEq α] {g : γ -> α} {s : Finset γ
} (H : Set.InjOn g s) : (s.image g).fold op b f = s.fold op b (f ∘ g)
· 使用定理 `IsMulCommutative.is_comm`：∀ {M : Type u_2} {inst : Mul M} [self : IsMulC
ommutative M], Std.Commutative fun x1 x2 => x1 * x2
-/
theorem prod_image [DecidableEq ι] {s : Finset κ} {g : κ → ι} :
    Set.InjOn g s → ∏ x ∈ s.image g, f x = ∏ x ∈ s, f (g x) :=
  fold_image

@[to_additive]
/-
**Finset.prod_attach** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
形式化陈述：prod_attach (s : Finset ι) (f : ι -> M) : ∏ x in s.attach, f x = ∏ x in s,
 f x
参数：s : Finset ι；f : ι -> M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.prod_image`：prod_image [DecidableEq ι] {s : Finset κ} {g : κ -> ι
} : Set.InjOn g s -> ∏ x in s.image g, f x = ∏ x in s, f (g x)
· 使用定理 `Function.Injective.injOn`：∀ {α : Type u_1} {β : Type u_2} {f : α → β}, F
unction.Injective f → ∀ {s : Set α}, Set.InjOn f s
· 使用定理 `Subtype.coe_injective`：coe_injective : Injective (fun (a : Subtype p) =>
 (a : α))
· 使用定理 `Finset.attach_image_val`：attach_image_val [DecidableEq α] {s : Finset α}
 : s.attach.image Subtype.val = s
-/
lemma prod_attach (s : Finset ι) (f : ι → M) : ∏ x ∈ s.attach, f x = ∏ x ∈ s, f x := by
  classical rw [← prod_image Subtype.coe_injective.injOn, attach_image_val]

@[to_additive (attr := congr)]
/-
**Finset.prod_congr** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：prod_congr (h : s₁ = s₂) : (forall x in s₂, f x = g x) -> s₁.prod f = s₂.p
rod g
参数：h : s₁ = s₂。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.fold_congr`：fold_congr {g : α -> β} (H : forall x in s, f x = g x
) : s.fold op b f = s.fold op b g
· 使用定理 `IsMulCommutative.is_comm`：∀ {M : Type u_2} {inst : Mul M} [self : IsMulC
ommutative M], Std.Commutative fun x1 x2 => x1 * x2
-/
theorem prod_congr (h : s₁ = s₂) : (∀ x ∈ s₂, f x = g x) → s₁.prod f = s₂.prod g := by
  rw [h]; exact fold_congr

@[to_additive]
/-
**Finset.prod_eq_one** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：prod_eq_one (h : forall x in s, f x = 1) : ∏ x in s, f x = 1
参数：h : forall x in s, f x = 1。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.prod_congr`：prod_congr (h : s₁ = s₂) : (forall x in s₂, f x = g x
) -> s₁.prod f = s₂.prod g
· 使用定理 `Finset.prod_const_one`：prod_const_one : (∏ _x in s, (1 : M)) = 1
-/
theorem prod_eq_one (h : ∀ x ∈ s, f x = 1) : ∏ x ∈ s, f x = 1 := calc
  ∏ x ∈ s, f x = ∏ _x ∈ s, 1 := prod_congr rfl h
  _ = 1 := prod_const_one

/-- In a monoid whose only unit is `1`, a product is equal to `1` iff all factors are `1`. -/
@[to_additive (attr := simp)
/-- In an additive monoid whose only unit is `0`, a sum is equal to `0` iff all terms are `0`. -/]
/-
**Finset.prod_eq_one_iff** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
形式化陈述：prod_eq_one_iff [Subsingleton Mˣ] : ∏ i in s, f i = 1 ↔ forall i in s, f i
 = 1
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.cons_induction`：∀ {α : Type u_3} {motive : Finset α → Prop},   mo
tive ∅ → (∀ (a : α) (s : Finset α) (h : a ∉ s), motive s → motive (Finset.cons a
 s h)) → ∀ …
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `instIsEmptyFalse`：IsEmpty False
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Finset.prod_cons`：prod_cons (h : a ∉ s) : ∏ x in cons a s h, f x = f a *
 ∏ x in s, f x
-/
lemma prod_eq_one_iff [Subsingleton Mˣ] : ∏ i ∈ s, f i = 1 ↔ ∀ i ∈ s, f i = 1 := by
  induction s using Finset.cons_induction <;> simp [*]

@[to_additive]
/-
**Finset.prod_disjUnion** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：prod_disjUnion (h) : ∏ x in s₁.disjUnion s₂ h, f x = (∏ x in s₁, f x) * ∏ 
x in s₂, f x
参数：h。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `IsMulCommutative.is_comm`：∀ {M : Type u_2} {inst : Mul M} [self : IsMulC
ommutative M], Std.Commutative fun x1 x2 => x1 * x2
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `Finset.fold_disjUnion`：fold_disjUnion {s₁ s₂ : Finset α} {b₁ b₂ : β} (h)
 : (s₁.disjUnion s₂ h).fold op (b₁ * b₂) f = s₁.fold op b₁ f * s₂.fold op b₂ f
-/
theorem prod_disjUnion (h) :
    ∏ x ∈ s₁.disjUnion s₂ h, f x = (∏ x ∈ s₁, f x) * ∏ x ∈ s₂, f x := by
  refine Eq.trans ?_ (fold_disjUnion h)
  rw [one_mul]
  rfl

@[to_additive]
/-
**Finset.prod_disjiUnion** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：prod_disjiUnion (s : Finset κ) (t : κ -> Finset ι) (h) : ∏ x in s.disjiUni
on t h, f x = ∏ i in s, ∏ x in t i, f x
参数：s : Finset κ；t : κ -> Finset ι；h。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `IsMulCommutative.is_comm`：∀ {M : Type u_2} {inst : Mul M} [self : IsMulC
ommutative M], Std.Commutative fun x1 x2 => x1 * x2
· 使用定理 `instLeftCommutativeOfCommutativeOfAssociative`：∀ {α : Sort u} {f : α → α
 → α} [hc : Std.Commutative f] [ha : Std.Associative f], LeftCommutative f
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.prod_const_one`：prod_const_one : (∏ _x in s, (1 : M)) = 1
· 使用定理 `Finset.fold_disjiUnion`：fold_disjiUnion {ι : Type*} {s : Finset ι} {t : 
ι -> Finset α} {b : ι -> β} {b₀ : β} (h) : (s.disjiUnion t h).fold op (s.fold op
 b₀ b) f = s…
-/
theorem prod_disjiUnion (s : Finset κ) (t : κ → Finset ι) (h) :
    ∏ x ∈ s.disjiUnion t h, f x = ∏ i ∈ s, ∏ x ∈ t i, f x := by
  refine Eq.trans ?_ (fold_disjiUnion h)
  dsimp [Finset.prod, Multiset.prod, Multiset.fold, Finset.disjUnion, Finset.fold]
  congr
  exact prod_const_one.symm

@[to_additive]
/-
**Finset.prod_union_inter** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：prod_union_inter [DecidableEq ι] : (∏ x in s₁ union s₂, f x) * ∏ x in s₁ i
nter s₂, f x = (∏ x in s₁, f x) * ∏ x in s₂, f x
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.fold_union_inter`：fold_union_inter [DecidableEq α] {s₁ s₂ : Finse
t α} {b₁ b₂ : β} : ((s₁ union s₂).fold op b₁ f * (s₁ inter s₂).fold op b₂ f) = s
₁.fold op b₂ …
· 使用定理 `IsMulCommutative.is_comm`：∀ {M : Type u_2} {inst : Mul M} [self : IsMulC
ommutative M], Std.Commutative fun x1 x2 => x1 * x2
-/
theorem prod_union_inter [DecidableEq ι] :
    (∏ x ∈ s₁ ∪ s₂, f x) * ∏ x ∈ s₁ ∩ s₂, f x = (∏ x ∈ s₁, f x) * ∏ x ∈ s₂, f x :=
  fold_union_inter

@[to_additive]
/-
**Finset.prod_union** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：prod_union [DecidableEq ι] (h : Disjoint s₁ s₂) : ∏ x in s₁ union s₂, f x 
= (∏ x in s₁, f x) * ∏ x in s₂, f x
参数：h : Disjoint s₁ s₂。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.prod_union_inter`：prod_union_inter [DecidableEq ι] : (∏ x in s₁ u
nion s₂, f x) * ∏ x in s₁ inter s₂, f x = (∏ x in s₁, f x) * ∏ x in s₂, f x
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Finset.disjoint_iff_inter_eq_empty`：disjoint_iff_inter_eq_empty : Disjoi
nt s t ↔ s inter t = ∅
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
-/
theorem prod_union [DecidableEq ι] (h : Disjoint s₁ s₂) :
    ∏ x ∈ s₁ ∪ s₂, f x = (∏ x ∈ s₁, f x) * ∏ x ∈ s₂, f x := by
  rw [← prod_union_inter, disjoint_iff_inter_eq_empty.mp h]; exact (mul_one _).symm

@[to_additive]
/-
**Finset.prod_filter_mul_prod_filter_not** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：prod_filter_mul_prod_filter_not (s : Finset ι) (p : ι -> Prop) [DecidableP
red p] [forall x, Decidable (¬p x)] (f : ι -> M) : (∏ x in s with p x, f x) * ∏ 
x in s with ¬p x, f x = ∏ x in s, f x
参数：s : Finset ι；p : ι -> Prop；¬p x；f : ι -> M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.prod_union`：prod_union [DecidableEq ι] (h : Disjoint s₁ s₂) : ∏ x
 in s₁ union s₂, f x = (∏ x in s₁, f x) * ∏ x in s₂, f x
· 使用定理 `Finset.disjoint_filter_filter_not`：disjoint_filter_filter_not (s t : Fin
set α) (p : α -> Prop) [DecidablePred p] [forall x, Decidable (¬p x)] : Disjoint
 (s.filter p) (t.filter…
· 使用定理 `Finset.filter_union_filter_not_eq`：filter_union_filter_not_eq [forall x,
 Decidable (¬p x)] (s : Finset α) : (s.filter p union s.filter fun a => ¬p a) = 
s
-/
theorem prod_filter_mul_prod_filter_not
    (s : Finset ι) (p : ι → Prop) [DecidablePred p] [∀ x, Decidable (¬p x)] (f : ι → M) :
    (∏ x ∈ s with p x, f x) * ∏ x ∈ s with ¬p x, f x = ∏ x ∈ s, f x := by
  have := Classical.decEq ι
  rw [← prod_union (disjoint_filter_filter_not s s p), filter_union_filter_not_eq]

@[to_additive]
/-
**Finset.prod_filter_not_mul_prod_filter** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
形式化陈述：prod_filter_not_mul_prod_filter (s : Finset ι) (p : ι -> Prop) [DecidableP
red p] [forall x, Decidable (¬p x)] (f : ι -> M) : (∏ x in s with ¬p x, f x) * ∏
 x in s with p x, f x = ∏ x in s, f x
参数：s : Finset ι；p : ι -> Prop；¬p x；f : ι -> M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `Finset.prod_filter_mul_prod_filter_not`：prod_filter_mul_prod_filter_not 
(s : Finset ι) (p : ι -> Prop) [DecidablePred p] [forall x, Decidable (¬p x)] (f
 : ι -> M) : (∏ x in s with …
-/
lemma prod_filter_not_mul_prod_filter (s : Finset ι) (p : ι → Prop) [DecidablePred p]
    [∀ x, Decidable (¬p x)] (f : ι → M) :
    (∏ x ∈ s with ¬p x, f x) * ∏ x ∈ s with p x, f x = ∏ x ∈ s, f x := by
  rw [mul_comm, prod_filter_mul_prod_filter_not]

set_option backward.isDefEq.respectTransparency.types false in
@[to_additive]
/-
**Finset.prod_filter_xor** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：prod_filter_xor (p q : ι -> Prop) [DecidablePred p] [DecidablePred q] : (∏
 x in s with (Xor (p x) (q x)), f x) = (∏ x in s with (p x ∧ ¬ q x), f x) * (∏ x
 in s with (q x ∧ ¬ p x), f x)
参数：p q : ι -> Prop。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.prod_union`：prod_union [DecidableEq ι] (h : Disjoint s₁ s₂) : ∏ x
 in s₁ union s₂, f x = (∏ x in s₁, f x) * ∏ x in s₂, f x
· 使用定理 `Finset.disjoint_filter_and_not_filter`：∀ {α : Type u_1} (p q : α → Prop)
 [inst : DecidablePred p] [inst_1 : DecidablePred q] {s : Finset α},   Disjoint 
({x ∈ s | p x ∧ ¬q x}) ({x …
· 使用定理 `Finset.filter_or`：filter_or (s : Finset α) : (s.filter fun a => p a ∨ q 
a) = s.filter p union s.filter q
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Finset.prod_congr`：prod_congr (h : s₁ = s₂) : (forall x in s₂, f x = g x
) -> s₁.prod f = s₂.prod g
· 使用定理 `Finset.filter_congr`：∀ {α : Type u_1} {p q : α → Prop} [inst : Decidable
Pred p] [inst_1 : DecidablePred q] {s : Finset α},   (∀ x ∈ s, p x ↔ q x) → Fins
et.filter…
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem prod_filter_xor (p q : ι → Prop) [DecidablePred p] [DecidablePred q] :
    (∏ x ∈ s with (Xor (p x) (q x)), f x) =
      (∏ x ∈ s with (p x ∧ ¬ q x), f x) * (∏ x ∈ s with (q x ∧ ¬ p x), f x) := by
  classical rw [← prod_union (disjoint_filter_and_not_filter _ _), ← filter_or]
  simp only [Xor]

@[to_additive]
/-
**Finset._root_.IsCompl.prod_mul_prod** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.IsCompl.prod_mul_prod [Fintype ι] {s t : Finset ι} (h : IsCompl s t) (f : ι → M) :
    (∏ i ∈ s, f i) * ∏ i ∈ t, f i = ∏ i, f i :=
  (Finset.prod_disjUnion h.disjoint).symm.trans <| by
    classical rw [Finset.disjUnion_eq_union, ← Finset.sup_eq_union, h.sup_eq_top]; rfl

/-- Multiplying the products of a function over `s` and over `sᶜ` gives the whole product.
For a version expressed with subtypes, see `Fintype.prod_subtype_mul_prod_subtype`. -/
@[to_additive /-- Adding the sums of a function over `s` and over `sᶜ` gives the whole sum.
For a version expressed with subtypes, see `Fintype.sum_subtype_add_sum_subtype`. -/]
/-
**Finset.prod_mul_prod_compl** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
形式化陈述：prod_mul_prod_compl [Fintype ι] [DecidableEq ι] (s : Finset ι) (f : ι -> M
) : (∏ i in s, f i) * ∏ i in sᶜ, f i = ∏ i, f i
参数：s : Finset ι；f : ι -> M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsCompl.prod_mul_prod`：∀ {ι : Type u_1} {M : Type u_4} [inst : CommMonoi
d M] [inst_1 : Fintype ι] {s t : Finset ι},   IsCompl s t → ∀ (f : ι → M), (∏ i 
∈ s, f i) *…
· 使用定理 `isCompl_compl`：isCompl_compl : IsCompl x xᶜ
-/
lemma prod_mul_prod_compl [Fintype ι] [DecidableEq ι] (s : Finset ι) (f : ι → M) :
    (∏ i ∈ s, f i) * ∏ i ∈ sᶜ, f i = ∏ i, f i :=
  IsCompl.prod_mul_prod isCompl_compl f

@[to_additive]
/-
**Finset.prod_compl_mul_prod** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
形式化陈述：prod_compl_mul_prod [Fintype ι] [DecidableEq ι] (s : Finset ι) (f : ι -> M
) : (∏ i in sᶜ, f i) * ∏ i in s, f i = ∏ i, f i
参数：s : Finset ι；f : ι -> M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsCompl.prod_mul_prod`：∀ {ι : Type u_1} {M : Type u_4} [inst : CommMonoi
d M] [inst_1 : Fintype ι] {s t : Finset ι},   IsCompl s t → ∀ (f : ι → M), (∏ i 
∈ s, f i) *…
· 使用定理 `IsCompl.symm`：∀ {α : Type u_1} [inst : PartialOrder α] [inst_1 : Bounded
Order α] {x y : α}, IsCompl x y → IsCompl y x
· 使用定理 `isCompl_compl`：isCompl_compl : IsCompl x xᶜ
-/
lemma prod_compl_mul_prod [Fintype ι] [DecidableEq ι] (s : Finset ι) (f : ι → M) :
    (∏ i ∈ sᶜ, f i) * ∏ i ∈ s, f i = ∏ i, f i :=
  (@isCompl_compl _ s _).symm.prod_mul_prod f

@[to_additive]
/-
**Finset.prod_sdiff** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：prod_sdiff [DecidableEq ι] (h : s₁ subseteq s₂) : (∏ x in s₂ \ s₁, f x) * 
∏ x in s₁, f x = ∏ x in s₂, f x
参数：h : s₁ subseteq s₂。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.prod_union`：prod_union [DecidableEq ι] (h : Disjoint s₁ s₂) : ∏ x
 in s₁ union s₂, f x = (∏ x in s₁, f x) * ∏ x in s₂, f x
· 使用定理 `Finset.sdiff_disjoint`：sdiff_disjoint : Disjoint (t \ s) s
· 使用定理 `Finset.sdiff_union_of_subset`：sdiff_union_of_subset {s₁ s₂ : Finset α} (
h : s₁ subseteq s₂) : s₂ \ s₁ union s₁ = s₂
-/
theorem prod_sdiff [DecidableEq ι] (h : s₁ ⊆ s₂) :
    (∏ x ∈ s₂ \ s₁, f x) * ∏ x ∈ s₁, f x = ∏ x ∈ s₂, f x := by
  rw [← prod_union sdiff_disjoint, sdiff_union_of_subset h]

@[to_additive]
/-
**Finset.prod_subset_one_on_sdiff** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：prod_subset_one_on_sdiff [DecidableEq ι] (h : s₁ subseteq s₂) (hg : forall
 x in s₂ \ s₁, g x = 1) (hfg : forall x in s₁, f x = g x) : ∏ i in s₁, f i = ∏ i
 in s₂, g i
参数：h : s₁ subseteq s₂；hg : forall x in s₂ \ s₁, g x = 1；hfg : forall x in s₁, f 
x = g x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.prod_sdiff`：prod_sdiff [DecidableEq ι] (h : s₁ subseteq s₂) : (∏ 
x in s₂ \ s₁, f x) * ∏ x in s₁, f x = ∏ x in s₂, f x
· 使用定理 `Finset.prod_eq_one`：prod_eq_one (h : forall x in s, f x = 1) : ∏ x in s,
 f x = 1
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `Finset.prod_congr`：prod_congr (h : s₁ = s₂) : (forall x in s₂, f x = g x
) -> s₁.prod f = s₂.prod g
-/
theorem prod_subset_one_on_sdiff [DecidableEq ι] (h : s₁ ⊆ s₂) (hg : ∀ x ∈ s₂ \ s₁, g x = 1)
    (hfg : ∀ x ∈ s₁, f x = g x) : ∏ i ∈ s₁, f i = ∏ i ∈ s₂, g i := by
  rw [← prod_sdiff h, prod_eq_one hg, one_mul]
  exact prod_congr rfl hfg

@[to_additive]
/-
**Finset.prod_subset** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：prod_subset (h : s₁ subseteq s₂) (hf : forall x in s₂, x ∉ s₁ -> f x = 1) 
: ∏ x in s₁, f x = ∏ x in s₂, f x
参数：h : s₁ subseteq s₂；hf : forall x in s₂, x ∉ s₁ -> f x = 1。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.prod_subset_one_on_sdiff`：prod_subset_one_on_sdiff [DecidableEq ι
] (h : s₁ subseteq s₂) (hg : forall x in s₂ \ s₁, g x = 1) (hfg : forall x in s₁
, f x = g x) : ∏ i in…
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
-/
theorem prod_subset (h : s₁ ⊆ s₂) (hf : ∀ x ∈ s₂, x ∉ s₁ → f x = 1) :
    ∏ x ∈ s₁, f x = ∏ x ∈ s₂, f x :=
  haveI := Classical.decEq ι
  prod_subset_one_on_sdiff h (by simpa) fun _ _ => rfl

@[to_additive (attr := simp)]
/-
**Finset.prod_disjSum** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：prod_disjSum (s : Finset ι) (t : Finset κ) (f : ι oplus κ -> M) : ∏ x in s
.disjSum t, f x = (∏ x in s, f (Sum.inl x)) * ∏ x in t, f (Sum.inr x)
参数：s : Finset ι；t : Finset κ；f : ι oplus κ -> M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.disjoint_map_inl_map_inr`：disjoint_map_inl_map_inr : Disjoint (s.
map Embedding.inl) (t.map Embedding.inr)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.map_inl_disjUnion_map_inr`：map_inl_disjUnion_map_inr : (s.map Emb
edding.inl).disjUnion (t.map Embedding.inr) (disjoint_map_inl_map_inr _ _) = s.d
isjSum t
· 使用定理 `Finset.prod_disjUnion`：prod_disjUnion (h) : ∏ x in s₁.disjUnion s₂ h, f 
x = (∏ x in s₁, f x) * ∏ x in s₂, f x
· 使用定理 `Finset.prod_map`：prod_map (s : Finset ι) (e : ι ↪ κ) (f : κ -> M) : ∏ x 
in s.map e, f x = ∏ x in s, f (e x)
-/
theorem prod_disjSum (s : Finset ι) (t : Finset κ) (f : ι ⊕ κ → M) :
    ∏ x ∈ s.disjSum t, f x = (∏ x ∈ s, f (Sum.inl x)) * ∏ x ∈ t, f (Sum.inr x) := by
  rw [← map_inl_disjUnion_map_inr, prod_disjUnion, prod_map, prod_map]
  rfl

@[to_additive]
/-
**Finset.prod_sum_eq_prod_toLeft_mul_prod_toRight** 是 Mathlib 中的一个引理，位于命名空间 `Fin
set`。
形式化陈述：prod_sum_eq_prod_toLeft_mul_prod_toRight (s : Finset (ι oplus κ)) (f : ι o
plus κ -> M) : ∏ x in s, f x = (∏ x in s.toLeft, f (Sum.inl x)) * ∏ x in s.toRig
ht, f (Sum.inr x)
参数：s : Finset (ι oplus κ)；f : ι oplus κ -> M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `Finset.toLeft_disjSum_toRight`：toLeft_disjSum_toRight : u.toLeft.disjSum
 u.toRight = u
· 使用定理 `Finset.prod_disjSum`：prod_disjSum (s : Finset ι) (t : Finset κ) (f : ι o
plus κ -> M) : ∏ x in s.disjSum t, f x = (∏ x in s, f (Sum.inl x)) * ∏ x in t, f
 (Sum.inr…
· 使用定理 `Finset.toLeft_disjSum`：∀ {α : Type u_1} {β : Type u_2} {s : Finset α} {t
 : Finset β}, (s.disjSum t).toLeft = s
· 使用定理 `Finset.toRight_disjSum`：∀ {α : Type u_1} {β : Type u_2} {s : Finset α} {
t : Finset β}, (s.disjSum t).toRight = t
-/
lemma prod_sum_eq_prod_toLeft_mul_prod_toRight (s : Finset (ι ⊕ κ)) (f : ι ⊕ κ → M) :
    ∏ x ∈ s, f x = (∏ x ∈ s.toLeft, f (Sum.inl x)) * ∏ x ∈ s.toRight, f (Sum.inr x) := by
  rw [← Finset.toLeft_disjSum_toRight (u := s), Finset.prod_disjSum, Finset.toLeft_disjSum,
    Finset.toRight_disjSum]

@[to_additive]
/-
**Finset.prod_sumElim** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：prod_sumElim (s : Finset ι) (t : Finset κ) (f : ι -> M) (g : κ -> M) : ∏ x
 in s.disjSum t, Sum.elim f g x = (∏ x in s, f x) * ∏ x in t, g x
参数：s : Finset ι；t : Finset κ；f : ι -> M；g : κ -> M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.prod_disjSum`：prod_disjSum (s : Finset ι) (t : Finset κ) (f : ι o
plus κ -> M) : ∏ x in s.disjSum t, f x = (∏ x in s, f (Sum.inl x)) * ∏ x in t, f
 (Sum.inr…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem prod_sumElim (s : Finset ι) (t : Finset κ) (f : ι → M) (g : κ → M) :
    ∏ x ∈ s.disjSum t, Sum.elim f g x = (∏ x ∈ s, f x) * ∏ x ∈ t, g x := by simp

/-- Given a finite family of pairwise disjoint finsets, the product over their union is the product
of the products over the sets.
See also `prod_biUnion_of_pairwise_eq_one` for a version with weaker assumptions. -/
@[to_additive /-- Given a finite family of pairwise disjoint finsets, the sum over their union is
the sum of the sums over the sets.
See also `sum_biUnion_of_pairwise_eq_zero` for a version with weaker assumptions. -/]
/-
**Finset.prod_biUnion** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：prod_biUnion [DecidableEq ι] {s : Finset κ} {t : κ -> Finset ι} (hs : Set.
PairwiseDisjoint (↑s) t) : ∏ x in s.biUnion t, f x = ∏ x in s, ∏ i in t x, f i
参数：hs : Set.PairwiseDisjoint (↑s) t。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `Finset.disjiUnion_eq_biUnion`：disjiUnion_eq_biUnion (s : Finset α) (f : 
α -> Finset β) (hf) : s.disjiUnion f hf = s.biUnion f
· 使用定理 `Finset.prod_disjiUnion`：prod_disjiUnion (s : Finset κ) (t : κ -> Finset 
ι) (h) : ∏ x in s.disjiUnion t h, f x = ∏ i in s, ∏ x in t i, f x
-/
theorem prod_biUnion [DecidableEq ι] {s : Finset κ} {t : κ → Finset ι}
    (hs : Set.PairwiseDisjoint (↑s) t) : ∏ x ∈ s.biUnion t, f x = ∏ x ∈ s, ∏ i ∈ t x, f i := by
  rw [← disjiUnion_eq_biUnion _ _ hs, prod_disjiUnion]

section bij
variable {s : Finset ι} {t : Finset κ} {f : ι → M} {g : κ → M}

@[to_additive]
/-
**Finset.prod_of_injOn** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
形式化陈述：prod_of_injOn (e : ι -> κ) (he : Set.InjOn e s) (hest : Set.MapsTo e s t) 
(h' : forall i in t, i ∉ e '' s -> g i = 1) (h : forall i in s, f i = g (e i)) :
 ∏ i in s, f i = ∏ j in t, g j
参数：e : ι -> κ；he : Set.InjOn e s；hest : Set.MapsTo e s t；h' : forall i in t, i ∉
 e '' s -> g i = 1；h : forall i in s, f i = g (e i)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用引理 `Finset.prod_nbij`：prod_nbij (i : ι -> κ) (hi : forall a in s, i a in t) 
(i_inj : (s : Set ι).InjOn i) (i_surj : (s : Set ι).SurjOn i t) (h : forall a in
 s, f …
· 使用定理 `Finset.mem_image_of_mem`：mem_image_of_mem (f : α -> β) {a} (h : a in s) 
: f a in s.image f
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.coe_image`：coe_image : ↑(s.image f) = f '' ↑s
· 使用定理 `Finset.prod_subset`：prod_subset (h : s₁ subseteq s₂) (hf : forall x in s
₂, x ∉ s₁ -> f x = 1) : ∏ x in s₁, f x = ∏ x in s₂, f x
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Finset.image_subset_iff`：image_subset_iff : s.image f subseteq t ↔ foral
l x in s, f x in t
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
-/
lemma prod_of_injOn (e : ι → κ) (he : Set.InjOn e s) (hest : Set.MapsTo e s t)
    (h' : ∀ i ∈ t, i ∉ e '' s → g i = 1) (h : ∀ i ∈ s, f i = g (e i)) :
    ∏ i ∈ s, f i = ∏ j ∈ t, g j := by
  classical
  exact (prod_nbij e (fun a ↦ mem_image_of_mem e) he (by simp [Set.surjOn_image]) h).trans <|
    prod_subset (image_subset_iff.2 hest) <| by simpa using h'

variable [DecidableEq κ]

@[to_additive]
/-
**Finset.prod_fiberwise_eq_prod_filter** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
形式化陈述：prod_fiberwise_eq_prod_filter (s : Finset ι) (t : Finset κ) (g : ι -> κ) (
f : ι -> M) : ∏ j in t, ∏ i in s with g i = j, f i = ∏ i in s with g i in t, f i
参数：s : Finset ι；t : Finset κ；g : ι -> κ；f : ι -> M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.prod_disjiUnion`：prod_disjiUnion (s : Finset κ) (t : κ -> Finset 
ι) (h) : ∏ x in s.disjiUnion t h, f x = ∏ i in s, ∏ x in t i, f x
· 使用定理 `_private.Mathlib.Data.Finset.Union.0.Finset.pairwiseDisjoint_fibers`：∀ {
α : Type u_1} {β : Type u_2} [inst : DecidableEq β] {s : Finset α} {t : Finset β
} {f : α → β},   (↑t).PairwiseDisjoint fun a => {x ∈ s | …
· 使用定理 `Finset.disjiUnion_filter_eq`：∀ {α : Type u_1} {β : Type u_2} [inst : Dec
idableEq β] (s : Finset α) (t : Finset β) (f : α → β),   t.disjiUnion (fun a => 
{x ∈ s | f x = a}…
-/
lemma prod_fiberwise_eq_prod_filter (s : Finset ι) (t : Finset κ) (g : ι → κ) (f : ι → M) :
    ∏ j ∈ t, ∏ i ∈ s with g i = j, f i = ∏ i ∈ s with g i ∈ t, f i := by
  rw [← prod_disjiUnion, disjiUnion_filter_eq]
  #adaptation_note /-- 2025-09-12 (kmill) copied from private lemma pairwiseDisjoint_fibers -/
  intro x' hx y' hy hne
  simp_rw [disjoint_left, mem_filter]; rintro i ⟨_, rfl⟩ ⟨_, rfl⟩; exact hne rfl

@[to_additive]
/-
**Finset.prod_fiberwise_eq_prod_filter'** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
形式化陈述：prod_fiberwise_eq_prod_filter' (s : Finset ι) (t : Finset κ) (g : ι -> κ) 
(f : κ -> M) : ∏ j in t, ∏ i in s with g i = j, f j = ∏ i in s with g i in t, f 
(g i)
参数：s : Finset ι；t : Finset κ；g : ι -> κ；f : κ -> M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.prod_congr`：prod_congr (h : s₁ = s₂) : (forall x in s₂, f x = g x
) -> s₁.prod f = s₂.prod g
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Finset.mem_filter`：∀ {α : Type u_1} {p : α → Prop} [inst : DecidablePred
 p] {s : Finset α} {a : α}, a ∈ Finset.filter p s ↔ a ∈ s ∧ p a
· 使用引理 `Finset.prod_fiberwise_eq_prod_filter`：prod_fiberwise_eq_prod_filter (s :
 Finset ι) (t : Finset κ) (g : ι -> κ) (f : ι -> M) : ∏ j in t, ∏ i in s with g 
i = j, f i = ∏ i in s with…
-/
lemma prod_fiberwise_eq_prod_filter' (s : Finset ι) (t : Finset κ) (g : ι → κ) (f : κ → M) :
    ∏ j ∈ t, ∏ i ∈ s with g i = j, f j = ∏ i ∈ s with g i ∈ t, f (g i) := by
  calc
    _ = ∏ j ∈ t, ∏ i ∈ s with g i = j, f (g i) :=
        prod_congr rfl fun j _ ↦ prod_congr rfl fun i hi ↦ by rw [(mem_filter.1 hi).2]
    _ = _ := prod_fiberwise_eq_prod_filter _ _ _ _

@[to_additive]
/-
**Finset.prod_fiberwise_of_maps_to** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
形式化陈述：prod_fiberwise_of_maps_to {g : ι -> κ} (h : forall i in s, g i in t) (f : 
ι -> M) : ∏ j in t, ∏ i in s with g i = j, f i = ∏ i in s, f i
参数：h : forall i in s, g i in t；f : ι -> M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.prod_disjiUnion`：prod_disjiUnion (s : Finset κ) (t : κ -> Finset 
ι) (h) : ∏ x in s.disjiUnion t h, f x = ∏ i in s, ∏ x in t i, f x
· 使用定理 `_private.Mathlib.Data.Finset.Union.0.Finset.pairwiseDisjoint_fibers`：∀ {
α : Type u_1} {β : Type u_2} [inst : DecidableEq β] {s : Finset α} {t : Finset β
} {f : α → β},   (↑t).PairwiseDisjoint fun a => {x ∈ s | …
· 使用引理 `Finset.disjiUnion_filter_eq_of_maps_to`：disjiUnion_filter_eq_of_maps_to 
(h : forall x in s, f x in t) : t.disjiUnion (fun a => s.filter (f · = a)) pairw
iseDisjoint_fibers = s
-/
lemma prod_fiberwise_of_maps_to {g : ι → κ} (h : ∀ i ∈ s, g i ∈ t) (f : ι → M) :
    ∏ j ∈ t, ∏ i ∈ s with g i = j, f i = ∏ i ∈ s, f i := by
  rw [← prod_disjiUnion, disjiUnion_filter_eq_of_maps_to h]
  #adaptation_note /-- 2025-09-12 (kmill) copied from private lemma pairwiseDisjoint_fibers -/
  intro x' hx y' hy hne
  simp_rw [disjoint_left, mem_filter]; rintro i ⟨_, rfl⟩ ⟨_, rfl⟩; exact hne rfl

@[to_additive]
/-
**Finset.prod_fiberwise_of_maps_to'** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
形式化陈述：prod_fiberwise_of_maps_to' {g : ι -> κ} (h : forall i in s, g i in t) (f :
 κ -> M) : ∏ j in t, ∏ i in s with g i = j, f j = ∏ i in s, f (g i)
参数：h : forall i in s, g i in t；f : κ -> M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.prod_congr`：prod_congr (h : s₁ = s₂) : (forall x in s₂, f x = g x
) -> s₁.prod f = s₂.prod g
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Finset.mem_filter`：∀ {α : Type u_1} {p : α → Prop} [inst : DecidablePred
 p] {s : Finset α} {a : α}, a ∈ Finset.filter p s ↔ a ∈ s ∧ p a
· 使用引理 `Finset.prod_fiberwise_of_maps_to`：prod_fiberwise_of_maps_to {g : ι -> κ}
 (h : forall i in s, g i in t) (f : ι -> M) : ∏ j in t, ∏ i in s with g i = j, f
 i = ∏ i in s, f i
-/
lemma prod_fiberwise_of_maps_to' {g : ι → κ} (h : ∀ i ∈ s, g i ∈ t) (f : κ → M) :
    ∏ j ∈ t, ∏ i ∈ s with g i = j, f j = ∏ i ∈ s, f (g i) := by
  calc
    _ = ∏ j ∈ t, ∏ i ∈ s with g i = j, f (g i) :=
        prod_congr rfl fun y _ ↦ prod_congr rfl fun x hx ↦ by rw [(mem_filter.1 hx).2]
    _ = _ := prod_fiberwise_of_maps_to h _

variable [Fintype κ]

@[to_additive]
/-
**Finset.prod_fiberwise** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
形式化陈述：prod_fiberwise (s : Finset ι) (g : ι -> κ) (f : ι -> M) : ∏ j, ∏ i in s wi
th g i = j, f i = ∏ i in s, f i
参数：s : Finset ι；g : ι -> κ；f : ι -> M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Finset.prod_fiberwise_of_maps_to`：prod_fiberwise_of_maps_to {g : ι -> κ}
 (h : forall i in s, g i in t) (f : ι -> M) : ∏ j in t, ∏ i in s with g i = j, f
 i = ∏ i in s, f i
· 使用定理 `Finset.mem_univ`：mem_univ (x : α) : x in (univ : Finset α)
-/
lemma prod_fiberwise (s : Finset ι) (g : ι → κ) (f : ι → M) :
    ∏ j, ∏ i ∈ s with g i = j, f i = ∏ i ∈ s, f i :=
  prod_fiberwise_of_maps_to (fun _ _ ↦ mem_univ _) _

@[to_additive]
/-
**Finset.prod_fiberwise'** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
形式化陈述：prod_fiberwise' (s : Finset ι) (g : ι -> κ) (f : κ -> M) : ∏ j, ∏ i in s w
ith g i = j, f j = ∏ i in s, f (g i)
参数：s : Finset ι；g : ι -> κ；f : κ -> M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Finset.prod_fiberwise_of_maps_to'`：prod_fiberwise_of_maps_to' {g : ι -> 
κ} (h : forall i in s, g i in t) (f : κ -> M) : ∏ j in t, ∏ i in s with g i = j,
 f j = ∏ i in s, f (g i…
· 使用定理 `Finset.mem_univ`：mem_univ (x : α) : x in (univ : Finset α)
-/
lemma prod_fiberwise' (s : Finset ι) (g : ι → κ) (f : κ → M) :
    ∏ j, ∏ i ∈ s with g i = j, f j = ∏ i ∈ s, f (g i) :=
  prod_fiberwise_of_maps_to' (fun _ _ ↦ mem_univ _) _

end bij

@[to_additive (attr := simp)]
/-
**Finset.prod_diag** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
形式化陈述：prod_diag (s : Finset ι) (f : ι × ι -> M) : ∏ i in s.diag, f i = ∏ i in s,
 f (i, i)
参数：s : Finset ι；f : ι × ι -> M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.prod_map`：prod_map (s : Finset ι) (e : ι ↪ κ) (f : κ -> M) : ∏ x 
in s.map e, f x = ∏ x in s, f (e x)
· 使用定理 `Function.diag_injective`：diag_injective : Injective (α
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma prod_diag (s : Finset ι) (f : ι × ι → M) :
    ∏ i ∈ s.diag, f i = ∏ i ∈ s, f (i, i) := by
  simp [diag]

@[to_additive]
/-
**Finset.prod_image'** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：prod_image' [DecidableEq ι] {s : Finset κ} {g : κ -> ι} (h : κ -> M) (eq :
 forall i in s, f (g i) = ∏ j in s with g j = g i, h j) : ∏ a in s.image g, f a 
= ∏ i in s, h i
参数：h : κ -> M；eq : forall i in s, f (g i) = ∏ j in s with g j = g i, h j。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.prod_congr`：prod_congr (h : s₁ = s₂) : (forall x in s₂, f x = g x
) -> s₁.prod f = s₂.prod g
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Finset.mem_image`：mem_image : b in s.image f ↔ exists a in s, f a = b
· 使用引理 `Finset.prod_fiberwise_of_maps_to`：prod_fiberwise_of_maps_to {g : ι -> κ}
 (h : forall i in s, g i in t) (f : ι -> M) : ∏ j in t, ∏ i in s with g i = j, f
 i = ∏ i in s, f i
· 使用定理 `Finset.mem_image_of_mem`：mem_image_of_mem (f : α -> β) {a} (h : a in s) 
: f a in s.image f
-/
theorem prod_image' [DecidableEq ι] {s : Finset κ} {g : κ → ι} (h : κ → M)
    (eq : ∀ i ∈ s, f (g i) = ∏ j ∈ s with g j = g i, h j) :
    ∏ a ∈ s.image g, f a = ∏ i ∈ s, h i :=
  calc
    ∏ a ∈ s.image g, f a = ∏ a ∈ s.image g, ∏ j ∈ s with g j = a, h j :=
      (prod_congr rfl) fun _a hx =>
        let ⟨i, his, hi⟩ := mem_image.1 hx
        hi ▸ eq i his
    _ = ∏ i ∈ s, h i := prod_fiberwise_of_maps_to (fun _ => mem_image_of_mem g) _

@[to_additive]
/-
**Finset.prod_mul_distrib** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：prod_mul_distrib : ∏ x in s, f x * g x = (∏ x in s, f x) * ∏ x in s, g x
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `IsMulCommutative.is_comm`：∀ {M : Type u_2} {inst : Mul M} [self : IsMulC
ommutative M], Std.Commutative fun x1 x2 => x1 * x2
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `Finset.fold_op_distrib`：fold_op_distrib {f g : α -> β} {b₁ b₂ : β} : (s.
fold op (b₁ * b₂) fun x => f x * g x) = s.fold op b₁ f * s.fold op b₂ g
-/
theorem prod_mul_distrib : ∏ x ∈ s, f x * g x = (∏ x ∈ s, f x) * ∏ x ∈ s, g x :=
  Eq.trans (by rw [one_mul]; rfl) fold_op_distrib

@[to_additive]
/-
**Finset.prod_mul_prod_comm** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
形式化陈述：prod_mul_prod_comm (f g h i : ι -> M) : (∏ a in s, f a * g a) * ∏ a in s, 
h a * i a = (∏ a in s, f a * h a) * ∏ a in s, g a * i a
参数：f g h i : ι -> M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.prod_mul_distrib`：prod_mul_distrib : ∏ x in s, f x * g x = (∏ x i
n s, f x) * ∏ x in s, g x
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `mul_mul_mul_comm`：mul_mul_mul_comm (a b c d : G) : a * b * (c * d) = a *
 c * (b * d)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma prod_mul_prod_comm (f g h i : ι → M) :
    (∏ a ∈ s, f a * g a) * ∏ a ∈ s, h a * i a = (∏ a ∈ s, f a * h a) * ∏ a ∈ s, g a * i a := by
  simp_rw [prod_mul_distrib, mul_mul_mul_comm]

@[to_additive]
/-
**Finset.prod_filter_of_ne** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：prod_filter_of_ne {p : ι -> Prop} [DecidablePred p] (hp : forall x in s, f
 x != 1 -> p x) : ∏ x in s with p x, f x = ∏ x in s, f x
参数：hp : forall x in s, f x != 1 -> p x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.prod_subset`：prod_subset (h : s₁ subseteq s₂) (hf : forall x in s
₂, x ∉ s₁ -> f x = 1) : ∏ x in s₁, f x = ∏ x in s₂, f x
· 使用定理 `Finset.filter_subset`：∀ {α : Type u_1} (p : α → Prop) [inst : DecidableP
red p] (s : Finset α), Finset.filter p s ⊆ s
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `not_imp_comm`：not_imp_comm : ¬a -> b ↔ ¬b -> a
· 使用定理 `Finset.mem_filter`：∀ {α : Type u_1} {p : α → Prop} [inst : DecidablePred
 p] {s : Finset α} {a : α}, a ∈ Finset.filter p s ↔ a ∈ s ∧ p a
-/
theorem prod_filter_of_ne {p : ι → Prop} [DecidablePred p] (hp : ∀ x ∈ s, f x ≠ 1 → p x) :
    ∏ x ∈ s with p x, f x = ∏ x ∈ s, f x :=
  (prod_subset (filter_subset _ _)) fun x => by
    rw [not_imp_comm, mem_filter]
    exact fun h₁ h₂ => ⟨h₁, by simpa using hp _ h₁ h₂⟩

-- If we use `[DecidableEq M]` here, some rewrites fail because they find a wrong `Decidable`
-- instance first; `{∀ x, Decidable (f x ≠ 1)}` doesn't work with `rw ← prod_filter_ne_one`
@[to_additive]
/-
**Finset.prod_filter_ne_one** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：prod_filter_ne_one (s : Finset ι) [forall x, Decidable (f x != 1)] : ∏ x i
n s with f x != 1, f x = ∏ x in s, f x
参数：s : Finset ι；f x != 1。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.prod_filter_of_ne`：prod_filter_of_ne {p : ι -> Prop} [DecidablePr
ed p] (hp : forall x in s, f x != 1 -> p x) : ∏ x in s with p x, f x = ∏ x in s,
 f x
-/
theorem prod_filter_ne_one (s : Finset ι) [∀ x, Decidable (f x ≠ 1)] :
    ∏ x ∈ s with f x ≠ 1, f x = ∏ x ∈ s, f x :=
  prod_filter_of_ne fun _ _ => id

@[to_additive]
/-
**Finset.prod_filter** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：prod_filter (p : ι -> Prop) [DecidablePred p] (f : ι -> M) : ∏ a in s with
 p a, f a = ∏ a in s, if p a then f a else 1
参数：p : ι -> Prop；f : ι -> M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.prod_congr`：prod_congr (h : s₁ = s₂) : (forall x in s₂, f x = g x
) -> s₁.prod f = s₂.prod g
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Finset.mem_filter`：∀ {α : Type u_1} {p : α → Prop} [inst : DecidablePred
 p] {s : Finset α} {a : α}, a ∈ Finset.filter p s ↔ a ∈ s ∧ p a
· 使用定理 `Finset.prod_subset`：prod_subset (h : s₁ subseteq s₂) (hf : forall x in s
₂, x ∉ s₁ -> f x = 1) : ∏ x in s₁, f x = ∏ x in s₂, f x
· 使用定理 `Finset.filter_subset`：∀ {α : Type u_1} (p : α → Prop) [inst : DecidableP
red p] (s : Finset α), Finset.filter p s ⊆ s
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
· 使用定理 `not_and`：∀ {a b : Prop}, ¬(a ∧ b) ↔ a → ¬b
-/
theorem prod_filter (p : ι → Prop) [DecidablePred p] (f : ι → M) :
    ∏ a ∈ s with p a, f a = ∏ a ∈ s, if p a then f a else 1 :=
  calc
    ∏ a ∈ s with p a, f a = ∏ a ∈ s with p a, if p a then f a else 1 :=
      prod_congr rfl fun a h => by rw [if_pos]; simpa using (mem_filter.1 h).2
    _ = ∏ a ∈ s, if p a then f a else 1 := by
      { refine prod_subset (filter_subset _ s) fun x hs h => ?_
        rw [mem_filter, not_and] at h
        exact if_neg (by simpa using h hs) }

@[to_additive]
/-
**Finset.prod_eq_single_of_mem** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：prod_eq_single_of_mem {s : Finset ι} {f : ι -> M} (a : ι) (h : a in s) (h₀
 : forall b in s, b != a -> f b = 1) : ∏ x in s, f x = f a
参数：a : ι；h : a in s；h₀ : forall b in s, b != a -> f b = 1。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.prod_subset`：prod_subset (h : s₁ subseteq s₂) (hf : forall x in s
₂, x ∉ s₁ -> f x = 1) : ∏ x in s₁, f x = ∏ x in s₂, f x
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Finset.mem_singleton`：mem_singleton {a b : α} : b in ({a} : Finset α) ↔ 
b = a
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Finset.prod_singleton`：prod_singleton (f : ι -> M) (a : ι) : ∏ x in sing
leton a, f x = f a
-/
theorem prod_eq_single_of_mem {s : Finset ι} {f : ι → M} (a : ι) (h : a ∈ s)
    (h₀ : ∀ b ∈ s, b ≠ a → f b = 1) : ∏ x ∈ s, f x = f a := by
  calc
    ∏ x ∈ s, f x = ∏ x ∈ {a}, f x := by
      { refine (prod_subset ?_ ?_).symm
        · intro _ H
          rwa [mem_singleton.1 H]
        · simpa only [mem_singleton] }
    _ = f a := prod_singleton _ _

@[to_additive]
/-
**Finset.prod_eq_single** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：prod_eq_single {s : Finset ι} {f : ι -> M} (a : ι) (h₀ : forall b in s, b 
!= a -> f b = 1) (h₁ : a ∉ s -> f a = 1) : ∏ x in s, f x = f a
参数：a : ι；h₀ : forall b in s, b != a -> f b = 1；h₁ : a ∉ s -> f a = 1。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `by_cases`：by_cases {p q : Prop} (hpq : p -> q) (hnpq : ¬p -> q) : q
· 使用定理 `Finset.prod_eq_single_of_mem`：prod_eq_single_of_mem {s : Finset ι} {f : 
ι -> M} (a : ι) (h : a in s) (h₀ : forall b in s, b != a -> f b = 1) : ∏ x in s,
 f x = f a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Finset.prod_congr`：prod_congr (h : s₁ = s₂) : (forall x in s₂, f x = g x
) -> s₁.prod f = s₂.prod g
· 使用定理 `Finset.prod_const_one`：prod_const_one : (∏ _x in s, (1 : M)) = 1
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem prod_eq_single {s : Finset ι} {f : ι → M} (a : ι) (h₀ : ∀ b ∈ s, b ≠ a → f b = 1)
    (h₁ : a ∉ s → f a = 1) : ∏ x ∈ s, f x = f a :=
  haveI := Classical.decEq ι
  by_cases (prod_eq_single_of_mem a · h₀) fun this =>
    (prod_congr rfl fun b hb => h₀ b hb <| by rintro rfl; exact this hb).trans <|
      prod_const_one.trans (h₁ this).symm

@[to_additive (attr := simp)]
/-
**Finset.prod_ite_mem_eq** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
形式化陈述：prod_ite_mem_eq [Fintype ι] (s : Finset ι) (f : ι -> M) [DecidablePred (· 
in s)] : (∏ i, if i in s then f i else 1) = ∏ i in s, f i
参数：s : Finset ι；f : ι -> M；· in s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.prod_filter`：prod_filter (p : ι -> Prop) [DecidablePred p] (f : ι
 -> M) : ∏ a in s with p a, f a = ∏ a in s, if p a then f a else 1
-/
lemma prod_ite_mem_eq [Fintype ι] (s : Finset ι) (f : ι → M) [DecidablePred (· ∈ s)] :
    (∏ i, if i ∈ s then f i else 1) = ∏ i ∈ s, f i := by
  rw [← Finset.prod_filter]; congr; grind

@[to_additive]
/-
**Finset.prod_eq_ite** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
形式化陈述：prod_eq_ite [DecidableEq ι] {s : Finset ι} {f : ι -> M} (a : ι) (h₀ : fora
ll b in s, b != a -> f b = 1) : ∏ x in s, f x = if a in s then f a else 1
参数：a : ι；h₀ : forall b in s, b != a -> f b = 1。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.prod_eq_single_of_mem`：prod_eq_single_of_mem {s : Finset ι} {f : 
ι -> M} (a : ι) (h : a in s) (h₀ : forall b in s, b != a -> f b = 1) : ∏ x in s,
 f x = f a
· 使用定理 `ite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α),
 c = True → (if c then a else b) = a
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Finset.prod_congr`：prod_congr (h : s₁ = s₂) : (forall x in s₂, f x = g x
) -> s₁.prod f = s₂.prod g
· 使用定理 `Finset.prod_const_one`：prod_const_one : (∏ _x in s, (1 : M)) = 1
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用定理 `ite_self`：∀ {α : Sort u} {c : Prop} {d : Decidable c} (a : α), (if c the
n a else a) = a
-/
lemma prod_eq_ite [DecidableEq ι] {s : Finset ι} {f : ι → M} (a : ι)
    (h₀ : ∀ b ∈ s, b ≠ a → f b = 1) :
    ∏ x ∈ s, f x = if a ∈ s then f a else 1 := by
  by_cases h : a ∈ s
  · simp [Finset.prod_eq_single_of_mem a h h₀, h]
  · replace h₀ : ∀ b ∈ s, f b = 1 := by grind
    simp +contextual [h₀]

@[to_additive]
/-
**Finset.prod_union_eq_left** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
形式化陈述：prod_union_eq_left [DecidableEq ι] (hs : forall a in s₂, a ∉ s₁ -> f a = 1
) : ∏ a in s₁ union s₂, f a = ∏ a in s₁, f a
参数：hs : forall a in s₂, a ∉ s₁ -> f a = 1。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.prod_subset`：prod_subset (h : s₁ subseteq s₂) (hf : forall x in s
₂, x ∉ s₁ -> f x = 1) : ∏ x in s₁, f x = ∏ x in s₂, f x
· 使用定理 `Finset.subset_union_left`：∀ {α : Type u_1} [inst : DecidableEq α] {s₁ s₂
 : Finset α}, s₁ ⊆ s₁ ∪ s₂
· 使用定理 `Or.resolve_left`：∀ {a b : Prop}, a ∨ b → ¬a → b
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Finset.mem_union`：mem_union : a in s union t ↔ a in s ∨ a in t
-/
lemma prod_union_eq_left [DecidableEq ι] (hs : ∀ a ∈ s₂, a ∉ s₁ → f a = 1) :
    ∏ a ∈ s₁ ∪ s₂, f a = ∏ a ∈ s₁, f a :=
  Eq.symm <|
    prod_subset subset_union_left fun _a ha ha' ↦ hs _ ((mem_union.1 ha).resolve_left ha') ha'

@[to_additive]
/-
**Finset.prod_union_eq_right** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
形式化陈述：prod_union_eq_right [DecidableEq ι] (hs : forall a in s₁, a ∉ s₂ -> f a = 
1) : ∏ a in s₁ union s₂, f a = ∏ a in s₂, f a
参数：hs : forall a in s₁, a ∉ s₂ -> f a = 1。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.union_comm`：union_comm (s₁ s₂ : Finset α) : s₁ union s₂ = s₂ unio
n s₁
· 使用引理 `Finset.prod_union_eq_left`：prod_union_eq_left [DecidableEq ι] (hs : fora
ll a in s₂, a ∉ s₁ -> f a = 1) : ∏ a in s₁ union s₂, f a = ∏ a in s₁, f a
-/
lemma prod_union_eq_right [DecidableEq ι] (hs : ∀ a ∈ s₁, a ∉ s₂ → f a = 1) :
    ∏ a ∈ s₁ ∪ s₂, f a = ∏ a ∈ s₂, f a := by rw [union_comm, prod_union_eq_left hs]

/-- The products of two functions `f g : ι → M` over finite sets `s₁ s₂ : Finset ι`
are equal if the functions agree on `s₁ ∩ s₂`, `f = 1` and `g = 1` on the respective
set differences. -/
@[to_additive /-- The sum of two functions `f g : ι → M` over finite sets `s₁ s₂ : Finset ι`
are equal if the functions agree on `s₁ ∩ s₂`, `f = 0` and `g = 0` on the respective
set differences. -/]
/-
**Finset.prod_congr_of_eq_on_inter** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
形式化陈述：prod_congr_of_eq_on_inter {ι M : Type*} {s₁ s₂ : Finset ι} {f g : ι -> M} 
[CommMonoid M] (h₁ : forall a in s₁, a ∉ s₂ -> f a = 1) (h₂ : forall a in s₂, a 
∉ s₁ -> g a = 1) (h : forall a in s₁, a in s₂ -> f a = g a) : ∏ a in s₁, f a = ∏
 a in s₂, g a
参数：h₁ : forall a in s₁, a ∉ s₂ -> f a = 1；h₂ : forall a in s₂, a ∉ s₁ -> g a = 1
；h : forall a in s₁, a in s₂ -> f a = g a。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.sdiff_union_inter`：sdiff_union_inter (s t : Finset α) : s \ t uni
on s inter t = s
· 使用引理 `Finset.prod_union_eq_right`：prod_union_eq_right [DecidableEq ι] (hs : fo
rall a in s₁, a ∉ s₂ -> f a = 1) : ∏ a in s₁ union s₂, f a = ∏ a in s₂, f a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr_ctx`：∀ {p₁ p₂ q₁ q₂ : Prop}, p₁ = p₂ → (p₂ → q₁ = q₂) → (p
₁ → q₁) = (p₂ → q₂)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `and_false`：∀ (p : Prop), (p ∧ False) = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `Finset.inter_comm`：inter_comm (s₁ s₂ : Finset α) : s₁ inter s₂ = s₂ inte
r s₁
· 使用定理 `Finset.prod_congr`：prod_congr (h : s₁ = s₂) : (forall x in s₂, f x = g x
) -> s₁.prod f = s₂.prod g
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
-/
lemma prod_congr_of_eq_on_inter {ι M : Type*} {s₁ s₂ : Finset ι} {f g : ι → M} [CommMonoid M]
    (h₁ : ∀ a ∈ s₁, a ∉ s₂ → f a = 1) (h₂ : ∀ a ∈ s₂, a ∉ s₁ → g a = 1)
    (h : ∀ a ∈ s₁, a ∈ s₂ → f a = g a) :
    ∏ a ∈ s₁, f a = ∏ a ∈ s₂, g a := by
  classical
  conv_lhs => rw [← sdiff_union_inter s₁ s₂, prod_union_eq_right (by simp_all)]
  conv_rhs => rw [← sdiff_union_inter s₂ s₁, prod_union_eq_right (by simp_all), inter_comm]
  exact prod_congr rfl (by simpa)

@[to_additive]
/-
**Finset.prod_eq_mul_of_mem** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：prod_eq_mul_of_mem {s : Finset ι} {f : ι -> M} (a b : ι) (ha : a in s) (hb
 : b in s) (hn : a != b) (h₀ : forall c in s, c != a ∧ c != b -> f c = 1) : ∏ x 
in s, f x = f a * f b
参数：a b : ι；ha : a in s；hb : b in s；hn : a != b；h₀ : forall c in s, c != a ∧ c !=
 b -> f c = 1。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.prod_subset`：prod_subset (h : s₁ subseteq s₂) (hf : forall x in s
₂, x ∉ s₁ -> f x = 1) : ∏ x in s₁, f x = ∏ x in s₂, f x
· 使用定理 `Finset.prod_pair`：prod_pair [DecidableEq ι] {a b : ι} (h : a != b) : (∏ 
x in ({a, b} : Finset ι), f x) = f a * f b
-/
theorem prod_eq_mul_of_mem {s : Finset ι} {f : ι → M} (a b : ι) (ha : a ∈ s) (hb : b ∈ s)
    (hn : a ≠ b) (h₀ : ∀ c ∈ s, c ≠ a ∧ c ≠ b → f c = 1) : ∏ x ∈ s, f x = f a * f b := by
  have := Classical.decEq ι; let s' := ({a, b} : Finset ι)
  have hu : s' ⊆ s := by grind
  have hf : ∀ c ∈ s, c ∉ s' → f c = 1 := by grind
  rw [← Finset.prod_subset hu hf]
  exact Finset.prod_pair hn

@[to_additive]
/-
**Finset.prod_eq_mul** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：prod_eq_mul {s : Finset ι} {f : ι -> M} (a b : ι) (hn : a != b) (h₀ : fora
ll c in s, c != a ∧ c != b -> f c = 1) (ha : a ∉ s -> f a = 1) (hb : b ∉ s -> f 
b = 1) : ∏ x in s, f x = f a * f b
参数：a b : ι；hn : a != b；h₀ : forall c in s, c != a ∧ c != b -> f c = 1；ha : a ∉ s
 -> f a = 1；hb : b ∉ s -> f b = 1。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.prod_eq_mul_of_mem`：prod_eq_mul_of_mem {s : Finset ι} {f : ι -> M
} (a b : ι) (ha : a in s) (hb : b in s) (hn : a != b) (h₀ : forall c in s, c != 
a ∧ c != b -> f…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `Finset.prod_eq_single_of_mem`：prod_eq_single_of_mem {s : Finset ι} {f : 
ι -> M} (a : ι) (h : a in s) (h₀ : forall b in s, b != a -> f b = 1) : ∏ x in s,
 f x = f a
· 使用定理 `ne_of_mem_of_not_mem`：∀ {α : Type u_1} {β : Type u_2} [inst : Membership
 α β] {s : β} {a b : α}, a ∈ s → b ∉ s → a ≠ b
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用引理 `trans`：trans [IsTrans α r] : a ≺ b -> b ≺ c -> a ≺ c
· 使用定理 `IsPreorder.toIsTrans`：∀ {α : Sort u_1} {r : α → α → Prop} [self : IsPreo
rder α r], IsTrans α r
· 使用定理 `IsEquiv.toIsPreorder`：∀ {α : Sort u_1} {r : α → α → Prop} [self : IsEqui
v α r], IsPreorder α r
· 使用定理 `Finset.prod_congr`：prod_congr (h : s₁ = s₂) : (forall x in s₂, f x = g x
) -> s₁.prod f = s₂.prod g
· 使用定理 `Finset.prod_const_one`：prod_const_one : (∏ _x in s, (1 : M)) = 1
-/
theorem prod_eq_mul {s : Finset ι} {f : ι → M} (a b : ι) (hn : a ≠ b)
    (h₀ : ∀ c ∈ s, c ≠ a ∧ c ≠ b → f c = 1) (ha : a ∉ s → f a = 1) (hb : b ∉ s → f b = 1) :
    ∏ x ∈ s, f x = f a * f b := by
  have := Classical.decEq ι; by_cases h₁ : a ∈ s <;> by_cases h₂ : b ∈ s
  · exact prod_eq_mul_of_mem a b h₁ h₂ hn h₀
  · rw [hb h₂, mul_one]
    apply prod_eq_single_of_mem a h₁
    exact fun c hc hca => h₀ c hc ⟨hca, ne_of_mem_of_not_mem hc h₂⟩
  · rw [ha h₁, one_mul]
    apply prod_eq_single_of_mem b h₂
    exact fun c hc hcb => h₀ c hc ⟨ne_of_mem_of_not_mem hc h₁, hcb⟩
  · rw [ha h₁, hb h₂, mul_one]
    exact
      _root_.trans
        (prod_congr rfl fun c hc =>
          h₀ c hc ⟨ne_of_mem_of_not_mem hc h₁, ne_of_mem_of_not_mem hc h₂⟩)
        prod_const_one

/-- A product over `s.subtype p` equals one over `{x ∈ s | p x}`. -/
@[to_additive (attr := simp)
/-- A sum over `s.subtype p` equals one over `{x ∈ s | p x}`. -/]
/-
**Finset.prod_subtype_eq_prod_filter** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：prod_subtype_eq_prod_filter (f : ι -> M) {p : ι -> Prop} [DecidablePred p]
 : ∏ x in s.subtype p, f x = ∏ x in s with p x, f x
参数：f : ι -> M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.prod_map`：prod_map (s : Finset ι) (e : ι ↪ κ) (f : κ -> M) : ∏ x 
in s.map e, f x = ∏ x in s, f (e x)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Finset.prod_congr`：prod_congr (h : s₁ = s₂) : (forall x in s₂, f x = g x
) -> s₁.prod f = s₂.prod g
· 使用定理 `Finset.subtype_map`：subtype_map (p : α -> Prop) [DecidablePred p] {s : F
inset α} : (s.subtype p).map (Embedding.subtype _) = s.filter p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem prod_subtype_eq_prod_filter (f : ι → M) {p : ι → Prop} [DecidablePred p] :
    ∏ x ∈ s.subtype p, f x = ∏ x ∈ s with p x, f x := by
  have := prod_map (s.subtype p) (Function.Embedding.subtype _) f
  simp_all

/-- If all elements of a `Finset` satisfy the predicate `p`, a product
over `s.subtype p` equals that product over `s`. -/
@[to_additive /-- If all elements of a `Finset` satisfy the predicate `p`, a sum
over `s.subtype p` equals that sum over `s`. -/]
/-
**Finset.prod_subtype_of_mem** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：prod_subtype_of_mem (f : ι -> M) {p : ι -> Prop} [DecidablePred p] (h : fo
rall x in s, p x) : ∏ x in s.subtype p, f x = ∏ x in s, f x
参数：f : ι -> M；h : forall x in s, p x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.prod_subtype_eq_prod_filter`：prod_subtype_eq_prod_filter (f : ι -
> M) {p : ι -> Prop} [DecidablePred p] : ∏ x in s.subtype p, f x = ∏ x in s with
 p x, f x
· 使用定理 `Finset.filter_true_of_mem`：∀ {α : Type u_1} {p : α → Prop} [inst : Decid
ablePred p] {s : Finset α}, (∀ x ∈ s, p x) → Finset.filter p s = s
-/
theorem prod_subtype_of_mem (f : ι → M) {p : ι → Prop} [DecidablePred p] (h : ∀ x ∈ s, p x) :
    ∏ x ∈ s.subtype p, f x = ∏ x ∈ s, f x := by
  rw [prod_subtype_eq_prod_filter, filter_true_of_mem]
  simpa using h

/-- A product of a function over a `Finset` in a subtype equals a
product in the main type of a function that agrees with the first
function on that `Finset`. -/
@[to_additive /-- A sum of a function over a `Finset` in a subtype equals a
sum in the main type of a function that agrees with the first
function on that `Finset`. -/]
/-
**Finset.prod_subtype_map_embedding** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：prod_subtype_map_embedding {p : ι -> Prop} {s : Finset { x // p x }} {f : 
{ x // p x } -> M} {g : ι -> M} (h : forall x : { x // p x }, x in s -> g x = f 
x) : (∏ x in s.map (Function.Embedding.subtype _), g x) = ∏ x in s, f x
参数：h : forall x : { x // p x }, x in s -> g x = f x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.prod_map`：prod_map (s : Finset ι) (e : ι ↪ κ) (f : κ -> M) : ∏ x 
in s.map e, f x = ∏ x in s, f (e x)
· 使用定理 `Finset.prod_congr`：prod_congr (h : s₁ = s₂) : (forall x in s₂, f x = g x
) -> s₁.prod f = s₂.prod g
-/
theorem prod_subtype_map_embedding {p : ι → Prop} {s : Finset { x // p x }} {f : { x // p x } → M}
    {g : ι → M} (h : ∀ x : { x // p x }, x ∈ s → g x = f x) :
    (∏ x ∈ s.map (Function.Embedding.subtype _), g x) = ∏ x ∈ s, f x := by
  rw [Finset.prod_map]
  exact Finset.prod_congr rfl h

variable (f s)

@[to_additive]
/-
**Finset.prod_coe_sort** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：prod_coe_sort : ∏ i : s, f i = ∏ i in s, f i
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Finset.prod_attach`：prod_attach (s : Finset ι) (f : ι -> M) : ∏ x in s.a
ttach, f x = ∏ x in s, f x
-/
theorem prod_coe_sort : ∏ i : s, f i = ∏ i ∈ s, f i := prod_attach _ _

@[to_additive]
/-
**Finset.prod_finset_coe** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：prod_finset_coe (f : ι -> M) (s : Finset ι) : (∏ i : (s : Set ι), f i) = ∏
 i in s, f i
参数：f : ι -> M；s : Finset ι。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.prod_coe_sort`：prod_coe_sort : ∏ i : s, f i = ∏ i in s, f i
-/
theorem prod_finset_coe (f : ι → M) (s : Finset ι) : (∏ i : (s : Set ι), f i) = ∏ i ∈ s, f i :=
  prod_coe_sort s f

variable {f s}

@[to_additive]
/-
**Finset.prod_subtype** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：prod_subtype {p : ι -> Prop} {F : Fintype (Subtype p)} (s : Finset ι) (h :
 forall x, x in s ↔ p x) (f : ι -> M) : ∏ a in s, f a = ∏ a : Subtype p, f a
参数：Subtype p；s : Finset ι；h : forall x, x in s ↔ p x；f : ι -> M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.prod_coe_sort`：prod_coe_sort : ∏ i : s, f i = ∏ i in s, f i
· 使用定理 `Finset.prod_congr`：prod_congr (h : s₁ = s₂) : (forall x in s₂, f x = g x
) -> s₁.prod f = s₂.prod g
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Lean.Meta.FastSubsingleton.elim`：∀ {α : Sort u} [h : Meta.FastSubsinglet
on α] (a b : α), a = b
· 使用定理 `Fintype.instFastSubsingleton`：∀ (α : Type u_4), Meta.FastSubsingleton (F
intype α)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem prod_subtype {p : ι → Prop} {F : Fintype (Subtype p)} (s : Finset ι) (h : ∀ x, x ∈ s ↔ p x)
    (f : ι → M) : ∏ a ∈ s, f a = ∏ a : Subtype p, f a := by
  obtain rfl : p = (· ∈ s) := by simp [h]
  rw [← prod_coe_sort]
  congr!

@[to_additive]
/-
**Finset.prod_set_coe** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：prod_set_coe (s : Set ι) [Fintype s] : (∏ i : s, f i) = ∏ i in s.toFinset,
 f i
参数：s : Set ι。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.prod_subtype`：prod_subtype {p : ι -> Prop} {F : Fintype (Subtype 
p)} (s : Finset ι) (h : forall x, x in s ↔ p x) (f : ι -> M) : ∏ a in s, f a = ∏
 a : Subt…
· 使用定理 `Set.mem_toFinset`：mem_toFinset {s : Set α} [Fintype s] {a : α} : a in s.
toFinset ↔ a in s
-/
theorem prod_set_coe (s : Set ι) [Fintype s] : (∏ i : s, f i) = ∏ i ∈ s.toFinset, f i :=
  (Finset.prod_subtype s.toFinset (fun _ ↦ Set.mem_toFinset) f).symm

/-- The product of a function `g` defined only on a set `s` is equal to
the product of a function `f` defined everywhere,
as long as `f` and `g` agree on `s`, and `f = 1` off `s`. -/
@[to_additive /-- The sum of a function `g` defined only on a set `s` is equal to
the sum of a function `f` defined everywhere,
as long as `f` and `g` agree on `s`, and `f = 0` off `s`. -/]
/-
**Finset.prod_congr_set** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：prod_congr_set [Fintype ι] (s : Set ι) [DecidablePred (· in s)] (f : ι -> 
M) (g : s -> M) (w : forall x (hx : x in s), f x = g ⟨x, hx⟩) (w' : forall x ∉ s
, f x = 1) : ∏ i, f i = ∏ i, g i
参数：s : Set ι；· in s；f : ι -> M；g : s -> M；w : forall x (hx : x in s), f x = g ⟨x
, hx⟩；w' : forall x ∉ s, f x = 1。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.prod_subset`：prod_subset (h : s₁ subseteq s₂) (hf : forall x in s
₂, x ∉ s₁ -> f x = 1) : ∏ x in s₁, f x = ∏ x in s₂, f x
· 使用定理 `Finset.subset_univ`：subset_univ (s : Finset α) : s subseteq univ
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `Finset.prod_subtype`：prod_subtype {p : ι -> Prop} {F : Fintype (Subtype 
p)} (s : Finset ι) (h : forall x, x in s ↔ p x) (f : ι -> M) : ∏ a in s, f a = ∏
 a : Subt…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `Finset.prod_congr`：prod_congr (h : s₁ = s₂) : (forall x in s₂, f x = g x
) -> s₁.prod f = s₂.prod g
-/
theorem prod_congr_set [Fintype ι] (s : Set ι) [DecidablePred (· ∈ s)] (f : ι → M) (g : s → M)
    (w : ∀ x (hx : x ∈ s), f x = g ⟨x, hx⟩) (w' : ∀ x ∉ s, f x = 1) : ∏ i, f i = ∏ i, g i := by
  rw [← prod_subset s.toFinset.subset_univ (by simpa), prod_subtype (p := (· ∈ s)) _ (by simp)]
  congr! with ⟨x, h⟩
  exact w x h

@[to_additive]
/-
**Finset.prod_extend_by_one** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：prod_extend_by_one [DecidableEq ι] (s : Finset ι) (f : ι -> M) : ∏ i in s,
 (if i in s then f i else 1) = ∏ i in s, f i
参数：s : Finset ι；f : ι -> M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.prod_congr`：prod_congr (h : s₁ = s₂) : (forall x in s₂, f x = g x
) -> s₁.prod f = s₂.prod g
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
-/
theorem prod_extend_by_one [DecidableEq ι] (s : Finset ι) (f : ι → M) :
    ∏ i ∈ s, (if i ∈ s then f i else 1) = ∏ i ∈ s, f i :=
  (prod_congr rfl) fun _i hi => if_pos hi

/-- Also see `Finset.prod_ite_mem_eq` -/
@[to_additive /-- Also see `Finset.sum_ite_mem_eq` -/]
/-
**Finset.prod_eq_prod_extend** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：prod_eq_prod_extend (f : s -> M) : ∏ x, f x = ∏ x in s, Subtype.val.extend
 f 1 x
参数：f : s -> M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.univ_eq_attach`：Finset.univ_eq_attach {α : Type u} (s : Finset α)
 : (univ : Finset s) = s.attach
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `Finset.prod_attach`：prod_attach (s : Finset ι) (f : ι -> M) : ∏ x in s.a
ttach, f x = ∏ x in s, f x
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Function.Injective.extend_apply`：∀ {α : Sort u_1} {β : Sort u_2} {γ : So
rt u_3} {f : α → β},   Function.Injective f → ∀ (g : α → γ) (e' : β → γ) (a : α)
, Function.extend f g…
· 使用定理 `Subtype.val_injective`：∀ {α : Sort u_1} {p : α → Prop}, Function.Injecti
ve Subtype.val

--- 原说明 ---
Also see `Finset.prod_ite_mem_eq`
-/
theorem prod_eq_prod_extend (f : s → M) : ∏ x, f x = ∏ x ∈ s, Subtype.val.extend f 1 x := by
  rw [univ_eq_attach, ← Finset.prod_attach s]
  congr with ⟨x, hx⟩
  rw [Subtype.val_injective.extend_apply]

@[to_additive]
/-
**Finset.prod_bij_ne_one** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：prod_bij_ne_one {s : Finset ι} {t : Finset κ} {f : ι -> M} {g : κ -> M} (i
 : forall a in s, f a != 1 -> κ) (hi : forall a h₁ h₂, i a h₁ h₂ in t) (i_inj : 
forall a₁ h₁₁ h₁₂ a₂ h₂₁ h₂₂, i a₁ h₁₁ h₁₂ = i a₂ h₂₁ h₂₂ -> a₁ = a₂) (i_surj : 
forall b in t, g b != 1 -> exists a h₁ h₂, i a h₁ h₂ = b) (h : forall a h₁ h₂, f
 a = g (i a h₁ h₂)) : ∏ x in s, f x = ∏ x in t, g x
参数：i : forall a in s, f a != 1 -> κ；hi : forall a h₁ h₂, i a h₁ h₂ in t；i_inj : 
forall a₁ h₁₁ h₁₂ a₂ h₂₁ h₂₂, i a₁ h₁₁ h₁₂ = i a₂ h₂₁ h₂₂ -> a₁ = a₂；i_surj : fo
rall b in t, g b != 1 -> exists a h₁ h₂, i a h₁ h₂ = b；h : forall a h₁ h₂, f a =
 g (i a h₁ h₂)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.prod_filter_ne_one`：prod_filter_ne_one (s : Finset ι) [forall x, 
Decidable (f x != 1)] : ∏ x in s with f x != 1, f x = ∏ x in s, f x
· 使用定理 `Finset.prod_bij`：prod_bij (i : forall a in s, κ) (hi : forall a ha, i a 
ha in t) (i_inj : forall a₁ ha₁ a₂ ha₂, i a₁ ha₁ = i a₂ ha₂ -> a₁ = a₂) (i_surj 
: for…
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Finset.mem_filter`：∀ {α : Type u_1} {p : α → Prop} [inst : DecidablePred
 p] {s : Finset α} {a : α}, a ∈ Finset.filter p s ↔ a ∈ s ∧ p a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `not_true_eq_false`：(¬True) = False
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
-/
theorem prod_bij_ne_one {s : Finset ι} {t : Finset κ} {f : ι → M} {g : κ → M}
    (i : ∀ a ∈ s, f a ≠ 1 → κ) (hi : ∀ a h₁ h₂, i a h₁ h₂ ∈ t)
    (i_inj : ∀ a₁ h₁₁ h₁₂ a₂ h₂₁ h₂₂, i a₁ h₁₁ h₁₂ = i a₂ h₂₁ h₂₂ → a₁ = a₂)
    (i_surj : ∀ b ∈ t, g b ≠ 1 → ∃ a h₁ h₂, i a h₁ h₂ = b) (h : ∀ a h₁ h₂, f a = g (i a h₁ h₂)) :
    ∏ x ∈ s, f x = ∏ x ∈ t, g x := by
  classical
  calc
    ∏ x ∈ s, f x = ∏ x ∈ s with f x ≠ 1, f x := by rw [prod_filter_ne_one]
    _ = ∏ x ∈ t with g x ≠ 1, g x :=
      prod_bij (fun a ha => i a (mem_filter.mp ha).1 <| by simpa using (mem_filter.mp ha).2)
        ?_ ?_ ?_ ?_
    _ = ∏ x ∈ t, g x := prod_filter_ne_one _
  · grind
  · solve_by_elim
  · intro b hb
    refine (mem_filter.mp hb).elim fun h₁ h₂ ↦ ?_
    obtain ⟨a, ha₁, ha₂, eq⟩ := i_surj b h₁ fun H ↦ by rw [H] at h₂; simp at h₂
    exact ⟨a, mem_filter.mpr ⟨ha₁, ha₂⟩, eq⟩
  · solve_by_elim

@[to_additive]
/-
**Finset.exists_ne_one_of_prod_ne_one** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：exists_ne_one_of_prod_ne_one (h : ∏ x in s, f x != 1) : exists a in s, f a
 != 1
参数：h : ∏ x in s, f x != 1。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose₂`：contrapose₂ {p q : Prop} : (¬ q -
> p) -> (¬ p -> q)
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `Mathlib.Tactic.Push.not_and_eq`：not_and_eq : (¬ (p ∧ q)) = (p -> ¬ q)
· 使用定理 `Finset.prod_eq_one`：prod_eq_one (h : forall x in s, f x = 1) : ∏ x in s,
 f x = 1
-/
theorem exists_ne_one_of_prod_ne_one (h : ∏ x ∈ s, f x ≠ 1) : ∃ a ∈ s, f a ≠ 1 := by
  contrapose! h
  exact prod_eq_one h

@[to_additive]
/-
**Finset.prod_range_succ_comm** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：prod_range_succ_comm (f : Nat -> M) (n : Nat) : (∏ x in range (n + 1), f x
) = f n * ∏ x in range n, f x
参数：f : Nat -> M；n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.range_add_one`：range_add_one : range (n + 1) = insert n (range n)
· 使用定理 `Finset.prod_insert`：prod_insert [DecidableEq ι] : a ∉ s -> ∏ x in insert
 a s, f x = f a * ∏ x in s, f x
· 使用定理 `Finset.notMem_range_self`：notMem_range_self : n ∉ range n
-/
theorem prod_range_succ_comm (f : ℕ → M) (n : ℕ) :
    (∏ x ∈ range (n + 1), f x) = f n * ∏ x ∈ range n, f x := by
  rw [range_add_one, prod_insert notMem_range_self]

@[to_additive]
/-
**Finset.prod_range_succ** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：prod_range_succ (f : Nat -> M) (n : Nat) : (∏ x in range (n + 1), f x) = (
∏ x in range n, f x) * f n
参数：f : Nat -> M；n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.prod_range_succ_comm`：prod_range_succ_comm (f : Nat -> M) (n : Na
t) : (∏ x in range (n + 1), f x) = f n * ∏ x in range n, f x
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem prod_range_succ (f : ℕ → M) (n : ℕ) :
    (∏ x ∈ range (n + 1), f x) = (∏ x ∈ range n, f x) * f n := by
  simp only [mul_comm, prod_range_succ_comm]

@[to_additive]
/-
**Finset.prod_range_succ'** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：∀ {M : Type u_4} [inst : CommMonoid M] (f : ℕ → M) (n : ℕ),   ∏ k ∈ Finset
.range (n + 1), f k = (∏ k ∈ Finset.range n, f (k + 1)) * f 0
参数：f : ℕ → M；n : ℕ；n + 1；∏ k ∈ Finset.range n, f (k + 1)。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem prod_range_succ' (f : ℕ → M) :
    ∀ n : ℕ, (∏ k ∈ range (n + 1), f k) = (∏ k ∈ range n, f (k + 1)) * f 0
  | 0 => prod_range_succ _ _
  | n + 1 => by rw [prod_range_succ _ n, mul_right_comm, ← prod_range_succ' _ n, prod_range_succ]

@[to_additive]
/-
**Finset.eventually_constant_prod** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：eventually_constant_prod {u : Nat -> M} {N : Nat} (hu : forall n >= N, u n
 = 1) {n : Nat} (hn : N <= n) : (∏ k in range n, u k) = ∏ k in range N, u k
参数：hu : forall n >= N, u n = 1；hn : N <= n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.exists_eq_add_of_le`：∀ {m n : ℕ}, m ≤ n → ∃ k, n = m + k
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.prod_congr`：prod_congr (h : s₁ = s₂) : (forall x in s₂, f x = g x
) -> s₁.prod f = s₂.prod g
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Finset.prod_range_succ`：prod_range_succ (f : Nat -> M) (n : Nat) : (∏ x 
in range (n + 1), f x) = (∏ x in range n, f x) * f n
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem eventually_constant_prod {u : ℕ → M} {N : ℕ} (hu : ∀ n ≥ N, u n = 1) {n : ℕ} (hn : N ≤ n) :
    (∏ k ∈ range n, u k) = ∏ k ∈ range N, u k := by
  obtain ⟨m, rfl : n = N + m⟩ := Nat.exists_eq_add_of_le hn
  clear hn
  induction m with
  | zero => simp
  | succ m hm => simp [← add_assoc, prod_range_succ, hm, hu]

@[to_additive]
/-
**Finset.prod_range_add** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：prod_range_add (f : Nat -> M) (n m : Nat) : (∏ x in range (n + m), f x) = 
(∏ x in range n, f x) * ∏ x in range m, f (n + x)
参数：f : Nat -> M；n m : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.prod_congr`：prod_congr (h : s₁ = s₂) : (forall x in s₂, f x = g x
) -> s₁.prod f = s₂.prod g
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Nat.add_succ`：∀ (n m : ℕ), n + m.succ = (n + m).succ
· 使用定理 `Finset.prod_range_succ`：prod_range_succ (f : Nat -> M) (n : Nat) : (∏ x 
in range (n + 1), f x) = (∏ x in range n, f x) * f n
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
-/
theorem prod_range_add (f : ℕ → M) (n m : ℕ) :
    (∏ x ∈ range (n + m), f x) = (∏ x ∈ range n, f x) * ∏ x ∈ range m, f (n + x) := by
  induction m with
  | zero => simp
  | succ m hm => rw [Nat.add_succ, prod_range_succ, prod_range_succ, hm, mul_assoc]

@[to_additive sum_range_one]
/-
**Finset.prod_range_one** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：prod_range_one (f : Nat -> M) : ∏ k in range 1, f k = f 0
参数：f : Nat -> M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.range_one`：range_one : range 1 = {0}
· 使用定理 `Finset.prod_singleton`：prod_singleton (f : ι -> M) (a : ι) : ∏ x in sing
leton a, f x = f a
-/
theorem prod_range_one (f : ℕ → M) : ∏ k ∈ range 1, f k = f 0 := by
  rw [range_one, prod_singleton]

open List

@[to_additive]
/-
**Finset.prod_list_map_count** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：prod_list_map_count [DecidableEq ι] (l : List ι) (f : ι -> M) : (l.map f).
prod = ∏ m in l.toFinset, f m ^ l.count m
参数：l : List ι；f : ι -> M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `List.map_nil`：∀ {α : Type u} {β : Type v} {f : α → β}, List.map f [] = [
]
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `pow_zero`：pow_zero (a : M) : a ^ 0 = 1
· 使用定理 `Finset.prod_const_one`：prod_const_one : (∏ _x in s, (1 : M)) = 1
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Finset.prod_congr`：prod_congr (h : s₁ = s₂) : (forall x in s₂, f x = g x
) -> s₁.prod f = s₂.prod g
· 使用定理 `List.toFinset_cons`：toFinset_cons : toFinset (a :: l) = insert a (toFins
et l)
· 使用定理 `Finset.insert_eq_of_mem`：insert_eq_of_mem (h : a in s) : insert a s = s
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.insert_erase`：∀ {α : Type u_1} [inst : DecidableEq α] {s : Finset
 α} {a : α}, a ∈ s → insert a (s.erase a) = s
· 使用定理 `Finset.prod_insert`：prod_insert [DecidableEq ι] : a ∉ s -> ∏ x in insert
 a s, f x = f a * ∏ x in s, f x
· 使用定理 `Finset.notMem_erase`：notMem_erase (a : α) (s : Finset α) : a ∉ erase s a
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `List.count_cons_self`：∀ {α : Type u_1} [inst : BEq α] [LawfulBEq α] {a :
 α} {l : List α}, List.count a (a :: l) = List.count a l + 1
· 使用定理 `instLawfulBEq`：∀ {α : Type u_1} [inst : DecidableEq α], LawfulBEq α
· 使用定理 `pow_succ'`：∀ {M : Type u_2} [inst : Monoid M] (a : M) (n : ℕ), a ^ (n + 
1) = a * a ^ n
· 使用定理 `List.count_cons_of_ne`：∀ {α : Type u_1} [inst : BEq α] [LawfulBEq α] {b 
a : α}, b ≠ a → ∀ {l : List α}, List.count a (b :: l) = List.count a l
· 使用定理 `Ne.symm`：∀ {α : Sort u} {a b : α}, a ≠ b → b ≠ a
· 使用定理 `Finset.ne_of_mem_erase`：ne_of_mem_erase : b in erase s a -> b != a
· 使用定理 `List.count_eq_zero_of_not_mem`：∀ {α : Type u_1} [inst : BEq α] [LawfulBE
q α] {a : α} {l : List α}, a ∉ l → List.count a l = 0
· 使用定理 `mt`：∀ {a b : Prop}, (a → b) → ¬b → ¬a
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `List.mem_toFinset`：mem_toFinset : a in l.toFinset ↔ a in l
· 使用引理 `pow_one`：pow_one (a : M) : a ^ 1 = a
-/
theorem prod_list_map_count [DecidableEq ι] (l : List ι) (f : ι → M) :
    (l.map f).prod = ∏ m ∈ l.toFinset, f m ^ l.count m := by
  induction l with
  | nil => simp only [map_nil, prod_nil, count_nil, pow_zero, prod_const_one]
  | cons a s IH =>
  simp only [List.map, List.prod_cons, toFinset_cons, IH]
  by_cases has : a ∈ s.toFinset
  · rw [insert_eq_of_mem has, ← insert_erase has, prod_insert (notMem_erase _ _),
      prod_insert (notMem_erase _ _), ← mul_assoc, count_cons_self, pow_succ']
    congr 1
    refine prod_congr rfl fun x hx => ?_
    rw [count_cons_of_ne (ne_of_mem_erase hx).symm]
  rw [prod_insert has, count_cons_self, count_eq_zero_of_not_mem (mt mem_toFinset.2 has), pow_one]
  grind [Finset.prod_congr]

@[to_additive]
/-
**Finset.prod_list_count** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：prod_list_count [DecidableEq M] (s : List M) : s.prod = ∏ m in s.toFinset,
 m ^ s.count m
参数：s : List M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `List.map_id_fun`：∀ {α : Type u_1}, List.map id = id
· 使用定理 `Finset.prod_congr`：prod_congr (h : s₁ = s₂) : (forall x in s₂, f x = g x
) -> s₁.prod f = s₂.prod g
· 使用定理 `Finset.prod_list_map_count`：prod_list_map_count [DecidableEq ι] (l : Lis
t ι) (f : ι -> M) : (l.map f).prod = ∏ m in l.toFinset, f m ^ l.count m
-/
theorem prod_list_count [DecidableEq M] (s : List M) :
    s.prod = ∏ m ∈ s.toFinset, m ^ s.count m := by simpa using prod_list_map_count s id

@[to_additive]
/-
**Finset.prod_list_count_of_subset** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：prod_list_count_of_subset [DecidableEq M] (m : List M) (s : Finset M) (hs 
: m.toFinset subseteq s) : m.prod = ∏ i in s, i ^ m.count i
参数：m : List M；s : Finset M；hs : m.toFinset subseteq s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.prod_list_count`：prod_list_count [DecidableEq M] (s : List M) : s
.prod = ∏ m in s.toFinset, m ^ s.count m
· 使用定理 `Finset.prod_subset`：prod_subset (h : s₁ subseteq s₂) (hf : forall x in s
₂, x ∉ s₁ -> f x = 1) : ∏ x in s₁, f x = ∏ x in s₂, f x
· 使用定理 `List.count_eq_zero_of_not_mem`：∀ {α : Type u_1} [inst : BEq α] [LawfulBE
q α] {a : α} {l : List α}, a ∉ l → List.count a l = 0
· 使用定理 `instLawfulBEq`：∀ {α : Type u_1} [inst : DecidableEq α], LawfulBEq α
· 使用定理 `List.mem_toFinset`：mem_toFinset : a in l.toFinset ↔ a in l
· 使用定理 `pow_zero`：pow_zero (a : M) : a ^ 0 = 1
-/
theorem prod_list_count_of_subset [DecidableEq M] (m : List M) (s : Finset M)
    (hs : m.toFinset ⊆ s) : m.prod = ∏ i ∈ s, i ^ m.count i := by
  rw [prod_list_count]
  refine prod_subset hs fun x _ hx => ?_
  rw [mem_toFinset] at hx
  rw [count_eq_zero_of_not_mem hx, pow_zero]

open Multiset

@[to_additive]
/-
**Finset.prod_multiset_map_count** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：prod_multiset_map_count [DecidableEq ι] (s : Multiset ι) {M : Type*} [Comm
Monoid M] (f : ι -> M) : (s.map f).prod = ∏ m in s.toFinset, f m ^ s.count m
参数：s : Multiset ι；f : ι -> M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Quot.induction_on`：∀ {α : Sort u_4} {r : α → α → Prop} {β : Quot r → Pro
p} (q : Quot r), (∀ (a : α), β (Quot.mk r a)) → β q
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.prod_list_map_count`：prod_list_map_count [DecidableEq ι] (l : Lis
t ι) (f : ι -> M) : (l.map f).prod = ∏ m in l.toFinset, f m ^ l.count m
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Multiset.coe_count`：coe_count (a : α) (l : List α) : count a (ofList l) 
= l.count a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem prod_multiset_map_count [DecidableEq ι] (s : Multiset ι) {M : Type*} [CommMonoid M]
    (f : ι → M) : (s.map f).prod = ∏ m ∈ s.toFinset, f m ^ s.count m := by
  refine Quot.induction_on s fun l => ?_
  simp [prod_list_map_count l f]

@[to_additive]
/-
**Finset.prod_multiset_count** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：prod_multiset_count [DecidableEq M] (s : Multiset M) : s.prod = ∏ m in s.t
oFinset, m ^ s.count m
参数：s : Multiset M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Multiset.map_id`：map_id (s : Multiset α) : map id s = s
· 使用定理 `Finset.prod_congr`：prod_congr (h : s₁ = s₂) : (forall x in s₂, f x = g x
) -> s₁.prod f = s₂.prod g
· 使用定理 `Finset.prod_multiset_map_count`：prod_multiset_map_count [DecidableEq ι] 
(s : Multiset ι) {M : Type*} [CommMonoid M] (f : ι -> M) : (s.map f).prod = ∏ m 
in s.toFinset, f m ^…
-/
theorem prod_multiset_count [DecidableEq M] (s : Multiset M) :
    s.prod = ∏ m ∈ s.toFinset, m ^ s.count m := by
  convert! prod_multiset_map_count s id
  rw [Multiset.map_id]

@[to_additive]
/-
**Finset.prod_multiset_count_of_subset** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：prod_multiset_count_of_subset [DecidableEq M] (m : Multiset M) (s : Finset
 M) (hs : m.toFinset subseteq s) : m.prod = ∏ i in s, i ^ m.count i
参数：m : Multiset M；s : Finset M；hs : m.toFinset subseteq s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Quot.induction_on`：∀ {α : Sort u_4} {r : α → α → Prop} {β : Quot r → Pro
p} (q : Quot r), (∀ (a : α), β (Quot.mk r a)) → β q
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.prod_congr`：prod_congr (h : s₁ = s₂) : (forall x in s₂, f x = g x
) -> s₁.prod f = s₂.prod g
· 使用定理 `Multiset.coe_count`：coe_count (a : α) (l : List α) : count a (ofList l) 
= l.count a
· 使用定理 `Finset.prod_list_count_of_subset`：prod_list_count_of_subset [DecidableEq
 M] (m : List M) (s : Finset M) (hs : m.toFinset subseteq s) : m.prod = ∏ i in s
, i ^ m.count i
-/
theorem prod_multiset_count_of_subset [DecidableEq M] (m : Multiset M) (s : Finset M)
    (hs : m.toFinset ⊆ s) : m.prod = ∏ i ∈ s, i ^ m.count i := by
  revert hs
  refine Quot.induction_on m fun l => ?_
  simp only [quot_mk_to_coe'', prod_coe, coe_count]
  apply prod_list_count_of_subset l s

/-- For any product along `{0, ..., n - 1}` of a commutative-monoid-valued function, we can verify
that it's equal to a different function just by checking ratios of adjacent terms up to `n`.

This is a multiplicative discrete analogue of the fundamental theorem of calculus. -/
@[to_additive /-- For any sum along `{0, ..., n - 1}` of a commutative-monoid-valued function, we
can verify that it's equal to a different function just by checking differences of adjacent terms
up to `n`.

This is a discrete analogue of the fundamental theorem of calculus. -/]
/-
**Finset.prod_range_induction** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：prod_range_induction (f s : Nat -> M) (base : s 0 = 1) (n : Nat) (step : f
orall k < n, s (k + 1) = s k * f k) : ∏ k in Finset.range n, f k = s n
参数：f s : Nat -> M；base : s 0 = 1；n : Nat；step : forall k < n, s (k + 1) = s k * 
f k。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.prod_range_zero`：prod_range_zero (f : Nat -> M) : ∏ k in range 0,
 f k = 1
· 使用定理 `Finset.prod_range_succ`：prod_range_succ (f : Nat -> M) (n : Nat) : (∏ x 
in range (n + 1), f x) = (∏ x in range n, f x) * f n
· 使用定理 `Nat.lt_succ_self`：∀ (n : ℕ), n < n.succ
· 使用定理 `Nat.lt_succ_of_lt`：∀ {a b : ℕ}, a < b → a < b.succ
-/
theorem prod_range_induction (f s : ℕ → M) (base : s 0 = 1)
    (n : ℕ) (step : ∀ k < n, s (k + 1) = s k * f k) :
    ∏ k ∈ Finset.range n, f k = s n := by
  induction n with
  | zero => rw [Finset.prod_range_zero, base]
  | succ k hk =>
    rw [Finset.prod_range_succ, step _ (Nat.lt_succ_self _), hk]
    exact fun _ hl ↦ step _ (Nat.lt_succ_of_lt hl)

@[to_additive (attr := simp)]
/-
**Finset.prod_const** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：prod_const (b : M) : ∏ _x in s, b = b ^ #s
参数：b : M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `Multiset.map_const`：map_const (s : Multiset α) (b : β) : map (const α b)
 s = replicate (card s) b
· 使用定理 `Multiset.prod_replicate`：prod_replicate (n : Nat) (a : M) : (replicate n
 a).prod = a ^ n
-/
theorem prod_const (b : M) : ∏ _x ∈ s, b = b ^ #s :=
  (congr_arg _ <| s.val.map_const b).trans <| Multiset.prod_replicate #s b

@[to_additive sum_eq_card_nsmul]
/-
**Finset.prod_eq_pow_card** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：prod_eq_pow_card {b : M} (hf : forall a in s, f a = b) : ∏ a in s, f a = b
 ^ #s
参数：hf : forall a in s, f a = b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Finset.prod_congr`：prod_congr (h : s₁ = s₂) : (forall x in s₂, f x = g x
) -> s₁.prod f = s₂.prod g
· 使用定理 `Finset.prod_const`：prod_const (b : M) : ∏ _x in s, b = b ^ #s
-/
theorem prod_eq_pow_card {b : M} (hf : ∀ a ∈ s, f a = b) : ∏ a ∈ s, f a = b ^ #s :=
  (prod_congr rfl hf).trans <| prod_const _

@[to_additive card_nsmul_add_sum]
/-
**Finset.pow_card_mul_prod** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：pow_card_mul_prod {b : M} : b ^ #s * ∏ a in s, f a = ∏ a in s, b * f a
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.prod_mul_distrib`：prod_mul_distrib : ∏ x in s, f x * g x = (∏ x i
n s, f x) * ∏ x in s, g x
· 使用定理 `Finset.prod_const`：prod_const (b : M) : ∏ _x in s, b = b ^ #s
-/
theorem pow_card_mul_prod {b : M} : b ^ #s * ∏ a ∈ s, f a = ∏ a ∈ s, b * f a :=
  (Finset.prod_const b).symm ▸ prod_mul_distrib.symm

@[to_additive sum_add_card_nsmul]
/-
**Finset.prod_mul_pow_card** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：prod_mul_pow_card {b : M} : (∏ a in s, f a) * b ^ #s = ∏ a in s, f a * b
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.prod_mul_distrib`：prod_mul_distrib : ∏ x in s, f x * g x = (∏ x i
n s, f x) * ∏ x in s, g x
· 使用定理 `Finset.prod_const`：prod_const (b : M) : ∏ _x in s, b = b ^ #s
-/
theorem prod_mul_pow_card {b : M} : (∏ a ∈ s, f a) * b ^ #s = ∏ a ∈ s, f a * b :=
  (Finset.prod_const b).symm ▸ prod_mul_distrib.symm

@[to_additive]
/-
**Finset.pow_eq_prod_const** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：pow_eq_prod_const (b : M) : forall n, b ^ n = ∏ _k in range n, b
参数：b : M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.prod_const`：prod_const (b : M) : ∏ _x in s, b = b ^ #s
· 使用定理 `Finset.card_range`：card_range (n : Nat) : #(range n) = n
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
theorem pow_eq_prod_const (b : M) : ∀ n, b ^ n = ∏ _k ∈ range n, b := by simp

@[to_additive sum_nsmul_assoc]
/-
**Finset.prod_pow_eq_pow_sum** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
形式化陈述：prod_pow_eq_pow_sum (s : Finset ι) (f : ι -> Nat) (a : M) : ∏ i in s, a ^ 
f i = a ^ ∑ i in s, f i
参数：s : Finset ι；f : ι -> Nat；a : M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.cons_induction`：∀ {α : Type u_3} {motive : Finset α → Prop},   mo
tive ∅ → (∀ (a : α) (s : Finset α) (h : a ∉ s), motive s → motive (Finset.cons a
 s h)) → ∀ …
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `pow_zero`：pow_zero (a : M) : a ^ 0 = 1
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Finset.prod_cons`：prod_cons (h : a ∉ s) : ∏ x in cons a s h, f x = f a *
 ∏ x in s, f x
· 使用定理 `Finset.sum_cons`：∀ {ι : Type u_1} {M : Type u_4} {s : Finset ι} {a : ι} 
[inst : AddCommMonoid M] {f : ι → M} (h : a ∉ s),   ∑ x ∈ Finset.cons a s h, f x
 = f …
· 使用定理 `pow_add`：pow_add {b₁ b₂ : Nat} {d : R} (_ : a ^ b₁ = c₁) (_ : a ^ b₂ = c
₂) (_ : c₁ * c₂ = d) : (a : R) ^ (b₁ + b₂) = d
-/
lemma prod_pow_eq_pow_sum (s : Finset ι) (f : ι → ℕ) (a : M) :
    ∏ i ∈ s, a ^ f i = a ^ ∑ i ∈ s, f i :=
  cons_induction (by simp) (fun _ _ _ _ ↦ by simp [prod_cons, sum_cons, pow_add, *]) s

@[to_additive]
/-
**Finset.prod_flip** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：prod_flip {n : Nat} (f : Nat -> M) : (∏ r in range (n + 1), f (n - r)) = ∏
 k in range (n + 1), f k
参数：f : Nat -> M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.prod_range_one`：prod_range_one (f : Nat -> M) : ∏ k in range 1, f
 k = f 0
· 使用定理 `Finset.prod_range_succ'`：∀ {M : Type u_4} [inst : CommMonoid M] (f : ℕ →
 M) (n : ℕ),   ∏ k ∈ Finset.range (n + 1), f k = (∏ k ∈ Finset.range n, f (k + 1
)) * f 0
· 使用定理 `Finset.prod_range_succ`：prod_range_succ (f : Nat -> M) (n : Nat) : (∏ x 
in range (n + 1), f x) = (∏ x in range n, f x) * f n
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Finset.prod_congr`：prod_congr (h : s₁ = s₂) : (forall x in s₂, f x = g x
) -> s₁.prod f = s₂.prod g
· 使用定理 `Nat.Simproc.add_sub_add_le`：∀ (a c : ℕ) {b d : ℕ}, b ≤ d → a + b - (c + 
d) = a - (c + (d - b))
· 使用定理 `of_decide_eq_true`：∀ {p : Prop} [inst : Decidable p], decide p = true → 
p
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem prod_flip {n : ℕ} (f : ℕ → M) :
    (∏ r ∈ range (n + 1), f (n - r)) = ∏ k ∈ range (n + 1), f k := by
  induction n with
  | zero => rw [prod_range_one, prod_range_one]
  | succ n ih =>
    rw [prod_range_succ', prod_range_succ _ (Nat.succ n)]
    simp [← ih]

/-- The difference with `Finset.prod_ninvolution` is that the involution is allowed to use
membership of the domain of the product, rather than being a non-dependent function. -/
@[to_additive /-- The difference with `Finset.sum_ninvolution` is that the involution is allowed to
use membership of the domain of the sum, rather than being a non-dependent function. -/]
/-
**Finset.prod_involution** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
形式化陈述：prod_involution (g : forall a in s, ι) (hg₁ : forall a ha, f a * f (g a ha
) = 1) (hg₃ : forall a ha, f a != 1 -> g a ha != a) (g_mem : forall a ha, g a ha
 in s) (hg₄ : forall a ha, g (g a ha) (g_mem a ha) = a) : ∏ x in s, f x = 1
参数：g : forall a in s, ι；hg₁ : forall a ha, f a * f (g a ha) = 1；hg₃ : forall a h
a, f a != 1 -> g a ha != a；g_mem : forall a ha, g a ha in s；hg₄ : forall a ha, g
 (g a ha) (g_mem a ha) = a。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.eq_empty_or_nonempty`：eq_empty_or_nonempty (s : Finset α) : s = ∅
 ∨ s.Nonempty
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
· 使用定理 `Finset.sdiff_subset`：sdiff_subset {s t : Finset α} : s \ t subseteq s
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Finset.ssubset_iff`：ssubset_iff : s ⊂ t ↔ exists a ∉ s, insert a s subse
teq t
· 使用定理 `true_or`：∀ (p : Prop), (True ∨ p) = True
· 使用定理 `not_true_eq_false`：(¬True) = False
· 使用定理 `and_false`：∀ (p : Prop), (p ∧ False) = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `Finset.insert_union`：insert_union (a : α) (s t : Finset α) : insert a s 
union t = insert a (s union t)
· 使用定理 `Finset.insert_eq_of_mem`：insert_eq_of_mem (h : a in s) : insert a s = s
· 使用定理 `or_true`：∀ (p : Prop), (p ∨ True) = True
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `forall_prop_domain_congr`：∀ {p₁ p₂ : Prop} {q₁ : p₁ → Prop} {q₂ : p₂ → P
rop} (h₁ : p₁ = p₂),   (∀ (a : p₂), q₁ ⋯ = q₂ a) → (∀ (a : p₁), q₁ a) = ∀ (a : p
₂), q₂ a
· 使用定理 `Eq.substr`：∀ {α : Sort u} {p : α → Prop} {a b : α}, b = a → p a → p b
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `Finset.prod_sdiff`：prod_sdiff [DecidableEq ι] (h : s₁ subseteq s₂) : (∏ 
x in s₂ \ s₁, f x) * ∏ x in s₁, f x = ∏ x in s₂, f x
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `Finset.prod_congr`：prod_congr (h : s₁ = s₂) : (forall x in s₂, f x = g x
) -> s₁.prod f = s₂.prod g
· 使用定理 `Finset.prod_singleton`：prod_singleton (f : ι -> M) (a : ι) : ∏ x in sing
leton a, f x = f a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
-/
lemma prod_involution (g : ∀ a ∈ s, ι) (hg₁ : ∀ a ha, f a * f (g a ha) = 1)
    (hg₃ : ∀ a ha, f a ≠ 1 → g a ha ≠ a)
    (g_mem : ∀ a ha, g a ha ∈ s) (hg₄ : ∀ a ha, g (g a ha) (g_mem a ha) = a) :
    ∏ x ∈ s, f x = 1 := by
  classical
  induction s using Finset.strongInduction with | H s ih => ?_
  obtain rfl | ⟨x, hx⟩ := s.eq_empty_or_nonempty
  · simp
  have : {x, g x hx} ⊆ s := by simp [insert_subset_iff, hx, g_mem]
  suffices h : ∏ x ∈ s \ {x, g x hx}, f x = 1 by
    rw [← prod_sdiff this, h, one_mul]
    cases eq_or_ne (g x hx) x with
    | inl hx' => simpa [hx'] using hg₃ x hx
    | inr hx' => grind
  suffices h₃ : ∀ a (ha : a ∈ s \ {x, g x hx}), g a (sdiff_subset ha) ∈ s \ {x, g x hx} from
    ih (s \ {x, g x hx}) (ssubset_iff.2 ⟨x, by simp [insert_subset_iff, hx]⟩) _
      (by simp [hg₁]) (fun _ _ => hg₃ _ _) h₃ (fun _ _ => hg₄ _ _)
  grind

/-- The difference with `Finset.prod_involution` is that the involution is a non-dependent function,
rather than being allowed to use membership of the domain of the product. -/
@[to_additive /-- The difference with `Finset.sum_involution` is that the involution is a
non-dependent function, rather than being allowed to use membership of the domain of the sum. -/]
/-
**Finset.prod_ninvolution** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
形式化陈述：prod_ninvolution (g : ι -> ι) (hg₁ : forall a, f a * f (g a) = 1) (hg₂ : f
orall a, f a != 1 -> g a != a) (g_mem : forall a, g a in s) (hg₃ : forall a, g (
g a) = a) : ∏ x in s, f x = 1
参数：g : ι -> ι；hg₁ : forall a, f a * f (g a) = 1；hg₂ : forall a, f a != 1 -> g a 
!= a；g_mem : forall a, g a in s；hg₃ : forall a, g (g a) = a。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Finset.prod_involution`：prod_involution (g : forall a in s, ι) (hg₁ : fo
rall a ha, f a * f (g a ha) = 1) (hg₃ : forall a ha, f a != 1 -> g a ha != a) (g
_mem : foral…
-/
lemma prod_ninvolution (g : ι → ι) (hg₁ : ∀ a, f a * f (g a) = 1) (hg₂ : ∀ a, f a ≠ 1 → g a ≠ a)
    (g_mem : ∀ a, g a ∈ s) (hg₃ : ∀ a, g (g a) = a) : ∏ x ∈ s, f x = 1 :=
  prod_involution (fun i _ => g i) (fun i _ => hg₁ i) (fun _ _ hi => hg₂ _ hi)
    (fun i _ => g_mem i) (fun i _ => hg₃ i)

/-- The product of the composition of functions `f` and `g`, is the product over `b ∈ s.image g` of
`f b` to the power of the cardinality of the fibre of `b`. See also `Finset.prod_image`. -/
@[to_additive /-- The sum of the composition of functions `f` and `g`, is the sum over
`b ∈ s.image g` of `f b` times of the cardinality of the fibre of `b`. See also
`Finset.sum_image`. -/]
/-
**Finset.prod_comp** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：prod_comp [DecidableEq κ] (f : κ -> M) (g : ι -> κ) : ∏ a in s, f (g a) = 
∏ b in s.image g, f b ^ #{a in s | g a = b}
参数：f : κ -> M；g : ι -> κ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.prod_congr`：prod_congr (h : s₁ = s₂) : (forall x in s₂, f x = g x
) -> s₁.prod f = s₂.prod g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用引理 `Finset.prod_fiberwise_of_maps_to'`：prod_fiberwise_of_maps_to' {g : ι -> 
κ} (h : forall i in s, g i in t) (f : κ -> M) : ∏ j in t, ∏ i in s with g i = j,
 f j = ∏ i in s, f (g i…
· 使用定理 `Finset.mem_image_of_mem`：mem_image_of_mem (f : α -> β) {a} (h : a in s) 
: f a in s.image f
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem prod_comp [DecidableEq κ] (f : κ → M) (g : ι → κ) :
    ∏ a ∈ s, f (g a) = ∏ b ∈ s.image g, f b ^ #{a ∈ s | g a = b} := by
  simp_rw [← prod_const, prod_fiberwise_of_maps_to' fun _ ↦ mem_image_of_mem _]

/-- A product can be partitioned into a product of products, each equivalent under a setoid. -/
@[to_additive /-- A sum can be partitioned into a sum of sums, each equivalent under a setoid. -/]
/-
**Finset.prod_partition** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：prod_partition (R : Setoid ι) [DecidableRel R.r] : ∏ x in s, f x = ∏ xbar 
in s.image (Quotient.mk _), ∏ y in s with ⟦y⟧ = xbar, f y
参数：R : Setoid ι。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.prod_image'`：prod_image' [DecidableEq ι] {s : Finset κ} {g : κ ->
 ι} (h : κ -> M) (eq : forall i in s, f (g i) = ∏ j in s with g j = g i, h j) : 
∏ a in s…

--- 原说明 ---
A product can be partitioned into a product of products, each equivalent under a
 setoid.
-/
theorem prod_partition (R : Setoid ι) [DecidableRel R.r] :
    ∏ x ∈ s, f x = ∏ xbar ∈ s.image (Quotient.mk _), ∏ y ∈ s with ⟦y⟧ = xbar, f y := by
  refine (Finset.prod_image' f fun x _hx => ?_).symm
  rfl

/-- If we can partition a product into subsets that cancel out, then the whole product cancels. -/
@[to_additive /-- If we can partition a sum into subsets that cancel out, then the whole sum
cancels. -/]
/-
**Finset.prod_cancels_of_partition_cancels** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：prod_cancels_of_partition_cancels (R : Setoid ι) [DecidableRel R] (h : for
all x in s, ∏ a in s with R a x, f a = 1) : ∏ x in s, f x = 1
参数：R : Setoid ι；h : forall x in s, ∏ a in s with R a x, f a = 1。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.prod_partition`：prod_partition (R : Setoid ι) [DecidableRel R.r] 
: ∏ x in s, f x = ∏ xbar in s.image (Quotient.mk _), ∏ y in s with ⟦y⟧ = xbar, f
 y
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.prod_eq_one`：prod_eq_one (h : forall x in s, f x = 1) : ∏ x in s,
 f x = 1
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Finset.mem_image`：mem_image : b in s.image f ↔ exists a in s, f a = b
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Finset.prod_congr`：prod_congr (h : s₁ = s₂) : (forall x in s₂, f x = g x
) -> s₁.prod f = s₂.prod g
· 使用定理 `Finset.filter_congr`：∀ {α : Type u_1} {p q : α → Prop} [inst : Decidable
Pred p] [inst_1 : DecidablePred q] {s : Finset α},   (∀ x ∈ s, p x ↔ q x) → Fins
et.filter…
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
-/
theorem prod_cancels_of_partition_cancels (R : Setoid ι) [DecidableRel R]
    (h : ∀ x ∈ s, ∏ a ∈ s with R a x, f a = 1) : ∏ x ∈ s, f x = 1 := by
  rw [prod_partition R, ← Finset.prod_eq_one]
  intro xbar xbar_in_s
  obtain ⟨x, x_in_s, rfl⟩ := mem_image.mp xbar_in_s
  simp only [← Quotient.eq] at h
  exact h x x_in_s

/-- If a product of a `Finset` of size at most 1 has a given value, so
do the terms in that product. -/
@[to_additive eq_of_card_le_one_of_sum_eq /-- If a sum of a `Finset` of size at most 1 has a given
value, so do the terms in that sum. -/]
/-
**Finset.eq_of_card_le_one_of_prod_eq** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：eq_of_card_le_one_of_prod_eq {s : Finset ι} (hc : #s <= 1) {f : ι -> M} {b
 : M} (h : ∏ x in s, f x = b) : forall x in s, f x = b
参数：hc : #s <= 1；h : ∏ x in s, f x = b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.card_ne_zero_of_mem`：card_ne_zero_of_mem (h : a in s) : #s != 0
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `Nat.one_le_of_lt`：∀ {a b : ℕ}, a < b → 1 ≤ b
· 使用定理 `Nat.pos_of_ne_zero`：∀ {n : ℕ}, n ≠ 0 → 0 < n
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.card_eq_one`：card_eq_one : #s = 1 ↔ exists a, s = {a}
-/
theorem eq_of_card_le_one_of_prod_eq {s : Finset ι} (hc : #s ≤ 1) {f : ι → M} {b : M}
    (h : ∏ x ∈ s, f x = b) : ∀ x ∈ s, f x = b := by
  intro x hx
  by_cases hc0 : #s = 0
  · exact False.elim (card_ne_zero_of_mem hx hc0)
  · have h1 : #s = 1 := le_antisymm hc (Nat.one_le_of_lt (Nat.pos_of_ne_zero hc0))
    rw [card_eq_one] at h1
    grind

/-- Taking a product over `s : Finset ι` is the same as multiplying the value on a single element
`f a` by the product of `s.erase a`.

See `Multiset.prod_map_erase` for the `Multiset` version. -/
@[to_additive /-- Taking a sum over `s : Finset ι` is the same as adding the value on a single
element `f a` to the sum over `s.erase a`.

See `Multiset.sum_map_erase` for the `Multiset` version. -/]
/-
**Finset.mul_prod_erase** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：mul_prod_erase [DecidableEq ι] (s : Finset ι) (f : ι -> M) {a : ι} (h : a 
in s) : (f a * ∏ x in s.erase a, f x) = ∏ x in s, f x
参数：s : Finset ι；f : ι -> M；h : a in s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.prod_insert`：prod_insert [DecidableEq ι] : a ∉ s -> ∏ x in insert
 a s, f x = f a * ∏ x in s, f x
· 使用定理 `Finset.notMem_erase`：notMem_erase (a : α) (s : Finset α) : a ∉ erase s a
· 使用定理 `Finset.insert_erase`：∀ {α : Type u_1} [inst : DecidableEq α] {s : Finset
 α} {a : α}, a ∈ s → insert a (s.erase a) = s
-/
theorem mul_prod_erase [DecidableEq ι] (s : Finset ι) (f : ι → M) {a : ι} (h : a ∈ s) :
    (f a * ∏ x ∈ s.erase a, f x) = ∏ x ∈ s, f x := by
  rw [← prod_insert (notMem_erase a s), insert_erase h]

/-- A variant of `Finset.mul_prod_erase` with the multiplication swapped. -/
@[to_additive /-- A variant of `Finset.add_sum_erase` with the addition swapped. -/]
/-
**Finset.prod_erase_mul** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：prod_erase_mul [DecidableEq ι] (s : Finset ι) (f : ι -> M) {a : ι} (h : a 
in s) : (∏ x in s.erase a, f x) * f a = ∏ x in s, f x
参数：s : Finset ι；f : ι -> M；h : a in s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `Finset.mul_prod_erase`：mul_prod_erase [DecidableEq ι] (s : Finset ι) (f 
: ι -> M) {a : ι} (h : a in s) : (f a * ∏ x in s.erase a, f x) = ∏ x in s, f x

--- 原说明 ---
A variant of `Finset.mul_prod_erase` with the multiplication swapped.
-/
theorem prod_erase_mul [DecidableEq ι] (s : Finset ι) (f : ι → M) {a : ι} (h : a ∈ s) :
    (∏ x ∈ s.erase a, f x) * f a = ∏ x ∈ s, f x := by rw [mul_comm, mul_prod_erase s f h]

/-- If a function applied at a point is 1, a product is unchanged by
removing that point, if present, from a `Finset`. -/
@[to_additive /-- If a function applied at a point is 0, a sum is unchanged by
removing that point, if present, from a `Finset`. -/]
/-
**Finset.prod_erase** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：prod_erase [DecidableEq ι] (s : Finset ι) {f : ι -> M} {a : ι} (h : f a = 
1) : ∏ x in s.erase a, f x = ∏ x in s, f x
参数：s : Finset ι；h : f a = 1。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.sdiff_singleton_eq_erase`：sdiff_singleton_eq_erase (a : α) (s : F
inset α) : s \ {a} = s.erase a
· 使用定理 `Finset.prod_subset`：prod_subset (h : s₁ subseteq s₂) (hf : forall x in s
₂, x ∉ s₁ -> f x = 1) : ∏ x in s₁, f x = ∏ x in s₂, f x
· 使用定理 `Finset.sdiff_subset`：sdiff_subset {s t : Finset α} : s \ t subseteq s
-/
theorem prod_erase [DecidableEq ι] (s : Finset ι) {f : ι → M} {a : ι} (h : f a = 1) :
    ∏ x ∈ s.erase a, f x = ∏ x ∈ s, f x := by
  rw [← sdiff_singleton_eq_erase]
  refine prod_subset sdiff_subset fun x hx hnx => ?_
  grind

@[to_additive]
/-
**Finset.prod_erase_lt_of_one_lt** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：prod_erase_lt_of_one_lt {κ : Type*} [DecidableEq ι] [CommMonoid κ] [LT κ] 
[MulLeftStrictMono κ] {s : Finset ι} {d : ι} (hd : d in s) {f : ι -> κ} (hdf : 1
 < f d) : ∏ m in s.erase d, f m < ∏ m in s, f m
参数：hd : d in s；hdf : 1 < f d。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.insert_erase`：∀ {α : Type u_1} [inst : DecidableEq α] {s : Finset
 α} {a : α}, a ∈ s → insert a (s.erase a) = s
· 使用定理 `Finset.prod_insert`：prod_insert [DecidableEq ι] : a ∉ s -> ∏ x in insert
 a s, f x = f a * ∏ x in s, f x
· 使用定理 `Finset.notMem_erase`：notMem_erase (a : α) (s : Finset α) : a ∉ erase s a
· 使用定理 `lt_mul_of_one_lt_left'`：lt_mul_of_one_lt_left' [MulRightStrictMono α] (a
 : α) {b : α} (h : 1 < b) : a < b * a
-/
theorem prod_erase_lt_of_one_lt {κ : Type*} [DecidableEq ι] [CommMonoid κ] [LT κ]
    [MulLeftStrictMono κ] {s : Finset ι} {d : ι} (hd : d ∈ s) {f : ι → κ}
    (hdf : 1 < f d) : ∏ m ∈ s.erase d, f m < ∏ m ∈ s, f m := by
  conv in ∏ m ∈ s, f m => rw [← Finset.insert_erase hd]
  rw [Finset.prod_insert (Finset.notMem_erase d s)]
  exact lt_mul_of_one_lt_left' _ hdf

/-- If a product is 1 and the function is 1 except possibly at one
point, it is 1 everywhere on the `Finset`. -/
@[to_additive /-- If a sum is 0 and the function is 0 except possibly at one
point, it is 0 everywhere on the `Finset`. -/]
/-
**Finset.eq_one_of_prod_eq_one** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：eq_one_of_prod_eq_one {s : Finset ι} {f : ι -> M} {a : ι} (hp : ∏ x in s, 
f x = 1) (h1 : forall x in s, x != a -> f x = 1) : forall x in s, f x = 1
参数：hp : ∏ x in s, f x = 1；h1 : forall x in s, x != a -> f x = 1。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.prod_singleton`：prod_singleton (f : ι -> M) (a : ι) : ∏ x in sing
leton a, f x = f a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.prod_subset`：prod_subset (h : s₁ subseteq s₂) (hf : forall x in s
₂, x ∉ s₁ -> f x = 1) : ∏ x in s₁, f x = ∏ x in s₂, f x
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Finset.singleton_subset_iff`：singleton_subset_iff {s : Finset α} {a : α}
 : {a} subseteq s ↔ a in s
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Finset.notMem_singleton`：notMem_singleton {a b : α} : a ∉ ({b} : Finset 
α) ↔ a != b
-/
theorem eq_one_of_prod_eq_one {s : Finset ι} {f : ι → M} {a : ι} (hp : ∏ x ∈ s, f x = 1)
    (h1 : ∀ x ∈ s, x ≠ a → f x = 1) : ∀ x ∈ s, f x = 1 := by
  intro x hx
  classical
    by_cases h : x = a
    · rw [h]
      rw [h] at hx
      rw [← prod_subset (singleton_subset_iff.2 hx) fun t ht ha => h1 t ht (notMem_singleton.1 ha),
        prod_singleton] at hp
      exact hp
    · exact h1 x hx h

@[to_additive]
/-
**Finset.prod_mul_eq_prod_mul_of_exists** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
形式化陈述：prod_mul_eq_prod_mul_of_exists {s : Finset ι} {f : ι -> M} {b₁ b₂ : M} (a 
: ι) (ha : a in s) (h : f a * b₁ = f a * b₂) : (∏ a in s, f a) * b₁ = (∏ a in s,
 f a) * b₂
参数：a : ι；ha : a in s；h : f a * b₁ = f a * b₂。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.insert_erase`：∀ {α : Type u_1} [inst : DecidableEq α] {s : Finset
 α} {a : α}, a ∈ s → insert a (s.erase a) = s
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Finset.prod_insert`：prod_insert [DecidableEq ι] : a ∉ s -> ∏ x in insert
 a s, f x = f a * ∏ x in s, f x
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `not_true_eq_false`：(¬True) = False
· 使用定理 `false_and`：∀ (p : Prop), (False ∧ p) = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
-/
lemma prod_mul_eq_prod_mul_of_exists {s : Finset ι} {f : ι → M} {b₁ b₂ : M}
    (a : ι) (ha : a ∈ s) (h : f a * b₁ = f a * b₂) :
    (∏ a ∈ s, f a) * b₁ = (∏ a ∈ s, f a) * b₂ := by
  classical
  rw [← insert_erase ha]
  simp only [mem_erase, ne_eq, not_true_eq_false, false_and, not_false_eq_true, prod_insert]
  rw [mul_assoc, mul_comm, mul_assoc, mul_comm b₁, h, ← mul_assoc, mul_comm _ (f a)]

@[to_additive]
/-
**Finset.prod_biUnion_of_pairwise_eq_one** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：prod_biUnion_of_pairwise_eq_one [DecidableEq ι] {s : Finset κ} {t : κ -> F
inset ι} (hs : (s : Set κ).Pairwise fun i j => forall k in t i inter t j, f k = 
1) : ∏ x in s.biUnion t, f x = ∏ x in s, ∏ i in t x, f i
参数：hs : (s : Set κ).Pairwise fun i j => forall k in t i inter t j, f k = 1。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.prod_filter_ne_one`：prod_filter_ne_one (s : Finset ι) [forall x, 
Decidable (f x != 1)] : ∏ x in s with f x != 1, f x = ∏ x in s, f x
· 使用定理 `Finset.prod_biUnion`：prod_biUnion [DecidableEq ι] {s : Finset κ} {t : κ 
-> Finset ι} (hs : Set.PairwiseDisjoint (↑s) t) : ∏ x in s.biUnion t, f x = ∏ x 
in s, ∏ i…
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Finset.filter_congr`：∀ {α : Type u_1} {p q : α → Prop} [inst : Decidable
Pred p] [inst_1 : DecidablePred q] {s : Finset α},   (∀ x ∈ s, p x ↔ q x) → Fins
et.filter…
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `Finset.prod_congr`：prod_congr (h : s₁ = s₂) : (forall x in s₂, f x = g x
) -> s₁.prod f = s₂.prod g
-/
theorem prod_biUnion_of_pairwise_eq_one [DecidableEq ι] {s : Finset κ} {t : κ → Finset ι}
    (hs : (s : Set κ).Pairwise fun i j ↦ ∀ k ∈ t i ∩ t j, f k = 1) :
    ∏ x ∈ s.biUnion t, f x = ∏ x ∈ s, ∏ i ∈ t x, f i := by
  classical
  let t' k := (t k).filter (fun i ↦ f i ≠ 1)
  have : s.biUnion t' = (s.biUnion t).filter (fun i ↦ f i ≠ 1) := by grind
  rw [← prod_filter_ne_one, ← this, prod_biUnion]
  swap
  · intro i hi j hj hij a hai haj k hk
    have hki : k ∈ t' i := hai hk
    have hkj : k ∈ t' j := haj hk
    simp only [ne_eq, mem_filter, t'] at hki hkj
    exact (hki.2 (hs hi hj hij k (by grind))).elim
  exact Finset.prod_congr rfl (fun i hi ↦ prod_filter_ne_one (t i))

@[to_additive]
/-
**Finset.prod_filter_of_pairwise_eq_one** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
形式化陈述：prod_filter_of_pairwise_eq_one [DecidableEq ι] {f : κ -> ι} {g : ι -> M} {
n : κ} {I : Finset κ} (hn : n in I) (hf : (I : Set κ).Pairwise fun i j => f i = 
f j -> g (f i) = 1) : ∏ j in I with f j = f n, g (f j) = g (f n)
参数：hn : n in I；hf : (I : Set κ).Pairwise fun i j => f i = f j -> g (f i) = 1。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `Finset.prod_eq_one`：prod_eq_one (h : forall x in s, f x = 1) : ∏ x in s,
 f x = 1
· 使用定理 `Finset.mul_prod_erase`：mul_prod_erase [DecidableEq ι] (s : Finset ι) (f 
: ι -> M) {a : ι} (h : a in s) : (f a * ∏ x in s.erase a, f x) = ∏ x in s, f x
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Finset.mem_filter`：∀ {α : Type u_1} {p : α → Prop} [inst : DecidablePred
 p] {s : Finset α} {a : α}, a ∈ Finset.filter p s ↔ a ∈ s ∧ p a
-/
lemma prod_filter_of_pairwise_eq_one [DecidableEq ι] {f : κ → ι} {g : ι → M} {n : κ} {I : Finset κ}
    (hn : n ∈ I) (hf : (I : Set κ).Pairwise fun i j ↦ f i = f j → g (f i) = 1) :
    ∏ j ∈ I with f j = f n, g (f j) = g (f n) := by
  classical
  have h j (hj : j ∈ {i ∈ I | f i = f n}.erase n) : g (f j) = 1 := by
    simp only [mem_erase, mem_filter] at hj
    exact hf hj.2.1 hn hj.1 hj.2.2
  rw [← mul_one (g (f n)), ← prod_eq_one h,
    ← mul_prod_erase {i ∈ I | f i = f n} (fun i ↦ g (f i)) <| mem_filter.mpr ⟨hn, by rfl⟩]

/-- A version of `Finset.prod_map` and `Finset.prod_image`, but we do not assume that `f` is
injective. Rather, we assume that the image of `f` on `I` only overlaps where `g (f i) = 1`.
The conclusion is the same as in `prod_image`. -/
@[to_additive (attr := simp)
/-- A version of `Finset.sum_map` and `Finset.sum_image`, but we do not assume that `f` is
injective. Rather, we assume that the image of `f` on `I` only overlaps where `g (f i) = 0`.
The conclusion is the same as in `sum_image`. -/]
/-
**Finset.prod_image_of_pairwise_eq_one** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
形式化陈述：prod_image_of_pairwise_eq_one [DecidableEq ι] {f : κ -> ι} {g : ι -> M} {I
 : Finset κ} (hf : (I : Set κ).Pairwise fun i j => f i = f j -> g (f i) = 1) : ∏
 s in I.image f, g s = ∏ i in I, g (f i)
参数：hf : (I : Set κ).Pairwise fun i j => f i = f j -> g (f i) = 1。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.prod_image'`：prod_image' [DecidableEq ι] {s : Finset κ} {g : κ ->
 ι} (h : κ -> M) (eq : forall i in s, f (g i) = ∏ j in s with g j = g i, h j) : 
∏ a in s…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `Finset.prod_filter_of_pairwise_eq_one`：prod_filter_of_pairwise_eq_one [D
ecidableEq ι] {f : κ -> ι} {g : ι -> M} {n : κ} {I : Finset κ} (hn : n in I) (hf
 : (I : Set κ).Pairwise fun…
-/
lemma prod_image_of_pairwise_eq_one [DecidableEq ι] {f : κ → ι} {g : ι → M} {I : Finset κ}
    (hf : (I : Set κ).Pairwise fun i j ↦ f i = f j → g (f i) = 1) :
    ∏ s ∈ I.image f, g s = ∏ i ∈ I, g (f i) := by
  rw [prod_image']
  exact fun n hnI => (prod_filter_of_pairwise_eq_one hnI hf).symm

/-- A version of `Finset.prod_map` and `Finset.prod_image`, but we do not assume that `f` is
injective. Rather, we assume that the images of `f` are disjoint on `I`, and `g ⊥ = 1`. The
conclusion is the same as in `prod_image`. -/
@[to_additive (attr := simp)
/-- A version of `Finset.sum_map` and `Finset.sum_image`, but we do not assume that `f` is
injective. Rather, we assume that the images of `f` are disjoint on `I`, and `g ⊥ = 0`. The
conclusion is the same as in `sum_image`. -/]
/-
**Finset.prod_image_of_disjoint** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
形式化陈述：prod_image_of_disjoint [DecidableEq ι] [PartialOrder ι] [OrderBot ι] {f : 
κ -> ι} {g : ι -> M} (hg_bot : g ⊥ = 1) {I : Finset κ} (hf_disj : (I : Set κ).Pa
irwiseDisjoint f) : ∏ s in I.image f, g s = ∏ i in I, g (f i)
参数：hg_bot : g ⊥ = 1；hf_disj : (I : Set κ).PairwiseDisjoint f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Finset.prod_image_of_pairwise_eq_one`：prod_image_of_pairwise_eq_one [Dec
idableEq ι] {f : κ -> ι} {g : ι -> M} {I : Finset κ} (hf : (I : Set κ).Pairwise 
fun i j => f i = f j -> g …
· 使用定理 `Set.Pairwise.imp`：∀ {α : Type u_1} {r p : α → α → Prop} {s : Set α}, s.P
airwise r → (∀ ⦃a b : α⦄, r a b → p a b) → s.Pairwise p
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `disjoint_self`：disjoint_self : Disjoint a a ↔ a = ⊥
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Function.onFun.eq_1`：∀ {α : Sort u₁} {β : Sort u₂} {φ : Sort u₃} (f : β 
→ β → φ) (g : α → β) (x y : α),   Function.onFun f g x y = f (g x) (g y)
-/
lemma prod_image_of_disjoint [DecidableEq ι] [PartialOrder ι] [OrderBot ι] {f : κ → ι} {g : ι → M}
    (hg_bot : g ⊥ = 1) {I : Finset κ} (hf_disj : (I : Set κ).PairwiseDisjoint f) :
    ∏ s ∈ I.image f, g s = ∏ i ∈ I, g (f i) := by
  refine prod_image_of_pairwise_eq_one <| hf_disj.imp fun i j hdisj hfij ↦ ?_
  rw [Function.onFun, ← hfij, disjoint_self] at hdisj
  rw [hdisj, hg_bot]

@[to_additive]
/-
**Finset.prod_unique_nonempty** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：prod_unique_nonempty [Unique ι] (s : Finset ι) (f : ι -> M) (h : s.Nonempt
y) : ∏ x in s, f x = f default
参数：s : Finset ι；f : ι -> M；h : s.Nonempty。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.Nonempty.eq_singleton_default`：∀ {α : Type u_1} [inst : Unique α]
 {s : Finset α}, s.Nonempty → s = {default}
· 使用定理 `Finset.prod_singleton`：prod_singleton (f : ι -> M) (a : ι) : ∏ x in sing
leton a, f x = f a
-/
theorem prod_unique_nonempty [Unique ι] (s : Finset ι) (f : ι → M) (h : s.Nonempty) :
    ∏ x ∈ s, f x = f default := by
  rw [h.eq_singleton_default, Finset.prod_singleton]
/-
**Finset.prod_dvd_prod_of_dvd** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
形式化陈述：prod_dvd_prod_of_dvd (f g : ι -> M) (h : forall i in s, f i ∣ g i) : ∏ i i
n s, f i ∣ ∏ i in s, g i
参数：f g : ι -> M；h : forall i in s, f i ∣ g i。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Multiset.prod_dvd_prod_of_dvd`：prod_dvd_prod_of_dvd [CommMonoid N] {S : 
Multiset M} (g1 g2 : M -> N) (h : forall a in S, g1 a ∣ g2 a) : (Multiset.map g1
 S).prod ∣ (Multise…
-/
lemma prod_dvd_prod_of_dvd (f g : ι → M) (h : ∀ i ∈ s, f i ∣ g i) :
    ∏ i ∈ s, f i ∣ ∏ i ∈ s, g i :=
  Multiset.prod_dvd_prod_of_dvd _ _ h

@[to_additive]
/-
**Finset.prod_map_equiv** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：prod_map_equiv (e : ι ≃ κ) : (s.map e).prod (f ∘ e.symm) = s.prod f
参数：e : ι ≃ κ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.prod_congr`：prod_congr (h : s₁ = s₂) : (forall x in s₂, f x = g x
) -> s₁.prod f = s₂.prod g
· 使用定理 `Finset.prod_map`：prod_map (s : Finset ι) (e : ι ↪ κ) (f : κ -> M) : ∏ x 
in s.map e, f x = ∏ x in s, f (e x)
· 使用定理 `Equiv.symm_apply_apply`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β) (x : α),
 e.symm (e x) = x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem prod_map_equiv (e : ι ≃ κ) : (s.map e).prod (f ∘ e.symm) = s.prod f := by simp

@[to_additive]
/-
**Finset.prod_comp_equiv** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：prod_comp_equiv {f : κ -> M} (e : ι ≃ κ) : s.prod (f ∘ e) = (s.map e).prod
 f
参数：e : ι ≃ κ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.prod_congr`：prod_congr (h : s₁ = s₂) : (forall x in s₂, f x = g x
) -> s₁.prod f = s₂.prod g
· 使用定理 `Finset.prod_map`：prod_map (s : Finset ι) (e : ι ↪ κ) (f : κ -> M) : ∏ x 
in s.map e, f x = ∏ x in s, f (e x)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem prod_comp_equiv {f : κ → M} (e : ι ≃ κ) : s.prod (f ∘ e) = (s.map e).prod f := by simp

end CommMonoid

section CancelCommMonoid
variable [DecidableEq ι] [CancelCommMonoid M] {s t : Finset ι} {f : ι → M}

@[to_additive]
/-
**Finset.prod_sdiff_eq_prod_sdiff_iff** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
形式化陈述：prod_sdiff_eq_prod_sdiff_iff : ∏ i in s \ t, f i = ∏ i in t \ s, f i ↔ ∏ i
 in s, f i = ∏ i in t, f i
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `eq_comm`：∀ {α : Sort u_1} {a b : α}, a = b ↔ b = a
· 使用定理 `eq_iff_eq_of_mul_eq_mul`：∀ {α : Type u_1} [inst : CancelCommMonoid α] {a
 b c d : α}, a * b = c * d → (a = c ↔ b = d)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.prod_union`：prod_union [DecidableEq ι] (h : Disjoint s₁ s₂) : ∏ x
 in s₁ union s₂, f x = (∏ x in s₁, f x) * ∏ x in s₂, f x
· 使用定理 `disjoint_sdiff_self_left`：disjoint_sdiff_self_left : Disjoint (y \ x) x
· 使用定理 `Finset.sdiff_union_self_eq_union`：sdiff_union_self_eq_union : s \ t unio
n t = s union t
· 使用定理 `Finset.union_comm`：union_comm (s₁ s₂ : Finset α) : s₁ union s₂ = s₂ unio
n s₁
-/
lemma prod_sdiff_eq_prod_sdiff_iff :
    ∏ i ∈ s \ t, f i = ∏ i ∈ t \ s, f i ↔ ∏ i ∈ s, f i = ∏ i ∈ t, f i :=
  eq_comm.trans <| eq_iff_eq_of_mul_eq_mul <| by
    rw [← prod_union disjoint_sdiff_self_left, ← prod_union disjoint_sdiff_self_left,
      sdiff_union_self_eq_union, sdiff_union_self_eq_union, union_comm]

@[to_additive]
/-
**Finset.prod_sdiff_ne_prod_sdiff_iff** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
形式化陈述：prod_sdiff_ne_prod_sdiff_iff : ∏ i in s \ t, f i != ∏ i in t \ s, f i ↔ ∏ 
i in s, f i != ∏ i in t, f i
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.not`：∀ {a b : Prop}, (a ↔ b) → (¬a ↔ ¬b)
· 使用引理 `Finset.prod_sdiff_eq_prod_sdiff_iff`：prod_sdiff_eq_prod_sdiff_iff : ∏ i 
in s \ t, f i = ∏ i in t \ s, f i ↔ ∏ i in s, f i = ∏ i in t, f i
-/
lemma prod_sdiff_ne_prod_sdiff_iff :
    ∏ i ∈ s \ t, f i ≠ ∏ i ∈ t \ s, f i ↔ ∏ i ∈ s, f i ≠ ∏ i ∈ t, f i :=
  prod_sdiff_eq_prod_sdiff_iff.not

end CancelCommMonoid

section CommGroup
variable [CommGroup G] [DecidableEq ι] {f : ι → G}

@[to_additive]
/-
**Finset.prod_insert_div** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
形式化陈述：prod_insert_div (ha : a ∉ s) (f : ι -> G) : (∏ x in insert a s, f x) / f a
 = ∏ x in s, f x
参数：ha : a ∉ s；f : ι -> G。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.prod_insert`：prod_insert [DecidableEq ι] : a ∉ s -> ∏ x in insert
 a s, f x = f a * ∏ x in s, f x
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `mul_div_cancel_left`：mul_div_cancel_left (a b : G) : a * b / a = b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma prod_insert_div (ha : a ∉ s) (f : ι → G) :
    (∏ x ∈ insert a s, f x) / f a = ∏ x ∈ s, f x := by simp [ha]

@[to_additive (attr := simp)]
/-
**Finset.prod_erase_eq_div** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：prod_erase_eq_div {a : ι} (h : a in s) : ∏ x in s.erase a, f x = (∏ x in s
, f x) / f a
参数：h : a in s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_div_iff_mul_eq'`：eq_div_iff_mul_eq' : a = b / c ↔ a * c = b
· 使用定理 `Finset.prod_erase_mul`：prod_erase_mul [DecidableEq ι] (s : Finset ι) (f 
: ι -> M) {a : ι} (h : a in s) : (∏ x in s.erase a, f x) * f a = ∏ x in s, f x
-/
theorem prod_erase_eq_div {a : ι} (h : a ∈ s) : ∏ x ∈ s.erase a, f x = (∏ x ∈ s, f x) / f a := by
  rw [eq_div_iff_mul_eq', prod_erase_mul _ _ h]

/-- A telescoping product along `{0, ..., n - 1}` of a commutative-group-valued function reduces to
the ratio of the last and first factors. -/
@[to_additive /-- A telescoping sum along `{0, ..., n - 1}` of a function valued in a commutative
additive group reduces to the difference of the last and first terms. -/]
/-
**Finset.prod_range_div** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
形式化陈述：prod_range_div (f : Nat -> G) (n : Nat) : (∏ i in range n, f (i + 1) / f i
) = f n / f 0
参数：f : Nat -> G；n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.prod_range_induction`：prod_range_induction (f s : Nat -> M) (base
 : s 0 = 1) (n : Nat) (step : forall k < n, s (k + 1) = s k * f k) : ∏ k in Fins
et.range n, f k =…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `div_self'`：div_self' (a : G) : a / a = 1
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `div_mul_div_cancel'`：div_mul_div_cancel' (a b c : G) : a / b * (c / a) =
 c / b
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
lemma prod_range_div (f : ℕ → G) (n : ℕ) : (∏ i ∈ range n, f (i + 1) / f i) = f n / f 0 := by
  apply prod_range_induction <;> simp

/-- A reversed telescoping product along `{0, ..., n - 1}` of a commutative-group-valued function
reduces to the ratio of the first and last factors. -/
@[to_additive /-- A reversed telescoping sum along `{0, ..., n - 1}` of a function valued in a
commutative additive group reduces to the difference of the first and last terms. -/]
/-
**Finset.prod_range_div'** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
形式化陈述：prod_range_div' (f : Nat -> G) (n : Nat) : (∏ i in range n, f i / f (i + 1
)) = f 0 / f n
参数：f : Nat -> G；n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.prod_range_induction`：prod_range_induction (f s : Nat -> M) (base
 : s 0 = 1) (n : Nat) (step : forall k < n, s (k + 1) = s k * f k) : ∏ k in Fins
et.range n, f k =…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `div_self'`：div_self' (a : G) : a / a = 1
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `div_mul_div_cancel`：div_mul_div_cancel (a b c : G) : a / b * (b / c) = a
 / c
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
lemma prod_range_div' (f : ℕ → G) (n : ℕ) : (∏ i ∈ range n, f i / f (i + 1)) = f 0 / f n := by
  apply prod_range_induction <;> simp

/-- Express `f n` as `f 0` multiplied by the telescoping product of consecutive ratios from
`0` to `n - 1`. -/
@[to_additive /-- Express `f n` as `f 0` plus the telescoping sum of consecutive differences from
`0` to `n - 1`. -/]
/-
**Finset.eq_prod_range_div** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
形式化陈述：eq_prod_range_div (f : Nat -> G) (n : Nat) : f n = f 0 * ∏ i in range n, f
 (i + 1) / f i
参数：f : Nat -> G；n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Finset.prod_range_div`：prod_range_div (f : Nat -> G) (n : Nat) : (∏ i in
 range n, f (i + 1) / f i) = f n / f 0
· 使用定理 `mul_div_cancel`：mul_div_cancel (a b : G) : a * (b / a) = b
-/
lemma eq_prod_range_div (f : ℕ → G) (n : ℕ) : f n = f 0 * ∏ i ∈ range n, f (i + 1) / f i := by
  rw [prod_range_div, mul_div_cancel]

@[to_additive]
/-
**Finset.eq_prod_range_div'** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
形式化陈述：eq_prod_range_div' (f : Nat -> G) (n : Nat) : f n = ∏ i in range (n + 1), 
if i = 0 then f 0 else f i / f (i - 1)
参数：f : Nat -> G；n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Finset.eq_prod_range_div`：eq_prod_range_div (f : Nat -> G) (n : Nat) : f
 n = f 0 * ∏ i in range n, f (i + 1) / f i
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Finset.prod_div_distrib`：prod_div_distrib (f g : ι -> G) : ∏ x in s, f x
 / g x = (∏ x in s, f x) / ∏ x in s, g x
· 使用定理 `Finset.prod_range_succ'`：∀ {M : Type u_4} [inst : CommMonoid M] (f : ℕ →
 M) (n : ℕ),   ∏ k ∈ Finset.range (n + 1), f k = (∏ k ∈ Finset.range n, f (k + 1
)) * f 0
· 使用定理 `Finset.prod_congr`：prod_congr (h : s₁ = s₂) : (forall x in s₂, f x = g x
) -> s₁.prod f = s₂.prod g
· 使用定理 `ite_cond_eq_false`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α)
, c = False → (if c then a else b) = b
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `and_false`：∀ (p : Prop), (p ∧ False) = False
· 使用定理 `ite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α),
 c = True → (if c then a else b) = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
-/
lemma eq_prod_range_div' (f : ℕ → G) (n : ℕ) :
    f n = ∏ i ∈ range (n + 1), if i = 0 then f 0 else f i / f (i - 1) := by
  conv_lhs => rw [Finset.eq_prod_range_div f]
  simp [Finset.prod_range_succ', mul_comm]

@[to_additive]
/-
**Finset.prod_range_add_div_prod_range** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
形式化陈述：prod_range_add_div_prod_range (f : Nat -> G) (n m : Nat) : (∏ k in range (
n + m), f k) / ∏ k in range n, f k = ∏ k in Finset.range m, f (n + k)
参数：f : Nat -> G；n m : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `div_eq_of_eq_mul'`：div_eq_of_eq_mul' {a b c : G} (h : a = b * c) : a / b
 = c
· 使用定理 `Finset.prod_range_add`：prod_range_add (f : Nat -> M) (n m : Nat) : (∏ x 
in range (n + m), f x) = (∏ x in range n, f x) * ∏ x in range m, f (n + x)
-/
lemma prod_range_add_div_prod_range (f : ℕ → G) (n m : ℕ) :
    (∏ k ∈ range (n + m), f k) / ∏ k ∈ range n, f k = ∏ k ∈ Finset.range m, f (n + k) :=
  div_eq_of_eq_mul' (prod_range_add f n m)

@[to_additive (attr := simp)]
/-
**Finset.prod_sdiff_eq_div** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
形式化陈述：prod_sdiff_eq_div (h : s₁ subseteq s₂) : ∏ x in s₂ \ s₁, f x = (∏ x in s₂,
 f x) / ∏ x in s₁, f x
参数：h : s₁ subseteq s₂。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_div_iff_mul_eq'`：eq_div_iff_mul_eq' : a = b / c ↔ a * c = b
· 使用定理 `Finset.prod_sdiff`：prod_sdiff [DecidableEq ι] (h : s₁ subseteq s₂) : (∏ 
x in s₂ \ s₁, f x) * ∏ x in s₁, f x = ∏ x in s₂, f x
-/
lemma prod_sdiff_eq_div (h : s₁ ⊆ s₂) : ∏ x ∈ s₂ \ s₁, f x = (∏ x ∈ s₂, f x) / ∏ x ∈ s₁, f x := by
  rw [eq_div_iff_mul_eq', prod_sdiff h]

@[to_additive]
/-
**Finset.prod_sdiff_div_prod_sdiff** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：prod_sdiff_div_prod_sdiff : (∏ x in s₂ \ s₁, f x) / ∏ x in s₁ \ s₂, f x = 
(∏ x in s₂, f x) / ∏ x in s₁, f x
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.prod_sdiff`：prod_sdiff [DecidableEq ι] (h : s₁ subseteq s₂) : (∏ 
x in s₂ \ s₁, f x) * ∏ x in s₁, f x = ∏ x in s₂, f x
· 使用定理 `inf_le_right`：∀ {α : Type u} [inst : SemilatticeInf α] {a b : α}, a ⊓ b 
≤ b
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Finset.prod_congr`：prod_congr (h : s₁ = s₂) : (forall x in s₂, f x = g x
) -> s₁.prod f = s₂.prod g
· 使用定理 `Finset.sdiff_inter_self_right`：sdiff_inter_self_right (s t : Finset α) :
 s \ (t inter s) = s \ t
· 使用定理 `inf_le_left`：∀ {α : Type u} [inst : SemilatticeInf α] {a b : α}, a ⊓ b ≤
 a
· 使用定理 `Finset.sdiff_inter_self_left`：sdiff_inter_self_left (s t : Finset α) : s
 \ (s inter t) = s \ t
· 使用定理 `mul_div_mul_right_eq_div`：mul_div_mul_right_eq_div (a b c : G) : a * c /
 (b * c) = a / b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem prod_sdiff_div_prod_sdiff :
    (∏ x ∈ s₂ \ s₁, f x) / ∏ x ∈ s₁ \ s₂, f x = (∏ x ∈ s₂, f x) / ∏ x ∈ s₁, f x := by
  simp [← Finset.prod_sdiff (@inf_le_left _ _ s₁ s₂), ← Finset.prod_sdiff (@inf_le_right _ _ s₁ s₂)]

end CommGroup

section OrderedSub
variable [AddCommMonoid M] [PartialOrder M] [Sub M] [OrderedSub M] [AddLeftMono M]
  [AddLeftReflectLE M] [ExistsAddOfLE M]

/-- A telescoping sum along `{0, ..., n-1}` of an `ℕ`-valued function reduces to the difference of
the last and first terms when the function we are summing is monotone. -/
/-
**Finset.sum_range_tsub** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
形式化陈述：sum_range_tsub {f : Nat -> M} (h : Monotone f) (n : Nat) : ∑ i in range n,
 (f (i + 1) - f i) = f n - f 0
参数：h : Monotone f；n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.sum_range_induction`：∀ {M : Type u_4} [inst : AddCommMonoid M] (f
 s : ℕ → M),   s 0 = 0 → ∀ (n : ℕ), (∀ k < n, s (k + 1) = s k + f k) → ∑ k ∈ Fin
set.range n, f k…
· 使用定理 `tsub_eq_of_eq_add`：tsub_eq_of_eq_add (h : a = c + b) : a - b = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `Nat.le_succ`：∀ (n : ℕ), n ≤ n.succ
· 使用定理 `Nat.zero_le`：∀ (n : ℕ), 0 ≤ n
· 使用定理 `tsub_add_eq_add_tsub`：tsub_add_eq_add_tsub (h : b <= a) : a - b + c = a 
+ c - b
· 使用定理 `add_tsub_cancel_of_le`：add_tsub_cancel_of_le (h : a <= b) : a + (b - a) 
= b

--- 原说明 ---
A telescoping sum along `{0, ..., n-1}` of an `ℕ`-valued function reduces to the
 difference of
the last and first terms when the function we are summing is monotone.
-/
lemma sum_range_tsub {f : ℕ → M} (h : Monotone f) (n : ℕ) :
    ∑ i ∈ range n, (f (i + 1) - f i) = f n - f 0 := by
  apply sum_range_induction
  case base => apply tsub_eq_of_eq_add; rw [zero_add]
  case step =>
    intro n _
    have h₁ : f n ≤ f (n + 1) := h (Nat.le_succ _)
    have h₂ : f 0 ≤ f n := h (Nat.zero_le _)
    rw [tsub_add_eq_add_tsub h₂, add_tsub_cancel_of_le h₁]
/-
**Finset.sum_tsub_distrib** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
形式化陈述：sum_tsub_distrib (s : Finset ι) {f g : ι -> M} (hfg : forall x in s, g x <
= f x) : ∑ x in s, (f x - g x) = ∑ x in s, f x - ∑ x in s, g x
参数：s : Finset ι；hfg : forall x in s, g x <= f x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Multiset.sum_map_tsub`：sum_map_tsub [AddCommMonoid M] [PartialOrder M] [
ExistsAddOfLE M] [AddLeftMono M] [AddLeftReflectLE M] [Sub M] [OrderedSub M] (l 
: Multiset …
-/
lemma sum_tsub_distrib (s : Finset ι) {f g : ι → M} (hfg : ∀ x ∈ s, g x ≤ f x) :
    ∑ x ∈ s, (f x - g x) = ∑ x ∈ s, f x - ∑ x ∈ s, g x := Multiset.sum_map_tsub _ hfg

end OrderedSub

section Nat

/-
**Finset.card_eq_sum_ones** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
形式化陈述：card_eq_sum_ones (s : Finset ι) : #s = ∑ _ in s, 1
参数：s : Finset ι。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.sum_const`：∀ {ι : Type u_1} {M : Type u_4} {s : Finset ι} [inst :
 AddCommMonoid M] (b : M), ∑ _x ∈ s, b = s.card • b
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma card_eq_sum_ones (s : Finset ι) : #s = ∑ _ ∈ s, 1 := by simp
/-
**Finset.sum_const_nat** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：sum_const_nat {m : Nat} {f : ι -> Nat} (h₁ : forall x in s, f x = m) : ∑ x
 in s, f x = #s * m
参数：h₁ : forall x in s, f x = m。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.nsmul_eq_mul`：∀ (m n : ℕ), m • n = m * n
· 使用定理 `Finset.sum_const`：∀ {ι : Type u_1} {M : Type u_4} {s : Finset ι} [inst :
 AddCommMonoid M] (b : M), ∑ _x ∈ s, b = s.card • b
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
-/
theorem sum_const_nat {m : ℕ} {f : ι → ℕ} (h₁ : ∀ x ∈ s, f x = m) : ∑ x ∈ s, f x = #s * m := by
  rw [← Nat.nsmul_eq_mul, ← sum_const]
  apply sum_congr rfl h₁
/-
**Finset.sum_card_fiberwise_eq_card_filter** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
形式化陈述：sum_card_fiberwise_eq_card_filter {κ : Type*} [DecidableEq κ] (s : Finset 
ι) (t : Finset κ) (g : ι -> κ) : ∑ j in t, #{i in s | g i = j} = #{i in s | g i 
in t}
参数：s : Finset ι；t : Finset κ；g : ι -> κ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用引理 `Finset.card_eq_sum_ones`：card_eq_sum_ones (s : Finset ι) : #s = ∑ _ in s
, 1
· 使用定理 `Finset.sum_fiberwise_eq_sum_filter`：∀ {ι : Type u_1} {κ : Type u_2} {M :
 Type u_4} [inst : AddCommMonoid M] [inst_1 : DecidableEq κ] (s : Finset ι)   (t
 : Finset κ) (g : ι → κ)…
-/
lemma sum_card_fiberwise_eq_card_filter {κ : Type*} [DecidableEq κ] (s : Finset ι) (t : Finset κ)
    (g : ι → κ) : ∑ j ∈ t, #{i ∈ s | g i = j} = #{i ∈ s | g i ∈ t} := by
  simpa only [card_eq_sum_ones] using sum_fiberwise_eq_sum_filter _ _ _ _

@[simp]
/-
**Finset.card_disjiUnion** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：card_disjiUnion (s : Finset ι) (t : ι -> Finset M) (h) : #(s.disjiUnion t 
h) = ∑ a in s, #(t a)
参数：s : Finset ι；t : ι -> Finset M；h。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Multiset.card_bind`：card_bind : card (s.bind f) = (s.map (card ∘ f)).sum
-/
theorem card_disjiUnion (s : Finset ι) (t : ι → Finset M) (h) :
    #(s.disjiUnion t h) = ∑ a ∈ s, #(t a) :=
  Multiset.card_bind _ _
/-
**Finset.card_biUnion** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：card_biUnion [DecidableEq M] {t : ι -> Finset M} (h : (s : Set ι).Pairwise
Disjoint t) : #(s.biUnion t) = ∑ u in s, #(t u)
参数：h : (s : Set ι).PairwiseDisjoint t。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `Finset.sum_const`：∀ {ι : Type u_1} {M : Type u_4} {s : Finset ι} [inst :
 AddCommMonoid M] (b : M), ∑ _x ∈ s, b = s.card • b
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `Finset.sum_biUnion`：∀ {ι : Type u_1} {κ : Type u_2} {M : Type u_4} [inst
 : AddCommMonoid M] {f : ι → M} [inst_1 : DecidableEq ι]   {s : Finset κ} {t : κ
 → Finse…
-/
theorem card_biUnion [DecidableEq M] {t : ι → Finset M} (h : (s : Set ι).PairwiseDisjoint t) :
    #(s.biUnion t) = ∑ u ∈ s, #(t u) := by simpa using sum_biUnion h (M := ℕ) (f := 1)
/-
**Finset.card_biUnion_le** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：card_biUnion_le [DecidableEq M] {s : Finset ι} {t : ι -> Finset M} : #(s.b
iUnion t) <= ∑ a in s, #(t a)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.induction_on`：∀ {α : Type u_3} {motive : Finset α → Prop} [inst :
 DecidableEq α] (s : Finset α),   motive ∅ → (∀ (a : α) (s : Finset α), a ∉ s → 
motive s …
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Finset.biUnion_insert`：biUnion_insert [DecidableEq α] {a : α} : (insert 
a s).biUnion t = t a union s.biUnion t
· 使用定理 `Finset.card_union_le`：card_union_le (s t : Finset α) : #(s union t) <= #
s + #t
-/
theorem card_biUnion_le [DecidableEq M] {s : Finset ι} {t : ι → Finset M} :
    #(s.biUnion t) ≤ ∑ a ∈ s, #(t a) :=
  haveI := Classical.decEq ι
  Finset.induction_on s (by simp) fun a s has ih =>
    calc
      #((insert a s).biUnion t) ≤ #(t a) + #(s.biUnion t) := by
        rw [biUnion_insert]; exact card_union_le ..
      _ ≤ ∑ a ∈ insert a s, #(t a) := by grind
/-
**Finset.card_eq_sum_card_fiberwise** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：card_eq_sum_card_fiberwise [DecidableEq M] {f : ι -> M} {s : Finset ι} {t 
: Finset M} (H : (s : Set ι).MapsTo f t) : #s = ∑ b in t, #{a in s | f a = b}
参数：H : (s : Set ι).MapsTo f t。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Finset.card_eq_sum_ones`：card_eq_sum_ones (s : Finset ι) : #s = ∑ _ in s
, 1
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `Finset.sum_fiberwise_of_maps_to`：∀ {ι : Type u_1} {κ : Type u_2} {M : Ty
pe u_4} [inst : AddCommMonoid M] {s : Finset ι} {t : Finset κ}   [inst_1 : Decid
ableEq κ] {g : ι → κ}…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem card_eq_sum_card_fiberwise [DecidableEq M] {f : ι → M} {s : Finset ι} {t : Finset M}
    (H : (s : Set ι).MapsTo f t) : #s = ∑ b ∈ t, #{a ∈ s | f a = b} := by
  simp only [card_eq_sum_ones, sum_fiberwise_of_maps_to H]
/-
**Finset.card_eq_sum_card_image** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：card_eq_sum_card_image [DecidableEq M] (f : ι -> M) (s : Finset ι) : #s = 
∑ b in s.image f, #{a in s | f a = b}
参数：f : ι -> M；s : Finset ι。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.card_eq_sum_card_fiberwise`：card_eq_sum_card_fiberwise [Decidable
Eq M] {f : ι -> M} {s : Finset ι} {t : Finset M} (H : (s : Set ι).MapsTo f t) : 
#s = ∑ b in t, #{a in s…
· 使用定理 `Finset.mem_image_of_mem`：mem_image_of_mem (f : α -> β) {a} (h : a in s) 
: f a in s.image f
-/
theorem card_eq_sum_card_image [DecidableEq M] (f : ι → M) (s : Finset ι) :
    #s = ∑ b ∈ s.image f, #{a ∈ s | f a = b} :=
  card_eq_sum_card_fiberwise fun _ => mem_image_of_mem _

end Nat
end Finset

namespace Fintype
variable {ι κ ι : Type*} [Fintype ι] [Fintype κ]

open Finset

section CommMonoid
variable [CommMonoid M]

@[to_additive]
/-
**Fintype.prod_of_injective** 是 Mathlib 中的一个引理，位于命名空间 `Fintype`。
形式化陈述：prod_of_injective (e : ι -> κ) (he : Injective e) (f : ι -> M) (g : κ -> M
) (h' : forall i ∉ Set.range e, g i = 1) (h : forall i, f i = g (e i)) : ∏ i, f 
i = ∏ j, g j
参数：e : ι -> κ；he : Injective e；f : ι -> M；g : κ -> M；h' : forall i ∉ Set.range e
, g i = 1；h : forall i, f i = g (e i)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Finset.prod_of_injOn`：prod_of_injOn (e : ι -> κ) (he : Set.InjOn e s) (h
est : Set.MapsTo e s t) (h' : forall i in t, i ∉ e '' s -> g i = 1) (h : forall 
i in s, f …
· 使用定理 `Function.Injective.injOn`：∀ {α : Type u_1} {β : Type u_2} {f : α → β}, F
unction.Injective f → ∀ {s : Set α}, Set.InjOn f s
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.coe_univ`：coe_univ : ↑(univ : Finset α) = (Set.univ : Set α)
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Set.image_univ`：image_univ {f : α -> β} : f '' univ = range f
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
-/
lemma prod_of_injective (e : ι → κ) (he : Injective e) (f : ι → M) (g : κ → M)
    (h' : ∀ i ∉ Set.range e, g i = 1) (h : ∀ i, f i = g (e i)) : ∏ i, f i = ∏ j, g j :=
  prod_of_injOn e he.injOn (by simp) (by simpa using h') (fun i _ ↦ h i)

@[to_additive]
/-
**Fintype.prod_fiberwise** 是 Mathlib 中的一个引理，位于命名空间 `Fintype`。
形式化陈述：prod_fiberwise [DecidableEq κ] (g : ι -> κ) (f : ι -> M) : ∏ j, ∏ i : {i /
/ g i = j}, f i = ∏ i, f i
参数：g : ι -> κ；f : ι -> M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `Finset.prod_fiberwise`：prod_fiberwise (s : Finset ι) (g : ι -> κ) (f : ι
 -> M) : ∏ j, ∏ i in s with g i = j, f i = ∏ i in s, f i
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Finset.prod_subtype`：prod_subtype {p : ι -> Prop} {F : Fintype (Subtype 
p)} (s : Finset ι) (h : forall x, x in s ↔ p x) (f : ι -> M) : ∏ a in s, f a = ∏
 a : Subt…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
lemma prod_fiberwise [DecidableEq κ] (g : ι → κ) (f : ι → M) :
    ∏ j, ∏ i : {i // g i = j}, f i = ∏ i, f i := by
  rw [← Finset.prod_fiberwise _ g f]
  congr with j
  exact (prod_subtype _ (by simp) _).symm

@[to_additive]
/-
**Fintype.prod_fiberwise'** 是 Mathlib 中的一个引理，位于命名空间 `Fintype`。
形式化陈述：prod_fiberwise' [DecidableEq κ] (g : ι -> κ) (f : κ -> M) : ∏ j, ∏ _i : {i
 // g i = j}, f j = ∏ i, f (g i)
参数：g : ι -> κ；f : κ -> M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `Finset.prod_fiberwise'`：prod_fiberwise' (s : Finset ι) (g : ι -> κ) (f :
 κ -> M) : ∏ j, ∏ i in s with g i = j, f j = ∏ i in s, f (g i)
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Finset.prod_subtype`：prod_subtype {p : ι -> Prop} {F : Fintype (Subtype 
p)} (s : Finset ι) (h : forall x, x in s ↔ p x) (f : ι -> M) : ∏ a in s, f a = ∏
 a : Subt…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
lemma prod_fiberwise' [DecidableEq κ] (g : ι → κ) (f : κ → M) :
    ∏ j, ∏ _i : {i // g i = j}, f j = ∏ i, f (g i) := by
  rw [← Finset.prod_fiberwise' _ g f]
  congr with j
  exact (prod_subtype _ (by simp) fun _ ↦ _).symm

@[to_additive]
/-
**Fintype.prod_unique** 是 Mathlib 中的一个定理，位于命名空间 `Fintype`。
形式化陈述：prod_unique [Unique ι] (f : ι -> M) : ∏ x : ι, f x = f default
参数：f : ι -> M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.univ_unique`：univ_unique [Unique α] : (univ : Finset α) = {defaul
t}
· 使用定理 `Finset.prod_singleton`：prod_singleton (f : ι -> M) (a : ι) : ∏ x in sing
leton a, f x = f a
-/
theorem prod_unique [Unique ι] (f : ι → M) : ∏ x : ι, f x = f default := by
  rw [univ_unique, prod_singleton]

@[to_additive]
/-
**Fintype.prod_subsingleton** 是 Mathlib 中的一个定理，位于命名空间 `Fintype`。
形式化陈述：prod_subsingleton [Subsingleton ι] (f : ι -> M) (a : ι) : ∏ x : ι, f x = f
 a
参数：f : ι -> M；a : ι。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Fintype.prod_unique`：prod_unique [Unique ι] (f : ι -> M) : ∏ x : ι, f x 
= f default
· 使用定理 `Subsingleton.elim`：∀ {α : Sort u} [h : Subsingleton α] (a b : α), a = b
-/
theorem prod_subsingleton [Subsingleton ι] (f : ι → M) (a : ι) : ∏ x : ι, f x = f a := by
  have : Unique ι := uniqueOfSubsingleton a
  rw [prod_unique f, Subsingleton.elim default a]
/-
**Fintype.prod_Prop** 是 Mathlib 中的一个定理，位于命名空间 `Fintype`。
形式化陈述：∀ {M : Type u_4} [inst : CommMonoid M] (f : Prop → M), ∏ p, f p = f True *
 f False
参数：f : Prop → M。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.prod_congr`：prod_congr (h : s₁ = s₂) : (forall x in s₂, f x = g x
) -> s₁.prod f = s₂.prod g
· 使用定理 `Fintype.univ_Prop`：Fintype.univ_Prop : (Finset.univ : Finset Prop) = {Tr
ue, False}
· 使用定理 `Finset.prod_insert`：prod_insert [DecidableEq ι] : a ∉ s -> ∏ x in insert
 a s, f x = f a * ∏ x in s, f x
· 使用定理 `iff_false`：∀ (p : Prop), (p ↔ False) = ¬p
· 使用定理 `not_true_eq_false`：(¬True) = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `Finset.prod_singleton`：prod_singleton (f : ι -> M) (a : ι) : ∏ x in sing
leton a, f x = f a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
@[to_additive] theorem prod_Prop (f : Prop → M) : ∏ p, f p = f True * f False := by simp

@[to_additive]
/-
**Fintype.prod_subtype_mul_prod_subtype** 是 Mathlib 中的一个定理，位于命名空间 `Fintype`。
形式化陈述：prod_subtype_mul_prod_subtype (p : ι -> Prop) (f : ι -> M) [DecidablePred 
p] : (∏ i : { x // p x }, f i) * ∏ i : { x // ¬p x }, f i = ∏ i, f i
参数：p : ι -> Prop；f : ι -> M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.prod_subtype`：prod_subtype {p : ι -> Prop} {F : Fintype (Subtype 
p)} (s : Finset ι) (h : forall x, x in s ↔ p x) (f : ι -> M) : ∏ a in s, f a = ∏
 a : Subt…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Set.toFinset_ofPred`：toFinset_ofPred [Fintype α] (p : α -> Prop) [Decida
blePred p] [Fintype { x | p x }] : Set.toFinset {x | p x} = Finset.univ.filter p
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `Finset.compl_filter`：compl_filter (p : α -> Prop) [DecidablePred p] [for
all x, Decidable ¬p x] : (univ.filter p)ᶜ = univ.filter fun x => ¬p x
· 使用引理 `Finset.prod_mul_prod_compl`：prod_mul_prod_compl [Fintype ι] [DecidableEq
 ι] (s : Finset ι) (f : ι -> M) : (∏ i in s, f i) * ∏ i in sᶜ, f i = ∏ i, f i
-/
theorem prod_subtype_mul_prod_subtype (p : ι → Prop) (f : ι → M) [DecidablePred p] :
    (∏ i : { x // p x }, f i) * ∏ i : { x // ¬p x }, f i = ∏ i, f i := by
  classical
    let s := { x | p x }.toFinset
    rw [← Finset.prod_subtype s, ← Finset.prod_subtype sᶜ]
    · exact Finset.prod_mul_prod_compl _ _
    · simp [s]
    · simp [s]
/-
**Fintype.prod_subset** 是 Mathlib 中的一个定理，位于命名空间 `Fintype`。
形式化陈述：∀ {M : Type u_4} {ι : Type u_7} [inst : Fintype ι] [inst_1 : CommMonoid M]
 {s : Finset ι} {f : ι → M},   (∀ (i : ι), f i ≠ 1 → i ∈ s) → ∏ i ∈ s, f i = ∏ i
, f i
参数：∀ (i : ι), f i ≠ 1 → i ∈ s。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.prod_subset`：prod_subset (h : s₁ subseteq s₂) (hf : forall x in s
₂, x ∉ s₁ -> f x = 1) : ∏ x in s₁, f x = ∏ x in s₂, f x
· 使用定理 `Finset.subset_univ`：subset_univ (s : Finset α) : s subseteq univ
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `not_imp_comm`：not_imp_comm : ¬a -> b ↔ ¬b -> a
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
-/
@[to_additive] lemma prod_subset {s : Finset ι} {f : ι → M} (h : ∀ i, f i ≠ 1 → i ∈ s) :
    ∏ i ∈ s, f i = ∏ i, f i :=
  Finset.prod_subset s.subset_univ <| by simpa [not_imp_comm (a := _ ∈ s)]

end CommMonoid
end Fintype

namespace List

@[to_additive]
/-
**List.prod_toFinset** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：prod_toFinset {M : Type*} [DecidableEq ι] [CommMonoid M] (f : ι -> M) : fo
rall {l : List ι} (_hl : l.Nodup), l.toFinset.prod f = (l.map f).prod | [], _ =>
 by simp | a :: l, hl => by let ⟨notMem, hl⟩
参数：f : ι -> M。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem prod_toFinset {M : Type*} [DecidableEq ι] [CommMonoid M] (f : ι → M) :
    ∀ {l : List ι} (_hl : l.Nodup), l.toFinset.prod f = (l.map f).prod
  | [], _ => by simp
  | a :: l, hl => by
    let ⟨notMem, hl⟩ := List.nodup_cons.mp hl
    simp [Finset.prod_insert (mt List.mem_toFinset.mp notMem), prod_toFinset _ hl]

@[simp]
/-
**List.sum_toFinset_count_eq_length** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：sum_toFinset_count_eq_length [DecidableEq ι] (l : List ι) : ∑ a in l.toFin
set, l.count a = l.length
参数：l : List ι。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `List.map_const'`：∀ {α : Type u_1} {β : Type u_2} {l : List α} {b : β}, L
ist.map (fun x => b) l = List.replicate l.length b
· 使用定理 `List.sum_replicate`：∀ {M : Type u_2} [inst : AddMonoid M] (n : ℕ) (a : M
), (List.replicate n a).sum = n • a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.sum_list_map_count`：∀ {ι : Type u_1} {M : Type u_4} [inst : AddCo
mmMonoid M] [inst_1 : DecidableEq ι] (l : List ι) (f : ι → M),   (List.map f l).
sum = ∑ m ∈ l.t…
-/
theorem sum_toFinset_count_eq_length [DecidableEq ι] (l : List ι) :
    ∑ a ∈ l.toFinset, l.count a = l.length := by
  simpa [List.map_const'] using (Finset.sum_list_map_count l fun _ => (1 : ℕ)).symm

end List

namespace Multiset

@[simp]
/-
**Multiset.mem_sum** 是 Mathlib 中的一个引理，位于命名空间 `Multiset`。
形式化陈述：mem_sum {a : M} {s : Finset ι} {m : ι -> Multiset M} : a in ∑ i in s, m i 
↔ exists i in s, a in m i
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.cons_induction`：∀ {α : Type u_3} {motive : Finset α → Prop},   mo
tive ∅ → (∀ (a : α) (s : Finset α) (h : a ∉ s), motive s → motive (Finset.cons a
 s h)) → ∀ …
-/
lemma mem_sum {a : M} {s : Finset ι} {m : ι → Multiset M} :
    a ∈ ∑ i ∈ s, m i ↔ ∃ i ∈ s, a ∈ m i := by
  induction s using Finset.cons_induction with grind

@[to_additive]
/-
**Multiset.prod_map_prod** 是 Mathlib 中的一个引理，位于命名空间 `Multiset`。
形式化陈述：prod_map_prod {α : Type*} [CommMonoid M] {m : Multiset ι} {s : Finset α} {
f : ι -> α -> M} : (m.map fun i => ∏ a in s, f i a).prod = ∏ a in s, (m.map fun 
i => f i a).prod
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.induction`：∀ {α : Type u_3} {motive : Finset α → Prop} [inst : De
cidableEq α],   motive ∅ → (∀ (a : α) (s : Finset α), a ∉ s → motive s → motive 
(inser…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Multiset.map_const'`：∀ {α : Type u_1} {β : Type v} (s : Multiset α) (b :
 β), Multiset.map (fun x => b) s = Multiset.replicate s.card b
· 使用定理 `Multiset.prod_replicate`：prod_replicate (n : Nat) (a : M) : (replicate n
 a).prod = a ^ n
· 使用定理 `one_pow`：one_pow {a : R} (b : Nat) (ha : IsNat a 1) : a ^ b = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Multiset.map_congr`：map_congr {f g : α -> β} {s t : Multiset α} : s = t 
-> (forall x in t, f x = g x) -> map f s = map g t
· 使用定理 `Finset.prod_insert`：prod_insert [DecidableEq ι] : a ∉ s -> ∏ x in insert
 a s, f x = f a * ∏ x in s, f x
· 使用定理 `Multiset.prod_map_mul`：prod_map_mul : (m.map fun i => f i * g i).prod = 
(m.map f).prod * (m.map g).prod
-/
lemma prod_map_prod {α : Type*} [CommMonoid M] {m : Multiset ι} {s : Finset α} {f : ι → α → M} :
    (m.map fun i ↦ ∏ a ∈ s, f i a).prod = ∏ a ∈ s, (m.map fun i ↦ f i a).prod := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | insert a s ha ih => simp [Finset.prod_insert ha, prod_map_mul, ih]

variable [DecidableEq ι]
/-
**Multiset.toFinset_sum_count_eq** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：toFinset_sum_count_eq (s : Multiset ι) : ∑ a in s.toFinset, s.count a = ca
rd s
参数：s : Multiset ι。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Multiset.map_const'`：∀ {α : Type u_1} {β : Type v} (s : Multiset α) (b :
 β), Multiset.map (fun x => b) s = Multiset.replicate s.card b
· 使用定理 `Multiset.sum_replicate`：∀ {M : Type u_3} [inst : AddCommMonoid M] (n : ℕ
) (a : M), (Multiset.replicate n a).sum = n • a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.sum_multiset_map_count`：∀ {ι : Type u_1} [inst : DecidableEq ι] (
s : Multiset ι) {M : Type u_5} [inst_1 : AddCommMonoid M] (f : ι → M),   (Multis
et.map f s).sum = ∑…
-/
theorem toFinset_sum_count_eq (s : Multiset ι) : ∑ a ∈ s.toFinset, s.count a = card s := by
  simpa using (Finset.sum_multiset_map_count s (fun _ => (1 : ℕ))).symm
/-
**Multiset.sum_count_eq_card** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：∀ {ι : Type u_1} [inst : DecidableEq ι] {s : Finset ι} {m : Multiset ι},  
 (∀ a ∈ m, a ∈ s) → ∑ a ∈ s, Multiset.count a m = m.card
参数：∀ a ∈ m, a ∈ s。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Multiset.toFinset_sum_count_eq`：toFinset_sum_count_eq (s : Multiset ι) :
 ∑ a in s.toFinset, s.count a = card s
· 使用定理 `Finset.sum_filter_ne_zero`：∀ {ι : Type u_1} {M : Type u_4} [inst : AddCo
mmMonoid M] {f : ι → M} (s : Finset ι)   [inst_1 : (x : ι) → Decidable (f x ≠ 0)
], ∑ x ∈ s with…
· 使用定理 `Finset.ext`：ext {s₁ s₂ : Finset α} (h : forall a, a in s₁ ↔ a in s₂) : s
₁ = s₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Finset.filter_congr`：∀ {α : Type u_1} {p q : α → Prop} [inst : Decidable
Pred p] [inst_1 : DecidablePred q] {s : Finset α},   (∀ x ∈ s, p x ↔ q x) → Fins
et.filter…
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
-/
@[simp] lemma sum_count_eq_card {s : Finset ι} {m : Multiset ι} (hms : ∀ a ∈ m, a ∈ s) :
    ∑ a ∈ s, m.count a = card m := by
  rw [← toFinset_sum_count_eq, ← Finset.sum_filter_ne_zero]
  congr with a
  simpa using hms a

@[simp]
/-
**Multiset.toFinset_sum_count_nsmul_eq** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：toFinset_sum_count_nsmul_eq (s : Multiset ι) : ∑ a in s.toFinset, s.count 
a • {a} = s
参数：s : Multiset ι。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.sum_multiset_map_count`：∀ {ι : Type u_1} [inst : DecidableEq ι] (
s : Multiset ι) {M : Type u_5} [inst_1 : AddCommMonoid M] (f : ι → M),   (Multis
et.map f s).sum = ∑…
· 使用定理 `Multiset.sum_map_singleton`：sum_map_singleton (s : Multiset M) : (s.map 
fun a => ({a} : Multiset M)).sum = s
-/
theorem toFinset_sum_count_nsmul_eq (s : Multiset ι) :
    ∑ a ∈ s.toFinset, s.count a • {a} = s := by
  rw [← Finset.sum_multiset_map_count, Multiset.sum_map_singleton]
/-
**Multiset.exists_smul_of_dvd_count** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：exists_smul_of_dvd_count (s : Multiset ι) {k : Nat} (h : forall a : ι, a i
n s -> k ∣ Multiset.count a s) : exists u : Multiset ι, s = k • u
参数：s : Multiset ι；h : forall a : ι, a in s -> k ∣ Multiset.count a s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `mul_nsmul'`：∀ {M : Type u_2} [inst : AddMonoid M] (a : M) (m n : ℕ), (m 
* n) • a = m • n • a
· 使用定理 `Nat.mul_div_cancel'`：∀ {n m : ℕ}, n ∣ m → n * (m / n) = m
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Multiset.mem_toFinset`：mem_toFinset {a : α} {s : Multiset α} : a in s.to
Finset ↔ a in s
· 使用定理 `Finset.sum_nsmul`：∀ {ι : Type u_1} {M : Type u_3} [inst : AddCommMonoid 
M] (s : Finset ι) (n : ℕ) (f : ι → M),   ∑ x ∈ s, n • f x = n • ∑ x ∈ s, f x
· 使用定理 `Multiset.toFinset_sum_count_nsmul_eq`：toFinset_sum_count_nsmul_eq (s : M
ultiset ι) : ∑ a in s.toFinset, s.count a • {a} = s
-/
theorem exists_smul_of_dvd_count (s : Multiset ι) {k : ℕ}
    (h : ∀ a : ι, a ∈ s → k ∣ Multiset.count a s) : ∃ u : Multiset ι, s = k • u := by
  use ∑ a ∈ s.toFinset, (s.count a / k) • {a}
  have h₂ :
    (∑ x ∈ s.toFinset, k • (count x s / k) • ({x} : Multiset ι)) =
      ∑ x ∈ s.toFinset, count x s • {x} := by
    apply Finset.sum_congr rfl
    intro x hx
    rw [← mul_nsmul', Nat.mul_div_cancel' (h x (mem_toFinset.mp hx))]
  rw [← Finset.sum_nsmul, h₂, toFinset_sum_count_nsmul_eq]

@[to_additive]
/-
**Multiset.prod_sum** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：prod_sum {ι : Type*} [CommMonoid M] (f : ι -> Multiset M) (s : Finset ι) :
 (∑ x in s, f x).prod = ∏ x in s, (f x).prod
参数：f : ι -> Multiset M；s : Finset ι。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.cons_induction`：∀ {α : Type u_3} {motive : Finset α → Prop},   mo
tive ∅ → (∀ (a : α) (s : Finset α) (h : a ∉ s), motive s → motive (Finset.cons a
 s h)) → ∀ …
-/
theorem prod_sum {ι : Type*} [CommMonoid M] (f : ι → Multiset M) (s : Finset ι) :
    (∑ x ∈ s, f x).prod = ∏ x ∈ s, (f x).prod := by
  induction s using Finset.cons_induction with grind

end Multiset

@[to_additive (attr := simp)]
/-
**IsUnit.multisetProd_iff** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：IsUnit.multisetProd_iff [CommMonoid M] {s : Multiset M} : IsUnit s.prod ↔ 
forall a in s, IsUnit a
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Multiset.induction`：∀ {α : Type u_1} {p : Multiset α → Prop},   p 0 → (∀
 (a : α) (s : Multiset α), p s → p (a ::ₘ s)) → ∀ (s : Multiset α), p s
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `instIsEmptyFalse`：IsEmpty False
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `Multiset.prod_cons`：prod_cons (a : M) (s) : prod (a ::ₘ s) = a * prod s
· 使用定理 `instIsDedekindFiniteMonoid`：∀ (M : Type u_2) [inst : CommMonoid M], IsDe
dekindFiniteMonoid M
-/
lemma IsUnit.multisetProd_iff [CommMonoid M] {s : Multiset M} :
    IsUnit s.prod ↔ ∀ a ∈ s, IsUnit a := by
  induction s using Multiset.induction with
  | empty => simp
  | cons a s ih => simpa using fun _ ↦ ih

@[to_additive (attr := simp)]
/-
**IsUnit.prod_iff** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：IsUnit.prod_iff [CommMonoid M] {f : ι -> M} : IsUnit (∏ a in s, f a) ↔ for
all a in s, IsUnit (f a)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.cons_induction`：∀ {α : Type u_3} {motive : Finset α → Prop},   mo
tive ∅ → (∀ (a : α) (s : Finset α) (h : a ∉ s), motive s → motive (Finset.cons a
 s h)) → ∀ …
-/
lemma IsUnit.prod_iff [CommMonoid M] {f : ι → M} :
    IsUnit (∏ a ∈ s, f a) ↔ ∀ a ∈ s, IsUnit (f a) := by
  induction s using Finset.cons_induction with grind

@[to_additive]
/-
**IsUnit.prod_univ_iff** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：IsUnit.prod_univ_iff [Fintype ι] [CommMonoid M] {f : ι -> M} : IsUnit (∏ a
, f a) ↔ forall a, IsUnit (f a)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma IsUnit.prod_univ_iff [Fintype ι] [CommMonoid M] {f : ι → M} :
    IsUnit (∏ a, f a) ↔ ∀ a, IsUnit (f a) := by simp
/-
**Int.natAbs_sum_le** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Int.natAbs_sum_le (s : Finset ι) (f : ι -> Int) : (∑ i in s, f i).natAbs <
= ∑ i in s, (f i).natAbs
参数：s : Finset ι；f : ι -> Int。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.cons_induction`：∀ {α : Type u_3} {motive : Finset α → Prop},   mo
tive ∅ → (∀ (a : α) (s : Finset α) (h : a ∉ s), motive s → motive (Finset.cons a
 s h)) → ∀ …
-/
theorem Int.natAbs_sum_le (s : Finset ι) (f : ι → ℤ) :
    (∑ i ∈ s, f i).natAbs ≤ ∑ i ∈ s, (f i).natAbs := by
  induction s using Finset.cons_induction with grind

@[deprecated (since := "2026-02-14")]
alias nat_abs_sum_le := Int.natAbs_sum_le
