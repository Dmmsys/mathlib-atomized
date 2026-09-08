/-
Copyright (c) 2016 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Leonardo de Moura, Mario Carneiro, Johannes Hölzl
-/
module

public import Mathlib.Algebra.CharZero.Defs
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Order.Monoid.Canonical.Defs
public import Mathlib.Algebra.Order.Monoid.WithTop
public import Mathlib.Algebra.Regular.Basic


/-!
# Linearly ordered commutative additive groups and monoids with a top element adjoined

This file sets up a special class of linearly ordered commutative additive monoids
that show up as the target of so-called “valuations” in algebraic number theory.

Usually, in the informal literature, these objects are constructed
by taking a linearly ordered commutative additive group Γ and formally adjoining a
top element: `Γ ∪ {⊤}`.

The disadvantage is that a type such as `ENNReal` is not of that form,
whereas it is a very common target for valuations.
The solutions is to use a typeclass, and that is exactly what we do in this file.
-/

public section

variable {G α : Type*}

/-- A linearly ordered commutative monoid with an additively absorbing `⊤` element.
  Instances should include number systems with an infinite element adjoined. -/
/-
**LinearOrderedAddCommMonoidWithTop** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：Type u_3 → Type u_3
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A linearly ordered commutative monoid with an additively absorbing `⊤` element.
  Instances should include number systems with an infinite element adjoined.
-/
class LinearOrderedAddCommMonoidWithTop (α : Type*) extends
    AddCommMonoid α, LinearOrder α, IsOrderedAddMonoid α, OrderTop α where
  /-- In a `LinearOrderedAddCommMonoidWithTop`, the `⊤` element is invariant under addition. -/
  protected top_add' : ∀ x : α, ⊤ + x = ⊤
  protected isAddLeftRegular_of_ne_top ⦃x : α⦄ : x ≠ ⊤ → IsAddLeftRegular x

/-- A linearly ordered commutative group with an additively absorbing `⊤` element.
  Instances should include number systems with an infinite element adjoined. -/
-- We do not extend `LinearOrderedAddCommMonoidWithTop` as that would bring in the unnecessary
-- `isAddLeftRegular_of_ne_top` field.
/-
**LinearOrderedAddCommGroupWithTop** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：Type u_3 → Type u_3
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
class LinearOrderedAddCommGroupWithTop (α : Type*)
    extends AddCommMonoid α, LinearOrder α, IsOrderedAddMonoid α, OrderTop α, SubNegMonoid α,
    Nontrivial α where
  /-- In a `LinearOrderedAddCommMonoidWithTop`, the `⊤` element is invariant under addition. -/
  protected top_add' (x : α) : ⊤ + x = ⊤
  neg_top : -(⊤ : α) = ⊤
  add_neg_cancel_of_ne_top ⦃x : α⦄ : x ≠ ⊤ → x + -x = 0

section LinearOrderedAddCommMonoidWithTop
variable [LinearOrderedAddCommMonoidWithTop α] {a b c : α}

@[simp]
/-
**top_add** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：top_add (a : α) : ⊤ + a = ⊤
参数：a : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearOrderedAddCommMonoidWithTop.top_add'`：∀ {α : Type u_3} [self : Lin
earOrderedAddCommMonoidWithTop α] (x : α), ⊤ + x = ⊤
-/
theorem top_add (a : α) : ⊤ + a = ⊤ :=
  LinearOrderedAddCommMonoidWithTop.top_add' a

@[simp]
/-
**add_top** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：add_top (a : α) : a + ⊤ = ⊤
参数：a : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
· 使用定理 `top_add`：top_add (a : α) : ⊤ + a = ⊤
-/
theorem add_top (a : α) : a + ⊤ = ⊤ :=
  Trans.trans (add_comm _ _) (top_add _)
/-
**IsAddRegular.of_ne_top** 是 Mathlib 中的一个定理，位于命名空间 `IsAddRegular`。
形式化陈述：∀ {α : Type u_2} [inst : LinearOrderedAddCommMonoidWithTop α] {a : α}, a ≠
 ⊤ → IsAddRegular a
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearOrderedAddCommMonoidWithTop.isAddLeftRegular_of_ne_top`：∀ {α : Typ
e u_3} [self : LinearOrderedAddCommMonoidWithTop α] ⦃x : α⦄, x ≠ ⊤ → IsAddLeftRe
gular x
-/
@[simp] lemma IsAddRegular.of_ne_top (ha : a ≠ ⊤) : IsAddRegular a := by
  simpa using LinearOrderedAddCommMonoidWithTop.isAddLeftRegular_of_ne_top ha
/-
**add_left_injective_of_ne_top** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：add_left_injective_of_ne_top (b : α) (h : b != ⊤) : Function.Injective (fu
n x => x + b)
参数：b : α；h : b != ⊤。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsAddRegular.right`：∀ {R : Type u_2} [inst : Add R] {c : R}, IsAddRegula
r c → IsAddRightRegular c
· 使用定理 `IsAddRegular.of_ne_top`：∀ {α : Type u_2} [inst : LinearOrderedAddCommMon
oidWithTop α] {a : α}, a ≠ ⊤ → IsAddRegular a
-/
lemma add_left_injective_of_ne_top (b : α) (h : b ≠ ⊤) : Function.Injective (fun x ↦ x + b) :=
  (IsAddRegular.of_ne_top h).2
/-
**add_right_injective_of_ne_top** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：add_right_injective_of_ne_top (b : α) (h : b != ⊤) : Function.Injective (f
un x => b + x)
参数：b : α；h : b != ⊤。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsAddRegular.left`：∀ {R : Type u_2} [inst : Add R] {c : R}, IsAddRegular
 c → IsAddLeftRegular c
· 使用定理 `IsAddRegular.of_ne_top`：∀ {α : Type u_2} [inst : LinearOrderedAddCommMon
oidWithTop α] {a : α}, a ≠ ⊤ → IsAddRegular a
-/
lemma add_right_injective_of_ne_top (b : α) (h : b ≠ ⊤) : Function.Injective (fun x ↦ b + x) :=
  (IsAddRegular.of_ne_top h).1

@[simp]
/-
**add_left_inj_of_ne_top** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：add_left_inj_of_ne_top (h : a != ⊤) : b + a = c + a ↔ b = c
参数：h : a != ⊤。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Injective.eq_iff`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β}, 
Function.Injective f → ∀ {a b : α}, f a = f b ↔ a = b
· 使用引理 `add_left_injective_of_ne_top`：add_left_injective_of_ne_top (b : α) (h : 
b != ⊤) : Function.Injective (fun x => x + b)
-/
lemma add_left_inj_of_ne_top (h : a ≠ ⊤) : b + a = c + a ↔ b = c :=
  (add_left_injective_of_ne_top _ h).eq_iff

@[simp]
/-
**add_right_inj_of_ne_top** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：add_right_inj_of_ne_top (h : a != ⊤) : a + b = a + c ↔ b = c
参数：h : a != ⊤。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Injective.eq_iff`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β}, 
Function.Injective f → ∀ {a b : α}, f a = f b ↔ a = b
· 使用引理 `add_right_injective_of_ne_top`：add_right_injective_of_ne_top (b : α) (h 
: b != ⊤) : Function.Injective (fun x => b + x)
-/
lemma add_right_inj_of_ne_top (h : a ≠ ⊤) : a + b = a + c ↔ b = c :=
  (add_right_injective_of_ne_top _ h).eq_iff
/-
**add_left_strictMono_of_ne_top** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：add_left_strictMono_of_ne_top (h : b != ⊤) : StrictMono (fun x => x + b)
参数：h : b != ⊤。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Monotone.strictMono_of_injective`：Monotone.strictMono_of_injective (h₁ :
 Monotone f) (h₂ : Injective f) : StrictMono f
· 使用定理 `add_left_mono`：∀ {α : Type u_1} [inst : Add α] [inst_1 : Preorder α] [Ad
dRightMono α] {a : α}, Monotone fun x => x + a
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `LinearOrderedAddCommMonoidWithTop.toIsOrderedAddMonoid`：∀ {α : Type u_3}
 [self : LinearOrderedAddCommMonoidWithTop α], IsOrderedAddMonoid α
· 使用引理 `add_left_injective_of_ne_top`：add_left_injective_of_ne_top (b : α) (h : 
b != ⊤) : Function.Injective (fun x => x + b)
-/
lemma add_left_strictMono_of_ne_top (h : b ≠ ⊤) : StrictMono (fun x ↦ x + b) :=
  add_left_mono.strictMono_of_injective <| add_left_injective_of_ne_top _ h
/-
**add_right_strictMono_of_ne_top** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：add_right_strictMono_of_ne_top (h : b != ⊤) : StrictMono (fun x => b + x)
参数：h : b != ⊤。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Monotone.strictMono_of_injective`：Monotone.strictMono_of_injective (h₁ :
 Monotone f) (h₂ : Injective f) : StrictMono f
· 使用定理 `add_right_mono`：∀ {α : Type u_1} [inst : Add α] [inst_1 : Preorder α] [A
ddLeftMono α] {a : α}, Monotone fun x => a + x
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `LinearOrderedAddCommMonoidWithTop.toIsOrderedAddMonoid`：∀ {α : Type u_3}
 [self : LinearOrderedAddCommMonoidWithTop α], IsOrderedAddMonoid α
· 使用引理 `add_right_injective_of_ne_top`：add_right_injective_of_ne_top (b : α) (h 
: b != ⊤) : Function.Injective (fun x => b + x)
-/
lemma add_right_strictMono_of_ne_top (h : b ≠ ⊤) : StrictMono (fun x ↦ b + x) :=
  add_right_mono.strictMono_of_injective <| add_right_injective_of_ne_top _ h

@[simp]
/-
**add_le_add_iff_left_of_ne_top** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：add_le_add_iff_left_of_ne_top (h : a != ⊤) : b + a <= c + a ↔ b <= c
参数：h : a != ⊤。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `StrictMono.le_iff_le`：StrictMono.le_iff_le (hf : StrictMono f) {a b : α}
 : f a <= f b ↔ a <= b
· 使用引理 `add_left_strictMono_of_ne_top`：add_left_strictMono_of_ne_top (h : b != ⊤
) : StrictMono (fun x => x + b)
-/
lemma add_le_add_iff_left_of_ne_top (h : a ≠ ⊤) : b + a ≤ c + a ↔ b ≤ c :=
  (add_left_strictMono_of_ne_top h).le_iff_le

@[simp]
/-
**add_le_add_iff_right_of_ne_top** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：add_le_add_iff_right_of_ne_top (h : a != ⊤) : a + b <= a + c ↔ b <= c
参数：h : a != ⊤。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `StrictMono.le_iff_le`：StrictMono.le_iff_le (hf : StrictMono f) {a b : α}
 : f a <= f b ↔ a <= b
· 使用引理 `add_right_strictMono_of_ne_top`：add_right_strictMono_of_ne_top (h : b !=
 ⊤) : StrictMono (fun x => b + x)
-/
lemma add_le_add_iff_right_of_ne_top (h : a ≠ ⊤) : a + b ≤ a + c ↔ b ≤ c :=
  (add_right_strictMono_of_ne_top h).le_iff_le

@[simp]
/-
**add_lt_add_iff_left_of_ne_top** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：add_lt_add_iff_left_of_ne_top (h : a != ⊤) : b + a < c + a ↔ b < c
参数：h : a != ⊤。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `StrictMono.lt_iff_lt`：StrictMono.lt_iff_lt (hf : StrictMono f) {a b : α}
 : f a < f b ↔ a < b
· 使用引理 `add_left_strictMono_of_ne_top`：add_left_strictMono_of_ne_top (h : b != ⊤
) : StrictMono (fun x => x + b)
-/
lemma add_lt_add_iff_left_of_ne_top (h : a ≠ ⊤) : b + a < c + a ↔ b < c :=
  (add_left_strictMono_of_ne_top h).lt_iff_lt

@[simp]
/-
**add_lt_add_iff_right_of_ne_top** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：add_lt_add_iff_right_of_ne_top (h : a != ⊤) : a + b < a + c ↔ b < c
参数：h : a != ⊤。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `StrictMono.lt_iff_lt`：StrictMono.lt_iff_lt (hf : StrictMono f) {a b : α}
 : f a < f b ↔ a < b
· 使用引理 `add_right_strictMono_of_ne_top`：add_right_strictMono_of_ne_top (h : b !=
 ⊤) : StrictMono (fun x => b + x)
-/
lemma add_lt_add_iff_right_of_ne_top (h : a ≠ ⊤) : a + b < a + c ↔ b < c :=
  (add_right_strictMono_of_ne_top h).lt_iff_lt

end LinearOrderedAddCommMonoidWithTop

namespace LinearOrderedAddCommGroupWithTop

variable [LinearOrderedAddCommGroupWithTop α] {a b c : α}

attribute [simp] neg_top

/-! Note: The following lemmas are special cases of the corresponding `IsAddUnit` lemmas. -/

/-
**LinearOrderedAddCommGroupWithTop.neg_add_cancel_of_ne_top** 是 Mathlib 中的一个引理，位
于命名空间 `LinearOrderedAddCommGroupWithTop`。
形式化陈述：neg_add_cancel_of_ne_top (ha : a != ⊤) : -a + a = 0
参数：ha : a != ⊤。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
· 使用定理 `LinearOrderedAddCommGroupWithTop.add_neg_cancel_of_ne_top`：∀ {α : Type u
_3} [self : LinearOrderedAddCommGroupWithTop α] ⦃x : α⦄, x ≠ ⊤ → x + -x = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
Note: The following lemmas are special cases of the corresponding `IsAddUnit` le
mmas.
-/
lemma neg_add_cancel_of_ne_top (ha : a ≠ ⊤) : -a + a = 0 := by
  simp [add_comm, add_neg_cancel_of_ne_top ha]
/-
**LinearOrderedAddCommGroupWithTop.add_neg_cancel_left_of_ne_top** 是 Mathlib 中的一
个引理，位于命名空间 `LinearOrderedAddCommGroupWithTop`。
形式化陈述：add_neg_cancel_left_of_ne_top (ha : a != ⊤) (b : α) : a + (-a + b) = b
参数：ha : a != ⊤；b : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LinearOrderedAddCommGroupWithTop.add_neg_cancel_of_ne_top`：∀ {α : Type u
_3} [self : LinearOrderedAddCommGroupWithTop α] ⦃x : α⦄, x ≠ ⊤ → x + -x = 0
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma add_neg_cancel_left_of_ne_top (ha : a ≠ ⊤) (b : α) : a + (-a + b) = b := by
  simp [← add_assoc, add_neg_cancel_of_ne_top ha]
/-
**LinearOrderedAddCommGroupWithTop.neg_add_cancel_left_of_ne_top** 是 Mathlib 中的一
个引理，位于命名空间 `LinearOrderedAddCommGroupWithTop`。
形式化陈述：neg_add_cancel_left_of_ne_top (ha : a != ⊤) (b : α) : -a + (a + b) = b
参数：ha : a != ⊤；b : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `LinearOrderedAddCommGroupWithTop.neg_add_cancel_of_ne_top`：neg_add_cance
l_of_ne_top (ha : a != ⊤) : -a + a = 0
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma neg_add_cancel_left_of_ne_top (ha : a ≠ ⊤) (b : α) : -a + (a + b) = b := by
  simp [← add_assoc, neg_add_cancel_of_ne_top ha]
/-
**LinearOrderedAddCommGroupWithTop.add_neg_cancel_right_of_ne_top** 是 Mathlib 中的
一个引理，位于命名空间 `LinearOrderedAddCommGroupWithTop`。
形式化陈述：add_neg_cancel_right_of_ne_top (hb : b != ⊤) (a : α) : a + b + -b = a
参数：hb : b != ⊤；a : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `add_assoc`：∀ {G : Type u_1} [inst : AddSemigroup G] (a b c : G), a + b +
 c = a + (b + c)
· 使用定理 `LinearOrderedAddCommGroupWithTop.add_neg_cancel_of_ne_top`：∀ {α : Type u
_3} [self : LinearOrderedAddCommGroupWithTop α] ⦃x : α⦄, x ≠ ⊤ → x + -x = 0
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma add_neg_cancel_right_of_ne_top (hb : b ≠ ⊤) (a : α) : a + b + -b = a := by
  simp [add_assoc, add_neg_cancel_of_ne_top hb]
/-
**LinearOrderedAddCommGroupWithTop.neg_add_cancel_right_of_ne_top** 是 Mathlib 中的
一个引理，位于命名空间 `LinearOrderedAddCommGroupWithTop`。
形式化陈述：neg_add_cancel_right_of_ne_top (hb : b != ⊤) (a : α) : a + -b + b = a
参数：hb : b != ⊤；a : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `add_assoc`：∀ {G : Type u_1} [inst : AddSemigroup G] (a b c : G), a + b +
 c = a + (b + c)
· 使用引理 `LinearOrderedAddCommGroupWithTop.neg_add_cancel_of_ne_top`：neg_add_cance
l_of_ne_top (ha : a != ⊤) : -a + a = 0
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma neg_add_cancel_right_of_ne_top (hb : b ≠ ⊤) (a : α) : a + -b + b = a := by
  simp [add_assoc, neg_add_cancel_of_ne_top hb]
/-
**LinearOrderedAddCommGroupWithTop.top_ne_zero** 是 Mathlib 中的一个定理，位于命名空间 `Linear
OrderedAddCommGroupWithTop`。
形式化陈述：∀ {α : Type u_2} [inst : LinearOrderedAddCommGroupWithTop α], ⊤ ≠ 0
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `exists_ne`：exists_ne [Nontrivial α] (x : α) : exists y, y != x
· 使用定理 `LinearOrderedAddCommGroupWithTop.toNontrivial`：∀ {α : Type u_3} [self : 
LinearOrderedAddCommGroupWithTop α], Nontrivial α
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `LinearOrderedAddCommGroupWithTop.top_add'`：∀ {α : Type u_3} [self : Line
arOrderedAddCommGroupWithTop α] (x : α), ⊤ + x = ⊤
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `not_true_eq_false`：(¬True) = False
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
-/
@[simp] lemma top_ne_zero : (⊤ : α) ≠ 0 := by
  intro h
  obtain ⟨a, ha⟩ := exists_ne (0 : α)
  rw [← zero_add a] at ha
  simp [LinearOrderedAddCommGroupWithTop.top_add', -zero_add, ← h] at ha
/-
**LinearOrderedAddCommGroupWithTop.zero_ne_top** 是 Mathlib 中的一个定理，位于命名空间 `Linear
OrderedAddCommGroupWithTop`。
形式化陈述：∀ {α : Type u_2} [inst : LinearOrderedAddCommGroupWithTop α], 0 ≠ ⊤
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ne.symm`：∀ {α : Sort u} {a b : α}, a ≠ b → b ≠ a
· 使用定理 `LinearOrderedAddCommGroupWithTop.top_ne_zero`：∀ {α : Type u_2} [inst : L
inearOrderedAddCommGroupWithTop α], ⊤ ≠ 0
-/
@[simp] lemma zero_ne_top : 0 ≠ (⊤ : α) := top_ne_zero.symm
/-
**LinearOrderedAddCommGroupWithTop.top_pos** 是 Mathlib 中的一个定理，位于命名空间 `LinearOrde
redAddCommGroupWithTop`。
形式化陈述：∀ {α : Type u_2} [inst : LinearOrderedAddCommGroupWithTop α], 0 < ⊤
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `lt_top_iff_ne_top`：lt_top_iff_ne_top : a < ⊤ ↔ a != ⊤
· 使用定理 `Ne.symm`：∀ {α : Sort u} {a b : α}, a ≠ b → b ≠ a
· 使用定理 `LinearOrderedAddCommGroupWithTop.top_ne_zero`：∀ {α : Type u_2} [inst : L
inearOrderedAddCommGroupWithTop α], ⊤ ≠ 0
-/
@[simp] lemma top_pos : (0 : α) < ⊤ := lt_top_iff_ne_top.2 top_ne_zero.symm
/-
**LinearOrderedAddCommGroupWithTop.isAddUnit_iff** 是 Mathlib 中的一个定理，位于命名空间 `Line
arOrderedAddCommGroupWithTop`。
形式化陈述：∀ {α : Type u_2} [inst : LinearOrderedAddCommGroupWithTop α] {a : α}, IsAd
dUnit a ↔ a ≠ ⊤
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LinearOrderedAddCommGroupWithTop.top_add'`：∀ {α : Type u_3} [self : Line
arOrderedAddCommGroupWithTop α] (x : α), ⊤ + x = ⊤
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `IsAddUnit.of_add_eq_zero`：∀ {M : Type u_1} [inst : AddMonoid M] [IsDedek
indFiniteAddMonoid M] {a : M} (b : M), a + b = 0 → IsAddUnit a
· 使用定理 `instIsDedekindFiniteAddMonoid`：∀ (M : Type u_2) [inst : AddCommMonoid M]
, IsDedekindFiniteAddMonoid M
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `LinearOrderedAddCommGroupWithTop.add_neg_cancel_of_ne_top`：∀ {α : Type u
_3} [self : LinearOrderedAddCommGroupWithTop α] ⦃x : α⦄, x ≠ ⊤ → x + -x = 0
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
@[simp] lemma isAddUnit_iff : IsAddUnit a ↔ a ≠ ⊤ where
  mp := by rintro ⟨⟨b, c, hbc, -⟩, rfl⟩ rfl; simp [LinearOrderedAddCommGroupWithTop.top_add'] at hbc
  mpr ha := .of_add_eq_zero (-a) <| by simp [ha, add_neg_cancel_of_ne_top]
/-
**LinearOrderedAddCommGroupWithTop.** 是 Mathlib 中的一个实例，位于命名空间 `LinearOrderedAddC
ommGroupWithTop`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : LinearOrderedAddCommMonoidWithTop α where
  top_add' := LinearOrderedAddCommGroupWithTop.top_add'
  isAddLeftRegular_of_ne_top _a ha := (isAddUnit_iff.2 ha).isAddRegular.1
/-
**LinearOrderedAddCommGroupWithTop.add_ne_top** 是 Mathlib 中的一个引理，位于命名空间 `LinearO
rderedAddCommGroupWithTop`。
形式化陈述：add_ne_top : a + b != ⊤ ↔ a != ⊤ ∧ b != ⊤
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `instIsDedekindFiniteAddMonoid`：∀ (M : Type u_2) [inst : AddCommMonoid M]
, IsDedekindFiniteAddMonoid M
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma add_ne_top : a + b ≠ ⊤ ↔ a ≠ ⊤ ∧ b ≠ ⊤ := by simp [← isAddUnit_iff]
/-
**LinearOrderedAddCommGroupWithTop.add_eq_top** 是 Mathlib 中的一个定理，位于命名空间 `LinearO
rderedAddCommGroupWithTop`。
形式化陈述：∀ {α : Type u_2} [inst : LinearOrderedAddCommGroupWithTop α] {a b : α}, a 
+ b = ⊤ ↔ a = ⊤ ∨ b = ⊤
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `not_iff_not`：not_iff_not : (¬a ↔ ¬b) ↔ (a ↔ b)
· 使用定理 `not_or`：∀ {p q : Prop}, ¬(p ∨ q) ↔ ¬p ∧ ¬q
· 使用引理 `LinearOrderedAddCommGroupWithTop.add_ne_top`：add_ne_top : a + b != ⊤ ↔ a
 != ⊤ ∧ b != ⊤
-/
@[simp] lemma add_eq_top : a + b = ⊤ ↔ a = ⊤ ∨ b = ⊤ := by
  rw [← not_iff_not, not_or]; exact add_ne_top
/-
**LinearOrderedAddCommGroupWithTop.add_lt_top** 是 Mathlib 中的一个定理，位于命名空间 `LinearO
rderedAddCommGroupWithTop`。
形式化陈述：∀ {α : Type u_2} [inst : LinearOrderedAddCommGroupWithTop α] {a b : α}, a 
+ b < ⊤ ↔ a < ⊤ ∧ b < ⊤
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
@[simp] lemma add_lt_top : a + b < ⊤ ↔ a < ⊤ ∧ b < ⊤ := by simp [lt_top_iff_ne_top]
/-
**LinearOrderedAddCommGroupWithTop.neg_eq_top** 是 Mathlib 中的一个定理，位于命名空间 `LinearO
rderedAddCommGroupWithTop`。
形式化陈述：∀ {α : Type u_2} [inst : LinearOrderedAddCommGroupWithTop α] {a : α}, -a =
 ⊤ ↔ a = ⊤
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `add_top`：add_top (a : α) : a + ⊤ = ⊤
· 使用定理 `LinearOrderedAddCommGroupWithTop.add_neg_cancel_of_ne_top`：∀ {α : Type u
_3} [self : LinearOrderedAddCommGroupWithTop α] ⦃x : α⦄, x ≠ ⊤ → x + -x = 0
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `LinearOrderedAddCommGroupWithTop.neg_top`：∀ {α : Type u_3} [self : Linea
rOrderedAddCommGroupWithTop α], -⊤ = ⊤
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
@[simp] lemma neg_eq_top : -a = ⊤ ↔ a = ⊤ where
  mp h := by simpa [h] using add_neg_cancel_of_ne_top (x := a)
  mpr h := by simp [h]
/-
**LinearOrderedAddCommGroupWithTop.sub_top** 是 Mathlib 中的一个定理，位于命名空间 `LinearOrde
redAddCommGroupWithTop`。
形式化陈述：∀ {α : Type u_2} [inst : LinearOrderedAddCommGroupWithTop α] {a : α}, a - 
⊤ = ⊤
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `sub_eq_add_neg`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a b : G), a - 
b = a + -b
· 使用定理 `LinearOrderedAddCommGroupWithTop.neg_top`：∀ {α : Type u_3} [self : Linea
rOrderedAddCommGroupWithTop α], -⊤ = ⊤
· 使用定理 `add_top`：add_top (a : α) : a + ⊤ = ⊤
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
@[simp] lemma sub_top : a - ⊤ = ⊤ := by simp [sub_eq_add_neg]
/-
**LinearOrderedAddCommGroupWithTop.** 是 Mathlib 中的一个实例，位于命名空间 `LinearOrderedAddC
ommGroupWithTop`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 100) toSubtractionMonoid : SubtractionMonoid α where
  neg_neg a := by
    obtain rfl | ha := eq_or_ne a ⊤
    · simp
    · apply left_neg_eq_right_neg (a := -a) <;> simp [add_comm, add_neg_cancel_of_ne_top, ha]
  neg_add_rev a b := by
    obtain rfl | ha := eq_or_ne a ⊤
    · simp
    obtain rfl | hb := eq_or_ne b ⊤
    · simp
    · exact left_neg_eq_right_neg (a := a + b) (by simp [neg_add_cancel_of_ne_top, *])
        (by simp [add_assoc, add_neg_cancel_of_ne_top, add_neg_cancel_left_of_ne_top, *])
  neg_eq_of_add a b h := by
    have ha : a ≠ ⊤ := by rintro rfl; simp at h
    exact left_neg_eq_right_neg (a := a) (by simp [neg_add_cancel_of_ne_top, *]) h
/-
**LinearOrderedAddCommGroupWithTop.sub_left_injective_of_ne_top** 是 Mathlib 中的一个
引理，位于命名空间 `LinearOrderedAddCommGroupWithTop`。
形式化陈述：sub_left_injective_of_ne_top (h : b != ⊤) : Function.Injective fun x => x 
- b
参数：h : b != ⊤。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `sub_eq_add_neg`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a b : G), a - 
b = a + -b
· 使用引理 `add_left_injective_of_ne_top`：add_left_injective_of_ne_top (b : α) (h : 
b != ⊤) : Function.Injective (fun x => x + b)
-/
lemma sub_left_injective_of_ne_top (h : b ≠ ⊤) : Function.Injective fun x ↦ x - b := by
  simpa [sub_eq_add_neg] using add_left_injective_of_ne_top (-b) (by simpa)
/-
**LinearOrderedAddCommGroupWithTop.sub_right_injective_of_ne_top** 是 Mathlib 中的一
个引理，位于命名空间 `LinearOrderedAddCommGroupWithTop`。
形式化陈述：sub_right_injective_of_ne_top (h : b != ⊤) : Function.Injective fun x => b
 - x
参数：h : b != ⊤。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `sub_eq_add_neg`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a b : G), a - 
b = a + -b
· 使用定理 `Function.Injective.comp`：∀ {α : Sort u_1} {β : Sort u_2} {γ : Sort u_3} 
{g : β → γ} {f : α → β},   Function.Injective g → Function.Injective f → Functio
n.Injective (…
· 使用引理 `add_right_injective_of_ne_top`：add_right_injective_of_ne_top (b : α) (h 
: b != ⊤) : Function.Injective (fun x => b + x)
· 使用定理 `neg_injective`：∀ {G : Type u_3} [inst : InvolutiveNeg G], Function.Injec
tive Neg.neg
-/
lemma sub_right_injective_of_ne_top (h : b ≠ ⊤) : Function.Injective fun x ↦ b - x := by
  simpa [sub_eq_add_neg] using! (add_right_injective_of_ne_top b h).comp neg_injective

@[simp]
/-
**LinearOrderedAddCommGroupWithTop.sub_left_inj_of_ne_top** 是 Mathlib 中的一个引理，位于命
名空间 `LinearOrderedAddCommGroupWithTop`。
形式化陈述：sub_left_inj_of_ne_top (h : a != ⊤) : b - a = c - a ↔ b = c
参数：h : a != ⊤。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Injective.eq_iff`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β}, 
Function.Injective f → ∀ {a b : α}, f a = f b ↔ a = b
· 使用引理 `LinearOrderedAddCommGroupWithTop.sub_left_injective_of_ne_top`：sub_left_
injective_of_ne_top (h : b != ⊤) : Function.Injective fun x => x - b
-/
lemma sub_left_inj_of_ne_top (h : a ≠ ⊤) : b - a = c - a ↔ b = c :=
  (sub_left_injective_of_ne_top h).eq_iff

@[simp]
/-
**LinearOrderedAddCommGroupWithTop.sub_right_inj_of_ne_top** 是 Mathlib 中的一个引理，位于
命名空间 `LinearOrderedAddCommGroupWithTop`。
形式化陈述：sub_right_inj_of_ne_top (h : a != ⊤) : a - b = a - c ↔ b = c
参数：h : a != ⊤。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Injective.eq_iff`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β}, 
Function.Injective f → ∀ {a b : α}, f a = f b ↔ a = b
· 使用引理 `LinearOrderedAddCommGroupWithTop.sub_right_injective_of_ne_top`：sub_righ
t_injective_of_ne_top (h : b != ⊤) : Function.Injective fun x => b - x
-/
lemma sub_right_inj_of_ne_top (h : a ≠ ⊤) : a - b = a - c ↔ b = c :=
  (sub_right_injective_of_ne_top h).eq_iff
/-
**LinearOrderedAddCommGroupWithTop.sub_left_strictMono_of_ne_top** 是 Mathlib 中的一
个引理，位于命名空间 `LinearOrderedAddCommGroupWithTop`。
形式化陈述：sub_left_strictMono_of_ne_top (h : b != ⊤) : StrictMono fun x => x - b
参数：h : b != ⊤。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `sub_eq_add_neg`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a b : G), a - 
b = a + -b
· 使用引理 `add_left_strictMono_of_ne_top`：add_left_strictMono_of_ne_top (h : b != ⊤
) : StrictMono (fun x => x + b)
-/
lemma sub_left_strictMono_of_ne_top (h : b ≠ ⊤) : StrictMono fun x ↦ x - b := by
  simpa [sub_eq_add_neg] using add_left_strictMono_of_ne_top (b := -b) (by simpa)

@[simp]
/-
**LinearOrderedAddCommGroupWithTop.sub_le_sub_iff_left_of_ne_top** 是 Mathlib 中的一
个引理，位于命名空间 `LinearOrderedAddCommGroupWithTop`。
形式化陈述：sub_le_sub_iff_left_of_ne_top (h : a != ⊤) : b - a <= c - a ↔ b <= c
参数：h : a != ⊤。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `StrictMono.le_iff_le`：StrictMono.le_iff_le (hf : StrictMono f) {a b : α}
 : f a <= f b ↔ a <= b
· 使用引理 `LinearOrderedAddCommGroupWithTop.sub_left_strictMono_of_ne_top`：sub_left
_strictMono_of_ne_top (h : b != ⊤) : StrictMono fun x => x - b
-/
lemma sub_le_sub_iff_left_of_ne_top (h : a ≠ ⊤) : b - a ≤ c - a ↔ b ≤ c :=
  (sub_left_strictMono_of_ne_top h).le_iff_le

@[simp]
/-
**LinearOrderedAddCommGroupWithTop.sub_lt_sub_iff_left_of_ne_top** 是 Mathlib 中的一
个引理，位于命名空间 `LinearOrderedAddCommGroupWithTop`。
形式化陈述：sub_lt_sub_iff_left_of_ne_top (h : a != ⊤) : b - a < c - a ↔ b < c
参数：h : a != ⊤。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `StrictMono.lt_iff_lt`：StrictMono.lt_iff_lt (hf : StrictMono f) {a b : α}
 : f a < f b ↔ a < b
· 使用引理 `LinearOrderedAddCommGroupWithTop.sub_left_strictMono_of_ne_top`：sub_left
_strictMono_of_ne_top (h : b != ⊤) : StrictMono fun x => x - b
-/
lemma sub_lt_sub_iff_left_of_ne_top (h : a ≠ ⊤) : b - a < c - a ↔ b < c :=
  (sub_left_strictMono_of_ne_top h).lt_iff_lt

@[simp]
/-
**LinearOrderedAddCommGroupWithTop.add_neg_cancel_iff_ne_top** 是 Mathlib 中的一个引理，
位于命名空间 `LinearOrderedAddCommGroupWithTop`。
形式化陈述：add_neg_cancel_iff_ne_top : a + -a = 0 ↔ a != ⊤ where mp
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose₃`：contrapose₃ {p q : Prop} : (q -> 
¬ p) -> (p -> ¬ q)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `implies_congr_ctx`：∀ {p₁ p₂ q₁ q₂ : Prop}, p₁ = p₂ → (p₂ → q₁ = q₂) → (p
₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `LinearOrderedAddCommGroupWithTop.neg_top`：∀ {α : Type u_3} [self : Linea
rOrderedAddCommGroupWithTop α], -⊤ = ⊤
· 使用定理 `add_top`：add_top (a : α) : a + ⊤ = ⊤
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `LinearOrderedAddCommGroupWithTop.add_neg_cancel_of_ne_top`：∀ {α : Type u
_3} [self : LinearOrderedAddCommGroupWithTop α] ⦃x : α⦄, x ≠ ⊤ → x + -x = 0
-/
lemma add_neg_cancel_iff_ne_top : a + -a = 0 ↔ a ≠ ⊤ where
  mp := by contrapose; simp +contextual
  mpr h := add_neg_cancel_of_ne_top h

@[simp]
/-
**LinearOrderedAddCommGroupWithTop.sub_self_eq_zero_iff_ne_top** 是 Mathlib 中的一个引
理，位于命名空间 `LinearOrderedAddCommGroupWithTop`。
形式化陈述：sub_self_eq_zero_iff_ne_top : a - a = 0 ↔ a != ⊤
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `sub_eq_add_neg`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a b : G), a - 
b = a + -b
· 使用引理 `LinearOrderedAddCommGroupWithTop.add_neg_cancel_iff_ne_top`：add_neg_canc
el_iff_ne_top : a + -a = 0 ↔ a != ⊤ where mp
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma sub_self_eq_zero_iff_ne_top : a - a = 0 ↔ a ≠ ⊤ := by
  rw [sub_eq_add_neg, add_neg_cancel_iff_ne_top]

alias ⟨_, sub_self_eq_zero_of_ne_top⟩ := sub_self_eq_zero_iff_ne_top
/-
**LinearOrderedAddCommGroupWithTop.sub_pos** 是 Mathlib 中的一个引理，位于命名空间 `LinearOrde
redAddCommGroupWithTop`。
形式化陈述：sub_pos : 0 < a - b ↔ b < a ∨ b = ⊤
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LinearOrderedAddCommGroupWithTop.sub_top`：∀ {α : Type u_2} [inst : Linea
rOrderedAddCommGroupWithTop α] {a : α}, a - ⊤ = ⊤
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `or_true`：∀ (p : Prop), (p ∨ True) = True
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `LinearOrderedAddCommGroupWithTop.sub_self_eq_zero_of_ne_top`：∀ {α : Type
 u_2} [inst : LinearOrderedAddCommGroupWithTop α] {a : α}, a ≠ ⊤ → a - a = 0
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `or_false`：∀ (p : Prop), (p ∨ False) = p
-/
lemma sub_pos : 0 < a - b ↔ b < a ∨ b = ⊤ := by
  obtain rfl | hb := eq_or_ne b ⊤
  · simp
  · simp [← sub_self_eq_zero_of_ne_top hb, hb]

@[simp]
/-
**LinearOrderedAddCommGroupWithTop.neg_pos** 是 Mathlib 中的一个引理，位于命名空间 `LinearOrde
redAddCommGroupWithTop`。
形式化陈述：neg_pos : 0 < -a ↔ a < 0 ∨ a = ⊤
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `zero_sub`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a : G), 0 - a = -a
· 使用引理 `LinearOrderedAddCommGroupWithTop.sub_pos`：sub_pos : 0 < a - b ↔ b < a ∨ 
b = ⊤
-/
lemma neg_pos : 0 < -a ↔ a < 0 ∨ a = ⊤ := by
  simpa using sub_pos (a := 0) (b := a)

@[simp]
/-
**LinearOrderedAddCommGroupWithTop.sub_self_nonneg** 是 Mathlib 中的一个引理，位于命名空间 `Li
nearOrderedAddCommGroupWithTop`。
形式化陈述：sub_self_nonneg : 0 <= a - a
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LinearOrderedAddCommGroupWithTop.sub_top`：∀ {α : Type u_2} [inst : Linea
rOrderedAddCommGroupWithTop α] {a : α}, a - ⊤ = ⊤
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `LinearOrderedAddCommGroupWithTop.sub_self_eq_zero_of_ne_top`：∀ {α : Type
 u_2} [inst : LinearOrderedAddCommGroupWithTop α] {a : α}, a ≠ ⊤ → a - a = 0
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
-/
lemma sub_self_nonneg : 0 ≤ a - a := by
  obtain rfl | ha := eq_or_ne a ⊤
  · simp
  · rw [sub_self_eq_zero_of_ne_top ha]

@[simp]
/-
**LinearOrderedAddCommGroupWithTop.sub_eq_zero** 是 Mathlib 中的一个引理，位于命名空间 `Linear
OrderedAddCommGroupWithTop`。
形式化陈述：sub_eq_zero (ha : a != ⊤) : b - a = 0 ↔ b = a
参数：ha : a != ⊤。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `LinearOrderedAddCommGroupWithTop.sub_self_eq_zero_of_ne_top`：∀ {α : Type
 u_2} [inst : LinearOrderedAddCommGroupWithTop α] {a : α}, a ≠ ⊤ → a - a = 0
· 使用引理 `LinearOrderedAddCommGroupWithTop.sub_left_inj_of_ne_top`：sub_left_inj_of
_ne_top (h : a != ⊤) : b - a = c - a ↔ b = c
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma sub_eq_zero (ha : a ≠ ⊤) : b - a = 0 ↔ b = a := by
  rw [← sub_self_eq_zero_of_ne_top ha, sub_left_inj_of_ne_top ha]

end LinearOrderedAddCommGroupWithTop

namespace WithTop

/-
**WithTop.linearOrderedAddCommMonoidWithTop** 是 Mathlib 中的一个实例，位于命名空间 `WithTop`。
形式化陈述：linearOrderedAddCommMonoidWithTop [AddCancelCommMonoid α] [LinearOrder α] 
[IsOrderedAddMonoid α] : LinearOrderedAddCommMonoidWithTop (WithTop α) where top
_add'
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance linearOrderedAddCommMonoidWithTop [AddCancelCommMonoid α] [LinearOrder α]
    [IsOrderedAddMonoid α] : LinearOrderedAddCommMonoidWithTop (WithTop α) where
  top_add' := WithTop.top_add
  isAddLeftRegular_of_ne_top _a ha _b _c := WithTop.add_left_cancel ha

namespace LinearOrderedAddCommGroup
variable [AddCommGroup G] {x y : WithTop G}

/-
**WithTop.LinearOrderedAddCommGroup.instNeg** 是 Mathlib 中的一个实例，位于命名空间 `WithTop.L
inearOrderedAddCommGroup`。
形式化陈述：instNeg : Neg (WithTop G) where neg
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instNeg : Neg (WithTop G) where
  neg := .map fun a ↦ -a

/-- If `G` has subtraction, we can extend the subtraction to `WithTop G`, by setting `x - ⊤ = ⊤` and
`⊤ - x = ⊤`. This definition is only registered as an instance on additive commutative groups, to
avoid conflicting with the instance `WithTop.instSub` on types with a bottom element. -/
/-
**WithTop.LinearOrderedAddCommGroup.instSub** 是 Mathlib 中的一个定义，位于命名空间 `WithTop.L
inearOrderedAddCommGroup`。
形式化陈述：{G : Type u_1} → [AddCommGroup G] → Sub (WithTop G)
参数：WithTop G。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `G` has subtraction, we can extend the subtraction to `WithTop G`, by setting
 `x - ⊤ = ⊤` and
`⊤ - x = ⊤`. This definition is only registered as an instance on additive commu
tative groups, to
avoid conflicting with the instance `WithTop.instSub` on types with a bottom ele
ment.
-/
instance instSub : Sub (WithTop G) where
  sub
  | _, ⊤ => ⊤
  | ⊤, (b : G) => ⊤
  | (a : G), (b : G) => (a - b : G)
/-
**WithTop.LinearOrderedAddCommGroup.coe_neg** 是 Mathlib 中的一个定理，位于命名空间 `WithTop.L
inearOrderedAddCommGroup`。
形式化陈述：∀ {G : Type u_1} [inst : AddCommGroup G] (a : G), ↑(-a) = -↑a
参数：a : G；-a。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp, norm_cast] lemma coe_neg (a : G) : (↑(-a) : WithTop G) = -a := rfl
/-
**WithTop.LinearOrderedAddCommGroup.coe_sub** 是 Mathlib 中的一个定理，位于命名空间 `WithTop.L
inearOrderedAddCommGroup`。
形式化陈述：∀ {G : Type u_1} [inst : AddCommGroup G] (a b : G), ↑(a - b) = ↑a - ↑b
参数：a b : G；a - b。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp, norm_cast] lemma coe_sub (a b : G) : (↑(a - b) : WithTop G) = ↑a - ↑b := rfl
/-
**WithTop.LinearOrderedAddCommGroup.neg_top** 是 Mathlib 中的一个定理，位于命名空间 `WithTop.L
inearOrderedAddCommGroup`。
形式化陈述：∀ {G : Type u_1} [inst : AddCommGroup G], -⊤ = ⊤
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma neg_top : -(⊤ : WithTop G) = ⊤ := rfl
/-
**WithTop.LinearOrderedAddCommGroup.top_sub** 是 Mathlib 中的一个定理，位于命名空间 `WithTop.L
inearOrderedAddCommGroup`。
形式化陈述：∀ {G : Type u_1} [inst : AddCommGroup G] (x : WithTop G), ⊤ - x = ⊤
参数：x : WithTop G。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
@[simp] lemma top_sub (x : WithTop G) : ⊤ - x = ⊤ := by cases x <;> rfl
/-
**WithTop.LinearOrderedAddCommGroup.sub_top** 是 Mathlib 中的一个定理，位于命名空间 `WithTop.L
inearOrderedAddCommGroup`。
形式化陈述：∀ {G : Type u_1} [inst : AddCommGroup G] (x : WithTop G), x - ⊤ = ⊤
参数：x : WithTop G。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
@[simp] lemma sub_top (x : WithTop G) : x - ⊤ = ⊤ := by cases x <;> rfl
/-
**WithTop.LinearOrderedAddCommGroup.sub_eq_top_iff** 是 Mathlib 中的一个定理，位于命名空间 `Wi
thTop.LinearOrderedAddCommGroup`。
形式化陈述：∀ {G : Type u_1} [inst : AddCommGroup G] {x y : WithTop G}, x - y = ⊤ ↔ x 
= ⊤ ∨ y = ⊤
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `WithTop.LinearOrderedAddCommGroup.sub_top`：∀ {G : Type u_1} [inst : AddC
ommGroup G] (x : WithTop G), x - ⊤ = ⊤
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `or_self`：∀ (p : Prop), (p ∨ p) = p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `WithTop.LinearOrderedAddCommGroup.top_sub`：∀ {G : Type u_1} [inst : AddC
ommGroup G] (x : WithTop G), ⊤ - x = ⊤
· 使用定理 `or_false`：∀ (p : Prop), (p ∨ False) = p
· 使用定理 `or_true`：∀ (p : Prop), (p ∨ True) = True
-/
@[simp] lemma sub_eq_top_iff : x - y = ⊤ ↔ x = ⊤ ∨ y = ⊤ := by
  cases x <;> cases y <;> simp [← coe_sub]
/-
**WithTop.LinearOrderedAddCommGroup.** 是 Mathlib 中的一个实例，位于命名空间 `WithTop.LinearOr
deredAddCommGroup`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [LinearOrder G] [IsOrderedAddMonoid G] : LinearOrderedAddCommGroupWithTop (WithTop G) where
  __ := WithTop.linearOrderedAddCommMonoidWithTop
  sub_eq_add_neg a b := by cases a <;> cases b <;> simp [← coe_sub, ← coe_neg, sub_eq_add_neg]
  neg_top := WithTop.map_top _
  zsmul := zsmulRec
  add_neg_cancel_of_ne_top | (a : G), _ => mod_cast add_neg_cancel a

end WithTop.LinearOrderedAddCommGroup

