/-
Copyright (c) 2020 Aaron Anderson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Anderson
-/
module

public import Mathlib.Order.Bounds.Basic

/-!
# Intervals in Lattices

In this file, we provide instances of lattice structures on intervals within lattices.
Some of them depend on the order of the endpoints of the interval, and thus are not made
global instances. These are probably not all of the lattice instances that could be placed on these
intervals, but more can be added easily along the same lines when needed.

## Main definitions

In the following, `*` can represent either `c`, `o`, or `i`.
  * `Set.Ic*.orderBot`
  * `Set.Ii*.semilatticeInf`
  * `Set.I*c.orderTop`
  * `Set.I*c.semilatticeInf`
  * `Set.I**.lattice`
  * `Set.Iic.boundedOrder`, within an `OrderBot`
  * `Set.Ici.boundedOrder`, within an `OrderTop`
-/

public section


variable {α : Type*}

namespace Set

namespace Ico

/-
**Set.Ico.semilatticeInf** 是 Mathlib 中的一个实例，位于命名空间 `Set.Ico`。
形式化陈述：semilatticeInf [SemilatticeInf α] {a b : α} : SemilatticeInf (Ico a b)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance semilatticeInf [SemilatticeInf α] {a b : α} : SemilatticeInf (Ico a b) :=
  Subtype.semilatticeInf fun _ _ hx hy => ⟨le_inf hx.1 hy.1, lt_of_le_of_lt inf_le_left hx.2⟩

@[simp, norm_cast]
/-
**Set.Ico.coe_inf** 是 Mathlib 中的一个定理，位于命名空间 `Set.Ico`。
形式化陈述：∀ {α : Type u_1} [inst : SemilatticeInf α] {a b : α} {x y : ↑(Set.Ico a b)
}, ↑(x ⊓ y) = ↑x ⊓ ↑y
参数：Set.Ico a b；x ⊓ y。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
protected lemma coe_inf [SemilatticeInf α] {a b : α} {x y : Ico a b} :
    ↑(x ⊓ y) = (↑x ⊓ ↑y : α) :=
  rfl

/-- `Ico a b` has a bottom element whenever `a < b`. -/
/-
**Set.Ico.orderBot** 是 Mathlib 中的一个实例，位于命名空间 `Set.Ico`。
形式化陈述：orderBot [PartialOrder α] {a b : α} [Fact (a < b)] : OrderBot (Ico a b)
参数：a < b。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`Ico a b` has a bottom element whenever `a < b`.
-/
instance orderBot [PartialOrder α] {a b : α} [Fact (a < b)] : OrderBot (Ico a b) :=
  (isLeast_Ico Fact.out).orderBot

@[simp, norm_cast]
/-
**Set.Ico.coe_bot** 是 Mathlib 中的一个定理，位于命名空间 `Set.Ico`。
形式化陈述：∀ {α : Type u_1} [inst : PartialOrder α] (a b : α) [inst_1 : Fact (a < b)]
, ↑⊥ = a
参数：a b : α；a < b。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
protected lemma coe_bot [PartialOrder α] (a b : α) [Fact (a < b)] : ↑(⊥ : Ico a b) = a := rfl
/-
**Set.Ico.disjoint_iff** 是 Mathlib 中的一个定理，位于命名空间 `Set.Ico`。
形式化陈述：∀ {α : Type u_1} [inst : SemilatticeInf α] {a b : α} [inst_1 : Fact (a < b
)] {x y : ↑(Set.Ico a b)},   Disjoint x y ↔ ↑x ⊓ ↑y = a
参数：a < b；Set.Ico a b。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
protected lemma disjoint_iff [SemilatticeInf α] {a b : α} [Fact (a < b)] {x y : Ico a b} :
    Disjoint x y ↔ ↑x ⊓ ↑y = a := by
  simp [_root_.disjoint_iff, Subtype.ext_iff]

end Ico

namespace Iio

/-
**Set.Iio.semilatticeInf** 是 Mathlib 中的一个实例，位于命名空间 `Set.Iio`。
形式化陈述：semilatticeInf [SemilatticeInf α] {a : α} : SemilatticeInf (Iio a)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance semilatticeInf [SemilatticeInf α] {a : α} : SemilatticeInf (Iio a) :=
  Subtype.semilatticeInf fun _ _ hx _ => lt_of_le_of_lt inf_le_left hx

@[simp, norm_cast]
/-
**Set.Iio.coe_inf** 是 Mathlib 中的一个定理，位于命名空间 `Set.Iio`。
形式化陈述：∀ {α : Type u_1} [inst : SemilatticeInf α] {a : α} {x y : ↑(Set.Iio a)}, ↑
(x ⊓ y) = ↑x ⊓ ↑y
参数：Set.Iio a；x ⊓ y。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
protected lemma coe_inf [SemilatticeInf α] {a : α} {x y : Iio a} :
    ↑(x ⊓ y) = (↑x ⊓ ↑y : α) :=
  rfl

end Iio

namespace Ioc

/-
**Set.Ioc.semilatticeSup** 是 Mathlib 中的一个实例，位于命名空间 `Set.Ioc`。
形式化陈述：semilatticeSup [SemilatticeSup α] {a b : α} : SemilatticeSup (Ioc a b)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance semilatticeSup [SemilatticeSup α] {a b : α} : SemilatticeSup (Ioc a b) :=
  Subtype.semilatticeSup fun _ _ hx hy => ⟨lt_of_lt_of_le hx.1 le_sup_left, sup_le hx.2 hy.2⟩

@[simp, norm_cast]
/-
**Set.Ioc.coe_sup** 是 Mathlib 中的一个定理，位于命名空间 `Set.Ioc`。
形式化陈述：∀ {α : Type u_1} [inst : SemilatticeSup α] {a b : α} {x y : ↑(Set.Ioc a b)
}, ↑(x ⊔ y) = ↑x ⊔ ↑y
参数：Set.Ioc a b；x ⊔ y。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
protected lemma coe_sup [SemilatticeSup α] {a b : α} {x y : Ioc a b} :
    ↑(x ⊔ y) = (↑x ⊔ ↑y : α) :=
  rfl

/-- `Ioc a b` has a top element whenever `a < b`. -/
/-
**Set.Ioc.orderTop** 是 Mathlib 中的一个实例，位于命名空间 `Set.Ioc`。
形式化陈述：orderTop [PartialOrder α] {a b : α} [Fact (a < b)] : OrderTop (Ioc a b)
参数：a < b。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`Ioc a b` has a top element whenever `a < b`.
-/
instance orderTop [PartialOrder α] {a b : α} [Fact (a < b)] : OrderTop (Ioc a b) :=
  (isGreatest_Ioc Fact.out).orderTop

@[simp, norm_cast]
/-
**Set.Ioc.coe_top** 是 Mathlib 中的一个定理，位于命名空间 `Set.Ioc`。
形式化陈述：∀ {α : Type u_1} [inst : PartialOrder α] (a b : α) [inst_1 : Fact (a < b)]
, ↑⊤ = b
参数：a b : α；a < b。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
protected lemma coe_top [PartialOrder α] (a b : α) [Fact (a < b)] : ↑(⊤ : Ioc a b) = b := rfl
/-
**Set.Ioc.codisjoint_iff** 是 Mathlib 中的一个定理，位于命名空间 `Set.Ioc`。
形式化陈述：∀ {α : Type u_1} [inst : SemilatticeSup α] {a b : α} [inst_1 : Fact (a < b
)] {x y : ↑(Set.Ioc a b)},   Codisjoint x y ↔ ↑x ⊔ ↑y = b
参数：a < b；Set.Ioc a b。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
protected lemma codisjoint_iff [SemilatticeSup α] {a b : α} [Fact (a < b)] {x y : Ioc a b} :
    Codisjoint x y ↔ ↑x ⊔ ↑y = b := by
  simp [_root_.codisjoint_iff, Subtype.ext_iff]

end Ioc

namespace Ioi

/-
**Set.Ioi.semilatticeSup** 是 Mathlib 中的一个实例，位于命名空间 `Set.Ioi`。
形式化陈述：semilatticeSup [SemilatticeSup α] {a : α} : SemilatticeSup (Ioi a)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance semilatticeSup [SemilatticeSup α] {a : α} : SemilatticeSup (Ioi a) :=
  Subtype.semilatticeSup fun _ _ hx _ => lt_of_lt_of_le hx le_sup_left

@[simp, norm_cast]
/-
**Set.Ioi.coe_sup** 是 Mathlib 中的一个定理，位于命名空间 `Set.Ioi`。
形式化陈述：∀ {α : Type u_1} [inst : SemilatticeSup α] {a : α} {x y : ↑(Set.Ioi a)}, ↑
(x ⊔ y) = ↑x ⊔ ↑y
参数：Set.Ioi a；x ⊔ y。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
protected lemma coe_sup [SemilatticeSup α] {a : α} {x y : Ioi a} :
    ↑(x ⊔ y) = (↑x ⊔ ↑y : α) :=
  rfl

end Ioi

namespace Iic

variable {a : α}

/-
**Set.Iic.semilatticeInf** 是 Mathlib 中的一个实例，位于命名空间 `Set.Iic`。
形式化陈述：semilatticeInf [SemilatticeInf α] : SemilatticeInf (Iic a)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance semilatticeInf [SemilatticeInf α] : SemilatticeInf (Iic a) :=
  Subtype.semilatticeInf fun _ _ hx _ => le_trans inf_le_left hx

@[simp, norm_cast]
/-
**Set.Iic.coe_inf** 是 Mathlib 中的一个定理，位于命名空间 `Set.Iic`。
形式化陈述：∀ {α : Type u_1} {a : α} [inst : SemilatticeInf α] {x y : ↑(Set.Iic a)}, ↑
(x ⊓ y) = ↑x ⊓ ↑y
参数：Set.Iic a；x ⊓ y。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
protected lemma coe_inf [SemilatticeInf α] {x y : Iic a} :
    ↑(x ⊓ y) = (↑x ⊓ ↑y : α) :=
  rfl
/-
**Set.Iic.semilatticeSup** 是 Mathlib 中的一个实例，位于命名空间 `Set.Iic`。
形式化陈述：semilatticeSup [SemilatticeSup α] : SemilatticeSup (Iic a)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `sup_le`：sup_le : a <= c -> b <= c -> a ⊔ b <= c
-/
instance semilatticeSup [SemilatticeSup α] : SemilatticeSup (Iic a) :=
  Subtype.semilatticeSup fun _ _ hx hy => sup_le hx hy

@[simp, norm_cast]
/-
**Set.Iic.coe_sup** 是 Mathlib 中的一个定理，位于命名空间 `Set.Iic`。
形式化陈述：∀ {α : Type u_1} {a : α} [inst : SemilatticeSup α] {x y : ↑(Set.Iic a)}, ↑
(x ⊔ y) = ↑x ⊔ ↑y
参数：Set.Iic a；x ⊔ y。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
protected lemma coe_sup [SemilatticeSup α] {x y : Iic a} :
    ↑(x ⊔ y) = (↑x ⊔ ↑y : α) :=
  rfl
/-
**Set.Iic.** 是 Mathlib 中的一个实例，位于命名空间 `Set.Iic`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Lattice α] : Lattice (Iic a) :=
  { Iic.semilatticeInf, Iic.semilatticeSup with }
/-
**Set.Iic.orderTop** 是 Mathlib 中的一个实例，位于命名空间 `Set.Iic`。
形式化陈述：orderTop [Preorder α] : OrderTop (Iic a) where top
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
-/
instance orderTop [Preorder α] :
    OrderTop (Iic a) where
  top := ⟨a, le_refl a⟩
  le_top x := x.prop

@[simp, norm_cast]
/-
**Set.Iic.coe_top** 是 Mathlib 中的一个定理，位于命名空间 `Set.Iic`。
形式化陈述：∀ {α : Type u_1} [inst : Preorder α] (a : α), ↑⊤ = a
参数：a : α。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
protected lemma coe_top [Preorder α] (a : α) : (⊤ : Iic a) = a := rfl
/-
**Set.Iic.eq_top_iff** 是 Mathlib 中的一个定理，位于命名空间 `Set.Iic`。
形式化陈述：∀ {α : Type u_1} {a : α} [inst : Preorder α] {x : ↑(Set.Iic a)}, x = ⊤ ↔ ↑
x = a
参数：Set.Iic a。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
protected lemma eq_top_iff [Preorder α] {x : Iic a} :
    x = ⊤ ↔ (x : α) = a := by
  simp [Subtype.ext_iff]
/-
**Set.Iic.orderBot** 是 Mathlib 中的一个实例，位于命名空间 `Set.Iic`。
形式化陈述：orderBot [Preorder α] [OrderBot α] : OrderBot (Iic a) where bot
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance orderBot [Preorder α] [OrderBot α] :
    OrderBot (Iic a) where
  bot := ⟨⊥, bot_le⟩
  bot_le := fun ⟨_, _⟩ => Subtype.mk_le_mk.2 bot_le

@[simp, norm_cast]
/-
**Set.Iic.coe_bot** 是 Mathlib 中的一个定理，位于命名空间 `Set.Iic`。
形式化陈述：∀ {α : Type u_1} [inst : Preorder α] [inst_1 : OrderBot α] (a : α), ↑⊥ = ⊥
参数：a : α。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
protected lemma coe_bot [Preorder α] [OrderBot α] (a : α) : (⊥ : Iic a) = (⊥ : α) := rfl
/-
**Set.Iic.** 是 Mathlib 中的一个实例，位于命名空间 `Set.Iic`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Preorder α] [OrderBot α] : BoundedOrder (Iic a) :=
  { Iic.orderTop, Iic.orderBot with }
/-
**Set.Iic.disjoint_iff** 是 Mathlib 中的一个定理，位于命名空间 `Set.Iic`。
形式化陈述：∀ {α : Type u_1} {a : α} [inst : SemilatticeInf α] [inst_1 : OrderBot α] {
x y : ↑(Set.Iic a)},   Disjoint x y ↔ Disjoint ↑x ↑y
参数：Set.Iic a。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
protected lemma disjoint_iff [SemilatticeInf α] [OrderBot α] {x y : Iic a} :
    Disjoint x y ↔ Disjoint (x : α) (y : α) := by
  simp [_root_.disjoint_iff, Subtype.ext_iff]
/-
**Set.Iic.codisjoint_iff** 是 Mathlib 中的一个定理，位于命名空间 `Set.Iic`。
形式化陈述：∀ {α : Type u_1} {a : α} [inst : SemilatticeSup α] {x y : ↑(Set.Iic a)}, C
odisjoint x y ↔ ↑x ⊔ ↑y = a
参数：Set.Iic a。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.Iic.eq_top_iff`：∀ {α : Type u_1} {a : α} [inst : Preorder α] {x : ↑(
Set.Iic a)}, x = ⊤ ↔ ↑x = a
-/
protected lemma codisjoint_iff [SemilatticeSup α] {x y : Iic a} :
    Codisjoint x y ↔ ↑x ⊔ ↑y = a := by
  simpa only [_root_.codisjoint_iff] using! Iic.eq_top_iff
/-
**Set.Iic.isCompl_iff** 是 Mathlib 中的一个定理，位于命名空间 `Set.Iic`。
形式化陈述：∀ {α : Type u_1} {a : α} [inst : Lattice α] [inst_1 : OrderBot α] {x y : ↑
(Set.Iic a)},   IsCompl x y ↔ Disjoint ↑x ↑y ∧ ↑x ⊔ ↑y = a
参数：Set.Iic a。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `isCompl_iff`：isCompl_iff [PartialOrder α] [BoundedOrder α] {a b : α} : I
sCompl a b ↔ Disjoint a b ∧ Codisjoint a b
· 使用定理 `Set.Iic.disjoint_iff`：∀ {α : Type u_1} {a : α} [inst : SemilatticeInf α]
 [inst_1 : OrderBot α] {x y : ↑(Set.Iic a)},   Disjoint x y ↔ Disjoint ↑x ↑y
· 使用定理 `Set.Iic.codisjoint_iff`：∀ {α : Type u_1} {a : α} [inst : SemilatticeSup 
α] {x y : ↑(Set.Iic a)}, Codisjoint x y ↔ ↑x ⊔ ↑y = a
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
protected lemma isCompl_iff [Lattice α] [OrderBot α] {x y : Iic a} :
    IsCompl x y ↔ Disjoint (x : α) (y : α) ∧ ↑x ⊔ ↑y = a := by
  rw [_root_.isCompl_iff, Iic.disjoint_iff, Iic.codisjoint_iff]
/-
**Set.Iic.complementedLattice_iff** 是 Mathlib 中的一个定理，位于命名空间 `Set.Iic`。
形式化陈述：∀ {α : Type u_1} {a : α} [inst : Lattice α] [inst_1 : OrderBot α],   Compl
ementedLattice ↑(Set.Iic a) ↔ ∀ b ≤ a, ∃ c ≤ a, b ⊓ c = ⊥ ∧ b ⊔ c = a
参数：Set.Iic a。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `exists_prop_congr`：∀ {p p' : Prop} {q q' : p → Prop}, (∀ (h : p), q h ↔ 
q' h) → ∀ (hp : p ↔ p'), Exists q ↔ ∃ (h : p'), q' ⋯
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
protected lemma complementedLattice_iff [Lattice α] [OrderBot α] :
    ComplementedLattice (Iic a) ↔ ∀ b, b ≤ a → ∃ c ≤ a, b ⊓ c = ⊥ ∧ b ⊔ c = a := by
  simp_rw [complementedLattice_iff, Iic.isCompl_iff, Subtype.forall, Subtype.exists, disjoint_iff,
    exists_prop, Set.mem_Iic]

end Iic

namespace Ici

/-
**Set.Ici.semilatticeInf** 是 Mathlib 中的一个实例，位于命名空间 `Set.Ici`。
形式化陈述：semilatticeInf [SemilatticeInf α] {a : α} : SemilatticeInf (Ici a)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `le_inf`：∀ {α : Type u} [inst : SemilatticeInf α] {c a b : α}, c ≤ a → c 
≤ b → c ≤ a ⊓ b
-/
instance semilatticeInf [SemilatticeInf α] {a : α} : SemilatticeInf (Ici a) :=
  Subtype.semilatticeInf fun _ _ hx hy => le_inf hx hy

@[simp, norm_cast]
/-
**Set.Ici.coe_inf** 是 Mathlib 中的一个定理，位于命名空间 `Set.Ici`。
形式化陈述：∀ {α : Type u_1} [inst : SemilatticeInf α] {a : α} {x y : ↑(Set.Ici a)}, ↑
(x ⊓ y) = ↑x ⊓ ↑y
参数：Set.Ici a；x ⊓ y。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
protected lemma coe_inf [SemilatticeInf α] {a : α} {x y : Ici a} :
    ↑(x ⊓ y) = (↑x ⊓ ↑y : α) :=
  rfl
/-
**Set.Ici.semilatticeSup** 是 Mathlib 中的一个实例，位于命名空间 `Set.Ici`。
形式化陈述：semilatticeSup [SemilatticeSup α] {a : α} : SemilatticeSup (Ici a)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance semilatticeSup [SemilatticeSup α] {a : α} : SemilatticeSup (Ici a) :=
  Subtype.semilatticeSup fun _ _ hx _ => le_trans hx le_sup_left

@[simp, norm_cast]
/-
**Set.Ici.coe_sup** 是 Mathlib 中的一个定理，位于命名空间 `Set.Ici`。
形式化陈述：∀ {α : Type u_1} [inst : SemilatticeSup α] {a : α} {x y : ↑(Set.Ici a)}, ↑
(x ⊔ y) = ↑x ⊔ ↑y
参数：Set.Ici a；x ⊔ y。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
protected lemma coe_sup [SemilatticeSup α] {a : α} {x y : Ici a} :
    ↑(x ⊔ y) = (↑x ⊔ ↑y : α) :=
  rfl
/-
**Set.Ici.lattice** 是 Mathlib 中的一个实例，位于命名空间 `Set.Ici`。
形式化陈述：lattice [Lattice α] {a : α} : Lattice (Ici a)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance lattice [Lattice α] {a : α} : Lattice (Ici a) :=
  { Ici.semilatticeInf, Ici.semilatticeSup with }
/-
**Set.Ici.distribLattice** 是 Mathlib 中的一个实例，位于命名空间 `Set.Ici`。
形式化陈述：distribLattice [DistribLattice α] {a : α} : DistribLattice (Ici a)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance distribLattice [DistribLattice α] {a : α} : DistribLattice (Ici a) :=
  { Ici.lattice with le_sup_inf := fun _ _ _ => le_sup_inf }
/-
**Set.Ici.orderBot** 是 Mathlib 中的一个实例，位于命名空间 `Set.Ici`。
形式化陈述：orderBot [Preorder α] {a : α} : OrderBot (Ici a) where bot
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
-/
instance orderBot [Preorder α] {a : α} :
    OrderBot (Ici a) where
  bot := ⟨a, le_refl a⟩
  bot_le x := x.prop

@[simp, norm_cast]
/-
**Set.Ici.coe_bot** 是 Mathlib 中的一个定理，位于命名空间 `Set.Ici`。
形式化陈述：∀ {α : Type u_1} [inst : Preorder α] (a : α), ↑⊥ = a
参数：a : α。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
protected lemma coe_bot [Preorder α] (a : α) : ↑(⊥ : Ici a) = a := rfl
/-
**Set.Ici.orderTop** 是 Mathlib 中的一个实例，位于命名空间 `Set.Ici`。
形式化陈述：orderTop [Preorder α] [OrderTop α] {a : α} : OrderTop (Ici a) where top
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance orderTop [Preorder α] [OrderTop α] {a : α} :
    OrderTop (Ici a) where
  top := ⟨⊤, le_top⟩
  le_top := fun ⟨_, _⟩ => Subtype.mk_le_mk.2 le_top

@[simp, norm_cast]
/-
**Set.Ici.coe_top** 是 Mathlib 中的一个定理，位于命名空间 `Set.Ici`。
形式化陈述：∀ {α : Type u_1} [inst : Preorder α] [inst_1 : OrderTop α] (a : α), ↑⊤ = ⊤
参数：a : α。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
protected lemma coe_top [Preorder α] [OrderTop α] (a : α) : ↑(⊤ : Ici a) = (⊤ : α) := rfl
/-
**Set.Ici.boundedOrder** 是 Mathlib 中的一个实例，位于命名空间 `Set.Ici`。
形式化陈述：boundedOrder [Preorder α] [OrderTop α] {a : α} : BoundedOrder (Ici a)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance boundedOrder [Preorder α] [OrderTop α] {a : α} : BoundedOrder (Ici a) :=
  { Ici.orderTop, Ici.orderBot with }
/-
**Set.Ici.disjoint_iff** 是 Mathlib 中的一个定理，位于命名空间 `Set.Ici`。
形式化陈述：∀ {α : Type u_1} [inst : SemilatticeInf α] {a : α} {x y : ↑(Set.Ici a)}, D
isjoint x y ↔ ↑x ⊓ ↑y = a
参数：Set.Ici a。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
protected lemma disjoint_iff [SemilatticeInf α] {a : α} {x y : Ici a} :
    Disjoint x y ↔ ↑x ⊓ ↑y = a := by
  simp [_root_.disjoint_iff, Subtype.ext_iff]
/-
**Set.Ici.codisjoint_iff** 是 Mathlib 中的一个定理，位于命名空间 `Set.Ici`。
形式化陈述：∀ {α : Type u_1} [inst : SemilatticeSup α] [inst_1 : OrderTop α] {a : α} {
x y : ↑(Set.Ici a)},   Codisjoint x y ↔ Codisjoint ↑x ↑y
参数：Set.Ici a。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
protected lemma codisjoint_iff [SemilatticeSup α] [OrderTop α] {a : α} {x y : Ici a} :
    Codisjoint x y ↔ Codisjoint (x : α) (y : α) := by
  simp [_root_.codisjoint_iff, Subtype.ext_iff]
/-
**Set.Ici.isCompl_iff** 是 Mathlib 中的一个定理，位于命名空间 `Set.Ici`。
形式化陈述：∀ {α : Type u_1} [inst : Lattice α] [inst_1 : OrderTop α] {a : α} {x y : ↑
(Set.Ici a)},   IsCompl x y ↔ ↑x ⊓ ↑y = a ∧ Codisjoint ↑x ↑y
参数：Set.Ici a。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `isCompl_iff`：isCompl_iff [PartialOrder α] [BoundedOrder α] {a b : α} : I
sCompl a b ↔ Disjoint a b ∧ Codisjoint a b
· 使用定理 `Set.Ici.disjoint_iff`：∀ {α : Type u_1} [inst : SemilatticeInf α] {a : α}
 {x y : ↑(Set.Ici a)}, Disjoint x y ↔ ↑x ⊓ ↑y = a
· 使用定理 `Set.Ici.codisjoint_iff`：∀ {α : Type u_1} [inst : SemilatticeSup α] [inst
_1 : OrderTop α] {a : α} {x y : ↑(Set.Ici a)},   Codisjoint x y ↔ Codisjoint ↑x 
↑y
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
protected lemma isCompl_iff [Lattice α] [OrderTop α] {a : α} {x y : Ici a} :
    IsCompl x y ↔ ↑x ⊓ ↑y = a ∧ Codisjoint (x : α) (y : α) := by
  rw [_root_.isCompl_iff, Ici.disjoint_iff, Ici.codisjoint_iff]

end Ici

namespace Icc

variable {a b : α}

/-
**Set.Icc.semilatticeInf** 是 Mathlib 中的一个实例，位于命名空间 `Set.Icc`。
形式化陈述：semilatticeInf [SemilatticeInf α] : SemilatticeInf (Icc a b)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance semilatticeInf [SemilatticeInf α] : SemilatticeInf (Icc a b) :=
  Subtype.semilatticeInf fun _ _ hx hy => ⟨le_inf hx.1 hy.1, le_trans inf_le_left hx.2⟩

@[simp, norm_cast]
/-
**Set.Icc.coe_inf** 是 Mathlib 中的一个定理，位于命名空间 `Set.Icc`。
形式化陈述：∀ {α : Type u_1} {a b : α} [inst : SemilatticeInf α] {x y : ↑(Set.Icc a b)
}, ↑(x ⊓ y) = ↑x ⊓ ↑y
参数：Set.Icc a b；x ⊓ y。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
protected lemma coe_inf [SemilatticeInf α] {x y : Icc a b} :
    ↑(x ⊓ y) = (↑x ⊓ ↑y : α) :=
  rfl
/-
**Set.Icc.semilatticeSup** 是 Mathlib 中的一个实例，位于命名空间 `Set.Icc`。
形式化陈述：semilatticeSup [SemilatticeSup α] : SemilatticeSup (Icc a b)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance semilatticeSup [SemilatticeSup α] : SemilatticeSup (Icc a b) :=
  Subtype.semilatticeSup fun _ _ hx hy => ⟨le_trans hx.1 le_sup_left, sup_le hx.2 hy.2⟩

@[simp, norm_cast]
/-
**Set.Icc.coe_sup** 是 Mathlib 中的一个定理，位于命名空间 `Set.Icc`。
形式化陈述：∀ {α : Type u_1} {a b : α} [inst : SemilatticeSup α] {x y : ↑(Set.Icc a b)
}, ↑(x ⊔ y) = ↑x ⊔ ↑y
参数：Set.Icc a b；x ⊔ y。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
protected lemma coe_sup [SemilatticeSup α] {x y : Icc a b} :
    ↑(x ⊔ y) = (↑x ⊔ ↑y : α) :=
  rfl
/-
**Set.Icc.lattice** 是 Mathlib 中的一个实例，位于命名空间 `Set.Icc`。
形式化陈述：lattice [Lattice α] : Lattice (Icc a b)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance lattice [Lattice α] : Lattice (Icc a b) :=
  { Icc.semilatticeInf, Icc.semilatticeSup with }

/-- `Icc a b` has a bottom element whenever `a ≤ b`. -/
/-
**Set.Icc.** 是 Mathlib 中的一个实例，位于命名空间 `Set.Icc`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`Icc a b` has a bottom element whenever `a ≤ b`.
-/
instance [Preorder α] [Fact (a ≤ b)] : OrderBot (Icc a b) :=
  (isLeast_Icc Fact.out).orderBot

@[simp, norm_cast]
/-
**Set.Icc.coe_bot** 是 Mathlib 中的一个定理，位于命名空间 `Set.Icc`。
形式化陈述：∀ {α : Type u_1} [inst : Preorder α] (a b : α) [inst_1 : Fact (a ≤ b)], ↑⊥
 = a
参数：a b : α；a ≤ b。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
protected lemma coe_bot [Preorder α] (a b : α) [Fact (a ≤ b)] : ↑(⊥ : Icc a b) = a := rfl

/-- `Icc a b` has a top element whenever `a ≤ b`. -/
/-
**Set.Icc.** 是 Mathlib 中的一个实例，位于命名空间 `Set.Icc`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`Icc a b` has a top element whenever `a ≤ b`.
-/
instance [Preorder α] [Fact (a ≤ b)] : OrderTop (Icc a b) :=
  (isGreatest_Icc Fact.out).orderTop

@[simp, norm_cast]
/-
**Set.Icc.coe_top** 是 Mathlib 中的一个定理，位于命名空间 `Set.Icc`。
形式化陈述：∀ {α : Type u_1} [inst : Preorder α] (a b : α) [inst_1 : Fact (a ≤ b)], ↑⊤
 = b
参数：a b : α；a ≤ b。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
protected lemma coe_top [Preorder α] (a b : α) [Fact (a ≤ b)] : ↑(⊤ : Icc a b) = b := rfl

/-- `Icc a b` is a `BoundedOrder` whenever `a ≤ b`. -/
/-
**Set.Icc.** 是 Mathlib 中的一个实例，位于命名空间 `Set.Icc`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`Icc a b` is a `BoundedOrder` whenever `a ≤ b`.
-/
instance [Preorder α] [Fact (a ≤ b)] : BoundedOrder (Icc a b) where
/-
**Set.Icc.disjoint_iff** 是 Mathlib 中的一个定理，位于命名空间 `Set.Icc`。
形式化陈述：∀ {α : Type u_1} {a b : α} [inst : SemilatticeInf α] [inst_1 : Fact (a ≤ b
)] {x y : ↑(Set.Icc a b)},   Disjoint x y ↔ ↑x ⊓ ↑y = a
参数：a ≤ b；Set.Icc a b。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
protected lemma disjoint_iff [SemilatticeInf α] [Fact (a ≤ b)] {x y : Icc a b} :
    Disjoint x y ↔ ↑x ⊓ ↑y = a := by
  simp [_root_.disjoint_iff, Subtype.ext_iff]
/-
**Set.Icc.codisjoint_iff** 是 Mathlib 中的一个定理，位于命名空间 `Set.Icc`。
形式化陈述：∀ {α : Type u_1} {a b : α} [inst : SemilatticeSup α] [inst_1 : Fact (a ≤ b
)] {x y : ↑(Set.Icc a b)},   Codisjoint x y ↔ ↑x ⊔ ↑y = b
参数：a ≤ b；Set.Icc a b。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
protected lemma codisjoint_iff [SemilatticeSup α] [Fact (a ≤ b)] {x y : Icc a b} :
    Codisjoint x y ↔ ↑x ⊔ (y : α) = b := by
  simp [_root_.codisjoint_iff, Subtype.ext_iff]
/-
**Set.Icc.isCompl_iff** 是 Mathlib 中的一个定理，位于命名空间 `Set.Icc`。
形式化陈述：∀ {α : Type u_1} {a b : α} [inst : Lattice α] [inst_1 : Fact (a ≤ b)] {x y
 : ↑(Set.Icc a b)},   IsCompl x y ↔ ↑x ⊓ ↑y = a ∧ ↑x ⊔ ↑y = b
参数：a ≤ b；Set.Icc a b。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `isCompl_iff`：isCompl_iff [PartialOrder α] [BoundedOrder α] {a b : α} : I
sCompl a b ↔ Disjoint a b ∧ Codisjoint a b
· 使用定理 `Set.Icc.disjoint_iff`：∀ {α : Type u_1} {a b : α} [inst : SemilatticeInf 
α] [inst_1 : Fact (a ≤ b)] {x y : ↑(Set.Icc a b)},   Disjoint x y ↔ ↑x ⊓ ↑y = a
· 使用定理 `Set.Icc.codisjoint_iff`：∀ {α : Type u_1} {a b : α} [inst : SemilatticeSu
p α] [inst_1 : Fact (a ≤ b)] {x y : ↑(Set.Icc a b)},   Codisjoint x y ↔ ↑x ⊔ ↑y 
= b
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
protected lemma isCompl_iff [Lattice α] [Fact (a ≤ b)] {x y : Icc a b} :
    IsCompl x y ↔ ↑x ⊓ ↑y = a ∧ ↑x ⊔ ↑y = b := by
  rw [_root_.isCompl_iff, Icc.disjoint_iff, Icc.codisjoint_iff]

end Icc

end Set

