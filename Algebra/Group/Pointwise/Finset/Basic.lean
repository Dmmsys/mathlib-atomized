/-
Copyright (c) 2020 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn, Yaël Dillies
-/
module

public import Mathlib.Algebra.Group.Pointwise.Set.Finite
public import Mathlib.Algebra.Group.Pointwise.Set.ListOfFn
public import Mathlib.Algebra.Order.Monoid.Unbundled.WithTop
public import Mathlib.Data.Finset.Max
public import Mathlib.Data.Finset.NAry
public import Mathlib.Data.Finset.Preimage

/-!
# Pointwise operations of finsets

This file defines pointwise algebraic operations on finsets.

## Main declarations

For finsets `s` and `t`:
* `0` (`Finset.zero`): The singleton `{0}`.
* `1` (`Finset.one`): The singleton `{1}`.
* `-s` (`Finset.neg`): Negation, finset of all `-x` where `x ∈ s`.
* `s⁻¹` (`Finset.inv`): Inversion, finset of all `x⁻¹` where `x ∈ s`.
* `s + t` (`Finset.add`): Addition, finset of all `x + y` where `x ∈ s` and `y ∈ t`.
* `s * t` (`Finset.mul`): Multiplication, finset of all `x * y` where `x ∈ s` and `y ∈ t`.
* `s - t` (`Finset.sub`): Subtraction, finset of all `x - y` where `x ∈ s` and `y ∈ t`.
* `s / t` (`Finset.div`): Division, finset of all `x / y` where `x ∈ s` and `y ∈ t`.

For `α` a semigroup/monoid, `Finset α` is a semigroup/monoid.
As an unfortunate side effect, this means that `n • s`, where `n : ℕ`, is ambiguous between
pointwise scaling and repeated pointwise addition; the former has `(2 : ℕ) • {1, 2} = {2, 4}`, while
the latter has `(2 : ℕ) • {1, 2} = {2, 3, 4}`. See note [pointwise nat action].

## Implementation notes

We put all instances in the scope `Pointwise`, so that these instances are not available by
default. Note that we do not mark them as reducible (as argued by note [reducible non-instances])
since we expect the scope to be open whenever the instances are actually used (and making the
instances reducible changes the behavior of `simp`).

## Tags

finset multiplication, finset addition, pointwise addition, pointwise multiplication,
pointwise subtraction
-/

@[expose] public section

assert_not_exists Cardinal Finset.dens MonoidWithZero MulAction IsOrderedMonoid

open Function MulOpposite

open scoped Pointwise

variable {F α β γ : Type*}

namespace Finset

/-! ### `0`/`1` as finsets -/

section One

variable [One α] {s : Finset α} {a : α}

/-- The finset `1 : Finset α` is defined as `{1}` in scope `Pointwise`. -/
@[to_additive (attr := instance_reducible)
  /-- The finset `0 : Finset α` is defined as `{0}` in scope `Pointwise`. -/]
/-
**Finset.one** 是 Mathlib 中的一个定义，位于命名空间 `Finset`。
形式化陈述：{α : Type u_2} → [One α] → One (Finset α)
参数：Finset α。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
protected def one : One (Finset α) :=
  ⟨{1}⟩

scoped[Pointwise] attribute [instance] Finset.one Finset.zero

@[to_additive (attr := simp)]
/-
**Finset.mem_one** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：mem_one : a in (1 : Finset α) ↔ a = 1
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.mem_singleton`：mem_singleton {a b : α} : b in ({a} : Finset α) ↔ 
b = a
-/
theorem mem_one : a ∈ (1 : Finset α) ↔ a = 1 :=
  mem_singleton

@[to_additive (attr := simp, norm_cast)]
/-
**Finset.coe_one** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：coe_one : ↑(1 : Finset α) = (1 : Set α)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.coe_singleton`：coe_singleton (a : α) : (({a} : Finset α) : Set α)
 = {a}
-/
theorem coe_one : ↑(1 : Finset α) = (1 : Set α) :=
  coe_singleton 1

@[to_additive (attr := simp, norm_cast)]
/-
**Finset.coe_eq_one** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
形式化陈述：coe_eq_one : (s : Set α) = 1 ↔ s = 1
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.coe_eq_singleton`：coe_eq_singleton {s : Finset α} {a : α} : (s : 
Set α) = {a} ↔ s = {a}
-/
lemma coe_eq_one : (s : Set α) = 1 ↔ s = 1 := coe_eq_singleton

@[to_additive (attr := simp)]
/-
**Finset.one_subset** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：one_subset : (1 : Finset α) subseteq s ↔ (1 : α) in s
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.singleton_subset_iff`：singleton_subset_iff {s : Finset α} {a : α}
 : {a} subseteq s ↔ a in s
-/
theorem one_subset : (1 : Finset α) ⊆ s ↔ (1 : α) ∈ s :=
  singleton_subset_iff

-- TODO: This would be a good simp lemma scoped to `Pointwise`, but it seems `@[simp]` can't be
-- scoped
@[to_additive]
/-
**Finset.singleton_one** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：singleton_one : ({1} : Finset α) = 1
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem singleton_one : ({1} : Finset α) = 1 :=
  rfl

@[to_additive]
/-
**Finset.one_mem_one** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：one_mem_one : (1 : α) in (1 : Finset α)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.mem_singleton_self`：mem_singleton_self (a : α) : a in ({a} : Fins
et α)
-/
theorem one_mem_one : (1 : α) ∈ (1 : Finset α) :=
  mem_singleton_self _

@[to_additive (attr := simp, aesop safe apply (rule_sets := [finsetNonempty]))]
/-
**Finset.one_nonempty** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：one_nonempty : (1 : Finset α).Nonempty
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.one_mem_one`：one_mem_one : (1 : α) in (1 : Finset α)
-/
theorem one_nonempty : (1 : Finset α).Nonempty :=
  ⟨1, one_mem_one⟩

@[to_additive (attr := simp)]
/-
**Finset.map_one** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：∀ {α : Type u_2} {β : Type u_3} [inst : One α] {f : α ↪ β}, Finset.map f 1
 = {f 1}
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.map_singleton`：map_singleton (f : α ↪ β) (a : α) : map f {a} = {f
 a}
-/
protected theorem map_one {f : α ↪ β} : map f 1 = {f 1} :=
  map_singleton f 1

@[to_additive (attr := simp)]
/-
**Finset.image_one** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：image_one [DecidableEq β] {f : α -> β} : image f 1 = {f 1}
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.image_singleton`：image_singleton (f : α -> β) (a : α) : image f {
a} = {f a}
-/
theorem image_one [DecidableEq β] {f : α → β} : image f 1 = {f 1} :=
  image_singleton _ _

@[to_additive]
/-
**Finset.subset_one_iff_eq** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：subset_one_iff_eq : s subseteq 1 ↔ s = ∅ ∨ s = 1
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.subset_singleton_iff`：subset_singleton_iff {s : Finset α} {a : α}
 : s subseteq {a} ↔ s = ∅ ∨ s = {a}
-/
theorem subset_one_iff_eq : s ⊆ 1 ↔ s = ∅ ∨ s = 1 :=
  subset_singleton_iff

@[to_additive]
/-
**Finset.Nonempty.subset_one_iff** 是 Mathlib 中的一个定理，位于命名空间 `Finset.Nonempty`。
形式化陈述：∀ {α : Type u_2} [inst : One α] {s : Finset α}, s.Nonempty → (s ⊆ 1 ↔ s = 
1)
参数：s ⊆ 1 ↔ s = 1。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.Nonempty.subset_singleton_iff`：∀ {α : Type u_1} {s : Finset α} {a
 : α}, s.Nonempty → (s ⊆ {a} ↔ s = {a})
-/
theorem Nonempty.subset_one_iff (h : s.Nonempty) : s ⊆ 1 ↔ s = 1 :=
  h.subset_singleton_iff

@[to_additive (attr := simp)]
/-
**Finset.card_one** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：card_one : #(1 : Finset α) = 1
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.card_singleton`：card_singleton (a : α) : #{a} = 1
-/
theorem card_one : #(1 : Finset α) = 1 :=
  card_singleton _

/-- The singleton operation as a `OneHom`. -/
@[to_additive /-- The singleton operation as a `ZeroHom`. -/]
/-
**Finset.singletonOneHom** 是 Mathlib 中的一个定义，位于命名空间 `Finset`。
形式化陈述：singletonOneHom : OneHom α (Finset α) where toFun
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.singleton_one`：singleton_one : ({1} : Finset α) = 1

--- 原说明 ---
The singleton operation as a `OneHom`.
-/
def singletonOneHom : OneHom α (Finset α) where
  toFun := singleton; map_one' := singleton_one

@[to_additive (attr := simp)]
/-
**Finset.coe_singletonOneHom** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：coe_singletonOneHom : (singletonOneHom : α -> Finset α) = singleton
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_singletonOneHom : (singletonOneHom : α → Finset α) = singleton :=
  rfl

@[to_additive (attr := simp)]
/-
**Finset.singletonOneHom_apply** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：singletonOneHom_apply (a : α) : singletonOneHom a = {a}
参数：a : α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem singletonOneHom_apply (a : α) : singletonOneHom a = {a} :=
  rfl

/-- Lift a `OneHom` to `Finset` via `image`. -/
@[to_additive (attr := simps) /-- Lift a `ZeroHom` to `Finset` via `image` -/]
/-
**Finset.imageOneHom** 是 Mathlib 中的一个定义，位于命名空间 `Finset`。
形式化陈述：imageOneHom [DecidableEq β] [One β] [FunLike F α β] [OneHomClass F α β] (f
 : F) : OneHom (Finset α) (Finset β) where toFun
参数：f : F。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Lift a `OneHom` to `Finset` via `image`.
-/
def imageOneHom [DecidableEq β] [One β] [FunLike F α β] [OneHomClass F α β] (f : F) :
    OneHom (Finset α) (Finset β) where
  toFun := Finset.image f
  map_one' := by rw [image_one, map_one, singleton_one]

@[to_additive (attr := simp)]
/-
**Finset.sup_one** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
形式化陈述：sup_one [SemilatticeSup β] [OrderBot β] (f : α -> β) : sup 1 f = f 1
参数：f : α -> β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.sup_singleton`：sup_singleton {b : β} : ({b} : Finset β).sup f = f
 b
-/
lemma sup_one [SemilatticeSup β] [OrderBot β] (f : α → β) : sup 1 f = f 1 := sup_singleton

@[to_additive (attr := simp)]
/-
**Finset.sup'_one** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：∀ {α : Type u_2} {β : Type u_3} [inst : One α] [inst_1 : SemilatticeSup β]
 (f : α → β), Finset.sup' 1 ⋯ f = f 1
参数：f : α → β。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Finset.sup'`：sup'_one [SemilatticeSup β] (f : α -> β) : sup' 1 one_nonem
pty f = f 1
· 使用定理 `Finset.one_nonempty`：one_nonempty : (1 : Finset α).Nonempty
-/
lemma sup'_one [SemilatticeSup β] (f : α → β) : sup' 1 one_nonempty f = f 1 := rfl

@[to_additive (attr := simp)]
/-
**Finset.inf_one** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
形式化陈述：inf_one [SemilatticeInf β] [OrderTop β] (f : α -> β) : inf 1 f = f 1
参数：f : α -> β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.inf_singleton`：∀ {α : Type u_2} {β : Type u_3} [inst : Semilattic
eInf α] [inst_1 : OrderTop α] {f : β → α} {b : β}, {b}.inf f = f b
-/
lemma inf_one [SemilatticeInf β] [OrderTop β] (f : α → β) : inf 1 f = f 1 := inf_singleton

@[to_additive (attr := simp)]
/-
**Finset.inf'_one** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：∀ {α : Type u_2} {β : Type u_3} [inst : One α] [inst_1 : SemilatticeInf β]
 (f : α → β), Finset.inf' 1 ⋯ f = f 1
参数：f : α → β。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Finset.inf'`：inf'_one [SemilatticeInf β] (f : α -> β) : inf' 1 one_nonem
pty f = f 1
· 使用定理 `Finset.one_nonempty`：one_nonempty : (1 : Finset α).Nonempty
-/
lemma inf'_one [SemilatticeInf β] (f : α → β) : inf' 1 one_nonempty f = f 1 := rfl

@[to_additive (attr := simp)]
/-
**Finset.max_one** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
形式化陈述：max_one [LinearOrder α] : (1 : Finset α).max = 1
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma max_one [LinearOrder α] : (1 : Finset α).max = 1 := rfl

@[to_additive (attr := simp)]
/-
**Finset.min_one** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
形式化陈述：min_one [LinearOrder α] : (1 : Finset α).min = 1
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma min_one [LinearOrder α] : (1 : Finset α).min = 1 := rfl

@[to_additive (attr := simp)]
/-
**Finset.max'_one** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：∀ {α : Type u_2} [inst : One α] [inst_1 : LinearOrder α], Finset.max' 1 ⋯ 
= 1
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Finset.max'`：max'_one [LinearOrder α] : (1 : Finset α).max' one_nonempty
 = 1
· 使用定理 `Finset.one_nonempty`：one_nonempty : (1 : Finset α).Nonempty
-/
lemma max'_one [LinearOrder α] : (1 : Finset α).max' one_nonempty = 1 := rfl

@[to_additive (attr := simp)]
/-
**Finset.min'_one** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：∀ {α : Type u_2} [inst : One α] [inst_1 : LinearOrder α], Finset.min' 1 ⋯ 
= 1
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Finset.min'`：min'_one [LinearOrder α] : (1 : Finset α).min' one_nonempty
 = 1
· 使用定理 `Finset.one_nonempty`：one_nonempty : (1 : Finset α).Nonempty
-/
lemma min'_one [LinearOrder α] : (1 : Finset α).min' one_nonempty = 1 := rfl

@[to_additive (attr := simp)]
/-
**Finset.image_op_one** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
形式化陈述：image_op_one [DecidableEq α] : (1 : Finset α).image op = 1
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma image_op_one [DecidableEq α] : (1 : Finset α).image op = 1 := rfl

@[to_additive (attr := simp)]
/-
**Finset.map_op_one** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
形式化陈述：map_op_one : (1 : Finset α).map opEquiv.toEmbedding = 1
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma map_op_one : (1 : Finset α).map opEquiv.toEmbedding = 1 := rfl

@[to_additive (attr := simp)]
/-
**Finset.one_product_one** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
形式化陈述：one_product_one [One β] : (1 ×ˢ 1 : Finset (α × β)) = 1
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.ext`：ext {s₁ s₂ : Finset α} (h : forall a, a in s₁ ↔ a in s₂) : s
₁ = s₂
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma one_product_one [One β] : (1 ×ˢ 1 : Finset (α × β)) = 1 := by ext; simp [Prod.ext_iff]

end One

/-! ### Finset negation/inversion -/

section Inv

variable [DecidableEq α] [Inv α] {s t : Finset α} {a : α}

/-- The pointwise inversion of finset `s⁻¹` is defined as `{x⁻¹ | x ∈ s}` in scope `Pointwise`. -/
@[to_additive (attr := instance_reducible)
  /-- The pointwise negation of finset `-s` is defined as `{-x | x ∈ s}` in scope `Pointwise`. -/]
/-
**Finset.inv** 是 Mathlib 中的一个定义，位于命名空间 `Finset`。
形式化陈述：{α : Type u_2} → [DecidableEq α] → [Inv α] → Inv (Finset α)
参数：Finset α。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
protected def inv : Inv (Finset α) :=
  ⟨image Inv.inv⟩

scoped[Pointwise] attribute [instance] Finset.inv Finset.neg

@[to_additive]
/-
**Finset.inv_def** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：inv_def : s⁻¹ = s.image fun x => x⁻¹
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem inv_def : s⁻¹ = s.image fun x => x⁻¹ :=
  rfl
/-
**Finset.image_inv_eq_inv** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：∀ {α : Type u_2} [inst : DecidableEq α] [inst_1 : Inv α] (s : Finset α), F
inset.image (fun x => x⁻¹) s = s⁻¹
参数：s : Finset α；fun x => x⁻¹。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[to_additive] lemma image_inv_eq_inv (s : Finset α) : s.image (·⁻¹) = s⁻¹ := rfl

@[to_additive]
/-
**Finset.mem_inv** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：mem_inv {x : α} : x in s⁻¹ ↔ exists y in s, y⁻¹ = x
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.mem_image`：mem_image : b in s.image f ↔ exists a in s, f a = b
-/
theorem mem_inv {x : α} : x ∈ s⁻¹ ↔ ∃ y ∈ s, y⁻¹ = x :=
  mem_image

@[to_additive]
/-
**Finset.inv_mem_inv** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：inv_mem_inv (ha : a in s) : a⁻¹ in s⁻¹
参数：ha : a in s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.mem_image_of_mem`：mem_image_of_mem (f : α -> β) {a} (h : a in s) 
: f a in s.image f
-/
theorem inv_mem_inv (ha : a ∈ s) : a⁻¹ ∈ s⁻¹ :=
  mem_image_of_mem _ ha

@[to_additive]
/-
**Finset.card_inv_le** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：card_inv_le : #s⁻¹ <= #s
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.card_image_le`：card_image_le [DecidableEq β] : #(s.image f) <= #s
-/
theorem card_inv_le : #s⁻¹ ≤ #s :=
  card_image_le

@[to_additive (attr := simp)]
/-
**Finset.inv_empty** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：inv_empty : (∅ : Finset α)⁻¹ = ∅
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem inv_empty : (∅ : Finset α)⁻¹ = ∅ :=
  rfl

@[to_additive (attr := simp)]
/-
**Finset.inv_nonempty_iff** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：inv_nonempty_iff : s⁻¹.Nonempty ↔ s.Nonempty
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Finset.image_nonempty`：image_nonempty : (s.image f).Nonempty ↔ s.Nonempt
y
-/
theorem inv_nonempty_iff : s⁻¹.Nonempty ↔ s.Nonempty := image_nonempty

alias ⟨Nonempty.of_inv, Nonempty.inv⟩ := inv_nonempty_iff

attribute [to_additive] Nonempty.inv Nonempty.of_inv
attribute [aesop safe apply (rule_sets := [finsetNonempty])] Nonempty.inv Nonempty.neg

@[to_additive (attr := simp)]
/-
**Finset.inv_eq_empty** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：inv_eq_empty : s⁻¹ = ∅ ↔ s = ∅
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.image_eq_empty`：image_eq_empty : s.image f = ∅ ↔ s = ∅
-/
theorem inv_eq_empty : s⁻¹ = ∅ ↔ s = ∅ := image_eq_empty

@[to_additive (attr := mono, gcongr)]
/-
**Finset.inv_subset_inv** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：inv_subset_inv (h : s subseteq t) : s⁻¹ subseteq t⁻¹
参数：h : s subseteq t。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.image_subset_image`：image_subset_image {s₁ s₂ : Finset α} (h : s₁
 subseteq s₂) : s₁.image f subseteq s₂.image f
-/
theorem inv_subset_inv (h : s ⊆ t) : s⁻¹ ⊆ t⁻¹ :=
  image_subset_image h

@[to_additive (attr := simp)]
/-
**Finset.inv_singleton** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：inv_singleton (a : α) : ({a} : Finset α)⁻¹ = {a⁻¹}
参数：a : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.image_singleton`：image_singleton (f : α -> β) (a : α) : image f {
a} = {f a}
-/
theorem inv_singleton (a : α) : ({a} : Finset α)⁻¹ = {a⁻¹} :=
  image_singleton _ _

@[to_additive (attr := simp)]
/-
**Finset.inv_insert** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：inv_insert (a : α) (s : Finset α) : (insert a s)⁻¹ = insert a⁻¹ s⁻¹
参数：a : α；s : Finset α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.image_insert`：image_insert [DecidableEq α] (f : α -> β) (a : α) (
s : Finset α) : (insert a s).image f = insert (f a) (s.image f)
-/
theorem inv_insert (a : α) (s : Finset α) : (insert a s)⁻¹ = insert a⁻¹ s⁻¹ :=
  image_insert _ _ _

@[to_additive (attr := simp)]
/-
**Finset.sup_inv** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
形式化陈述：sup_inv [SemilatticeSup β] [OrderBot β] (s : Finset α) (f : α -> β) : sup 
s⁻¹ f = sup s (f ·⁻¹)
参数：s : Finset α；f : α -> β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.sup_image`：sup_image [DecidableEq β] (s : Finset γ) (f : γ -> β) 
(g : β -> α) : (s.image f).sup g = s.sup (g ∘ f)
-/
lemma sup_inv [SemilatticeSup β] [OrderBot β] (s : Finset α) (f : α → β) :
    sup s⁻¹ f = sup s (f ·⁻¹) :=
  sup_image ..

@[to_additive (attr := simp)]
/-
**Finset.sup'_inv** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：∀ {α : Type u_2} {β : Type u_3} [inst : DecidableEq α] [inst_1 : Inv α] [i
nst_2 : SemilatticeSup β] {s : Finset α}   (hs : s⁻¹.Nonempty) (f : α → β), s⁻¹.
sup' hs f = s.sup' ⋯ fun x => f x⁻¹
参数：hs : s⁻¹.Nonempty；f : α → β。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.sup'_image`：∀ {α : Type u_2} {β : Type u_3} {γ : Type u_4} [inst 
: SemilatticeSup α] [inst_1 : DecidableEq β] {s : Finset γ}   {f : γ → β} (hs : 
(Finset…
-/
lemma sup'_inv [SemilatticeSup β] {s : Finset α} (hs : s⁻¹.Nonempty) (f : α → β) :
    sup' s⁻¹ hs f = sup' s hs.of_inv (f ·⁻¹) :=
  sup'_image ..

@[to_additive (attr := simp)]
/-
**Finset.inf_inv** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
形式化陈述：inf_inv [SemilatticeInf β] [OrderTop β] (s : Finset α) (f : α -> β) : inf 
s⁻¹ f = inf s (f ·⁻¹)
参数：s : Finset α；f : α -> β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.inf_image`：∀ {α : Type u_2} {β : Type u_3} {γ : Type u_4} [inst :
 SemilatticeInf α] [inst_1 : OrderTop α] [inst_2 : DecidableEq β]   (s : Finset 
γ) (f …
-/
lemma inf_inv [SemilatticeInf β] [OrderTop β] (s : Finset α) (f : α → β) :
    inf s⁻¹ f = inf s (f ·⁻¹) :=
  inf_image ..

@[to_additive (attr := simp)]
/-
**Finset.inf'_inv** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：∀ {α : Type u_2} {β : Type u_3} [inst : DecidableEq α] [inst_1 : Inv α] [i
nst_2 : SemilatticeInf β] {s : Finset α}   (hs : s⁻¹.Nonempty) (f : α → β), s⁻¹.
inf' hs f = s.inf' ⋯ fun x => f x⁻¹
参数：hs : s⁻¹.Nonempty；f : α → β。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.inf'_image`：∀ {α : Type u_2} {β : Type u_3} {γ : Type u_4} [inst 
: SemilatticeInf α] [inst_1 : DecidableEq β] {s : Finset γ}   {f : γ → β} (hs : 
(Finset…
-/
lemma inf'_inv [SemilatticeInf β] {s : Finset α} (hs : s⁻¹.Nonempty) (f : α → β) :
    inf' s⁻¹ hs f = inf' s hs.of_inv (f ·⁻¹) :=
  inf'_image ..
/-
**Finset.image_op_inv** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：∀ {α : Type u_2} [inst : DecidableEq α] [inst_1 : Inv α] (s : Finset α),  
 Finset.image MulOpposite.op s⁻¹ = (Finset.image MulOpposite.op s)⁻¹
参数：s : Finset α；Finset.image MulOpposite.op s。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.image_comm`：image_comm {β'} [DecidableEq β'] [DecidableEq γ] {f :
 β -> γ} {g : α -> β} {f' : α -> β'} {g' : β' -> γ} (h_comm : forall a, f (g a) 
= g' (f…
· 使用定理 `MulOpposite.op_inv`：∀ {α : Type u_1} [inst : Inv α] (x : α), MulOpposite
.op x⁻¹ = (MulOpposite.op x)⁻¹
-/
@[to_additive] lemma image_op_inv (s : Finset α) : s⁻¹.image op = (s.image op)⁻¹ :=
  image_comm op_inv

@[to_additive]
/-
**Finset.map_op_inv** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
形式化陈述：map_op_inv (s : Finset α) : s⁻¹.map opEquiv.toEmbedding = (s.map opEquiv.t
oEmbedding)⁻¹
参数：s : Finset α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.map_eq_image`：map_eq_image (f : α ↪ β) (s : Finset α) : s.map f =
 s.image f
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `MulOpposite.opEquiv_apply`：∀ {α : Type u_1}, ⇑MulOpposite.opEquiv = MulO
pposite.op
· 使用定理 `Finset.image_op_inv`：∀ {α : Type u_2} [inst : DecidableEq α] [inst_1 : I
nv α] (s : Finset α),   Finset.image MulOpposite.op s⁻¹ = (Finset.image MulOppos
ite.op s)…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma map_op_inv (s : Finset α) : s⁻¹.map opEquiv.toEmbedding = (s.map opEquiv.toEmbedding)⁻¹ := by
  simp [map_eq_image, image_op_inv]

end Inv

open scoped Pointwise

section InvolutiveInv
variable [DecidableEq α] [InvolutiveInv α] {s : Finset α} {a : α}

@[to_additive (attr := simp)]
/-
**Finset.mem_inv'** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
形式化陈述：mem_inv' : a in s⁻¹ ↔ a⁻¹ in s
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma mem_inv' : a ∈ s⁻¹ ↔ a⁻¹ ∈ s := by simp [mem_inv, inv_eq_iff_eq_inv]

@[to_additive (attr := simp)]
/-
**Finset.inv_filter** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：inv_filter (s : Finset α) (p : α -> Prop) [DecidablePred p] : ({x in s | p
 x} : Finset α)⁻¹ = {x in s⁻¹ | p x⁻¹}
参数：s : Finset α；p : α -> Prop。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.ext`：ext {s₁ s₂ : Finset α} (h : forall a, a in s₁ ↔ a in s₂) : s
₁ = s₂
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem inv_filter (s : Finset α) (p : α → Prop) [DecidablePred p] :
    ({x ∈ s | p x} : Finset α)⁻¹ = {x ∈ s⁻¹ | p x⁻¹} := by
  ext; simp

@[to_additive]
/-
**Finset.inv_filter_univ** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：inv_filter_univ (p : α -> Prop) [Fintype α] [DecidablePred p] : ({x | p x}
 : Finset α)⁻¹ = {x | p x⁻¹}
参数：p : α -> Prop。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.inv_filter`：inv_filter (s : Finset α) (p : α -> Prop) [DecidableP
red p] : ({x in s | p x} : Finset α)⁻¹ = {x in s⁻¹ | p x⁻¹}
· 使用定理 `Finset.coe_filter`：∀ {α : Type u_1} (p : α → Prop) [inst : DecidablePred
 p] (s : Finset α), ↑(Finset.filter p s) = {x | x ∈ s ∧ p x}
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem inv_filter_univ (p : α → Prop) [Fintype α] [DecidablePred p] :
    ({x | p x} : Finset α)⁻¹ = {x | p x⁻¹} := by
  simp

@[to_additive (attr := simp, norm_cast)]
/-
**Finset.coe_inv** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：coe_inv (s : Finset α) : ↑s⁻¹ = (s : Set α)⁻¹
参数：s : Finset α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Finset.coe_image`：coe_image : ↑(s.image f) = f '' ↑s
· 使用定理 `Set.image_inv_eq_inv`：image_inv_eq_inv : (·⁻¹) '' s = s⁻¹
-/
theorem coe_inv (s : Finset α) : ↑s⁻¹ = (s : Set α)⁻¹ := coe_image.trans Set.image_inv_eq_inv

@[to_additive (attr := simp)]
/-
**Finset.card_inv** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：card_inv (s : Finset α) : #s⁻¹ = #s
参数：s : Finset α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.card_image_of_injective`：card_image_of_injective [DecidableEq β] 
(s : Finset α) (H : Injective f) : #(s.image f) = #s
· 使用定理 `inv_injective`：inv_injective : Function.Injective (Inv.inv : G -> G)
-/
theorem card_inv (s : Finset α) : #s⁻¹ = #s := card_image_of_injective _ inv_injective

@[to_additive (attr := simp)]
/-
**Finset.preimage_inv** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：preimage_inv (s : Finset α) : s.preimage (·⁻¹) inv_injective.injOn = s⁻¹
参数：s : Finset α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.coe_injective`：coe_injective {α} : Injective ((↑) : Finset α -> S
et α)
· 使用定理 `Function.Injective.injOn`：∀ {α : Type u_1} {β : Type u_2} {f : α → β}, F
unction.Injective f → ∀ {s : Set α}, Set.InjOn f s
· 使用定理 `inv_injective`：inv_injective : Function.Injective (Inv.inv : G -> G)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.coe_preimage`：coe_preimage {f : α -> β} (s : Finset β) (hf : Set.
InjOn f (f ⁻¹' ↑s)) : (↑(preimage s f hf) : Set α) = f ⁻¹' ↑s
· 使用定理 `Set.inv_preimage`：inv_preimage : Inv.inv ⁻¹' s = s⁻¹
· 使用定理 `Finset.coe_inv`：coe_inv (s : Finset α) : ↑s⁻¹ = (s : Set α)⁻¹
-/
theorem preimage_inv (s : Finset α) : s.preimage (·⁻¹) inv_injective.injOn = s⁻¹ :=
  coe_injective <| by rw [coe_preimage, Set.inv_preimage, coe_inv]

@[to_additive (attr := simp)]
/-
**Finset.inv_univ** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
形式化陈述：inv_univ [Fintype α] : (univ : Finset α)⁻¹ = univ
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.ext`：ext {s₁ s₂ : Finset α} (h : forall a, a in s₁ ↔ a in s₂) : s
₁ = s₂
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma inv_univ [Fintype α] : (univ : Finset α)⁻¹ = univ := by ext; simp

@[to_additive (attr := simp)]
/-
**Finset.inv_inter** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
形式化陈述：inv_inter (s t : Finset α) : (s inter t)⁻¹ = s⁻¹ inter t⁻¹
参数：s t : Finset α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.coe_injective`：coe_injective {α} : Injective ((↑) : Finset α -> S
et α)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.coe_inv`：coe_inv (s : Finset α) : ↑s⁻¹ = (s : Set α)⁻¹
· 使用定理 `Finset.coe_inter`：coe_inter (s₁ s₂ : Finset α) : ↑(s₁ inter s₂) = (s₁ in
ter s₂ : Set α)
· 使用定理 `Set.inter_inv`：inter_inv : (s inter t)⁻¹ = s⁻¹ inter t⁻¹
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma inv_inter (s t : Finset α) : (s ∩ t)⁻¹ = s⁻¹ ∩ t⁻¹ := coe_injective <| by simp

@[to_additive (attr := simp)]
/-
**Finset.inv_product** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
形式化陈述：inv_product [DecidableEq β] [InvolutiveInv β] (s : Finset α) (t : Finset β
) : (s ×ˢ t)⁻¹ = s⁻¹ ×ˢ t⁻¹
参数：s : Finset α；t : Finset β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Set.inv_prod`：inv_prod [Inv β] (s : Set α) (t : Set β) : (s ×ˢ t)⁻¹ = s⁻
¹ ×ˢ t⁻¹
-/
lemma inv_product [DecidableEq β] [InvolutiveInv β] (s : Finset α) (t : Finset β) :
    (s ×ˢ t)⁻¹ = s⁻¹ ×ˢ t⁻¹ := mod_cast (s : Set α).inv_prod (t : Set β)

end InvolutiveInv

open scoped Pointwise

/-! ### Finset addition/multiplication -/


section Mul

variable [DecidableEq α] [Mul α] [Mul β] [FunLike F α β] [MulHomClass F α β]
  (f : F) {s s₁ s₂ t t₁ t₂ u : Finset α} {a b : α}

/-- The pointwise multiplication of finsets `s * t` and `t` is defined as `{x * y | x ∈ s, y ∈ t}`
in scope `Pointwise`. -/
@[to_additive (attr := instance_reducible)
  /-- The pointwise addition of finsets `s + t` is defined as `{x + y | x ∈ s, y ∈ t}` in
  scope `Pointwise`. -/]
/-
**Finset.mul** 是 Mathlib 中的一个定义，位于命名空间 `Finset`。
形式化陈述：{α : Type u_2} → [DecidableEq α] → [Mul α] → Mul (Finset α)
参数：Finset α。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
protected def mul : Mul (Finset α) :=
  ⟨image₂ (· * ·)⟩

scoped[Pointwise] attribute [instance] Finset.mul Finset.add

@[to_additive]
/-
**Finset.mul_def** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：mul_def : s * t = (s ×ˢ t).image fun p : α × α => p.1 * p.2
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem mul_def : s * t = (s ×ˢ t).image fun p : α × α => p.1 * p.2 :=
  rfl

@[to_additive]
/-
**Finset.image_mul_product** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：image_mul_product : ((s ×ˢ t).image fun x : α × α => x.fst * x.snd) = s * 
t
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem image_mul_product : ((s ×ˢ t).image fun x : α × α => x.fst * x.snd) = s * t :=
  rfl

@[to_additive]
/-
**Finset.mem_mul** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：mem_mul {x : α} : x in s * t ↔ exists y in s, exists z in t, y * z = x
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.mem_image₂`：mem_image₂ : c in image₂ f s t ↔ exists a in s, exist
s b in t, f a b = c
-/
theorem mem_mul {x : α} : x ∈ s * t ↔ ∃ y ∈ s, ∃ z ∈ t, y * z = x := mem_image₂

@[to_additive (attr := simp, norm_cast)]
/-
**Finset.coe_mul** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：coe_mul (s t : Finset α) : (↑(s * t) : Set α) = ↑s * ↑t
参数：s t : Finset α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.coe_image₂`：coe_image₂ (f : α -> β -> γ) (s : Finset α) (t : Fins
et β) : (image₂ f s t : Set γ) = Set.image2 f s t
-/
theorem coe_mul (s t : Finset α) : (↑(s * t) : Set α) = ↑s * ↑t :=
  coe_image₂ _ _ _

@[to_additive]
/-
**Finset.mul_mem_mul** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：mul_mem_mul : a in s -> b in t -> a * b in s * t
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.mem_image₂_of_mem`：mem_image₂_of_mem (ha : a in s) (hb : b in t) 
: f a b in image₂ f s t
-/
theorem mul_mem_mul : a ∈ s → b ∈ t → a * b ∈ s * t :=
  mem_image₂_of_mem

@[to_additive]
/-
**Finset.card_mul_le** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：card_mul_le : #(s * t) <= #s * #t
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.card_image₂_le`：card_image₂_le (f : α -> β -> γ) (s : Finset α) (
t : Finset β) : #(image₂ f s t) <= #s * #t
-/
theorem card_mul_le : #(s * t) ≤ #s * #t :=
  card_image₂_le _ _ _

@[to_additive]
/-
**Finset.card_mul_iff** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：card_mul_iff : #(s * t) = #s * #t ↔ (s ×ˢ t : Set (α × α)).InjOn fun p => 
p.1 * p.2
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.card_image₂_iff`：card_image₂_iff : #(image₂ f s t) = #s * #t ↔ (s
 ×ˢ t : Set (α × β)).InjOn fun x => f x.1 x.2
-/
theorem card_mul_iff :
    #(s * t) = #s * #t ↔ (s ×ˢ t : Set (α × α)).InjOn fun p => p.1 * p.2 :=
  card_image₂_iff

@[to_additive (attr := simp)]
/-
**Finset.empty_mul** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：empty_mul (s : Finset α) : ∅ * s = ∅
参数：s : Finset α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.image₂_empty_left`：image₂_empty_left : image₂ f ∅ t = ∅
-/
theorem empty_mul (s : Finset α) : ∅ * s = ∅ :=
  image₂_empty_left

@[to_additive (attr := simp)]
/-
**Finset.mul_empty** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：mul_empty (s : Finset α) : s * ∅ = ∅
参数：s : Finset α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.image₂_empty_right`：image₂_empty_right : image₂ f s ∅ = ∅
-/
theorem mul_empty (s : Finset α) : s * ∅ = ∅ :=
  image₂_empty_right

@[to_additive (attr := simp)]
/-
**Finset.mul_eq_empty** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：mul_eq_empty : s * t = ∅ ↔ s = ∅ ∨ t = ∅
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.image₂_eq_empty_iff`：image₂_eq_empty_iff : image₂ f s t = ∅ ↔ s =
 ∅ ∨ t = ∅
-/
theorem mul_eq_empty : s * t = ∅ ↔ s = ∅ ∨ t = ∅ :=
  image₂_eq_empty_iff

@[to_additive (attr := simp)]
/-
**Finset.mul_nonempty** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：mul_nonempty : (s * t).Nonempty ↔ s.Nonempty ∧ t.Nonempty
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.image₂_nonempty_iff`：image₂_nonempty_iff : (image₂ f s t).Nonempt
y ↔ s.Nonempty ∧ t.Nonempty
-/
theorem mul_nonempty : (s * t).Nonempty ↔ s.Nonempty ∧ t.Nonempty :=
  image₂_nonempty_iff

@[to_additive (attr := aesop safe apply (rule_sets := [finsetNonempty]))]
/-
**Finset.Nonempty.mul** 是 Mathlib 中的一个定理，位于命名空间 `Finset.Nonempty`。
形式化陈述：∀ {α : Type u_2} [inst : DecidableEq α] [inst_1 : Mul α] {s t : Finset α},
 s.Nonempty → t.Nonempty → (s * t).Nonempty
参数：s * t。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.Nonempty.image₂`：∀ {α : Type u_1} {β : Type u_3} {γ : Type u_5} [
inst : DecidableEq γ] {f : α → β → γ} {s : Finset α} {t : Finset β},   s.Nonempt
y → t.Nonemp…
-/
theorem Nonempty.mul : s.Nonempty → t.Nonempty → (s * t).Nonempty :=
  Nonempty.image₂

@[to_additive]
/-
**Finset.Nonempty.of_mul_left** 是 Mathlib 中的一个定理，位于命名空间 `Finset.Nonempty`。
形式化陈述：∀ {α : Type u_2} [inst : DecidableEq α] [inst_1 : Mul α] {s t : Finset α},
 (s * t).Nonempty → s.Nonempty
参数：s * t。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.Nonempty.of_image₂_left`：∀ {α : Type u_1} {β : Type u_3} {γ : Typ
e u_5} [inst : DecidableEq γ] {f : α → β → γ} {s : Finset α} {t : Finset β},   (
Finset.image₂ f s t)…
-/
theorem Nonempty.of_mul_left : (s * t).Nonempty → s.Nonempty :=
  Nonempty.of_image₂_left

@[to_additive]
/-
**Finset.Nonempty.of_mul_right** 是 Mathlib 中的一个定理，位于命名空间 `Finset.Nonempty`。
形式化陈述：∀ {α : Type u_2} [inst : DecidableEq α] [inst_1 : Mul α] {s t : Finset α},
 (s * t).Nonempty → t.Nonempty
参数：s * t。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.Nonempty.of_image₂_right`：∀ {α : Type u_1} {β : Type u_3} {γ : Ty
pe u_5} [inst : DecidableEq γ] {f : α → β → γ} {s : Finset α} {t : Finset β},   
(Finset.image₂ f s t)…
-/
theorem Nonempty.of_mul_right : (s * t).Nonempty → t.Nonempty :=
  Nonempty.of_image₂_right

@[to_additive (attr := simp)]
/-
**Finset.singleton_mul_singleton** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：singleton_mul_singleton (a b : α) : ({a} : Finset α) * {b} = {a * b}
参数：a b : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.image₂_singleton`：image₂_singleton : image₂ f {a} {b} = {f a b}
-/
theorem singleton_mul_singleton (a b : α) : ({a} : Finset α) * {b} = {a * b} :=
  image₂_singleton

@[to_additive]
/-
**Finset.mul_subset_mul** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：mul_subset_mul : s₁ subseteq s₂ -> t₁ subseteq t₂ -> s₁ * t₁ subseteq s₂ *
 t₂
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.image₂_subset`：image₂_subset (hs : s subseteq s') (ht : t subsete
q t') : image₂ f s t subseteq image₂ f s' t'
-/
theorem mul_subset_mul : s₁ ⊆ s₂ → t₁ ⊆ t₂ → s₁ * t₁ ⊆ s₂ * t₂ :=
  image₂_subset

@[to_additive]
/-
**Finset.mul_subset_mul_left** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：mul_subset_mul_left : t₁ subseteq t₂ -> s * t₁ subseteq s * t₂
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.image₂_subset_left`：image₂_subset_left (ht : t subseteq t') : ima
ge₂ f s t subseteq image₂ f s t'
-/
theorem mul_subset_mul_left : t₁ ⊆ t₂ → s * t₁ ⊆ s * t₂ :=
  image₂_subset_left

@[to_additive]
/-
**Finset.mul_subset_mul_right** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：mul_subset_mul_right : s₁ subseteq s₂ -> s₁ * t subseteq s₂ * t
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.image₂_subset_right`：image₂_subset_right (hs : s subseteq s') : i
mage₂ f s t subseteq image₂ f s' t
-/
theorem mul_subset_mul_right : s₁ ⊆ s₂ → s₁ * t ⊆ s₂ * t :=
  image₂_subset_right
/-
**Finset.** 是 Mathlib 中的一个实例，位于命名空间 `Finset`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[to_additive] instance : MulLeftMono (Finset α) where elim _s _t₁ _t₂ := mul_subset_mul_left
/-
**Finset.** 是 Mathlib 中的一个实例，位于命名空间 `Finset`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[to_additive] instance : MulRightMono (Finset α) where elim _t _s₁ _s₂ := mul_subset_mul_right

@[to_additive]
/-
**Finset.mul_subset_iff** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：mul_subset_iff : s * t subseteq u ↔ forall x in s, forall y in t, x * y in
 u
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.image₂_subset_iff`：image₂_subset_iff : image₂ f s t subseteq u ↔ 
forall x in s, forall y in t, f x y in u
-/
theorem mul_subset_iff : s * t ⊆ u ↔ ∀ x ∈ s, ∀ y ∈ t, x * y ∈ u :=
  image₂_subset_iff

@[to_additive]
/-
**Finset.union_mul** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：union_mul : (s₁ union s₂) * t = s₁ * t union s₂ * t
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.image₂_union_left`：image₂_union_left [DecidableEq α] : image₂ f (
s union s') t = image₂ f s t union image₂ f s' t
-/
theorem union_mul : (s₁ ∪ s₂) * t = s₁ * t ∪ s₂ * t :=
  image₂_union_left

@[to_additive]
/-
**Finset.mul_union** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：mul_union : s * (t₁ union t₂) = s * t₁ union s * t₂
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.image₂_union_right`：image₂_union_right [DecidableEq β] : image₂ f
 s (t union t') = image₂ f s t union image₂ f s t'
-/
theorem mul_union : s * (t₁ ∪ t₂) = s * t₁ ∪ s * t₂ :=
  image₂_union_right

@[to_additive]
/-
**Finset.inter_mul_subset** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：inter_mul_subset : s₁ inter s₂ * t subseteq s₁ * t inter (s₂ * t)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.image₂_inter_subset_left`：image₂_inter_subset_left [DecidableEq α
] : image₂ f (s inter s') t subseteq image₂ f s t inter image₂ f s' t
-/
theorem inter_mul_subset : s₁ ∩ s₂ * t ⊆ s₁ * t ∩ (s₂ * t) :=
  image₂_inter_subset_left

@[to_additive]
/-
**Finset.mul_inter_subset** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：mul_inter_subset : s * (t₁ inter t₂) subseteq s * t₁ inter (s * t₂)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.image₂_inter_subset_right`：image₂_inter_subset_right [DecidableEq
 β] : image₂ f s (t inter t') subseteq image₂ f s t inter image₂ f s t'
-/
theorem mul_inter_subset : s * (t₁ ∩ t₂) ⊆ s * t₁ ∩ (s * t₂) :=
  image₂_inter_subset_right

@[to_additive]
/-
**Finset.inter_mul_union_subset_union** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：inter_mul_union_subset_union : s₁ inter s₂ * (t₁ union t₂) subseteq s₁ * t
₁ union s₂ * t₂
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.image₂_inter_union_subset_union`：image₂_inter_union_subset_union 
: image₂ f (s inter s') (t union t') subseteq image₂ f s t union image₂ f s' t'
-/
theorem inter_mul_union_subset_union : s₁ ∩ s₂ * (t₁ ∪ t₂) ⊆ s₁ * t₁ ∪ s₂ * t₂ :=
  image₂_inter_union_subset_union

@[to_additive]
/-
**Finset.union_mul_inter_subset_union** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：union_mul_inter_subset_union : (s₁ union s₂) * (t₁ inter t₂) subseteq s₁ *
 t₁ union s₂ * t₂
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.image₂_union_inter_subset_union`：image₂_union_inter_subset_union 
: image₂ f (s union s') (t inter t') subseteq image₂ f s t union image₂ f s' t'
-/
theorem union_mul_inter_subset_union : (s₁ ∪ s₂) * (t₁ ∩ t₂) ⊆ s₁ * t₁ ∪ s₂ * t₂ :=
  image₂_union_inter_subset_union

/-- If a finset `u` is contained in the product of two sets `s * t`, we can find two finsets `s'`,
`t'` such that `s' ⊆ s`, `t' ⊆ t` and `u ⊆ s' * t'`. -/
@[to_additive
  /-- If a finset `u` is contained in the sum of two sets `s + t`, we can find two finsets
  `s'`, `t'` such that `s' ⊆ s`, `t' ⊆ t` and `u ⊆ s' + t'`. -/]
/-
**Finset.subset_mul** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：subset_mul {s t : Set α} : ↑u subseteq s * t -> exists s' t' : Finset α, ↑
s' subseteq s ∧ ↑t' subseteq t ∧ u subseteq s' * t'
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.subset_set_image₂`：subset_set_image₂ {s : Set α} {t : Set β} (hu 
: ↑u subseteq image2 f s t) : exists (s' : Finset α) (t' : Finset β), ↑s' subset
eq s ∧ ↑t' sub…
-/
theorem subset_mul {s t : Set α} :
    ↑u ⊆ s * t → ∃ s' t' : Finset α, ↑s' ⊆ s ∧ ↑t' ⊆ t ∧ u ⊆ s' * t' :=
  subset_set_image₂

@[to_additive]
/-
**Finset.image_mul** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：image_mul [DecidableEq β] : (s * t).image (f : α -> β) = s.image f * t.ima
ge f
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.image_image₂_distrib`：image_image₂_distrib {g : γ -> δ} {f' : α' 
-> β' -> δ} {g₁ : α -> α'} {g₂ : β -> β'} (h_distrib : forall a b, g (f a b) = f
' (g₁ a) (g₂ b)) …
· 使用定理 `map_mul`：map_mul [MulHomClass F M N] (f : F) (x y : M) : f (x * y) = f x
 * f y
-/
theorem image_mul [DecidableEq β] : (s * t).image (f : α → β) = s.image f * t.image f :=
  image_image₂_distrib <| map_mul f

@[to_additive]
/-
**Finset.image_op_mul** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
形式化陈述：image_op_mul (s t : Finset α) : (s * t).image op = t.image op * s.image op
参数：s t : Finset α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.image_image₂_antidistrib`：image_image₂_antidistrib {g : γ -> δ} {
f' : β' -> α' -> δ} {g₁ : β -> β'} {g₂ : α -> α'} (h_antidistrib : forall a b, g
 (f a b) = f' (g₁ b) …
· 使用定理 `MulOpposite.op_mul`：∀ {α : Type u_1} [inst : Mul α] (x y : α), MulOpposi
te.op (x * y) = MulOpposite.op y * MulOpposite.op x
-/
lemma image_op_mul (s t : Finset α) : (s * t).image op = t.image op * s.image op :=
  image_image₂_antidistrib op_mul

@[to_additive (attr := simp)]
/-
**Finset.product_mul_product_comm** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
形式化陈述：product_mul_product_comm [DecidableEq β] (s₁ s₂ : Finset α) (t₁ t₂ : Finse
t β) : (s₁ ×ˢ t₁) * (s₂ ×ˢ t₂) = (s₁ * s₂) ×ˢ (t₁ * t₂)
参数：s₁ s₂ : Finset α；t₁ t₂ : Finset β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Set.prod_mul_prod_comm`：prod_mul_prod_comm [Mul β] (s₁ s₂ : Set α) (t₁ t
₂ : Set β) : (s₁ ×ˢ t₁) * (s₂ ×ˢ t₂) = (s₁ * s₂) ×ˢ (t₁ * t₂)
-/
lemma product_mul_product_comm [DecidableEq β] (s₁ s₂ : Finset α) (t₁ t₂ : Finset β) :
    (s₁ ×ˢ t₁) * (s₂ ×ˢ t₂) = (s₁ * s₂) ×ˢ (t₁ * t₂) :=
  mod_cast (s₁ : Set α).prod_mul_prod_comm s₂ (t₁ : Set β) t₂

@[to_additive]
/-
**Finset.map_op_mul** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
形式化陈述：map_op_mul (s t : Finset α) : (s * t).map opEquiv.toEmbedding = t.map opEq
uiv.toEmbedding * s.map opEquiv.toEmbedding
参数：s t : Finset α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.map_eq_image`：map_eq_image (f : α ↪ β) (s : Finset α) : s.map f =
 s.image f
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `MulOpposite.opEquiv_apply`：∀ {α : Type u_1}, ⇑MulOpposite.opEquiv = MulO
pposite.op
· 使用引理 `Finset.image_op_mul`：image_op_mul (s t : Finset α) : (s * t).image op = 
t.image op * s.image op
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma map_op_mul (s t : Finset α) :
    (s * t).map opEquiv.toEmbedding = t.map opEquiv.toEmbedding * s.map opEquiv.toEmbedding := by
  simp [map_eq_image, image_op_mul]

/-- The singleton operation as a `MulHom`. -/
@[to_additive /-- The singleton operation as an `AddHom`. -/]
/-
**Finset.singletonMulHom** 是 Mathlib 中的一个定义，位于命名空间 `Finset`。
形式化陈述：singletonMulHom : α ->ₙ* Finset α where toFun
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The singleton operation as a `MulHom`.
-/
def singletonMulHom : α →ₙ* Finset α where
  toFun := singleton; map_mul' _ _ := (singleton_mul_singleton _ _).symm

@[to_additive (attr := simp)]
/-
**Finset.coe_singletonMulHom** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：coe_singletonMulHom : (singletonMulHom : α -> Finset α) = singleton
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_singletonMulHom : (singletonMulHom : α → Finset α) = singleton :=
  rfl

@[to_additive (attr := simp)]
/-
**Finset.singletonMulHom_apply** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：singletonMulHom_apply (a : α) : singletonMulHom a = {a}
参数：a : α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem singletonMulHom_apply (a : α) : singletonMulHom a = {a} :=
  rfl

/-- Lift a `MulHom` to `Finset` via `image`. -/
@[to_additive (attr := simps) /-- Lift an `AddHom` to `Finset` via `image` -/]
/-
**Finset.imageMulHom** 是 Mathlib 中的一个定义，位于命名空间 `Finset`。
形式化陈述：imageMulHom [DecidableEq β] : Finset α ->ₙ* Finset β where toFun
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.image_mul`：image_mul [DecidableEq β] : (s * t).image (f : α -> β)
 = s.image f * t.image f

--- 原说明 ---
Lift a `MulHom` to `Finset` via `image`.
-/
def imageMulHom [DecidableEq β] : Finset α →ₙ* Finset β where
  toFun := Finset.image f
  map_mul' _ _ := image_mul _

@[to_additive (attr := simp (default + 1))]
/-
**Finset.sup_mul_le** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
形式化陈述：sup_mul_le {β} [SemilatticeSup β] [OrderBot β] {s t : Finset α} {f : α -> 
β} {a : β} : sup (s * t) f <= a ↔ forall x in s, forall y in t, f (x * y) <= a
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Finset.sup_image₂_le`：sup_image₂_le {g : γ -> δ} {a : δ} : sup (image₂ f
 s t) g <= a ↔ forall x in s, forall y in t, g (f x y) <= a
-/
lemma sup_mul_le {β} [SemilatticeSup β] [OrderBot β] {s t : Finset α} {f : α → β} {a : β} :
    sup (s * t) f ≤ a ↔ ∀ x ∈ s, ∀ y ∈ t, f (x * y) ≤ a :=
  sup_image₂_le

@[to_additive]
/-
**Finset.sup_mul_left** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
形式化陈述：sup_mul_left {β} [SemilatticeSup β] [OrderBot β] (s t : Finset α) (f : α -
> β) : sup (s * t) f = sup s fun x => sup t (f <| x * ·)
参数：s t : Finset α；f : α -> β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Finset.sup_image₂_left`：sup_image₂_left (g : γ -> δ) : sup (image₂ f s t
) g = sup s fun x => sup t (g <| f x ·)
-/
lemma sup_mul_left {β} [SemilatticeSup β] [OrderBot β] (s t : Finset α) (f : α → β) :
    sup (s * t) f = sup s fun x ↦ sup t (f <| x * ·) :=
  sup_image₂_left ..

@[to_additive]
/-
**Finset.sup_mul_right** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
形式化陈述：sup_mul_right {β} [SemilatticeSup β] [OrderBot β] (s t : Finset α) (f : α 
-> β) : sup (s * t) f = sup t fun y => sup s (f <| · * y)
参数：s t : Finset α；f : α -> β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Finset.sup_image₂_right`：sup_image₂_right (g : γ -> δ) : sup (image₂ f s
 t) g = sup t fun y => sup s (g <| f · y)
-/
lemma sup_mul_right {β} [SemilatticeSup β] [OrderBot β] (s t : Finset α) (f : α → β) :
    sup (s * t) f = sup t fun y ↦ sup s (f <| · * y) :=
  sup_image₂_right ..

@[to_additive (attr := simp (default + 1))]
/-
**Finset.le_inf_mul** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
形式化陈述：le_inf_mul {β} [SemilatticeInf β] [OrderTop β] {s t : Finset α} {f : α -> 
β} {a : β} : a <= inf (s * t) f ↔ forall x in s, forall y in t, a <= f (x * y)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Finset.le_inf_image₂`：le_inf_image₂ {g : γ -> δ} {a : δ} : a <= inf (ima
ge₂ f s t) g ↔ forall x in s, forall y in t, a <= g (f x y)
-/
lemma le_inf_mul {β} [SemilatticeInf β] [OrderTop β] {s t : Finset α} {f : α → β} {a : β} :
    a ≤ inf (s * t) f ↔ ∀ x ∈ s, ∀ y ∈ t, a ≤ f (x * y) :=
  le_inf_image₂

@[to_additive]
/-
**Finset.inf_mul_left** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
形式化陈述：inf_mul_left {β} [SemilatticeInf β] [OrderTop β] (s t : Finset α) (f : α -
> β) : inf (s * t) f = inf s fun x => inf t (f <| x * ·)
参数：s t : Finset α；f : α -> β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Finset.inf_image₂_left`：inf_image₂_left (g : γ -> δ) : inf (image₂ f s t
) g = inf s fun x => inf t (g ∘ f x)
-/
lemma inf_mul_left {β} [SemilatticeInf β] [OrderTop β] (s t : Finset α) (f : α → β) :
    inf (s * t) f = inf s fun x ↦ inf t (f <| x * ·) :=
  inf_image₂_left ..

@[to_additive]
/-
**Finset.inf_mul_right** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
形式化陈述：inf_mul_right {β} [SemilatticeInf β] [OrderTop β] (s t : Finset α) (f : α 
-> β) : inf (s * t) f = inf t fun y => inf s (f <| · * y)
参数：s t : Finset α；f : α -> β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Finset.inf_image₂_right`：inf_image₂_right (g : γ -> δ) : inf (image₂ f s
 t) g = inf t fun y => inf s (g <| f · y)
-/
lemma inf_mul_right {β} [SemilatticeInf β] [OrderTop β] (s t : Finset α) (f : α → β) :
    inf (s * t) f = inf t fun y ↦ inf s (f <| · * y) :=
  inf_image₂_right ..

/--
See `card_le_card_mul_left` for a more convenient but less general version for types with a
left-cancellative multiplication.
-/
@[to_additive
/-- See `card_le_card_add_left` for a more convenient but less general version for types with a
left-cancellative addition. -/]
/-
**Finset.card_le_card_mul_left_of_injective** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
形式化陈述：card_le_card_mul_left_of_injective (has : a in s) (ha : IsLeftRegular a) :
 #t <= #(s * t)
参数：has : a in s；ha : IsLeftRegular a。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.card_le_card_image₂_left`：card_le_card_image₂_left {s : Finset α}
 (ha : a in s) (hf : Injective (f a)) : #t <= #(image₂ f s t)
-/
lemma card_le_card_mul_left_of_injective (has : a ∈ s) (ha : IsLeftRegular a) :
    #t ≤ #(s * t) :=
  card_le_card_image₂_left _ has ha

/--
See `card_le_card_mul_right` for a more convenient but less general version for types with a
right-cancellative multiplication.
-/
@[to_additive
/-- See `card_le_card_add_right` for a more convenient but less general version for types with a
right-cancellative addition. -/]
/-
**Finset.card_le_card_mul_right_of_injective** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
形式化陈述：card_le_card_mul_right_of_injective (hat : a in t) (ha : IsRightRegular a)
 : #s <= #(s * t)
参数：hat : a in t；ha : IsRightRegular a。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.card_le_card_image₂_right`：card_le_card_image₂_right {t : Finset 
β} (hb : b in t) (hf : Injective (f · b)) : #s <= #(image₂ f s t)
-/
lemma card_le_card_mul_right_of_injective (hat : a ∈ t) (ha : IsRightRegular a) :
    #s ≤ #(s * t) :=
  card_le_card_image₂_right _ hat ha

end Mul

/-! ### Finset subtraction/division -/

section Div

variable [DecidableEq α] [Div α] {s s₁ s₂ t t₁ t₂ u : Finset α} {a b : α}

/-- The pointwise division of finsets `s / t` is defined as `{x / y | x ∈ s, y ∈ t}` in locale
`Pointwise`. -/
@[to_additive (attr := instance_reducible)
  /-- The pointwise subtraction of finsets `s - t` is defined as `{x - y | x ∈ s, y ∈ t}`
  in scope `Pointwise`. -/]
/-
**Finset.div** 是 Mathlib 中的一个定义，位于命名空间 `Finset`。
形式化陈述：{α : Type u_2} → [DecidableEq α] → [Div α] → Div (Finset α)
参数：Finset α。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
protected def div : Div (Finset α) :=
  ⟨image₂ (· / ·)⟩

scoped[Pointwise] attribute [instance] Finset.div Finset.sub

@[to_additive]
/-
**Finset.div_def** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：div_def : s / t = (s ×ˢ t).image fun p : α × α => p.1 / p.2
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem div_def : s / t = (s ×ˢ t).image fun p : α × α => p.1 / p.2 :=
  rfl

@[to_additive]
/-
**Finset.image_div_product** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：image_div_product : ((s ×ˢ t).image fun x : α × α => x.fst / x.snd) = s / 
t
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem image_div_product : ((s ×ˢ t).image fun x : α × α => x.fst / x.snd) = s / t :=
  rfl

@[to_additive]
/-
**Finset.mem_div** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：mem_div : a in s / t ↔ exists b in s, exists c in t, b / c = a
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.mem_image₂`：mem_image₂ : c in image₂ f s t ↔ exists a in s, exist
s b in t, f a b = c
-/
theorem mem_div : a ∈ s / t ↔ ∃ b ∈ s, ∃ c ∈ t, b / c = a :=
  mem_image₂

@[to_additive (attr := simp, norm_cast)]
/-
**Finset.coe_div** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：coe_div (s t : Finset α) : (↑(s / t) : Set α) = ↑s / ↑t
参数：s t : Finset α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.coe_image₂`：coe_image₂ (f : α -> β -> γ) (s : Finset α) (t : Fins
et β) : (image₂ f s t : Set γ) = Set.image2 f s t
-/
theorem coe_div (s t : Finset α) : (↑(s / t) : Set α) = ↑s / ↑t :=
  coe_image₂ _ _ _

@[to_additive]
/-
**Finset.div_mem_div** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：div_mem_div : a in s -> b in t -> a / b in s / t
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.mem_image₂_of_mem`：mem_image₂_of_mem (ha : a in s) (hb : b in t) 
: f a b in image₂ f s t
-/
theorem div_mem_div : a ∈ s → b ∈ t → a / b ∈ s / t :=
  mem_image₂_of_mem

@[to_additive]
/-
**Finset.card_div_le** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：card_div_le : #(s / t) <= #s * #t
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.card_image₂_le`：card_image₂_le (f : α -> β -> γ) (s : Finset α) (
t : Finset β) : #(image₂ f s t) <= #s * #t
-/
theorem card_div_le : #(s / t) ≤ #s * #t :=
  card_image₂_le _ _ _

@[to_additive (attr := simp)]
/-
**Finset.empty_div** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：empty_div (s : Finset α) : ∅ / s = ∅
参数：s : Finset α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.image₂_empty_left`：image₂_empty_left : image₂ f ∅ t = ∅
-/
theorem empty_div (s : Finset α) : ∅ / s = ∅ :=
  image₂_empty_left

@[to_additive (attr := simp)]
/-
**Finset.div_empty** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：div_empty (s : Finset α) : s / ∅ = ∅
参数：s : Finset α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.image₂_empty_right`：image₂_empty_right : image₂ f s ∅ = ∅
-/
theorem div_empty (s : Finset α) : s / ∅ = ∅ :=
  image₂_empty_right

@[to_additive (attr := simp)]
/-
**Finset.div_eq_empty** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：div_eq_empty : s / t = ∅ ↔ s = ∅ ∨ t = ∅
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.image₂_eq_empty_iff`：image₂_eq_empty_iff : image₂ f s t = ∅ ↔ s =
 ∅ ∨ t = ∅
-/
theorem div_eq_empty : s / t = ∅ ↔ s = ∅ ∨ t = ∅ :=
  image₂_eq_empty_iff

@[to_additive (attr := simp)]
/-
**Finset.div_nonempty** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：div_nonempty : (s / t).Nonempty ↔ s.Nonempty ∧ t.Nonempty
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.image₂_nonempty_iff`：image₂_nonempty_iff : (image₂ f s t).Nonempt
y ↔ s.Nonempty ∧ t.Nonempty
-/
theorem div_nonempty : (s / t).Nonempty ↔ s.Nonempty ∧ t.Nonempty :=
  image₂_nonempty_iff

@[to_additive (attr := aesop safe apply (rule_sets := [finsetNonempty]))]
/-
**Finset.Nonempty.div** 是 Mathlib 中的一个定理，位于命名空间 `Finset.Nonempty`。
形式化陈述：∀ {α : Type u_2} [inst : DecidableEq α] [inst_1 : Div α] {s t : Finset α},
 s.Nonempty → t.Nonempty → (s / t).Nonempty
参数：s / t。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.Nonempty.image₂`：∀ {α : Type u_1} {β : Type u_3} {γ : Type u_5} [
inst : DecidableEq γ] {f : α → β → γ} {s : Finset α} {t : Finset β},   s.Nonempt
y → t.Nonemp…
-/
theorem Nonempty.div : s.Nonempty → t.Nonempty → (s / t).Nonempty :=
  Nonempty.image₂

@[to_additive]
/-
**Finset.Nonempty.of_div_left** 是 Mathlib 中的一个定理，位于命名空间 `Finset.Nonempty`。
形式化陈述：∀ {α : Type u_2} [inst : DecidableEq α] [inst_1 : Div α] {s t : Finset α},
 (s / t).Nonempty → s.Nonempty
参数：s / t。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.Nonempty.of_image₂_left`：∀ {α : Type u_1} {β : Type u_3} {γ : Typ
e u_5} [inst : DecidableEq γ] {f : α → β → γ} {s : Finset α} {t : Finset β},   (
Finset.image₂ f s t)…
-/
theorem Nonempty.of_div_left : (s / t).Nonempty → s.Nonempty :=
  Nonempty.of_image₂_left

@[to_additive]
/-
**Finset.Nonempty.of_div_right** 是 Mathlib 中的一个定理，位于命名空间 `Finset.Nonempty`。
形式化陈述：∀ {α : Type u_2} [inst : DecidableEq α] [inst_1 : Div α] {s t : Finset α},
 (s / t).Nonempty → t.Nonempty
参数：s / t。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.Nonempty.of_image₂_right`：∀ {α : Type u_1} {β : Type u_3} {γ : Ty
pe u_5} [inst : DecidableEq γ] {f : α → β → γ} {s : Finset α} {t : Finset β},   
(Finset.image₂ f s t)…
-/
theorem Nonempty.of_div_right : (s / t).Nonempty → t.Nonempty :=
  Nonempty.of_image₂_right

@[to_additive (attr := simp)]
/-
**Finset.div_singleton** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：div_singleton (a : α) : s / {a} = s.image (· / a)
参数：a : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.image₂_singleton_right`：image₂_singleton_right : image₂ f s {b} =
 s.image fun a => f a b
-/
theorem div_singleton (a : α) : s / {a} = s.image (· / a) :=
  image₂_singleton_right

@[to_additive (attr := simp)]
/-
**Finset.singleton_div** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：singleton_div (a : α) : {a} / s = s.image (a / ·)
参数：a : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.image₂_singleton_left`：image₂_singleton_left : image₂ f {a} t = t
.image fun b => f a b
-/
theorem singleton_div (a : α) : {a} / s = s.image (a / ·) :=
  image₂_singleton_left

@[to_additive]
/-
**Finset.singleton_div_singleton** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：singleton_div_singleton (a b : α) : ({a} : Finset α) / {b} = {a / b}
参数：a b : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.image₂_singleton`：image₂_singleton : image₂ f {a} {b} = {f a b}
-/
theorem singleton_div_singleton (a b : α) : ({a} : Finset α) / {b} = {a / b} :=
  image₂_singleton

@[to_additive (attr := mono, gcongr)]
/-
**Finset.div_subset_div** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：div_subset_div : s₁ subseteq s₂ -> t₁ subseteq t₂ -> s₁ / t₁ subseteq s₂ /
 t₂
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.image₂_subset`：image₂_subset (hs : s subseteq s') (ht : t subsete
q t') : image₂ f s t subseteq image₂ f s' t'
-/
theorem div_subset_div : s₁ ⊆ s₂ → t₁ ⊆ t₂ → s₁ / t₁ ⊆ s₂ / t₂ :=
  image₂_subset

@[to_additive]
/-
**Finset.div_subset_div_left** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：div_subset_div_left : t₁ subseteq t₂ -> s / t₁ subseteq s / t₂
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.image₂_subset_left`：image₂_subset_left (ht : t subseteq t') : ima
ge₂ f s t subseteq image₂ f s t'
-/
theorem div_subset_div_left : t₁ ⊆ t₂ → s / t₁ ⊆ s / t₂ :=
  image₂_subset_left

@[to_additive]
/-
**Finset.div_subset_div_right** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：div_subset_div_right : s₁ subseteq s₂ -> s₁ / t subseteq s₂ / t
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.image₂_subset_right`：image₂_subset_right (hs : s subseteq s') : i
mage₂ f s t subseteq image₂ f s' t
-/
theorem div_subset_div_right : s₁ ⊆ s₂ → s₁ / t ⊆ s₂ / t :=
  image₂_subset_right

@[to_additive]
/-
**Finset.div_subset_iff** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：div_subset_iff : s / t subseteq u ↔ forall x in s, forall y in t, x / y in
 u
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.image₂_subset_iff`：image₂_subset_iff : image₂ f s t subseteq u ↔ 
forall x in s, forall y in t, f x y in u
-/
theorem div_subset_iff : s / t ⊆ u ↔ ∀ x ∈ s, ∀ y ∈ t, x / y ∈ u :=
  image₂_subset_iff

@[to_additive]
/-
**Finset.union_div** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：union_div : (s₁ union s₂) / t = s₁ / t union s₂ / t
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.image₂_union_left`：image₂_union_left [DecidableEq α] : image₂ f (
s union s') t = image₂ f s t union image₂ f s' t
-/
theorem union_div : (s₁ ∪ s₂) / t = s₁ / t ∪ s₂ / t :=
  image₂_union_left

@[to_additive]
/-
**Finset.div_union** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：div_union : s / (t₁ union t₂) = s / t₁ union s / t₂
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.image₂_union_right`：image₂_union_right [DecidableEq β] : image₂ f
 s (t union t') = image₂ f s t union image₂ f s t'
-/
theorem div_union : s / (t₁ ∪ t₂) = s / t₁ ∪ s / t₂ :=
  image₂_union_right

@[to_additive]
/-
**Finset.inter_div_subset** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：inter_div_subset : s₁ inter s₂ / t subseteq s₁ / t inter (s₂ / t)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.image₂_inter_subset_left`：image₂_inter_subset_left [DecidableEq α
] : image₂ f (s inter s') t subseteq image₂ f s t inter image₂ f s' t
-/
theorem inter_div_subset : s₁ ∩ s₂ / t ⊆ s₁ / t ∩ (s₂ / t) :=
  image₂_inter_subset_left

@[to_additive]
/-
**Finset.div_inter_subset** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：div_inter_subset : s / (t₁ inter t₂) subseteq s / t₁ inter (s / t₂)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.image₂_inter_subset_right`：image₂_inter_subset_right [DecidableEq
 β] : image₂ f s (t inter t') subseteq image₂ f s t inter image₂ f s t'
-/
theorem div_inter_subset : s / (t₁ ∩ t₂) ⊆ s / t₁ ∩ (s / t₂) :=
  image₂_inter_subset_right

@[to_additive]
/-
**Finset.inter_div_union_subset_union** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：inter_div_union_subset_union : s₁ inter s₂ / (t₁ union t₂) subseteq s₁ / t
₁ union s₂ / t₂
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.image₂_inter_union_subset_union`：image₂_inter_union_subset_union 
: image₂ f (s inter s') (t union t') subseteq image₂ f s t union image₂ f s' t'
-/
theorem inter_div_union_subset_union : s₁ ∩ s₂ / (t₁ ∪ t₂) ⊆ s₁ / t₁ ∪ s₂ / t₂ :=
  image₂_inter_union_subset_union

@[to_additive]
/-
**Finset.union_div_inter_subset_union** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：union_div_inter_subset_union : (s₁ union s₂) / (t₁ inter t₂) subseteq s₁ /
 t₁ union s₂ / t₂
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.image₂_union_inter_subset_union`：image₂_union_inter_subset_union 
: image₂ f (s union s') (t inter t') subseteq image₂ f s t union image₂ f s' t'
-/
theorem union_div_inter_subset_union : (s₁ ∪ s₂) / (t₁ ∩ t₂) ⊆ s₁ / t₁ ∪ s₂ / t₂ :=
  image₂_union_inter_subset_union

/-- If a finset `u` is contained in the product of two sets `s / t`, we can find two finsets `s'`,
`t'` such that `s' ⊆ s`, `t' ⊆ t` and `u ⊆ s' / t'`. -/
@[to_additive
  /-- If a finset `u` is contained in the sum of two sets `s - t`, we can find two finsets
  `s'`, `t'` such that `s' ⊆ s`, `t' ⊆ t` and `u ⊆ s' - t'`. -/]
/-
**Finset.subset_div** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：subset_div {s t : Set α} : ↑u subseteq s / t -> exists s' t' : Finset α, ↑
s' subseteq s ∧ ↑t' subseteq t ∧ u subseteq s' / t'
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.subset_set_image₂`：subset_set_image₂ {s : Set α} {t : Set β} (hu 
: ↑u subseteq image2 f s t) : exists (s' : Finset α) (t' : Finset β), ↑s' subset
eq s ∧ ↑t' sub…
-/
theorem subset_div {s t : Set α} :
    ↑u ⊆ s / t → ∃ s' t' : Finset α, ↑s' ⊆ s ∧ ↑t' ⊆ t ∧ u ⊆ s' / t' :=
  subset_set_image₂

@[to_additive (attr := simp (default + 1))]
/-
**Finset.sup_div_le** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
形式化陈述：sup_div_le [SemilatticeSup β] [OrderBot β] {s t : Finset α} {f : α -> β} {
a : β} : sup (s / t) f <= a ↔ forall x in s, forall y in t, f (x / y) <= a
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Finset.sup_image₂_le`：sup_image₂_le {g : γ -> δ} {a : δ} : sup (image₂ f
 s t) g <= a ↔ forall x in s, forall y in t, g (f x y) <= a
-/
lemma sup_div_le [SemilatticeSup β] [OrderBot β] {s t : Finset α} {f : α → β} {a : β} :
    sup (s / t) f ≤ a ↔ ∀ x ∈ s, ∀ y ∈ t, f (x / y) ≤ a :=
  sup_image₂_le

@[to_additive]
/-
**Finset.sup_div_left** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
形式化陈述：sup_div_left [SemilatticeSup β] [OrderBot β] (s t : Finset α) (f : α -> β)
 : sup (s / t) f = sup s fun x => sup t (f <| x / ·)
参数：s t : Finset α；f : α -> β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Finset.sup_image₂_left`：sup_image₂_left (g : γ -> δ) : sup (image₂ f s t
) g = sup s fun x => sup t (g <| f x ·)
-/
lemma sup_div_left [SemilatticeSup β] [OrderBot β] (s t : Finset α) (f : α → β) :
    sup (s / t) f = sup s fun x ↦ sup t (f <| x / ·) :=
  sup_image₂_left ..

@[to_additive]
/-
**Finset.sup_div_right** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
形式化陈述：sup_div_right [SemilatticeSup β] [OrderBot β] (s t : Finset α) (f : α -> β
) : sup (s / t) f = sup t fun y => sup s (f <| · / y)
参数：s t : Finset α；f : α -> β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Finset.sup_image₂_right`：sup_image₂_right (g : γ -> δ) : sup (image₂ f s
 t) g = sup t fun y => sup s (g <| f · y)
-/
lemma sup_div_right [SemilatticeSup β] [OrderBot β] (s t : Finset α) (f : α → β) :
    sup (s / t) f = sup t fun y ↦ sup s (f <| · / y) :=
  sup_image₂_right ..

@[to_additive (attr := simp (default + 1))]
/-
**Finset.le_inf_div** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
形式化陈述：le_inf_div [SemilatticeInf β] [OrderTop β] {s t : Finset α} {f : α -> β} {
a : β} : a <= inf (s / t) f ↔ forall x in s, forall y in t, a <= f (x / y)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Finset.le_inf_image₂`：le_inf_image₂ {g : γ -> δ} {a : δ} : a <= inf (ima
ge₂ f s t) g ↔ forall x in s, forall y in t, a <= g (f x y)
-/
lemma le_inf_div [SemilatticeInf β] [OrderTop β] {s t : Finset α} {f : α → β} {a : β} :
    a ≤ inf (s / t) f ↔ ∀ x ∈ s, ∀ y ∈ t, a ≤ f (x / y) :=
  le_inf_image₂

@[to_additive]
/-
**Finset.inf_div_left** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
形式化陈述：inf_div_left [SemilatticeInf β] [OrderTop β] (s t : Finset α) (f : α -> β)
 : inf (s / t) f = inf s fun x => inf t (f <| x / ·)
参数：s t : Finset α；f : α -> β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Finset.inf_image₂_left`：inf_image₂_left (g : γ -> δ) : inf (image₂ f s t
) g = inf s fun x => inf t (g ∘ f x)
-/
lemma inf_div_left [SemilatticeInf β] [OrderTop β] (s t : Finset α) (f : α → β) :
    inf (s / t) f = inf s fun x ↦ inf t (f <| x / ·) :=
  inf_image₂_left ..

@[to_additive]
/-
**Finset.inf_div_right** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
形式化陈述：inf_div_right [SemilatticeInf β] [OrderTop β] (s t : Finset α) (f : α -> β
) : inf (s / t) f = inf t fun y => inf s (f <| · / y)
参数：s t : Finset α；f : α -> β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Finset.inf_image₂_right`：inf_image₂_right (g : γ -> δ) : inf (image₂ f s
 t) g = inf t fun y => inf s (g <| f · y)
-/
lemma inf_div_right [SemilatticeInf β] [OrderTop β] (s t : Finset α) (f : α → β) :
    inf (s / t) f = inf t fun y ↦ inf s (f <| · / y) :=
  inf_image₂_right ..

end Div

/-! ### Instances -/

section Instances

variable [DecidableEq α] [DecidableEq β]

/-- Repeated pointwise multiplication (not the same as pointwise repeated multiplication!) of a
`Finset`. See note [pointwise nat action]. -/
@[to_additive (attr := instance_reducible)
/-- Repeated pointwise addition (not the same as pointwise repeated addition!) of a `Finset`. See
note [pointwise nat action]. -/]
/-
**Finset.npow** 是 Mathlib 中的一个定义，位于命名空间 `Finset`。
形式化陈述：{α : Type u_2} → [DecidableEq α] → [One α] → [Mul α] → Pow (Finset α) ℕ
参数：Finset α。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
protected def npow [One α] [Mul α] : Pow (Finset α) ℕ :=
  ⟨fun s n => npowRec n s⟩

/-- Repeated pointwise multiplication/division (not the same as pointwise repeated
multiplication/division!) of a `Finset`. See note [pointwise nat action]. -/
@[to_additive (attr := instance_reducible)
/-- Repeated pointwise addition/subtraction (not the same as pointwise repeated
addition/subtraction!) of a `Finset`. See note [pointwise nat action]. -/]
/-
**Finset.zpow** 是 Mathlib 中的一个定义，位于命名空间 `Finset`。
形式化陈述：{α : Type u_2} → [DecidableEq α] → [One α] → [Mul α] → [Inv α] → Pow (Fins
et α) ℤ
参数：Finset α。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
protected def zpow [One α] [Mul α] [Inv α] : Pow (Finset α) ℤ :=
  ⟨fun s n => zpowRec npowRec n s⟩

scoped[Pointwise] attribute [instance] Finset.nsmul Finset.npow Finset.zsmul Finset.zpow

/-- `Finset α` is a `Semigroup` under pointwise operations if `α` is. -/
@[to_additive (attr := instance_reducible)
  /-- `Finset α` is an `AddSemigroup` under pointwise operations if `α` is. -/]
/-
**Finset.semigroup** 是 Mathlib 中的一个定义，位于命名空间 `Finset`。
形式化陈述：{α : Type u_2} → [DecidableEq α] → [Semigroup α] → Semigroup (Finset α)
参数：Finset α。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.coe_injective`：coe_injective {α} : Injective ((↑) : Finset α -> S
et α)
-/
protected def semigroup [Semigroup α] : Semigroup (Finset α) :=
  coe_injective.semigroup _ coe_mul

section CommSemigroup

variable [CommSemigroup α] {s t : Finset α}

/-- `Finset α` is a `CommSemigroup` under pointwise operations if `α` is. -/
@[to_additive (attr := instance_reducible)
  /-- `Finset α` is an `AddCommSemigroup` under pointwise operations if `α` is. -/]
/-
**Finset.commSemigroup** 是 Mathlib 中的一个定义，位于命名空间 `Finset`。
形式化陈述：{α : Type u_2} → [DecidableEq α] → [CommSemigroup α] → CommSemigroup (Fins
et α)
参数：Finset α。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.coe_injective`：coe_injective {α} : Injective ((↑) : Finset α -> S
et α)
-/
protected def commSemigroup : CommSemigroup (Finset α) :=
  coe_injective.commSemigroup _ coe_mul

@[to_additive]
/-
**Finset.inter_mul_union_subset** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：inter_mul_union_subset : s inter t * (s union t) subseteq s * t
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.image₂_inter_union_subset`：image₂_inter_union_subset {f : α -> α 
-> β} {s t : Finset α} (hf : forall a b, f a b = f b a) : image₂ f (s inter t) (
s union t) subseteq im…
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
-/
theorem inter_mul_union_subset : s ∩ t * (s ∪ t) ⊆ s * t :=
  image₂_inter_union_subset mul_comm

@[to_additive]
/-
**Finset.union_mul_inter_subset** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：union_mul_inter_subset : (s union t) * (s inter t) subseteq s * t
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.image₂_union_inter_subset`：image₂_union_inter_subset {f : α -> α 
-> β} {s t : Finset α} (hf : forall a b, f a b = f b a) : image₂ f (s union t) (
s inter t) subseteq im…
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
-/
theorem union_mul_inter_subset : (s ∪ t) * (s ∩ t) ⊆ s * t :=
  image₂_union_inter_subset mul_comm

end CommSemigroup

section MulOneClass

variable [MulOneClass α]

/-- `Finset α` is a `MulOneClass` under pointwise operations if `α` is. -/
@[to_additive (attr := instance_reducible)
  /-- `Finset α` is an `AddZeroClass` under pointwise operations if `α` is. -/]
/-
**Finset.mulOneClass** 是 Mathlib 中的一个定义，位于命名空间 `Finset`。
形式化陈述：{α : Type u_2} → [DecidableEq α] → [MulOneClass α] → MulOneClass (Finset α
)
参数：Finset α。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.coe_injective`：coe_injective {α} : Injective ((↑) : Finset α -> S
et α)
-/
protected def mulOneClass : MulOneClass (Finset α) :=
  coe_injective.mulOneClass _ (coe_singleton 1) coe_mul

scoped[Pointwise] attribute [instance] Finset.semigroup Finset.addSemigroup Finset.commSemigroup
  Finset.addCommSemigroup Finset.mulOneClass Finset.addZeroClass

@[to_additive]
/-
**Finset.subset_mul_left** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：subset_mul_left (s : Finset α) {t : Finset α} (ht : (1 : α) in t) : s subs
eteq s * t
参数：s : Finset α；ht : (1 : α) in t。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Finset.mem_mul`：mem_mul {x : α} : x in s * t ↔ exists y in s, exists z i
n t, y * z = x
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
-/
theorem subset_mul_left (s : Finset α) {t : Finset α} (ht : (1 : α) ∈ t) : s ⊆ s * t := fun a ha =>
  mem_mul.2 ⟨a, ha, 1, ht, mul_one _⟩

@[to_additive]
/-
**Finset.subset_mul_right** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：subset_mul_right {s : Finset α} (t : Finset α) (hs : (1 : α) in s) : t sub
seteq s * t
参数：t : Finset α；hs : (1 : α) in s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Finset.mem_mul`：mem_mul {x : α} : x in s * t ↔ exists y in s, exists z i
n t, y * z = x
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
-/
theorem subset_mul_right {s : Finset α} (t : Finset α) (hs : (1 : α) ∈ s) : t ⊆ s * t := fun a ha =>
  mem_mul.2 ⟨1, hs, a, ha, one_mul _⟩

/-- The singleton operation as a `MonoidHom`. -/
@[to_additive /-- The singleton operation as an `AddMonoidHom`. -/]
/-
**Finset.singletonMonoidHom** 是 Mathlib 中的一个定义，位于命名空间 `Finset`。
形式化陈述：singletonMonoidHom : α ->* Finset α
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The singleton operation as a `MonoidHom`.
-/
def singletonMonoidHom : α →* Finset α :=
  { singletonMulHom, singletonOneHom with }

@[to_additive (attr := simp)]
/-
**Finset.coe_singletonMonoidHom** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：coe_singletonMonoidHom : (singletonMonoidHom : α -> Finset α) = singleton
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_singletonMonoidHom : (singletonMonoidHom : α → Finset α) = singleton :=
  rfl

@[to_additive (attr := simp)]
/-
**Finset.singletonMonoidHom_apply** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：singletonMonoidHom_apply (a : α) : singletonMonoidHom a = {a}
参数：a : α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem singletonMonoidHom_apply (a : α) : singletonMonoidHom a = {a} :=
  rfl

/-- The coercion from `Finset` to `Set` as a `MonoidHom`. -/
@[to_additive /-- The coercion from `Finset` to `set` as an `AddMonoidHom`. -/]
/-
**Finset.coeMonoidHom** 是 Mathlib 中的一个定义，位于命名空间 `Finset`。
形式化陈述：coeMonoidHom : Finset α ->* Set α where toFun
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The coercion from `Finset` to `Set` as a `MonoidHom`.
-/
def coeMonoidHom : Finset α →* Set α where
  toFun := (↑)
  map_one' := coe_one
  map_mul' := coe_mul

@[to_additive (attr := simp)]
/-
**Finset.coe_coeMonoidHom** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：coe_coeMonoidHom : (coeMonoidHom : Finset α -> Set α) = (↑)
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_coeMonoidHom : (coeMonoidHom : Finset α → Set α) = (↑) :=
  rfl

@[to_additive (attr := simp)]
/-
**Finset.coeMonoidHom_apply** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：coeMonoidHom_apply (s : Finset α) : coeMonoidHom s = s
参数：s : Finset α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coeMonoidHom_apply (s : Finset α) : coeMonoidHom s = s :=
  rfl

/-- Lift a `MonoidHom` to `Finset` via `image`. -/
@[to_additive (attr := simps) /-- Lift an `add_monoid_hom` to `Finset` via `image` -/]
/-
**Finset.imageMonoidHom** 是 Mathlib 中的一个定义，位于命名空间 `Finset`。
形式化陈述：imageMonoidHom [MulOneClass β] [FunLike F α β] [MonoidHomClass F α β] (f :
 F) : Finset α ->* Finset β
参数：f : F。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Lift a `MonoidHom` to `Finset` via `image`.
-/
def imageMonoidHom [MulOneClass β] [FunLike F α β] [MonoidHomClass F α β] (f : F) :
    Finset α →* Finset β :=
  { imageMulHom f, imageOneHom f with }

end MulOneClass

section Monoid

variable [Monoid α] {s t : Finset α} {a : α} {m n : ℕ}

@[to_additive (attr := simp, norm_cast)]
/-
**Finset.coe_pow** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：coe_pow (s : Finset α) (n : Nat) : ↑(s ^ n) = (s : Set α) ^ n
参数：s : Finset α；n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `npowRec.eq_1`：∀ {M : Type u_1} [inst : One M] [inst_1 : Mul M] (x : M), 
npowRec 0 x = 1
· 使用定理 `pow_zero`：pow_zero (a : M) : a ^ 0 = 1
· 使用定理 `Finset.coe_one`：coe_one : ↑(1 : Finset α) = (1 : Set α)
· 使用定理 `npowRec.eq_2`：∀ {M : Type u_1} [inst : One M] [inst_1 : Mul M] (x : M) (
n : ℕ), npowRec n.succ x = npowRec n x * x
· 使用定理 `pow_succ`：pow_succ (a : M) (n : Nat) : a ^ (n + 1) = a ^ n * a
· 使用定理 `Finset.coe_mul`：coe_mul (s t : Finset α) : (↑(s * t) : Set α) = ↑s * ↑t
-/
theorem coe_pow (s : Finset α) (n : ℕ) : ↑(s ^ n) = (s : Set α) ^ n := by
  change ↑(npowRec n s) = (s : Set α) ^ n
  induction n with
  | zero => rw [npowRec, pow_zero, coe_one]
  | succ n ih => rw [npowRec, pow_succ, coe_mul, ih]

/-- `Finset α` is a `Monoid` under pointwise operations if `α` is. -/
@[to_additive (attr := instance_reducible)
  /-- `Finset α` is an `AddMonoid` under pointwise operations if `α` is. -/]
/-
**Finset.monoid** 是 Mathlib 中的一个定义，位于命名空间 `Finset`。
形式化陈述：{α : Type u_2} → [DecidableEq α] → [Monoid α] → Monoid (Finset α)
参数：Finset α。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.coe_injective`：coe_injective {α} : Injective ((↑) : Finset α -> S
et α)
· 使用定理 `Finset.coe_pow`：coe_pow (s : Finset α) (n : Nat) : ↑(s ^ n) = (s : Set α
) ^ n
-/
protected def monoid : Monoid (Finset α) :=
  coe_injective.monoid _ coe_one coe_mul coe_pow

scoped[Pointwise] attribute [instance] Finset.monoid Finset.addMonoid

-- `Finset.pow_left_monotone` doesn't exist since it would syntactically be a special case of
-- `pow_left_mono`

@[to_additive]
/-
**Finset.pow_right_monotone** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：∀ {α : Type u_2} [inst : DecidableEq α] [inst_1 : Monoid α] {s : Finset α}
, 1 ∈ s → Monotone fun x => s ^ x
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `pow_right_monotone`：pow_right_monotone (ha : 1 <= a) : Monotone fun n : 
Nat => a ^ n
· 使用定理 `Finset.instMulLeftMono`：∀ {α : Type u_2} [inst : DecidableEq α] [inst_1 
: Mul α], MulLeftMono (Finset α)
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Finset.one_subset`：one_subset : (1 : Finset α) subseteq s ↔ (1 : α) in s
-/
protected lemma pow_right_monotone (hs : 1 ∈ s) : Monotone (s ^ ·) :=
  pow_right_monotone <| one_subset.2 hs

@[to_additive]
/-
**Finset.pow_subset_pow_left** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
形式化陈述：pow_subset_pow_left (hst : s subseteq t) : s ^ n subseteq t ^ n
参数：hst : s subseteq t。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `pow_left_mono`：pow_left_mono (n : Nat) : Monotone fun a : M => a ^ n
· 使用定理 `Finset.instMulLeftMono`：∀ {α : Type u_2} [inst : DecidableEq α] [inst_1 
: Mul α], MulLeftMono (Finset α)
· 使用定理 `Finset.instMulRightMono`：∀ {α : Type u_2} [inst : DecidableEq α] [inst_1
 : Mul α], MulRightMono (Finset α)
-/
lemma pow_subset_pow_left (hst : s ⊆ t) : s ^ n ⊆ t ^ n := pow_left_mono n hst

@[to_additive]
/-
**Finset.pow_subset_pow_right** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
形式化陈述：pow_subset_pow_right (hs : 1 in s) (hmn : m <= n) : s ^ m subseteq s ^ n
参数：hs : 1 in s；hmn : m <= n。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.pow_right_monotone`：∀ {α : Type u_2} [inst : DecidableEq α] [inst
_1 : Monoid α] {s : Finset α}, 1 ∈ s → Monotone fun x => s ^ x
-/
lemma pow_subset_pow_right (hs : 1 ∈ s) (hmn : m ≤ n) : s ^ m ⊆ s ^ n :=
  Finset.pow_right_monotone hs hmn

@[to_additive (attr := gcongr)]
/-
**Finset.pow_subset_pow** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
形式化陈述：pow_subset_pow (hst : s subseteq t) (ht : 1 in t) (hmn : m <= n) : s ^ m s
ubseteq t ^ n
参数：hst : s subseteq t；ht : 1 in t；hmn : m <= n。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用引理 `Finset.pow_subset_pow_left`：pow_subset_pow_left (hst : s subseteq t) : s
 ^ n subseteq t ^ n
· 使用引理 `Finset.pow_subset_pow_right`：pow_subset_pow_right (hs : 1 in s) (hmn : m
 <= n) : s ^ m subseteq s ^ n
-/
lemma pow_subset_pow (hst : s ⊆ t) (ht : 1 ∈ t) (hmn : m ≤ n) : s ^ m ⊆ t ^ n :=
  (pow_subset_pow_left hst).trans (pow_subset_pow_right ht hmn)

@[to_additive]
/-
**Finset.subset_pow** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
形式化陈述：subset_pow (hs : 1 in s) (hn : n != 0) : s subseteq s ^ n
参数：hs : 1 in s；hn : n != 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `pow_one`：pow_one (a : M) : a ^ 1 = a
· 使用引理 `Finset.pow_subset_pow_right`：pow_subset_pow_right (hs : 1 in s) (hmn : m
 <= n) : s ^ m subseteq s ^ n
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Nat.one_le_iff_ne_zero`：∀ {n : ℕ}, 1 ≤ n ↔ n ≠ 0
-/
lemma subset_pow (hs : 1 ∈ s) (hn : n ≠ 0) : s ⊆ s ^ n := by
  simpa using pow_subset_pow_right hs <| Nat.one_le_iff_ne_zero.2 hn

@[to_additive]
/-
**Finset.pow_subset_pow_mul_of_sq_subset_mul** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
形式化陈述：pow_subset_pow_mul_of_sq_subset_mul (hst : s ^ 2 subseteq t * s) (hn : n !
= 0) : s ^ n subseteq t ^ (n - 1) * s
参数：hst : s ^ 2 subseteq t * s；hn : n != 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `pow_le_pow_mul_of_sq_le_mul`：pow_le_pow_mul_of_sq_le_mul [MulLeftMono M]
 {a b : M} (hab : a ^ 2 <= b * a) : forall {n}, n != 0 -> a ^ n <= b ^ (n - 1) *
 a | 1, _ => by s…
· 使用定理 `Finset.instMulRightMono`：∀ {α : Type u_2} [inst : DecidableEq α] [inst_1
 : Mul α], MulRightMono (Finset α)
· 使用定理 `Finset.instMulLeftMono`：∀ {α : Type u_2} [inst : DecidableEq α] [inst_1 
: Mul α], MulLeftMono (Finset α)
-/
lemma pow_subset_pow_mul_of_sq_subset_mul (hst : s ^ 2 ⊆ t * s) (hn : n ≠ 0) :
    s ^ n ⊆ t ^ (n - 1) * s := pow_le_pow_mul_of_sq_le_mul hst hn

@[to_additive (attr := simp) nsmul_empty]
/-
**Finset.empty_pow** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
形式化陈述：empty_pow (hn : n != 0) : (∅ : Finset α) ^ n = ∅
参数：hn : n != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `pow_succ`：pow_succ (a : M) (n : Nat) : a ^ (n + 1) = a ^ n * a
· 使用定理 `Finset.mul_empty`：mul_empty (s : Finset α) : s * ∅ = ∅
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma empty_pow (hn : n ≠ 0) : (∅ : Finset α) ^ n = ∅ := match n with | n + 1 => by simp [pow_succ]

@[to_additive]
/-
**Finset.Nonempty.pow** 是 Mathlib 中的一个定理，位于命名空间 `Finset.Nonempty`。
形式化陈述：∀ {α : Type u_2} [inst : DecidableEq α] [inst_1 : Monoid α] {s : Finset α}
, s.Nonempty → ∀ {n : ℕ}, (s ^ n).Nonempty
参数：s ^ n。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma Nonempty.pow (hs : s.Nonempty) : ∀ {n}, (s ^ n).Nonempty
  | 0 => by simp
  | n + 1 => by rw [pow_succ]; exact hs.pow.mul hs
/-
**Finset.pow_eq_empty** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：∀ {α : Type u_2} [inst : DecidableEq α] [inst_1 : Monoid α] {s : Finset α}
 {n : ℕ}, s ^ n = ∅ ↔ s = ∅ ∧ n ≠ 0
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose₁`：contrapose₁ {p q : Prop} : (¬ q -
> ¬ p) -> (p -> q)
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Mathlib.Tactic.Push.not_and_or_eq`：not_and_or_eq : (¬ (p ∧ q)) = (¬ p ∨ 
¬ q)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.Nonempty.pow`：∀ {α : Type u_2} [inst : DecidableEq α] [inst_1 : M
onoid α] {s : Finset α}, s.Nonempty → ∀ {n : ℕ}, (s ^ n).Nonempty
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `pow_zero`：pow_zero (a : M) : a ^ 0 = 1
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `Finset.empty_pow`：empty_pow (hn : n != 0) : (∅ : Finset α) ^ n = ∅
-/
@[to_additive (attr := simp)] lemma pow_eq_empty : s ^ n = ∅ ↔ s = ∅ ∧ n ≠ 0 := by
  constructor
  · contrapose! +distrib
    rintro (hs | rfl)
    · exact hs.pow
    · simp
  · rintro ⟨rfl, hn⟩
    exact empty_pow hn

@[to_additive (attr := simp) nsmul_singleton]
/-
**Finset.singleton_pow** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：∀ {α : Type u_2} [inst : DecidableEq α] [inst_1 : Monoid α] (a : α) (n : ℕ
), {a} ^ n = {a ^ n}
参数：a : α；n : ℕ。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma singleton_pow (a : α) : ∀ n, ({a} : Finset α) ^ n = {a ^ n}
  | 0 => by simp [singleton_one]
  | n + 1 => by simp [pow_succ, singleton_pow _ n]
/-
**Finset.pow_mem_pow** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：∀ {α : Type u_2} [inst : DecidableEq α] [inst_1 : Monoid α] {s : Finset α}
 {a : α} {n : ℕ}, a ∈ s → a ^ n ∈ s ^ n
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.singleton_pow`：∀ {α : Type u_2} [inst : DecidableEq α] [inst_1 : 
Monoid α] (a : α) (n : ℕ), {a} ^ n = {a ^ n}
· 使用引理 `Finset.pow_subset_pow_left`：pow_subset_pow_left (hst : s subseteq t) : s
 ^ n subseteq t ^ n
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Finset.singleton_subset_iff`：singleton_subset_iff {s : Finset α} {a : α}
 : {a} subseteq s ↔ a in s
-/
@[to_additive] lemma pow_mem_pow (ha : a ∈ s) : a ^ n ∈ s ^ n := by
  simpa using pow_subset_pow_left (singleton_subset_iff.2 ha)
/-
**Finset.one_mem_pow** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：∀ {α : Type u_2} [inst : DecidableEq α] [inst_1 : Monoid α] {s : Finset α}
 {n : ℕ}, 1 ∈ s → 1 ∈ s ^ n
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `one_pow`：one_pow {a : R} (b : Nat) (ha : IsNat a 1) : a ^ b = a
· 使用定理 `Finset.pow_mem_pow`：∀ {α : Type u_2} [inst : DecidableEq α] [inst_1 : Mo
noid α] {s : Finset α} {a : α} {n : ℕ}, a ∈ s → a ^ n ∈ s ^ n
-/
@[to_additive] lemma one_mem_pow (hs : 1 ∈ s) : 1 ∈ s ^ n := by simpa using pow_mem_pow hs

@[to_additive]
/-
**Finset.inter_pow_subset** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
形式化陈述：inter_pow_subset : (s inter t) ^ n subseteq s ^ n inter t ^ n
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.subset_inter`：subset_inter {s₁ s₂ u : Finset α} : s₁ subseteq s₂ 
-> s₁ subseteq u -> s₁ subseteq s₂ inter u
· 使用定理 `pow_le_pow_left'`：∀ {M : Type u_3} [inst : Monoid M] [inst_1 : Preorder 
M] [MulLeftMono M] [MulRightMono M] {a b : M},   a ≤ b → ∀ (i : ℕ), a ^ i ≤ b ^ 
i
· 使用定理 `Finset.instMulLeftMono`：∀ {α : Type u_2} [inst : DecidableEq α] [inst_1 
: Mul α], MulLeftMono (Finset α)
· 使用定理 `Finset.instMulRightMono`：∀ {α : Type u_2} [inst : DecidableEq α] [inst_1
 : Mul α], MulRightMono (Finset α)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
-/
lemma inter_pow_subset : (s ∩ t) ^ n ⊆ s ^ n ∩ t ^ n := by apply subset_inter <;> gcongr <;> simp

@[to_additive (attr := simp, norm_cast)]
/-
**Finset.coe_list_prod** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：coe_list_prod (s : List (Finset α)) : (↑s.prod : Set α) = (s.map (↑)).prod
参数：s : List (Finset α)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `map_list_prod`：map_list_prod {F : Type*} [FunLike F M N] [MonoidHomClass
 F M N] (f : F) (l : List M) : f l.prod = (l.map f).prod
-/
theorem coe_list_prod (s : List (Finset α)) : (↑s.prod : Set α) = (s.map (↑)).prod :=
  map_list_prod (coeMonoidHom : Finset α →* Set α) _

@[to_additive]
/-
**Finset.mem_prod_list_ofFn** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：mem_prod_list_ofFn {a : α} {s : Fin n -> Finset α} : a in (List.ofFn s).pr
od ↔ exists f : forall i : Fin n, s i, (List.ofFn fun i => (f i : α)).prod = a
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.mem_coe`：mem_coe {a : α} {s : Finset α} : a in (s : Set α) ↔ a in
 (s : Finset α)
· 使用定理 `Finset.coe_list_prod`：coe_list_prod (s : List (Finset α)) : (↑s.prod : S
et α) = (s.map (↑)).prod
· 使用定理 `List.map_ofFn`：∀ {n : ℕ} {α : Type u_1} {β : Type u_2} {f : Fin n → α} {
g : α → β}, List.map g (List.ofFn f) = List.ofFn (g ∘ f)
· 使用定理 `Set.mem_prod_list_ofFn`：mem_prod_list_ofFn {a : α} {s : Fin n -> Set α} 
: a in (List.ofFn s).prod ↔ exists f : forall i : Fin n, s i, (List.ofFn fun i =
> (f i : α))…
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem mem_prod_list_ofFn {a : α} {s : Fin n → Finset α} :
    a ∈ (List.ofFn s).prod ↔ ∃ f : ∀ i : Fin n, s i, (List.ofFn fun i => (f i : α)).prod = a := by
  rw [← mem_coe, coe_list_prod, List.map_ofFn, Set.mem_prod_list_ofFn]
  rfl

@[to_additive]
/-
**Finset.mem_pow** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：mem_pow {a : α} {n : Nat} : a in s ^ n ↔ exists f : Fin n -> s, (List.ofFn
 fun i => ↑(f i)).prod = a
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.mem_coe`：mem_coe {a : α} {s : Finset α} : a in (s : Set α) ↔ a in
 (s : Finset α)
· 使用定理 `Finset.coe_pow`：coe_pow (s : Finset α) (n : Nat) : ↑(s ^ n) = (s : Set α
) ^ n
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem mem_pow {a : α} {n : ℕ} :
    a ∈ s ^ n ↔ ∃ f : Fin n → s, (List.ofFn fun i => ↑(f i)).prod = a := by
  simp [← mem_coe (s := s ^ n), coe_pow, Set.mem_pow]

@[to_additive]
/-
**Finset.card_pow_le** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：∀ {α : Type u_2} [inst : DecidableEq α] [inst_1 : Monoid α] {s : Finset α}
 {n : ℕ}, (s ^ n).card ≤ s.card ^ n
参数：s ^ n。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma card_pow_le : ∀ {n}, #(s ^ n) ≤ #s ^ n
  | 0 => by simp
  | n + 1 => by rw [pow_succ, pow_succ]; refine card_mul_le.trans (by gcongr; exact card_pow_le)

@[to_additive]
/-
**Finset.mul_univ_of_one_mem** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：mul_univ_of_one_mem [Fintype α] (hs : (1 : α) in s) : s * univ = univ
参数：hs : (1 : α) in s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Finset.eq_univ_iff_forall`：eq_univ_iff_forall : s = univ ↔ forall x, x i
n s
· 使用定理 `Finset.mem_mul`：mem_mul {x : α} : x in s * t ↔ exists y in s, exists z i
n t, y * z = x
· 使用定理 `Finset.mem_univ`：mem_univ (x : α) : x in (univ : Finset α)
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
-/
theorem mul_univ_of_one_mem [Fintype α] (hs : (1 : α) ∈ s) : s * univ = univ :=
  eq_univ_iff_forall.2 fun _ => mem_mul.2 ⟨_, hs, _, mem_univ _, one_mul _⟩

@[to_additive]
/-
**Finset.univ_mul_of_one_mem** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：univ_mul_of_one_mem [Fintype α] (ht : (1 : α) in t) : univ * t = univ
参数：ht : (1 : α) in t。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Finset.eq_univ_iff_forall`：eq_univ_iff_forall : s = univ ↔ forall x, x i
n s
· 使用定理 `Finset.mem_mul`：mem_mul {x : α} : x in s * t ↔ exists y in s, exists z i
n t, y * z = x
· 使用定理 `Finset.mem_univ`：mem_univ (x : α) : x in (univ : Finset α)
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
-/
theorem univ_mul_of_one_mem [Fintype α] (ht : (1 : α) ∈ t) : univ * t = univ :=
  eq_univ_iff_forall.2 fun _ => mem_mul.2 ⟨_, mem_univ _, _, ht, mul_one _⟩

@[to_additive (attr := simp)]
/-
**Finset.univ_mul_univ** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：univ_mul_univ [Fintype α] : (univ : Finset α) * univ = univ
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.mul_univ_of_one_mem`：mul_univ_of_one_mem [Fintype α] (hs : (1 : α
) in s) : s * univ = univ
· 使用定理 `Finset.mem_univ`：mem_univ (x : α) : x in (univ : Finset α)
-/
theorem univ_mul_univ [Fintype α] : (univ : Finset α) * univ = univ :=
  mul_univ_of_one_mem <| mem_univ _

@[to_additive (attr := simp) nsmul_univ]
/-
**Finset.univ_pow** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：univ_pow [Fintype α] (hn : n != 0) : (univ : Finset α) ^ n = univ
参数：hn : n != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.coe_injective`：coe_injective {α} : Injective ((↑) : Finset α -> S
et α)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.coe_pow`：coe_pow (s : Finset α) (n : Nat) : ↑(s ^ n) = (s : Set α
) ^ n
· 使用定理 `Finset.coe_univ`：coe_univ : ↑(univ : Finset α) = (Set.univ : Set α)
· 使用定理 `Set.univ_pow`：∀ {α : Type u_2} [inst : Monoid α] {n : ℕ}, n ≠ 0 → Set.un
iv ^ n = Set.univ
-/
theorem univ_pow [Fintype α] (hn : n ≠ 0) : (univ : Finset α) ^ n = univ :=
  coe_injective <| by rw [coe_pow, coe_univ, Set.univ_pow hn]

@[to_additive]
/-
**Finset._root_.IsUnit.finset** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
protected theorem _root_.IsUnit.finset : IsUnit a → IsUnit ({a} : Finset α) :=
  IsUnit.map (singletonMonoidHom : α →* Finset α)

@[to_additive]
/-
**Finset.image_op_pow** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：∀ {α : Type u_2} [inst : DecidableEq α] [inst_1 : Monoid α] (s : Finset α)
 (n : ℕ),   Finset.image MulOpposite.op (s ^ n) = Finset.image MulOpposite.op s 
^ n
参数：s : Finset α；n : ℕ；s ^ n。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma image_op_pow (s : Finset α) : ∀ n : ℕ, (s ^ n).image op = s.image op ^ n
  | 0 => by simp [singleton_one]
  | n + 1 => by rw [pow_succ, pow_succ', image_op_mul, image_op_pow]

@[to_additive]
/-
**Finset.map_op_pow** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：∀ {α : Type u_2} [inst : DecidableEq α] [inst_1 : Monoid α] (s : Finset α)
 (n : ℕ),   Finset.map MulOpposite.opEquiv.toEmbedding (s ^ n) = Finset.map MulO
pposite.opEquiv.toEmbedding s ^ n
参数：s : Finset α；n : ℕ；s ^ n。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma map_op_pow (s : Finset α) :
    ∀ n : ℕ, (s ^ n).map opEquiv.toEmbedding = s.map opEquiv.toEmbedding ^ n
  | 0 => by simp [singleton_one]
  | n + 1 => by rw [pow_succ, pow_succ', map_op_mul, map_op_pow]

@[to_additive]
/-
**Finset.product_pow** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：∀ {α : Type u_2} {β : Type u_3} [inst : DecidableEq α] [inst_1 : Decidable
Eq β] [inst_2 : Monoid α] [inst_3 : Monoid β]   (s : Finset α) (t : Finset β) (n
 : ℕ), s ×ˢ t ^ n = (s ^ n) ×ˢ (t ^ n)
参数：s : Finset α；t : Finset β；n : ℕ；s ^ n；t ^ n。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma product_pow [Monoid β] (s : Finset α) (t : Finset β) : ∀ n, (s ×ˢ t) ^ n = (s ^ n) ×ˢ (t ^ n)
  | 0 => by simp
  | n + 1 => by simp [pow_succ, product_pow _ _ n]

end Monoid

section CommMonoid

variable [CommMonoid α]

/-- `Finset α` is a `CommMonoid` under pointwise operations if `α` is. -/
@[to_additive (attr := instance_reducible)
  /-- `Finset α` is an `AddCommMonoid` under pointwise operations if `α` is. -/]
/-
**Finset.commMonoid** 是 Mathlib 中的一个定义，位于命名空间 `Finset`。
形式化陈述：{α : Type u_2} → [DecidableEq α] → [CommMonoid α] → CommMonoid (Finset α)
参数：Finset α。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.coe_injective`：coe_injective {α} : Injective ((↑) : Finset α -> S
et α)
-/
protected def commMonoid : CommMonoid (Finset α) :=
  coe_injective.commMonoid _ coe_one coe_mul coe_pow

scoped[Pointwise] attribute [instance] Finset.commMonoid Finset.addCommMonoid

end CommMonoid

section DivisionMonoid

variable [DivisionMonoid α] {s t : Finset α} {n : ℤ}

@[to_additive (attr := simp)]
/-
**Finset.coe_zpow** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：∀ {α : Type u_2} [inst : DecidableEq α] [inst_1 : DivisionMonoid α] (s : F
inset α) (n : ℤ), ↑(s ^ n) = ↑s ^ n
参数：s : Finset α；n : ℤ；s ^ n。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.coe_pow`：coe_pow (s : Finset α) (n : Nat) : ↑(s ^ n) = (s : Set α
) ^ n
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Finset.coe_inv`：coe_inv (s : Finset α) : ↑s⁻¹ = (s : Set α)⁻¹
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
-/
theorem coe_zpow (s : Finset α) : ∀ n : ℤ, ↑(s ^ n) = (s : Set α) ^ n
  | Int.ofNat _ => coe_pow _ _
  | Int.negSucc n => by
    refine (coe_inv _).trans ?_
    exact congr_arg Inv.inv (coe_pow _ _)

@[to_additive]
/-
**Finset.mul_eq_one_iff** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：∀ {α : Type u_2} [inst : DecidableEq α] [inst_1 : DivisionMonoid α] {s t :
 Finset α},   s * t = 1 ↔ ∃ a b, s = {a} ∧ t = {b} ∧ a * b = 1
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Finset.coe_mul`：coe_mul (s t : Finset α) : (↑(s * t) : Set α) = ↑s * ↑t
· 使用定理 `Finset.coe_one`：coe_one : ↑(1 : Finset α) = (1 : Set α)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Finset.coe_singleton`：coe_singleton (a : α) : (({a} : Finset α) : Set α)
 = {a}
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
protected theorem mul_eq_one_iff : s * t = 1 ↔ ∃ a b, s = {a} ∧ t = {b} ∧ a * b = 1 := by
  simp_rw [← coe_inj, coe_mul, coe_one, Set.mul_eq_one_iff, coe_singleton]

/-- `Finset α` is a division monoid under pointwise operations if `α` is. -/
@[to_additive (attr := instance_reducible)
  /-- `Finset α` is a subtraction monoid under pointwise operations if `α` is. -/]
/-
**Finset.divisionMonoid** 是 Mathlib 中的一个定义，位于命名空间 `Finset`。
形式化陈述：{α : Type u_2} → [DecidableEq α] → [DivisionMonoid α] → DivisionMonoid (Fi
nset α)
参数：Finset α。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.coe_injective`：coe_injective {α} : Injective ((↑) : Finset α -> S
et α)
· 使用定理 `Finset.coe_zpow`：∀ {α : Type u_2} [inst : DecidableEq α] [inst_1 : Divis
ionMonoid α] (s : Finset α) (n : ℤ), ↑(s ^ n) = ↑s ^ n
-/
protected def divisionMonoid : DivisionMonoid (Finset α) :=
  coe_injective.divisionMonoid _ coe_one coe_mul coe_inv coe_div coe_pow coe_zpow

scoped[Pointwise] attribute [instance] Finset.divisionMonoid Finset.subtractionMonoid

@[to_additive (attr := simp)]
/-
**Finset.isUnit_iff** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：isUnit_iff : IsUnit s ↔ exists a, s = {a} ∧ IsUnit a
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Finset.mul_eq_one_iff`：∀ {α : Type u_2} [inst : DecidableEq α] [inst_1 :
 DivisionMonoid α] {s t : Finset α},   s * t = 1 ↔ ∃ a b, s = {a} ∧ t = {b} ∧ a 
* b = 1
· 使用定理 `Units.mul_inv`：mul_inv : (a * ↑a⁻¹ : α) = 1
· 使用定理 `Finset.singleton_injective`：singleton_injective : Injective (singleton :
 α -> Finset α)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.singleton_mul_singleton`：singleton_mul_singleton (a b : α) : ({a}
 : Finset α) * {b} = {a * b}
· 使用定理 `Units.inv_mul`：inv_mul : (↑a⁻¹ * a : α) = 1
· 使用定理 `IsUnit.finset`：∀ {α : Type u_2} [inst : DecidableEq α] [inst_1 : Monoid 
α] {a : α}, IsUnit a → IsUnit {a}
-/
theorem isUnit_iff : IsUnit s ↔ ∃ a, s = {a} ∧ IsUnit a := by
  constructor
  · rintro ⟨u, rfl⟩
    obtain ⟨a, b, ha, hb, h⟩ := Finset.mul_eq_one_iff.1 u.mul_inv
    refine ⟨a, ha, ⟨a, b, h, singleton_injective ?_⟩, rfl⟩
    rw [← singleton_mul_singleton, ← ha, ← hb]
    exact u.inv_mul
  · rintro ⟨a, rfl, ha⟩
    exact ha.finset

@[to_additive (attr := simp)]
/-
**Finset.isUnit_coe** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：isUnit_coe : IsUnit (s : Set α) ↔ IsUnit s
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem isUnit_coe : IsUnit (s : Set α) ↔ IsUnit s := by
  simp_rw [isUnit_iff, Set.isUnit_iff, coe_eq_singleton]

@[to_additive (attr := simp)]
/-
**Finset.univ_div_univ** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
形式化陈述：univ_div_univ [Fintype α] : (univ / univ : Finset α) = univ
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `div_eq_mul_inv`：div_eq_mul_inv (a b : G) : a / b = a * b⁻¹
· 使用引理 `Finset.inv_univ`：inv_univ [Fintype α] : (univ : Finset α)⁻¹ = univ
· 使用定理 `Finset.univ_mul_univ`：univ_mul_univ [Fintype α] : (univ : Finset α) * un
iv = univ
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma univ_div_univ [Fintype α] : (univ / univ : Finset α) = univ := by simp [div_eq_mul_inv]
/-
**Finset.subset_div_left** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：∀ {α : Type u_2} [inst : DecidableEq α] [inst_1 : DivisionMonoid α] {s t :
 Finset α}, 1 ∈ t → s ⊆ s / t
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `div_eq_mul_inv`：div_eq_mul_inv (a b : G) : a / b = a * b⁻¹
· 使用定理 `Finset.subset_mul_left`：subset_mul_left (s : Finset α) {t : Finset α} (h
t : (1 : α) in t) : s subseteq s * t
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `inv_one`：inv_one : (1 : G)⁻¹ = 1
-/
@[to_additive] lemma subset_div_left (ht : 1 ∈ t) : s ⊆ s / t := by
  rw [div_eq_mul_inv]; exact subset_mul_left _ <| by simpa
/-
**Finset.inv_subset_div_right** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：∀ {α : Type u_2} [inst : DecidableEq α] [inst_1 : DivisionMonoid α] {s t :
 Finset α}, 1 ∈ s → t⁻¹ ⊆ s / t
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `div_eq_mul_inv`：div_eq_mul_inv (a b : G) : a / b = a * b⁻¹
· 使用定理 `Finset.subset_mul_right`：subset_mul_right {s : Finset α} (t : Finset α) 
(hs : (1 : α) in s) : t subseteq s * t
-/
@[to_additive] lemma inv_subset_div_right (hs : 1 ∈ s) : t⁻¹ ⊆ s / t := by
  rw [div_eq_mul_inv]; exact subset_mul_right _ hs

@[to_additive (attr := simp) zsmul_empty]
/-
**Finset.empty_zpow** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
形式化陈述：empty_zpow (hn : n != 0) : (∅ : Finset α) ^ n = ∅
参数：hn : n != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `zpow_natCast`：zpow_natCast (a : G) : forall n : Nat, a ^ (n : Int) = a ^
 n | 0 => (zpow_zero _).trans (pow_zero _).symm | n + 1 => calc a ^ (↑(n + 1) : 
In…
· 使用引理 `Finset.empty_pow`：empty_pow (hn : n != 0) : (∅ : Finset α) ^ n = ∅
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `zpow_negSucc`：zpow_negSucc (a : G) (n : Nat) : a ^ (Int.negSucc n) = (a 
^ (n + 1))⁻¹
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `and_false`：∀ (p : Prop), (p ∧ False) = False
-/
lemma empty_zpow (hn : n ≠ 0) : (∅ : Finset α) ^ n = ∅ := by cases n <;> simp_all

@[to_additive]
/-
**Finset.Nonempty.zpow** 是 Mathlib 中的一个定理，位于命名空间 `Finset.Nonempty`。
形式化陈述：∀ {α : Type u_2} [inst : DecidableEq α] [inst_1 : DivisionMonoid α] {s : F
inset α},   s.Nonempty → ∀ {n : ℤ}, (s ^ n).Nonempty
参数：s ^ n。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.Nonempty.pow`：∀ {α : Type u_2} [inst : DecidableEq α] [inst_1 : M
onoid α] {s : Finset α}, s.Nonempty → ∀ {n : ℕ}, (s ^ n).Nonempty
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `zpow_negSucc`：zpow_negSucc (a : G) (n : Nat) : a ^ (Int.negSucc n) = (a 
^ (n + 1))⁻¹
-/
lemma Nonempty.zpow (hs : s.Nonempty) : ∀ {n : ℤ}, (s ^ n).Nonempty
  | (n : ℕ) => hs.pow
  | .negSucc n => by simpa using hs.pow
/-
**Finset.zpow_eq_empty** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：∀ {α : Type u_2} [inst : DecidableEq α] [inst_1 : DivisionMonoid α] {s : F
inset α} {n : ℤ}, s ^ n = ∅ ↔ s = ∅ ∧ n ≠ 0
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose₁`：contrapose₁ {p q : Prop} : (¬ q -
> ¬ p) -> (p -> q)
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Mathlib.Tactic.Push.not_and_or_eq`：not_and_or_eq : (¬ (p ∧ q)) = (¬ p ∨ 
¬ q)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.Nonempty.zpow`：∀ {α : Type u_2} [inst : DecidableEq α] [inst_1 : 
DivisionMonoid α] {s : Finset α},   s.Nonempty → ∀ {n : ℤ}, (s ^ n).Nonempty
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用引理 `zpow_ofNat`：zpow_ofNat (a : G) (n : Nat) : a ^ (ofNat(n) : Int) = a ^ Of
Nat.ofNat n
· 使用定理 `pow_zero`：pow_zero (a : M) : a ^ 0 = 1
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `Finset.empty_zpow`：empty_zpow (hn : n != 0) : (∅ : Finset α) ^ n = ∅
-/
@[to_additive (attr := simp)] lemma zpow_eq_empty : s ^ n = ∅ ↔ s = ∅ ∧ n ≠ 0 := by
  constructor
  · contrapose! +distrib
    rintro (hs | rfl)
    · exact hs.zpow
    · simp
  · rintro ⟨rfl, hn⟩
    exact empty_zpow hn

@[to_additive (attr := simp) zsmul_singleton]
/-
**Finset.singleton_zpow** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
形式化陈述：singleton_zpow (a : α) (n : Int) : ({a} : Finset α) ^ n = {a ^ n}
参数：a : α；n : Int。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `zpow_natCast`：zpow_natCast (a : G) : forall n : Nat, a ^ (n : Int) = a ^
 n | 0 => (zpow_zero _).trans (pow_zero _).symm | n + 1 => calc a ^ (↑(n + 1) : 
In…
· 使用定理 `Finset.singleton_pow`：∀ {α : Type u_2} [inst : DecidableEq α] [inst_1 : 
Monoid α] (a : α) (n : ℕ), {a} ^ n = {a ^ n}
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `zpow_negSucc`：zpow_negSucc (a : G) (n : Nat) : a ^ (Int.negSucc n) = (a 
^ (n + 1))⁻¹
· 使用定理 `Finset.inv_singleton`：inv_singleton (a : α) : ({a} : Finset α)⁻¹ = {a⁻¹}
-/
lemma singleton_zpow (a : α) (n : ℤ) : ({a} : Finset α) ^ n = {a ^ n} := by cases n <;> simp

end DivisionMonoid

/-- `Finset α` is a commutative division monoid under pointwise operations if `α` is. -/
@[to_additive (attr := instance_reducible) subtractionCommMonoid
  /-- `Finset α` is a commutative subtraction monoid under pointwise operations if `α` is. -/]
/-
**Finset.divisionCommMonoid** 是 Mathlib 中的一个定义，位于命名空间 `Finset`。
形式化陈述：{α : Type u_2} → [DecidableEq α] → [DivisionCommMonoid α] → DivisionCommMo
noid (Finset α)
参数：Finset α。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.coe_injective`：coe_injective {α} : Injective ((↑) : Finset α -> S
et α)
-/
protected def divisionCommMonoid [DivisionCommMonoid α] :
    DivisionCommMonoid (Finset α) :=
  coe_injective.divisionCommMonoid _ coe_one coe_mul coe_inv coe_div coe_pow coe_zpow

scoped[Pointwise] attribute [instance] Finset.divisionCommMonoid Finset.subtractionCommMonoid
section Group

variable [Group α] [DivisionMonoid β] [FunLike F α β] [MonoidHomClass F α β]
variable (f : F) {s t : Finset α} {a b : α}

/-! Note that `Finset` is not a `Group` because `s / s ≠ 1` in general. -/


@[to_additive (attr := simp)]
/-
**Finset.one_mem_div_iff** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：one_mem_div_iff : (1 : α) in s / t ↔ ¬Disjoint s t
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.mem_coe`：mem_coe {a : α} {s : Finset α} : a in (s : Set α) ↔ a in
 (s : Finset α)
· 使用定理 `Finset.disjoint_coe`：disjoint_coe : Disjoint (s : Set α) t ↔ Disjoint s 
t
· 使用定理 `Finset.coe_div`：coe_div (s t : Finset α) : (↑(s / t) : Set α) = ↑s / ↑t
· 使用定理 `Set.one_mem_div_iff`：one_mem_div_iff : (1 : α) in s / t ↔ ¬Disjoint s t
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a

--- 原说明 ---
Note that `Finset` is not a `Group` because `s / s ≠ 1` in general.
-/
theorem one_mem_div_iff : (1 : α) ∈ s / t ↔ ¬Disjoint s t := by
  rw [← mem_coe, ← disjoint_coe, coe_div, Set.one_mem_div_iff]

@[to_additive (attr := simp)]
/-
**Finset.one_mem_inv_mul_iff** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
形式化陈述：one_mem_inv_mul_iff : (1 : α) in t⁻¹ * s ↔ ¬Disjoint s t
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Exists.elim`：∀ {α : Sort u} {p : α → Prop} {b : Prop}, (∃ x, p x) → (∀ (
a : α), p a → b) → b
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `inv_inv`：inv_inv (a : G) : a⁻¹⁻¹ = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `and_true`：∀ (p : Prop), (p ∧ True) = p
-/
lemma one_mem_inv_mul_iff : (1 : α) ∈ t⁻¹ * s ↔ ¬Disjoint s t := by
  aesop (add simp [not_disjoint_iff_nonempty_inter, mem_mul, mul_eq_one_iff_eq_inv,
    Finset.Nonempty])

@[to_additive]
/-
**Finset.one_notMem_div_iff** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：one_notMem_div_iff : (1 : α) ∉ s / t ↔ Disjoint s t
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.not_left`：Iff.not_left (h : a ↔ ¬b) : ¬a ↔ b
· 使用定理 `Finset.one_mem_div_iff`：one_mem_div_iff : (1 : α) in s / t ↔ ¬Disjoint s
 t
-/
theorem one_notMem_div_iff : (1 : α) ∉ s / t ↔ Disjoint s t :=
  one_mem_div_iff.not_left

@[to_additive]
/-
**Finset.one_notMem_inv_mul_iff** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
形式化陈述：one_notMem_inv_mul_iff : (1 : α) ∉ t⁻¹ * s ↔ Disjoint s t
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.not_left`：Iff.not_left (h : a ↔ ¬b) : ¬a ↔ b
· 使用引理 `Finset.one_mem_inv_mul_iff`：one_mem_inv_mul_iff : (1 : α) in t⁻¹ * s ↔ ¬
Disjoint s t
-/
lemma one_notMem_inv_mul_iff : (1 : α) ∉ t⁻¹ * s ↔ Disjoint s t := one_mem_inv_mul_iff.not_left

@[to_additive]
/-
**Finset.Nonempty.one_mem_div** 是 Mathlib 中的一个定理，位于命名空间 `Finset.Nonempty`。
形式化陈述：∀ {α : Type u_2} [inst : DecidableEq α] [inst_1 : Group α] {s : Finset α},
 s.Nonempty → 1 ∈ s / s
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Finset.mem_div`：mem_div : a in s / t ↔ exists b in s, exists c in t, b /
 c = a
· 使用定理 `div_self'`：div_self' (a : G) : a / a = 1
-/
theorem Nonempty.one_mem_div (h : s.Nonempty) : (1 : α) ∈ s / s :=
  let ⟨a, ha⟩ := h
  mem_div.2 ⟨a, ha, a, ha, div_self' _⟩

@[to_additive]
/-
**Finset.isUnit_singleton** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：isUnit_singleton (a : α) : IsUnit ({a} : Finset α)
参数：a : α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsUnit.finset`：∀ {α : Type u_2} [inst : DecidableEq α] [inst_1 : Monoid 
α] {a : α}, IsUnit a → IsUnit {a}
· 使用引理 `Group.isUnit`：Group.isUnit [Group α] (a : α) : IsUnit a
-/
theorem isUnit_singleton (a : α) : IsUnit ({a} : Finset α) :=
  (Group.isUnit a).finset
/-
**Finset.isUnit_iff_singleton** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：isUnit_iff_singleton : IsUnit s ↔ exists a, s = {a}
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `and_true`：∀ (p : Prop), (p ∧ True) = p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem isUnit_iff_singleton : IsUnit s ↔ ∃ a, s = {a} := by
  simp only [isUnit_iff, Group.isUnit, and_true]

@[simp]
/-
**Finset.isUnit_iff_singleton_aux** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：isUnit_iff_singleton_aux {α} [Group α] {s : Finset α} : (exists a, s = {a}
 ∧ IsUnit a) ↔ exists a, s = {a}
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `and_true`：∀ (p : Prop), (p ∧ True) = p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem isUnit_iff_singleton_aux {α} [Group α] {s : Finset α} :
    (∃ a, s = {a} ∧ IsUnit a) ↔ ∃ a, s = {a} := by
  simp only [Group.isUnit, and_true]

@[to_additive (attr := simp)]
/-
**Finset.image_mul_left** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：image_mul_left : image (fun b => a * b) t = preimage t (fun b => a⁻¹ * b) 
(mul_right_injective _).injOn
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.coe_injective`：coe_injective {α} : Injective ((↑) : Finset α -> S
et α)
· 使用定理 `Function.Injective.injOn`：∀ {α : Type u_1} {β : Type u_2} {f : α → β}, F
unction.Injective f → ∀ {s : Set α}, Set.InjOn f s
· 使用定理 `mul_right_injective`：mul_right_injective (a : G) : Injective (a * ·)
· 使用定理 `LeftCancelSemigroup.toIsLeftCancelMul`：∀ {G : Type u} [self : LeftCancel
Semigroup G], IsLeftCancelMul G
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.coe_image`：coe_image : ↑(s.image f) = f '' ↑s
· 使用定理 `Set.image_mul_left`：image_mul_left : (a * ·) '' t = (a⁻¹ * ·) ⁻¹' t
· 使用定理 `Finset.coe_preimage`：coe_preimage {f : α -> β} (s : Finset β) (hf : Set.
InjOn f (f ⁻¹' ↑s)) : (↑(preimage s f hf) : Set α) = f ⁻¹' ↑s
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem image_mul_left :
    image (fun b => a * b) t = preimage t (fun b => a⁻¹ * b) (mul_right_injective _).injOn :=
  coe_injective <| by simp

@[to_additive (attr := simp)]
/-
**Finset.image_mul_right** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：image_mul_right : image (· * b) t = preimage t (· * b⁻¹) (mul_left_injecti
ve _).injOn
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.coe_injective`：coe_injective {α} : Injective ((↑) : Finset α -> S
et α)
· 使用定理 `Function.Injective.injOn`：∀ {α : Type u_1} {β : Type u_2} {f : α → β}, F
unction.Injective f → ∀ {s : Set α}, Set.InjOn f s
· 使用定理 `mul_left_injective`：mul_left_injective (a : G) : Function.Injective (· *
 a)
· 使用定理 `RightCancelSemigroup.toIsRightCancelMul`：∀ {G : Type u} [self : RightCan
celSemigroup G], IsRightCancelMul G
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.coe_image`：coe_image : ↑(s.image f) = f '' ↑s
· 使用定理 `Set.image_mul_right`：image_mul_right : (· * b) '' t = (· * b⁻¹) ⁻¹' t
· 使用定理 `Finset.coe_preimage`：coe_preimage {f : α -> β} (s : Finset β) (hf : Set.
InjOn f (f ⁻¹' ↑s)) : (↑(preimage s f hf) : Set α) = f ⁻¹' ↑s
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem image_mul_right : image (· * b) t = preimage t (· * b⁻¹) (mul_left_injective _).injOn :=
  coe_injective <| by simp

@[to_additive]
/-
**Finset.image_mul_left'** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：image_mul_left' : image (fun b => a⁻¹ * b) t = preimage t (fun b => a * b)
 (mul_right_injective _).injOn
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Function.Injective.injOn`：∀ {α : Type u_1} {β : Type u_2} {f : α → β}, F
unction.Injective f → ∀ {s : Set α}, Set.InjOn f s
· 使用定理 `mul_right_injective`：mul_right_injective (a : G) : Injective (a * ·)
· 使用定理 `LeftCancelSemigroup.toIsLeftCancelMul`：∀ {G : Type u} [self : LeftCancel
Semigroup G], IsLeftCancelMul G
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `inv_inv`：inv_inv (a : G) : a⁻¹⁻¹ = a
· 使用定理 `Finset.image_mul_left`：image_mul_left : image (fun b => a * b) t = preim
age t (fun b => a⁻¹ * b) (mul_right_injective _).injOn
· 使用定理 `Finset.preimage.congr_simp`：∀ {α : Type u} {β : Type v} (s s_1 : Finset 
β) (e_s : s = s_1) (f f_1 : α → β) (e_f : f = f_1)   (hf : Set.InjOn f (f ⁻¹' ↑s
)), s.preimage f…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem image_mul_left' :
    image (fun b => a⁻¹ * b) t = preimage t (fun b => a * b) (mul_right_injective _).injOn := by
  simp

@[to_additive]
/-
**Finset.image_mul_right'** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：image_mul_right' : image (· * b⁻¹) t = preimage t (· * b) (mul_left_inject
ive _).injOn
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Function.Injective.injOn`：∀ {α : Type u_1} {β : Type u_2} {f : α → β}, F
unction.Injective f → ∀ {s : Set α}, Set.InjOn f s
· 使用定理 `mul_left_injective`：mul_left_injective (a : G) : Function.Injective (· *
 a)
· 使用定理 `RightCancelSemigroup.toIsRightCancelMul`：∀ {G : Type u} [self : RightCan
celSemigroup G], IsRightCancelMul G
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `inv_inv`：inv_inv (a : G) : a⁻¹⁻¹ = a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Finset.image_mul_right`：image_mul_right : image (· * b) t = preimage t (
· * b⁻¹) (mul_left_injective _).injOn
· 使用定理 `Finset.preimage.congr_simp`：∀ {α : Type u} {β : Type v} (s s_1 : Finset 
β) (e_s : s = s_1) (f f_1 : α → β) (e_f : f = f_1)   (hf : Set.InjOn f (f ⁻¹' ↑s
)), s.preimage f…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem image_mul_right' :
    image (· * b⁻¹) t = preimage t (· * b) (mul_left_injective _).injOn := by simp

@[to_additive]
/-
**Finset.image_inv** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
形式化陈述：image_inv (f : F) (s : Finset α) : s⁻¹.image f = (s.image f)⁻¹
参数：f : F；s : Finset α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.image_comm`：image_comm {β'} [DecidableEq β'] [DecidableEq γ] {f :
 β -> γ} {g : α -> β} {f' : α -> β'} {g' : β' -> γ} (h_comm : forall a, f (g a) 
= g' (f…
· 使用定理 `map_inv`：map_inv [Group G] [DivisionMonoid H] [MonoidHomClass F G H] (f 
: F) (a : G) : f a⁻¹ = (f a)⁻¹
-/
lemma image_inv (f : F) (s : Finset α) : s⁻¹.image f = (s.image f)⁻¹ := image_comm (map_inv _)
/-
**Finset.image_div** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：image_div : (s / t).image (f : α -> β) = s.image f / t.image f
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.image_image₂_distrib`：image_image₂_distrib {g : γ -> δ} {f' : α' 
-> β' -> δ} {g₁ : α -> α'} {g₂ : β -> β'} (h_distrib : forall a b, g (f a b) = f
' (g₁ a) (g₂ b)) …
· 使用定理 `map_div`：map_div [Group G] [DivisionMonoid H] [MonoidHomClass F G H] (f 
: F) : forall a b, f (a / b) = f a / f b
-/
theorem image_div : (s / t).image (f : α → β) = s.image f / t.image f :=
  image_image₂_distrib <| map_div f

end Group

end Instances

section Group

variable [Group α] {a b : α}

@[to_additive (attr := simp)]
/-
**Finset.preimage_mul_left_singleton** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：preimage_mul_left_singleton : preimage {b} (a * ·) (mul_right_injective _)
.injOn = {a⁻¹ * b}
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Injective.injOn`：∀ {α : Type u_1} {β : Type u_2} {f : α → β}, F
unction.Injective f → ∀ {s : Set α}, Set.InjOn f s
· 使用定理 `mul_right_injective`：mul_right_injective (a : G) : Injective (a * ·)
· 使用定理 `LeftCancelSemigroup.toIsLeftCancelMul`：∀ {G : Type u} [self : LeftCancel
Semigroup G], IsLeftCancelMul G
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.image_mul_left'`：image_mul_left' : image (fun b => a⁻¹ * b) t = p
reimage t (fun b => a * b) (mul_right_injective _).injOn
· 使用定理 `Finset.image_singleton`：image_singleton (f : α -> β) (a : α) : image f {
a} = {f a}
-/
theorem preimage_mul_left_singleton :
    preimage {b} (a * ·) (mul_right_injective _).injOn = {a⁻¹ * b} := by
  classical rw [← image_mul_left', image_singleton]

@[to_additive (attr := simp)]
/-
**Finset.preimage_mul_right_singleton** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：preimage_mul_right_singleton : preimage {b} (· * a) (mul_left_injective _)
.injOn = {b * a⁻¹}
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Injective.injOn`：∀ {α : Type u_1} {β : Type u_2} {f : α → β}, F
unction.Injective f → ∀ {s : Set α}, Set.InjOn f s
· 使用定理 `mul_left_injective`：mul_left_injective (a : G) : Function.Injective (· *
 a)
· 使用定理 `RightCancelSemigroup.toIsRightCancelMul`：∀ {G : Type u} [self : RightCan
celSemigroup G], IsRightCancelMul G
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.image_mul_right'`：image_mul_right' : image (· * b⁻¹) t = preimage
 t (· * b) (mul_left_injective _).injOn
· 使用定理 `Finset.image_singleton`：image_singleton (f : α -> β) (a : α) : image f {
a} = {f a}
-/
theorem preimage_mul_right_singleton :
    preimage {b} (· * a) (mul_left_injective _).injOn = {b * a⁻¹} := by
  classical rw [← image_mul_right', image_singleton]

@[to_additive (attr := simp)]
/-
**Finset.preimage_mul_left_one** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：preimage_mul_left_one : preimage 1 (a * ·) (mul_right_injective _).injOn =
 {a⁻¹}
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Injective.injOn`：∀ {α : Type u_1} {β : Type u_2} {f : α → β}, F
unction.Injective f → ∀ {s : Set α}, Set.InjOn f s
· 使用定理 `mul_right_injective`：mul_right_injective (a : G) : Injective (a * ·)
· 使用定理 `LeftCancelSemigroup.toIsLeftCancelMul`：∀ {G : Type u} [self : LeftCancel
Semigroup G], IsLeftCancelMul G
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.image_mul_left'`：image_mul_left' : image (fun b => a⁻¹ * b) t = p
reimage t (fun b => a * b) (mul_right_injective _).injOn
· 使用定理 `Finset.image_one`：image_one [DecidableEq β] {f : α -> β} : image f 1 = {
f 1}
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
-/
theorem preimage_mul_left_one : preimage 1 (a * ·) (mul_right_injective _).injOn = {a⁻¹} := by
  classical rw [← image_mul_left', image_one, mul_one]

@[to_additive (attr := simp)]
/-
**Finset.preimage_mul_right_one** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：preimage_mul_right_one : preimage 1 (· * b) (mul_left_injective _).injOn =
 {b⁻¹}
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Injective.injOn`：∀ {α : Type u_1} {β : Type u_2} {f : α → β}, F
unction.Injective f → ∀ {s : Set α}, Set.InjOn f s
· 使用定理 `mul_left_injective`：mul_left_injective (a : G) : Function.Injective (· *
 a)
· 使用定理 `RightCancelSemigroup.toIsRightCancelMul`：∀ {G : Type u} [self : RightCan
celSemigroup G], IsRightCancelMul G
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.image_mul_right'`：image_mul_right' : image (· * b⁻¹) t = preimage
 t (· * b) (mul_left_injective _).injOn
· 使用定理 `Finset.image_one`：image_one [DecidableEq β] {f : α -> β} : image f 1 = {
f 1}
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
-/
theorem preimage_mul_right_one : preimage 1 (· * b) (mul_left_injective _).injOn = {b⁻¹} := by
  classical rw [← image_mul_right', image_one, one_mul]

@[to_additive]
/-
**Finset.preimage_mul_left_one'** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：preimage_mul_left_one' : preimage 1 (a⁻¹ * ·) (mul_right_injective _).injO
n = {a}
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Injective.injOn`：∀ {α : Type u_1} {β : Type u_2} {f : α → β}, F
unction.Injective f → ∀ {s : Set α}, Set.InjOn f s
· 使用定理 `mul_right_injective`：mul_right_injective (a : G) : Injective (a * ·)
· 使用定理 `LeftCancelSemigroup.toIsLeftCancelMul`：∀ {G : Type u} [self : LeftCancel
Semigroup G], IsLeftCancelMul G
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.preimage_mul_left_one`：preimage_mul_left_one : preimage 1 (a * ·)
 (mul_right_injective _).injOn = {a⁻¹}
· 使用定理 `inv_inv`：inv_inv (a : G) : a⁻¹⁻¹ = a
-/
theorem preimage_mul_left_one' : preimage 1 (a⁻¹ * ·) (mul_right_injective _).injOn = {a} := by
  rw [preimage_mul_left_one, inv_inv]

@[to_additive]
/-
**Finset.preimage_mul_right_one'** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：preimage_mul_right_one' : preimage 1 (· * b⁻¹) (mul_left_injective _).injO
n = {b}
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Injective.injOn`：∀ {α : Type u_1} {β : Type u_2} {f : α → β}, F
unction.Injective f → ∀ {s : Set α}, Set.InjOn f s
· 使用定理 `mul_left_injective`：mul_left_injective (a : G) : Function.Injective (· *
 a)
· 使用定理 `RightCancelSemigroup.toIsRightCancelMul`：∀ {G : Type u} [self : RightCan
celSemigroup G], IsRightCancelMul G
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.preimage_mul_right_one`：preimage_mul_right_one : preimage 1 (· * 
b) (mul_left_injective _).injOn = {b⁻¹}
· 使用定理 `inv_inv`：inv_inv (a : G) : a⁻¹⁻¹ = a
-/
theorem preimage_mul_right_one' : preimage 1 (· * b⁻¹) (mul_left_injective _).injOn = {b} := by
  rw [preimage_mul_right_one, inv_inv]

end Group

section Monoid
variable [DecidableEq α] [DecidableEq β] [Monoid α] [Monoid β] [FunLike F α β]

@[to_additive]
/-
**Finset.image_pow_of_ne_zero** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：∀ {F : Type u_1} {α : Type u_2} {β : Type u_3} [inst : DecidableEq α] [ins
t_1 : DecidableEq β] [inst_2 : Monoid α]   [inst_3 : Monoid β] [inst_4 : FunLike
 F α β] [MulHomClass F α β] {n : ℕ},   n ≠ 0 → ∀ (f : F) (s : Finset α), Finset.
image (⇑f) (s ^ n) = Finset.image (⇑f) s ^ n
参数：f : F；s : Finset α；⇑f；s ^ n；⇑f。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma image_pow_of_ne_zero [MulHomClass F α β] :
    ∀ {n}, n ≠ 0 → ∀ (f : F) (s : Finset α), (s ^ n).image f = s.image f ^ n
  | 1, _ => by simp
  | n + 2, _ => by simp [image_mul, pow_succ _ n.succ, image_pow_of_ne_zero]

@[to_additive]
/-
**Finset.image_pow** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：∀ {F : Type u_1} {α : Type u_2} {β : Type u_3} [inst : DecidableEq α] [ins
t_1 : DecidableEq β] [inst_2 : Monoid α]   [inst_3 : Monoid β] [inst_4 : FunLike
 F α β] [MonoidHomClass F α β] (f : F) (s : Finset α) (n : ℕ),   Finset.image (⇑
f) (s ^ n) = Finset.image (⇑f) s ^ n
参数：f : F；s : Finset α；n : ℕ；⇑f；s ^ n；⇑f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `pow_zero`：pow_zero (a : M) : a ^ 0 = 1
· 使用定理 `Finset.image_one`：image_one [DecidableEq β] {f : α -> β} : image f 1 = {
f 1}
· 使用定理 `map_one`：map_one [OneHomClass F M N] (f : F) : f 1 = 1
· 使用定理 `MonoidHomClass.toOneHomClass`：∀ {F : Type u_10} {M : outParam (Type u_11
)} {N : outParam (Type u_12)} {inst : MulOne M} {inst_1 : MulOne N}   {inst_2 : 
FunLike F M N} [se…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Finset.image_pow_of_ne_zero`：∀ {F : Type u_1} {α : Type u_2} {β : Type u
_3} [inst : DecidableEq α] [inst_1 : DecidableEq β] [inst_2 : Monoid α]   [inst_
3 : Monoid β] [in…
· 使用定理 `MonoidHomClass.toMulHomClass`：∀ {F : Type u_10} {M : outParam (Type u_11
)} {N : outParam (Type u_12)} {inst : MulOne M} {inst_1 : MulOne N}   {inst_2 : 
FunLike F M N} [se…
· 使用定理 `Nat.succ_ne_zero`：∀ (n : ℕ), n.succ ≠ 0
-/
lemma image_pow [MonoidHomClass F α β] (f : F) (s : Finset α) : ∀ n, (s ^ n).image f = s.image f ^ n
  | 0 => by simp [singleton_one]
  | n + 1 => image_pow_of_ne_zero n.succ_ne_zero ..

end Monoid

section IsLeftCancelMul

variable [Mul α] [IsLeftCancelMul α] [DecidableEq α] {s t : Finset α} {a : α}

@[to_additive]
/-
**Finset.Nontrivial.mul_left** 是 Mathlib 中的一个定理，位于命名空间 `Finset.Nontrivial`。
形式化陈述：∀ {α : Type u_2} [inst : Mul α] [IsLeftCancelMul α] [inst_2 : DecidableEq 
α] {s t : Finset α},   t.Nontrivial → s.Nonempty → (s * t).Nontrivial
参数：s * t。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.mul_mem_mul`：mul_mem_mul : a in s -> b in t -> a * b in s * t
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
-/
lemma Nontrivial.mul_left : t.Nontrivial → s.Nonempty → (s * t).Nontrivial := by
  rintro ⟨a, ha, b, hb, hab⟩ ⟨c, hc⟩
  exact ⟨c * a, mul_mem_mul hc ha, c * b, mul_mem_mul hc hb, by simpa⟩

@[to_additive]
/-
**Finset.Nontrivial.mul** 是 Mathlib 中的一个定理，位于命名空间 `Finset.Nontrivial`。
形式化陈述：∀ {α : Type u_2} [inst : Mul α] [IsLeftCancelMul α] [inst_2 : DecidableEq 
α] {s t : Finset α},   s.Nontrivial → t.Nontrivial → (s * t).Nontrivial
参数：s * t。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.Nontrivial.mul_left`：∀ {α : Type u_2} [inst : Mul α] [IsLeftCance
lMul α] [inst_2 : DecidableEq α] {s t : Finset α},   t.Nontrivial → s.Nonempty →
 (s * t).Nontriv…
· 使用定理 `Finset.Nontrivial.nonempty`：∀ {α : Type u_1} {s : Finset α}, s.Nontrivia
l → s.Nonempty
-/
lemma Nontrivial.mul (hs : s.Nontrivial) (ht : t.Nontrivial) : (s * t).Nontrivial :=
  ht.mul_left hs.nonempty

@[to_additive (attr := simp)]
/-
**Finset.card_singleton_mul** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：card_singleton_mul (a : α) (t : Finset α) : #({a} * t) = #t
参数：a : α；t : Finset α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.card_image₂_singleton_left`：card_image₂_singleton_left (hf : Inje
ctive (f a)) : #(image₂ f {a} t) = #t
· 使用定理 `mul_right_injective`：mul_right_injective (a : G) : Injective (a * ·)
-/
theorem card_singleton_mul (a : α) (t : Finset α) : #({a} * t) = #t :=
  card_image₂_singleton_left _ <| mul_right_injective _

@[to_additive]
/-
**Finset.singleton_mul_inter** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：singleton_mul_inter (a : α) (s t : Finset α) : {a} * (s inter t) = {a} * s
 inter ({a} * t)
参数：a : α；s t : Finset α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.image₂_singleton_inter`：image₂_singleton_inter [DecidableEq β] (t
₁ t₂ : Finset β) (hf : Injective (f a)) : image₂ f {a} (t₁ inter t₂) = image₂ f 
{a} t₁ inter image₂…
· 使用定理 `mul_right_injective`：mul_right_injective (a : G) : Injective (a * ·)
-/
theorem singleton_mul_inter (a : α) (s t : Finset α) : {a} * (s ∩ t) = {a} * s ∩ ({a} * t) :=
  image₂_singleton_inter _ _ <| mul_right_injective _

@[to_additive]
/-
**Finset.card_le_card_mul_left** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：card_le_card_mul_left {s : Finset α} (hs : s.Nonempty) : #t <= #(s * t)
参数：hs : s.Nonempty。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Finset.card_le_card_mul_left_of_injective`：card_le_card_mul_left_of_inje
ctive (has : a in s) (ha : IsLeftRegular a) : #t <= #(s * t)
· 使用定理 `mul_right_injective`：mul_right_injective (a : G) : Injective (a * ·)
-/
theorem card_le_card_mul_left {s : Finset α} (hs : s.Nonempty) : #t ≤ #(s * t) :=
  have ⟨_, ha⟩ := hs; card_le_card_mul_left_of_injective ha (mul_right_injective _)

/--
The size of `s * s` is at least the size of `s`, version with left-cancellative multiplication.
See `card_le_card_mul_self'` for the version with right-cancellative multiplication.
-/
@[to_additive
/-- The size of `s + s` is at least the size of `s`, version with left-cancellative addition.
See `card_le_card_add_self'` for the version with right-cancellative addition. -/]
/-
**Finset.card_le_card_mul_self** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：card_le_card_mul_self {s : Finset α} : #s <= #(s * s)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.eq_empty_or_nonempty`：eq_empty_or_nonempty (s : Finset α) : s = ∅
 ∨ s.Nonempty
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.mul_empty`：mul_empty (s : Finset α) : s * ∅ = ∅
-/
theorem card_le_card_mul_self {s : Finset α} : #s ≤ #(s * s) := by
  cases s.eq_empty_or_nonempty <;> simp [card_le_card_mul_left, *]

end IsLeftCancelMul

section IsRightCancelMul

variable [Mul α] [IsRightCancelMul α] [DecidableEq α] {s t : Finset α} {a : α}

@[to_additive]
/-
**Finset.Nontrivial.mul_right** 是 Mathlib 中的一个定理，位于命名空间 `Finset.Nontrivial`。
形式化陈述：∀ {α : Type u_2} [inst : Mul α] [IsRightCancelMul α] [inst_2 : DecidableEq
 α] {s t : Finset α},   s.Nontrivial → t.Nonempty → (s * t).Nontrivial
参数：s * t。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.mul_mem_mul`：mul_mem_mul : a in s -> b in t -> a * b in s * t
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
-/
lemma Nontrivial.mul_right : s.Nontrivial → t.Nonempty → (s * t).Nontrivial := by
  rintro ⟨a, ha, b, hb, hab⟩ ⟨c, hc⟩
  exact ⟨a * c, mul_mem_mul ha hc, b * c, mul_mem_mul hb hc, by simpa⟩

@[to_additive (attr := simp)]
/-
**Finset.card_mul_singleton** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：card_mul_singleton (s : Finset α) (a : α) : #(s * {a}) = #s
参数：s : Finset α；a : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.card_image₂_singleton_right`：card_image₂_singleton_right (hf : In
jective fun a => f a b) : #(image₂ f s {b}) = #s
· 使用定理 `mul_left_injective`：mul_left_injective (a : G) : Function.Injective (· *
 a)
-/
theorem card_mul_singleton (s : Finset α) (a : α) : #(s * {a}) = #s :=
  card_image₂_singleton_right _ <| mul_left_injective _

@[to_additive]
/-
**Finset.inter_mul_singleton** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：inter_mul_singleton (s t : Finset α) (a : α) : s inter t * {a} = s * {a} i
nter (t * {a})
参数：s t : Finset α；a : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.image₂_inter_singleton`：image₂_inter_singleton [DecidableEq α] (s
₁ s₂ : Finset α) (hf : Injective fun a => f a b) : image₂ f (s₁ inter s₂) {b} = 
image₂ f s₁ {b} int…
· 使用定理 `mul_left_injective`：mul_left_injective (a : G) : Function.Injective (· *
 a)
-/
theorem inter_mul_singleton (s t : Finset α) (a : α) : s ∩ t * {a} = s * {a} ∩ (t * {a}) :=
  image₂_inter_singleton _ _ <| mul_left_injective _

@[to_additive]
/-
**Finset.card_le_card_mul_right** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：card_le_card_mul_right (ht : t.Nonempty) : #s <= #(s * t)
参数：ht : t.Nonempty。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Finset.card_le_card_mul_right_of_injective`：card_le_card_mul_right_of_in
jective (hat : a in t) (ha : IsRightRegular a) : #s <= #(s * t)
· 使用定理 `mul_left_injective`：mul_left_injective (a : G) : Function.Injective (· *
 a)
-/
theorem card_le_card_mul_right (ht : t.Nonempty) : #s ≤ #(s * t) :=
  have ⟨_, ha⟩ := ht; card_le_card_mul_right_of_injective ha (mul_left_injective _)

/--
The size of `s * s` is at least the size of `s`, version with right-cancellative multiplication.
See `card_le_card_mul_self` for the version with left-cancellative multiplication.
-/
@[to_additive
/-- The size of `s + s` is at least the size of `s`, version with right-cancellative addition.
See `card_le_card_add_self` for the version with left-cancellative addition. -/]
/-
**Finset.card_le_card_mul_self'** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：card_le_card_mul_self' : #s <= #(s * s)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.eq_empty_or_nonempty`：eq_empty_or_nonempty (s : Finset α) : s = ∅
 ∨ s.Nonempty
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.mul_empty`：mul_empty (s : Finset α) : s * ∅ = ∅
-/
theorem card_le_card_mul_self' : #s ≤ #(s * s) := by
  cases s.eq_empty_or_nonempty <;> simp [card_le_card_mul_right, *]

end IsRightCancelMul

section CancelMonoid
variable [DecidableEq α] [CancelMonoid α] {s : Finset α} {m n : ℕ}

@[to_additive]
/-
**Finset.Nontrivial.pow** 是 Mathlib 中的一个定理，位于命名空间 `Finset.Nontrivial`。
形式化陈述：∀ {α : Type u_2} [inst : DecidableEq α] [inst_1 : CancelMonoid α] {s : Fin
set α},   s.Nontrivial → ∀ {n : ℕ}, n ≠ 0 → (s ^ n).Nontrivial
参数：s ^ n。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma Nontrivial.pow (hs : s.Nontrivial) : ∀ {n}, n ≠ 0 → (s ^ n).Nontrivial
  | 1, _ => by simpa
  | n + 2, _ => by simpa [pow_succ] using (hs.pow n.succ_ne_zero).mul hs

/-- See `Finset.card_pow_mono` for a version that works for the empty set. -/
@[to_additive /-- See `Finset.card_nsmul_mono` for a version that works for the empty set. -/]
/-
**Finset.Nonempty.card_pow_mono** 是 Mathlib 中的一个定理，位于命名空间 `Finset.Nonempty`。
形式化陈述：∀ {α : Type u_2} [inst : DecidableEq α] [inst_1 : CancelMonoid α] {s : Fin
set α},   s.Nonempty → Monotone fun n => (s ^ n).card
参数：s ^ n。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `monotone_nat_of_le_succ`：monotone_nat_of_le_succ {f : Nat -> α} (hf : fo
rall n, f n <= f (n + 1)) : Monotone f
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `pow_succ`：pow_succ (a : M) (n : Nat) : a ^ (n + 1) = a ^ n * a
· 使用定理 `Finset.card_le_card_mul_right`：card_le_card_mul_right (ht : t.Nonempty) 
: #s <= #(s * t)
· 使用定理 `RightCancelSemigroup.toIsRightCancelMul`：∀ {G : Type u} [self : RightCan
celSemigroup G], IsRightCancelMul G

--- 原说明 ---
See `Finset.card_pow_mono` for a version that works for the empty set.
-/
protected lemma Nonempty.card_pow_mono (hs : s.Nonempty) : Monotone fun n : ℕ ↦ #(s ^ n) :=
  monotone_nat_of_le_succ fun n ↦ by rw [pow_succ]; exact card_le_card_mul_right hs

/-- See `Finset.Nonempty.card_pow_mono` for a version that works for zero powers. -/
@[to_additive
/-- See `Finset.Nonempty.card_nsmul_mono` for a version that works for zero scalars. -/]
/-
**Finset.card_pow_mono** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
形式化陈述：card_pow_mono (hm : m != 0) (hmn : m <= n) : #(s ^ m) <= #(s ^ n)
参数：hm : m != 0；hmn : m <= n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.eq_empty_or_nonempty`：eq_empty_or_nonempty (s : Finset α) : s = ∅
 ∨ s.Nonempty
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Finset.empty_pow`：empty_pow (hn : n != 0) : (∅ : Finset α) ^ n = ∅
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.Nonempty.card_pow_mono`：∀ {α : Type u_2} [inst : DecidableEq α] [
inst_1 : CancelMonoid α] {s : Finset α},   s.Nonempty → Monotone fun n => (s ^ n
).card
-/
lemma card_pow_mono (hm : m ≠ 0) (hmn : m ≤ n) : #(s ^ m) ≤ #(s ^ n) := by
  obtain rfl | hs := s.eq_empty_or_nonempty
  · simp [hm]
  · exact hs.card_pow_mono hmn

@[to_additive]
/-
**Finset.card_le_card_pow** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
形式化陈述：card_le_card_pow (hn : n != 0) : #s <= #(s ^ n)
参数：hn : n != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `pow_one`：pow_one (a : M) : a ^ 1 = a
· 使用引理 `Finset.card_pow_mono`：card_pow_mono (hm : m != 0) (hmn : m <= n) : #(s ^
 m) <= #(s ^ n)
· 使用定理 `one_ne_zero`：∀ {α : Type u_2} [inst : Zero α] [inst_1 : One α] [NeZero 1
], 1 ≠ 0
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Nat.one_le_iff_ne_zero`：∀ {n : ℕ}, 1 ≤ n ↔ n ≠ 0
-/
lemma card_le_card_pow (hn : n ≠ 0) : #s ≤ #(s ^ n) := by
  simpa using card_pow_mono (s := s) one_ne_zero (Nat.one_le_iff_ne_zero.2 hn)

end CancelMonoid

section Group
variable [Group α] [DecidableEq α] {s t : Finset α}

/-
**Finset.card_le_card_div_left** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：∀ {α : Type u_2} [inst : Group α] [inst_1 : DecidableEq α] {s t : Finset α
}, s.Nonempty → t.card ≤ (s / t).card
参数：s / t。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.card_le_card_image₂_left`：card_le_card_image₂_left {s : Finset α}
 (ha : a in s) (hf : Injective (f a)) : #t <= #(image₂ f s t)
· 使用定理 `div_right_injective`：div_right_injective : Function.Injective fun a => b
 / a
-/
@[to_additive] lemma card_le_card_div_left (hs : s.Nonempty) : #t ≤ #(s / t) :=
  have ⟨_, ha⟩ := hs; card_le_card_image₂_left _ ha div_right_injective
/-
**Finset.card_le_card_div_right** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：∀ {α : Type u_2} [inst : Group α] [inst_1 : DecidableEq α] {s t : Finset α
}, t.Nonempty → s.card ≤ (s / t).card
参数：s / t。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.card_le_card_image₂_right`：card_le_card_image₂_right {t : Finset 
β} (hb : b in t) (hf : Injective (f · b)) : #s <= #(image₂ f s t)
· 使用定理 `div_left_injective`：div_left_injective : Function.Injective fun a => a /
 b
-/
@[to_additive] lemma card_le_card_div_right (ht : t.Nonempty) : #s ≤ #(s / t) :=
  have ⟨_, ha⟩ := ht; card_le_card_image₂_right _ ha div_left_injective
/-
**Finset.card_le_card_div_self** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：∀ {α : Type u_2} [inst : Group α] [inst_1 : DecidableEq α] {s : Finset α},
 s.card ≤ (s / s).card
参数：s / s。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.eq_empty_or_nonempty`：eq_empty_or_nonempty (s : Finset α) : s = ∅
 ∨ s.Nonempty
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.div_empty`：div_empty (s : Finset α) : s / ∅ = ∅
-/
@[to_additive] lemma card_le_card_div_self : #s ≤ #(s / s) := by
  cases s.eq_empty_or_nonempty <;> simp [card_le_card_div_left, *]

end Group

end Finset

namespace Fintype
variable {ι : Type*} {α β : ι → Type*} [Fintype ι] [DecidableEq ι] [∀ i, DecidableEq (β i)]
  [∀ i, DecidableEq (α i)]

@[to_additive]
/-
**Fintype.piFinset_mul** 是 Mathlib 中的一个引理，位于命名空间 `Fintype`。
形式化陈述：piFinset_mul [forall i, Mul (α i)] (s t : forall i, Finset (α i)) : piFins
et (fun i => s i * t i) = piFinset s * piFinset t
参数：α i；s t : forall i, Finset (α i)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Fintype.piFinset_image₂`：piFinset_image₂ (f : forall i, α i -> β i -> γ 
i) (s : forall i, Finset (α i)) (t : forall i, Finset (β i)) : piFinset (fun i =
> image₂ (f i…
-/
lemma piFinset_mul [∀ i, Mul (α i)] (s t : ∀ i, Finset (α i)) :
    piFinset (fun i ↦ s i * t i) = piFinset s * piFinset t := piFinset_image₂ _ _ _

@[to_additive]
/-
**Fintype.piFinset_div** 是 Mathlib 中的一个引理，位于命名空间 `Fintype`。
形式化陈述：piFinset_div [forall i, Div (α i)] (s t : forall i, Finset (α i)) : piFins
et (fun i => s i / t i) = piFinset s / piFinset t
参数：α i；s t : forall i, Finset (α i)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Fintype.piFinset_image₂`：piFinset_image₂ (f : forall i, α i -> β i -> γ 
i) (s : forall i, Finset (α i)) (t : forall i, Finset (β i)) : piFinset (fun i =
> image₂ (f i…
-/
lemma piFinset_div [∀ i, Div (α i)] (s t : ∀ i, Finset (α i)) :
    piFinset (fun i ↦ s i / t i) = piFinset s / piFinset t := piFinset_image₂ _ _ _

@[to_additive (attr := simp)]
/-
**Fintype.piFinset_inv** 是 Mathlib 中的一个引理，位于命名空间 `Fintype`。
形式化陈述：piFinset_inv [forall i, Inv (α i)] (s : forall i, Finset (α i)) : piFinset
 (fun i => (s i)⁻¹) = (piFinset s)⁻¹
参数：α i；s : forall i, Finset (α i)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Fintype.piFinset_image`：piFinset_image [forall a, DecidableEq (δ a)] (f 
: forall a, γ a -> δ a) (s : forall a, Finset (γ a)) : piFinset (fun a => (s a).
image (f a))…
-/
lemma piFinset_inv [∀ i, Inv (α i)] (s : ∀ i, Finset (α i)) :
    piFinset (fun i ↦ (s i)⁻¹) = (piFinset s)⁻¹ := piFinset_image _ _

end Fintype

open scoped Pointwise

namespace Set

section One

-- Redeclaring an instance for better keys
@[to_additive]
/-
**Set.instFintypeOne** 是 Mathlib 中的一个实例，位于命名空间 `Set`。
形式化陈述：instFintypeOne [One α] : Fintype (1 : Set α)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instFintypeOne [One α] : Fintype (1 : Set α) := Set.fintypeSingleton _

variable [One α]

@[to_additive (attr := simp)]
/-
**Set.toFinset_one** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：toFinset_one : (1 : Set α).toFinset = 1
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem toFinset_one : (1 : Set α).toFinset = 1 :=
  rfl

-- should take simp priority over `Finite.toFinset_singleton`
@[to_additive (attr := simp high)]
/-
**Set.Finite.toFinset_one** 是 Mathlib 中的一个定理，位于命名空间 `Set.Finite`。
形式化陈述：∀ {α : Type u_2} [inst : One α] (h : optParam (Set.Finite 1) ⋯), h.toFinse
t = 1
参数：h : optParam (Set.Finite 1) ⋯。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.Finite.toFinset_singleton`：∀ {α : Type u} {a : α} (ha : optParam {a}
.Finite ⋯), ha.toFinset = {a}
-/
theorem Finite.toFinset_one (h : (1 : Set α).Finite := finite_one) : h.toFinset = 1 :=
  Finite.toFinset_singleton _

end One

section Mul

variable [DecidableEq α] [Mul α] {s t : Set α}

@[to_additive (attr := simp)]
/-
**Set.toFinset_mul** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：toFinset_mul (s t : Set α) [Fintype s] [Fintype t] [Fintype ↑(s * t)] : (s
 * t).toFinset = s.toFinset * t.toFinset
参数：s t : Set α；s * t。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.toFinset_image2`：toFinset_image2 (f : α -> β -> γ) (s : Set α) (t : 
Set β) [Fintype s] [Fintype t] [Fintype (image2 f s t)] : (image2 f s t).toFinse
t = Finse…
-/
theorem toFinset_mul (s t : Set α) [Fintype s] [Fintype t] [Fintype ↑(s * t)] :
    (s * t).toFinset = s.toFinset * t.toFinset :=
  toFinset_image2 _ _ _

@[to_additive]
/-
**Set.Finite.toFinset_mul** 是 Mathlib 中的一个定理，位于命名空间 `Set.Finite`。
形式化陈述：∀ {α : Type u_2} [inst : DecidableEq α] [inst_1 : Mul α] {s t : Set α} (hs
 : s.Finite) (ht : t.Finite)   (hf : optParam (s * t).Finite ⋯), hf.toFinset = h
s.toFinset * ht.toFinset
参数：hs : s.Finite；ht : t.Finite；hf : optParam (s * t).Finite ⋯。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.Finite.toFinset_image2`：∀ {α : Type u_1} {β : Type u_3} {γ : Type u_
5} [inst : DecidableEq γ] {s : Set α} {t : Set β} (f : α → β → γ)   (hs : s.Fini
te) (ht : t.Fini…
· 使用定理 `Set.Finite.image2`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {s : S
et α} {t : Set β} (f : α → β → γ),   s.Finite → t.Finite → (Set.image2 f s t).Fi
nite
-/
theorem Finite.toFinset_mul (hs : s.Finite) (ht : t.Finite) (hf := hs.mul ht) :
    hf.toFinset = hs.toFinset * ht.toFinset :=
  Finite.toFinset_image2 _ _ _

end Mul

end Set

