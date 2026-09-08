/-
Copyright (c) 2018 Mitchell Rowett. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mitchell Rowett, Kim Morrison
-/
module

public import Mathlib.Algebra.Group.Action.Pointwise.Set.Basic
public import Mathlib.Algebra.Group.Subgroup.Basic
public import Mathlib.Data.Setoid.Basic
public import Mathlib.GroupTheory.Coset.Defs

/-!
# Cosets

This file develops the basic theory of left and right cosets.

When `G` is a group and `a : G`, `s : Set G`, with  `open scoped Pointwise` we can write:
* the left coset of `s` by `a` as `a • s`
* the right coset of `s` by `a` as `MulOpposite.op a • s` (or `op a • s` with `open MulOpposite`,
  or `s <• a` with `open scoped Pointwise RightActions`)

If instead `G` is an additive group, we can write (with  `open scoped Pointwise` still)
* the left coset of `s` by `a` as `a +ᵥ s`
* the right coset of `s` by `a` as `AddOpposite.op a +ᵥ s` (or `op a +ᵥ s` with `open AddOpposite`,
  or `s <+ᵥ a` with `open scoped Pointwise RightActions`)

## Main definitions

* `Subgroup.leftCosetEquivSubgroup`: the natural bijection between a left coset and the subgroup,
  for an `AddGroup` this is `AddSubgroup.leftCosetEquivAddSubgroup`.

## Notation

* `G ⧸ H` is the quotient of the (additive) group `G` by the (additive) subgroup `H`

## TODO

Properly merge with pointwise actions on sets, by renaming and deduplicating lemmas as appropriate.
-/

@[expose] public section

assert_not_exists Cardinal Multiset

open Function MulOpposite Set
open scoped Pointwise

variable {α : Type*}

section CosetMul

variable [Mul α]

@[to_additive mem_leftAddCoset]
/-
**mem_leftCoset** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：mem_leftCoset {s : Set α} {x : α} (a : α) (hxS : x in s) : a * x in a • s
参数：a : α；hxS : x in s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.mem_image_of_mem`：mem_image_of_mem (f : α -> β) {x : α} {a : Set α} 
(h : x in a) : f x in f '' a
-/
theorem mem_leftCoset {s : Set α} {x : α} (a : α) (hxS : x ∈ s) : a * x ∈ a • s :=
  mem_image_of_mem (fun b : α => a * b) hxS

@[to_additive mem_rightAddCoset]
/-
**mem_rightCoset** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：mem_rightCoset {s : Set α} {x : α} (a : α) (hxS : x in s) : x * a in op a 
• s
参数：a : α；hxS : x in s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.mem_image_of_mem`：mem_image_of_mem (f : α -> β) {x : α} {a : Set α} 
(h : x in a) : f x in f '' a
-/
theorem mem_rightCoset {s : Set α} {x : α} (a : α) (hxS : x ∈ s) : x * a ∈ op a • s :=
  mem_image_of_mem (fun b : α => b * a) hxS

/-- Equality of two left cosets `a * s` and `b * s`. -/
@[to_additive LeftAddCosetEquivalence /-- Equality of two left cosets `a + s` and `b + s`. -/]
/-
**LeftCosetEquivalence** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：LeftCosetEquivalence (s : Set α) (a b : α)
参数：s : Set α；a b : α。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Equality of two left cosets `a * s` and `b * s`.
-/
def LeftCosetEquivalence (s : Set α) (a b : α) :=
  a • s = b • s

@[to_additive leftAddCosetEquivalence_rel]
/-
**leftCosetEquivalence_rel** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：leftCosetEquivalence_rel (s : Set α) : Equivalence (LeftCosetEquivalence s
)
参数：s : Set α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
-/
theorem leftCosetEquivalence_rel (s : Set α) : Equivalence (LeftCosetEquivalence s) :=
  @Equivalence.mk _ (LeftCosetEquivalence s) (fun _ => rfl) Eq.symm Eq.trans

/-- Equality of two right cosets `s * a` and `s * b`. -/
@[to_additive RightAddCosetEquivalence /-- Equality of two right cosets `s + a` and `s + b`. -/]
/-
**RightCosetEquivalence** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：RightCosetEquivalence (s : Set α) (a b : α)
参数：s : Set α；a b : α。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Equality of two right cosets `s * a` and `s * b`.
-/
def RightCosetEquivalence (s : Set α) (a b : α) :=
  op a • s = op b • s

@[to_additive rightAddCosetEquivalence_rel]
/-
**rightCosetEquivalence_rel** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：rightCosetEquivalence_rel (s : Set α) : Equivalence (RightCosetEquivalence
 s)
参数：s : Set α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
-/
theorem rightCosetEquivalence_rel (s : Set α) : Equivalence (RightCosetEquivalence s) :=
  @Equivalence.mk _ (RightCosetEquivalence s) (fun _a => rfl) Eq.symm Eq.trans

end CosetMul

section CosetSemigroup

variable [Semigroup α]

@[to_additive leftAddCoset_assoc]
/-
**leftCoset_assoc** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：leftCoset_assoc (s : Set α) (a b : α) : a • (b • s) = (a * b) • s
参数：s : Set α；a b : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.image_congr`：image_congr {f g : α -> β} {s : Set α} (h : forall a in
 s, f a = g a) : f '' s = g '' s
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.image_comp`：image_comp (f : β -> γ) (g : α -> β) (a : Set α) : f ∘ g
 '' a = f '' g '' a
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem leftCoset_assoc (s : Set α) (a b : α) : a • (b • s) = (a * b) • s := by
  simp [← image_smul, (image_comp _ _ _).symm, Function.comp, mul_assoc]

@[to_additive rightAddCoset_assoc]
/-
**rightCoset_assoc** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：rightCoset_assoc (s : Set α) (a b : α) : op b • op a • s = op (a * b) • s
参数：s : Set α；a b : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.image_congr`：image_congr {f g : α -> β} {s : Set α} (h : forall a in
 s, f a = g a) : f '' s = g '' s
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.image_comp`：image_comp (f : β -> γ) (g : α -> β) (a : Set α) : f ∘ g
 '' a = f '' g '' a
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem rightCoset_assoc (s : Set α) (a b : α) : op b • op a • s = op (a * b) • s := by
  simp [← image_smul, (image_comp _ _ _).symm, Function.comp, mul_assoc]

@[to_additive leftAddCoset_rightAddCoset]
/-
**leftCoset_rightCoset** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：leftCoset_rightCoset (s : Set α) (a b : α) : op b • a • s = a • (op b • s)
参数：s : Set α；a b : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.image_congr`：image_congr {f g : α -> β} {s : Set α} (h : forall a in
 s, f a = g a) : f '' s = g '' s
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.image_comp`：image_comp (f : β -> γ) (g : α -> β) (a : Set α) : f ∘ g
 '' a = f '' g '' a
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem leftCoset_rightCoset (s : Set α) (a b : α) : op b • a • s = a • (op b • s) := by
  simp [← image_smul, (image_comp _ _ _).symm, Function.comp, mul_assoc]

end CosetSemigroup

section CosetMonoid

variable [Monoid α] (s : Set α)

@[to_additive zero_leftAddCoset]
/-
**one_leftCoset** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：one_leftCoset : (1 : α) • s = s
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
theorem one_leftCoset : (1 : α) • s = s :=
  Set.ext <| by simp

@[to_additive rightAddCoset_zero]
/-
**rightCoset_one** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：rightCoset_one : op (1 : α) • s = s
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
theorem rightCoset_one : op (1 : α) • s = s :=
  Set.ext <| by simp

end CosetMonoid

section CosetSubmonoid

open Submonoid

variable [Monoid α] (s : Submonoid α)

@[to_additive mem_own_leftAddCoset]
/-
**mem_own_leftCoset** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：mem_own_leftCoset (a : α) : a in a • (s : Set α)
参数：a : α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `mem_leftCoset`：mem_leftCoset {s : Set α} {x : α} (a : α) (hxS : x in s) 
: a * x in a • s
· 使用定理 `OneMemClass.one_mem`：∀ {S : Type u_3} {M : outParam (Type u_4)} {inst : 
One M} {inst_1 : SetLike S M} [self : OneMemClass S M] (s : S), 1 ∈ s
· 使用定理 `SubmonoidClass.toOneMemClass`：∀ {S : Type u_3} {M : outParam (Type u_4)}
 {inst : MulOneClass M} {inst_1 : SetLike S M} [self : SubmonoidClass S M],   On
eMemClass S M
· 使用定理 `Submonoid.instSubmonoidClass`：∀ {M : Type u_1} [inst : MulOneClass M], S
ubmonoidClass (Submonoid M) M
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
-/
theorem mem_own_leftCoset (a : α) : a ∈ a • (s : Set α) :=
  suffices a * 1 ∈ a • (s : Set α) by simpa
  mem_leftCoset a (one_mem s : 1 ∈ s)

@[to_additive mem_own_rightAddCoset]
/-
**mem_own_rightCoset** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：mem_own_rightCoset (a : α) : a in op a • (s : Set α)
参数：a : α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `mem_rightCoset`：mem_rightCoset {s : Set α} {x : α} (a : α) (hxS : x in s
) : x * a in op a • s
· 使用定理 `OneMemClass.one_mem`：∀ {S : Type u_3} {M : outParam (Type u_4)} {inst : 
One M} {inst_1 : SetLike S M} [self : OneMemClass S M] (s : S), 1 ∈ s
· 使用定理 `SubmonoidClass.toOneMemClass`：∀ {S : Type u_3} {M : outParam (Type u_4)}
 {inst : MulOneClass M} {inst_1 : SetLike S M} [self : SubmonoidClass S M],   On
eMemClass S M
· 使用定理 `Submonoid.instSubmonoidClass`：∀ {M : Type u_1} [inst : MulOneClass M], S
ubmonoidClass (Submonoid M) M
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
-/
theorem mem_own_rightCoset (a : α) : a ∈ op a • (s : Set α) :=
  suffices 1 * a ∈ op a • (s : Set α) by simpa
  mem_rightCoset a (one_mem s : 1 ∈ s)

@[to_additive mem_leftAddCoset_leftAddCoset]
/-
**mem_leftCoset_leftCoset** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：mem_leftCoset_leftCoset {a : α} (ha : a • (s : Set α) = s) : a in s
参数：ha : a • (s : Set α) = s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `SetLike.mem_coe`：mem_coe {x : B} : x in (p : Set B) ↔ x in p
· 使用定理 `mem_own_leftCoset`：mem_own_leftCoset (a : α) : a in a • (s : Set α)
-/
theorem mem_leftCoset_leftCoset {a : α} (ha : a • (s : Set α) = s) : a ∈ s := by
  rw [← SetLike.mem_coe, ← ha]; exact mem_own_leftCoset s a

@[to_additive mem_rightAddCoset_rightAddCoset]
/-
**mem_rightCoset_rightCoset** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：mem_rightCoset_rightCoset {a : α} (ha : op a • (s : Set α) = s) : a in s
参数：ha : op a • (s : Set α) = s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `SetLike.mem_coe`：mem_coe {x : B} : x in (p : Set B) ↔ x in p
· 使用定理 `mem_own_rightCoset`：mem_own_rightCoset (a : α) : a in op a • (s : Set α)
-/
theorem mem_rightCoset_rightCoset {a : α} (ha : op a • (s : Set α) = s) : a ∈ s := by
  rw [← SetLike.mem_coe, ← ha]; exact mem_own_rightCoset s a

end CosetSubmonoid

section CosetGroup

variable [Group α] {s : Set α} {x : α}

@[to_additive mem_leftAddCoset_iff]
/-
**mem_leftCoset_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：mem_leftCoset_iff (a : α) : x in a • s ↔ a⁻¹ * x in s
参数：a : α。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `inv_mul_cancel_left`：inv_mul_cancel_left (a b : G) : a⁻¹ * (a * b) = b
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `mul_inv_cancel_left`：mul_inv_cancel_left (a b : G) : a * (a⁻¹ * b) = b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem mem_leftCoset_iff (a : α) : x ∈ a • s ↔ a⁻¹ * x ∈ s :=
  Iff.intro (fun ⟨b, hb, h⟩ => by simp [h.symm, hb]) fun h => ⟨a⁻¹ * x, h, by simp⟩

@[to_additive mem_rightAddCoset_iff]
/-
**mem_rightCoset_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：mem_rightCoset_iff (a : α) : x in op a • s ↔ x * a⁻¹ in s
参数：a : α。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `mul_inv_cancel_right`：mul_inv_cancel_right (a b : G) : a * b * b⁻¹ = a
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `inv_mul_cancel_right`：inv_mul_cancel_right (a b : G) : a * b⁻¹ * b = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem mem_rightCoset_iff (a : α) : x ∈ op a • s ↔ x * a⁻¹ ∈ s :=
  Iff.intro (fun ⟨b, hb, h⟩ => by simp [h.symm, hb]) fun h => ⟨x * a⁻¹, h, by simp⟩

end CosetGroup

section CosetSubgroup

open Subgroup

variable [Group α] (s : Subgroup α)

@[to_additive leftAddCoset_mem_leftAddCoset]
/-
**leftCoset_mem_leftCoset** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：leftCoset_mem_leftCoset {a : α} (ha : a in s) : a • (s : Set α) = s
参数：ha : a in s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mul_mem_cancel_left`：mul_mem_cancel_left {x y : G} (h : x in H) : x * y 
in H ↔ y in H
· 使用定理 `Subgroup.instSubgroupClass`：∀ {G : Type u_1} [inst : Group G], SubgroupC
lass (Subgroup G) G
· 使用定理 `Subgroup.inv_mem`：∀ {G : Type u_1} [inst : Group G] (H : Subgroup G) {x 
: G}, x ∈ H → x⁻¹ ∈ H
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
theorem leftCoset_mem_leftCoset {a : α} (ha : a ∈ s) : a • (s : Set α) = s :=
  Set.ext <| by simp [mem_leftCoset_iff, mul_mem_cancel_left (s.inv_mem ha)]

@[to_additive rightAddCoset_mem_rightAddCoset]
/-
**rightCoset_mem_rightCoset** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：rightCoset_mem_rightCoset {a : α} (ha : a in s) : op a • (s : Set α) = s
参数：ha : a in s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mul_mem_cancel_right`：mul_mem_cancel_right {x y : G} (h : x in H) : y * 
x in H ↔ y in H
· 使用定理 `Subgroup.instSubgroupClass`：∀ {G : Type u_1} [inst : Group G], SubgroupC
lass (Subgroup G) G
· 使用定理 `Subgroup.inv_mem`：∀ {G : Type u_1} [inst : Group G] (H : Subgroup G) {x 
: G}, x ∈ H → x⁻¹ ∈ H
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem rightCoset_mem_rightCoset {a : α} (ha : a ∈ s) : op a • (s : Set α) = s :=
  Set.ext fun b => by simp [mem_rightCoset_iff, mul_mem_cancel_right (s.inv_mem ha)]

@[to_additive]
/-
**orbit_subgroup_eq_rightCoset** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：orbit_subgroup_eq_rightCoset (a : α) : MulAction.orbit s a = op a • s
参数：a : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
-/
theorem orbit_subgroup_eq_rightCoset (a : α) : MulAction.orbit s a = op a • s :=
  Set.ext fun _b => ⟨fun ⟨c, d⟩ => ⟨c, c.2, d⟩, fun ⟨c, d, e⟩ => ⟨⟨c, d⟩, e⟩⟩

@[to_additive]
/-
**orbit_subgroup_eq_self_of_mem** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：orbit_subgroup_eq_self_of_mem {a : α} (ha : a in s) : MulAction.orbit s a 
= s
参数：ha : a in s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `orbit_subgroup_eq_rightCoset`：orbit_subgroup_eq_rightCoset (a : α) : Mul
Action.orbit s a = op a • s
· 使用定理 `rightCoset_mem_rightCoset`：rightCoset_mem_rightCoset {a : α} (ha : a in 
s) : op a • (s : Set α) = s
-/
theorem orbit_subgroup_eq_self_of_mem {a : α} (ha : a ∈ s) : MulAction.orbit s a = s :=
  (orbit_subgroup_eq_rightCoset s a).trans (rightCoset_mem_rightCoset s ha)

@[to_additive]
/-
**orbit_subgroup_one_eq_self** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：orbit_subgroup_one_eq_self : MulAction.orbit s (1 : α) = s
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `orbit_subgroup_eq_self_of_mem`：orbit_subgroup_eq_self_of_mem {a : α} (ha
 : a in s) : MulAction.orbit s a = s
· 使用定理 `Subgroup.one_mem`：∀ {G : Type u_1} [inst : Group G] (H : Subgroup G), 1 
∈ H
-/
theorem orbit_subgroup_one_eq_self : MulAction.orbit s (1 : α) = s :=
  orbit_subgroup_eq_self_of_mem s s.one_mem

@[to_additive eq_addCosets_of_normal]
/-
**eq_cosets_of_normal** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：eq_cosets_of_normal (N : s.Normal) (g : α) : g • (s : Set α) = op g • s
参数：N : s.Normal；g : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Subgroup.Normal.mem_comm_iff`：mem_comm_iff (nH : H.Normal) {a b : G} : a
 * b in H ↔ b * a in H
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem eq_cosets_of_normal (N : s.Normal) (g : α) : g • (s : Set α) = op g • s :=
  Set.ext fun a => by simp [mem_leftCoset_iff, mem_rightCoset_iff, N.mem_comm_iff]

@[to_additive normal_of_eq_addCosets]
/-
**normal_of_eq_cosets** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：normal_of_eq_cosets (h : forall g : α, g • (s : Set α) = op g • s) : s.Nor
mal
参数：h : forall g : α, g • (s : Set α) = op g • s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `mem_rightCoset_iff`：mem_rightCoset_iff (a : α) : x in op a • s ↔ x * a⁻¹
 in s
· 使用定理 `mem_leftCoset`：mem_leftCoset {s : Set α} {x : α} (a : α) (hxS : x in s) 
: a * x in a • s
-/
theorem normal_of_eq_cosets (h : ∀ g : α, g • (s : Set α) = op g • s) : s.Normal :=
  ⟨fun a ha g =>
    show g * a * g⁻¹ ∈ (s : Set α) by rw [← mem_rightCoset_iff, ← h]; exact mem_leftCoset g ha⟩

@[to_additive normal_iff_eq_addCosets]
/-
**normal_iff_eq_cosets** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：normal_iff_eq_cosets : s.Normal ↔ forall g : α, g • (s : Set α) = op g • s
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_cosets_of_normal`：eq_cosets_of_normal (N : s.Normal) (g : α) : g • (s
 : Set α) = op g • s
· 使用定理 `normal_of_eq_cosets`：normal_of_eq_cosets (h : forall g : α, g • (s : Set
 α) = op g • s) : s.Normal
-/
theorem normal_iff_eq_cosets : s.Normal ↔ ∀ g : α, g • (s : Set α) = op g • s :=
  ⟨@eq_cosets_of_normal _ _ s, normal_of_eq_cosets s⟩

@[to_additive leftAddCoset_eq_iff]
/-
**leftCoset_eq_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：leftCoset_eq_iff {x y : α} : x • (s : Set α) = y • s ↔ x⁻¹ * y in s
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.ext_iff`：∀ {α : Type u} {a b : Set α}, a = b ↔ ∀ (x : α), x ∈ a ↔ x 
∈ b
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `inv_mul_cancel`：inv_mul_cancel (a : G) : a⁻¹ * a = 1
· 使用定理 `Subgroup.one_mem`：∀ {G : Type u_1} [inst : Group G] (H : Subgroup G), 1 
∈ H
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `mul_inv_cancel_right`：mul_inv_cancel_right (a b : G) : a * b * b⁻¹ = a
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `Subgroup.mul_mem_cancel_left`：∀ {G : Type u_1} [inst : Group G] (H : Sub
group G) {x y : G}, x ∈ H → (x * y ∈ H ↔ y ∈ H)
-/
theorem leftCoset_eq_iff {x y : α} : x • (s : Set α) = y • s ↔ x⁻¹ * y ∈ s := by
  rw [Set.ext_iff]
  simp_rw [mem_leftCoset_iff, SetLike.mem_coe]
  constructor
  · intro h
    apply (h y).mpr
    rw [inv_mul_cancel]
    exact s.one_mem
  · intro h z
    rw [← mul_inv_cancel_right x⁻¹ y]
    rw [mul_assoc]
    exact s.mul_mem_cancel_left h

@[to_additive rightAddCoset_eq_iff]
/-
**rightCoset_eq_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：rightCoset_eq_iff {x y : α} : op x • (s : Set α) = op y • s ↔ y * x⁻¹ in s
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.ext_iff`：∀ {α : Type u} {a b : Set α}, a = b ↔ ∀ (x : α), x ∈ a ↔ x 
∈ b
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `mul_inv_cancel`：mul_inv_cancel (a : G) : a * a⁻¹ = 1
· 使用定理 `Subgroup.one_mem`：∀ {G : Type u_1} [inst : Group G] (H : Subgroup G), 1 
∈ H
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `inv_mul_cancel_left`：inv_mul_cancel_left (a b : G) : a⁻¹ * (a * b) = b
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `Subgroup.mul_mem_cancel_right`：∀ {G : Type u_1} [inst : Group G] (H : Su
bgroup G) {x y : G}, x ∈ H → (y * x ∈ H ↔ y ∈ H)
-/
theorem rightCoset_eq_iff {x y : α} : op x • (s : Set α) = op y • s ↔ y * x⁻¹ ∈ s := by
  rw [Set.ext_iff]
  simp_rw [mem_rightCoset_iff, SetLike.mem_coe]
  constructor
  · intro h
    apply (h y).mpr
    rw [mul_inv_cancel]
    exact s.one_mem
  · intro h z
    rw [← inv_mul_cancel_left y x⁻¹]
    rw [← mul_assoc]
    exact s.mul_mem_cancel_right h

end CosetSubgroup

namespace QuotientGroup

variable [Group α] (s : Subgroup α)

/-
**QuotientGroup.leftRel_r_eq_leftCosetEquivalence** 是 Mathlib 中的一个定理，位于命名空间 `Quo
tientGroup`。
形式化陈述：leftRel_r_eq_leftCosetEquivalence : ⇑(QuotientGroup.leftRel s) = LeftCoset
Equivalence s
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `QuotientGroup.leftRel_eq`：leftRel_eq : ⇑(leftRel s) = fun x y => x⁻¹ * y
 in s
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用定理 `leftCoset_eq_iff`：leftCoset_eq_iff {x y : α} : x • (s : Set α) = y • s ↔
 x⁻¹ * y in s
-/
theorem leftRel_r_eq_leftCosetEquivalence :
    ⇑(QuotientGroup.leftRel s) = LeftCosetEquivalence s := by
  ext
  rw [leftRel_eq]
  exact (leftCoset_eq_iff s).symm

@[to_additive leftRel_prod]
/-
**QuotientGroup.leftRel_prod** 是 Mathlib 中的一个引理，位于命名空间 `QuotientGroup`。
形式化陈述：leftRel_prod {β : Type*} [Group β] (s' : Subgroup β) : leftRel (s.prod s')
 = (leftRel s).prod (leftRel s')
参数：s' : Subgroup β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Setoid.ext`：ext {α : Sort*} : forall {s t : Setoid α}, (forall a b, s a 
b ↔ t a b) -> s = t | ⟨r, _⟩, ⟨p, _⟩, Eq => by have : r = p
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Setoid.prod_apply`：prod_apply {r : Setoid α} {s : Setoid β} {x₁ x₂ : α} 
{y₁ y₂ : β} : @Setoid.r _ (r.prod s) (x₁, y₁) (x₂, y₂) ↔ (@Setoid.r _ r x₁ x₂ ∧ 
@Setoid…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma leftRel_prod {β : Type*} [Group β] (s' : Subgroup β) :
    leftRel (s.prod s') = (leftRel s).prod (leftRel s') := by
  refine Setoid.ext fun x y ↦ ?_
  rw [Setoid.prod_apply]
  simp_rw [leftRel_apply]
  rfl

@[to_additive]
/-
**QuotientGroup.leftRel_pi** 是 Mathlib 中的一个引理，位于命名空间 `QuotientGroup`。
形式化陈述：leftRel_pi {ι : Type*} {β : ι -> Type*} [forall i, Group (β i)] (s' : fora
ll i, Subgroup (β i)) : leftRel (Subgroup.pi Set.univ s') = @piSetoid _ _ fun i 
=> leftRel (s' i)
参数：β i；s' : forall i, Subgroup (β i)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Setoid.ext`：ext {α : Sort*} : forall {s t : Setoid α}, (forall a b, s a 
b ↔ t a b) -> s = t | ⟨r, _⟩, ⟨p, _⟩, Eq => by have : r = p
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
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma leftRel_pi {ι : Type*} {β : ι → Type*} [∀ i, Group (β i)] (s' : ∀ i, Subgroup (β i)) :
    leftRel (Subgroup.pi Set.univ s') = @piSetoid _ _ fun i ↦ leftRel (s' i) := by
  refine Setoid.ext fun x y ↦ ?_
  simp [Setoid.piSetoid_apply, leftRel_apply, Subgroup.mem_pi]
/-
**QuotientGroup.rightRel_r_eq_rightCosetEquivalence** 是 Mathlib 中的一个定理，位于命名空间 `Q
uotientGroup`。
形式化陈述：rightRel_r_eq_rightCosetEquivalence : ⇑(QuotientGroup.rightRel s) = RightC
osetEquivalence s
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `QuotientGroup.rightRel_eq`：rightRel_eq : ⇑(rightRel s) = fun x y => y * 
x⁻¹ in s
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用定理 `rightCoset_eq_iff`：rightCoset_eq_iff {x y : α} : op x • (s : Set α) = op
 y • s ↔ y * x⁻¹ in s
-/
theorem rightRel_r_eq_rightCosetEquivalence :
    ⇑(QuotientGroup.rightRel s) = RightCosetEquivalence s := by
  ext
  rw [rightRel_eq]
  exact (rightCoset_eq_iff s).symm

@[to_additive rightRel_prod]
/-
**QuotientGroup.rightRel_prod** 是 Mathlib 中的一个引理，位于命名空间 `QuotientGroup`。
形式化陈述：rightRel_prod {β : Type*} [Group β] (s' : Subgroup β) : rightRel (s.prod s
') = (rightRel s).prod (rightRel s')
参数：s' : Subgroup β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Setoid.ext`：ext {α : Sort*} : forall {s t : Setoid α}, (forall a b, s a 
b ↔ t a b) -> s = t | ⟨r, _⟩, ⟨p, _⟩, Eq => by have : r = p
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Setoid.prod_apply`：prod_apply {r : Setoid α} {s : Setoid β} {x₁ x₂ : α} 
{y₁ y₂ : β} : @Setoid.r _ (r.prod s) (x₁, y₁) (x₂, y₂) ↔ (@Setoid.r _ r x₁ x₂ ∧ 
@Setoid…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma rightRel_prod {β : Type*} [Group β] (s' : Subgroup β) :
    rightRel (s.prod s') = (rightRel s).prod (rightRel s') := by
  refine Setoid.ext fun x y ↦ ?_
  rw [Setoid.prod_apply]
  simp_rw [rightRel_apply]
  rfl

@[to_additive]
/-
**QuotientGroup.rightRel_pi** 是 Mathlib 中的一个引理，位于命名空间 `QuotientGroup`。
形式化陈述：rightRel_pi {ι : Type*} {β : ι -> Type*} [forall i, Group (β i)] (s' : for
all i, Subgroup (β i)) : rightRel (Subgroup.pi Set.univ s') = @piSetoid _ _ fun 
i => rightRel (s' i)
参数：β i；s' : forall i, Subgroup (β i)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Setoid.ext`：ext {α : Sort*} : forall {s t : Setoid α}, (forall a b, s a 
b ↔ t a b) -> s = t | ⟨r, _⟩, ⟨p, _⟩, Eq => by have : r = p
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
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma rightRel_pi {ι : Type*} {β : ι → Type*} [∀ i, Group (β i)] (s' : ∀ i, Subgroup (β i)) :
    rightRel (Subgroup.pi Set.univ s') = @piSetoid _ _ fun i ↦ rightRel (s' i) := by
  refine Setoid.ext fun x y ↦ ?_
  simp [Setoid.piSetoid_apply, rightRel_apply, Subgroup.mem_pi]

end QuotientGroup

namespace QuotientGroup

variable [Group α] {s : Subgroup α}

variable (s)

/-- Given a subgroup `s`, the function that sends a subgroup `t` to the pair consisting of
its intersection with `s` and its image in the quotient `α ⧸ s` is strictly monotone, even though
it is not injective in general. -/
@[to_additive QuotientAddGroup.strictMono_comap_prod_image /-- Given an additive subgroup `s`,
the function that sends an additive subgroup `t` to the pair consisting of
its intersection with `s` and its image in the quotient `α ⧸ s`
is strictly monotone, even though it is not injective in general. -/]
/-
**QuotientGroup.strictMono_comap_prod_image** 是 Mathlib 中的一个定理，位于命名空间 `QuotientG
roup`。
形式化陈述：strictMono_comap_prod_image : StrictMono fun t : Subgroup α => (t.comap s.
subtype, mk (s
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subgroup.comap_mono`：comap_mono {f : G ->* N} {K K' : Subgroup N} : K <=
 K' -> comap f K <= comap f K'
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用引理 `Set.image_mono`：image_mono (h : s subseteq t) : f '' s subseteq f '' t
· 使用定理 `mt`：∀ {a b : Prop}, (a → b) → ¬b → ¬a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `QuotientGroup.eq`：∀ {α : Type u_1} [inst : Group α] {s : Subgroup α} {a 
b : α}, ↑a = ↑b ↔ a⁻¹ * b ∈ s
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mul_inv_cancel_left`：mul_inv_cancel_left (a b : G) : a * (a⁻¹ * b) = b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Subgroup.mul_mem`：∀ {G : Type u_1} [inst : Group G] (H : Subgroup G) {x 
y : G}, x ∈ H → y ∈ H → x * y ∈ H
· 使用定理 `Subgroup.inv_mem`：∀ {G : Type u_1} [inst : Group G] (H : Subgroup G) {x 
: G}, x ∈ H → x⁻¹ ∈ H
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
theorem strictMono_comap_prod_image :
    StrictMono fun t : Subgroup α ↦ (t.comap s.subtype, mk (s := s) '' t) := by
  refine fun t₁ t₂ h ↦ ⟨⟨Subgroup.comap_mono h.1, Set.image_mono h.1⟩,
    mt (fun ⟨le1, le2⟩ a ha ↦ ?_) h.2⟩
  obtain ⟨a', h', eq⟩ := le2 ⟨_, ha, rfl⟩
  convert t₁.mul_mem h' (@le1 ⟨_, QuotientGroup.eq.1 eq⟩ <| t₂.mul_mem (t₂.inv_mem <| h.1 h') ha)
  simp

variable {s} {a b : α}

@[to_additive]
/-
**QuotientGroup.eq_class_eq_leftCoset** 是 Mathlib 中的一个定理，位于命名空间 `QuotientGroup`。
形式化陈述：eq_class_eq_leftCoset (s : Subgroup α) (g : α) : { x : α | (x : α ⧸ s) = g
 } = g • s
参数：s : Subgroup α；g : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mem_leftCoset_iff`：mem_leftCoset_iff (a : α) : x in a • s ↔ a⁻¹ * x in s
· 使用定理 `Set.mem_ofPred_eq`：mem_ofPred_eq {x : α} {p : α -> Prop} : (x in {y | p 
y}) = p x
· 使用定理 `eq_comm`：∀ {α : Sort u_1} {a b : α}, a = b ↔ b = a
· 使用定理 `QuotientGroup.eq`：∀ {α : Type u_1} [inst : Group α] {s : Subgroup α} {a 
b : α}, ↑a = ↑b ↔ a⁻¹ * b ∈ s
· 使用定理 `SetLike.mem_coe`：mem_coe {x : B} : x in (p : Set B) ↔ x in p
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem eq_class_eq_leftCoset (s : Subgroup α) (g : α) :
    { x : α | (x : α ⧸ s) = g } = g • s :=
  Set.ext fun z => by
    rw [mem_leftCoset_iff, Set.mem_ofPred_eq, eq_comm, QuotientGroup.eq, SetLike.mem_coe]

open MulAction in
@[to_additive]
/-
**QuotientGroup.orbit_mk_eq_smul** 是 Mathlib 中的一个引理，位于命名空间 `QuotientGroup`。
形式化陈述：orbit_mk_eq_smul (x : α) : MulAction.orbitRel.Quotient.orbit (x : α ⧸ s) =
 x • s
参数：x : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `Quotient.mk''`：mk''_surjective : Function.Surjective (Quotient.mk'' : α 
-> Quotient s₁)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MulAction.orbitRel.Quotient.mem_orbit`：∀ {G : Type u_1} {α : Type u_2} [
inst : Group G] [inst_1 : MulAction G α] {a : α} {x : MulAction.orbitRel.Quotien
t G α},   a ∈ x.orbit ↔ Quo…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Setoid.comm'`：comm' (s : Setoid α) {x y} : s x y ↔ s y x
-/
lemma orbit_mk_eq_smul (x : α) : MulAction.orbitRel.Quotient.orbit (x : α ⧸ s) = x • s := by
  ext
  rw [orbitRel.Quotient.mem_orbit]
  simpa [mem_smul_set_iff_inv_smul_mem, ← leftRel_apply, Quotient.eq''] using Setoid.comm' _

@[to_additive]
/-
**QuotientGroup.orbit_eq_out_smul** 是 Mathlib 中的一个引理，位于命名空间 `QuotientGroup`。
形式化陈述：orbit_eq_out_smul (x : α ⧸ s) : MulAction.orbitRel.Quotient.orbit x = x.ou
t • s
参数：x : α ⧸ s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `QuotientGroup.induction_on`：induction_on {C : α ⧸ s -> Prop} (x : α ⧸ s)
 (H : forall z, C (QuotientGroup.mk z)) : C x
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `QuotientGroup.orbit_mk_eq_smul`：orbit_mk_eq_smul (x : α) : MulAction.orb
itRel.Quotient.orbit (x : α ⧸ s) = x • s
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Quotient.out_eq'`：out_eq' (q : Quotient s₁) : Quotient.mk'' q.out = q
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma orbit_eq_out_smul (x : α ⧸ s) : MulAction.orbitRel.Quotient.orbit x = x.out • s := by
  induction x using QuotientGroup.induction_on
  simp only [orbit_mk_eq_smul, ← eq_class_eq_leftCoset, Quotient.out_eq']

end QuotientGroup

namespace Subgroup

open QuotientGroup

variable [Group α] {s : Subgroup α}

/-- The natural bijection between a left coset `g * s` and `s`. -/
@[to_additive /-- The natural bijection between the cosets `g + s` and `s`. -/]
/-
**Subgroup.leftCosetEquivSubgroup** 是 Mathlib 中的一个定义，位于命名空间 `Subgroup`。
形式化陈述：leftCosetEquivSubgroup (g : α) : (g • s : Set α) ≃ s
参数：g : α。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The natural bijection between a left coset `g * s` and `s`.
-/
def leftCosetEquivSubgroup (g : α) : (g • s : Set α) ≃ s :=
  ⟨fun x => ⟨g⁻¹ * x.1, (mem_leftCoset_iff _).1 x.2⟩, fun x => ⟨g * x.1, x.1, x.2, rfl⟩,
    fun ⟨x, _⟩ => Subtype.ext <| by simp, fun ⟨g, _⟩ => Subtype.ext <| by simp⟩

/-- The natural bijection between a right coset `s * g` and `s`. -/
@[to_additive /-- The natural bijection between the cosets `s + g` and `s`. -/]
/-
**Subgroup.rightCosetEquivSubgroup** 是 Mathlib 中的一个定义，位于命名空间 `Subgroup`。
形式化陈述：rightCosetEquivSubgroup (g : α) : (op g • s : Set α) ≃ s
参数：g : α。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The natural bijection between a right coset `s * g` and `s`.
-/
def rightCosetEquivSubgroup (g : α) : (op g • s : Set α) ≃ s :=
  ⟨fun x => ⟨x.1 * g⁻¹, (mem_rightCoset_iff _).1 x.2⟩, fun x => ⟨x.1 * g, x.1, x.2, rfl⟩,
    fun ⟨x, _⟩ => Subtype.ext <| by simp, fun ⟨g, _⟩ => Subtype.ext <| by simp⟩

/-- A (non-canonical) bijection between a group `α` and the product `(α/s) × s` -/
@[to_additive addGroupEquivQuotientProdAddSubgroup
  /-- A (non-canonical) bijection between an `AddGroup` `α` and the product `(α/s) × s` -/]
/-
**Subgroup.groupEquivQuotientProdSubgroup** 是 Mathlib 中的一个定义，位于命名空间 `Subgroup`。
形式化陈述：groupEquivQuotientProdSubgroup : α ≃ (α ⧸ s) × s
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `Quotient.mk''`：mk''_surjective : Function.Surjective (Quotient.mk'' : α 
-> Quotient s₁)
· 使用定理 `Equiv.refl`：Equiv.refl (s : Computation α) : s ~ s
-/
noncomputable def groupEquivQuotientProdSubgroup : α ≃ (α ⧸ s) × s :=
  calc
    α ≃ Σ L : α ⧸ s, { x : α // (x : α ⧸ s) = L } := (Equiv.sigmaFiberEquiv QuotientGroup.mk).symm
    _ ≃ Σ L : α ⧸ s, (Quotient.out L • s : Set α) :=
      Equiv.sigmaCongrRight fun L => by
        rw [← eq_class_eq_leftCoset]
        change
          (_root_.Subtype fun x : α => Quotient.mk'' x = L) ≃
            _root_.Subtype fun x : α => Quotient.mk'' x = Quotient.mk'' _
        simp
        rfl
    _ ≃ Σ _L : α ⧸ s, s := Equiv.sigmaCongrRight fun _ => leftCosetEquivSubgroup _
    _ ≃ (α ⧸ s) × s := Equiv.sigmaEquivProd _ _

variable {t : Subgroup α}

/-- If `H ≤ K`, then `G/H ≃ G/K × K/H` constructively, using the provided right inverse
of the quotient map `G → G/K`. The classical version is `Subgroup.quotientEquivProdOfLE`. -/
@[to_additive (attr := simps) quotientEquivProdOfLE'
  /-- If `H ≤ K`, then `G/H ≃ G/K × K/H` constructively, using the provided right inverse
  of the quotient map `G → G/K`. The classical version is `AddSubgroup.quotientEquivProdOfLE`. -/]
/-
**Subgroup.quotientEquivProdOfLE'** 是 Mathlib 中的一个定义，位于命名空间 `Subgroup`。
形式化陈述：quotientEquivProdOfLE' (h_le : s <= t) (f : α ⧸ t -> α) (hf : Function.Rig
htInverse f QuotientGroup.mk) : α ⧸ s ≃ (α ⧸ t) × t ⧸ s.subgroupOf t where toFun
 a
参数：h_le : s <= t；f : α ⧸ t -> α；hf : Function.RightInverse f QuotientGroup.mk。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Quotient.map'`：map'_mk'' (f : α -> β) (h) (x : α) : (Quotient.mk'' x : Q
uotient s₁).map' f h = (Quotient.mk'' (f x) : Quotient s₂)
· 使用定理 `Quotient.mk''`：mk''_surjective : Function.Surjective (Quotient.mk'' : α 
-> Quotient s₁)
-/
def quotientEquivProdOfLE' (h_le : s ≤ t) (f : α ⧸ t → α)
    (hf : Function.RightInverse f QuotientGroup.mk) : α ⧸ s ≃ (α ⧸ t) × t ⧸ s.subgroupOf t where
  toFun a :=
    ⟨a.map' id fun _ _ h => leftRel_apply.mpr (h_le (leftRel_apply.mp h)),
      a.map' (fun g : α => ⟨(f (Quotient.mk'' g))⁻¹ * g, leftRel_apply.mp (Quotient.exact' (hf g))⟩)
        fun b c h => by
        rw [leftRel_apply]
        change ((f b)⁻¹ * b)⁻¹ * ((f c)⁻¹ * c) ∈ s
        have key : f b = f c :=
          congr_arg f (Quotient.sound' (leftRel_apply.mpr (h_le (leftRel_apply.mp h))))
        rwa [key, mul_inv_rev, inv_inv, mul_assoc, mul_inv_cancel_left, ← leftRel_apply]⟩
  invFun a := by
    refine a.2.map' (fun (b : { x // x ∈ t}) => f a.1 * b) fun b c h => by
      rw [leftRel_apply] at h ⊢
      rwa [mul_inv_rev, mul_assoc, inv_mul_cancel_left]
  left_inv := by
    refine Quotient.ind' fun a => ?_
    simp_rw [Quotient.map'_mk'', id, mul_inv_cancel_left]
  right_inv := by
    refine Prod.rec ?_
    refine Quotient.ind' fun a => ?_
    refine Quotient.ind' fun b => ?_
    have key : Quotient.mk'' (f (Quotient.mk'' a) * b) = Quotient.mk'' a :=
      (QuotientGroup.mk_mul_of_mem (f a) b.2).trans (hf a)
    simp_rw [Quotient.map'_mk'', id, key, inv_mul_cancel_left]

/-- If `H ≤ K`, then `G/H ≃ G/K × K/H` nonconstructively.
The constructive version is `quotientEquivProdOfLE'`. -/
@[to_additive (attr := simps!) quotientEquivProdOfLE
  /-- If `H ≤ K`, then `G/H ≃ G/K × K/H` nonconstructively. The
constructive version is `quotientEquivProdOfLE'`. -/]
/-
**Subgroup.quotientEquivProdOfLE** 是 Mathlib 中的一个定义，位于命名空间 `Subgroup`。
形式化陈述：quotientEquivProdOfLE (h_le : s <= t) : α ⧸ s ≃ (α ⧸ t) × t ⧸ s.subgroupOf
 t
参数：h_le : s <= t。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
noncomputable def quotientEquivProdOfLE (h_le : s ≤ t) : α ⧸ s ≃ (α ⧸ t) × t ⧸ s.subgroupOf t :=
  quotientEquivProdOfLE' h_le Quotient.out Quotient.out_eq'

/-- If `s ≤ t`, then there is an embedding `s ⧸ H.subgroupOf s ↪ t ⧸ H.subgroupOf t`. -/
@[to_additive
/-- If `s ≤ t`, there is an embedding `s ⧸ H.addSubgroupOf s ↪ t ⧸ H.addSubgroupOf t`. -/]
/-
**Subgroup.quotientSubgroupOfEmbeddingOfLE** 是 Mathlib 中的一个定义，位于命名空间 `Subgroup`。
形式化陈述：quotientSubgroupOfEmbeddingOfLE (H : Subgroup α) (h : s <= t) : s ⧸ H.subg
roupOf s ↪ t ⧸ H.subgroupOf t where toFun
参数：H : Subgroup α；h : s <= t。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Quotient.map'`：map'_mk'' (f : α -> β) (h) (x : α) : (Quotient.mk'' x : Q
uotient s₁).map' f h = (Quotient.mk'' (f x) : Quotient s₂)
-/
def quotientSubgroupOfEmbeddingOfLE (H : Subgroup α) (h : s ≤ t) :
    s ⧸ H.subgroupOf s ↪ t ⧸ H.subgroupOf t where
  toFun :=
    Quotient.map' (inclusion h) fun a b => by
      simp_rw [leftRel_eq]
      exact id
  inj' :=
    Quotient.ind₂' <| by
      intro a b h
      simpa only [Quotient.map'_mk'', QuotientGroup.eq] using! h

@[to_additive (attr := simp)]
/-
**Subgroup.quotientSubgroupOfEmbeddingOfLE_apply_mk** 是 Mathlib 中的一个定理，位于命名空间 `S
ubgroup`。
形式化陈述：quotientSubgroupOfEmbeddingOfLE_apply_mk (H : Subgroup α) (h : s <= t) (g 
: s) : quotientSubgroupOfEmbeddingOfLE H h (QuotientGroup.mk g) = QuotientGroup.
mk (inclusion h g)
参数：H : Subgroup α；h : s <= t；g : s。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem quotientSubgroupOfEmbeddingOfLE_apply_mk (H : Subgroup α) (h : s ≤ t) (g : s) :
    quotientSubgroupOfEmbeddingOfLE H h (QuotientGroup.mk g) = QuotientGroup.mk (inclusion h g) :=
  rfl

/-- If `s ≤ t`, then there is a map `H ⧸ s.subgroupOf H → H ⧸ t.subgroupOf H`. -/
@[to_additive
/-- If `s ≤ t`, then there is a map `H ⧸ s.addSubgroupOf H → H ⧸ t.addSubgroupOf H`. -/]
/-
**Subgroup.quotientSubgroupOfMapOfLE** 是 Mathlib 中的一个定义，位于命名空间 `Subgroup`。
形式化陈述：quotientSubgroupOfMapOfLE (H : Subgroup α) (h : s <= t) : H ⧸ s.subgroupOf
 H -> H ⧸ t.subgroupOf H
参数：H : Subgroup α；h : s <= t。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Quotient.map'`：map'_mk'' (f : α -> β) (h) (x : α) : (Quotient.mk'' x : Q
uotient s₁).map' f h = (Quotient.mk'' (f x) : Quotient s₂)
-/
def quotientSubgroupOfMapOfLE (H : Subgroup α) (h : s ≤ t) :
    H ⧸ s.subgroupOf H → H ⧸ t.subgroupOf H :=
  Quotient.map' id fun a b => by
    simp_rw [leftRel_eq]
    apply h

@[to_additive (attr := simp)]
/-
**Subgroup.quotientSubgroupOfMapOfLE_apply_mk** 是 Mathlib 中的一个定理，位于命名空间 `Subgrou
p`。
形式化陈述：quotientSubgroupOfMapOfLE_apply_mk (H : Subgroup α) (h : s <= t) (g : H) :
 quotientSubgroupOfMapOfLE H h (QuotientGroup.mk g) = QuotientGroup.mk g
参数：H : Subgroup α；h : s <= t；g : H。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem quotientSubgroupOfMapOfLE_apply_mk (H : Subgroup α) (h : s ≤ t) (g : H) :
    quotientSubgroupOfMapOfLE H h (QuotientGroup.mk g) = QuotientGroup.mk g :=
  rfl

/-- If `s ≤ t`, then there is a map `α ⧸ s → α ⧸ t`. -/
@[to_additive /-- If `s ≤ t`, then there is a map `α ⧸ s → α ⧸ t`. -/]
/-
**Subgroup.quotientMapOfLE** 是 Mathlib 中的一个定义，位于命名空间 `Subgroup`。
形式化陈述：quotientMapOfLE (h : s <= t) : α ⧸ s -> α ⧸ t
参数：h : s <= t。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Quotient.map'`：map'_mk'' (f : α -> β) (h) (x : α) : (Quotient.mk'' x : Q
uotient s₁).map' f h = (Quotient.mk'' (f x) : Quotient s₂)

--- 原说明 ---
If `s ≤ t`, then there is a map `α ⧸ s → α ⧸ t`.
-/
def quotientMapOfLE (h : s ≤ t) : α ⧸ s → α ⧸ t :=
  Quotient.map' id fun a b => by
    simp_rw [leftRel_eq]
    apply h

@[to_additive (attr := simp)]
/-
**Subgroup.quotientMapOfLE_apply_mk** 是 Mathlib 中的一个定理，位于命名空间 `Subgroup`。
形式化陈述：quotientMapOfLE_apply_mk (h : s <= t) (g : α) : quotientMapOfLE h (Quotien
tGroup.mk g) = QuotientGroup.mk g
参数：h : s <= t；g : α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem quotientMapOfLE_apply_mk (h : s ≤ t) (g : α) :
    quotientMapOfLE h (QuotientGroup.mk g) = QuotientGroup.mk g :=
  rfl

/-- The natural embedding `H ⧸ (⨅ i, f i).subgroupOf H ↪ Π i, H ⧸ (f i).subgroupOf H`. -/
@[to_additive (attr := simps) /-- The natural embedding
`H ⧸ (⨅ i, f i).addSubgroupOf H) ↪ Π i, H ⧸ (f i).addSubgroupOf H`. -/]
/-
**Subgroup.quotientiInfSubgroupOfEmbedding** 是 Mathlib 中的一个定义，位于命名空间 `Subgroup`。
形式化陈述：quotientiInfSubgroupOfEmbedding {ι : Type*} (f : ι -> Subgroup α) (H : Sub
group α) : H ⧸ (⨅ i, f i).subgroupOf H ↪ forall i, H ⧸ (f i).subgroupOf H where 
toFun q i
参数：f : ι -> Subgroup α；H : Subgroup α。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def quotientiInfSubgroupOfEmbedding {ι : Type*} (f : ι → Subgroup α) (H : Subgroup α) :
    H ⧸ (⨅ i, f i).subgroupOf H ↪ ∀ i, H ⧸ (f i).subgroupOf H where
  toFun q i := quotientSubgroupOfMapOfLE H (iInf_le f i) q
  inj' :=
    Quotient.ind₂' <| by
      simp_rw [funext_iff, quotientSubgroupOfMapOfLE_apply_mk, QuotientGroup.eq, mem_subgroupOf,
        mem_iInf, imp_self, forall_const]

@[to_additive (attr := simp)]
/-
**Subgroup.quotientiInfSubgroupOfEmbedding_apply_mk** 是 Mathlib 中的一个定理，位于命名空间 `S
ubgroup`。
形式化陈述：quotientiInfSubgroupOfEmbedding_apply_mk {ι : Type*} (f : ι -> Subgroup α)
 (H : Subgroup α) (g : H) (i : ι) : quotientiInfSubgroupOfEmbedding f H (Quotien
tGroup.mk g) i = QuotientGroup.mk g
参数：f : ι -> Subgroup α；H : Subgroup α；g : H；i : ι。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem quotientiInfSubgroupOfEmbedding_apply_mk {ι : Type*} (f : ι → Subgroup α) (H : Subgroup α)
    (g : H) (i : ι) :
    quotientiInfSubgroupOfEmbedding f H (QuotientGroup.mk g) i = QuotientGroup.mk g :=
  rfl

/-- The natural embedding `α ⧸ (⨅ i, f i) ↪ Π i, α ⧸ f i`. -/
@[to_additive (attr := simps) /-- The natural embedding `α ⧸ (⨅ i, f i) ↪ Π i, α ⧸ f i`. -/]
/-
**Subgroup.quotientiInfEmbedding** 是 Mathlib 中的一个定义，位于命名空间 `Subgroup`。
形式化陈述：quotientiInfEmbedding {ι : Type*} (f : ι -> Subgroup α) : (α ⧸ ⨅ i, f i) ↪
 forall i, α ⧸ f i where toFun q i
参数：f : ι -> Subgroup α。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The natural embedding `α ⧸ (⨅ i, f i) ↪ Π i, α ⧸ f i`.
-/
def quotientiInfEmbedding {ι : Type*} (f : ι → Subgroup α) : (α ⧸ ⨅ i, f i) ↪ ∀ i, α ⧸ f i where
  toFun q i := quotientMapOfLE (iInf_le f i) q
  inj' :=
    Quotient.ind₂' <| by
      simp_rw [funext_iff, quotientMapOfLE_apply_mk, QuotientGroup.eq, mem_iInf, imp_self,
        forall_const]

@[to_additive (attr := simp)]
/-
**Subgroup.quotientiInfEmbedding_apply_mk** 是 Mathlib 中的一个定理，位于命名空间 `Subgroup`。
形式化陈述：quotientiInfEmbedding_apply_mk {ι : Type*} (f : ι -> Subgroup α) (g : α) (
i : ι) : quotientiInfEmbedding f (QuotientGroup.mk g) i = QuotientGroup.mk g
参数：f : ι -> Subgroup α；g : α；i : ι。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem quotientiInfEmbedding_apply_mk {ι : Type*} (f : ι → Subgroup α) (g : α) (i : ι) :
    quotientiInfEmbedding f (QuotientGroup.mk g) i = QuotientGroup.mk g :=
  rfl

end Subgroup

namespace MonoidHom

variable [Group α] {H : Type*} [Group H]

/-- An equivalence between any non-empty fiber of a `MonoidHom` and its kernel. -/
@[to_additive
/-- An equivalence between any non-empty fiber of an `AddMonoidHom` and its kernel. -/]
/-
**MonoidHom.fiberEquivKer** 是 Mathlib 中的一个定义，位于命名空间 `MonoidHom`。
形式化陈述：fiberEquivKer (f : α ->* H) (a : α) : f ⁻¹' {f a} ≃ f.ker
参数：f : α ->* H；a : α。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.trans`：Equiv.trans {s t u : Computation α} : s ~ t -> t ~ u -> s ~
 u
-/
def fiberEquivKer (f : α →* H) (a : α) : f ⁻¹' {f a} ≃ f.ker :=
  .trans
    (Equiv.setCongr <| Set.ext fun _ => by
      rw [mem_preimage, mem_singleton_iff, mem_smul_set_iff_inv_smul_mem, SetLike.mem_coe, mem_ker,
        smul_eq_mul, map_mul, map_inv, inv_mul_eq_one, eq_comm])
    (Subgroup.leftCosetEquivSubgroup a)

@[to_additive (attr := simp)]
/-
**MonoidHom.fiberEquivKer_apply** 是 Mathlib 中的一个引理，位于命名空间 `MonoidHom`。
形式化陈述：fiberEquivKer_apply (f : α ->* H) (a : α) (g : f ⁻¹' {f a}) : f.fiberEquiv
Ker a g = a⁻¹ * g
参数：f : α ->* H；a : α；g : f ⁻¹' {f a}。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma fiberEquivKer_apply (f : α →* H) (a : α) (g : f ⁻¹' {f a}) : f.fiberEquivKer a g = a⁻¹ * g :=
  rfl

@[to_additive (attr := simp)]
/-
**MonoidHom.fiberEquivKer_symm_apply** 是 Mathlib 中的一个引理，位于命名空间 `MonoidHom`。
形式化陈述：fiberEquivKer_symm_apply (f : α ->* H) (a : α) (g : f.ker) : (f.fiberEquiv
Ker a).symm g = a * g
参数：f : α ->* H；a : α；g : f.ker。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
-/
lemma fiberEquivKer_symm_apply (f : α →* H) (a : α) (g : f.ker) :
    (f.fiberEquivKer a).symm g = a * g :=
  rfl

/-- An equivalence between any fiber of a surjective `MonoidHom` and its kernel. -/
@[to_additive
/-- An equivalence between any fiber of a surjective `AddMonoidHom` and its kernel. -/]
/-
**MonoidHom.fiberEquivKerOfSurjective** 是 Mathlib 中的一个定义，位于命名空间 `MonoidHom`。
形式化陈述：fiberEquivKerOfSurjective {f : α ->* H} (hf : Function.Surjective f) (h : 
H) : f ⁻¹' {h} ≃ f.ker
参数：hf : Function.Surjective f；h : H。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
noncomputable def fiberEquivKerOfSurjective {f : α →* H} (hf : Function.Surjective f) (h : H) :
    f ⁻¹' {h} ≃ f.ker :=
  (hf h).choose_spec ▸ f.fiberEquivKer (hf h).choose

/-- An equivalence between any two non-empty fibers of a `MonoidHom`. -/
@[to_additive /-- An equivalence between any two non-empty fibers of an `AddMonoidHom`. -/]
/-
**MonoidHom.fiberEquiv** 是 Mathlib 中的一个定义，位于命名空间 `MonoidHom`。
形式化陈述：fiberEquiv (f : α ->* H) (a b : α) : f ⁻¹' {f a} ≃ f ⁻¹' {f b}
参数：f : α ->* H；a b : α。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.trans`：Equiv.trans {s t u : Computation α} : s ~ t -> t ~ u -> s ~
 u
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s

--- 原说明 ---
An equivalence between any two non-empty fibers of a `MonoidHom`.
-/
def fiberEquiv (f : α →* H) (a b : α) : f ⁻¹' {f a} ≃ f ⁻¹' {f b} :=
  (f.fiberEquivKer a).trans (f.fiberEquivKer b).symm

@[to_additive (attr := simp)]
/-
**MonoidHom.fiberEquiv_apply** 是 Mathlib 中的一个引理，位于命名空间 `MonoidHom`。
形式化陈述：fiberEquiv_apply (f : α ->* H) (a b : α) (g : f ⁻¹' {f a}) : f.fiberEquiv 
a b g = b * (a⁻¹ * g)
参数：f : α ->* H；a b : α；g : f ⁻¹' {f a}。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma fiberEquiv_apply (f : α →* H) (a b : α) (g : f ⁻¹' {f a}) :
    f.fiberEquiv a b g = b * (a⁻¹ * g) :=
  rfl

@[to_additive (attr := simp)]
/-
**MonoidHom.fiberEquiv_symm_apply** 是 Mathlib 中的一个引理，位于命名空间 `MonoidHom`。
形式化陈述：fiberEquiv_symm_apply (f : α ->* H) (a b : α) (g : f ⁻¹' {f b}) : (f.fiber
Equiv a b).symm g = a * (b⁻¹ * g)
参数：f : α ->* H；a b : α；g : f ⁻¹' {f b}。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
-/
lemma fiberEquiv_symm_apply (f : α →* H) (a b : α) (g : f ⁻¹' {f b}) :
    (f.fiberEquiv a b).symm g = a * (b⁻¹ * g) :=
  rfl

/-- An equivalence between any two fibers of a surjective `MonoidHom`. -/
@[to_additive /-- An equivalence between any two fibers of a surjective `AddMonoidHom`. -/]
/-
**MonoidHom.fiberEquivOfSurjective** 是 Mathlib 中的一个定义，位于命名空间 `MonoidHom`。
形式化陈述：fiberEquivOfSurjective {f : α ->* H} (hf : Function.Surjective f) (h h' : 
H) : f ⁻¹' {h} ≃ f ⁻¹' {h'}
参数：hf : Function.Surjective f；h h' : H。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.trans`：Equiv.trans {s t u : Computation α} : s ~ t -> t ~ u -> s ~
 u
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s

--- 原说明 ---
An equivalence between any two fibers of a surjective `MonoidHom`.
-/
noncomputable def fiberEquivOfSurjective {f : α →* H} (hf : Function.Surjective f) (h h' : H) :
    f ⁻¹' {h} ≃ f ⁻¹' {h'} :=
  (fiberEquivKerOfSurjective hf h).trans (fiberEquivKerOfSurjective hf h').symm

end MonoidHom

namespace QuotientGroup

variable [Group α]

/-- If `s` is a subgroup of the group `α`, and `t` is a subset of `α ⧸ s`, then there is a
(typically non-canonical) bijection between the preimage of `t` in `α` and the product `s × t`. -/
@[to_additive preimageMkEquivAddSubgroupProdSet
/-- If `s` is a subgroup of the additive group `α`, and `t` is a subset of `α ⧸ s`, then
there is a (typically non-canonical) bijection between the preimage of `t` in `α` and the product
`s × t`. -/]
/-
**QuotientGroup.preimageMkEquivSubgroupProdSet** 是 Mathlib 中的一个定义，位于命名空间 `Quotie
ntGroup`。
形式化陈述：preimageMkEquivSubgroupProdSet (s : Subgroup α) (t : Set (α ⧸ s)) : Quotie
ntGroup.mk ⁻¹' t ≃ s × t where toFun a
参数：s : Subgroup α；t : Set (α ⧸ s)。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
noncomputable def preimageMkEquivSubgroupProdSet (s : Subgroup α) (t : Set (α ⧸ s)) :
    QuotientGroup.mk ⁻¹' t ≃ s × t where
  toFun a :=
    ⟨⟨((Quotient.out (QuotientGroup.mk a)) : α)⁻¹ * a,
        leftRel_apply.mp (@Quotient.exact' _ (leftRel s) _ _ <| Quotient.out_eq' _)⟩,
      ⟨QuotientGroup.mk a, a.2⟩⟩
  invFun a :=
    ⟨Quotient.out a.2.1 * a.1.1,
      show QuotientGroup.mk _ ∈ t by
        rw [mk_mul_of_mem _ a.1.2, out_eq']
        exact a.2.2⟩
  left_inv := fun ⟨a, _⟩ => Subtype.ext <| show _ * _ = a by simp
  right_inv := fun ⟨⟨a, ha⟩, ⟨x, hx⟩⟩ => by ext <;> simp [ha]

open MulAction in
/-- A group is made up of a disjoint union of cosets of a subgroup. -/
@[to_additive /-- An additive group is made up of a disjoint union of cosets of an additive
subgroup. -/]
/-
**QuotientGroup.univ_eq_iUnion_smul** 是 Mathlib 中的一个引理，位于命名空间 `QuotientGroup`。
形式化陈述：univ_eq_iUnion_smul (H : Subgroup α) : (Set.univ (α
参数：H : Subgroup α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `MulAction.univ_eq_iUnion_orbit`：univ_eq_iUnion_orbit : Set.univ (α
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用引理 `QuotientGroup.orbit_eq_out_smul`：orbit_eq_out_smul (x : α ⧸ s) : MulActi
on.orbitRel.Quotient.orbit x = x.out • s
-/
lemma univ_eq_iUnion_smul (H : Subgroup α) :
    (Set.univ (α := α)) = ⋃ x : α ⧸ H, x.out • (H : Set _) := by
  simp_rw [univ_eq_iUnion_orbit H.op, orbit_eq_out_smul]
  rfl

variable (α) in
/-- `α ⧸ ⊥` is in bijection with `α`. See `QuotientGroup.quotientBot` for a multiplicative
version. -/
@[to_additive /-- `α ⧸ ⊥` is in bijection with `α`. See `QuotientAddGroup.quotientBot` for an
additive version. -/]
/-
**QuotientGroup.quotientEquivSelf** 是 Mathlib 中的一个定义，位于命名空间 `QuotientGroup`。
形式化陈述：quotientEquivSelf : α ⧸ (⊥ : Subgroup α) ≃ α where toFun
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def quotientEquivSelf : α ⧸ (⊥ : Subgroup α) ≃ α where
  toFun := Quotient.lift id <| fun x y (h : leftRel ⊥ x y) ↦
    eq_of_inv_mul_eq_one <| by rwa [leftRel_apply, Subgroup.mem_bot] at h
  invFun := QuotientGroup.mk
  left_inv x := by induction x using Quotient.inductionOn; simp
  right_inv x := by simp

end QuotientGroup

