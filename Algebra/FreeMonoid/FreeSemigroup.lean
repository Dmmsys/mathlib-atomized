/-
Copyright (c) 2026 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public import Mathlib.Algebra.FreeMonoid.Basic
public import Mathlib.Algebra.Free
public import Mathlib.Algebra.Group.WithOne.Basic
public import Mathlib.Algebra.Group.Units.Basic
public import Mathlib.Data.Set.Operations

import Mathlib.Data.Set.Insert

/-!
# Relation between the free semigroup and the free monoid

We provide some constructions relating the free semigroup and the free monoid on the same type.

## Main definitions
* `FreeSemigroup.toFreeMonoid`: the natural embedding of the free semigroup into the free monoid.
* `FreeMonoid.equivWithOneFreeSemigroup`: the free monoid is isomorphic to the free semigroup
  with a `1` added.
-/

public section

variable {α : Type*}

namespace FreeSemigroup

open FreeMonoid

/--
The natural embedding of the free semigroup into the free monoid.
This is injective (`FreeSemigroup.toFreeMonoid_injective`), and its image
consists of all non-`1` elements of the free monoid (`FreeSemigroup.eq_one_or_toFreeMonoid`).
-/
@[expose, to_additive /-- The natural embedding of the free additive semigroup into the
free additive monoid. This is injective (`FreeAddSemigroup.toFreeAddMonoid_injective`), and its
image consists of all non-`0` elements of the free additive monoid
(`FreeAddSemigroup.eq_zero_or_toFreeAddMonoid`). -/]
/-
**FreeSemigroup.toFreeMonoid** 是 Mathlib 中的一个定义，位于命名空间 `FreeSemigroup`。
形式化陈述：toFreeMonoid : FreeSemigroup α ->ₙ* FreeMonoid α
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def toFreeMonoid : FreeSemigroup α →ₙ* FreeMonoid α :=
  lift FreeMonoid.of

@[to_additive (attr := simp, grind =)]
/-
**FreeSemigroup.toFreeMonoid_of** 是 Mathlib 中的一个引理，位于命名空间 `FreeSemigroup`。
形式化陈述：toFreeMonoid_of (x : α) : toFreeMonoid (.of x) = .of x
参数：x : α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma toFreeMonoid_of (x : α) : toFreeMonoid (.of x) = .of x := rfl

@[to_additive]
/-
**FreeSemigroup.toFreeMonoid_mk_eq_cons** 是 Mathlib 中的一个引理，位于命名空间 `FreeSemigroup
`。
形式化陈述：toFreeMonoid_mk_eq_cons (x : α) (xs : List α) : toFreeMonoid ⟨x, xs⟩ = Fre
eMonoid.ofList (x :: xs)
参数：x : α；xs : List α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `MulHom.mk.congr_simp`：∀ {M : Type u_10} {N : Type u_11} [inst : Mul M] [
inst_1 : Mul N] (toFun toFun_1 : M → N) (e_toFun : toFun = toFun_1)   (map_mul' 
: ∀ (x y :…
· 使用定理 `Equiv.mk.congr_simp`：∀ {α : Sort u_1} {β : Sort u_2} (toFun toFun_1 : α 
→ β) (e_toFun : toFun = toFun_1) (invFun invFun_1 : β → α)   (e_invFun : invFun 
= invFun_…
-/
lemma toFreeMonoid_mk_eq_cons (x : α) (xs : List α) :
    toFreeMonoid ⟨x, xs⟩ = FreeMonoid.ofList (x :: xs) := by
  suffices ∀ x : FreeMonoid α, (xs.map FreeMonoid.of).foldl (· * ·) x = x * ofList xs by
    simpa [← List.foldl_map, lift_mk_eq_foldl, toFreeMonoid, lift] using this (FreeMonoid.of x)
  induction xs with grind [ofList_nil, ofList_cons]

@[to_additive (attr := grind .)]
/-
**FreeSemigroup.toFreeMonoid_injective** 是 Mathlib 中的一个引理，位于命名空间 `FreeSemigroup`
。
形式化陈述：toFreeMonoid_injective : Function.Injective (@toFreeMonoid α)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `FreeSemigroup.mk.injEq`：∀ {α : Type u} (head : α) (tail : List α) (head_
1 : α) (tail_1 : List α),   ({ head := head, tail := tail } = { head := head_1, 
tail := tail…
· 使用定理 `List.cons.injEq`：∀ {α : Type u} (head : α) (tail : List α) (head_1 : α) 
(tail_1 : List α),   (head :: tail = head_1 :: tail_1) = (head = head_1 ∧ tail =
 tail…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `FreeSemigroup.toFreeMonoid_mk_eq_cons`：toFreeMonoid_mk_eq_cons (x : α) (
xs : List α) : toFreeMonoid ⟨x, xs⟩ = FreeMonoid.ofList (x :: xs)
-/
lemma toFreeMonoid_injective : Function.Injective (@toFreeMonoid α) := by
  rintro ⟨x, xs⟩ ⟨y, ys⟩ h
  simp only [toFreeMonoid_mk_eq_cons, Equiv.apply_eq_iff_eq] at h
  simpa using h

@[to_additive (attr := simp, grind .)]
/-
**FreeSemigroup.toFreeMonoid_ne_one** 是 Mathlib 中的一个引理，位于命名空间 `FreeSemigroup`。
形式化陈述：toFreeMonoid_ne_one (x : FreeSemigroup α) : toFreeMonoid x != 1
参数：x : FreeSemigroup α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `map_mul`：map_mul [MulHomClass F M N] (f : F) (x y : M) : f (x * y) = f x
 * f y
· 使用定理 `Unique.instSubsingleton`：∀ {α : Sort u_1} [Unique α], Subsingleton α
· 使用定理 `false_and`：∀ (p : Prop), (False ∧ p) = False
-/
lemma toFreeMonoid_ne_one (x : FreeSemigroup α) : toFreeMonoid x ≠ 1 := by
  induction x with simp

@[to_additive]
/-
**FreeSemigroup.eq_one_or_toFreeMonoid** 是 Mathlib 中的一个引理，位于命名空间 `FreeSemigroup`
。
形式化陈述：eq_one_or_toFreeMonoid (x : FreeMonoid α) : x = 1 ∨ exists y, toFreeMonoid
 y = x
参数：x : FreeMonoid α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `FreeMonoid.inductionOn'`：∀ {α : Type u_1} {motive : FreeMonoid α → Prop}
 (a : FreeMonoid α),   motive 1 → (∀ (b : α) (a : FreeMonoid α), motive a → moti
ve (FreeMonoi…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `or_false`：∀ (p : Prop), (p ∨ False) = p
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `map_mul`：map_mul [MulHomClass F M N] (f : F) (x y : M) : f (x * y) = f x
 * f y
-/
lemma eq_one_or_toFreeMonoid (x : FreeMonoid α) : x = 1 ∨ ∃ y, toFreeMonoid y = x :=
  x.inductionOn' (by simp) <| by
    rintro b _ (rfl | ⟨y, rfl⟩)
    · exact Or.inr ⟨of b, by simp⟩
    · exact Or.inr ⟨of b * y, by simp⟩

@[to_additive (attr := simp)]
/-
**FreeSemigroup.range_toFreeMonoid** 是 Mathlib 中的一个引理，位于命名空间 `FreeSemigroup`。
形式化陈述：range_toFreeMonoid : Set.range (@toFreeMonoid α) = {1}ᶜ
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
-/
lemma range_toFreeMonoid : Set.range (@toFreeMonoid α) = {1}ᶜ := by
  ext x; grind [eq_one_or_toFreeMonoid x]

end FreeSemigroup

open FreeSemigroup FreeMonoid WithOne

/--
The free monoid on `α` is isomorphic to the free semigroup on `α` with a `1` added.
-/
@[expose, to_additive (attr := simps) /-- The free additive monoid on `α` is isomorphic to
the free additive semigroup on `α` with a `0` added. -/]
/-
**FreeMonoid.equivWithOneFreeSemigroup** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：FreeMonoid.equivWithOneFreeSemigroup : FreeMonoid α ≃* WithOne (FreeSemigr
oup α) where toFun
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def FreeMonoid.equivWithOneFreeSemigroup : FreeMonoid α ≃* WithOne (FreeSemigroup α) where
  toFun := lift fun x ↦ ↑(FreeSemigroup.of x)
  invFun := WithOne.lift toFreeMonoid
  left_inv x := by induction x with simp [*]
  right_inv x := by
    induction x with
    | one => simp
    | coe a => induction a with simp_all
  map_mul' := by simp
