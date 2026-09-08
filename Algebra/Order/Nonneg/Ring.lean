/-
Copyright (c) 2021 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn
-/
module

public import Mathlib.Algebra.Order.GroupWithZero.Canonical
public import Mathlib.Algebra.Order.Nonneg.Basic
public import Mathlib.Algebra.Order.Nonneg.Lattice
public import Mathlib.Algebra.Order.Ring.InjSurj
public import Mathlib.Tactic.FastInstance

/-!
# Bundled ordered algebra instance on the type of nonnegative elements

This file defines instances and prove some properties about the nonnegative elements
`{x : α // 0 ≤ x}` of an arbitrary type `α`.

Currently we only state instances and states some `simp`/`norm_cast` lemmas.

When `α` is `ℝ`, this will give us some properties about `ℝ≥0`.

## Implementation Notes

Instead of `{x : α // 0 ≤ x}` we could also use `Set.Ici (0 : α)`, which is definitionally equal.
However, using the explicit subtype has a big advantage: when writing an element explicitly
with a proof of nonnegativity as `⟨x, hx⟩`, the `hx` is expected to have type `0 ≤ x`. If we would
use `Ici 0`, then the type is expected to be `x ∈ Ici 0`. Although these types are definitionally
equal, this often confuses the elaborator. Similar problems arise when doing cases on an element.

The disadvantage is that we have to duplicate some instances about `Set.Ici` to this subtype.
-/

public section

open Set

variable {α : Type*}

namespace Nonneg

/-
**Nonneg.isOrderedAddMonoid** 是 Mathlib 中的一个实例，位于命名空间 `Nonneg`。
形式化陈述：isOrderedAddMonoid [AddCommMonoid α] [PartialOrder α] [IsOrderedAddMonoid 
α] : IsOrderedAddMonoid { x : α // 0 <= x }
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Injective.isOrderedAddMonoid`：∀ {α : Type u} {β : Type u_1} [in
st : AddCommMonoid α] [inst_1 : Preorder α] [IsOrderedAddMonoid α]   [inst_3 : A
ddCommMonoid β] [inst_4 : P…
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `Nonneg.coe_add`：∀ {α : Type u_1} [inst : AddZeroClass α] [inst_1 : Preor
der α] [inst_2 : AddLeftMono α] (a b : { x // 0 ≤ x }),   ↑(a + b) = ↑a + ↑b
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
instance isOrderedAddMonoid [AddCommMonoid α] [PartialOrder α] [IsOrderedAddMonoid α] :
    IsOrderedAddMonoid { x : α // 0 ≤ x } :=
  Function.Injective.isOrderedAddMonoid Subtype.val Nonneg.coe_add .rfl
/-
**Nonneg.isOrderedCancelAddMonoid** 是 Mathlib 中的一个实例，位于命名空间 `Nonneg`。
形式化陈述：isOrderedCancelAddMonoid [AddCommMonoid α] [PartialOrder α] [IsOrderedCanc
elAddMonoid α] : IsOrderedCancelAddMonoid { x : α // 0 <= x }
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Injective.isOrderedCancelAddMonoid`：∀ {α : Type u} {β : Type u_
1} [inst : AddCommMonoid α] [inst_1 : Preorder α] [IsOrderedCancelAddMonoid α]  
 [inst_3 : AddCommMonoid β] [inst…
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `IsOrderedCancelAddMonoid.toIsOrderedAddMonoid`：∀ {α : Type u_2} {inst : 
AddCommMonoid α} {inst_1 : Preorder α} [self : IsOrderedCancelAddMonoid α],   Is
OrderedAddMonoid α
· 使用定理 `Nonneg.coe_add`：∀ {α : Type u_1} [inst : AddZeroClass α] [inst_1 : Preor
der α] [inst_2 : AddLeftMono α] (a b : { x // 0 ≤ x }),   ↑(a + b) = ↑a + ↑b
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
instance isOrderedCancelAddMonoid [AddCommMonoid α] [PartialOrder α] [IsOrderedCancelAddMonoid α] :
    IsOrderedCancelAddMonoid { x : α // 0 ≤ x } :=
  Function.Injective.isOrderedCancelAddMonoid _ Nonneg.coe_add .rfl
/-
**Nonneg.isOrderedRing** 是 Mathlib 中的一个实例，位于命名空间 `Nonneg`。
形式化陈述：isOrderedRing [Semiring α] [PartialOrder α] [IsOrderedRing α] : IsOrderedR
ing { x : α // 0 <= x }
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Injective.isOrderedRing`：∀ {R : Type u_1} {S : Type u_2} [inst 
: Semiring R] [inst_1 : PartialOrder R] [IsOrderedRing R] [inst_3 : Semiring S] 
  [inst_4 : PartialOrd…
· 使用定理 `IsOrderedRing.toZeroLEOneClass`：∀ {R : Type u_1} {inst : Semiring R} {in
st_1 : PartialOrder R} [self : IsOrderedRing R], ZeroLEOneClass R
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `IsOrderedRing.toIsOrderedAddMonoid`：∀ {R : Type u_1} {inst : Semiring R}
 {inst_1 : PartialOrder R} [self : IsOrderedRing R], IsOrderedAddMonoid R
· 使用定理 `IsOrderedRing.toPosMulMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], PosMulMono R
· 使用定理 `Nonneg.coe_zero`：∀ {α : Type u_1} [inst : Zero α] [inst_1 : Preorder α],
 ↑0 = 0
· 使用定理 `Nonneg.coe_one`：∀ {α : Type u_1} [inst : Zero α] [inst_1 : One α] [inst_
2 : LE α] [inst_3 : ZeroLEOneClass α], ↑1 = 1
· 使用定理 `Nonneg.coe_add`：∀ {α : Type u_1} [inst : AddZeroClass α] [inst_1 : Preor
der α] [inst_2 : AddLeftMono α] (a b : { x // 0 ≤ x }),   ↑(a + b) = ↑a + ↑b
· 使用定理 `Nonneg.coe_mul`：∀ {α : Type u_1} [inst : MulZeroClass α] [inst_1 : Preor
der α] [inst_2 : PosMulMono α] (a b : { x // 0 ≤ x }),   ↑(a * b) = ↑a * ↑b
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
instance isOrderedRing [Semiring α] [PartialOrder α] [IsOrderedRing α] :
    IsOrderedRing { x : α // 0 ≤ x } :=
  Function.Injective.isOrderedRing Subtype.val Nonneg.coe_zero Nonneg.coe_one Nonneg.coe_add
    Nonneg.coe_mul .rfl
/-
**Nonneg.isStrictOrderedRing** 是 Mathlib 中的一个实例，位于命名空间 `Nonneg`。
形式化陈述：isStrictOrderedRing [Semiring α] [PartialOrder α] [IsStrictOrderedRing α] 
: IsStrictOrderedRing { x : α // 0 <= x }
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Injective.isStrictOrderedRing`：∀ {R : Type u_1} {S : Type u_2} 
[inst : Semiring R] [inst_1 : PartialOrder R] [IsStrictOrderedRing R]   [inst_3 
: Semiring S] [inst_4 : Part…
· 使用定理 `IsStrictOrderedRing.toZeroLEOneClass`：∀ {R : Type u_1} {inst : Semiring 
R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], ZeroLEOneClass R
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `IsOrderedRing.toIsOrderedAddMonoid`：∀ {R : Type u_1} {inst : Semiring R}
 {inst_1 : PartialOrder R} [self : IsOrderedRing R], IsOrderedAddMonoid R
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `IsOrderedRing.toPosMulMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], PosMulMono R
· 使用定理 `Nonneg.coe_zero`：∀ {α : Type u_1} [inst : Zero α] [inst_1 : Preorder α],
 ↑0 = 0
· 使用定理 `Nonneg.coe_one`：∀ {α : Type u_1} [inst : Zero α] [inst_1 : One α] [inst_
2 : LE α] [inst_3 : ZeroLEOneClass α], ↑1 = 1
· 使用定理 `Nonneg.coe_add`：∀ {α : Type u_1} [inst : AddZeroClass α] [inst_1 : Preor
der α] [inst_2 : AddLeftMono α] (a b : { x // 0 ≤ x }),   ↑(a + b) = ↑a + ↑b
· 使用定理 `Nonneg.coe_mul`：∀ {α : Type u_1} [inst : MulZeroClass α] [inst_1 : Preor
der α] [inst_2 : PosMulMono α] (a b : { x // 0 ≤ x }),   ↑(a * b) = ↑a * ↑b
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
instance isStrictOrderedRing [Semiring α] [PartialOrder α] [IsStrictOrderedRing α] :
    IsStrictOrderedRing { x : α // 0 ≤ x } :=
  Function.Injective.isStrictOrderedRing Subtype.val Nonneg.coe_zero Nonneg.coe_one Nonneg.coe_add
    Nonneg.coe_mul .rfl .rfl
/-
**Nonneg.existsAddOfLE** 是 Mathlib 中的一个实例，位于命名空间 `Nonneg`。
形式化陈述：existsAddOfLE [Semiring α] [PartialOrder α] [IsStrictOrderedRing α] [Exist
sAddOfLE α] : ExistsAddOfLE { x : α // 0 <= x }
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `IsOrderedRing.toIsOrderedAddMonoid`：∀ {R : Type u_1} {inst : Semiring R}
 {inst_1 : PartialOrder R} [self : IsOrderedRing R], IsOrderedAddMonoid R
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `ExistsAddOfLE.exists_add_of_le`：∀ {α : Type u} {inst : Add α} {inst_1 : 
LE α} [self : ExistsAddOfLE α] {a b : α}, a ≤ b → ∃ c, b = a + c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Subtype.coe_le_coe`：coe_le_coe [LE α] {p : α -> Prop} {x y : Subtype p} 
: (x : α) <= y ↔ x <= y
· 使用定理 `le_of_add_le_add_left`：∀ {α : Type u_1} [inst : Add α] [inst_1 : LE α] [
AddLeftReflectLE α] {a b c : α}, a + b ≤ a + c → b ≤ c
· 使用定理 `IsLeftCancelAdd.addLeftReflectLE_of_addLeftReflectLT`：∀ (N : Type u_2) [
inst : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftReflectLT N]
, AddLeftReflectLE N
· 使用定理 `IsCancelAdd.toIsLeftCancelAdd`：∀ {G : Type u} {inst : Add G} [self : IsC
ancelAdd G], IsLeftCancelAdd G
· 使用定理 `IsOrderedCancelAddMonoid.toIsCancelAdd`：∀ {α : Type u_1} [inst : AddComm
Monoid α] [inst_1 : PartialOrder α] [IsOrderedCancelAddMonoid α], IsCancelAdd α
· 使用定理 `IsStrictOrderedRing.toIsOrderedCancelAddMonoid`：∀ {R : Type u_1} {inst :
 Semiring R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R],   IsOrder
edCancelAddMonoid R
· 使用定理 `IsOrderedCancelAddMonoid.toAddLeftReflectLT`：∀ {α : Type u_1} [inst : Ad
dCommMonoid α] [inst_1 : PartialOrder α] [IsOrderedCancelAddMonoid α], AddLeftRe
flectLT α
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
instance existsAddOfLE [Semiring α] [PartialOrder α] [IsStrictOrderedRing α] [ExistsAddOfLE α] :
    ExistsAddOfLE { x : α // 0 ≤ x } :=
  ⟨fun {a b} h ↦ by
    rw [← Subtype.coe_le_coe] at h
    obtain ⟨c, hc⟩ := exists_add_of_le h
    refine ⟨⟨c, ?_⟩, by simp [Subtype.ext_iff, hc]⟩
    rw [← add_zero a.val, hc] at h
    exact le_of_add_le_add_left h⟩
/-
**Nonneg.nontrivial** 是 Mathlib 中的一个实例，位于命名空间 `Nonneg`。
形式化陈述：nontrivial [Semiring α] [LinearOrder α] [IsStrictOrderedRing α] : Nontrivi
al { x : α // 0 <= x }
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `IsStrictOrderedRing.toZeroLEOneClass`：∀ {R : Type u_1} {inst : Semiring 
R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], ZeroLEOneClass R
· 使用定理 `zero_ne_one`：∀ {α : Type u_2} [inst : Zero α] [inst_1 : One α] [NeZero 1
], 0 ≠ 1
· 使用定理 `IsStrictOrderedRing.toCharZero`：∀ {R : Type u} [inst : Semiring R] [inst
_1 : PartialOrder R] [IsStrictOrderedRing R], CharZero R
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
-/
instance nontrivial [Semiring α] [LinearOrder α] [IsStrictOrderedRing α] :
    Nontrivial { x : α // 0 ≤ x } :=
  ⟨⟨0, 1, fun h => zero_ne_one (congr_arg Subtype.val h)⟩⟩
/-
**Nonneg.** 是 Mathlib 中的一个实例，位于命名空间 `Nonneg`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Nontrivial α] [AddGroup α] [LinearOrder α] [AddLeftMono α] :
    Nontrivial { x : α // 0 ≤ x } := by
  have ⟨a, ha⟩ := exists_ne (0 : α)
  obtain lt | lt := ha.lt_or_gt
  · exact ⟨0, ⟨-a, neg_nonneg.mpr lt.le⟩, Subtype.coe_ne_coe.mp (neg_ne_zero.mpr ha).symm⟩
  · exact ⟨0, ⟨a, lt.le⟩, Subtype.coe_ne_coe.mp ha.symm⟩
/-
**Nonneg.linearOrderedCommMonoidWithZero** 是 Mathlib 中的一个实例，位于命名空间 `Nonneg`。
形式化陈述：linearOrderedCommMonoidWithZero [CommSemiring α] [LinearOrder α] [IsStrict
OrderedRing α] : LinearOrderedCommMonoidWithZero { x : α // 0 <= x } where isBot
_zero a
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance linearOrderedCommMonoidWithZero [CommSemiring α] [LinearOrder α] [IsStrictOrderedRing α] :
    LinearOrderedCommMonoidWithZero { x : α // 0 ≤ x } where
  isBot_zero a := a.2
/-
**Nonneg.canonicallyOrderedAdd** 是 Mathlib 中的一个实例，位于命名空间 `Nonneg`。
形式化陈述：canonicallyOrderedAdd [Ring α] [PartialOrder α] [IsOrderedRing α] : Canoni
callyOrderedAdd { x : α // 0 <= x } where le_add_self _ b
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `IsOrderedRing.toIsOrderedAddMonoid`：∀ {R : Type u_1} {inst : Semiring R}
 {inst_1 : PartialOrder R} [self : IsOrderedRing R], IsOrderedAddMonoid R
· 使用定理 `sub_nonneg_of_le`：∀ {α : Type u} [inst : AddGroup α] [inst_1 : LE α] [Ad
dRightMono α] {a b : α}, b ≤ a → 0 ≤ a - b
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `Subtype.ext`：∀ {α : Sort u} {p : α → Prop} {a1 a2 : { x // p x }}, ↑a1 =
 ↑a2 → a1 = a2
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `add_sub_cancel`：∀ {G : Type u_3} [inst : AddCommGroup G] (a b : G), a + 
(b - a) = b
· 使用定理 `le_add_of_nonneg_left`：∀ {α : Type u_1} [inst : AddZeroClass α] [inst_1 
: LE α] [AddRightMono α] {a b : α}, 0 ≤ b → a ≤ b + a
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `le_add_of_nonneg_right`：∀ {α : Type u_1} [inst : AddZeroClass α] [inst_1
 : LE α] [AddLeftMono α] {a b : α}, 0 ≤ b → a ≤ a + b
-/
instance canonicallyOrderedAdd [Ring α] [PartialOrder α] [IsOrderedRing α] :
    CanonicallyOrderedAdd { x : α // 0 ≤ x } where
  le_add_self _ b := le_add_of_nonneg_left b.2
  le_self_add _ b := le_add_of_nonneg_right b.2
  exists_add_of_le := fun {a b} h =>
    ⟨⟨b - a, sub_nonneg_of_le h⟩, Subtype.ext (add_sub_cancel _ _).symm⟩
/-
**Nonneg.noZeroDivisors** 是 Mathlib 中的一个实例，位于命名空间 `Nonneg`。
形式化陈述：noZeroDivisors [Semiring α] [PartialOrder α] [IsOrderedRing α] [NoZeroDivi
sors α] : NoZeroDivisors { x : α // 0 <= x }
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `IsOrderedRing.toPosMulMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], PosMulMono R
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `mul_nonneg`：∀ {α : Type u_1} [inst : MulZeroClass α] {a b : α} [inst_1 :
 Preorder α] [PosMulMono α], 0 ≤ a → 0 ≤ b → 0 ≤ a * b
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
-/
instance noZeroDivisors [Semiring α] [PartialOrder α] [IsOrderedRing α] [NoZeroDivisors α] :
    NoZeroDivisors { x : α // 0 ≤ x } :=
  { eq_zero_or_eq_zero_of_mul_eq_zero := by
      rintro ⟨a, ha⟩ ⟨b, hb⟩
      simp only [mk_mul_mk, mk_eq_zero, mul_eq_zero, imp_self] }
/-
**Nonneg.orderedSub** 是 Mathlib 中的一个实例，位于命名空间 `Nonneg`。
形式化陈述：orderedSub [Ring α] [LinearOrder α] [IsStrictOrderedRing α] : OrderedSub {
 x : α // 0 <= x }
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `IsOrderedRing.toIsOrderedAddMonoid`：∀ {R : Type u_1} {inst : Semiring R}
 {inst_1 : PartialOrder R} [self : IsOrderedRing R], IsOrderedAddMonoid R
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `add_nonneg`：∀ {α : Type u_1} [inst : AddZeroClass α] [inst_1 : Preorder 
α] [AddLeftMono α] {a b : α}, 0 ≤ a → 0 ≤ b → 0 ≤ a + b
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
instance orderedSub [Ring α] [LinearOrder α] [IsStrictOrderedRing α] :
    OrderedSub { x : α // 0 ≤ x } :=
  ⟨by
    rintro ⟨a, ha⟩ ⟨b, hb⟩ ⟨c, hc⟩
    simp only [sub_le_iff_le_add, Subtype.mk_le_mk, mk_sub_mk, mk_add_mk, toNonneg_le]⟩

end Nonneg

