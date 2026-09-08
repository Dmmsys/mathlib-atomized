/-
Copyright (c) 2024 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
module

public import Mathlib.Algebra.Order.Group.Abs
public import Mathlib.Algebra.Order.Monoid.Submonoid
public import Mathlib.Algebra.Order.Ring.Basic
public import Mathlib.Algebra.Order.Ring.Int
public import Mathlib.Algebra.Order.Star.Basic

/-!
# Star ordered ring structure on `ℤ`

This file shows that `ℤ` is a `StarOrderedRing`.
-/

public section

open AddSubmonoid Set

namespace Int

/-
**Int.addSubmonoid_closure_range_pow** 是 Mathlib 中的一个定理，位于命名空间 `Int`。
形式化陈述：∀ {n : ℕ}, Even n → AddSubmonoid.closure (Set.range fun x => x ^ n) = AddS
ubmonoid.nonneg ℤ
参数：Set.range fun x => x ^ n。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `AddSubmonoid.closure_le`：∀ {M : Type u_1} [inst : AddZeroClass M] {s : S
et M} {S : AddSubmonoid M}, AddSubmonoid.closure s ≤ S ↔ s ⊆ ↑S
· 使用定理 `Set.range_subset_iff`：range_subset_iff : range f subseteq s ↔ forall y, 
f y in s
· 使用定理 `Even.pow_nonneg`：∀ {R : Type u_3} [inst : Semiring R] [inst_1 : LinearOr
der R] [IsOrderedRing R] [ExistsAddOfLE R] {n : ℕ},   Even n → ∀ (a : R), 0 ≤ a 
^ n
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `AddGroup.existsAddOfLE`：∀ (α : Type u) [inst : AddGroup α] [inst_1 : LE 
α], ExistsAddOfLE α
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `one_pow`：one_pow {a : R} (b : Nat) (ha : IsNat a 1) : a ^ b = a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Nat.cast_natAbs`：∀ {α : Type u_1} [inst : AddGroupWithOne α] (n : ℤ), ↑n
.natAbs = ↑|n|
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `eq_comm`：∀ {α : Sort u_1} {a b : α}, a = b ↔ b = a
· 使用定理 `nsmul_mem`：∀ {M : Type u_3} {A : Type u_4} [inst : AddMonoid M] [inst_1 
: SetLike A M] [AddSubmonoidClass A M] {S : A} {x : M},   x ∈ S → ∀ (n : ℕ), n …
· 使用定理 `AddSubmonoid.instAddSubmonoidClass`：∀ {M : Type u_1} [inst : AddZeroClas
s M], AddSubmonoidClass (AddSubmonoid M) M
· 使用定理 `AddSubmonoid.subset_closure`：∀ {M : Type u_1} [inst : AddZeroClass M] {s
 : Set M}, s ⊆ ↑(AddSubmonoid.closure s)
· 使用定理 `Set.mem_range_self`：∀ {α : Type u} {ι : Sort u_1} {f : ι → α} (i : ι), f
 i ∈ Set.range f
-/
@[simp] lemma addSubmonoid_closure_range_pow {n : ℕ} (hn : Even n) :
    closure (range fun x : ℤ ↦ x ^ n) = nonneg _ := by
  refine le_antisymm (closure_le.2 <| range_subset_iff.2 hn.pow_nonneg) fun x hx ↦ ?_
  have : x = x.natAbs • 1 ^ n := by simpa [eq_comm (a := x)] using hx
  rw [this]
  exact nsmul_mem (subset_closure <| mem_range_self _) _

@[simp]
/-
**Int.addSubmonoid_closure_range_mul_self** 是 Mathlib 中的一个引理，位于命名空间 `Int`。
形式化陈述：addSubmonoid_closure_range_mul_self : closure (range fun x : Int => x * x)
 = nonneg _
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `sq`：∀ {M : Type u_2} [inst : Monoid M] (a : M), a ^ 2 = a * a
· 使用定理 `Int.addSubmonoid_closure_range_pow`：∀ {n : ℕ}, Even n → AddSubmonoid.clo
sure (Set.range fun x => x ^ n) = AddSubmonoid.nonneg ℤ
· 使用定理 `even_two`：∀ {α : Type u_2} [inst : AddMonoidWithOne α], Even 2
-/
lemma addSubmonoid_closure_range_mul_self : closure (range fun x : ℤ ↦ x * x) = nonneg _ := by
  simpa only [sq] using addSubmonoid_closure_range_pow even_two
/-
**Int.instStarOrderedRing** 是 Mathlib 中的一个实例，位于命名空间 `Int`。
形式化陈述：instStarOrderedRing : StarOrderedRing Int where le_iff a b
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `le_iff_exists_nonneg_add`：∀ {α : Type u} [inst : AddZeroClass α] [inst_1
 : Preorder α] [ExistsAddOfLE α] {a b : α} [AddLeftMono α]   [AddLeftReflectLE α
], a ≤ b ↔ ∃ c…
· 使用定理 `AddGroup.existsAddOfLE`：∀ (α : Type u) [inst : AddGroup α] [inst_1 : LE 
α], ExistsAddOfLE α
· 使用定理 `IsLeftCancelAdd.addLeftReflectLE_of_addLeftReflectLT`：∀ (N : Type u_2) [
inst : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftReflectLT N]
, AddLeftReflectLE N
· 使用定理 `AddLeftCancelSemigroup.toIsLeftCancelAdd`：∀ {G : Type u} [self : AddLeft
CancelSemigroup G], IsLeftCancelAdd G
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `TrivialStar.star_trivial`：∀ {R : Type u} {inst : Star R} [self : Trivial
Star R] (r : R), star r = r
· 使用引理 `Int.addSubmonoid_closure_range_mul_self`：addSubmonoid_closure_range_mul_
self : closure (range fun x : Int => x * x) = nonneg _
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
instance instStarOrderedRing : StarOrderedRing ℤ where
  le_iff a b := by simp [eq_comm, le_iff_exists_nonneg_add (a := a)]

end Int

