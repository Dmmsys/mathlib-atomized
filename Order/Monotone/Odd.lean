/-
Copyright (c) 2022 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
module

public import Mathlib.Algebra.Order.Group.Defs
public import Mathlib.Algebra.Order.Monoid.OrderDual
public import Mathlib.Order.Monotone.Union

/-!
# Monotonicity of odd functions

An odd function on a linear ordered additive commutative group `G` is monotone on the whole group
provided that it is monotone on `Set.Ici 0`, see `monotone_of_odd_of_monotoneOn_nonneg`. We also
prove versions of this lemma for `Antitone`, `StrictMono`, and `StrictAnti`.
-/

public section


open Set

variable {G H : Type*} [AddCommGroup G] [LinearOrder G] [IsOrderedAddMonoid G]
  [AddCommGroup H] [PartialOrder H] [IsOrderedAddMonoid H]

/-- An odd function on a linear ordered additive commutative group is strictly monotone on the whole
group provided that it is strictly monotone on `Set.Ici 0`. -/
/-
**strictMono_of_odd_strictMonoOn_nonneg** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：strictMono_of_odd_strictMonoOn_nonneg {f : G -> H} (h₁ : forall x, f (-x) 
= -f x) (h₂ : StrictMonoOn f (Ici 0)) : StrictMono f
参数：h₁ : forall x, f (-x) = -f x；h₂ : StrictMonoOn f (Ici 0)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `StrictMonoOn.Iic_union_Ici`：∀ {α : Type u_1} {β : Type u_2} [inst : Line
arOrder α] [inst_1 : Preorder β] {a : α} {f : α → β},   StrictMonoOn f (Set.Iic 
a) → StrictMonoO…
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `neg_lt_neg_iff`：∀ {α : Type u} [inst : AddGroup α] [inst_1 : LT α] [AddL
eftStrictMono α] {a b : α} [AddRightStrictMono α],   -a < -b ↔ b < a
· 使用定理 `IsLeftCancelAdd.addLeftStrictMono_of_addLeftMono`：∀ (N : Type u_2) [inst
 : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftMono N], AddLeft
StrictMono N
· 使用定理 `instIsLeftCancelAddOfAddLeftReflectLE`：∀ {α : Type u_1} [inst : Add α] [
inst_1 : PartialOrder α] [AddLeftReflectLE α], IsLeftCancelAdd α
· 使用定理 `AddGroup.addLeftReflectLE_of_addLeftMono`：∀ {N : Type u_2} [inst : AddGr
oup N] [inst_1 : LE N] [AddLeftMono N], AddLeftReflectLE N
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `IsRightCancelAdd.addRightStrictMono_of_addRightMono`：∀ (N : Type u_2) [i
nst : Add N] [IsRightCancelAdd N] [inst_2 : PartialOrder N] [AddRightMono N], Ad
dRightStrictMono N
· 使用定理 `instIsRightCancelAddOfAddRightReflectLE`：∀ {α : Type u_1} [inst : Add α]
 [inst_1 : PartialOrder α] [AddRightReflectLE α], IsRightCancelAdd α
· 使用定理 `addRightReflectLE_of_addLeftReflectLE`：∀ (N : Type u_2) [inst : AddCommS
emigroup N] [inst_1 : LE N] [AddLeftReflectLE N], AddRightReflectLE N
· 使用定理 `IsLeftCancelAdd.addLeftReflectLE_of_addLeftReflectLT`：∀ (N : Type u_2) [
inst : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftReflectLT N]
, AddLeftReflectLE N
· 使用定理 `AddLeftCancelSemigroup.toIsLeftCancelAdd`：∀ {G : Type u} [self : AddLeft
CancelSemigroup G], IsLeftCancelAdd G
· 使用定理 `IsOrderedCancelAddMonoid.toAddLeftReflectLT`：∀ {α : Type u_1} [inst : Ad
dCommMonoid α] [inst_1 : PartialOrder α] [IsOrderedCancelAddMonoid α], AddLeftRe
flectLT α
· 使用定理 `IsOrderedAddMonoid.toIsOrderedCancelAddMonoid`：∀ {α : Type u} [inst : Ad
dCommGroup α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], IsOrderedCancelAddMo
noid α
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `neg_nonneg`：∀ {α : Type u} [inst : AddGroup α] [inst_1 : LE α] [AddLeftM
ono α] {a : α}, 0 ≤ -a ↔ a ≤ 0
· 使用定理 `neg_lt_neg`：∀ {α : Type u} [inst : AddCommGroup α] [inst_1 : PartialOrde
r α] [IsOrderedAddMonoid α] {a b : α}, a < b → -b < -a

--- 原说明 ---
An odd function on a linear ordered additive commutative group is strictly monot
one on the whole
group provided that it is strictly monotone on `Set.Ici 0`.
-/
theorem strictMono_of_odd_strictMonoOn_nonneg {f : G → H} (h₁ : ∀ x, f (-x) = -f x)
    (h₂ : StrictMonoOn f (Ici 0)) : StrictMono f := by
  refine StrictMonoOn.Iic_union_Ici (fun x hx y hy hxy => neg_lt_neg_iff.1 ?_) h₂
  rw [← h₁, ← h₁]
  exact h₂ (neg_nonneg.2 hy) (neg_nonneg.2 hx) (neg_lt_neg hxy)

/-- An odd function on a linear ordered additive commutative group is strictly antitone on the whole
group provided that it is strictly antitone on `Set.Ici 0`. -/
/-
**strictAnti_of_odd_strictAntiOn_nonneg** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：strictAnti_of_odd_strictAntiOn_nonneg {f : G -> H} (h₁ : forall x, f (-x) 
= -f x) (h₂ : StrictAntiOn f (Ici 0)) : StrictAnti f
参数：h₁ : forall x, f (-x) = -f x；h₂ : StrictAntiOn f (Ici 0)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `strictMono_of_odd_strictMonoOn_nonneg`：strictMono_of_odd_strictMonoOn_no
nneg {f : G -> H} (h₁ : forall x, f (-x) = -f x) (h₂ : StrictMonoOn f (Ici 0)) :
 StrictMono f
· 使用定理 `OrderDual.isOrderedAddMonoid`：∀ {α : Type u} [inst : AddCommMonoid α] [i
nst_1 : Preorder α] [IsOrderedAddMonoid α], IsOrderedAddMonoid αᵒᵈ

--- 原说明 ---
An odd function on a linear ordered additive commutative group is strictly antit
one on the whole
group provided that it is strictly antitone on `Set.Ici 0`.
-/
theorem strictAnti_of_odd_strictAntiOn_nonneg {f : G → H} (h₁ : ∀ x, f (-x) = -f x)
    (h₂ : StrictAntiOn f (Ici 0)) : StrictAnti f :=
  strictMono_of_odd_strictMonoOn_nonneg (H := Hᵒᵈ) h₁ h₂

/-- An odd function on a linear ordered additive commutative group is monotone on the whole group
provided that it is monotone on `Set.Ici 0`. -/
/-
**monotone_of_odd_of_monotoneOn_nonneg** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：monotone_of_odd_of_monotoneOn_nonneg {f : G -> H} (h₁ : forall x, f (-x) =
 -f x) (h₂ : MonotoneOn f (Ici 0)) : Monotone f
参数：h₁ : forall x, f (-x) = -f x；h₂ : MonotoneOn f (Ici 0)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MonotoneOn.Iic_union_Ici`：∀ {α : Type u_1} {β : Type u_2} [inst : Linear
Order α] [inst_1 : Preorder β] {a : α} {f : α → β},   MonotoneOn f (Set.Iic a) →
 MonotoneOn f …
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `neg_le_neg_iff`：∀ {α : Type u} [inst : AddGroup α] [inst_1 : LE α] [AddL
eftMono α] {a b : α} [AddRightMono α], -a ≤ -b ↔ b ≤ a
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `neg_nonneg`：∀ {α : Type u} [inst : AddGroup α] [inst_1 : LE α] [AddLeftM
ono α] {a : α}, 0 ≤ -a ↔ a ≤ 0
· 使用定理 `neg_le_neg`：∀ {α : Type u} [inst : AddCommGroup α] [inst_1 : PartialOrde
r α] [IsOrderedAddMonoid α] {a b : α}, a ≤ b → -b ≤ -a

--- 原说明 ---
An odd function on a linear ordered additive commutative group is monotone on th
e whole group
provided that it is monotone on `Set.Ici 0`.
-/
theorem monotone_of_odd_of_monotoneOn_nonneg {f : G → H} (h₁ : ∀ x, f (-x) = -f x)
    (h₂ : MonotoneOn f (Ici 0)) : Monotone f := by
  refine MonotoneOn.Iic_union_Ici (fun x hx y hy hxy => neg_le_neg_iff.1 ?_) h₂
  rw [← h₁, ← h₁]
  exact h₂ (neg_nonneg.2 hy) (neg_nonneg.2 hx) (neg_le_neg hxy)

/-- An odd function on a linear ordered additive commutative group is antitone on the whole group
provided that it is monotone on `Set.Ici 0`. -/
/-
**antitone_of_odd_of_monotoneOn_nonneg** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：antitone_of_odd_of_monotoneOn_nonneg {f : G -> H} (h₁ : forall x, f (-x) =
 -f x) (h₂ : AntitoneOn f (Ici 0)) : Antitone f
参数：h₁ : forall x, f (-x) = -f x；h₂ : AntitoneOn f (Ici 0)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `monotone_of_odd_of_monotoneOn_nonneg`：monotone_of_odd_of_monotoneOn_nonn
eg {f : G -> H} (h₁ : forall x, f (-x) = -f x) (h₂ : MonotoneOn f (Ici 0)) : Mon
otone f
· 使用定理 `OrderDual.isOrderedAddMonoid`：∀ {α : Type u} [inst : AddCommMonoid α] [i
nst_1 : Preorder α] [IsOrderedAddMonoid α], IsOrderedAddMonoid αᵒᵈ

--- 原说明 ---
An odd function on a linear ordered additive commutative group is antitone on th
e whole group
provided that it is monotone on `Set.Ici 0`.
-/
theorem antitone_of_odd_of_monotoneOn_nonneg {f : G → H} (h₁ : ∀ x, f (-x) = -f x)
    (h₂ : AntitoneOn f (Ici 0)) : Antitone f :=
  monotone_of_odd_of_monotoneOn_nonneg (H := Hᵒᵈ) h₁ h₂
