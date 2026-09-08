/-
Copyright (c) 2022 Yaël Dillies, Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Bhavik Mehta
-/
module

public import Mathlib.Algebra.Order.Ring.Nat
public import Mathlib.Data.Set.Equitable
public import Mathlib.Logic.Equiv.Fin.Basic
public import Mathlib.Order.Partition.Finpartition
public import Mathlib.Tactic.ApplyFun

/-!
# Finite equipartitions

This file defines finite equipartitions, the partitions whose parts all are the same size up to a
difference of `1`.

## Main declarations

* `Finpartition.IsEquipartition`: Predicate for a `Finpartition` to be an equipartition.
* `Finpartition.IsEquipartition.exists_partPreservingEquiv`: part-preserving enumeration of a finset
  equipped with an equipartition. Indices of elements in the same part are congruent modulo
  the number of parts.
-/

@[expose] public section


open Finset Fintype

namespace Finpartition

variable {α : Type*} [DecidableEq α] {s t : Finset α} (P : Finpartition s)

/-- An equipartition is a partition whose parts are all the same size, up to a difference of `1`. -/
/-
**Finpartition.IsEquipartition** 是 Mathlib 中的一个定义，位于命名空间 `Finpartition`。
形式化陈述：IsEquipartition : Prop
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An equipartition is a partition whose parts are all the same size, up to a diffe
rence of `1`.
-/
def IsEquipartition : Prop :=
  (P.parts : Set (Finset α)).EquitableOn card
/-
**Finpartition.isEquipartition_iff_card_parts_eq_average** 是 Mathlib 中的一个定理，位于命名
空间 `Finpartition`。
形式化陈述：isEquipartition_iff_card_parts_eq_average : P.IsEquipartition ↔ forall a :
 Finset α, a in P.parts -> #a = #s / #P.parts ∨ #a = #s / #P.parts + 1
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Finpartition.sum_card_parts`：sum_card_parts : ∑ i in P.parts, #i = #s
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem isEquipartition_iff_card_parts_eq_average :
    P.IsEquipartition ↔
      ∀ a : Finset α, a ∈ P.parts → #a = #s / #P.parts ∨ #a = #s / #P.parts + 1 := by
  simp_rw [IsEquipartition, Finset.equitableOn_iff, P.sum_card_parts]

variable {P}
/-
**Finpartition.not_isEquipartition** 是 Mathlib 中的一个引理，位于命名空间 `Finpartition`。
形式化陈述：not_isEquipartition : ¬P.IsEquipartition ↔ exists a in P.parts, exists b i
n P.parts, #b + 1 < #a
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Set.not_equitableOn`：not_equitableOn : ¬s.EquitableOn f ↔ exists a in s,
 exists b in s, f b + 1 < f a
-/
lemma not_isEquipartition :
    ¬P.IsEquipartition ↔ ∃ a ∈ P.parts, ∃ b ∈ P.parts, #b + 1 < #a := Set.not_equitableOn
/-
**Finpartition._root_.Set.Subsingleton.isEquipartition** 是 Mathlib 中的一个定理，位于命名空间
 `Finpartition`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.Set.Subsingleton.isEquipartition (h : (P.parts : Set (Finset α)).Subsingleton) :
    P.IsEquipartition :=
  Set.Subsingleton.equitableOn h _
/-
**Finpartition.IsEquipartition.card_parts_eq_average** 是 Mathlib 中的一个定理，位于命名空间 `
Finpartition.IsEquipartition`。
形式化陈述：∀ {α : Type u_1} [inst : DecidableEq α] {s t : Finset α} {P : Finpartition
 s},   P.IsEquipartition → t ∈ P.parts → t.card = s.card / P.parts.card ∨ t.card
 = s.card / P.parts.card + 1
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Finpartition.isEquipartition_iff_card_parts_eq_average`：isEquipartition_
iff_card_parts_eq_average : P.IsEquipartition ↔ forall a : Finset α, a in P.part
s -> #a = #s / #P.parts ∨ #a = #s / #P.parts…
-/
theorem IsEquipartition.card_parts_eq_average (hP : P.IsEquipartition) (ht : t ∈ P.parts) :
    #t = #s / #P.parts ∨ #t = #s / #P.parts + 1 :=
  P.isEquipartition_iff_card_parts_eq_average.1 hP _ ht
/-
**Finpartition.IsEquipartition.card_part_eq_average_iff** 是 Mathlib 中的一个定理，位于命名空
间 `Finpartition.IsEquipartition`。
形式化陈述：∀ {α : Type u_1} [inst : DecidableEq α] {s t : Finset α} {P : Finpartition
 s},   P.IsEquipartition → t ∈ P.parts → (t.card = s.card / P.parts.card ↔ t.car
d ≠ s.card / P.parts.card + 1)
参数：t.card = s.card / P.parts.card ↔ t.card ≠ s.card / P.parts.card + 1。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finpartition.IsEquipartition.card_parts_eq_average`：∀ {α : Type u_1} [in
st : DecidableEq α] {s t : Finset α} {P : Finpartition s},   P.IsEquipartition →
 t ∈ P.parts → t.card = s.card / P.parts…
-/
theorem IsEquipartition.card_part_eq_average_iff (hP : P.IsEquipartition) (ht : t ∈ P.parts) :
    #t = #s / #P.parts ↔ #t ≠ #s / #P.parts + 1 := by
  have a := hP.card_parts_eq_average ht
  lia
/-
**Finpartition.IsEquipartition.average_le_card_part** 是 Mathlib 中的一个定理，位于命名空间 `F
inpartition.IsEquipartition`。
形式化陈述：∀ {α : Type u_1} [inst : DecidableEq α] {s t : Finset α} {P : Finpartition
 s},   P.IsEquipartition → t ∈ P.parts → s.card / P.parts.card ≤ t.card
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finpartition.sum_card_parts`：sum_card_parts : ∑ i in P.parts, #i = #s
· 使用定理 `Finset.EquitableOn.le`：∀ {α : Type u_1} {s : Finset α} {f : α → ℕ} {a : 
α}, (↑s).EquitableOn f → a ∈ s → (∑ i ∈ s, f i) / s.card ≤ f a
-/
theorem IsEquipartition.average_le_card_part (hP : P.IsEquipartition) (ht : t ∈ P.parts) :
    #s / #P.parts ≤ #t := by
  rw [← P.sum_card_parts]
  exact Finset.EquitableOn.le hP ht
/-
**Finpartition.IsEquipartition.card_part_le_average_add_one** 是 Mathlib 中的一个定理，位
于命名空间 `Finpartition.IsEquipartition`。
形式化陈述：∀ {α : Type u_1} [inst : DecidableEq α] {s t : Finset α} {P : Finpartition
 s},   P.IsEquipartition → t ∈ P.parts → t.card ≤ s.card / P.parts.card + 1
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finpartition.sum_card_parts`：sum_card_parts : ∑ i in P.parts, #i = #s
· 使用定理 `Finset.EquitableOn.le_add_one`：∀ {α : Type u_1} {s : Finset α} {f : α → 
ℕ} {a : α}, (↑s).EquitableOn f → a ∈ s → f a ≤ (∑ i ∈ s, f i) / s.card + 1
-/
theorem IsEquipartition.card_part_le_average_add_one (hP : P.IsEquipartition) (ht : t ∈ P.parts) :
    #t ≤ #s / #P.parts + 1 := by
  rw [← P.sum_card_parts]
  exact Finset.EquitableOn.le_add_one hP ht
/-
**Finpartition.IsEquipartition.filter_ne_average_add_one_eq_average** 是 Mathlib 
中的一个定理，位于命名空间 `Finpartition.IsEquipartition`。
形式化陈述：∀ {α : Type u_1} [inst : DecidableEq α] {s : Finset α} {P : Finpartition s
},   P.IsEquipartition →     {p ∈ P.parts | ¬p.card = s.card / P.parts.card + 1}
 = {p ∈ P.parts | p.card = s.card / P.parts.card}
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.ext`：ext {s₁ s₂ : Finset α} (h : forall a, a in s₁ ↔ a in s₂) : s
₁ = s₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用定理 `Finpartition.IsEquipartition.card_part_eq_average_iff`：∀ {α : Type u_1} 
[inst : DecidableEq α] {s t : Finset α} {P : Finpartition s},   P.IsEquipartitio
n → t ∈ P.parts → (t.card = s.card / P.part…
-/
theorem IsEquipartition.filter_ne_average_add_one_eq_average (hP : P.IsEquipartition) :
    {p ∈ P.parts | ¬#p = #s / #P.parts + 1} = {p ∈ P.parts | #p = #s / #P.parts} := by
  ext p
  simp only [mem_filter, and_congr_right_iff]
  exact fun hp ↦ (hP.card_part_eq_average_iff hp).symm

/-- An equipartition of a finset with `n` elements into `k` parts has
`n % k` parts of size `n / k + 1`. -/
/-
**Finpartition.IsEquipartition.card_large_parts_eq_mod** 是 Mathlib 中的一个定理，位于命名空间
 `Finpartition.IsEquipartition`。
形式化陈述：∀ {α : Type u_1} [inst : DecidableEq α] {s : Finset α} {P : Finpartition s
},   P.IsEquipartition → {p ∈ P.parts | p.card = s.card / P.parts.card + 1}.card
 = s.card % P.parts.card
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finpartition.sum_card_parts`：sum_card_parts : ∑ i in P.parts, #i = #s
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `add_left_inj`：∀ {G : Type u_1} [inst : Add G] [IsRightCancelAdd G] (a : 
G) {b c : G}, b + a = c + a ↔ b = c
· 使用定理 `instIsRightCancelAddOfAddRightReflectLE`：∀ {α : Type u_1} [inst : Add α]
 [inst_1 : PartialOrder α] [AddRightReflectLE α], IsRightCancelAdd α
· 使用定理 `addRightReflectLE_of_addLeftReflectLE`：∀ (N : Type u_2) [inst : AddCommS
emigroup N] [inst_1 : LE N] [AddLeftReflectLE N], AddRightReflectLE N
· 使用定理 `IsLeftCancelAdd.addLeftReflectLE_of_addLeftReflectLT`：∀ (N : Type u_2) [
inst : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftReflectLT N]
, AddLeftReflectLE N
· 使用定理 `AddLeftCancelSemigroup.toIsLeftCancelAdd`：∀ {G : Type u} [self : AddLeft
CancelSemigroup G], IsLeftCancelAdd G
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `Nat.mod_add_div`：∀ (m k : ℕ), m % k + k * (m / k) = m
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
· 使用定理 `Finset.card_filter_add_card_filter_not`：card_filter_add_card_filter_not 
(p : α -> Prop) [DecidablePred p] [forall x, Decidable (¬p x)] : #(s.filter p) +
 #(s.filter fun a => ¬ p a) …
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `add_mul`：add_mul {d : R} (_ : (a₁ : R) * b = c₁) (_ : a₂ * b = c₂) (_ : 
c₁ + c₂ = d) : (a₁ + a₂) * b = d
· 使用定理 `Distrib.rightDistribClass`：∀ (R : Type u_1) [inst : Distrib R], RightDis
tribClass R
· 使用定理 `add_assoc`：∀ {G : Type u_1} [inst : AddSemigroup G] (a b c : G), a + b +
 c = a + (b + c)
· 使用定理 `mul_add`：mul_add {d : R} (_ : (a : R) * b₁ = c₁) (_ : a * b₂ = c₂) (_ : 
c₁ + 0 + c₂ = d) : a * (b₁ + b₂) = d
· 使用定理 `Distrib.leftDistribClass`：∀ (R : Type u_1) [inst : Distrib R], LeftDistr
ibClass R
· 使用定理 `Finpartition.IsEquipartition.filter_ne_average_add_one_eq_average`：∀ {α 
: Type u_1} [inst : DecidableEq α] {s : Finset α} {P : Finpartition s},   P.IsEq
uipartition →     {p ∈ P.parts | ¬p.card = s.card / P.p…
· 使用定理 `Finset.sum_const_nat`：sum_const_nat {m : Nat} {f : ι -> Nat} (h₁ : foral
l x in s, f x = m) : ∑ x in s, f x = #s * m
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `Finset.sum_filter_add_sum_filter_not`：∀ {ι : Type u_1} {M : Type u_4} [i
nst : AddCommMonoid M] (s : Finset ι) (p : ι → Prop) [inst_1 : DecidablePred p] 
  [inst_2 : (x : ι) → Deci…

--- 原说明 ---
An equipartition of a finset with `n` elements into `k` parts has
`n % k` parts of size `n / k + 1`.
-/
theorem IsEquipartition.card_large_parts_eq_mod (hP : P.IsEquipartition) :
    #{p ∈ P.parts | #p = #s / #P.parts + 1} = #s % #P.parts := by
  have z := P.sum_card_parts
  rw [← sum_filter_add_sum_filter_not (s := P.parts) (p := fun x ↦ #x = #s / #P.parts + 1),
    hP.filter_ne_average_add_one_eq_average, sum_const_nat (m := #s / #P.parts + 1) (by simp),
    sum_const_nat (m := #s / #P.parts) (by simp), ← hP.filter_ne_average_add_one_eq_average,
    mul_add, add_comm, ← add_assoc, ← add_mul, mul_one, add_comm #_,
    card_filter_add_card_filter_not, add_comm] at z
  rw [← add_left_inj, Nat.mod_add_div, z]

/-- An equipartition of a finset with `n` elements into `k` parts has
`n - n % k` parts of size `n / k`. -/
/-
**Finpartition.IsEquipartition.card_small_parts_eq_mod** 是 Mathlib 中的一个定理，位于命名空间
 `Finpartition.IsEquipartition`。
形式化陈述：∀ {α : Type u_1} [inst : DecidableEq α] {s : Finset α} {P : Finpartition s
},   P.IsEquipartition → {p ∈ P.parts | p.card = s.card / P.parts.card}.card = P
.parts.card - s.card % P.parts.card
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.card_filter_add_card_filter_not`：card_filter_add_card_filter_not 
(p : α -> Prop) [DecidablePred p] [forall x, Decidable (¬p x)] : #(s.filter p) +
 #(s.filter fun a => ¬ p a) …
· 使用定理 `Finpartition.IsEquipartition.card_large_parts_eq_mod`：∀ {α : Type u_1} [
inst : DecidableEq α] {s : Finset α} {P : Finpartition s},   P.IsEquipartition →
 {p ∈ P.parts | p.card = s.card / P.parts.…
· 使用定理 `add_tsub_cancel_left`：add_tsub_cancel_left (a b : α) : a + b - a = b
· 使用定理 `IsLeftCancelAdd.addLeftReflectLE_of_addLeftReflectLT`：∀ (N : Type u_2) [
inst : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftReflectLT N]
, AddLeftReflectLE N
· 使用定理 `AddLeftCancelSemigroup.toIsLeftCancelAdd`：∀ {G : Type u} [self : AddLeft
CancelSemigroup G], IsLeftCancelAdd G
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `Finpartition.IsEquipartition.filter_ne_average_add_one_eq_average`：∀ {α 
: Type u_1} [inst : DecidableEq α] {s : Finset α} {P : Finpartition s},   P.IsEq
uipartition →     {p ∈ P.parts | ¬p.card = s.card / P.p…

--- 原说明 ---
An equipartition of a finset with `n` elements into `k` parts has
`n - n % k` parts of size `n / k`.
-/
theorem IsEquipartition.card_small_parts_eq_mod (hP : P.IsEquipartition) :
    #{p ∈ P.parts | #p = #s / #P.parts} = #P.parts - #s % #P.parts := by
  conv_rhs =>
    arg 1
    rw [← card_filter_add_card_filter_not (p := fun p ↦ #p = #s / #P.parts + 1)]
  rw [hP.card_large_parts_eq_mod, add_tsub_cancel_left, hP.filter_ne_average_add_one_eq_average]

/-- There exists an enumeration of an equipartition's parts where
larger parts map to smaller numbers and vice versa. -/
/-
**Finpartition.IsEquipartition.exists_partsEquiv** 是 Mathlib 中的一个定理，位于命名空间 `Finp
artition.IsEquipartition`。
形式化陈述：∀ {α : Type u_1} [inst : DecidableEq α] {s : Finset α} {P : Finpartition s
},   P.IsEquipartition → ∃ f, ∀ (t : ↥P.parts), (↑t).card = s.card / P.parts.car
d + 1 ↔ ↑(f t) < s.card % P.parts.card
参数：t : ↥P.parts；↑t；f t。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.refl`：Equiv.refl (s : Computation α) : s ~ s
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finpartition.IsEquipartition.card_part_eq_average_iff`：∀ {α : Type u_1} 
[inst : DecidableEq α] {s t : Finset α} {P : Finpartition s},   P.IsEquipartitio
n → t ∈ P.parts → (t.card = s.card / P.part…
· 使用定理 `ne_eq`：∀ {α : Sort u_1} (a b : α), (a ≠ b) = ¬a = b
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
· 使用定理 `Equiv.trans`：Equiv.trans {s t u : Computation α} : s ~ t -> t ~ u -> s ~
 u
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `Finpartition.IsEquipartition.card_large_parts_eq_mod`：∀ {α : Type u_1} [
inst : DecidableEq α] {s : Finset α} {P : Finpartition s},   P.IsEquipartition →
 {p ∈ P.parts | p.card = s.card / P.parts.…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Finpartition.IsEquipartition.card_small_parts_eq_mod`：∀ {α : Type u_1} [
inst : DecidableEq α] {s : Finset α} {P : Finpartition s},   P.IsEquipartition →
 {p ∈ P.parts | p.card = s.card / P.parts.…
· 使用定理 `Nat.add_sub_of_le`：∀ {a b : ℕ}, a ≤ b → a + (b - a) = b
· 使用引理 `Finpartition.card_mod_card_parts_le`：card_mod_card_parts_le : #s % #P.pa
rts <= #P.parts
· 使用定理 `Equiv.sumCongr_apply`：∀ {α₁ : Type u_9} {α₂ : Type u_10} {β₁ : Type u_11
} {β₂ : Type u_12} (ea : α₁ ≃ α₂) (eb : β₁ ≃ β₂) (a : α₁ ⊕ β₁),   (ea.sumCongr e
b) a = Sum…
· 使用定理 `finCongr_apply`：∀ {n m : ℕ} (eq : n = m) (i : Fin n), (finCongr eq) i = 
Fin.cast eq i
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Equiv.sumCompl_symm_apply_of_pos`：sumCompl_symm_apply_of_pos {α} {p : α 
-> Prop} [DecidablePred p] {a : α} (h : p a) : (sumCompl p).symm a = Sum.inl ⟨a,
 h⟩
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `Equiv.sumCompl_symm_apply_of_neg`：sumCompl_symm_apply_of_neg {α} {p : α 
-> Prop} [DecidablePred p] {a : α} (h : ¬p a) : (sumCompl p).symm a = Sum.inr ⟨a
, h⟩
· 使用定理 `IsLeftCancelAdd.addLeftStrictMono_of_addLeftMono`：∀ (N : Type u_2) [inst
 : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftMono N], AddLeft
StrictMono N
· 使用定理 `instIsLeftCancelAddOfAddLeftReflectLE`：∀ {α : Type u_1} [inst : Add α] [
inst_1 : PartialOrder α] [AddLeftReflectLE α], IsLeftCancelAdd α
· 使用定理 `IsOrderedCancelAddMonoid.toAddLeftReflectLE`：∀ {α : Type u_2} [inst : Ad
dCommMonoid α] [inst_1 : Preorder α] [IsOrderedCancelAddMonoid α], AddLeftReflec
tLE α
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `LinearOrderedCommMonoidWithZero.toIsBotZeroClass`：∀ {α : Type u_3} [self
 : LinearOrderedCommMonoidWithZero α], IsBotZeroClass α

--- 原说明 ---
There exists an enumeration of an equipartition's parts where
larger parts map to smaller numbers and vice versa.
-/
theorem IsEquipartition.exists_partsEquiv (hP : P.IsEquipartition) :
    ∃ f : P.parts ≃ Fin #P.parts, ∀ t, #t.1 = #s / #P.parts + 1 ↔ f t < #s % #P.parts := by
  let el := {p ∈ P.parts | #p = #s / #P.parts + 1}.equivFin
  let es := {p ∈ P.parts | #p = #s / #P.parts}.equivFin
  simp_rw [mem_filter, hP.card_large_parts_eq_mod] at el
  simp_rw [mem_filter, hP.card_small_parts_eq_mod] at es
  let sneg :
      {x // x ∈ P.parts ∧ ¬#x = #s / #P.parts + 1} ≃ {x // x ∈ P.parts ∧ #x = #s / #P.parts} := by
    apply (Equiv.refl _).subtypeEquiv
    simp only [Equiv.refl_apply, and_congr_right_iff]
    exact fun _ ha ↦ by rw [hP.card_part_eq_average_iff ha, ne_eq]
  replace el : { x : P.parts // #x.1 = #s / #P.parts + 1 } ≃
      Fin (#s % #P.parts) := (Equiv.Set.sep ..).symm.trans el
  replace es : { x : P.parts // ¬#x.1 = #s / #P.parts + 1 } ≃
      Fin (#P.parts - #s % #P.parts) := (Equiv.Set.sep ..).symm.trans (sneg.trans es)
  let f := (Equiv.sumCompl _).symm.trans ((el.sumCongr es).trans finSumFinEquiv)
  use f.trans (finCongr (Nat.add_sub_of_le P.card_mod_card_parts_le))
  intro ⟨p, _⟩
  simp_rw [f, Equiv.trans_apply, Equiv.sumCongr_apply, finCongr_apply, Fin.val_cast]
  by_cases hc : #p = #s / #P.parts + 1 <;> simp [hc]

/-- Given a finset equipartitioned into `k` parts, its elements can be enumerated such that
elements in the same part have congruent indices modulo `k`. -/
/-
**Finpartition.IsEquipartition.exists_partPreservingEquiv** 是 Mathlib 中的一个定理，位于命
名空间 `Finpartition.IsEquipartition`。
形式化陈述：∀ {α : Type u_1} [inst : DecidableEq α] {s : Finset α} {P : Finpartition s
},   P.IsEquipartition → ∃ f, ∀ (a b : ↥s), P.part ↑a = P.part ↑b ↔ ↑(f a) % P.p
arts.card = ↑(f b) % P.parts.card
参数：a b : ↥s；f a；f b。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Finpartition.exists_enumeration`：exists_enumeration : exists f : s ≃ Σ t
 : P.parts, Fin #t.1, forall a b : s, P.part a = P.part b ↔ (f a).1 = (f b).1
· 使用定理 `Finpartition.IsEquipartition.exists_partsEquiv`：∀ {α : Type u_1} [inst :
 DecidableEq α] {s : Finset α} {P : Finpartition s},   P.IsEquipartition → ∃ f, 
∀ (t : ↥P.parts), (↑t).card = s.card…
· 使用定理 `Fin.isLt`：∀ {n : ℕ} (self : Fin n), ↑self < n
· 使用定理 `Finpartition.IsEquipartition.card_parts_eq_average`：∀ {α : Type u_1} [in
st : DecidableEq α] {s t : Finset α} {P : Finpartition s},   P.IsEquipartition →
 t ∈ P.parts → t.card = s.card / P.parts…
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mul_add_one`：mul_add_one [LeftDistribClass α] (a b : α) : a * (b + 1) = 
a * b + a
· 使用定理 `Distrib.leftDistribClass`：∀ (R : Type u_1) [inst : Distrib R], LeftDistr
ibClass R
· 使用定理 `add_lt_add_right`：∀ {α : Type u_1} [inst : Add α] [inst_1 : LT α] [AddLe
ftStrictMono α] {b c : α}, b < c → ∀ (a : α), a + b < a + c
· 使用定理 `IsLeftCancelAdd.addLeftStrictMono_of_addLeftMono`：∀ (N : Type u_2) [inst
 : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftMono N], AddLeft
StrictMono N
· 使用定理 `instIsLeftCancelAddOfAddLeftReflectLE`：∀ {α : Type u_1} [inst : Add α] [
inst_1 : PartialOrder α] [AddLeftReflectLE α], IsLeftCancelAdd α
· 使用定理 `IsOrderedCancelAddMonoid.toAddLeftReflectLE`：∀ {α : Type u_2} [inst : Ad
dCommMonoid α] [inst_1 : Preorder α] [IsOrderedCancelAddMonoid α], AddLeftReflec
tLE α
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `mul_le_mul'`：mul_le_mul' [MulLeftMono α] [MulRightMono α] {a b c d : α} 
(h₁ : a <= b) (h₂ : c <= d) : a * c <= b * d
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `Nat.le_add_right`：∀ (n k : ℕ), n ≤ n + k
· 使用定理 `Nat.div_add_mod`：∀ (m n : ℕ), n * (m / n) + m % n = m
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `add_lt_add_of_le_of_lt`：∀ {α : Type u_1} [inst : Add α] [inst_1 : Preord
er α] [AddLeftStrictMono α] [AddRightMono α] {a b c d : α},   a ≤ b → c < d → a 
+ c < b + d
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `mul_le_mul_right`：mul_le_mul_right [MulLeftMono α] {b c : α} (bc : b <= 
c) (a : α) : a * b <= a * c
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Fintype.bijective_iff_injective_and_card`：bijective_iff_injective_and_ca
rd (f : α -> β) : Bijective f ↔ Injective f ∧ card α = card β
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `LE.le.trans_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b 
→ b < c → a < c
· 使用定理 `Nat.zero_le`：∀ (n : ℕ), 0 ≤ n
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `Equiv.injective`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β), Function.Injec
tive ⇑e
· 使用定理 `Sigma.ext`：∀ {α : Type u} {β : α → Type v} {x y : Sigma β}, x.fst = y.fs
t → x.snd ≍ y.snd → x = y
（共 48 条，此处仅展示前 30 条）

--- 原说明 ---
Given a finset equipartitioned into `k` parts, its elements can be enumerated su
ch that
elements in the same part have congruent indices modulo `k`.
-/
theorem IsEquipartition.exists_partPreservingEquiv (hP : P.IsEquipartition) : ∃ f : s ≃ Fin #s,
    ∀ a b : s, P.part a = P.part b ↔ f a % #P.parts = f b % #P.parts := by
  obtain ⟨f, hf⟩ := P.exists_enumeration
  obtain ⟨g, hg⟩ := hP.exists_partsEquiv
  let z := fun a ↦ #P.parts * (f a).2 + g (f a).1
  have gl := fun a ↦ (g (f a).1).2
  have less : ∀ a, z a < #s := fun a ↦ by
    rcases hP.card_parts_eq_average (f a).1.2 with (c | c)
    · calc
        _ < #P.parts * ((f a).2 + 1) := by simp only [z, mul_add_one]; gcongr; exact gl a
        _ ≤ #P.parts * (#s / #P.parts) := by gcongr; exact c ▸ (f a).2.2
        _ ≤ #P.parts * (#s / #P.parts) + #s % #P.parts := Nat.le_add_right ..
        _ = _ := Nat.div_add_mod ..
    · rw [← Nat.div_add_mod #s #P.parts]
      exact add_lt_add_of_le_of_lt (mul_le_mul_right (by lia) _) ((hg (f a).1).mp c)
  let z' : s → Fin #s := fun a ↦ ⟨z a, less a⟩
  have bij : z'.Bijective := by
    refine (bijective_iff_injective_and_card z').mpr ⟨fun a b e ↦ ?_, by simp⟩
    simp_rw [z', z, Fin.mk.injEq, mul_comm #P.parts] at e
    have : NeZero #P.parts := ⟨((Nat.zero_le _).trans_lt (gl a)).ne'⟩
    change (#P.parts).divModEquiv.symm (_, _) = (#P.parts).divModEquiv.symm (_, _) at e
    simp only [Equiv.apply_eq_iff_eq, Prod.mk.injEq] at e
    apply_fun f
    exact Sigma.ext e.2 <| (Fin.heq_ext_iff (by rw [e.2])).mpr e.1
  use Equiv.ofBijective _ bij
  intro a b
  simp_rw [z', z, Equiv.ofBijective_apply, hf a b, Nat.mul_add_mod,
    Nat.mod_eq_of_lt (gl a), Nat.mod_eq_of_lt (gl b), Fin.val_eq_val, g.apply_eq_iff_eq]

/-! ### Discrete and indiscrete finpartitions -/


variable (s)

/-
**Finpartition.bot_isEquipartition** 是 Mathlib 中的一个定理，位于命名空间 `Finpartition`。
形式化陈述：bot_isEquipartition : (⊥ : Finpartition s).IsEquipartition
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.equitableOn_iff_exists_eq_eq_add_one`：equitableOn_iff_exists_eq_eq_a
dd_one {s : Set α} {f : α -> Nat} : s.EquitableOn f ↔ exists b, forall a in s, f
 a = b ∨ f a = b + 1
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.singleton_injective`：singleton_injective : Injective (singleton :
 α -> Finset α)
· 使用定理 `Finset.coe_map`：coe_map (f : α ↪ β) (s : Finset α) : (s.map f : Set β) =
 f '' s
· 使用定理 `Set.image_congr`：image_congr {f g : α -> β} {s : Set α} (h : forall a in
 s, f a = g a) : f '' s = g '' s
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Finset.card_singleton`：card_singleton (a : α) : #{a} = 1
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `or_false`：∀ (p : Prop), (p ∨ False) = p
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
theorem bot_isEquipartition : (⊥ : Finpartition s).IsEquipartition :=
  Set.equitableOn_iff_exists_eq_eq_add_one.2 ⟨1, by simp⟩
/-
**Finpartition.top_isEquipartition** 是 Mathlib 中的一个定理，位于命名空间 `Finpartition`。
形式化陈述：top_isEquipartition [Decidable (s = ∅)] : (⊤ : Finpartition s).IsEquiparti
tion
参数：s = ∅。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.Subsingleton.isEquipartition`：∀ {α : Type u_1} [inst : DecidableEq α
] {s : Finset α} {P : Finpartition s}, (↑P.parts).Subsingleton → P.IsEquipartiti
on
· 使用定理 `Finpartition.parts_top_subsingleton`：parts_top_subsingleton (a : α) [Dec
idable (a = ⊥)] : ((⊤ : Finpartition a).parts : Set α).Subsingleton
-/
theorem top_isEquipartition [Decidable (s = ∅)] : (⊤ : Finpartition s).IsEquipartition :=
  Set.Subsingleton.isEquipartition (parts_top_subsingleton _)
/-
**Finpartition.indiscrete_isEquipartition** 是 Mathlib 中的一个定理，位于命名空间 `Finpartitio
n`。
形式化陈述：indiscrete_isEquipartition {hs : s != ∅} : (indiscrete hs).IsEquipartition
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finpartition.IsEquipartition.eq_1`：∀ {α : Type u_1} [inst : DecidableEq 
α] {s : Finset α} (P : Finpartition s),   P.IsEquipartition = (↑P.parts).Equitab
leOn Finset.card
· 使用定理 `Finpartition.indiscrete_parts`：∀ {α : Type u_1} [inst : Lattice α] [inst
_1 : OrderBot α] {a : α} (ha : a ≠ ⊥), (Finpartition.indiscrete ha).parts = {a}
· 使用定理 `Finset.coe_singleton`：coe_singleton (a : α) : (({a} : Finset α) : Set α)
 = {a}
· 使用定理 `Set.equitableOn_singleton`：equitableOn_singleton (a : α) (f : α -> β) : 
Set.EquitableOn {a} f
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
-/
theorem indiscrete_isEquipartition {hs : s ≠ ∅} : (indiscrete hs).IsEquipartition := by
  rw [IsEquipartition, indiscrete_parts, coe_singleton]
  exact Set.equitableOn_singleton s _

end Finpartition

