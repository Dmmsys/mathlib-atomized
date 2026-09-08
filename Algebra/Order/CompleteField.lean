/-
Copyright (c) 2022 Alex J. Best. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex J. Best, Yaël Dillies
-/
module

public import Mathlib.Algebra.Order.Archimedean.Hom
public import Mathlib.Algebra.Order.Group.Pointwise.CompleteLattice

/-!
# Conditionally complete linear ordered fields

This file shows that the reals are unique, or, more formally, given a type satisfying the common
axioms of the reals (field, conditionally complete, linearly ordered) that there is an isomorphism
preserving these properties to the reals.
This is `ConditionallyCompleteLinearOrderedField.inducedOrderRingIso`.
Moreover this isomorphism is unique.

We show all conditionally complete linear ordered fields are
archimedean. We also construct the natural map from a linearly ordered field to such a field.

## Main definitions

* `ConditionallyCompleteLinearOrderedField.inducedMap`: A (unique) map from any archimedean linear
  ordered field to a conditionally complete linear ordered field. Various bundlings are available.

## Main results

* `ConditionallyCompleteLinearOrderedField.uniqueOrderRingHom` : Uniqueness of `OrderRingHom`s
  from an archimedean linear ordered field to a conditionally complete linear ordered field.
* `ConditionallyCompleteLinearOrderedField.uniqueOrderRingIso` : Uniqueness of `OrderRingIso`s
  between two conditionally complete linearly ordered fields.

## References

* https://mathoverflow.net/questions/362991/who-first-characterized-the-real-numbers-as-the-unique-complete-ordered-field

## Tags

reals, conditionally complete, ordered field, uniqueness
-/

@[expose] public section

variable {F α β γ : Type*}

noncomputable section

open Function Rat Set

open scoped Pointwise

/-- A field which is both linearly ordered and conditionally complete with respect to the order.
This axiomatizes the reals. -/
@[deprecated "Use `[Field α] [ConditionallyCompleteLinearOrder α] [IsStrictOrderedRing α]` instead."
  (since := "2026-02-23")]
/-
**ConditionallyCompleteLinearOrderedField** 是 Mathlib 中的一个结构，位于命名空间 ``。
形式化陈述：ConditionallyCompleteLinearOrderedField (α : Type*) extends Field α, Condi
tionallyCompleteLinearOrder α, IsStrictOrderedRing α where  -- see Note [lower i
nstance priority] /-- Any conditionally complete linearly ordered field is archi
medean. -/ scoped instance (priority
参数：α : Type*。
继承自：Field α, ConditionallyCompleteLinearOrder α, IsStrictOrderedRing α。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
structure ConditionallyCompleteLinearOrderedField (α : Type*) extends
    Field α, ConditionallyCompleteLinearOrder α, IsStrictOrderedRing α where

-- see Note [lower instance priority]
/-- Any conditionally complete linearly ordered field is archimedean. -/
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Any conditionally complete linearly ordered field is archimedean.
-/
scoped instance (priority := 100) ConditionallyCompleteLinearOrderedField.to_archimedean
    [Field α] [ConditionallyCompleteLinearOrder α] [IsStrictOrderedRing α] : Archimedean α :=
  archimedean_iff_nat_lt.2 <| by
    by_contra! ⟨x, h⟩
    have := csSup_le (range_nonempty Nat.cast)
      (forall_mem_range.2 fun m =>
        le_sub_iff_add_le.2 <| le_csSup ⟨x, forall_mem_range.2 h⟩ ⟨m+1, Nat.cast_succ m⟩)
    linarith

namespace LinearOrderedField

/-!
### Rational cut map

The idea is that a conditionally complete linear ordered field is fully characterized by its copy of
the rationals. Hence we define `LinearOrderedField.cutMap β : α → Set β` which sends `a : α` to the
"rationals in `β`" that are less than `a`.
-/


section CutMap

variable [Field α] [LinearOrder α]

section DivisionRing

variable (β) [DivisionRing β] {a a₁ a₂ : α} {b : β} {q : ℚ}

/-- The lower cut of rationals inside a linear ordered field that are less than a given element of
another linear ordered field. -/
/-
**LinearOrderedField.cutMap** 是 Mathlib 中的一个定义，位于命名空间 `LinearOrderedField`。
形式化陈述：cutMap (a : α) : Set β
参数：a : α。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The lower cut of rationals inside a linear ordered field that are less than a gi
ven element of
another linear ordered field.
-/
def cutMap (a : α) : Set β :=
  (Rat.cast : ℚ → β) '' {t | ↑t < a}
/-
**LinearOrderedField.cutMap_mono** 是 Mathlib 中的一个定理，位于命名空间 `LinearOrderedField`。
形式化陈述：cutMap_mono (h : a₁ <= a₂) : cutMap β a₁ subseteq cutMap β a₂
参数：h : a₁ <= a₂。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Set.image_mono`：image_mono (h : s subseteq t) : f '' s subseteq f '' t
· 使用定理 `LE.le.trans_lt'`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, b ≤ a
 → c < b → c < a
-/
theorem cutMap_mono (h : a₁ ≤ a₂) : cutMap β a₁ ⊆ cutMap β a₂ := image_mono fun _ => h.trans_lt'

variable {β}

@[simp]
/-
**LinearOrderedField.mem_cutMap_iff** 是 Mathlib 中的一个定理，位于命名空间 `LinearOrderedFiel
d`。
形式化陈述：mem_cutMap_iff : b in cutMap β a ↔ exists q : Rat, (q : α) < a ∧ (q : β) =
 b
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem mem_cutMap_iff : b ∈ cutMap β a ↔ ∃ q : ℚ, (q : α) < a ∧ (q : β) = b := Iff.rfl
/-
**LinearOrderedField.coe_mem_cutMap_iff** 是 Mathlib 中的一个定理，位于命名空间 `LinearOrdered
Field`。
形式化陈述：coe_mem_cutMap_iff [CharZero β] : (q : β) in cutMap β a ↔ (q : α) < a
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Injective.mem_set_image`：∀ {α : Type u_1} {β : Type u_2} {f : α
 → β}, Function.Injective f → ∀ {s : Set α} {a : α}, f a ∈ f '' s ↔ a ∈ s
· 使用引理 `Rat.cast_injective`：cast_injective : Injective ((↑) : Rat -> α) | ⟨n₁, d
₁, d₁0, c₁⟩, ⟨n₂, d₂, d₂0, c₂⟩, h => by have d₁a : (d₁ : α) != 0
-/
theorem coe_mem_cutMap_iff [CharZero β] : (q : β) ∈ cutMap β a ↔ (q : α) < a :=
  Rat.cast_injective.mem_set_image
/-
**LinearOrderedField.cutMap_self** 是 Mathlib 中的一个定理，位于命名空间 `LinearOrderedField`。
形式化陈述：cutMap_self (a : α) : cutMap α a = Iio a inter range (Rat.cast : Rat -> α)
参数：a : α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem cutMap_self (a : α) : cutMap α a = Iio a ∩ range (Rat.cast : ℚ → α) := by
  grind [mem_cutMap_iff]

end DivisionRing

variable (β) [IsStrictOrderedRing α] [Field β] [LinearOrder β] [IsStrictOrderedRing β]
  {a a₁ a₂ : α} {b : β} {q : ℚ}

/-
**LinearOrderedField.cutMap_coe** 是 Mathlib 中的一个定理，位于命名空间 `LinearOrderedField`。
形式化陈述：cutMap_coe (q : Rat) : cutMap β (q : α) = Rat.cast '' {r : Rat | (r : β) <
 q}
参数：q : Rat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem cutMap_coe (q : ℚ) : cutMap β (q : α) = Rat.cast '' {r : ℚ | (r : β) < q} := by
  simp_rw [cutMap, Rat.cast_lt]

variable [Archimedean α]

omit [LinearOrder β] [IsStrictOrderedRing β] in
/-
**LinearOrderedField.cutMap_nonempty** 是 Mathlib 中的一个定理，位于命名空间 `LinearOrderedFie
ld`。
形式化陈述：cutMap_nonempty (a : α) : (cutMap β a).Nonempty
参数：a : α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.Nonempty.image`：∀ {α : Type u_1} {β : Type u_2} (f : α → β) {s : Set
 α}, s.Nonempty → (f '' s).Nonempty
· 使用定理 `exists_rat_lt`：exists_rat_lt (x : K) : exists q : Rat, (q : K) < x
-/
theorem cutMap_nonempty (a : α) : (cutMap β a).Nonempty :=
  Nonempty.image _ <| exists_rat_lt a
/-
**LinearOrderedField.cutMap_bddAbove** 是 Mathlib 中的一个定理，位于命名空间 `LinearOrderedFie
ld`。
形式化陈述：cutMap_bddAbove (a : α) : BddAbove (cutMap β a)
参数：a : α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `exists_rat_gt`：exists_rat_gt (x : K) : exists q : Rat, x < q
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.forall_mem_image`：forall_mem_image {f : α -> β} {s : Set α} {p : β -
> Prop} : (forall y in f '' s, p y) ↔ forall ⦃x⦄, x in s -> p (f x)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `LT.lt.trans'`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, b < a → 
c < b → c < a
-/
theorem cutMap_bddAbove (a : α) : BddAbove (cutMap β a) := by
  obtain ⟨q, hq⟩ := exists_rat_gt a
  exact ⟨q, forall_mem_image.2 fun r hr => mod_cast (hq.trans' hr).le⟩
/-
**LinearOrderedField.cutMap_add** 是 Mathlib 中的一个定理，位于命名空间 `LinearOrderedField`。
形式化陈述：cutMap_add (a b : α) : cutMap β (a + b) = cutMap β a + cutMap β b
参数：a b : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.antisymm`：∀ {α : Type u_1} [inst : PartialOrder α] {a b : α}, a ≤ 
b → b ≤ a → a = b
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.image_subset_iff`：image_subset_iff {s : Set α} {t : Set β} {f : α ->
 β} : f '' s subseteq t ↔ s subseteq f ⁻¹' t
· 使用定理 `exists_rat_btwn`：exists_rat_btwn {x y : K} (h : x < y) : exists q : Rat,
 x < q ∧ q < y
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `sub_lt_iff_lt_add`：∀ {α : Type u} [inst : AddGroup α] [inst_1 : LT α] [A
ddRightStrictMono α] {a b c : α}, a - c < b ↔ a < b + c
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
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `IsOrderedRing.toIsOrderedAddMonoid`：∀ {R : Type u_1} {inst : Semiring R}
 {inst_1 : PartialOrder R} [self : IsOrderedRing R], IsOrderedAddMonoid R
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `Set.mem_ofPred_eq`：mem_ofPred_eq {x : α} {p : α -> Prop} : (x in {y | p 
y}) = p x
· 使用定理 `LinearOrderedField.coe_mem_cutMap_iff`：coe_mem_cutMap_iff [CharZero β] :
 (q : β) in cutMap β a ↔ (q : α) < a
· 使用定理 `IsStrictOrderedRing.toCharZero`：∀ {R : Type u} [inst : Semiring R] [inst
_1 : PartialOrder R] [IsStrictOrderedRing R], CharZero R
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `sub_lt_comm`：∀ {α : Type u} [inst : AddCommGroup α] [inst_1 : LT α] [Add
LeftStrictMono α] {a b c : α}, a - b < c ↔ a - c < b
· 使用定理 `IsLeftCancelAdd.addLeftStrictMono_of_addLeftMono`：∀ (N : Type u_2) [inst
 : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftMono N], AddLeft
StrictMono N
· 使用定理 `instIsLeftCancelAddOfAddLeftReflectLE`：∀ {α : Type u_1} [inst : Add α] [
inst_1 : PartialOrder α] [AddLeftReflectLE α], IsLeftCancelAdd α
· 使用定理 `AddGroup.addLeftReflectLE_of_addLeftMono`：∀ {N : Type u_2} [inst : AddGr
oup N] [inst_1 : LE N] [AddLeftMono N], AddLeftReflectLE N
· 使用定理 `add_sub_cancel`：∀ {G : Type u_3} [inst : AddCommGroup G] (a b : G), a + 
(b - a) = b
· 使用定理 `Rat.cast_add`：∀ {α : Type u_3} [inst : DivisionRing α] [CharZero α] (p q
 : ℚ), ↑(p + q) = ↑p + ↑q
· 使用定理 `add_lt_add`：∀ {α : Type u_1} [inst : Add α] [inst_1 : Preorder α] [AddLe
ftStrictMono α] [AddRightStrictMono α] {a b c d : α},   a < b → c < d → a + c < 
…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
-/
theorem cutMap_add (a b : α) : cutMap β (a + b) = cutMap β a + cutMap β b := by
  refine (image_subset_iff.2 fun q hq => ?_).antisymm ?_
  · rw [mem_ofPred_eq, ← sub_lt_iff_lt_add] at hq
    obtain ⟨q₁, hq₁q, hq₁ab⟩ := exists_rat_btwn hq
    refine ⟨q₁, by rwa [coe_mem_cutMap_iff], q - q₁, ?_, add_sub_cancel _ _⟩
    norm_cast
    rw [coe_mem_cutMap_iff]
    exact mod_cast sub_lt_comm.mp hq₁q
  · rintro _ ⟨_, ⟨qa, ha, rfl⟩, _, ⟨qb, hb, rfl⟩, rfl⟩
    -- After https://github.com/leanprover/lean4/pull/2734, `norm_cast` needs help with beta reduction.
    refine ⟨qa + qb, ?_, by beta_reduce; norm_cast⟩
    rw [mem_ofPred_eq, cast_add]
    exact add_lt_add ha hb

end CutMap

end LinearOrderedField

namespace ConditionallyCompleteLinearOrderedField

open LinearOrderedField

/-!
### Induced map

`LinearOrderedField.cutMap` spits out a `Set β`. To get something in `β`, we now take the supremum.
-/


section InducedMap

variable (α β γ) [Field α] [LinearOrder α] [IsStrictOrderedRing α]
  [Field β] [ConditionallyCompleteLinearOrder β] [IsStrictOrderedRing β]
  [Field γ] [ConditionallyCompleteLinearOrder γ] [IsStrictOrderedRing γ]

/-- The induced order-preserving function from a linear ordered field to a conditionally complete
linear ordered field, defined by taking the Sup in the codomain of all the rationals less than the
input. -/
/-
**ConditionallyCompleteLinearOrderedField.inducedMap** 是 Mathlib 中的一个定义，位于命名空间 `
ConditionallyCompleteLinearOrderedField`。
形式化陈述：inducedMap (x : α) : β
参数：x : α。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The induced order-preserving function from a linear ordered field to a condition
ally complete
linear ordered field, defined by taking the Sup in the codomain of all the ratio
nals less than the
input.
-/
def inducedMap (x : α) : β :=
  sSup <| cutMap β x

variable [Archimedean α]
/-
**ConditionallyCompleteLinearOrderedField.inducedMap_mono** 是 Mathlib 中的一个定理，位于命
名空间 `ConditionallyCompleteLinearOrderedField`。
形式化陈述：inducedMap_mono : Monotone (inducedMap α β)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `csSup_le_csSup`：csSup_le_csSup (ht : BddAbove t) (hs : s.Nonempty) (h : 
s subseteq t) : sSup s <= sSup t
· 使用定理 `LinearOrderedField.cutMap_bddAbove`：cutMap_bddAbove (a : α) : BddAbove (
cutMap β a)
· 使用定理 `LinearOrderedField.cutMap_nonempty`：cutMap_nonempty (a : α) : (cutMap β 
a).Nonempty
· 使用定理 `LinearOrderedField.cutMap_mono`：cutMap_mono (h : a₁ <= a₂) : cutMap β a₁
 subseteq cutMap β a₂
-/
theorem inducedMap_mono : Monotone (inducedMap α β) := fun _ _ h =>
  csSup_le_csSup (cutMap_bddAbove β _) (cutMap_nonempty β _) (cutMap_mono β h)
/-
**ConditionallyCompleteLinearOrderedField.inducedMap_rat** 是 Mathlib 中的一个定理，位于命名
空间 `ConditionallyCompleteLinearOrderedField`。
形式化陈述：inducedMap_rat (q : Rat) : inducedMap α β (q : α) = q
参数：q : Rat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `csSup_eq_of_forall_le_of_forall_lt_exists_gt`：csSup_eq_of_forall_le_of_f
orall_lt_exists_gt (hs : s.Nonempty) (H : forall a in s, a <= b) (H' : forall w,
 w < b -> exists a in s, w < a) : …
· 使用定理 `LinearOrderedField.cutMap_nonempty`：cutMap_nonempty (a : α) : (cutMap β 
a).Nonempty
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LinearOrderedField.cutMap_coe`：cutMap_coe (q : Rat) : cutMap β (q : α) =
 Rat.cast '' {r : Rat | (r : β) < q}
· 使用定理 `le_of_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `exists_rat_btwn`：exists_rat_btwn {x y : K} (h : x < y) : exists q : Rat,
 x < q ∧ q < y
· 使用定理 `ConditionallyCompleteLinearOrderedField.to_archimedean`：∀ {α : Type u_2}
 [inst : Field α] [inst_1 : ConditionallyCompleteLinearOrder α] [IsStrictOrdered
Ring α], Archimedean α
-/
theorem inducedMap_rat (q : ℚ) : inducedMap α β (q : α) = q := by
  refine csSup_eq_of_forall_le_of_forall_lt_exists_gt
    (cutMap_nonempty β (q : α)) (fun x h => ?_) fun w h => ?_
  · rw [cutMap_coe] at h
    obtain ⟨r, h, rfl⟩ := h
    exact le_of_lt h
  · obtain ⟨q', hwq, hq⟩ := exists_rat_btwn h
    rw [cutMap_coe]
    exact ⟨q', ⟨_, hq, rfl⟩, hwq⟩

@[simp]
/-
**ConditionallyCompleteLinearOrderedField.inducedMap_zero** 是 Mathlib 中的一个定理，位于命
名空间 `ConditionallyCompleteLinearOrderedField`。
形式化陈述：inducedMap_zero : inducedMap α β 0 = 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.cast_zero`：cast_zero : ((0 : Nat) : R) = 0
· 使用定理 `Rat.cast_zero`：cast_zero : ((0 : Rat) : α) = 0
· 使用定理 `ConditionallyCompleteLinearOrderedField.inducedMap_rat`：inducedMap_rat (
q : Rat) : inducedMap α β (q : α) = q
-/
theorem inducedMap_zero : inducedMap α β 0 = 0 := mod_cast inducedMap_rat α β 0

@[simp]
/-
**ConditionallyCompleteLinearOrderedField.inducedMap_one** 是 Mathlib 中的一个定理，位于命名
空间 `ConditionallyCompleteLinearOrderedField`。
形式化陈述：inducedMap_one : inducedMap α β 1 = 1
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `Rat.cast_one`：cast_one : ((1 : Rat) : α) = 1
· 使用定理 `ConditionallyCompleteLinearOrderedField.inducedMap_rat`：inducedMap_rat (
q : Rat) : inducedMap α β (q : α) = q
-/
theorem inducedMap_one : inducedMap α β 1 = 1 := mod_cast inducedMap_rat α β 1

variable {α β} {a : α} {b : β} {q : ℚ}
/-
**ConditionallyCompleteLinearOrderedField.inducedMap_nonneg** 是 Mathlib 中的一个定理，位
于命名空间 `ConditionallyCompleteLinearOrderedField`。
形式化陈述：inducedMap_nonneg (ha : 0 <= a) : 0 <= inducedMap α β a
参数：ha : 0 <= a。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `Eq.ge`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → b ≤ a
· 使用定理 `ConditionallyCompleteLinearOrderedField.inducedMap_zero`：inducedMap_zero
 : inducedMap α β 0 = 0
· 使用定理 `ConditionallyCompleteLinearOrderedField.inducedMap_mono`：inducedMap_mono
 : Monotone (inducedMap α β)
-/
theorem inducedMap_nonneg (ha : 0 ≤ a) : 0 ≤ inducedMap α β a :=
  (inducedMap_zero α _).ge.trans <| inducedMap_mono _ _ ha
/-
**ConditionallyCompleteLinearOrderedField.coe_lt_inducedMap_iff** 是 Mathlib 中的一个
定理，位于命名空间 `ConditionallyCompleteLinearOrderedField`。
形式化陈述：coe_lt_inducedMap_iff : (q : β) < inducedMap α β a ↔ (q : α) < a
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Monotone.reflect_lt`：Monotone.reflect_lt (hf : Monotone f) {a b : α} (h 
: f a < f b) : a < b
· 使用定理 `ConditionallyCompleteLinearOrderedField.inducedMap_mono`：inducedMap_mono
 : Monotone (inducedMap α β)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `ConditionallyCompleteLinearOrderedField.inducedMap_rat`：inducedMap_rat (
q : Rat) : inducedMap α β (q : α) = q
· 使用定理 `exists_rat_btwn`：exists_rat_btwn {x y : K} (h : x < y) : exists q : Rat,
 x < q ∧ q < y
· 使用定理 `lt_csSup_of_lt`：lt_csSup_of_lt (hs : BddAbove s) (ha : a in s) (h : b < 
a) : b < sSup s
· 使用定理 `LinearOrderedField.cutMap_bddAbove`：cutMap_bddAbove (a : α) : BddAbove (
cutMap β a)
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `LinearOrderedField.coe_mem_cutMap_iff`：coe_mem_cutMap_iff [CharZero β] :
 (q : β) in cutMap β a ↔ (q : α) < a
· 使用定理 `IsStrictOrderedRing.toCharZero`：∀ {R : Type u} [inst : Semiring R] [inst
_1 : PartialOrder R] [IsStrictOrderedRing R], CharZero R
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
-/
theorem coe_lt_inducedMap_iff : (q : β) < inducedMap α β a ↔ (q : α) < a := by
  refine ⟨fun h => ?_, fun hq => ?_⟩
  · rw [← inducedMap_rat α] at h
    exact (inducedMap_mono α β).reflect_lt h
  · obtain ⟨q', hq, hqa⟩ := exists_rat_btwn hq
    apply lt_csSup_of_lt (cutMap_bddAbove β a) (coe_mem_cutMap_iff.mpr hqa)
    exact mod_cast hq
/-
**ConditionallyCompleteLinearOrderedField.lt_inducedMap_iff** 是 Mathlib 中的一个定理，位
于命名空间 `ConditionallyCompleteLinearOrderedField`。
形式化陈述：lt_inducedMap_iff : b < inducedMap α β a ↔ exists q : Rat, b < q ∧ (q : α)
 < a
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Exists.imp`：∀ {α : Sort u_1} {p q : α → Prop}, (∀ (a : α), p a → q a) → 
(∃ a, p a) → ∃ a, q a
· 使用定理 `And.imp_right`：∀ {a b c : Prop}, (a → b) → c ∧ a → c ∧ b
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `ConditionallyCompleteLinearOrderedField.coe_lt_inducedMap_iff`：coe_lt_in
ducedMap_iff : (q : β) < inducedMap α β a ↔ (q : α) < a
· 使用定理 `exists_rat_btwn`：exists_rat_btwn {x y : K} (h : x < y) : exists q : Rat,
 x < q ∧ q < y
· 使用定理 `ConditionallyCompleteLinearOrderedField.to_archimedean`：∀ {α : Type u_2}
 [inst : Field α] [inst_1 : ConditionallyCompleteLinearOrder α] [IsStrictOrdered
Ring α], Archimedean α
· 使用定理 `LT.lt.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a < b → b
 < c → a < c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
-/
theorem lt_inducedMap_iff : b < inducedMap α β a ↔ ∃ q : ℚ, b < q ∧ (q : α) < a :=
  ⟨fun h => (exists_rat_btwn h).imp fun _ => And.imp_right coe_lt_inducedMap_iff.1,
    fun ⟨q, hbq, hqa⟩ => hbq.trans <| by rwa [coe_lt_inducedMap_iff]⟩

@[simp]
/-
**ConditionallyCompleteLinearOrderedField.inducedMap_self** 是 Mathlib 中的一个定理，位于命
名空间 `ConditionallyCompleteLinearOrderedField`。
形式化陈述：inducedMap_self (b : β) : inducedMap β β b = b
参数：b : β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_of_forall_rat_lt_iff_lt`：eq_of_forall_rat_lt_iff_lt (h : forall q : R
at, (q : K) < x ↔ (q : K) < y) : x = y
· 使用定理 `ConditionallyCompleteLinearOrderedField.to_archimedean`：∀ {α : Type u_2}
 [inst : Field α] [inst_1 : ConditionallyCompleteLinearOrder α] [IsStrictOrdered
Ring α], Archimedean α
· 使用定理 `ConditionallyCompleteLinearOrderedField.coe_lt_inducedMap_iff`：coe_lt_in
ducedMap_iff : (q : β) < inducedMap α β a ↔ (q : α) < a
-/
theorem inducedMap_self (b : β) : inducedMap β β b = b :=
  eq_of_forall_rat_lt_iff_lt fun _ => coe_lt_inducedMap_iff

variable (α β)

@[simp]
/-
**ConditionallyCompleteLinearOrderedField.inducedMap_inducedMap** 是 Mathlib 中的一个
定理，位于命名空间 `ConditionallyCompleteLinearOrderedField`。
形式化陈述：inducedMap_inducedMap (a : α) : inducedMap β γ (inducedMap α β a) = induce
dMap α γ a
参数：a : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_of_forall_rat_lt_iff_lt`：eq_of_forall_rat_lt_iff_lt (h : forall q : R
at, (q : K) < x ↔ (q : K) < y) : x = y
· 使用定理 `ConditionallyCompleteLinearOrderedField.to_archimedean`：∀ {α : Type u_2}
 [inst : Field α] [inst_1 : ConditionallyCompleteLinearOrder α] [IsStrictOrdered
Ring α], Archimedean α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ConditionallyCompleteLinearOrderedField.coe_lt_inducedMap_iff`：coe_lt_in
ducedMap_iff : (q : β) < inducedMap α β a ↔ (q : α) < a
· 使用定理 `Iff.comm`：∀ {a b : Prop}, (a ↔ b) ↔ (b ↔ a)
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem inducedMap_inducedMap (a : α) : inducedMap β γ (inducedMap α β a) = inducedMap α γ a :=
  eq_of_forall_rat_lt_iff_lt fun q => by
    rw [coe_lt_inducedMap_iff, coe_lt_inducedMap_iff, Iff.comm, coe_lt_inducedMap_iff]
/-
**ConditionallyCompleteLinearOrderedField.inducedMap_inv_self** 是 Mathlib 中的一个定理
，位于命名空间 `ConditionallyCompleteLinearOrderedField`。
形式化陈述：inducedMap_inv_self (b : β) : inducedMap γ β (inducedMap β γ b) = b
参数：b : β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ConditionallyCompleteLinearOrderedField.inducedMap_inducedMap`：inducedMa
p_inducedMap (a : α) : inducedMap β γ (inducedMap α β a) = inducedMap α γ a
· 使用定理 `ConditionallyCompleteLinearOrderedField.to_archimedean`：∀ {α : Type u_2}
 [inst : Field α] [inst_1 : ConditionallyCompleteLinearOrder α] [IsStrictOrdered
Ring α], Archimedean α
· 使用定理 `ConditionallyCompleteLinearOrderedField.inducedMap_self`：inducedMap_self
 (b : β) : inducedMap β β b = b
-/
theorem inducedMap_inv_self (b : β) : inducedMap γ β (inducedMap β γ b) = b := by
  rw [inducedMap_inducedMap, inducedMap_self]
/-
**ConditionallyCompleteLinearOrderedField.inducedMap_add** 是 Mathlib 中的一个定理，位于命名
空间 `ConditionallyCompleteLinearOrderedField`。
形式化陈述：inducedMap_add (x y : α) : inducedMap α β (x + y) = inducedMap α β x + ind
ucedMap α β y
参数：x y : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ConditionallyCompleteLinearOrderedField.inducedMap.eq_1`：∀ (α : Type u_2
) (β : Type u_3) [inst : Field α] [inst_1 : LinearOrder α] [inst_2 : Field β]   
[inst_3 : ConditionallyCompleteLinearOrder β]…
· 使用定理 `LinearOrderedField.cutMap_add`：cutMap_add (a b : α) : cutMap β (a + b) =
 cutMap β a + cutMap β b
· 使用定理 `csSup_add`：∀ {M : Type u_1} [inst : ConditionallyCompleteLattice M] [ins
t_1 : AddGroup M] [AddLeftMono M] [AddRightMono M]   {s t : Set M}, s.Nonempty …
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `IsOrderedRing.toIsOrderedAddMonoid`：∀ {R : Type u_1} {inst : Semiring R}
 {inst_1 : PartialOrder R} [self : IsOrderedRing R], IsOrderedAddMonoid R
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `LinearOrderedField.cutMap_nonempty`：cutMap_nonempty (a : α) : (cutMap β 
a).Nonempty
· 使用定理 `LinearOrderedField.cutMap_bddAbove`：cutMap_bddAbove (a : α) : BddAbove (
cutMap β a)
-/
theorem inducedMap_add (x y : α) :
    inducedMap α β (x + y) = inducedMap α β x + inducedMap α β y := by
  rw [inducedMap, cutMap_add]
  exact csSup_add (cutMap_nonempty β x) (cutMap_bddAbove β x) (cutMap_nonempty β y)
    (cutMap_bddAbove β y)

variable {α β}

/-- Preparatory lemma for `inducedOrderRingHom`. -/
/-
**ConditionallyCompleteLinearOrderedField.le_inducedMap_mul_self_of_mem_cutMap**
 是 Mathlib 中的一个定理，位于命名空间 `ConditionallyCompleteLinearOrderedField`。
形式化陈述：le_inducedMap_mul_self_of_mem_cutMap (ha : 0 < a) (b : β) (hb : b in cutMa
p β (a * a)) : b <= inducedMap α β a * inducedMap α β a
参数：ha : 0 < a；b : β；hb : b in cutMap β (a * a)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `exists_rat_pow_btwn`：exists_rat_pow_btwn {n : Nat} (hn : n != 0) {x y : 
K} (h : x < y) (hy : 0 < y) : exists q : Rat, 0 < q ∧ x < (q : K) ^ n ∧ (q : K) 
^ n < y
· 使用引理 `two_ne_zero`：two_ne_zero [OfNat α 2] [NeZero (2 : α)] : (2 : α) != 0
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `mul_self_pos`：mul_self_pos [ExistsAddOfLE R] [PosMulStrictMono R] [MulPo
sStrictMono R] [AddLeftStrictMono R] [AddLeftReflectLT R] {a : R} : 0 < a * a ↔ 
a …
· 使用定理 `AddGroup.existsAddOfLE`：∀ (α : Type u) [inst : AddGroup α] [inst_1 : LE 
α], ExistsAddOfLE α
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `IsStrictOrderedRing.toMulPosStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], MulPosStrictMono 
R
· 使用定理 `IsLeftCancelAdd.addLeftStrictMono_of_addLeftMono`：∀ (N : Type u_2) [inst
 : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftMono N], AddLeft
StrictMono N
· 使用定理 `instIsLeftCancelAddOfAddLeftReflectLE`：∀ {α : Type u_1} [inst : Add α] [
inst_1 : PartialOrder α] [AddLeftReflectLE α], IsLeftCancelAdd α
· 使用定理 `AddGroup.addLeftReflectLE_of_addLeftMono`：∀ {N : Type u_2} [inst : AddGr
oup N] [inst_1 : LE N] [AddLeftMono N], AddLeftReflectLE N
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `IsOrderedRing.toIsOrderedAddMonoid`：∀ {R : Type u_1} {inst : Semiring R}
 {inst_1 : PartialOrder R} [self : IsOrderedRing R], IsOrderedAddMonoid R
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `pow_two`：∀ {M : Type u_2} [inst : Monoid M] (a : M), a ^ 2 = a * a
· 使用定理 `mul_self_le_mul_self`：mul_self_le_mul_self [PosMulMono α] [MulPosMono α]
 (ha : 0 <= a) (hab : a <= b) : a * a <= b * b
· 使用定理 `IsOrderedRing.toPosMulMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], PosMulMono R
· 使用定理 `IsOrderedRing.toMulPosMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], MulPosMono R
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Nat.cast_zero`：cast_zero : ((0 : Nat) : R) = 0
· 使用定理 `le_csSup`：le_csSup (h₁ : BddAbove s) (h₂ : a in s) : a <= sSup s
· 使用定理 `LinearOrderedField.cutMap_bddAbove`：cutMap_bddAbove (a : α) : BddAbove (
cutMap β a)
· 使用定理 `LinearOrderedField.coe_mem_cutMap_iff`：coe_mem_cutMap_iff [CharZero β] :
 (q : β) in cutMap β a ↔ (q : α) < a
· 使用定理 `IsStrictOrderedRing.toCharZero`：∀ {R : Type u} [inst : Semiring R] [inst
_1 : PartialOrder R] [IsStrictOrderedRing R], CharZero R
· 使用引理 `lt_of_mul_self_lt_mul_self₀`：lt_of_mul_self_lt_mul_self₀ (hb : 0 <= b) :
 a * a < b * b -> a < b

--- 原说明 ---
Preparatory lemma for `inducedOrderRingHom`.
-/
theorem le_inducedMap_mul_self_of_mem_cutMap (ha : 0 < a) (b : β) (hb : b ∈ cutMap β (a * a)) :
    b ≤ inducedMap α β a * inducedMap α β a := by
  obtain ⟨q, hb, rfl⟩ := hb
  obtain ⟨q', hq', hqq', hqa⟩ := exists_rat_pow_btwn two_ne_zero hb (mul_self_pos.2 ha.ne')
  trans (q' : β) ^ 2
  · exact mod_cast hqq'.le
  · rw [pow_two] at hqa ⊢
    exact mul_self_le_mul_self (mod_cast hq'.le)
      (le_csSup (cutMap_bddAbove β a) <|
        coe_mem_cutMap_iff.2 <| lt_of_mul_self_lt_mul_self₀ ha.le hqa)

/-- Preparatory lemma for `inducedOrderRingHom`. -/
/-
**ConditionallyCompleteLinearOrderedField.exists_mem_cutMap_mul_self_of_lt_induc
edMap_mul_self** 是 Mathlib 中的一个定理，位于命名空间 `ConditionallyCompleteLinearOrderedFiel
d`。
形式化陈述：exists_mem_cutMap_mul_self_of_lt_inducedMap_mul_self (ha : 0 < a) (b : β) 
(hba : b < inducedMap α β a * inducedMap α β a) : exists c in cutMap β (a * a), 
b < c
参数：ha : 0 < a；b : β；hba : b < inducedMap α β a * inducedMap α β a。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `lt_or_ge`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), a < b ∨ b ≤
 a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Rat.cast_zero`：cast_zero : ((0 : Rat) : α) = 0
· 使用定理 `LinearOrderedField.coe_mem_cutMap_iff`：coe_mem_cutMap_iff [CharZero β] :
 (q : β) in cutMap β a ↔ (q : α) < a
· 使用定理 `IsStrictOrderedRing.toCharZero`：∀ {R : Type u} [inst : Semiring R] [inst
_1 : PartialOrder R] [IsStrictOrderedRing R], CharZero R
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `mul_self_pos`：mul_self_pos [ExistsAddOfLE R] [PosMulStrictMono R] [MulPo
sStrictMono R] [AddLeftStrictMono R] [AddLeftReflectLT R] {a : R} : 0 < a * a ↔ 
a …
· 使用定理 `AddGroup.existsAddOfLE`：∀ (α : Type u) [inst : AddGroup α] [inst_1 : LE 
α], ExistsAddOfLE α
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `IsStrictOrderedRing.toMulPosStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], MulPosStrictMono 
R
· 使用定理 `IsLeftCancelAdd.addLeftStrictMono_of_addLeftMono`：∀ (N : Type u_2) [inst
 : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftMono N], AddLeft
StrictMono N
· 使用定理 `instIsLeftCancelAddOfAddLeftReflectLE`：∀ {α : Type u_1} [inst : Add α] [
inst_1 : PartialOrder α] [AddLeftReflectLE α], IsLeftCancelAdd α
· 使用定理 `AddGroup.addLeftReflectLE_of_addLeftMono`：∀ {N : Type u_2} [inst : AddGr
oup N] [inst_1 : LE N] [AddLeftMono N], AddLeftReflectLE N
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `IsOrderedRing.toIsOrderedAddMonoid`：∀ {R : Type u_1} {inst : Semiring R}
 {inst_1 : PartialOrder R} [self : IsOrderedRing R], IsOrderedAddMonoid R
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `exists_rat_pow_btwn`：exists_rat_pow_btwn {n : Nat} (hn : n != 0) {x y : 
K} (h : x < y) (hy : 0 < y) : exists q : Rat, 0 < q ∧ x < (q : K) ^ n ∧ (q : K) 
^ n < y
· 使用定理 `ConditionallyCompleteLinearOrderedField.to_archimedean`：∀ {α : Type u_2}
 [inst : Field α] [inst_1 : ConditionallyCompleteLinearOrder α] [IsStrictOrdered
Ring α], Archimedean α
· 使用引理 `two_ne_zero`：two_ne_zero [OfNat α 2] [NeZero (2 : α)] : (2 : α) != 0
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `LE.le.trans_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b 
→ b < c → a < c
· 使用定理 `pow_two`：∀ {M : Type u_2} [inst : Monoid M] (a : M), a ^ 2 = a * a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Rat.cast_mul`：∀ {α : Type u_3} [inst : DivisionRing α] [CharZero α] (p q
 : ℚ), ↑(p * q) = ↑p * ↑q
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `ConditionallyCompleteLinearOrderedField.lt_inducedMap_iff`：lt_inducedMap
_iff : b < inducedMap α β a ↔ exists q : Rat, b < q ∧ (q : α) < a
· 使用引理 `lt_of_mul_self_lt_mul_self₀`：lt_of_mul_self_lt_mul_self₀ (hb : 0 <= b) :
 a * a < b * b -> a < b
· 使用定理 `IsOrderedRing.toMulPosMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], MulPosMono R
（共 37 条，此处仅展示前 30 条）

--- 原说明 ---
Preparatory lemma for `inducedOrderRingHom`.
-/
theorem exists_mem_cutMap_mul_self_of_lt_inducedMap_mul_self (ha : 0 < a) (b : β)
    (hba : b < inducedMap α β a * inducedMap α β a) : ∃ c ∈ cutMap β (a * a), b < c := by
  obtain hb | hb := lt_or_ge b 0
  · refine ⟨0, ?_, hb⟩
    rw [← Rat.cast_zero, coe_mem_cutMap_iff, Rat.cast_zero]
    exact mul_self_pos.2 ha.ne'
  obtain ⟨q, hq, hbq, hqa⟩ := exists_rat_pow_btwn two_ne_zero hba (hb.trans_lt hba)
  rw [← cast_pow] at hbq
  refine ⟨(q ^ 2 : ℚ), coe_mem_cutMap_iff.2 ?_, hbq⟩
  rw [pow_two] at hqa ⊢
  push_cast
  obtain ⟨q', hq', hqa'⟩ := lt_inducedMap_iff.1 (lt_of_mul_self_lt_mul_self₀
    (inducedMap_nonneg ha.le) hqa)
  exact mul_self_lt_mul_self (mod_cast hq.le) (hqa'.trans' <| by assumption_mod_cast)

variable (α β)

/-- `inducedMap` as an additive homomorphism. -/
/-
**ConditionallyCompleteLinearOrderedField.inducedAddHom** 是 Mathlib 中的一个定义，位于命名空
间 `ConditionallyCompleteLinearOrderedField`。
形式化陈述：inducedAddHom : α ->+ β
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `ConditionallyCompleteLinearOrderedField.inducedMap_zero`：inducedMap_zero
 : inducedMap α β 0 = 0
· 使用定理 `ConditionallyCompleteLinearOrderedField.inducedMap_add`：inducedMap_add (
x y : α) : inducedMap α β (x + y) = inducedMap α β x + inducedMap α β y

--- 原说明 ---
`inducedMap` as an additive homomorphism.
-/
def inducedAddHom : α →+ β :=
  ⟨⟨inducedMap α β, inducedMap_zero α β⟩, inducedMap_add α β⟩

/-- `inducedMap` as an `OrderRingHom`. -/
@[simps!]
/-
**ConditionallyCompleteLinearOrderedField.inducedOrderRingHom** 是 Mathlib 中的一个定义
，位于命名空间 `ConditionallyCompleteLinearOrderedField`。
形式化陈述：inducedOrderRingHom : α ->+*o β
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Field.isDomain`：∀ {K : Type u_1} [inst : Field K], IsDomain K
· 使用定理 `ConditionallyCompleteLinearOrderedField.inducedMap_one`：inducedMap_one :
 inducedMap α β 1 = 1
· 使用定理 `ConditionallyCompleteLinearOrderedField.inducedMap_mono`：inducedMap_mono
 : Monotone (inducedMap α β)

--- 原说明 ---
`inducedMap` as an `OrderRingHom`.
-/
def inducedOrderRingHom : α →+*o β :=
  { AddMonoidHom.mkRingHomOfMulSelfOfTwoNeZero (inducedAddHom α β) (by
      suffices ∀ x, 0 < x → inducedAddHom α β (x * x) = inducedAddHom α β x * inducedAddHom α β x by
        intro x
        obtain h | rfl | h := lt_trichotomy x 0
        · convert! this (-x) (neg_pos.2 h) using 1
          · rw [neg_mul, mul_neg, neg_neg]
          · simp_rw [map_neg, neg_mul, mul_neg, neg_neg]
        · simp only [mul_zero, map_zero]
        · exact this x h
        -- prove that the (Sup of rationals less than x) ^ 2 is the Sup of the set of rationals less
        -- than (x ^ 2) by showing it is an upper bound and any smaller number is not an upper bound
      refine fun x hx => csSup_eq_of_forall_le_of_forall_lt_exists_gt (cutMap_nonempty β _) ?_ ?_
      · exact le_inducedMap_mul_self_of_mem_cutMap hx
      · exact exists_mem_cutMap_mul_self_of_lt_inducedMap_mul_self hx)
          two_ne_zero (inducedMap_one _ _) with
    monotone' := inducedMap_mono _ _ }

set_option backward.isDefEq.respectTransparency false in
/-- The isomorphism of ordered rings between two conditionally complete linearly ordered fields. -/
/-
**ConditionallyCompleteLinearOrderedField.inducedOrderRingIso** 是 Mathlib 中的一个定义
，位于命名空间 `ConditionallyCompleteLinearOrderedField`。
形式化陈述：inducedOrderRingIso : β ≃+*o γ
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `ConditionallyCompleteLinearOrderedField.to_archimedean`：∀ {α : Type u_2}
 [inst : Field α] [inst_1 : ConditionallyCompleteLinearOrder α] [IsStrictOrdered
Ring α], Archimedean α
· 使用定理 `ConditionallyCompleteLinearOrderedField.inducedMap_inv_self`：inducedMap_
inv_self (b : β) : inducedMap γ β (inducedMap β γ b) = b

--- 原说明 ---
The isomorphism of ordered rings between two conditionally complete linearly ord
ered fields.
-/
def inducedOrderRingIso : β ≃+*o γ :=
  { inducedOrderRingHom β γ with
    invFun := inducedMap γ β
    left_inv := inducedMap_inv_self _ _
    right_inv := inducedMap_inv_self _ _
    map_le_map_iff' := by
      dsimp
      refine ⟨fun h => ?_, fun h => inducedMap_mono _ _ h⟩
      convert! inducedMap_mono γ β h <;>
      · rw [inducedOrderRingHom, AddMonoidHom.coe_fn_mkRingHomOfMulSelfOfTwoNeZero, inducedAddHom]
        dsimp
        rw [inducedMap_inv_self β γ _] }

@[simp]
/-
**ConditionallyCompleteLinearOrderedField.coe_inducedOrderRingIso** 是 Mathlib 中的
一个定理，位于命名空间 `ConditionallyCompleteLinearOrderedField`。
形式化陈述：coe_inducedOrderRingIso : ⇑(inducedOrderRingIso β γ) = inducedMap β γ
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_inducedOrderRingIso : ⇑(inducedOrderRingIso β γ) = inducedMap β γ := rfl

@[simp]
/-
**ConditionallyCompleteLinearOrderedField.inducedOrderRingIso_symm** 是 Mathlib 中
的一个定理，位于命名空间 `ConditionallyCompleteLinearOrderedField`。
形式化陈述：inducedOrderRingIso_symm : (inducedOrderRingIso β γ).symm = inducedOrderRi
ngIso γ β
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem inducedOrderRingIso_symm : (inducedOrderRingIso β γ).symm = inducedOrderRingIso γ β := rfl

@[simp]
/-
**ConditionallyCompleteLinearOrderedField.inducedOrderRingIso_self** 是 Mathlib 中
的一个定理，位于命名空间 `ConditionallyCompleteLinearOrderedField`。
形式化陈述：inducedOrderRingIso_self : inducedOrderRingIso β β = OrderRingIso.refl β
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `OrderRingIso.ext`：ext {f g : α ≃+*o β} (h : forall a, f a = g a) : f = g
· 使用定理 `ConditionallyCompleteLinearOrderedField.inducedMap_self`：inducedMap_self
 (b : β) : inducedMap β β b = b
-/
theorem inducedOrderRingIso_self : inducedOrderRingIso β β = OrderRingIso.refl β :=
  OrderRingIso.ext inducedMap_self

open OrderRingIso

/-- There is a unique ordered ring homomorphism from an archimedean linear ordered field to a
conditionally complete linear ordered field. -/
/-
**ConditionallyCompleteLinearOrderedField.uniqueOrderRingHom** 是 Mathlib 中的一个定义，
位于命名空间 `ConditionallyCompleteLinearOrderedField`。
形式化陈述：(α : Type u_2) →   (β : Type u_3) →     [inst : Field α] →       [inst_1 :
 LinearOrder α] →         [IsStrictOrderedRing α] →           [inst_3 : Field β]
 →             [inst_4 : ConditionallyCompleteLinearOrder β] →               [Is
StrictOrderedRing β] → [Archimedean α] → Unique (α →+*o β)
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
There is a unique ordered ring homomorphism from an archimedean linear ordered f
ield to a
conditionally complete linear ordered field.
-/
scoped instance uniqueOrderRingHom : Unique (α →+*o β) :=
  uniqueOfSubsingleton <| inducedOrderRingHom α β

/-- There is a unique ordered ring isomorphism between two conditionally complete linear ordered
fields. -/
/-
**ConditionallyCompleteLinearOrderedField.uniqueOrderRingIso** 是 Mathlib 中的一个定义，
位于命名空间 `ConditionallyCompleteLinearOrderedField`。
形式化陈述：(β : Type u_3) →   (γ : Type u_4) →     [inst : Field β] →       [inst_1 :
 ConditionallyCompleteLinearOrder β] →         [IsStrictOrderedRing β] →        
   [inst_3 : Field γ] →             [inst_4 : ConditionallyCompleteLinearOrder γ
] → [IsStrictOrderedRing γ] → Unique (β ≃+*o γ)
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
There is a unique ordered ring isomorphism between two conditionally complete li
near ordered
fields.
-/
scoped instance uniqueOrderRingIso : Unique (β ≃+*o γ) :=
  uniqueOfSubsingleton <| inducedOrderRingIso β γ

end InducedMap

end ConditionallyCompleteLinearOrderedField

namespace LinearOrderedField

@[deprecated (since := "2026-02-24")]
alias inducedMap := ConditionallyCompleteLinearOrderedField.inducedMap
@[deprecated (since := "2026-02-24")]
alias inducedMap_mono := ConditionallyCompleteLinearOrderedField.inducedMap_mono
@[deprecated (since := "2026-02-24")]
alias inducedMap_rat := ConditionallyCompleteLinearOrderedField.inducedMap_rat
@[deprecated (since := "2026-02-24")]
alias inducedMap_zero := ConditionallyCompleteLinearOrderedField.inducedMap_zero
@[deprecated (since := "2026-02-24")]
alias inducedMap_one := ConditionallyCompleteLinearOrderedField.inducedMap_one
@[deprecated (since := "2026-02-24")]
alias inducedMap_nonneg := ConditionallyCompleteLinearOrderedField.inducedMap_nonneg
@[deprecated (since := "2026-02-24")]
alias coe_lt_inducedMap_iff := ConditionallyCompleteLinearOrderedField.coe_lt_inducedMap_iff
@[deprecated (since := "2026-02-24")]
alias lt_inducedMap_iff := ConditionallyCompleteLinearOrderedField.lt_inducedMap_iff
@[deprecated (since := "2026-02-24")]
alias inducedMap_self := ConditionallyCompleteLinearOrderedField.inducedMap_self
@[deprecated (since := "2026-02-24")]
alias inducedMap_inducedMap := ConditionallyCompleteLinearOrderedField.inducedMap_inducedMap
@[deprecated (since := "2026-02-24")]
alias inducedMap_inv_self := ConditionallyCompleteLinearOrderedField.inducedMap_inv_self
@[deprecated (since := "2026-02-24")]
alias inducedMap_add := ConditionallyCompleteLinearOrderedField.inducedMap_add
@[deprecated (since := "2026-02-24")]
alias le_inducedMap_mul_self_of_mem_cutMap :=
  ConditionallyCompleteLinearOrderedField.le_inducedMap_mul_self_of_mem_cutMap
@[deprecated (since := "2026-02-24")]
alias exists_mem_cutMap_mul_self_of_lt_inducedMap_mul_self :=
  ConditionallyCompleteLinearOrderedField.exists_mem_cutMap_mul_self_of_lt_inducedMap_mul_self
@[deprecated (since := "2026-02-24")]
alias inducedAddHom := ConditionallyCompleteLinearOrderedField.inducedAddHom
@[deprecated (since := "2026-02-24")]
alias inducedOrderRingHom := ConditionallyCompleteLinearOrderedField.inducedOrderRingHom
@[deprecated (since := "2026-02-24")]
alias inducedOrderRingIso := ConditionallyCompleteLinearOrderedField.inducedOrderRingIso
@[deprecated (since := "2026-02-24")]
alias coe_inducedOrderRingIso := ConditionallyCompleteLinearOrderedField.coe_inducedOrderRingIso
@[deprecated (since := "2026-02-24")]
alias inducedOrderRingIso_symm := ConditionallyCompleteLinearOrderedField.inducedOrderRingIso_symm
@[deprecated (since := "2026-02-24")]
alias inducedOrderRingIso_self := ConditionallyCompleteLinearOrderedField.inducedOrderRingIso_self

end LinearOrderedField

