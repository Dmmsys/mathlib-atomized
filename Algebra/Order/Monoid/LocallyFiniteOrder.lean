/-
Copyright (c) 2025 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
module

public import Mathlib.Algebra.Group.Subgroup.Ker
public import Mathlib.Algebra.Order.Group.Units
public import Mathlib.Algebra.Order.Hom.MonoidWithZero
public import Mathlib.Algebra.Order.Hom.TypeTags
public import Mathlib.Algebra.Order.Ring.Int
public import Mathlib.Data.Nat.Cast.Order.Ring
public import Mathlib.Tactic.Abel
public import Mathlib.Algebra.Group.Embedding
public import Mathlib.Order.Interval.Finset.Basic

/-!

# Locally Finite Linearly Ordered Abelian Groups

## Main results
- `LocallyFiniteOrder.orderAddMonoidEquiv`:
  Any nontrivial linearly ordered additive abelian group that is locally finite is
  isomorphic to `ℤ`.
- `LocallyFiniteOrder.orderMonoidEquiv`:
  Any nontrivial linearly ordered abelian group that is locally finite is isomorphic to
  `Multiplicative ℤ`.
- `LocallyFiniteOrder.orderMonoidWithZeroEquiv`:
  Any nontrivial linearly ordered abelian group with zero that is locally finite
  is isomorphic to `ℤᵐ⁰`.

-/

@[expose] public section

open Finset

section Multiplicative

variable {M : Type*} [CancelCommMonoid M] [LinearOrder M] [IsOrderedMonoid M] [LocallyFiniteOrder M]

@[to_additive]
/-
**Finset.card_Ico_mul_right** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Finset.card_Ico_mul_right [ExistsMulOfLE M] (a b c : M) : #(Ico (a * c) (b
 * c)) = #(Ico a b)
参数：a b c : M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instIsRightCancelMulOfMulRightReflectLE`：∀ {α : Type u_1} [inst : Mul α]
 [inst_1 : PartialOrder α] [MulRightReflectLE α], IsRightCancelMul α
· 使用定理 `LeftCancelSemigroup.toIsLeftCancelMul`：∀ {G : Type u} [self : LeftCancel
Semigroup G], IsLeftCancelMul G
· 使用定理 `IsOrderedMonoid.toMulLeftMono`：∀ {α : Type u_1} [inst : CommMonoid α] [i
nst_1 : Preorder α] [IsOrderedMonoid α], MulLeftMono α
· 使用定理 `Finset.ext`：ext {s₁ s₂ : Finset α} (h : forall a, a in s₁ ↔ a in s₂) : s
₁ = s₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `mulRightEmbedding_apply`：∀ {G : Type u_1} [inst : Mul G] [inst_1 : IsRig
htCancelMul G] (g h : G), (mulRightEmbedding g) h = h * g
· 使用定理 `ExistsMulOfLE.exists_mul_of_le`：∀ {α : Type u} {inst : Mul α} {inst_1 : 
LE α} [self : ExistsMulOfLE α] {a b : α}, a ≤ b → ∃ c, b = a * c
· 使用定理 `mul_right_comm`：mul_right_comm (a b c : G) : a * b * c = a * c * b
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `RightCancelSemigroup.toIsRightCancelMul`：∀ {G : Type u} [self : RightCan
celSemigroup G], IsRightCancelMul G
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
· 使用定理 `Finset.card_map`：card_map (f : α ↪ β) : #(s.map f) = #s
-/
lemma Finset.card_Ico_mul_right [ExistsMulOfLE M] (a b c : M) :
    #(Ico (a * c) (b * c)) = #(Ico a b) := by
  have : (Ico (a * c) (b * c)) = (Ico a b).map (mulRightEmbedding c) := by
    ext x
    simp only [mem_Ico, mem_map, mulRightEmbedding_apply]
    constructor
    · rintro ⟨h₁, h₂⟩
      obtain ⟨d, rfl⟩ := exists_mul_of_le h₁
      exact ⟨a * d, ⟨by simpa using h₁, by simpa [mul_right_comm a c d] using h₂⟩,
        by simp_rw [mul_assoc, mul_comm]⟩
    · aesop
  simp [this]

@[to_additive]
/-
**card_Ico_one_mul** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：card_Ico_one_mul [ExistsMulOfLE M] (a b : M) (ha : 1 <= a) (hb : 1 <= b) :
 #(Ico 1 (a * b)) = #(Ico 1 a) + #(Ico 1 b)
参数：a b : M；ha : 1 <= a；hb : 1 <= b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `Finset.Ico_union_Ico`：Ico_union_Ico {a b c d : α} (h₁ : min a b <= max c
 d) (h₂ : min c d <= max a b) : Ico a b union Ico c d = Ico (min a c) (max b d)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `inf_of_le_left`：∀ {α : Type u} [inst : SemilatticeInf α] {a b : α}, a ≤ 
b → a ⊓ b = a
· 使用定理 `sup_of_le_right`：∀ {α : Type u} [inst : SemilatticeSup α] {a b : α}, a ≤
 b → a ⊔ b = b
· 使用定理 `IsOrderedMonoid.toMulLeftMono`：∀ {α : Type u_1} [inst : CommMonoid α] [i
nst_1 : Preorder α] [IsOrderedMonoid α], MulLeftMono α
· 使用定理 `instIsRightCancelMulOfMulRightReflectLE`：∀ {α : Type u_1} [inst : Mul α]
 [inst_1 : PartialOrder α] [MulRightReflectLE α], IsRightCancelMul α
· 使用定理 `LeftCancelSemigroup.toIsLeftCancelMul`：∀ {G : Type u} [self : LeftCancel
Semigroup G], IsLeftCancelMul G
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `Right.one_le_mul`：Right.one_le_mul [MulRightMono α] {a b : α} (ha : 1 <=
 a) (hb : 1 <= b) : 1 <= a * b
· 使用定理 `RightCancelSemigroup.toIsRightCancelMul`：∀ {G : Type u} [self : RightCan
celSemigroup G], IsRightCancelMul G
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `Finset.card_union`：card_union (s t : Finset α) : #(s union t) = #s + #t 
- #(s inter t)
· 使用引理 `Finset.card_Ico_mul_right`：Finset.card_Ico_mul_right [ExistsMulOfLE M] (
a b c : M) : #(Ico (a * c) (b * c)) = #(Ico a b)
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
· 使用定理 `Finset.Ico_inter_Ico_consecutive`：Ico_inter_Ico_consecutive (a b c : α) 
: Ico a b inter Ico b c = ∅
· 使用定理 `tsub_zero`：tsub_zero (a : α) : a - 0 = a
-/
lemma card_Ico_one_mul [ExistsMulOfLE M] (a b : M)
    (ha : 1 ≤ a) (hb : 1 ≤ b) :
    #(Ico 1 (a * b)) = #(Ico 1 a) + #(Ico 1 b) := by
  have : Ico 1 b ∪ Ico (1 * b) (a * b) = Ico 1 (a * b) := by
    simp [Ico_union_Ico, ha, hb, Right.one_le_mul ha hb]
  rw [← this, Finset.card_union, Finset.card_Ico_mul_right]
  simp [add_comm]

end Multiplicative

variable {M G : Type*} [AddCancelCommMonoid M] [LinearOrder M] [IsOrderedAddMonoid M]
    [LocallyFiniteOrder M] [AddCommGroup G] [LinearOrder G]
    [IsOrderedAddMonoid G] [LocallyFiniteOrder G]

variable (G) in
/-- The canonical embedding (as a monoid hom) from a linearly ordered cancellative additive monoid
into `ℤ`. This is either surjective or zero. -/
/-
**LocallyFiniteOrder.addMonoidHom** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：LocallyFiniteOrder.addMonoidHom : G ->+ Int where toFun a
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The canonical embedding (as a monoid hom) from a linearly ordered cancellative a
dditive monoid
into `ℤ`. This is either surjective or zero.
-/
def LocallyFiniteOrder.addMonoidHom :
    G →+ ℤ where
  toFun a := #(Ico 0 a) - #(Ico 0 (-a))
  map_zero' := by simp
  map_add' a b := by
    wlog hab : a ≤ b generalizing a b
    · convert! this b a (le_of_not_ge hab) using 1 <;> simp only [add_comm]
    obtain ha | ha := le_total 0 a <;> obtain hb | hb := le_total 0 b
    · have : -b ≤ a := by trans 0 <;> simp [ha, hb]
      simp [ha, hb, card_Ico_zero_add, this]
    · obtain rfl := hb.antisymm (ha.trans hab)
      obtain rfl := ha.antisymm hab
      simp
    · simp only [neg_add_rev, ha, Ico_eq_empty_of_le, card_empty, Nat.cast_zero, zero_sub,
        Left.neg_nonpos_iff, hb, sub_zero]
      obtain ⟨b, rfl⟩ : ∃ r, b = r - a := ⟨a + b, by abel⟩
      simp only [add_sub_cancel, neg_sub, sub_add_eq_add_sub, add_neg_cancel, zero_sub]
      obtain hb' | hb' := le_total 0 b
      · simp [hb', neg_add_eq_sub, eq_sub_iff_add_eq, ← Nat.cast_add,
          ← card_Ico_zero_add, ha, ← sub_eq_add_neg]
      · simp [hb', neg_add_eq_sub, eq_sub_iff_add_eq, sub_eq_iff_eq_add,
          ← Nat.cast_add, ← card_Ico_zero_add, hb, sub_add_eq_add_sub]
    · have : ¬0 < a + b := by simpa using add_nonpos ha hb
      simp [ha, hb, card_Ico_zero_add, Ico_eq_empty, this]

variable (G) in
/-- The canonical embedding (as an ordered monoid hom) from a linearly ordered cancellative
group into `ℤ`. This is either surjective or zero. -/
/-
**LocallyFiniteOrder.orderAddMonoidHom** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：LocallyFiniteOrder.orderAddMonoidHom : G ->+o Int where __
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The canonical embedding (as an ordered monoid hom) from a linearly ordered cance
llative
group into `ℤ`. This is either surjective or zero.
-/
def LocallyFiniteOrder.orderAddMonoidHom :
    G →+o ℤ where
  __ := addMonoidHom G
  monotone' a b hab := by
    obtain ⟨b, rfl⟩ := add_left_surjective a b
    replace hab : 0 ≤ b := by simpa using hab
    suffices 0 ≤ addMonoidHom G b by simpa
    simp [addMonoidHom, hab]

@[simp]
/-
**LocallyFiniteOrder.orderAddMonoidHom_toAddMonoidHom** 是 Mathlib 中的一个引理，位于命名空间 
``。
形式化陈述：LocallyFiniteOrder.orderAddMonoidHom_toAddMonoidHom : orderAddMonoidHom G 
= addMonoidHom G
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `OrderAddMonoidHom.instAddMonoidHomClass`：∀ {α : Type u_2} {β : Type u_3}
 [inst : Preorder α] [inst_1 : Preorder β] [inst_2 : AddZeroClass α]   [inst_3 :
 AddZeroClass β], AddMonoidHo…
-/
lemma LocallyFiniteOrder.orderAddMonoidHom_toAddMonoidHom :
    orderAddMonoidHom G = addMonoidHom G := rfl

@[simp]
/-
**LocallyFiniteOrder.orderAddMonoidHom_apply** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：LocallyFiniteOrder.orderAddMonoidHom_apply (x : G) : orderAddMonoidHom G x
 = addMonoidHom G x
参数：x : G。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma LocallyFiniteOrder.orderAddMonoidHom_apply (x : G) :
    orderAddMonoidHom G x = addMonoidHom G x := rfl
/-
**LocallyFiniteOrder.orderAddMonoidHom_strictMono** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：LocallyFiniteOrder.orderAddMonoidHom_strictMono : StrictMono (orderAddMono
idHom G)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `strictMono_iff_map_pos`：strictMono_iff_map_pos : StrictMono (f : α -> β)
 ↔ forall a, 0 < a -> 0 < f a
· 使用定理 `OrderAddMonoidHom.instAddMonoidHomClass`：∀ {α : Type u_2} {β : Type u_3}
 [inst : Preorder α] [inst_1 : Preorder β] [inst_2 : AddZeroClass α]   [inst_3 :
 AddZeroClass β], AddMonoidHo…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Finset.Ico_eq_empty_of_le`：Ico_eq_empty_of_le (h : b <= a) : Ico a b = ∅
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `Nat.cast_zero`：cast_zero : ((0 : Nat) : R) = 0
· 使用定理 `sub_zero`：∀ {G : Type u_3} [inst : SubNegZeroMonoid G] (a : G), a - 0 = 
a
-/
lemma LocallyFiniteOrder.orderAddMonoidHom_strictMono :
    StrictMono (orderAddMonoidHom G) := by
  rw [strictMono_iff_map_pos]
  intro g H
  simpa [addMonoidHom, H.le]
/-
**LocallyFiniteOrder.orderAddMonoidHom_bijective** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：LocallyFiniteOrder.orderAddMonoidHom_bijective [Nontrivial G] : Function.B
ijective (orderAddMonoidHom G)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `StrictMono.injective`：StrictMono.injective (hf : StrictMono f) : Injecti
ve f
· 使用引理 `LocallyFiniteOrder.orderAddMonoidHom_strictMono`：LocallyFiniteOrder.orde
rAddMonoidHom_strictMono : StrictMono (orderAddMonoidHom G)
· 使用定理 `exists_zero_lt`：∀ {α : Type u} [inst : AddCommGroup α] [inst_1 : LinearO
rder α] [IsOrderedAddMonoid α] [Nontrivial α], ∃ a, 0 < a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用引理 `exists_covBy_of_wellFoundedLT`：exists_covBy_of_wellFoundedLT [wf : WellF
oundedLT α] ⦃a : α⦄ (h : ¬ IsMax a) : exists a', a ⋖ a'
· 使用定理 `IsWellOrder.toIsWellFounded`：∀ {α : Type u} {r : α → α → Prop} [self : I
sWellOrder α r], IsWellFounded α r
· 使用定理 `isWellOrder_lt`：∀ {α : Type u} [inst : LinearOrder α] [WellFoundedLT α],
 IsWellOrder α fun x1 x2 => x1 < x2
· 使用定理 `Finite.to_wellFoundedLT`：∀ {α : Type u_1} [Finite α] [inst : Preorder α]
, WellFoundedLT α
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `LT.lt.not_ge`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → ¬b
 ≤ a
· 使用定理 `and_true`：∀ (p : Prop), (p ∧ True) = p
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Finset.ext`：ext {s₁ s₂ : Finset α} (h : forall a, a in s₁ ↔ a in s₂) : s
₁ = s₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Decidable.byContradiction`：∀ {p : Prop} [dec : Decidable p], (¬p → False
) → p
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用引理 `lt_of_le_of_ne`：lt_of_le_of_ne : a <= b -> a != b -> a < b
· 使用定理 `Subtype.mk.injEq`：∀ {α : Sort u} {p : α → Prop} (val : α) (property : p 
val) (val_1 : α) (property_1 : p val_1),   (⟨val, property⟩ = ⟨val_1, property_1
⟩) = (…
· 使用定理 `Ne.symm`：∀ {α : Sort u} {a b : α}, a ≠ b → b ≠ a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.card_singleton`：card_singleton (a : α) : #{a} = 1
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `IsLeftCancelAdd.addLeftStrictMono_of_addLeftMono`：∀ (N : Type u_2) [inst
 : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftMono N], AddLeft
StrictMono N
（共 38 条，此处仅展示前 30 条）
-/
lemma LocallyFiniteOrder.orderAddMonoidHom_bijective [Nontrivial G] :
    Function.Bijective (orderAddMonoidHom G) := by
  refine ⟨orderAddMonoidHom_strictMono.injective, ?_⟩
  suffices 1 ∈ (orderAddMonoidHom G).range by
    obtain ⟨x, hx⟩ := this
    exact fun a ↦ ⟨a • x, by simp_all⟩
  have ⟨a, ha⟩ := exists_zero_lt (α := G)
  obtain ⟨b, hb⟩ := exists_covBy_of_wellFoundedLT (α := Icc 0 a) (a := ⟨0, by simpa using! ha.le⟩)
    (fun H ↦ ha.not_ge (@H ⟨a, by simpa using! ha.le⟩ ha.le))
  use b.1
  have : 0 ≤ b.1 := hb.1.le
  suffices Ico 0 b.1 = {0} by simpa [orderAddMonoidHom, addMonoidHom, this]
  ext x
  simp only [mem_Ico, mem_singleton]
  constructor
  · rintro ⟨h₁, h₂⟩
    by_contra hx'
    have := b.2
    simp only [Finset.mem_Icc] at this
    exact hb.2 (c := ⟨x, by simpa [h₁] using! h₂.le.trans this.2⟩)
      (lt_of_le_of_ne h₁ (by simpa using! Ne.symm hx')) h₂
  · rintro rfl
    simpa using! hb.1

variable (G) in
/-- Any nontrivial linearly ordered abelian group that is locally finite is isomorphic to `ℤ`. -/
noncomputable
/-
**LocallyFiniteOrder.orderAddMonoidEquiv** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：LocallyFiniteOrder.orderAddMonoidEquiv [Nontrivial G] : G ≃+o Int where __
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用引理 `LocallyFiniteOrder.orderAddMonoidHom_bijective`：LocallyFiniteOrder.order
AddMonoidHom_bijective [Nontrivial G] : Function.Bijective (orderAddMonoidHom G)
-/
def LocallyFiniteOrder.orderAddMonoidEquiv [Nontrivial G] :
    G ≃+o ℤ where
  __ := orderAddMonoidHom G
  __ := AddEquiv.ofBijective (orderAddMonoidHom G) orderAddMonoidHom_bijective
  map_le_map_iff' {a b} := by
    obtain ⟨b, rfl⟩ := add_left_surjective a b
    suffices 0 ≤ orderAddMonoidHom G b ↔ 0 ≤ b by simpa
    obtain hb | hb := le_total 0 b
    · simp [orderAddMonoidHom, addMonoidHom, hb]
    · simp [orderAddMonoidHom, addMonoidHom, hb]
/-
**LocallyFiniteOrder.orderAddMonoidEquiv_apply** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：LocallyFiniteOrder.orderAddMonoidEquiv_apply [Nontrivial G] (x : G) : orde
rAddMonoidEquiv G x = addMonoidHom G x
参数：x : G。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma LocallyFiniteOrder.orderAddMonoidEquiv_apply [Nontrivial G] (x : G) :
    orderAddMonoidEquiv G x = addMonoidHom G x := rfl

set_option backward.isDefEq.respectTransparency false in
/-- Any linearly ordered abelian group that is locally finite embeds to `Multiplicative ℤ`. -/
noncomputable
/-
**LocallyFiniteOrder.orderMonoidEquiv** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：LocallyFiniteOrder.orderMonoidEquiv (G : Type*) [CommGroup G] [LinearOrder
 G] [IsOrderedMonoid G] [LocallyFiniteOrder G] [Nontrivial G] : G ≃*o Multiplica
tive Int
参数：G : Type*。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def LocallyFiniteOrder.orderMonoidEquiv (G : Type*) [CommGroup G] [LinearOrder G]
    [IsOrderedMonoid G] [LocallyFiniteOrder G] [Nontrivial G] :
    G ≃*o Multiplicative ℤ :=
  have : LocallyFiniteOrder (Additive G) := ‹LocallyFiniteOrder G›
  (orderAddMonoidEquiv (Additive G)).toMultiplicative

set_option backward.isDefEq.respectTransparency false in
/-- Any linearly ordered abelian group that is locally finite embeds into `Multiplicative ℤ`. -/
noncomputable
/-
**LocallyFiniteOrder.orderMonoidHom** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：LocallyFiniteOrder.orderMonoidHom (G : Type*) [CommGroup G] [LinearOrder G
] [IsOrderedMonoid G] [LocallyFiniteOrder G] : G ->*o Multiplicative Int
参数：G : Type*。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def LocallyFiniteOrder.orderMonoidHom (G : Type*) [CommGroup G] [LinearOrder G]
    [IsOrderedMonoid G] [LocallyFiniteOrder G] :
    G →*o Multiplicative ℤ :=
  have : LocallyFiniteOrder (Additive G) := ‹LocallyFiniteOrder G›
  ⟨(orderAddMonoidHom (Additive G)).toMultiplicative, (orderAddMonoidHom (Additive G)).2⟩

set_option backward.isDefEq.respectTransparency false in
/-
**LocallyFiniteOrder.orderMonoidHom_strictMono** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：LocallyFiniteOrder.orderMonoidHom_strictMono {G : Type*} [CommGroup G] [Li
nearOrder G] [IsOrderedMonoid G] [LocallyFiniteOrder G] : StrictMono (orderMonoi
dHom G)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `LocallyFiniteOrder.orderAddMonoidHom_strictMono`：LocallyFiniteOrder.orde
rAddMonoidHom_strictMono : StrictMono (orderAddMonoidHom G)
-/
lemma LocallyFiniteOrder.orderMonoidHom_strictMono {G : Type*} [CommGroup G] [LinearOrder G]
    [IsOrderedMonoid G] [LocallyFiniteOrder G] :
    StrictMono (orderMonoidHom G) :=
  let : LocallyFiniteOrder (Additive G) := ‹LocallyFiniteOrder G›
  fun a b h ↦ orderAddMonoidHom_strictMono h

open scoped WithZero in
/-- Any nontrivial linearly ordered abelian group with zero that is locally finite
is isomorphic to `ℤᵐ⁰`. -/
noncomputable
/-
**LocallyFiniteOrder.orderMonoidWithZeroEquiv** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：LocallyFiniteOrder.orderMonoidWithZeroEquiv (G : Type*) [LinearOrderedComm
GroupWithZero G] [LocallyFiniteOrder Gˣ] [Nontrivial Gˣ] : G ≃*o Intᵐ⁰
参数：G : Type*。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def LocallyFiniteOrder.orderMonoidWithZeroEquiv (G : Type*) [LinearOrderedCommGroupWithZero G]
    [LocallyFiniteOrder Gˣ] [Nontrivial Gˣ] : G ≃*o ℤᵐ⁰ :=
  OrderMonoidIso.withZeroUnits.symm.trans (LocallyFiniteOrder.orderMonoidEquiv _).withZero

open scoped WithZero in
/-- Any linearly ordered abelian group with zero that is locally finite embeds into `ℤᵐ⁰`. -/
noncomputable
/-
**LocallyFiniteOrder.orderMonoidWithZeroHom** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：LocallyFiniteOrder.orderMonoidWithZeroHom (G : Type*) [LinearOrderedCommGr
oupWithZero G] [LocallyFiniteOrder Gˣ] : G ->*₀o Intᵐ⁰ where __
参数：G : Type*。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def LocallyFiniteOrder.orderMonoidWithZeroHom (G : Type*) [LinearOrderedCommGroupWithZero G]
    [LocallyFiniteOrder Gˣ] : G →*₀o ℤᵐ⁰ where
  __ := (WithZero.map' (orderMonoidHom Gˣ)).comp
    OrderMonoidIso.withZeroUnits.symm.toMonoidWithZeroHom
  monotone' a b h := by have := (orderMonoidHom Gˣ).monotone'; aesop
/-
**LocallyFiniteOrder.orderMonoidWithZeroHom_strictMono** 是 Mathlib 中的一个引理，位于命名空间
 ``。
形式化陈述：LocallyFiniteOrder.orderMonoidWithZeroHom_strictMono {G : Type*} [LinearOr
deredCommGroupWithZero G] [LocallyFiniteOrder Gˣ] : StrictMono (orderMonoidWithZ
eroHom G)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearOrderedCommMonoidWithZero.toIsOrderedMonoid`：∀ {α : Type u_1} [ins
t : LinearOrderedCommMonoidWithZero α], IsOrderedMonoid α
· 使用引理 `LocallyFiniteOrder.orderMonoidHom_strictMono`：LocallyFiniteOrder.orderMo
noidHom_strictMono {G : Type*} [CommGroup G] [LinearOrder G] [IsOrderedMonoid G]
 [LocallyFiniteOrder G] : StrictMo…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `OrderMonoidIso.instMulEquivClass`：∀ {α : Type u_2} {β : Type u_3} [inst 
: Preorder α] [inst_1 : Preorder β] [inst_2 : Mul α] [inst_3 : Mul β],   MulEqui
vClass (α ≃*o β) α β
· 使用定理 `OrderMonoidIso.withZeroUnits_symm_apply`：∀ {α : Type u_6} [inst : Linear
OrderedCommGroupWithZero α] [inst_1 : DecidablePred fun a => a = 0] (a : α),   O
rderMonoidIso.withZeroUnits.s…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `dif_neg`：∀ {c : Prop} {h : Decidable c} (hnc : ¬c) {α : Sort u} {t : c →
 α} {e : ¬c → α}, dite c t e = e hnc
· 使用定理 `dif_pos`：∀ {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t : c → α
} {e : ¬c → α}, dite c t e = t hc
· 使用定理 `LinearOrderedCommMonoidWithZero.toIsBotZeroClass`：∀ {α : Type u_3} [self
 : LinearOrderedCommMonoidWithZero α], IsBotZeroClass α
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `MonoidWithZeroHomClass.toZeroHomClass`：∀ {F : Type u_7} {α : outParam (T
ype u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : MulZe
roOneClass β} {inst_2 : Fun…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
-/
lemma LocallyFiniteOrder.orderMonoidWithZeroHom_strictMono {G : Type*}
    [LinearOrderedCommGroupWithZero G] [LocallyFiniteOrder Gˣ] :
    StrictMono (orderMonoidWithZeroHom G) := by
  have := orderMonoidHom_strictMono (G := Gˣ)
  intro a b h
  aesop (add simp orderMonoidWithZeroHom)
