/-
Copyright (c) 2020 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import Mathlib.Data.ZMod.Basic
public import Mathlib.Tactic.NormNum

/-!
# Some facts about finite rings
-/

public section


open Finset ZMod

section Ring

variable {R : Type*} [Ring R] [Fintype R] [DecidableEq R]

/-
**Finset.univ_of_card_le_two** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Finset.univ_of_card_le_two (h : Fintype.card R <= 2) : (univ : Finset R) =
 {0, 1}
参数：h : Fintype.card R <= 2。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `subsingleton_or_nontrivial`：subsingleton_or_nontrivial (α : Type*) : Sub
singleton α ∨ Nontrivial α
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Subsingleton.elim`：∀ {α : Sort u} [h : Subsingleton α] (a b : α), a = b
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `true_or`：∀ (p : Prop), (True ∨ p) = True
· 使用定理 `Finset.subset_univ`：subset_univ (s : Finset α) : s subseteq univ
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.eq_of_subset_of_card_le`：eq_of_subset_of_card_le (h : s subseteq 
t) (h₂ : #t <= #s) : s = t
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Finset.card_insert_of_notMem`：card_insert_of_notMem (h : a ∉ s) : #(inse
rt a s) = #s + 1
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `Finset.card_singleton`：card_singleton (a : α) : #{a} = 1
-/
lemma Finset.univ_of_card_le_two (h : Fintype.card R ≤ 2) :
    (univ : Finset R) = {0, 1} := by
  rcases subsingleton_or_nontrivial R
  · exact le_antisymm (fun a _ ↦ by simp [Subsingleton.elim a 0]) (Finset.subset_univ _)
  · refine (eq_of_subset_of_card_le (subset_univ _) ?_).symm
    convert! h
    simp
/-
**Finset.univ_of_card_le_three** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Finset.univ_of_card_le_three (h : Fintype.card R <= 3) : (univ : Finset R)
 = {0, 1, -1}
参数：h : Fintype.card R <= 3。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.eq_of_subset_of_card_le`：eq_of_subset_of_card_le (h : s subseteq 
t) (h₂ : #t <= #s) : s = t
· 使用定理 `Finset.subset_univ`：subset_univ (s : Finset α) : s subseteq univ
· 使用引理 `lt_or_eq_of_le`：lt_or_eq_of_le : a <= b -> a < b ∨ a = b
· 使用定理 `Finset.card_le_card`：card_le_card : s subseteq t -> #s <= #t
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Finset.univ_of_card_le_two`：Finset.univ_of_card_le_two (h : Fintype.card
 R <= 2) : (univ : Finset R) = {0, 1}
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Nat.lt_succ_iff`：∀ {m n : ℕ}, m < n.succ ↔ m ≤ n
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `true_or`：∀ (p : Prop), (True ∨ p) = True
· 使用定理 `Fintype.one_lt_card_iff_nontrivial`：one_lt_card_iff_nontrivial : 1 < car
d α ↔ Nontrivial α
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `Finset.card_univ`：Finset.card_univ [Fintype α] : #(univ : Finset α) = Fi
ntype.card α
· 使用定理 `Finset.card_insert_of_notMem`：card_insert_of_notMem (h : a ∉ s) : #(inse
rt a s) = #s + 1
· 使用定理 `or_self`：∀ (p : Prop), (p ∨ p) = p
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `Finset.mem_singleton`：mem_singleton {a b : α} : b in ({a} : Finset α) ↔ 
b = a
· 使用定理 `Nat.prime_three`：prime_three : Prime 3
· 使用定理 `map_ofNat`：map_ofNat [FunLike F R S] [RingHomClass F R S] (f : F) (n : N
at) [Nat.AtLeastTwo n] : (f ofNat(n) : S) = OfNat.ofNat n
· 使用定理 `RingEquivClass.toRingHomClass`：∀ {F : Type u_1} {R : Type u_4} {S : Type
 u_5} [inst : EquivLike F R S] [inst_1 : NonAssocSemiring R]   [inst_2 : NonAsso
cSemiring S] [h : R…
· 使用定理 `RingEquiv.instRingEquivClass`：∀ {R : Type u_4} {S : Type u_5} [inst : Mu
l R] [inst_1 : Mul S] [inst_2 : Add R] [inst_3 : Add S],   RingEquivClass (R ≃+*
 S) R S
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `MonoidWithZeroHomClass.toZeroHomClass`：∀ {F : Type u_7} {α : outParam (T
ype u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : MulZe
roOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
（共 39 条，此处仅展示前 30 条）
-/
lemma Finset.univ_of_card_le_three (h : Fintype.card R ≤ 3) :
    (univ : Finset R) = {0, 1, -1} := by
  refine (eq_of_subset_of_card_le (subset_univ _) ?_).symm
  rcases lt_or_eq_of_le h with h | h
  · apply card_le_card
    rw [Finset.univ_of_card_le_two (Nat.lt_succ_iff.1 h)]
    simp
  · have : Nontrivial R := by
      refine Fintype.one_lt_card_iff_nontrivial.1 ?_
      rw [h]
      simp
    rw [card_univ, h, card_insert_of_notMem, card_insert_of_notMem, card_singleton]
    · rw [mem_singleton]
      intro H
      rw [← add_eq_zero_iff_eq_neg, one_add_one_eq_two] at H
      apply_fun (ringEquivOfPrime R Nat.prime_three h).symm at H
      simp only [map_ofNat, map_zero] at H
      replace H : ((2 : ℕ) : ZMod 3) = 0 := H
      rw [natCast_eq_zero_iff] at H
      norm_num at H
    · simp

end Ring

section MonoidWithZero

variable (M₀ : Type*) [MonoidWithZero M₀] [Nontrivial M₀]

open scoped Classical in
/-
**card_units_lt** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：card_units_lt [Fintype M₀] : Fintype.card M₀ˣ < Fintype.card M₀
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Fintype.card_lt_of_injective_of_notMem`：card_lt_of_injective_of_notMem (
f : α -> β) (h : Function.Injective f) {b : β} (w : b ∉ Set.range f) : card α < 
card β
· 使用定理 `Units.val_injective`：∀ {α : Type u} [inst : Monoid α], Function.Injectiv
e Units.val
· 使用定理 `not_isUnit_zero`：not_isUnit_zero [Nontrivial M₀] : ¬IsUnit (0 : M₀)
-/
theorem card_units_lt [Fintype M₀] : Fintype.card M₀ˣ < Fintype.card M₀ :=
  Fintype.card_lt_of_injective_of_notMem Units.val Units.val_injective not_isUnit_zero
/-
**natCard_units_lt** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：natCard_units_lt [Finite M₀] : Nat.card M₀ˣ < Nat.card M₀
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Fintype.card_eq_nat_card`：∀ {α : Type u_1} {x : Fintype α}, Fintype.card
 α = Nat.card α
· 使用定理 `card_units_lt`：card_units_lt [Fintype M₀] : Fintype.card M₀ˣ < Fintype.c
ard M₀
-/
lemma natCard_units_lt [Finite M₀] : Nat.card M₀ˣ < Nat.card M₀ := by
  have : Fintype M₀ := Fintype.ofFinite M₀
  simpa only [Fintype.card_eq_nat_card] using card_units_lt M₀

variable {M₀}
/-
**orderOf_lt_card** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：orderOf_lt_card [Finite M₀] (a : M₀) : orderOf a < Nat.card M₀
参数：a : M₀。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `IsUnit.unit_spec`：unit_spec (h : IsUnit a) : ↑h.unit = a
· 使用定理 `orderOf_units`：orderOf_units {y : Gˣ} : orderOf (y : G) = orderOf y
· 使用定理 `LE.le.trans_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b 
→ b < c → a < c
· 使用定理 `orderOf_le_card`：orderOf_le_card [Finite G] : orderOf x <= Nat.card G
· 使用定理 `instFiniteUnits`：∀ {α : Type u_1} [inst : Monoid α] [Finite α], Finite α
ˣ
· 使用引理 `natCard_units_lt`：natCard_units_lt [Finite M₀] : Nat.card M₀ˣ < Nat.card
 M₀
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `orderOf_eq_zero_iff'`：orderOf_eq_zero_iff' : orderOf x = 0 ↔ forall n : 
Nat, 0 < n -> x ^ n != 1
· 使用引理 `IsUnit.of_pow_eq_one`：IsUnit.of_pow_eq_one (ha : a ^ n = 1) (hn : n != 0
) : IsUnit a
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `Nat.card_pos`：∀ {α : Type u_1} [Nonempty α] [Finite α], 0 < Nat.card α
· 使用定理 `Nontrivial.to_nonempty`：∀ {α : Type u_1} [Nontrivial α], Nonempty α
-/
lemma orderOf_lt_card [Finite M₀] (a : M₀) : orderOf a < Nat.card M₀ := by
  by_cases h : IsUnit a
  · rw [← h.unit_spec, orderOf_units]
    exact orderOf_le_card.trans_lt <| natCard_units_lt M₀
  · rw [orderOf_eq_zero_iff'.mpr fun n hn ha ↦ h <| IsUnit.of_pow_eq_one ha hn.ne']
    exact Nat.card_pos

end MonoidWithZero

/-
**ZMod.orderOf_lt** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：ZMod.orderOf_lt {n : Nat} (hn : 1 < n) (a : ZMod n) : orderOf a < n
参数：hn : 1 < n；a : ZMod n。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.ne_zero_of_lt`：∀ {b a : ℕ}, b < a → a ≠ 0
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `ZMod.nontrivial_iff`：nontrivial_iff {n : Nat} : Nontrivial (ZMod n) ↔ n 
!= 1
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `LT.lt.trans_eq`：∀ {α : Type u_1} {a b c : α} [inst : LT α], a < b → b = 
c → a < c
· 使用引理 `orderOf_lt_card`：orderOf_lt_card [Finite M₀] (a : M₀) : orderOf a < Nat.
card M₀
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `Nat.card_zmod`：card_zmod (n : Nat) : Nat.card (ZMod n) = n
-/
lemma ZMod.orderOf_lt {n : ℕ} (hn : 1 < n) (a : ZMod n) : orderOf a < n :=
  have : NeZero n := ⟨Nat.ne_zero_of_lt hn⟩
  have : Nontrivial (ZMod n) := nontrivial_iff.mpr hn.ne'
  (orderOf_lt_card a).trans_eq <| Nat.card_zmod n
