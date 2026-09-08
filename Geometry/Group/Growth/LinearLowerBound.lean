/-
Copyright (c) 2024 Yaël Dillies, Patrick Luo, Eric Rodriguez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Patrick Luo, Eric Rodriguez
-/
module

public import Mathlib.Algebra.Group.Action.Pointwise.Finset
public import Mathlib.Algebra.Group.Subgroup.Pointwise
public import Mathlib.Data.Nat.SuccPred

/-!
# Linear lower bound on the growth of a generating set

This file proves that the growth of a set generating an infinite group is at least linear.
-/

public section

open Subgroup
open scoped Pointwise

namespace Finset
variable {G : Type*} [Group G] [DecidableEq G] {X : Finset G} {n : ℕ}

@[to_additive]
/-
**Finset.pow_ssubset_pow_succ_of_pow_ne_closure** 是 Mathlib 中的一个引理，位于命名空间 `Finse
t`。
形式化陈述：pow_ssubset_pow_succ_of_pow_ne_closure (hX₁ : (1 : G) in X) (hX : X.Nontri
vial) (hXclosure : (X ^ n : Set G) != closure (X : Set G)) : X ^ n ⊂ X ^ (n + 1)
参数：hX₁ : (1 : G) in X；hX : X.Nontrivial；hXclosure : (X ^ n : Set G) != closure (
X : Set G)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `pow_zero`：pow_zero (a : M) : a ^ 0 = 1
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用引理 `pow_one`：pow_one (a : M) : a ^ 1 = a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `Finset.Nontrivial.not_subset_singleton`：∀ {α : Type u_1} {s : Finset α} 
{a : α}, s.Nontrivial → ¬s ⊆ {a}
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `LE.le.ssubset_of_ne`：∀ {α : Type u_1} [UsesSetNotationForOrder α] [inst 
: PartialOrder α] {a b : α}, a ⊆ b → a ≠ b → a ⊂ b
· 使用引理 `Finset.pow_subset_pow_right`：pow_subset_pow_right (hs : 1 in s) (hmn : m
 <= n) : s ^ m subseteq s ^ n
· 使用定理 `Nat.le_add_right`：∀ (n k : ℕ), n ≤ n + k
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose₄`：contrapose₄ {p q : Prop} : (q -> 
p) -> (¬ p -> ¬ q)
· 使用引理 `Subgroup.closure_pow`：closure_pow {n : Nat} (hs : 1 in s) (hn : n != 0) 
: closure (s ^ n) = closure s
· 使用定理 `Classical.em`：∀ (p : Prop), p ∨ ¬p
· 使用定理 `Finset.mul_mem_mul`：mul_mem_mul : a in s -> b in t -> a * b in s * t
· 使用定理 `Finset.smul_finset_subset_mul`：∀ {α : Type u_2} [inst : Mul α] [inst_1 :
 DecidableEq α] {s t : Finset α} {a : α}, a ∈ s → a • t ⊆ s * t
· 使用定理 `Finset.eq_of_subset_of_card_le`：eq_of_subset_of_card_le (h : s subseteq 
t) (h₂ : #t <= #s) : s = t
· 使用定理 `Eq.ge`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → b ≤ a
· 使用定理 `Finset.card_smul_finset`：card_smul_finset (a : α) (s : Finset β) : (a • 
s).card = s.card
· 使用定理 `eq_inv_smul_iff`：∀ {G : Type u_3} {α : Type u_5} [inst : Group G] [inst_
1 : MulAction G α] {g : G} {a b : α}, a = g⁻¹ • b ↔ g • a = b
· 使用定理 `mul_inv_cancel`：mul_inv_cancel (a : G) : a * a⁻¹ = 1
· 使用定理 `LE.le.antisymm`：∀ {α : Type u_1} [inst : PartialOrder α] {a b : α}, a ≤ 
b → b ≤ a → a = b
· 使用定理 `Subgroup.subset_closure`：subset_closure : k subseteq closure k
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Subgroup.closure_le`：closure_le : closure k <= K ↔ k subseteq K
· 使用定理 `subset_rfl`：∀ {α : Type u_1} [UsesSetNotationForOrder α] [inst : Preorde
r α] {a : α}, a ⊆ a
（共 42 条，此处仅展示前 30 条）
-/
lemma pow_ssubset_pow_succ_of_pow_ne_closure (hX₁ : (1 : G) ∈ X) (hX : X.Nontrivial)
    (hXclosure : (X ^ n : Set G) ≠ closure (X : Set G)) : X ^ n ⊂ X ^ (n + 1) := by
  obtain rfl | hn := eq_or_ne n 0
  · simpa [ssubset_iff_subset_not_subset, hX₁, -Finset.subset_singleton_iff]
      using! hX.not_subset_singleton
  refine (pow_subset_pow_right hX₁ <| n.le_add_right _).ssubset_of_ne ?_
  contrapose hXclosure with hXn
  rw [← closure_pow (mod_cast hX₁) hn]
  wlog hn₁ : n = 1
  · simp +contextual only [pow_one] at this
    replace hXn d : X ^ (n + d) = X ^ n := by
      induction d with
      | zero => rw [add_zero]
      | succ d hd =>
        rw [pow_add, pow_one] at hXn
        rw [← add_assoc, pow_add, pow_one, hd, ← hXn]
    exact mod_cast this (one_mem_pow hX₁) (hX.pow hn) one_ne_zero
      (by simp [hXn, ← pow_mul, mul_two]) (by simp)
  subst hn₁
  simp only [ne_eq, one_ne_zero, not_false_eq_true, Nat.reduceAdd, pow_one] at *
  let Xgp : Subgroup G :=
  { carrier := X
    mul_mem' := fun {x y} hx hy ↦ by
      norm_cast at *
      simpa [← hXn, ← sq] using! mul_mem_mul hx hy
    one_mem' := hX₁
    inv_mem' := fun {x} hx ↦ by
      norm_cast at *
      have : x • X ⊆ X := by
        simpa [← hXn, add_assoc, ← sq] using! smul_finset_subset_mul (t := X) hx
      have : x • X = X := eq_of_subset_of_card_le this (card_smul_finset ..).ge
      rw [← eq_inv_smul_iff] at this
      rw [this]
      simpa [mem_inv_smul_finset_iff] }
  exact subset_closure.antisymm <| (closure_le Xgp).2 subset_rfl

@[to_additive]
/-
**Finset.pow_right_strictMonoOn** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
形式化陈述：pow_right_strictMonoOn (hX₁ : 1 in X) (hX : X.Nontrivial) : StrictMonoOn (
fun n => X ^ n) {n | (X ^ (n - 1) : Set G) != closure (X : Set G)}
参数：hX₁ : 1 in X；hX : X.Nontrivial。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `strictMonoOn_of_lt_add_one`：strictMonoOn_of_lt_add_one (hs : s.OrdConnec
ted) : (forall a, ¬ IsMax a -> a in s -> a + 1 in s -> f a < f (a + 1)) -> Stric
tMonoOn f s
· 使用定理 `Nat.instIsSuccArchimedean`：IsSuccArchimedean ℕ
· 使用定理 `Nat.eq_zero_or_pos`：∀ (n : ℕ), n = 0 ∨ n > 0
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.sub_eq_zero_of_le`：∀ {n m : ℕ}, n ≤ m → n - m = 0
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `instIsBotZeroClass`：∀ {α : Type u} [inst : AddZeroClass α] [inst_1 : LE 
α] [CanonicallyOrderedAdd α], IsBotZeroClass α
· 使用定理 `pow_zero`：pow_zero (a : M) : a ^ 0 = 1
· 使用定理 `eq_comm`：∀ {α : Sort u_1} {a b : α}, a = b ↔ b = a
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `Set.Nontrivial.not_subset_singleton`：∀ {α : Type u} {s : Set α} {x : α},
 s.Nontrivial → ¬s ⊆ {x}
· 使用定理 `Finset.Nontrivial.coe`：∀ {α : Type u_1} {s : Finset α}, s.Nontrivial → (
↑s).Nontrivial
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `pow_add`：pow_add {b₁ b₂ : Nat} {d : R} (_ : a ^ b₁ = c₁) (_ : a ^ b₂ = c
₂) (_ : c₁ * c₂ = d) : (a : R) ^ (b₁ + b₂) = d
· 使用定理 `Set.pow_mul_subgroupClosure`：∀ {G : Type u_2} [inst : Group G] {s : Set 
G},   s.Nonempty → ∀ (n : ℕ), s ^ n * ↑(Subgroup.closure s) = ↑(Subgroup.closure
 s)
· 使用定理 `Finset.Nonempty.to_set`：∀ {α : Type u_1} {s : Finset α}, s.Nonempty → (↑
s).Nonempty
· 使用定理 `Finset.Nontrivial.nonempty`：∀ {α : Type u_1} {s : Finset α}, s.Nontrivia
l → s.Nonempty
· 使用引理 `Finset.pow_ssubset_pow_succ_of_pow_ne_closure`：pow_ssubset_pow_succ_of_p
ow_ne_closure (hX₁ : (1 : G) in X) (hX : X.Nontrivial) (hXclosure : (X ^ n : Set
 G) != closure (X : Set G)) : X ^ n…
-/
lemma pow_right_strictMonoOn (hX₁ : 1 ∈ X) (hX : X.Nontrivial) :
    StrictMonoOn (fun n ↦ X ^ n) {n | (X ^ (n - 1) : Set G) ≠ closure (X : Set G)} := by
  refine strictMonoOn_of_lt_add_one ⟨?_⟩ fun n _ _ hn ↦
    pow_ssubset_pow_succ_of_pow_ne_closure hX₁ hX hn
  rintro - - n hn m ⟨-, hmn⟩ hm
  apply hn
  obtain rfl | hm₀ := m.eq_zero_or_pos
  · simp [eq_comm (a := (1 : Set _)), coe_set_eq_one, -Set.subset_singleton_iff,
      hX.coe.not_subset_singleton] at hm
  · calc (X : Set G) ^ (n - 1)
    _ = X ^ (n - m) * X ^ (m - 1) := by rw [← pow_add]; congr 1; lia
    _ = closure (X : Set G) := by rw [hm, Set.pow_mul_subgroupClosure hX.nonempty.to_set]

@[to_additive]
/-
**Finset.pow_right_strictMono** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
形式化陈述：pow_right_strictMono (hX₁ : 1 in X) (hXclosure : (closure (X : Set G) : Se
t G).Infinite) : StrictMono fun n => X ^ n
参数：hX₁ : 1 in X；hXclosure : (closure (X : Set G) : Set G).Infinite。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.eq_singleton_or_nontrivial`：eq_singleton_or_nontrivial (ha : a in
 s) : s = {a} ∨ s.Nontrivial
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.coe_singleton`：coe_singleton (a : α) : (({a} : Finset α) : Set α)
 = {a}
· 使用定理 `Subgroup.closure_singleton_one`：closure_singleton_one : closure ({1} : S
et G) = ⊥
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用引理 `Finset.pow_right_strictMonoOn`：pow_right_strictMonoOn (hX₁ : 1 in X) (hX
 : X.Nontrivial) : StrictMonoOn (fun n => X ^ n) {n | (X ^ (n - 1) : Set G) != c
losure (X : Set G)}
-/
lemma pow_right_strictMono (hX₁ : 1 ∈ X) (hXclosure : (closure (X : Set G) : Set G).Infinite) :
    StrictMono fun n ↦ X ^ n := by
  obtain rfl | hX := eq_singleton_or_nontrivial hX₁
  · simp [closure_singleton_one] at hXclosure
  have h n : (X ^ (n - 1) : Set G) ≠ closure (X : Set G) :=
    fun h ↦ by simp [← h, ← coe_pow] at hXclosure
  simpa [h] using pow_right_strictMonoOn hX₁ hX

/-- The growth of a set generating an infinite group is at least linear. -/
@[to_additive /-- The growth of a set generating an infinite group is at least linear. -/]
/-
**Finset.add_one_le_card_pow** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：∀ {G : Type u_1} [inst : Group G] [inst_1 : DecidableEq G] {X : Finset G},
   1 ∈ X → (↑(Subgroup.closure ↑X)).Infinite → ∀ (n : ℕ), n + 1 ≤ (X ^ n).card
参数：↑(Subgroup.closure ↑X)；n : ℕ；X ^ n。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The growth of a set generating an infinite group is at least linear.
-/
lemma add_one_le_card_pow (hX₁ : 1 ∈ X) (hXclosure : (closure (X : Set G) : Set G).Infinite) :
    ∀ n, n + 1 ≤ #(X ^ n)
  | 0 => by simp
  | n + 1 => (add_one_le_card_pow hX₁ hXclosure _).trans_lt <| card_lt_card <|
      pow_right_strictMono hX₁ (by simp [hXclosure]) n.lt_succ_self

end Finset

