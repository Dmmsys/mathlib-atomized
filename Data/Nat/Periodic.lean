/-
Copyright (c) 2021 Bolton Bailey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bolton Bailey
-/
module

public import Mathlib.Algebra.Ring.Periodic
public import Mathlib.Data.Nat.Count

/-!
# Periodic Functions on ℕ

This file identifies a few functions on `ℕ` which are periodic, and also proves a lemma about
periodic predicates which helps determine their cardinality when filtering intervals over them.
-/

public section

assert_not_exists TwoSidedIdeal

namespace Nat

open Function

/-
**Nat.periodic_gcd** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：periodic_gcd (a : Nat) : Periodic (gcd a) a
参数：a : Nat。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.gcd_add_self_right`：∀ (m n : ℕ), m.gcd (n + m) = m.gcd n
-/
theorem periodic_gcd (a : ℕ) : Periodic (gcd a) a :=
  a.gcd_add_self_right
/-
**Nat.periodic_coprime** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：periodic_coprime (a : Nat) : Periodic (Coprime a) a
参数：a : Nat。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `eq_iff_iff`：∀ {a b : Prop}, a = b ↔ (a ↔ b)
· 使用定理 `Nat.coprime_add_self_right`：coprime_add_self_right {m n : Nat} : Coprime
 m (n + m) ↔ Coprime m n
-/
theorem periodic_coprime (a : ℕ) : Periodic (Coprime a) a :=
  fun _ ↦ eq_iff_iff.mpr coprime_add_self_right
/-
**Nat.periodic_mod** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：periodic_mod (a : Nat) : Periodic (fun n => n % a) a
参数：a : Nat。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.add_mod_right`：∀ (x z : ℕ), (x + z) % z = x % z
-/
theorem periodic_mod (a : ℕ) : Periodic (fun n => n % a) a :=
  (add_mod_right · a)
/-
**Nat._root_.Function.Periodic.map_mod_nat** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.Function.Periodic.map_mod_nat {α : Type*} {f : ℕ → α} {a : ℕ} (hf : Periodic f a) :
    ∀ n, f (n % a) = f n := fun n => by
  conv_rhs => rw [← n.mod_add_div a, mul_comm, ← Nat.nsmul_eq_mul, hf.nsmul]

section Multiset

open Multiset

/-- An interval of length `a` filtered over a periodic predicate of period `a` has cardinality
equal to the number naturals below `a` for which `p a` is true. -/
/-
**Nat.filter_multiset_Ico_card_eq_of_periodic** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：filter_multiset_Ico_card_eq_of_periodic (n a : Nat) (p : Nat -> Prop) [Dec
idablePred p] (pp : Periodic p a) : card (filter p (Ico n (n + a))) = a.count p
参数：n a : Nat；p : Nat -> Prop；pp : Periodic p a。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.count_eq_card_filter_range`：count_eq_card_filter_range (n : Nat) : c
ount p n = #{x in range n | p x}
· 使用定理 `Finset.card.eq_1`：∀ {α : Type u_1} (s : Finset α), s.card = s.val.card
· 使用定理 `Finset.filter_val`：∀ {α : Type u_1} (p : α → Prop) [inst : DecidablePred
 p] (s : Finset α),   (Finset.filter p s).val = Multiset.filter p s.val
· 使用定理 `Finset.range_val`：range_val (n : Nat) : (range n).1 = Multiset.range n
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.multiset_Ico_map_mod`：multiset_Ico_map_mod (n a : Nat) : (Multiset.I
co n (n + a)).map (· % a) = Multiset.range a
· 使用定理 `Multiset.map_count_True_eq_filter_card`：map_count_True_eq_filter_card (s
 : Multiset α) (p : α -> Prop) [DecidablePred p] : (s.map p).count True = card (
s.filter p)
· 使用定理 `Multiset.map_map`：map_map (g : β -> γ) (f : α -> β) (s : Multiset α) : m
ap g (map f s) = map (g ∘ f) s
· 使用定理 `Subsingleton.elim`：∀ {α : Sort u} [h : Subsingleton α] (a b : α), a = b
· 使用定理 `Pi.instSubsingleton`：∀ {α : Sort u} {β : α → Sort v} [∀ (a : α), Subsing
leton (β a)], Subsingleton ((a : α) → β a)
· 使用定理 `instSubsingletonDecidable`：∀ (p : Prop), Subsingleton (Decidable p)
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Function.Periodic.map_mod_nat`：∀ {α : Type u_1} {f : ℕ → α} {a : ℕ}, Fun
ction.Periodic f a → ∀ (n : ℕ), f (n % a) = f n

--- 原说明 ---
An interval of length `a` filtered over a periodic predicate of period `a` has c
ardinality
equal to the number naturals below `a` for which `p a` is true.
-/
theorem filter_multiset_Ico_card_eq_of_periodic (n a : ℕ) (p : ℕ → Prop) [DecidablePred p]
    (pp : Periodic p a) : card (filter p (Ico n (n + a))) = a.count p := by
  rw [count_eq_card_filter_range, Finset.card, Finset.filter_val, Finset.range_val, ←
    multiset_Ico_map_mod n, ← map_count_True_eq_filter_card, ← map_count_True_eq_filter_card,
    map_map]
  congr; funext n
  exact (pp.map_mod_nat n).symm

end Multiset

section Finset

open Finset

/-- An interval of length `a` filtered over a periodic predicate of period `a` has cardinality
equal to the number naturals below `a` for which `p a` is true. -/
/-
**Nat.filter_Ico_card_eq_of_periodic** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：filter_Ico_card_eq_of_periodic (n a : Nat) (p : Nat -> Prop) [DecidablePre
d p] (pp : Periodic p a) : ((Ico n (n + a)).filter p).card = a.count p
参数：n a : Nat；p : Nat -> Prop；pp : Periodic p a。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.filter_multiset_Ico_card_eq_of_periodic`：filter_multiset_Ico_card_eq
_of_periodic (n a : Nat) (p : Nat -> Prop) [DecidablePred p] (pp : Periodic p a)
 : card (filter p (Ico n (n + a))…

--- 原说明 ---
An interval of length `a` filtered over a periodic predicate of period `a` has c
ardinality
equal to the number naturals below `a` for which `p a` is true.
-/
theorem filter_Ico_card_eq_of_periodic (n a : ℕ) (p : ℕ → Prop) [DecidablePred p]
    (pp : Periodic p a) : ((Ico n (n + a)).filter p).card = a.count p :=
  n.filter_multiset_Ico_card_eq_of_periodic a p pp

end Finset

end Nat

