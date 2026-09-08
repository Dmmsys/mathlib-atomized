/-
Copyright (c) 2023 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
module

public import Mathlib.Data.Nat.Fib.Basic

/-!
# Zeckendorf's Theorem

This file proves Zeckendorf's theorem: Every natural number can be written uniquely as a sum of
distinct non-consecutive Fibonacci numbers.

## Main declarations

* `List.IsZeckendorfRep`: Predicate for a list to be an increasing sequence of non-consecutive
  natural numbers greater than or equal to `2`, namely a Zeckendorf representation.
* `Nat.greatestFib`: Greatest index of a Fibonacci number less than or equal to some natural.
* `Nat.zeckendorf`: Send a natural number to its Zeckendorf representation.
* `Nat.zeckendorfEquiv`: Zeckendorf's theorem, in the form of an equivalence between natural numbers
  and Zeckendorf representations.

## TODO

We could prove that the order induced by `zeckendorfEquiv` on Zeckendorf representations is exactly
the lexicographic order.

## Tags

fibonacci, zeckendorf, digit
-/

@[expose] public section

open List Nat

-- TODO: The `local` attribute makes this not considered as an instance by linters
@[nolint docBlame]
local instance : IsTrans ℕ fun a b ↦ b + 2 ≤ a where
  trans _a _b _c hba hcb := hcb.trans <| le_self_add.trans hba

namespace List

/-- A list of natural numbers is a Zeckendorf representation (of a natural number) if it is an
increasing sequence of non-consecutive numbers greater than or equal to `2`.

This is relevant for Zeckendorf's theorem, since if we write a natural `n` as a sum of Fibonacci
numbers `(l.map fib).sum`, `IsZeckendorfRep l` exactly means that we can't simplify any expression
of the form `fib n + fib (n + 1) = fib (n + 2)`, `fib 1 = fib 2` or `fib 0 = 0` in the sum. -/
/-
**List.IsZeckendorfRep** 是 Mathlib 中的一个定义，位于命名空间 `List`。
形式化陈述：IsZeckendorfRep (l : List Nat) : Prop
参数：l : List Nat。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A list of natural numbers is a Zeckendorf representation (of a natural number) i
f it is an
increasing sequence of non-consecutive numbers greater than or equal to `2`.

This is relevant for Zeckendorf's theorem, since if we write a natural `n` as a 
sum of Fibonacci
numbers `(l.map fib).sum`, `IsZeckendorfRep l` exactly means that we can't simpl
ify any expression
of the form `fib n + fib (n + 1) = fib (n + 2)`, `fib 1 = fib 2` or `fib 0 = 0` 
in the sum.
-/
def IsZeckendorfRep (l : List ℕ) : Prop := (l ++ [0]).IsChain (fun a b ↦ b + 2 ≤ a)

@[simp]
/-
**List.IsZeckendorfRep_nil** 是 Mathlib 中的一个引理，位于命名空间 `List`。
形式化陈述：IsZeckendorfRep_nil : IsZeckendorfRep []
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
-/
lemma IsZeckendorfRep_nil : IsZeckendorfRep [] := by simp [IsZeckendorfRep]
/-
**List.IsZeckendorfRep.sum_fib_lt** 是 Mathlib 中的一个定理，位于命名空间 `List.IsZeckendorfRe
p`。
形式化陈述：∀ {n : ℕ} {l : List ℕ}, l.IsZeckendorfRep → (∀ a ∈ (l ++ [0]).head?, a < n
) → (List.map Nat.fib l).sum < Nat.fib n
参数：∀ a ∈ (l ++ [0]).head?, a < n；List.map Nat.fib l。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma IsZeckendorfRep.sum_fib_lt : ∀ {n l}, IsZeckendorfRep l → (∀ a ∈ (l ++ [0]).head?, a < n) →
    (l.map fib).sum < fib n
  | _, [], _, hn => fib_pos.2 <| hn _ rfl
  | n, a :: l, hl, hn => by
    simp only [IsZeckendorfRep, cons_append, isChain_iff_pairwise, pairwise_cons] at hl
    have : ∀ b, b ∈ head? (l ++ [0]) → b < a - 1 :=
      fun b hb ↦ lt_tsub_iff_right.2 <| hl.1 _ <| mem_of_mem_head? hb
    simp only [mem_append, mem_singleton, ← isChain_iff_pairwise, or_imp, forall_and, forall_eq,
      zero_add] at hl
    calc
      fib a + (map fib l).sum < fib a + fib (a - 1) := by gcongr; exact sum_fib_lt hl.2 this
      _ ≤ fib n := by
        rw [add_comm, ← fib_add_one (hl.1.2.trans_lt' zero_lt_two).ne']; exact fib_mono (hn _ rfl)

end List

namespace Nat
variable {m n : ℕ}

/-- The greatest index of a Fibonacci number less than or equal to `n`. -/
/-
**Nat.greatestFib** 是 Mathlib 中的一个定义，位于命名空间 `Nat`。
形式化陈述：greatestFib (n : Nat) : Nat
参数：n : Nat。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The greatest index of a Fibonacci number less than or equal to `n`.
-/
def greatestFib (n : ℕ) : ℕ := (n + 1).findGreatest (fun k ↦ fib k ≤ n)
/-
**Nat.fib_greatestFib_le** 是 Mathlib 中的一个引理，位于命名空间 `Nat`。
形式化陈述：fib_greatestFib_le (n : Nat) : fib (greatestFib n) <= n
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Nat.findGreatest_spec`：findGreatest_spec (hmb : m <= n) (hm : P m) : P (
Nat.findGreatest P n)
· 使用定理 `Nat.zero_le`：∀ (n : ℕ), 0 ≤ n
-/
lemma fib_greatestFib_le (n : ℕ) : fib (greatestFib n) ≤ n :=
  findGreatest_spec (P := (fun k ↦ fib k ≤ n)) (zero_le _) <| zero_le _
/-
**Nat.greatestFib_mono** 是 Mathlib 中的一个引理，位于命名空间 `Nat`。
形式化陈述：greatestFib_mono : Monotone greatestFib
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Nat.findGreatest_mono`：findGreatest_mono [DecidablePred Q] (hPQ : forall
 n, P n -> Q n) (hmn : m <= n) : Nat.findGreatest P m <= Nat.findGreatest Q n
· 使用定理 `LE.le.trans'`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, b ≤ a → 
c ≤ b → c ≤ a
· 使用定理 `add_le_add`：∀ {α : Type u_1} [inst : Add α] [inst_1 : Preorder α] [AddLe
ftMono α] [AddRightMono α] {a b c d : α},   a ≤ b → c ≤ d → a + c ≤ b + d
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
-/
lemma greatestFib_mono : Monotone greatestFib :=
  fun _a _b hab ↦ findGreatest_mono (fun _k ↦ hab.trans') <| by gcongr
/-
**Nat.le_greatestFib** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：∀ {m n : ℕ}, m ≤ n.greatestFib ↔ Nat.fib m ≤ n
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `Nat.fib_mono`：fib_mono : Monotone fib
· 使用引理 `Nat.fib_greatestFib_le`：fib_greatestFib_le (n : Nat) : fib (greatestFib 
n) <= n
· 使用引理 `Nat.le_findGreatest`：le_findGreatest (hmb : m <= n) (hm : P m) : m <= Na
t.findGreatest P n
· 使用定理 `Nat.le_fib_add_one`：∀ (n : ℕ), n ≤ Nat.fib n + 1
· 使用定理 `add_le_add`：∀ {α : Type u_1} [inst : Add α] [inst_1 : Preorder α] [AddLe
ftMono α] [AddRightMono α] {a b c d : α},   a ≤ b → c ≤ d → a + c ≤ b + d
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
-/
@[simp] lemma le_greatestFib : m ≤ greatestFib n ↔ fib m ≤ n :=
  ⟨fun h ↦ (fib_mono h).trans <| fib_greatestFib_le _,
    fun h ↦ le_findGreatest (m.le_fib_add_one.trans <| by gcongr) h⟩
/-
**Nat.greatestFib_lt** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：∀ {m n : ℕ}, m.greatestFib < n ↔ m < Nat.fib n
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `lt_iff_lt_of_le_iff_le`：lt_iff_lt_of_le_iff_le {β} [LinearOrder α] [Line
arOrder β] {a b : α} {c d : β} (H : a <= b ↔ c <= d) : b < a ↔ d < c
· 使用定理 `Nat.le_greatestFib`：∀ {m n : ℕ}, m ≤ n.greatestFib ↔ Nat.fib m ≤ n
-/
@[simp] lemma greatestFib_lt : greatestFib m < n ↔ m < fib n :=
  lt_iff_lt_of_le_iff_le le_greatestFib
/-
**Nat.lt_fib_greatestFib_add_one** 是 Mathlib 中的一个引理，位于命名空间 `Nat`。
形式化陈述：lt_fib_greatestFib_add_one (n : Nat) : n < fib (greatestFib n + 1)
参数：n : Nat。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Nat.greatestFib_lt`：∀ {m n : ℕ}, m.greatestFib < n ↔ m < Nat.fib n
· 使用定理 `Nat.lt_succ_self`：∀ (n : ℕ), n < n.succ
-/
lemma lt_fib_greatestFib_add_one (n : ℕ) : n < fib (greatestFib n + 1) :=
  greatestFib_lt.1 <| lt_succ_self _
/-
**Nat.greatestFib_fib** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：∀ {n : ℕ}, n ≠ 1 → (Nat.fib n).greatestFib = n
参数：Nat.fib n。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `Nat.findGreatest_eq_iff`：findGreatest_eq_iff : Nat.findGreatest P k = m 
↔ m <= k ∧ (m != 0 -> P m) ∧ forall ⦃n⦄, m < n -> n <= k -> ¬P n
· 使用定理 `Nat.le_fib_add_one`：∀ (n : ℕ), n ≤ Nat.fib n + 1
· 使用引理 `le_rfl`：le_rfl : a <= a
· 使用定理 `LT.lt.not_ge`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → ¬b
 ≤ a
· 使用定理 `Nat.fib_lt_fib`：∀ {m : ℕ}, 2 ≤ m → ∀ {n : ℕ}, Nat.fib m < Nat.fib n ↔ m 
< n
· 使用定理 `le_add_self`：∀ {α : Type u} [inst : Add α] [inst_1 : LE α] [CanonicallyO
rderedAdd α] {a b : α}, a ≤ b + a
-/
@[simp] lemma greatestFib_fib : ∀ {n}, n ≠ 1 → greatestFib (fib n) = n
  | 0, _ => rfl
  | _n + 2, _ => findGreatest_eq_iff.2
    ⟨le_fib_add_one _, fun _ ↦ le_rfl, fun _m hnm _ ↦ ((fib_lt_fib le_add_self).2 hnm).not_ge⟩
/-
**Nat.greatestFib_eq_zero** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：∀ {n : ℕ}, n.greatestFib = 0 ↔ n = 0
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `Nat.findGreatest_eq_zero_iff`：findGreatest_eq_zero_iff : Nat.findGreates
t P k = 0 ↔ forall ⦃n⦄, 0 < n -> n <= k -> ¬P n
· 使用定理 `zero_lt_one`：∀ {α : Type u_1} [inst : Zero α] [inst_1 : One α] [inst_2 :
 PartialOrder α] [ZeroLEOneClass α] [NeZero 1], 0 < 1
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `le_add_self`：∀ {α : Type u} [inst : Add α] [inst_1 : LE α] [CanonicallyO
rderedAdd α] {a b : α}, a ≤ b + a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
@[simp] lemma greatestFib_eq_zero : greatestFib n = 0 ↔ n = 0 :=
  ⟨fun h ↦ by simpa using findGreatest_eq_zero_iff.1 h zero_lt_one le_add_self, by rintro rfl; rfl⟩
/-
**Nat.greatestFib_ne_zero** 是 Mathlib 中的一个引理，位于命名空间 `Nat`。
形式化陈述：greatestFib_ne_zero : greatestFib n != 0 ↔ n != 0
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.not`：∀ {a b : Prop}, (a ↔ b) → (¬a ↔ ¬b)
· 使用定理 `Nat.greatestFib_eq_zero`：∀ {n : ℕ}, n.greatestFib = 0 ↔ n = 0
-/
lemma greatestFib_ne_zero : greatestFib n ≠ 0 ↔ n ≠ 0 := greatestFib_eq_zero.not
/-
**Nat.greatestFib_pos** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：∀ {n : ℕ}, 0 < n.greatestFib ↔ 0 < n
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LinearOrderedCommMonoidWithZero.toIsBotZeroClass`：∀ {α : Type u_3} [self
 : LinearOrderedCommMonoidWithZero α], IsBotZeroClass α
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
@[simp] lemma greatestFib_pos : 0 < greatestFib n ↔ 0 < n := by simp [pos_iff_ne_zero]
/-
**Nat.greatestFib_sub_fib_greatestFib_le_greatestFib** 是 Mathlib 中的一个引理，位于命名空间 `
Nat`。
形式化陈述：greatestFib_sub_fib_greatestFib_le_greatestFib (hn : n != 0) : greatestFib
 (n - fib (greatestFib n)) <= greatestFib n - 2
参数：hn : n != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.lt_succ_iff`：∀ {m n : ℕ}, m < n.succ ↔ m ≤ n
· 使用定理 `Nat.greatestFib_lt`：∀ {m n : ℕ}, m.greatestFib < n ↔ m < Nat.fib n
· 使用定理 `tsub_lt_iff_right`：tsub_lt_iff_right (hbc : b <= a) : a - b < c ↔ a < c 
+ b
· 使用定理 `CanonicallyOrderedAdd.toExistsAddOfLE`：∀ {α : Type u_1} {inst : Add α} {
inst_1 : LE α} [self : CanonicallyOrderedAdd α], ExistsAddOfLE α
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `IsLeftCancelAdd.addLeftReflectLE_of_addLeftReflectLT`：∀ (N : Type u_2) [
inst : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftReflectLT N]
, AddLeftReflectLE N
· 使用定理 `AddLeftCancelSemigroup.toIsLeftCancelAdd`：∀ {G : Type u} [self : AddLeft
CancelSemigroup G], IsLeftCancelAdd G
· 使用引理 `Nat.fib_greatestFib_le`：fib_greatestFib_le (n : Nat) : fib (greatestFib 
n) <= n
· 使用定理 `Nat.sub_succ`：∀ (n m : ℕ), n - m.succ = (n - m).pred
· 使用定理 `Nat.succ_pred`：∀ {a : ℕ}, a ≠ 0 → a.pred.succ = a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `Ne.bot_lt`：∀ {α : Type u} [inst : PartialOrder α] [inst_1 : OrderBot α] 
{a : α}, a ≠ ⊥ → ⊥ < a
· 使用定理 `Nat.fib_add_one`：∀ {n : ℕ}, n ≠ 0 → Nat.fib (n + 1) = Nat.fib (n - 1) + 
Nat.fib n
· 使用引理 `Nat.lt_fib_greatestFib_add_one`：lt_fib_greatestFib_add_one (n : Nat) : n
 < fib (greatestFib n + 1)
-/
lemma greatestFib_sub_fib_greatestFib_le_greatestFib (hn : n ≠ 0) :
    greatestFib (n - fib (greatestFib n)) ≤ greatestFib n - 2 := by
  rw [← Nat.lt_succ_iff, greatestFib_lt, tsub_lt_iff_right n.fib_greatestFib_le, Nat.sub_succ,
    succ_pred, ← fib_add_one]
  · exact n.lt_fib_greatestFib_add_one
  · simpa
  · simpa [← succ_le_iff, tsub_eq_zero_iff_le] using hn.bot_lt
/-
**Nat.zeckendorf_aux** 是 Mathlib 中的一个引理，位于命名空间 `Nat`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private lemma zeckendorf_aux (hm : 0 < m) : m - fib (greatestFib m) < m :=
tsub_lt_self hm <| fib_pos.2 <| findGreatest_pos.2 ⟨1, zero_lt_one, le_add_self, hm⟩

/-- The Zeckendorf representation of a natural number.

Note: For unfolding, you should use the equational lemmas `Nat.zeckendorf_zero` and
`Nat.zeckendorf_of_pos` instead of the autogenerated one. -/
/-
**Nat.zeckendorf** 是 Mathlib 中的一个定义，位于命名空间 `Nat`。
形式化陈述：zeckendorf : Nat -> List Nat | 0 => [] | m@(_ + 1) => letI a
该定义给出了一等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The Zeckendorf representation of a natural number.

Note: For unfolding, you should use the equational lemmas `Nat.zeckendorf_zero` 
and
`Nat.zeckendorf_of_pos` instead of the autogenerated one.
-/
def zeckendorf : ℕ → List ℕ
  | 0 => []
  | m@(_ + 1) =>
    letI a := greatestFib m
    a :: zeckendorf (m - fib a)
/-
**Nat.zeckendorf_zero** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：Nat.zeckendorf 0 = []
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.zeckendorf.eq_1`：Nat.zeckendorf 0 = []
-/
@[simp] lemma zeckendorf_zero : zeckendorf 0 = [] := zeckendorf.eq_1 ..
/-
**Nat.zeckendorf_succ** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：∀ (n : ℕ), (n + 1).zeckendorf = (n + 1).greatestFib :: (n + 1 - Nat.fib (n
 + 1).greatestFib).zeckendorf
参数：n : ℕ；n + 1；n + 1。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.zeckendorf.eq_2`：∀ (n : ℕ), n.succ.zeckendorf = n.succ.greatestFib :
: (n.succ - Nat.fib n.succ.greatestFib).zeckendorf
-/
@[simp] lemma zeckendorf_succ (n : ℕ) :
    zeckendorf (n + 1) = greatestFib (n + 1) :: zeckendorf (n + 1 - fib (greatestFib (n + 1))) :=
  zeckendorf.eq_2 ..
/-
**Nat.zeckendorf_of_pos** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：∀ {n : ℕ}, 0 < n → n.zeckendorf = n.greatestFib :: (n - Nat.fib n.greatest
Fib).zeckendorf
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.zeckendorf_succ`：∀ (n : ℕ), (n + 1).zeckendorf = (n + 1).greatestFib
 :: (n + 1 - Nat.fib (n + 1).greatestFib).zeckendorf
-/
@[simp] lemma zeckendorf_of_pos : ∀ {n}, 0 < n →
    zeckendorf n = greatestFib n :: zeckendorf (n - fib (greatestFib n))
  | _n + 1, _ => zeckendorf_succ _
/-
**Nat.isZeckendorfRep_zeckendorf** 是 Mathlib 中的一个引理，位于命名空间 `Nat`。
形式化陈述：isZeckendorfRep_zeckendorf : forall n, (zeckendorf n).IsZeckendorfRep | 0 
=> by simp only [zeckendorf_zero, IsZeckendorfRep_nil] | n + 1 => by rw [zeckend
orf_succ]; rw [IsZeckendorfRep]; rw [List.cons_append] refine (isZeckendorfRep_z
eckendorf _).cons (fun a ha => ?_) obtain h | h
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.zeckendorf_zero`：Nat.zeckendorf 0 = []
· 使用定理 `Nat.zeckendorf_succ`：∀ (n : ℕ), (n + 1).zeckendorf = (n + 1).greatestFib
 :: (n + 1 - Nat.fib (n + 1).greatestFib).zeckendorf
· 使用定理 `List.IsZeckendorfRep.eq_1`：∀ (l : List ℕ), l.IsZeckendorfRep = List.IsCh
ain (fun a b => b + 2 ≤ a) (l ++ [0])
· 使用定理 `List.cons_append`：∀ {α : Type u} {a : α} {as bs : List α}, a :: as ++ bs
 = a :: (as ++ bs)
· 使用定理 `List.IsChain.cons`：∀ {α : Type u_1} {R : α → α → Prop} {x : α} {l : List
 α},   List.IsChain R l → (∀ y ∈ l.head?, R x y) → List.IsChain R (x :: l)
· 使用定理 `IsLeftCancelAdd.addLeftReflectLE_of_addLeftReflectLT`：∀ (N : Type u_2) [
inst : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftReflectLT N]
, AddLeftReflectLE N
· 使用定理 `instIsLeftCancelAddOfAddLeftReflectLE`：∀ {α : Type u_1} [inst : Add α] [
inst_1 : PartialOrder α] [AddLeftReflectLE α], IsLeftCancelAdd α
· 使用定理 `IsOrderedCancelAddMonoid.toAddLeftReflectLE`：∀ {α : Type u_2} [inst : Ad
dCommMonoid α] [inst_1 : Preorder α] [IsOrderedCancelAddMonoid α], AddLeftReflec
tLE α
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `or_true`：∀ (p : Prop), (p ∨ True) = True
· 使用定理 `IsRightCancelAdd.addRightStrictMono_of_addRightMono`：∀ (N : Type u_2) [i
nst : Add N] [IsRightCancelAdd N] [inst_2 : PartialOrder N] [AddRightMono N], Ad
dRightStrictMono N
· 使用定理 `instIsRightCancelAddOfAddRightReflectLE`：∀ {α : Type u_1} [inst : Add α]
 [inst_1 : PartialOrder α] [AddRightReflectLE α], IsRightCancelAdd α
· 使用定理 `addRightReflectLE_of_addLeftReflectLE`：∀ (N : Type u_2) [inst : AddCommS
emigroup N] [inst_1 : LE N] [AddLeftReflectLE N], AddRightReflectLE N
· 使用定理 `AddLeftCancelSemigroup.toIsLeftCancelAdd`：∀ {G : Type u} [self : AddLeft
CancelSemigroup G], IsLeftCancelAdd G
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `contravariant_swap_add_of_contravariant_add`：∀ (N : Type u_2) (r : N → N
 → Prop) [inst : AddCommSemigroup N] [ContravariantClass N N (fun x1 x2 => x1 + 
x2) r],   ContravariantClass N N …
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
· 使用定理 `Nat.eq_zero_or_pos`：∀ (n : ℕ), n = 0 ∨ n > 0
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Nat.le_greatestFib`：∀ {m n : ℕ}, m ≤ n.greatestFib ↔ Nat.fib m ≤ n
· 使用定理 `le_add_self`：∀ {α : Type u} [inst : Add α] [inst_1 : LE α] [CanonicallyO
rderedAdd α] {a b : α}, a ≤ b + a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `add_le_of_le_tsub_right_of_le`：add_le_of_le_tsub_right_of_le (h : b <= c
) (h2 : a <= c - b) : a + b <= c
· 使用定理 `CanonicallyOrderedAdd.toExistsAddOfLE`：∀ {α : Type u_1} {inst : Add α} {
inst_1 : LE α} [self : CanonicallyOrderedAdd α], ExistsAddOfLE α
· 使用引理 `Nat.greatestFib_sub_fib_greatestFib_le_greatestFib`：greatestFib_sub_fib_
greatestFib_le_greatestFib (hn : n != 0) : greatestFib (n - fib (greatestFib n))
 <= greatestFib n - 2
（共 34 条，此处仅展示前 30 条）
-/
lemma isZeckendorfRep_zeckendorf : ∀ n, (zeckendorf n).IsZeckendorfRep
  | 0 => by simp only [zeckendorf_zero, IsZeckendorfRep_nil]
  | n + 1 => by
    rw [zeckendorf_succ, IsZeckendorfRep, List.cons_append]
    refine (isZeckendorfRep_zeckendorf _).cons (fun a ha ↦ ?_)
    obtain h | h := eq_zero_or_pos (n + 1 - fib (greatestFib (n + 1)))
    · simp only [h, zeckendorf_zero, nil_append, head?_cons, Option.mem_some_iff] at ha
      subst ha
      exact le_greatestFib.2 le_add_self
    rw [zeckendorf_of_pos h, cons_append, head?_cons, Option.mem_some_iff] at ha
    subst a
    exact add_le_of_le_tsub_right_of_le (le_greatestFib.2 le_add_self)
      (greatestFib_sub_fib_greatestFib_le_greatestFib n.succ_ne_zero)
/-
**Nat.zeckendorf_sum_fib** 是 Mathlib 中的一个引理，位于命名空间 `Nat`。
形式化陈述：zeckendorf_sum_fib : forall {l}, IsZeckendorfRep l -> zeckendorf (l.map fi
b).sum = l | [], _ => by simp only [map_nil, List.sum_nil, zeckendorf_zero] | a 
:: l, hl => by have hl'
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma zeckendorf_sum_fib : ∀ {l}, IsZeckendorfRep l → zeckendorf (l.map fib).sum = l
  | [], _ => by simp only [map_nil, List.sum_nil, zeckendorf_zero]
  | a :: l, hl => by
    have hl' := hl
    simp only [IsZeckendorfRep, cons_append, isChain_iff_pairwise, pairwise_cons, mem_append,
      mem_singleton, or_imp, forall_and, forall_eq, zero_add] at hl
    rw [← isChain_iff_pairwise] at hl
    have ha : 0 < a := hl.1.2.trans_lt' zero_lt_two
    suffices h : greatestFib (fib a + sum (map fib l)) = a by
      simp only [map, List.sum_cons, add_pos_iff, fib_pos.2 ha, true_or, zeckendorf_of_pos, h,
      add_tsub_cancel_left, zeckendorf_sum_fib hl.2]
    simp only [add_comm, add_assoc, greatestFib, findGreatest_eq_iff, ne_eq, ha.ne',
      not_false_eq_true, le_add_iff_nonneg_left, _root_.zero_le, forall_true_left, not_le, true_and]
    refine ⟨le_add_of_le_right <| le_fib_add_one _, fun n hn _ ↦ ?_⟩
    rw [add_comm, ← List.sum_cons, ← map_cons]
    exact hl'.sum_fib_lt (by simpa)
/-
**Nat.sum_zeckendorf_fib** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：∀ (n : ℕ), (List.map Nat.fib n.zeckendorf).sum = n
参数：n : ℕ；List.map Nat.fib n.zeckendorf。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.zeckendorf.induct`：∀ (motive : ℕ → Prop),   motive 0 → (∀ (n : ℕ), m
otive (n + 1 - Nat.fib (n + 1).greatestFib) → motive n.succ) → ∀ (a : ℕ), motive
 a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.zeckendorf_zero`：Nat.zeckendorf 0 = []
· 使用定理 `List.map_nil`：∀ {α : Type u} {β : Type v} {f : α → β}, List.map f [] = [
]
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Nat.zeckendorf_succ`：∀ (n : ℕ), (n + 1).zeckendorf = (n + 1).greatestFib
 :: (n + 1 - Nat.fib (n + 1).greatestFib).zeckendorf
· 使用定理 `List.map_cons`：∀ {α : Type u} {β : Type v} {f : α → β} {a : α} {l : List
 α}, List.map f (a :: l) = f a :: List.map f l
· 使用定理 `add_tsub_cancel_of_le`：add_tsub_cancel_of_le (h : a <= b) : a + (b - a) 
= b
· 使用定理 `CanonicallyOrderedAdd.toExistsAddOfLE`：∀ {α : Type u_1} {inst : Add α} {
inst_1 : LE α} [self : CanonicallyOrderedAdd α], ExistsAddOfLE α
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
-/
@[simp] lemma sum_zeckendorf_fib (n : ℕ) : (n.zeckendorf.map fib).sum = n := by
  induction n using zeckendorf.induct <;> simp_all [fib_greatestFib_le]

/-- **Zeckendorf's Theorem** as an equivalence between natural numbers and Zeckendorf
representations. Every natural number can be written uniquely as a sum of non-consecutive Fibonacci
numbers (if we forget about the first two terms `F₀ = 0`, `F₁ = 1`). -/
/-
**Nat.zeckendorfEquiv** 是 Mathlib 中的一个定义，位于命名空间 `Nat`。
形式化陈述：zeckendorfEquiv : Nat ≃ {l // IsZeckendorfRep l} where toFun n
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用引理 `Nat.isZeckendorfRep_zeckendorf`：isZeckendorfRep_zeckendorf : forall n, (
zeckendorf n).IsZeckendorfRep | 0 => by simp only [zeckendorf_zero, IsZeckendorf
Rep_nil] | n + 1 => …
· 使用定理 `Nat.sum_zeckendorf_fib`：∀ (n : ℕ), (List.map Nat.fib n.zeckendorf).sum =
 n

--- 原说明 ---
**Zeckendorf's Theorem** as an equivalence between natural numbers and Zeckendor
f
representations. Every natural number can be written uniquely as a sum of non-co
nsecutive Fibonacci
numbers (if we forget about the first two terms `F₀ = 0`, `F₁ = 1`).
-/
def zeckendorfEquiv : ℕ ≃ {l // IsZeckendorfRep l} where
  toFun n := ⟨zeckendorf n, isZeckendorfRep_zeckendorf _⟩
  invFun l := (map fib l).sum
  left_inv := sum_zeckendorf_fib
  right_inv l := Subtype.ext <| zeckendorf_sum_fib l.2

end Nat

