/-
Copyright (c) 2018 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes, Yaël Dillies
-/
module

public import Mathlib.Algebra.Field.GeomSum
public import Mathlib.Algebra.Order.Archimedean.Basic
public import Mathlib.Algebra.Order.BigOperators.Ring.Finset
public import Mathlib.Algebra.Order.CauSeq.Basic

/-!
# Cauchy sequences and big operators

This file proves some more lemmas about basic Cauchy sequences that involve finite sums.
-/

public section

open Finset IsAbsoluteValue

namespace IsCauSeq
variable {α β : Type*} [Field α] [LinearOrder α] [IsStrictOrderedRing α] [Ring β]
  {abv : β → α} [IsAbsoluteValue abv]
  {f g : ℕ → β} {a : ℕ → α}

/-
**IsCauSeq.of_abv_le** 是 Mathlib 中的一个引理，位于命名空间 `IsCauSeq`。
形式化陈述：of_abv_le (n : Nat) (hm : forall m, n <= m -> abv (f m) <= a m) : IsCauSeq
 abs (fun n => ∑ i in range n, a i) -> IsCauSeq abv fun n => ∑ i in range n, f i
参数：n : Nat；hm : forall m, n <= m -> abv (f m) <= a m。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用引理 `div_pos`：div_pos (ha : 0 < a) (hb : 0 < b) : 0 < a / b
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `instNontrivialOfCharZero`：∀ {α : Type u_1} [inst : AddMonoidWithOne α] [
CharZero α], Nontrivial α
· 使用定理 `IsStrictOrderedRing.toCharZero`：∀ {R : Type u} [inst : Semiring R] [inst
_1 : PartialOrder R] [IsStrictOrderedRing R], CharZero R
· 使用引理 `le_trans`：le_trans : a <= b -> b <= c -> a <= c
· 使用定理 `le_max_right`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), b ≤ max
 a b
· 使用定理 `abs_sub_le`：∀ {G : Type u_1} [inst : AddCommGroup G] [inst_1 : LinearOrd
er G] [IsOrderedAddMonoid G] (a b c : G),   |a - c| ≤ |a - b| + |b - c|
· 使用定理 `IsOrderedRing.toIsOrderedAddMonoid`：∀ {R : Type u_1} {inst : Semiring R}
 {inst_1 : PartialOrder R} [self : IsOrderedRing R], IsOrderedAddMonoid R
· 使用定理 `add_lt_add`：∀ {α : Type u_1} [inst : Add α] [inst_1 : Preorder α] [AddLe
ftStrictMono α] [AddRightStrictMono α] {a b c d : α},   a < b → c < d → a + c < 
…
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
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用引理 `lt_of_le_of_lt`：lt_of_le_of_lt (hab : a <= b) (hbc : b < c) : a < c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `tsub_eq_iff_eq_add_of_le`：tsub_eq_iff_eq_add_of_le (h : b <= a) : a - b 
= c ↔ a = c + b
· 使用定理 `CanonicallyOrderedAdd.toExistsAddOfLE`：∀ {α : Type u_1} {inst : Add α} {
inst_1 : LE α} [self : CanonicallyOrderedAdd α], ExistsAddOfLE α
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
（共 49 条，此处仅展示前 30 条）
-/
lemma of_abv_le (n : ℕ) (hm : ∀ m, n ≤ m → abv (f m) ≤ a m) :
    IsCauSeq abs (fun n ↦ ∑ i ∈ range n, a i) → IsCauSeq abv fun n ↦ ∑ i ∈ range n, f i := by
  intro hg ε ε0
  obtain ⟨i, hi⟩ := hg (ε / 2) (div_pos ε0 (by simp))
  exists max n i
  intro j ji
  have hi₁ := hi j (le_trans (le_max_right n i) ji)
  have hi₂ := hi (max n i) (le_max_right n i)
  have sub_le :=
    abs_sub_le (∑ k ∈ range j, a k) (∑ k ∈ range i, a k) (∑ k ∈ range (max n i), a k)
  have := add_lt_add hi₁ hi₂
  rw [abs_sub_comm (∑ k ∈ range (max n i), a k), add_halves ε] at this
  refine lt_of_le_of_lt (le_trans (le_trans ?_ (le_abs_self _)) sub_le) this
  generalize hk : j - max n i = k
  clear this hi₂ hi₁ hi ε0 ε hg sub_le
  rw [tsub_eq_iff_eq_add_of_le ji] at hk
  rw [hk]
  dsimp only
  clear hk ji j
  induction k with
  | zero => simp [abv_zero abv]
  | succ k hi =>
    simp only [Nat.succ_add, Nat.succ_eq_add_one, Finset.sum_range_succ_comm]
    simp only [add_assoc, sub_eq_add_neg]
    simp only [sub_eq_add_neg] at hi
    grw [abv_add abv, hm _ (by omega), hi]
/-
**IsCauSeq.of_abv** 是 Mathlib 中的一个引理，位于命名空间 `IsCauSeq`。
形式化陈述：of_abv (hf : IsCauSeq abs fun m => ∑ n in range m, abv (f n)) : IsCauSeq a
bv fun m => ∑ n in range m, f n
参数：hf : IsCauSeq abs fun m => ∑ n in range m, abv (f n)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `IsCauSeq.of_abv_le`：of_abv_le (n : Nat) (hm : forall m, n <= m -> abv (f
 m) <= a m) : IsCauSeq abs (fun n => ∑ i in range n, a i) -> IsCauSeq abv fun n 
=> ∑ i i…
· 使用引理 `le_rfl`：le_rfl : a <= a
-/
lemma of_abv (hf : IsCauSeq abs fun m ↦ ∑ n ∈ range m, abv (f n)) :
    IsCauSeq abv fun m ↦ ∑ n ∈ range m, f n :=
  hf.of_abv_le 0 fun _ _ ↦ le_rfl
/-
**IsCauSeq._root_.cauchy_product** 是 Mathlib 中的一个定理，位于命名空间 `IsCauSeq`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.cauchy_product (ha : IsCauSeq abs fun m ↦ ∑ n ∈ range m, abv (f n))
    (hb : IsCauSeq abv fun m ↦ ∑ n ∈ range m, g n) (ε : α) (ε0 : 0 < ε) :
    ∃ i : ℕ, ∀ j ≥ i,
      abv ((∑ k ∈ range j, f k) * ∑ k ∈ range j, g k -
        ∑ n ∈ range j, ∑ m ∈ range (n + 1), f m * g (n - m)) < ε := by
  let ⟨P, hP⟩ := ha.bounded
  let ⟨Q, hQ⟩ := hb.bounded
  have hP0 : 0 < P := lt_of_le_of_lt (abs_nonneg _) (hP 0)
  have hPε0 : 0 < ε / (2 * P) := div_pos ε0 (mul_pos (show (2 : α) > 0 by simp) hP0)
  let ⟨N, hN⟩ := hb.cauchy₂ hPε0
  have hQε0 : 0 < ε / (4 * Q) :=
    div_pos ε0 (mul_pos (show (0 : α) < 4 by simp) (lt_of_le_of_lt (abv_nonneg _ _) (hQ 0)))
  let ⟨M, hM⟩ := ha.cauchy₂ hQε0
  refine ⟨2 * (max N M + 1), fun K hK ↦ ?_⟩
  have h₁ :
    (∑ m ∈ range K, ∑ k ∈ range (m + 1), f k * g (m - k)) =
      ∑ m ∈ range K, ∑ n ∈ range (K - m), f m * g n := by
    simpa using sum_range_diag_flip K fun m n ↦ f m * g n
  have h₂ :
    (fun i ↦ ∑ k ∈ range (K - i), f i * g k) = fun i ↦ f i * ∑ k ∈ range (K - i), g k := by
    simp [Finset.mul_sum]
  have h₃ :
    ∑ i ∈ range K, f i * ∑ k ∈ range (K - i), g k =
      ∑ i ∈ range K, f i * (∑ k ∈ range (K - i), g k - ∑ k ∈ range K, g k) +
        ∑ i ∈ range K, f i * ∑ k ∈ range K, g k := by
    rw [← sum_add_distrib]; simp [(mul_add _ _ _).symm]
  have two_mul_two : (4 : α) = 2 * 2 := by norm_num
  have hQ0 : Q ≠ 0 := fun h ↦ by simp [h] at hQε0
  have h2Q0 : 2 * Q ≠ 0 := mul_ne_zero two_ne_zero hQ0
  have hε : ε / (2 * P) * P + ε / (4 * Q) * (2 * Q) = ε := by
    rw [← div_div, div_mul_cancel₀ _ (Ne.symm (ne_of_lt hP0)), two_mul_two, mul_assoc, ← div_div,
      div_mul_cancel₀ _ h2Q0, add_halves]
  have hNMK : max N M + 1 < K :=
    lt_of_lt_of_le (by rw [two_mul]; exact lt_add_of_pos_left _ (Nat.succ_pos _)) hK
  have hKN : N < K :=
    calc
      N ≤ max N M := le_max_left _ _
      _ < max N M + 1 := Nat.lt_succ_self _
      _ < K := hNMK
  have hsumlesum :
      (∑ i ∈ range (max N M + 1),
        abv (f i) * abv ((∑ k ∈ range (K - i), g k) - ∑ k ∈ range K, g k)) ≤
      ∑ i ∈ range (max N M + 1), abv (f i) * (ε / (2 * P)) := by
    gcongr with m hmJ
    refine le_of_lt <| hN (K - m) (le_tsub_of_add_le_left <| hK.trans' ?_) K hKN.le
    rw [two_mul]
    gcongr
    · exact (mem_range.1 hmJ).le
    · exact Nat.le_succ_of_le (le_max_left _ _)
  have hsumltP : (∑ n ∈ range (max N M + 1), abv (f n)) < P :=
    calc
      (∑ n ∈ range (max N M + 1), abv (f n)) = |∑ n ∈ range (max N M + 1), abv (f n)| :=
        Eq.symm (abs_of_nonneg (sum_nonneg fun x _ ↦ abv_nonneg abv (f x)))
      _ < P := hP (max N M + 1)
  rw [h₁, h₂, h₃, sum_mul, ← sub_sub, sub_right_comm, sub_self, zero_sub, abv_neg abv]
  refine lt_of_le_of_lt (IsAbsoluteValue.abv_sum _ _ _) ?_
  suffices
    (∑ i ∈ range (max N M + 1),
          abv (f i) * abv ((∑ k ∈ range (K - i), g k) - ∑ k ∈ range K, g k)) +
        ((∑ i ∈ range K, abv (f i) * abv ((∑ k ∈ range (K - i), g k) - ∑ k ∈ range K, g k)) -
          ∑ i ∈ range (max N M + 1),
            abv (f i) * abv ((∑ k ∈ range (K - i), g k) - ∑ k ∈ range K, g k)) <
      ε / (2 * P) * P + ε / (4 * Q) * (2 * Q) by
    rw [hε] at this
    simpa [abv_mul abv] using this
  gcongr
  · exact lt_of_le_of_lt hsumlesum
        (by rw [← sum_mul, mul_comm]; gcongr)
  rw [sum_range_sub_sum_range (le_of_lt hNMK)]
  calc
    (∑ i ∈ range K with max N M + 1 ≤ i,
          abv (f i) * abv ((∑ k ∈ range (K - i), g k) - ∑ k ∈ range K, g k)) ≤
        ∑ i ∈ range K with max N M + 1 ≤ i, abv (f i) * (2 * Q) := by
        gcongr
        rw [sub_eq_add_neg]
        grw [abv_add abv]
        rw [two_mul, abv_neg abv]
        gcongr <;> exact le_of_lt (hQ _)
    _ < ε / (4 * Q) * (2 * Q) := by
        rw [← sum_mul, ← sum_range_sub_sum_range (le_of_lt hNMK)]
        have := lt_of_le_of_lt (abv_nonneg _ _) (hQ 0)
        gcongr
        exact (le_abs_self _).trans_lt <|
          hM _ ((Nat.le_succ_of_le (le_max_right _ _)).trans hNMK.le) _ <|
            Nat.le_succ_of_le <| le_max_right _ _

variable [Archimedean α]
/-
**IsCauSeq.of_decreasing_bounded** 是 Mathlib 中的一个引理，位于命名空间 `IsCauSeq`。
形式化陈述：of_decreasing_bounded (f : Nat -> α) {a : α} {m : Nat} (ham : forall n >= 
m, |f n| <= a) (hnm : forall n >= m, f n.succ <= f n) : IsCauSeq abs f
参数：f : Nat -> α；ham : forall n >= m, |f n| <= a；hnm : forall n >= m, f n.succ <=
 f n。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Archimedean.arch`：∀ {R : Type u_2} {inst : AddCommMonoid R} {inst_1 : Pa
rtialOrder R} [self : Archimedean R] (x : R) {y : R},   0 < y → ∃ n, x ≤ n • y
· 使用引理 `lt_of_lt_of_le`：lt_of_lt_of_le (hab : a < b) (hbc : b <= c) : a < c
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `lt_neg`：∀ {α : Type u} [inst : AddGroup α] [inst_1 : LT α] [AddLeftStric
tMono α] {a b : α} [AddRightStrictMono α],   a < -b ↔ b < -a
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
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `LE.le.trans_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b 
→ b < c → a < c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `neg_sub`：∀ {α : Type u_1} [inst : SubtractionMonoid α] (a b : α), -(a - 
b) = b - a
· 使用定理 `lt_sub_iff_add_lt`：∀ {α : Type u} [inst : AddGroup α] [inst_1 : LT α] [A
ddRightStrictMono α] {a b c : α}, a < c - b ↔ a + b < c
· 使用定理 `add_nsmul`：∀ {M : Type u_2} [inst : AddMonoid M] (a : M) (m n : ℕ), (m +
 n) • a = m • a + n • a
· 使用定理 `one_nsmul`：∀ {M : Type u_2} [inst : AddMonoid M] (a : M), 1 • a = a
· 使用定理 `add_lt_add_of_le_of_lt`：∀ {α : Type u_1} [inst : Add α] [inst_1 : Preord
er α] [AddLeftStrictMono α] [AddRightMono α] {a b c d : α},   a ≤ b → c < d → a 
+ c < b + d
· 使用引理 `lt_of_le_of_lt`：lt_of_le_of_lt (hab : a <= b) (hbc : b < c) : a < c
· 使用定理 `lt_add_of_pos_right`：∀ {α : Type u_1} [inst : AddZeroClass α] [inst_1 : 
LT α] [AddLeftStrictMono α] (a : α) {b : α}, 0 < b → a < a + b
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `neg_le`：∀ {α : Type u} [inst : AddGroup α] [inst_1 : LE α] [AddLeftMono 
α] [AddRightMono α] {a b : α}, -a ≤ b ↔ -b ≤ a
· 使用定理 `le_abs_self`：∀ {α : Type u_1} [inst : Lattice α] [inst_1 : AddGroup α] (
a : α), a ≤ |a|
· 使用定理 `abs_neg`：∀ {α : Type u_1} [inst : Lattice α] [inst_1 : AddGroup α] (a : 
α), |(-a)| = |a|
· 使用定理 `Nat.find_spec`：∀ {p : ℕ → Prop} [inst : DecidablePred p] (H : ∃ n, p n),
 p (Nat.find H)
（共 59 条，此处仅展示前 30 条）
-/
lemma of_decreasing_bounded (f : ℕ → α) {a : α} {m : ℕ} (ham : ∀ n ≥ m, |f n| ≤ a)
    (hnm : ∀ n ≥ m, f n.succ ≤ f n) : IsCauSeq abs f := fun ε ε0 ↦ by
  classical
  let ⟨k, hk⟩ := Archimedean.arch a ε0
  have h : ∃ l, ∀ n ≥ m, a - l • ε < f n :=
    ⟨k + k + 1, fun n hnm ↦
      lt_of_lt_of_le (show a - (k + (k + 1)) • ε < -|f n| from
          lt_neg.1 <| (ham n hnm).trans_lt
              (by
                rw [neg_sub, lt_sub_iff_add_lt, add_nsmul, add_nsmul, one_nsmul]
                exact add_lt_add_of_le_of_lt hk (lt_of_le_of_lt hk (lt_add_of_pos_right _ ε0))))
        (neg_le.2 <| abs_neg (f n) ▸ le_abs_self _)⟩
  let l := Nat.find h
  have hl : ∀ n : ℕ, n ≥ m → f n > a - l • ε := Nat.find_spec h
  have hl0 : l ≠ 0 := fun hl0 ↦
    not_lt_of_ge (ham m le_rfl)
      (lt_of_lt_of_le (by have := hl m (le_refl m); simpa [hl0] using this) (le_abs_self (f m)))
  obtain ⟨i, hi⟩ := not_forall.1 (Nat.find_min h (Nat.pred_lt hl0))
  rw [Classical.not_imp, not_lt] at hi
  exists i
  intro j hj
  have hfij : f j ≤ f i := (Nat.rel_of_forall_rel_succ_of_le_of_le (· ≥ ·) hnm hi.1 hj).le
  rw [abs_of_nonpos (sub_nonpos.2 hfij), neg_sub, sub_lt_iff_lt_add']
  calc
    f i ≤ a - Nat.pred l • ε := hi.2
    _ = a - l • ε + ε := by
      conv =>
        rhs
        rw [← Nat.succ_pred_eq_of_pos (Nat.pos_of_ne_zero hl0), succ_nsmul, sub_add,
          add_sub_cancel_right]
    _ < f j + ε := by gcongr; exact hl _ <| hi.1.trans hj
/-
**IsCauSeq.of_mono_bounded** 是 Mathlib 中的一个引理，位于命名空间 `IsCauSeq`。
形式化陈述：of_mono_bounded (f : Nat -> α) {a : α} {m : Nat} (ham : forall n >= m, |f 
n| <= a) (hnm : forall n >= m, f n <= f n.succ) : IsCauSeq abs f
参数：f : Nat -> α；ham : forall n >= m, |f n| <= a；hnm : forall n >= m, f n <= f n.
succ。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsCauSeq.of_neg`：∀ {α : Type u_1} {β : Type u_2} [inst : Field α] [inst_
1 : LinearOrder α] [inst_2 : IsStrictOrderedRing α]   [inst_3 : Ring β] {abv : β
 → α}…
· 使用引理 `IsCauSeq.of_decreasing_bounded`：of_decreasing_bounded (f : Nat -> α) {a 
: α} {m : Nat} (ham : forall n >= m, |f n| <= a) (hnm : forall n >= m, f n.succ 
<= f n) : IsCauSeq a…
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `abs_neg`：∀ {α : Type u_1} [inst : Lattice α] [inst_1 : AddGroup α] (a : 
α), |(-a)| = |a|
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `IsOrderedRing.toIsOrderedAddMonoid`：∀ {R : Type u_1} {inst : Semiring R}
 {inst_1 : PartialOrder R} [self : IsOrderedRing R], IsOrderedAddMonoid R
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
-/
lemma of_mono_bounded (f : ℕ → α) {a : α} {m : ℕ} (ham : ∀ n ≥ m, |f n| ≤ a)
    (hnm : ∀ n ≥ m, f n ≤ f n.succ) : IsCauSeq abs f :=
  (of_decreasing_bounded (-f) (a := a) (m := m) (by simpa using ham) <| by simpa using hnm).of_neg
/-
**IsCauSeq.geo_series** 是 Mathlib 中的一个引理，位于命名空间 `IsCauSeq`。
形式化陈述：geo_series [Nontrivial β] (x : β) (hx1 : abv x < 1) : IsCauSeq abv fun n =
> ∑ m in range n, x ^ m
参数：x : β；hx1 : abv x < 1。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `IsCauSeq.of_abv`：of_abv (hf : IsCauSeq abs fun m => ∑ n in range m, abv 
(f n)) : IsCauSeq abv fun m => ∑ n in range m, f n
· 使用定理 `IsCauSeq.congr_simp`：∀ {α : Type u_3} [inst : Field α] [inst_1 : LinearO
rder α] [inst_2 : IsStrictOrderedRing α] {β : Type u_4}   [inst_3 : Ring β] (abv
 abv_1 : …
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `IsAbsoluteValue.abv_pow`：abv_pow [Nontrivial R] (abv : R -> S) [IsAbsolu
teValue abv] (a : R) (n : Nat) : abv (a ^ n) = abv a ^ n
· 使用定理 `IsStrictOrderedRing.isDomain`：∀ {R : Type u} [inst : Semiring R] [inst_1
 : LinearOrder R] [IsStrictOrderedRing R] [ExistsAddOfLE R], IsDomain R
· 使用定理 `AddGroup.existsAddOfLE`：∀ (α : Type u) [inst : AddGroup α] [inst_1 : LE 
α], ExistsAddOfLE α
· 使用定理 `geom_sum_eq`：geom_sum_eq (h : x != 1) (n : Nat) : ∑ i in range n, x ^ i 
= (x ^ n - 1) / (x - 1)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `neg_div_neg_eq`：neg_div_neg_eq (a b : R) : -a / -b = a / b
· 使用定理 `neg_sub`：∀ {α : Type u_1} [inst : SubtractionMonoid α] (a b : α), -(a - 
b) = b - a
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `sub_pos`：∀ {α : Type u} [inst : AddGroup α] [inst_1 : LT α] [AddRightStr
ictMono α] {a b : α}, 0 < a - b ↔ b < a
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
· 使用引理 `IsCauSeq.of_mono_bounded`：of_mono_bounded (f : Nat -> α) {a : α} {m : Na
t} (ham : forall n >= m, |f n| <= a) (hnm : forall n >= m, f n <= f n.succ) : Is
CauSeq abs f
· 使用定理 `abs_of_nonneg`：∀ {α : Type u_1} [inst : Lattice α] [inst_1 : AddGroup α]
 {a : α} [AddLeftMono α], 0 ≤ a → |a| = a
· 使用引理 `div_nonneg`：div_nonneg (ha : 0 <= a) (hb : 0 <= b) : 0 <= a / b
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
（共 50 条，此处仅展示前 30 条）
-/
lemma geo_series [Nontrivial β] (x : β) (hx1 : abv x < 1) :
    IsCauSeq abv fun n ↦ ∑ m ∈ range n, x ^ m := by
  have hx1' : abv x ≠ 1 := fun h ↦ by simp [h] at hx1
  refine of_abv ?_
  simp only [abv_pow abv, geom_sum_eq hx1']
  conv in _ / _ => rw [← neg_div_neg_eq, neg_sub, neg_sub]
  have : 0 < 1 - abv x := sub_pos.2 hx1
  refine of_mono_bounded _ (a := (1 : α) / (1 - abv x)) (m := 0) ?_ ?_
  · intro n _
    rw [abs_of_nonneg]
    · gcongr
      exact sub_le_self _ (abv_pow abv x n ▸ abv_nonneg _ _)
    refine div_nonneg (sub_nonneg.2 ?_) (sub_nonneg.2 <| le_of_lt hx1)
    exact pow_le_one₀ (by positivity) hx1.le
  · intro n _
    rw [← one_mul (abv x ^ n), pow_succ']
    gcongr
/-
**IsCauSeq.geo_series_const** 是 Mathlib 中的一个引理，位于命名空间 `IsCauSeq`。
形式化陈述：geo_series_const (a : α) {x : α} (hx1 : |x| < 1) : IsCauSeq abs fun m => ∑
 n in range m, (a * x ^ n)
参数：a : α；hx1 : |x| < 1。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsCauSeq.congr_simp`：∀ {α : Type u_3} [inst : Field α] [inst_1 : LinearO
rder α] [inst_2 : IsStrictOrderedRing α] {β : Type u_4}   [inst_3 : Ring β] (abv
 abv_1 : …
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用引理 `Finset.mul_sum`：mul_sum (s : Finset ι) (f : ι -> R) (a : R) : a * ∑ i in
 s, f i = ∑ i in s, a * f i
· 使用引理 `IsCauSeq.mul`：mul (hf : IsCauSeq abv f) (hg : IsCauSeq abv g) : IsCauSeq
 abv (f * g)
· 使用引理 `IsCauSeq.const`：const (x : β) : IsCauSeq abv fun _ => x
· 使用引理 `IsCauSeq.geo_series`：geo_series [Nontrivial β] (x : β) (hx1 : abv x < 1)
 : IsCauSeq abv fun n => ∑ m in range n, x ^ m
· 使用定理 `instNontrivialOfCharZero`：∀ {α : Type u_1} [inst : AddMonoidWithOne α] [
CharZero α], Nontrivial α
· 使用定理 `IsStrictOrderedRing.toCharZero`：∀ {R : Type u} [inst : Semiring R] [inst
_1 : PartialOrder R] [IsStrictOrderedRing R], CharZero R
-/
lemma geo_series_const (a : α) {x : α} (hx1 : |x| < 1) :
    IsCauSeq abs fun m ↦ ∑ n ∈ range m, (a * x ^ n) := by
  simpa [mul_sum, Pi.mul_def] using (const a).mul (geo_series x hx1)
/-
**IsCauSeq.series_ratio_test** 是 Mathlib 中的一个引理，位于命名空间 `IsCauSeq`。
形式化陈述：series_ratio_test {f : Nat -> β} (n : Nat) (r : α) (hr0 : 0 <= r) (hr1 : r
 < 1) (h : forall m, n <= m -> abv (f m.succ) <= r * abv (f m)) : IsCauSeq abv f
un m => ∑ n in range m, f n
参数：n : Nat；r : α；hr0 : 0 <= r；hr1 : r < 1；h : forall m, n <= m -> abv (f m.succ)
 <= r * abv (f m)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `abs_of_nonneg`：∀ {α : Type u_1} [inst : Lattice α] [inst_1 : AddGroup α]
 {a : α} [AddLeftMono α], 0 ≤ a → |a| = a
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `IsOrderedRing.toIsOrderedAddMonoid`：∀ {R : Type u_1} {inst : Semiring R}
 {inst_1 : PartialOrder R} [self : IsOrderedRing R], IsOrderedAddMonoid R
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用引理 `IsCauSeq.of_abv_le`：of_abv_le (n : Nat) (hm : forall m, n <= m -> abv (f
 m) <= a m) : IsCauSeq abs (fun n => ∑ i in range n, a i) -> IsCauSeq abv fun n 
=> ∑ i i…
· 使用定理 `LE.le.eq_or_lt`：∀ {α : Type u_2} [inst : PartialOrder α] {a b : α}, a ≤ 
b → a = b ∨ a < b
· 使用引理 `lt_of_lt_of_le`：lt_of_lt_of_le (hab : a < b) (hbc : b <= c) : a < c
· 使用定理 `Nat.succ_pos`：∀ (n : ℕ), 0 < n.succ
· 使用定理 `Nat.le_of_succ_le_succ`：∀ {n m : ℕ}, n.succ ≤ m.succ → n ≤ m
· 使用定理 `Nat.succ_pred_eq_of_pos`：∀ {n : ℕ}, 0 < n → n.pred.succ = n
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `inv_zero`：∀ {G₀ : Type u} [inst : GroupWithZero G₀], 0⁻¹ = 0
· 使用定理 `pow_succ`：pow_succ (a : M) (n : Nat) : a ^ (n + 1) = a ^ n * a
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Nat.sub_add_cancel`：∀ {n m : ℕ}, m ≤ n → n - m + m = n
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `tsub_eq_iff_eq_add_of_le`：tsub_eq_iff_eq_add_of_le (h : b <= a) : a - b 
= c ↔ a = c + b
· 使用定理 `CanonicallyOrderedAdd.toExistsAddOfLE`：∀ {α : Type u_1} {inst : Add α} {
inst_1 : LE α} [self : CanonicallyOrderedAdd α], ExistsAddOfLE α
· 使用定理 `IsLeftCancelAdd.addLeftReflectLE_of_addLeftReflectLT`：∀ (N : Type u_2) [
inst : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftReflectLT N]
, AddLeftReflectLE N
· 使用定理 `AddLeftCancelSemigroup.toIsLeftCancelAdd`：∀ {G : Type u} [self : AddLeft
CancelSemigroup G], IsLeftCancelAdd G
· 使用定理 `Nat.zero_add`：∀ (n : ℕ), 0 + n = n
· 使用定理 `mul_right_comm`：mul_right_comm (a b c : G) : a * b * c = a * c * b
· 使用定理 `inv_pow`：∀ {α : Type u_1} [inst : DivisionMonoid α] (a : α) (n : ℕ), a⁻¹
 ^ n = (a ^ n)⁻¹
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `div_eq_mul_inv`：div_eq_mul_inv (a b : G) : a / b = a * b⁻¹
· 使用定理 `mul_div_cancel_right₀`：∀ {M₀ : Type u_1} [inst : MonoidWithZero M₀] [ins
t_1 : Div M₀] [MulDivCancelClass M₀] (a : M₀) {b : M₀},   b ≠ 0 → a * b / b = a
（共 54 条，此处仅展示前 30 条）
-/
lemma series_ratio_test {f : ℕ → β} (n : ℕ) (r : α) (hr0 : 0 ≤ r) (hr1 : r < 1)
    (h : ∀ m, n ≤ m → abv (f m.succ) ≤ r * abv (f m)) :
    IsCauSeq abv fun m ↦ ∑ n ∈ range m, f n := by
  have har1 : |r| < 1 := by rwa [abs_of_nonneg hr0]
  refine (geo_series_const (abv (f n.succ) * r⁻¹ ^ n.succ) har1).of_abv_le n.succ fun m hmn ↦ ?_
  obtain rfl | hr := hr0.eq_or_lt
  · have m_pos := lt_of_lt_of_le (Nat.succ_pos n) hmn
    have := h m.pred (Nat.le_of_succ_le_succ (by rwa [Nat.succ_pred_eq_of_pos m_pos]))
    simpa [Nat.sub_add_cancel m_pos, pow_succ] using this
  generalize hk : m - n.succ = k
  replace hk : m = k + n.succ := (tsub_eq_iff_eq_add_of_le hmn).1 hk
  induction k generalizing m n with
  | zero =>
    rw [hk, Nat.zero_add, mul_right_comm, inv_pow _ _, ← div_eq_mul_inv, mul_div_cancel_right₀]
    positivity
  | succ k ih =>
    have kn : k + n.succ ≥ n.succ := by
      rw [← zero_add n.succ]; exact add_le_add (Nat.zero_le _) (by simp)
    rw [hk, Nat.succ_add, pow_succ r, ← mul_assoc]
    refine
      le_trans (by rw [mul_comm] <;> exact h _ (Nat.le_of_succ_le kn))
        (mul_le_mul_of_nonneg_right ?_ hr0)
    exact ih _ h _ (by simp) rfl

end IsCauSeq

