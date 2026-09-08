/-
Copyright (c) 2024 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
module

public import Mathlib.Combinatorics.Additive.PluenneckeRuzsa
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Data.Real.Basic
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Positivity.Finset
public import Mathlib.Tactic.Ring

/-!
# Small tripling implies small powers

This file shows that a set with small tripling has small powers, even in non-abelian groups.

## See also

In abelian groups, the Plünnecke-Ruzsa inequality is the stronger statement that small doubling
implies small powers. See `Mathlib/Combinatorics/Additive/PluenneckeRuzsa.lean`.
-/

public section

open Fin MulOpposite
open List hiding tail
open scoped Pointwise

namespace Finset
variable {G : Type*} [DecidableEq G] [Group G] {A : Finset G} {k K : ℝ} {m : ℕ}

@[to_additive]
/-
**Finset.inductive_claim_mul** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private lemma inductive_claim_mul (hm : 3 ≤ m)
    (h : ∀ ε : Fin 3 → ℤ, (∀ i, |ε i| = 1) → #((finRange 3).map fun i ↦ A ^ ε i).prod ≤ k * #A)
    (ε : Fin m → ℤ) (hε : ∀ i, |ε i| = 1) :
    #((finRange m).map fun i ↦ A ^ ε i).prod ≤ k ^ (m - 2) * #A := by
  induction m, hm using Nat.le_induction with
  | base => simpa using h ε hε
  | succ m hm ih =>
    obtain _ | m := m
    · simp at hm
    have hm₀ : m ≠ 0 := by simp at hm; positivity
    have hε₀ i : ε i ≠ 0 := fun h ↦ by simpa [h] using hε i
    obtain rfl | hA := A.eq_empty_or_nonempty
    · simp [hε₀]
    have hk : 0 ≤ k :=
      nonneg_of_mul_nonneg_left ((h 1 (by simp)).trans' (by positivity)) (by positivity)
    let π {n} (δ : Fin n → ℤ) : Finset G := ((finRange _).map fun i ↦ A ^ δ i).prod
    let V : Finset G := π ![-ε 1, -ε 0]
    let W : Finset G := π <| tail <| tail ε
    refine le_of_mul_le_mul_left ?_ (by positivity : (0 : ℝ) < #A)
    calc
      (#A * #(π ε) : ℝ)
        = #A * #(V⁻¹ * W) := by
        simp [π, V, W, List.finRange_succ, Fin.tail, Function.comp_def, mul_assoc]
      _ ≤ #(A * V) * #(A * W) := by norm_cast; exact ruzsa_triangle_inequality_invMul_mul_mul ..
      _ = #(π ![1, -ε 1, -ε 0]) * #(π <| Fin.cons 1 <| tail <| tail ε) := by
        simp [π, V, W, List.finRange_succ, Fin.tail, Function.comp_def]
      _ ≤ (k * #A) * (k ^ (m - 1) * #A) := by
        gcongr
        · exact h ![1, -ε 1, -ε 0] fun i ↦ by fin_cases i <;> simp [hε]
        · exact ih (Fin.cons 1 <| tail <| tail ε) <| Fin.cons (by simp) (by simp [hε, Fin.tail])
      _ = #A * (k ^ m * #A) := by rw [← pow_sub_one_mul hm₀]; ring

@[to_additive]
/-
**Finset.small_neg_pos_pos_mul** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private lemma small_neg_pos_pos_mul (hA : #(A ^ 3) ≤ K * #A) : #(A⁻¹ * A * A) ≤ K ^ 2 * #A := by
  obtain rfl | hA₀ := A.eq_empty_or_nonempty
  · simp
  have : 0 ≤ K := nonneg_of_mul_nonneg_left (hA.trans' <| by positivity) (by positivity)
  refine le_of_mul_le_mul_left ?_ (by positivity : (0 : ℝ) < #A)
  calc
    (#A * #(A⁻¹ * A * A) : ℝ) = #A * #(A⁻¹ * (A * A)) := by rw [mul_assoc]
    _ ≤ #(A * A) * #(A * (A * A)) := by
      norm_cast; exact ruzsa_triangle_inequality_invMul_mul_mul A A (A * A)
    _ = #(A ^ 2) * #(A ^ 3) := by simp [pow_succ']
    _ ≤ (K * #A) * (K * #A) := by
      gcongr
      calc
        (#(A ^ 2) : ℝ) ≤ #(A ^ 3) := mod_cast hA₀.card_pow_mono (by simp)
        _ ≤ K * #A := hA
    _ = #A * (K ^ 2 * #A) := by ring

@[to_additive]
/-
**Finset.small_neg_neg_pos_mul** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private lemma small_neg_neg_pos_mul (hA : #(A ^ 3) ≤ K * #A) : #(A⁻¹ * A⁻¹ * A) ≤ K ^ 2 * #A := by
  rw [← card_inv]
  simpa [mul_assoc] using small_neg_pos_pos_mul (A := A) (K := K) (by simpa)

@[to_additive]
/-
**Finset.small_pos_neg_neg_mul** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private lemma small_pos_neg_neg_mul (hA : #(A ^ 3) ≤ K * #A) : #(A * A⁻¹ * A⁻¹) ≤ K ^ 2 * #A := by
  simpa using small_neg_pos_pos_mul (A := A⁻¹) (by simpa)

@[to_additive]
/-
**Finset.small_pos_pos_neg_mul** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private lemma small_pos_pos_neg_mul (hA : #(A ^ 3) ≤ K * #A) : #(A * A * A⁻¹) ≤ K ^ 2 * #A := by
  rw [← card_inv]
  simpa [mul_assoc] using small_pos_neg_neg_mul (A := A) (K := K) (by simpa)

@[to_additive]
/-
**Finset.small_pos_neg_pos_mul** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private lemma small_pos_neg_pos_mul (hA : #(A ^ 3) ≤ K * #A) : #(A * A⁻¹ * A) ≤ K ^ 3 * #A := by
  obtain rfl | hA₀ := A.eq_empty_or_nonempty
  · simp
  refine le_of_mul_le_mul_left ?_ (by positivity : (0 : ℝ) < #A)
  calc
    (#A * #(A * A⁻¹ * A) : ℝ) ≤ #(A * (A * A⁻¹)) * #(A * A) := by
      norm_cast; simpa using ruzsa_triangle_inequality_invMul_mul_mul (A * A⁻¹) A A
    _ = #(A * A * A⁻¹) * #(A ^ 2) := by simp [pow_succ, mul_assoc]
    _ ≤ (K ^ 2 * #A) * (K * #A) := by
      gcongr
      · exact small_pos_pos_neg_mul hA
      calc
        (#(A ^ 2) : ℝ) ≤ #(A ^ 3) := mod_cast hA₀.card_pow_mono (by simp)
        _ ≤ K * #A := hA
    _ = #A * (K ^ 3 * #A) := by ring

@[to_additive]
/-
**Finset.small_neg_pos_neg_mul** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private lemma small_neg_pos_neg_mul (hA : #(A ^ 3) ≤ K * #A) : #(A⁻¹ * A * A⁻¹) ≤ K ^ 3 * #A := by
  rw [← card_inv]
  simpa [mul_assoc] using small_pos_neg_pos_mul (A := A) (K := K) (by simpa)

/-- If `A` has small tripling, say with constant `K`, then `A` has small alternating powers, in the
sense that `|A^±1 * ... * A^±1|` is at most `|A|` times a constant exponential in the number of
terms in the product.

When `A` is symmetric (`A⁻¹ = A`), the base of the exponential can be lowered from `K ^ 3` to `K`,
where `K` is the tripling constant. See `Finset.small_pow_of_small_tripling`. -/
@[to_additive
/-- If `A` has small tripling, say with constant `K`, then `A` has small alternating powers, in the
sense that `|±A ± ... ± A|` is at most `|A|` times a constant exponential in the number of
terms in the product.

When `A` is symmetric (`-A = A`), the base of the exponential can be lowered from `K ^ 3` to `K`,
where `K` is the tripling constant. See `Finset.small_nsmul_of_small_tripling`. -/]
/-
**Finset.small_alternating_pow_of_small_tripling** 是 Mathlib 中的一个引理，位于命名空间 `Fins
et`。
形式化陈述：small_alternating_pow_of_small_tripling (hm : 3 <= m) (hA : #(A ^ 3) <= K 
* #A) (ε : Fin m -> Int) (hε : forall i, |ε i| = 1) : #((finRange m).map fun i =
> A ^ ε i).prod <= K ^ (3 * (m - 2)) * #A
参数：hm : 3 <= m；hA : #(A ^ 3) <= K * #A；ε : Fin m -> Int；hε : forall i, |ε i| = 1
。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ne_of_gt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用引理 `lt_of_lt_of_le`：lt_of_lt_of_le (hab : a < b) (hbc : b <= c) : a < c
· 使用引理 `Mathlib.Meta.Positivity.pos_of_isNat`：pos_of_isNat {n : Nat} [Semiring A
] [PartialOrder A] [IsOrderedRing A] [Nontrivial A] (h : NormNum.IsNat e n) (w :
 Nat.ble 1 n = true) : 0 <…
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `Mathlib.Meta.NormNum.isNat_ofNat`：isNat_ofNat (α : Type u) [AddMonoidWit
hOne α] {a : α} {n : Nat} (h : n = a) : IsNat a n
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `abs_zero`：∀ {α : Type u_1} [inst : Lattice α] [inst_1 : AddGroup α] [Add
LeftMono α], |0| = 0
· 使用定理 `Int.instNeZeroOfNatOfNat`：∀ {n : ℕ} [NeZero n], NeZero (OfNat.ofNat n)
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Finset.eq_empty_or_nonempty`：eq_empty_or_nonempty (s : Finset α) : s = ∅
 ∨ s.Nonempty
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用引理 `Finset.empty_zpow`：empty_zpow (hn : n != 0) : (∅ : Finset α) ^ n = ∅
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `List.map_const'`：∀ {α : Type u_1} {β : Type u_2} {l : List α} {b : β}, L
ist.map (fun x => b) l = List.replicate l.length b
· 使用定理 `List.length_finRange`：∀ {n : ℕ}, (List.finRange n).length = n
· 使用定理 `List.prod_replicate`：prod_replicate (n : Nat) (a : M) : (replicate n a).
prod = a ^ n
· 使用引理 `Finset.empty_pow`：empty_pow (hn : n != 0) : (∅ : Finset α) ^ n = ∅
· 使用定理 `Nat.cast_zero`：cast_zero : ((0 : Nat) : R) = 0
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `one_le_of_le_mul_right₀`：one_le_of_le_mul_right₀ [MulPosReflectLE α] (hb
 : 0 < b) (h : b <= a * b) : 1 <= a
· 使用定理 `MulPosStrictMono.toMulPosReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [MulPosStrictMono α], MulPosReflectLE α
· 使用定理 `IsStrictOrderedRing.toMulPosStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], MulPosStrictMono 
R
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Nat.cast_pos'`：cast_pos' {n : Nat} : (0 : α) < n ↔ 0 < n
（共 129 条，此处仅展示前 30 条）
-/
lemma small_alternating_pow_of_small_tripling (hm : 3 ≤ m) (hA : #(A ^ 3) ≤ K * #A) (ε : Fin m → ℤ)
    (hε : ∀ i, |ε i| = 1) :
    #((finRange m).map fun i ↦ A ^ ε i).prod ≤ K ^ (3 * (m - 2)) * #A := by
  have hm₀ : m ≠ 0 := by positivity
  have hε₀ i : ε i ≠ 0 := fun h ↦ by simpa [h] using hε i
  obtain rfl | hA₀ := A.eq_empty_or_nonempty
  · simp [hm₀, hε₀]
  have hK₁ : 1 ≤ K :=
    one_le_of_le_mul_right₀ (by positivity)
      (hA.trans' <| by norm_cast; exact card_le_card_pow (by simp))
  rw [pow_mul]
  refine inductive_claim_mul hm (fun δ hδ ↦ ?_) ε hε
  simp only [finRange_succ, Nat.reduceAdd, isValue, finRange_zero, map_nil, List.map_cons,
    succ_zero_eq_one, succ_one_eq_two, List.prod_cons, prod_nil, mul_one, ← mul_assoc]
  simp only [zero_le_one, abs_eq, Int.reduceNeg, forall_iff_succ, isValue, succ_zero_eq_one,
    succ_one_eq_two, IsEmpty.forall_iff, and_true] at hδ
  have : K ^ 2 ≤ K ^ 3 := by gcongr; simp
  obtain ⟨hδ₀ | hδ₀, hδ₁ | hδ₁, hδ₂ | hδ₂⟩ := hδ <;> simp [hδ₀, hδ₁, hδ₂]
  · simp [pow_succ] at hA
    nlinarith
  · nlinarith [small_pos_pos_neg_mul hA]
  · nlinarith [small_pos_neg_pos_mul hA]
  · nlinarith [small_pos_neg_neg_mul hA]
  · nlinarith [small_neg_pos_pos_mul hA]
  · nlinarith [small_neg_pos_neg_mul hA]
  · nlinarith [small_neg_neg_pos_mul hA]
  · simp [*, pow_succ', ← mul_inv_rev] at hA ⊢
    nlinarith

/-- If `A` is symmetric (`A⁻¹ = A`) and has small tripling, then `A` has small powers,
in the sense that `|A ^ m|` is at most `|A|` times a constant exponential in `m`.

See also `Finset.small_alternating_pow_of_small_tripling` for a version with a weaker constant but
which encompasses non-symmetric sets. -/
@[to_additive
/-- If `A` is symmetric (`-A = A`) and has small tripling, then `A` has small powers,
in the sense that `|m • A|` is at most `|A|` times a constant exponential in `m`.

See also `Finset.small_alternating_nsmul_of_small_tripling` for a version with a weaker constant but
which encompasses non-symmetric sets. -/]
/-
**Finset.small_pow_of_small_tripling** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
形式化陈述：small_pow_of_small_tripling (hm : 3 <= m) (hA : #(A ^ 3) <= K * #A) (hAsym
m : A⁻¹ = A) : #(A ^ m) <= K ^ (m - 2) * #A
参数：hm : 3 <= m；hA : #(A ^ 3) <= K * #A；hAsymm : A⁻¹ = A。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_or_eq_neg_of_abs_eq`：∀ {α : Type u_1} [inst : AddGroup α] [inst_1 : L
inearOrder α] {a b : α}, |a| = b → a = b ∨ a = -b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `zpow_ofNat`：zpow_ofNat (a : G) (n : Nat) : a ^ (ofNat(n) : Int) = a ^ Of
Nat.ofNat n
· 使用引理 `pow_one`：pow_one (a : M) : a ^ 1 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `zpow_neg`：∀ {α : Type u_1} [inst : DivisionMonoid α] (a : α) (n : ℤ), a 
^ (-n) = (a ^ n)⁻¹
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `List.map_const'`：∀ {α : Type u_1} {β : Type u_2} {l : List α} {b : β}, L
ist.map (fun x => b) l = List.replicate l.length b
· 使用定理 `List.length_finRange`：∀ {n : ℕ}, (List.finRange n).length = n
· 使用定理 `List.prod_replicate`：prod_replicate (n : Nat) (a : M) : (replicate n a).
prod = a ^ n
· 使用定理 `_private.Mathlib.Combinatorics.Additive.SmallTripling.0.Finset.inductive
_claim_mul`：∀ {G : Type u_1} [inst : DecidableEq G] [inst_1 : Group G] {A : Fins
et G} {k : ℝ} {m : ℕ},   3 ≤ m →     (∀ (ε : Fin 3 → ℤ),         (∀ (i :…
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `pow_succ'`：∀ {M : Type u_2} [inst : Monoid M] (a : M) (n : ℕ), a ^ (n + 
1) = a * a ^ n
· 使用定理 `pow_zero`：pow_zero (a : M) : a ^ 0 = 1
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `abs_one`：∀ {α : Type u_1} [inst : Ring α] [inst_1 : LinearOrder α] [IsOr
deredRing α], |1| = 1
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
lemma small_pow_of_small_tripling (hm : 3 ≤ m) (hA : #(A ^ 3) ≤ K * #A) (hAsymm : A⁻¹ = A) :
    #(A ^ m) ≤ K ^ (m - 2) * #A := by
  have (ε : ℤ) (hε : |ε| = 1) : A ^ ε = A := by
    obtain rfl | rfl := eq_or_eq_neg_of_abs_eq hε <;> simp [hAsymm]
  calc
    (#(A ^ m) : ℝ) = #((finRange m).map fun i ↦ A ^ 1).prod := by simp
    _ ≤ K ^ (m - 2) * #A :=
      inductive_claim_mul hm (fun δ hδ ↦ by simpa [this _ (hδ _), pow_succ'] using hA) _ (by simp)

end Finset

