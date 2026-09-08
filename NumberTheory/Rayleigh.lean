/-
Copyright (c) 2023 Jason Yuen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Yuen
-/
module

public import Mathlib.Data.Real.ConjExponents
public import Mathlib.NumberTheory.Real.Irrational

/-!
# Rayleigh's theorem on Beatty sequences

This file proves Rayleigh's theorem on Beatty sequences. We start by proving `compl_beattySeq`,
which is a generalization of Rayleigh's theorem, and eventually prove
`Irrational.beattySeq_symmDiff_beattySeq_pos`, which is Rayleigh's theorem.

## Main definitions

* `beattySeq`: In the Beatty sequence for real number `r`, the `k`th term is `⌊k * r⌋`.
* `beattySeq'`: In this variant of the Beatty sequence for `r`, the `k`th term is `⌈k * r⌉ - 1`.

## Main statements

Define the following Beatty sets, where `r` denotes a real number:

* `B_r := {⌊k * r⌋ | k ∈ ℤ}`
* `B'_r := {⌈k * r⌉ - 1 | k ∈ ℤ}`
* `B⁺_r := {⌊r⌋, ⌊2r⌋, ⌊3r⌋, ...}`
* `B⁺'_r := {⌈r⌉-1, ⌈2r⌉-1, ⌈3r⌉-1, ...}`

The main statements are:

* `compl_beattySeq`: Let `r` be a real number greater than 1, and `1/r + 1/s = 1`.
  Then the complement of `B_r` is `B'_s`.
* `beattySeq_symmDiff_beattySeq'_pos`: Let `r` be a real number greater than 1, and `1/r + 1/s = 1`.
  Then `B⁺_r` and `B⁺'_s` partition the positive integers.
* `Irrational.beattySeq_symmDiff_beattySeq_pos`: Let `r` be an irrational number greater than 1, and
  `1/r + 1/s = 1`. Then `B⁺_r` and `B⁺_s` partition the positive integers.

## References

* [Wikipedia, *Beatty sequence*](https://en.wikipedia.org/wiki/Beatty_sequence)

## Tags

beatty, sequence, rayleigh, irrational, floor, positive
-/

@[expose] public section

/-- In the Beatty sequence for real number `r`, the `k`th term is `⌊k * r⌋`. -/
/-
**beattySeq** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：beattySeq (r : Real) : Int -> Int
参数：r : Real。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
In the Beatty sequence for real number `r`, the `k`th term is `⌊k * r⌋`.
-/
noncomputable def beattySeq (r : ℝ) : ℤ → ℤ :=
  fun k ↦ ⌊k * r⌋

/-- In this variant of the Beatty sequence for `r`, the `k`th term is `⌈k * r⌉ - 1`. -/
/-
**beattySeq'** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：beattySeq' (r : Real) : Int -> Int
参数：r : Real。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
In this variant of the Beatty sequence for `r`, the `k`th term is `⌈k * r⌉ - 1`.
-/
noncomputable def beattySeq' (r : ℝ) : ℤ → ℤ :=
  fun k ↦ ⌈k * r⌉ - 1

namespace Beatty

variable {r s : ℝ} {j : ℤ}

/-- Let `r > 1` and `1/r + 1/s = 1`. Then `B_r` and `B'_s` are disjoint (i.e. no collision exists).
-/
/-
**Beatty.no_collision** 是 Mathlib 中的一个定理，位于命名空间 `Beatty`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Let `r > 1` and `1/r + 1/s = 1`. Then `B_r` and `B'_s` are disjoint (i.e. no col
lision exists).
-/
private theorem no_collision (hrs : r.HolderConjugate s) :
    Disjoint {beattySeq r k | k} {beattySeq' s k | k} := by
  rw [Set.disjoint_left]
  intro j ⟨k, h₁⟩ ⟨m, h₂⟩
  rw [beattySeq, Int.floor_eq_iff, ← div_le_iff₀ hrs.pos, ← lt_div_iff₀ hrs.pos] at h₁
  rw [beattySeq', sub_eq_iff_eq_add, Int.ceil_eq_iff, Int.cast_add, Int.cast_one,
    add_sub_cancel_right, ← div_lt_iff₀ hrs.symm.pos, ← le_div_iff₀ hrs.symm.pos] at h₂
  have h₃ := add_lt_add_of_le_of_lt h₁.1 h₂.1
  have h₄ := add_lt_add_of_lt_of_le h₁.2 h₂.2
  simp_rw [div_eq_inv_mul, ← right_distrib, hrs.inv_add_inv_eq_one, one_mul] at h₃ h₄
  rw [← Int.cast_one] at h₄
  simp_rw [← Int.cast_add, Int.cast_lt, Int.lt_add_one_iff] at h₃ h₄
  exact h₄.not_gt h₃

/-- Let `r > 1` and `1/r + 1/s = 1`. Suppose there is an integer `j` where `B_r` and `B'_s` both
jump over `j` (i.e. an anti-collision). Then this leads to a contradiction. -/
/-
**Beatty.no_anticollision** 是 Mathlib 中的一个定理，位于命名空间 `Beatty`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Let `r > 1` and `1/r + 1/s = 1`. Suppose there is an integer `j` where `B_r` and
 `B'_s` both
jump over `j` (i.e. an anti-collision). Then this leads to a contradiction.
-/
private theorem no_anticollision (hrs : r.HolderConjugate s) :
    ¬∃ j k m : ℤ, k < j / r ∧ (j + 1) / r ≤ k + 1 ∧ m ≤ j / s ∧ (j + 1) / s < m + 1 := by
  intro ⟨j, k, m, h₁₁, h₁₂, h₂₁, h₂₂⟩
  have h₃ := add_lt_add_of_lt_of_le h₁₁ h₂₁
  have h₄ := add_lt_add_of_le_of_lt h₁₂ h₂₂
  simp_rw [div_eq_inv_mul, ← right_distrib, hrs.inv_add_inv_eq_one, one_mul] at h₃ h₄
  rw [← Int.cast_one, ← add_assoc, add_lt_add_iff_right, add_right_comm] at h₄
  simp_rw [← Int.cast_add, Int.cast_lt, Int.lt_add_one_iff] at h₃ h₄
  exact h₄.not_gt h₃

/-- Let `0 < r ∈ ℝ` and `j ∈ ℤ`. Then either `j ∈ B_r` or `B_r` jumps over `j`. -/
/-
**Beatty.hit_or_miss** 是 Mathlib 中的一个定理，位于命名空间 `Beatty`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Let `0 < r ∈ ℝ` and `j ∈ ℤ`. Then either `j ∈ B_r` or `B_r` jumps over `j`.
-/
private theorem hit_or_miss (h : r > 0) :
    j ∈ {beattySeq r k | k} ∨ ∃ k : ℤ, k < j / r ∧ (j + 1) / r ≤ k + 1 := by
  -- for both cases, the candidate is `k = ⌈(j + 1) / r⌉ - 1`
  cases lt_or_ge ((⌈(j + 1) / r⌉ - 1) * r) j
  · refine Or.inr ⟨⌈(j + 1) / r⌉ - 1, ?_⟩
    rw [Int.cast_sub, Int.cast_one, lt_div_iff₀ h, sub_add_cancel]
    exact ⟨‹_›, Int.le_ceil _⟩
  · refine Or.inl ⟨⌈(j + 1) / r⌉ - 1, ?_⟩
    rw [beattySeq, Int.floor_eq_iff, Int.cast_sub, Int.cast_one, ← lt_div_iff₀ h, sub_lt_iff_lt_add]
    exact ⟨‹_›, Int.ceil_lt_add_one _⟩

/-- Let `0 < r ∈ ℝ` and `j ∈ ℤ`. Then either `j ∈ B'_r` or `B'_r` jumps over `j`. -/
/-
**Beatty.hit_or_miss'** 是 Mathlib 中的一个定理，位于命名空间 `Beatty`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Let `0 < r ∈ ℝ` and `j ∈ ℤ`. Then either `j ∈ B'_r` or `B'_r` jumps over `j`.
-/
private theorem hit_or_miss' (h : r > 0) :
    j ∈ {beattySeq' r k | k} ∨ ∃ k : ℤ, k ≤ j / r ∧ (j + 1) / r < k + 1 := by
  -- for both cases, the candidate is `k = ⌊(j + 1) / r⌋`
  cases le_or_gt (⌊(j + 1) / r⌋ * r) j
  · exact Or.inr ⟨⌊(j + 1) / r⌋, (le_div_iff₀ h).2 ‹_›, Int.lt_floor_add_one _⟩
  · refine Or.inl ⟨⌊(j + 1) / r⌋, ?_⟩
    rw [beattySeq', sub_eq_iff_eq_add, Int.ceil_eq_iff, Int.cast_add, Int.cast_one]
    constructor
    · rwa [add_sub_cancel_right]
    exact sub_nonneg.1 (Int.sub_floor_div_mul_nonneg (j + 1 : ℝ) h)

end Beatty

/-- Generalization of Rayleigh's theorem on Beatty sequences. Let `r` be a real number greater
than 1, and `1/r + 1/s = 1`. Then the complement of `B_r` is `B'_s`. -/
/-
**compl_beattySeq** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：compl_beattySeq {r s : Real} (hrs : r.HolderConjugate s) : {beattySeq r k 
| k}ᶜ = {beattySeq' s k | k}
参数：hrs : r.HolderConjugate s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `Set.not_disjoint_iff`：not_disjoint_iff : ¬Disjoint s t ↔ exists x, x in 
s ∧ x in t
· 使用定理 `_private.Mathlib.NumberTheory.Rayleigh.0.Beatty.no_collision`：∀ {r s : ℝ
}, r.HolderConjugate s → Disjoint {x | ∃ k, beattySeq r k = x} {x | ∃ k, beattyS
eq' s k = x}
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `not_true_eq_false`：(¬True) = False
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `Or.resolve_left`：∀ {a b : Prop}, a ∨ b → ¬a → b
· 使用定理 `_private.Mathlib.NumberTheory.Rayleigh.0.Beatty.hit_or_miss`：∀ {r : ℝ} {
j : ℤ}, r > 0 → j ∈ {x | ∃ k, beattySeq r k = x} ∨ ∃ k, ↑k < ↑j / r ∧ (↑j + 1) /
 r ≤ ↑k + 1
· 使用定理 `Real.HolderTriple.pos`：pos : 0 < p
· 使用定理 `_private.Mathlib.NumberTheory.Rayleigh.0.Beatty.hit_or_miss'`：∀ {r : ℝ} 
{j : ℤ}, r > 0 → j ∈ {x | ∃ k, beattySeq' r k = x} ∨ ∃ k, ↑k ≤ ↑j / r ∧ (↑j + 1)
 / r < ↑k + 1
· 使用定理 `Real.HolderConjugate.symm`：∀ {p q : ℝ}, p.HolderConjugate q → q.HolderCo
njugate p
· 使用定理 `_private.Mathlib.NumberTheory.Rayleigh.0.Beatty.no_anticollision`：∀ {r s
 : ℝ}, r.HolderConjugate s → ¬∃ j k m, ↑k < ↑j / r ∧ (↑j + 1) / r ≤ ↑k + 1 ∧ ↑m 
≤ ↑j / s ∧ (↑j + 1) / s < ↑m + 1

--- 原说明 ---
Generalization of Rayleigh's theorem on Beatty sequences. Let `r` be a real numb
er greater
than 1, and `1/r + 1/s = 1`. Then the complement of `B_r` is `B'_s`.
-/
theorem compl_beattySeq {r s : ℝ} (hrs : r.HolderConjugate s) :
    {beattySeq r k | k}ᶜ = {beattySeq' s k | k} := by
  ext j
  by_cases h₁ : j ∈ {beattySeq r k | k} <;> by_cases h₂ : j ∈ {beattySeq' s k | k}
  · exact (Set.not_disjoint_iff.2 ⟨j, h₁, h₂⟩ (Beatty.no_collision hrs)).elim
  · simp only [Set.mem_compl_iff, h₁, h₂, not_true_eq_false]
  · simp only [Set.mem_compl_iff, h₁, h₂, not_false_eq_true]
  · have ⟨k, h₁₁, h₁₂⟩ := (Beatty.hit_or_miss hrs.pos).resolve_left h₁
    have ⟨m, h₂₁, h₂₂⟩ := (Beatty.hit_or_miss' hrs.symm.pos).resolve_left h₂
    exact (Beatty.no_anticollision hrs ⟨j, k, m, h₁₁, h₁₂, h₂₁, h₂₂⟩).elim
/-
**compl_beattySeq'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：compl_beattySeq' {r s : Real} (hrs : r.HolderConjugate s) : {beattySeq' r 
k | k}ᶜ = {beattySeq s k | k}
参数：hrs : r.HolderConjugate s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `compl_beattySeq`：compl_beattySeq {r s : Real} (hrs : r.HolderConjugate s
) : {beattySeq r k | k}ᶜ = {beattySeq' s k | k}
· 使用定理 `Real.HolderConjugate.symm`：∀ {p q : ℝ}, p.HolderConjugate q → q.HolderCo
njugate p
· 使用定理 `compl_compl`：compl_compl (x : α) : xᶜᶜ = x
-/
theorem compl_beattySeq' {r s : ℝ} (hrs : r.HolderConjugate s) :
    {beattySeq' r k | k}ᶜ = {beattySeq s k | k} := by
  rw [← compl_beattySeq hrs.symm, compl_compl]

open scoped symmDiff

/-- Generalization of Rayleigh's theorem on Beatty sequences. Let `r` be a real number greater
than 1, and `1/r + 1/s = 1`. Then `B⁺_r` and `B⁺'_s` partition the positive integers. -/
/-
**beattySeq_symmDiff_beattySeq'_pos** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {r s : ℝ},   r.HolderConjugate s → symmDiff {x | ∃ k > 0, beattySeq r k 
= x} {x | ∃ k > 0, beattySeq' s k = x} = {n | 0 < n}
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.eq_of_subset_of_subset`：eq_of_subset_of_subset {a b : Set α} : a sub
seteq b -> b subseteq a -> a = b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.mem_ofPred_eq`：mem_ofPred_eq {x : α} {p : α -> Prop} : (x in {y | p 
y}) = p x
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `beattySeq.eq_1`：∀ (r : ℝ) (k : ℤ), beattySeq r k = ⌊↑k * r⌋
· 使用定理 `Int.floor_pos`：floor_pos : 0 < ⌊a⌋ ↔ 1 <= a
· 使用引理 `one_le_mul_of_one_le_of_one_le`：one_le_mul_of_one_le_of_one_le [ZeroLEOn
eClass M₀] [PosMulMono M₀] (ha : 1 <= a) (hb : 1 <= b) : (1 : M₀) <= a * b
· 使用定理 `IsOrderedRing.toPosMulMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], PosMulMono R
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `Int.cast_one`：cast_one : ((1 : Int) : R) = 1
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用引理 `Real.HolderTriple.lt`：lt : r < p
· 使用定理 `beattySeq'.eq_1`：∀ (r : ℝ) (k : ℤ), beattySeq' r k = ⌈↑k * r⌉ - 1
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
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `Int.lt_ceil`：lt_ceil : z < ⌈a⌉ ↔ (z : α) < a
· 使用引理 `one_lt_mul_of_le_of_lt`：one_lt_mul_of_le_of_lt [ZeroLEOneClass M₀] [MulP
osMono M₀] (ha : 1 <= a) (hb : 1 < b) : 1 < a * b
· 使用定理 `IsOrderedRing.toMulPosMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], MulPosMono R
· 使用定理 `Real.HolderConjugate.symm`：∀ {p q : ℝ}, p.HolderConjugate q → q.HolderCo
njugate p
· 使用定理 `Nat.cast_zero`：cast_zero : ((0 : Nat) : R) = 0
· 使用定理 `Int.cast_zero`：cast_zero : ((0 : Int) : R) = 0
（共 44 条，此处仅展示前 30 条）

--- 原说明 ---
Generalization of Rayleigh's theorem on Beatty sequences. Let `r` be a real numb
er greater
than 1, and `1/r + 1/s = 1`. Then `B⁺_r` and `B⁺'_s` partition the positive inte
gers.
-/
theorem beattySeq_symmDiff_beattySeq'_pos {r s : ℝ} (hrs : r.HolderConjugate s) :
    {beattySeq r k | k > 0} ∆ {beattySeq' s k | k > 0} = {n | 0 < n} := by
  apply Set.eq_of_subset_of_subset
  · rintro j (⟨⟨k, hk, hjk⟩, -⟩ | ⟨⟨k, hk, hjk⟩, -⟩)
    · rw [Set.mem_ofPred_eq, ← hjk, beattySeq, Int.floor_pos]
      exact one_le_mul_of_one_le_of_one_le (by norm_cast) hrs.lt.le
    · rw [Set.mem_ofPred_eq, ← hjk, beattySeq', sub_pos, Int.lt_ceil, Int.cast_one]
      exact one_lt_mul_of_le_of_lt (by norm_cast) hrs.symm.lt
  intro j (hj : 0 < j)
  have hb₁ : ∀ s ≥ 0, j ∈ {beattySeq s k | k > 0} ↔ j ∈ {beattySeq s k | k} := by
    intro _ hs
    refine ⟨fun ⟨k, _, hk⟩ ↦ ⟨k, hk⟩, fun ⟨k, hk⟩ ↦ ⟨k, ?_, hk⟩⟩
    rw [← hk, beattySeq, Int.floor_pos] at hj
    exact_mod_cast pos_of_mul_pos_left (zero_lt_one.trans_le hj) hs
  have hb₂ : ∀ s ≥ 0, j ∈ {beattySeq' s k | k > 0} ↔ j ∈ {beattySeq' s k | k} := by
    intro _ hs
    refine ⟨fun ⟨k, _, hk⟩ ↦ ⟨k, hk⟩, fun ⟨k, hk⟩ ↦ ⟨k, ?_, hk⟩⟩
    rw [← hk, beattySeq', sub_pos, Int.lt_ceil, Int.cast_one] at hj
    exact_mod_cast pos_of_mul_pos_left (zero_lt_one.trans hj) hs
  rw [Set.mem_symmDiff, hb₁ _ hrs.nonneg, hb₂ _ hrs.symm.nonneg, ← compl_beattySeq hrs,
    Set.notMem_compl_iff, Set.mem_compl_iff, and_self, and_self]
  exact or_not
/-
**beattySeq'_symmDiff_beattySeq_pos** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {r s : ℝ},   r.HolderConjugate s → symmDiff {x | ∃ k > 0, beattySeq' r k
 = x} {x | ∃ k > 0, beattySeq s k = x} = {n | 0 < n}
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `symmDiff_comm`：symmDiff_comm : a ∆ b = b ∆ a
· 使用定理 `beattySeq_symmDiff_beattySeq'_pos`：∀ {r s : ℝ},   r.HolderConjugate s → 
symmDiff {x | ∃ k > 0, beattySeq r k = x} {x | ∃ k > 0, beattySeq' s k = x} = {n
 | 0 < n}
· 使用定理 `Real.HolderConjugate.symm`：∀ {p q : ℝ}, p.HolderConjugate q → q.HolderCo
njugate p
-/
theorem beattySeq'_symmDiff_beattySeq_pos {r s : ℝ} (hrs : r.HolderConjugate s) :
    {beattySeq' r k | k > 0} ∆ {beattySeq s k | k > 0} = {n | 0 < n} := by
  rw [symmDiff_comm, beattySeq_symmDiff_beattySeq'_pos hrs.symm]

/-- Let `r` be an irrational number. Then `B⁺_r` and `B⁺'_r` are equal. -/
/-
**Irrational.beattySeq'_pos_eq** 是 Mathlib 中的一个定理，位于命名空间 `Irrational`。
形式化陈述：∀ {r : ℝ}, Irrational r → {x | ∃ k > 0, beattySeq' r k = x} = {x | ∃ k > 0
, beattySeq r k = x}
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `and_congr_right_iff`：∀ {a b c : Prop}, (a ∧ b ↔ a ∧ c) ↔ a → (b ↔ c)
· 使用定理 `iff_of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `sub_eq_iff_eq_add`：∀ {G : Type u_3} [inst : AddGroup G] {a b c : G}, a -
 b = c ↔ a = c + b
· 使用定理 `Int.ceil_eq_iff`：ceil_eq_iff : ⌈a⌉ = z ↔ ↑z - 1 < a ∧ a <= z
· 使用定理 `Int.cast_add`：∀ {R : Type u} [inst : AddGroupWithOne R] (m n : ℤ), ↑(m +
 n) = ↑m + ↑n
· 使用定理 `Int.cast_one`：cast_one : ((1 : Int) : R) = 1
· 使用定理 `add_sub_cancel_right`：∀ {G : Type u_1} [inst : AddGroup G] (a b : G), a 
+ b - b = a
· 使用定理 `LE.le.lt_of_ne`：∀ {α : Type u_1} [inst : PartialOrder α] {a b : α}, a ≤ 
b → a ≠ b → a < b
· 使用定理 `Int.floor_le`：floor_le (a : α) : (⌊a⌋ : α) <= a
· 使用定理 `Irrational.ne_int`：ne_int (h : Irrational x) (m : Int) : x != m
· 使用定理 `Irrational.intCast_mul`：intCast_mul (h : Irrational x) {m : Int} (hm : m
 != 0) : Irrational (m * x)
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `Int.lt_floor_add_one`：lt_floor_add_one (a : R) : a < ⌊a⌋ + 1

--- 原说明 ---
Let `r` be an irrational number. Then `B⁺_r` and `B⁺'_r` are equal.
-/
theorem Irrational.beattySeq'_pos_eq {r : ℝ} (hr : Irrational r) :
    {beattySeq' r k | k > 0} = {beattySeq r k | k > 0} := by
  dsimp only [beattySeq, beattySeq']
  congr! 4; rename_i k; rw [and_congr_right_iff]; intro hk; congr!
  rw [sub_eq_iff_eq_add, Int.ceil_eq_iff, Int.cast_add, Int.cast_one, add_sub_cancel_right]
  refine ⟨(Int.floor_le _).lt_of_ne fun h ↦ ?_, (Int.lt_floor_add_one _).le⟩
  exact (hr.intCast_mul hk.ne').ne_int ⌊k * r⌋ h.symm

/-- **Rayleigh's theorem** on Beatty sequences. Let `r` be an irrational number greater than 1, and
`1/r + 1/s = 1`. Then `B⁺_r` and `B⁺_s` partition the positive integers. -/
/-
**Irrational.beattySeq_symmDiff_beattySeq_pos** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Irrational.beattySeq_symmDiff_beattySeq_pos {r s : Real} (hrs : r.HolderCo
njugate s) (hr : Irrational r) : {beattySeq r k | k > 0} ∆ {beattySeq s k | k > 
0} = {n | 0 < n}
参数：hrs : r.HolderConjugate s；hr : Irrational r。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Irrational.beattySeq'_pos_eq`：∀ {r : ℝ}, Irrational r → {x | ∃ k > 0, be
attySeq' r k = x} = {x | ∃ k > 0, beattySeq r k = x}
· 使用定理 `beattySeq'_symmDiff_beattySeq_pos`：∀ {r s : ℝ},   r.HolderConjugate s → 
symmDiff {x | ∃ k > 0, beattySeq' r k = x} {x | ∃ k > 0, beattySeq s k = x} = {n
 | 0 < n}

--- 原说明 ---
**Rayleigh's theorem** on Beatty sequences. Let `r` be an irrational number grea
ter than 1, and
`1/r + 1/s = 1`. Then `B⁺_r` and `B⁺_s` partition the positive integers.
-/
theorem Irrational.beattySeq_symmDiff_beattySeq_pos {r s : ℝ}
    (hrs : r.HolderConjugate s) (hr : Irrational r) :
    {beattySeq r k | k > 0} ∆ {beattySeq s k | k > 0} = {n | 0 < n} := by
  rw [← hr.beattySeq'_pos_eq, beattySeq'_symmDiff_beattySeq_pos hrs]
