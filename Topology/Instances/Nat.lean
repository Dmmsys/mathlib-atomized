/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro
-/
module

public import Mathlib.Order.Lattice.Nat
public import Mathlib.Topology.Instances.Int

/-!
# Topology on the natural numbers

The structure of a metric space on `ℕ` is introduced in this file, induced from `ℝ`.
-/

public section

noncomputable section

open Filter Metric Set Topology

namespace Nat

/-
**Nat.** 是 Mathlib 中的一个实例，位于命名空间 `Nat`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
noncomputable instance : Dist ℕ :=
  ⟨fun x y => dist (x : ℝ) y⟩
/-
**Nat.dist_eq** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：dist_eq (x y : Nat) : dist x y = |(x : Real) - y|
参数：x y : Nat。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem dist_eq (x y : ℕ) : dist x y = |(x : ℝ) - y| := rfl
/-
**Nat.dist_coe_int** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：dist_coe_int (x y : Nat) : dist (x : Int) (y : Int) = dist x y
参数：x y : Nat。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem dist_coe_int (x y : ℕ) : dist (x : ℤ) (y : ℤ) = dist x y := rfl

@[norm_cast, simp]
/-
**Nat.dist_cast_real** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：dist_cast_real (x y : Nat) : dist (x : Real) y = dist x y
参数：x y : Nat。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem dist_cast_real (x y : ℕ) : dist (x : ℝ) y = dist x y := rfl
/-
**Nat.pairwise_one_le_dist** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：pairwise_one_le_dist : Pairwise fun m n : Nat => 1 <= dist m n
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Int.pairwise_one_le_dist`：pairwise_one_le_dist : Pairwise fun m n : Int 
=> 1 <= dist m n
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
-/
theorem pairwise_one_le_dist : Pairwise fun m n : ℕ => 1 ≤ dist m n := fun _ _ hne =>
  Int.pairwise_one_le_dist <| mod_cast hne
/-
**Nat.isUniformEmbedding_coe_real** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：isUniformEmbedding_coe_real : IsUniformEmbedding ((↑) : Nat -> Real)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Metric.isUniformEmbedding_bot_of_pairwise_le_dist`：isUniformEmbedding_bo
t_of_pairwise_le_dist {β : Type*} {ε : Real} (hε : 0 < ε) {f : β -> α} (hf : Pai
rwise fun x y => ε <= dist (f x) (f y))…
· 使用定理 `zero_lt_one`：∀ {α : Type u_1} [inst : Zero α] [inst_1 : One α] [inst_2 :
 PartialOrder α] [ZeroLEOneClass α] [NeZero 1], 0 < 1
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `Nat.pairwise_one_le_dist`：pairwise_one_le_dist : Pairwise fun m n : Nat 
=> 1 <= dist m n
-/
theorem isUniformEmbedding_coe_real : IsUniformEmbedding ((↑) : ℕ → ℝ) :=
  isUniformEmbedding_bot_of_pairwise_le_dist zero_lt_one pairwise_one_le_dist
/-
**Nat.isClosedEmbedding_coe_real** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：isClosedEmbedding_coe_real : IsClosedEmbedding ((↑) : Nat -> Real)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Metric.isClosedEmbedding_of_pairwise_le_dist`：isClosedEmbedding_of_pairw
ise_le_dist {α : Type*} [TopologicalSpace α] [DiscreteTopology α] {ε : Real} (hε
 : 0 < ε) {f : α -> γ} (hf : Pairw…
· 使用定理 `instDiscreteTopologyNat`：DiscreteTopology ℕ
· 使用定理 `zero_lt_one`：∀ {α : Type u_1} [inst : Zero α] [inst_1 : One α] [inst_2 :
 PartialOrder α] [ZeroLEOneClass α] [NeZero 1], 0 < 1
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `Nat.pairwise_one_le_dist`：pairwise_one_le_dist : Pairwise fun m n : Nat 
=> 1 <= dist m n
-/
theorem isClosedEmbedding_coe_real : IsClosedEmbedding ((↑) : ℕ → ℝ) :=
  isClosedEmbedding_of_pairwise_le_dist zero_lt_one pairwise_one_le_dist
/-
**Nat.** 是 Mathlib 中的一个实例，位于命名空间 `Nat`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : MetricSpace ℕ := Nat.isUniformEmbedding_coe_real.comapMetricSpace _
/-
**Nat.preimage_ball** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：preimage_ball (x : Nat) (r : Real) : (↑) ⁻¹' ball (x : Real) r = ball x r
参数：x : Nat；r : Real。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem preimage_ball (x : ℕ) (r : ℝ) : (↑) ⁻¹' ball (x : ℝ) r = ball x r := rfl
/-
**Nat.preimage_closedBall** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：preimage_closedBall (x : Nat) (r : Real) : (↑) ⁻¹' closedBall (x : Real) r
 = closedBall x r
参数：x : Nat；r : Real。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem preimage_closedBall (x : ℕ) (r : ℝ) : (↑) ⁻¹' closedBall (x : ℝ) r = closedBall x r := rfl
/-
**Nat.closedBall_eq_Icc** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：closedBall_eq_Icc (x : Nat) (r : Real) : closedBall x r = Icc ⌈↑x - r⌉₊ ⌊↑
x + r⌋₊
参数：x : Nat；r : Real。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `le_or_gt`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), a ≤ b ∨ b <
 a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.preimage_closedBall`：preimage_closedBall (x : Nat) (r : Real) : (↑) 
⁻¹' closedBall (x : Real) r = closedBall x r
· 使用定理 `Real.closedBall_eq_Icc`：Real.closedBall_eq_Icc {x r : Real} : closedBall
 x r = Icc (x - r) (x + r)
· 使用定理 `Nat.preimage_Icc`：preimage_Icc {a b : R} (hb : 0 <= b) : (Nat.cast : Nat
 -> R) ⁻¹' Set.Icc a b = Set.Icc ⌈a⌉₊ ⌊b⌋₊
· 使用定理 `add_nonneg`：∀ {α : Type u_1} [inst : AddZeroClass α] [inst_1 : Preorder 
α] [AddLeftMono α] {a b : α}, 0 ≤ a → 0 ≤ b → 0 ≤ a + b
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `Nat.cast_nonneg'`：cast_nonneg' (n : Nat) : 0 <= (n : α)
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Metric.closedBall_eq_empty`：closedBall_eq_empty : closedBall x ε = ∅ ↔ ε
 < 0
· 使用定理 `Set.Icc_eq_empty_of_lt`：Icc_eq_empty_of_lt (h : b < a) : Icc a b = ∅
· 使用定理 `Nat.floor_mono`：floor_mono : Monotone (floor : R -> Nat)
· 使用引理 `le_of_not_gt`：le_of_not_gt (h : ¬b < a) : a <= b
· 使用定理 `Mathlib.Tactic.Linarith.lt_irrefl`：lt_irrefl {α : Type u} [Preorder α] {
a : α} : ¬a < a
· 使用定理 `Mathlib.Tactic.Ring.of_eq`：∀ {α : Sort u_2} {a b c : α}, a = c → b = c →
 a = b
· 使用定理 `Mathlib.Tactic.Ring.Common.add_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' + b' = c → a + b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.sub_congr`：∀ {R : Type u_2} [inst : CommRing 
R] {a a' b b' c : R}, a = a' → b = b' → a' - b' = c → a - b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.atom_pf`：∀ {R : Type u_1} [inst : CommSemirin
g R] {b : R} (a : R) {e : ℕ},   Nat.rawCast 1 = e → a ^ e * Nat.rawCast 1 = b → 
a = b + 0
· 使用定理 `Mathlib.Tactic.Ring.cast_zero`：∀ {R : Type u_1} [inst : CommSemiring R] 
{a : R}, Mathlib.Meta.NormNum.IsNat a 0 → a = 0
· 使用定理 `Mathlib.Meta.NormNum.isNat_ofNat`：isNat_ofNat (α : Type u) [AddMonoidWit
hOne α] {a : α} {n : Nat} (h : n = a) : IsNat a n
· 使用定理 `Nat.cast_zero`：cast_zero : ((0 : Nat) : R) = 0
· 使用定理 `Mathlib.Tactic.Ring.Common.sub_pf`：∀ {R : Type u_2} [inst : CommRing R] 
{a b c d : R}, -b = c → a + c = d → a - b = d
· 使用定理 `Mathlib.Tactic.Ring.Common.neg_zero`：∀ {R : Type u_2} [inst : CommRing R
], -0 = 0
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_add_zero`：∀ {R : Type u_1} [inst : Com
mSemiring R] (a : R), a + 0 = a
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_add_gt`：∀ {R : Type u_1} [inst : CommS
emiring R] {a b₂ c : R} (b₁ : R), a + b₂ = c → a + (b₁ + b₂) = b₁ + c
· 使用定理 `Mathlib.Tactic.Ring.Common.neg_add`：∀ {R : Type u_2} [inst : CommRing R]
 {a₁ a₂ b₁ b₂ : R}, -a₁ = b₁ → -a₂ = b₂ → -(a₁ + a₂) = b₁ + b₂
· 使用定理 `Mathlib.Tactic.Ring.Common.neg_mul`：∀ {R : Type u_2} [inst : CommRing R]
 (a₁ : R) (a₂ : ℕ) {a₃ b : R}, -a₃ = b → -(a₁ ^ a₂ * a₃) = a₁ ^ a₂ * b
· 使用定理 `Mathlib.Meta.NormNum.IsInt.to_raw_eq`：∀ {α : Type u} {a : α} {n : ℤ} [in
st : Ring α], Mathlib.Meta.NormNum.IsInt a n → a = n.rawCast
· 使用定理 `Mathlib.Meta.NormNum.isInt_neg`：∀ {α : Type u_1} [inst : Ring α] {f : α 
→ α} {a : α} {a' b : ℤ},   f = Neg.neg → Mathlib.Meta.NormNum.IsInt a a' → a'.ne
g = b → Mathlib.Meta…
（共 46 条，此处仅展示前 30 条）
-/
theorem closedBall_eq_Icc (x : ℕ) (r : ℝ) : closedBall x r = Icc ⌈↑x - r⌉₊ ⌊↑x + r⌋₊ := by
  rcases le_or_gt 0 r with (hr | hr)
  · rw [← preimage_closedBall, Real.closedBall_eq_Icc, preimage_Icc]
    positivity
  · rw [closedBall_eq_empty.2 hr, Icc_eq_empty_of_lt]
    calc ⌊(x : ℝ) + r⌋₊ ≤ ⌊(x : ℝ)⌋₊ := floor_mono <| by linarith
    _ < ⌈↑x - r⌉₊ := by
      rw [floor_natCast, Nat.lt_ceil]
      linarith
/-
**Nat.** 是 Mathlib 中的一个实例，位于命名空间 `Nat`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : ProperSpace ℕ :=
  ⟨fun x r => by
    rw [closedBall_eq_Icc]
    exact (Set.finite_Icc _ _).isCompact⟩
/-
**Nat.** 是 Mathlib 中的一个实例，位于命名空间 `Nat`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : IsOrderBornology ℕ := .of_isCompactIcc 0 (by simp) (by simp [Nat.closedBall_eq_Icc])
/-
**Nat.** 是 Mathlib 中的一个实例，位于命名空间 `Nat`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : NoncompactSpace ℕ :=
  noncompactSpace_of_neBot <| by simp only [Filter.cocompact_eq_cofinite, Filter.cofinite_neBot]

end Nat

