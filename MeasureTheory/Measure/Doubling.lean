/-
Copyright (c) 2022 Oliver Nash. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Nash
-/
module

public import Mathlib.MeasureTheory.Measure.MeasureSpaceDef

/-!
# Uniformly locally doubling measures

A uniformly locally doubling measure `μ` on a metric space is a measure for which there exists a
constant `C` such that for all sufficiently small radii `ε`, and for any centre, the measure of a
ball of radius `2 * ε` is bounded by `C` times the measure of the concentric ball of radius `ε`.

This file records basic facts about uniformly locally doubling measures.

## Main definitions

  * `IsUnifLocDoublingMeasure`: the definition of a uniformly locally doubling measure (as a
    typeclass).
  * `IsUnifLocDoublingMeasure.doublingConstant`: a function yielding the doubling constant `C`
    appearing in the definition of a uniformly locally doubling measure.
-/

@[expose] public section

assert_not_exists Real.instPow

noncomputable section

open Set Filter Metric MeasureTheory TopologicalSpace ENNReal NNReal Topology

/-- A measure `μ` is said to be a uniformly locally doubling measure if there exists a constant `C`
such that for all sufficiently small radii `ε`, and for any centre, the measure of a ball of radius
`2 * ε` is bounded by `C` times the measure of the concentric ball of radius `ε`.

Note: it is important that this definition makes a demand only for sufficiently small `ε`. For
example we want hyperbolic space to carry the instance `IsUnifLocDoublingMeasure volume` but
volumes grow exponentially in hyperbolic space. To be really explicit, consider the hyperbolic plane
of curvature -1, the area of a disc of radius `ε` is `A(ε) = 2π(cosh(ε) - 1)` so
`A(2ε)/A(ε) ~ exp(ε)`. -/
/-
**IsUnifLocDoublingMeasure** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：{α : Type u_1} → [PseudoMetricSpace α] → [inst : MeasurableSpace α] → Meas
ureTheory.Measure α → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A measure `μ` is said to be a uniformly locally doubling measure if there exists
 a constant `C`
such that for all sufficiently small radii `ε`, and for any centre, the measure 
of a ball of radius
`2 * ε` is bounded by `C` times the measure of the concentric ball of radius `ε`
.

Note: it is important that this definition makes a demand only for sufficiently 
small `ε`. For
example we want hyperbolic space to carry the instance `IsUnifLocDoublingMeasure
 volume` but
volumes grow exponentially in hyperbolic space. To be really explicit, consider 
the hyperbolic plane
of curvature -1, the area of a disc of radius `ε` is `A(ε) = 2π(cosh(ε) - 1)` so
`A(2ε)/A(ε) ~ exp(ε)`.
-/
class IsUnifLocDoublingMeasure {α : Type*} [PseudoMetricSpace α] [MeasurableSpace α]
  (μ : Measure α) : Prop where
  exists_measure_closedBall_le_mul'' :
    ∃ C : ℝ≥0, ∀ᶠ ε in 𝓝[>] 0, ∀ x, μ (closedBall x (2 * ε)) ≤ C * μ (closedBall x ε)

namespace IsUnifLocDoublingMeasure

variable {α : Type*} [PseudoMetricSpace α] [MeasurableSpace α] (μ : Measure α)
  [IsUnifLocDoublingMeasure μ]

/-
**IsUnifLocDoublingMeasure.exists_measure_closedBall_le_mul** 是 Mathlib 中的一个定理，位
于命名空间 `IsUnifLocDoublingMeasure`。
形式化陈述：exists_measure_closedBall_le_mul : exists C : Real>=0, forallᶠ ε in 𝓝[>] 0
, forall x, μ (closedBall x (2 * ε)) <= C * μ (closedBall x ε)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsUnifLocDoublingMeasure.exists_measure_closedBall_le_mul''`：∀ {α : Type
 u_1} {inst : PseudoMetricSpace α} {inst_1 : MeasurableSpace α} {μ : MeasureTheo
ry.Measure α}   [self : IsUnifLocDoublingMeasure …
-/
theorem exists_measure_closedBall_le_mul :
    ∃ C : ℝ≥0, ∀ᶠ ε in 𝓝[>] 0, ∀ x, μ (closedBall x (2 * ε)) ≤ C * μ (closedBall x ε) :=
  exists_measure_closedBall_le_mul''

/-- A doubling constant for a uniformly locally doubling measure.

See also `IsUnifLocDoublingMeasure.scalingConstantOf`. -/
/-
**IsUnifLocDoublingMeasure.doublingConstant** 是 Mathlib 中的一个定义，位于命名空间 `IsUnifLoc
DoublingMeasure`。
形式化陈述：doublingConstant : Real>=0
该定义给出了一等式。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `IsUnifLocDoublingMeasure.exists_measure_closedBall_le_mul`：exists_measur
e_closedBall_le_mul : exists C : Real>=0, forallᶠ ε in 𝓝[>] 0, forall x, μ (clos
edBall x (2 * ε)) <= C * μ (closedBall x ε)

--- 原说明 ---
A doubling constant for a uniformly locally doubling measure.

See also `IsUnifLocDoublingMeasure.scalingConstantOf`.
-/
def doublingConstant : ℝ≥0 :=
  Classical.choose <| exists_measure_closedBall_le_mul μ
/-
**IsUnifLocDoublingMeasure.eventually_measure_le_doublingConstant_mul** 是 Mathli
b 中的一个定理，位于命名空间 `IsUnifLocDoublingMeasure`。
形式化陈述：eventually_measure_le_doublingConstant_mul : forallᶠ ε in 𝓝[>] 0, forall x
, μ (closedBall x (2 * ε)) <= doublingConstant μ * μ (closedBall x ε)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Classical.choose_spec`：∀ {α : Sort u} {p : α → Prop} (h : ∃ x, p x), p (
Classical.choose h)
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `IsUnifLocDoublingMeasure.exists_measure_closedBall_le_mul`：exists_measur
e_closedBall_le_mul : exists C : Real>=0, forallᶠ ε in 𝓝[>] 0, forall x, μ (clos
edBall x (2 * ε)) <= C * μ (closedBall x ε)
-/
theorem eventually_measure_le_doublingConstant_mul :
    ∀ᶠ ε in 𝓝[>] 0, ∀ x, μ (closedBall x (2 * ε)) ≤ doublingConstant μ * μ (closedBall x ε) :=
  Classical.choose_spec <| exists_measure_closedBall_le_mul μ
/-
**IsUnifLocDoublingMeasure.exists_eventually_forall_measure_closedBall_le_mul** 
是 Mathlib 中的一个定理，位于命名空间 `IsUnifLocDoublingMeasure`。
形式化陈述：exists_eventually_forall_measure_closedBall_le_mul (K : Real) : exists C :
 Real>=0, forallᶠ ε in 𝓝[>] 0, forall x, forall t <= K, μ (closedBall x (t * ε))
 <= C * μ (closedBall x ε)
参数：K : Real。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `pow_zero`：pow_zero (a : M) : a ^ 0 = 1
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `eventually_nhdsGT_zero_mul_left`：eventually_nhdsGT_zero_mul_left {x : 𝕜}
 (hx : 0 < x) {p : 𝕜 -> Prop} (h : forallᶠ ε in 𝓝[>] 0, p ε) : forallᶠ ε in 𝓝[>]
 0, p (x * ε)
· 使用定理 `instOrderTopologyReal`：OrderTopology ℝ
· 使用定理 `two_pos`：∀ {α : Type u_1} [inst : AddMonoidWithOne α] [inst_1 : PartialO
rder α] [ZeroLEOneClass α] [NeZero 1] [AddLeftMono α],   0 < 2
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `IsUnifLocDoublingMeasure.eventually_measure_le_doublingConstant_mul`：eve
ntually_measure_le_doublingConstant_mul : forallᶠ ε in 𝓝[>] 0, forall x, μ (clos
edBall x (2 * ε)) <= doublingConstant μ * μ (closedBall x…
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `pow_succ`：pow_succ (a : M) (n : Nat) : a ^ (n + 1) = a ^ n * a
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `le_imp_le_of_le_of_le`：le_imp_le_of_le_of_le (h₁ : c <= a) (h₂ : b <= d)
 : a <= b -> c <= d
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `mul_le_mul'`：mul_le_mul' [MulLeftMono α] [MulRightMono α] {a b c d : α} 
(h₁ : a <= b) (h₂ : c <= d) : a * c <= b * d
· 使用定理 `IsOrderedMonoid.toMulLeftMono`：∀ {α : Type u_1} [inst : CommMonoid α] [i
nst_1 : Preorder α] [IsOrderedMonoid α], MulLeftMono α
· 使用定理 `ENNReal.instIsOrderedMonoid`：IsOrderedMonoid ENNReal
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `pow_unbounded_of_one_lt`：pow_unbounded_of_one_lt [ExistsAddOfLE R] (x : 
R) (hy1 : 1 < y) : exists n : Nat, x < y ^ n
· 使用定理 `AddGroup.existsAddOfLE`：∀ (α : Type u) [inst : AddGroup α] [inst_1 : LE 
α], ExistsAddOfLE α
（共 43 条，此处仅展示前 30 条）
-/
theorem exists_eventually_forall_measure_closedBall_le_mul (K : ℝ) :
    ∃ C : ℝ≥0, ∀ᶠ ε in 𝓝[>] 0, ∀ x, ∀ t ≤ K, μ (closedBall x (t * ε)) ≤ C * μ (closedBall x ε) := by
  let C := doublingConstant μ
  suffices ∀ n,
      ∀ᶠ ε in 𝓝[>] 0, ∀ x, μ (closedBall x ((2 : ℝ) ^ n * ε)) ≤ C ^ n * μ (closedBall x ε) by
    rcases pow_unbounded_of_one_lt K one_lt_two with ⟨n, hn⟩
    use C ^ n
    filter_upwards [eventually_mem_nhdsWithin, this n] with ε hε₀ hε x t ht
    rw [mem_Ioi] at hε₀
    grw [ht, hn, ENNReal.coe_pow]
    exact hε x
  intro n
  induction n with
  | zero => simp
  | succ n ihn =>
    replace ihn := eventually_nhdsGT_zero_mul_left (two_pos : 0 < (2 : ℝ)) ihn
    filter_upwards [ihn, eventually_measure_le_doublingConstant_mul μ] with ε hεn hε x
    grw [pow_succ, mul_assoc, hεn, hε, ← mul_assoc, pow_succ]

/-- A variant of `IsUnifLocDoublingMeasure.doublingConstant` which allows for scaling the
radius by values other than `2`. -/
/-
**IsUnifLocDoublingMeasure.scalingConstantOf** 是 Mathlib 中的一个定义，位于命名空间 `IsUnifLo
cDoublingMeasure`。
形式化陈述：scalingConstantOf (K : Real) : Real>=0
参数：K : Real。
该定义给出了一等式。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `IsUnifLocDoublingMeasure.exists_eventually_forall_measure_closedBall_le_
mul`：exists_eventually_forall_measure_closedBall_le_mul (K : Real) : exists C : 
Real>=0, forallᶠ ε in 𝓝[>] 0, forall x, forall t <= K, μ (closedB…

--- 原说明 ---
A variant of `IsUnifLocDoublingMeasure.doublingConstant` which allows for scalin
g the
radius by values other than `2`.
-/
def scalingConstantOf (K : ℝ) : ℝ≥0 :=
  max (Classical.choose <| exists_eventually_forall_measure_closedBall_le_mul μ K) 1

@[simp]
/-
**IsUnifLocDoublingMeasure.one_le_scalingConstantOf** 是 Mathlib 中的一个定理，位于命名空间 `I
sUnifLocDoublingMeasure`。
形式化陈述：one_le_scalingConstantOf (K : Real) : 1 <= scalingConstantOf μ K
参数：K : Real。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `le_max_of_le_right`：le_max_of_le_right : a <= c -> a <= max b c
· 使用定理 `IsUnifLocDoublingMeasure.exists_eventually_forall_measure_closedBall_le_
mul`：exists_eventually_forall_measure_closedBall_le_mul (K : Real) : exists C : 
Real>=0, forallᶠ ε in 𝓝[>] 0, forall x, forall t <= K, μ (closedB…
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
-/
theorem one_le_scalingConstantOf (K : ℝ) : 1 ≤ scalingConstantOf μ K :=
  le_max_of_le_right <| le_refl 1
/-
**IsUnifLocDoublingMeasure.eventually_measure_mul_le_scalingConstantOf_mul** 是 M
athlib 中的一个定理，位于命名空间 `IsUnifLocDoublingMeasure`。
形式化陈述：eventually_measure_mul_le_scalingConstantOf_mul (K : Real) : exists R : Re
al, 0 < R ∧ forall x t r, t in Ioc 0 K -> r <= R -> μ (closedBall x (t * r)) <= 
scalingConstantOf μ K * μ (closedBall x r)
参数：K : Real。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsUnifLocDoublingMeasure.exists_eventually_forall_measure_closedBall_le_
mul`：exists_eventually_forall_measure_closedBall_le_mul (K : Real) : exists C : 
Real>=0, forallᶠ ε in 𝓝[>] 0, forall x, forall t <= K, μ (closedB…
· 使用定理 `Classical.choose_spec`：∀ {α : Sort u} {p : α → Prop} (h : ∃ x, p x), p (
Classical.choose h)
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `mem_nhdsGT_iff_exists_Ioc_subset`：mem_nhdsGT_iff_exists_Ioc_subset [NoMa
xOrder α] [DenselyOrdered α] {a : α} {s : Set α} : s in 𝓝[>] a ↔ exists u in Ioi
 a, Ioc a u subseteq s
· 使用定理 `instOrderTopologyReal`：OrderTopology ℝ
· 使用定理 `instNoMaxOrderOfNontrivial`：∀ {R : Type u} [inst : Ring R] [inst_1 : Par
tialOrder R] [IsOrderedRing R] [Nontrivial R], NoMaxOrder R
· 使用定理 `LinearOrderedSemiField.toDenselyOrdered`：∀ {α : Type u_2} [inst : Semifi
eld α] [inst_1 : PartialOrder α] [PosMulReflectLT α] [IsStrictOrderedRing α],   
DenselyOrdered α
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用引理 `lt_trichotomy`：lt_trichotomy (a b : α) : a < b ∨ a = b ∨ b < a
· 使用定理 `mul_neg_of_pos_of_neg`：mul_neg_of_pos_of_neg [PosMulStrictMono α] (ha : 
0 < a) (hb : b < 0) : a * b < 0
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Metric.closedBall_eq_empty`：closedBall_eq_empty : closedBall x ε = ∅ ↔ ε
 < 0
· 使用定理 `MeasureTheory.measure_empty`：measure_empty : μ ∅ = 0
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `instIsBotZeroClass`：∀ {α : Type u} [inst : AddZeroClass α] [inst_1 : LE 
α] [CanonicallyOrderedAdd α], IsBotZeroClass α
· 使用定理 `ENNReal.instCanonicallyOrderedAdd`：CanonicallyOrderedAdd ENNReal
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `le_mul_of_one_le_of_le`：le_mul_of_one_le_of_le [MulRightMono α] {a b c :
 α} (ha : 1 <= a) (hbc : b <= c) : b <= a * c
· 使用定理 `IsOrderedMonoid.toMulLeftMono`：∀ {α : Type u_1} [inst : CommMonoid α] [i
nst_1 : Preorder α] [IsOrderedMonoid α], MulLeftMono α
· 使用定理 `ENNReal.instIsOrderedMonoid`：IsOrderedMonoid ENNReal
· 使用定理 `ENNReal.one_le_coe_iff`：one_le_coe_iff : (1 : Real>=0∞) <= ↑r ↔ 1 <= r
· 使用定理 `le_max_right`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), b ≤ max
 a b
· 使用引理 `le_rfl`：le_rfl : a <= a
（共 37 条，此处仅展示前 30 条）
-/
theorem eventually_measure_mul_le_scalingConstantOf_mul (K : ℝ) :
    ∃ R : ℝ,
      0 < R ∧
        ∀ x t r, t ∈ Ioc 0 K → r ≤ R →
          μ (closedBall x (t * r)) ≤ scalingConstantOf μ K * μ (closedBall x r) := by
  have h := Classical.choose_spec (exists_eventually_forall_measure_closedBall_le_mul μ K)
  rcases mem_nhdsGT_iff_exists_Ioc_subset.1 h with ⟨R, Rpos, hR⟩
  refine ⟨R, Rpos, fun x t r ht hr => ?_⟩
  rcases lt_trichotomy r 0 with (rneg | rfl | rpos)
  · have : t * r < 0 := mul_neg_of_pos_of_neg ht.1 rneg
    simp only [closedBall_eq_empty.2 this, measure_empty, zero_le]
  · simp only [mul_zero]
    refine le_mul_of_one_le_of_le ?_ le_rfl
    apply ENNReal.one_le_coe_iff.2 (le_max_right _ _)
  · apply (hR ⟨rpos, hr⟩ x t ht.2).trans
    gcongr
    apply le_max_left
/-
**IsUnifLocDoublingMeasure.eventually_measure_le_scaling_constant_mul** 是 Mathli
b 中的一个定理，位于命名空间 `IsUnifLocDoublingMeasure`。
形式化陈述：eventually_measure_le_scaling_constant_mul (K : Real) : forallᶠ r in 𝓝[>] 
0, forall x, μ (closedBall x (K * r)) <= scalingConstantOf μ K * μ (closedBall x
 r)
参数：K : Real。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `IsUnifLocDoublingMeasure.exists_eventually_forall_measure_closedBall_le_
mul`：exists_eventually_forall_measure_closedBall_le_mul (K : Real) : exists C : 
Real>=0, forallᶠ ε in 𝓝[>] 0, forall x, forall t <= K, μ (closedB…
· 使用定理 `Classical.choose_spec`：∀ {α : Sort u} {p : α → Prop} (h : ∃ x, p x), p (
Classical.choose h)
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `le_imp_le_of_le_of_le`：le_imp_le_of_le_of_le (h₁ : c <= a) (h₂ : b <= d)
 : a <= b -> c <= d
· 使用引理 `le_rfl`：le_rfl : a <= a
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `IsUnifLocDoublingMeasure.scalingConstantOf.eq_1`：∀ {α : Type u_1} [inst 
: PseudoMetricSpace α] [inst_1 : MeasurableSpace α] (μ : MeasureTheory.Measure α
)   [inst_2 : IsUnifLocDoublingMeasur…
· 使用定理 `mul_le_mul'`：mul_le_mul' [MulLeftMono α] [MulRightMono α] {a b c d : α} 
(h₁ : a <= b) (h₂ : c <= d) : a * c <= b * d
· 使用定理 `IsOrderedMonoid.toMulLeftMono`：∀ {α : Type u_1} [inst : CommMonoid α] [i
nst_1 : Preorder α] [IsOrderedMonoid α], MulLeftMono α
· 使用定理 `ENNReal.instIsOrderedMonoid`：IsOrderedMonoid ENNReal
· 使用定理 `ENNReal.coe_le_coe._gcongr_2`：∀ {r q : NNReal}, r ≤ q → ↑r ≤ ↑q
· 使用定理 `le_max_left`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), a ≤ max 
a b
-/
theorem eventually_measure_le_scaling_constant_mul (K : ℝ) :
    ∀ᶠ r in 𝓝[>] 0, ∀ x, μ (closedBall x (K * r)) ≤ scalingConstantOf μ K * μ (closedBall x r) := by
  filter_upwards [Classical.choose_spec
      (exists_eventually_forall_measure_closedBall_le_mul μ K)] with r hr x
  grw [hr x K le_rfl, scalingConstantOf, ← le_max_left]
/-
**IsUnifLocDoublingMeasure.eventually_measure_le_scaling_constant_mul'** 是 Mathl
ib 中的一个定理，位于命名空间 `IsUnifLocDoublingMeasure`。
形式化陈述：eventually_measure_le_scaling_constant_mul' (K : Real) (hK : 0 < K) : fora
llᶠ r in 𝓝[>] 0, forall x, μ (closedBall x r) <= scalingConstantOf μ K⁻¹ * μ (cl
osedBall x (K * r))
参数：K : Real；hK : 0 < K。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `pi_congr`：∀ {α : Sort u} {β β' : α → Sort v}, (∀ (a : α), β a = β' a) → 
((a : α) → β a) = ((a : α) → β' a)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `inv_mul_cancel_left₀`：inv_mul_cancel_left₀ (h : a != 0) (b : G₀) : a⁻¹ *
 (a * b) = b
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `eventually_nhdsGT_zero_mul_left`：eventually_nhdsGT_zero_mul_left {x : 𝕜}
 (hx : 0 < x) {p : 𝕜 -> Prop} (h : forallᶠ ε in 𝓝[>] 0, p ε) : forallᶠ ε in 𝓝[>]
 0, p (x * ε)
· 使用定理 `instOrderTopologyReal`：OrderTopology ℝ
· 使用定理 `IsUnifLocDoublingMeasure.eventually_measure_le_scaling_constant_mul`：eve
ntually_measure_le_scaling_constant_mul (K : Real) : forallᶠ r in 𝓝[>] 0, forall
 x, μ (closedBall x (K * r)) <= scalingConstantOf μ K * μ…
-/
theorem eventually_measure_le_scaling_constant_mul' (K : ℝ) (hK : 0 < K) :
    ∀ᶠ r in 𝓝[>] 0, ∀ x,
      μ (closedBall x r) ≤ scalingConstantOf μ K⁻¹ * μ (closedBall x (K * r)) := by
  convert! eventually_nhdsGT_zero_mul_left hK (eventually_measure_le_scaling_constant_mul μ K⁻¹)
  simp [inv_mul_cancel_left₀ hK.ne']

/-- A scale below which the doubling measure `μ` satisfies good rescaling properties when one
multiplies the radius of balls by at most `K`, as stated
in `IsUnifLocDoublingMeasure.measure_mul_le_scalingConstantOf_mul`. -/
/-
**IsUnifLocDoublingMeasure.scalingScaleOf** 是 Mathlib 中的一个定义，位于命名空间 `IsUnifLocDo
ublingMeasure`。
形式化陈述：scalingScaleOf (K : Real) : Real
参数：K : Real。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `IsUnifLocDoublingMeasure.eventually_measure_mul_le_scalingConstantOf_mul
`：eventually_measure_mul_le_scalingConstantOf_mul (K : Real) : exists R : Real, 
0 < R ∧ forall x t r, t in Ioc 0 K -> r <= R -> μ (closedBall …

--- 原说明 ---
A scale below which the doubling measure `μ` satisfies good rescaling properties
 when one
multiplies the radius of balls by at most `K`, as stated
in `IsUnifLocDoublingMeasure.measure_mul_le_scalingConstantOf_mul`.
-/
def scalingScaleOf (K : ℝ) : ℝ :=
  (eventually_measure_mul_le_scalingConstantOf_mul μ K).choose
/-
**IsUnifLocDoublingMeasure.scalingScaleOf_pos** 是 Mathlib 中的一个定理，位于命名空间 `IsUnifL
ocDoublingMeasure`。
形式化陈述：scalingScaleOf_pos (K : Real) : 0 < scalingScaleOf μ K
参数：K : Real。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `IsUnifLocDoublingMeasure.eventually_measure_mul_le_scalingConstantOf_mul
`：eventually_measure_mul_le_scalingConstantOf_mul (K : Real) : exists R : Real, 
0 < R ∧ forall x t r, t in Ioc 0 K -> r <= R -> μ (closedBall …
· 使用定理 `Exists.choose_spec`：∀ {α : Sort u_1} {p : α → Prop} (P : ∃ a, p a), p P.
choose
-/
theorem scalingScaleOf_pos (K : ℝ) : 0 < scalingScaleOf μ K :=
  (eventually_measure_mul_le_scalingConstantOf_mul μ K).choose_spec.1
/-
**IsUnifLocDoublingMeasure.measure_mul_le_scalingConstantOf_mul** 是 Mathlib 中的一个
定理，位于命名空间 `IsUnifLocDoublingMeasure`。
形式化陈述：measure_mul_le_scalingConstantOf_mul {K : Real} {x : α} {t r : Real} (ht :
 t in Ioc 0 K) (hr : r <= scalingScaleOf μ K) : μ (closedBall x (t * r)) <= scal
ingConstantOf μ K * μ (closedBall x r)
参数：ht : t in Ioc 0 K；hr : r <= scalingScaleOf μ K。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `IsUnifLocDoublingMeasure.eventually_measure_mul_le_scalingConstantOf_mul
`：eventually_measure_mul_le_scalingConstantOf_mul (K : Real) : exists R : Real, 
0 < R ∧ forall x t r, t in Ioc 0 K -> r <= R -> μ (closedBall …
· 使用定理 `Exists.choose_spec`：∀ {α : Sort u_1} {p : α → Prop} (P : ∃ a, p a), p P.
choose
-/
theorem measure_mul_le_scalingConstantOf_mul {K : ℝ} {x : α} {t r : ℝ} (ht : t ∈ Ioc 0 K)
    (hr : r ≤ scalingScaleOf μ K) :
    μ (closedBall x (t * r)) ≤ scalingConstantOf μ K * μ (closedBall x r) :=
  (eventually_measure_mul_le_scalingConstantOf_mul μ K).choose_spec.2 x t r ht hr

end IsUnifLocDoublingMeasure

