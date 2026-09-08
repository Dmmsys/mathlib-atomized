/-
Copyright (c) 2021 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
module

public import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
public import Mathlib.MeasureTheory.Covering.Besicovitch
public import Mathlib.Tactic.AdaptationNote

/-!
# Satellite configurations for Besicovitch covering lemma in vector spaces

The Besicovitch covering theorem ensures that, in a nice metric space, there exists a number `N`
such that, from any family of balls with bounded radii, one can extract `N` families, each made of
disjoint balls, covering together all the centers of the initial family.

A key tool in the proof of this theorem is the notion of a satellite configuration, i.e., a family
of `N + 1` balls, where the first `N` balls all intersect the last one, but none of them contains
the center of another one and their radii are controlled. This is a technical notion, but it shows
up naturally in the proof of the Besicovitch theorem (which goes through a greedy algorithm): to
ensure that in the end one needs at most `N` families of balls, the crucial property of the
underlying metric space is that there should be no satellite configuration of `N + 1` points.

This file is devoted to the study of this property in vector spaces: we prove the main result
of [Füredi and Loeb, On the best constant for the Besicovitch covering theorem][furedi-loeb1994],
which shows that the optimal such `N` in a vector space coincides with the maximal number
of points one can put inside the unit ball of radius `2` under the condition that their distances
are bounded below by `1`.
In particular, this number is bounded by `5 ^ dim` by a straightforward measure argument.

## Main definitions and results

* `multiplicity E` is the maximal number of points one can put inside the unit ball
  of radius `2` in the vector space `E`, under the condition that their distances
  are bounded below by `1`.
* `multiplicity_le E` shows that `multiplicity E ≤ 5 ^ (dim E)`.
* `good_τ E` is a constant `> 1`, but close enough to `1` that satellite configurations
  with this parameter `τ` are not worst than for `τ = 1`.
* `isEmpty_satelliteConfig_multiplicity` is the main theorem, saying that there are
  no satellite configurations of `(multiplicity E) + 1` points, for the parameter `goodτ E`.
-/

@[expose] public section


universe u

open Metric Set Module MeasureTheory Filter Fin

open scoped ENNReal Topology

noncomputable section

namespace Besicovitch

variable {E : Type*} [NormedAddCommGroup E]

namespace SatelliteConfig

variable [NormedSpace ℝ E] {N : ℕ} {τ : ℝ} (a : SatelliteConfig E N τ)

/-- Rescaling a satellite configuration in a vector space, to put the basepoint at `0` and the base
radius at `1`. -/
/-
**Besicovitch.SatelliteConfig.centerAndRescale** 是 Mathlib 中的一个定义，位于命名空间 `Besico
vitch.SatelliteConfig`。
形式化陈述：centerAndRescale : SatelliteConfig E N τ where c i
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Rescaling a satellite configuration in a vector space, to put the basepoint at `
0` and the base
radius at `1`.
-/
def centerAndRescale : SatelliteConfig E N τ where
  c i := (a.r (last N))⁻¹ • (a.c i - a.c (last N))
  r i := (a.r (last N))⁻¹ * a.r i
  rpos i := by positivity
  h i j hij := by
    simp (disch := positivity) only [dist_smul₀, dist_sub_right, mul_left_comm τ,
      Real.norm_of_nonneg]
    rcases a.h hij with (⟨H₁, H₂⟩ | ⟨H₁, H₂⟩) <;> [left; right] <;> constructor <;> gcongr
  hlast i hi := by
    simp (disch := positivity) only [dist_smul₀, dist_sub_right, mul_left_comm τ,
      Real.norm_of_nonneg]
    have ⟨H₁, H₂⟩ := a.hlast i hi
    constructor <;> gcongr
  inter i hi := by
    simp (disch := positivity) only [dist_smul₀, ← mul_add, dist_sub_right, Real.norm_of_nonneg]
    gcongr
    exact a.inter i hi
/-
**Besicovitch.SatelliteConfig.centerAndRescale_center** 是 Mathlib 中的一个定理，位于命名空间 
`Besicovitch.SatelliteConfig`。
形式化陈述：centerAndRescale_center : a.centerAndRescale.c (last N) = 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `sub_self`：∀ {G : Type u_1} [inst : AddGroup G] (a : G), a - a = 0
· 使用定理 `smul_zero`：smul_zero (a : M) : a • (0 : A) = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem centerAndRescale_center : a.centerAndRescale.c (last N) = 0 := by
  simp [SatelliteConfig.centerAndRescale]
/-
**Besicovitch.SatelliteConfig.centerAndRescale_radius** 是 Mathlib 中的一个定理，位于命名空间 
`Besicovitch.SatelliteConfig`。
形式化陈述：centerAndRescale_radius {N : Nat} {τ : Real} (a : SatelliteConfig E N τ) :
 a.centerAndRescale.r (last N) = 1
参数：a : SatelliteConfig E N τ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `inv_mul_cancel₀`：inv_mul_cancel₀ (h : a != 0) : a⁻¹ * a = 1
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `Besicovitch.SatelliteConfig.rpos`：∀ {α : Type u_1} [inst : MetricSpace α
] {N : ℕ} {τ : ℝ} (self : Besicovitch.SatelliteConfig α N τ) (i : Fin N.succ),  
 0 < self.r i
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem centerAndRescale_radius {N : ℕ} {τ : ℝ} (a : SatelliteConfig E N τ) :
    a.centerAndRescale.r (last N) = 1 := by
  simp [SatelliteConfig.centerAndRescale, inv_mul_cancel₀ (a.rpos _).ne']

end SatelliteConfig

/-! ### Disjoint balls of radius close to `1` in the radius `2` ball. -/


/-- The maximum cardinality of a `1`-separated set in the ball of radius `2`. This is also the
optimal number of families in the Besicovitch covering theorem. -/
/-
**Besicovitch.multiplicity** 是 Mathlib 中的一个定义，位于命名空间 `Besicovitch`。
形式化陈述：multiplicity (E : Type*) [NormedAddCommGroup E]
参数：E : Type*。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The maximum cardinality of a `1`-separated set in the ball of radius `2`. This i
s also the
optimal number of families in the Besicovitch covering theorem.
-/
def multiplicity (E : Type*) [NormedAddCommGroup E] :=
  sSup {N | ∃ s : Finset E, s.card = N ∧ (∀ c ∈ s, ‖c‖ ≤ 2) ∧ ∀ c ∈ s, ∀ d ∈ s, c ≠ d → 1 ≤ ‖c - d‖}

section

variable [NormedSpace ℝ E] [FiniteDimensional ℝ E]

open scoped Function in -- required for scoped `on` notation
/-- Any `1`-separated set in the ball of radius `2` has cardinality at most `5 ^ dim`. This is
useful to show that the supremum in the definition of `Besicovitch.multiplicity E` is
well behaved. -/
/-
**Besicovitch.card_le_of_separated** 是 Mathlib 中的一个定理，位于命名空间 `Besicovitch`。
形式化陈述：card_le_of_separated (s : Finset E) (hs : forall c in s, ‖c‖ <= 2) (h : fo
rall c in s, forall d in s, c != d -> 1 <= ‖c - d‖) : s.card <= 5 ^ finrank Real
 E
参数：s : Finset E；hs : forall c in s, ‖c‖ <= 2；h : forall c in s, forall d in s, c
 != d -> 1 <= ‖c - d‖。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `locallyCompact_of_proper`：∀ {α : Type u} [inst : PseudoMetricSpace α] [P
roperSpace α], LocallyCompactSpace α
· 使用定理 `FiniteDimensional.proper_real`：∀ (E : Type u) [inst : NormedAddCommGroup
 E] [inst_1 : NormedSpace ℝ E] [FiniteDimensional ℝ E], ProperSpace E
· 使用定理 `Mathlib.Meta.NormNum.isNNRat_lt_true`：isNNRat_lt_true [Semiring α] [Line
arOrder α] [IsStrictOrderedRing α] : {a b : α} -> {na nb : Nat} -> {da db : Nat}
 -> IsNNRat a na da -> IsN…
· 使用定理 `Mathlib.Meta.NormNum.IsNat.to_isNNRat`：∀ {α : Type u_1} [inst : Semiring
 α] {a : α} {n : ℕ},   Mathlib.Meta.NormNum.IsNat a n → Mathlib.Meta.NormNum.IsN
NRat a n 1
· 使用定理 `Mathlib.Meta.NormNum.isNat_ofNat`：isNat_ofNat (α : Type u) [AddMonoidWit
hOne α] {a : α} {n : Nat} (h : n = a) : IsNat a n
· 使用定理 `Nat.cast_zero`：cast_zero : ((0 : Nat) : R) = 0
· 使用定理 `Mathlib.Meta.NormNum.isNNRat_div`：∀ {α : Type u} [inst : DivisionSemirin
g α] {a b : α} {cn cd : ℕ},   Mathlib.Meta.NormNum.IsNNRat (a * b⁻¹) cn cd → Mat
hlib.Meta.NormNum.IsNN…
· 使用定理 `Mathlib.Meta.NormNum.isNNRat_mul`：isNNRat_mul {α} [Semiring α] {f : α ->
 α -> α} {a b : α} {na nb nc : Nat} {da db dc k : Nat} : f = HMul.hMul -> IsNNRa
t a na da -> IsNNRat b…
· 使用引理 `Mathlib.Meta.NormNum.instAtLeastTwo`：instAtLeastTwo (n : Nat) : Nat.AtLe
astTwo (n + 2)
· 使用定理 `Mathlib.Meta.NormNum.isNNRat_inv_pos`：isNNRat_inv_pos {α} [DivisionSemir
ing α] [CharZero α] {a : α} {n d : Nat} : IsNNRat a (Nat.succ n) d -> IsNNRat a⁻
¹ d (Nat.succ n)
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `Metric.ball_disjoint_ball`：ball_disjoint_ball (h : δ + ε <= dist x y) : 
Disjoint (ball x δ) (ball y ε)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `dist_eq_norm`：∀ {E : Type u_5} [inst : SeminormedAddCommGroup E] (a b : 
E), dist a b = ‖a - b‖
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Mathlib.Meta.NormNum.isNat_eq_true`：∀ {α : Type u} [inst : AddMonoidWith
One α] {a b : α} {c : ℕ},   Mathlib.Meta.NormNum.IsNat a c → Mathlib.Meta.NormNu
m.IsNat b c → a = b
· 使用定理 `Mathlib.Meta.NormNum.IsNNRat.to_isNat`：∀ {α : Type u_1} [inst : Semiring
 α] {a : α} {n : ℕ},   Mathlib.Meta.NormNum.IsNNRat a n 1 → Mathlib.Meta.NormNum
.IsNat a n
· 使用定理 `Mathlib.Meta.NormNum.isNNRat_add`：isNNRat_add {α} [Semiring α] {f : α ->
 α -> α} {a b : α} {na nb nc : Nat} {da db dc k : Nat} : f = HAdd.hAdd -> IsNNRa
t a na da -> IsNNRat b…
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `Set.iUnion₂_subset`：iUnion₂_subset {s : forall i, κ i -> Set α} {t : Set
 α} (h : forall i j, s i j subseteq t) : ⋃ (i) (j), s i j subseteq t
· 使用定理 `Metric.ball_subset_ball'`：ball_subset_ball' (h : ε₁ + dist x y <= ε₂) : 
ball x ε₁ subseteq ball y ε₂
· 使用定理 `dist_zero_right`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (a : E),
 dist a 0 = ‖a‖
· 使用定理 `add_le_add`：∀ {α : Type u_1} [inst : Add α] [inst_1 : Preorder α] [AddLe
ftMono α] [AddRightMono α] {a b c d : α},   a ≤ b → c ≤ d → a + c ≤ b + d
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用引理 `le_rfl`：le_rfl : a <= a
（共 78 条，此处仅展示前 30 条）

--- 原说明 ---
Any `1`-separated set in the ball of radius `2` has cardinality at most `5 ^ dim
`. This is
useful to show that the supremum in the definition of `Besicovitch.multiplicity 
E` is
well behaved.
-/
theorem card_le_of_separated (s : Finset E) (hs : ∀ c ∈ s, ‖c‖ ≤ 2)
    (h : ∀ c ∈ s, ∀ d ∈ s, c ≠ d → 1 ≤ ‖c - d‖) : s.card ≤ 5 ^ finrank ℝ E := by
  /- We consider balls of radius `1/2` around the points in `s`. They are disjoint, and all
    contained in the ball of radius `5/2`. A volume argument gives `s.card * (1/2)^dim ≤ (5/2)^dim`,
    i.e., `s.card ≤ 5^dim`. -/
  borelize E
  let μ : Measure E := Measure.addHaar
  let δ : ℝ := (1 : ℝ) / 2
  let ρ : ℝ := (5 : ℝ) / 2
  have ρpos : 0 < ρ := by norm_num
  set A := ⋃ c ∈ s, ball (c : E) δ with hA
  have D : Set.Pairwise (s : Set E) (Disjoint on fun c => ball (c : E) δ) := by
    rintro c hc d hd hcd
    apply ball_disjoint_ball
    rw [dist_eq_norm]
    convert! h c hc d hd hcd
    norm_num
  have A_subset : A ⊆ ball (0 : E) ρ := by
    refine iUnion₂_subset fun x hx => ?_
    apply ball_subset_ball'
    calc
      δ + dist x 0 ≤ δ + 2 := by rw [dist_zero_right]; exact add_le_add le_rfl (hs x hx)
      _ = 5 / 2 := by norm_num
  have I :
    (s.card : ℝ≥0∞) * ENNReal.ofReal (δ ^ finrank ℝ E) * μ (ball 0 1) ≤
      ENNReal.ofReal (ρ ^ finrank ℝ E) * μ (ball 0 1) :=
    calc
      (s.card : ℝ≥0∞) * ENNReal.ofReal (δ ^ finrank ℝ E) * μ (ball 0 1) = μ A := by
        rw [hA, measure_biUnion_finset D fun c _ => measurableSet_ball]
        have I : 0 < δ := by norm_num
        simp only [μ.addHaar_ball_of_pos _ I]
        simp only [Finset.sum_const, nsmul_eq_mul, mul_assoc]
      _ ≤ μ (ball (0 : E) ρ) := measure_mono A_subset
      _ = ENNReal.ofReal (ρ ^ finrank ℝ E) * μ (ball 0 1) := by
        simp only [μ.addHaar_ball_of_pos _ ρpos]
  have J : (s.card : ℝ≥0∞) * ENNReal.ofReal (δ ^ finrank ℝ E) ≤ ENNReal.ofReal (ρ ^ finrank ℝ E) :=
    (ENNReal.mul_le_mul_iff_left (measure_ball_pos _ _ zero_lt_one).ne' measure_ball_lt_top.ne).1 I
  have K : (s.card : ℝ) ≤ (5 : ℝ) ^ finrank ℝ E := by
    have := ENNReal.toReal_le_of_le_ofReal (pow_nonneg ρpos.le _) J
    simpa [ρ, δ, div_eq_mul_inv, mul_pow] using this
  exact mod_cast K
/-
**Besicovitch.multiplicity_le** 是 Mathlib 中的一个定理，位于命名空间 `Besicovitch`。
形式化陈述：multiplicity_le : multiplicity E <= 5 ^ finrank Real E
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `csSup_le`：csSup_le (h₁ : s.Nonempty) (h₂ : forall b in s, b <= a) : sSup
 s <= a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `instIsEmptyFalse`：IsEmpty False
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
· 使用定理 `Besicovitch.card_le_of_separated`：card_le_of_separated (s : Finset E) (h
s : forall c in s, ‖c‖ <= 2) (h : forall c in s, forall d in s, c != d -> 1 <= ‖
c - d‖) : s.card <= 5 …
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
theorem multiplicity_le : multiplicity E ≤ 5 ^ finrank ℝ E := by
  apply csSup_le
  · refine ⟨0, ⟨∅, by simp⟩⟩
  · rintro _ ⟨s, ⟨rfl, h⟩⟩
    exact Besicovitch.card_le_of_separated s h.1 h.2
/-
**Besicovitch.card_le_multiplicity** 是 Mathlib 中的一个定理，位于命名空间 `Besicovitch`。
形式化陈述：card_le_multiplicity {s : Finset E} (hs : forall c in s, ‖c‖ <= 2) (h's : 
forall c in s, forall d in s, c != d -> 1 <= ‖c - d‖) : s.card <= multiplicity E
参数：hs : forall c in s, ‖c‖ <= 2；h's : forall c in s, forall d in s, c != d -> 1 
<= ‖c - d‖。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `le_csSup`：le_csSup (h₁ : BddAbove s) (h₂ : a in s) : a <= sSup s
· 使用定理 `Besicovitch.card_le_of_separated`：card_le_of_separated (s : Finset E) (h
s : forall c in s, ‖c‖ <= 2) (h : forall c in s, forall d in s, c != d -> 1 <= ‖
c - d‖) : s.card <= 5 …
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
theorem card_le_multiplicity {s : Finset E} (hs : ∀ c ∈ s, ‖c‖ ≤ 2)
    (h's : ∀ c ∈ s, ∀ d ∈ s, c ≠ d → 1 ≤ ‖c - d‖) : s.card ≤ multiplicity E := by
  apply le_csSup
  · refine ⟨5 ^ finrank ℝ E, ?_⟩
    rintro _ ⟨s, ⟨rfl, h⟩⟩
    exact Besicovitch.card_le_of_separated s h.1 h.2
  · simp only [mem_ofPred_eq, Ne]
    exact ⟨s, rfl, hs, h's⟩

variable (E)

/-- If `δ` is small enough, a `(1-δ)`-separated set in the ball of radius `2` also has cardinality
at most `multiplicity E`. -/
/-
**Besicovitch.exists_good** 是 Mathlib 中的一个定理，位于命名空间 `Besicovitch`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `δ` is small enough, a `(1-δ)`-separated set in the ball of radius `2` also h
as cardinality
at most `multiplicity E`.
-/
theorem exists_goodδ :
    ∃ δ : ℝ, 0 < δ ∧ δ < 1 ∧ ∀ s : Finset E, (∀ c ∈ s, ‖c‖ ≤ 2) →
      (∀ c ∈ s, ∀ d ∈ s, c ≠ d → 1 - δ ≤ ‖c - d‖) → s.card ≤ multiplicity E := by
  classical
  /- This follows from a compactness argument: otherwise, one could extract a converging
    subsequence, to obtain a `1`-separated set in the ball of radius `2` with cardinality
    `N = multiplicity E + 1`. To formalize this, we work with functions `Fin N → E`.
     -/
  by_contra! h
  set N := multiplicity E + 1 with hN
  have :
    ∀ δ : ℝ, 0 < δ → ∃ f : Fin N → E, (∀ i : Fin N, ‖f i‖ ≤ 2) ∧
      Pairwise fun i j => 1 - δ ≤ ‖f i - f j‖ := by
    intro δ hδ
    rcases lt_or_ge δ 1 with (hδ' | hδ')
    · rcases h δ hδ hδ' with ⟨s, hs, h's, s_card⟩
      obtain ⟨f, f_inj, hfs⟩ : ∃ f : Fin N → E, Function.Injective f ∧ range f ⊆ ↑s := by
        have : Fintype.card (Fin N) ≤ s.card := by simp only [Fintype.card_fin]; exact s_card
        rcases Function.Embedding.exists_of_card_le_finset this with ⟨f, hf⟩
        exact ⟨f, f.injective, hf⟩
      simp only [range_subset_iff, Finset.mem_coe] at hfs
      exact ⟨f, fun i => hs _ (hfs i), fun i j hij => h's _ (hfs i) _ (hfs j) (f_inj.ne hij)⟩
    · exact
        ⟨fun _ => 0, by simp, fun i j _ => by
          simpa only [norm_zero, sub_nonpos, sub_self]⟩
  -- For `δ > 0`, `F δ` is a function from `Fin N` to the ball of radius `2` for which two points
  -- in the image are separated by `1 - δ`.
  choose! F hF using this
  -- Choose a converging subsequence when `δ → 0`.
  have : ∃ f : Fin N → E, (∀ i : Fin N, ‖f i‖ ≤ 2) ∧ Pairwise fun i j => 1 ≤ ‖f i - f j‖ := by
    obtain ⟨u, _, zero_lt_u, hu⟩ :
      ∃ u : ℕ → ℝ,
        (∀ m n : ℕ, m < n → u n < u m) ∧ (∀ n : ℕ, 0 < u n) ∧ Filter.Tendsto u Filter.atTop (𝓝 0) :=
      exists_seq_strictAnti_tendsto (0 : ℝ)
    have A : ∀ n, F (u n) ∈ closedBall (0 : Fin N → E) 2 := by
      intro n
      simp only [pi_norm_le_iff_of_nonneg zero_le_two, mem_closedBall, dist_zero_right,
        (hF (u n) (zero_lt_u n)).left, forall_const]
    obtain ⟨f, fmem, φ, φ_mono, hf⟩ :
      ∃ f ∈ closedBall (0 : Fin N → E) 2,
        ∃ φ : ℕ → ℕ, StrictMono φ ∧ Tendsto ((F ∘ u) ∘ φ) atTop (𝓝 f) :=
      IsCompact.tendsto_subseq (isCompact_closedBall _ _) A
    refine ⟨f, fun i => ?_, fun i j hij => ?_⟩
    · simp only [pi_norm_le_iff_of_nonneg zero_le_two, mem_closedBall, dist_zero_right] at fmem
      exact fmem i
    · have A : Tendsto (fun n => ‖F (u (φ n)) i - F (u (φ n)) j‖) atTop (𝓝 ‖f i - f j‖) :=
        ((hf.apply_nhds i).sub (hf.apply_nhds j)).norm
      have B : Tendsto (fun n => 1 - u (φ n)) atTop (𝓝 (1 - 0)) :=
        tendsto_const_nhds.sub (hu.comp φ_mono.tendsto_atTop)
      rw [sub_zero] at B
      exact le_of_tendsto_of_tendsto' B A fun n => (hF (u (φ n)) (zero_lt_u _)).2 hij
  rcases this with ⟨f, hf, h'f⟩
  -- the range of `f` contradicts the definition of `multiplicity E`.
  have finj : Function.Injective f := by
    intro i j hij
    by_contra h
    have : 1 ≤ ‖f i - f j‖ := h'f h
    simp only [hij, norm_zero, sub_self] at this
    exact lt_irrefl _ (this.trans_lt zero_lt_one)
  let s := Finset.image f Finset.univ
  have s_card : s.card = N := by rw [Finset.card_image_of_injective _ finj]; exact Finset.card_fin N
  have hs : ∀ c ∈ s, ‖c‖ ≤ 2 := by
    simp only [s, hf, forall_apply_eq_imp_iff, forall_const, forall_exists_index, Finset.mem_univ,
      Finset.mem_image, true_and]
  have h's : ∀ c ∈ s, ∀ d ∈ s, c ≠ d → 1 ≤ ‖c - d‖ := by
    simp only [s, forall_apply_eq_imp_iff, forall_exists_index, Finset.mem_univ, Finset.mem_image,
      Ne, forall_apply_eq_imp_iff, true_and]
    intro i j hij
    have : i ≠ j := fun h => by rw [h] at hij; exact hij rfl
    exact h'f this
  have : s.card ≤ multiplicity E := card_le_multiplicity hs h's
  rw [s_card, hN] at this
  exact lt_irrefl _ ((Nat.lt_succ_self (multiplicity E)).trans_le this)

/-- A small positive number such that any `1 - δ`-separated set in the ball of radius `2` has
cardinality at most `Besicovitch.multiplicity E`. -/
/-
**Besicovitch.good** 是 Mathlib 中的一个定义，位于命名空间 `Besicovitch`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A small positive number such that any `1 - δ`-separated set in the ball of radiu
s `2` has
cardinality at most `Besicovitch.multiplicity E`.
-/
def goodδ : ℝ :=
  (exists_goodδ E).choose
/-
**Besicovitch.good** 是 Mathlib 中的一个定理，位于命名空间 `Besicovitch`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem goodδ_lt_one : goodδ E < 1 :=
  (exists_goodδ E).choose_spec.2.1

/-- A number `τ > 1`, but chosen close enough to `1` so that the construction in the Besicovitch
covering theorem using this parameter `τ` will give the smallest possible number of covering
families. -/
/-
**Besicovitch.good** 是 Mathlib 中的一个定义，位于命名空间 `Besicovitch`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A number `τ > 1`, but chosen close enough to `1` so that the construction in the
 Besicovitch
covering theorem using this parameter `τ` will give the smallest possible number
 of covering
families.
-/
def goodτ : ℝ :=
  1 + goodδ E / 4
/-
**Besicovitch.one_lt_good** 是 Mathlib 中的一个定理，位于命名空间 `Besicovitch`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem one_lt_goodτ : 1 < goodτ E := by
  dsimp [goodτ, goodδ]; linarith [(exists_goodδ E).choose_spec.1]

variable {E}
/-
**Besicovitch.card_le_multiplicity_of_** 是 Mathlib 中的一个定理，位于命名空间 `Besicovitch`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem card_le_multiplicity_of_δ {s : Finset E} (hs : ∀ c ∈ s, ‖c‖ ≤ 2)
    (h's : ∀ c ∈ s, ∀ d ∈ s, c ≠ d → 1 - goodδ E ≤ ‖c - d‖) : s.card ≤ multiplicity E :=
  (Classical.choose_spec (exists_goodδ E)).2.2 s hs h's
/-
**Besicovitch.le_multiplicity_of_** 是 Mathlib 中的一个定理，位于命名空间 `Besicovitch`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem le_multiplicity_of_δ_of_fin {n : ℕ} (f : Fin n → E) (h : ∀ i, ‖f i‖ ≤ 2)
    (h' : Pairwise fun i j => 1 - goodδ E ≤ ‖f i - f j‖) : n ≤ multiplicity E := by
  classical
  have finj : Function.Injective f := by
    intro i j hij
    by_contra h
    have : 1 - goodδ E ≤ ‖f i - f j‖ := h' h
    simp only [hij, norm_zero, sub_self] at this
    linarith [goodδ_lt_one E]
  let s := Finset.image f Finset.univ
  have s_card : s.card = n := by rw [Finset.card_image_of_injective _ finj]; exact Finset.card_fin n
  have hs : ∀ c ∈ s, ‖c‖ ≤ 2 := by
    simp only [s, h, forall_apply_eq_imp_iff, forall_exists_index, Finset.mem_univ,
      Finset.mem_image, imp_true_iff, true_and]
  have h's : ∀ c ∈ s, ∀ d ∈ s, c ≠ d → 1 - goodδ E ≤ ‖c - d‖ := by
    simp only [s, forall_apply_eq_imp_iff, forall_exists_index, Finset.mem_univ, Finset.mem_image,
      Ne, forall_apply_eq_imp_iff, true_and]
    intro i j hij
    have : i ≠ j := fun h => by rw [h] at hij; exact hij rfl
    exact h' this
  have : s.card ≤ multiplicity E := card_le_multiplicity_of_δ hs h's
  rwa [s_card] at this

end

namespace SatelliteConfig

/-!
### Relating satellite configurations to separated points in the ball of radius `2`.

We prove that the number of points in a satellite configuration is bounded by the maximal number
of `1`-separated points in the ball of radius `2`. For this, start from a satellite configuration
`c`. Without loss of generality, one can assume that the last ball is centered at `0` and of
radius `1`. Define `c' i = c i` if `‖c i‖ ≤ 2`, and `c' i = (2/‖c i‖) • c i` if `‖c i‖ > 2`.
It turns out that these points are `1 - δ`-separated, where `δ` is arbitrarily small if `τ` is
close enough to `1`. The number of such configurations is bounded by `multiplicity E` if `δ` is
suitably small.

To check that the points `c' i` are `1 - δ`-separated, one treats separately the cases where
both `‖c i‖` and `‖c j‖` are `≤ 2`, where one of them is `≤ 2` and the other one is `> 2`, and
where both of them are `> 2`.
-/


/-
**Besicovitch.SatelliteConfig.exists_normalized_aux1** 是 Mathlib 中的一个定理，位于命名空间 `
Besicovitch.SatelliteConfig`。
形式化陈述：exists_normalized_aux1 {N : Nat} {τ : Real} (a : SatelliteConfig E N τ) (l
astr : a.r (last N) = 1) (hτ : 1 <= τ) (δ : Real) (hδ1 : τ <= 1 + δ / 4) (hδ2 : 
δ <= 1) (i j : Fin N.succ) (inej : i != j) : 1 - δ <= ‖a.c i - a.c j‖
参数：a : SatelliteConfig E N τ；lastr : a.r (last N) = 1；hτ : 1 <= τ；δ : Real；hδ1 :
 τ <= 1 + δ / 4；hδ2 : δ <= 1；i j : Fin N.succ；inej : i != j。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `dist_eq_norm`：∀ {E : Type u_5} [inst : SeminormedAddCommGroup E] (a b : 
E), dist a b = ‖a - b‖
· 使用定理 `Besicovitch.SatelliteConfig.h`：∀ {α : Type u_1} [inst : MetricSpace α] {
N : ℕ} {τ : ℝ} (self : Besicovitch.SatelliteConfig α N τ),   Pairwise fun i j =>
     self.r i ≤ dis…
· 使用引理 `le_of_not_gt`：le_of_not_gt (h : ¬b < a) : a <= b
· 使用定理 `Mathlib.Tactic.Linarith.lt_irrefl`：lt_irrefl {α : Type u} [Preorder α] {
a : α} : ¬a < a
· 使用定理 `instNeZeroNatHAdd_1`：∀ {n m : ℕ} [h : NeZero m], NeZero (n + m)
· 使用引理 `Mathlib.Meta.NormNum.instAtLeastTwo`：instAtLeastTwo (n : Nat) : Nat.AtLe
astTwo (n + 2)
· 使用定理 `Mathlib.Tactic.Ring.of_eq`：∀ {α : Sort u_2} {a b c : α}, a = c → b = c →
 a = b
· 使用定理 `Mathlib.Tactic.Ring.Common.add_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' + b' = c → a + b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.sub_congr`：∀ {R : Type u_2} [inst : CommRing 
R] {a a' b b' c : R}, a = a' → b = b' → a' - b' = c → a - b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.atom_pf`：∀ {R : Type u_1} [inst : CommSemirin
g R] {b : R} (a : R) {e : ℕ},   Nat.rawCast 1 = e → a ^ e * Nat.rawCast 1 = b → 
a = b + 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
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
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' * b' = c → a * b = c
· 使用定理 `Mathlib.Tactic.Ring.cast_pos`：∀ {R : Type u_1} [inst : CommSemiring R] {
a : R} {n : ℕ}, Mathlib.Meta.NormNum.IsNat a n → a = n.rawCast + 0
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `Mathlib.Tactic.Ring.Common.neg_add`：∀ {R : Type u_2} [inst : CommRing R]
 {a₁ a₂ b₁ b₂ : R}, -a₁ = b₁ → -a₂ = b₂ → -(a₁ + a₂) = b₁ + b₂
· 使用定理 `Mathlib.Tactic.Ring.Common.neg_mul`：∀ {R : Type u_2} [inst : CommRing R]
 (a₁ : R) (a₂ : ℕ) {a₃ b : R}, -a₃ = b → -(a₁ ^ a₂ * a₃) = a₁ ^ a₂ * b
· 使用定理 `Mathlib.Meta.NormNum.IsInt.to_raw_eq`：∀ {α : Type u} {a : α} {n : ℤ} [in
st : Ring α], Mathlib.Meta.NormNum.IsInt a n → a = n.rawCast
· 使用定理 `Mathlib.Meta.NormNum.isInt_neg`：∀ {α : Type u_1} [inst : Ring α] {f : α 
→ α} {a : α} {a' b : ℤ},   f = Neg.neg → Mathlib.Meta.NormNum.IsInt a a' → a'.ne
g = b → Mathlib.Meta…
（共 117 条，此处仅展示前 30 条）

--- 原说明 ---
### Relating satellite configurations to separated points in the ball of radius 
`2`.

We prove that the number of points in a satellite configuration is bounded by th
e maximal number
of `1`-separated points in the ball of radius `2`. For this, start from a satell
ite configuration
`c`. Without loss of generality, one can assume that the last ball is centered a
t `0` and of
radius `1`. Define `c' i = c i` if `‖c i‖ ≤ 2`, and `c' i = (2/‖c i‖) • c i` if 
`‖c i‖ > 2`.
It turns out that these points are `1 - δ`-separated, where `δ` is arbitrarily s
mall if `τ` is
close enough to `1`. The number of such configurations is bounded by `multiplici
ty E` if `δ` is
suitably small.

To check that the points `c' i` are `1 - δ`-separated, one treats separately the
 cases where
both `‖c i‖` and `‖c j‖` are `≤ 2`, where one of them is `≤ 2` and the other one
 is `> 2`, and
where both of them are `> 2`.
-/
theorem exists_normalized_aux1 {N : ℕ} {τ : ℝ} (a : SatelliteConfig E N τ)
    (lastr : a.r (last N) = 1) (hτ : 1 ≤ τ) (δ : ℝ) (hδ1 : τ ≤ 1 + δ / 4) (hδ2 : δ ≤ 1)
    (i j : Fin N.succ) (inej : i ≠ j) : 1 - δ ≤ ‖a.c i - a.c j‖ := by
  have ah :
      Pairwise fun i j => a.r i ≤ ‖a.c i - a.c j‖ ∧ a.r j ≤ τ * a.r i ∨
        a.r j ≤ ‖a.c j - a.c i‖ ∧ a.r i ≤ τ * a.r j := by
    simpa only [dist_eq_norm] using a.h
  have δnonneg : 0 ≤ δ := by linarith only [hτ, hδ1]
  have D : 0 ≤ 1 - δ / 4 := by linarith only [hδ2]
  have τpos : 0 < τ := _root_.zero_lt_one.trans_le hτ
  have I : (1 - δ / 4) * τ ≤ 1 :=
    calc
      (1 - δ / 4) * τ ≤ (1 - δ / 4) * (1 + δ / 4) := by gcongr
      _ = (1 : ℝ) - δ ^ 2 / 16 := by ring
      _ ≤ 1 := by linarith only [sq_nonneg δ]
  have J : 1 - δ ≤ 1 - δ / 4 := by linarith only [δnonneg]
  have K : 1 - δ / 4 ≤ τ⁻¹ := by rw [inv_eq_one_div, le_div_iff₀ τpos]; exact I
  suffices L : τ⁻¹ ≤ ‖a.c i - a.c j‖ by linarith only [J, K, L]
  have hτ' : ∀ k, τ⁻¹ ≤ a.r k := by
    intro k
    rw [inv_eq_one_div, div_le_iff₀ τpos, ← lastr, mul_comm]
    exact a.hlast' k hτ
  rcases ah inej with (H | H)
  · apply le_trans _ H.1
    exact hτ' i
  · rw [norm_sub_rev]
    apply le_trans _ H.1
    exact hτ' j

variable [NormedSpace ℝ E]
/-
**Besicovitch.SatelliteConfig.exists_normalized_aux2** 是 Mathlib 中的一个定理，位于命名空间 `
Besicovitch.SatelliteConfig`。
形式化陈述：exists_normalized_aux2 {N : Nat} {τ : Real} (a : SatelliteConfig E N τ) (l
astc : a.c (last N) = 0) (lastr : a.r (last N) = 1) (hτ : 1 <= τ) (δ : Real) (hδ
1 : τ <= 1 + δ / 4) (hδ2 : δ <= 1) (i j : Fin N.succ) (inej : i != j) (hi : ‖a.c
 i‖ <= 2) (hj : 2 < ‖a.c j‖) : 1 - δ <= ‖a.c i - (2 / ‖a.c j‖) • a.c j‖
参数：a : SatelliteConfig E N τ；lastc : a.c (last N) = 0；lastr : a.r (last N) = 1；h
τ : 1 <= τ；δ : Real；hδ1 : τ <= 1 + δ / 4；hδ2 : δ <= 1；i j : Fin N.succ；inej : i 
!= j；hi : ‖a.c i‖ <= 2；hj : 2 < ‖a.c j‖。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `dist_eq_norm`：∀ {E : Type u_5} [inst : SeminormedAddCommGroup E] (a b : 
E), dist a b = ‖a - b‖
· 使用定理 `Besicovitch.SatelliteConfig.h`：∀ {α : Type u_1} [inst : MetricSpace α] {
N : ℕ} {τ : ℝ} (self : Besicovitch.SatelliteConfig α N τ),   Pairwise fun i j =>
     self.r i ≤ dis…
· 使用引理 `le_of_not_gt`：le_of_not_gt (h : ¬b < a) : a <= b
· 使用定理 `Mathlib.Tactic.Linarith.lt_irrefl`：lt_irrefl {α : Type u} [Preorder α] {
a : α} : ¬a < a
· 使用定理 `instNeZeroNatHAdd_1`：∀ {n m : ℕ} [h : NeZero m], NeZero (n + m)
· 使用引理 `Mathlib.Meta.NormNum.instAtLeastTwo`：instAtLeastTwo (n : Nat) : Nat.AtLe
astTwo (n + 2)
· 使用定理 `Mathlib.Tactic.Ring.of_eq`：∀ {α : Sort u_2} {a b c : α}, a = c → b = c →
 a = b
· 使用定理 `Mathlib.Tactic.Ring.Common.add_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' + b' = c → a + b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.sub_congr`：∀ {R : Type u_2} [inst : CommRing 
R] {a a' b b' c : R}, a = a' → b = b' → a' - b' = c → a - b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.atom_pf`：∀ {R : Type u_1} [inst : CommSemirin
g R] {b : R} (a : R) {e : ℕ},   Nat.rawCast 1 = e → a ^ e * Nat.rawCast 1 = b → 
a = b + 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
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
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' * b' = c → a * b = c
· 使用定理 `Mathlib.Tactic.Ring.cast_pos`：∀ {R : Type u_1} [inst : CommSemiring R] {
a : R} {n : ℕ}, Mathlib.Meta.NormNum.IsNat a n → a = n.rawCast + 0
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `Mathlib.Tactic.Ring.Common.neg_add`：∀ {R : Type u_2} [inst : CommRing R]
 {a₁ a₂ b₁ b₂ : R}, -a₁ = b₁ → -a₂ = b₂ → -(a₁ + a₂) = b₁ + b₂
· 使用定理 `Mathlib.Tactic.Ring.Common.neg_mul`：∀ {R : Type u_2} [inst : CommRing R]
 (a₁ : R) (a₂ : ℕ) {a₃ b : R}, -a₃ = b → -(a₁ ^ a₂ * a₃) = a₁ ^ a₂ * b
· 使用定理 `Mathlib.Meta.NormNum.IsInt.to_raw_eq`：∀ {α : Type u} {a : α} {n : ℤ} [in
st : Ring α], Mathlib.Meta.NormNum.IsInt a n → a = n.rawCast
· 使用定理 `Mathlib.Meta.NormNum.isInt_neg`：∀ {α : Type u_1} [inst : Ring α] {f : α 
→ α} {a : α} {a' b : ℤ},   f = Neg.neg → Mathlib.Meta.NormNum.IsInt a a' → a'.ne
g = b → Mathlib.Meta…
（共 178 条，此处仅展示前 30 条）
-/
theorem exists_normalized_aux2 {N : ℕ} {τ : ℝ} (a : SatelliteConfig E N τ)
    (lastc : a.c (last N) = 0) (lastr : a.r (last N) = 1) (hτ : 1 ≤ τ) (δ : ℝ) (hδ1 : τ ≤ 1 + δ / 4)
    (hδ2 : δ ≤ 1) (i j : Fin N.succ) (inej : i ≠ j) (hi : ‖a.c i‖ ≤ 2) (hj : 2 < ‖a.c j‖) :
    1 - δ ≤ ‖a.c i - (2 / ‖a.c j‖) • a.c j‖ := by
  have ah :
      Pairwise fun i j => a.r i ≤ ‖a.c i - a.c j‖ ∧ a.r j ≤ τ * a.r i ∨
        a.r j ≤ ‖a.c j - a.c i‖ ∧ a.r i ≤ τ * a.r j := by
    simpa only [dist_eq_norm] using a.h
  have δnonneg : 0 ≤ δ := by linarith only [hτ, hδ1]
  have D : 0 ≤ 1 - δ / 4 := by linarith only [hδ2]
  have hcrj : ‖a.c j‖ ≤ a.r j + 1 := by simpa only [lastc, lastr, dist_zero_right] using a.inter' j
  have I : a.r i ≤ 2 := by
    rcases lt_or_ge i (last N) with (H | H)
    · apply (a.hlast i H).1.trans
      simpa only [dist_eq_norm, lastc, sub_zero] using hi
    · have : i = last N := top_le_iff.1 H
      rw [this, lastr]
      exact one_le_two
  have J : (1 - δ / 4) * τ ≤ 1 :=
    calc
      (1 - δ / 4) * τ ≤ (1 - δ / 4) * (1 + δ / 4) := by gcongr
      _ = (1 : ℝ) - δ ^ 2 / 16 := by ring
      _ ≤ 1 := by linarith only [sq_nonneg δ]
  have A : a.r j - δ ≤ ‖a.c i - a.c j‖ := by
    rcases ah inej.symm with (H | H); · rw [norm_sub_rev]; linarith [H.1]
    have C : a.r j ≤ 4 :=
      calc
        a.r j ≤ τ * a.r i := H.2
        _ ≤ τ * 2 := by gcongr
        _ ≤ 5 / 4 * 2 := by gcongr; linarith only [hδ1, hδ2]
        _ ≤ 4 := by norm_num
    calc
      a.r j - δ ≤ a.r j - a.r j / 4 * δ := by
        gcongr _ - ?_
        exact mul_le_of_le_one_left δnonneg (by linarith only [C])
      _ = (1 - δ / 4) * a.r j := by ring
      _ ≤ (1 - δ / 4) * (τ * a.r i) := by gcongr; exact H.2
      _ ≤ 1 * a.r i := by rw [← mul_assoc]; gcongr
      _ ≤ ‖a.c i - a.c j‖ := by rw [one_mul]; exact H.1
  set d := (2 / ‖a.c j‖) • a.c j with hd
  have : a.r j - δ ≤ ‖a.c i - d‖ + (a.r j - 1) :=
    calc
      a.r j - δ ≤ ‖a.c i - a.c j‖ := A
      _ ≤ ‖a.c i - d‖ + ‖d - a.c j‖ := by simp only [← dist_eq_norm, dist_triangle]
      _ ≤ ‖a.c i - d‖ + (a.r j - 1) := by
        gcongr
        have A : 0 ≤ 1 - 2 / ‖a.c j‖ := by simpa [div_le_iff₀ (zero_le_two.trans_lt hj)] using hj.le
        rw [← one_smul ℝ (a.c j), hd, ← sub_smul, norm_smul, norm_sub_rev, Real.norm_eq_abs,
          abs_of_nonneg A, sub_mul]
        field_simp
        linarith only [hcrj]
  linarith only [this]
/-
**Besicovitch.SatelliteConfig.exists_normalized_aux3** 是 Mathlib 中的一个定理，位于命名空间 `
Besicovitch.SatelliteConfig`。
形式化陈述：exists_normalized_aux3 {N : Nat} {τ : Real} (a : SatelliteConfig E N τ) (l
astc : a.c (last N) = 0) (lastr : a.r (last N) = 1) (hτ : 1 <= τ) (δ : Real) (hδ
1 : τ <= 1 + δ / 4) (i j : Fin N.succ) (inej : i != j) (hi : 2 < ‖a.c i‖) (hij :
 ‖a.c i‖ <= ‖a.c j‖) : 1 - δ <= ‖(2 / ‖a.c i‖) • a.c i - (2 / ‖a.c j‖) • a.c j‖
参数：a : SatelliteConfig E N τ；lastc : a.c (last N) = 0；lastr : a.r (last N) = 1；h
τ : 1 <= τ；δ : Real；hδ1 : τ <= 1 + δ / 4；i j : Fin N.succ；inej : i != j；hi : 2 <
 ‖a.c i‖；hij : ‖a.c i‖ <= ‖a.c j‖。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `dist_eq_norm`：∀ {E : Type u_5} [inst : SeminormedAddCommGroup E] (a b : 
E), dist a b = ‖a - b‖
· 使用定理 `Besicovitch.SatelliteConfig.h`：∀ {α : Type u_1} [inst : MetricSpace α] {
N : ℕ} {τ : ℝ} (self : Besicovitch.SatelliteConfig α N τ),   Pairwise fun i j =>
     self.r i ≤ dis…
· 使用引理 `le_of_not_gt`：le_of_not_gt (h : ¬b < a) : a <= b
· 使用定理 `Mathlib.Tactic.Linarith.lt_irrefl`：lt_irrefl {α : Type u} [Preorder α] {
a : α} : ¬a < a
· 使用定理 `instNeZeroNatHAdd_1`：∀ {n m : ℕ} [h : NeZero m], NeZero (n + m)
· 使用引理 `Mathlib.Meta.NormNum.instAtLeastTwo`：instAtLeastTwo (n : Nat) : Nat.AtLe
astTwo (n + 2)
· 使用定理 `Mathlib.Tactic.Ring.of_eq`：∀ {α : Sort u_2} {a b c : α}, a = c → b = c →
 a = b
· 使用定理 `Mathlib.Tactic.Ring.Common.add_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' + b' = c → a + b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.sub_congr`：∀ {R : Type u_2} [inst : CommRing 
R] {a a' b b' c : R}, a = a' → b = b' → a' - b' = c → a - b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.atom_pf`：∀ {R : Type u_1} [inst : CommSemirin
g R] {b : R} (a : R) {e : ℕ},   Nat.rawCast 1 = e → a ^ e * Nat.rawCast 1 = b → 
a = b + 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
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
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' * b' = c → a * b = c
· 使用定理 `Mathlib.Tactic.Ring.cast_pos`：∀ {R : Type u_1} [inst : CommSemiring R] {
a : R} {n : ℕ}, Mathlib.Meta.NormNum.IsNat a n → a = n.rawCast + 0
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `Mathlib.Tactic.Ring.Common.neg_add`：∀ {R : Type u_2} [inst : CommRing R]
 {a₁ a₂ b₁ b₂ : R}, -a₁ = b₁ → -a₂ = b₂ → -(a₁ + a₂) = b₁ + b₂
· 使用定理 `Mathlib.Tactic.Ring.Common.neg_mul`：∀ {R : Type u_2} [inst : CommRing R]
 (a₁ : R) (a₂ : ℕ) {a₃ b : R}, -a₃ = b → -(a₁ ^ a₂ * a₃) = a₁ ^ a₂ * b
· 使用定理 `Mathlib.Meta.NormNum.IsInt.to_raw_eq`：∀ {α : Type u} {a : α} {n : ℤ} [in
st : Ring α], Mathlib.Meta.NormNum.IsInt a n → a = n.rawCast
· 使用定理 `Mathlib.Meta.NormNum.isInt_neg`：∀ {α : Type u_1} [inst : Ring α] {f : α 
→ α} {a : α} {a' b : ℤ},   f = Neg.neg → Mathlib.Meta.NormNum.IsInt a a' → a'.ne
g = b → Mathlib.Meta…
（共 169 条，此处仅展示前 30 条）
-/
theorem exists_normalized_aux3 {N : ℕ} {τ : ℝ} (a : SatelliteConfig E N τ)
    (lastc : a.c (last N) = 0) (lastr : a.r (last N) = 1) (hτ : 1 ≤ τ) (δ : ℝ) (hδ1 : τ ≤ 1 + δ / 4)
    (i j : Fin N.succ) (inej : i ≠ j) (hi : 2 < ‖a.c i‖) (hij : ‖a.c i‖ ≤ ‖a.c j‖) :
    1 - δ ≤ ‖(2 / ‖a.c i‖) • a.c i - (2 / ‖a.c j‖) • a.c j‖ := by
  have ah :
      Pairwise fun i j => a.r i ≤ ‖a.c i - a.c j‖ ∧ a.r j ≤ τ * a.r i ∨
        a.r j ≤ ‖a.c j - a.c i‖ ∧ a.r i ≤ τ * a.r j := by
    simpa only [dist_eq_norm] using a.h
  have δnonneg : 0 ≤ δ := by linarith only [hτ, hδ1]
  have hcrj : ‖a.c j‖ ≤ a.r j + 1 := by simpa only [lastc, lastr, dist_zero_right] using a.inter' j
  have A : a.r i ≤ ‖a.c i‖ := by
    have : i < last N := by
      apply lt_top_iff_ne_top.2
      intro iN
      change i = last N at iN
      rw [iN, lastc, norm_zero] at hi
      exact lt_irrefl _ (zero_le_two.trans_lt hi)
    convert! (a.hlast i this).1 using 1
    rw [dist_eq_norm, lastc, sub_zero]
  have hj : 2 < ‖a.c j‖ := hi.trans_le hij
  set s := ‖a.c i‖
  have spos : 0 < s := zero_lt_two.trans hi
  set d := (s / ‖a.c j‖) • a.c j with hd
  have I : ‖a.c j - a.c i‖ ≤ ‖a.c j‖ - s + ‖d - a.c i‖ :=
    calc
      ‖a.c j - a.c i‖ ≤ ‖a.c j - d‖ + ‖d - a.c i‖ := by simp [← dist_eq_norm, dist_triangle]
      _ = ‖a.c j‖ - ‖a.c i‖ + ‖d - a.c i‖ := by
        nth_rw 1 [← one_smul ℝ (a.c j)]
        rw [add_left_inj, hd, ← sub_smul, norm_smul, Real.norm_eq_abs, abs_of_nonneg, sub_mul,
          one_mul, div_mul_cancel₀ _ (zero_le_two.trans_lt hj).ne']
        rwa [sub_nonneg, div_le_iff₀ (zero_lt_two.trans hj), one_mul]
  have J : a.r j - ‖a.c j - a.c i‖ ≤ s / 2 * δ :=
    calc
      a.r j - ‖a.c j - a.c i‖ ≤ s * (τ - 1) := by
        rcases ah inej.symm with (H | H)
        · calc
            a.r j - ‖a.c j - a.c i‖ ≤ 0 := sub_nonpos.2 H.1
            _ ≤ s * (τ - 1) := mul_nonneg spos.le (sub_nonneg.2 hτ)
        · rw [norm_sub_rev] at H
          calc
            a.r j - ‖a.c j - a.c i‖ ≤ τ * a.r i - a.r i := sub_le_sub H.2 H.1
            _ = a.r i * (τ - 1) := by ring
            _ ≤ s * (τ - 1) := by gcongr
      _ ≤ s * (δ / 2) := by gcongr; linarith only [δnonneg, hδ1]
      _ = s / 2 * δ := by ring
  have invs_nonneg : 0 ≤ 2 / s := div_nonneg zero_le_two (zero_le_two.trans hi.le)
  calc
    1 - δ = 2 / s * (s / 2 - s / 2 * δ) := by field
    _ ≤ 2 / s * ‖d - a.c i‖ := by
      gcongr; linarith only [hcrj, I, J, hi]
    _ = ‖(2 / s) • a.c i - (2 / ‖a.c j‖) • a.c j‖ := by
      conv_lhs => rw [norm_sub_rev, ← abs_of_nonneg invs_nonneg]
      rw [← Real.norm_eq_abs, ← norm_smul, smul_sub, hd, smul_smul]
      congr 3
      field
/-
**Besicovitch.SatelliteConfig.exists_normalized** 是 Mathlib 中的一个定理，位于命名空间 `Besic
ovitch.SatelliteConfig`。
形式化陈述：exists_normalized {N : Nat} {τ : Real} (a : SatelliteConfig E N τ) (lastc 
: a.c (last N) = 0) (lastr : a.r (last N) = 1) (hτ : 1 <= τ) (δ : Real) (hδ1 : τ
 <= 1 + δ / 4) (hδ2 : δ <= 1) : exists c' : Fin N.succ -> E, (forall n, ‖c' n‖ <
= 2) ∧ Pairwise fun i j => 1 - δ <= ‖c' i - c' j‖
参数：a : SatelliteConfig E N τ；lastc : a.c (last N) = 0；lastr : a.r (last N) = 1；h
τ : 1 <= τ；δ : Real；hδ1 : τ <= 1 + δ / 4；hδ2 : δ <= 1。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `div_zero`：div_zero (a : G₀) : a / 0 = 0
· 使用定理 `zero_smul`：zero_smul (m : A) : (0 : M₀) • m = 0
· 使用定理 `norm_zero`：∀ {E : Type u_5} [inst : SeminormedAddGroup E], ‖0‖ = 0
· 使用引理 `norm_smul`：norm_smul [Norm α] [Norm β] [SMul α β] [NormSMulClass α β] (r
 : α) (x : β) : ‖r • x‖ = ‖r‖ * ‖x‖
· 使用定理 `NormedSpace.toNormSMulClass`：∀ {𝕜 : Type u_1} {E : Type u_3} [inst : Nor
medField 𝕜] [inst_1 : SeminormedAddCommGroup E] [inst_2 : NormedSpace 𝕜 E],   No
rmSMulClass 𝕜 E
· 使用定理 `norm_div`：norm_div (a b : α) : ‖a / b‖ = ‖a‖ / ‖b‖
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Real.norm_ofNat`：∀ (n : ℕ) [inst : n.AtLeastTwo], ‖OfNat.ofNat n‖ = OfNa
t.ofNat n
· 使用定理 `norm_norm`：∀ {E : Type u_5} [inst : SeminormedAddCommGroup E] (x : E), ‖
‖x‖‖ = ‖x‖
· 使用定理 `IsUnit.div_mul_cancel`：∀ {α : Type u} [inst : DivisionMonoid α] {b : α},
 IsUnit b → ∀ (a : α), a / b * b = a
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `Classical.em`：∀ (p : Prop), p ∨ ¬p
· 使用定理 `le_or_gt`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), a ≤ b ∨ b <
 a
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `if_true`：∀ {α : Sort u_1} {x : Decidable True} (t e : α), (if True then 
t else e) = t
· 使用定理 `Besicovitch.SatelliteConfig.exists_normalized_aux1`：exists_normalized_au
x1 {N : Nat} {τ : Real} (a : SatelliteConfig E N τ) (lastr : a.r (last N) = 1) (
hτ : 1 <= τ) (δ : Real) (hδ1 : τ <= 1 + …
· 使用定理 `iff_false`：∀ (p : Prop), (p ↔ False) = ¬p
· 使用定理 `if_false`：∀ {α : Sort u_1} {x : Decidable False} (t e : α), (if False th
en t else e) = e
· 使用定理 `Besicovitch.SatelliteConfig.exists_normalized_aux2`：exists_normalized_au
x2 {N : Nat} {τ : Real} (a : SatelliteConfig E N τ) (lastc : a.c (last N) = 0) (
lastr : a.r (last N) = 1) (hτ : 1 <= τ) …
（共 34 条，此处仅展示前 30 条）
-/
theorem exists_normalized {N : ℕ} {τ : ℝ} (a : SatelliteConfig E N τ) (lastc : a.c (last N) = 0)
    (lastr : a.r (last N) = 1) (hτ : 1 ≤ τ) (δ : ℝ) (hδ1 : τ ≤ 1 + δ / 4) (hδ2 : δ ≤ 1) :
    ∃ c' : Fin N.succ → E, (∀ n, ‖c' n‖ ≤ 2) ∧ Pairwise fun i j => 1 - δ ≤ ‖c' i - c' j‖ := by
  let c' : Fin N.succ → E := fun i => if ‖a.c i‖ ≤ 2 then a.c i else (2 / ‖a.c i‖) • a.c i
  have norm_c'_le : ∀ i, ‖c' i‖ ≤ 2 := by
    intro i
    simp only [c']
    split_ifs with h; · exact h
    by_cases hi : ‖a.c i‖ = 0 <;> simp [norm_smul, hi]
  refine ⟨c', fun n => norm_c'_le n, fun i j inej => ?_⟩
  -- up to exchanging `i` and `j`, one can assume `‖c i‖ ≤ ‖c j‖`.
  wlog hij : ‖a.c i‖ ≤ ‖a.c j‖ generalizing i j
  · rw [norm_sub_rev]; exact this j i inej.symm (le_of_not_ge hij)
  rcases le_or_gt ‖a.c j‖ 2 with (Hj | Hj)
  -- case `‖c j‖ ≤ 2` (and therefore also `‖c i‖ ≤ 2`)
  · simp_rw [c', Hj, hij.trans Hj, if_true]
    exact exists_normalized_aux1 a lastr hτ δ hδ1 hδ2 i j inej
  -- case `2 < ‖c j‖`
  · have H'j : ‖a.c j‖ ≤ 2 ↔ False := by simpa only [not_le, iff_false] using Hj
    rcases le_or_gt ‖a.c i‖ 2 with (Hi | Hi)
    · -- case `‖c i‖ ≤ 2`
      simp_rw [c', Hi, if_true, H'j, if_false]
      exact exists_normalized_aux2 a lastc lastr hτ δ hδ1 hδ2 i j inej Hi Hj
    · -- case `2 < ‖c i‖`
      have H'i : ‖a.c i‖ ≤ 2 ↔ False := by simpa only [not_le, iff_false] using Hi
      simp_rw [c', H'i, if_false, H'j, if_false]
      exact exists_normalized_aux3 a lastc lastr hτ δ hδ1 i j inej Hi hij

end SatelliteConfig

variable (E)
variable [NormedSpace ℝ E] [FiniteDimensional ℝ E]

/-- In a normed vector space `E`, there can be no satellite configuration with `multiplicity E + 1`
points and the parameter `goodτ E`. This will ensure that in the inductive construction to get
the Besicovitch covering families, there will never be more than `multiplicity E` nonempty
families. -/
/-
**Besicovitch.isEmpty_satelliteConfig_multiplicity** 是 Mathlib 中的一个定理，位于命名空间 `Be
sicovitch`。
形式化陈述：isEmpty_satelliteConfig_multiplicity : IsEmpty (SatelliteConfig E (multipl
icity E) (goodτ E))
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Besicovitch.SatelliteConfig.exists_normalized`：exists_normalized {N : Na
t} {τ : Real} (a : SatelliteConfig E N τ) (lastc : a.c (last N) = 0) (lastr : a.
r (last N) = 1) (hτ : 1 <= τ) (δ : …
· 使用定理 `Besicovitch.SatelliteConfig.centerAndRescale_center`：centerAndRescale_ce
nter : a.centerAndRescale.c (last N) = 0
· 使用定理 `Besicovitch.SatelliteConfig.centerAndRescale_radius`：centerAndRescale_ra
dius {N : Nat} {τ : Real} (a : SatelliteConfig E N τ) : a.centerAndRescale.r (la
st N) = 1
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `Besicovitch.one_lt_goodτ`：one_lt_goodτ : 1 < goodτ E
· 使用引理 `le_rfl`：le_rfl : a <= a
· 使用定理 `Besicovitch.goodδ_lt_one`：goodδ_lt_one : goodδ E < 1
· 使用引理 `lt_irrefl`：lt_irrefl (a : α) : ¬a < a
· 使用定理 `LT.lt.trans_le`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a < b 
→ b ≤ c → a < c
· 使用定理 `Nat.lt_succ_self`：∀ (n : ℕ), n < n.succ
· 使用定理 `Besicovitch.le_multiplicity_of_δ_of_fin`：le_multiplicity_of_δ_of_fin {n 
: Nat} (f : Fin n -> E) (h : forall i, ‖f i‖ <= 2) (h' : Pairwise fun i j => 1 -
 goodδ E <= ‖f i - f j‖) : n …

--- 原说明 ---
In a normed vector space `E`, there can be no satellite configuration with `mult
iplicity E + 1`
points and the parameter `goodτ E`. This will ensure that in the inductive const
ruction to get
the Besicovitch covering families, there will never be more than `multiplicity E
` nonempty
families.
-/
theorem isEmpty_satelliteConfig_multiplicity :
    IsEmpty (SatelliteConfig E (multiplicity E) (goodτ E)) :=
  ⟨by
    intro a
    let b := a.centerAndRescale
    rcases b.exists_normalized a.centerAndRescale_center a.centerAndRescale_radius
        (one_lt_goodτ E).le (goodδ E) le_rfl (goodδ_lt_one E).le with
      ⟨c', c'_le_two, hc'⟩
    exact
      lt_irrefl _ ((Nat.lt_succ_self _).trans_le (le_multiplicity_of_δ_of_fin c' c'_le_two hc'))⟩
/-
**Besicovitch.** 是 Mathlib 中的一个实例，位于命名空间 `Besicovitch`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 100) instHasBesicovitchCovering : HasBesicovitchCovering E :=
  ⟨⟨multiplicity E, goodτ E, one_lt_goodτ E, isEmpty_satelliteConfig_multiplicity E⟩⟩

end Besicovitch

