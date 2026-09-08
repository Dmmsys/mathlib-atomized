/-
Copyright (c) 2022 Oliver Nash. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Nash
-/
module

public import Mathlib.MeasureTheory.Covering.Vitali
public import Mathlib.MeasureTheory.Covering.Differentiation

/-!
# Uniformly locally doubling measures and Lebesgue's density theorem

Lebesgue's density theorem states that given a set `S` in a sigma compact metric space with
locally-finite uniformly locally doubling measure `μ` then for almost all points `x` in `S`, for any
sequence of closed balls `B₀, B₁, B₂, ...` containing `x`, the limit `μ (S ∩ Bⱼ) / μ (Bⱼ) → 1` as
`j → ∞`.

In this file we combine general results about existence of Vitali families for uniformly locally
doubling measures with results about differentiation along a Vitali family to obtain an explicit
form of Lebesgue's density theorem.

## Main results
* `IsUnifLocDoublingMeasure.ae_tendsto_measure_inter_div`: a version of Lebesgue's density
  theorem for sequences of balls converging on a point but whose centres are not required to be
  fixed.

-/

@[expose] public section


noncomputable section

open Set Filter Metric MeasureTheory TopologicalSpace

open scoped NNReal Topology

namespace IsUnifLocDoublingMeasure

variable {α : Type*} [PseudoMetricSpace α] [MeasurableSpace α] (μ : Measure α)
  [IsUnifLocDoublingMeasure μ]

section

variable [SecondCountableTopology α] [BorelSpace α] [IsLocallyFiniteMeasure μ]

open scoped Topology

/-- A Vitali family in a space with a uniformly locally doubling measure, designed so that the sets
at `x` contain all `closedBall y r` when `dist x y ≤ K * r`. -/
irreducible_def vitaliFamily (K : ℝ) : VitaliFamily μ := by
  /- the Vitali covering theorem gives a family that works well at small scales, thanks to the
    doubling property. We enlarge this family to add large sets, to make sure that all balls and not
    only small ones belong to the family, for convenience. -/
  let R := scalingScaleOf μ (max (4 * K + 3) 3)
  have Rpos : 0 < R := scalingScaleOf_pos _ _
  have A : ∀ x : α, ∃ᶠ r in 𝓝[>] (0 : ℝ),
      μ (closedBall x (3 * r)) ≤ scalingConstantOf μ (max (4 * K + 3) 3) * μ (closedBall x r) := by
    intro x
    apply frequently_iff.2 fun {U} hU => ?_
    obtain ⟨ε, εpos, hε⟩ := mem_nhdsGT_iff_exists_Ioc_subset.1 hU
    refine ⟨min ε R, hε ⟨lt_min εpos Rpos, min_le_left _ _⟩, ?_⟩
    exact measure_mul_le_scalingConstantOf_mul μ
      ⟨zero_lt_three, le_max_right _ _⟩ (min_le_right _ _)
  exact (Vitali.vitaliFamily μ (scalingConstantOf μ (max (4 * K + 3) 3)) A).enlarge (R / 4)
    (by linarith)

/-- In the Vitali family `IsUnifLocDoublingMeasure.vitaliFamily K`, the sets based at `x`
contain all balls `closedBall y r` when `dist x y ≤ K * r`. -/
/-
**IsUnifLocDoublingMeasure.closedBall_mem_vitaliFamily_of_dist_le_mul** 是 Mathli
b 中的一个定理，位于命名空间 `IsUnifLocDoublingMeasure`。
形式化陈述：closedBall_mem_vitaliFamily_of_dist_le_mul {K : Real} {x y : α} {r : Real}
 (h : dist x y <= K * r) (rpos : 0 < r) : closedBall y r in (vitaliFamily μ K).s
etsAt x
参数：h : dist x y <= K * r；rpos : 0 < r。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `IsUnifLocDoublingMeasure.vitaliFamily_def`：∀ {α : Type u_2} [inst : Pseu
doMetricSpace α] [inst_1 : MeasurableSpace α] (μ : MeasureTheory.Measure α)   [i
nst_2 : IsUnifLocDoublingMeasur…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `Set.Nonempty.mono`：∀ {α : Type u} {s t : Set α}, s ⊆ t → s.Nonempty → t.
Nonempty
· 使用定理 `Metric.ball_subset_interior_closedBall`：ball_subset_interior_closedBall 
: ball x ε subseteq interior (closedBall x ε)
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Metric.nonempty_ball`：nonempty_ball : (ball x ε).Nonempty ↔ 0 < ε
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `BorelSpace.opensMeasurable`：∀ {α : Type u_6} [inst : TopologicalSpace α]
 [inst_1 : MeasurableSpace α] [BorelSpace α], OpensMeasurableSpace α
· 使用定理 `le_or_gt`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), a ≤ b ∨ b <
 a
· 使用定理 `Metric.closedBall_subset_closedBall'`：closedBall_subset_closedBall' (h :
 ε₁ + dist x y <= ε₂) : closedBall x ε₁ subseteq closedBall y ε₂
· 使用定理 `dist_comm`：dist_comm (x y : α) : dist x y = dist y x
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
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' * b' = c → a * b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.add_mul`：∀ {R : Type u_1} [inst : CommSemirin
g R] {a₁ a₂ b c₁ c₂ d : R},   a₁ * b = c₁ → a₂ * b = c₂ → c₁ + c₂ = d → (a₁ + a₂
) * b = d
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_add`：∀ {R : Type u_1} [inst : CommSemirin
g R] {a b₁ b₂ c₁ c₂ d : R},   a * b₁ = c₁ → a * b₂ = c₂ → c₁ + 0 + c₂ = d → a * 
(b₁ + b₂) = d
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_pf_left`：∀ {R : Type u_1} [inst : CommSem
iring R] {a₃ b c : R} (a₁ : R) (a₂ : ℕ), a₃ * b = c → a₁ ^ a₂ * a₃ * b = a₁ ^ a₂
 * c
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_pf_right`：∀ {R : Type u_1} [inst : CommSe
miring R] {a b₃ c : R} (b₁ : R) (b₂ : ℕ), a * b₃ = c → a * (b₁ ^ b₂ * b₃) = b₁ ^
 b₂ * c
· 使用定理 `Mathlib.Meta.NormNum.IsNat.to_raw_eq`：∀ {α : Type u} {a : α} {n : ℕ} [in
st : AddMonoidWithOne α], Mathlib.Meta.NormNum.IsNat a n → a = n.rawCast
（共 107 条，此处仅展示前 30 条）

--- 原说明 ---
In the Vitali family `IsUnifLocDoublingMeasure.vitaliFamily K`, the sets based a
t `x`
contain all balls `closedBall y r` when `dist x y ≤ K * r`.
-/
theorem closedBall_mem_vitaliFamily_of_dist_le_mul {K : ℝ} {x y : α} {r : ℝ} (h : dist x y ≤ K * r)
    (rpos : 0 < r) : closedBall y r ∈ (vitaliFamily μ K).setsAt x := by
  let R := scalingScaleOf μ (max (4 * K + 3) 3)
  simp only [vitaliFamily, VitaliFamily.enlarge, Vitali.vitaliFamily, mem_union, mem_ofPred_eq,
    isClosed_closedBall, true_and, (nonempty_ball.2 rpos).mono ball_subset_interior_closedBall,
    measurableSet_closedBall]
  /- The measure is doubling on scales smaller than `R`. Therefore, we treat differently small
    and large balls. For large balls, this follows directly from the enlargement we used in the
    definition. -/
  by_cases H : closedBall y r ⊆ closedBall x (R / 4)
  swap; · exact Or.inr H
  left
  /- For small balls, there is the difficulty that `r` could be large but still the ball could be
    small, if the annulus `{y | ε ≤ dist y x ≤ R/4}` is empty. We split between the cases `r ≤ R`
    and `r > R`, and use the doubling for the former and rough estimates for the latter. -/
  rcases le_or_gt r R with (hr | hr)
  · refine ⟨(K + 1) * r, ?_⟩
    constructor
    · apply closedBall_subset_closedBall'
      rw [dist_comm]
      linarith
    · have I1 : closedBall x (3 * ((K + 1) * r)) ⊆ closedBall y ((4 * K + 3) * r) := by
        apply closedBall_subset_closedBall'
        linarith
      have I2 : closedBall y ((4 * K + 3) * r) ⊆ closedBall y (max (4 * K + 3) 3 * r) := by
        gcongr
        exact le_max_left ..
      apply (measure_mono (I1.trans I2)).trans
      exact measure_mul_le_scalingConstantOf_mul _
        ⟨zero_lt_three.trans_le (le_max_right _ _), le_rfl⟩ hr
  · refine ⟨_, H, ?_⟩
    grw [scalingConstantOf, ← le_max_right, ENNReal.coe_one, one_mul,
      closedBall_subset_closedBall' (y := y)]
    have A : y ∈ closedBall y r := mem_closedBall_self rpos.le
    have B := mem_closedBall'.1 (H A)
    linarith
/-
**IsUnifLocDoublingMeasure.tendsto_closedBall_filterAt** 是 Mathlib 中的一个定理，位于命名空间
 `IsUnifLocDoublingMeasure`。
形式化陈述：tendsto_closedBall_filterAt {K : Real} {x : α} {ι : Type*} {l : Filter ι} 
(w : ι -> α) (δ : ι -> Real) (δlim : Tendsto δ l (𝓝[>] 0)) (xmem : forallᶠ j in 
l, x in closedBall (w j) (K * δ j)) : Tendsto (fun j => closedBall (w j) (δ j)) 
l ((vitaliFamily μ K).filterAt x)
参数：w : ι -> α；δ : ι -> Real；δlim : Tendsto δ l (𝓝[>] 0)；xmem : forallᶠ j in l, x
 in closedBall (w j) (K * δ j)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `VitaliFamily.tendsto_filterAt_iff`：tendsto_filterAt_iff {ι : Type*} {l :
 Filter ι} {f : ι -> Set X} {x : X} : Tendsto f l (v.filterAt x) ↔ (forallᶠ i in
 l, f i in v.setsAt x) …
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `self_mem_nhdsWithin`：self_mem_nhdsWithin {a : α} {s : Set α} : s in 𝓝[s]
 a
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `IsUnifLocDoublingMeasure.closedBall_mem_vitaliFamily_of_dist_le_mul`：clo
sedBall_mem_vitaliFamily_of_dist_le_mul {K : Real} {x y : α} {r : Real} (h : dis
t x y <= K * r) (rpos : 0 < r) : closedBall y r in (vital…
· 使用定理 `Filter.eq_or_neBot`：eq_or_neBot (f : Filter α) : f = ⊥ ∨ NeBot f
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Filter.Eventually.exists`：∀ {α : Type u} {p : α → Prop} {f : Filter α} [
f.NeBot], (∀ᶠ (x : α) in f, p x) → ∃ x, p x
· 使用定理 `Filter.Eventually.and`：∀ {α : Type u} {p q : α → Prop} {f : Filter α},  
 Filter.Eventually p f → Filter.Eventually q f → ∀ᶠ (x : α) in f, p x ∧ q x
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Metric.nonempty_closedBall`：nonempty_closedBall : (closedBall x ε).Nonem
pty ↔ 0 <= ε
· 使用定理 `mul_nonneg_iff_left_nonneg_of_pos`：mul_nonneg_iff_left_nonneg_of_pos [Po
sMulStrictMono R] [MulPosStrictMono R] (hb : 0 < b) : 0 <= a * b ↔ 0 <= a
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `IsStrictOrderedRing.toMulPosStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], MulPosStrictMono 
R
· 使用定理 `Set.mem_Ioi`：∀ {α : Type u_1} [inst : Preorder α] {b x : α}, x ∈ Set.Ioi
 b ↔ b < x
· 使用定理 `eventually_mem_of_tendsto_nhdsWithin`：eventually_mem_of_tendsto_nhdsWith
in {f : β -> α} {a : α} {s : Set α} {l : Filter β} (h : Tendsto f l (𝓝[s] a)) : 
forallᶠ i in l, f i in s
· 使用定理 `tendsto_nhds_of_tendsto_nhdsWithin`：tendsto_nhds_of_tendsto_nhdsWithin {
f : β -> α} {a : α} {s : Set α} {l : Filter β} (h : Tendsto f l (𝓝[s] a)) : Tend
sto f l (𝓝 a)
· 使用定理 `lt_of_not_ge`：∀ {α : Type u_1} [inst : LinearOrder α] {a b : α}, ¬b ≤ a 
→ a < b
· 使用定理 `Mathlib.Tactic.Linarith.lt_irrefl`：lt_irrefl {α : Type u} [Preorder α] {
a : α} : ¬a < a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Mathlib.Tactic.Ring.of_eq`：∀ {α : Sort u_2} {a b c : α}, a = c → b = c →
 a = b
· 使用定理 `Mathlib.Tactic.Ring.Common.add_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' + b' = c → a + b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.neg_congr`：∀ {R : Type u_2} [inst : CommRing 
R] {a a' b : R}, a = a' → -a' = b → -a = b
· 使用定理 `Mathlib.Tactic.Ring.cast_pos`：∀ {R : Type u_1} [inst : CommSemiring R] {
a : R} {n : ℕ}, Mathlib.Meta.NormNum.IsNat a n → a = n.rawCast + 0
· 使用定理 `Mathlib.Meta.NormNum.isNat_ofNat`：isNat_ofNat (α : Type u) [AddMonoidWit
hOne α] {a : α} {n : Nat} (h : n = a) : IsNat a n
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `Mathlib.Tactic.Ring.Common.neg_add`：∀ {R : Type u_2} [inst : CommRing R]
 {a₁ a₂ b₁ b₂ : R}, -a₁ = b₁ → -a₂ = b₂ → -(a₁ + a₂) = b₁ + b₂
· 使用定理 `Mathlib.Meta.NormNum.IsInt.to_raw_eq`：∀ {α : Type u} {a : α} {n : ℤ} [in
st : Ring α], Mathlib.Meta.NormNum.IsInt a n → a = n.rawCast
（共 77 条，此处仅展示前 30 条）
-/
theorem tendsto_closedBall_filterAt {K : ℝ} {x : α} {ι : Type*} {l : Filter ι} (w : ι → α)
    (δ : ι → ℝ) (δlim : Tendsto δ l (𝓝[>] 0)) (xmem : ∀ᶠ j in l, x ∈ closedBall (w j) (K * δ j)) :
    Tendsto (fun j => closedBall (w j) (δ j)) l ((vitaliFamily μ K).filterAt x) := by
  refine (vitaliFamily μ K).tendsto_filterAt_iff.mpr ⟨?_, fun ε hε => ?_⟩
  · filter_upwards [xmem, δlim self_mem_nhdsWithin] with j hj h'j
    exact closedBall_mem_vitaliFamily_of_dist_le_mul μ hj h'j
  · rcases l.eq_or_neBot with rfl | h
    · simp
    have hK : 0 ≤ K := by
      rcases (xmem.and (δlim self_mem_nhdsWithin)).exists with ⟨j, hj, h'j⟩
      have : 0 ≤ K * δ j := nonempty_closedBall.1 ⟨x, hj⟩
      exact (mul_nonneg_iff_left_nonneg_of_pos (mem_Ioi.1 h'j)).1 this
    have δpos := eventually_mem_of_tendsto_nhdsWithin δlim
    replace δlim := tendsto_nhds_of_tendsto_nhdsWithin δlim
    replace hK : 0 < K + 1 := by linarith
    apply (((Metric.tendsto_nhds.mp δlim _ (div_pos hε hK)).and δpos).and xmem).mono
    rintro j ⟨⟨hjε, hj₀ : 0 < δ j⟩, hx⟩ y hy
    replace hjε : (K + 1) * δ j < ε := by
      simpa [abs_eq_self.mpr hj₀.le] using (lt_div_iff₀' hK).mp hjε
    simp only [mem_closedBall] at hx hy ⊢
    linarith [dist_triangle_right y x (w j)]

end

section Applications

variable [SecondCountableTopology α] [BorelSpace α] [IsLocallyFiniteMeasure μ] {E : Type*}
  [NormedAddCommGroup E]

/-- A version of **Lebesgue's density theorem** for a sequence of closed balls whose centers are
not required to be fixed.

See also `Besicovitch.ae_tendsto_measure_inter_div`. -/
/-
**IsUnifLocDoublingMeasure.ae_tendsto_measure_inter_div** 是 Mathlib 中的一个定理，位于命名空
间 `IsUnifLocDoublingMeasure`。
形式化陈述：ae_tendsto_measure_inter_div (S : Set α) (K : Real) : forallᵐ x ∂μ.restric
t S, forall {ι : Type*} {l : Filter ι} (w : ι -> α) (δ : ι -> Real) (_ : Tendsto
 δ l (𝓝[>] 0)) (_ : forallᶠ j in l, x in closedBall (w j) (K * δ j)), Tendsto (f
un j => μ (S inter closedBall (w j) (δ j)) / μ (closedBall (w j) (δ j))) l (𝓝 1)
参数：S : Set α；K : Real。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `VitaliFamily.ae_tendsto_measure_inter_div`：ae_tendsto_measure_inter_div 
(s : Set α) : forallᵐ x ∂μ.restrict s, Tendsto (fun a => μ (s inter a) / μ a) (v
.filterAt x) (𝓝 1)
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `Filter.Tendsto.comp`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {f :
 α → β} {g : β → γ} {x : Filter α} {y : Filter β} {z : Filter γ},   Filter.Tends
to g y z …
· 使用定理 `IsUnifLocDoublingMeasure.tendsto_closedBall_filterAt`：tendsto_closedBall
_filterAt {K : Real} {x : α} {ι : Type*} {l : Filter ι} (w : ι -> α) (δ : ι -> R
eal) (δlim : Tendsto δ l (𝓝[>] 0)) (xmem :…

--- 原说明 ---
A version of **Lebesgue's density theorem** for a sequence of closed balls whose
 centers are
not required to be fixed.

See also `Besicovitch.ae_tendsto_measure_inter_div`.
-/
theorem ae_tendsto_measure_inter_div (S : Set α) (K : ℝ) : ∀ᵐ x ∂μ.restrict S,
    ∀ {ι : Type*} {l : Filter ι} (w : ι → α) (δ : ι → ℝ) (_ : Tendsto δ l (𝓝[>] 0))
      (_ : ∀ᶠ j in l, x ∈ closedBall (w j) (K * δ j)),
      Tendsto (fun j => μ (S ∩ closedBall (w j) (δ j)) / μ (closedBall (w j) (δ j))) l (𝓝 1) := by
  filter_upwards [(vitaliFamily μ K).ae_tendsto_measure_inter_div S] with x hx ι l w δ δlim
    xmem using hx.comp (tendsto_closedBall_filterAt μ _ _ δlim xmem)

/-- A version of **Lebesgue differentiation theorem** for a sequence of closed balls whose
centers are not required to be fixed. -/
/-
**IsUnifLocDoublingMeasure.ae_tendsto_average_norm_sub** 是 Mathlib 中的一个定理，位于命名空间
 `IsUnifLocDoublingMeasure`。
形式化陈述：ae_tendsto_average_norm_sub {f : α -> E} (hf : LocallyIntegrable f μ) (K :
 Real) : forallᵐ x ∂μ, forall {ι : Type*} {l : Filter ι} (w : ι -> α) (δ : ι -> 
Real) (_ : Tendsto δ l (𝓝[>] 0)) (_ : forallᶠ j in l, x in closedBall (w j) (K *
 δ j)), Tendsto (fun j => ⨍ y in closedBall (w j) (δ j), ‖f y - f x‖ ∂μ) l (𝓝 0)
参数：hf : LocallyIntegrable f μ；K : Real。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `VitaliFamily.ae_tendsto_average_norm_sub`：ae_tendsto_average_norm_sub {f
 : α -> E} (hf : LocallyIntegrable f μ) : forallᵐ x ∂μ, Tendsto (fun a => ⨍ y in
 a, ‖f y - f x‖ ∂μ) (v.filterA…
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `Filter.Tendsto.comp`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {f :
 α → β} {g : β → γ} {x : Filter α} {y : Filter β} {z : Filter γ},   Filter.Tends
to g y z …
· 使用定理 `IsUnifLocDoublingMeasure.tendsto_closedBall_filterAt`：tendsto_closedBall
_filterAt {K : Real} {x : α} {ι : Type*} {l : Filter ι} (w : ι -> α) (δ : ι -> R
eal) (δlim : Tendsto δ l (𝓝[>] 0)) (xmem :…

--- 原说明 ---
A version of **Lebesgue differentiation theorem** for a sequence of closed balls
 whose
centers are not required to be fixed.
-/
theorem ae_tendsto_average_norm_sub {f : α → E} (hf : LocallyIntegrable f μ) (K : ℝ) : ∀ᵐ x ∂μ,
    ∀ {ι : Type*} {l : Filter ι} (w : ι → α) (δ : ι → ℝ) (_ : Tendsto δ l (𝓝[>] 0))
      (_ : ∀ᶠ j in l, x ∈ closedBall (w j) (K * δ j)),
      Tendsto (fun j => ⨍ y in closedBall (w j) (δ j), ‖f y - f x‖ ∂μ) l (𝓝 0) := by
  filter_upwards [(vitaliFamily μ K).ae_tendsto_average_norm_sub hf] with x hx ι l w δ δlim
    xmem using hx.comp (tendsto_closedBall_filterAt μ _ _ δlim xmem)

/-- A version of **Lebesgue differentiation theorem** for a sequence of closed balls whose
centers are not required to be fixed. -/
/-
**IsUnifLocDoublingMeasure.ae_tendsto_average** 是 Mathlib 中的一个定理，位于命名空间 `IsUnifL
ocDoublingMeasure`。
形式化陈述：ae_tendsto_average [NormedSpace Real E] [CompleteSpace E] {f : α -> E} (hf
 : LocallyIntegrable f μ) (K : Real) : forallᵐ x ∂μ, forall {ι : Type*} {l : Fil
ter ι} (w : ι -> α) (δ : ι -> Real) (_ : Tendsto δ l (𝓝[>] 0)) (_ : forallᶠ j in
 l, x in closedBall (w j) (K * δ j)), Tendsto (fun j => ⨍ y in closedBall (w j) 
(δ j), f y ∂μ) l (𝓝 (f x))
参数：hf : LocallyIntegrable f μ；K : Real。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `VitaliFamily.ae_tendsto_average`：ae_tendsto_average [NormedSpace Real E]
 [CompleteSpace E] {f : α -> E} (hf : LocallyIntegrable f μ) : forallᵐ x ∂μ, Ten
dsto (fun a => ⨍ y in…
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `Filter.Tendsto.comp`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {f :
 α → β} {g : β → γ} {x : Filter α} {y : Filter β} {z : Filter γ},   Filter.Tends
to g y z …
· 使用定理 `IsUnifLocDoublingMeasure.tendsto_closedBall_filterAt`：tendsto_closedBall
_filterAt {K : Real} {x : α} {ι : Type*} {l : Filter ι} (w : ι -> α) (δ : ι -> R
eal) (δlim : Tendsto δ l (𝓝[>] 0)) (xmem :…

--- 原说明 ---
A version of **Lebesgue differentiation theorem** for a sequence of closed balls
 whose
centers are not required to be fixed.
-/
theorem ae_tendsto_average [NormedSpace ℝ E] [CompleteSpace E]
    {f : α → E} (hf : LocallyIntegrable f μ) (K : ℝ) : ∀ᵐ x ∂μ,
      ∀ {ι : Type*} {l : Filter ι} (w : ι → α) (δ : ι → ℝ) (_ : Tendsto δ l (𝓝[>] 0))
        (_ : ∀ᶠ j in l, x ∈ closedBall (w j) (K * δ j)),
        Tendsto (fun j => ⨍ y in closedBall (w j) (δ j), f y ∂μ) l (𝓝 (f x)) := by
  filter_upwards [(vitaliFamily μ K).ae_tendsto_average hf] with x hx ι l w δ δlim xmem using
    hx.comp (tendsto_closedBall_filterAt μ _ _ δlim xmem)

end Applications

end IsUnifLocDoublingMeasure

