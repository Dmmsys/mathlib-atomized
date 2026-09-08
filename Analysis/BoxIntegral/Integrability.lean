/-
Copyright (c) 2021 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
module

public import Mathlib.Analysis.BoxIntegral.Basic
public import Mathlib.MeasureTheory.Integral.Bochner.Set

/-!
# McShane integrability vs Bochner integrability

In this file we prove that any Bochner integrable function is McShane integrable (hence, it is
Henstock and `GP` integrable) with the same integral. The proof is based on
[Russel A. Gordon, *The integrals of Lebesgue, Denjoy, Perron, and Henstock*][Gordon55].

We deduce that the same is true for the Riemann integral for continuous functions.

## Tags

integral, McShane integral, Bochner integral
-/

public section

open scoped NNReal ENNReal Topology

universe u v

variable {ι : Type u} {E : Type v} [Fintype ι] [NormedAddCommGroup E] [NormedSpace ℝ E]

open MeasureTheory Metric Set Finset Filter BoxIntegral

namespace BoxIntegral

set_option backward.defeqAttrib.useBackward true in
/-- The indicator function of a measurable set is McShane integrable with respect to any
locally-finite measure. -/
/-
**BoxIntegral.hasIntegralIndicatorConst** 是 Mathlib 中的一个定理，位于命名空间 `BoxIntegral`。
形式化陈述：hasIntegralIndicatorConst (l : IntegrationParams) (hl : l.bRiemann = false
) {s : Set (ι -> Real)} (hs : MeasurableSet s) (I : Box ι) (y : E) (μ : Measure 
(ι -> Real)) [IsLocallyFiniteMeasure μ] : HasIntegral.{u, v, v} I l (s.indicator
 fun _ => y) μ.toBoxAdditive.toSMul (μ.real (s inter I) • y)
参数：l : IntegrationParams；hl : l.bRiemann = false；ι -> Real；hs : MeasurableSet s；
I : Box ι；y : E；μ : Measure (ι -> Real)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `BoxIntegral.HasIntegral.of_mul`：∀ {ι : Type u} {E : Type v} {F : Type w}
 [inst : NormedAddCommGroup E] [inst_1 : NormedSpace ℝ E]   [inst_2 : NormedAddC
ommGroup F] [inst_3 …
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `CanLift.prf`：∀ {α : Sort u_1} {β : Sort u_2} {coe : outParam (β → α)} {c
ond : outParam (α → Prop)} [self : CanLift α β coe cond]   (x : α), cond x → ∃ y
,…
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `LT.lt.ne`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≠ b
· 使用定理 `LE.le.trans_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b 
→ b < c → a < c
· 使用定理 `MeasureTheory.measure_mono`：measure_mono (h : s subseteq t) : μ s <= μ t
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `Set.inter_subset_right`：inter_subset_right {s t : Set α} : s inter t sub
seteq t
· 使用定理 `BoxIntegral.Box.measure_Icc_lt_top`：measure_Icc_lt_top (μ : Measure (ι -
> Real)) [IsLocallyFiniteMeasure μ] : μ (Box.Icc I) < ∞
· 使用定理 `BoxIntegral.Box.measure_coe_lt_top`：measure_coe_lt_top (μ : Measure (ι -
> Real)) [IsLocallyFiniteMeasure μ] : μ I < ∞
· 使用定理 `MeasurableSet.exists_isClosed_sdiff_lt`：∀ {α : Type u_1} [inst : Measura
bleSpace α] {μ : MeasureTheory.Measure α} [inst_1 : TopologicalSpace α]   [Opens
MeasurableSpace α] [μ.Weakly…
· 使用定理 `Finite.to_countable`：∀ {α : Sort u} [Finite α], Countable α
· 使用定理 `instSecondCountableTopologyReal`：SecondCountableTopology ℝ
· 使用定理 `BorelSpace.opensMeasurable`：∀ {α : Type u_6} [inst : TopologicalSpace α]
 [inst_1 : MeasurableSpace α] [BorelSpace α], OpensMeasurableSpace α
· 使用定理 `MeasureTheory.Measure.WeaklyRegular.of_pseudoMetrizableSpace_secondCount
able_of_locallyFinite`：∀ {X : Type u_3} [inst : TopologicalSpace X] [Topological
Space.PseudoMetrizableSpace X] [SecondCountableTopology X]   [inst_3 : Measurabl
eSp…
· 使用定理 `PseudoEMetricSpace.pseudoMetrizableSpace`：∀ {α : Type u_2} [inst : Pseud
oEMetricSpace α], TopologicalSpace.PseudoMetrizableSpace α
· 使用定理 `TopologicalSpace.instSecondCountableTopologyForallOfCountable`：∀ {ι : Ty
pe u_1} {X : ι → Type u_2} [Countable ι] [inst : (a : ι) → TopologicalSpace (X a
)]   [∀ (a : ι), SecondCountableTopology (X a)], Se…
· 使用定理 `MeasurableSet.inter`：∀ {α : Type u_1} {m : MeasurableSpace α} {s₁ s₂ : S
et α}, MeasurableSet s₁ → MeasurableSet s₂ → MeasurableSet (s₁ ∩ s₂)
· 使用定理 `BoxIntegral.Box.measurableSet_Icc`：measurableSet_Icc : MeasurableSet (Bo
x.Icc I)
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `ENNReal.coe_pos`：∀ {r : NNReal}, 0 < ↑r ↔ 0 < r
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `NNReal.coe_pos`：∀ {r : NNReal}, 0 < ↑r ↔ 0 < r
· 使用定理 `MeasurableSet.exists_isOpen_sdiff_lt`：∀ {α : Type u_1} [inst : Measurabl
eSpace α] {μ : MeasureTheory.Measure α} [inst_1 : TopologicalSpace α] [μ.OuterRe
gular]   {A : Set α}, Meas…
· 使用定理 `MeasureTheory.Measure.WeaklyRegular.toOuterRegular`：∀ {α : Type u_1} {in
st : MeasurableSpace α} {inst_1 : TopologicalSpace α} {μ : MeasureTheory.Measure
 α}   [self : μ.WeaklyRegular], μ.OuterR…
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Filter.HasBasis.mem_iff`：∀ {α : Type u_1} {ι : Sort u_4} {l : Filter α} 
{p : ι → Prop} {s : ι → Set α} {t : Set α},   l.HasBasis p s → (t ∈ l ↔ ∃ i, p i
 ∧ s i ⊆ t)
· 使用定理 `Metric.nhds_basis_closedBall`：nhds_basis_closedBall : (𝓝 x).HasBasis (fu
n ε : Real => 0 < ε) (closedBall x)
（共 72 条，此处仅展示前 30 条）

--- 原说明 ---
The indicator function of a measurable set is McShane integrable with respect to
 any
locally-finite measure.
-/
theorem hasIntegralIndicatorConst (l : IntegrationParams) (hl : l.bRiemann = false)
    {s : Set (ι → ℝ)} (hs : MeasurableSet s) (I : Box ι) (y : E) (μ : Measure (ι → ℝ))
    [IsLocallyFiniteMeasure μ] :
    HasIntegral.{u, v, v} I l (s.indicator fun _ => y) μ.toBoxAdditive.toSMul
      (μ.real (s ∩ I) • y) := by
  refine HasIntegral.of_mul ‖y‖ fun ε ε0 => ?_
  lift ε to ℝ≥0 using ε0.le; rw [NNReal.coe_pos] at ε0
  /- First we choose a closed set `F ⊆ s ∩ I.Icc` and an open set `U ⊇ s` such that
    both `(s ∩ I.Icc) \ F` and `U \ s` have measure less than `ε`. -/
  have A : μ (s ∩ Box.Icc I) ≠ ∞ :=
    ((measure_mono Set.inter_subset_right).trans_lt (I.measure_Icc_lt_top μ)).ne
  have B : μ (s ∩ I) ≠ ∞ :=
    ((measure_mono Set.inter_subset_right).trans_lt (I.measure_coe_lt_top μ)).ne
  obtain ⟨F, hFs, hFc, hμF⟩ : ∃ F, F ⊆ s ∩ Box.Icc I ∧ IsClosed F ∧ μ ((s ∩ Box.Icc I) \ F) < ε :=
    (hs.inter I.measurableSet_Icc).exists_isClosed_sdiff_lt A (ENNReal.coe_pos.2 ε0).ne'
  obtain ⟨U, hsU, hUo, hUt, hμU⟩ :
      ∃ U, s ∩ Box.Icc I ⊆ U ∧ IsOpen U ∧ μ U < ∞ ∧ μ (U \ (s ∩ Box.Icc I)) < ε :=
    (hs.inter I.measurableSet_Icc).exists_isOpen_sdiff_lt A (ENNReal.coe_pos.2 ε0).ne'
  /- Then we choose `r` so that `closed_ball x (r x) ⊆ U` whenever `x ∈ s ∩ I.Icc` and
    `closed_ball x (r x)` is disjoint with `F` otherwise. -/
  have : ∀ x ∈ s ∩ Box.Icc I, ∃ r : Ioi (0 : ℝ), closedBall x r ⊆ U := fun x hx => by
    rcases nhds_basis_closedBall.mem_iff.1 (hUo.mem_nhds <| hsU hx) with ⟨r, hr₀, hr⟩
    exact ⟨⟨r, hr₀⟩, hr⟩
  choose! rs hrsU using this
  have : ∀ x ∈ Box.Icc I \ s, ∃ r : Ioi (0 : ℝ), closedBall x r ⊆ Fᶜ := fun x hx => by
    obtain ⟨r, hr₀, hr⟩ :=
      nhds_basis_closedBall.mem_iff.1 (hFc.isOpen_compl.mem_nhds fun hx' => hx.2 (hFs hx').1)
    exact ⟨⟨r, hr₀⟩, hr⟩
  choose! rs' hrs'F using this
  classical
  set r : (ι → ℝ) → Ioi (0 : ℝ) := s.piecewise rs rs'
  refine ⟨fun _ => r, fun c => l.rCond_of_bRiemann_eq_false hl, fun c π hπ hπp => ?_⟩; rw [mul_comm]
  /- Then the union of boxes `J ∈ π` such that `π.tag ∈ s` includes `F` and is included by `U`,
    hence its measure is `ε`-close to the measure of `s`. -/
  dsimp [integralSum]
  simp only [dist_eq_norm, ← indicator_const_smul_apply, sum_indicator_eq_sum_filter, ← sum_smul,
    ← sub_smul, norm_smul, Real.norm_eq_abs, ← Prepartition.filter_boxes,
    ← Prepartition.measure_iUnion_toReal]
  gcongr
  set t := (π.filter (π.tag · ∈ s)).iUnion
  change abs (μ.real t - μ.real (s ∩ I)) ≤ ε
  have htU : t ⊆ U ∩ I := by
    simp only [t, TaggedPrepartition.iUnion_def, iUnion_subset_iff, TaggedPrepartition.mem_filter,
      and_imp]
    refine fun J hJ hJs x hx => ⟨hrsU _ ⟨hJs, π.tag_mem_Icc J⟩ ?_, π.le_of_mem' J hJ hx⟩
    simpa only [r, s.piecewise_eq_of_mem _ _ hJs] using hπ.1 J hJ (Box.coe_subset_Icc hx)
  refine abs_sub_le_iff.2 ⟨?_, ?_⟩
  · refine (ENNReal.le_toReal_sub B).trans (ENNReal.toReal_le_coe_of_le_coe ?_)
    refine (tsub_le_tsub (measure_mono htU) le_rfl).trans (le_measure_sdiff.trans ?_)
    refine (measure_mono fun x hx => ?_).trans hμU.le
    exact ⟨hx.1.1, fun hx' => hx.2 ⟨hx'.1, hx.1.2⟩⟩
  · have hμt : μ t ≠ ∞ := ((measure_mono (htU.trans inter_subset_left)).trans_lt hUt).ne
    refine (ENNReal.le_toReal_sub hμt).trans (ENNReal.toReal_le_coe_of_le_coe ?_)
    refine le_measure_sdiff.trans ((measure_mono ?_).trans hμF.le)
    rintro x ⟨⟨hxs, hxI⟩, hxt⟩
    refine ⟨⟨hxs, Box.coe_subset_Icc hxI⟩, fun hxF => hxt ?_⟩
    simp only [t, TaggedPrepartition.iUnion_def, TaggedPrepartition.mem_filter, Set.mem_iUnion]
    rcases hπp x hxI with ⟨J, hJπ, hxJ⟩
    refine ⟨J, ⟨hJπ, ?_⟩, hxJ⟩
    contrapose hxF
    refine hrs'F _ ⟨π.tag_mem_Icc J, hxF⟩ ?_
    simpa only [r, s.piecewise_eq_of_notMem _ _ hxF] using hπ.1 J hJπ (Box.coe_subset_Icc hxJ)

/-- If `f` is a.e. equal to zero on a rectangular box, then it has McShane integral zero on this
box. -/
/-
**BoxIntegral.HasIntegral.of_aeEq_zero** 是 Mathlib 中的一个定理，位于命名空间 `BoxIntegral.Ha
sIntegral`。
形式化陈述：∀ {ι : Type u} {E : Type v} [inst : Fintype ι] [inst_1 : NormedAddCommGrou
p E] [inst_2 : NormedSpace ℝ E]   {l : BoxIntegral.IntegrationParams} {I : BoxIn
tegral.Box ι} {f : (ι → ℝ) → E} {μ : MeasureTheory.Measure (ι → ℝ)}   [inst_3 : 
MeasureTheory.IsLocallyFiniteMeasure μ],   f =ᵐ[μ.restrict ↑I] 0 → l.bRiemann = 
false → BoxIntegral.HasIntegral I l f μ.toBoxAdditive.toSMul 0
参数：ι → ℝ；ι → ℝ。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `BoxIntegral.hasIntegral_iff`：hasIntegral_iff : HasIntegral I l f vol y ↔
 forall ε > (0 : Real), exists r : Real>=0 -> Realⁿ -> Ioi (0 : Real), (forall c
, l.RCond (r c)) …
· 使用定理 `CanLift.prf`：∀ {α : Sort u_1} {β : Sort u_2} {coe : outParam (β → α)} {c
ond : outParam (α → Prop)} [self : CanLift α β coe cond]   (x : α), cond x → ∃ y
,…
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `GT.gt.lt`：∀ {α : Type u_2} [inst : LT α] {a b : α}, a > b → b < a
· 使用定理 `NNReal.exists_pos_sum_of_countable`：exists_pos_sum_of_countable {ε : Rea
l>=0} (hε : ε != 0) (ι) [Countable ι] : exists ε' : ι -> Real>=0, (forall i, 0 <
 ε' i) ∧ exists c, HasSu…
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `NNReal.coe_pos`：∀ {r : NNReal}, 0 < ↑r ↔ 0 < r
· 使用定理 `gt_iff_lt`：∀ {α : Type u_1} [inst : LT α] {x y : α}, x > y ↔ y < x
· 使用定理 `instCountableNat`：Countable ℕ
· 使用定理 `BoxIntegral.Box.measure_coe_lt_top`：measure_coe_lt_top (μ : Measure (ι -
> Real)) [IsLocallyFiniteMeasure μ] : μ I < ∞
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `Set.exists_isOpen_lt_of_lt`：∀ {α : Type u_1} [inst : MeasurableSpace α] 
{μ : MeasureTheory.Measure α} [inst_1 : TopologicalSpace α] [μ.OuterRegular]   (
A : Set α) (r : …
· 使用定理 `MeasureTheory.Measure.WeaklyRegular.toOuterRegular`：∀ {α : Type u_1} {in
st : MeasurableSpace α} {inst_1 : TopologicalSpace α} {μ : MeasureTheory.Measure
 α}   [self : μ.WeaklyRegular], μ.OuterR…
· 使用定理 `MeasureTheory.Measure.WeaklyRegular.of_pseudoMetrizableSpace_secondCount
able_of_locallyFinite`：∀ {X : Type u_3} [inst : TopologicalSpace X] [Topological
Space.PseudoMetrizableSpace X] [SecondCountableTopology X]   [inst_3 : Measurabl
eSp…
· 使用定理 `PseudoEMetricSpace.pseudoMetrizableSpace`：∀ {α : Type u_2} [inst : Pseud
oEMetricSpace α], TopologicalSpace.PseudoMetrizableSpace α
· 使用定理 `TopologicalSpace.instSecondCountableTopologyForallOfCountable`：∀ {ι : Ty
pe u_1} {X : ι → Type u_2} [Countable ι] [inst : (a : ι) → TopologicalSpace (X a
)]   [∀ (a : ι), SecondCountableTopology (X a)], Se…
· 使用定理 `Finite.to_countable`：∀ {α : Sort u} [Finite α], Countable α
· 使用定理 `instSecondCountableTopologyReal`：SecondCountableTopology ℝ
· 使用定理 `MeasureTheory.instIsLocallyFiniteMeasureRestrict`：∀ {α : Type u_1} {m0 :
 MeasurableSpace α} {s : Set α} [inst : TopologicalSpace α] (μ : MeasureTheory.M
easure α)   [hμ : MeasureTheory.IsLoca…
· 使用定理 `CharP.cast_eq_zero`：∀ (R : Type u_1) [inst : AddMonoidWithOne R] (p : ℕ)
 [CharP R p], ↑p = 0
· 使用定理 `ENNReal.instCharZero`：CharZero ENNReal
（共 103 条，此处仅展示前 30 条）

--- 原说明 ---
If `f` is a.e. equal to zero on a rectangular box, then it has McShane integral 
zero on this
box.
-/
theorem HasIntegral.of_aeEq_zero {l : IntegrationParams} {I : Box ι} {f : (ι → ℝ) → E}
    {μ : Measure (ι → ℝ)} [IsLocallyFiniteMeasure μ] (hf : f =ᵐ[μ.restrict I] 0)
    (hl : l.bRiemann = false) : HasIntegral.{u, v, v} I l f μ.toBoxAdditive.toSMul 0 := by
  /- Each set `{x | n < ‖f x‖ ≤ n + 1}`, `n : ℕ`, has measure zero. We cover it by an open set of
    measure less than `ε / 2 ^ n / (n + 1)`. Then the norm of the integral sum is less than `ε`. -/
  refine hasIntegral_iff.2 fun ε ε0 => ?_
  lift ε to ℝ≥0 using ε0.lt.le; rw [gt_iff_lt, NNReal.coe_pos] at ε0
  rcases NNReal.exists_pos_sum_of_countable ε0.ne' ℕ with ⟨δ, δ0, c, hδc, hcε⟩
  have := Fact.mk (I.measure_coe_lt_top μ)
  change μ.restrict I {x | f x ≠ 0} = 0 at hf
  set N : (ι → ℝ) → ℕ := fun x => ⌈‖f x‖⌉₊
  have N0 : ∀ {x}, N x = 0 ↔ f x = 0 := by simp [N]
  have : ∀ n, ∃ U, N ⁻¹' {n} ⊆ U ∧ IsOpen U ∧ μ.restrict I U < δ n / n := fun n ↦ by
    refine (N ⁻¹' {n}).exists_isOpen_lt_of_lt _ ?_
    rcases n with - | n
    · simp [ENNReal.div_zero (ENNReal.coe_pos.2 (δ0 _)).ne']
    · refine (measure_mono_null ?_ hf).le.trans_lt ?_
      · exact fun x hxN hxf => n.succ_ne_zero ((Eq.symm hxN).trans <| N0.2 hxf)
      · simp [(δ0 _).ne']
  choose U hNU hUo hμU using this
  have : ∀ x, ∃ r : Ioi (0 : ℝ), closedBall x r ⊆ U (N x) := fun x => by
    obtain ⟨r, hr₀, hr⟩ := nhds_basis_closedBall.mem_iff.1 ((hUo _).mem_nhds (hNU _ rfl))
    exact ⟨⟨r, hr₀⟩, hr⟩
  choose r hrU using this
  refine ⟨fun _ => r, fun c => l.rCond_of_bRiemann_eq_false hl, fun c π hπ _ => ?_⟩
  rw [dist_eq_norm, sub_zero, ← integralSum_fiberwise fun J => N (π.tag J)]
  grw [← hcε, ← sum_le_hasSum _ (fun n _ => (δ n).2) (NNReal.hasSum_coe.2 hδc)]
  apply norm_sum_le_of_le
  rintro n -
  dsimp [integralSum]
  have : ∀ J ∈ π.filter fun J => N (π.tag J) = n,
      ‖μ.real ↑J • f (π.tag J)‖ ≤ μ.real J * n := fun J hJ ↦ by
    rw [TaggedPrepartition.mem_filter] at hJ
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg measureReal_nonneg]
    gcongr
    exact hJ.2 ▸ Nat.le_ceil _
  refine (norm_sum_le_of_le _ this).trans ?_; clear this
  rw [← sum_mul, ← Prepartition.measure_iUnion_toReal]
  let m := μ (π.filter fun J => N (π.tag J) = n).iUnion
  change m.toReal * ↑n ≤ ↑(δ n)
  have : m < δ n / n := by
    simp only [Measure.restrict_apply (hUo _).measurableSet] at hμU
    refine (measure_mono ?_).trans_lt (hμU _)
    simp only [Set.subset_def, TaggedPrepartition.mem_iUnion, TaggedPrepartition.mem_filter]
    rintro x ⟨J, ⟨hJ, rfl⟩, hx⟩
    exact ⟨hrU _ (hπ.1 _ hJ (Box.coe_subset_Icc hx)), π.le_of_mem' J hJ hx⟩
  clear_value m
  lift m to ℝ≥0 using ne_top_of_lt this
  grw [ENNReal.coe_toReal, ← NNReal.coe_natCast, ← NNReal.coe_mul, NNReal.coe_le_coe, ←
    ENNReal.coe_le_coe, ENNReal.coe_mul, ENNReal.coe_natCast, mul_comm, this, ENNReal.mul_div_le]

/-- If `f` has integral `y` on a box `I` with respect to a locally finite measure `μ` and `g` is
a.e. equal to `f` on `I`, then `g` has the same integral on `I`. -/
/-
**BoxIntegral.HasIntegral.congr_ae** 是 Mathlib 中的一个定理，位于命名空间 `BoxIntegral.HasInt
egral`。
形式化陈述：∀ {ι : Type u} {E : Type v} [inst : Fintype ι] [inst_1 : NormedAddCommGrou
p E] [inst_2 : NormedSpace ℝ E]   {l : BoxIntegral.IntegrationParams} {I : BoxIn
tegral.Box ι} {y : E} {f g : (ι → ℝ) → E}   {μ : MeasureTheory.Measure (ι → ℝ)} 
[inst_3 : MeasureTheory.IsLocallyFiniteMeasure μ],   BoxIntegral.HasIntegral I l
 f μ.toBoxAdditive.toSMul y →     f =ᵐ[μ.restrict ↑I] g → l.bRiemann = false → B
oxIntegral.HasIntegral I l g μ.toBoxAdditive.toSMul y
参数：ι → ℝ；ι → ℝ。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `Filter.Eventually.mono`：∀ {α : Type u} {p q : α → Prop} {f : Filter α}, 
(∀ᶠ (x : α) in f, p x) → (∀ (x : α), p x → q x) → ∀ᶠ (x : α) in f, q x
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `sub_eq_zero`：∀ {G : Type u_3} [inst : AddGroup G] {a b : G}, a - b = 0 ↔
 a = b
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `add_sub_cancel`：∀ {G : Type u_3} [inst : AddCommGroup G] (a b : G), a + 
(b - a) = b
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `BoxIntegral.HasIntegral.add`：∀ {ι : Type u} {E : Type v} {F : Type w} [i
nst : NormedAddCommGroup E] [inst_1 : NormedSpace ℝ E]   [inst_2 : NormedAddComm
Group F] [inst_3 …
· 使用定理 `BoxIntegral.HasIntegral.of_aeEq_zero`：∀ {ι : Type u} {E : Type v} [inst 
: Fintype ι] [inst_1 : NormedAddCommGroup E] [inst_2 : NormedSpace ℝ E]   {l : B
oxIntegral.IntegrationPara…

--- 原说明 ---
If `f` has integral `y` on a box `I` with respect to a locally finite measure `μ
` and `g` is
a.e. equal to `f` on `I`, then `g` has the same integral on `I`.
-/
theorem HasIntegral.congr_ae {l : IntegrationParams} {I : Box ι} {y : E} {f g : (ι → ℝ) → E}
    {μ : Measure (ι → ℝ)} [IsLocallyFiniteMeasure μ]
    (hf : HasIntegral.{u, v, v} I l f μ.toBoxAdditive.toSMul y) (hfg : f =ᵐ[μ.restrict I] g)
    (hl : l.bRiemann = false) : HasIntegral.{u, v, v} I l g μ.toBoxAdditive.toSMul y := by
  have : g - f =ᵐ[μ.restrict I] 0 := hfg.mono fun x hx => sub_eq_zero.2 hx.symm
  simpa using hf.add (HasIntegral.of_aeEq_zero this hl)

end BoxIntegral

namespace MeasureTheory

namespace SimpleFunc

/-- A simple function is McShane integrable w.r.t. any locally finite measure. -/
/-
**MeasureTheory.SimpleFunc.hasBoxIntegral** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheo
ry.SimpleFunc`。
形式化陈述：hasBoxIntegral (f : SimpleFunc (ι -> Real) E) (μ : Measure (ι -> Real)) [I
sLocallyFiniteMeasure μ] (I : Box ι) (l : IntegrationParams) (hl : l.bRiemann = 
false) : HasIntegral.{u, v, v} I l f μ.toBoxAdditive.toSMul (f.integral (μ.restr
ict I))
参数：f : SimpleFunc (ι -> Real) E；μ : Measure (ι -> Real)；I : Box ι；l : Integratio
nParams；hl : l.bRiemann = false。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.SimpleFunc.induction`：∀ {α : Type u_5} {γ : Type u_6} [ins
t : MeasurableSpace α] [inst_1 : AddZeroClass γ]   {motive : MeasureTheory.Simpl
eFunc α γ → Prop},   (∀ …
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.piecewise_eq_indicator`：∀ {α : Type u_1} {M : Type u_3} [inst : Zero
 M] {s : Set α} {f : α → M} [inst_1 : DecidablePred fun x => x ∈ s],   s.piecewi
se f 0 = s.indic…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `MeasureTheory.SimpleFunc.integral_piecewise_zero`：integral_piecewise_zer
o {m : MeasurableSpace α} (f : α ->ₛ F) (μ : Measure α) {s : Set α} (hs : Measur
ableSet s) : (piecewise s hs f 0).inte…
· 使用定理 `MeasureTheory.Measure.restrict_restrict`：restrict_restrict (hs : Measura
bleSet s) : (μ.restrict t).restrict s = μ.restrict (s inter t)
· 使用定理 `MeasureTheory.SimpleFunc.integral_const`：integral_const {m : MeasurableS
pace α} (μ : Measure α) (y : F) : (const α y).integral μ = μ.real univ • y
· 使用定理 `MeasureTheory.measureReal_restrict_apply`：measureReal_restrict_apply (ht
 : MeasurableSet t) : (μ.restrict s).real t = μ.real (t inter s)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Set.univ_inter`：univ_inter (a : Set α) : univ inter a = a
· 使用定理 `BoxIntegral.hasIntegralIndicatorConst`：hasIntegralIndicatorConst (l : In
tegrationParams) (hl : l.bRiemann = false) {s : Set (ι -> Real)} (hs : Measurabl
eSet s) (I : Box ι) (y : E)…
· 使用定理 `BoxIntegral.Box.measure_coe_lt_top`：measure_coe_lt_top (μ : Measure (ι -
> Real)) [IsLocallyFiniteMeasure μ] : μ I < ∞
· 使用定理 `MeasureTheory.SimpleFunc.integral_add`：integral_add {f g : α ->ₛ E} (hf 
: Integrable f μ) (hg : Integrable g μ) : integral μ (f + g) = integral μ f + in
tegral μ g
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `MeasureTheory.SimpleFunc.integrable_iff`：integrable_iff {f : α ->ₛ E} : 
Integrable f μ ↔ forall y, y != 0 -> μ (f ⁻¹' {y}) < ∞
· 使用定理 `MeasureTheory.measure_lt_top`：measure_lt_top (μ : Measure α) [IsFiniteMe
asure μ] (s : Set α) : μ s < ∞
· 使用定理 `MeasureTheory.Restrict.isFiniteMeasure`：∀ {α : Type u_1} {m0 : Measurabl
eSpace α} {s : Set α} (μ : MeasureTheory.Measure α) [hs : Fact (μ s < ⊤)],   Mea
sureTheory.IsFiniteMeasure (…
· 使用定理 `BoxIntegral.HasIntegral.add`：∀ {ι : Type u} {E : Type v} {F : Type w} [i
nst : NormedAddCommGroup E] [inst_1 : NormedSpace ℝ E]   [inst_2 : NormedAddComm
Group F] [inst_3 …

--- 原说明 ---
A simple function is McShane integrable w.r.t. any locally finite measure.
-/
theorem hasBoxIntegral (f : SimpleFunc (ι → ℝ) E) (μ : Measure (ι → ℝ)) [IsLocallyFiniteMeasure μ]
    (I : Box ι) (l : IntegrationParams) (hl : l.bRiemann = false) :
    HasIntegral.{u, v, v} I l f μ.toBoxAdditive.toSMul (f.integral (μ.restrict I)) := by
  induction f using MeasureTheory.SimpleFunc.induction with
  | @const y s hs =>
    simpa [hs] using! BoxIntegral.hasIntegralIndicatorConst l hl hs I y μ
  | @add f g _ hfi hgi =>
    borelize E; have := Fact.mk (I.measure_coe_lt_top μ)
    rw [integral_add]
    exacts [hfi.add hgi, integrable_iff.2 fun _ _ => measure_lt_top _ _,
      integrable_iff.2 fun _ _ => measure_lt_top _ _]

/-- For a simple function, its McShane (or Henstock, or `⊥`) box integral is equal to its
integral in the sense of `MeasureTheory.SimpleFunc.integral`. -/
/-
**MeasureTheory.SimpleFunc.box_integral_eq_integral** 是 Mathlib 中的一个定理，位于命名空间 `M
easureTheory.SimpleFunc`。
形式化陈述：box_integral_eq_integral (f : SimpleFunc (ι -> Real) E) (μ : Measure (ι ->
 Real)) [IsLocallyFiniteMeasure μ] (I : Box ι) (l : IntegrationParams) (hl : l.b
Riemann = false) : BoxIntegral.integral.{u, v, v} I l f μ.toBoxAdditive.toSMul =
 f.integral (μ.restrict I)
参数：f : SimpleFunc (ι -> Real) E；μ : Measure (ι -> Real)；I : Box ι；l : Integratio
nParams；hl : l.bRiemann = false。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `BoxIntegral.HasIntegral.integral_eq`：∀ {ι : Type u} {E : Type v} {F : Ty
pe w} [inst : NormedAddCommGroup E] [inst_1 : NormedSpace ℝ E]   [inst_2 : Norme
dAddCommGroup F] [inst_3 …
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `MeasureTheory.SimpleFunc.hasBoxIntegral`：hasBoxIntegral (f : SimpleFunc 
(ι -> Real) E) (μ : Measure (ι -> Real)) [IsLocallyFiniteMeasure μ] (I : Box ι) 
(l : IntegrationParams) (hl :…

--- 原说明 ---
For a simple function, its McShane (or Henstock, or `⊥`) box integral is equal t
o its
integral in the sense of `MeasureTheory.SimpleFunc.integral`.
-/
theorem box_integral_eq_integral (f : SimpleFunc (ι → ℝ) E) (μ : Measure (ι → ℝ))
    [IsLocallyFiniteMeasure μ] (I : Box ι) (l : IntegrationParams) (hl : l.bRiemann = false) :
    BoxIntegral.integral.{u, v, v} I l f μ.toBoxAdditive.toSMul = f.integral (μ.restrict I) :=
  (f.hasBoxIntegral μ I l hl).integral_eq

end SimpleFunc

open TopologicalSpace

set_option backward.defeqAttrib.useBackward true in
/-- If `f : ℝⁿ → E` is Bochner integrable w.r.t. a locally finite measure `μ` on a rectangular box
`I`, then it is McShane integrable on `I` with the same integral. -/
/-
**MeasureTheory.IntegrableOn.hasBoxIntegral** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTh
eory.IntegrableOn`。
形式化陈述：∀ {ι : Type u} {E : Type v} [inst : Fintype ι] [inst_1 : NormedAddCommGrou
p E] [inst_2 : NormedSpace ℝ E]   [CompleteSpace E] {f : (ι → ℝ) → E} {μ : Measu
reTheory.Measure (ι → ℝ)}   [inst_4 : MeasureTheory.IsLocallyFiniteMeasure μ] {I
 : BoxIntegral.Box ι},   MeasureTheory.IntegrableOn f (↑I) μ →     ∀ (l : BoxInt
egral.IntegrationParams),       l.bRiemann = false → BoxIntegral.HasIntegral I l
 f μ.toBoxAdditive.toSMul (∫ (x : ι → ℝ) in ↑I, f x ∂μ)
参数：ι → ℝ；ι → ℝ；↑I；l : BoxIntegral.IntegrationParams；∫ (x : ι → ℝ) in ↑I, f x ∂μ。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `MeasureTheory.Integrable.aestronglyMeasurable`：∀ {α : Type u_1} {ε : Typ
e u_5} {m : MeasurableSpace α} {μ : MeasureTheory.Measure α} [inst : Topological
Space ε]   [inst_1 : ContinuousENor…
· 使用定理 `MeasureTheory.StronglyMeasurable.separableSpace_range_union_singleton`：s
eparableSpace_range_union_singleton {_ : MeasurableSpace α} [TopologicalSpace β]
 [PseudoMetrizableSpace β] (hf : StronglyMeasurable f) {b :…
· 使用定理 `PseudoEMetricSpace.pseudoMetrizableSpace`：∀ {α : Type u_2} [inst : Pseud
oEMetricSpace α], TopologicalSpace.PseudoMetrizableSpace α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.integral_congr_ae`：integral_congr_ae {f g : α -> G} (h : f
 =ᵐ[μ] g) : ∫ a, f a ∂μ = ∫ a, g a ∂μ
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `MeasureTheory.integrable_congr`：integrable_congr {f g : α -> ε} (h : f =
ᵐ[μ] g) : Integrable f μ ↔ Integrable g μ
· 使用定理 `BoxIntegral.HasIntegral.congr_ae`：∀ {ι : Type u} {E : Type v} [inst : Fi
ntype ι] [inst_1 : NormedAddCommGroup E] [inst_2 : NormedSpace ℝ E]   {l : BoxIn
tegral.IntegrationPara…
· 使用定理 `BorelSpace.opensMeasurable`：∀ {α : Type u_6} [inst : TopologicalSpace α]
 [inst_1 : MeasurableSpace α] [BorelSpace α], OpensMeasurableSpace α
· 使用定理 `MeasureTheory.StronglyMeasurable.measurable`：∀ {α : Type u_1} {β : Type 
u_2} {f : α → β} {x : MeasurableSpace α} [inst : TopologicalSpace β]   [Topologi
calSpace.PseudoMetrizableSpace β]…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Set.union_singleton`：union_singleton : s union {a} = insert a s
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `true_or`：∀ (p : Prop), (True ∨ p) = True
· 使用定理 `MeasureTheory.SimpleFunc.integrable_approxOn_range`：integrable_approxOn_
range [BorelSpace E] {f : β -> E} {μ : Measure β} (fmeas : Measurable f) [Separa
bleSpace (range f union {0} : Set E)] (h…
· 使用定理 `BoxIntegral.HasIntegral.integrable`：∀ {ι : Type u} {E : Type v} {F : Typ
e w} [inst : NormedAddCommGroup E] [inst_1 : NormedSpace ℝ E]   [inst_2 : Normed
AddCommGroup F] [inst_3 …
· 使用定理 `MeasureTheory.SimpleFunc.hasBoxIntegral`：hasBoxIntegral (f : SimpleFunc 
(ι -> Real) E) (μ : Measure (ι -> Real)) [IsLocallyFiniteMeasure μ] (I : Box ι) 
(l : IntegrationParams) (hl :…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `dist_eq_norm`：∀ {E : Type u_5} [inst : SeminormedAddCommGroup E] (a b : 
E), dist a b = ‖a - b‖
· 使用定理 `dist_nndist`：dist_nndist (x y : α) : dist x y = nndist x y
· 使用定理 `NNReal.coe_le_coe`：∀ {r₁ r₂ : NNReal}, ↑r₁ ≤ ↑r₂ ↔ r₁ ≤ r₂
· 使用定理 `ENNReal.coe_le_coe`：∀ {r q : NNReal}, ↑r ≤ ↑q ↔ r ≤ q
· 使用定理 `edist_nndist`：edist_nndist (x y : α) : edist x y = nndist x y
· 使用定理 `MeasureTheory.SimpleFunc.edist_approxOn_mono`：edist_approxOn_mono {f : β
 -> α} (hf : Measurable f) {s : Set α} {y₀ : α} (h₀ : y₀ in s) [SeparableSpace s
] (x : β) {m n : Nat} (h : m <= n)…
· 使用定理 `BoxIntegral.HasIntegral.of_mul`：∀ {ι : Type u} {E : Type v} {F : Type w}
 [inst : NormedAddCommGroup E] [inst_1 : NormedSpace ℝ E]   [inst_2 : NormedAddC
ommGroup F] [inst_3 …
（共 118 条，此处仅展示前 30 条）

--- 原说明 ---
If `f : ℝⁿ → E` is Bochner integrable w.r.t. a locally finite measure `μ` on a r
ectangular box
`I`, then it is McShane integrable on `I` with the same integral.
-/
theorem IntegrableOn.hasBoxIntegral [CompleteSpace E] {f : (ι → ℝ) → E} {μ : Measure (ι → ℝ)}
    [IsLocallyFiniteMeasure μ] {I : Box ι} (hf : IntegrableOn f I μ) (l : IntegrationParams)
    (hl : l.bRiemann = false) :
    HasIntegral.{u, v, v} I l f μ.toBoxAdditive.toSMul (∫ x in I, f x ∂μ) := by
  borelize E
  -- First we replace an `ae_strongly_measurable` function by a measurable one.
  rcases hf.aestronglyMeasurable with ⟨g, hg, hfg⟩
  have : SeparableSpace (range g ∪ {0} : Set E) := hg.separableSpace_range_union_singleton
  rw [integral_congr_ae hfg]; have hgi : IntegrableOn g I μ := (integrable_congr hfg).1 hf
  refine BoxIntegral.HasIntegral.congr_ae ?_ hfg.symm hl
  clear! f
  /- Now consider the sequence of simple functions
    `SimpleFunc.approxOn g hg.measurable (range g ∪ {0}) 0 (by simp)`
    approximating `g`. Recall some properties of this sequence. -/
  set f : ℕ → SimpleFunc (ι → ℝ) E :=
    SimpleFunc.approxOn g hg.measurable (range g ∪ {0}) 0 (by simp)
  have hfi : ∀ n, IntegrableOn (f n) I μ :=
    SimpleFunc.integrable_approxOn_range hg.measurable hgi
  have hfi' := fun n => ((f n).hasBoxIntegral μ I l hl).integrable
  have hfg_mono : ∀ (x) {m n}, m ≤ n → ‖f n x - g x‖ ≤ ‖f m x - g x‖ := by
    intro x m n hmn
    rw [← dist_eq_norm, ← dist_eq_norm, dist_nndist, dist_nndist, NNReal.coe_le_coe, ←
      ENNReal.coe_le_coe, ← edist_nndist, ← edist_nndist]
    exact SimpleFunc.edist_approxOn_mono hg.measurable _ x hmn
  /- Now consider `ε > 0`. We need to find `r` such that for any tagged partition subordinate
    to `r`, the integral sum is `(μ I + 1 + 1) * ε`-close to the Bochner integral. -/
  refine HasIntegral.of_mul (μ.real I + 1 + 1) fun ε ε0 => ?_
  lift ε to ℝ≥0 using ε0.le; rw [NNReal.coe_pos] at ε0; have ε0' := ENNReal.coe_pos.2 ε0
  -- Choose `N` such that the integral of `‖f N x - g x‖` is less than or equal to `ε`.
  obtain ⟨N₀, hN₀⟩ : ∃ N : ℕ, ∫ x in I, ‖f N x - g x‖ ∂μ ≤ ε := by
    have : Tendsto (fun n => ∫⁻ x in I, ‖f n x - g x‖₊ ∂μ) atTop (𝓝 0) :=
      SimpleFunc.tendsto_approxOn_range_L1_enorm hg.measurable hgi
    refine (this.eventually (ge_mem_nhds ε0')).exists.imp fun N hN => ?_
    exact integral_coe_le_of_lintegral_coe_le hN
  -- For each `x`, we choose `Nx x ≥ N₀` such that `dist (f Nx x) (g x) ≤ ε`.
  have : ∀ x, ∃ N₁, N₀ ≤ N₁ ∧ dist (f N₁ x) (g x) ≤ ε := fun x ↦ by
    have : Tendsto (f · x) atTop (𝓝 <| g x) :=
      SimpleFunc.tendsto_approxOn hg.measurable _ (subset_closure (by simp))
    exact ((eventually_ge_atTop N₀).and <| this <| closedBall_mem_nhds _ ε0).exists
  choose Nx hNx hNxε using this
  -- We also choose a convergent series with `∑' i : ℕ, δ i < ε`.
  rcases NNReal.exists_pos_sum_of_countable ε0.ne' ℕ with ⟨δ, δ0, c, hδc, hcε⟩
  /- Since each simple function `fᵢ` is integrable, there exists `rᵢ : ℝⁿ → (0, ∞)` such that
    the integral sum of `f` over any tagged prepartition is `δᵢ`-close to the sum of integrals
    of `fᵢ` over the boxes of this prepartition. For each `x`, we choose `r (Nx x)` as the radius
    at `x`. -/
  set r : ℝ≥0 → (ι → ℝ) → Ioi (0 : ℝ) := fun c x => (hfi' <| Nx x).convergenceR (δ <| Nx x) c x
  refine ⟨r, fun c => l.rCond_of_bRiemann_eq_false hl, fun c π hπ hπp => ?_⟩
  /- Now we prove the estimate in 3 "jumps": first we replace `g x` in the formula for the
    integral sum by `f (Nx x)`; then we replace each `μ J • f (Nx (π.tag J)) (π.tag J)`
    by the Bochner integral of `f (Nx (π.tag J)) x` over `J`, then we jump to the Bochner
    integral of `g`. -/
  refine (dist_triangle4 _ (∑ J ∈ π.boxes, μ.real J • f (Nx <| π.tag J) (π.tag J))
    (∑ J ∈ π.boxes, ∫ x in J, f (Nx <| π.tag J) x ∂μ) _).trans ?_
  rw [add_mul, add_mul, one_mul]
  refine add_le_add_three ?_ ?_ ?_
  · /- Since each `f (Nx <| π.tag J)` is `ε`-close to `g (π.tag J)`, replacing the latter with
        the former in the formula for the integral sum changes the sum at most by `μ I * ε`. -/
    rw [← hπp.iUnion_eq, π.measure_iUnion_toReal, sum_mul, integralSum]
    refine dist_sum_sum_le_of_le _ fun J _ => ?_; dsimp
    rw [dist_eq_norm, ← smul_sub, norm_smul, Real.norm_eq_abs, abs_of_nonneg measureReal_nonneg]
    gcongr
    rw [← dist_eq_norm']; exact hNxε _
  · /- We group the terms of both sums by the values of `Nx (π.tag J)`.
        For each `N`, the sum of Bochner integrals over the boxes is equal
        to the sum of box integrals, and the sum of box integrals is `δᵢ`-close
        to the corresponding integral sum due to the Henstock-Sacks inequality. -/
    rw [← π.sum_fiberwise fun J => Nx (π.tag J), ← π.sum_fiberwise fun J => Nx (π.tag J)]
    grw [← hcε]
    refine
      (dist_sum_sum_le_of_le _ fun n hn => ?_).trans
        (sum_le_hasSum _ (fun n _ => (δ n).2) (NNReal.hasSum_coe.2 hδc))
    have hNxn : ∀ J ∈ π.filter fun J => Nx (π.tag J) = n, Nx (π.tag J) = n := fun J hJ =>
      (π.mem_filter.1 hJ).2
    have hrn : ∀ J ∈ π.filter fun J => Nx (π.tag J) = n,
        r c (π.tag J) = (hfi' n).convergenceR (δ n) c (π.tag J) := fun J hJ ↦ by
      obtain rfl := hNxn J hJ
      rfl
    have :
        l.MemBaseSet I c ((hfi' n).convergenceR (δ n) c) (π.filter fun J => Nx (π.tag J) = n) :=
      (hπ.filter _).mono' _ le_rfl le_rfl fun J hJ => (hrn J hJ).le
    convert! (hfi' n).dist_integralSum_sum_integral_le_of_memBaseSet (δ0 _) this using 2
    · refine sum_congr rfl fun J hJ => ?_
      simp [hNxn J hJ]
    · refine sum_congr rfl fun J hJ => ?_
      rw [← SimpleFunc.integral_eq_integral, SimpleFunc.box_integral_eq_integral _ _ _ _ hl,
        hNxn J hJ]
      exact (hfi _).mono_set (Prepartition.le_of_mem _ hJ)
  · /-  For the last jump, we use the fact that the distance between `f (Nx x) x` and `g x` is less
        than or equal to the distance between `f N₀ x` and `g x` and the integral of
        `‖f N₀ x - g x‖` is less than or equal to `ε`. -/
    refine le_trans ?_ hN₀
    have hfi : ∀ (n), ∀ J ∈ π, IntegrableOn (f n) (↑J) μ := fun n J hJ =>
      (hfi n).mono_set (π.le_of_mem' J hJ)
    have hgi : ∀ J ∈ π, IntegrableOn g (↑J) μ := fun J hJ => hgi.mono_set (π.le_of_mem' J hJ)
    have hfgi : ∀ (n), ∀ J ∈ π, IntegrableOn (fun x => ‖f n x - g x‖) J μ := fun n J hJ =>
      ((hfi n J hJ).sub (hgi J hJ)).norm
    rw [← hπp.iUnion_eq, Prepartition.iUnion_def',
      integral_biUnion_finset π.boxes (fun J _ => J.measurableSet_coe) π.pairwiseDisjoint hgi,
      integral_biUnion_finset π.boxes (fun J _ => J.measurableSet_coe) π.pairwiseDisjoint (hfgi _)]
    refine dist_sum_sum_le_of_le _ fun J hJ => ?_
    rw [dist_eq_norm, ← integral_sub (hfi _ J hJ) (hgi J hJ)]
    refine norm_integral_le_of_norm_le (hfgi _ J hJ) (Eventually.of_forall fun x => ?_)
    exact hfg_mono x (hNx (π.tag J))

/-- If `f : ℝⁿ → E` is continuous on a rectangular box `I`, then it is Box integrable on `I`
w.r.t. a locally finite measure `μ` with the same integral. -/
/-
**MeasureTheory.ContinuousOn.hasBoxIntegral** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTh
eory.ContinuousOn`。
形式化陈述：∀ {ι : Type u} {E : Type v} [inst : Fintype ι] [inst_1 : NormedAddCommGrou
p E] [inst_2 : NormedSpace ℝ E]   [CompleteSpace E] {f : (ι → ℝ) → E} (μ : Measu
reTheory.Measure (ι → ℝ))   [inst_4 : MeasureTheory.IsLocallyFiniteMeasure μ] {I
 : BoxIntegral.Box ι},   ContinuousOn f (BoxIntegral.Box.Icc I) →     ∀ (l : Box
Integral.IntegrationParams),       BoxIntegral.HasIntegral I l f μ.toBoxAdditive
.toSMul (∫ (x : ι → ℝ) in ↑I, f x ∂μ)
参数：ι → ℝ；μ : MeasureTheory.Measure (ι → ℝ)；BoxIntegral.Box.Icc I；l : BoxIntegral
.IntegrationParams；∫ (x : ι → ℝ) in ↑I, f x ∂μ。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `BoxIntegral.integrable_of_continuousOn`：integrable_of_continuousOn [Comp
leteSpace E] {I : Box ι} {f : Realⁿ -> E} (hc : ContinuousOn f (Box.Icc I)) (μ :
 Measure Realⁿ) [IsLocallyFi…
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.IntegrableOn.mono_set`：∀ {α : Type u_1} {ε : Type u_3} {mα
 : MeasurableSpace α} {f : α → ε} {s t : Set α} {μ : MeasureTheory.Measure α}   
[inst : TopologicalSpace …
· 使用定理 `ContinuousOn.integrableOn_compact`：ContinuousOn.integrableOn_compact [T2
Space X] (hK : IsCompact K) (hf : ContinuousOn f K) : IntegrableOn f K μ
· 使用定理 `Finite.to_countable`：∀ {α : Sort u} [Finite α], Countable α
· 使用定理 `instSecondCountableTopologyReal`：SecondCountableTopology ℝ
· 使用定理 `BorelSpace.opensMeasurable`：∀ {α : Type u_6} [inst : TopologicalSpace α]
 [inst_1 : MeasurableSpace α] [BorelSpace α], OpensMeasurableSpace α
· 使用定理 `MeasureTheory.Measure.Regular.toIsFiniteMeasureOnCompacts`：∀ {α : Type u
_1} {inst : MeasurableSpace α} {inst_1 : TopologicalSpace α} {μ : MeasureTheory.
Measure α}   [self : μ.Regular], MeasureTheory.…
· 使用定理 `MeasureTheory.Measure.Regular.of_sigmaCompactSpace_of_isLocallyFiniteMea
sure`：∀ {X : Type u_3} [inst : TopologicalSpace X] [TopologicalSpace.PseudoMetri
zableSpace X] [SigmaCompactSpace X]   [inst_3 : MeasurableSpace X]…
· 使用定理 `PseudoEMetricSpace.pseudoMetrizableSpace`：∀ {α : Type u_2} [inst : Pseud
oEMetricSpace α], TopologicalSpace.PseudoMetrizableSpace α
· 使用定理 `instSigmaCompactSpaceForallOfFinite`：∀ {ι : Type u_3} [Finite ι] {X : ι 
→ Type u_4} [inst : (i : ι) → TopologicalSpace (X i)]   [∀ (i : ι), SigmaCompact
Space (X i)], SigmaCompac…
· 使用定理 `SeparableWeaklyLocallyCompactAddGroup.sigmaCompactSpace`：∀ {G : Type w} 
[inst : TopologicalSpace G] [inst_1 : AddGroup G] [IsTopologicalAddGroup G]   [T
opologicalSpace.SeparableSpace G] [WeaklyLoca…
· 使用定理 `instIsTopologicalAddGroupReal`：IsTopologicalAddGroup ℝ
· 使用定理 `TopologicalSpace.SecondCountableTopology.to_separableSpace`：∀ {α : Type 
u} [t : TopologicalSpace α] [SecondCountableTopology α], TopologicalSpace.Separa
bleSpace α
· 使用定理 `instWeaklyLocallyCompactSpaceOfLocallyCompactSpace`：∀ {X : Type u_1} [in
st : TopologicalSpace X] [LocallyCompactSpace X], WeaklyLocallyCompactSpace X
· 使用定理 `locallyCompact_of_proper`：∀ {α : Type u} [inst : PseudoMetricSpace α] [P
roperSpace α], LocallyCompactSpace α
· 使用定理 `instProperSpaceReal`：ProperSpace ℝ
· 使用定理 `TopologicalSpace.t2Space_of_metrizableSpace`：∀ {X : Type u_2} [inst : To
pologicalSpace X] [TopologicalSpace.MetrizableSpace X], T2Space X
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α
· 使用定理 `BoxIntegral.Box.isCompact_Icc`：∀ {ι : Type u_1} (I : BoxIntegral.Box ι),
 IsCompact (BoxIntegral.Box.Icc I)
· 使用定理 `BoxIntegral.Box.coe_subset_Icc`：coe_subset_Icc : ↑I subseteq Box.Icc I
· 使用定理 `BoxIntegral.HasIntegral.unique`：∀ {ι : Type u} {E : Type v} {F : Type w}
 [inst : NormedAddCommGroup E] [inst_1 : NormedSpace ℝ E]   [inst_2 : NormedAddC
ommGroup F] [inst_3 …
· 使用定理 `MeasureTheory.IntegrableOn.hasBoxIntegral`：∀ {ι : Type u} {E : Type v} [
inst : Fintype ι] [inst_1 : NormedAddCommGroup E] [inst_2 : NormedSpace ℝ E]   [
CompleteSpace E] {f : (ι → ℝ) →…
· 使用定理 `BoxIntegral.HasIntegral.mono`：∀ {ι : Type u} {E : Type v} {F : Type w} [
inst : NormedAddCommGroup E] [inst_1 : NormedSpace ℝ E]   [inst_2 : NormedAddCom
mGroup F] [inst_3 …
· 使用定理 `bot_le`：∀ {α : Type u} [inst : LE α] [inst_1 : OrderBot α] {a : α}, ⊥ ≤ 
a

--- 原说明 ---
If `f : ℝⁿ → E` is continuous on a rectangular box `I`, then it is Box integrabl
e on `I`
w.r.t. a locally finite measure `μ` with the same integral.
-/
theorem ContinuousOn.hasBoxIntegral [CompleteSpace E] {f : (ι → ℝ) → E} (μ : Measure (ι → ℝ))
    [IsLocallyFiniteMeasure μ] {I : Box ι} (hc : ContinuousOn f (Box.Icc I))
    (l : IntegrationParams) :
    HasIntegral.{u, v, v} I l f μ.toBoxAdditive.toSMul (∫ x in I, f x ∂μ) := by
  obtain ⟨y, hy⟩ := BoxIntegral.integrable_of_continuousOn l hc μ
  convert! hy
  have : IntegrableOn f I μ :=
    IntegrableOn.mono_set (hc.integrableOn_compact I.isCompact_Icc) Box.coe_subset_Icc
  exact HasIntegral.unique (IntegrableOn.hasBoxIntegral this ⊥ rfl) (HasIntegral.mono hy bot_le)

/-- If `f : ℝⁿ → E` is a.e. continuous and bounded on a rectangular box `I`, then it is Box
integrable on `I` w.r.t. a locally finite measure `μ` with the same integral. -/
/-
**MeasureTheory.AEContinuous.hasBoxIntegral** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTh
eory.AEContinuous`。
形式化陈述：∀ {ι : Type u} {E : Type v} [inst : Fintype ι] [inst_1 : NormedAddCommGrou
p E] [inst_2 : NormedSpace ℝ E]   [CompleteSpace E] {f : (ι → ℝ) → E} (μ : Measu
reTheory.Measure (ι → ℝ))   [inst_4 : MeasureTheory.IsLocallyFiniteMeasure μ] {I
 : BoxIntegral.Box ι},   (∃ C, ∀ x ∈ BoxIntegral.Box.Icc I, ‖f x‖ ≤ C) →     (∀ᵐ
 (x : ι → ℝ) ∂μ, ContinuousAt f x) →       ∀ (l : BoxIntegral.IntegrationParams)
,         BoxIntegral.HasIntegral I l f μ.toBoxAdditive.toSMul (∫ (x : ι → ℝ) in
 ↑I, f x ∂μ)
参数：ι → ℝ；μ : MeasureTheory.Measure (ι → ℝ)；∃ C, ∀ x ∈ BoxIntegral.Box.Icc I, ‖f 
x‖ ≤ C；∀ᵐ (x : ι → ℝ) ∂μ, ContinuousAt f x；l : BoxIntegral.IntegrationParams；∫ (
x : ι → ℝ) in ↑I, f x ∂μ。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `BoxIntegral.integrable_of_bounded_and_ae_continuous`：integrable_of_bound
ed_and_ae_continuous [CompleteSpace E] {I : Box ι} {f : Realⁿ -> E} (hb : exists
 C : Real, forall x in Box.Icc I, ‖f x‖ <…
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `BoxIntegral.HasIntegral.unique`：∀ {ι : Type u} {E : Type v} {F : Type w}
 [inst : NormedAddCommGroup E] [inst_1 : NormedSpace ℝ E]   [inst_2 : NormedAddC
ommGroup F] [inst_3 …
· 使用定理 `MeasureTheory.IntegrableOn.hasBoxIntegral`：∀ {ι : Type u} {E : Type v} [
inst : Fintype ι] [inst_1 : NormedAddCommGroup E] [inst_2 : NormedSpace ℝ E]   [
CompleteSpace E] {f : (ι → ℝ) →…
· 使用定理 `ContinuousOn.aestronglyMeasurable`：ContinuousOn.aestronglyMeasurable [To
pologicalSpace α] [TopologicalSpace β] [h : SecondCountableTopologyEither α β] [
OpensMeasurableSpace α]…
· 使用定理 `secondCountableTopologyEither_of_left`：∀ (α : Type u_6) (β : Type u_7) [
inst : TopologicalSpace α] [inst_1 : TopologicalSpace β] [SecondCountableTopolog
y α],   SecondCountableTopo…
· 使用定理 `TopologicalSpace.instSecondCountableTopologyForallOfCountable`：∀ {ι : Ty
pe u_1} {X : ι → Type u_2} [Countable ι] [inst : (a : ι) → TopologicalSpace (X a
)]   [∀ (a : ι), SecondCountableTopology (X a)], Se…
· 使用定理 `Finite.to_countable`：∀ {α : Sort u} [Finite α], Countable α
· 使用定理 `instSecondCountableTopologyReal`：SecondCountableTopology ℝ
· 使用定理 `BorelSpace.opensMeasurable`：∀ {α : Type u_6} [inst : TopologicalSpace α]
 [inst_1 : MeasurableSpace α] [BorelSpace α], OpensMeasurableSpace α
· 使用定理 `PseudoEMetricSpace.pseudoMetrizableSpace`：∀ {α : Type u_2} [inst : Pseud
oEMetricSpace α], TopologicalSpace.PseudoMetrizableSpace α
· 使用定理 `continuousOn_of_forall_continuousAt`：continuousOn_of_forall_continuousAt
 (hcont : forall x in s, ContinuousAt f x) : ContinuousOn f s
· 使用定理 `measurableSet_of_continuousAt`：measurableSet_of_continuousAt {β} [Pseudo
EMetricSpace β] (f : α -> β) : MeasurableSet { x | ContinuousAt f x }
· 使用定理 `MeasureTheory.AEStronglyMeasurable.mono_measure`：mono_measure {ν : Measu
re α} (hf : AEStronglyMeasurable[m] f μ) (h : ν <= μ) : AEStronglyMeasurable[m] 
f ν
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `MeasureTheory.Measure.le_iff`：le_iff : μ₁ <= μ₂ ↔ forall s, MeasurableSe
t s -> μ₁ s <= μ₂ s
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.Measure.restrict_apply`：restrict_apply (ht : MeasurableSet
 t) : μ.restrict s t = μ (t inter s)
· 使用定理 `le_of_le_of_eq`：∀ {α : Type u_1} {a b c : α} [inst : LE α], a ≤ b → b = 
c → a ≤ c
· 使用定理 `MeasureTheory.OuterMeasure.mono`：∀ {α : Type u_2} (self : MeasureTheory.
OuterMeasure α) {s₁ s₂ : Set α}, s₁ ⊆ s₂ → self.measureOf s₁ ≤ self.measureOf s₂
· 使用定理 `Set.inter_subset_left`：inter_subset_left {s t : Set α} : s inter t subse
teq s
· 使用定理 `MeasureTheory.measure_eq_measure_of_null_sdiff`：measure_eq_measure_of_nu
ll_sdiff {s t : Set α} (hst : s subseteq t) (h_nullsdiff : μ (t \ s) = 0) : μ s 
= μ t
· 使用定理 `Set.sdiff_self_inter`：sdiff_self_inter {s t : Set α} : s \ (s inter t) =
 s \ t
· 使用定理 `Set.sdiff_eq`：sdiff_eq (s t : Set α) : s \ t = s inter tᶜ
· 使用定理 `nonpos_iff_eq_zero`：∀ {α : Type u_1} {a : α} [inst : PartialOrder α] [in
st_1 : Zero α] [IsBotZeroClass α], a ≤ 0 ↔ a = 0
（共 63 条，此处仅展示前 30 条）

--- 原说明 ---
If `f : ℝⁿ → E` is a.e. continuous and bounded on a rectangular box `I`, then it
 is Box
integrable on `I` w.r.t. a locally finite measure `μ` with the same integral.
-/
theorem AEContinuous.hasBoxIntegral [CompleteSpace E] {f : (ι → ℝ) → E} (μ : Measure (ι → ℝ))
    [IsLocallyFiniteMeasure μ] {I : Box ι} (hb : ∃ C : ℝ, ∀ x ∈ Box.Icc I, ‖f x‖ ≤ C)
    (hc : ∀ᵐ x ∂μ, ContinuousAt f x) (l : IntegrationParams) :
    HasIntegral.{u, v, v} I l f μ.toBoxAdditive.toSMul (∫ x in I, f x ∂μ) := by
  obtain ⟨y, hy⟩ := integrable_of_bounded_and_ae_continuous l hb μ hc
  convert! hy
  refine HasIntegral.unique (IntegrableOn.hasBoxIntegral ?_ ⊥ rfl) (HasIntegral.mono hy bot_le)
  constructor
  · let v := {x : (ι → ℝ) | ContinuousAt f x}
    have : AEStronglyMeasurable f (μ.restrict v) :=
      (continuousOn_of_forall_continuousAt fun _ h ↦ h).aestronglyMeasurable
      (measurableSet_of_continuousAt f)
    refine this.mono_measure (Measure.le_iff.2 fun s hs ↦ ?_)
    repeat rw [μ.restrict_apply hs]
    apply le_of_le_of_eq <| μ.mono s.inter_subset_left
    refine measure_eq_measure_of_null_sdiff s.inter_subset_left ?_ |>.symm
    rw [sdiff_self_inter, Set.sdiff_eq, ← nonpos_iff_eq_zero]
    grw [s.inter_subset_right]
    exact hc.le
  · have : IsFiniteMeasure (μ.restrict (Box.Icc I)) :=
      { measure_univ_lt_top := by simp [I.isCompact_Icc.measure_lt_top (μ := μ)] }
    have : IsFiniteMeasure (μ.restrict I) :=
      isFiniteMeasure_of_le _ (μ.restrict_mono Box.coe_subset_Icc le_rfl)
    obtain ⟨C, hC⟩ := hb
    refine .of_bounded (C := C) (Filter.eventually_iff_exists_mem.2 ?_)
    use I, self_mem_ae_restrict I.measurableSet_coe, fun y hy ↦ hC y (I.coe_subset_Icc hy)

end MeasureTheory

