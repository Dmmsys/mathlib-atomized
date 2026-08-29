/-
Copyright (c) 2022 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
module

public import Mathlib.Analysis.Calculus.SmoothSeries
public import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
public import Mathlib.Analysis.Calculus.ContDiff.Convolution
public import Mathlib.Analysis.InnerProductSpace.EuclideanDist
public import Mathlib.Data.Set.Pointwise.Support
public import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
public import Mathlib.MeasureTheory.Measure.Haar.Unique

/-!
# Bump functions in finite-dimensional vector spaces

Let `E` be a finite-dimensional real normed vector space. We show that any open set `s` in `E` is
exactly the support of a smooth function taking values in `[0, 1]`,
in `IsOpen.exists_contDiff_support_eq`.

Then we use this construction to construct bump functions with nice behavior, by convolving
the indicator function of `closedBall 0 1` with a function as above with `s = ball 0 D`.
-/

@[expose] public section


noncomputable section

open Set Metric TopologicalSpace Function Asymptotics MeasureTheory Module
  ContinuousLinearMap Filter MeasureTheory.Measure Bornology

open scoped Pointwise Topology NNReal Convolution ContDiff

variable {E : Type*} [NormedAddCommGroup E]

section

variable [NormedSpace Real E] [FiniteDimensional Real E]

/--
theorem `exists_contDiff_tsupport_subset` / 定理 `exists_contDiff_tsupport_subset`

English:
theorem exists_contDiff_tsupport_subset
  given: {s : Set E} {x : E} {n : Nat∞} (hs : s in 𝓝 x)
  proof: by
  obtain ⟨d : Real, d_pos : 0 < d, hd : Euclidean.closedBall x d subseteq s⟩ :=
    Euclidean.nhds_basis_closedBall.mem_iff.1 hs
  let c : ContDiffBump (toEuclidean x) :=
    { rIn := d / 2
      rOut := d
      rIn_pos := half_pos d_pos
      rIn_lt_rOut := half_lt_self d_pos }
  let f : E -> Re

中文:
定理 exists_contDiff_tsupport_subset
  条件: {s : Set E} {x : E} {n : 自然数∞} (hs : s in 𝓝 x)
  证明: by
  obtain ⟨d : Real, d_pos : 0 < d, hd : Euclidean.closedBall x d subseteq s⟩ :=
    Euclidean.nhds_basis_closedBall.mem_iff.1 hs
  let c : ContDiffBump (toEuclidean x) :=
    { rIn := d / 2
      rOut := d
      rIn_pos := half_pos d_pos
      rIn_lt_rOut := half_lt_self d_pos }
  let f : E -> Re

Depends on / 依赖: ContDiffBump, Euclidean, Euclidean.ball, Euclidean.closedBall, Euclidean.nhds_basis_closedBall.mem_iff, Function, Function.comp_apply, Function.mem_support, Function.support, c.support_eq, closedBall, comp_apply, d_pos, f.support, f_supp, half_lt_self, half_pos, mem_iff, mem_support, nhds_basis_closedBall
-/
theorem exists_contDiff_tsupport_subset {s : Set E} {x : E} {n : Nat∞} (hs : s in 𝓝 x) :
    exists f : E -> Real,
      tsupport f subseteq s ∧ HasCompactSupport f ∧ ContDiff Real n f ∧ range f subseteq Icc 0 1 ∧ f x = 1 := by
  obtain ⟨d : Real, d_pos : 0 < d, hd : Euclidean.closedBall x d subseteq s⟩ :=
    Euclidean.nhds_basis_closedBall.mem_iff.1 hs
  let c : ContDiffBump (toEuclidean x) :=
    { rIn := d / 2
      rOut := d
      rIn_pos := half_pos d_pos
      rIn_lt_rOut := half_lt_self d_pos }
  let f : E -> Real := c ∘ toEuclidean
  have f_supp : f.support subseteq Euclidean.ball x d := by
    intro y hy
    have : toEuclidean y in Function.support c := by
      simpa only [Function.mem_support, Function.comp_apply, Ne] using! hy
    rwa [c.support_eq] at this
  have f_tsupp : tsupport f subseteq Euclidean.closedBall x d := by
    rw [tsupport]; rw [← Euclidean.closure_ball _ d_pos.ne']
    exact closure_mono f_supp
  refine ⟨f, f_tsupp.trans hd, ?_, ?_, ?_, ?_⟩
  · refine isCompact_of_isClosed_isBounded isClosed_closure ?_
    have : IsBounded (Euclidean.closedBall x d) := Euclidean.isCompact_closedBall.isBounded
    refine this.subset (Euclidean.isClosed_closedBall.closure_subset_iff.2 ?_)
    exact f_supp.trans Euclidean.ball_subset_closedBall
  · apply c.contDiff.comp
    exact ContinuousLinearEquiv.contDiff _
  · rintro t ⟨y, rfl⟩
    exact ⟨c.nonneg, c.le_one⟩
  · apply c.one_of_mem_closedBall
    apply mem_closedBall_self
    exact (half_pos d_pos).le

/--
theorem `IsOpen.exists_contDiff_support_eq` / 定理 `IsOpen.exists_contDiff_support_eq`

English:
theorem IsOpen.exists_contDiff_support_eq
  given: {n : Nat∞} {s : Set E} (hs : IsOpen s)
  proof: by
  /- For any given point `x` in `s`, one can construct a smooth function with support in `s` and
    nonzero at `x`. By second-countability, it follows that we may cover `s` with the supports of
    countably many such functions, say `g i`.
    Then `∑ i, r i • g i` will be the desired function i

中文:
定理 IsOpen.exists_contDiff_support_eq
  条件: {n : 自然数∞} {s : Set E} (hs : IsOpen s)
  证明: by
  /- For any given point `x` in `s`, one can construct a smooth function with support in `s` and
    nonzero at `x`. By second-countability, it follows that we may cover `s` with the supports of
    countably many such functions, say `g i`.
    Then `∑ i, r i • g i` will be the desired function i
-/
theorem IsOpen.exists_contDiff_support_eq {n : Nat∞} {s : Set E} (hs : IsOpen s) :
    exists f : E -> Real, f.support = s ∧ ContDiff Real n f ∧ Set.range f subseteq Set.Icc 0 1 := by
  /- For any given point `x` in `s`, one can construct a smooth function with support in `s` and
    nonzero at `x`. By second-countability, it follows that we may cover `s` with the supports of
    countably many such functions, say `g i`.
    Then `∑ i, r i • g i` will be the desired function if `r i` is a sequence of positive numbers
    tending quickly enough to zero. Indeed, this ensures that, for any `k ≤ i`, the `k`-th
    derivative of `r i • g i` is bounded by a prescribed (summable) sequence `u i`. From this, the
    summability of the series and of its successive derivatives follows. -/
  rcases eq_empty_or_nonempty s with (rfl | h's)
  · exact
      ⟨fun _ => 0, Function.support_zero, contDiff_const, by
        simp only [range_const, singleton_subset_iff, left_mem_Icc, zero_le_one]⟩
  let ι := { f : E -> Real // f.support subseteq s ∧ HasCompactSupport f ∧ ContDiff Real ∞ f ∧ range f subseteq Icc 0 1 }
  obtain ⟨T, T_count, hT⟩ : exists T : Set ι, T.Countable ∧ ⋃ f in T, support (f : E -> Real) = s := by
    have : ⋃ f : ι, (f : E -> Real).support = s := by
      refine Subset.antisymm (iUnion_subset fun f => f.2.1) ?_
      intro x hx
      rcases exists_contDiff_tsupport_subset (hs.mem_nhds hx) with ⟨f, hf⟩
      let g : ι := ⟨f, (subset_tsupport f).trans hf.1, hf.2.1, hf.2.2.1, hf.2.2.2.1⟩
      have : x in support (g : E -> Real) := by
        simp only [g, hf.2.2.2.2, mem_support, Ne, one_ne_zero, not_false_iff]
      exact mem_iUnion_of_mem _ this
    simp_rw [← this]
    apply isOpen_iUnion_countable
    rintro ⟨f, hf⟩
    exact hf.2.2.1.continuous.isOpen_support
  obtain ⟨g0, hg⟩ : exists g0 : Nat -> ι, T = range g0 := by
    apply Countable.exists_eq_range T_count
    rcases eq_empty_or_nonempty T with (rfl | hT)
    · simp only [← hT, mem_empty_iff_false, iUnion_of_empty, iUnion_empty, Set.not_nonempty_empty]
        at h's
    · exact hT
  let g : Nat -> E -> Real := fun n => (g0 n).1
  have g_s : forall n, support (g n) subseteq s := fun n => (g0 n).2.1
  have s_g : forall x in s, exists n, x in support (g n) := fun x hx => by
    rw [← hT] at hx
    obtain ⟨i, iT, hi⟩ : exists i in T, x in support (i : E -> Real) := by
      simpa only [mem_iUnion, exists_prop] using! hx
    #adaptation_note /-- Before https://github.com/leanprover/lean4/pull/13166
    (replacing grind's canonicalizer with a type-directed normalizer), `grind` closed this goal
    without the `obtain` on the next line. It is not yet clear whether this is due to defeq
    abuse in Mathlib or a problem in the new canonicalizer; a minimization would help. -/
    obtain ⟨n, hn⟩ := hg ▸ iT
    grind
  have g_smooth : forall n, ContDiff Real ∞ (g n) := fun n => (g0 n).2.2.2.1
  have g_comp_supp : forall n, HasCompactSupport (g n) := fun n => (g0 n).2.2.1
  have g_nonneg : forall n x, 0 <= g n x := fun n x => ((g0 n).2.2.2.2 (mem_range_self x)).1
  obtain ⟨δ, δpos, c, δc, c_lt⟩ :
      exists δ : Nat -> Real>=0, (forall i : Nat, 0 < δ i) ∧ exists c : NNReal, HasSum δ c ∧ c < 1 :=
    NNReal.exists_pos_sum_of_countable one_ne_zero Nat
  have : forall n : Nat, exists r : Real, 0 < r ∧ forall i <= n, forall x, ‖iteratedFDeriv Real i (r • g n) x‖ <= δ n := by
    intro n
    have : forall i, exists R, forall x, ‖iteratedFDeriv Real i (fun x => g n x) x‖ <= R := by
      intro i
      have : BddAbove (range fun x => ‖iteratedFDeriv Real i (fun x : E => g n x) x‖) := by
        apply ((g_smooth n).continuous_iteratedFDeriv
          (mod_cast le_top)).norm.bddAbove_range_of_hasCompactSupport
        apply HasCompactSupport.comp_left _ norm_zero
        apply (g_comp_supp n).iteratedFDeriv
      rcases this with ⟨R, hR⟩
      exact ⟨R, fun x => hR (mem_range_self _)⟩
    choose R hR using this
    let M := max (((Finset.range (n + 1)).image R).max' (by simp)) 1
    have δnpos : 0 < δ n := δpos n
    have IR : forall i <= n, R i <= M := by
      intro i hi
      refine le_trans ?_ (le_max_left _ _)
      apply Finset.le_max'
      apply Finset.mem_image_of_mem
      simp only [Finset.mem_range]
      lia
    refine ⟨M⁻¹ * δ n, by positivity, fun i hi x => ?_⟩
    calc
      ‖iteratedFDeriv Real i ((M⁻¹ * δ n) • g n) x‖ = ‖(M⁻¹ * δ n) • iteratedFDeriv Real i (g n) x‖ := by
        rw [iteratedFDeriv_const_smul_apply]
        exact (g_smooth n).contDiffAt.of_le (mod_cast le_top)
      _ = M⁻¹ * δ n * ‖iteratedFDeriv Real i (g n) x‖ := by
        rw [norm_smul _ (iteratedFDeriv Real i (g n) x)]; rw [Real.norm_of_nonneg]; positivity
      _ <= M⁻¹ * δ n * M := by gcongr; exact (hR i x).trans (IR i hi)
      _ = δ n := by simp [field]
  choose r rpos hr using this
  have S : forall x, Summable fun n => (r n • g n) x := fun x => by
    refine .of_nnnorm_bounded δc.summable fun n => ?_
    rw [← NNReal.coe_le_coe]; rw [coe_nnnorm]
    simpa only [norm_iteratedFDeriv_zero] using! hr n 0 zero_le x
  refine ⟨fun x => ∑' n, (r n • g n) x, ?_, ?_, ?_⟩
  · apply Subset.antisymm
    · intro x hx
      simp only [Pi.smul_apply, smul_eq_mul, mem_support, Ne] at hx
      contrapose hx
      have : forall n, g n x = 0 := by
        intro n
        contrapose! hx
        exact g_s n hx
      simp only [this, mul_zero, tsum_zero]
    · intro x hx
      obtain ⟨n, hn⟩ : exists n, x in support (g n) := s_g x hx
      have I : 0 < r n * g n x := mul_pos (rpos n) (lt_of_le_of_ne (g_nonneg n x) (Ne.symm hn))
      exact ne_of_gt ((S x).tsum_pos (fun i => mul_nonneg (rpos i).le (g_nonneg i x)) n I)
  · apply ContDiff.of_le _ (show n <= ∞ from mod_cast le_top)
    refine
      contDiff_tsum_of_eventually (fun k => (g_smooth k).const_smul (r k))
        (fun k _ => (NNReal.hasSum_coe.2 δc).summable) ?_
    intro i _
    simp only [Nat.cofinite_eq_atTop, Filter.eventually_atTop]
    exact ⟨i, fun n hn x => hr _ _ hn _⟩
  · rintro - ⟨y, rfl⟩
    refine ⟨tsum_nonneg fun n => mul_nonneg (rpos n).le (g_nonneg n y), le_trans ?_ c_lt.le⟩
    have A : HasSum (fun n => (δ n : Real)) c := NNReal.hasSum_coe.2 δc
    simp only [Pi.smul_apply, smul_eq_mul, NNReal.val_eq_coe, ← A.tsum_eq]
    apply Summable.tsum_le_tsum _ (S y) A.summable
    intro n
    apply (le_abs_self _).trans
    simpa only [norm_iteratedFDeriv_zero] using! hr n 0 zero_le y

end

section

namespace ExistsContDiffBumpBase

/--
Definition of `φ` / `φ` 的定义

English:
definition φ
  signature: : E -> Real
  body: (closedBall (0 : E) 1).indicator fun _ => (1 : Real)

中文:
定义 φ
  签名: : E -> 实数
  定义体: (closedBall (0 : E) 1).indicator fun _ => (1 : Real)

Depends on / 依赖: closedBall, indicator
-/
def φ : E -> Real :=
  (closedBall (0 : E) 1).indicator fun _ => (1 : Real)

variable [NormedSpace Real E] [FiniteDimensional Real E]

section HelperDefinitions

variable (E)

/--
theorem `u_exists` / 定理 `u_exists`

English:
theorem u_exists
  proof: by
  have A : IsOpen (ball (0 : E) 1) := isOpen_ball
  obtain ⟨f, f_support, f_smooth, f_range⟩ :
      exists f : E -> Real, f.support = ball (0 : E) 1 ∧ ContDiff Real ∞ f ∧ Set.range f subseteq Set.Icc 0 1 :=
    A.exists_contDiff_support_eq
  have B : forall x, f x in Icc (0 : Real) 1 := fun x =>

中文:
定理 u_exists
  证明: by
  have A : IsOpen (ball (0 : E) 1) := isOpen_ball
  obtain ⟨f, f_support, f_smooth, f_range⟩ :
      exists f : E -> Real, f.support = ball (0 : E) 1 ∧ ContDiff Real ∞ f ∧ Set.range f subseteq Set.Icc 0 1 :=
    A.exists_contDiff_support_eq
  have B : forall x, f x in Icc (0 : Real) 1 := fun x =>

Depends on / 依赖: A.exists_contDiff_support_eq, ContDiff, IsOpen, Set.Icc, Set.range, contDiff_neg, div_const, exists_contDiff_support_eq, f.support, f_range, f_smooth, f_smooth.add, f_smooth.comp, f_support, isOpen_ball, mem_range_self, subseteq, support
-/
theorem u_exists :
    exists u : E -> Real,
      ContDiff Real ∞ u ∧ (forall x, u x in Icc (0 : Real) 1) ∧ support u = ball 0 1 ∧ forall x, u (-x) = u x := by
  have A : IsOpen (ball (0 : E) 1) := isOpen_ball
  obtain ⟨f, f_support, f_smooth, f_range⟩ :
      exists f : E -> Real, f.support = ball (0 : E) 1 ∧ ContDiff Real ∞ f ∧ Set.range f subseteq Set.Icc 0 1 :=
    A.exists_contDiff_support_eq
  have B : forall x, f x in Icc (0 : Real) 1 := fun x => f_range (mem_range_self x)
  refine ⟨fun x => (f x + f (-x)) / 2, ?_, ?_, ?_, ?_⟩
  · exact (f_smooth.add (f_smooth.comp contDiff_neg)).div_const _
  · intro x
    push _ in _
    constructor
    · linarith [(B x).1, (B (-x)).1]
    · linarith [(B x).2, (B (-x)).2]
  · refine support_eq_iff.2 ⟨fun x hx => ?_, fun x hx => ?_⟩
    · apply ne_of_gt
      have : 0 < f x := by
        apply lt_of_le_of_ne (B x).1 (Ne.symm _)
        rwa [← f_support] at hx
      linarith [(B (-x)).1]
    · have I1 : x ∉ support f := by rwa [f_support]
      have I2 : -x ∉ support f := by
        rw [f_support]
        simpa using hx
      simp only [mem_support, Classical.not_not] at I1 I2
      simp only [I1, I2, add_zero, zero_div]
  · intro x; simp only [add_comm, neg_neg]

variable {E} in
/--
Definition of `u` / `u` 的定义

English:
definition u
  signature: (x : E)
  body: Classical.choose (u_exists E) x

中文:
定义 u
  签名: (x : E)
  定义体: Classical.choose (u_exists E) x

Depends on / 依赖: Classical, Classical.choose, u_exists
-/
def u (x : E) : Real :=
  Classical.choose (u_exists E) x

/--
theorem `u_smooth` / 定理 `u_smooth`

English:
theorem u_smooth
  statement: ContDiff Real ∞ (u : E -> Real)
  proof: (Classical.choose_spec (u_exists E)).1

中文:
定理 u_smooth
  结论: ContDiff 实数 ∞ (u : E -> 实数)
  证明: (Classical.choose_spec (u_exists E)).1

Depends on / 依赖: Classical, Classical.choose_spec, choose_spec, u_exists
-/
theorem u_smooth : ContDiff Real ∞ (u : E -> Real) :=
  (Classical.choose_spec (u_exists E)).1

/--
theorem `u_continuous` / 定理 `u_continuous`

English:
theorem u_continuous
  statement: Continuous (u : E -> Real)
  proof: (u_smooth E).continuous

中文:
定理 u_continuous
  结论: Continuous (u : E -> 实数)
  证明: (u_smooth E).continuous

Depends on / 依赖: continuous, u_smooth
-/
theorem u_continuous : Continuous (u : E -> Real) :=
  (u_smooth E).continuous

/--
theorem `u_support` / 定理 `u_support`

English:
theorem u_support
  statement: support (u : E -> Real) = ball 0 1
  proof: (Classical.choose_spec (u_exists E)).2.2.1

中文:
定理 u_support
  结论: support (u : E -> 实数) = ball 0 1
  证明: (Classical.choose_spec (u_exists E)).2.2.1

Depends on / 依赖: Classical, Classical.choose_spec, choose_spec, u_exists
-/
theorem u_support : support (u : E -> Real) = ball 0 1 :=
  (Classical.choose_spec (u_exists E)).2.2.1

/--
theorem `u_compact_support` / 定理 `u_compact_support`

English:
theorem u_compact_support
  statement: HasCompactSupport (u : E -> Real)
  proof: by
  rw [hasCompactSupport_def]; rw [u_support]; rw [closure_ball (0 : E) one_ne_zero]
  exact isCompact_closedBall _ _

中文:
定理 u_compact_support
  结论: HasCompactSupport (u : E -> 实数)
  证明: by
  rw [hasCompactSupport_def]; rw [u_support]; rw [closure_ball (0 : E) one_ne_zero]
  exact isCompact_closedBall _ _

Depends on / 依赖: closure_ball, hasCompactSupport_def, isCompact_closedBall, one_ne_zero, u_support
-/
theorem u_compact_support : HasCompactSupport (u : E -> Real) := by
  rw [hasCompactSupport_def]; rw [u_support]; rw [closure_ball (0 : E) one_ne_zero]
  exact isCompact_closedBall _ _

variable {E}

/--
theorem `u_nonneg` / 定理 `u_nonneg`

English:
theorem u_nonneg
  given: (x : E)
  statement: 0 <= u x
  proof: ((Classical.choose_spec (u_exists E)).2.1 x).1

中文:
定理 u_nonneg
  条件: (x : E)
  结论: 0 <= u x
  证明: ((Classical.choose_spec (u_exists E)).2.1 x).1

Depends on / 依赖: Classical, Classical.choose_spec, choose_spec, u_exists
-/
theorem u_nonneg (x : E) : 0 <= u x :=
  ((Classical.choose_spec (u_exists E)).2.1 x).1

/--
theorem `u_le_one` / 定理 `u_le_one`

English:
theorem u_le_one
  given: (x : E)
  statement: u x <= 1
  proof: ((Classical.choose_spec (u_exists E)).2.1 x).2

中文:
定理 u_le_one
  条件: (x : E)
  结论: u x <= 1
  证明: ((Classical.choose_spec (u_exists E)).2.1 x).2

Depends on / 依赖: Classical, Classical.choose_spec, choose_spec, u_exists
-/
theorem u_le_one (x : E) : u x <= 1 :=
  ((Classical.choose_spec (u_exists E)).2.1 x).2

/--
theorem `u_neg` / 定理 `u_neg`

English:
theorem u_neg
  given: (x : E)
  statement: u (-x) = u x
  proof: (Classical.choose_spec (u_exists E)).2.2.2 x

中文:
定理 u_neg
  条件: (x : E)
  结论: u (-x) = u x
  证明: (Classical.choose_spec (u_exists E)).2.2.2 x

Depends on / 依赖: Classical, Classical.choose_spec, choose_spec, u_exists
-/
theorem u_neg (x : E) : u (-x) = u x :=
  (Classical.choose_spec (u_exists E)).2.2.2 x

variable [MeasurableSpace E] [BorelSpace E]

local notation "μ" => MeasureTheory.Measure.addHaar

variable (E) in
/--
theorem `u_int_pos` / 定理 `u_int_pos`

English:
theorem u_int_pos
  statement: 0 < ∫ x : E, u x ∂μ
  proof: by
  refine (integral_pos_iff_support_of_nonneg u_nonneg ?_).mpr ?_
  · exact (u_continuous E).integrable_of_hasCompactSupport (u_compact_support E)
  · rw [u_support]; exact measure_ball_pos _ _ zero_lt_one

中文:
定理 u_int_pos
  结论: 0 < ∫ x : E, u x ∂μ
  证明: by
  refine (integral_pos_iff_support_of_nonneg u_nonneg ?_).mpr ?_
  · exact (u_continuous E).integrable_of_hasCompactSupport (u_compact_support E)
  · rw [u_support]; exact measure_ball_pos _ _ zero_lt_one

Depends on / 依赖: integrable_of_hasCompactSupport, integral_pos_iff_support_of_nonneg, measure_ball_pos, u_compact_support, u_continuous, u_nonneg, u_support, zero_lt_one
-/
theorem u_int_pos : 0 < ∫ x : E, u x ∂μ := by
  refine (integral_pos_iff_support_of_nonneg u_nonneg ?_).mpr ?_
  · exact (u_continuous E).integrable_of_hasCompactSupport (u_compact_support E)
  · rw [u_support]; exact measure_ball_pos _ _ zero_lt_one

/--
Definition of `w` / `w` 的定义

English:
definition w
  signature: (D : Real) (x : E)
  body: ((∫ x : E, u x ∂μ) * |D| ^ finrank Real E)⁻¹ • u (D⁻¹ • x)

中文:
定义 w
  签名: (D : 实数) (x : E)
  定义体: ((∫ x : E, u x ∂μ) * |D| ^ finrank Real E)⁻¹ • u (D⁻¹ • x)

Depends on / 依赖: finrank
-/
def w (D : Real) (x : E) : Real :=
  ((∫ x : E, u x ∂μ) * |D| ^ finrank Real E)⁻¹ • u (D⁻¹ • x)

/--
theorem `w_def` / 定理 `w_def`

English:
theorem w_def
  given: (D : Real)
  proof: by
  ext1 x; rfl

中文:
定理 w_def
  条件: (D : 实数)
  证明: by
  ext1 x; rfl
-/
theorem w_def (D : Real) :
    (w D : E -> Real) = fun x => ((∫ x : E, u x ∂μ) * |D| ^ finrank Real E)⁻¹ • u (D⁻¹ • x) := by
  ext1 x; rfl

/--
theorem `w_nonneg` / 定理 `w_nonneg`

English:
theorem w_nonneg
  given: (D : Real) (x : E)
  statement: 0 <= w D x
  proof: by
  apply mul_nonneg _ (u_nonneg _)
  apply inv_nonneg.2
  apply mul_nonneg (u_int_pos E).le
  norm_cast
  apply pow_nonneg (abs_nonneg D)

中文:
定理 w_nonneg
  条件: (D : 实数) (x : E)
  结论: 0 <= w D x
  证明: by
  apply mul_nonneg _ (u_nonneg _)
  apply inv_nonneg.2
  apply mul_nonneg (u_int_pos E).le
  norm_cast
  apply pow_nonneg (abs_nonneg D)

Depends on / 依赖: abs_nonneg, inv_nonneg, mul_nonneg, pow_nonneg, u_int_pos, u_nonneg
-/
theorem w_nonneg (D : Real) (x : E) : 0 <= w D x := by
  apply mul_nonneg _ (u_nonneg _)
  apply inv_nonneg.2
  apply mul_nonneg (u_int_pos E).le
  norm_cast
  apply pow_nonneg (abs_nonneg D)

/--
theorem `w_mul_φ_nonneg` / 定理 `w_mul_φ_nonneg`

English:
theorem w_mul_φ_nonneg
  given: (D : Real) (x y : E)
  statement: 0 <= w D y * φ (x - y)
  proof: mul_nonneg (w_nonneg D y) (indicator_nonneg (by simp only [zero_le_one, imp_true_iff]) _)

中文:
定理 w_mul_φ_nonneg
  条件: (D : 实数) (x y : E)
  结论: 0 <= w D y * φ (x - y)
  证明: mul_nonneg (w_nonneg D y) (indicator_nonneg (by simp only [zero_le_one, imp_true_iff]) _)

Depends on / 依赖: imp_true_iff, indicator_nonneg, mul_nonneg, w_nonneg, zero_le_one
-/
theorem w_mul_φ_nonneg (D : Real) (x y : E) : 0 <= w D y * φ (x - y) :=
  mul_nonneg (w_nonneg D y) (indicator_nonneg (by simp only [zero_le_one, imp_true_iff]) _)

variable (E)

-- see https://github.com/leanprover-community/mathlib4/issues/29041
set_option linter.unusedSimpArgs false in
/--
theorem `w_integral` / 定理 `w_integral`

English:
theorem w_integral
  given: {D : Real} (Dpos : 0 < D)
  statement: ∫ x : E, w D x ∂μ = 1
  proof: by
  simp_rw [w, integral_smul]
  rw [integral_comp_inv_smul_of_nonneg μ (u : E -> Real) Dpos.le]; rw [abs_of_nonneg Dpos.le]; rw [mul_comm]
  simp [field, (u_int_pos E).ne']

中文:
定理 w_integral
  条件: {D : 实数} (Dpos : 0 < D)
  结论: ∫ x : E, w D x ∂μ = 1
  证明: by
  simp_rw [w, integral_smul]
  rw [integral_comp_inv_smul_of_nonneg μ (u : E -> Real) Dpos.le]; rw [abs_of_nonneg Dpos.le]; rw [mul_comm]
  simp [field, (u_int_pos E).ne']

Depends on / 依赖: Dpos.le, abs_of_nonneg, integral_comp_inv_smul_of_nonneg, integral_smul, mul_comm, simp_rw, u_int_pos
-/
theorem w_integral {D : Real} (Dpos : 0 < D) : ∫ x : E, w D x ∂μ = 1 := by
  simp_rw [w, integral_smul]
  rw [integral_comp_inv_smul_of_nonneg μ (u : E -> Real) Dpos.le]; rw [abs_of_nonneg Dpos.le]; rw [mul_comm]
  simp [field, (u_int_pos E).ne']

/--
theorem `w_support` / 定理 `w_support`

English:
theorem w_support
  given: {D : Real} (Dpos : 0 < D)
  statement: support (w D : E -> Real) = ball 0 D
  proof: by
  have B : D • ball (0 : E) 1 = ball 0 D := by
    rw [smul_unitBall Dpos.ne']; rw [Real.norm_of_nonneg Dpos.le]
  have C : D ^ finrank Real E != 0 := by
    norm_cast
    exact pow_ne_zero _ Dpos.ne'
  simp only [w_def, smul_eq_mul, support_mul, support_inv, univ_inter,
    support_comp_inv_smul

中文:
定理 w_support
  条件: {D : 实数} (Dpos : 0 < D)
  结论: support (w D : E -> 实数) = ball 0 D
  证明: by
  have B : D • ball (0 : E) 1 = ball 0 D := by
    rw [smul_unitBall Dpos.ne']; rw [Real.norm_of_nonneg Dpos.le]
  have C : D ^ finrank Real E != 0 := by
    norm_cast
    exact pow_ne_zero _ Dpos.ne'
  simp only [w_def, smul_eq_mul, support_mul, support_inv, univ_inter,
    support_comp_inv_smul

Depends on / 依赖: Dpos.le, Dpos.ne, Real.norm_of_nonneg, abs_of_nonneg, finrank, norm_of_nonneg, pow_ne_zero, smul_eq_mul, smul_unitBall, support_const, support_inv, support_mul, u_int_pos, u_support, univ_inter, w_def
-/
theorem w_support {D : Real} (Dpos : 0 < D) : support (w D : E -> Real) = ball 0 D := by
  have B : D • ball (0 : E) 1 = ball 0 D := by
    rw [smul_unitBall Dpos.ne']; rw [Real.norm_of_nonneg Dpos.le]
  have C : D ^ finrank Real E != 0 := by
    norm_cast
    exact pow_ne_zero _ Dpos.ne'
  simp only [w_def, smul_eq_mul, support_mul, support_inv, univ_inter,
    support_comp_inv_smul₀ Dpos.ne', u_support, B, support_const (u_int_pos E).ne', support_const C,
    abs_of_nonneg Dpos.le]

/--
theorem `w_compact_support` / 定理 `w_compact_support`

English:
theorem w_compact_support
  given: {D : Real} (Dpos : 0 < D)
  statement: HasCompactSupport (w D : E -> Real)
  proof: by
  rw [hasCompactSupport_def]; rw [w_support E Dpos]; rw [closure_ball (0 : E) Dpos.ne']
  exact isCompact_closedBall _ _

中文:
定理 w_compact_support
  条件: {D : 实数} (Dpos : 0 < D)
  结论: HasCompactSupport (w D : E -> 实数)
  证明: by
  rw [hasCompactSupport_def]; rw [w_support E Dpos]; rw [closure_ball (0 : E) Dpos.ne']
  exact isCompact_closedBall _ _

Depends on / 依赖: Dpos.ne, closure_ball, hasCompactSupport_def, isCompact_closedBall, w_support
-/
theorem w_compact_support {D : Real} (Dpos : 0 < D) : HasCompactSupport (w D : E -> Real) := by
  rw [hasCompactSupport_def]; rw [w_support E Dpos]; rw [closure_ball (0 : E) Dpos.ne']
  exact isCompact_closedBall _ _

variable {E}

/--
Definition of `y` / `y` 的定义

English:
definition y
  signature: (D : Real)
  body: w D ⋆[lsmul Real Real, μ] φ

中文:
定义 y
  签名: (D : 实数)
  定义体: w D ⋆[lsmul Real Real, μ] φ
-/
def y (D : Real) : E -> Real :=
  w D ⋆[lsmul Real Real, μ] φ

/--
theorem `y_neg` / 定理 `y_neg`

English:
theorem y_neg
  given: (D : Real) (x : E)
  statement: y D (-x) = y D x
  proof: by
  apply convolution_neg_of_neg_eq
  · filter_upwards with x
    simp only [w_def, mul_inv_rev, smul_neg, u_neg, smul_eq_mul]
  · filter_upwards with x
    simp only [φ, indicator, mem_closedBall, dist_zero_right, norm_neg]

中文:
定理 y_neg
  条件: (D : 实数) (x : E)
  结论: y D (-x) = y D x
  证明: by
  apply convolution_neg_of_neg_eq
  · filter_upwards with x
    simp only [w_def, mul_inv_rev, smul_neg, u_neg, smul_eq_mul]
  · filter_upwards with x
    simp only [φ, indicator, mem_closedBall, dist_zero_right, norm_neg]

Depends on / 依赖: convolution_neg_of_neg_eq, dist_zero_right, filter_upwards, indicator, mem_closedBall, mul_inv_rev, norm_neg, smul_eq_mul, smul_neg, u_neg, w_def
-/
theorem y_neg (D : Real) (x : E) : y D (-x) = y D x := by
  apply convolution_neg_of_neg_eq
  · filter_upwards with x
    simp only [w_def, mul_inv_rev, smul_neg, u_neg, smul_eq_mul]
  · filter_upwards with x
    simp only [φ, indicator, mem_closedBall, dist_zero_right, norm_neg]

/--
theorem `y_eq_one_of_mem_closedBall` / 定理 `y_eq_one_of_mem_closedBall`

English:
theorem y_eq_one_of_mem_closedBall
  statement: {D : Real} {x : E} (Dpos : 0 < D)
  proof: by
  change (w D ⋆[lsmul Real Real, μ] φ) x = 1
  have B : forall y : E, y in ball x D -> φ y = 1 := by
    have C : ball x D subseteq ball 0 1 := by
      apply ball_subset_ball'
      simp only [mem_closedBall] at hx
      linarith only [hx]
    intro y hy
    simp only [φ, indicator, mem_closedBa

中文:
定理 y_eq_one_of_mem_closedBall
  结论: {D : 实数} {x : E} (Dpos : 0 < D)
  证明: by
  change (w D ⋆[lsmul Real Real, μ] φ) x = 1
  have B : forall y : E, y in ball x D -> φ y = 1 := by
    have C : ball x D subseteq ball 0 1 := by
      apply ball_subset_ball'
      simp only [mem_closedBall] at hx
      linarith only [hx]
    intro y hy
    simp only [φ, indicator, mem_closedBa

Depends on / 依赖: ball_subset_ball, convolution_eq_right, indicator, ite_eq_left_iff, mem_ball, mem_ball_self, mem_closedBall, not_le, subseteq, zero_ne_one
-/
theorem y_eq_one_of_mem_closedBall {D : Real} {x : E} (Dpos : 0 < D)
    (hx : x in closedBall (0 : E) (1 - D)) : y D x = 1 := by
  change (w D ⋆[lsmul Real Real, μ] φ) x = 1
  have B : forall y : E, y in ball x D -> φ y = 1 := by
    have C : ball x D subseteq ball 0 1 := by
      apply ball_subset_ball'
      simp only [mem_closedBall] at hx
      linarith only [hx]
    intro y hy
    simp only [φ, indicator, mem_closedBall, ite_eq_left_iff, not_le, zero_ne_one]
    intro h'y
    linarith only [mem_ball.1 (C hy), h'y]
  have Bx : φ x = 1 := B _ (mem_ball_self Dpos)
  have B' : forall y, y in ball x D -> φ y = φ x := by rw [Bx]; exact B
  rw [convolution_eq_right' _ (le_of_eq (w_support E Dpos)) B']
  simp only [lsmul_apply, smul_eq_mul, integral_mul_const, w_integral E Dpos, Bx,
    one_mul]

/--
theorem `y_eq_zero_of_notMem_ball` / 定理 `y_eq_zero_of_notMem_ball`

English:
theorem y_eq_zero_of_notMem_ball
  given: {D : Real} {x : E} (Dpos : 0 < D) (hx : x ∉ ball (0 : E) (1 + D))
  proof: by
  change (w D ⋆[lsmul Real Real, μ] φ) x = 0
  have B : forall y, y in ball x D -> φ y = 0 := by
    intro y hy
    simp only [φ, indicator, mem_closedBall_zero_iff, ite_eq_right_iff, one_ne_zero]
    intro h'y
    have C : ball y D subseteq ball 0 (1 + D) := by
      apply ball_subset_ball'
    

中文:
定理 y_eq_zero_of_notMem_ball
  条件: {D : 实数} {x : E} (Dpos : 0 < D) (hx : x ∉ ball (0 : E) (1 + D))
  证明: by
  change (w D ⋆[lsmul Real Real, μ] φ) x = 0
  have B : forall y, y in ball x D -> φ y = 0 := by
    intro y hy
    simp only [φ, indicator, mem_closedBall_zero_iff, ite_eq_right_iff, one_ne_zero]
    intro h'y
    have C : ball y D subseteq ball 0 (1 + D) := by
      apply ball_subset_ball'
    

Depends on / 依赖: ball_subset_ball, convolution_eq_right, dist_zero_right, indicator, ite_eq_right_iff, mem_ball_comm, mem_ball_self, mem_closedBall_zero_iff, one_ne_zero, subseteq
-/
theorem y_eq_zero_of_notMem_ball {D : Real} {x : E} (Dpos : 0 < D) (hx : x ∉ ball (0 : E) (1 + D)) :
    y D x = 0 := by
  change (w D ⋆[lsmul Real Real, μ] φ) x = 0
  have B : forall y, y in ball x D -> φ y = 0 := by
    intro y hy
    simp only [φ, indicator, mem_closedBall_zero_iff, ite_eq_right_iff, one_ne_zero]
    intro h'y
    have C : ball y D subseteq ball 0 (1 + D) := by
      apply ball_subset_ball'
      rw [← dist_zero_right] at h'y
      linarith only [h'y]
    exact hx (C (mem_ball_comm.1 hy))
  have Bx : φ x = 0 := B _ (mem_ball_self Dpos)
  have B' : forall y, y in ball x D -> φ y = φ x := by rw [Bx]; exact B
  rw [convolution_eq_right' _ (le_of_eq (w_support E Dpos)) B']
  simp only [lsmul_apply, smul_eq_mul, Bx, mul_zero, integral_const]

/--
theorem `y_nonneg` / 定理 `y_nonneg`

English:
theorem y_nonneg
  given: (D : Real) (x : E)
  statement: 0 <= y D x
  proof: integral_nonneg (w_mul_φ_nonneg D x)

中文:
定理 y_nonneg
  条件: (D : 实数) (x : E)
  结论: 0 <= y D x
  证明: integral_nonneg (w_mul_φ_nonneg D x)

Depends on / 依赖: integral_nonneg
-/
theorem y_nonneg (D : Real) (x : E) : 0 <= y D x :=
  integral_nonneg (w_mul_φ_nonneg D x)

/--
theorem `y_le_one` / 定理 `y_le_one`

English:
theorem y_le_one
  given: {D : Real} (x : E) (Dpos : 0 < D)
  statement: y D x <= 1
  proof: by
  have A : (w D ⋆[lsmul Real Real, μ] φ) x <= (w D ⋆[lsmul Real Real, μ] 1) x := by
    apply
      convolution_mono_right_of_nonneg _ (w_nonneg D) (indicator_le_self' fun x _ => zero_le_one)
        fun _ => zero_le_one
    refine ((w_compact_support E Dpos).convolutionExists_left _ ?_
      (lo

中文:
定理 y_le_one
  条件: {D : 实数} (x : E) (Dpos : 0 < D)
  结论: y D x <= 1
  证明: by
  have A : (w D ⋆[lsmul Real Real, μ] φ) x <= (w D ⋆[lsmul Real Real, μ] 1) x := by
    apply
      convolution_mono_right_of_nonneg _ (w_nonneg D) (indicator_le_self' fun x _ => zero_le_one)
        fun _ => zero_le_one
    refine ((w_compact_support E Dpos).convolutionExists_left _ ?_
      (lo

Depends on / 依赖: continuous_const, continuous_const.mul, convolution, convolutionExists_left, convolution_mono_right_of_nonneg, fun_prop, indicator_le_self, integrable, locallyIntegrable_const, lsmul_apply, mul_one, u_continuous, w_compact_support, w_nonneg, zero_le_one
-/
theorem y_le_one {D : Real} (x : E) (Dpos : 0 < D) : y D x <= 1 := by
  have A : (w D ⋆[lsmul Real Real, μ] φ) x <= (w D ⋆[lsmul Real Real, μ] 1) x := by
    apply
      convolution_mono_right_of_nonneg _ (w_nonneg D) (indicator_le_self' fun x _ => zero_le_one)
        fun _ => zero_le_one
    refine ((w_compact_support E Dpos).convolutionExists_left _ ?_
      (locallyIntegrable_const (1 : Real)) x).integrable
    exact continuous_const.mul ((u_continuous E).comp (by fun_prop))
  have B : (w D ⋆[lsmul Real Real, μ] fun _ => (1 : Real)) x = 1 := by
    simp only [convolution, mul_one, lsmul_apply, smul_eq_mul, w_integral E Dpos]
  exact A.trans (le_of_eq B)

/--
theorem `y_pos_of_mem_ball` / 定理 `y_pos_of_mem_ball`

English:
theorem y_pos_of_mem_ball
  statement: {D : Real} {x : E} (Dpos : 0 < D) (D_lt_one : D < 1)
  proof: by
  simp only [mem_ball_zero_iff] at hx
  refine (integral_pos_iff_support_of_nonneg (w_mul_φ_nonneg D x) ?_).2 ?_
  · have F_comp : HasCompactSupport (w D) := w_compact_support E Dpos
    have B : LocallyIntegrable (φ : E -> Real) μ :=
      (locallyIntegrable_const _).indicator measurableSet_clos

中文:
定理 y_pos_of_mem_ball
  结论: {D : 实数} {x : E} (Dpos : 0 < D) (D_lt_one : D < 1)
  证明: by
  simp only [mem_ball_zero_iff] at hx
  refine (integral_pos_iff_support_of_nonneg (w_mul_φ_nonneg D x) ?_).2 ?_
  · have F_comp : HasCompactSupport (w D) := w_compact_support E Dpos
    have B : LocallyIntegrable (φ : E -> Real) μ :=
      (locallyIntegrable_const _).indicator measurableSet_clos

Depends on / 依赖: Continuous, F_comp, F_comp.convolutionExists_left, HasCompactSupport, LocallyIntegrable, continuous_const, continuous_const.mul, convolutionExists_left, fun_prop, indicator, integrable, integral_pos_iff_support_of_nonneg, locallyIntegrable_const, measurableSet_closedBall, mem_ball_zero_iff, u_continuous, w_compact_support
-/
theorem y_pos_of_mem_ball {D : Real} {x : E} (Dpos : 0 < D) (D_lt_one : D < 1)
    (hx : x in ball (0 : E) (1 + D)) : 0 < y D x := by
  simp only [mem_ball_zero_iff] at hx
  refine (integral_pos_iff_support_of_nonneg (w_mul_φ_nonneg D x) ?_).2 ?_
  · have F_comp : HasCompactSupport (w D) := w_compact_support E Dpos
    have B : LocallyIntegrable (φ : E -> Real) μ :=
      (locallyIntegrable_const _).indicator measurableSet_closedBall
    have C : Continuous (w D : E -> Real) :=
      continuous_const.mul ((u_continuous E).comp (by fun_prop))
    exact (F_comp.convolutionExists_left (lsmul Real Real : Real ->L[Real] Real ->L[Real] Real) C B x).integrable
  · set z := (D / (1 + D)) • x with hz
    have B : 0 < 1 + D := by linarith
    have C : ball z (D * (1 + D - ‖x‖) / (1 + D)) subseteq support fun y : E => w D y * φ (x - y) := by
      intro y hy
      simp only [support_mul, w_support E Dpos]
      simp only [φ, mem_inter_iff, mem_support, Ne, indicator_apply_eq_zero,
        mem_closedBall_zero_iff, one_ne_zero, not_forall, not_false_iff, exists_prop, and_true]
      constructor
      · apply ball_subset_ball' _ hy
        simp only [hz, norm_smul, abs_of_nonneg Dpos.le, abs_of_nonneg B.le, dist_zero_right,
          Real.norm_eq_abs, abs_div]
        field_simp
        linarith only
      · have ID : ‖D / (1 + D) - 1‖ = 1 / (1 + D) := by
          rw [Real.norm_of_nonpos]
          · field
          · field_simp
            linarith only
        rw [← mem_closedBall_iff_norm']
        apply closedBall_subset_closedBall' _ (ball_subset_closedBall hy)
        rw [← one_smul Real x]; rw [dist_eq_norm]; rw [hz]; rw [← sub_smul]; rw [one_smul]; rw [norm_smul]; rw [ID]
        field_simp
        nlinarith only [hx, D_lt_one]
    apply lt_of_lt_of_le _ (measure_mono C)
    apply measure_ball_pos
    exact div_pos (mul_pos Dpos (by linarith only [hx])) B

variable (E)

/--
theorem `y_smooth` / 定理 `y_smooth`

English:
theorem y_smooth
  statement: ContDiffOn Real ∞ (uncurry y) (Ioo (0 : Real) 1 ×ˢ (univ : Set E))
  proof: by
  have hs : IsOpen (Ioo (0 : Real) (1 : Real)) := isOpen_Ioo
  have hk : IsCompact (closedBall (0 : E) 1) := ProperSpace.isCompact_closedBall _ _
  refine contDiffOn_convolution_left_with_param (lsmul Real Real) hs hk ?_ ?_ ?_
  · rintro p x hp hx
    simp only [w, mul_inv_rev, smul_eq_mul, mul_e

中文:
定理 y_smooth
  结论: ContDiffOn 实数 ∞ (uncurry y) (Ioo (0 : 实数) 1 ×ˢ (univ : Set E))
  证明: by
  have hs : IsOpen (Ioo (0 : Real) (1 : Real)) := isOpen_Ioo
  have hk : IsCompact (closedBall (0 : E) 1) := ProperSpace.isCompact_closedBall _ _
  refine contDiffOn_convolution_left_with_param (lsmul Real Real) hs hk ?_ ?_ ?_
  · rintro p x hp hx
    simp only [w, mul_inv_rev, smul_eq_mul, mul_e

Depends on / 依赖: IsCompact, IsOpen, ProperSpace, ProperSpace.isCompact_closedBall, Real.norm_eq_abs, abs_inv, abs_of_nonneg, closedBall, contDiffOn_convolution_left_with_param, contrapose, div_eq_inv_mul, inv_eq_zero, isCompact_closedBall, isOpen_Ioo, mem_ball_zero_iff, mem_support, mul_eq_zero, mul_inv_rev, norm_eq_abs, norm_smul
-/
theorem y_smooth : ContDiffOn Real ∞ (uncurry y) (Ioo (0 : Real) 1 ×ˢ (univ : Set E)) := by
  have hs : IsOpen (Ioo (0 : Real) (1 : Real)) := isOpen_Ioo
  have hk : IsCompact (closedBall (0 : E) 1) := ProperSpace.isCompact_closedBall _ _
  refine contDiffOn_convolution_left_with_param (lsmul Real Real) hs hk ?_ ?_ ?_
  · rintro p x hp hx
    simp only [w, mul_inv_rev, smul_eq_mul, mul_eq_zero, inv_eq_zero]
    right
    contrapose! hx
    have : p⁻¹ • x in support u := mem_support.2 hx
    simp only [u_support, norm_smul, mem_ball_zero_iff, Real.norm_eq_abs, abs_inv,
      abs_of_nonneg hp.1.le, ← div_eq_inv_mul, div_lt_one hp.1] at this
    rw [mem_closedBall_zero_iff]
    exact this.le.trans hp.2.le
  · exact (locallyIntegrable_const _).indicator measurableSet_closedBall
  · apply ContDiffOn.mul
    · norm_cast
      refine
        (contDiffOn_const.mul ?_).inv fun x hx =>
          ne_of_gt (mul_pos (u_int_pos E) (pow_pos (abs_pos_of_pos hx.1.1) (finrank Real E)))
      apply ContDiffOn.pow
      simp_rw [← Real.norm_eq_abs]
      apply ContDiffOn.norm Real
      · exact contDiffOn_fst
      · intro x hx; exact ne_of_gt hx.1.1
    · apply (u_smooth E).comp_contDiffOn
      exact ContDiffOn.smul (contDiffOn_fst.inv fun x hx => ne_of_gt hx.1.1) contDiffOn_snd

/--
theorem `y_support` / 定理 `y_support`

English:
theorem y_support
  given: {D : Real} (Dpos : 0 < D) (D_lt_one : D < 1)
  proof: support_eq_iff.2
    ⟨fun _ hx => (y_pos_of_mem_ball Dpos D_lt_one hx).ne', fun _ hx =>
      y_eq_zero_of_notMem_ball Dpos hx⟩

中文:
定理 y_support
  条件: {D : 实数} (Dpos : 0 < D) (D_lt_one : D < 1)
  证明: support_eq_iff.2
    ⟨fun _ hx => (y_pos_of_mem_ball Dpos D_lt_one hx).ne', fun _ hx =>
      y_eq_zero_of_notMem_ball Dpos hx⟩

Depends on / 依赖: D_lt_one, support_eq_iff, y_eq_zero_of_notMem_ball, y_pos_of_mem_ball
-/
theorem y_support {D : Real} (Dpos : 0 < D) (D_lt_one : D < 1) :
    support (y D : E -> Real) = ball (0 : E) (1 + D) :=
  support_eq_iff.2
    ⟨fun _ hx => (y_pos_of_mem_ball Dpos D_lt_one hx).ne', fun _ hx =>
      y_eq_zero_of_notMem_ball Dpos hx⟩

end HelperDefinitions

instance (priority := 100) {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
    [FiniteDimensional Real E] : HasContDiffBump E := by
  refine ⟨⟨?_⟩⟩
  borelize E
  have IR : forall R : Real, 1 < R -> 0 < (R - 1) / (R + 1) := by intro R hR; apply div_pos <;> linarith
  exact
    { toFun := fun R x => if 1 < R then y ((R - 1) / (R + 1)) (((R + 1) / 2)⁻¹ • x) else 0
      mem_Icc := fun R x => by
        push _ in _
        split_ifs with h
        · refine ⟨y_nonneg _ _, y_le_one _ (IR R h)⟩
        · simp only [le_refl, zero_le_one, and_self]
      symmetric := fun R x => by
        split_ifs
        · simp only [y_neg, smul_neg]
        · rfl
      smooth := by
        suffices
          ContDiffOn Real ∞
            (uncurry y ∘ fun p : Real × E => ((p.1 - 1) / (p.1 + 1), ((p.1 + 1) / 2)⁻¹ • p.2))
            (Ioi 1 ×ˢ univ) by
          apply this.congr
          rintro ⟨R, x⟩ ⟨hR : 1 < R, _⟩
          simp only [hR, uncurry_apply_pair, if_true, Function.comp_apply]
        apply (y_smooth E).comp
        · apply ContDiffOn.prodMk
          · refine
              (contDiffOn_fst.sub contDiffOn_const).div (contDiffOn_fst.add contDiffOn_const) ?_
            rintro ⟨R, x⟩ ⟨hR : 1 < R, _⟩
            apply ne_of_gt
            dsimp only
            linarith
          · apply ContDiffOn.smul _ contDiffOn_snd
            refine ((contDiffOn_fst.add contDiffOn_const).div_const _).inv ?_
            rintro ⟨R, x⟩ ⟨hR : 1 < R, _⟩
            apply ne_of_gt
            dsimp only
            linarith
        · rintro ⟨R, x⟩ ⟨hR : 1 < R, _⟩
          have A : 0 < (R - 1) / (R + 1) := by apply div_pos <;> linarith
          have B : (R - 1) / (R + 1) < 1 := by apply (div_lt_one _).2 <;> linarith
          simp only [prodMk_mem_set_prod_eq, mem_Ioo, mem_univ, and_true, A, B]
      eq_one := fun R hR x hx => by
        have A : 0 < R + 1 := by linarith
        simp only [hR, if_true]
        apply y_eq_one_of_mem_closedBall (IR R hR)
        simp only [norm_smul, inv_div, mem_closedBall_zero_iff, Real.norm_eq_abs, abs_div, abs_two,
          abs_of_nonneg A.le]
        calc
          2 / (R + 1) * ‖x‖ <= 2 / (R + 1) := mul_le_of_le_one_right (by positivity) hx
          _ = 1 - (R - 1) / (R + 1) := by field
      support := fun R hR => by
        have A : 0 < (R + 1) / 2 := by linarith
        have C : (R - 1) / (R + 1) < 1 := by apply (div_lt_one _).2 <;> linarith
        simp only [hR, if_true, support_comp_inv_smul₀ A.ne', y_support _ (IR R hR) C,
          _root_.smul_ball A.ne', Real.norm_of_nonneg A.le, smul_zero]
        refine congr (congr_arg ball (Eq.refl 0)) ?_
        field }

end ExistsContDiffBumpBase

end
