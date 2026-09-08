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

variable [NormedSpace ℝ E] [FiniteDimensional ℝ E]

/-- If a set `s` is a neighborhood of `x`, then there exists a smooth function `f` taking
values in `[0, 1]`, supported in `s` and with `f x = 1`. -/
/-
**exists_contDiff_tsupport_subset** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：exists_contDiff_tsupport_subset {s : Set E} {x : E} {n : Nat∞} (hs : s in 
𝓝 x) : exists f : E -> Real, tsupport f subseteq s ∧ HasCompactSupport f ∧ ContD
iff Real n f ∧ range f subseteq Icc 0 1 ∧ f x = 1
参数：hs : s in 𝓝 x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `TopologicalSpace.t2Space_of_metrizableSpace`：∀ {X : Type u_2} [inst : To
pologicalSpace X] [TopologicalSpace.MetrizableSpace X], T2Space X
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Filter.HasBasis.mem_iff`：∀ {α : Type u_1} {ι : Sort u_4} {l : Filter α} 
{p : ι → Prop} {s : ι → Set α} {t : Set α},   l.HasBasis p s → (t ∈ l ↔ ∃ i, p i
 ∧ s i ⊆ t)
· 使用定理 `Euclidean.nhds_basis_closedBall`：nhds_basis_closedBall {x : E} : (𝓝 x).H
asBasis (fun r : Real => 0 < r) (closedBall x)
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `half_pos`：half_pos (h : 0 < a) : 0 < a / 2
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `half_lt_self`：∀ {α : Type u_2} [inst : Semifield α] [inst_1 : PartialOrd
er α] [PosMulReflectLT α] {a : α} [IsStrictOrderedRing α],   0 < a → a / 2 < a
· 使用定理 `fact_one_le_two_ennreal`：Fact (1 ≤ 2)
· 使用定理 `hasContDiffBump_of_innerProductSpace`：∀ (E : Type u_1) [inst : NormedAdd
CommGroup E] [inst_1 : InnerProductSpace ℝ E], HasContDiffBump E
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ContDiffBump.support_eq`：support_eq : Function.support f = Metric.ball c
 f.rOut
· 使用定理 `tsupport.eq_1`：∀ {X : Type u_1} {α : Type u_2} [inst : Zero α] [inst_1 :
 TopologicalSpace X] (f : X → α),   tsupport f = closure (Function.support f)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Euclidean.closure_ball`：∀ {E : Type u_1} [inst : AddCommGroup E] [inst_1
 : TopologicalSpace E] [inst_2 : IsTopologicalAddGroup E]   [inst_3 : T2Space E]
 [inst_4 : _…
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `closure_mono`：closure_mono (h : s subseteq t) : closure s subseteq closu
re t
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `Metric.isCompact_of_isClosed_isBounded`：isCompact_of_isClosed_isBounded 
[ProperSpace α] (hc : IsClosed s) (hb : IsBounded s) : IsCompact s
· 使用定理 `FiniteDimensional.proper_real`：∀ (E : Type u) [inst : NormedAddCommGroup
 E] [inst_1 : NormedSpace ℝ E] [FiniteDimensional ℝ E], ProperSpace E
· 使用定理 `isClosed_closure`：isClosed_closure : IsClosed (closure s)
· 使用定理 `IsCompact.isBounded`：∀ {α : Type u} [inst : PseudoMetricSpace α] {s : Se
t α}, IsCompact s → Bornology.IsBounded s
· 使用定理 `Euclidean.isCompact_closedBall`：∀ {E : Type u_1} [inst : AddCommGroup E]
 [inst_1 : TopologicalSpace E] [inst_2 : IsTopologicalAddGroup E]   [inst_3 : T2
Space E] [inst_4 : _…
· 使用定理 `Bornology.IsBounded.subset`：∀ {α : Type u_2} {x : Bornology α} {s t : Se
t α}, Bornology.IsBounded t → s ⊆ t → Bornology.IsBounded s
（共 42 条，此处仅展示前 30 条）

--- 原说明 ---
If a set `s` is a neighborhood of `x`, then there exists a smooth function `f` t
aking
values in `[0, 1]`, supported in `s` and with `f x = 1`.
-/
theorem exists_contDiff_tsupport_subset {s : Set E} {x : E} {n : ℕ∞} (hs : s ∈ 𝓝 x) :
    ∃ f : E → ℝ,
      tsupport f ⊆ s ∧ HasCompactSupport f ∧ ContDiff ℝ n f ∧ range f ⊆ Icc 0 1 ∧ f x = 1 := by
  obtain ⟨d : ℝ, d_pos : 0 < d, hd : Euclidean.closedBall x d ⊆ s⟩ :=
    Euclidean.nhds_basis_closedBall.mem_iff.1 hs
  let c : ContDiffBump (toEuclidean x) :=
    { rIn := d / 2
      rOut := d
      rIn_pos := half_pos d_pos
      rIn_lt_rOut := half_lt_self d_pos }
  let f : E → ℝ := c ∘ toEuclidean
  have f_supp : f.support ⊆ Euclidean.ball x d := by
    intro y hy
    have : toEuclidean y ∈ Function.support c := by
      simpa only [Function.mem_support, Function.comp_apply, Ne] using! hy
    rwa [c.support_eq] at this
  have f_tsupp : tsupport f ⊆ Euclidean.closedBall x d := by
    rw [tsupport, ← Euclidean.closure_ball _ d_pos.ne']
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

/-- Given an open set `s` in a finite-dimensional real normed vector space, there exists a smooth
function with values in `[0, 1]` whose support is exactly `s`. -/
/-
**IsOpen.exists_contDiff_support_eq** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsOpen.exists_contDiff_support_eq {n : Nat∞} {s : Set E} (hs : IsOpen s) :
 exists f : E -> Real, f.support = s ∧ ContDiff Real n f ∧ Set.range f subseteq 
Set.Icc 0 1
参数：hs : IsOpen s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.eq_empty_or_nonempty`：eq_empty_or_nonempty (s : Set α) : s = ∅ ∨ s.N
onempty
· 使用定理 `Function.support_zero`：∀ {ι : Type u_1} {M : Type u_3} [inst : Zero M], 
Function.support 0 = ∅
· 使用定理 `contDiff_const`：contDiff_const {c : F} : ContDiff 𝕜 n fun _ : E => c
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.range_const`：range_const : forall [Nonempty ι] {c : α}, (range fun _
 : ι => c) = {c}
· 使用定理 `AddTorsor.nonempty`：∀ {G : outParam (Type u_1)} {P : Type u_2} {inst : A
ddGroup G} [self : AddTorsor G P], Nonempty P
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.Subset.antisymm`：∀ {α : Type u} {a b : Set α}, a ⊆ b → b ⊆ a → a = b
· 使用定理 `Set.iUnion_subset`：iUnion_subset {s : ι -> Set α} {t : Set α} (h : foral
l i, s i subseteq t) : ⋃ i, s i subseteq t
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `exists_contDiff_tsupport_subset`：exists_contDiff_tsupport_subset {s : Se
t E} {x : E} {n : Nat∞} (hs : s in 𝓝 x) : exists f : E -> Real, tsupport f subse
teq s ∧ HasCompactSup…
· 使用定理 `IsOpen.mem_nhds`：IsOpen.mem_nhds (hs : IsOpen s) (hx : x in s) : s in 𝓝 
x
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `subset_tsupport`：∀ {X : Type u_1} {α : Type u_2} [inst : Zero α] [inst_1
 : TopologicalSpace X] (f : X → α),   Function.support f ⊆ tsupport f
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `Set.mem_iUnion_of_mem`：mem_iUnion_of_mem {s : ι -> Set α} {a : α} (i : ι
) (ha : a in s i) : a in ⋃ i, s i
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `TopologicalSpace.isOpen_iUnion_countable`：isOpen_iUnion_countable [Secon
dCountableTopology α] {ι} (s : ι -> Set α) (H : forall i, IsOpen (s i)) : exists
 T : Set ι, T.Countable ∧ ⋃ i …
· 使用定理 `secondCountable_of_proper`：∀ {α : Type u} [inst : PseudoMetricSpace α] [
ProperSpace α], SecondCountableTopology α
· 使用定理 `FiniteDimensional.proper_real`：∀ (E : Type u) [inst : NormedAddCommGroup
 E] [inst_1 : NormedSpace ℝ E] [FiniteDimensional ℝ E], ProperSpace E
· 使用定理 `Continuous.isOpen_support`：∀ {X : Type u_1} {Y : Type u_2} [inst : Topol
ogicalSpace X] [T1Space X] [inst_2 : Zero X] [inst_3 : TopologicalSpace Y]   {f 
: Y → X}, Conti…
· 使用定理 `T5Space.toT1Space`：∀ {X : Type u} {inst : TopologicalSpace X} [self : T5
Space X], T1Space X
· 使用定理 `T6Space.toT5Space`：∀ {X : Type u_1} [inst : TopologicalSpace X] [T6Space
 X], T5Space X
· 使用定理 `instT6SpaceOfMetrizableSpace`：∀ {X : Type u_1} [inst : TopologicalSpace 
X] [TopologicalSpace.MetrizableSpace X], T6Space X
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α
（共 142 条，此处仅展示前 30 条）

--- 原说明 ---
Given an open set `s` in a finite-dimensional real normed vector space, there ex
ists a smooth
function with values in `[0, 1]` whose support is exactly `s`.
-/
theorem IsOpen.exists_contDiff_support_eq {n : ℕ∞} {s : Set E} (hs : IsOpen s) :
    ∃ f : E → ℝ, f.support = s ∧ ContDiff ℝ n f ∧ Set.range f ⊆ Set.Icc 0 1 := by
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
  let ι := { f : E → ℝ // f.support ⊆ s ∧ HasCompactSupport f ∧ ContDiff ℝ ∞ f ∧ range f ⊆ Icc 0 1 }
  obtain ⟨T, T_count, hT⟩ : ∃ T : Set ι, T.Countable ∧ ⋃ f ∈ T, support (f : E → ℝ) = s := by
    have : ⋃ f : ι, (f : E → ℝ).support = s := by
      refine Subset.antisymm (iUnion_subset fun f => f.2.1) ?_
      intro x hx
      rcases exists_contDiff_tsupport_subset (hs.mem_nhds hx) with ⟨f, hf⟩
      let g : ι := ⟨f, (subset_tsupport f).trans hf.1, hf.2.1, hf.2.2.1, hf.2.2.2.1⟩
      have : x ∈ support (g : E → ℝ) := by
        simp only [g, hf.2.2.2.2, mem_support, Ne, one_ne_zero, not_false_iff]
      exact mem_iUnion_of_mem _ this
    simp_rw [← this]
    apply isOpen_iUnion_countable
    rintro ⟨f, hf⟩
    exact hf.2.2.1.continuous.isOpen_support
  obtain ⟨g0, hg⟩ : ∃ g0 : ℕ → ι, T = range g0 := by
    apply Countable.exists_eq_range T_count
    rcases eq_empty_or_nonempty T with (rfl | hT)
    · simp only [← hT, mem_empty_iff_false, iUnion_of_empty, iUnion_empty, Set.not_nonempty_empty]
        at h's
    · exact hT
  let g : ℕ → E → ℝ := fun n => (g0 n).1
  have g_s : ∀ n, support (g n) ⊆ s := fun n => (g0 n).2.1
  have s_g : ∀ x ∈ s, ∃ n, x ∈ support (g n) := fun x hx ↦ by
    rw [← hT] at hx
    obtain ⟨i, iT, hi⟩ : ∃ i ∈ T, x ∈ support (i : E → ℝ) := by
      simpa only [mem_iUnion, exists_prop] using! hx
    #adaptation_note /-- Before https://github.com/leanprover/lean4/pull/13166
    (replacing grind's canonicalizer with a type-directed normalizer), `grind` closed this goal
    without the `obtain` on the next line. It is not yet clear whether this is due to defeq
    abuse in Mathlib or a problem in the new canonicalizer; a minimization would help. -/
    obtain ⟨n, hn⟩ := hg ▸ iT
    grind
  have g_smooth : ∀ n, ContDiff ℝ ∞ (g n) := fun n => (g0 n).2.2.2.1
  have g_comp_supp : ∀ n, HasCompactSupport (g n) := fun n => (g0 n).2.2.1
  have g_nonneg : ∀ n x, 0 ≤ g n x := fun n x => ((g0 n).2.2.2.2 (mem_range_self x)).1
  obtain ⟨δ, δpos, c, δc, c_lt⟩ :
      ∃ δ : ℕ → ℝ≥0, (∀ i : ℕ, 0 < δ i) ∧ ∃ c : NNReal, HasSum δ c ∧ c < 1 :=
    NNReal.exists_pos_sum_of_countable one_ne_zero ℕ
  have : ∀ n : ℕ, ∃ r : ℝ, 0 < r ∧ ∀ i ≤ n, ∀ x, ‖iteratedFDeriv ℝ i (r • g n) x‖ ≤ δ n := by
    intro n
    have : ∀ i, ∃ R, ∀ x, ‖iteratedFDeriv ℝ i (fun x => g n x) x‖ ≤ R := by
      intro i
      have : BddAbove (range fun x => ‖iteratedFDeriv ℝ i (fun x : E => g n x) x‖) := by
        apply ((g_smooth n).continuous_iteratedFDeriv
          (mod_cast le_top)).norm.bddAbove_range_of_hasCompactSupport
        apply HasCompactSupport.comp_left _ norm_zero
        apply (g_comp_supp n).iteratedFDeriv
      rcases this with ⟨R, hR⟩
      exact ⟨R, fun x => hR (mem_range_self _)⟩
    choose R hR using this
    let M := max (((Finset.range (n + 1)).image R).max' (by simp)) 1
    have δnpos : 0 < δ n := δpos n
    have IR : ∀ i ≤ n, R i ≤ M := by
      intro i hi
      refine le_trans ?_ (le_max_left _ _)
      apply Finset.le_max'
      apply Finset.mem_image_of_mem
      simp only [Finset.mem_range]
      lia
    refine ⟨M⁻¹ * δ n, by positivity, fun i hi x => ?_⟩
    calc
      ‖iteratedFDeriv ℝ i ((M⁻¹ * δ n) • g n) x‖ = ‖(M⁻¹ * δ n) • iteratedFDeriv ℝ i (g n) x‖ := by
        rw [iteratedFDeriv_const_smul_apply]
        exact (g_smooth n).contDiffAt.of_le (mod_cast le_top)
      _ = M⁻¹ * δ n * ‖iteratedFDeriv ℝ i (g n) x‖ := by
        rw [norm_smul _ (iteratedFDeriv ℝ i (g n) x), Real.norm_of_nonneg]; positivity
      _ ≤ M⁻¹ * δ n * M := by gcongr; exact (hR i x).trans (IR i hi)
      _ = δ n := by simp [field]
  choose r rpos hr using this
  have S : ∀ x, Summable fun n => (r n • g n) x := fun x ↦ by
    refine .of_nnnorm_bounded δc.summable fun n => ?_
    rw [← NNReal.coe_le_coe, coe_nnnorm]
    simpa only [norm_iteratedFDeriv_zero] using! hr n 0 zero_le x
  refine ⟨fun x => ∑' n, (r n • g n) x, ?_, ?_, ?_⟩
  · apply Subset.antisymm
    · intro x hx
      simp only [Pi.smul_apply, smul_eq_mul, mem_support, Ne] at hx
      contrapose hx
      have : ∀ n, g n x = 0 := by
        intro n
        contrapose! hx
        exact g_s n hx
      simp only [this, mul_zero, tsum_zero]
    · intro x hx
      obtain ⟨n, hn⟩ : ∃ n, x ∈ support (g n) := s_g x hx
      have I : 0 < r n * g n x := mul_pos (rpos n) (lt_of_le_of_ne (g_nonneg n x) (Ne.symm hn))
      exact ne_of_gt ((S x).tsum_pos (fun i => mul_nonneg (rpos i).le (g_nonneg i x)) n I)
  · apply ContDiff.of_le _ (show n ≤ ∞ from mod_cast le_top)
    refine
      contDiff_tsum_of_eventually (fun k => (g_smooth k).const_smul (r k))
        (fun k _ => (NNReal.hasSum_coe.2 δc).summable) ?_
    intro i _
    simp only [Nat.cofinite_eq_atTop, Filter.eventually_atTop]
    exact ⟨i, fun n hn x => hr _ _ hn _⟩
  · rintro - ⟨y, rfl⟩
    refine ⟨tsum_nonneg fun n => mul_nonneg (rpos n).le (g_nonneg n y), le_trans ?_ c_lt.le⟩
    have A : HasSum (fun n => (δ n : ℝ)) c := NNReal.hasSum_coe.2 δc
    simp only [Pi.smul_apply, smul_eq_mul, NNReal.val_eq_coe, ← A.tsum_eq]
    apply Summable.tsum_le_tsum _ (S y) A.summable
    intro n
    apply (le_abs_self _).trans
    simpa only [norm_iteratedFDeriv_zero] using! hr n 0 zero_le y

end

section

namespace ExistsContDiffBumpBase

/-- An auxiliary function to construct partitions of unity on finite-dimensional real vector spaces.
It is the characteristic function of the closed unit ball. -/
/-
**ExistsContDiffBumpBase.** 是 Mathlib 中的一个定义，位于命名空间 `ExistsContDiffBumpBase`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An auxiliary function to construct partitions of unity on finite-dimensional rea
l vector spaces.
It is the characteristic function of the closed unit ball.
-/
def φ : E → ℝ :=
  (closedBall (0 : E) 1).indicator fun _ => (1 : ℝ)

variable [NormedSpace ℝ E] [FiniteDimensional ℝ E]

section HelperDefinitions

variable (E)

/-
**ExistsContDiffBumpBase.u_exists** 是 Mathlib 中的一个定理，位于命名空间 `ExistsContDiffBumpB
ase`。
形式化陈述：u_exists : exists u : E -> Real, ContDiff Real ∞ u ∧ (forall x, u x in Icc
 (0 : Real) 1) ∧ support u = ball 0 1 ∧ forall x, u (-x) = u x
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Metric.isOpen_ball`：∀ {α : Type u} [inst : PseudoMetricSpace α] {x : α} 
{ε : ℝ}, IsOpen (Metric.ball x ε)
· 使用定理 `IsOpen.exists_contDiff_support_eq`：IsOpen.exists_contDiff_support_eq {n 
: Nat∞} {s : Set E} (hs : IsOpen s) : exists f : E -> Real, f.support = s ∧ Cont
Diff Real n f ∧ Set.ran…
· 使用定理 `Set.mem_range_self`：∀ {α : Type u} {ι : Sort u_1} {f : ι → α} (i : ι), f
 i ∈ Set.range f
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `ContDiff.div_const`：ContDiff.div_const {f : E -> 𝕜'} {n} (hf : ContDiff 
𝕜 n f) (c : 𝕜') : ContDiff 𝕜 n fun x => f x / c
· 使用定理 `ContDiff.add`：ContDiff.add {f g : E -> F} (hf : ContDiff 𝕜 n f) (hg : Co
ntDiff 𝕜 n g) : ContDiff 𝕜 n fun x => f x + g x
· 使用定理 `ContDiff.comp`：ContDiff.comp {g : F -> G} {f : E -> F} (hg : ContDiff 𝕜 
n g) (hf : ContDiff 𝕜 n f) : ContDiff 𝕜 n (g ∘ f)
· 使用定理 `contDiff_neg`：contDiff_neg : ContDiff 𝕜 n fun p : F => -p
· 使用引理 `le_of_not_gt`：le_of_not_gt (h : ¬b < a) : a <= b
· 使用定理 `Mathlib.Tactic.Linarith.lt_irrefl`：lt_irrefl {α : Type u} [Preorder α] {
a : α} : ¬a < a
· 使用引理 `Mathlib.Meta.NormNum.instAtLeastTwo`：instAtLeastTwo (n : Nat) : Nat.AtLe
astTwo (n + 2)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Mathlib.Tactic.Ring.of_eq`：∀ {α : Sort u_2} {a b c : α}, a = c → b = c →
 a = b
· 使用定理 `Mathlib.Tactic.Ring.Common.add_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' + b' = c → a + b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.sub_congr`：∀ {R : Type u_2} [inst : CommRing 
R] {a a' b b' c : R}, a = a' → b = b' → a' - b' = c → a - b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' * b' = c → a * b = c
· 使用定理 `Mathlib.Tactic.Ring.cast_pos`：∀ {R : Type u_1} [inst : CommSemiring R] {
a : R} {n : ℕ}, Mathlib.Meta.NormNum.IsNat a n → a = n.rawCast + 0
· 使用定理 `Mathlib.Meta.NormNum.isNat_ofNat`：isNat_ofNat (α : Type u) [AddMonoidWit
hOne α] {a : α} {n : Nat} (h : n = a) : IsNat a n
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `Mathlib.Tactic.Ring.Common.atom_pf`：∀ {R : Type u_1} [inst : CommSemirin
g R] {b : R} (a : R) {e : ℕ},   Nat.rawCast 1 = e → a ^ e * Nat.rawCast 1 = b → 
a = b + 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Mathlib.Tactic.Ring.Common.add_mul`：∀ {R : Type u_1} [inst : CommSemirin
g R] {a₁ a₂ b c₁ c₂ d : R},   a₁ * b = c₁ → a₂ * b = c₂ → c₁ + c₂ = d → (a₁ + a₂
) * b = d
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_add`：∀ {R : Type u_1} [inst : CommSemirin
g R] {a b₁ b₂ c₁ c₂ d : R},   a * b₁ = c₁ → a * b₂ = c₂ → c₁ + 0 + c₂ = d → a * 
(b₁ + b₂) = d
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_pf_right`：∀ {R : Type u_1} [inst : CommSe
miring R] {a b₃ c : R} (b₁ : R) (b₂ : ℕ), a * b₃ = c → a * (b₁ ^ b₂ * b₃) = b₁ ^
 b₂ * c
· 使用定理 `Mathlib.Meta.NormNum.IsNat.to_raw_eq`：∀ {α : Type u} {a : α} {n : ℕ} [in
st : AddMonoidWithOne α], Mathlib.Meta.NormNum.IsNat a n → a = n.rawCast
· 使用定理 `Mathlib.Meta.NormNum.isNat_mul`：∀ {α : Type u_1} [inst : Semiring α] {f 
: α → α → α} {a b : α} {a' b' c : ℕ},   f = HMul.hMul →     Mathlib.Meta.NormNum
.IsNat a a' →       …
· 使用定理 `Mathlib.Meta.NormNum.IsNat.of_raw`：∀ (α : Type u_1) [inst : AddMonoidWit
hOne α] (n : ℕ), Mathlib.Meta.NormNum.IsNat n.rawCast n
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_zero`：∀ {R : Type u_1} [inst : CommSemiri
ng R] (a : R), a * 0 = 0
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_add_zero`：∀ {R : Type u_1} [inst : Com
mSemiring R] (a : R), a + 0 = a
（共 84 条，此处仅展示前 30 条）
-/
theorem u_exists :
    ∃ u : E → ℝ,
      ContDiff ℝ ∞ u ∧ (∀ x, u x ∈ Icc (0 : ℝ) 1) ∧ support u = ball 0 1 ∧ ∀ x, u (-x) = u x := by
  have A : IsOpen (ball (0 : E) 1) := isOpen_ball
  obtain ⟨f, f_support, f_smooth, f_range⟩ :
      ∃ f : E → ℝ, f.support = ball (0 : E) 1 ∧ ContDiff ℝ ∞ f ∧ Set.range f ⊆ Set.Icc 0 1 :=
    A.exists_contDiff_support_eq
  have B : ∀ x, f x ∈ Icc (0 : ℝ) 1 := fun x => f_range (mem_range_self x)
  refine ⟨fun x => (f x + f (-x)) / 2, ?_, ?_, ?_, ?_⟩
  · exact (f_smooth.add (f_smooth.comp contDiff_neg)).div_const _
  · intro x
    push _ ∈ _
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
/-- An auxiliary function to construct partitions of unity on finite-dimensional real vector spaces,
which is smooth, symmetric, and with support equal to the unit ball. -/
/-
**ExistsContDiffBumpBase.u** 是 Mathlib 中的一个定义，位于命名空间 `ExistsContDiffBumpBase`。
形式化陈述：u (x : E) : Real
参数：x : E。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `ExistsContDiffBumpBase.u_exists`：u_exists : exists u : E -> Real, ContDi
ff Real ∞ u ∧ (forall x, u x in Icc (0 : Real) 1) ∧ support u = ball 0 1 ∧ foral
l x, u (-x) = u x

--- 原说明 ---
An auxiliary function to construct partitions of unity on finite-dimensional rea
l vector spaces,
which is smooth, symmetric, and with support equal to the unit ball.
-/
def u (x : E) : ℝ :=
  Classical.choose (u_exists E) x
/-
**ExistsContDiffBumpBase.u_smooth** 是 Mathlib 中的一个定理，位于命名空间 `ExistsContDiffBumpB
ase`。
形式化陈述：u_smooth : ContDiff Real ∞ (u : E -> Real)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `ExistsContDiffBumpBase.u_exists`：u_exists : exists u : E -> Real, ContDi
ff Real ∞ u ∧ (forall x, u x in Icc (0 : Real) 1) ∧ support u = ball 0 1 ∧ foral
l x, u (-x) = u x
· 使用定理 `Classical.choose_spec`：∀ {α : Sort u} {p : α → Prop} (h : ∃ x, p x), p (
Classical.choose h)
-/
theorem u_smooth : ContDiff ℝ ∞ (u : E → ℝ) :=
  (Classical.choose_spec (u_exists E)).1
/-
**ExistsContDiffBumpBase.u_continuous** 是 Mathlib 中的一个定理，位于命名空间 `ExistsContDiffB
umpBase`。
形式化陈述：u_continuous : Continuous (u : E -> Real)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContDiff.continuous`：ContDiff.continuous (h : ContDiff 𝕜 n f) : Continuo
us f
· 使用定理 `ExistsContDiffBumpBase.u_smooth`：u_smooth : ContDiff Real ∞ (u : E -> Re
al)
-/
theorem u_continuous : Continuous (u : E → ℝ) :=
  (u_smooth E).continuous
/-
**ExistsContDiffBumpBase.u_support** 是 Mathlib 中的一个定理，位于命名空间 `ExistsContDiffBump
Base`。
形式化陈述：u_support : support (u : E -> Real) = ball 0 1
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `ExistsContDiffBumpBase.u_exists`：u_exists : exists u : E -> Real, ContDi
ff Real ∞ u ∧ (forall x, u x in Icc (0 : Real) 1) ∧ support u = ball 0 1 ∧ foral
l x, u (-x) = u x
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Classical.choose_spec`：∀ {α : Sort u} {p : α → Prop} (h : ∃ x, p x), p (
Classical.choose h)
-/
theorem u_support : support (u : E → ℝ) = ball 0 1 :=
  (Classical.choose_spec (u_exists E)).2.2.1
/-
**ExistsContDiffBumpBase.u_compact_support** 是 Mathlib 中的一个定理，位于命名空间 `ExistsCont
DiffBumpBase`。
形式化陈述：u_compact_support : HasCompactSupport (u : E -> Real)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `hasCompactSupport_def`：∀ {α : Type u_2} {β : Type u_4} [inst : Topologic
alSpace α] [inst_1 : Zero β] {f : α → β},   HasCompactSupport f ↔ IsCompact (clo
sure (Funct…
· 使用定理 `ExistsContDiffBumpBase.u_support`：u_support : support (u : E -> Real) = 
ball 0 1
· 使用定理 `closure_ball`：closure_ball (x : E) {r : Real} (hr : r != 0) : closure (b
all x r) = closedBall x r
· 使用定理 `one_ne_zero`：∀ {α : Type u_2} [inst : Zero α] [inst_1 : One α] [NeZero 1
], 1 ≠ 0
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `ProperSpace.isCompact_closedBall`：∀ {α : Type u} {inst : PseudoMetricSpa
ce α} [self : ProperSpace α] (x : α) (r : ℝ), IsCompact (Metric.closedBall x r)
· 使用定理 `FiniteDimensional.proper_real`：∀ (E : Type u) [inst : NormedAddCommGroup
 E] [inst_1 : NormedSpace ℝ E] [FiniteDimensional ℝ E], ProperSpace E
-/
theorem u_compact_support : HasCompactSupport (u : E → ℝ) := by
  rw [hasCompactSupport_def, u_support, closure_ball (0 : E) one_ne_zero]
  exact isCompact_closedBall _ _

variable {E}
/-
**ExistsContDiffBumpBase.u_nonneg** 是 Mathlib 中的一个定理，位于命名空间 `ExistsContDiffBumpB
ase`。
形式化陈述：u_nonneg (x : E) : 0 <= u x
参数：x : E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `ExistsContDiffBumpBase.u_exists`：u_exists : exists u : E -> Real, ContDi
ff Real ∞ u ∧ (forall x, u x in Icc (0 : Real) 1) ∧ support u = ball 0 1 ∧ foral
l x, u (-x) = u x
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Classical.choose_spec`：∀ {α : Sort u} {p : α → Prop} (h : ∃ x, p x), p (
Classical.choose h)
-/
theorem u_nonneg (x : E) : 0 ≤ u x :=
  ((Classical.choose_spec (u_exists E)).2.1 x).1
/-
**ExistsContDiffBumpBase.u_le_one** 是 Mathlib 中的一个定理，位于命名空间 `ExistsContDiffBumpB
ase`。
形式化陈述：u_le_one (x : E) : u x <= 1
参数：x : E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `ExistsContDiffBumpBase.u_exists`：u_exists : exists u : E -> Real, ContDi
ff Real ∞ u ∧ (forall x, u x in Icc (0 : Real) 1) ∧ support u = ball 0 1 ∧ foral
l x, u (-x) = u x
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Classical.choose_spec`：∀ {α : Sort u} {p : α → Prop} (h : ∃ x, p x), p (
Classical.choose h)
-/
theorem u_le_one (x : E) : u x ≤ 1 :=
  ((Classical.choose_spec (u_exists E)).2.1 x).2
/-
**ExistsContDiffBumpBase.u_neg** 是 Mathlib 中的一个定理，位于命名空间 `ExistsContDiffBumpBase
`。
形式化陈述：u_neg (x : E) : u (-x) = u x
参数：x : E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `ExistsContDiffBumpBase.u_exists`：u_exists : exists u : E -> Real, ContDi
ff Real ∞ u ∧ (forall x, u x in Icc (0 : Real) 1) ∧ support u = ball 0 1 ∧ foral
l x, u (-x) = u x
· 使用定理 `Classical.choose_spec`：∀ {α : Sort u} {p : α → Prop} (h : ∃ x, p x), p (
Classical.choose h)
-/
theorem u_neg (x : E) : u (-x) = u x :=
  (Classical.choose_spec (u_exists E)).2.2.2 x

variable [MeasurableSpace E] [BorelSpace E]

local notation "μ" => MeasureTheory.Measure.addHaar

variable (E) in
/-
**ExistsContDiffBumpBase.u_int_pos** 是 Mathlib 中的一个定理，位于命名空间 `ExistsContDiffBump
Base`。
形式化陈述：u_int_pos : 0 < ∫ x : E, u x ∂μ
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `locallyCompact_of_proper`：∀ {α : Type u} [inst : PseudoMetricSpace α] [P
roperSpace α], LocallyCompactSpace α
· 使用定理 `FiniteDimensional.proper_real`：∀ (E : Type u) [inst : NormedAddCommGroup
 E] [inst_1 : NormedSpace ℝ E] [FiniteDimensional ℝ E], ProperSpace E
· 使用定理 `MeasureTheory.integral_pos_iff_support_of_nonneg`：integral_pos_iff_suppo
rt_of_nonneg {f : α -> Real} (hf : 0 <= f) (hfi : Integrable f μ) : (0 < ∫ x, f 
x ∂μ) ↔ 0 < μ (Function.support f)
· 使用定理 `ExistsContDiffBumpBase.u_nonneg`：u_nonneg (x : E) : 0 <= u x
· 使用定理 `Continuous.integrable_of_hasCompactSupport`：Continuous.integrable_of_has
CompactSupport (hf : Continuous f) (hcf : HasCompactSupport f) : Integrable f μ
· 使用定理 `BorelSpace.opensMeasurable`：∀ {α : Type u_6} [inst : TopologicalSpace α]
 [inst_1 : MeasurableSpace α] [BorelSpace α], OpensMeasurableSpace α
· 使用定理 `MeasureTheory.Measure.IsAddHaarMeasure.toIsFiniteMeasureOnCompacts`：∀ {G
 : Type u_3} {inst : AddGroup G} {inst_1 : TopologicalSpace G} {inst_2 : Measura
bleSpace G}   {μ : MeasureTheory.Measure G} [self : μ.Is…
· 使用定理 `MeasureTheory.Measure.isAddHaarMeasure_addHaarMeasure`：∀ {G : Type u_1} 
[inst : AddGroup G] [inst_1 : TopologicalSpace G] [inst_2 : IsTopologicalAddGrou
p G]   [inst_3 : MeasurableSpace G] [inst_4…
· 使用定理 `ExistsContDiffBumpBase.u_continuous`：u_continuous : Continuous (u : E ->
 Real)
· 使用定理 `ExistsContDiffBumpBase.u_compact_support`：u_compact_support : HasCompact
Support (u : E -> Real)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ExistsContDiffBumpBase.u_support`：u_support : support (u : E -> Real) = 
ball 0 1
· 使用定理 `Metric.measure_ball_pos`：measure_ball_pos (x : X) {r : Real} (hr : 0 < r
) : 0 < μ (ball x r)
· 使用定理 `MeasureTheory.Measure.IsAddHaarMeasure.toIsOpenPosMeasure`：∀ {G : Type u
_3} {inst : AddGroup G} {inst_1 : TopologicalSpace G} {inst_2 : MeasurableSpace 
G}   {μ : MeasureTheory.Measure G} [self : μ.Is…
· 使用定理 `zero_lt_one`：∀ {α : Type u_1} [inst : Zero α] [inst_1 : One α] [inst_2 :
 PartialOrder α] [ZeroLEOneClass α] [NeZero 1], 0 < 1
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
-/
theorem u_int_pos : 0 < ∫ x : E, u x ∂μ := by
  refine (integral_pos_iff_support_of_nonneg u_nonneg ?_).mpr ?_
  · exact (u_continuous E).integrable_of_hasCompactSupport (u_compact_support E)
  · rw [u_support]; exact measure_ball_pos _ _ zero_lt_one

/-- An auxiliary function to construct partitions of unity on finite-dimensional real vector spaces,
which is smooth, symmetric, with support equal to the ball of radius `D` and integral `1`. -/
/-
**ExistsContDiffBumpBase.w** 是 Mathlib 中的一个定义，位于命名空间 `ExistsContDiffBumpBase`。
形式化陈述：w (D : Real) (x : E) : Real
参数：D : Real；x : E。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An auxiliary function to construct partitions of unity on finite-dimensional rea
l vector spaces,
which is smooth, symmetric, with support equal to the ball of radius `D` and int
egral `1`.
-/
def w (D : ℝ) (x : E) : ℝ :=
  ((∫ x : E, u x ∂μ) * |D| ^ finrank ℝ E)⁻¹ • u (D⁻¹ • x)
/-
**ExistsContDiffBumpBase.w_def** 是 Mathlib 中的一个定理，位于命名空间 `ExistsContDiffBumpBase
`。
形式化陈述：w_def (D : Real) : (w D : E -> Real) = fun x => ((∫ x : E, u x ∂μ) * |D| ^
 finrank Real E)⁻¹ • u (D⁻¹ • x)
参数：D : Real。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `locallyCompact_of_proper`：∀ {α : Type u} [inst : PseudoMetricSpace α] [P
roperSpace α], LocallyCompactSpace α
· 使用定理 `FiniteDimensional.proper_real`：∀ (E : Type u) [inst : NormedAddCommGroup
 E] [inst_1 : NormedSpace ℝ E] [FiniteDimensional ℝ E], ProperSpace E
-/
theorem w_def (D : ℝ) :
    (w D : E → ℝ) = fun x => ((∫ x : E, u x ∂μ) * |D| ^ finrank ℝ E)⁻¹ • u (D⁻¹ • x) := by
  ext1 x; rfl
/-
**ExistsContDiffBumpBase.w_nonneg** 是 Mathlib 中的一个定理，位于命名空间 `ExistsContDiffBumpB
ase`。
形式化陈述：w_nonneg (D : Real) (x : E) : 0 <= w D x
参数：D : Real；x : E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `mul_nonneg`：∀ {α : Type u_1} [inst : MulZeroClass α] {a b : α} [inst_1 :
 Preorder α] [PosMulMono α], 0 ≤ a → 0 ≤ b → 0 ≤ a * b
· 使用定理 `IsOrderedRing.toPosMulMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], PosMulMono R
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `inv_nonneg`：∀ {G₀ : Type u_3} [inst : GroupWithZero G₀] [inst_1 : Partia
lOrder G₀] [PosMulReflectLT G₀] {a : G₀}, 0 ≤ a⁻¹ ↔ 0 ≤ a
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `locallyCompact_of_proper`：∀ {α : Type u} [inst : PseudoMetricSpace α] [P
roperSpace α], LocallyCompactSpace α
· 使用定理 `FiniteDimensional.proper_real`：∀ (E : Type u) [inst : NormedAddCommGroup
 E] [inst_1 : NormedSpace ℝ E] [FiniteDimensional ℝ E], ProperSpace E
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `ExistsContDiffBumpBase.u_int_pos`：u_int_pos : 0 < ∫ x : E, u x ∂μ
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.cast_zero`：cast_zero : ((0 : Nat) : R) = 0
· 使用定理 `pow_nonneg`：∀ {M₀ : Type u_2} [inst : MonoidWithZero M₀] [inst_1 : Preor
der M₀] {a : M₀} [ZeroLEOneClass M₀] [PosMulMono M₀],   0 ≤ a → ∀ (n : ℕ), 0 ≤ a
…
· 使用定理 `abs_nonneg`：∀ {α : Type u_1} [inst : Lattice α] [inst_1 : AddGroup α] [A
ddLeftMono α] [AddRightMono α] (a : α), 0 ≤ |a|
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `ExistsContDiffBumpBase.u_nonneg`：u_nonneg (x : E) : 0 <= u x
-/
theorem w_nonneg (D : ℝ) (x : E) : 0 ≤ w D x := by
  apply mul_nonneg _ (u_nonneg _)
  apply inv_nonneg.2
  apply mul_nonneg (u_int_pos E).le
  norm_cast
  apply pow_nonneg (abs_nonneg D)
/-
**ExistsContDiffBumpBase.w_mul_** 是 Mathlib 中的一个定理，位于命名空间 `ExistsContDiffBumpBas
e`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem w_mul_φ_nonneg (D : ℝ) (x y : E) : 0 ≤ w D y * φ (x - y) :=
  mul_nonneg (w_nonneg D y) (indicator_nonneg (by simp only [zero_le_one, imp_true_iff]) _)

variable (E)

-- see https://github.com/leanprover-community/mathlib4/issues/29041
set_option linter.unusedSimpArgs false in
/-
**ExistsContDiffBumpBase.w_integral** 是 Mathlib 中的一个定理，位于命名空间 `ExistsContDiffBum
pBase`。
形式化陈述：w_integral {D : Real} (Dpos : 0 < D) : ∫ x : E, w D x ∂μ = 1
参数：Dpos : 0 < D。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `locallyCompact_of_proper`：∀ {α : Type u} [inst : PseudoMetricSpace α] [P
roperSpace α], LocallyCompactSpace α
· 使用定理 `FiniteDimensional.proper_real`：∀ (E : Type u) [inst : NormedAddCommGroup
 E] [inst_1 : NormedSpace ℝ E] [FiniteDimensional ℝ E], ProperSpace E
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.integral_smul`：integral_smul [Module 𝕜 G] [NormSMulClass 𝕜
 G] [SMulCommClass Real 𝕜 G] (c : 𝕜) (f : α -> G) : ∫ a, c • f a ∂μ = c • ∫ a, f
 a ∂μ
· 使用定理 `NormedSpace.toNormSMulClass`：∀ {𝕜 : Type u_1} {E : Type u_3} [inst : Nor
medField 𝕜] [inst_1 : SeminormedAddCommGroup E] [inst_2 : NormedSpace 𝕜 E],   No
rmSMulClass 𝕜 E
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `MeasureTheory.Measure.integral_comp_inv_smul_of_nonneg`：integral_comp_in
v_smul_of_nonneg (f : E -> F) {R : Real} (hR : 0 <= R) : ∫ x, f (R⁻¹ • x) ∂μ = R
 ^ finrank Real E • ∫ x, f x ∂μ
· 使用定理 `MeasureTheory.Measure.isAddHaarMeasure_addHaarMeasure`：∀ {G : Type u_1} 
[inst : AddGroup G] [inst_1 : TopologicalSpace G] [inst_2 : IsTopologicalAddGrou
p G]   [inst_3 : MeasurableSpace G] [inst_4…
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `abs_of_nonneg`：∀ {α : Type u_1} [inst : Lattice α] [inst_1 : AddGroup α]
 {a : α} [AddLeftMono α], 0 ≤ a → |a| = a
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `mul_inv_rev`：mul_inv_rev (a b : G) : (a * b)⁻¹ = b⁻¹ * a⁻¹
· 使用定理 `Mathlib.Tactic.FieldSimp.eq_eq_cancel_eq`：eq_eq_cancel_eq {M : Type*} [M
onoidWithZero M] [IsLeftCancelMulZero M] {e₁ e₂ f₁ f₂ L : M} (H₁ : e₁ = L * f₁) 
(H₂ : e₂ = L * f₂) (HL : L != …
· 使用定理 `IsCancelMulZero.toIsLeftCancelMulZero`：∀ {M₀ : Type u} {inst : Mul M₀} {
inst_1 : Zero M₀} [self : IsCancelMulZero M₀], IsLeftCancelMulZero M₀
· 使用定理 `instIsCancelMulZero`：∀ {G₀ : Type u_2} [inst : GroupWithZero G₀], IsCanc
elMulZero G₀
· 使用定理 `Mathlib.Tactic.FieldSimp.eq_mul_of_eq_eq_eq_mul`：eq_mul_of_eq_eq_eq_mul 
{M : Type*} [Mul M] {a b c D e f : M} (h₁ : a = b) (h₂ : b = c) (h₃ : c = D * e)
 (h₄ : e = f) : a = D * f
· 使用定理 `congr_arg₂`：∀ {α : Sort u_1} {β : Sort u_2} {γ : Sort u_3} (f : α → β → 
γ) {x x' : α} {y y' : β}, x = x' → y = y' → f x y = f x' y'
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `Mathlib.Tactic.FieldSimp.NF.mul_eq_eval`：mul_eq_eval [GroupWithZero M] {
l₁ l₂ l : NF M} {x₁ x₂ : M} (hx₁ : x₁ = l₁.eval) (hx₂ : x₂ = l₂.eval) (h : l₁.ev
al * l₂.eval = l.eval) : x₁ *…
· 使用定理 `Mathlib.Tactic.FieldSimp.NF.inv_eq_eval`：inv_eq_eval [CommGroupWithZero 
M] {l : NF M} {x : M} (h : x = l.eval) : x⁻¹ = (l⁻¹).eval
· 使用定理 `Mathlib.Tactic.FieldSimp.NF.atom_eq_eval`：atom_eq_eval [GroupWithZero M]
 (x : M) : x = NF.eval [(1, x)]
· 使用定理 `Mathlib.Tactic.FieldSimp.NF.mul_eq_eval₃`：mul_eq_eval₃ [CommGroupWithZer
o M] {a₁ : Int × M} (a₂ : Int × M) {l₁ l₂ l : NF M} (h : (a₁ ::ᵣ l₁).eval * l₂.e
val = l.eval) : (a₁ ::ᵣ l₁).ev…
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `Mathlib.Tactic.FieldSimp.NF.mul_eq_eval₁`：mul_eq_eval₁ [CommGroupWithZer
o M] (a₁ : Int × M) {a₂ : Int × M} {l₁ l₂ l : NF M} (h : l₁.eval * (a₂ ::ᵣ l₂).e
val = l.eval) : (a₁ ::ᵣ l₁).ev…
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
（共 49 条，此处仅展示前 30 条）
-/
theorem w_integral {D : ℝ} (Dpos : 0 < D) : ∫ x : E, w D x ∂μ = 1 := by
  simp_rw [w, integral_smul]
  rw [integral_comp_inv_smul_of_nonneg μ (u : E → ℝ) Dpos.le, abs_of_nonneg Dpos.le, mul_comm]
  simp [field, (u_int_pos E).ne']
/-
**ExistsContDiffBumpBase.w_support** 是 Mathlib 中的一个定理，位于命名空间 `ExistsContDiffBump
Base`。
形式化陈述：w_support {D : Real} (Dpos : 0 < D) : support (w D : E -> Real) = ball 0 D
参数：Dpos : 0 < D。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `smul_unitBall`：smul_unitBall {c : 𝕜} (hc : c != 0) : c • ball (0 : E) (1
 : Real) = ball (0 : E) ‖c‖
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `Real.norm_of_nonneg`：norm_of_nonneg (hr : 0 <= r) : ‖r‖ = r
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.cast_zero`：cast_zero : ((0 : Nat) : R) = 0
· 使用引理 `pow_ne_zero`：pow_ne_zero (n : Nat) (h : a != 0) : a ^ n != 0
· 使用定理 `isReduced_of_noZeroDivisors`：∀ {M₀ : Type u_1} [inst : MonoidWithZero M₀
] [NoZeroDivisors M₀], IsReduced M₀
· 使用定理 `NormedDivisionRing.toNormMulClass`：∀ {α : Type u_2} [inst : NormedDivisi
onRing α], NormMulClass α
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `locallyCompact_of_proper`：∀ {α : Type u} [inst : PseudoMetricSpace α] [P
roperSpace α], LocallyCompactSpace α
· 使用定理 `FiniteDimensional.proper_real`：∀ (E : Type u) [inst : NormedAddCommGroup
 E] [inst_1 : NormedSpace ℝ E] [FiniteDimensional ℝ E], ProperSpace E
· 使用定理 `ExistsContDiffBumpBase.w_def`：w_def (D : Real) : (w D : E -> Real) = fun
 x => ((∫ x : E, u x ∂μ) * |D| ^ finrank Real E)⁻¹ • u (D⁻¹ • x)
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `abs_of_nonneg`：∀ {α : Type u_1} [inst : Lattice α] [inst_1 : AddGroup α]
 {a : α} [AddLeftMono α], 0 ≤ a → |a| = a
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `Function.support_mul`：∀ {ι : Type u_1} {M₀ : Type u_4} [inst : MulZeroCl
ass M₀] [NoZeroDivisors M₀] (f g : ι → M₀),   (Function.support fun x => f x * g
 x) = Func…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Function.support_inv`：∀ {ι : Type u_1} {G₀ : Type u_3} [inst : GroupWith
Zero G₀] (f : ι → G₀),   (Function.support fun a => (f a)⁻¹) = Function.support 
f
· 使用定理 `Function.support_const`：∀ {ι : Type u_1} {M : Type u_3} [inst : Zero M] 
{c : M}, c ≠ 0 → (Function.support fun x => c) = Set.univ
· 使用定理 `ExistsContDiffBumpBase.u_int_pos`：u_int_pos : 0 < ∫ x : E, u x ∂μ
· 使用定理 `Set.univ_inter`：univ_inter (a : Set α) : univ inter a = a
· 使用定理 `support_comp_inv_smul₀`：support_comp_inv_smul₀ [Zero γ] {c : α} (hc : c 
!= 0) (f : β -> γ) : (support fun x => f (c⁻¹ • x)) = c • support f
· 使用定理 `ExistsContDiffBumpBase.u_support`：u_support : support (u : E -> Real) = 
ball 0 1
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem w_support {D : ℝ} (Dpos : 0 < D) : support (w D : E → ℝ) = ball 0 D := by
  have B : D • ball (0 : E) 1 = ball 0 D := by
    rw [smul_unitBall Dpos.ne', Real.norm_of_nonneg Dpos.le]
  have C : D ^ finrank ℝ E ≠ 0 := by
    norm_cast
    exact pow_ne_zero _ Dpos.ne'
  simp only [w_def, smul_eq_mul, support_mul, support_inv, univ_inter,
    support_comp_inv_smul₀ Dpos.ne', u_support, B, support_const (u_int_pos E).ne', support_const C,
    abs_of_nonneg Dpos.le]
/-
**ExistsContDiffBumpBase.w_compact_support** 是 Mathlib 中的一个定理，位于命名空间 `ExistsCont
DiffBumpBase`。
形式化陈述：w_compact_support {D : Real} (Dpos : 0 < D) : HasCompactSupport (w D : E -
> Real)
参数：Dpos : 0 < D。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `hasCompactSupport_def`：∀ {α : Type u_2} {β : Type u_4} [inst : Topologic
alSpace α] [inst_1 : Zero β] {f : α → β},   HasCompactSupport f ↔ IsCompact (clo
sure (Funct…
· 使用定理 `ExistsContDiffBumpBase.w_support`：w_support {D : Real} (Dpos : 0 < D) : 
support (w D : E -> Real) = ball 0 D
· 使用定理 `closure_ball`：closure_ball (x : E) {r : Real} (hr : r != 0) : closure (b
all x r) = closedBall x r
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `ProperSpace.isCompact_closedBall`：∀ {α : Type u} {inst : PseudoMetricSpa
ce α} [self : ProperSpace α] (x : α) (r : ℝ), IsCompact (Metric.closedBall x r)
· 使用定理 `FiniteDimensional.proper_real`：∀ (E : Type u) [inst : NormedAddCommGroup
 E] [inst_1 : NormedSpace ℝ E] [FiniteDimensional ℝ E], ProperSpace E
-/
theorem w_compact_support {D : ℝ} (Dpos : 0 < D) : HasCompactSupport (w D : E → ℝ) := by
  rw [hasCompactSupport_def, w_support E Dpos, closure_ball (0 : E) Dpos.ne']
  exact isCompact_closedBall _ _

variable {E}

/-- An auxiliary function to construct partitions of unity on finite-dimensional real vector spaces.
It is the convolution between a smooth function of integral `1` supported in the ball of radius `D`,
with the indicator function of the closed unit ball. Therefore, it is smooth, equal to `1` on the
ball of radius `1 - D`, with support equal to the ball of radius `1 + D`. -/
/-
**ExistsContDiffBumpBase.y** 是 Mathlib 中的一个定义，位于命名空间 `ExistsContDiffBumpBase`。
形式化陈述：y (D : Real) : E -> Real
参数：D : Real。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An auxiliary function to construct partitions of unity on finite-dimensional rea
l vector spaces.
It is the convolution between a smooth function of integral `1` supported in the
 ball of radius `D`,
with the indicator function of the closed unit ball. Therefore, it is smooth, eq
ual to `1` on the
ball of radius `1 - D`, with support equal to the ball of radius `1 + D`.
-/
def y (D : ℝ) : E → ℝ :=
  w D ⋆[lsmul ℝ ℝ, μ] φ
/-
**ExistsContDiffBumpBase.y_neg** 是 Mathlib 中的一个定理，位于命名空间 `ExistsContDiffBumpBase
`。
形式化陈述：y_neg (D : Real) (x : E) : y D (-x) = y D x
参数：D : Real；x : E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.convolution_neg_of_neg_eq`：convolution_neg_of_neg_eq (h1 :
 forallᵐ x ∂μ, f (-x) = f x) (h2 : forallᵐ x ∂μ, g (-x) = g x) : (f ⋆[L, μ] g) (
-x) = (f ⋆[L, μ] g) x
· 使用定理 `MeasureTheory.Measure.isAddLeftInvariant_addHaarMeasure`：∀ {G : Type u_1
} [inst : AddGroup G] [inst_1 : TopologicalSpace G] [inst_2 : IsTopologicalAddGr
oup G]   [inst_3 : MeasurableSpace G] [inst_4…
· 使用定理 `MeasureTheory.Measure.IsAddHaarMeasure.isNegInvariant_of_innerRegular`：∀
 {G : Type u_1} [inst : AddCommGroup G] [inst_1 : TopologicalSpace G] [IsTopolog
icalAddGroup G]   [inst_3 : MeasurableSpace G] [BorelSpace …
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `MeasureTheory.Measure.isAddHaarMeasure_addHaarMeasure`：∀ {G : Type u_1} 
[inst : AddGroup G] [inst_1 : TopologicalSpace G] [inst_2 : IsTopologicalAddGrou
p G]   [inst_3 : MeasurableSpace G] [inst_4…
· 使用定理 `locallyCompact_of_proper`：∀ {α : Type u} [inst : PseudoMetricSpace α] [P
roperSpace α], LocallyCompactSpace α
· 使用定理 `FiniteDimensional.proper_real`：∀ (E : Type u) [inst : NormedAddCommGroup
 E] [inst_1 : NormedSpace ℝ E] [FiniteDimensional ℝ E], ProperSpace E
· 使用定理 `MeasureTheory.Measure.instInnerRegularOfPseudoMetrizableSpaceOfSigmaComp
actSpaceOfBorelSpaceOfSigmaFinite`：∀ {X : Type u_3} [inst : TopologicalSpace X] 
[TopologicalSpace.PseudoMetrizableSpace X] [SigmaCompactSpace X]   [inst_3 : Mea
surableSpace X]…
· 使用定理 `PseudoEMetricSpace.pseudoMetrizableSpace`：∀ {α : Type u_2} [inst : Pseud
oEMetricSpace α], TopologicalSpace.PseudoMetrizableSpace α
· 使用定理 `SeparableWeaklyLocallyCompactAddGroup.sigmaCompactSpace`：∀ {G : Type w} 
[inst : TopologicalSpace G] [inst_1 : AddGroup G] [IsTopologicalAddGroup G]   [T
opologicalSpace.SeparableSpace G] [WeaklyLoca…
· 使用定理 `TopologicalSpace.SecondCountableTopology.to_separableSpace`：∀ {α : Type 
u} [t : TopologicalSpace α] [SecondCountableTopology α], TopologicalSpace.Separa
bleSpace α
· 使用定理 `secondCountable_of_proper`：∀ {α : Type u} [inst : PseudoMetricSpace α] [
ProperSpace α], SecondCountableTopology α
· 使用定理 `instWeaklyLocallyCompactSpaceOfLocallyCompactSpace`：∀ {X : Type u_1} [in
st : TopologicalSpace X] [LocallyCompactSpace X], WeaklyLocallyCompactSpace X
· 使用定理 `MeasureTheory.Measure.sigmaFinite_addHaarMeasure`：∀ {G : Type u_1} [inst
 : AddGroup G] [inst_1 : TopologicalSpace G] [inst_2 : IsTopologicalAddGroup G] 
  [inst_3 : MeasurableSpace G] [inst_4…
· 使用定理 `ContinuousNeg.measurableNeg`：∀ {γ : Type u_3} [inst : TopologicalSpace γ
] [inst_1 : MeasurableSpace γ] [BorelSpace γ] [inst_3 : Neg γ]   [ContinuousNeg 
γ], MeasurableNeg…
· 使用定理 `IsTopologicalAddGroup.toContinuousNeg`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousNeg 
G
· 使用定理 `ContinuousAdd.measurableAdd`：∀ {γ : Type u_3} [inst : TopologicalSpace γ
] [inst_1 : MeasurableSpace γ] [BorelSpace γ] [inst_3 : Add γ]   [SeparatelyCont
inuousAdd γ], Mea…
· 使用定理 `instSeparatelyContinuousAddOfContinuousAdd`：∀ {M : Type u_1} [inst : Top
ologicalSpace M] [inst_1 : Add M] [ContinuousAdd M], SeparatelyContinuousAdd M
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `ExistsContDiffBumpBase.w_def`：w_def (D : Real) : (w D : E -> Real) = fun
 x => ((∫ x : E, u x ∂μ) * |D| ^ finrank Real E)⁻¹ • u (D⁻¹ • x)
· 使用定理 `mul_inv_rev`：mul_inv_rev (a b : G) : (a * b)⁻¹ = b⁻¹ * a⁻¹
· 使用定理 `ExistsContDiffBumpBase.u.congr_simp`：∀ {E : Type u_1} [inst : NormedAddC
ommGroup E] [inst_1 : NormedSpace ℝ E] [inst_2 : FiniteDimensional ℝ E] (x x_1 :
 E),   x = x_1 → ExistsCo…
· 使用定理 `smul_neg`：smul_neg (r : M) (x : A) : r • -x = -(r • x)
（共 36 条，此处仅展示前 30 条）
-/
theorem y_neg (D : ℝ) (x : E) : y D (-x) = y D x := by
  apply convolution_neg_of_neg_eq
  · filter_upwards with x
    simp only [w_def, mul_inv_rev, smul_neg, u_neg, smul_eq_mul]
  · filter_upwards with x
    simp only [φ, indicator, mem_closedBall, dist_zero_right, norm_neg]
/-
**ExistsContDiffBumpBase.y_eq_one_of_mem_closedBall** 是 Mathlib 中的一个定理，位于命名空间 `E
xistsContDiffBumpBase`。
形式化陈述：y_eq_one_of_mem_closedBall {D : Real} {x : E} (Dpos : 0 < D) (hx : x in cl
osedBall (0 : E) (1 - D)) : y D x = 1
参数：Dpos : 0 < D；hx : x in closedBall (0 : E) (1 - D)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Metric.ball_subset_ball'`：ball_subset_ball' (h : ε₁ + dist x y <= ε₂) : 
ball x ε₁ subseteq ball y ε₂
· 使用引理 `le_of_not_gt`：le_of_not_gt (h : ¬b < a) : a <= b
· 使用定理 `Mathlib.Tactic.Linarith.lt_irrefl`：lt_irrefl {α : Type u} [Preorder α] {
a : α} : ¬a < a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Mathlib.Tactic.Ring.of_eq`：∀ {α : Sort u_2} {a b c : α}, a = c → b = c →
 a = b
· 使用定理 `Mathlib.Tactic.Ring.Common.add_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' + b' = c → a + b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.sub_congr`：∀ {R : Type u_2} [inst : CommRing 
R] {a a' b b' c : R}, a = a' → b = b' → a' - b' = c → a - b = c
· 使用定理 `Mathlib.Tactic.Ring.cast_pos`：∀ {R : Type u_1} [inst : CommSemiring R] {
a : R} {n : ℕ}, Mathlib.Meta.NormNum.IsNat a n → a = n.rawCast + 0
· 使用定理 `Mathlib.Meta.NormNum.isNat_ofNat`：isNat_ofNat (α : Type u) [AddMonoidWit
hOne α] {a : α} {n : Nat} (h : n = a) : IsNat a n
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `Mathlib.Tactic.Ring.Common.atom_pf`：∀ {R : Type u_1} [inst : CommSemirin
g R] {b : R} (a : R) {e : ℕ},   Nat.rawCast 1 = e → a ^ e * Nat.rawCast 1 = b → 
a = b + 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_add_lt`：∀ {R : Type u_1} [inst : CommS
emiring R] {a₂ b c : R} (a₁ : R), a₂ + b = c → a₁ + a₂ + b = a₁ + c
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_zero_add`：∀ {R : Type u_1} [inst : Com
mSemiring R] (b : R), 0 + b = b
· 使用定理 `Mathlib.Tactic.Ring.Common.sub_pf`：∀ {R : Type u_2} [inst : CommRing R] 
{a b c d : R}, -b = c → a + c = d → a - b = d
· 使用定理 `Mathlib.Tactic.Ring.Common.neg_add`：∀ {R : Type u_2} [inst : CommRing R]
 {a₁ a₂ b₁ b₂ : R}, -a₁ = b₁ → -a₂ = b₂ → -(a₁ + a₂) = b₁ + b₂
· 使用定理 `Mathlib.Tactic.Ring.Common.neg_mul`：∀ {R : Type u_2} [inst : CommRing R]
 (a₁ : R) (a₂ : ℕ) {a₃ b : R}, -a₃ = b → -(a₁ ^ a₂ * a₃) = a₁ ^ a₂ * b
· 使用定理 `Mathlib.Meta.NormNum.IsInt.to_raw_eq`：∀ {α : Type u} {a : α} {n : ℤ} [in
st : Ring α], Mathlib.Meta.NormNum.IsInt a n → a = n.rawCast
· 使用定理 `Mathlib.Meta.NormNum.isInt_neg`：∀ {α : Type u_1} [inst : Ring α] {f : α 
→ α} {a : α} {a' b : ℤ},   f = Neg.neg → Mathlib.Meta.NormNum.IsInt a a' → a'.ne
g = b → Mathlib.Meta…
· 使用定理 `Mathlib.Meta.NormNum.IsNat.to_isInt`：∀ {α : Type u_1} [inst : Ring α] {a
 : α} {n : ℕ},   Mathlib.Meta.NormNum.IsNat a n → Mathlib.Meta.NormNum.IsInt a (
Int.ofNat n)
· 使用定理 `Mathlib.Meta.NormNum.IsNat.of_raw`：∀ (α : Type u_1) [inst : AddMonoidWit
hOne α] (n : ℕ), Mathlib.Meta.NormNum.IsNat n.rawCast n
· 使用定理 `Mathlib.Tactic.Ring.Common.neg_zero`：∀ {R : Type u_2} [inst : CommRing R
], -0 = 0
· 使用定理 `Mathlib.Meta.NormNum.IsNat.to_raw_eq`：∀ {α : Type u} {a : α} {n : ℕ} [in
st : AddMonoidWithOne α], Mathlib.Meta.NormNum.IsNat a n → a = n.rawCast
· 使用定理 `Mathlib.Meta.NormNum.IsInt.to_isNat`：∀ {α : Type u_1} [inst : Ring α] {a
 : α} {n : ℕ},   Mathlib.Meta.NormNum.IsInt a (Int.ofNat n) → Mathlib.Meta.NormN
um.IsNat a n
· 使用定理 `Mathlib.Meta.NormNum.IsInt.of_raw`：∀ (α : Type u_1) [inst : Ring α] (n :
 ℤ), Mathlib.Meta.NormNum.IsInt n.rawCast n
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_add_gt`：∀ {R : Type u_1} [inst : CommS
emiring R] {a b₂ c : R} (b₁ : R), a + b₂ = c → a + (b₁ + b₂) = b₁ + c
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_add_zero`：∀ {R : Type u_1} [inst : Com
mSemiring R] (a : R), a + 0 = a
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_add_overlap_zero`：∀ {R : Type u_1} [in
st : CommSemiring R] {a₁ a₂ b₁ b₂ c : R},   Mathlib.Meta.NormNum.IsNat (a₁ + b₁)
 0 → a₂ + b₂ = c → a₁ + a₂ + (b₁ + b₂) =…
· 使用定理 `Mathlib.Meta.NormNum.isInt_add`：∀ {α : Type u_1} [inst : Ring α] {f : α 
→ α → α} {a b : α} {a' b' c : ℤ},   f = HAdd.hAdd →     Mathlib.Meta.NormNum.IsI
nt a a' →       Math…
· 使用定理 `Mathlib.Tactic.Ring.Common.add_overlap_pf_zero`：∀ {R : Type u_1} [inst :
 CommSemiring R] {a b : R} (x : R) (e : ℕ),   Mathlib.Meta.NormNum.IsNat (a + b)
 0 → Mathlib.Meta.NormNum.IsNat (x ^…
（共 60 条，此处仅展示前 30 条）
-/
theorem y_eq_one_of_mem_closedBall {D : ℝ} {x : E} (Dpos : 0 < D)
    (hx : x ∈ closedBall (0 : E) (1 - D)) : y D x = 1 := by
  change (w D ⋆[lsmul ℝ ℝ, μ] φ) x = 1
  have B : ∀ y : E, y ∈ ball x D → φ y = 1 := by
    have C : ball x D ⊆ ball 0 1 := by
      apply ball_subset_ball'
      simp only [mem_closedBall] at hx
      linarith only [hx]
    intro y hy
    simp only [φ, indicator, mem_closedBall, ite_eq_left_iff, not_le, zero_ne_one]
    intro h'y
    linarith only [mem_ball.1 (C hy), h'y]
  have Bx : φ x = 1 := B _ (mem_ball_self Dpos)
  have B' : ∀ y, y ∈ ball x D → φ y = φ x := by rw [Bx]; exact B
  rw [convolution_eq_right' _ (le_of_eq (w_support E Dpos)) B']
  simp only [lsmul_apply, smul_eq_mul, integral_mul_const, w_integral E Dpos, Bx,
    one_mul]
/-
**ExistsContDiffBumpBase.y_eq_zero_of_notMem_ball** 是 Mathlib 中的一个定理，位于命名空间 `Exi
stsContDiffBumpBase`。
形式化陈述：y_eq_zero_of_notMem_ball {D : Real} {x : E} (Dpos : 0 < D) (hx : x ∉ ball 
(0 : E) (1 + D)) : y D x = 0
参数：Dpos : 0 < D；hx : x ∉ ball (0 : E) (1 + D)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `Metric.ball_subset_ball'`：ball_subset_ball' (h : ε₁ + dist x y <= ε₂) : 
ball x ε₁ subseteq ball y ε₂
· 使用引理 `le_of_not_gt`：le_of_not_gt (h : ¬b < a) : a <= b
· 使用定理 `Mathlib.Tactic.Linarith.lt_irrefl`：lt_irrefl {α : Type u} [Preorder α] {
a : α} : ¬a < a
· 使用定理 `Mathlib.Tactic.Ring.of_eq`：∀ {α : Sort u_2} {a b c : α}, a = c → b = c →
 a = b
· 使用定理 `Mathlib.Tactic.Ring.Common.add_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' + b' = c → a + b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.sub_congr`：∀ {R : Type u_2} [inst : CommRing 
R] {a a' b b' c : R}, a = a' → b = b' → a' - b' = c → a - b = c
· 使用定理 `Mathlib.Tactic.Ring.cast_pos`：∀ {R : Type u_1} [inst : CommSemiring R] {
a : R} {n : ℕ}, Mathlib.Meta.NormNum.IsNat a n → a = n.rawCast + 0
· 使用定理 `Mathlib.Meta.NormNum.isNat_ofNat`：isNat_ofNat (α : Type u) [AddMonoidWit
hOne α] {a : α} {n : Nat} (h : n = a) : IsNat a n
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `Mathlib.Tactic.Ring.Common.atom_pf`：∀ {R : Type u_1} [inst : CommSemirin
g R] {b : R} (a : R) {e : ℕ},   Nat.rawCast 1 = e → a ^ e * Nat.rawCast 1 = b → 
a = b + 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_add_lt`：∀ {R : Type u_1} [inst : CommS
emiring R] {a₂ b c : R} (a₁ : R), a₂ + b = c → a₁ + a₂ + b = a₁ + c
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_zero_add`：∀ {R : Type u_1} [inst : Com
mSemiring R] (b : R), 0 + b = b
· 使用定理 `Mathlib.Tactic.Ring.Common.sub_pf`：∀ {R : Type u_2} [inst : CommRing R] 
{a b c d : R}, -b = c → a + c = d → a - b = d
· 使用定理 `Mathlib.Tactic.Ring.Common.neg_add`：∀ {R : Type u_2} [inst : CommRing R]
 {a₁ a₂ b₁ b₂ : R}, -a₁ = b₁ → -a₂ = b₂ → -(a₁ + a₂) = b₁ + b₂
· 使用定理 `Mathlib.Tactic.Ring.Common.neg_mul`：∀ {R : Type u_2} [inst : CommRing R]
 (a₁ : R) (a₂ : ℕ) {a₃ b : R}, -a₃ = b → -(a₁ ^ a₂ * a₃) = a₁ ^ a₂ * b
· 使用定理 `Mathlib.Meta.NormNum.IsInt.to_raw_eq`：∀ {α : Type u} {a : α} {n : ℤ} [in
st : Ring α], Mathlib.Meta.NormNum.IsInt a n → a = n.rawCast
· 使用定理 `Mathlib.Meta.NormNum.isInt_neg`：∀ {α : Type u_1} [inst : Ring α] {f : α 
→ α} {a : α} {a' b : ℤ},   f = Neg.neg → Mathlib.Meta.NormNum.IsInt a a' → a'.ne
g = b → Mathlib.Meta…
· 使用定理 `Mathlib.Meta.NormNum.IsNat.to_isInt`：∀ {α : Type u_1} [inst : Ring α] {a
 : α} {n : ℕ},   Mathlib.Meta.NormNum.IsNat a n → Mathlib.Meta.NormNum.IsInt a (
Int.ofNat n)
· 使用定理 `Mathlib.Meta.NormNum.IsNat.of_raw`：∀ (α : Type u_1) [inst : AddMonoidWit
hOne α] (n : ℕ), Mathlib.Meta.NormNum.IsNat n.rawCast n
· 使用定理 `Mathlib.Tactic.Ring.Common.neg_zero`：∀ {R : Type u_2} [inst : CommRing R
], -0 = 0
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_add_overlap_zero`：∀ {R : Type u_1} [in
st : CommSemiring R] {a₁ a₂ b₁ b₂ c : R},   Mathlib.Meta.NormNum.IsNat (a₁ + b₁)
 0 → a₂ + b₂ = c → a₁ + a₂ + (b₁ + b₂) =…
· 使用定理 `Mathlib.Tactic.Ring.Common.add_overlap_pf_zero`：∀ {R : Type u_1} [inst :
 CommSemiring R] {a b : R} (x : R) (e : ℕ),   Mathlib.Meta.NormNum.IsNat (a + b)
 0 → Mathlib.Meta.NormNum.IsNat (x ^…
· 使用定理 `Mathlib.Meta.NormNum.IsInt.to_isNat`：∀ {α : Type u_1} [inst : Ring α] {a
 : α} {n : ℕ},   Mathlib.Meta.NormNum.IsInt a (Int.ofNat n) → Mathlib.Meta.NormN
um.IsNat a n
（共 58 条，此处仅展示前 30 条）
-/
theorem y_eq_zero_of_notMem_ball {D : ℝ} {x : E} (Dpos : 0 < D) (hx : x ∉ ball (0 : E) (1 + D)) :
    y D x = 0 := by
  change (w D ⋆[lsmul ℝ ℝ, μ] φ) x = 0
  have B : ∀ y, y ∈ ball x D → φ y = 0 := by
    intro y hy
    simp only [φ, indicator, mem_closedBall_zero_iff, ite_eq_right_iff, one_ne_zero]
    intro h'y
    have C : ball y D ⊆ ball 0 (1 + D) := by
      apply ball_subset_ball'
      rw [← dist_zero_right] at h'y
      linarith only [h'y]
    exact hx (C (mem_ball_comm.1 hy))
  have Bx : φ x = 0 := B _ (mem_ball_self Dpos)
  have B' : ∀ y, y ∈ ball x D → φ y = φ x := by rw [Bx]; exact B
  rw [convolution_eq_right' _ (le_of_eq (w_support E Dpos)) B']
  simp only [lsmul_apply, smul_eq_mul, Bx, mul_zero, integral_const]
/-
**ExistsContDiffBumpBase.y_nonneg** 是 Mathlib 中的一个定理，位于命名空间 `ExistsContDiffBumpB
ase`。
形式化陈述：y_nonneg (D : Real) (x : E) : 0 <= y D x
参数：D : Real；x : E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `MeasureTheory.integral_nonneg`：integral_nonneg {f : α -> E} (hf : 0 <= f
) : 0 <= ∫ x, f x ∂μ
· 使用定理 `IsStrictOrderedModule.toIsOrderedModule`：∀ {α : Type u_1} {β : Type u_2}
 [inst : Zero α] [inst_1 : Zero β] [inst_2 : SMulWithZero α β] [inst_3 : Partial
Order α]   [inst_4 : PartialO…
· 使用定理 `IsStrictOrderedRing.toIsStrictOrderedModule`：∀ {α : Type u_1} [inst : Se
miring α] [inst_1 : PartialOrder α] [IsStrictOrderedRing α], IsStrictOrderedModu
le α α
· 使用定理 `instClosedIciTopology`：∀ {α : Type u} [inst : TopologicalSpace α] [inst_
1 : Preorder α] [t : OrderClosedTopology α], ClosedIciTopology α
· 使用定理 `HasSolidNorm.orderClosedTopology`：∀ {E : Type u_2} [inst : NormedAddComm
Group E] [inst_1 : Lattice E] [HasSolidNorm E] [IsOrderedAddMonoid E],   OrderCl
osedTopology E
· 使用定理 `instHasSolidNormReal`：HasSolidNorm ℝ
· 使用定理 `ExistsContDiffBumpBase.w_mul_φ_nonneg`：w_mul_φ_nonneg (D : Real) (x y : 
E) : 0 <= w D y * φ (x - y)
-/
theorem y_nonneg (D : ℝ) (x : E) : 0 ≤ y D x :=
  integral_nonneg (w_mul_φ_nonneg D x)
/-
**ExistsContDiffBumpBase.y_le_one** 是 Mathlib 中的一个定理，位于命名空间 `ExistsContDiffBumpB
ase`。
形式化陈述：y_le_one {D : Real} (x : E) (Dpos : 0 < D) : y D x <= 1
参数：x : E；Dpos : 0 < D。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `locallyCompact_of_proper`：∀ {α : Type u} [inst : PseudoMetricSpace α] [P
roperSpace α], LocallyCompactSpace α
· 使用定理 `FiniteDimensional.proper_real`：∀ (E : Type u) [inst : NormedAddCommGroup
 E] [inst_1 : NormedSpace ℝ E] [FiniteDimensional ℝ E], ProperSpace E
· 使用定理 `MeasureTheory.convolution_mono_right_of_nonneg`：convolution_mono_right_o
f_nonneg {f g g' : G -> Real} (hfg' : ConvolutionExistsAt f g' x (lsmul Real Rea
l) μ) (hf : forall x, 0 <= f x) (hg …
· 使用定理 `MeasureTheory.ConvolutionExistsAt.integrable`：∀ {𝕜 : Type u𝕜} {G : Type 
uG} {E : Type uE} {E' : Type uE'} {F : Type uF} [inst : NormedAddCommGroup E]   
[inst_1 : NormedAddCommGroup E'] […
· 使用定理 `HasCompactSupport.convolutionExists_left`：∀ {𝕜 : Type u𝕜} {G : Type uG} 
{E : Type uE} {E' : Type uE'} {F : Type uF} [inst : NormedAddCommGroup E]   [ins
t_1 : NormedAddCommGroup E'] […
· 使用定理 `MeasureTheory.Measure.isAddLeftInvariant_addHaarMeasure`：∀ {G : Type u_1
} [inst : AddGroup G] [inst_1 : TopologicalSpace G] [inst_2 : IsTopologicalAddGr
oup G]   [inst_3 : MeasurableSpace G] [inst_4…
· 使用定理 `MeasureTheory.Measure.IsAddHaarMeasure.isNegInvariant_of_innerRegular`：∀
 {G : Type u_1} [inst : AddCommGroup G] [inst_1 : TopologicalSpace G] [IsTopolog
icalAddGroup G]   [inst_3 : MeasurableSpace G] [BorelSpace …
· 使用定理 `MeasureTheory.Measure.isAddHaarMeasure_addHaarMeasure`：∀ {G : Type u_1} 
[inst : AddGroup G] [inst_1 : TopologicalSpace G] [inst_2 : IsTopologicalAddGrou
p G]   [inst_3 : MeasurableSpace G] [inst_4…
· 使用定理 `MeasureTheory.Measure.instInnerRegularOfPseudoMetrizableSpaceOfSigmaComp
actSpaceOfBorelSpaceOfSigmaFinite`：∀ {X : Type u_3} [inst : TopologicalSpace X] 
[TopologicalSpace.PseudoMetrizableSpace X] [SigmaCompactSpace X]   [inst_3 : Mea
surableSpace X]…
· 使用定理 `PseudoEMetricSpace.pseudoMetrizableSpace`：∀ {α : Type u_2} [inst : Pseud
oEMetricSpace α], TopologicalSpace.PseudoMetrizableSpace α
· 使用定理 `SeparableWeaklyLocallyCompactAddGroup.sigmaCompactSpace`：∀ {G : Type w} 
[inst : TopologicalSpace G] [inst_1 : AddGroup G] [IsTopologicalAddGroup G]   [T
opologicalSpace.SeparableSpace G] [WeaklyLoca…
· 使用定理 `TopologicalSpace.SecondCountableTopology.to_separableSpace`：∀ {α : Type 
u} [t : TopologicalSpace α] [SecondCountableTopology α], TopologicalSpace.Separa
bleSpace α
· 使用定理 `secondCountable_of_proper`：∀ {α : Type u} [inst : PseudoMetricSpace α] [
ProperSpace α], SecondCountableTopology α
· 使用定理 `instWeaklyLocallyCompactSpaceOfLocallyCompactSpace`：∀ {X : Type u_1} [in
st : TopologicalSpace X] [LocallyCompactSpace X], WeaklyLocallyCompactSpace X
· 使用定理 `MeasureTheory.Measure.sigmaFinite_addHaarMeasure`：∀ {G : Type u_1} [inst
 : AddGroup G] [inst_1 : TopologicalSpace G] [inst_2 : IsTopologicalAddGroup G] 
  [inst_3 : MeasurableSpace G] [inst_4…
· 使用定理 `ExistsContDiffBumpBase.w_compact_support`：w_compact_support {D : Real} (
Dpos : 0 < D) : HasCompactSupport (w D : E -> Real)
· 使用定理 `Continuous.mul`：Continuous.mul (hf : Continuous f) (hg : Continuous g) :
 Continuous (f * g)
· 使用定理 `IsTopologicalSemiring.toContinuousMul`：∀ {R : Type u_1} {inst : Topologi
calSpace R} {inst_1 : NonUnitalNonAssocSemiring R} [self : IsTopologicalSemiring
 R],   ContinuousMul R
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `continuous_const`：continuous_const (y : Y) : Continuous (fun x ↦ y)
· 使用定理 `Continuous.comp`：Continuous.comp {g : Y -> Z} (hg : Continuous g) (hf : 
Continuous f) : Continuous (g ∘ f)
· 使用定理 `ExistsContDiffBumpBase.u_continuous`：u_continuous : Continuous (u : E ->
 Real)
· 使用定理 `Continuous.fun_const_smul`：∀ {M : Type u_1} {α : Type u_2} {β : Type u_3
} [inst : TopologicalSpace α] [inst_1 : SMul M α] [ContinuousConstSMul M α]   [i
nst_3 : Topolog…
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `continuous_id'`：continuous_id' : Continuous (fun (x : X) => x)
· 使用定理 `MeasureTheory.locallyIntegrable_const`：locallyIntegrable_const [IsLocall
yFiniteMeasure μ] (c : E) : LocallyIntegrable (fun _ => c) μ
（共 45 条，此处仅展示前 30 条）
-/
theorem y_le_one {D : ℝ} (x : E) (Dpos : 0 < D) : y D x ≤ 1 := by
  have A : (w D ⋆[lsmul ℝ ℝ, μ] φ) x ≤ (w D ⋆[lsmul ℝ ℝ, μ] 1) x := by
    apply
      convolution_mono_right_of_nonneg _ (w_nonneg D) (indicator_le_self' fun x _ => zero_le_one)
        fun _ => zero_le_one
    refine ((w_compact_support E Dpos).convolutionExists_left _ ?_
      (locallyIntegrable_const (1 : ℝ)) x).integrable
    exact continuous_const.mul ((u_continuous E).comp (by fun_prop))
  have B : (w D ⋆[lsmul ℝ ℝ, μ] fun _ => (1 : ℝ)) x = 1 := by
    simp only [convolution, mul_one, lsmul_apply, smul_eq_mul, w_integral E Dpos]
  exact A.trans (le_of_eq B)
/-
**ExistsContDiffBumpBase.y_pos_of_mem_ball** 是 Mathlib 中的一个定理，位于命名空间 `ExistsCont
DiffBumpBase`。
形式化陈述：y_pos_of_mem_ball {D : Real} {x : E} (Dpos : 0 < D) (D_lt_one : D < 1) (hx
 : x in ball (0 : E) (1 + D)) : 0 < y D x
参数：Dpos : 0 < D；D_lt_one : D < 1；hx : x in ball (0 : E) (1 + D)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `MeasureTheory.integral_pos_iff_support_of_nonneg`：integral_pos_iff_suppo
rt_of_nonneg {f : α -> Real} (hf : 0 <= f) (hfi : Integrable f μ) : (0 < ∫ x, f 
x ∂μ) ↔ 0 < μ (Function.support f)
· 使用定理 `ExistsContDiffBumpBase.w_mul_φ_nonneg`：w_mul_φ_nonneg (D : Real) (x y : 
E) : 0 <= w D y * φ (x - y)
· 使用定理 `ExistsContDiffBumpBase.w_compact_support`：w_compact_support {D : Real} (
Dpos : 0 < D) : HasCompactSupport (w D : E -> Real)
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `locallyCompact_of_proper`：∀ {α : Type u} [inst : PseudoMetricSpace α] [P
roperSpace α], LocallyCompactSpace α
· 使用定理 `FiniteDimensional.proper_real`：∀ (E : Type u) [inst : NormedAddCommGroup
 E] [inst_1 : NormedSpace ℝ E] [FiniteDimensional ℝ E], ProperSpace E
· 使用定理 `MeasureTheory.LocallyIntegrable.indicator`：∀ {X : Type u_1} {ε'' : Type 
u_5} [inst : MeasurableSpace X] [inst_1 : TopologicalSpace X]   [inst_2 : Topolo
gicalSpace ε''] [inst_3 : ESemi…
· 使用定理 `MeasureTheory.locallyIntegrable_const`：locallyIntegrable_const [IsLocall
yFiniteMeasure μ] (c : E) : LocallyIntegrable (fun _ => c) μ
· 使用定理 `MeasureTheory.isLocallyFiniteMeasure_of_isFiniteMeasureOnCompacts`：∀ {α 
: Type u_1} {m0 : MeasurableSpace α} {μ : MeasureTheory.Measure α} [inst : Topol
ogicalSpace α]   [WeaklyLocallyCompactSpace α] [Measure…
· 使用定理 `instWeaklyLocallyCompactSpaceOfLocallyCompactSpace`：∀ {X : Type u_1} [in
st : TopologicalSpace X] [LocallyCompactSpace X], WeaklyLocallyCompactSpace X
· 使用定理 `MeasureTheory.Measure.IsAddHaarMeasure.toIsFiniteMeasureOnCompacts`：∀ {G
 : Type u_3} {inst : AddGroup G} {inst_1 : TopologicalSpace G} {inst_2 : Measura
bleSpace G}   {μ : MeasureTheory.Measure G} [self : μ.Is…
· 使用定理 `MeasureTheory.Measure.isAddHaarMeasure_addHaarMeasure`：∀ {G : Type u_1} 
[inst : AddGroup G] [inst_1 : TopologicalSpace G] [inst_2 : IsTopologicalAddGrou
p G]   [inst_3 : MeasurableSpace G] [inst_4…
· 使用定理 `measurableSet_closedBall`：measurableSet_closedBall : MeasurableSet (Metr
ic.closedBall x ε)
· 使用定理 `BorelSpace.opensMeasurable`：∀ {α : Type u_6} [inst : TopologicalSpace α]
 [inst_1 : MeasurableSpace α] [BorelSpace α], OpensMeasurableSpace α
· 使用定理 `Continuous.mul`：Continuous.mul (hf : Continuous f) (hg : Continuous g) :
 Continuous (f * g)
· 使用定理 `IsTopologicalSemiring.toContinuousMul`：∀ {R : Type u_1} {inst : Topologi
calSpace R} {inst_1 : NonUnitalNonAssocSemiring R} [self : IsTopologicalSemiring
 R],   ContinuousMul R
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `continuous_const`：continuous_const (y : Y) : Continuous (fun x ↦ y)
· 使用定理 `Continuous.comp`：Continuous.comp {g : Y -> Z} (hg : Continuous g) (hf : 
Continuous f) : Continuous (g ∘ f)
· 使用定理 `ExistsContDiffBumpBase.u_continuous`：u_continuous : Continuous (u : E ->
 Real)
· 使用定理 `Continuous.fun_const_smul`：∀ {M : Type u_1} {α : Type u_2} {β : Type u_3
} [inst : TopologicalSpace α] [inst_1 : SMul M α] [ContinuousConstSMul M α]   [i
nst_3 : Topolog…
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `continuous_id'`：continuous_id' : Continuous (fun (x : X) => x)
· 使用定理 `MeasureTheory.ConvolutionExistsAt.integrable`：∀ {𝕜 : Type u𝕜} {G : Type 
uG} {E : Type uE} {E' : Type uE'} {F : Type uF} [inst : NormedAddCommGroup E]   
[inst_1 : NormedAddCommGroup E'] […
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `HasCompactSupport.convolutionExists_left`：∀ {𝕜 : Type u𝕜} {G : Type uG} 
{E : Type uE} {E' : Type uE'} {F : Type uF} [inst : NormedAddCommGroup E]   [ins
t_1 : NormedAddCommGroup E'] […
· 使用定理 `MeasureTheory.Measure.isAddLeftInvariant_addHaarMeasure`：∀ {G : Type u_1
} [inst : AddGroup G] [inst_1 : TopologicalSpace G] [inst_2 : IsTopologicalAddGr
oup G]   [inst_3 : MeasurableSpace G] [inst_4…
（共 180 条，此处仅展示前 30 条）
-/
theorem y_pos_of_mem_ball {D : ℝ} {x : E} (Dpos : 0 < D) (D_lt_one : D < 1)
    (hx : x ∈ ball (0 : E) (1 + D)) : 0 < y D x := by
  simp only [mem_ball_zero_iff] at hx
  refine (integral_pos_iff_support_of_nonneg (w_mul_φ_nonneg D x) ?_).2 ?_
  · have F_comp : HasCompactSupport (w D) := w_compact_support E Dpos
    have B : LocallyIntegrable (φ : E → ℝ) μ :=
      (locallyIntegrable_const _).indicator measurableSet_closedBall
    have C : Continuous (w D : E → ℝ) :=
      continuous_const.mul ((u_continuous E).comp (by fun_prop))
    exact (F_comp.convolutionExists_left (lsmul ℝ ℝ : ℝ →L[ℝ] ℝ →L[ℝ] ℝ) C B x).integrable
  · set z := (D / (1 + D)) • x with hz
    have B : 0 < 1 + D := by linarith
    have C : ball z (D * (1 + D - ‖x‖) / (1 + D)) ⊆ support fun y : E => w D y * φ (x - y) := by
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
        rw [← one_smul ℝ x, dist_eq_norm, hz, ← sub_smul, one_smul, norm_smul, ID]
        field_simp
        nlinarith only [hx, D_lt_one]
    apply lt_of_lt_of_le _ (measure_mono C)
    apply measure_ball_pos
    exact div_pos (mul_pos Dpos (by linarith only [hx])) B

variable (E)
/-
**ExistsContDiffBumpBase.y_smooth** 是 Mathlib 中的一个定理，位于命名空间 `ExistsContDiffBumpB
ase`。
形式化陈述：y_smooth : ContDiffOn Real ∞ (uncurry y) (Ioo (0 : Real) 1 ×ˢ (univ : Set 
E))
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `isOpen_Ioo`：isOpen_Ioo : IsOpen (Ioo a b)
· 使用定理 `HasSolidNorm.orderClosedTopology`：∀ {E : Type u_2} [inst : NormedAddComm
Group E] [inst_1 : Lattice E] [HasSolidNorm E] [IsOrderedAddMonoid E],   OrderCl
osedTopology E
· 使用定理 `instHasSolidNormReal`：HasSolidNorm ℝ
· 使用定理 `ProperSpace.isCompact_closedBall`：∀ {α : Type u} {inst : PseudoMetricSpa
ce α} [self : ProperSpace α] (x : α) (r : ℝ), IsCompact (Metric.closedBall x r)
· 使用定理 `FiniteDimensional.proper_real`：∀ (E : Type u) [inst : NormedAddCommGroup
 E] [inst_1 : NormedSpace ℝ E] [FiniteDimensional ℝ E], ProperSpace E
· 使用定理 `MeasureTheory.contDiffOn_convolution_left_with_param`：contDiffOn_convolu
tion_left_with_param [μ.IsAddLeftInvariant] [μ.IsNegInvariant] (L : E' ->L[𝕜] E 
->L[𝕜] F) {f : G -> E} {n : Nat∞} {g : P -…
· 使用定理 `MeasureTheory.Measure.isAddLeftInvariant_addHaarMeasure`：∀ {G : Type u_1
} [inst : AddGroup G] [inst_1 : TopologicalSpace G] [inst_2 : IsTopologicalAddGr
oup G]   [inst_3 : MeasurableSpace G] [inst_4…
· 使用定理 `MeasureTheory.Measure.IsAddHaarMeasure.isNegInvariant_of_innerRegular`：∀
 {G : Type u_1} [inst : AddCommGroup G] [inst_1 : TopologicalSpace G] [IsTopolog
icalAddGroup G]   [inst_3 : MeasurableSpace G] [BorelSpace …
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `MeasureTheory.Measure.isAddHaarMeasure_addHaarMeasure`：∀ {G : Type u_1} 
[inst : AddGroup G] [inst_1 : TopologicalSpace G] [inst_2 : IsTopologicalAddGrou
p G]   [inst_3 : MeasurableSpace G] [inst_4…
· 使用定理 `locallyCompact_of_proper`：∀ {α : Type u} [inst : PseudoMetricSpace α] [P
roperSpace α], LocallyCompactSpace α
· 使用定理 `MeasureTheory.Measure.instInnerRegularOfPseudoMetrizableSpaceOfSigmaComp
actSpaceOfBorelSpaceOfSigmaFinite`：∀ {X : Type u_3} [inst : TopologicalSpace X] 
[TopologicalSpace.PseudoMetrizableSpace X] [SigmaCompactSpace X]   [inst_3 : Mea
surableSpace X]…
· 使用定理 `PseudoEMetricSpace.pseudoMetrizableSpace`：∀ {α : Type u_2} [inst : Pseud
oEMetricSpace α], TopologicalSpace.PseudoMetrizableSpace α
· 使用定理 `SeparableWeaklyLocallyCompactAddGroup.sigmaCompactSpace`：∀ {G : Type w} 
[inst : TopologicalSpace G] [inst_1 : AddGroup G] [IsTopologicalAddGroup G]   [T
opologicalSpace.SeparableSpace G] [WeaklyLoca…
· 使用定理 `TopologicalSpace.SecondCountableTopology.to_separableSpace`：∀ {α : Type 
u} [t : TopologicalSpace α] [SecondCountableTopology α], TopologicalSpace.Separa
bleSpace α
· 使用定理 `secondCountable_of_proper`：∀ {α : Type u} [inst : PseudoMetricSpace α] [
ProperSpace α], SecondCountableTopology α
· 使用定理 `instWeaklyLocallyCompactSpaceOfLocallyCompactSpace`：∀ {X : Type u_1} [in
st : TopologicalSpace X] [LocallyCompactSpace X], WeaklyLocallyCompactSpace X
· 使用定理 `MeasureTheory.Measure.sigmaFinite_addHaarMeasure`：∀ {G : Type u_1} [inst
 : AddGroup G] [inst_1 : TopologicalSpace G] [inst_2 : IsTopologicalAddGroup G] 
  [inst_3 : MeasurableSpace G] [inst_4…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mul_inv_rev`：mul_inv_rev (a b : G) : (a * b)⁻¹ = b⁻¹ * a⁻¹
· 使用定理 `NormedDivisionRing.toNormMulClass`：∀ {α : Type u_2} [inst : NormedDivisi
onRing α], NormMulClass α
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose₂`：contrapose₂ {p q : Prop} : (¬ q -
> p) -> (¬ p -> q)
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Function.mem_support`：∀ {ι : Type u_1} {M : Type u_3} [inst : Zero M] {f
 : ι → M} {x : ι}, x ∈ Function.support f ↔ f x ≠ 0
· 使用定理 `mem_closedBall_zero_iff`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] 
{a : E} {r : ℝ}, a ∈ Metric.closedBall 0 r ↔ ‖a‖ ≤ r
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
（共 66 条，此处仅展示前 30 条）
-/
theorem y_smooth : ContDiffOn ℝ ∞ (uncurry y) (Ioo (0 : ℝ) 1 ×ˢ (univ : Set E)) := by
  have hs : IsOpen (Ioo (0 : ℝ) (1 : ℝ)) := isOpen_Ioo
  have hk : IsCompact (closedBall (0 : E) 1) := ProperSpace.isCompact_closedBall _ _
  refine contDiffOn_convolution_left_with_param (lsmul ℝ ℝ) hs hk ?_ ?_ ?_
  · rintro p x hp hx
    simp only [w, mul_inv_rev, smul_eq_mul, mul_eq_zero, inv_eq_zero]
    right
    contrapose! hx
    have : p⁻¹ • x ∈ support u := mem_support.2 hx
    simp only [u_support, norm_smul, mem_ball_zero_iff, Real.norm_eq_abs, abs_inv,
      abs_of_nonneg hp.1.le, ← div_eq_inv_mul, div_lt_one hp.1] at this
    rw [mem_closedBall_zero_iff]
    exact this.le.trans hp.2.le
  · exact (locallyIntegrable_const _).indicator measurableSet_closedBall
  · apply ContDiffOn.mul
    · norm_cast
      refine
        (contDiffOn_const.mul ?_).inv fun x hx =>
          ne_of_gt (mul_pos (u_int_pos E) (pow_pos (abs_pos_of_pos hx.1.1) (finrank ℝ E)))
      apply ContDiffOn.pow
      simp_rw [← Real.norm_eq_abs]
      apply ContDiffOn.norm ℝ
      · exact contDiffOn_fst
      · intro x hx; exact ne_of_gt hx.1.1
    · apply (u_smooth E).comp_contDiffOn
      exact ContDiffOn.smul (contDiffOn_fst.inv fun x hx => ne_of_gt hx.1.1) contDiffOn_snd
/-
**ExistsContDiffBumpBase.y_support** 是 Mathlib 中的一个定理，位于命名空间 `ExistsContDiffBump
Base`。
形式化陈述：y_support {D : Real} (Dpos : 0 < D) (D_lt_one : D < 1) : support (y D : E 
-> Real) = ball (0 : E) (1 + D)
参数：Dpos : 0 < D；D_lt_one : D < 1。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Function.support_eq_iff`：∀ {ι : Type u_1} {M : Type u_3} [inst : Zero M]
 {f : ι → M} {s : Set ι},   Function.support f = s ↔ (∀ x ∈ s, f x ≠ 0) ∧ ∀ x ∉ 
s, f x = 0
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `ExistsContDiffBumpBase.y_pos_of_mem_ball`：y_pos_of_mem_ball {D : Real} {
x : E} (Dpos : 0 < D) (D_lt_one : D < 1) (hx : x in ball (0 : E) (1 + D)) : 0 < 
y D x
· 使用定理 `ExistsContDiffBumpBase.y_eq_zero_of_notMem_ball`：y_eq_zero_of_notMem_bal
l {D : Real} {x : E} (Dpos : 0 < D) (hx : x ∉ ball (0 : E) (1 + D)) : y D x = 0
-/
theorem y_support {D : ℝ} (Dpos : 0 < D) (D_lt_one : D < 1) :
    support (y D : E → ℝ) = ball (0 : E) (1 + D) :=
  support_eq_iff.2
    ⟨fun _ hx => (y_pos_of_mem_ball Dpos D_lt_one hx).ne', fun _ hx =>
      y_eq_zero_of_notMem_ball Dpos hx⟩

end HelperDefinitions

/-
**ExistsContDiffBumpBase.** 是 Mathlib 中的一个实例，位于命名空间 `ExistsContDiffBumpBase`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 100) {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] : HasContDiffBump E := by
  refine ⟨⟨?_⟩⟩
  borelize E
  have IR : ∀ R : ℝ, 1 < R → 0 < (R - 1) / (R + 1) := by intro R hR; apply div_pos <;> linarith
  exact
    { toFun := fun R x => if 1 < R then y ((R - 1) / (R + 1)) (((R + 1) / 2)⁻¹ • x) else 0
      mem_Icc := fun R x => by
        push _ ∈ _
        split_ifs with h
        · refine ⟨y_nonneg _ _, y_le_one _ (IR R h)⟩
        · simp only [le_refl, zero_le_one, and_self]
      symmetric := fun R x => by
        split_ifs
        · simp only [y_neg, smul_neg]
        · rfl
      smooth := by
        suffices
          ContDiffOn ℝ ∞
            (uncurry y ∘ fun p : ℝ × E => ((p.1 - 1) / (p.1 + 1), ((p.1 + 1) / 2)⁻¹ • p.2))
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
          2 / (R + 1) * ‖x‖ ≤ 2 / (R + 1) := mul_le_of_le_one_right (by positivity) hx
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

