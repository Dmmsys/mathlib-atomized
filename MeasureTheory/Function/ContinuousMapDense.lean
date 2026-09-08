/-
Copyright (c) 2021 Heather Macbeth. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Heather Macbeth
-/
module

public import Mathlib.Topology.UrysohnsLemma
public import Mathlib.MeasureTheory.Function.LpSpace.ContinuousFunctions
public import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
# Approximation in Lᵖ by continuous functions

This file proves that bounded continuous functions are dense in `Lp E p μ`, for `p < ∞`, if the
domain `α` of the functions is a normal topological space and the measure `μ` is weakly regular.
It also proves the same results for approximation by continuous functions with compact support
when the space is locally compact and `μ` is regular.

The result is presented in several versions. First concrete versions giving an approximation
up to `ε` in these various contexts, and then abstract versions stating that the topological
closure of the relevant subgroups of `Lp` are the whole space.

* `MeasureTheory.MemLp.exists_hasCompactSupport_eLpNorm_sub_le` states that, in a locally compact
  space, an `ℒp` function can be approximated by continuous functions with compact support,
  in the sense that `eLpNorm (f - g) p μ` is small.
* `MeasureTheory.MemLp.exists_hasCompactSupport_integral_rpow_sub_le`: same result, but expressed in
  terms of `∫ ‖f - g‖^p`.

Versions with `Integrable` instead of `MemLp` are specialized to the case `p = 1`.
Versions with `boundedContinuous` instead of `HasCompactSupport` drop the locally
compact assumption and give only approximation by a bounded continuous function.

* `MeasureTheory.Lp.boundedContinuousFunction_dense`: The subgroup
  `MeasureTheory.Lp.boundedContinuousFunction` of `Lp E p μ`, the additive subgroup of
  `Lp E p μ` consisting of equivalence classes containing a continuous representative, is dense in
  `Lp E p μ`.
* `BoundedContinuousFunction.toLp_denseRange`: For finite-measure `μ`, the continuous linear
  map `BoundedContinuousFunction.toLp p μ 𝕜` from `α →ᵇ E` to `Lp E p μ` has dense range.
* `ContinuousMap.toLp_denseRange`: For compact `α` and finite-measure `μ`, the continuous linear
  map `ContinuousMap.toLp p μ 𝕜` from `C(α, E)` to `Lp E p μ` has dense range.

Note that for `p = ∞` this result is not true:  the characteristic function of the set `[0, ∞)` in
`ℝ` cannot be continuously approximated in `L∞`.

The proof is in three steps.  First, since simple functions are dense in `Lp`, it suffices to prove
the result for a scalar multiple of a characteristic function of a measurable set `s`. Secondly,
since the measure `μ` is weakly regular, the set `s` can be approximated above by an open set and
below by a closed set.  Finally, since the domain `α` is normal, we use Urysohn's lemma to find a
continuous function interpolating between these two sets.

## Related results

Are you looking for a result on "directional" approximation (above or below with respect to an
order) of functions whose codomain is `ℝ≥0∞` or `ℝ`, by semicontinuous functions?
See the Vitali-Carathéodory theorem,
in the file `Mathlib/MeasureTheory/Integral/Bochner/VitaliCaratheodory.lean`.
-/

public section

open scoped ENNReal NNReal Topology BoundedContinuousFunction

open MeasureTheory TopologicalSpace ContinuousMap Set Bornology

variable {α : Type*} [TopologicalSpace α] [NormalSpace α]
  [MeasurableSpace α] [BorelSpace α]
variable {E : Type*} [NormedAddCommGroup E] {μ : Measure α} {p : ℝ≥0∞}

namespace MeasureTheory

variable [NormedSpace ℝ E]

/-- A variant of Urysohn's lemma, `ℒ^p` version, for an outer regular measure `μ`:
consider two sets `s ⊆ u` which are respectively closed and open with `μ s < ∞`, and a vector `c`.
Then one may find a continuous function `f` equal to `c` on `s` and to `0` outside of `u`,
bounded by `‖c‖` everywhere, and such that the `ℒ^p` norm of `f - s.indicator (fun y ↦ c)` is
arbitrarily small. Additionally, this function `f` belongs to `ℒ^p`. -/
/-
**MeasureTheory.exists_continuous_eLpNorm_sub_le_of_closed** 是 Mathlib 中的一个定理，位于
命名空间 `MeasureTheory`。
形式化陈述：exists_continuous_eLpNorm_sub_le_of_closed [μ.OuterRegular] (hp : p != ∞) 
{s u : Set α} (s_closed : IsClosed s) (u_open : IsOpen u) (hsu : s subseteq u) (
hs : μ s != ∞) (c : E) {ε : Real>=0∞} (hε : ε != 0) : exists f : α -> E, Continu
ous f ∧ eLpNorm (fun x => f x - s.indicator (fun _y => c) x) p μ <= ε ∧ (forall 
x, ‖f x‖ <= ‖c‖) ∧ Function.support f subseteq u ∧ MemLp f p μ
参数：hp : p != ∞；s_closed : IsClosed s；u_open : IsOpen u；hsu : s subseteq u；hs : μ
 s != ∞；c : E；hε : ε != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.exists_eLpNorm_indicator_le`：exists_eLpNorm_indicator_le (
hp : p != ∞) (c : E) {ε : Real>=0∞} (hε : ε != 0) : exists η : Real>=0, 0 < η ∧ 
forall s : Set α, μ s <= η -> e…
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `ENNReal.coe_lt_coe`：∀ {r q : NNReal}, ↑r < ↑q ↔ r < q
· 使用定理 `MeasurableSet.exists_isOpen_sdiff_lt`：∀ {α : Type u_1} [inst : Measurabl
eSpace α] {μ : MeasureTheory.Measure α} [inst_1 : TopologicalSpace α] [μ.OuterRe
gular]   {A : Set α}, Meas…
· 使用定理 `IsClosed.measurableSet`：IsClosed.measurableSet (h : IsClosed s) : Measur
ableSet s
· 使用定理 `BorelSpace.opensMeasurable`：∀ {α : Type u_6} [inst : TopologicalSpace α]
 [inst_1 : MeasurableSpace α] [BorelSpace α], OpensMeasurableSpace α
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `Set.subset_inter`：subset_inter {s t r : Set α} (rs : r subseteq s) (rt :
 r subseteq t) : r subseteq s inter t
· 使用定理 `LE.le.trans_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b 
→ b < c → a < c
· 使用定理 `MeasureTheory.measure_mono`：measure_mono (h : s subseteq t) : μ s <= μ t
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `Set.inter_subset_right`：inter_subset_right {s t : Set α} : s inter t sub
seteq t
· 使用定理 `exists_continuous_zero_one_of_isClosed`：exists_continuous_zero_one_of_is
Closed [NormalSpace X] {s t : Set X} (hs : IsClosed s) (ht : IsClosed t) (hd : D
isjoint s t) : exists f : C(…
· 使用定理 `IsOpen.isClosed_compl`：∀ {X : Type u} [inst : TopologicalSpace X] {s : S
et X}, IsOpen s → IsClosed sᶜ
· 使用定理 `IsOpen.inter`：IsOpen.inter (s t : Set α) : IsOpen α s -> IsOpen α t -> I
sOpen α (s inter t)
· 使用定理 `disjoint_compl_left_iff`：disjoint_compl_left_iff : Disjoint xᶜ y ↔ y <= 
x
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Real.norm_eq_abs`：norm_eq_abs (r : Real) : ‖r‖ = |r|
· 使用定理 `abs_of_nonneg`：∀ {α : Type u_1} [inst : Lattice α] [inst_1 : AddGroup α]
 {a : α} [AddLeftMono α], 0 ≤ a → |a| = a
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用引理 `norm_smul`：norm_smul [Norm α] [Norm β] [SMul α β] [NormSMulClass α β] (r
 : α) (x : β) : ‖r • x‖ = ‖r‖ * ‖x‖
· 使用定理 `NormedSpace.toNormSMulClass`：∀ {𝕜 : Type u_1} {E : Type u_3} [inst : Nor
medField 𝕜] [inst_1 : SeminormedAddCommGroup E] [inst_2 : NormedSpace 𝕜 E],   No
rmSMulClass 𝕜 E
· 使用定理 `mul_le_of_le_one_left`：mul_le_of_le_one_left [MulPosMono α] (hb : 0 <= b
) (h : a <= 1) : a * b <= b
· 使用定理 `IsOrderedRing.toMulPosMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], MulPosMono R
· 使用定理 `norm_nonneg`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (a : E), 0 ≤
 ‖a‖
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
（共 82 条，此处仅展示前 30 条）

--- 原说明 ---
A variant of Urysohn's lemma, `ℒ^p` version, for an outer regular measure `μ`:
consider two sets `s ⊆ u` which are respectively closed and open with `μ s < ∞`,
 and a vector `c`.
Then one may find a continuous function `f` equal to `c` on `s` and to `0` outsi
de of `u`,
bounded by `‖c‖` everywhere, and such that the `ℒ^p` norm of `f - s.indicator (f
un y ↦ c)` is
arbitrarily small. Additionally, this function `f` belongs to `ℒ^p`.
-/
theorem exists_continuous_eLpNorm_sub_le_of_closed [μ.OuterRegular] (hp : p ≠ ∞) {s u : Set α}
    (s_closed : IsClosed s) (u_open : IsOpen u) (hsu : s ⊆ u) (hs : μ s ≠ ∞) (c : E) {ε : ℝ≥0∞}
    (hε : ε ≠ 0) :
    ∃ f : α → E,
      Continuous f ∧
        eLpNorm (fun x => f x - s.indicator (fun _y => c) x) p μ ≤ ε ∧
          (∀ x, ‖f x‖ ≤ ‖c‖) ∧ Function.support f ⊆ u ∧ MemLp f p μ := by
  obtain ⟨η, η_pos, hη⟩ :
      ∃ η : ℝ≥0, 0 < η ∧ ∀ s : Set α, μ s ≤ η → eLpNorm (s.indicator fun _x => c) p μ ≤ ε :=
    exists_eLpNorm_indicator_le hp c hε
  have ηpos : (0 : ℝ≥0∞) < η := ENNReal.coe_lt_coe.2 η_pos
  obtain ⟨V, sV, V_open, h'V, hV⟩ : ∃ (V : Set α), V ⊇ s ∧ IsOpen V ∧ μ V < ∞ ∧ μ (V \ s) < η :=
    s_closed.measurableSet.exists_isOpen_sdiff_lt hs ηpos.ne'
  let v := u ∩ V
  have hsv : s ⊆ v := subset_inter hsu sV
  have hμv : μ v < ∞ := (measure_mono inter_subset_right).trans_lt h'V
  obtain ⟨g, hgv, hgs, hg_range⟩ :=
    exists_continuous_zero_one_of_isClosed (u_open.inter V_open).isClosed_compl s_closed
      (disjoint_compl_left_iff.2 hsv)
  -- Multiply this by `c` to get a continuous approximation to the function `f`; the key point is
  -- that this is pointwise bounded by the indicator of the set `v \ s`, which has small measure.
  have g_norm : ∀ x, ‖g x‖ = g x := fun x => by rw [Real.norm_eq_abs, abs_of_nonneg (hg_range x).1]
  have gc_bd0 : ∀ x, ‖g x • c‖ ≤ ‖c‖ := by
    intro x
    simp only [norm_smul, g_norm x]
    apply mul_le_of_le_one_left (norm_nonneg _)
    exact (hg_range x).2
  have gc_bd :
      ∀ x, ‖g x • c - s.indicator (fun _x => c) x‖ ≤ ‖(v \ s).indicator (fun _x => c) x‖ := by
    intro x
    by_cases hv : x ∈ v
    · rw [← Set.sdiff_union_of_subset hsv] at hv
      rcases hv with hsv | hs
      · simpa only [hsv.2, Set.indicator_of_notMem, not_false_iff, sub_zero, hsv,
          Set.indicator_of_mem] using gc_bd0 x
      · simp [hgs hs, hs]
    · simp [hgv hv, show x ∉ s from fun h => hv (hsv h)]
  have gc_support : (Function.support fun x : α => g x • c) ⊆ v := by
    refine Function.support_subset_iff'.2 fun x hx => ?_
    simp only [hgv hx, Pi.zero_apply, zero_smul]
  have gc_mem : MemLp (fun x => g x • c) p μ := by
    refine MemLp.smul (memLp_top_const _) ?_ (p := p) (q := ∞)
    refine ⟨g.continuous.aestronglyMeasurable, ?_⟩
    have : eLpNorm (v.indicator fun _x => (1 : ℝ)) p μ < ⊤ :=
      (eLpNorm_indicator_const_le _ _).trans_lt <| by simp [lt_top_iff_ne_top, hμv.ne]
    refine (eLpNorm_mono fun x => ?_).trans_lt this
    by_cases hx : x ∈ v
    · simp only [hx, abs_of_nonneg (hg_range x).1, (hg_range x).2, Real.norm_eq_abs,
        indicator_of_mem, CStarRing.norm_one]
    · simp only [hgv hx, Pi.zero_apply, Real.norm_eq_abs, abs_zero, abs_nonneg]
  refine ⟨fun x ↦ g x • c, by fun_prop, (eLpNorm_mono gc_bd).trans ?_, gc_bd0,
      gc_support.trans inter_subset_left, gc_mem⟩
  exact hη _ ((measure_mono (sdiff_subset_sdiff inter_subset_right Subset.rfl)).trans hV.le)

/-- In a locally compact space, any function in `ℒp` can be approximated by compactly supported
continuous functions when `p < ∞`, version in terms of `eLpNorm`. -/
/-
**MeasureTheory.MemLp.exists_hasCompactSupport_eLpNorm_sub_le** 是 Mathlib 中的一个定理
，位于命名空间 `MeasureTheory.MemLp`。
形式化陈述：∀ {α : Type u_1} [inst : TopologicalSpace α] [NormalSpace α] [inst_2 : Mea
surableSpace α] [BorelSpace α] {E : Type u_2}   [inst_4 : NormedAddCommGroup E] 
{μ : MeasureTheory.Measure α} {p : ENNReal} [NormedSpace ℝ E] [R1Space α]   [Wea
klyLocallyCompactSpace α] [μ.Regular],   p ≠ ⊤ →     ∀ {f : α → E},       Measur
eTheory.MemLp f p μ →         ∀ {ε : ENNReal},           ε ≠ 0 →             ∃ g
, HasCompactSupport g ∧ MeasureTheory.eLpNorm (f - g) p μ ≤ ε ∧ Continuous g ∧ M
easureTheory.MemLp g p μ
参数：f - g。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.MemLp.induction_dense`：∀ {α : Type u_1} {E : Type u_4} [in
st : MeasurableSpace α] [inst_1 : NormedAddCommGroup E] {p : ENNReal}   {μ : Mea
sureTheory.Measure α},   …
· 使用定理 `MeasureTheory.exists_Lp_half`：exists_Lp_half (p : Real>=0∞) {δ : Real>=0
∞} (hδ : δ != 0) : exists η : Real>=0∞, 0 < η ∧ forall (f g : α -> ε), AEStrongl
yMeasurable f μ ->…
· 使用定理 `MeasureTheory.exists_eLpNorm_indicator_le`：exists_eLpNorm_indicator_le (
hp : p != ∞) (c : E) {ε : Real>=0∞} (hε : ε != 0) : exists η : Real>=0, 0 < η ∧ 
forall s : Set α, μ s <= η -> e…
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `ENNReal.coe_pos`：∀ {r : NNReal}, 0 < ↑r ↔ 0 < r
· 使用定理 `MeasurableSet.exists_isCompact_isClosed_sdiff_lt`：∀ {α : Type u_1} [inst
 : MeasurableSpace α] {μ : MeasureTheory.Measure α} [inst_1 : TopologicalSpace α
] [BorelSpace α]   [R1Space α] [μ.Inne…
· 使用定理 `MeasureTheory.Measure.Regular.instInnerRegularCompactLTTop`：∀ {α : Type 
u_1} [inst : MeasurableSpace α] {μ : MeasureTheory.Measure α} [inst_1 : Topologi
calSpace α] [μ.Regular],   μ.InnerRegularCompact…
· 使用定理 `LT.lt.ne`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≠ b
· 使用定理 `LE.le.trans_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b 
→ b < c → a < c
· 使用定理 `MeasureTheory.measure_mono`：measure_mono (h : s subseteq t) : μ s <= μ t
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.eLpNorm_neg`：eLpNorm_neg (f : α -> F) (p : Real>=0∞) (μ : 
Measure α) : eLpNorm (-f) p μ = eLpNorm f p μ
· 使用定理 `neg_sub`：∀ {α : Type u_1} [inst : SubtractionMonoid α] (a b : α), -(a - 
b) = b - a
· 使用定理 `Set.indicator_sdiff`：∀ {α : Type u_1} {G : Type u_6} [inst : AddGroup G]
 {s t : Set α},   s ⊆ t → ∀ (f : α → G), (t \ s).indicator f = t.indicator f - s
.indicato…
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `exists_compact_superset`：exists_compact_superset [WeaklyLocallyCompactSp
ace X] {K : Set X} (hK : IsCompact K) : exists K', IsCompact K' ∧ K subseteq int
erior K'
· 使用定理 `MeasureTheory.exists_continuous_eLpNorm_sub_le_of_closed`：exists_continu
ous_eLpNorm_sub_le_of_closed [μ.OuterRegular] (hp : p != ∞) {s u : Set α} (s_clo
sed : IsClosed s) (u_open : IsOpen u) (hsu : s…
· 使用定理 `MeasureTheory.Measure.WeaklyRegular.toOuterRegular`：∀ {α : Type u_1} {in
st : MeasurableSpace α} {inst_1 : TopologicalSpace α} {μ : MeasureTheory.Measure
 α}   [self : μ.WeaklyRegular], μ.OuterR…
· 使用定理 `MeasureTheory.Measure.Regular.weaklyRegular`：∀ {α : Type u_1} [inst : Me
asurableSpace α] {μ : MeasureTheory.Measure α} [inst_1 : TopologicalSpace α] [R1
Space α]   [μ.Regular], μ.WeaklyR…
· 使用定理 `isOpen_interior`：isOpen_interior : IsOpen (interior s)
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `sub_add_sub_cancel`：∀ {G : Type u_3} [inst : AddGroup G] (a b c : G), a 
- b + (b - c) = a - c
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `MeasureTheory.AEStronglyMeasurable.sub`：∀ {α : Type u_1} {β : Type u_2} 
[inst : TopologicalSpace β] {m m₀ : MeasurableSpace α} {μ : MeasureTheory.Measur
e α}   {f g : α → β} [inst_1…
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
（共 43 条，此处仅展示前 30 条）

--- 原说明 ---
In a locally compact space, any function in `ℒp` can be approximated by compactl
y supported
continuous functions when `p < ∞`, version in terms of `eLpNorm`.
-/
theorem MemLp.exists_hasCompactSupport_eLpNorm_sub_le
    [R1Space α] [WeaklyLocallyCompactSpace α] [μ.Regular]
    (hp : p ≠ ∞) {f : α → E} (hf : MemLp f p μ) {ε : ℝ≥0∞} (hε : ε ≠ 0) :
    ∃ g : α → E, HasCompactSupport g ∧ eLpNorm (f - g) p μ ≤ ε ∧ Continuous g ∧ MemLp g p μ := by
  suffices H :
      ∃ g : α → E, eLpNorm (f - g) p μ ≤ ε ∧ Continuous g ∧ MemLp g p μ ∧ HasCompactSupport g by
    rcases H with ⟨g, hg, g_cont, g_mem, g_support⟩
    exact ⟨g, g_support, hg, g_cont, g_mem⟩
  -- It suffices to check that the set of functions we consider approximates characteristic
  -- functions, is stable under addition and consists of ae strongly measurable functions.
  -- First check the latter easy facts.
  apply hf.induction_dense hp _ _ _ _ hε
  rotate_left
  -- stability under addition
  · rintro f g ⟨f_cont, f_mem, hf⟩ ⟨g_cont, g_mem, hg⟩
    exact ⟨f_cont.add g_cont, f_mem.add g_mem, hf.add hg⟩
  -- ae strong measurability
  · rintro f ⟨_f_cont, f_mem, _hf⟩
    exact f_mem.aestronglyMeasurable
  -- We are left with approximating characteristic functions.
  -- This follows from `exists_continuous_eLpNorm_sub_le_of_closed`.
  intro c t ht htμ ε hε
  rcases exists_Lp_half E μ p hε with ⟨δ, δpos, hδ⟩
  obtain ⟨η, ηpos, hη⟩ :
      ∃ η : ℝ≥0, 0 < η ∧ ∀ s : Set α, μ s ≤ η → eLpNorm (s.indicator fun _x => c) p μ ≤ δ :=
    exists_eLpNorm_indicator_le hp c δpos.ne'
  have hη_pos' : (0 : ℝ≥0∞) < η := ENNReal.coe_pos.2 ηpos
  obtain ⟨s, st, s_compact, s_closed, μs⟩ :
      ∃ s, s ⊆ t ∧ IsCompact s ∧ IsClosed s ∧ μ (t \ s) < η :=
    ht.exists_isCompact_isClosed_sdiff_lt htμ.ne hη_pos'.ne'
  have hsμ : μ s < ∞ := (measure_mono st).trans_lt htμ
  have I1 : eLpNorm ((s.indicator fun _y => c) - t.indicator fun _y => c) p μ ≤ δ := by
    rw [← eLpNorm_neg, neg_sub, ← indicator_sdiff st]
    exact hη _ μs.le
  obtain ⟨k, k_compact, sk⟩ : ∃ k : Set α, IsCompact k ∧ s ⊆ interior k :=
    exists_compact_superset s_compact
  rcases exists_continuous_eLpNorm_sub_le_of_closed hp s_closed isOpen_interior sk hsμ.ne c δpos.ne'
    with ⟨f, f_cont, I2, _f_bound, f_support, f_mem⟩
  have I3 : eLpNorm (f - t.indicator fun _y => c) p μ ≤ ε := by
    convert!
      (hδ _ _
          (f_mem.aestronglyMeasurable.sub
            (aestronglyMeasurable_const.indicator s_closed.measurableSet))
          ((aestronglyMeasurable_const.indicator s_closed.measurableSet).sub
            (aestronglyMeasurable_const.indicator ht))
          I2 I1).le using 2
    simp only [sub_add_sub_cancel]
  refine ⟨f, I3, f_cont, f_mem, HasCompactSupport.intro k_compact fun x hx => ?_⟩
  rw [← Function.notMem_support]
  contrapose hx
  exact interior_subset (f_support hx)


/-- In a locally compact space, any function in `ℒp` can be approximated by compactly supported
continuous functions when `0 < p < ∞`, version in terms of `∫`. -/
/-
**MeasureTheory.MemLp.exists_hasCompactSupport_integral_rpow_sub_le** 是 Mathlib 
中的一个定理，位于命名空间 `MeasureTheory.MemLp`。
形式化陈述：∀ {α : Type u_1} [inst : TopologicalSpace α] [NormalSpace α] [inst_2 : Mea
surableSpace α] [BorelSpace α] {E : Type u_2}   [inst_4 : NormedAddCommGroup E] 
{μ : MeasureTheory.Measure α} [NormedSpace ℝ E] [R1Space α]   [WeaklyLocallyComp
actSpace α] [μ.Regular] {p : ℝ},   0 < p →     ∀ {f : α → E},       MeasureTheor
y.MemLp f (ENNReal.ofReal p) μ →         ∀ {ε : ℝ},           0 < ε →           
  ∃ g,               HasCompactSupport g ∧                 ∫ (x : α), ‖f x - g x
‖ ^ p ∂μ ≤ ε ∧ Continuous g ∧ MeasureTheory.MemLp g (ENNReal.ofReal p) μ
参数：ENNReal.ofReal p；x : α；ENNReal.ofReal p。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Real.rpow_pos_of_pos`：rpow_pos_of_pos {x : Real} (hx : 0 < x) (y : Real)
 : 0 < x ^ y
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `MeasureTheory.MemLp.exists_hasCompactSupport_eLpNorm_sub_le`：∀ {α : Type
 u_1} [inst : TopologicalSpace α] [NormalSpace α] [inst_2 : MeasurableSpace α] [
BorelSpace α] {E : Type u_2}   [inst_4 : NormedAd…
· 使用定理 `ENNReal.coe_ne_top`：coe_ne_top : (r : Real>=0∞) != ∞
· 使用定理 `Real.rpow_le_rpow_iff`：rpow_le_rpow_iff (hx : 0 <= x) (hy : 0 <= y) (hz 
: 0 < z) : x ^ z <= y ^ z ↔ x <= y
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
· 使用定理 `Real.rpow_nonneg`：rpow_nonneg {x : Real} (hx : 0 <= x) (y : Real) : 0 <=
 x ^ y
· 使用定理 `norm_nonneg`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (a : E), 0 ≤
 ‖a‖
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `inv_pos`：∀ {G₀ : Type u_3} [inst : GroupWithZero G₀] [inst_1 : PartialOr
der G₀] [PosMulReflectLT G₀] {a : G₀}, 0 < a⁻¹ ↔ 0 < a
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `ENNReal.toReal_ofReal`：toReal_ofReal {r : Real} (h : 0 <= r) : (ENNReal.
ofReal r).toReal = r
· 使用定理 `one_div`：one_div (a : G) : 1 / a = a⁻¹
· 使用定理 `ENNReal.ofReal_le_ofReal_iff`：ofReal_le_ofReal_iff {p q : Real} (h : 0 <
= q) : ENNReal.ofReal p <= ENNReal.ofReal q ↔ p <= q
· 使用定理 `MeasureTheory.MemLp.eLpNorm_eq_integral_rpow_norm`：∀ {α : Type u_1} {m :
 MeasurableSpace α} {μ : MeasureTheory.Measure α} {H : Type u_6} [inst : NormedA
ddCommGroup H]   {f : α → H} {p : ENNRe…
· 使用定理 `MeasureTheory.MemLp.sub`：∀ {α : Type u_1} {E : Type u_2} {m : Measurable
Space α} [inst : NormedAddCommGroup E] {p : ENNReal}   {μ : MeasureTheory.Measur
e α} {f g : α…

--- 原说明 ---
In a locally compact space, any function in `ℒp` can be approximated by compactl
y supported
continuous functions when `0 < p < ∞`, version in terms of `∫`.
-/
theorem MemLp.exists_hasCompactSupport_integral_rpow_sub_le
    [R1Space α] [WeaklyLocallyCompactSpace α] [μ.Regular]
    {p : ℝ} (hp : 0 < p) {f : α → E} (hf : MemLp f (ENNReal.ofReal p) μ) {ε : ℝ} (hε : 0 < ε) :
    ∃ g : α → E,
      HasCompactSupport g ∧
        (∫ x, ‖f x - g x‖ ^ p ∂μ) ≤ ε ∧ Continuous g ∧ MemLp g (ENNReal.ofReal p) μ := by
  have I : 0 < ε ^ (1 / p) := Real.rpow_pos_of_pos hε _
  have A : ENNReal.ofReal (ε ^ (1 / p)) ≠ 0 := by
    simp only [Ne, ENNReal.ofReal_eq_zero, not_le, I]
  have B : ENNReal.ofReal p ≠ 0 := by simpa only [Ne, ENNReal.ofReal_eq_zero, not_le] using hp
  rcases hf.exists_hasCompactSupport_eLpNorm_sub_le ENNReal.coe_ne_top A with
    ⟨g, g_support, hg, g_cont, g_mem⟩
  change eLpNorm _ (ENNReal.ofReal p) _ ≤ _ at hg
  refine ⟨g, g_support, ?_, g_cont, g_mem⟩
  rwa [(hf.sub g_mem).eLpNorm_eq_integral_rpow_norm B ENNReal.coe_ne_top,
    ENNReal.ofReal_le_ofReal_iff I.le, one_div, ENNReal.toReal_ofReal hp.le,
    Real.rpow_le_rpow_iff _ hε.le (inv_pos.2 hp)] at hg
  positivity


/-- In a locally compact space, any integrable function can be approximated by compactly supported
continuous functions, version in terms of `∫⁻`. -/
/-
**MeasureTheory.Integrable.exists_hasCompactSupport_lintegral_sub_le** 是 Mathlib
 中的一个定理，位于命名空间 `MeasureTheory.Integrable`。
形式化陈述：∀ {α : Type u_1} [inst : TopologicalSpace α] [NormalSpace α] [inst_2 : Mea
surableSpace α] [BorelSpace α] {E : Type u_2}   [inst_4 : NormedAddCommGroup E] 
{μ : MeasureTheory.Measure α} [NormedSpace ℝ E] [R1Space α]   [WeaklyLocallyComp
actSpace α] [μ.Regular] {f : α → E},   MeasureTheory.Integrable f μ →     ∀ {ε :
 ENNReal},       ε ≠ 0 → ∃ g, HasCompactSupport g ∧ ∫⁻ (x : α), ‖f x - g x‖ₑ ∂μ 
≤ ε ∧ Continuous g ∧ MeasureTheory.Integrable g μ
参数：x : α。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `MeasureTheory.MemLp.exists_hasCompactSupport_eLpNorm_sub_le`：∀ {α : Type
 u_1} [inst : TopologicalSpace α] [NormalSpace α] [inst_2 : MeasurableSpace α] [
BorelSpace α] {E : Type u_2}   [inst_4 : NormedAd…
· 使用定理 `ENNReal.one_ne_top`：1 ≠ ⊤

--- 原说明 ---
In a locally compact space, any integrable function can be approximated by compa
ctly supported
continuous functions, version in terms of `∫⁻`.
-/
theorem Integrable.exists_hasCompactSupport_lintegral_sub_le
    [R1Space α] [WeaklyLocallyCompactSpace α] [μ.Regular]
    {f : α → E} (hf : Integrable f μ) {ε : ℝ≥0∞} (hε : ε ≠ 0) :
    ∃ g : α → E,
      HasCompactSupport g ∧ ∫⁻ x, ‖f x - g x‖ₑ ∂μ ≤ ε ∧ Continuous g ∧ Integrable g μ := by
  simp only [← memLp_one_iff_integrable, ← eLpNorm_one_eq_lintegral_enorm] at hf ⊢
  exact hf.exists_hasCompactSupport_eLpNorm_sub_le ENNReal.one_ne_top hε

/-- In a locally compact space, any integrable function can be approximated by compactly supported
continuous functions, version in terms of `∫`. -/
/-
**MeasureTheory.Integrable.exists_hasCompactSupport_integral_sub_le** 是 Mathlib 
中的一个定理，位于命名空间 `MeasureTheory.Integrable`。
形式化陈述：∀ {α : Type u_1} [inst : TopologicalSpace α] [NormalSpace α] [inst_2 : Mea
surableSpace α] [BorelSpace α] {E : Type u_2}   [inst_4 : NormedAddCommGroup E] 
{μ : MeasureTheory.Measure α} [NormedSpace ℝ E] [R1Space α]   [WeaklyLocallyComp
actSpace α] [μ.Regular] {f : α → E},   MeasureTheory.Integrable f μ →     ∀ {ε :
 ℝ},       0 < ε → ∃ g, HasCompactSupport g ∧ ∫ (x : α), ‖f x - g x‖ ∂μ ≤ ε ∧ Co
ntinuous g ∧ MeasureTheory.Integrable g μ
参数：x : α。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `ENNReal.ofReal_one`：ENNReal.ofReal 1 = 1
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Real.rpow_one`：rpow_one (x : Real) : x ^ (1 : Real) = x
· 使用定理 `MeasureTheory.MemLp.exists_hasCompactSupport_integral_rpow_sub_le`：∀ {α 
: Type u_1} [inst : TopologicalSpace α] [NormalSpace α] [inst_2 : MeasurableSpac
e α] [BorelSpace α] {E : Type u_2}   [inst_4 : NormedAd…
· 使用定理 `zero_lt_one`：∀ {α : Type u_1} [inst : Zero α] [inst_1 : One α] [inst_2 :
 PartialOrder α] [ZeroLEOneClass α] [NeZero 1], 0 < 1
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α

--- 原说明 ---
In a locally compact space, any integrable function can be approximated by compa
ctly supported
continuous functions, version in terms of `∫`.
-/
theorem Integrable.exists_hasCompactSupport_integral_sub_le
    [R1Space α] [WeaklyLocallyCompactSpace α] [μ.Regular]
    {f : α → E} (hf : Integrable f μ) {ε : ℝ} (hε : 0 < ε) :
    ∃ g : α → E, HasCompactSupport g ∧ (∫ x, ‖f x - g x‖ ∂μ) ≤ ε ∧
      Continuous g ∧ Integrable g μ := by
  simp only [← memLp_one_iff_integrable, ← ENNReal.ofReal_one]
    at hf ⊢
  simpa using hf.exists_hasCompactSupport_integral_rpow_sub_le zero_lt_one hε

/-- Any function in `ℒp` can be approximated by bounded continuous functions when `p < ∞`,
version in terms of `eLpNorm`. -/
/-
**MeasureTheory.MemLp.exists_boundedContinuous_eLpNorm_sub_le** 是 Mathlib 中的一个定理
，位于命名空间 `MeasureTheory.MemLp`。
形式化陈述：∀ {α : Type u_1} [inst : TopologicalSpace α] [NormalSpace α] [inst_2 : Mea
surableSpace α] [BorelSpace α] {E : Type u_2}   [inst_4 : NormedAddCommGroup E] 
{μ : MeasureTheory.Measure α} {p : ENNReal} [NormedSpace ℝ E] [μ.WeaklyRegular],
   p ≠ ⊤ →     ∀ {f : α → E},       MeasureTheory.MemLp f p μ →         ∀ {ε : E
NNReal}, ε ≠ 0 → ∃ g, MeasureTheory.eLpNorm (f - ⇑g) p μ ≤ ε ∧ MeasureTheory.Mem
Lp (⇑g) p μ
参数：f - ⇑g；⇑g。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.MemLp.induction_dense`：∀ {α : Type u_1} {E : Type u_4} [in
st : MeasurableSpace α] [inst_1 : NormedAddCommGroup E] {p : ENNReal}   {μ : Mea
sureTheory.Measure α},   …
· 使用定理 `MeasureTheory.exists_Lp_half`：exists_Lp_half (p : Real>=0∞) {δ : Real>=0
∞} (hδ : δ != 0) : exists η : Real>=0∞, 0 < η ∧ forall (f g : α -> ε), AEStrongl
yMeasurable f μ ->…
· 使用定理 `MeasureTheory.exists_eLpNorm_indicator_le`：exists_eLpNorm_indicator_le (
hp : p != ∞) (c : E) {ε : Real>=0∞} (hε : ε != 0) : exists η : Real>=0, 0 < η ∧ 
forall s : Set α, μ s <= η -> e…
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `ENNReal.coe_pos`：∀ {r : NNReal}, 0 < ↑r ↔ 0 < r
· 使用定理 `MeasurableSet.exists_isClosed_sdiff_lt`：∀ {α : Type u_1} [inst : Measura
bleSpace α] {μ : MeasureTheory.Measure α} [inst_1 : TopologicalSpace α]   [Opens
MeasurableSpace α] [μ.Weakly…
· 使用定理 `BorelSpace.opensMeasurable`：∀ {α : Type u_6} [inst : TopologicalSpace α]
 [inst_1 : MeasurableSpace α] [BorelSpace α], OpensMeasurableSpace α
· 使用定理 `LT.lt.ne`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≠ b
· 使用定理 `LE.le.trans_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b 
→ b < c → a < c
· 使用定理 `MeasureTheory.measure_mono`：measure_mono (h : s subseteq t) : μ s <= μ t
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.eLpNorm_neg`：eLpNorm_neg (f : α -> F) (p : Real>=0∞) (μ : 
Measure α) : eLpNorm (-f) p μ = eLpNorm f p μ
· 使用定理 `neg_sub`：∀ {α : Type u_1} [inst : SubtractionMonoid α] (a b : α), -(a - 
b) = b - a
· 使用定理 `Set.indicator_sdiff`：∀ {α : Type u_1} {G : Type u_6} [inst : AddGroup G]
 {s t : Set α},   s ⊆ t → ∀ (f : α → G), (t \ s).indicator f = t.indicator f - s
.indicato…
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `MeasureTheory.exists_continuous_eLpNorm_sub_le_of_closed`：exists_continu
ous_eLpNorm_sub_le_of_closed [μ.OuterRegular] (hp : p != ∞) {s u : Set α} (s_clo
sed : IsClosed s) (u_open : IsOpen u) (hsu : s…
· 使用定理 `MeasureTheory.Measure.WeaklyRegular.toOuterRegular`：∀ {α : Type u_1} {in
st : MeasurableSpace α} {inst_1 : TopologicalSpace α} {μ : MeasureTheory.Measure
 α}   [self : μ.WeaklyRegular], μ.OuterR…
· 使用定理 `isOpen_univ`：∀ {X : Type u} [inst : TopologicalSpace X], IsOpen Set.univ
· 使用定理 `Set.subset_univ`：subset_univ (s : Set α) : s subseteq univ
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `sub_add_sub_cancel`：∀ {G : Type u_3} [inst : AddGroup G] (a b c : G), a 
- b + (b - c) = a - c
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `MeasureTheory.AEStronglyMeasurable.sub`：∀ {α : Type u_1} {β : Type u_2} 
[inst : TopologicalSpace β] {m m₀ : MeasurableSpace α} {μ : MeasureTheory.Measur
e α}   {f g : α → β} [inst_1…
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `MeasureTheory.MemLp.aestronglyMeasurable`：∀ {α : Type u_1} {ε : Type u_2
} {m0 : MeasurableSpace α} [inst : ENorm ε] {μ : MeasureTheory.Measure α}   [ins
t_1 : TopologicalSpace ε] {f :…
（共 41 条，此处仅展示前 30 条）

--- 原说明 ---
Any function in `ℒp` can be approximated by bounded continuous functions when `p
 < ∞`,
version in terms of `eLpNorm`.
-/
theorem MemLp.exists_boundedContinuous_eLpNorm_sub_le [μ.WeaklyRegular] (hp : p ≠ ∞) {f : α → E}
    (hf : MemLp f p μ) {ε : ℝ≥0∞} (hε : ε ≠ 0) :
    ∃ g : α →ᵇ E, eLpNorm (f - (g : α → E)) p μ ≤ ε ∧ MemLp g p μ := by
  suffices H :
      ∃ g : α → E, eLpNorm (f - g) p μ ≤ ε ∧ Continuous g ∧ MemLp g p μ ∧ IsBounded (range g) by
    rcases H with ⟨g, hg, g_cont, g_mem, g_bd⟩
    exact ⟨⟨⟨g, g_cont⟩, Metric.isBounded_range_iff.1 g_bd⟩, hg, g_mem⟩
  -- It suffices to check that the set of functions we consider approximates characteristic
  -- functions, is stable under addition and made of ae strongly measurable functions.
  -- First check the latter easy facts.
  apply hf.induction_dense hp _ _ _ _ hε
  rotate_left
  -- stability under addition
  · rintro f g ⟨f_cont, f_mem, f_bd⟩ ⟨g_cont, g_mem, g_bd⟩
    refine ⟨f_cont.add g_cont, f_mem.add g_mem, ?_⟩
    let f' : α →ᵇ E := ⟨⟨f, f_cont⟩, Metric.isBounded_range_iff.1 f_bd⟩
    let g' : α →ᵇ E := ⟨⟨g, g_cont⟩, Metric.isBounded_range_iff.1 g_bd⟩
    exact (f' + g').isBounded_range
  -- ae strong measurability
  · exact fun f ⟨_, h, _⟩ => h.aestronglyMeasurable
  -- We are left with approximating characteristic functions.
  -- This follows from `exists_continuous_eLpNorm_sub_le_of_closed`.
  intro c t ht htμ ε hε
  rcases exists_Lp_half E μ p hε with ⟨δ, δpos, hδ⟩
  obtain ⟨η, ηpos, hη⟩ :
      ∃ η : ℝ≥0, 0 < η ∧ ∀ s : Set α, μ s ≤ η → eLpNorm (s.indicator fun _x => c) p μ ≤ δ :=
    exists_eLpNorm_indicator_le hp c δpos.ne'
  have hη_pos' : (0 : ℝ≥0∞) < η := ENNReal.coe_pos.2 ηpos
  obtain ⟨s, st, s_closed, μs⟩ : ∃ s, s ⊆ t ∧ IsClosed s ∧ μ (t \ s) < η :=
    ht.exists_isClosed_sdiff_lt htμ.ne hη_pos'.ne'
  have hsμ : μ s < ∞ := (measure_mono st).trans_lt htμ
  have I1 : eLpNorm ((s.indicator fun _y => c) - t.indicator fun _y => c) p μ ≤ δ := by
    rw [← eLpNorm_neg, neg_sub, ← indicator_sdiff st]
    exact hη _ μs.le
  rcases exists_continuous_eLpNorm_sub_le_of_closed hp s_closed isOpen_univ (subset_univ _) hsμ.ne c
      δpos.ne' with
    ⟨f, f_cont, I2, f_bound, -, f_mem⟩
  have I3 : eLpNorm (f - t.indicator fun _y => c) p μ ≤ ε := by
    convert!
      (hδ _ _
          (f_mem.aestronglyMeasurable.sub
            (aestronglyMeasurable_const.indicator s_closed.measurableSet))
          ((aestronglyMeasurable_const.indicator s_closed.measurableSet).sub
            (aestronglyMeasurable_const.indicator ht))
          I2 I1).le using 2
    simp only [sub_add_sub_cancel]
  refine ⟨f, I3, f_cont, f_mem, ?_⟩
  exact (BoundedContinuousFunction.ofNormedAddCommGroup f f_cont _ f_bound).isBounded_range

/-- Any function in `ℒp` can be approximated by bounded continuous functions when `0 < p < ∞`,
version in terms of `∫`. -/
/-
**MeasureTheory.MemLp.exists_boundedContinuous_integral_rpow_sub_le** 是 Mathlib 
中的一个定理，位于命名空间 `MeasureTheory.MemLp`。
形式化陈述：∀ {α : Type u_1} [inst : TopologicalSpace α] [NormalSpace α] [inst_2 : Mea
surableSpace α] [BorelSpace α] {E : Type u_2}   [inst_4 : NormedAddCommGroup E] 
{μ : MeasureTheory.Measure α} [NormedSpace ℝ E] [μ.WeaklyRegular] {p : ℝ},   0 <
 p →     ∀ {f : α → E},       MeasureTheory.MemLp f (ENNReal.ofReal p) μ →      
   ∀ {ε : ℝ}, 0 < ε → ∃ g, ∫ (x : α), ‖f x - g x‖ ^ p ∂μ ≤ ε ∧ MeasureTheory.Mem
Lp (⇑g) (ENNReal.ofReal p) μ
参数：ENNReal.ofReal p；x : α；⇑g；ENNReal.ofReal p。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Real.rpow_pos_of_pos`：rpow_pos_of_pos {x : Real} (hx : 0 < x) (y : Real)
 : 0 < x ^ y
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `MeasureTheory.MemLp.exists_boundedContinuous_eLpNorm_sub_le`：∀ {α : Type
 u_1} [inst : TopologicalSpace α] [NormalSpace α] [inst_2 : MeasurableSpace α] [
BorelSpace α] {E : Type u_2}   [inst_4 : NormedAd…
· 使用定理 `ENNReal.coe_ne_top`：coe_ne_top : (r : Real>=0∞) != ∞
· 使用定理 `Real.rpow_le_rpow_iff`：rpow_le_rpow_iff (hx : 0 <= x) (hy : 0 <= y) (hz 
: 0 < z) : x ^ z <= y ^ z ↔ x <= y
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
· 使用定理 `Real.rpow_nonneg`：rpow_nonneg {x : Real} (hx : 0 <= x) (y : Real) : 0 <=
 x ^ y
· 使用定理 `norm_nonneg`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (a : E), 0 ≤
 ‖a‖
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `inv_pos`：∀ {G₀ : Type u_3} [inst : GroupWithZero G₀] [inst_1 : PartialOr
der G₀] [PosMulReflectLT G₀] {a : G₀}, 0 < a⁻¹ ↔ 0 < a
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `ENNReal.toReal_ofReal`：toReal_ofReal {r : Real} (h : 0 <= r) : (ENNReal.
ofReal r).toReal = r
· 使用定理 `one_div`：one_div (a : G) : 1 / a = a⁻¹
· 使用定理 `ENNReal.ofReal_le_ofReal_iff`：ofReal_le_ofReal_iff {p q : Real} (h : 0 <
= q) : ENNReal.ofReal p <= ENNReal.ofReal q ↔ p <= q
· 使用定理 `MeasureTheory.MemLp.eLpNorm_eq_integral_rpow_norm`：∀ {α : Type u_1} {m :
 MeasurableSpace α} {μ : MeasureTheory.Measure α} {H : Type u_6} [inst : NormedA
ddCommGroup H]   {f : α → H} {p : ENNRe…
· 使用定理 `MeasureTheory.MemLp.sub`：∀ {α : Type u_1} {E : Type u_2} {m : Measurable
Space α} [inst : NormedAddCommGroup E] {p : ENNReal}   {μ : MeasureTheory.Measur
e α} {f g : α…

--- 原说明 ---
Any function in `ℒp` can be approximated by bounded continuous functions when `0
 < p < ∞`,
version in terms of `∫`.
-/
theorem MemLp.exists_boundedContinuous_integral_rpow_sub_le [μ.WeaklyRegular] {p : ℝ} (hp : 0 < p)
    {f : α → E} (hf : MemLp f (ENNReal.ofReal p) μ) {ε : ℝ} (hε : 0 < ε) :
    ∃ g : α →ᵇ E, (∫ x, ‖f x - g x‖ ^ p ∂μ) ≤ ε ∧ MemLp g (ENNReal.ofReal p) μ := by
  have I : 0 < ε ^ (1 / p) := Real.rpow_pos_of_pos hε _
  have A : ENNReal.ofReal (ε ^ (1 / p)) ≠ 0 := by
    simp only [Ne, ENNReal.ofReal_eq_zero, not_le, I]
  have B : ENNReal.ofReal p ≠ 0 := by simpa only [Ne, ENNReal.ofReal_eq_zero, not_le] using hp
  rcases hf.exists_boundedContinuous_eLpNorm_sub_le ENNReal.coe_ne_top A with ⟨g, hg, g_mem⟩
  change eLpNorm _ (ENNReal.ofReal p) _ ≤ _ at hg
  refine ⟨g, ?_, g_mem⟩
  rwa [(hf.sub g_mem).eLpNorm_eq_integral_rpow_norm B ENNReal.coe_ne_top,
    ENNReal.ofReal_le_ofReal_iff I.le, one_div, ENNReal.toReal_ofReal hp.le,
    Real.rpow_le_rpow_iff _ hε.le (inv_pos.2 hp)] at hg
  positivity

/-- Any integrable function can be approximated by bounded continuous functions,
version in terms of `∫⁻`. -/
/-
**MeasureTheory.Integrable.exists_boundedContinuous_lintegral_sub_le** 是 Mathlib
 中的一个定理，位于命名空间 `MeasureTheory.Integrable`。
形式化陈述：∀ {α : Type u_1} [inst : TopologicalSpace α] [NormalSpace α] [inst_2 : Mea
surableSpace α] [BorelSpace α] {E : Type u_2}   [inst_4 : NormedAddCommGroup E] 
{μ : MeasureTheory.Measure α} [NormedSpace ℝ E] [μ.WeaklyRegular] {f : α → E},  
 MeasureTheory.Integrable f μ →     ∀ {ε : ENNReal}, ε ≠ 0 → ∃ g, ∫⁻ (x : α), ‖f
 x - g x‖ₑ ∂μ ≤ ε ∧ MeasureTheory.Integrable (⇑g) μ
参数：x : α；⇑g。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `MeasureTheory.MemLp.exists_boundedContinuous_eLpNorm_sub_le`：∀ {α : Type
 u_1} [inst : TopologicalSpace α] [NormalSpace α] [inst_2 : MeasurableSpace α] [
BorelSpace α] {E : Type u_2}   [inst_4 : NormedAd…
· 使用定理 `ENNReal.one_ne_top`：1 ≠ ⊤

--- 原说明 ---
Any integrable function can be approximated by bounded continuous functions,
version in terms of `∫⁻`.
-/
theorem Integrable.exists_boundedContinuous_lintegral_sub_le [μ.WeaklyRegular] {f : α → E}
    (hf : Integrable f μ) {ε : ℝ≥0∞} (hε : ε ≠ 0) :
    ∃ g : α →ᵇ E, ∫⁻ x, ‖f x - g x‖ₑ ∂μ ≤ ε ∧ Integrable g μ := by
  simp only [← memLp_one_iff_integrable, ← eLpNorm_one_eq_lintegral_enorm] at hf ⊢
  exact hf.exists_boundedContinuous_eLpNorm_sub_le ENNReal.one_ne_top hε

/-- Any integrable function can be approximated by bounded continuous functions,
version in terms of `∫`. -/
/-
**MeasureTheory.Integrable.exists_boundedContinuous_integral_sub_le** 是 Mathlib 
中的一个定理，位于命名空间 `MeasureTheory.Integrable`。
形式化陈述：∀ {α : Type u_1} [inst : TopologicalSpace α] [NormalSpace α] [inst_2 : Mea
surableSpace α] [BorelSpace α] {E : Type u_2}   [inst_4 : NormedAddCommGroup E] 
{μ : MeasureTheory.Measure α} [NormedSpace ℝ E] [μ.WeaklyRegular] {f : α → E},  
 MeasureTheory.Integrable f μ → ∀ {ε : ℝ}, 0 < ε → ∃ g, ∫ (x : α), ‖f x - g x‖ ∂
μ ≤ ε ∧ MeasureTheory.Integrable (⇑g) μ
参数：x : α；⇑g。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `ENNReal.ofReal_one`：ENNReal.ofReal 1 = 1
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Real.rpow_one`：rpow_one (x : Real) : x ^ (1 : Real) = x
· 使用定理 `MeasureTheory.MemLp.exists_boundedContinuous_integral_rpow_sub_le`：∀ {α 
: Type u_1} [inst : TopologicalSpace α] [NormalSpace α] [inst_2 : MeasurableSpac
e α] [BorelSpace α] {E : Type u_2}   [inst_4 : NormedAd…
· 使用定理 `zero_lt_one`：∀ {α : Type u_1} [inst : Zero α] [inst_1 : One α] [inst_2 :
 PartialOrder α] [ZeroLEOneClass α] [NeZero 1], 0 < 1
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α

--- 原说明 ---
Any integrable function can be approximated by bounded continuous functions,
version in terms of `∫`.
-/
theorem Integrable.exists_boundedContinuous_integral_sub_le [μ.WeaklyRegular] {f : α → E}
    (hf : Integrable f μ) {ε : ℝ} (hε : 0 < ε) :
    ∃ g : α →ᵇ E, (∫ x, ‖f x - g x‖ ∂μ) ≤ ε ∧ Integrable g μ := by
  simp only [← memLp_one_iff_integrable, ← ENNReal.ofReal_one]
    at hf ⊢
  simpa using hf.exists_boundedContinuous_integral_rpow_sub_le zero_lt_one hε

namespace Lp

variable (E μ)

/-- A function in `Lp` can be approximated in `Lp` by continuous functions. -/
/-
**MeasureTheory.Lp.boundedContinuousFunction_dense** 是 Mathlib 中的一个定理，位于命名空间 `Me
asureTheory.Lp`。
形式化陈述：boundedContinuousFunction_dense [SecondCountableTopologyEither α E] [Fact 
(1 <= p)] (hp : p != ∞) [μ.WeaklyRegular] : Dense (boundedContinuousFunction E p
 μ : Set (Lp E p μ))
参数：1 <= p；hp : p != ∞。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `mem_closure_iff_nhds_basis`：mem_closure_iff_nhds_basis {p : ι -> Prop} {
s : ι -> Set X} (h : (𝓝 x).HasBasis p s) : x in closure t ↔ forall i, p i -> exi
sts y in t, y in…
· 使用定理 `Metric.nhds_basis_closedEBall`：nhds_basis_closedEBall : (𝓝 x).HasBasis (
fun ε : Real>=0∞ => 0 < ε) (closedEBall x)
· 使用定理 `MeasureTheory.MemLp.exists_boundedContinuous_eLpNorm_sub_le`：∀ {α : Type
 u_1} [inst : TopologicalSpace α] [NormalSpace α] [inst_2 : MeasurableSpace α] [
BorelSpace α] {E : Type u_2}   [inst_4 : NormedAd…
· 使用定理 `MeasureTheory.Lp.memLp`：∀ {α : Type u_1} {E : Type u_4} {m : MeasurableS
pace α} {p : ENNReal} {μ : MeasureTheory.Measure α}   [inst : NormedAddCommGroup
 E] (f : ↥(M…
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Metric.mem_closedEBall'`：mem_closedEBall' : y in closedEBall x ε ↔ edist
 x y <= ε
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.Lp.toLp_coeFn`：toLp_coeFn (f : Lp E p μ) (hf : MemLp f p μ
) : hf.toLp f = f
· 使用定理 `MeasureTheory.Lp.edist_toLp_toLp`：edist_toLp_toLp (f g : α -> E) (hf : M
emLp f p μ) (hg : MemLp g p μ) : edist (hf.toLp f) (hg.toLp g) = eLpNorm (f - g)
 p μ

--- 原说明 ---
A function in `Lp` can be approximated in `Lp` by continuous functions.
-/
theorem boundedContinuousFunction_dense [SecondCountableTopologyEither α E] [Fact (1 ≤ p)]
    (hp : p ≠ ∞) [μ.WeaklyRegular] :
    Dense (boundedContinuousFunction E p μ : Set (Lp E p μ)) := by
  intro f
  refine (mem_closure_iff_nhds_basis Metric.nhds_basis_closedEBall).2 fun ε hε ↦ ?_
  obtain ⟨g, hg, g_mem⟩ :
      ∃ g : α →ᵇ E, eLpNorm ((f : α → E) - (g : α → E)) p μ ≤ ε ∧ MemLp g p μ :=
    (Lp.memLp f).exists_boundedContinuous_eLpNorm_sub_le hp hε.ne'
  refine ⟨g_mem.toLp _, ⟨g, rfl⟩, ?_⟩
  rwa [Metric.mem_closedEBall', ← Lp.toLp_coeFn f (Lp.memLp f), Lp.edist_toLp_toLp]

/-- A function in `Lp` can be approximated in `Lp` by continuous functions. -/
/-
**MeasureTheory.Lp.boundedContinuousFunction_topologicalClosure** 是 Mathlib 中的一个
定理，位于命名空间 `MeasureTheory.Lp`。
形式化陈述：boundedContinuousFunction_topologicalClosure [SecondCountableTopologyEithe
r α E] [Fact (1 <= p)] (hp : p != ∞) [μ.WeaklyRegular] : (boundedContinuousFunct
ion E p μ).topologicalClosure = ⊤
参数：1 <= p；hp : p != ∞。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SetLike.ext'`：ext' (h : (p : Set B) = q) : p = q
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `Dense.closure_eq`：∀ {X : Type u} [inst : TopologicalSpace X] {s : Set X}
, Dense s → closure s = Set.univ
· 使用定理 `MeasureTheory.Lp.boundedContinuousFunction_dense`：boundedContinuousFunct
ion_dense [SecondCountableTopologyEither α E] [Fact (1 <= p)] (hp : p != ∞) [μ.W
eaklyRegular] : Dense (boundedContinuo…

--- 原说明 ---
A function in `Lp` can be approximated in `Lp` by continuous functions.
-/
theorem boundedContinuousFunction_topologicalClosure [SecondCountableTopologyEither α E]
    [Fact (1 ≤ p)] (hp : p ≠ ∞) [μ.WeaklyRegular] :
    (boundedContinuousFunction E p μ).topologicalClosure = ⊤ :=
  SetLike.ext' <| (boundedContinuousFunction_dense E μ hp).closure_eq

end Lp

end MeasureTheory

variable [SecondCountableTopologyEither α E] [_i : Fact (1 ≤ p)]
variable (𝕜 : Type*) [NormedRing 𝕜] [Module 𝕜 E] [IsBoundedSMul 𝕜 E] [NormedSpace ℝ E]

variable (E) (μ)

namespace BoundedContinuousFunction

/-
**BoundedContinuousFunction.toLp_denseRange** 是 Mathlib 中的一个定理，位于命名空间 `BoundedCo
ntinuousFunction`。
形式化陈述：toLp_denseRange [μ.WeaklyRegular] [IsFiniteMeasure μ] (hp : p != ∞) : Dens
eRange (toLp p μ 𝕜 : (α ->ᵇ E) ->L[𝕜] Lp E p μ)
参数：hp : p != ∞。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `instBoundedAddOfLipschitzAdd`：∀ {R : Type u_1} [inst : PseudoMetricSpace
 R] [inst_1 : AddMonoid R] [LipschitzAdd R], BoundedAdd R
· 使用定理 `SeminormedAddCommGroup.to_lipschitzAdd`：∀ {E : Type u_2} [inst : Seminor
medAddCommGroup E], LipschitzAdd E
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `BoundedContinuousFunction.range_toLp`：range_toLp : (toLp p μ 𝕜 : (α ->ᵇ 
E) ->L[𝕜] Lp E p μ).range.toAddSubgroup = MeasureTheory.Lp.boundedContinuousFunc
tion E p μ
· 使用定理 `MeasureTheory.Lp.boundedContinuousFunction_dense`：boundedContinuousFunct
ion_dense [SecondCountableTopologyEither α E] [Fact (1 <= p)] (hp : p != ∞) [μ.W
eaklyRegular] : Dense (boundedContinuo…
-/
theorem toLp_denseRange [μ.WeaklyRegular] [IsFiniteMeasure μ] (hp : p ≠ ∞) :
    DenseRange (toLp p μ 𝕜 : (α →ᵇ E) →L[𝕜] Lp E p μ) := by
  simpa only [← range_toLp p μ (𝕜 := 𝕜)]
    using! MeasureTheory.Lp.boundedContinuousFunction_dense E μ hp

end BoundedContinuousFunction

namespace ContinuousMap

/-- Continuous functions are dense in `MeasureTheory.Lp`, `1 ≤ p < ∞`. This theorem assumes that
the domain is a compact space because otherwise `ContinuousMap.toLp` is undefined. Use
`BoundedContinuousFunction.toLp_denseRange` if the domain is not a compact space. -/
/-
**ContinuousMap.toLp_denseRange** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousMap`。
形式化陈述：toLp_denseRange [CompactSpace α] [μ.WeaklyRegular] [IsFiniteMeasure μ] (hp
 : p != ∞) : DenseRange (toLp p μ 𝕜 : C(α, E) ->L[𝕜] Lp E p μ)
参数：hp : p != ∞。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Dense.mono`：Dense.mono (h : s₁ subseteq s₂) (hd : Dense s₁) : Dense s₂
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `instBoundedAddOfLipschitzAdd`：∀ {R : Type u_1} [inst : PseudoMetricSpace
 R] [inst_1 : AddMonoid R] [LipschitzAdd R], BoundedAdd R
· 使用定理 `SeminormedAddCommGroup.to_lipschitzAdd`：∀ {E : Type u_2} [inst : Seminor
medAddCommGroup E], LipschitzAdd E
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.range_subset_iff`：range_subset_iff : range f subseteq s ↔ forall y, 
f y in s
· 使用定理 `BoundedContinuousFunction.toLp_denseRange`：toLp_denseRange [μ.WeaklyRegu
lar] [IsFiniteMeasure μ] (hp : p != ∞) : DenseRange (toLp p μ 𝕜 : (α ->ᵇ E) ->L[
𝕜] Lp E p μ)

--- 原说明 ---
Continuous functions are dense in `MeasureTheory.Lp`, `1 ≤ p < ∞`. This theorem 
assumes that
the domain is a compact space because otherwise `ContinuousMap.toLp` is undefine
d. Use
`BoundedContinuousFunction.toLp_denseRange` if the domain is not a compact space
.
-/
theorem toLp_denseRange [CompactSpace α] [μ.WeaklyRegular] [IsFiniteMeasure μ] (hp : p ≠ ∞) :
    DenseRange (toLp p μ 𝕜 : C(α, E) →L[𝕜] Lp E p μ) := by
  refine (BoundedContinuousFunction.toLp_denseRange _ _ 𝕜 hp).mono ?_
  refine range_subset_iff.2 fun f ↦ ?_
  exact ⟨f.toContinuousMap, rfl⟩

end ContinuousMap

