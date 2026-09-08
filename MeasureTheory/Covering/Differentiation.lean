/-
Copyright (c) 2021 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
module

public import Mathlib.MeasureTheory.Covering.VitaliFamily
public import Mathlib.MeasureTheory.Function.AEMeasurableOrder
public import Mathlib.MeasureTheory.Integral.Average
public import Mathlib.MeasureTheory.Measure.Decomposition.Lebesgue

/-!
# Differentiation of measures

On a second countable metric space with a measure `μ`, consider a Vitali family (i.e., for each `x`
one has a family of sets shrinking to `x`, with a good behavior with respect to covering theorems).
Consider also another measure `ρ`. Then, for almost every `x`, the ratio `ρ a / μ a` converges when
`a` shrinks to `x` along the Vitali family, towards the Radon-Nikodym derivative of `ρ` with
respect to `μ`. This is the main theorem on differentiation of measures.

This theorem is proved in this file, under the name `VitaliFamily.ae_tendsto_rnDeriv`. Note that,
almost surely, `μ a` is eventually positive and finite (see
`VitaliFamily.ae_eventually_measure_pos` and `VitaliFamily.eventually_measure_lt_top`), so the
ratio really makes sense.

For concrete applications, one needs concrete instances of Vitali families, as provided for instance
by `Besicovitch.vitaliFamily` (for balls) or by `Vitali.vitaliFamily` (for doubling measures).

Specific applications to Lebesgue density points and the Lebesgue differentiation theorem are also
derived:
* `VitaliFamily.ae_tendsto_measure_inter_div` states that, for almost every point `x ∈ s`,
  then `μ (s ∩ a) / μ a` tends to `1` as `a` shrinks to `x` along a Vitali family.
* `VitaliFamily.ae_tendsto_average_norm_sub` states that, for almost every point `x`, then the
  average of `y ↦ ‖f y - f x‖` on `a` tends to `0` as `a` shrinks to `x` along a Vitali family.

## Sketch of proof

Let `v` be a Vitali family for `μ`. Assume for simplicity that `ρ` is absolutely continuous with
respect to `μ`, as the case of a singular measure is easier.

It is easy to see that a set `s` on which `liminf ρ a / μ a < q` satisfies `ρ s ≤ q * μ s`, by using
a disjoint subcovering provided by the definition of Vitali families. Similarly for the limsup.
It follows that a set on which `ρ a / μ a` oscillates has measure `0`, and therefore that
`ρ a / μ a` converges almost surely (`VitaliFamily.ae_tendsto_div`). Moreover, on a set where the
limit is close to a constant `c`, one gets `ρ s ∼ c μ s`, using again a covering lemma as above.
It follows that `ρ` is equal to `μ.withDensity (v.limRatio ρ x)`, where `v.limRatio ρ x` is the
limit of `ρ a / μ a` at `x` (which is well defined almost everywhere). By uniqueness of the
Radon-Nikodym derivative, one gets `v.limRatio ρ x = ρ.rnDeriv μ x` almost everywhere, completing
the proof.

There is a difficulty in this sketch: this argument works well when `v.limRatio ρ` is measurable,
but there is no guarantee that this is the case, especially if one doesn't make further assumptions
on the Vitali family. We use an indirect argument to show that `v.limRatio ρ` is always
almost everywhere measurable, again based on the disjoint subcovering argument
(see `VitaliFamily.exists_measurable_supersets_limRatio`), and then proceed as sketched above
but replacing `v.limRatio ρ` by a measurable version called `v.limRatioMeas ρ`.

## Counterexample

The standing assumption in this file is that spaces are second countable. Without this assumption,
measures may be zero locally but nonzero globally, which is not compatible with differentiation
theory (which deduces global information from local one). Here is an example displaying this
behavior.

Define a measure `μ` by `μ s = 0` if `s` is covered by countably many balls of radius `1`,
and `μ s = ∞` otherwise. This is indeed a countably additive measure, which is moreover
locally finite and doubling at small scales. It vanishes on every ball of radius `1`, so all the
quantities in differentiation theory (defined as ratios of measures as the radius tends to zero)
make no sense. However, the measure is not globally zero if the space is big enough.

## References

* [Herbert Federer, Geometric Measure Theory, Chapter 2.9][Federer1996]
-/

@[expose] public section

open MeasureTheory Metric Set Filter TopologicalSpace MeasureTheory.Measure

open scoped Filter ENNReal MeasureTheory NNReal Topology

variable {α : Type*} [PseudoMetricSpace α] {m0 : MeasurableSpace α} {μ : Measure α}
  (v : VitaliFamily μ)
  {E : Type*} [NormedAddCommGroup E]

namespace VitaliFamily

/-- The limit along a Vitali family of `ρ a / μ a` where it makes sense, and garbage otherwise.
Do *not* use this definition: it is only a temporary device to show that this ratio tends almost
everywhere to the Radon-Nikodym derivative. -/
/-
**VitaliFamily.limRatio** 是 Mathlib 中的一个定义，位于命名空间 `VitaliFamily`。
形式化陈述：limRatio (ρ : Measure α) (x : α) : Real>=0∞
参数：ρ : Measure α；x : α。
该定义给出了一等式。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α

--- 原说明 ---
The limit along a Vitali family of `ρ a / μ a` where it makes sense, and garbage
 otherwise.
Do *not* use this definition: it is only a temporary device to show that this ra
tio tends almost
everywhere to the Radon-Nikodym derivative.
-/
noncomputable def limRatio (ρ : Measure α) (x : α) : ℝ≥0∞ :=
  limUnder (v.filterAt x) fun a => ρ a / μ a

/-- For almost every point `x`, sufficiently small sets in a Vitali family around `x` have positive
measure. (This is a nontrivial result, following from the covering property of Vitali families). -/
/-
**VitaliFamily.ae_eventually_measure_pos** 是 Mathlib 中的一个定理，位于命名空间 `VitaliFamily
`。
形式化陈述：ae_eventually_measure_pos [SecondCountableTopology α] : forallᵐ x ∂μ, fora
llᶠ a in v.filterAt x, 0 < μ a
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `instIsBotZeroClass`：∀ {α : Type u} [inst : AddZeroClass α] [inst_1 : LE 
α] [CanonicallyOrderedAdd α], IsBotZeroClass α
· 使用定理 `ENNReal.instCanonicallyOrderedAdd`：CanonicallyOrderedAdd ENNReal
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `VitaliFamily.FineSubfamilyOn.measure_le_tsum`：measure_le_tsum [SecondCou
ntableTopology X] : μ s <= ∑' x : h.index, μ (h.covering x)
· 使用定理 `VitaliFamily.FineSubfamilyOn.covering_mem`：covering_mem {p : X × Set X} 
(hp : p in h.index) : h.covering p in f p.1
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `tsum_zero`：∀ {α : Type u_1} {β : Type u_2} [inst : AddCommMonoid α] [ins
t_1 : TopologicalSpace α] {L : SummationFilter β},   ∑'[L] (x : β), 0 = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `bot_le`：∀ {α : Type u} [inst : LE α] [inst_1 : OrderBot α] {a : α}, ⊥ ≤ 
a

--- 原说明 ---
For almost every point `x`, sufficiently small sets in a Vitali family around `x
` have positive
measure. (This is a nontrivial result, following from the covering property of V
itali families).
-/
theorem ae_eventually_measure_pos [SecondCountableTopology α] :
    ∀ᵐ x ∂μ, ∀ᶠ a in v.filterAt x, 0 < μ a := by
  set s := {x | ¬∀ᶠ a in v.filterAt x, 0 < μ a} with hs
  simp -zeta only [not_lt, not_eventually, nonpos_iff_eq_zero] at hs
  change μ s = 0
  let f : α → Set (Set α) := fun _ => {a | μ a = 0}
  have h : v.FineSubfamilyOn f s := by
    intro x hx ε εpos
    rw [hs] at hx
    simp only [frequently_filterAt_iff, gt_iff_lt, mem_ofPred_eq] at hx
    rcases hx ε εpos with ⟨a, a_sets, ax, μa⟩
    exact ⟨a, ⟨a_sets, μa⟩, ax⟩
  refine le_antisymm ?_ bot_le
  calc
    μ s ≤ ∑' x : h.index, μ (h.covering x) := h.measure_le_tsum
    _ = ∑' x : h.index, 0 := by congr; ext1 x; exact h.covering_mem x.2
    _ = 0 := by simp only [tsum_zero]

/-- For every point `x`, sufficiently small sets in a Vitali family around `x` have finite measure.
(This is a trivial result, following from the fact that the measure is locally finite). -/
/-
**VitaliFamily.eventually_measure_lt_top** 是 Mathlib 中的一个定理，位于命名空间 `VitaliFamily
`。
形式化陈述：eventually_measure_lt_top [IsLocallyFiniteMeasure μ] (x : α) : forallᶠ a i
n v.filterAt x, μ a < ∞
参数：x : α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.Eventually.filter_mono`：∀ {α : Type u} {f₁ f₂ : Filter α}, f₁ ≤ f
₂ → ∀ {p : α → Prop}, (∀ᶠ (x : α) in f₂, p x) → ∀ᶠ (x : α) in f₁, p x
· 使用定理 `inf_le_left`：∀ {α : Type u} [inst : SemilatticeInf α] {a b : α}, a ⊓ b ≤
 a
· 使用定理 `MeasureTheory.Measure.FiniteAtFilter.eventually`：∀ {α : Type u_1} {m0 : 
MeasurableSpace α} {μ : MeasureTheory.Measure α} {f : Filter α},   μ.FiniteAtFil
ter f → ∀ᶠ (s : Set α) in f.smallSets…
· 使用定理 `MeasureTheory.Measure.finiteAt_nhds`：∀ {α : Type u_1} {m0 : MeasurableSp
ace α} [inst : TopologicalSpace α] (μ : MeasureTheory.Measure α)   [MeasureTheor
y.IsLocallyFiniteMeasure …

--- 原说明 ---
For every point `x`, sufficiently small sets in a Vitali family around `x` have 
finite measure.
(This is a trivial result, following from the fact that the measure is locally f
inite).
-/
theorem eventually_measure_lt_top [IsLocallyFiniteMeasure μ] (x : α) :
    ∀ᶠ a in v.filterAt x, μ a < ∞ :=
  (μ.finiteAt_nhds x).eventually.filter_mono inf_le_left

/-- If two measures `ρ` and `ν` have, at every point of a set `s`, arbitrarily small sets in a
Vitali family satisfying `ρ a ≤ ν a`, then `ρ s ≤ ν s` if `ρ ≪ μ`. -/
/-
**VitaliFamily.measure_le_of_frequently_le** 是 Mathlib 中的一个定理，位于命名空间 `VitaliFami
ly`。
形式化陈述：measure_le_of_frequently_le [SecondCountableTopology α] [BorelSpace α] {ρ 
: Measure α} (ν : Measure α) [IsLocallyFiniteMeasure ν] (hρ : ρ ≪ μ) (s : Set α)
 (hs : forall x in s, existsᶠ a in v.filterAt x, ρ a <= ν a) : ρ s <= ν s
参数：ν : Measure α；hρ : ρ ≪ μ；s : Set α；hs : forall x in s, existsᶠ a in v.filterA
t x, ρ a <= ν a。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ENNReal.le_of_forall_pos_le_add`：le_of_forall_pos_le_add (h : forall ε :
 Real>=0, 0 < ε -> b < ∞ -> a <= b + ε) : a <= b
· 使用定理 `Set.exists_isOpen_le_add`：∀ {α : Type u_1} [inst : MeasurableSpace α] [i
nst_1 : TopologicalSpace α] (A : Set α) (μ : MeasureTheory.Measure α)   [μ.Outer
Regular] {ε : …
· 使用定理 `MeasureTheory.Measure.WeaklyRegular.toOuterRegular`：∀ {α : Type u_1} {in
st : MeasurableSpace α} {inst_1 : TopologicalSpace α} {μ : MeasureTheory.Measure
 α}   [self : μ.WeaklyRegular], μ.OuterR…
· 使用定理 `MeasureTheory.Measure.WeaklyRegular.of_pseudoMetrizableSpace_secondCount
able_of_locallyFinite`：∀ {X : Type u_3} [inst : TopologicalSpace X] [Topological
Space.PseudoMetrizableSpace X] [SecondCountableTopology X]   [inst_3 : Measurabl
eSp…
· 使用定理 `PseudoEMetricSpace.pseudoMetrizableSpace`：∀ {α : Type u_2} [inst : Pseud
oEMetricSpace α], TopologicalSpace.PseudoMetrizableSpace α
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `ENNReal.coe_pos`：∀ {r : NNReal}, 0 < ↑r ↔ 0 < r
· 使用定理 `VitaliFamily.fineSubfamilyOn_of_frequently`：fineSubfamilyOn_of_frequentl
y (v : VitaliFamily μ) (f : X -> Set (Set X)) (s : Set X) (h : forall x in s, ex
istsᶠ t in v.filterAt x, t in f …
· 使用定理 `Filter.Frequently.and_eventually`：∀ {α : Type u} {p q : α → Prop} {f : F
ilter α},   (∃ᶠ (x : α) in f, p x) → (∀ᶠ (x : α) in f, q x) → ∃ᶠ (x : α) in f, p
 x ∧ q x
· 使用定理 `Filter.Eventually.and`：∀ {α : Type u} {p q : α → Prop} {f : Filter α},  
 Filter.Eventually p f → Filter.Eventually q f → ∀ᶠ (x : α) in f, p x ∧ q x
· 使用定理 `VitaliFamily.eventually_filterAt_mem_setsAt`：eventually_filterAt_mem_set
sAt (x : X) : forallᶠ t in v.filterAt x, t in v.setsAt x
· 使用定理 `VitaliFamily.eventually_filterAt_subset_of_nhds`：eventually_filterAt_sub
set_of_nhds {x : X} {o : Set X} (hx : o in 𝓝 x) : forallᶠ t in v.filterAt x, t s
ubseteq o
· 使用定理 `IsOpen.mem_nhds`：IsOpen.mem_nhds (hs : IsOpen s) (hx : x in s) : s in 𝓝 
x
· 使用定理 `Filter.Frequently.mono`：∀ {α : Type u} {p q : α → Prop} {f : Filter α}, 
(∃ᶠ (x : α) in f, p x) → (∀ (x : α), p x → q x) → ∃ᶠ (x : α) in f, q x
· 使用定理 `VitaliFamily.FineSubfamilyOn.index_countable`：index_countable [SecondCou
ntableTopology X] : h.index.Countable
· 使用定理 `VitaliFamily.FineSubfamilyOn.measure_le_tsum_of_absolutelyContinuous`：me
asure_le_tsum_of_absolutelyContinuous [SecondCountableTopology X] {ρ : Measure X
} (hρ : ρ ≪ μ) : ρ s <= ∑' p : h.index, ρ (h.covering p)
· 使用定理 `ENNReal.tsum_le_tsum`：∀ {α : Type u_1} {f g : α → ENNReal}, (∀ (a : α), 
f a ≤ g a) → ∑' (a : α), f a ≤ ∑' (a : α), g a
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `VitaliFamily.FineSubfamilyOn.covering_mem`：covering_mem {p : X × Set X} 
(hp : p in h.index) : h.covering p in f p.1
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.measure_iUnion`：measure_iUnion {m0 : MeasurableSpace α} {μ
 : Measure α} [Countable ι] {f : ι -> Set α} (hn : Pairwise (Disjoint on f)) (h 
: forall i, Measur…
· 使用定理 `Encodable.countable`：∀ {α : Type u_1} [Encodable α], Countable α
· 使用定理 `VitaliFamily.FineSubfamilyOn.covering_disjoint_subtype`：covering_disjoin
t_subtype : Pairwise (Disjoint on fun x : h.index => h.covering x)
· 使用定理 `VitaliFamily.FineSubfamilyOn.measurableSet_u`：∀ {X : Type u_1} [inst : P
seudoMetricSpace X] {m0 : MeasurableSpace X} {μ : MeasureTheory.Measure X}   {v 
: VitaliFamily μ} {f : X → Set (Se…
· 使用定理 `MeasureTheory.measure_mono`：measure_mono (h : s subseteq t) : μ s <= μ t
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `Set.iUnion_subset`：iUnion_subset {s : ι -> Set α} {t : Set α} (h : foral
l i, s i subseteq t) : ⋃ i, s i subseteq t
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b

--- 原说明 ---
If two measures `ρ` and `ν` have, at every point of a set `s`, arbitrarily small
 sets in a
Vitali family satisfying `ρ a ≤ ν a`, then `ρ s ≤ ν s` if `ρ ≪ μ`.
-/
theorem measure_le_of_frequently_le [SecondCountableTopology α] [BorelSpace α] {ρ : Measure α}
    (ν : Measure α) [IsLocallyFiniteMeasure ν] (hρ : ρ ≪ μ) (s : Set α)
    (hs : ∀ x ∈ s, ∃ᶠ a in v.filterAt x, ρ a ≤ ν a) : ρ s ≤ ν s := by
  -- this follows from a covering argument using the sets satisfying `ρ a ≤ ν a`.
  apply ENNReal.le_of_forall_pos_le_add fun ε εpos _ => ?_
  obtain ⟨U, sU, U_open, νU⟩ : ∃ (U : Set α), s ⊆ U ∧ IsOpen U ∧ ν U ≤ ν s + ε :=
    exists_isOpen_le_add s ν (ENNReal.coe_pos.2 εpos).ne'
  let f : α → Set (Set α) := fun _ => {a | ρ a ≤ ν a ∧ a ⊆ U}
  have h : v.FineSubfamilyOn f s := by
    apply v.fineSubfamilyOn_of_frequently f s fun x hx => ?_
    have :=
      (hs x hx).and_eventually
        ((v.eventually_filterAt_mem_setsAt x).and
          (v.eventually_filterAt_subset_of_nhds (U_open.mem_nhds (sU hx))))
    apply Frequently.mono this
    rintro a ⟨ρa, _, aU⟩
    exact ⟨ρa, aU⟩
  have : Encodable h.index := h.index_countable.toEncodable
  calc
    ρ s ≤ ∑' x : h.index, ρ (h.covering x) := h.measure_le_tsum_of_absolutelyContinuous hρ
    _ ≤ ∑' x : h.index, ν (h.covering x) := ENNReal.tsum_le_tsum fun x => (h.covering_mem x.2).1
    _ = ν (⋃ x : h.index, h.covering x) := by
      rw [measure_iUnion h.covering_disjoint_subtype fun i => h.measurableSet_u i.2]
    _ ≤ ν U := (measure_mono (iUnion_subset fun i => (h.covering_mem i.2).2))
    _ ≤ ν s + ε := νU
/-
**VitaliFamily.eventually_filterAt_integrableOn** 是 Mathlib 中的一个定理，位于命名空间 `Vital
iFamily`。
形式化陈述：eventually_filterAt_integrableOn (x : α) {f : α -> E} (hf : LocallyIntegra
ble f μ) : forallᶠ a in v.filterAt x, IntegrableOn f a μ
参数：x : α；hf : LocallyIntegrable f μ。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `VitaliFamily.eventually_filterAt_subset_of_nhds`：eventually_filterAt_sub
set_of_nhds {x : X} {o : Set X} (hx : o in 𝓝 x) : forallᶠ t in v.filterAt x, t s
ubseteq o
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `MeasureTheory.IntegrableOn.mono_set`：∀ {α : Type u_1} {ε : Type u_3} {mα
 : MeasurableSpace α} {f : α → ε} {s t : Set α} {μ : MeasureTheory.Measure α}   
[inst : TopologicalSpace …
-/
theorem eventually_filterAt_integrableOn (x : α) {f : α → E} (hf : LocallyIntegrable f μ) :
    ∀ᶠ a in v.filterAt x, IntegrableOn f a μ := by
  rcases hf x with ⟨w, w_nhds, hw⟩
  filter_upwards [v.eventually_filterAt_subset_of_nhds w_nhds] with a ha
  exact hw.mono_set ha

section

variable [SecondCountableTopology α] [BorelSpace α] [IsLocallyFiniteMeasure μ] {ρ : Measure α}
  [IsLocallyFiniteMeasure ρ]

/-- If a measure `ρ` is singular with respect to `μ`, then for `μ` almost every `x`, the ratio
`ρ a / μ a` tends to zero when `a` shrinks to `x` along the Vitali family. This makes sense
as `μ a` is eventually positive by `ae_eventually_measure_pos`. -/
/-
**VitaliFamily.ae_eventually_measure_zero_of_singular** 是 Mathlib 中的一个定理，位于命名空间 
`VitaliFamily`。
形式化陈述：ae_eventually_measure_zero_of_singular (hρ : ρ ⟂ₘ μ) : forallᵐ x ∂μ, Tends
to (fun a => ρ a / μ a) (v.filterAt x) (𝓝 0)
参数：hρ : ρ ⟂ₘ μ。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.inter_union_compl`：inter_union_compl (s t : Set α) : s inter t union
 s inter tᶜ = s
· 使用定理 `MeasureTheory.measure_mono`：measure_mono (h : s subseteq t) : μ s <= μ t
· 使用定理 `Set.union_subset_union`：union_subset_union {s₁ s₂ t₁ t₂ : Set α} (h₁ : s
₁ subseteq s₂) (h₂ : t₁ subseteq t₂) : s₁ union t₁ subseteq s₂ union t₂
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `Set.inter_subset_right`：inter_subset_right {s t : Set α} : s inter t sub
seteq t
· 使用定理 `MeasureTheory.measure_union_le`：measure_union_le (s t : Set α) : μ (s un
ion t) <= μ s + μ t
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `ENNReal.mul_inv_cancel`：∀ {a : ENNReal}, a ≠ 0 → a ≠ ⊤ → a * a⁻¹ = 1
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `ENNReal.coe_pos`：∀ {r : NNReal}, 0 < ↑r ↔ 0 < r
· 使用定理 `ENNReal.coe_ne_top`：coe_ne_top : (r : Real>=0∞) != ∞
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `mul_le_mul'`：mul_le_mul' [MulLeftMono α] [MulRightMono α] {a b c d : α} 
(h₁ : a <= b) (h₂ : c <= d) : a * c <= b * d
· 使用定理 `IsOrderedMonoid.toMulLeftMono`：∀ {α : Type u_1} [inst : CommMonoid α] [i
nst_1 : Preorder α] [IsOrderedMonoid α], MulLeftMono α
· 使用定理 `ENNReal.instIsOrderedMonoid`：IsOrderedMonoid ENNReal
· 使用定理 `VitaliFamily.measure_le_of_frequently_le`：measure_le_of_frequently_le [S
econdCountableTopology α] [BorelSpace α] {ρ : Measure α} (ν : Measure α) [IsLoca
llyFiniteMeasure ν] (hρ : ρ ≪ …
· 使用引理 `MeasureTheory.Measure.smul_absolutelyContinuous`：smul_absolutelyContinuo
us {c : Real>=0∞} : c • μ ≪ μ
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `bot_le`：∀ {α : Type u} [inst : LE α] [inst_1 : OrderBot α] {a : α}, ⊥ ≤ 
a
（共 60 条，此处仅展示前 30 条）

--- 原说明 ---
If a measure `ρ` is singular with respect to `μ`, then for `μ` almost every `x`,
 the ratio
`ρ a / μ a` tends to zero when `a` shrinks to `x` along the Vitali family. This 
makes sense
as `μ a` is eventually positive by `ae_eventually_measure_pos`.
-/
theorem ae_eventually_measure_zero_of_singular (hρ : ρ ⟂ₘ μ) :
    ∀ᵐ x ∂μ, Tendsto (fun a => ρ a / μ a) (v.filterAt x) (𝓝 0) := by
  have A : ∀ ε > (0 : ℝ≥0), ∀ᵐ x ∂μ, ∀ᶠ a in v.filterAt x, ρ a < ε * μ a := by
    intro ε εpos
    set s := {x | ¬∀ᶠ a in v.filterAt x, ρ a < ε * μ a} with hs
    change μ s = 0
    obtain ⟨o, _, ρo, μo⟩ : ∃ o : Set α, MeasurableSet o ∧ ρ o = 0 ∧ μ oᶜ = 0 := hρ
    apply le_antisymm _ bot_le
    calc
      μ s ≤ μ (s ∩ o ∪ oᶜ) := by
        conv_lhs => rw [← inter_union_compl s o]
        gcongr
        apply inter_subset_right
      _ ≤ μ (s ∩ o) + μ oᶜ := measure_union_le _ _
      _ = μ (s ∩ o) := by rw [μo, add_zero]
      _ = (ε : ℝ≥0∞)⁻¹ * (ε • μ) (s ∩ o) := by
        simp only [coe_nnreal_smul_apply, ← mul_assoc, mul_comm _ (ε : ℝ≥0∞)]
        rw [ENNReal.mul_inv_cancel (ENNReal.coe_pos.2 εpos).ne' ENNReal.coe_ne_top, one_mul]
      _ ≤ (ε : ℝ≥0∞)⁻¹ * ρ (s ∩ o) := by
        gcongr _ * ?_
        refine v.measure_le_of_frequently_le ρ smul_absolutelyContinuous _ ?_
        intro x hx
        rw [hs] at hx
        simp only [mem_inter_iff, not_lt, not_eventually, mem_ofPred_eq] at hx
        exact hx.1
      _ ≤ (ε : ℝ≥0∞)⁻¹ * ρ o := by gcongr; apply inter_subset_right
      _ = 0 := by rw [ρo, mul_zero]
  obtain ⟨u, _, u_pos, u_lim⟩ :
    ∃ u : ℕ → ℝ≥0, StrictAnti u ∧ (∀ n : ℕ, 0 < u n) ∧ Tendsto u atTop (𝓝 0) :=
    exists_seq_strictAnti_tendsto (0 : ℝ≥0)
  have B : ∀ᵐ x ∂μ, ∀ n, ∀ᶠ a in v.filterAt x, ρ a < u n * μ a :=
    ae_all_iff.2 fun n => A (u n) (u_pos n)
  filter_upwards [B, v.ae_eventually_measure_pos]
  intro x hx h'x
  refine tendsto_order.2 ⟨fun z hz => (ENNReal.not_lt_zero hz).elim, fun z hz => ?_⟩
  obtain ⟨w, w_pos, w_lt⟩ : ∃ w : ℝ≥0, (0 : ℝ≥0∞) < w ∧ (w : ℝ≥0∞) < z :=
    ENNReal.lt_iff_exists_nnreal_btwn.1 hz
  obtain ⟨n, hn⟩ : ∃ n, u n < w := ((tendsto_order.1 u_lim).2 w (ENNReal.coe_pos.1 w_pos)).exists
  filter_upwards [hx n, h'x, v.eventually_measure_lt_top x]
  intro a ha μa_pos μa_lt_top
  grw [ENNReal.div_lt_iff (.inl μa_pos.ne') (.inl μa_lt_top.ne), ha, hn, w_lt]

section AbsolutelyContinuous

variable (hρ : ρ ≪ μ)
include hρ

/-- A set of points `s` satisfying both `ρ a ≤ c * μ a` and `ρ a ≥ d * μ a` at arbitrarily small
sets in a Vitali family has measure `0` if `c < d`. Indeed, the first inequality should imply
that `ρ s ≤ c * μ s`, and the second one that `ρ s ≥ d * μ s`, a contradiction if `0 < μ s`. -/
/-
**VitaliFamily.null_of_frequently_le_of_frequently_ge** 是 Mathlib 中的一个定理，位于命名空间 
`VitaliFamily`。
形式化陈述：null_of_frequently_le_of_frequently_ge {c d : Real>=0} (hcd : c < d) (s : 
Set α) (hc : forall x in s, existsᶠ a in v.filterAt x, ρ a <= c * μ a) (hd : for
all x in s, existsᶠ a in v.filterAt x, (d : Real>=0∞) * μ a <= ρ a) : μ s = 0
参数：hcd : c < d；s : Set α；hc : forall x in s, existsᶠ a in v.filterAt x, ρ a <= c
 * μ a；hd : forall x in s, existsᶠ a in v.filterAt x, (d : Real>=0∞) * μ a <= ρ 
a。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.measure_null_of_locally_null`：measure_null_of_locally_null
 [TopologicalSpace α] [SecondCountableTopology α] (s : Set α) (hs : forall x in 
s, exists u in 𝓝[s] x, μ u = 0) …
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `MeasureTheory.Measure.exists_isOpen_measure_lt_top`：∀ {α : Type u_1} {m0
 : MeasurableSpace α} [inst : TopologicalSpace α] (μ : MeasureTheory.Measure α) 
  [MeasureTheory.IsLocallyFiniteMeasure …
· 使用定理 `inter_mem_nhdsWithin`：inter_mem_nhdsWithin (s : Set α) {t : Set α} {a : 
α} (h : t in 𝓝 a) : s inter t in 𝓝[s] a
· 使用定理 `IsOpen.mem_nhds`：IsOpen.mem_nhds (hs : IsOpen s) (hx : x in s) : s in 𝓝 
x
· 使用定理 `Decidable.byContradiction`：∀ {p : Prop} [dec : Decidable p], (¬p → False
) → p
· 使用引理 `lt_irrefl`：lt_irrefl (a : α) : ¬a < a
· 使用定理 `VitaliFamily.measure_le_of_frequently_le`：measure_le_of_frequently_le [S
econdCountableTopology α] [BorelSpace α] {ρ : Measure α} (ν : Measure α) [IsLoca
llyFiniteMeasure ν] (hρ : ρ ≪ …
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `ENNReal.mul_lt_mul_left`：∀ {a b c : ENNReal}, a ≠ 0 → a ≠ ⊤ → b < c → b 
* a < c * a
· 使用定理 `ne_of_gt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `lt_of_le_of_ne'`：∀ {α : Type u_1} [inst : PartialOrder α] {a b : α}, b ≤
 a → a ≠ b → b < a
· 使用定理 `zero_le`：∀ {α : Type u_1} [inst : LE α] [inst_1 : Zero α] [IsBotZeroClas
s α] {a : α}, 0 ≤ a
· 使用定理 `instIsBotZeroClass`：∀ {α : Type u} [inst : AddZeroClass α] [inst_1 : LE 
α] [CanonicallyOrderedAdd α], IsBotZeroClass α
· 使用定理 `ENNReal.instCanonicallyOrderedAdd`：CanonicallyOrderedAdd ENNReal
· 使用定理 `MeasureTheory.measure_ne_top_of_subset`：measure_ne_top_of_subset (h : t 
subseteq s) (ht : μ s != ∞) : μ t != ∞
· 使用定理 `Set.inter_subset_right`：inter_subset_right {s t : Set α} : s inter t sub
seteq t
· 使用定理 `LT.lt.ne`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≠ b
· 使用定理 `ENNReal.coe_lt_coe._gcongr_2`：∀ {r q : NNReal}, r < q → ↑r < ↑q
· 使用引理 `MeasureTheory.Measure.smul_absolutelyContinuous`：smul_absolutelyContinuo
us {c : Real>=0∞} : c • μ ≪ μ

--- 原说明 ---
A set of points `s` satisfying both `ρ a ≤ c * μ a` and `ρ a ≥ d * μ a` at arbit
rarily small
sets in a Vitali family has measure `0` if `c < d`. Indeed, the first inequality
 should imply
that `ρ s ≤ c * μ s`, and the second one that `ρ s ≥ d * μ s`, a contradiction i
f `0 < μ s`.
-/
theorem null_of_frequently_le_of_frequently_ge {c d : ℝ≥0} (hcd : c < d) (s : Set α)
    (hc : ∀ x ∈ s, ∃ᶠ a in v.filterAt x, ρ a ≤ c * μ a)
    (hd : ∀ x ∈ s, ∃ᶠ a in v.filterAt x, (d : ℝ≥0∞) * μ a ≤ ρ a) : μ s = 0 := by
  apply measure_null_of_locally_null s fun x _ => ?_
  obtain ⟨o, xo, o_open, μo⟩ : ∃ o : Set α, x ∈ o ∧ IsOpen o ∧ μ o < ∞ :=
    Measure.exists_isOpen_measure_lt_top μ x
  refine ⟨s ∩ o, inter_mem_nhdsWithin _ (o_open.mem_nhds xo), ?_⟩
  let s' := s ∩ o
  by_contra h
  apply lt_irrefl (ρ s')
  calc
    ρ s' ≤ c * μ s' := v.measure_le_of_frequently_le (c • μ) hρ s' fun x hx => hc x hx.1
    _ < d * μ s' := by gcongr; exact measure_ne_top_of_subset inter_subset_right μo.ne
    _ ≤ ρ s' := v.measure_le_of_frequently_le ρ smul_absolutelyContinuous s' fun x hx ↦ hd x hx.1

/-- If `ρ` is absolutely continuous with respect to `μ`, then for almost every `x`,
the ratio `ρ a / μ a` converges as `a` shrinks to `x` along a Vitali family for `μ`. -/
/-
**VitaliFamily.ae_tendsto_div** 是 Mathlib 中的一个定理，位于命名空间 `VitaliFamily`。
形式化陈述：ae_tendsto_div : forallᵐ x ∂μ, exists c, Tendsto (fun a => ρ a / μ a) (v.f
ilterAt x) (𝓝 c)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `ENNReal.exists_countable_dense_no_zero_top`：exists_countable_dense_no_ze
ro_top : exists s : Set Real>=0∞, s.Countable ∧ Dense s ∧ 0 ∉ s ∧ ∞ ∉ s
· 使用定理 `CanLift.prf`：∀ {α : Sort u_1} {β : Sort u_2} {coe : outParam (β → α)} {c
ond : outParam (α → Prop)} [self : CanLift α β coe cond]   (x : α), cond x → ∃ y
,…
· 使用定理 `VitaliFamily.null_of_frequently_le_of_frequently_ge`：null_of_frequently_
le_of_frequently_ge {c d : Real>=0} (hcd : c < d) (s : Set α) (hc : forall x in 
s, existsᶠ a in v.filterAt x, ρ a <= c * …
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `ENNReal.coe_lt_coe`：∀ {r q : NNReal}, ↑r < ↑q ↔ r < q
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `exists_prop_congr`：∀ {p p' : Prop} {q q' : p → Prop}, (∀ (h : p), q h ↔ 
q' h) → ∀ (hp : p ↔ p'), Exists q ↔ ∃ (h : p'), q' ⋯
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `Filter.Frequently.mono`：∀ {α : Type u} {p q : α → Prop} {f : Filter α}, 
(∃ᶠ (x : α) in f, p x) → (∀ (x : α), p x → q x) → ∃ᶠ (x : α) in f, q x
· 使用定理 `ENNReal.div_le_iff_le_mul`：∀ {a b c : ENNReal}, b ≠ 0 ∨ c ≠ ⊤ → b ≠ ⊤ ∨ 
c ≠ 0 → (a / b ≤ c ↔ a ≤ c * b)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `or_true`：∀ (p : Prop), (p ∨ True) = True
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `LE.le.trans_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b 
→ b < c → a < c
· 使用定理 `bot_le`：∀ {α : Type u} [inst : LE α] [inst_1 : OrderBot α] {a : α}, ⊥ ≤ 
a
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `ENNReal.mul_le_of_le_div`：mul_le_of_le_div (h : a <= b / c) : a * c <= b
· 使用定理 `MeasureTheory.ae_ball_iff`：ae_ball_iff {ι : Type*} {S : Set ι} (hS : S.C
ountable) {p : α -> forall i in S, Prop} : (forallᵐ x ∂μ, forall i (hi : i in S)
, p x i hi) ↔ f…
· 使用定理 `Prop.countable`：∀ (p : Prop), Countable p
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `tendsto_of_no_upcrossings`：tendsto_of_no_upcrossings [DenselyOrdered α] 
{f : Filter β} {u : β -> α} {s : Set α} (hs : Dense s) (H : forall a in s, foral
l b in s, a < b…
· 使用定理 `ENNReal.instOrderTopology`：OrderTopology ENNReal
· 使用定理 `ENNReal.instDenselyOrdered`：DenselyOrdered ENNReal
（共 32 条，此处仅展示前 30 条）

--- 原说明 ---
If `ρ` is absolutely continuous with respect to `μ`, then for almost every `x`,
the ratio `ρ a / μ a` converges as `a` shrinks to `x` along a Vitali family for 
`μ`.
-/
theorem ae_tendsto_div : ∀ᵐ x ∂μ, ∃ c, Tendsto (fun a => ρ a / μ a) (v.filterAt x) (𝓝 c) := by
  obtain ⟨w, w_count, w_dense, _, w_top⟩ :
    ∃ w : Set ℝ≥0∞, w.Countable ∧ Dense w ∧ 0 ∉ w ∧ ∞ ∉ w :=
    ENNReal.exists_countable_dense_no_zero_top
  have I : ∀ x ∈ w, x ≠ ∞ := fun x xs hx => w_top (hx ▸ xs)
  have A : ∀ c ∈ w, ∀ d ∈ w, c < d → ∀ᵐ x ∂μ,
      ¬((∃ᶠ a in v.filterAt x, ρ a / μ a < c) ∧ ∃ᶠ a in v.filterAt x, d < ρ a / μ a) := by
    intro c hc d hd hcd
    lift c to ℝ≥0 using I c hc
    lift d to ℝ≥0 using I d hd
    apply v.null_of_frequently_le_of_frequently_ge hρ (ENNReal.coe_lt_coe.1 hcd)
    · simp only [and_imp, exists_prop, not_frequently, not_and, not_lt, not_le, not_eventually,
        mem_ofPred_eq, mem_compl_iff, not_forall]
      intro x h1x _
      apply h1x.mono fun a ha => ?_
      refine (ENNReal.div_le_iff_le_mul ?_ (Or.inr (bot_le.trans_lt ha).ne')).1 ha.le
      simp only [ENNReal.coe_ne_top, Ne, or_true, not_false_iff]
    · simp only [and_imp, exists_prop, not_frequently, not_and, not_lt, not_le, not_eventually,
        mem_ofPred_eq, mem_compl_iff, not_forall]
      intro x _ h2x
      apply h2x.mono fun a ha => ?_
      exact ENNReal.mul_le_of_le_div ha.le
  have B : ∀ᵐ x ∂μ, ∀ c ∈ w, ∀ d ∈ w, c < d →
      ¬((∃ᶠ a in v.filterAt x, ρ a / μ a < c) ∧ ∃ᶠ a in v.filterAt x, d < ρ a / μ a) := by
    simpa only [ae_ball_iff w_count, ae_all_iff]
  filter_upwards [B]
  intro x hx
  exact tendsto_of_no_upcrossings w_dense hx
/-
**VitaliFamily.ae_tendsto_limRatio** 是 Mathlib 中的一个定理，位于命名空间 `VitaliFamily`。
形式化陈述：ae_tendsto_limRatio : forallᵐ x ∂μ, Tendsto (fun a => ρ a / μ a) (v.filter
At x) (𝓝 (v.limRatio ρ x))
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `VitaliFamily.ae_tendsto_div`：ae_tendsto_div : forallᵐ x ∂μ, exists c, Te
ndsto (fun a => ρ a / μ a) (v.filterAt x) (𝓝 c)
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `tendsto_nhds_limUnder`：tendsto_nhds_limUnder {f : Filter α} {g : α -> X}
 (h : exists x, Tendsto g f (𝓝 x)) : Tendsto g f (𝓝 (@limUnder _ _ _ h.nonempty 
f g))
-/
theorem ae_tendsto_limRatio :
    ∀ᵐ x ∂μ, Tendsto (fun a => ρ a / μ a) (v.filterAt x) (𝓝 (v.limRatio ρ x)) := by
  filter_upwards [v.ae_tendsto_div hρ]
  intro x hx
  exact tendsto_nhds_limUnder hx

/-- Given two thresholds `p < q`, the sets `{x | v.limRatio ρ x < p}`
and `{x | q < v.limRatio ρ x}` are obviously disjoint. The key to proving that `v.limRatio ρ` is
almost everywhere measurable is to show that these sets have measurable supersets which are also
disjoint, up to zero measure. This is the content of this lemma. -/
/-
**VitaliFamily.exists_measurable_supersets_limRatio** 是 Mathlib 中的一个定理，位于命名空间 `V
italiFamily`。
形式化陈述：exists_measurable_supersets_limRatio {p q : Real>=0} (hpq : p < q) : exist
s a b, MeasurableSet a ∧ MeasurableSet b ∧ {x | v.limRatio ρ x < p} subseteq a ∧
 {x | (q : Real>=0∞) < v.limRatio ρ x} subseteq b ∧ μ (a inter b) = 0
参数：hpq : p < q。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Add.sigmaFinite`：∀ {α : Type u_1} {m0 : MeasurableSpace α}
 (μ ν : MeasureTheory.Measure α) [MeasureTheory.SigmaFinite μ]   [MeasureTheory.
SigmaFinite ν], Mea…
· 使用定理 `MeasureTheory.sigmaFinite_of_locallyFinite`：∀ {α : Type u_1} {m0 : Measu
rableSpace α} {μ : MeasureTheory.Measure α} [inst : TopologicalSpace α]   [Secon
dCountableTopology α] [MeasureTh…
· 使用定理 `MeasurableSet.union`：∀ {α : Type u_1} {m : MeasurableSpace α} {s₁ s₂ : S
et α}, MeasurableSet s₁ → MeasurableSet s₂ → MeasurableSet (s₁ ∪ s₂)
· 使用定理 `MeasureTheory.measurableSet_toMeasurable`：measurableSet_toMeasurable (μ 
: Measure α) (s : Set α) : MeasurableSet (toMeasurable μ s)
· 使用定理 `MeasurableSet.iUnion`：∀ {α : Type u_1} {ι : Sort u_6} {m : MeasurableSpa
ce α} [Countable ι] ⦃f : ι → Set α⦄,   (∀ (b : ι), MeasurableSet (f b)) → Measur
ableSet (⋃…
· 使用定理 `instCountableNat`：Countable ℕ
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.mem_iUnion`：mem_iUnion {x : α} {s : ι -> Set α} : (x in ⋃ i, s i) ↔ 
exists i, x in s i
· 使用定理 `MeasureTheory.subset_toMeasurable`：subset_toMeasurable (μ : Measure α) (
s : Set α) : s subseteq toMeasurable μ s
· 使用定理 `MeasureTheory.mem_spanningSetsIndex`：mem_spanningSetsIndex (μ : Measure 
α) [SigmaFinite μ] (x : α) : x in spanningSets μ (spanningSetsIndex μ x)
· 使用定理 `LT.lt.ne`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≠ b
· 使用引理 `lt_of_le_of_lt`：lt_of_le_of_lt (hab : a <= b) (hbc : b < c) : a < c
· 使用定理 `MeasureTheory.measure_mono`：measure_mono (h : s subseteq t) : μ s <= μ t
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `Set.inter_subset_right`：inter_subset_right {s t : Set α} : s inter t sub
seteq t
· 使用定理 `MeasureTheory.measure_spanningSets_lt_top`：measure_spanningSets_lt_top (
μ : Measure α) [SigmaFinite μ] (i : Nat) : μ (spanningSets μ i) < ∞
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `MeasureTheory.Measure.measure_toMeasurable_add_inter_left`：measure_toMea
surable_add_inter_left {s t : Set α} (hs : MeasurableSet s) (ht : (μ + ν) t != ∞
) : μ (toMeasurable (μ + ν) t inter s) = μ (t i…
· 使用定理 `VitaliFamily.measure_le_of_frequently_le`：measure_le_of_frequently_le [S
econdCountableTopology α] [BorelSpace α] {ρ : Measure α} (ν : Measure α) [IsLoca
llyFiniteMeasure ν] (hρ : ρ ≪ …
· 使用定理 `tendsto_nhds_limUnder`：tendsto_nhds_limUnder {f : Filter α} {g : α -> X}
 (h : exists x, Tendsto g f (𝓝 x)) : Tendsto g f (𝓝 (@limUnder _ _ _ h.nonempty 
f g))
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `tendsto_order`：tendsto_order [OrderTopology α] {f : β -> α} {a : α} {x :
 Filter β} : Tendsto f x (𝓝 a) ↔ (forall a' < a, forallᶠ b in x, a' < f b) ∧ for
all…
· 使用定理 `ENNReal.instOrderTopology`：OrderTopology ENNReal
· 使用定理 `Filter.Frequently.mono`：∀ {α : Type u} {p q : α → Prop} {f : Filter α}, 
(∃ᶠ (x : α) in f, p x) → (∀ (x : α), p x → q x) → ∃ᶠ (x : α) in f, q x
· 使用定理 `Filter.Eventually.frequently`：∀ {α : Type u} {f : Filter α} [f.NeBot] {p
 : α → Prop}, (∀ᶠ (x : α) in f, p x) → ∃ᶠ (x : α) in f, p x
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.Measure.coe_nnreal_smul_apply`：coe_nnreal_smul_apply {_m :
 MeasurableSpace α} (c : Real>=0) (μ : Measure α) (s : Set α) : (c • μ) s = c * 
μ s
· 使用定理 `ENNReal.div_le_iff_le_mul`：∀ {a b c : ENNReal}, b ≠ 0 ∨ c ≠ ⊤ → b ≠ ⊤ ∨ 
c ≠ 0 → (a / b ≤ c ↔ a ≤ c * b)
（共 74 条，此处仅展示前 30 条）

--- 原说明 ---
Given two thresholds `p < q`, the sets `{x | v.limRatio ρ x < p}`
and `{x | q < v.limRatio ρ x}` are obviously disjoint. The key to proving that `
v.limRatio ρ` is
almost everywhere measurable is to show that these sets have measurable superset
s which are also
disjoint, up to zero measure. This is the content of this lemma.
-/
theorem exists_measurable_supersets_limRatio {p q : ℝ≥0} (hpq : p < q) :
    ∃ a b, MeasurableSet a ∧ MeasurableSet b ∧
      {x | v.limRatio ρ x < p} ⊆ a ∧ {x | (q : ℝ≥0∞) < v.limRatio ρ x} ⊆ b ∧ μ (a ∩ b) = 0 := by
  /- Here is a rough sketch, assuming that the measure is finite and the limit is well defined
    everywhere. Let `u := {x | v.limRatio ρ x < p}` and `w := {x | q < v.limRatio ρ x}`. They
    have measurable supersets `u'` and `w'` of the same measure. We will show that these satisfy
    the conclusion of the theorem, i.e., `μ (u' ∩ w') = 0`. For this, note that
    `ρ (u' ∩ w') = ρ (u ∩ w')` (as `w'` is measurable, see `measure_toMeasurable_add_inter_left`).
    The latter set is included in the set where the limit of the ratios is `< p`, and therefore
    its measure is `≤ p * μ (u ∩ w')`. Using the same trick in the other direction gives that this
    is `p * μ (u' ∩ w')`. We have shown that `ρ (u' ∩ w') ≤ p * μ (u' ∩ w')`. Arguing in the same
    way but using the `w` part gives `q * μ (u' ∩ w') ≤ ρ (u' ∩ w')`. If `μ (u' ∩ w')` were nonzero,
    this would be a contradiction as `p < q`.

    For the rigorous proof, we need to work on a part of the space where the measure is finite
    (provided by `spanningSets (ρ + μ)`) and to restrict to the set where the limit is well defined
    (called `s` below, of full measure). Otherwise, the argument goes through.
    -/
  let s := {x | ∃ c, Tendsto (fun a => ρ a / μ a) (v.filterAt x) (𝓝 c)}
  let o : ℕ → Set α := spanningSets (ρ + μ)
  let u n := s ∩ {x | v.limRatio ρ x < p} ∩ o n
  let w n := s ∩ {x | (q : ℝ≥0∞) < v.limRatio ρ x} ∩ o n
  -- the supersets are obtained by restricting to the set `s` where the limit is well defined, to
  -- a finite measure part `o n`, taking a measurable superset here, and then taking the union over
  -- `n`.
  refine
    ⟨toMeasurable μ sᶜ ∪ ⋃ n, toMeasurable (ρ + μ) (u n),
      toMeasurable μ sᶜ ∪ ⋃ n, toMeasurable (ρ + μ) (w n), ?_, ?_, ?_, ?_, ?_⟩
  -- check that these sets are measurable supersets as required
  · exact
      (measurableSet_toMeasurable _ _).union
        (MeasurableSet.iUnion fun n => measurableSet_toMeasurable _ _)
  · exact
      (measurableSet_toMeasurable _ _).union
        (MeasurableSet.iUnion fun n => measurableSet_toMeasurable _ _)
  · intro x hx
    by_cases h : x ∈ s
    · refine Or.inr (mem_iUnion.2 ⟨spanningSetsIndex (ρ + μ) x, ?_⟩)
      exact subset_toMeasurable _ _ ⟨⟨h, hx⟩, mem_spanningSetsIndex _ _⟩
    · exact Or.inl (subset_toMeasurable μ sᶜ h)
  · intro x hx
    by_cases h : x ∈ s
    · refine Or.inr (mem_iUnion.2 ⟨spanningSetsIndex (ρ + μ) x, ?_⟩)
      exact subset_toMeasurable _ _ ⟨⟨h, hx⟩, mem_spanningSetsIndex _ _⟩
    · exact Or.inl (subset_toMeasurable μ sᶜ h)
  -- it remains to check the nontrivial part that these sets have zero measure intersection.
  -- it suffices to do it for fixed `m` and `n`, as one is taking countable unions.
  suffices H : ∀ m n : ℕ, μ (toMeasurable (ρ + μ) (u m) ∩ toMeasurable (ρ + μ) (w n)) = 0 by
    have A :
      (toMeasurable μ sᶜ ∪ ⋃ n, toMeasurable (ρ + μ) (u n)) ∩
          (toMeasurable μ sᶜ ∪ ⋃ n, toMeasurable (ρ + μ) (w n)) ⊆
        toMeasurable μ sᶜ ∪
          ⋃ (m) (n), toMeasurable (ρ + μ) (u m) ∩ toMeasurable (ρ + μ) (w n) := by
      simp only [inter_union_distrib_left, union_inter_distrib_right, true_and,
        subset_union_left, union_subset_iff, inter_self]
      refine ⟨?_, ?_, ?_⟩
      · exact inter_subset_right.trans subset_union_left
      · exact inter_subset_left.trans subset_union_left
      · simp_rw [iUnion_inter, inter_iUnion]; exact subset_union_right
    refine le_antisymm ((measure_mono A).trans ?_) bot_le
    calc
      μ (toMeasurable μ sᶜ ∪
        ⋃ (m) (n), toMeasurable (ρ + μ) (u m) ∩ toMeasurable (ρ + μ) (w n)) ≤
          μ (toMeasurable μ sᶜ) +
            μ (⋃ (m) (n), toMeasurable (ρ + μ) (u m) ∩ toMeasurable (ρ + μ) (w n)) :=
        measure_union_le _ _
      _ = μ (⋃ (m) (n), toMeasurable (ρ + μ) (u m) ∩ toMeasurable (ρ + μ) (w n)) := by
        have : μ sᶜ = 0 := v.ae_tendsto_div hρ; rw [measure_toMeasurable, this, zero_add]
      _ ≤ ∑' (m) (n), μ (toMeasurable (ρ + μ) (u m) ∩ toMeasurable (ρ + μ) (w n)) :=
        ((measure_iUnion_le _).trans (ENNReal.tsum_le_tsum fun m => measure_iUnion_le _))
      _ = 0 := by simp only [H, tsum_zero]
  -- now starts the nontrivial part of the argument. We fix `m` and `n`, and show that the
  -- measurable supersets of `u m` and `w n` have zero measure intersection by using the lemmas
  -- `measure_toMeasurable_add_inter_left` (to reduce to `u m` or `w n` instead of the measurable
  -- superset) and `measure_le_of_frequently_le` to compare their measures for `ρ` and `μ`.
  intro m n
  have I : (ρ + μ) (u m) ≠ ∞ := by
    apply (lt_of_le_of_lt (measure_mono _) (measure_spanningSets_lt_top (ρ + μ) m)).ne
    exact inter_subset_right
  have J : (ρ + μ) (w n) ≠ ∞ := by
    apply (lt_of_le_of_lt (measure_mono _) (measure_spanningSets_lt_top (ρ + μ) n)).ne
    exact inter_subset_right
  have A :
    ρ (toMeasurable (ρ + μ) (u m) ∩ toMeasurable (ρ + μ) (w n)) ≤
      p * μ (toMeasurable (ρ + μ) (u m) ∩ toMeasurable (ρ + μ) (w n)) :=
    calc
      ρ (toMeasurable (ρ + μ) (u m) ∩ toMeasurable (ρ + μ) (w n)) =
          ρ (u m ∩ toMeasurable (ρ + μ) (w n)) :=
        measure_toMeasurable_add_inter_left (measurableSet_toMeasurable _ _) I
      _ ≤ (p • μ) (u m ∩ toMeasurable (ρ + μ) (w n)) := by
        refine v.measure_le_of_frequently_le (p • μ) hρ _ fun x hx => ?_
        have L : Tendsto (fun a : Set α => ρ a / μ a) (v.filterAt x) (𝓝 (v.limRatio ρ x)) :=
          tendsto_nhds_limUnder hx.1.1.1
        have I : ∀ᶠ b : Set α in v.filterAt x, ρ b / μ b < p := (tendsto_order.1 L).2 _ hx.1.1.2
        apply I.frequently.mono fun a ha => ?_
        rw [coe_nnreal_smul_apply]
        refine (ENNReal.div_le_iff_le_mul ?_ (Or.inr (bot_le.trans_lt ha).ne')).1 ha.le
        simp only [ENNReal.coe_ne_top, Ne, or_true, not_false_iff]
      _ = p * μ (toMeasurable (ρ + μ) (u m) ∩ toMeasurable (ρ + μ) (w n)) := by
        simp only [coe_nnreal_smul_apply,
          measure_toMeasurable_add_inter_right (measurableSet_toMeasurable _ _) I]
  have B :
    (q : ℝ≥0∞) * μ (toMeasurable (ρ + μ) (u m) ∩ toMeasurable (ρ + μ) (w n)) ≤
      ρ (toMeasurable (ρ + μ) (u m) ∩ toMeasurable (ρ + μ) (w n)) :=
    calc
      (q : ℝ≥0∞) * μ (toMeasurable (ρ + μ) (u m) ∩ toMeasurable (ρ + μ) (w n)) =
          (q : ℝ≥0∞) * μ (toMeasurable (ρ + μ) (u m) ∩ w n) := by
        conv_rhs => rw [inter_comm]
        rw [inter_comm, measure_toMeasurable_add_inter_right (measurableSet_toMeasurable _ _) J]
      _ ≤ ρ (toMeasurable (ρ + μ) (u m) ∩ w n) := by
        rw [← coe_nnreal_smul_apply]
        refine v.measure_le_of_frequently_le _ (.smul_left .rfl _) _ ?_
        intro x hx
        have L : Tendsto (fun a : Set α => ρ a / μ a) (v.filterAt x) (𝓝 (v.limRatio ρ x)) :=
          tendsto_nhds_limUnder hx.2.1.1
        have I : ∀ᶠ b : Set α in v.filterAt x, (q : ℝ≥0∞) < ρ b / μ b :=
          (tendsto_order.1 L).1 _ hx.2.1.2
        apply I.frequently.mono fun a ha => ?_
        rw [coe_nnreal_smul_apply]
        exact ENNReal.mul_le_of_le_div ha.le
      _ = ρ (toMeasurable (ρ + μ) (u m) ∩ toMeasurable (ρ + μ) (w n)) := by
        conv_rhs => rw [inter_comm]
        rw [inter_comm]
        exact (measure_toMeasurable_add_inter_left (measurableSet_toMeasurable _ _) J).symm
  by_contra h
  apply lt_irrefl (ρ (toMeasurable (ρ + μ) (u m) ∩ toMeasurable (ρ + μ) (w n)))
  calc
    ρ (toMeasurable (ρ + μ) (u m) ∩ toMeasurable (ρ + μ) (w n)) ≤
        p * μ (toMeasurable (ρ + μ) (u m) ∩ toMeasurable (ρ + μ) (w n)) :=
      A
    _ < q * μ (toMeasurable (ρ + μ) (u m) ∩ toMeasurable (ρ + μ) (w n)) := by
      gcongr
      suffices H : (ρ + μ) (toMeasurable (ρ + μ) (u m) ∩ toMeasurable (ρ + μ) (w n)) ≠ ∞ by
        simp only [not_or, ENNReal.add_eq_top, Pi.add_apply, Ne, coe_add] at H
        exact H.2
      apply (lt_of_le_of_lt (measure_mono inter_subset_left) _).ne
      rw [measure_toMeasurable]
      apply lt_of_le_of_lt (measure_mono _) (measure_spanningSets_lt_top (ρ + μ) m)
      exact inter_subset_right
    _ ≤ ρ (toMeasurable (ρ + μ) (u m) ∩ toMeasurable (ρ + μ) (w n)) := B
/-
**VitaliFamily.aemeasurable_limRatio** 是 Mathlib 中的一个定理，位于命名空间 `VitaliFamily`。
形式化陈述：aemeasurable_limRatio : AEMeasurable (v.limRatio ρ) μ
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ENNReal.aemeasurable_of_exist_almost_disjoint_supersets`：ENNReal.aemeasu
rable_of_exist_almost_disjoint_supersets {α : Type*} {m : MeasurableSpace α} (μ 
: Measure α) (f : α -> Real>=0∞) (h : forall …
· 使用定理 `VitaliFamily.exists_measurable_supersets_limRatio`：exists_measurable_sup
ersets_limRatio {p q : Real>=0} (hpq : p < q) : exists a b, MeasurableSet a ∧ Me
asurableSet b ∧ {x | v.limRatio ρ x < p…
-/
theorem aemeasurable_limRatio : AEMeasurable (v.limRatio ρ) μ := by
  apply ENNReal.aemeasurable_of_exist_almost_disjoint_supersets _ _ fun p q hpq => ?_
  exact v.exists_measurable_supersets_limRatio hρ hpq

/-- A measurable version of `v.limRatio ρ`. Do *not* use this definition: it is only a temporary
device to show that `v.limRatio` is almost everywhere equal to the Radon-Nikodym derivative. -/
/-
**VitaliFamily.limRatioMeas** 是 Mathlib 中的一个定义，位于命名空间 `VitaliFamily`。
形式化陈述：limRatioMeas : α -> Real>=0∞
该定义给出了一等式。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `VitaliFamily.aemeasurable_limRatio`：aemeasurable_limRatio : AEMeasurable
 (v.limRatio ρ) μ

--- 原说明 ---
A measurable version of `v.limRatio ρ`. Do *not* use this definition: it is only
 a temporary
device to show that `v.limRatio` is almost everywhere equal to the Radon-Nikodym
 derivative.
-/
noncomputable def limRatioMeas : α → ℝ≥0∞ :=
  (v.aemeasurable_limRatio hρ).mk _
/-
**VitaliFamily.limRatioMeas_measurable** 是 Mathlib 中的一个定理，位于命名空间 `VitaliFamily`。
形式化陈述：limRatioMeas_measurable : Measurable (v.limRatioMeas hρ)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AEMeasurable.measurable_mk`：measurable_mk (h : AEMeasurable f μ) : Measu
rable (h.mk f)
· 使用定理 `VitaliFamily.aemeasurable_limRatio`：aemeasurable_limRatio : AEMeasurable
 (v.limRatio ρ) μ
-/
theorem limRatioMeas_measurable : Measurable (v.limRatioMeas hρ) :=
  AEMeasurable.measurable_mk _
/-
**VitaliFamily.ae_tendsto_limRatioMeas** 是 Mathlib 中的一个定理，位于命名空间 `VitaliFamily`。
形式化陈述：ae_tendsto_limRatioMeas : forallᵐ x ∂μ, Tendsto (fun a => ρ a / μ a) (v.fi
lterAt x) (𝓝 (v.limRatioMeas hρ x))
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `VitaliFamily.aemeasurable_limRatio`：aemeasurable_limRatio : AEMeasurable
 (v.limRatio ρ) μ
· 使用定理 `AEMeasurable.ae_eq_mk`：ae_eq_mk (h : AEMeasurable f μ) : f =ᵐ[μ] h.mk f
· 使用定理 `VitaliFamily.ae_tendsto_limRatio`：ae_tendsto_limRatio : forallᵐ x ∂μ, Te
ndsto (fun a => ρ a / μ a) (v.filterAt x) (𝓝 (v.limRatio ρ x))
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
-/
theorem ae_tendsto_limRatioMeas :
    ∀ᵐ x ∂μ, Tendsto (fun a => ρ a / μ a) (v.filterAt x) (𝓝 (v.limRatioMeas hρ x)) := by
  filter_upwards [v.ae_tendsto_limRatio hρ, AEMeasurable.ae_eq_mk (v.aemeasurable_limRatio hρ)]
  intro x hx h'x
  rwa [h'x] at hx

/-- If, for all `x` in a set `s`, one has frequently `ρ a / μ a < p`, then `ρ s ≤ p * μ s`, as
proved in `measure_le_of_frequently_le`. Since `ρ a / μ a` tends almost everywhere to
`v.limRatioMeas hρ x`, the same property holds for sets `s` on which `v.limRatioMeas hρ < p`. -/
/-
**VitaliFamily.measure_le_mul_of_subset_limRatioMeas_lt** 是 Mathlib 中的一个定理，位于命名空
间 `VitaliFamily`。
形式化陈述：measure_le_mul_of_subset_limRatioMeas_lt {p : Real>=0} {s : Set α} (h : s 
subseteq {x | v.limRatioMeas hρ x < p}) : ρ s <= p * μ s
参数：h : s subseteq {x | v.limRatioMeas hρ x < p}。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `VitaliFamily.ae_tendsto_limRatioMeas`：ae_tendsto_limRatioMeas : forallᵐ 
x ∂μ, Tendsto (fun a => ρ a / μ a) (v.filterAt x) (𝓝 (v.limRatioMeas hρ x))
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `VitaliFamily.measure_le_of_frequently_le`：measure_le_of_frequently_le [S
econdCountableTopology α] [BorelSpace α] {ρ : Measure α} (ν : Measure α) [IsLoca
llyFiniteMeasure ν] (hρ : ρ ≪ …
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `tendsto_order`：tendsto_order [OrderTopology α] {f : β -> α} {a : α} {x :
 Filter β} : Tendsto f x (𝓝 a) ↔ (forall a' < a, forallᶠ b in x, a' < f b) ∧ for
all…
· 使用定理 `ENNReal.instOrderTopology`：OrderTopology ENNReal
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Filter.Frequently.mono`：∀ {α : Type u} {p q : α → Prop} {f : Filter α}, 
(∃ᶠ (x : α) in f, p x) → (∀ (x : α), p x → q x) → ∃ᶠ (x : α) in f, q x
· 使用定理 `Filter.Eventually.frequently`：∀ {α : Type u} {f : Filter α} [f.NeBot] {p
 : α → Prop}, (∀ᶠ (x : α) in f, p x) → ∃ᶠ (x : α) in f, p x
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.Measure.coe_nnreal_smul_apply`：coe_nnreal_smul_apply {_m :
 MeasurableSpace α} (c : Real>=0) (μ : Measure α) (s : Set α) : (c • μ) s = c * 
μ s
· 使用定理 `ENNReal.div_le_iff_le_mul`：∀ {a b c : ENNReal}, b ≠ 0 ∨ c ≠ ⊤ → b ≠ ⊤ ∨ 
c ≠ 0 → (a / b ≤ c ↔ a ≤ c * b)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `or_true`：∀ (p : Prop), (p ∨ True) = True
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `LE.le.trans_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b 
→ b < c → a < c
· 使用定理 `bot_le`：∀ {α : Type u} [inst : LE α] [inst_1 : OrderBot α] {a : α}, ⊥ ≤ 
a
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `Set.inter_union_compl`：inter_union_compl (s t : Set α) : s inter t union
 s inter tᶜ = s
· 使用定理 `MeasureTheory.measure_union_le`：measure_union_le (s t : Set α) : μ (s un
ion t) <= μ s + μ t
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `add_le_add`：∀ {α : Type u_1} [inst : Add α] [inst_1 : Preorder α] [AddLe
ftMono α] [AddRightMono α] {a b c d : α},   a ≤ b → c ≤ d → a + c ≤ b + d
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `ENNReal.instIsOrderedAddMonoid`：IsOrderedAddMonoid ENNReal
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `MeasureTheory.measure_mono`：measure_mono (h : s subseteq t) : μ s <= μ t
· 使用定理 `Set.inter_subset_right`：inter_subset_right {s t : Set α} : s inter t sub
seteq t
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
（共 36 条，此处仅展示前 30 条）

--- 原说明 ---
If, for all `x` in a set `s`, one has frequently `ρ a / μ a < p`, then `ρ s ≤ p 
* μ s`, as
proved in `measure_le_of_frequently_le`. Since `ρ a / μ a` tends almost everywhe
re to
`v.limRatioMeas hρ x`, the same property holds for sets `s` on which `v.limRatio
Meas hρ < p`.
-/
theorem measure_le_mul_of_subset_limRatioMeas_lt {p : ℝ≥0} {s : Set α}
    (h : s ⊆ {x | v.limRatioMeas hρ x < p}) : ρ s ≤ p * μ s := by
  let t := {x : α | Tendsto (fun a => ρ a / μ a) (v.filterAt x) (𝓝 (v.limRatioMeas hρ x))}
  have A : μ tᶜ = 0 := v.ae_tendsto_limRatioMeas hρ
  suffices H : ρ (s ∩ t) ≤ (p • μ) (s ∩ t) by calc
    ρ s = ρ (s ∩ t ∪ s ∩ tᶜ) := by rw [inter_union_compl]
    _ ≤ ρ (s ∩ t) + ρ (s ∩ tᶜ) := measure_union_le _ _
    _ ≤ (p • μ) (s ∩ t) + ρ tᶜ := by gcongr; apply inter_subset_right
    _ ≤ p * μ (s ∩ t) := by simp [(hρ A)]
    _ ≤ p * μ s := by gcongr; apply inter_subset_left
  refine v.measure_le_of_frequently_le (p • μ) hρ _ fun x hx => ?_
  have I : ∀ᶠ b : Set α in v.filterAt x, ρ b / μ b < p := (tendsto_order.1 hx.2).2 _ (h hx.1)
  apply I.frequently.mono fun a ha => ?_
  rw [coe_nnreal_smul_apply]
  refine (ENNReal.div_le_iff_le_mul ?_ (Or.inr (bot_le.trans_lt ha).ne')).1 ha.le
  simp only [ENNReal.coe_ne_top, Ne, or_true, not_false_iff]

/-- If, for all `x` in a set `s`, one has frequently `q < ρ a / μ a`, then `q * μ s ≤ ρ s`, as
proved in `measure_le_of_frequently_le`. Since `ρ a / μ a` tends almost everywhere to
`v.limRatioMeas hρ x`, the same property holds for sets `s` on which `q < v.limRatioMeas hρ`. -/
/-
**VitaliFamily.mul_measure_le_of_subset_lt_limRatioMeas** 是 Mathlib 中的一个定理，位于命名空
间 `VitaliFamily`。
形式化陈述：mul_measure_le_of_subset_lt_limRatioMeas {q : Real>=0} {s : Set α} (h : s 
subseteq {x | (q : Real>=0∞) < v.limRatioMeas hρ x}) : (q : Real>=0∞) * μ s <= ρ
 s
参数：h : s subseteq {x | (q : Real>=0∞) < v.limRatioMeas hρ x}。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `VitaliFamily.ae_tendsto_limRatioMeas`：ae_tendsto_limRatioMeas : forallᵐ 
x ∂μ, Tendsto (fun a => ρ a / μ a) (v.filterAt x) (𝓝 (v.limRatioMeas hρ x))
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `VitaliFamily.measure_le_of_frequently_le`：measure_le_of_frequently_le [S
econdCountableTopology α] [BorelSpace α] {ρ : Measure α} (ν : Measure α) [IsLoca
llyFiniteMeasure ν] (hρ : ρ ≪ …
· 使用定理 `MeasureTheory.Measure.AbsolutelyContinuous.smul_left`：∀ {α : Type u_1} {
R : Type u_5} {mα : MeasurableSpace α} {μ ν : MeasureTheory.Measure α} [inst : S
Mul R ENNReal]   [inst_1 : IsScalarTower R…
· 使用定理 `MeasureTheory.Measure.AbsolutelyContinuous.rfl`：∀ {α : Type u_1} {mα : M
easurableSpace α} {μ : MeasureTheory.Measure α}, μ.AbsolutelyContinuous μ
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `tendsto_order`：tendsto_order [OrderTopology α] {f : β -> α} {a : α} {x :
 Filter β} : Tendsto f x (𝓝 a) ↔ (forall a' < a, forallᶠ b in x, a' < f b) ∧ for
all…
· 使用定理 `ENNReal.instOrderTopology`：OrderTopology ENNReal
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Filter.Frequently.mono`：∀ {α : Type u} {p q : α → Prop} {f : Filter α}, 
(∃ᶠ (x : α) in f, p x) → (∀ (x : α), p x → q x) → ∃ᶠ (x : α) in f, q x
· 使用定理 `Filter.Eventually.frequently`：∀ {α : Type u} {f : Filter α} [f.NeBot] {p
 : α → Prop}, (∀ᶠ (x : α) in f, p x) → ∃ᶠ (x : α) in f, p x
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.Measure.coe_nnreal_smul_apply`：coe_nnreal_smul_apply {_m :
 MeasurableSpace α} (c : Real>=0) (μ : Measure α) (s : Set α) : (c • μ) s = c * 
μ s
· 使用定理 `ENNReal.mul_le_of_le_div`：mul_le_of_le_div (h : a <= b / c) : a * c <= b
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `Set.inter_union_compl`：inter_union_compl (s t : Set α) : s inter t union
 s inter tᶜ = s
· 使用定理 `MeasureTheory.measure_union_le`：measure_union_le (s t : Set α) : μ (s un
ion t) <= μ s + μ t
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `add_le_add`：∀ {α : Type u_1} [inst : Add α] [inst_1 : Preorder α] [AddLe
ftMono α] [AddRightMono α] {a b c d : α},   a ≤ b → c ≤ d → a + c ≤ b + d
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `ENNReal.instIsOrderedAddMonoid`：IsOrderedAddMonoid ENNReal
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `MeasureTheory.measure_mono`：measure_mono (h : s subseteq t) : μ s <= μ t
· 使用定理 `Set.inter_subset_right`：inter_subset_right {s t : Set α} : s inter t sub
seteq t
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `smul_zero`：smul_zero (a : M) : a • (0 : A) = 0
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
（共 32 条，此处仅展示前 30 条）

--- 原说明 ---
If, for all `x` in a set `s`, one has frequently `q < ρ a / μ a`, then `q * μ s 
≤ ρ s`, as
proved in `measure_le_of_frequently_le`. Since `ρ a / μ a` tends almost everywhe
re to
`v.limRatioMeas hρ x`, the same property holds for sets `s` on which `q < v.limR
atioMeas hρ`.
-/
theorem mul_measure_le_of_subset_lt_limRatioMeas {q : ℝ≥0} {s : Set α}
    (h : s ⊆ {x | (q : ℝ≥0∞) < v.limRatioMeas hρ x}) : (q : ℝ≥0∞) * μ s ≤ ρ s := by
  let t := {x : α | Tendsto (fun a => ρ a / μ a) (v.filterAt x) (𝓝 (v.limRatioMeas hρ x))}
  have A : μ tᶜ = 0 := v.ae_tendsto_limRatioMeas hρ
  suffices H : (q • μ) (s ∩ t) ≤ ρ (s ∩ t) by calc
    (q • μ) s = (q • μ) (s ∩ t ∪ s ∩ tᶜ) := by rw [inter_union_compl]
    _ ≤ (q • μ) (s ∩ t) + (q • μ) (s ∩ tᶜ) := measure_union_le _ _
    _ ≤ ρ (s ∩ t) + (q • μ) tᶜ := by gcongr; apply inter_subset_right
    _ = ρ (s ∩ t) := by simp [A]
    _ ≤ ρ s := by gcongr; apply inter_subset_left
  refine v.measure_le_of_frequently_le _ (.smul_left .rfl _) _ ?_
  intro x hx
  have I : ∀ᶠ a in v.filterAt x, (q : ℝ≥0∞) < ρ a / μ a := (tendsto_order.1 hx.2).1 _ (h hx.1)
  apply I.frequently.mono fun a ha => ?_
  rw [coe_nnreal_smul_apply]
  exact ENNReal.mul_le_of_le_div ha.le

/-- The points with `v.limRatioMeas hρ x = ∞` have measure `0` for `μ`. -/
/-
**VitaliFamily.measure_limRatioMeas_top** 是 Mathlib 中的一个定理，位于命名空间 `VitaliFamily`
。
形式化陈述：measure_limRatioMeas_top : μ {x | v.limRatioMeas hρ x = ∞} = 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.measure_null_of_locally_null`：measure_null_of_locally_null
 [TopologicalSpace α] [SecondCountableTopology α] (s : Set α) (hs : forall x in 
s, exists u in 𝓝[s] x, μ u = 0) …
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `MeasureTheory.Measure.exists_isOpen_measure_lt_top`：∀ {α : Type u_1} {m0
 : MeasurableSpace α} [inst : TopologicalSpace α] (μ : MeasureTheory.Measure α) 
  [MeasureTheory.IsLocallyFiniteMeasure …
· 使用定理 `inter_mem_nhdsWithin`：inter_mem_nhdsWithin (s : Set α) {t : Set α} {a : 
α} (h : t in 𝓝 a) : s inter t in 𝓝[s] a
· 使用定理 `IsOpen.mem_nhds`：IsOpen.mem_nhds (hs : IsOpen s) (hx : x in s) : s in 𝓝 
x
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `MeasureTheory.measure_ne_top_of_subset`：measure_ne_top_of_subset (h : t 
subseteq s) (ht : μ s != ∞) : μ t != ∞
· 使用定理 `Set.inter_subset_right`：inter_subset_right {s t : Set α} : s inter t sub
seteq t
· 使用定理 `LT.lt.ne`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≠ b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `div_eq_mul_inv`：div_eq_mul_inv (a b : G) : a / b = a * b⁻¹
· 使用定理 `ENNReal.le_div_iff_mul_le`：∀ {a b c : ENNReal}, b ≠ 0 ∨ c ≠ 0 → b ≠ ⊤ ∨ 
c ≠ ⊤ → (a ≤ c / b ↔ a * b ≤ c)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `LT.lt.trans_le`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a < b 
→ b ≤ c → a < c
· 使用定理 `zero_lt_one`：∀ {α : Type u_1} [inst : Zero α] [inst_1 : One α] [inst_2 :
 PartialOrder α] [ZeroLEOneClass α] [NeZero 1], 0 < 1
· 使用定理 `FloorSemiring.instZeroLEOneClass`：∀ {α : Type u_2} [inst : Semiring α] [
inst_1 : PartialOrder α] [FloorSemiring α], ZeroLEOneClass α
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `true_or`：∀ (p : Prop), (True ∨ p) = True
· 使用定理 `VitaliFamily.mul_measure_le_of_subset_lt_limRatioMeas`：mul_measure_le_of
_subset_lt_limRatioMeas {q : Real>=0} {s : Set α} (h : s subseteq {x | (q : Real
>=0∞) < v.limRatioMeas hρ x}) : (q : Real>=…
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `ENNReal.Tendsto.mul_const`：∀ {α : Type u_1} {f : Filter α} {m : α → ENNR
eal} {a b : ENNReal},   Filter.Tendsto m f (nhds a) → a ≠ 0 ∨ b ≠ ⊤ → Filter.Ten
dsto (fun x => …
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `tendsto_inv_iff`：tendsto_inv_iff {l : Filter α} {m : α -> G} {a : G} : T
endsto (fun x => (m x)⁻¹) l (𝓝 a⁻¹) ↔ Tendsto m l (𝓝 a)
· 使用定理 `ENNReal.instContinuousInv`：ContinuousInv ENNReal
（共 44 条，此处仅展示前 30 条）

--- 原说明 ---
The points with `v.limRatioMeas hρ x = ∞` have measure `0` for `μ`.
-/
theorem measure_limRatioMeas_top : μ {x | v.limRatioMeas hρ x = ∞} = 0 := by
  refine measure_null_of_locally_null _ fun x _ => ?_
  obtain ⟨o, xo, o_open, μo⟩ : ∃ o : Set α, x ∈ o ∧ IsOpen o ∧ ρ o < ∞ :=
    Measure.exists_isOpen_measure_lt_top ρ x
  let s := {x : α | v.limRatioMeas hρ x = ∞} ∩ o
  refine ⟨s, inter_mem_nhdsWithin _ (o_open.mem_nhds xo), le_antisymm ?_ bot_le⟩
  have ρs : ρ s ≠ ∞ := measure_ne_top_of_subset inter_subset_right μo.ne
  have A : ∀ q : ℝ≥0, 1 ≤ q → μ s ≤ (q : ℝ≥0∞)⁻¹ * ρ s := by
    intro q hq
    rw [mul_comm, ← div_eq_mul_inv, ENNReal.le_div_iff_mul_le _ (Or.inr ρs), mul_comm]
    · apply v.mul_measure_le_of_subset_lt_limRatioMeas hρ
      intro y hy
      have : v.limRatioMeas hρ y = ∞ := hy.1
      simp only [this, ENNReal.coe_lt_top, mem_ofPred_eq]
    · simp only [(zero_lt_one.trans_le hq).ne', true_or, ENNReal.coe_eq_zero, Ne,
        not_false_iff]
  have B : Tendsto (fun q : ℝ≥0 => (q : ℝ≥0∞)⁻¹ * ρ s) atTop (𝓝 (∞⁻¹ * ρ s)) := by
    apply ENNReal.Tendsto.mul_const _ (Or.inr ρs)
    exact tendsto_inv_iff.2 (ENNReal.tendsto_coe_nhds_top.2 tendsto_id)
  simp only [zero_mul, ENNReal.inv_top] at B
  apply ge_of_tendsto B
  exact eventually_atTop.2 ⟨1, A⟩

/-- The points with `v.limRatioMeas hρ x = 0` have measure `0` for `ρ`. -/
/-
**VitaliFamily.measure_limRatioMeas_zero** 是 Mathlib 中的一个定理，位于命名空间 `VitaliFamily
`。
形式化陈述：measure_limRatioMeas_zero : ρ (v.limRatioMeas hρ ⁻¹' {0}) = 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.measure_null_of_locally_null`：measure_null_of_locally_null
 [TopologicalSpace α] [SecondCountableTopology α] (s : Set α) (hs : forall x in 
s, exists u in 𝓝[s] x, μ u = 0) …
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `MeasureTheory.Measure.exists_isOpen_measure_lt_top`：∀ {α : Type u_1} {m0
 : MeasurableSpace α} [inst : TopologicalSpace α] (μ : MeasureTheory.Measure α) 
  [MeasureTheory.IsLocallyFiniteMeasure …
· 使用定理 `inter_mem_nhdsWithin`：inter_mem_nhdsWithin (s : Set α) {t : Set α} {a : 
α} (h : t in 𝓝 a) : s inter t in 𝓝[s] a
· 使用定理 `IsOpen.mem_nhds`：IsOpen.mem_nhds (hs : IsOpen s) (hx : x in s) : s in 𝓝 
x
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `MeasureTheory.measure_ne_top_of_subset`：measure_ne_top_of_subset (h : t 
subseteq s) (ht : μ s != ∞) : μ t != ∞
· 使用定理 `Set.inter_subset_right`：inter_subset_right {s t : Set α} : s inter t sub
seteq t
· 使用定理 `LT.lt.ne`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≠ b
· 使用定理 `VitaliFamily.measure_le_mul_of_subset_limRatioMeas_lt`：measure_le_mul_of
_subset_limRatioMeas_lt {p : Real>=0} {s : Set α} (h : s subseteq {x | v.limRati
oMeas hρ x < p}) : ρ s <= p * μ s
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `ENNReal.Tendsto.mul_const`：∀ {α : Type u_1} {f : Filter α} {m : α → ENNR
eal} {a b : ENNReal},   Filter.Tendsto m f (nhds a) → a ≠ 0 ∨ b ≠ ⊤ → Filter.Ten
dsto (fun x => …
· 使用定理 `ENNReal.tendsto_coe`：tendsto_coe {f : Filter α} {m : α -> Real>=0} {a : 
Real>=0} : Tendsto (fun a => (m a : Real>=0∞)) f (𝓝 ↑a) ↔ Tendsto m f (𝓝 a)
· 使用定理 `nhdsWithin_le_nhds`：nhdsWithin_le_nhds {a : α} {s : Set α} : 𝓝[s] a <= 𝓝
 a
· 使用定理 `ge_of_tendsto`：∀ {α : Type u} {β : Type v} [inst : TopologicalSpace α] [
inst_1 : Preorder α] [ClosedIciTopology α] {f : β → α}   {a b : α} {x : Filter β
} […
· 使用定理 `instClosedIciTopology`：∀ {α : Type u} [inst : TopologicalSpace α] [inst_
1 : Preorder α] [t : OrderClosedTopology α], ClosedIciTopology α
· 使用定理 `OrderTopology.to_orderClosedTopology`：∀ {α : Type u} [inst : Topological
Space α] [inst_1 : LinearOrder α] [OrderTopology α], OrderClosedTopology α
· 使用定理 `ENNReal.instOrderTopology`：OrderTopology ENNReal
· 使用定理 `NNReal.instOrderTopology`：OrderTopology NNReal
· 使用定理 `NNReal.instDenselyOrdered`：DenselyOrdered NNReal
· 使用定理 `IsStrictOrderedRing.toNoMaxOrder`：∀ {R : Type u} [inst : Semiring R] [in
st_1 : PartialOrder R] [IsStrictOrderedRing R], NoMaxOrder R
· 使用定理 `NNReal.instIsStrictOrderedRing_1`：IsStrictOrderedRing NNReal
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `self_mem_nhdsWithin`：self_mem_nhdsWithin {a : α} {s : Set α} : s in 𝓝[s]
 a
（共 32 条，此处仅展示前 30 条）

--- 原说明 ---
The points with `v.limRatioMeas hρ x = 0` have measure `0` for `ρ`.
-/
theorem measure_limRatioMeas_zero : ρ (v.limRatioMeas hρ ⁻¹' {0}) = 0 := by
  refine measure_null_of_locally_null _ fun x _ => ?_
  obtain ⟨o, xo, o_open, μo⟩ : ∃ o : Set α, x ∈ o ∧ IsOpen o ∧ μ o < ∞ :=
    Measure.exists_isOpen_measure_lt_top μ x
  let s := {x : α | v.limRatioMeas hρ x = 0} ∩ o
  refine ⟨s, inter_mem_nhdsWithin _ (o_open.mem_nhds xo), le_antisymm ?_ bot_le⟩
  have μs : μ s ≠ ∞ := measure_ne_top_of_subset inter_subset_right μo.ne
  have A : ∀ q : ℝ≥0, 0 < q → ρ s ≤ q * μ s := by
    intro q hq
    apply v.measure_le_mul_of_subset_limRatioMeas_lt hρ
    intro y hy
    have : v.limRatioMeas hρ y = 0 := hy.1
    simp only [this, mem_ofPred_eq, hq, ENNReal.coe_pos]
  have B : Tendsto (fun q : ℝ≥0 => (q : ℝ≥0∞) * μ s) (𝓝[>] (0 : ℝ≥0)) (𝓝 ((0 : ℝ≥0) * μ s)) := by
    apply ENNReal.Tendsto.mul_const _ (Or.inr μs)
    rw [ENNReal.tendsto_coe]
    exact nhdsWithin_le_nhds
  simp only [zero_mul, ENNReal.coe_zero] at B
  apply ge_of_tendsto B
  filter_upwards [self_mem_nhdsWithin] using A

/-- As an intermediate step to show that `μ.withDensity (v.limRatioMeas hρ) = ρ`, we show here
that `μ.withDensity (v.limRatioMeas hρ) ≤ t^2 ρ` for any `t > 1`. -/
/-
**VitaliFamily.withDensity_le_mul** 是 Mathlib 中的一个定理，位于命名空间 `VitaliFamily`。
形式化陈述：withDensity_le_mul {s : Set α} (hs : MeasurableSet s) {t : Real>=0} (ht : 
1 < t) : μ.withDensity (v.limRatioMeas hρ) s <= (t : Real>=0∞) ^ 2 * ρ s
参数：hs : MeasurableSet s；ht : 1 < t。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `LT.lt.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a < b → b
 < c → a < c
· 使用定理 `zero_lt_one`：∀ {α : Type u_1} [inst : Zero α] [inst_1 : One α] [inst_2 :
 PartialOrder α] [ZeroLEOneClass α] [NeZero 1], 0 < 1
· 使用定理 `FloorSemiring.instZeroLEOneClass`：∀ {α : Type u_2} [inst : Semiring α] [
inst_1 : PartialOrder α] [FloorSemiring α], ZeroLEOneClass α
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `VitaliFamily.limRatioMeas_measurable`：limRatioMeas_measurable : Measurab
le (v.limRatioMeas hρ)
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `LE.le.trans'`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, b ≤ a → 
c ≤ b → c ≤ a
· 使用定理 `zero_le`：∀ {α : Type u_1} [inst : LE α] [inst_1 : Zero α] [IsBotZeroClas
s α] {a : α}, 0 ≤ a
· 使用定理 `instIsBotZeroClass`：∀ {α : Type u} [inst : AddZeroClass α] [inst_1 : LE 
α] [CanonicallyOrderedAdd α], IsBotZeroClass α
· 使用定理 `ENNReal.instCanonicallyOrderedAdd`：CanonicallyOrderedAdd ENNReal
· 使用定理 `MeasurableSet.inter`：∀ {α : Type u_1} {m : MeasurableSpace α} {s₁ s₂ : S
et α}, MeasurableSet s₁ → MeasurableSet s₂ → MeasurableSet (s₁ ∩ s₂)
· 使用定理 `MeasurableSingletonClass.measurableSet_singleton`：∀ {α : Type u_7} {inst
 : MeasurableSpace α} [self : MeasurableSingletonClass α] (x : α), MeasurableSet
 {x}
· 使用定理 `instMeasurableSingletonClassOfMeasurableEq`：∀ {α : Type u_1} [inst : Mea
surableSpace α] [MeasurableEq α], MeasurableSingletonClass α
· 使用定理 `StandardBorelSpace.instMeasurableEq`：∀ {α : Type u_1} [inst : Measurable
Space α] [StandardBorelSpace α], MeasurableEq α
· 使用定理 `standardBorel_of_polish`：∀ {α : Type u_1} [inst : MeasurableSpace α] [τ 
: TopologicalSpace α] [BorelSpace α] [PolishSpace α],   StandardBorelSpace α
· 使用定理 `PolishSpace.instENNReal`：PolishSpace ENNReal
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `MeasureTheory.withDensity_apply`：withDensity_apply (f : α -> Real>=0∞) {
s : Set α} (hs : MeasurableSet s) : μ.withDensity f s = ∫⁻ a in s, f a ∂μ
· 使用定理 `MeasureTheory.lintegral_eq_zero_iff`：lintegral_eq_zero_iff {f : α -> Rea
l>=0∞} (hf : Measurable f) : ∫⁻ a, f a ∂μ = 0 ↔ f =ᵐ[μ] 0
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `MeasureTheory.ae_restrict_iff'`：ae_restrict_iff'₀ {p : α -> Prop} (hs : 
NullMeasurableSet s μ) : (forallᵐ x ∂μ.restrict s, p x) ↔ forallᵐ x ∂μ, x in s -
> p x
· 使用定理 `Filter.Eventually.of_forall`：∀ {α : Type u} {p : α → Prop} {f : Filter α
}, (∀ (x : α), p x) → ∀ᶠ (x : α) in f, p x
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `MeasureTheory.withDensity_absolutelyContinuous`：withDensity_absolutelyCo
ntinuous {m : MeasurableSpace α} (μ : Measure α) (f : α -> Real>=0∞) : μ.withDen
sity f ≪ μ
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `nonpos_iff_eq_zero`：∀ {α : Type u_1} {a : α} [inst : PartialOrder α] [in
st_1 : Zero α] [IsBotZeroClass α], a ≤ 0 ↔ a = 0
（共 85 条，此处仅展示前 30 条）

--- 原说明 ---
As an intermediate step to show that `μ.withDensity (v.limRatioMeas hρ) = ρ`, we
 show here
that `μ.withDensity (v.limRatioMeas hρ) ≤ t^2 ρ` for any `t > 1`.
-/
theorem withDensity_le_mul {s : Set α} (hs : MeasurableSet s) {t : ℝ≥0} (ht : 1 < t) :
    μ.withDensity (v.limRatioMeas hρ) s ≤ (t : ℝ≥0∞) ^ 2 * ρ s := by
  /- We cut `s` into the sets where `v.limRatioMeas hρ = 0`, where `v.limRatioMeas hρ = ∞`, and
    where `v.limRatioMeas hρ ∈ [t^n, t^(n+1))` for `n : ℤ`. The first and second have measure `0`.
    For the latter, since `v.limRatioMeas hρ` fluctuates by at most `t` on this slice, we can use
    `measure_le_mul_of_subset_limRatioMeas_lt` and `mul_measure_le_of_subset_lt_limRatioMeas` to
    show that the two measures are comparable up to `t` (in fact `t^2` for technical reasons of
    strict inequalities). -/
  have t_ne_zero' : t ≠ 0 := (zero_lt_one.trans ht).ne'
  have t_ne_zero : (t : ℝ≥0∞) ≠ 0 := by simpa only [ENNReal.coe_eq_zero, Ne] using t_ne_zero'
  let ν := μ.withDensity (v.limRatioMeas hρ)
  let f := v.limRatioMeas hρ
  have f_meas : Measurable f := v.limRatioMeas_measurable hρ
  -- Note(kmill): smul elaborator when used for CoeFun fails to get CoeFun instance to trigger
  -- unless you use the `(... :)` notation. Another fix is using `(2 : Nat)`, so this appears
  -- to be an unpleasant interaction with default instances.
  have A : ν (s ∩ f ⁻¹' {0}) ≤ ((t : ℝ≥0∞) ^ 2 • ρ :) (s ∩ f ⁻¹' {0}) := by
    apply zero_le.trans'
    have M : MeasurableSet (s ∩ f ⁻¹' {0}) := hs.inter (f_meas (measurableSet_singleton _))
    simp only [f, ν, nonpos_iff_eq_zero, M, withDensity_apply, lintegral_eq_zero_iff f_meas]
    apply (ae_restrict_iff' M).2
    exact Eventually.of_forall fun x hx => hx.2
  have B : ν (s ∩ f ⁻¹' {∞}) ≤ ((t : ℝ≥0∞) ^ 2 • ρ :) (s ∩ f ⁻¹' {∞}) := by
    rw [withDensity_absolutelyContinuous μ]
    · exact zero_le
    · rw [← nonpos_iff_eq_zero]
      exact (measure_mono inter_subset_right).trans (v.measure_limRatioMeas_top hρ).le
  have C :
    ∀ n : ℤ,
      ν (s ∩ f ⁻¹' Ico ((t : ℝ≥0∞) ^ n) ((t : ℝ≥0∞) ^ (n + 1))) ≤
        ((t : ℝ≥0∞) ^ 2 • ρ :) (s ∩ f ⁻¹' Ico ((t : ℝ≥0∞) ^ n) ((t : ℝ≥0∞) ^ (n + 1))) := by
    intro n
    let I := Ico ((t : ℝ≥0∞) ^ n) ((t : ℝ≥0∞) ^ (n + 1))
    have M : MeasurableSet (s ∩ f ⁻¹' I) := hs.inter (f_meas measurableSet_Ico)
    simp only [ν, I, M, withDensity_apply]
    calc
      (∫⁻ x in s ∩ f ⁻¹' I, f x ∂μ) ≤ ∫⁻ _ in s ∩ f ⁻¹' I, (t : ℝ≥0∞) ^ (n + 1) ∂μ :=
        lintegral_mono_ae ((ae_restrict_iff' M).2 (Eventually.of_forall fun x hx => hx.2.2.le))
      _ = (t : ℝ≥0∞) ^ (n + 1) * μ (s ∩ f ⁻¹' I) := by
        simp only [lintegral_const, MeasurableSet.univ, Measure.restrict_apply, univ_inter]
      _ = (t : ℝ≥0∞) ^ (2 : ℤ) * ((t : ℝ≥0∞) ^ (n - 1) * μ (s ∩ f ⁻¹' I)) := by
        rw [← mul_assoc, ← ENNReal.zpow_add t_ne_zero ENNReal.coe_ne_top]
        congr 2
        abel
      _ ≤ (t : ℝ≥0∞) ^ (2 : ℤ) * ρ (s ∩ f ⁻¹' I) := by
        gcongr
        rw [← ENNReal.coe_zpow (zero_lt_one.trans ht).ne']
        apply v.mul_measure_le_of_subset_lt_limRatioMeas hρ
        intro x hx
        apply lt_of_lt_of_le _ hx.2.1
        rw [← ENNReal.coe_zpow (zero_lt_one.trans ht).ne', ENNReal.coe_lt_coe, sub_eq_add_neg,
          zpow_add₀ t_ne_zero']
        conv_rhs => rw [← mul_one (t ^ n)]
        gcongr
        rw [zpow_neg_one]
        exact inv_lt_one_of_one_lt₀ ht
  calc
    ν s =
      ν (s ∩ f ⁻¹' {0}) + ν (s ∩ f ⁻¹' {∞}) +
        ∑' n : ℤ, ν (s ∩ f ⁻¹' Ico ((t : ℝ≥0∞) ^ n) ((t : ℝ≥0∞) ^ (n + 1))) :=
      measure_eq_measure_preimage_add_measure_tsum_Ico_zpow ν f_meas hs ht
    _ ≤
        ((t : ℝ≥0∞) ^ 2 • ρ :) (s ∩ f ⁻¹' {0}) + ((t : ℝ≥0∞) ^ 2 • ρ :) (s ∩ f ⁻¹' {∞}) +
          ∑' n : ℤ, ((t : ℝ≥0∞) ^ 2 • ρ :) (s ∩ f ⁻¹' Ico (t ^ n) (t ^ (n + 1))) :=
      (add_le_add (add_le_add A B) (ENNReal.tsum_le_tsum C))
    _ = ((t : ℝ≥0∞) ^ 2 • ρ :) s :=
      (measure_eq_measure_preimage_add_measure_tsum_Ico_zpow ((t : ℝ≥0∞) ^ 2 • ρ) f_meas hs ht).symm

/-- As an intermediate step to show that `μ.withDensity (v.limRatioMeas hρ) = ρ`, we show here
that `ρ ≤ t μ.withDensity (v.limRatioMeas hρ)` for any `t > 1`. -/
/-
**VitaliFamily.le_mul_withDensity** 是 Mathlib 中的一个定理，位于命名空间 `VitaliFamily`。
形式化陈述：le_mul_withDensity {s : Set α} (hs : MeasurableSet s) {t : Real>=0} (ht : 
1 < t) : ρ s <= t * μ.withDensity (v.limRatioMeas hρ) s
参数：hs : MeasurableSet s；ht : 1 < t。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `LT.lt.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a < b → b
 < c → a < c
· 使用定理 `zero_lt_one`：∀ {α : Type u_1} [inst : Zero α] [inst_1 : One α] [inst_2 :
 PartialOrder α] [ZeroLEOneClass α] [NeZero 1], 0 < 1
· 使用定理 `FloorSemiring.instZeroLEOneClass`：∀ {α : Type u_2} [inst : Semiring α] [
inst_1 : PartialOrder α] [FloorSemiring α], ZeroLEOneClass α
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `VitaliFamily.limRatioMeas_measurable`：limRatioMeas_measurable : Measurab
le (v.limRatioMeas hρ)
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `le_imp_le_of_le_of_le`：le_imp_le_of_le_of_le (h₁ : c <= a) (h₂ : b <= d)
 : a <= b -> c <= d
· 使用定理 `MeasureTheory.measure_mono`：measure_mono (h : s subseteq t) : μ s <= μ t
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `Set.inter_subset_right`：inter_subset_right {s t : Set α} : s inter t sub
seteq t
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `VitaliFamily.measure_limRatioMeas_zero`：measure_limRatioMeas_zero : ρ (v
.limRatioMeas hρ ⁻¹' {0}) = 0
· 使用定理 `zero_le`：∀ {α : Type u_1} [inst : LE α] [inst_1 : Zero α] [IsBotZeroClas
s α] {a : α}, 0 ≤ a
· 使用定理 `instIsBotZeroClass`：∀ {α : Type u} [inst : AddZeroClass α] [inst_1 : LE 
α] [CanonicallyOrderedAdd α], IsBotZeroClass α
· 使用定理 `ENNReal.instCanonicallyOrderedAdd`：CanonicallyOrderedAdd ENNReal
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `Eq.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → a ≤ b
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `nonpos_iff_eq_zero`：∀ {α : Type u_1} {a : α} [inst : PartialOrder α] [in
st_1 : Zero α] [IsBotZeroClass α], a ≤ 0 ↔ a = 0
· 使用定理 `VitaliFamily.measure_limRatioMeas_top`：measure_limRatioMeas_top : μ {x |
 v.limRatioMeas hρ x = ∞} = 0
· 使用定理 `MeasurableSet.inter`：∀ {α : Type u_1} {m : MeasurableSpace α} {s₁ s₂ : S
et α}, MeasurableSet s₁ → MeasurableSet s₂ → MeasurableSet (s₁ ∩ s₂)
· 使用定理 `measurableSet_Ico`：measurableSet_Ico [ClosedIciTopology α] : MeasurableS
et (Ico a b)
· 使用定理 `BorelSpace.opensMeasurable`：∀ {α : Type u_6} [inst : TopologicalSpace α]
 [inst_1 : MeasurableSpace α] [BorelSpace α], OpensMeasurableSpace α
· 使用定理 `instClosedIciTopology`：∀ {α : Type u} [inst : TopologicalSpace α] [inst_
1 : Preorder α] [t : OrderClosedTopology α], ClosedIciTopology α
· 使用定理 `OrderTopology.to_orderClosedTopology`：∀ {α : Type u} [inst : Topological
Space α] [inst_1 : LinearOrder α] [OrderTopology α], OrderClosedTopology α
· 使用定理 `ENNReal.instOrderTopology`：OrderTopology ENNReal
· 使用定理 `MeasureTheory.withDensity_apply`：withDensity_apply (f : α -> Real>=0∞) {
s : Set α} (hs : MeasurableSet s) : μ.withDensity f s = ∫⁻ a in s, f a ∂μ
· 使用定理 `ENNReal.coe_zpow`：coe_zpow (hr : r != 0) (n : Int) : (↑(r ^ n) : Real>=0
∞) = (r : Real>=0∞) ^ n
（共 59 条，此处仅展示前 30 条）

--- 原说明 ---
As an intermediate step to show that `μ.withDensity (v.limRatioMeas hρ) = ρ`, we
 show here
that `ρ ≤ t μ.withDensity (v.limRatioMeas hρ)` for any `t > 1`.
-/
theorem le_mul_withDensity {s : Set α} (hs : MeasurableSet s) {t : ℝ≥0} (ht : 1 < t) :
    ρ s ≤ t * μ.withDensity (v.limRatioMeas hρ) s := by
  /- We cut `s` into the sets where `v.limRatioMeas hρ = 0`, where `v.limRatioMeas hρ = ∞`, and
    where `v.limRatioMeas hρ ∈ [t^n, t^(n+1))` for `n : ℤ`. The first and second have measure `0`.
    For the latter, since `v.limRatioMeas hρ` fluctuates by at most `t` on this slice, we can use
    `measure_le_mul_of_subset_limRatioMeas_lt` and `mul_measure_le_of_subset_lt_limRatioMeas` to
    show that the two measures are comparable up to `t`. -/
  have t_ne_zero' : t ≠ 0 := (zero_lt_one.trans ht).ne'
  have t_ne_zero : (t : ℝ≥0∞) ≠ 0 := by simpa only [ENNReal.coe_eq_zero, Ne] using t_ne_zero'
  let ν := μ.withDensity (v.limRatioMeas hρ)
  let f := v.limRatioMeas hρ
  have f_meas : Measurable f := v.limRatioMeas_measurable hρ
  have A : ρ (s ∩ f ⁻¹' {0}) ≤ (t • ν) (s ∩ f ⁻¹' {0}) := by
    grw [measure_mono inter_subset_right, v.measure_limRatioMeas_zero hρ]
    exact zero_le
  have B : ρ (s ∩ f ⁻¹' {∞}) ≤ (t • ν) (s ∩ f ⁻¹' {∞}) := by
    apply (hρ _).le.trans zero_le
    rw [← nonpos_iff_eq_zero]
    exact (measure_mono inter_subset_right).trans (v.measure_limRatioMeas_top hρ).le
  have C :
    ∀ n : ℤ,
      ρ (s ∩ f ⁻¹' Ico ((t : ℝ≥0∞) ^ n) ((t : ℝ≥0∞) ^ (n + 1))) ≤
        (t • ν) (s ∩ f ⁻¹' Ico ((t : ℝ≥0∞) ^ n) ((t : ℝ≥0∞) ^ (n + 1))) := by
    intro n
    let I := Ico ((t : ℝ≥0∞) ^ n) ((t : ℝ≥0∞) ^ (n + 1))
    have M : MeasurableSet (s ∩ f ⁻¹' I) := hs.inter (f_meas measurableSet_Ico)
    simp only [ν, I, M, withDensity_apply, coe_nnreal_smul_apply]
    calc
      ρ (s ∩ f ⁻¹' I) ≤ (t : ℝ≥0∞) ^ (n + 1) * μ (s ∩ f ⁻¹' I) := by
        rw [← ENNReal.coe_zpow t_ne_zero']
        apply v.measure_le_mul_of_subset_limRatioMeas_lt hρ
        intro x hx
        apply hx.2.2.trans_le (le_of_eq _)
        rw [ENNReal.coe_zpow t_ne_zero']
      _ = ∫⁻ _ in s ∩ f ⁻¹' I, (t : ℝ≥0∞) ^ (n + 1) ∂μ := by
        simp only [lintegral_const, MeasurableSet.univ, Measure.restrict_apply, univ_inter]
      _ ≤ ∫⁻ x in s ∩ f ⁻¹' I, t * f x ∂μ := by
        apply lintegral_mono_ae ((ae_restrict_iff' M).2 (Eventually.of_forall fun x hx => ?_))
        grw [add_comm, ENNReal.zpow_add t_ne_zero ENNReal.coe_ne_top, zpow_one, hx.2.1]
      _ = t * ∫⁻ x in s ∩ f ⁻¹' I, f x ∂μ := lintegral_const_mul _ f_meas
  calc
    ρ s =
      ρ (s ∩ f ⁻¹' {0}) + ρ (s ∩ f ⁻¹' {∞}) +
        ∑' n : ℤ, ρ (s ∩ f ⁻¹' Ico ((t : ℝ≥0∞) ^ n) ((t : ℝ≥0∞) ^ (n + 1))) :=
      measure_eq_measure_preimage_add_measure_tsum_Ico_zpow ρ f_meas hs ht
    _ ≤
        (t • ν) (s ∩ f ⁻¹' {0}) + (t • ν) (s ∩ f ⁻¹' {∞}) +
          ∑' n : ℤ, (t • ν) (s ∩ f ⁻¹' Ico ((t : ℝ≥0∞) ^ n) ((t : ℝ≥0∞) ^ (n + 1))) :=
      (add_le_add (add_le_add A B) (ENNReal.tsum_le_tsum C))
    _ = (t • ν) s :=
      (measure_eq_measure_preimage_add_measure_tsum_Ico_zpow (t • ν) f_meas hs ht).symm
/-
**VitaliFamily.withDensity_limRatioMeas_eq** 是 Mathlib 中的一个定理，位于命名空间 `VitaliFami
ly`。
形式化陈述：withDensity_limRatioMeas_eq : μ.withDensity (v.limRatioMeas hρ) = ρ
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.ext`：ext (h : forall s, MeasurableSet s -> μ₁ s = 
μ₂ s) : μ₁ = μ₂
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `ENNReal.Tendsto.mul`：∀ {α : Type u_1} {f : Filter α} {ma mb : α → ENNRea
l} {a b : ENNReal},   Filter.Tendsto ma f (nhds a) →     a ≠ 0 ∨ b ≠ ⊤ →       F
ilter.Ten…
· 使用定理 `ENNReal.Tendsto.pow`：∀ {α : Type u_1} {f : Filter α} {m : α → ENNReal} {
a : ENNReal} {n : ℕ},   Filter.Tendsto m f (nhds a) → Filter.Tendsto (fun x => m
 x ^ n) f…
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `ENNReal.tendsto_coe`：tendsto_coe {f : Filter α} {m : α -> Real>=0} {a : 
Real>=0} : Tendsto (fun a => (m a : Real>=0∞)) f (𝓝 ↑a) ↔ Tendsto m f (𝓝 a)
· 使用定理 `nhdsWithin_le_nhds`：nhdsWithin_le_nhds {a : α} {s : Set α} : 𝓝[s] a <= 𝓝
 a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `one_pow`：one_pow {a : R} (b : Nat) (ha : IsNat a 1) : a ^ b = a
· 使用定理 `ENNReal.instCharZero`：CharZero ENNReal
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `true_or`：∀ (p : Prop), (True ∨ p) = True
· 使用定理 `tendsto_const_nhds`：tendsto_const_nhds {f : Filter α} : Tendsto (fun _ :
 α => x) f (𝓝 x)
· 使用定理 `or_true`：∀ (p : Prop), (p ∨ True) = True
· 使用定理 `ge_of_tendsto`：∀ {α : Type u} {β : Type v} [inst : TopologicalSpace α] [
inst_1 : Preorder α] [ClosedIciTopology α] {f : β → α}   {a b : α} {x : Filter β
} […
· 使用定理 `instClosedIciTopology`：∀ {α : Type u} [inst : TopologicalSpace α] [inst_
1 : Preorder α] [t : OrderClosedTopology α], ClosedIciTopology α
· 使用定理 `OrderTopology.to_orderClosedTopology`：∀ {α : Type u} [inst : Topological
Space α] [inst_1 : LinearOrder α] [OrderTopology α], OrderClosedTopology α
· 使用定理 `ENNReal.instOrderTopology`：OrderTopology ENNReal
· 使用定理 `NNReal.instOrderTopology`：OrderTopology NNReal
· 使用定理 `NNReal.instDenselyOrdered`：DenselyOrdered NNReal
· 使用定理 `IsStrictOrderedRing.toNoMaxOrder`：∀ {R : Type u} [inst : Semiring R] [in
st_1 : PartialOrder R] [IsStrictOrderedRing R], NoMaxOrder R
· 使用定理 `NNReal.instIsStrictOrderedRing_1`：IsStrictOrderedRing NNReal
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `self_mem_nhdsWithin`：self_mem_nhdsWithin {a : α} {s : Set α} : s in 𝓝[s]
 a
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `VitaliFamily.withDensity_le_mul`：withDensity_le_mul {s : Set α} (hs : Me
asurableSet s) {t : Real>=0} (ht : 1 < t) : μ.withDensity (v.limRatioMeas hρ) s 
<= (t : Real>=0∞) ^ 2…
（共 32 条，此处仅展示前 30 条）
-/
theorem withDensity_limRatioMeas_eq : μ.withDensity (v.limRatioMeas hρ) = ρ := by
  ext1 s hs
  refine le_antisymm ?_ ?_
  · have : Tendsto (fun t : ℝ≥0 =>
        ((t : ℝ≥0∞) ^ 2 * ρ s : ℝ≥0∞)) (𝓝[>] 1) (𝓝 ((1 : ℝ≥0∞) ^ 2 * ρ s)) := by
      refine ENNReal.Tendsto.mul ?_ ?_ tendsto_const_nhds ?_
      · exact ENNReal.Tendsto.pow (ENNReal.tendsto_coe.2 nhdsWithin_le_nhds)
      · simp
      · simp only [one_pow, Ne, or_true, ENNReal.one_ne_top, not_false_iff]
    simp only [one_pow, one_mul] at this
    refine ge_of_tendsto this ?_
    filter_upwards [self_mem_nhdsWithin] with _ ht
    exact v.withDensity_le_mul hρ hs ht
  · have :
      Tendsto (fun t : ℝ≥0 => (t : ℝ≥0∞) * μ.withDensity (v.limRatioMeas hρ) s) (𝓝[>] 1)
        (𝓝 ((1 : ℝ≥0∞) * μ.withDensity (v.limRatioMeas hρ) s)) := by
      refine ENNReal.Tendsto.mul_const (ENNReal.tendsto_coe.2 nhdsWithin_le_nhds) ?_
      simp only [true_or, Ne, not_false_iff, one_ne_zero]
    simp only [one_mul] at this
    refine ge_of_tendsto this ?_
    filter_upwards [self_mem_nhdsWithin] with _ ht
    exact v.le_mul_withDensity hρ hs ht

/-- Weak version of the main theorem on differentiation of measures: given a Vitali family `v`
for a locally finite measure `μ`, and another locally finite measure `ρ`, then for `μ`-almost
every `x` the ratio `ρ a / μ a` converges, when `a` shrinks to `x` along the Vitali family,
towards the Radon-Nikodym derivative of `ρ` with respect to `μ`.

This version assumes that `ρ` is absolutely continuous with respect to `μ`. The general version
without this superfluous assumption is `VitaliFamily.ae_tendsto_rnDeriv`.
-/
/-
**VitaliFamily.ae_tendsto_rnDeriv_of_absolutelyContinuous** 是 Mathlib 中的一个定理，位于命
名空间 `VitaliFamily`。
形式化陈述：ae_tendsto_rnDeriv_of_absolutelyContinuous : forallᵐ x ∂μ, Tendsto (fun a 
=> ρ a / μ a) (v.filterAt x) (𝓝 (ρ.rnDeriv μ x))
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `MeasureTheory.Measure.rnDeriv_withDensity`：rnDeriv_withDensity (ν : Meas
ure α) [SigmaFinite ν] {f : α -> Real>=0∞} (hf : Measurable f) : (ν.withDensity 
f).rnDeriv ν =ᵐ[ν] f
· 使用定理 `MeasureTheory.sigmaFinite_of_locallyFinite`：∀ {α : Type u_1} {m0 : Measu
rableSpace α} {μ : MeasureTheory.Measure α} [inst : TopologicalSpace α]   [Secon
dCountableTopology α] [MeasureTh…
· 使用定理 `VitaliFamily.limRatioMeas_measurable`：limRatioMeas_measurable : Measurab
le (v.limRatioMeas hρ)
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `VitaliFamily.withDensity_limRatioMeas_eq`：withDensity_limRatioMeas_eq : 
μ.withDensity (v.limRatioMeas hρ) = ρ
· 使用定理 `VitaliFamily.ae_tendsto_limRatioMeas`：ae_tendsto_limRatioMeas : forallᵐ 
x ∂μ, Tendsto (fun a => ρ a / μ a) (v.filterAt x) (𝓝 (v.limRatioMeas hρ x))
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f

--- 原说明 ---
Weak version of the main theorem on differentiation of measures: given a Vitali 
family `v`
for a locally finite measure `μ`, and another locally finite measure `ρ`, then f
or `μ`-almost
every `x` the ratio `ρ a / μ a` converges, when `a` shrinks to `x` along the Vit
ali family,
towards the Radon-Nikodym derivative of `ρ` with respect to `μ`.

This version assumes that `ρ` is absolutely continuous with respect to `μ`. The 
general version
without this superfluous assumption is `VitaliFamily.ae_tendsto_rnDeriv`.
-/
theorem ae_tendsto_rnDeriv_of_absolutelyContinuous :
    ∀ᵐ x ∂μ, Tendsto (fun a => ρ a / μ a) (v.filterAt x) (𝓝 (ρ.rnDeriv μ x)) := by
  have A : (μ.withDensity (v.limRatioMeas hρ)).rnDeriv μ =ᵐ[μ] v.limRatioMeas hρ :=
    rnDeriv_withDensity μ (v.limRatioMeas_measurable hρ)
  rw [v.withDensity_limRatioMeas_eq hρ] at A
  filter_upwards [v.ae_tendsto_limRatioMeas hρ, A] with _ _ h'x
  rwa [h'x]

end AbsolutelyContinuous

variable (ρ)

/-- Main theorem on differentiation of measures: given a Vitali family `v` for a locally finite
measure `μ`, and another locally finite measure `ρ`, then for `μ`-almost every `x` the
ratio `ρ a / μ a` converges, when `a` shrinks to `x` along the Vitali family, towards the
Radon-Nikodym derivative of `ρ` with respect to `μ`. -/
/-
**VitaliFamily.ae_tendsto_rnDeriv** 是 Mathlib 中的一个定理，位于命名空间 `VitaliFamily`。
形式化陈述：ae_tendsto_rnDeriv : forallᵐ x ∂μ, Tendsto (fun a => ρ a / μ a) (v.filterA
t x) (𝓝 (ρ.rnDeriv μ x))
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.haveLebesgueDecomposition_add`：haveLebesgueDecompo
sition_add (μ ν : Measure α) [HaveLebesgueDecomposition μ ν] : μ = μ.singularPar
t ν + ν.withDensity (μ.rnDeriv ν)
· 使用定理 `MeasureTheory.Measure.haveLebesgueDecomposition_of_sigmaFinite`：∀ {α : T
ype u_1} {m : MeasurableSpace α} (μ ν : MeasureTheory.Measure α) [MeasureTheory.
SFinite μ]   [MeasureTheory.SigmaFinite ν], μ.HaveLe…
· 使用定理 `MeasureTheory.instSFiniteOfSigmaFinite`：∀ {α : Type u_1} {m0 : Measurabl
eSpace α} {μ : MeasureTheory.Measure α} [MeasureTheory.SigmaFinite μ],   Measure
Theory.SFinite μ
· 使用定理 `MeasureTheory.sigmaFinite_of_locallyFinite`：∀ {α : Type u_1} {m0 : Measu
rableSpace α} {μ : MeasureTheory.Measure α} [inst : TopologicalSpace α]   [Secon
dCountableTopology α] [MeasureTh…
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `VitaliFamily.ae_eventually_measure_zero_of_singular`：ae_eventually_measu
re_zero_of_singular (hρ : ρ ⟂ₘ μ) : forallᵐ x ∂μ, Tendsto (fun a => ρ a / μ a) (
v.filterAt x) (𝓝 0)
· 使用定理 `MeasureTheory.Measure.singularPart.instIsLocallyFiniteMeasure`：∀ {α : Ty
pe u_1} {m : MeasurableSpace α} {μ ν : MeasureTheory.Measure α} [inst : Topologi
calSpace α]   [MeasureTheory.IsLocallyFiniteMeasure…
· 使用定理 `MeasureTheory.Measure.mutuallySingular_singularPart`：mutuallySingular_si
ngularPart (μ ν : Measure α) : μ.singularPart ν ⟂ₘ ν
· 使用定理 `MeasureTheory.Measure.rnDeriv_withDensity`：rnDeriv_withDensity (ν : Meas
ure α) [SigmaFinite ν] {f : α -> Real>=0∞} (hf : Measurable f) : (ν.withDensity 
f).rnDeriv ν =ᵐ[ν] f
· 使用定理 `MeasureTheory.Measure.measurable_rnDeriv`：measurable_rnDeriv (μ ν : Meas
ure α) : Measurable μ.rnDeriv ν
· 使用定理 `VitaliFamily.ae_tendsto_rnDeriv_of_absolutelyContinuous`：ae_tendsto_rnDe
riv_of_absolutelyContinuous : forallᵐ x ∂μ, Tendsto (fun a => ρ a / μ a) (v.filt
erAt x) (𝓝 (ρ.rnDeriv μ x))
· 使用定理 `MeasureTheory.Measure.withDensity.instIsLocallyFiniteMeasure`：∀ {α : Typ
e u_1} {m : MeasurableSpace α} {μ ν : MeasureTheory.Measure α} [inst : Topologic
alSpace α]   [MeasureTheory.IsLocallyFiniteMeasure…
· 使用定理 `MeasureTheory.withDensity_absolutelyContinuous`：withDensity_absolutelyCo
ntinuous {m : MeasurableSpace α} (μ : Measure α) (f : α -> Real>=0∞) : μ.withDen
sity f ≪ μ
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `ENNReal.add_div`：∀ {a b c : ENNReal}, (a + b) / c = a / c + b / c
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `Filter.Tendsto.add`：∀ {M : Type u_1} [inst : TopologicalSpace M] [inst_1
 : Add M] [ContinuousAdd M] {α : Type u_2} {f g : α → M}   {x : Filter α} {a b :
 M},   F…
· 使用定理 `ENNReal.instContinuousAdd`：ContinuousAdd ENNReal

--- 原说明 ---
Main theorem on differentiation of measures: given a Vitali family `v` for a loc
ally finite
measure `μ`, and another locally finite measure `ρ`, then for `μ`-almost every `
x` the
ratio `ρ a / μ a` converges, when `a` shrinks to `x` along the Vitali family, to
wards the
Radon-Nikodym derivative of `ρ` with respect to `μ`.
-/
theorem ae_tendsto_rnDeriv :
    ∀ᵐ x ∂μ, Tendsto (fun a => ρ a / μ a) (v.filterAt x) (𝓝 (ρ.rnDeriv μ x)) := by
  let t := μ.withDensity (ρ.rnDeriv μ)
  have eq_add : ρ = ρ.singularPart μ + t := haveLebesgueDecomposition_add _ _
  have A : ∀ᵐ x ∂μ, Tendsto (fun a => ρ.singularPart μ a / μ a) (v.filterAt x) (𝓝 0) :=
    v.ae_eventually_measure_zero_of_singular (mutuallySingular_singularPart ρ μ)
  have B : ∀ᵐ x ∂μ, t.rnDeriv μ x = ρ.rnDeriv μ x :=
    rnDeriv_withDensity μ (measurable_rnDeriv ρ μ)
  have C : ∀ᵐ x ∂μ, Tendsto (fun a => t a / μ a) (v.filterAt x) (𝓝 (t.rnDeriv μ x)) :=
    v.ae_tendsto_rnDeriv_of_absolutelyContinuous (withDensity_absolutelyContinuous _ _)
  filter_upwards [A, B, C] with _ Ax Bx Cx
  convert! Ax.add Cx using 1
  · ext1 a
    conv_lhs => rw [eq_add]
    simp only [Pi.add_apply, coe_add, ENNReal.add_div]
  · simp only [Bx, zero_add]

/-! ### Lebesgue density points -/


/-- Given a measurable set `s`, then `μ (s ∩ a) / μ a` converges when `a` shrinks to a typical
point `x` along a Vitali family. The limit is `1` for `x ∈ s` and `0` for `x ∉ s`. This shows that
almost every point of `s` is a Lebesgue density point for `s`. A version for non-measurable sets
holds, but it only gives the first conclusion, see `ae_tendsto_measure_inter_div`. -/
/-
**VitaliFamily.ae_tendsto_measure_inter_div_of_measurableSet** 是 Mathlib 中的一个定理，
位于命名空间 `VitaliFamily`。
形式化陈述：ae_tendsto_measure_inter_div_of_measurableSet {s : Set α} (hs : Measurable
Set s) : forallᵐ x ∂μ, Tendsto (fun a => μ (s inter a) / μ a) (v.filterAt x) (𝓝 
(s.indicator 1 x))
参数：hs : MeasurableSet s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.isLocallyFiniteMeasure_of_le`：isLocallyFiniteMeasu
re_of_le [TopologicalSpace α] {_m : MeasurableSpace α} {μ ν : Measure α} [H : Is
LocallyFiniteMeasure μ] (h : ν <= μ) : I…
· 使用定理 `MeasureTheory.Measure.restrict_le_self`：restrict_le_self : μ.restrict s 
<= μ
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `MeasureTheory.Measure.rnDeriv_restrict_self`：rnDeriv_restrict_self (ν : 
Measure α) [SigmaFinite ν] {s : Set α} (hs : MeasurableSet s) : (ν.restrict s).r
nDeriv ν =ᵐ[ν] s.indicator 1
· 使用定理 `MeasureTheory.sigmaFinite_of_locallyFinite`：∀ {α : Type u_1} {m0 : Measu
rableSpace α} {μ : MeasureTheory.Measure α} [inst : TopologicalSpace α]   [Secon
dCountableTopology α] [MeasureTh…
· 使用定理 `VitaliFamily.ae_tendsto_rnDeriv`：ae_tendsto_rnDeriv : forallᵐ x ∂μ, Tend
sto (fun a => ρ a / μ a) (v.filterAt x) (𝓝 (ρ.rnDeriv μ x))
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `MeasureTheory.Measure.restrict_apply'`：restrict_apply' (hs : MeasurableS
et s) : μ.restrict s t = μ (t inter s)
· 使用定理 `Set.inter_comm`：inter_comm (a b : Set α) : a inter b = b inter a

--- 原说明 ---
Given a measurable set `s`, then `μ (s ∩ a) / μ a` converges when `a` shrinks to
 a typical
point `x` along a Vitali family. The limit is `1` for `x ∈ s` and `0` for `x ∉ s
`. This shows that
almost every point of `s` is a Lebesgue density point for `s`. A version for non
-measurable sets
holds, but it only gives the first conclusion, see `ae_tendsto_measure_inter_div
`.
-/
theorem ae_tendsto_measure_inter_div_of_measurableSet {s : Set α} (hs : MeasurableSet s) :
    ∀ᵐ x ∂μ, Tendsto (fun a => μ (s ∩ a) / μ a) (v.filterAt x) (𝓝 (s.indicator 1 x)) := by
  have : IsLocallyFiniteMeasure (μ.restrict s) :=
    isLocallyFiniteMeasure_of_le restrict_le_self
  filter_upwards [ae_tendsto_rnDeriv v (μ.restrict s), rnDeriv_restrict_self μ hs]
  intro x hx h'x
  simpa only [h'x, restrict_apply' hs, inter_comm] using hx

/-- Given an arbitrary set `s`, then `μ (s ∩ a) / μ a` converges to `1` when `a` shrinks to a
typical point of `s` along a Vitali family. This shows that almost every point of `s` is a
Lebesgue density point for `s`. A stronger version for measurable sets is given
in `ae_tendsto_measure_inter_div_of_measurableSet`. -/
/-
**VitaliFamily.ae_tendsto_measure_inter_div** 是 Mathlib 中的一个定理，位于命名空间 `VitaliFam
ily`。
形式化陈述：ae_tendsto_measure_inter_div (s : Set α) : forallᵐ x ∂μ.restrict s, Tendst
o (fun a => μ (s inter a) / μ a) (v.filterAt x) (𝓝 1)
参数：s : Set α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `MeasureTheory.ae_mono`：ae_mono (h : μ <= ν) : ae μ <= ae ν
· 使用定理 `MeasureTheory.Measure.restrict_le_self`：restrict_le_self : μ.restrict s 
<= μ
· 使用定理 `VitaliFamily.ae_tendsto_measure_inter_div_of_measurableSet`：ae_tendsto_m
easure_inter_div_of_measurableSet {s : Set α} (hs : MeasurableSet s) : forallᵐ x
 ∂μ, Tendsto (fun a => μ (s inter a) / μ a) (v.f…
· 使用定理 `MeasureTheory.measurableSet_toMeasurable`：measurableSet_toMeasurable (μ 
: Measure α) (s : Set α) : MeasurableSet (toMeasurable μ s)
· 使用定理 `MeasureTheory.ae_restrict_of_ae_restrict_of_subset`：ae_restrict_of_ae_re
strict_of_subset {s t : Set α} {p : α -> Prop} (hst : s subseteq t) (h : forallᵐ
 x ∂μ.restrict t, p x) : forallᵐ x ∂μ.re…
· 使用定理 `MeasureTheory.subset_toMeasurable`：subset_toMeasurable (μ : Measure α) (
s : Set α) : s subseteq toMeasurable μ s
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `MeasureTheory.ae_restrict_mem`：ae_restrict_mem (hs : MeasurableSet s) : 
forallᵐ x ∂μ.restrict s, x in s
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.indicator_of_mem`：∀ {α : Type u_1} {M : Type u_3} [inst : Zero M] {s
 : Set α} {a : α}, a ∈ s → ∀ (f : α → M), s.indicator f a = f a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Filter.Tendsto.congr'`：∀ {α : Type u_1} {β : Type u_2} {f₁ f₂ : α → β} {
l₁ : Filter α} {l₂ : Filter β},   f₁ =ᶠ[l₁] f₂ → Filter.Tendsto f₁ l₁ l₂ → Filte
r.Tendsto f…
· 使用定理 `VitaliFamily.eventually_filterAt_measurableSet`：eventually_filterAt_meas
urableSet (x : X) : forallᶠ t in v.filterAt x, MeasurableSet t
· 使用定理 `MeasureTheory.Measure.measure_toMeasurable_inter_of_sFinite`：measure_toM
easurable_inter_of_sFinite [SFinite μ] {s : Set α} (hs : MeasurableSet s) (t : S
et α) : μ (toMeasurable μ t inter s) = μ (t inter…
· 使用定理 `MeasureTheory.instSFiniteOfSigmaFinite`：∀ {α : Type u_1} {m0 : Measurabl
eSpace α} {μ : MeasureTheory.Measure α} [MeasureTheory.SigmaFinite μ],   Measure
Theory.SFinite μ
· 使用定理 `MeasureTheory.sigmaFinite_of_locallyFinite`：∀ {α : Type u_1} {m0 : Measu
rableSpace α} {μ : MeasureTheory.Measure α} [inst : TopologicalSpace α]   [Secon
dCountableTopology α] [MeasureTh…

--- 原说明 ---
Given an arbitrary set `s`, then `μ (s ∩ a) / μ a` converges to `1` when `a` shr
inks to a
typical point of `s` along a Vitali family. This shows that almost every point o
f `s` is a
Lebesgue density point for `s`. A stronger version for measurable sets is given
in `ae_tendsto_measure_inter_div_of_measurableSet`.
-/
theorem ae_tendsto_measure_inter_div (s : Set α) :
    ∀ᵐ x ∂μ.restrict s, Tendsto (fun a => μ (s ∩ a) / μ a) (v.filterAt x) (𝓝 1) := by
  let t := toMeasurable μ s
  have A :
    ∀ᵐ x ∂μ.restrict s,
      Tendsto (fun a => μ (t ∩ a) / μ a) (v.filterAt x) (𝓝 (t.indicator 1 x)) := by
    apply ae_mono restrict_le_self
    apply ae_tendsto_measure_inter_div_of_measurableSet
    exact measurableSet_toMeasurable _ _
  have B : ∀ᵐ x ∂μ.restrict s, t.indicator 1 x = (1 : ℝ≥0∞) := by
    refine ae_restrict_of_ae_restrict_of_subset (subset_toMeasurable μ s) ?_
    filter_upwards [ae_restrict_mem (measurableSet_toMeasurable μ s)] with _ hx
    simp only [t, hx, Pi.one_apply, indicator_of_mem]
  filter_upwards [A, B] with x hx h'x
  rw [h'x] at hx
  apply hx.congr' _
  filter_upwards [v.eventually_filterAt_measurableSet x] with _ ha
  congr 1
  exact measure_toMeasurable_inter_of_sFinite ha _

/-! ### Lebesgue differentiation theorem -/

/-
**VitaliFamily.ae_tendsto_lintegral_div'** 是 Mathlib 中的一个定理，位于命名空间 `VitaliFamily
`。
形式化陈述：ae_tendsto_lintegral_div' {f : α -> Real>=0∞} (hf : Measurable f) (h'f : (
∫⁻ y, f y ∂μ) != ∞) : forallᵐ x ∂μ, Tendsto (fun a => (∫⁻ y in a, f y ∂μ) / μ a)
 (v.filterAt x) (𝓝 (f x))
参数：hf : Measurable f；h'f : (∫⁻ y, f y ∂μ) != ∞。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.isFiniteMeasure_withDensity`：isFiniteMeasure_withDensity {
f : α -> Real>=0∞} (hf : ∫⁻ a, f a ∂μ != ∞) : IsFiniteMeasure (μ.withDensity f)
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `MeasureTheory.Measure.rnDeriv_withDensity`：rnDeriv_withDensity (ν : Meas
ure α) [SigmaFinite ν] {f : α -> Real>=0∞} (hf : Measurable f) : (ν.withDensity 
f).rnDeriv ν =ᵐ[ν] f
· 使用定理 `MeasureTheory.sigmaFinite_of_locallyFinite`：∀ {α : Type u_1} {m0 : Measu
rableSpace α} {μ : MeasureTheory.Measure α} [inst : TopologicalSpace α]   [Secon
dCountableTopology α] [MeasureTh…
· 使用定理 `VitaliFamily.ae_tendsto_rnDeriv`：ae_tendsto_rnDeriv : forallᵐ x ∂μ, Tend
sto (fun a => ρ a / μ a) (v.filterAt x) (𝓝 (ρ.rnDeriv μ x))
· 使用定理 `MeasureTheory.IsFiniteMeasure.toIsLocallyFiniteMeasure`：∀ {α : Type u_1}
 {m0 : MeasurableSpace α} [inst : TopologicalSpace α] (μ : MeasureTheory.Measure
 α)   [MeasureTheory.IsFiniteMeasure μ], Mea…
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Filter.Tendsto.congr'`：∀ {α : Type u_1} {β : Type u_2} {f₁ f₂ : α → β} {
l₁ : Filter α} {l₂ : Filter β},   f₁ =ᶠ[l₁] f₂ → Filter.Tendsto f₁ l₁ l₂ → Filte
r.Tendsto f…
· 使用定理 `VitaliFamily.eventually_filterAt_measurableSet`：eventually_filterAt_meas
urableSet (x : X) : forallᶠ t in v.filterAt x, MeasurableSet t
· 使用定理 `MeasureTheory.withDensity_apply`：withDensity_apply (f : α -> Real>=0∞) {
s : Set α} (hs : MeasurableSet s) : μ.withDensity f s = ∫⁻ a in s, f a ∂μ

--- 原说明 ---
### Lebesgue differentiation theorem
-/
theorem ae_tendsto_lintegral_div' {f : α → ℝ≥0∞} (hf : Measurable f) (h'f : (∫⁻ y, f y ∂μ) ≠ ∞) :
    ∀ᵐ x ∂μ, Tendsto (fun a => (∫⁻ y in a, f y ∂μ) / μ a) (v.filterAt x) (𝓝 (f x)) := by
  let ρ := μ.withDensity f
  have : IsFiniteMeasure ρ := isFiniteMeasure_withDensity h'f
  filter_upwards [ae_tendsto_rnDeriv v ρ, rnDeriv_withDensity μ hf] with x hx h'x
  rw [← h'x]
  apply hx.congr' _
  filter_upwards [v.eventually_filterAt_measurableSet x] with a ha
  rw [← withDensity_apply f ha]
/-
**VitaliFamily.ae_tendsto_lintegral_div** 是 Mathlib 中的一个定理，位于命名空间 `VitaliFamily`
。
形式化陈述：ae_tendsto_lintegral_div {f : α -> Real>=0∞} (hf : AEMeasurable f μ) (h'f 
: (∫⁻ y, f y ∂μ) != ∞) : forallᵐ x ∂μ, Tendsto (fun a => (∫⁻ y in a, f y ∂μ) / μ
 a) (v.filterAt x) (𝓝 (f x))
参数：hf : AEMeasurable f μ；h'f : (∫⁻ y, f y ∂μ) != ∞。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.lintegral_congr_ae`：lintegral_congr_ae {f g : α -> Real>=0
∞} (h : f =ᵐ[μ] g) : ∫⁻ a, f a ∂μ = ∫⁻ a, g a ∂μ
· 使用定理 `Filter.EventuallyEq.symm`：∀ {α : Type u} {β : Type v} {f g : α → β} {l :
 Filter α}, f =ᶠ[l] g → g =ᶠ[l] f
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `AEMeasurable.ae_eq_mk`：ae_eq_mk (h : AEMeasurable f μ) : f =ᵐ[μ] h.mk f
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `VitaliFamily.ae_tendsto_lintegral_div'`：ae_tendsto_lintegral_div' {f : α
 -> Real>=0∞} (hf : Measurable f) (h'f : (∫⁻ y, f y ∂μ) != ∞) : forallᵐ x ∂μ, Te
ndsto (fun a => (∫⁻ y in a, …
· 使用定理 `AEMeasurable.measurable_mk`：measurable_mk (h : AEMeasurable f μ) : Measu
rable (h.mk f)
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `MeasureTheory.ae_restrict_of_ae`：ae_restrict_of_ae {s : Set α} {p : α ->
 Prop} (h : forallᵐ x ∂μ, p x) : forallᵐ x ∂μ.restrict s, p x
-/
theorem ae_tendsto_lintegral_div {f : α → ℝ≥0∞} (hf : AEMeasurable f μ) (h'f : (∫⁻ y, f y ∂μ) ≠ ∞) :
    ∀ᵐ x ∂μ, Tendsto (fun a => (∫⁻ y in a, f y ∂μ) / μ a) (v.filterAt x) (𝓝 (f x)) := by
  have A : (∫⁻ y, hf.mk f y ∂μ) ≠ ∞ := by
    convert! h'f using 1
    apply lintegral_congr_ae
    exact hf.ae_eq_mk.symm
  filter_upwards [v.ae_tendsto_lintegral_div' hf.measurable_mk A, hf.ae_eq_mk] with x hx h'x
  rw [h'x]
  convert! hx using 1
  ext1 a
  congr 1
  apply lintegral_congr_ae
  exact ae_restrict_of_ae hf.ae_eq_mk
/-
**VitaliFamily.ae_tendsto_lintegral_enorm_sub_div'_of_integrable** 是 Mathlib 中的一
个定理，位于命名空间 `VitaliFamily`。
形式化陈述：∀ {α : Type u_1} [inst : PseudoMetricSpace α] {m0 : MeasurableSpace α} {μ 
: MeasureTheory.Measure α}   (v : VitaliFamily μ) {E : Type u_2} [inst_1 : Norme
dAddCommGroup E] [SecondCountableTopology α] [BorelSpace α]   [MeasureTheory.IsL
ocallyFiniteMeasure μ] {f : α → E},   MeasureTheory.Integrable f μ →     Measure
Theory.StronglyMeasurable f →       ∀ᵐ (x : α) ∂μ, Filter.Tendsto (fun a => (∫⁻ 
(y : α) in a, ‖f y - f x‖ₑ ∂μ) / μ a) (v.filterAt x) (nhds 0)
参数：v : VitaliFamily μ；x : α；fun a => (∫⁻ (y : α) in a, ‖f y - f x‖ₑ ∂μ) / μ a；v.
filterAt x；nhds 0。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `MeasureTheory.StronglyMeasurable.isSeparable_range`：∀ {α : Type u_1} {β 
: Type u_2} {f : α → β} {m : MeasurableSpace α} [inst : TopologicalSpace β],   M
easureTheory.StronglyMeasurable f → Topo…
· 使用定理 `instCountableNat`：Countable ℕ
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `MeasureTheory.ae_ball_iff`：ae_ball_iff {ι : Type*} {S : Set ι} (hS : S.C
ountable) {p : α -> forall i in S, Prop} : (forallᵐ x ∂μ, forall i (hi : i in S)
, p x i hi) ↔ f…
· 使用定理 `VitaliFamily.ae_tendsto_lintegral_div'`：ae_tendsto_lintegral_div' {f : α
 -> Real>=0∞} (hf : Measurable f) (h'f : (∫⁻ y, f y ∂μ) != ∞) : forallᵐ x ∂μ, Te
ndsto (fun a => (∫⁻ y in a, …
· 使用定理 `MeasureTheory.StronglyMeasurable.enorm`：∀ {α : Type u_1} {x : Measurable
Space α} {ε : Type u_5} [inst : TopologicalSpace ε] [inst_1 : ContinuousENorm ε]
   {f : α → ε}, MeasureTheor…
· 使用定理 `MeasureTheory.StronglyMeasurable.sub`：∀ {α : Type u_1} {β : Type u_2} {f
 g : α → β} {mα : MeasurableSpace α} [inst : TopologicalSpace β] [inst_1 : Sub β
]   [ContinuousSub β],   M…
· 使用定理 `IsTopologicalAddGroup.to_continuousSub`：∀ {G : Type u} [inst : Topologic
alSpace G] [inst_1 : AddGroup G] [IsTopologicalAddGroup G], ContinuousSub G
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `MeasureTheory.StronglyMeasurable.indicator`：∀ {α : Type u_1} {β : Type u
_2} {f : α → β} {x : MeasurableSpace α} [inst : TopologicalSpace β] [inst_1 : Ze
ro β],   MeasureTheory.StronglyM…
· 使用定理 `MeasureTheory.stronglyMeasurable_const`：stronglyMeasurable_const {b : β}
 : StronglyMeasurable fun _ : α => b
· 使用定理 `IsOpen.measurableSet`：IsOpen.measurableSet (h : IsOpen s) : MeasurableSe
t s
· 使用定理 `BorelSpace.opensMeasurable`：∀ {α : Type u_6} [inst : TopologicalSpace α]
 [inst_1 : MeasurableSpace α] [BorelSpace α], OpensMeasurableSpace α
· 使用定理 `MeasureTheory.Measure.FiniteSpanningSetsIn.set_mem`：∀ {α : Type u_1} {m0
 : MeasurableSpace α} {μ : MeasureTheory.Measure α} {C : Set (Set α)}   (self : 
μ.FiniteSpanningSetsIn C) (i : ℕ), self.…
· 使用引理 `ne_of_lt`：ne_of_lt (h : a < b) : a != b
· 使用定理 `MeasureTheory.lintegral_mono`：lintegral_mono ⦃f g : α -> Real>=0∞⦄ (hfg 
: f <= g) : ∫⁻ a, f a ∂μ <= ∫⁻ a, g a ∂μ
· 使用定理 `enorm_sub_le`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] {a b : E}, 
‖a - b‖ₑ ≤ ‖a‖ₑ + ‖b‖ₑ
· 使用定理 `MeasureTheory.lintegral_add_left`：lintegral_add_left {f : α -> Real>=0∞}
 (hf : Measurable f) (g : α -> Real>=0∞) : ∫⁻ a, f a + g a ∂μ = ∫⁻ a, f a ∂μ + ∫
⁻ a, g a ∂μ
· 使用定理 `ENNReal.add_lt_add`：∀ {a b c d : ENNReal}, a < c → b < d → a + b < c + d
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `MeasureTheory.integrable_indicator_iff`：integrable_indicator_iff (hs : M
easurableSet s) : Integrable (indicator s f) μ ↔ IntegrableOn f s μ
· 使用定理 `MeasureTheory.integrableOn_const_iff`：integrableOn_const_iff {C : ε'} (h
C : ‖C‖ₑ != ∞
· 使用引理 `enorm_ne_top`：enorm_ne_top : ‖x‖ₑ != ∞
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `MeasureTheory.Measure.FiniteSpanningSetsIn.finite`：∀ {α : Type u_1} {m0 
: MeasurableSpace α} {μ : MeasureTheory.Measure α} {C : Set (Set α)}   (self : μ
.FiniteSpanningSetsIn C) (i : ℕ), μ (se…
· 使用定理 `or_true`：∀ (p : Prop), (p ∨ True) = True
（共 81 条，此处仅展示前 30 条）
-/
theorem ae_tendsto_lintegral_enorm_sub_div'_of_integrable {f : α → E} (hf : Integrable f μ)
    (h'f : StronglyMeasurable f) :
    ∀ᵐ x ∂μ, Tendsto (fun a => (∫⁻ y in a, ‖f y - f x‖ₑ ∂μ) / μ a) (v.filterAt x) (𝓝 0) := by
  /- For every `c`, then `(∫⁻ y in a, ‖f y - c‖ₑ ∂μ) / μ a` tends almost everywhere to `‖f x - c‖`.
    We apply this to a countable set of `c` which is dense in the range of `f`, to deduce the
    desired convergence.
    A minor technical inconvenience is that constants are not integrable, so to apply previous
    lemmas we need to replace `c` with the restriction of `c` to a finite measure set `A n` in the
    above sketch. -/
  let A := MeasureTheory.Measure.finiteSpanningSetsInOpen' μ
  rcases h'f.isSeparable_range with ⟨t, t_count, ht⟩
  have main :
    ∀ᵐ x ∂μ,
      ∀ᵉ (n : ℕ) (c ∈ t),
        Tendsto (fun a => (∫⁻ y in a, ‖f y - (A.set n).indicator (fun _ => c) y‖ₑ ∂μ) / μ a)
          (v.filterAt x) (𝓝 ‖f x - (A.set n).indicator (fun _ => c) x‖ₑ) := by
    simp_rw [ae_all_iff, ae_ball_iff t_count]
    intro n c _
    apply ae_tendsto_lintegral_div'
    · refine (h'f.sub ?_).enorm
      exact stronglyMeasurable_const.indicator (IsOpen.measurableSet (A.set_mem n))
    · apply ne_of_lt
      calc
        ∫⁻ y, ‖f y - (A.set n).indicator (fun _ : α => c) y‖ₑ ∂μ
          ≤ ∫⁻ y, ‖f y‖ₑ + ‖(A.set n).indicator (fun _ : α => c) y‖ₑ ∂μ :=
          lintegral_mono fun x ↦ enorm_sub_le
        _ = ∫⁻ y, ‖f y‖ₑ ∂μ + ∫⁻ y, ‖(A.set n).indicator (fun _ : α => c) y‖ₑ ∂μ :=
          lintegral_add_left h'f.enorm _
        _ < ∞ + ∞ :=
          haveI I : Integrable ((A.set n).indicator fun _ : α => c) μ := by
            simp only [integrable_indicator_iff (IsOpen.measurableSet (A.set_mem n)),
              integrableOn_const_iff (C := c), A.finite n, or_true]
          ENNReal.add_lt_add hf.2 I.2
  filter_upwards [main, v.ae_eventually_measure_pos] with x hx h'x
  have M c (hc : c ∈ t) :
      Tendsto (fun a => (∫⁻ y in a, ‖f y - c‖ₑ ∂μ) / μ a) (v.filterAt x) (𝓝 ‖f x - c‖ₑ) := by
    obtain ⟨n, xn⟩ : ∃ n, x ∈ A.set n := by simpa [← A.spanning] using mem_univ x
    specialize hx n c hc
    simp only [xn, indicator_of_mem] at hx
    apply hx.congr' _
    filter_upwards [v.eventually_filterAt_subset_of_nhds (IsOpen.mem_nhds (A.set_mem n) xn),
      v.eventually_filterAt_measurableSet x] with a ha h'a
    congr 1
    apply setLIntegral_congr_fun h'a (fun y hy ↦ ?_)
    simp only [ha hy, indicator_of_mem]
  apply ENNReal.tendsto_nhds_zero.2 fun ε εpos => ?_
  obtain ⟨c, ct, xc⟩ : ∃ c ∈ t, ‖f x - c‖ₑ < ε / 2 := by
    simp_rw [← edist_eq_enorm_sub]
    have : f x ∈ closure t := ht (mem_range_self _)
    exact EMetric.mem_closure_iff.1 this (ε / 2) (ENNReal.half_pos (ne_of_gt εpos))
  filter_upwards [(tendsto_order.1 (M c ct)).2 (ε / 2) xc, h'x, v.eventually_measure_lt_top x] with
    a ha h'a h''a
  apply ENNReal.div_le_of_le_mul
  calc
    (∫⁻ y in a, ‖f y - f x‖ₑ ∂μ) ≤ ∫⁻ y in a, ‖f y - c‖ₑ + ‖f x - c‖ₑ ∂μ := by
      apply lintegral_mono fun x => ?_
      simpa only [← edist_eq_enorm_sub] using edist_triangle_right _ _ _
    _ = (∫⁻ y in a, ‖f y - c‖ₑ ∂μ) + ∫⁻ _ in a, ‖f x - c‖ₑ ∂μ :=
      (lintegral_add_right _ measurable_const)
    _ ≤ ε / 2 * μ a + ε / 2 * μ a := by
      gcongr
      · rw [ENNReal.div_lt_iff (Or.inl h'a.ne') (Or.inl h''a.ne)] at ha
        exact ha.le
      · simp only [lintegral_const, Measure.restrict_apply, MeasurableSet.univ, univ_inter]
        gcongr
    _ = ε * μ a := by rw [← add_mul, ENNReal.add_halves]
/-
**VitaliFamily.ae_tendsto_lintegral_enorm_sub_div_of_integrable** 是 Mathlib 中的一个
定理，位于命名空间 `VitaliFamily`。
形式化陈述：ae_tendsto_lintegral_enorm_sub_div_of_integrable {f : α -> E} (hf : Integr
able f μ) : forallᵐ x ∂μ, Tendsto (fun a => (∫⁻ y in a, ‖f y - f x‖ₑ ∂μ) / μ a) 
(v.filterAt x) (𝓝 0)
参数：hf : Integrable f μ。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `MeasureTheory.Integrable.congr`：∀ {α : Type u_1} {ε : Type u_5} {m : Mea
surableSpace α} {μ : MeasureTheory.Measure α} [inst : TopologicalSpace ε]   [ins
t_1 : ContinuousENor…
· 使用定理 `MeasureTheory.AEStronglyMeasurable.ae_eq_mk`：ae_eq_mk (hf : AEStronglyMe
asurable[m] f μ) : f =ᵐ[μ] hf.mk f
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `VitaliFamily.ae_tendsto_lintegral_enorm_sub_div'_of_integrable`：∀ {α : T
ype u_1} [inst : PseudoMetricSpace α] {m0 : MeasurableSpace α} {μ : MeasureTheor
y.Measure α}   (v : VitaliFamily μ) {E : Type u_2} […
· 使用引理 `MeasureTheory.AEStronglyMeasurable.stronglyMeasurable_mk`：stronglyMeasur
able_mk (hf : AEStronglyMeasurable[m] f μ) : StronglyMeasurable[m] (hf.mk f)
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `Filter.Tendsto.congr`：∀ {α : Type u_1} {β : Type u_2} {f₁ f₂ : α → β} {l
₁ : Filter α} {l₂ : Filter β},   (∀ (x : α), f₁ x = f₂ x) → Filter.Tendsto f₁ l₁
 l₂ → Filt…
· 使用定理 `MeasureTheory.lintegral_congr_ae`：lintegral_congr_ae {f g : α -> Real>=0
∞} (h : f =ᵐ[μ] g) : ∫⁻ a, f a ∂μ = ∫⁻ a, g a ∂μ
· 使用定理 `MeasureTheory.ae_restrict_of_ae`：ae_restrict_of_ae {s : Set α} {p : α ->
 Prop} (h : forallᵐ x ∂μ, p x) : forallᵐ x ∂μ.restrict s, p x
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
-/
theorem ae_tendsto_lintegral_enorm_sub_div_of_integrable {f : α → E} (hf : Integrable f μ) :
    ∀ᵐ x ∂μ, Tendsto (fun a => (∫⁻ y in a, ‖f y - f x‖ₑ ∂μ) / μ a) (v.filterAt x) (𝓝 0) := by
  have I : Integrable (hf.1.mk f) μ := hf.congr hf.1.ae_eq_mk
  filter_upwards [v.ae_tendsto_lintegral_enorm_sub_div'_of_integrable I hf.1.stronglyMeasurable_mk,
    hf.1.ae_eq_mk] with x hx h'x
  apply hx.congr _
  intro a
  congr 1
  apply lintegral_congr_ae
  apply ae_restrict_of_ae
  filter_upwards [hf.1.ae_eq_mk] with y hy
  rw [hy, h'x]
/-
**VitaliFamily.ae_tendsto_lintegral_enorm_sub_div** 是 Mathlib 中的一个定理，位于命名空间 `Vit
aliFamily`。
形式化陈述：ae_tendsto_lintegral_enorm_sub_div {f : α -> E} (hf : LocallyIntegrable f 
μ) : forallᵐ x ∂μ, Tendsto (fun a => (∫⁻ y in a, ‖f y - f x‖ₑ ∂μ) / μ a) (v.filt
erAt x) (𝓝 0)
参数：hf : LocallyIntegrable f μ。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `MeasureTheory.LocallyIntegrable.exists_nat_integrableOn`：∀ {X : Type u_1
} {ε : Type u_3} [inst : MeasurableSpace X] [inst_1 : TopologicalSpace X] [inst_
2 : TopologicalSpace ε]   [inst_3 : Continuou…
· 使用定理 `VitaliFamily.ae_tendsto_lintegral_enorm_sub_div_of_integrable`：ae_tendst
o_lintegral_enorm_sub_div_of_integrable {f : α -> E} (hf : Integrable f μ) : for
allᵐ x ∂μ, Tendsto (fun a => (∫⁻ y in a, ‖f y - f x…
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `MeasureTheory.integrable_indicator_iff`：integrable_indicator_iff (hs : M
easurableSet s) : Integrable (indicator s f) μ ↔ IntegrableOn f s μ
· 使用定理 `IsOpen.measurableSet`：IsOpen.measurableSet (h : IsOpen s) : MeasurableSe
t s
· 使用定理 `BorelSpace.opensMeasurable`：∀ {α : Type u_6} [inst : TopologicalSpace α]
 [inst_1 : MeasurableSpace α] [BorelSpace α], OpensMeasurableSpace α
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `MeasureTheory.ae_all_iff`：ae_all_iff {ι : Sort*} [Countable ι] {p : α ->
 ι -> Prop} : (forallᵐ a ∂μ, forall i, p a i) ↔ forall i, forallᵐ a ∂μ, p a i
· 使用定理 `instCountableNat`：Countable ℕ
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.mem_univ`：mem_univ (x : α) : x in @univ α
· 使用定理 `Filter.Tendsto.congr'`：∀ {α : Type u_1} {β : Type u_2} {f₁ f₂ : α → β} {
l₁ : Filter α} {l₂ : Filter β},   f₁ =ᶠ[l₁] f₂ → Filter.Tendsto f₁ l₁ l₂ → Filte
r.Tendsto f…
· 使用定理 `VitaliFamily.eventually_filterAt_measurableSet`：eventually_filterAt_meas
urableSet (x : X) : forallᶠ t in v.filterAt x, MeasurableSet t
· 使用定理 `VitaliFamily.eventually_filterAt_subset_of_nhds`：eventually_filterAt_sub
set_of_nhds {x : X} {o : Set X} (hx : o in 𝓝 x) : forallᶠ t in v.filterAt x, t s
ubseteq o
· 使用定理 `IsOpen.mem_nhds`：IsOpen.mem_nhds (hs : IsOpen s) (hx : x in s) : s in 𝓝 
x
· 使用定理 `MeasureTheory.setLIntegral_congr_fun`：setLIntegral_congr_fun {f g : α ->
 Real>=0∞} {s : Set α} (hs : MeasurableSet s) (hfg : EqOn f g s) : ∫⁻ x in s, f 
x ∂μ = ∫⁻ x in s, g x ∂μ
· 使用定理 `Set.indicator_of_mem`：∀ {α : Type u_1} {M : Type u_3} [inst : Zero M] {s
 : Set α} {a : α}, a ∈ s → ∀ (f : α → M), s.indicator f a = f a
-/
theorem ae_tendsto_lintegral_enorm_sub_div {f : α → E} (hf : LocallyIntegrable f μ) :
    ∀ᵐ x ∂μ, Tendsto (fun a => (∫⁻ y in a, ‖f y - f x‖ₑ ∂μ) / μ a) (v.filterAt x) (𝓝 0) := by
  rcases hf.exists_nat_integrableOn with ⟨u, u_open, u_univ, hu⟩
  have : ∀ n, ∀ᵐ x ∂μ,
      Tendsto (fun a => (∫⁻ y in a, ‖(u n).indicator f y - (u n).indicator f x‖ₑ ∂μ) / μ a)
      (v.filterAt x) (𝓝 0) := by
    intro n
    apply ae_tendsto_lintegral_enorm_sub_div_of_integrable
    exact (integrable_indicator_iff (u_open n).measurableSet).2 (hu n)
  filter_upwards [ae_all_iff.2 this] with x hx
  obtain ⟨n, hn⟩ : ∃ n, x ∈ u n := by simpa only [← u_univ, mem_iUnion] using mem_univ x
  apply Tendsto.congr' _ (hx n)
  filter_upwards [v.eventually_filterAt_subset_of_nhds ((u_open n).mem_nhds hn),
    v.eventually_filterAt_measurableSet x] with a ha h'a
  congr 1
  refine setLIntegral_congr_fun h'a (fun y hy ↦ ?_)
  rw [indicator_of_mem (ha hy) f, indicator_of_mem hn f]

/-- *Lebesgue differentiation theorem*: for almost every point `x`, the
average of `‖f y - f x‖` on `a` tends to `0` as `a` shrinks to `x` along a Vitali family. -/
/-
**VitaliFamily.ae_tendsto_average_norm_sub** 是 Mathlib 中的一个定理，位于命名空间 `VitaliFami
ly`。
形式化陈述：ae_tendsto_average_norm_sub {f : α -> E} (hf : LocallyIntegrable f μ) : fo
rallᵐ x ∂μ, Tendsto (fun a => ⨍ y in a, ‖f y - f x‖ ∂μ) (v.filterAt x) (𝓝 0)
参数：hf : LocallyIntegrable f μ。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `VitaliFamily.ae_tendsto_lintegral_enorm_sub_div`：ae_tendsto_lintegral_en
orm_sub_div {f : α -> E} (hf : LocallyIntegrable f μ) : forallᵐ x ∂μ, Tendsto (f
un a => (∫⁻ y in a, ‖f y - f x‖ₑ ∂μ) …
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `Filter.Tendsto.comp`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {f :
 α → β} {g : β → γ} {x : Filter α} {y : Filter β} {z : Filter γ},   Filter.Tends
to g y z …
· 使用定理 `ENNReal.tendsto_toReal`：tendsto_toReal {a : Real>=0∞} (ha : a != ∞) : Te
ndsto ENNReal.toReal (𝓝 a) (𝓝 a.toReal)
· 使用定理 `ENNReal.zero_ne_top`：0 ≠ ⊤
· 使用定理 `Filter.Tendsto.congr'`：∀ {α : Type u_1} {β : Type u_2} {f₁ f₂ : α → β} {
l₁ : Filter α} {l₂ : Filter β},   f₁ =ᶠ[l₁] f₂ → Filter.Tendsto f₁ l₁ l₂ → Filte
r.Tendsto f…
· 使用定理 `VitaliFamily.eventually_filterAt_integrableOn`：eventually_filterAt_integ
rableOn (x : α) {f : α -> E} (hf : LocallyIntegrable f μ) : forallᶠ a in v.filte
rAt x, IntegrableOn f a μ
· 使用定理 `VitaliFamily.eventually_measure_lt_top`：eventually_measure_lt_top [IsLoc
allyFiniteMeasure μ] (x : α) : forallᶠ a in v.filterAt x, μ a < ∞
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `ENNReal.toReal_div`：∀ (a b : ENNReal), (a / b).toReal = a.toReal / b.toR
eal
· 使用定理 `div_eq_inv_mul`：div_eq_inv_mul : a / b = b⁻¹ * a
· 使用定理 `MeasureTheory.setAverage_eq`：setAverage_eq (f : α -> E) (s : Set α) : ⨍ 
x in s, f x ∂μ = (μ.real s)⁻¹ • ∫ x in s, f x ∂μ
· 使用定理 `MeasureTheory.Integrable.norm`：∀ {α : Type u_1} {β : Type u_2} {m : Meas
urableSpace α} {μ : MeasureTheory.Measure α} [inst : NormedAddCommGroup β]   {f 
: α → β}, MeasureTh…
· 使用定理 `MeasureTheory.IntegrableOn.sub`：∀ {α : Type u_1} {E : Type u_5} {mα : Me
asurableSpace α} [inst : NormedAddCommGroup E] {s : Set α}   {μ : MeasureTheory.
Measure α} {f g : α …
· 使用定理 `MeasureTheory.integrableOn_const`：integrableOn_const {C : ε'} (hs : μ s 
!= ∞
· 使用定理 `LT.lt.ne`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≠ b
· 使用引理 `enorm_ne_top`：enorm_ne_top : ‖x‖ₑ != ∞
· 使用定理 `MeasureTheory.lintegral_coe_eq_integral`：lintegral_coe_eq_integral (f : 
α -> Real>=0) (hfi : Integrable (fun x => (f x : Real)) μ) : ∫⁻ a, f a ∂μ = ENNR
eal.ofReal (∫ a, f a ∂μ)
· 使用定理 `ENNReal.toReal_ofReal`：toReal_ofReal {r : Real} (h : 0 <= r) : (ENNReal.
ofReal r).toReal = r
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
· 使用定理 `NNReal.coe_nonneg`：∀ (r : NNReal), 0 ≤ ↑r
（共 32 条，此处仅展示前 30 条）

--- 原说明 ---
*Lebesgue differentiation theorem*: for almost every point `x`, the
average of `‖f y - f x‖` on `a` tends to `0` as `a` shrinks to `x` along a Vital
i family.
-/
theorem ae_tendsto_average_norm_sub {f : α → E} (hf : LocallyIntegrable f μ) :
    ∀ᵐ x ∂μ, Tendsto (fun a => ⨍ y in a, ‖f y - f x‖ ∂μ) (v.filterAt x) (𝓝 0) := by
  filter_upwards [v.ae_tendsto_lintegral_enorm_sub_div hf] with x hx
  have := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp hx
  simp only [ENNReal.toReal_zero] at this
  apply Tendsto.congr' _ this
  filter_upwards [v.eventually_measure_lt_top x, v.eventually_filterAt_integrableOn x hf]
    with a h'a h''a
  simp only [Function.comp_apply, ENNReal.toReal_div, setAverage_eq, div_eq_inv_mul]
  have A : IntegrableOn (fun y => (‖f y - f x‖₊ : ℝ)) a μ := by
    simp_rw [coe_nnnorm]
    exact (h''a.sub (integrableOn_const h'a.ne)).norm
  dsimp [enorm]
  rw [lintegral_coe_eq_integral _ A, ENNReal.toReal_ofReal (by positivity)]
  simp only [coe_nnnorm, measureReal_def]

/-- *Lebesgue differentiation theorem*: for almost every point `x`, the
average of `f` on `a` tends to `f x` as `a` shrinks to `x` along a Vitali family. -/
/-
**VitaliFamily.ae_tendsto_average** 是 Mathlib 中的一个定理，位于命名空间 `VitaliFamily`。
形式化陈述：ae_tendsto_average [NormedSpace Real E] [CompleteSpace E] {f : α -> E} (hf
 : LocallyIntegrable f μ) : forallᵐ x ∂μ, Tendsto (fun a => ⨍ y in a, f y ∂μ) (v
.filterAt x) (𝓝 (f x))
参数：hf : LocallyIntegrable f μ。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `VitaliFamily.ae_eventually_measure_pos`：ae_eventually_measure_pos [Secon
dCountableTopology α] : forallᵐ x ∂μ, forallᶠ a in v.filterAt x, 0 < μ a
· 使用定理 `VitaliFamily.ae_tendsto_average_norm_sub`：ae_tendsto_average_norm_sub {f
 : α -> E} (hf : LocallyIntegrable f μ) : forallᵐ x ∂μ, Tendsto (fun a => ⨍ y in
 a, ‖f y - f x‖ ∂μ) (v.filterA…
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `tendsto_iff_norm_sub_tendsto_zero`：∀ {α : Type u_1} {E : Type u_4} [inst
 : SeminormedAddCommGroup E] {f : α → E} {a : Filter α} {b : E},   Filter.Tendst
o f a (nhds b) ↔ Filter…
· 使用引理 `squeeze_zero'`：squeeze_zero' {α} {f g : α -> Real} {t₀ : Filter α} (hf :
 forallᶠ t in t₀, 0 <= f t) (hft : forallᶠ t in t₀, f t <= g t) (g0 : Tendsto g 
t₀ …
· 使用定理 `Filter.Eventually.of_forall`：∀ {α : Type u} {p : α → Prop} {f : Filter α
}, (∀ (x : α), p x) → ∀ᶠ (x : α) in f, p x
· 使用定理 `norm_nonneg`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (a : E), 0 ≤
 ‖a‖
· 使用定理 `VitaliFamily.eventually_filterAt_integrableOn`：eventually_filterAt_integ
rableOn (x : α) {f : α -> E} (hf : LocallyIntegrable f μ) : forallᶠ a in v.filte
rAt x, IntegrableOn f a μ
· 使用定理 `VitaliFamily.eventually_measure_lt_top`：eventually_measure_lt_top [IsLoc
allyFiniteMeasure μ] (x : α) : forallᶠ a in v.filterAt x, μ a < ∞
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.setAverage_const`：setAverage_const {s : Set α} (hs₀ : μ s 
!= 0) (hs : μ s != ∞) (c : E) : ⨍ _ in s, c ∂μ = c
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `LT.lt.ne`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≠ b
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `MeasureTheory.setAverage_eq'`：setAverage_eq' (f : α -> E) (s : Set α) : 
⨍ x in s, f x ∂μ = ∫ x, f x ∂(μ s)⁻¹ • μ.restrict s
· 使用定理 `MeasureTheory.integral_sub`：integral_sub {f g : α -> G} (hf : Integrable
 f μ) (hg : Integrable g μ) : ∫ a, f a - g a ∂μ = ∫ a, f a ∂μ - ∫ a, g a ∂μ
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `MeasureTheory.integrable_inv_smul_measure`：integrable_inv_smul_measure {
f : α -> ε} {c : Real>=0∞} (h₁ : c != 0) (h₂ : c != ∞) : Integrable f (c⁻¹ • μ) 
↔ Integrable f μ
· 使用定理 `MeasureTheory.integrableOn_const`：integrableOn_const {C : ε'} (hs : μ s 
!= ∞
· 使用引理 `enorm_ne_top`：enorm_ne_top : ‖x‖ₑ != ∞
· 使用定理 `MeasureTheory.norm_integral_le_integral_norm`：norm_integral_le_integral_
norm (f : α -> G) : ‖∫ a, f a ∂μ‖ <= ∫ a, ‖f a‖ ∂μ

--- 原说明 ---
*Lebesgue differentiation theorem*: for almost every point `x`, the
average of `f` on `a` tends to `f x` as `a` shrinks to `x` along a Vitali family
.
-/
theorem ae_tendsto_average [NormedSpace ℝ E] [CompleteSpace E] {f : α → E}
    (hf : LocallyIntegrable f μ) :
    ∀ᵐ x ∂μ, Tendsto (fun a => ⨍ y in a, f y ∂μ) (v.filterAt x) (𝓝 (f x)) := by
  filter_upwards [v.ae_tendsto_average_norm_sub hf, v.ae_eventually_measure_pos] with x hx h'x
  rw [tendsto_iff_norm_sub_tendsto_zero]
  refine squeeze_zero' (Eventually.of_forall fun a => norm_nonneg _) ?_ hx
  filter_upwards [h'x, v.eventually_measure_lt_top x, v.eventually_filterAt_integrableOn x hf]
    with a ha h'a h''a
  nth_rw 1 [← setAverage_const ha.ne' h'a.ne (f x)]
  simp_rw [setAverage_eq']
  rw [← integral_sub]
  · exact norm_integral_le_integral_norm _
  · exact (integrable_inv_smul_measure ha.ne' h'a.ne).2 h''a
  · exact (integrable_inv_smul_measure ha.ne' h'a.ne).2 (integrableOn_const h'a.ne)

end

end VitaliFamily

