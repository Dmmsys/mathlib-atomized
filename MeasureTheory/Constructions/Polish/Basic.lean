/-
Copyright (c) 2022 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel, Felix Weilacher
-/
module

public import Mathlib.MeasureTheory.Constructions.BorelSpace.Metrizable
public import Mathlib.Tactic.CrossRefAttribute
public import Mathlib.Topology.MetricSpace.Perfect
public import Mathlib.Topology.Separation.CountableSeparatingOn

/-!
# The Borel sigma-algebra on Polish spaces

We discuss several results pertaining to the relationship between the topology and the Borel
structure on Polish spaces.

## Main definitions and results

First, we define standard Borel spaces.

* A `StandardBorelSpace α` is a typeclass for measurable spaces which arise as the Borel sets
  of some Polish topology.

Next, we define the class of analytic sets and establish its basic properties.

* `MeasureTheory.AnalyticSet s`: a set in a topological space is analytic if it is the continuous
  image of a Polish space. Equivalently, it is empty, or the image of `ℕ → ℕ`.
* `MeasureTheory.AnalyticSet.image_of_continuous`: a continuous image of an analytic set is
  analytic.
* `MeasurableSet.analyticSet`: in a Polish space, any Borel-measurable set is analytic.

Then, we show Lusin's theorem that two disjoint analytic sets can be separated by Borel sets.

* `MeasurablySeparable s t` states that there exists a measurable set containing `s` and disjoint
  from `t`.
* `AnalyticSet.measurablySeparable` shows that two disjoint analytic sets are separated by a
  Borel set.

We then prove the Lusin-Souslin theorem that a continuous injective image of a Borel subset of
a Polish space is Borel. The proof of this nontrivial result relies on the above results on
analytic sets.

* `MeasurableSet.image_of_continuousOn_injOn` asserts that, if `s` is a Borel measurable set in
  a Polish space, then the image of `s` under a continuous injective map is still Borel measurable.
* `Continuous.measurableEmbedding` states that a continuous injective map on a Polish space
  is a measurable embedding for the Borel sigma-algebra.
* `ContinuousOn.measurableEmbedding` is the same result for a map restricted to a measurable set
  on which it is continuous.
* `Measurable.measurableEmbedding` states that a measurable injective map from
  a standard Borel space to a second-countable topological space is a measurable embedding.
* `isClopenable_iff_measurableSet`: in a Polish space, a set is clopenable (i.e., it can be made
  open and closed by using a finer Polish topology) if and only if it is Borel-measurable.

We use this to prove several versions of the Borel isomorphism theorem.

* `PolishSpace.measurableEquivOfNotCountable` : Any two uncountable standard Borel spaces
  are Borel isomorphic.
* `PolishSpace.Equiv.measurableEquiv` : Any two standard Borel spaces of the same cardinality
  are Borel isomorphic.
-/

@[expose] public section


open Set Function PolishSpace PiNat TopologicalSpace Bornology Metric Filter Topology MeasureTheory

/-! ### Standard Borel Spaces -/

variable (α : Type*)

/-- A standard Borel space is a measurable space arising as the Borel sets of some Polish topology.
This is useful in situations where a space has no natural topology or
the natural topology in a space is non-Polish.

To endow a standard Borel space `α` with a compatible Polish topology, use
`letI := upgradeStandardBorel α`. One can then use `eq_borel_upgradeStandardBorel α` to
rewrite the `MeasurableSpace α` instance to `borel α t`, where `t` is the new topology. -/
@[wikidata Q25378068]
/--
Definition of `StandardBorelSpace` / `StandardBorelSpace` 的定义

English:
class StandardBorelSpace
  parameters: [MeasurableSpace α]
  axioms and operations (1):
    - polish : exists _ : TopologicalSpace α, BorelSpace α ∧ PolishSpace α

中文:
类 StandardBorelSpace
  参数: [MeasurableSpace α]
  公理与运算 (1 个):
    - polish : 存在 _ : TopologicalSpace α, BorelSpace α ∧ PolishSpace α

Depends on / 依赖: upgradeStandardBorel
-/
class StandardBorelSpace [MeasurableSpace α] : Prop where
  /-- There exists a compatible Polish topology. -/
  polish : exists _ : TopologicalSpace α, BorelSpace α ∧ PolishSpace α

/--
Definition of `UpgradedStandardBorel` / `UpgradedStandardBorel` 的定义

English:
class UpgradedStandardBorel
  parameters: extends MeasurableSpace α, TopologicalSpace α,
  extends: MeasurableSpace α, TopologicalSpace α, 
  (no additional axioms)

中文:
类 UpgradedStandardBorel
  参数: extends MeasurableSpace α, TopologicalSpace α,
  继承: MeasurableSpace α, TopologicalSpace α, 
  (无附加公理)

Depends on / 依赖: standard, upgradeStandardBorel
-/
class UpgradedStandardBorel extends MeasurableSpace α, TopologicalSpace α,
  BorelSpace α, PolishSpace α

/-- Use as `letI := upgradeStandardBorel α` to endow a standard Borel space `α` with
a compatible Polish topology.

Warning: following this with `borelize α` will cause an error. Instead, one can
rewrite with `eq_borel_upgradeStandardBorel α`.
TODO: fix the corresponding bug in `borelize`. -/
@[instance_reducible]
noncomputable
/--
Definition of `upgradeStandardBorel` / `upgradeStandardBorel` 的定义

English:
definition upgradeStandardBorel
  signature: [MeasurableSpace α] [h : StandardBorelSpace α]
  body: by
  choose τ hb hp using h.polish
  constructor

中文:
定义 upgradeStandardBorel
  签名: [MeasurableSpace α] [h : StandardBorelSpace α]
  定义体: by
  choose τ hb hp using h.polish
  constructor

Depends on / 依赖: h.polish, polish
-/
def upgradeStandardBorel [MeasurableSpace α] [h : StandardBorelSpace α] :
    UpgradedStandardBorel α := by
  choose τ hb hp using h.polish
  constructor

/--
theorem `eq_borel_upgradeStandardBorel` / 定理 `eq_borel_upgradeStandardBorel`

English:
theorem eq_borel_upgradeStandardBorel
  given: [MeasurableSpace α] [StandardBorelSpace α]
  proof: @BorelSpace.measurable_eq _ (upgradeStandardBorel α).toTopologicalSpace _
    (upgradeStandardBorel α).toBorelSpace

中文:
定理 eq_borel_upgradeStandardBorel
  条件: [MeasurableSpace α] [StandardBorelSpace α]
  证明: @BorelSpace.measurable_eq _ (upgradeStandardBorel α).toTopologicalSpace _
    (upgradeStandardBorel α).toBorelSpace

Depends on / 依赖: BorelSpace, BorelSpace.measurable_eq, measurable_eq, toBorelSpace, toTopologicalSpace, upgradeStandardBorel
-/
theorem eq_borel_upgradeStandardBorel [MeasurableSpace α] [StandardBorelSpace α] :
    ‹MeasurableSpace α› = @borel _ (upgradeStandardBorel α).toTopologicalSpace :=
  @BorelSpace.measurable_eq _ (upgradeStandardBorel α).toTopologicalSpace _
    (upgradeStandardBorel α).toBorelSpace

variable {α}

section

variable [MeasurableSpace α]

-- See note [lower instance priority]
instance (priority := 100) standardBorel_of_polish [τ : TopologicalSpace α]
    [BorelSpace α] [PolishSpace α] : StandardBorelSpace α := by exists τ

-- See note [lower instance priority]
instance (priority := 100) standardBorelSpace_of_discreteMeasurableSpace [DiscreteMeasurableSpace α]
    [Countable α] : StandardBorelSpace α :=
  let _ : TopologicalSpace α := ⊥
  have : DiscreteTopology α := ⟨rfl⟩
  inferInstance

-- See note [lower instance priority]
instance (priority := 100) countablyGenerated_of_standardBorel [StandardBorelSpace α] :
    MeasurableSpace.CountablyGenerated α :=
  letI := upgradeStandardBorel α
  inferInstance

-- See note [lower instance priority]
instance (priority := 100) measurableSingleton_of_standardBorel [StandardBorelSpace α] :
    MeasurableSingletonClass α :=
  letI := upgradeStandardBorel α
  inferInstance

namespace StandardBorelSpace

variable {β : Type*} [MeasurableSpace β]

section instances

/--
Instance `prod` / 实例 `prod`

English:
instance prod
  signature: [StandardBorelSpace α] [StandardBorelSpace β]
  body: letI := upgradeStandardBorel α
  letI := upgradeStandardBorel β
  inferInstance

中文:
实例 prod
  签名: [StandardBorelSpace α] [StandardBorelSpace β]
  定义体: letI := upgradeStandardBorel α
  letI := upgradeStandardBorel β
  inferInstance

Depends on / 依赖: upgradeStandardBorel
-/
instance prod [StandardBorelSpace α] [StandardBorelSpace β] : StandardBorelSpace (α × β) :=
  letI := upgradeStandardBorel α
  letI := upgradeStandardBorel β
  inferInstance

/--
Instance `pi_countable` / 实例 `pi_countable`

English:
instance pi_countable
  signature: {ι : Type*} [Countable ι] {α : ι -> Type*} [forall n, MeasurableSpace (α n)]
  body: letI := fun n => upgradeStandardBorel (α n)
  inferInstance

中文:
实例 pi_countable
  签名: {ι : 类型} [Countable ι] {α : ι -> 类型} [对任意 n, MeasurableSpace (α n)]
  定义体: letI := fun n => upgradeStandardBorel (α n)
  inferInstance

Depends on / 依赖: upgradeStandardBorel
-/
instance pi_countable {ι : Type*} [Countable ι] {α : ι -> Type*} [forall n, MeasurableSpace (α n)]
    [forall n, StandardBorelSpace (α n)] : StandardBorelSpace (forall n, α n) :=
  letI := fun n => upgradeStandardBorel (α n)
  inferInstance

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [StandardBorelSpace
  signature: α] : MeasurableEq α
  body: by
  let := upgradeStandardBorel α
  infer_instance

中文:
实例 [StandardBorelSpace
  签名: α] : MeasurableEq α
  定义体: by
  let := upgradeStandardBorel α
  infer_instance

Depends on / 依赖: infer_instance, upgradeStandardBorel
-/
instance [StandardBorelSpace α] : MeasurableEq α := by
  let := upgradeStandardBorel α
  infer_instance

end instances

end StandardBorelSpace

end

variable {ι : Type*}

namespace MeasureTheory

variable [TopologicalSpace α]

/-! ### Analytic sets -/

/-- An analytic set is a set which is the continuous image of some Polish space. There are several
equivalent characterizations of this definition. For the definition, we pick one that avoids
universe issues: a set is analytic if and only if it is a continuous image of `ℕ → ℕ` (or if it
is empty). The above more usual characterization is given
in `analyticSet_iff_exists_polishSpace_range`.

Warning: these are analytic sets in the context of descriptive set theory (which is why they are
registered in the namespace `MeasureTheory`). They have nothing to do with analytic sets in the
context of complex analysis. -/
irreducible_def AnalyticSet (s : Set α) : Prop :=
  s = ∅ ∨ exists f : (Nat -> Nat) -> α, Continuous f ∧ range f = s

/--
theorem `analyticSet_empty` / 定理 `analyticSet_empty`

English:
theorem analyticSet_empty
  statement: AnalyticSet (∅ : Set α)
  proof: by
  rw [AnalyticSet]
  exact Or.inl rfl

中文:
定理 analyticSet_empty
  结论: AnalyticSet (∅ : Set α)
  证明: by
  rw [AnalyticSet]
  exact Or.inl rfl

Depends on / 依赖: AnalyticSet, Or.inl
-/
theorem analyticSet_empty : AnalyticSet (∅ : Set α) := by
  rw [AnalyticSet]
  exact Or.inl rfl

/--
theorem `analyticSet_range_of_polishSpace` / 定理 `analyticSet_range_of_polishSpace`

English:
theorem analyticSet_range_of_polishSpace
  statement: {β : Type*} [TopologicalSpace β] [PolishSpace β]
  proof: by
  cases isEmpty_or_nonempty β
  · rw [range_eq_empty]
    exact analyticSet_empty
  · rw [AnalyticSet]
    obtain ⟨g, g_cont, hg⟩ : exists g : (Nat -> Nat) -> β, Continuous g ∧ Surjective g :=
      exists_nat_nat_continuous_surjective β
    refine Or.inr ⟨f ∘ g, f_cont.comp g_cont, ?_⟩
    rw [h

中文:
定理 analyticSet_range_of_polishSpace
  结论: {β : 类型} [TopologicalSpace β] [PolishSpace β]
  证明: by
  cases isEmpty_or_nonempty β
  · rw [range_eq_empty]
    exact analyticSet_empty
  · rw [AnalyticSet]
    obtain ⟨g, g_cont, hg⟩ : exists g : (Nat -> Nat) -> β, Continuous g ∧ Surjective g :=
      exists_nat_nat_continuous_surjective β
    refine Or.inr ⟨f ∘ g, f_cont.comp g_cont, ?_⟩
    rw [h

Depends on / 依赖: AnalyticSet, Continuous, Or.inr, Surjective, analyticSet_empty, exists_nat_nat_continuous_surjective, f_cont, f_cont.comp, g_cont, hg.range_comp, isEmpty_or_nonempty, range_comp, range_eq_empty
-/
theorem analyticSet_range_of_polishSpace {β : Type*} [TopologicalSpace β] [PolishSpace β]
    {f : β -> α} (f_cont : Continuous f) : AnalyticSet (range f) := by
  cases isEmpty_or_nonempty β
  · rw [range_eq_empty]
    exact analyticSet_empty
  · rw [AnalyticSet]
    obtain ⟨g, g_cont, hg⟩ : exists g : (Nat -> Nat) -> β, Continuous g ∧ Surjective g :=
      exists_nat_nat_continuous_surjective β
    refine Or.inr ⟨f ∘ g, f_cont.comp g_cont, ?_⟩
    rw [hg.range_comp]

/--
theorem `_root_.IsOpen.analyticSet_image` / 定理 `_root_.IsOpen.analyticSet_image`

English:
theorem _root_.IsOpen.analyticSet_image
  statement: {β : Type*} [TopologicalSpace β] [PolishSpace β]
  proof: by
  rw [image_eq_range]
  have : PolishSpace s := hs.polishSpace
  exact analyticSet_range_of_polishSpace (f_cont.comp continuous_subtype_val)

中文:
定理 _root_.IsOpen.analyticSet_image
  结论: {β : 类型} [TopologicalSpace β] [PolishSpace β]
  证明: by
  rw [image_eq_range]
  have : PolishSpace s := hs.polishSpace
  exact analyticSet_range_of_polishSpace (f_cont.comp continuous_subtype_val)

Depends on / 依赖: PolishSpace, analyticSet_range_of_polishSpace, continuous_subtype_val, f_cont, f_cont.comp, hs.polishSpace, image_eq_range, polishSpace
-/
theorem _root_.IsOpen.analyticSet_image {β : Type*} [TopologicalSpace β] [PolishSpace β]
    {s : Set β} (hs : IsOpen s) {f : β -> α} (f_cont : Continuous f) : AnalyticSet (f '' s) := by
  rw [image_eq_range]
  have : PolishSpace s := hs.polishSpace
  exact analyticSet_range_of_polishSpace (f_cont.comp continuous_subtype_val)

/--
theorem `analyticSet_iff_exists_polishSpace_range` / 定理 `analyticSet_iff_exists_polishSpace_range`

English:
theorem analyticSet_iff_exists_polishSpace_range
  given: {s : Set α}
  proof: by
  constructor
  · intro h
    rw [AnalyticSet] at h
    rcases h with h | h
    · refine ⟨Empty, inferInstance, inferInstance, Empty.elim, continuous_bot, ?_⟩
      rw [h]
      exact range_eq_empty _
    · exact ⟨Nat -> Nat, inferInstance, inferInstance, h⟩
  · rintro ⟨β, h, h', f, f_cont, f_ran

中文:
定理 analyticSet_iff_exists_polishSpace_range
  条件: {s : Set α}
  证明: by
  constructor
  · intro h
    rw [AnalyticSet] at h
    rcases h with h | h
    · refine ⟨Empty, inferInstance, inferInstance, Empty.elim, continuous_bot, ?_⟩
      rw [h]
      exact range_eq_empty _
    · exact ⟨Nat -> Nat, inferInstance, inferInstance, h⟩
  · rintro ⟨β, h, h', f, f_cont, f_ran

Depends on / 依赖: AnalyticSet, Empty.elim, analyticSet_range_of_polishSpace, continuous_bot, f_cont, f_range, range_eq_empty
-/
theorem analyticSet_iff_exists_polishSpace_range {s : Set α} :
    AnalyticSet s ↔
      exists (β : Type) (h : TopologicalSpace β) (_ : @PolishSpace β h) (f : β -> α),
        @Continuous _ _ h _ f ∧ range f = s := by
  constructor
  · intro h
    rw [AnalyticSet] at h
    rcases h with h | h
    · refine ⟨Empty, inferInstance, inferInstance, Empty.elim, continuous_bot, ?_⟩
      rw [h]
      exact range_eq_empty _
    · exact ⟨Nat -> Nat, inferInstance, inferInstance, h⟩
  · rintro ⟨β, h, h', f, f_cont, f_range⟩
    rw [← f_range]
    exact analyticSet_range_of_polishSpace f_cont

/--
theorem `AnalyticSet.image_of_continuousOn` / 定理 `AnalyticSet.image_of_continuousOn`

English:
theorem AnalyticSet.image_of_continuousOn
  statement: {β : Type*} [TopologicalSpace β] {s : Set α}
  proof: by
  rcases analyticSet_iff_exists_polishSpace_range.1 hs with ⟨γ, γtop, γpolish, g, g_cont, gs⟩
  have : f '' s = range (f ∘ g) := by rw [range_comp, gs]
  rw [this]
  apply analyticSet_range_of_polishSpace
  apply hf.comp_continuous g_cont fun x => _
  rw [← gs]
  exact mem_range_self

中文:
定理 AnalyticSet.image_of_continuousOn
  结论: {β : 类型} [TopologicalSpace β] {s : Set α}
  证明: by
  rcases analyticSet_iff_exists_polishSpace_range.1 hs with ⟨γ, γtop, γpolish, g, g_cont, gs⟩
  have : f '' s = range (f ∘ g) := by rw [range_comp, gs]
  rw [this]
  apply analyticSet_range_of_polishSpace
  apply hf.comp_continuous g_cont fun x => _
  rw [← gs]
  exact mem_range_self

Depends on / 依赖: analyticSet_iff_exists_polishSpace_range, analyticSet_range_of_polishSpace, comp_continuous, g_cont, hf.comp_continuous, mem_range_self, range_comp
-/
theorem AnalyticSet.image_of_continuousOn {β : Type*} [TopologicalSpace β] {s : Set α}
    (hs : AnalyticSet s) {f : α -> β} (hf : ContinuousOn f s) : AnalyticSet (f '' s) := by
  rcases analyticSet_iff_exists_polishSpace_range.1 hs with ⟨γ, γtop, γpolish, g, g_cont, gs⟩
  have : f '' s = range (f ∘ g) := by rw [range_comp, gs]
  rw [this]
  apply analyticSet_range_of_polishSpace
  apply hf.comp_continuous g_cont fun x => _
  rw [← gs]
  exact mem_range_self

/--
theorem `AnalyticSet.image_of_continuous` / 定理 `AnalyticSet.image_of_continuous`

English:
theorem AnalyticSet.image_of_continuous
  statement: {β : Type*} [TopologicalSpace β] {s : Set α}
  proof: hs.image_of_continuousOn hf.continuousOn

中文:
定理 AnalyticSet.image_of_continuous
  结论: {β : 类型} [TopologicalSpace β] {s : Set α}
  证明: hs.image_of_continuousOn hf.continuousOn

Depends on / 依赖: continuousOn, hf.continuousOn, hs.image_of_continuousOn, image_of_continuousOn
-/
theorem AnalyticSet.image_of_continuous {β : Type*} [TopologicalSpace β] {s : Set α}
    (hs : AnalyticSet s) {f : α -> β} (hf : Continuous f) : AnalyticSet (f '' s) :=
  hs.image_of_continuousOn hf.continuousOn

/--
theorem `AnalyticSet.iInter` / 定理 `AnalyticSet.iInter`

English:
theorem AnalyticSet.iInter
  statement: [hι : Nonempty ι] [Countable ι] [T2Space α] {s : ι -> Set α}
  proof: by
  rcases hι with ⟨i₀⟩
  /- For the proof, write each `s n` as the continuous image under a map `f n` of a
    Polish space `β n`. The product space `γ = Π n, β n` is also Polish, and so is the subset
    `t` of sequences `x n` for which `f n (x n)` is independent of `n`. The set `t` is Polish, an

中文:
定理 AnalyticSet.iInter
  结论: [hι : Nonempty ι] [Countable ι] [T2Space α] {s : ι -> Set α}
  证明: by
  rcases hι with ⟨i₀⟩
  /- For the proof, write each `s n` as the continuous image under a map `f n` of a
    Polish space `β n`. The product space `γ = Π n, β n` is also Polish, and so is the subset
    `t` of sequences `x n` for which `f n (x n)` is independent of `n`. The set `t` is Polish, an
-/
theorem AnalyticSet.iInter [hι : Nonempty ι] [Countable ι] [T2Space α] {s : ι -> Set α}
    (hs : forall n, AnalyticSet (s n)) : AnalyticSet (⋂ n, s n) := by
  rcases hι with ⟨i₀⟩
  /- For the proof, write each `s n` as the continuous image under a map `f n` of a
    Polish space `β n`. The product space `γ = Π n, β n` is also Polish, and so is the subset
    `t` of sequences `x n` for which `f n (x n)` is independent of `n`. The set `t` is Polish, and
    the range of `x ↦ f 0 (x 0)` on `t` is exactly `⋂ n, s n`, so this set is analytic. -/
  choose β hβ h'β f f_cont f_range using fun n =>
    analyticSet_iff_exists_polishSpace_range.1 (hs n)
  let γ := forall n, β n
  let t : Set γ := ⋂ n, { x | f n (x n) = f i₀ (x i₀) }
  have t_closed : IsClosed t := by
    apply isClosed_iInter
    intro n
    exact
      isClosed_eq ((f_cont n).comp (continuous_apply n)) ((f_cont i₀).comp (continuous_apply i₀))
  have : PolishSpace t := t_closed.polishSpace
  let F : t -> α := fun x => f i₀ ((x : γ) i₀)
  have F_cont : Continuous F := (f_cont i₀).comp ((continuous_apply i₀).comp continuous_subtype_val)
  have F_range : range F = ⋂ n : ι, s n := by
    apply Subset.antisymm
    · rintro y ⟨x, rfl⟩
      refine mem_iInter.2 fun n => ?_
      have : f n ((x : γ) n) = F x := (mem_iInter.1 x.2 n :)
      rw [← this]; rw [← f_range n]
      exact mem_range_self _
    · intro y hy
      have A : forall n, exists x : β n, f n x = y := by
        intro n
        rw [← mem_range]; rw [f_range n]
        exact mem_iInter.1 hy n
      choose x hx using A
      have xt : x in t := by
        refine mem_iInter.2 fun n => ?_
        simp [γ, hx]
      refine ⟨⟨x, xt⟩, ?_⟩
      exact hx i₀
  rw [← F_range]
  exact analyticSet_range_of_polishSpace F_cont

/--
theorem `AnalyticSet.iUnion` / 定理 `AnalyticSet.iUnion`

English:
theorem AnalyticSet.iUnion
  given: [Countable ι] {s : ι -> Set α} (hs : forall n, AnalyticSet (s n))
  proof: by
  /- For the proof, write each `s n` as the continuous image under a map `f n` of a
    Polish space `β n`. The union space `γ = Σ n, β n` is also Polish, and the map `F : γ → α` which
    coincides with `f n` on `β n` sends it to `⋃ n, s n`. -/
  choose β hβ h'β f f_cont f_range using fun n =>
 

中文:
定理 AnalyticSet.iUnion
  条件: [Countable ι] {s : ι -> Set α} (hs : 对任意 n, AnalyticSet (s n))
  证明: by
  /- For the proof, write each `s n` as the continuous image under a map `f n` of a
    Polish space `β n`. The union space `γ = Σ n, β n` is also Polish, and the map `F : γ → α` which
    coincides with `f n` on `β n` sends it to `⋃ n, s n`. -/
  choose β hβ h'β f f_cont f_range using fun n =>
 
-/
theorem AnalyticSet.iUnion [Countable ι] {s : ι -> Set α} (hs : forall n, AnalyticSet (s n)) :
    AnalyticSet (⋃ n, s n) := by
  /- For the proof, write each `s n` as the continuous image under a map `f n` of a
    Polish space `β n`. The union space `γ = Σ n, β n` is also Polish, and the map `F : γ → α` which
    coincides with `f n` on `β n` sends it to `⋃ n, s n`. -/
  choose β hβ h'β f f_cont f_range using fun n =>
    analyticSet_iff_exists_polishSpace_range.1 (hs n)
  let γ := Σ n, β n
  let F : γ -> α := fun ⟨n, x⟩ => f n x
  have F_cont : Continuous F := continuous_sigma f_cont
  have F_range : range F = ⋃ n, s n := by
    simp only [γ, F, range_sigma_eq_iUnion_range, f_range]
  rw [← F_range]
  exact analyticSet_range_of_polishSpace F_cont

/--
theorem `_root_.IsClosed.analyticSet` / 定理 `_root_.IsClosed.analyticSet`

English:
theorem _root_.IsClosed.analyticSet
  given: [PolishSpace α] {s : Set α} (hs : IsClosed s)
  proof: by
  have : PolishSpace s := hs.polishSpace
  rw [← @Subtype.range_val α s]
  exact analyticSet_range_of_polishSpace continuous_subtype_val

中文:
定理 _root_.IsClosed.analyticSet
  条件: [PolishSpace α] {s : Set α} (hs : IsClosed s)
  证明: by
  have : PolishSpace s := hs.polishSpace
  rw [← @Subtype.range_val α s]
  exact analyticSet_range_of_polishSpace continuous_subtype_val

Depends on / 依赖: PolishSpace, Subtype, Subtype.range_val, analyticSet_range_of_polishSpace, continuous_subtype_val, hs.polishSpace, polishSpace, range_val
-/
theorem _root_.IsClosed.analyticSet [PolishSpace α] {s : Set α} (hs : IsClosed s) :
    AnalyticSet s := by
  have : PolishSpace s := hs.polishSpace
  rw [← @Subtype.range_val α s]
  exact analyticSet_range_of_polishSpace continuous_subtype_val

/--
theorem `_root_.MeasurableSet.isClopenable` / 定理 `_root_.MeasurableSet.isClopenable`

English:
theorem _root_.MeasurableSet.isClopenable
  statement: [PolishSpace α] [MeasurableSpace α] [BorelSpace α]
  proof: by
  revert s
  apply MeasurableSet.induction_on_open
  · exact fun u hu => hu.isClopenable
  · exact fun u _ h'u => h'u.compl
  · exact fun f _ _ hf => IsClopenable.iUnion hf

中文:
定理 _root_.MeasurableSet.isClopenable
  结论: [PolishSpace α] [MeasurableSpace α] [BorelSpace α]
  证明: by
  revert s
  apply MeasurableSet.induction_on_open
  · exact fun u hu => hu.isClopenable
  · exact fun u _ h'u => h'u.compl
  · exact fun f _ _ hf => IsClopenable.iUnion hf

Depends on / 依赖: IsClopenable, IsClopenable.iUnion, MeasurableSet, MeasurableSet.induction_on_open, hu.isClopenable, iUnion, induction_on_open, isClopenable, revert, u.compl
-/
theorem _root_.MeasurableSet.isClopenable [PolishSpace α] [MeasurableSpace α] [BorelSpace α]
    {s : Set α} (hs : MeasurableSet s) : IsClopenable s := by
  revert s
  apply MeasurableSet.induction_on_open
  · exact fun u hu => hu.isClopenable
  · exact fun u _ h'u => h'u.compl
  · exact fun f _ _ hf => IsClopenable.iUnion hf

/--
theorem `_root_.MeasurableSet.analyticSet` / 定理 `_root_.MeasurableSet.analyticSet`

English:
theorem _root_.MeasurableSet.analyticSet
  statement: {α : Type*} [t : TopologicalSpace α] [PolishSpace α]
  proof: by
  /- For a short proof (avoiding measurable induction), one sees `s` as a closed set for a finer
    topology `t'`. It is analytic for this topology. As the identity from `t'` to `t` is continuous
    and the image of an analytic set is analytic, it follows that `s` is also analytic for `t`. -/
 

中文:
定理 _root_.MeasurableSet.analyticSet
  结论: {α : 类型} [t : TopologicalSpace α] [PolishSpace α]
  证明: by
  /- For a short proof (avoiding measurable induction), one sees `s` as a closed set for a finer
    topology `t'`. It is analytic for this topology. As the identity from `t'` to `t` is continuous
    and the image of an analytic set is analytic, it follows that `s` is also analytic for `t`. -/
 
-/
theorem _root_.MeasurableSet.analyticSet {α : Type*} [t : TopologicalSpace α] [PolishSpace α]
    [MeasurableSpace α] [BorelSpace α] {s : Set α} (hs : MeasurableSet s) : AnalyticSet s := by
  /- For a short proof (avoiding measurable induction), one sees `s` as a closed set for a finer
    topology `t'`. It is analytic for this topology. As the identity from `t'` to `t` is continuous
    and the image of an analytic set is analytic, it follows that `s` is also analytic for `t`. -/
  obtain ⟨t', t't, t'_polish, s_closed, _⟩ :
      exists t' : TopologicalSpace α, t' <= t ∧ @PolishSpace α t' ∧ IsClosed[t'] s ∧ IsOpen[t'] s :=
    hs.isClopenable
  have A := @IsClosed.analyticSet α t' t'_polish s s_closed
  convert! @AnalyticSet.image_of_continuous α t' α t s A id (continuous_id_of_le t't)
  simp only [id, image_id']

/--
theorem `_root_.Measurable.exists_continuous` / 定理 `_root_.Measurable.exists_continuous`

English:
theorem _root_.Measurable.exists_continuous
  statement: {α β : Type*} [t : TopologicalSpace α] [PolishSpace α]
  proof: by
  obtain ⟨b, b_count, -, hb⟩ :
      exists b : Set (Set (range f)), b.Countable ∧ ∅ ∉ b ∧ IsTopologicalBasis b :=
    exists_countable_basis (range f)
  have : Countable b := b_count.to_subtype
  have : forall s : b, IsClopenable (rangeFactorization f ⁻¹' s) := fun s => by
    apply MeasurableSe

中文:
定理 _root_.Measurable.exists_continuous
  结论: {α β : 类型} [t : TopologicalSpace α] [PolishSpace α]
  证明: by
  obtain ⟨b, b_count, -, hb⟩ :
      exists b : Set (Set (range f)), b.Countable ∧ ∅ ∉ b ∧ IsTopologicalBasis b :=
    exists_countable_basis (range f)
  have : Countable b := b_count.to_subtype
  have : forall s : b, IsClopenable (rangeFactorization f ⁻¹' s) := fun s => by
    apply MeasurableSe

Depends on / 依赖: Countable, IsClopenable, IsTopologicalBasis, MeasurableSet, MeasurableSet.isClopenable, PolishSpace, TopologicalSpace, Tpolish, _polish, b.Countable, b_count, b_count.to_subtype, exists_countable_basis, hb.isOpen, hf.subtype_mk, isClopenable, isOpen, measurableSet, rangeFactorization, subtype_mk
-/
theorem _root_.Measurable.exists_continuous {α β : Type*} [t : TopologicalSpace α] [PolishSpace α]
    [MeasurableSpace α] [BorelSpace α] [tβ : TopologicalSpace β] [MeasurableSpace β]
    [OpensMeasurableSpace β] {f : α -> β} [SecondCountableTopology (range f)] (hf : Measurable f) :
    exists t' : TopologicalSpace α, t' <= t ∧ @Continuous α β t' tβ f ∧ @PolishSpace α t' := by
  obtain ⟨b, b_count, -, hb⟩ :
      exists b : Set (Set (range f)), b.Countable ∧ ∅ ∉ b ∧ IsTopologicalBasis b :=
    exists_countable_basis (range f)
  have : Countable b := b_count.to_subtype
  have : forall s : b, IsClopenable (rangeFactorization f ⁻¹' s) := fun s => by
    apply MeasurableSet.isClopenable
    exact hf.subtype_mk (hb.isOpen s.2).measurableSet
  choose T Tt Tpolish _ Topen using this
  obtain ⟨t', t'T, t't, t'_polish⟩ :
      exists t' : TopologicalSpace α, (forall i, t' <= T i) ∧ t' <= t ∧ @PolishSpace α t' :=
    exists_polishSpace_forall_le (t := t) T Tt Tpolish
  refine ⟨t', t't, ?_, t'_polish⟩
  have : Continuous[t', _] (rangeFactorization f) :=
    hb.continuous_iff.2 fun s hs => t'T ⟨s, hs⟩ _ (Topen ⟨s, hs⟩)
  exact continuous_subtype_val.comp this

/--
theorem `_root_.MeasurableSet.analyticSet_image` / 定理 `_root_.MeasurableSet.analyticSet_image`

English:
theorem _root_.MeasurableSet.analyticSet_image
  statement: {X Y : Type*} [MeasurableSpace X]
  proof: by
  let := upgradeStandardBorel X
  rw [eq_borel_upgradeStandardBorel X] at hs
  rcases hf.exists_continuous with ⟨τ', hle, hfc, hτ'⟩
  let m' : MeasurableSpace X := @borel _ τ'
  have b' : BorelSpace X := ⟨rfl⟩
  have hle := borel_anti hle
  exact (hle _ hs).analyticSet.image_of_continuous hfc

中文:
定理 _root_.MeasurableSet.analyticSet_image
  结论: {X Y : 类型} [MeasurableSpace X]
  证明: by
  let := upgradeStandardBorel X
  rw [eq_borel_upgradeStandardBorel X] at hs
  rcases hf.exists_continuous with ⟨τ', hle, hfc, hτ'⟩
  let m' : MeasurableSpace X := @borel _ τ'
  have b' : BorelSpace X := ⟨rfl⟩
  have hle := borel_anti hle
  exact (hle _ hs).analyticSet.image_of_continuous hfc

Depends on / 依赖: BorelSpace, MeasurableSpace, analyticSet, analyticSet.image_of_continuous, borel_anti, eq_borel_upgradeStandardBorel, exists_continuous, hf.exists_continuous, image_of_continuous, upgradeStandardBorel
-/
theorem _root_.MeasurableSet.analyticSet_image {X Y : Type*} [MeasurableSpace X]
    [StandardBorelSpace X] [TopologicalSpace Y] [MeasurableSpace Y]
    [OpensMeasurableSpace Y] {f : X -> Y} [SecondCountableTopology (range f)] {s : Set X}
    (hs : MeasurableSet s) (hf : Measurable f) : AnalyticSet (f '' s) := by
  let := upgradeStandardBorel X
  rw [eq_borel_upgradeStandardBorel X] at hs
  rcases hf.exists_continuous with ⟨τ', hle, hfc, hτ'⟩
  let m' : MeasurableSpace X := @borel _ τ'
  have b' : BorelSpace X := ⟨rfl⟩
  have hle := borel_anti hle
  exact (hle _ hs).analyticSet.image_of_continuous hfc

/--
lemma `AnalyticSet.preimage` / 引理 `AnalyticSet.preimage`

English:
lemma AnalyticSet.preimage
  statement: {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
  proof: by
  rcases analyticSet_iff_exists_polishSpace_range.1 hs with ⟨Z, _, _, g, hg, rfl⟩
  have : IsClosed {x : X × Z | f x.1 = g x.2} := isClosed_eq hf.fst' hg.snd'
  convert! this.analyticSet.image_of_continuous continuous_fst
  ext x
  simp [eq_comm]

中文:
引理 AnalyticSet.preimage
  结论: {X Y : 类型} [TopologicalSpace X] [TopologicalSpace Y]
  证明: by
  rcases analyticSet_iff_exists_polishSpace_range.1 hs with ⟨Z, _, _, g, hg, rfl⟩
  have : IsClosed {x : X × Z | f x.1 = g x.2} := isClosed_eq hf.fst' hg.snd'
  convert! this.analyticSet.image_of_continuous continuous_fst
  ext x
  simp [eq_comm]
-/
protected lemma AnalyticSet.preimage {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    [PolishSpace X] [T2Space Y] {s : Set Y} (hs : AnalyticSet s) {f : X -> Y} (hf : Continuous f) :
    AnalyticSet (f ⁻¹' s) := by
  rcases analyticSet_iff_exists_polishSpace_range.1 hs with ⟨Z, _, _, g, hg, rfl⟩
  have : IsClosed {x : X × Z | f x.1 = g x.2} := isClosed_eq hf.fst' hg.snd'
  convert! this.analyticSet.image_of_continuous continuous_fst
  ext x
  simp [eq_comm]

/-! ### Separating sets with measurable sets -/

/--
Definition of `MeasurablySeparable` / `MeasurablySeparable` 的定义

English:
definition MeasurablySeparable
  signature: {α : Type*} [MeasurableSpace α] (s t : Set α)
  body: exists u, s subseteq u ∧ Disjoint t u ∧ MeasurableSet u

中文:
定义 MeasurablySeparable
  签名: {α : 类型} [MeasurableSpace α] (s t : Set α)
  定义体: exists u, s subseteq u ∧ Disjoint t u ∧ MeasurableSet u

Depends on / 依赖: Disjoint, MeasurableSet, subseteq
-/
def MeasurablySeparable {α : Type*} [MeasurableSpace α] (s t : Set α) : Prop :=
  exists u, s subseteq u ∧ Disjoint t u ∧ MeasurableSet u

/--
theorem `MeasurablySeparable.iUnion` / 定理 `MeasurablySeparable.iUnion`

English:
theorem MeasurablySeparable.iUnion
  statement: [Countable ι] {α : Type*} [MeasurableSpace α] {s t : ι -> Set α}
  proof: by
  choose u hsu htu hu using h
  refine ⟨⋃ m, ⋂ n, u m n, ?_, ?_, ?_⟩
  · refine iUnion_subset fun m => subset_iUnion_of_subset m ?_
    exact subset_iInter fun n => hsu m n
  · simp_rw [disjoint_iUnion_left, disjoint_iUnion_right]
    intro n m
    apply Disjoint.mono_right _ (htu m n)
    apply 

中文:
定理 MeasurablySeparable.iUnion
  结论: [Countable ι] {α : 类型} [MeasurableSpace α] {s t : ι -> Set α}
  证明: by
  choose u hsu htu hu using h
  refine ⟨⋃ m, ⋂ n, u m n, ?_, ?_, ?_⟩
  · refine iUnion_subset fun m => subset_iUnion_of_subset m ?_
    exact subset_iInter fun n => hsu m n
  · simp_rw [disjoint_iUnion_left, disjoint_iUnion_right]
    intro n m
    apply Disjoint.mono_right _ (htu m n)
    apply 

Depends on / 依赖: Disjoint, Disjoint.mono_right, MeasurableSet, MeasurableSet.iInter, MeasurableSet.iUnion, disjoint_iUnion_left, disjoint_iUnion_right, iInter, iInter_subset, iUnion, iUnion_subset, mono_right, simp_rw, subset_iInter, subset_iUnion_of_subset
-/
theorem MeasurablySeparable.iUnion [Countable ι] {α : Type*} [MeasurableSpace α] {s t : ι -> Set α}
    (h : forall m n, MeasurablySeparable (s m) (t n)) : MeasurablySeparable (⋃ n, s n) (⋃ m, t m) := by
  choose u hsu htu hu using h
  refine ⟨⋃ m, ⋂ n, u m n, ?_, ?_, ?_⟩
  · refine iUnion_subset fun m => subset_iUnion_of_subset m ?_
    exact subset_iInter fun n => hsu m n
  · simp_rw [disjoint_iUnion_left, disjoint_iUnion_right]
    intro n m
    apply Disjoint.mono_right _ (htu m n)
    apply iInter_subset
  · refine MeasurableSet.iUnion fun m => ?_
    exact MeasurableSet.iInter fun n => hu m n

/--
theorem `measurablySeparable_range_of_disjoint` / 定理 `measurablySeparable_range_of_disjoint`

English:
theorem measurablySeparable_range_of_disjoint
  statement: [T2Space α] [MeasurableSpace α]
  proof: by
  /- We follow [Kechris, *Classical Descriptive Set Theory* (Theorem 14.7)][kechris1995].
    If the ranges are not Borel-separated, then one can find two cylinders of length one whose
    images are not Borel-separated, and then two smaller cylinders of length two whose images are
    not Borel-

中文:
定理 measurablySeparable_range_of_disjoint
  结论: [T2Space α] [MeasurableSpace α]
  证明: by
  /- We follow [Kechris, *Classical Descriptive Set Theory* (Theorem 14.7)][kechris1995].
    If the ranges are not Borel-separated, then one can find two cylinders of length one whose
    images are not Borel-separated, and then two smaller cylinders of length two whose images are
    not Borel-
-/
theorem measurablySeparable_range_of_disjoint [T2Space α] [MeasurableSpace α]
    [OpensMeasurableSpace α] {f g : (Nat -> Nat) -> α} (hf : Continuous f) (hg : Continuous g)
    (h : Disjoint (range f) (range g)) : MeasurablySeparable (range f) (range g) := by
  /- We follow [Kechris, *Classical Descriptive Set Theory* (Theorem 14.7)][kechris1995].
    If the ranges are not Borel-separated, then one can find two cylinders of length one whose
    images are not Borel-separated, and then two smaller cylinders of length two whose images are
    not Borel-separated, and so on. One thus gets two sequences of cylinders, that decrease to two
    points `x` and `y`. Their images are different by the disjointness assumption, hence contained
    in two disjoint open sets by the T2 property. By continuity, long enough cylinders around `x`
    and `y` have images which are separated by these two disjoint open sets, a contradiction.
    -/
  by_contra hfg
  have I : forall n x y, ¬MeasurablySeparable (f '' cylinder x n) (g '' cylinder y n) ->
      exists x' y', x' in cylinder x n ∧ y' in cylinder y n ∧
      ¬MeasurablySeparable (f '' cylinder x' (n + 1)) (g '' cylinder y' (n + 1)) := by
    intro n x y
    contrapose!
    intro H
    rw [← iUnion_cylinder_update x n]; rw [← iUnion_cylinder_update y n]; rw [image_iUnion]; rw [image_iUnion]
    refine MeasurablySeparable.iUnion fun i j => ?_
    exact H _ _ (update_mem_cylinder _ _ _) (update_mem_cylinder _ _ _)
  -- consider the set of pairs of cylinders of some length whose images are not Borel-separated
  let A :=
    { p : Nat × (Nat -> Nat) × (Nat -> Nat) //
      ¬MeasurablySeparable (f '' cylinder p.2.1 p.1) (g '' cylinder p.2.2 p.1) }
  -- for each such pair, one can find longer cylinders whose images are not Borel-separated either
  have : forall p : A, exists q : A,
      q.1.1 = p.1.1 + 1 ∧ q.1.2.1 in cylinder p.1.2.1 p.1.1 ∧ q.1.2.2 in cylinder p.1.2.2 p.1.1 := by
    rintro ⟨⟨n, x, y⟩, hp⟩
    rcases I n x y hp with ⟨x', y', hx', hy', h'⟩
    exact ⟨⟨⟨n + 1, x', y'⟩, h'⟩, rfl, hx', hy'⟩
  choose F hFn hFx hFy using this
  let p0 : A := ⟨⟨0, fun _ => 0, fun _ => 0⟩, by simp [hfg]⟩
  -- construct inductively decreasing sequences of cylinders whose images are not separated
  let p : Nat -> A := fun n => F^[n] p0
  have prec : forall n, p (n + 1) = F (p n) := fun n => by simp only [p, iterate_succ', Function.comp]
  -- check that at the `n`-th step we deal with cylinders of length `n`
  have pn_fst : forall n, (p n).1.1 = n := fun n => by
    induction n with
    | zero => rfl
    | succ n IH => simp only [prec, hFn, IH]
  -- check that the cylinders we construct are indeed decreasing, by checking that the coordinates
  -- are stationary.
  have Ix : forall m n, m + 1 <= n -> (p n).1.2.1 m = (p (m + 1)).1.2.1 m := by
    intro m
    apply Nat.le_induction
    · rfl
    intro n hmn IH
    have I : (F (p n)).val.snd.fst m = (p n).val.snd.fst m := by
      apply hFx (p n) m
      rw [pn_fst]
      exact hmn
    rw [prec]; rw [I]; rw [IH]
  have Iy : forall m n, m + 1 <= n -> (p n).1.2.2 m = (p (m + 1)).1.2.2 m := by
    intro m
    apply Nat.le_induction
    · rfl
    intro n hmn IH
    have I : (F (p n)).val.snd.snd m = (p n).val.snd.snd m := by
      apply hFy (p n) m
      rw [pn_fst]
      exact hmn
    rw [prec]; rw [I]; rw [IH]
  -- denote by `x` and `y` the limit points of these two sequences of cylinders.
  set x : Nat -> Nat := fun n => (p (n + 1)).1.2.1 n with hx
  set y : Nat -> Nat := fun n => (p (n + 1)).1.2.2 n with hy
  -- by design, the cylinders around these points have images which are not Borel-separable.
  have M : forall n, ¬MeasurablySeparable (f '' cylinder x n) (g '' cylinder y n) := by
    intro n
    convert! (p n).2 using 3
    · rw [pn_fst, ← mem_cylinder_iff_eq, mem_cylinder_iff]
      intro i hi
      rw [hx]
      exact (Ix i n hi).symm
    · rw [pn_fst, ← mem_cylinder_iff_eq, mem_cylinder_iff]
      intro i hi
      rw [hy]
      exact (Iy i n hi).symm
  -- consider two open sets separating `f x` and `g y`.
  obtain ⟨u, v, u_open, v_open, xu, yv, huv⟩ :
      exists u v : Set α, IsOpen u ∧ IsOpen v ∧ f x in u ∧ g y in v ∧ Disjoint u v := by
    apply t2_separation
    exact disjoint_iff_forall_ne.1 h (mem_range_self _) (mem_range_self _)
  let : MetricSpace (Nat -> Nat) := metricSpaceNatNat
  obtain ⟨εx, εxpos, hεx⟩ : exists (εx : Real), εx > 0 ∧ Metric.ball x εx subseteq f ⁻¹' u := by
    apply Metric.mem_nhds_iff.1
    exact hf.continuousAt.preimage_mem_nhds (u_open.mem_nhds xu)
  obtain ⟨εy, εypos, hεy⟩ : exists (εy : Real), εy > 0 ∧ Metric.ball y εy subseteq g ⁻¹' v := by
    apply Metric.mem_nhds_iff.1
    exact hg.continuousAt.preimage_mem_nhds (v_open.mem_nhds yv)
  obtain ⟨n, hn⟩ : exists n : Nat, (1 / 2 : Real) ^ n < min εx εy :=
    exists_pow_lt_of_lt_one (lt_min εxpos εypos) (by norm_num)
  -- for large enough `n`, these open sets separate the images of long cylinders around `x` and `y`
  have B : MeasurablySeparable (f '' cylinder x n) (g '' cylinder y n) := by
    refine ⟨u, ?_, ?_, u_open.measurableSet⟩
    · rw [image_subset_iff]
      apply Subset.trans _ hεx
      intro z hz
      rw [mem_cylinder_iff_dist_le] at hz
      exact hz.trans_lt (hn.trans_le (min_le_left _ _))
    · refine Disjoint.mono_left ?_ huv.symm
      change g '' cylinder y n subseteq v
      rw [image_subset_iff]
      apply Subset.trans _ hεy
      intro z hz
      rw [mem_cylinder_iff_dist_le] at hz
      exact hz.trans_lt (hn.trans_le (min_le_right _ _))
  -- this is a contradiction.
  exact M n B

/--
theorem `AnalyticSet.measurablySeparable` / 定理 `AnalyticSet.measurablySeparable`

English:
theorem AnalyticSet.measurablySeparable
  statement: [T2Space α] [MeasurableSpace α] [OpensMeasurableSpace α]
  proof: by
  rw [AnalyticSet] at hs ht
  rcases hs with (rfl | ⟨f, f_cont, rfl⟩)
  · refine ⟨∅, Subset.refl _, by simp, MeasurableSet.empty⟩
  rcases ht with (rfl | ⟨g, g_cont, rfl⟩)
  · exact ⟨univ, subset_univ _, by simp, MeasurableSet.univ⟩
  exact measurablySeparable_range_of_disjoint f_cont g_cont h

中文:
定理 AnalyticSet.measurablySeparable
  结论: [T2Space α] [MeasurableSpace α] [OpensMeasurableSpace α]
  证明: by
  rw [AnalyticSet] at hs ht
  rcases hs with (rfl | ⟨f, f_cont, rfl⟩)
  · refine ⟨∅, Subset.refl _, by simp, MeasurableSet.empty⟩
  rcases ht with (rfl | ⟨g, g_cont, rfl⟩)
  · exact ⟨univ, subset_univ _, by simp, MeasurableSet.univ⟩
  exact measurablySeparable_range_of_disjoint f_cont g_cont h

Depends on / 依赖: AnalyticSet, MeasurableSet, MeasurableSet.empty, MeasurableSet.univ, Subset, Subset.refl, f_cont, g_cont, measurablySeparable_range_of_disjoint, subset_univ
-/
theorem AnalyticSet.measurablySeparable [T2Space α] [MeasurableSpace α] [OpensMeasurableSpace α]
    {s t : Set α} (hs : AnalyticSet s) (ht : AnalyticSet t) (h : Disjoint s t) :
    MeasurablySeparable s t := by
  rw [AnalyticSet] at hs ht
  rcases hs with (rfl | ⟨f, f_cont, rfl⟩)
  · refine ⟨∅, Subset.refl _, by simp, MeasurableSet.empty⟩
  rcases ht with (rfl | ⟨g, g_cont, rfl⟩)
  · exact ⟨univ, subset_univ _, by simp, MeasurableSet.univ⟩
  exact measurablySeparable_range_of_disjoint f_cont g_cont h

/--
theorem `AnalyticSet.measurableSet_of_compl` / 定理 `AnalyticSet.measurableSet_of_compl`

English:
theorem AnalyticSet.measurableSet_of_compl
  statement: [T2Space α] [MeasurableSpace α] [OpensMeasurableSpace α]
  proof: by
  rcases hs.measurablySeparable hsc disjoint_compl_right with ⟨u, hsu, hdu, hmu⟩
  obtain rfl : s = u := hsu.antisymm (disjoint_compl_left_iff_subset.1 hdu)
  exact hmu

中文:
定理 AnalyticSet.measurableSet_of_compl
  结论: [T2Space α] [MeasurableSpace α] [OpensMeasurableSpace α]
  证明: by
  rcases hs.measurablySeparable hsc disjoint_compl_right with ⟨u, hsu, hdu, hmu⟩
  obtain rfl : s = u := hsu.antisymm (disjoint_compl_left_iff_subset.1 hdu)
  exact hmu

Depends on / 依赖: antisymm, disjoint_compl_left_iff_subset, disjoint_compl_right, hs.measurablySeparable, hsu.antisymm, measurablySeparable
-/
theorem AnalyticSet.measurableSet_of_compl [T2Space α] [MeasurableSpace α] [OpensMeasurableSpace α]
    {s : Set α} (hs : AnalyticSet s) (hsc : AnalyticSet sᶜ) : MeasurableSet s := by
  rcases hs.measurablySeparable hsc disjoint_compl_right with ⟨u, hsu, hdu, hmu⟩
  obtain rfl : s = u := hsu.antisymm (disjoint_compl_left_iff_subset.1 hdu)
  exact hmu

end MeasureTheory

/-!
### Measurability of preimages under measurable maps
-/

namespace Measurable

open MeasurableSpace

variable {X Y Z β : Type*} [MeasurableSpace X] [StandardBorelSpace X]
  [TopologicalSpace Y] [T0Space Y] [MeasurableSpace Y] [OpensMeasurableSpace Y] [MeasurableSpace β]
  [MeasurableSpace Z]

/--
theorem `measurableSet_preimage_iff_of_surjective` / 定理 `measurableSet_preimage_iff_of_surjective`

English:
theorem measurableSet_preimage_iff_of_surjective
  statement: [CountablySeparated Z]
  proof: by
  refine ⟨fun h => ?_, fun h => hf h⟩
  rcases exists_opensMeasurableSpace_of_countablySeparated Z with ⟨τ, _, _, _⟩
  apply AnalyticSet.measurableSet_of_compl
  · rw [← image_preimage_eq s hsurj]
    exact h.analyticSet_image hf
  · rw [← image_preimage_eq sᶜ hsurj]
    exact h.compl.analyticSet

中文:
定理 measurableSet_preimage_iff_of_surjective
  结论: [CountablySeparated Z]
  证明: by
  refine ⟨fun h => ?_, fun h => hf h⟩
  rcases exists_opensMeasurableSpace_of_countablySeparated Z with ⟨τ, _, _, _⟩
  apply AnalyticSet.measurableSet_of_compl
  · rw [← image_preimage_eq s hsurj]
    exact h.analyticSet_image hf
  · rw [← image_preimage_eq sᶜ hsurj]
    exact h.compl.analyticSet

Depends on / 依赖: AnalyticSet, AnalyticSet.measurableSet_of_compl, analyticSet_image, exists_opensMeasurableSpace_of_countablySeparated, h.analyticSet_image, h.compl.analyticSet_image, image_preimage_eq, measurableSet_of_compl
-/
theorem measurableSet_preimage_iff_of_surjective [CountablySeparated Z]
    {f : X -> Z} (hf : Measurable f) (hsurj : Surjective f) {s : Set Z} :
    MeasurableSet (f ⁻¹' s) ↔ MeasurableSet s := by
  refine ⟨fun h => ?_, fun h => hf h⟩
  rcases exists_opensMeasurableSpace_of_countablySeparated Z with ⟨τ, _, _, _⟩
  apply AnalyticSet.measurableSet_of_compl
  · rw [← image_preimage_eq s hsurj]
    exact h.analyticSet_image hf
  · rw [← image_preimage_eq sᶜ hsurj]
    exact h.compl.analyticSet_image hf

/--
theorem `map_measurableSpace_eq` / 定理 `map_measurableSpace_eq`

English:
theorem map_measurableSpace_eq
  statement: [CountablySeparated Z]
  proof: MeasurableSpace.ext fun _ => hf.measurableSet_preimage_iff_of_surjective hsurj

中文:
定理 map_measurableSpace_eq
  结论: [CountablySeparated Z]
  证明: MeasurableSpace.ext fun _ => hf.measurableSet_preimage_iff_of_surjective hsurj

Depends on / 依赖: MeasurableSpace, MeasurableSpace.ext, hf.measurableSet_preimage_iff_of_surjective, measurableSet_preimage_iff_of_surjective
-/
theorem map_measurableSpace_eq [CountablySeparated Z]
    {f : X -> Z} (hf : Measurable f)
    (hsurj : Surjective f) : MeasurableSpace.map f ‹MeasurableSpace X› = ‹MeasurableSpace Z› :=
  MeasurableSpace.ext fun _ => hf.measurableSet_preimage_iff_of_surjective hsurj

/--
theorem `map_measurableSpace_eq_borel` / 定理 `map_measurableSpace_eq_borel`

English:
theorem map_measurableSpace_eq_borel
  statement: [SecondCountableTopology Y] {f : X -> Y} (hf : Measurable f)
  proof: by
  have d := hf.mono le_rfl OpensMeasurableSpace.borel_le
  let := borel Y; have : BorelSpace Y := ⟨rfl⟩
  exact d.map_measurableSpace_eq hsurj

中文:
定理 map_measurableSpace_eq_borel
  结论: [SecondCountableTopology Y] {f : X -> Y} (hf : Measurable f)
  证明: by
  have d := hf.mono le_rfl OpensMeasurableSpace.borel_le
  let := borel Y; have : BorelSpace Y := ⟨rfl⟩
  exact d.map_measurableSpace_eq hsurj

Depends on / 依赖: BorelSpace, OpensMeasurableSpace, OpensMeasurableSpace.borel_le, borel_le, d.map_measurableSpace_eq, hf.mono, le_rfl, map_measurableSpace_eq
-/
theorem map_measurableSpace_eq_borel [SecondCountableTopology Y] {f : X -> Y} (hf : Measurable f)
    (hsurj : Surjective f) : MeasurableSpace.map f ‹MeasurableSpace X› = borel Y := by
  have d := hf.mono le_rfl OpensMeasurableSpace.borel_le
  let := borel Y; have : BorelSpace Y := ⟨rfl⟩
  exact d.map_measurableSpace_eq hsurj

/--
theorem `borelSpace_codomain` / 定理 `borelSpace_codomain`

English:
theorem borelSpace_codomain
  statement: [SecondCountableTopology Y] {f : X -> Y} (hf : Measurable f)
  proof: ⟨(hf.map_measurableSpace_eq hsurj).symm.trans hf.map_measurableSpace_eq_borel hsurj⟩

中文:
定理 borelSpace_codomain
  结论: [SecondCountableTopology Y] {f : X -> Y} (hf : Measurable f)
  证明: ⟨(hf.map_measurableSpace_eq hsurj).symm.trans hf.map_measurableSpace_eq_borel hsurj⟩

Depends on / 依赖: hf.map_measurableSpace_eq, hf.map_measurableSpace_eq_borel, map_measurableSpace_eq, map_measurableSpace_eq_borel, symm.trans
-/
theorem borelSpace_codomain [SecondCountableTopology Y] {f : X -> Y} (hf : Measurable f)
    (hsurj : Surjective f) : BorelSpace Y :=
⟨(hf.map_measurableSpace_eq hsurj).symm.trans hf.map_measurableSpace_eq_borel hsurj⟩

/--
theorem `measurableSet_preimage_iff_preimage_val` / 定理 `measurableSet_preimage_iff_preimage_val`

English:
theorem measurableSet_preimage_iff_preimage_val
  statement: {f : X -> Z} [CountablySeparated (range f)]
  proof: have hf' : Measurable (rangeFactorization f) := by fun_prop
  hf'.measurableSet_preimage_iff_of_surjective (s := Subtype.val ⁻¹' s)
    rangeFactorization_surjective

中文:
定理 measurableSet_preimage_iff_preimage_val
  结论: {f : X -> Z} [CountablySeparated (range f)]
  证明: have hf' : Measurable (rangeFactorization f) := by fun_prop
  hf'.measurableSet_preimage_iff_of_surjective (s := Subtype.val ⁻¹' s)
    rangeFactorization_surjective

Depends on / 依赖: Measurable, Subtype, Subtype.val, fun_prop, measurableSet_preimage_iff_of_surjective, rangeFactorization, rangeFactorization_surjective
-/
theorem measurableSet_preimage_iff_preimage_val {f : X -> Z} [CountablySeparated (range f)]
    (hf : Measurable f) {s : Set Z} :
    MeasurableSet (f ⁻¹' s) ↔ MeasurableSet ((↑) ⁻¹' s : Set (range f)) :=
  have hf' : Measurable (rangeFactorization f) := by fun_prop
  hf'.measurableSet_preimage_iff_of_surjective (s := Subtype.val ⁻¹' s)
    rangeFactorization_surjective

/--
theorem `measurableSet_preimage_iff_inter_range` / 定理 `measurableSet_preimage_iff_inter_range`

English:
theorem measurableSet_preimage_iff_inter_range
  statement: {f : X -> Z} [CountablySeparated (range f)]
  proof: by
  rw [hf.measurableSet_preimage_iff_preimage_val]; rw [inter_comm]; rw [← (MeasurableEmbedding.subtype_coe hr).measurableSet_image]; rw [Subtype.image_preimage_coe]

中文:
定理 measurableSet_preimage_iff_inter_range
  结论: {f : X -> Z} [CountablySeparated (range f)]
  证明: by
  rw [hf.measurableSet_preimage_iff_preimage_val]; rw [inter_comm]; rw [← (MeasurableEmbedding.subtype_coe hr).measurableSet_image]; rw [Subtype.image_preimage_coe]

Depends on / 依赖: MeasurableEmbedding, MeasurableEmbedding.subtype_coe, Subtype, Subtype.image_preimage_coe, hf.measurableSet_preimage_iff_preimage_val, image_preimage_coe, inter_comm, measurableSet_image, measurableSet_preimage_iff_preimage_val, subtype_coe
-/
theorem measurableSet_preimage_iff_inter_range {f : X -> Z} [CountablySeparated (range f)]
    (hf : Measurable f) (hr : MeasurableSet (range f)) {s : Set Z} :
    MeasurableSet (f ⁻¹' s) ↔ MeasurableSet (s inter range f) := by
  rw [hf.measurableSet_preimage_iff_preimage_val]; rw [inter_comm]; rw [← (MeasurableEmbedding.subtype_coe hr).measurableSet_image]; rw [Subtype.image_preimage_coe]

/--
theorem `measurable_comp_iff_restrict` / 定理 `measurable_comp_iff_restrict`

English:
theorem measurable_comp_iff_restrict
  statement: {f : X -> Z}
  proof: forall₂_congr fun s _ => measurableSet_preimage_iff_preimage_val hf (s := g ⁻¹' s)

中文:
定理 measurable_comp_iff_restrict
  结论: {f : X -> Z}
  证明: forall₂_congr fun s _ => measurableSet_preimage_iff_preimage_val hf (s := g ⁻¹' s)

Depends on / 依赖: measurableSet_preimage_iff_preimage_val
-/
theorem measurable_comp_iff_restrict {f : X -> Z}
    [CountablySeparated (range f)]
    (hf : Measurable f) {g : Z -> β} : Measurable (g ∘ f) ↔ Measurable (domRestrict (range f) g) :=
  forall₂_congr fun s _ => measurableSet_preimage_iff_preimage_val hf (s := g ⁻¹' s)

/--
theorem `measurable_comp_iff_of_surjective` / 定理 `measurable_comp_iff_of_surjective`

English:
theorem measurable_comp_iff_of_surjective
  statement: [CountablySeparated Z]
  proof: forall₂_congr fun s _ => measurableSet_preimage_iff_of_surjective hf hsurj (s := g ⁻¹' s)

中文:
定理 measurable_comp_iff_of_surjective
  结论: [CountablySeparated Z]
  证明: forall₂_congr fun s _ => measurableSet_preimage_iff_of_surjective hf hsurj (s := g ⁻¹' s)

Depends on / 依赖: measurableSet_preimage_iff_of_surjective
-/
theorem measurable_comp_iff_of_surjective [CountablySeparated Z]
    {f : X -> Z} (hf : Measurable f) (hsurj : Surjective f)
    {g : Z -> β} : Measurable (g ∘ f) ↔ Measurable g :=
  forall₂_congr fun s _ => measurableSet_preimage_iff_of_surjective hf hsurj (s := g ⁻¹' s)

end Measurable

/--
theorem `Continuous.map_eq_borel` / 定理 `Continuous.map_eq_borel`

English:
theorem Continuous.map_eq_borel
  statement: {X Y : Type*} [TopologicalSpace X] [PolishSpace X]
  proof: by
  borelize Y
  exact hf.measurable.map_measurableSpace_eq hsurj

中文:
定理 Continuous.map_eq_borel
  结论: {X Y : 类型} [TopologicalSpace X] [PolishSpace X]
  证明: by
  borelize Y
  exact hf.measurable.map_measurableSpace_eq hsurj

Depends on / 依赖: borelize, hf.measurable.map_measurableSpace_eq, map_measurableSpace_eq, measurable
-/
theorem Continuous.map_eq_borel {X Y : Type*} [TopologicalSpace X] [PolishSpace X]
    [MeasurableSpace X] [BorelSpace X] [TopologicalSpace Y] [T0Space Y] [SecondCountableTopology Y]
    {f : X -> Y} (hf : Continuous f) (hsurj : Surjective f) :
    MeasurableSpace.map f ‹MeasurableSpace X› = borel Y := by
  borelize Y
  exact hf.measurable.map_measurableSpace_eq hsurj

/--
theorem `Continuous.map_borel_eq` / 定理 `Continuous.map_borel_eq`

English:
theorem Continuous.map_borel_eq
  statement: {X Y : Type*} [TopologicalSpace X] [PolishSpace X]
  proof: by
  borelize X
  exact hf.map_eq_borel hsurj

中文:
定理 Continuous.map_borel_eq
  结论: {X Y : 类型} [TopologicalSpace X] [PolishSpace X]
  证明: by
  borelize X
  exact hf.map_eq_borel hsurj

Depends on / 依赖: borelize, hf.map_eq_borel, map_eq_borel
-/
theorem Continuous.map_borel_eq {X Y : Type*} [TopologicalSpace X] [PolishSpace X]
    [TopologicalSpace Y] [T0Space Y] [SecondCountableTopology Y] {f : X -> Y} (hf : Continuous f)
    (hsurj : Surjective f) : MeasurableSpace.map f (borel X) = borel Y := by
  borelize X
  exact hf.map_eq_borel hsurj

/--
Instance `Quotient.borelSpace` / 实例 `Quotient.borelSpace`

English:
instance Quotient.borelSpace
  signature: {X : Type*} [TopologicalSpace X] [PolishSpace X] [MeasurableSpace X]
  body: ⟨continuous_quotient_mk'.map_eq_borel Quotient.mk'_surjective⟩

中文:
实例 Quotient.borelSpace
  签名: {X : 类型} [TopologicalSpace X] [PolishSpace X] [MeasurableSpace X]
  定义体: ⟨continuous_quotient_mk'.map_eq_borel Quotient.mk'_surjective⟩

Depends on / 依赖: Quotient, Quotient.mk, _surjective, continuous_quotient_mk, map_eq_borel
-/
instance Quotient.borelSpace {X : Type*} [TopologicalSpace X] [PolishSpace X] [MeasurableSpace X]
    [BorelSpace X] {s : Setoid X} [T0Space (Quotient s)] [SecondCountableTopology (Quotient s)] :
    BorelSpace (Quotient s) :=
  ⟨continuous_quotient_mk'.map_eq_borel Quotient.mk'_surjective⟩

/-- When the subgroup `N < G` is not necessarily `Normal`, we have a `CosetSpace` as opposed
to `QuotientGroup` (the next `instance`).
TODO: typeclass inference should normally find this, but currently doesn't.
E.g., `MeasurableSMul G (G ⧸ Γ)` fails to synthesize, even though `G ⧸ Γ` is the quotient
of `G` by the action of `Γ`; it seems unable to pick up the `BorelSpace` instance. -/
@[to_additive AddCosetSpace.borelSpace
  /-- When the additive subgroup `N < G` is not necessarily `Normal`, we have an `AddCosetSpace` as
opposed to `QuotientAddGroup` (the next `instance`).
TODO: typeclass inference should normally find this, but currently doesn't.
E.g., `MeasurableVAdd G (G ⧸ Γ)` fails to synthesize, even though `G ⧸ Γ` is the quotient
of `G` by the action of `Γ`; it seems unable to pick up the `BorelSpace` instance. -/]
/--
Instance `CosetSpace.borelSpace` / 实例 `CosetSpace.borelSpace`

English:
instance CosetSpace.borelSpace
  signature: {G : Type*} [TopologicalSpace G] [PolishSpace G] [Group G]
  body: Quotient.borelSpace

@[to_additive]

中文:
实例 CosetSpace.borelSpace
  签名: {G : 类型} [TopologicalSpace G] [PolishSpace G] [Group G]
  定义体: Quotient.borelSpace

@[to_additive]

Depends on / 依赖: Quotient, Quotient.borelSpace, borelSpace
-/
instance CosetSpace.borelSpace {G : Type*} [TopologicalSpace G] [PolishSpace G] [Group G]
    [MeasurableSpace G] [BorelSpace G] {N : Subgroup G} [T2Space (G ⧸ N)]
    [SecondCountableTopology (G ⧸ N)] : BorelSpace (G ⧸ N) := Quotient.borelSpace

@[to_additive]
/--
Instance `QuotientGroup.borelSpace` / 实例 `QuotientGroup.borelSpace`

English:
instance QuotientGroup.borelSpace
  signature: {G : Type*} [TopologicalSpace G] [PolishSpace G] [Group G]
  body: ⟨continuous_mk.map_eq_borel mk_surjective⟩

中文:
实例 QuotientGroup.borelSpace
  签名: {G : 类型} [TopologicalSpace G] [PolishSpace G] [Group G]
  定义体: ⟨continuous_mk.map_eq_borel mk_surjective⟩

Depends on / 依赖: continuous_mk, continuous_mk.map_eq_borel, map_eq_borel, mk_surjective
-/
instance QuotientGroup.borelSpace {G : Type*} [TopologicalSpace G] [PolishSpace G] [Group G]
    [IsTopologicalGroup G] [MeasurableSpace G] [BorelSpace G] {N : Subgroup G} [N.Normal]
    [IsClosed (N : Set G)] : BorelSpace (G ⧸ N) :=
  ⟨continuous_mk.map_eq_borel mk_surjective⟩

/-! ### Injective images of Borel sets -/

variable {γ : Type*}

/--
theorem `MeasureTheory.measurableSet_range_of_continuous_injective` / 定理 `MeasureTheory.measurableSet_range_of_continuous_injective`

English:
theorem MeasureTheory.measurableSet_range_of_continuous_injective
  statement: {β : Type*} [TopologicalSpace γ]
  proof: by
  /- We follow [Fremlin, *Measure Theory* (volume 4, 423I)][fremlin_vol4].
    Let `b = {s i}` be a countable basis for `α`. When `s i` and `s j` are disjoint, their images
    are disjoint analytic sets, hence by the separation theorem one can find a Borel-measurable set
    `q i j` separating t

中文:
定理 MeasureTheory.measurableSet_range_of_continuous_injective
  结论: {β : 类型} [TopologicalSpace γ]
  证明: by
  /- We follow [Fremlin, *Measure Theory* (volume 4, 423I)][fremlin_vol4].
    Let `b = {s i}` be a countable basis for `α`. When `s i` and `s j` are disjoint, their images
    are disjoint analytic sets, hence by the separation theorem one can find a Borel-measurable set
    `q i j` separating t
-/
theorem MeasureTheory.measurableSet_range_of_continuous_injective {β : Type*} [TopologicalSpace γ]
    [PolishSpace γ] [TopologicalSpace β] [T2Space β] [MeasurableSpace β] [OpensMeasurableSpace β]
    {f : γ -> β} (f_cont : Continuous f) (f_inj : Injective f) :
    MeasurableSet (range f) := by
  /- We follow [Fremlin, *Measure Theory* (volume 4, 423I)][fremlin_vol4].
    Let `b = {s i}` be a countable basis for `α`. When `s i` and `s j` are disjoint, their images
    are disjoint analytic sets, hence by the separation theorem one can find a Borel-measurable set
    `q i j` separating them.
    Let `E i = closure (f '' s i) ∩ ⋂ j, q i j \ q j i`. It contains `f '' (s i)` and it is
    measurable. Let `F n = ⋃ E i`, where the union is taken over those `i` for which `diam (s i)`
    is bounded by some number `u n` tending to `0` with `n`.
    We claim that `range f = ⋂ F n`, from which the measurability is obvious. The inclusion `⊆` is
    straightforward. To show `⊇`, consider a point `x` in the intersection. For each `n`, it belongs
    to some `E i` with `diam (s i) ≤ u n`. Pick a point `y i ∈ s i`. We claim that for such `i`
    and `j`, the intersection `s i ∩ s j` is nonempty: if it were empty, then thanks to the
    separating set `q i j` in the definition of `E i` one could not have `x ∈ E i ∩ E j`.
    Since these two sets have small diameter, it follows that `y i` and `y j` are close.
    Thus, `y` is a Cauchy sequence, converging to a limit `z`. We claim that `f z = x`, completing
    the proof.
    Otherwise, one could find open sets `v` and `w` separating `f z` from `x`. Then, for large `n`,
    the image `f '' (s i)` would be included in `v` by continuity of `f`, so its closure would be
    contained in the closure of `v`, and therefore it would be disjoint from `w`. This is a
    contradiction since `x` belongs both to this closure and to `w`. -/
  let := TopologicalSpace.upgradeIsCompletelyMetrizable γ
  obtain ⟨b, b_count, b_nonempty, hb⟩ :
    exists b : Set (Set γ), b.Countable ∧ ∅ ∉ b ∧ IsTopologicalBasis b := exists_countable_basis γ
  have : Encodable b := b_count.toEncodable
  let A := { p : b × b // Disjoint (p.1 : Set γ) p.2 }
  -- for each pair of disjoint sets in the topological basis `b`, consider Borel sets separating
  -- their images, by injectivity of `f` and the Lusin separation theorem.
  have : forall p : A, exists q : Set β,
      f '' (p.1.1 : Set γ) subseteq q ∧ Disjoint (f '' (p.1.2 : Set γ)) q ∧ MeasurableSet q := by
    intro p
    apply
      AnalyticSet.measurablySeparable ((hb.isOpen p.1.1.2).analyticSet_image f_cont)
        ((hb.isOpen p.1.2.2).analyticSet_image f_cont)
    exact Disjoint.image p.2 f_inj.injOn (subset_univ _) (subset_univ _)
  choose q hq1 hq2 q_meas using this
  -- define sets `E i` and `F n` as in the proof sketch above
  let E : b -> Set β := fun s =>
    closure (f '' s) inter ⋂ (t : b) (ht : Disjoint s.1 t.1), q ⟨(s, t), ht⟩ \ q ⟨(t, s), ht.symm⟩
  obtain ⟨u, u_anti, u_pos, u_lim⟩ :
      exists u : Nat -> Real, StrictAnti u ∧ (forall n : Nat, 0 < u n) ∧ Tendsto u atTop (𝓝 0) :=
    exists_seq_strictAnti_tendsto (0 : Real)
  let F : Nat -> Set β := fun n => ⋃ (s : b) (_ : IsBounded s.1 ∧ diam s.1 <= u n), E s
  -- it is enough to show that `range f = ⋂ F n`, as the latter set is obviously measurable.
  suffices range f = ⋂ n, F n by
    have E_meas : forall s : b, MeasurableSet (E s) := by
      intro b
      refine isClosed_closure.measurableSet.inter ?_
      refine MeasurableSet.iInter fun s => ?_
      exact MeasurableSet.iInter fun hs => (q_meas _).diff (q_meas _)
    have F_meas : forall n, MeasurableSet (F n) := by
      intro n
      refine MeasurableSet.iUnion fun s => ?_
      exact MeasurableSet.iUnion fun _ => E_meas _
    rw [this]
    exact MeasurableSet.iInter fun n => F_meas n
  -- we check both inclusions.
  apply Subset.antisymm
  -- we start with the easy inclusion `range f ⊆ ⋂ F n`. One just needs to unfold the definitions.
  · rintro x ⟨y, rfl⟩
    refine mem_iInter.2 fun n => ?_
    obtain ⟨s, sb, ys, hs⟩ : exists (s : Set γ), s in b ∧ y in s ∧ s subseteq ball y (u n / 2) := by
      apply hb.mem_nhds_iff.1
      exact ball_mem_nhds _ (half_pos (u_pos n))
    have diam_s : diam s <= u n := by
      apply (diam_mono hs isBounded_ball).trans
      convert! diam_ball (x := y) (half_pos (u_pos n)).le
      ring
    refine mem_iUnion.2 ⟨⟨s, sb⟩, ?_⟩
    refine mem_iUnion.2 ⟨⟨isBounded_ball.subset hs, diam_s⟩, ?_⟩
    apply mem_inter (subset_closure (mem_image_of_mem _ ys))
    refine mem_iInter.2 fun t => mem_iInter.2 fun ht => ⟨?_, ?_⟩
    · apply hq1
      exact mem_image_of_mem _ ys
    · apply disjoint_left.1 (hq2 ⟨(t, ⟨s, sb⟩), ht.symm⟩)
      exact mem_image_of_mem _ ys
  -- Now, let us prove the harder inclusion `⋂ F n ⊆ range f`.
  · intro x hx
    -- pick for each `n` a good set `s n` of small diameter for which `x ∈ E (s n)`.
    have C1 : forall n, exists (s : b) (_ : IsBounded s.1 ∧ diam s.1 <= u n), x in E s := fun n => by
      simpa only [F, mem_iUnion] using mem_iInter.1 hx n
    choose s hs hxs using C1
    have C2 : forall n, (s n).1.Nonempty := by
      intro n
      rw [nonempty_iff_ne_empty]
      grind
    -- choose a point `y n ∈ s n`.
    choose y hy using C2
    have I : forall m n, ((s m).1 inter (s n).1).Nonempty := by
      intro m n
      rw [← not_disjoint_iff_nonempty_inter]
      by_contra! h
      have A : x in q ⟨(s m, s n), h⟩ \ q ⟨(s n, s m), h.symm⟩ :=
        haveI := mem_iInter.1 (hxs m).2 (s n)
        (mem_iInter.1 this h :)
      have B : x in q ⟨(s n, s m), h.symm⟩ \ q ⟨(s m, s n), h⟩ :=
        haveI := mem_iInter.1 (hxs n).2 (s m)
        (mem_iInter.1 this h.symm :)
      exact A.2 B.1
    -- the points `y n` are nearby, and therefore they form a Cauchy sequence.
    have cauchy_y : CauchySeq y := by
      have : Tendsto (fun n => 2 * u n) atTop (𝓝 0) := by
        simpa only [mul_zero] using u_lim.const_mul 2
      refine cauchySeq_of_le_tendsto_0' (fun n => 2 * u n) (fun m n hmn => ?_) this
      rcases I m n with ⟨z, zsm, zsn⟩
      calc
        dist (y m) (y n) <= dist (y m) z + dist z (y n) := dist_triangle _ _ _
        _ <= u m + u n :=
          (add_le_add ((dist_le_diam_of_mem (hs m).1 (hy m) zsm).trans (hs m).2)
            ((dist_le_diam_of_mem (hs n).1 zsn (hy n)).trans (hs n).2))
        _ <= 2 * u m := by linarith [u_anti.antitone hmn]
    have : Nonempty γ := ⟨y 0⟩
    -- let `z` be its limit.
    let z := limUnder atTop y
    have y_lim : Tendsto y atTop (𝓝 z) := cauchy_y.tendsto_limUnder
    suffices f z = x by
      rw [← this]
      exact mem_range_self _
    -- assume for a contradiction that `f z ≠ x`.
    by_contra! hne
    -- introduce disjoint open sets `v` and `w` separating `f z` from `x`.
    obtain ⟨v, w, v_open, w_open, fzv, xw, hvw⟩ := t2_separation hne
    obtain ⟨δ, δpos, hδ⟩ : exists δ > (0 : Real), ball z δ subseteq f ⁻¹' v := by
      apply Metric.mem_nhds_iff.1
      exact f_cont.continuousAt.preimage_mem_nhds (v_open.mem_nhds fzv)
    obtain ⟨n, hn⟩ : exists n, u n + dist (y n) z < δ :=
      haveI : Tendsto (fun n => u n + dist (y n) z) atTop (𝓝 0) := by
        simpa only [add_zero] using u_lim.add (tendsto_iff_dist_tendsto_zero.1 y_lim)
      ((tendsto_order.1 this).2 _ δpos).exists
    -- for large enough `n`, the image of `s n` is contained in `v`, by continuity of `f`.
    have fsnv : f '' s n subseteq v := by
      rw [image_subset_iff]
      apply Subset.trans _ hδ
      intro a ha
      calc
        dist a z <= dist a (y n) + dist (y n) z := dist_triangle _ _ _
        _ <= u n + dist (y n) z := by grw [dist_le_diam_of_mem (hs n).1 ha (hy n), (hs n).2]
        _ < δ := hn
    -- as `x` belongs to the closure of `f '' (s n)`, it belongs to the closure of `v`.
    have : x in closure v := closure_mono fsnv (hxs n).1
    -- this is a contradiction, as `x` is supposed to belong to `w`, which is disjoint from
    -- the closure of `v`.
    exact disjoint_left.1 (hvw.closure_left w_open) this xw

/--
theorem `IsClosed.measurableSet_image_of_continuousOn_injOn` / 定理 `IsClosed.measurableSet_image_of_continuousOn_injOn`

English:
theorem IsClosed.measurableSet_image_of_continuousOn_injOn
  proof: by
  rw [image_eq_range]
  have : PolishSpace s := IsClosed.polishSpace hs
  apply measurableSet_range_of_continuous_injective
  · rwa [continuousOn_iff_continuous_domRestrict] at f_cont
  · rwa [injOn_iff_injective] at f_inj

中文:
定理 IsClosed.measurableSet_image_of_continuousOn_injOn
  证明: by
  rw [image_eq_range]
  have : PolishSpace s := IsClosed.polishSpace hs
  apply measurableSet_range_of_continuous_injective
  · rwa [continuousOn_iff_continuous_domRestrict] at f_cont
  · rwa [injOn_iff_injective] at f_inj

Depends on / 依赖: IsClosed, IsClosed.polishSpace, PolishSpace, continuousOn_iff_continuous_domRestrict, f_cont, f_inj, image_eq_range, injOn_iff_injective, measurableSet_range_of_continuous_injective, polishSpace
-/
theorem IsClosed.measurableSet_image_of_continuousOn_injOn
    [TopologicalSpace γ] [PolishSpace γ] {β : Type*} [TopologicalSpace β] [T2Space β]
    [MeasurableSpace β] [OpensMeasurableSpace β] {s : Set γ} (hs : IsClosed s) {f : γ -> β}
    (f_cont : ContinuousOn f s) (f_inj : InjOn f s) : MeasurableSet (f '' s) := by
  rw [image_eq_range]
  have : PolishSpace s := IsClosed.polishSpace hs
  apply measurableSet_range_of_continuous_injective
  · rwa [continuousOn_iff_continuous_domRestrict] at f_cont
  · rwa [injOn_iff_injective] at f_inj

variable {α β : Type*} [MeasurableSpace β]
section
variable [tβ : TopologicalSpace β] [T2Space β] [MeasurableSpace α] {s : Set γ} {f : γ -> β}

/--
theorem `MeasurableSet.image_of_continuousOn_injOn` / 定理 `MeasurableSet.image_of_continuousOn_injOn`

English:
theorem MeasurableSet.image_of_continuousOn_injOn
  statement: [OpensMeasurableSpace β]
  proof: by
  obtain ⟨t', t't, t'_polish, s_closed, _⟩ :
      exists t' : TopologicalSpace γ, t' <= tγ ∧ @PolishSpace γ t' ∧ IsClosed[t'] s ∧ IsOpen[t'] s :=
    hs.isClopenable
  exact
    @IsClosed.measurableSet_image_of_continuousOn_injOn γ t' t'_polish β _ _ _ _ s s_closed f
      (f_cont.mono_dom t't) 

中文:
定理 MeasurableSet.image_of_continuousOn_injOn
  结论: [OpensMeasurableSpace β]
  证明: by
  obtain ⟨t', t't, t'_polish, s_closed, _⟩ :
      exists t' : TopologicalSpace γ, t' <= tγ ∧ @PolishSpace γ t' ∧ IsClosed[t'] s ∧ IsOpen[t'] s :=
    hs.isClopenable
  exact
    @IsClosed.measurableSet_image_of_continuousOn_injOn γ t' t'_polish β _ _ _ _ s s_closed f
      (f_cont.mono_dom t't) 

Depends on / 依赖: IsClosed, IsClosed.measurableSet_image_of_continuousOn_injOn, IsOpen, PolishSpace, TopologicalSpace, _polish, f_cont, f_cont.mono_dom, f_inj, hs.isClopenable, isClopenable, measurableSet_image_of_continuousOn_injOn, mono_dom, s_closed
-/
theorem MeasurableSet.image_of_continuousOn_injOn [OpensMeasurableSpace β]
    [tγ : TopologicalSpace γ] [PolishSpace γ] [MeasurableSpace γ] [BorelSpace γ]
    (hs : MeasurableSet s)
    (f_cont : ContinuousOn f s) (f_inj : InjOn f s) : MeasurableSet (f '' s) := by
  obtain ⟨t', t't, t'_polish, s_closed, _⟩ :
      exists t' : TopologicalSpace γ, t' <= tγ ∧ @PolishSpace γ t' ∧ IsClosed[t'] s ∧ IsOpen[t'] s :=
    hs.isClopenable
  exact
    @IsClosed.measurableSet_image_of_continuousOn_injOn γ t' t'_polish β _ _ _ _ s s_closed f
      (f_cont.mono_dom t't) f_inj

/--
theorem `MeasurableSet.image_of_measurable_injOn` / 定理 `MeasurableSet.image_of_measurable_injOn`

English:
theorem MeasurableSet.image_of_measurable_injOn
  statement: {f : γ -> α}
  proof: by
  let := upgradeStandardBorel γ
  let tγ : TopologicalSpace γ := inferInstance
  rcases exists_opensMeasurableSpace_of_countablySeparated α with ⟨τ, _, _, _⟩
  -- for a finer Polish topology, `f` is continuous. Therefore, one may apply the corresponding
  -- result for continuous maps.
  obtain ⟨

中文:
定理 MeasurableSet.image_of_measurable_injOn
  结论: {f : γ -> α}
  证明: by
  let := upgradeStandardBorel γ
  let tγ : TopologicalSpace γ := inferInstance
  rcases exists_opensMeasurableSpace_of_countablySeparated α with ⟨τ, _, _, _⟩
  -- for a finer Polish topology, `f` is continuous. Therefore, one may apply the corresponding
  -- result for continuous maps.
  obtain ⟨

Depends on / 依赖: TopologicalSpace, exists_opensMeasurableSpace_of_countablySeparated, upgradeStandardBorel
-/
theorem MeasurableSet.image_of_measurable_injOn {f : γ -> α}
    [MeasurableSpace.CountablySeparated α]
    [MeasurableSpace γ] [StandardBorelSpace γ]
    (hs : MeasurableSet s) (f_meas : Measurable f) (f_inj : InjOn f s) :
    MeasurableSet (f '' s) := by
  let := upgradeStandardBorel γ
  let tγ : TopologicalSpace γ := inferInstance
  rcases exists_opensMeasurableSpace_of_countablySeparated α with ⟨τ, _, _, _⟩
  -- for a finer Polish topology, `f` is continuous. Therefore, one may apply the corresponding
  -- result for continuous maps.
  obtain ⟨t', t't, f_cont, t'_polish⟩ :
      exists t' : TopologicalSpace γ, t' <= tγ ∧ @Continuous γ _ t' _ f ∧ @PolishSpace γ t' :=
    f_meas.exists_continuous
have hs' := (borel_anti t't s) by rwa [← eq_borel_upgradeStandardBorel γ]
  let : MeasurableSpace γ := @borel γ t'
  let : BorelSpace γ := ⟨rfl⟩
  exact hs'.image_of_continuousOn_injOn f_cont.continuousOn f_inj

/--
theorem `Continuous.measurableEmbedding` / 定理 `Continuous.measurableEmbedding`

English:
theorem Continuous.measurableEmbedding
  statement: [BorelSpace β]
  proof: { injective := f_inj
    measurable := f_cont.measurable
    measurableSet_image' := fun _u hu =>
      hu.image_of_continuousOn_injOn f_cont.continuousOn f_inj.injOn }

中文:
定理 Continuous.measurableEmbedding
  结论: [BorelSpace β]
  证明: { injective := f_inj
    measurable := f_cont.measurable
    measurableSet_image' := fun _u hu =>
      hu.image_of_continuousOn_injOn f_cont.continuousOn f_inj.injOn }

Depends on / 依赖: continuousOn, f_cont, f_cont.continuousOn, f_cont.measurable, f_inj, f_inj.injOn, hu.image_of_continuousOn_injOn, image_of_continuousOn_injOn, injective, measurable, measurableSet_image
-/
theorem Continuous.measurableEmbedding [BorelSpace β]
    [TopologicalSpace γ] [PolishSpace γ] [MeasurableSpace γ] [BorelSpace γ]
    (f_cont : Continuous f) (f_inj : Injective f) :
    MeasurableEmbedding f :=
  { injective := f_inj
    measurable := f_cont.measurable
    measurableSet_image' := fun _u hu =>
      hu.image_of_continuousOn_injOn f_cont.continuousOn f_inj.injOn }

/--
theorem `ContinuousOn.measurableEmbedding` / 定理 `ContinuousOn.measurableEmbedding`

English:
theorem ContinuousOn.measurableEmbedding
  statement: [BorelSpace β]
  proof: { injective := injOn_iff_injective.1 f_inj
    measurable := (continuousOn_iff_continuous_domRestrict.1 f_cont).measurable
    measurableSet_image' := by
      intro u hu
      have A : MeasurableSet (((↑) : s -> γ) '' u) :=
        (MeasurableEmbedding.subtype_coe hs).measurableSet_image.2 hu
     

中文:
定理 ContinuousOn.measurableEmbedding
  结论: [BorelSpace β]
  证明: { injective := injOn_iff_injective.1 f_inj
    measurable := (continuousOn_iff_continuous_domRestrict.1 f_cont).measurable
    measurableSet_image' := by
      intro u hu
      have A : MeasurableSet (((↑) : s -> γ) '' u) :=
        (MeasurableEmbedding.subtype_coe hs).measurableSet_image.2 hu
     

Depends on / 依赖: A.image_of_continuousOn_injOn, MeasurableEmbedding, MeasurableEmbedding.subtype_coe, MeasurableSet, Subtype, Subtype.coe_image_subset, coe_image_subset, continuousOn_iff_continuous_domRestrict, f_cont, f_cont.mono, f_inj, f_inj.mono, image_comp, image_of_continuousOn_injOn, injOn_iff_injective, injective, measurable, measurableSet_image, subtype_coe
-/
theorem ContinuousOn.measurableEmbedding [BorelSpace β]
    [TopologicalSpace γ] [PolishSpace γ] [MeasurableSpace γ] [BorelSpace γ]
    (hs : MeasurableSet s) (f_cont : ContinuousOn f s)
    (f_inj : InjOn f s) : MeasurableEmbedding (s.domRestrict f) :=
  { injective := injOn_iff_injective.1 f_inj
    measurable := (continuousOn_iff_continuous_domRestrict.1 f_cont).measurable
    measurableSet_image' := by
      intro u hu
      have A : MeasurableSet (((↑) : s -> γ) '' u) :=
        (MeasurableEmbedding.subtype_coe hs).measurableSet_image.2 hu
      have B : MeasurableSet (f '' ((↑) : s -> γ) '' u) :=
        A.image_of_continuousOn_injOn (f_cont.mono (Subtype.coe_image_subset s u))
          (f_inj.mono (Subtype.coe_image_subset s u))
      rwa [← image_comp] at B }

/--
theorem `Measurable.measurableEmbedding` / 定理 `Measurable.measurableEmbedding`

English:
theorem Measurable.measurableEmbedding
  statement: {f : γ -> α}
  proof: { injective := f_inj
    measurable := f_meas
    measurableSet_image' := fun _u hu => hu.image_of_measurable_injOn f_meas f_inj.injOn }

中文:
定理 Measurable.measurableEmbedding
  结论: {f : γ -> α}
  证明: { injective := f_inj
    measurable := f_meas
    measurableSet_image' := fun _u hu => hu.image_of_measurable_injOn f_meas f_inj.injOn }

Depends on / 依赖: f_inj, f_inj.injOn, f_meas, hu.image_of_measurable_injOn, image_of_measurable_injOn, injective, measurable, measurableSet_image
-/
theorem Measurable.measurableEmbedding {f : γ -> α}
    [MeasurableSpace.CountablySeparated α]
    [MeasurableSpace γ] [StandardBorelSpace γ]
    (f_meas : Measurable f) (f_inj : Injective f) : MeasurableEmbedding f :=
  { injective := f_inj
    measurable := f_meas
    measurableSet_image' := fun _u hu => hu.image_of_measurable_injOn f_meas f_inj.injOn }

/--
theorem `MeasureTheory.borel_eq_borel_of_le` / 定理 `MeasureTheory.borel_eq_borel_of_le`

English:
theorem MeasureTheory.borel_eq_borel_of_le
  statement: {t t' : TopologicalSpace γ}
  proof: by
  refine le_antisymm ?_ (borel_anti hle)
  intro s hs
  have e := @Continuous.measurableEmbedding
    _ _ (@borel _ t') t' _ _ (@BorelSpace.mk _ _ (borel γ) rfl)
    t _ (@borel _ t) (@BorelSpace.mk _ t (@borel _ t) rfl) (continuous_id_of_le hle) injective_id
  convert! e.measurableSet_image.2 hs

中文:
定理 MeasureTheory.borel_eq_borel_of_le
  结论: {t t' : TopologicalSpace γ}
  证明: by
  refine le_antisymm ?_ (borel_anti hle)
  intro s hs
  have e := @Continuous.measurableEmbedding
    _ _ (@borel _ t') t' _ _ (@BorelSpace.mk _ _ (borel γ) rfl)
    t _ (@borel _ t) (@BorelSpace.mk _ t (@borel _ t) rfl) (continuous_id_of_le hle) injective_id
  convert! e.measurableSet_image.2 hs

Depends on / 依赖: PolishSpace
-/
theorem MeasureTheory.borel_eq_borel_of_le {t t' : TopologicalSpace γ}
    (ht : PolishSpace (h := t)) (ht' : PolishSpace (h := t')) (hle : t <= t') :
    @borel _ t = @borel _ t' := by
  refine le_antisymm ?_ (borel_anti hle)
  intro s hs
  have e := @Continuous.measurableEmbedding
    _ _ (@borel _ t') t' _ _ (@BorelSpace.mk _ _ (borel γ) rfl)
    t _ (@borel _ t) (@BorelSpace.mk _ t (@borel _ t) rfl) (continuous_id_of_le hle) injective_id
  convert! e.measurableSet_image.2 hs
  simp only [id_eq, image_id']

/--
theorem `MeasureTheory.isClopenable_iff_measurableSet` / 定理 `MeasureTheory.isClopenable_iff_measurableSet`

English:
theorem MeasureTheory.isClopenable_iff_measurableSet
  proof: by
  -- we already know that a measurable set is clopenable. Conversely, assume that `s` is clopenable.
  refine ⟨fun hs => ?_, fun hs => hs.isClopenable⟩
  borelize γ
  -- consider a finer topology `t'` in which `s` is open and closed.
  obtain ⟨t', t't, t'_polish, _, s_open⟩ :
    exists t' : Topo

中文:
定理 MeasureTheory.isClopenable_iff_measurableSet
  证明: by
  -- we already know that a measurable set is clopenable. Conversely, assume that `s` is clopenable.
  refine ⟨fun hs => ?_, fun hs => hs.isClopenable⟩
  borelize γ
  -- consider a finer topology `t'` in which `s` is open and closed.
  obtain ⟨t', t't, t'_polish, _, s_open⟩ :
    exists t' : Topo
-/
theorem MeasureTheory.isClopenable_iff_measurableSet
    [tγ : TopologicalSpace γ] [PolishSpace γ] [MeasurableSpace γ] [BorelSpace γ] :
    IsClopenable s ↔ MeasurableSet s := by
  -- we already know that a measurable set is clopenable. Conversely, assume that `s` is clopenable.
  refine ⟨fun hs => ?_, fun hs => hs.isClopenable⟩
  borelize γ
  -- consider a finer topology `t'` in which `s` is open and closed.
  obtain ⟨t', t't, t'_polish, _, s_open⟩ :
    exists t' : TopologicalSpace γ, t' <= tγ ∧ @PolishSpace γ t' ∧ IsClosed[t'] s ∧ IsOpen[t'] s := hs
  rw [← borel_eq_borel_of_le t'_polish _ t't]
  · exact MeasurableSpace.measurableSet_generateFrom s_open
  infer_instance

end

section LinearOrder

variable {α β : Type*} {t : Set α} {g : α -> β}
  [TopologicalSpace α] [MeasurableSpace α] [BorelSpace α] [LinearOrder α] [OrderTopology α]
  [PolishSpace α]
  [TopologicalSpace β] [MeasurableSpace β] [BorelSpace β] [LinearOrder β] [OrderTopology β]

/--
theorem `MeasurableSet.image_of_monotoneOn_of_continuousOn` / 定理 `MeasurableSet.image_of_monotoneOn_of_continuousOn`

English:
theorem MeasurableSet.image_of_monotoneOn_of_continuousOn
  proof: by
  /- We use that the image of a measurable set by a continuous injective map is measurable.
  Therefore, we need to remove the points where the map is not injective. There are only countably
  many points that have several preimages, so this set is also measurable. -/
  let u : Set β := {c | exis

中文:
定理 MeasurableSet.image_of_monotoneOn_of_continuousOn
  证明: by
  /- We use that the image of a measurable set by a continuous injective map is measurable.
  Therefore, we need to remove the points where the map is not injective. There are only countably
  many points that have several preimages, so this set is also measurable. -/
  let u : Set β := {c | exis
-/
theorem MeasurableSet.image_of_monotoneOn_of_continuousOn
    (ht : MeasurableSet t) (hg : MonotoneOn g t) (h'g : ContinuousOn g t) :
    MeasurableSet (g '' t) := by
  /- We use that the image of a measurable set by a continuous injective map is measurable.
  Therefore, we need to remove the points where the map is not injective. There are only countably
  many points that have several preimages, so this set is also measurable. -/
  let u : Set β := {c | exists x, exists y, x in t ∧ y in t ∧ x < y ∧ g x = c ∧ g y = c}
  have hu : Set.Countable u := MonotoneOn.countable_setOfPred_two_preimages hg
  let t' := t inter g ⁻¹' u
  have ht' : MeasurableSet t' := by
    have : t' = ⋃ c in u, t inter g ⁻¹' {c} := by ext; simp [t']
    rw [this]
    apply MeasurableSet.biUnion hu (fun c hc => ?_)
    obtain ⟨v, hv, tv⟩ : exists v, OrdConnected v ∧ t inter g ⁻¹' {c} = t inter v :=
      ordConnected_singleton.preimage_monotoneOn hg
    exact tv ▸ ht.inter hv.measurableSet
  have : g '' t = g '' (t \ t') union g '' t' := by simp [← image_union, t']
  rw [this]
  apply MeasurableSet.union
  · apply (ht.diff ht').image_of_continuousOn_injOn (h'g.mono sdiff_subset)
    intro x hx y hy hxy
    contrapose! hxy
    wlog! H : x < y generalizing x y with h
    · have : y < x := lt_of_le_of_ne H hxy.symm
      exact (h hy hx hxy.symm this).symm
    intro h
    exact hx.2 ⟨hx.1, x, y, hx.1, hy.1, H, rfl, h.symm⟩
.measurableSet · exact hu.mono (by simp [t'])

/--
theorem `MeasurableSet.image_of_monotoneOn` / 定理 `MeasurableSet.image_of_monotoneOn`

English:
theorem MeasurableSet.image_of_monotoneOn
  statement: [SecondCountableTopology β]
  proof: by
  /- Since there are only countably many discontinuity points, the result follows by reduction to
  the continuous case, which we have already proved. -/
  let t' := {x in t | ¬ ContinuousWithinAt g t x}
  have ht' : Set.Countable t' := hg.countable_not_continuousWithinAt
  have : g '' t = g '' (

中文:
定理 MeasurableSet.image_of_monotoneOn
  结论: [SecondCountableTopology β]
  证明: by
  /- Since there are only countably many discontinuity points, the result follows by reduction to
  the continuous case, which we have already proved. -/
  let t' := {x in t | ¬ ContinuousWithinAt g t x}
  have ht' : Set.Countable t' := hg.countable_not_continuousWithinAt
  have : g '' t = g '' (
-/
theorem MeasurableSet.image_of_monotoneOn [SecondCountableTopology β]
    (ht : MeasurableSet t) (hg : MonotoneOn g t) : MeasurableSet (g '' t) := by
  /- Since there are only countably many discontinuity points, the result follows by reduction to
  the continuous case, which we have already proved. -/
  let t' := {x in t | ¬ ContinuousWithinAt g t x}
  have ht' : Set.Countable t' := hg.countable_not_continuousWithinAt
  have : g '' t = g '' (t \ t') union g '' t' := by
    rw [← image_union]
    congr!
    ext
    simp only [sdiff_sep_self, not_not, mem_union, mem_ofPred_eq, t']
    tauto
  rw [this]
  apply MeasurableSet.union _ (ht'.image g).measurableSet
  apply MeasurableSet.image_of_monotoneOn_of_continuousOn (ht.diff ht'.measurableSet)
    (hg.mono sdiff_subset)
  intro x hx
  simp only [sdiff_sep_self, not_not, mem_ofPred_eq, t'] at hx
  exact hx.2.mono sdiff_subset

/--
theorem `MeasurableSet.image_of_antitoneOn` / 定理 `MeasurableSet.image_of_antitoneOn`

English:
theorem MeasurableSet.image_of_antitoneOn
  statement: [SecondCountableTopology β]
  proof: (ht.image_of_monotoneOn hg.dual_right :)

中文:
定理 MeasurableSet.image_of_antitoneOn
  结论: [SecondCountableTopology β]
  证明: (ht.image_of_monotoneOn hg.dual_right :)

Depends on / 依赖: dual_right, hg.dual_right, ht.image_of_monotoneOn, image_of_monotoneOn
-/
theorem MeasurableSet.image_of_antitoneOn [SecondCountableTopology β]
    (ht : MeasurableSet t) (hg : AntitoneOn g t) : MeasurableSet (g '' t) :=
  (ht.image_of_monotoneOn hg.dual_right :)

end LinearOrder

/-- The set of points for which a sequence of measurable functions converges to a given function
is measurable. -/
@[measurability]
/--
lemma `MeasureTheory.measurableSet_tendsto_fun` / 引理 `MeasureTheory.measurableSet_tendsto_fun`

English:
lemma MeasureTheory.measurableSet_tendsto_fun
  statement: [MeasurableSpace γ] [Countable ι]
  proof: by
  let := TopologicalSpace.pseudoMetrizableSpacePseudoMetric γ
  simp_rw [tendsto_iff_dist_tendsto_zero (f := fun n => f n _)]
  exact measurableSet_tendsto (𝓝 0) (fun n => (hf n).dist hg)

中文:
引理 MeasureTheory.measurableSet_tendsto_fun
  结论: [MeasurableSpace γ] [Countable ι]
  证明: by
  let := TopologicalSpace.pseudoMetrizableSpacePseudoMetric γ
  simp_rw [tendsto_iff_dist_tendsto_zero (f := fun n => f n _)]
  exact measurableSet_tendsto (𝓝 0) (fun n => (hf n).dist hg)

Depends on / 依赖: TopologicalSpace, TopologicalSpace.pseudoMetrizableSpacePseudoMetric, measurableSet_tendsto, pseudoMetrizableSpacePseudoMetric, simp_rw, tendsto_iff_dist_tendsto_zero
-/
lemma MeasureTheory.measurableSet_tendsto_fun [MeasurableSpace γ] [Countable ι]
    {l : Filter ι} [l.IsCountablyGenerated]
    [TopologicalSpace γ] [SecondCountableTopology γ] [PseudoMetrizableSpace γ]
    [OpensMeasurableSpace γ]
    {f : ι -> β -> γ} (hf : forall i, Measurable (f i)) {g : β -> γ} (hg : Measurable g) :
    MeasurableSet { x | Tendsto (fun n => f n x) l (𝓝 (g x)) } := by
  let := TopologicalSpace.pseudoMetrizableSpacePseudoMetric γ
  simp_rw [tendsto_iff_dist_tendsto_zero (f := fun n => f n _)]
  exact measurableSet_tendsto (𝓝 0) (fun n => (hf n).dist hg)

/-- The set of points for which a measurable sequence of functions converges is measurable. -/
@[measurability]
/--
theorem `MeasureTheory.measurableSet_exists_tendsto` / 定理 `MeasureTheory.measurableSet_exists_tendsto`

English:
theorem MeasureTheory.measurableSet_exists_tendsto
  statement: [TopologicalSpace γ]
  proof: by
  rcases l.eq_or_neBot with rfl | hl
  · simp
  let := TopologicalSpace.upgradeIsCompletelyPseudoMetrizable γ
  rcases l.exists_antitone_basis with ⟨u, hu⟩
  simp_rw [← cauchy_map_iff_exists_tendsto]
  change MeasurableSet { x | _ ∧ _ }
  have : forall x, (map (f · x) l ×ˢ map (f · x) l).HasAntit

中文:
定理 MeasureTheory.measurableSet_exists_tendsto
  结论: [TopologicalSpace γ]
  证明: by
  rcases l.eq_or_neBot with rfl | hl
  · simp
  let := TopologicalSpace.upgradeIsCompletelyPseudoMetrizable γ
  rcases l.exists_antitone_basis with ⟨u, hu⟩
  simp_rw [← cauchy_map_iff_exists_tendsto]
  change MeasurableSet { x | _ ∧ _ }
  have : forall x, (map (f · x) l ×ˢ map (f · x) l).HasAntit

Depends on / 依赖: Filter, Filter.HasBasis.le_basis_iff, HasAntitoneBasis, HasBasis, MeasurableSet, Metric, Metric.uniformity_basis_dist_inv_nat, TopologicalSpace, TopologicalSpace.upgradeIsCompletelyPseudoMetrizable, and_iff_right, cauchy_map_iff_exists_tendsto, eq_or_neBot, exists_antitone_basis, hl.map, hu.map, l.eq_or_neBot, l.exists_antitone_basis, le_basis_iff, simp_rw, toHasBasis
-/
theorem MeasureTheory.measurableSet_exists_tendsto [TopologicalSpace γ]
    [IsCompletelyPseudoMetrizableSpace γ] [SecondCountableTopology γ] [MeasurableSpace γ]
    [hγ : OpensMeasurableSpace γ] [Countable ι] {l : Filter ι}
    [l.IsCountablyGenerated] {f : ι -> β -> γ} (hf : forall i, Measurable (f i)) :
    MeasurableSet { x | exists c, Tendsto (fun n => f n x) l (𝓝 c) } := by
  rcases l.eq_or_neBot with rfl | hl
  · simp
  let := TopologicalSpace.upgradeIsCompletelyPseudoMetrizable γ
  rcases l.exists_antitone_basis with ⟨u, hu⟩
  simp_rw [← cauchy_map_iff_exists_tendsto]
  change MeasurableSet { x | _ ∧ _ }
  have : forall x, (map (f · x) l ×ˢ map (f · x) l).HasAntitoneBasis fun n =>
      ((f · x) '' u n) ×ˢ ((f · x) '' u n) := fun x => (hu.map _).prod (hu.map _)
  simp_rw [and_iff_right (hl.map _),
    Filter.HasBasis.le_basis_iff (this _).toHasBasis Metric.uniformity_basis_dist_inv_nat_succ,
    Set.ofPred_forall]
  refine MeasurableSet.biInter Set.countable_univ fun K _ => ?_
  simp_rw [Set.ofPred_exists, true_and]
  refine MeasurableSet.iUnion fun N => ?_
  simp_rw [prod_image_image_eq, image_subset_iff, prod_subset_iff, Set.ofPred_forall]
  exact
    MeasurableSet.biInter (to_countable (u N)) fun i _ =>
      MeasurableSet.biInter (to_countable (u N)) fun j _ =>
        measurableSet_lt (Measurable.dist (hf i) (hf j)) measurable_const

section Measurable

variable {X E ι : Type*} [MeasurableSpace X] [CommMonoid E] [TopologicalSpace E]

section

variable [IsCompletelyPseudoMetrizableSpace E] [SecondCountableTopology E]
  [MeasurableSpace E] [BorelSpace E] [MeasurableMul₂ E]
  [Countable ι] {L : SummationFilter ι} [L.NeBot] [L.filter.IsCountablyGenerated]

/-- The product of measurable functions is measurable. -/
@[to_additive (attr := fun_prop)
/-- The sum of measurable functions is measurable. -/]
/--
theorem `Measurable.tprod` / 定理 `Measurable.tprod`

English:
theorem Measurable.tprod
  given: {f : ι -> X -> E} (h : forall i : ι, Measurable (f i))
  proof: by
  let E := { x | Multipliable (f · x) L }
  have hE : MeasurableSet E := measurableSet_exists_tendsto (by fun_prop)
  have h0 : (Eᶜ.domRestrict fun x => ∏'[L] i, f i x) = fun _ => 1 :=
    funext fun ⟨x, hx⟩ => tprod_eq_one_of_not_multipliable hx
  refine measurable_of_restrict_of_restrict_compl 

中文:
定理 Measurable.tprod
  条件: {f : ι -> X -> E} (h : 对任意 i : ι, Measurable (f i))
  证明: by
  let E := { x | Multipliable (f · x) L }
  have hE : MeasurableSet E := measurableSet_exists_tendsto (by fun_prop)
  have h0 : (Eᶜ.domRestrict fun x => ∏'[L] i, f i x) = fun _ => 1 :=
    funext fun ⟨x, hx⟩ => tprod_eq_one_of_not_multipliable hx
  refine measurable_of_restrict_of_restrict_compl 

Depends on / 依赖: L.filter, MeasurableSet, Multipliable, domRestrict, filter, fun_prop, hasProd, measurableSet_exists_tendsto, measurable_const, measurable_of_restrict_of_restrict_compl, measurable_of_tendsto_metrizable, tendsto_pi_nhds, tendsto_pi_nhds.mpr, tprod_eq_one_of_not_multipliable
-/
theorem Measurable.tprod {f : ι -> X -> E} (h : forall i : ι, Measurable (f i)) :
    Measurable (fun x => ∏'[L] i : ι, f i x) := by
  let E := { x | Multipliable (f · x) L }
  have hE : MeasurableSet E := measurableSet_exists_tendsto (by fun_prop)
  have h0 : (Eᶜ.domRestrict fun x => ∏'[L] i, f i x) = fun _ => 1 :=
    funext fun ⟨x, hx⟩ => tprod_eq_one_of_not_multipliable hx
  refine measurable_of_restrict_of_restrict_compl hE ?_ (h0 ▸ measurable_const)
  refine measurable_of_tendsto_metrizable' L.filter ?_ (tendsto_pi_nhds.mpr fun e => e.2.hasProd)
  fun_prop

/-- The product of almost everywhere measurable functions is measurable. -/
@[to_additive (attr := fun_prop)
/-- The sum of almost everywhere measurable functions is measurable. -/]
/--
theorem `AEMeasurable.tprod` / 定理 `AEMeasurable.tprod`

English:
theorem AEMeasurable.tprod
  statement: {μ : MeasureTheory.Measure X} {f : ι -> X -> E}
  proof: by
  choose g hg_meas hg_eq_f using h
  use (fun x => ∏'[L] i, g i x), Measurable.tprod hg_meas
  filter_upwards [ae_all_iff.mpr hg_eq_f] with x h_eq using tprod_congr h_eq

中文:
定理 AEMeasurable.tprod
  结论: {μ : MeasureTheory.Measure X} {f : ι -> X -> E}
  证明: by
  choose g hg_meas hg_eq_f using h
  use (fun x => ∏'[L] i, g i x), Measurable.tprod hg_meas
  filter_upwards [ae_all_iff.mpr hg_eq_f] with x h_eq using tprod_congr h_eq

Depends on / 依赖: Measurable, Measurable.tprod, ae_all_iff, ae_all_iff.mpr, filter_upwards, h_eq, hg_eq_f, hg_meas, tprod_congr
-/
theorem AEMeasurable.tprod {μ : MeasureTheory.Measure X} {f : ι -> X -> E}
    (h : forall i : ι, AEMeasurable (f i) μ) : AEMeasurable (fun x => ∏'[L] i : ι, f i x) μ := by
  choose g hg_meas hg_eq_f using h
  use (fun x => ∏'[L] i, g i x), Measurable.tprod hg_meas
  filter_upwards [ae_all_iff.mpr hg_eq_f] with x h_eq using tprod_congr h_eq

end

section

variable [PseudoMetrizableSpace E] [MeasurableSpace E] [BorelSpace E] [MeasurableMul₂ E]
  {L : SummationFilter ι} [L.NeBot] [L.filter.IsCountablyGenerated]

/-- The product of measurable functions is measurable. -/
@[to_additive (attr := fun_prop)
/-- The sum of measurable functions is measurable. -/]
/--
theorem `Measurable.tprod'` / 定理 `Measurable.tprod'`

English:
theorem Measurable.tprod'
  given: {f : ι -> X -> E} (h : forall i : ι, Measurable (f i))
  proof: by
  rw [tprod_def]; rw [finprod_def']
  split_ifs with hm
  any_goals exact measurable_one
  · refine Finset.measurable_prod_apply (fun _ _ => ?_) measurable_id
    rw [Set.mulIndicator]
    split_ifs <;> fun_prop
  · exact measurable_of_tendsto_metrizable' L.filter (by fun_prop) hm.choose_spec

中文:
定理 Measurable.tprod'
  条件: {f : ι -> X -> E} (h : 对任意 i : ι, Measurable (f i))
  证明: by
  rw [tprod_def]; rw [finprod_def']
  split_ifs with hm
  any_goals exact measurable_one
  · refine Finset.measurable_prod_apply (fun _ _ => ?_) measurable_id
    rw [Set.mulIndicator]
    split_ifs <;> fun_prop
  · exact measurable_of_tendsto_metrizable' L.filter (by fun_prop) hm.choose_spec

Depends on / 依赖: Finset, Finset.measurable_prod_apply, L.filter, Set.mulIndicator, any_goals, choose_spec, filter, finprod_def, fun_prop, hm.choose_spec, measurable_id, measurable_of_tendsto_metrizable, measurable_one, measurable_prod_apply, mulIndicator, split_ifs, tprod_def
-/
theorem Measurable.tprod' {f : ι -> X -> E} (h : forall i : ι, Measurable (f i)) :
    Measurable (∏'[L] i : ι, f i) := by
  rw [tprod_def]; rw [finprod_def']
  split_ifs with hm
  any_goals exact measurable_one
  · refine Finset.measurable_prod_apply (fun _ _ => ?_) measurable_id
    rw [Set.mulIndicator]
    split_ifs <;> fun_prop
  · exact measurable_of_tendsto_metrizable' L.filter (by fun_prop) hm.choose_spec

/-- The product of almost everywhere measurable functions is measurable. -/
@[to_additive (attr := fun_prop)
/-- The sum of almost everywhere measurable functions is measurable. -/]
/--
theorem `AEMeasurable.tprod'` / 定理 `AEMeasurable.tprod'`

English:
theorem AEMeasurable.tprod'
  statement: {μ : MeasureTheory.Measure X} {f : ι -> X -> E}
  proof: by
  rw [tprod_def]; rw [finprod_def']
  split_ifs with hm
  any_goals exact aemeasurable_one
  · refine Finset.aemeasurable_prod _ (fun _ _ => ?_)
    rw [Set.mulIndicator]
    split_ifs <;> fun_prop
  · apply aemeasurable_of_tendsto_metrizable_ae L.filter (f := fun s => ∏ i in s, f i)
    · fun_pr

中文:
定理 AEMeasurable.tprod'
  结论: {μ : MeasureTheory.Measure X} {f : ι -> X -> E}
  证明: by
  rw [tprod_def]; rw [finprod_def']
  split_ifs with hm
  any_goals exact aemeasurable_one
  · refine Finset.aemeasurable_prod _ (fun _ _ => ?_)
    rw [Set.mulIndicator]
    split_ifs <;> fun_prop
  · apply aemeasurable_of_tendsto_metrizable_ae L.filter (f := fun s => ∏ i in s, f i)
    · fun_pr

Depends on / 依赖: Finset, Finset.aemeasurable_prod, L.filter, Set.mulIndicator, aemeasurable_of_tendsto_metrizable_ae, aemeasurable_one, aemeasurable_prod, any_goals, apply_nhds, choose_spec, filter, finprod_def, fun_prop, hm.choose_spec.apply_nhds, mulIndicator, of_forall, split_ifs, tprod_def
-/
theorem AEMeasurable.tprod' {μ : MeasureTheory.Measure X} {f : ι -> X -> E}
    (h : forall i : ι, AEMeasurable (f i) μ) : AEMeasurable (∏'[L] i : ι, f i) μ := by
  rw [tprod_def]; rw [finprod_def']
  split_ifs with hm
  any_goals exact aemeasurable_one
  · refine Finset.aemeasurable_prod _ (fun _ _ => ?_)
    rw [Set.mulIndicator]
    split_ifs <;> fun_prop
  · apply aemeasurable_of_tendsto_metrizable_ae L.filter (f := fun s => ∏ i in s, f i)
    · fun_prop
    · exact .of_forall fun x => hm.choose_spec.apply_nhds x

end

end Measurable

section StandardBorelSpace

variable [MeasurableSpace α] [StandardBorelSpace α]

/--
theorem `MeasurableSet.isClopenable'` / 定理 `MeasurableSet.isClopenable'`

English:
theorem MeasurableSet.isClopenable'
  given: {s : Set α} (hs : MeasurableSet s)
  proof: by
  let := upgradeStandardBorel α
  obtain ⟨t, hle, ht, s_clopen⟩ := hs.isClopenable
  refine ⟨t, ?_, ht, s_clopen⟩
  constructor
  rw [eq_borel_upgradeStandardBorel α]; rw [borel_eq_borel_of_le ht _ hle]
  infer_instance

中文:
定理 MeasurableSet.isClopenable'
  条件: {s : Set α} (hs : MeasurableSet s)
  证明: by
  let := upgradeStandardBorel α
  obtain ⟨t, hle, ht, s_clopen⟩ := hs.isClopenable
  refine ⟨t, ?_, ht, s_clopen⟩
  constructor
  rw [eq_borel_upgradeStandardBorel α]; rw [borel_eq_borel_of_le ht _ hle]
  infer_instance

Depends on / 依赖: borel_eq_borel_of_le, eq_borel_upgradeStandardBorel, hs.isClopenable, infer_instance, isClopenable, s_clopen, upgradeStandardBorel
-/
theorem MeasurableSet.isClopenable' {s : Set α} (hs : MeasurableSet s) :
    exists _ : TopologicalSpace α, BorelSpace α ∧ PolishSpace α ∧ IsClosed s ∧ IsOpen s := by
  let := upgradeStandardBorel α
  obtain ⟨t, hle, ht, s_clopen⟩ := hs.isClopenable
  refine ⟨t, ?_, ht, s_clopen⟩
  constructor
  rw [eq_borel_upgradeStandardBorel α]; rw [borel_eq_borel_of_le ht _ hle]
  infer_instance

/--
theorem `MeasurableSet.standardBorel` / 定理 `MeasurableSet.standardBorel`

English:
theorem MeasurableSet.standardBorel
  given: {s : Set α} (hs : MeasurableSet s)
  proof: by
  obtain ⟨_, _, _, s_closed, _⟩ := hs.isClopenable'
  have := s_closed.polishSpace
  infer_instance

中文:
定理 MeasurableSet.standardBorel
  条件: {s : Set α} (hs : MeasurableSet s)
  证明: by
  obtain ⟨_, _, _, s_closed, _⟩ := hs.isClopenable'
  have := s_closed.polishSpace
  infer_instance

Depends on / 依赖: hs.isClopenable, infer_instance, isClopenable, polishSpace, s_closed, s_closed.polishSpace
-/
theorem MeasurableSet.standardBorel {s : Set α} (hs : MeasurableSet s) :
    StandardBorelSpace s := by
  obtain ⟨_, _, _, s_closed, _⟩ := hs.isClopenable'
  have := s_closed.polishSpace
  infer_instance

end StandardBorelSpace

/-! ### The Borel Isomorphism Theorem -/

namespace PolishSpace

variable {β : Type*}
variable [MeasurableSpace α] [MeasurableSpace β] [StandardBorelSpace α] [StandardBorelSpace β]

/--
Definition of `borelSchroederBernstein` / `borelSchroederBernstein` 的定义

English:
definition borelSchroederBernstein
  signature: {f : α -> β} {g : β -> α} (fmeas : Measurable f)
  body: letI := upgradeStandardBorel α
  letI := upgradeStandardBorel β
  (fmeas.measurableEmbedding finj).schroederBernstein (gmeas.measurableEmbedding ginj)

中文:
定义 borelSchroederBernstein
  签名: {f : α -> β} {g : β -> α} (fmeas : Measurable f)
  定义体: letI := upgradeStandardBorel α
  letI := upgradeStandardBorel β
  (fmeas.measurableEmbedding finj).schroederBernstein (gmeas.measurableEmbedding ginj)

Depends on / 依赖: fmeas.measurableEmbedding, gmeas.measurableEmbedding, measurableEmbedding, schroederBernstein, upgradeStandardBorel
-/
noncomputable def borelSchroederBernstein {f : α -> β} {g : β -> α} (fmeas : Measurable f)
    (finj : Function.Injective f) (gmeas : Measurable g) (ginj : Function.Injective g) : α ≃ᵐ β :=
  letI := upgradeStandardBorel α
  letI := upgradeStandardBorel β
  (fmeas.measurableEmbedding finj).schroederBernstein (gmeas.measurableEmbedding ginj)

/--
Definition of `measurableEquivNatBoolOfNotCountable` / `measurableEquivNatBoolOfNotCountable` 的定义

English:
definition measurableEquivNatBoolOfNotCountable
  signature: (h : ¬Countable α)
  body: by
  apply Nonempty.some
  let := upgradeStandardBorel α
  obtain ⟨f, -, fcts, finj⟩ :=
    isClosed_univ.exists_nat_bool_injection_of_not_countable (α := α)
      (by rwa [← countable_coe_iff, (Equiv.Set.univ _).countable_iff])
  obtain ⟨g, gmeas, ginj⟩ :=
    MeasurableSpace.measurable_injection_n

中文:
定义 measurableEquivNatBoolOfNotCountable
  签名: (h : ¬Countable α)
  定义体: by
  apply Nonempty.some
  let := upgradeStandardBorel α
  obtain ⟨f, -, fcts, finj⟩ :=
    isClosed_univ.exists_nat_bool_injection_of_not_countable (α := α)
      (by rwa [← countable_coe_iff, (Equiv.Set.univ _).countable_iff])
  obtain ⟨g, gmeas, ginj⟩ :=
    MeasurableSpace.measurable_injection_n

Depends on / 依赖: Equiv.Set.univ, MeasurableSpace, MeasurableSpace.measurable_injection_nat_bool_of_countablySeparated, Nonempty, Nonempty.some, borelSchroederBernstein, countable_coe_iff, countable_iff, exists_nat_bool_injection_of_not_countable, fcts.measurable, isClosed_univ, isClosed_univ.exists_nat_bool_injection_of_not_countable, measurable, measurable_injection_nat_bool_of_countablySeparated, upgradeStandardBorel
-/
noncomputable def measurableEquivNatBoolOfNotCountable (h : ¬Countable α) : α ≃ᵐ (Nat -> Bool) := by
  apply Nonempty.some
  let := upgradeStandardBorel α
  obtain ⟨f, -, fcts, finj⟩ :=
    isClosed_univ.exists_nat_bool_injection_of_not_countable (α := α)
      (by rwa [← countable_coe_iff, (Equiv.Set.univ _).countable_iff])
  obtain ⟨g, gmeas, ginj⟩ :=
    MeasurableSpace.measurable_injection_nat_bool_of_countablySeparated α
  exact ⟨borelSchroederBernstein gmeas ginj fcts.measurable finj⟩

/--
Definition of `measurableEquivOfNotCountable` / `measurableEquivOfNotCountable` 的定义

English:
definition measurableEquivOfNotCountable
  signature: (hα : ¬Countable α) (hβ : ¬Countable β)
  body: (measurableEquivNatBoolOfNotCountable hα).trans (measurableEquivNatBoolOfNotCountable hβ).symm

中文:
定义 measurableEquivOfNotCountable
  签名: (hα : ¬Countable α) (hβ : ¬Countable β)
  定义体: (measurableEquivNatBoolOfNotCountable hα).trans (measurableEquivNatBoolOfNotCountable hβ).symm

Depends on / 依赖: measurableEquivNatBoolOfNotCountable
-/
noncomputable def measurableEquivOfNotCountable (hα : ¬Countable α) (hβ : ¬Countable β) : α ≃ᵐ β :=
  (measurableEquivNatBoolOfNotCountable hα).trans (measurableEquivNatBoolOfNotCountable hβ).symm

/--
Definition of `Equiv.measurableEquiv` / `Equiv.measurableEquiv` 的定义

English:
definition Equiv.measurableEquiv
  signature: (e : α ≃ β)
  body: by
  by_cases h : Countable α
  · letI := Countable.of_equiv α e
    refine ⟨e, ?_, ?_⟩ <;> apply measurable_of_countable
  refine measurableEquivOfNotCountable h ?_
  rwa [e.countable_iff] at h

中文:
定义 Equiv.measurableEquiv
  签名: (e : α ≃ β)
  定义体: by
  by_cases h : Countable α
  · letI := Countable.of_equiv α e
    refine ⟨e, ?_, ?_⟩ <;> apply measurable_of_countable
  refine measurableEquivOfNotCountable h ?_
  rwa [e.countable_iff] at h

Depends on / 依赖: Countable, Countable.of_equiv, countable_iff, e.countable_iff, measurableEquivOfNotCountable, measurable_of_countable, of_equiv
-/
noncomputable def Equiv.measurableEquiv (e : α ≃ β) : α ≃ᵐ β := by
  by_cases h : Countable α
  · letI := Countable.of_equiv α e
    refine ⟨e, ?_, ?_⟩ <;> apply measurable_of_countable
  refine measurableEquivOfNotCountable h ?_
  rwa [e.countable_iff] at h

end PolishSpace
