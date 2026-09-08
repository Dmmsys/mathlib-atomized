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
/-
**StandardBorelSpace** 是 Mathlib 中的一个类，位于命名空间 ``。
形式化陈述：StandardBorelSpace [MeasurableSpace α] : Prop where /-- There exists a com
patible Polish topology. -/ polish : exists _ : TopologicalSpace α, BorelSpace α
 ∧ PolishSpace α  /-- A convenience class similar to `UpgradedPolishSpace`. No i
nstance should be registered. Instead one should use `letI
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A standard Borel space is a measurable space arising as the Borel sets of some P
olish topology.
This is useful in situations where a space has no natural topology or
the natural topology in a space is non-Polish.

To endow a standard Borel space `α` with a compatible Polish topology, use
`letI := upgradeStandardBorel α`. One can then use `eq_borel_upgradeStandardBore
l α` to
rewrite the `MeasurableSpace α` instance to `borel α t`, where `t` is the new to
pology. -/
-/
class StandardBorelSpace [MeasurableSpace α] : Prop where
  /-- There exists a compatible Polish topology. -/
  polish : ∃ _ : TopologicalSpace α, BorelSpace α ∧ PolishSpace α

/-- A convenience class similar to `UpgradedPolishSpace`. No instance should be registered.
Instead one should use `letI := upgradeStandardBorel α`. -/
/-
**UpgradedStandardBorel** 是 Mathlib 中的一个类，位于命名空间 ``。
形式化陈述：UpgradedStandardBorel extends MeasurableSpace α, TopologicalSpace α, Borel
Space α, PolishSpace α  /-- Use as `letI
继承自：MeasurableSpace α, TopologicalSpace α, BorelSpace α, PolishSpace α  /-- Use 
as `letI。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A convenience class similar to `UpgradedPolishSpace`. No instance should be regi
stered.
Instead one should use `letI := upgradeStandardBorel α`. -/ -/
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
/-
**upgradeStandardBorel** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：upgradeStandardBorel [MeasurableSpace α] [h : StandardBorelSpace α] : Upgr
adedStandardBorel α
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `StandardBorelSpace.polish`：∀ {α : Type u_1} {inst : MeasurableSpace α} [
self : StandardBorelSpace α], ∃ x, BorelSpace α ∧ PolishSpace α
-/
def upgradeStandardBorel [MeasurableSpace α] [h : StandardBorelSpace α] :
    UpgradedStandardBorel α := by
  choose τ hb hp using h.polish
  constructor

/-- The `MeasurableSpace α` instance on a `StandardBorelSpace` `α` is equal to
the Borel sets of `upgradeStandardBorel α`. -/
/-
**eq_borel_upgradeStandardBorel** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：eq_borel_upgradeStandardBorel [MeasurableSpace α] [StandardBorelSpace α] :
 ‹MeasurableSpace α› = @borel _ (upgradeStandardBorel α).toTopologicalSpace
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `BorelSpace.measurable_eq`：∀ {α : Type u_6} {inst : TopologicalSpace α} {
inst_1 : MeasurableSpace α} [self : BorelSpace α], inst_1 = borel α
· 使用定理 `UpgradedStandardBorel.toBorelSpace`：∀ {α : Type u_1} [self : UpgradedSta
ndardBorel α], BorelSpace α

--- 原说明 ---
The `MeasurableSpace α` instance on a `StandardBorelSpace` `α` is equal to
the Borel sets of `upgradeStandardBorel α`.
-/
theorem eq_borel_upgradeStandardBorel [MeasurableSpace α] [StandardBorelSpace α] :
    ‹MeasurableSpace α› = @borel _ (upgradeStandardBorel α).toTopologicalSpace :=
  @BorelSpace.measurable_eq _ (upgradeStandardBorel α).toTopologicalSpace _
    (upgradeStandardBorel α).toBorelSpace

variable {α}

section

variable [MeasurableSpace α]

-- See note [lower instance priority]
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 100) standardBorel_of_polish [τ : TopologicalSpace α]
    [BorelSpace α] [PolishSpace α] : StandardBorelSpace α := by exists τ

-- See note [lower instance priority]
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 100) standardBorelSpace_of_discreteMeasurableSpace [DiscreteMeasurableSpace α]
    [Countable α] : StandardBorelSpace α :=
  let _ : TopologicalSpace α := ⊥
  have : DiscreteTopology α := ⟨rfl⟩
  inferInstance

-- See note [lower instance priority]
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 100) countablyGenerated_of_standardBorel [StandardBorelSpace α] :
    MeasurableSpace.CountablyGenerated α :=
  letI := upgradeStandardBorel α
  inferInstance

-- See note [lower instance priority]
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 100) measurableSingleton_of_standardBorel [StandardBorelSpace α] :
    MeasurableSingletonClass α :=
  letI := upgradeStandardBorel α
  inferInstance

namespace StandardBorelSpace

variable {β : Type*} [MeasurableSpace β]

section instances

/-- A product of two standard Borel spaces is standard Borel. -/
/-
**StandardBorelSpace.prod** 是 Mathlib 中的一个实例，位于命名空间 `StandardBorelSpace`。
形式化陈述：prod [StandardBorelSpace α] [StandardBorelSpace β] : StandardBorelSpace (α
 × β)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `standardBorel_of_polish`：∀ {α : Type u_1} [inst : MeasurableSpace α] [τ 
: TopologicalSpace α] [BorelSpace α] [PolishSpace α],   StandardBorelSpace α
· 使用定理 `UpgradedStandardBorel.toBorelSpace`：∀ {α : Type u_1} [self : UpgradedSta
ndardBorel α], BorelSpace α
· 使用定理 `secondCountableTopologyEither_of_right`：∀ (α : Type u_6) (β : Type u_7) 
[inst : TopologicalSpace α] [inst_1 : TopologicalSpace β] [SecondCountableTopolo
gy β],   SecondCountableTopo…
· 使用定理 `PolishSpace.toSecondCountableTopology`：∀ {α : Type u_3} {h : Topological
Space α} [self : PolishSpace α], SecondCountableTopology α
· 使用定理 `UpgradedStandardBorel.toPolishSpace`：∀ {α : Type u_1} [self : UpgradedSt
andardBorel α], PolishSpace α
· 使用定理 `instPolishSpaceOfSeparableSpaceOfIsCompletelyMetrizableSpace`：∀ {α : Typ
e u_1} [inst : TopologicalSpace α] [TopologicalSpace.SeparableSpace α]   [Topolo
gicalSpace.IsCompletelyMetrizableSpace α], PolishS…
· 使用定理 `TopologicalSpace.instSeparableSpaceProd`：∀ {α : Type u} {β : Type u_1} [
t : TopologicalSpace α] [inst : TopologicalSpace β] [TopologicalSpace.SeparableS
pace α]   [TopologicalSpace.S…
· 使用定理 `TopologicalSpace.SecondCountableTopology.to_separableSpace`：∀ {α : Type 
u} [t : TopologicalSpace α] [SecondCountableTopology α], TopologicalSpace.Separa
bleSpace α
· 使用定理 `PolishSpace.toIsCompletelyMetrizableSpace`：∀ {α : Type u_3} {h : Topolog
icalSpace α} [self : PolishSpace α], TopologicalSpace.IsCompletelyMetrizableSpac
e α

--- 原说明 ---
A product of two standard Borel spaces is standard Borel.
-/
instance prod [StandardBorelSpace α] [StandardBorelSpace β] : StandardBorelSpace (α × β) :=
  letI := upgradeStandardBorel α
  letI := upgradeStandardBorel β
  inferInstance

/-- A product of countably many standard Borel spaces is standard Borel. -/
/-
**StandardBorelSpace.pi_countable** 是 Mathlib 中的一个实例，位于命名空间 `StandardBorelSpace`
。
形式化陈述：pi_countable {ι : Type*} [Countable ι] {α : ι -> Type*} [forall n, Measura
bleSpace (α n)] [forall n, StandardBorelSpace (α n)] : StandardBorelSpace (foral
l n, α n)
参数：α n；α n。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `standardBorel_of_polish`：∀ {α : Type u_1} [inst : MeasurableSpace α] [τ 
: TopologicalSpace α] [BorelSpace α] [PolishSpace α],   StandardBorelSpace α
· 使用定理 `PolishSpace.toSecondCountableTopology`：∀ {α : Type u_3} {h : Topological
Space α} [self : PolishSpace α], SecondCountableTopology α
· 使用定理 `UpgradedStandardBorel.toPolishSpace`：∀ {α : Type u_1} [self : UpgradedSt
andardBorel α], PolishSpace α
· 使用定理 `UpgradedStandardBorel.toBorelSpace`：∀ {α : Type u_1} [self : UpgradedSta
ndardBorel α], BorelSpace α
· 使用定理 `instPolishSpaceOfSeparableSpaceOfIsCompletelyMetrizableSpace`：∀ {α : Typ
e u_1} [inst : TopologicalSpace α] [TopologicalSpace.SeparableSpace α]   [Topolo
gicalSpace.IsCompletelyMetrizableSpace α], PolishS…
· 使用定理 `TopologicalSpace.instSeparableSpaceForallOfCountable`：∀ {ι : Type u_2} {
X : ι → Type u_3} [inst : (i : ι) → TopologicalSpace (X i)]   [∀ (i : ι), Topolo
gicalSpace.SeparableSpace (X i)] [Countabl…
· 使用定理 `TopologicalSpace.SecondCountableTopology.to_separableSpace`：∀ {α : Type 
u} [t : TopologicalSpace α] [SecondCountableTopology α], TopologicalSpace.Separa
bleSpace α
· 使用定理 `PolishSpace.toIsCompletelyMetrizableSpace`：∀ {α : Type u_3} {h : Topolog
icalSpace α} [self : PolishSpace α], TopologicalSpace.IsCompletelyMetrizableSpac
e α

--- 原说明 ---
A product of countably many standard Borel spaces is standard Borel.
-/
instance pi_countable {ι : Type*} [Countable ι] {α : ι → Type*} [∀ n, MeasurableSpace (α n)]
    [∀ n, StandardBorelSpace (α n)] : StandardBorelSpace (∀ n, α n) :=
  letI := fun n => upgradeStandardBorel (α n)
  inferInstance
/-
**StandardBorelSpace.** 是 Mathlib 中的一个实例，位于命名空间 `StandardBorelSpace`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
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
  s = ∅ ∨ ∃ f : (ℕ → ℕ) → α, Continuous f ∧ range f = s

/-
**MeasureTheory.analyticSet_empty** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：analyticSet_empty : AnalyticSet (∅ : Set α)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.AnalyticSet_def`：∀ {α : Type u_3} [inst : TopologicalSpace
 α] (s : Set α),   MeasureTheory.AnalyticSet s = (s = ∅ ∨ ∃ f, Continuous f ∧ Se
t.range f = s)
-/
theorem analyticSet_empty : AnalyticSet (∅ : Set α) := by
  rw [AnalyticSet]
  exact Or.inl rfl
/-
**MeasureTheory.analyticSet_range_of_polishSpace** 是 Mathlib 中的一个定理，位于命名空间 `Meas
ureTheory`。
形式化陈述：analyticSet_range_of_polishSpace {β : Type*} [TopologicalSpace β] [PolishS
pace β] {f : β -> α} (f_cont : Continuous f) : AnalyticSet (range f)
参数：f_cont : Continuous f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `isEmpty_or_nonempty`：isEmpty_or_nonempty : IsEmpty α ∨ Nonempty α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.range_eq_empty`：range_eq_empty [IsEmpty ι] (f : ι -> α) : range f = 
∅
· 使用定理 `MeasureTheory.analyticSet_empty`：analyticSet_empty : AnalyticSet (∅ : Se
t α)
· 使用定理 `MeasureTheory.AnalyticSet_def`：∀ {α : Type u_3} [inst : TopologicalSpace
 α] (s : Set α),   MeasureTheory.AnalyticSet s = (s = ∅ ∨ ∃ f, Continuous f ∧ Se
t.range f = s)
· 使用定理 `PolishSpace.exists_nat_nat_continuous_surjective`：exists_nat_nat_continu
ous_surjective (α : Type*) [TopologicalSpace α] [PolishSpace α] [Nonempty α] : e
xists f : (Nat -> Nat) -> α, Continuou…
· 使用定理 `Continuous.comp`：Continuous.comp {g : Y -> Z} (hg : Continuous g) (hf : 
Continuous f) : Continuous (g ∘ f)
· 使用定理 `Function.Surjective.range_comp`：∀ {α : Type u_1} {ι : Sort u_3} {ι' : So
rt u_4} {f : ι → ι'},   Function.Surjective f → ∀ (g : ι' → α), Set.range (g ∘ f
) = Set.range g
-/
theorem analyticSet_range_of_polishSpace {β : Type*} [TopologicalSpace β] [PolishSpace β]
    {f : β → α} (f_cont : Continuous f) : AnalyticSet (range f) := by
  cases isEmpty_or_nonempty β
  · rw [range_eq_empty]
    exact analyticSet_empty
  · rw [AnalyticSet]
    obtain ⟨g, g_cont, hg⟩ : ∃ g : (ℕ → ℕ) → β, Continuous g ∧ Surjective g :=
      exists_nat_nat_continuous_surjective β
    refine Or.inr ⟨f ∘ g, f_cont.comp g_cont, ?_⟩
    rw [hg.range_comp]

/-- The image of an open set under a continuous map is analytic. -/
/-
**MeasureTheory._root_.IsOpen.analyticSet_image** 是 Mathlib 中的一个定理，位于命名空间 `Measu
reTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The image of an open set under a continuous map is analytic.
-/
theorem _root_.IsOpen.analyticSet_image {β : Type*} [TopologicalSpace β] [PolishSpace β]
    {s : Set β} (hs : IsOpen s) {f : β → α} (f_cont : Continuous f) : AnalyticSet (f '' s) := by
  rw [image_eq_range]
  have : PolishSpace s := hs.polishSpace
  exact analyticSet_range_of_polishSpace (f_cont.comp continuous_subtype_val)

/-- A set is analytic if and only if it is the continuous image of some Polish space. -/
/-
**MeasureTheory.analyticSet_iff_exists_polishSpace_range** 是 Mathlib 中的一个定理，位于命名
空间 `MeasureTheory`。
形式化陈述：analyticSet_iff_exists_polishSpace_range {s : Set α} : AnalyticSet s ↔ exi
sts (β : Type) (h : TopologicalSpace β) (_ : @PolishSpace β h) (f : β -> α), @Co
ntinuous _ _ h _ f ∧ range f = s
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.AnalyticSet_def`：∀ {α : Type u_3} [inst : TopologicalSpace
 α] (s : Set α),   MeasureTheory.AnalyticSet s = (s = ∅ ∨ ∃ f, Continuous f ∧ Se
t.range f = s)
· 使用定理 `instPolishSpaceOfSeparableSpaceOfIsCompletelyMetrizableSpace`：∀ {α : Typ
e u_1} [inst : TopologicalSpace α] [TopologicalSpace.SeparableSpace α]   [Topolo
gicalSpace.IsCompletelyMetrizableSpace α], PolishS…
· 使用定理 `TopologicalSpace.SecondCountableTopology.to_separableSpace`：∀ {α : Type 
u} [t : TopologicalSpace α] [SecondCountableTopology α], TopologicalSpace.Separa
bleSpace α
· 使用定理 `TopologicalSpace.instSecondCountableTopologyOfLindelofSpaceOfPseudoMetri
zableSpace`：∀ (X : Type u_5) [inst : TopologicalSpace X] [LindelofSpace X] [Topo
logicalSpace.PseudoMetrizableSpace X],   SecondCountableTopology X
· 使用定理 `Countable.LindelofSpace`：∀ {X : Type u} [inst : TopologicalSpace X] [Cou
ntable X], LindelofSpace X
· 使用定理 `Encodable.countable`：∀ {α : Type u_1} [Encodable α], Countable α
· 使用定理 `PseudoEMetricSpace.pseudoMetrizableSpace`：∀ {α : Type u_2} [inst : Pseud
oEMetricSpace α], TopologicalSpace.PseudoMetrizableSpace α
· 使用定理 `TopologicalSpace.IsCompletelyMetrizableSpace.of_completeSpace_metrizable
`：∀ {X : Type u_1} [inst : UniformSpace X] [CompleteSpace X] [(uniformity X).IsC
ountablyGenerated] [T0Space X],   TopologicalSpace.IsCompletel…
· 使用定理 `DiscreteUniformity.instCompleteSpace`：∀ {α : Type u} [uniformSpace : Uni
formSpace α] [DiscreteUniformity α], CompleteSpace α
· 使用定理 `DiscreteUniformity.instOfFiniteOfDiscreteTopology`：∀ {Y : Type u_2} [Fin
ite Y] [inst : UniformSpace Y] [DiscreteTopology Y], DiscreteUniformity Y
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `instDiscreteTopologyEmpty`：DiscreteTopology Empty
· 使用定理 `EMetric.instIsCountablyGeneratedUniformity`：∀ {α : Type u} [inst : Pseud
oEMetricSpace α], (uniformity α).IsCountablyGenerated
· 使用定理 `T6Space.toT0Space`：∀ {X : Type u} {inst : TopologicalSpace X} [self : T6
Space X], T0Space X
· 使用定理 `instT6SpaceOfMetrizableSpace`：∀ {X : Type u_1} [inst : TopologicalSpace 
X] [TopologicalSpace.MetrizableSpace X], T6Space X
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α
· 使用定理 `continuous_bot`：continuous_bot {t : TopologicalSpace β} : Continuous[⊥, 
t] f
· 使用定理 `Set.range_eq_empty`：range_eq_empty [IsEmpty ι] (f : ι -> α) : range f = 
∅
· 使用定理 `TopologicalSpace.instSeparableSpaceForallOfCountable`：∀ {ι : Type u_2} {
X : ι → Type u_3} [inst : (i : ι) → TopologicalSpace (X i)]   [∀ (i : ι), Topolo
gicalSpace.SeparableSpace (X i)] [Countabl…
· 使用定理 `instCountableNat`：Countable ℕ
· 使用定理 `DiscreteUniformity.inst`：∀ (X : Type u_1), DiscreteUniformity X
· 使用定理 `instIsCountablyGeneratedProdForallUniformityOfCountable`：∀ {ι : Type u_1
} {α : ι → Type u} [U : (i : ι) → UniformSpace (α i)] [Countable ι]   [∀ (i : ι)
, (uniformity (α i)).IsCountablyGenerated], (…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.analyticSet_range_of_polishSpace`：analyticSet_range_of_pol
ishSpace {β : Type*} [TopologicalSpace β] [PolishSpace β] {f : β -> α} (f_cont :
 Continuous f) : AnalyticSet (range …

--- 原说明 ---
A set is analytic if and only if it is the continuous image of some Polish space
.
-/
theorem analyticSet_iff_exists_polishSpace_range {s : Set α} :
    AnalyticSet s ↔
      ∃ (β : Type) (h : TopologicalSpace β) (_ : @PolishSpace β h) (f : β → α),
        @Continuous _ _ h _ f ∧ range f = s := by
  constructor
  · intro h
    rw [AnalyticSet] at h
    rcases h with h | h
    · refine ⟨Empty, inferInstance, inferInstance, Empty.elim, continuous_bot, ?_⟩
      rw [h]
      exact range_eq_empty _
    · exact ⟨ℕ → ℕ, inferInstance, inferInstance, h⟩
  · rintro ⟨β, h, h', f, f_cont, f_range⟩
    rw [← f_range]
    exact analyticSet_range_of_polishSpace f_cont

/-- The continuous image of an analytic set is analytic -/
/-
**MeasureTheory.AnalyticSet.image_of_continuousOn** 是 Mathlib 中的一个定理，位于命名空间 `Mea
sureTheory.AnalyticSet`。
形式化陈述：∀ {α : Type u_1} [inst : TopologicalSpace α] {β : Type u_3} [inst_1 : Topo
logicalSpace β] {s : Set α},   MeasureTheory.AnalyticSet s → ∀ {f : α → β}, Cont
inuousOn f s → MeasureTheory.AnalyticSet (f '' s)
参数：f '' s。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `MeasureTheory.analyticSet_iff_exists_polishSpace_range`：analyticSet_iff_
exists_polishSpace_range {s : Set α} : AnalyticSet s ↔ exists (β : Type) (h : To
pologicalSpace β) (_ : @PolishSpace β h) (f …
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.range_comp`：range_comp (g : α -> β) (f : ι -> α) : range (g ∘ f) = g
 '' range f
· 使用定理 `MeasureTheory.analyticSet_range_of_polishSpace`：analyticSet_range_of_pol
ishSpace {β : Type*} [TopologicalSpace β] [PolishSpace β] {f : β -> α} (f_cont :
 Continuous f) : AnalyticSet (range …
· 使用定理 `ContinuousOn.comp_continuous`：ContinuousOn.comp_continuous {g : β -> γ} 
{f : α -> β} {s : Set β} (hg : ContinuousOn g s) (hf : Continuous f) (hs : foral
l x, f x in s) : C…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.mem_range_self`：∀ {α : Type u} {ι : Sort u_1} {f : ι → α} (i : ι), f
 i ∈ Set.range f

--- 原说明 ---
The continuous image of an analytic set is analytic
-/
theorem AnalyticSet.image_of_continuousOn {β : Type*} [TopologicalSpace β] {s : Set α}
    (hs : AnalyticSet s) {f : α → β} (hf : ContinuousOn f s) : AnalyticSet (f '' s) := by
  rcases analyticSet_iff_exists_polishSpace_range.1 hs with ⟨γ, γtop, γpolish, g, g_cont, gs⟩
  have : f '' s = range (f ∘ g) := by rw [range_comp, gs]
  rw [this]
  apply analyticSet_range_of_polishSpace
  apply hf.comp_continuous g_cont fun x => _
  rw [← gs]
  exact mem_range_self
/-
**MeasureTheory.AnalyticSet.image_of_continuous** 是 Mathlib 中的一个定理，位于命名空间 `Measu
reTheory.AnalyticSet`。
形式化陈述：∀ {α : Type u_1} [inst : TopologicalSpace α] {β : Type u_3} [inst_1 : Topo
logicalSpace β] {s : Set α},   MeasureTheory.AnalyticSet s → ∀ {f : α → β}, Cont
inuous f → MeasureTheory.AnalyticSet (f '' s)
参数：f '' s。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.AnalyticSet.image_of_continuousOn`：∀ {α : Type u_1} [inst 
: TopologicalSpace α] {β : Type u_3} [inst_1 : TopologicalSpace β] {s : Set α}, 
  MeasureTheory.AnalyticSet s → ∀ {f …
· 使用定理 `Continuous.continuousOn`：Continuous.continuousOn (h : Continuous f) : Co
ntinuousOn f s
-/
theorem AnalyticSet.image_of_continuous {β : Type*} [TopologicalSpace β] {s : Set α}
    (hs : AnalyticSet s) {f : α → β} (hf : Continuous f) : AnalyticSet (f '' s) :=
  hs.image_of_continuousOn hf.continuousOn

/-- A countable intersection of analytic sets is analytic. -/
/-
**MeasureTheory.AnalyticSet.iInter** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.Anal
yticSet`。
形式化陈述：∀ {α : Type u_1} {ι : Type u_2} [inst : TopologicalSpace α] [hι : Nonempty
 ι] [Countable ι] [T2Space α] {s : ι → Set α},   (∀ (n : ι), MeasureTheory.Analy
ticSet (s n)) → MeasureTheory.AnalyticSet (⋂ n, s n)
参数：∀ (n : ι), MeasureTheory.AnalyticSet (s n)；⋂ n, s n。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `isClosed_iInter`：isClosed_iInter {f : ι -> Set X} (h : forall i, IsClose
d (f i)) : IsClosed (⋂ i, f i)
· 使用定理 `isClosed_eq`：isClosed_eq [T2Space X] {f g : Y -> X} (hf : Continuous f) 
(hg : Continuous g) : IsClosed { y : Y | f y = g y }
· 使用定理 `Continuous.comp`：Continuous.comp {g : Y -> Z} (hg : Continuous g) (hf : 
Continuous f) : Continuous (g ∘ f)
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `continuous_apply`：continuous_apply (a : α) : Continuous (fun f : (α → X)
 ↦ f a)
· 使用定理 `IsClosed.polishSpace`：∀ {α : Type u_1} [inst : TopologicalSpace α] [Poli
shSpace α] {s : Set α}, IsClosed s → PolishSpace ↑s
· 使用定理 `instPolishSpaceOfSeparableSpaceOfIsCompletelyMetrizableSpace`：∀ {α : Typ
e u_1} [inst : TopologicalSpace α] [TopologicalSpace.SeparableSpace α]   [Topolo
gicalSpace.IsCompletelyMetrizableSpace α], PolishS…
· 使用定理 `TopologicalSpace.instSeparableSpaceForallOfCountable`：∀ {ι : Type u_2} {
X : ι → Type u_3} [inst : (i : ι) → TopologicalSpace (X i)]   [∀ (i : ι), Topolo
gicalSpace.SeparableSpace (X i)] [Countabl…
· 使用定理 `TopologicalSpace.SecondCountableTopology.to_separableSpace`：∀ {α : Type 
u} [t : TopologicalSpace α] [SecondCountableTopology α], TopologicalSpace.Separa
bleSpace α
· 使用定理 `PolishSpace.toSecondCountableTopology`：∀ {α : Type u_3} {h : Topological
Space α} [self : PolishSpace α], SecondCountableTopology α
· 使用定理 `PolishSpace.toIsCompletelyMetrizableSpace`：∀ {α : Type u_3} {h : Topolog
icalSpace α} [self : PolishSpace α], TopologicalSpace.IsCompletelyMetrizableSpac
e α
· 使用定理 `continuous_subtype_val`：continuous_subtype_val : Continuous (@Subtype.va
l X p)
· 使用定理 `Set.Subset.antisymm`：∀ {α : Type u} {a b : Set α}, a ⊆ b → b ⊆ a → a = b
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.mem_iInter`：mem_iInter {x : α} {s : ι -> Set α} : (x in ⋂ i, s i) ↔ 
forall i, x in s i
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Set.mem_range_self`：∀ {α : Type u} {ι : Sort u_1} {f : ι → α} (i : ι), f
 i ∈ Set.range f
· 使用定理 `Set.mem_range`：∀ {α : Type u} {ι : Sort u_1} {f : ι → α} {x : α}, x ∈ Se
t.range f ↔ ∃ y, f y = x
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Classical.choose_spec`：∀ {α : Sort u} {p : α → Prop} (h : ∃ x, p x), p (
Classical.choose h)
· 使用定理 `MeasureTheory.analyticSet_range_of_polishSpace`：analyticSet_range_of_pol
ishSpace {β : Type*} [TopologicalSpace β] [PolishSpace β] {f : β -> α} (f_cont :
 Continuous f) : AnalyticSet (range …
· 使用定理 `MeasureTheory.analyticSet_iff_exists_polishSpace_range`：analyticSet_iff_
exists_polishSpace_range {s : Set α} : AnalyticSet s ↔ exists (β : Type) (h : To
pologicalSpace β) (_ : @PolishSpace β h) (f …

--- 原说明 ---
A countable intersection of analytic sets is analytic.
-/
theorem AnalyticSet.iInter [hι : Nonempty ι] [Countable ι] [T2Space α] {s : ι → Set α}
    (hs : ∀ n, AnalyticSet (s n)) : AnalyticSet (⋂ n, s n) := by
  rcases hι with ⟨i₀⟩
  /- For the proof, write each `s n` as the continuous image under a map `f n` of a
    Polish space `β n`. The product space `γ = Π n, β n` is also Polish, and so is the subset
    `t` of sequences `x n` for which `f n (x n)` is independent of `n`. The set `t` is Polish, and
    the range of `x ↦ f 0 (x 0)` on `t` is exactly `⋂ n, s n`, so this set is analytic. -/
  choose β hβ h'β f f_cont f_range using fun n =>
    analyticSet_iff_exists_polishSpace_range.1 (hs n)
  let γ := ∀ n, β n
  let t : Set γ := ⋂ n, { x | f n (x n) = f i₀ (x i₀) }
  have t_closed : IsClosed t := by
    apply isClosed_iInter
    intro n
    exact
      isClosed_eq ((f_cont n).comp (continuous_apply n)) ((f_cont i₀).comp (continuous_apply i₀))
  have : PolishSpace t := t_closed.polishSpace
  let F : t → α := fun x => f i₀ ((x : γ) i₀)
  have F_cont : Continuous F := (f_cont i₀).comp ((continuous_apply i₀).comp continuous_subtype_val)
  have F_range : range F = ⋂ n : ι, s n := by
    apply Subset.antisymm
    · rintro y ⟨x, rfl⟩
      refine mem_iInter.2 fun n => ?_
      have : f n ((x : γ) n) = F x := (mem_iInter.1 x.2 n :)
      rw [← this, ← f_range n]
      exact mem_range_self _
    · intro y hy
      have A : ∀ n, ∃ x : β n, f n x = y := by
        intro n
        rw [← mem_range, f_range n]
        exact mem_iInter.1 hy n
      choose x hx using A
      have xt : x ∈ t := by
        refine mem_iInter.2 fun n => ?_
        simp [γ, hx]
      refine ⟨⟨x, xt⟩, ?_⟩
      exact hx i₀
  rw [← F_range]
  exact analyticSet_range_of_polishSpace F_cont

/-- A countable union of analytic sets is analytic. -/
/-
**MeasureTheory.AnalyticSet.iUnion** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.Anal
yticSet`。
形式化陈述：∀ {α : Type u_1} {ι : Type u_2} [inst : TopologicalSpace α] [Countable ι] 
{s : ι → Set α},   (∀ (n : ι), MeasureTheory.AnalyticSet (s n)) → MeasureTheory.
AnalyticSet (⋃ n, s n)
参数：∀ (n : ι), MeasureTheory.AnalyticSet (s n)；⋃ n, s n。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `continuous_sigma`：continuous_sigma {f : Sigma σ -> X} (hf : forall i, Co
ntinuous fun a => f ⟨i, a⟩) : Continuous f
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.range_sigma_eq_iUnion_range`：range_sigma_eq_iUnion_range {γ : α -> T
ype*} (f : Sigma γ -> β) : range f = ⋃ a, range fun b => f ⟨a, b⟩
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.analyticSet_range_of_polishSpace`：analyticSet_range_of_pol
ishSpace {β : Type*} [TopologicalSpace β] [PolishSpace β] {f : β -> α} (f_cont :
 Continuous f) : AnalyticSet (range …
· 使用定理 `instPolishSpaceOfSeparableSpaceOfIsCompletelyMetrizableSpace`：∀ {α : Typ
e u_1} [inst : TopologicalSpace α] [TopologicalSpace.SeparableSpace α]   [Topolo
gicalSpace.IsCompletelyMetrizableSpace α], PolishS…
· 使用定理 `TopologicalSpace.SecondCountableTopology.to_separableSpace`：∀ {α : Type 
u} [t : TopologicalSpace α] [SecondCountableTopology α], TopologicalSpace.Separa
bleSpace α
· 使用定理 `TopologicalSpace.instSecondCountableTopologySigmaOfCountable`：∀ {ι : Typ
e u_1} {E : ι → Type u_2} [inst : (i : ι) → TopologicalSpace (E i)] [Countable ι
]   [∀ (i : ι), SecondCountableTopology (E i)], Se…
· 使用定理 `PolishSpace.toSecondCountableTopology`：∀ {α : Type u_3} {h : Topological
Space α} [self : PolishSpace α], SecondCountableTopology α
· 使用定理 `PolishSpace.toIsCompletelyMetrizableSpace`：∀ {α : Type u_3} {h : Topolog
icalSpace α} [self : PolishSpace α], TopologicalSpace.IsCompletelyMetrizableSpac
e α
· 使用定理 `Classical.choose_spec`：∀ {α : Sort u} {p : α → Prop} (h : ∃ x, p x), p (
Classical.choose h)
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `MeasureTheory.analyticSet_iff_exists_polishSpace_range`：analyticSet_iff_
exists_polishSpace_range {s : Set α} : AnalyticSet s ↔ exists (β : Type) (h : To
pologicalSpace β) (_ : @PolishSpace β h) (f …

--- 原说明 ---
A countable union of analytic sets is analytic.
-/
theorem AnalyticSet.iUnion [Countable ι] {s : ι → Set α} (hs : ∀ n, AnalyticSet (s n)) :
    AnalyticSet (⋃ n, s n) := by
  /- For the proof, write each `s n` as the continuous image under a map `f n` of a
    Polish space `β n`. The union space `γ = Σ n, β n` is also Polish, and the map `F : γ → α` which
    coincides with `f n` on `β n` sends it to `⋃ n, s n`. -/
  choose β hβ h'β f f_cont f_range using fun n =>
    analyticSet_iff_exists_polishSpace_range.1 (hs n)
  let γ := Σ n, β n
  let F : γ → α := fun ⟨n, x⟩ ↦ f n x
  have F_cont : Continuous F := continuous_sigma f_cont
  have F_range : range F = ⋃ n, s n := by
    simp only [γ, F, range_sigma_eq_iUnion_range, f_range]
  rw [← F_range]
  exact analyticSet_range_of_polishSpace F_cont
/-
**MeasureTheory._root_.IsClosed.analyticSet** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTh
eory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.IsClosed.analyticSet [PolishSpace α] {s : Set α} (hs : IsClosed s) :
    AnalyticSet s := by
  have : PolishSpace s := hs.polishSpace
  rw [← @Subtype.range_val α s]
  exact analyticSet_range_of_polishSpace continuous_subtype_val

/-- Given a Borel-measurable set in a Polish space, there exists a finer Polish topology making
it clopen. This is in fact an equivalence, see `isClopenable_iff_measurableSet`. -/
/-
**MeasureTheory._root_.MeasurableSet.isClopenable** 是 Mathlib 中的一个定理，位于命名空间 `Mea
sureTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given a Borel-measurable set in a Polish space, there exists a finer Polish topo
logy making
it clopen. This is in fact an equivalence, see `isClopenable_iff_measurableSet`.
-/
theorem _root_.MeasurableSet.isClopenable [PolishSpace α] [MeasurableSpace α] [BorelSpace α]
    {s : Set α} (hs : MeasurableSet s) : IsClopenable s := by
  revert s
  apply MeasurableSet.induction_on_open
  · exact fun u hu => hu.isClopenable
  · exact fun u _ h'u => h'u.compl
  · exact fun f _ _ hf => IsClopenable.iUnion hf

/-- A Borel-measurable set in a Polish space is analytic. -/
/-
**MeasureTheory._root_.MeasurableSet.analyticSet** 是 Mathlib 中的一个定理，位于命名空间 `Meas
ureTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A Borel-measurable set in a Polish space is analytic.
-/
theorem _root_.MeasurableSet.analyticSet {α : Type*} [t : TopologicalSpace α] [PolishSpace α]
    [MeasurableSpace α] [BorelSpace α] {s : Set α} (hs : MeasurableSet s) : AnalyticSet s := by
  /- For a short proof (avoiding measurable induction), one sees `s` as a closed set for a finer
    topology `t'`. It is analytic for this topology. As the identity from `t'` to `t` is continuous
    and the image of an analytic set is analytic, it follows that `s` is also analytic for `t`. -/
  obtain ⟨t', t't, t'_polish, s_closed, _⟩ :
      ∃ t' : TopologicalSpace α, t' ≤ t ∧ @PolishSpace α t' ∧ IsClosed[t'] s ∧ IsOpen[t'] s :=
    hs.isClopenable
  have A := @IsClosed.analyticSet α t' t'_polish s s_closed
  convert! @AnalyticSet.image_of_continuous α t' α t s A id (continuous_id_of_le t't)
  simp only [id, image_id']

/-- Given a Borel-measurable function from a Polish space to a second-countable space, there exists
a finer Polish topology on the source space for which the function is continuous. -/
/-
**MeasureTheory._root_.Measurable.exists_continuous** 是 Mathlib 中的一个定理，位于命名空间 `M
easureTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given a Borel-measurable function from a Polish space to a second-countable spac
e, there exists
a finer Polish topology on the source space for which the function is continuous
.
-/
theorem _root_.Measurable.exists_continuous {α β : Type*} [t : TopologicalSpace α] [PolishSpace α]
    [MeasurableSpace α] [BorelSpace α] [tβ : TopologicalSpace β] [MeasurableSpace β]
    [OpensMeasurableSpace β] {f : α → β} [SecondCountableTopology (range f)] (hf : Measurable f) :
    ∃ t' : TopologicalSpace α, t' ≤ t ∧ @Continuous α β t' tβ f ∧ @PolishSpace α t' := by
  obtain ⟨b, b_count, -, hb⟩ :
      ∃ b : Set (Set (range f)), b.Countable ∧ ∅ ∉ b ∧ IsTopologicalBasis b :=
    exists_countable_basis (range f)
  have : Countable b := b_count.to_subtype
  have : ∀ s : b, IsClopenable (rangeFactorization f ⁻¹' s) := fun s ↦ by
    apply MeasurableSet.isClopenable
    exact hf.subtype_mk (hb.isOpen s.2).measurableSet
  choose T Tt Tpolish _ Topen using this
  obtain ⟨t', t'T, t't, t'_polish⟩ :
      ∃ t' : TopologicalSpace α, (∀ i, t' ≤ T i) ∧ t' ≤ t ∧ @PolishSpace α t' :=
    exists_polishSpace_forall_le (t := t) T Tt Tpolish
  refine ⟨t', t't, ?_, t'_polish⟩
  have : Continuous[t', _] (rangeFactorization f) :=
    hb.continuous_iff.2 fun s hs => t'T ⟨s, hs⟩ _ (Topen ⟨s, hs⟩)
  exact continuous_subtype_val.comp this

/-- The image of a measurable set in a standard Borel space under a measurable map
is an analytic set. -/
/-
**MeasureTheory._root_.MeasurableSet.analyticSet_image** 是 Mathlib 中的一个定理，位于命名空间
 `MeasureTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The image of a measurable set in a standard Borel space under a measurable map
is an analytic set.
-/
theorem _root_.MeasurableSet.analyticSet_image {X Y : Type*} [MeasurableSpace X]
    [StandardBorelSpace X] [TopologicalSpace Y] [MeasurableSpace Y]
    [OpensMeasurableSpace Y] {f : X → Y} [SecondCountableTopology (range f)] {s : Set X}
    (hs : MeasurableSet s) (hf : Measurable f) : AnalyticSet (f '' s) := by
  let := upgradeStandardBorel X
  rw [eq_borel_upgradeStandardBorel X] at hs
  rcases hf.exists_continuous with ⟨τ', hle, hfc, hτ'⟩
  let m' : MeasurableSpace X := @borel _ τ'
  have b' : BorelSpace X := ⟨rfl⟩
  have hle := borel_anti hle
  exact (hle _ hs).analyticSet.image_of_continuous hfc

/-- Preimage of an analytic set is an analytic set. -/
/-
**MeasureTheory.AnalyticSet.preimage** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.An
alyticSet`。
形式化陈述：∀ {X : Type u_3} {Y : Type u_4} [inst : TopologicalSpace X] [inst_1 : Topo
logicalSpace Y] [PolishSpace X] [T2Space Y]   {s : Set Y}, MeasureTheory.Analyti
cSet s → ∀ {f : X → Y}, Continuous f → MeasureTheory.AnalyticSet (f ⁻¹' s)
参数：f ⁻¹' s。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `MeasureTheory.analyticSet_iff_exists_polishSpace_range`：analyticSet_iff_
exists_polishSpace_range {s : Set α} : AnalyticSet s ↔ exists (β : Type) (h : To
pologicalSpace β) (_ : @PolishSpace β h) (f …
· 使用定理 `isClosed_eq`：isClosed_eq [T2Space X] {f g : Y -> X} (hf : Continuous f) 
(hg : Continuous g) : IsClosed { y : Y | f y = g y }
· 使用定理 `Continuous.fst'`：Continuous.fst' {f : X -> Z} (hf : Continuous f) : Cont
inuous fun x : X × Y => f x.fst
· 使用定理 `Continuous.snd'`：Continuous.snd' {f : Y -> Z} (hf : Continuous f) : Cont
inuous fun x : X × Y => f x.snd
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `MeasureTheory.AnalyticSet.image_of_continuous`：∀ {α : Type u_1} [inst : 
TopologicalSpace α] {β : Type u_3} [inst_1 : TopologicalSpace β] {s : Set α},   
MeasureTheory.AnalyticSet s → ∀ {f …
· 使用定理 `IsClosed.analyticSet`：∀ {α : Type u_1} [inst : TopologicalSpace α] [Poli
shSpace α] {s : Set α}, IsClosed s → MeasureTheory.AnalyticSet s
· 使用定理 `instPolishSpaceOfSeparableSpaceOfIsCompletelyMetrizableSpace`：∀ {α : Typ
e u_1} [inst : TopologicalSpace α] [TopologicalSpace.SeparableSpace α]   [Topolo
gicalSpace.IsCompletelyMetrizableSpace α], PolishS…
· 使用定理 `TopologicalSpace.instSeparableSpaceProd`：∀ {α : Type u} {β : Type u_1} [
t : TopologicalSpace α] [inst : TopologicalSpace β] [TopologicalSpace.SeparableS
pace α]   [TopologicalSpace.S…
· 使用定理 `TopologicalSpace.SecondCountableTopology.to_separableSpace`：∀ {α : Type 
u} [t : TopologicalSpace α] [SecondCountableTopology α], TopologicalSpace.Separa
bleSpace α
· 使用定理 `PolishSpace.toSecondCountableTopology`：∀ {α : Type u_3} {h : Topological
Space α} [self : PolishSpace α], SecondCountableTopology α
· 使用定理 `PolishSpace.toIsCompletelyMetrizableSpace`：∀ {α : Type u_3} {h : Topolog
icalSpace α} [self : PolishSpace α], TopologicalSpace.IsCompletelyMetrizableSpac
e α
· 使用定理 `continuous_fst`：continuous_fst (f : X → Y × Z) (hf : Continuous f) : Con
tinuous (fun x ↦ (f x).fst)

--- 原说明 ---
Preimage of an analytic set is an analytic set.
-/
protected lemma AnalyticSet.preimage {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    [PolishSpace X] [T2Space Y] {s : Set Y} (hs : AnalyticSet s) {f : X → Y} (hf : Continuous f) :
    AnalyticSet (f ⁻¹' s) := by
  rcases analyticSet_iff_exists_polishSpace_range.1 hs with ⟨Z, _, _, g, hg, rfl⟩
  have : IsClosed {x : X × Z | f x.1 = g x.2} := isClosed_eq hf.fst' hg.snd'
  convert! this.analyticSet.image_of_continuous continuous_fst
  ext x
  simp [eq_comm]

/-! ### Separating sets with measurable sets -/

/-- Two sets `u` and `v` in a measurable space are measurably separable if there
exists a measurable set containing `u` and disjoint from `v`.
This is mostly interesting for Borel-separable sets. -/
/-
**MeasureTheory.MeasurablySeparable** 是 Mathlib 中的一个定义，位于命名空间 `MeasureTheory`。
形式化陈述：MeasurablySeparable {α : Type*} [MeasurableSpace α] (s t : Set α) : Prop
参数：s t : Set α。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Two sets `u` and `v` in a measurable space are measurably separable if there
exists a measurable set containing `u` and disjoint from `v`.
This is mostly interesting for Borel-separable sets.
-/
def MeasurablySeparable {α : Type*} [MeasurableSpace α] (s t : Set α) : Prop :=
  ∃ u, s ⊆ u ∧ Disjoint t u ∧ MeasurableSet u
/-
**MeasureTheory.MeasurablySeparable.iUnion** 是 Mathlib 中的一个定理，位于命名空间 `MeasureThe
ory.MeasurablySeparable`。
形式化陈述：∀ {ι : Type u_2} [Countable ι] {α : Type u_3} [inst : MeasurableSpace α] {
s t : ι → Set α},   (∀ (m n : ι), MeasureTheory.MeasurablySeparable (s m) (t n))
 → MeasureTheory.MeasurablySeparable (⋃ n, s n) (⋃ m, t m)
参数：∀ (m n : ι), MeasureTheory.MeasurablySeparable (s m) (t n)；⋃ n, s n；⋃ m, t m。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.iUnion_subset`：iUnion_subset {s : ι -> Set α} {t : Set α} (h : foral
l i, s i subseteq t) : ⋃ i, s i subseteq t
· 使用定理 `Set.subset_iUnion_of_subset`：subset_iUnion_of_subset {s : Set α} {t : ι 
-> Set α} (i : ι) (h : s subseteq t i) : s subseteq ⋃ i, t i
· 使用定理 `Set.subset_iInter`：subset_iInter {t : Set β} {s : ι -> Set β} (h : foral
l i, t subseteq s i) : t subseteq ⋂ i, s i
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `Disjoint.mono_right`：Disjoint.mono_right (h : b <= c) : Disjoint a c -> 
Disjoint a b
· 使用定理 `Set.iInter_subset`：iInter_subset : forall (s : ι -> Set β) (i : ι), ⋂ i,
 s i subseteq s i
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `MeasurableSet.iUnion`：∀ {α : Type u_1} {ι : Sort u_6} {m : MeasurableSpa
ce α} [Countable ι] ⦃f : ι → Set α⦄,   (∀ (b : ι), MeasurableSet (f b)) → Measur
ableSet (⋃…
· 使用定理 `MeasurableSet.iInter`：MeasurableSet.iInter [Countable ι] {f : ι -> Set α
} (h : forall b, MeasurableSet (f b)) : MeasurableSet (⋂ b, f b)
· 使用定理 `Classical.choose_spec`：∀ {α : Sort u} {p : α → Prop} (h : ∃ x, p x), p (
Classical.choose h)
-/
theorem MeasurablySeparable.iUnion [Countable ι] {α : Type*} [MeasurableSpace α] {s t : ι → Set α}
    (h : ∀ m n, MeasurablySeparable (s m) (t n)) : MeasurablySeparable (⋃ n, s n) (⋃ m, t m) := by
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

/-- The hard part of the Lusin separation theorem saying that two disjoint analytic sets are
contained in disjoint Borel sets (see the full statement in `AnalyticSet.measurablySeparable`).
Here, we prove this when our analytic sets are the ranges of functions from `ℕ → ℕ`.
-/
/-
**MeasureTheory.measurablySeparable_range_of_disjoint** 是 Mathlib 中的一个定理，位于命名空间 
`MeasureTheory`。
形式化陈述：measurablySeparable_range_of_disjoint [T2Space α] [MeasurableSpace α] [Ope
nsMeasurableSpace α] {f g : (Nat -> Nat) -> α} (hf : Continuous f) (hg : Continu
ous g) (h : Disjoint (range f) (range g)) : MeasurablySeparable (range f) (range
 g)
参数：Nat -> Nat；hf : Continuous f；hg : Continuous g；h : Disjoint (range f) (range 
g)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Classical.byContradiction`：∀ {p : Prop}, (¬p → False) → p
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose₂`：contrapose₂ {p q : Prop} : (¬ q -
> p) -> (¬ p -> q)
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `Mathlib.Tactic.Push.not_and_eq`：not_and_eq : (¬ (p ∧ q)) = (p -> ¬ q)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `PiNat.iUnion_cylinder_update`：iUnion_cylinder_update (x : forall n, E n)
 (n : Nat) : ⋃ k, cylinder (update x n k) (n + 1) = cylinder x n
· 使用定理 `Set.image_iUnion`：image_iUnion {f : α -> β} {s : ι -> Set α} : (f '' ⋃ i
, s i) = ⋃ i, f '' s i
· 使用定理 `MeasureTheory.MeasurablySeparable.iUnion`：∀ {ι : Type u_2} [Countable ι]
 {α : Type u_3} [inst : MeasurableSpace α] {s t : ι → Set α},   (∀ (m n : ι), Me
asureTheory.MeasurablySeparabl…
· 使用定理 `instCountableNat`：Countable ℕ
· 使用定理 `PiNat.update_mem_cylinder`：update_mem_cylinder (x : forall n, E n) (n : 
Nat) (y : E n) : update x n y in cylinder x n
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `PiNat.cylinder_zero`：cylinder_zero (x : forall n, E n) : cylinder x 0 = 
univ
· 使用定理 `Set.image_univ`：image_univ {f : α -> β} : f '' univ = range f
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `Function.iterate_succ'`：iterate_succ' (n : Nat) : f^[n.succ] = f ∘ f^[n]
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用引理 `Nat.le_induction`：le_induction {m : Nat} {P : forall n, m <= n -> Prop} 
(base : P m m.le_refl) (succ : forall n hmn, P n hmn -> P (n + 1) (le_succ_of_le
 hmn))…
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `PiNat.mem_cylinder_iff_eq`：mem_cylinder_iff_eq {x y : forall n, E n} {n 
: Nat} : y in cylinder x n ↔ cylinder y n = cylinder x n
· 使用定理 `PiNat.mem_cylinder_iff`：mem_cylinder_iff {x y : forall n, E n} {n : Nat}
 : y in cylinder x n ↔ forall i < n, y i = x i
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
（共 63 条，此处仅展示前 30 条）

--- 原说明 ---
The hard part of the Lusin separation theorem saying that two disjoint analytic 
sets are
contained in disjoint Borel sets (see the full statement in `AnalyticSet.measura
blySeparable`).
Here, we prove this when our analytic sets are the ranges of functions from `ℕ →
 ℕ`.
-/
theorem measurablySeparable_range_of_disjoint [T2Space α] [MeasurableSpace α]
    [OpensMeasurableSpace α] {f g : (ℕ → ℕ) → α} (hf : Continuous f) (hg : Continuous g)
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
  have I : ∀ n x y, ¬MeasurablySeparable (f '' cylinder x n) (g '' cylinder y n) →
      ∃ x' y', x' ∈ cylinder x n ∧ y' ∈ cylinder y n ∧
      ¬MeasurablySeparable (f '' cylinder x' (n + 1)) (g '' cylinder y' (n + 1)) := by
    intro n x y
    contrapose!
    intro H
    rw [← iUnion_cylinder_update x n, ← iUnion_cylinder_update y n, image_iUnion, image_iUnion]
    refine MeasurablySeparable.iUnion fun i j => ?_
    exact H _ _ (update_mem_cylinder _ _ _) (update_mem_cylinder _ _ _)
  -- consider the set of pairs of cylinders of some length whose images are not Borel-separated
  let A :=
    { p : ℕ × (ℕ → ℕ) × (ℕ → ℕ) //
      ¬MeasurablySeparable (f '' cylinder p.2.1 p.1) (g '' cylinder p.2.2 p.1) }
  -- for each such pair, one can find longer cylinders whose images are not Borel-separated either
  have : ∀ p : A, ∃ q : A,
      q.1.1 = p.1.1 + 1 ∧ q.1.2.1 ∈ cylinder p.1.2.1 p.1.1 ∧ q.1.2.2 ∈ cylinder p.1.2.2 p.1.1 := by
    rintro ⟨⟨n, x, y⟩, hp⟩
    rcases I n x y hp with ⟨x', y', hx', hy', h'⟩
    exact ⟨⟨⟨n + 1, x', y'⟩, h'⟩, rfl, hx', hy'⟩
  choose F hFn hFx hFy using this
  let p0 : A := ⟨⟨0, fun _ => 0, fun _ => 0⟩, by simp [hfg]⟩
  -- construct inductively decreasing sequences of cylinders whose images are not separated
  let p : ℕ → A := fun n => F^[n] p0
  have prec : ∀ n, p (n + 1) = F (p n) := fun n => by simp only [p, iterate_succ', Function.comp]
  -- check that at the `n`-th step we deal with cylinders of length `n`
  have pn_fst : ∀ n, (p n).1.1 = n := fun n ↦ by
    induction n with
    | zero => rfl
    | succ n IH => simp only [prec, hFn, IH]
  -- check that the cylinders we construct are indeed decreasing, by checking that the coordinates
  -- are stationary.
  have Ix : ∀ m n, m + 1 ≤ n → (p n).1.2.1 m = (p (m + 1)).1.2.1 m := by
    intro m
    apply Nat.le_induction
    · rfl
    intro n hmn IH
    have I : (F (p n)).val.snd.fst m = (p n).val.snd.fst m := by
      apply hFx (p n) m
      rw [pn_fst]
      exact hmn
    rw [prec, I, IH]
  have Iy : ∀ m n, m + 1 ≤ n → (p n).1.2.2 m = (p (m + 1)).1.2.2 m := by
    intro m
    apply Nat.le_induction
    · rfl
    intro n hmn IH
    have I : (F (p n)).val.snd.snd m = (p n).val.snd.snd m := by
      apply hFy (p n) m
      rw [pn_fst]
      exact hmn
    rw [prec, I, IH]
  -- denote by `x` and `y` the limit points of these two sequences of cylinders.
  set x : ℕ → ℕ := fun n => (p (n + 1)).1.2.1 n with hx
  set y : ℕ → ℕ := fun n => (p (n + 1)).1.2.2 n with hy
  -- by design, the cylinders around these points have images which are not Borel-separable.
  have M : ∀ n, ¬MeasurablySeparable (f '' cylinder x n) (g '' cylinder y n) := by
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
      ∃ u v : Set α, IsOpen u ∧ IsOpen v ∧ f x ∈ u ∧ g y ∈ v ∧ Disjoint u v := by
    apply t2_separation
    exact disjoint_iff_forall_ne.1 h (mem_range_self _) (mem_range_self _)
  let : MetricSpace (ℕ → ℕ) := metricSpaceNatNat
  obtain ⟨εx, εxpos, hεx⟩ : ∃ (εx : ℝ), εx > 0 ∧ Metric.ball x εx ⊆ f ⁻¹' u := by
    apply Metric.mem_nhds_iff.1
    exact hf.continuousAt.preimage_mem_nhds (u_open.mem_nhds xu)
  obtain ⟨εy, εypos, hεy⟩ : ∃ (εy : ℝ), εy > 0 ∧ Metric.ball y εy ⊆ g ⁻¹' v := by
    apply Metric.mem_nhds_iff.1
    exact hg.continuousAt.preimage_mem_nhds (v_open.mem_nhds yv)
  obtain ⟨n, hn⟩ : ∃ n : ℕ, (1 / 2 : ℝ) ^ n < min εx εy :=
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
      change g '' cylinder y n ⊆ v
      rw [image_subset_iff]
      apply Subset.trans _ hεy
      intro z hz
      rw [mem_cylinder_iff_dist_le] at hz
      exact hz.trans_lt (hn.trans_le (min_le_right _ _))
  -- this is a contradiction.
  exact M n B

/-- The **Lusin separation theorem**: if two analytic sets are disjoint, then they are contained in
disjoint Borel sets. -/
/-
**MeasureTheory.AnalyticSet.measurablySeparable** 是 Mathlib 中的一个定理，位于命名空间 `Measu
reTheory.AnalyticSet`。
形式化陈述：∀ {α : Type u_1} [inst : TopologicalSpace α] [T2Space α] [inst_2 : Measura
bleSpace α] [OpensMeasurableSpace α]   {s t : Set α},   MeasureTheory.AnalyticSe
t s → MeasureTheory.AnalyticSet t → Disjoint s t → MeasureTheory.MeasurablySepar
able s t
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.AnalyticSet_def`：∀ {α : Type u_3} [inst : TopologicalSpace
 α] (s : Set α),   MeasureTheory.AnalyticSet s = (s = ∅ ∨ ∃ f, Continuous f ∧ Se
t.range f = s)
· 使用定理 `Set.Subset.refl`：∀ {α : Type u} (a : Set α), a ⊆ a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `MeasurableSet.empty`：MeasurableSet.empty [MeasurableSpace α] : Measurabl
eSet (∅ : Set α)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.subset_univ`：subset_univ (s : Set α) : s subseteq univ
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `MeasurableSet.univ`：∀ {α : Type u_1} {m : MeasurableSpace α}, Measurable
Set Set.univ
· 使用定理 `MeasureTheory.measurablySeparable_range_of_disjoint`：measurablySeparable
_range_of_disjoint [T2Space α] [MeasurableSpace α] [OpensMeasurableSpace α] {f g
 : (Nat -> Nat) -> α} (hf : Continuous f)…

--- 原说明 ---
The **Lusin separation theorem**: if two analytic sets are disjoint, then they a
re contained in
disjoint Borel sets.
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

/-- **Suslin's Theorem**: in a Hausdorff topological space, an analytic set with an analytic
complement is measurable. -/
/-
**MeasureTheory.AnalyticSet.measurableSet_of_compl** 是 Mathlib 中的一个定理，位于命名空间 `Me
asureTheory.AnalyticSet`。
形式化陈述：∀ {α : Type u_1} [inst : TopologicalSpace α] [T2Space α] [inst_2 : Measura
bleSpace α] [OpensMeasurableSpace α]   {s : Set α}, MeasureTheory.AnalyticSet s 
→ MeasureTheory.AnalyticSet sᶜ → MeasurableSet s
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.AnalyticSet.measurablySeparable`：∀ {α : Type u_1} [inst : 
TopologicalSpace α] [T2Space α] [inst_2 : MeasurableSpace α] [OpensMeasurableSpa
ce α]   {s t : Set α},   MeasureThe…
· 使用定理 `disjoint_compl_right`：disjoint_compl_right : Disjoint a aᶜ
· 使用定理 `LE.le.antisymm`：∀ {α : Type u_1} [inst : PartialOrder α] {a b : α}, a ≤ 
b → b ≤ a → a = b
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `Set.disjoint_compl_left_iff_subset`：disjoint_compl_left_iff_subset : Dis
joint sᶜ t ↔ t subseteq s

--- 原说明 ---
**Suslin's Theorem**: in a Hausdorff topological space, an analytic set with an 
analytic
complement is measurable.
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

/-- If `f : X → Z` is a surjective Borel measurable map from a standard Borel space
to a countably separated measurable space, then the preimage of a set `s`
is measurable if and only if the set is measurable.
One implication is the definition of measurability, the other one heavily relies on `X` being a
standard Borel space. -/
/-
**Measurable.measurableSet_preimage_iff_of_surjective** 是 Mathlib 中的一个定理，位于命名空间 
`Measurable`。
形式化陈述：measurableSet_preimage_iff_of_surjective [CountablySeparated Z] {f : X -> 
Z} (hf : Measurable f) (hsurj : Surjective f) {s : Set Z} : MeasurableSet (f ⁻¹'
 s) ↔ MeasurableSet s
参数：hf : Measurable f；hsurj : Surjective f。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `exists_opensMeasurableSpace_of_countablySeparated`：exists_opensMeasurabl
eSpace_of_countablySeparated (α : Type*) [m : MeasurableSpace α] [CountablySepar
ated α] : exists _ : TopologicalSpace α…
· 使用定理 `MeasureTheory.AnalyticSet.measurableSet_of_compl`：∀ {α : Type u_1} [inst
 : TopologicalSpace α] [T2Space α] [inst_2 : MeasurableSpace α] [OpensMeasurable
Space α]   {s : Set α}, MeasureTheory.…
· 使用定理 `T25Space.t2Space`：∀ {X : Type u_1} [inst : TopologicalSpace X] [T25Space
 X], T2Space X
· 使用定理 `T3Space.t25Space`：∀ {X : Type u_1} [inst : TopologicalSpace X] [T3Space 
X], T25Space X
· 使用定理 `T4Space.t3Space`：∀ {X : Type u_1} [inst : TopologicalSpace X] [T4Space X
], T3Space X
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.image_preimage_eq`：image_preimage_eq {f : α -> β} (s : Set β) (h : S
urjective f) : f '' f ⁻¹' s = s
· 使用定理 `MeasurableSet.analyticSet_image`：∀ {X : Type u_3} {Y : Type u_4} [inst :
 MeasurableSpace X] [StandardBorelSpace X] [inst_2 : TopologicalSpace Y]   [inst
_3 : MeasurableSpace …
· 使用定理 `TopologicalSpace.Subtype.secondCountableTopology`：∀ {α : Type u} [t : To
pologicalSpace α] (s : Set α) [SecondCountableTopology α], SecondCountableTopolo
gy ↑s
· 使用定理 `MeasurableSet.compl`：∀ {α : Type u_1} {s : Set α} {m : MeasurableSpace α
}, MeasurableSet s → MeasurableSet sᶜ

--- 原说明 ---
If `f : X → Z` is a surjective Borel measurable map from a standard Borel space
to a countably separated measurable space, then the preimage of a set `s`
is measurable if and only if the set is measurable.
One implication is the definition of measurability, the other one heavily relies
 on `X` being a
standard Borel space.
-/
theorem measurableSet_preimage_iff_of_surjective [CountablySeparated Z]
    {f : X → Z} (hf : Measurable f) (hsurj : Surjective f) {s : Set Z} :
    MeasurableSet (f ⁻¹' s) ↔ MeasurableSet s := by
  refine ⟨fun h => ?_, fun h => hf h⟩
  rcases exists_opensMeasurableSpace_of_countablySeparated Z with ⟨τ, _, _, _⟩
  apply AnalyticSet.measurableSet_of_compl
  · rw [← image_preimage_eq s hsurj]
    exact h.analyticSet_image hf
  · rw [← image_preimage_eq sᶜ hsurj]
    exact h.compl.analyticSet_image hf
/-
**Measurable.map_measurableSpace_eq** 是 Mathlib 中的一个定理，位于命名空间 `Measurable`。
形式化陈述：map_measurableSpace_eq [CountablySeparated Z] {f : X -> Z} (hf : Measurabl
e f) (hsurj : Surjective f) : MeasurableSpace.map f ‹MeasurableSpace X› = ‹Measu
rableSpace Z›
参数：hf : Measurable f；hsurj : Surjective f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasurableSpace.ext`：MeasurableSpace.ext {m₁ m₂ : MeasurableSpace α} (h 
: forall s : Set α, MeasurableSet[m₁] s ↔ MeasurableSet[m₂] s) : m₁ = m₂
· 使用定理 `Measurable.measurableSet_preimage_iff_of_surjective`：measurableSet_preim
age_iff_of_surjective [CountablySeparated Z] {f : X -> Z} (hf : Measurable f) (h
surj : Surjective f) {s : Set Z} : Measur…
-/
theorem map_measurableSpace_eq [CountablySeparated Z]
    {f : X → Z} (hf : Measurable f)
    (hsurj : Surjective f) : MeasurableSpace.map f ‹MeasurableSpace X› = ‹MeasurableSpace Z› :=
  MeasurableSpace.ext fun _ => hf.measurableSet_preimage_iff_of_surjective hsurj
/-
**Measurable.map_measurableSpace_eq_borel** 是 Mathlib 中的一个定理，位于命名空间 `Measurable`
。
形式化陈述：map_measurableSpace_eq_borel [SecondCountableTopology Y] {f : X -> Y} (hf 
: Measurable f) (hsurj : Surjective f) : MeasurableSpace.map f ‹MeasurableSpace 
X› = borel Y
参数：hf : Measurable f；hsurj : Surjective f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Measurable.mono`：Measurable.mono {ma ma' : MeasurableSpace α} {mb mb' : 
MeasurableSpace β} {f : α -> β} (hf : @Measurable α β ma mb f) (ha : ma <= ma') 
(hb :…
· 使用引理 `le_rfl`：le_rfl : a <= a
· 使用定理 `OpensMeasurableSpace.borel_le`：∀ {α : Type u_6} {inst : TopologicalSpace
 α} {h : MeasurableSpace α} [self : OpensMeasurableSpace α], borel α ≤ h
· 使用定理 `Measurable.map_measurableSpace_eq`：map_measurableSpace_eq [CountablySepa
rated Z] {f : X -> Z} (hf : Measurable f) (hsurj : Surjective f) : MeasurableSpa
ce.map f ‹MeasurableSpa…
· 使用定理 `BorelSpace.countablyGenerated`：∀ {α : Type u_6} [inst : TopologicalSpace
 α] [inst_1 : MeasurableSpace α] [BorelSpace α] [SecondCountableTopology α],   M
easurableSpace.Coun…
· 使用定理 `BorelSpace.opensMeasurable`：∀ {α : Type u_6} [inst : TopologicalSpace α]
 [inst_1 : MeasurableSpace α] [BorelSpace α], OpensMeasurableSpace α
-/
theorem map_measurableSpace_eq_borel [SecondCountableTopology Y] {f : X → Y} (hf : Measurable f)
    (hsurj : Surjective f) : MeasurableSpace.map f ‹MeasurableSpace X› = borel Y := by
  have d := hf.mono le_rfl OpensMeasurableSpace.borel_le
  let := borel Y; have : BorelSpace Y := ⟨rfl⟩
  exact d.map_measurableSpace_eq hsurj
/-
**Measurable.borelSpace_codomain** 是 Mathlib 中的一个定理，位于命名空间 `Measurable`。
形式化陈述：borelSpace_codomain [SecondCountableTopology Y] {f : X -> Y} (hf : Measura
ble f) (hsurj : Surjective f) : BorelSpace Y
参数：hf : Measurable f；hsurj : Surjective f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Measurable.map_measurableSpace_eq`：map_measurableSpace_eq [CountablySepa
rated Z] {f : X -> Z} (hf : Measurable f) (hsurj : Surjective f) : MeasurableSpa
ce.map f ‹MeasurableSpa…
· 使用定理 `instCountablySeparatedElemOfHasCountableSeparatingOnIsOpen`：∀ {α : Type 
u_1} [inst : TopologicalSpace α] [inst_1 : MeasurableSpace α] [OpensMeasurableSp
ace α] {s : Set α}   [h : HasCountableSeparating…
· 使用定理 `instHasCountableSeparatingOnIsOpenOfT0SpaceOfSecondCountableTopologyElem
`：∀ {X : Type u_1} [inst : TopologicalSpace X] {s : Set X} [T0Space ↑s] [SecondC
ountableTopology ↑s],   HasCountableSeparatingOn X IsOpen s
· 使用定理 `TopologicalSpace.Subtype.secondCountableTopology`：∀ {α : Type u} [t : To
pologicalSpace α] (s : Set α) [SecondCountableTopology α], SecondCountableTopolo
gy ↑s
· 使用定理 `Measurable.map_measurableSpace_eq_borel`：map_measurableSpace_eq_borel [S
econdCountableTopology Y] {f : X -> Y} (hf : Measurable f) (hsurj : Surjective f
) : MeasurableSpace.map f ‹Me…
-/
theorem borelSpace_codomain [SecondCountableTopology Y] {f : X → Y} (hf : Measurable f)
    (hsurj : Surjective f) : BorelSpace Y :=
  ⟨(hf.map_measurableSpace_eq hsurj).symm.trans <| hf.map_measurableSpace_eq_borel hsurj⟩

/-- If `f : X → Z` is a Borel measurable map from a standard Borel space to a
countably separated measurable space then the preimage of a set `s` is measurable
if and only if the set is measurable in `Set.range f`. -/
/-
**Measurable.measurableSet_preimage_iff_preimage_val** 是 Mathlib 中的一个定理，位于命名空间 `
Measurable`。
形式化陈述：measurableSet_preimage_iff_preimage_val {f : X -> Z} [CountablySeparated (
range f)] (hf : Measurable f) {s : Set Z} : MeasurableSet (f ⁻¹' s) ↔ Measurable
Set ((↑) ⁻¹' s : Set (range f))
参数：range f；hf : Measurable f。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Measurable.rangeFactorization`：∀ {α : Type u_1} {β : Type u_2} {m : Meas
urableSpace α} {mβ : MeasurableSpace β} {f : α → β},   Measurable f → Measurable
 (Set.rangeFactoriz…
· 使用定理 `Measurable.measurableSet_preimage_iff_of_surjective`：measurableSet_preim
age_iff_of_surjective [CountablySeparated Z] {f : X -> Z} (hf : Measurable f) (h
surj : Surjective f) {s : Set Z} : Measur…
· 使用定理 `Set.rangeFactorization_surjective`：∀ {α : Type u} {ι : Sort u_1} {f : ι 
→ α}, Function.Surjective (Set.rangeFactorization f)

--- 原说明 ---
If `f : X → Z` is a Borel measurable map from a standard Borel space to a
countably separated measurable space then the preimage of a set `s` is measurabl
e
if and only if the set is measurable in `Set.range f`.
-/
theorem measurableSet_preimage_iff_preimage_val {f : X → Z} [CountablySeparated (range f)]
    (hf : Measurable f) {s : Set Z} :
    MeasurableSet (f ⁻¹' s) ↔ MeasurableSet ((↑) ⁻¹' s : Set (range f)) :=
  have hf' : Measurable (rangeFactorization f) := by fun_prop
  hf'.measurableSet_preimage_iff_of_surjective (s := Subtype.val ⁻¹' s)
    rangeFactorization_surjective

/-- If `f : X → Z` is a Borel measurable map from a standard Borel space to a
countably separated measurable space and the range of `f` is measurable,
then the preimage of a set `s` is measurable
if and only if the intersection with `Set.range f` is measurable. -/
/-
**Measurable.measurableSet_preimage_iff_inter_range** 是 Mathlib 中的一个定理，位于命名空间 `M
easurable`。
形式化陈述：measurableSet_preimage_iff_inter_range {f : X -> Z} [CountablySeparated (r
ange f)] (hf : Measurable f) (hr : MeasurableSet (range f)) {s : Set Z} : Measur
ableSet (f ⁻¹' s) ↔ MeasurableSet (s inter range f)
参数：range f；hf : Measurable f；hr : MeasurableSet (range f)。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Measurable.measurableSet_preimage_iff_preimage_val`：measurableSet_preima
ge_iff_preimage_val {f : X -> Z} [CountablySeparated (range f)] (hf : Measurable
 f) {s : Set Z} : MeasurableSet (f ⁻¹' s…
· 使用定理 `Set.inter_comm`：inter_comm (a b : Set α) : a inter b = b inter a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasurableEmbedding.measurableSet_image`：measurableSet_image (hf : Measu
rableEmbedding f) : MeasurableSet (f '' s) ↔ MeasurableSet s
· 使用定理 `MeasurableEmbedding.subtype_coe`：subtype_coe (hs : MeasurableSet s) : Me
asurableEmbedding ((↑) : s -> α) where injective
· 使用定理 `Subtype.image_preimage_coe`：image_preimage_coe (s t : Set α) : ((↑) : s 
-> α) '' ((↑) : s -> α) ⁻¹' t = s inter t
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a

--- 原说明 ---
If `f : X → Z` is a Borel measurable map from a standard Borel space to a
countably separated measurable space and the range of `f` is measurable,
then the preimage of a set `s` is measurable
if and only if the intersection with `Set.range f` is measurable.
-/
theorem measurableSet_preimage_iff_inter_range {f : X → Z} [CountablySeparated (range f)]
    (hf : Measurable f) (hr : MeasurableSet (range f)) {s : Set Z} :
    MeasurableSet (f ⁻¹' s) ↔ MeasurableSet (s ∩ range f) := by
  rw [hf.measurableSet_preimage_iff_preimage_val, inter_comm,
    ← (MeasurableEmbedding.subtype_coe hr).measurableSet_image, Subtype.image_preimage_coe]

/-- If `f : X → Z` is a Borel measurable map from a standard Borel space
to a countably separated measurable space,
then for any measurable space `β` and `g : Z → β`, the composition `g ∘ f` is
measurable if and only if the restriction of `g` to the range of `f` is measurable. -/
/-
**Measurable.measurable_comp_iff_restrict** 是 Mathlib 中的一个定理，位于命名空间 `Measurable`
。
形式化陈述：measurable_comp_iff_restrict {f : X -> Z} [CountablySeparated (range f)] (
hf : Measurable f) {g : Z -> β} : Measurable (g ∘ f) ↔ Measurable (domRestrict (
range f) g)
参数：range f；hf : Measurable f。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `forall₂_congr`：∀ {α : Sort u_1} {β : α → Sort u_2} {p q : (a : α) → β a 
→ Prop},   (∀ (a : α) (b : β a), p a b ↔ q a b) → ((∀ (a : α) (b : β a), p a b) 
↔ ∀…
· 使用定理 `Measurable.measurableSet_preimage_iff_preimage_val`：measurableSet_preima
ge_iff_preimage_val {f : X -> Z} [CountablySeparated (range f)] (hf : Measurable
 f) {s : Set Z} : MeasurableSet (f ⁻¹' s…

--- 原说明 ---
If `f : X → Z` is a Borel measurable map from a standard Borel space
to a countably separated measurable space,
then for any measurable space `β` and `g : Z → β`, the composition `g ∘ f` is
measurable if and only if the restriction of `g` to the range of `f` is measurab
le.
-/
theorem measurable_comp_iff_restrict {f : X → Z}
    [CountablySeparated (range f)]
    (hf : Measurable f) {g : Z → β} : Measurable (g ∘ f) ↔ Measurable (domRestrict (range f) g) :=
  forall₂_congr fun s _ => measurableSet_preimage_iff_preimage_val hf (s := g ⁻¹' s)

/-- If `f : X → Z` is a surjective Borel measurable map from a standard Borel space
to a countably separated measurable space,
then for any measurable space `α` and `g : Z → α`, the composition
`g ∘ f` is measurable if and only if `g` is measurable. -/
/-
**Measurable.measurable_comp_iff_of_surjective** 是 Mathlib 中的一个定理，位于命名空间 `Measur
able`。
形式化陈述：measurable_comp_iff_of_surjective [CountablySeparated Z] {f : X -> Z} (hf 
: Measurable f) (hsurj : Surjective f) {g : Z -> β} : Measurable (g ∘ f) ↔ Measu
rable g
参数：hf : Measurable f；hsurj : Surjective f。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `forall₂_congr`：∀ {α : Sort u_1} {β : α → Sort u_2} {p q : (a : α) → β a 
→ Prop},   (∀ (a : α) (b : β a), p a b ↔ q a b) → ((∀ (a : α) (b : β a), p a b) 
↔ ∀…
· 使用定理 `Measurable.measurableSet_preimage_iff_of_surjective`：measurableSet_preim
age_iff_of_surjective [CountablySeparated Z] {f : X -> Z} (hf : Measurable f) (h
surj : Surjective f) {s : Set Z} : Measur…

--- 原说明 ---
If `f : X → Z` is a surjective Borel measurable map from a standard Borel space
to a countably separated measurable space,
then for any measurable space `α` and `g : Z → α`, the composition
`g ∘ f` is measurable if and only if `g` is measurable.
-/
theorem measurable_comp_iff_of_surjective [CountablySeparated Z]
    {f : X → Z} (hf : Measurable f) (hsurj : Surjective f)
    {g : Z → β} : Measurable (g ∘ f) ↔ Measurable g :=
  forall₂_congr fun s _ => measurableSet_preimage_iff_of_surjective hf hsurj (s := g ⁻¹' s)

end Measurable

/-
**Continuous.map_eq_borel** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Continuous.map_eq_borel {X Y : Type*} [TopologicalSpace X] [PolishSpace X]
 [MeasurableSpace X] [BorelSpace X] [TopologicalSpace Y] [T0Space Y] [SecondCoun
tableTopology Y] {f : X -> Y} (hf : Continuous f) (hsurj : Surjective f) : Measu
rableSpace.map f ‹MeasurableSpace X› = borel Y
参数：hf : Continuous f；hsurj : Surjective f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Measurable.map_measurableSpace_eq`：map_measurableSpace_eq [CountablySepa
rated Z] {f : X -> Z} (hf : Measurable f) (hsurj : Surjective f) : MeasurableSpa
ce.map f ‹MeasurableSpa…
· 使用定理 `standardBorel_of_polish`：∀ {α : Type u_1} [inst : MeasurableSpace α] [τ 
: TopologicalSpace α] [BorelSpace α] [PolishSpace α],   StandardBorelSpace α
· 使用定理 `BorelSpace.countablyGenerated`：∀ {α : Type u_6} [inst : TopologicalSpace
 α] [inst_1 : MeasurableSpace α] [BorelSpace α] [SecondCountableTopology α],   M
easurableSpace.Coun…
· 使用定理 `BorelSpace.opensMeasurable`：∀ {α : Type u_6} [inst : TopologicalSpace α]
 [inst_1 : MeasurableSpace α] [BorelSpace α], OpensMeasurableSpace α
· 使用定理 `Continuous.measurable`：Continuous.measurable {f : α -> γ} (hf : Continuo
us f) : Measurable f
-/
theorem Continuous.map_eq_borel {X Y : Type*} [TopologicalSpace X] [PolishSpace X]
    [MeasurableSpace X] [BorelSpace X] [TopologicalSpace Y] [T0Space Y] [SecondCountableTopology Y]
    {f : X → Y} (hf : Continuous f) (hsurj : Surjective f) :
    MeasurableSpace.map f ‹MeasurableSpace X› = borel Y := by
  borelize Y
  exact hf.measurable.map_measurableSpace_eq hsurj
/-
**Continuous.map_borel_eq** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Continuous.map_borel_eq {X Y : Type*} [TopologicalSpace X] [PolishSpace X]
 [TopologicalSpace Y] [T0Space Y] [SecondCountableTopology Y] {f : X -> Y} (hf :
 Continuous f) (hsurj : Surjective f) : MeasurableSpace.map f (borel X) = borel 
Y
参数：hf : Continuous f；hsurj : Surjective f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Continuous.map_eq_borel`：Continuous.map_eq_borel {X Y : Type*} [Topologi
calSpace X] [PolishSpace X] [MeasurableSpace X] [BorelSpace X] [TopologicalSpace
 Y] [T0Space …
-/
theorem Continuous.map_borel_eq {X Y : Type*} [TopologicalSpace X] [PolishSpace X]
    [TopologicalSpace Y] [T0Space Y] [SecondCountableTopology Y] {f : X → Y} (hf : Continuous f)
    (hsurj : Surjective f) : MeasurableSpace.map f (borel X) = borel Y := by
  borelize X
  exact hf.map_eq_borel hsurj
/-
**Quotient.borelSpace** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：Quotient.borelSpace {X : Type*} [TopologicalSpace X] [PolishSpace X] [Meas
urableSpace X] [BorelSpace X] {s : Setoid X} [T0Space (Quotient s)] [SecondCount
ableTopology (Quotient s)] : BorelSpace (Quotient s)
参数：Quotient s；Quotient s。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Continuous.map_eq_borel`：Continuous.map_eq_borel {X Y : Type*} [Topologi
calSpace X] [PolishSpace X] [MeasurableSpace X] [BorelSpace X] [TopologicalSpace
 Y] [T0Space …
· 使用定理 `Quotient.mk'`：Quotient.mk'_surjective [s : Setoid α] : Function.Surjecti
ve (Quotient.mk' : α -> Quotient s)
· 使用定理 `continuous_quotient_mk'`：continuous_quotient_mk' : Continuous (@Quotient
.mk' X s)
· 使用定理 `Quotient.mk'_surjective`：∀ {α : Sort u_1} [s : Setoid α], Function.Surje
ctive Quotient.mk'
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
/-
**CosetSpace.borelSpace** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：CosetSpace.borelSpace {G : Type*} [TopologicalSpace G] [PolishSpace G] [Gr
oup G] [MeasurableSpace G] [BorelSpace G] {N : Subgroup G} [T2Space (G ⧸ N)] [Se
condCountableTopology (G ⧸ N)] : BorelSpace (G ⧸ N)
参数：G ⧸ N；G ⧸ N。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `T1Space.t0Space`：∀ {X : Type u_1} [inst : TopologicalSpace X] [T1Space X
], T0Space X
· 使用定理 `T2Space.t1Space`：∀ {X : Type u_1} [inst : TopologicalSpace X] [T2Space X
], T1Space X
-/
instance CosetSpace.borelSpace {G : Type*} [TopologicalSpace G] [PolishSpace G] [Group G]
    [MeasurableSpace G] [BorelSpace G] {N : Subgroup G} [T2Space (G ⧸ N)]
    [SecondCountableTopology (G ⧸ N)] : BorelSpace (G ⧸ N) := Quotient.borelSpace

@[to_additive]
/-
**QuotientGroup.borelSpace** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：QuotientGroup.borelSpace {G : Type*} [TopologicalSpace G] [PolishSpace G] 
[Group G] [IsTopologicalGroup G] [MeasurableSpace G] [BorelSpace G] {N : Subgrou
p G} [N.Normal] [IsClosed (N : Set G)] : BorelSpace (G ⧸ N)
参数：N : Set G。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Continuous.map_eq_borel`：Continuous.map_eq_borel {X Y : Type*} [Topologi
calSpace X] [PolishSpace X] [MeasurableSpace X] [BorelSpace X] [TopologicalSpace
 Y] [T0Space …
· 使用定理 `T3Space.toT0Space`：∀ {X : Type u} {inst : TopologicalSpace X} [self : T3
Space X], T0Space X
· 使用定理 `instSeparatelyContinuousMulOfContinuousMul`：∀ {M : Type u_1} [inst : Top
ologicalSpace M] [inst_1 : Mul M] [ContinuousMul M], SeparatelyContinuousMul M
· 使用定理 `IsTopologicalGroup.toContinuousMul`：∀ {G : Type u_4} {inst : Topological
Space G} {inst_1 : Group G} [self : IsTopologicalGroup G], ContinuousMul G
· 使用定理 `PolishSpace.toSecondCountableTopology`：∀ {α : Type u_3} {h : Topological
Space α} [self : PolishSpace α], SecondCountableTopology α
· 使用定理 `QuotientGroup.continuous_mk`：continuous_mk {N : Subgroup G} : Continuous
 (mk : G -> G ⧸ N)
· 使用定理 `QuotientGroup.mk_surjective`：mk_surjective : Function.Surjective @mk _ _
 s
-/
instance QuotientGroup.borelSpace {G : Type*} [TopologicalSpace G] [PolishSpace G] [Group G]
    [IsTopologicalGroup G] [MeasurableSpace G] [BorelSpace G] {N : Subgroup G} [N.Normal]
    [IsClosed (N : Set G)] : BorelSpace (G ⧸ N) :=
  ⟨continuous_mk.map_eq_borel mk_surjective⟩

/-! ### Injective images of Borel sets -/

variable {γ : Type*}

/-- The **Lusin-Souslin theorem**: the range of a continuous injective function defined on a Polish
space is Borel-measurable. -/
/-
**MeasureTheory.measurableSet_range_of_continuous_injective** 是 Mathlib 中的一个定理，位
于命名空间 ``。
形式化陈述：MeasureTheory.measurableSet_range_of_continuous_injective {β : Type*} [Top
ologicalSpace γ] [PolishSpace γ] [TopologicalSpace β] [T2Space β] [MeasurableSpa
ce β] [OpensMeasurableSpace β] {f : γ -> β} (f_cont : Continuous f) (f_inj : Inj
ective f) : MeasurableSet (range f)
参数：f_cont : Continuous f；f_inj : Injective f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `PolishSpace.toIsCompletelyMetrizableSpace`：∀ {α : Type u_3} {h : Topolog
icalSpace α} [self : PolishSpace α], TopologicalSpace.IsCompletelyMetrizableSpac
e α
· 使用定理 `TopologicalSpace.exists_countable_basis`：exists_countable_basis [SecondC
ountableTopology α] : exists b : Set (Set α), b.Countable ∧ ∅ ∉ b ∧ IsTopologica
lBasis b
· 使用定理 `PolishSpace.toSecondCountableTopology`：∀ {α : Type u_3} {h : Topological
Space α} [self : PolishSpace α], SecondCountableTopology α
· 使用定理 `MeasureTheory.AnalyticSet.measurablySeparable`：∀ {α : Type u_1} [inst : 
TopologicalSpace α] [T2Space α] [inst_2 : MeasurableSpace α] [OpensMeasurableSpa
ce α]   {s t : Set α},   MeasureThe…
· 使用定理 `IsOpen.analyticSet_image`：∀ {α : Type u_1} [inst : TopologicalSpace α] {
β : Type u_3} [inst_1 : TopologicalSpace β] [PolishSpace β] {s : Set β},   IsOpe
n s → ∀ {f : β…
· 使用定理 `TopologicalSpace.IsTopologicalBasis.isOpen`：∀ {α : Type u} [t : Topologi
calSpace α] {s : Set α} {b : Set (Set α)},   TopologicalSpace.IsTopologicalBasis
 b → s ∈ b → IsOpen s
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `Disjoint.image`：∀ {α : Type u_1} {β : Type u_2} {s t u : Set α} {f : α →
 β},   Disjoint s t → Set.InjOn f u → s ⊆ u → t ⊆ u → Disjoint (f '' s) (f '' t)
· 使用定理 `Function.Injective.injOn`：∀ {α : Type u_1} {β : Type u_2} {f : α → β}, F
unction.Injective f → ∀ {s : Set α}, Set.InjOn f s
· 使用定理 `Set.subset_univ`：subset_univ (s : Set α) : s subseteq univ
· 使用定理 `Disjoint.symm`：Disjoint.symm (x y : Finmap β) (h : Disjoint x y) : Disjo
int y x
· 使用定理 `exists_seq_strictAnti_tendsto`：exists_seq_strictAnti_tendsto [DenselyOrd
ered α] [NoMaxOrder α] [FirstCountableTopology α] (x : α) : exists u : Nat -> α,
 StrictAnti u ∧ (fo…
· 使用定理 `instOrderTopologyReal`：OrderTopology ℝ
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
· 使用定理 `instNoMaxOrderOfNontrivial`：∀ {R : Type u} [inst : Ring R] [inst_1 : Par
tialOrder R] [IsOrderedRing R] [Nontrivial R], NoMaxOrder R
· 使用定理 `TopologicalSpace.PseudoMetrizableSpace.firstCountableTopology`：∀ {X : Ty
pe u_2} [inst : TopologicalSpace X] [h : TopologicalSpace.PseudoMetrizableSpace 
X], FirstCountableTopology X
· 使用定理 `PseudoEMetricSpace.pseudoMetrizableSpace`：∀ {α : Type u_2} [inst : Pseud
oEMetricSpace α], TopologicalSpace.PseudoMetrizableSpace α
· 使用定理 `Set.Subset.antisymm`：∀ {α : Type u} {a b : Set α}, a ⊆ b → b ⊆ a → a = b
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.mem_iInter`：mem_iInter {x : α} {s : ι -> Set α} : (x in ⋂ i, s i) ↔ 
forall i, x in s i
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `TopologicalSpace.IsTopologicalBasis.mem_nhds_iff`：∀ {α : Type u} [t : To
pologicalSpace α] {a : α} {s : Set α} {b : Set (Set α)},   TopologicalSpace.IsTo
pologicalBasis b → (s ∈ nhds a ↔ ∃ t ∈…
· 使用定理 `Metric.ball_mem_nhds`：ball_mem_nhds (x : α) {ε : Real} (ε0 : 0 < ε) : ba
ll x ε in 𝓝 x
· 使用定理 `half_pos`：half_pos (h : 0 < a) : 0 < a / 2
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
（共 150 条，此处仅展示前 30 条）

--- 原说明 ---
The **Lusin-Souslin theorem**: the range of a continuous injective function defi
ned on a Polish
space is Borel-measurable.
-/
theorem MeasureTheory.measurableSet_range_of_continuous_injective {β : Type*} [TopologicalSpace γ]
    [PolishSpace γ] [TopologicalSpace β] [T2Space β] [MeasurableSpace β] [OpensMeasurableSpace β]
    {f : γ → β} (f_cont : Continuous f) (f_inj : Injective f) :
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
    ∃ b : Set (Set γ), b.Countable ∧ ∅ ∉ b ∧ IsTopologicalBasis b := exists_countable_basis γ
  have : Encodable b := b_count.toEncodable
  let A := { p : b × b // Disjoint (p.1 : Set γ) p.2 }
  -- for each pair of disjoint sets in the topological basis `b`, consider Borel sets separating
  -- their images, by injectivity of `f` and the Lusin separation theorem.
  have : ∀ p : A, ∃ q : Set β,
      f '' (p.1.1 : Set γ) ⊆ q ∧ Disjoint (f '' (p.1.2 : Set γ)) q ∧ MeasurableSet q := by
    intro p
    apply
      AnalyticSet.measurablySeparable ((hb.isOpen p.1.1.2).analyticSet_image f_cont)
        ((hb.isOpen p.1.2.2).analyticSet_image f_cont)
    exact Disjoint.image p.2 f_inj.injOn (subset_univ _) (subset_univ _)
  choose q hq1 hq2 q_meas using this
  -- define sets `E i` and `F n` as in the proof sketch above
  let E : b → Set β := fun s =>
    closure (f '' s) ∩ ⋂ (t : b) (ht : Disjoint s.1 t.1), q ⟨(s, t), ht⟩ \ q ⟨(t, s), ht.symm⟩
  obtain ⟨u, u_anti, u_pos, u_lim⟩ :
      ∃ u : ℕ → ℝ, StrictAnti u ∧ (∀ n : ℕ, 0 < u n) ∧ Tendsto u atTop (𝓝 0) :=
    exists_seq_strictAnti_tendsto (0 : ℝ)
  let F : ℕ → Set β := fun n => ⋃ (s : b) (_ : IsBounded s.1 ∧ diam s.1 ≤ u n), E s
  -- it is enough to show that `range f = ⋂ F n`, as the latter set is obviously measurable.
  suffices range f = ⋂ n, F n by
    have E_meas : ∀ s : b, MeasurableSet (E s) := by
      intro b
      refine isClosed_closure.measurableSet.inter ?_
      refine MeasurableSet.iInter fun s => ?_
      exact MeasurableSet.iInter fun hs => (q_meas _).diff (q_meas _)
    have F_meas : ∀ n, MeasurableSet (F n) := by
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
    obtain ⟨s, sb, ys, hs⟩ : ∃ (s : Set γ), s ∈ b ∧ y ∈ s ∧ s ⊆ ball y (u n / 2) := by
      apply hb.mem_nhds_iff.1
      exact ball_mem_nhds _ (half_pos (u_pos n))
    have diam_s : diam s ≤ u n := by
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
    have C1 : ∀ n, ∃ (s : b) (_ : IsBounded s.1 ∧ diam s.1 ≤ u n), x ∈ E s := fun n => by
      simpa only [F, mem_iUnion] using mem_iInter.1 hx n
    choose s hs hxs using C1
    have C2 : ∀ n, (s n).1.Nonempty := by
      intro n
      rw [nonempty_iff_ne_empty]
      grind
    -- choose a point `y n ∈ s n`.
    choose y hy using C2
    have I : ∀ m n, ((s m).1 ∩ (s n).1).Nonempty := by
      intro m n
      rw [← not_disjoint_iff_nonempty_inter]
      by_contra! h
      have A : x ∈ q ⟨(s m, s n), h⟩ \ q ⟨(s n, s m), h.symm⟩ :=
        haveI := mem_iInter.1 (hxs m).2 (s n)
        (mem_iInter.1 this h :)
      have B : x ∈ q ⟨(s n, s m), h.symm⟩ \ q ⟨(s m, s n), h⟩ :=
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
        dist (y m) (y n) ≤ dist (y m) z + dist z (y n) := dist_triangle _ _ _
        _ ≤ u m + u n :=
          (add_le_add ((dist_le_diam_of_mem (hs m).1 (hy m) zsm).trans (hs m).2)
            ((dist_le_diam_of_mem (hs n).1 zsn (hy n)).trans (hs n).2))
        _ ≤ 2 * u m := by linarith [u_anti.antitone hmn]
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
    obtain ⟨δ, δpos, hδ⟩ : ∃ δ > (0 : ℝ), ball z δ ⊆ f ⁻¹' v := by
      apply Metric.mem_nhds_iff.1
      exact f_cont.continuousAt.preimage_mem_nhds (v_open.mem_nhds fzv)
    obtain ⟨n, hn⟩ : ∃ n, u n + dist (y n) z < δ :=
      haveI : Tendsto (fun n => u n + dist (y n) z) atTop (𝓝 0) := by
        simpa only [add_zero] using u_lim.add (tendsto_iff_dist_tendsto_zero.1 y_lim)
      ((tendsto_order.1 this).2 _ δpos).exists
    -- for large enough `n`, the image of `s n` is contained in `v`, by continuity of `f`.
    have fsnv : f '' s n ⊆ v := by
      rw [image_subset_iff]
      apply Subset.trans _ hδ
      intro a ha
      calc
        dist a z ≤ dist a (y n) + dist (y n) z := dist_triangle _ _ _
        _ ≤ u n + dist (y n) z := by grw [dist_le_diam_of_mem (hs n).1 ha (hy n), (hs n).2]
        _ < δ := hn
    -- as `x` belongs to the closure of `f '' (s n)`, it belongs to the closure of `v`.
    have : x ∈ closure v := closure_mono fsnv (hxs n).1
    -- this is a contradiction, as `x` is supposed to belong to `w`, which is disjoint from
    -- the closure of `v`.
    exact disjoint_left.1 (hvw.closure_left w_open) this xw
/-
**IsClosed.measurableSet_image_of_continuousOn_injOn** 是 Mathlib 中的一个定理，位于命名空间 `
`。
形式化陈述：IsClosed.measurableSet_image_of_continuousOn_injOn [TopologicalSpace γ] [P
olishSpace γ] {β : Type*} [TopologicalSpace β] [T2Space β] [MeasurableSpace β] [
OpensMeasurableSpace β] {s : Set γ} (hs : IsClosed s) {f : γ -> β} (f_cont : Con
tinuousOn f s) (f_inj : InjOn f s) : MeasurableSet (f '' s)
参数：hs : IsClosed s；f_cont : ContinuousOn f s；f_inj : InjOn f s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.image_eq_range`：image_eq_range (f : α -> β) (s : Set α) : f '' s = r
ange fun x : s => f x
· 使用定理 `IsClosed.polishSpace`：∀ {α : Type u_1} [inst : TopologicalSpace α] [Poli
shSpace α] {s : Set α}, IsClosed s → PolishSpace ↑s
· 使用定理 `MeasureTheory.measurableSet_range_of_continuous_injective`：MeasureTheory
.measurableSet_range_of_continuous_injective {β : Type*} [TopologicalSpace γ] [P
olishSpace γ] [TopologicalSpace β] [T2Space β] …
· 使用定理 `continuousOn_iff_continuous_domRestrict`：continuousOn_iff_continuous_dom
Restrict : ContinuousOn f s ↔ Continuous (s.domRestrict f)
· 使用定理 `Set.injOn_iff_injective`：injOn_iff_injective : InjOn f s ↔ Injective (s.
domRestrict f)
-/
theorem IsClosed.measurableSet_image_of_continuousOn_injOn
    [TopologicalSpace γ] [PolishSpace γ] {β : Type*} [TopologicalSpace β] [T2Space β]
    [MeasurableSpace β] [OpensMeasurableSpace β] {s : Set γ} (hs : IsClosed s) {f : γ → β}
    (f_cont : ContinuousOn f s) (f_inj : InjOn f s) : MeasurableSet (f '' s) := by
  rw [image_eq_range]
  have : PolishSpace s := IsClosed.polishSpace hs
  apply measurableSet_range_of_continuous_injective
  · rwa [continuousOn_iff_continuous_domRestrict] at f_cont
  · rwa [injOn_iff_injective] at f_inj

variable {α β : Type*} [MeasurableSpace β]
section
variable [tβ : TopologicalSpace β] [T2Space β] [MeasurableSpace α] {s : Set γ} {f : γ → β}

/-- The Lusin-Souslin theorem: if `s` is Borel-measurable in a Polish space, then its image under
a continuous injective map is also Borel-measurable. -/
/-
**MeasurableSet.image_of_continuousOn_injOn** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：MeasurableSet.image_of_continuousOn_injOn [OpensMeasurableSpace β] [tγ : T
opologicalSpace γ] [PolishSpace γ] [MeasurableSpace γ] [BorelSpace γ] (hs : Meas
urableSet s) (f_cont : ContinuousOn f s) (f_inj : InjOn f s) : MeasurableSet (f 
'' s)
参数：hs : MeasurableSet s；f_cont : ContinuousOn f s；f_inj : InjOn f s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasurableSet.isClopenable`：∀ {α : Type u_1} [inst : TopologicalSpace α]
 [PolishSpace α] [inst_2 : MeasurableSpace α] [BorelSpace α] {s : Set α},   Meas
urableSet s → Po…
· 使用定理 `IsClosed.measurableSet_image_of_continuousOn_injOn`：IsClosed.measurableS
et_image_of_continuousOn_injOn [TopologicalSpace γ] [PolishSpace γ] {β : Type*} 
[TopologicalSpace β] [T2Space β] [Measur…
· 使用定理 `ContinuousOn.mono_dom`：ContinuousOn.mono_dom {α β : Type*} {t₁ t₂ : Topo
logicalSpace α} {t₃ : TopologicalSpace β} (h₁ : t₂ <= t₁) {s : Set α} {f : α -> 
β} (h₂ : @C…

--- 原说明 ---
The Lusin-Souslin theorem: if `s` is Borel-measurable in a Polish space, then it
s image under
a continuous injective map is also Borel-measurable.
-/
theorem MeasurableSet.image_of_continuousOn_injOn [OpensMeasurableSpace β]
    [tγ : TopologicalSpace γ] [PolishSpace γ] [MeasurableSpace γ] [BorelSpace γ]
    (hs : MeasurableSet s)
    (f_cont : ContinuousOn f s) (f_inj : InjOn f s) : MeasurableSet (f '' s) := by
  obtain ⟨t', t't, t'_polish, s_closed, _⟩ :
      ∃ t' : TopologicalSpace γ, t' ≤ tγ ∧ @PolishSpace γ t' ∧ IsClosed[t'] s ∧ IsOpen[t'] s :=
    hs.isClopenable
  exact
    @IsClosed.measurableSet_image_of_continuousOn_injOn γ t' t'_polish β _ _ _ _ s s_closed f
      (f_cont.mono_dom t't) f_inj

/-- The Lusin-Souslin theorem: if `s` is Borel-measurable in a standard Borel space,
then its image under a measurable injective map taking values in a
countably separate measurable space is also Borel-measurable. -/
/-
**MeasurableSet.image_of_measurable_injOn** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：MeasurableSet.image_of_measurable_injOn {f : γ -> α} [MeasurableSpace.Coun
tablySeparated α] [MeasurableSpace γ] [StandardBorelSpace γ] (hs : MeasurableSet
 s) (f_meas : Measurable f) (f_inj : InjOn f s) : MeasurableSet (f '' s)
参数：hs : MeasurableSet s；f_meas : Measurable f；f_inj : InjOn f s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `exists_opensMeasurableSpace_of_countablySeparated`：exists_opensMeasurabl
eSpace_of_countablySeparated (α : Type*) [m : MeasurableSpace α] [CountablySepar
ated α] : exists _ : TopologicalSpace α…
· 使用定理 `Measurable.exists_continuous`：∀ {α : Type u_3} {β : Type u_4} [t : Topol
ogicalSpace α] [PolishSpace α] [inst : MeasurableSpace α] [BorelSpace α]   [tβ :
 TopologicalSpace …
· 使用定理 `UpgradedStandardBorel.toPolishSpace`：∀ {α : Type u_1} [self : UpgradedSt
andardBorel α], PolishSpace α
· 使用定理 `UpgradedStandardBorel.toBorelSpace`：∀ {α : Type u_1} [self : UpgradedSta
ndardBorel α], BorelSpace α
· 使用定理 `TopologicalSpace.Subtype.secondCountableTopology`：∀ {α : Type u} [t : To
pologicalSpace α] (s : Set α) [SecondCountableTopology α], SecondCountableTopolo
gy ↑s
· 使用定理 `borel_anti`：borel_anti : Antitone (@borel α)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `eq_borel_upgradeStandardBorel`：eq_borel_upgradeStandardBorel [Measurable
Space α] [StandardBorelSpace α] : ‹MeasurableSpace α› = @borel _ (upgradeStandar
dBorel α).toTopolog…
· 使用定理 `MeasurableSet.image_of_continuousOn_injOn`：MeasurableSet.image_of_contin
uousOn_injOn [OpensMeasurableSpace β] [tγ : TopologicalSpace γ] [PolishSpace γ] 
[MeasurableSpace γ] [BorelSpace…
· 使用定理 `T25Space.t2Space`：∀ {X : Type u_1} [inst : TopologicalSpace X] [T25Space
 X], T2Space X
· 使用定理 `T3Space.t25Space`：∀ {X : Type u_1} [inst : TopologicalSpace X] [T3Space 
X], T25Space X
· 使用定理 `T4Space.t3Space`：∀ {X : Type u_1} [inst : TopologicalSpace X] [T4Space X
], T3Space X
· 使用定理 `Continuous.continuousOn`：Continuous.continuousOn (h : Continuous f) : Co
ntinuousOn f s

--- 原说明 ---
The Lusin-Souslin theorem: if `s` is Borel-measurable in a standard Borel space,
then its image under a measurable injective map taking values in a
countably separate measurable space is also Borel-measurable.
-/
theorem MeasurableSet.image_of_measurable_injOn {f : γ → α}
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
      ∃ t' : TopologicalSpace γ, t' ≤ tγ ∧ @Continuous γ _ t' _ f ∧ @PolishSpace γ t' :=
    f_meas.exists_continuous
  have hs' := (borel_anti t't s) <| by rwa [← eq_borel_upgradeStandardBorel γ]
  let : MeasurableSpace γ := @borel γ t'
  let : BorelSpace γ := ⟨rfl⟩
  exact hs'.image_of_continuousOn_injOn f_cont.continuousOn f_inj

/-- An injective continuous function on a Polish space is a measurable embedding. -/
/-
**Continuous.measurableEmbedding** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Continuous.measurableEmbedding [BorelSpace β] [TopologicalSpace γ] [Polish
Space γ] [MeasurableSpace γ] [BorelSpace γ] (f_cont : Continuous f) (f_inj : Inj
ective f) : MeasurableEmbedding f
参数：f_cont : Continuous f；f_inj : Injective f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Continuous.measurable`：Continuous.measurable {f : α -> γ} (hf : Continuo
us f) : Measurable f
· 使用定理 `BorelSpace.opensMeasurable`：∀ {α : Type u_6} [inst : TopologicalSpace α]
 [inst_1 : MeasurableSpace α] [BorelSpace α], OpensMeasurableSpace α
· 使用定理 `MeasurableSet.image_of_continuousOn_injOn`：MeasurableSet.image_of_contin
uousOn_injOn [OpensMeasurableSpace β] [tγ : TopologicalSpace γ] [PolishSpace γ] 
[MeasurableSpace γ] [BorelSpace…
· 使用定理 `Continuous.continuousOn`：Continuous.continuousOn (h : Continuous f) : Co
ntinuousOn f s
· 使用定理 `Function.Injective.injOn`：∀ {α : Type u_1} {β : Type u_2} {f : α → β}, F
unction.Injective f → ∀ {s : Set α}, Set.InjOn f s

--- 原说明 ---
An injective continuous function on a Polish space is a measurable embedding.
-/
theorem Continuous.measurableEmbedding [BorelSpace β]
    [TopologicalSpace γ] [PolishSpace γ] [MeasurableSpace γ] [BorelSpace γ]
    (f_cont : Continuous f) (f_inj : Injective f) :
    MeasurableEmbedding f :=
  { injective := f_inj
    measurable := f_cont.measurable
    measurableSet_image' := fun _u hu =>
      hu.image_of_continuousOn_injOn f_cont.continuousOn f_inj.injOn }

/-- If `s` is Borel-measurable in a Polish space and `f` is continuous injective on `s`, then
the restriction of `f` to `s` is a measurable embedding. -/
/-
**ContinuousOn.measurableEmbedding** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ContinuousOn.measurableEmbedding [BorelSpace β] [TopologicalSpace γ] [Poli
shSpace γ] [MeasurableSpace γ] [BorelSpace γ] (hs : MeasurableSet s) (f_cont : C
ontinuousOn f s) (f_inj : InjOn f s) : MeasurableEmbedding (s.domRestrict f)
参数：hs : MeasurableSet s；f_cont : ContinuousOn f s；f_inj : InjOn f s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Set.injOn_iff_injective`：injOn_iff_injective : InjOn f s ↔ Injective (s.
domRestrict f)
· 使用定理 `Continuous.measurable`：Continuous.measurable {f : α -> γ} (hf : Continuo
us f) : Measurable f
· 使用定理 `BorelSpace.opensMeasurable`：∀ {α : Type u_6} [inst : TopologicalSpace α]
 [inst_1 : MeasurableSpace α] [BorelSpace α], OpensMeasurableSpace α
· 使用定理 `continuousOn_iff_continuous_domRestrict`：continuousOn_iff_continuous_dom
Restrict : ContinuousOn f s ↔ Continuous (s.domRestrict f)
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `MeasurableEmbedding.measurableSet_image`：measurableSet_image (hf : Measu
rableEmbedding f) : MeasurableSet (f '' s) ↔ MeasurableSet s
· 使用定理 `MeasurableEmbedding.subtype_coe`：subtype_coe (hs : MeasurableSet s) : Me
asurableEmbedding ((↑) : s -> α) where injective
· 使用定理 `MeasurableSet.image_of_continuousOn_injOn`：MeasurableSet.image_of_contin
uousOn_injOn [OpensMeasurableSpace β] [tγ : TopologicalSpace γ] [PolishSpace γ] 
[MeasurableSpace γ] [BorelSpace…
· 使用定理 `ContinuousOn.mono`：ContinuousOn.mono (hf : ContinuousOn f s) (h : t subs
eteq s) : ContinuousOn f t
· 使用定理 `Subtype.coe_image_subset`：coe_image_subset (s : Set α) (t : Set s) : ((↑
) : s -> α) '' t subseteq s
· 使用定理 `Set.InjOn.mono`：∀ {α : Type u_1} {β : Type u_2} {s₁ s₂ : Set α} {f : α →
 β}, s₁ ⊆ s₂ → Set.InjOn f s₂ → Set.InjOn f s₁
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.image_comp`：image_comp (f : β -> γ) (g : α -> β) (a : Set α) : f ∘ g
 '' a = f '' g '' a

--- 原说明 ---
If `s` is Borel-measurable in a Polish space and `f` is continuous injective on 
`s`, then
the restriction of `f` to `s` is a measurable embedding.
-/
theorem ContinuousOn.measurableEmbedding [BorelSpace β]
    [TopologicalSpace γ] [PolishSpace γ] [MeasurableSpace γ] [BorelSpace γ]
    (hs : MeasurableSet s) (f_cont : ContinuousOn f s)
    (f_inj : InjOn f s) : MeasurableEmbedding (s.domRestrict f) :=
  { injective := injOn_iff_injective.1 f_inj
    measurable := (continuousOn_iff_continuous_domRestrict.1 f_cont).measurable
    measurableSet_image' := by
      intro u hu
      have A : MeasurableSet (((↑) : s → γ) '' u) :=
        (MeasurableEmbedding.subtype_coe hs).measurableSet_image.2 hu
      have B : MeasurableSet (f '' ((↑) : s → γ) '' u) :=
        A.image_of_continuousOn_injOn (f_cont.mono (Subtype.coe_image_subset s u))
          (f_inj.mono (Subtype.coe_image_subset s u))
      rwa [← image_comp] at B }

/-- An injective measurable function from a standard Borel space to a
countably separated measurable space is a measurable embedding. -/
/-
**Measurable.measurableEmbedding** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Measurable.measurableEmbedding {f : γ -> α} [MeasurableSpace.CountablySepa
rated α] [MeasurableSpace γ] [StandardBorelSpace γ] (f_meas : Measurable f) (f_i
nj : Injective f) : MeasurableEmbedding f
参数：f_meas : Measurable f；f_inj : Injective f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasurableSet.image_of_measurable_injOn`：MeasurableSet.image_of_measurab
le_injOn {f : γ -> α} [MeasurableSpace.CountablySeparated α] [MeasurableSpace γ]
 [StandardBorelSpace γ] (hs :…
· 使用定理 `Function.Injective.injOn`：∀ {α : Type u_1} {β : Type u_2} {f : α → β}, F
unction.Injective f → ∀ {s : Set α}, Set.InjOn f s

--- 原说明 ---
An injective measurable function from a standard Borel space to a
countably separated measurable space is a measurable embedding.
-/
theorem Measurable.measurableEmbedding {f : γ → α}
    [MeasurableSpace.CountablySeparated α]
    [MeasurableSpace γ] [StandardBorelSpace γ]
    (f_meas : Measurable f) (f_inj : Injective f) : MeasurableEmbedding f :=
  { injective := f_inj
    measurable := f_meas
    measurableSet_image' := fun _u hu => hu.image_of_measurable_injOn f_meas f_inj.injOn }

/-- If one Polish topology on a type refines another, they have the same Borel sets. -/
/-
**MeasureTheory.borel_eq_borel_of_le** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：MeasureTheory.borel_eq_borel_of_le {t t' : TopologicalSpace γ} (ht : Polis
hSpace (h
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `Continuous.measurableEmbedding`：Continuous.measurableEmbedding [BorelSpa
ce β] [TopologicalSpace γ] [PolishSpace γ] [MeasurableSpace γ] [BorelSpace γ] (f
_cont : Continuous f…
· 使用定理 `TopologicalSpace.t2Space_of_metrizableSpace`：∀ {X : Type u_2} [inst : To
pologicalSpace X] [TopologicalSpace.MetrizableSpace X], T2Space X
· 使用定理 `TopologicalSpace.IsCompletelyMetrizableSpace.MetrizableSpace`：∀ {X : Typ
e u_1} [inst : TopologicalSpace X] [TopologicalSpace.IsCompletelyMetrizableSpace
 X],   TopologicalSpace.MetrizableSpace X
· 使用定理 `PolishSpace.toIsCompletelyMetrizableSpace`：∀ {α : Type u_3} {h : Topolog
icalSpace α} [self : PolishSpace α], TopologicalSpace.IsCompletelyMetrizableSpac
e α
· 使用定理 `continuous_id_of_le`：continuous_id_of_le {t t' : TopologicalSpace α} (h 
: t <= t') : Continuous[t, t'] id
· 使用定理 `Function.injective_id`：∀ {α : Sort u_1}, Function.Injective id
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.image_congr`：image_congr {f g : α -> β} {s : Set α} (h : forall a in
 s, f a = g a) : f '' s = g '' s
· 使用定理 `Set.image_id'`：image_id' (s : Set α) : (fun x => x) '' s = s
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `MeasurableEmbedding.measurableSet_image`：measurableSet_image (hf : Measu
rableEmbedding f) : MeasurableSet (f '' s) ↔ MeasurableSet s
· 使用定理 `borel_anti`：borel_anti : Antitone (@borel α)

--- 原说明 ---
If one Polish topology on a type refines another, they have the same Borel sets.
-/
theorem MeasureTheory.borel_eq_borel_of_le {t t' : TopologicalSpace γ}
    (ht : PolishSpace (h := t)) (ht' : PolishSpace (h := t')) (hle : t ≤ t') :
    @borel _ t = @borel _ t' := by
  refine le_antisymm ?_ (borel_anti hle)
  intro s hs
  have e := @Continuous.measurableEmbedding
    _ _ (@borel _ t') t' _ _ (@BorelSpace.mk _ _ (borel γ) rfl)
    t _ (@borel _ t) (@BorelSpace.mk _ t (@borel _ t) rfl) (continuous_id_of_le hle) injective_id
  convert! e.measurableSet_image.2 hs
  simp only [id_eq, image_id']

/-- In a Polish space, a set is clopenable if and only if it is Borel-measurable. -/
/-
**MeasureTheory.isClopenable_iff_measurableSet** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：MeasureTheory.isClopenable_iff_measurableSet [tγ : TopologicalSpace γ] [Po
lishSpace γ] [MeasurableSpace γ] [BorelSpace γ] : IsClopenable s ↔ MeasurableSet
 s
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `BorelSpace.measurable_eq`：∀ {α : Type u_6} {inst : TopologicalSpace α} {
inst_1 : MeasurableSpace α} [self : BorelSpace α], inst_1 = borel α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.borel_eq_borel_of_le`：MeasureTheory.borel_eq_borel_of_le {
t t' : TopologicalSpace γ} (ht : PolishSpace (h
· 使用定理 `MeasurableSpace.measurableSet_generateFrom`：measurableSet_generateFrom {
s : Set (Set α)} {t : Set α} (ht : t in s) : MeasurableSet[generateFrom s] t
· 使用定理 `MeasurableSet.isClopenable`：∀ {α : Type u_1} [inst : TopologicalSpace α]
 [PolishSpace α] [inst_2 : MeasurableSpace α] [BorelSpace α] {s : Set α},   Meas
urableSet s → Po…

--- 原说明 ---
In a Polish space, a set is clopenable if and only if it is Borel-measurable.
-/
theorem MeasureTheory.isClopenable_iff_measurableSet
    [tγ : TopologicalSpace γ] [PolishSpace γ] [MeasurableSpace γ] [BorelSpace γ] :
    IsClopenable s ↔ MeasurableSet s := by
  -- we already know that a measurable set is clopenable. Conversely, assume that `s` is clopenable.
  refine ⟨fun hs => ?_, fun hs => hs.isClopenable⟩
  borelize γ
  -- consider a finer topology `t'` in which `s` is open and closed.
  obtain ⟨t', t't, t'_polish, _, s_open⟩ :
    ∃ t' : TopologicalSpace γ, t' ≤ tγ ∧ @PolishSpace γ t' ∧ IsClosed[t'] s ∧ IsOpen[t'] s := hs
  rw [← borel_eq_borel_of_le t'_polish _ t't]
  · exact MeasurableSpace.measurableSet_generateFrom s_open
  infer_instance

end

section LinearOrder

variable {α β : Type*} {t : Set α} {g : α → β}
  [TopologicalSpace α] [MeasurableSpace α] [BorelSpace α] [LinearOrder α] [OrderTopology α]
  [PolishSpace α]
  [TopologicalSpace β] [MeasurableSpace β] [BorelSpace β] [LinearOrder β] [OrderTopology β]

/-
**MeasurableSet.image_of_monotoneOn_of_continuousOn** 是 Mathlib 中的一个定理，位于命名空间 ``
。
形式化陈述：MeasurableSet.image_of_monotoneOn_of_continuousOn (ht : MeasurableSet t) (
hg : MonotoneOn g t) (h'g : ContinuousOn g t) : MeasurableSet (g '' t)
参数：ht : MeasurableSet t；hg : MonotoneOn g t；h'g : ContinuousOn g t。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `MonotoneOn.countable_setOfPred_two_preimages`：MonotoneOn.countable_setOf
Pred_two_preimages [SecondCountableTopology α] (hf : MonotoneOn f s) : Set.Count
able {c | exists x y, x in s ∧ y i…
· 使用定理 `PolishSpace.toSecondCountableTopology`：∀ {α : Type u_3} {h : Topological
Space α} [self : PolishSpace α], SecondCountableTopology α
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `exists_prop_congr`：∀ {p p' : Prop} {q q' : p → Prop}, (∀ (h : p), q h ↔ 
q' h) → ∀ (hp : p ↔ p'), Exists q ↔ ∃ (h : p'), q' ⋯
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `Exists.elim`：∀ {α : Sort u} {p : α → Prop} {b : Prop}, (∃ x, p x) → (∀ (
a : α), p a → b) → b
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `and_true`：∀ (p : Prop), (p ∧ True) = p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `MeasurableSet.biUnion`：∀ {α : Type u_1} {β : Type u_2} {m : MeasurableSp
ace α} {f : β → Set α} {s : Set β},   s.Countable → (∀ b ∈ s, MeasurableSet (f b
)) → Measur…
· 使用定理 `Set.OrdConnected.preimage_monotoneOn`：∀ {α : Type u_1} {β : Type u_2} [i
nst : Preorder α] [inst_1 : Preorder β] {f : β → α} {t : Set β} {s : Set α},   s
.OrdConnected → MonotoneOn…
· 使用定理 `Set.ordConnected_singleton`：ordConnected_singleton {α : Type*} [PartialO
rder α] {a : α} : OrdConnected ({a} : Set α)
· 使用定理 `MeasurableSet.inter`：∀ {α : Type u_1} {m : MeasurableSpace α} {s₁ s₂ : S
et α}, MeasurableSet s₁ → MeasurableSet s₂ → MeasurableSet (s₁ ∩ s₂)
· 使用定理 `Set.OrdConnected.measurableSet`：Set.OrdConnected.measurableSet [OrderClo
sedTopology α] (h : OrdConnected s) : MeasurableSet s
· 使用定理 `BorelSpace.opensMeasurable`：∀ {α : Type u_6} [inst : TopologicalSpace α]
 [inst_1 : MeasurableSpace α] [BorelSpace α], OpensMeasurableSpace α
· 使用定理 `OrderTopology.to_orderClosedTopology`：∀ {α : Type u} [inst : Topological
Space α] [inst_1 : LinearOrder α] [OrderTopology α], OrderClosedTopology α
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Set.sdiff_self_inter`：sdiff_self_inter {s t : Set α} : s \ (s inter t) =
 s \ t
· 使用定理 `Set.sdiff_union_inter`：sdiff_union_inter (s t : Set α) : s \ t union s i
nter t = s
· 使用定理 `MeasurableSet.union`：∀ {α : Type u_1} {m : MeasurableSpace α} {s₁ s₂ : S
et α}, MeasurableSet s₁ → MeasurableSet s₂ → MeasurableSet (s₁ ∪ s₂)
· 使用定理 `MeasurableSet.image_of_continuousOn_injOn`：MeasurableSet.image_of_contin
uousOn_injOn [OpensMeasurableSpace β] [tγ : TopologicalSpace γ] [PolishSpace γ] 
[MeasurableSpace γ] [BorelSpace…
· 使用定理 `T25Space.t2Space`：∀ {X : Type u_1} [inst : TopologicalSpace X] [T25Space
 X], T2Space X
（共 45 条，此处仅展示前 30 条）
-/
theorem MeasurableSet.image_of_monotoneOn_of_continuousOn
    (ht : MeasurableSet t) (hg : MonotoneOn g t) (h'g : ContinuousOn g t) :
    MeasurableSet (g '' t) := by
  /- We use that the image of a measurable set by a continuous injective map is measurable.
  Therefore, we need to remove the points where the map is not injective. There are only countably
  many points that have several preimages, so this set is also measurable. -/
  let u : Set β := {c | ∃ x, ∃ y, x ∈ t ∧ y ∈ t ∧ x < y ∧ g x = c ∧ g y = c}
  have hu : Set.Countable u := MonotoneOn.countable_setOfPred_two_preimages hg
  let t' := t ∩ g ⁻¹' u
  have ht' : MeasurableSet t' := by
    have : t' = ⋃ c ∈ u, t ∩ g ⁻¹' {c} := by ext; simp [t']
    rw [this]
    apply MeasurableSet.biUnion hu (fun c hc ↦ ?_)
    obtain ⟨v, hv, tv⟩ : ∃ v, OrdConnected v ∧ t ∩ g ⁻¹' {c} = t ∩ v :=
      ordConnected_singleton.preimage_monotoneOn hg
    exact tv ▸ ht.inter hv.measurableSet
  have : g '' t = g '' (t \ t') ∪ g '' t' := by simp [← image_union, t']
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
  · exact hu.mono (by simp [t']) |>.measurableSet

/-- The image of a measurable set under a monotone map is measurable. -/
/-
**MeasurableSet.image_of_monotoneOn** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：MeasurableSet.image_of_monotoneOn [SecondCountableTopology β] (ht : Measur
ableSet t) (hg : MonotoneOn g t) : MeasurableSet (g '' t)
参数：ht : MeasurableSet t；hg : MonotoneOn g t。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MonotoneOn.countable_not_continuousWithinAt`：MonotoneOn.countable_not_co
ntinuousWithinAt (hf : MonotoneOn f s) : Set.Countable {x in s | ¬ContinuousWith
inAt f s x}
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.image_union`：image_union (f : α -> β) (s t : Set α) : f '' (s union 
t) = f '' s union f '' t
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Set.sdiff_sep_self`：∀ {α : Type u_1} (s : Set α) (p : α → Prop), s \ {a 
| a ∈ s ∧ p a} = {a | a ∈ s ∧ ¬p a}
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Classical.or_iff_not_imp_left`：∀ {a b : Prop}, a ∨ b ↔ ¬a → b
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Decidable.not_and_iff_not_or_not'`：∀ {b a : Prop} [Decidable b], ¬(a ∧ b
) ↔ ¬a ∨ ¬b
· 使用定理 `MeasurableSet.union`：∀ {α : Type u_1} {m : MeasurableSpace α} {s₁ s₂ : S
et α}, MeasurableSet s₁ → MeasurableSet s₂ → MeasurableSet (s₁ ∪ s₂)
· 使用定理 `MeasurableSet.image_of_monotoneOn_of_continuousOn`：MeasurableSet.image_o
f_monotoneOn_of_continuousOn (ht : MeasurableSet t) (hg : MonotoneOn g t) (h'g :
 ContinuousOn g t) : MeasurableSet (g '…
· 使用定理 `MeasurableSet.diff`：∀ {α : Type u_1} {m : MeasurableSpace α} {s₁ s₂ : Se
t α}, MeasurableSet s₁ → MeasurableSet s₂ → MeasurableSet (s₁ \ s₂)
· 使用定理 `Set.Countable.measurableSet`：Set.Countable.measurableSet {s : Set α} (hs
 : s.Countable) : MeasurableSet s
· 使用定理 `instMeasurableSingletonClassOfMeasurableEq`：∀ {α : Type u_1} [inst : Mea
surableSpace α] [MeasurableEq α], MeasurableSingletonClass α
· 使用定理 `StandardBorelSpace.instMeasurableEq`：∀ {α : Type u_1} [inst : Measurable
Space α] [StandardBorelSpace α], MeasurableEq α
· 使用定理 `standardBorel_of_polish`：∀ {α : Type u_1} [inst : MeasurableSpace α] [τ 
: TopologicalSpace α] [BorelSpace α] [PolishSpace α],   StandardBorelSpace α
· 使用定理 `MonotoneOn.mono`：∀ {α : Type u_1} {β : Type u_2} {s s₂ : Set α} {f : α →
 β} [inst : Preorder α] [inst_1 : Preorder β],   MonotoneOn f s → s₂ ⊆ s → Monot
oneOn…
· 使用定理 `Set.sdiff_subset`：sdiff_subset {s t : Set α} : s \ t subseteq s
· 使用定理 `ContinuousWithinAt.mono`：ContinuousWithinAt.mono (h : ContinuousWithinAt
 f t x) (hs : s subseteq t) : ContinuousWithinAt f s x
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `instMeasurableEqOfSecondCountableTopologyOfT2Space`：∀ {α : Type u_1} [in
st : TopologicalSpace α] [inst_1 : MeasurableSpace α] [OpensMeasurableSpace α]  
 [SecondCountableTopology α] [T2Space α]…
· 使用定理 `BorelSpace.opensMeasurable`：∀ {α : Type u_6} [inst : TopologicalSpace α]
 [inst_1 : MeasurableSpace α] [BorelSpace α], OpensMeasurableSpace α
· 使用定理 `T25Space.t2Space`：∀ {X : Type u_1} [inst : TopologicalSpace X] [T25Space
 X], T2Space X
· 使用定理 `T3Space.t25Space`：∀ {X : Type u_1} [inst : TopologicalSpace X] [T3Space 
X], T25Space X
· 使用定理 `T4Space.t3Space`：∀ {X : Type u_1} [inst : TopologicalSpace X] [T4Space X
], T3Space X
（共 33 条，此处仅展示前 30 条）

--- 原说明 ---
The image of a measurable set under a monotone map is measurable.
-/
theorem MeasurableSet.image_of_monotoneOn [SecondCountableTopology β]
    (ht : MeasurableSet t) (hg : MonotoneOn g t) : MeasurableSet (g '' t) := by
  /- Since there are only countably many discontinuity points, the result follows by reduction to
  the continuous case, which we have already proved. -/
  let t' := {x ∈ t | ¬ ContinuousWithinAt g t x}
  have ht' : Set.Countable t' := hg.countable_not_continuousWithinAt
  have : g '' t = g '' (t \ t') ∪ g '' t' := by
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

/-- The image of a measurable set under an antitone map is measurable. -/
/-
**MeasurableSet.image_of_antitoneOn** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：MeasurableSet.image_of_antitoneOn [SecondCountableTopology β] (ht : Measur
ableSet t) (hg : AntitoneOn g t) : MeasurableSet (g '' t)
参数：ht : MeasurableSet t；hg : AntitoneOn g t。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasurableSet.image_of_monotoneOn`：MeasurableSet.image_of_monotoneOn [Se
condCountableTopology β] (ht : MeasurableSet t) (hg : MonotoneOn g t) : Measurab
leSet (g '' t)
· 使用定理 `OrderDual.borelSpace`：∀ {α : Type u_6} [inst : TopologicalSpace α] [inst
_1 : MeasurableSpace α] [h : BorelSpace α], BorelSpace αᵒᵈ
· 使用定理 `instOrderTopologyOrderDual`：∀ {α : Type u} [ts : TopologicalSpace α] [in
st : Preorder α] [t : OrderTopology α], OrderTopology αᵒᵈ
· 使用定理 `instSecondCountableTopologyOrderDual`：∀ {α : Type u} [inst : Topological
Space α] [h : SecondCountableTopology α], SecondCountableTopology αᵒᵈ
· 使用定理 `AntitoneOn.dual_right`：∀ {α : Type u} {β : Type v} [inst : Preorder α] [
inst_1 : Preorder β] {f : α → β} {s : Set α},   AntitoneOn f s → MonotoneOn (⇑Or
derDual.toD…

--- 原说明 ---
The image of a measurable set under an antitone map is measurable.
-/
theorem MeasurableSet.image_of_antitoneOn [SecondCountableTopology β]
    (ht : MeasurableSet t) (hg : AntitoneOn g t) : MeasurableSet (g '' t) :=
  (ht.image_of_monotoneOn hg.dual_right :)

end LinearOrder

/-- The set of points for which a sequence of measurable functions converges to a given function
is measurable. -/
@[measurability]
/-
**MeasureTheory.measurableSet_tendsto_fun** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：MeasureTheory.measurableSet_tendsto_fun [MeasurableSpace γ] [Countable ι] 
{l : Filter ι} [l.IsCountablyGenerated] [TopologicalSpace γ] [SecondCountableTop
ology γ] [PseudoMetrizableSpace γ] [OpensMeasurableSpace γ] {f : ι -> β -> γ} (h
f : forall i, Measurable (f i)) {g : β -> γ} (hg : Measurable g) : MeasurableSet
 { x | Tendsto (fun n => f n x) l (𝓝 (g x)) }
参数：hf : forall i, Measurable (f i)；hg : Measurable g。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `tendsto_iff_dist_tendsto_zero`：tendsto_iff_dist_tendsto_zero {f : β -> α
} {x : Filter β} {a : α} : Tendsto f x (𝓝 a) ↔ Tendsto (fun b => dist (f b) a) x
 (𝓝 0)
· 使用引理 `measurableSet_tendsto`：measurableSet_tendsto {_ : MeasurableSpace β} [Me
asurableSpace γ] [Countable δ] {l : Filter δ} [l.IsCountablyGenerated] (l' : Fil
ter γ) [l'.…
· 使用定理 `FirstCountableTopology.nhds_generated_countable`：∀ {α : Type u} {t : Top
ologicalSpace α} [self : FirstCountableTopology α] (a : α), (nhds a).IsCountably
Generated
· 使用定理 `TopologicalSpace.PseudoMetrizableSpace.firstCountableTopology`：∀ {X : Ty
pe u_2} [inst : TopologicalSpace X] [h : TopologicalSpace.PseudoMetrizableSpace 
X], FirstCountableTopology X
· 使用定理 `PseudoEMetricSpace.pseudoMetrizableSpace`：∀ {α : Type u_2} [inst : Pseud
oEMetricSpace α], TopologicalSpace.PseudoMetrizableSpace α
· 使用定理 `BorelSpace.opensMeasurable`：∀ {α : Type u_6} [inst : TopologicalSpace α]
 [inst_1 : MeasurableSpace α] [BorelSpace α], OpensMeasurableSpace α
· 使用定理 `Measurable.dist`：Measurable.dist {f g : β -> α} (hf : Measurable f) (hg 
: Measurable g) : Measurable fun b => dist (f b) (g b)

--- 原说明 ---
The set of points for which a sequence of measurable functions converges to a gi
ven function
is measurable.
-/
lemma MeasureTheory.measurableSet_tendsto_fun [MeasurableSpace γ] [Countable ι]
    {l : Filter ι} [l.IsCountablyGenerated]
    [TopologicalSpace γ] [SecondCountableTopology γ] [PseudoMetrizableSpace γ]
    [OpensMeasurableSpace γ]
    {f : ι → β → γ} (hf : ∀ i, Measurable (f i)) {g : β → γ} (hg : Measurable g) :
    MeasurableSet { x | Tendsto (fun n ↦ f n x) l (𝓝 (g x)) } := by
  let := TopologicalSpace.pseudoMetrizableSpacePseudoMetric γ
  simp_rw [tendsto_iff_dist_tendsto_zero (f := fun n ↦ f n _)]
  exact measurableSet_tendsto (𝓝 0) (fun n ↦ (hf n).dist hg)

/-- The set of points for which a measurable sequence of functions converges is measurable. -/
@[measurability]
/-
**MeasureTheory.measurableSet_exists_tendsto** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：MeasureTheory.measurableSet_exists_tendsto [TopologicalSpace γ] [IsComplet
elyPseudoMetrizableSpace γ] [SecondCountableTopology γ] [MeasurableSpace γ] [hγ 
: OpensMeasurableSpace γ] [Countable ι] {l : Filter ι} [l.IsCountablyGenerated] 
{f : ι -> β -> γ} (hf : forall i, Measurable (f i)) : MeasurableSet { x | exists
 c, Tendsto (fun n => f n x) l (𝓝 c) }
参数：hf : forall i, Measurable (f i)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.eq_or_neBot`：eq_or_neBot (f : Filter α) : f = ⊥ ∨ NeBot f
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `and_true`：∀ (p : Prop), (p ∧ True) = p
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Filter.exists_antitone_basis`：exists_antitone_basis (f : Filter α) [f.Is
CountablyGenerated] : exists x : Nat -> Set α, f.HasAntitoneBasis x
· 使用定理 `TopologicalSpace.UpgradedIsCompletelyPseudoMetrizableSpace.toCompleteSpa
ce`：∀ {X : Type u_3} [self : TopologicalSpace.UpgradedIsCompletelyPseudoMetrizab
leSpace X], CompleteSpace X
· 使用定理 `Filter.HasAntitoneBasis.prod`：∀ {α : Type u_1} {β : Type u_2} {ι : Type 
u_6} [inst : LinearOrder ι] {f : Filter α} {g : Filter β} {s : ι → Set α}   {t :
 ι → Set β}, f.Has…
· 使用定理 `Filter.HasAntitoneBasis.map`：∀ {α : Type u_1} {β : Type u_2} {ι'' : Type
 u_6} [inst : Preorder ι''] {l : Filter α} {s : ι'' → Set α},   l.HasAntitoneBas
is s → ∀ (m : α →…
· 使用定理 `and_iff_right`：∀ {a b : Prop}, a → (a ∧ b ↔ b)
· 使用定理 `Filter.NeBot.map`：∀ {α : Type u_1} {β : Type u_2} {f : Filter α}, f.NeBo
t → ∀ (m : α → β), (Filter.map m f).NeBot
· 使用定理 `Filter.HasBasis.le_basis_iff`：∀ {α : Type u_1} {ι : Sort u_4} {ι' : Sort
 u_5} {l l' : Filter α} {p : ι → Prop} {s : ι → Set α} {p' : ι' → Prop}   {s' : 
ι' → Set α}, l.Has…
· 使用定理 `Filter.HasAntitoneBasis.toHasBasis`：∀ {α : Type u_1} {ι'' : Type u_6} [i
nst : Preorder ι''] {l : Filter α} {s : ι'' → Set α},   l.HasAntitoneBasis s → l
.HasBasis (fun x => True…
· 使用定理 `Metric.uniformity_basis_dist_inv_nat_succ`：uniformity_basis_dist_inv_nat
_succ : (𝓤 α).HasBasis (fun _ => True) fun n : Nat => { p : α × α | dist p.1 p.2
 < 1 / (↑n + 1) }
· 使用定理 `Set.ofPred_forall`：ofPred_forall (p : ι -> β -> Prop) : { x | forall i, 
p i x } = ⋂ i, { x | p i x }
· 使用定理 `MeasurableSet.biInter`：MeasurableSet.biInter {f : β -> Set α} {s : Set β
} (hs : s.Countable) (h : forall b in s, MeasurableSet (f b)) : MeasurableSet (⋂
 b in s, f …
· 使用定理 `Set.countable_univ`：countable_univ [Countable α] : (univ : Set α).Counta
ble
· 使用定理 `instCountableNat`：Countable ℕ
· 使用定理 `Set.ofPred_exists`：ofPred_exists (p : ι -> β -> Prop) : { x | exists i, 
p i x } = ⋃ i, { x | p i x }
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `MeasurableSet.iUnion`：∀ {α : Type u_1} {ι : Sort u_6} {m : MeasurableSpa
ce α} [Countable ι] ⦃f : ι → Set α⦄,   (∀ (b : ι), MeasurableSet (f b)) → Measur
ableSet (⋃…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Set.prod_image_image_eq`：prod_image_image_eq {m₁ : α -> γ} {m₂ : β -> δ}
 : (m₁ '' s) ×ˢ (m₂ '' t) = (fun p : α × β => (m₁ p.1, m₂ p.2)) '' s ×ˢ t
· 使用定理 `Set.iInter_congr_Prop`：iInter_congr_Prop {p q : Prop} {f₁ : p -> Set α} 
{f₂ : q -> Set α} (pq : p ↔ q) (f : forall x, f₁ (pq.mpr x) = f₂ x) : iInter f₁ 
= iInter f₂
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `Set.to_countable`：to_countable (s : Set α) [Countable s] : s.Countable
· 使用定理 `SetCoe.countable`：∀ {α : Type u} [Countable α] (s : Set α), Countable ↑s
· 使用定理 `measurableSet_lt`：measurableSet_lt [SecondCountableTopology α] [OrderClo
sedTopology α] {f g : δ -> α} (hf : Measurable f) (hg : Measurable g) : Measurab
leSet …
（共 36 条，此处仅展示前 30 条）

--- 原说明 ---
The set of points for which a measurable sequence of functions converges is meas
urable.
-/
theorem MeasureTheory.measurableSet_exists_tendsto [TopologicalSpace γ]
    [IsCompletelyPseudoMetrizableSpace γ] [SecondCountableTopology γ] [MeasurableSpace γ]
    [hγ : OpensMeasurableSpace γ] [Countable ι] {l : Filter ι}
    [l.IsCountablyGenerated] {f : ι → β → γ} (hf : ∀ i, Measurable (f i)) :
    MeasurableSet { x | ∃ c, Tendsto (fun n => f n x) l (𝓝 c) } := by
  rcases l.eq_or_neBot with rfl | hl
  · simp
  let := TopologicalSpace.upgradeIsCompletelyPseudoMetrizable γ
  rcases l.exists_antitone_basis with ⟨u, hu⟩
  simp_rw [← cauchy_map_iff_exists_tendsto]
  change MeasurableSet { x | _ ∧ _ }
  have : ∀ x, (map (f · x) l ×ˢ map (f · x) l).HasAntitoneBasis fun n =>
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
/-
**Measurable.tprod** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Measurable.tprod {f : ι -> X -> E} (h : forall i : ι, Measurable (f i)) : 
Measurable (fun x => ∏'[L] i : ι, f i x)
参数：h : forall i : ι, Measurable (f i)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.measurableSet_exists_tendsto`：MeasureTheory.measurableSet_
exists_tendsto [TopologicalSpace γ] [IsCompletelyPseudoMetrizableSpace γ] [Secon
dCountableTopology γ] [Measurabl…
· 使用定理 `BorelSpace.opensMeasurable`：∀ {α : Type u_6} [inst : TopologicalSpace α]
 [inst_1 : MeasurableSpace α] [BorelSpace α], OpensMeasurableSpace α
· 使用定理 `Finset.countable`：∀ {α : Type u_1} [Countable α], Countable (Finset α)
· 使用定理 `Finset.measurable_prod`：Finset.measurable_prod (s : Finset ι) (hf : fora
ll i in s, Measurable (f i)) : Measurable fun a => ∏ i in s, f i a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `tprod_eq_one_of_not_multipliable`：tprod_eq_one_of_not_multipliable (h : 
¬Multipliable f L) : ∏'[L] b, f b = 1
· 使用定理 `measurable_of_restrict_of_restrict_compl`：measurable_of_restrict_of_rest
rict_compl {f : α -> β} {s : Set α} (hs : MeasurableSet s) (h₁ : Measurable (s.d
omRestrict f)) (h₂ : Measurabl…
· 使用定理 `measurable_of_tendsto_metrizable'`：measurable_of_tendsto_metrizable' {ι}
 {f : ι -> α -> β} {g : α -> β} (u : Filter ι) [NeBot u] [IsCountablyGenerated u
] (hf : forall i, Measu…
· 使用定理 `TopologicalSpace.IsCompletelyPseudoMetrizableSpace.PseudoMetrizableSpace
`：∀ {X : Type u_1} [inst : TopologicalSpace X] [TopologicalSpace.IsCompletelyPse
udoMetrizableSpace X],   TopologicalSpace.PseudoMetrizableSpac…
· 使用定理 `SummationFilter.instNeBotFinsetFilterOfNeBot`：∀ {β : Type u_2} (L : Summ
ationFilter β) [L.NeBot], L.filter.NeBot
· 使用定理 `Measurable.fun_comp`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {x :
 MeasurableSpace α} {x_1 : MeasurableSpace β}   {x_2 : MeasurableSpace γ} {g : β
 → γ} {f …
· 使用定理 `Measurable.subtype_coe`：Measurable.subtype_coe {p : β -> Prop} {f : α ->
 Subtype p} (hf : Measurable f) : Measurable fun a : α => (f a : β)
· 使用定理 `measurable_id'`：measurable_id' {_ : MeasurableSpace α} : Measurable fun 
a : α => a
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `tendsto_pi_nhds`：tendsto_pi_nhds {f : Y -> forall i, A i} {g : forall i,
 A i} {u : Filter Y} : Tendsto f u (𝓝 g) ↔ forall x, Tendsto (fun i => f i x) u 
(𝓝 (g…
· 使用定理 `Multipliable.hasProd`：Multipliable.hasProd (ha : Multipliable f L) : Has
Prod f (∏'[L] b, f b) L
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `measurable_const`：measurable_const {_ : MeasurableSpace α} {_ : Measurab
leSpace β} {a : α} : Measurable fun _ : β => a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem Measurable.tprod {f : ι → X → E} (h : ∀ i : ι, Measurable (f i)) :
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
/-
**AEMeasurable.tprod** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：AEMeasurable.tprod {μ : MeasureTheory.Measure X} {f : ι -> X -> E} (h : fo
rall i : ι, AEMeasurable (f i) μ) : AEMeasurable (fun x => ∏'[L] i : ι, f i x) μ
参数：h : forall i : ι, AEMeasurable (f i) μ。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `Measurable.tprod`：Measurable.tprod {f : ι -> X -> E} (h : forall i : ι, 
Measurable (f i)) : Measurable (fun x => ∏'[L] i : ι, f i x)
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `MeasureTheory.ae_all_iff`：ae_all_iff {ι : Sort*} [Countable ι] {p : α ->
 ι -> Prop} : (forallᵐ a ∂μ, forall i, p a i) ↔ forall i, forallᵐ a ∂μ, p a i
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `tprod_congr`：tprod_congr {f g : β -> α} (hfg : forall b, f b = g b) : ∏'
[L] b, f b = ∏'[L] b, g b
· 使用定理 `Classical.choose_spec`：∀ {α : Sort u} {p : α → Prop} (h : ∃ x, p x), p (
Classical.choose h)
-/
theorem AEMeasurable.tprod {μ : MeasureTheory.Measure X} {f : ι → X → E}
    (h : ∀ i : ι, AEMeasurable (f i) μ) : AEMeasurable (fun x => ∏'[L] i : ι, f i x) μ := by
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
/-
**Measurable.tprod'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Measurable.tprod' {f : ι -> X -> E} (h : forall i : ι, Measurable (f i)) :
 Measurable (∏'[L] i : ι, f i)
参数：h : forall i : ι, Measurable (f i)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `tprod_def`：∀ {α : Type u_4} {β : Type u_5} [inst : CommMonoid α] [inst_1
 : TopologicalSpace α] (f : β → α) (L : SummationFilter β),   tprod f L =     i…
· 使用定理 `finprod_def'`：∀ {M : Type u_7} {α : Sort u_8} [inst : CommMonoid M] (f :
 α → M),   finprod f = if h : Function.HasFiniteMulSupport (f ∘ PLift.down) then
 ∏…
· 使用定理 `dif_pos`：∀ {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t : c → α
} {e : ¬c → α}, dite c t e = t hc
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用引理 `Finset.measurable_prod_apply`：Finset.measurable_prod_apply {f : ι -> α -
> β -> M} {g : α -> β} {s : Finset ι} (hf : forall i in s, Measurable ↿(f i)) (h
g : Measurable g) …
· 使用定理 `Set.mulIndicator.eq_1`：∀ {α : Type u_1} {M : Type u_3} [inst : One M] (s
 : Set α) (f : α → M) (x : α),   s.mulIndicator f x = if x ∈ s then f x else 1
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Measurable.fun_comp`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {x :
 MeasurableSpace α} {x_1 : MeasurableSpace β}   {x_2 : MeasurableSpace γ} {g : β
 → γ} {f …
· 使用定理 `Measurable.snd`：Measurable.snd {f : α -> β × γ} (hf : Measurable f) : Me
asurable fun a : α => (f a).2
· 使用定理 `measurable_id'`：measurable_id' {_ : MeasurableSpace α} : Measurable fun 
a : α => a
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
· 使用定理 `measurable_one`：measurable_one [One α] : Measurable (1 : β -> α)
· 使用定理 `measurable_id`：measurable_id {_ : MeasurableSpace α} : Measurable (@id α
)
· 使用定理 `dif_neg`：∀ {c : Prop} {h : Decidable c} (hnc : ¬c) {α : Sort u} {t : c →
 α} {e : ¬c → α}, dite c t e = e hnc
· 使用定理 `measurable_of_tendsto_metrizable'`：measurable_of_tendsto_metrizable' {ι}
 {f : ι -> α -> β} {g : α -> β} (u : Filter ι) [NeBot u] [IsCountablyGenerated u
] (hf : forall i, Measu…
· 使用定理 `SummationFilter.instNeBotFinsetFilterOfNeBot`：∀ {β : Type u_2} (L : Summ
ationFilter β) [L.NeBot], L.filter.NeBot
· 使用定理 `Exists.choose_spec`：∀ {α : Sort u_1} {p : α → Prop} (P : ∃ a, p a), p P.
choose
-/
theorem Measurable.tprod' {f : ι → X → E} (h : ∀ i : ι, Measurable (f i)) :
    Measurable (∏'[L] i : ι, f i) := by
  rw [tprod_def, finprod_def']
  split_ifs with hm
  any_goals exact measurable_one
  · refine Finset.measurable_prod_apply (fun _ _ ↦ ?_) measurable_id
    rw [Set.mulIndicator]
    split_ifs <;> fun_prop
  · exact measurable_of_tendsto_metrizable' L.filter (by fun_prop) hm.choose_spec

/-- The product of almost everywhere measurable functions is measurable. -/
@[to_additive (attr := fun_prop)
/-- The sum of almost everywhere measurable functions is measurable. -/]
/-
**AEMeasurable.tprod'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：AEMeasurable.tprod' {μ : MeasureTheory.Measure X} {f : ι -> X -> E} (h : f
orall i : ι, AEMeasurable (f i) μ) : AEMeasurable (∏'[L] i : ι, f i) μ
参数：h : forall i : ι, AEMeasurable (f i) μ。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `tprod_def`：∀ {α : Type u_4} {β : Type u_5} [inst : CommMonoid α] [inst_1
 : TopologicalSpace α] (f : β → α) (L : SummationFilter β),   tprod f L =     i…
· 使用定理 `finprod_def'`：∀ {M : Type u_7} {α : Sort u_8} [inst : CommMonoid M] (f :
 α → M),   finprod f = if h : Function.HasFiniteMulSupport (f ∘ PLift.down) then
 ∏…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `dif_pos`：∀ {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t : c → α
} {e : ¬c → α}, dite c t e = t hc
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用定理 `Finset.aemeasurable_prod`：Finset.aemeasurable_prod (s : Finset ι) (hf : 
forall i in s, AEMeasurable (f i) μ) : AEMeasurable (∏ i in s, f i) μ
· 使用定理 `Set.mulIndicator.eq_1`：∀ {α : Type u_1} {M : Type u_3} [inst : One M] (s
 : Set α) (f : α → M) (x : α),   s.mulIndicator f x = if x ∈ s then f x else 1
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
· 使用定理 `Measurable.aemeasurable`：Measurable.aemeasurable (h : Measurable f) : AE
Measurable f μ
· 使用定理 `measurable_one`：measurable_one [One α] : Measurable (1 : β -> α)
· 使用定理 `dif_neg`：∀ {c : Prop} {h : Decidable c} (hnc : ¬c) {α : Sort u} {t : c →
 α} {e : ¬c → α}, dite c t e = e hnc
· 使用定理 `aemeasurable_one`：aemeasurable_one [One β] : AEMeasurable (fun _ : α => 
(1 : β)) μ
· 使用定理 `aemeasurable_of_tendsto_metrizable_ae`：aemeasurable_of_tendsto_metrizabl
e_ae {ι} {μ : Measure α} {f : ι -> α -> β} {g : α -> β} (u : Filter ι) [hu : NeB
ot u] [IsCountablyGenerated…
· 使用定理 `SummationFilter.instNeBotFinsetFilterOfNeBot`：∀ {β : Type u_2} (L : Summ
ationFilter β) [L.NeBot], L.filter.NeBot
· 使用定理 `Filter.Eventually.of_forall`：∀ {α : Type u} {p : α → Prop} {f : Filter α
}, (∀ (x : α), p x) → ∀ᶠ (x : α) in f, p x
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `Filter.Tendsto.apply_nhds`：Filter.Tendsto.apply_nhds {l : Filter Y} {f :
 Y -> forall i, A i} {x : forall i, A i} (h : Tendsto f l (𝓝 x)) (i : ι) : Tends
to (fun a => f …
· 使用定理 `Exists.choose_spec`：∀ {α : Sort u_1} {p : α → Prop} (P : ∃ a, p a), p P.
choose
-/
theorem AEMeasurable.tprod' {μ : MeasureTheory.Measure X} {f : ι → X → E}
    (h : ∀ i : ι, AEMeasurable (f i) μ) : AEMeasurable (∏'[L] i : ι, f i) μ := by
  rw [tprod_def, finprod_def']
  split_ifs with hm
  any_goals exact aemeasurable_one
  · refine Finset.aemeasurable_prod _ (fun _ _ ↦ ?_)
    rw [Set.mulIndicator]
    split_ifs <;> fun_prop
  · apply aemeasurable_of_tendsto_metrizable_ae L.filter (f := fun s => ∏ i ∈ s, f i)
    · fun_prop
    · exact .of_forall fun x ↦ hm.choose_spec.apply_nhds x

end

end Measurable

section StandardBorelSpace

variable [MeasurableSpace α] [StandardBorelSpace α]

/-- If `s` is a measurable set in a standard Borel space, there is a compatible Polish topology
making `s` clopen. -/
/-
**MeasurableSet.isClopenable'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：MeasurableSet.isClopenable' {s : Set α} (hs : MeasurableSet s) : exists _ 
: TopologicalSpace α, BorelSpace α ∧ PolishSpace α ∧ IsClosed s ∧ IsOpen s
参数：hs : MeasurableSet s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasurableSet.isClopenable`：∀ {α : Type u_1} [inst : TopologicalSpace α]
 [PolishSpace α] [inst_2 : MeasurableSpace α] [BorelSpace α] {s : Set α},   Meas
urableSet s → Po…
· 使用定理 `UpgradedStandardBorel.toPolishSpace`：∀ {α : Type u_1} [self : UpgradedSt
andardBorel α], PolishSpace α
· 使用定理 `UpgradedStandardBorel.toBorelSpace`：∀ {α : Type u_1} [self : UpgradedSta
ndardBorel α], BorelSpace α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_borel_upgradeStandardBorel`：eq_borel_upgradeStandardBorel [Measurable
Space α] [StandardBorelSpace α] : ‹MeasurableSpace α› = @borel _ (upgradeStandar
dBorel α).toTopolog…
· 使用定理 `MeasureTheory.borel_eq_borel_of_le`：MeasureTheory.borel_eq_borel_of_le {
t t' : TopologicalSpace γ} (ht : PolishSpace (h

--- 原说明 ---
If `s` is a measurable set in a standard Borel space, there is a compatible Poli
sh topology
making `s` clopen.
-/
theorem MeasurableSet.isClopenable' {s : Set α} (hs : MeasurableSet s) :
    ∃ _ : TopologicalSpace α, BorelSpace α ∧ PolishSpace α ∧ IsClosed s ∧ IsOpen s := by
  let := upgradeStandardBorel α
  obtain ⟨t, hle, ht, s_clopen⟩ := hs.isClopenable
  refine ⟨t, ?_, ht, s_clopen⟩
  constructor
  rw [eq_borel_upgradeStandardBorel α, borel_eq_borel_of_le ht _ hle]
  infer_instance

/-- A measurable subspace of a standard Borel space is standard Borel. -/
/-
**MeasurableSet.standardBorel** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：MeasurableSet.standardBorel {s : Set α} (hs : MeasurableSet s) : StandardB
orelSpace s
参数：hs : MeasurableSet s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasurableSet.isClopenable'`：MeasurableSet.isClopenable' {s : Set α} (hs
 : MeasurableSet s) : exists _ : TopologicalSpace α, BorelSpace α ∧ PolishSpace 
α ∧ IsClosed s ∧ …
· 使用定理 `IsClosed.polishSpace`：∀ {α : Type u_1} [inst : TopologicalSpace α] [Poli
shSpace α] {s : Set α}, IsClosed s → PolishSpace ↑s
· 使用定理 `standardBorel_of_polish`：∀ {α : Type u_1} [inst : MeasurableSpace α] [τ 
: TopologicalSpace α] [BorelSpace α] [PolishSpace α],   StandardBorelSpace α

--- 原说明 ---
A measurable subspace of a standard Borel space is standard Borel.
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

/-- If two standard Borel spaces admit Borel measurable injections to one another,
then they are Borel isomorphic. -/
/-
**PolishSpace.borelSchroederBernstein** 是 Mathlib 中的一个定义，位于命名空间 `PolishSpace`。
形式化陈述：borelSchroederBernstein {f : α -> β} {g : β -> α} (fmeas : Measurable f) (
finj : Function.Injective f) (gmeas : Measurable g) (ginj : Function.Injective g
) : α ≃ᵐ β
参数：fmeas : Measurable f；finj : Function.Injective f；gmeas : Measurable g；ginj : 
Function.Injective g。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If two standard Borel spaces admit Borel measurable injections to one another,
then they are Borel isomorphic.
-/
noncomputable def borelSchroederBernstein {f : α → β} {g : β → α} (fmeas : Measurable f)
    (finj : Function.Injective f) (gmeas : Measurable g) (ginj : Function.Injective g) : α ≃ᵐ β :=
  letI := upgradeStandardBorel α
  letI := upgradeStandardBorel β
  (fmeas.measurableEmbedding finj).schroederBernstein (gmeas.measurableEmbedding ginj)

/-- Any uncountable standard Borel space is Borel isomorphic to the Cantor space `ℕ → Bool`. -/
/-
**PolishSpace.measurableEquivNatBoolOfNotCountable** 是 Mathlib 中的一个定义，位于命名空间 `Po
lishSpace`。
形式化陈述：measurableEquivNatBoolOfNotCountable (h : ¬Countable α) : α ≃ᵐ (Nat -> Boo
l)
参数：h : ¬Countable α。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Any uncountable standard Borel space is Borel isomorphic to the Cantor space `ℕ 
→ Bool`.
-/
noncomputable def measurableEquivNatBoolOfNotCountable (h : ¬Countable α) : α ≃ᵐ (ℕ → Bool) := by
  apply Nonempty.some
  let := upgradeStandardBorel α
  obtain ⟨f, -, fcts, finj⟩ :=
    isClosed_univ.exists_nat_bool_injection_of_not_countable (α := α)
      (by rwa [← countable_coe_iff, (Equiv.Set.univ _).countable_iff])
  obtain ⟨g, gmeas, ginj⟩ :=
    MeasurableSpace.measurable_injection_nat_bool_of_countablySeparated α
  exact ⟨borelSchroederBernstein gmeas ginj fcts.measurable finj⟩

/-- The **Borel Isomorphism Theorem**: Any two uncountable standard Borel spaces are
Borel isomorphic. -/
/-
**PolishSpace.measurableEquivOfNotCountable** 是 Mathlib 中的一个定义，位于命名空间 `PolishSpa
ce`。
形式化陈述：measurableEquivOfNotCountable (hα : ¬Countable α) (hβ : ¬Countable β) : α 
≃ᵐ β
参数：hα : ¬Countable α；hβ : ¬Countable β。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The **Borel Isomorphism Theorem**: Any two uncountable standard Borel spaces are
Borel isomorphic.
-/
noncomputable def measurableEquivOfNotCountable (hα : ¬Countable α) (hβ : ¬Countable β) : α ≃ᵐ β :=
  (measurableEquivNatBoolOfNotCountable hα).trans (measurableEquivNatBoolOfNotCountable hβ).symm

/-- The **Borel Isomorphism Theorem**: If two standard Borel spaces have the same cardinality,
they are Borel isomorphic. -/
/-
**PolishSpace.Equiv.measurableEquiv** 是 Mathlib 中的一个定义，位于命名空间 `PolishSpace.Equiv
`。
形式化陈述：{α : Type u_4} →   {β : Type u_6} →     [inst : MeasurableSpace α] →      
 [inst_1 : MeasurableSpace β] → [StandardBorelSpace α] → [StandardBorelSpace β] 
→ α ≃ β → α ≃ᵐ β
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The **Borel Isomorphism Theorem**: If two standard Borel spaces have the same ca
rdinality,
they are Borel isomorphic.
-/
noncomputable def Equiv.measurableEquiv (e : α ≃ β) : α ≃ᵐ β := by
  by_cases h : Countable α
  · letI := Countable.of_equiv α e
    refine ⟨e, ?_, ?_⟩ <;> apply measurable_of_countable
  refine measurableEquivOfNotCountable h ?_
  rwa [e.countable_iff] at h

end PolishSpace

