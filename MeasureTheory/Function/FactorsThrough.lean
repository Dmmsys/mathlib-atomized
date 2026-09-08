/-
Copyright (c) 2025 Etienne Marion. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Etienne Marion
-/
module

public import Mathlib.Probability.Process.Filtration

/-!
# Factorization of a map from measurability

Consider `f : X → Y` and `g : X → Z` and assume that `g` is measurable with respect to the pullback
along `f`. Then `g` factors through `f`, which means that (if `Z` is nonempty)
there exists `h : Y → Z` such that `g = h ∘ f`.

If `Z` is completely metrizable, the factorization map `h` can be taken to be measurable.
This is the content of the [Doob-Dynkin lemma](https://en.wikipedia.org/wiki/Doob–Dynkin_lemma):
see `exists_eq_measurable_comp`.
-/

public section

namespace MeasureTheory

open Filter Filtration Set TopologicalSpace

open scoped Topology

variable {X Y Z : Type*} [mY : MeasurableSpace Y] {f : X → Y} {g : X → Z}

section FactorsThrough

/-- If a function `g` is measurable with respect to the pullback along some function `f`,
then to prove `g x = g y` it is enough to prove `f x = f y`. -/
/-
**MeasureTheory._root_.Measurable.factorsThrough** 是 Mathlib 中的一个定理，位于命名空间 `Meas
ureTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If a function `g` is measurable with respect to the pullback along some function
 `f`,
then to prove `g x = g y` it is enough to prove `f x = f y`.
-/
theorem _root_.Measurable.factorsThrough [MeasurableSpace Z] [MeasurableSingletonClass Z]
    (hg : Measurable[mY.comap f] g) : g.FactorsThrough f := by
  refine fun x₁ x₂ h ↦ eq_of_mem_singleton ?_
  obtain ⟨s, -, hs⟩ := hg (measurableSet_singleton (g x₂))
  rw [← mem_preimage, ← hs, mem_preimage, h, ← mem_preimage, hs, mem_preimage, mem_singleton_iff]

/-- If a function `g` is strongly measurable with respect to the pullback along some function `f`,
then to prove `g x = g y` it is enough to prove `f x = f y`.

If `Z` is not empty there exists `h : Y → Z` such that `g = h ∘ f`.
If `Z` is also completely metrizable, the factorization map `h` can be taken to be measurable
(see `exists_eq_measurable_comp`). -/
/-
**MeasureTheory.StronglyMeasurable.factorsThrough** 是 Mathlib 中的一个定理，位于命名空间 `Mea
sureTheory.StronglyMeasurable`。
形式化陈述：∀ {X : Type u_1} {Y : Type u_2} {Z : Type u_3} [mY : MeasurableSpace Y] {f
 : X → Y} {g : X → Z}   [inst : TopologicalSpace Z] [TopologicalSpace.PseudoMetr
izableSpace Z] [T1Space Z],   MeasureTheory.StronglyMeasurable g → Function.Fact
orsThrough g f
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Measurable.factorsThrough`：∀ {X : Type u_1} {Y : Type u_2} {Z : Type u_3
} [mY : MeasurableSpace Y] {f : X → Y} {g : X → Z}   [inst : MeasurableSpace Z] 
[MeasurableSing…
· 使用定理 `OpensMeasurableSpace.toMeasurableSingletonClass`：∀ {α : Type u_1} [inst 
: TopologicalSpace α] [inst_1 : MeasurableSpace α] [OpensMeasurableSpace α] [T1S
pace α],   MeasurableSingletonClass α
· 使用定理 `BorelSpace.opensMeasurable`：∀ {α : Type u_6} [inst : TopologicalSpace α]
 [inst_1 : MeasurableSpace α] [BorelSpace α], OpensMeasurableSpace α
· 使用定理 `MeasureTheory.StronglyMeasurable.measurable`：∀ {α : Type u_1} {β : Type 
u_2} {f : α → β} {x : MeasurableSpace α} [inst : TopologicalSpace β]   [Topologi
calSpace.PseudoMetrizableSpace β]…

--- 原说明 ---
If a function `g` is strongly measurable with respect to the pullback along some
 function `f`,
then to prove `g x = g y` it is enough to prove `f x = f y`.

If `Z` is not empty there exists `h : Y → Z` such that `g = h ∘ f`.
If `Z` is also completely metrizable, the factorization map `h` can be taken to 
be measurable
(see `exists_eq_measurable_comp`).
-/
theorem StronglyMeasurable.factorsThrough [TopologicalSpace Z]
    [PseudoMetrizableSpace Z] [T1Space Z] (hg : StronglyMeasurable[mY.comap f] g) :
    g.FactorsThrough f := by
  borelize Z
  exact hg.measurable.factorsThrough

set_option backward.isDefEq.respectTransparency false in
/-- If a function `g` is strongly measurable with respect to the pullback along some function `f`,
then there exists some strongly measurable function `h : Y → Z` such that `g = h ∘ f`. -/
/-
**MeasureTheory.StronglyMeasurable.exists_eq_measurable_comp** 是 Mathlib 中的一个定理，
位于命名空间 `MeasureTheory.StronglyMeasurable`。
形式化陈述：∀ {X : Type u_1} {Y : Type u_2} {Z : Type u_3} [mY : MeasurableSpace Y] {f
 : X → Y} {g : X → Z} [Nonempty Z]   [inst : TopologicalSpace Z] [TopologicalSpa
ce.IsCompletelyMetrizableSpace Z],   MeasureTheory.StronglyMeasurable g → ∃ h, M
easureTheory.StronglyMeasurable h ∧ g = h ∘ f
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.StronglyMeasurable.induction'`：induction' [MeasurableSpace
 α] [Nonempty β] [TopologicalSpace β] {P : (f : α -> β) -> StronglyMeasurable f 
-> Prop} (const : forall (c), P (…
· 使用定理 `MeasureTheory.stronglyMeasurable_const`：stronglyMeasurable_const {b : β}
 : StronglyMeasurable fun _ : α => b
· 使用定理 `MeasureTheory.StronglyMeasurable.piecewise`：∀ {α : Type u_1} {β : Type u
_2} {f g : α → β} {m : MeasurableSpace α} [inst : TopologicalSpace β] {s : Set α
}   {x : DecidablePred fun x => …
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Set.piecewise_comp`：piecewise_comp (f g : α -> γ) (h : β -> α) : letI : 
DecidablePred (· in h ⁻¹' s)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.StronglyMeasurable.limUnder`：∀ {ι : Type u_1} {X : Type u_
2} {E : Type u_3} [inst : MeasurableSpace X] [inst_1 : TopologicalSpace E] [Coun
table ι]   {l : Filter ι} [l.Is…
· 使用定理 `instCountableNat`：Countable ℕ
· 使用定理 `instDiscreteTopologyNat`：DiscreteTopology ℕ
· 使用定理 `TopologicalSpace.SecondCountableTopology.to_separableSpace`：∀ {α : Type 
u} [t : TopologicalSpace α] [SecondCountableTopology α], TopologicalSpace.Separa
bleSpace α
· 使用定理 `TopologicalSpace.instSecondCountableTopologyOfLindelofSpaceOfPseudoMetri
zableSpace`：∀ (X : Type u_5) [inst : TopologicalSpace X] [LindelofSpace X] [Topo
logicalSpace.PseudoMetrizableSpace X],   SecondCountableTopology X
· 使用定理 `Countable.LindelofSpace`：∀ {X : Type u} [inst : TopologicalSpace X] [Cou
ntable X], LindelofSpace X
· 使用定理 `PseudoEMetricSpace.pseudoMetrizableSpace`：∀ {α : Type u_2} [inst : Pseud
oEMetricSpace α], TopologicalSpace.PseudoMetrizableSpace α
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Function.comp_apply`：∀ {β : Sort u_1} {δ : Sort u_2} {α : Sort u_3} {f :
 β → δ} {g : α → β} {x : α}, (f ∘ g) x = f (g x)
· 使用定理 `Filter.Tendsto.limUnder_eq`：Filter.Tendsto.limUnder_eq {x : X} {f : Filt
er Y} [NeBot f] {g : Y -> X} (h : Tendsto g f (𝓝 x)) : @limUnder _ _ _ ⟨x⟩ f g =
 x
· 使用定理 `TopologicalSpace.t2Space_of_metrizableSpace`：∀ {X : Type u_2} [inst : To
pologicalSpace X] [TopologicalSpace.MetrizableSpace X], T2Space X
· 使用定理 `TopologicalSpace.IsCompletelyMetrizableSpace.MetrizableSpace`：∀ {X : Typ
e u_1} [inst : TopologicalSpace X] [TopologicalSpace.IsCompletelyMetrizableSpace
 X],   TopologicalSpace.MetrizableSpace X
· 使用定理 `instIsDirectedOrder`：∀ {R : Type u_3} [inst : Semiring R] [inst_1 : Part
ialOrder R] [IsOrderedRing R] [Archimedean R], IsDirectedOrder R
· 使用定理 `instArchimedeanNat`：Archimedean ℕ
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Classical.choose_spec`：∀ {α : Sort u} {p : α → Prop} (h : ∃ x, p x), p (
Classical.choose h)

--- 原说明 ---
If a function `g` is strongly measurable with respect to the pullback along some
 function `f`,
then there exists some strongly measurable function `h : Y → Z` such that `g = h
 ∘ f`.
-/
theorem StronglyMeasurable.exists_eq_measurable_comp [Nonempty Z] [TopologicalSpace Z]
    [IsCompletelyMetrizableSpace Z] (hg : StronglyMeasurable[mY.comap f] g) :
    ∃ h : Y → Z, StronglyMeasurable h ∧ g = h ∘ f := by
  let mX : MeasurableSpace X := mY.comap f
  induction g, hg using StronglyMeasurable.induction' with
  | const z => exact ⟨fun _ ↦ z, stronglyMeasurable_const, rfl⟩
  | @pcw g₁ g₂ s hg₁ hg₂ hs h₁ h₂ =>
    obtain ⟨t, ht, rfl⟩ := hs
    obtain ⟨h₁, mh₁, rfl⟩ := h₁
    obtain ⟨h₂, mh₂, rfl⟩ := h₂
    classical
    exact ⟨t.piecewise h₁ h₂, mh₁.piecewise ht mh₂, by rw [piecewise_comp]⟩
  | @lim g i hg hi h₁ h₂ =>
    choose h mh hh using h₁
    refine ⟨fun y ↦ limUnder atTop (h · y), StronglyMeasurable.limUnder mh, ?_⟩
    ext x
    rw [Function.comp_apply, Tendsto.limUnder_eq]
    simp_all

/-- If a function `g` is measurable with respect to the pullback along some function `f`,
then there exists some measurable function `h : Y → Z` such that `g = h ∘ f`. -/
/-
**MeasureTheory._root_.Measurable.exists_eq_measurable_comp** 是 Mathlib 中的一个定理，位
于命名空间 `MeasureTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If a function `g` is measurable with respect to the pullback along some function
 `f`,
then there exists some measurable function `h : Y → Z` such that `g = h ∘ f`.
-/
theorem _root_.Measurable.exists_eq_measurable_comp [Nonempty Z] [MeasurableSpace Z]
    [StandardBorelSpace Z] (hg : Measurable[mY.comap f] g) :
    ∃ h : Y → Z, Measurable h ∧ g = h ∘ f := by
  let := upgradeStandardBorel Z
  obtain ⟨h, mh, hh⟩ := hg.stronglyMeasurable.exists_eq_measurable_comp
  exact ⟨h, mh.measurable, hh⟩

end FactorsThrough

variable {ι : Type*} {X : ι → Type*} [∀ i, MeasurableSpace (X i)] {f : (Π i, X i) → Z}

section piLE

variable [Preorder ι] {i : ι}

/-- If a function is measurable with respect to the σ-algebra generated by the
first coordinates, then it only depends on those first coordinates. -/
/-
**MeasureTheory._root_.Measurable.dependsOn_of_piLE** 是 Mathlib 中的一个定理，位于命名空间 `M
easureTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If a function is measurable with respect to the σ-algebra generated by the
first coordinates, then it only depends on those first coordinates.
-/
theorem _root_.Measurable.dependsOn_of_piLE [MeasurableSpace Z] [MeasurableSingletonClass Z]
    (hf : Measurable[piLE i] f) : DependsOn f (Iic i) :=
  dependsOn_iff_factorsThrough.2 hf.factorsThrough

/-- If a function is strongly measurable with respect to the σ-algebra generated by the
first coordinates, then it only depends on those first coordinates. -/
/-
**MeasureTheory.StronglyMeasurable.dependsOn_of_piLE** 是 Mathlib 中的一个定理，位于命名空间 `
MeasureTheory.StronglyMeasurable`。
形式化陈述：∀ {Z : Type u_3} {ι : Type u_4} {X : ι → Type u_5} [inst : (i : ι) → Measu
rableSpace (X i)] {f : ((i : ι) → X i) → Z}   [inst_1 : Preorder ι] {i : ι} [ins
t_2 : TopologicalSpace Z] [TopologicalSpace.PseudoMetrizableSpace Z] [T1Space Z]
,   MeasureTheory.StronglyMeasurable f → DependsOn f (Set.Iic i)
参数：i : ι；X i；(i : ι) → X i；Set.Iic i。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `dependsOn_iff_factorsThrough`：dependsOn_iff_factorsThrough {f : (Π i, α 
i) -> β} {s : Set ι} : DependsOn f s ↔ FactorsThrough f s.domRestrict
· 使用定理 `MeasureTheory.StronglyMeasurable.factorsThrough`：∀ {X : Type u_1} {Y : T
ype u_2} {Z : Type u_3} [mY : MeasurableSpace Y] {f : X → Y} {g : X → Z}   [inst
 : TopologicalSpace Z] [TopologicalSp…

--- 原说明 ---
If a function is strongly measurable with respect to the σ-algebra generated by 
the
first coordinates, then it only depends on those first coordinates.
-/
theorem StronglyMeasurable.dependsOn_of_piLE [TopologicalSpace Z] [PseudoMetrizableSpace Z]
    [T1Space Z] (hf : StronglyMeasurable[piLE i] f) : DependsOn f (Iic i) :=
  dependsOn_iff_factorsThrough.2 hf.factorsThrough

end piLE

section piFinset

variable {s : Finset ι}

/-- If a function is measurable with respect to the σ-algebra generated by the
first coordinates, then it only depends on those first coordinates. -/
/-
**MeasureTheory._root_.Measurable.dependsOn_of_piFinset** 是 Mathlib 中的一个定理，位于命名空
间 `MeasureTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If a function is measurable with respect to the σ-algebra generated by the
first coordinates, then it only depends on those first coordinates.
-/
theorem _root_.Measurable.dependsOn_of_piFinset [MeasurableSpace Z] [MeasurableSingletonClass Z]
    (hf : Measurable[piFinset s] f) : DependsOn f s :=
  dependsOn_iff_factorsThrough.2 hf.factorsThrough

/-- If a function is strongly measurable with respect to the σ-algebra generated by the
first coordinates, then it only depends on those first coordinates. -/
/-
**MeasureTheory.StronglyMeasurable.dependsOn_of_piFinset** 是 Mathlib 中的一个定理，位于命名
空间 `MeasureTheory.StronglyMeasurable`。
形式化陈述：∀ {Z : Type u_3} {ι : Type u_4} {X : ι → Type u_5} [inst : (i : ι) → Measu
rableSpace (X i)] {f : ((i : ι) → X i) → Z}   {s : Finset ι} [inst_1 : Topologic
alSpace Z] [TopologicalSpace.PseudoMetrizableSpace Z] [T1Space Z],   MeasureTheo
ry.StronglyMeasurable f → DependsOn f ↑s
参数：i : ι；X i；(i : ι) → X i。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `dependsOn_iff_factorsThrough`：dependsOn_iff_factorsThrough {f : (Π i, α 
i) -> β} {s : Set ι} : DependsOn f s ↔ FactorsThrough f s.domRestrict
· 使用定理 `MeasureTheory.StronglyMeasurable.factorsThrough`：∀ {X : Type u_1} {Y : T
ype u_2} {Z : Type u_3} [mY : MeasurableSpace Y] {f : X → Y} {g : X → Z}   [inst
 : TopologicalSpace Z] [TopologicalSp…

--- 原说明 ---
If a function is strongly measurable with respect to the σ-algebra generated by 
the
first coordinates, then it only depends on those first coordinates.
-/
theorem StronglyMeasurable.dependsOn_of_piFinset [TopologicalSpace Z] [PseudoMetrizableSpace Z]
    [T1Space Z] (hf : StronglyMeasurable[piFinset s] f) : DependsOn f s :=
  dependsOn_iff_factorsThrough.2 hf.factorsThrough

end piFinset

end MeasureTheory

