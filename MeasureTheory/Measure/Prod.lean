/-
Copyright (c) 2020 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn
-/
module

public import Mathlib.MeasureTheory.Measure.GiryMonad
public import Mathlib.MeasureTheory.Measure.OpenPos
public import Mathlib.MeasureTheory.Measure.Doubling

/-!
# The product measure

In this file we define and prove properties about the binary product measure. If `α` and `β` have
s-finite measures `μ` resp. `ν` then `α × β` can be equipped with an s-finite measure `μ.prod ν`
that satisfies `(μ.prod ν) s = ∫⁻ x, ν {y | (x, y) ∈ s} ∂μ`.
We also have `(μ.prod ν) (s ×ˢ t) = μ s * ν t`, i.e. the measure of a rectangle is the product of
the measures of the sides.

We also prove Tonelli's theorem.

## Main definition

* `MeasureTheory.Measure.prod`: The product of two measures.

## Main results

* `MeasureTheory.Measure.prod_apply` states `μ.prod ν s = ∫⁻ x, ν {y | (x, y) ∈ s} ∂μ`
  for measurable `s`. `MeasureTheory.Measure.prod_apply_symm` is the reversed version.
* `MeasureTheory.Measure.prod_prod` states `μ.prod ν (s ×ˢ t) = μ s * ν t` for measurable sets
  `s` and `t`.
* `MeasureTheory.lintegral_prod`: Tonelli's theorem. It states that for a measurable function
  `α × β → ℝ≥0∞` we have `∫⁻ z, f z ∂(μ.prod ν) = ∫⁻ x, ∫⁻ y, f (x, y) ∂ν ∂μ`. The version
  for functions `α → β → ℝ≥0∞` is reversed, and called `lintegral_lintegral`. Both versions have
  a variant with `_symm` appended, where the order of integration is reversed.
  The lemma `Measurable.lintegral_prod_right'` states that the inner integral of the right-hand side
  is measurable.

## Implementation Notes

Many results are proven twice, once for functions in curried form (`α → β → γ`) and one for
functions in uncurried form (`α × β → γ`). The former often has an assumption
`Measurable (uncurry f)`, which could be inconvenient to discharge, but for the latter it is more
common that the function has to be given explicitly, since Lean cannot synthesize the function by
itself. We name the lemmas about the uncurried form with a prime.
Tonelli's theorem has a different naming scheme, since the version for the uncurried version is
reversed.

## Tags

product measure, Tonelli's theorem, Fubini-Tonelli theorem
-/

@[expose] public section


noncomputable section

open Topology ENNReal MeasureTheory Set Function Real ENNReal MeasurableSpace MeasureTheory.Measure

open TopologicalSpace hiding generateFrom

open Filter hiding prod_eq map

variable {α β γ : Type*}

variable [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ]
variable {μ μ' : Measure α} {ν ν' : Measure β} {τ : Measure γ}

/-- If `ν` is a finite measure, and `s ⊆ α × β` is measurable, then `x ↦ ν { y | (x, y) ∈ s }` is
  a measurable function. `measurable_measure_prodMk_left` is strictly more general. -/
/-
**measurable_measure_prodMk_left_finite** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：measurable_measure_prodMk_left_finite [IsFiniteMeasure ν] {s : Set (α × β)
} (hs : MeasurableSet s) : Measurable fun x => ν (Prod.mk x ⁻¹' s)
参数：α × β；hs : MeasurableSet s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasurableSpace.induction_on_inter`：induction_on_inter {m : MeasurableSp
ace α} {C : forall s : Set α, MeasurableSet s -> Prop} {s : Set (Set α)} (h_eq :
 m = generateFrom s) (h_…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `generateFrom_prod`：generateFrom_prod : generateFrom (image2 (· ×ˢ ·) { s
 : Set α | MeasurableSet s } { t : Set β | MeasurableSet t }) = Prod.instMeasura
bleSpac…
· 使用引理 `isPiSystem_prod`：isPiSystem_prod : IsPiSystem (image2 (· ×ˢ ·) { s : Set
 α | MeasurableSet s } { t : Set β | MeasurableSet t })
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `MeasureTheory.measure_empty`：measure_empty : μ ∅ = 0
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `Set.mk_preimage_prod_right_eq_if`：mk_preimage_prod_right_eq_if [Decidabl
ePred (· in s)] : Prod.mk a ⁻¹' s ×ˢ t = if a in s then t else ∅
· 使用定理 `MeasureTheory.measure_if`：measure_if {x : β} {t : Set β} {s : Set α} [De
cidable (x in t)] : μ (if x in t then s else ∅) = indicator t (fun _ => μ s) x
· 使用定理 `Measurable.indicator`：Measurable.indicator [Zero β] (hf : Measurable f) 
(hs : MeasurableSet s) : Measurable (s.indicator f)
· 使用定理 `measurable_const`：measurable_const {_ : MeasurableSpace α} {_ : Measurab
leSpace β} {a : α} : Measurable fun _ : β => a
· 使用定理 `MeasureTheory.measure_compl`：measure_compl (h₁ : MeasurableSet s) (h_fin
 : μ s != ∞) : μ sᶜ = μ univ - μ s
· 使用定理 `measurable_prodMk_left`：measurable_prodMk_left {x : α} : Measurable (@Pr
od.mk _ β x)
· 使用定理 `MeasureTheory.measure_ne_top`：measure_ne_top (μ : Measure α) [IsFiniteMe
asure μ] (s : Set α) : μ s != ∞
· 使用定理 `Measurable.const_sub`：∀ {G : Type u_2} {α : Type u_3} [inst : Measurable
Space G] [inst_1 : Sub G] {m : MeasurableSpace α} {f : α → G}   [MeasurableSub G
], Measura…
· 使用定理 `MeasurableSub₂.toMeasurableSub`：∀ {G : Type u_2} [inst : MeasurableSpace
 G] [inst_1 : Sub G] [MeasurableSub₂ G], MeasurableSub G
· 使用定理 `Set.preimage_iUnion`：preimage_iUnion {f : α -> β} {s : ι -> Set β} : (f 
⁻¹' ⋃ i, s i) = ⋃ i, f ⁻¹' s i
· 使用定理 `MeasureTheory.measure_iUnion`：measure_iUnion {m0 : MeasurableSpace α} {μ
 : Measure α} [Countable ι] {f : ι -> Set α} (hn : Pairwise (Disjoint on f)) (h 
: forall i, Measur…
· 使用定理 `instCountableNat`：Countable ℕ
· 使用定理 `Pairwise.mono`：Pairwise.mono (h : t subseteq s) (hs : s.Pairwise r) : t.
Pairwise r
· 使用定理 `Disjoint.preimage`：Disjoint.preimage (f : α -> β) {s t : Set β} (h : Dis
joint s t) : Disjoint (f ⁻¹' s) (f ⁻¹' t)
· 使用定理 `Measurable.tsum`：∀ {X : Type u_6} {E : Type u_7} {ι : Type u_8} [inst : 
MeasurableSpace X] [inst_1 : AddCommMonoid E]   [inst_2 : TopologicalSpace E] [T
opolo…
· 使用定理 `TopologicalSpace.IsCompletelyMetrizableSpace.toIsCompletelyPseudoMetriza
bleSpace`：∀ {X : Type u_1} [inst : TopologicalSpace X] [TopologicalSpace.IsCompl
etelyMetrizableSpace X],   TopologicalSpace.IsCompletelyPseudoMetrizab…
· 使用定理 `PolishSpace.toIsCompletelyMetrizableSpace`：∀ {α : Type u_3} {h : Topolog
icalSpace α} [self : PolishSpace α], TopologicalSpace.IsCompletelyMetrizableSpac
e α
· 使用定理 `PolishSpace.instENNReal`：PolishSpace ENNReal
· 使用定理 `ENNReal.instSecondCountableTopology`：SecondCountableTopology ENNReal
· 使用定理 `ContinuousAdd.measurableMul₂`：∀ {γ : Type u_3} [inst : TopologicalSpace 
γ] [inst_1 : MeasurableSpace γ] [BorelSpace γ] [SecondCountableTopology γ]   [in
st_4 : Add γ] [Con…
（共 33 条，此处仅展示前 30 条）

--- 原说明 ---
If `ν` is a finite measure, and `s ⊆ α × β` is measurable, then `x ↦ ν { y | (x,
 y) ∈ s }` is
  a measurable function. `measurable_measure_prodMk_left` is strictly more gener
al.
-/
theorem measurable_measure_prodMk_left_finite [IsFiniteMeasure ν] {s : Set (α × β)}
    (hs : MeasurableSet s) : Measurable fun x => ν (Prod.mk x ⁻¹' s) := by
  induction s, hs using induction_on_inter generateFrom_prod.symm isPiSystem_prod with
  | empty => simp
  | basic s hs =>
    obtain ⟨s, hs, t, -, rfl⟩ := hs
    classical simpa only [mk_preimage_prod_right_eq_if, measure_if]
      using measurable_const.indicator hs
  | compl s hs ihs =>
    simp_rw [preimage_compl, measure_compl (measurable_prodMk_left hs) (measure_ne_top ν _)]
    exact ihs.const_sub _
  | iUnion f hfd hfm ihf =>
    have (a : α) : ν (Prod.mk a ⁻¹' ⋃ i, f i) = ∑' i, ν (Prod.mk a ⁻¹' f i) := by
      rw [preimage_iUnion, measure_iUnion]
      exacts [hfd.mono fun _ _ ↦ .preimage _, fun i ↦ measurable_prodMk_left (hfm i)]
    simpa only [this] using Measurable.tsum ihf

/-- If `ν` is an s-finite measure, and `s ⊆ α × β` is measurable, then `x ↦ ν { y | (x, y) ∈ s }`
is a measurable function.

Not true without the s-finite assumption: on `ℝ × ℝ` with the product sigma-algebra, let `s` be the
diagonal and let `ν` be an uncountable sum of Dirac measures (all Dirac measures for points in a
set `t`). Then `ν (Prod.mk x ⁻¹' s) = ν {x} = if x ∈ t then 1 else 0`. If `t` is chosen
non-measurable, this will not be measurable. -/
/-
**measurable_measure_prodMk_left** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：measurable_measure_prodMk_left [SFinite ν] {s : Set (α × β)} (hs : Measura
bleSet s) : Measurable fun x => ν (Prod.mk x ⁻¹' s)
参数：α × β；hs : MeasurableSet s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `MeasureTheory.sum_sfiniteSeq`：sum_sfiniteSeq (μ : Measure α) [h : SFinit
e μ] : sum (sfiniteSeq μ) = μ
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `MeasureTheory.Measure.sum_apply_of_countable`：sum_apply_of_countable [Co
untable ι] (f : ι -> Measure α) (s : Set α) : sum f s = ∑' i, f i s
· 使用定理 `instCountableNat`：Countable ℕ
· 使用定理 `Measurable.tsum`：∀ {X : Type u_6} {E : Type u_7} {ι : Type u_8} [inst : 
MeasurableSpace X] [inst_1 : AddCommMonoid E]   [inst_2 : TopologicalSpace E] [T
opolo…
· 使用定理 `TopologicalSpace.IsCompletelyMetrizableSpace.toIsCompletelyPseudoMetriza
bleSpace`：∀ {X : Type u_1} [inst : TopologicalSpace X] [TopologicalSpace.IsCompl
etelyMetrizableSpace X],   TopologicalSpace.IsCompletelyPseudoMetrizab…
· 使用定理 `PolishSpace.toIsCompletelyMetrizableSpace`：∀ {α : Type u_3} {h : Topolog
icalSpace α} [self : PolishSpace α], TopologicalSpace.IsCompletelyMetrizableSpac
e α
· 使用定理 `PolishSpace.instENNReal`：PolishSpace ENNReal
· 使用定理 `ENNReal.instSecondCountableTopology`：SecondCountableTopology ENNReal
· 使用定理 `ContinuousAdd.measurableMul₂`：∀ {γ : Type u_3} [inst : TopologicalSpace 
γ] [inst_1 : MeasurableSpace γ] [BorelSpace γ] [SecondCountableTopology γ]   [in
st_4 : Add γ] [Con…
· 使用定理 `ENNReal.instContinuousAdd`：ContinuousAdd ENNReal
· 使用定理 `SummationFilter.instNeBotUnconditional`：∀ (β : Type u_2), (SummationFilt
er.unconditional β).NeBot
· 使用定理 `SummationFilter.instIsCountablyGeneratedFinsetFilterUnconditionalOfCount
able`：∀ (β : Type u_2) [Countable β], (SummationFilter.unconditional β).filter.I
sCountablyGenerated
· 使用定理 `measurable_measure_prodMk_left_finite`：measurable_measure_prodMk_left_fi
nite [IsFiniteMeasure ν] {s : Set (α × β)} (hs : MeasurableSet s) : Measurable f
un x => ν (Prod.mk x ⁻¹' s)

--- 原说明 ---
If `ν` is an s-finite measure, and `s ⊆ α × β` is measurable, then `x ↦ ν { y | 
(x, y) ∈ s }`
is a measurable function.

Not true without the s-finite assumption: on `ℝ × ℝ` with the product sigma-alge
bra, let `s` be the
diagonal and let `ν` be an uncountable sum of Dirac measures (all Dirac measures
 for points in a
set `t`). Then `ν (Prod.mk x ⁻¹' s) = ν {x} = if x ∈ t then 1 else 0`. If `t` is
 chosen
non-measurable, this will not be measurable.
-/
theorem measurable_measure_prodMk_left [SFinite ν] {s : Set (α × β)} (hs : MeasurableSet s) :
    Measurable fun x => ν (Prod.mk x ⁻¹' s) := by
  rw [← sum_sfiniteSeq ν]
  simp_rw [Measure.sum_apply_of_countable]
  exact Measurable.tsum (fun i ↦ measurable_measure_prodMk_left_finite hs)

/-- If `μ` is an s-finite measure, and `s ⊆ α × β` is measurable, then `y ↦ μ { x | (x, y) ∈ s }` is
  a measurable function. -/
/-
**measurable_measure_prodMk_right** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：measurable_measure_prodMk_right {μ : Measure α} [SFinite μ] {s : Set (α × 
β)} (hs : MeasurableSet s) : Measurable fun y => μ ((fun x => (x, y)) ⁻¹' s)
参数：α × β；hs : MeasurableSet s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `measurable_measure_prodMk_left`：measurable_measure_prodMk_left [SFinite 
ν] {s : Set (α × β)} (hs : MeasurableSet s) : Measurable fun x => ν (Prod.mk x ⁻
¹' s)
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `measurableSet_swap_iff`：measurableSet_swap_iff {s : Set (α × β)} : Measu
rableSet (Prod.swap ⁻¹' s) ↔ MeasurableSet s

--- 原说明 ---
If `μ` is an s-finite measure, and `s ⊆ α × β` is measurable, then `y ↦ μ { x | 
(x, y) ∈ s }` is
  a measurable function.
-/
theorem measurable_measure_prodMk_right {μ : Measure α} [SFinite μ] {s : Set (α × β)}
    (hs : MeasurableSet s) : Measurable fun y => μ ((fun x => (x, y)) ⁻¹' s) :=
  measurable_measure_prodMk_left (measurableSet_swap_iff.mpr hs)
/-
**Measurable.map_prodMk_left** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Measurable.map_prodMk_left [SFinite ν] : Measurable fun x : α => map (Prod
.mk x) ν
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.measurable_of_measurable_coe`：measurable_of_measur
able_coe (f : β -> Measure α) (h : forall (s : Set α), MeasurableSet s -> Measur
able fun b => f b s) : Measurable f
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `MeasureTheory.Measure.map_apply`：map_apply (hf : Measurable f) {s : Set 
β} (hs : MeasurableSet s) : μ.map f s = μ (f ⁻¹' s)
· 使用定理 `measurable_prodMk_left`：measurable_prodMk_left {x : α} : Measurable (@Pr
od.mk _ β x)
· 使用定理 `measurable_measure_prodMk_left`：measurable_measure_prodMk_left [SFinite 
ν] {s : Set (α × β)} (hs : MeasurableSet s) : Measurable fun x => ν (Prod.mk x ⁻
¹' s)
-/
theorem Measurable.map_prodMk_left [SFinite ν] :
    Measurable fun x : α => map (Prod.mk x) ν := by
  apply measurable_of_measurable_coe; intro s hs
  simp_rw [map_apply measurable_prodMk_left hs]
  exact measurable_measure_prodMk_left hs
/-
**Measurable.map_prodMk_right** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Measurable.map_prodMk_right {μ : Measure α} [SFinite μ] : Measurable fun y
 : β => map (fun x : α => (x, y)) μ
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.measurable_of_measurable_coe`：measurable_of_measur
able_coe (f : β -> Measure α) (h : forall (s : Set α), MeasurableSet s -> Measur
able fun b => f b s) : Measurable f
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `MeasureTheory.Measure.map_apply`：map_apply (hf : Measurable f) {s : Set 
β} (hs : MeasurableSet s) : μ.map f s = μ (f ⁻¹' s)
· 使用定理 `measurable_prodMk_right`：measurable_prodMk_right {y : β} : Measurable fu
n x : α => (x, y)
· 使用定理 `measurable_measure_prodMk_right`：measurable_measure_prodMk_right {μ : Me
asure α} [SFinite μ] {s : Set (α × β)} (hs : MeasurableSet s) : Measurable fun y
 => μ ((fun x => (x, …
-/
theorem Measurable.map_prodMk_right {μ : Measure α} [SFinite μ] :
    Measurable fun y : β => map (fun x : α => (x, y)) μ := by
  apply measurable_of_measurable_coe; intro s hs
  simp_rw [map_apply measurable_prodMk_right hs]
  exact measurable_measure_prodMk_right hs

/-- The Lebesgue integral is measurable. This shows that the integrand of (the right-hand-side of)
  Tonelli's theorem is measurable. -/
/-
**Measurable.lintegral_prod_right'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Measurable.lintegral_prod_right' [SFinite ν] : forall {f : α × β -> Real>=
0∞}, Measurable f -> Measurable fun x => ∫⁻ y, f (x, y) ∂ν
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `measurable_prodMk_left`：measurable_prodMk_left {x : α} : Measurable (@Pr
od.mk _ β x)
· 使用定理 `Measurable.ennreal_induction`：Measurable.ennreal_induction {motive : (α 
-> Real>=0∞) -> Prop} (indicator : forall (c : Real>=0∞) ⦃s⦄, MeasurableSet s ->
 motive (Set.indic…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Measurable.const_mul`：Measurable.const_mul [MeasurableMul M] (hf : Measu
rable f) (c : M) : Measurable fun x => c * f x
· 使用定理 `MeasurableMul₂.toMeasurableMul`：∀ {M : Type u_2} [inst : MeasurableSpace
 M] [inst_1 : Mul M] [MeasurableMul₂ M], MeasurableMul M
· 使用定理 `measurable_measure_prodMk_left`：measurable_measure_prodMk_left [SFinite 
ν] {s : Set (α × β)} (hs : MeasurableSet s) : Measurable fun x => ν (Prod.mk x ⁻
¹' s)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `MeasureTheory.lintegral_indicator`：lintegral_indicator {s : Set α} (hs :
 MeasurableSet s) (f : α -> Real>=0∞) : ∫⁻ a, s.indicator f a ∂μ = ∫⁻ a in s, f 
a ∂μ
· 使用定理 `MeasureTheory.lintegral_const`：lintegral_const (c : Real>=0∞) : ∫⁻ _, c 
∂μ = c * μ univ
· 使用定理 `MeasureTheory.Measure.restrict_apply`：restrict_apply (ht : MeasurableSet
 t) : μ.restrict s t = μ (t inter s)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Set.univ_inter`：univ_inter (a : Set α) : univ inter a = a
· 使用定理 `MeasureTheory.lintegral_add_left`：lintegral_add_left {f : α -> Real>=0∞}
 (hf : Measurable f) (g : α -> Real>=0∞) : ∫⁻ a, f a + g a ∂μ = ∫⁻ a, f a ∂μ + ∫
⁻ a, g a ∂μ
· 使用定理 `Measurable.comp`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {x : Mea
surableSpace α} {x_1 : MeasurableSpace β}   {x_2 : MeasurableSpace γ} {g : β → γ
} {f …
· 使用定理 `Measurable.add`：∀ {M : Type u_2} {α : Type u_3} [inst : MeasurableSpace 
M] [inst_1 : Add M] {m : MeasurableSpace α} {f g : α → M}   [MeasurableAdd₂ M], 
Meas…
· 使用定理 `ContinuousAdd.measurableMul₂`：∀ {γ : Type u_3} [inst : TopologicalSpace 
γ] [inst_1 : MeasurableSpace γ] [BorelSpace γ] [SecondCountableTopology γ]   [in
st_4 : Add γ] [Con…
· 使用定理 `ENNReal.instSecondCountableTopology`：SecondCountableTopology ENNReal
· 使用定理 `ENNReal.instContinuousAdd`：ContinuousAdd ENNReal
· 使用定理 `MeasureTheory.lintegral_iSup`：lintegral_iSup {f : Nat -> α -> Real>=0∞} 
(hf : forall n, Measurable (f n)) (h_mono : Monotone f) : ∫⁻ a, ⨆ n, f n a ∂μ = 
⨆ n, ∫⁻ a, f n a ∂…
· 使用定理 `Measurable.iSup`：∀ {α : Type u_1} {δ : Type u_4} [inst : TopologicalSpac
e α] {mα : MeasurableSpace α} [BorelSpace α]   {mδ : MeasurableSpace δ} [inst_2 
: Con…
· 使用定理 `ENNReal.instOrderTopology`：OrderTopology ENNReal
· 使用定理 `instCountableNat`：Countable ℕ

--- 原说明 ---
The Lebesgue integral is measurable. This shows that the integrand of (the right
-hand-side of)
  Tonelli's theorem is measurable.
-/
theorem Measurable.lintegral_prod_right' [SFinite ν] :
    ∀ {f : α × β → ℝ≥0∞}, Measurable f → Measurable fun x => ∫⁻ y, f (x, y) ∂ν := by
  have m := @measurable_prodMk_left
  refine Measurable.ennreal_induction (motive := fun f ↦ Measurable fun (x : α) ↦ ∫⁻ y, f (x, y) ∂ν)
    ?_ ?_ ?_
  · intro c s hs
    simp only [← indicator_comp_right]
    suffices Measurable fun x => c * ν (Prod.mk x ⁻¹' s) by simpa [lintegral_indicator (m hs)]
    exact (measurable_measure_prodMk_left hs).const_mul _
  · rintro f g - hf - h2f h2g
    simp only [Pi.add_apply]
    conv => enter [1, x]; erw [lintegral_add_left (hf.comp m)]
    exact h2f.add h2g
  · intro f hf h2f h3f
    have : ∀ x, Monotone fun n y => f n (x, y) := fun x i j hij y => h2f hij (x, y)
    conv => enter [1, x]; erw [lintegral_iSup (fun n => (hf n).comp m) (this x)]
    exact .iSup h3f

/-- The Lebesgue integral is measurable. This shows that the integrand of (the right-hand-side of)
  Tonelli's theorem is measurable.
  This version has the argument `f` in curried form. -/
@[fun_prop]
/-
**Measurable.lintegral_prod_right** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Measurable.lintegral_prod_right [SFinite ν] {f : α -> β -> Real>=0∞} (hf :
 Measurable (uncurry f)) : Measurable fun x => ∫⁻ y, f x y ∂ν
参数：hf : Measurable (uncurry f)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Measurable.lintegral_prod_right'`：Measurable.lintegral_prod_right' [SFin
ite ν] : forall {f : α × β -> Real>=0∞}, Measurable f -> Measurable fun x => ∫⁻ 
y, f (x, y) ∂ν

--- 原说明 ---
The Lebesgue integral is measurable. This shows that the integrand of (the right
-hand-side of)
  Tonelli's theorem is measurable.
  This version has the argument `f` in curried form.
-/
theorem Measurable.lintegral_prod_right [SFinite ν] {f : α → β → ℝ≥0∞}
    (hf : Measurable (uncurry f)) : Measurable fun x => ∫⁻ y, f x y ∂ν :=
  hf.lintegral_prod_right'

/-- The Lebesgue integral is measurable. This shows that the integrand of (the right-hand-side of)
  the symmetric version of Tonelli's theorem is measurable. -/
/-
**Measurable.lintegral_prod_left'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Measurable.lintegral_prod_left' [SFinite μ] {f : α × β -> Real>=0∞} (hf : 
Measurable f) : Measurable fun y => ∫⁻ x, f (x, y) ∂μ
参数：hf : Measurable f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Measurable.lintegral_prod_right'`：Measurable.lintegral_prod_right' [SFin
ite ν] : forall {f : α × β -> Real>=0∞}, Measurable f -> Measurable fun x => ∫⁻ 
y, f (x, y) ∂ν
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `measurable_swap_iff`：measurable_swap_iff {_ : MeasurableSpace γ} {f : α 
× β -> γ} : Measurable (f ∘ Prod.swap) ↔ Measurable f

--- 原说明 ---
The Lebesgue integral is measurable. This shows that the integrand of (the right
-hand-side of)
  the symmetric version of Tonelli's theorem is measurable.
-/
theorem Measurable.lintegral_prod_left' [SFinite μ] {f : α × β → ℝ≥0∞} (hf : Measurable f) :
    Measurable fun y => ∫⁻ x, f (x, y) ∂μ :=
  (measurable_swap_iff.mpr hf).lintegral_prod_right'

/-- The Lebesgue integral is measurable. This shows that the integrand of (the right-hand-side of)
  the symmetric version of Tonelli's theorem is measurable.
  This version has the argument `f` in curried form. -/
/-
**Measurable.lintegral_prod_left** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Measurable.lintegral_prod_left [SFinite μ] {f : α -> β -> Real>=0∞} (hf : 
Measurable (uncurry f)) : Measurable fun y => ∫⁻ x, f x y ∂μ
参数：hf : Measurable (uncurry f)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Measurable.lintegral_prod_left'`：Measurable.lintegral_prod_left' [SFinit
e μ] {f : α × β -> Real>=0∞} (hf : Measurable f) : Measurable fun y => ∫⁻ x, f (
x, y) ∂μ

--- 原说明 ---
The Lebesgue integral is measurable. This shows that the integrand of (the right
-hand-side of)
  the symmetric version of Tonelli's theorem is measurable.
  This version has the argument `f` in curried form.
-/
theorem Measurable.lintegral_prod_left [SFinite μ] {f : α → β → ℝ≥0∞}
    (hf : Measurable (uncurry f)) : Measurable fun y => ∫⁻ x, f x y ∂μ :=
  hf.lintegral_prod_left'

/-! ### The product measure -/


namespace MeasureTheory

namespace Measure

/-- The binary product of measures. They are defined for arbitrary measures, but we basically
  prove all properties under the assumption that at least one of them is s-finite. -/
protected irreducible_def prod (μ : Measure α) (ν : Measure β) : Measure (α × β) :=
  bind μ fun x : α => map (Prod.mk x) ν

/-
**MeasureTheory.Measure.prod.measureSpace** 是 Mathlib 中的一个定义，位于命名空间 `MeasureTheo
ry.Measure.prod`。
形式化陈述：{α : Type u_4} →   {β : Type u_5} → [MeasureTheory.MeasureSpace α] → [Meas
ureTheory.MeasureSpace β] → MeasureTheory.MeasureSpace (α × β)
参数：α × β。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance prod.measureSpace {α β} [MeasureSpace α] [MeasureSpace β] : MeasureSpace (α × β) where
  volume := volume.prod volume
/-
**MeasureTheory.Measure.volume_eq_prod** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.
Measure`。
形式化陈述：volume_eq_prod (α β) [MeasureSpace α] [MeasureSpace β] : (volume : Measure
 (α × β)) = (volume : Measure α).prod (volume : Measure β)
参数：α β。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem volume_eq_prod (α β) [MeasureSpace α] [MeasureSpace β] :
    (volume : Measure (α × β)) = (volume : Measure α).prod (volume : Measure β) :=
  rfl

/-- For an s-finite measure `ν`, see `prod_apply` below. -/
/-
**MeasureTheory.Measure.prod_apply_le** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.M
easure`。
形式化陈述：prod_apply_le {s : Set (α × β)} (hs : MeasurableSet s) : μ.prod ν s <= ∫⁻ 
x, ν (Prod.mk x ⁻¹' s) ∂μ
参数：α × β；hs : MeasurableSet s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `MeasureTheory.Measure.prod_def`：∀ {α : Type u_4} {β : Type u_5} [inst : 
MeasurableSpace α] [inst_1 : MeasurableSpace β] (μ : MeasureTheory.Measure α)   
(ν : MeasureTheory.M…
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.Measure.map_apply`：map_apply (hf : Measurable f) {s : Set 
β} (hs : MeasurableSet s) : μ.map f s = μ (f ⁻¹' s)
· 使用定理 `measurable_prodMk_left`：measurable_prodMk_left {x : α} : Measurable (@Pr
od.mk _ β x)
· 使用定理 `MeasureTheory.Measure.bind_apply_le`：bind_apply_le {m : Measure α} (f : 
α -> Measure β) {s : Set β} (hs : MeasurableSet s) : bind m f s <= ∫⁻ a, f a s ∂
m

--- 原说明 ---
For an s-finite measure `ν`, see `prod_apply` below.
-/
theorem prod_apply_le {s : Set (α × β)} (hs : MeasurableSet s) :
    μ.prod ν s ≤ ∫⁻ x, ν (Prod.mk x ⁻¹' s) ∂μ := by
  simp only [Measure.prod, ← map_apply measurable_prodMk_left hs]
  exact bind_apply_le _ hs

/-- For any measures `μ` and `ν` and any sets `s` and `t`,
we have `μ.prod ν (s ×ˢ t) ≤ μ s * ν t`.

If `ν` is an s-finite measure (which is usually true),
then this inequality becomes an equality, see `prod_prod` below. -/
/-
**MeasureTheory.Measure.prod_prod_le** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.Me
asure`。
形式化陈述：prod_prod_le (s : Set α) (t : Set β) : μ.prod ν (s ×ˢ t) <= μ s * ν t
参数：s : Set α；t : Set β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.measure_mono`：measure_mono (h : s subseteq t) : μ s <= μ t
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `Set.prod_mono`：prod_mono (hs : s₁ subseteq s₂) (ht : t₁ subseteq t₂) : s
₁ ×ˢ t₁ subseteq s₂ ×ˢ t₂
· 使用定理 `MeasureTheory.subset_toMeasurable`：subset_toMeasurable (μ : Measure α) (
s : Set α) : s subseteq toMeasurable μ s
· 使用定理 `MeasureTheory.Measure.prod_apply_le`：prod_apply_le {s : Set (α × β)} (hs
 : MeasurableSet s) : μ.prod ν s <= ∫⁻ x, ν (Prod.mk x ⁻¹' s) ∂μ
· 使用定理 `MeasurableSet.prod`：∀ {α : Type u_1} {β : Type u_2} {m : MeasurableSpace
 α} {mβ : MeasurableSpace β} {s : Set α} {t : Set β},   MeasurableSet s → Measur
ableSet …
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Set.mk_preimage_prod_right_eq_if`：mk_preimage_prod_right_eq_if [Decidabl
ePred (· in s)] : Prod.mk a ⁻¹' s ×ˢ t = if a in s then t else ∅
· 使用定理 `MeasureTheory.measure_if`：measure_if {x : β} {t : Set β} {s : Set α} [De
cidable (x in t)] : μ (if x in t then s else ∅) = indicator t (fun _ => μ s) x
· 使用定理 `MeasureTheory.lintegral_indicator`：lintegral_indicator {s : Set α} (hs :
 MeasurableSet s) (f : α -> Real>=0∞) : ∫⁻ a, s.indicator f a ∂μ = ∫⁻ a in s, f 
a ∂μ
· 使用定理 `MeasureTheory.measurableSet_toMeasurable`：measurableSet_toMeasurable (μ 
: Measure α) (s : Set α) : MeasurableSet (toMeasurable μ s)
· 使用定理 `MeasureTheory.lintegral_const`：lintegral_const (c : Real>=0∞) : ∫⁻ _, c 
∂μ = c * μ univ
· 使用定理 `MeasureTheory.Measure.restrict_apply_univ`：restrict_apply_univ (s : Set 
α) : μ.restrict s univ = μ s
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `MeasureTheory.measure_toMeasurable`：measure_toMeasurable (s : Set α) : μ
 (toMeasurable μ s) = μ s

--- 原说明 ---
For any measures `μ` and `ν` and any sets `s` and `t`,
we have `μ.prod ν (s ×ˢ t) ≤ μ s * ν t`.

If `ν` is an s-finite measure (which is usually true),
then this inequality becomes an equality, see `prod_prod` below.
-/
theorem prod_prod_le (s : Set α) (t : Set β) : μ.prod ν (s ×ˢ t) ≤ μ s * ν t := by
  set S := toMeasurable μ s
  set T := toMeasurable ν t
  calc
    μ.prod ν (s ×ˢ t) ≤ μ.prod ν (S ×ˢ T) := by gcongr <;> apply subset_toMeasurable
    _ ≤ ∫⁻ x, ν (Prod.mk x ⁻¹' (S ×ˢ T)) ∂μ := prod_apply_le (by measurability)
    _ = μ S * ν T := by
      classical
      simp_rw [S, mk_preimage_prod_right_eq_if, measure_if,
        lintegral_indicator (measurableSet_toMeasurable _ _), lintegral_const,
        restrict_apply_univ, mul_comm]
    _ = μ s * ν t := by rw [measure_toMeasurable, measure_toMeasurable]
/-
**MeasureTheory.Measure.prod.instNullSingletonClass_fst** 是 Mathlib 中的一个定理，位于命名空
间 `MeasureTheory.Measure.prod`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} [inst : MeasurableSpace α] [inst_1 : Measu
rableSpace β] {μ : MeasureTheory.Measure α}   {ν : MeasureTheory.Measure β} [Mea
sureTheory.NullSingletonClass μ], MeasureTheory.NullSingletonClass (μ.prod ν)
参数：μ.prod ν。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `nonpos_iff_eq_zero`：∀ {α : Type u_1} {a : α} [inst : PartialOrder α] [in
st_1 : Zero α] [IsBotZeroClass α], a ≤ 0 ↔ a = 0
· 使用定理 `instIsBotZeroClass`：∀ {α : Type u} [inst : AddZeroClass α] [inst_1 : LE 
α] [CanonicallyOrderedAdd α], IsBotZeroClass α
· 使用定理 `ENNReal.instCanonicallyOrderedAdd`：CanonicallyOrderedAdd ENNReal
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.singleton_prod_singleton`：singleton_prod_singleton : ({a} : Set α) ×
ˢ ({b} : Set β) = {(a, b)}
· 使用定理 `MeasureTheory.Measure.prod_prod_le`：prod_prod_le (s : Set α) (t : Set β)
 : μ.prod ν (s ×ˢ t) <= μ s * ν t
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `MeasureTheory.NullSingletonClass.measure_singleton`：∀ {α : Type u_1} {m0
 : MeasurableSpace α} {μ : MeasureTheory.Measure α} [self : MeasureTheory.NullSi
ngletonClass μ]   (x : α), μ {x} = 0
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
instance prod.instNullSingletonClass_fst [NullSingletonClass μ] :
    NullSingletonClass (Measure.prod μ ν) where
  measure_singleton
  | (x, y) => nonpos_iff_eq_zero.mp <| calc
    μ.prod ν {(x, y)} = μ.prod ν ({x} ×ˢ {y}) := by rw [singleton_prod_singleton]
    _ ≤ μ {x} * ν {y} := prod_prod_le _ _
    _ = 0 := by simp
/-
**MeasureTheory.Measure.prod.instNullSingletonClass_snd** 是 Mathlib 中的一个定理，位于命名空
间 `MeasureTheory.Measure.prod`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} [inst : MeasurableSpace α] [inst_1 : Measu
rableSpace β] {μ : MeasureTheory.Measure α}   {ν : MeasureTheory.Measure β} [Mea
sureTheory.NullSingletonClass ν], MeasureTheory.NullSingletonClass (μ.prod ν)
参数：μ.prod ν。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `nonpos_iff_eq_zero`：∀ {α : Type u_1} {a : α} [inst : PartialOrder α] [in
st_1 : Zero α] [IsBotZeroClass α], a ≤ 0 ↔ a = 0
· 使用定理 `instIsBotZeroClass`：∀ {α : Type u} [inst : AddZeroClass α] [inst_1 : LE 
α] [CanonicallyOrderedAdd α], IsBotZeroClass α
· 使用定理 `ENNReal.instCanonicallyOrderedAdd`：CanonicallyOrderedAdd ENNReal
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.singleton_prod_singleton`：singleton_prod_singleton : ({a} : Set α) ×
ˢ ({b} : Set β) = {(a, b)}
· 使用定理 `MeasureTheory.Measure.prod_prod_le`：prod_prod_le (s : Set α) (t : Set β)
 : μ.prod ν (s ×ˢ t) <= μ s * ν t
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `MeasureTheory.NullSingletonClass.measure_singleton`：∀ {α : Type u_1} {m0
 : MeasurableSpace α} {μ : MeasureTheory.Measure α} [self : MeasureTheory.NullSi
ngletonClass μ]   (x : α), μ {x} = 0
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
instance prod.instNullSingletonClass_snd [NullSingletonClass ν] :
    NullSingletonClass (Measure.prod μ ν) where
  measure_singleton
  | (x, y) => nonpos_iff_eq_zero.mp <| calc
    μ.prod ν {(x, y)} = μ.prod ν ({x} ×ˢ {y}) := by rw [singleton_prod_singleton]
    _ ≤ μ {x} * ν {y} := prod_prod_le _ _
    _ = 0 := by simp

variable [SFinite ν]
/-
**MeasureTheory.Measure.prod_apply** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.Meas
ure`。
形式化陈述：prod_apply {s : Set (α × β)} (hs : MeasurableSet s) : μ.prod ν s = ∫⁻ x, ν
 (Prod.mk x ⁻¹' s) ∂μ
参数：α × β；hs : MeasurableSet s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.Measure.prod_def`：∀ {α : Type u_4} {β : Type u_5} [inst : 
MeasurableSpace α] [inst_1 : MeasurableSpace β] (μ : MeasureTheory.Measure α)   
(ν : MeasureTheory.M…
· 使用定理 `MeasureTheory.Measure.bind_apply`：bind_apply {m : Measure α} {f : α -> M
easure β} {s : Set β} (hs : MeasurableSet s) (hf : AEMeasurable f m) : bind m f 
s = ∫⁻ a, f a s ∂m
· 使用定理 `Measurable.aemeasurable`：Measurable.aemeasurable (h : Measurable f) : AE
Measurable f μ
· 使用定理 `Measurable.map_prodMk_left`：Measurable.map_prodMk_left [SFinite ν] : Mea
surable fun x : α => map (Prod.mk x) ν
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `MeasureTheory.Measure.map_apply`：map_apply (hf : Measurable f) {s : Set 
β} (hs : MeasurableSet s) : μ.map f s = μ (f ⁻¹' s)
· 使用定理 `measurable_prodMk_left`：measurable_prodMk_left {x : α} : Measurable (@Pr
od.mk _ β x)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem prod_apply {s : Set (α × β)} (hs : MeasurableSet s) :
    μ.prod ν s = ∫⁻ x, ν (Prod.mk x ⁻¹' s) ∂μ := by
  simp_rw [Measure.prod, bind_apply hs (Measurable.map_prodMk_left (ν := ν)).aemeasurable,
    map_apply measurable_prodMk_left hs]

/-- The product measure of the product of two sets is the product of their measures. Note that we
do not need the sets to be measurable. -/
@[simp]
/-
**MeasureTheory.Measure.prod_prod** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.Measu
re`。
形式化陈述：prod_prod (s : Set α) (t : Set β) : μ.prod ν (s ×ˢ t) = μ s * ν t
参数：s : Set α；t : Set β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.antisymm`：∀ {α : Type u_1} [inst : PartialOrder α] {a b : α}, a ≤ 
b → b ≤ a → a = b
· 使用定理 `MeasureTheory.Measure.prod_prod_le`：prod_prod_le (s : Set α) (t : Set β)
 : μ.prod ν (s ×ˢ t) <= μ s * ν t
· 使用定理 `MeasureTheory.measurableSet_toMeasurable`：measurableSet_toMeasurable (μ 
: Measure α) (s : Set α) : MeasurableSet (toMeasurable μ s)
· 使用定理 `MeasureTheory.subset_toMeasurable`：subset_toMeasurable (μ : Measure α) (
s : Set α) : s subseteq toMeasurable μ s
· 使用定理 `measurable_measure_prodMk_left`：measurable_measure_prodMk_left [SFinite 
ν] {s : Set (α × β)} (hs : MeasurableSet s) : Measurable fun x => ν (Prod.mk x ⁻
¹' s)
· 使用定理 `MeasureTheory.measure_mono`：measure_mono (h : s subseteq t) : μ s <= μ t
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `Set.mk_mem_prod`：mk_mem_prod (ha : a in s) (hb : b in t) : (a, b) in s ×
ˢ t
· 使用定理 `mul_le_mul'`：mul_le_mul' [MulLeftMono α] [MulRightMono α] {a b c d : α} 
(h₁ : a <= b) (h₂ : c <= d) : a * c <= b * d
· 使用定理 `IsOrderedMonoid.toMulLeftMono`：∀ {α : Type u_1} [inst : CommMonoid α] [i
nst_1 : Preorder α] [IsOrderedMonoid α], MulLeftMono α
· 使用定理 `ENNReal.instIsOrderedMonoid`：IsOrderedMonoid ENNReal
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.setLIntegral_const`：setLIntegral_const (s : Set α) (c : Re
al>=0∞) : ∫⁻ _ in s, c ∂μ = c * μ s
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `MeasureTheory.setLIntegral_mono`：setLIntegral_mono {s : Set α} {f g : α 
-> Real>=0∞} (hg : Measurable g) (hfg : forall x in s, f x <= g x) : ∫⁻ x in s, 
f x ∂μ <= ∫⁻ x in s, …
· 使用定理 `MeasureTheory.lintegral_mono'`：lintegral_mono' {m : MeasurableSpace α} ⦃
μ ν : Measure α⦄ (hμν : μ <= ν) ⦃f g : α -> Real>=0∞⦄ (hfg : f <= g) : ∫⁻ a, f a
 ∂μ <= ∫⁻ a, g a ∂ν
· 使用定理 `MeasureTheory.Measure.restrict_le_self`：restrict_le_self : μ.restrict s 
<= μ
· 使用引理 `le_rfl`：le_rfl : a <= a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.Measure.prod_apply`：prod_apply {s : Set (α × β)} (hs : Mea
surableSet s) : μ.prod ν s = ∫⁻ x, ν (Prod.mk x ⁻¹' s) ∂μ
· 使用定理 `MeasureTheory.measure_toMeasurable`：measure_toMeasurable (s : Set α) : μ
 (toMeasurable μ s) = μ s

--- 原说明 ---
The product measure of the product of two sets is the product of their measures.
 Note that we
do not need the sets to be measurable.
-/
theorem prod_prod (s : Set α) (t : Set β) : μ.prod ν (s ×ˢ t) = μ s * ν t := by
  apply (prod_prod_le s t).antisymm
  -- Formalization is based on https://mathoverflow.net/a/254134/136589
  set ST := toMeasurable (μ.prod ν) (s ×ˢ t)
  have hSTm : MeasurableSet ST := measurableSet_toMeasurable _ _
  have hST : s ×ˢ t ⊆ ST := subset_toMeasurable _ _
  set f : α → ℝ≥0∞ := fun x => ν (Prod.mk x ⁻¹' ST)
  have hfm : Measurable f := measurable_measure_prodMk_left hSTm
  set s' : Set α := { x | ν t ≤ f x }
  have hss' : s ⊆ s' := fun x hx => measure_mono fun y hy => hST <| mk_mem_prod hx hy
  calc
    μ s * ν t ≤ μ s' * ν t := by gcongr
    _ = ∫⁻ _ in s', ν t ∂μ := by rw [setLIntegral_const, mul_comm]
    _ ≤ ∫⁻ x in s', f x ∂μ := setLIntegral_mono hfm fun x => id
    _ ≤ ∫⁻ x, f x ∂μ := lintegral_mono' restrict_le_self le_rfl
    _ = μ.prod ν ST := (prod_apply hSTm).symm
    _ = μ.prod ν (s ×ˢ t) := measure_toMeasurable _

@[simp]
/-
**MeasureTheory.Measure._root_.MeasureTheory.measureReal_prod_prod** 是 Mathlib 中
的一个定理，位于命名空间 `MeasureTheory.Measure`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.MeasureTheory.measureReal_prod_prod (s : Set α) (t : Set β) :
    (μ.prod ν).real (s ×ˢ t) = μ.real s * ν.real t := by
  simp only [measureReal_def, prod_prod, ENNReal.toReal_mul]
/-
**MeasureTheory.Measure.map_fst_prod** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.Me
asure`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} [inst : MeasurableSpace α] [inst_1 : Measu
rableSpace β] {μ : MeasureTheory.Measure α}   {ν : MeasureTheory.Measure β} [Mea
sureTheory.SFinite ν],   MeasureTheory.Measure.map Prod.fst (μ.prod ν) = ν Set.u
niv • μ
参数：μ.prod ν。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.ext`：ext (h : forall s, MeasurableSet s -> μ₁ s = 
μ₂ s) : μ₁ = μ₂
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.Measure.map_apply`：map_apply (hf : Measurable f) {s : Set 
β} (hs : MeasurableSet s) : μ.map f s = μ (f ⁻¹' s)
· 使用定理 `measurable_fst`：measurable_fst {_ : MeasurableSpace α} {_ : MeasurableSp
ace β} : Measurable (Prod.fst : α × β -> α)
· 使用定理 `MeasureTheory.Measure.prod_prod`：prod_prod (s : Set α) (t : Set β) : μ.p
rod ν (s ×ˢ t) = μ s * ν t
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
@[simp] lemma map_fst_prod : Measure.map Prod.fst (μ.prod ν) = (ν univ) • μ := by
  ext s hs
  simp [Measure.map_apply measurable_fst hs, ← prod_univ, mul_comm]
/-
**MeasureTheory.Measure._root_.MeasureTheory.measurePreserving_fst** 是 Mathlib 中
的一个引理，位于命名空间 `MeasureTheory.Measure`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma _root_.MeasureTheory.measurePreserving_fst [IsProbabilityMeasure ν] :
    MeasurePreserving Prod.fst (μ.prod ν) μ :=
  ⟨measurable_fst, by rw [map_fst_prod, measure_univ, one_smul]⟩
/-
**MeasureTheory.Measure.map_snd_prod** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.Me
asure`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} [inst : MeasurableSpace α] [inst_1 : Measu
rableSpace β] {μ : MeasureTheory.Measure α}   {ν : MeasureTheory.Measure β} [Mea
sureTheory.SFinite ν],   MeasureTheory.Measure.map Prod.snd (μ.prod ν) = μ Set.u
niv • ν
参数：μ.prod ν。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.ext`：ext (h : forall s, MeasurableSet s -> μ₁ s = 
μ₂ s) : μ₁ = μ₂
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.Measure.map_apply`：map_apply (hf : Measurable f) {s : Set 
β} (hs : MeasurableSet s) : μ.map f s = μ (f ⁻¹' s)
· 使用定理 `measurable_snd`：measurable_snd {_ : MeasurableSpace α} {_ : MeasurableSp
ace β} : Measurable (Prod.snd : α × β -> β)
· 使用定理 `MeasureTheory.Measure.prod_prod`：prod_prod (s : Set α) (t : Set β) : μ.p
rod ν (s ×ˢ t) = μ s * ν t
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
@[simp] lemma map_snd_prod : Measure.map Prod.snd (μ.prod ν) = (μ univ) • ν := by
  ext s hs
  simp [Measure.map_apply measurable_snd hs, ← univ_prod]
/-
**MeasureTheory.Measure._root_.MeasureTheory.measurePreserving_snd** 是 Mathlib 中
的一个引理，位于命名空间 `MeasureTheory.Measure`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma _root_.MeasureTheory.measurePreserving_snd [IsProbabilityMeasure μ] :
    MeasurePreserving Prod.snd (μ.prod ν) ν :=
  ⟨measurable_snd, by rw [map_snd_prod, measure_univ, one_smul]⟩
/-
**MeasureTheory.Measure.prod.instIsOpenPosMeasure** 是 Mathlib 中的一个定理，位于命名空间 `Mea
sureTheory.Measure.prod`。
形式化陈述：∀ {X : Type u_4} {Y : Type u_5} [inst : TopologicalSpace X] [inst_1 : Topo
logicalSpace Y] {m : MeasurableSpace X}   {μ : MeasureTheory.Measure X} [μ.IsOpe
nPosMeasure] {m' : MeasurableSpace Y} {ν : MeasureTheory.Measure Y}   [ν.IsOpenP
osMeasure] [MeasureTheory.SFinite ν], (μ.prod ν).IsOpenPosMeasure
参数：μ.prod ν。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `isOpen_prod_iff`：isOpen_prod_iff {s : Set (X × Y)} : IsOpen s ↔ forall a
 b, (a, b) in s -> exists u v, IsOpen u ∧ IsOpen v ∧ a in u ∧ b in v ∧ u ×ˢ v su
bsete…
· 使用定理 `ne_of_gt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用引理 `lt_of_lt_of_le`：lt_of_lt_of_le (hab : a < b) (hbc : b <= c) : a < c
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.Measure.prod_prod`：prod_prod (s : Set α) (t : Set β) : μ.p
rod ν (s ×ˢ t) = μ s * ν t
· 使用定理 `ENNReal.instCanonicallyOrderedAdd`：CanonicallyOrderedAdd ENNReal
· 使用定理 `ENNReal.instNoZeroDivisors`：NoZeroDivisors ENNReal
· 使用定理 `IsOpen.measure_pos`：∀ {X : Type u_1} [inst : TopologicalSpace X] {m : Me
asurableSpace X} (μ : MeasureTheory.Measure X) [μ.IsOpenPosMeasure]   {U : Set X
}, IsOpe…
· 使用定理 `MeasureTheory.measure_mono`：measure_mono (h : s subseteq t) : μ s <= μ t
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
-/
instance prod.instIsOpenPosMeasure {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {m : MeasurableSpace X} {μ : Measure X} [IsOpenPosMeasure μ] {m' : MeasurableSpace Y}
    {ν : Measure Y} [IsOpenPosMeasure ν] [SFinite ν] : IsOpenPosMeasure (μ.prod ν) := by
  constructor
  rintro U U_open ⟨⟨x, y⟩, hxy⟩
  rcases isOpen_prod_iff.1 U_open x y hxy with ⟨u, v, u_open, v_open, xu, yv, huv⟩
  refine ne_of_gt (lt_of_lt_of_le ?_ (measure_mono huv))
  simp only [prod_prod, CanonicallyOrderedAdd.mul_pos]
  constructor
  · exact u_open.measure_pos μ ⟨x, xu⟩
  · exact v_open.measure_pos ν ⟨y, yv⟩
/-
**MeasureTheory.Measure.** 是 Mathlib 中的一个实例，位于命名空间 `MeasureTheory.Measure`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {X Y : Type*}
    [TopologicalSpace X] [MeasureSpace X] [IsOpenPosMeasure (volume : Measure X)]
    [TopologicalSpace Y] [MeasureSpace Y] [IsOpenPosMeasure (volume : Measure Y)]
    [SFinite (volume : Measure Y)] : IsOpenPosMeasure (volume : Measure (X × Y)) :=
  prod.instIsOpenPosMeasure
/-
**MeasureTheory.Measure.FiniteAtFilter.prod** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTh
eory.Measure.FiniteAtFilter`。
形式化陈述：∀ {X : Type u_4} {Y : Type u_5} {m : MeasurableSpace X} {μ : MeasureTheory
.Measure X} {m' : MeasurableSpace Y}   {ν : MeasureTheory.Measure Y} {l : Filter
 X} {l' : Filter Y},   μ.FiniteAtFilter l → ν.FiniteAtFilter l' → (μ.prod ν).Fin
iteAtFilter (l ×ˢ l')
参数：μ.prod ν；l ×ˢ l'。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.prod_mem_prod`：prod_mem_prod (hs : s in f) (ht : t in g) : s ×ˢ t
 in f ×ˢ g
· 使用定理 `lt_imp_lt_of_le_of_le`：lt_imp_lt_of_le_of_le (h₁ : c <= a) (h₂ : b <= d)
 : a < b -> c < d
· 使用定理 `MeasureTheory.Measure.prod_prod_le`：prod_prod_le (s : Set α) (t : Set β)
 : μ.prod ν (s ×ˢ t) <= μ s * ν t
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `ENNReal.mul_lt_top`：mul_lt_top : a < ∞ -> b < ∞ -> a * b < ∞
-/
protected theorem FiniteAtFilter.prod {X Y : Type*} {m : MeasurableSpace X} {μ : Measure X}
    {m' : MeasurableSpace Y} {ν : Measure Y} {l : Filter X} {l' : Filter Y}
    (hμ : μ.FiniteAtFilter l) (hν : ν.FiniteAtFilter l') :
    (μ.prod ν).FiniteAtFilter (l ×ˢ l') := by
  rcases hμ with ⟨s, hs, hμs⟩
  rcases hν with ⟨t, ht, hνt⟩
  use s ×ˢ t, Filter.prod_mem_prod hs ht
  grw [prod_prod_le]
  exact ENNReal.mul_lt_top hμs hνt
/-
**MeasureTheory.Measure.prod.instIsLocallyFiniteMeasure** 是 Mathlib 中的一个定理，位于命名空
间 `MeasureTheory.Measure.prod`。
形式化陈述：∀ {X : Type u_4} {Y : Type u_5} [inst : TopologicalSpace X] [inst_1 : Topo
logicalSpace Y] {m : MeasurableSpace X}   {μ : MeasureTheory.Measure X} [Measure
Theory.IsLocallyFiniteMeasure μ] {m' : MeasurableSpace Y}   {ν : MeasureTheory.M
easure Y} [MeasureTheory.IsLocallyFiniteMeasure ν],   MeasureTheory.IsLocallyFin
iteMeasure (μ.prod ν)
参数：μ.prod ν。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `nhds_prod_eq`：nhds_prod_eq {x : X} {y : Y} : 𝓝 (x, y) = 𝓝 x ×ˢ 𝓝 y
· 使用定理 `MeasureTheory.Measure.FiniteAtFilter.prod`：∀ {X : Type u_4} {Y : Type u_
5} {m : MeasurableSpace X} {μ : MeasureTheory.Measure X} {m' : MeasurableSpace Y
}   {ν : MeasureTheory.Measure …
· 使用定理 `MeasureTheory.Measure.finiteAt_nhds`：∀ {α : Type u_1} {m0 : MeasurableSp
ace α} [inst : TopologicalSpace α] (μ : MeasureTheory.Measure α)   [MeasureTheor
y.IsLocallyFiniteMeasure …
-/
instance prod.instIsLocallyFiniteMeasure {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {m : MeasurableSpace X} {μ : Measure X} [IsLocallyFiniteMeasure μ] {m' : MeasurableSpace Y}
    {ν : Measure Y} [IsLocallyFiniteMeasure ν] : IsLocallyFiniteMeasure (μ.prod ν) where
  finiteAtNhds x := by
    rw [nhds_prod_eq]
    exact μ.finiteAt_nhds _ |>.prod <| ν.finiteAt_nhds _
/-
**MeasureTheory.Measure.** 是 Mathlib 中的一个实例，位于命名空间 `MeasureTheory.Measure`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {m : MeasureSpace X} [IsLocallyFiniteMeasure (volume : Measure X)]
    {m' : MeasureSpace Y} [IsLocallyFiniteMeasure (volume : Measure Y)] :
    IsLocallyFiniteMeasure (volume : Measure (X × Y)) :=
  prod.instIsLocallyFiniteMeasure
/-
**MeasureTheory.Measure.prod.instIsFiniteMeasure** 是 Mathlib 中的一个定理，位于命名空间 `Meas
ureTheory.Measure.prod`。
形式化陈述：∀ {α : Type u_4} {β : Type u_5} {mα : MeasurableSpace α} {mβ : MeasurableS
pace β} (μ : MeasureTheory.Measure α)   (ν : MeasureTheory.Measure β) [MeasureTh
eory.IsFiniteMeasure μ] [MeasureTheory.IsFiniteMeasure ν],   MeasureTheory.IsFin
iteMeasure (μ.prod ν)
参数：μ : MeasureTheory.Measure α；ν : MeasureTheory.Measure β；μ.prod ν。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.univ_prod_univ`：univ_prod_univ : @univ α ×ˢ @univ β = univ
· 使用定理 `MeasureTheory.Measure.prod_prod`：prod_prod (s : Set α) (t : Set β) : μ.p
rod ν (s ×ˢ t) = μ s * ν t
· 使用定理 `MeasureTheory.instSFiniteOfSigmaFinite`：∀ {α : Type u_1} {m0 : Measurabl
eSpace α} {μ : MeasureTheory.Measure α} [MeasureTheory.SigmaFinite μ],   Measure
Theory.SFinite μ
· 使用定理 `MeasureTheory.IsFiniteMeasure.toSigmaFinite`：∀ {α : Type u_1} {_m0 : Mea
surableSpace α} (μ : MeasureTheory.Measure α) [MeasureTheory.IsFiniteMeasure μ],
   MeasureTheory.SigmaFinite μ
· 使用定理 `Ne.lt_top`：Ne.lt_top (h : a != ⊤) : a < ⊤
· 使用定理 `ENNReal.mul_ne_top`：mul_ne_top : a != ∞ -> b != ∞ -> a * b != ∞
· 使用定理 `MeasureTheory.measure_ne_top`：measure_ne_top (μ : Measure α) [IsFiniteMe
asure μ] (s : Set α) : μ s != ∞
-/
instance prod.instIsFiniteMeasure {α β : Type*} {mα : MeasurableSpace α} {mβ : MeasurableSpace β}
    (μ : Measure α) (ν : Measure β) [IsFiniteMeasure μ] [IsFiniteMeasure ν] :
    IsFiniteMeasure (μ.prod ν) := by
  constructor
  rw [← univ_prod_univ, prod_prod]
  finiteness
/-
**MeasureTheory.Measure.** 是 Mathlib 中的一个实例，位于命名空间 `MeasureTheory.Measure`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {α β : Type*} [MeasureSpace α] [MeasureSpace β] [IsFiniteMeasure (volume : Measure α)]
    [IsFiniteMeasure (volume : Measure β)] : IsFiniteMeasure (volume : Measure (α × β)) :=
  prod.instIsFiniteMeasure _ _
/-
**MeasureTheory.Measure.prod.instIsProbabilityMeasure** 是 Mathlib 中的一个定理，位于命名空间 
`MeasureTheory.Measure.prod`。
形式化陈述：∀ {α : Type u_4} {β : Type u_5} {mα : MeasurableSpace α} {mβ : MeasurableS
pace β} (μ : MeasureTheory.Measure α)   (ν : MeasureTheory.Measure β) [MeasureTh
eory.IsProbabilityMeasure μ] [MeasureTheory.IsProbabilityMeasure ν],   MeasureTh
eory.IsProbabilityMeasure (μ.prod ν)
参数：μ : MeasureTheory.Measure α；ν : MeasureTheory.Measure β；μ.prod ν。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.univ_prod_univ`：univ_prod_univ : @univ α ×ˢ @univ β = univ
· 使用定理 `MeasureTheory.Measure.prod_prod`：prod_prod (s : Set α) (t : Set β) : μ.p
rod ν (s ×ˢ t) = μ s * ν t
· 使用定理 `MeasureTheory.instSFiniteOfSigmaFinite`：∀ {α : Type u_1} {m0 : Measurabl
eSpace α} {μ : MeasureTheory.Measure α} [MeasureTheory.SigmaFinite μ],   Measure
Theory.SFinite μ
· 使用定理 `MeasureTheory.IsFiniteMeasure.toSigmaFinite`：∀ {α : Type u_1} {_m0 : Mea
surableSpace α} (μ : MeasureTheory.Measure α) [MeasureTheory.IsFiniteMeasure μ],
   MeasureTheory.SigmaFinite μ
· 使用定理 `MeasureTheory.IsZeroOrProbabilityMeasure.toIsFiniteMeasure`：∀ {α : Type 
u_1} {m0 : MeasurableSpace α} (μ : MeasureTheory.Measure α) [MeasureTheory.IsZer
oOrProbabilityMeasure μ],   MeasureTheory.IsFini…
· 使用定理 `MeasureTheory.instIsZeroOrProbabilityMeasureOfIsProbabilityMeasure`：∀ {α
 : Type u_1} {m0 : MeasurableSpace α} (μ : MeasureTheory.Measure α) [MeasureTheo
ry.IsProbabilityMeasure μ],   MeasureTheory.IsZeroOrProb…
· 使用定理 `MeasureTheory.IsProbabilityMeasure.measure_univ`：∀ {α : Type u_1} {m0 : 
MeasurableSpace α} {μ : MeasureTheory.Measure α} [self : MeasureTheory.IsProbabi
lityMeasure μ],   μ Set.univ = 1
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
-/
instance prod.instIsProbabilityMeasure {α β : Type*} {mα : MeasurableSpace α}
    {mβ : MeasurableSpace β} (μ : Measure α) (ν : Measure β) [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν] : IsProbabilityMeasure (μ.prod ν) :=
  ⟨by rw [← univ_prod_univ, prod_prod, measure_univ, measure_univ, mul_one]⟩
/-
**MeasureTheory.Measure.** 是 Mathlib 中的一个实例，位于命名空间 `MeasureTheory.Measure`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {α β : Type*} [MeasureSpace α] [MeasureSpace β]
    [IsProbabilityMeasure (volume : Measure α)] [IsProbabilityMeasure (volume : Measure β)] :
    IsProbabilityMeasure (volume : Measure (α × β)) :=
  prod.instIsProbabilityMeasure _ _
/-
**MeasureTheory.Measure.prod.instIsFiniteMeasureOnCompacts** 是 Mathlib 中的一个定理，位于
命名空间 `MeasureTheory.Measure.prod`。
形式化陈述：∀ {α : Type u_4} {β : Type u_5} [inst : TopologicalSpace α] [inst_1 : Topo
logicalSpace β] {mα : MeasurableSpace α}   {mβ : MeasurableSpace β} (μ : Measure
Theory.Measure α) (ν : MeasureTheory.Measure β)   [MeasureTheory.IsFiniteMeasure
OnCompacts μ] [MeasureTheory.IsFiniteMeasureOnCompacts ν],   MeasureTheory.IsFin
iteMeasureOnCompacts (μ.prod ν)
参数：μ : MeasureTheory.Measure α；ν : MeasureTheory.Measure β；μ.prod ν。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.measure_mono`：measure_mono (h : s subseteq t) : μ s <= μ t
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `Set.subset_prod`：subset_prod {s : Set (α × β)} : s subseteq (Prod.fst ''
 s) ×ˢ (Prod.snd '' s)
· 使用定理 `MeasureTheory.Measure.prod_prod_le`：prod_prod_le (s : Set α) (t : Set β)
 : μ.prod ν (s ×ˢ t) <= μ s * ν t
· 使用定理 `ENNReal.mul_lt_top`：mul_lt_top : a < ∞ -> b < ∞ -> a * b < ∞
· 使用定理 `IsCompact.measure_lt_top`：∀ {α : Type u_1} {m0 : MeasurableSpace α} [ins
t : TopologicalSpace α] {μ : MeasureTheory.Measure α}   [MeasureTheory.IsFiniteM
easureOnCompac…
· 使用定理 `IsCompact.image`：IsCompact.image {f : X -> Y} (hs : IsCompact s) (hf : C
ontinuous f) : IsCompact (f '' s)
· 使用定理 `continuous_fst`：continuous_fst (f : X → Y × Z) (hf : Continuous f) : Con
tinuous (fun x ↦ (f x).fst)
· 使用定理 `continuous_snd`：continuous_snd (f : X → Y × Z) (hf : Continuous f) : Con
tinuous (fun x ↦ (f x).snd)
-/
instance prod.instIsFiniteMeasureOnCompacts {α β : Type*} [TopologicalSpace α] [TopologicalSpace β]
    {mα : MeasurableSpace α} {mβ : MeasurableSpace β} (μ : Measure α) (ν : Measure β)
    [IsFiniteMeasureOnCompacts μ] [IsFiniteMeasureOnCompacts ν] :
    IsFiniteMeasureOnCompacts (μ.prod ν) where
  lt_top_of_isCompact K hK := calc
    μ.prod ν K ≤ μ.prod ν ((Prod.fst '' K) ×ˢ (Prod.snd '' K)) := measure_mono subset_prod
    _ ≤ μ (Prod.fst '' K) * ν (Prod.snd '' K) := prod_prod_le _ _
    _ < ∞ :=
      mul_lt_top (hK.image continuous_fst).measure_lt_top (hK.image continuous_snd).measure_lt_top
/-
**MeasureTheory.Measure.** 是 Mathlib 中的一个实例，位于命名空间 `MeasureTheory.Measure`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {X Y : Type*}
    [TopologicalSpace X] [MeasureSpace X] [IsFiniteMeasureOnCompacts (volume : Measure X)]
    [TopologicalSpace Y] [MeasureSpace Y] [IsFiniteMeasureOnCompacts (volume : Measure Y)] :
    IsFiniteMeasureOnCompacts (volume : Measure (X × Y)) :=
  prod.instIsFiniteMeasureOnCompacts _ _


open IsUnifLocDoublingMeasure in
/--
The product of two uniformly locally doubling measures is a uniformly locally doubling measure,
assuming the second one is s-finite.
-/
/-
**MeasureTheory.Measure._root_.IsUnifLocDoublingMeasure.prod** 是 Mathlib 中的一个实例，
位于命名空间 `MeasureTheory.Measure`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The product of two uniformly locally doubling measures is a uniformly locally do
ubling measure,
assuming the second one is s-finite.
-/
instance _root_.IsUnifLocDoublingMeasure.prod {X Y : Type*}
    [PseudoMetricSpace X] [MeasurableSpace X] [PseudoMetricSpace Y] [MeasurableSpace Y]
    (μ : Measure X) (ν : Measure Y) [SFinite ν]
    [IsUnifLocDoublingMeasure μ] [IsUnifLocDoublingMeasure ν] :
    IsUnifLocDoublingMeasure (μ.prod ν) := by
  constructor
  use doublingConstant μ * doublingConstant ν
  filter_upwards [eventually_measure_le_doublingConstant_mul μ,
    eventually_measure_le_doublingConstant_mul ν] with r hμr hνr x
  rw [← closedBall_prod_same, prod_prod, ← closedBall_prod_same, prod_prod]
  grw [hμr, hνr, ENNReal.coe_mul, mul_mul_mul_comm]
/-
**MeasureTheory.Measure.IsUnifLocDoublingMeasure.volume_prod** 是 Mathlib 中的一个定理，
位于命名空间 `MeasureTheory.Measure.IsUnifLocDoublingMeasure`。
形式化陈述：∀ {X : Type u_4} {Y : Type u_5} [inst : PseudoMetricSpace X] [inst_1 : Mea
sureTheory.MeasureSpace X]   [inst_2 : PseudoMetricSpace Y] [inst_3 : MeasureThe
ory.MeasureSpace Y] [MeasureTheory.SFinite MeasureTheory.volume]   [IsUnifLocDou
blingMeasure MeasureTheory.volume] [IsUnifLocDoublingMeasure MeasureTheory.volum
e],   IsUnifLocDoublingMeasure MeasureTheory.volume
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsUnifLocDoublingMeasure.prod`：∀ {X : Type u_4} {Y : Type u_5} [inst : P
seudoMetricSpace X] [inst_1 : MeasurableSpace X] [inst_2 : PseudoMetricSpace Y] 
  [inst_3 : Measura…
-/
instance IsUnifLocDoublingMeasure.volume_prod {X Y : Type*} [PseudoMetricSpace X] [MeasureSpace X]
    [PseudoMetricSpace Y] [MeasureSpace Y] [SFinite (volume : Measure Y)]
    [IsUnifLocDoublingMeasure (volume : Measure X)]
    [IsUnifLocDoublingMeasure (volume : Measure Y)] :
    IsUnifLocDoublingMeasure (volume : Measure (X × Y)) :=
  .prod _ _
/-
**MeasureTheory.Measure.ae_measure_lt_top** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheo
ry.Measure`。
形式化陈述：ae_measure_lt_top {s : Set (α × β)} (hs : MeasurableSet s) (h2s : (μ.prod 
ν) s != ∞) : forallᵐ x ∂μ, ν (Prod.mk x ⁻¹' s) < ∞
参数：α × β；hs : MeasurableSet s；h2s : (μ.prod ν) s != ∞。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.ae_lt_top`：ae_lt_top {f : α -> Real>=0∞} (hf : Measurable 
f) (h2f : ∫⁻ x, f x ∂μ != ∞) : forallᵐ x ∂μ, f x < ∞
· 使用定理 `measurable_measure_prodMk_left`：measurable_measure_prodMk_left [SFinite 
ν] {s : Set (α × β)} (hs : MeasurableSet s) : Measurable fun x => ν (Prod.mk x ⁻
¹' s)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.Measure.prod_apply`：prod_apply {s : Set (α × β)} (hs : Mea
surableSet s) : μ.prod ν s = ∫⁻ x, ν (Prod.mk x ⁻¹' s) ∂μ
-/
theorem ae_measure_lt_top {s : Set (α × β)} (hs : MeasurableSet s) (h2s : (μ.prod ν) s ≠ ∞) :
    ∀ᵐ x ∂μ, ν (Prod.mk x ⁻¹' s) < ∞ := by
  rw [prod_apply hs] at h2s
  exact ae_lt_top (measurable_measure_prodMk_left hs) h2s

omit [SFinite ν] in
/-- If `μ`-a.e. section `{y | (x, y) ∈ s}` of a measurable set have `ν` measure zero,
then `s` has `μ.prod ν` measure zero.

This implication requires `s` to be measurable but does not require `ν` to be s-finite.
See also `measure_prod_null` and `measure_ae_null_of_prod_null` below. -/
/-
**MeasureTheory.Measure.measure_prod_null_of_ae_null** 是 Mathlib 中的一个定理，位于命名空间 `
MeasureTheory.Measure`。
形式化陈述：measure_prod_null_of_ae_null {s : Set (α × β)} (hsm : MeasurableSet s) (hs
 : (fun x => ν (Prod.mk x ⁻¹' s)) =ᵐ[μ] 0) : μ.prod ν s = 0
参数：α × β；hsm : MeasurableSet s；hs : (fun x => ν (Prod.mk x ⁻¹' s)) =ᵐ[μ] 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `nonpos_iff_eq_zero`：∀ {α : Type u_1} {a : α} [inst : PartialOrder α] [in
st_1 : Zero α] [IsBotZeroClass α], a ≤ 0 ↔ a = 0
· 使用定理 `instIsBotZeroClass`：∀ {α : Type u} [inst : AddZeroClass α] [inst_1 : LE 
α] [CanonicallyOrderedAdd α], IsBotZeroClass α
· 使用定理 `ENNReal.instCanonicallyOrderedAdd`：CanonicallyOrderedAdd ENNReal
· 使用定理 `MeasureTheory.Measure.prod_apply_le`：prod_apply_le {s : Set (α × β)} (hs
 : MeasurableSet s) : μ.prod ν s <= ∫⁻ x, ν (Prod.mk x ⁻¹' s) ∂μ
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `MeasureTheory.lintegral_congr_ae`：lintegral_congr_ae {f g : α -> Real>=0
∞} (h : f =ᵐ[μ] g) : ∫⁻ a, f a ∂μ = ∫⁻ a, g a ∂μ
· 使用定理 `MeasureTheory.lintegral_const`：lintegral_const (c : Real>=0∞) : ∫⁻ _, c 
∂μ = c * μ univ
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
If `μ`-a.e. section `{y | (x, y) ∈ s}` of a measurable set have `ν` measure zero
,
then `s` has `μ.prod ν` measure zero.

This implication requires `s` to be measurable but does not require `ν` to be s-
finite.
See also `measure_prod_null` and `measure_ae_null_of_prod_null` below.
-/
theorem measure_prod_null_of_ae_null {s : Set (α × β)} (hsm : MeasurableSet s)
    (hs : (fun x => ν (Prod.mk x ⁻¹' s)) =ᵐ[μ] 0) : μ.prod ν s = 0 := by
  rw [← nonpos_iff_eq_zero]
  calc
    μ.prod ν s ≤ ∫⁻ x, ν (Prod.mk x ⁻¹' s) ∂μ := prod_apply_le hsm
    _ = 0 := by simp [lintegral_congr_ae hs]

/-- A measurable set `s` has `μ.prod ν` measure zero, where `ν` is an s-finite measure,
if and only if `μ`-a.e. section `{y | (x, y) ∈ s}` of `s` have `ν` measure zero.

See `measure_ae_null_of_prod_null` for the forward implication without the measurability assumption
and `measure_prod_null_of_ae_null` for the reverse implication without the s-finiteness assumption.

Note: the assumption `hs` cannot be dropped. For a counterexample, see
Walter Rudin *Real and Complex Analysis*, example (c) in section 8.9. -/
/-
**MeasureTheory.Measure.measure_prod_null** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheo
ry.Measure`。
形式化陈述：measure_prod_null {s : Set (α × β)} (hs : MeasurableSet s) : μ.prod ν s = 
0 ↔ (fun x => ν (Prod.mk x ⁻¹' s)) =ᵐ[μ] 0
参数：α × β；hs : MeasurableSet s。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.Measure.prod_apply`：prod_apply {s : Set (α × β)} (hs : Mea
surableSet s) : μ.prod ν s = ∫⁻ x, ν (Prod.mk x ⁻¹' s) ∂μ
· 使用定理 `MeasureTheory.lintegral_eq_zero_iff`：lintegral_eq_zero_iff {f : α -> Rea
l>=0∞} (hf : Measurable f) : ∫⁻ a, f a ∂μ = 0 ↔ f =ᵐ[μ] 0
· 使用定理 `measurable_measure_prodMk_left`：measurable_measure_prodMk_left [SFinite 
ν] {s : Set (α × β)} (hs : MeasurableSet s) : Measurable fun x => ν (Prod.mk x ⁻
¹' s)
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a

--- 原说明 ---
A measurable set `s` has `μ.prod ν` measure zero, where `ν` is an s-finite measu
re,
if and only if `μ`-a.e. section `{y | (x, y) ∈ s}` of `s` have `ν` measure zero.

See `measure_ae_null_of_prod_null` for the forward implication without the measu
rability assumption
and `measure_prod_null_of_ae_null` for the reverse implication without the s-fin
iteness assumption.

Note: the assumption `hs` cannot be dropped. For a counterexample, see
Walter Rudin *Real and Complex Analysis*, example (c) in section 8.9.
-/
theorem measure_prod_null {s : Set (α × β)} (hs : MeasurableSet s) :
    μ.prod ν s = 0 ↔ (fun x => ν (Prod.mk x ⁻¹' s)) =ᵐ[μ] 0 := by
  rw [prod_apply hs, lintegral_eq_zero_iff (measurable_measure_prodMk_left hs)]

/-- Note: the converse is not true without assuming that `s` is measurable. For a counterexample,
  see Walter Rudin *Real and Complex Analysis*, example (c) in section 8.9. -/
/-
**MeasureTheory.Measure.measure_ae_null_of_prod_null** 是 Mathlib 中的一个定理，位于命名空间 `
MeasureTheory.Measure`。
形式化陈述：measure_ae_null_of_prod_null {s : Set (α × β)} (h : μ.prod ν s = 0) : (fun
 x => ν (Prod.mk x ⁻¹' s)) =ᵐ[μ] 0
参数：α × β；h : μ.prod ν s = 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `MeasureTheory.exists_measurable_superset_of_null`：exists_measurable_supe
rset_of_null (h : μ s = 0) : exists t, s subseteq t ∧ MeasurableSet t ∧ μ t = 0
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Filter.eventuallyLE_antisymm_iff`：eventuallyLE_antisymm_iff [PartialOrde
r β] {l : Filter α} {f g : α -> β} : f =ᶠ[l] g ↔ f <=ᶠ[l] g ∧ g <=ᶠ[l] f
· 使用定理 `Filter.EventuallyLE.trans_eq`：∀ {α : Type u} {β : Type v} [inst : Preord
er β] {l : Filter α} {f g h : α → β}, f ≤ᶠ[l] g → g =ᶠ[l] h → f ≤ᶠ[l] h
· 使用定理 `Filter.Eventually.of_forall`：∀ {α : Type u} {p : α → Prop} {f : Filter α
}, (∀ (x : α), p x) → ∀ᶠ (x : α) in f, p x
· 使用定理 `MeasureTheory.measure_mono`：measure_mono (h : s subseteq t) : μ s <= μ t
· 使用定理 `Set.preimage_mono`：preimage_mono {s t : Set β} (h : s subseteq t) : f ⁻¹
' s subseteq f ⁻¹' t
· 使用定理 `MeasureTheory.Measure.measure_prod_null`：measure_prod_null {s : Set (α ×
 β)} (hs : MeasurableSet s) : μ.prod ν s = 0 ↔ (fun x => ν (Prod.mk x ⁻¹' s)) =ᵐ
[μ] 0
· 使用定理 `zero_le`：∀ {α : Type u_1} [inst : LE α] [inst_1 : Zero α] [IsBotZeroClas
s α] {a : α}, 0 ≤ a
· 使用定理 `instIsBotZeroClass`：∀ {α : Type u} [inst : AddZeroClass α] [inst_1 : LE 
α] [CanonicallyOrderedAdd α], IsBotZeroClass α
· 使用定理 `ENNReal.instCanonicallyOrderedAdd`：CanonicallyOrderedAdd ENNReal

--- 原说明 ---
Note: the converse is not true without assuming that `s` is measurable. For a co
unterexample,
  see Walter Rudin *Real and Complex Analysis*, example (c) in section 8.9.
-/
theorem measure_ae_null_of_prod_null {s : Set (α × β)} (h : μ.prod ν s = 0) :
    (fun x => ν (Prod.mk x ⁻¹' s)) =ᵐ[μ] 0 := by
  obtain ⟨t, hst, mt, ht⟩ := exists_measurable_superset_of_null h
  rw [measure_prod_null mt] at ht
  rw [eventuallyLE_antisymm_iff]
  exact
    ⟨EventuallyLE.trans_eq (Eventually.of_forall fun x => measure_mono (preimage_mono hst)) ht,
      Eventually.of_forall fun x => zero_le⟩

omit [SFinite ν] in
/-
**MeasureTheory.Measure.AbsolutelyContinuous.prod** 是 Mathlib 中的一个定理，位于命名空间 `Mea
sureTheory.Measure.AbsolutelyContinuous`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} [inst : MeasurableSpace α] [inst_1 : Measu
rableSpace β] {μ μ' : MeasureTheory.Measure α}   {ν ν' : MeasureTheory.Measure β
} [MeasureTheory.SFinite ν'],   μ.AbsolutelyContinuous μ' → ν.AbsolutelyContinuo
us ν' → (μ.prod ν).AbsolutelyContinuous (μ'.prod ν')
参数：μ.prod ν；μ'.prod ν'。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.AbsolutelyContinuous.mk`：mk (h : forall ⦃s : Set α
⦄, MeasurableSet s -> ν s = 0 -> μ s = 0) : μ ≪ ν
· 使用定理 `MeasureTheory.Measure.measure_prod_null_of_ae_null`：measure_prod_null_of
_ae_null {s : Set (α × β)} (hsm : MeasurableSet s) (hs : (fun x => ν (Prod.mk x 
⁻¹' s)) =ᵐ[μ] 0) : μ.prod ν s = 0
· 使用定理 `Filter.Eventually.mono`：∀ {α : Type u} {p q : α → Prop} {f : Filter α}, 
(∀ᶠ (x : α) in f, p x) → (∀ (x : α), p x → q x) → ∀ᶠ (x : α) in f, q x
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `Filter.EventuallyEq.filter_mono`：∀ {α : Type u} {β : Type v} {l l' : Fil
ter α} {f g : α → β}, f =ᶠ[l] g → l' ≤ l → f =ᶠ[l'] g
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.Measure.measure_prod_null`：measure_prod_null {s : Set (α ×
 β)} (hs : MeasurableSet s) : μ.prod ν s = 0 ↔ (fun x => ν (Prod.mk x ⁻¹' s)) =ᵐ
[μ] 0
· 使用定理 `MeasureTheory.Measure.AbsolutelyContinuous.ae_le`：∀ {α : Type u_1} {mα :
 MeasurableSpace α} {μ ν : MeasureTheory.Measure α},   μ.AbsolutelyContinuous ν 
→ MeasureTheory.ae μ ≤ MeasureTheory.a…
-/
theorem AbsolutelyContinuous.prod [SFinite ν'] (h1 : μ ≪ μ') (h2 : ν ≪ ν') :
    μ.prod ν ≪ μ'.prod ν' := by
  refine AbsolutelyContinuous.mk fun s hs h2s => ?_
  apply measure_prod_null_of_ae_null hs
  rw [measure_prod_null hs] at h2s
  exact (h2s.filter_mono h1.ae_le).mono fun _ h => h2 h

omit [SFinite ν] in
/-
**MeasureTheory.Measure.prod_mono** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.Measu
re`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} [inst : MeasurableSpace α] [inst_1 : Measu
rableSpace β] {μ μ' : MeasureTheory.Measure α}   {ν ν' : MeasureTheory.Measure β
} [MeasureTheory.SFinite ν'], μ ≤ μ' → ν ≤ ν' → μ.prod ν ≤ μ'.prod ν'
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `MeasureTheory.Measure.le_iff`：le_iff : μ₁ <= μ₂ ↔ forall s, MeasurableSe
t s -> μ₁ s <= μ₂ s
· 使用定理 `MeasureTheory.Measure.prod_apply_le`：prod_apply_le {s : Set (α × β)} (hs
 : MeasurableSet s) : μ.prod ν s <= ∫⁻ x, ν (Prod.mk x ⁻¹' s) ∂μ
· 使用定理 `MeasureTheory.lintegral_mono_fn'`：∀ {α : Type u_1} {m : MeasurableSpace 
α} {μ ν : MeasureTheory.Measure α},   μ ≤ ν → ∀ ⦃f g : α → ENNReal⦄, (∀ (x : α),
 f x ≤ g x) → ∫⁻ (a : …
· 使用定理 `MeasureTheory.Measure.measure_mono_left`：∀ {α : Type u_1} {m0 : Measurab
leSpace α} {μ ν : MeasureTheory.Measure α}, μ ≤ ν → ∀ (s : Set α), μ s ≤ ν s
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.Measure.prod_apply`：prod_apply {s : Set (α × β)} (hs : Mea
surableSet s) : μ.prod ν s = ∫⁻ x, ν (Prod.mk x ⁻¹' s) ∂μ
-/
@[gcongr] theorem prod_mono [SFinite ν'] (h1 : μ ≤ μ') (h2 : ν ≤ ν') : μ.prod ν ≤ μ'.prod ν' := by
  apply Measure.le_iff.2 (fun s hs ↦ ?_)
  calc μ.prod ν s
  _ ≤ ∫⁻ x, ν (Prod.mk x ⁻¹' s) ∂μ := prod_apply_le hs
  _ ≤ ∫⁻ x, ν' (Prod.mk x ⁻¹' s) ∂μ' := by gcongr
  _ = (μ'.prod ν') s := (prod_apply hs).symm

/-- Note: the converse is not true. For a counterexample, see
  Walter Rudin *Real and Complex Analysis*, example (c) in section 8.9. It is true if the set is
  measurable, see `ae_prod_mem_iff_ae_ae_mem`. -/
/-
**MeasureTheory.Measure.ae_ae_of_ae_prod** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheor
y.Measure`。
形式化陈述：ae_ae_of_ae_prod {p : α × β -> Prop} (h : forallᵐ z ∂μ.prod ν, p z) : fora
llᵐ x ∂μ, forallᵐ y ∂ν, p (x, y)
参数：h : forallᵐ z ∂μ.prod ν, p z。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `MeasureTheory.Measure.measure_ae_null_of_prod_null`：measure_ae_null_of_p
rod_null {s : Set (α × β)} (h : μ.prod ν s = 0) : (fun x => ν (Prod.mk x ⁻¹' s))
 =ᵐ[μ] 0

--- 原说明 ---
Note: the converse is not true. For a counterexample, see
  Walter Rudin *Real and Complex Analysis*, example (c) in section 8.9. It is tr
ue if the set is
  measurable, see `ae_prod_mem_iff_ae_ae_mem`.
-/
theorem ae_ae_of_ae_prod {p : α × β → Prop} (h : ∀ᵐ z ∂μ.prod ν, p z) :
    ∀ᵐ x ∂μ, ∀ᵐ y ∂ν, p (x, y) :=
  measure_ae_null_of_prod_null h
/-
**MeasureTheory.Measure.ae_ae_eq_curry_of_prod** 是 Mathlib 中的一个定理，位于命名空间 `Measur
eTheory.Measure`。
形式化陈述：ae_ae_eq_curry_of_prod {γ : Type*} {f g : α × β -> γ} (h : f =ᵐ[μ.prod ν] 
g) : forallᵐ x ∂μ, curry f x =ᵐ[ν] curry g x
参数：h : f =ᵐ[μ.prod ν] g。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `MeasureTheory.Measure.ae_ae_of_ae_prod`：ae_ae_of_ae_prod {p : α × β -> P
rop} (h : forallᵐ z ∂μ.prod ν, p z) : forallᵐ x ∂μ, forallᵐ y ∂ν, p (x, y)
-/
theorem ae_ae_eq_curry_of_prod {γ : Type*} {f g : α × β → γ} (h : f =ᵐ[μ.prod ν] g) :
    ∀ᵐ x ∂μ, curry f x =ᵐ[ν] curry g x :=
  ae_ae_of_ae_prod h
/-
**MeasureTheory.Measure.ae_ae_eq_of_ae_eq_uncurry** 是 Mathlib 中的一个定理，位于命名空间 `Mea
sureTheory.Measure`。
形式化陈述：ae_ae_eq_of_ae_eq_uncurry {γ : Type*} {f g : α -> β -> γ} (h : uncurry f =
ᵐ[μ.prod ν] uncurry g) : forallᵐ x ∂μ, f x =ᵐ[ν] g x
参数：h : uncurry f =ᵐ[μ.prod ν] uncurry g。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `MeasureTheory.Measure.ae_ae_eq_curry_of_prod`：ae_ae_eq_curry_of_prod {γ 
: Type*} {f g : α × β -> γ} (h : f =ᵐ[μ.prod ν] g) : forallᵐ x ∂μ, curry f x =ᵐ[
ν] curry g x
-/
theorem ae_ae_eq_of_ae_eq_uncurry {γ : Type*} {f g : α → β → γ}
    (h : uncurry f =ᵐ[μ.prod ν] uncurry g) : ∀ᵐ x ∂μ, f x =ᵐ[ν] g x :=
  ae_ae_eq_curry_of_prod h
/-
**MeasureTheory.Measure.ae_prod_iff_ae_ae** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheo
ry.Measure`。
形式化陈述：ae_prod_iff_ae_ae {p : α × β -> Prop} (hp : MeasurableSet {x | p x}) : (fo
rallᵐ z ∂μ.prod ν, p z) ↔ forallᵐ x ∂μ, forallᵐ y ∂ν, p (x, y)
参数：hp : MeasurableSet {x | p x}。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.measure_prod_null`：measure_prod_null {s : Set (α ×
 β)} (hs : MeasurableSet s) : μ.prod ν s = 0 ↔ (fun x => ν (Prod.mk x ⁻¹' s)) =ᵐ
[μ] 0
· 使用定理 `MeasurableSet.compl`：∀ {α : Type u_1} {s : Set α} {m : MeasurableSpace α
}, MeasurableSet s → MeasurableSet sᶜ
-/
theorem ae_prod_iff_ae_ae {p : α × β → Prop} (hp : MeasurableSet {x | p x}) :
    (∀ᵐ z ∂μ.prod ν, p z) ↔ ∀ᵐ x ∂μ, ∀ᵐ y ∂ν, p (x, y) :=
  measure_prod_null hp.compl
/-
**MeasureTheory.Measure.ae_prod_mem_iff_ae_ae_mem** 是 Mathlib 中的一个定理，位于命名空间 `Mea
sureTheory.Measure`。
形式化陈述：ae_prod_mem_iff_ae_ae_mem {s : Set (α × β)} (hs : MeasurableSet s) : (fora
llᵐ z ∂μ.prod ν, z in s) ↔ forallᵐ x ∂μ, forallᵐ y ∂ν, (x, y) in s
参数：α × β；hs : MeasurableSet s。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.measure_prod_null`：measure_prod_null {s : Set (α ×
 β)} (hs : MeasurableSet s) : μ.prod ν s = 0 ↔ (fun x => ν (Prod.mk x ⁻¹' s)) =ᵐ
[μ] 0
· 使用定理 `MeasurableSet.compl`：∀ {α : Type u_1} {s : Set α} {m : MeasurableSpace α
}, MeasurableSet s → MeasurableSet sᶜ
-/
theorem ae_prod_mem_iff_ae_ae_mem {s : Set (α × β)} (hs : MeasurableSet s) :
    (∀ᵐ z ∂μ.prod ν, z ∈ s) ↔ ∀ᵐ x ∂μ, ∀ᵐ y ∂ν, (x, y) ∈ s :=
  measure_prod_null hs.compl

omit [SFinite ν] in
@[fun_prop]
/-
**MeasureTheory.Measure.quasiMeasurePreserving_fst** 是 Mathlib 中的一个定理，位于命名空间 `Me
asureTheory.Measure`。
形式化陈述：quasiMeasurePreserving_fst : QuasiMeasurePreserving Prod.fst (μ.prod ν) μ
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `measurable_fst`：measurable_fst {_ : MeasurableSpace α} {_ : MeasurableSp
ace β} : Measurable (Prod.fst : α × β -> α)
· 使用定理 `MeasureTheory.Measure.AbsolutelyContinuous.mk`：mk (h : forall ⦃s : Set α
⦄, MeasurableSet s -> ν s = 0 -> μ s = 0) : μ ≪ ν
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.Measure.map_apply`：map_apply (hf : Measurable f) {s : Set 
β} (hs : MeasurableSet s) : μ.map f s = μ (f ⁻¹' s)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.prod_univ`：prod_univ {s : Set α} : s ×ˢ (univ : Set β) = Prod.fst ⁻¹
' s
· 使用定理 `nonpos_iff_eq_zero`：∀ {α : Type u_1} {a : α} [inst : PartialOrder α] [in
st_1 : Zero α] [IsBotZeroClass α], a ≤ 0 ↔ a = 0
· 使用定理 `instIsBotZeroClass`：∀ {α : Type u} [inst : AddZeroClass α] [inst_1 : LE 
α] [CanonicallyOrderedAdd α], IsBotZeroClass α
· 使用定理 `ENNReal.instCanonicallyOrderedAdd`：CanonicallyOrderedAdd ENNReal
· 使用定理 `LE.le.trans_eq`：∀ {α : Type u_1} {a b c : α} [inst : LE α], a ≤ b → b = 
c → a ≤ c
· 使用定理 `MeasureTheory.Measure.prod_prod_le`：prod_prod_le (s : Set α) (t : Set β)
 : μ.prod ν (s ×ˢ t) <= μ s * ν t
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
-/
theorem quasiMeasurePreserving_fst : QuasiMeasurePreserving Prod.fst (μ.prod ν) μ := by
  refine ⟨measurable_fst, AbsolutelyContinuous.mk fun s hs h2s => ?_⟩
  rw [map_apply measurable_fst hs, ← prod_univ, ← nonpos_iff_eq_zero]
  refine (prod_prod_le _ _).trans_eq ?_
  rw [h2s, zero_mul]

omit [SFinite ν] in
@[fun_prop]
/-
**MeasureTheory.Measure.quasiMeasurePreserving_snd** 是 Mathlib 中的一个定理，位于命名空间 `Me
asureTheory.Measure`。
形式化陈述：quasiMeasurePreserving_snd : QuasiMeasurePreserving Prod.snd (μ.prod ν) ν
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `measurable_snd`：measurable_snd {_ : MeasurableSpace α} {_ : MeasurableSp
ace β} : Measurable (Prod.snd : α × β -> β)
· 使用定理 `MeasureTheory.Measure.AbsolutelyContinuous.mk`：mk (h : forall ⦃s : Set α
⦄, MeasurableSet s -> ν s = 0 -> μ s = 0) : μ ≪ ν
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.Measure.map_apply`：map_apply (hf : Measurable f) {s : Set 
β} (hs : MeasurableSet s) : μ.map f s = μ (f ⁻¹' s)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.univ_prod`：univ_prod {t : Set β} : (univ : Set α) ×ˢ t = Prod.snd ⁻¹
' t
· 使用定理 `nonpos_iff_eq_zero`：∀ {α : Type u_1} {a : α} [inst : PartialOrder α] [in
st_1 : Zero α] [IsBotZeroClass α], a ≤ 0 ↔ a = 0
· 使用定理 `instIsBotZeroClass`：∀ {α : Type u} [inst : AddZeroClass α] [inst_1 : LE 
α] [CanonicallyOrderedAdd α], IsBotZeroClass α
· 使用定理 `ENNReal.instCanonicallyOrderedAdd`：CanonicallyOrderedAdd ENNReal
· 使用定理 `LE.le.trans_eq`：∀ {α : Type u_1} {a b c : α} [inst : LE α], a ≤ b → b = 
c → a ≤ c
· 使用定理 `MeasureTheory.Measure.prod_prod_le`：prod_prod_le (s : Set α) (t : Set β)
 : μ.prod ν (s ×ˢ t) <= μ s * ν t
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
-/
theorem quasiMeasurePreserving_snd : QuasiMeasurePreserving Prod.snd (μ.prod ν) ν := by
  refine ⟨measurable_snd, AbsolutelyContinuous.mk fun s hs h2s => ?_⟩
  rw [map_apply measurable_snd hs, ← univ_prod, ← nonpos_iff_eq_zero]
  refine (prod_prod_le _ _).trans_eq ?_
  rw [h2s, mul_zero]

omit [SFinite ν] in
/-
**MeasureTheory.Measure.set_prod_ae_eq** 是 Mathlib 中的一个引理，位于命名空间 `MeasureTheory.
Measure`。
形式化陈述：set_prod_ae_eq {s s' : Set α} {t t' : Set β} (hs : s =ᵐ[μ] s') (ht : t =ᵐ[
ν] t') : (s ×ˢ t : Set (α × β)) =ᵐ[μ.prod ν] (s' ×ˢ t' : Set (α × β))
参数：hs : s =ᵐ[μ] s'；ht : t =ᵐ[ν] t'。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `Filter.EventuallyEq.inter`：∀ {α : Type u} {s t s' t' : Set α} {l : Filte
r α}, s =ᶠ[l] t → s' =ᶠ[l] t' → s ∩ s' =ᶠ[l] t ∩ t'
· 使用定理 `MeasureTheory.Measure.QuasiMeasurePreserving.preimage_ae_eq`：preimage_ae
_eq {s t : Set β} (hf : QuasiMeasurePreserving f μa μb) (h : s =ᵐ[μb] t) : f ⁻¹'
 s =ᵐ[μa] f ⁻¹' t
· 使用定理 `MeasureTheory.Measure.quasiMeasurePreserving_fst`：quasiMeasurePreserving
_fst : QuasiMeasurePreserving Prod.fst (μ.prod ν) μ
· 使用定理 `MeasureTheory.Measure.quasiMeasurePreserving_snd`：quasiMeasurePreserving
_snd : QuasiMeasurePreserving Prod.snd (μ.prod ν) ν
-/
lemma set_prod_ae_eq {s s' : Set α} {t t' : Set β} (hs : s =ᵐ[μ] s') (ht : t =ᵐ[ν] t') :
    (s ×ˢ t : Set (α × β)) =ᵐ[μ.prod ν] (s' ×ˢ t' : Set (α × β)) :=
  (quasiMeasurePreserving_fst.preimage_ae_eq hs).inter
    (quasiMeasurePreserving_snd.preimage_ae_eq ht)
/-
**MeasureTheory.Measure.measure_prod_compl_eq_zero** 是 Mathlib 中的一个引理，位于命名空间 `Me
asureTheory.Measure`。
形式化陈述：measure_prod_compl_eq_zero {s : Set α} {t : Set β} (s_ae_univ : μ sᶜ = 0) 
(t_ae_univ : ν tᶜ = 0) : μ.prod ν (s ×ˢ t)ᶜ = 0
参数：s_ae_univ : μ sᶜ = 0；t_ae_univ : ν tᶜ = 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Set.compl_prod_eq_union`：compl_prod_eq_union {α β : Type*} (s : Set α) (
t : Set β) : (s ×ˢ t)ᶜ = (sᶜ ×ˢ univ) union (univ ×ˢ tᶜ)
· 使用定理 `MeasureTheory.measure_union_null_iff`：measure_union_null_iff : μ (s unio
n t) = 0 ↔ μ s = 0 ∧ μ t = 0
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `MeasureTheory.Measure.prod_prod`：prod_prod (s : Set α) (t : Set β) : μ.p
rod ν (s ×ˢ t) = μ s * ν t
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
-/
lemma measure_prod_compl_eq_zero {s : Set α} {t : Set β}
    (s_ae_univ : μ sᶜ = 0) (t_ae_univ : ν tᶜ = 0) :
    μ.prod ν (s ×ˢ t)ᶜ = 0 := by
  rw [Set.compl_prod_eq_union, measure_union_null_iff]
  simp [s_ae_univ, t_ae_univ]

omit [SFinite ν] in
/-
**MeasureTheory.Measure._root_.MeasureTheory.NullMeasurableSet.prod** 是 Mathlib 
中的一个引理，位于命名空间 `MeasureTheory.Measure`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma _root_.MeasureTheory.NullMeasurableSet.prod {s : Set α} {t : Set β}
    (s_mble : NullMeasurableSet s μ) (t_mble : NullMeasurableSet t ν) :
    NullMeasurableSet (s ×ˢ t) (μ.prod ν) :=
  let ⟨s₀, mble_s₀, s_aeeq_s₀⟩ := s_mble
  let ⟨t₀, mble_t₀, t_aeeq_t₀⟩ := t_mble
  ⟨s₀ ×ˢ t₀, ⟨mble_s₀.prod mble_t₀, set_prod_ae_eq s_aeeq_s₀ t_aeeq_t₀⟩⟩

/-- If `s ×ˢ t` is a null measurable set and `μ s ≠ 0`, then `t` is a null measurable set. -/
/-
**MeasureTheory.Measure._root_.MeasureTheory.NullMeasurableSet.right_of_prod** 是
 Mathlib 中的一个引理，位于命名空间 `MeasureTheory.Measure`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `s ×ˢ t` is a null measurable set and `μ s ≠ 0`, then `t` is a null measurabl
e set.
-/
lemma _root_.MeasureTheory.NullMeasurableSet.right_of_prod {s : Set α} {t : Set β}
    (h : NullMeasurableSet (s ×ˢ t) (μ.prod ν)) (hs : μ s ≠ 0) : NullMeasurableSet t ν := by
  rcases h with ⟨u, hum, hu⟩
  obtain ⟨x, hxs, hx⟩ : ∃ x ∈ s, (Prod.mk x ⁻¹' (s ×ˢ t)) =ᵐ[ν] (Prod.mk x ⁻¹' u) :=
    ((frequently_ae_iff.2 hs).and_eventually (ae_ae_eq_curry_of_prod hu)).exists
  refine ⟨Prod.mk x ⁻¹' u, measurable_prodMk_left hum, ?_⟩
  rwa [mk_preimage_prod_right hxs] at hx

/-- If `Prod.snd ⁻¹' t` is a null measurable set and `μ ≠ 0`, then `t` is a null measurable set. -/
/-
**MeasureTheory.Measure._root_.MeasureTheory.NullMeasurableSet.of_preimage_snd**
 是 Mathlib 中的一个引理，位于命名空间 `MeasureTheory.Measure`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `Prod.snd ⁻¹' t` is a null measurable set and `μ ≠ 0`, then `t` is a null mea
surable set.
-/
lemma _root_.MeasureTheory.NullMeasurableSet.of_preimage_snd [NeZero μ] {t : Set β}
    (h : NullMeasurableSet (Prod.snd ⁻¹' t) (μ.prod ν)) : NullMeasurableSet t ν :=
  .right_of_prod (by rwa [univ_prod]) (NeZero.ne (μ univ))

/-- `Prod.snd ⁻¹' t` is null measurable w.r.t. `μ.prod ν` iff `t` is null measurable w.r.t. `ν`
provided that `μ ≠ 0`. -/
/-
**MeasureTheory.Measure.nullMeasurableSet_preimage_snd** 是 Mathlib 中的一个引理，位于命名空间
 `MeasureTheory.Measure`。
形式化陈述：nullMeasurableSet_preimage_snd [NeZero μ] {t : Set β} : NullMeasurableSet 
(Prod.snd ⁻¹' t) (μ.prod ν) ↔ NullMeasurableSet t ν
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.NullMeasurableSet.of_preimage_snd`：∀ {α : Type u_1} {β : T
ype u_2} [inst : MeasurableSpace α] [inst_1 : MeasurableSpace β] {μ : MeasureThe
ory.Measure α}   {ν : MeasureTheory.M…
· 使用定理 `MeasureTheory.NullMeasurableSet.preimage`：∀ {α : Type u_1} {β : Type u_2
} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {μa : MeasureTheory.Measure 
α}   {μb : MeasureTheory.Measu…
· 使用定理 `MeasureTheory.Measure.quasiMeasurePreserving_snd`：quasiMeasurePreserving
_snd : QuasiMeasurePreserving Prod.snd (μ.prod ν) ν

--- 原说明 ---
`Prod.snd ⁻¹' t` is null measurable w.r.t. `μ.prod ν` iff `t` is null measurable
 w.r.t. `ν`
provided that `μ ≠ 0`.
-/
lemma nullMeasurableSet_preimage_snd [NeZero μ] {t : Set β} :
    NullMeasurableSet (Prod.snd ⁻¹' t) (μ.prod ν) ↔ NullMeasurableSet t ν :=
  ⟨.of_preimage_snd, (.preimage · quasiMeasurePreserving_snd)⟩
/-
**MeasureTheory.Measure.nullMeasurable_comp_snd** 是 Mathlib 中的一个引理，位于命名空间 `Measu
reTheory.Measure`。
形式化陈述：nullMeasurable_comp_snd [NeZero μ] {f : β -> γ} : NullMeasurable (f ∘ Prod
.snd) (μ.prod ν) ↔ NullMeasurable f ν
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `forall₂_congr`：∀ {α : Sort u_1} {β : α → Sort u_2} {p q : (a : α) → β a 
→ Prop},   (∀ (a : α) (b : β a), p a b ↔ q a b) → ((∀ (a : α) (b : β a), p a b) 
↔ ∀…
· 使用引理 `MeasureTheory.Measure.nullMeasurableSet_preimage_snd`：nullMeasurableSet_
preimage_snd [NeZero μ] {t : Set β} : NullMeasurableSet (Prod.snd ⁻¹' t) (μ.prod
 ν) ↔ NullMeasurableSet t ν
-/
lemma nullMeasurable_comp_snd [NeZero μ] {f : β → γ} :
    NullMeasurable (f ∘ Prod.snd) (μ.prod ν) ↔ NullMeasurable f ν :=
  forall₂_congr fun s _ ↦ nullMeasurableSet_preimage_snd (t := f ⁻¹' s)

/-- `μ.prod ν` has finite spanning sets in rectangles of finite spanning sets. -/
/-
**MeasureTheory.Measure.FiniteSpanningSetsIn.prod** 是 Mathlib 中的一个定义，位于命名空间 `Mea
sureTheory.Measure.FiniteSpanningSetsIn`。
形式化陈述：{α : Type u_1} →   {β : Type u_2} →     [inst : MeasurableSpace α] →      
 [inst_1 : MeasurableSpace β] →         {μ : MeasureTheory.Measure α} →         
  {ν : MeasureTheory.Measure β} →             {C : Set (Set α)} →               
{D : Set (Set β)} →                 μ.FiniteSpanningSetsIn C →                  
 ν.FiniteSpanningSetsIn D → (μ.prod ν).FiniteSpanningSetsIn (Set.image2 (fun x1 
x2 => x1 ×ˢ x2) C D)
参数：Set α；Set β；μ.prod ν；Set.image2 (fun x1 x2 => x1 ×ˢ x2) C D。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`μ.prod ν` has finite spanning sets in rectangles of finite spanning sets.
-/
noncomputable def FiniteSpanningSetsIn.prod {ν : Measure β} {C : Set (Set α)} {D : Set (Set β)}
    (hμ : μ.FiniteSpanningSetsIn C) (hν : ν.FiniteSpanningSetsIn D) :
    (μ.prod ν).FiniteSpanningSetsIn (image2 (· ×ˢ ·) C D) := by
  haveI := hν.sigmaFinite
  refine
    ⟨fun n => hμ.set n.unpair.1 ×ˢ hν.set n.unpair.2, fun n =>
      mem_image2_of_mem (hμ.set_mem _) (hν.set_mem _), fun n => ?_, ?_⟩
  · rw [prod_prod]
    exact mul_lt_top (hμ.finite _) (hν.finite _)
  · simp_rw [iUnion_unpair_prod, hμ.spanning, hν.spanning, univ_prod_univ]
/-
**MeasureTheory.Measure.prod_sum_left** 是 Mathlib 中的一个引理，位于命名空间 `MeasureTheory.M
easure`。
形式化陈述：prod_sum_left {ι : Type*} (m : ι -> Measure α) (μ : Measure β) [SFinite μ]
 : (Measure.sum m).prod μ = Measure.sum (fun i => (m i).prod μ)
参数：m : ι -> Measure α；μ : Measure β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.ext`：ext (h : forall s, MeasurableSet s -> μ₁ s = 
μ₂ s) : μ₁ = μ₂
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.Measure.prod_apply`：prod_apply {s : Set (α × β)} (hs : Mea
surableSet s) : μ.prod ν s = ∫⁻ x, ν (Prod.mk x ⁻¹' s) ∂μ
· 使用定理 `MeasureTheory.lintegral_sum_measure`：lintegral_sum_measure {m : Measurab
leSpace α} {ι} (f : α -> Real>=0∞) (μ : ι -> Measure α) : ∫⁻ a, f a ∂Measure.sum
 μ = ∑' i, ∫⁻ a, f a ∂μ i
· 使用定理 `MeasureTheory.Measure.sum_apply`：sum_apply (f : ι -> Measure α) {s : Set
 α} (hs : MeasurableSet s) : sum f s = ∑' i, f i s
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma prod_sum_left {ι : Type*} (m : ι → Measure α) (μ : Measure β) [SFinite μ] :
    (Measure.sum m).prod μ = Measure.sum (fun i ↦ (m i).prod μ) := by
  ext s hs
  simp only [prod_apply hs, lintegral_sum_measure, hs, sum_apply]
/-
**MeasureTheory.Measure.prod_sum_right** 是 Mathlib 中的一个引理，位于命名空间 `MeasureTheory.
Measure`。
形式化陈述：prod_sum_right {ι' : Type*} [Countable ι'] (m : Measure α) (m' : ι' -> Mea
sure β) [forall n, SFinite (m' n)] : m.prod (Measure.sum m') = Measure.sum (fun 
p => m.prod (m' p))
参数：m : Measure α；m' : ι' -> Measure β；m' n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.ext`：ext (h : forall s, MeasurableSet s -> μ₁ s = 
μ₂ s) : μ₁ = μ₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.Measure.prod_apply`：prod_apply {s : Set (α × β)} (hs : Mea
surableSet s) : μ.prod ν s = ∫⁻ x, ν (Prod.mk x ⁻¹' s) ∂μ
· 使用定理 `MeasureTheory.instSFiniteSumOfCountable`：∀ {α : Type u_1} {ι : Type u_3}
 {m0 : MeasurableSpace α} [Countable ι] (m : ι → MeasureTheory.Measure α)   [∀ (
n : ι), MeasureTheory.SFinite…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `MeasureTheory.Measure.sum_apply`：sum_apply (f : ι -> Measure α) {s : Set
 α} (hs : MeasurableSet s) : sum f s = ∑' i, f i s
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `measurable_prodMk_left`：measurable_prodMk_left {x : α} : Measurable (@Pr
od.mk _ β x)
· 使用定理 `MeasureTheory.lintegral_tsum`：lintegral_tsum [Countable β] {f : β -> α -
> Real>=0∞} (hf : forall i, AEMeasurable (f i) μ) : ∫⁻ a, ∑' i, f i a ∂μ = ∑' i,
 ∫⁻ a, f i a ∂μ
· 使用定理 `Measurable.aemeasurable`：Measurable.aemeasurable (h : Measurable f) : AE
Measurable f μ
· 使用定理 `measurable_measure_prodMk_left`：measurable_measure_prodMk_left [SFinite 
ν] {s : Set (α × β)} (hs : MeasurableSet s) : Measurable fun x => ν (Prod.mk x ⁻
¹' s)
-/
lemma prod_sum_right {ι' : Type*} [Countable ι'] (m : Measure α) (m' : ι' → Measure β)
    [∀ n, SFinite (m' n)] :
    m.prod (Measure.sum m') = Measure.sum (fun p ↦ m.prod (m' p)) := by
  ext s hs
  simp only [prod_apply hs, hs, sum_apply]
  have M : ∀ x, MeasurableSet (Prod.mk x ⁻¹' s) := fun x => measurable_prodMk_left hs
  simp_rw [Measure.sum_apply _ (M _)]
  rw [lintegral_tsum (fun i ↦ (measurable_measure_prodMk_left hs).aemeasurable)]
/-
**MeasureTheory.Measure.prod_sum** 是 Mathlib 中的一个引理，位于命名空间 `MeasureTheory.Measur
e`。
形式化陈述：prod_sum {ι ι' : Type*} [Countable ι'] (m : ι -> Measure α) (m' : ι' -> Me
asure β) [forall n, SFinite (m' n)] : (Measure.sum m).prod (Measure.sum m') = Me
asure.sum (fun (p : ι × ι') => (m p.1).prod (m' p.2))
参数：m : ι -> Measure α；m' : ι' -> Measure β；m' n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `MeasureTheory.Measure.prod_sum_left`：prod_sum_left {ι : Type*} (m : ι ->
 Measure α) (μ : Measure β) [SFinite μ] : (Measure.sum m).prod μ = Measure.sum (
fun i => (m i).prod μ)
· 使用定理 `MeasureTheory.instSFiniteSumOfCountable`：∀ {α : Type u_1} {ι : Type u_3}
 {m0 : MeasurableSpace α} [Countable ι] (m : ι → MeasureTheory.Measure α)   [∀ (
n : ι), MeasureTheory.SFinite…
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用引理 `MeasureTheory.Measure.prod_sum_right`：prod_sum_right {ι' : Type*} [Count
able ι'] (m : Measure α) (m' : ι' -> Measure β) [forall n, SFinite (m' n)] : m.p
rod (Measure.sum m') = Mea…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `MeasureTheory.Measure.sum_sum`：sum_sum {ι' : Type*} (μ : ι -> ι' -> Meas
ure α) : (sum fun n => sum (μ n)) = sum (fun (p : ι × ι') => μ p.1 p.2)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma prod_sum {ι ι' : Type*} [Countable ι'] (m : ι → Measure α) (m' : ι' → Measure β)
    [∀ n, SFinite (m' n)] :
    (Measure.sum m).prod (Measure.sum m') =
      Measure.sum (fun (p : ι × ι') ↦ (m p.1).prod (m' p.2)) := by
  simp_rw [prod_sum_left, prod_sum_right, sum_sum]
/-
**MeasureTheory.Measure.prod.instSigmaFinite** 是 Mathlib 中的一个定理，位于命名空间 `MeasureT
heory.Measure.prod`。
形式化陈述：∀ {α : Type u_4} {β : Type u_5} {x : MeasurableSpace α} {μ : MeasureTheory
.Measure α} [MeasureTheory.SigmaFinite μ]   {x_1 : MeasurableSpace β} {ν : Measu
reTheory.Measure β} [MeasureTheory.SigmaFinite ν],   MeasureTheory.SigmaFinite (
μ.prod ν)
参数：μ.prod ν。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.FiniteSpanningSetsIn.sigmaFinite`：∀ {α : Type u_1}
 {m0 : MeasurableSpace α} {μ : MeasureTheory.Measure α} {C : Set (Set α)}   (h :
 μ.FiniteSpanningSetsIn C), MeasureTheory.Si…
-/
instance prod.instSigmaFinite {α β : Type*} {_ : MeasurableSpace α} {μ : Measure α}
    [SigmaFinite μ] {_ : MeasurableSpace β} {ν : Measure β} [SigmaFinite ν] :
    SigmaFinite (μ.prod ν) :=
  (μ.toFiniteSpanningSetsIn.prod ν.toFiniteSpanningSetsIn).sigmaFinite
/-
**MeasureTheory.Measure.prod.instSFinite** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheor
y.Measure.prod`。
形式化陈述：∀ {α : Type u_4} {β : Type u_5} {x : MeasurableSpace α} {μ : MeasureTheory
.Measure α} [MeasureTheory.SFinite μ]   {x_1 : MeasurableSpace β} {ν : MeasureTh
eory.Measure β} [MeasureTheory.SFinite ν], MeasureTheory.SFinite (μ.prod ν)
参数：μ.prod ν。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `MeasureTheory.sum_sfiniteSeq`：sum_sfiniteSeq (μ : Measure α) [h : SFinit
e μ] : sum (sfiniteSeq μ) = μ
· 使用引理 `MeasureTheory.Measure.prod_sum`：prod_sum {ι ι' : Type*} [Countable ι'] (
m : ι -> Measure α) (m' : ι' -> Measure β) [forall n, SFinite (m' n)] : (Measure
.sum m).prod (Measur…
· 使用定理 `instCountableNat`：Countable ℕ
· 使用定理 `MeasureTheory.instSFiniteOfSigmaFinite`：∀ {α : Type u_1} {m0 : Measurabl
eSpace α} {μ : MeasureTheory.Measure α} [MeasureTheory.SigmaFinite μ],   Measure
Theory.SFinite μ
· 使用定理 `MeasureTheory.IsFiniteMeasure.toSigmaFinite`：∀ {α : Type u_1} {_m0 : Mea
surableSpace α} (μ : MeasureTheory.Measure α) [MeasureTheory.IsFiniteMeasure μ],
   MeasureTheory.SigmaFinite μ
· 使用定理 `MeasureTheory.instSFiniteSumOfCountable`：∀ {α : Type u_1} {ι : Type u_3}
 {m0 : MeasurableSpace α} [Countable ι] (m : ι → MeasureTheory.Measure α)   [∀ (
n : ι), MeasureTheory.SFinite…
· 使用定理 `instCountableProd`：∀ {α : Type u} {β : Type v} [Countable α] [Countable 
β], Countable (α × β)
· 使用定理 `MeasureTheory.Measure.prod.instSigmaFinite`：∀ {α : Type u_4} {β : Type u
_5} {x : MeasurableSpace α} {μ : MeasureTheory.Measure α} [MeasureTheory.SigmaFi
nite μ]   {x_1 : MeasurableSpace…
-/
instance prod.instSFinite {α β : Type*} {_ : MeasurableSpace α} {μ : Measure α}
    [SFinite μ] {_ : MeasurableSpace β} {ν : Measure β} [SFinite ν] :
    SFinite (μ.prod ν) := by
  have : μ.prod ν =
      Measure.sum (fun (p : ℕ × ℕ) ↦ (sfiniteSeq μ p.1).prod (sfiniteSeq ν p.2)) := by
    conv_lhs => rw [← sum_sfiniteSeq μ, ← sum_sfiniteSeq ν]
    apply prod_sum
  rw [this]
  infer_instance
/-
**MeasureTheory.Measure.** 是 Mathlib 中的一个实例，位于命名空间 `MeasureTheory.Measure`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {α β} [MeasureSpace α] [SigmaFinite (volume : Measure α)]
    [MeasureSpace β] [SigmaFinite (volume : Measure β)] : SigmaFinite (volume : Measure (α × β)) :=
  prod.instSigmaFinite
/-
**MeasureTheory.Measure.** 是 Mathlib 中的一个实例，位于命名空间 `MeasureTheory.Measure`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {α β} [MeasureSpace α] [SFinite (volume : Measure α)]
    [MeasureSpace β] [SFinite (volume : Measure β)] : SFinite (volume : Measure (α × β)) :=
  prod.instSFinite

/-- A measure on a product space equals the product measure if they are equal on rectangles
  with as sides sets that generate the corresponding σ-algebras. -/
/-
**MeasureTheory.Measure.prod_eq_generateFrom** 是 Mathlib 中的一个定理，位于命名空间 `MeasureT
heory.Measure`。
形式化陈述：prod_eq_generateFrom {μ : Measure α} {ν : Measure β} {C : Set (Set α)} {D 
: Set (Set β)} (hC : generateFrom C = ‹_›) (hD : generateFrom D = ‹_›) (h2C : Is
PiSystem C) (h2D : IsPiSystem D) (h3C : μ.FiniteSpanningSetsIn C) (h3D : ν.Finit
eSpanningSetsIn D) {μν : Measure (α × β)} (h₁ : forall s in C, forall t in D, μν
 (s ×ˢ t) = μ s * ν t) : μ.prod ν = μν
参数：Set α；Set β；hC : generateFrom C = ‹_›；hD : generateFrom D = ‹_›；h2C : IsPiSys
tem C；h2D : IsPiSystem D；h3C : μ.FiniteSpanningSetsIn C；h3D : ν.FiniteSpanningSe
tsIn D；α × β；h₁ : forall s in C, forall t in D, μν (s ×ˢ t) = μ s * ν t。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.FiniteSpanningSetsIn.ext`：∀ {α : Type u_1} {m0 : M
easurableSpace α} {μ ν : MeasureTheory.Measure α} {C : Set (Set α)},   m0 = Meas
urableSpace.generateFrom C → IsPiSys…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `generateFrom_eq_prod`：generateFrom_eq_prod {C : Set (Set α)} {D : Set (S
et β)} (hC : generateFrom C = ‹_›) (hD : generateFrom D = ‹_›) (h2C : IsCountabl
ySpanning …
· 使用定理 `MeasureTheory.Measure.FiniteSpanningSetsIn.isCountablySpanning`：∀ {α : T
ype u_1} {m0 : MeasurableSpace α} {μ : MeasureTheory.Measure α} {C : Set (Set α)
}   (h : μ.FiniteSpanningSetsIn C), IsCountablySpann…
· 使用引理 `IsPiSystem.prod`：IsPiSystem.prod {C : Set (Set α)} {D : Set (Set β)} (hC
 : IsPiSystem C) (hD : IsPiSystem D) : IsPiSystem (image2 (· ×ˢ ·) C D)
· 使用定理 `MeasureTheory.Measure.FiniteSpanningSetsIn.sigmaFinite`：∀ {α : Type u_1}
 {m0 : MeasurableSpace α} {μ : MeasureTheory.Measure α} {C : Set (Set α)}   (h :
 μ.FiniteSpanningSetsIn C), MeasureTheory.Si…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.Measure.prod_prod`：prod_prod (s : Set α) (t : Set β) : μ.p
rod ν (s ×ˢ t) = μ s * ν t
· 使用定理 `MeasureTheory.instSFiniteOfSigmaFinite`：∀ {α : Type u_1} {m0 : Measurabl
eSpace α} {μ : MeasureTheory.Measure α} [MeasureTheory.SigmaFinite μ],   Measure
Theory.SFinite μ

--- 原说明 ---
A measure on a product space equals the product measure if they are equal on rec
tangles
  with as sides sets that generate the corresponding σ-algebras.
-/
theorem prod_eq_generateFrom {μ : Measure α} {ν : Measure β} {C : Set (Set α)} {D : Set (Set β)}
    (hC : generateFrom C = ‹_›) (hD : generateFrom D = ‹_›) (h2C : IsPiSystem C)
    (h2D : IsPiSystem D) (h3C : μ.FiniteSpanningSetsIn C) (h3D : ν.FiniteSpanningSetsIn D)
    {μν : Measure (α × β)} (h₁ : ∀ s ∈ C, ∀ t ∈ D, μν (s ×ˢ t) = μ s * ν t) : μ.prod ν = μν := by
  refine
    (h3C.prod h3D).ext
      (generateFrom_eq_prod hC hD h3C.isCountablySpanning h3D.isCountablySpanning).symm
      (h2C.prod h2D) ?_
  rintro _ ⟨s, hs, t, ht, rfl⟩
  have := h3D.sigmaFinite
  rw [h₁ s hs t ht, prod_prod]

/- Note that the next theorem is not true for s-finite measures: let `μ = ν = ∞ • Leb` on `[0,1]`
(they are s-finite as countable sums of the finite Lebesgue measure), and let `μν = μ.prod ν + λ`
where `λ` is Lebesgue measure on the diagonal. Then both measures give infinite mass to rectangles
`s × t` whose sides have positive Lebesgue measure, and `0` measure when one of the sides has zero
Lebesgue measure. And yet they do not coincide, as the first one gives zero mass to the diagonal,
and the second one gives mass one.
-/
/-- A measure on a product space equals the product measure of sigma-finite measures if they are
equal on rectangles. -/
/-
**MeasureTheory.Measure.prod_eq** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.Measure
`。
形式化陈述：prod_eq {μ : Measure α} [SigmaFinite μ] {ν : Measure β} [SigmaFinite ν] {μ
ν : Measure (α × β)} (h : forall s t, MeasurableSet s -> MeasurableSet t -> μν (
s ×ˢ t) = μ s * ν t) : μ.prod ν = μν
参数：α × β；h : forall s t, MeasurableSet s -> MeasurableSet t -> μν (s ×ˢ t) = μ s
 * ν t。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.prod_eq_generateFrom`：prod_eq_generateFrom {μ : Me
asure α} {ν : Measure β} {C : Set (Set α)} {D : Set (Set β)} (hC : generateFrom 
C = ‹_›) (hD : generateFrom D = …
· 使用定理 `MeasurableSpace.generateFrom_measurableSet`：generateFrom_measurableSet [
MeasurableSpace α] : generateFrom {s : Set α | MeasurableSet s} = ‹_›
· 使用定理 `MeasurableSpace.isPiSystem_measurableSet`：isPiSystem_measurableSet {α : 
Type*} [MeasurableSpace α] : IsPiSystem { s : Set α | MeasurableSet s }

--- 原说明 ---
A measure on a product space equals the product measure of sigma-finite measures
 if they are
equal on rectangles.
-/
theorem prod_eq {μ : Measure α} [SigmaFinite μ] {ν : Measure β} [SigmaFinite ν]
    {μν : Measure (α × β)}
    (h : ∀ s t, MeasurableSet s → MeasurableSet t → μν (s ×ˢ t) = μ s * ν t) : μ.prod ν = μν :=
  prod_eq_generateFrom generateFrom_measurableSet generateFrom_measurableSet
    isPiSystem_measurableSet isPiSystem_measurableSet μ.toFiniteSpanningSetsIn
    ν.toFiniteSpanningSetsIn fun s hs t ht => h s t hs ht

-- This is not true for σ-finite measures. See the discussion at
-- https://leanprover.zulipchat.com/#narrow/channel/116395-maths/topic/Uniqueness.20of.20sigma-finite.20measures.20on.20a.20product.20space/with/541741071
/-- Two finite measures on a product that are equal on products of sets are equal. -/
/-
**MeasureTheory.Measure.ext_prod** 是 Mathlib 中的一个引理，位于命名空间 `MeasureTheory.Measur
e`。
形式化陈述：ext_prod {α β : Type*} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {
μ ν : Measure (α × β)} [IsFiniteMeasure μ] (h : forall {s : Set α} {t : Set β}, 
MeasurableSet s -> MeasurableSet t -> μ (s ×ˢ t) = ν (s ×ˢ t)) : μ = ν
参数：α × β；h : forall {s : Set α} {t : Set β}, MeasurableSet s -> MeasurableSet t 
-> μ (s ×ˢ t) = ν (s ×ˢ t)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.ext`：ext (h : forall s, MeasurableSet s -> μ₁ s = 
μ₂ s) : μ₁ = μ₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.univ_prod_univ`：univ_prod_univ : @univ α ×ˢ @univ β = univ
· 使用定理 `MeasurableSet.univ`：∀ {α : Type u_1} {m : MeasurableSpace α}, Measurable
Set Set.univ
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `MeasurableSpace.induction_on_inter`：induction_on_inter {m : MeasurableSp
ace α} {C : forall s : Set α, MeasurableSet s -> Prop} {s : Set (Set α)} (h_eq :
 m = generateFrom s) (h_…
· 使用引理 `generateFrom_prod`：generateFrom_prod : generateFrom (image2 (· ×ˢ ·) { s
 : Set α | MeasurableSet s } { t : Set β | MeasurableSet t }) = Prod.instMeasura
bleSpac…
· 使用引理 `isPiSystem_prod`：isPiSystem_prod : IsPiSystem (image2 (· ×ˢ ·) { s : Set
 α | MeasurableSet s } { t : Set β | MeasurableSet t })
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `MeasureTheory.measure_empty`：measure_empty : μ ∅ = 0
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `MeasureTheory.measure_compl`：measure_compl (h₁ : MeasurableSet s) (h_fin
 : μ s != ∞) : μ sᶜ = μ univ - μ s
· 使用定理 `MeasureTheory.measure_ne_top`：measure_ne_top (μ : Measure α) [IsFiniteMe
asure μ] (s : Set α) : μ s != ∞
· 使用定理 `MeasureTheory.measure_iUnion`：measure_iUnion {m0 : MeasurableSpace α} {μ
 : Measure α} [Countable ι] {f : ι -> Set α} (hn : Pairwise (Disjoint on f)) (h 
: forall i, Measur…
· 使用定理 `instCountableNat`：Countable ℕ
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g

--- 原说明 ---
Two finite measures on a product that are equal on products of sets are equal.
-/
lemma ext_prod {α β : Type*} {mα : MeasurableSpace α} {mβ : MeasurableSpace β}
    {μ ν : Measure (α × β)} [IsFiniteMeasure μ]
    (h : ∀ {s : Set α} {t : Set β}, MeasurableSet s → MeasurableSet t → μ (s ×ˢ t) = ν (s ×ˢ t)) :
    μ = ν := by
  ext s hs
  have h_univ : μ univ = ν univ := by
    rw [← univ_prod_univ]
    exact h .univ .univ
  have : IsFiniteMeasure ν := ⟨by simp [← h_univ]⟩
  refine MeasurableSpace.induction_on_inter generateFrom_prod.symm isPiSystem_prod (by simp)
    ?_ ?_ ?_ s hs
  · rintro - ⟨s, hs, t, ht, rfl⟩
    exact h hs ht
  · intro t ht h
    simp_rw [measure_compl ht (measure_ne_top _ _), h, h_univ]
  · intro f h_disj hf h_eq
    simp_rw [measure_iUnion h_disj hf, h_eq]

/-- Two finite measures on a product are equal iff they are equal on products of sets. -/
/-
**MeasureTheory.Measure.ext_prod_iff** 是 Mathlib 中的一个引理，位于命名空间 `MeasureTheory.Me
asure`。
形式化陈述：ext_prod_iff {α β : Type*} {mα : MeasurableSpace α} {mβ : MeasurableSpace 
β} {μ ν : Measure (α × β)} [IsFiniteMeasure μ] : μ = ν ↔ forall {s : Set α} {t :
 Set β}, MeasurableSet s -> MeasurableSet t -> μ (s ×ˢ t) = ν (s ×ˢ t)
参数：α × β。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `MeasureTheory.Measure.ext_prod`：ext_prod {α β : Type*} {mα : MeasurableS
pace α} {mβ : MeasurableSpace β} {μ ν : Measure (α × β)} [IsFiniteMeasure μ] (h 
: forall {s : Set α}…

--- 原说明 ---
Two finite measures on a product are equal iff they are equal on products of set
s.
-/
lemma ext_prod_iff {α β : Type*} {mα : MeasurableSpace α} {mβ : MeasurableSpace β}
    {μ ν : Measure (α × β)} [IsFiniteMeasure μ] :
    μ = ν
      ↔ ∀ {s : Set α} {t : Set β}, MeasurableSet s → MeasurableSet t → μ (s ×ˢ t) = ν (s ×ˢ t) :=
  ⟨fun h s t hs ht ↦ by rw [h], Measure.ext_prod⟩

/-- Two finite measures on a product `α × β × γ` that are equal on products of sets are equal.
See `ext_prod₃'` for the same statement for `(α × β) × γ`. -/
/-
**MeasureTheory.Measure.ext_prod** 是 Mathlib 中的一个引理，位于命名空间 `MeasureTheory.Measur
e`。
形式化陈述：ext_prod {α β : Type*} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {
μ ν : Measure (α × β)} [IsFiniteMeasure μ] (h : forall {s : Set α} {t : Set β}, 
MeasurableSet s -> MeasurableSet t -> μ (s ×ˢ t) = ν (s ×ˢ t)) : μ = ν
参数：α × β；h : forall {s : Set α} {t : Set β}, MeasurableSet s -> MeasurableSet t 
-> μ (s ×ˢ t) = ν (s ×ˢ t)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.ext`：ext (h : forall s, MeasurableSet s -> μ₁ s = 
μ₂ s) : μ₁ = μ₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.univ_prod_univ`：univ_prod_univ : @univ α ×ˢ @univ β = univ
· 使用定理 `MeasurableSet.univ`：∀ {α : Type u_1} {m : MeasurableSpace α}, Measurable
Set Set.univ
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `MeasurableSpace.induction_on_inter`：induction_on_inter {m : MeasurableSp
ace α} {C : forall s : Set α, MeasurableSet s -> Prop} {s : Set (Set α)} (h_eq :
 m = generateFrom s) (h_…
· 使用引理 `generateFrom_prod`：generateFrom_prod : generateFrom (image2 (· ×ˢ ·) { s
 : Set α | MeasurableSet s } { t : Set β | MeasurableSet t }) = Prod.instMeasura
bleSpac…
· 使用引理 `isPiSystem_prod`：isPiSystem_prod : IsPiSystem (image2 (· ×ˢ ·) { s : Set
 α | MeasurableSet s } { t : Set β | MeasurableSet t })
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `MeasureTheory.measure_empty`：measure_empty : μ ∅ = 0
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `MeasureTheory.measure_compl`：measure_compl (h₁ : MeasurableSet s) (h_fin
 : μ s != ∞) : μ sᶜ = μ univ - μ s
· 使用定理 `MeasureTheory.measure_ne_top`：measure_ne_top (μ : Measure α) [IsFiniteMe
asure μ] (s : Set α) : μ s != ∞
· 使用定理 `MeasureTheory.measure_iUnion`：measure_iUnion {m0 : MeasurableSpace α} {μ
 : Measure α} [Countable ι] {f : ι -> Set α} (hn : Pairwise (Disjoint on f)) (h 
: forall i, Measur…
· 使用定理 `instCountableNat`：Countable ℕ
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g

--- 原说明 ---
Two finite measures on a product `α × β × γ` that are equal on products of sets 
are equal.
See `ext_prod₃'` for the same statement for `(α × β) × γ`.
-/
lemma ext_prod₃ {α β γ : Type*} {mα : MeasurableSpace α} {mβ : MeasurableSpace β}
    {mγ : MeasurableSpace γ} {μ ν : Measure (α × β × γ)} [IsFiniteMeasure μ]
    (h : ∀ {s : Set α} {t : Set β} {u : Set γ},
      MeasurableSet s → MeasurableSet t → MeasurableSet u → μ (s ×ˢ t ×ˢ u) = ν (s ×ˢ t ×ˢ u)) :
    μ = ν := by
  ext s hs
  have h_univ : μ univ = ν univ := by
    simp_rw [← univ_prod_univ]
    exact h .univ .univ .univ
  have : IsFiniteMeasure ν := ⟨by simp [← h_univ]⟩
  let C₂ := image2 (· ×ˢ ·) { t : Set β | MeasurableSet t } { u : Set γ | MeasurableSet u }
  let C := image2 (· ×ˢ ·) { s : Set α | MeasurableSet s } C₂
  refine MeasurableSpace.induction_on_inter (s := C) ?_ ?_ (by simp) ?_ ?_ ?_ s hs
  · refine (generateFrom_eq_prod (C := { s : Set α | MeasurableSet s }) (D := C₂) (by simp)
      generateFrom_prod isCountablySpanning_measurableSet ?_).symm
    exact isCountablySpanning_measurableSet.prod isCountablySpanning_measurableSet
  · exact MeasurableSpace.isPiSystem_measurableSet.prod isPiSystem_prod
  · rintro - ⟨s, hs, -, ⟨t, ht, u, hu, rfl⟩, rfl⟩
    exact h hs ht hu
  · intro t ht h
    simp_rw [measure_compl ht (measure_ne_top _ _), h, h_univ]
  · intro f h_disj hf h_eq
    simp_rw [measure_iUnion h_disj hf, h_eq]

/-- Two finite measures on a product `α × β × γ` are equal iff they are equal on products of sets.
See `ext_prod₃_iff'` for the same statement for `(α × β) × γ`. -/
/-
**MeasureTheory.Measure.ext_prod** 是 Mathlib 中的一个引理，位于命名空间 `MeasureTheory.Measur
e`。
形式化陈述：ext_prod {α β : Type*} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {
μ ν : Measure (α × β)} [IsFiniteMeasure μ] (h : forall {s : Set α} {t : Set β}, 
MeasurableSet s -> MeasurableSet t -> μ (s ×ˢ t) = ν (s ×ˢ t)) : μ = ν
参数：α × β；h : forall {s : Set α} {t : Set β}, MeasurableSet s -> MeasurableSet t 
-> μ (s ×ˢ t) = ν (s ×ˢ t)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.ext`：ext (h : forall s, MeasurableSet s -> μ₁ s = 
μ₂ s) : μ₁ = μ₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.univ_prod_univ`：univ_prod_univ : @univ α ×ˢ @univ β = univ
· 使用定理 `MeasurableSet.univ`：∀ {α : Type u_1} {m : MeasurableSpace α}, Measurable
Set Set.univ
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `MeasurableSpace.induction_on_inter`：induction_on_inter {m : MeasurableSp
ace α} {C : forall s : Set α, MeasurableSet s -> Prop} {s : Set (Set α)} (h_eq :
 m = generateFrom s) (h_…
· 使用引理 `generateFrom_prod`：generateFrom_prod : generateFrom (image2 (· ×ˢ ·) { s
 : Set α | MeasurableSet s } { t : Set β | MeasurableSet t }) = Prod.instMeasura
bleSpac…
· 使用引理 `isPiSystem_prod`：isPiSystem_prod : IsPiSystem (image2 (· ×ˢ ·) { s : Set
 α | MeasurableSet s } { t : Set β | MeasurableSet t })
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `MeasureTheory.measure_empty`：measure_empty : μ ∅ = 0
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `MeasureTheory.measure_compl`：measure_compl (h₁ : MeasurableSet s) (h_fin
 : μ s != ∞) : μ sᶜ = μ univ - μ s
· 使用定理 `MeasureTheory.measure_ne_top`：measure_ne_top (μ : Measure α) [IsFiniteMe
asure μ] (s : Set α) : μ s != ∞
· 使用定理 `MeasureTheory.measure_iUnion`：measure_iUnion {m0 : MeasurableSpace α} {μ
 : Measure α} [Countable ι] {f : ι -> Set α} (hn : Pairwise (Disjoint on f)) (h 
: forall i, Measur…
· 使用定理 `instCountableNat`：Countable ℕ
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g

--- 原说明 ---
Two finite measures on a product `α × β × γ` are equal iff they are equal on pro
ducts of sets.
See `ext_prod₃_iff'` for the same statement for `(α × β) × γ`.
-/
lemma ext_prod₃_iff {α β γ : Type*} {mα : MeasurableSpace α} {mβ : MeasurableSpace β}
    {mγ : MeasurableSpace γ} {μ ν : Measure (α × β × γ)} [IsFiniteMeasure μ] :
    μ = ν ↔ (∀ {s : Set α} {t : Set β} {u : Set γ},
      MeasurableSet s → MeasurableSet t → MeasurableSet u → μ (s ×ˢ t ×ˢ u) = ν (s ×ˢ t ×ˢ u)) :=
  ⟨fun h s t u hs ht hu ↦ by rw [h], Measure.ext_prod₃⟩

/-- Two finite measures on a product `(α × β) × γ` are equal iff they are equal on products of sets.
See `ext_prod₃_iff` for the same statement for `α × β × γ`. -/
/-
**MeasureTheory.Measure.ext_prod** 是 Mathlib 中的一个引理，位于命名空间 `MeasureTheory.Measur
e`。
形式化陈述：ext_prod {α β : Type*} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {
μ ν : Measure (α × β)} [IsFiniteMeasure μ] (h : forall {s : Set α} {t : Set β}, 
MeasurableSet s -> MeasurableSet t -> μ (s ×ˢ t) = ν (s ×ˢ t)) : μ = ν
参数：α × β；h : forall {s : Set α} {t : Set β}, MeasurableSet s -> MeasurableSet t 
-> μ (s ×ˢ t) = ν (s ×ˢ t)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.ext`：ext (h : forall s, MeasurableSet s -> μ₁ s = 
μ₂ s) : μ₁ = μ₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.univ_prod_univ`：univ_prod_univ : @univ α ×ˢ @univ β = univ
· 使用定理 `MeasurableSet.univ`：∀ {α : Type u_1} {m : MeasurableSpace α}, Measurable
Set Set.univ
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `MeasurableSpace.induction_on_inter`：induction_on_inter {m : MeasurableSp
ace α} {C : forall s : Set α, MeasurableSet s -> Prop} {s : Set (Set α)} (h_eq :
 m = generateFrom s) (h_…
· 使用引理 `generateFrom_prod`：generateFrom_prod : generateFrom (image2 (· ×ˢ ·) { s
 : Set α | MeasurableSet s } { t : Set β | MeasurableSet t }) = Prod.instMeasura
bleSpac…
· 使用引理 `isPiSystem_prod`：isPiSystem_prod : IsPiSystem (image2 (· ×ˢ ·) { s : Set
 α | MeasurableSet s } { t : Set β | MeasurableSet t })
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `MeasureTheory.measure_empty`：measure_empty : μ ∅ = 0
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `MeasureTheory.measure_compl`：measure_compl (h₁ : MeasurableSet s) (h_fin
 : μ s != ∞) : μ sᶜ = μ univ - μ s
· 使用定理 `MeasureTheory.measure_ne_top`：measure_ne_top (μ : Measure α) [IsFiniteMe
asure μ] (s : Set α) : μ s != ∞
· 使用定理 `MeasureTheory.measure_iUnion`：measure_iUnion {m0 : MeasurableSpace α} {μ
 : Measure α} [Countable ι] {f : ι -> Set α} (hn : Pairwise (Disjoint on f)) (h 
: forall i, Measur…
· 使用定理 `instCountableNat`：Countable ℕ
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g

--- 原说明 ---
Two finite measures on a product `(α × β) × γ` are equal iff they are equal on p
roducts of sets.
See `ext_prod₃_iff` for the same statement for `α × β × γ`.
-/
lemma ext_prod₃_iff' {α β γ : Type*} {mα : MeasurableSpace α} {mβ : MeasurableSpace β}
    {mγ : MeasurableSpace γ} {μ ν : Measure ((α × β) × γ)} [IsFiniteMeasure μ] :
    μ = ν ↔ (∀ {s : Set α} {t : Set β} {u : Set γ},
      MeasurableSet s → MeasurableSet t → MeasurableSet u →
      μ ((s ×ˢ t) ×ˢ u) = ν ((s ×ˢ t) ×ˢ u)) := by
  rw [← MeasurableEquiv.prodAssoc.map_measurableEquiv_injective.eq_iff, ext_prod₃_iff]
  have h_eq (ν : Measure ((α × β) × γ)) {s : Set α} {t : Set β} {u : Set γ}
      (hs : MeasurableSet s) (ht : MeasurableSet t) (hu : MeasurableSet u) :
      ν.map MeasurableEquiv.prodAssoc (s ×ˢ (t ×ˢ u)) = ν ((s ×ˢ t) ×ˢ u) := by
    rw [map_apply (by fun_prop) (hs.prod (ht.prod hu))]
    congr 1 with x
    simp [MeasurableEquiv.prodAssoc]
  refine ⟨fun h s t u hs ht hu ↦ ?_, fun h s t u hs ht hu ↦ ?_⟩ <;> specialize h hs ht hu
  · rwa [h_eq μ hs ht hu, h_eq ν hs ht hu] at h
  · rwa [h_eq μ hs ht hu, h_eq ν hs ht hu]

/-- Two finite measures on a product `(α × β) × γ` that are equal on products of sets are equal.
See `ext_prod₃` for the same statement for `α × β × γ`. -/
alias ⟨_, ext_prod₃'⟩ := ext_prod₃_iff'

variable [SFinite μ]

/-
**MeasureTheory.Measure.prod_swap** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.Measu
re`。
形式化陈述：prod_swap : map Prod.swap (μ.prod ν) = ν.prod μ
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.ext`：ext (h : forall s, MeasurableSet s -> μ₁ s = 
μ₂ s) : μ₁ = μ₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.Measure.sum_apply`：sum_apply (f : ι -> Measure α) {s : Set
 α} (hs : MeasurableSet s) : sum f s = ∑' i, f i s
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Equiv.tsum_eq`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} [inst : Ad
dCommMonoid α] [inst_1 : TopologicalSpace α] (e : γ ≃ β)   (f : β → α), ∑' (c : 
γ),…
· 使用引理 `MeasureTheory.sum_sfiniteSeq`：sum_sfiniteSeq (μ : Measure α) [h : SFinit
e μ] : sum (sfiniteSeq μ) = μ
· 使用引理 `MeasureTheory.Measure.prod_sum`：prod_sum {ι ι' : Type*} [Countable ι'] (
m : ι -> Measure α) (m' : ι' -> Measure β) [forall n, SFinite (m' n)] : (Measure
.sum m).prod (Measur…
· 使用定理 `instCountableNat`：Countable ℕ
· 使用定理 `MeasureTheory.instSFiniteOfSigmaFinite`：∀ {α : Type u_1} {m0 : Measurabl
eSpace α} {μ : MeasureTheory.Measure α} [MeasureTheory.SigmaFinite μ],   Measure
Theory.SFinite μ
· 使用定理 `MeasureTheory.IsFiniteMeasure.toSigmaFinite`：∀ {α : Type u_1} {_m0 : Mea
surableSpace α} (μ : MeasureTheory.Measure α) [MeasureTheory.IsFiniteMeasure μ],
   MeasureTheory.SigmaFinite μ
· 使用引理 `MeasureTheory.Measure.map_sum`：map_sum {ι : Type*} {m : ι -> Measure α} 
{f : α -> β} (hf : AEMeasurable f (Measure.sum m)) : Measure.map f (Measure.sum 
m) = Measure.sum (f…
· 使用定理 `Measurable.aemeasurable`：Measurable.aemeasurable (h : Measurable f) : AE
Measurable f μ
· 使用定理 `measurable_swap`：measurable_swap : Measurable (Prod.swap : α × β -> β × 
α)
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `MeasureTheory.Measure.prod_eq`：prod_eq {μ : Measure α} [SigmaFinite μ] {
ν : Measure β} [SigmaFinite ν] {μν : Measure (α × β)} (h : forall s t, Measurabl
eSet s -> Measurabl…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `MeasureTheory.Measure.map_apply`：map_apply (hf : Measurable f) {s : Set 
β} (hs : MeasurableSet s) : μ.map f s = μ (f ⁻¹' s)
· 使用定理 `MeasurableSet.prod`：∀ {α : Type u_1} {β : Type u_2} {m : MeasurableSpace
 α} {mβ : MeasurableSpace β} {s : Set α} {t : Set β},   MeasurableSet s → Measur
ableSet …
· 使用定理 `Set.preimage_swap_prod`：preimage_swap_prod (s : Set α) (t : Set β) : Pro
d.swap ⁻¹' s ×ˢ t = t ×ˢ s
· 使用定理 `MeasureTheory.Measure.prod_prod`：prod_prod (s : Set α) (t : Set β) : μ.p
rod ν (s ×ˢ t) = μ s * ν t
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem prod_swap : map Prod.swap (μ.prod ν) = ν.prod μ := by
  have : sum (fun (i : ℕ × ℕ) ↦ map Prod.swap ((sfiniteSeq μ i.1).prod (sfiniteSeq ν i.2)))
       = sum (fun (i : ℕ × ℕ) ↦ map Prod.swap ((sfiniteSeq μ i.2).prod (sfiniteSeq ν i.1))) := by
    ext s hs
    rw [sum_apply _ hs, sum_apply _ hs]
    exact ((Equiv.prodComm ℕ ℕ).tsum_eq _).symm
  rw [← sum_sfiniteSeq μ, ← sum_sfiniteSeq ν, prod_sum, prod_sum,
    map_sum measurable_swap.aemeasurable, this]
  congr 1
  ext1 i
  refine (prod_eq ?_).symm
  intro s t hs ht
  simp_rw [map_apply measurable_swap (hs.prod ht), preimage_swap_prod, prod_prod, mul_comm]
/-
**MeasureTheory.Measure.measurePreserving_swap** 是 Mathlib 中的一个定理，位于命名空间 `Measur
eTheory.Measure`。
形式化陈述：measurePreserving_swap : MeasurePreserving Prod.swap (μ.prod ν) (ν.prod μ)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `measurable_swap`：measurable_swap : Measurable (Prod.swap : α × β -> β × 
α)
· 使用定理 `MeasureTheory.Measure.prod_swap`：prod_swap : map Prod.swap (μ.prod ν) = 
ν.prod μ
-/
theorem measurePreserving_swap : MeasurePreserving Prod.swap (μ.prod ν) (ν.prod μ) :=
  ⟨measurable_swap, prod_swap⟩
/-
**MeasureTheory.Measure.prod_apply_symm** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory
.Measure`。
形式化陈述：prod_apply_symm {s : Set (α × β)} (hs : MeasurableSet s) : μ.prod ν s = ∫⁻
 y, μ ((fun x => (x, y)) ⁻¹' s) ∂ν
参数：α × β；hs : MeasurableSet s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.Measure.prod_swap`：prod_swap : map Prod.swap (μ.prod ν) = 
ν.prod μ
· 使用定理 `MeasureTheory.Measure.map_apply`：map_apply (hf : Measurable f) {s : Set 
β} (hs : MeasurableSet s) : μ.map f s = μ (f ⁻¹' s)
· 使用定理 `measurable_swap`：measurable_swap : Measurable (Prod.swap : α × β -> β × 
α)
· 使用定理 `MeasureTheory.Measure.prod_apply`：prod_apply {s : Set (α × β)} (hs : Mea
surableSet s) : μ.prod ν s = ∫⁻ x, ν (Prod.mk x ⁻¹' s) ∂μ
-/
theorem prod_apply_symm {s : Set (α × β)} (hs : MeasurableSet s) :
    μ.prod ν s = ∫⁻ y, μ ((fun x => (x, y)) ⁻¹' s) ∂ν := by
  rw [← prod_swap, map_apply measurable_swap hs, prod_apply (measurable_swap hs)]
  rfl
/-
**MeasureTheory.Measure.ae_ae_comm** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.Meas
ure`。
形式化陈述：ae_ae_comm {p : α -> β -> Prop} (h : MeasurableSet {x : α × β | p x.1 x.2}
) : (forallᵐ x ∂μ, forallᵐ y ∂ν, p x y) ↔ forallᵐ y ∂ν, forallᵐ x ∂μ, p x y
参数：h : MeasurableSet {x : α × β | p x.1 x.2}。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用定理 `MeasureTheory.Measure.ae_prod_iff_ae_ae`：ae_prod_iff_ae_ae {p : α × β ->
 Prop} (hp : MeasurableSet {x | p x}) : (forallᵐ z ∂μ.prod ν, p z) ↔ forallᵐ x ∂
μ, forallᵐ y ∂ν, p (x, y)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.Measure.prod_swap`：prod_swap : map Prod.swap (μ.prod ν) = 
ν.prod μ
· 使用定理 `MeasureTheory.ae_map_iff`：ae_map_iff {f : α -> β} (hf : AEMeasurable f μ
) {p : β -> Prop} (hp : MeasurableSet { x | p x }) : (forallᵐ y ∂μ.map f, p y) ↔
 forallᵐ x ∂μ,…
· 使用定理 `Measurable.aemeasurable`：Measurable.aemeasurable (h : Measurable f) : AE
Measurable f μ
· 使用定理 `measurable_swap`：measurable_swap : Measurable (Prod.swap : α × β -> β × 
α)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem ae_ae_comm {p : α → β → Prop} (h : MeasurableSet {x : α × β | p x.1 x.2}) :
    (∀ᵐ x ∂μ, ∀ᵐ y ∂ν, p x y) ↔ ∀ᵐ y ∂ν, ∀ᵐ x ∂μ, p x y := calc
  _ ↔ ∀ᵐ x ∂μ.prod ν, p x.1 x.2 := .symm <| ae_prod_iff_ae_ae h
  _ ↔ ∀ᵐ x ∂ν.prod μ, p x.2 x.1 := by rw [← prod_swap, ae_map_iff (by fun_prop) h]; simp
  _ ↔ ∀ᵐ y ∂ν, ∀ᵐ x ∂μ, p x y := ae_prod_iff_ae_ae <| measurable_swap h

/-- If `s ×ˢ t` is a null measurable set and `ν t ≠ 0`, then `s` is a null measurable set. -/
/-
**MeasureTheory.Measure._root_.MeasureTheory.NullMeasurableSet.left_of_prod** 是 
Mathlib 中的一个引理，位于命名空间 `MeasureTheory.Measure`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `s ×ˢ t` is a null measurable set and `ν t ≠ 0`, then `s` is a null measurabl
e set.
-/
lemma _root_.MeasureTheory.NullMeasurableSet.left_of_prod {s : Set α} {t : Set β}
    (h : NullMeasurableSet (s ×ˢ t) (μ.prod ν)) (ht : ν t ≠ 0) : NullMeasurableSet s μ := by
  refine .right_of_prod ?_ ht
  rw [← preimage_swap_prod]
  exact h.preimage measurePreserving_swap.quasiMeasurePreserving

/-- If `Prod.fst ⁻¹' s` is a null measurable set and `ν ≠ 0`, then `s` is a null measurable set. -/
/-
**MeasureTheory.Measure._root_.MeasureTheory.NullMeasurableSet.of_preimage_fst**
 是 Mathlib 中的一个引理，位于命名空间 `MeasureTheory.Measure`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `Prod.fst ⁻¹' s` is a null measurable set and `ν ≠ 0`, then `s` is a null mea
surable set.
-/
lemma _root_.MeasureTheory.NullMeasurableSet.of_preimage_fst [NeZero ν] {s : Set α}
    (h : NullMeasurableSet (Prod.fst ⁻¹' s) (μ.prod ν)) : NullMeasurableSet s μ :=
  .left_of_prod (by rwa [prod_univ]) (NeZero.ne (ν univ))

/-- `Prod.fst ⁻¹' s` is null measurable w.r.t. `μ.prod ν` iff `s` is null measurable w.r.t. `μ`
provided that `ν ≠ 0`. -/
/-
**MeasureTheory.Measure.nullMeasurableSet_preimage_fst** 是 Mathlib 中的一个引理，位于命名空间
 `MeasureTheory.Measure`。
形式化陈述：nullMeasurableSet_preimage_fst [NeZero ν] {s : Set α} : NullMeasurableSet 
(Prod.fst ⁻¹' s) (μ.prod ν) ↔ NullMeasurableSet s μ
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.NullMeasurableSet.of_preimage_fst`：∀ {α : Type u_1} {β : T
ype u_2} [inst : MeasurableSpace α] [inst_1 : MeasurableSpace β] {μ : MeasureThe
ory.Measure α}   {ν : MeasureTheory.M…
· 使用定理 `MeasureTheory.NullMeasurableSet.preimage`：∀ {α : Type u_1} {β : Type u_2
} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {μa : MeasureTheory.Measure 
α}   {μb : MeasureTheory.Measu…
· 使用定理 `MeasureTheory.Measure.quasiMeasurePreserving_fst`：quasiMeasurePreserving
_fst : QuasiMeasurePreserving Prod.fst (μ.prod ν) μ

--- 原说明 ---
`Prod.fst ⁻¹' s` is null measurable w.r.t. `μ.prod ν` iff `s` is null measurable
 w.r.t. `μ`
provided that `ν ≠ 0`.
-/
lemma nullMeasurableSet_preimage_fst [NeZero ν] {s : Set α} :
    NullMeasurableSet (Prod.fst ⁻¹' s) (μ.prod ν) ↔ NullMeasurableSet s μ :=
  ⟨.of_preimage_fst, (.preimage · quasiMeasurePreserving_fst)⟩
/-
**MeasureTheory.Measure.nullMeasurable_comp_fst** 是 Mathlib 中的一个引理，位于命名空间 `Measu
reTheory.Measure`。
形式化陈述：nullMeasurable_comp_fst [NeZero ν] {f : α -> γ} : NullMeasurable (f ∘ Prod
.fst) (μ.prod ν) ↔ NullMeasurable f μ
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `forall₂_congr`：∀ {α : Sort u_1} {β : α → Sort u_2} {p q : (a : α) → β a 
→ Prop},   (∀ (a : α) (b : β a), p a b ↔ q a b) → ((∀ (a : α) (b : β a), p a b) 
↔ ∀…
· 使用引理 `MeasureTheory.Measure.nullMeasurableSet_preimage_fst`：nullMeasurableSet_
preimage_fst [NeZero ν] {s : Set α} : NullMeasurableSet (Prod.fst ⁻¹' s) (μ.prod
 ν) ↔ NullMeasurableSet s μ
-/
lemma nullMeasurable_comp_fst [NeZero ν] {f : α → γ} :
    NullMeasurable (f ∘ Prod.fst) (μ.prod ν) ↔ NullMeasurable f μ :=
  forall₂_congr fun s _ ↦ nullMeasurableSet_preimage_fst (s := f ⁻¹' s)

/-- The product of two non-null sets is null measurable
if and only if both of them are null measurable. -/
/-
**MeasureTheory.Measure.nullMeasurableSet_prod_of_ne_zero** 是 Mathlib 中的一个引理，位于命
名空间 `MeasureTheory.Measure`。
形式化陈述：nullMeasurableSet_prod_of_ne_zero {s : Set α} {t : Set β} (hs : μ s != 0) 
(ht : ν t != 0) : NullMeasurableSet (s ×ˢ t) (μ.prod ν) ↔ NullMeasurableSet s μ 
∧ NullMeasurableSet t ν
参数：hs : μ s != 0；ht : ν t != 0。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.NullMeasurableSet.left_of_prod`：∀ {α : Type u_1} {β : Type
 u_2} [inst : MeasurableSpace α] [inst_1 : MeasurableSpace β] {μ : MeasureTheory
.Measure α}   {ν : MeasureTheory.M…
· 使用定理 `MeasureTheory.NullMeasurableSet.right_of_prod`：∀ {α : Type u_1} {β : Typ
e u_2} [inst : MeasurableSpace α] [inst_1 : MeasurableSpace β] {μ : MeasureTheor
y.Measure α}   {ν : MeasureTheory.M…
· 使用定理 `MeasureTheory.NullMeasurableSet.prod`：∀ {α : Type u_1} {β : Type u_2} [i
nst : MeasurableSpace α] [inst_1 : MeasurableSpace β] {μ : MeasureTheory.Measure
 α}   {ν : MeasureTheory.M…

--- 原说明 ---
The product of two non-null sets is null measurable
if and only if both of them are null measurable.
-/
lemma nullMeasurableSet_prod_of_ne_zero {s : Set α} {t : Set β} (hs : μ s ≠ 0) (ht : ν t ≠ 0) :
    NullMeasurableSet (s ×ˢ t) (μ.prod ν) ↔ NullMeasurableSet s μ ∧ NullMeasurableSet t ν :=
  ⟨fun h ↦ ⟨h.left_of_prod ht, h.right_of_prod hs⟩, fun ⟨hs, ht⟩ ↦ hs.prod ht⟩

/-- The product of two sets is null measurable
if and only if both of them are null measurable or one of them has measure zero. -/
/-
**MeasureTheory.Measure.nullMeasurableSet_prod** 是 Mathlib 中的一个引理，位于命名空间 `Measur
eTheory.Measure`。
形式化陈述：nullMeasurableSet_prod {s : Set α} {t : Set β} : NullMeasurableSet (s ×ˢ t
) (μ.prod ν) ↔ NullMeasurableSet s μ ∧ NullMeasurableSet t ν ∨ μ s = 0 ∨ ν t = 0
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `MeasureTheory.Measure.prod_prod`：prod_prod (s : Set α) (t : Set β) : μ.p
rod ν (s ×ˢ t) = μ s * ν t
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `true_or`：∀ (p : Prop), (True ∨ p) = True
· 使用定理 `or_true`：∀ (p : Prop), (p ∨ True) = True
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `and_true`：∀ (p : Prop), (p ∧ True) = p
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `or_self`：∀ (p : Prop), (p ∨ p) = p
· 使用定理 `or_false`：∀ (p : Prop), (p ∨ False) = p

--- 原说明 ---
The product of two sets is null measurable
if and only if both of them are null measurable or one of them has measure zero.
-/
lemma nullMeasurableSet_prod {s : Set α} {t : Set β} :
    NullMeasurableSet (s ×ˢ t) (μ.prod ν) ↔
      NullMeasurableSet s μ ∧ NullMeasurableSet t ν ∨ μ s = 0 ∨ ν t = 0 := by
  rcases eq_or_ne (μ s) 0 with hs | hs; · simp [NullMeasurableSet.of_null, *]
  rcases eq_or_ne (ν t) 0 with ht | ht; · simp [NullMeasurableSet.of_null, *]
  simp [*, nullMeasurableSet_prod_of_ne_zero]
/-
**MeasureTheory.Measure.prodAssoc_prod** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.
Measure`。
形式化陈述：prodAssoc_prod [SFinite τ] : map MeasurableEquiv.prodAssoc ((μ.prod ν).pro
d τ) = μ.prod (ν.prod τ)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.ext`：ext (h : forall s, MeasurableSet s -> μ₁ s = 
μ₂ s) : μ₁ = μ₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.Measure.sum_apply`：sum_apply (f : ι -> Measure α) {s : Set
 α} (hs : MeasurableSet s) : sum f s = ∑' i, f i s
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Equiv.tsum_eq`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} [inst : Ad
dCommMonoid α] [inst_1 : TopologicalSpace α] (e : γ ≃ β)   (f : β → α), ∑' (c : 
γ),…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `MeasureTheory.sfiniteSeq.congr_simp`：∀ {α : Type u_1} {m0 : MeasurableSp
ace α} (μ μ_1 : MeasureTheory.Measure α) (e_μ : μ = μ_1)   [h : MeasureTheory.SF
inite μ] (a a_1 : ℕ), a =…
· 使用定理 `Equiv.prodAssoc_apply`：∀ (α : Type u_9) (β : Type u_10) (γ : Type u_11) 
(p : (α × β) × γ), (Equiv.prodAssoc α β γ) p = (p.1.1, p.1.2, p.2)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用引理 `MeasureTheory.sum_sfiniteSeq`：sum_sfiniteSeq (μ : Measure α) [h : SFinit
e μ] : sum (sfiniteSeq μ) = μ
· 使用引理 `MeasureTheory.Measure.prod_sum`：prod_sum {ι ι' : Type*} [Countable ι'] (
m : ι -> Measure α) (m' : ι' -> Measure β) [forall n, SFinite (m' n)] : (Measure
.sum m).prod (Measur…
· 使用定理 `instCountableNat`：Countable ℕ
· 使用定理 `MeasureTheory.instSFiniteOfSigmaFinite`：∀ {α : Type u_1} {m0 : Measurabl
eSpace α} {μ : MeasureTheory.Measure α} [MeasureTheory.SigmaFinite μ],   Measure
Theory.SFinite μ
· 使用定理 `MeasureTheory.IsFiniteMeasure.toSigmaFinite`：∀ {α : Type u_1} {_m0 : Mea
surableSpace α} (μ : MeasureTheory.Measure α) [MeasureTheory.IsFiniteMeasure μ],
   MeasureTheory.SigmaFinite μ
· 使用引理 `MeasureTheory.Measure.map_sum`：map_sum {ι : Type*} {m : ι -> Measure α} 
{f : α -> β} (hf : AEMeasurable f (Measure.sum m)) : Measure.map f (Measure.sum 
m) = Measure.sum (f…
· 使用定理 `Measurable.aemeasurable`：Measurable.aemeasurable (h : Measurable f) : AE
Measurable f μ
· 使用定理 `MeasurableEquiv.measurable`：∀ {α : Type u_1} {β : Type u_2} [inst : Meas
urableSpace α] [inst_1 : MeasurableSpace β] (e : α ≃ᵐ β), Measurable ⇑e
· 使用定理 `instCountableProd`：∀ {α : Type u} {β : Type v} [Countable α] [Countable 
β], Countable (α × β)
· 使用定理 `MeasureTheory.Measure.prod.instSFinite`：∀ {α : Type u_4} {β : Type u_5} 
{x : MeasurableSpace α} {μ : MeasureTheory.Measure α} [MeasureTheory.SFinite μ] 
  {x_1 : MeasurableSpace β} …
· 使用定理 `MeasureTheory.Measure.prod_eq_generateFrom`：prod_eq_generateFrom {μ : Me
asure α} {ν : Measure β} {C : Set (Set α)} {D : Set (Set β)} (hC : generateFrom 
C = ‹_›) (hD : generateFrom D = …
· 使用定理 `MeasurableSpace.generateFrom_measurableSet`：generateFrom_measurableSet [
MeasurableSpace α] : generateFrom {s : Set α | MeasurableSet s} = ‹_›
· 使用引理 `generateFrom_prod`：generateFrom_prod : generateFrom (image2 (· ×ˢ ·) { s
 : Set α | MeasurableSet s } { t : Set β | MeasurableSet t }) = Prod.instMeasura
bleSpac…
· 使用定理 `MeasurableSpace.isPiSystem_measurableSet`：isPiSystem_measurableSet {α : 
Type*} [MeasurableSpace α] : IsPiSystem { s : Set α | MeasurableSet s }
· 使用引理 `isPiSystem_prod`：isPiSystem_prod : IsPiSystem (image2 (· ×ˢ ·) { s : Set
 α | MeasurableSet s } { t : Set β | MeasurableSet t })
· 使用定理 `MeasureTheory.Measure.map_apply`：map_apply (hf : Measurable f) {s : Set 
β} (hs : MeasurableSet s) : μ.map f s = μ (f ⁻¹' s)
· 使用定理 `MeasurableSet.prod`：∀ {α : Type u_1} {β : Type u_2} {m : MeasurableSpace
 α} {mβ : MeasurableSpace β} {s : Set α} {t : Set β},   MeasurableSet s → Measur
ableSet …
（共 34 条，此处仅展示前 30 条）
-/
theorem prodAssoc_prod [SFinite τ] :
    map MeasurableEquiv.prodAssoc ((μ.prod ν).prod τ) = μ.prod (ν.prod τ) := by
  have : sum (fun (p : ℕ × ℕ × ℕ) ↦
        (sfiniteSeq μ p.1).prod ((sfiniteSeq ν p.2.1).prod (sfiniteSeq τ p.2.2)))
      = sum (fun (p : (ℕ × ℕ) × ℕ) ↦
        (sfiniteSeq μ p.1.1).prod ((sfiniteSeq ν p.1.2).prod (sfiniteSeq τ p.2))) := by
    ext s hs
    rw [sum_apply _ hs, sum_apply _ hs, ← (Equiv.prodAssoc _ _ _).tsum_eq]
    simp only [Equiv.prodAssoc_apply]
  rw [← sum_sfiniteSeq μ, ← sum_sfiniteSeq ν, ← sum_sfiniteSeq τ, prod_sum, prod_sum,
    map_sum MeasurableEquiv.prodAssoc.measurable.aemeasurable, prod_sum, prod_sum, this]
  congr
  ext1 i
  refine (prod_eq_generateFrom generateFrom_measurableSet generateFrom_prod
    isPiSystem_measurableSet isPiSystem_prod ((sfiniteSeq μ i.1.1)).toFiniteSpanningSetsIn
    ((sfiniteSeq ν i.1.2).toFiniteSpanningSetsIn.prod (sfiniteSeq τ i.2).toFiniteSpanningSetsIn)
      ?_).symm
  rintro s hs _ ⟨t, ht, u, hu, rfl⟩; rw [mem_ofPred_eq] at hs ht hu
  simp_rw [map_apply (MeasurableEquiv.measurable _) (hs.prod (ht.prod hu)),
    MeasurableEquiv.prodAssoc, MeasurableEquiv.coe_mk, Equiv.prod_assoc_preimage, prod_prod,
    mul_assoc]

/-! ### The product of specific measures -/

/-
**MeasureTheory.Measure.prod_restrict** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.M
easure`。
形式化陈述：prod_restrict (s : Set α) (t : Set β) : (μ.restrict s).prod (ν.restrict t)
 = (μ.prod ν).restrict (s ×ˢ t)
参数：s : Set α；t : Set β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `MeasureTheory.sum_sfiniteSeq`：sum_sfiniteSeq (μ : Measure α) [h : SFinit
e μ] : sum (sfiniteSeq μ) = μ
· 使用定理 `MeasureTheory.Measure.restrict_sum_of_countable`：restrict_sum_of_countab
le [Countable ι] (μ : ι -> Measure α) (s : Set α) : (sum μ).restrict s = sum fun
 i => (μ i).restrict s
· 使用定理 `instCountableNat`：Countable ℕ
· 使用引理 `MeasureTheory.Measure.prod_sum`：prod_sum {ι ι' : Type*} [Countable ι'] (
m : ι -> Measure α) (m' : ι' -> Measure β) [forall n, SFinite (m' n)] : (Measure
.sum m).prod (Measur…
· 使用定理 `MeasureTheory.instSFiniteRestrict`：∀ {α : Type u_1} {m0 : MeasurableSpac
e α} {μ : MeasureTheory.Measure α} [MeasureTheory.SFinite μ] (s : Set α),   Meas
ureTheory.SFinite (μ.re…
· 使用定理 `MeasureTheory.instSFiniteOfSigmaFinite`：∀ {α : Type u_1} {m0 : Measurabl
eSpace α} {μ : MeasureTheory.Measure α} [MeasureTheory.SigmaFinite μ],   Measure
Theory.SFinite μ
· 使用定理 `MeasureTheory.IsFiniteMeasure.toSigmaFinite`：∀ {α : Type u_1} {_m0 : Mea
surableSpace α} (μ : MeasureTheory.Measure α) [MeasureTheory.IsFiniteMeasure μ],
   MeasureTheory.SigmaFinite μ
· 使用定理 `instCountableProd`：∀ {α : Type u} {β : Type v} [Countable α] [Countable 
β], Countable (α × β)
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `MeasureTheory.Measure.prod_eq`：prod_eq {μ : Measure α} [SigmaFinite μ] {
ν : Measure β} [SigmaFinite ν] {μν : Measure (α × β)} (h : forall s t, Measurabl
eSet s -> Measurabl…
· 使用定理 `MeasureTheory.Restrict.sigmaFinite`：∀ {α : Type u_1} {m0 : MeasurableSpa
ce α} (μ : MeasureTheory.Measure α) [MeasureTheory.SigmaFinite μ] (s : Set α),  
 MeasureTheory.SigmaFini…
· 使用定理 `MeasureTheory.Measure.restrict_apply`：restrict_apply (ht : MeasurableSet
 t) : μ.restrict s t = μ (t inter s)
· 使用定理 `MeasurableSet.prod`：∀ {α : Type u_1} {β : Type u_2} {m : MeasurableSpace
 α} {mβ : MeasurableSpace β} {s : Set α} {t : Set β},   MeasurableSet s → Measur
ableSet …
· 使用定理 `Set.prod_inter_prod`：prod_inter_prod : s₁ ×ˢ t₁ inter s₂ ×ˢ t₂ = (s₁ int
er s₂) ×ˢ (t₁ inter t₂)
· 使用定理 `MeasureTheory.Measure.prod_prod`：prod_prod (s : Set α) (t : Set β) : μ.p
rod ν (s ×ˢ t) = μ s * ν t

--- 原说明 ---
### The product of specific measures
-/
theorem prod_restrict (s : Set α) (t : Set β) :
    (μ.restrict s).prod (ν.restrict t) = (μ.prod ν).restrict (s ×ˢ t) := by
  rw [← sum_sfiniteSeq μ, ← sum_sfiniteSeq ν, restrict_sum_of_countable, restrict_sum_of_countable,
    prod_sum, prod_sum, restrict_sum_of_countable]
  congr 1
  ext1 i
  refine prod_eq fun s' t' hs' ht' => ?_
  rw [restrict_apply (hs'.prod ht'), prod_inter_prod, prod_prod, restrict_apply hs',
    restrict_apply ht']
/-
**MeasureTheory.Measure.restrict_prod_eq_prod_univ** 是 Mathlib 中的一个定理，位于命名空间 `Me
asureTheory.Measure`。
形式化陈述：restrict_prod_eq_prod_univ (s : Set α) : (μ.restrict s).prod ν = (μ.prod ν
).restrict (s ×ˢ univ)
参数：s : Set α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.Measure.restrict_univ`：restrict_univ : μ.restrict univ = μ
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.Measure.prod_restrict`：prod_restrict (s : Set α) (t : Set 
β) : (μ.restrict s).prod (ν.restrict t) = (μ.prod ν).restrict (s ×ˢ t)
-/
theorem restrict_prod_eq_prod_univ (s : Set α) :
    (μ.restrict s).prod ν = (μ.prod ν).restrict (s ×ˢ univ) := by
  have : ν = ν.restrict Set.univ := Measure.restrict_univ.symm
  rw [this, Measure.prod_restrict, ← this]
/-
**MeasureTheory.Measure.prod_dirac** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.Meas
ure`。
形式化陈述：prod_dirac (y : β) : μ.prod (dirac y) = map (fun x => (x, y)) μ
参数：y : β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `MeasureTheory.sum_sfiniteSeq`：sum_sfiniteSeq (μ : Measure α) [h : SFinit
e μ] : sum (sfiniteSeq μ) = μ
· 使用引理 `MeasureTheory.Measure.prod_sum_left`：prod_sum_left {ι : Type*} (m : ι ->
 Measure α) (μ : Measure β) [SFinite μ] : (Measure.sum m).prod μ = Measure.sum (
fun i => (m i).prod μ)
· 使用定理 `MeasureTheory.instSFiniteOfSigmaFinite`：∀ {α : Type u_1} {m0 : Measurabl
eSpace α} {μ : MeasureTheory.Measure α} [MeasureTheory.SigmaFinite μ],   Measure
Theory.SFinite μ
· 使用定理 `MeasureTheory.Measure.dirac.instSigmaFinite`：∀ {α : Type u_1} [inst : Me
asurableSpace α] {a : α}, MeasureTheory.SigmaFinite (MeasureTheory.Measure.dirac
 a)
· 使用引理 `MeasureTheory.Measure.map_sum`：map_sum {ι : Type*} {m : ι -> Measure α} 
{f : α -> β} (hf : AEMeasurable f (Measure.sum m)) : Measure.map f (Measure.sum 
m) = Measure.sum (f…
· 使用定理 `Measurable.aemeasurable`：Measurable.aemeasurable (h : Measurable f) : AE
Measurable f μ
· 使用定理 `measurable_prodMk_right`：measurable_prodMk_right {y : β} : Measurable fu
n x : α => (x, y)
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `MeasureTheory.Measure.prod_eq`：prod_eq {μ : Measure α} [SigmaFinite μ] {
ν : Measure β} [SigmaFinite ν] {μν : Measure (α × β)} (h : forall s t, Measurabl
eSet s -> Measurabl…
· 使用定理 `MeasureTheory.IsFiniteMeasure.toSigmaFinite`：∀ {α : Type u_1} {_m0 : Mea
surableSpace α} (μ : MeasureTheory.Measure α) [MeasureTheory.IsFiniteMeasure μ],
   MeasureTheory.SigmaFinite μ
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `MeasureTheory.Measure.map_apply`：map_apply (hf : Measurable f) {s : Set 
β} (hs : MeasurableSet s) : μ.map f s = μ (f ⁻¹' s)
· 使用定理 `MeasurableSet.prod`：∀ {α : Type u_1} {β : Type u_2} {m : MeasurableSpace
 α} {mβ : MeasurableSpace β} {s : Set α} {t : Set β},   MeasurableSet s → Measur
ableSet …
· 使用定理 `Set.mk_preimage_prod_left_eq_if`：mk_preimage_prod_left_eq_if [DecidableP
red (· in t)] : (fun a => (a, b)) ⁻¹' s ×ˢ t = if b in t then s else ∅
· 使用定理 `MeasureTheory.measure_if`：measure_if {x : β} {t : Set β} {s : Set α} [De
cidable (x in t)] : μ (if x in t then s else ∅) = indicator t (fun _ => μ s) x
· 使用定理 `MeasureTheory.Measure.dirac_apply'`：dirac_apply' (a : α) (hs : Measurabl
eSet s) : dirac a s = s.indicator 1 a
· 使用引理 `Set.indicator_mul_right`：indicator_mul_right (s : Set ι) (f g : ι -> M₀)
 : indicator s (fun j => f j * g j) i = f i * indicator s g i
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem prod_dirac (y : β) : μ.prod (dirac y) = map (fun x => (x, y)) μ := by
  classical
  rw [← sum_sfiniteSeq μ, prod_sum_left, map_sum measurable_prodMk_right.aemeasurable]
  congr
  ext1 i
  refine prod_eq fun s t hs ht => ?_
  simp_rw [map_apply measurable_prodMk_right (hs.prod ht), mk_preimage_prod_left_eq_if, measure_if,
    dirac_apply' _ ht, ← indicator_mul_right _ fun _ => sfiniteSeq μ i s, Pi.one_apply, mul_one]
/-
**MeasureTheory.Measure.dirac_prod** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.Meas
ure`。
形式化陈述：dirac_prod (x : α) : (dirac x).prod ν = map (Prod.mk x) ν
参数：x : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `MeasureTheory.sum_sfiniteSeq`：sum_sfiniteSeq (μ : Measure α) [h : SFinit
e μ] : sum (sfiniteSeq μ) = μ
· 使用引理 `MeasureTheory.Measure.prod_sum_right`：prod_sum_right {ι' : Type*} [Count
able ι'] (m : Measure α) (m' : ι' -> Measure β) [forall n, SFinite (m' n)] : m.p
rod (Measure.sum m') = Mea…
· 使用定理 `instCountableNat`：Countable ℕ
· 使用定理 `MeasureTheory.instSFiniteOfSigmaFinite`：∀ {α : Type u_1} {m0 : Measurabl
eSpace α} {μ : MeasureTheory.Measure α} [MeasureTheory.SigmaFinite μ],   Measure
Theory.SFinite μ
· 使用定理 `MeasureTheory.IsFiniteMeasure.toSigmaFinite`：∀ {α : Type u_1} {_m0 : Mea
surableSpace α} (μ : MeasureTheory.Measure α) [MeasureTheory.IsFiniteMeasure μ],
   MeasureTheory.SigmaFinite μ
· 使用引理 `MeasureTheory.Measure.map_sum`：map_sum {ι : Type*} {m : ι -> Measure α} 
{f : α -> β} (hf : AEMeasurable f (Measure.sum m)) : Measure.map f (Measure.sum 
m) = Measure.sum (f…
· 使用定理 `Measurable.aemeasurable`：Measurable.aemeasurable (h : Measurable f) : AE
Measurable f μ
· 使用定理 `measurable_prodMk_left`：measurable_prodMk_left {x : α} : Measurable (@Pr
od.mk _ β x)
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `MeasureTheory.Measure.prod_eq`：prod_eq {μ : Measure α} [SigmaFinite μ] {
ν : Measure β} [SigmaFinite ν] {μν : Measure (α × β)} (h : forall s t, Measurabl
eSet s -> Measurabl…
· 使用定理 `MeasureTheory.Measure.dirac.instSigmaFinite`：∀ {α : Type u_1} [inst : Me
asurableSpace α] {a : α}, MeasureTheory.SigmaFinite (MeasureTheory.Measure.dirac
 a)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `MeasureTheory.Measure.map_apply`：map_apply (hf : Measurable f) {s : Set 
β} (hs : MeasurableSet s) : μ.map f s = μ (f ⁻¹' s)
· 使用定理 `MeasurableSet.prod`：∀ {α : Type u_1} {β : Type u_2} {m : MeasurableSpace
 α} {mβ : MeasurableSpace β} {s : Set α} {t : Set β},   MeasurableSet s → Measur
ableSet …
· 使用定理 `Set.mk_preimage_prod_right_eq_if`：mk_preimage_prod_right_eq_if [Decidabl
ePred (· in s)] : Prod.mk a ⁻¹' s ×ˢ t = if a in s then t else ∅
· 使用定理 `MeasureTheory.measure_if`：measure_if {x : β} {t : Set β} {s : Set α} [De
cidable (x in t)] : μ (if x in t then s else ∅) = indicator t (fun _ => μ s) x
· 使用定理 `MeasureTheory.Measure.dirac_apply'`：dirac_apply' (a : α) (hs : Measurabl
eSet s) : dirac a s = s.indicator 1 a
· 使用引理 `Set.indicator_mul_left`：indicator_mul_left (s : Set ι) (f g : ι -> M₀) :
 indicator s (fun j => f j * g j) i = indicator s f i * g i
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem dirac_prod (x : α) : (dirac x).prod ν = map (Prod.mk x) ν := by
  classical
  rw [← sum_sfiniteSeq ν, prod_sum_right, map_sum measurable_prodMk_left.aemeasurable]
  congr
  ext1 i
  refine prod_eq fun s t hs ht => ?_
  simp_rw [map_apply measurable_prodMk_left (hs.prod ht), mk_preimage_prod_right_eq_if, measure_if,
    dirac_apply' _ hs, ← indicator_mul_left _ _ fun _ => sfiniteSeq ν i t, Pi.one_apply, one_mul]
/-
**MeasureTheory.Measure.dirac_prod_dirac** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheor
y.Measure`。
形式化陈述：dirac_prod_dirac {x : α} {y : β} : (dirac x).prod (dirac y) = dirac (x, y)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.Measure.prod_dirac`：prod_dirac (y : β) : μ.prod (dirac y) 
= map (fun x => (x, y)) μ
· 使用定理 `MeasureTheory.instSFiniteOfSigmaFinite`：∀ {α : Type u_1} {m0 : Measurabl
eSpace α} {μ : MeasureTheory.Measure α} [MeasureTheory.SigmaFinite μ],   Measure
Theory.SFinite μ
· 使用定理 `MeasureTheory.Measure.dirac.instSigmaFinite`：∀ {α : Type u_1} [inst : Me
asurableSpace α] {a : α}, MeasureTheory.SigmaFinite (MeasureTheory.Measure.dirac
 a)
· 使用定理 `MeasureTheory.Measure.map_dirac'`：map_dirac' {f : α -> β} (hf : Measurab
le f) (a : α) : (dirac a).map f = dirac (f a)
· 使用定理 `measurable_prodMk_right`：measurable_prodMk_right {y : β} : Measurable fu
n x : α => (x, y)
-/
theorem dirac_prod_dirac {x : α} {y : β} : (dirac x).prod (dirac y) = dirac (x, y) := by
  rw [prod_dirac, map_dirac' measurable_prodMk_right]
/-
**MeasureTheory.Measure.prod_add** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.Measur
e`。
形式化陈述：prod_add (ν' : Measure β) [SFinite ν'] : μ.prod (ν + ν') = μ.prod ν + μ.pr
od ν'
参数：ν' : Measure β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `MeasureTheory.sum_sfiniteSeq`：sum_sfiniteSeq (μ : Measure α) [h : SFinit
e μ] : sum (sfiniteSeq μ) = μ
· 使用定理 `MeasureTheory.Measure.sum_add_sum`：sum_add_sum {ι : Type*} (μ ν : ι -> M
easure α) : sum μ + sum ν = sum fun n => μ n + ν n
· 使用引理 `MeasureTheory.Measure.prod_sum`：prod_sum {ι ι' : Type*} [Countable ι'] (
m : ι -> Measure α) (m' : ι' -> Measure β) [forall n, SFinite (m' n)] : (Measure
.sum m).prod (Measur…
· 使用定理 `instCountableNat`：Countable ℕ
· 使用定理 `MeasureTheory.instSFiniteHAddMeasure`：∀ {α : Type u_1} {m0 : MeasurableS
pace α} {μ ν : MeasureTheory.Measure α} [MeasureTheory.SFinite μ]   [MeasureTheo
ry.SFinite ν], MeasureTheo…
· 使用定理 `MeasureTheory.instSFiniteOfSigmaFinite`：∀ {α : Type u_1} {m0 : Measurabl
eSpace α} {μ : MeasureTheory.Measure α} [MeasureTheory.SigmaFinite μ],   Measure
Theory.SFinite μ
· 使用定理 `MeasureTheory.IsFiniteMeasure.toSigmaFinite`：∀ {α : Type u_1} {_m0 : Mea
surableSpace α} (μ : MeasureTheory.Measure α) [MeasureTheory.IsFiniteMeasure μ],
   MeasureTheory.SigmaFinite μ
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `MeasureTheory.Measure.prod_eq`：prod_eq {μ : Measure α} [SigmaFinite μ] {
ν : Measure β} [SigmaFinite ν] {μν : Measure (α × β)} (h : forall s t, Measurabl
eSet s -> Measurabl…
· 使用定理 `MeasureTheory.Add.sigmaFinite`：∀ {α : Type u_1} {m0 : MeasurableSpace α}
 (μ ν : MeasureTheory.Measure α) [MeasureTheory.SigmaFinite μ]   [MeasureTheory.
SigmaFinite ν], Mea…
· 使用定理 `MeasureTheory.Measure.prod_prod`：prod_prod (s : Set α) (t : Set β) : μ.p
rod ν (s ×ˢ t) = μ s * ν t
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `left_distrib`：left_distrib [Mul R] [Add R] [LeftDistribClass R] (a b c :
 R) : a * (b + c) = a * b + a * c
· 使用定理 `Distrib.leftDistribClass`：∀ (R : Type u_1) [inst : Distrib R], LeftDistr
ibClass R
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem prod_add (ν' : Measure β) [SFinite ν'] : μ.prod (ν + ν') = μ.prod ν + μ.prod ν' := by
  simp_rw [← sum_sfiniteSeq ν, ← sum_sfiniteSeq ν', sum_add_sum, ← sum_sfiniteSeq μ, prod_sum,
    sum_add_sum]
  congr
  ext1 i
  refine prod_eq fun s t _ _ => ?_
  simp_rw [add_apply, prod_prod, left_distrib]
/-
**MeasureTheory.Measure.add_prod** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.Measur
e`。
形式化陈述：add_prod (μ' : Measure α) [SFinite μ'] : (μ + μ').prod ν = μ.prod ν + μ'.p
rod ν
参数：μ' : Measure α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `MeasureTheory.sum_sfiniteSeq`：sum_sfiniteSeq (μ : Measure α) [h : SFinit
e μ] : sum (sfiniteSeq μ) = μ
· 使用定理 `MeasureTheory.Measure.sum_add_sum`：sum_add_sum {ι : Type*} (μ ν : ι -> M
easure α) : sum μ + sum ν = sum fun n => μ n + ν n
· 使用引理 `MeasureTheory.Measure.prod_sum`：prod_sum {ι ι' : Type*} [Countable ι'] (
m : ι -> Measure α) (m' : ι' -> Measure β) [forall n, SFinite (m' n)] : (Measure
.sum m).prod (Measur…
· 使用定理 `instCountableNat`：Countable ℕ
· 使用定理 `MeasureTheory.instSFiniteOfSigmaFinite`：∀ {α : Type u_1} {m0 : Measurabl
eSpace α} {μ : MeasureTheory.Measure α} [MeasureTheory.SigmaFinite μ],   Measure
Theory.SFinite μ
· 使用定理 `MeasureTheory.IsFiniteMeasure.toSigmaFinite`：∀ {α : Type u_1} {_m0 : Mea
surableSpace α} (μ : MeasureTheory.Measure α) [MeasureTheory.IsFiniteMeasure μ],
   MeasureTheory.SigmaFinite μ
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `MeasureTheory.Measure.prod_eq`：prod_eq {μ : Measure α} [SigmaFinite μ] {
ν : Measure β} [SigmaFinite ν] {μν : Measure (α × β)} (h : forall s t, Measurabl
eSet s -> Measurabl…
· 使用定理 `MeasureTheory.Add.sigmaFinite`：∀ {α : Type u_1} {m0 : MeasurableSpace α}
 (μ ν : MeasureTheory.Measure α) [MeasureTheory.SigmaFinite μ]   [MeasureTheory.
SigmaFinite ν], Mea…
· 使用定理 `MeasureTheory.Measure.prod_prod`：prod_prod (s : Set α) (t : Set β) : μ.p
rod ν (s ×ˢ t) = μ s * ν t
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `right_distrib`：right_distrib [Mul R] [Add R] [RightDistribClass R] (a b 
c : R) : (a + b) * c = a * c + b * c
· 使用定理 `Distrib.rightDistribClass`：∀ (R : Type u_1) [inst : Distrib R], RightDis
tribClass R
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem add_prod (μ' : Measure α) [SFinite μ'] : (μ + μ').prod ν = μ.prod ν + μ'.prod ν := by
  simp_rw [← sum_sfiniteSeq μ, ← sum_sfiniteSeq μ', sum_add_sum, ← sum_sfiniteSeq ν, prod_sum,
    sum_add_sum]
  congr
  ext1 i
  refine prod_eq fun s t _ _ => ?_
  simp_rw [add_apply, prod_prod, right_distrib]

@[simp]
/-
**MeasureTheory.Measure.zero_prod** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.Measu
re`。
形式化陈述：zero_prod (ν : Measure β) : (0 : Measure α).prod ν = 0
参数：ν : Measure β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.Measure.prod_def`：∀ {α : Type u_4} {β : Type u_5} [inst : 
MeasurableSpace α] [inst_1 : MeasurableSpace β] (μ : MeasureTheory.Measure α)   
(ν : MeasureTheory.M…
· 使用定理 `MeasureTheory.Measure.bind_zero_left`：bind_zero_left (f : α -> Measure β
) : bind (0 : Measure α) f = 0
-/
theorem zero_prod (ν : Measure β) : (0 : Measure α).prod ν = 0 := by
  rw [Measure.prod]
  exact bind_zero_left _

@[simp]
/-
**MeasureTheory.Measure.prod_zero** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.Measu
re`。
形式化陈述：prod_zero (μ : Measure α) : μ.prod (0 : Measure β) = 0
参数：μ : Measure α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.Measure.prod_def`：∀ {α : Type u_4} {β : Type u_5} [inst : 
MeasurableSpace α] [inst_1 : MeasurableSpace β] (μ : MeasureTheory.Measure α)   
(ν : MeasureTheory.M…
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `MeasureTheory.Measure.map_zero`：∀ {α : Type u_1} {β : Type u_2} {mα : Me
asurableSpace α} {mβ : MeasurableSpace β} (f : α → β),   MeasureTheory.Measure.m
ap f 0 = 0
· 使用引理 `MeasureTheory.Measure.bind_const`：bind_const {m : Measure α} {ν : Measur
e β} : m.bind (fun _ => ν) = m Set.univ • ν
· 使用定理 `smul_zero`：smul_zero (a : M) : a • (0 : A) = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem prod_zero (μ : Measure α) : μ.prod (0 : Measure β) = 0 := by simp [Measure.prod]
/-
**MeasureTheory.Measure.map_prod_map** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.Me
asure`。
形式化陈述：map_prod_map {δ} [MeasurableSpace δ] {f : α -> β} {g : γ -> δ} (μa : Measu
re α) (μc : Measure γ) [SFinite μa] [SFinite μc] (hf : Measurable f) (hg : Measu
rable g) : (map f μa).prod (map g μc) = map (Prod.map f g) (μa.prod μc)
参数：μa : Measure α；μc : Measure γ；hf : Measurable f；hg : Measurable g。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `MeasureTheory.sum_sfiniteSeq`：sum_sfiniteSeq (μ : Measure α) [h : SFinit
e μ] : sum (sfiniteSeq μ) = μ
· 使用引理 `MeasureTheory.Measure.map_sum`：map_sum {ι : Type*} {m : ι -> Measure α} 
{f : α -> β} (hf : AEMeasurable f (Measure.sum m)) : Measure.map f (Measure.sum 
m) = Measure.sum (f…
· 使用定理 `Measurable.aemeasurable`：Measurable.aemeasurable (h : Measurable f) : AE
Measurable f μ
· 使用引理 `MeasureTheory.Measure.prod_sum`：prod_sum {ι ι' : Type*} [Countable ι'] (
m : ι -> Measure α) (m' : ι' -> Measure β) [forall n, SFinite (m' n)] : (Measure
.sum m).prod (Measur…
· 使用定理 `instCountableNat`：Countable ℕ
· 使用定理 `MeasureTheory.Measure.instSFiniteMap`：∀ {α : Type u_2} {β : Type u_3} {m
0 : MeasurableSpace α} [inst : MeasurableSpace β] (μ : MeasureTheory.Measure α) 
  (f : α → β) [MeasureTheo…
· 使用定理 `MeasureTheory.instSFiniteOfSigmaFinite`：∀ {α : Type u_1} {m0 : Measurabl
eSpace α} {μ : MeasureTheory.Measure α} [MeasureTheory.SigmaFinite μ],   Measure
Theory.SFinite μ
· 使用定理 `MeasureTheory.IsFiniteMeasure.toSigmaFinite`：∀ {α : Type u_1} {_m0 : Mea
surableSpace α} (μ : MeasureTheory.Measure α) [MeasureTheory.IsFiniteMeasure μ],
   MeasureTheory.SigmaFinite μ
· 使用定理 `Measurable.prodMap`：Measurable.prodMap [MeasurableSpace δ] {f : α -> β} 
{g : γ -> δ} (hf : Measurable f) (hg : Measurable g) : Measurable (Prod.map f g)
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `MeasureTheory.Measure.prod_eq`：prod_eq {μ : Measure α} [SigmaFinite μ] {
ν : Measure β} [SigmaFinite ν] {μν : Measure (α × β)} (h : forall s t, Measurabl
eSet s -> Measurabl…
· 使用定理 `MeasureTheory.Measure.isFiniteMeasure_map`：∀ {α : Type u_1} {β : Type u_
2} [mβ : MeasurableSpace β] {m : MeasurableSpace α} (μ : MeasureTheory.Measure α
)   [MeasureTheory.IsFiniteMeas…
· 使用定理 `MeasureTheory.Measure.map_apply`：map_apply (hf : Measurable f) {s : Set 
β} (hs : MeasurableSet s) : μ.map f s = μ (f ⁻¹' s)
· 使用定理 `MeasurableSet.prod`：∀ {α : Type u_1} {β : Type u_2} {m : MeasurableSpace
 α} {mβ : MeasurableSpace β} {s : Set α} {t : Set β},   MeasurableSet s → Measur
ableSet …
· 使用定理 `MeasureTheory.Measure.prod_prod`：prod_prod (s : Set α) (t : Set β) : μ.p
rod ν (s ×ˢ t) = μ s * ν t
-/
theorem map_prod_map {δ} [MeasurableSpace δ] {f : α → β} {g : γ → δ} (μa : Measure α)
    (μc : Measure γ) [SFinite μa] [SFinite μc] (hf : Measurable f) (hg : Measurable g) :
    (map f μa).prod (map g μc) = map (Prod.map f g) (μa.prod μc) := by
  simp_rw [← sum_sfiniteSeq μa, ← sum_sfiniteSeq μc, map_sum hf.aemeasurable,
    map_sum hg.aemeasurable, prod_sum, map_sum (hf.prodMap hg).aemeasurable]
  congr
  ext1 i
  refine prod_eq fun s t hs ht => ?_
  rw [map_apply (hf.prodMap hg) (hs.prod ht), map_apply hf hs, map_apply hg ht]
  exact prod_prod (f ⁻¹' s) (g ⁻¹' t)

-- `prod_smul_right` needs an instance to get `SFinite (c • ν)` from `SFinite ν`,
-- hence it is placed in the `WithDensity` file, where the instance is defined.
/-
**MeasureTheory.Measure.prod_smul_left** 是 Mathlib 中的一个引理，位于命名空间 `MeasureTheory.
Measure`。
形式化陈述：prod_smul_left {μ : Measure α} {R : Type*} [SMul R Real>=0∞] [IsScalarTowe
r R Real>=0∞ Real>=0∞] (c : R) : (c • μ).prod ν = c • (μ.prod ν)
参数：c : R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.ext`：ext (h : forall s, MeasurableSet s -> μ₁ s = 
μ₂ s) : μ₁ = μ₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.Measure.prod_apply`：prod_apply {s : Set (α × β)} (hs : Mea
surableSet s) : μ.prod ν s = ∫⁻ x, ν (Prod.mk x ⁻¹' s) ∂μ
· 使用定理 `MeasureTheory.Measure.smul_apply`：smul_apply {_m : MeasurableSpace α} (c
 : R) (μ : Measure α) (s : Set α) : (c • μ) s = c • μ s
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `MeasureTheory.lintegral_smul_measure`：lintegral_smul_measure {R : Type*}
 [SMul R Real>=0∞] [IsScalarTower R Real>=0∞ Real>=0∞] (c : R) (f : α -> Real>=0
∞) : ∫⁻ a, f a ∂c • μ = c …
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma prod_smul_left {μ : Measure α} {R : Type*} [SMul R ℝ≥0∞] [IsScalarTower R ℝ≥0∞ ℝ≥0∞]
    (c : R) : (c • μ).prod ν = c • (μ.prod ν) := by
  ext s hs
  rw [prod_apply hs, Measure.smul_apply, prod_apply hs]
  simp

end Measure

open Measure

namespace MeasurePreserving

variable {δ : Type*} [MeasurableSpace δ] {μa : Measure α} {μb : Measure β} {μc : Measure γ}
  {μd : Measure δ}

/-- Let `f : α → β` be a measure-preserving map.
For a.e. all `a`, let `g a : γ → δ` be a measure-preserving map.
Also suppose that `g` is measurable as a function of two arguments.
Then the map `fun (a, c) ↦ (f a, g a c)` is a measure-preserving map
for the product measures on `α × γ` and `β × δ`.

Some authors call a map of the form `fun (a, c) ↦ (f a, g a c)` a *skew product* over `f`,
thus the choice of a name.
-/
/-
**MeasureTheory.MeasurePreserving.skew_product** 是 Mathlib 中的一个定理，位于命名空间 `Measur
eTheory.MeasurePreserving`。
形式化陈述：skew_product [SFinite μa] [SFinite μc] {f : α -> β} (hf : MeasurePreservin
g f μa μb) {g : α -> γ -> δ} (hgm : Measurable (uncurry g)) (hg : forallᵐ a ∂μa,
 map (g a) μc = μd) : MeasurePreserving (fun p : α × γ => (f p.1, g p.1 p.2)) (μ
a.prod μc) (μb.prod μd)
参数：hf : MeasurePreserving f μa μb；hgm : Measurable (uncurry g)；hg : forallᵐ a ∂μ
a, map (g a) μc = μd。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `Measurable.prodMk`：Measurable.prodMk {β γ} {_ : MeasurableSpace β} {_ : 
MeasurableSpace γ} {f : α -> β} {g : α -> γ} (hf : Measurable f) (hg : Measurabl
e g) : …
· 使用定理 `Measurable.comp`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {x : Mea
surableSpace α} {x_1 : MeasurableSpace β}   {x_2 : MeasurableSpace γ} {g : β → γ
} {f …
· 使用定理 `MeasureTheory.MeasurePreserving.measurable`：∀ {α : Type u_1} {β : Type u
_2} [inst : MeasurableSpace α] [inst_1 : MeasurableSpace β] {f : α → β}   {μa : 
autoParam (MeasureTheory.Measure…
· 使用定理 `measurable_fst`：measurable_fst {_ : MeasurableSpace α} {_ : MeasurableSp
ace β} : Measurable (Prod.fst : α × β -> α)
· 使用定理 `eq_zero_or_neZero`：eq_zero_or_neZero (a : R) : a = 0 ∨ NeZero a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.Measure.zero_prod`：zero_prod (ν : Measure β) : (0 : Measur
e α).prod ν = 0
· 使用定理 `MeasureTheory.Measure.map_zero`：∀ {α : Type u_1} {β : Type u_2} {mα : Me
asurableSpace α} {mβ : MeasurableSpace β} (f : α → β),   MeasureTheory.Measure.m
ap f 0 = 0
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.MeasurePreserving.map_eq`：∀ {α : Type u_1} {β : Type u_2} 
[inst : MeasurableSpace α] [inst_1 : MeasurableSpace β] {f : α → β}   {μa : auto
Param (MeasureTheory.Measure…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Filter.Eventually.exists`：∀ {α : Type u} {p : α → Prop} {f : Filter α} [
f.NeBot], (∀ᶠ (x : α) in f, p x) → ∃ x, p x
· 使用定理 `MeasureTheory.Measure.ae.neBot`：∀ {α : Type u_1} {m0 : MeasurableSpace α
} {μ : MeasureTheory.Measure α} [NeZero μ], (MeasureTheory.ae μ).NeBot
· 使用定理 `MeasureTheory.Measure.instSFiniteMap`：∀ {α : Type u_2} {β : Type u_3} {m
0 : MeasurableSpace α} [inst : MeasurableSpace β] (μ : MeasureTheory.Measure α) 
  (f : α → β) [MeasureTheo…
· 使用定理 `MeasureTheory.Measure.ext`：ext (h : forall s, MeasurableSet s -> μ₁ s = 
μ₂ s) : μ₁ = μ₂
· 使用定理 `MeasureTheory.Measure.map_apply`：map_apply (hf : Measurable f) {s : Set 
β} (hs : MeasurableSet s) : μ.map f s = μ (f ⁻¹' s)
· 使用定理 `MeasureTheory.Measure.prod_apply`：prod_apply {s : Set (α × β)} (hs : Mea
surableSet s) : μ.prod ν s = ∫⁻ x, ν (Prod.mk x ⁻¹' s) ∂μ
· 使用定理 `MeasureTheory.MeasurePreserving.lintegral_comp`：lintegral_comp {f : β ->
 Real>=0∞} (hf : Measurable f) : ∫⁻ a, f (g a) ∂μ = ∫⁻ b, f b ∂ν
· 使用定理 `measurable_measure_prodMk_left`：measurable_measure_prodMk_left [SFinite 
ν] {s : Set (α × β)} (hs : MeasurableSet s) : Measurable fun x => ν (Prod.mk x ⁻
¹' s)
· 使用定理 `MeasureTheory.lintegral_congr_ae`：lintegral_congr_ae {f g : α -> Real>=0
∞} (h : f =ᵐ[μ] g) : ∫⁻ a, f a ∂μ = ∫⁻ a, g a ∂μ
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `Measurable.of_uncurry_left`：Measurable.of_uncurry_left {f : α -> β -> γ}
 (hf : Measurable (uncurry f)) {x : α} : Measurable (f x)
· 使用定理 `measurable_prodMk_left`：measurable_prodMk_left {x : α} : Measurable (@Pr
od.mk _ β x)
· 使用定理 `Set.preimage_preimage`：preimage_preimage {g : β -> γ} {f : α -> β} {s : 
Set γ} : f ⁻¹' g ⁻¹' s = (fun x => g (f x)) ⁻¹' s

--- 原说明 ---
Let `f : α → β` be a measure-preserving map.
For a.e. all `a`, let `g a : γ → δ` be a measure-preserving map.
Also suppose that `g` is measurable as a function of two arguments.
Then the map `fun (a, c) ↦ (f a, g a c)` is a measure-preserving map
for the product measures on `α × γ` and `β × δ`.

Some authors call a map of the form `fun (a, c) ↦ (f a, g a c)` a *skew product*
 over `f`,
thus the choice of a name.
-/
theorem skew_product [SFinite μa] [SFinite μc] {f : α → β} (hf : MeasurePreserving f μa μb)
    {g : α → γ → δ} (hgm : Measurable (uncurry g)) (hg : ∀ᵐ a ∂μa, map (g a) μc = μd) :
    MeasurePreserving (fun p : α × γ => (f p.1, g p.1 p.2)) (μa.prod μc) (μb.prod μd) := by
  have : Measurable fun p : α × γ => (f p.1, g p.1 p.2) := (hf.1.comp measurable_fst).prodMk hgm
  use this
  /- if `μa = 0`, then the lemma is trivial, otherwise we can use `hg`
    to deduce `SFinite μd`. -/
  rcases eq_zero_or_neZero μa with rfl | _
  · simp [← hf.map_eq]
  have sf : SFinite μd := by
    obtain ⟨a, ha⟩ : ∃ a, map (g a) μc = μd := hg.exists
    rw [← ha]
    infer_instance
  -- Thus we can use the integral formula for the product measure, and compute things explicitly
  ext s hs
  rw [map_apply this hs, Measure.prod_apply (this hs), Measure.prod_apply hs,
    ← hf.lintegral_comp (measurable_measure_prodMk_left hs)]
  apply lintegral_congr_ae
  filter_upwards [hg] with a ha
  rw [← ha, map_apply hgm.of_uncurry_left (measurable_prodMk_left hs), preimage_preimage,
    preimage_preimage]

/-- If `f : α → β` sends the measure `μa` to `μb` and `g : γ → δ` sends the measure `μc` to `μd`,
then `Prod.map f g` sends `μa.prod μc` to `μb.prod μd`. -/
/-
**MeasureTheory.MeasurePreserving.prod** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.
MeasurePreserving`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} [inst : MeasurableSpace α] 
[inst_1 : MeasurableSpace β]   [inst_2 : MeasurableSpace γ] {δ : Type u_4} [inst
_3 : MeasurableSpace δ] {μa : MeasureTheory.Measure α}   {μb : MeasureTheory.Mea
sure β} {μc : MeasureTheory.Measure γ} {μd : MeasureTheory.Measure δ}   [Measure
Theory.SFinite μa] [MeasureTheory.SFinite μc] {f : α → β} {g : γ → δ},   Measure
Theory.MeasurePreserving f μa μb →     MeasureTheory.MeasurePreserving g μc μd →
 MeasureTheory.MeasurePreserving (Prod.map f g) (μa.prod μc) (μb.prod μd)
参数：Prod.map f g；μa.prod μc；μb.prod μd。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Measurable.comp`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {x : Mea
surableSpace α} {x_1 : MeasurableSpace β}   {x_2 : MeasurableSpace γ} {g : β → γ
} {f …
· 使用定理 `MeasureTheory.MeasurePreserving.measurable`：∀ {α : Type u_1} {β : Type u
_2} [inst : MeasurableSpace α] [inst_1 : MeasurableSpace β] {f : α → β}   {μa : 
autoParam (MeasureTheory.Measure…
· 使用定理 `measurable_snd`：measurable_snd {_ : MeasurableSpace α} {_ : MeasurableSp
ace β} : Measurable (Prod.snd : α × β -> β)
· 使用定理 `MeasureTheory.MeasurePreserving.skew_product`：skew_product [SFinite μa] 
[SFinite μc] {f : α -> β} (hf : MeasurePreserving f μa μb) {g : α -> γ -> δ} (hg
m : Measurable (uncurry g)) (hg : …
· 使用定理 `MeasureTheory.ae_of_all`：ae_of_all {p : α -> Prop} (μ : F) : (forall a, 
p a) -> forallᵐ a ∂μ, p a
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `MeasureTheory.MeasurePreserving.map_eq`：∀ {α : Type u_1} {β : Type u_2} 
[inst : MeasurableSpace α] [inst_1 : MeasurableSpace β] {f : α → β}   {μa : auto
Param (MeasureTheory.Measure…

--- 原说明 ---
If `f : α → β` sends the measure `μa` to `μb` and `g : γ → δ` sends the measure 
`μc` to `μd`,
then `Prod.map f g` sends `μa.prod μc` to `μb.prod μd`.
-/
protected theorem prod [SFinite μa] [SFinite μc] {f : α → β} {g : γ → δ}
    (hf : MeasurePreserving f μa μb) (hg : MeasurePreserving g μc μd) :
    MeasurePreserving (Prod.map f g) (μa.prod μc) (μb.prod μd) :=
  have : Measurable (uncurry fun _ : α => g) := hg.1.comp measurable_snd
  hf.skew_product this <| ae_of_all _ fun _ => hg.map_eq

end MeasurePreserving

namespace QuasiMeasurePreserving

/-
**MeasureTheory.QuasiMeasurePreserving.prod_of_right** 是 Mathlib 中的一个定理，位于命名空间 `
MeasureTheory.QuasiMeasurePreserving`。
形式化陈述：prod_of_right {f : α × β -> γ} {μ : Measure α} {ν : Measure β} {τ : Measur
e γ} (hf : Measurable f) [SFinite ν] (h2f : forallᵐ x ∂μ, QuasiMeasurePreserving
 (fun y => f (x, y)) ν τ) : QuasiMeasurePreserving f (μ.prod ν) τ
参数：hf : Measurable f；h2f : forallᵐ x ∂μ, QuasiMeasurePreserving (fun y => f (x, 
y)) ν τ。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `MeasureTheory.Measure.AbsolutelyContinuous.mk`：mk (h : forall ⦃s : Set α
⦄, MeasurableSet s -> ν s = 0 -> μ s = 0) : μ ≪ ν
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.Measure.map_apply`：map_apply (hf : Measurable f) {s : Set 
β} (hs : MeasurableSet s) : μ.map f s = μ (f ⁻¹' s)
· 使用定理 `MeasureTheory.Measure.prod_apply`：prod_apply {s : Set (α × β)} (hs : Mea
surableSet s) : μ.prod ν s = ∫⁻ x, ν (Prod.mk x ⁻¹' s) ∂μ
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Set.preimage_preimage`：preimage_preimage {g : β -> γ} {f : α -> β} {s : 
Set γ} : f ⁻¹' g ⁻¹' s = (fun x => g (f x)) ⁻¹' s
· 使用定理 `MeasureTheory.lintegral_congr_ae`：lintegral_congr_ae {f g : α -> Real>=0
∞} (h : f =ᵐ[μ] g) : ∫⁻ a, f a ∂μ = ∫⁻ a, g a ∂μ
· 使用定理 `Filter.Eventually.mono`：∀ {α : Type u} {p q : α → Prop} {f : Filter α}, 
(∀ᶠ (x : α) in f, p x) → (∀ (x : α), p x → q x) → ∀ᶠ (x : α) in f, q x
· 使用定理 `MeasureTheory.Measure.QuasiMeasurePreserving.preimage_null`：preimage_nul
l (h : QuasiMeasurePreserving f μa μb) {s : Set β} (hs : μb s = 0) : μa (f ⁻¹' s
) = 0
· 使用定理 `MeasureTheory.lintegral_zero`：lintegral_zero : ∫⁻ _ : α, 0 ∂μ = 0
-/
theorem prod_of_right {f : α × β → γ} {μ : Measure α} {ν : Measure β} {τ : Measure γ}
    (hf : Measurable f) [SFinite ν]
    (h2f : ∀ᵐ x ∂μ, QuasiMeasurePreserving (fun y => f (x, y)) ν τ) :
    QuasiMeasurePreserving f (μ.prod ν) τ := by
  refine ⟨hf, ?_⟩
  refine AbsolutelyContinuous.mk fun s hs h2s => ?_
  rw [map_apply hf hs, Measure.prod_apply (hf hs)]; simp_rw [preimage_preimage]
  rw [lintegral_congr_ae (h2f.mono fun x hx => hx.preimage_null h2s), lintegral_zero]
/-
**MeasureTheory.QuasiMeasurePreserving.prod_of_left** 是 Mathlib 中的一个定理，位于命名空间 `M
easureTheory.QuasiMeasurePreserving`。
形式化陈述：prod_of_left {α β γ} [MeasurableSpace α] [MeasurableSpace β] [MeasurableSp
ace γ] {f : α × β -> γ} {μ : Measure α} {ν : Measure β} {τ : Measure γ} (hf : Me
asurable f) [SFinite μ] [SFinite ν] (h2f : forallᵐ y ∂ν, QuasiMeasurePreserving 
(fun x => f (x, y)) μ τ) : QuasiMeasurePreserving f (μ.prod ν) τ
参数：hf : Measurable f；h2f : forallᵐ y ∂ν, QuasiMeasurePreserving (fun x => f (x, 
y)) μ τ。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.Measure.prod_swap`：prod_swap : map Prod.swap (μ.prod ν) = 
ν.prod μ
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `MeasureTheory.Measure.QuasiMeasurePreserving.comp`：∀ {α : Type u_1} {β :
 Type u_2} {γ : Type u_3} {mα : MeasurableSpace α} {mβ : MeasurableSpace β}   {m
γ : MeasurableSpace γ} {μa : MeasureThe…
· 使用定理 `MeasureTheory.QuasiMeasurePreserving.prod_of_right`：prod_of_right {f : α
 × β -> γ} {μ : Measure α} {ν : Measure β} {τ : Measure γ} (hf : Measurable f) [
SFinite ν] (h2f : forallᵐ x ∂μ, QuasiMea…
· 使用定理 `Measurable.comp`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {x : Mea
surableSpace α} {x_1 : MeasurableSpace β}   {x_2 : MeasurableSpace γ} {g : β → γ
} {f …
· 使用定理 `measurable_swap`：measurable_swap : Measurable (Prod.swap : α × β -> β × 
α)
· 使用定理 `MeasureTheory.MeasurePreserving.quasiMeasurePreserving`：∀ {α : Type u_1}
 {β : Type u_2} [inst : MeasurableSpace α] [inst_1 : MeasurableSpace β] {μa : Me
asureTheory.Measure α}   {μb : MeasureTheory…
· 使用定理 `MeasureTheory.MeasurePreserving.symm`：symm (e : α ≃ᵐ β) {μa : Measure α}
 {μb : Measure β} (h : MeasurePreserving e μa μb) : MeasurePreserving e.symm μb 
μa
· 使用定理 `Measurable.measurePreserving`：∀ {α : Type u_1} {β : Type u_2} [inst : Me
asurableSpace α] [inst_1 : MeasurableSpace β] {f : α → β},   Measurable f → ∀ (μ
a : MeasureTheory.…
-/
theorem prod_of_left {α β γ} [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ]
    {f : α × β → γ} {μ : Measure α} {ν : Measure β} {τ : Measure γ} (hf : Measurable f)
    [SFinite μ] [SFinite ν]
    (h2f : ∀ᵐ y ∂ν, QuasiMeasurePreserving (fun x => f (x, y)) μ τ) :
    QuasiMeasurePreserving f (μ.prod ν) τ := by
  rw [← prod_swap]
  convert!
    (QuasiMeasurePreserving.prod_of_right (hf.comp measurable_swap) h2f).comp
      ((measurable_swap.measurePreserving (ν.prod μ)).symm
          MeasurableEquiv.prodComm).quasiMeasurePreserving

@[fun_prop]
/-
**MeasureTheory.QuasiMeasurePreserving.fst** 是 Mathlib 中的一个定理，位于命名空间 `MeasureThe
ory.QuasiMeasurePreserving`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} [inst : MeasurableSpace α] 
[inst_1 : MeasurableSpace β]   [inst_2 : MeasurableSpace γ] {μ : MeasureTheory.M
easure α} {ν : MeasureTheory.Measure β} {τ : MeasureTheory.Measure γ}   {f : α →
 β × γ},   MeasureTheory.Measure.QuasiMeasurePreserving f μ (ν.prod τ) →     Mea
sureTheory.Measure.QuasiMeasurePreserving (fun x => (f x).1) μ ν
参数：ν.prod τ；fun x => (f x).1。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.QuasiMeasurePreserving.comp`：∀ {α : Type u_1} {β :
 Type u_2} {γ : Type u_3} {mα : MeasurableSpace α} {mβ : MeasurableSpace β}   {m
γ : MeasurableSpace γ} {μa : MeasureThe…
· 使用定理 `MeasureTheory.Measure.quasiMeasurePreserving_fst`：quasiMeasurePreserving
_fst : QuasiMeasurePreserving Prod.fst (μ.prod ν) μ
-/
protected theorem fst {f : α → β × γ} (hf : QuasiMeasurePreserving f μ (ν.prod τ)) :
    QuasiMeasurePreserving (fun x ↦ (f x).1) μ ν :=
  (quasiMeasurePreserving_fst (μ := ν) (ν := τ)).comp hf

@[fun_prop]
/-
**MeasureTheory.QuasiMeasurePreserving.snd** 是 Mathlib 中的一个定理，位于命名空间 `MeasureThe
ory.QuasiMeasurePreserving`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} [inst : MeasurableSpace α] 
[inst_1 : MeasurableSpace β]   [inst_2 : MeasurableSpace γ] {μ : MeasureTheory.M
easure α} {ν : MeasureTheory.Measure β} {τ : MeasureTheory.Measure γ}   {f : α →
 β × γ},   MeasureTheory.Measure.QuasiMeasurePreserving f μ (ν.prod τ) →     Mea
sureTheory.Measure.QuasiMeasurePreserving (fun x => (f x).2) μ τ
参数：ν.prod τ；fun x => (f x).2。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.QuasiMeasurePreserving.comp`：∀ {α : Type u_1} {β :
 Type u_2} {γ : Type u_3} {mα : MeasurableSpace α} {mβ : MeasurableSpace β}   {m
γ : MeasurableSpace γ} {μa : MeasureThe…
· 使用定理 `MeasureTheory.Measure.quasiMeasurePreserving_snd`：quasiMeasurePreserving
_snd : QuasiMeasurePreserving Prod.snd (μ.prod ν) ν
-/
protected theorem snd {f : α → β × γ} (hf : QuasiMeasurePreserving f μ (ν.prod τ)) :
    QuasiMeasurePreserving (fun x ↦ (f x).2) μ τ :=
  (quasiMeasurePreserving_snd (μ := ν) (ν := τ)).comp hf

@[fun_prop]
/-
**MeasureTheory.QuasiMeasurePreserving.prodMap** 是 Mathlib 中的一个定理，位于命名空间 `Measur
eTheory.QuasiMeasurePreserving`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} [inst : MeasurableSpace α] 
[inst_1 : MeasurableSpace β]   [inst_2 : MeasurableSpace γ] {μ : MeasureTheory.M
easure α} {ν : MeasureTheory.Measure β} {τ : MeasureTheory.Measure γ}   {ω : Typ
e u_4} {mω : MeasurableSpace ω} {υ : MeasureTheory.Measure ω} [MeasureTheory.SFi
nite μ]   [MeasureTheory.SFinite τ] [MeasureTheory.SFinite υ] {f : α → β} {g : γ
 → ω},   MeasureTheory.Measure.QuasiMeasurePreserving f μ ν →     MeasureTheory.
Measure.QuasiMeasurePreserving g τ υ →       MeasureTheory.Measure.QuasiMeasureP
reserving (Prod.map f g) (μ.prod τ) (ν.prod υ)
参数：Prod.map f g；μ.prod τ；ν.prod υ。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Measurable.prodMap`：Measurable.prodMap [MeasurableSpace δ] {f : α -> β} 
{g : γ -> δ} (hf : Measurable f) (hg : Measurable g) : Measurable (Prod.map f g)
· 使用定理 `MeasureTheory.Measure.QuasiMeasurePreserving.measurable`：∀ {α : Type u_1
} {β : Type u_2} {mβ : MeasurableSpace β} {m0 : MeasurableSpace α} {f : α → β}  
 {μa : autoParam (MeasureTheory.Measure α) Me…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.Measure.map_prod_map`：map_prod_map {δ} [MeasurableSpace δ]
 {f : α -> β} {g : γ -> δ} (μa : Measure α) (μc : Measure γ) [SFinite μa] [SFini
te μc] (hf : Measurable …
· 使用定理 `MeasureTheory.Measure.AbsolutelyContinuous.prod`：∀ {α : Type u_1} {β : T
ype u_2} [inst : MeasurableSpace α] [inst_1 : MeasurableSpace β] {μ μ' : Measure
Theory.Measure α}   {ν ν' : MeasureTh…
· 使用定理 `MeasureTheory.Measure.QuasiMeasurePreserving.absolutelyContinuous`：∀ {α 
: Type u_1} {β : Type u_2} {mβ : MeasurableSpace β} {m0 : MeasurableSpace α} {f 
: α → β}   {μa : autoParam (MeasureTheory.Measure α) Me…
-/
protected theorem prodMap {ω : Type*} {mω : MeasurableSpace ω} {υ : Measure ω}
    [SFinite μ] [SFinite τ] [SFinite υ] {f : α → β} {g : γ → ω}
    (hf : QuasiMeasurePreserving f μ ν) (hg : QuasiMeasurePreserving g τ υ) :
    QuasiMeasurePreserving (Prod.map f g) (μ.prod τ) (ν.prod υ) := by
  refine ⟨by fun_prop, ?_⟩
  rw [← map_prod_map _ _ (by fun_prop) (by fun_prop)]
  exact hf.absolutelyContinuous.prod hg.absolutelyContinuous

end QuasiMeasurePreserving

end MeasureTheory

open MeasureTheory.Measure

section

/-
**AEMeasurable.prod_swap** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：AEMeasurable.prod_swap [SFinite μ] [SFinite ν] {f : β × α -> γ} (hf : AEMe
asurable f (ν.prod μ)) : AEMeasurable (fun z : α × β => f z.swap) (μ.prod ν)
参数：hf : AEMeasurable f (ν.prod μ)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AEMeasurable.comp_measurable`：comp_measurable {f : α -> δ} {g : δ -> β} 
(hg : AEMeasurable g (μ.map f)) (hf : Measurable f) : AEMeasurable (g ∘ f) μ
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.Measure.prod_swap`：prod_swap : map Prod.swap (μ.prod ν) = 
ν.prod μ
· 使用定理 `measurable_swap`：measurable_swap : Measurable (Prod.swap : α × β -> β × 
α)
-/
theorem AEMeasurable.prod_swap [SFinite μ] [SFinite ν] {f : β × α → γ}
    (hf : AEMeasurable f (ν.prod μ)) : AEMeasurable (fun z : α × β => f z.swap) (μ.prod ν) := by
  rw [← Measure.prod_swap] at hf
  exact hf.comp_measurable measurable_swap
/-
**MeasureTheory.NullMeasurable.comp_fst** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：MeasureTheory.NullMeasurable.comp_fst {f : α -> γ} (hf : NullMeasurable f 
μ) : NullMeasurable (fun z : α × β => f z.1) (μ.prod ν)
参数：hf : NullMeasurable f μ。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.NullMeasurable.comp_quasiMeasurePreserving`：∀ {α : Type u_
1} {β : Type u_2} {γ : Type u_3} {mα : MeasurableSpace α} {mβ : MeasurableSpace 
β}   {mγ : MeasurableSpace γ} {μ : MeasureTheo…
· 使用定理 `MeasureTheory.Measure.quasiMeasurePreserving_fst`：quasiMeasurePreserving
_fst : QuasiMeasurePreserving Prod.fst (μ.prod ν) μ
-/
theorem MeasureTheory.NullMeasurable.comp_fst {f : α → γ} (hf : NullMeasurable f μ) :
    NullMeasurable (fun z : α × β => f z.1) (μ.prod ν) :=
  hf.comp_quasiMeasurePreserving quasiMeasurePreserving_fst
/-
**AEMeasurable.comp_fst** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：AEMeasurable.comp_fst {f : α -> γ} (hf : AEMeasurable f μ) : AEMeasurable 
(fun z : α × β => f z.1) (μ.prod ν)
参数：hf : AEMeasurable f μ。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AEMeasurable.comp_quasiMeasurePreserving`：comp_quasiMeasurePreserving {ν
 : Measure δ} {f : α -> δ} {g : δ -> β} (hg : AEMeasurable g ν) (hf : QuasiMeasu
rePreserving f μ ν) : AEMeasur…
· 使用定理 `MeasureTheory.Measure.quasiMeasurePreserving_fst`：quasiMeasurePreserving
_fst : QuasiMeasurePreserving Prod.fst (μ.prod ν) μ
-/
theorem AEMeasurable.comp_fst {f : α → γ} (hf : AEMeasurable f μ) :
    AEMeasurable (fun z : α × β => f z.1) (μ.prod ν) :=
  hf.comp_quasiMeasurePreserving quasiMeasurePreserving_fst
/-
**MeasureTheory.NullMeasurable.comp_snd** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：MeasureTheory.NullMeasurable.comp_snd {f : β -> γ} (hf : NullMeasurable f 
ν) : NullMeasurable (fun z : α × β => f z.2) (μ.prod ν)
参数：hf : NullMeasurable f ν。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.NullMeasurable.comp_quasiMeasurePreserving`：∀ {α : Type u_
1} {β : Type u_2} {γ : Type u_3} {mα : MeasurableSpace α} {mβ : MeasurableSpace 
β}   {mγ : MeasurableSpace γ} {μ : MeasureTheo…
· 使用定理 `MeasureTheory.Measure.quasiMeasurePreserving_snd`：quasiMeasurePreserving
_snd : QuasiMeasurePreserving Prod.snd (μ.prod ν) ν
-/
theorem MeasureTheory.NullMeasurable.comp_snd {f : β → γ} (hf : NullMeasurable f ν) :
    NullMeasurable (fun z : α × β => f z.2) (μ.prod ν) :=
  hf.comp_quasiMeasurePreserving quasiMeasurePreserving_snd
/-
**AEMeasurable.comp_snd** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：AEMeasurable.comp_snd {f : β -> γ} (hf : AEMeasurable f ν) : AEMeasurable 
(fun z : α × β => f z.2) (μ.prod ν)
参数：hf : AEMeasurable f ν。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AEMeasurable.comp_quasiMeasurePreserving`：comp_quasiMeasurePreserving {ν
 : Measure δ} {f : α -> δ} {g : δ -> β} (hg : AEMeasurable g ν) (hf : QuasiMeasu
rePreserving f μ ν) : AEMeasur…
· 使用定理 `MeasureTheory.Measure.quasiMeasurePreserving_snd`：quasiMeasurePreserving
_snd : QuasiMeasurePreserving Prod.snd (μ.prod ν) ν
-/
theorem AEMeasurable.comp_snd {f : β → γ} (hf : AEMeasurable f ν) :
    AEMeasurable (fun z : α × β => f z.2) (μ.prod ν) :=
  hf.comp_quasiMeasurePreserving quasiMeasurePreserving_snd
/-
**AEMeasurable.lintegral_prod_right'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：AEMeasurable.lintegral_prod_right' [SFinite ν] {f : α × β -> Real>=0∞} (hf
 : AEMeasurable f (μ.prod ν)) : AEMeasurable (fun x => ∫⁻ y, f (x, y) ∂ν) μ
参数：hf : AEMeasurable f (μ.prod ν)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `Measurable.lintegral_prod_right`：Measurable.lintegral_prod_right [SFinit
e ν] {f : α -> β -> Real>=0∞} (hf : Measurable (uncurry f)) : Measurable fun x =
> ∫⁻ y, f x y ∂ν
· 使用定理 `Filter.Eventually.mono`：∀ {α : Type u} {p q : α → Prop} {f : Filter α}, 
(∀ᶠ (x : α) in f, p x) → (∀ (x : α), p x → q x) → ∀ᶠ (x : α) in f, q x
· 使用定理 `MeasureTheory.Measure.ae_ae_of_ae_prod`：ae_ae_of_ae_prod {p : α × β -> P
rop} (h : forallᵐ z ∂μ.prod ν, p z) : forallᵐ x ∂μ, forallᵐ y ∂ν, p (x, y)
· 使用定理 `MeasureTheory.lintegral_congr_ae`：lintegral_congr_ae {f g : α -> Real>=0
∞} (h : f =ᵐ[μ] g) : ∫⁻ a, f a ∂μ = ∫⁻ a, g a ∂μ
-/
theorem AEMeasurable.lintegral_prod_right' [SFinite ν] {f : α × β → ℝ≥0∞}
    (hf : AEMeasurable f (μ.prod ν)) : AEMeasurable (fun x ↦ ∫⁻ y, f (x, y) ∂ν) μ := by
  obtain ⟨g, hg, hfg⟩ := hf
  refine ⟨fun x ↦ ∫⁻ y, g (x, y) ∂ν, by fun_prop, ?_⟩
  exact (ae_ae_of_ae_prod hfg).mono fun x hfg' ↦ lintegral_congr_ae hfg'

@[fun_prop]
/-
**AEMeasurable.lintegral_prod_right** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：AEMeasurable.lintegral_prod_right [SFinite ν] {f : α -> β -> Real>=0∞} (hf
 : AEMeasurable f.uncurry (μ.prod ν)) : AEMeasurable (fun x => ∫⁻ y, f x y ∂ν) μ
参数：hf : AEMeasurable f.uncurry (μ.prod ν)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AEMeasurable.lintegral_prod_right'`：AEMeasurable.lintegral_prod_right' [
SFinite ν] {f : α × β -> Real>=0∞} (hf : AEMeasurable f (μ.prod ν)) : AEMeasurab
le (fun x => ∫⁻ y, f (x,…
-/
theorem AEMeasurable.lintegral_prod_right [SFinite ν] {f : α → β → ℝ≥0∞}
    (hf : AEMeasurable f.uncurry (μ.prod ν)) : AEMeasurable (fun x ↦ ∫⁻ y, f x y ∂ν) μ :=
  hf.lintegral_prod_right'
/-
**AEMeasurable.lintegral_prod_left'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：AEMeasurable.lintegral_prod_left' [SFinite ν] [SFinite μ] {f : α × β -> Re
al>=0∞} (hf : AEMeasurable f (μ.prod ν)) : AEMeasurable (fun y => ∫⁻ x, f (x, y)
 ∂μ) ν
参数：hf : AEMeasurable f (μ.prod ν)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AEMeasurable.lintegral_prod_right'`：AEMeasurable.lintegral_prod_right' [
SFinite ν] {f : α × β -> Real>=0∞} (hf : AEMeasurable f (μ.prod ν)) : AEMeasurab
le (fun x => ∫⁻ y, f (x,…
· 使用定理 `AEMeasurable.prod_swap`：AEMeasurable.prod_swap [SFinite μ] [SFinite ν] {
f : β × α -> γ} (hf : AEMeasurable f (ν.prod μ)) : AEMeasurable (fun z : α × β =
> f z.swap) …
-/
theorem AEMeasurable.lintegral_prod_left' [SFinite ν] [SFinite μ] {f : α × β → ℝ≥0∞}
    (hf : AEMeasurable f (μ.prod ν)) : AEMeasurable (fun y ↦ ∫⁻ x, f (x, y) ∂μ) ν :=
  hf.prod_swap.lintegral_prod_right'

@[fun_prop]
/-
**AEMeasurable.lintegral_prod_left** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：AEMeasurable.lintegral_prod_left [SFinite ν] [SFinite μ] {f : α -> β -> Re
al>=0∞} (hf : AEMeasurable f.uncurry (μ.prod ν)) : AEMeasurable (fun y => ∫⁻ x, 
f x y ∂μ) ν
参数：hf : AEMeasurable f.uncurry (μ.prod ν)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AEMeasurable.lintegral_prod_left'`：AEMeasurable.lintegral_prod_left' [SF
inite ν] [SFinite μ] {f : α × β -> Real>=0∞} (hf : AEMeasurable f (μ.prod ν)) : 
AEMeasurable (fun y => …
-/
theorem AEMeasurable.lintegral_prod_left [SFinite ν] [SFinite μ] {f : α → β → ℝ≥0∞}
    (hf : AEMeasurable f.uncurry (μ.prod ν)) : AEMeasurable (fun y ↦ ∫⁻ x, f x y ∂μ) ν :=
  hf.lintegral_prod_left'

end

namespace MeasureTheory

/-! ### The Lebesgue integral on a product -/

variable [SFinite ν]

/-
**MeasureTheory.lintegral_prod_swap** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：lintegral_prod_swap [SFinite μ] (f : α × β -> Real>=0∞) : ∫⁻ z, f z.swap ∂
ν.prod μ = ∫⁻ z, f z ∂μ.prod ν
参数：f : α × β -> Real>=0∞。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.MeasurePreserving.lintegral_comp_emb`：lintegral_comp_emb (
hge : MeasurableEmbedding g) (f : β -> Real>=0∞) : ∫⁻ a, f (g a) ∂μ = ∫⁻ b, f b 
∂ν
· 使用定理 `MeasureTheory.Measure.measurePreserving_swap`：measurePreserving_swap : M
easurePreserving Prod.swap (μ.prod ν) (ν.prod μ)
· 使用定理 `MeasurableEquiv.measurableEmbedding`：∀ {α : Type u_1} {β : Type u_2} [in
st : MeasurableSpace α] [inst_1 : MeasurableSpace β] (e : α ≃ᵐ β),   MeasurableE
mbedding ⇑e
-/
theorem lintegral_prod_swap [SFinite μ] (f : α × β → ℝ≥0∞) :
    ∫⁻ z, f z.swap ∂ν.prod μ = ∫⁻ z, f z ∂μ.prod ν :=
  measurePreserving_swap.lintegral_comp_emb MeasurableEquiv.prodComm.measurableEmbedding f

/-- **Tonelli's Theorem**: For `ℝ≥0∞`-valued almost everywhere measurable functions on `α × β`,
  the integral of `f` is equal to the iterated integral. -/
/-
**MeasureTheory.lintegral_prod** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：lintegral_prod (f : α × β -> Real>=0∞) (hf : AEMeasurable f (μ.prod ν)) : 
∫⁻ z, f z ∂μ.prod ν = ∫⁻ x, ∫⁻ y, f (x, y) ∂ν ∂μ
参数：f : α × β -> Real>=0∞；hf : AEMeasurable f (μ.prod ν)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.Measure.prod_def`：∀ {α : Type u_4} {β : Type u_5} [inst : 
MeasurableSpace α] [inst_1 : MeasurableSpace β] (μ : MeasureTheory.Measure α)   
(ν : MeasureTheory.M…
· 使用定理 `MeasureTheory.Measure.lintegral_bind`：lintegral_bind {m : Measure α} {μ 
: α -> Measure β} {f : β -> Real>=0∞} (hμ : AEMeasurable μ m) (hf : AEMeasurable
 f (bind m μ)) : ∫⁻ x, f x…
· 使用定理 `Measurable.aemeasurable`：Measurable.aemeasurable (h : Measurable f) : AE
Measurable f μ
· 使用定理 `Measurable.map_prodMk_left`：Measurable.map_prodMk_left [SFinite ν] : Mea
surable fun x : α => map (Prod.mk x) ν
· 使用定理 `MeasureTheory.lintegral_congr_ae`：lintegral_congr_ae {f g : α -> Real>=0
∞} (h : f =ᵐ[μ] g) : ∫⁻ a, f a ∂μ = ∫⁻ a, g a ∂μ
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `AEMeasurable.ae_of_bind`：∀ {α : Type u_1} {β : Type u_2} {mα : Measurabl
eSpace α} {mβ : MeasurableSpace β} {γ : Type u_3} {x : MeasurableSpace γ}   {m :
 MeasureTheor…
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `MeasureTheory.lintegral_map'`：lintegral_map' {f : β -> Real>=0∞} {g : α 
-> β} (hf : AEMeasurable f (Measure.map g μ)) (hg : AEMeasurable g μ) : ∫⁻ a, f 
a ∂Measure.map g μ…
· 使用定理 `AEMeasurable.prodMk`：prodMk {f : α -> β} {g : α -> γ} (hf : AEMeasurable
 f μ) (hg : AEMeasurable g μ) : AEMeasurable (fun x => (f x, g x)) μ
· 使用定理 `aemeasurable_const`：aemeasurable_const {b : β} : AEMeasurable (fun _a : 
α => b) μ
· 使用定理 `aemeasurable_id`：aemeasurable_id : AEMeasurable id μ

--- 原说明 ---
**Tonelli's Theorem**: For `ℝ≥0∞`-valued almost everywhere measurable functions 
on `α × β`,
  the integral of `f` is equal to the iterated integral.
-/
theorem lintegral_prod (f : α × β → ℝ≥0∞) (hf : AEMeasurable f (μ.prod ν)) :
    ∫⁻ z, f z ∂μ.prod ν = ∫⁻ x, ∫⁻ y, f (x, y) ∂ν ∂μ := by
  rw [Measure.prod] at *
  rw [lintegral_bind Measurable.map_prodMk_left.aemeasurable hf]
  apply lintegral_congr_ae
  filter_upwards [Measurable.map_prodMk_left.aemeasurable.ae_of_bind hf] with a ha
  exact lintegral_map' ha (by fun_prop)

omit [SFinite ν] in
/-
**MeasureTheory.lintegral_prod_le** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：lintegral_prod_le (f : α × β -> Real>=0∞) : ∫⁻ z, f z ∂μ.prod ν <= ∫⁻ x, ∫
⁻ y, f (x, y) ∂ν ∂μ
参数：f : α × β -> Real>=0∞。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.Measure.prod_def`：∀ {α : Type u_4} {β : Type u_5} [inst : 
MeasurableSpace α] [inst_1 : MeasurableSpace β] (μ : MeasureTheory.Measure α)   
(ν : MeasureTheory.M…
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `MeasureTheory.Measure.lintegral_bind_le`：lintegral_bind_le (f : β -> Rea
l>=0∞) (m : Measure α) (μ : α -> Measure β) : ∫⁻ x, f x ∂bind m μ <= ∫⁻ a, ∫⁻ x,
 f x ∂μ a ∂m
· 使用定理 `MeasureTheory.lintegral_mono`：lintegral_mono ⦃f g : α -> Real>=0∞⦄ (hfg 
: f <= g) : ∫⁻ a, f a ∂μ <= ∫⁻ a, g a ∂μ
· 使用定理 `MeasureTheory.lintegral_map_le`：lintegral_map_le (f : β -> Real>=0∞) (g 
: α -> β) : ∫⁻ a, f a ∂Measure.map g μ <= ∫⁻ a, f (g a) ∂μ
-/
theorem lintegral_prod_le (f : α × β → ℝ≥0∞) :
    ∫⁻ z, f z ∂μ.prod ν ≤ ∫⁻ x, ∫⁻ y, f (x, y) ∂ν ∂μ := by
  rw [Measure.prod]
  exact (lintegral_bind_le _ _ _).trans <| lintegral_mono fun a ↦ lintegral_map_le _ _

/-- **Tonelli's Theorem for set integrals**: For `ℝ≥0∞`-valued almost everywhere measurable
functions on `s ×ˢ t`, the integral of `f` on `s ×ˢ t` is equal to the iterated integral on `s`
and `t` respectively. -/
/-
**MeasureTheory.setLIntegral_prod** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：setLIntegral_prod [SFinite μ] {s : Set α} {t : Set β} (f : α × β -> Real>=
0∞) (hf : AEMeasurable f ((μ.prod ν).restrict (s ×ˢ t))) : ∫⁻ z in s ×ˢ t, f z ∂
μ.prod ν = ∫⁻ x in s, ∫⁻ y in t, f (x, y) ∂ν ∂μ
参数：f : α × β -> Real>=0∞；hf : AEMeasurable f ((μ.prod ν).restrict (s ×ˢ t))。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.Measure.prod_restrict`：prod_restrict (s : Set α) (t : Set 
β) : (μ.restrict s).prod (ν.restrict t) = (μ.prod ν).restrict (s ×ˢ t)
· 使用定理 `MeasureTheory.lintegral_prod`：lintegral_prod (f : α × β -> Real>=0∞) (hf
 : AEMeasurable f (μ.prod ν)) : ∫⁻ z, f z ∂μ.prod ν = ∫⁻ x, ∫⁻ y, f (x, y) ∂ν ∂μ
· 使用定理 `MeasureTheory.instSFiniteRestrict`：∀ {α : Type u_1} {m0 : MeasurableSpac
e α} {μ : MeasureTheory.Measure α} [MeasureTheory.SFinite μ] (s : Set α),   Meas
ureTheory.SFinite (μ.re…

--- 原说明 ---
**Tonelli's Theorem for set integrals**: For `ℝ≥0∞`-valued almost everywhere mea
surable
functions on `s ×ˢ t`, the integral of `f` on `s ×ˢ t` is equal to the iterated 
integral on `s`
and `t` respectively.
-/
theorem setLIntegral_prod [SFinite μ] {s : Set α} {t : Set β} (f : α × β → ℝ≥0∞)
    (hf : AEMeasurable f ((μ.prod ν).restrict (s ×ˢ t))) :
    ∫⁻ z in s ×ˢ t, f z ∂μ.prod ν = ∫⁻ x in s, ∫⁻ y in t, f (x, y) ∂ν ∂μ := by
  rw [← Measure.prod_restrict, lintegral_prod _ (by rwa [Measure.prod_restrict])]

/-- The symmetric version of Tonelli's Theorem: For `ℝ≥0∞`-valued almost everywhere measurable
functions on `α × β`, the integral of `f` is equal to the iterated integral, in reverse order. -/
/-
**MeasureTheory.lintegral_prod_symm** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：lintegral_prod_symm [SFinite μ] (f : α × β -> Real>=0∞) (hf : AEMeasurable
 f (μ.prod ν)) : ∫⁻ z, f z ∂μ.prod ν = ∫⁻ y, ∫⁻ x, f (x, y) ∂μ ∂ν
参数：f : α × β -> Real>=0∞；hf : AEMeasurable f (μ.prod ν)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.lintegral_prod_swap`：lintegral_prod_swap [SFinite μ] (f : 
α × β -> Real>=0∞) : ∫⁻ z, f z.swap ∂ν.prod μ = ∫⁻ z, f z ∂μ.prod ν
· 使用定理 `MeasureTheory.lintegral_prod`：lintegral_prod (f : α × β -> Real>=0∞) (hf
 : AEMeasurable f (μ.prod ν)) : ∫⁻ z, f z ∂μ.prod ν = ∫⁻ x, ∫⁻ y, f (x, y) ∂ν ∂μ
· 使用定理 `AEMeasurable.prod_swap`：AEMeasurable.prod_swap [SFinite μ] [SFinite ν] {
f : β × α -> γ} (hf : AEMeasurable f (ν.prod μ)) : AEMeasurable (fun z : α × β =
> f z.swap) …

--- 原说明 ---
The symmetric version of Tonelli's Theorem: For `ℝ≥0∞`-valued almost everywhere 
measurable
functions on `α × β`, the integral of `f` is equal to the iterated integral, in 
reverse order.
-/
theorem lintegral_prod_symm [SFinite μ] (f : α × β → ℝ≥0∞) (hf : AEMeasurable f (μ.prod ν)) :
    ∫⁻ z, f z ∂μ.prod ν = ∫⁻ y, ∫⁻ x, f (x, y) ∂μ ∂ν := by
  simp_rw [← lintegral_prod_swap f]
  exact lintegral_prod _ hf.prod_swap

/-- The symmetric version of Tonelli's Theorem: For `ℝ≥0∞`-valued measurable
functions on `α × β`, the integral of `f` is equal to the iterated integral, in reverse order. -/
/-
**MeasureTheory.lintegral_prod_symm'** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：lintegral_prod_symm' [SFinite μ] (f : α × β -> Real>=0∞) (hf : Measurable 
f) : ∫⁻ z, f z ∂μ.prod ν = ∫⁻ y, ∫⁻ x, f (x, y) ∂μ ∂ν
参数：f : α × β -> Real>=0∞；hf : Measurable f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.lintegral_prod_symm`：lintegral_prod_symm [SFinite μ] (f : 
α × β -> Real>=0∞) (hf : AEMeasurable f (μ.prod ν)) : ∫⁻ z, f z ∂μ.prod ν = ∫⁻ y
, ∫⁻ x, f (x, y) ∂μ ∂ν
· 使用定理 `Measurable.aemeasurable`：Measurable.aemeasurable (h : Measurable f) : AE
Measurable f μ

--- 原说明 ---
The symmetric version of Tonelli's Theorem: For `ℝ≥0∞`-valued measurable
functions on `α × β`, the integral of `f` is equal to the iterated integral, in 
reverse order.
-/
theorem lintegral_prod_symm' [SFinite μ] (f : α × β → ℝ≥0∞) (hf : Measurable f) :
    ∫⁻ z, f z ∂μ.prod ν = ∫⁻ y, ∫⁻ x, f (x, y) ∂μ ∂ν :=
  lintegral_prod_symm f hf.aemeasurable

/-- The symmetric version of Tonelli's Theorem for set integrals: For `ℝ≥0∞`-valued almost
everywhere measurable functions on `s ×ˢ t`, the integral of `f` on `s ×ˢ t` is equal to the
iterated integral on `t` and `s` respectively. -/
/-
**MeasureTheory.setLIntegral_prod_symm** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`
。
形式化陈述：setLIntegral_prod_symm [SFinite μ] {s : Set α} {t : Set β} (f : α × β -> R
eal>=0∞) (hf : AEMeasurable f ((μ.prod ν).restrict (s ×ˢ t))) : ∫⁻ z in s ×ˢ t, 
f z ∂μ.prod ν = ∫⁻ y in t, ∫⁻ x in s, f (x, y) ∂μ ∂ν
参数：f : α × β -> Real>=0∞；hf : AEMeasurable f ((μ.prod ν).restrict (s ×ˢ t))。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.Measure.prod_restrict`：prod_restrict (s : Set α) (t : Set 
β) : (μ.restrict s).prod (ν.restrict t) = (μ.prod ν).restrict (s ×ˢ t)
· 使用定理 `MeasureTheory.lintegral_prod_swap`：lintegral_prod_swap [SFinite μ] (f : 
α × β -> Real>=0∞) : ∫⁻ z, f z.swap ∂ν.prod μ = ∫⁻ z, f z ∂μ.prod ν
· 使用定理 `MeasureTheory.instSFiniteRestrict`：∀ {α : Type u_1} {m0 : MeasurableSpac
e α} {μ : MeasureTheory.Measure α} [MeasureTheory.SFinite μ] (s : Set α),   Meas
ureTheory.SFinite (μ.re…
· 使用定理 `MeasureTheory.setLIntegral_prod`：setLIntegral_prod [SFinite μ] {s : Set 
α} {t : Set β} (f : α × β -> Real>=0∞) (hf : AEMeasurable f ((μ.prod ν).restrict
 (s ×ˢ t))) : ∫⁻ z in…
· 使用定理 `AEMeasurable.comp_measurable`：comp_measurable {f : α -> δ} {g : δ -> β} 
(hg : AEMeasurable g (μ.map f)) (hf : Measurable f) : AEMeasurable (g ∘ f) μ
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `MeasureTheory.Measure.prod_swap`：prod_swap : map Prod.swap (μ.prod ν) = 
ν.prod μ
· 使用定理 `measurable_swap`：measurable_swap : Measurable (Prod.swap : α × β -> β × 
α)

--- 原说明 ---
The symmetric version of Tonelli's Theorem for set integrals: For `ℝ≥0∞`-valued 
almost
everywhere measurable functions on `s ×ˢ t`, the integral of `f` on `s ×ˢ t` is 
equal to the
iterated integral on `t` and `s` respectively.
-/
theorem setLIntegral_prod_symm [SFinite μ] {s : Set α} {t : Set β} (f : α × β → ℝ≥0∞)
    (hf : AEMeasurable f ((μ.prod ν).restrict (s ×ˢ t))) :
    ∫⁻ z in s ×ˢ t, f z ∂μ.prod ν = ∫⁻ y in t, ∫⁻ x in s, f (x, y) ∂μ ∂ν := by
  rw [← Measure.prod_restrict, ← lintegral_prod_swap, Measure.prod_restrict,
    setLIntegral_prod]
  · rfl
  · refine AEMeasurable.comp_measurable ?_ measurable_swap
    convert! hf
    rw [← Measure.prod_restrict, Measure.prod_swap, Measure.prod_restrict]

/-- The reversed version of **Tonelli's Theorem**. In this version `f` is in curried form, which
makes it easier for the elaborator to figure out `f` automatically. -/
/-
**MeasureTheory.lintegral_lintegral** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：lintegral_lintegral ⦃f : α -> β -> Real>=0∞⦄ (hf : AEMeasurable (uncurry f
) (μ.prod ν)) : ∫⁻ x, ∫⁻ y, f x y ∂ν ∂μ = ∫⁻ z, f z.1 z.2 ∂μ.prod ν
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.lintegral_prod`：lintegral_prod (f : α × β -> Real>=0∞) (hf
 : AEMeasurable f (μ.prod ν)) : ∫⁻ z, f z ∂μ.prod ν = ∫⁻ x, ∫⁻ y, f (x, y) ∂ν ∂μ

--- 原说明 ---
The reversed version of **Tonelli's Theorem**. In this version `f` is in curried
 form, which
makes it easier for the elaborator to figure out `f` automatically.
-/
theorem lintegral_lintegral ⦃f : α → β → ℝ≥0∞⦄ (hf : AEMeasurable (uncurry f) (μ.prod ν)) :
    ∫⁻ x, ∫⁻ y, f x y ∂ν ∂μ = ∫⁻ z, f z.1 z.2 ∂μ.prod ν :=
  (lintegral_prod _ hf).symm

/-- The reversed version of **Tonelli's Theorem** (symmetric version). In this version `f` is in
curried form, which makes it easier for the elaborator to figure out `f` automatically. -/
/-
**MeasureTheory.lintegral_lintegral_symm** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheor
y`。
形式化陈述：lintegral_lintegral_symm [SFinite μ] ⦃f : α -> β -> Real>=0∞⦄ (hf : AEMeas
urable (uncurry f) (μ.prod ν)) : ∫⁻ x, ∫⁻ y, f x y ∂ν ∂μ = ∫⁻ z, f z.2 z.1 ∂ν.pr
od μ
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.lintegral_prod_symm`：lintegral_prod_symm [SFinite μ] (f : 
α × β -> Real>=0∞) (hf : AEMeasurable f (μ.prod ν)) : ∫⁻ z, f z ∂μ.prod ν = ∫⁻ y
, ∫⁻ x, f (x, y) ∂μ ∂ν
· 使用定理 `AEMeasurable.prod_swap`：AEMeasurable.prod_swap [SFinite μ] [SFinite ν] {
f : β × α -> γ} (hf : AEMeasurable f (ν.prod μ)) : AEMeasurable (fun z : α × β =
> f z.swap) …

--- 原说明 ---
The reversed version of **Tonelli's Theorem** (symmetric version). In this versi
on `f` is in
curried form, which makes it easier for the elaborator to figure out `f` automat
ically.
-/
theorem lintegral_lintegral_symm [SFinite μ] ⦃f : α → β → ℝ≥0∞⦄
    (hf : AEMeasurable (uncurry f) (μ.prod ν)) :
    ∫⁻ x, ∫⁻ y, f x y ∂ν ∂μ = ∫⁻ z, f z.2 z.1 ∂ν.prod μ :=
  (lintegral_prod_symm _ hf.prod_swap).symm

/-- Change the order of Lebesgue integration. -/
/-
**MeasureTheory.lintegral_lintegral_swap** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheor
y`。
形式化陈述：lintegral_lintegral_swap [SFinite μ] ⦃f : α -> β -> Real>=0∞⦄ (hf : AEMeas
urable (uncurry f) (μ.prod ν)) : ∫⁻ x, ∫⁻ y, f x y ∂ν ∂μ = ∫⁻ y, ∫⁻ x, f x y ∂μ 
∂ν
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `MeasureTheory.lintegral_lintegral`：lintegral_lintegral ⦃f : α -> β -> Re
al>=0∞⦄ (hf : AEMeasurable (uncurry f) (μ.prod ν)) : ∫⁻ x, ∫⁻ y, f x y ∂ν ∂μ = ∫
⁻ z, f z.1 z.2 ∂μ.prod …
· 使用定理 `MeasureTheory.lintegral_prod_symm`：lintegral_prod_symm [SFinite μ] (f : 
α × β -> Real>=0∞) (hf : AEMeasurable f (μ.prod ν)) : ∫⁻ z, f z ∂μ.prod ν = ∫⁻ y
, ∫⁻ x, f (x, y) ∂μ ∂ν

--- 原说明 ---
Change the order of Lebesgue integration.
-/
theorem lintegral_lintegral_swap [SFinite μ] ⦃f : α → β → ℝ≥0∞⦄
    (hf : AEMeasurable (uncurry f) (μ.prod ν)) :
    ∫⁻ x, ∫⁻ y, f x y ∂ν ∂μ = ∫⁻ y, ∫⁻ x, f x y ∂μ ∂ν :=
  (lintegral_lintegral hf).trans (lintegral_prod_symm _ hf)
/-
**MeasureTheory.lintegral_prod_mul** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：lintegral_prod_mul {f : α -> Real>=0∞} {g : β -> Real>=0∞} (hf : AEMeasura
ble f μ) (hg : AEMeasurable g ν) : ∫⁻ z, f z.1 * g z.2 ∂μ.prod ν = (∫⁻ x, f x ∂μ
) * ∫⁻ y, g y ∂ν
参数：hf : AEMeasurable f μ；hg : AEMeasurable g ν。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.lintegral_prod`：lintegral_prod (f : α × β -> Real>=0∞) (hf
 : AEMeasurable f (μ.prod ν)) : ∫⁻ z, f z ∂μ.prod ν = ∫⁻ x, ∫⁻ y, f (x, y) ∂ν ∂μ
· 使用定理 `AEMeasurable.fun_mul`：∀ {M : Type u_2} {α : Type u_3} [inst : Measurable
Space M] [inst_1 : Mul M] {m : MeasurableSpace α} {f g : α → M}   {μ : MeasureTh
eory.Measu…
· 使用定理 `AEMeasurable.comp_quasiMeasurePreserving`：comp_quasiMeasurePreserving {ν
 : Measure δ} {f : α -> δ} {g : δ -> β} (hg : AEMeasurable g ν) (hf : QuasiMeasu
rePreserving f μ ν) : AEMeasur…
· 使用定理 `MeasureTheory.QuasiMeasurePreserving.fst`：∀ {α : Type u_1} {β : Type u_2
} {γ : Type u_3} [inst : MeasurableSpace α] [inst_1 : MeasurableSpace β]   [inst
_2 : MeasurableSpace γ] {μ : M…
· 使用定理 `MeasureTheory.Measure.QuasiMeasurePreserving.id`：∀ {α : Type u_1} {_m0 :
 MeasurableSpace α} (μ : MeasureTheory.Measure α),   MeasureTheory.Measure.Quasi
MeasurePreserving id μ μ
· 使用定理 `MeasureTheory.QuasiMeasurePreserving.snd`：∀ {α : Type u_1} {β : Type u_2
} {γ : Type u_3} [inst : MeasurableSpace α] [inst_1 : MeasurableSpace β]   [inst
_2 : MeasurableSpace γ] {μ : M…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `MeasureTheory.lintegral_lintegral_mul`：lintegral_lintegral_mul {β} [Meas
urableSpace β] {ν : Measure β} {f : α -> Real>=0∞} {g : β -> Real>=0∞} (hf : AEM
easurable f μ) (hg : AEMeas…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem lintegral_prod_mul {f : α → ℝ≥0∞} {g : β → ℝ≥0∞} (hf : AEMeasurable f μ)
    (hg : AEMeasurable g ν) : ∫⁻ z, f z.1 * g z.2 ∂μ.prod ν = (∫⁻ x, f x ∂μ) * ∫⁻ y, g y ∂ν := by
  rw [lintegral_prod _ (by fun_prop)]
  simp [lintegral_lintegral_mul hf hg]

/-! ### Marginals of a measure defined on a product -/


namespace Measure

variable {ρ : Measure (α × β)}

/-- Marginal measure on `α` obtained from a measure `ρ` on `α × β`, defined by `ρ.map Prod.fst`. -/
/-
**MeasureTheory.Measure.fst** 是 Mathlib 中的一个定义，位于命名空间 `MeasureTheory.Measure`。
形式化陈述：fst (ρ : Measure (α × β)) : Measure α
参数：ρ : Measure (α × β)。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Marginal measure on `α` obtained from a measure `ρ` on `α × β`, defined by `ρ.ma
p Prod.fst`.
-/
noncomputable def fst (ρ : Measure (α × β)) : Measure α :=
  ρ.map Prod.fst
/-
**MeasureTheory.Measure.fst_apply** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.Measu
re`。
形式化陈述：fst_apply {s : Set α} (hs : MeasurableSet s) : ρ.fst s = ρ (Prod.fst ⁻¹' s
)
参数：hs : MeasurableSet s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.Measure.fst.eq_1`：∀ {α : Type u_1} {β : Type u_2} [inst : 
MeasurableSpace α] [inst_1 : MeasurableSpace β]   (ρ : MeasureTheory.Measure (α 
× β)), ρ.fst = Measu…
· 使用定理 `MeasureTheory.Measure.map_apply`：map_apply (hf : Measurable f) {s : Set 
β} (hs : MeasurableSet s) : μ.map f s = μ (f ⁻¹' s)
· 使用定理 `measurable_fst`：measurable_fst {_ : MeasurableSpace α} {_ : MeasurableSp
ace β} : Measurable (Prod.fst : α × β -> α)
-/
theorem fst_apply {s : Set α} (hs : MeasurableSet s) : ρ.fst s = ρ (Prod.fst ⁻¹' s) := by
  rw [fst, Measure.map_apply measurable_fst hs]
/-
**MeasureTheory.Measure.fst_univ** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.Measur
e`。
形式化陈述：fst_univ : ρ.fst univ = ρ univ
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.Measure.fst_apply`：fst_apply {s : Set α} (hs : MeasurableS
et s) : ρ.fst s = ρ (Prod.fst ⁻¹' s)
· 使用定理 `MeasurableSet.univ`：∀ {α : Type u_1} {m : MeasurableSpace α}, Measurable
Set Set.univ
· 使用定理 `Set.preimage_univ`：preimage_univ : f ⁻¹' univ = univ
-/
theorem fst_univ : ρ.fst univ = ρ univ := by rw [fst_apply MeasurableSet.univ, preimage_univ]
/-
**MeasureTheory.Measure.fst_zero** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.Measur
e`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} [inst : MeasurableSpace α] [inst_1 : Measu
rableSpace β], MeasureTheory.Measure.fst 0 = 0
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.Measure.map_zero`：∀ {α : Type u_1} {β : Type u_2} {mα : Me
asurableSpace α} {mβ : MeasurableSpace β} (f : α → β),   MeasureTheory.Measure.m
ap f 0 = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
@[simp] theorem fst_zero : fst (0 : Measure (α × β)) = 0 := by simp [fst]
/-
**MeasureTheory.Measure.** 是 Mathlib 中的一个实例，位于命名空间 `MeasureTheory.Measure`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [SFinite ρ] : SFinite ρ.fst := by
  rw [fst]
  infer_instance
/-
**MeasureTheory.Measure.fst.instIsFiniteMeasure** 是 Mathlib 中的一个定理，位于命名空间 `Measu
reTheory.Measure.fst`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} [inst : MeasurableSpace α] [inst_1 : Measu
rableSpace β]   {ρ : MeasureTheory.Measure (α × β)} [MeasureTheory.IsFiniteMeasu
re ρ], MeasureTheory.IsFiniteMeasure ρ.fst
参数：α × β。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.Measure.fst.eq_1`：∀ {α : Type u_1} {β : Type u_2} [inst : 
MeasurableSpace α] [inst_1 : MeasurableSpace β]   (ρ : MeasureTheory.Measure (α 
× β)), ρ.fst = Measu…
· 使用定理 `MeasureTheory.Measure.isFiniteMeasure_map`：∀ {α : Type u_1} {β : Type u_
2} [mβ : MeasurableSpace β] {m : MeasurableSpace α} (μ : MeasureTheory.Measure α
)   [MeasureTheory.IsFiniteMeas…
-/
instance fst.instIsFiniteMeasure [IsFiniteMeasure ρ] : IsFiniteMeasure ρ.fst := by
  rw [fst]
  infer_instance
/-
**MeasureTheory.Measure.fst.instIsProbabilityMeasure** 是 Mathlib 中的一个定理，位于命名空间 `
MeasureTheory.Measure.fst`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} [inst : MeasurableSpace α] [inst_1 : Measu
rableSpace β]   {ρ : MeasureTheory.Measure (α × β)} [MeasureTheory.IsProbability
Measure ρ], MeasureTheory.IsProbabilityMeasure ρ.fst
参数：α × β。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.Measure.fst_univ`：fst_univ : ρ.fst univ = ρ univ
· 使用定理 `MeasureTheory.IsProbabilityMeasure.measure_univ`：∀ {α : Type u_1} {m0 : 
MeasurableSpace α} {μ : MeasureTheory.Measure α} [self : MeasureTheory.IsProbabi
lityMeasure μ],   μ Set.univ = 1
-/
instance fst.instIsProbabilityMeasure [IsProbabilityMeasure ρ] : IsProbabilityMeasure ρ.fst where
  measure_univ := by
    rw [fst_univ]
    exact measure_univ
/-
**MeasureTheory.Measure.fst.instIsZeroOrProbabilityMeasure** 是 Mathlib 中的一个定理，位于
命名空间 `MeasureTheory.Measure.fst`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} [inst : MeasurableSpace α] [inst_1 : Measu
rableSpace β]   {ρ : MeasureTheory.Measure (α × β)} [MeasureTheory.IsZeroOrProba
bilityMeasure ρ],   MeasureTheory.IsZeroOrProbabilityMeasure ρ.fst
参数：α × β。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `MeasureTheory.eq_zero_or_isProbabilityMeasure`：eq_zero_or_isProbabilityM
easure : μ = 0 ∨ IsProbabilityMeasure μ
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `MeasureTheory.Measure.fst_zero`：∀ {α : Type u_1} {β : Type u_2} [inst : 
MeasurableSpace α] [inst_1 : MeasurableSpace β], MeasureTheory.Measure.fst 0 = 0
· 使用定理 `MeasureTheory.instIsZeroOrProbabilityMeasureOfNatMeasure`：∀ {α : Type u_
1} {m0 : MeasurableSpace α}, MeasureTheory.IsZeroOrProbabilityMeasure 0
· 使用定理 `MeasureTheory.instIsZeroOrProbabilityMeasureOfIsProbabilityMeasure`：∀ {α
 : Type u_1} {m0 : MeasurableSpace α} (μ : MeasureTheory.Measure α) [MeasureTheo
ry.IsProbabilityMeasure μ],   MeasureTheory.IsZeroOrProb…
· 使用定理 `MeasureTheory.Measure.fst.instIsProbabilityMeasure`：∀ {α : Type u_1} {β 
: Type u_2} [inst : MeasurableSpace α] [inst_1 : MeasurableSpace β]   {ρ : Measu
reTheory.Measure (α × β)} [MeasureTheory…
-/
instance fst.instIsZeroOrProbabilityMeasure [IsZeroOrProbabilityMeasure ρ] :
    IsZeroOrProbabilityMeasure ρ.fst := by
  rcases eq_zero_or_isProbabilityMeasure ρ with h | h
  · simp only [h, fst_zero]
    infer_instance
  · infer_instance

@[simp]
/-
**MeasureTheory.Measure.fst_prod** 是 Mathlib 中的一个引理，位于命名空间 `MeasureTheory.Measur
e`。
形式化陈述：fst_prod [IsProbabilityMeasure ν] : (μ.prod ν).fst = μ
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.ext`：ext (h : forall s, MeasurableSet s -> μ₁ s = 
μ₂ s) : μ₁ = μ₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.Measure.fst_apply`：fst_apply {s : Set α} (hs : MeasurableS
et s) : ρ.fst s = ρ (Prod.fst ⁻¹' s)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.prod_univ`：prod_univ {s : Set α} : s ×ˢ (univ : Set β) = Prod.fst ⁻¹
' s
· 使用定理 `MeasureTheory.Measure.prod_prod`：prod_prod (s : Set α) (t : Set β) : μ.p
rod ν (s ×ˢ t) = μ s * ν t
· 使用定理 `MeasureTheory.IsProbabilityMeasure.measure_univ`：∀ {α : Type u_1} {m0 : 
MeasurableSpace α} {μ : MeasureTheory.Measure α} [self : MeasureTheory.IsProbabi
lityMeasure μ],   μ Set.univ = 1
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
-/
lemma fst_prod [IsProbabilityMeasure ν] : (μ.prod ν).fst = μ := by
  ext1 s hs
  rw [fst_apply hs, ← prod_univ, prod_prod, measure_univ, mul_one]
/-
**MeasureTheory.Measure.fst_map_prodMk** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.
Measure`。
形式化陈述：fst_map_prodMk {X : α -> β} {Y : α -> γ} {μ : Measure α} (hY : Measurable 
Y) : (μ.map fun a => (X a, Y a)).fst = μ.map X
参数：hY : Measurable Y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.fst_map_prodMk₀`：fst_map_prodMk₀ {X : α -> β} {Y :
 α -> γ} {μ : Measure α} (hY : AEMeasurable Y μ) : (μ.map fun a => (X a, Y a)).f
st = μ.map X
· 使用定理 `Measurable.aemeasurable`：Measurable.aemeasurable (h : Measurable f) : AE
Measurable f μ
-/
theorem fst_map_prodMk₀ {X : α → β} {Y : α → γ} {μ : Measure α}
    (hY : AEMeasurable Y μ) : (μ.map fun a => (X a, Y a)).fst = μ.map X := by
  by_cases hX : AEMeasurable X μ
  · ext1 s hs
    rw [Measure.fst_apply hs, Measure.map_apply_of_aemeasurable (hX.prodMk hY) (measurable_fst hs),
      Measure.map_apply_of_aemeasurable hX hs, ← prod_univ, mk_preimage_prod, preimage_univ,
      inter_univ]
  · have : ¬AEMeasurable (fun x ↦ (X x, Y x)) μ := by
      contrapose hX
      exact measurable_fst.comp_aemeasurable hX
    simp [map_of_not_aemeasurable, hX, this]
/-
**MeasureTheory.Measure.fst_map_prodMk** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.
Measure`。
形式化陈述：fst_map_prodMk {X : α -> β} {Y : α -> γ} {μ : Measure α} (hY : Measurable 
Y) : (μ.map fun a => (X a, Y a)).fst = μ.map X
参数：hY : Measurable Y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.fst_map_prodMk₀`：fst_map_prodMk₀ {X : α -> β} {Y :
 α -> γ} {μ : Measure α} (hY : AEMeasurable Y μ) : (μ.map fun a => (X a, Y a)).f
st = μ.map X
· 使用定理 `Measurable.aemeasurable`：Measurable.aemeasurable (h : Measurable f) : AE
Measurable f μ
-/
theorem fst_map_prodMk {X : α → β} {Y : α → γ} {μ : Measure α}
    (hY : Measurable Y) : (μ.map fun a => (X a, Y a)).fst = μ.map X :=
  fst_map_prodMk₀ hY.aemeasurable

@[simp]
/-
**MeasureTheory.Measure.fst_add** 是 Mathlib 中的一个引理，位于命名空间 `MeasureTheory.Measure
`。
形式化陈述：fst_add {μ ν : Measure (α × β)} : (μ + ν).fst = μ.fst + ν.fst
参数：α × β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.map_add`：∀ {α : Type u_1} {β : Type u_2} {mα : Mea
surableSpace α} {mβ : MeasurableSpace β} (μ ν : MeasureTheory.Measure α)   {f : 
α → β},   Measurabl…
· 使用定理 `measurable_fst`：measurable_fst {_ : MeasurableSpace α} {_ : MeasurableSp
ace β} : Measurable (Prod.fst : α × β -> α)
-/
lemma fst_add {μ ν : Measure (α × β)} : (μ + ν).fst = μ.fst + ν.fst :=
  Measure.map_add _ _ measurable_fst
/-
**MeasureTheory.Measure.fst_sum** 是 Mathlib 中的一个引理，位于命名空间 `MeasureTheory.Measure
`。
形式化陈述：fst_sum {ι : Type*} (μ : ι -> Measure (α × β)) : (sum μ).fst = sum (fun n 
=> (μ n).fst)
参数：μ : ι -> Measure (α × β)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `MeasureTheory.Measure.map_sum`：map_sum {ι : Type*} {m : ι -> Measure α} 
{f : α -> β} (hf : AEMeasurable f (Measure.sum m)) : Measure.map f (Measure.sum 
m) = Measure.sum (f…
· 使用定理 `Measurable.aemeasurable`：Measurable.aemeasurable (h : Measurable f) : AE
Measurable f μ
· 使用定理 `measurable_fst`：measurable_fst {_ : MeasurableSpace α} {_ : MeasurableSp
ace β} : Measurable (Prod.fst : α × β -> α)
-/
lemma fst_sum {ι : Type*} (μ : ι → Measure (α × β)) : (sum μ).fst = sum (fun n ↦ (μ n).fst) :=
  Measure.map_sum measurable_fst.aemeasurable

@[gcongr]
/-
**MeasureTheory.Measure.fst_mono** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.Measur
e`。
形式化陈述：fst_mono {μ : Measure (α × β)} (h : ρ <= μ) : ρ.fst <= μ.fst
参数：α × β；h : ρ <= μ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.map_mono`：map_mono {f : α -> β} (h : μ <= ν) (hf :
 Measurable f) : μ.map f <= ν.map f
· 使用定理 `measurable_fst`：measurable_fst {_ : MeasurableSpace α} {_ : MeasurableSp
ace β} : Measurable (Prod.fst : α × β -> α)
-/
theorem fst_mono {μ : Measure (α × β)} (h : ρ ≤ μ) : ρ.fst ≤ μ.fst := map_mono h measurable_fst

/-- Marginal measure on `β` obtained from a measure on `ρ` `α × β`, defined by `ρ.map Prod.snd`. -/
/-
**MeasureTheory.Measure.snd** 是 Mathlib 中的一个定义，位于命名空间 `MeasureTheory.Measure`。
形式化陈述：snd (ρ : Measure (α × β)) : Measure β
参数：ρ : Measure (α × β)。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Marginal measure on `β` obtained from a measure on `ρ` `α × β`, defined by `ρ.ma
p Prod.snd`.
-/
noncomputable def snd (ρ : Measure (α × β)) : Measure β :=
  ρ.map Prod.snd
/-
**MeasureTheory.Measure.snd_apply** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.Measu
re`。
形式化陈述：snd_apply {s : Set β} (hs : MeasurableSet s) : ρ.snd s = ρ (Prod.snd ⁻¹' s
)
参数：hs : MeasurableSet s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.Measure.snd.eq_1`：∀ {α : Type u_1} {β : Type u_2} [inst : 
MeasurableSpace α] [inst_1 : MeasurableSpace β]   (ρ : MeasureTheory.Measure (α 
× β)), ρ.snd = Measu…
· 使用定理 `MeasureTheory.Measure.map_apply`：map_apply (hf : Measurable f) {s : Set 
β} (hs : MeasurableSet s) : μ.map f s = μ (f ⁻¹' s)
· 使用定理 `measurable_snd`：measurable_snd {_ : MeasurableSpace α} {_ : MeasurableSp
ace β} : Measurable (Prod.snd : α × β -> β)
-/
theorem snd_apply {s : Set β} (hs : MeasurableSet s) : ρ.snd s = ρ (Prod.snd ⁻¹' s) := by
  rw [snd, Measure.map_apply measurable_snd hs]
/-
**MeasureTheory.Measure.snd_univ** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.Measur
e`。
形式化陈述：snd_univ : ρ.snd univ = ρ univ
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.Measure.snd_apply`：snd_apply {s : Set β} (hs : MeasurableS
et s) : ρ.snd s = ρ (Prod.snd ⁻¹' s)
· 使用定理 `MeasurableSet.univ`：∀ {α : Type u_1} {m : MeasurableSpace α}, Measurable
Set Set.univ
· 使用定理 `Set.preimage_univ`：preimage_univ : f ⁻¹' univ = univ
-/
theorem snd_univ : ρ.snd univ = ρ univ := by rw [snd_apply MeasurableSet.univ, preimage_univ]
/-
**MeasureTheory.Measure.snd_zero** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.Measur
e`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} [inst : MeasurableSpace α] [inst_1 : Measu
rableSpace β], MeasureTheory.Measure.snd 0 = 0
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.Measure.map_zero`：∀ {α : Type u_1} {β : Type u_2} {mα : Me
asurableSpace α} {mβ : MeasurableSpace β} (f : α → β),   MeasureTheory.Measure.m
ap f 0 = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
@[simp] theorem snd_zero : snd (0 : Measure (α × β)) = 0 := by simp [snd]
/-
**MeasureTheory.Measure.** 是 Mathlib 中的一个实例，位于命名空间 `MeasureTheory.Measure`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [SFinite ρ] : SFinite ρ.snd := by
  rw [snd]
  infer_instance
/-
**MeasureTheory.Measure.snd.instIsFiniteMeasure** 是 Mathlib 中的一个定理，位于命名空间 `Measu
reTheory.Measure.snd`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} [inst : MeasurableSpace α] [inst_1 : Measu
rableSpace β]   {ρ : MeasureTheory.Measure (α × β)} [MeasureTheory.IsFiniteMeasu
re ρ], MeasureTheory.IsFiniteMeasure ρ.snd
参数：α × β。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.Measure.snd.eq_1`：∀ {α : Type u_1} {β : Type u_2} [inst : 
MeasurableSpace α] [inst_1 : MeasurableSpace β]   (ρ : MeasureTheory.Measure (α 
× β)), ρ.snd = Measu…
· 使用定理 `MeasureTheory.Measure.isFiniteMeasure_map`：∀ {α : Type u_1} {β : Type u_
2} [mβ : MeasurableSpace β] {m : MeasurableSpace α} (μ : MeasureTheory.Measure α
)   [MeasureTheory.IsFiniteMeas…
-/
instance snd.instIsFiniteMeasure [IsFiniteMeasure ρ] : IsFiniteMeasure ρ.snd := by
  rw [snd]
  infer_instance
/-
**MeasureTheory.Measure.snd.instIsProbabilityMeasure** 是 Mathlib 中的一个定理，位于命名空间 `
MeasureTheory.Measure.snd`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} [inst : MeasurableSpace α] [inst_1 : Measu
rableSpace β]   {ρ : MeasureTheory.Measure (α × β)} [MeasureTheory.IsProbability
Measure ρ], MeasureTheory.IsProbabilityMeasure ρ.snd
参数：α × β。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.Measure.snd_univ`：snd_univ : ρ.snd univ = ρ univ
· 使用定理 `MeasureTheory.IsProbabilityMeasure.measure_univ`：∀ {α : Type u_1} {m0 : 
MeasurableSpace α} {μ : MeasureTheory.Measure α} [self : MeasureTheory.IsProbabi
lityMeasure μ],   μ Set.univ = 1
-/
instance snd.instIsProbabilityMeasure [IsProbabilityMeasure ρ] : IsProbabilityMeasure ρ.snd where
  measure_univ := by
    rw [snd_univ]
    exact measure_univ
/-
**MeasureTheory.Measure.snd.instIsZeroOrProbabilityMeasure** 是 Mathlib 中的一个定理，位于
命名空间 `MeasureTheory.Measure.snd`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} [inst : MeasurableSpace α] [inst_1 : Measu
rableSpace β]   {ρ : MeasureTheory.Measure (α × β)} [MeasureTheory.IsZeroOrProba
bilityMeasure ρ],   MeasureTheory.IsZeroOrProbabilityMeasure ρ.snd
参数：α × β。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `MeasureTheory.eq_zero_or_isProbabilityMeasure`：eq_zero_or_isProbabilityM
easure : μ = 0 ∨ IsProbabilityMeasure μ
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `MeasureTheory.Measure.snd_zero`：∀ {α : Type u_1} {β : Type u_2} [inst : 
MeasurableSpace α] [inst_1 : MeasurableSpace β], MeasureTheory.Measure.snd 0 = 0
· 使用定理 `MeasureTheory.instIsZeroOrProbabilityMeasureOfNatMeasure`：∀ {α : Type u_
1} {m0 : MeasurableSpace α}, MeasureTheory.IsZeroOrProbabilityMeasure 0
· 使用定理 `MeasureTheory.instIsZeroOrProbabilityMeasureOfIsProbabilityMeasure`：∀ {α
 : Type u_1} {m0 : MeasurableSpace α} (μ : MeasureTheory.Measure α) [MeasureTheo
ry.IsProbabilityMeasure μ],   MeasureTheory.IsZeroOrProb…
· 使用定理 `MeasureTheory.Measure.snd.instIsProbabilityMeasure`：∀ {α : Type u_1} {β 
: Type u_2} [inst : MeasurableSpace α] [inst_1 : MeasurableSpace β]   {ρ : Measu
reTheory.Measure (α × β)} [MeasureTheory…
-/
instance snd.instIsZeroOrProbabilityMeasure [IsZeroOrProbabilityMeasure ρ] :
    IsZeroOrProbabilityMeasure ρ.snd := by
  rcases eq_zero_or_isProbabilityMeasure ρ with h | h
  · simp only [h, snd_zero]
    infer_instance
  · infer_instance

@[simp]
/-
**MeasureTheory.Measure.snd_prod** 是 Mathlib 中的一个引理，位于命名空间 `MeasureTheory.Measur
e`。
形式化陈述：snd_prod [IsProbabilityMeasure μ] : (μ.prod ν).snd = ν
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.ext`：ext (h : forall s, MeasurableSet s -> μ₁ s = 
μ₂ s) : μ₁ = μ₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.Measure.snd_apply`：snd_apply {s : Set β} (hs : MeasurableS
et s) : ρ.snd s = ρ (Prod.snd ⁻¹' s)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.univ_prod`：univ_prod {t : Set β} : (univ : Set α) ×ˢ t = Prod.snd ⁻¹
' t
· 使用定理 `MeasureTheory.Measure.prod_prod`：prod_prod (s : Set α) (t : Set β) : μ.p
rod ν (s ×ˢ t) = μ s * ν t
· 使用定理 `MeasureTheory.IsProbabilityMeasure.measure_univ`：∀ {α : Type u_1} {m0 : 
MeasurableSpace α} {μ : MeasureTheory.Measure α} [self : MeasureTheory.IsProbabi
lityMeasure μ],   μ Set.univ = 1
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
-/
lemma snd_prod [IsProbabilityMeasure μ] : (μ.prod ν).snd = ν := by
  ext1 s hs
  rw [snd_apply hs, ← univ_prod, prod_prod, measure_univ, one_mul]
/-
**MeasureTheory.Measure.snd_map_prodMk** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.
Measure`。
形式化陈述：snd_map_prodMk {X : α -> β} {Y : α -> γ} {μ : Measure α} (hX : Measurable 
X) : (μ.map fun a => (X a, Y a)).snd = μ.map Y
参数：hX : Measurable X。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.snd_map_prodMk₀`：snd_map_prodMk₀ {X : α -> β} {Y :
 α -> γ} {μ : Measure α} (hX : AEMeasurable X μ) : (μ.map fun a => (X a, Y a)).s
nd = μ.map Y
· 使用定理 `Measurable.aemeasurable`：Measurable.aemeasurable (h : Measurable f) : AE
Measurable f μ
-/
theorem snd_map_prodMk₀ {X : α → β} {Y : α → γ} {μ : Measure α} (hX : AEMeasurable X μ) :
    (μ.map fun a => (X a, Y a)).snd = μ.map Y := by
  by_cases hY : AEMeasurable Y μ
  · ext1 s hs
    rw [Measure.snd_apply hs, Measure.map_apply_of_aemeasurable (hX.prodMk hY) (measurable_snd hs),
      Measure.map_apply_of_aemeasurable hY hs, ← univ_prod, mk_preimage_prod, preimage_univ,
      univ_inter]
  · have : ¬AEMeasurable (fun x ↦ (X x, Y x)) μ := by
      contrapose hY
      exact measurable_snd.comp_aemeasurable hY
    simp [map_of_not_aemeasurable, hY, this]
/-
**MeasureTheory.Measure.snd_map_prodMk** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.
Measure`。
形式化陈述：snd_map_prodMk {X : α -> β} {Y : α -> γ} {μ : Measure α} (hX : Measurable 
X) : (μ.map fun a => (X a, Y a)).snd = μ.map Y
参数：hX : Measurable X。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.snd_map_prodMk₀`：snd_map_prodMk₀ {X : α -> β} {Y :
 α -> γ} {μ : Measure α} (hX : AEMeasurable X μ) : (μ.map fun a => (X a, Y a)).s
nd = μ.map Y
· 使用定理 `Measurable.aemeasurable`：Measurable.aemeasurable (h : Measurable f) : AE
Measurable f μ
-/
theorem snd_map_prodMk {X : α → β} {Y : α → γ} {μ : Measure α} (hX : Measurable X) :
    (μ.map fun a => (X a, Y a)).snd = μ.map Y :=
  snd_map_prodMk₀ hX.aemeasurable

@[simp]
/-
**MeasureTheory.Measure.snd_add** 是 Mathlib 中的一个引理，位于命名空间 `MeasureTheory.Measure
`。
形式化陈述：snd_add {μ ν : Measure (α × β)} : (μ + ν).snd = μ.snd + ν.snd
参数：α × β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.map_add`：∀ {α : Type u_1} {β : Type u_2} {mα : Mea
surableSpace α} {mβ : MeasurableSpace β} (μ ν : MeasureTheory.Measure α)   {f : 
α → β},   Measurabl…
· 使用定理 `measurable_snd`：measurable_snd {_ : MeasurableSpace α} {_ : MeasurableSp
ace β} : Measurable (Prod.snd : α × β -> β)
-/
lemma snd_add {μ ν : Measure (α × β)} : (μ + ν).snd = μ.snd + ν.snd :=
  Measure.map_add _ _ measurable_snd
/-
**MeasureTheory.Measure.snd_sum** 是 Mathlib 中的一个引理，位于命名空间 `MeasureTheory.Measure
`。
形式化陈述：snd_sum {ι : Type*} (μ : ι -> Measure (α × β)) : (sum μ).snd = sum (fun n 
=> (μ n).snd)
参数：μ : ι -> Measure (α × β)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `MeasureTheory.Measure.map_sum`：map_sum {ι : Type*} {m : ι -> Measure α} 
{f : α -> β} (hf : AEMeasurable f (Measure.sum m)) : Measure.map f (Measure.sum 
m) = Measure.sum (f…
· 使用定理 `Measurable.aemeasurable`：Measurable.aemeasurable (h : Measurable f) : AE
Measurable f μ
· 使用定理 `measurable_snd`：measurable_snd {_ : MeasurableSpace α} {_ : MeasurableSp
ace β} : Measurable (Prod.snd : α × β -> β)
-/
lemma snd_sum {ι : Type*} (μ : ι → Measure (α × β)) : (sum μ).snd = sum (fun n ↦ (μ n).snd) :=
  map_sum measurable_snd.aemeasurable

@[gcongr]
/-
**MeasureTheory.Measure.snd_mono** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.Measur
e`。
形式化陈述：snd_mono {μ : Measure (α × β)} (h : ρ <= μ) : ρ.snd <= μ.snd
参数：α × β；h : ρ <= μ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.map_mono`：map_mono {f : α -> β} (h : μ <= ν) (hf :
 Measurable f) : μ.map f <= ν.map f
· 使用定理 `measurable_snd`：measurable_snd {_ : MeasurableSpace α} {_ : MeasurableSp
ace β} : Measurable (Prod.snd : α × β -> β)
-/
theorem snd_mono {μ : Measure (α × β)} (h : ρ ≤ μ) : ρ.snd ≤ μ.snd := map_mono h measurable_snd
/-
**MeasureTheory.Measure.fst_map_swap** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.Me
asure`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} [inst : MeasurableSpace α] [inst_1 : Measu
rableSpace β]   {ρ : MeasureTheory.Measure (α × β)}, (MeasureTheory.Measure.map 
Prod.swap ρ).fst = ρ.snd
参数：α × β；MeasureTheory.Measure.map Prod.swap ρ。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.Measure.fst.eq_1`：∀ {α : Type u_1} {β : Type u_2} [inst : 
MeasurableSpace α] [inst_1 : MeasurableSpace β]   (ρ : MeasureTheory.Measure (α 
× β)), ρ.fst = Measu…
· 使用定理 `MeasureTheory.Measure.map_map`：map_map {g : β -> γ} {f : α -> β} (hg : M
easurable g) (hf : Measurable f) : (μ.map f).map g = μ.map (g ∘ f)
· 使用定理 `measurable_fst`：measurable_fst {_ : MeasurableSpace α} {_ : MeasurableSp
ace β} : Measurable (Prod.fst : α × β -> α)
· 使用定理 `measurable_swap`：measurable_swap : Measurable (Prod.swap : α × β -> β × 
α)
-/
@[simp] lemma fst_map_swap : (ρ.map Prod.swap).fst = ρ.snd := by
  rw [Measure.fst, Measure.map_map measurable_fst measurable_swap]
  rfl
/-
**MeasureTheory.Measure.snd_map_swap** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.Me
asure`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} [inst : MeasurableSpace α] [inst_1 : Measu
rableSpace β]   {ρ : MeasureTheory.Measure (α × β)}, (MeasureTheory.Measure.map 
Prod.swap ρ).snd = ρ.fst
参数：α × β；MeasureTheory.Measure.map Prod.swap ρ。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.Measure.snd.eq_1`：∀ {α : Type u_1} {β : Type u_2} [inst : 
MeasurableSpace α] [inst_1 : MeasurableSpace β]   (ρ : MeasureTheory.Measure (α 
× β)), ρ.snd = Measu…
· 使用定理 `MeasureTheory.Measure.map_map`：map_map {g : β -> γ} {f : α -> β} (hg : M
easurable g) (hf : Measurable f) : (μ.map f).map g = μ.map (g ∘ f)
· 使用定理 `measurable_snd`：measurable_snd {_ : MeasurableSpace α} {_ : MeasurableSp
ace β} : Measurable (Prod.snd : α × β -> β)
· 使用定理 `measurable_swap`：measurable_swap : Measurable (Prod.swap : α × β -> β × 
α)
-/
@[simp] lemma snd_map_swap : (ρ.map Prod.swap).snd = ρ.fst := by
  rw [Measure.snd, Measure.map_map measurable_snd measurable_swap]
  rfl

end Measure

section MeasurePreserving

-- Note that these results cannot be put in the previous `measurePreserving` section since
-- they use `lintegral_prod`.

/-- The measurable equiv induced by the equiv `(α × β) × γ ≃ α × (β × γ)` is measure preserving. -/
/-
**MeasureTheory._root_.MeasureTheory.measurePreserving_prodAssoc** 是 Mathlib 中的一
个定理，位于命名空间 `MeasureTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The measurable equiv induced by the equiv `(α × β) × γ ≃ α × (β × γ)` is measure
 preserving.
-/
theorem _root_.MeasureTheory.measurePreserving_prodAssoc (μa : Measure α) (μb : Measure β)
    (μc : Measure γ) [SFinite μb] [SFinite μc] :
    MeasurePreserving (MeasurableEquiv.prodAssoc : (α × β) × γ ≃ᵐ α × β × γ)
      ((μa.prod μb).prod μc) (μa.prod (μb.prod μc)) where
  measurable := MeasurableEquiv.prodAssoc.measurable
  map_eq := by
    ext s hs
    have A (x : α) : MeasurableSet (Prod.mk x ⁻¹' s) := measurable_prodMk_left hs
    have B : MeasurableSet (MeasurableEquiv.prodAssoc ⁻¹' s) :=
      MeasurableEquiv.prodAssoc.measurable hs
    simp_rw [map_apply MeasurableEquiv.prodAssoc.measurable hs, Measure.prod_apply hs,
    Measure.prod_apply (A _), Measure.prod_apply B,
    lintegral_prod _ (measurable_measure_prodMk_left B).aemeasurable]
    rfl
/-
**MeasureTheory._root_.MeasureTheory.volume_preserving_prodAssoc** 是 Mathlib 中的一
个定理，位于命名空间 `MeasureTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.MeasureTheory.volume_preserving_prodAssoc {α₁ β₁ γ₁ : Type*} [MeasureSpace α₁]
    [MeasureSpace β₁] [MeasureSpace γ₁] [SFinite (volume : Measure β₁)]
    [SFinite (volume : Measure γ₁)] :
    MeasurePreserving (MeasurableEquiv.prodAssoc : (α₁ × β₁) × γ₁ ≃ᵐ α₁ × β₁ × γ₁) :=
  MeasureTheory.measurePreserving_prodAssoc volume volume volume

end MeasurePreserving

end MeasureTheory

