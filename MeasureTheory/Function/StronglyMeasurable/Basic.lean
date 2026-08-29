/-
Copyright (c) 2021 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne, Sébastien Gouëzel
-/
module

public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.MeasureTheory.Function.SimpleFuncDense

/-!
# Strongly measurable and finitely strongly measurable functions

A function `f` is said to be strongly measurable if `f` is the sequential limit of simple functions.
It is said to be finitely strongly measurable with respect to a measure `μ` if the supports
of those simple functions have finite measure.

If the target space has a second countable topology, strongly measurable and measurable are
equivalent.

If the measure is sigma-finite, strongly measurable and finitely strongly measurable are equivalent.

The main property of finitely strongly measurable functions is
`FinStronglyMeasurable.exists_set_sigmaFinite`: there exists a measurable set `t` such that the
function is supported on `t` and `μ.restrict t` is sigma-finite. As a consequence, we can prove some
results for those functions as if the measure was sigma-finite.

We provide a solid API for strongly measurable functions, as a basis for the Bochner integral.

## Main definitions

* `StronglyMeasurable f`: `f : α → β` is the limit of a sequence `fs : ℕ → SimpleFunc α β`.
* `FinStronglyMeasurable f μ`: `f : α → β` is the limit of a sequence `fs : ℕ → SimpleFunc α β`
  such that for all `n ∈ ℕ`, the measure of the support of `fs n` is finite.

## References

* [Hytönen, Tuomas, Jan Van Neerven, Mark Veraar, and Lutz Weis. Analysis in Banach spaces.
  Springer, 2016.][Hytonen_VanNeerven_Veraar_Wies_2016]

-/

@[expose] public section

-- Guard against import creep
assert_not_exists InnerProductSpace

open MeasureTheory Filter TopologicalSpace Function Set MeasureTheory.Measure

open ENNReal Topology MeasureTheory NNReal

variable {α β γ ι : Type*} [Countable ι]

namespace MeasureTheory

local infixr:25 " ->ₛ " => SimpleFunc

section Definitions

variable [TopologicalSpace β]

/-- A function is `StronglyMeasurable` if it is the limit of simple functions. -/
@[fun_prop]
/--
Definition of `StronglyMeasurable` / `StronglyMeasurable` 的定义

English:
definition StronglyMeasurable
  signature: [MeasurableSpace α] (f : α -> β)
  body: exists fs : Nat -> α ->ₛ β, forall x, Tendsto (fun n => fs n x) atTop (𝓝 (f x))

add_aesop_rules safe tactic
  (rule_sets := [Measurable])
  (index := [target @StronglyMeasurable ..])
  (by fun_prop (disch := measurability))

中文:
定义 StronglyMeasurable
  签名: [MeasurableSpace α] (f : α -> β)
  定义体: exists fs : Nat -> α ->ₛ β, forall x, Tendsto (fun n => fs n x) atTop (𝓝 (f x))

add_aesop_rules safe tactic
  (rule_sets := [Measurable])
  (index := [target @StronglyMeasurable ..])
  (by fun_prop (disch := measurability))

Depends on / 依赖: Tendsto
-/
def StronglyMeasurable [MeasurableSpace α] (f : α -> β) : Prop :=
  exists fs : Nat -> α ->ₛ β, forall x, Tendsto (fun n => fs n x) atTop (𝓝 (f x))

add_aesop_rules safe tactic
  (rule_sets := [Measurable])
  (index := [target @StronglyMeasurable ..])
  (by fun_prop (disch := measurability))

/-- The notation for StronglyMeasurable giving the measurable space instance explicitly. -/
scoped notation "StronglyMeasurable[" m "]" => @MeasureTheory.StronglyMeasurable _ _ _ m

/--
Definition of `FinStronglyMeasurable` / `FinStronglyMeasurable` 的定义

English:
definition FinStronglyMeasurable
  signature: [Zero β]
  body: exists fs : Nat -> α ->ₛ β, (forall n, μ (support (fs n)) < ∞) ∧ forall x, Tendsto (fun n => fs n x) atTop (𝓝 (f x))

中文:
定义 FinStronglyMeasurable
  签名: [Zero β]
  定义体: exists fs : Nat -> α ->ₛ β, (forall n, μ (support (fs n)) < ∞) ∧ forall x, Tendsto (fun n => fs n x) atTop (𝓝 (f x))

Depends on / 依赖: Tendsto, support, volume_tac
-/
def FinStronglyMeasurable [Zero β]
    {_ : MeasurableSpace α} (f : α -> β) (μ : Measure α := by volume_tac) : Prop :=
  exists fs : Nat -> α ->ₛ β, (forall n, μ (support (fs n)) < ∞) ∧ forall x, Tendsto (fun n => fs n x) atTop (𝓝 (f x))

end Definitions

open MeasureTheory

/-! ## Strongly measurable functions -/

section StronglyMeasurable
variable {_ : MeasurableSpace α} {μ : Measure α} {f : α -> β} {g : Nat -> α} {m : Nat}

variable [TopologicalSpace β]

@[fun_prop]
/--
theorem `SimpleFunc.stronglyMeasurable` / 定理 `SimpleFunc.stronglyMeasurable`

English:
theorem SimpleFunc.stronglyMeasurable
  given: (f : α ->ₛ β)
  statement: StronglyMeasurable f
  proof: ⟨fun _ => f, fun _ => tendsto_const_nhds⟩

@[simp, nontriviality]

中文:
定理 SimpleFunc.stronglyMeasurable
  条件: (f : α ->ₛ β)
  结论: StronglyMeasurable f
  证明: ⟨fun _ => f, fun _ => tendsto_const_nhds⟩

@[simp, nontriviality]

Depends on / 依赖: tendsto_const_nhds
-/
theorem SimpleFunc.stronglyMeasurable (f : α ->ₛ β) : StronglyMeasurable f :=
  ⟨fun _ => f, fun _ => tendsto_const_nhds⟩

@[simp, nontriviality]
/--
lemma `StronglyMeasurable.of_subsingleton_dom` / 引理 `StronglyMeasurable.of_subsingleton_dom`

English:
lemma StronglyMeasurable.of_subsingleton_dom
  given: [Subsingleton α]
  statement: StronglyMeasurable f
  proof: ⟨fun _ => SimpleFunc.ofFinite f, fun _ => tendsto_const_nhds⟩

@[simp, nontriviality]

中文:
引理 StronglyMeasurable.of_subsingleton_dom
  条件: [Subsingleton α]
  结论: StronglyMeasurable f
  证明: ⟨fun _ => SimpleFunc.ofFinite f, fun _ => tendsto_const_nhds⟩

@[simp, nontriviality]

Depends on / 依赖: SimpleFunc, SimpleFunc.ofFinite, ofFinite, tendsto_const_nhds
-/
lemma StronglyMeasurable.of_subsingleton_dom [Subsingleton α] : StronglyMeasurable f :=
  ⟨fun _ => SimpleFunc.ofFinite f, fun _ => tendsto_const_nhds⟩

@[simp, nontriviality]
/--
lemma `StronglyMeasurable.of_subsingleton_cod` / 引理 `StronglyMeasurable.of_subsingleton_cod`

English:
lemma StronglyMeasurable.of_subsingleton_cod
  given: [Subsingleton β]
  statement: StronglyMeasurable f
  proof: by
  let f_sf : α ->ₛ β := ⟨f, fun x => ?_, Set.Subsingleton.finite Set.subsingleton_of_subsingleton⟩
  · exact ⟨fun _ => f_sf, fun x => tendsto_const_nhds⟩
  · simp [Set.preimage, eq_iff_true_of_subsingleton]

@[fun_prop]

中文:
引理 StronglyMeasurable.of_subsingleton_cod
  条件: [Subsingleton β]
  结论: StronglyMeasurable f
  证明: by
  let f_sf : α ->ₛ β := ⟨f, fun x => ?_, Set.Subsingleton.finite Set.subsingleton_of_subsingleton⟩
  · exact ⟨fun _ => f_sf, fun x => tendsto_const_nhds⟩
  · simp [Set.preimage, eq_iff_true_of_subsingleton]

@[fun_prop]

Depends on / 依赖: Set.Subsingleton.finite, Set.preimage, Set.subsingleton_of_subsingleton, Subsingleton, eq_iff_true_of_subsingleton, f_sf, finite, preimage, subsingleton_of_subsingleton, tendsto_const_nhds
-/
lemma StronglyMeasurable.of_subsingleton_cod [Subsingleton β] : StronglyMeasurable f := by
  let f_sf : α ->ₛ β := ⟨f, fun x => ?_, Set.Subsingleton.finite Set.subsingleton_of_subsingleton⟩
  · exact ⟨fun _ => f_sf, fun x => tendsto_const_nhds⟩
  · simp [Set.preimage, eq_iff_true_of_subsingleton]

@[fun_prop]
/--
theorem `stronglyMeasurable_const` / 定理 `stronglyMeasurable_const`

English:
theorem stronglyMeasurable_const
  given: {b : β}
  statement: StronglyMeasurable fun _ : α => b
  proof: ⟨fun _ => SimpleFunc.const α b, fun _ => tendsto_const_nhds⟩

@[to_additive]

中文:
定理 stronglyMeasurable_const
  条件: {b : β}
  结论: StronglyMeasurable fun _ : α => b
  证明: ⟨fun _ => SimpleFunc.const α b, fun _ => tendsto_const_nhds⟩

@[to_additive]

Depends on / 依赖: SimpleFunc, SimpleFunc.const, tendsto_const_nhds
-/
theorem stronglyMeasurable_const {b : β} : StronglyMeasurable fun _ : α => b :=
  ⟨fun _ => SimpleFunc.const α b, fun _ => tendsto_const_nhds⟩

@[to_additive]
/--
theorem `stronglyMeasurable_one` / 定理 `stronglyMeasurable_one`

English:
theorem stronglyMeasurable_one
  given: [One β]
  statement: StronglyMeasurable (1 : α -> β)
  proof: stronglyMeasurable_const

中文:
定理 stronglyMeasurable_one
  条件: [One β]
  结论: StronglyMeasurable (1 : α -> β)
  证明: stronglyMeasurable_const

Depends on / 依赖: stronglyMeasurable_const
-/
theorem stronglyMeasurable_one [One β] : StronglyMeasurable (1 : α -> β) := stronglyMeasurable_const

/--
theorem `stronglyMeasurable_const'` / 定理 `stronglyMeasurable_const'`

English:
theorem stronglyMeasurable_const'
  given: (hf : forall x y, f x = f y)
  statement: StronglyMeasurable f
  proof: by
  nontriviality α
  inhabit α
  convert! stronglyMeasurable_const (β := β) using 1
  exact funext fun x => hf x default

中文:
定理 stronglyMeasurable_const'
  条件: (hf : 对任意 x y, f x = f y)
  结论: StronglyMeasurable f
  证明: by
  nontriviality α
  inhabit α
  convert! stronglyMeasurable_const (β := β) using 1
  exact funext fun x => hf x default

Depends on / 依赖: convert, inhabit, nontriviality, stronglyMeasurable_const
-/
theorem stronglyMeasurable_const' (hf : forall x y, f x = f y) : StronglyMeasurable f := by
  nontriviality α
  inhabit α
  convert! stronglyMeasurable_const (β := β) using 1
  exact funext fun x => hf x default

variable [MeasurableSingletonClass α]

section aux
omit [TopologicalSpace β]

/--
Definition of `noncomputable` / `noncomputable` 的定义

English:
definition noncomputable
  signature: def simpleFuncAux (f : α -> β) (g : Nat -> α)

中文:
定义 noncomputable
  签名: def simpleFuncAux (f : α -> β) (g : 自然数 -> α)
-/
private noncomputable def simpleFuncAux (f : α -> β) (g : Nat -> α) : Nat -> SimpleFunc α β
  | 0 => .const _ (f (g 0))
  | n + 1 => .piecewise {g n} (.singleton _) (.const _ <| f (g n)) (simpleFuncAux f g n)

/--
lemma `simpleFuncAux_eq_of_lt` / 引理 `simpleFuncAux_eq_of_lt`

English:
lemma simpleFuncAux_eq_of_lt
  statement: forall n > m, simpleFuncAux f g n (g m) = f (g m)
  proof: eq_or_ne (g n) (g m) <;>
      simp [simpleFuncAux, Set.piecewise_eq_of_notMem, hnm.symm, simpleFuncAux_eq_of_lt _ hmn]

中文:
引理 simpleFuncAux_eq_of_lt
  结论: 对任意 n > m, simpleFuncAux f g n (g m) = f (g m)
  证明: eq_or_ne (g n) (g m) <;>
      simp [simpleFuncAux, Set.piecewise_eq_of_notMem, hnm.symm, simpleFuncAux_eq_of_lt _ hmn]
-/
private lemma simpleFuncAux_eq_of_lt : forall n > m, simpleFuncAux f g n (g m) = f (g m)
  | _, .refl => by simp [simpleFuncAux]
  | _, Nat.le.step (m := n) hmn => by
    obtain hnm | hnm := eq_or_ne (g n) (g m) <;>
      simp [simpleFuncAux, Set.piecewise_eq_of_notMem, hnm.symm, simpleFuncAux_eq_of_lt _ hmn]

/--
lemma `simpleFuncAux_eventuallyEq` / 引理 `simpleFuncAux_eventuallyEq`

English:
lemma simpleFuncAux_eventuallyEq
  statement: forallᶠ n in atTop, simpleFuncAux f g n (g m) = f (g m)
  proof: eventually_atTop.2 ⟨_, simpleFuncAux_eq_of_lt⟩

中文:
引理 simpleFuncAux_eventuallyEq
  结论: 对任意ᶠ n in atTop, simpleFuncAux f g n (g m) = f (g m)
  证明: eventually_atTop.2 ⟨_, simpleFuncAux_eq_of_lt⟩
-/
private lemma simpleFuncAux_eventuallyEq : forallᶠ n in atTop, simpleFuncAux f g n (g m) = f (g m) :=
  eventually_atTop.2 ⟨_, simpleFuncAux_eq_of_lt⟩

end aux

@[fun_prop]
/--
lemma `StronglyMeasurable.of_discrete` / 引理 `StronglyMeasurable.of_discrete`

English:
lemma StronglyMeasurable.of_discrete
  given: [Countable α]
  statement: StronglyMeasurable f
  proof: by
  nontriviality α
  obtain ⟨g, hg⟩ := exists_surjective_nat α
  exact ⟨simpleFuncAux f g, hg.forall.2 fun m =>
    tendsto_nhds_of_eventually_eq simpleFuncAux_eventuallyEq⟩

中文:
引理 StronglyMeasurable.of_discrete
  条件: [Countable α]
  结论: StronglyMeasurable f
  证明: by
  nontriviality α
  obtain ⟨g, hg⟩ := exists_surjective_nat α
  exact ⟨simpleFuncAux f g, hg.forall.2 fun m =>
    tendsto_nhds_of_eventually_eq simpleFuncAux_eventuallyEq⟩

Depends on / 依赖: exists_surjective_nat, hg.forall, nontriviality, simpleFuncAux, simpleFuncAux_eventuallyEq, tendsto_nhds_of_eventually_eq
-/
lemma StronglyMeasurable.of_discrete [Countable α] : StronglyMeasurable f := by
  nontriviality α
  obtain ⟨g, hg⟩ := exists_surjective_nat α
  exact ⟨simpleFuncAux f g, hg.forall.2 fun m =>
    tendsto_nhds_of_eventually_eq simpleFuncAux_eventuallyEq⟩

end StronglyMeasurable

namespace StronglyMeasurable

variable {f g : α -> β}

section BasicPropertiesInAnyTopologicalSpace

variable [TopologicalSpace β]

/--
Definition of `noncomputable` / `noncomputable` 的定义

English:
definition noncomputable
  signature: def approx {_ : MeasurableSpace α} (hf : StronglyMeasurable f)
  body: hf.choose

中文:
定义 noncomputable
  签名: def approx {_ : MeasurableSpace α} (hf : StronglyMeasurable f)
  定义体: hf.choose
-/
protected noncomputable def approx {_ : MeasurableSpace α} (hf : StronglyMeasurable f) :
    Nat -> α ->ₛ β :=
  hf.choose

/--
theorem `tendsto_approx` / 定理 `tendsto_approx`

English:
theorem tendsto_approx
  given: {_ : MeasurableSpace α} (hf : StronglyMeasurable f)
  proof: hf.choose_spec

中文:
定理 tendsto_approx
  条件: {_ : MeasurableSpace α} (hf : StronglyMeasurable f)
  证明: hf.choose_spec
-/
protected theorem tendsto_approx {_ : MeasurableSpace α} (hf : StronglyMeasurable f) :
    forall x, Tendsto (fun n => hf.approx n x) atTop (𝓝 (f x)) :=
  hf.choose_spec

/--
Definition of `approxBounded` / `approxBounded` 的定义

English:
definition approxBounded
  signature: {_ : MeasurableSpace α} [Norm β] [SMul Real β]
  body: fun n =>
  (hf.approx n).map fun x => min 1 (c / ‖x‖) • x

中文:
定义 approxBounded
  签名: {_ : MeasurableSpace α} [Norm β] [SMul 实数 β]
  定义体: fun n =>
  (hf.approx n).map fun x => min 1 (c / ‖x‖) • x
-/
noncomputable def approxBounded {_ : MeasurableSpace α} [Norm β] [SMul Real β]
    (hf : StronglyMeasurable f) (c : Real) : Nat -> SimpleFunc α β := fun n =>
  (hf.approx n).map fun x => min 1 (c / ‖x‖) • x

/--
theorem `tendsto_approxBounded_of_norm_le` / 定理 `tendsto_approxBounded_of_norm_le`

English:
theorem tendsto_approxBounded_of_norm_le
  statement: {β} {f : α -> β} [NormedAddCommGroup β] [NormedSpace Real β]
  proof: by
  have h_tendsto := hf.tendsto_approx x
  simp only [StronglyMeasurable.approxBounded, SimpleFunc.coe_map, Function.comp_apply]
  by_cases hfx0 : ‖f x‖ = 0
  · rw [norm_eq_zero] at hfx0
    rw [hfx0] at h_tendsto ⊢
    have h_tendsto_norm : Tendsto (fun n => ‖hf.approx n x‖) atTop (𝓝 0) := by
   

中文:
定理 tendsto_approxBounded_of_norm_le
  结论: {β} {f : α -> β} [NormedAddCommGroup β] [NormedSpace 实数 β]
  证明: by
  have h_tendsto := hf.tendsto_approx x
  simp only [StronglyMeasurable.approxBounded, SimpleFunc.coe_map, Function.comp_apply]
  by_cases hfx0 : ‖f x‖ = 0
  · rw [norm_eq_zero] at hfx0
    rw [hfx0] at h_tendsto ⊢
    have h_tendsto_norm : Tendsto (fun n => ‖hf.approx n x‖) atTop (𝓝 0) := by
   

Depends on / 依赖: Function, Function.comp_apply, SimpleFunc, SimpleFunc.coe_map, StronglyMeasurable, StronglyMeasurable.approxBounded, Tendsto, approx, approxBounded, coe_map, comp_apply, convert, h_tendsto, h_tendsto.norm, h_tendsto_norm, hf.approx, hf.tendsto_approx, norm_eq_zero, norm_smul, norm_zero
-/
theorem tendsto_approxBounded_of_norm_le {β} {f : α -> β} [NormedAddCommGroup β] [NormedSpace Real β]
    {m : MeasurableSpace α} (hf : StronglyMeasurable[m] f) {c : Real} {x : α} (hfx : ‖f x‖ <= c) :
    Tendsto (fun n => hf.approxBounded c n x) atTop (𝓝 (f x)) := by
  have h_tendsto := hf.tendsto_approx x
  simp only [StronglyMeasurable.approxBounded, SimpleFunc.coe_map, Function.comp_apply]
  by_cases hfx0 : ‖f x‖ = 0
  · rw [norm_eq_zero] at hfx0
    rw [hfx0] at h_tendsto ⊢
    have h_tendsto_norm : Tendsto (fun n => ‖hf.approx n x‖) atTop (𝓝 0) := by
      convert! h_tendsto.norm
      rw [norm_zero]
    refine squeeze_zero_norm (fun n => ?_) h_tendsto_norm
    calc
      ‖min 1 (c / ‖hf.approx n x‖) • hf.approx n x‖ =
          ‖min 1 (c / ‖hf.approx n x‖)‖ * ‖hf.approx n x‖ :=
        norm_smul _ _
      _ <= ‖(1 : Real)‖ * ‖hf.approx n x‖ := by
        gcongr
        rw [norm_one]; rw [Real.norm_of_nonneg]
        · exact min_le_left _ _
        · exact le_min zero_le_one (div_nonneg ((norm_nonneg _).trans hfx) (norm_nonneg _))
      _ = ‖hf.approx n x‖ := by rw [norm_one, one_mul]
  rw [← one_smul Real (f x)]
  refine Tendsto.smul ?_ h_tendsto
  have : min 1 (c / ‖f x‖) = 1 := by
    rw [min_eq_left_iff]; rw [one_le_div (lt_of_le_of_ne (norm_nonneg _) (Ne.symm hfx0))]
    exact hfx
  nth_rw 2 [this.symm]
  refine Tendsto.min tendsto_const_nhds ?_
  exact Tendsto.div tendsto_const_nhds h_tendsto.norm hfx0

/--
theorem `tendsto_approxBounded_ae` / 定理 `tendsto_approxBounded_ae`

English:
theorem tendsto_approxBounded_ae
  statement: {β} {f : α -> β} [NormedAddCommGroup β] [NormedSpace Real β]
  proof: by
  filter_upwards [hf_bound] with x hfx using tendsto_approxBounded_of_norm_le hf hfx

中文:
定理 tendsto_approxBounded_ae
  结论: {β} {f : α -> β} [NormedAddCommGroup β] [NormedSpace 实数 β]
  证明: by
  filter_upwards [hf_bound] with x hfx using tendsto_approxBounded_of_norm_le hf hfx

Depends on / 依赖: filter_upwards, hf_bound, tendsto_approxBounded_of_norm_le
-/
theorem tendsto_approxBounded_ae {β} {f : α -> β} [NormedAddCommGroup β] [NormedSpace Real β]
    {m m0 : MeasurableSpace α} {μ : Measure α} (hf : StronglyMeasurable[m] f) {c : Real}
    (hf_bound : forallᵐ x ∂μ, ‖f x‖ <= c) :
    forallᵐ x ∂μ, Tendsto (fun n => hf.approxBounded c n x) atTop (𝓝 (f x)) := by
  filter_upwards [hf_bound] with x hfx using tendsto_approxBounded_of_norm_le hf hfx

/--
theorem `norm_approxBounded_le` / 定理 `norm_approxBounded_le`

English:
theorem norm_approxBounded_le
  statement: {β} {f : α -> β} [SeminormedAddCommGroup β] [NormedSpace Real β]
  proof: by
  simp only [StronglyMeasurable.approxBounded, SimpleFunc.coe_map, Function.comp_apply]
  refine (norm_smul_le _ _).trans ?_
  by_cases h0 : ‖hf.approx n x‖ = 0
  · simp only [h0, _root_.div_zero, min_eq_right, zero_le_one, norm_zero, mul_zero]
    exact hc
  rcases le_total ‖hf.approx n x‖ c wit

中文:
定理 norm_approxBounded_le
  结论: {β} {f : α -> β} [SeminormedAddCommGroup β] [NormedSpace 实数 β]
  证明: by
  simp only [StronglyMeasurable.approxBounded, SimpleFunc.coe_map, Function.comp_apply]
  refine (norm_smul_le _ _).trans ?_
  by_cases h0 : ‖hf.approx n x‖ = 0
  · simp only [h0, _root_.div_zero, min_eq_right, zero_le_one, norm_zero, mul_zero]
    exact hc
  rcases le_total ‖hf.approx n x‖ c wit

Depends on / 依赖: Function, Function.comp_apply, Ne.symm, SimpleFunc, SimpleFunc.coe_map, StronglyMeasurable, StronglyMeasurable.approxBounded, _root_, _root_.div_zero, approx, approxBounded, coe_map, comp_apply, div_eq_mul_, div_zero, hf.approx, le_total, lt_of_le_of_ne, min_eq_left, min_eq_right
-/
theorem norm_approxBounded_le {β} {f : α -> β} [SeminormedAddCommGroup β] [NormedSpace Real β]
    {m : MeasurableSpace α} {c : Real} (hf : StronglyMeasurable[m] f) (hc : 0 <= c) (n : Nat) (x : α) :
    ‖hf.approxBounded c n x‖ <= c := by
  simp only [StronglyMeasurable.approxBounded, SimpleFunc.coe_map, Function.comp_apply]
  refine (norm_smul_le _ _).trans ?_
  by_cases h0 : ‖hf.approx n x‖ = 0
  · simp only [h0, _root_.div_zero, min_eq_right, zero_le_one, norm_zero, mul_zero]
    exact hc
  rcases le_total ‖hf.approx n x‖ c with h | h
  · rw [min_eq_left _]
    · simpa only [norm_one, one_mul] using h
    · rwa [one_le_div (lt_of_le_of_ne (norm_nonneg _) (Ne.symm h0))]
  · rw [min_eq_right _]
    · rw [norm_div, norm_norm, mul_comm, mul_div, div_eq_mul_inv, mul_comm, ← mul_assoc,
        inv_mul_cancel₀ h0, one_mul, Real.norm_of_nonneg hc]
    · rwa [div_le_one (lt_of_le_of_ne (norm_nonneg _) (Ne.symm h0))]

/--
theorem `_root_.stronglyMeasurable_bot_iff` / 定理 `_root_.stronglyMeasurable_bot_iff`

English:
theorem _root_.stronglyMeasurable_bot_iff
  given: [Nonempty β] [T2Space β]
  proof: by
  rcases isEmpty_or_nonempty α with hα | hα
  · simp [eq_iff_true_of_subsingleton]
  refine ⟨fun hf => ?_, fun hf_eq => ?_⟩
  · refine ⟨f hα.some, ?_⟩
    let fs := hf.approx
    have h_fs_tendsto : forall x, Tendsto (fun n => fs n x) atTop (𝓝 (f x)) := hf.tendsto_approx
    have : forall n, exis

中文:
定理 _root_.stronglyMeasurable_bot_iff
  条件: [Nonempty β] [T2Space β]
  证明: by
  rcases isEmpty_or_nonempty α with hα | hα
  · simp [eq_iff_true_of_subsingleton]
  refine ⟨fun hf => ?_, fun hf_eq => ?_⟩
  · refine ⟨f hα.some, ?_⟩
    let fs := hf.approx
    have h_fs_tendsto : forall x, Tendsto (fun n => fs n x) atTop (𝓝 (f x)) := hf.tendsto_approx
    have : forall n, exis

Depends on / 依赖: SimpleFunc, SimpleFunc.simpleFunc_bot, Tendsto, approx, choose_spec, eq_iff_true_of_subsingleton, h_cs_eq, h_fs_tendsto, hf.approx, hf.tendsto_approx, hf_eq, isEmpty_or_nonempty, simpleFunc_bot, tendsto_approx
-/
theorem _root_.stronglyMeasurable_bot_iff [Nonempty β] [T2Space β] :
    StronglyMeasurable[⊥] f ↔ exists c, f = fun _ => c := by
  rcases isEmpty_or_nonempty α with hα | hα
  · simp [eq_iff_true_of_subsingleton]
  refine ⟨fun hf => ?_, fun hf_eq => ?_⟩
  · refine ⟨f hα.some, ?_⟩
    let fs := hf.approx
    have h_fs_tendsto : forall x, Tendsto (fun n => fs n x) atTop (𝓝 (f x)) := hf.tendsto_approx
    have : forall n, exists c, forall x, fs n x = c := fun n => SimpleFunc.simpleFunc_bot (fs n)
    let cs n := (this n).choose
    have h_cs_eq : forall n, ⇑(fs n) = fun _ => cs n := fun n => funext (this n).choose_spec
    conv at h_fs_tendsto => enter [x, 1, n]; rw [h_cs_eq]
    have h_tendsto : Tendsto cs atTop (𝓝 (f hα.some)) := h_fs_tendsto hα.some
    ext1 x
    exact tendsto_nhds_unique (h_fs_tendsto x) h_tendsto
  · obtain ⟨c, rfl⟩ := hf_eq
    exact stronglyMeasurable_const

end BasicPropertiesInAnyTopologicalSpace

/--
theorem `finStronglyMeasurable_of_set_sigmaFinite` / 定理 `finStronglyMeasurable_of_set_sigmaFinite`

English:
theorem finStronglyMeasurable_of_set_sigmaFinite
  statement: [TopologicalSpace β] [Zero β]
  proof: by
  have : SigmaFinite (μ.restrict t) := htμ
  let S := spanningSets (μ.restrict t)
  have hS_meas : forall n, MeasurableSet (S n) := measurableSet_spanningSets (μ.restrict t)
  let f_approx := hf_meas.approx
  let fs n := SimpleFunc.restrict (f_approx n) (S n inter t)
  have h_fs_t_compl : forall 

中文:
定理 finStronglyMeasurable_of_set_sigmaFinite
  结论: [TopologicalSpace β] [Zero β]
  证明: by
  have : SigmaFinite (μ.restrict t) := htμ
  let S := spanningSets (μ.restrict t)
  have hS_meas : forall n, MeasurableSet (S n) := measurableSet_spanningSets (μ.restrict t)
  let f_approx := hf_meas.approx
  let fs n := SimpleFunc.restrict (f_approx n) (S n inter t)
  have h_fs_t_compl : forall 

Depends on / 依赖: MeasurableSet, Set.indicator_of_notMem, SigmaFinite, SimpleFunc, SimpleFunc.restrict, SimpleFunc.restrict_apply, SimpleFunc.suppo, approx, f_approx, hS_meas, h_fs_t_compl, hf_meas, hf_meas.approx, indicator_of_notMem, measurableSet_spanningSets, restrict, restrict_apply, simp_rw, spanningSets
-/
theorem finStronglyMeasurable_of_set_sigmaFinite [TopologicalSpace β] [Zero β]
    {m : MeasurableSpace α} {μ : Measure α} (hf_meas : StronglyMeasurable f) {t : Set α}
    (ht : MeasurableSet t) (hft_zero : forall x in tᶜ, f x = 0) (htμ : SigmaFinite (μ.restrict t)) :
    FinStronglyMeasurable f μ := by
  have : SigmaFinite (μ.restrict t) := htμ
  let S := spanningSets (μ.restrict t)
  have hS_meas : forall n, MeasurableSet (S n) := measurableSet_spanningSets (μ.restrict t)
  let f_approx := hf_meas.approx
  let fs n := SimpleFunc.restrict (f_approx n) (S n inter t)
  have h_fs_t_compl : forall n, forall x, x ∉ t -> fs n x = 0 := by
    intro n x hxt
    rw [SimpleFunc.restrict_apply _ ((hS_meas n).inter ht)]
    refine Set.indicator_of_notMem ?_ _
    simp [hxt]
  refine ⟨fs, ?_, fun x => ?_⟩
  · simp_rw [SimpleFunc.support_eq, ← Finset.mem_coe]
    classical
    refine fun n => measure_biUnion_lt_top {y in (fs n).range | y != 0}.finite_toSet fun y hy => ?_
    rw [SimpleFunc.restrict_preimage_singleton _ ((hS_meas n).inter ht)]
    swap
    · let : (y : β) -> Decidable (y = 0) := fun y => Classical.propDecidable _
      rw [Finset.mem_coe]; rw [Finset.mem_filter] at hy
      exact hy.2
    refine (measure_mono Set.inter_subset_left).trans_lt ?_
    have h_lt_top := measure_spanningSets_lt_top (μ.restrict t) n
    rwa [Measure.restrict_apply' ht] at h_lt_top
  · by_cases hxt : x in t
    swap
    · rw [funext fun n => h_fs_t_compl n x hxt, hft_zero x hxt]
      exact tendsto_const_nhds
    have h : Tendsto (fun n => (f_approx n) x) atTop (𝓝 (f x)) := hf_meas.tendsto_approx x
    obtain ⟨n₁, hn₁⟩ : exists n, forall m, n <= m -> fs m x = f_approx m x := by
      obtain ⟨n, hn⟩ : exists n, forall m, n <= m -> x in S m inter t := by
        rsuffices ⟨n, hn⟩ : exists n, forall m, n <= m -> x in S m
        · exact ⟨n, fun m hnm => Set.mem_inter (hn m hnm) hxt⟩
        rsuffices ⟨n, hn⟩ : exists n, x in S n
        · exact ⟨n, fun m hnm => monotone_spanningSets (μ.restrict t) hnm hn⟩
        rw [← Set.mem_iUnion]; rw [iUnion_spanningSets (μ.restrict t)]
        trivial
      refine ⟨n, fun m hnm => ?_⟩
      simp_rw [fs, SimpleFunc.restrict_apply _ ((hS_meas m).inter ht),
        Set.indicator_of_mem (hn m hnm)]
    rw [tendsto_atTop'] at h ⊢
    intro s hs
    obtain ⟨n₂, hn₂⟩ := h s hs
    refine ⟨max n₁ n₂, fun m hm => ?_⟩
    rw [hn₁ m ((le_max_left _ _).trans hm)]
    exact hn₂ m ((le_max_right _ _).trans hm)

/-- If the measure is sigma-finite, all strongly measurable functions are
  `FinStronglyMeasurable`. -/
@[aesop 5% apply (rule_sets := [Measurable])]
/--
theorem `finStronglyMeasurable` / 定理 `finStronglyMeasurable`

English:
theorem finStronglyMeasurable
  statement: [TopologicalSpace β] [Zero β] {m0 : MeasurableSpace α}
  proof: hf.finStronglyMeasurable_of_set_sigmaFinite MeasurableSet.univ (by simp)
    (by rwa [Measure.restrict_univ])

中文:
定理 finStronglyMeasurable
  结论: [TopologicalSpace β] [Zero β] {m0 : MeasurableSpace α}
  证明: hf.finStronglyMeasurable_of_set_sigmaFinite MeasurableSet.univ (by simp)
    (by rwa [Measure.restrict_univ])
-/
protected theorem finStronglyMeasurable [TopologicalSpace β] [Zero β] {m0 : MeasurableSpace α}
    (hf : StronglyMeasurable f) (μ : Measure α) [SigmaFinite μ] : FinStronglyMeasurable f μ :=
  hf.finStronglyMeasurable_of_set_sigmaFinite MeasurableSet.univ (by simp)
    (by rwa [Measure.restrict_univ])

/-- A strongly measurable function is measurable. -/
@[fun_prop]
/--
theorem `measurable` / 定理 `measurable`

English:
theorem measurable
  statement: {_ : MeasurableSpace α} [TopologicalSpace β] [PseudoMetrizableSpace β]
  proof: measurable_of_tendsto_metrizable (fun n => (hf.approx n).measurable)
    (tendsto_pi_nhds.mpr hf.tendsto_approx)

中文:
定理 measurable
  结论: {_ : MeasurableSpace α} [TopologicalSpace β] [PseudoMetrizableSpace β]
  证明: measurable_of_tendsto_metrizable (fun n => (hf.approx n).measurable)
    (tendsto_pi_nhds.mpr hf.tendsto_approx)
-/
protected theorem measurable {_ : MeasurableSpace α} [TopologicalSpace β] [PseudoMetrizableSpace β]
    [MeasurableSpace β] [BorelSpace β] (hf : StronglyMeasurable f) : Measurable f :=
  measurable_of_tendsto_metrizable (fun n => (hf.approx n).measurable)
    (tendsto_pi_nhds.mpr hf.tendsto_approx)

/-- A strongly measurable function is almost everywhere measurable. -/
@[fun_prop]
/--
theorem `aemeasurable` / 定理 `aemeasurable`

English:
theorem aemeasurable
  statement: {_ : MeasurableSpace α} [TopologicalSpace β]
  proof: hf.measurable.aemeasurable

中文:
定理 aemeasurable
  结论: {_ : MeasurableSpace α} [TopologicalSpace β]
  证明: hf.measurable.aemeasurable
-/
protected theorem aemeasurable {_ : MeasurableSpace α} [TopologicalSpace β]
    [PseudoMetrizableSpace β] [MeasurableSpace β] [BorelSpace β] {μ : Measure α}
    (hf : StronglyMeasurable f) : AEMeasurable f μ :=
  hf.measurable.aemeasurable

/--
theorem `_root_.Continuous.comp_stronglyMeasurable` / 定理 `_root_.Continuous.comp_stronglyMeasurable`

English:
theorem _root_.Continuous.comp_stronglyMeasurable
  statement: {_ : MeasurableSpace α} [TopologicalSpace β]
  proof: ⟨fun n => SimpleFunc.map g (hf.approx n), fun x => (hg.tendsto _).comp (hf.tendsto_approx x)⟩

@[to_additive]
nonrec theorem measurableSet_mulSupport {m : MeasurableSpace α} [One β] [TopologicalSpace β]
    [MetrizableSpace β] (hf : StronglyMeasurable f) : MeasurableSet (mulSupport f) := by
  boreli

中文:
定理 _root_.Continuous.comp_stronglyMeasurable
  结论: {_ : MeasurableSpace α} [TopologicalSpace β]
  证明: ⟨fun n => SimpleFunc.map g (hf.approx n), fun x => (hg.tendsto _).comp (hf.tendsto_approx x)⟩

@[to_additive]
nonrec theorem measurableSet_mulSupport {m : MeasurableSpace α} [One β] [TopologicalSpace β]
    [MetrizableSpace β] (hf : StronglyMeasurable f) : MeasurableSet (mulSupport f) := by
  boreli

Depends on / 依赖: SimpleFunc, SimpleFunc.map, approx, hf.approx, hf.tendsto_approx, hg.tendsto, tendsto, tendsto_approx
-/
theorem _root_.Continuous.comp_stronglyMeasurable {_ : MeasurableSpace α} [TopologicalSpace β]
    [TopologicalSpace γ] {g : β -> γ} {f : α -> β} (hg : Continuous g) (hf : StronglyMeasurable f) :
    StronglyMeasurable fun x => g (f x) :=
  ⟨fun n => SimpleFunc.map g (hf.approx n), fun x => (hg.tendsto _).comp (hf.tendsto_approx x)⟩

@[to_additive]
nonrec theorem measurableSet_mulSupport {m : MeasurableSpace α} [One β] [TopologicalSpace β]
    [MetrizableSpace β] (hf : StronglyMeasurable f) : MeasurableSet (mulSupport f) := by
  borelize β
  exact measurableSet_mulSupport hf.measurable

/--
theorem `mono` / 定理 `mono`

English:
theorem mono
  statement: {m m' : MeasurableSpace α} [TopologicalSpace β]
  proof: by
  let f_approx : Nat -> @SimpleFunc α m β := fun n =>
    @SimpleFunc.mk α m β
      (hf.approx n)
      (fun x => h_mono _ (SimpleFunc.measurableSet_fiber' _ x))
      (SimpleFunc.finite_range (hf.approx n))
  exact ⟨f_approx, hf.tendsto_approx⟩

@[fun_prop]

中文:
定理 mono
  结论: {m m' : MeasurableSpace α} [TopologicalSpace β]
  证明: by
  let f_approx : Nat -> @SimpleFunc α m β := fun n =>
    @SimpleFunc.mk α m β
      (hf.approx n)
      (fun x => h_mono _ (SimpleFunc.measurableSet_fiber' _ x))
      (SimpleFunc.finite_range (hf.approx n))
  exact ⟨f_approx, hf.tendsto_approx⟩

@[fun_prop]
-/
protected theorem mono {m m' : MeasurableSpace α} [TopologicalSpace β]
    (hf : StronglyMeasurable[m'] f) (h_mono : m' <= m) : StronglyMeasurable[m] f := by
  let f_approx : Nat -> @SimpleFunc α m β := fun n =>
    @SimpleFunc.mk α m β
      (hf.approx n)
      (fun x => h_mono _ (SimpleFunc.measurableSet_fiber' _ x))
      (SimpleFunc.finite_range (hf.approx n))
  exact ⟨f_approx, hf.tendsto_approx⟩

@[fun_prop]
/--
theorem `fst` / 定理 `fst`

English:
theorem fst
  statement: {m : MeasurableSpace α} [TopologicalSpace β] [TopologicalSpace γ]
  proof: continuous_fst.comp_stronglyMeasurable hf

@[fun_prop]

中文:
定理 fst
  结论: {m : MeasurableSpace α} [TopologicalSpace β] [TopologicalSpace γ]
  证明: continuous_fst.comp_stronglyMeasurable hf

@[fun_prop]
-/
protected theorem fst {m : MeasurableSpace α} [TopologicalSpace β] [TopologicalSpace γ]
    {f : α -> β × γ} (hf : StronglyMeasurable f) : StronglyMeasurable fun x => (f x).1 :=
  continuous_fst.comp_stronglyMeasurable hf

@[fun_prop]
/--
theorem `snd` / 定理 `snd`

English:
theorem snd
  statement: {m : MeasurableSpace α} [TopologicalSpace β] [TopologicalSpace γ]
  proof: continuous_snd.comp_stronglyMeasurable hf

@[fun_prop]

中文:
定理 snd
  结论: {m : MeasurableSpace α} [TopologicalSpace β] [TopologicalSpace γ]
  证明: continuous_snd.comp_stronglyMeasurable hf

@[fun_prop]
-/
protected theorem snd {m : MeasurableSpace α} [TopologicalSpace β] [TopologicalSpace γ]
    {f : α -> β × γ} (hf : StronglyMeasurable f) : StronglyMeasurable fun x => (f x).2 :=
  continuous_snd.comp_stronglyMeasurable hf

@[fun_prop]
/--
theorem `prodMk` / 定理 `prodMk`

English:
theorem prodMk
  statement: {m : MeasurableSpace α} [TopologicalSpace β] [TopologicalSpace γ]
  proof: by
  refine ⟨fun n => SimpleFunc.pair (hf.approx n) (hg.approx n), fun x => ?_⟩
  rw [nhds_prod_eq]
  exact Tendsto.prodMk (hf.tendsto_approx x) (hg.tendsto_approx x)

@[fun_prop]

中文:
定理 prodMk
  结论: {m : MeasurableSpace α} [TopologicalSpace β] [TopologicalSpace γ]
  证明: by
  refine ⟨fun n => SimpleFunc.pair (hf.approx n) (hg.approx n), fun x => ?_⟩
  rw [nhds_prod_eq]
  exact Tendsto.prodMk (hf.tendsto_approx x) (hg.tendsto_approx x)

@[fun_prop]
-/
protected theorem prodMk {m : MeasurableSpace α} [TopologicalSpace β] [TopologicalSpace γ]
    {f : α -> β} {g : α -> γ} (hf : StronglyMeasurable f) (hg : StronglyMeasurable g) :
    StronglyMeasurable fun x => (f x, g x) := by
  refine ⟨fun n => SimpleFunc.pair (hf.approx n) (hg.approx n), fun x => ?_⟩
  rw [nhds_prod_eq]
  exact Tendsto.prodMk (hf.tendsto_approx x) (hg.tendsto_approx x)

@[fun_prop]
/--
theorem `comp_measurable` / 定理 `comp_measurable`

English:
theorem comp_measurable
  statement: [TopologicalSpace β] {_ : MeasurableSpace α} {_ : MeasurableSpace γ}
  proof: ⟨fun n => SimpleFunc.comp (hf.approx n) g hg, fun x => hf.tendsto_approx (g x)⟩

中文:
定理 comp_measurable
  结论: [TopologicalSpace β] {_ : MeasurableSpace α} {_ : MeasurableSpace γ}
  证明: ⟨fun n => SimpleFunc.comp (hf.approx n) g hg, fun x => hf.tendsto_approx (g x)⟩

Depends on / 依赖: SimpleFunc, SimpleFunc.comp, approx, hf.approx, hf.tendsto_approx, tendsto_approx
-/
theorem comp_measurable [TopologicalSpace β] {_ : MeasurableSpace α} {_ : MeasurableSpace γ}
    {f : α -> β} {g : γ -> α} (hf : StronglyMeasurable f) (hg : Measurable g) :
    StronglyMeasurable (f ∘ g) :=
  ⟨fun n => SimpleFunc.comp (hf.approx n) g hg, fun x => hf.tendsto_approx (g x)⟩

/--
theorem `of_uncurry_left` / 定理 `of_uncurry_left`

English:
theorem of_uncurry_left
  statement: [TopologicalSpace β] {_ : MeasurableSpace α} {_ : MeasurableSpace γ}
  proof: hf.comp_measurable measurable_prodMk_left

中文:
定理 of_uncurry_left
  结论: [TopologicalSpace β] {_ : MeasurableSpace α} {_ : MeasurableSpace γ}
  证明: hf.comp_measurable measurable_prodMk_left

Depends on / 依赖: comp_measurable, hf.comp_measurable, measurable_prodMk_left
-/
theorem of_uncurry_left [TopologicalSpace β] {_ : MeasurableSpace α} {_ : MeasurableSpace γ}
    {f : α -> γ -> β} (hf : StronglyMeasurable (uncurry f)) {x : α} : StronglyMeasurable (f x) :=
  hf.comp_measurable measurable_prodMk_left

/--
theorem `of_uncurry_right` / 定理 `of_uncurry_right`

English:
theorem of_uncurry_right
  statement: [TopologicalSpace β] {_ : MeasurableSpace α} {_ : MeasurableSpace γ}
  proof: hf.comp_measurable measurable_prodMk_right

中文:
定理 of_uncurry_right
  结论: [TopologicalSpace β] {_ : MeasurableSpace α} {_ : MeasurableSpace γ}
  证明: hf.comp_measurable measurable_prodMk_right

Depends on / 依赖: comp_measurable, hf.comp_measurable, measurable_prodMk_right
-/
theorem of_uncurry_right [TopologicalSpace β] {_ : MeasurableSpace α} {_ : MeasurableSpace γ}
    {f : α -> γ -> β} (hf : StronglyMeasurable (uncurry f)) {y : γ} :
    StronglyMeasurable fun x => f x y :=
  hf.comp_measurable measurable_prodMk_right

/--
theorem `prod_swap` / 定理 `prod_swap`

English:
theorem prod_swap
  statement: {_ : MeasurableSpace α} {_ : MeasurableSpace β} [TopologicalSpace γ]
  proof: hf.comp_measurable measurable_swap

中文:
定理 prod_swap
  结论: {_ : MeasurableSpace α} {_ : MeasurableSpace β} [TopologicalSpace γ]
  证明: hf.comp_measurable measurable_swap
-/
protected theorem prod_swap {_ : MeasurableSpace α} {_ : MeasurableSpace β} [TopologicalSpace γ]
    {f : β × α -> γ} (hf : StronglyMeasurable f) :
    StronglyMeasurable (fun z : α × β => f z.swap) :=
  hf.comp_measurable measurable_swap

/--
theorem `comp_fst` / 定理 `comp_fst`

English:
theorem comp_fst
  statement: {_ : MeasurableSpace α} [mβ : MeasurableSpace β] [TopologicalSpace γ]
  proof: hf.comp_measurable measurable_fst

中文:
定理 comp_fst
  结论: {_ : MeasurableSpace α} [mβ : MeasurableSpace β] [TopologicalSpace γ]
  证明: hf.comp_measurable measurable_fst
-/
protected theorem comp_fst {_ : MeasurableSpace α} [mβ : MeasurableSpace β] [TopologicalSpace γ]
    {f : α -> γ} (hf : StronglyMeasurable f) :
    StronglyMeasurable (fun z : α × β => f z.1) :=
  hf.comp_measurable measurable_fst

/--
theorem `comp_snd` / 定理 `comp_snd`

English:
theorem comp_snd
  statement: [mα : MeasurableSpace α] {_ : MeasurableSpace β} [TopologicalSpace γ]
  proof: hf.comp_measurable measurable_snd

中文:
定理 comp_snd
  结论: [mα : MeasurableSpace α] {_ : MeasurableSpace β} [TopologicalSpace γ]
  证明: hf.comp_measurable measurable_snd
-/
protected theorem comp_snd [mα : MeasurableSpace α] {_ : MeasurableSpace β} [TopologicalSpace γ]
    {f : β -> γ} (hf : StronglyMeasurable f) :
    StronglyMeasurable (fun z : α × β => f z.2) :=
  hf.comp_measurable measurable_snd

section Arithmetic

variable {mα : MeasurableSpace α} [TopologicalSpace β]

@[to_fun (attr := to_additive (attr := fun_prop))]
/--
theorem `mul` / 定理 `mul`

English:
theorem mul
  statement: [Mul β] [ContinuousMul β] (hf : StronglyMeasurable f)
  proof: ⟨fun n => hf.approx n * hg.approx n, fun x => (hf.tendsto_approx x).mul (hg.tendsto_approx x)⟩

@[to_additive (attr := fun_prop)]

中文:
定理 mul
  结论: [Mul β] [ContinuousMul β] (hf : StronglyMeasurable f)
  证明: ⟨fun n => hf.approx n * hg.approx n, fun x => (hf.tendsto_approx x).mul (hg.tendsto_approx x)⟩

@[to_additive (attr := fun_prop)]
-/
protected theorem mul [Mul β] [ContinuousMul β] (hf : StronglyMeasurable f)
    (hg : StronglyMeasurable g) : StronglyMeasurable (f * g) :=
  ⟨fun n => hf.approx n * hg.approx n, fun x => (hf.tendsto_approx x).mul (hg.tendsto_approx x)⟩

@[to_additive (attr := fun_prop)]
/--
theorem `mul_const` / 定理 `mul_const`

English:
theorem mul_const
  given: [Mul β] [ContinuousMul β] (hf : StronglyMeasurable f) (c : β)
  proof: hf.mul stronglyMeasurable_const

@[to_additive (attr := fun_prop)]

中文:
定理 mul_const
  条件: [Mul β] [ContinuousMul β] (hf : StronglyMeasurable f) (c : β)
  证明: hf.mul stronglyMeasurable_const

@[to_additive (attr := fun_prop)]

Depends on / 依赖: hf.mul, stronglyMeasurable_const
-/
theorem mul_const [Mul β] [ContinuousMul β] (hf : StronglyMeasurable f) (c : β) :
    StronglyMeasurable fun x => f x * c :=
  hf.mul stronglyMeasurable_const

@[to_additive (attr := fun_prop)]
/--
theorem `const_mul` / 定理 `const_mul`

English:
theorem const_mul
  given: [Mul β] [ContinuousMul β] (hf : StronglyMeasurable f) (c : β)
  proof: stronglyMeasurable_const.mul hf

@[to_additive (attr := to_fun (attr := fun_prop)) const_nsmul]

中文:
定理 const_mul
  条件: [Mul β] [ContinuousMul β] (hf : StronglyMeasurable f) (c : β)
  证明: stronglyMeasurable_const.mul hf

@[to_additive (attr := to_fun (attr := fun_prop)) const_nsmul]

Depends on / 依赖: stronglyMeasurable_const, stronglyMeasurable_const.mul
-/
theorem const_mul [Mul β] [ContinuousMul β] (hf : StronglyMeasurable f) (c : β) :
    StronglyMeasurable fun x => c * f x :=
  stronglyMeasurable_const.mul hf

@[to_additive (attr := to_fun (attr := fun_prop)) const_nsmul]
/--
theorem `pow` / 定理 `pow`

English:
theorem pow
  given: [Monoid β] [ContinuousMul β] (hf : StronglyMeasurable f) (n : Nat)
  proof: ⟨fun k => hf.approx k ^ n, fun x => (hf.tendsto_approx x).pow n⟩

@[to_fun (attr := to_additive (attr := fun_prop))]

中文:
定理 pow
  条件: [Monoid β] [ContinuousMul β] (hf : StronglyMeasurable f) (n : 自然数)
  证明: ⟨fun k => hf.approx k ^ n, fun x => (hf.tendsto_approx x).pow n⟩

@[to_fun (attr := to_additive (attr := fun_prop))]
-/
protected theorem pow [Monoid β] [ContinuousMul β] (hf : StronglyMeasurable f) (n : Nat) :
    StronglyMeasurable (f ^ n) :=
  ⟨fun k => hf.approx k ^ n, fun x => (hf.tendsto_approx x).pow n⟩

@[to_fun (attr := to_additive (attr := fun_prop))]
/--
theorem `inv` / 定理 `inv`

English:
theorem inv
  given: [Inv β] [ContinuousInv β] (hf : StronglyMeasurable f)
  proof: ⟨fun n => (hf.approx n)⁻¹, fun x => (hf.tendsto_approx x).inv⟩

@[to_fun (attr := fun_prop)]

中文:
定理 inv
  条件: [Inv β] [ContinuousInv β] (hf : StronglyMeasurable f)
  证明: ⟨fun n => (hf.approx n)⁻¹, fun x => (hf.tendsto_approx x).inv⟩

@[to_fun (attr := fun_prop)]
-/
protected theorem inv [Inv β] [ContinuousInv β] (hf : StronglyMeasurable f) :
    StronglyMeasurable f⁻¹ :=
  ⟨fun n => (hf.approx n)⁻¹, fun x => (hf.tendsto_approx x).inv⟩

@[to_fun (attr := fun_prop)]
/--
theorem `inv₀` / 定理 `inv₀`

English:
theorem inv₀
  statement: [GroupWithZero β] [ContinuousInv₀ β] [MetrizableSpace β]
  proof: by
  borelize β
  refine ⟨fun n => ((hf.approx n).restrict {x | f x != 0})⁻¹, fun x => ?_⟩
  have : MeasurableSet {x | f x != 0} := ((MeasurableSet.singleton 0).preimage hf.measurable).compl
  by_cases h : f x = 0
  · simp_all only [ne_eq, measurableSet_setOfPred, SimpleFunc.coe_inv, SimpleFunc.coe_

中文:
定理 inv₀
  结论: [GroupWithZero β] [ContinuousInv₀ β] [MetrizableSpace β]
  证明: by
  borelize β
  refine ⟨fun n => ((hf.approx n).restrict {x | f x != 0})⁻¹, fun x => ?_⟩
  have : MeasurableSet {x | f x != 0} := ((MeasurableSet.singleton 0).preimage hf.measurable).compl
  by_cases h : f x = 0
  · simp_all only [ne_eq, measurableSet_setOfPred, SimpleFunc.coe_inv, SimpleFunc.coe_
-/
protected theorem inv₀ [GroupWithZero β] [ContinuousInv₀ β] [MetrizableSpace β]
    (hf : StronglyMeasurable f) : StronglyMeasurable f⁻¹ := by
  borelize β
  refine ⟨fun n => ((hf.approx n).restrict {x | f x != 0})⁻¹, fun x => ?_⟩
  have : MeasurableSet {x | f x != 0} := ((MeasurableSet.singleton 0).preimage hf.measurable).compl
  by_cases h : f x = 0
  · simp_all only [ne_eq, measurableSet_setOfPred, SimpleFunc.coe_inv, SimpleFunc.coe_restrict,
      Pi.inv_apply, mem_ofPred_eq, not_true_eq_false, not_false_eq_true, indicator_of_notMem,
      _root_.inv_zero]
    exact tendsto_const_nhds
  · simp_all only [ne_eq, measurableSet_setOfPred, SimpleFunc.coe_inv, SimpleFunc.coe_restrict,
      Pi.inv_apply, mem_ofPred_eq, not_false_eq_true, indicator_of_mem]
    apply (hf.tendsto_approx x).inv₀ h

@[to_additive (attr := to_fun (attr := fun_prop)) sub]
/--
theorem `div'` / 定理 `div'`

English:
theorem div'
  statement: [Div β] [ContinuousDiv β] (hf : StronglyMeasurable f)
  proof: ⟨fun n => hf.approx n / hg.approx n, fun x => (hf.tendsto_approx x).div' (hg.tendsto_approx x)⟩

@[fun_prop]

中文:
定理 div'
  结论: [Div β] [ContinuousDiv β] (hf : StronglyMeasurable f)
  证明: ⟨fun n => hf.approx n / hg.approx n, fun x => (hf.tendsto_approx x).div' (hg.tendsto_approx x)⟩

@[fun_prop]
-/
protected theorem div' [Div β] [ContinuousDiv β] (hf : StronglyMeasurable f)
    (hg : StronglyMeasurable g) : StronglyMeasurable (f / g) :=
  ⟨fun n => hf.approx n / hg.approx n, fun x => (hf.tendsto_approx x).div' (hg.tendsto_approx x)⟩

@[fun_prop]
/--
theorem `div₀` / 定理 `div₀`

English:
theorem div₀
  statement: [GroupWithZero β] [ContinuousMul β] [ContinuousInv₀ β] (hf : StronglyMeasurable f)
  proof: ⟨fun n => hf.approx n / hg.approx n,
    fun x => (hf.tendsto_approx x).div (hg.tendsto_approx x) (h₀ x)⟩

中文:
定理 div₀
  结论: [GroupWithZero β] [ContinuousMul β] [ContinuousInv₀ β] (hf : StronglyMeasurable f)
  证明: ⟨fun n => hf.approx n / hg.approx n,
    fun x => (hf.tendsto_approx x).div (hg.tendsto_approx x) (h₀ x)⟩

Depends on / 依赖: approx, hf.approx, hf.tendsto_approx, hg.approx, hg.tendsto_approx, tendsto_approx
-/
theorem div₀ [GroupWithZero β] [ContinuousMul β] [ContinuousInv₀ β] (hf : StronglyMeasurable f)
    (hg : StronglyMeasurable g) (h₀ : forall (x : α), g x != 0) : StronglyMeasurable (f / g) :=
  ⟨fun n => hf.approx n / hg.approx n,
    fun x => (hf.tendsto_approx x).div (hg.tendsto_approx x) (h₀ x)⟩

set_option backward.isDefEq.respectTransparency false in
@[fun_prop]
/--
theorem `div` / 定理 `div`

English:
theorem div
  statement: [GroupWithZero β] [ContinuousMul β] [ContinuousInv₀ β] [MetrizableSpace β]
  proof: by
  borelize β
  refine ⟨fun n => hf.approx n / (hg.approx n).restrict {x | g x != 0}, fun x => ?_⟩
  have : MeasurableSet {x | g x != 0} := ((MeasurableSet.singleton 0).preimage hg.measurable).compl
  by_cases h : g x = 0
  · simp_all only [ne_eq, SimpleFunc.coe_div, SimpleFunc.coe_restrict, Pi.di

中文:
定理 div
  结论: [GroupWithZero β] [ContinuousMul β] [ContinuousInv₀ β] [MetrizableSpace β]
  证明: by
  borelize β
  refine ⟨fun n => hf.approx n / (hg.approx n).restrict {x | g x != 0}, fun x => ?_⟩
  have : MeasurableSet {x | g x != 0} := ((MeasurableSet.singleton 0).preimage hg.measurable).compl
  by_cases h : g x = 0
  · simp_all only [ne_eq, SimpleFunc.coe_div, SimpleFunc.coe_restrict, Pi.di

Depends on / 依赖: MeasurableSet, MeasurableSet.singleton, Pi.div_apply, SimpleFunc, SimpleFunc.coe_div, SimpleFunc.coe_restrict, _root_, _root_.div_zero, approx, borelize, coe_div, coe_restrict, div_apply, div_zero, hf.approx, hg.approx, hg.measurable, indicator_of_notMem, measurable, mem_ofPred_eq
-/
theorem div [GroupWithZero β] [ContinuousMul β] [ContinuousInv₀ β] [MetrizableSpace β]
    (hf : StronglyMeasurable f) (hg : StronglyMeasurable g) :
    StronglyMeasurable (f / g) := by
  borelize β
  refine ⟨fun n => hf.approx n / (hg.approx n).restrict {x | g x != 0}, fun x => ?_⟩
  have : MeasurableSet {x | g x != 0} := ((MeasurableSet.singleton 0).preimage hg.measurable).compl
  by_cases h : g x = 0
  · simp_all only [ne_eq, SimpleFunc.coe_div, SimpleFunc.coe_restrict, Pi.div_apply, mem_ofPred_eq,
      not_true_eq_false, not_false_eq_true, indicator_of_notMem, _root_.div_zero]
    exact tendsto_const_nhds
  · simp_all only [ne_eq, SimpleFunc.coe_div, SimpleFunc.coe_restrict,
      Pi.div_apply, mem_ofPred_eq, not_false_eq_true, indicator_of_mem]
    exact (hf.tendsto_approx x).div (hg.tendsto_approx x) h

@[to_additive]
/--
theorem `mul_iff_right` / 定理 `mul_iff_right`

English:
theorem mul_iff_right
  given: [CommGroup β] [IsTopologicalGroup β] (hf : StronglyMeasurable f)
  proof: ⟨fun h => show g = f * g * f⁻¹ by simp only [mul_inv_cancel_comm] ▸ h.mul hf.inv,
    fun h => hf.mul h⟩

@[to_additive]

中文:
定理 mul_iff_right
  条件: [CommGroup β] [IsTopologicalGroup β] (hf : StronglyMeasurable f)
  证明: ⟨fun h => show g = f * g * f⁻¹ by simp only [mul_inv_cancel_comm] ▸ h.mul hf.inv,
    fun h => hf.mul h⟩

@[to_additive]

Depends on / 依赖: h.mul, hf.inv, hf.mul, mul_inv_cancel_comm
-/
theorem mul_iff_right [CommGroup β] [IsTopologicalGroup β] (hf : StronglyMeasurable f) :
    StronglyMeasurable (f * g) ↔ StronglyMeasurable g :=
  ⟨fun h => show g = f * g * f⁻¹ by simp only [mul_inv_cancel_comm] ▸ h.mul hf.inv,
    fun h => hf.mul h⟩

@[to_additive]
/--
theorem `mul_iff_left` / 定理 `mul_iff_left`

English:
theorem mul_iff_left
  given: [CommGroup β] [IsTopologicalGroup β] (hf : StronglyMeasurable f)
  proof: mul_comm g f ▸ mul_iff_right hf

@[to_fun (attr := to_additive (attr := fun_prop))]

中文:
定理 mul_iff_left
  条件: [CommGroup β] [IsTopologicalGroup β] (hf : StronglyMeasurable f)
  证明: mul_comm g f ▸ mul_iff_right hf

@[to_fun (attr := to_additive (attr := fun_prop))]

Depends on / 依赖: mul_comm, mul_iff_right
-/
theorem mul_iff_left [CommGroup β] [IsTopologicalGroup β] (hf : StronglyMeasurable f) :
    StronglyMeasurable (g * f) ↔ StronglyMeasurable g :=
  mul_comm g f ▸ mul_iff_right hf

@[to_fun (attr := to_additive (attr := fun_prop))]
/--
theorem `smul` / 定理 `smul`

English:
theorem smul
  statement: {𝕜} [TopologicalSpace 𝕜] [SMul 𝕜 β] [ContinuousSMul 𝕜 β] {f : α -> 𝕜}
  proof: continuous_smul.comp_stronglyMeasurable (hf.prodMk hg)

@[to_additive (attr := to_fun (attr := fun_prop))]

中文:
定理 smul
  结论: {𝕜} [TopologicalSpace 𝕜] [SMul 𝕜 β] [ContinuousSMul 𝕜 β] {f : α -> 𝕜}
  证明: continuous_smul.comp_stronglyMeasurable (hf.prodMk hg)

@[to_additive (attr := to_fun (attr := fun_prop))]
-/
protected theorem smul {𝕜} [TopologicalSpace 𝕜] [SMul 𝕜 β] [ContinuousSMul 𝕜 β] {f : α -> 𝕜}
    {g : α -> β} (hf : StronglyMeasurable f) (hg : StronglyMeasurable g) :
    StronglyMeasurable (f • g) :=
  continuous_smul.comp_stronglyMeasurable (hf.prodMk hg)

@[to_additive (attr := to_fun (attr := fun_prop))]
/--
theorem `const_smul` / 定理 `const_smul`

English:
theorem const_smul
  statement: {𝕜} [SMul 𝕜 β] [ContinuousConstSMul 𝕜 β] (hf : StronglyMeasurable f)
  proof: ⟨fun n => c • hf.approx n, fun x => (hf.tendsto_approx x).const_smul c⟩

@[deprecated (since := "2026-06-26")]
alias const_smul' := StronglyMeasurable.fun_const_smul

@[deprecated (since := "2026-06-26")]
alias const_vadd' := StronglyMeasurable.fun_const_vadd

@[to_additive (attr := fun_prop)]

中文:
定理 const_smul
  结论: {𝕜} [SMul 𝕜 β] [ContinuousConstSMul 𝕜 β] (hf : StronglyMeasurable f)
  证明: ⟨fun n => c • hf.approx n, fun x => (hf.tendsto_approx x).const_smul c⟩

@[deprecated (since := "2026-06-26")]
alias const_smul' := StronglyMeasurable.fun_const_smul

@[deprecated (since := "2026-06-26")]
alias const_vadd' := StronglyMeasurable.fun_const_vadd

@[to_additive (attr := fun_prop)]
-/
protected theorem const_smul {𝕜} [SMul 𝕜 β] [ContinuousConstSMul 𝕜 β] (hf : StronglyMeasurable f)
    (c : 𝕜) : StronglyMeasurable (c • f) :=
  ⟨fun n => c • hf.approx n, fun x => (hf.tendsto_approx x).const_smul c⟩

@[deprecated (since := "2026-06-26")]
alias const_smul' := StronglyMeasurable.fun_const_smul

@[deprecated (since := "2026-06-26")]
alias const_vadd' := StronglyMeasurable.fun_const_vadd

@[to_additive (attr := fun_prop)]
/--
theorem `smul_const` / 定理 `smul_const`

English:
theorem smul_const
  statement: {𝕜} [TopologicalSpace 𝕜] [SMul 𝕜 β] [ContinuousSMul 𝕜 β] {f : α -> 𝕜}
  proof: continuous_smul.comp_stronglyMeasurable (hf.prodMk stronglyMeasurable_const)

中文:
定理 smul_const
  结论: {𝕜} [TopologicalSpace 𝕜] [SMul 𝕜 β] [ContinuousSMul 𝕜 β] {f : α -> 𝕜}
  证明: continuous_smul.comp_stronglyMeasurable (hf.prodMk stronglyMeasurable_const)
-/
protected theorem smul_const {𝕜} [TopologicalSpace 𝕜] [SMul 𝕜 β] [ContinuousSMul 𝕜 β] {f : α -> 𝕜}
    (hf : StronglyMeasurable f) (c : β) : StronglyMeasurable fun x => f x • c :=
  continuous_smul.comp_stronglyMeasurable (hf.prodMk stronglyMeasurable_const)

/-- Pointwise star on functions induced from continuous star preserves strong measurability. -/
@[fun_prop]
/--
theorem `star` / 定理 `star`

English:
theorem star
  statement: {R : Type*} [MeasurableSpace α] [Star R] [TopologicalSpace R]
  proof: ⟨fun n => star (hf.approx n), fun x => (hf.tendsto_approx x).star⟩

中文:
定理 star
  结论: {R : 类型} [MeasurableSpace α] [Star R] [TopologicalSpace R]
  证明: ⟨fun n => star (hf.approx n), fun x => (hf.tendsto_approx x).star⟩
-/
protected theorem star {R : Type*} [MeasurableSpace α] [Star R] [TopologicalSpace R]
    [ContinuousStar R] (f : α -> R) (hf : StronglyMeasurable f) : StronglyMeasurable (star f) :=
  ⟨fun n => star (hf.approx n), fun x => (hf.tendsto_approx x).star⟩

/--
theorem `_root_.Measurable.add_stronglyMeasurable` / 定理 `_root_.Measurable.add_stronglyMeasurable`

English:
theorem _root_.Measurable.add_stronglyMeasurable
  proof: by
  rcases hf with ⟨φ, hφ⟩
  have : Tendsto (fun n x => g x + φ n x) atTop (𝓝 (g + f)) :=
    tendsto_pi_nhds.2 (fun x => tendsto_const_nhds.add (hφ x))
  apply measurable_of_tendsto_metrizable (fun n => ?_) this
  exact hg.add_simpleFunc _

中文:
定理 _root_.Measurable.add_stronglyMeasurable
  证明: by
  rcases hf with ⟨φ, hφ⟩
  have : Tendsto (fun n x => g x + φ n x) atTop (𝓝 (g + f)) :=
    tendsto_pi_nhds.2 (fun x => tendsto_const_nhds.add (hφ x))
  apply measurable_of_tendsto_metrizable (fun n => ?_) this
  exact hg.add_simpleFunc _

Depends on / 依赖: Tendsto, add_simpleFunc, hg.add_simpleFunc, measurable_of_tendsto_metrizable, tendsto_const_nhds, tendsto_const_nhds.add, tendsto_pi_nhds
-/
theorem _root_.Measurable.add_stronglyMeasurable
    {α E : Type*} {_ : MeasurableSpace α} [AddCancelMonoid E] [TopologicalSpace E]
    [MeasurableSpace E] [BorelSpace E] [ContinuousAdd E] [PseudoMetrizableSpace E]
    {g f : α -> E} (hg : Measurable g) (hf : StronglyMeasurable f) :
    Measurable (g + f) := by
  rcases hf with ⟨φ, hφ⟩
  have : Tendsto (fun n x => g x + φ n x) atTop (𝓝 (g + f)) :=
    tendsto_pi_nhds.2 (fun x => tendsto_const_nhds.add (hφ x))
  apply measurable_of_tendsto_metrizable (fun n => ?_) this
  exact hg.add_simpleFunc _

/--
theorem `_root_.Measurable.sub_stronglyMeasurable` / 定理 `_root_.Measurable.sub_stronglyMeasurable`

English:
theorem _root_.Measurable.sub_stronglyMeasurable
  proof: by
  rw [sub_eq_add_neg]
  exact hg.add_stronglyMeasurable hf.neg

中文:
定理 _root_.Measurable.sub_stronglyMeasurable
  证明: by
  rw [sub_eq_add_neg]
  exact hg.add_stronglyMeasurable hf.neg

Depends on / 依赖: add_stronglyMeasurable, hf.neg, hg.add_stronglyMeasurable, sub_eq_add_neg
-/
theorem _root_.Measurable.sub_stronglyMeasurable
    {α E : Type*} {_ : MeasurableSpace α} [AddGroup E] [TopologicalSpace E]
    [MeasurableSpace E] [BorelSpace E] [ContinuousAdd E] [ContinuousNeg E] [PseudoMetrizableSpace E]
    {g f : α -> E} (hg : Measurable g) (hf : StronglyMeasurable f) :
    Measurable (g - f) := by
  rw [sub_eq_add_neg]
  exact hg.add_stronglyMeasurable hf.neg

/--
theorem `_root_.Measurable.stronglyMeasurable_add` / 定理 `_root_.Measurable.stronglyMeasurable_add`

English:
theorem _root_.Measurable.stronglyMeasurable_add
  proof: by
  rcases hf with ⟨φ, hφ⟩
  have : Tendsto (fun n x => φ n x + g x) atTop (𝓝 (f + g)) :=
    tendsto_pi_nhds.2 (fun x => (hφ x).add tendsto_const_nhds)
  apply measurable_of_tendsto_metrizable (fun n => ?_) this
  exact hg.simpleFunc_add _

中文:
定理 _root_.Measurable.stronglyMeasurable_add
  证明: by
  rcases hf with ⟨φ, hφ⟩
  have : Tendsto (fun n x => φ n x + g x) atTop (𝓝 (f + g)) :=
    tendsto_pi_nhds.2 (fun x => (hφ x).add tendsto_const_nhds)
  apply measurable_of_tendsto_metrizable (fun n => ?_) this
  exact hg.simpleFunc_add _

Depends on / 依赖: Tendsto, hg.simpleFunc_add, measurable_of_tendsto_metrizable, simpleFunc_add, tendsto_const_nhds, tendsto_pi_nhds
-/
theorem _root_.Measurable.stronglyMeasurable_add
    {α E : Type*} {_ : MeasurableSpace α} [AddCancelMonoid E] [TopologicalSpace E]
    [MeasurableSpace E] [BorelSpace E] [ContinuousAdd E] [PseudoMetrizableSpace E]
    {g f : α -> E} (hg : Measurable g) (hf : StronglyMeasurable f) :
    Measurable (f + g) := by
  rcases hf with ⟨φ, hφ⟩
  have : Tendsto (fun n x => φ n x + g x) atTop (𝓝 (f + g)) :=
    tendsto_pi_nhds.2 (fun x => (hφ x).add tendsto_const_nhds)
  apply measurable_of_tendsto_metrizable (fun n => ?_) this
  exact hg.simpleFunc_add _

end Arithmetic

section MulAction

variable {M G G₀ : Type*}
variable [TopologicalSpace β]
variable [Monoid M] [MulAction M β] [ContinuousConstSMul M β]
variable [Group G] [MulAction G β] [ContinuousConstSMul G β]
variable [GroupWithZero G₀] [MulAction G₀ β] [ContinuousConstSMul G₀ β]

/--
theorem `_root_.stronglyMeasurable_const_smul_iff` / 定理 `_root_.stronglyMeasurable_const_smul_iff`

English:
theorem _root_.stronglyMeasurable_const_smul_iff
  given: {m : MeasurableSpace α} (c : G)
  proof: ⟨fun h => by simpa only [inv_smul_smul] using h.fun_const_smul c⁻¹, fun h => h.const_smul c⟩

nonrec theorem _root_.IsUnit.stronglyMeasurable_const_smul_iff {_ : MeasurableSpace α} {c : M}
    (hc : IsUnit c) :
    (StronglyMeasurable fun x => c • f x) ↔ StronglyMeasurable f :=
  let ⟨u, hu⟩ := hc
 

中文:
定理 _root_.stronglyMeasurable_const_smul_iff
  条件: {m : MeasurableSpace α} (c : G)
  证明: ⟨fun h => by simpa only [inv_smul_smul] using h.fun_const_smul c⁻¹, fun h => h.const_smul c⟩

nonrec theorem _root_.IsUnit.stronglyMeasurable_const_smul_iff {_ : MeasurableSpace α} {c : M}
    (hc : IsUnit c) :
    (StronglyMeasurable fun x => c • f x) ↔ StronglyMeasurable f :=
  let ⟨u, hu⟩ := hc
 

Depends on / 依赖: const_smul, fun_const_smul, h.const_smul, h.fun_const_smul, inv_smul_smul
-/
theorem _root_.stronglyMeasurable_const_smul_iff {m : MeasurableSpace α} (c : G) :
    (StronglyMeasurable fun x => c • f x) ↔ StronglyMeasurable f :=
  ⟨fun h => by simpa only [inv_smul_smul] using h.fun_const_smul c⁻¹, fun h => h.const_smul c⟩

nonrec theorem _root_.IsUnit.stronglyMeasurable_const_smul_iff {_ : MeasurableSpace α} {c : M}
    (hc : IsUnit c) :
    (StronglyMeasurable fun x => c • f x) ↔ StronglyMeasurable f :=
  let ⟨u, hu⟩ := hc
  hu ▸ stronglyMeasurable_const_smul_iff u

/--
theorem `_root_.stronglyMeasurable_const_smul_iff₀` / 定理 `_root_.stronglyMeasurable_const_smul_iff₀`

English:
theorem _root_.stronglyMeasurable_const_smul_iff₀
  given: {_ : MeasurableSpace α} {c : G₀} (hc : c != 0)
  proof: (IsUnit.mk0 _ hc).stronglyMeasurable_const_smul_iff

中文:
定理 _root_.stronglyMeasurable_const_smul_iff₀
  条件: {_ : MeasurableSpace α} {c : G₀} (hc : c != 0)
  证明: (IsUnit.mk0 _ hc).stronglyMeasurable_const_smul_iff

Depends on / 依赖: IsUnit, IsUnit.mk0, stronglyMeasurable_const_smul_iff
-/
theorem _root_.stronglyMeasurable_const_smul_iff₀ {_ : MeasurableSpace α} {c : G₀} (hc : c != 0) :
    (StronglyMeasurable fun x => c • f x) ↔ StronglyMeasurable f :=
  (IsUnit.mk0 _ hc).stronglyMeasurable_const_smul_iff

end MulAction

section Order

variable [MeasurableSpace α] [TopologicalSpace β]

open Filter

@[to_fun (attr := fun_prop)]
/--
theorem `sup` / 定理 `sup`

English:
theorem sup
  statement: [Max β] [ContinuousSup β] (hf : StronglyMeasurable f)
  proof: ⟨fun n => hf.approx n ⊔ hg.approx n, fun x =>
    (hf.tendsto_approx x).sup_nhds (hg.tendsto_approx x)⟩

@[to_fun (attr := fun_prop)]

中文:
定理 sup
  结论: [Max β] [ContinuousSup β] (hf : StronglyMeasurable f)
  证明: ⟨fun n => hf.approx n ⊔ hg.approx n, fun x =>
    (hf.tendsto_approx x).sup_nhds (hg.tendsto_approx x)⟩

@[to_fun (attr := fun_prop)]
-/
protected theorem sup [Max β] [ContinuousSup β] (hf : StronglyMeasurable f)
    (hg : StronglyMeasurable g) : StronglyMeasurable (f ⊔ g) :=
  ⟨fun n => hf.approx n ⊔ hg.approx n, fun x =>
    (hf.tendsto_approx x).sup_nhds (hg.tendsto_approx x)⟩

@[to_fun (attr := fun_prop)]
/--
theorem `inf` / 定理 `inf`

English:
theorem inf
  statement: [Min β] [ContinuousInf β] (hf : StronglyMeasurable f)
  proof: ⟨fun n => hf.approx n ⊓ hg.approx n, fun x =>
    (hf.tendsto_approx x).inf_nhds (hg.tendsto_approx x)⟩

@[to_additive (attr := fun_prop)]

中文:
定理 inf
  结论: [Min β] [ContinuousInf β] (hf : StronglyMeasurable f)
  证明: ⟨fun n => hf.approx n ⊓ hg.approx n, fun x =>
    (hf.tendsto_approx x).inf_nhds (hg.tendsto_approx x)⟩

@[to_additive (attr := fun_prop)]
-/
protected theorem inf [Min β] [ContinuousInf β] (hf : StronglyMeasurable f)
    (hg : StronglyMeasurable g) : StronglyMeasurable (f ⊓ g) :=
  ⟨fun n => hf.approx n ⊓ hg.approx n, fun x =>
    (hf.tendsto_approx x).inf_nhds (hg.tendsto_approx x)⟩

@[to_additive (attr := fun_prop)]
/--
theorem `oneLePart` / 定理 `oneLePart`

English:
theorem oneLePart
  given: [Group β] [Lattice β] [ContinuousSup β] (hf : StronglyMeasurable f)
  proof: hf.sup stronglyMeasurable_const

@[to_additive (attr := fun_prop)]

中文:
定理 oneLePart
  条件: [Group β] [Lattice β] [ContinuousSup β] (hf : StronglyMeasurable f)
  证明: hf.sup stronglyMeasurable_const

@[to_additive (attr := fun_prop)]
-/
protected theorem oneLePart [Group β] [Lattice β] [ContinuousSup β] (hf : StronglyMeasurable f) :
    StronglyMeasurable fun x => oneLePart (f x) :=
  hf.sup stronglyMeasurable_const

@[to_additive (attr := fun_prop)]
/--
theorem `leOnePart` / 定理 `leOnePart`

English:
theorem leOnePart
  statement: [Group β] [Lattice β] [ContinuousSup β] [ContinuousInv β]
  proof: hf.inv.sup stronglyMeasurable_const

中文:
定理 leOnePart
  结论: [Group β] [Lattice β] [ContinuousSup β] [ContinuousInv β]
  证明: hf.inv.sup stronglyMeasurable_const
-/
protected theorem leOnePart [Group β] [Lattice β] [ContinuousSup β] [ContinuousInv β]
    (hf : StronglyMeasurable f) :
    StronglyMeasurable fun x => leOnePart (f x) :=
  hf.inv.sup stronglyMeasurable_const

end Order

/-!
### Big operators: `∏` and `∑`
-/


section Monoid

variable {M : Type*} [Monoid M] [TopologicalSpace M] [ContinuousMul M] {m : MeasurableSpace α}

-- TODO: `fun_prop` cannot use lemmas with a condition quantifying over the function
@[to_additive (attr := fun_prop)]
/--
theorem `_root_.List.stronglyMeasurable_prod` / 定理 `_root_.List.stronglyMeasurable_prod`

English:
theorem _root_.List.stronglyMeasurable_prod
  statement: (l : List (α -> M))
  proof: by
  induction l with
  | nil => exact stronglyMeasurable_one
  | cons f l ihl =>
    rw [List.forall_mem_cons] at hl
    rw [List.prod_cons]
    exact hl.1.mul (ihl hl.2)

@[to_additive (attr := fun_prop)]

中文:
定理 _root_.List.stronglyMeasurable_prod
  结论: (l : List (α -> M))
  证明: by
  induction l with
  | nil => exact stronglyMeasurable_one
  | cons f l ihl =>
    rw [List.forall_mem_cons] at hl
    rw [List.prod_cons]
    exact hl.1.mul (ihl hl.2)

@[to_additive (attr := fun_prop)]

Depends on / 依赖: List.forall_mem_cons, List.prod_cons, forall_mem_cons, prod_cons, stronglyMeasurable_one
-/
theorem _root_.List.stronglyMeasurable_prod (l : List (α -> M))
    (hl : forall f in l, StronglyMeasurable f) : StronglyMeasurable l.prod := by
  induction l with
  | nil => exact stronglyMeasurable_one
  | cons f l ihl =>
    rw [List.forall_mem_cons] at hl
    rw [List.prod_cons]
    exact hl.1.mul (ihl hl.2)

@[to_additive (attr := fun_prop)]
/--
theorem `_root_.List.stronglyMeasurable_fun_prod` / 定理 `_root_.List.stronglyMeasurable_fun_prod`

English:
theorem _root_.List.stronglyMeasurable_fun_prod
  statement: (l : List (α -> M))
  proof: by
  simpa only [← Pi.list_prod_apply] using l.stronglyMeasurable_prod hl

中文:
定理 _root_.List.stronglyMeasurable_fun_prod
  结论: (l : List (α -> M))
  证明: by
  simpa only [← Pi.list_prod_apply] using l.stronglyMeasurable_prod hl

Depends on / 依赖: Pi.list_prod_apply, l.stronglyMeasurable_prod, list_prod_apply, stronglyMeasurable_prod
-/
theorem _root_.List.stronglyMeasurable_fun_prod (l : List (α -> M))
    (hl : forall f in l, StronglyMeasurable f) :
    StronglyMeasurable fun x => (l.map fun f : α -> M => f x).prod := by
  simpa only [← Pi.list_prod_apply] using l.stronglyMeasurable_prod hl

end Monoid

section CommMonoid

variable {M : Type*} [CommMonoid M] [TopologicalSpace M] [ContinuousMul M] {m : MeasurableSpace α}


@[to_additive (attr := fun_prop)]
/--
theorem `_root_.Multiset.stronglyMeasurable_prod` / 定理 `_root_.Multiset.stronglyMeasurable_prod`

English:
theorem _root_.Multiset.stronglyMeasurable_prod
  statement: (l : Multiset (α -> M))
  proof: by
  rcases l with ⟨l⟩
  simpa using l.stronglyMeasurable_prod (by simpa using hl)

@[to_additive (attr := fun_prop)]

中文:
定理 _root_.Multiset.stronglyMeasurable_prod
  结论: (l : Multiset (α -> M))
  证明: by
  rcases l with ⟨l⟩
  simpa using l.stronglyMeasurable_prod (by simpa using hl)

@[to_additive (attr := fun_prop)]

Depends on / 依赖: l.stronglyMeasurable_prod, stronglyMeasurable_prod
-/
theorem _root_.Multiset.stronglyMeasurable_prod (l : Multiset (α -> M))
    (hl : forall f in l, StronglyMeasurable f) : StronglyMeasurable l.prod := by
  rcases l with ⟨l⟩
  simpa using l.stronglyMeasurable_prod (by simpa using hl)

@[to_additive (attr := fun_prop)]
/--
theorem `_root_.Multiset.stronglyMeasurable_fun_prod` / 定理 `_root_.Multiset.stronglyMeasurable_fun_prod`

English:
theorem _root_.Multiset.stronglyMeasurable_fun_prod
  statement: (s : Multiset (α -> M))
  proof: by
  simpa only [← Pi.multiset_prod_apply] using s.stronglyMeasurable_prod hs

@[to_additive (attr := fun_prop)]

中文:
定理 _root_.Multiset.stronglyMeasurable_fun_prod
  结论: (s : Multiset (α -> M))
  证明: by
  simpa only [← Pi.multiset_prod_apply] using s.stronglyMeasurable_prod hs

@[to_additive (attr := fun_prop)]

Depends on / 依赖: Pi.multiset_prod_apply, multiset_prod_apply, s.stronglyMeasurable_prod, stronglyMeasurable_prod
-/
theorem _root_.Multiset.stronglyMeasurable_fun_prod (s : Multiset (α -> M))
    (hs : forall f in s, StronglyMeasurable f) :
    StronglyMeasurable fun x => (s.map fun f : α -> M => f x).prod := by
  simpa only [← Pi.multiset_prod_apply] using s.stronglyMeasurable_prod hs

@[to_additive (attr := fun_prop)]
/--
theorem `_root_.Finset.stronglyMeasurable_prod` / 定理 `_root_.Finset.stronglyMeasurable_prod`

English:
theorem _root_.Finset.stronglyMeasurable_prod
  statement: {ι : Type*} {f : ι -> α -> M} (s : Finset ι)
  proof: Finset.prod_induction _ _ (fun _a _b ha hb => ha.mul hb) (@stronglyMeasurable_one α M _ _ _) hf

@[to_additive (attr := fun_prop)]

中文:
定理 _root_.Finset.stronglyMeasurable_prod
  结论: {ι : 类型} {f : ι -> α -> M} (s : Finset ι)
  证明: Finset.prod_induction _ _ (fun _a _b ha hb => ha.mul hb) (@stronglyMeasurable_one α M _ _ _) hf

@[to_additive (attr := fun_prop)]

Depends on / 依赖: Finset, Finset.prod_induction, ha.mul, prod_induction, stronglyMeasurable_one
-/
theorem _root_.Finset.stronglyMeasurable_prod {ι : Type*} {f : ι -> α -> M} (s : Finset ι)
    (hf : forall i in s, StronglyMeasurable (f i)) : StronglyMeasurable (∏ i in s, f i) :=
  Finset.prod_induction _ _ (fun _a _b ha hb => ha.mul hb) (@stronglyMeasurable_one α M _ _ _) hf

@[to_additive (attr := fun_prop)]
/--
theorem `_root_.Finset.stronglyMeasurable_fun_prod` / 定理 `_root_.Finset.stronglyMeasurable_fun_prod`

English:
theorem _root_.Finset.stronglyMeasurable_fun_prod
  statement: {ι : Type*} {f : ι -> α -> M} (s : Finset ι)
  proof: by
  simpa only [← Finset.prod_apply] using s.stronglyMeasurable_prod hf

中文:
定理 _root_.Finset.stronglyMeasurable_fun_prod
  结论: {ι : 类型} {f : ι -> α -> M} (s : Finset ι)
  证明: by
  simpa only [← Finset.prod_apply] using s.stronglyMeasurable_prod hf

Depends on / 依赖: Finset, Finset.prod_apply, prod_apply, s.stronglyMeasurable_prod, stronglyMeasurable_prod
-/
theorem _root_.Finset.stronglyMeasurable_fun_prod {ι : Type*} {f : ι -> α -> M} (s : Finset ι)
    (hf : forall i in s, StronglyMeasurable (f i)) : StronglyMeasurable fun a => ∏ i in s, f i a := by
  simpa only [← Finset.prod_apply] using s.stronglyMeasurable_prod hf

variable {n : MeasurableSpace β} in
/-- Compositional version of `Finset.stronglyMeasurable_prod` for use by `fun_prop`. -/
@[to_additive (attr := fun_prop)
/-- Compositional version of `Finset.stronglyMeasurable_sum` for use by `fun_prop`. -/]
/--
lemma `Finset.stronglyMeasurable_prod_apply` / 引理 `Finset.stronglyMeasurable_prod_apply`

English:
lemma Finset.stronglyMeasurable_prod_apply
  statement: {ι : Type*} {f : ι -> α -> β -> M} {g : α -> β}
  proof: by
  simp only [Finset.prod_apply]; fun_prop

中文:
引理 Finset.stronglyMeasurable_prod_apply
  结论: {ι : 类型} {f : ι -> α -> β -> M} {g : α -> β}
  证明: by
  simp only [Finset.prod_apply]; fun_prop

Depends on / 依赖: Finset, Finset.prod_apply, fun_prop, prod_apply
-/
lemma Finset.stronglyMeasurable_prod_apply {ι : Type*} {f : ι -> α -> β -> M} {g : α -> β}
    {s : Finset ι} (hf : forall i in s, StronglyMeasurable ↿(f i)) (hg : Measurable g) :
    StronglyMeasurable fun a => (∏ i in s, f i a) (g a) := by
  simp only [Finset.prod_apply]; fun_prop

end CommMonoid

/--
theorem `isSeparable_range` / 定理 `isSeparable_range`

English:
theorem isSeparable_range
  statement: {m : MeasurableSpace α} [TopologicalSpace β]
  proof: by
  have : IsSeparable (closure (⋃ n, range (hf.approx n))) :=
.closure .iUnion fun n => (hf.approx n).finite_range.isSeparable
  apply this.mono
  rintro _ ⟨x, rfl⟩
  apply mem_closure_of_tendsto (hf.tendsto_approx x)
  filter_upwards with n
  apply mem_iUnion_of_mem n
  exact mem_range_self _

中文:
定理 isSeparable_range
  结论: {m : MeasurableSpace α} [TopologicalSpace β]
  证明: by
  have : IsSeparable (closure (⋃ n, range (hf.approx n))) :=
.closure .iUnion fun n => (hf.approx n).finite_range.isSeparable
  apply this.mono
  rintro _ ⟨x, rfl⟩
  apply mem_closure_of_tendsto (hf.tendsto_approx x)
  filter_upwards with n
  apply mem_iUnion_of_mem n
  exact mem_range_self _
-/
protected theorem isSeparable_range {m : MeasurableSpace α} [TopologicalSpace β]
    (hf : StronglyMeasurable f) : TopologicalSpace.IsSeparable (range f) := by
  have : IsSeparable (closure (⋃ n, range (hf.approx n))) :=
.closure .iUnion fun n => (hf.approx n).finite_range.isSeparable
  apply this.mono
  rintro _ ⟨x, rfl⟩
  apply mem_closure_of_tendsto (hf.tendsto_approx x)
  filter_upwards with n
  apply mem_iUnion_of_mem n
  exact mem_range_self _

/--
theorem `separableSpace_range_union_singleton` / 定理 `separableSpace_range_union_singleton`

English:
theorem separableSpace_range_union_singleton
  statement: {_ : MeasurableSpace α} [TopologicalSpace β]
  proof: letI := pseudoMetrizableSpacePseudoMetric β
  (hf.isSeparable_range.union (finite_singleton _).isSeparable).separableSpace

中文:
定理 separableSpace_range_union_singleton
  结论: {_ : MeasurableSpace α} [TopologicalSpace β]
  证明: letI := pseudoMetrizableSpacePseudoMetric β
  (hf.isSeparable_range.union (finite_singleton _).isSeparable).separableSpace

Depends on / 依赖: finite_singleton, hf.isSeparable_range.union, isSeparable, isSeparable_range, pseudoMetrizableSpacePseudoMetric, separableSpace
-/
theorem separableSpace_range_union_singleton {_ : MeasurableSpace α} [TopologicalSpace β]
    [PseudoMetrizableSpace β] (hf : StronglyMeasurable f) {b : β} :
    SeparableSpace (range f union {b} : Set β) :=
  letI := pseudoMetrizableSpacePseudoMetric β
  (hf.isSeparable_range.union (finite_singleton _).isSeparable).separableSpace

section SecondCountableStronglyMeasurable

variable {mα : MeasurableSpace α} [MeasurableSpace β]

/-- In a space with second countable topology, measurable implies strongly measurable. -/
@[fun_prop]
/--
theorem `_root_.Measurable.stronglyMeasurable` / 定理 `_root_.Measurable.stronglyMeasurable`

English:
theorem _root_.Measurable.stronglyMeasurable
  statement: [TopologicalSpace β] [PseudoMetrizableSpace β]
  proof: by
  let := pseudoMetrizableSpacePseudoMetric β
  nontriviality β; inhabit β
  exact ⟨SimpleFunc.approxOn f hf Set.univ default (Set.mem_univ _), fun x =>
    SimpleFunc.tendsto_approxOn hf (Set.mem_univ _) (by simp)⟩

中文:
定理 _root_.Measurable.stronglyMeasurable
  结论: [TopologicalSpace β] [PseudoMetrizableSpace β]
  证明: by
  let := pseudoMetrizableSpacePseudoMetric β
  nontriviality β; inhabit β
  exact ⟨SimpleFunc.approxOn f hf Set.univ default (Set.mem_univ _), fun x =>
    SimpleFunc.tendsto_approxOn hf (Set.mem_univ _) (by simp)⟩

Depends on / 依赖: Set.mem_univ, Set.univ, SimpleFunc, SimpleFunc.approxOn, SimpleFunc.tendsto_approxOn, approxOn, inhabit, mem_univ, nontriviality, pseudoMetrizableSpacePseudoMetric, tendsto_approxOn
-/
theorem _root_.Measurable.stronglyMeasurable [TopologicalSpace β] [PseudoMetrizableSpace β]
    [SecondCountableTopology β] [OpensMeasurableSpace β] (hf : Measurable f) :
    StronglyMeasurable f := by
  let := pseudoMetrizableSpacePseudoMetric β
  nontriviality β; inhabit β
  exact ⟨SimpleFunc.approxOn f hf Set.univ default (Set.mem_univ _), fun x =>
    SimpleFunc.tendsto_approxOn hf (Set.mem_univ _) (by simp)⟩

/--
theorem `_root_.stronglyMeasurable_iff_measurable` / 定理 `_root_.stronglyMeasurable_iff_measurable`

English:
theorem _root_.stronglyMeasurable_iff_measurable
  statement: [TopologicalSpace β] [PseudoMetrizableSpace β]
  proof: ⟨fun h => h.measurable, fun h => Measurable.stronglyMeasurable h⟩

@[fun_prop]

中文:
定理 _root_.stronglyMeasurable_iff_measurable
  结论: [TopologicalSpace β] [PseudoMetrizableSpace β]
  证明: ⟨fun h => h.measurable, fun h => Measurable.stronglyMeasurable h⟩

@[fun_prop]

Depends on / 依赖: Measurable, Measurable.stronglyMeasurable, h.measurable, measurable, stronglyMeasurable
-/
theorem _root_.stronglyMeasurable_iff_measurable [TopologicalSpace β] [PseudoMetrizableSpace β]
    [BorelSpace β] [SecondCountableTopology β] : StronglyMeasurable f ↔ Measurable f :=
  ⟨fun h => h.measurable, fun h => Measurable.stronglyMeasurable h⟩

@[fun_prop]
/--
theorem `_root_.stronglyMeasurable_id` / 定理 `_root_.stronglyMeasurable_id`

English:
theorem _root_.stronglyMeasurable_id
  statement: [TopologicalSpace α] [PseudoMetrizableSpace α]
  proof: measurable_id.stronglyMeasurable

中文:
定理 _root_.stronglyMeasurable_id
  结论: [TopologicalSpace α] [PseudoMetrizableSpace α]
  证明: measurable_id.stronglyMeasurable

Depends on / 依赖: measurable_id, measurable_id.stronglyMeasurable, stronglyMeasurable
-/
theorem _root_.stronglyMeasurable_id [TopologicalSpace α] [PseudoMetrizableSpace α]
    [OpensMeasurableSpace α] [SecondCountableTopology α] : StronglyMeasurable (id : α -> α) :=
  measurable_id.stronglyMeasurable

end SecondCountableStronglyMeasurable

/--
theorem `_root_.stronglyMeasurable_iff_measurable_separable` / 定理 `_root_.stronglyMeasurable_iff_measurable_separable`

English:
theorem _root_.stronglyMeasurable_iff_measurable_separable
  statement: {m : MeasurableSpace α}
  proof: by
  refine ⟨fun H => ⟨H.measurable, H.isSeparable_range⟩, fun ⟨Hm, Hsep⟩ => ?_⟩
  have := Hsep.secondCountableTopology
  have Hm' : StronglyMeasurable (rangeFactorization f) := Hm.subtype_mk.stronglyMeasurable
  exact continuous_subtype_val.comp_stronglyMeasurable Hm'

中文:
定理 _root_.stronglyMeasurable_iff_measurable_separable
  结论: {m : MeasurableSpace α}
  证明: by
  refine ⟨fun H => ⟨H.measurable, H.isSeparable_range⟩, fun ⟨Hm, Hsep⟩ => ?_⟩
  have := Hsep.secondCountableTopology
  have Hm' : StronglyMeasurable (rangeFactorization f) := Hm.subtype_mk.stronglyMeasurable
  exact continuous_subtype_val.comp_stronglyMeasurable Hm'

Depends on / 依赖: H.isSeparable_range, H.measurable, Hm.subtype_mk.stronglyMeasurable, Hsep.secondCountableTopology, StronglyMeasurable, comp_stronglyMeasurable, continuous_subtype_val, continuous_subtype_val.comp_stronglyMeasurable, isSeparable_range, measurable, rangeFactorization, secondCountableTopology, stronglyMeasurable, subtype_mk
-/
theorem _root_.stronglyMeasurable_iff_measurable_separable {m : MeasurableSpace α}
    [TopologicalSpace β] [PseudoMetrizableSpace β] [MeasurableSpace β] [BorelSpace β] :
    StronglyMeasurable f ↔ Measurable f ∧ IsSeparable (range f) := by
  refine ⟨fun H => ⟨H.measurable, H.isSeparable_range⟩, fun ⟨Hm, Hsep⟩ => ?_⟩
  have := Hsep.secondCountableTopology
  have Hm' : StronglyMeasurable (rangeFactorization f) := Hm.subtype_mk.stronglyMeasurable
  exact continuous_subtype_val.comp_stronglyMeasurable Hm'

/--
theorem `_root_.Continuous.stronglyMeasurable` / 定理 `_root_.Continuous.stronglyMeasurable`

English:
theorem _root_.Continuous.stronglyMeasurable
  statement: [MeasurableSpace α] [TopologicalSpace α]
  proof: by
  borelize β
  cases h.out
  · rw [stronglyMeasurable_iff_measurable_separable]
    refine ⟨hf.measurable, ?_⟩
    exact isSeparable_range hf
  · exact hf.measurable.stronglyMeasurable

中文:
定理 _root_.Continuous.stronglyMeasurable
  结论: [MeasurableSpace α] [TopologicalSpace α]
  证明: by
  borelize β
  cases h.out
  · rw [stronglyMeasurable_iff_measurable_separable]
    refine ⟨hf.measurable, ?_⟩
    exact isSeparable_range hf
  · exact hf.measurable.stronglyMeasurable

Depends on / 依赖: borelize, h.out, hf.measurable, hf.measurable.stronglyMeasurable, isSeparable_range, measurable, stronglyMeasurable, stronglyMeasurable_iff_measurable_separable
-/
theorem _root_.Continuous.stronglyMeasurable [MeasurableSpace α] [TopologicalSpace α]
    [OpensMeasurableSpace α] [TopologicalSpace β] [PseudoMetrizableSpace β]
    [h : SecondCountableTopologyEither α β] {f : α -> β} (hf : Continuous f) :
    StronglyMeasurable f := by
  borelize β
  cases h.out
  · rw [stronglyMeasurable_iff_measurable_separable]
    refine ⟨hf.measurable, ?_⟩
    exact isSeparable_range hf
  · exact hf.measurable.stronglyMeasurable

/-- A continuous function whose support is contained in a compact set is strongly measurable. -/
@[to_additive /-- A continuous function whose support is contained in a compact set is strongly
measurable. -/]
/--
theorem `_root_.Continuous.stronglyMeasurable_of_mulSupport_subset_isCompact` / 定理 `_root_.Continuous.stronglyMeasurable_of_mulSupport_subset_isCompact`

English:
theorem _root_.Continuous.stronglyMeasurable_of_mulSupport_subset_isCompact
  proof: by
  borelize β
  let : PseudoMetricSpace β := pseudoMetrizableSpacePseudoMetric β
  rw [stronglyMeasurable_iff_measurable_separable]
  exact ⟨hf.measurable, (isCompact_range_of_mulSupport_subset_isCompact hf hk h'f).isSeparable⟩

中文:
定理 _root_.Continuous.stronglyMeasurable_of_mulSupport_subset_isCompact
  证明: by
  borelize β
  let : PseudoMetricSpace β := pseudoMetrizableSpacePseudoMetric β
  rw [stronglyMeasurable_iff_measurable_separable]
  exact ⟨hf.measurable, (isCompact_range_of_mulSupport_subset_isCompact hf hk h'f).isSeparable⟩

Depends on / 依赖: PseudoMetricSpace, borelize, hf.measurable, isCompact_range_of_mulSupport_subset_isCompact, isSeparable, measurable, pseudoMetrizableSpacePseudoMetric, stronglyMeasurable_iff_measurable_separable
-/
theorem _root_.Continuous.stronglyMeasurable_of_mulSupport_subset_isCompact
    [MeasurableSpace α] [TopologicalSpace α] [OpensMeasurableSpace α] [TopologicalSpace β]
    [PseudoMetrizableSpace β] [One β] {f : α -> β} (hf : Continuous f) {k : Set α}
    (hk : IsCompact k) (h'f : mulSupport f subseteq k) : StronglyMeasurable f := by
  borelize β
  let : PseudoMetricSpace β := pseudoMetrizableSpacePseudoMetric β
  rw [stronglyMeasurable_iff_measurable_separable]
  exact ⟨hf.measurable, (isCompact_range_of_mulSupport_subset_isCompact hf hk h'f).isSeparable⟩

/-- A continuous function with compact support is strongly measurable. -/
@[to_additive /-- A continuous function with compact support is strongly measurable. -/]
/--
theorem `_root_.Continuous.stronglyMeasurable_of_hasCompactMulSupport` / 定理 `_root_.Continuous.stronglyMeasurable_of_hasCompactMulSupport`

English:
theorem _root_.Continuous.stronglyMeasurable_of_hasCompactMulSupport
  proof: hf.stronglyMeasurable_of_mulSupport_subset_isCompact h'f (subset_mulTSupport f)

中文:
定理 _root_.Continuous.stronglyMeasurable_of_hasCompactMulSupport
  证明: hf.stronglyMeasurable_of_mulSupport_subset_isCompact h'f (subset_mulTSupport f)

Depends on / 依赖: hf.stronglyMeasurable_of_mulSupport_subset_isCompact, stronglyMeasurable_of_mulSupport_subset_isCompact, subset_mulTSupport
-/
theorem _root_.Continuous.stronglyMeasurable_of_hasCompactMulSupport
    [MeasurableSpace α] [TopologicalSpace α] [OpensMeasurableSpace α] [TopologicalSpace β]
    [PseudoMetrizableSpace β] [One β] {f : α -> β} (hf : Continuous f)
    (h'f : HasCompactMulSupport f) : StronglyMeasurable f :=
  hf.stronglyMeasurable_of_mulSupport_subset_isCompact h'f (subset_mulTSupport f)

/--
lemma `_root_.HasCompactSupport.stronglyMeasurable_of_prod` / 引理 `_root_.HasCompactSupport.stronglyMeasurable_of_prod`

English:
lemma _root_.HasCompactSupport.stronglyMeasurable_of_prod
  statement: {X Y : Type*} [Zero α]
  proof: by
  borelize α
  apply stronglyMeasurable_iff_measurable_separable.2 ⟨h'f.measurable_of_prod hf, ?_⟩
  let : PseudoMetricSpace α := pseudoMetrizableSpacePseudoMetric α
  exact IsCompact.isSeparable (s := range f) (h'f.isCompact_range hf)

中文:
引理 _root_.HasCompactSupport.stronglyMeasurable_of_prod
  结论: {X Y : 类型} [Zero α]
  证明: by
  borelize α
  apply stronglyMeasurable_iff_measurable_separable.2 ⟨h'f.measurable_of_prod hf, ?_⟩
  let : PseudoMetricSpace α := pseudoMetrizableSpacePseudoMetric α
  exact IsCompact.isSeparable (s := range f) (h'f.isCompact_range hf)

Depends on / 依赖: IsCompact, IsCompact.isSeparable, PseudoMetricSpace, borelize, f.isCompact_range, f.measurable_of_prod, isCompact_range, isSeparable, measurable_of_prod, pseudoMetrizableSpacePseudoMetric, stronglyMeasurable_iff_measurable_separable
-/
lemma _root_.HasCompactSupport.stronglyMeasurable_of_prod {X Y : Type*} [Zero α]
    [TopologicalSpace X] [TopologicalSpace Y] [MeasurableSpace X] [MeasurableSpace Y]
    [OpensMeasurableSpace X] [OpensMeasurableSpace Y] [TopologicalSpace α] [PseudoMetrizableSpace α]
    {f : X × Y -> α} (hf : Continuous f) (h'f : HasCompactSupport f) :
    StronglyMeasurable f := by
  borelize α
  apply stronglyMeasurable_iff_measurable_separable.2 ⟨h'f.measurable_of_prod hf, ?_⟩
  let : PseudoMetricSpace α := pseudoMetrizableSpacePseudoMetric α
  exact IsCompact.isSeparable (s := range f) (h'f.isCompact_range hf)

/--
theorem `_root_.Embedding.comp_stronglyMeasurable_iff` / 定理 `_root_.Embedding.comp_stronglyMeasurable_iff`

English:
theorem _root_.Embedding.comp_stronglyMeasurable_iff
  statement: {m : MeasurableSpace α} [TopologicalSpace β]
  proof: by
  let := pseudoMetrizableSpacePseudoMetric γ
  borelize β γ
  refine
    ⟨fun H => stronglyMeasurable_iff_measurable_separable.2 ⟨?_, ?_⟩, fun H =>
      hg.continuous.comp_stronglyMeasurable H⟩
  · let G : β -> range g := rangeFactorization g
    have hG : IsClosedEmbedding G :=
      { hg.codRe

中文:
定理 _root_.Embedding.comp_stronglyMeasurable_iff
  结论: {m : MeasurableSpace α} [TopologicalSpace β]
  证明: by
  let := pseudoMetrizableSpacePseudoMetric γ
  borelize β γ
  refine
    ⟨fun H => stronglyMeasurable_iff_measurable_separable.2 ⟨?_, ?_⟩, fun H =>
      hg.continuous.comp_stronglyMeasurable H⟩
  · let G : β -> range g := rangeFactorization g
    have hG : IsClosedEmbedding G :=
      { hg.codRe

Depends on / 依赖: H.measurable, IsClosedEmbedding, Measurable, Measurable.subtype_mk, borelize, codRestrict, comp_stronglyMeasurable, continuous, hG.measurableEmbedding.measurable_comp_iff, hg.codRestrict, hg.continuous.comp_stronglyMeasurable, isClosed_range, isClosed_univ, measurable, measurableEmbedding, measurable_comp_iff, pseudoMetrizableSpacePseudoMetric, rangeFactorization, rangeFactorization_surjective, rangeFactorization_surjective.range_eq
-/
theorem _root_.Embedding.comp_stronglyMeasurable_iff {m : MeasurableSpace α} [TopologicalSpace β]
    [PseudoMetrizableSpace β] [TopologicalSpace γ] [PseudoMetrizableSpace γ] {g : β -> γ} {f : α -> β}
    (hg : IsEmbedding g) : (StronglyMeasurable fun x => g (f x)) ↔ StronglyMeasurable f := by
  let := pseudoMetrizableSpacePseudoMetric γ
  borelize β γ
  refine
    ⟨fun H => stronglyMeasurable_iff_measurable_separable.2 ⟨?_, ?_⟩, fun H =>
      hg.continuous.comp_stronglyMeasurable H⟩
  · let G : β -> range g := rangeFactorization g
    have hG : IsClosedEmbedding G :=
      { hg.codRestrict _ _ with
        isClosed_range := by
          rw [rangeFactorization_surjective.range_eq]
          exact isClosed_univ }
    have : Measurable (G ∘ f) := Measurable.subtype_mk H.measurable
    exact hG.measurableEmbedding.measurable_comp_iff.1 this
  · have : IsSeparable (g ⁻¹' range (g ∘ f)) := hg.isSeparable_preimage H.isSeparable_range
    rwa [range_comp, hg.injective.preimage_image] at this

/--
theorem `_root_.stronglyMeasurable_of_tendsto` / 定理 `_root_.stronglyMeasurable_of_tendsto`

English:
theorem _root_.stronglyMeasurable_of_tendsto
  statement: {ι : Type*} {m : MeasurableSpace α}
  proof: by
  borelize β
  refine stronglyMeasurable_iff_measurable_separable.2 ⟨?_, ?_⟩
  · exact measurable_of_tendsto_metrizable' u (fun i => (hf i).measurable) lim
  · rcases u.exists_seq_tendsto with ⟨v, hv⟩
    have : IsSeparable (closure (⋃ i, range (f (v i)))) :=
.closure .iUnion fun i => (hf (v i)).

中文:
定理 _root_.stronglyMeasurable_of_tendsto
  结论: {ι : 类型} {m : MeasurableSpace α}
  证明: by
  borelize β
  refine stronglyMeasurable_iff_measurable_separable.2 ⟨?_, ?_⟩
  · exact measurable_of_tendsto_metrizable' u (fun i => (hf i).measurable) lim
  · rcases u.exists_seq_tendsto with ⟨v, hv⟩
    have : IsSeparable (closure (⋃ i, range (f (v i)))) :=
.closure .iUnion fun i => (hf (v i)).

Depends on / 依赖: IsSeparable, borelize, closure, exists_seq_tendsto, filter_upwards, iUnion, isSeparable_range, measurable, measurable_of_tendsto_metrizable, mem_closure_of_tendsto, mem_iUnion_of_mem, mem_range_self, stronglyMeasurable_iff_measurable_separable, tendsto_pi_nhds, this.mono, u.exists_seq_tendsto
-/
theorem _root_.stronglyMeasurable_of_tendsto {ι : Type*} {m : MeasurableSpace α}
    [TopologicalSpace β] [PseudoMetrizableSpace β] (u : Filter ι) [NeBot u] [IsCountablyGenerated u]
    {f : ι -> α -> β} {g : α -> β} (hf : forall i, StronglyMeasurable (f i)) (lim : Tendsto f u (𝓝 g)) :
    StronglyMeasurable g := by
  borelize β
  refine stronglyMeasurable_iff_measurable_separable.2 ⟨?_, ?_⟩
  · exact measurable_of_tendsto_metrizable' u (fun i => (hf i).measurable) lim
  · rcases u.exists_seq_tendsto with ⟨v, hv⟩
    have : IsSeparable (closure (⋃ i, range (f (v i)))) :=
.closure .iUnion fun i => (hf (v i)).isSeparable_range
    apply this.mono
    rintro _ ⟨x, rfl⟩
    rw [tendsto_pi_nhds] at lim
    apply mem_closure_of_tendsto ((lim x).comp hv)
    filter_upwards with n
    apply mem_iUnion_of_mem n
    exact mem_range_self _

/--
theorem `piecewise` / 定理 `piecewise`

English:
theorem piecewise
  statement: {m : MeasurableSpace α} [TopologicalSpace β] {s : Set α}
  proof: by
  refine ⟨fun n => SimpleFunc.piecewise s hs (hf.approx n) (hg.approx n), fun x => ?_⟩
  by_cases hx : x in s
  · simpa [@Set.piecewise_eq_of_mem _ _ _ _ _ (fun _ => Classical.propDecidable _) _ hx,
      hx] using hf.tendsto_approx x
  · simpa [@Set.piecewise_eq_of_notMem _ _ _ _ _ (fun _ => Cla

中文:
定理 piecewise
  结论: {m : MeasurableSpace α} [TopologicalSpace β] {s : Set α}
  证明: by
  refine ⟨fun n => SimpleFunc.piecewise s hs (hf.approx n) (hg.approx n), fun x => ?_⟩
  by_cases hx : x in s
  · simpa [@Set.piecewise_eq_of_mem _ _ _ _ _ (fun _ => Classical.propDecidable _) _ hx,
      hx] using hf.tendsto_approx x
  · simpa [@Set.piecewise_eq_of_notMem _ _ _ _ _ (fun _ => Cla
-/
protected theorem piecewise {m : MeasurableSpace α} [TopologicalSpace β] {s : Set α}
    {_ : DecidablePred (· in s)} (hs : MeasurableSet s) (hf : StronglyMeasurable f)
    (hg : StronglyMeasurable g) : StronglyMeasurable (Set.piecewise s f g) := by
  refine ⟨fun n => SimpleFunc.piecewise s hs (hf.approx n) (hg.approx n), fun x => ?_⟩
  by_cases hx : x in s
  · simpa [@Set.piecewise_eq_of_mem _ _ _ _ _ (fun _ => Classical.propDecidable _) _ hx,
      hx] using hf.tendsto_approx x
  · simpa [@Set.piecewise_eq_of_notMem _ _ _ _ _ (fun _ => Classical.propDecidable _) _ hx,
      hx] using hg.tendsto_approx x

/--
theorem `ite` / 定理 `ite`

English:
theorem ite
  statement: {_ : MeasurableSpace α} [TopologicalSpace β] {p : α -> Prop}
  proof: StronglyMeasurable.piecewise hp hf hg

中文:
定理 ite
  结论: {_ : MeasurableSpace α} [TopologicalSpace β] {p : α -> 命题}
  证明: StronglyMeasurable.piecewise hp hf hg
-/
protected theorem ite {_ : MeasurableSpace α} [TopologicalSpace β] {p : α -> Prop}
    {_ : DecidablePred p} (hp : MeasurableSet { a : α | p a }) (hf : StronglyMeasurable f)
    (hg : StronglyMeasurable g) : StronglyMeasurable fun x => ite (p x) (f x) (g x) :=
  StronglyMeasurable.piecewise hp hf hg

/--
theorem `dite` / 定理 `dite`

English:
theorem dite
  statement: {s : Set α} {m : MeasurableSpace α} [TopologicalSpace β]
  proof: by
  refine ⟨fun n => SimpleFunc.dite s hs (hf.approx n) (hg.approx n), fun x => ?_⟩
  by_cases hx : x in s
  · simpa [hx] using hf.tendsto_approx ⟨x, hx⟩
  · simpa [hx] using hg.tendsto_approx ⟨x, hx⟩

中文:
定理 dite
  结论: {s : Set α} {m : MeasurableSpace α} [TopologicalSpace β]
  证明: by
  refine ⟨fun n => SimpleFunc.dite s hs (hf.approx n) (hg.approx n), fun x => ?_⟩
  by_cases hx : x in s
  · simpa [hx] using hf.tendsto_approx ⟨x, hx⟩
  · simpa [hx] using hg.tendsto_approx ⟨x, hx⟩
-/
protected theorem dite {s : Set α} {m : MeasurableSpace α} [TopologicalSpace β]
    [(x : α) -> Decidable (x in s)] {f : ↑s -> β} (hf : StronglyMeasurable f)
    {g : ↑sᶜ -> β} (hg : StronglyMeasurable g) (hs : MeasurableSet s) :
    StronglyMeasurable fun x => if hx : x in s then f ⟨x, hx⟩ else g ⟨x, hx⟩ := by
  refine ⟨fun n => SimpleFunc.dite s hs (hf.approx n) (hg.approx n), fun x => ?_⟩
  by_cases hx : x in s
  · simpa [hx] using hf.tendsto_approx ⟨x, hx⟩
  · simpa [hx] using hg.tendsto_approx ⟨x, hx⟩

/--
theorem `_root_.ContinuousOn.stronglyMeasurable_of_countable_compl` / 定理 `_root_.ContinuousOn.stronglyMeasurable_of_countable_compl`

English:
theorem _root_.ContinuousOn.stronglyMeasurable_of_countable_compl
  statement: [MeasurableSpace α]
  proof: by
  classical
  have h's : MeasurableSet s := by simpa using hs.measurableSet.compl
  have : f = fun x => if hx : x in s then f (⟨x, hx⟩ : s) else f (⟨x, hx⟩ : (sᶜ : Set α)) := by simp
  rw [this]
  apply StronglyMeasurable.dite (f := fun x => f x) (g := fun x => f x) ?_ ?_ h's
  · have : SecondCou

中文:
定理 _root_.ContinuousOn.stronglyMeasurable_of_countable_compl
  结论: [MeasurableSpace α]
  证明: by
  classical
  have h's : MeasurableSet s := by simpa using hs.measurableSet.compl
  have : f = fun x => if hx : x in s then f (⟨x, hx⟩ : s) else f (⟨x, hx⟩ : (sᶜ : Set α)) := by simp
  rw [this]
  apply StronglyMeasurable.dite (f := fun x => f x) (g := fun x => f x) ?_ ?_ h's
  · have : SecondCou

Depends on / 依赖: MeasurableSet, MeasureTheory, MeasureTheory.StronglyMeasurable.of_discrete, SecondCountableTopologyEither, StronglyMeasurable, StronglyMeasurable.dite, classical, continuousOn_iff_continuous_domRestrict, h.out, hs.measurableSet.compl, hs.to_subtype, infer_instance, measurableSet, of_discrete, stronglyMeasurable, to_subtype
-/
theorem _root_.ContinuousOn.stronglyMeasurable_of_countable_compl [MeasurableSpace α]
    [TopologicalSpace α] [OpensMeasurableSpace α] [MeasurableSingletonClass α]
    [TopologicalSpace β] [PseudoMetrizableSpace β]
    [h : SecondCountableTopologyEither α β] {f : α -> β} {s : Set α} (hf : ContinuousOn f s)
    (hs : (sᶜ).Countable) : StronglyMeasurable f := by
  classical
  have h's : MeasurableSet s := by simpa using hs.measurableSet.compl
  have : f = fun x => if hx : x in s then f (⟨x, hx⟩ : s) else f (⟨x, hx⟩ : (sᶜ : Set α)) := by simp
  rw [this]
  apply StronglyMeasurable.dite (f := fun x => f x) (g := fun x => f x) ?_ ?_ h's
  · have : SecondCountableTopologyEither s β := by cases h.out <;> infer_instance
    exact (continuousOn_iff_continuous_domRestrict.1 hf).stronglyMeasurable
  · have := hs.to_subtype
    exact MeasureTheory.StronglyMeasurable.of_discrete

/--
theorem `of_countable_not_continuousAt` / 定理 `of_countable_not_continuousAt`

English:
theorem of_countable_not_continuousAt
  statement: [MeasurableSpace α] [TopologicalSpace α]
  proof: by
  have : ContinuousOn f {x | ContinuousAt f x} := fun x hx => hx.continuousWithinAt
  apply this.stronglyMeasurable_of_countable_compl
  convert hf
  grind

@[fun_prop]

中文:
定理 of_countable_not_continuousAt
  结论: [MeasurableSpace α] [TopologicalSpace α]
  证明: by
  have : ContinuousOn f {x | ContinuousAt f x} := fun x hx => hx.continuousWithinAt
  apply this.stronglyMeasurable_of_countable_compl
  convert hf
  grind

@[fun_prop]

Depends on / 依赖: ContinuousAt, ContinuousOn, continuousWithinAt, convert, hx.continuousWithinAt, stronglyMeasurable_of_countable_compl, this.stronglyMeasurable_of_countable_compl
-/
theorem of_countable_not_continuousAt [MeasurableSpace α] [TopologicalSpace α]
    [OpensMeasurableSpace α] [MeasurableSingletonClass α]
    [TopologicalSpace β] [PseudoMetrizableSpace β]
    [h : SecondCountableTopologyEither α β] {f : α -> β}
    (hf : Set.Countable {x | ¬ ContinuousAt f x}) : StronglyMeasurable f := by
  have : ContinuousOn f {x | ContinuousAt f x} := fun x hx => hx.continuousWithinAt
  apply this.stronglyMeasurable_of_countable_compl
  convert hf
  grind

@[fun_prop]
/--
theorem `_root_.MeasurableEmbedding.stronglyMeasurable_extend` / 定理 `_root_.MeasurableEmbedding.stronglyMeasurable_extend`

English:
theorem _root_.MeasurableEmbedding.stronglyMeasurable_extend
  statement: {f : α -> β} {g : α -> γ} {g' : γ -> β}
  proof: by
  refine ⟨fun n => SimpleFunc.extend (hf.approx n) g hg (hg'.approx n), ?_⟩
  intro x
  by_cases hx : exists y, g y = x
  · rcases hx with ⟨y, rfl⟩
    simpa only [SimpleFunc.extend_apply, hg.injective, Injective.extend_apply] using
      hf.tendsto_approx y
  · simpa only [hx, SimpleFunc.extend_

中文:
定理 _root_.MeasurableEmbedding.stronglyMeasurable_extend
  结论: {f : α -> β} {g : α -> γ} {g' : γ -> β}
  证明: by
  refine ⟨fun n => SimpleFunc.extend (hf.approx n) g hg (hg'.approx n), ?_⟩
  intro x
  by_cases hx : exists y, g y = x
  · rcases hx with ⟨y, rfl⟩
    simpa only [SimpleFunc.extend_apply, hg.injective, Injective.extend_apply] using
      hf.tendsto_approx y
  · simpa only [hx, SimpleFunc.extend_

Depends on / 依赖: Injective, Injective.extend_apply, SimpleFunc, SimpleFunc.extend, SimpleFunc.extend_apply, approx, extend, extend_apply, hf.approx, hf.tendsto_approx, hg.injective, injective, not_false_iff, tendsto_approx
-/
theorem _root_.MeasurableEmbedding.stronglyMeasurable_extend {f : α -> β} {g : α -> γ} {g' : γ -> β}
    {mα : MeasurableSpace α} {mγ : MeasurableSpace γ} [TopologicalSpace β]
    (hg : MeasurableEmbedding g) (hf : StronglyMeasurable f) (hg' : StronglyMeasurable g') :
    StronglyMeasurable (Function.extend g f g') := by
  refine ⟨fun n => SimpleFunc.extend (hf.approx n) g hg (hg'.approx n), ?_⟩
  intro x
  by_cases hx : exists y, g y = x
  · rcases hx with ⟨y, rfl⟩
    simpa only [SimpleFunc.extend_apply, hg.injective, Injective.extend_apply] using
      hf.tendsto_approx y
  · simpa only [hx, SimpleFunc.extend_apply', not_false_iff, extend_apply'] using
      hg'.tendsto_approx x

/--
theorem `_root_.MeasurableEmbedding.exists_stronglyMeasurable_extend` / 定理 `_root_.MeasurableEmbedding.exists_stronglyMeasurable_extend`

English:
theorem _root_.MeasurableEmbedding.exists_stronglyMeasurable_extend
  statement: {f : α -> β} {g : α -> γ}
  proof: ⟨Function.extend g f fun x => Classical.choice (hne x),
    hg.stronglyMeasurable_extend hf (stronglyMeasurable_const' fun _ _ => rfl),
    funext fun _ => hg.injective.extend_apply _ _ _⟩

中文:
定理 _root_.MeasurableEmbedding.exists_stronglyMeasurable_extend
  结论: {f : α -> β} {g : α -> γ}
  证明: ⟨Function.extend g f fun x => Classical.choice (hne x),
    hg.stronglyMeasurable_extend hf (stronglyMeasurable_const' fun _ _ => rfl),
    funext fun _ => hg.injective.extend_apply _ _ _⟩

Depends on / 依赖: Classical, Classical.choice, Function, Function.extend, choice, extend, extend_apply, hg.injective.extend_apply, hg.stronglyMeasurable_extend, injective, stronglyMeasurable_const, stronglyMeasurable_extend
-/
theorem _root_.MeasurableEmbedding.exists_stronglyMeasurable_extend {f : α -> β} {g : α -> γ}
    {_ : MeasurableSpace α} {_ : MeasurableSpace γ} [TopologicalSpace β]
    (hg : MeasurableEmbedding g) (hf : StronglyMeasurable f) (hne : γ -> Nonempty β) :
    exists f' : γ -> β, StronglyMeasurable f' ∧ f' ∘ g = f :=
  ⟨Function.extend g f fun x => Classical.choice (hne x),
    hg.stronglyMeasurable_extend hf (stronglyMeasurable_const' fun _ _ => rfl),
    funext fun _ => hg.injective.extend_apply _ _ _⟩

/--
theorem `_root_.stronglyMeasurable_of_stronglyMeasurable_union_cover` / 定理 `_root_.stronglyMeasurable_of_stronglyMeasurable_union_cover`

English:
theorem _root_.stronglyMeasurable_of_stronglyMeasurable_union_cover
  statement: {m : MeasurableSpace α}
  proof: by
  nontriviality β; inhabit β
  suffices Function.extend Subtype.val (fun x : s => f x)
      (Function.extend (↑) (fun x : t => f x) fun _ => default) = f from
this ▸ (MeasurableEmbedding.subtype_coe hs).stronglyMeasurable_extend hc
      (MeasurableEmbedding.subtype_coe ht).stronglyMeasurable_ex

中文:
定理 _root_.stronglyMeasurable_of_stronglyMeasurable_union_cover
  结论: {m : MeasurableSpace α}
  证明: by
  nontriviality β; inhabit β
  suffices Function.extend Subtype.val (fun x : s => f x)
      (Function.extend (↑) (fun x : t => f x) fun _ => default) = f from
this ▸ (MeasurableEmbedding.subtype_coe hs).stronglyMeasurable_extend hc
      (MeasurableEmbedding.subtype_coe ht).stronglyMeasurable_ex

Depends on / 依赖: Function, Function.extend, MeasurableEmbedding, MeasurableEmbedding.subtype_coe, Subtype, Subtype.coe_injective.extend_apply, Subtype.val, coe_injective, extend, extend_apply, inhabit, nontriviality, resolve_left, stronglyMeasurable_const, stronglyMeasurable_extend, subtype_coe
-/
theorem _root_.stronglyMeasurable_of_stronglyMeasurable_union_cover {m : MeasurableSpace α}
    [TopologicalSpace β] {f : α -> β} (s t : Set α) (hs : MeasurableSet s) (ht : MeasurableSet t)
    (h : univ subseteq s union t) (hc : StronglyMeasurable fun a : s => f a)
    (hd : StronglyMeasurable fun a : t => f a) : StronglyMeasurable f := by
  nontriviality β; inhabit β
  suffices Function.extend Subtype.val (fun x : s => f x)
      (Function.extend (↑) (fun x : t => f x) fun _ => default) = f from
this ▸ (MeasurableEmbedding.subtype_coe hs).stronglyMeasurable_extend hc
      (MeasurableEmbedding.subtype_coe ht).stronglyMeasurable_extend hd stronglyMeasurable_const
  ext x
  by_cases hxs : x in s
  · lift x to s using hxs
    simp
  · lift x to t using (h trivial).resolve_left hxs
    rw [extend_apply']; rw [Subtype.coe_injective.extend_apply]
exact fun ⟨y, hy⟩ => hxs hy ▸ y.2

/--
theorem `_root_.stronglyMeasurable_of_restrict_of_restrict_compl` / 定理 `_root_.stronglyMeasurable_of_restrict_of_restrict_compl`

English:
theorem _root_.stronglyMeasurable_of_restrict_of_restrict_compl
  statement: {_ : MeasurableSpace α}
  proof: stronglyMeasurable_of_stronglyMeasurable_union_cover s sᶜ hs hs.compl (union_compl_self s).ge h₁
    h₂

@[fun_prop]

中文:
定理 _root_.stronglyMeasurable_of_restrict_of_restrict_compl
  结论: {_ : MeasurableSpace α}
  证明: stronglyMeasurable_of_stronglyMeasurable_union_cover s sᶜ hs hs.compl (union_compl_self s).ge h₁
    h₂

@[fun_prop]

Depends on / 依赖: hs.compl, stronglyMeasurable_of_stronglyMeasurable_union_cover, union_compl_self
-/
theorem _root_.stronglyMeasurable_of_restrict_of_restrict_compl {_ : MeasurableSpace α}
    [TopologicalSpace β] {f : α -> β} {s : Set α} (hs : MeasurableSet s)
    (h₁ : StronglyMeasurable (s.domRestrict f)) (h₂ : StronglyMeasurable (sᶜ.domRestrict f)) :
    StronglyMeasurable f :=
  stronglyMeasurable_of_stronglyMeasurable_union_cover s sᶜ hs hs.compl (union_compl_self s).ge h₁
    h₂

@[fun_prop]
/--
theorem `indicator` / 定理 `indicator`

English:
theorem indicator
  statement: {_ : MeasurableSpace α} [TopologicalSpace β] [Zero β]
  proof: hf.piecewise hs stronglyMeasurable_const

中文:
定理 indicator
  结论: {_ : MeasurableSpace α} [TopologicalSpace β] [Zero β]
  证明: hf.piecewise hs stronglyMeasurable_const
-/
protected theorem indicator {_ : MeasurableSpace α} [TopologicalSpace β] [Zero β]
    (hf : StronglyMeasurable f) {s : Set α} (hs : MeasurableSet s) :
    StronglyMeasurable (s.indicator f) :=
  hf.piecewise hs stronglyMeasurable_const

/--
theorem `induction` / 定理 `induction`

English:
theorem induction
  statement: [MeasurableSpace α] [AddZeroClass β] [TopologicalSpace β]
  proof: by
  let s := hf.approx
  refine lim (fun n => (s n).stronglyMeasurable) hf (fun n => ?_) hf.tendsto_approx
  induction s n using SimpleFunc.induction with
  | const c hs => exact ind c hs
  | @add f g h_supp hf hg =>
    exact add f.stronglyMeasurable g.stronglyMeasurable (f + g).stronglyMeasurable

中文:
定理 induction
  结论: [MeasurableSpace α] [AddZeroClass β] [TopologicalSpace β]
  证明: by
  let s := hf.approx
  refine lim (fun n => (s n).stronglyMeasurable) hf (fun n => ?_) hf.tendsto_approx
  induction s n using SimpleFunc.induction with
  | const c hs => exact ind c hs
  | @add f g h_supp hf hg =>
    exact add f.stronglyMeasurable g.stronglyMeasurable (f + g).stronglyMeasurable

Depends on / 依赖: SimpleFunc, SimpleFunc.induction, approx, f.stronglyMeasurable, g.stronglyMeasurable, h_supp, hf.approx, hf.tendsto_approx, stronglyMeasurable, tendsto_approx
-/
theorem induction [MeasurableSpace α] [AddZeroClass β] [TopologicalSpace β]
    {P : (f : α -> β) -> StronglyMeasurable f -> Prop}
    (ind : forall c ⦃s : Set α⦄ (hs : MeasurableSet s),
      P (s.indicator fun _ => c) (stronglyMeasurable_const.indicator hs))
    (add : forall ⦃f g : α -> β⦄ (hf : StronglyMeasurable f) (hg : StronglyMeasurable g)
      (hfg : StronglyMeasurable (f + g)), Disjoint f.support g.support ->
      P f hf -> P g hg -> P (f + g) hfg)
    (lim : forall ⦃f : Nat -> α -> β⦄ ⦃g : α -> β⦄ (hf : forall n, StronglyMeasurable (f n))
      (hg : StronglyMeasurable g), (forall n, P (f n) (hf n)) ->
      (forall x, Tendsto (f · x) atTop (𝓝 (g x))) -> P g hg)
    (f : α -> β) (hf : StronglyMeasurable f) : P f hf := by
  let s := hf.approx
  refine lim (fun n => (s n).stronglyMeasurable) hf (fun n => ?_) hf.tendsto_approx
  induction s n using SimpleFunc.induction with
  | const c hs => exact ind c hs
  | @add f g h_supp hf hg =>
    exact add f.stronglyMeasurable g.stronglyMeasurable (f + g).stronglyMeasurable h_supp hf hg

open scoped Classical in
/--
theorem `induction'` / 定理 `induction'`

English:
theorem induction'
  statement: [MeasurableSpace α] [Nonempty β] [TopologicalSpace β]
  proof: by
  let s := hf.approx
  refine lim (fun n => (s n).stronglyMeasurable) hf (fun n => ?_) hf.tendsto_approx
  induction s n with
  | const c => exact const c
  | @pcw f g s hs Pf Pg =>
    simp_rw [SimpleFunc.coe_piecewise]
    exact pcw f.stronglyMeasurable g.stronglyMeasurable hs Pf Pg

@[fun_prop

中文:
定理 induction'
  结论: [MeasurableSpace α] [Nonempty β] [TopologicalSpace β]
  证明: by
  let s := hf.approx
  refine lim (fun n => (s n).stronglyMeasurable) hf (fun n => ?_) hf.tendsto_approx
  induction s n with
  | const c => exact const c
  | @pcw f g s hs Pf Pg =>
    simp_rw [SimpleFunc.coe_piecewise]
    exact pcw f.stronglyMeasurable g.stronglyMeasurable hs Pf Pg

@[fun_prop

Depends on / 依赖: SimpleFunc, SimpleFunc.coe_piecewise, approx, coe_piecewise, f.stronglyMeasurable, g.stronglyMeasurable, hf.approx, hf.tendsto_approx, simp_rw, stronglyMeasurable, tendsto_approx
-/
theorem induction' [MeasurableSpace α] [Nonempty β] [TopologicalSpace β]
    {P : (f : α -> β) -> StronglyMeasurable f -> Prop}
    (const : forall (c), P (fun _ => c) stronglyMeasurable_const)
    (pcw : forall ⦃f g : α -> β⦄ {s} (hf : StronglyMeasurable f) (hg : StronglyMeasurable g)
      (hs : MeasurableSet s), P f hf -> P g hg -> P (s.piecewise f g) (hf.piecewise hs hg))
    (lim : forall ⦃f : Nat -> α -> β⦄ ⦃g : α -> β⦄ (hf : forall n, StronglyMeasurable (f n))
      (hg : StronglyMeasurable g), (forall n, P (f n) (hf n)) ->
      (forall x, Tendsto (f · x) atTop (𝓝 (g x))) -> P g hg)
    (f : α -> β) (hf : StronglyMeasurable f) : P f hf := by
  let s := hf.approx
  refine lim (fun n => (s n).stronglyMeasurable) hf (fun n => ?_) hf.tendsto_approx
  induction s n with
  | const c => exact const c
  | @pcw f g s hs Pf Pg =>
    simp_rw [SimpleFunc.coe_piecewise]
    exact pcw f.stronglyMeasurable g.stronglyMeasurable hs Pf Pg

@[fun_prop]
/--
theorem `dist` / 定理 `dist`

English:
theorem dist
  statement: {_ : MeasurableSpace α} {β : Type*} [PseudoMetricSpace β] {f g : α -> β}
  proof: continuous_dist.comp_stronglyMeasurable (hf.prodMk hg)

@[fun_prop]

中文:
定理 dist
  结论: {_ : MeasurableSpace α} {β : 类型} [PseudoMetricSpace β] {f g : α -> β}
  证明: continuous_dist.comp_stronglyMeasurable (hf.prodMk hg)

@[fun_prop]
-/
protected theorem dist {_ : MeasurableSpace α} {β : Type*} [PseudoMetricSpace β] {f g : α -> β}
    (hf : StronglyMeasurable f) (hg : StronglyMeasurable g) :
    StronglyMeasurable fun x => dist (f x) (g x) :=
  continuous_dist.comp_stronglyMeasurable (hf.prodMk hg)

@[fun_prop]
/--
theorem `edist` / 定理 `edist`

English:
theorem edist
  statement: {_ : MeasurableSpace α} {β : Type*} [PseudoEMetricSpace β] {f g : α -> β}
  proof: continuous_edist.comp_stronglyMeasurable (hf.prodMk hg)

@[fun_prop]

中文:
定理 edist
  结论: {_ : MeasurableSpace α} {β : 类型} [PseudoEMetricSpace β] {f g : α -> β}
  证明: continuous_edist.comp_stronglyMeasurable (hf.prodMk hg)

@[fun_prop]
-/
protected theorem edist {_ : MeasurableSpace α} {β : Type*} [PseudoEMetricSpace β] {f g : α -> β}
    (hf : StronglyMeasurable f) (hg : StronglyMeasurable g) :
    StronglyMeasurable fun x => edist (f x) (g x) :=
  continuous_edist.comp_stronglyMeasurable (hf.prodMk hg)

@[fun_prop]
/--
theorem `norm` / 定理 `norm`

English:
theorem norm
  statement: {_ : MeasurableSpace α} {β : Type*} [SeminormedAddCommGroup β] {f : α -> β}
  proof: continuous_norm.comp_stronglyMeasurable hf

@[fun_prop]

中文:
定理 norm
  结论: {_ : MeasurableSpace α} {β : 类型} [SeminormedAddCommGroup β] {f : α -> β}
  证明: continuous_norm.comp_stronglyMeasurable hf

@[fun_prop]
-/
protected theorem norm {_ : MeasurableSpace α} {β : Type*} [SeminormedAddCommGroup β] {f : α -> β}
    (hf : StronglyMeasurable f) : StronglyMeasurable fun x => ‖f x‖ :=
  continuous_norm.comp_stronglyMeasurable hf

@[fun_prop]
/--
theorem `nnnorm` / 定理 `nnnorm`

English:
theorem nnnorm
  statement: {_ : MeasurableSpace α} {β : Type*} [SeminormedAddCommGroup β] {f : α -> β}
  proof: continuous_nnnorm.comp_stronglyMeasurable hf

中文:
定理 nnnorm
  结论: {_ : MeasurableSpace α} {β : 类型} [SeminormedAddCommGroup β] {f : α -> β}
  证明: continuous_nnnorm.comp_stronglyMeasurable hf
-/
protected theorem nnnorm {_ : MeasurableSpace α} {β : Type*} [SeminormedAddCommGroup β] {f : α -> β}
    (hf : StronglyMeasurable f) : StronglyMeasurable fun x => ‖f x‖₊ :=
  continuous_nnnorm.comp_stronglyMeasurable hf

/-- The `enorm` of a strongly measurable function is measurable.

Unlike `StrongMeasurable.norm` and `StronglyMeasurable.nnnorm`, this lemma proves measurability,
**not** strong measurability. This is an intentional decision: for functions taking values in
ℝ≥0∞, measurability is much more useful than strong measurability. -/
@[fun_prop]
/--
theorem `enorm` / 定理 `enorm`

English:
theorem enorm
  statement: {_ : MeasurableSpace α} {ε : Type*} [TopologicalSpace ε] [ContinuousENorm ε]
  proof: (continuous_enorm.comp_stronglyMeasurable hf).measurable

@[fun_prop]

中文:
定理 enorm
  结论: {_ : MeasurableSpace α} {ε : 类型} [TopologicalSpace ε] [ContinuousENorm ε]
  证明: (continuous_enorm.comp_stronglyMeasurable hf).measurable

@[fun_prop]
-/
protected theorem enorm {_ : MeasurableSpace α} {ε : Type*} [TopologicalSpace ε] [ContinuousENorm ε]
    {f : α -> ε} (hf : StronglyMeasurable f) : Measurable (‖f ·‖ₑ) :=
  (continuous_enorm.comp_stronglyMeasurable hf).measurable

@[fun_prop]
/--
theorem `real_toNNReal` / 定理 `real_toNNReal`

English:
theorem real_toNNReal
  given: {_ : MeasurableSpace α} {f : α -> Real} (hf : StronglyMeasurable f)
  proof: continuous_real_toNNReal.comp_stronglyMeasurable hf

中文:
定理 real_toNNReal
  条件: {_ : MeasurableSpace α} {f : α -> 实数} (hf : StronglyMeasurable f)
  证明: continuous_real_toNNReal.comp_stronglyMeasurable hf
-/
protected theorem real_toNNReal {_ : MeasurableSpace α} {f : α -> Real} (hf : StronglyMeasurable f) :
    StronglyMeasurable fun x => (f x).toNNReal :=
  continuous_real_toNNReal.comp_stronglyMeasurable hf

section PseudoMetrizableSpace
variable {E : Type*} {m m₀ : MeasurableSpace α} {μ : Measure[m₀] α} {f g : α -> E}
  [TopologicalSpace E] [Preorder E] [OrderClosedTopology E] [PseudoMetrizableSpace E]

/--
lemma `measurableSet_le` / 引理 `measurableSet_le`

English:
lemma measurableSet_le
  given: (hf : StronglyMeasurable[m] f) (hg : StronglyMeasurable[m] g)
  proof: by
  borelize (E × E)
  exact (hf.prodMk hg).measurable isClosed_le_prod.measurableSet

中文:
引理 measurableSet_le
  条件: (hf : StronglyMeasurable[m] f) (hg : StronglyMeasurable[m] g)
  证明: by
  borelize (E × E)
  exact (hf.prodMk hg).measurable isClosed_le_prod.measurableSet

Depends on / 依赖: borelize, hf.prodMk, isClosed_le_prod, isClosed_le_prod.measurableSet, measurable, measurableSet, prodMk
-/
lemma measurableSet_le (hf : StronglyMeasurable[m] f) (hg : StronglyMeasurable[m] g) :
    MeasurableSet[m] {a | f a <= g a} := by
  borelize (E × E)
  exact (hf.prodMk hg).measurable isClosed_le_prod.measurableSet

/--
lemma `measurableSet_lt` / 引理 `measurableSet_lt`

English:
lemma measurableSet_lt
  given: (hf : StronglyMeasurable[m] f) (hg : StronglyMeasurable[m] g)
  proof: by
  simpa only [lt_iff_le_not_ge] using! (hf.measurableSet_le hg).inter (hg.measurableSet_le hf).compl

中文:
引理 measurableSet_lt
  条件: (hf : StronglyMeasurable[m] f) (hg : StronglyMeasurable[m] g)
  证明: by
  simpa only [lt_iff_le_not_ge] using! (hf.measurableSet_le hg).inter (hg.measurableSet_le hf).compl

Depends on / 依赖: hf.measurableSet_le, hg.measurableSet_le, lt_iff_le_not_ge, measurableSet_le
-/
lemma measurableSet_lt (hf : StronglyMeasurable[m] f) (hg : StronglyMeasurable[m] g) :
    MeasurableSet[m] {a | f a < g a} := by
  simpa only [lt_iff_le_not_ge] using! (hf.measurableSet_le hg).inter (hg.measurableSet_le hf).compl

/--
lemma `ae_le_trim_of_stronglyMeasurable` / 引理 `ae_le_trim_of_stronglyMeasurable`

English:
lemma ae_le_trim_of_stronglyMeasurable
  statement: (hm : m <= m₀) (hf : StronglyMeasurable[m] f)
  proof: by
  rwa [EventuallyLE, ae_iff, trim_measurableSet_eq hm]
  exact (hf.measurableSet_le hg).compl

中文:
引理 ae_le_trim_of_stronglyMeasurable
  结论: (hm : m <= m₀) (hf : StronglyMeasurable[m] f)
  证明: by
  rwa [EventuallyLE, ae_iff, trim_measurableSet_eq hm]
  exact (hf.measurableSet_le hg).compl

Depends on / 依赖: EventuallyLE, ae_iff, hf.measurableSet_le, measurableSet_le, trim_measurableSet_eq
-/
lemma ae_le_trim_of_stronglyMeasurable (hm : m <= m₀) (hf : StronglyMeasurable[m] f)
    (hg : StronglyMeasurable[m] g) (hfg : f <=ᵐ[μ] g) : f <=ᵐ[μ.trim hm] g := by
  rwa [EventuallyLE, ae_iff, trim_measurableSet_eq hm]
  exact (hf.measurableSet_le hg).compl

/--
lemma `ae_le_trim_iff` / 引理 `ae_le_trim_iff`

English:
lemma ae_le_trim_iff
  given: (hm : m <= m₀) (hf : StronglyMeasurable[m] f) (hg : StronglyMeasurable[m] g)
  proof: ⟨ae_le_of_ae_le_trim, ae_le_trim_of_stronglyMeasurable hm hf hg⟩

中文:
引理 ae_le_trim_iff
  条件: (hm : m <= m₀) (hf : StronglyMeasurable[m] f) (hg : StronglyMeasurable[m] g)
  证明: ⟨ae_le_of_ae_le_trim, ae_le_trim_of_stronglyMeasurable hm hf hg⟩

Depends on / 依赖: ae_le_of_ae_le_trim, ae_le_trim_of_stronglyMeasurable
-/
lemma ae_le_trim_iff (hm : m <= m₀) (hf : StronglyMeasurable[m] f) (hg : StronglyMeasurable[m] g) :
    f <=ᵐ[μ.trim hm] g ↔ f <=ᵐ[μ] g :=
  ⟨ae_le_of_ae_le_trim, ae_le_trim_of_stronglyMeasurable hm hf hg⟩

end PseudoMetrizableSpace

section MetrizableSpace
variable {E : Type*} {m m₀ : MeasurableSpace α} {μ : Measure[m₀] α} {f g : α -> E}
  [TopologicalSpace E] [MetrizableSpace E]

/--
lemma `measurableSet_eq_fun` / 引理 `measurableSet_eq_fun`

English:
lemma measurableSet_eq_fun
  given: (hf : StronglyMeasurable[m] f) (hg : StronglyMeasurable[m] g)
  proof: by
  borelize (E × E)
  exact (hf.prodMk hg).measurable isClosed_diagonal.measurableSet

中文:
引理 measurableSet_eq_fun
  条件: (hf : StronglyMeasurable[m] f) (hg : StronglyMeasurable[m] g)
  证明: by
  borelize (E × E)
  exact (hf.prodMk hg).measurable isClosed_diagonal.measurableSet

Depends on / 依赖: borelize, hf.prodMk, isClosed_diagonal, isClosed_diagonal.measurableSet, measurable, measurableSet, prodMk
-/
lemma measurableSet_eq_fun (hf : StronglyMeasurable[m] f) (hg : StronglyMeasurable[m] g) :
    MeasurableSet[m] {a | f a = g a} := by
  borelize (E × E)
  exact (hf.prodMk hg).measurable isClosed_diagonal.measurableSet

/--
lemma `ae_eq_trim_of_stronglyMeasurable` / 引理 `ae_eq_trim_of_stronglyMeasurable`

English:
lemma ae_eq_trim_of_stronglyMeasurable
  statement: (hm : m <= m₀) (hf : StronglyMeasurable[m] f)
  proof: by
  rwa [EventuallyEq, ae_iff, trim_measurableSet_eq hm]
  exact (hf.measurableSet_eq_fun hg).compl

中文:
引理 ae_eq_trim_of_stronglyMeasurable
  结论: (hm : m <= m₀) (hf : StronglyMeasurable[m] f)
  证明: by
  rwa [EventuallyEq, ae_iff, trim_measurableSet_eq hm]
  exact (hf.measurableSet_eq_fun hg).compl

Depends on / 依赖: EventuallyEq, ae_iff, hf.measurableSet_eq_fun, measurableSet_eq_fun, trim_measurableSet_eq
-/
lemma ae_eq_trim_of_stronglyMeasurable (hm : m <= m₀) (hf : StronglyMeasurable[m] f)
    (hg : StronglyMeasurable[m] g) (hfg : f =ᵐ[μ] g) : f =ᵐ[μ.trim hm] g := by
  rwa [EventuallyEq, ae_iff, trim_measurableSet_eq hm]
  exact (hf.measurableSet_eq_fun hg).compl

/--
lemma `ae_eq_trim_iff` / 引理 `ae_eq_trim_iff`

English:
lemma ae_eq_trim_iff
  given: (hm : m <= m₀) (hf : StronglyMeasurable[m] f) (hg : StronglyMeasurable[m] g)
  proof: ⟨ae_eq_of_ae_eq_trim, ae_eq_trim_of_stronglyMeasurable hm hf hg⟩

中文:
引理 ae_eq_trim_iff
  条件: (hm : m <= m₀) (hf : StronglyMeasurable[m] f) (hg : StronglyMeasurable[m] g)
  证明: ⟨ae_eq_of_ae_eq_trim, ae_eq_trim_of_stronglyMeasurable hm hf hg⟩

Depends on / 依赖: ae_eq_of_ae_eq_trim, ae_eq_trim_of_stronglyMeasurable
-/
lemma ae_eq_trim_iff (hm : m <= m₀) (hf : StronglyMeasurable[m] f) (hg : StronglyMeasurable[m] g) :
    f =ᵐ[μ.trim hm] g ↔ f =ᵐ[μ] g :=
  ⟨ae_eq_of_ae_eq_trim, ae_eq_trim_of_stronglyMeasurable hm hf hg⟩

end MetrizableSpace

/--
theorem `stronglyMeasurable_in_set` / 定理 `stronglyMeasurable_in_set`

English:
theorem stronglyMeasurable_in_set
  statement: {m : MeasurableSpace α} [TopologicalSpace β] [Zero β] {s : Set α}
  proof: by
  refine ⟨fun n => (hf.approx n).restrict s, ?_, ?_⟩
  · intro x
    by_cases hx : x in s
    · simpa [SimpleFunc.coe_restrict, hs, hx] using hf.tendsto_approx x
    · simpa [SimpleFunc.coe_restrict, hs, hx, hf_zero x hx] using tendsto_const_nhds
  · intro x hx n
    simp [SimpleFunc.coe_restrict

中文:
定理 stronglyMeasurable_in_set
  结论: {m : MeasurableSpace α} [TopologicalSpace β] [Zero β] {s : Set α}
  证明: by
  refine ⟨fun n => (hf.approx n).restrict s, ?_, ?_⟩
  · intro x
    by_cases hx : x in s
    · simpa [SimpleFunc.coe_restrict, hs, hx] using hf.tendsto_approx x
    · simpa [SimpleFunc.coe_restrict, hs, hx, hf_zero x hx] using tendsto_const_nhds
  · intro x hx n
    simp [SimpleFunc.coe_restrict

Depends on / 依赖: SimpleFunc, SimpleFunc.coe_restrict, approx, coe_restrict, hf.approx, hf.tendsto_approx, hf_zero, restrict, tendsto_approx, tendsto_const_nhds
-/
theorem stronglyMeasurable_in_set {m : MeasurableSpace α} [TopologicalSpace β] [Zero β] {s : Set α}
    {f : α -> β} (hs : MeasurableSet s) (hf : StronglyMeasurable f)
    (hf_zero : forall x, x ∉ s -> f x = 0) :
    exists fs : Nat -> α ->ₛ β,
      (forall x, Tendsto (fun n => fs n x) atTop (𝓝 (f x))) ∧ forall x ∉ s, forall n, fs n x = 0 := by
  refine ⟨fun n => (hf.approx n).restrict s, ?_, ?_⟩
  · intro x
    by_cases hx : x in s
    · simpa [SimpleFunc.coe_restrict, hs, hx] using hf.tendsto_approx x
    · simpa [SimpleFunc.coe_restrict, hs, hx, hf_zero x hx] using tendsto_const_nhds
  · intro x hx n
    simp [SimpleFunc.coe_restrict, hs, hx]

/--
theorem `stronglyMeasurable_of_measurableSpace_le_on` / 定理 `stronglyMeasurable_of_measurableSpace_le_on`

English:
theorem stronglyMeasurable_of_measurableSpace_le_on
  statement: {α E} {m m₂ : MeasurableSpace α}
  proof: by
  have hs_m₂ : MeasurableSet[m₂] s := by
    have : MeasurableSet (s inter univ) := hs univ (by simpa)
    simpa
  have h_sub : m.comap ((↑) : s -> α) <= m₂.comap ((↑) : s -> α) := by
    intro _ ht
    rcases ht with ⟨u, hu, rfl⟩
    exact ⟨s inter u, hs u (hs_m.inter hu), by simp⟩
  refine stro

中文:
定理 stronglyMeasurable_of_measurableSpace_le_on
  结论: {α E} {m m₂ : MeasurableSpace α}
  证明: by
  have hs_m₂ : MeasurableSet[m₂] s := by
    have : MeasurableSet (s inter univ) := hs univ (by simpa)
    simpa
  have h_sub : m.comap ((↑) : s -> α) <= m₂.comap ((↑) : s -> α) := by
    intro _ ht
    rcases ht with ⟨u, hu, rfl⟩
    exact ⟨s inter u, hs u (hs_m.inter hu), by simp⟩
  refine stro

Depends on / 依赖: MeasurableSet, comap_measurable, comp_measurable, h_sub, hf.comp_measurable, hf_zero, hs_m, hs_m.inter, m.comap, stronglyMeasurable_const, stronglyMeasurable_of_restrict_of_restrict_compl
-/
theorem stronglyMeasurable_of_measurableSpace_le_on {α E} {m m₂ : MeasurableSpace α}
    [TopologicalSpace E] [Zero E] {s : Set α} {f : α -> E} (hs_m : MeasurableSet[m] s)
    (hs : forall t, MeasurableSet[m] (s inter t) -> MeasurableSet[m₂] (s inter t))
    (hf : StronglyMeasurable[m] f) (hf_zero : forall x ∉ s, f x = 0) :
    StronglyMeasurable[m₂] f := by
  have hs_m₂ : MeasurableSet[m₂] s := by
    have : MeasurableSet (s inter univ) := hs univ (by simpa)
    simpa
  have h_sub : m.comap ((↑) : s -> α) <= m₂.comap ((↑) : s -> α) := by
    intro _ ht
    rcases ht with ⟨u, hu, rfl⟩
    exact ⟨s inter u, hs u (hs_m.inter hu), by simp⟩
  refine stronglyMeasurable_of_restrict_of_restrict_compl hs_m₂ ?_ ?_
  · exact (hf.comp_measurable (comap_measurable _)).mono h_sub
  · exact stronglyMeasurable_const' fun x y => by simp [hf_zero _ x.2, hf_zero _ y.2]

/--
theorem `exists_spanning_measurableSet_norm_le` / 定理 `exists_spanning_measurableSet_norm_le`

English:
theorem exists_spanning_measurableSet_norm_le
  statement: [SeminormedAddCommGroup β] {m m0 : MeasurableSpace α}
  proof: by
  obtain ⟨s, hs, hs_univ⟩ :=
    @exists_spanning_measurableSet_le _ m _ hf.nnnorm.measurable (μ.trim hm) _
  refine ⟨s, fun n => ⟨(hs n).1, (le_trim hm).trans_lt (hs n).2.1, fun x hx => ?_⟩, hs_univ⟩
  have hx_nnnorm : ‖f x‖₊ <= n := (hs n).2.2 x hx
  rw [← coe_nnnorm]
  norm_cast

中文:
定理 exists_spanning_measurableSet_norm_le
  结论: [SeminormedAddCommGroup β] {m m0 : MeasurableSpace α}
  证明: by
  obtain ⟨s, hs, hs_univ⟩ :=
    @exists_spanning_measurableSet_le _ m _ hf.nnnorm.measurable (μ.trim hm) _
  refine ⟨s, fun n => ⟨(hs n).1, (le_trim hm).trans_lt (hs n).2.1, fun x hx => ?_⟩, hs_univ⟩
  have hx_nnnorm : ‖f x‖₊ <= n := (hs n).2.2 x hx
  rw [← coe_nnnorm]
  norm_cast

Depends on / 依赖: coe_nnnorm, exists_spanning_measurableSet_le, hf.nnnorm.measurable, hs_univ, hx_nnnorm, le_trim, measurable, nnnorm, trans_lt
-/
theorem exists_spanning_measurableSet_norm_le [SeminormedAddCommGroup β] {m m0 : MeasurableSpace α}
    (hm : m <= m0) (hf : StronglyMeasurable[m] f) (μ : Measure α) [SigmaFinite (μ.trim hm)] :
    exists s : Nat -> Set α,
      (forall n, MeasurableSet[m] (s n) ∧ μ (s n) < ∞ ∧ forall x in s n, ‖f x‖ <= n) ∧
      ⋃ i, s i = Set.univ := by
  obtain ⟨s, hs, hs_univ⟩ :=
    @exists_spanning_measurableSet_le _ m _ hf.nnnorm.measurable (μ.trim hm) _
  refine ⟨s, fun n => ⟨(hs n).1, (le_trim hm).trans_lt (hs n).2.1, fun x hx => ?_⟩, hs_univ⟩
  have hx_nnnorm : ‖f x‖₊ <= n := (hs n).2.2 x hx
  rw [← coe_nnnorm]
  norm_cast

end StronglyMeasurable



/--
theorem `finStronglyMeasurable_zero` / 定理 `finStronglyMeasurable_zero`

English:
theorem finStronglyMeasurable_zero
  statement: {α β} {m : MeasurableSpace α} {μ : Measure α} [Zero β]
  proof: ⟨0, by
    simp only [Pi.zero_apply, SimpleFunc.coe_zero, support_zero, measure_empty,
      zero_lt_top, forall_const],
    fun _ => tendsto_const_nhds⟩

中文:
定理 finStronglyMeasurable_zero
  结论: {α β} {m : MeasurableSpace α} {μ : Measure α} [Zero β]
  证明: ⟨0, by
    simp only [Pi.zero_apply, SimpleFunc.coe_zero, support_zero, measure_empty,
      zero_lt_top, forall_const],
    fun _ => tendsto_const_nhds⟩

Depends on / 依赖: Pi.zero_apply, SimpleFunc, SimpleFunc.coe_zero, coe_zero, forall_const, measure_empty, support_zero, tendsto_const_nhds, zero_apply, zero_lt_top
-/
theorem finStronglyMeasurable_zero {α β} {m : MeasurableSpace α} {μ : Measure α} [Zero β]
    [TopologicalSpace β] : FinStronglyMeasurable (0 : α -> β) μ :=
  ⟨0, by
    simp only [Pi.zero_apply, SimpleFunc.coe_zero, support_zero, measure_empty,
      zero_lt_top, forall_const],
    fun _ => tendsto_const_nhds⟩

namespace FinStronglyMeasurable

variable {m0 : MeasurableSpace α} {μ : Measure α} {f g : α -> β}

section sequence

variable [Zero β] [TopologicalSpace β] (hf : FinStronglyMeasurable f μ)

/--
Definition of `noncomputable` / `noncomputable` 的定义

English:
definition noncomputable
  signature: def approx
  body: hf.choose

中文:
定义 noncomputable
  签名: def approx
  定义体: hf.choose
-/
protected noncomputable def approx : Nat -> α ->ₛ β :=
  hf.choose

/--
theorem `fin_support_approx` / 定理 `fin_support_approx`

English:
theorem fin_support_approx
  statement: forall n, μ (support (hf.approx n)) < ∞
  proof: hf.choose_spec.1

中文:
定理 fin_support_approx
  结论: 对任意 n, μ (support (hf.approx n)) < ∞
  证明: hf.choose_spec.1
-/
protected theorem fin_support_approx : forall n, μ (support (hf.approx n)) < ∞ :=
  hf.choose_spec.1

/--
theorem `tendsto_approx` / 定理 `tendsto_approx`

English:
theorem tendsto_approx
  statement: forall x, Tendsto (fun n => hf.approx n x) atTop (𝓝 (f x))
  proof: hf.choose_spec.2

中文:
定理 tendsto_approx
  结论: 对任意 x, Tendsto (fun n => hf.approx n x) atTop (𝓝 (f x))
  证明: hf.choose_spec.2
-/
protected theorem tendsto_approx : forall x, Tendsto (fun n => hf.approx n x) atTop (𝓝 (f x)) :=
  hf.choose_spec.2

end sequence

/-- A finitely strongly measurable function is strongly measurable. -/
@[fun_prop]
/--
theorem `stronglyMeasurable` / 定理 `stronglyMeasurable`

English:
theorem stronglyMeasurable
  statement: [Zero β] [TopologicalSpace β]
  proof: ⟨hf.approx, hf.tendsto_approx⟩

中文:
定理 stronglyMeasurable
  结论: [Zero β] [TopologicalSpace β]
  证明: ⟨hf.approx, hf.tendsto_approx⟩
-/
protected theorem stronglyMeasurable [Zero β] [TopologicalSpace β]
    (hf : FinStronglyMeasurable f μ) : StronglyMeasurable f :=
  ⟨hf.approx, hf.tendsto_approx⟩

/--
theorem `exists_set_sigmaFinite` / 定理 `exists_set_sigmaFinite`

English:
theorem exists_set_sigmaFinite
  statement: [Zero β] [TopologicalSpace β] [T2Space β]
  proof: by
  rcases hf with ⟨fs, hT_lt_top, h_approx⟩
  let T n := support (fs n)
  have hT_meas : forall n, MeasurableSet (T n) := fun n => SimpleFunc.measurableSet_support (fs n)
  let t := ⋃ n, T n
  refine ⟨t, MeasurableSet.iUnion hT_meas, ?_, ?_⟩
  · have h_fs_zero : forall n, forall x in tᶜ, fs n x = 

中文:
定理 exists_set_sigmaFinite
  结论: [Zero β] [TopologicalSpace β] [T2Space β]
  证明: by
  rcases hf with ⟨fs, hT_lt_top, h_approx⟩
  let T n := support (fs n)
  have hT_meas : forall n, MeasurableSet (T n) := fun n => SimpleFunc.measurableSet_support (fs n)
  let t := ⋃ n, T n
  refine ⟨t, MeasurableSet.iUnion hT_meas, ?_, ?_⟩
  · have h_fs_zero : forall n, forall x in tᶜ, fs n x = 

Depends on / 依赖: MeasurableSet, MeasurableSet.iUnion, Set.mem_compl_iff, Set.mem_iUnion, SimpleFunc, SimpleFunc.measurableSet_support, hT_lt_top, hT_meas, h_approx, h_fs_zero, iUnion, measurableSet_support, mem_compl_iff, mem_iUnion, not_exists, support, tendsto_nhds_unique
-/
theorem exists_set_sigmaFinite [Zero β] [TopologicalSpace β] [T2Space β]
    (hf : FinStronglyMeasurable f μ) :
    exists t, MeasurableSet t ∧ (forall x in tᶜ, f x = 0) ∧ SigmaFinite (μ.restrict t) := by
  rcases hf with ⟨fs, hT_lt_top, h_approx⟩
  let T n := support (fs n)
  have hT_meas : forall n, MeasurableSet (T n) := fun n => SimpleFunc.measurableSet_support (fs n)
  let t := ⋃ n, T n
  refine ⟨t, MeasurableSet.iUnion hT_meas, ?_, ?_⟩
  · have h_fs_zero : forall n, forall x in tᶜ, fs n x = 0 := by
      intro n x hxt
      rw [Set.mem_compl_iff]; rw [Set.mem_iUnion]; rw [not_exists] at hxt
      simpa [T] using hxt n
    refine fun x hxt => tendsto_nhds_unique (h_approx x) ?_
    rw [funext fun n => h_fs_zero n x hxt]
    exact tendsto_const_nhds
  · refine ⟨⟨⟨fun n => tᶜ union T n, fun _ => trivial, fun n => ?_, ?_⟩⟩⟩
    · rw [Measure.restrict_apply' (MeasurableSet.iUnion hT_meas), Set.union_inter_distrib_right,
        Set.compl_inter_self t, Set.empty_union]
      exact (measure_mono Set.inter_subset_left).trans_lt (hT_lt_top n)
    · rw [← Set.union_iUnion tᶜ T]
      exact Set.compl_union_self _

/--
theorem `measurable` / 定理 `measurable`

English:
theorem measurable
  statement: [Zero β] [TopologicalSpace β] [PseudoMetrizableSpace β]
  proof: hf.stronglyMeasurable.measurable

中文:
定理 measurable
  结论: [Zero β] [TopologicalSpace β] [PseudoMetrizableSpace β]
  证明: hf.stronglyMeasurable.measurable
-/
protected theorem measurable [Zero β] [TopologicalSpace β] [PseudoMetrizableSpace β]
    [MeasurableSpace β] [BorelSpace β] (hf : FinStronglyMeasurable f μ) : Measurable f :=
  hf.stronglyMeasurable.measurable

section Arithmetic

variable [TopologicalSpace β]

@[aesop safe 20 (rule_sets := [Measurable])]
/--
theorem `mul` / 定理 `mul`

English:
theorem mul
  statement: [MulZeroClass β] [ContinuousMul β] (hf : FinStronglyMeasurable f μ)
  proof: by
  refine
    ⟨fun n => hf.approx n * hg.approx n, ?_, fun x =>
      (hf.tendsto_approx x).mul (hg.tendsto_approx x)⟩
  intro n
  exact (measure_mono (support_mul_subset_left _ _)).trans_lt (hf.fin_support_approx n)

@[aesop safe 20 (rule_sets := [Measurable])]

中文:
定理 mul
  结论: [MulZeroClass β] [ContinuousMul β] (hf : FinStronglyMeasurable f μ)
  证明: by
  refine
    ⟨fun n => hf.approx n * hg.approx n, ?_, fun x =>
      (hf.tendsto_approx x).mul (hg.tendsto_approx x)⟩
  intro n
  exact (measure_mono (support_mul_subset_left _ _)).trans_lt (hf.fin_support_approx n)

@[aesop safe 20 (rule_sets := [Measurable])]
-/
protected theorem mul [MulZeroClass β] [ContinuousMul β] (hf : FinStronglyMeasurable f μ)
    (hg : FinStronglyMeasurable g μ) : FinStronglyMeasurable (f * g) μ := by
  refine
    ⟨fun n => hf.approx n * hg.approx n, ?_, fun x =>
      (hf.tendsto_approx x).mul (hg.tendsto_approx x)⟩
  intro n
  exact (measure_mono (support_mul_subset_left _ _)).trans_lt (hf.fin_support_approx n)

@[aesop safe 20 (rule_sets := [Measurable])]
/--
theorem `add` / 定理 `add`

English:
theorem add
  statement: [AddZeroClass β] [ContinuousAdd β] (hf : FinStronglyMeasurable f μ)
  proof: ⟨fun n => hf.approx n + hg.approx n, fun n =>
    (measure_mono (Function.support_add _ _)).trans_lt
      ((measure_union_le _ _).trans_lt
        (ENNReal.add_lt_top.mpr ⟨hf.fin_support_approx n, hg.fin_support_approx n⟩)),
    fun x => (hf.tendsto_approx x).add (hg.tendsto_approx x)⟩

@[measurabi

中文:
定理 add
  结论: [AddZeroClass β] [ContinuousAdd β] (hf : FinStronglyMeasurable f μ)
  证明: ⟨fun n => hf.approx n + hg.approx n, fun n =>
    (measure_mono (Function.support_add _ _)).trans_lt
      ((measure_union_le _ _).trans_lt
        (ENNReal.add_lt_top.mpr ⟨hf.fin_support_approx n, hg.fin_support_approx n⟩)),
    fun x => (hf.tendsto_approx x).add (hg.tendsto_approx x)⟩

@[measurabi
-/
protected theorem add [AddZeroClass β] [ContinuousAdd β] (hf : FinStronglyMeasurable f μ)
    (hg : FinStronglyMeasurable g μ) : FinStronglyMeasurable (f + g) μ :=
  ⟨fun n => hf.approx n + hg.approx n, fun n =>
    (measure_mono (Function.support_add _ _)).trans_lt
      ((measure_union_le _ _).trans_lt
        (ENNReal.add_lt_top.mpr ⟨hf.fin_support_approx n, hg.fin_support_approx n⟩)),
    fun x => (hf.tendsto_approx x).add (hg.tendsto_approx x)⟩

@[measurability]
/--
theorem `neg` / 定理 `neg`

English:
theorem neg
  given: [SubtractionMonoid β] [ContinuousNeg β] (hf : FinStronglyMeasurable f μ)
  proof: by
  refine ⟨fun n => -hf.approx n, fun n => ?_, fun x => (hf.tendsto_approx x).neg⟩
  suffices μ (Function.support fun x => -(hf.approx n) x) < ∞ by convert! this
  rw [Function.support_fun_neg (hf.approx n)]
  exact hf.fin_support_approx n

@[measurability]

中文:
定理 neg
  条件: [SubtractionMonoid β] [ContinuousNeg β] (hf : FinStronglyMeasurable f μ)
  证明: by
  refine ⟨fun n => -hf.approx n, fun n => ?_, fun x => (hf.tendsto_approx x).neg⟩
  suffices μ (Function.support fun x => -(hf.approx n) x) < ∞ by convert! this
  rw [Function.support_fun_neg (hf.approx n)]
  exact hf.fin_support_approx n

@[measurability]
-/
protected theorem neg [SubtractionMonoid β] [ContinuousNeg β] (hf : FinStronglyMeasurable f μ) :
    FinStronglyMeasurable (-f) μ := by
  refine ⟨fun n => -hf.approx n, fun n => ?_, fun x => (hf.tendsto_approx x).neg⟩
  suffices μ (Function.support fun x => -(hf.approx n) x) < ∞ by convert! this
  rw [Function.support_fun_neg (hf.approx n)]
  exact hf.fin_support_approx n

@[measurability]
/--
theorem `sub` / 定理 `sub`

English:
theorem sub
  statement: [SubtractionMonoid β] [ContinuousSub β] (hf : FinStronglyMeasurable f μ)
  proof: ⟨fun n => hf.approx n - hg.approx n, fun n =>
    (measure_mono (Function.support_sub _ _)).trans_lt
      ((measure_union_le _ _).trans_lt
        (ENNReal.add_lt_top.mpr ⟨hf.fin_support_approx n, hg.fin_support_approx n⟩)),
    fun x => (hf.tendsto_approx x).sub (hg.tendsto_approx x)⟩

@[measurabi

中文:
定理 sub
  结论: [SubtractionMonoid β] [ContinuousSub β] (hf : FinStronglyMeasurable f μ)
  证明: ⟨fun n => hf.approx n - hg.approx n, fun n =>
    (measure_mono (Function.support_sub _ _)).trans_lt
      ((measure_union_le _ _).trans_lt
        (ENNReal.add_lt_top.mpr ⟨hf.fin_support_approx n, hg.fin_support_approx n⟩)),
    fun x => (hf.tendsto_approx x).sub (hg.tendsto_approx x)⟩

@[measurabi
-/
protected theorem sub [SubtractionMonoid β] [ContinuousSub β] (hf : FinStronglyMeasurable f μ)
    (hg : FinStronglyMeasurable g μ) : FinStronglyMeasurable (f - g) μ :=
  ⟨fun n => hf.approx n - hg.approx n, fun n =>
    (measure_mono (Function.support_sub _ _)).trans_lt
      ((measure_union_le _ _).trans_lt
        (ENNReal.add_lt_top.mpr ⟨hf.fin_support_approx n, hg.fin_support_approx n⟩)),
    fun x => (hf.tendsto_approx x).sub (hg.tendsto_approx x)⟩

@[measurability]
/--
theorem `const_smul` / 定理 `const_smul`

English:
theorem const_smul
  statement: {𝕜} [TopologicalSpace 𝕜] [Zero β]
  proof: by
  refine ⟨fun n => c • hf.approx n, fun n => ?_, fun x => (hf.tendsto_approx x).const_smul c⟩
  rw [SimpleFunc.coe_smul]
  exact (measure_mono (support_const_smul_subset c _)).trans_lt (hf.fin_support_approx n)

中文:
定理 const_smul
  结论: {𝕜} [TopologicalSpace 𝕜] [Zero β]
  证明: by
  refine ⟨fun n => c • hf.approx n, fun n => ?_, fun x => (hf.tendsto_approx x).const_smul c⟩
  rw [SimpleFunc.coe_smul]
  exact (measure_mono (support_const_smul_subset c _)).trans_lt (hf.fin_support_approx n)
-/
protected theorem const_smul {𝕜} [TopologicalSpace 𝕜] [Zero β]
    [SMulZeroClass 𝕜 β] [ContinuousSMul 𝕜 β] (hf : FinStronglyMeasurable f μ) (c : 𝕜) :
    FinStronglyMeasurable (c • f) μ := by
  refine ⟨fun n => c • hf.approx n, fun n => ?_, fun x => (hf.tendsto_approx x).const_smul c⟩
  rw [SimpleFunc.coe_smul]
  exact (measure_mono (support_const_smul_subset c _)).trans_lt (hf.fin_support_approx n)

end Arithmetic

section Order

variable [TopologicalSpace β] [Zero β]

@[aesop safe 20 (rule_sets := [Measurable])]
/--
theorem `sup` / 定理 `sup`

English:
theorem sup
  statement: [SemilatticeSup β] [ContinuousSup β] (hf : FinStronglyMeasurable f μ)
  proof: by
  refine
    ⟨fun n => hf.approx n ⊔ hg.approx n, fun n => ?_, fun x =>
      (hf.tendsto_approx x).sup_nhds (hg.tendsto_approx x)⟩
  refine (measure_mono (support_sup _ _)).trans_lt ?_
  exact measure_union_lt_top_iff.mpr ⟨hf.fin_support_approx n, hg.fin_support_approx n⟩

@[aesop safe 20 (rule_

中文:
定理 sup
  结论: [SemilatticeSup β] [ContinuousSup β] (hf : FinStronglyMeasurable f μ)
  证明: by
  refine
    ⟨fun n => hf.approx n ⊔ hg.approx n, fun n => ?_, fun x =>
      (hf.tendsto_approx x).sup_nhds (hg.tendsto_approx x)⟩
  refine (measure_mono (support_sup _ _)).trans_lt ?_
  exact measure_union_lt_top_iff.mpr ⟨hf.fin_support_approx n, hg.fin_support_approx n⟩

@[aesop safe 20 (rule_
-/
protected theorem sup [SemilatticeSup β] [ContinuousSup β] (hf : FinStronglyMeasurable f μ)
    (hg : FinStronglyMeasurable g μ) : FinStronglyMeasurable (f ⊔ g) μ := by
  refine
    ⟨fun n => hf.approx n ⊔ hg.approx n, fun n => ?_, fun x =>
      (hf.tendsto_approx x).sup_nhds (hg.tendsto_approx x)⟩
  refine (measure_mono (support_sup _ _)).trans_lt ?_
  exact measure_union_lt_top_iff.mpr ⟨hf.fin_support_approx n, hg.fin_support_approx n⟩

@[aesop safe 20 (rule_sets := [Measurable])]
/--
theorem `inf` / 定理 `inf`

English:
theorem inf
  statement: [SemilatticeInf β] [ContinuousInf β] (hf : FinStronglyMeasurable f μ)
  proof: by
  refine
    ⟨fun n => hf.approx n ⊓ hg.approx n, fun n => ?_, fun x =>
      (hf.tendsto_approx x).inf_nhds (hg.tendsto_approx x)⟩
  refine (measure_mono (support_inf _ _)).trans_lt ?_
  exact measure_union_lt_top_iff.mpr ⟨hf.fin_support_approx n, hg.fin_support_approx n⟩

中文:
定理 inf
  结论: [SemilatticeInf β] [ContinuousInf β] (hf : FinStronglyMeasurable f μ)
  证明: by
  refine
    ⟨fun n => hf.approx n ⊓ hg.approx n, fun n => ?_, fun x =>
      (hf.tendsto_approx x).inf_nhds (hg.tendsto_approx x)⟩
  refine (measure_mono (support_inf _ _)).trans_lt ?_
  exact measure_union_lt_top_iff.mpr ⟨hf.fin_support_approx n, hg.fin_support_approx n⟩
-/
protected theorem inf [SemilatticeInf β] [ContinuousInf β] (hf : FinStronglyMeasurable f μ)
    (hg : FinStronglyMeasurable g μ) : FinStronglyMeasurable (f ⊓ g) μ := by
  refine
    ⟨fun n => hf.approx n ⊓ hg.approx n, fun n => ?_, fun x =>
      (hf.tendsto_approx x).inf_nhds (hg.tendsto_approx x)⟩
  refine (measure_mono (support_inf _ _)).trans_lt ?_
  exact measure_union_lt_top_iff.mpr ⟨hf.fin_support_approx n, hg.fin_support_approx n⟩

end Order

end FinStronglyMeasurable

/--
theorem `finStronglyMeasurable_iff_stronglyMeasurable_and_exists_set_sigmaFinite` / 定理 `finStronglyMeasurable_iff_stronglyMeasurable_and_exists_set_sigmaFinite`

English:
theorem finStronglyMeasurable_iff_stronglyMeasurable_and_exists_set_sigmaFinite
  statement: {α β} {f : α -> β}
  proof: ⟨fun hf => ⟨hf.stronglyMeasurable, hf.exists_set_sigmaFinite⟩, fun hf =>
    hf.1.finStronglyMeasurable_of_set_sigmaFinite hf.2.choose_spec.1 hf.2.choose_spec.2.1
      hf.2.choose_spec.2.2⟩

中文:
定理 finStronglyMeasurable_iff_stronglyMeasurable_and_exists_set_sigmaFinite
  结论: {α β} {f : α -> β}
  证明: ⟨fun hf => ⟨hf.stronglyMeasurable, hf.exists_set_sigmaFinite⟩, fun hf =>
    hf.1.finStronglyMeasurable_of_set_sigmaFinite hf.2.choose_spec.1 hf.2.choose_spec.2.1
      hf.2.choose_spec.2.2⟩

Depends on / 依赖: choose_spec, exists_set_sigmaFinite, finStronglyMeasurable_of_set_sigmaFinite, hf.exists_set_sigmaFinite, hf.stronglyMeasurable, stronglyMeasurable
-/
theorem finStronglyMeasurable_iff_stronglyMeasurable_and_exists_set_sigmaFinite {α β} {f : α -> β}
    [TopologicalSpace β] [T2Space β] [Zero β] {_ : MeasurableSpace α} {μ : Measure α} :
    FinStronglyMeasurable f μ ↔
      StronglyMeasurable f ∧
        exists t, MeasurableSet t ∧ (forall x in tᶜ, f x = 0) ∧ SigmaFinite (μ.restrict t) :=
  ⟨fun hf => ⟨hf.stronglyMeasurable, hf.exists_set_sigmaFinite⟩, fun hf =>
    hf.1.finStronglyMeasurable_of_set_sigmaFinite hf.2.choose_spec.1 hf.2.choose_spec.2.1
      hf.2.choose_spec.2.2⟩

section SecondCountableTopology

variable {G : Type*} [SeminormedAddCommGroup G] [MeasurableSpace G] [BorelSpace G]
  [SecondCountableTopology G] {f : α -> G}

/--
theorem `finStronglyMeasurable_iff_measurable` / 定理 `finStronglyMeasurable_iff_measurable`

English:
theorem finStronglyMeasurable_iff_measurable
  statement: {_m0 : MeasurableSpace α} (μ : Measure α)
  proof: ⟨fun h => h.measurable, fun h => (Measurable.stronglyMeasurable h).finStronglyMeasurable μ⟩

中文:
定理 finStronglyMeasurable_iff_measurable
  结论: {_m0 : MeasurableSpace α} (μ : Measure α)
  证明: ⟨fun h => h.measurable, fun h => (Measurable.stronglyMeasurable h).finStronglyMeasurable μ⟩

Depends on / 依赖: Measurable, Measurable.stronglyMeasurable, finStronglyMeasurable, h.measurable, measurable, stronglyMeasurable
-/
theorem finStronglyMeasurable_iff_measurable {_m0 : MeasurableSpace α} (μ : Measure α)
    [SigmaFinite μ] : FinStronglyMeasurable f μ ↔ Measurable f :=
  ⟨fun h => h.measurable, fun h => (Measurable.stronglyMeasurable h).finStronglyMeasurable μ⟩

/-- In a space with second countable topology and a sigma-finite measure, a measurable function
is `FinStronglyMeasurable`. -/
@[aesop 90% apply (rule_sets := [Measurable])]
/--
theorem `finStronglyMeasurable_of_measurable` / 定理 `finStronglyMeasurable_of_measurable`

English:
theorem finStronglyMeasurable_of_measurable
  statement: {_m0 : MeasurableSpace α} (μ : Measure α)
  proof: (finStronglyMeasurable_iff_measurable μ).mpr hf

中文:
定理 finStronglyMeasurable_of_measurable
  结论: {_m0 : MeasurableSpace α} (μ : Measure α)
  证明: (finStronglyMeasurable_iff_measurable μ).mpr hf

Depends on / 依赖: finStronglyMeasurable_iff_measurable
-/
theorem finStronglyMeasurable_of_measurable {_m0 : MeasurableSpace α} (μ : Measure α)
    [SigmaFinite μ] (hf : Measurable f) : FinStronglyMeasurable f μ :=
  (finStronglyMeasurable_iff_measurable μ).mpr hf

end SecondCountableTopology

/--
theorem `measurable_uncurry_of_continuous_of_measurable` / 定理 `measurable_uncurry_of_continuous_of_measurable`

English:
theorem measurable_uncurry_of_continuous_of_measurable
  statement: {α β ι : Type*} [TopologicalSpace ι]
  proof: by
  obtain ⟨t_sf, ht_sf⟩ :
    exists t : Nat -> SimpleFunc ι ι, forall j x, Tendsto (fun n => u (t n j) x) atTop (𝓝 <| u j x) := by
    have h_str_meas : StronglyMeasurable (id : ι -> ι) := stronglyMeasurable_id
    refine ⟨h_str_meas.approx, fun j x => ?_⟩
    exact ((hu_cont x).tendsto j).comp (

中文:
定理 measurable_uncurry_of_continuous_of_measurable
  结论: {α β ι : 类型} [TopologicalSpace ι]
  证明: by
  obtain ⟨t_sf, ht_sf⟩ :
    exists t : Nat -> SimpleFunc ι ι, forall j x, Tendsto (fun n => u (t n j) x) atTop (𝓝 <| u j x) := by
    have h_str_meas : StronglyMeasurable (id : ι -> ι) := stronglyMeasurable_id
    refine ⟨h_str_meas.approx, fun j x => ?_⟩
    exact ((hu_cont x).tendsto j).comp (

Depends on / 依赖: SimpleFunc, StronglyMeasurable, Tendsto, approx, h_str_meas, h_str_meas.approx, h_str_meas.tendsto_approx, h_tendsto, ht_sf, hu_cont, measurab, p.fst, p.snd, stronglyMeasurable_id, t_sf, tendsto, tendsto_approx, tendsto_pi_nhds
-/
theorem measurable_uncurry_of_continuous_of_measurable {α β ι : Type*} [TopologicalSpace ι]
    [MetrizableSpace ι] [MeasurableSpace ι] [SecondCountableTopology ι] [OpensMeasurableSpace ι]
    {mβ : MeasurableSpace β} [TopologicalSpace β] [PseudoMetrizableSpace β] [BorelSpace β]
    {m : MeasurableSpace α} {u : ι -> α -> β} (hu_cont : forall x, Continuous fun i => u i x)
    (h : forall i, Measurable (u i)) : Measurable (Function.uncurry u) := by
  obtain ⟨t_sf, ht_sf⟩ :
    exists t : Nat -> SimpleFunc ι ι, forall j x, Tendsto (fun n => u (t n j) x) atTop (𝓝 <| u j x) := by
    have h_str_meas : StronglyMeasurable (id : ι -> ι) := stronglyMeasurable_id
    refine ⟨h_str_meas.approx, fun j x => ?_⟩
    exact ((hu_cont x).tendsto j).comp (h_str_meas.tendsto_approx j)
  let U (n : Nat) (p : ι × α) := u (t_sf n p.fst) p.snd
  have h_tendsto : Tendsto U atTop (𝓝 fun p => u p.fst p.snd) := by
    rw [tendsto_pi_nhds]
    exact fun p => ht_sf p.fst p.snd
  refine measurable_of_tendsto_metrizable (fun n => ?_) h_tendsto
  have h_meas : Measurable fun p : (t_sf n).range × α => u (↑p.fst) p.snd := by
    have :
      (fun p : ↥(t_sf n).range × α => u (↑p.fst) p.snd) =
        (fun p : α × (t_sf n).range => u (↑p.snd) p.fst) ∘ Prod.swap :=
      rfl
    rw [this]; rw [@measurable_swap_iff α (↥(t_sf n).range) β m]
    exact measurable_from_prod_countable_left fun j => h j
  have :
    (fun p : ι × α => u (t_sf n p.fst) p.snd) =
      (fun p : ↥(t_sf n).range × α => u p.fst p.snd) ∘ fun p : ι × α =>
        (⟨t_sf n p.fst, SimpleFunc.mem_range_self _ _⟩, p.snd) :=
    rfl
  simp_rw [U, this]
  refine h_meas.comp (Measurable.prodMk ?_ measurable_snd)
  exact ((t_sf n).measurable.comp measurable_fst).subtype_mk

/--
theorem `stronglyMeasurable_uncurry_of_continuous_of_stronglyMeasurable` / 定理 `stronglyMeasurable_uncurry_of_continuous_of_stronglyMeasurable`

English:
theorem stronglyMeasurable_uncurry_of_continuous_of_stronglyMeasurable
  statement: {α β ι : Type*}
  proof: by
  borelize β
  obtain ⟨t_sf, ht_sf⟩ :
    exists t : Nat -> SimpleFunc ι ι, forall j x, Tendsto (fun n => u (t n j) x) atTop (𝓝 <| u j x) := by
    have h_str_meas : StronglyMeasurable (id : ι -> ι) := stronglyMeasurable_id
    refine ⟨h_str_meas.approx, fun j x => ?_⟩
    exact ((hu_cont x).tend

中文:
定理 stronglyMeasurable_uncurry_of_continuous_of_stronglyMeasurable
  结论: {α β ι : 类型}
  证明: by
  borelize β
  obtain ⟨t_sf, ht_sf⟩ :
    exists t : Nat -> SimpleFunc ι ι, forall j x, Tendsto (fun n => u (t n j) x) atTop (𝓝 <| u j x) := by
    have h_str_meas : StronglyMeasurable (id : ι -> ι) := stronglyMeasurable_id
    refine ⟨h_str_meas.approx, fun j x => ?_⟩
    exact ((hu_cont x).tend

Depends on / 依赖: SimpleFunc, StronglyMeasurable, Tendsto, approx, borelize, h_str_meas, h_str_meas.approx, h_str_meas.tendsto_approx, h_tendsto, ht_sf, hu_cont, p.fst, p.snd, stronglyMeasurable_id, t_sf, tendsto, tendsto_approx, tendsto_pi_nhds
-/
theorem stronglyMeasurable_uncurry_of_continuous_of_stronglyMeasurable {α β ι : Type*}
    [TopologicalSpace ι] [MetrizableSpace ι] [MeasurableSpace ι] [SecondCountableTopology ι]
    [OpensMeasurableSpace ι] [TopologicalSpace β] [PseudoMetrizableSpace β] [MeasurableSpace α]
    {u : ι -> α -> β} (hu_cont : forall x, Continuous fun i => u i x) (h : forall i, StronglyMeasurable (u i)) :
    StronglyMeasurable (Function.uncurry u) := by
  borelize β
  obtain ⟨t_sf, ht_sf⟩ :
    exists t : Nat -> SimpleFunc ι ι, forall j x, Tendsto (fun n => u (t n j) x) atTop (𝓝 <| u j x) := by
    have h_str_meas : StronglyMeasurable (id : ι -> ι) := stronglyMeasurable_id
    refine ⟨h_str_meas.approx, fun j x => ?_⟩
    exact ((hu_cont x).tendsto j).comp (h_str_meas.tendsto_approx j)
  let U (n : Nat) (p : ι × α) := u (t_sf n p.fst) p.snd
  have h_tendsto : Tendsto U atTop (𝓝 fun p => u p.fst p.snd) := by
    rw [tendsto_pi_nhds]
    exact fun p => ht_sf p.fst p.snd
  refine stronglyMeasurable_of_tendsto _ (fun n => ?_) h_tendsto
  have h_str_meas : StronglyMeasurable fun p : (t_sf n).range × α => u (↑p.fst) p.snd := by
    refine stronglyMeasurable_iff_measurable_separable.2 ⟨?_, ?_⟩
    · have :
        (fun p : ↥(t_sf n).range × α => u (↑p.fst) p.snd) =
          (fun p : α × (t_sf n).range => u (↑p.snd) p.fst) ∘ Prod.swap :=
        rfl
      rw [this]; rw [measurable_swap_iff]
      exact measurable_from_prod_countable_left fun j => (h j).measurable
    · have : IsSeparable (⋃ i : (t_sf n).range, range (u i)) :=
        .iUnion fun i => (h i).isSeparable_range
      apply this.mono
      rintro _ ⟨⟨i, x⟩, rfl⟩
      simp only [mem_iUnion, mem_range]
      exact ⟨i, x, rfl⟩
  have :
    (fun p : ι × α => u (t_sf n p.fst) p.snd) =
      (fun p : ↥(t_sf n).range × α => u p.fst p.snd) ∘ fun p : ι × α =>
        (⟨t_sf n p.fst, SimpleFunc.mem_range_self _ _⟩, p.snd) :=
    rfl
  simp_rw [U, this]
  refine h_str_meas.comp_measurable (Measurable.prodMk ?_ measurable_snd)
  exact ((t_sf n).measurable.comp measurable_fst).subtype_mk

end MeasureTheory
