/-
Copyright (c) 2018 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Johannes Hölzl
-/
module

public import Mathlib.MeasureTheory.Integral.Lebesgue.Markov
public import Mathlib.MeasureTheory.Integral.Lebesgue.Sub

/-!
# Dominated convergence theorem

Lebesgue's dominated convergence theorem states that the limit and Lebesgue integral of
a sequence of (almost everywhere) measurable functions can be swapped if the functions are
pointwise dominated by a fixed function. This file provides a few variants of the result.
-/

public section

open Filter ENNReal Topology

namespace MeasureTheory

variable {α : Type*} [MeasurableSpace α] {μ : Measure α}

/-
**MeasureTheory.limsup_lintegral_le** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：limsup_lintegral_le {f : Nat -> α -> Real>=0∞} (g : α -> Real>=0∞) (hf_mea
s : forall n, Measurable (f n)) (h_bound : forall n, f n <=ᵐ[μ] g) (h_fin : ∫⁻ a
, g a ∂μ != ∞) : limsup (fun n => ∫⁻ a, f n a ∂μ) atTop <= ∫⁻ a, limsup (fun n =
> f n a) atTop ∂μ
参数：g : α -> Real>=0∞；hf_meas : forall n, Measurable (f n)；h_bound : forall n, f 
n <=ᵐ[μ] g；h_fin : ∫⁻ a, g a ∂μ != ∞。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `Filter.limsup_eq_iInf_iSup_of_nat`：limsup_eq_iInf_iSup_of_nat {u : Nat -
> α} : limsup u atTop = ⨅ n : Nat, ⨆ i >= n, u i
· 使用定理 `iInf_mono`：∀ {α : Type u_1} {ι : Sort u_4} [inst : CompleteLattice α] {f
 g : ι → α}, (∀ (i : ι), g i ≤ f i) → iInf g ≤ iInf f
· 使用定理 `MeasureTheory.iSup₂_lintegral_le`：iSup₂_lintegral_le {ι : Sort*} {ι' : ι
 -> Sort*} (f : forall i, ι' i -> α -> Real>=0∞) : ⨆ (i) (j), ∫⁻ a, f i j a ∂μ <
= ∫⁻ a, ⨆ (i) (j), f i…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.lintegral_iInf`：lintegral_iInf {f : Nat -> α -> Real>=0∞} 
(h_meas : forall n, Measurable (f n)) (h_anti : Antitone f) (h_fin : ∫⁻ a, f 0 a
 ∂μ != ∞) : ∫⁻ a, …
· 使用定理 `Measurable.biSup`：Measurable.biSup {ι} (s : Set ι) {f : ι -> δ -> α} (hs
 : s.Countable) (hf : forall i in s, Measurable (f i)) : Measurable fun b => ⨆ i
 in s,…
· 使用定理 `ENNReal.instOrderTopology`：OrderTopology ENNReal
· 使用定理 `ENNReal.instSecondCountableTopology`：SecondCountableTopology ENNReal
· 使用定理 `Set.to_countable`：to_countable (s : Set α) [Countable s] : s.Countable
· 使用定理 `Subtype.countable`：∀ {α : Sort u} [Countable α] {p : α → Prop}, Countabl
e { x // p x }
· 使用定理 `instCountableNat`：Countable ℕ
· 使用定理 `iSup_le_iSup_of_subset`：iSup_le_iSup_of_subset {f : β -> α} {s t : Set β
} : s subseteq t -> ⨆ x in s, f x <= ⨆ x in t, f x
· 使用引理 `le_trans`：le_trans : a <= b -> b <= c -> a <= c
· 使用定理 `ne_top_of_le_ne_top`：ne_top_of_le_ne_top (hb : b != ⊤) (hab : a <= b) : 
a != ⊤
· 使用定理 `MeasureTheory.lintegral_mono_ae`：lintegral_mono_ae {f g : α -> Real>=0∞}
 (h : forallᵐ a ∂μ, f a <= g a) : ∫⁻ a, f a ∂μ <= ∫⁻ a, g a ∂μ
· 使用定理 `Filter.Eventually.mono`：∀ {α : Type u} {p q : α → Prop} {f : Filter α}, 
(∀ᶠ (x : α) in f, p x) → (∀ (x : α), p x → q x) → ∀ᶠ (x : α) in f, q x
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `MeasureTheory.ae_all_iff`：ae_all_iff {ι : Sort*} [Countable ι] {p : α ->
 ι -> Prop} : (forallᵐ a ∂μ, forall i, p a i) ↔ forall i, forallᵐ a ∂μ, p a i
· 使用定理 `iSup_le`：iSup_le (h : forall i, f i <= a) : iSup f <= a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem limsup_lintegral_le {f : ℕ → α → ℝ≥0∞} (g : α → ℝ≥0∞) (hf_meas : ∀ n, Measurable (f n))
    (h_bound : ∀ n, f n ≤ᵐ[μ] g) (h_fin : ∫⁻ a, g a ∂μ ≠ ∞) :
    limsup (fun n => ∫⁻ a, f n a ∂μ) atTop ≤ ∫⁻ a, limsup (fun n => f n a) atTop ∂μ :=
  calc
    limsup (fun n => ∫⁻ a, f n a ∂μ) atTop = ⨅ n : ℕ, ⨆ i ≥ n, ∫⁻ a, f i a ∂μ :=
      limsup_eq_iInf_iSup_of_nat
    _ ≤ ⨅ n : ℕ, ∫⁻ a, ⨆ i ≥ n, f i a ∂μ := iInf_mono fun _ => iSup₂_lintegral_le _
    _ = ∫⁻ a, ⨅ n : ℕ, ⨆ i ≥ n, f i a ∂μ := by
      refine (lintegral_iInf ?_ ?_ ?_).symm
      · intro n
        exact .biSup _ (Set.to_countable _) (fun i _ ↦ hf_meas i)
      · intro n m hnm a
        exact iSup_le_iSup_of_subset fun i hi => le_trans hnm hi
      · refine ne_top_of_le_ne_top h_fin (lintegral_mono_ae ?_)
        refine (ae_all_iff.2 h_bound).mono fun n hn => ?_
        exact iSup_le fun i => iSup_le fun _ => hn i
    _ = ∫⁻ a, limsup (fun n => f n a) atTop ∂μ := by simp only [limsup_eq_iInf_iSup_of_nat]

/-- **Dominated convergence theorem** for nonnegative `Measurable` functions. -/
/-
**MeasureTheory.tendsto_lintegral_of_dominated_convergence** 是 Mathlib 中的一个定理，位于
命名空间 `MeasureTheory`。
形式化陈述：tendsto_lintegral_of_dominated_convergence {F : Nat -> α -> Real>=0∞} {f :
 α -> Real>=0∞} (bound : α -> Real>=0∞) (hF_meas : forall n, Measurable (F n)) (
h_bound : forall n, F n <=ᵐ[μ] bound) (h_fin : ∫⁻ a, bound a ∂μ != ∞) (h_lim : f
orallᵐ a ∂μ, Tendsto (fun n => F n a) atTop (𝓝 (f a))) : Tendsto (fun n => ∫⁻ a,
 F n a ∂μ) atTop (𝓝 (∫⁻ a, f a ∂μ))
参数：bound : α -> Real>=0∞；hF_meas : forall n, Measurable (F n)；h_bound : forall n
, F n <=ᵐ[μ] bound；h_fin : ∫⁻ a, bound a ∂μ != ∞；h_lim : forallᵐ a ∂μ, Tendsto (
fun n => F n a) atTop (𝓝 (f a))。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `tendsto_of_le_liminf_of_limsup_le`：tendsto_of_le_liminf_of_limsup_le {f 
: Filter β} {u : β -> α} {a : α} (hinf : a <= liminf u f) (hsup : limsup u f <= 
a) (h : f.IsBoundedUnde…
· 使用定理 `ENNReal.instOrderTopology`：OrderTopology ENNReal
· 使用定理 `MeasureTheory.lintegral_congr_ae`：lintegral_congr_ae {f g : α -> Real>=0
∞} (h : f =ᵐ[μ] g) : ∫⁻ a, f a ∂μ = ∫⁻ a, g a ∂μ
· 使用定理 `Filter.Eventually.mono`：∀ {α : Type u} {p q : α → Prop} {f : Filter α}, 
(∀ᶠ (x : α) in f, p x) → (∀ (x : α), p x → q x) → ∀ᶠ (x : α) in f, q x
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Filter.Tendsto.liminf_eq`：Filter.Tendsto.liminf_eq {f : Filter β} {u : β
 -> α} {a : α} [NeBot f] (h : Tendsto u f (𝓝 a)) : liminf u f = a
· 使用定理 `instIsDirectedOrder`：∀ {R : Type u_3} [inst : Semiring R] [inst_1 : Part
ialOrder R] [IsOrderedRing R] [Archimedean R], IsDirectedOrder R
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `instArchimedeanNat`：Archimedean ℕ
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `MeasureTheory.lintegral_liminf_le`：lintegral_liminf_le {ι : Type*} {f : 
ι -> α -> Real>=0∞} {u : Filter ι} [IsCountablyGenerated u] (h_meas : forall i, 
Measurable (f i)) : ∫⁻ …
· 使用定理 `instDiscreteTopologyNat`：DiscreteTopology ℕ
· 使用定理 `TopologicalSpace.SecondCountableTopology.to_separableSpace`：∀ {α : Type 
u} [t : TopologicalSpace α] [SecondCountableTopology α], TopologicalSpace.Separa
bleSpace α
· 使用定理 `TopologicalSpace.instSecondCountableTopologyOfLindelofSpaceOfPseudoMetri
zableSpace`：∀ (X : Type u_5) [inst : TopologicalSpace X] [LindelofSpace X] [Topo
logicalSpace.PseudoMetrizableSpace X],   SecondCountableTopology X
· 使用定理 `Countable.LindelofSpace`：∀ {X : Type u} [inst : TopologicalSpace X] [Cou
ntable X], LindelofSpace X
· 使用定理 `instCountableNat`：Countable ℕ
· 使用定理 `PseudoEMetricSpace.pseudoMetrizableSpace`：∀ {α : Type u_2} [inst : Pseud
oEMetricSpace α], TopologicalSpace.PseudoMetrizableSpace α
· 使用定理 `MeasureTheory.limsup_lintegral_le`：limsup_lintegral_le {f : Nat -> α -> 
Real>=0∞} (g : α -> Real>=0∞) (hf_meas : forall n, Measurable (f n)) (h_bound : 
forall n, f n <=ᵐ[μ] g)…
· 使用定理 `Filter.Tendsto.limsup_eq`：Filter.Tendsto.limsup_eq {f : Filter β} {u : β
 -> α} {a : α} [NeBot f] (h : Tendsto u f (𝓝 a)) : limsup u f = a
· 使用定理 `Filter.isBounded_le_of_top`：isBounded_le_of_top [LE α] [OrderTop α] {f :
 Filter α} : f.IsBounded (· <= ·)
· 使用定理 `Filter.isBounded_ge_of_bot`：∀ {α : Type u_1} [inst : LE α] [OrderBot α] 
{f : Filter α}, Filter.IsBounded (fun x1 x2 => x2 ≤ x1) f

--- 原说明 ---
**Dominated convergence theorem** for nonnegative `Measurable` functions.
-/
theorem tendsto_lintegral_of_dominated_convergence {F : ℕ → α → ℝ≥0∞} {f : α → ℝ≥0∞}
    (bound : α → ℝ≥0∞) (hF_meas : ∀ n, Measurable (F n)) (h_bound : ∀ n, F n ≤ᵐ[μ] bound)
    (h_fin : ∫⁻ a, bound a ∂μ ≠ ∞) (h_lim : ∀ᵐ a ∂μ, Tendsto (fun n => F n a) atTop (𝓝 (f a))) :
    Tendsto (fun n => ∫⁻ a, F n a ∂μ) atTop (𝓝 (∫⁻ a, f a ∂μ)) :=
  tendsto_of_le_liminf_of_limsup_le
    (calc
      ∫⁻ a, f a ∂μ = ∫⁻ a, liminf (fun n : ℕ => F n a) atTop ∂μ :=
        lintegral_congr_ae <| h_lim.mono fun _ h => h.liminf_eq.symm
      _ ≤ liminf (fun n => ∫⁻ a, F n a ∂μ) atTop := lintegral_liminf_le hF_meas)
    (calc
      limsup (fun n : ℕ => ∫⁻ a, F n a ∂μ) atTop ≤ ∫⁻ a, limsup (fun n => F n a) atTop ∂μ :=
        limsup_lintegral_le _ hF_meas h_bound h_fin
      _ = ∫⁻ a, f a ∂μ := lintegral_congr_ae <| h_lim.mono fun _ h => h.limsup_eq)

/-- **Dominated convergence theorem** for nonnegative `AEMeasurable` functions. -/
/-
**MeasureTheory.tendsto_lintegral_of_dominated_convergence'** 是 Mathlib 中的一个定理，位
于命名空间 `MeasureTheory`。
形式化陈述：tendsto_lintegral_of_dominated_convergence' {F : Nat -> α -> Real>=0∞} {f 
: α -> Real>=0∞} (bound : α -> Real>=0∞) (hF_meas : forall n, AEMeasurable (F n)
 μ) (h_bound : forall n, F n <=ᵐ[μ] bound) (h_fin : ∫⁻ a, bound a ∂μ != ∞) (h_li
m : forallᵐ a ∂μ, Tendsto (fun n => F n a) atTop (𝓝 (f a))) : Tendsto (fun n => 
∫⁻ a, F n a ∂μ) atTop (𝓝 (∫⁻ a, f a ∂μ))
参数：bound : α -> Real>=0∞；hF_meas : forall n, AEMeasurable (F n) μ；h_bound : fora
ll n, F n <=ᵐ[μ] bound；h_fin : ∫⁻ a, bound a ∂μ != ∞；h_lim : forallᵐ a ∂μ, Tends
to (fun n => F n a) atTop (𝓝 (f a))。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `MeasureTheory.lintegral_congr_ae`：lintegral_congr_ae {f g : α -> Real>=0
∞} (h : f =ᵐ[μ] g) : ∫⁻ a, f a ∂μ = ∫⁻ a, g a ∂μ
· 使用定理 `AEMeasurable.ae_eq_mk`：ae_eq_mk (h : AEMeasurable f μ) : f =ᵐ[μ] h.mk f
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `MeasureTheory.tendsto_lintegral_of_dominated_convergence`：tendsto_linteg
ral_of_dominated_convergence {F : Nat -> α -> Real>=0∞} {f : α -> Real>=0∞} (bou
nd : α -> Real>=0∞) (hF_meas : forall n, Measu…
· 使用定理 `AEMeasurable.measurable_mk`：measurable_mk (h : AEMeasurable f μ) : Measu
rable (h.mk f)
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `Filter.EventuallyEq.symm`：∀ {α : Type u} {β : Type v} {f g : α → β} {l :
 Filter α}, f =ᶠ[l] g → g =ᶠ[l] f
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `MeasureTheory.ae_all_iff`：ae_all_iff {ι : Sort*} [Countable ι] {p : α ->
 ι -> Prop} : (forallᵐ a ∂μ, forall i, p a i) ↔ forall i, forallᵐ a ∂μ, p a i
· 使用定理 `instCountableNat`：Countable ℕ

--- 原说明 ---
**Dominated convergence theorem** for nonnegative `AEMeasurable` functions.
-/
theorem tendsto_lintegral_of_dominated_convergence' {F : ℕ → α → ℝ≥0∞} {f : α → ℝ≥0∞}
    (bound : α → ℝ≥0∞) (hF_meas : ∀ n, AEMeasurable (F n) μ) (h_bound : ∀ n, F n ≤ᵐ[μ] bound)
    (h_fin : ∫⁻ a, bound a ∂μ ≠ ∞) (h_lim : ∀ᵐ a ∂μ, Tendsto (fun n => F n a) atTop (𝓝 (f a))) :
    Tendsto (fun n => ∫⁻ a, F n a ∂μ) atTop (𝓝 (∫⁻ a, f a ∂μ)) := by
  have : ∀ n, ∫⁻ a, F n a ∂μ = ∫⁻ a, (hF_meas n).mk (F n) a ∂μ := fun n =>
    lintegral_congr_ae (hF_meas n).ae_eq_mk
  simp_rw [this]
  apply
    tendsto_lintegral_of_dominated_convergence bound (fun n => (hF_meas n).measurable_mk) _ h_fin
  · have : ∀ n, ∀ᵐ a ∂μ, (hF_meas n).mk (F n) a = F n a := fun n => (hF_meas n).ae_eq_mk.symm
    have : ∀ᵐ a ∂μ, ∀ n, (hF_meas n).mk (F n) a = F n a := ae_all_iff.mpr this
    filter_upwards [this, h_lim] with a H H'
    simp_rw [H]
    exact H'
  · intro n
    filter_upwards [h_bound n, (hF_meas n).ae_eq_mk] with a H H'
    rwa [H'] at H

/-- **Dominated convergence theorem** for filters with a countable basis and
AEMeasurable functions. -/
/-
**MeasureTheory.tendsto_lintegral_filter_of_dominated_convergence'** 是 Mathlib 中
的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：tendsto_lintegral_filter_of_dominated_convergence' {ι} {l : Filter ι} [l.I
sCountablyGenerated] {F : ι -> α -> Real>=0∞} {f : α -> Real>=0∞} (bound : α -> 
Real>=0∞) (hF_meas : forallᶠ n in l, AEMeasurable (F n) μ) (h_bound : forallᶠ n 
in l, forallᵐ a ∂μ, F n a <= bound a) (h_fin : ∫⁻ a, bound a ∂μ != ∞) (h_lim : f
orallᵐ a ∂μ, Tendsto (fun n => F n a) l (𝓝 (f a))) : Tendsto (fun n => ∫⁻ a, F n
 a ∂μ) l (𝓝 <| ∫⁻ a, f a ∂μ)
参数：bound : α -> Real>=0∞；hF_meas : forallᶠ n in l, AEMeasurable (F n) μ；h_bound 
: forallᶠ n in l, forallᵐ a ∂μ, F n a <= bound a；h_fin : ∫⁻ a, bound a ∂μ != ∞；h
_lim : forallᵐ a ∂μ, Tendsto (fun n => F n a) l (𝓝 (f a))。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Filter.tendsto_iff_seq_tendsto`：tendsto_iff_seq_tendsto {f : α -> β} {k 
: Filter α} {l : Filter β} [k.IsCountablyGenerated] : Tendsto f k l ↔ forall x :
 Nat -> α, Tendsto x…
· 使用定理 `Filter.tendsto_atTop'`：tendsto_atTop' : Tendsto f atTop l ↔ forall s in 
l, exists a, forall b, a <= b -> f b in s
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `instIsDirectedOrder`：∀ {R : Type u_3} [inst : Semiring R] [inst_1 : Part
ialOrder R] [IsOrderedRing R] [Archimedean R], IsDirectedOrder R
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `instArchimedeanNat`：Archimedean ℕ
· 使用定理 `Filter.inter_mem`：inter_mem (hs : s in f) (ht : t in f) : s inter t in f
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Filter.tendsto_add_atTop_iff_nat`：tendsto_add_atTop_iff_nat {f : Nat -> 
α} {l : Filter α} (k : Nat) : Tendsto (fun n => f (n + k)) atTop l ↔ Tendsto f a
tTop l
· 使用定理 `MeasureTheory.tendsto_lintegral_of_dominated_convergence'`：tendsto_linte
gral_of_dominated_convergence' {F : Nat -> α -> Real>=0∞} {f : α -> Real>=0∞} (b
ound : α -> Real>=0∞) (hF_meas : forall n, AEMe…
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Nat.le_add_left`：∀ (n m : ℕ), n ≤ m + n
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Filter.Eventually.mono`：∀ {α : Type u} {p q : α → Prop} {f : Filter α}, 
(∀ᶠ (x : α) in f, p x) → (∀ (x : α), p x → q x) → ∀ᶠ (x : α) in f, q x
· 使用定理 `Filter.Tendsto.comp`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {f :
 α → β} {g : β → γ} {x : Filter α} {y : Filter β} {z : Filter γ},   Filter.Tends
to g y z …

--- 原说明 ---
**Dominated convergence theorem** for filters with a countable basis and
AEMeasurable functions.
-/
theorem tendsto_lintegral_filter_of_dominated_convergence' {ι} {l : Filter ι}
    [l.IsCountablyGenerated] {F : ι → α → ℝ≥0∞} {f : α → ℝ≥0∞} (bound : α → ℝ≥0∞)
    (hF_meas : ∀ᶠ n in l, AEMeasurable (F n) μ) (h_bound : ∀ᶠ n in l, ∀ᵐ a ∂μ, F n a ≤ bound a)
    (h_fin : ∫⁻ a, bound a ∂μ ≠ ∞) (h_lim : ∀ᵐ a ∂μ, Tendsto (fun n => F n a) l (𝓝 (f a))) :
    Tendsto (fun n => ∫⁻ a, F n a ∂μ) l (𝓝 <| ∫⁻ a, f a ∂μ) := by
  rw [tendsto_iff_seq_tendsto]
  intro x xl
  have hxl := by
    rw [tendsto_atTop'] at xl
    exact xl
  have h := inter_mem hF_meas h_bound
  replace h := hxl _ h
  rcases h with ⟨k, h⟩
  rw [← tendsto_add_atTop_iff_nat k]
  refine tendsto_lintegral_of_dominated_convergence' ?_ ?_ ?_ ?_ ?_
  · exact bound
  · intro
    refine (h _ ?_).1
    exact Nat.le_add_left _ _
  · intro
    refine (h _ ?_).2
    exact Nat.le_add_left _ _
  · assumption
  · refine h_lim.mono fun a h_lim => ?_
    apply @Tendsto.comp _ _ _ (fun n => x (n + k)) fun n => F n a
    · assumption
    rw [tendsto_add_atTop_iff_nat]
    assumption

/-- **Dominated convergence theorem** for filters with a countable basis. -/
/-
**MeasureTheory.tendsto_lintegral_filter_of_dominated_convergence** 是 Mathlib 中的
一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：tendsto_lintegral_filter_of_dominated_convergence {ι} {l : Filter ι} [l.Is
CountablyGenerated] {F : ι -> α -> Real>=0∞} {f : α -> Real>=0∞} (bound : α -> R
eal>=0∞) (hF_meas : forallᶠ n in l, Measurable (F n)) (h_bound : forallᶠ n in l,
 forallᵐ a ∂μ, F n a <= bound a) (h_fin : ∫⁻ a, bound a ∂μ != ∞) (h_lim : forall
ᵐ a ∂μ, Tendsto (fun n => F n a) l (𝓝 (f a))) : Tendsto (fun n => ∫⁻ a, F n a ∂μ
) l (𝓝 <| ∫⁻ a, f a ∂μ)
参数：bound : α -> Real>=0∞；hF_meas : forallᶠ n in l, Measurable (F n)；h_bound : fo
rallᶠ n in l, forallᵐ a ∂μ, F n a <= bound a；h_fin : ∫⁻ a, bound a ∂μ != ∞；h_lim
 : forallᵐ a ∂μ, Tendsto (fun n => F n a) l (𝓝 (f a))。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `MeasureTheory.tendsto_lintegral_filter_of_dominated_convergence'`：tendst
o_lintegral_filter_of_dominated_convergence' {ι} {l : Filter ι} [l.IsCountablyGe
nerated] {F : ι -> α -> Real>=0∞} {f : α -> Real>=0∞} …
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `Measurable.aemeasurable`：Measurable.aemeasurable (h : Measurable f) : AE
Measurable f μ

--- 原说明 ---
**Dominated convergence theorem** for filters with a countable basis.
-/
theorem tendsto_lintegral_filter_of_dominated_convergence {ι} {l : Filter ι}
    [l.IsCountablyGenerated] {F : ι → α → ℝ≥0∞} {f : α → ℝ≥0∞} (bound : α → ℝ≥0∞)
    (hF_meas : ∀ᶠ n in l, Measurable (F n)) (h_bound : ∀ᶠ n in l, ∀ᵐ a ∂μ, F n a ≤ bound a)
    (h_fin : ∫⁻ a, bound a ∂μ ≠ ∞) (h_lim : ∀ᵐ a ∂μ, Tendsto (fun n => F n a) l (𝓝 (f a))) :
    Tendsto (fun n => ∫⁻ a, F n a ∂μ) l (𝓝 <| ∫⁻ a, f a ∂μ) := by
  refine tendsto_lintegral_filter_of_dominated_convergence' bound ?_ h_bound h_fin h_lim
  filter_upwards [hF_meas] using by fun_prop

/-- If a monotone sequence of functions has an upper bound and the sequence of integrals of these
functions tends to the integral of the upper bound, then the sequence of functions converges
almost everywhere to the upper bound. Auxiliary version assuming moreover that the
functions in the sequence are ae measurable. -/
/-
**MeasureTheory.tendsto_of_lintegral_tendsto_of_monotone_aux** 是 Mathlib 中的一个引理，
位于命名空间 `MeasureTheory`。
形式化陈述：tendsto_of_lintegral_tendsto_of_monotone_aux {α : Type*} {mα : MeasurableS
pace α} {f : Nat -> α -> Real>=0∞} {F : α -> Real>=0∞} {μ : Measure α} (hf_meas 
: forall n, AEMeasurable (f n) μ) (hF_meas : AEMeasurable F μ) (hf_tendsto : Ten
dsto (fun i => ∫⁻ a, f i a ∂μ) atTop (𝓝 (∫⁻ a, F a ∂μ))) (hf_mono : forallᵐ a ∂μ
, Monotone (fun i => f i a)) (h_bound : forallᵐ a ∂μ, forall i, f i a <= F a) (h
_int_finite : ∫⁻ a, F a ∂μ != ∞) : forallᵐ a ∂μ, Tendsto (fun i => f i a) atTop 
(𝓝 (F a))
参数：hf_meas : forall n, AEMeasurable (f n) μ；hF_meas : AEMeasurable F μ；hf_tendst
o : Tendsto (fun i => ∫⁻ a, f i a ∂μ) atTop (𝓝 (∫⁻ a, F a ∂μ))；hf_mono : forallᵐ
 a ∂μ, Monotone (fun i => f i a)；h_bound : forallᵐ a ∂μ, forall i, f i a <= F a；
h_int_finite : ∫⁻ a, F a ∂μ != ∞。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `MeasureTheory.ae_lt_top'`：ae_lt_top' {f : α -> Real>=0∞} (hf : AEMeasura
ble f μ) (h2f : ∫⁻ x, f x ∂μ != ∞) : forallᵐ x ∂μ, f x < ∞
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `LT.lt.ne`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≠ b
· 使用定理 `tendsto_atTop_of_monotone`：tendsto_atTop_of_monotone {ι α : Type*} [Preo
rder ι] [TopologicalSpace α] [ConditionallyCompleteLinearOrder α] [OrderTopology
 α] {f : ι -> α…
· 使用定理 `ENNReal.instOrderTopology`：OrderTopology ENNReal
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Filter.tendsto_atTop_atTop_iff_of_monotone`：tendsto_atTop_atTop_iff_of_m
onotone (hf : Monotone f) : Tendsto f atTop atTop ↔ forall b : β, exists a, b <=
 f a
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `instIsDirectedOrder`：∀ {R : Type u_3} [inst : Semiring R] [inst_1 : Part
ialOrder R] [IsOrderedRing R] [Archimedean R], IsDirectedOrder R
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `instArchimedeanNat`：Archimedean ℕ
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `not_le`：∀ {α : Type u_1} [inst : LinearOrder α] {a b : α}, ¬a ≤ b ↔ b < 
a
· 使用定理 `ENNReal.lt_add_right`：lt_add_right (ha : a != ∞) (hb : b != 0) : a < a +
 b
· 使用定理 `one_ne_zero`：∀ {α : Type u_2} [inst : Zero α] [inst_1 : One α] [NeZero 1
], 1 ≠ 0
· 使用定理 `ENNReal.instCharZero`：CharZero ENNReal
· 使用定理 `dif_pos`：∀ {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t : c → α
} {e : ¬c → α}, dite c t e = t hc
· 使用定理 `Exists.choose_spec`：∀ {α : Sort u_1} {p : α → Prop} (P : ∃ a, p a), p P.
choose
· 使用定理 `le_of_tendsto'`：le_of_tendsto' {x : Filter β} [hx : NeBot x] (lim : Tend
sto f x (𝓝 a)) (h : forall c, f c <= b) : a <= b
· 使用定理 `instClosedIicTopology`：∀ {α : Type u} [inst : TopologicalSpace α] [inst_
1 : Preorder α] [t : OrderClosedTopology α], ClosedIicTopology α
· 使用定理 `OrderTopology.to_orderClosedTopology`：∀ {α : Type u} [inst : Topological
Space α] [inst_1 : LinearOrder α] [OrderTopology α], OrderClosedTopology α
· 使用定理 `tendsto_nhds_unique`：tendsto_nhds_unique [T2Space X] {f : Y -> X} {l : F
ilter Y} {a b : X} [NeBot l] (ha : Tendsto f l (𝓝 a)) (hb : Tendsto f l (𝓝 b)) :
 a = b
· 使用定理 `ENNReal.instT2Space`：T2Space ENNReal
· 使用定理 `MeasureTheory.lintegral_tendsto_of_tendsto_of_monotone`：lintegral_tendst
o_of_tendsto_of_monotone {f : Nat -> α -> Real>=0∞} {F : α -> Real>=0∞} (hf : fo
rall n, AEMeasurable (f n) μ) (h_mono : fora…
· 使用定理 `MeasureTheory.ae_eq_of_ae_le_of_lintegral_le`：ae_eq_of_ae_le_of_lintegra
l_le {f g : α -> Real>=0∞} (hfg : f <=ᵐ[μ] g) (hf : ∫⁻ x, f x ∂μ != ∞) (hg : AEM
easurable g μ) (hgf : ∫⁻ x, g x ∂μ…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Eq.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → a ≤ b

--- 原说明 ---
If a monotone sequence of functions has an upper bound and the sequence of integ
rals of these
functions tends to the integral of the upper bound, then the sequence of functio
ns converges
almost everywhere to the upper bound. Auxiliary version assuming moreover that t
he
functions in the sequence are ae measurable.
-/
lemma tendsto_of_lintegral_tendsto_of_monotone_aux {α : Type*} {mα : MeasurableSpace α}
    {f : ℕ → α → ℝ≥0∞} {F : α → ℝ≥0∞} {μ : Measure α}
    (hf_meas : ∀ n, AEMeasurable (f n) μ) (hF_meas : AEMeasurable F μ)
    (hf_tendsto : Tendsto (fun i ↦ ∫⁻ a, f i a ∂μ) atTop (𝓝 (∫⁻ a, F a ∂μ)))
    (hf_mono : ∀ᵐ a ∂μ, Monotone (fun i ↦ f i a))
    (h_bound : ∀ᵐ a ∂μ, ∀ i, f i a ≤ F a) (h_int_finite : ∫⁻ a, F a ∂μ ≠ ∞) :
    ∀ᵐ a ∂μ, Tendsto (fun i ↦ f i a) atTop (𝓝 (F a)) := by
  have h_bound_finite : ∀ᵐ a ∂μ, F a ≠ ∞ := by
    filter_upwards [ae_lt_top' hF_meas h_int_finite] with a ha using ha.ne
  have h_exists : ∀ᵐ a ∂μ, ∃ l, Tendsto (fun i ↦ f i a) atTop (𝓝 l) := by
    filter_upwards [h_bound, h_bound_finite, hf_mono] with a h_le h_fin h_mono
    have h_tendsto : Tendsto (fun i ↦ f i a) atTop atTop ∨
        ∃ l, Tendsto (fun i ↦ f i a) atTop (𝓝 l) := tendsto_atTop_of_monotone h_mono
    rcases h_tendsto with h_absurd | h_tendsto
    · rw [tendsto_atTop_atTop_iff_of_monotone h_mono] at h_absurd
      obtain ⟨i, hi⟩ := h_absurd (F a + 1)
      refine absurd (hi.trans (h_le _)) (not_le.mpr ?_)
      exact ENNReal.lt_add_right h_fin one_ne_zero
    · exact h_tendsto
  classical
  let F' : α → ℝ≥0∞ := fun a ↦ if h : ∃ l, Tendsto (fun i ↦ f i a) atTop (𝓝 l)
    then h.choose else ∞
  have hF'_tendsto : ∀ᵐ a ∂μ, Tendsto (fun i ↦ f i a) atTop (𝓝 (F' a)) := by
    filter_upwards [h_exists] with a ha
    simp_rw [F', dif_pos ha]
    exact ha.choose_spec
  suffices F' =ᵐ[μ] F by
    filter_upwards [this, hF'_tendsto] with a h_eq h_tendsto using h_eq ▸ h_tendsto
  have hF'_le : F' ≤ᵐ[μ] F := by
    filter_upwards [h_bound, hF'_tendsto] with a h_le h_tendsto
    exact le_of_tendsto' h_tendsto (fun m ↦ h_le _)
  suffices ∫⁻ a, F' a ∂μ = ∫⁻ a, F a ∂μ from
    ae_eq_of_ae_le_of_lintegral_le hF'_le (this ▸ h_int_finite) hF_meas this.symm.le
  refine tendsto_nhds_unique ?_ hf_tendsto
  exact lintegral_tendsto_of_tendsto_of_monotone hf_meas hf_mono hF'_tendsto

/-- If a monotone sequence of functions has an upper bound and the sequence of integrals of these
functions tends to the integral of the upper bound, then the sequence of functions converges
almost everywhere to the upper bound. -/
/-
**MeasureTheory.tendsto_of_lintegral_tendsto_of_monotone** 是 Mathlib 中的一个引理，位于命名
空间 `MeasureTheory`。
形式化陈述：tendsto_of_lintegral_tendsto_of_monotone {α : Type*} {mα : MeasurableSpace
 α} {f : Nat -> α -> Real>=0∞} {F : α -> Real>=0∞} {μ : Measure α} (hF_meas : AE
Measurable F μ) (hf_tendsto : Tendsto (fun i => ∫⁻ a, f i a ∂μ) atTop (𝓝 (∫⁻ a, 
F a ∂μ))) (hf_mono : forallᵐ a ∂μ, Monotone (fun i => f i a)) (h_bound : forallᵐ
 a ∂μ, forall i, f i a <= F a) (h_int_finite : ∫⁻ a, F a ∂μ != ∞) : forallᵐ a ∂μ
, Tendsto (fun i => f i a) atTop (𝓝 (F a))
参数：hF_meas : AEMeasurable F μ；hf_tendsto : Tendsto (fun i => ∫⁻ a, f i a ∂μ) atT
op (𝓝 (∫⁻ a, F a ∂μ))；hf_mono : forallᵐ a ∂μ, Monotone (fun i => f i a)；h_bound 
: forallᵐ a ∂μ, forall i, f i a <= F a；h_int_finite : ∫⁻ a, F a ∂μ != ∞。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `MeasureTheory.exists_measurable_le_lintegral_eq`：exists_measurable_le_li
ntegral_eq (f : α -> Real>=0∞) : exists g : α -> Real>=0∞, Measurable g ∧ g <= f
 ∧ ∫⁻ a, f a ∂μ = ∫⁻ a, g a ∂μ
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Measurable.max`：Measurable.max {f g : δ -> α} (hf : Measurable f) (hg : 
Measurable g) : Measurable fun a => max (f a) (g a)
· 使用定理 `BorelSpace.opensMeasurable`：∀ {α : Type u_6} [inst : TopologicalSpace α]
 [inst_1 : MeasurableSpace α] [BorelSpace α], OpensMeasurableSpace α
· 使用定理 `ENNReal.instSecondCountableTopology`：SecondCountableTopology ENNReal
· 使用定理 `OrderTopology.to_orderClosedTopology`：∀ {α : Type u} [inst : Topological
Space α] [inst_1 : LinearOrder α] [OrderTopology α], OrderClosedTopology α
· 使用定理 `ENNReal.instOrderTopology`：OrderTopology ENNReal
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `max_le`：∀ {α : Type u_1} [inst : LinearOrder α] {a b c : α}, a ≤ c → b ≤
 c → max a b ≤ c
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `Nat.le_succ`：∀ (n : ℕ), n ≤ n.succ
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `MeasureTheory.lintegral_mono_ae`：lintegral_mono_ae {f g : α -> Real>=0∞}
 (h : forallᵐ a ∂μ, f a <= g a) : ∫⁻ a, f a ∂μ <= ∫⁻ a, g a ∂μ
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.lintegral_mono`：lintegral_mono ⦃f g : α -> Real>=0∞⦄ (hfg 
: f <= g) : ∫⁻ a, f a ∂μ <= ∫⁻ a, g a ∂μ
· 使用引理 `MeasureTheory.tendsto_of_lintegral_tendsto_of_monotone_aux`：tendsto_of_l
integral_tendsto_of_monotone_aux {α : Type*} {mα : MeasurableSpace α} {f : Nat -
> α -> Real>=0∞} {F : α -> Real>=0∞} {μ : Measur…
· 使用定理 `Measurable.aemeasurable`：Measurable.aemeasurable (h : Measurable f) : AE
Measurable f μ
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Filter.Eventually.of_forall`：∀ {α : Type u} {p : α → Prop} {f : Filter α
}, (∀ (x : α), p x) → ∀ᶠ (x : α) in f, p x
· 使用定理 `monotone_nat_of_le_succ`：monotone_nat_of_le_succ {f : Nat -> α} (hf : fo
rall n, f n <= f (n + 1)) : Monotone f
· 使用定理 `le_max_right`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), b ≤ max
 a b
· 使用定理 `tendsto_of_tendsto_of_tendsto_of_le_of_le`：tendsto_of_tendsto_of_tendsto
_of_le_of_le [OrderTopology α] {f g h : β -> α} {b : Filter β} {a : α} (hg : Ten
dsto g b (𝓝 a)) (hh : Tendsto h…
· 使用定理 `tendsto_const_nhds`：tendsto_const_nhds {f : Filter α} : Tendsto (fun _ :
 α => x) f (𝓝 x)
· 使用定理 `Classical.choose_spec`：∀ {α : Sort u} {p : α → Prop} (h : ∃ x, p x), p (
Classical.choose h)

--- 原说明 ---
If a monotone sequence of functions has an upper bound and the sequence of integ
rals of these
functions tends to the integral of the upper bound, then the sequence of functio
ns converges
almost everywhere to the upper bound.
-/
lemma tendsto_of_lintegral_tendsto_of_monotone {α : Type*} {mα : MeasurableSpace α}
    {f : ℕ → α → ℝ≥0∞} {F : α → ℝ≥0∞} {μ : Measure α}
    (hF_meas : AEMeasurable F μ)
    (hf_tendsto : Tendsto (fun i ↦ ∫⁻ a, f i a ∂μ) atTop (𝓝 (∫⁻ a, F a ∂μ)))
    (hf_mono : ∀ᵐ a ∂μ, Monotone (fun i ↦ f i a))
    (h_bound : ∀ᵐ a ∂μ, ∀ i, f i a ≤ F a) (h_int_finite : ∫⁻ a, F a ∂μ ≠ ∞) :
    ∀ᵐ a ∂μ, Tendsto (fun i ↦ f i a) atTop (𝓝 (F a)) := by
  have : ∀ n, ∃ g : α → ℝ≥0∞, Measurable g ∧ g ≤ f n ∧ ∫⁻ a, f n a ∂μ = ∫⁻ a, g a ∂μ :=
    fun n ↦ exists_measurable_le_lintegral_eq _ _
  choose g gmeas gf hg using this
  let g' : ℕ → α → ℝ≥0∞ := Nat.rec (g 0) (fun n I x ↦ max (g (n + 1) x) (I x))
  have M n : Measurable (g' n) := by
    induction n with
    | zero => simp [g', gmeas 0]
    | succ n ih => exact Measurable.max (gmeas (n + 1)) ih
  have I : ∀ n x, g n x ≤ g' n x := by
    intro n x
    cases n with | zero | succ => simp [g']
  have I' : ∀ᵐ x ∂μ, ∀ n, g' n x ≤ f n x := by
    filter_upwards [hf_mono] with x hx n
    induction n with
    | zero => simpa [g'] using gf 0 x
    | succ n ih => exact max_le (gf (n + 1) x) (ih.trans (hx (Nat.le_succ n)))
  have Int_eq n : ∫⁻ x, g' n x ∂μ = ∫⁻ x, f n x ∂μ := by
    apply le_antisymm
    · apply lintegral_mono_ae
      filter_upwards [I'] with x hx using hx n
    · rw [hg n]
      exact lintegral_mono (I n)
  have : ∀ᵐ a ∂μ, Tendsto (fun i ↦ g' i a) atTop (𝓝 (F a)) := by
    apply tendsto_of_lintegral_tendsto_of_monotone_aux _ hF_meas _ _ _ h_int_finite
    · exact fun n ↦ (M n).aemeasurable
    · simp_rw [Int_eq]
      exact hf_tendsto
    · exact Eventually.of_forall (fun x ↦ monotone_nat_of_le_succ (fun n ↦ le_max_right _ _))
    · filter_upwards [h_bound, I'] with x h'x hx n using (hx n).trans (h'x n)
  filter_upwards [this, I', h_bound] with x hx h'x h''x
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le hx tendsto_const_nhds h'x h''x

/-- If an antitone sequence of functions has a lower bound and the sequence of integrals of these
functions tends to the integral of the lower bound, then the sequence of functions converges
almost everywhere to the lower bound. -/
/-
**MeasureTheory.tendsto_of_lintegral_tendsto_of_antitone** 是 Mathlib 中的一个引理，位于命名
空间 `MeasureTheory`。
形式化陈述：tendsto_of_lintegral_tendsto_of_antitone {α : Type*} {mα : MeasurableSpace
 α} {f : Nat -> α -> Real>=0∞} {F : α -> Real>=0∞} {μ : Measure α} (hf_meas : fo
rall n, AEMeasurable (f n) μ) (hf_tendsto : Tendsto (fun i => ∫⁻ a, f i a ∂μ) at
Top (𝓝 (∫⁻ a, F a ∂μ))) (hf_mono : forallᵐ a ∂μ, Antitone (fun i => f i a)) (h_b
ound : forallᵐ a ∂μ, forall i, F a <= f i a) (h0 : ∫⁻ a, f 0 a ∂μ != ∞) : forall
ᵐ a ∂μ, Tendsto (fun i => f i a) atTop (𝓝 (F a))
参数：hf_meas : forall n, AEMeasurable (f n) μ；hf_tendsto : Tendsto (fun i => ∫⁻ a,
 f i a ∂μ) atTop (𝓝 (∫⁻ a, F a ∂μ))；hf_mono : forallᵐ a ∂μ, Antitone (fun i => f
 i a)；h_bound : forallᵐ a ∂μ, forall i, F a <= f i a；h0 : ∫⁻ a, f 0 a ∂μ != ∞。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `LT.lt.ne`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≠ b
· 使用定理 `LE.le.trans_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b 
→ b < c → a < c
· 使用定理 `MeasureTheory.lintegral_mono_ae`：lintegral_mono_ae {f g : α -> Real>=0∞}
 (h : forallᵐ a ∂μ, f a <= g a) : ∫⁻ a, f a ∂μ <= ∫⁻ a, g a ∂μ
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `Ne.lt_top`：Ne.lt_top (h : a != ⊤) : a < ⊤
· 使用定理 `tendsto_atTop_of_antitone`：tendsto_atTop_of_antitone {ι α : Type*} [Preo
rder ι] [TopologicalSpace α] [ConditionallyCompleteLinearOrder α] [OrderTopology
 α] {f : ι -> α…
· 使用定理 `ENNReal.instOrderTopology`：OrderTopology ENNReal
· 使用定理 `Filter.Tendsto.mono_right`：∀ {α : Type u_1} {β : Type u_2} {f : α → β} {
x : Filter α} {y z : Filter β},   Filter.Tendsto f x y → y ≤ z → Filter.Tendsto 
f x z
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Filter.OrderBot.atBot_eq`：∀ (α : Type u_6) [inst : PartialOrder α] [inst
_1 : OrderBot α], Filter.atBot = pure ⊥
· 使用定理 `pure_le_nhds`：pure_le_nhds : pure <= (𝓝 : X -> Filter X)
· 使用定理 `dif_pos`：∀ {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t : c → α
} {e : ¬c → α}, dite c t e = t hc
· 使用定理 `Exists.choose_spec`：∀ {α : Sort u_1} {p : α → Prop} (P : ∃ a, p a), p P.
choose
· 使用定理 `ge_of_tendsto'`：∀ {α : Type u} {β : Type v} [inst : TopologicalSpace α] 
[inst_1 : Preorder α] [ClosedIciTopology α] {f : β → α}   {a b : α} {x : Filter 
β} […
· 使用定理 `instClosedIciTopology`：∀ {α : Type u} [inst : TopologicalSpace α] [inst_
1 : Preorder α] [t : OrderClosedTopology α], ClosedIciTopology α
· 使用定理 `OrderTopology.to_orderClosedTopology`：∀ {α : Type u} [inst : Topological
Space α] [inst_1 : LinearOrder α] [OrderTopology α], OrderClosedTopology α
· 使用定理 `instIsDirectedOrder`：∀ {R : Type u_3} [inst : Semiring R] [inst_1 : Part
ialOrder R] [IsOrderedRing R] [Archimedean R], IsDirectedOrder R
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `instArchimedeanNat`：Archimedean ℕ
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `tendsto_nhds_unique`：tendsto_nhds_unique [T2Space X] {f : Y -> X} {l : F
ilter Y} {a b : X} [NeBot l] (ha : Tendsto f l (𝓝 a)) (hb : Tendsto f l (𝓝 b)) :
 a = b
· 使用定理 `ENNReal.instT2Space`：T2Space ENNReal
· 使用定理 `MeasureTheory.lintegral_tendsto_of_tendsto_of_antitone`：lintegral_tendst
o_of_tendsto_of_antitone {f : Nat -> α -> Real>=0∞} {F : α -> Real>=0∞} (hf : fo
rall n, AEMeasurable (f n) μ) (h_anti : fora…
· 使用定理 `Filter.EventuallyEq.symm`：∀ {α : Type u} {β : Type v} {f g : α → β} {l :
 Filter α}, f =ᶠ[l] g → g =ᶠ[l] f
· 使用定理 `MeasureTheory.ae_eq_of_ae_le_of_lintegral_le`：ae_eq_of_ae_le_of_lintegra
l_le {f g : α -> Real>=0∞} (hfg : f <=ᵐ[μ] g) (hf : ∫⁻ x, f x ∂μ != ∞) (hg : AEM
easurable g μ) (hgf : ∫⁻ x, g x ∂μ…
· 使用引理 `ENNReal.aemeasurable_of_tendsto`：aemeasurable_of_tendsto {f : Nat -> α -
> Real>=0∞} {g : α -> Real>=0∞} {μ : Measure α} (hf : forall i, AEMeasurable (f 
i) μ) (hlim : forallᵐ…
· 使用定理 `Eq.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → a ≤ b

--- 原说明 ---
If an antitone sequence of functions has a lower bound and the sequence of integ
rals of these
functions tends to the integral of the lower bound, then the sequence of functio
ns converges
almost everywhere to the lower bound.
-/
lemma tendsto_of_lintegral_tendsto_of_antitone {α : Type*} {mα : MeasurableSpace α}
    {f : ℕ → α → ℝ≥0∞} {F : α → ℝ≥0∞} {μ : Measure α}
    (hf_meas : ∀ n, AEMeasurable (f n) μ)
    (hf_tendsto : Tendsto (fun i ↦ ∫⁻ a, f i a ∂μ) atTop (𝓝 (∫⁻ a, F a ∂μ)))
    (hf_mono : ∀ᵐ a ∂μ, Antitone (fun i ↦ f i a))
    (h_bound : ∀ᵐ a ∂μ, ∀ i, F a ≤ f i a) (h0 : ∫⁻ a, f 0 a ∂μ ≠ ∞) :
    ∀ᵐ a ∂μ, Tendsto (fun i ↦ f i a) atTop (𝓝 (F a)) := by
  have h_int_finite : ∫⁻ a, F a ∂μ ≠ ∞ := by
    refine ((lintegral_mono_ae ?_).trans_lt h0.lt_top).ne
    filter_upwards [h_bound] with a ha using ha 0
  have h_exists : ∀ᵐ a ∂μ, ∃ l, Tendsto (fun i ↦ f i a) atTop (𝓝 l) := by
    filter_upwards [hf_mono] with a h_mono
    rcases _root_.tendsto_atTop_of_antitone h_mono with h | h
    · refine ⟨0, h.mono_right ?_⟩
      rw [OrderBot.atBot_eq]
      exact pure_le_nhds _
    · exact h
  classical
  let F' : α → ℝ≥0∞ := fun a ↦ if h : ∃ l, Tendsto (fun i ↦ f i a) atTop (𝓝 l)
    then h.choose else ∞
  have hF'_tendsto : ∀ᵐ a ∂μ, Tendsto (fun i ↦ f i a) atTop (𝓝 (F' a)) := by
    filter_upwards [h_exists] with a ha
    simp_rw [F', dif_pos ha]
    exact ha.choose_spec
  suffices F' =ᵐ[μ] F by
    filter_upwards [this, hF'_tendsto] with a h_eq h_tendsto using h_eq ▸ h_tendsto
  have hF'_le : F ≤ᵐ[μ] F' := by
    filter_upwards [h_bound, hF'_tendsto] with a h_le h_tendsto
    exact ge_of_tendsto' h_tendsto (fun m ↦ h_le _)
  suffices ∫⁻ a, F' a ∂μ = ∫⁻ a, F a ∂μ by
    refine (ae_eq_of_ae_le_of_lintegral_le hF'_le h_int_finite ?_ this.le).symm
    exact ENNReal.aemeasurable_of_tendsto hf_meas hF'_tendsto
  refine tendsto_nhds_unique ?_ hf_tendsto
  exact lintegral_tendsto_of_tendsto_of_antitone hf_meas hf_mono h0 hF'_tendsto

end MeasureTheory

