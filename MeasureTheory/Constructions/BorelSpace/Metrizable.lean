/-
Copyright (c) 2020 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn
-/
module

public import Mathlib.MeasureTheory.Constructions.BorelSpace.Metric
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Real
public import Mathlib.Topology.Metrizable.Real
public import Mathlib.Topology.IndicatorConstPointwise

/-!
# Measurable functions in (pseudo-)metrizable Borel spaces
-/

public section

open Filter MeasureTheory TopologicalSpace Topology NNReal ENNReal MeasureTheory

variable {α β : Type*} [MeasurableSpace α]

section Limits

variable [TopologicalSpace β] [PseudoMetrizableSpace β] [MeasurableSpace β] [BorelSpace β]

open Metric

/-- A limit (over a general filter) of measurable functions valued in a (pseudo) metrizable space is
measurable. -/
/-
**measurable_of_tendsto_metrizable'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：measurable_of_tendsto_metrizable' {ι} {f : ι -> α -> β} {g : α -> β} (u : 
Filter ι) [NeBot u] [IsCountablyGenerated u] (hf : forall i, Measurable (f i)) (
lim : Tendsto f u (𝓝 g)) : Measurable g
参数：u : Filter ι；hf : forall i, Measurable (f i)；lim : Tendsto f u (𝓝 g)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `measurable_of_isClosed'`：measurable_of_isClosed' {f : δ -> γ} (hf : fora
ll s, IsClosed s -> s.Nonempty -> s != univ -> MeasurableSet (f ⁻¹' s)) : Measur
able f
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `tendsto_pi_nhds`：tendsto_pi_nhds {f : Y -> forall i, A i} {g : forall i,
 A i} {u : Filter Y} : Tendsto f u (𝓝 g) ↔ forall x, Tendsto (fun i => f i x) u 
(𝓝 (g…
· 使用定理 `Filter.Tendsto.comp`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {f :
 α → β} {g : β → γ} {x : Filter α} {y : Filter β} {z : Filter γ},   Filter.Tends
to g y z …
· 使用定理 `Continuous.tendsto`：Continuous.tendsto (hf : Continuous f) (x) : Tendsto
 f (𝓝 x) (𝓝 (f x))
· 使用定理 `Metric.continuous_infNndist_pt`：continuous_infNndist_pt (s : Set α) : Co
ntinuous fun x => infNndist x s
· 使用定理 `NNReal.measurable_of_tendsto'`：measurable_of_tendsto' {ι} {f : ι -> α ->
 Real>=0} {g : α -> Real>=0} (u : Filter ι) [NeBot u] [IsCountablyGenerated u] (
hf : forall i, Meas…
· 使用定理 `Measurable.infNndist`：Measurable.infNndist {f : β -> α} (hf : Measurable
 f) {s : Set α} : Measurable fun x => infNndist (f x) s
· 使用定理 `BorelSpace.opensMeasurable`：∀ {α : Type u_6} [inst : TopologicalSpace α]
 [inst_1 : MeasurableSpace α] [BorelSpace α], OpensMeasurableSpace α
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `IsClosed.mem_iff_infDist_zero`：∀ {α : Type u} [inst : PseudoMetricSpace 
α] {s : Set α} {x : α},   IsClosed s → s.Nonempty → (x ∈ s ↔ Metric.infDist x s 
= 0)
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `MeasurableSingletonClass.measurableSet_singleton`：∀ {α : Type u_7} {inst
 : MeasurableSpace α} [self : MeasurableSingletonClass α] (x : α), MeasurableSet
 {x}
· 使用定理 `instMeasurableSingletonClassOfMeasurableEq`：∀ {α : Type u_1} [inst : Mea
surableSpace α] [MeasurableEq α], MeasurableSingletonClass α
· 使用定理 `instMeasurableEqOfSecondCountableTopologyOfT2Space`：∀ {α : Type u_1} [in
st : TopologicalSpace α] [inst_1 : MeasurableSpace α] [OpensMeasurableSpace α]  
 [SecondCountableTopology α] [T2Space α]…
· 使用定理 `NNReal.instSecondCountableTopology`：SecondCountableTopology NNReal
· 使用定理 `TopologicalSpace.t2Space_of_metrizableSpace`：∀ {X : Type u_2} [inst : To
pologicalSpace X] [TopologicalSpace.MetrizableSpace X], T2Space X
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α

--- 原说明 ---
A limit (over a general filter) of measurable functions valued in a (pseudo) met
rizable space is
measurable.
-/
theorem measurable_of_tendsto_metrizable' {ι} {f : ι → α → β} {g : α → β} (u : Filter ι) [NeBot u]
    [IsCountablyGenerated u] (hf : ∀ i, Measurable (f i)) (lim : Tendsto f u (𝓝 g)) :
    Measurable g := by
  let : PseudoMetricSpace β := pseudoMetrizableSpacePseudoMetric β
  apply measurable_of_isClosed'
  intro s h1s h2s h3s
  have : Measurable fun x => infNndist (g x) s := by
    suffices Tendsto (fun i x => infNndist (f i x) s) u (𝓝 fun x => infNndist (g x) s) from
      NNReal.measurable_of_tendsto' u (fun i => (hf i).infNndist) this
    rw [tendsto_pi_nhds] at lim ⊢
    intro x
    exact ((continuous_infNndist_pt s).tendsto (g x)).comp (lim x)
  have h4s : g ⁻¹' s = (fun x => infNndist (g x) s) ⁻¹' {0} := by
    ext x
    simp [← h1s.mem_iff_infDist_zero h2s, ← NNReal.coe_eq_zero]
  rw [h4s]
  exact this (measurableSet_singleton 0)

/-- A sequential limit of measurable functions valued in a (pseudo) metrizable space is
measurable. -/
/-
**measurable_of_tendsto_metrizable** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：measurable_of_tendsto_metrizable {f : Nat -> α -> β} {g : α -> β} (hf : fo
rall i, Measurable (f i)) (lim : Tendsto f atTop (𝓝 g)) : Measurable g
参数：hf : forall i, Measurable (f i)；lim : Tendsto f atTop (𝓝 g)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `measurable_of_tendsto_metrizable'`：measurable_of_tendsto_metrizable' {ι}
 {f : ι -> α -> β} {g : α -> β} (u : Filter ι) [NeBot u] [IsCountablyGenerated u
] (hf : forall i, Measu…
· 使用定理 `instIsDirectedOrder`：∀ {R : Type u_3} [inst : Semiring R] [inst_1 : Part
ialOrder R] [IsOrderedRing R] [Archimedean R], IsDirectedOrder R
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `instArchimedeanNat`：Archimedean ℕ
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
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

--- 原说明 ---
A sequential limit of measurable functions valued in a (pseudo) metrizable space
 is
measurable.
-/
theorem measurable_of_tendsto_metrizable {f : ℕ → α → β} {g : α → β} (hf : ∀ i, Measurable (f i))
    (lim : Tendsto f atTop (𝓝 g)) : Measurable g :=
  measurable_of_tendsto_metrizable' atTop hf lim
/-
**aemeasurable_of_tendsto_metrizable_ae** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：aemeasurable_of_tendsto_metrizable_ae {ι} {μ : Measure α} {f : ι -> α -> β
} {g : α -> β} (u : Filter ι) [hu : NeBot u] [IsCountablyGenerated u] (hf : fora
ll n, AEMeasurable (f n) μ) (h_tendsto : forallᵐ x ∂μ, Tendsto (fun n => f n x) 
u (𝓝 (g x))) : AEMeasurable g μ
参数：u : Filter ι；hf : forall n, AEMeasurable (f n) μ；h_tendsto : forallᵐ x ∂μ, Te
ndsto (fun n => f n x) u (𝓝 (g x))。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `Filter.exists_seq_tendsto`：exists_seq_tendsto (f : Filter α) [IsCountabl
yGenerated f] [NeBot f] : exists x : Nat -> α, Tendsto x atTop f
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `Filter.Tendsto.comp`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {f :
 α → β} {g : β → γ} {x : Filter α} {y : Filter β} {z : Filter γ},   Filter.Tends
to g y z …
· 使用定理 `measurable_of_tendsto_metrizable'`：measurable_of_tendsto_metrizable' {ι}
 {f : ι -> α -> β} {g : α -> β} (u : Filter ι) [NeBot u] [IsCountablyGenerated u
] (hf : forall i, Measu…
· 使用定理 `instIsDirectedOrder`：∀ {R : Type u_3} [inst : Semiring R] [inst_1 : Part
ialOrder R] [IsOrderedRing R] [Archimedean R], IsDirectedOrder R
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `instArchimedeanNat`：Archimedean ℕ
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
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
· 使用定理 `aeSeq.measurable`：measurable (hf : forall i, AEMeasurable (f i) μ) (p : 
α -> (ι -> β) -> Prop) (i : ι) : Measurable (aeSeq hf p i)
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `tendsto_pi_nhds`：tendsto_pi_nhds {f : Y -> forall i, A i} {g : forall i,
 A i} {u : Filter Y} : Tendsto f u (𝓝 g) ↔ forall x, Tendsto (fun i => f i x) u 
(𝓝 (g…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用定理 `aeSeq.mk_eq_fun_of_mem_aeSeqSet`：mk_eq_fun_of_mem_aeSeqSet (hf : forall 
i, AEMeasurable (f i) μ) {x : α} (hx : x in aeSeqSet hf p) (i : ι) : (hf i).mk (
f i) x = f i x
· 使用定理 `aeSeq.fun_prop_of_mem_aeSeqSet`：fun_prop_of_mem_aeSeqSet (hf : forall i,
 AEMeasurable (f i) μ) {x : α} (hx : x in aeSeqSet hf p) : p x fun n => f n x
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
· 使用定理 `tendsto_const_nhds`：tendsto_const_nhds {f : Filter α} : Tendsto (fun _ :
 α => x) f (𝓝 x)
· 使用定理 `Filter.EventuallyEq.symm`：∀ {α : Type u} {β : Type v} {f g : α → β} {l :
 Filter α}, f =ᶠ[l] g → g =ᶠ[l] f
（共 32 条，此处仅展示前 30 条）
-/
theorem aemeasurable_of_tendsto_metrizable_ae {ι} {μ : Measure α} {f : ι → α → β} {g : α → β}
    (u : Filter ι) [hu : NeBot u] [IsCountablyGenerated u] (hf : ∀ n, AEMeasurable (f n) μ)
    (h_tendsto : ∀ᵐ x ∂μ, Tendsto (fun n => f n x) u (𝓝 (g x))) : AEMeasurable g μ := by
  classical
  rcases u.exists_seq_tendsto with ⟨v, hv⟩
  have h'f : ∀ n, AEMeasurable (f (v n)) μ := fun n => hf (v n)
  set p : α → (ℕ → β) → Prop := fun x f' => Tendsto (fun n => f' n) atTop (𝓝 (g x))
  have hp : ∀ᵐ x ∂μ, p x fun n => f (v n) x := by
    filter_upwards [h_tendsto] with x hx using hx.comp hv
  set aeSeqLim := fun x => ite (x ∈ aeSeqSet h'f p) (g x) (⟨f (v 0) x⟩ : Nonempty β).some
  refine
    ⟨aeSeqLim,
      measurable_of_tendsto_metrizable' atTop (aeSeq.measurable h'f p)
        (tendsto_pi_nhds.mpr fun x => ?_),
      ?_⟩
  · simp_rw [aeSeqLim, aeSeq]
    split_ifs with hx
    · simp_rw [aeSeq.mk_eq_fun_of_mem_aeSeqSet h'f hx]
      exact @aeSeq.fun_prop_of_mem_aeSeqSet _ α β _ _ _ _ _ h'f x hx
    · exact tendsto_const_nhds
  · exact
      (ite_ae_eq_of_measure_compl_zero g (fun x => (⟨f (v 0) x⟩ : Nonempty β).some) (aeSeqSet h'f p)
          (aeSeq.measure_compl_aeSeqSet_eq_zero h'f hp)).symm
/-
**aemeasurable_of_tendsto_metrizable_ae'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：aemeasurable_of_tendsto_metrizable_ae' {μ : Measure α} {f : Nat -> α -> β}
 {g : α -> β} (hf : forall n, AEMeasurable (f n) μ) (h_ae_tendsto : forallᵐ x ∂μ
, Tendsto (fun n => f n x) atTop (𝓝 (g x))) : AEMeasurable g μ
参数：hf : forall n, AEMeasurable (f n) μ；h_ae_tendsto : forallᵐ x ∂μ, Tendsto (fun
 n => f n x) atTop (𝓝 (g x))。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `aemeasurable_of_tendsto_metrizable_ae`：aemeasurable_of_tendsto_metrizabl
e_ae {ι} {μ : Measure α} {f : ι -> α -> β} {g : α -> β} (u : Filter ι) [hu : NeB
ot u] [IsCountablyGenerated…
· 使用定理 `instIsDirectedOrder`：∀ {R : Type u_3} [inst : Semiring R] [inst_1 : Part
ialOrder R] [IsOrderedRing R] [Archimedean R], IsDirectedOrder R
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `instArchimedeanNat`：Archimedean ℕ
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
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
-/
theorem aemeasurable_of_tendsto_metrizable_ae' {μ : Measure α} {f : ℕ → α → β} {g : α → β}
    (hf : ∀ n, AEMeasurable (f n) μ)
    (h_ae_tendsto : ∀ᵐ x ∂μ, Tendsto (fun n => f n x) atTop (𝓝 (g x))) : AEMeasurable g μ :=
  aemeasurable_of_tendsto_metrizable_ae atTop hf h_ae_tendsto
/-
**aemeasurable_of_unif_approx** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：aemeasurable_of_unif_approx {β} [MeasurableSpace β] [PseudoMetricSpace β] 
[BorelSpace β] {μ : Measure α} {g : α -> β} (hf : forall ε > (0 : Real), exists 
f : α -> β, AEMeasurable f μ ∧ forallᵐ x ∂μ, dist (f x) (g x) <= ε) : AEMeasurab
le g μ
参数：hf : forall ε > (0 : Real), exists f : α -> β, AEMeasurable f μ ∧ forallᵐ x ∂
μ, dist (f x) (g x) <= ε。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
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
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `MeasureTheory.ae_all_iff`：ae_all_iff {ι : Sort*} [Countable ι] {p : α ->
 ι -> Prop} : (forallᵐ a ∂μ, forall i, p a i) ↔ forall i, forallᵐ a ∂μ, p a i
· 使用定理 `instCountableNat`：Countable ℕ
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `tendsto_iff_dist_tendsto_zero`：tendsto_iff_dist_tendsto_zero {f : β -> α
} {x : Filter β} {a : α} : Tendsto f x (𝓝 a) ↔ Tendsto (fun b => dist (f b) a) x
 (𝓝 0)
· 使用引理 `squeeze_zero`：squeeze_zero {α} {f g : α -> Real} {t₀ : Filter α} (hf : f
orall t, 0 <= f t) (hft : forall t, f t <= g t) (g0 : Tendsto g t₀ (𝓝 0)) : Tend
st…
· 使用定理 `dist_nonneg`：dist_nonneg {x y : α} : 0 <= dist x y
· 使用定理 `aemeasurable_of_tendsto_metrizable_ae'`：aemeasurable_of_tendsto_metrizab
le_ae' {μ : Measure α} {f : Nat -> α -> β} {g : α -> β} (hf : forall n, AEMeasur
able (f n) μ) (h_ae_tendsto …
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Classical.choose_spec`：∀ {α : Sort u} {p : α → Prop} (h : ∃ x, p x), p (
Classical.choose h)
-/
theorem aemeasurable_of_unif_approx {β} [MeasurableSpace β] [PseudoMetricSpace β] [BorelSpace β]
    {μ : Measure α} {g : α → β}
    (hf : ∀ ε > (0 : ℝ), ∃ f : α → β, AEMeasurable f μ ∧ ∀ᵐ x ∂μ, dist (f x) (g x) ≤ ε) :
    AEMeasurable g μ := by
  obtain ⟨u, -, u_pos, u_lim⟩ :
    ∃ u : ℕ → ℝ, StrictAnti u ∧ (∀ n : ℕ, 0 < u n) ∧ Tendsto u atTop (𝓝 0) :=
    exists_seq_strictAnti_tendsto (0 : ℝ)
  choose f Hf using fun n : ℕ => hf (u n) (u_pos n)
  have : ∀ᵐ x ∂μ, Tendsto (fun n => f n x) atTop (𝓝 (g x)) := by
    have : ∀ᵐ x ∂μ, ∀ n, dist (f n x) (g x) ≤ u n := ae_all_iff.2 fun n => (Hf n).2
    filter_upwards [this]
    intro x hx
    rw [tendsto_iff_dist_tendsto_zero]
    exact squeeze_zero (fun n => dist_nonneg) hx u_lim
  exact aemeasurable_of_tendsto_metrizable_ae' (fun n => (Hf n).1) this
/-
**measurable_of_tendsto_metrizable_ae** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：measurable_of_tendsto_metrizable_ae {μ : Measure α} [μ.IsComplete] {f : Na
t -> α -> β} {g : α -> β} (hf : forall n, Measurable (f n)) (h_ae_tendsto : fora
llᵐ x ∂μ, Tendsto (fun n => f n x) atTop (𝓝 (g x))) : Measurable g
参数：hf : forall n, Measurable (f n)；h_ae_tendsto : forallᵐ x ∂μ, Tendsto (fun n =
> f n x) atTop (𝓝 (g x))。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `aemeasurable_iff_measurable`：aemeasurable_iff_measurable [μ.IsComplete] 
: AEMeasurable f μ ↔ Measurable f
· 使用定理 `aemeasurable_of_tendsto_metrizable_ae'`：aemeasurable_of_tendsto_metrizab
le_ae' {μ : Measure α} {f : Nat -> α -> β} {g : α -> β} (hf : forall n, AEMeasur
able (f n) μ) (h_ae_tendsto …
· 使用定理 `Measurable.aemeasurable`：Measurable.aemeasurable (h : Measurable f) : AE
Measurable f μ
-/
theorem measurable_of_tendsto_metrizable_ae {μ : Measure α} [μ.IsComplete] {f : ℕ → α → β}
    {g : α → β} (hf : ∀ n, Measurable (f n))
    (h_ae_tendsto : ∀ᵐ x ∂μ, Tendsto (fun n => f n x) atTop (𝓝 (g x))) : Measurable g :=
  aemeasurable_iff_measurable.mp
    (aemeasurable_of_tendsto_metrizable_ae' (fun i => (hf i).aemeasurable) h_ae_tendsto)
/-
**measurable_limit_of_tendsto_metrizable_ae** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：measurable_limit_of_tendsto_metrizable_ae {ι} [Nonempty ι] {μ : Measure α}
 {f : ι -> α -> β} {L : Filter ι} [L.IsCountablyGenerated] (hf : forall n, AEMea
surable (f n) μ) (h_ae_tendsto : forallᵐ x ∂μ, exists l : β, Tendsto (fun n => f
 n x) L (𝓝 l)) : exists f_lim : α -> β, Measurable f_lim ∧ forallᵐ x ∂μ, Tendsto
 (fun n => f n x) L (𝓝 (f_lim x))
参数：hf : forall n, AEMeasurable (f n) μ；h_ae_tendsto : forallᵐ x ∂μ, exists l : β
, Tendsto (fun n => f n x) L (𝓝 l)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `Filter.eq_or_neBot`：eq_or_neBot (f : Filter α) : f = ⊥ ∨ NeBot f
· 使用定理 `AEMeasurable.measurable_mk`：measurable_mk (h : AEMeasurable f μ) : Measu
rable (h.mk f)
· 使用定理 `Filter.Eventually.of_forall`：∀ {α : Type u} {p : α → Prop} {f : Filter α
}, (∀ (x : α), p x) → ∀ᶠ (x : α) in f, p x
· 使用定理 `Filter.tendsto_bot`：tendsto_bot {f : α -> β} {l : Filter β} : Tendsto f 
⊥ l
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `dite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} {t : c → 
α} {e : ¬c → α} (h : c = True), dite c t e = t ⋯
· 使用定理 `Exists.choose_spec`：∀ {α : Sort u_1} {p : α → Prop} (P : ∃ a, p a), p P.
choose
· 使用定理 `aemeasurable_of_tendsto_metrizable_ae`：aemeasurable_of_tendsto_metrizabl
e_ae {ι} {μ : Measure α} {f : ι -> α -> β} {g : α -> β} (u : Filter ι) [hu : NeB
ot u] [IsCountablyGenerated…
· 使用定理 `AEMeasurable.ae_eq_mk`：ae_eq_mk (h : AEMeasurable f μ) : f =ᵐ[μ] h.mk f
-/
theorem measurable_limit_of_tendsto_metrizable_ae {ι} [Nonempty ι] {μ : Measure α}
    {f : ι → α → β} {L : Filter ι} [L.IsCountablyGenerated] (hf : ∀ n, AEMeasurable (f n) μ)
    (h_ae_tendsto : ∀ᵐ x ∂μ, ∃ l : β, Tendsto (fun n => f n x) L (𝓝 l)) :
    ∃ f_lim : α → β, Measurable f_lim ∧ ∀ᵐ x ∂μ, Tendsto (fun n => f n x) L (𝓝 (f_lim x)) := by
  classical
  inhabit ι
  rcases eq_or_neBot L with (rfl | hL)
  · exact ⟨(hf default).mk _, (hf default).measurable_mk, Eventually.of_forall fun x => tendsto_bot⟩
  set f_lim : α → β := fun x ↦
    if h : ∃ l : β, Tendsto (fun n ↦ f n x) L (𝓝 l) then h.choose
      else (⟨f default x⟩ : Nonempty β).some
  have h_ae_tendsto_f_lim : ∀ᵐ x ∂μ, Tendsto (fun n ↦ f n x) L (𝓝 (f_lim x)) := by
    filter_upwards [h_ae_tendsto] with x hx
    simpa [f_lim, hx] using hx.choose_spec
  have hf_lim : AEMeasurable f_lim μ :=
    aemeasurable_of_tendsto_metrizable_ae L hf h_ae_tendsto_f_lim
  refine ⟨hf_lim.mk f_lim, hf_lim.measurable_mk, ?_⟩
  filter_upwards [h_ae_tendsto_f_lim, hf_lim.ae_eq_mk] with x hx h_eq
  simpa [h_eq] using hx

end Limits

section TendstoIndicator

variable {α : Type*} [MeasurableSpace α] {A : Set α}
variable {ι : Type*} (L : Filter ι) [IsCountablyGenerated L] {As : ι → Set α}

/-- If the indicator functions of measurable sets `Aᵢ` converge to the indicator function of
a set `A` along a nontrivial countably generated filter, then `A` is also measurable. -/
/-
**measurableSet_of_tendsto_indicator** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：measurableSet_of_tendsto_indicator [NeBot L] (As_mble : forall i, Measurab
leSet (As i)) (h_lim : forall x, forallᶠ i in L, x in As i ↔ x in A) : Measurabl
eSet A
参数：As_mble : forall i, MeasurableSet (As i)；h_lim : forall x, forallᶠ i in L, x 
in As i ↔ x in A。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `measurable_indicator_const_iff`：measurable_indicator_const_iff [Zero β] 
[MeasurableSingletonClass β] (b : β) [NeZero b] : Measurable (s.indicator (fun (
_ : α) => b)) ↔ Meas…
· 使用定理 `instMeasurableSingletonClassOfMeasurableEq`：∀ {α : Type u_1} [inst : Mea
surableSpace α] [MeasurableEq α], MeasurableSingletonClass α
· 使用定理 `instMeasurableEqOfSecondCountableTopologyOfT2Space`：∀ {α : Type u_1} [in
st : TopologicalSpace α] [inst_1 : MeasurableSpace α] [OpensMeasurableSpace α]  
 [SecondCountableTopology α] [T2Space α]…
· 使用定理 `BorelSpace.opensMeasurable`：∀ {α : Type u_6} [inst : TopologicalSpace α]
 [inst_1 : MeasurableSpace α] [BorelSpace α], OpensMeasurableSpace α
· 使用定理 `ENNReal.instSecondCountableTopology`：SecondCountableTopology ENNReal
· 使用定理 `ENNReal.instT2Space`：T2Space ENNReal
· 使用定理 `ENNReal.instCharZero`：CharZero ENNReal
· 使用定理 `ENNReal.measurable_of_tendsto'`：measurable_of_tendsto' {ι : Type*} {f : 
ι -> α -> Real>=0∞} {g : α -> Real>=0∞} (u : Filter ι) [NeBot u] [IsCountablyGen
erated u] (hf : fora…
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `tendsto_indicator_const_iff_forall_eventually`：∀ {α : Type u_1} {A : Set
 α} {β : Type u_2} [inst : Zero β] [inst_1 : TopologicalSpace β] {ι : Type u_3} 
(L : Filter ι)   {As : ι → Set α} […
· 使用定理 `T5Space.toT1Space`：∀ {X : Type u} {inst : TopologicalSpace X} [self : T5
Space X], T1Space X
· 使用定理 `ENNReal.instT5Space`：T5Space ENNReal

--- 原说明 ---
If the indicator functions of measurable sets `Aᵢ` converge to the indicator fun
ction of
a set `A` along a nontrivial countably generated filter, then `A` is also measur
able.
-/
lemma measurableSet_of_tendsto_indicator [NeBot L] (As_mble : ∀ i, MeasurableSet (As i))
    (h_lim : ∀ x, ∀ᶠ i in L, x ∈ As i ↔ x ∈ A) :
    MeasurableSet A := by
  simp_rw [← measurable_indicator_const_iff (1 : ℝ≥0∞)] at As_mble ⊢
  exact ENNReal.measurable_of_tendsto' L As_mble
    ((tendsto_indicator_const_iff_forall_eventually L (1 : ℝ≥0∞)).mpr h_lim)

/-- If the indicator functions of a.e.-measurable sets `Aᵢ` converge a.e. to the indicator function
of a set `A` along a nontrivial countably generated filter, then `A` is also a.e.-measurable. -/
/-
**nullMeasurableSet_of_tendsto_indicator** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：nullMeasurableSet_of_tendsto_indicator [NeBot L] {μ : Measure α} (As_mble 
: forall i, NullMeasurableSet (As i) μ) (h_lim : forallᵐ x ∂μ, forallᶠ i in L, x
 in As i ↔ x in A) : NullMeasurableSet A μ
参数：As_mble : forall i, NullMeasurableSet (As i) μ；h_lim : forallᵐ x ∂μ, forallᶠ 
i in L, x in As i ↔ x in A。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `aemeasurable_indicator_const_iff`：aemeasurable_indicator_const_iff {s} [
MeasurableSingletonClass β] (b : β) [NeZero b] : AEMeasurable (s.indicator (fun 
_ => b)) μ ↔ NullMeasu…
· 使用定理 `instMeasurableSingletonClassOfMeasurableEq`：∀ {α : Type u_1} [inst : Mea
surableSpace α] [MeasurableEq α], MeasurableSingletonClass α
· 使用定理 `instMeasurableEqOfSecondCountableTopologyOfT2Space`：∀ {α : Type u_1} [in
st : TopologicalSpace α] [inst_1 : MeasurableSpace α] [OpensMeasurableSpace α]  
 [SecondCountableTopology α] [T2Space α]…
· 使用定理 `BorelSpace.opensMeasurable`：∀ {α : Type u_6} [inst : TopologicalSpace α]
 [inst_1 : MeasurableSpace α] [BorelSpace α], OpensMeasurableSpace α
· 使用定理 `ENNReal.instSecondCountableTopology`：SecondCountableTopology ENNReal
· 使用定理 `ENNReal.instT2Space`：T2Space ENNReal
· 使用定理 `ENNReal.instCharZero`：CharZero ENNReal
· 使用定理 `aemeasurable_of_tendsto_metrizable_ae`：aemeasurable_of_tendsto_metrizabl
e_ae {ι} {μ : Measure α} {f : ι -> α -> β} {g : α -> β} (u : Filter ι) [hu : NeB
ot u] [IsCountablyGenerated…
· 使用定理 `TopologicalSpace.MetrizableSpace.toPseudoMetrizableSpace`：∀ {X : Type u_
5} {t : TopologicalSpace X} [self : TopologicalSpace.MetrizableSpace X],   Topol
ogicalSpace.PseudoMetrizableSpace X
· 使用定理 `ENNReal.instMetrizableSpace`：TopologicalSpace.MetrizableSpace ENNReal
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `T5Space.toT1Space`：∀ {X : Type u} {inst : TopologicalSpace X} [self : T5
Space X], T1Space X
· 使用定理 `ENNReal.instT5Space`：T5Space ENNReal

--- 原说明 ---
If the indicator functions of a.e.-measurable sets `Aᵢ` converge a.e. to the ind
icator function
of a set `A` along a nontrivial countably generated filter, then `A` is also a.e
.-measurable.
-/
lemma nullMeasurableSet_of_tendsto_indicator [NeBot L] {μ : Measure α}
    (As_mble : ∀ i, NullMeasurableSet (As i) μ)
    (h_lim : ∀ᵐ x ∂μ, ∀ᶠ i in L, x ∈ As i ↔ x ∈ A) :
    NullMeasurableSet A μ := by
  simp_rw [← aemeasurable_indicator_const_iff (1 : ℝ≥0∞)] at As_mble ⊢
  apply aemeasurable_of_tendsto_metrizable_ae L As_mble
  simpa [tendsto_indicator_const_apply_iff_eventually] using h_lim

end TendstoIndicator

