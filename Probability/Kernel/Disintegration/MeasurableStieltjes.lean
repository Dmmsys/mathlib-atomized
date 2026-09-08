/-
Copyright (c) 2024 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Mathlib.MeasureTheory.Measure.GiryMonad
public import Mathlib.MeasureTheory.Measure.Stieltjes
public import Mathlib.Analysis.Normed.Order.Lattice
public import Mathlib.MeasureTheory.Function.StronglyMeasurable.Basic

/-!
# Measurable parametric Stieltjes functions

We provide tools to build a measurable function `α → StieltjesFunction ℝ` with limits 0 at -∞
and 1 at +∞ for all `a : α` from a measurable function `f : α → ℚ → ℝ`. These measurable parametric
Stieltjes functions are cumulative distribution functions (CDF) of transition kernels.
The reason for going through `ℚ` instead of defining directly a Stieltjes function is that since
`ℚ` is countable, building a measurable function is easier and we can obtain properties of the
form `∀ᵐ (a : α) ∂μ, ∀ (q : ℚ), ...` (for some measure `μ` on `α`) by proving the weaker
`∀ (q : ℚ), ∀ᵐ (a : α) ∂μ, ...`.

This construction will be possible if `f a : ℚ → ℝ` satisfies a package of properties for all `a`:
monotonicity, limits at +-∞ and a continuity property. We define `IsRatStieltjesPoint f a` to state
that this is the case at `a` and define the property `IsMeasurableRatCDF f` that `f` is measurable
and `IsRatStieltjesPoint f a` for all `a`.
The function `α → StieltjesFunction ℝ` obtained by extending `f` by continuity from the right is
then called `IsMeasurableRatCDF.stieltjesFunction`.

In applications, we will often only have `IsRatStieltjesPoint f a` almost surely with respect to
some measure. In order to turn that almost everywhere property into an everywhere property we define
`toRatCDF (f : α → ℚ → ℝ) := fun a q ↦ if IsRatStieltjesPoint f a then f a q else defaultRatCDF q`,
which satisfies the property `IsMeasurableRatCDF (toRatCDF f)`.

Finally, we define `stieltjesOfMeasurableRat`, composition of `toRatCDF` and
`IsMeasurableRatCDF.stieltjesFunction`.

## Main definitions

* `stieltjesOfMeasurableRat`: turn a measurable function `f : α → ℚ → ℝ` into a measurable
  function `α → StieltjesFunction ℝ`.

-/

@[expose] public section

open MeasureTheory Set Filter TopologicalSpace

open scoped NNReal ENNReal MeasureTheory Topology

/-- A measurable function `α → StieltjesFunction ℝ` with limits 0 at -∞ and 1 at +∞ gives a
measurable function `α → Measure ℝ` by taking `StieltjesFunction.measure` at each point. -/
/-
**StieltjesFunction.measurable_measure** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：StieltjesFunction.measurable_measure {α : Type*} {_ : MeasurableSpace α} {
f : α -> StieltjesFunction Real} (hf : forall q, Measurable fun a => f a q) (hf_
bot : forall a, Tendsto (f a) atBot (𝓝 0)) (hf_top : forall a, Tendsto (f a) atT
op (𝓝 1)) : Measurable fun a => (f a).measure
参数：hf : forall q, Measurable fun a => f a q；hf_bot : forall a, Tendsto (f a) atB
ot (𝓝 0)；hf_top : forall a, Tendsto (f a) atTop (𝓝 1)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instOrderTopologyReal`：OrderTopology ℝ
· 使用定理 `ConditionallyCompleteLinearOrder.toCompactIccSpace`：∀ (α : Type u_2) [in
st : ConditionallyCompleteLinearOrder α] [inst_1 : TopologicalSpace α] [OrderTop
ology α],   CompactIccSpace α
· 使用定理 `instSecondCountableTopologyReal`：SecondCountableTopology ℝ
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
· 使用引理 `StieltjesFunction.isProbabilityMeasure`：isProbabilityMeasure [Nonempty R
] (hf_bot : Tendsto f atBot (𝓝 0)) (hf_top : Tendsto f atTop (𝓝 1)) : IsProbabil
ityMeasure f.measure
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `Measurable.measure_of_isPiSystem_of_isProbabilityMeasure`：∀ {α : Type u_
1} {β : Type u_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {μ : α → Mea
sureTheory.Measure β}   [∀ (a : α), MeasureThe…
· 使用定理 `borel_eq_generateFrom_Iic`：borel_eq_generateFrom_Iic : borel α = Measura
bleSpace.generateFrom (range Iic)
· 使用定理 `isPiSystem_Iic`：isPiSystem_Iic : IsPiSystem (range Iic : Set (Set α))
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `StieltjesFunction.measure_Iic`：measure_Iic {l : Real} (hf : Tendsto f at
Bot (𝓝 l)) (x : R) : f.measure (Iic x) = ofReal (f x - l)
· 使用定理 `sub_zero`：∀ {G : Type u_3} [inst : SubNegZeroMonoid G] (a : G), a - 0 = 
a
· 使用定理 `Measurable.ennreal_ofReal`：Measurable.ennreal_ofReal {f : α -> Real} (hf
 : Measurable f) : Measurable fun x => ENNReal.ofReal (f x)

--- 原说明 ---
A measurable function `α → StieltjesFunction ℝ` with limits 0 at -∞ and 1 at +∞ 
gives a
measurable function `α → Measure ℝ` by taking `StieltjesFunction.measure` at eac
h point.
-/
lemma StieltjesFunction.measurable_measure {α : Type*} {_ : MeasurableSpace α}
    {f : α → StieltjesFunction ℝ} (hf : ∀ q, Measurable fun a ↦ f a q)
    (hf_bot : ∀ a, Tendsto (f a) atBot (𝓝 0))
    (hf_top : ∀ a, Tendsto (f a) atTop (𝓝 1)) :
    Measurable fun a ↦ (f a).measure :=
  have : ∀ a, IsProbabilityMeasure (f a).measure :=
    fun a ↦ (f a).isProbabilityMeasure (hf_bot a) (hf_top a)
  .measure_of_isPiSystem_of_isProbabilityMeasure (borel_eq_generateFrom_Iic ℝ) isPiSystem_Iic <| by
    simp_rw [forall_mem_range, StieltjesFunction.measure_Iic (f _) (hf_bot _), sub_zero]
    exact fun _ ↦ (hf _).ennreal_ofReal

namespace ProbabilityTheory

variable {α : Type*}

section IsMeasurableRatCDF

variable {f : α → ℚ → ℝ}

/-- `a : α` is a Stieltjes point for `f : α → ℚ → ℝ` if `f a` is monotone with limit 0 at -∞
and 1 at +∞ and satisfies a continuity property. -/
/-
**ProbabilityTheory.IsRatStieltjesPoint** 是 Mathlib 中的一个归纳类型，位于命名空间 `Probability
Theory`。
形式化陈述：{α : Type u_1} → (α → ℚ → ℝ) → α → Prop
参数：α → ℚ → ℝ。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`a : α` is a Stieltjes point for `f : α → ℚ → ℝ` if `f a` is monotone with limit
 0 at -∞
and 1 at +∞ and satisfies a continuity property.
-/
structure IsRatStieltjesPoint (f : α → ℚ → ℝ) (a : α) : Prop where
  mono : Monotone (f a)
  tendsto_atTop_one : Tendsto (f a) atTop (𝓝 1)
  tendsto_atBot_zero : Tendsto (f a) atBot (𝓝 0)
  iInf_rat_gt_eq : ∀ t : ℚ, ⨅ r : Ioi t, f a r = f a t
/-
**ProbabilityTheory.isRatStieltjesPoint_unit_prod_iff** 是 Mathlib 中的一个引理，位于命名空间 
`ProbabilityTheory`。
形式化陈述：isRatStieltjesPoint_unit_prod_iff (f : α -> Rat -> Real) (a : α) : IsRatSt
ieltjesPoint (fun p : Unit × α => f p.2) ((), a) ↔ IsRatStieltjesPoint f a
参数：f : α -> Rat -> Real；a : α。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ProbabilityTheory.IsRatStieltjesPoint.mono`：∀ {α : Type u_1} {f : α → ℚ 
→ ℝ} {a : α}, ProbabilityTheory.IsRatStieltjesPoint f a → Monotone (f a)
· 使用定理 `ProbabilityTheory.IsRatStieltjesPoint.tendsto_atTop_one`：∀ {α : Type u_1
} {f : α → ℚ → ℝ} {a : α},   ProbabilityTheory.IsRatStieltjesPoint f a → Filter.
Tendsto (f a) Filter.atTop (nhds 1)
· 使用定理 `ProbabilityTheory.IsRatStieltjesPoint.tendsto_atBot_zero`：∀ {α : Type u_
1} {f : α → ℚ → ℝ} {a : α},   ProbabilityTheory.IsRatStieltjesPoint f a → Filter
.Tendsto (f a) Filter.atBot (nhds 0)
· 使用定理 `ProbabilityTheory.IsRatStieltjesPoint.iInf_rat_gt_eq`：∀ {α : Type u_1} {
f : α → ℚ → ℝ} {a : α}, ProbabilityTheory.IsRatStieltjesPoint f a → ∀ (t : ℚ), ⨅
 r, f a ↑r = f a t
-/
lemma isRatStieltjesPoint_unit_prod_iff (f : α → ℚ → ℝ) (a : α) :
    IsRatStieltjesPoint (fun p : Unit × α ↦ f p.2) ((), a)
      ↔ IsRatStieltjesPoint f a := by
  constructor <;>
    exact fun h ↦ ⟨h.mono, h.tendsto_atTop_one, h.tendsto_atBot_zero, h.iInf_rat_gt_eq⟩
/-
**ProbabilityTheory.measurableSet_isRatStieltjesPoint** 是 Mathlib 中的一个引理，位于命名空间 
`ProbabilityTheory`。
形式化陈述：measurableSet_isRatStieltjesPoint [MeasurableSpace α] (hf : Measurable f) 
: MeasurableSet {a | IsRatStieltjesPoint f a}
参数：hf : Measurable f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Set.ofPred_forall`：ofPred_forall (p : ι -> β -> Prop) : { x | forall i, 
p i x } = ⋂ i, { x | p i x }
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `MeasurableSet.iInter`：MeasurableSet.iInter [Countable ι] {f : ι -> Set α
} (h : forall b, MeasurableSet (f b)) : MeasurableSet (⋂ b, f b)
· 使用定理 `Encodable.countable`：∀ {α : Type u_1} [Encodable α], Countable α
· 使用定理 `Prop.countable`：∀ (p : Prop), Countable p
· 使用定理 `measurableSet_le`：measurableSet_le {f g : δ -> α} (hf : Measurable f) (h
g : Measurable g) : MeasurableSet { a | f a <= g a }
· 使用定理 `BorelSpace.opensMeasurable`：∀ {α : Type u_6} [inst : TopologicalSpace α]
 [inst_1 : MeasurableSpace α] [BorelSpace α], OpensMeasurableSpace α
· 使用定理 `HasSolidNorm.orderClosedTopology`：∀ {E : Type u_2} [inst : NormedAddComm
Group E] [inst_1 : Lattice E] [HasSolidNorm E] [IsOrderedAddMonoid E],   OrderCl
osedTopology E
· 使用定理 `instHasSolidNormReal`：HasSolidNorm ℝ
· 使用定理 `instSecondCountableTopologyReal`：SecondCountableTopology ℝ
· 使用定理 `Measurable.eval`：Measurable.eval {a : δ} {g : α -> forall a, X a} (hg : 
Measurable g) : Measurable fun x => g x a
· 使用引理 `measurableSet_tendsto`：measurableSet_tendsto {_ : MeasurableSpace β} [Me
asurableSpace γ] [Countable δ] {l : Filter δ} [l.IsCountablyGenerated] (l' : Fil
ter γ) [l'.…
· 使用定理 `Rat.instOrderTopology`：OrderTopology ℚ
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
· 使用定理 `FirstCountableTopology.nhds_generated_countable`：∀ {α : Type u} {t : Top
ologicalSpace α} [self : FirstCountableTopology α] (a : α), (nhds a).IsCountably
Generated
· 使用定理 `TopologicalSpace.PseudoMetrizableSpace.firstCountableTopology`：∀ {X : Ty
pe u_2} [inst : TopologicalSpace X] [h : TopologicalSpace.PseudoMetrizableSpace 
X], FirstCountableTopology X
· 使用定理 `instIsCountablyGenerated_atBot`：∀ {α : Type u} [inst : TopologicalSpace 
α] [inst_1 : LinearOrder α] [OrderTopology α]   [TopologicalSpace.SeparableSpace
 α], Filter.atBot.Is…
· 使用定理 `measurableSet_eq_fun`：measurableSet_eq_fun {m : MeasurableSpace α} [Meas
urableSpace β] [MeasurableEq β] {f g : α -> β} (hf : Measurable f) (hg : Measura
ble g) : M…
· 使用定理 `StandardBorelSpace.instMeasurableEq`：∀ {α : Type u_1} [inst : Measurable
Space α] [StandardBorelSpace α], MeasurableEq α
· 使用定理 `standardBorel_of_polish`：∀ {α : Type u_1} [inst : MeasurableSpace α] [τ 
: TopologicalSpace α] [BorelSpace α] [PolishSpace α],   StandardBorelSpace α
· 使用定理 `instPolishSpaceOfSeparableSpaceOfIsCompletelyMetrizableSpace`：∀ {α : Typ
e u_1} [inst : TopologicalSpace α] [TopologicalSpace.SeparableSpace α]   [Topolo
gicalSpace.IsCompletelyMetrizableSpace α], PolishS…
· 使用定理 `TopologicalSpace.IsCompletelyMetrizableSpace.of_completeSpace_metrizable
`：∀ {X : Type u_1} [inst : UniformSpace X] [CompleteSpace X] [(uniformity X).IsC
ountablyGenerated] [T0Space X],   TopologicalSpace.IsCompletel…
· 使用定理 `EMetric.instIsCountablyGeneratedUniformity`：∀ {α : Type u} [inst : Pseud
oEMetricSpace α], (uniformity α).IsCountablyGenerated
· 使用定理 `T6Space.toT0Space`：∀ {X : Type u} {inst : TopologicalSpace X} [self : T6
Space X], T0Space X
· 使用定理 `instT6SpaceOfMetrizableSpace`：∀ {X : Type u_1} [inst : TopologicalSpace 
X] [TopologicalSpace.MetrizableSpace X], T6Space X
（共 43 条，此处仅展示前 30 条）
-/
lemma measurableSet_isRatStieltjesPoint [MeasurableSpace α] (hf : Measurable f) :
    MeasurableSet {a | IsRatStieltjesPoint f a} := by
  have h1 : MeasurableSet {a | Monotone (f a)} := by
    change MeasurableSet {a | ∀ q r (_ : q ≤ r), f a q ≤ f a r}
    simp_rw [Set.ofPred_forall]
    refine MeasurableSet.iInter (fun q ↦ ?_)
    refine MeasurableSet.iInter (fun r ↦ ?_)
    refine MeasurableSet.iInter (fun _ ↦ ?_)
    exact measurableSet_le hf.eval hf.eval
  have h2 : MeasurableSet {a | Tendsto (f a) atTop (𝓝 1)} :=
    measurableSet_tendsto _ (fun q ↦ hf.eval)
  have h3 : MeasurableSet {a | Tendsto (f a) atBot (𝓝 0)} :=
    measurableSet_tendsto _ (fun q ↦ hf.eval)
  have h4 : MeasurableSet {a | ∀ t : ℚ, ⨅ r : Ioi t, f a r = f a t} := by
    rw [Set.ofPred_forall]
    refine MeasurableSet.iInter (fun q ↦ ?_)
    exact measurableSet_eq_fun (.iInf fun _ ↦ hf.eval) hf.eval
  suffices {a | IsRatStieltjesPoint f a}
      = ({a | Monotone (f a)} ∩ {a | Tendsto (f a) atTop (𝓝 1)} ∩ {a | Tendsto (f a) atBot (𝓝 0)}
        ∩ {a | ∀ t : ℚ, ⨅ r : Ioi t, f a r = f a t}) by
    rw [this]
    exact (((h1.inter h2).inter h3).inter h4)
  ext a
  simp only [mem_ofPred_eq, mem_inter_iff]
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · exact ⟨⟨⟨h.mono, h.tendsto_atTop_one⟩, h.tendsto_atBot_zero⟩, h.iInf_rat_gt_eq⟩
  · exact ⟨h.1.1.1, h.1.1.2, h.1.2, h.2⟩
/-
**ProbabilityTheory.IsRatStieltjesPoint.ite** 是 Mathlib 中的一个定理，位于命名空间 `Probabili
tyTheory.IsRatStieltjesPoint`。
形式化陈述：∀ {α : Type u_1} {f g : α → ℚ → ℝ} {a : α} (p : α → Prop) [inst : Decidabl
ePred p],   (p a → ProbabilityTheory.IsRatStieltjesPoint f a) →     (¬p a → Prob
abilityTheory.IsRatStieltjesPoint g a) →       ProbabilityTheory.IsRatStieltjesP
oint (fun a => if p a then f a else g a) a
参数：p : α → Prop；p a → ProbabilityTheory.IsRatStieltjesPoint f a；¬p a → Probabili
tyTheory.IsRatStieltjesPoint g a；fun a => if p a then f a else g a。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用定理 `ProbabilityTheory.IsRatStieltjesPoint.mono`：∀ {α : Type u_1} {f : α → ℚ 
→ ℝ} {a : α}, ProbabilityTheory.IsRatStieltjesPoint f a → Monotone (f a)
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `ProbabilityTheory.IsRatStieltjesPoint.tendsto_atTop_one`：∀ {α : Type u_1
} {f : α → ℚ → ℝ} {a : α},   ProbabilityTheory.IsRatStieltjesPoint f a → Filter.
Tendsto (f a) Filter.atTop (nhds 1)
· 使用定理 `ProbabilityTheory.IsRatStieltjesPoint.tendsto_atBot_zero`：∀ {α : Type u_
1} {f : α → ℚ → ℝ} {a : α},   ProbabilityTheory.IsRatStieltjesPoint f a → Filter
.Tendsto (f a) Filter.atBot (nhds 0)
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `ProbabilityTheory.IsRatStieltjesPoint.iInf_rat_gt_eq`：∀ {α : Type u_1} {
f : α → ℚ → ℝ} {a : α}, ProbabilityTheory.IsRatStieltjesPoint f a → ∀ (t : ℚ), ⨅
 r, f a ↑r = f a t
-/
lemma IsRatStieltjesPoint.ite {f g : α → ℚ → ℝ} {a : α} (p : α → Prop) [DecidablePred p]
    (hf : p a → IsRatStieltjesPoint f a) (hg : ¬ p a → IsRatStieltjesPoint g a) :
    IsRatStieltjesPoint (fun a ↦ if p a then f a else g a) a where
  mono := by split_ifs with h; exacts [(hf h).mono, (hg h).mono]
  tendsto_atTop_one := by
    split_ifs with h; exacts [(hf h).tendsto_atTop_one, (hg h).tendsto_atTop_one]
  tendsto_atBot_zero := by
    split_ifs with h; exacts [(hf h).tendsto_atBot_zero, (hg h).tendsto_atBot_zero]
  iInf_rat_gt_eq := by split_ifs with h; exacts [(hf h).iInf_rat_gt_eq, (hg h).iInf_rat_gt_eq]

variable [MeasurableSpace α]

/-- A function `f : α → ℚ → ℝ` is a (kernel) rational cumulative distribution function if it is
measurable in the first argument and if `f a` satisfies a list of properties for all `a : α`:
monotonicity between 0 at -∞ and 1 at +∞ and a form of continuity.

A function with these properties can be extended to a measurable function `α → StieltjesFunction ℝ`.
See `ProbabilityTheory.IsMeasurableRatCDF.stieltjesFunction`.
-/
/-
**ProbabilityTheory.IsMeasurableRatCDF** 是 Mathlib 中的一个归纳类型，位于命名空间 `ProbabilityT
heory`。
形式化陈述：{α : Type u_1} → [MeasurableSpace α] → (α → ℚ → ℝ) → Prop
参数：α → ℚ → ℝ。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A function `f : α → ℚ → ℝ` is a (kernel) rational cumulative distribution functi
on if it is
measurable in the first argument and if `f a` satisfies a list of properties for
 all `a : α`:
monotonicity between 0 at -∞ and 1 at +∞ and a form of continuity.

A function with these properties can be extended to a measurable function `α → S
tieltjesFunction ℝ`.
See `ProbabilityTheory.IsMeasurableRatCDF.stieltjesFunction`.
-/
structure IsMeasurableRatCDF (f : α → ℚ → ℝ) : Prop where
  isRatStieltjesPoint : ∀ a, IsRatStieltjesPoint f a
  measurable : Measurable f
/-
**ProbabilityTheory.IsMeasurableRatCDF.nonneg** 是 Mathlib 中的一个定理，位于命名空间 `Probabi
lityTheory.IsMeasurableRatCDF`。
形式化陈述：∀ {α : Type u_1} [inst : MeasurableSpace α] {f : α → ℚ → ℝ},   Probability
Theory.IsMeasurableRatCDF f → ∀ (a : α) (q : ℚ), 0 ≤ f a q
参数：a : α；q : ℚ。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Monotone.le_of_tendsto`：Monotone.le_of_tendsto [TopologicalSpace α] [Pre
order α] [OrderClosedTopology α] [Preorder β] [IsCodirectedOrder β] {f : β -> α}
 {a : α} (hf…
· 使用定理 `HasSolidNorm.orderClosedTopology`：∀ {E : Type u_2} [inst : NormedAddComm
Group E] [inst_1 : Lattice E] [HasSolidNorm E] [IsOrderedAddMonoid E],   OrderCl
osedTopology E
· 使用定理 `instHasSolidNormReal`：HasSolidNorm ℝ
· 使用定理 `instIsCodirectedOrder`：∀ {R : Type u_3} [inst : Ring R] [inst_1 : Partia
lOrder R] [IsOrderedRing R] [Archimedean R], IsCodirectedOrder R
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `instArchimedeanRat`：Archimedean ℚ
· 使用定理 `ProbabilityTheory.IsRatStieltjesPoint.mono`：∀ {α : Type u_1} {f : α → ℚ 
→ ℝ} {a : α}, ProbabilityTheory.IsRatStieltjesPoint f a → Monotone (f a)
· 使用定理 `ProbabilityTheory.IsMeasurableRatCDF.isRatStieltjesPoint`：∀ {α : Type u_
1} [inst : MeasurableSpace α] {f : α → ℚ → ℝ},   ProbabilityTheory.IsMeasurableR
atCDF f → ∀ (a : α), ProbabilityTheory.IsRatSt…
· 使用定理 `ProbabilityTheory.IsRatStieltjesPoint.tendsto_atBot_zero`：∀ {α : Type u_
1} {f : α → ℚ → ℝ} {a : α},   ProbabilityTheory.IsRatStieltjesPoint f a → Filter
.Tendsto (f a) Filter.atBot (nhds 0)
-/
lemma IsMeasurableRatCDF.nonneg {f : α → ℚ → ℝ} (hf : IsMeasurableRatCDF f) (a : α) (q : ℚ) :
    0 ≤ f a q :=
  Monotone.le_of_tendsto (hf.isRatStieltjesPoint a).mono
    (hf.isRatStieltjesPoint a).tendsto_atBot_zero q
/-
**ProbabilityTheory.IsMeasurableRatCDF.le_one** 是 Mathlib 中的一个定理，位于命名空间 `Probabi
lityTheory.IsMeasurableRatCDF`。
形式化陈述：∀ {α : Type u_1} [inst : MeasurableSpace α] {f : α → ℚ → ℝ},   Probability
Theory.IsMeasurableRatCDF f → ∀ (a : α) (q : ℚ), f a q ≤ 1
参数：a : α；q : ℚ。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Monotone.ge_of_tendsto`：Monotone.ge_of_tendsto [TopologicalSpace α] [Pre
order α] [OrderClosedTopology α] [Preorder β] [IsDirectedOrder β] {f : β -> α} {
a : α} (hf :…
· 使用定理 `HasSolidNorm.orderClosedTopology`：∀ {E : Type u_2} [inst : NormedAddComm
Group E] [inst_1 : Lattice E] [HasSolidNorm E] [IsOrderedAddMonoid E],   OrderCl
osedTopology E
· 使用定理 `instHasSolidNormReal`：HasSolidNorm ℝ
· 使用定理 `instIsDirectedOrder`：∀ {R : Type u_3} [inst : Semiring R] [inst_1 : Part
ialOrder R] [IsOrderedRing R] [Archimedean R], IsDirectedOrder R
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `instArchimedeanRat`：Archimedean ℚ
· 使用定理 `ProbabilityTheory.IsRatStieltjesPoint.mono`：∀ {α : Type u_1} {f : α → ℚ 
→ ℝ} {a : α}, ProbabilityTheory.IsRatStieltjesPoint f a → Monotone (f a)
· 使用定理 `ProbabilityTheory.IsMeasurableRatCDF.isRatStieltjesPoint`：∀ {α : Type u_
1} [inst : MeasurableSpace α] {f : α → ℚ → ℝ},   ProbabilityTheory.IsMeasurableR
atCDF f → ∀ (a : α), ProbabilityTheory.IsRatSt…
· 使用定理 `ProbabilityTheory.IsRatStieltjesPoint.tendsto_atTop_one`：∀ {α : Type u_1
} {f : α → ℚ → ℝ} {a : α},   ProbabilityTheory.IsRatStieltjesPoint f a → Filter.
Tendsto (f a) Filter.atTop (nhds 1)
-/
lemma IsMeasurableRatCDF.le_one {f : α → ℚ → ℝ} (hf : IsMeasurableRatCDF f) (a : α) (q : ℚ) :
    f a q ≤ 1 :=
  Monotone.ge_of_tendsto (hf.isRatStieltjesPoint a).mono
    (hf.isRatStieltjesPoint a).tendsto_atTop_one q
/-
**ProbabilityTheory.IsMeasurableRatCDF.tendsto_atTop_one** 是 Mathlib 中的一个定理，位于命名
空间 `ProbabilityTheory.IsMeasurableRatCDF`。
形式化陈述：∀ {α : Type u_1} [inst : MeasurableSpace α] {f : α → ℚ → ℝ},   Probability
Theory.IsMeasurableRatCDF f → ∀ (a : α), Filter.Tendsto (f a) Filter.atTop (nhds
 1)
参数：a : α；f a；nhds 1。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ProbabilityTheory.IsRatStieltjesPoint.tendsto_atTop_one`：∀ {α : Type u_1
} {f : α → ℚ → ℝ} {a : α},   ProbabilityTheory.IsRatStieltjesPoint f a → Filter.
Tendsto (f a) Filter.atTop (nhds 1)
· 使用定理 `ProbabilityTheory.IsMeasurableRatCDF.isRatStieltjesPoint`：∀ {α : Type u_
1} [inst : MeasurableSpace α] {f : α → ℚ → ℝ},   ProbabilityTheory.IsMeasurableR
atCDF f → ∀ (a : α), ProbabilityTheory.IsRatSt…
-/
lemma IsMeasurableRatCDF.tendsto_atTop_one {f : α → ℚ → ℝ} (hf : IsMeasurableRatCDF f) (a : α) :
    Tendsto (f a) atTop (𝓝 1) := (hf.isRatStieltjesPoint a).tendsto_atTop_one
/-
**ProbabilityTheory.IsMeasurableRatCDF.tendsto_atBot_zero** 是 Mathlib 中的一个定理，位于命
名空间 `ProbabilityTheory.IsMeasurableRatCDF`。
形式化陈述：∀ {α : Type u_1} [inst : MeasurableSpace α] {f : α → ℚ → ℝ},   Probability
Theory.IsMeasurableRatCDF f → ∀ (a : α), Filter.Tendsto (f a) Filter.atBot (nhds
 0)
参数：a : α；f a；nhds 0。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ProbabilityTheory.IsRatStieltjesPoint.tendsto_atBot_zero`：∀ {α : Type u_
1} {f : α → ℚ → ℝ} {a : α},   ProbabilityTheory.IsRatStieltjesPoint f a → Filter
.Tendsto (f a) Filter.atBot (nhds 0)
· 使用定理 `ProbabilityTheory.IsMeasurableRatCDF.isRatStieltjesPoint`：∀ {α : Type u_
1} [inst : MeasurableSpace α] {f : α → ℚ → ℝ},   ProbabilityTheory.IsMeasurableR
atCDF f → ∀ (a : α), ProbabilityTheory.IsRatSt…
-/
lemma IsMeasurableRatCDF.tendsto_atBot_zero {f : α → ℚ → ℝ} (hf : IsMeasurableRatCDF f) (a : α) :
    Tendsto (f a) atBot (𝓝 0) := (hf.isRatStieltjesPoint a).tendsto_atBot_zero
/-
**ProbabilityTheory.IsMeasurableRatCDF.iInf_rat_gt_eq** 是 Mathlib 中的一个定理，位于命名空间 
`ProbabilityTheory.IsMeasurableRatCDF`。
形式化陈述：∀ {α : Type u_1} [inst : MeasurableSpace α] {f : α → ℚ → ℝ},   Probability
Theory.IsMeasurableRatCDF f → ∀ (a : α) (q : ℚ), ⨅ r, f a ↑r = f a q
参数：a : α；q : ℚ。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ProbabilityTheory.IsRatStieltjesPoint.iInf_rat_gt_eq`：∀ {α : Type u_1} {
f : α → ℚ → ℝ} {a : α}, ProbabilityTheory.IsRatStieltjesPoint f a → ∀ (t : ℚ), ⨅
 r, f a ↑r = f a t
· 使用定理 `ProbabilityTheory.IsMeasurableRatCDF.isRatStieltjesPoint`：∀ {α : Type u_
1} [inst : MeasurableSpace α] {f : α → ℚ → ℝ},   ProbabilityTheory.IsMeasurableR
atCDF f → ∀ (a : α), ProbabilityTheory.IsRatSt…
-/
lemma IsMeasurableRatCDF.iInf_rat_gt_eq {f : α → ℚ → ℝ} (hf : IsMeasurableRatCDF f) (a : α)
    (q : ℚ) :
    ⨅ r : Ioi q, f a r = f a q := (hf.isRatStieltjesPoint a).iInf_rat_gt_eq q

end IsMeasurableRatCDF

section DefaultRatCDF

/-- A function with the property `IsMeasurableRatCDF`.
Used in a piecewise construction to convert a function which only satisfies the properties
defining `IsMeasurableRatCDF` on some set into a true `IsMeasurableRatCDF`. -/
/-
**ProbabilityTheory.defaultRatCDF** 是 Mathlib 中的一个定义，位于命名空间 `ProbabilityTheory`。
形式化陈述：defaultRatCDF (q : Rat)
参数：q : Rat。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A function with the property `IsMeasurableRatCDF`.
Used in a piecewise construction to convert a function which only satisfies the 
properties
defining `IsMeasurableRatCDF` on some set into a true `IsMeasurableRatCDF`.
-/
def defaultRatCDF (q : ℚ) := if q < 0 then (0 : ℝ) else 1
/-
**ProbabilityTheory.monotone_defaultRatCDF** 是 Mathlib 中的一个引理，位于命名空间 `Probabilit
yTheory`。
形式化陈述：monotone_defaultRatCDF : Monotone defaultRatCDF
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用引理 `le_rfl`：le_rfl : a <= a
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
· 使用定理 `zero_le_one`：∀ {α : Type u_1} [inst : Zero α] [inst_1 : One α] [inst_2 :
 LE α] [ZeroLEOneClass α], 0 ≤ 1
· 使用定理 `LE.le.trans_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b 
→ b < c → a < c
-/
lemma monotone_defaultRatCDF : Monotone defaultRatCDF := by
  unfold defaultRatCDF
  intro x y hxy
  dsimp only
  split_ifs with h_1 h_2 h_2
  exacts [le_rfl, zero_le_one, absurd (hxy.trans_lt h_2) h_1, le_rfl]
/-
**ProbabilityTheory.defaultRatCDF_nonneg** 是 Mathlib 中的一个引理，位于命名空间 `ProbabilityT
heory`。
形式化陈述：defaultRatCDF_nonneg (q : Rat) : 0 <= defaultRatCDF q
参数：q : Rat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用引理 `le_rfl`：le_rfl : a <= a
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
· 使用定理 `zero_le_one`：∀ {α : Type u_1} [inst : Zero α] [inst_1 : One α] [inst_2 :
 LE α] [ZeroLEOneClass α], 0 ≤ 1
-/
lemma defaultRatCDF_nonneg (q : ℚ) : 0 ≤ defaultRatCDF q := by
  unfold defaultRatCDF
  split_ifs
  exacts [le_rfl, zero_le_one]
/-
**ProbabilityTheory.defaultRatCDF_le_one** 是 Mathlib 中的一个引理，位于命名空间 `ProbabilityT
heory`。
形式化陈述：defaultRatCDF_le_one (q : Rat) : defaultRatCDF q <= 1
参数：q : Rat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
-/
lemma defaultRatCDF_le_one (q : ℚ) : defaultRatCDF q ≤ 1 := by
  unfold defaultRatCDF
  split_ifs <;> simp
/-
**ProbabilityTheory.tendsto_defaultRatCDF_atTop** 是 Mathlib 中的一个引理，位于命名空间 `Proba
bilityTheory`。
形式化陈述：tendsto_defaultRatCDF_atTop : Tendsto defaultRatCDF atTop (𝓝 1)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Filter.tendsto_congr'`：tendsto_congr' {f₁ f₂ : α -> β} {l₁ : Filter α} {
l₂ : Filter β} (hl : f₁ =ᶠ[l₁] f₂) : Tendsto f₁ l₁ l₂ ↔ Tendsto f₂ l₁ l₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Filter.EventuallyEq.eq_1`：∀ {α : Type u_1} {β : Type u_2} (l : Filter α)
 (f g : α → β), (f =ᶠ[l] g) = ∀ᶠ (x : α) in l, f x = g x
· 使用引理 `Filter.eventually_atTop`：eventually_atTop : (forallᶠ x in atTop, p x) ↔ 
exists a, forall b, a <= b -> p b
· 使用定理 `instIsDirectedOrder`：∀ {R : Type u_3} [inst : Semiring R] [inst_1 : Part
ialOrder R] [IsOrderedRing R] [Archimedean R], IsDirectedOrder R
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `instArchimedeanRat`：Archimedean ℚ
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `not_lt`：∀ {α : Type u_1} [inst : LinearOrder α] {a b : α}, ¬a < b ↔ b ≤ 
a
· 使用定理 `tendsto_const_nhds`：tendsto_const_nhds {f : Filter α} : Tendsto (fun _ :
 α => x) f (𝓝 x)
-/
lemma tendsto_defaultRatCDF_atTop : Tendsto defaultRatCDF atTop (𝓝 1) := by
  refine (tendsto_congr' ?_).mp tendsto_const_nhds
  rw [EventuallyEq, eventually_atTop]
  exact ⟨0, fun q hq => (if_neg (not_lt.mpr hq)).symm⟩
/-
**ProbabilityTheory.tendsto_defaultRatCDF_atBot** 是 Mathlib 中的一个引理，位于命名空间 `Proba
bilityTheory`。
形式化陈述：tendsto_defaultRatCDF_atBot : Tendsto defaultRatCDF atBot (𝓝 0)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Filter.tendsto_congr'`：tendsto_congr' {f₁ f₂ : α -> β} {l₁ : Filter α} {
l₂ : Filter β} (hl : f₁ =ᶠ[l₁] f₂) : Tendsto f₁ l₁ l₂ ↔ Tendsto f₂ l₁ l₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Filter.EventuallyEq.eq_1`：∀ {α : Type u_1} {β : Type u_2} (l : Filter α)
 (f g : α → β), (f =ᶠ[l] g) = ∀ᶠ (x : α) in l, f x = g x
· 使用定理 `Filter.eventually_atBot`：∀ {α : Type u_3} [inst : Preorder α] [IsCodirec
tedOrder α] {p : α → Prop} [Nonempty α],   (∀ᶠ (x : α) in Filter.atBot, p x) ↔ ∃
 a, ∀ b ≤ a, …
· 使用定理 `instIsCodirectedOrder`：∀ {R : Type u_3} [inst : Ring R] [inst_1 : Partia
lOrder R] [IsOrderedRing R] [Archimedean R], IsCodirectedOrder R
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `instArchimedeanRat`：Archimedean ℚ
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用定理 `LE.le.trans_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b 
→ b < c → a < c
· 使用定理 `lt_of_not_ge`：∀ {α : Type u_1} [inst : LinearOrder α] {a b : α}, ¬b ≤ a 
→ a < b
· 使用定理 `Mathlib.Tactic.Linarith.lt_irrefl`：lt_irrefl {α : Type u} [Preorder α] {
a : α} : ¬a < a
· 使用定理 `Mathlib.Tactic.Ring.of_eq`：∀ {α : Sort u_2} {a b c : α}, a = c → b = c →
 a = b
· 使用定理 `Mathlib.Tactic.Ring.Common.add_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' + b' = c → a + b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.neg_congr`：∀ {R : Type u_2} [inst : CommRing 
R] {a a' b : R}, a = a' → -a' = b → -a = b
· 使用定理 `Mathlib.Tactic.Ring.cast_pos`：∀ {R : Type u_1} [inst : CommSemiring R] {
a : R} {n : ℕ}, Mathlib.Meta.NormNum.IsNat a n → a = n.rawCast + 0
· 使用定理 `Mathlib.Meta.NormNum.isNat_ofNat`：isNat_ofNat (α : Type u) [AddMonoidWit
hOne α] {a : α} {n : Nat} (h : n = a) : IsNat a n
· 使用定理 `Mathlib.Tactic.Ring.Common.neg_add`：∀ {R : Type u_2} [inst : CommRing R]
 {a₁ a₂ b₁ b₂ : R}, -a₁ = b₁ → -a₂ = b₂ → -(a₁ + a₂) = b₁ + b₂
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
· 使用定理 `Mathlib.Tactic.Ring.Common.sub_congr`：∀ {R : Type u_2} [inst : CommRing 
R] {a a' b b' c : R}, a = a' → b = b' → a' - b' = c → a - b = c
· 使用定理 `Mathlib.Tactic.Ring.cast_zero`：∀ {R : Type u_1} [inst : CommSemiring R] 
{a : R}, Mathlib.Meta.NormNum.IsNat a 0 → a = 0
· 使用定理 `Mathlib.Tactic.Ring.Common.sub_pf`：∀ {R : Type u_2} [inst : CommRing R] 
{a b c d : R}, -b = c → a + c = d → a - b = d
· 使用定理 `Mathlib.Meta.NormNum.IsNat.to_raw_eq`：∀ {α : Type u} {a : α} {n : ℕ} [in
st : AddMonoidWithOne α], Mathlib.Meta.NormNum.IsNat a n → a = n.rawCast
· 使用定理 `Mathlib.Meta.NormNum.IsInt.to_isNat`：∀ {α : Type u_1} [inst : Ring α] {a
 : α} {n : ℕ},   Mathlib.Meta.NormNum.IsInt a (Int.ofNat n) → Mathlib.Meta.NormN
um.IsNat a n
（共 39 条，此处仅展示前 30 条）
-/
lemma tendsto_defaultRatCDF_atBot : Tendsto defaultRatCDF atBot (𝓝 0) := by
  refine (tendsto_congr' ?_).mp tendsto_const_nhds
  rw [EventuallyEq, eventually_atBot]
  refine ⟨-1, fun q hq => (if_pos (hq.trans_lt ?_)).symm⟩
  linarith

set_option backward.isDefEq.respectTransparency false in
/-
**ProbabilityTheory.iInf_rat_gt_defaultRatCDF** 是 Mathlib 中的一个引理，位于命名空间 `Probabi
lityTheory`。
形式化陈述：iInf_rat_gt_defaultRatCDF (t : Rat) : ⨅ r : Ioi t, defaultRatCDF r = defau
ltRatCDF t
参数：t : Rat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.mem_range`：∀ {α : Type u} {ι : Sort u_1} {f : ι → α} {x : α}, x ∈ Se
t.range f ↔ ∃ y, f y = x
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用引理 `le_rfl`：le_rfl : a <= a
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
· 使用定理 `zero_le_one`：∀ {α : Type u_1} [inst : Zero α] [inst_1 : One α] [inst_2 :
 LE α] [ZeroLEOneClass α], 0 ≤ 1
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `lt_of_not_ge`：∀ {α : Type u_1} [inst : LinearOrder α] {a b : α}, ¬b ≤ a 
→ a < b
· 使用定理 `Mathlib.Tactic.Linarith.lt_irrefl`：lt_irrefl {α : Type u} [Preorder α] {
a : α} : ¬a < a
· 使用定理 `Mathlib.Tactic.Ring.of_eq`：∀ {α : Sort u_2} {a b c : α}, a = c → b = c →
 a = b
· 使用定理 `Mathlib.Tactic.Ring.Common.add_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' + b' = c → a + b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.sub_congr`：∀ {R : Type u_2} [inst : CommRing 
R] {a a' b b' c : R}, a = a' → b = b' → a' - b' = c → a - b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.atom_pf`：∀ {R : Type u_1} [inst : CommSemirin
g R] {b : R} (a : R) {e : ℕ},   Nat.rawCast 1 = e → a ^ e * Nat.rawCast 1 = b → 
a = b + 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Mathlib.Tactic.Ring.cast_zero`：∀ {R : Type u_1} [inst : CommSemiring R] 
{a : R}, Mathlib.Meta.NormNum.IsNat a 0 → a = 0
· 使用定理 `Mathlib.Meta.NormNum.isNat_ofNat`：isNat_ofNat (α : Type u) [AddMonoidWit
hOne α] {a : α} {n : Nat} (h : n = a) : IsNat a n
· 使用定理 `Mathlib.Tactic.Ring.Common.sub_pf`：∀ {R : Type u_2} [inst : CommRing R] 
{a b c d : R}, -b = c → a + c = d → a - b = d
· 使用定理 `Mathlib.Tactic.Ring.Common.neg_zero`：∀ {R : Type u_2} [inst : CommRing R
], -0 = 0
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_add_zero`：∀ {R : Type u_1} [inst : Com
mSemiring R] (a : R), a + 0 = a
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' * b' = c → a * b = c
· 使用定理 `Mathlib.Tactic.Ring.cast_pos`：∀ {R : Type u_1} [inst : CommSemiring R] {
a : R} {n : ℕ}, Mathlib.Meta.NormNum.IsNat a n → a = n.rawCast + 0
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
· 使用定理 `Mathlib.Tactic.Ring.Common.zero_mul`：∀ {R : Type u_1} [inst : CommSemiri
ng R] (b : R), 0 * b = 0
（共 75 条，此处仅展示前 30 条）
-/
lemma iInf_rat_gt_defaultRatCDF (t : ℚ) :
    ⨅ r : Ioi t, defaultRatCDF r = defaultRatCDF t := by
  simp only [defaultRatCDF]
  have h_bdd : BddBelow (range fun r : ↥(Ioi t) ↦ ite ((r : ℚ) < 0) (0 : ℝ) 1) := by
    refine ⟨0, fun x hx ↦ ?_⟩
    obtain ⟨y, rfl⟩ := mem_range.mpr hx
    dsimp only
    split_ifs
    exacts [le_rfl, zero_le_one]
  split_ifs with h
  · refine le_antisymm ?_ (le_ciInf fun x ↦ ?_)
    · obtain ⟨q, htq, hq_neg⟩ : ∃ q, t < q ∧ q < 0 := ⟨t / 2, by linarith, by linarith⟩
      refine (ciInf_le h_bdd ⟨q, htq⟩).trans ?_
      rw [if_pos]
      rwa [Subtype.coe_mk]
    · split_ifs
      exacts [le_rfl, zero_le_one]
  · refine le_antisymm ?_ ?_
    · refine (ciInf_le h_bdd ⟨t + 1, lt_add_one t⟩).trans ?_
      split_ifs
      exacts [zero_le_one, le_rfl]
    · refine le_ciInf fun x ↦ ?_
      rw [if_neg]
      rw [not_lt] at h ⊢
      exact h.trans (mem_Ioi.mp x.prop).le
/-
**ProbabilityTheory.isRatStieltjesPoint_defaultRatCDF** 是 Mathlib 中的一个引理，位于命名空间 
`ProbabilityTheory`。
形式化陈述：isRatStieltjesPoint_defaultRatCDF (a : α) : IsRatStieltjesPoint (fun (_ : 
α) => defaultRatCDF) a where mono
参数：a : α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `ProbabilityTheory.monotone_defaultRatCDF`：monotone_defaultRatCDF : Monot
one defaultRatCDF
· 使用引理 `ProbabilityTheory.tendsto_defaultRatCDF_atTop`：tendsto_defaultRatCDF_atT
op : Tendsto defaultRatCDF atTop (𝓝 1)
· 使用引理 `ProbabilityTheory.tendsto_defaultRatCDF_atBot`：tendsto_defaultRatCDF_atB
ot : Tendsto defaultRatCDF atBot (𝓝 0)
· 使用引理 `ProbabilityTheory.iInf_rat_gt_defaultRatCDF`：iInf_rat_gt_defaultRatCDF (
t : Rat) : ⨅ r : Ioi t, defaultRatCDF r = defaultRatCDF t
-/
lemma isRatStieltjesPoint_defaultRatCDF (a : α) :
    IsRatStieltjesPoint (fun (_ : α) ↦ defaultRatCDF) a where
  mono := monotone_defaultRatCDF
  tendsto_atTop_one := tendsto_defaultRatCDF_atTop
  tendsto_atBot_zero := tendsto_defaultRatCDF_atBot
  iInf_rat_gt_eq := iInf_rat_gt_defaultRatCDF
/-
**ProbabilityTheory.IsMeasurableRatCDF_defaultRatCDF** 是 Mathlib 中的一个引理，位于命名空间 `
ProbabilityTheory`。
形式化陈述：IsMeasurableRatCDF_defaultRatCDF (α : Type*) [MeasurableSpace α] : IsMeasu
rableRatCDF (fun (_ : α) (q : Rat) => defaultRatCDF q) where isRatStieltjesPoint
参数：α : Type*。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `ProbabilityTheory.isRatStieltjesPoint_defaultRatCDF`：isRatStieltjesPoint
_defaultRatCDF (a : α) : IsRatStieltjesPoint (fun (_ : α) => defaultRatCDF) a wh
ere mono
· 使用定理 `measurable_const`：measurable_const {_ : MeasurableSpace α} {_ : Measurab
leSpace β} {a : α} : Measurable fun _ : β => a
-/
lemma IsMeasurableRatCDF_defaultRatCDF (α : Type*) [MeasurableSpace α] :
    IsMeasurableRatCDF (fun (_ : α) (q : ℚ) ↦ defaultRatCDF q) where
  isRatStieltjesPoint := isRatStieltjesPoint_defaultRatCDF
  measurable := measurable_const

end DefaultRatCDF

section ToRatCDF

variable {f : α → ℚ → ℝ}

open scoped Classical in
/-- Turn a function `f : α → ℚ → ℝ` into another with the property `IsRatStieltjesPoint f a`
everywhere. At `a` that does not satisfy that property, `f a` is replaced by an arbitrary suitable
function.
Mainly useful when `f` satisfies the property `IsRatStieltjesPoint f a` almost everywhere with
respect to some measure. -/
noncomputable
/-
**ProbabilityTheory.toRatCDF** 是 Mathlib 中的一个定义，位于命名空间 `ProbabilityTheory`。
形式化陈述：toRatCDF (f : α -> Rat -> Real) : α -> Rat -> Real
参数：f : α -> Rat -> Real。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def toRatCDF (f : α → ℚ → ℝ) : α → ℚ → ℝ := fun a ↦
  if IsRatStieltjesPoint f a then f a else defaultRatCDF
/-
**ProbabilityTheory.toRatCDF_of_isRatStieltjesPoint** 是 Mathlib 中的一个引理，位于命名空间 `P
robabilityTheory`。
形式化陈述：toRatCDF_of_isRatStieltjesPoint {a : α} (h : IsRatStieltjesPoint f a) (q :
 Rat) : toRatCDF f a q = f a q
参数：h : IsRatStieltjesPoint f a；q : Rat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ProbabilityTheory.toRatCDF.eq_1`：∀ {α : Type u_1} (f : α → ℚ → ℝ) (a : α
),   ProbabilityTheory.toRatCDF f a =     if ProbabilityTheory.IsRatStieltjesPoi
nt f a then f a else …
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
-/
lemma toRatCDF_of_isRatStieltjesPoint {a : α} (h : IsRatStieltjesPoint f a) (q : ℚ) :
    toRatCDF f a q = f a q := by
  rw [toRatCDF, if_pos h]
/-
**ProbabilityTheory.toRatCDF_unit_prod** 是 Mathlib 中的一个引理，位于命名空间 `ProbabilityThe
ory`。
形式化陈述：toRatCDF_unit_prod (a : α) : toRatCDF (fun (p : Unit × α) => f p.2) ((), a
) = toRatCDF f a
参数：a : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `ProbabilityTheory.isRatStieltjesPoint_unit_prod_iff`：isRatStieltjesPoint
_unit_prod_iff (f : α -> Rat -> Real) (a : α) : IsRatStieltjesPoint (fun p : Uni
t × α => f p.2) ((), a) ↔ IsRatStieltjesP…
-/
lemma toRatCDF_unit_prod (a : α) :
    toRatCDF (fun (p : Unit × α) ↦ f p.2) ((), a) = toRatCDF f a := by
  unfold toRatCDF
  rw [isRatStieltjesPoint_unit_prod_iff]

variable [MeasurableSpace α]
/-
**ProbabilityTheory.measurable_toRatCDF** 是 Mathlib 中的一个引理，位于命名空间 `ProbabilityTh
eory`。
形式化陈述：measurable_toRatCDF (hf : Measurable f) : Measurable (toRatCDF f)
参数：hf : Measurable f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Measurable.ite`：Measurable.ite {p : α -> Prop} {_ : DecidablePred p} (hp
 : MeasurableSet { a : α | p a }) (hf : Measurable f) (hg : Measurable g) : Meas
urab…
· 使用引理 `ProbabilityTheory.measurableSet_isRatStieltjesPoint`：measurableSet_isRat
StieltjesPoint [MeasurableSpace α] (hf : Measurable f) : MeasurableSet {a | IsRa
tStieltjesPoint f a}
· 使用定理 `measurable_const`：measurable_const {_ : MeasurableSpace α} {_ : Measurab
leSpace β} {a : α} : Measurable fun _ : β => a
-/
lemma measurable_toRatCDF (hf : Measurable f) : Measurable (toRatCDF f) :=
  Measurable.ite (measurableSet_isRatStieltjesPoint hf) hf measurable_const
/-
**ProbabilityTheory.isMeasurableRatCDF_toRatCDF** 是 Mathlib 中的一个引理，位于命名空间 `Proba
bilityTheory`。
形式化陈述：isMeasurableRatCDF_toRatCDF (hf : Measurable f) : IsMeasurableRatCDF (toRa
tCDF f) where isRatStieltjesPoint a
参数：hf : Measurable f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ProbabilityTheory.IsRatStieltjesPoint.ite`：∀ {α : Type u_1} {f g : α → ℚ
 → ℝ} {a : α} (p : α → Prop) [inst : DecidablePred p],   (p a → ProbabilityTheor
y.IsRatStieltjesPoint f a) →   …
· 使用引理 `ProbabilityTheory.isRatStieltjesPoint_defaultRatCDF`：isRatStieltjesPoint
_defaultRatCDF (a : α) : IsRatStieltjesPoint (fun (_ : α) => defaultRatCDF) a wh
ere mono
· 使用引理 `ProbabilityTheory.measurable_toRatCDF`：measurable_toRatCDF (hf : Measura
ble f) : Measurable (toRatCDF f)
-/
lemma isMeasurableRatCDF_toRatCDF (hf : Measurable f) :
    IsMeasurableRatCDF (toRatCDF f) where
  isRatStieltjesPoint a := by
    classical
    exact IsRatStieltjesPoint.ite (IsRatStieltjesPoint f) id
      (fun _ ↦ isRatStieltjesPoint_defaultRatCDF a)
  measurable := measurable_toRatCDF hf

end ToRatCDF

section IsMeasurableRatCDF.stieltjesFunction

/-- Auxiliary definition for `IsMeasurableRatCDF.stieltjesFunction`: turn `f : α → ℚ → ℝ` into
a function `α → ℝ → ℝ` by assigning to `f a x` the infimum of `f a q` over `q : ℚ` with `x < q`. -/
noncomputable irreducible_def IsMeasurableRatCDF.stieltjesFunctionAux (f : α → ℚ → ℝ) :
    α → ℝ → ℝ :=
  fun a x ↦ ⨅ q : { q' : ℚ // x < q' }, f a q

/-
**ProbabilityTheory.IsMeasurableRatCDF.stieltjesFunctionAux_def'** 是 Mathlib 中的一
个定理，位于命名空间 `ProbabilityTheory.IsMeasurableRatCDF`。
形式化陈述：∀ {α : Type u_1} (f : α → ℚ → ℝ) (a : α),   ProbabilityTheory.IsMeasurable
RatCDF.stieltjesFunctionAux f a = fun t => ⨅ r, f a ↑r
参数：f : α → ℚ → ℝ；a : α。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `ProbabilityTheory.IsMeasurableRatCDF.stieltjesFunctionAux_def`：∀ {α : Ty
pe u_2} (f : α → ℚ → ℝ) (a : α) (x : ℝ),   ProbabilityTheory.IsMeasurableRatCDF.
stieltjesFunctionAux f a x = ⨅ q, f a ↑q
-/
lemma IsMeasurableRatCDF.stieltjesFunctionAux_def' (f : α → ℚ → ℝ) (a : α) :
    IsMeasurableRatCDF.stieltjesFunctionAux f a
      = fun (t : ℝ) ↦ ⨅ r : { r' : ℚ // t < r' }, f a r := by
  ext t; exact IsMeasurableRatCDF.stieltjesFunctionAux_def f a t
/-
**ProbabilityTheory.IsMeasurableRatCDF.stieltjesFunctionAux_unit_prod** 是 Mathli
b 中的一个定理，位于命名空间 `ProbabilityTheory.IsMeasurableRatCDF`。
形式化陈述：∀ {α : Type u_1} {f : α → ℚ → ℝ} (a : α),   ProbabilityTheory.IsMeasurable
RatCDF.stieltjesFunctionAux (fun p => f p.2) ((), a) =     ProbabilityTheory.IsM
easurableRatCDF.stieltjesFunctionAux f a
参数：a : α；fun p => f p.2；(), a。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ProbabilityTheory.IsMeasurableRatCDF.stieltjesFunctionAux_def'`：∀ {α : T
ype u_1} (f : α → ℚ → ℝ) (a : α),   ProbabilityTheory.IsMeasurableRatCDF.stieltj
esFunctionAux f a = fun t => ⨅ r, f a ↑r
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma IsMeasurableRatCDF.stieltjesFunctionAux_unit_prod {f : α → ℚ → ℝ} (a : α) :
    IsMeasurableRatCDF.stieltjesFunctionAux (fun (p : Unit × α) ↦ f p.2) ((), a)
      = IsMeasurableRatCDF.stieltjesFunctionAux f a := by
  simp_rw [IsMeasurableRatCDF.stieltjesFunctionAux_def']

variable {f : α → ℚ → ℝ} [MeasurableSpace α] (hf : IsMeasurableRatCDF f)
include hf

set_option backward.isDefEq.respectTransparency false in
/-
**ProbabilityTheory.IsMeasurableRatCDF.stieltjesFunctionAux_eq** 是 Mathlib 中的一个定
理，位于命名空间 `ProbabilityTheory.IsMeasurableRatCDF`。
形式化陈述：∀ {α : Type u_1} {f : α → ℚ → ℝ} [inst : MeasurableSpace α],   Probability
Theory.IsMeasurableRatCDF f →     ∀ (a : α) (r : ℚ), ProbabilityTheory.IsMeasura
bleRatCDF.stieltjesFunctionAux f a ↑r = f a r
参数：a : α；r : ℚ。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `ProbabilityTheory.IsMeasurableRatCDF.iInf_rat_gt_eq`：∀ {α : Type u_1} [i
nst : MeasurableSpace α] {f : α → ℚ → ℝ},   ProbabilityTheory.IsMeasurableRatCDF
 f → ∀ (a : α) (q : ℚ), ⨅ r, f a ↑r = f a…
· 使用定理 `ProbabilityTheory.IsMeasurableRatCDF.stieltjesFunctionAux_def`：∀ {α : Ty
pe u_2} (f : α → ℚ → ℝ) (a : α) (x : ℝ),   ProbabilityTheory.IsMeasurableRatCDF.
stieltjesFunctionAux f a x = ⨅ q, f a ↑q
· 使用定理 `Equiv.iInf_congr`：∀ {α : Type u_1} {ι : Sort u_4} {ι' : Sort u_5} [inst 
: InfSet α] {f : ι → α} {g : ι' → α} (e : ι ≃ ι'),   (∀ (x : ι), g (e x) = f x) 
→ ⨅ x,…
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Subtype.coe_eta`：coe_eta (a : { a // p a }) (h : p a) : mk (↑a) h = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma IsMeasurableRatCDF.stieltjesFunctionAux_eq (a : α) (r : ℚ) :
    IsMeasurableRatCDF.stieltjesFunctionAux f a r = f a r := by
  rw [← hf.iInf_rat_gt_eq a r, IsMeasurableRatCDF.stieltjesFunctionAux]
  refine Equiv.iInf_congr ?_ ?_
  · exact
      { toFun := fun t ↦ ⟨t.1, mod_cast t.2⟩
        invFun := fun t ↦ ⟨t.1, mod_cast t.2⟩
        left_inv := fun t ↦ by simp only [Subtype.coe_eta]
        right_inv := fun t ↦ by simp only [Subtype.coe_eta] }
  · intro t
    simp only [Equiv.coe_fn_mk, Subtype.coe_mk]
/-
**ProbabilityTheory.IsMeasurableRatCDF.stieltjesFunctionAux_nonneg** 是 Mathlib 中
的一个定理，位于命名空间 `ProbabilityTheory.IsMeasurableRatCDF`。
形式化陈述：∀ {α : Type u_1} {f : α → ℚ → ℝ} [inst : MeasurableSpace α],   Probability
Theory.IsMeasurableRatCDF f →     ∀ (a : α) (r : ℝ), 0 ≤ ProbabilityTheory.IsMea
surableRatCDF.stieltjesFunctionAux f a r
参数：a : α；r : ℝ。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `exists_rat_gt`：exists_rat_gt (x : K) : exists q : Rat, x < q
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ProbabilityTheory.IsMeasurableRatCDF.stieltjesFunctionAux_def`：∀ {α : Ty
pe u_2} (f : α → ℚ → ℝ) (a : α) (x : ℝ),   ProbabilityTheory.IsMeasurableRatCDF.
stieltjesFunctionAux f a x = ⨅ q, f a ↑q
· 使用定理 `le_ciInf`：le_ciInf [Nonempty ι] {f : ι -> α} {c : α} (H : forall x, c <=
 f x) : c <= iInf f
· 使用定理 `ProbabilityTheory.IsMeasurableRatCDF.nonneg`：∀ {α : Type u_1} [inst : Me
asurableSpace α] {f : α → ℚ → ℝ},   ProbabilityTheory.IsMeasurableRatCDF f → ∀ (
a : α) (q : ℚ), 0 ≤ f a q
-/
lemma IsMeasurableRatCDF.stieltjesFunctionAux_nonneg (a : α) (r : ℝ) :
    0 ≤ IsMeasurableRatCDF.stieltjesFunctionAux f a r := by
  have : Nonempty { r' : ℚ // r < ↑r' } := by
    obtain ⟨r, hrx⟩ := exists_rat_gt r
    exact ⟨⟨r, hrx⟩⟩
  rw [IsMeasurableRatCDF.stieltjesFunctionAux_def]
  exact le_ciInf fun r' ↦ hf.nonneg a _
/-
**ProbabilityTheory.IsMeasurableRatCDF.monotone_stieltjesFunctionAux** 是 Mathlib
 中的一个定理，位于命名空间 `ProbabilityTheory.IsMeasurableRatCDF`。
形式化陈述：∀ {α : Type u_1} {f : α → ℚ → ℝ} [inst : MeasurableSpace α],   Probability
Theory.IsMeasurableRatCDF f →     ∀ (a : α), Monotone (ProbabilityTheory.IsMeasu
rableRatCDF.stieltjesFunctionAux f a)
参数：a : α；ProbabilityTheory.IsMeasurableRatCDF.stieltjesFunctionAux f a。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `exists_rat_gt`：exists_rat_gt (x : K) : exists q : Rat, x < q
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ProbabilityTheory.IsMeasurableRatCDF.stieltjesFunctionAux_def`：∀ {α : Ty
pe u_2} (f : α → ℚ → ℝ) (a : α) (x : ℝ),   ProbabilityTheory.IsMeasurableRatCDF.
stieltjesFunctionAux f a x = ⨅ q, f a ↑q
· 使用定理 `le_ciInf`：le_ciInf [Nonempty ι] {f : ι -> α} {c : α} (H : forall x, c <=
 f x) : c <= iInf f
· 使用定理 `LE.le.trans_eq`：∀ {α : Type u_1} {a b c : α} [inst : LE α], a ≤ b → b = 
c → a ≤ c
· 使用定理 `LE.le.trans_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b 
→ b < c → a < c
· 使用定理 `Subtype.prop`：prop (x : Subtype p) : p x
· 使用定理 `ciInf_le`：ciInf_le {f : ι -> α} (H : BddBelow (range f)) (c : ι) : iInf 
f <= f c
· 使用定理 `ProbabilityTheory.IsMeasurableRatCDF.nonneg`：∀ {α : Type u_1} [inst : Me
asurableSpace α] {f : α → ℚ → ℝ},   ProbabilityTheory.IsMeasurableRatCDF f → ∀ (
a : α) (q : ℚ), 0 ≤ f a q
-/
lemma IsMeasurableRatCDF.monotone_stieltjesFunctionAux (a : α) :
    Monotone (IsMeasurableRatCDF.stieltjesFunctionAux f a) := by
  intro x y hxy
  have : Nonempty { r' : ℚ // y < ↑r' } := by
    obtain ⟨r, hrx⟩ := exists_rat_gt y
    exact ⟨⟨r, hrx⟩⟩
  simp_rw [IsMeasurableRatCDF.stieltjesFunctionAux_def]
  refine le_ciInf fun r ↦ (ciInf_le ?_ ?_).trans_eq ?_
  · refine ⟨0, fun z ↦ ?_⟩; rintro ⟨u, rfl⟩; exact hf.nonneg a _
  · exact ⟨r.1, hxy.trans_lt r.prop⟩
  · rfl
/-
**ProbabilityTheory.IsMeasurableRatCDF.continuousWithinAt_stieltjesFunctionAux_I
ci** 是 Mathlib 中的一个定理，位于命名空间 `ProbabilityTheory.IsMeasurableRatCDF`。
形式化陈述：∀ {α : Type u_1} {f : α → ℚ → ℝ} [inst : MeasurableSpace α],   Probability
Theory.IsMeasurableRatCDF f →     ∀ (a : α) (x : ℝ), ContinuousWithinAt (Probabi
lityTheory.IsMeasurableRatCDF.stieltjesFunctionAux f a) (Set.Ici x) x
参数：a : α；x : ℝ；ProbabilityTheory.IsMeasurableRatCDF.stieltjesFunctionAux f a；Set
.Ici x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `continuousWithinAt_Ioi_iff_Ici`：continuousWithinAt_Ioi_iff_Ici {a : α} {
f : α -> β} : ContinuousWithinAt f (Ioi a) a ↔ ContinuousWithinAt f (Ici a) a
· 使用定理 `sInf_image'`：∀ {α : Type u_1} {β : Type u_2} [inst : InfSet α] {s : Set 
β} {f : β → α}, sInf (f '' s) = ⨅ a, f ↑a
· 使用定理 `Real.iInf_Ioi_eq_iInf_rat_gt`：iInf_Ioi_eq_iInf_rat_gt {f : Real -> Real}
 (x : Real) (hf : BddBelow (f '' Ioi x)) (hf_mono : Monotone f) : ⨅ r : Ioi x, f
 r = ⨅ q : { q' : …
· 使用定理 `ProbabilityTheory.IsMeasurableRatCDF.stieltjesFunctionAux_nonneg`：∀ {α :
 Type u_1} {f : α → ℚ → ℝ} [inst : MeasurableSpace α],   ProbabilityTheory.IsMea
surableRatCDF f →     ∀ (a : α) (r : ℝ), 0 ≤ Probabili…
· 使用定理 `ProbabilityTheory.IsMeasurableRatCDF.monotone_stieltjesFunctionAux`：∀ {α
 : Type u_1} {f : α → ℚ → ℝ} [inst : MeasurableSpace α],   ProbabilityTheory.IsM
easurableRatCDF f →     ∀ (a : α), Monotone (Probability…
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `ProbabilityTheory.IsMeasurableRatCDF.stieltjesFunctionAux_eq`：∀ {α : Typ
e u_1} {f : α → ℚ → ℝ} [inst : MeasurableSpace α],   ProbabilityTheory.IsMeasura
bleRatCDF f →     ∀ (a : α) (r : ℚ), ProbabilityTh…
· 使用定理 `ContinuousWithinAt.eq_1`：∀ {X : Type u_1} {Y : Type u_2} [inst : Topolog
icalSpace X] [inst_1 : TopologicalSpace Y] (f : X → Y) (s : Set X)   (x : X), Co
ntinuousWithi…
· 使用定理 `iff_of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `ProbabilityTheory.IsMeasurableRatCDF.stieltjesFunctionAux_def`：∀ {α : Ty
pe u_2} (f : α → ℚ → ℝ) (a : α) (x : ℝ),   ProbabilityTheory.IsMeasurableRatCDF.
stieltjesFunctionAux f a x = ⨅ q, f a ↑q
· 使用定理 `Monotone.tendsto_nhdsGT`：Monotone.tendsto_nhdsGT {α β : Type*} [LinearOr
der α] [TopologicalSpace α] [OrderTopology α] [ConditionallyCompleteLinearOrder 
β] [Topologic…
· 使用定理 `instOrderTopologyReal`：OrderTopology ℝ
-/
lemma IsMeasurableRatCDF.continuousWithinAt_stieltjesFunctionAux_Ici (a : α) (x : ℝ) :
    ContinuousWithinAt (IsMeasurableRatCDF.stieltjesFunctionAux f a) (Ici x) x := by
  rw [← continuousWithinAt_Ioi_iff_Ici]
  convert! Monotone.tendsto_nhdsGT (monotone_stieltjesFunctionAux hf a) x
  rw [sInf_image']
  have h' : ⨅ r : Ioi x, stieltjesFunctionAux f a r
      = ⨅ r : { r' : ℚ // x < r' }, stieltjesFunctionAux f a r := by
    refine Real.iInf_Ioi_eq_iInf_rat_gt x ?_ (monotone_stieltjesFunctionAux hf a)
    refine ⟨0, fun z ↦ ?_⟩
    rintro ⟨u, -, rfl⟩
    exact stieltjesFunctionAux_nonneg hf a u
  have h'' :
    ⨅ r : { r' : ℚ // x < r' }, stieltjesFunctionAux f a r =
      ⨅ r : { r' : ℚ // x < r' }, f a r := by
    congr with r
    exact stieltjesFunctionAux_eq hf a r
  rw [h', h'', ContinuousWithinAt]
  congr!
  rw [stieltjesFunctionAux_def]

/-- Extend a function `f : α → ℚ → ℝ` with property `IsMeasurableRatCDF` from `ℚ` to `ℝ`,
to a function `α → StieltjesFunction ℝ`. -/
/-
**ProbabilityTheory.IsMeasurableRatCDF.stieltjesFunction** 是 Mathlib 中的一个定义，位于命名
空间 `ProbabilityTheory.IsMeasurableRatCDF`。
形式化陈述：{α : Type u_1} →   {f : α → ℚ → ℝ} → [inst : MeasurableSpace α] → Probabil
ityTheory.IsMeasurableRatCDF f → α → StieltjesFunction ℝ
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `ProbabilityTheory.IsMeasurableRatCDF.monotone_stieltjesFunctionAux`：∀ {α
 : Type u_1} {f : α → ℚ → ℝ} [inst : MeasurableSpace α],   ProbabilityTheory.IsM
easurableRatCDF f →     ∀ (a : α), Monotone (Probability…
· 使用定理 `ProbabilityTheory.IsMeasurableRatCDF.continuousWithinAt_stieltjesFunctio
nAux_Ici`：∀ {α : Type u_1} {f : α → ℚ → ℝ} [inst : MeasurableSpace α],   Probabi
lityTheory.IsMeasurableRatCDF f →     ∀ (a : α) (x : ℝ), ContinuousWit…

--- 原说明 ---
Extend a function `f : α → ℚ → ℝ` with property `IsMeasurableRatCDF` from `ℚ` to
 `ℝ`,
to a function `α → StieltjesFunction ℝ`.
-/
noncomputable def IsMeasurableRatCDF.stieltjesFunction (a : α) : StieltjesFunction ℝ where
  toFun := stieltjesFunctionAux f a
  mono' := monotone_stieltjesFunctionAux hf a
  right_continuous' x := continuousWithinAt_stieltjesFunctionAux_Ici hf a x
/-
**ProbabilityTheory.IsMeasurableRatCDF.stieltjesFunction_eq** 是 Mathlib 中的一个定理，位
于命名空间 `ProbabilityTheory.IsMeasurableRatCDF`。
形式化陈述：∀ {α : Type u_1} {f : α → ℚ → ℝ} [inst : MeasurableSpace α] (hf : Probabil
ityTheory.IsMeasurableRatCDF f) (a : α)   (r : ℚ), ↑(hf.stieltjesFunction a) ↑r 
= f a r
参数：hf : ProbabilityTheory.IsMeasurableRatCDF f；a : α；r : ℚ；hf.stieltjesFunction 
a。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ProbabilityTheory.IsMeasurableRatCDF.stieltjesFunctionAux_eq`：∀ {α : Typ
e u_1} {f : α → ℚ → ℝ} [inst : MeasurableSpace α],   ProbabilityTheory.IsMeasura
bleRatCDF f →     ∀ (a : α) (r : ℚ), ProbabilityTh…
-/
lemma IsMeasurableRatCDF.stieltjesFunction_eq (a : α) (r : ℚ) : hf.stieltjesFunction a r = f a r :=
  stieltjesFunctionAux_eq hf a r
/-
**ProbabilityTheory.IsMeasurableRatCDF.stieltjesFunction_nonneg** 是 Mathlib 中的一个
定理，位于命名空间 `ProbabilityTheory.IsMeasurableRatCDF`。
形式化陈述：∀ {α : Type u_1} {f : α → ℚ → ℝ} [inst : MeasurableSpace α] (hf : Probabil
ityTheory.IsMeasurableRatCDF f) (a : α)   (r : ℝ), 0 ≤ ↑(hf.stieltjesFunction a)
 r
参数：hf : ProbabilityTheory.IsMeasurableRatCDF f；a : α；r : ℝ；hf.stieltjesFunction 
a。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ProbabilityTheory.IsMeasurableRatCDF.stieltjesFunctionAux_nonneg`：∀ {α :
 Type u_1} {f : α → ℚ → ℝ} [inst : MeasurableSpace α],   ProbabilityTheory.IsMea
surableRatCDF f →     ∀ (a : α) (r : ℝ), 0 ≤ Probabili…
-/
lemma IsMeasurableRatCDF.stieltjesFunction_nonneg (a : α) (r : ℝ) : 0 ≤ hf.stieltjesFunction a r :=
  stieltjesFunctionAux_nonneg hf a r
/-
**ProbabilityTheory.IsMeasurableRatCDF.stieltjesFunction_le_one** 是 Mathlib 中的一个
定理，位于命名空间 `ProbabilityTheory.IsMeasurableRatCDF`。
形式化陈述：∀ {α : Type u_1} {f : α → ℚ → ℝ} [inst : MeasurableSpace α] (hf : Probabil
ityTheory.IsMeasurableRatCDF f) (a : α)   (x : ℝ), ↑(hf.stieltjesFunction a) x ≤
 1
参数：hf : ProbabilityTheory.IsMeasurableRatCDF f；a : α；x : ℝ；hf.stieltjesFunction 
a。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `exists_rat_gt`：exists_rat_gt (x : K) : exists q : Rat, x < q
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `StieltjesFunction.iInf_rat_gt_eq`：iInf_rat_gt_eq (f : StieltjesFunction 
Real) (x : Real) : ⨅ r : { r' : Rat // x < r' }, f r = f x
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `ProbabilityTheory.IsMeasurableRatCDF.stieltjesFunction_eq`：∀ {α : Type u
_1} {f : α → ℚ → ℝ} [inst : MeasurableSpace α] (hf : ProbabilityTheory.IsMeasura
bleRatCDF f) (a : α)   (r : ℚ), ↑(hf.stieltjesF…
· 使用定理 `ciInf_le_of_le`：ciInf_le_of_le {f : ι -> α} (H : BddBelow (range f)) (c 
: ι) (h : f c <= a) : iInf f <= a
· 使用定理 `ProbabilityTheory.IsMeasurableRatCDF.nonneg`：∀ {α : Type u_1} [inst : Me
asurableSpace α] {f : α → ℚ → ℝ},   ProbabilityTheory.IsMeasurableRatCDF f → ∀ (
a : α) (q : ℚ), 0 ≤ f a q
· 使用定理 `ProbabilityTheory.IsMeasurableRatCDF.le_one`：∀ {α : Type u_1} [inst : Me
asurableSpace α] {f : α → ℚ → ℝ},   ProbabilityTheory.IsMeasurableRatCDF f → ∀ (
a : α) (q : ℚ), f a q ≤ 1
-/
lemma IsMeasurableRatCDF.stieltjesFunction_le_one (a : α) (x : ℝ) :
    hf.stieltjesFunction a x ≤ 1 := by
  obtain ⟨r, hrx⟩ := exists_rat_gt x
  rw [← StieltjesFunction.iInf_rat_gt_eq]
  simp_rw [IsMeasurableRatCDF.stieltjesFunction_eq]
  refine ciInf_le_of_le ?_ ?_ (hf.le_one _ _)
  · refine ⟨0, fun z ↦ ?_⟩; rintro ⟨u, rfl⟩; exact hf.nonneg a _
  · exact ⟨r, hrx⟩
/-
**ProbabilityTheory.IsMeasurableRatCDF.tendsto_stieltjesFunction_atBot** 是 Mathl
ib 中的一个定理，位于命名空间 `ProbabilityTheory.IsMeasurableRatCDF`。
形式化陈述：∀ {α : Type u_1} {f : α → ℚ → ℝ} [inst : MeasurableSpace α] (hf : Probabil
ityTheory.IsMeasurableRatCDF f) (a : α),   Filter.Tendsto (↑(hf.stieltjesFunctio
n a)) Filter.atBot (nhds 0)
参数：hf : ProbabilityTheory.IsMeasurableRatCDF f；a : α；↑(hf.stieltjesFunction a)；n
hds 0。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `exists_rat_btwn`：exists_rat_btwn {x y : K} (h : x < y) : exists q : Rat,
 x < q ∧ q < y
· 使用引理 `lt_add_one`：lt_add_one [One α] [AddZeroClass α] [PartialOrder α] [ZeroLE
OneClass α] [NeZero (1 : α)] [AddLeftStrictMono α] (a : α) : a < a + 1
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `IsLeftCancelAdd.addLeftStrictMono_of_addLeftMono`：∀ (N : Type u_2) [inst
 : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftMono N], AddLeft
StrictMono N
· 使用定理 `instIsLeftCancelAddOfAddLeftReflectLE`：∀ {α : Type u_1} [inst : Add α] [
inst_1 : PartialOrder α] [AddLeftReflectLE α], IsLeftCancelAdd α
· 使用定理 `AddGroup.addLeftReflectLE_of_addLeftMono`：∀ {N : Type u_2} [inst : AddGr
oup N] [inst_1 : LE N] [AddLeftMono N], AddLeftReflectLE N
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Filter.tendsto_atBot_atBot`：∀ {α : Type u_3} {β : Type u_4} [Nonempty α]
 [inst : Preorder α] [IsCodirectedOrder α] {f : α → β}   [inst_2 : Preorder β], 
Filter.Tendsto f…
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `instIsCodirectedOrder`：∀ {R : Type u_3} [inst : Ring R] [inst_1 : Partia
lOrder R] [IsOrderedRing R] [Archimedean R], IsCodirectedOrder R
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Exists.choose_spec`：∀ {α : Sort u_1} {p : α → Prop} (P : ∃ a, p a), p P.
choose
· 使用定理 `add_le_add`：∀ {α : Type u_1} [inst : Add α] [inst_1 : Preorder α] [AddLe
ftMono α] [AddRightMono α] {a b c d : α},   a ≤ b → c ≤ d → a + c ≤ b + d
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用引理 `le_rfl`：le_rfl : a <= a
· 使用定理 `sub_add_cancel`：∀ {G : Type u_1} [inst : AddGroup G] (a b : G), a - b + 
b = a
· 使用定理 `tendsto_of_tendsto_of_tendsto_of_le_of_le`：tendsto_of_tendsto_of_tendsto
_of_le_of_le [OrderTopology α] {f g h : β -> α} {b : Filter β} {a : α} (hg : Ten
dsto g b (𝓝 a)) (hh : Tendsto h…
· 使用定理 `instOrderTopologyReal`：OrderTopology ℝ
· 使用定理 `tendsto_const_nhds`：tendsto_const_nhds {f : Filter α} : Tendsto (fun _ :
 α => x) f (𝓝 x)
· 使用定理 `Filter.Tendsto.comp`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {f :
 α → β} {g : β → γ} {x : Filter α} {y : Filter β} {z : Filter γ},   Filter.Tends
to g y z …
· 使用定理 `ProbabilityTheory.IsMeasurableRatCDF.tendsto_atBot_zero`：∀ {α : Type u_1
} [inst : MeasurableSpace α] {f : α → ℚ → ℝ},   ProbabilityTheory.IsMeasurableRa
tCDF f → ∀ (a : α), Filter.Tendsto (f a) Filt…
· 使用定理 `ProbabilityTheory.IsMeasurableRatCDF.stieltjesFunction_nonneg`：∀ {α : Ty
pe u_1} {f : α → ℚ → ℝ} [inst : MeasurableSpace α] (hf : ProbabilityTheory.IsMea
surableRatCDF f) (a : α)   (r : ℝ), 0 ≤ ↑(hf.stielt…
· 使用定理 `Function.comp_apply`：∀ {β : Sort u_1} {δ : Sort u_2} {α : Sort u_3} {f :
 β → δ} {g : α → β} {x : α}, (f ∘ g) x = f (g x)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `ProbabilityTheory.IsMeasurableRatCDF.stieltjesFunction_eq`：∀ {α : Type u
_1} {f : α → ℚ → ℝ} [inst : MeasurableSpace α] (hf : ProbabilityTheory.IsMeasura
bleRatCDF f) (a : α)   (r : ℚ), ↑(hf.stieltjesF…
· 使用定理 `StieltjesFunction.mono`：mono : Monotone f
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
-/
lemma IsMeasurableRatCDF.tendsto_stieltjesFunction_atBot (a : α) :
    Tendsto (hf.stieltjesFunction a) atBot (𝓝 0) := by
  have h_exists : ∀ x : ℝ, ∃ q : ℚ, x < q ∧ ↑q < x + 1 := fun x ↦ exists_rat_btwn (lt_add_one x)
  let qs : ℝ → ℚ := fun x ↦ (h_exists x).choose
  have hqs_tendsto : Tendsto qs atBot atBot := by
    rw [tendsto_atBot_atBot]
    refine fun q ↦ ⟨q - 1, fun y hy ↦ ?_⟩
    have h_le : ↑(qs y) ≤ (q : ℝ) - 1 + 1 :=
      (h_exists y).choose_spec.2.le.trans (add_le_add hy le_rfl)
    rw [sub_add_cancel] at h_le
    exact mod_cast h_le
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
    ((hf.tendsto_atBot_zero a).comp hqs_tendsto) (stieltjesFunction_nonneg hf a) fun x ↦ ?_
  rw [Function.comp_apply, ← stieltjesFunction_eq hf]
  exact (hf.stieltjesFunction a).mono (h_exists x).choose_spec.1.le
/-
**ProbabilityTheory.IsMeasurableRatCDF.tendsto_stieltjesFunction_atTop** 是 Mathl
ib 中的一个定理，位于命名空间 `ProbabilityTheory.IsMeasurableRatCDF`。
形式化陈述：∀ {α : Type u_1} {f : α → ℚ → ℝ} [inst : MeasurableSpace α] (hf : Probabil
ityTheory.IsMeasurableRatCDF f) (a : α),   Filter.Tendsto (↑(hf.stieltjesFunctio
n a)) Filter.atTop (nhds 1)
参数：hf : ProbabilityTheory.IsMeasurableRatCDF f；a : α；↑(hf.stieltjesFunction a)；n
hds 1。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `exists_rat_btwn`：exists_rat_btwn {x y : K} (h : x < y) : exists q : Rat,
 x < q ∧ q < y
· 使用引理 `sub_one_lt`：sub_one_lt [ZeroLEOneClass R] [NeZero (1 : R)] [AddLeftStric
tMono R] (a : R) : a - 1 < a
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `IsLeftCancelAdd.addLeftStrictMono_of_addLeftMono`：∀ (N : Type u_2) [inst
 : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftMono N], AddLeft
StrictMono N
· 使用定理 `instIsLeftCancelAddOfAddLeftReflectLE`：∀ {α : Type u_1} [inst : Add α] [
inst_1 : PartialOrder α] [AddLeftReflectLE α], IsLeftCancelAdd α
· 使用定理 `AddGroup.addLeftReflectLE_of_addLeftMono`：∀ {N : Type u_2} [inst : AddGr
oup N] [inst_1 : LE N] [AddLeftMono N], AddLeftReflectLE N
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Filter.tendsto_atTop_atTop`：tendsto_atTop_atTop : Tendsto f atTop atTop 
↔ forall b : β, exists i : α, forall a : α, i <= a -> b <= f a
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `instIsDirectedOrder`：∀ {R : Type u_3} [inst : Semiring R] [inst_1 : Part
ialOrder R] [IsOrderedRing R] [Archimedean R], IsDirectedOrder R
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Exists.choose_spec`：∀ {α : Sort u_1} {p : α → Prop} (P : ∃ a, p a), p P.
choose
· 使用定理 `le_of_add_le_add_right`：∀ {α : Type u_1} [inst : Add α] [inst_1 : LE α] 
[AddRightReflectLE α] {a b c : α}, b + a ≤ c + a → b ≤ c
· 使用定理 `IsRightCancelAdd.addRightReflectLE_of_addRightReflectLT`：∀ (N : Type u_2
) [inst : Add N] [IsRightCancelAdd N] [inst_2 : PartialOrder N] [AddRightReflect
LT N],   AddRightReflectLE N
· 使用定理 `instIsRightCancelAddOfAddRightReflectLE`：∀ {α : Type u_1} [inst : Add α]
 [inst_1 : PartialOrder α] [AddRightReflectLE α], IsRightCancelAdd α
· 使用定理 `addRightReflectLE_of_addLeftReflectLE`：∀ (N : Type u_2) [inst : AddCommS
emigroup N] [inst_1 : LE N] [AddLeftReflectLE N], AddRightReflectLE N
· 使用定理 `IsLeftCancelAdd.addLeftReflectLE_of_addLeftReflectLT`：∀ (N : Type u_2) [
inst : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftReflectLT N]
, AddLeftReflectLE N
· 使用定理 `AddLeftCancelSemigroup.toIsLeftCancelAdd`：∀ {G : Type u} [self : AddLeft
CancelSemigroup G], IsLeftCancelAdd G
· 使用定理 `contravariant_swap_add_of_contravariant_add`：∀ (N : Type u_2) (r : N → N
 → Prop) [inst : AddCommSemigroup N] [ContravariantClass N N (fun x1 x2 => x1 + 
x2) r],   ContravariantClass N N …
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `sub_le_iff_le_add`：∀ {α : Type u} [inst : AddGroup α] [inst_1 : LE α] [A
ddRightMono α] {a b c : α}, a - c ≤ b ↔ a ≤ b + c
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `tendsto_of_tendsto_of_tendsto_of_le_of_le`：tendsto_of_tendsto_of_tendsto
_of_le_of_le [OrderTopology α] {f g h : β -> α} {b : Filter β} {a : α} (hg : Ten
dsto g b (𝓝 a)) (hh : Tendsto h…
· 使用定理 `instOrderTopologyReal`：OrderTopology ℝ
· 使用定理 `Filter.Tendsto.comp`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {f :
 α → β} {g : β → γ} {x : Filter α} {y : Filter β} {z : Filter γ},   Filter.Tends
to g y z …
· 使用定理 `ProbabilityTheory.IsMeasurableRatCDF.tendsto_atTop_one`：∀ {α : Type u_1}
 [inst : MeasurableSpace α] {f : α → ℚ → ℝ},   ProbabilityTheory.IsMeasurableRat
CDF f → ∀ (a : α), Filter.Tendsto (f a) Filt…
· 使用定理 `tendsto_const_nhds`：tendsto_const_nhds {f : Filter α} : Tendsto (fun _ :
 α => x) f (𝓝 x)
· 使用定理 `Function.comp_apply`：∀ {β : Sort u_1} {δ : Sort u_2} {α : Sort u_3} {f :
 β → δ} {g : α → β} {x : α}, (f ∘ g) x = f (g x)
（共 36 条，此处仅展示前 30 条）
-/
lemma IsMeasurableRatCDF.tendsto_stieltjesFunction_atTop (a : α) :
    Tendsto (hf.stieltjesFunction a) atTop (𝓝 1) := by
  have h_exists : ∀ x : ℝ, ∃ q : ℚ, x - 1 < q ∧ ↑q < x := fun x ↦ exists_rat_btwn (sub_one_lt x)
  let qs : ℝ → ℚ := fun x ↦ (h_exists x).choose
  have hqs_tendsto : Tendsto qs atTop atTop := by
    rw [tendsto_atTop_atTop]
    refine fun q ↦ ⟨q + 1, fun y hy ↦ ?_⟩
    have h_le : y - 1 ≤ qs y := (h_exists y).choose_spec.1.le
    rw [sub_le_iff_le_add] at h_le
    exact_mod_cast le_of_add_le_add_right (hy.trans h_le)
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le ((hf.tendsto_atTop_one a).comp hqs_tendsto)
      tendsto_const_nhds ?_ (stieltjesFunction_le_one hf a)
  intro x
  rw [Function.comp_apply, ← stieltjesFunction_eq hf]
  exact (hf.stieltjesFunction a).mono (le_of_lt (h_exists x).choose_spec.2)
/-
**ProbabilityTheory.IsMeasurableRatCDF.measurable_stieltjesFunction** 是 Mathlib 
中的一个定理，位于命名空间 `ProbabilityTheory.IsMeasurableRatCDF`。
形式化陈述：∀ {α : Type u_1} {f : α → ℚ → ℝ} [inst : MeasurableSpace α] (hf : Probabil
ityTheory.IsMeasurableRatCDF f) (x : ℝ),   Measurable fun a => ↑(hf.stieltjesFun
ction a) x
参数：hf : ProbabilityTheory.IsMeasurableRatCDF f；x : ℝ；hf.stieltjesFunction a。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `StieltjesFunction.iInf_rat_gt_eq`：iInf_rat_gt_eq (f : StieltjesFunction 
Real) (x : Real) : ⨅ r : { r' : Rat // x < r' }, f r = f x
· 使用定理 `ProbabilityTheory.IsMeasurableRatCDF.stieltjesFunction_eq`：∀ {α : Type u
_1} {f : α → ℚ → ℝ} [inst : MeasurableSpace α] (hf : ProbabilityTheory.IsMeasura
bleRatCDF f) (a : α)   (r : ℚ), ↑(hf.stieltjesF…
· 使用定理 `Measurable.iInf`：∀ {α : Type u_1} {δ : Type u_4} [inst : TopologicalSpac
e α] {mα : MeasurableSpace α} [BorelSpace α]   {mδ : MeasurableSpace δ} [inst_2 
: Con…
· 使用定理 `instOrderTopologyReal`：OrderTopology ℝ
· 使用定理 `instSecondCountableTopologyReal`：SecondCountableTopology ℝ
· 使用定理 `Subtype.countable`：∀ {α : Sort u} [Countable α] {p : α → Prop}, Countabl
e { x // p x }
· 使用定理 `Encodable.countable`：∀ {α : Type u_1} [Encodable α], Countable α
· 使用定理 `Measurable.eval`：Measurable.eval {a : δ} {g : α -> forall a, X a} (hg : 
Measurable g) : Measurable fun x => g x a
· 使用定理 `ProbabilityTheory.IsMeasurableRatCDF.measurable`：∀ {α : Type u_1} [inst 
: MeasurableSpace α] {f : α → ℚ → ℝ}, ProbabilityTheory.IsMeasurableRatCDF f → M
easurable f
-/
lemma IsMeasurableRatCDF.measurable_stieltjesFunction (x : ℝ) :
    Measurable fun a ↦ hf.stieltjesFunction a x := by
  have : (fun a ↦ hf.stieltjesFunction a x) = fun a ↦ ⨅ r : { r' : ℚ // x < r' }, f a ↑r := by
    ext1 a
    rw [← StieltjesFunction.iInf_rat_gt_eq]
    congr with q
    rw [stieltjesFunction_eq]
  rw [this]
  exact .iInf (fun q ↦ hf.measurable.eval)
/-
**ProbabilityTheory.IsMeasurableRatCDF.stronglyMeasurable_stieltjesFunction** 是 
Mathlib 中的一个定理，位于命名空间 `ProbabilityTheory.IsMeasurableRatCDF`。
形式化陈述：∀ {α : Type u_1} {f : α → ℚ → ℝ} [inst : MeasurableSpace α] (hf : Probabil
ityTheory.IsMeasurableRatCDF f) (x : ℝ),   MeasureTheory.StronglyMeasurable fun 
a => ↑(hf.stieltjesFunction a) x
参数：hf : ProbabilityTheory.IsMeasurableRatCDF f；x : ℝ；hf.stieltjesFunction a。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Measurable.stronglyMeasurable`：∀ {α : Type u_1} {β : Type u_2} {f : α → 
β} {mα : MeasurableSpace α} [inst : MeasurableSpace β]   [inst_1 : TopologicalSp
ace β] [Topological…
· 使用定理 `PseudoEMetricSpace.pseudoMetrizableSpace`：∀ {α : Type u_2} [inst : Pseud
oEMetricSpace α], TopologicalSpace.PseudoMetrizableSpace α
· 使用定理 `instSecondCountableTopologyReal`：SecondCountableTopology ℝ
· 使用定理 `BorelSpace.opensMeasurable`：∀ {α : Type u_6} [inst : TopologicalSpace α]
 [inst_1 : MeasurableSpace α] [BorelSpace α], OpensMeasurableSpace α
· 使用定理 `ProbabilityTheory.IsMeasurableRatCDF.measurable_stieltjesFunction`：∀ {α 
: Type u_1} {f : α → ℚ → ℝ} [inst : MeasurableSpace α] (hf : ProbabilityTheory.I
sMeasurableRatCDF f) (x : ℝ),   Measurable fun a => ↑(h…
-/
lemma IsMeasurableRatCDF.stronglyMeasurable_stieltjesFunction (x : ℝ) :
    StronglyMeasurable fun a ↦ hf.stieltjesFunction a x :=
  (measurable_stieltjesFunction hf x).stronglyMeasurable

section Measure

/-
**ProbabilityTheory.IsMeasurableRatCDF.measure_stieltjesFunction_Iic** 是 Mathlib
 中的一个定理，位于命名空间 `ProbabilityTheory.IsMeasurableRatCDF`。
形式化陈述：∀ {α : Type u_1} {f : α → ℚ → ℝ} [inst : MeasurableSpace α] (hf : Probabil
ityTheory.IsMeasurableRatCDF f) (a : α)   (x : ℝ), (hf.stieltjesFunction a).meas
ure (Set.Iic x) = ENNReal.ofReal (↑(hf.stieltjesFunction a) x)
参数：hf : ProbabilityTheory.IsMeasurableRatCDF f；a : α；x : ℝ；hf.stieltjesFunction 
a；Set.Iic x；↑(hf.stieltjesFunction a) x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instOrderTopologyReal`：OrderTopology ℝ
· 使用定理 `ConditionallyCompleteLinearOrder.toCompactIccSpace`：∀ (α : Type u_2) [in
st : ConditionallyCompleteLinearOrder α] [inst_1 : TopologicalSpace α] [OrderTop
ology α],   CompactIccSpace α
· 使用定理 `instSecondCountableTopologyReal`：SecondCountableTopology ℝ
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
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `sub_zero`：∀ {G : Type u_3} [inst : SubNegZeroMonoid G] (a : G), a - 0 = 
a
· 使用定理 `StieltjesFunction.measure_Iic`：measure_Iic {l : Real} (hf : Tendsto f at
Bot (𝓝 l)) (x : R) : f.measure (Iic x) = ofReal (f x - l)
· 使用定理 `ProbabilityTheory.IsMeasurableRatCDF.tendsto_stieltjesFunction_atBot`：∀ 
{α : Type u_1} {f : α → ℚ → ℝ} [inst : MeasurableSpace α] (hf : ProbabilityTheor
y.IsMeasurableRatCDF f) (a : α),   Filter.Tendsto (↑(hf.st…
-/
lemma IsMeasurableRatCDF.measure_stieltjesFunction_Iic (a : α) (x : ℝ) :
    (hf.stieltjesFunction a).measure (Iic x) = ENNReal.ofReal (hf.stieltjesFunction a x) := by
  rw [← sub_zero (hf.stieltjesFunction a x)]
  exact (hf.stieltjesFunction a).measure_Iic (tendsto_stieltjesFunction_atBot hf a) _
/-
**ProbabilityTheory.IsMeasurableRatCDF.measure_stieltjesFunction_univ** 是 Mathli
b 中的一个定理，位于命名空间 `ProbabilityTheory.IsMeasurableRatCDF`。
形式化陈述：∀ {α : Type u_1} {f : α → ℚ → ℝ} [inst : MeasurableSpace α] (hf : Probabil
ityTheory.IsMeasurableRatCDF f) (a : α),   (hf.stieltjesFunction a).measure Set.
univ = 1
参数：hf : ProbabilityTheory.IsMeasurableRatCDF f；a : α；hf.stieltjesFunction a。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instOrderTopologyReal`：OrderTopology ℝ
· 使用定理 `ConditionallyCompleteLinearOrder.toCompactIccSpace`：∀ (α : Type u_2) [in
st : ConditionallyCompleteLinearOrder α] [inst_1 : TopologicalSpace α] [OrderTop
ology α],   CompactIccSpace α
· 使用定理 `instSecondCountableTopologyReal`：SecondCountableTopology ℝ
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
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `ENNReal.ofReal_one`：ENNReal.ofReal 1 = 1
· 使用定理 `sub_zero`：∀ {G : Type u_3} [inst : SubNegZeroMonoid G] (a : G), a - 0 = 
a
· 使用定理 `StieltjesFunction.measure_univ`：measure_univ [Nonempty R] {l u : Real} (
hfl : Tendsto f atBot (𝓝 l)) (hfu : Tendsto f atTop (𝓝 u)) : f.measure univ = of
Real (u - l)
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `ProbabilityTheory.IsMeasurableRatCDF.tendsto_stieltjesFunction_atBot`：∀ 
{α : Type u_1} {f : α → ℚ → ℝ} [inst : MeasurableSpace α] (hf : ProbabilityTheor
y.IsMeasurableRatCDF f) (a : α),   Filter.Tendsto (↑(hf.st…
· 使用定理 `ProbabilityTheory.IsMeasurableRatCDF.tendsto_stieltjesFunction_atTop`：∀ 
{α : Type u_1} {f : α → ℚ → ℝ} [inst : MeasurableSpace α] (hf : ProbabilityTheor
y.IsMeasurableRatCDF f) (a : α),   Filter.Tendsto (↑(hf.st…
-/
lemma IsMeasurableRatCDF.measure_stieltjesFunction_univ (a : α) :
    (hf.stieltjesFunction a).measure univ = 1 := by
  rw [← ENNReal.ofReal_one, ← sub_zero (1 : ℝ)]
  exact StieltjesFunction.measure_univ _ (tendsto_stieltjesFunction_atBot hf a)
    (tendsto_stieltjesFunction_atTop hf a)
/-
**ProbabilityTheory.IsMeasurableRatCDF.instIsProbabilityMeasure_stieltjesFunctio
n** 是 Mathlib 中的一个定理，位于命名空间 `ProbabilityTheory.IsMeasurableRatCDF`。
形式化陈述：∀ {α : Type u_1} {f : α → ℚ → ℝ} [inst : MeasurableSpace α] (hf : Probabil
ityTheory.IsMeasurableRatCDF f) (a : α),   MeasureTheory.IsProbabilityMeasure (h
f.stieltjesFunction a).measure
参数：hf : ProbabilityTheory.IsMeasurableRatCDF f；a : α；hf.stieltjesFunction a。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instOrderTopologyReal`：OrderTopology ℝ
· 使用定理 `ConditionallyCompleteLinearOrder.toCompactIccSpace`：∀ (α : Type u_2) [in
st : ConditionallyCompleteLinearOrder α] [inst_1 : TopologicalSpace α] [OrderTop
ology α],   CompactIccSpace α
· 使用定理 `instSecondCountableTopologyReal`：SecondCountableTopology ℝ
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
· 使用定理 `ProbabilityTheory.IsMeasurableRatCDF.measure_stieltjesFunction_univ`：∀ {
α : Type u_1} {f : α → ℚ → ℝ} [inst : MeasurableSpace α] (hf : ProbabilityTheory
.IsMeasurableRatCDF f) (a : α),   (hf.stieltjesFunction a…
-/
instance IsMeasurableRatCDF.instIsProbabilityMeasure_stieltjesFunction (a : α) :
    IsProbabilityMeasure (hf.stieltjesFunction a).measure :=
  ⟨measure_stieltjesFunction_univ hf a⟩
/-
**ProbabilityTheory.IsMeasurableRatCDF.measurable_measure_stieltjesFunction** 是 
Mathlib 中的一个定理，位于命名空间 `ProbabilityTheory.IsMeasurableRatCDF`。
形式化陈述：∀ {α : Type u_1} {f : α → ℚ → ℝ} [inst : MeasurableSpace α] (hf : Probabil
ityTheory.IsMeasurableRatCDF f),   Measurable fun a => (hf.stieltjesFunction a).
measure
参数：hf : ProbabilityTheory.IsMeasurableRatCDF f；hf.stieltjesFunction a。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `StieltjesFunction.measurable_measure`：StieltjesFunction.measurable_measu
re {α : Type*} {_ : MeasurableSpace α} {f : α -> StieltjesFunction Real} (hf : f
orall q, Measurable fun a …
· 使用定理 `ProbabilityTheory.IsMeasurableRatCDF.measurable_stieltjesFunction`：∀ {α 
: Type u_1} {f : α → ℚ → ℝ} [inst : MeasurableSpace α] (hf : ProbabilityTheory.I
sMeasurableRatCDF f) (x : ℝ),   Measurable fun a => ↑(h…
· 使用定理 `ProbabilityTheory.IsMeasurableRatCDF.tendsto_stieltjesFunction_atBot`：∀ 
{α : Type u_1} {f : α → ℚ → ℝ} [inst : MeasurableSpace α] (hf : ProbabilityTheor
y.IsMeasurableRatCDF f) (a : α),   Filter.Tendsto (↑(hf.st…
· 使用定理 `ProbabilityTheory.IsMeasurableRatCDF.tendsto_stieltjesFunction_atTop`：∀ 
{α : Type u_1} {f : α → ℚ → ℝ} [inst : MeasurableSpace α] (hf : ProbabilityTheor
y.IsMeasurableRatCDF f) (a : α),   Filter.Tendsto (↑(hf.st…
-/
lemma IsMeasurableRatCDF.measurable_measure_stieltjesFunction :
    Measurable fun a ↦ (hf.stieltjesFunction a).measure := by
  apply_rules [StieltjesFunction.measurable_measure, measurable_stieltjesFunction,
    tendsto_stieltjesFunction_atBot, tendsto_stieltjesFunction_atTop]

end Measure

end IsMeasurableRatCDF.stieltjesFunction

section stieltjesOfMeasurableRat

variable {f : α → ℚ → ℝ} [MeasurableSpace α]

/-- Turn a measurable function `f : α → ℚ → ℝ` into a measurable function `α → StieltjesFunction ℝ`.
Composition of `toRatCDF` and `IsMeasurableRatCDF.stieltjesFunction`. -/
noncomputable
/-
**ProbabilityTheory.stieltjesOfMeasurableRat** 是 Mathlib 中的一个定义，位于命名空间 `Probabil
ityTheory`。
形式化陈述：stieltjesOfMeasurableRat (f : α -> Rat -> Real) (hf : Measurable f) : α ->
 StieltjesFunction Real
参数：f : α -> Rat -> Real；hf : Measurable f。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用引理 `ProbabilityTheory.isMeasurableRatCDF_toRatCDF`：isMeasurableRatCDF_toRatC
DF (hf : Measurable f) : IsMeasurableRatCDF (toRatCDF f) where isRatStieltjesPoi
nt a
-/
def stieltjesOfMeasurableRat (f : α → ℚ → ℝ) (hf : Measurable f) : α → StieltjesFunction ℝ :=
  (isMeasurableRatCDF_toRatCDF hf).stieltjesFunction
/-
**ProbabilityTheory.stieltjesOfMeasurableRat_eq** 是 Mathlib 中的一个引理，位于命名空间 `Proba
bilityTheory`。
形式化陈述：stieltjesOfMeasurableRat_eq (hf : Measurable f) (a : α) (r : Rat) : stielt
jesOfMeasurableRat f hf a r = toRatCDF f a r
参数：hf : Measurable f；a : α；r : Rat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ProbabilityTheory.IsMeasurableRatCDF.stieltjesFunction_eq`：∀ {α : Type u
_1} {f : α → ℚ → ℝ} [inst : MeasurableSpace α] (hf : ProbabilityTheory.IsMeasura
bleRatCDF f) (a : α)   (r : ℚ), ↑(hf.stieltjesF…
· 使用引理 `ProbabilityTheory.isMeasurableRatCDF_toRatCDF`：isMeasurableRatCDF_toRatC
DF (hf : Measurable f) : IsMeasurableRatCDF (toRatCDF f) where isRatStieltjesPoi
nt a
-/
lemma stieltjesOfMeasurableRat_eq (hf : Measurable f) (a : α) (r : ℚ) :
    stieltjesOfMeasurableRat f hf a r = toRatCDF f a r :=
  IsMeasurableRatCDF.stieltjesFunction_eq _ a r
/-
**ProbabilityTheory.stieltjesOfMeasurableRat_unit_prod** 是 Mathlib 中的一个引理，位于命名空间
 `ProbabilityTheory`。
形式化陈述：stieltjesOfMeasurableRat_unit_prod (hf : Measurable f) (a : α) : stieltjes
OfMeasurableRat (fun (p : Unit × α) => f p.2) (hf.comp measurable_snd) ((), a) =
 stieltjesOfMeasurableRat f hf a
参数：hf : Measurable f；a : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Measurable.comp`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {x : Mea
surableSpace α} {x_1 : MeasurableSpace β}   {x_2 : MeasurableSpace γ} {g : β → γ
} {f …
· 使用定理 `measurable_snd`：measurable_snd {_ : MeasurableSpace α} {_ : MeasurableSp
ace β} : Measurable (Prod.snd : α × β -> β)
· 使用引理 `ProbabilityTheory.isMeasurableRatCDF_toRatCDF`：isMeasurableRatCDF_toRatC
DF (hf : Measurable f) : IsMeasurableRatCDF (toRatCDF f) where isRatStieltjesPoi
nt a
· 使用定理 `ProbabilityTheory.IsMeasurableRatCDF.monotone_stieltjesFunctionAux`：∀ {α
 : Type u_1} {f : α → ℚ → ℝ} [inst : MeasurableSpace α],   ProbabilityTheory.IsM
easurableRatCDF f →     ∀ (a : α), Monotone (Probability…
· 使用定理 `ProbabilityTheory.IsMeasurableRatCDF.continuousWithinAt_stieltjesFunctio
nAux_Ici`：∀ {α : Type u_1} {f : α → ℚ → ℝ} [inst : MeasurableSpace α],   Probabi
lityTheory.IsMeasurableRatCDF f →     ∀ (a : α) (x : ℝ), ContinuousWit…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `ProbabilityTheory.IsMeasurableRatCDF.stieltjesFunctionAux_unit_prod`：∀ {
α : Type u_1} {f : α → ℚ → ℝ} (a : α),   ProbabilityTheory.IsMeasurableRatCDF.st
ieltjesFunctionAux (fun p => f p.2) ((), a) =     Probabi…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `StieltjesFunction.mk.congr_simp`：∀ {R : Type u_1} [inst : LinearOrder R]
 [inst_1 : TopologicalSpace R] (toFun toFun_1 : R → ℝ)   (e_toFun : toFun = toFu
n_1) (mono' : Monoton…
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用引理 `ProbabilityTheory.toRatCDF_unit_prod`：toRatCDF_unit_prod (a : α) : toRat
CDF (fun (p : Unit × α) => f p.2) ((), a) = toRatCDF f a
-/
lemma stieltjesOfMeasurableRat_unit_prod (hf : Measurable f) (a : α) :
    stieltjesOfMeasurableRat (fun (p : Unit × α) ↦ f p.2) (hf.comp measurable_snd) ((), a)
      = stieltjesOfMeasurableRat f hf a := by
  simp_rw [stieltjesOfMeasurableRat, IsMeasurableRatCDF.stieltjesFunction,
    ← IsMeasurableRatCDF.stieltjesFunctionAux_unit_prod a]
  congr 1 with x
  congr 1 with p : 1
  cases p with
  | mk _ b => rw [← toRatCDF_unit_prod b]
/-
**ProbabilityTheory.stieltjesOfMeasurableRat_nonneg** 是 Mathlib 中的一个引理，位于命名空间 `P
robabilityTheory`。
形式化陈述：stieltjesOfMeasurableRat_nonneg (hf : Measurable f) (a : α) (r : Real) : 0
 <= stieltjesOfMeasurableRat f hf a r
参数：hf : Measurable f；a : α；r : Real。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ProbabilityTheory.IsMeasurableRatCDF.stieltjesFunction_nonneg`：∀ {α : Ty
pe u_1} {f : α → ℚ → ℝ} [inst : MeasurableSpace α] (hf : ProbabilityTheory.IsMea
surableRatCDF f) (a : α)   (r : ℝ), 0 ≤ ↑(hf.stielt…
· 使用引理 `ProbabilityTheory.isMeasurableRatCDF_toRatCDF`：isMeasurableRatCDF_toRatC
DF (hf : Measurable f) : IsMeasurableRatCDF (toRatCDF f) where isRatStieltjesPoi
nt a
-/
lemma stieltjesOfMeasurableRat_nonneg (hf : Measurable f) (a : α) (r : ℝ) :
    0 ≤ stieltjesOfMeasurableRat f hf a r := IsMeasurableRatCDF.stieltjesFunction_nonneg _ a r
/-
**ProbabilityTheory.stieltjesOfMeasurableRat_le_one** 是 Mathlib 中的一个引理，位于命名空间 `P
robabilityTheory`。
形式化陈述：stieltjesOfMeasurableRat_le_one (hf : Measurable f) (a : α) (x : Real) : s
tieltjesOfMeasurableRat f hf a x <= 1
参数：hf : Measurable f；a : α；x : Real。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ProbabilityTheory.IsMeasurableRatCDF.stieltjesFunction_le_one`：∀ {α : Ty
pe u_1} {f : α → ℚ → ℝ} [inst : MeasurableSpace α] (hf : ProbabilityTheory.IsMea
surableRatCDF f) (a : α)   (x : ℝ), ↑(hf.stieltjesF…
· 使用引理 `ProbabilityTheory.isMeasurableRatCDF_toRatCDF`：isMeasurableRatCDF_toRatC
DF (hf : Measurable f) : IsMeasurableRatCDF (toRatCDF f) where isRatStieltjesPoi
nt a
-/
lemma stieltjesOfMeasurableRat_le_one (hf : Measurable f) (a : α) (x : ℝ) :
    stieltjesOfMeasurableRat f hf a x ≤ 1 := IsMeasurableRatCDF.stieltjesFunction_le_one _ a x
/-
**ProbabilityTheory.tendsto_stieltjesOfMeasurableRat_atBot** 是 Mathlib 中的一个引理，位于
命名空间 `ProbabilityTheory`。
形式化陈述：tendsto_stieltjesOfMeasurableRat_atBot (hf : Measurable f) (a : α) : Tends
to (stieltjesOfMeasurableRat f hf a) atBot (𝓝 0)
参数：hf : Measurable f；a : α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ProbabilityTheory.IsMeasurableRatCDF.tendsto_stieltjesFunction_atBot`：∀ 
{α : Type u_1} {f : α → ℚ → ℝ} [inst : MeasurableSpace α] (hf : ProbabilityTheor
y.IsMeasurableRatCDF f) (a : α),   Filter.Tendsto (↑(hf.st…
· 使用引理 `ProbabilityTheory.isMeasurableRatCDF_toRatCDF`：isMeasurableRatCDF_toRatC
DF (hf : Measurable f) : IsMeasurableRatCDF (toRatCDF f) where isRatStieltjesPoi
nt a
-/
lemma tendsto_stieltjesOfMeasurableRat_atBot (hf : Measurable f) (a : α) :
    Tendsto (stieltjesOfMeasurableRat f hf a) atBot (𝓝 0) :=
  IsMeasurableRatCDF.tendsto_stieltjesFunction_atBot _ a
/-
**ProbabilityTheory.tendsto_stieltjesOfMeasurableRat_atTop** 是 Mathlib 中的一个引理，位于
命名空间 `ProbabilityTheory`。
形式化陈述：tendsto_stieltjesOfMeasurableRat_atTop (hf : Measurable f) (a : α) : Tends
to (stieltjesOfMeasurableRat f hf a) atTop (𝓝 1)
参数：hf : Measurable f；a : α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ProbabilityTheory.IsMeasurableRatCDF.tendsto_stieltjesFunction_atTop`：∀ 
{α : Type u_1} {f : α → ℚ → ℝ} [inst : MeasurableSpace α] (hf : ProbabilityTheor
y.IsMeasurableRatCDF f) (a : α),   Filter.Tendsto (↑(hf.st…
· 使用引理 `ProbabilityTheory.isMeasurableRatCDF_toRatCDF`：isMeasurableRatCDF_toRatC
DF (hf : Measurable f) : IsMeasurableRatCDF (toRatCDF f) where isRatStieltjesPoi
nt a
-/
lemma tendsto_stieltjesOfMeasurableRat_atTop (hf : Measurable f) (a : α) :
    Tendsto (stieltjesOfMeasurableRat f hf a) atTop (𝓝 1) :=
  IsMeasurableRatCDF.tendsto_stieltjesFunction_atTop _ a
/-
**ProbabilityTheory.measurable_stieltjesOfMeasurableRat** 是 Mathlib 中的一个引理，位于命名空
间 `ProbabilityTheory`。
形式化陈述：measurable_stieltjesOfMeasurableRat (hf : Measurable f) (x : Real) : Measu
rable fun a => stieltjesOfMeasurableRat f hf a x
参数：hf : Measurable f；x : Real。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ProbabilityTheory.IsMeasurableRatCDF.measurable_stieltjesFunction`：∀ {α 
: Type u_1} {f : α → ℚ → ℝ} [inst : MeasurableSpace α] (hf : ProbabilityTheory.I
sMeasurableRatCDF f) (x : ℝ),   Measurable fun a => ↑(h…
· 使用引理 `ProbabilityTheory.isMeasurableRatCDF_toRatCDF`：isMeasurableRatCDF_toRatC
DF (hf : Measurable f) : IsMeasurableRatCDF (toRatCDF f) where isRatStieltjesPoi
nt a
-/
lemma measurable_stieltjesOfMeasurableRat (hf : Measurable f) (x : ℝ) :
    Measurable fun a ↦ stieltjesOfMeasurableRat f hf a x :=
  IsMeasurableRatCDF.measurable_stieltjesFunction _ x
/-
**ProbabilityTheory.stronglyMeasurable_stieltjesOfMeasurableRat** 是 Mathlib 中的一个
引理，位于命名空间 `ProbabilityTheory`。
形式化陈述：stronglyMeasurable_stieltjesOfMeasurableRat (hf : Measurable f) (x : Real)
 : StronglyMeasurable fun a => stieltjesOfMeasurableRat f hf a x
参数：hf : Measurable f；x : Real。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ProbabilityTheory.IsMeasurableRatCDF.stronglyMeasurable_stieltjesFunctio
n`：∀ {α : Type u_1} {f : α → ℚ → ℝ} [inst : MeasurableSpace α] (hf : Probability
Theory.IsMeasurableRatCDF f) (x : ℝ),   MeasureTheory.StronglyM…
· 使用引理 `ProbabilityTheory.isMeasurableRatCDF_toRatCDF`：isMeasurableRatCDF_toRatC
DF (hf : Measurable f) : IsMeasurableRatCDF (toRatCDF f) where isRatStieltjesPoi
nt a
-/
lemma stronglyMeasurable_stieltjesOfMeasurableRat (hf : Measurable f) (x : ℝ) :
    StronglyMeasurable fun a ↦ stieltjesOfMeasurableRat f hf a x :=
  IsMeasurableRatCDF.stronglyMeasurable_stieltjesFunction _ x

section Measure

/-
**ProbabilityTheory.measure_stieltjesOfMeasurableRat_Iic** 是 Mathlib 中的一个引理，位于命名
空间 `ProbabilityTheory`。
形式化陈述：measure_stieltjesOfMeasurableRat_Iic (hf : Measurable f) (a : α) (x : Real
) : (stieltjesOfMeasurableRat f hf a).measure (Iic x) = ENNReal.ofReal (stieltje
sOfMeasurableRat f hf a x)
参数：hf : Measurable f；a : α；x : Real。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ProbabilityTheory.IsMeasurableRatCDF.measure_stieltjesFunction_Iic`：∀ {α
 : Type u_1} {f : α → ℚ → ℝ} [inst : MeasurableSpace α] (hf : ProbabilityTheory.
IsMeasurableRatCDF f) (a : α)   (x : ℝ), (hf.stieltjesFu…
· 使用引理 `ProbabilityTheory.isMeasurableRatCDF_toRatCDF`：isMeasurableRatCDF_toRatC
DF (hf : Measurable f) : IsMeasurableRatCDF (toRatCDF f) where isRatStieltjesPoi
nt a
-/
lemma measure_stieltjesOfMeasurableRat_Iic (hf : Measurable f) (a : α) (x : ℝ) :
    (stieltjesOfMeasurableRat f hf a).measure (Iic x)
      = ENNReal.ofReal (stieltjesOfMeasurableRat f hf a x) :=
  IsMeasurableRatCDF.measure_stieltjesFunction_Iic _ _ _
/-
**ProbabilityTheory.measure_stieltjesOfMeasurableRat_univ** 是 Mathlib 中的一个引理，位于命
名空间 `ProbabilityTheory`。
形式化陈述：measure_stieltjesOfMeasurableRat_univ (hf : Measurable f) (a : α) : (stiel
tjesOfMeasurableRat f hf a).measure univ = 1
参数：hf : Measurable f；a : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ProbabilityTheory.IsMeasurableRatCDF.measure_stieltjesFunction_univ`：∀ {
α : Type u_1} {f : α → ℚ → ℝ} [inst : MeasurableSpace α] (hf : ProbabilityTheory
.IsMeasurableRatCDF f) (a : α),   (hf.stieltjesFunction a…
· 使用引理 `ProbabilityTheory.isMeasurableRatCDF_toRatCDF`：isMeasurableRatCDF_toRatC
DF (hf : Measurable f) : IsMeasurableRatCDF (toRatCDF f) where isRatStieltjesPoi
nt a
-/
lemma measure_stieltjesOfMeasurableRat_univ (hf : Measurable f) (a : α) :
    (stieltjesOfMeasurableRat f hf a).measure univ = 1 :=
  IsMeasurableRatCDF.measure_stieltjesFunction_univ _ _
/-
**ProbabilityTheory.instIsProbabilityMeasure_stieltjesOfMeasurableRat** 是 Mathli
b 中的一个实例，位于命名空间 `ProbabilityTheory`。
形式化陈述：instIsProbabilityMeasure_stieltjesOfMeasurableRat (hf : Measurable f) (a :
 α) : IsProbabilityMeasure (stieltjesOfMeasurableRat f hf a).measure
参数：hf : Measurable f；a : α。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `ProbabilityTheory.IsMeasurableRatCDF.instIsProbabilityMeasure_stieltjesF
unction`：∀ {α : Type u_1} {f : α → ℚ → ℝ} [inst : MeasurableSpace α] (hf : Proba
bilityTheory.IsMeasurableRatCDF f) (a : α),   MeasureTheory.IsProbabi…
· 使用引理 `ProbabilityTheory.isMeasurableRatCDF_toRatCDF`：isMeasurableRatCDF_toRatC
DF (hf : Measurable f) : IsMeasurableRatCDF (toRatCDF f) where isRatStieltjesPoi
nt a
-/
instance instIsProbabilityMeasure_stieltjesOfMeasurableRat
    (hf : Measurable f) (a : α) :
    IsProbabilityMeasure (stieltjesOfMeasurableRat f hf a).measure :=
  IsMeasurableRatCDF.instIsProbabilityMeasure_stieltjesFunction _ _
/-
**ProbabilityTheory.measurable_measure_stieltjesOfMeasurableRat** 是 Mathlib 中的一个
引理，位于命名空间 `ProbabilityTheory`。
形式化陈述：measurable_measure_stieltjesOfMeasurableRat (hf : Measurable f) : Measurab
le fun a => (stieltjesOfMeasurableRat f hf a).measure
参数：hf : Measurable f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ProbabilityTheory.IsMeasurableRatCDF.measurable_measure_stieltjesFunctio
n`：∀ {α : Type u_1} {f : α → ℚ → ℝ} [inst : MeasurableSpace α] (hf : Probability
Theory.IsMeasurableRatCDF f),   Measurable fun a => (hf.stieltj…
· 使用引理 `ProbabilityTheory.isMeasurableRatCDF_toRatCDF`：isMeasurableRatCDF_toRatC
DF (hf : Measurable f) : IsMeasurableRatCDF (toRatCDF f) where isRatStieltjesPoi
nt a
-/
lemma measurable_measure_stieltjesOfMeasurableRat (hf : Measurable f) :
    Measurable fun a ↦ (stieltjesOfMeasurableRat f hf a).measure :=
  IsMeasurableRatCDF.measurable_measure_stieltjesFunction _

end Measure

end stieltjesOfMeasurableRat

end ProbabilityTheory

