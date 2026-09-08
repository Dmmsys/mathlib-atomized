/-
Copyright (c) 2019 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl
-/
module

public import Mathlib.MeasureTheory.Constructions.Polish.Basic
public import Mathlib.MeasureTheory.Integral.Lebesgue.Countable

/-!
# The Giry monad

Let X be a measurable space. The collection of all measures on X again
forms a measurable space. This construction forms a monad on
measurable spaces and measurable functions, called the Giry monad.

Note that most sources use the term "Giry monad" for the restriction
to *probability* measures. Here we include all measures on X.

See also `Mathlib/MeasureTheory/Category/MeasCat.lean`, containing an upgrade of the type-level
monad to an honest monad of the functor `measure : MeasCat ⥤ MeasCat`.

## References

* <https://ncatlab.org/nlab/show/Giry+monad>

## Tags

giry monad
-/

@[expose] public section


noncomputable section

open ENNReal Set Filter

variable {α β : Type*}

namespace MeasureTheory

namespace Measure

variable {mα : MeasurableSpace α} {mβ : MeasurableSpace β}

/-- Measurability structure on `Measure`: Measures are measurable w.r.t. all projections -/
/-
**MeasureTheory.Measure.instMeasurableSpace** 是 Mathlib 中的一个实例，位于命名空间 `MeasureTh
eory.Measure`。
形式化陈述：instMeasurableSpace : MeasurableSpace (Measure α)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Measurability structure on `Measure`: Measures are measurable w.r.t. all project
ions
-/
instance instMeasurableSpace : MeasurableSpace (Measure α) :=
  ⨆ (s : Set α) (_ : MeasurableSet s), (borel ℝ≥0∞).comap fun μ => μ s
/-
**MeasureTheory.Measure.measurable_coe** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.
Measure`。
形式化陈述：measurable_coe {s : Set α} (hs : MeasurableSet s) : Measurable fun μ : Mea
sure α => μ s
参数：hs : MeasurableSet s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Measurable.of_comap_le`：∀ {α : Type u_1} {β : Type u_2} {m₁ : Measurable
Space α} {m₂ : MeasurableSpace β} {f : α → β},   MeasurableSpace.comap f m₂ ≤ m₁
 → Measurabl…
· 使用定理 `le_iSup_of_le`：le_iSup_of_le (i : ι) (h : a <= f i) : a <= iSup f
· 使用引理 `le_rfl`：le_rfl : a <= a
-/
theorem measurable_coe {s : Set α} (hs : MeasurableSet s) : Measurable fun μ : Measure α => μ s :=
  Measurable.of_comap_le <| le_iSup_of_le s <| le_iSup_of_le hs <| le_rfl
/-
**MeasureTheory.Measure.measurable_of_measurable_coe** 是 Mathlib 中的一个定理，位于命名空间 `
MeasureTheory.Measure`。
形式化陈述：measurable_of_measurable_coe (f : β -> Measure α) (h : forall (s : Set α),
 MeasurableSet s -> Measurable fun b => f b s) : Measurable f
参数：f : β -> Measure α；h : forall (s : Set α), MeasurableSet s -> Measurable fun 
b => f b s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Measurable.of_le_map`：∀ {α : Type u_1} {β : Type u_2} {m₁ : MeasurableSp
ace α} {m₂ : MeasurableSpace β} {f : α → β},   m₂ ≤ MeasurableSpace.map f m₁ → M
easurable …
· 使用定理 `iSup₂_le`：iSup₂_le {f : forall i, κ i -> α} (h : forall i j, f i j <= a)
 : ⨆ (i) (j), f i j <= a
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `MeasurableSpace.comap_le_iff_le_map`：comap_le_iff_le_map {f : α -> β} : 
m'.comap f <= m ↔ m' <= m.map f
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasurableSpace.map_comp`：map_comp {f : α -> β} {g : β -> γ} : (m.map f)
.map g = m.map (g ∘ f)
-/
theorem measurable_of_measurable_coe (f : β → Measure α)
    (h : ∀ (s : Set α), MeasurableSet s → Measurable fun b => f b s) : Measurable f :=
  Measurable.of_le_map <|
    iSup₂_le fun s hs =>
      MeasurableSpace.comap_le_iff_le_map.2 <| by rw [MeasurableSpace.map_comp]; exact h s hs
/-
**MeasureTheory.Measure.instMeasurableAdd** 是 Mathlib 中的一个实例，位于命名空间 `MeasureTheo
ry.Measure`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instMeasurableAdd₂ {α : Type*} {m : MeasurableSpace α} : MeasurableAdd₂ (Measure α) := by
  refine ⟨Measure.measurable_of_measurable_coe _ fun s hs => ?_⟩
  simp_rw [Measure.coe_add, Pi.add_apply]
  refine Measurable.add ?_ ?_
  · exact (Measure.measurable_coe hs).comp measurable_fst
  · exact (Measure.measurable_coe hs).comp measurable_snd

-- There is no typeclass for measurability of `SMul` only on that side, otherwise we could
-- turn that into an instance.
@[fun_prop]
/-
**MeasureTheory.Measure._root_.Measurable.smul_measure** 是 Mathlib 中的一个引理，位于命名空间
 `MeasureTheory.Measure`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma _root_.Measurable.smul_measure {f : α → ℝ≥0∞} (hf : Measurable f) (μ : Measure β) :
    Measurable (fun x ↦ f x • μ) := by
  refine Measure.measurable_of_measurable_coe _ fun s hs ↦ ?_
  simp only [Measure.smul_apply, smul_eq_mul]
  fun_prop
/-
**MeasureTheory.Measure.measurable_measure** 是 Mathlib 中的一个定理，位于命名空间 `MeasureThe
ory.Measure`。
形式化陈述：measurable_measure {μ : α -> Measure β} : Measurable μ ↔ forall (s : Set β
), MeasurableSet s -> Measurable fun b => μ b s
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Measurable.comp`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {x : Mea
surableSpace α} {x_1 : MeasurableSpace β}   {x_2 : MeasurableSpace γ} {g : β → γ
} {f …
· 使用定理 `MeasureTheory.Measure.measurable_coe`：measurable_coe {s : Set α} (hs : M
easurableSet s) : Measurable fun μ : Measure α => μ s
· 使用定理 `MeasureTheory.Measure.measurable_of_measurable_coe`：measurable_of_measur
able_coe (f : β -> Measure α) (h : forall (s : Set α), MeasurableSet s -> Measur
able fun b => f b s) : Measurable f
-/
theorem measurable_measure {μ : α → Measure β} :
    Measurable μ ↔ ∀ (s : Set β), MeasurableSet s → Measurable fun b => μ b s :=
  ⟨fun hμ _s hs => (measurable_coe hs).comp hμ, measurable_of_measurable_coe μ⟩
/-
**MeasureTheory.Measure._root_.Measurable.measure_of_isPiSystem** 是 Mathlib 中的一个
定理，位于命名空间 `MeasureTheory.Measure`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.Measurable.measure_of_isPiSystem {μ : α → Measure β} [∀ a, IsFiniteMeasure (μ a)]
    {S : Set (Set β)} (hgen : ‹MeasurableSpace β› = .generateFrom S) (hpi : IsPiSystem S)
    (h_basic : ∀ s ∈ S, Measurable fun a ↦ μ a s) (h_univ : Measurable fun a ↦ μ a univ) :
    Measurable μ := by
  rw [measurable_measure]
  intro s hs
  induction s, hs using MeasurableSpace.induction_on_inter hgen hpi with
  | empty => simp
  | basic s hs => exact h_basic s hs
  | compl s hsm ihs =>
    simp only [measure_compl hsm (measure_ne_top _ _)]
    exact h_univ.sub ihs
  | iUnion f hfd hfm ihf =>
    simpa only [measure_iUnion hfd hfm] using .tsum ihf
/-
**MeasureTheory.Measure._root_.Measurable.measure_of_isPiSystem_of_isProbability
Measure** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.Measure`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.Measurable.measure_of_isPiSystem_of_isProbabilityMeasure {μ : α → Measure β}
    [∀ a, IsProbabilityMeasure (μ a)]
    {S : Set (Set β)} (hgen : ‹MeasurableSpace β› = .generateFrom S) (hpi : IsPiSystem S)
    (h_basic : ∀ s ∈ S, Measurable fun a ↦ μ a s) : Measurable μ :=
  .measure_of_isPiSystem hgen hpi h_basic <| by simp

@[fun_prop]
/-
**MeasureTheory.Measure.measurable_map** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.
Measure`。
形式化陈述：measurable_map (f : α -> β) (hf : Measurable f) : Measurable fun μ : Measu
re α => map f μ
参数：f : α -> β；hf : Measurable f。
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
· 使用定理 `MeasureTheory.Measure.measurable_coe`：measurable_coe {s : Set α} (hs : M
easurableSet s) : Measurable fun μ : Measure α => μ s
-/
theorem measurable_map (f : α → β) (hf : Measurable f) :
    Measurable fun μ : Measure α => map f μ := by
  refine measurable_of_measurable_coe _ fun s hs => ?_
  simp_rw [map_apply hf hs]
  exact measurable_coe (hf hs)

@[fun_prop]
/-
**MeasureTheory.Measure.measurable_dirac** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheor
y.Measure`。
形式化陈述：measurable_dirac : Measurable (Measure.dirac : α -> Measure α)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.measurable_of_measurable_coe`：measurable_of_measur
able_coe (f : β -> Measure α) (h : forall (s : Set α), MeasurableSet s -> Measur
able fun b => f b s) : Measurable f
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `MeasureTheory.Measure.dirac_apply'`：dirac_apply' (a : α) (hs : Measurabl
eSet s) : dirac a s = s.indicator 1 a
· 使用定理 `Measurable.indicator`：Measurable.indicator [Zero β] (hf : Measurable f) 
(hs : MeasurableSet s) : Measurable (s.indicator f)
· 使用定理 `measurable_one`：measurable_one [One α] : Measurable (1 : β -> α)
-/
theorem measurable_dirac : Measurable (Measure.dirac : α → Measure α) := by
  refine measurable_of_measurable_coe _ fun s hs => ?_
  simp_rw [dirac_apply' _ hs]
  exact measurable_one.indicator hs

@[fun_prop]
/-
**MeasureTheory.Measure.measurable_lintegral** 是 Mathlib 中的一个定理，位于命名空间 `MeasureT
heory.Measure`。
形式化陈述：measurable_lintegral {f : α -> Real>=0∞} (hf : Measurable f) : Measurable 
fun μ : Measure α => ∫⁻ x, f x ∂μ
参数：hf : Measurable f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `MeasureTheory.lintegral_eq_iSup_eapprox_lintegral`：lintegral_eq_iSup_eap
prox_lintegral {f : α -> Real>=0∞} (hf : Measurable f) : ∫⁻ a, f a ∂μ = ⨆ n, (ea
pprox f n).lintegral μ
· 使用定理 `Measurable.iSup`：∀ {α : Type u_1} {δ : Type u_4} [inst : TopologicalSpac
e α] {mα : MeasurableSpace α} [BorelSpace α]   {mδ : MeasurableSpace δ} [inst_2 
: Con…
· 使用定理 `ENNReal.instOrderTopology`：OrderTopology ENNReal
· 使用定理 `ENNReal.instSecondCountableTopology`：SecondCountableTopology ENNReal
· 使用定理 `instCountableNat`：Countable ℕ
· 使用定理 `Finset.measurable_fun_sum`：∀ {M : Type u_2} {ι : Type u_3} {α : Type u_4
} [inst : AddCommMonoid M] [inst_1 : MeasurableSpace M] [MeasurableAdd₂ M]   {m 
: MeasurableSpa…
· 使用定理 `ContinuousAdd.measurableMul₂`：∀ {γ : Type u_3} [inst : TopologicalSpace 
γ] [inst_1 : MeasurableSpace γ] [BorelSpace γ] [SecondCountableTopology γ]   [in
st_4 : Add γ] [Con…
· 使用定理 `ENNReal.instContinuousAdd`：ContinuousAdd ENNReal
· 使用定理 `Measurable.const_mul`：Measurable.const_mul [MeasurableMul M] (hf : Measu
rable f) (c : M) : Measurable fun x => c * f x
· 使用定理 `MeasurableMul₂.toMeasurableMul`：∀ {M : Type u_2} [inst : MeasurableSpace
 M] [inst_1 : Mul M] [MeasurableMul₂ M], MeasurableMul M
· 使用定理 `MeasureTheory.Measure.measurable_coe`：measurable_coe {s : Set α} (hs : M
easurableSet s) : Measurable fun μ : Measure α => μ s
· 使用定理 `MeasureTheory.SimpleFunc.measurableSet_preimage`：measurableSet_preimage 
(f : α ->ₛ β) (s) : MeasurableSet (f ⁻¹' s)
-/
theorem measurable_lintegral {f : α → ℝ≥0∞} (hf : Measurable f) :
    Measurable fun μ : Measure α => ∫⁻ x, f x ∂μ := by
  simp only [lintegral_eq_iSup_eapprox_lintegral, hf, SimpleFunc.lintegral]
  refine .iSup fun n => Finset.measurable_fun_sum _ fun i _ => ?_
  refine Measurable.const_mul ?_ _
  exact measurable_coe ((SimpleFunc.eapprox f n).measurableSet_preimage _)

/-- Monadic join on `Measure` in the category of measurable spaces and measurable
functions. -/
/-
**MeasureTheory.Measure.join** 是 Mathlib 中的一个定义，位于命名空间 `MeasureTheory.Measure`。
形式化陈述：join (m : Measure (Measure α)) : Measure α
参数：m : Measure (Measure α)。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Monadic join on `Measure` in the category of measurable spaces and measurable
functions.
-/
def join (m : Measure (Measure α)) : Measure α :=
  Measure.ofMeasurable (fun s _ => ∫⁻ μ, μ s ∂m)
    (by simp only [measure_empty, lintegral_const, zero_mul])
    (by
      intro f hf h
      simp_rw [measure_iUnion h hf]
      apply lintegral_tsum
      intro i; exact (measurable_coe (hf i)).aemeasurable)

@[simp]
/-
**MeasureTheory.Measure.join_apply** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.Meas
ure`。
形式化陈述：join_apply {m : Measure (Measure α)} {s : Set α} (hs : MeasurableSet s) : 
join m s = ∫⁻ μ, μ s ∂m
参数：Measure α；hs : MeasurableSet s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.ofMeasurable_apply`：ofMeasurable_apply {m : forall
 s : Set α, MeasurableSet s -> Real>=0∞} {m0 : m ∅ MeasurableSet.empty = 0} {mU 
: forall ⦃f : Nat -> Set α⦄ (h…
-/
theorem join_apply {m : Measure (Measure α)} {s : Set α} (hs : MeasurableSet s) :
    join m s = ∫⁻ μ, μ s ∂m :=
  Measure.ofMeasurable_apply s hs
/-
**MeasureTheory.Measure.le_join_apply** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.M
easure`。
形式化陈述：le_join_apply (m : Measure (Measure α)) (s : Set α) : ∫⁻ μ, μ s ∂m <= join
 m s
参数：m : Measure (Measure α)；s : Set α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.measure_eq_iInf`：measure_eq_iInf (s : Set α) : μ s = ⨅ (t)
 (_ : s subseteq t) (_ : MeasurableSet t), μ t
· 使用定理 `le_iInf₂`：∀ {α : Type u_1} {ι : Sort u_4} {κ : ι → Sort u_6} [inst : Com
pleteLattice α] {a : α} {f : (i : ι) → κ i → α},   (∀ (i : ι) (j : κ i), a ≤ f…
· 使用定理 `le_iInf`：∀ {α : Type u_1} {ι : Sort u_4} [inst : CompleteLattice α] {f :
 ι → α} {a : α}, (∀ (i : ι), a ≤ f i) → a ≤ iInf f
· 使用定理 `MeasureTheory.lintegral_mono_fn'`：∀ {α : Type u_1} {m : MeasurableSpace 
α} {μ ν : MeasureTheory.Measure α},   μ ≤ ν → ∀ ⦃f g : α → ENNReal⦄, (∀ (x : α),
 f x ≤ g x) → ∫⁻ (a : …
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `MeasureTheory.measure_mono`：measure_mono (h : s subseteq t) : μ s <= μ t
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.Measure.join_apply`：join_apply {m : Measure (Measure α)} {
s : Set α} (hs : MeasurableSet s) : join m s = ∫⁻ μ, μ s ∂m
-/
theorem le_join_apply (m : Measure (Measure α)) (s : Set α) : ∫⁻ μ, μ s ∂m ≤ join m s := by
  rw [measure_eq_iInf]
  exact le_iInf₂ fun t hst ↦ le_iInf fun htm ↦ join_apply htm ▸ by gcongr

@[simp]
/-
**MeasureTheory.Measure.join_smul** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.Measu
re`。
形式化陈述：join_smul {R : Type*} [SMul R Real>=0∞] [IsScalarTower R Real>=0∞ Real>=0∞
] (c : R) (m : Measure (Measure α)) : (c • m).join = c • m.join
参数：c : R；m : Measure (Measure α)。
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
· 使用定理 `MeasureTheory.Measure.join_apply`：join_apply {m : Measure (Measure α)} {
s : Set α} (hs : MeasurableSet s) : join m s = ∫⁻ μ, μ s ∂m
· 使用定理 `MeasureTheory.lintegral_smul_measure`：lintegral_smul_measure {R : Type*}
 [SMul R Real>=0∞] [IsScalarTower R Real>=0∞ Real>=0∞] (c : R) (f : α -> Real>=0
∞) : ∫⁻ a, f a ∂c • μ = c …
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem join_smul {R : Type*} [SMul R ℝ≥0∞] [IsScalarTower R ℝ≥0∞ ℝ≥0∞] (c : R)
    (m : Measure (Measure α)) : (c • m).join = c • m.join := by
  ext s hs
  simp [hs]
/-
**MeasureTheory.Measure.join_sum** 是 Mathlib 中的一个引理，位于命名空间 `MeasureTheory.Measur
e`。
形式化陈述：join_sum {ι : Type*} (m : ι -> Measure (Measure α)) : (sum m).join = sum f
un (i : ι) => (m i).join
参数：m : ι -> Measure (Measure α)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.ext`：ext (h : forall s, MeasurableSet s -> μ₁ s = 
μ₂ s) : μ₁ = μ₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.Measure.sum_apply`：sum_apply (f : ι -> Measure α) {s : Set
 α} (hs : MeasurableSet s) : sum f s = ∑' i, f i s
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `MeasureTheory.Measure.join_apply`：join_apply {m : Measure (Measure α)} {
s : Set α} (hs : MeasurableSet s) : join m s = ∫⁻ μ, μ s ∂m
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `MeasureTheory.lintegral_sum_measure`：lintegral_sum_measure {m : Measurab
leSpace α} {ι} (f : α -> Real>=0∞) (μ : ι -> Measure α) : ∫⁻ a, f a ∂Measure.sum
 μ = ∑' i, ∫⁻ a, f a ∂μ i
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma join_sum {ι : Type*} (m : ι → Measure (Measure α)) :
    (sum m).join = sum fun (i : ι) ↦ (m i).join := by
  ext s hs
  simp_rw [sum_apply _ hs, join_apply hs, lintegral_sum_measure]

@[simp]
/-
**MeasureTheory.Measure.join_dirac** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.Meas
ure`。
形式化陈述：join_dirac (μ : Measure α) : join (dirac μ) = μ
参数：μ : Measure α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.ext`：ext (h : forall s, MeasurableSet s -> μ₁ s = 
μ₂ s) : μ₁ = μ₂
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.Measure.join_apply`：join_apply {m : Measure (Measure α)} {
s : Set α} (hs : MeasurableSet s) : join m s = ∫⁻ μ, μ s ∂m
· 使用定理 `MeasureTheory.lintegral_dirac'`：lintegral_dirac' (a : α) {f : α -> Real>
=0∞} (hf : Measurable f) : ∫⁻ a, f a ∂dirac a = f a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem join_dirac (μ : Measure α) : join (dirac μ) = μ := by
  ext s hs
  simp [hs, lintegral_dirac', measurable_coe]
/-
**MeasureTheory.Measure.le_ae_join** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.Meas
ure`。
形式化陈述：le_ae_join (m : Measure (Measure α)) : (ae m).bind ae <= ae m.join
参数：m : Measure (Measure α)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `MeasureTheory.exists_measurable_superset_of_null`：exists_measurable_supe
rset_of_null (h : μ s = 0) : exists t, s subseteq t ∧ MeasurableSet t ∧ μ t = 0
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Filter.mem_bind'`：mem_bind' {s : Set β} {f : Filter α} {m : α -> Filter 
β} : s in bind f m ↔ { a | s in m a } in f
· 使用定理 `Filter.Eventually.mono`：∀ {α : Type u} {p q : α → Prop} {f : Filter α}, 
(∀ᶠ (x : α) in f, p x) → (∀ (x : α), p x → q x) → ∀ᶠ (x : α) in f, q x
· 使用定理 `MeasureTheory.lintegral_eq_zero_iff`：lintegral_eq_zero_iff {f : α -> Rea
l>=0∞} (hf : Measurable f) : ∫⁻ a, f a ∂μ = 0 ↔ f =ᵐ[μ] 0
· 使用定理 `MeasureTheory.Measure.measurable_coe`：measurable_coe {s : Set α} (hs : M
easurableSet s) : Measurable fun μ : Measure α => μ s
· 使用定理 `MeasureTheory.Measure.join_apply`：join_apply {m : Measure (Measure α)} {
s : Set α} (hs : MeasurableSet s) : join m s = ∫⁻ μ, μ s ∂m
· 使用定理 `MeasureTheory.measure_mono_null`：measure_mono_null (h : s subseteq t) (h
t : μ t = 0) : μ s = 0
-/
theorem le_ae_join (m : Measure (Measure α)) : (ae m).bind ae ≤ ae m.join := by
  intro s hs
  rcases exists_measurable_superset_of_null hs with ⟨t, hst, htm, ht⟩
  rw [join_apply htm, lintegral_eq_zero_iff (measurable_coe htm)] at ht
  rw [mem_bind']
  exact ht.mono fun _ ↦ measure_mono_null hst
/-
**MeasureTheory.Measure.ae_ae_of_ae_join** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheor
y.Measure`。
形式化陈述：ae_ae_of_ae_join {m : Measure (Measure α)} {p : α -> Prop} (h : forallᵐ a 
∂m.join, p a) : forallᵐ μ ∂m, forallᵐ a ∂μ, p a
参数：Measure α；h : forallᵐ a ∂m.join, p a。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `MeasureTheory.Measure.le_ae_join`：le_ae_join (m : Measure (Measure α)) :
 (ae m).bind ae <= ae m.join
-/
theorem ae_ae_of_ae_join {m : Measure (Measure α)} {p : α → Prop} (h : ∀ᵐ a ∂m.join, p a) :
    ∀ᵐ μ ∂m, ∀ᵐ a ∂μ, p a :=
  le_ae_join m h
/-
**MeasureTheory.Measure._root_.AEMeasurable.ae_of_join** 是 Mathlib 中的一个定理，位于命名空间
 `MeasureTheory.Measure`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.AEMeasurable.ae_of_join {m : Measure (Measure α)} {f : α → β}
    (h : AEMeasurable f m.join) : ∀ᵐ μ ∂m, AEMeasurable f μ :=
  let ⟨g, hgm, hg⟩ := h; (ae_ae_of_ae_join hg).mono fun _μ hμ ↦ ⟨g, hgm, hμ⟩
/-
**MeasureTheory.Measure.aemeasurable_lintegral** 是 Mathlib 中的一个定理，位于命名空间 `Measur
eTheory.Measure`。
形式化陈述：aemeasurable_lintegral {m : Measure (Measure α)} {f : α -> Real>=0∞} (h : 
AEMeasurable f m.join) : AEMeasurable (fun μ => ∫⁻ a, f a ∂μ) m
参数：Measure α；h : AEMeasurable f m.join。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `MeasureTheory.Measure.measurable_lintegral`：measurable_lintegral {f : α 
-> Real>=0∞} (hf : Measurable f) : Measurable fun μ : Measure α => ∫⁻ x, f x ∂μ
· 使用定理 `Filter.Eventually.mono`：∀ {α : Type u} {p q : α → Prop} {f : Filter α}, 
(∀ᶠ (x : α) in f, p x) → (∀ (x : α), p x → q x) → ∀ᶠ (x : α) in f, q x
· 使用定理 `MeasureTheory.Measure.ae_ae_of_ae_join`：ae_ae_of_ae_join {m : Measure (M
easure α)} {p : α -> Prop} (h : forallᵐ a ∂m.join, p a) : forallᵐ μ ∂m, forallᵐ 
a ∂μ, p a
· 使用定理 `MeasureTheory.lintegral_congr_ae`：lintegral_congr_ae {f g : α -> Real>=0
∞} (h : f =ᵐ[μ] g) : ∫⁻ a, f a ∂μ = ∫⁻ a, g a ∂μ
-/
theorem aemeasurable_lintegral {m : Measure (Measure α)} {f : α → ℝ≥0∞}
    (h : AEMeasurable f m.join) : AEMeasurable (fun μ ↦ ∫⁻ a, f a ∂μ) m :=
  let ⟨g, hgm, hfg⟩ := h
  ⟨fun μ ↦ ∫⁻ a, g a ∂μ, measurable_lintegral hgm,
    (ae_ae_of_ae_join hfg).mono fun _ ↦ lintegral_congr_ae⟩

@[simp]
/-
**MeasureTheory.Measure.join_zero** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.Measu
re`。
形式化陈述：join_zero : (0 : Measure (Measure α)).join = 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.ext`：ext (h : forall s, MeasurableSet s -> μ₁ s = 
μ₂ s) : μ₁ = μ₂
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.Measure.join_apply`：join_apply {m : Measure (Measure α)} {
s : Set α} (hs : MeasurableSet s) : join m s = ∫⁻ μ, μ s ∂m
· 使用定理 `MeasureTheory.lintegral_zero_measure`：lintegral_zero_measure {m : Measur
ableSpace α} (f : α -> Real>=0∞) : ∫⁻ a, f a ∂(0 : Measure α) = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem join_zero : (0 : Measure (Measure α)).join = 0 := by
  ext1 s hs
  simp [hs]

@[fun_prop]
/-
**MeasureTheory.Measure.measurable_join** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory
.Measure`。
形式化陈述：measurable_join : Measurable (join : Measure (Measure α) -> Measure α)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.measurable_of_measurable_coe`：measurable_of_measur
able_coe (f : β -> Measure α) (h : forall (s : Set α), MeasurableSet s -> Measur
able fun b => f b s) : Measurable f
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `MeasureTheory.Measure.join_apply`：join_apply {m : Measure (Measure α)} {
s : Set α} (hs : MeasurableSet s) : join m s = ∫⁻ μ, μ s ∂m
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `MeasureTheory.Measure.measurable_lintegral`：measurable_lintegral {f : α 
-> Real>=0∞} (hf : Measurable f) : Measurable fun μ : Measure α => ∫⁻ x, f x ∂μ
· 使用定理 `MeasureTheory.Measure.measurable_coe`：measurable_coe {s : Set α} (hs : M
easurableSet s) : Measurable fun μ : Measure α => μ s
-/
theorem measurable_join : Measurable (join : Measure (Measure α) → Measure α) :=
  measurable_of_measurable_coe _ fun s hs => by
    simp only [join_apply hs, measurable_lintegral (measurable_coe hs)]
/-
**MeasureTheory.Measure.lintegral_join** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.
Measure`。
形式化陈述：lintegral_join {m : Measure (Measure α)} {f : α -> Real>=0∞} (hf : AEMeasu
rable f (join m)) : ∫⁻ x, f x ∂join m = ∫⁻ μ, ∫⁻ x, f x ∂μ ∂m
参数：Measure α；hf : AEMeasurable f (join m)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Classical.em`：∀ (p : Prop), p ∨ ¬p
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.lintegral_eq_iSup_eapprox_lintegral`：lintegral_eq_iSup_eap
prox_lintegral {f : α -> Real>=0∞} (hf : Measurable f) : ∫⁻ a, f a ∂μ = ⨆ n, (ea
pprox f n).lintegral μ
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `MeasureTheory.Measure.join_apply`：join_apply {m : Measure (Measure α)} {
s : Set α} (hs : MeasurableSet s) : join m s = ∫⁻ μ, μ s ∂m
· 使用定理 `MeasureTheory.SimpleFunc.measurableSet_preimage`：measurableSet_preimage 
(f : α ->ₛ β) (s) : MeasurableSet (f ⁻¹' s)
· 使用定理 `MeasureTheory.lintegral_iSup`：lintegral_iSup {f : Nat -> α -> Real>=0∞} 
(hf : forall n, Measurable (f n)) (h_mono : Monotone f) : ∫⁻ a, ⨆ n, f n a ∂μ = 
⨆ n, ∫⁻ a, f n a ∂…
· 使用定理 `Finset.measurable_sum`：∀ {M : Type u_2} {ι : Type u_3} {α : Type u_4} [i
nst : AddCommMonoid M] [inst_1 : MeasurableSpace M] [MeasurableAdd₂ M]   {m : Me
asurableSpa…
· 使用定理 `ContinuousAdd.measurableMul₂`：∀ {γ : Type u_3} [inst : TopologicalSpace 
γ] [inst_1 : MeasurableSpace γ] [BorelSpace γ] [SecondCountableTopology γ]   [in
st_4 : Add γ] [Con…
· 使用定理 `ENNReal.instSecondCountableTopology`：SecondCountableTopology ENNReal
· 使用定理 `ENNReal.instContinuousAdd`：ContinuousAdd ENNReal
· 使用定理 `Measurable.const_mul`：Measurable.const_mul [MeasurableMul M] (hf : Measu
rable f) (c : M) : Measurable fun x => c * f x
· 使用定理 `MeasurableMul₂.toMeasurableMul`：∀ {M : Type u_2} [inst : MeasurableSpace
 M] [inst_1 : Mul M] [MeasurableMul₂ M], MeasurableMul M
· 使用定理 `MeasureTheory.lintegral_finsetSum`：lintegral_finsetSum (s : Finset β) {f
 : β -> α -> Real>=0∞} (hf : forall b in s, Measurable (f b)) : ∫⁻ a, ∑ b in s, 
f b a ∂μ = ∑ b in s, ∫⁻…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `MeasureTheory.lintegral_const_mul`：lintegral_const_mul (r : Real>=0∞) {f
 : α -> Real>=0∞} (hf : Measurable f) : ∫⁻ a, r * f a ∂μ = r * ∫⁻ a, f a ∂μ
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `MeasureTheory.Measure.measurable_coe`：measurable_coe {s : Set α} (hs : M
easurableSet s) : Measurable fun μ : Measure α => μ s
· 使用定理 `MeasureTheory.SimpleFunc.lintegral_mono`：lintegral_mono {f g : α ->ₛ Rea
l>=0∞} (hfg : f <= g) (hμν : μ <= ν) : f.lintegral μ <= g.lintegral ν
· 使用定理 `MeasureTheory.SimpleFunc.monotone_eapprox`：monotone_eapprox (f : α -> Re
al>=0∞) : Monotone (eapprox f)
· 使用引理 `le_rfl`：le_rfl : a <= a
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `MeasureTheory.lintegral_congr_ae`：lintegral_congr_ae {f g : α -> Real>=0
∞} (h : f =ᵐ[μ] g) : ∫⁻ a, f a ∂μ = ∫⁻ a, g a ∂μ
· 使用定理 `Measurable.aemeasurable`：Measurable.aemeasurable (h : Measurable f) : AE
Measurable f μ
· 使用定理 `Filter.Eventually.mono`：∀ {α : Type u} {p q : α → Prop} {f : Filter α}, 
(∀ᶠ (x : α) in f, p x) → (∀ (x : α), p x → q x) → ∀ᶠ (x : α) in f, q x
· 使用定理 `MeasureTheory.Measure.ae_ae_of_ae_join`：ae_ae_of_ae_join {m : Measure (M
easure α)} {p : α -> Prop} (h : forallᵐ a ∂m.join, p a) : forallᵐ μ ∂m, forallᵐ 
a ∂μ, p a
（共 31 条，此处仅展示前 30 条）
-/
theorem lintegral_join {m : Measure (Measure α)} {f : α → ℝ≥0∞} (hf : AEMeasurable f (join m)) :
    ∫⁻ x, f x ∂join m = ∫⁻ μ, ∫⁻ x, f x ∂μ ∂m := by
  wlog hfm : Measurable f generalizing f
  · rcases hf with ⟨g, hgm, hfg⟩
    rw [lintegral_congr_ae hfg, this hgm.aemeasurable hgm]
    exact lintegral_congr_ae <| (ae_ae_of_ae_join hfg).mono fun μ hμ ↦
      .symm <| lintegral_congr_ae hμ
  simp_rw [lintegral_eq_iSup_eapprox_lintegral hfm, SimpleFunc.lintegral,
    join_apply (SimpleFunc.measurableSet_preimage _ _)]
  clear hf
  suffices
    ∀ (s : ℕ → Finset ℝ≥0∞) (f : ℕ → ℝ≥0∞ → Measure α → ℝ≥0∞), (∀ n r, Measurable (f n r)) →
      Monotone (fun n μ => ∑ r ∈ s n, r * f n r μ) →
      ⨆ n, ∑ r ∈ s n, r * ∫⁻ μ, f n r μ ∂m = ∫⁻ μ, ⨆ n, ∑ r ∈ s n, r * f n r μ ∂m by
    refine
      this (fun n => SimpleFunc.range (SimpleFunc.eapprox f n))
        (fun n r μ => μ (SimpleFunc.eapprox f n ⁻¹' {r})) ?_ ?_
    · exact fun n r => measurable_coe (SimpleFunc.measurableSet_preimage _ _)
    · exact fun n m h μ => SimpleFunc.lintegral_mono (SimpleFunc.monotone_eapprox _ h) le_rfl
  intro s f hf hm
  rw [lintegral_iSup _ hm]
  swap
  · fun_prop
  congr
  funext n
  rw [lintegral_finsetSum (s n)]
  · simp_rw [lintegral_const_mul _ (hf _ _)]
  · exact fun r _ => (hf _ _).const_mul _
/-
**MeasureTheory.Measure.lintegral_join_le** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheo
ry.Measure`。
形式化陈述：lintegral_join_le (f : α -> Real>=0∞) (m : Measure (Measure α)) : ∫⁻ x, f 
x ∂join m <= ∫⁻ μ, ∫⁻ x, f x ∂μ ∂m
参数：f : α -> Real>=0∞；m : Measure (Measure α)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.exists_measurable_le_lintegral_eq`：exists_measurable_le_li
ntegral_eq (f : α -> Real>=0∞) : exists g : α -> Real>=0∞, Measurable g ∧ g <= f
 ∧ ∫⁻ a, f a ∂μ = ∫⁻ a, g a ∂μ
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.Measure.lintegral_join`：lintegral_join {m : Measure (Measu
re α)} {f : α -> Real>=0∞} (hf : AEMeasurable f (join m)) : ∫⁻ x, f x ∂join m = 
∫⁻ μ, ∫⁻ x, f x ∂μ ∂m
· 使用定理 `Measurable.aemeasurable`：Measurable.aemeasurable (h : Measurable f) : AE
Measurable f μ
· 使用定理 `MeasureTheory.lintegral_mono_fn'`：∀ {α : Type u_1} {m : MeasurableSpace 
α} {μ ν : MeasureTheory.Measure α},   μ ≤ ν → ∀ ⦃f g : α → ENNReal⦄, (∀ (x : α),
 f x ≤ g x) → ∫⁻ (a : …
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
-/
theorem lintegral_join_le (f : α → ℝ≥0∞) (m : Measure (Measure α)) :
    ∫⁻ x, f x ∂join m ≤ ∫⁻ μ, ∫⁻ x, f x ∂μ ∂m := by
  rcases exists_measurable_le_lintegral_eq (join m) f with ⟨g, hgm, hgf, hfg_int⟩
  rw [hfg_int, lintegral_join hgm.aemeasurable]
  gcongr
  apply hgf

/-- Monadic bind on `Measure`, only works in the category of measurable spaces and measurable
functions. When the function `f` is not measurable the result is not well defined. -/
/-
**MeasureTheory.Measure.bind** 是 Mathlib 中的一个定义，位于命名空间 `MeasureTheory.Measure`。
形式化陈述：bind (m : Measure α) (f : α -> Measure β) : Measure β
参数：m : Measure α；f : α -> Measure β。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Monadic bind on `Measure`, only works in the category of measurable spaces and m
easurable
functions. When the function `f` is not measurable the result is not well define
d.
-/
def bind (m : Measure α) (f : α → Measure β) : Measure β :=
  join (map f m)

@[simp]
/-
**MeasureTheory.Measure.bind_zero_left** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.
Measure`。
形式化陈述：bind_zero_left (f : α -> Measure β) : bind (0 : Measure α) f = 0
参数：f : α -> Measure β。
该定理/引理给出了一组等式。
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
· 使用定理 `MeasureTheory.Measure.join_zero`：join_zero : (0 : Measure (Measure α)).j
oin = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem bind_zero_left (f : α → Measure β) : bind (0 : Measure α) f = 0 := by simp [bind]

@[simp]
/-
**MeasureTheory.Measure.bind_apply** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.Meas
ure`。
形式化陈述：bind_apply {m : Measure α} {f : α -> Measure β} {s : Set β} (hs : Measurab
leSet s) (hf : AEMeasurable f m) : bind m f s = ∫⁻ a, f a s ∂m
参数：hs : MeasurableSet s；hf : AEMeasurable f m。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.Measure.bind.eq_1`：∀ {α : Type u_1} {β : Type u_2} {mα : M
easurableSpace α} {mβ : MeasurableSpace β} (m : MeasureTheory.Measure α)   (f : 
α → MeasureTheory.Mea…
· 使用定理 `MeasureTheory.Measure.join_apply`：join_apply {m : Measure (Measure α)} {
s : Set α} (hs : MeasurableSet s) : join m s = ∫⁻ μ, μ s ∂m
· 使用定理 `MeasureTheory.lintegral_map'`：lintegral_map' {f : β -> Real>=0∞} {g : α 
-> β} (hf : AEMeasurable f (Measure.map g μ)) (hg : AEMeasurable g μ) : ∫⁻ a, f 
a ∂Measure.map g μ…
· 使用定理 `Measurable.aemeasurable`：Measurable.aemeasurable (h : Measurable f) : AE
Measurable f μ
· 使用定理 `MeasureTheory.Measure.measurable_coe`：measurable_coe {s : Set α} (hs : M
easurableSet s) : Measurable fun μ : Measure α => μ s
-/
theorem bind_apply {m : Measure α} {f : α → Measure β} {s : Set β} (hs : MeasurableSet s)
    (hf : AEMeasurable f m) : bind m f s = ∫⁻ a, f a s ∂m := by
  rw [bind, join_apply hs, lintegral_map' (measurable_coe hs).aemeasurable hf]
/-
**MeasureTheory.Measure.bind_apply_le** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.M
easure`。
形式化陈述：bind_apply_le {m : Measure α} (f : α -> Measure β) {s : Set β} (hs : Measu
rableSet s) : bind m f s <= ∫⁻ a, f a s ∂m
参数：f : α -> Measure β；hs : MeasurableSet s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.Measure.bind.eq_1`：∀ {α : Type u_1} {β : Type u_2} {mα : M
easurableSpace α} {mβ : MeasurableSpace β} (m : MeasureTheory.Measure α)   (f : 
α → MeasureTheory.Mea…
· 使用定理 `MeasureTheory.Measure.join_apply`：join_apply {m : Measure (Measure α)} {
s : Set α} (hs : MeasurableSet s) : join m s = ∫⁻ μ, μ s ∂m
· 使用定理 `MeasureTheory.lintegral_map_le`：lintegral_map_le (f : β -> Real>=0∞) (g 
: α -> β) : ∫⁻ a, f a ∂Measure.map g μ <= ∫⁻ a, f (g a) ∂μ
-/
theorem bind_apply_le {m : Measure α} (f : α → Measure β) {s : Set β} (hs : MeasurableSet s) :
    bind m f s ≤ ∫⁻ a, f a s ∂m := by
  rw [bind, join_apply hs]
  apply lintegral_map_le
/-
**MeasureTheory.Measure.ae_ae_of_ae_bind** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheor
y.Measure`。
形式化陈述：ae_ae_of_ae_bind {m : Measure α} {f : α -> Measure β} {p : β -> Prop} (hf 
: AEMeasurable f m) (h : forallᵐ b ∂m.bind f, p b) : forallᵐ a ∂m, forallᵐ b ∂f 
a, p b
参数：hf : AEMeasurable f m；h : forallᵐ b ∂m.bind f, p b。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `MeasureTheory.ae_of_ae_map`：ae_of_ae_map {f : α -> β} (hf : AEMeasurable
 f μ) {p : β -> Prop} (h : forallᵐ y ∂μ.map f, p y) : forallᵐ x ∂μ, p (f x)
· 使用定理 `MeasureTheory.Measure.ae_ae_of_ae_join`：ae_ae_of_ae_join {m : Measure (M
easure α)} {p : α -> Prop} (h : forallᵐ a ∂m.join, p a) : forallᵐ μ ∂m, forallᵐ 
a ∂μ, p a
-/
theorem ae_ae_of_ae_bind {m : Measure α} {f : α → Measure β} {p : β → Prop} (hf : AEMeasurable f m)
    (h : ∀ᵐ b ∂m.bind f, p b) : ∀ᵐ a ∂m, ∀ᵐ b ∂f a, p b :=
  ae_of_ae_map hf <| ae_ae_of_ae_join h
/-
**MeasureTheory.Measure._root_.AEMeasurable.ae_of_bind** 是 Mathlib 中的一个定理，位于命名空间
 `MeasureTheory.Measure`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.AEMeasurable.ae_of_bind {γ : Type*} {_ : MeasurableSpace γ} {m : Measure α}
    {f : α → Measure β} {g : β → γ} (hf : AEMeasurable f m) (hg : AEMeasurable g (m.bind f)) :
    ∀ᵐ a ∂m, AEMeasurable g (f a) :=
  ae_of_ae_map hf hg.ae_of_join
/-
**MeasureTheory.Measure.bind_congr_right** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheor
y.Measure`。
形式化陈述：bind_congr_right {μ : Measure α} {f g : α -> Measure β} (h : f =ᵐ[μ] g) : 
μ.bind f = μ.bind g
参数：h : f =ᵐ[μ] g。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.Measure.map_congr`：map_congr {f g : α -> β} (h : f =ᵐ[μ] g
) : Measure.map f μ = Measure.map g μ
-/
theorem bind_congr_right {μ : Measure α} {f g : α → Measure β} (h : f =ᵐ[μ] g) :
    μ.bind f = μ.bind g :=
  congrArg join <| map_congr h

@[simp]
/-
**MeasureTheory.Measure.bind_const** 是 Mathlib 中的一个引理，位于命名空间 `MeasureTheory.Meas
ure`。
形式化陈述：bind_const {m : Measure α} {ν : Measure β} : m.bind (fun _ => ν) = m Set.u
niv • ν
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `MeasureTheory.Measure.map_const`：map_const (μ : Measure α) (c : β) : μ.m
ap (fun _ => c) = (μ Set.univ) • dirac c
· 使用定理 `MeasureTheory.Measure.join_smul`：join_smul {R : Type*} [SMul R Real>=0∞]
 [IsScalarTower R Real>=0∞ Real>=0∞] (c : R) (m : Measure (Measure α)) : (c • m)
.join = c • m.join
· 使用定理 `MeasureTheory.Measure.join_dirac`：join_dirac (μ : Measure α) : join (dir
ac μ) = μ
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma bind_const {m : Measure α} {ν : Measure β} : m.bind (fun _ ↦ ν) = m Set.univ • ν := by
  simp [bind]
/-
**MeasureTheory.Measure.bind_zero_right'** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheor
y.Measure`。
形式化陈述：bind_zero_right' (m : Measure α) : bind m (fun _ => 0 : α -> Measure β) = 
0
参数：m : Measure α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用引理 `MeasureTheory.Measure.bind_const`：bind_const {m : Measure α} {ν : Measur
e β} : m.bind (fun _ => ν) = m Set.univ • ν
· 使用定理 `smul_zero`：smul_zero (a : M) : a • (0 : A) = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem bind_zero_right' (m : Measure α) : bind m (fun _ => 0 : α → Measure β) = 0 := by simp

@[simp]
/-
**MeasureTheory.Measure.bind_zero_right** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory
.Measure`。
形式化陈述：bind_zero_right (m : Measure α) : bind m (0 : α -> Measure β) = 0
参数：m : Measure α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.bind_zero_right'`：bind_zero_right' (m : Measure α)
 : bind m (fun _ => 0 : α -> Measure β) = 0
-/
theorem bind_zero_right (m : Measure α) : bind m (0 : α → Measure β) = 0 := bind_zero_right' m

@[fun_prop]
/-
**MeasureTheory.Measure.measurable_bind'** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheor
y.Measure`。
形式化陈述：measurable_bind' {g : α -> Measure β} (hg : Measurable g) : Measurable fun
 m : Measure α => bind m g
参数：hg : Measurable g。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Measurable.comp`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {x : Mea
surableSpace α} {x_1 : MeasurableSpace β}   {x_2 : MeasurableSpace γ} {g : β → γ
} {f …
· 使用定理 `MeasureTheory.Measure.measurable_join`：measurable_join : Measurable (joi
n : Measure (Measure α) -> Measure α)
· 使用定理 `MeasureTheory.Measure.measurable_map`：measurable_map (f : α -> β) (hf : 
Measurable f) : Measurable fun μ : Measure α => map f μ
-/
theorem measurable_bind' {g : α → Measure β} (hg : Measurable g) :
    Measurable fun m : Measure α => bind m g :=
  measurable_join.comp (measurable_map _ hg)
/-
**MeasureTheory.Measure.aemeasurable_bind** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheo
ry.Measure`。
形式化陈述：aemeasurable_bind {g : α -> Measure β} {m : Measure (Measure α)} (hg : AEM
easurable g m.join) : AEMeasurable (bind · g) m
参数：Measure α；hg : AEMeasurable g m.join。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `MeasureTheory.Measure.measurable_bind'`：measurable_bind' {g : α -> Measu
re β} (hg : Measurable g) : Measurable fun m : Measure α => bind m g
· 使用定理 `Filter.Eventually.mono`：∀ {α : Type u} {p q : α → Prop} {f : Filter α}, 
(∀ᶠ (x : α) in f, p x) → (∀ (x : α), p x → q x) → ∀ᶠ (x : α) in f, q x
· 使用定理 `MeasureTheory.Measure.ae_ae_of_ae_join`：ae_ae_of_ae_join {m : Measure (M
easure α)} {p : α -> Prop} (h : forallᵐ a ∂m.join, p a) : forallᵐ μ ∂m, forallᵐ 
a ∂μ, p a
· 使用定理 `MeasureTheory.Measure.bind_congr_right`：bind_congr_right {μ : Measure α}
 {f g : α -> Measure β} (h : f =ᵐ[μ] g) : μ.bind f = μ.bind g
-/
theorem aemeasurable_bind {g : α → Measure β} {m : Measure (Measure α)}
    (hg : AEMeasurable g m.join) : AEMeasurable (bind · g) m :=
  let ⟨f, hfm, hf⟩ := hg
  ⟨(bind · f), measurable_bind' hfm, (ae_ae_of_ae_join hf).mono fun _ ↦ bind_congr_right⟩
/-
**MeasureTheory.Measure.bind_sum** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.Measur
e`。
形式化陈述：bind_sum {ι : Type*} (m : ι -> Measure α) (f : α -> Measure β) (h : AEMeas
urable f (sum fun i => m i)) : (sum fun (i : ι) => m i).bind f = sum fun (i : ι)
 => (m i).bind f
参数：m : ι -> Measure α；f : α -> Measure β；h : AEMeasurable f (sum fun i => m i)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `MeasureTheory.Measure.map_sum`：map_sum {ι : Type*} {m : ι -> Measure α} 
{f : α -> β} (hf : AEMeasurable f (Measure.sum m)) : Measure.map f (Measure.sum 
m) = Measure.sum (f…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用引理 `MeasureTheory.Measure.join_sum`：join_sum {ι : Type*} (m : ι -> Measure (
Measure α)) : (sum m).join = sum fun (i : ι) => (m i).join
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem bind_sum {ι : Type*} (m : ι → Measure α) (f : α → Measure β)
    (h : AEMeasurable f (sum fun i => m i)) :
    (sum fun (i : ι) ↦ m i).bind f = sum fun (i : ι) ↦ (m i).bind f := by
  simp_rw [bind, map_sum h, join_sum]
/-
**MeasureTheory.Measure.bind_smul** 是 Mathlib 中的一个引理，位于命名空间 `MeasureTheory.Measu
re`。
形式化陈述：bind_smul {R : Type*} [SMul R Real>=0∞] [IsScalarTower R Real>=0∞ Real>=0∞
] (c : R) (m : Measure α) (f : α -> Measure β) : (c • m).bind f = c • (m.bind f)
参数：c : R；m : Measure α；f : α -> Measure β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.Measure.map_smul`：∀ {α : Type u_1} {β : Type u_2} {mα : Me
asurableSpace α} {mβ : MeasurableSpace β} {R : Type u_4} [inst : SMul R ENNReal]
   [inst_1 : IsScala…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `MeasureTheory.Measure.join_smul`：join_smul {R : Type*} [SMul R Real>=0∞]
 [IsScalarTower R Real>=0∞ Real>=0∞] (c : R) (m : Measure (Measure α)) : (c • m)
.join = c • m.join
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma bind_smul {R : Type*} [SMul R ℝ≥0∞] [IsScalarTower R ℝ≥0∞ ℝ≥0∞] (c : R) (m : Measure α)
    (f : α → Measure β) : (c • m).bind f = c • (m.bind f) := by
  simp_rw [bind, Measure.map_smul, join_smul]
/-
**MeasureTheory.Measure.lintegral_bind** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.
Measure`。
形式化陈述：lintegral_bind {m : Measure α} {μ : α -> Measure β} {f : β -> Real>=0∞} (h
μ : AEMeasurable μ m) (hf : AEMeasurable f (bind m μ)) : ∫⁻ x, f x ∂bind m μ = ∫
⁻ a, ∫⁻ x, f x ∂μ a ∂m
参数：hμ : AEMeasurable μ m；hf : AEMeasurable f (bind m μ)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `MeasureTheory.Measure.lintegral_join`：lintegral_join {m : Measure (Measu
re α)} {f : α -> Real>=0∞} (hf : AEMeasurable f (join m)) : ∫⁻ x, f x ∂join m = 
∫⁻ μ, ∫⁻ x, f x ∂μ ∂m
· 使用定理 `MeasureTheory.lintegral_map'`：lintegral_map' {f : β -> Real>=0∞} {g : α 
-> β} (hf : AEMeasurable f (Measure.map g μ)) (hg : AEMeasurable g μ) : ∫⁻ a, f 
a ∂Measure.map g μ…
· 使用定理 `MeasureTheory.Measure.aemeasurable_lintegral`：aemeasurable_lintegral {m 
: Measure (Measure α)} {f : α -> Real>=0∞} (h : AEMeasurable f m.join) : AEMeasu
rable (fun μ => ∫⁻ a, f a ∂μ) m
-/
theorem lintegral_bind {m : Measure α} {μ : α → Measure β} {f : β → ℝ≥0∞} (hμ : AEMeasurable μ m)
    (hf : AEMeasurable f (bind m μ)) : ∫⁻ x, f x ∂bind m μ = ∫⁻ a, ∫⁻ x, f x ∂μ a ∂m :=
  (lintegral_join hf).trans (lintegral_map' (aemeasurable_lintegral hf) hμ)
/-
**MeasureTheory.Measure.lintegral_bind_le** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheo
ry.Measure`。
形式化陈述：lintegral_bind_le (f : β -> Real>=0∞) (m : Measure α) (μ : α -> Measure β)
 : ∫⁻ x, f x ∂bind m μ <= ∫⁻ a, ∫⁻ x, f x ∂μ a ∂m
参数：f : β -> Real>=0∞；m : Measure α；μ : α -> Measure β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `MeasureTheory.Measure.lintegral_join_le`：lintegral_join_le (f : α -> Rea
l>=0∞) (m : Measure (Measure α)) : ∫⁻ x, f x ∂join m <= ∫⁻ μ, ∫⁻ x, f x ∂μ ∂m
· 使用定理 `MeasureTheory.lintegral_map_le`：lintegral_map_le (f : β -> Real>=0∞) (g 
: α -> β) : ∫⁻ a, f a ∂Measure.map g μ <= ∫⁻ a, f (g a) ∂μ
-/
theorem lintegral_bind_le (f : β → ℝ≥0∞) (m : Measure α) (μ : α → Measure β) :
    ∫⁻ x, f x ∂bind m μ ≤ ∫⁻ a, ∫⁻ x, f x ∂μ a ∂m :=
  (lintegral_join_le _ _).trans (lintegral_map_le _ _)
/-
**MeasureTheory.Measure.bind_bind** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.Measu
re`。
形式化陈述：bind_bind {γ} [MeasurableSpace γ] {m : Measure α} {f : α -> Measure β} {g 
: β -> Measure γ} (hf : AEMeasurable f m) (hg : AEMeasurable g (m.bind f)) : bin
d (bind m f) g = bind m fun a => bind (f a) g
参数：hf : AEMeasurable f m；hg : AEMeasurable g (m.bind f)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.ext`：ext (h : forall s, MeasurableSet s -> μ₁ s = 
μ₂ s) : μ₁ = μ₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.Measure.bind_apply`：bind_apply {m : Measure α} {f : α -> M
easure β} {s : Set β} (hs : MeasurableSet s) (hf : AEMeasurable f m) : bind m f 
s = ∫⁻ a, f a s ∂m
· 使用定理 `MeasureTheory.Measure.lintegral_bind`：lintegral_bind {m : Measure α} {μ 
: α -> Measure β} {f : β -> Real>=0∞} (hμ : AEMeasurable μ m) (hf : AEMeasurable
 f (bind m μ)) : ∫⁻ x, f x…
· 使用定理 `Measurable.comp_aemeasurable`：Measurable.comp_aemeasurable [MeasurableSp
ace δ] {f : α -> δ} {g : δ -> β} (hg : Measurable g) (hf : AEMeasurable f μ) : A
EMeasurable (g ∘ f…
· 使用定理 `MeasureTheory.Measure.measurable_coe`：measurable_coe {s : Set α} (hs : M
easurableSet s) : Measurable fun μ : Measure α => μ s
· 使用定理 `AEMeasurable.comp_aemeasurable`：comp_aemeasurable {f : α -> δ} {g : δ ->
 β} (hg : AEMeasurable g (μ.map f)) (hf : AEMeasurable f μ) : AEMeasurable (g ∘ 
f) μ
· 使用定理 `MeasureTheory.Measure.aemeasurable_bind`：aemeasurable_bind {g : α -> Mea
sure β} {m : Measure (Measure α)} (hg : AEMeasurable g m.join) : AEMeasurable (b
ind · g) m
· 使用定理 `MeasureTheory.lintegral_congr_ae`：lintegral_congr_ae {f g : α -> Real>=0
∞} (h : f =ᵐ[μ] g) : ∫⁻ a, f a ∂μ = ∫⁻ a, g a ∂μ
· 使用定理 `Filter.Eventually.mono`：∀ {α : Type u} {p q : α → Prop} {f : Filter α}, 
(∀ᶠ (x : α) in f, p x) → (∀ (x : α), p x → q x) → ∀ᶠ (x : α) in f, q x
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `AEMeasurable.ae_of_bind`：∀ {α : Type u_1} {β : Type u_2} {mα : Measurabl
eSpace α} {mβ : MeasurableSpace β} {γ : Type u_3} {x : MeasurableSpace γ}   {m :
 MeasureTheor…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem bind_bind {γ} [MeasurableSpace γ] {m : Measure α} {f : α → Measure β} {g : β → Measure γ}
    (hf : AEMeasurable f m) (hg : AEMeasurable g (m.bind f)) :
    bind (bind m f) g = bind m fun a => bind (f a) g := by
  ext1 s hs
  rw [bind_apply hs hg, lintegral_bind hf, bind_apply hs]
  · exact lintegral_congr_ae <| (hf.ae_of_bind hg).mono fun a ha ↦ .symm <| bind_apply hs ha
  · exact (aemeasurable_bind hg).comp_aemeasurable hf
  · exact (measurable_coe hs).comp_aemeasurable hg

@[simp]
/-
**MeasureTheory.Measure.dirac_bind** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.Meas
ure`。
形式化陈述：dirac_bind {f : α -> Measure β} (hf : Measurable f) (a : α) : bind (dirac 
a) f = f a
参数：hf : Measurable f；a : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.Measure.map_dirac'`：map_dirac' {f : α -> β} (hf : Measurab
le f) (a : α) : (dirac a).map f = dirac (f a)
· 使用定理 `MeasureTheory.Measure.join_dirac`：join_dirac (μ : Measure α) : join (dir
ac μ) = μ
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem dirac_bind {f : α → Measure β} (hf : Measurable f) (a : α) : bind (dirac a) f = f a := by
  simp [bind, map_dirac' hf]

@[simp]
/-
**MeasureTheory.Measure.bind_dirac** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.Meas
ure`。
形式化陈述：bind_dirac {m : Measure α} : bind m dirac = m
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.ext`：ext (h : forall s, MeasurableSet s -> μ₁ s = 
μ₂ s) : μ₁ = μ₂
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.Measure.bind_apply`：bind_apply {m : Measure α} {f : α -> M
easure β} {s : Set β} (hs : MeasurableSet s) (hf : AEMeasurable f m) : bind m f 
s = ∫⁻ a, f a s ∂m
· 使用定理 `Measurable.aemeasurable`：Measurable.aemeasurable (h : Measurable f) : AE
Measurable f μ
· 使用定理 `MeasureTheory.Measure.measurable_dirac`：measurable_dirac : Measurable (M
easure.dirac : α -> Measure α)
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `MeasureTheory.Measure.dirac_apply'`：dirac_apply' (a : α) (hs : Measurabl
eSet s) : dirac a s = s.indicator 1 a
· 使用定理 `MeasureTheory.lintegral_indicator`：lintegral_indicator {s : Set α} (hs :
 MeasurableSet s) (f : α -> Real>=0∞) : ∫⁻ a, s.indicator f a ∂μ = ∫⁻ a in s, f 
a ∂μ
· 使用定理 `MeasureTheory.lintegral_one`：lintegral_one : ∫⁻ _, (1 : Real>=0∞) ∂μ = μ
 univ
· 使用定理 `MeasureTheory.Measure.restrict_apply`：restrict_apply (ht : MeasurableSet
 t) : μ.restrict s t = μ (t inter s)
· 使用定理 `Set.univ_inter`：univ_inter (a : Set α) : univ inter a = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem bind_dirac {m : Measure α} : bind m dirac = m := by
  ext1 s hs
  simp only [bind_apply hs measurable_dirac.aemeasurable, dirac_apply' _ hs, lintegral_indicator hs,
    Pi.one_apply, lintegral_one, restrict_apply, MeasurableSet.univ, univ_inter]

@[simp]
/-
**MeasureTheory.Measure.bind_dirac_eq_map** 是 Mathlib 中的一个引理，位于命名空间 `MeasureTheo
ry.Measure`。
形式化陈述：bind_dirac_eq_map (m : Measure α) {f : α -> β} (hf : Measurable f) : m.bin
d (fun x => Measure.dirac (f x)) = m.map f
参数：m : Measure α；hf : Measurable f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.Measure.bind_dirac`：bind_dirac {m : Measure α} : bind m di
rac = m
· 使用定理 `MeasureTheory.Measure.bind.eq_1`：∀ {α : Type u_1} {β : Type u_2} {mα : M
easurableSpace α} {mβ : MeasurableSpace β} (m : MeasureTheory.Measure α)   (f : 
α → MeasureTheory.Mea…
· 使用定理 `MeasureTheory.Measure.map_map`：map_map {g : β -> γ} {f : α -> β} (hg : M
easurable g) (hf : Measurable f) : (μ.map f).map g = μ.map (g ∘ f)
· 使用定理 `MeasureTheory.Measure.measurable_dirac`：measurable_dirac : Measurable (M
easure.dirac : α -> Measure α)
· 使用定理 `Function.comp_def`：∀ {α : Sort u_1} {β : Sort u_2} {δ : Sort u_3} (f : β
 → δ) (g : α → β), f ∘ g = fun x => f (g x)
-/
lemma bind_dirac_eq_map (m : Measure α) {f : α → β} (hf : Measurable f) :
    m.bind (fun x ↦ Measure.dirac (f x)) = m.map f := by
  rw [← bind_dirac (m := m.map f), bind, bind, map_map, Function.comp_def]
  exacts [measurable_dirac, hf]
/-
**MeasureTheory.Measure.join_eq_bind** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.Me
asure`。
形式化陈述：join_eq_bind (μ : Measure (Measure α)) : join μ = bind μ id
参数：μ : Measure (Measure α)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.Measure.bind.eq_1`：∀ {α : Type u_1} {β : Type u_2} {mα : M
easurableSpace α} {mβ : MeasurableSpace β} (m : MeasureTheory.Measure α)   (f : 
α → MeasureTheory.Mea…
· 使用定理 `MeasureTheory.Measure.map_id`：map_id : map id μ = μ
-/
theorem join_eq_bind (μ : Measure (Measure α)) : join μ = bind μ id := by rw [bind, map_id]
/-
**MeasureTheory.Measure.join_map_map** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.Me
asure`。
形式化陈述：join_map_map {f : α -> β} (hf : Measurable f) (μ : Measure (Measure α)) : 
join (map (map f) μ) = map f (join μ)
参数：hf : Measurable f；μ : Measure (Measure α)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.ext`：ext (h : forall s, MeasurableSet s -> μ₁ s = 
μ₂ s) : μ₁ = μ₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.Measure.join_apply`：join_apply {m : Measure (Measure α)} {
s : Set α} (hs : MeasurableSet s) : join m s = ∫⁻ μ, μ s ∂m
· 使用定理 `MeasureTheory.Measure.map_apply`：map_apply (hf : Measurable f) {s : Set 
β} (hs : MeasurableSet s) : μ.map f s = μ (f ⁻¹' s)
· 使用定理 `MeasureTheory.lintegral_map`：lintegral_map {f : β -> Real>=0∞} {g : α ->
 β} (hf : Measurable f) (hg : Measurable g) : ∫⁻ a, f a ∂map g μ = ∫⁻ a, f (g a)
 ∂μ
· 使用定理 `MeasureTheory.Measure.measurable_coe`：measurable_coe {s : Set α} (hs : M
easurableSet s) : Measurable fun μ : Measure α => μ s
· 使用定理 `MeasureTheory.Measure.measurable_map`：measurable_map (f : α -> β) (hf : 
Measurable f) : Measurable fun μ : Measure α => map f μ
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem join_map_map {f : α → β} (hf : Measurable f) (μ : Measure (Measure α)) :
    join (map (map f) μ) = map f (join μ) := by
  ext1 s hs
  rw [join_apply hs, map_apply hf hs, join_apply (hf hs),
    lintegral_map (measurable_coe hs) (measurable_map f hf)]
  simp_rw [map_apply hf hs]
/-
**MeasureTheory.Measure.join_map_join** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.M
easure`。
形式化陈述：join_map_join (μ : Measure (Measure (Measure α))) : join (map join μ) = jo
in (join μ)
参数：μ : Measure (Measure (Measure α))。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.Measure.join_eq_bind`：join_eq_bind (μ : Measure (Measure α
)) : join μ = bind μ id
· 使用定理 `MeasureTheory.Measure.bind_bind`：bind_bind {γ} [MeasurableSpace γ] {m : 
Measure α} {f : α -> Measure β} {g : β -> Measure γ} (hf : AEMeasurable f m) (hg
 : AEMeasurable g (m.…
· 使用定理 `aemeasurable_id`：aemeasurable_id : AEMeasurable id μ
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
-/
theorem join_map_join (μ : Measure (Measure (Measure α))) : join (map join μ) = join (join μ) := by
  change bind μ join = join (join μ)
  rw [join_eq_bind, join_eq_bind, bind_bind aemeasurable_id aemeasurable_id]
  apply congr_arg (bind μ)
  funext ν
  exact join_eq_bind ν
/-
**MeasureTheory.Measure.join_map_dirac** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.
Measure`。
形式化陈述：join_map_dirac (μ : Measure α) : join (map dirac μ) = μ
参数：μ : Measure α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.bind_dirac`：bind_dirac {m : Measure α} : bind m di
rac = m
-/
theorem join_map_dirac (μ : Measure α) : join (map dirac μ) = μ := bind_dirac

end Measure

end MeasureTheory

