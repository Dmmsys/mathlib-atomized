/-
Copyright (c) 2023 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
module

public import Mathlib.Geometry.Manifold.PartitionOfUnity
public import Mathlib.MeasureTheory.Function.AEEqOfIntegral

/-!
# Functions which vanish as distributions vanish as functions

In a finite-dimensional normed real vector space endowed with a Borel measure, consider a locally
integrable function whose integral against all compactly supported smooth functions vanishes. Then
the function is almost everywhere zero.
This is proved in `ae_eq_zero_of_integral_contDiff_smul_eq_zero`.

A version for two functions having the same integral when multiplied by smooth compactly supported
functions is also given in `ae_eq_of_integral_contDiff_smul_eq`.

These are deduced from the same results on finite-dimensional real manifolds, given respectively
as `ae_eq_zero_of_integral_contMDiff_smul_eq_zero` and `ae_eq_of_integral_contMDiff_smul_eq`.
-/

public section

open MeasureTheory Filter Metric Function Set TopologicalSpace

open scoped Topology Manifold ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

section Manifold

variable {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [MeasurableSpace M] [BorelSpace M] [T2Space M]
  {f f' : M → F} {μ : Measure M}

/-- If a locally integrable function `f` on a finite-dimensional real manifold has zero integral
when multiplied by any smooth compactly supported function, then `f` vanishes almost everywhere. -/
/-
**ae_eq_zero_of_integral_contMDiff_smul_eq_zero** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ae_eq_zero_of_integral_contMDiff_smul_eq_zero [SigmaCompactSpace M] (hf : 
LocallyIntegrable f μ) (h : forall g : M -> Real, CMDiff ∞ g -> HasCompactSuppor
t g -> ∫ x, g x • f x ∂μ = 0) : forallᵐ x ∂μ, f x = 0
参数：hf : LocallyIntegrable f μ；h : forall g : M -> Real, CMDiff ∞ g -> HasCompact
Support g -> ∫ x, g x • f x ∂μ = 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ModelWithCorners.locallyCompactSpace`：∀ {𝕜 : Type u_1} [inst : Nontrivia
llyNormedField 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : Nor
medSpace 𝕜 E] {H : Type u_…
· 使用定理 `locallyCompact_of_proper`：∀ {α : Type u} [inst : PseudoMetricSpace α] [P
roperSpace α], LocallyCompactSpace α
· 使用定理 `FiniteDimensional.proper_real`：∀ (E : Type u) [inst : NormedAddCommGroup
 E] [inst_1 : NormedSpace ℝ E] [FiniteDimensional ℝ E], ProperSpace E
· 使用定理 `ChartedSpace.locallyCompactSpace`：ChartedSpace.locallyCompactSpace [Loca
llyCompactSpace H] : LocallyCompactSpace M
· 使用定理 `ModelWithCorners.secondCountableTopology`：∀ {𝕜 : Type u_1} [inst : Nontr
iviallyNormedField 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 :
 NormedSpace 𝕜 E] {H : Type u_…
· 使用定理 `secondCountable_of_proper`：∀ {α : Type u} [inst : PseudoMetricSpace α] [
ProperSpace α], SecondCountableTopology α
· 使用定理 `ChartedSpace.secondCountable_of_sigmaCompact`：ChartedSpace.secondCountab
le_of_sigmaCompact [SecondCountableTopology H] [SigmaCompactSpace M] : SecondCou
ntableTopology M
· 使用定理 `TopologicalSpace.PseudoMetrizableSpace.toMetrizableSpace`：∀ {X : Type u_
2} [inst : TopologicalSpace X] [T0Space X] [h : TopologicalSpace.PseudoMetrizabl
eSpace X],   TopologicalSpace.MetrizableSpace …
· 使用定理 `T1Space.t0Space`：∀ {X : Type u_1} [inst : TopologicalSpace X] [T1Space X
], T0Space X
· 使用定理 `T2Space.t1Space`：∀ {X : Type u_1} [inst : TopologicalSpace X] [T2Space X
], T1Space X
· 使用定理 `TopologicalSpace.PseudoMetrizableSpace.of_regularSpace_secondCountableTo
pology`：∀ (X : Type u_1) [inst : TopologicalSpace X] [RegularSpace X] [SecondCou
ntableTopology X],   TopologicalSpace.PseudoMetrizableSpace X
· 使用定理 `instRegularSpaceOfWeaklyLocallyCompactSpaceOfR1Space`：∀ {X : Type u_1} [
inst : TopologicalSpace X] [WeaklyLocallyCompactSpace X] [R1Space X], RegularSpa
ce X
· 使用定理 `instWeaklyLocallyCompactSpaceOfLocallyCompactSpace`：∀ {X : Type u_1} [in
st : TopologicalSpace X] [LocallyCompactSpace X], WeaklyLocallyCompactSpace X
· 使用定理 `T2Space.r1Space`：∀ {X : Type u_1} [inst : TopologicalSpace X] [T2Space X
], R1Space X
· 使用引理 `MeasureTheory.ae_eq_zero_of_forall_setIntegral_isCompact_eq_zero'`：ae_eq
_zero_of_forall_setIntegral_isCompact_eq_zero' [SigmaCompactSpace β] [R1Space β]
 {μ : Measure β} {f : β -> E} (hf : LocallyIntegrable f…
· 使用定理 `instR1Space`：∀ {X : Type u_1} [inst : TopologicalSpace X] [RegularSpace 
X], R1Space X
· 使用定理 `TopologicalSpace.PseudoMetrizableSpace.regularSpace`：∀ {X : Type u_2} [i
nst : TopologicalSpace X] [TopologicalSpace.PseudoMetrizableSpace X], RegularSpa
ce X
· 使用定理 `PseudoEMetricSpace.pseudoMetrizableSpace`：∀ {α : Type u_2} [inst : Pseud
oEMetricSpace α], TopologicalSpace.PseudoMetrizableSpace α
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `IsCompact.exists_isCompact_cthickening`：∀ {α : Type u} [inst : PseudoEMe
tricSpace α] {s : Set α} [LocallyCompactSpace α],   IsCompact s → ∃ δ, 0 < δ ∧ I
sCompact (Metric.cthickening…
· 使用定理 `exists_seq_strictAnti_tendsto'`：exists_seq_strictAnti_tendsto' [DenselyO
rdered α] [FirstCountableTopology α] {x y : α} (hy : x < y) : exists u : Nat -> 
α, StrictAnti u ∧ (f…
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
· 使用定理 `TopologicalSpace.PseudoMetrizableSpace.firstCountableTopology`：∀ {X : Ty
pe u_2} [inst : TopologicalSpace X] [h : TopologicalSpace.PseudoMetrizableSpace 
X], FirstCountableTopology X
· 使用定理 `Metric.thickening_subset_cthickening_of_le`：thickening_subset_cthickenin
g_of_le {δ₁ δ₂ : Real} (hle : δ₁ <= δ₂) (E : Set α) : thickening δ₁ E subseteq c
thickening δ₂ E
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
（共 93 条，此处仅展示前 30 条）

--- 原说明 ---
If a locally integrable function `f` on a finite-dimensional real manifold has z
ero integral
when multiplied by any smooth compactly supported function, then `f` vanishes al
most everywhere.
-/
theorem ae_eq_zero_of_integral_contMDiff_smul_eq_zero [SigmaCompactSpace M]
    (hf : LocallyIntegrable f μ)
    (h : ∀ g : M → ℝ, CMDiff ∞ g → HasCompactSupport g → ∫ x, g x • f x ∂μ = 0) :
    ∀ᵐ x ∂μ, f x = 0 := by
  -- record topological properties of `M`
  have := I.locallyCompactSpace
  have := ChartedSpace.locallyCompactSpace H M
  have := I.secondCountableTopology
  have := ChartedSpace.secondCountable_of_sigmaCompact H M
  let _ : MetricSpace M := TopologicalSpace.metrizableSpaceMetric M
  -- it suffices to show that the integral of the function vanishes on any compact set `s`
  apply ae_eq_zero_of_forall_setIntegral_isCompact_eq_zero' hf (fun s hs ↦ Eq.symm ?_)
  obtain ⟨δ, δpos, hδ⟩ : ∃ δ, 0 < δ ∧ IsCompact (cthickening δ s) := hs.exists_isCompact_cthickening
  -- choose a sequence of smooth functions `gₙ` equal to `1` on `s` and vanishing outside of the
  -- `uₙ`-neighborhood of `s`, where `uₙ` tends to zero. Then each integral `∫ gₙ f` vanishes,
  -- and by dominated convergence these integrals converge to `∫ x in s, f`.
  obtain ⟨u, -, u_pos, u_lim⟩ : ∃ u, StrictAnti u ∧ (∀ (n : ℕ), u n ∈ Ioo 0 δ)
    ∧ Tendsto u atTop (𝓝 0) := exists_seq_strictAnti_tendsto' δpos
  let v : ℕ → Set M := fun n ↦ thickening (u n) s
  obtain ⟨K, K_compact, vK⟩ : ∃ K, IsCompact K ∧ ∀ n, v n ⊆ K :=
    ⟨_, hδ, fun n ↦ thickening_subset_cthickening_of_le (u_pos n).2.le _⟩
  have : ∀ n, ∃ (g : M → ℝ), support g = v n ∧ CMDiff ∞ g ∧ Set.range g ⊆ Set.Icc 0 1
          ∧ ∀ x ∈ s, g x = 1 := by
    intro n
    rcases exists_contMDiff_support_eq_eq_one_iff I isOpen_thickening hs.isClosed
      (self_subset_thickening (u_pos n).1 s) with ⟨g, g_smooth, g_range, g_supp, hg⟩
    exact ⟨g, g_supp, g_smooth, g_range, fun x hx ↦ (hg x).1 hx⟩
  choose g g_supp g_diff g_range hg using this
  -- main fact: the integral of `∫ gₙ f` tends to `∫ x in s, f`.
  have L : Tendsto (fun n ↦ ∫ x, g n x • f x ∂μ) atTop (𝓝 (∫ x in s, f x ∂μ)) := by
    rw [← integral_indicator hs.measurableSet]
    let bound : M → ℝ := K.indicator (fun x ↦ ‖f x‖)
    have A : ∀ n, AEStronglyMeasurable (fun x ↦ g n x • f x) μ :=
      fun n ↦ (g_diff n).continuous.aestronglyMeasurable.smul hf.aestronglyMeasurable
    have B : Integrable bound μ := by
      rw [integrable_indicator_iff K_compact.measurableSet]
      exact (hf.integrableOn_isCompact K_compact).norm
    have C : ∀ n, ∀ᵐ x ∂μ, ‖g n x • f x‖ ≤ bound x := by
      intro n
      filter_upwards with x
      rw [norm_smul]
      refine le_indicator_apply (fun _ ↦ ?_) (fun hxK ↦ ?_)
      · have : ‖g n x‖ ≤ 1 := by
          have := g_range n (mem_range_self (f := g n) x)
          rw [Real.norm_of_nonneg this.1]
          exact this.2
        exact mul_le_of_le_one_left (norm_nonneg _) this
      · have : g n x = 0 := by rw [← notMem_support, g_supp]; contrapose hxK; exact vK n hxK
        simp [this]
    have D : ∀ᵐ x ∂μ, Tendsto (fun n => g n x • f x) atTop (𝓝 (s.indicator f x)) := by
      filter_upwards with x
      by_cases hxs : x ∈ s
      · have : ∀ n, g n x = 1 := fun n ↦ hg n x hxs
        simp [this, indicator_of_mem hxs f]
      · simp_rw [indicator_of_notMem hxs f]
        apply tendsto_const_nhds.congr'
        suffices H : ∀ᶠ n in atTop, g n x = 0 by
          filter_upwards [H] with n hn using by simp [hn]
        obtain ⟨ε, εpos, hε⟩ : ∃ ε, 0 < ε ∧ x ∉ thickening ε s := by
          rw [← hs.isClosed.closure_eq, closure_eq_iInter_thickening s] at hxs
          simpa using hxs
        filter_upwards [(tendsto_order.1 u_lim).2 _ εpos] with n hn
        rw [← notMem_support, g_supp]
        contrapose hε
        exact thickening_mono hn.le s hε
    exact tendsto_integral_of_dominated_convergence bound A B C D
  -- deduce that `∫ x in s, f = 0` as each integral `∫ gₙ f` vanishes by assumption
  have : ∀ n, ∫ x, g n x • f x ∂μ = 0 := by
    refine fun n ↦ h _ (g_diff n) ?_
    apply HasCompactSupport.of_support_subset_isCompact K_compact
    simpa [g_supp] using vK n
  simpa [this] using L

-- An instance with keys containing `Opens`
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (U : Opens M) : BorelSpace U := inferInstanceAs (BorelSpace (U : Set M))

/-- If a function `f` locally integrable on an open subset `U` of a finite-dimensional real
  manifold has zero integral when multiplied by any smooth function compactly supported
  in `U`, then `f` vanishes almost everywhere in `U`. -/
/-
**IsOpen.ae_eq_zero_of_integral_contMDiff_smul_eq_zero'** 是 Mathlib 中的一个定理，位于命名空
间 ``。
形式化陈述：IsOpen.ae_eq_zero_of_integral_contMDiff_smul_eq_zero' {U : Set M} (hU : Is
Open U) (hSig : IsSigmaCompact U) (hf : LocallyIntegrableOn f U μ) (h : forall g
 : M -> Real, CMDiff ∞ g -> HasCompactSupport g -> tsupport g subseteq U -> ∫ x,
 g x • f x ∂μ = 0) : forallᵐ x ∂μ, x in U -> f x = 0
参数：hU : IsOpen U；hSig : IsSigmaCompact U；hf : LocallyIntegrableOn f U μ；h : fora
ll g : M -> Real, CMDiff ∞ g -> HasCompactSupport g -> tsupport g subseteq U -> 
∫ x, g x • f x ∂μ = 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsOpen.measurableSet`：IsOpen.measurableSet (h : IsOpen s) : MeasurableSe
t s
· 使用定理 `BorelSpace.opensMeasurable`：∀ {α : Type u_6} [inst : TopologicalSpace α]
 [inst_1 : MeasurableSpace α] [BorelSpace α], OpensMeasurableSpace α
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.ae_restrict_iff'`：ae_restrict_iff'₀ {p : α -> Prop} (hs : 
NullMeasurableSet s μ) : (forallᵐ x ∂μ.restrict s, p x) ↔ forallᵐ x ∂μ, x in s -
> p x
· 使用定理 `ae_restrict_iff_subtype`：ae_restrict_iff_subtype {m0 : MeasurableSpace α
} {μ : Measure α} {s : Set α} (hs : MeasurableSet s) {p : α -> Prop} : (forallᵐ 
x ∂μ.restrict…
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `isSigmaCompact_iff_sigmaCompactSpace`：isSigmaCompact_iff_sigmaCompactSpa
ce {s : Set X} : IsSigmaCompact s ↔ SigmaCompactSpace s
· 使用定理 `ae_eq_zero_of_integral_contMDiff_smul_eq_zero`：ae_eq_zero_of_integral_co
ntMDiff_smul_eq_zero [SigmaCompactSpace M] (hf : LocallyIntegrable f μ) (h : for
all g : M -> Real, CMDiff ∞ g -> Ha…
· 使用定理 `TopologicalSpace.Opens.instIsManifoldSubtypeMem`：∀ {𝕜 : Type u_1} [inst 
: NontriviallyNormedField 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [i
nst_2 : NormedSpace 𝕜 E] {H : Type u_…
· 使用定理 `instBorelSpaceSubtypeMemOpens`：∀ {M : Type u_4} [inst : TopologicalSpace
 M] [inst_1 : MeasurableSpace M] [BorelSpace M] (U : TopologicalSpace.Opens M), 
  BorelSpace ↥U
· 使用定理 `instT2SpaceSubtype`：∀ {X : Type u_1} [inst : TopologicalSpace X] {p : X 
→ Prop} [T2Space X], T2Space (Subtype p)
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `MeasureTheory.locallyIntegrable_comap`：locallyIntegrable_comap (hs : Mea
surableSet s) : LocallyIntegrable (fun x : s => f x) (μ.comap Subtype.val) ↔ Loc
allyIntegrableOn f s μ
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Function.Injective.extend_apply`：∀ {α : Sort u_1} {β : Sort u_2} {γ : So
rt u_3} {f : α → β},   Function.Injective f → ∀ (g : α → γ) (e' : β → γ) (a : α)
, Function.extend f g…
· 使用定理 `Subtype.val_injective`：∀ {α : Sort u_1} {p : α → Prop}, Function.Injecti
ve Subtype.val
· 使用定理 `MeasureTheory.integral_subtype_comap`：integral_subtype_comap {α} [Measur
ableSpace α] {μ : Measure α} {s : Set α} (hs : MeasurableSet s) (f : α -> G) : ∫
 x : s, f (x : α) ∂(Measur…
· 使用定理 `MeasureTheory.setIntegral_eq_integral_of_forall_compl_eq_zero`：setIntegr
al_eq_integral_of_forall_compl_eq_zero (h : forall x, x ∉ s -> f x = 0) : ∫ x in
 s, f x ∂μ = ∫ x, f x ∂μ
· 使用定理 `Function.extend_apply'`：extend_apply' (g : α -> γ) (e' : β -> γ) (b : β)
 (hb : ¬exists a, f a = b) : extend f g e' b = e' b
· 使用定理 `mt`：∀ {a b : Prop}, (a → b) → ¬b → ¬a
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `zero_smul`：zero_smul (m : A) : (0 : M₀) • m = 0
· 使用定理 `ContMDiff.extend_zero`：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedField 
𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜 E] {
H : Type u_…
· 使用定理 `HasCompactSupport.extend_zero`：∀ {α : Type u_2} {α' : Type u_3} {β : Typ
e u_4} [inst : TopologicalSpace α] [inst_1 : TopologicalSpace α']   [inst_2 : Ze
ro β] {f : α → β} […
· 使用定理 `continuous_subtype_val`：continuous_subtype_val : Continuous (@Subtype.va
l X p)
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `HasCompactSupport.tsupport_extend_zero_subset`：∀ {α : Type u_2} {α' : Ty
pe u_3} {β : Type u_4} [inst : TopologicalSpace α] [inst_1 : TopologicalSpace α'
]   [inst_2 : Zero β] {f : α → β} […
（共 31 条，此处仅展示前 30 条）

--- 原说明 ---
If a function `f` locally integrable on an open subset `U` of a finite-dimension
al real
  manifold has zero integral when multiplied by any smooth function compactly su
pported
  in `U`, then `f` vanishes almost everywhere in `U`.
-/
theorem IsOpen.ae_eq_zero_of_integral_contMDiff_smul_eq_zero' {U : Set M} (hU : IsOpen U)
    (hSig : IsSigmaCompact U) (hf : LocallyIntegrableOn f U μ)
    (h : ∀ g : M → ℝ,
      CMDiff ∞ g → HasCompactSupport g → tsupport g ⊆ U → ∫ x, g x • f x ∂μ = 0) :
    ∀ᵐ x ∂μ, x ∈ U → f x = 0 := by
  have meas_U := hU.measurableSet
  rw [← ae_restrict_iff' meas_U, ae_restrict_iff_subtype meas_U]
  let U : Opens M := ⟨U, hU⟩
  change ∀ᵐ (x : U) ∂_, _
  have : SigmaCompactSpace U := isSigmaCompact_iff_sigmaCompactSpace.mp hSig
  refine ae_eq_zero_of_integral_contMDiff_smul_eq_zero I ?_ fun g g_smth g_supp ↦ ?_
  · exact (locallyIntegrable_comap meas_U).mpr hf
  specialize h (Subtype.val.extend g 0) (g_smth.extend_zero g_supp)
    (g_supp.extend_zero continuous_subtype_val) ((g_supp.tsupport_extend_zero_subset
      continuous_subtype_val).trans <| Subtype.coe_image_subset _ _)
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero (s := U) fun x hx ↦ ?_] at h
  · rw [← integral_subtype_comap] at h
    · simp_rw [Subtype.val_injective.extend_apply] at h; exact h
    · exact meas_U
  rw [Function.extend_apply' _ _ _ (mt _ hx)]
  · apply zero_smul
  · rintro ⟨x, rfl⟩; exact x.2

variable [SigmaCompactSpace M]
/-
**IsOpen.ae_eq_zero_of_integral_contMDiff_smul_eq_zero** 是 Mathlib 中的一个定理，位于命名空间
 ``。
形式化陈述：IsOpen.ae_eq_zero_of_integral_contMDiff_smul_eq_zero {U : Set M} (hU : IsO
pen U) (hf : LocallyIntegrableOn f U μ) (h : forall g : M -> Real, CMDiff ∞ g ->
 HasCompactSupport g -> tsupport g subseteq U -> ∫ x, g x • f x ∂μ = 0) : forall
ᵐ x ∂μ, x in U -> f x = 0
参数：hU : IsOpen U；hf : LocallyIntegrableOn f U μ；h : forall g : M -> Real, CMDiff
 ∞ g -> HasCompactSupport g -> tsupport g subseteq U -> ∫ x, g x • f x ∂μ = 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsOpen.ae_eq_zero_of_integral_contMDiff_smul_eq_zero'`：IsOpen.ae_eq_zero
_of_integral_contMDiff_smul_eq_zero' {U : Set M} (hU : IsOpen U) (hSig : IsSigma
Compact U) (hf : LocallyIntegrableOn f U μ)…
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `isSigmaCompact_iff_sigmaCompactSpace`：isSigmaCompact_iff_sigmaCompactSpa
ce {s : Set X} : IsSigmaCompact s ↔ SigmaCompactSpace s
· 使用定理 `sigmaCompactSpace_of_locallyCompact_secondCountable`：∀ {X : Type u_1} [i
nst : TopologicalSpace X] [LocallyCompactSpace X] [SecondCountableTopology X], S
igmaCompactSpace X
· 使用定理 `IsOpen.locallyCompactSpace`：∀ {X : Type u_1} [inst : TopologicalSpace X]
 [LocallyCompactSpace X] {s : Set X}, IsOpen s → LocallyCompactSpace ↑s
· 使用定理 `ChartedSpace.locallyCompactSpace`：ChartedSpace.locallyCompactSpace [Loca
llyCompactSpace H] : LocallyCompactSpace M
· 使用定理 `ModelWithCorners.locallyCompactSpace`：∀ {𝕜 : Type u_1} [inst : Nontrivia
llyNormedField 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : Nor
medSpace 𝕜 E] {H : Type u_…
· 使用定理 `locallyCompact_of_proper`：∀ {α : Type u} [inst : PseudoMetricSpace α] [P
roperSpace α], LocallyCompactSpace α
· 使用定理 `FiniteDimensional.proper_real`：∀ (E : Type u) [inst : NormedAddCommGroup
 E] [inst_1 : NormedSpace ℝ E] [FiniteDimensional ℝ E], ProperSpace E
· 使用定理 `TopologicalSpace.Subtype.secondCountableTopology`：∀ {α : Type u} [t : To
pologicalSpace α] (s : Set α) [SecondCountableTopology α], SecondCountableTopolo
gy ↑s
· 使用定理 `ChartedSpace.secondCountable_of_sigmaCompact`：ChartedSpace.secondCountab
le_of_sigmaCompact [SecondCountableTopology H] [SigmaCompactSpace M] : SecondCou
ntableTopology M
· 使用定理 `ModelWithCorners.secondCountableTopology`：∀ {𝕜 : Type u_1} [inst : Nontr
iviallyNormedField 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 :
 NormedSpace 𝕜 E] {H : Type u_…
· 使用定理 `secondCountable_of_proper`：∀ {α : Type u} [inst : PseudoMetricSpace α] [
ProperSpace α], SecondCountableTopology α
-/
theorem IsOpen.ae_eq_zero_of_integral_contMDiff_smul_eq_zero {U : Set M} (hU : IsOpen U)
    (hf : LocallyIntegrableOn f U μ)
    (h : ∀ g : M → ℝ,
      CMDiff ∞ g → HasCompactSupport g → tsupport g ⊆ U → ∫ x, g x • f x ∂μ = 0) :
    ∀ᵐ x ∂μ, x ∈ U → f x = 0 :=
  haveI := I.locallyCompactSpace
  haveI := ChartedSpace.locallyCompactSpace H M
  haveI := hU.locallyCompactSpace
  haveI := I.secondCountableTopology
  haveI := ChartedSpace.secondCountable_of_sigmaCompact H M
  hU.ae_eq_zero_of_integral_contMDiff_smul_eq_zero' _
    (isSigmaCompact_iff_sigmaCompactSpace.mpr inferInstance) hf h

/-- If two locally integrable functions on a finite-dimensional real manifold have the same integral
when multiplied by any smooth compactly supported function, then they coincide almost everywhere. -/
/-
**ae_eq_of_integral_contMDiff_smul_eq** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ae_eq_of_integral_contMDiff_smul_eq (hf : LocallyIntegrable f μ) (hf' : Lo
callyIntegrable f' μ) (h : forall (g : M -> Real), CMDiff ∞ g -> HasCompactSuppo
rt g -> ∫ x, g x • f x ∂μ = ∫ x, g x • f' x ∂μ) : forallᵐ x ∂μ, f x = f' x
参数：hf : LocallyIntegrable f μ；hf' : LocallyIntegrable f' μ；h : forall (g : M -> 
Real), CMDiff ∞ g -> HasCompactSupport g -> ∫ x, g x • f x ∂μ = ∫ x, g x • f' x 
∂μ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `ae_eq_zero_of_integral_contMDiff_smul_eq_zero`：ae_eq_zero_of_integral_co
ntMDiff_smul_eq_zero [SigmaCompactSpace M] (hf : LocallyIntegrable f μ) (h : for
all g : M -> Real, CMDiff ∞ g -> Ha…
· 使用定理 `MeasureTheory.LocallyIntegrable.sub`：∀ {X : Type u_1} {E : Type u_6} [in
st : MeasurableSpace X] [inst_1 : TopologicalSpace X] [inst_2 : NormedAddCommGro
up E]   {μ : MeasureTheor…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `smul_sub`：smul_sub (r : M) (x y : A) : r • (x - y) = r • x - r • y
· 使用定理 `MeasureTheory.integral_sub`：integral_sub {f g : α -> G} (hf : Integrable
 f μ) (hg : Integrable g μ) : ∫ a, f a - g a ∂μ = ∫ a, f a ∂μ - ∫ a, g a ∂μ
· 使用定理 `MeasureTheory.LocallyIntegrable.integrable_smul_left_of_hasCompactSuppor
t`：∀ {X : Type u_1} {E : Type u_6} [inst : MeasurableSpace X] [inst_1 : Topologi
calSpace X] [inst_2 : NormedAddCommGroup E]   {μ : MeasureTheor…
· 使用定理 `BorelSpace.opensMeasurable`：∀ {α : Type u_6} [inst : TopologicalSpace α]
 [inst_1 : MeasurableSpace α] [BorelSpace α], OpensMeasurableSpace α
· 使用定理 `ContMDiff.continuous`：ContMDiff.continuous (hf : ContMDiff I I' n f) : C
ontinuous f
· 使用定理 `sub_eq_zero`：∀ {G : Type u_3} [inst : AddGroup G] {a b : G}, a - b = 0 ↔
 a = b
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f

--- 原说明 ---
If two locally integrable functions on a finite-dimensional real manifold have t
he same integral
when multiplied by any smooth compactly supported function, then they coincide a
lmost everywhere.
-/
theorem ae_eq_of_integral_contMDiff_smul_eq
    (hf : LocallyIntegrable f μ) (hf' : LocallyIntegrable f' μ) (h : ∀ (g : M → ℝ),
      CMDiff ∞ g → HasCompactSupport g → ∫ x, g x • f x ∂μ = ∫ x, g x • f' x ∂μ) :
    ∀ᵐ x ∂μ, f x = f' x := by
  have : ∀ᵐ x ∂μ, (f - f') x = 0 := by
    apply ae_eq_zero_of_integral_contMDiff_smul_eq_zero I (hf.sub hf')
    intro g g_diff g_supp
    simp only [Pi.sub_apply, smul_sub]
    rw [integral_sub, sub_eq_zero]
    · exact h g g_diff g_supp
    · exact hf.integrable_smul_left_of_hasCompactSupport g_diff.continuous g_supp
    · exact hf'.integrable_smul_left_of_hasCompactSupport g_diff.continuous g_supp
  filter_upwards [this] with x hx
  simpa [sub_eq_zero] using hx

end Manifold

section VectorSpace

variable [MeasurableSpace E] [BorelSpace E] {f f' : E → F} {μ : Measure E}

/-- If a locally integrable function `f` on a finite-dimensional real vector space has zero integral
when multiplied by any smooth compactly supported function, then `f` vanishes almost everywhere. -/
/-
**ae_eq_zero_of_integral_contDiff_smul_eq_zero** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ae_eq_zero_of_integral_contDiff_smul_eq_zero (hf : LocallyIntegrable f μ) 
(h : forall (g : E -> Real), ContDiff Real ∞ g -> HasCompactSupport g -> ∫ x, g 
x • f x ∂μ = 0) : forallᵐ x ∂μ, f x = 0
参数：hf : LocallyIntegrable f μ；h : forall (g : E -> Real), ContDiff Real ∞ g -> H
asCompactSupport g -> ∫ x, g x • f x ∂μ = 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ae_eq_zero_of_integral_contMDiff_smul_eq_zero`：ae_eq_zero_of_integral_co
ntMDiff_smul_eq_zero [SigmaCompactSpace M] (hf : LocallyIntegrable f μ) (h : for
all g : M -> Real, CMDiff ∞ g -> Ha…
· 使用定理 `ContMDiffAdd.toIsManifold`：∀ {𝕜 : Type u_1} {inst : NontriviallyNormedFi
eld 𝕜} {H : Type u_2} {inst_1 : TopologicalSpace H} {E : Type u_3}   {inst_2 : N
ormedAddCommGro…
· 使用定理 `TopologicalSpace.t2Space_of_metrizableSpace`：∀ {X : Type u_2} [inst : To
pologicalSpace X] [TopologicalSpace.MetrizableSpace X], T2Space X
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α
· 使用定理 `SeparableWeaklyLocallyCompactAddGroup.sigmaCompactSpace`：∀ {G : Type w} 
[inst : TopologicalSpace G] [inst_1 : AddGroup G] [IsTopologicalAddGroup G]   [T
opologicalSpace.SeparableSpace G] [WeaklyLoca…
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `TopologicalSpace.SecondCountableTopology.to_separableSpace`：∀ {α : Type 
u} [t : TopologicalSpace α] [SecondCountableTopology α], TopologicalSpace.Separa
bleSpace α
· 使用定理 `secondCountable_of_proper`：∀ {α : Type u} [inst : PseudoMetricSpace α] [
ProperSpace α], SecondCountableTopology α
· 使用定理 `FiniteDimensional.proper_real`：∀ (E : Type u) [inst : NormedAddCommGroup
 E] [inst_1 : NormedSpace ℝ E] [FiniteDimensional ℝ E], ProperSpace E
· 使用定理 `instWeaklyLocallyCompactSpaceOfLocallyCompactSpace`：∀ {X : Type u_1} [in
st : TopologicalSpace X] [LocallyCompactSpace X], WeaklyLocallyCompactSpace X
· 使用定理 `locallyCompact_of_proper`：∀ {α : Type u} [inst : PseudoMetricSpace α] [P
roperSpace α], LocallyCompactSpace α
· 使用定理 `ContMDiff.contDiff`：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedField 𝕜] 
{E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜 E] {E' 
: Type u…

--- 原说明 ---
If a locally integrable function `f` on a finite-dimensional real vector space h
as zero integral
when multiplied by any smooth compactly supported function, then `f` vanishes al
most everywhere.
-/
theorem ae_eq_zero_of_integral_contDiff_smul_eq_zero (hf : LocallyIntegrable f μ)
    (h : ∀ (g : E → ℝ), ContDiff ℝ ∞ g → HasCompactSupport g → ∫ x, g x • f x ∂μ = 0) :
    ∀ᵐ x ∂μ, f x = 0 :=
  ae_eq_zero_of_integral_contMDiff_smul_eq_zero 𝓘(ℝ, E) hf
    (fun g g_diff g_supp ↦ h g g_diff.contDiff g_supp)

/-- If two locally integrable functions on a finite-dimensional real vector space have the same
integral when multiplied by any smooth compactly supported function, then they coincide almost
everywhere. -/
/-
**ae_eq_of_integral_contDiff_smul_eq** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ae_eq_of_integral_contDiff_smul_eq (hf : LocallyIntegrable f μ) (hf' : Loc
allyIntegrable f' μ) (h : forall (g : E -> Real), ContDiff Real ∞ g -> HasCompac
tSupport g -> ∫ x, g x • f x ∂μ = ∫ x, g x • f' x ∂μ) : forallᵐ x ∂μ, f x = f' x
参数：hf : LocallyIntegrable f μ；hf' : LocallyIntegrable f' μ；h : forall (g : E -> 
Real), ContDiff Real ∞ g -> HasCompactSupport g -> ∫ x, g x • f x ∂μ = ∫ x, g x 
• f' x ∂μ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ae_eq_of_integral_contMDiff_smul_eq`：ae_eq_of_integral_contMDiff_smul_eq
 (hf : LocallyIntegrable f μ) (hf' : LocallyIntegrable f' μ) (h : forall (g : M 
-> Real), CMDiff ∞ g -> H…
· 使用定理 `ContMDiffAdd.toIsManifold`：∀ {𝕜 : Type u_1} {inst : NontriviallyNormedFi
eld 𝕜} {H : Type u_2} {inst_1 : TopologicalSpace H} {E : Type u_3}   {inst_2 : N
ormedAddCommGro…
· 使用定理 `TopologicalSpace.t2Space_of_metrizableSpace`：∀ {X : Type u_2} [inst : To
pologicalSpace X] [TopologicalSpace.MetrizableSpace X], T2Space X
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α
· 使用定理 `SeparableWeaklyLocallyCompactAddGroup.sigmaCompactSpace`：∀ {G : Type w} 
[inst : TopologicalSpace G] [inst_1 : AddGroup G] [IsTopologicalAddGroup G]   [T
opologicalSpace.SeparableSpace G] [WeaklyLoca…
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `TopologicalSpace.SecondCountableTopology.to_separableSpace`：∀ {α : Type 
u} [t : TopologicalSpace α] [SecondCountableTopology α], TopologicalSpace.Separa
bleSpace α
· 使用定理 `secondCountable_of_proper`：∀ {α : Type u} [inst : PseudoMetricSpace α] [
ProperSpace α], SecondCountableTopology α
· 使用定理 `FiniteDimensional.proper_real`：∀ (E : Type u) [inst : NormedAddCommGroup
 E] [inst_1 : NormedSpace ℝ E] [FiniteDimensional ℝ E], ProperSpace E
· 使用定理 `instWeaklyLocallyCompactSpaceOfLocallyCompactSpace`：∀ {X : Type u_1} [in
st : TopologicalSpace X] [LocallyCompactSpace X], WeaklyLocallyCompactSpace X
· 使用定理 `locallyCompact_of_proper`：∀ {α : Type u} [inst : PseudoMetricSpace α] [P
roperSpace α], LocallyCompactSpace α
· 使用定理 `ContMDiff.contDiff`：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedField 𝕜] 
{E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜 E] {E' 
: Type u…

--- 原说明 ---
If two locally integrable functions on a finite-dimensional real vector space ha
ve the same
integral when multiplied by any smooth compactly supported function, then they c
oincide almost
everywhere.
-/
theorem ae_eq_of_integral_contDiff_smul_eq
    (hf : LocallyIntegrable f μ) (hf' : LocallyIntegrable f' μ) (h : ∀ (g : E → ℝ),
      ContDiff ℝ ∞ g → HasCompactSupport g → ∫ x, g x • f x ∂μ = ∫ x, g x • f' x ∂μ) :
    ∀ᵐ x ∂μ, f x = f' x :=
  ae_eq_of_integral_contMDiff_smul_eq 𝓘(ℝ, E) hf hf'
    (fun g g_diff g_supp ↦ h g g_diff.contDiff g_supp)

/-- If a function `f` locally integrable on an open subset `U` of a finite-dimensional real
  vector space has zero integral when multiplied by any smooth function compactly supported
  in `U`, then `f` vanishes almost everywhere in `U`. -/
/-
**IsOpen.ae_eq_zero_of_integral_contDiff_smul_eq_zero** 是 Mathlib 中的一个定理，位于命名空间 
``。
形式化陈述：IsOpen.ae_eq_zero_of_integral_contDiff_smul_eq_zero {U : Set E} (hU : IsOp
en U) (hf : LocallyIntegrableOn f U μ) (h : forall (g : E -> Real), ContDiff Rea
l ∞ g -> HasCompactSupport g -> tsupport g subseteq U -> ∫ x, g x • f x ∂μ = 0) 
: forallᵐ x ∂μ, x in U -> f x = 0
参数：hU : IsOpen U；hf : LocallyIntegrableOn f U μ；h : forall (g : E -> Real), Cont
Diff Real ∞ g -> HasCompactSupport g -> tsupport g subseteq U -> ∫ x, g x • f x 
∂μ = 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsOpen.ae_eq_zero_of_integral_contMDiff_smul_eq_zero`：IsOpen.ae_eq_zero_
of_integral_contMDiff_smul_eq_zero {U : Set M} (hU : IsOpen U) (hf : LocallyInte
grableOn f U μ) (h : forall g : M -> Real,…
· 使用定理 `ContMDiffAdd.toIsManifold`：∀ {𝕜 : Type u_1} {inst : NontriviallyNormedFi
eld 𝕜} {H : Type u_2} {inst_1 : TopologicalSpace H} {E : Type u_3}   {inst_2 : N
ormedAddCommGro…
· 使用定理 `TopologicalSpace.t2Space_of_metrizableSpace`：∀ {X : Type u_2} [inst : To
pologicalSpace X] [TopologicalSpace.MetrizableSpace X], T2Space X
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α
· 使用定理 `SeparableWeaklyLocallyCompactAddGroup.sigmaCompactSpace`：∀ {G : Type w} 
[inst : TopologicalSpace G] [inst_1 : AddGroup G] [IsTopologicalAddGroup G]   [T
opologicalSpace.SeparableSpace G] [WeaklyLoca…
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `TopologicalSpace.SecondCountableTopology.to_separableSpace`：∀ {α : Type 
u} [t : TopologicalSpace α] [SecondCountableTopology α], TopologicalSpace.Separa
bleSpace α
· 使用定理 `secondCountable_of_proper`：∀ {α : Type u} [inst : PseudoMetricSpace α] [
ProperSpace α], SecondCountableTopology α
· 使用定理 `FiniteDimensional.proper_real`：∀ (E : Type u) [inst : NormedAddCommGroup
 E] [inst_1 : NormedSpace ℝ E] [FiniteDimensional ℝ E], ProperSpace E
· 使用定理 `instWeaklyLocallyCompactSpaceOfLocallyCompactSpace`：∀ {X : Type u_1} [in
st : TopologicalSpace X] [LocallyCompactSpace X], WeaklyLocallyCompactSpace X
· 使用定理 `locallyCompact_of_proper`：∀ {α : Type u} [inst : PseudoMetricSpace α] [P
roperSpace α], LocallyCompactSpace α
· 使用定理 `ContMDiff.contDiff`：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedField 𝕜] 
{E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜 E] {E' 
: Type u…

--- 原说明 ---
If a function `f` locally integrable on an open subset `U` of a finite-dimension
al real
  vector space has zero integral when multiplied by any smooth function compactl
y supported
  in `U`, then `f` vanishes almost everywhere in `U`.
-/
theorem IsOpen.ae_eq_zero_of_integral_contDiff_smul_eq_zero {U : Set E} (hU : IsOpen U)
    (hf : LocallyIntegrableOn f U μ)
    (h : ∀ (g : E → ℝ), ContDiff ℝ ∞ g → HasCompactSupport g → tsupport g ⊆ U →
        ∫ x, g x • f x ∂μ = 0) :
    ∀ᵐ x ∂μ, x ∈ U → f x = 0 :=
  hU.ae_eq_zero_of_integral_contMDiff_smul_eq_zero 𝓘(ℝ, E) hf
    (fun g g_diff g_supp ↦ h g g_diff.contDiff g_supp)

end VectorSpace

