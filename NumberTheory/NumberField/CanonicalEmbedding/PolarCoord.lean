/-
Copyright (c) 2025 Xavier Roblot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xavier Roblot
-/
module

public import Mathlib.Analysis.SpecialFunctions.PolarCoord
public import Mathlib.NumberTheory.NumberField.CanonicalEmbedding.Basic
public import Mathlib.Topology.OpenPartialHomeomorph.Constructions

/-!
# Polar coordinate change of variables for the mixed space of a number field

We define two polar coordinate changes of variables for the mixed space `ℝ^r₁ × ℂ^r₂` associated
to a number field `K` of signature `(r₁, r₂)`. The first one is `mixedEmbedding.polarCoord` and has
value in `realMixedSpace K` defined as `ℝ^r₁ × (ℝ ⨯ ℝ)^r₂`, the second is
`mixedEmbedding.polarSpaceCoord` and has value in `polarSpace K` defined as `ℝ^(r₁+r₂) × ℝ^r₂`.

The change of variables with the `polarSpace` is useful to compute the volume of subsets of the
mixed space with enough symmetries, see `volume_eq_two_pi_pow_mul_integral` and
`volume_eq_two_pow_mul_two_pi_pow_mul_integral`

## Main definitions and results

* `mixedEmbedding.polarCoord`: the polar coordinate change of variables between the mixed
  space `ℝ^r₁ × ℂ^r₂` and `ℝ^r₁ × (ℝ × ℝ)^r₂` defined as the identity on the first component and
  mapping `(zᵢ)ᵢ` to `(‖zᵢ‖, Arg zᵢ)ᵢ` on the second component.

* `mixedEmbedding.integral_comp_polarCoord_symm`: the change of variables formula for
  `mixedEmbedding.polarCoord`

* `mixedEmbedding.polarSpaceCoord`: the polar coordinate change of variables between the mixed
  space `ℝ^r₁ × ℂ^r₂` and the polar space `ℝ^(r₁ + r₂) × ℝ^r₂` defined by sending `x` to
  `x w` or `‖x w‖` depending on whether `w` is real or complex for the first component, and
  to `Arg (x w)`, `w` complex, for the second component.

* `mixedEmbedding.integral_comp_polarSpaceCoord_symm`: the change of variables formula for
  `mixedEmbedding.polarSpaceCoord`

* `mixedEmbedding.volume_eq_two_pi_pow_mul_integral`: if the measurable set `A` of the mixed space
  is norm-stable at complex places in the sense that
  `normAtComplexPlaces⁻¹ (normAtComplexPlaces '' A) = A`, then its volume can be computed via an
  integral over `normAtComplexPlaces '' A`.

* `mixedEmbedding.volume_eq_two_pow_mul_two_pi_pow_mul_integral`: if the measurable set `A` of the
  mixed space is norm-stable in the sense that `normAtAllPlaces⁻¹ (normAtAllPlaces '' A) = A`,
  then its volume can be computed via an integral over `normAtAllPlaces '' A`.

-/

@[expose] public section

variable (K : Type*) [Field K]

namespace NumberField.mixedEmbedding

open NumberField NumberField.InfinitePlace NumberField.mixedEmbedding ENNReal MeasureTheory
  MeasureTheory.Measure Real

noncomputable section realMixedSpace

/--
The real mixed space `ℝ^r₁ × (ℝ × ℝ)^r₂` with `(r₁, r₂)` the signature of `K`.
-/
/-
**NumberField.mixedEmbedding.realMixedSpace** 是 Mathlib 中的一个缩写定义，位于命名空间 `NumberF
ield.mixedEmbedding`。
形式化陈述：realMixedSpace
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The real mixed space `ℝ^r₁ × (ℝ × ℝ)^r₂` with `(r₁, r₂)` the signature of `K`.
-/
abbrev realMixedSpace :=
  ({w : InfinitePlace K // IsReal w} → ℝ) × ({w : InfinitePlace K // IsComplex w} → ℝ × ℝ)

/--
The natural homeomorphism between the mixed space `ℝ^r₁ × ℂ^r₂` and the real mixed space
`ℝ^r₁ × (ℝ × ℝ)^r₂`.
-/
/-
**NumberField.mixedEmbedding.mixedSpaceToRealMixedSpace** 是 Mathlib 中的一个定义，位于命名空
间 `NumberField.mixedEmbedding`。
形式化陈述：mixedSpaceToRealMixedSpace : mixedSpace K ≃ₜ realMixedSpace K
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The natural homeomorphism between the mixed space `ℝ^r₁ × ℂ^r₂` and the real mix
ed space
`ℝ^r₁ × (ℝ × ℝ)^r₂`.
-/
noncomputable def mixedSpaceToRealMixedSpace : mixedSpace K ≃ₜ realMixedSpace K :=
  (Homeomorph.refl _).prodCongr <| .piCongrRight fun _ ↦ Complex.equivRealProdCLM.toHomeomorph

@[simp]
/-
**NumberField.mixedEmbedding.mixedSpaceToRealMixedSpace_apply** 是 Mathlib 中的一个定理
，位于命名空间 `NumberField.mixedEmbedding`。
形式化陈述：mixedSpaceToRealMixedSpace_apply (x : mixedSpace K) : mixedSpaceToRealMixe
dSpace K x = (x.1, fun w => Complex.equivRealProd (x.2 w))
参数：x : mixedSpace K。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem mixedSpaceToRealMixedSpace_apply (x : mixedSpace K) :
    mixedSpaceToRealMixedSpace K x = (x.1, fun w ↦ Complex.equivRealProd (x.2 w)) := rfl

variable [NumberField K]

open scoped Classical in
/-
**NumberField.mixedEmbedding.volume_preserving_mixedSpaceToRealMixedSpace_symm**
 是 Mathlib 中的一个定理，位于命名空间 `NumberField.mixedEmbedding`。
形式化陈述：volume_preserving_mixedSpaceToRealMixedSpace_symm : MeasurePreserving (mix
edSpaceToRealMixedSpace K).symm
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.MeasurePreserving.prod`：∀ {α : Type u_1} {β : Type u_2} {γ
 : Type u_3} [inst : MeasurableSpace α] [inst_1 : MeasurableSpace β]   [inst_2 :
 MeasurableSpace γ] {δ : T…
· 使用定理 `Complex.instFiniteDimensionalReal`：FiniteDimensional ℝ ℂ
· 使用定理 `MeasureTheory.instSFiniteOfSigmaFinite`：∀ {α : Type u_1} {m0 : Measurabl
eSpace α} {μ : MeasureTheory.Measure α} [MeasureTheory.SigmaFinite μ],   Measure
Theory.SFinite μ
· 使用定理 `MeasureTheory.Measure.instSigmaFiniteForallVolume`：∀ {ι : Type u_1} [ins
t : Fintype ι] {α : ι → Type u_4} [inst_1 : (i : ι) → MeasureTheory.MeasureSpace
 (α i)]   [∀ (i : ι), MeasureTheory.Sig…
· 使用定理 `MeasureTheory.Measure.IsAddHaarMeasure.sigmaFinite`：∀ {G : Type u_1} [in
st : MeasurableSpace G] [inst_1 : AddGroup G] [inst_2 : TopologicalSpace G]   (μ
 : MeasureTheory.Measure G) [μ.IsAddHaar…
· 使用定理 `instIsAddHaarMeasureVolume`：∀ {E : Type u_3} [inst : NormedAddCommGroup 
E] [inst_1 : InnerProductSpace ℝ E] [inst_2 : FiniteDimensional ℝ E]   [inst_3 :
 MeasurableSpace…
· 使用定理 `SeparableWeaklyLocallyCompactAddGroup.sigmaCompactSpace`：∀ {G : Type w} 
[inst : TopologicalSpace G] [inst_1 : AddGroup G] [IsTopologicalAddGroup G]   [T
opologicalSpace.SeparableSpace G] [WeaklyLoca…
· 使用定理 `instIsTopologicalAddGroupReal`：IsTopologicalAddGroup ℝ
· 使用定理 `TopologicalSpace.SecondCountableTopology.to_separableSpace`：∀ {α : Type 
u} [t : TopologicalSpace α] [SecondCountableTopology α], TopologicalSpace.Separa
bleSpace α
· 使用定理 `instSecondCountableTopologyReal`：SecondCountableTopology ℝ
· 使用定理 `instWeaklyLocallyCompactSpaceOfLocallyCompactSpace`：∀ {X : Type u_1} [in
st : TopologicalSpace X] [LocallyCompactSpace X], WeaklyLocallyCompactSpace X
· 使用定理 `locallyCompact_of_proper`：∀ {α : Type u} [inst : PseudoMetricSpace α] [P
roperSpace α], LocallyCompactSpace α
· 使用定理 `instProperSpaceReal`：ProperSpace ℝ
· 使用定理 `MeasureTheory.Measure.instSigmaFiniteProdVolume`：∀ {α : Type u_4} {β : T
ype u_5} [inst : MeasureTheory.MeasureSpace α] [MeasureTheory.SigmaFinite Measur
eTheory.volume]   [inst_2 : MeasureTh…
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `MeasureTheory.MeasurePreserving.id`：∀ {α : Type u_1} [inst : MeasurableS
pace α] (μ : MeasureTheory.Measure α), MeasureTheory.MeasurePreserving id μ μ
· 使用定理 `MeasureTheory.volume_preserving_pi`：volume_preserving_pi {α' β' : ι -> T
ype*} [forall i, MeasureSpace (α' i)] [forall i, MeasureSpace (β' i)] [forall i,
 SigmaFinite (volume : M…
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `secondCountable_of_proper`：∀ {α : Type u} [inst : PseudoMetricSpace α] [
ProperSpace α], SecondCountableTopology α
· 使用定理 `Complex.instProperSpace`：ProperSpace ℂ
· 使用定理 `MeasureTheory.MeasurePreserving.symm`：symm (e : α ≃ᵐ β) {μa : Measure α}
 {μb : Measure β} (h : MeasurePreserving e μa μb) : MeasurePreserving e.symm μb 
μa
· 使用定理 `Complex.volume_preserving_equiv_real_prod`：volume_preserving_equiv_real_
prod : MeasurePreserving measurableEquivRealProd
-/
theorem volume_preserving_mixedSpaceToRealMixedSpace_symm :
    MeasurePreserving (mixedSpaceToRealMixedSpace K).symm :=
  (MeasurePreserving.id _).prod <|
    volume_preserving_pi fun _ ↦ Complex.volume_preserving_equiv_real_prod.symm

open scoped Classical in
/-
**NumberField.mixedEmbedding.** 是 Mathlib 中的一个实例，位于命名空间 `NumberField.mixedEmbedd
ing`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : IsAddHaarMeasure (volume : Measure (realMixedSpace K)) := prod.instIsAddHaarMeasure _ _

/--
The polar coordinate open partial homeomorphism of `ℝ^r₁ × (ℝ × ℝ)^r₂` defined as the identity on
the first component and mapping `(rᵢ cos θᵢ, rᵢ sin θᵢ)ᵢ` to `(rᵢ, θᵢ)ᵢ` on the second component.
-/
@[simps! apply target]
/-
**NumberField.mixedEmbedding.polarCoordReal** 是 Mathlib 中的一个定义，位于命名空间 `NumberFie
ld.mixedEmbedding`。
形式化陈述：polarCoordReal : OpenPartialHomeomorph (realMixedSpace K) (realMixedSpace 
K)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The polar coordinate open partial homeomorphism of `ℝ^r₁ × (ℝ × ℝ)^r₂` defined a
s the identity on
the first component and mapping `(rᵢ cos θᵢ, rᵢ sin θᵢ)ᵢ` to `(rᵢ, θᵢ)ᵢ` on the 
second component.
-/
def polarCoordReal : OpenPartialHomeomorph (realMixedSpace K) (realMixedSpace K) :=
  (OpenPartialHomeomorph.refl _).prod (OpenPartialHomeomorph.pi fun _ ↦ polarCoord)
/-
**NumberField.mixedEmbedding.measurable_polarCoordReal_symm** 是 Mathlib 中的一个定理，位
于命名空间 `NumberField.mixedEmbedding`。
形式化陈述：measurable_polarCoordReal_symm : Measurable (polarCoordReal K).symm
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Measurable.prodMk`：Measurable.prodMk {β γ} {_ : MeasurableSpace β} {_ : 
MeasurableSpace γ} {f : α -> β} {g : α -> γ} (hf : Measurable f) (hg : Measurabl
e g) : …
· 使用定理 `measurable_fst`：measurable_fst {_ : MeasurableSpace α} {_ : MeasurableSp
ace β} : Measurable (Prod.fst : α × β -> α)
· 使用定理 `Measurable.comp`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {x : Mea
surableSpace α} {x_1 : MeasurableSpace β}   {x_2 : MeasurableSpace γ} {g : β → γ
} {f …
· 使用定理 `measurable_pi_lambda`：measurable_pi_lambda (f : α -> forall a, X a) (hf 
: forall a, Measurable fun c => f c a) : Measurable f
· 使用定理 `Continuous.measurable`：Continuous.measurable {f : α -> γ} (hf : Continuo
us f) : Measurable f
· 使用定理 `BorelSpace.opensMeasurable`：∀ {α : Type u_6} [inst : TopologicalSpace α]
 [inst_1 : MeasurableSpace α] [BorelSpace α], OpensMeasurableSpace α
· 使用定理 `secondCountableTopologyEither_of_right`：∀ (α : Type u_6) (β : Type u_7) 
[inst : TopologicalSpace α] [inst_1 : TopologicalSpace β] [SecondCountableTopolo
gy β],   SecondCountableTopo…
· 使用定理 `instSecondCountableTopologyReal`：SecondCountableTopology ℝ
· 使用定理 `continuous_polarCoord_symm`：continuous_polarCoord_symm : Continuous pola
rCoord.symm
· 使用定理 `measurable_pi_apply`：measurable_pi_apply (a : δ) : Measurable fun f : fo
rall a, X a => f a
· 使用定理 `measurable_snd`：measurable_snd {_ : MeasurableSpace α} {_ : MeasurableSp
ace β} : Measurable (Prod.snd : α × β -> β)
-/
theorem measurable_polarCoordReal_symm :
    Measurable (polarCoordReal K).symm := by
  refine measurable_fst.prodMk <| Measurable.comp ?_ measurable_snd
  exact measurable_pi_lambda _
    fun _ ↦ continuous_polarCoord_symm.measurable.comp (measurable_pi_apply _)
/-
**NumberField.mixedEmbedding.polarCoordReal_source** 是 Mathlib 中的一个定理，位于命名空间 `Nu
mberField.mixedEmbedding`。
形式化陈述：polarCoordReal_source : (polarCoordReal K).source = Set.univ ×ˢ (Set.univ.
pi fun _ => polarCoord.source)
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem polarCoordReal_source :
    (polarCoordReal K).source = Set.univ ×ˢ (Set.univ.pi fun _ ↦ polarCoord.source) := rfl
/-
**NumberField.mixedEmbedding.abs_of_mem_polarCoordReal_target** 是 Mathlib 中的一个定理
，位于命名空间 `NumberField.mixedEmbedding`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private theorem abs_of_mem_polarCoordReal_target {x : realMixedSpace K}
    (hx : x ∈ (polarCoordReal K).target) (w : {w // IsComplex w}) :
    |(x.2 w).1| = (x.2 w).1 :=
  abs_of_pos (hx.2 w (Set.mem_univ _)).1

open ContinuousLinearMap in
/--
The derivative of `polarCoordReal.symm`, see `hasFDerivAt_polarCoordReal_symm`.
-/
/-
**NumberField.mixedEmbedding.FDerivPolarCoordRealSymm** 是 Mathlib 中的一个定义，位于命名空间 
`NumberField.mixedEmbedding`。
形式化陈述：FDerivPolarCoordRealSymm : realMixedSpace K -> realMixedSpace K ->L[Real] 
realMixedSpace K
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The derivative of `polarCoordReal.symm`, see `hasFDerivAt_polarCoordReal_symm`.
-/
def FDerivPolarCoordRealSymm : realMixedSpace K → realMixedSpace K →L[ℝ] realMixedSpace K :=
  fun x ↦ (fst ℝ _ _).prod <| (fderivPiPolarCoordSymm x.2).comp (snd ℝ _ _)
/-
**NumberField.mixedEmbedding.hasFDerivAt_polarCoordReal_symm** 是 Mathlib 中的一个定理，
位于命名空间 `NumberField.mixedEmbedding`。
形式化陈述：hasFDerivAt_polarCoordReal_symm (x : realMixedSpace K) : HasFDerivAt (pola
rCoordReal K).symm (FDerivPolarCoordRealSymm K x) x
参数：x : realMixedSpace K。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasFDerivAt.prodMap`：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedField 𝕜]
 {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜 E] {F 
: Type u_…
· 使用定理 `hasFDerivAt_id`：hasFDerivAt_id (x : E) : HasFDerivAt id (.id 𝕜 E) x
· 使用定理 `hasFDerivAt_pi_polarCoord_symm`：hasFDerivAt_pi_polarCoord_symm [Finite ι
] (p : ι -> Real × Real) : HasFDerivAt (fun x i => polarCoord.symm (x i)) (fderi
vPiPolarCoordSymm p)…
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
-/
theorem hasFDerivAt_polarCoordReal_symm (x : realMixedSpace K) :
    HasFDerivAt (polarCoordReal K).symm (FDerivPolarCoordRealSymm K x) x := by
  classical
  exact (hasFDerivAt_id x.1).prodMap x (hasFDerivAt_pi_polarCoord_symm x.2)

open scoped Classical in
/-
**NumberField.mixedEmbedding.det_fderivPolarCoordRealSymm** 是 Mathlib 中的一个定理，位于命
名空间 `NumberField.mixedEmbedding`。
形式化陈述：det_fderivPolarCoordRealSymm (x : realMixedSpace K) : (FDerivPolarCoordRea
lSymm K x).det = ∏ w : {w // IsComplex w}, (x.2 w).1
参数：x : realMixedSpace K。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ContinuousLinearMap.det.eq_1`：∀ {R : Type u_1} [inst : CommRing R] {M : 
Type u_2} [inst_1 : TopologicalSpace M] [inst_2 : AddCommGroup M]   [inst_3 : _r
oot_.Module R M] (…
· 使用定理 `LinearMap.det_prodMap`：det_prodMap [Module.Free R M] [Module.Free R M'] 
[Module.Finite R M] [Module.Finite R M'] (f : Module.End R M) (f' : Module.End R
 M') : (pro…
· 使用定理 `Module.Free.function`：∀ (ι : Type u_1) (R : Type u_2) (M : Type u_3) [in
st : Semiring R] [inst_1 : AddCommMonoid M]   [inst_2 : _root_.Module R M] [Fini
te ι] [Mod…
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `instIsPrincipalIdealRingOfIsSemisimpleRing`：∀ {R : Type u_2} [inst : Rin
g R] [IsSemisimpleRing R], IsPrincipalIdealRing R
· 使用定理 `instIsSemisimpleModuleOfIsSimpleModule`：∀ (R : Type u_2) [inst : Ring R]
 (M : Type u_4) [inst_1 : AddCommGroup M] [inst_2 : _root_.Module R M]   [IsSimp
leModule R M], IsSemisimpleM…
· 使用定理 `instIsSimpleModule`：∀ (R : Type u_5) [inst : DivisionRing R], IsSimpleMo
dule R R
· 使用定理 `Real.instIsDomain`：IsDomain ℝ
· 使用定理 `instIsTorsionFreeOfIsDomainOfNoZeroSMulDivisors`：∀ {R : Type u_1} {M : T
ype u_2} [inst : Semiring R] [IsDomain R] [inst_2 : AddCommGroup M] [inst_3 : _r
oot_.Module R M]   [NoZeroSMulDivisor…
· 使用定理 `GroupWithZero.toNoZeroSMulDivisors`：∀ {R : Type u_1} {M : Type u_2} [ins
t : GroupWithZero R] [inst_1 : AddMonoid M] [inst_2 : DistribMulAction R M],   N
oZeroSMulDivisors R M
· 使用定理 `Module.Free.prod`：∀ (R : Type u_7) (M : Type u_8) (N : Type u_9) [inst :
 Semiring R] [inst_1 : AddCommMonoid M]   [inst_2 : _root_.Module R M] [inst_3 :
 AddCo…
· 使用定理 `LinearMap.det_id`：det_id : LinearMap.det (LinearMap.id : M ->ₗ[A] M) = 1
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `det_fderivPiPolarCoordSymm`：det_fderivPiPolarCoordSymm (p : ι -> Real × 
Real) : (fderivPiPolarCoordSymm p).det = ∏ i, (p i).1
-/
theorem det_fderivPolarCoordRealSymm (x : realMixedSpace K) :
    (FDerivPolarCoordRealSymm K x).det = ∏ w : {w // IsComplex w}, (x.2 w).1 := by
  have : (FDerivPolarCoordRealSymm K x).toLinearMap =
      LinearMap.prodMap (LinearMap.id) (fderivPiPolarCoordSymm x.2).toLinearMap := rfl
  rw [ContinuousLinearMap.det, this, LinearMap.det_prodMap, LinearMap.det_id, one_mul,
    ← ContinuousLinearMap.det, det_fderivPiPolarCoordSymm]

open scoped Classical in
/-
**NumberField.mixedEmbedding.polarCoordReal_symm_target_ae_eq_univ** 是 Mathlib 中
的一个定理，位于命名空间 `NumberField.mixedEmbedding`。
形式化陈述：polarCoordReal_symm_target_ae_eq_univ : (polarCoordReal K).symm '' (polarC
oordReal K).target =ᵐ[volume] Set.univ
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.univ_prod_univ`：univ_prod_univ : @univ α ×ˢ @univ β = univ
· 使用定理 `MeasureTheory.Measure.volume_eq_prod`：volume_eq_prod (α β) [MeasureSpace
 α] [MeasureSpace β] : (volume : Measure (α × β)) = (volume : Measure α).prod (v
olume : Measure β)
· 使用定理 `OpenPartialHomeomorph.symm_image_target_eq_source`：symm_image_target_eq_
source : e.symm '' e.target = e.source
· 使用定理 `NumberField.mixedEmbedding.polarCoordReal_source`：polarCoordReal_source 
: (polarCoordReal K).source = Set.univ ×ˢ (Set.univ.pi fun _ => polarCoord.sourc
e)
· 使用定理 `Set.piMap_image_univ_pi`：piMap_image_univ_pi (f : forall i, α i -> β i) 
(t : forall i, Set (α i)) : Pi.map f '' univ.pi t = univ.pi fun i => f i '' t i
· 使用引理 `MeasureTheory.Measure.set_prod_ae_eq`：set_prod_ae_eq {s s' : Set α} {t t
' : Set β} (hs : s =ᵐ[μ] s') (ht : t =ᵐ[ν] t') : (s ×ˢ t : Set (α × β)) =ᵐ[μ.pro
d ν] (s' ×ˢ t' : Set (α × …
· 使用定理 `Filter.EventuallyEq.rfl`：∀ {α : Type u} {β : Type v} {l : Filter α} {f :
 α → β}, f =ᶠ[l] f
· 使用定理 `pi_polarCoord_symm_target_ae_eq_univ`：pi_polarCoord_symm_target_ae_eq_un
iv : (Pi.map (fun _ : ι => polarCoord.symm) '' Set.univ.pi fun _ => polarCoord.t
arget) =ᵐ[volume] Set.univ
-/
theorem polarCoordReal_symm_target_ae_eq_univ :
    (polarCoordReal K).symm '' (polarCoordReal K).target =ᵐ[volume] Set.univ := by
  rw [← Set.univ_prod_univ, volume_eq_prod, (polarCoordReal K).symm_image_target_eq_source,
    polarCoordReal_source, ← polarCoord.symm_image_target_eq_source, ← Set.piMap_image_univ_pi]
  exact set_prod_ae_eq .rfl pi_polarCoord_symm_target_ae_eq_univ

open scoped Classical in
/-
**NumberField.mixedEmbedding.integral_comp_polarCoordReal_symm** 是 Mathlib 中的一个定
理，位于命名空间 `NumberField.mixedEmbedding`。
形式化陈述：integral_comp_polarCoordReal_symm {E : Type*} [NormedAddCommGroup E] [Norm
edSpace Real E] (f : realMixedSpace K -> E) : ∫ x in (polarCoordReal K).target, 
(∏ w : {w // IsComplex w}, (x.2 w).1) • f ((polarCoordReal K).symm x) = ∫ x, f x
参数：f : realMixedSpace K -> E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.setIntegral_univ`：setIntegral_univ : ∫ x in univ, f x ∂μ =
 ∫ x, f x ∂μ
· 使用定理 `MeasureTheory.setIntegral_congr_set`：setIntegral_congr_set (hst : s =ᵐ[μ
] t) : ∫ x in s, f x ∂μ = ∫ x in t, f x ∂μ
· 使用定理 `NumberField.mixedEmbedding.polarCoordReal_symm_target_ae_eq_univ`：polarC
oordReal_symm_target_ae_eq_univ : (polarCoordReal K).symm '' (polarCoordReal K).
target =ᵐ[volume] Set.univ
· 使用定理 `MeasureTheory.integral_image_eq_integral_abs_det_fderiv_smul`：integral_i
mage_eq_integral_abs_det_fderiv_smul (hs : MeasurableSet s) (hf' : forall x in s
, HasFDerivWithinAt f (f' x) s x) (hf : InjOn f s)…
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `Subtype.countable`：∀ {α : Sort u} [Countable α] {p : α → Prop}, Countabl
e { x // p x }
· 使用定理 `Finite.to_countable`：∀ {α : Sort u} [Finite α], Countable α
· 使用定理 `instSecondCountableTopologyReal`：SecondCountableTopology ℝ
· 使用定理 `TopologicalSpace.instSecondCountableTopologyProd`：∀ {α : Type u} [t : To
pologicalSpace α] {β : Type u_1} [inst : TopologicalSpace β] [SecondCountableTop
ology α]   [SecondCountableTopology β]…
· 使用定理 `secondCountableTopologyEither_of_right`：∀ (α : Type u_6) (β : Type u_7) 
[inst : TopologicalSpace α] [inst_1 : TopologicalSpace β] [SecondCountableTopolo
gy β],   SecondCountableTopo…
· 使用定理 `TopologicalSpace.instSecondCountableTopologyForallOfCountable`：∀ {ι : Ty
pe u_1} {X : ι → Type u_2} [Countable ι] [inst : (a : ι) → TopologicalSpace (X a
)]   [∀ (a : ι), SecondCountableTopology (X a)], Se…
· 使用定理 `NumberField.mixedEmbedding.instIsAddHaarMeasureRealMixedSpaceVolume`：∀ (
K : Type u_1) [inst : Field K] [inst_1 : NumberField K], MeasureTheory.volume.Is
AddHaarMeasure
· 使用定理 `IsOpen.measurableSet`：IsOpen.measurableSet (h : IsOpen s) : MeasurableSe
t s
· 使用定理 `BorelSpace.opensMeasurable`：∀ {α : Type u_6} [inst : TopologicalSpace α]
 [inst_1 : MeasurableSpace α] [BorelSpace α], OpensMeasurableSpace α
· 使用定理 `OpenPartialHomeomorph.open_target`：∀ {X : Type u_7} {Y : Type u_8} [inst
 : TopologicalSpace X] [inst_1 : TopologicalSpace Y]   (self : OpenPartialHomeom
orph X Y), IsOpen self.…
· 使用定理 `HasFDerivAt.hasFDerivWithinAt`：HasFDerivAt.hasFDerivWithinAt (h : HasFDe
rivAt f f' x) : HasFDerivWithinAt f f' s x
· 使用定理 `NumberField.mixedEmbedding.hasFDerivAt_polarCoordReal_symm`：hasFDerivAt_
polarCoordReal_symm (x : realMixedSpace K) : HasFDerivAt (polarCoordReal K).symm
 (FDerivPolarCoordRealSymm K x) x
· 使用定理 `OpenPartialHomeomorph.injOn`：∀ {X : Type u_1} {Y : Type u_3} [inst : Top
ologicalSpace X] [inst_1 : TopologicalSpace Y]   (e : OpenPartialHomeomorph X Y)
, Set.InjOn (↑e) …
· 使用定理 `MeasureTheory.setIntegral_congr_fun`：setIntegral_congr_fun (hs : Measura
bleSet s) (h : EqOn f g s) : ∫ x in s, f x ∂μ = ∫ x in s, g x ∂μ
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `NumberField.mixedEmbedding.det_fderivPolarCoordRealSymm`：det_fderivPolar
CoordRealSymm (x : realMixedSpace K) : (FDerivPolarCoordRealSymm K x).det = ∏ w 
: {w // IsComplex w}, (x.2 w).1
· 使用引理 `Finset.abs_prod`：abs_prod [CommRing R] [LinearOrder R] [IsStrictOrderedR
ing R] (s : Finset ι) (f : ι -> R) : |∏ x in s, f x| = ∏ x in s, |f x|
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Finset.prod_congr`：prod_congr (h : s₁ = s₂) : (forall x in s₂, f x = g x
) -> s₁.prod f = s₂.prod g
· 使用定理 `_private.Mathlib.NumberTheory.NumberField.CanonicalEmbedding.PolarCoord.
0.NumberField.mixedEmbedding.abs_of_mem_polarCoordReal_target`：∀ (K : Type u_1) 
[inst : Field K] [inst_1 : NumberField K] {x : NumberField.mixedEmbedding.realMi
xedSpace K},   x ∈ (NumberField.mixedEmbedd…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem integral_comp_polarCoordReal_symm {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : realMixedSpace K → E) :
    ∫ x in (polarCoordReal K).target, (∏ w : {w // IsComplex w}, (x.2 w).1) •
      f ((polarCoordReal K).symm x) = ∫ x, f x := by
  rw [← setIntegral_univ (f := f),
    ← setIntegral_congr_set (polarCoordReal_symm_target_ae_eq_univ K),
    integral_image_eq_integral_abs_det_fderiv_smul volume
      (polarCoordReal K).open_target.measurableSet
      (fun x _ ↦ (hasFDerivAt_polarCoordReal_symm K x).hasFDerivWithinAt)
      (polarCoordReal K).symm.injOn f]
  refine setIntegral_congr_fun (polarCoordReal K).open_target.measurableSet fun x hx ↦ ?_
  simp_rw [det_fderivPolarCoordRealSymm, Finset.abs_prod, abs_of_mem_polarCoordReal_target K hx]

open scoped Classical in
/-
**NumberField.mixedEmbedding.lintegral_comp_polarCoordReal_symm** 是 Mathlib 中的一个
定理，位于命名空间 `NumberField.mixedEmbedding`。
形式化陈述：lintegral_comp_polarCoordReal_symm (f : realMixedSpace K -> Real>=0∞) : ∫⁻
 x in (polarCoordReal K).target, (∏ w : {w // IsComplex w}, .ofReal (x.2 w).1) *
 f ((polarCoordReal K).symm x) = ∫⁻ x, f x
参数：f : realMixedSpace K -> Real>=0∞。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.setLIntegral_univ`：setLIntegral_univ (f : α -> Real>=0∞) :
 ∫⁻ x in univ, f x ∂μ = ∫⁻ x, f x ∂μ
· 使用定理 `MeasureTheory.setLIntegral_congr`：setLIntegral_congr {f : α -> Real>=0∞}
 {s t : Set α} (h : s =ᵐ[μ] t) : ∫⁻ x in s, f x ∂μ = ∫⁻ x in t, f x ∂μ
· 使用定理 `NumberField.mixedEmbedding.polarCoordReal_symm_target_ae_eq_univ`：polarC
oordReal_symm_target_ae_eq_univ : (polarCoordReal K).symm '' (polarCoordReal K).
target =ᵐ[volume] Set.univ
· 使用定理 `MeasureTheory.lintegral_image_eq_lintegral_abs_det_fderiv_mul`：lintegral
_image_eq_lintegral_abs_det_fderiv_mul (hs : MeasurableSet s) (hf' : forall x in
 s, HasFDerivWithinAt f (f' x) s x) (hf : InjOn f s…
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `Subtype.countable`：∀ {α : Sort u} [Countable α] {p : α → Prop}, Countabl
e { x // p x }
· 使用定理 `Finite.to_countable`：∀ {α : Sort u} [Finite α], Countable α
· 使用定理 `instSecondCountableTopologyReal`：SecondCountableTopology ℝ
· 使用定理 `TopologicalSpace.instSecondCountableTopologyProd`：∀ {α : Type u} [t : To
pologicalSpace α] {β : Type u_1} [inst : TopologicalSpace β] [SecondCountableTop
ology α]   [SecondCountableTopology β]…
· 使用定理 `secondCountableTopologyEither_of_right`：∀ (α : Type u_6) (β : Type u_7) 
[inst : TopologicalSpace α] [inst_1 : TopologicalSpace β] [SecondCountableTopolo
gy β],   SecondCountableTopo…
· 使用定理 `TopologicalSpace.instSecondCountableTopologyForallOfCountable`：∀ {ι : Ty
pe u_1} {X : ι → Type u_2} [Countable ι] [inst : (a : ι) → TopologicalSpace (X a
)]   [∀ (a : ι), SecondCountableTopology (X a)], Se…
· 使用定理 `NumberField.mixedEmbedding.instIsAddHaarMeasureRealMixedSpaceVolume`：∀ (
K : Type u_1) [inst : Field K] [inst_1 : NumberField K], MeasureTheory.volume.Is
AddHaarMeasure
· 使用定理 `IsOpen.measurableSet`：IsOpen.measurableSet (h : IsOpen s) : MeasurableSe
t s
· 使用定理 `BorelSpace.opensMeasurable`：∀ {α : Type u_6} [inst : TopologicalSpace α]
 [inst_1 : MeasurableSpace α] [BorelSpace α], OpensMeasurableSpace α
· 使用定理 `OpenPartialHomeomorph.open_target`：∀ {X : Type u_7} {Y : Type u_8} [inst
 : TopologicalSpace X] [inst_1 : TopologicalSpace Y]   (self : OpenPartialHomeom
orph X Y), IsOpen self.…
· 使用定理 `HasFDerivAt.hasFDerivWithinAt`：HasFDerivAt.hasFDerivWithinAt (h : HasFDe
rivAt f f' x) : HasFDerivWithinAt f f' s x
· 使用定理 `NumberField.mixedEmbedding.hasFDerivAt_polarCoordReal_symm`：hasFDerivAt_
polarCoordReal_symm (x : realMixedSpace K) : HasFDerivAt (polarCoordReal K).symm
 (FDerivPolarCoordRealSymm K x) x
· 使用定理 `OpenPartialHomeomorph.injOn`：∀ {X : Type u_1} {Y : Type u_3} [inst : Top
ologicalSpace X] [inst_1 : TopologicalSpace Y]   (e : OpenPartialHomeomorph X Y)
, Set.InjOn (↑e) …
· 使用定理 `MeasureTheory.setLIntegral_congr_fun`：setLIntegral_congr_fun {f g : α ->
 Real>=0∞} {s : Set α} (hs : MeasurableSet s) (hfg : EqOn f g s) : ∫⁻ x in s, f 
x ∂μ = ∫⁻ x in s, g x ∂μ
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `NumberField.mixedEmbedding.det_fderivPolarCoordRealSymm`：det_fderivPolar
CoordRealSymm (x : realMixedSpace K) : (FDerivPolarCoordRealSymm K x).det = ∏ w 
: {w // IsComplex w}, (x.2 w).1
· 使用引理 `Finset.abs_prod`：abs_prod [CommRing R] [LinearOrder R] [IsStrictOrderedR
ing R] (s : Finset ι) (f : ι -> R) : |∏ x in s, f x| = ∏ x in s, |f x|
· 使用定理 `ENNReal.ofReal_prod_of_nonneg`：ofReal_prod_of_nonneg {α : Type*} {s : Fi
nset α} {f : α -> Real} (hf : forall i, i in s -> 0 <= f i) : ENNReal.ofReal (∏ 
i in s, f i) = ∏ i …
· 使用定理 `abs_nonneg`：∀ {α : Type u_1} [inst : Lattice α] [inst_1 : AddGroup α] [A
ddLeftMono α] [AddRightMono α] (a : α), 0 ≤ |a|
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
（共 33 条，此处仅展示前 30 条）
-/
theorem lintegral_comp_polarCoordReal_symm (f : realMixedSpace K → ℝ≥0∞) :
    ∫⁻ x in (polarCoordReal K).target, (∏ w : {w // IsComplex w}, .ofReal (x.2 w).1) *
      f ((polarCoordReal K).symm x) = ∫⁻ x, f x := by
  rw [← setLIntegral_univ f, ← setLIntegral_congr (polarCoordReal_symm_target_ae_eq_univ K),
    lintegral_image_eq_lintegral_abs_det_fderiv_mul volume
      (polarCoordReal K).open_target.measurableSet
      (fun x _ ↦ (hasFDerivAt_polarCoordReal_symm K x).hasFDerivWithinAt)
      (polarCoordReal K).symm.injOn f]
  refine setLIntegral_congr_fun (polarCoordReal K).open_target.measurableSet (fun x hx ↦ ?_)
  simp_rw [det_fderivPolarCoordRealSymm, Finset.abs_prod,
    ENNReal.ofReal_prod_of_nonneg (fun _ _ ↦ abs_nonneg _), abs_of_mem_polarCoordReal_target K hx]

end realMixedSpace

section mixedSpace

variable [NumberField K]

/--
The polar coordinate open partial homeomorphism between the mixed space `ℝ^r₁ × ℂ^r₂` and
`ℝ^r₁ × (ℝ × ℝ)^r₂` defined as the identity on the first component and mapping `(zᵢ)ᵢ` to
`(‖zᵢ‖, Arg zᵢ)ᵢ` on the second component.
-/
@[simps!]
/-
**NumberField.mixedEmbedding.polarCoord** 是 Mathlib 中的一个定义，位于命名空间 `NumberField.m
ixedEmbedding`。
形式化陈述：(K : Type u_1) →   [inst : Field K] →     [NumberField K] →       OpenPart
ialHomeomorph (NumberField.mixedEmbedding.mixedSpace K) (NumberField.mixedEmbedd
ing.realMixedSpace K)
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The polar coordinate open partial homeomorphism between the mixed space `ℝ^r₁ × 
ℂ^r₂` and
`ℝ^r₁ × (ℝ × ℝ)^r₂` defined as the identity on the first component and mapping `
(zᵢ)ᵢ` to
`(‖zᵢ‖, Arg zᵢ)ᵢ` on the second component.
-/
protected noncomputable def polarCoord : OpenPartialHomeomorph (mixedSpace K) (realMixedSpace K) :=
  (OpenPartialHomeomorph.refl _).prod (OpenPartialHomeomorph.pi fun _ ↦ Complex.polarCoord)
/-
**NumberField.mixedEmbedding.polarCoord_target_eq_polarCoordReal_target** 是 Math
lib 中的一个定理，位于命名空间 `NumberField.mixedEmbedding`。
形式化陈述：polarCoord_target_eq_polarCoordReal_target : (mixedEmbedding.polarCoord K)
.target = (polarCoordReal K).target
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem polarCoord_target_eq_polarCoordReal_target :
    (mixedEmbedding.polarCoord K).target = (polarCoordReal K).target := rfl
/-
**NumberField.mixedEmbedding.polarCoord_symm_eq** 是 Mathlib 中的一个定理，位于命名空间 `Numbe
rField.mixedEmbedding`。
形式化陈述：polarCoord_symm_eq : (mixedEmbedding.polarCoord K).symm = (mixedSpaceToRea
lMixedSpace K).symm ∘ (polarCoordReal K).symm
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem polarCoord_symm_eq :
    (mixedEmbedding.polarCoord K).symm =
      (mixedSpaceToRealMixedSpace K).symm ∘ (polarCoordReal K).symm := rfl
/-
**NumberField.mixedEmbedding.measurable_polarCoord_symm** 是 Mathlib 中的一个定理，位于命名空
间 `NumberField.mixedEmbedding`。
形式化陈述：measurable_polarCoord_symm : Measurable (mixedEmbedding.polarCoord K).symm
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `NumberField.mixedEmbedding.polarCoord_symm_eq`：polarCoord_symm_eq : (mix
edEmbedding.polarCoord K).symm = (mixedSpaceToRealMixedSpace K).symm ∘ (polarCoo
rdReal K).symm
· 使用定理 `Measurable.comp`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {x : Mea
surableSpace α} {x_1 : MeasurableSpace β}   {x_2 : MeasurableSpace γ} {g : β → γ
} {f …
· 使用定理 `Homeomorph.measurable`：∀ {α : Type u_1} {γ : Type u_3} [inst : Topologic
alSpace α] [inst_1 : MeasurableSpace α] [OpensMeasurableSpace α]   [inst_3 : Top
ologicalSpa…
· 使用定理 `Subtype.countable`：∀ {α : Sort u} [Countable α] {p : α → Prop}, Countabl
e { x // p x }
· 使用定理 `Finite.to_countable`：∀ {α : Sort u} [Finite α], Countable α
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `instSecondCountableTopologyReal`：SecondCountableTopology ℝ
· 使用定理 `BorelSpace.opensMeasurable`：∀ {α : Type u_6} [inst : TopologicalSpace α]
 [inst_1 : MeasurableSpace α] [BorelSpace α], OpensMeasurableSpace α
· 使用定理 `TopologicalSpace.instSecondCountableTopologyProd`：∀ {α : Type u} [t : To
pologicalSpace α] {β : Type u_1} [inst : TopologicalSpace β] [SecondCountableTop
ology α]   [SecondCountableTopology β]…
· 使用定理 `secondCountableTopologyEither_of_right`：∀ (α : Type u_6) (β : Type u_7) 
[inst : TopologicalSpace α] [inst_1 : TopologicalSpace β] [SecondCountableTopolo
gy β],   SecondCountableTopo…
· 使用定理 `TopologicalSpace.instSecondCountableTopologyForallOfCountable`：∀ {ι : Ty
pe u_1} {X : ι → Type u_2} [Countable ι] [inst : (a : ι) → TopologicalSpace (X a
)]   [∀ (a : ι), SecondCountableTopology (X a)], Se…
· 使用定理 `secondCountable_of_proper`：∀ {α : Type u} [inst : PseudoMetricSpace α] [
ProperSpace α], SecondCountableTopology α
· 使用定理 `Complex.instProperSpace`：ProperSpace ℂ
· 使用定理 `NumberField.mixedEmbedding.measurable_polarCoordReal_symm`：measurable_po
larCoordReal_symm : Measurable (polarCoordReal K).symm
-/
theorem measurable_polarCoord_symm :
    Measurable (mixedEmbedding.polarCoord K).symm := by
  rw [polarCoord_symm_eq]
  exact (Homeomorph.measurable _).comp (measurable_polarCoordReal_symm K)
/-
**NumberField.mixedEmbedding.normAtPlace_polarCoord_symm_of_isReal** 是 Mathlib 中
的一个定理，位于命名空间 `NumberField.mixedEmbedding`。
形式化陈述：normAtPlace_polarCoord_symm_of_isReal (x : realMixedSpace K) {w : Infinite
Place K} (hw : IsReal w) : normAtPlace w ((mixedEmbedding.polarCoord K).symm x) 
= ‖x.1 ⟨w, hw⟩‖
参数：x : realMixedSpace K；hw : IsReal w。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `NumberField.mixedEmbedding.polarCoord_symm_apply`：∀ (K : Type u_1) [inst
 : Field K] [inst_1 : NumberField K]   (p : ({ w // w.IsReal } → ℝ) × ({ w // w.
IsComplex } → ℝ × ℝ)),   ↑(NumberField…
· 使用定理 `NumberField.mixedEmbedding.normAtPlace_apply_of_isReal`：normAtPlace_appl
y_of_isReal {w : InfinitePlace K} (hw : IsReal w) (x : mixedSpace K) : normAtPla
ce w x = ‖x.1 ⟨w, hw⟩‖
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem normAtPlace_polarCoord_symm_of_isReal (x : realMixedSpace K) {w : InfinitePlace K}
    (hw : IsReal w) :
    normAtPlace w ((mixedEmbedding.polarCoord K).symm x) = ‖x.1 ⟨w, hw⟩‖ := by
  simp [normAtPlace_apply_of_isReal hw]
/-
**NumberField.mixedEmbedding.normAtPlace_polarCoord_symm_of_isComplex** 是 Mathli
b 中的一个定理，位于命名空间 `NumberField.mixedEmbedding`。
形式化陈述：normAtPlace_polarCoord_symm_of_isComplex (x : realMixedSpace K) {w : Infin
itePlace K} (hw : IsComplex w) : normAtPlace w ((mixedEmbedding.polarCoord K).sy
mm x) = ‖(x.2 ⟨w, hw⟩).1‖
参数：x : realMixedSpace K；hw : IsComplex w。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `NumberField.mixedEmbedding.polarCoord_symm_apply`：∀ (K : Type u_1) [inst
 : Field K] [inst_1 : NumberField K]   (p : ({ w // w.IsReal } → ℝ) × ({ w // w.
IsComplex } → ℝ × ℝ)),   ↑(NumberField…
· 使用定理 `NumberField.mixedEmbedding.normAtPlace_apply_of_isComplex`：normAtPlace_a
pply_of_isComplex {w : InfinitePlace K} (hw : IsComplex w) (x : mixedSpace K) : 
normAtPlace w x = ‖x.2 ⟨w, hw⟩‖
· 使用定理 `Complex.polarCoord_symm_apply`：∀ (p : ℝ × ℝ), ↑Complex.polarCoord.symm p
 = ↑p.1 * (↑(Real.cos p.2) + ↑(Real.sin p.2) * Complex.I)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Complex.ofReal_cos`：ofReal_cos (x : Real) : (Real.cos x : Complex) = cos
 x
· 使用定理 `Complex.ofReal_sin`：ofReal_sin (x : Real) : (Real.sin x : Complex) = sin
 x
· 使用定理 `Complex.norm_mul`：∀ (z w : ℂ), ‖z * w‖ = ‖z‖ * ‖w‖
· 使用引理 `Complex.norm_real`：norm_real (r : Real) : ‖(r : Complex)‖ = ‖r‖
· 使用定理 `Complex.norm_cos_add_sin_mul_I`：norm_cos_add_sin_mul_I (x : Real) : ‖cos
 x + sin x * I‖ = 1
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem normAtPlace_polarCoord_symm_of_isComplex (x : realMixedSpace K)
    {w : InfinitePlace K} (hw : IsComplex w) :
    normAtPlace w ((mixedEmbedding.polarCoord K).symm x) = ‖(x.2 ⟨w, hw⟩).1‖ := by
  simp [normAtPlace_apply_of_isComplex hw]

open scoped Classical in
/-
**NumberField.mixedEmbedding.integral_comp_polarCoord_symm** 是 Mathlib 中的一个定理，位于
命名空间 `NumberField.mixedEmbedding`。
形式化陈述：∀ (K : Type u_1) [inst : Field K] [inst_1 : NumberField K] {E : Type u_2} 
[inst_2 : NormedAddCommGroup E]   [inst_3 : NormedSpace ℝ E] (f : NumberField.mi
xedEmbedding.mixedSpace K → E),   ∫ (x : NumberField.mixedEmbedding.realMixedSpa
ce K) in (NumberField.mixedEmbedding.polarCoord K).target,       (∏ w, (x.2 w).1
) • f (↑(NumberField.mixedEmbedding.polarCoord K).symm x) =     ∫ (x : NumberFie
ld.mixedEmbedding.mixedSpace K), f x
参数：K : Type u_1；f : NumberField.mixedEmbedding.mixedSpace K → E；x : NumberField.
mixedEmbedding.realMixedSpace K；NumberField.mixedEmbedding.polarCoord K；∏ w, (x.
2 w).1；↑(NumberField.mixedEmbedding.polarCoord K).symm x；x : NumberField.mixedEm
bedding.mixedSpace K。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Complex.instFiniteDimensionalReal`：FiniteDimensional ℝ ℂ
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.MeasurePreserving.integral_comp`：∀ {α : Type u_1} {G : Typ
e u_5} [inst : NormedAddCommGroup G] [inst_1 : NormedSpace ℝ G] {m : MeasurableS
pace α}   {μ : MeasureTheory.Measur…
· 使用定理 `NumberField.mixedEmbedding.volume_preserving_mixedSpaceToRealMixedSpace_
symm`：volume_preserving_mixedSpaceToRealMixedSpace_symm : MeasurePreserving (mix
edSpaceToRealMixedSpace K).symm
· 使用引理 `Homeomorph.measurableEmbedding`：Homeomorph.measurableEmbedding (h : γ ≃ₜ
 γ₂) : MeasurableEmbedding h
· 使用定理 `Subtype.countable`：∀ {α : Sort u} [Countable α] {p : α → Prop}, Countabl
e { x // p x }
· 使用定理 `Finite.to_countable`：∀ {α : Sort u} [Finite α], Countable α
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `instSecondCountableTopologyReal`：SecondCountableTopology ℝ
· 使用定理 `TopologicalSpace.instSecondCountableTopologyProd`：∀ {α : Type u} [t : To
pologicalSpace α] {β : Type u_1} [inst : TopologicalSpace β] [SecondCountableTop
ology α]   [SecondCountableTopology β]…
· 使用定理 `secondCountableTopologyEither_of_right`：∀ (α : Type u_6) (β : Type u_7) 
[inst : TopologicalSpace α] [inst_1 : TopologicalSpace β] [SecondCountableTopolo
gy β],   SecondCountableTopo…
· 使用定理 `TopologicalSpace.instSecondCountableTopologyForallOfCountable`：∀ {ι : Ty
pe u_1} {X : ι → Type u_2} [Countable ι] [inst : (a : ι) → TopologicalSpace (X a
)]   [∀ (a : ι), SecondCountableTopology (X a)], Se…
· 使用定理 `secondCountable_of_proper`：∀ {α : Type u} [inst : PseudoMetricSpace α] [
ProperSpace α], SecondCountableTopology α
· 使用定理 `Complex.instProperSpace`：ProperSpace ℂ
· 使用定理 `NumberField.mixedEmbedding.integral_comp_polarCoordReal_symm`：integral_c
omp_polarCoordReal_symm {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E] 
(f : realMixedSpace K -> E) : ∫ x in (polarCoordRe…
· 使用定理 `NumberField.mixedEmbedding.polarCoord_target_eq_polarCoordReal_target`：p
olarCoord_target_eq_polarCoordReal_target : (mixedEmbedding.polarCoord K).target
 = (polarCoordReal K).target
· 使用定理 `NumberField.mixedEmbedding.polarCoord_symm_eq`：polarCoord_symm_eq : (mix
edEmbedding.polarCoord K).symm = (mixedSpaceToRealMixedSpace K).symm ∘ (polarCoo
rdReal K).symm
· 使用定理 `Function.comp_def`：∀ {α : Sort u_1} {β : Sort u_2} {δ : Sort u_3} (f : β
 → δ) (g : α → β), f ∘ g = fun x => f (g x)
-/
protected theorem integral_comp_polarCoord_symm {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : mixedSpace K → E) :
    ∫ x in (mixedEmbedding.polarCoord K).target,
      (∏ w : {w // IsComplex w}, (x.2 w).1) • f ((mixedEmbedding.polarCoord K).symm x) =
        ∫ x, f x := by
  rw [← (volume_preserving_mixedSpaceToRealMixedSpace_symm K).integral_comp
    (mixedSpaceToRealMixedSpace K).symm.measurableEmbedding, ← integral_comp_polarCoordReal_symm,
    polarCoord_target_eq_polarCoordReal_target, polarCoord_symm_eq, Function.comp_def]

open scoped Classical in
/-
**NumberField.mixedEmbedding.lintegral_comp_polarCoord_symm** 是 Mathlib 中的一个定理，位
于命名空间 `NumberField.mixedEmbedding`。
形式化陈述：∀ (K : Type u_1) [inst : Field K] [inst_1 : NumberField K] (f : NumberFiel
d.mixedEmbedding.mixedSpace K → ENNReal),   ∫⁻ (x : NumberField.mixedEmbedding.r
ealMixedSpace K) in (NumberField.mixedEmbedding.polarCoord K).target,       (∏ w
, ENNReal.ofReal (x.2 w).1) * f (↑(NumberField.mixedEmbedding.polarCoord K).symm
 x) =     ∫⁻ (x : NumberField.mixedEmbedding.mixedSpace K), f x
参数：K : Type u_1；f : NumberField.mixedEmbedding.mixedSpace K → ENNReal；x : Number
Field.mixedEmbedding.realMixedSpace K；NumberField.mixedEmbedding.polarCoord K；∏ 
w, ENNReal.ofReal (x.2 w).1；↑(NumberField.mixedEmbedding.polarCoord K).symm x；x 
: NumberField.mixedEmbedding.mixedSpace K。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Complex.instFiniteDimensionalReal`：FiniteDimensional ℝ ℂ
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.MeasurePreserving.lintegral_comp_emb`：lintegral_comp_emb (
hge : MeasurableEmbedding g) (f : β -> Real>=0∞) : ∫⁻ a, f (g a) ∂μ = ∫⁻ b, f b 
∂ν
· 使用定理 `NumberField.mixedEmbedding.volume_preserving_mixedSpaceToRealMixedSpace_
symm`：volume_preserving_mixedSpaceToRealMixedSpace_symm : MeasurePreserving (mix
edSpaceToRealMixedSpace K).symm
· 使用引理 `Homeomorph.measurableEmbedding`：Homeomorph.measurableEmbedding (h : γ ≃ₜ
 γ₂) : MeasurableEmbedding h
· 使用定理 `Subtype.countable`：∀ {α : Sort u} [Countable α] {p : α → Prop}, Countabl
e { x // p x }
· 使用定理 `Finite.to_countable`：∀ {α : Sort u} [Finite α], Countable α
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `instSecondCountableTopologyReal`：SecondCountableTopology ℝ
· 使用定理 `TopologicalSpace.instSecondCountableTopologyProd`：∀ {α : Type u} [t : To
pologicalSpace α] {β : Type u_1} [inst : TopologicalSpace β] [SecondCountableTop
ology α]   [SecondCountableTopology β]…
· 使用定理 `secondCountableTopologyEither_of_right`：∀ (α : Type u_6) (β : Type u_7) 
[inst : TopologicalSpace α] [inst_1 : TopologicalSpace β] [SecondCountableTopolo
gy β],   SecondCountableTopo…
· 使用定理 `TopologicalSpace.instSecondCountableTopologyForallOfCountable`：∀ {ι : Ty
pe u_1} {X : ι → Type u_2} [Countable ι] [inst : (a : ι) → TopologicalSpace (X a
)]   [∀ (a : ι), SecondCountableTopology (X a)], Se…
· 使用定理 `secondCountable_of_proper`：∀ {α : Type u} [inst : PseudoMetricSpace α] [
ProperSpace α], SecondCountableTopology α
· 使用定理 `Complex.instProperSpace`：ProperSpace ℂ
· 使用定理 `NumberField.mixedEmbedding.lintegral_comp_polarCoordReal_symm`：lintegral
_comp_polarCoordReal_symm (f : realMixedSpace K -> Real>=0∞) : ∫⁻ x in (polarCoo
rdReal K).target, (∏ w : {w // IsComplex w}, .ofRea…
· 使用定理 `NumberField.mixedEmbedding.polarCoord_target_eq_polarCoordReal_target`：p
olarCoord_target_eq_polarCoordReal_target : (mixedEmbedding.polarCoord K).target
 = (polarCoordReal K).target
· 使用定理 `NumberField.mixedEmbedding.polarCoord_symm_eq`：polarCoord_symm_eq : (mix
edEmbedding.polarCoord K).symm = (mixedSpaceToRealMixedSpace K).symm ∘ (polarCoo
rdReal K).symm
· 使用定理 `Function.comp_def`：∀ {α : Sort u_1} {β : Sort u_2} {δ : Sort u_3} (f : β
 → δ) (g : α → β), f ∘ g = fun x => f (g x)
-/
protected theorem lintegral_comp_polarCoord_symm (f : mixedSpace K → ℝ≥0∞) :
    ∫⁻ x in (mixedEmbedding.polarCoord K).target, (∏ w : {w // IsComplex w}, .ofReal (x.2 w).1) *
      f ((mixedEmbedding.polarCoord K).symm x) = ∫⁻ x, f x := by
  rw [← (volume_preserving_mixedSpaceToRealMixedSpace_symm K).lintegral_comp_emb
    (mixedSpaceToRealMixedSpace K).symm.measurableEmbedding, ← lintegral_comp_polarCoordReal_symm,
    polarCoord_target_eq_polarCoordReal_target, polarCoord_symm_eq, Function.comp_def]

end mixedSpace

noncomputable section polarSpace

open MeasurableEquiv

/--
The space `ℝ^(r₁+r₂) × ℝ^r₂`, it is homeomorphic to the `realMixedSpace`, see
`homeoRealMixedSpacePolarSpace`.
-/
/-
**NumberField.mixedEmbedding.polarSpace** 是 Mathlib 中的一个缩写定义，位于命名空间 `NumberField
.mixedEmbedding`。
形式化陈述：polarSpace
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The space `ℝ^(r₁+r₂) × ℝ^r₂`, it is homeomorphic to the `realMixedSpace`, see
`homeoRealMixedSpacePolarSpace`.
-/
abbrev polarSpace := ((InfinitePlace K) → ℝ) × ({w : InfinitePlace K // w.IsComplex} → ℝ)

open scoped Classical in
/--
The measurable equivalence between the `realMixedSpace` and the `polarSpace`. It is actually an
homeomorphism, see `homeoRealMixedSpacePolarSpace`, but defining it in this way makes it easier
to prove that it is volume preserving, see `volume_preserving_homeoRealMixedSpacePolarSpace`.
-/
/-
**NumberField.mixedEmbedding.measurableEquivRealMixedSpacePolarSpace** 是 Mathlib
 中的一个定义，位于命名空间 `NumberField.mixedEmbedding`。
形式化陈述：measurableEquivRealMixedSpacePolarSpace : realMixedSpace K ≃ᵐ polarSpace K
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The measurable equivalence between the `realMixedSpace` and the `polarSpace`. It
 is actually an
homeomorphism, see `homeoRealMixedSpacePolarSpace`, but defining it in this way 
makes it easier
to prove that it is volume preserving, see `volume_preserving_homeoRealMixedSpac
ePolarSpace`.
-/
def measurableEquivRealMixedSpacePolarSpace : realMixedSpace K ≃ᵐ polarSpace K :=
  MeasurableEquiv.trans (prodCongr (refl _)
    (arrowProdEquivProdArrow ℝ ℝ _)) <|
    MeasurableEquiv.trans prodAssoc.symm <|
      MeasurableEquiv.trans
        (prodCongr (prodCongr (refl _)
          (arrowCongr' (Equiv.subtypeEquivRight (fun _ ↦ not_isReal_iff_isComplex.symm)) (refl _)))
            (refl _))
          (prodCongr (piEquivPiSubtypeProd (fun _ ↦ ℝ) _).symm (refl _))

open scoped Classical in
/--
The homeomorphism between the `realMixedSpace` and the `polarSpace`.
-/
/-
**NumberField.mixedEmbedding.homeoRealMixedSpacePolarSpace** 是 Mathlib 中的一个定义，位于
命名空间 `NumberField.mixedEmbedding`。
形式化陈述：homeoRealMixedSpacePolarSpace : realMixedSpace K ≃ₜ polarSpace K
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The homeomorphism between the `realMixedSpace` and the `polarSpace`.
-/
def homeoRealMixedSpacePolarSpace : realMixedSpace K ≃ₜ polarSpace K :=
{ measurableEquivRealMixedSpacePolarSpace K with
  continuous_toFun := by
    change Continuous fun x : realMixedSpace K ↦ (fun w ↦ if hw : w.IsReal then x.1 ⟨w, hw⟩ else
      (x.2 ⟨w, not_isReal_iff_isComplex.mp hw⟩).1, fun w ↦ (x.2 w).2)
    refine .prodMk (continuous_pi fun w ↦ ?_) (by fun_prop)
    split_ifs <;> fun_prop
  continuous_invFun := by
    change Continuous fun x : polarSpace K ↦
      (⟨fun w ↦ x.1 w.val, fun w ↦ ⟨x.1 w.val, x.2 w⟩⟩ : realMixedSpace K)
    fun_prop }

open scoped Classical in
/-
**NumberField.mixedEmbedding.homeoRealMixedSpacePolarSpace_apply** 是 Mathlib 中的一
个定理，位于命名空间 `NumberField.mixedEmbedding`。
形式化陈述：homeoRealMixedSpacePolarSpace_apply (x : realMixedSpace K) : homeoRealMixe
dSpacePolarSpace K x = ⟨fun w => if hw : w.IsReal then x.1 ⟨w, hw⟩ else (x.2 ⟨w,
 not_isReal_iff_isComplex.mp hw⟩).1, fun w => (x.2 w).2⟩
参数：x : realMixedSpace K。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem homeoRealMixedSpacePolarSpace_apply (x : realMixedSpace K) :
    homeoRealMixedSpacePolarSpace K x =
      ⟨fun w ↦ if hw : w.IsReal then x.1 ⟨w, hw⟩ else
        (x.2 ⟨w, not_isReal_iff_isComplex.mp hw⟩).1, fun w ↦ (x.2 w).2⟩ := rfl
/-
**NumberField.mixedEmbedding.homeoRealMixedSpacePolarSpace_apply_fst_ofIsReal** 
是 Mathlib 中的一个定理，位于命名空间 `NumberField.mixedEmbedding`。
形式化陈述：homeoRealMixedSpacePolarSpace_apply_fst_ofIsReal (x : realMixedSpace K) (w
 : {w // IsReal w}) : (homeoRealMixedSpacePolarSpace K x).1 w.1 = x.1 w
参数：x : realMixedSpace K；w : {w // IsReal w}。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `NumberField.InfinitePlace.not_isReal_iff_isComplex`：not_isReal_iff_isCom
plex {w : InfinitePlace K} : ¬IsReal w ↔ IsComplex w
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Subtype.prop`：prop (x : Subtype p) : p x
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `dif_pos`：∀ {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t : c → α
} {e : ¬c → α}, dite c t e = t hc
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem homeoRealMixedSpacePolarSpace_apply_fst_ofIsReal (x : realMixedSpace K)
    (w : {w // IsReal w}) :
    (homeoRealMixedSpacePolarSpace K x).1 w.1 = x.1 w := by
  simp_rw [homeoRealMixedSpacePolarSpace_apply, dif_pos w.prop]
/-
**NumberField.mixedEmbedding.homeoRealMixedSpacePolarSpace_apply_fst_ofIsComplex
** 是 Mathlib 中的一个定理，位于命名空间 `NumberField.mixedEmbedding`。
形式化陈述：homeoRealMixedSpacePolarSpace_apply_fst_ofIsComplex (x : realMixedSpace K)
 (w : {w // IsComplex w}) : (homeoRealMixedSpacePolarSpace K x).1 w.1 = (x.2 w).
1
参数：x : realMixedSpace K；w : {w // IsComplex w}。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `NumberField.InfinitePlace.not_isReal_iff_isComplex`：not_isReal_iff_isCom
plex {w : InfinitePlace K} : ¬IsReal w ↔ IsComplex w
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Subtype.prop`：prop (x : Subtype p) : p x
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `dif_neg`：∀ {c : Prop} {h : Decidable c} (hnc : ¬c) {α : Sort u} {t : c →
 α} {e : ¬c → α}, dite c t e = e hnc
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem homeoRealMixedSpacePolarSpace_apply_fst_ofIsComplex (x : realMixedSpace K)
    (w : {w // IsComplex w}) :
    (homeoRealMixedSpacePolarSpace K x).1 w.1 = (x.2 w).1 := by
  simp_rw [homeoRealMixedSpacePolarSpace_apply, dif_neg (not_isReal_iff_isComplex.mpr w.prop)]
/-
**NumberField.mixedEmbedding.homeoRealMixedSpacePolarSpace_apply_snd** 是 Mathlib
 中的一个定理，位于命名空间 `NumberField.mixedEmbedding`。
形式化陈述：homeoRealMixedSpacePolarSpace_apply_snd (x : realMixedSpace K) (w : {w // 
IsComplex w}) : (homeoRealMixedSpacePolarSpace K x).2 w = (x.2 w).2
参数：x : realMixedSpace K；w : {w // IsComplex w}。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem homeoRealMixedSpacePolarSpace_apply_snd (x : realMixedSpace K) (w : {w // IsComplex w}) :
    (homeoRealMixedSpacePolarSpace K x).2 w = (x.2 w).2 := rfl

@[simp]
/-
**NumberField.mixedEmbedding.homeoRealMixedSpacePolarSpace_symm_apply** 是 Mathli
b 中的一个定理，位于命名空间 `NumberField.mixedEmbedding`。
形式化陈述：homeoRealMixedSpacePolarSpace_symm_apply (x : polarSpace K) : (homeoRealMi
xedSpacePolarSpace K).symm x = ⟨fun w => x.1 w, fun w => (x.1 w, x.2 w)⟩
参数：x : polarSpace K。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem homeoRealMixedSpacePolarSpace_symm_apply (x : polarSpace K) :
    (homeoRealMixedSpacePolarSpace K).symm x = ⟨fun w ↦ x.1 w, fun w ↦ (x.1 w, x.2 w)⟩ := rfl

open scoped Classical in
/-
**NumberField.mixedEmbedding.volume_preserving_homeoRealMixedSpacePolarSpace** 是
 Mathlib 中的一个定理，位于命名空间 `NumberField.mixedEmbedding`。
形式化陈述：volume_preserving_homeoRealMixedSpacePolarSpace [NumberField K] : MeasureP
reserving (homeoRealMixedSpacePolarSpace K)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.MeasurePreserving.trans`：∀ {α : Type u_1} {β : Type u_2} {
γ : Type u_3} [inst : MeasurableSpace α] [inst_1 : MeasurableSpace β]   [inst_2 
: MeasurableSpace γ] {e : α…
· 使用定理 `MeasureTheory.MeasurePreserving.prod`：∀ {α : Type u_1} {β : Type u_2} {γ
 : Type u_3} [inst : MeasurableSpace α] [inst_1 : MeasurableSpace β]   [inst_2 :
 MeasurableSpace γ] {δ : T…
· 使用定理 `MeasureTheory.instSFiniteOfSigmaFinite`：∀ {α : Type u_1} {m0 : Measurabl
eSpace α} {μ : MeasureTheory.Measure α} [MeasureTheory.SigmaFinite μ],   Measure
Theory.SFinite μ
· 使用定理 `MeasureTheory.Measure.instSigmaFiniteForallVolume`：∀ {ι : Type u_1} [ins
t : Fintype ι] {α : ι → Type u_4} [inst_1 : (i : ι) → MeasureTheory.MeasureSpace
 (α i)]   [∀ (i : ι), MeasureTheory.Sig…
· 使用定理 `MeasureTheory.Measure.IsAddHaarMeasure.sigmaFinite`：∀ {G : Type u_1} [in
st : MeasurableSpace G] [inst_1 : AddGroup G] [inst_2 : TopologicalSpace G]   (μ
 : MeasureTheory.Measure G) [μ.IsAddHaar…
· 使用定理 `instIsAddHaarMeasureVolume`：∀ {E : Type u_3} [inst : NormedAddCommGroup 
E] [inst_1 : InnerProductSpace ℝ E] [inst_2 : FiniteDimensional ℝ E]   [inst_3 :
 MeasurableSpace…
· 使用定理 `SeparableWeaklyLocallyCompactAddGroup.sigmaCompactSpace`：∀ {G : Type w} 
[inst : TopologicalSpace G] [inst_1 : AddGroup G] [IsTopologicalAddGroup G]   [T
opologicalSpace.SeparableSpace G] [WeaklyLoca…
· 使用定理 `instIsTopologicalAddGroupReal`：IsTopologicalAddGroup ℝ
· 使用定理 `TopologicalSpace.SecondCountableTopology.to_separableSpace`：∀ {α : Type 
u} [t : TopologicalSpace α] [SecondCountableTopology α], TopologicalSpace.Separa
bleSpace α
· 使用定理 `instSecondCountableTopologyReal`：SecondCountableTopology ℝ
· 使用定理 `instWeaklyLocallyCompactSpaceOfLocallyCompactSpace`：∀ {X : Type u_1} [in
st : TopologicalSpace X] [LocallyCompactSpace X], WeaklyLocallyCompactSpace X
· 使用定理 `locallyCompact_of_proper`：∀ {α : Type u} [inst : PseudoMetricSpace α] [P
roperSpace α], LocallyCompactSpace α
· 使用定理 `instProperSpaceReal`：ProperSpace ℝ
· 使用定理 `MeasureTheory.Measure.instSigmaFiniteProdVolume`：∀ {α : Type u_4} {β : T
ype u_5} [inst : MeasureTheory.MeasureSpace α] [MeasureTheory.SigmaFinite Measur
eTheory.volume]   [inst_2 : MeasureTh…
· 使用定理 `MeasureTheory.MeasurePreserving.id`：∀ {α : Type u_1} [inst : MeasurableS
pace α] (μ : MeasureTheory.Measure α), MeasureTheory.MeasurePreserving id μ μ
· 使用定理 `MeasureTheory.volume_measurePreserving_arrowProdEquivProdArrow`：volume_m
easurePreserving_arrowProdEquivProdArrow (α β γ : Type*) [MeasureSpace α] [Measu
reSpace β] [Fintype γ] [SigmaFinite (volume : Measur…
· 使用定理 `MeasureTheory.MeasurePreserving.symm`：symm (e : α ≃ᵐ β) {μa : Measure α}
 {μb : Measure β} (h : MeasurePreserving e μa μb) : MeasurePreserving e.symm μb 
μa
· 使用定理 `MeasureTheory.volume_preserving_prodAssoc`：∀ {α₁ : Type u_4} {β₁ : Type 
u_5} {γ₁ : Type u_6} [inst : MeasureTheory.MeasureSpace α₁]   [inst_1 : MeasureT
heory.MeasureSpace β₁] [inst_2 …
· 使用定理 `MeasureTheory.Measure.prod.instSFinite`：∀ {α : Type u_4} {β : Type u_5} 
{x : MeasurableSpace α} {μ : MeasureTheory.Measure α} [MeasureTheory.SFinite μ] 
  {x_1 : MeasurableSpace β} …
· 使用定理 `MeasureTheory.volume_preserving_arrowCongr'`：volume_preserving_arrowCong
r' {α₁ β₁ α₂ β₂ : Type*} [Fintype α₁] [Fintype α₂] [MeasureSpace β₁] [MeasureSpa
ce β₂] [SigmaFinite (volume : Mea…
· 使用定理 `MeasureTheory.Measure.instSFiniteProdVolume`：∀ {α : Type u_4} {β : Type 
u_5} [inst : MeasureTheory.MeasureSpace α] [MeasureTheory.SFinite MeasureTheory.
volume]   [inst_2 : MeasureTheory…
· 使用定理 `MeasureTheory.volume_preserving_piEquivPiSubtypeProd`：volume_preserving_
piEquivPiSubtypeProd (α : ι -> Type*) [forall i, MeasureSpace (α i)] [forall i, 
SigmaFinite (volume : Measure (α i))] (p :…
-/
theorem volume_preserving_homeoRealMixedSpacePolarSpace [NumberField K] :
    MeasurePreserving (homeoRealMixedSpacePolarSpace K) :=
  ((MeasurePreserving.id volume).prod
    (volume_measurePreserving_arrowProdEquivProdArrow ℝ ℝ _)).trans <|
      (volume_preserving_prodAssoc.symm).trans <|
        (((MeasurePreserving.id volume).prod (volume_preserving_arrowCongr' _
          (MeasurableEquiv.refl ℝ) (.id volume))).prod (.id volume)).trans <|
            ((volume_preserving_piEquivPiSubtypeProd
              (fun _ : InfinitePlace K ↦ ℝ) (fun w ↦ IsReal w)).symm).prod (.id volume)

/--
The polar coordinate open partial homeomorphism between the mixed space `ℝ^r₁ × ℂ^r₂` and the polar
space `ℝ^(r₁ + r₂) × ℝ^r₂` defined by sending `x` to `x w` or `‖x w‖` depending on whether `w` is
real or complex for the first component, and to `Arg (x w)`, `w` complex, for the second component.
-/
@[simps!]
/-
**NumberField.mixedEmbedding.polarSpaceCoord** 是 Mathlib 中的一个定义，位于命名空间 `NumberFi
eld.mixedEmbedding`。
形式化陈述：polarSpaceCoord [NumberField K] : OpenPartialHomeomorph (mixedSpace K) (po
larSpace K)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The polar coordinate open partial homeomorphism between the mixed space `ℝ^r₁ × 
ℂ^r₂` and the polar
space `ℝ^(r₁ + r₂) × ℝ^r₂` defined by sending `x` to `x w` or `‖x w‖` depending 
on whether `w` is
real or complex for the first component, and to `Arg (x w)`, `w` complex, for th
e second component.
-/
def polarSpaceCoord [NumberField K] : OpenPartialHomeomorph (mixedSpace K) (polarSpace K) :=
    (mixedEmbedding.polarCoord K).transHomeomorph (homeoRealMixedSpacePolarSpace K)
/-
**NumberField.mixedEmbedding.measurable_polarSpaceCoord_symm** 是 Mathlib 中的一个定理，
位于命名空间 `NumberField.mixedEmbedding`。
形式化陈述：measurable_polarSpaceCoord_symm [NumberField K] : Measurable (polarSpaceCo
ord K).symm
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `NumberField.mixedEmbedding.polarSpaceCoord.eq_1`：∀ (K : Type u_1) [inst 
: Field K] [inst_1 : NumberField K],   NumberField.mixedEmbedding.polarSpaceCoor
d K =     (NumberField.mixedEmbedding…
· 使用定理 `OpenPartialHomeomorph.transHomeomorph_symm_apply`：∀ {X : Type u_1} {Y : 
Type u_3} {Z : Type u_5} [inst : TopologicalSpace X] [inst_1 : TopologicalSpace 
Y]   [inst_2 : TopologicalSpace Z] (e …
· 使用定理 `Measurable.comp`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {x : Mea
surableSpace α} {x_1 : MeasurableSpace β}   {x_2 : MeasurableSpace γ} {g : β → γ
} {f …
· 使用定理 `NumberField.mixedEmbedding.measurable_polarCoord_symm`：measurable_polarC
oord_symm : Measurable (mixedEmbedding.polarCoord K).symm
· 使用定理 `Homeomorph.measurable`：∀ {α : Type u_1} {γ : Type u_3} [inst : Topologic
alSpace α] [inst_1 : MeasurableSpace α] [OpensMeasurableSpace α]   [inst_3 : Top
ologicalSpa…
· 使用定理 `Finite.to_countable`：∀ {α : Sort u} [Finite α], Countable α
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `instSecondCountableTopologyReal`：SecondCountableTopology ℝ
· 使用定理 `BorelSpace.opensMeasurable`：∀ {α : Type u_6} [inst : TopologicalSpace α]
 [inst_1 : MeasurableSpace α] [BorelSpace α], OpensMeasurableSpace α
· 使用定理 `Subtype.countable`：∀ {α : Sort u} [Countable α] {p : α → Prop}, Countabl
e { x // p x }
· 使用定理 `secondCountableTopologyEither_of_right`：∀ (α : Type u_6) (β : Type u_7) 
[inst : TopologicalSpace α] [inst_1 : TopologicalSpace β] [SecondCountableTopolo
gy β],   SecondCountableTopo…
· 使用定理 `TopologicalSpace.instSecondCountableTopologyForallOfCountable`：∀ {ι : Ty
pe u_1} {X : ι → Type u_2} [Countable ι] [inst : (a : ι) → TopologicalSpace (X a
)]   [∀ (a : ι), SecondCountableTopology (X a)], Se…
· 使用定理 `TopologicalSpace.instSecondCountableTopologyProd`：∀ {α : Type u} [t : To
pologicalSpace α] {β : Type u_1} [inst : TopologicalSpace β] [SecondCountableTop
ology α]   [SecondCountableTopology β]…
-/
theorem measurable_polarSpaceCoord_symm [NumberField K] :
    Measurable (polarSpaceCoord K).symm := by
  rw [polarSpaceCoord, OpenPartialHomeomorph.transHomeomorph_symm_apply]
  exact (measurable_polarCoord_symm K).comp (Homeomorph.measurable _)

open scoped Classical in
/-
**NumberField.mixedEmbedding.polarSpaceCoord_target'** 是 Mathlib 中的一个定理，位于命名空间 `
NumberField.mixedEmbedding`。
形式化陈述：polarSpaceCoord_target' [NumberField K] : (polarSpaceCoord K).target = (Se
t.univ.pi fun w => if w.IsReal then Set.univ else Set.Ioi 0) ×ˢ (Set.univ.pi fun
 _ => Set.Ioo (-π) π)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `NumberField.mixedEmbedding.polarSpaceCoord_target`：∀ (K : Type u_1) [ins
t : Field K] [inst_1 : NumberField K],   (NumberField.mixedEmbedding.polarSpaceC
oord K).target =     ⇑(NumberField.mixe…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem polarSpaceCoord_target' [NumberField K] :
    (polarSpaceCoord K).target =
      (Set.univ.pi fun w ↦ if w.IsReal then Set.univ else Set.Ioi 0) ×ˢ
        (Set.univ.pi fun _ ↦ Set.Ioo (-π) π) := by
  ext
  simp_rw [polarSpaceCoord_target, Set.mem_preimage, homeoRealMixedSpacePolarSpace_symm_apply,
    Set.mem_prod, Set.mem_univ, true_and, Set.mem_univ_pi, Set.mem_ite_univ_left,
    not_isReal_iff_isComplex, Subtype.forall, Complex.polarCoord_target, Set.mem_prod, forall_and]

open scoped Classical in
/-
**NumberField.mixedEmbedding.integral_comp_polarSpaceCoord_symm** 是 Mathlib 中的一个
定理，位于命名空间 `NumberField.mixedEmbedding`。
形式化陈述：integral_comp_polarSpaceCoord_symm [NumberField K] {E : Type*} [NormedAddC
ommGroup E] [NormedSpace Real E] (f : mixedSpace K -> E) : ∫ x in (polarSpaceCoo
rd K).target, (∏ w : {w // IsComplex w}, x.1 w.1) • f ((polarSpaceCoord K).symm 
x) = ∫ x, f x
参数：f : mixedSpace K -> E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Complex.instFiniteDimensionalReal`：FiniteDimensional ℝ ℂ
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.MeasurePreserving.setIntegral_preimage_emb`：∀ {X : Type u_
1} {E : Type u_3} {mX : MeasurableSpace X} [inst : NormedAddCommGroup E] [inst_1
 : NormedSpace ℝ E]   {μ : MeasureTheory.Measu…
· 使用定理 `NumberField.mixedEmbedding.volume_preserving_homeoRealMixedSpacePolarSpa
ce`：volume_preserving_homeoRealMixedSpacePolarSpace [NumberField K] : MeasurePre
serving (homeoRealMixedSpacePolarSpace K)
· 使用引理 `Homeomorph.measurableEmbedding`：Homeomorph.measurableEmbedding (h : γ ≃ₜ
 γ₂) : MeasurableEmbedding h
· 使用定理 `Subtype.countable`：∀ {α : Sort u} [Countable α] {p : α → Prop}, Countabl
e { x // p x }
· 使用定理 `Finite.to_countable`：∀ {α : Sort u} [Finite α], Countable α
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `instSecondCountableTopologyReal`：SecondCountableTopology ℝ
· 使用定理 `TopologicalSpace.instSecondCountableTopologyProd`：∀ {α : Type u} [t : To
pologicalSpace α] {β : Type u_1} [inst : TopologicalSpace β] [SecondCountableTop
ology α]   [SecondCountableTopology β]…
· 使用定理 `secondCountableTopologyEither_of_right`：∀ (α : Type u_6) (β : Type u_7) 
[inst : TopologicalSpace α] [inst_1 : TopologicalSpace β] [SecondCountableTopolo
gy β],   SecondCountableTopo…
· 使用定理 `TopologicalSpace.instSecondCountableTopologyForallOfCountable`：∀ {ι : Ty
pe u_1} {X : ι → Type u_2} [Countable ι] [inst : (a : ι) → TopologicalSpace (X a
)]   [∀ (a : ι), SecondCountableTopology (X a)], Se…
· 使用定理 `NumberField.mixedEmbedding.integral_comp_polarCoord_symm`：∀ (K : Type u_
1) [inst : Field K] [inst_1 : NumberField K] {E : Type u_2} [inst_2 : NormedAddC
ommGroup E]   [inst_3 : NormedSpace ℝ E] (f : …
· 使用定理 `NumberField.mixedEmbedding.polarSpaceCoord_target`：∀ (K : Type u_1) [ins
t : Field K] [inst_1 : NumberField K],   (NumberField.mixedEmbedding.polarSpaceC
oord K).target =     ⇑(NumberField.mixe…
· 使用定理 `Homeomorph.image_eq_preimage_symm`：image_eq_preimage_symm (h : X ≃ₜ Y) (
s : Set X) : h '' s = h.symm ⁻¹' s
· 使用定理 `Homeomorph.preimage_image`：preimage_image (h : X ≃ₜ Y) (s : Set X) : h ⁻
¹' h '' s = s
· 使用定理 `NumberField.mixedEmbedding.polarCoord_target`：∀ (K : Type u_1) [inst : F
ield K] [inst_1 : NumberField K],   (NumberField.mixedEmbedding.polarCoord K).ta
rget = Set.univ ×ˢ Set.univ.pi fun…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `NumberField.mixedEmbedding.polarSpaceCoord_symm_apply`：∀ (K : Type u_1) 
[inst : Field K] [inst_1 : NumberField K] (a : NumberField.mixedEmbedding.polarS
pace K),   ↑(NumberField.mixedEmbedding.pol…
· 使用定理 `NumberField.mixedEmbedding.polarCoord_symm_apply`：∀ (K : Type u_1) [inst
 : Field K] [inst_1 : NumberField K]   (p : ({ w // w.IsReal } → ℝ) × ({ w // w.
IsComplex } → ℝ × ℝ)),   ↑(NumberField…
· 使用定理 `NumberField.mixedEmbedding.homeoRealMixedSpacePolarSpace_apply_fst_ofIsR
eal`：homeoRealMixedSpacePolarSpace_apply_fst_ofIsReal (x : realMixedSpace K) (w 
: {w // IsReal w}) : (homeoRealMixedSpacePolarSpace K x).1 w.1 = …
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Finset.prod_congr`：prod_congr (h : s₁ = s₂) : (forall x in s₂, f x = g x
) -> s₁.prod f = s₂.prod g
· 使用定理 `NumberField.mixedEmbedding.homeoRealMixedSpacePolarSpace_apply_fst_ofIsC
omplex`：homeoRealMixedSpacePolarSpace_apply_fst_ofIsComplex (x : realMixedSpace 
K) (w : {w // IsComplex w}) : (homeoRealMixedSpacePolarSpace K x).1 …
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem integral_comp_polarSpaceCoord_symm [NumberField K] {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (f : mixedSpace K → E) :
    ∫ x in (polarSpaceCoord K).target,
      (∏ w : {w // IsComplex w}, x.1 w.1) • f ((polarSpaceCoord K).symm x) = ∫ x, f x := by
  rw [← (volume_preserving_homeoRealMixedSpacePolarSpace K).setIntegral_preimage_emb
    (homeoRealMixedSpacePolarSpace K).measurableEmbedding,
    ← mixedEmbedding.integral_comp_polarCoord_symm, polarSpaceCoord_target,
    ← Homeomorph.image_eq_preimage_symm, Homeomorph.preimage_image,
    mixedEmbedding.polarCoord_target]
  simp_rw [polarSpaceCoord_symm_apply, mixedEmbedding.polarCoord_symm_apply,
    homeoRealMixedSpacePolarSpace_apply_fst_ofIsReal,
    homeoRealMixedSpacePolarSpace_apply_fst_ofIsComplex, homeoRealMixedSpacePolarSpace_apply_snd]

open scoped Classical in
/-
**NumberField.mixedEmbedding.lintegral_comp_polarSpaceCoord_symm** 是 Mathlib 中的一
个定理，位于命名空间 `NumberField.mixedEmbedding`。
形式化陈述：lintegral_comp_polarSpaceCoord_symm [NumberField K] (f : mixedSpace K -> R
eal>=0∞) : ∫⁻ x in (polarSpaceCoord K).target, (∏ w : {w // IsComplex w}, .ofRea
l (x.1 w.1)) * f ((polarSpaceCoord K).symm x) = ∫⁻ x, f x
参数：f : mixedSpace K -> Real>=0∞。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Complex.instFiniteDimensionalReal`：FiniteDimensional ℝ ℂ
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.MeasurePreserving.setLIntegral_comp_preimage_emb`：setLInte
gral_comp_preimage_emb (hge : MeasurableEmbedding g) (f : β -> Real>=0∞) (s : Se
t β) : ∫⁻ a in g ⁻¹' s, f (g a) ∂μ = ∫⁻ b in s, f b …
· 使用定理 `NumberField.mixedEmbedding.volume_preserving_homeoRealMixedSpacePolarSpa
ce`：volume_preserving_homeoRealMixedSpacePolarSpace [NumberField K] : MeasurePre
serving (homeoRealMixedSpacePolarSpace K)
· 使用引理 `Homeomorph.measurableEmbedding`：Homeomorph.measurableEmbedding (h : γ ≃ₜ
 γ₂) : MeasurableEmbedding h
· 使用定理 `Subtype.countable`：∀ {α : Sort u} [Countable α] {p : α → Prop}, Countabl
e { x // p x }
· 使用定理 `Finite.to_countable`：∀ {α : Sort u} [Finite α], Countable α
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `instSecondCountableTopologyReal`：SecondCountableTopology ℝ
· 使用定理 `TopologicalSpace.instSecondCountableTopologyProd`：∀ {α : Type u} [t : To
pologicalSpace α] {β : Type u_1} [inst : TopologicalSpace β] [SecondCountableTop
ology α]   [SecondCountableTopology β]…
· 使用定理 `secondCountableTopologyEither_of_right`：∀ (α : Type u_6) (β : Type u_7) 
[inst : TopologicalSpace α] [inst_1 : TopologicalSpace β] [SecondCountableTopolo
gy β],   SecondCountableTopo…
· 使用定理 `TopologicalSpace.instSecondCountableTopologyForallOfCountable`：∀ {ι : Ty
pe u_1} {X : ι → Type u_2} [Countable ι] [inst : (a : ι) → TopologicalSpace (X a
)]   [∀ (a : ι), SecondCountableTopology (X a)], Se…
· 使用定理 `NumberField.mixedEmbedding.lintegral_comp_polarCoord_symm`：∀ (K : Type u
_1) [inst : Field K] [inst_1 : NumberField K] (f : NumberField.mixedEmbedding.mi
xedSpace K → ENNReal),   ∫⁻ (x : NumberField.mi…
· 使用定理 `NumberField.mixedEmbedding.polarSpaceCoord_target`：∀ (K : Type u_1) [ins
t : Field K] [inst_1 : NumberField K],   (NumberField.mixedEmbedding.polarSpaceC
oord K).target =     ⇑(NumberField.mixe…
· 使用定理 `Homeomorph.image_eq_preimage_symm`：image_eq_preimage_symm (h : X ≃ₜ Y) (
s : Set X) : h '' s = h.symm ⁻¹' s
· 使用定理 `Homeomorph.preimage_image`：preimage_image (h : X ≃ₜ Y) (s : Set X) : h ⁻
¹' h '' s = s
· 使用定理 `NumberField.mixedEmbedding.polarCoord_target`：∀ (K : Type u_1) [inst : F
ield K] [inst_1 : NumberField K],   (NumberField.mixedEmbedding.polarCoord K).ta
rget = Set.univ ×ˢ Set.univ.pi fun…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `NumberField.mixedEmbedding.polarSpaceCoord_symm_apply`：∀ (K : Type u_1) 
[inst : Field K] [inst_1 : NumberField K] (a : NumberField.mixedEmbedding.polarS
pace K),   ↑(NumberField.mixedEmbedding.pol…
· 使用定理 `NumberField.mixedEmbedding.polarCoord_symm_apply`：∀ (K : Type u_1) [inst
 : Field K] [inst_1 : NumberField K]   (p : ({ w // w.IsReal } → ℝ) × ({ w // w.
IsComplex } → ℝ × ℝ)),   ↑(NumberField…
· 使用定理 `NumberField.mixedEmbedding.homeoRealMixedSpacePolarSpace_apply_fst_ofIsR
eal`：homeoRealMixedSpacePolarSpace_apply_fst_ofIsReal (x : realMixedSpace K) (w 
: {w // IsReal w}) : (homeoRealMixedSpacePolarSpace K x).1 w.1 = …
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Finset.prod_congr`：prod_congr (h : s₁ = s₂) : (forall x in s₂, f x = g x
) -> s₁.prod f = s₂.prod g
· 使用定理 `NumberField.mixedEmbedding.homeoRealMixedSpacePolarSpace_apply_fst_ofIsC
omplex`：homeoRealMixedSpacePolarSpace_apply_fst_ofIsComplex (x : realMixedSpace 
K) (w : {w // IsComplex w}) : (homeoRealMixedSpacePolarSpace K x).1 …
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem lintegral_comp_polarSpaceCoord_symm [NumberField K] (f : mixedSpace K → ℝ≥0∞) :
    ∫⁻ x in (polarSpaceCoord K).target,
      (∏ w : {w // IsComplex w}, .ofReal (x.1 w.1)) * f ((polarSpaceCoord K).symm x) =
        ∫⁻ x, f x := by
  rw [← (volume_preserving_homeoRealMixedSpacePolarSpace K).setLIntegral_comp_preimage_emb
    (homeoRealMixedSpacePolarSpace K).measurableEmbedding,
    ← mixedEmbedding.lintegral_comp_polarCoord_symm, polarSpaceCoord_target,
    ← Homeomorph.image_eq_preimage_symm, Homeomorph.preimage_image,
    mixedEmbedding.polarCoord_target]
  simp_rw [polarSpaceCoord_symm_apply, mixedEmbedding.polarCoord_symm_apply,
    homeoRealMixedSpacePolarSpace_apply_fst_ofIsReal,
    homeoRealMixedSpacePolarSpace_apply_fst_ofIsComplex, homeoRealMixedSpacePolarSpace_apply_snd]

variable {K}

variable {A : Set (mixedSpace K)}
/-
**NumberField.mixedEmbedding.normAtComplexPlaces_polarSpaceCoord_symm** 是 Mathli
b 中的一个定理，位于命名空间 `NumberField.mixedEmbedding`。
形式化陈述：normAtComplexPlaces_polarSpaceCoord_symm [NumberField K] (x : polarSpace K
) : normAtComplexPlaces ((polarSpaceCoord K).symm x) = normAtComplexPlaces (mixe
dSpaceOfRealSpace x.1)
参数：x : polarSpace K。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `NumberField.InfinitePlace.isReal_or_isComplex`：isReal_or_isComplex (w : 
InfinitePlace K) : IsReal w ∨ IsComplex w
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `NumberField.mixedEmbedding.polarSpaceCoord_symm_apply`：∀ (K : Type u_1) 
[inst : Field K] [inst_1 : NumberField K] (a : NumberField.mixedEmbedding.polarS
pace K),   ↑(NumberField.mixedEmbedding.pol…
· 使用定理 `NumberField.mixedEmbedding.normAtComplexPlaces_apply_isReal`：normAtCompl
exPlaces_apply_isReal {x : mixedSpace K} (w : {w // IsReal w}) : normAtComplexPl
aces x w = x.1 w
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `NumberField.mixedEmbedding.normAtComplexPlaces_apply_isComplex`：normAtCo
mplexPlaces_apply_isComplex {x : mixedSpace K} (w : {w // IsComplex w}) : normAt
ComplexPlaces x w = ‖x.2 w‖
· 使用定理 `Complex.polarCoord_symm_apply`：∀ (p : ℝ × ℝ), ↑Complex.polarCoord.symm p
 = ↑p.1 * (↑(Real.cos p.2) + ↑(Real.sin p.2) * Complex.I)
· 使用定理 `Complex.ofReal_cos`：ofReal_cos (x : Real) : (Real.cos x : Complex) = cos
 x
· 使用定理 `Complex.ofReal_sin`：ofReal_sin (x : Real) : (Real.sin x : Complex) = sin
 x
· 使用定理 `Complex.norm_mul`：∀ (z w : ℂ), ‖z * w‖ = ‖z‖ * ‖w‖
· 使用引理 `Complex.norm_real`：norm_real (r : Real) : ‖(r : Complex)‖ = ‖r‖
· 使用定理 `Complex.norm_cos_add_sin_mul_I`：norm_cos_add_sin_mul_I (x : Real) : ‖cos
 x + sin x * I‖ = 1
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
-/
theorem normAtComplexPlaces_polarSpaceCoord_symm [NumberField K] (x : polarSpace K) :
    normAtComplexPlaces ((polarSpaceCoord K).symm x) =
      normAtComplexPlaces (mixedSpaceOfRealSpace x.1) := by
  ext w
  obtain hw | hw := isReal_or_isComplex w
  · simp [normAtComplexPlaces_apply_isReal ⟨w, hw⟩, mixedSpaceOfRealSpace_apply]
  · simp [normAtComplexPlaces_apply_isComplex ⟨w, hw⟩, mixedSpaceOfRealSpace_apply]

open scoped ComplexOrder Classical in
/-
**NumberField.mixedEmbedding.volume_eq_two_pi_pow_mul_integral_aux** 是 Mathlib 中
的一个定理，位于命名空间 `NumberField.mixedEmbedding`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private theorem volume_eq_two_pi_pow_mul_integral_aux
    (hA : normAtComplexPlaces ⁻¹' normAtComplexPlaces '' A = A) :
    normAtComplexPlaces '' A =
      (mixedSpaceOfRealSpace ⁻¹' A) ∩
        Set.univ.pi fun w ↦ if w.IsReal then Set.univ else Set.Ici 0 := by
  have h : ∀ (x : mixedSpace K), ∀ w, IsComplex w → 0 ≤ normAtComplexPlaces x w := by
    intro x w hw
    rw [normAtComplexPlaces_apply_isComplex ⟨w, hw⟩]
    exact norm_nonneg _
  ext x
  refine ⟨?_, fun ⟨hx₁, hx₂⟩ ↦ ?_⟩
  · rintro ⟨a, ha, rfl⟩
    refine ⟨?_, by simpa using h a⟩
    rw [Set.mem_preimage, ← hA, Set.mem_preimage, normAtComplexPlaces_mixedSpaceOfRealSpace (h a)]
    exact Set.mem_image_of_mem _ ha
  · rwa [Set.mem_preimage, ← hA, Set.mem_preimage, normAtComplexPlaces_mixedSpaceOfRealSpace] at hx₁
    intro w hw
    simpa [if_neg (not_isReal_iff_isComplex.mpr hw)] using hx₂ w (Set.mem_univ w)

open scoped Classical in
/--
If the measurable set `A` is norm-stable at complex places in the sense that
`normAtComplexPlaces⁻¹ (normAtComplexPlaces '' A) = A`, then its volume can be computed via an
integral over `normAtComplexPlaces '' A`.
-/
/-
**NumberField.mixedEmbedding.volume_eq_two_pi_pow_mul_integral** 是 Mathlib 中的一个定
理，位于命名空间 `NumberField.mixedEmbedding`。
形式化陈述：volume_eq_two_pi_pow_mul_integral [NumberField K] (hA : normAtComplexPlace
s ⁻¹' normAtComplexPlaces '' A = A) (hm : MeasurableSet A) : volume A = .ofReal 
(2 * π) ^ nrComplexPlaces K * ∫⁻ x in normAtComplexPlaces '' A, ∏ w : {w // IsCo
mplex w}, ENNReal.ofReal (x w.1)
参数：hA : normAtComplexPlaces ⁻¹' normAtComplexPlaces '' A = A；hm : MeasurableSet 
A。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Complex.instFiniteDimensionalReal`：FiniteDimensional ℝ ℂ
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.lintegral_indicator_one`：lintegral_indicator_one {s : Set 
α} (hs : MeasurableSet s) : ∫⁻ a, s.indicator 1 a ∂μ = μ s
· 使用定理 `NumberField.mixedEmbedding.lintegral_comp_polarSpaceCoord_symm`：lintegra
l_comp_polarSpaceCoord_symm [NumberField K] (f : mixedSpace K -> Real>=0∞) : ∫⁻ 
x in (polarSpaceCoord K).target, (∏ w : {w // IsComp…
· 使用定理 `NumberField.mixedEmbedding.polarSpaceCoord_target'`：polarSpaceCoord_targ
et' [NumberField K] : (polarSpaceCoord K).target = (Set.univ.pi fun w => if w.Is
Real then Set.univ else Set.Ioi 0) ×ˢ (S…
· 使用定理 `MeasureTheory.Measure.volume_eq_prod`：volume_eq_prod (α β) [MeasureSpace
 α] [MeasureSpace β] : (volume : Measure (α × β)) = (volume : Measure α).prod (v
olume : Measure β)
· 使用定理 `MeasureTheory.setLIntegral_prod`：setLIntegral_prod [SFinite μ] {s : Set 
α} {t : Set β} (f : α × β -> Real>=0∞) (hf : AEMeasurable f ((μ.prod ν).restrict
 (s ×ˢ t))) : ∫⁻ z in…
· 使用定理 `MeasureTheory.instSFiniteOfSigmaFinite`：∀ {α : Type u_1} {m0 : Measurabl
eSpace α} {μ : MeasureTheory.Measure α} [MeasureTheory.SigmaFinite μ],   Measure
Theory.SFinite μ
· 使用定理 `MeasureTheory.Measure.instSigmaFiniteForallVolume`：∀ {ι : Type u_1} [ins
t : Fintype ι] {α : ι → Type u_4} [inst_1 : (i : ι) → MeasureTheory.MeasureSpace
 (α i)]   [∀ (i : ι), MeasureTheory.Sig…
· 使用定理 `MeasureTheory.Measure.IsAddHaarMeasure.sigmaFinite`：∀ {G : Type u_1} [in
st : MeasurableSpace G] [inst_1 : AddGroup G] [inst_2 : TopologicalSpace G]   (μ
 : MeasureTheory.Measure G) [μ.IsAddHaar…
· 使用定理 `instIsAddHaarMeasureVolume`：∀ {E : Type u_3} [inst : NormedAddCommGroup 
E] [inst_1 : InnerProductSpace ℝ E] [inst_2 : FiniteDimensional ℝ E]   [inst_3 :
 MeasurableSpace…
· 使用定理 `SeparableWeaklyLocallyCompactAddGroup.sigmaCompactSpace`：∀ {G : Type w} 
[inst : TopologicalSpace G] [inst_1 : AddGroup G] [IsTopologicalAddGroup G]   [T
opologicalSpace.SeparableSpace G] [WeaklyLoca…
· 使用定理 `instIsTopologicalAddGroupReal`：IsTopologicalAddGroup ℝ
· 使用定理 `TopologicalSpace.SecondCountableTopology.to_separableSpace`：∀ {α : Type 
u} [t : TopologicalSpace α] [SecondCountableTopology α], TopologicalSpace.Separa
bleSpace α
· 使用定理 `instSecondCountableTopologyReal`：SecondCountableTopology ℝ
· 使用定理 `instWeaklyLocallyCompactSpaceOfLocallyCompactSpace`：∀ {X : Type u_1} [in
st : TopologicalSpace X] [LocallyCompactSpace X], WeaklyLocallyCompactSpace X
· 使用定理 `locallyCompact_of_proper`：∀ {α : Type u} [inst : PseudoMetricSpace α] [P
roperSpace α], LocallyCompactSpace α
· 使用定理 `instProperSpaceReal`：ProperSpace ℝ
· 使用定理 `Measurable.aemeasurable`：Measurable.aemeasurable (h : Measurable f) : AE
Measurable f μ
· 使用定理 `Measurable.mul`：Measurable.mul [MeasurableMul₂ M] (hf : Measurable f) (h
g : Measurable g) : Measurable (f * g)
· 使用定理 `Finset.measurable_prod`：Finset.measurable_prod (s : Finset ι) (hf : fora
ll i in s, Measurable (f i)) : Measurable fun a => ∏ i in s, f i a
· 使用定理 `Measurable.ennreal_ofReal`：Measurable.ennreal_ofReal {f : α -> Real} (hf
 : Measurable f) : Measurable fun x => ENNReal.ofReal (f x)
· 使用定理 `Measurable.fun_comp`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {x :
 MeasurableSpace α} {x_1 : MeasurableSpace β}   {x_2 : MeasurableSpace γ} {g : β
 → γ} {f …
（共 88 条，此处仅展示前 30 条）

--- 原说明 ---
If the measurable set `A` is norm-stable at complex places in the sense that
`normAtComplexPlaces⁻¹ (normAtComplexPlaces '' A) = A`, then its volume can be c
omputed via an
integral over `normAtComplexPlaces '' A`.
-/
theorem volume_eq_two_pi_pow_mul_integral [NumberField K]
    (hA : normAtComplexPlaces ⁻¹' normAtComplexPlaces '' A = A) (hm : MeasurableSet A) :
    volume A = .ofReal (2 * π) ^ nrComplexPlaces K *
      ∫⁻ x in normAtComplexPlaces '' A, ∏ w : {w // IsComplex w}, ENNReal.ofReal (x w.1) := by
  have hA' {x} : (A.indicator 1 x : ℝ≥0∞) =
      (normAtComplexPlaces '' A).indicator 1 (normAtComplexPlaces x) := by
    simp_rw [← Set.indicator_comp_right, Function.comp_def, Pi.one_def, hA]
  rw [← lintegral_indicator_one hm, ← lintegral_comp_polarSpaceCoord_symm, polarSpaceCoord_target',
    Measure.volume_eq_prod, setLIntegral_prod]
  · simp_rw [hA', normAtComplexPlaces_polarSpaceCoord_symm, lintegral_const, restrict_apply
      MeasurableSet.univ, Set.univ_inter, volume_pi, Measure.pi_pi, volume_Ioo, sub_neg_eq_add,
      ← two_mul, Finset.prod_const, Finset.card_univ, ← Set.indicator_const_mul,
      ← Set.indicator_comp_right, Function.comp_def, Pi.one_apply, mul_one]
    rw [lintegral_mul_const' _ _ (ne_of_beq_false rfl).symm, mul_comm]
    erw [setLIntegral_indicator (by convert! hm.preimage mixedSpaceOfRealSpace.measurable)]
    rw [hA, volume_eq_two_pi_pow_mul_integral_aux hA]
    congr 1
    refine setLIntegral_congr (ae_eq_set_inter (by rfl) (Measure.ae_eq_set_pi fun w _ ↦ ?_))
    split_ifs
    exacts [ae_eq_rfl, Ioi_ae_eq_Ici]
  · exact (Measurable.mul (by fun_prop)
      <| measurable_const.indicator <| hm.preimage (measurable_polarSpaceCoord_symm K)).aemeasurable
/-
**NumberField.mixedEmbedding.volume_eq_two_pow_mul_two_pi_pow_mul_integral_aux**
 是 Mathlib 中的一个定理，位于命名空间 `NumberField.mixedEmbedding`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private theorem volume_eq_two_pow_mul_two_pi_pow_mul_integral_aux
    (hA : normAtAllPlaces ⁻¹' normAtAllPlaces '' A = A) :
    normAtAllPlaces '' A ∩ (⋂ w : {w // IsReal w}, {x | x w.1 ≠ 0}) =
      normAtComplexPlaces '' plusPart A := by
  ext x
  refine ⟨?_, ?_⟩
  · rintro ⟨⟨a, ha, rfl⟩, ha₂⟩
    refine ⟨mixedSpaceOfRealSpace (normAtAllPlaces a), ⟨?_, ?_⟩, ?_⟩
    · rw [← hA, Set.mem_preimage, normAtAllPlaces_normAtAllPlaces]
      exact Set.mem_image_of_mem normAtAllPlaces ha
    · intro w
      refine lt_of_le_of_ne' (normAtPlace_nonneg _ _) (Set.mem_iInter.mp ha₂ w)
    · rw [normAtComplexPlaces_normAtAllPlaces]
  · rintro ⟨a, ⟨ha₁, ha₂⟩, rfl⟩
    refine ⟨⟨a, ha₁, funext fun w ↦ ?_⟩, Set.mem_iInter.mpr fun w ↦ ?_⟩
    · obtain hw | hw := isReal_or_isComplex w
      · simpa [normAtComplexPlaces_apply_isReal ⟨w, hw⟩, normAtPlace_apply_of_isReal hw]
          using (ha₂ ⟨w, hw⟩).le
      · rw [normAtAllPlaces_apply, normAtPlace_apply_of_isComplex hw,
          normAtComplexPlaces_apply_isComplex ⟨w, hw⟩]
    · simpa [Set.mem_ofPred_eq, normAtComplexPlaces_apply_isReal] using (ha₂ w).ne'

open scoped Classical in
/--
If the measurable set `A` is norm-stable in the sense that
`normAtAllPlaces⁻¹ (normAtAllPlaces '' A) = A`, then its volume can be computed via an integral
over `normAtAllPlaces '' A`.
-/
/-
**NumberField.mixedEmbedding.volume_eq_two_pow_mul_two_pi_pow_mul_integral** 是 M
athlib 中的一个定理，位于命名空间 `NumberField.mixedEmbedding`。
形式化陈述：volume_eq_two_pow_mul_two_pi_pow_mul_integral [NumberField K] (hA : normAt
AllPlaces ⁻¹' normAtAllPlaces '' A = A) (hm : MeasurableSet A) : volume A = 2 ^ 
nrRealPlaces K * .ofReal (2 * π) ^ nrComplexPlaces K * ∫⁻ x in normAtAllPlaces '
' A, ∏ w : {w // IsComplex w}, ENNReal.ofReal (x w.1)
参数：hA : normAtAllPlaces ⁻¹' normAtAllPlaces '' A = A；hm : MeasurableSet A。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `NumberField.mixedEmbedding.normAtAllPlaces_norm_at_real_places`：normAtAl
lPlaces_norm_at_real_places (x : mixedSpace K) : normAtAllPlaces (fun w => ‖x.1 
w‖, x.2) = normAtAllPlaces x
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `subset_antisymm`：∀ {α : Type u_1} [UsesSetNotationForOrder α] [inst : Pa
rtialOrder α] {a b : α}, a ⊆ b → b ⊆ a → a = b
· 使用定理 `Set.mem_preimage`：mem_preimage {f : α -> β} {s : Set β} {a : α} : a in f
 ⁻¹' s ↔ f a in s
· 使用定理 `NumberField.mixedEmbedding.normAtAllPlaces_eq_of_normAtComplexPlaces_eq`
：normAtAllPlaces_eq_of_normAtComplexPlaces_eq {x y : mixedSpace K} (h : normAtCo
mplexPlaces x = normAtComplexPlaces y) : normAtAllPlaces x = …
· 使用定理 `Set.mem_image_of_mem`：mem_image_of_mem (f : α -> β) {x : α} {a : Set α} 
(h : x in a) : f x in f '' a
· 使用定理 `Set.inter_subset_left`：inter_subset_left {s t : Set α} : s inter t subse
teq s
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `funext_iff`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g
 ↔ ∀ (x : α), f x = g x
· 使用定理 `NumberField.mixedEmbedding.normAtComplexPlaces_apply_isReal`：normAtCompl
exPlaces_apply_isReal {x : mixedSpace K} (w : {w // IsReal w}) : normAtComplexPl
aces x w = x.1 w
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Set.subset_preimage_image`：subset_preimage_image (f : α -> β) (s : Set α
) : s subseteq f ⁻¹' f '' s
· 使用定理 `Complex.instFiniteDimensionalReal`：FiniteDimensional ℝ ℂ
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `NumberField.mixedEmbedding.volume_eq_two_pow_mul_volume_plusPart`：volume
_eq_two_pow_mul_volume_plusPart (hm : MeasurableSet A) : volume A = 2 ^ nrRealPl
aces K * volume (plusPart A)
· 使用定理 `NumberField.mixedEmbedding.volume_eq_two_pi_pow_mul_integral`：volume_eq_
two_pi_pow_mul_integral [NumberField K] (hA : normAtComplexPlaces ⁻¹' normAtComp
lexPlaces '' A = A) (hm : MeasurableSet A) : volum…
· 使用定理 `NumberField.mixedEmbedding.measurableSet_plusPart`：measurableSet_plusPar
t (hm : MeasurableSet A) : MeasurableSet (plusPart A)
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `MeasureTheory.setLIntegral_congr`：setLIntegral_congr {f : α -> Real>=0∞}
 {s t : Set α} (h : s =ᵐ[μ] t) : ∫⁻ x in s, f x ∂μ = ∫⁻ x in t, f x ∂μ
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `_private.Mathlib.NumberTheory.NumberField.CanonicalEmbedding.PolarCoord.
0.NumberField.mixedEmbedding.volume_eq_two_pow_mul_two_pi_pow_mul_integral_aux`：
∀ {K : Type u_1} [inst : Field K] {A : Set (NumberField.mixedEmbedding.mixedSpac
e K)},   NumberField.mixedEmbedding.normAtAllPlaces ⁻¹' Numb…
· 使用定理 `MeasureTheory.inter_ae_eq_left_of_ae_eq_univ`：inter_ae_eq_left_of_ae_eq_
univ (h : t =ᵐ[μ] univ) : (s inter t : Set α) =ᵐ[μ] s
（共 40 条，此处仅展示前 30 条）

--- 原说明 ---
If the measurable set `A` is norm-stable in the sense that
`normAtAllPlaces⁻¹ (normAtAllPlaces '' A) = A`, then its volume can be computed 
via an integral
over `normAtAllPlaces '' A`.
-/
theorem volume_eq_two_pow_mul_two_pi_pow_mul_integral [NumberField K]
    (hA : normAtAllPlaces ⁻¹' normAtAllPlaces '' A = A) (hm : MeasurableSet A) :
    volume A = 2 ^ nrRealPlaces K * .ofReal (2 * π) ^ nrComplexPlaces K *
      ∫⁻ x in normAtAllPlaces '' A, ∏ w : {w // IsComplex w}, ENNReal.ofReal (x w.1) := by
  have hA₁ (x : mixedSpace K) : x ∈ A ↔ (fun w ↦ ‖x.1 w‖, x.2) ∈ A := by
    rw [← hA]
    simp_rw [Set.mem_preimage, Set.mem_image, normAtAllPlaces_norm_at_real_places]
  have hA₃ : normAtComplexPlaces ⁻¹' normAtComplexPlaces '' plusPart A = plusPart A := by
    refine subset_antisymm (fun x ⟨a, ha₁, ha₂⟩ ↦ ⟨?_, fun w ↦ ?_⟩) (Set.subset_preimage_image _ _)
    · rw [← hA, Set.mem_preimage, ← normAtAllPlaces_eq_of_normAtComplexPlaces_eq ha₂]
      exact Set.mem_image_of_mem normAtAllPlaces (Set.inter_subset_left ha₁)
    · have := funext_iff.mp ha₂ w
      rw [normAtComplexPlaces_apply_isReal, normAtComplexPlaces_apply_isReal] at this
      rw [← this]
      exact ha₁.2 w
  rw [volume_eq_two_pow_mul_volume_plusPart hA₁ hm, volume_eq_two_pi_pow_mul_integral hA₃
    (measurableSet_plusPart hm), ← mul_assoc]
  refine congr_arg (_ * _ * ·) <| setLIntegral_congr ?_
  rw [← volume_eq_two_pow_mul_two_pi_pow_mul_integral_aux hA]
  refine inter_ae_eq_left_of_ae_eq_univ <| ae_eq_univ.mpr
    <| Set.compl_iInter _ ▸ measure_iUnion_null_iff.mpr fun w ↦ ?_
  rw [show {x : realSpace K | x w.1 ≠ 0}ᶜ = {x | x w.1 = 0} by ext; simp]
  exact realSpace.volume_eq_zero w.1

end polarSpace

end NumberField.mixedEmbedding

