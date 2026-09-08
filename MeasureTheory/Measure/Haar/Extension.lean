/-
Copyright (c) 2025 Thomas Browning. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Browning
-/
module

public import Mathlib.MeasureTheory.Group.Integral
public import Mathlib.MeasureTheory.Integral.RieszMarkovKakutani.Real
public import Mathlib.Topology.Algebra.Group.Extension

/-!
# Haar measures on group extensions

In this file, if `1 → A → B → C → 1` is a short exact sequence of topological groups,
we construct a Haar measure on `B` from Haar measures on `A` and `C`.

## Main definitions

* `TopologicalGroup.IsSES.inducedMeasure`: The Haar measure on `B` induced by Haar measures
  on `A` and `C`.

## Main results

* `TopologicalGroup.IsSES.isHaarMeasure_inducedMeasure`: `inducedMeasure` is a Haar measure.
* `TopologicalGroup.IsSES.inducedMeasure_lt_of_injOn`: If `ψ` is injective on an open set `U`,
  then the induced measure on `U` is bounded by `μC Set.univ * μA {1}` (possibly infinite).

-/

@[expose] public section

open MeasureTheory Measure

open scoped Pointwise

namespace TopologicalGroup.IsSES

variable {A B C E : Type*} [Group A] [Group B] [Group C]
  [TopologicalSpace A] [TopologicalSpace B] [TopologicalSpace C]
  {φ : A →* B} {ψ : B →* C} (H : TopologicalGroup.IsSES φ ψ)
  [IsTopologicalGroup A] [IsTopologicalGroup B] [NormedAddCommGroup E]

/-- If `φ : A →* B` and `ψ : B →* C` define a short exact sequence of topological groups, then we
can pull back a continuous compactly supported function `f` on `B` along `φ` to the continuous
compactly supported function `a ↦ f (b * φ a)` on `A`. -/
@[to_additive /-- If `φ : A →+ B` and `ψ : B →+ C` define a short exact sequence of additive
topological groups, then we can pull back a continuous compactly supported function `f` on `B` along
`φ` to the continuous compactly supported function `a ↦ f (b + φ a)` on `A`. -/]
/-
**TopologicalGroup.IsSES.pullback** 是 Mathlib 中的一个缩写定义，位于命名空间 `TopologicalGroup.
IsSES`。
形式化陈述：pullback (f : CompactlySupportedContinuousMap B E) (b : B) : CompactlySupp
ortedContinuousMap A E
参数：f : CompactlySupportedContinuousMap B E；b : B。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalGroup.toContinuousMul`：∀ {G : Type u_4} {inst : Topological
Space G} {inst_1 : Group G} [self : IsTopologicalGroup G], ContinuousMul G
· 使用定理 `TopologicalGroup.IsSES.isClosedEmbedding`：∀ {A : Type u_1} {B : Type u_2
} {C : Type u_3} [inst : Group A] [inst_1 : Group B] [inst_2 : Group C]   [inst_
3 : TopologicalSpace A] [inst_…
-/
noncomputable abbrev pullback (f : CompactlySupportedContinuousMap B E) (b : B) :
    CompactlySupportedContinuousMap A E :=
  f.pullback_monoidHom H.isClosedEmbedding b

@[to_additive]
/-
**TopologicalGroup.IsSES.pullback_def** 是 Mathlib 中的一个定理，位于命名空间 `TopologicalGrou
p.IsSES`。
形式化陈述：pullback_def (f : CompactlySupportedContinuousMap B E) (b : B) (a : A) : p
ullback H f b a = f (b * φ a)
参数：f : CompactlySupportedContinuousMap B E；b : B；a : A。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CompactlySupportedContinuousMap.pullback_monoidHom_def`：pullback_monoidH
om_def (f : CompactlySupportedContinuousMap β γ) (b : β) (a : α) : pullback_mono
idHom hφ f b a = f (b * φ a)
· 使用定理 `instR1Space`：∀ {X : Type u_1} [inst : TopologicalSpace X] [RegularSpace 
X], R1Space X
· 使用定理 `IsTopologicalGroup.regularSpace`：∀ (G : Type w) [inst : TopologicalSpace
 G] [inst_1 : Group G] [IsTopologicalGroup G], RegularSpace G
· 使用定理 `IsTopologicalGroup.toContinuousMul`：∀ {G : Type u_4} {inst : Topological
Space G} {inst_1 : Group G} [self : IsTopologicalGroup G], ContinuousMul G
· 使用定理 `TopologicalGroup.IsSES.isClosedEmbedding`：∀ {A : Type u_1} {B : Type u_2
} {C : Type u_3} [inst : Group A] [inst_1 : Group B] [inst_2 : Group C]   [inst_
3 : TopologicalSpace A] [inst_…
-/
theorem pullback_def (f : CompactlySupportedContinuousMap B E) (b : B) (a : A) :
    pullback H f b a = f (b * φ a) :=
  f.pullback_monoidHom_def H.isClosedEmbedding b a

variable [MeasurableSpace A] [BorelSpace A] (μA : Measure A) [hμA : IsHaarMeasure μA]
  [NormedSpace ℝ E]

@[to_additive]
/-
**TopologicalGroup.IsSES.integral_pullback_invFun_apply** 是 Mathlib 中的一个定理，位于命名空
间 `TopologicalGroup.IsSES`。
形式化陈述：integral_pullback_invFun_apply (f : CompactlySupportedContinuousMap B E) (
b : B) : ∫ a, H.pullback f (Function.invFun ψ (ψ b)) a ∂μA = ∫ a, H.pullback f b
 a ∂μA
参数：f : CompactlySupportedContinuousMap B E；b : B。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Torsor.nonempty`：∀ {G : outParam (Type u_1)} {P : Type u_2} {inst : Grou
p G} [self : Torsor G P], Nonempty P
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `map_mul`：map_mul [MulHomClass F M N] (f : F) (x y : M) : f (x * y) = f x
 * f y
· 使用定理 `MonoidHomClass.toMulHomClass`：∀ {F : Type u_10} {M : outParam (Type u_11
)} {N : outParam (Type u_12)} {inst : MulOne M} {inst_1 : MulOne N}   {inst_2 : 
FunLike F M N} [se…
· 使用定理 `map_inv`：map_inv [Group G] [DivisionMonoid H] [MonoidHomClass F G H] (f 
: F) (a : G) : f a⁻¹ = (f a)⁻¹
· 使用定理 `Function.apply_invFun_apply`：apply_invFun_apply {α β : Type*} {f : α -> 
β} {a : α} : f (@invFun _ _ ⟨a⟩ f (f a)) = f a
· 使用定理 `inv_mul_cancel`：inv_mul_cancel (a : G) : a⁻¹ * a = 1
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用引理 `Function.MulExact.monoidHom_ker_eq`：monoidHom_ker_eq (hfg : MulExact f g
) : ker g = range f
· 使用定理 `TopologicalGroup.IsSES.mulExact`：∀ {A : Type u_1} {B : Type u_2} {C : Ty
pe u_3} [inst : Group A] [inst_1 : Group B] [inst_2 : Group C]   [inst_3 : Topol
ogicalSpace A] [inst_…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MonoidHom.mem_ker`：mem_ker {f : G ->* M} {x : G} : x in f.ker ↔ f x = 1
· 使用定理 `MeasureTheory.integral_mul_left_eq_self`：integral_mul_left_eq_self [IsMu
lLeftInvariant μ] (f : G -> E) (g : G) : (∫ x, f (g * x) ∂μ) = ∫ x, f x ∂μ
· 使用定理 `ContinuousMul.measurableMul`：∀ {γ : Type u_3} [inst : TopologicalSpace γ
] [inst_1 : MeasurableSpace γ] [BorelSpace γ] [inst_3 : Mul γ]   [SeparatelyCont
inuousMul γ], Mea…
· 使用定理 `instSeparatelyContinuousMulOfContinuousMul`：∀ {M : Type u_1} [inst : Top
ologicalSpace M] [inst_1 : Mul M] [ContinuousMul M], SeparatelyContinuousMul M
· 使用定理 `IsTopologicalGroup.toContinuousMul`：∀ {G : Type u_4} {inst : Topological
Space G} {inst_1 : Group G} [self : IsTopologicalGroup G], ContinuousMul G
· 使用定理 `MeasureTheory.Measure.IsHaarMeasure.toIsMulLeftInvariant`：∀ {G : Type u_
3} {inst : Group G} {inst_1 : TopologicalSpace G} {inst_2 : MeasurableSpace G}  
 {μ : MeasureTheory.Measure G} [self : μ.IsHaa…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `TopologicalGroup.IsSES.pullback_def`：pullback_def (f : CompactlySupporte
dContinuousMap B E) (b : B) (a : A) : pullback H f b a = f (b * φ a)
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `mul_inv_cancel_left`：mul_inv_cancel_left (a b : G) : a * (a⁻¹ * b) = b
-/
theorem integral_pullback_invFun_apply (f : CompactlySupportedContinuousMap B E) (b : B) :
    ∫ a, H.pullback f (Function.invFun ψ (ψ b)) a ∂μA = ∫ a, H.pullback f b a ∂μA := by
  have h : ψ ((Function.invFun ψ (ψ b))⁻¹ * b) = 1 := by simp [Function.apply_invFun_apply]
  rw [← ψ.mem_ker, H.mulExact.monoidHom_ker_eq] at h
  obtain ⟨a, ha⟩ := h
  rw [← integral_mul_left_eq_self _ a]
  simp [pullback_def, ha, mul_assoc]

variable [IsTopologicalGroup C] [LocallyCompactSpace B]

/-- If `φ : A →* B` and `ψ : B →* C` define a short exact sequence of topological groups, then we
can push forward a continuous compactly supported function on `B` to a continuous compactly
supported function on `C` by integrating over `A`. -/
@[to_additive /-- If `φ : A →+ B` and `ψ : B →+ C` define a short exact sequence of additive
topological groups, then we can push forward a continuous compactly supported function on `B` to a
continuous compactly supported function on `C` by integrating over `A`. -/]
/-
**TopologicalGroup.IsSES.pushforward** 是 Mathlib 中的一个定义，位于命名空间 `TopologicalGroup
.IsSES`。
形式化陈述：pushforward : CompactlySupportedContinuousMap B E ->ₗ[Real] CompactlySuppo
rtedContinuousMap C E where toFun f
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
noncomputable def pushforward :
    CompactlySupportedContinuousMap B E →ₗ[ℝ] CompactlySupportedContinuousMap C E where
  toFun f :=
  { toFun := fun c ↦ ∫ a, pullback H f (Function.invFun ψ c) a ∂μA
    hasCompactSupport' := by
      obtain ⟨K, hK, hf⟩ := exists_compact_iff_hasCompactSupport.mpr f.hasCompactSupport
      refine exists_compact_iff_hasCompactSupport.mp
        ⟨ψ '' K, hK.image H.isOpenQuotientMap.continuous, fun x hx ↦ ?_⟩
      suffices ∀ a : A, f (Function.invFun ψ x * φ a) = 0 by simp [this, pullback_def]
      refine fun a ↦ hf _ (mt (Set.mem_image_of_mem ψ) ?_)
      rwa [map_mul, Function.rightInverse_invFun H.isOpenQuotientMap.surjective,
        H.mulExact.apply_apply_eq_one, mul_one]
    continuous_toFun := by
      let := IsTopologicalGroup.rightUniformSpace B
      simp_rw [← H.isOpenQuotientMap.continuous_comp_iff, Function.comp_def,
        integral_pullback_invFun_apply, Metric.continuous_iff']
      intro b ε hε
      obtain ⟨U₀, hU₀, hb⟩ := exists_compact_mem_nhds b
      obtain ⟨K, hK, hf₀⟩ := exists_compact_iff_hasCompactSupport.mpr f.hasCompactSupport
      let S : Set A := φ ⁻¹' (U₀⁻¹ * K)
      have hSc : IsCompact S := H.isClosedEmbedding.isCompact_preimage (hU₀.inv.mul hK)
      obtain ⟨δ, hδ0, hδ⟩ : ∃ δ > 0, ENNReal.ofReal δ * μA S < ENNReal.ofReal ε := by
        rw [← ENNReal.ofReal_toReal hSc.measure_ne_top, ← measureReal_def]
        by_cases hS' : μA.real S = 0
        · simp [hS', hε, exists_gt]
        · refine ⟨ε / 2 / μA.real S, by positivity, ?_⟩
          rwa [← ENNReal.ofReal_mul' measureReal_nonneg, ENNReal.ofReal_lt_ofReal_iff hε,
            div_mul_cancel₀ _ hS', half_lt_self_iff]
      have hS {x} (hx : x ∈ U₀) {y} (hy : y ∉ S) : H.pullback f x y = 0 := by
        contrapose! hy
        exact Set.mem_mul.mpr ⟨x⁻¹, Set.inv_mem_inv.mpr hx, x * φ y,
          not_imp_comm.mp (hf₀ (x * φ y)) hy, inv_mul_cancel_left x (φ y)⟩
      have ha := f.hasCompactSupport.uniformContinuous_of_continuous f.continuous
      rw [uniformContinuous_iff_eventually] at ha
      obtain ⟨U, hU, hf⟩ := ha _ (Metric.dist_mem_uniformity hδ0)
      refine Filter.mem_of_superset (Filter.inter_mem
        (mul_singleton_mem_nhds_of_nhds_one b (inv_mem_nhds_one B hU)) hb) ?_
      rintro - ⟨⟨t, ht, b, rfl, -, rfl⟩, htb⟩
      have h (a) (ha : a ∈ S) : edist (H.pullback f (t * b) a) (H.pullback f b a) ≤ .ofReal δ := by
        rw [edist_dist]
        exact ENNReal.ofReal_le_ofReal (@hf ⟨t * b * φ a, b * φ a⟩ (by simpa)).le
      grw [Set.mem_ofPred_eq, dist_integral_le_lintegral_edist (H.pullback f (t * b)).integrable
        (H.pullback f b).integrable, ← setLIntegral_eq_of_support_subset]
      · refine ENNReal.toReal_lt_of_lt_ofReal ((setLIntegral_mono measurable_const h).trans_lt ?_)
        rwa [lintegral_const, restrict_apply_univ]
      · intro y hy
        contrapose hy
        rw [Function.notMem_support, hS htb hy, hS (mem_of_mem_nhds hb) hy, edist_self] }
  map_add' f g := by
    ext c
    exact integral_add (pullback H f _).integrable (pullback H g _).integrable
  map_smul' x f := by
    ext c
    apply integral_smul

@[to_additive]
/-
**TopologicalGroup.IsSES.pushforward_def** 是 Mathlib 中的一个定理，位于命名空间 `TopologicalG
roup.IsSES`。
形式化陈述：pushforward_def (f : CompactlySupportedContinuousMap B E) (c : C) : pushfo
rward H μA f c = ∫ a, pullback H f (Function.invFun ψ c) a ∂μA
参数：f : CompactlySupportedContinuousMap B E；c : C。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
-/
theorem pushforward_def (f : CompactlySupportedContinuousMap B E) (c : C) :
    pushforward H μA f c = ∫ a, pullback H f (Function.invFun ψ c) a ∂μA :=
  rfl

@[to_additive]
/-
**TopologicalGroup.IsSES.pushforward_apply_apply** 是 Mathlib 中的一个定理，位于命名空间 `Topo
logicalGroup.IsSES`。
形式化陈述：pushforward_apply_apply (f : CompactlySupportedContinuousMap B E) (b : B) 
: pushforward H μA f (ψ b) = ∫ a, pullback H f b a ∂μA
参数：f : CompactlySupportedContinuousMap B E；b : B。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `TopologicalGroup.IsSES.integral_pullback_invFun_apply`：integral_pullback
_invFun_apply (f : CompactlySupportedContinuousMap B E) (b : B) : ∫ a, H.pullbac
k f (Function.invFun ψ (ψ b)) a ∂μA = ∫ a, …
-/
theorem pushforward_apply_apply (f : CompactlySupportedContinuousMap B E) (b : B) :
    pushforward H μA f (ψ b) = ∫ a, pullback H f b a ∂μA :=
  integral_pullback_invFun_apply H μA f b

@[to_additive]
/-
**TopologicalGroup.IsSES.pushforward_mono** 是 Mathlib 中的一个定理，位于命名空间 `Topological
Group.IsSES`。
形式化陈述：pushforward_mono {f g : CompactlySupportedContinuousMap B Real} (h : f <= 
g) : pushforward H μA f <= pushforward H μA g
参数：h : f <= g。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `MeasureTheory.integral_mono`：integral_mono {f g : α -> E} (hf : Integrab
le f μ) (hg : Integrable g μ) (h : f <= g) : ∫ x, f x ∂μ <= ∫ x, g x ∂μ
· 使用定理 `IsStrictOrderedModule.toIsOrderedModule`：∀ {α : Type u_1} {β : Type u_2}
 [inst : Zero α] [inst_1 : Zero β] [inst_2 : SMulWithZero α β] [inst_3 : Partial
Order α]   [inst_4 : PartialO…
· 使用定理 `IsStrictOrderedRing.toIsStrictOrderedModule`：∀ {α : Type u_1} [inst : Se
miring α] [inst_1 : PartialOrder α] [IsStrictOrderedRing α], IsStrictOrderedModu
le α α
· 使用定理 `instClosedIciTopology`：∀ {α : Type u} [inst : TopologicalSpace α] [inst_
1 : Preorder α] [t : OrderClosedTopology α], ClosedIciTopology α
· 使用定理 `HasSolidNorm.orderClosedTopology`：∀ {E : Type u_2} [inst : NormedAddComm
Group E] [inst_1 : Lattice E] [HasSolidNorm E] [IsOrderedAddMonoid E],   OrderCl
osedTopology E
· 使用定理 `instHasSolidNormReal`：HasSolidNorm ℝ
· 使用引理 `CompactlySupportedContinuousMap.integrable`：integrable {E : Type*} [Norm
edAddCommGroup E] (f : C_c(X, E)) {μ : Measure X} [IsFiniteMeasureOnCompacts μ] 
: Integrable f μ
· 使用定理 `BorelSpace.opensMeasurable`：∀ {α : Type u_6} [inst : TopologicalSpace α]
 [inst_1 : MeasurableSpace α] [BorelSpace α], OpensMeasurableSpace α
· 使用定理 `MeasureTheory.Measure.IsHaarMeasure.toIsFiniteMeasureOnCompacts`：∀ {G : 
Type u_3} {inst : Group G} {inst_1 : TopologicalSpace G} {inst_2 : MeasurableSpa
ce G}   {μ : MeasureTheory.Measure G} [self : μ.IsHaa…
-/
theorem pushforward_mono {f g : CompactlySupportedContinuousMap B ℝ} (h : f ≤ g) :
    pushforward H μA f ≤ pushforward H μA g :=
  fun _ ↦ integral_mono (pullback H f _).integrable (pullback H g _).integrable (fun _ ↦ h _)

variable [MeasurableSpace C] [BorelSpace C] (μC : Measure C) [hμC : IsHaarMeasure μC]

/-- If `φ : A →* B` and `ψ : B →* C` define a short exact sequence of topological groups, then we
can integrate a continuous compactly supported function on `B` by integrating over `A` and `C`. -/
@[to_additive /-- If `φ : A →+ B` and `ψ : B →+ C` define a short exact sequence of additive
topological groups, then we can integrate a continuous compactly supported function on `B` by
integrating over `A` and `C`. -/]
/-
**TopologicalGroup.IsSES.integrate** 是 Mathlib 中的一个定义，位于命名空间 `TopologicalGroup.I
sSES`。
形式化陈述：integrate : CompactlySupportedContinuousMap B E ->ₗ[Real] E where toFun f
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
noncomputable def integrate : CompactlySupportedContinuousMap B E →ₗ[ℝ] E where
  toFun f := ∫ c, pushforward H μA f c ∂μC
  map_add' f g := by
    rw [map_add]
    exact integral_add (pushforward H μA f).integrable (pushforward H μA g).integrable
  map_smul' x f := by
    rw [map_smul]
    exact integral_smul x (H.pushforward μA f)

@[to_additive]
/-
**TopologicalGroup.IsSES.integrate_apply** 是 Mathlib 中的一个定理，位于命名空间 `TopologicalG
roup.IsSES`。
形式化陈述：integrate_apply (f : CompactlySupportedContinuousMap B E) : H.integrate μA
 μC f = ∫ c, pushforward H μA f c ∂μC
参数：f : CompactlySupportedContinuousMap B E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
-/
theorem integrate_apply (f : CompactlySupportedContinuousMap B E) :
    H.integrate μA μC f = ∫ c, pushforward H μA f c ∂μC :=
  rfl

@[to_additive]
/-
**TopologicalGroup.IsSES.integrate_mono** 是 Mathlib 中的一个定理，位于命名空间 `TopologicalGr
oup.IsSES`。
形式化陈述：integrate_mono {f g : CompactlySupportedContinuousMap B Real} (h : f <= g)
 : integrate H μA μC f <= integrate H μA μC g
参数：h : f <= g。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `MeasureTheory.integral_mono`：integral_mono {f g : α -> E} (hf : Integrab
le f μ) (hg : Integrable g μ) (h : f <= g) : ∫ x, f x ∂μ <= ∫ x, g x ∂μ
· 使用定理 `IsStrictOrderedModule.toIsOrderedModule`：∀ {α : Type u_1} {β : Type u_2}
 [inst : Zero α] [inst_1 : Zero β] [inst_2 : SMulWithZero α β] [inst_3 : Partial
Order α]   [inst_4 : PartialO…
· 使用定理 `IsStrictOrderedRing.toIsStrictOrderedModule`：∀ {α : Type u_1} [inst : Se
miring α] [inst_1 : PartialOrder α] [IsStrictOrderedRing α], IsStrictOrderedModu
le α α
· 使用定理 `instClosedIciTopology`：∀ {α : Type u} [inst : TopologicalSpace α] [inst_
1 : Preorder α] [t : OrderClosedTopology α], ClosedIciTopology α
· 使用定理 `HasSolidNorm.orderClosedTopology`：∀ {E : Type u_2} [inst : NormedAddComm
Group E] [inst_1 : Lattice E] [HasSolidNorm E] [IsOrderedAddMonoid E],   OrderCl
osedTopology E
· 使用定理 `instHasSolidNormReal`：HasSolidNorm ℝ
· 使用引理 `CompactlySupportedContinuousMap.integrable`：integrable {E : Type*} [Norm
edAddCommGroup E] (f : C_c(X, E)) {μ : Measure X} [IsFiniteMeasureOnCompacts μ] 
: Integrable f μ
· 使用定理 `BorelSpace.opensMeasurable`：∀ {α : Type u_6} [inst : TopologicalSpace α]
 [inst_1 : MeasurableSpace α] [BorelSpace α], OpensMeasurableSpace α
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `MeasureTheory.Measure.IsHaarMeasure.toIsFiniteMeasureOnCompacts`：∀ {G : 
Type u_3} {inst : Group G} {inst_1 : TopologicalSpace G} {inst_2 : MeasurableSpa
ce G}   {μ : MeasureTheory.Measure G} [self : μ.IsHaa…
· 使用定理 `TopologicalGroup.IsSES.pushforward_mono`：pushforward_mono {f g : Compact
lySupportedContinuousMap B Real} (h : f <= g) : pushforward H μA f <= pushforwar
d H μA g
-/
theorem integrate_mono {f g : CompactlySupportedContinuousMap B ℝ} (h : f ≤ g) :
    integrate H μA μC f ≤ integrate H μA μC g :=
  integral_mono (pushforward H μA f).integrable (pushforward H μA g).integrable
    (pushforward_mono H μA h)

variable [T2Space B] [MeasurableSpace B] [BorelSpace B]

/-- If `φ : A →* B` and `ψ : B →* C` define a short exact sequence of topological groups, then we
can define a Haar measure on `B` induced by the Haar measures on `A` and `C`. -/
@[to_additive /-- If `φ : A →+ B` and `ψ : B →+ C` define a short exact sequence of additive
topological groups, then we can define a Haar measure on `B` induced by the Haar measures on `A`
and `C`. -/]
/-
**TopologicalGroup.IsSES.inducedMeasure** 是 Mathlib 中的一个定义，位于命名空间 `TopologicalGr
oup.IsSES`。
形式化陈述：inducedMeasure : Measure B
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `TopologicalGroup.IsSES.integrate_mono`：integrate_mono {f g : CompactlySu
pportedContinuousMap B Real} (h : f <= g) : integrate H μA μC f <= integrate H μ
A μC g
-/
noncomputable def inducedMeasure : Measure B :=
  RealRMK.rieszMeasure ⟨integrate H μA μC, fun _ _ ↦ integrate_mono H μA μC⟩

@[to_additive]
/-
**TopologicalGroup.IsSES.inducedMeasure_regular** 是 Mathlib 中的一个实例，位于命名空间 `Topol
ogicalGroup.IsSES`。
形式化陈述：inducedMeasure_regular : (inducedMeasure H μA μC).Regular
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `TopologicalGroup.IsSES.integrate_mono`：integrate_mono {f g : CompactlySu
pportedContinuousMap B Real} (h : f <= g) : integrate H μA μC f <= integrate H μ
A μC g
-/
instance inducedMeasure_regular : (inducedMeasure H μA μC).Regular :=
  RealRMK.regular_rieszMeasure _

@[to_additive]
/-
**TopologicalGroup.IsSES.integral_inducedMeasure** 是 Mathlib 中的一个定理，位于命名空间 `Topo
logicalGroup.IsSES`。
形式化陈述：integral_inducedMeasure (f : CompactlySupportedContinuousMap B Real) : ∫ b
 : B, f b ∂(inducedMeasure H μA μC) = integrate H μA μC f
参数：f : CompactlySupportedContinuousMap B Real。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RealRMK.integral_rieszMeasure`：integral_rieszMeasure (f : C_c(X, Real)) 
: ∫ x, f x ∂(rieszMeasure Λ) = Λ f
· 使用定理 `TopologicalGroup.IsSES.integrate_mono`：integrate_mono {f g : CompactlySu
pportedContinuousMap B Real} (h : f <= g) : integrate H μA μC f <= integrate H μ
A μC g
-/
theorem integral_inducedMeasure (f : CompactlySupportedContinuousMap B ℝ) :
    ∫ b : B, f b ∂(inducedMeasure H μA μC) = integrate H μA μC f := by
  apply RealRMK.integral_rieszMeasure

@[to_additive]
/-
**TopologicalGroup.IsSES.isHaarMeasure_inducedMeasure** 是 Mathlib 中的一个实例，位于命名空间 
`TopologicalGroup.IsSES`。
形式化陈述：isHaarMeasure_inducedMeasure : IsHaarMeasure (inducedMeasure H μA μC) wher
e lt_top_of_isCompact K hK
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用引理 `exists_continuousMap_one_of_isCompact_subset_isOpen`：exists_continuousMa
p_one_of_isCompact_subset_isOpen [R1Space X] [LocallyCompactSpace X] {K V : Set 
X} (hK : IsCompact K) (hV : IsOpen V) (hK…
· 使用定理 `instR1Space`：∀ {X : Type u_1} [inst : TopologicalSpace X] [RegularSpace 
X], R1Space X
· 使用定理 `IsTopologicalGroup.regularSpace`：∀ (G : Type w) [inst : TopologicalSpace
 G] [inst_1 : Group G] [IsTopologicalGroup G], RegularSpace G
· 使用定理 `isOpen_univ`：∀ {X : Type u} [inst : TopologicalSpace X], IsOpen Set.univ
· 使用定理 `Set.subset_univ`：subset_univ (s : Set α) : s subseteq univ
· 使用引理 `lt_of_le_of_lt`：lt_of_le_of_lt (hab : a <= b) (hbc : b < c) : a < c
· 使用定理 `IsSemitopologicalSemiring.toContinuousAdd`：∀ {R : Type u_2} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSemitopologic
alSemiring R], ContinuousAdd R
· 使用定理 `IsSemitopologicalRing.toIsSemitopologicalSemiring`：∀ {R : Type u_2} {ins
t : TopologicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopolog
icalRing R],   IsSemitopologicalSemirin…
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `IsSemitopologicalSemiring.toSeparatelyContinuousMul`：∀ {R : Type u_2} {i
nst : TopologicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSem
itopologicalSemiring R], SeparatelyContin…
· 使用定理 `TopologicalGroup.IsSES.integrate_mono`：integrate_mono {f g : CompactlySu
pportedContinuousMap B Real} (h : f <= g) : integrate H μA μC f <= integrate H μ
A μC g
· 使用引理 `RealRMK.rieszMeasure_le_of_eq_one`：rieszMeasure_le_of_eq_one {f : C_c(X,
 Real)} (hf : forall x, 0 <= f x) {K : Set X} (hK : IsCompact K) (hfK : forall x
 in K, f x = 1) : riesz…
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `ENNReal.ofReal_lt_top`：∀ {r : ℝ}, ENNReal.ofReal r < ⊤
· 使用定理 `MeasureTheory.Measure.Regular.map`：∀ {α : Type u_1} {β : Type u_2} [inst
 : MeasurableSpace α] {μ : MeasureTheory.Measure α} [inst_1 : TopologicalSpace α
]   [BorelSpace α] [ins…
· 使用定理 `instSeparatelyContinuousMulOfContinuousMul`：∀ {M : Type u_1} [inst : Top
ologicalSpace M] [inst_1 : Mul M] [ContinuousMul M], SeparatelyContinuousMul M
· 使用定理 `IsTopologicalGroup.toContinuousMul`：∀ {G : Type u_4} {inst : Topological
Space G} {inst_1 : Group G} [self : IsTopologicalGroup G], ContinuousMul G
· 使用定理 `MeasureTheory.Measure.ext_of_integral_eq_on_compactlySupported`：∀ {X : T
ype u_1} [inst : TopologicalSpace X] [T2Space X] [inst_2 : MeasurableSpace X] [B
orelSpace X]   {μ ν : MeasureTheory.Measure X} [Loca…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.integral_map`：integral_map {β} [MeasurableSpace β] {φ : α 
-> β} (hφ : AEMeasurable φ μ) {f : β -> G} (hfm : AEStronglyMeasurable f (Measur
e.map φ μ)) : ∫ …
· 使用定理 `AEMeasurable.const_mul`：AEMeasurable.const_mul [MeasurableMul M] (hf : A
EMeasurable f μ) (c : M) : AEMeasurable (fun x => c * f x) μ
· 使用定理 `ContinuousMul.measurableMul`：∀ {γ : Type u_3} [inst : TopologicalSpace γ
] [inst_1 : MeasurableSpace γ] [BorelSpace γ] [inst_3 : Mul γ]   [SeparatelyCont
inuousMul γ], Mea…
· 使用定理 `aemeasurable_id`：aemeasurable_id : AEMeasurable id μ
· 使用定理 `Continuous.aestronglyMeasurable`：∀ {α : Type u_1} {β : Type u_2} [inst :
 TopologicalSpace β] {m₀ : MeasurableSpace α} {μ : MeasureTheory.Measure α}   {f
 : α → β} [inst_1 : T…
· 使用定理 `BorelSpace.opensMeasurable`：∀ {α : Type u_6} [inst : TopologicalSpace α]
 [inst_1 : MeasurableSpace α] [BorelSpace α], OpensMeasurableSpace α
· 使用定理 `PseudoEMetricSpace.pseudoMetrizableSpace`：∀ {α : Type u_2} [inst : Pseud
oEMetricSpace α], TopologicalSpace.PseudoMetrizableSpace α
· 使用定理 `secondCountableTopologyEither_of_right`：∀ (α : Type u_6) (β : Type u_7) 
[inst : TopologicalSpace α] [inst_1 : TopologicalSpace β] [SecondCountableTopolo
gy β],   SecondCountableTopo…
· 使用定理 `instSecondCountableTopologyReal`：SecondCountableTopology ℝ
· 使用定理 `ContinuousMapClass.map_continuous`：∀ {F : Type u_1} {X : outParam (Type 
u_2)} {Y : outParam (Type u_3)} {inst : TopologicalSpace X}   {inst_1 : Topologi
calSpace Y} {inst_2 : F…
（共 84 条，此处仅展示前 30 条）
-/
instance isHaarMeasure_inducedMeasure : IsHaarMeasure (inducedMeasure H μA μC) where
  lt_top_of_isCompact K hK := by
    obtain ⟨f, hf1, hf2, hf3, hf4⟩ :=
      exists_continuousMap_one_of_isCompact_subset_isOpen hK isOpen_univ K.subset_univ
    exact lt_of_le_of_lt (RealRMK.rieszMeasure_le_of_eq_one (f := ⟨f, hf2⟩) _
      (fun x ↦ (hf4 x).1) hK (fun x hx ↦ hf1 hx)) ENNReal.ofReal_lt_top
  map_mul_left_eq_self b := by
    have : ((inducedMeasure H μA μC).map (b * ·)).Regular := Regular.map (Homeomorph.mulLeft b)
    refine ext_of_integral_eq_on_compactlySupported fun f ↦ ?_
    rw [integral_map (by fun_prop) (by fun_prop)]
    have h (x : B) : f (b * x) = f.comp (Homeomorph.mulLeft b).toCocompactMap x := rfl
    simp_rw [h, integral_inducedMeasure, integrate_apply]
    rw [← integral_mul_left_eq_self _ (ψ b)⁻¹]
    congr with c
    obtain ⟨b', rfl⟩ := H.isOpenQuotientMap.surjective c
    rw [← map_inv, ← map_mul, pushforward_apply_apply, pushforward_apply_apply]
    simp [pullback_def, mul_assoc]
  open_pos U hU := by
    rintro ⟨b, hb⟩
    obtain ⟨K, hK, hb, hKU⟩ := exists_compact_subset hU hb
    obtain ⟨f, hf1, hf2, hf3, hf4⟩ := exists_continuousMap_one_of_isCompact_subset_isOpen hK hU hKU
    have hf0 : 0 ≤ H.pushforward μA ⟨f, hf2⟩ := by
      rw [← map_zero (H.pushforward μA)]
      apply pushforward_mono
      exact fun x ↦ (hf4 x).1
    grw [← pos_iff_ne_zero, inducedMeasure,
      ← RealRMK.le_rieszMeasure_tsupport_subset (f := ⟨f, hf2⟩) _ hf4 hf3, ENNReal.ofReal_pos]
    suffices (0 : ℝ) < pushforward H μA ⟨f, hf2⟩ (ψ b) from
      (pushforward H μA ⟨f, hf2⟩).continuous.integral_pos_of_hasCompactSupport_nonneg_nonzero
        (pushforward H μA ⟨f, hf2⟩).hasCompactSupport hf0 this.ne'
    have : (Function.invFun ψ (ψ b))⁻¹ * b ∈ φ.range := by
      simp [← H.mulExact.monoidHom_ker_eq, Function.apply_invFun_apply]
    obtain ⟨a, ha⟩ := this
    replace ha : f (Function.invFun ψ (ψ b) * φ a) ≠ 0 := by simp [ha, hf1 (interior_subset hb)]
    exact (pullback H ⟨f, hf2⟩ _).continuous.integral_pos_of_hasCompactSupport_nonneg_nonzero
      (pullback H ⟨f, hf2⟩ _).hasCompactSupport (fun x ↦ (hf4 _).1) ha

set_option backward.isDefEq.respectTransparency.types false in
/-- If `φ : A →* B` and `ψ : B →* C` define a short exact sequence of topological groups, and if
`ψ` is injective on an open set `U`, then the induced measure on `U` is bounded above by
`μC Set.univ * μA {1}` (possibly infinite). -/
@[to_additive /-- If `φ : A →+ B` and `ψ : B →+ C` define a short exact sequence of additive
topological groups, and if `ψ` is injective on an open set `U`, then the induced measure on `U` is
bounded above by `μC Set.univ * μA {1}` (possibly infinite). -/]
/-
**TopologicalGroup.IsSES.inducedMeasure_lt_of_injOn** 是 Mathlib 中的一个定理，位于命名空间 `T
opologicalGroup.IsSES`。
形式化陈述：inducedMeasure_lt_of_injOn {U : Set B} (hU : IsOpen U) [DiscreteTopology A
] (h : U.InjOn ψ) : inducedMeasure H μA μC U <= μC Set.univ * μA {1}
参数：hU : IsOpen U；h : U.InjOn ψ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose₁`：contrapose₁ {p q : Prop} : (¬ q -
> ¬ p) -> (p -> q)
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `IsOpen.measure_pos`：∀ {X : Type u_1} [inst : TopologicalSpace X] {m : Me
asurableSpace X} (μ : MeasureTheory.Measure X) [μ.IsOpenPosMeasure]   {U : Set X
}, IsOpe…
· 使用定理 `MeasureTheory.Measure.IsHaarMeasure.toIsOpenPosMeasure`：∀ {G : Type u_3}
 {inst : Group G} {inst_1 : TopologicalSpace G} {inst_2 : MeasurableSpace G}   {
μ : MeasureTheory.Measure G} [self : μ.IsHaa…
· 使用定理 `isOpen_discrete`：isOpen_discrete (s : Set α) : IsOpen s
· 使用定理 `Set.singleton_nonempty`：singleton_nonempty (a : α) : ({a} : Set α).Nonem
pty
· 使用定理 `IsCompact.measure_lt_top`：∀ {α : Type u_1} {m0 : MeasurableSpace α} [ins
t : TopologicalSpace α] {μ : MeasureTheory.Measure α}   [MeasureTheory.IsFiniteM
easureOnCompac…
· 使用定理 `MeasureTheory.Measure.IsHaarMeasure.toIsFiniteMeasureOnCompacts`：∀ {G : 
Type u_3} {inst : Group G} {inst_1 : TopologicalSpace G} {inst_2 : MeasurableSpa
ce G}   {μ : MeasureTheory.Measure G} [self : μ.IsHaa…
· 使用定理 `isCompact_singleton`：isCompact_singleton {x : X} : IsCompact ({x} : Set 
X)
· 使用定理 `MeasureTheory.Measure.Regular.innerRegular`：∀ {α : Type u_1} {inst : Mea
surableSpace α} {inst_1 : TopologicalSpace α} {μ : MeasureTheory.Measure α}   [s
elf : μ.Regular], μ.InnerRegular…
· 使用引理 `exists_continuousMap_one_of_isCompact_subset_isOpen`：exists_continuousMa
p_one_of_isCompact_subset_isOpen [R1Space X] [LocallyCompactSpace X] {K V : Set 
X} (hK : IsCompact K) (hV : IsOpen V) (hK…
· 使用定理 `instR1Space`：∀ {X : Type u_1} [inst : TopologicalSpace X] [RegularSpace 
X], R1Space X
· 使用定理 `IsTopologicalGroup.regularSpace`：∀ (G : Type w) [inst : TopologicalSpace
 G] [inst_1 : Group G] [IsTopologicalGroup G], RegularSpace G
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用引理 `lt_of_lt_of_le`：lt_of_lt_of_le (hab : a < b) (hbc : b <= c) : a < c
· 使用引理 `RealRMK.rieszMeasure_le_of_eq_one`：rieszMeasure_le_of_eq_one {f : C_c(X,
 Real)} (hf : forall x, 0 <= f x) {K : Set X} (hK : IsCompact K) (hfK : forall x
 in K, f x = 1) : riesz…
· 使用定理 `TopologicalGroup.IsSES.integrate_mono`：integrate_mono {f g : CompactlySu
pportedContinuousMap B Real} (h : f <= g) : integrate H μA μC f <= integrate H μ
A μC g
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `eq_top_or_lt_top`：eq_top_or_lt_top (a : α) : a = ⊤ ∨ a < ⊤
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `ENNReal.top_mul`：∀ {a : ENNReal}, a ≠ 0 → ⊤ * a = ⊤
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `ENNReal.ofReal_le_iff_le_toReal`：ofReal_le_iff_le_toReal {a : Real} {b :
 Real>=0∞} (hb : b != ∞) : ENNReal.ofReal a <= b ↔ a <= ENNReal.toReal b
（共 83 条，此处仅展示前 30 条）
-/
theorem inducedMeasure_lt_of_injOn {U : Set B} (hU : IsOpen U) [DiscreteTopology A]
    (h : U.InjOn ψ) :
    inducedMeasure H μA μC U ≤ μC Set.univ * μA {1} := by
  contrapose! h
  have ho : 0 < μA {1} := (isOpen_discrete {1}).measure_pos _ (Set.singleton_nonempty 1)
  have ht : μA {1} < ⊤ := isCompact_singleton.measure_lt_top
  obtain ⟨K, hKU, hK, h⟩ := Regular.innerRegular hU _ h
  obtain ⟨f, hf1, hf2, hf3, hf4⟩ := exists_continuousMap_one_of_isCompact_subset_isOpen hK hU hKU
  replace h : μC Set.univ * μA {1} < ENNReal.ofReal (∫ c : C, pushforward H μA ⟨f, hf2⟩ c ∂μC) :=
    lt_of_lt_of_le h ((RealRMK.rieszMeasure_le_of_eq_one (f := ⟨f, hf2⟩) _ (fun x ↦ (hf4 x).1)
      hK (fun x hx ↦ hf1 hx)))
  obtain ⟨c, hc⟩ : ∃ c : C, (μA {1}).toReal < pushforward H μA ⟨f, hf2⟩ c := by
    contrapose! h
    rcases eq_top_or_lt_top (μC Set.univ) with hC | hC
    · simp [hC, ENNReal.top_mul ho.ne']
    · have : IsFiniteMeasure μC := ⟨hC⟩
      rw [ENNReal.ofReal_le_iff_le_toReal (ENNReal.mul_lt_top hC ht).ne, ENNReal.toReal_mul,
        ← Measure.real_def, ← smul_eq_mul, ← integral_const]
      exact integral_mono (H.pushforward μA ⟨f, hf2⟩).integrable (integrable_const _) h
  contrapose! hc
  obtain ⟨b, rfl⟩ := H.isOpenQuotientMap.surjective c
  simp only [pushforward_apply_apply, pullback_def, CompactlySupportedContinuousMap.coe_mk]
  rw [← setIntegral_support]
  have key : (Function.support fun a ↦ f (b * φ a)).Subsingleton := by
    intro a ha b hb
    simpa [H.isClosedEmbedding.injective.eq_iff] using hc (hf3 (subset_tsupport _ ha))
      (hf3 (subset_tsupport _ hb)) (by simp [H.mulExact.apply_apply_eq_one])
  obtain h | ⟨a, ha⟩ := key.eq_empty_or_singleton
  · simp [h]
  · rw [ha, integral_singleton, real_def, haar_singleton, smul_eq_mul, mul_le_iff_le_one_right]
    · exact (hf4 _).2
    · exact ENNReal.toReal_pos ho.ne' ht.ne

end TopologicalGroup.IsSES

