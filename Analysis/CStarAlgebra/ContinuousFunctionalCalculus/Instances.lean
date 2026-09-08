/-
Copyright (c) 2024 Jireh Loreaux. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jireh Loreaux
-/
module

public import Mathlib.Analysis.Complex.Spectrum
public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Restrict
public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Unique
public import Mathlib.Analysis.CStarAlgebra.Unitization
public import Mathlib.Analysis.Normed.Algebra.Spectrum
public import Mathlib.Analysis.RCLike.Lemmas

/-! # Instances of the continuous functional calculus

## Main theorems

* `IsSelfAdjoint.instContinuousFunctionalCalculus`: the continuous functional calculus for
  selfadjoint elements in a `ℂ`-algebra with a continuous functional calculus for normal elements
  and where every element has compact spectrum. In particular, this includes unital C⋆-algebras
  over `ℂ`.
* `Nonneg.instContinuousFunctionalCalculus`: the continuous functional calculus for nonnegative
  elements in an `ℝ`-algebra with a continuous functional calculus for selfadjoint elements,
  where every element has compact spectrum, and where nonnegative elements have nonnegative
  spectrum. In particular, this includes unital C⋆-algebras over `ℝ`.

## Tags

continuous functional calculus, normal, selfadjoint
-/

@[expose] public section

open Topology

noncomputable section

local notation "σₙ" => quasispectrum
local notation "σ" => spectrum

/-!
### Pull back a non-unital instance from a unital one on the unitization
-/

section RCLike

variable {𝕜 A : Type*} [RCLike 𝕜] [NonUnitalNormedRing A] [StarRing A]
variable [NormedSpace 𝕜 A] [IsScalarTower 𝕜 A A] [SMulCommClass 𝕜 A A]
variable [StarModule 𝕜 A] {p : A → Prop} {p₁ : Unitization 𝕜 A → Prop}

local postfix:max "⁺¹" => Unitization 𝕜

variable (hp₁ : ∀ {x : A}, p₁ x ↔ p x) (a : A) (ha : p a)
variable [ClosedEmbeddingContinuousFunctionalCalculus 𝕜 (Unitization 𝕜 A) p₁]

open scoped ContinuousMapZero


open Unitization in
/--
This is an auxiliary definition used for constructing an instance of the non-unital continuous
functional calculus given an instance of the unital one on the unitization.

This is the natural non-unital star homomorphism obtained from the chain
```lean
calc
  C(σₙ 𝕜 a, 𝕜)₀ →⋆ₙₐ[𝕜] C(σₙ 𝕜 a, 𝕜) := ContinuousMapZero.toContinuousMapHom
  _             ≃⋆[𝕜] C(σ 𝕜 (↑a : A⁺¹), 𝕜) := Homeomorph.compStarAlgEquiv'
  _             →⋆ₐ[𝕜] A⁺¹ := cfcHom
```
This range of this map is contained in the range of `(↑) : A → A⁺¹` (see `cfcₙAux_mem_range_inr`),
and so we may restrict it to `A` to get the necessary homomorphism for the non-unital continuous
functional calculus.
-/
/-
**cfc** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：{R : Type u_3} →   {A : Type u_4} →     {p : A → Prop} →       [inst : Com
mSemiring R] →         [inst_1 : StarRing R] →           [inst_2 : MetricSpace R
] →             [inst_3 : IsTopologicalSemiring R] →               [inst_4 : Con
tinuousStar R] →                 [inst_5 : TopologicalSpace A] →                
   [inst_6 : Ring A] →                     [inst_7 : StarRing A] →              
         [inst_8 : Algebra R A] → [instCFC : ContinuousFunctionalCalculus R A p]
 → (R → R) → A → A
参数：R → R。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
This is an auxiliary definition used for constructing an instance of the non-uni
tal continuous
functional calculus given an instance of the unital one on the unitization.

This is the natural non-unital star homomorphism obtained from the chain
```lean
calc
  C(σₙ 𝕜 a, 𝕜)₀ →⋆ₙₐ[𝕜] C(σₙ 𝕜 a, 𝕜) := ContinuousMapZero.toContinuousMapHom
  _             ≃⋆[𝕜] C(σ 𝕜 (↑a : A⁺¹), 𝕜) := Homeomorph.compStarAlgEquiv'
  _             →⋆ₐ[𝕜] A⁺¹ := cfcHom
```
This range of this map is contained in the range of `(↑) : A → A⁺¹` (see `cfcₙAu
x_mem_range_inr`),
and so we may restrict it to `A` to get the necessary homomorphism for the non-u
nital continuous
functional calculus.
-/
noncomputable def cfcₙAux : C(σₙ 𝕜 a, 𝕜)₀ →⋆ₙₐ[𝕜] A⁺¹ :=
  (cfcHom (R := 𝕜) (hp₁.mpr ha) : C(σ 𝕜 (a : A⁺¹), 𝕜) →⋆ₙₐ[𝕜] A⁺¹) |>.comp
    (Homeomorph.compStarAlgEquiv' 𝕜 𝕜 <| .setCongr <| (quasispectrum_eq_spectrum_inr' 𝕜 𝕜 a).symm)
    |>.comp ContinuousMapZero.toContinuousMapHom
/-
**cfc** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：{R : Type u_3} →   {A : Type u_4} →     {p : A → Prop} →       [inst : Com
mSemiring R] →         [inst_1 : StarRing R] →           [inst_2 : MetricSpace R
] →             [inst_3 : IsTopologicalSemiring R] →               [inst_4 : Con
tinuousStar R] →                 [inst_5 : TopologicalSpace A] →                
   [inst_6 : Ring A] →                     [inst_7 : StarRing A] →              
         [inst_8 : Algebra R A] → [instCFC : ContinuousFunctionalCalculus R A p]
 → (R → R) → A → A
参数：R → R。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma cfcₙAux_id : cfcₙAux hp₁ a ha (.id _) = a := cfcHom_id (hp₁.mpr ha)
/-
**continuous_cfc** 是 Mathlib 中的一个引理，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma continuous_cfcₙAux : Continuous (cfcₙAux hp₁ a ha) :=
  (cfcHom_continuous (hp₁.mpr ha)).comp <|
    (ContinuousMap.continuous_precomp _).comp <|
    ContinuousMapZero.isEmbedding_toContinuousMap.continuous
/-
**cfc** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：{R : Type u_3} →   {A : Type u_4} →     {p : A → Prop} →       [inst : Com
mSemiring R] →         [inst_1 : StarRing R] →           [inst_2 : MetricSpace R
] →             [inst_3 : IsTopologicalSemiring R] →               [inst_4 : Con
tinuousStar R] →                 [inst_5 : TopologicalSpace A] →                
   [inst_6 : Ring A] →                     [inst_7 : StarRing A] →              
         [inst_8 : Algebra R A] → [instCFC : ContinuousFunctionalCalculus R A p]
 → (R → R) → A → A
参数：R → R。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma cfcₙAux_injective : Function.Injective (cfcₙAux hp₁ a ha) :=
  (cfcHom_injective (hp₁.mpr ha)).comp <|
    .comp (Equiv.injective _) ContinuousMapZero.isEmbedding_toContinuousMap.injective
/-
**spec_cfc** 是 Mathlib 中的一个引理，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma spec_cfcₙAux (f : C(σₙ 𝕜 a, 𝕜)₀) : σ 𝕜 (cfcₙAux hp₁ a ha f) = Set.range f := by
  rw [cfcₙAux, NonUnitalStarAlgHom.comp_assoc, NonUnitalStarAlgHom.comp_apply]
  simp only [NonUnitalStarAlgHom.comp_apply, NonUnitalStarAlgHom.coe_coe]
  rw [cfcHom_map_spectrum (hp₁.mpr ha) (R := 𝕜) _]
  simp

open Unitization in
/-
**isClosedEmbedding_cfc** 是 Mathlib 中的一个引理，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma isClosedEmbedding_cfcₙAux : IsClosedEmbedding (cfcₙAux hp₁ a ha) := by
  simp only [cfcₙAux, NonUnitalStarAlgHom.coe_comp]
  refine ((cfcHom_isClosedEmbedding (hp₁.mpr ha)).comp ?_).comp
    ContinuousMapZero.isClosedEmbedding_toContinuousMap
  let e : C(σₙ 𝕜 a, 𝕜) ≃ₜ C(σ 𝕜 (a : A⁺¹), 𝕜) :=
    (Homeomorph.setCongr (quasispectrum_eq_spectrum_inr' 𝕜 𝕜 a)).arrowCongr (.refl _)
  exact e.isClosedEmbedding

variable [CompleteSpace A]
/-
**cfc** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：{R : Type u_3} →   {A : Type u_4} →     {p : A → Prop} →       [inst : Com
mSemiring R] →         [inst_1 : StarRing R] →           [inst_2 : MetricSpace R
] →             [inst_3 : IsTopologicalSemiring R] →               [inst_4 : Con
tinuousStar R] →                 [inst_5 : TopologicalSpace A] →                
   [inst_6 : Ring A] →                     [inst_7 : StarRing A] →              
         [inst_8 : Algebra R A] → [instCFC : ContinuousFunctionalCalculus R A p]
 → (R → R) → A → A
参数：R → R。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma cfcₙAux_mem_range_inr (f : C(σₙ 𝕜 a, 𝕜)₀) :
    cfcₙAux hp₁ a ha f ∈ NonUnitalStarAlgHom.range (Unitization.inrNonUnitalStarAlgHom 𝕜 A) := by
  have h₁ := (continuous_cfcₙAux hp₁ a ha).range_subset_closure_image_dense
    (ContinuousMapZero.adjoin_id_dense (σₙ 𝕜 a)) ⟨f, rfl⟩
  rw [← SetLike.mem_coe]
  refine closure_minimal ?_ ?_ h₁
  · rw [← NonUnitalStarSubalgebra.coe_map, SetLike.coe_subset_coe, NonUnitalStarSubalgebra.map_le]
    apply NonUnitalStarAlgebra.adjoin_le
    apply Set.singleton_subset_iff.mpr
    rw [SetLike.mem_coe, NonUnitalStarSubalgebra.mem_comap, cfcₙAux_id hp₁ a ha]
    exact ⟨a, rfl⟩
  · simp only [NonUnitalStarAlgHom.coe_range]
    convert! IsClosed.preimage (Unitization.continuous_fst (𝕜 := 𝕜)) isClosed_singleton
    aesop

variable [CStarRing A]

include hp₁ in
open Unitization NonUnitalStarAlgHom in
/-
**RCLike.nonUnitalContinuousFunctionalCalculus** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：RCLike.nonUnitalContinuousFunctionalCalculus : NonUnitalContinuousFunction
alCalculus 𝕜 A p where predicate_zero
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `IsTopologicalDivisionRing.toIsTopologicalRing`：∀ {K : Type u_1} {inst : 
DivisionRing K} {inst_1 : TopologicalSpace K} [self : IsTopologicalDivisionRing 
K],   IsTopologicalRing K
· 使用定理 `NormedDivisionRing.to_isTopologicalDivisionRing`：∀ {α : Type u_1} [inst 
: NormedDivisionRing α], IsTopologicalDivisionRing α
· 使用定理 `RCLike.instContinuousStar`：∀ {K : Type u_1} [inst : RCLike K], Continuou
sStar K
· 使用定理 `IsLocalRing.toNontrivial`：∀ {R : Type u_1} {inst : Semiring R} [self : I
sLocalRing R], Nontrivial R
· 使用定理 `Field.instIsLocalRing`：∀ (K : Type u_3) [inst : Field K], IsLocalRing K
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Unitization.inr_zero`：inr_zero [Zero R] [Zero A] : ↑(0 : A) = (0 : Uniti
zation R A)
· 使用引理 `cfc_predicate_zero`：cfc_predicate_zero : p 0
· 使用定理 `ClosedEmbeddingContinuousFunctionalCalculus.toContinuousFunctionalCalcul
us`：∀ {R : Type u_1} {A : Type u_2} {p : outParam (A → Prop)} {inst : CommSemiri
ng R} {inst_1 : StarRing R}   {inst_2 : MetricSpace R} {inst_3 :…
· 使用定理 `quasispectrum.instCompactSpace`：∀ {𝕜 : Type u_1} [inst : NormedField 𝕜] 
{B : Type u_3} [inst_1 : NonUnitalNormedRing B] [inst_2 : NormedSpace 𝕜 B]   [Co
mpleteSpace B] [IsSc…
· 使用定理 `FiniteDimensional.proper_real`：∀ (E : Type u) [inst : NormedAddCommGroup
 E] [inst_1 : NormedSpace ℝ E] [FiniteDimensional ℝ E], ProperSpace E
· 使用定理 `IsSemitopologicalSemiring.toContinuousAdd`：∀ {R : Type u_2} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSemitopologic
alSemiring R], ContinuousAdd R
· 使用定理 `IsSemitopologicalRing.toIsSemitopologicalSemiring`：∀ {R : Type u_2} {ins
t : TopologicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopolog
icalRing R],   IsSemitopologicalSemirin…
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `IsSemitopologicalSemiring.toSeparatelyContinuousMul`：∀ {R : Type u_2} {i
nst : TopologicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSem
itopologicalSemiring R], SeparatelyContin…
· 使用定理 `NonUnitalStarAlgHom.instNonUnitalAlgHomClass`：∀ {R : Type u_1} {A : Type
 u_2} {B : Type u_3} [inst : Monoid R] [inst_1 : NonUnitalNonAssocSemiring A]   
[inst_2 : DistribMulAction R A] [i…
· 使用定理 `NonUnitalStarAlgHom.instStarHomClass`：∀ {R : Type u_1} {A : Type u_2} {B
 : Type u_3} [inst : Monoid R] [inst_1 : NonUnitalNonAssocSemiring A]   [inst_2 
: DistribMulAction R A] [i…
· 使用定理 `instNonUnitalAlgHomClassOfNonUnitalAlgEquivClass`：∀ {F : Type u_1} {R : 
Type u_2} {A : Type u_3} {B : Type u_4} [inst : Monoid R] [inst_1 : NonUnitalNon
AssocSemiring A]   [inst_2 : DistribMu…
· 使用定理 `StarAlgEquiv.instNonUnitalAlgEquivClass`：∀ {R : Type u_2} {A : Type u_3}
 {B : Type u_4} [inst : Add A] [inst_1 : Add B] [inst_2 : Mul A] [inst_3 : Mul B
]   [inst_4 : SMul R A] [inst…
· 使用定理 `NonUnitalStarRingHomClass.toStarHomClass`：∀ {F : Type u_1} {A : outParam
 (Type u_2)} {B : outParam (Type u_3)} {inst : NonUnitalNonAssocSemiring A}   {i
nst_1 : Star A} {inst_2 : NonU…
· 使用定理 `RingEquivClass.toNonUnitalRingHomClass`：∀ {F : Type u_1} {R : Type u_4} 
{S : Type u_5} [inst : EquivLike F R S] [inst_1 : NonUnitalNonAssocSemiring R]  
 [inst_2 : NonUnitalNonAssoc…
· 使用定理 `StarRingEquivClass.toRingEquivClass`：∀ {F : Type u_1} {A : outParam (Typ
e u_2)} {B : outParam (Type u_3)} {inst : Add A} {inst_1 : Mul A} {inst_2 : Star
 A}   {inst_3 : Add B} {i…
· 使用定理 `StarAlgEquiv.instStarRingEquivClass`：∀ {R : Type u_2} {A : Type u_3} {B 
: Type u_4} [inst : Add A] [inst_1 : Add B] [inst_2 : Mul A] [inst_3 : Mul B]   
[inst_4 : SMul R A] [inst…
· 使用定理 `StarRingEquivClass.instNonUnitalStarRingHomClass`：∀ {F : Type u_1} {A : 
Type u_2} {B : Type u_3} [inst : NonUnitalNonAssocSemiring A] [inst_1 : Star A] 
  [inst_2 : NonUnitalNonAssocSemiring …
· 使用引理 `cfcₙAux_mem_range_inr`：cfcₙAux_mem_range_inr (f : C(σₙ 𝕜 a, 𝕜)₀) : cfcₙA
ux hp₁ a ha f in NonUnitalStarAlgHom.range (Unitization.inrNonUnitalStarAlgHom 𝕜
 A)
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `StarAlgEquiv.apply_symm_apply`：apply_symm_apply (e : A ≃⋆ₐ[R] B) : foral
l x, e (e.symm x) = x
· 使用定理 `IsTopologicalSemiring.toIsSemitopologicalSemiring`：∀ (R : Type u_2) [ins
t : TopologicalSpace R] [inst_1 : NonUnitalNonAssocSemiring R] [IsTopologicalSem
iring R],   IsSemitopologicalSemiring R
（共 52 条，此处仅展示前 30 条）
-/
theorem RCLike.nonUnitalContinuousFunctionalCalculus :
    NonUnitalContinuousFunctionalCalculus 𝕜 A p where
  predicate_zero := by
    rw [← hp₁, Unitization.inr_zero 𝕜]
    exact cfc_predicate_zero 𝕜
  exists_cfc_of_predicate a ha := by
    let ψ : C(σₙ 𝕜 a, 𝕜)₀ →⋆ₙₐ[𝕜] A := comp (inrRangeEquiv 𝕜 A).symm <|
      codRestrict (cfcₙAux hp₁ a ha) _ (cfcₙAux_mem_range_inr hp₁ a ha)
    have coe_ψ (f : C(σₙ 𝕜 a, 𝕜)₀) : ψ f = cfcₙAux hp₁ a ha f :=
      congr_arg Subtype.val <| (inrRangeEquiv 𝕜 A).apply_symm_apply
        ⟨cfcₙAux hp₁ a ha f, cfcₙAux_mem_range_inr hp₁ a ha f⟩
    refine ⟨ψ, ?continuous, ?injective, ?map_id, fun f ↦ ?map_spec, fun f ↦ ?isStarNormal⟩
    case continuous =>
      rw [isometry_inr (𝕜 := 𝕜) |>.isEmbedding.continuous_iff]
      have := continuous_cfcₙAux hp₁ a ha
      simp only [coe_comp, NonUnitalStarAlgHom.coe_coe, Function.comp_def,
        inrRangeEquiv_symm_apply, coe_codRestrict, ψ]
      fun_prop
    case injective =>
      have h₁ : Function.Injective ⇑(codRestrict (cfcₙAux hp₁ a ha) _
          (cfcₙAux_mem_range_inr hp₁ a ha)) :=
        (Set.injective_codRestrict _).mpr (cfcₙAux_injective hp₁ a ha)
      simpa [ψ] using (inrRangeEquiv 𝕜 A).symm.injective.comp h₁
    case map_id => exact inr_injective (R := 𝕜) <| coe_ψ _ ▸ cfcₙAux_id hp₁ a ha
    case map_spec =>
      exact quasispectrum_eq_spectrum_inr' 𝕜 𝕜 (ψ f) ▸ coe_ψ _ ▸ spec_cfcₙAux hp₁ a ha f
    case isStarNormal => exact hp₁.mp <| coe_ψ _ ▸ cfcHom_predicate (R := 𝕜) (hp₁.mpr ha) _

open Unitization in
open scoped NonUnitalContinuousFunctionalCalculus in
/-
**inrNonUnitalStarAlgHom_comp_cfc** 是 Mathlib 中的一个引理，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma inrNonUnitalStarAlgHom_comp_cfcₙHom_eq_cfcₙAux (a : A) (ha : p a) :
    letI _ := RCLike.nonUnitalContinuousFunctionalCalculus hp₁
    (inrNonUnitalStarAlgHom 𝕜 A).comp (cfcₙHom ha) = cfcₙAux hp₁ a ha := by
  let _ := RCLike.nonUnitalContinuousFunctionalCalculus hp₁
  apply ContinuousMapZero.UniqueHom.eq_of_continuous_of_map_id _ _ _
    (Unitization.continuous_inr.comp <| cfcₙHom_continuous ha)
    (continuous_cfcₙAux hp₁ a ha)
    (by simp [cfcₙHom_id ha, cfcₙAux_id hp₁ a ha])
  all_goals infer_instance


include hp₁ in
open Unitization NonUnitalStarAlgHom in
/-
**RCLike.nonUnitalContinuousFunctionalCalculusIsClosedEmbedding** 是 Mathlib 中的一个
定理，位于命名空间 ``。
形式化陈述：RCLike.nonUnitalContinuousFunctionalCalculusIsClosedEmbedding : NonUnitalC
losedEmbeddingContinuousFunctionalCalculus 𝕜 A p where toNonUnitalContinuousFunc
tionalCalculus
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `IsTopologicalDivisionRing.toIsTopologicalRing`：∀ {K : Type u_1} {inst : 
DivisionRing K} {inst_1 : TopologicalSpace K} [self : IsTopologicalDivisionRing 
K],   IsTopologicalRing K
· 使用定理 `NormedDivisionRing.to_isTopologicalDivisionRing`：∀ {α : Type u_1} [inst 
: NormedDivisionRing α], IsTopologicalDivisionRing α
· 使用定理 `RCLike.instContinuousStar`：∀ {K : Type u_1} [inst : RCLike K], Continuou
sStar K
· 使用定理 `IsLocalRing.toNontrivial`：∀ {R : Type u_1} {inst : Semiring R} [self : I
sLocalRing R], Nontrivial R
· 使用定理 `Field.instIsLocalRing`：∀ (K : Type u_3) [inst : Field K], IsLocalRing K
· 使用定理 `RCLike.nonUnitalContinuousFunctionalCalculus`：RCLike.nonUnitalContinuous
FunctionalCalculus : NonUnitalContinuousFunctionalCalculus 𝕜 A p where predicate
_zero
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `IsSemitopologicalSemiring.toContinuousAdd`：∀ {R : Type u_2} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSemitopologic
alSemiring R], ContinuousAdd R
· 使用定理 `IsTopologicalSemiring.toIsSemitopologicalSemiring`：∀ (R : Type u_2) [ins
t : TopologicalSpace R] [inst_1 : NonUnitalNonAssocSemiring R] [IsTopologicalSem
iring R],   IsSemitopologicalSemiring R
· 使用定理 `IsSemitopologicalSemiring.toSeparatelyContinuousMul`：∀ {R : Type u_2} {i
nst : TopologicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSem
itopologicalSemiring R], SeparatelyContin…
· 使用定理 `Topology.IsClosedEmbedding.of_comp_iff`：∀ {X : Type u_1} {Y : Type u_2} 
{Z : Type u_3} {f : X → Y} {g : Y → Z} [inst : TopologicalSpace X]   [inst_1 : T
opologicalSpace Y] [inst_2 :…
· 使用定理 `Isometry.isClosedEmbedding`：isClosedEmbedding [CompleteSpace α] [EMetric
Space γ] {f : α -> γ} (hf : Isometry f) : IsClosedEmbedding f
· 使用引理 `Unitization.isometry_inr`：isometry_inr : Isometry ((↑) : A -> Unitizatio
n 𝕜 A)
· 使用定理 `IsSemitopologicalRing.toIsSemitopologicalSemiring`：∀ {R : Type u_2} {ins
t : TopologicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopolog
icalRing R],   IsSemitopologicalSemirin…
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `inrNonUnitalStarAlgHom_comp_cfcₙHom_eq_cfcₙAux`：inrNonUnitalStarAlgHom_c
omp_cfcₙHom_eq_cfcₙAux (a : A) (ha : p a) : letI _
· 使用引理 `isClosedEmbedding_cfcₙAux`：isClosedEmbedding_cfcₙAux : IsClosedEmbedding
 (cfcₙAux hp₁ a ha)
-/
theorem RCLike.nonUnitalContinuousFunctionalCalculusIsClosedEmbedding :
    NonUnitalClosedEmbeddingContinuousFunctionalCalculus 𝕜 A p where
  toNonUnitalContinuousFunctionalCalculus := RCLike.nonUnitalContinuousFunctionalCalculus hp₁
  isClosedEmbedding a ha := by
    apply isometry_inr (𝕜 := 𝕜) (A := A) |>.isClosedEmbedding |>.of_comp_iff.mp
    convert! isClosedEmbedding_cfcₙAux hp₁ a ha
    congrm (⇑$(inrNonUnitalStarAlgHom_comp_cfcₙHom_eq_cfcₙAux hp₁ a ha))

end RCLike

/-!
### Continuous functional calculus for selfadjoint elements
-/

section SelfAdjointNonUnital

variable {A : Type*} [TopologicalSpace A] [NonUnitalRing A] [StarRing A] [Module ℂ A]
  [IsScalarTower ℂ A A] [SMulCommClass ℂ A A]
  [NonUnitalContinuousFunctionalCalculus ℂ A IsStarNormal]

/-- An element in a non-unital C⋆-algebra is selfadjoint if and only if it is normal and its
quasispectrum is contained in `ℝ`. -/
/-
**isSelfAdjoint_iff_isStarNormal_and_quasispectrumRestricts** 是 Mathlib 中的一个引理，位
于命名空间 ``。
形式化陈述：isSelfAdjoint_iff_isStarNormal_and_quasispectrumRestricts {a : A} : IsSelf
Adjoint a ↔ IsStarNormal a ∧ QuasispectrumRestricts a Complex.reCLM
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Complex.instNontrivial`：Nontrivial ℂ
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `IsTopologicalDivisionRing.toIsTopologicalRing`：∀ {K : Type u_1} {inst : 
DivisionRing K} {inst_1 : TopologicalSpace K} [self : IsTopologicalDivisionRing 
K],   IsTopologicalRing K
· 使用定理 `NormedDivisionRing.to_isTopologicalDivisionRing`：∀ {α : Type u_1} [inst 
: NormedDivisionRing α], IsTopologicalDivisionRing α
· 使用定理 `Complex.instContinuousStar`：ContinuousStar ℂ
· 使用定理 `IsSelfAdjoint.isStarNormal`：isStarNormal {R : Type*} [Mul R] [Star R] {x
 : R} (hx : IsSelfAdjoint x) : IsStarNormal x
· 使用引理 `eqOn_of_cfcₙ_eq_cfcₙ`：eqOn_of_cfcₙ_eq_cfcₙ {f g : R -> R} {a : A} (h : c
fcₙ f a = cfcₙ g a) (ha : p a
· 使用定理 `IsSelfAdjoint.star_eq`：star_eq [Star R] {x : R} (hx : IsSelfAdjoint x) :
 star x = x
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `cfcₙ_id`：cfcₙ_id : cfcₙ (id : R -> R) a = a
· 使用引理 `cfcₙ_star`：cfcₙ_star : cfcₙ (fun x => star (f x)) a = star (cfcₙ f a)
· 使用定理 `ContinuousOn.star`：ContinuousOn.star (hf : ContinuousOn f s) : Continuou
sOn (fun x => star (f x)) s
· 使用定理 `continuousOn_id'`：continuousOn_id' (s : Set α) : ContinuousOn (fun x : α
 => x) s
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `star_zero`：star_zero [AddMonoid R] [StarAddMonoid R] : star (0 : R) = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Complex.conj_eq_iff_re`：conj_eq_iff_re {z : Complex} : conj z = z ↔ (z.r
e : Complex) = z
· 使用定理 `Complex.ofReal_re`：ofReal_re (r : Real) : Complex.re (r : Complex) = r
· 使用定理 `isSelfAdjoint_iff`：∀ {R : Type u_1} [inst : Star R] {x : R}, IsSelfAdjoi
nt x ↔ star x = x
· 使用引理 `cfcₙ_star_id`：cfcₙ_star_id : cfcₙ (star · : R -> R) a = star a
· 使用引理 `cfcₙ_congr`：cfcₙ_congr {f g : R -> R} {a : A} (hfg : (σₙ R a).EqOn f g) 
: cfcₙ f a = cfcₙ g a
· 使用定理 `QuasispectrumRestricts.algebraMap_image`：algebraMap_image (h : Quasispec
trumRestricts a f) : algebraMap R S '' quasispectrum R a = quasispectrum S a
· 使用定理 `Complex.conj_ofReal`：conj_ofReal (r : Real) : conj (r : Complex) = r

--- 原说明 ---
An element in a non-unital C⋆-algebra is selfadjoint if and only if it is normal
 and its
quasispectrum is contained in `ℝ`.
-/
lemma isSelfAdjoint_iff_isStarNormal_and_quasispectrumRestricts {a : A} :
    IsSelfAdjoint a ↔ IsStarNormal a ∧ QuasispectrumRestricts a Complex.reCLM := by
  refine ⟨fun ha ↦ ⟨ha.isStarNormal, ⟨fun x hx ↦ ?_, Complex.ofReal_re⟩⟩, ?_⟩
  · have := eqOn_of_cfcₙ_eq_cfcₙ <|
      (cfcₙ_star (id : ℂ → ℂ) a).symm ▸ (cfcₙ_id ℂ a).symm ▸ ha.star_eq
    exact Complex.conj_eq_iff_re.mp (by simpa using this hx)
  · rintro ⟨ha₁, ha₂⟩
    rw [isSelfAdjoint_iff]
    nth_rw 2 [← cfcₙ_id ℂ a]
    rw [← cfcₙ_star_id a (R := ℂ)]
    refine cfcₙ_congr fun x hx ↦ ?_
    obtain ⟨x, -, rfl⟩ := ha₂.algebraMap_image.symm ▸ hx
    exact Complex.conj_ofReal _
/-
**IsSelfAdjoint.quasispectrumRestricts** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：IsSelfAdjoint.quasispectrumRestricts {a : A} (ha : IsSelfAdjoint a) : Quas
ispectrumRestricts a Complex.reCLM
参数：ha : IsSelfAdjoint a。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Complex.instNontrivial`：Nontrivial ℂ
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `IsTopologicalDivisionRing.toIsTopologicalRing`：∀ {K : Type u_1} {inst : 
DivisionRing K} {inst_1 : TopologicalSpace K} [self : IsTopologicalDivisionRing 
K],   IsTopologicalRing K
· 使用定理 `NormedDivisionRing.to_isTopologicalDivisionRing`：∀ {α : Type u_1} [inst 
: NormedDivisionRing α], IsTopologicalDivisionRing α
· 使用定理 `Complex.instContinuousStar`：ContinuousStar ℂ
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `isSelfAdjoint_iff_isStarNormal_and_quasispectrumRestricts`：isSelfAdjoint
_iff_isStarNormal_and_quasispectrumRestricts {a : A} : IsSelfAdjoint a ↔ IsStarN
ormal a ∧ QuasispectrumRestricts a Complex.reCL…
-/
lemma IsSelfAdjoint.quasispectrumRestricts {a : A} (ha : IsSelfAdjoint a) :
    QuasispectrumRestricts a Complex.reCLM :=
  isSelfAdjoint_iff_isStarNormal_and_quasispectrumRestricts |>.mp ha |>.2

/-- A normal element whose `ℂ`-quasispectrum is contained in `ℝ` is selfadjoint. -/
/-
**QuasispectrumRestricts.isSelfAdjoint** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：QuasispectrumRestricts.isSelfAdjoint (a : A) (ha : QuasispectrumRestricts 
a Complex.reCLM) [IsStarNormal a] : IsSelfAdjoint a
参数：a : A；ha : QuasispectrumRestricts a Complex.reCLM。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Complex.instNontrivial`：Nontrivial ℂ
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `IsTopologicalDivisionRing.toIsTopologicalRing`：∀ {K : Type u_1} {inst : 
DivisionRing K} {inst_1 : TopologicalSpace K} [self : IsTopologicalDivisionRing 
K],   IsTopologicalRing K
· 使用定理 `NormedDivisionRing.to_isTopologicalDivisionRing`：∀ {α : Type u_1} [inst 
: NormedDivisionRing α], IsTopologicalDivisionRing α
· 使用定理 `Complex.instContinuousStar`：ContinuousStar ℂ
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `isSelfAdjoint_iff_isStarNormal_and_quasispectrumRestricts`：isSelfAdjoint
_iff_isStarNormal_and_quasispectrumRestricts {a : A} : IsSelfAdjoint a ↔ IsStarN
ormal a ∧ QuasispectrumRestricts a Complex.reCL…

--- 原说明 ---
A normal element whose `ℂ`-quasispectrum is contained in `ℝ` is selfadjoint.
-/
lemma QuasispectrumRestricts.isSelfAdjoint (a : A) (ha : QuasispectrumRestricts a Complex.reCLM)
    [IsStarNormal a] : IsSelfAdjoint a :=
  isSelfAdjoint_iff_isStarNormal_and_quasispectrumRestricts.mpr ⟨‹_›, ha⟩
/-
**IsSelfAdjoint.instNonUnitalContinuousFunctionalCalculus** 是 Mathlib 中的一个实例，位于命
名空间 ``。
形式化陈述：IsSelfAdjoint.instNonUnitalContinuousFunctionalCalculus : NonUnitalContinu
ousFunctionalCalculus Real A IsSelfAdjoint
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Complex.instNontrivial`：Nontrivial ℂ
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `IsTopologicalDivisionRing.toIsTopologicalRing`：∀ {K : Type u_1} {inst : 
DivisionRing K} {inst_1 : TopologicalSpace K} [self : IsTopologicalDivisionRing 
K],   IsTopologicalRing K
· 使用定理 `NormedDivisionRing.to_isTopologicalDivisionRing`：∀ {α : Type u_1} [inst 
: NormedDivisionRing α], IsTopologicalDivisionRing α
· 使用定理 `Complex.instContinuousStar`：ContinuousStar ℂ
· 使用定理 `QuasispectrumRestricts.cfc`：∀ {R : Type u_1} {S : Type u_2} {A : Type u_
3} {p q : A → Prop} [inst : Semifield R] [inst_1 : StarRing R]   [inst_2 : Metri
cSpace R] [inst_…
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `instContinuousStarReal`：ContinuousStar ℝ
· 使用定理 `Complex.instStarModuleReal`：StarModule ℝ ℂ
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `SMulCommClass.complexToReal`：∀ {M : Type u_1} {E : Type u_2} [inst : Add
CommGroup E] [inst_1 : _root_.Module ℂ E] [inst_2 : SMul M E]   [SMulCommClass ℂ
 M E], SMulCommCl…
· 使用定理 `ContinuousSemilinearMapClass.toContinuousMapClass`：∀ {F : Type u_1} {R :
 outParam (Type u_2)} {S : outParam (Type u_3)} {inst : Semiring R} {inst_1 : Se
miring S}   {σ : outParam (R →+* S)} {M…
· 使用定理 `Isometry.isClosedEmbedding`：isClosedEmbedding [CompleteSpace α] [EMetric
Space γ] {f : α -> γ} (hf : Isometry f) : IsClosedEmbedding f
· 使用定理 `Complex.isometry_ofReal`：Isometry Complex.ofReal
· 使用定理 `IsSelfAdjoint.zero`：∀ (R : Type u_1) [inst : AddMonoid R] [inst_1 : Star
AddMonoid R], IsSelfAdjoint 0
· 使用引理 `isSelfAdjoint_iff_isStarNormal_and_quasispectrumRestricts`：isSelfAdjoint
_iff_isStarNormal_and_quasispectrumRestricts {a : A} : IsSelfAdjoint a ↔ IsStarN
ormal a ∧ QuasispectrumRestricts a Complex.reCL…
-/
instance IsSelfAdjoint.instNonUnitalContinuousFunctionalCalculus :
    NonUnitalContinuousFunctionalCalculus ℝ A IsSelfAdjoint :=
  QuasispectrumRestricts.cfc (q := IsStarNormal) (p := IsSelfAdjoint) Complex.reCLM
    Complex.isometry_ofReal.isClosedEmbedding (.zero _)
    (fun _ ↦ isSelfAdjoint_iff_isStarNormal_and_quasispectrumRestricts)

end SelfAdjointNonUnital

section SelfAdjointUnital


variable {A : Type*} [TopologicalSpace A] [Ring A] [StarRing A] [Algebra ℂ A]
  [ContinuousFunctionalCalculus ℂ A IsStarNormal]

/-
**IsSelfAdjoint.spectrumRestricts** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：IsSelfAdjoint.spectrumRestricts {a : A} (ha : IsSelfAdjoint a) : SpectrumR
estricts a Complex.reCLM
参数：ha : IsSelfAdjoint a。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `IsTopologicalDivisionRing.toIsTopologicalRing`：∀ {K : Type u_1} {inst : 
DivisionRing K} {inst_1 : TopologicalSpace K} [self : IsTopologicalDivisionRing 
K],   IsTopologicalRing K
· 使用定理 `NormedDivisionRing.to_isTopologicalDivisionRing`：∀ {α : Type u_1} [inst 
: NormedDivisionRing α], IsTopologicalDivisionRing α
· 使用定理 `Complex.instContinuousStar`：ContinuousStar ℂ
· 使用引理 `IsSelfAdjoint.quasispectrumRestricts`：IsSelfAdjoint.quasispectrumRestric
ts {a : A} (ha : IsSelfAdjoint a) : QuasispectrumRestricts a Complex.reCLM
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
-/
lemma IsSelfAdjoint.spectrumRestricts {a : A} (ha : IsSelfAdjoint a) :
    SpectrumRestricts a Complex.reCLM :=
  ha.quasispectrumRestricts
/-
**IsSelfAdjoint.instContinuousFunctionalCalculus** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：IsSelfAdjoint.instContinuousFunctionalCalculus : ContinuousFunctionalCalcu
lus Real A IsSelfAdjoint
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `IsTopologicalDivisionRing.toIsTopologicalRing`：∀ {K : Type u_1} {inst : 
DivisionRing K} {inst_1 : TopologicalSpace K} [self : IsTopologicalDivisionRing 
K],   IsTopologicalRing K
· 使用定理 `NormedDivisionRing.to_isTopologicalDivisionRing`：∀ {α : Type u_1} [inst 
: NormedDivisionRing α], IsTopologicalDivisionRing α
· 使用定理 `Complex.instContinuousStar`：ContinuousStar ℂ
· 使用定理 `SpectrumRestricts.cfc`：∀ {R : Type u_1} {S : Type u_2} {A : Type u_3} {p
 q : A → Prop} [inst : Semifield R] [inst_1 : StarRing R]   [inst_2 : MetricSpac
e R] [inst_…
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `instContinuousStarReal`：ContinuousStar ℝ
· 使用定理 `Complex.instStarModuleReal`：StarModule ℝ ℂ
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `ContinuousSemilinearMapClass.toContinuousMapClass`：∀ {F : Type u_1} {R :
 outParam (Type u_2)} {S : outParam (Type u_3)} {inst : Semiring R} {inst_1 : Se
miring S}   {σ : outParam (R →+* S)} {M…
· 使用定理 `Isometry.isClosedEmbedding`：isClosedEmbedding [CompleteSpace α] [EMetric
Space γ] {f : α -> γ} (hf : Isometry f) : IsClosedEmbedding f
· 使用定理 `Complex.isometry_ofReal`：Isometry Complex.ofReal
· 使用定理 `IsSelfAdjoint.zero`：∀ (R : Type u_1) [inst : AddMonoid R] [inst_1 : Star
AddMonoid R], IsSelfAdjoint 0
· 使用引理 `isSelfAdjoint_iff_isStarNormal_and_quasispectrumRestricts`：isSelfAdjoint
_iff_isStarNormal_and_quasispectrumRestricts {a : A} : IsSelfAdjoint a ↔ IsStarN
ormal a ∧ QuasispectrumRestricts a Complex.reCL…
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
-/
instance IsSelfAdjoint.instContinuousFunctionalCalculus :
    ContinuousFunctionalCalculus ℝ A IsSelfAdjoint :=
  SpectrumRestricts.cfc (q := IsStarNormal) (p := IsSelfAdjoint) Complex.reCLM
    Complex.isometry_ofReal.isClosedEmbedding (.zero _)
    (fun _ ↦ isSelfAdjoint_iff_isStarNormal_and_quasispectrumRestricts)

@[deprecated "Use `ContinuousFunctionalCalculus.spectrum_nonempty a ha` instead."
    (since := "2026-03-08")]
/-
**IsSelfAdjoint.spectrum_nonempty** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：IsSelfAdjoint.spectrum_nonempty {A : Type*} [Ring A] [StarRing A] [Topolog
icalSpace A] [Algebra Real A] [ContinuousFunctionalCalculus Real A IsSelfAdjoint
] [Nontrivial A] {a : A} (ha : IsSelfAdjoint a) : (σ Real a).Nonempty
参数：ha : IsSelfAdjoint a。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `instContinuousStarReal`：ContinuousStar ℝ
· 使用定理 `ContinuousFunctionalCalculus.spectrum_nonempty`：∀ {R : Type u_1} {A : Ty
pe u_2} {p : outParam (A → Prop)} {inst : CommSemiring R} {inst_1 : StarRing R} 
  {inst_2 : MetricSpace R} {inst_3 :…
-/
lemma IsSelfAdjoint.spectrum_nonempty {A : Type*} [Ring A] [StarRing A]
    [TopologicalSpace A] [Algebra ℝ A] [ContinuousFunctionalCalculus ℝ A IsSelfAdjoint]
    [Nontrivial A] {a : A} (ha : IsSelfAdjoint a) : (σ ℝ a).Nonempty :=
  ContinuousFunctionalCalculus.spectrum_nonempty a ha

end SelfAdjointUnital

/-!
### Continuous functional calculus for nonnegative elements
-/

section Nonneg

/-
**CFC.exists_sqrt_of_isSelfAdjoint_of_quasispectrumRestricts** 是 Mathlib 中的一个引理，
位于命名空间 ``。
形式化陈述：CFC.exists_sqrt_of_isSelfAdjoint_of_quasispectrumRestricts {A : Type*} [No
nUnitalRing A] [StarRing A] [TopologicalSpace A] [Module Real A] [IsScalarTower 
Real A A] [SMulCommClass Real A A] [NonUnitalContinuousFunctionalCalculus Real A
 IsSelfAdjoint] {a : A} (ha₁ : IsSelfAdjoint a) (ha₂ : QuasispectrumRestricts a 
ContinuousMap.realToNNReal) : exists x : A, IsSelfAdjoint x ∧ QuasispectrumRestr
icts x ContinuousMap.realToNNReal ∧ x * x = a
参数：ha₁ : IsSelfAdjoint a；ha₂ : QuasispectrumRestricts a ContinuousMap.realToNNRe
al。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `instContinuousStarReal`：ContinuousStar ℝ
· 使用引理 `cfcₙ_predicate`：cfcₙ_predicate (f : R -> R) (a : A) : p (cfcₙ f a)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `cfcₙ_map_quasispectrum`：cfcₙ_map_quasispectrum : σₙ R (cfcₙ f a) = f '' 
σₙ R a
· 使用定理 `ContinuousOn.sqrt`：ContinuousOn.sqrt (h : ContinuousOn f s) : Continuous
On (fun x => √(f x)) s
· 使用定理 `continuousOn_id'`：continuousOn_id' (s : Set α) : ContinuousOn (fun x : α
 => x) s
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Real.sqrt_zero`：sqrt_zero : √0 = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Real.sqrt_nonneg`：∀ (x : ℝ), 0 ≤ √x
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `cfcₙ_mul`：cfcₙ_mul : cfcₙ (fun x => f x * g x) a = cfcₙ f a * cfcₙ g a
· 使用引理 `cfcₙ_id`：cfcₙ_id : cfcₙ (id : R -> R) a = a
· 使用引理 `cfcₙ_congr`：cfcₙ_congr {f g : R -> R} {a : A} (hfg : (σₙ R a).EqOn f g) 
: cfcₙ f a = cfcₙ g a
· 使用定理 `Real.sq_sqrt`：sq_sqrt (h : 0 <= x) : √x ^ 2 = x
· 使用引理 `QuasispectrumRestricts.nnreal_iff`：nnreal_iff [Module Real A] [IsScalarT
ower Real A A] [SMulCommClass Real A A] {a : A} : QuasispectrumRestricts a Conti
nuousMap.realToNNReal ↔…
-/
lemma CFC.exists_sqrt_of_isSelfAdjoint_of_quasispectrumRestricts {A : Type*} [NonUnitalRing A]
    [StarRing A] [TopologicalSpace A] [Module ℝ A] [IsScalarTower ℝ A A] [SMulCommClass ℝ A A]
    [NonUnitalContinuousFunctionalCalculus ℝ A IsSelfAdjoint]
    {a : A} (ha₁ : IsSelfAdjoint a) (ha₂ : QuasispectrumRestricts a ContinuousMap.realToNNReal) :
    ∃ x : A, IsSelfAdjoint x ∧ QuasispectrumRestricts x ContinuousMap.realToNNReal ∧ x * x = a := by
  use cfcₙ (√·) a, cfcₙ_predicate (√·) a
  constructor
  · simpa only [QuasispectrumRestricts.nnreal_iff, cfcₙ_map_quasispectrum (√·) a,
      Set.mem_image, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂]
        using fun x _ ↦ Real.sqrt_nonneg x
  · rw [← cfcₙ_mul ..]
    nth_rw 2 [← cfcₙ_id ℝ a]
    apply cfcₙ_congr fun x hx ↦ ?_
    rw [QuasispectrumRestricts.nnreal_iff] at ha₂
    apply ha₂ x at hx
    simp [← sq, Real.sq_sqrt hx]

variable {A : Type*} [NonUnitalRing A] [PartialOrder A] [StarRing A] [StarOrderedRing A]
variable [TopologicalSpace A] [Module ℝ A] [IsScalarTower ℝ A A] [SMulCommClass ℝ A A]
variable [NonUnitalContinuousFunctionalCalculus ℝ A IsSelfAdjoint]
variable [NonnegSpectrumClass ℝ A]
/-
**nonneg_iff_isSelfAdjoint_and_quasispectrumRestricts** 是 Mathlib 中的一个引理，位于命名空间 
``。
形式化陈述：nonneg_iff_isSelfAdjoint_and_quasispectrumRestricts {a : A} : 0 <= a ↔ IsS
elfAdjoint a ∧ QuasispectrumRestricts a ContinuousMap.realToNNReal
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `instContinuousStarReal`：ContinuousStar ℝ
· 使用引理 `IsSelfAdjoint.of_nonneg`：IsSelfAdjoint.of_nonneg {x : R} (hx : 0 <= x) :
 IsSelfAdjoint x
· 使用引理 `QuasispectrumRestricts.nnreal_of_nonneg`：nnreal_of_nonneg [Module Real A
] [IsScalarTower Real A A] [SMulCommClass Real A A] [PartialOrder A] [NonnegSpec
trumClass Real A] {a : A} (ha…
· 使用引理 `CFC.exists_sqrt_of_isSelfAdjoint_of_quasispectrumRestricts`：CFC.exists_s
qrt_of_isSelfAdjoint_of_quasispectrumRestricts {A : Type*} [NonUnitalRing A] [St
arRing A] [TopologicalSpace A] [Module Real A] […
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `IsSelfAdjoint.star_eq`：star_eq [Star R] {x : R} (hx : IsSelfAdjoint x) :
 star x = x
· 使用定理 `star_mul_self_nonneg`：star_mul_self_nonneg (r : R) : 0 <= star r * r
-/
lemma nonneg_iff_isSelfAdjoint_and_quasispectrumRestricts {a : A} :
    0 ≤ a ↔ IsSelfAdjoint a ∧ QuasispectrumRestricts a ContinuousMap.realToNNReal := by
  refine ⟨fun ha ↦ ⟨.of_nonneg ha, .nnreal_of_nonneg ha⟩, ?_⟩
  rintro ⟨ha₁, ha₂⟩
  obtain ⟨x, hx, -, rfl⟩ := CFC.exists_sqrt_of_isSelfAdjoint_of_quasispectrumRestricts ha₁ ha₂
  simpa [sq, hx.star_eq] using star_mul_self_nonneg x

open NNReal in
/-
**Nonneg.instNonUnitalContinuousFunctionalCalculus** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：Nonneg.instNonUnitalContinuousFunctionalCalculus : NonUnitalContinuousFunc
tionalCalculus Real>=0 A (0 <= ·)
该定义给出了一等式。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `instContinuousStarReal`：ContinuousStar ℝ
· 使用定理 `QuasispectrumRestricts.cfc`：∀ {R : Type u_1} {S : Type u_2} {A : Type u_
3} {p q : A → Prop} [inst : Semifield R] [inst_1 : StarRing R]   [inst_2 : Metri
cSpace R] [inst_…
· 使用定理 `NNReal.instIsTopologicalSemiring`：IsTopologicalSemiring NNReal
· 使用定理 `NNReal.instContinuousStar`：ContinuousStar NNReal
· 使用定理 `NNReal.instIsScalarTowerOfReal`：∀ {M : Type u_1} {N : Type u_2} [inst : 
MulAction ℝ M] [inst_1 : MulAction ℝ N] [inst_2 : SMul M N]   [IsScalarTower ℝ M
 N], IsScalarTower N…
· 使用定理 `instStarModuleNNRealReal`：StarModule NNReal ℝ
· 使用定理 `NNReal.instContinuousSMulOfReal`：∀ {α : Type u_1} [inst : TopologicalSpa
ce α] [inst_1 : MulAction ℝ α] [ContinuousSMul ℝ α], ContinuousSMul NNReal α
· 使用定理 `IsTopologicalSemiring.toIsModuleTopology`：∀ (R : Type u_1) [inst : Semir
ing R] [τR : TopologicalSpace R] [IsTopologicalSemiring R], IsModuleTopology R R
· 使用定理 `NNReal.isClosedEmbedding_coe`：NNReal.isClosedEmbedding_coe : Topology.Is
ClosedEmbedding NNReal.toReal
· 使用引理 `le_rfl`：le_rfl : a <= a
· 使用引理 `nonneg_iff_isSelfAdjoint_and_quasispectrumRestricts`：nonneg_iff_isSelfAd
joint_and_quasispectrumRestricts {a : A} : 0 <= a ↔ IsSelfAdjoint a ∧ Quasispect
rumRestricts a ContinuousMap.realToNNReal
-/
instance Nonneg.instNonUnitalContinuousFunctionalCalculus :
    NonUnitalContinuousFunctionalCalculus ℝ≥0 A (0 ≤ ·) :=
  QuasispectrumRestricts.cfc (q := IsSelfAdjoint) ContinuousMap.realToNNReal
    NNReal.isClosedEmbedding_coe le_rfl
    (fun _ ↦ nonneg_iff_isSelfAdjoint_and_quasispectrumRestricts)

/-- In a C⋆-algebra, commuting nonnegative elements have nonnegative products. -/
/-
**Commute.mul_nonneg** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Commute.mul_nonneg {a b : A} (ha : 0 <= a) (hb : 0 <= b) (h : Commute a b)
 : 0 <= a * b
参数：ha : 0 <= a；hb : 0 <= b；h : Commute a b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `instContinuousStarReal`：ContinuousStar ℝ
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `nonneg_iff_isSelfAdjoint_and_quasispectrumRestricts`：nonneg_iff_isSelfAd
joint_and_quasispectrumRestricts {a : A} : 0 <= a ↔ IsSelfAdjoint a ∧ Quasispect
rumRestricts a ContinuousMap.realToNNReal
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `IsSelfAdjoint.commute_iff`：commute_iff {R : Type*} [Mul R] [StarMul R] {
x y : R} (hx : IsSelfAdjoint x) (hy : IsSelfAdjoint y) : Commute x y ↔ IsSelfAdj
oint (x * y)
· 使用定理 `LE.le.isSelfAdjoint`：∀ {R : Type u_1} [inst : NonUnitalSemiring R] [inst
_1 : PartialOrder R] [inst_2 : StarRing R] [StarOrderedRing R]   {x : R}, 0 ≤ x 
→ IsSelfA…
· 使用引理 `CFC.exists_sqrt_of_isSelfAdjoint_of_quasispectrumRestricts`：CFC.exists_s
qrt_of_isSelfAdjoint_of_quasispectrumRestricts {A : Type*} [NonUnitalRing A] [St
arRing A] [TopologicalSpace A] [Module Real A] […
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用引理 `quasispectrumRestricts_iff`：quasispectrumRestricts_iff {R S A : Type*} [
CommSemiring R] [CommSemiring S] [NonUnitalRing A] [Module R A] [Module S A] [Al
gebra R S] (a : …
· 使用引理 `quasispectrum.mul_comm`：quasispectrum.mul_comm {R A : Type*} [CommRing R
] [NonUnitalRing A] [Module R A] [IsScalarTower R A A] [SMulCommClass R A A] (a 
b : A) : qua…
· 使用引理 `QuasispectrumRestricts.nnreal_of_nonneg`：nnreal_of_nonneg [Module Real A
] [IsScalarTower Real A A] [SMulCommClass Real A A] [PartialOrder A] [NonnegSpec
trumClass Real A] {a : A} (ha…
· 使用定理 `conjugate_nonneg_of_nonneg`：conjugate_nonneg_of_nonneg {a : R} (ha : 0 <
= a) {c : R} (hc : 0 <= c) : 0 <= c * a * c

--- 原说明 ---
In a C⋆-algebra, commuting nonnegative elements have nonnegative products.
-/
lemma Commute.mul_nonneg {a b : A} (ha : 0 ≤ a) (hb : 0 ≤ b) (h : Commute a b) :
    0 ≤ a * b := by
  rw [nonneg_iff_isSelfAdjoint_and_quasispectrumRestricts]
  refine ⟨ha.isSelfAdjoint.commute_iff hb.isSelfAdjoint |>.mp h, ?_⟩
  rw [nonneg_iff_isSelfAdjoint_and_quasispectrumRestricts] at hb
  obtain ⟨x, hx₁, hx₂, rfl⟩ := CFC.exists_sqrt_of_isSelfAdjoint_of_quasispectrumRestricts hb.1 hb.2
  have hx := nonneg_iff_isSelfAdjoint_and_quasispectrumRestricts.mpr ⟨hx₁, hx₂⟩
  rw [← mul_assoc, quasispectrumRestricts_iff, quasispectrum.mul_comm,
    ← quasispectrumRestricts_iff, ← mul_assoc]
  exact QuasispectrumRestricts.nnreal_of_nonneg <| conjugate_nonneg_of_nonneg ha hx
/-
**commute_iff_mul_nonneg** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：commute_iff_mul_nonneg {a b : A} (ha : 0 <= a) (hb : 0 <= b) : Commute a b
 ↔ 0 <= a * b
参数：ha : 0 <= a；hb : 0 <= b。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `instContinuousStarReal`：ContinuousStar ℝ
· 使用引理 `Commute.mul_nonneg`：Commute.mul_nonneg {a b : A} (ha : 0 <= a) (hb : 0 <
= b) (h : Commute a b) : 0 <= a * b
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `IsSelfAdjoint.commute_iff`：commute_iff {R : Type*} [Mul R] [StarMul R] {
x y : R} (hx : IsSelfAdjoint x) (hy : IsSelfAdjoint y) : Commute x y ↔ IsSelfAdj
oint (x * y)
· 使用定理 `LE.le.isSelfAdjoint`：∀ {R : Type u_1} [inst : NonUnitalSemiring R] [inst
_1 : PartialOrder R] [inst_2 : StarRing R] [StarOrderedRing R]   {x : R}, 0 ≤ x 
→ IsSelfA…
-/
lemma commute_iff_mul_nonneg {a b : A} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    Commute a b ↔ 0 ≤ a * b :=
  ⟨Commute.mul_nonneg ha hb,
  fun h => ha.isSelfAdjoint.commute_iff hb.isSelfAdjoint |>.mpr h.isSelfAdjoint⟩

open NNReal in
@[deprecated "Use `ContinuousFunctionalCalculus.spectrum_nonempty a ha` instead"
  (since := "2026-03-08")]
/-
**NNReal.spectrum_nonempty** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：NNReal.spectrum_nonempty {A : Type*} [Ring A] [StarRing A] [LE A] [Topolog
icalSpace A] [Algebra Real>=0 A] [ContinuousFunctionalCalculus Real>=0 A (0 <= ·
)] [Nontrivial A] {a : A} (ha : 0 <= a) : (spectrum Real>=0 a).Nonempty
参数：0 <= ·；ha : 0 <= a。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `NNReal.instIsTopologicalSemiring`：IsTopologicalSemiring NNReal
· 使用定理 `NNReal.instContinuousStar`：ContinuousStar NNReal
· 使用定理 `ContinuousFunctionalCalculus.spectrum_nonempty`：∀ {R : Type u_1} {A : Ty
pe u_2} {p : outParam (A → Prop)} {inst : CommSemiring R} {inst_1 : StarRing R} 
  {inst_2 : MetricSpace R} {inst_3 :…
-/
lemma NNReal.spectrum_nonempty {A : Type*} [Ring A] [StarRing A] [LE A]
    [TopologicalSpace A] [Algebra ℝ≥0 A] [ContinuousFunctionalCalculus ℝ≥0 A (0 ≤ ·)]
    [Nontrivial A] {a : A} (ha : 0 ≤ a) : (spectrum ℝ≥0 a).Nonempty :=
  ContinuousFunctionalCalculus.spectrum_nonempty a ha

end Nonneg

section Nonneg

variable {A : Type*} [Ring A] [PartialOrder A] [StarRing A] [StarOrderedRing A] [TopologicalSpace A]
variable [Algebra ℝ A] [ContinuousFunctionalCalculus ℝ A IsSelfAdjoint]
variable [NonnegSpectrumClass ℝ A]

open NNReal in
/-
**Nonneg.instContinuousFunctionalCalculus** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：Nonneg.instContinuousFunctionalCalculus : ContinuousFunctionalCalculus Rea
l>=0 A (0 <= ·)
该定义给出了一等式。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `instContinuousStarReal`：ContinuousStar ℝ
· 使用定理 `SpectrumRestricts.cfc`：∀ {R : Type u_1} {S : Type u_2} {A : Type u_3} {p
 q : A → Prop} [inst : Semifield R] [inst_1 : StarRing R]   [inst_2 : MetricSpac
e R] [inst_…
· 使用定理 `NNReal.instIsTopologicalSemiring`：IsTopologicalSemiring NNReal
· 使用定理 `NNReal.instContinuousStar`：ContinuousStar NNReal
· 使用定理 `NNReal.instIsScalarTowerOfReal`：∀ {M : Type u_1} {N : Type u_2} [inst : 
MulAction ℝ M] [inst_1 : MulAction ℝ N] [inst_2 : SMul M N]   [IsScalarTower ℝ M
 N], IsScalarTower N…
· 使用定理 `instStarModuleNNRealReal`：StarModule NNReal ℝ
· 使用定理 `NNReal.instContinuousSMulOfReal`：∀ {α : Type u_1} [inst : TopologicalSpa
ce α] [inst_1 : MulAction ℝ α] [ContinuousSMul ℝ α], ContinuousSMul NNReal α
· 使用定理 `IsTopologicalSemiring.toIsModuleTopology`：∀ (R : Type u_1) [inst : Semir
ing R] [τR : TopologicalSpace R] [IsTopologicalSemiring R], IsModuleTopology R R
· 使用定理 `NNReal.isClosedEmbedding_coe`：NNReal.isClosedEmbedding_coe : Topology.Is
ClosedEmbedding NNReal.toReal
· 使用引理 `le_rfl`：le_rfl : a <= a
· 使用引理 `nonneg_iff_isSelfAdjoint_and_quasispectrumRestricts`：nonneg_iff_isSelfAd
joint_and_quasispectrumRestricts {a : A} : 0 <= a ↔ IsSelfAdjoint a ∧ Quasispect
rumRestricts a ContinuousMap.realToNNReal
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
-/
instance Nonneg.instContinuousFunctionalCalculus :
    ContinuousFunctionalCalculus ℝ≥0 A (0 ≤ ·) :=
  SpectrumRestricts.cfc (q := IsSelfAdjoint) ContinuousMap.realToNNReal
    NNReal.isClosedEmbedding_coe le_rfl
    (fun _ ↦ nonneg_iff_isSelfAdjoint_and_quasispectrumRestricts)
/-
**IsStrictlyPositive.commute_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsStrictlyPositive.commute_iff {a b : A} (ha : IsStrictlyPositive a) (hb :
 IsStrictlyPositive b) : Commute a b ↔ IsStrictlyPositive (a * b)
参数：ha : IsStrictlyPositive a；hb : IsStrictlyPositive b。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `instContinuousStarReal`：ContinuousStar ℝ
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `commute_iff_mul_nonneg`：commute_iff_mul_nonneg {a b : A} (ha : 0 <= a) (
hb : 0 <= b) : Commute a b ↔ 0 <= a * b
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `IsStrictlyPositive.nonneg`：∀ {A : Type u_1} [inst : LE A] [inst_1 : Mono
id A] [inst_2 : Zero A] {a : A}, IsStrictlyPositive a → 0 ≤ a
· 使用定理 `IsUnit.isStrictlyPositive`：∀ {A : Type u_1} [inst : LE A] [inst_1 : Mono
id A] [inst_2 : Zero A] {a : A}, IsUnit a → 0 ≤ a → IsStrictlyPositive a
· 使用定理 `IsUnit.mul`：∀ {M : Type u_1} [inst : Monoid M] {a b : M}, IsUnit a → IsU
nit b → IsUnit (a * b)
· 使用定理 `IsStrictlyPositive.isUnit`：∀ {A : Type u_1} [inst : LE A] [inst_1 : Mono
id A] [inst_2 : Zero A] {a : A}, IsStrictlyPositive a → IsUnit a
-/
theorem IsStrictlyPositive.commute_iff {a b : A} (ha : IsStrictlyPositive a)
    (hb : IsStrictlyPositive b) : Commute a b ↔ IsStrictlyPositive (a * b) := by
  rw [commute_iff_mul_nonneg ha.nonneg hb.nonneg]
  exact ⟨fun h => ha.isUnit.mul hb.isUnit |>.isStrictlyPositive h, fun h => h.nonneg⟩

end Nonneg

/-!
### The restriction of a continuous functional calculus is equal to the original one
-/
section RealEqComplex

variable {A : Type*} [TopologicalSpace A] [Ring A] [StarRing A] [Algebra ℂ A]
  [ContinuousFunctionalCalculus ℂ A IsStarNormal] [T2Space A]

/-
**cfcHom_real_eq_restrict** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：cfcHom_real_eq_restrict {a : A} (ha : IsSelfAdjoint a) : cfcHom ha = ha.sp
ectrumRestricts.starAlgHom (R
参数：ha : IsSelfAdjoint a。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `IsTopologicalDivisionRing.toIsTopologicalRing`：∀ {K : Type u_1} {inst : 
DivisionRing K} {inst_1 : TopologicalSpace K} [self : IsTopologicalDivisionRing 
K],   IsTopologicalRing K
· 使用定理 `NormedDivisionRing.to_isTopologicalDivisionRing`：∀ {α : Type u_1} [inst 
: NormedDivisionRing α], IsTopologicalDivisionRing α
· 使用定理 `Complex.instContinuousStar`：ContinuousStar ℂ
· 使用引理 `SpectrumRestricts.cfcHom_eq_restrict`：cfcHom_eq_restrict (f : C(S, R)) {
a : A} (hpa : p a) (hqa : q a) (h : SpectrumRestricts a f) : cfcHom hpa = h.star
AlgHom (cfcHom hqa)
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `instContinuousStarReal`：ContinuousStar ℝ
· 使用定理 `Complex.instStarModuleReal`：StarModule ℝ ℂ
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `ContinuousSemilinearMapClass.toContinuousMapClass`：∀ {F : Type u_1} {R :
 outParam (Type u_2)} {S : outParam (Type u_3)} {inst : Semiring R} {inst_1 : Se
miring S}   {σ : outParam (R →+* S)} {M…
· 使用定理 `IsSelfAdjoint.isStarNormal`：isStarNormal {R : Type*} [Mul R] [Star R] {x
 : R} (hx : IsSelfAdjoint x) : IsStarNormal x
· 使用引理 `IsSelfAdjoint.spectrumRestricts`：IsSelfAdjoint.spectrumRestricts {a : A}
 (ha : IsSelfAdjoint a) : SpectrumRestricts a Complex.reCLM
-/
lemma cfcHom_real_eq_restrict {a : A} (ha : IsSelfAdjoint a) :
    cfcHom ha =
      ha.spectrumRestricts.starAlgHom (R := ℝ) (S := ℂ)
        (cfcHom ha.isStarNormal) (f := Complex.reCLM) :=
  ha.spectrumRestricts.cfcHom_eq_restrict _ ha ha.isStarNormal
/-
**cfc_real_eq_complex** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：cfc_real_eq_complex {a : A} (f : Real -> Real) (ha : IsSelfAdjoint a
参数：f : Real -> Real。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `IsTopologicalDivisionRing.toIsTopologicalRing`：∀ {K : Type u_1} {inst : 
DivisionRing K} {inst_1 : TopologicalSpace K} [self : IsTopologicalDivisionRing 
K],   IsTopologicalRing K
· 使用定理 `NormedDivisionRing.to_isTopologicalDivisionRing`：∀ {α : Type u_1} [inst 
: NormedDivisionRing α], IsTopologicalDivisionRing α
· 使用定理 `Complex.instContinuousStar`：ContinuousStar ℂ
· 使用引理 `SpectrumRestricts.cfc_eq_restrict`：cfc_eq_restrict (f : C(S, R)) (halg :
 IsClosedEmbedding (algebraMap R S)) {a : A} (hpa : p a) (hqa : q a) (h : Spectr
umRestricts a f) (g : R…
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `instContinuousStarReal`：ContinuousStar ℝ
· 使用定理 `Complex.instStarModuleReal`：StarModule ℝ ℂ
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `ContinuousSemilinearMapClass.toContinuousMapClass`：∀ {F : Type u_1} {R :
 outParam (Type u_2)} {S : outParam (Type u_3)} {inst : Semiring R} {inst_1 : Se
miring S}   {σ : outParam (R →+* S)} {M…
· 使用定理 `Isometry.isClosedEmbedding`：isClosedEmbedding [CompleteSpace α] [EMetric
Space γ] {f : α -> γ} (hf : Isometry f) : IsClosedEmbedding f
· 使用定理 `Complex.isometry_ofReal`：Isometry Complex.ofReal
· 使用定理 `IsSelfAdjoint.isStarNormal`：isStarNormal {R : Type*} [Mul R] [Star R] {x
 : R} (hx : IsSelfAdjoint x) : IsStarNormal x
· 使用引理 `IsSelfAdjoint.spectrumRestricts`：IsSelfAdjoint.spectrumRestricts {a : A}
 (ha : IsSelfAdjoint a) : SpectrumRestricts a Complex.reCLM
-/
lemma cfc_real_eq_complex {a : A} (f : ℝ → ℝ) (ha : IsSelfAdjoint a := by cfc_tac) :
    cfc f a = cfc (fun x ↦ f x.re : ℂ → ℂ) a := by
  exact ha.spectrumRestricts.cfc_eq_restrict (f := Complex.reCLM)
    Complex.isometry_ofReal.isClosedEmbedding ha ha.isStarNormal f
/-
**cfc_complex_eq_real** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：cfc_complex_eq_real {f : Complex -> Complex} (a : A) (hf_real : forall x i
n spectrum Complex a, star (f x) = f x) (ha : IsSelfAdjoint a
参数：a : A；hf_real : forall x in spectrum Complex a, star (f x) = f x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `IsTopologicalDivisionRing.toIsTopologicalRing`：∀ {K : Type u_1} {inst : 
DivisionRing K} {inst_1 : TopologicalSpace K} [self : IsTopologicalDivisionRing 
K],   IsTopologicalRing K
· 使用定理 `NormedDivisionRing.to_isTopologicalDivisionRing`：∀ {α : Type u_1} [inst 
: NormedDivisionRing α], IsTopologicalDivisionRing α
· 使用定理 `Complex.instContinuousStar`：ContinuousStar ℂ
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `instContinuousStarReal`：ContinuousStar ℝ
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `cfc_real_eq_complex`：cfc_real_eq_complex {a : A} (f : Real -> Real) (ha 
: IsSelfAdjoint a
· 使用引理 `cfc_congr`：cfc_congr {f g : R -> R} {a : A} (hfg : (spectrum R a).EqOn f
 g) : cfc f a = cfc g a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `SpectrumRestricts.real_iff`：real_iff [Algebra Complex A] {a : A} : Spect
rumRestricts a Complex.reCLM ↔ forall x in spectrum Complex a, x = x.re
· 使用引理 `IsSelfAdjoint.spectrumRestricts`：IsSelfAdjoint.spectrumRestricts {a : A}
 (ha : IsSelfAdjoint a) : SpectrumRestricts a Complex.reCLM
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
-/
lemma cfc_complex_eq_real {f : ℂ → ℂ} (a : A) (hf_real : ∀ x ∈ spectrum ℂ a, star (f x) = f x)
    (ha : IsSelfAdjoint a := by cfc_tac) :
    cfc f a = cfc (fun x : ℝ ↦ (f x).re) a := by
  rw [cfc_real_eq_complex ..]
  refine cfc_congr fun x hx ↦ ?_
  simp_rw [RCLike.star_def, RCLike.conj_eq_iff_re, RCLike.re_eq_complex_re,
    RCLike.ofReal_eq_complex_ofReal] at hf_real
  rw [← SpectrumRestricts.real_iff.mp ha.spectrumRestricts _ hx, hf_real _ hx]

end RealEqComplex

section RealEqComplexNonUnital

variable {A : Type*} [TopologicalSpace A] [NonUnitalRing A] [StarRing A] [Module ℂ A]
  [IsScalarTower ℂ A A] [SMulCommClass ℂ A A] [T2Space A]
  [NonUnitalContinuousFunctionalCalculus ℂ A IsStarNormal]

/-
**cfc** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：{R : Type u_3} →   {A : Type u_4} →     {p : A → Prop} →       [inst : Com
mSemiring R] →         [inst_1 : StarRing R] →           [inst_2 : MetricSpace R
] →             [inst_3 : IsTopologicalSemiring R] →               [inst_4 : Con
tinuousStar R] →                 [inst_5 : TopologicalSpace A] →                
   [inst_6 : Ring A] →                     [inst_7 : StarRing A] →              
         [inst_8 : Algebra R A] → [instCFC : ContinuousFunctionalCalculus R A p]
 → (R → R) → A → A
参数：R → R。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma cfcₙHom_real_eq_restrict {a : A} (ha : IsSelfAdjoint a) :
    cfcₙHom ha = ha.quasispectrumRestricts.nonUnitalStarAlgHom (cfcₙHom ha.isStarNormal)
      (R := ℝ) (S := ℂ) (f := Complex.reCLM) :=
  ha.quasispectrumRestricts.cfcₙHom_eq_restrict _ ha ha.isStarNormal
/-
**cfc** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：{R : Type u_3} →   {A : Type u_4} →     {p : A → Prop} →       [inst : Com
mSemiring R] →         [inst_1 : StarRing R] →           [inst_2 : MetricSpace R
] →             [inst_3 : IsTopologicalSemiring R] →               [inst_4 : Con
tinuousStar R] →                 [inst_5 : TopologicalSpace A] →                
   [inst_6 : Ring A] →                     [inst_7 : StarRing A] →              
         [inst_8 : Algebra R A] → [instCFC : ContinuousFunctionalCalculus R A p]
 → (R → R) → A → A
参数：R → R。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma cfcₙ_real_eq_complex {a : A} (f : ℝ → ℝ) (ha : IsSelfAdjoint a := by cfc_tac) :
    cfcₙ f a = cfcₙ (fun x ↦ f x.re : ℂ → ℂ) a := by
  exact ha.quasispectrumRestricts.cfcₙ_eq_restrict (f := Complex.reCLM)
    Complex.isometry_ofReal.isClosedEmbedding ha ha.isStarNormal f
/-
**cfc** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：{R : Type u_3} →   {A : Type u_4} →     {p : A → Prop} →       [inst : Com
mSemiring R] →         [inst_1 : StarRing R] →           [inst_2 : MetricSpace R
] →             [inst_3 : IsTopologicalSemiring R] →               [inst_4 : Con
tinuousStar R] →                 [inst_5 : TopologicalSpace A] →                
   [inst_6 : Ring A] →                     [inst_7 : StarRing A] →              
         [inst_8 : Algebra R A] → [instCFC : ContinuousFunctionalCalculus R A p]
 → (R → R) → A → A
参数：R → R。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma cfcₙ_complex_eq_real {f : ℂ → ℂ} (a : A) (hf_real : ∀ x ∈ σₙ ℂ a, star (f x) = f x)
    (ha : IsSelfAdjoint a := by cfc_tac) :
    cfcₙ f a = cfcₙ (fun x : ℝ ↦ (f x).re) a := by
  rw [cfcₙ_real_eq_complex ..]
  refine cfcₙ_congr fun x hx ↦ ?_
  simp_rw [RCLike.star_def, RCLike.conj_eq_iff_re, RCLike.re_eq_complex_re,
    RCLike.ofReal_eq_complex_ofReal] at hf_real
  rw [← QuasispectrumRestricts.real_iff.mp ha.quasispectrumRestricts _ hx, hf_real _ hx]

end RealEqComplexNonUnital

section NNRealEqReal

open NNReal

variable {A : Type*} [TopologicalSpace A] [Ring A] [PartialOrder A] [StarRing A]
  [StarOrderedRing A] [Algebra ℝ A] [IsSemitopologicalRing A] [T2Space A]
  [ContinuousFunctionalCalculus ℝ A IsSelfAdjoint]
  [NonnegSpectrumClass ℝ A]

/-
**cfcHom_nnreal_eq_restrict** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：cfcHom_nnreal_eq_restrict {a : A} (ha : 0 <= a) : cfcHom ha = (SpectrumRes
tricts.nnreal_of_nonneg ha).starAlgHom (cfcHom (IsSelfAdjoint.of_nonneg ha))
参数：ha : 0 <= a。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `instContinuousStarReal`：ContinuousStar ℝ
· 使用引理 `SpectrumRestricts.cfcHom_eq_restrict`：cfcHom_eq_restrict (f : C(S, R)) {
a : A} (hpa : p a) (hqa : q a) (h : SpectrumRestricts a f) : cfcHom hpa = h.star
AlgHom (cfcHom hqa)
· 使用定理 `NNReal.instIsTopologicalSemiring`：IsTopologicalSemiring NNReal
· 使用定理 `NNReal.instContinuousStar`：ContinuousStar NNReal
· 使用定理 `NNReal.instIsScalarTowerOfReal`：∀ {M : Type u_1} {N : Type u_2} [inst : 
MulAction ℝ M] [inst_1 : MulAction ℝ N] [inst_2 : SMul M N]   [IsScalarTower ℝ M
 N], IsScalarTower N…
· 使用定理 `instStarModuleNNRealReal`：StarModule NNReal ℝ
· 使用定理 `NNReal.instContinuousSMulOfReal`：∀ {α : Type u_1} [inst : TopologicalSpa
ce α] [inst_1 : MulAction ℝ α] [ContinuousSMul ℝ α], ContinuousSMul NNReal α
· 使用定理 `IsTopologicalSemiring.toIsModuleTopology`：∀ (R : Type u_1) [inst : Semir
ing R] [τR : TopologicalSpace R] [IsTopologicalSemiring R], IsModuleTopology R R
· 使用引理 `SpectrumRestricts.nnreal_of_nonneg`：nnreal_of_nonneg [PartialOrder A] [N
onnegSpectrumClass Real A] {a : A} (ha : 0 <= a) : SpectrumRestricts a Continuou
sMap.realToNNReal
· 使用引理 `IsSelfAdjoint.of_nonneg`：IsSelfAdjoint.of_nonneg {x : R} (hx : 0 <= x) :
 IsSelfAdjoint x
-/
lemma cfcHom_nnreal_eq_restrict {a : A} (ha : 0 ≤ a) :
    cfcHom ha = (SpectrumRestricts.nnreal_of_nonneg ha).starAlgHom
      (cfcHom (IsSelfAdjoint.of_nonneg ha)) := by
  apply (SpectrumRestricts.nnreal_of_nonneg ha).cfcHom_eq_restrict _
/-
**cfc_nnreal_eq_real** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：cfc_nnreal_eq_real (f : Real>=0 -> Real>=0) (a : A) (ha : 0 <= a
参数：f : Real>=0 -> Real>=0；a : A。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `instContinuousStarReal`：ContinuousStar ℝ
· 使用引理 `SpectrumRestricts.cfc_eq_restrict`：cfc_eq_restrict (f : C(S, R)) (halg :
 IsClosedEmbedding (algebraMap R S)) {a : A} (hpa : p a) (hqa : q a) (h : Spectr
umRestricts a f) (g : R…
· 使用定理 `NNReal.instIsTopologicalSemiring`：IsTopologicalSemiring NNReal
· 使用定理 `NNReal.instContinuousStar`：ContinuousStar NNReal
· 使用定理 `NNReal.instIsScalarTowerOfReal`：∀ {M : Type u_1} {N : Type u_2} [inst : 
MulAction ℝ M] [inst_1 : MulAction ℝ N] [inst_2 : SMul M N]   [IsScalarTower ℝ M
 N], IsScalarTower N…
· 使用定理 `instStarModuleNNRealReal`：StarModule NNReal ℝ
· 使用定理 `NNReal.instContinuousSMulOfReal`：∀ {α : Type u_1} [inst : TopologicalSpa
ce α] [inst_1 : MulAction ℝ α] [ContinuousSMul ℝ α], ContinuousSMul NNReal α
· 使用定理 `IsTopologicalSemiring.toIsModuleTopology`：∀ (R : Type u_1) [inst : Semir
ing R] [τR : TopologicalSpace R] [IsTopologicalSemiring R], IsModuleTopology R R
· 使用定理 `NNReal.isClosedEmbedding_coe`：NNReal.isClosedEmbedding_coe : Topology.Is
ClosedEmbedding NNReal.toReal
· 使用引理 `IsSelfAdjoint.of_nonneg`：IsSelfAdjoint.of_nonneg {x : R} (hx : 0 <= x) :
 IsSelfAdjoint x
· 使用引理 `SpectrumRestricts.nnreal_of_nonneg`：nnreal_of_nonneg [PartialOrder A] [N
onnegSpectrumClass Real A] {a : A} (ha : 0 <= a) : SpectrumRestricts a Continuou
sMap.realToNNReal
-/
lemma cfc_nnreal_eq_real (f : ℝ≥0 → ℝ≥0) (a : A) (ha : 0 ≤ a := by cfc_tac) :
    cfc f a = cfc (fun x ↦ f x.toNNReal : ℝ → ℝ) a := by
  apply (SpectrumRestricts.nnreal_of_nonneg ha).cfc_eq_restrict _
    NNReal.isClosedEmbedding_coe ha (.of_nonneg ha)
/-
**cfc_real_eq_nnreal** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：cfc_real_eq_nnreal {f : Real -> Real} (a : A) (hf_nonneg : forall x in spe
ctrum Real a, 0 <= f x) (ha : 0 <= a
参数：a : A；hf_nonneg : forall x in spectrum Real a, 0 <= f x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `instContinuousStarReal`：ContinuousStar ℝ
· 使用定理 `NNReal.instIsTopologicalSemiring`：IsTopologicalSemiring NNReal
· 使用定理 `NNReal.instContinuousStar`：ContinuousStar NNReal
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `cfc_nnreal_eq_real`：cfc_nnreal_eq_real (f : Real>=0 -> Real>=0) (a : A) 
(ha : 0 <= a
· 使用引理 `cfc_congr`：cfc_congr {f g : R -> R} {a : A} (hfg : (spectrum R a).EqOn f
 g) : cfc f a = cfc g a
· 使用定理 `Real.coe_toNNReal`：∀ (r : ℝ), 0 ≤ r → ↑r.toNNReal = r
· 使用引理 `spectrum_nonneg_of_nonneg`：spectrum_nonneg_of_nonneg {𝕜 A : Type*} [Comm
Semiring 𝕜] [PartialOrder 𝕜] [Ring A] [PartialOrder A] [Algebra 𝕜 A] [NonnegSpec
trumClass 𝕜 A] …
-/
lemma cfc_real_eq_nnreal {f : ℝ → ℝ} (a : A) (hf_nonneg : ∀ x ∈ spectrum ℝ a, 0 ≤ f x)
    (ha : 0 ≤ a := by cfc_tac) : cfc f a = cfc (fun x : ℝ≥0 ↦ (f x).toNNReal) a := by
  rw [cfc_nnreal_eq_real ..]
  refine cfc_congr fun x hx ↦ ?_
  rw [x.coe_toNNReal (spectrum_nonneg_of_nonneg ha hx), (f x).coe_toNNReal (hf_nonneg x hx)]

end NNRealEqReal

section NNRealEqRealNonUnital

open NNReal

variable {A : Type*} [TopologicalSpace A] [NonUnitalRing A] [PartialOrder A] [StarRing A]
  [StarOrderedRing A] [Module ℝ A] [IsSemitopologicalRing A] [IsScalarTower ℝ A A]
  [SMulCommClass ℝ A A] [T2Space A] [NonUnitalContinuousFunctionalCalculus ℝ A IsSelfAdjoint]
  [NonnegSpectrumClass ℝ A]

/-
**cfc** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：{R : Type u_3} →   {A : Type u_4} →     {p : A → Prop} →       [inst : Com
mSemiring R] →         [inst_1 : StarRing R] →           [inst_2 : MetricSpace R
] →             [inst_3 : IsTopologicalSemiring R] →               [inst_4 : Con
tinuousStar R] →                 [inst_5 : TopologicalSpace A] →                
   [inst_6 : Ring A] →                     [inst_7 : StarRing A] →              
         [inst_8 : Algebra R A] → [instCFC : ContinuousFunctionalCalculus R A p]
 → (R → R) → A → A
参数：R → R。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma cfcₙHom_nnreal_eq_restrict {a : A} (ha : 0 ≤ a) :
    cfcₙHom ha = (QuasispectrumRestricts.nnreal_of_nonneg ha).nonUnitalStarAlgHom
      (cfcₙHom (IsSelfAdjoint.of_nonneg ha)) := by
  apply (QuasispectrumRestricts.nnreal_of_nonneg ha).cfcₙHom_eq_restrict _
/-
**cfc** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：{R : Type u_3} →   {A : Type u_4} →     {p : A → Prop} →       [inst : Com
mSemiring R] →         [inst_1 : StarRing R] →           [inst_2 : MetricSpace R
] →             [inst_3 : IsTopologicalSemiring R] →               [inst_4 : Con
tinuousStar R] →                 [inst_5 : TopologicalSpace A] →                
   [inst_6 : Ring A] →                     [inst_7 : StarRing A] →              
         [inst_8 : Algebra R A] → [instCFC : ContinuousFunctionalCalculus R A p]
 → (R → R) → A → A
参数：R → R。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma cfcₙ_nnreal_eq_real (f : ℝ≥0 → ℝ≥0) (a : A) (ha : 0 ≤ a := by cfc_tac) :
    cfcₙ f a = cfcₙ (fun x ↦ f x.toNNReal : ℝ → ℝ) a := by
  apply (QuasispectrumRestricts.nnreal_of_nonneg ha).cfcₙ_eq_restrict _
    NNReal.isClosedEmbedding_coe ha (.of_nonneg ha)
/-
**cfc** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：{R : Type u_3} →   {A : Type u_4} →     {p : A → Prop} →       [inst : Com
mSemiring R] →         [inst_1 : StarRing R] →           [inst_2 : MetricSpace R
] →             [inst_3 : IsTopologicalSemiring R] →               [inst_4 : Con
tinuousStar R] →                 [inst_5 : TopologicalSpace A] →                
   [inst_6 : Ring A] →                     [inst_7 : StarRing A] →              
         [inst_8 : Algebra R A] → [instCFC : ContinuousFunctionalCalculus R A p]
 → (R → R) → A → A
参数：R → R。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma cfcₙ_real_eq_nnreal {f : ℝ → ℝ} (a : A) (hf_nonneg : ∀ x ∈ σₙ ℝ a, 0 ≤ f x)
    (ha : 0 ≤ a := by cfc_tac) : cfcₙ f a = cfcₙ (fun x : ℝ≥0 ↦ (f x).toNNReal) a := by
  rw [cfcₙ_nnreal_eq_real ..]
  refine cfcₙ_congr fun x hx ↦ ?_
  rw [x.coe_toNNReal (quasispectrum_nonneg_of_nonneg _ ha _ hx),
    (f x).coe_toNNReal (hf_nonneg x hx)]

end NNRealEqRealNonUnital

end

