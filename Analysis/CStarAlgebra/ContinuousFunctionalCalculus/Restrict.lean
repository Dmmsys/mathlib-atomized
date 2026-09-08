/-
Copyright (c) 2024 Jireh Loreaux. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jireh Loreaux
-/
module

public import Mathlib.Topology.Algebra.Algebra
public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.NonUnital

/-! # Restriction of the continuous functional calculus to a scalar subring

The main declaration in this file is:

+ `SpectrumRestricts.cfc`: builds a continuous functional calculus over a subring of scalars.
  This is used for automatically deriving the continuous functional calculi on selfadjoint or
  positive elements from the one for normal elements.

This will allow us to take an instance of the
`ContinuousFunctionalCalculus ℂ A IsStarNormal` and produce both of the instances
`ContinuousFunctionalCalculus ℝ A IsSelfAdjoint` and `ContinuousFunctionalCalculus ℝ≥0 A (0 ≤ ·)`
simply by proving:

1. `IsSelfAdjoint x ↔ IsStarNormal x ∧ SpectrumRestricts Complex.re x`,
2. `0 ≤ x ↔ IsSelfAdjoint x ∧ SpectrumRestricts Real.toNNReal x`.
-/

@[expose] public section

open Set Topology

namespace SpectrumRestricts

/-- The homeomorphism `spectrum S a ≃ₜ spectrum R a` induced by `SpectrumRestricts a f`. -/
/-
**SpectrumRestricts.homeomorph** 是 Mathlib 中的一个定义，位于命名空间 `SpectrumRestricts`。
形式化陈述：homeomorph {R S A : Type*} [Semifield R] [Semifield S] [Ring A] [Algebra R
 S] [Algebra R A] [Algebra S A] [IsScalarTower R S A] [TopologicalSpace R] [Topo
logicalSpace S] [ContinuousSMul R S] {a : A} {f : C(S, R)} (h : SpectrumRestrict
s a f) : spectrum S a ≃ₜ spectrum R a where toFun
参数：S, R；h : SpectrumRestricts a f。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The homeomorphism `spectrum S a ≃ₜ spectrum R a` induced by `SpectrumRestricts a
 f`.
-/
def homeomorph {R S A : Type*} [Semifield R] [Semifield S] [Ring A]
    [Algebra R S] [Algebra R A] [Algebra S A] [IsScalarTower R S A] [TopologicalSpace R]
    [TopologicalSpace S] [ContinuousSMul R S] {a : A} {f : C(S, R)} (h : SpectrumRestricts a f) :
    spectrum S a ≃ₜ spectrum R a where
  toFun := MapsTo.restrict f _ _ h.subset_preimage
  invFun := MapsTo.restrict (algebraMap R S) _ _ (image_subset_iff.mp h.algebraMap_image.subset)
  left_inv x := Subtype.ext <| h.rightInvOn x.2
  right_inv x := Subtype.ext <| h.left_inv x
/-
**SpectrumRestricts.compactSpace** 是 Mathlib 中的一个引理，位于命名空间 `SpectrumRestricts`。
形式化陈述：compactSpace {R S A : Type*} [Semifield R] [Semifield S] [Ring A] [Algebra
 R S] [Algebra R A] [Algebra S A] [IsScalarTower R S A] [TopologicalSpace R] [To
pologicalSpace S] {a : A} (f : C(S, R)) (h : SpectrumRestricts a f) [h_cpct : Co
mpactSpace (spectrum S a)] : CompactSpace (spectrum R a)
参数：f : C(S, R)；h : SpectrumRestricts a f；spectrum S a。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `isCompact_iff_compactSpace`：isCompact_iff_compactSpace : IsCompact s ↔ C
ompactSpace s
· 使用定理 `IsCompact.image`：IsCompact.image {f : X -> Y} (hs : IsCompact s) (hf : C
ontinuous f) : IsCompact (f '' s)
· 使用定理 `ContinuousMapClass.map_continuous`：∀ {F : Type u_1} {X : outParam (Type 
u_2)} {Y : outParam (Type u_3)} {inst : TopologicalSpace X}   {inst_1 : Topologi
calSpace Y} {inst_2 : F…
· 使用定理 `SpectrumRestricts.image`：image (h : SpectrumRestricts a f) : f '' spectr
um S a = spectrum R a
-/
lemma compactSpace {R S A : Type*} [Semifield R] [Semifield S] [Ring A]
    [Algebra R S] [Algebra R A] [Algebra S A] [IsScalarTower R S A] [TopologicalSpace R]
    [TopologicalSpace S] {a : A} (f : C(S, R)) (h : SpectrumRestricts a f)
    [h_cpct : CompactSpace (spectrum S a)] : CompactSpace (spectrum R a) := by
  rw [← isCompact_iff_compactSpace] at h_cpct ⊢
  exact h.image ▸ h_cpct.image (map_continuous f)

universe u v w

set_option backward.isDefEq.respectTransparency.types false in
/-- If the spectrum of an element restricts to a smaller scalar ring, then a continuous functional
calculus over the larger scalar ring descends to the smaller one. -/
@[simps!]
/-
**SpectrumRestricts.starAlgHom** 是 Mathlib 中的一个定义，位于命名空间 `SpectrumRestricts`。
形式化陈述：starAlgHom {R : Type u} {S : Type v} {A : Type w} [Semifield R] [StarRing 
R] [TopologicalSpace R] [IsTopologicalSemiring R] [ContinuousStar R] [Semifield 
S] [StarRing S] [TopologicalSpace S] [IsTopologicalSemiring S] [ContinuousStar S
] [Ring A] [StarRing A] [Algebra R S] [Algebra R A] [Algebra S A] [IsScalarTower
 R S A] [StarModule R S] [ContinuousSMul R S] {a : A} (φ : C(spectrum S a, S) ->
⋆ₐ[S] A) {f : C(S, R)} (h : SpectrumRestricts a f) : C(spectrum R a, R) ->⋆ₐ[R] 
A
参数：φ : C(spectrum S a, S) ->⋆ₐ[S] A；S, R；h : SpectrumRestricts a f。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If the spectrum of an element restricts to a smaller scalar ring, then a continu
ous functional
calculus over the larger scalar ring descends to the smaller one.
-/
def starAlgHom {R : Type u} {S : Type v} {A : Type w} [Semifield R]
    [StarRing R] [TopologicalSpace R] [IsTopologicalSemiring R] [ContinuousStar R] [Semifield S]
    [StarRing S] [TopologicalSpace S] [IsTopologicalSemiring S] [ContinuousStar S] [Ring A]
    [StarRing A] [Algebra R S] [Algebra R A] [Algebra S A]
    [IsScalarTower R S A] [StarModule R S] [ContinuousSMul R S] {a : A}
    (φ : C(spectrum S a, S) →⋆ₐ[S] A) {f : C(S, R)} (h : SpectrumRestricts a f) :
    C(spectrum R a, R) →⋆ₐ[R] A :=
  (φ.restrictScalars R).comp <|
    (ContinuousMap.compStarAlgHom (spectrum S a) (.ofId R S) (algebraMapCLM R S).continuous).comp <|
      ContinuousMap.compStarAlgHom' R R
        ⟨Subtype.map f h.subset_preimage, (map_continuous f).subtype_map
          fun x (hx : x ∈ spectrum S a) => h.subset_preimage hx⟩

variable {R S A : Type*} {p q : A → Prop}
variable [Semifield R] [StarRing R] [MetricSpace R] [IsTopologicalSemiring R] [ContinuousStar R]
variable [Semifield S] [StarRing S] [MetricSpace S] [IsTopologicalSemiring S] [ContinuousStar S]
variable [Ring A] [StarRing A] [Algebra S A]
variable [Algebra R S] [Algebra R A] [IsScalarTower R S A] [StarModule R S] [ContinuousSMul R S]
/-
**SpectrumRestricts.starAlgHom_id** 是 Mathlib 中的一个引理，位于命名空间 `SpectrumRestricts`。
形式化陈述：starAlgHom_id {a : A} {φ : C(spectrum S a, S) ->⋆ₐ[S] A} {f : C(S, R)} (h 
: SpectrumRestricts a f) (h_id : φ (.restrict (spectrum S a) <| .id S) = a) : h.
starAlgHom φ (.restrict (spectrum R a) <| .id R) = a
参数：spectrum S a, S；S, R；h : SpectrumRestricts a f；h_id : φ (.restrict (spectrum 
S a) <| .id S) = a。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `SpectrumRestricts.starAlgHom_apply`：∀ {R : Type u} {S : Type v} {A : Typ
e w} [inst : Semifield R] [inst_1 : StarRing R] [inst_2 : TopologicalSpace R]   
[inst_3 : IsTopologicalS…
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `ContinuousMap.ext`：ext {f g : C(X, Y)} (h : forall a, f a = g a) : f = g
· 使用定理 `SpectrumRestricts.rightInvOn`：rightInvOn (h : SpectrumRestricts a f) : (
spectrum S a).RightInvOn f (algebraMap R S)
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
-/
lemma starAlgHom_id {a : A} {φ : C(spectrum S a, S) →⋆ₐ[S] A} {f : C(S, R)}
    (h : SpectrumRestricts a f) (h_id : φ (.restrict (spectrum S a) <| .id S) = a) :
    h.starAlgHom φ (.restrict (spectrum R a) <| .id R) = a := by
  simp only [SpectrumRestricts.starAlgHom_apply]
  convert! h_id
  ext x
  exact h.rightInvOn x.2

open ContinuousMap in
/-
**SpectrumRestricts.starAlgHom_injective** 是 Mathlib 中的一个引理，位于命名空间 `SpectrumRest
ricts`。
形式化陈述：starAlgHom_injective {a : A} {φ : C(spectrum S a, S) ->⋆ₐ[S] A} (hφ : Func
tion.Injective φ) {f : C(S, R)} (h : SpectrumRestricts a f) (halg : Function.Inj
ective (algebraMap R S)) : Function.Injective (h.starAlgHom φ)
参数：spectrum S a, S；hφ : Function.Injective φ；S, R；h : SpectrumRestricts a f；halg
 : Function.Injective (algebraMap R S)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Injective.comp`：∀ {α : Sort u_1} {β : Sort u_2} {γ : Sort u_3} 
{g : β → γ} {f : α → β},   Function.Injective g → Function.Injective f → Functio
n.Injective (…
· 使用定理 `ContinuousMap.postcomp_injective`：postcomp_injective (g : C(Y, Z)) (hg :
 Function.Injective g) : Function.Injective (ContinuousMap.comp g : C(X, Y) -> C
(X, Z))
· 使用定理 `Homeomorph.injective`：∀ {X : Type u_1} {Y : Type u_2} [inst : Topologica
lSpace X] [inst_1 : TopologicalSpace Y] (h : X ≃ₜ Y),   Function.Injective ⇑h
-/
lemma starAlgHom_injective {a : A} {φ : C(spectrum S a, S) →⋆ₐ[S] A}
    (hφ : Function.Injective φ) {f : C(S, R)} (h : SpectrumRestricts a f)
    (halg : Function.Injective (algebraMap R S)) :
    Function.Injective (h.starAlgHom φ) :=
  hφ.comp <| (postcomp_injective _ halg).comp <|
    h.homeomorph.symm.arrowCongr (.refl _) |>.injective

variable [TopologicalSpace A]

section Generic

variable [ContinuousFunctionalCalculus S A q]

open ContinuousMap in
/-
**SpectrumRestricts.continuous_starAlgHom** 是 Mathlib 中的一个引理，位于命名空间 `SpectrumRes
tricts`。
形式化陈述：continuous_starAlgHom {a : A} {φ : C(spectrum S a, S) ->⋆ₐ[S] A} (hφ : Con
tinuous φ) {f : C(S, R)} (h : SpectrumRestricts a f) : Continuous (h.starAlgHom 
φ)
参数：spectrum S a, S；hφ : Continuous φ；S, R；h : SpectrumRestricts a f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Continuous.comp`：Continuous.comp {g : Y -> Z} (hg : Continuous g) (hf : 
Continuous f) : Continuous (g ∘ f)
· 使用定理 `ContinuousMap.continuous_postcomp`：continuous_postcomp (g : C(Y, Z)) : C
ontinuous (ContinuousMap.comp g : C(X, Y) -> C(X, Z))
· 使用定理 `ContinuousMap.continuous_precomp`：continuous_precomp (f : C(X, Y)) : Con
tinuous (fun g => g.comp f : C(Y, Z) -> C(X, Z))
-/
lemma continuous_starAlgHom {a : A} {φ : C(spectrum S a, S) →⋆ₐ[S] A}
    (hφ : Continuous φ) {f : C(S, R)} (h : SpectrumRestricts a f) :
    Continuous (h.starAlgHom φ) :=
  hφ.comp <| (continuous_postcomp _).comp (continuous_precomp _)

variable [CompleteSpace R] in
/-
**SpectrumRestricts.isClosedEmbedding_starAlgHom** 是 Mathlib 中的一个引理，位于命名空间 `Spec
trumRestricts`。
形式化陈述：isClosedEmbedding_starAlgHom {a : A} {φ : C(spectrum S a, S) ->⋆ₐ[S] A} (h
φ : IsClosedEmbedding φ) {f : C(S, R)} (h : SpectrumRestricts a f) (halg : IsUni
formEmbedding (algebraMap R S)) : IsClosedEmbedding (h.starAlgHom φ)
参数：spectrum S a, S；hφ : IsClosedEmbedding φ；S, R；h : SpectrumRestricts a f；halg 
: IsUniformEmbedding (algebraMap R S)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Topology.IsClosedEmbedding.comp`：∀ {X : Type u_1} {Y : Type u_2} {Z : Ty
pe u_3} {f : X → Y} {g : Y → Z} [inst : TopologicalSpace X]   [inst_1 : Topologi
calSpace Y] [inst_2 :…
· 使用定理 `IsUniformEmbedding.isClosedEmbedding`：IsUniformEmbedding.isClosedEmbeddi
ng [UniformSpace α] [UniformSpace β] [CompleteSpace α] [T0Space β] {f : α -> β} 
(hf : IsUniformEmbedding f…
· 使用定理 `FrechetUrysohnSpace.to_sequentialSpace`：∀ {X : Type u_1} [inst : Topolog
icalSpace X] [FrechetUrysohnSpace X], SequentialSpace X
· 使用定理 `FirstCountableTopology.frechetUrysohnSpace`：∀ {X : Type u_1} [inst : Top
ologicalSpace X] [FirstCountableTopology X], FrechetUrysohnSpace X
· 使用定理 `TopologicalSpace.PseudoMetrizableSpace.firstCountableTopology`：∀ {X : Ty
pe u_2} [inst : TopologicalSpace X] [h : TopologicalSpace.PseudoMetrizableSpace 
X], FirstCountableTopology X
· 使用定理 `PseudoEMetricSpace.pseudoMetrizableSpace`：∀ {α : Type u_2} [inst : Pseud
oEMetricSpace α], TopologicalSpace.PseudoMetrizableSpace α
· 使用定理 `ContinuousMap.instT0Space`：∀ {X : Type u_2} {Y : Type u_3} [inst : Topol
ogicalSpace X] [inst_1 : TopologicalSpace Y] [T0Space Y], T0Space C(X, Y)
· 使用定理 `T3Space.toT0Space`：∀ {X : Type u} {inst : TopologicalSpace X} [self : T3
Space X], T0Space X
· 使用定理 `T4Space.t3Space`：∀ {X : Type u_1} [inst : TopologicalSpace X] [T4Space X
], T3Space X
· 使用定理 `instT4SpaceOfT1SpaceOfNormalSpace`：∀ {X : Type u_1} [inst : TopologicalS
pace X] [T1Space X] [NormalSpace X], T4Space X
· 使用定理 `T2Space.t1Space`：∀ {X : Type u_1} [inst : TopologicalSpace X] [T2Space X
], T1Space X
· 使用定理 `TopologicalSpace.t2Space_of_metrizableSpace`：∀ {X : Type u_2} [inst : To
pologicalSpace X] [TopologicalSpace.MetrizableSpace X], T2Space X
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α
· 使用定理 `CompletelyNormalSpace.toNormalSpace`：∀ {X : Type u_1} [inst : Topologica
lSpace X] [CompletelyNormalSpace X], NormalSpace X
· 使用定理 `UniformSpace.completelyNormalSpace_of_isCountablyGenerated_uniformity`：∀
 {α : Type u} [inst : UniformSpace α] [(uniformity α).IsCountablyGenerated], Com
pletelyNormalSpace α
· 使用定理 `EMetric.instIsCountablyGeneratedUniformity`：∀ {α : Type u} [inst : Pseud
oEMetricSpace α], (uniformity α).IsCountablyGenerated
· 使用定理 `IsUniformEmbedding.comp`：IsUniformEmbedding.comp {g : β -> γ} (hg : IsUn
iformEmbedding g) {f : α -> β} (hf : IsUniformEmbedding f) : IsUniformEmbedding 
(g ∘ f) where…
· 使用定理 `ContinuousMap.isUniformEmbedding_comp`：isUniformEmbedding_comp (g : C(β,
 δ)) (hg : IsUniformEmbedding g) : IsUniformEmbedding (ContinuousMap.comp g : C(
α, β) -> C(α, δ))
· 使用引理 `UniformEquiv.isUniformEmbedding`：isUniformEmbedding (h : α ≃ᵤ β) : IsUni
formEmbedding h
-/
lemma isClosedEmbedding_starAlgHom {a : A} {φ : C(spectrum S a, S) →⋆ₐ[S] A}
    (hφ : IsClosedEmbedding φ) {f : C(S, R)} (h : SpectrumRestricts a f)
    (halg : IsUniformEmbedding (algebraMap R S)) :
    IsClosedEmbedding (h.starAlgHom φ) :=
  hφ.comp <| IsUniformEmbedding.isClosedEmbedding <| .comp
    (ContinuousMap.isUniformEmbedding_comp _ halg)
    (UniformEquiv.arrowCongr h.homeomorph.symm (.refl _) |>.isUniformEmbedding)

set_option backward.isDefEq.respectTransparency.types false in
/-- Given a `ContinuousFunctionalCalculus S A q`. If we form the predicate `p` for `a : A`
characterized by: `q a` and the spectrum of `a` restricts to the scalar subring `R` via
`f : C(S, R)`, then we can get a restricted functional calculus
`ContinuousFunctionalCalculus R A p`. -/
/-
**SpectrumRestricts.cfc** 是 Mathlib 中的一个定理，位于命名空间 `SpectrumRestricts`。
形式化陈述：∀ {R : Type u_1} {S : Type u_2} {A : Type u_3} {p q : A → Prop} [inst : Se
mifield R] [inst_1 : StarRing R]   [inst_2 : MetricSpace R] [inst_3 : IsTopologi
calSemiring R] [inst_4 : ContinuousStar R] [inst_5 : Semifield S]   [inst_6 : St
arRing S] [inst_7 : MetricSpace S] [inst_8 : IsTopologicalSemiring S] [inst_9 : 
ContinuousStar S]   [inst_10 : Ring A] [inst_11 : StarRing A] [inst_12 : Algebra
 S A] [inst_13 : Algebra R S] [inst_14 : Algebra R A]   [IsScalarTower R S A] [S
tarModule R S] [ContinuousSMul R S] [inst_18 : TopologicalSpace A]   [Continuous
FunctionalCalculus S A q] (f : C(S, R)),   Topology.IsClosedEmbedding ⇑(algebraM
ap R S) →     p 0 → (∀ (a : A), p a ↔ q a ∧ SpectrumRestricts a ⇑f) → Continuous
FunctionalCalculus R A p
参数：f : C(S, R)；algebraMap R S；∀ (a : A), p a ↔ q a ∧ SpectrumRestricts a ⇑f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousFunctionalCalculus.compactSpace_spectrum`：∀ {R : Type u_1} {A 
: Type u_2} {p : outParam (A → Prop)} {inst : CommSemiring R} {inst_1 : StarRing
 R}   {inst_2 : MetricSpace R} {inst_3 :…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `isCompact_iff_compactSpace`：isCompact_iff_compactSpace : IsCompact s ↔ C
ompactSpace s
· 使用定理 `spectrum.preimage_algebraMap`：preimage_algebraMap (S : Type*) {R A : Typ
e*} [CommSemiring R] [CommSemiring S] [Ring A] [Algebra R S] [Algebra R A] [Alge
bra S A] [IsScalar…
· 使用定理 `Topology.IsClosedEmbedding.isCompact_preimage`：Topology.IsClosedEmbeddin
g.isCompact_preimage (hf : IsClosedEmbedding f) {K : Set Y} (hK : IsCompact K) :
 IsCompact (f ⁻¹' K)
· 使用定理 `Set.Nonempty.image`：∀ {α : Type u_1} {β : Type u_2} (f : α → β) {s : Set
 α}, s.Nonempty → (f '' s).Nonempty
· 使用定理 `ContinuousFunctionalCalculus.spectrum_nonempty`：∀ {R : Type u_1} {A : Ty
pe u_2} {p : outParam (A → Prop)} {inst : CommSemiring R} {inst_1 : StarRing R} 
  {inst_2 : MetricSpace R} {inst_3 :…
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `SpectrumRestricts.image`：image (h : SpectrumRestricts a f) : f '' spectr
um S a = spectrum R a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用引理 `SpectrumRestricts.continuous_starAlgHom`：continuous_starAlgHom {a : A} {
φ : C(spectrum S a, S) ->⋆ₐ[S] A} (hφ : Continuous φ) {f : C(S, R)} (h : Spectru
mRestricts a f) : Continuous …
· 使用引理 `cfcHom_continuous`：cfcHom_continuous : Continuous (cfcHom ha : C(spectru
m R a, R) ->⋆ₐ[R] A)
· 使用引理 `SpectrumRestricts.starAlgHom_injective`：starAlgHom_injective {a : A} {φ 
: C(spectrum S a, S) ->⋆ₐ[S] A} (hφ : Function.Injective φ) {f : C(S, R)} (h : S
pectrumRestricts a f) (halg …
· 使用引理 `cfcHom_injective`：cfcHom_injective : Function.Injective (cfcHom ha : C(s
pectrum R a, R) ->⋆ₐ[R] A)
· 使用定理 `Topology.IsEmbedding.injective`：∀ {X : Type u_1} {Y : Type u_2} [tX : To
pologicalSpace X] [tY : TopologicalSpace Y] {f : X → Y},   Topology.IsEmbedding 
f → Function.Injecti…
· 使用定理 `Topology.IsClosedEmbedding.toIsEmbedding`：∀ {X : Type u_1} {Y : Type u_2
} [tX : TopologicalSpace X] [tY : TopologicalSpace Y] {f : X → Y},   Topology.Is
ClosedEmbedding f → Topology.I…
· 使用引理 `SpectrumRestricts.starAlgHom_id`：starAlgHom_id {a : A} {φ : C(spectrum S
 a, S) ->⋆ₐ[S] A} {f : C(S, R)} (h : SpectrumRestricts a f) (h_id : φ (.restrict
 (spectrum S a) <| .i…
· 使用引理 `cfcHom_id`：cfcHom_id : cfcHom ha ((ContinuousMap.id R).restrict <| spect
rum R a) = a
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `SpectrumRestricts.starAlgHom_apply`：∀ {R : Type u} {S : Type v} {A : Typ
e w} [inst : Semifield R] [inst_1 : StarRing R] [inst_2 : TopologicalSpace R]   
[inst_3 : IsTopologicalS…
· 使用引理 `cfcHom_map_spectrum`：cfcHom_map_spectrum (f : C(spectrum R a, R)) : spec
trum R (cfcHom ha f) = Set.range f
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `StarAlgHom.ofId_apply`：∀ (R : Type u_7) (A : Type u_8) [inst : CommSemir
ing R] [inst_1 : StarRing R] [inst_2 : Semiring A] [inst_3 : StarMul A]   [inst_
4 : Algebra…
· 使用定理 `Function.Injective.eq_iff`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β}, 
Function.Injective f → ∀ {a b : α}, f a = f b ↔ a = b
· 使用定理 `Equiv.exists_congr`：∀ {α : Sort u} {β : Sort v} {p : α → Prop} {q : β → 
Prop} (e : α ≃ β),   (∀ (a : α), p a ↔ q (e a)) → ((∃ a, p a) ↔ ∃ b, q b)
（共 36 条，此处仅展示前 30 条）

--- 原说明 ---
Given a `ContinuousFunctionalCalculus S A q`. If we form the predicate `p` for `
a : A`
characterized by: `q a` and the spectrum of `a` restricts to the scalar subring 
`R` via
`f : C(S, R)`, then we can get a restricted functional calculus
`ContinuousFunctionalCalculus R A p`.
-/
protected theorem cfc (f : C(S, R)) (halg : IsClosedEmbedding (algebraMap R S)) (h0 : p 0)
    (h : ∀ a, p a ↔ q a ∧ SpectrumRestricts a f) :
    ContinuousFunctionalCalculus R A p where
  predicate_zero := h0
  spectrum_nonempty a ha := ((h a).mp ha).2.image ▸
    (ContinuousFunctionalCalculus.spectrum_nonempty a ((h a).mp ha).1 |>.image f)
  compactSpace_spectrum a := by
    have := ContinuousFunctionalCalculus.compactSpace_spectrum (R := S) a
    rw [← isCompact_iff_compactSpace] at this ⊢
    simpa using halg.isCompact_preimage this
  exists_cfc_of_predicate a ha := by
    refine ⟨((h a).mp ha).2.starAlgHom (cfcHom ((h a).mp ha).1 (R := S)),
      ?hom_continuous, ?hom_injective, ?hom_id, ?hom_map_spectrum, ?predicate_hom⟩
    case hom_continuous =>
      exact ((h a).mp ha).2.continuous_starAlgHom (cfcHom_continuous ((h a).mp ha).1)
    case hom_injective =>
      exact ((h a).mp ha).2.starAlgHom_injective (cfcHom_injective ((h a).mp ha).1) halg.injective
    case hom_id => exact ((h a).mp ha).2.starAlgHom_id <| cfcHom_id ((h a).mp ha).1
    case hom_map_spectrum =>
      simp only [SpectrumRestricts.starAlgHom_apply, ← @spectrum.preimage_algebraMap (R := R) S,
        cfcHom_map_spectrum, Set.ext_iff, Set.mem_preimage, Set.mem_range, ContinuousMap.comp_apply,
        ContinuousMap.coe_mk, StarAlgHom.ofId_apply, halg.injective.eq_iff]
      exact fun _ _ ↦ ((h a).mp ha).2.homeomorph.exists_congr fun _ ↦ Iff.rfl
    case predicate_hom =>
      intro g
      rw [h]
      refine ⟨cfcHom_predicate _ _, ?_⟩
      refine .of_rightInvOn (((h a).mp ha).2.left_inv) fun s hs ↦ ?_
      rw [SpectrumRestricts.starAlgHom_apply, cfcHom_map_spectrum] at hs
      obtain ⟨r, rfl⟩ := hs
      simp [((h a).mp ha).2.left_inv _]

variable [ContinuousFunctionalCalculus R A p] [ContinuousMap.UniqueHom R A]
/-
**SpectrumRestricts.cfcHom_eq_restrict** 是 Mathlib 中的一个引理，位于命名空间 `SpectrumRestri
cts`。
形式化陈述：cfcHom_eq_restrict (f : C(S, R)) {a : A} (hpa : p a) (hqa : q a) (h : Spec
trumRestricts a f) : cfcHom hpa = h.starAlgHom (cfcHom hqa)
参数：f : C(S, R)；hpa : p a；hqa : q a；h : SpectrumRestricts a f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `cfcHom_eq_of_continuous_of_map_id`：cfcHom_eq_of_continuous_of_map_id [Un
iqueHom R A] (φ : C(spectrum R a, R) ->⋆ₐ[R] A) (hφ₁ : Continuous φ) (hφ₂ : φ (.
restrict (spectrum R a)…
· 使用引理 `SpectrumRestricts.continuous_starAlgHom`：continuous_starAlgHom {a : A} {
φ : C(spectrum S a, S) ->⋆ₐ[S] A} (hφ : Continuous φ) {f : C(S, R)} (h : Spectru
mRestricts a f) : Continuous …
· 使用引理 `cfcHom_continuous`：cfcHom_continuous : Continuous (cfcHom ha : C(spectru
m R a, R) ->⋆ₐ[R] A)
· 使用引理 `SpectrumRestricts.starAlgHom_id`：starAlgHom_id {a : A} {φ : C(spectrum S
 a, S) ->⋆ₐ[S] A} {f : C(S, R)} (h : SpectrumRestricts a f) (h_id : φ (.restrict
 (spectrum S a) <| .i…
· 使用引理 `cfcHom_id`：cfcHom_id : cfcHom ha ((ContinuousMap.id R).restrict <| spect
rum R a) = a
-/
lemma cfcHom_eq_restrict (f : C(S, R)) {a : A} (hpa : p a) (hqa : q a) (h : SpectrumRestricts a f) :
    cfcHom hpa = h.starAlgHom (cfcHom hqa) := by
  apply cfcHom_eq_of_continuous_of_map_id
  · exact h.continuous_starAlgHom (cfcHom_continuous hqa)
  · exact h.starAlgHom_id (cfcHom_id hqa)

set_option backward.isDefEq.respectTransparency.types false in
/-
**SpectrumRestricts.cfc_eq_restrict** 是 Mathlib 中的一个引理，位于命名空间 `SpectrumRestricts
`。
形式化陈述：cfc_eq_restrict (f : C(S, R)) (halg : IsClosedEmbedding (algebraMap R S)) 
{a : A} (hpa : p a) (hqa : q a) (h : SpectrumRestricts a f) (g : R -> R) : cfc g
 a = cfc (fun x => algebraMap R S (g (f x))) a
参数：f : C(S, R)；halg : IsClosedEmbedding (algebraMap R S)；hpa : p a；hqa : q a；h :
 SpectrumRestricts a f；g : R -> R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousOn.domRestrict`：∀ {α : Type u_1} {β : Type u_2} [inst : Topolo
gicalSpace α] [inst_1 : TopologicalSpace β] {f : α → β} {s : Set α},   Continuou
sOn f s → Cont…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `cfc_apply`：cfc_apply : cfc f a = cfcHom (a
· 使用引理 `SpectrumRestricts.cfcHom_eq_restrict`：cfcHom_eq_restrict (f : C(S, R)) {
a : A} (hpa : p a) (hqa : q a) (h : SpectrumRestricts a f) : cfcHom hpa = h.star
AlgHom (cfcHom hqa)
· 使用定理 `SpectrumRestricts.starAlgHom_apply`：∀ {R : Type u} {S : Type v} {A : Typ
e w} [inst : Semifield R] [inst_1 : StarRing R] [inst_2 : TopologicalSpace R]   
[inst_3 : IsTopologicalS…
· 使用引理 `cfcHom_eq_cfc_extend`：cfcHom_eq_cfc_extend {a : A} (g : R -> R) (ha : p 
a) (f : C(spectrum R a, R)) : cfcHom ha f = cfc (Function.extend Subtype.val f g
) a
· 使用引理 `cfc_congr`：cfc_congr {f g : R -> R} {a : A} (hfg : (spectrum R a).EqOn f
 g) : cfc f a = cfc g a
· 使用定理 `CanLift.prf`：∀ {α : Sort u_1} {β : Sort u_2} {coe : outParam (β → α)} {c
ond : outParam (α → Prop)} [self : CanLift α β coe cond]   (x : α), cond x → ∃ y
,…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Function.Injective.extend_apply`：∀ {α : Sort u_1} {β : Sort u_2} {γ : So
rt u_3} {f : α → β},   Function.Injective f → ∀ (g : α → γ) (e' : β → γ) (a : α)
, Function.extend f g…
· 使用定理 `Subtype.map_coe`：∀ {α : Sort u_1} {β : Sort u_2} {p : α → Prop} {q : β →
 Prop} (f : α → β) (h : ∀ (a : α), p a → q (f a))   (a : Subtype p), ↑(Subtype.m
ap f …
· 使用定理 `StarAlgHom.ofId_apply`：∀ (R : Type u_7) (A : Type u_8) [inst : CommSemir
ing R] [inst_1 : StarRing R] [inst_2 : Semiring A] [inst_3 : StarMul A]   [inst_
4 : Algebra…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用引理 `Topology.IsEmbedding.continuousOn_iff`：Topology.IsEmbedding.continuousOn
_iff {f : α -> β} {g : β -> γ} (hg : IsEmbedding g) {s : Set α} : ContinuousOn f
 s ↔ ContinuousOn (g ∘ f) s
· 使用定理 `Topology.IsClosedEmbedding.isEmbedding`：∀ {X : Type u_1} {Y : Type u_2} 
{f : X → Y} [inst : TopologicalSpace X] [inst_1 : TopologicalSpace Y],   Topolog
y.IsClosedEmbedding f → Topo…
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `QuasispectrumRestricts.left_inv`：∀ {R : Type u_3} {S : Type u_4} {A : Ty
pe u_5} [inst : CommSemiring R] [inst_1 : CommSemiring S]   [inst_2 : NonUnitalR
ing A] [inst_3 : _roo…
· 使用定理 `ContinuousOn.comp`：ContinuousOn.comp {g : β -> γ} {t : Set β} (hg : Cont
inuousOn g t) (hf : ContinuousOn f s) (h : MapsTo f s t) : ContinuousOn (g ∘ f) 
s
· 使用定理 `Continuous.continuousOn`：Continuous.continuousOn (h : Continuous f) : Co
ntinuousOn f s
· 使用定理 `Topology.IsEmbedding.continuous`：∀ {X : Type u_1} {Y : Type u_2} {f : X 
→ Y} [inst : TopologicalSpace X] [inst_1 : TopologicalSpace Y],   Topology.IsEmb
edding f → Continuous…
· 使用定理 `spectrum.algebraMap_mem`：∀ (S : Type u_1) {R : Type u_2} {A : Type u_3} 
[inst : CommSemiring R] [inst_1 : CommSemiring S] [inst_2 : Ring A]   [inst_3 : 
Algebra R S] …
· 使用引理 `cfc_apply_of_not_continuousOn`：cfc_apply_of_not_continuousOn {f : R -> R
} (a : A) (hf : ¬ ContinuousOn f (spectrum R a)) : cfc f a = 0
-/
lemma cfc_eq_restrict (f : C(S, R)) (halg : IsClosedEmbedding (algebraMap R S)) {a : A} (hpa : p a)
    (hqa : q a) (h : SpectrumRestricts a f) (g : R → R) :
    cfc g a = cfc (fun x ↦ algebraMap R S (g (f x))) a := by
  by_cases hg : ContinuousOn g (spectrum R a)
  · rw [cfc_apply g a, cfcHom_eq_restrict f hpa hqa h, SpectrumRestricts.starAlgHom_apply,
      cfcHom_eq_cfc_extend 0]
    apply cfc_congr fun x hx ↦ ?_
    lift x to spectrum S a using hx
    simp [Function.comp]
  · have : ¬ ContinuousOn (fun x ↦ algebraMap R S (g (f x)) : S → S) (spectrum S a) := by
      refine fun hg' ↦ hg ?_
      rw [halg.isEmbedding.continuousOn_iff]
      simpa [halg.isEmbedding.continuousOn_iff, Function.comp_def, h.left_inv _] using
        hg'.comp halg.isEmbedding.continuous.continuousOn (fun _ : R ↦ spectrum.algebraMap_mem S)
    rw [cfc_apply_of_not_continuousOn a hg, cfc_apply_of_not_continuousOn a this]

end Generic

variable [ClosedEmbeddingContinuousFunctionalCalculus S A q]
  [ContinuousMap.UniqueHom R A] [CompleteSpace R]

open ContinuousFunctionalCalculus in
/-- Given a `ContinuousFunctionalCalculus S A q`. If we form the predicate `p` for `a : A`
characterized by: `q a` and the spectrum of `a` restricts to the scalar subring `R` via
`f : C(S, R)`, then we can get a restricted functional calculus
`ContinuousFunctionalCalculus R A p`. -/
/-
**SpectrumRestricts.closedEmbeddingCFC** 是 Mathlib 中的一个定理，位于命名空间 `SpectrumRestri
cts`。
形式化陈述：∀ {R : Type u_1} {S : Type u_2} {A : Type u_3} {p q : A → Prop} [inst : Se
mifield R] [inst_1 : StarRing R]   [inst_2 : MetricSpace R] [inst_3 : IsTopologi
calSemiring R] [inst_4 : ContinuousStar R] [inst_5 : Semifield S]   [inst_6 : St
arRing S] [inst_7 : MetricSpace S] [inst_8 : IsTopologicalSemiring S] [inst_9 : 
ContinuousStar S]   [inst_10 : Ring A] [inst_11 : StarRing A] [inst_12 : Algebra
 S A] [inst_13 : Algebra R S] [inst_14 : Algebra R A]   [IsScalarTower R S A] [S
tarModule R S] [ContinuousSMul R S] [inst_18 : TopologicalSpace A]   [ClosedEmbe
ddingContinuousFunctionalCalculus S A q] [ContinuousMap.UniqueHom R A] [Complete
Space R] (f : C(S, R)),   IsUniformEmbedding ⇑(algebraMap R S) →     p 0 → (∀ (a
 : A), p a ↔ q a ∧ SpectrumRestricts a ⇑f) → ClosedEmbeddingContinuousFunctional
Calculus R A p
参数：f : C(S, R)；algebraMap R S；∀ (a : A), p a ↔ q a ∧ SpectrumRestricts a ⇑f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SpectrumRestricts.cfc`：∀ {R : Type u_1} {S : Type u_2} {A : Type u_3} {p
 q : A → Prop} [inst : Semifield R] [inst_1 : StarRing R]   [inst_2 : MetricSpac
e R] [inst_…
· 使用定理 `ClosedEmbeddingContinuousFunctionalCalculus.toContinuousFunctionalCalcul
us`：∀ {R : Type u_1} {A : Type u_2} {p : outParam (A → Prop)} {inst : CommSemiri
ng R} {inst_1 : StarRing R}   {inst_2 : MetricSpace R} {inst_3 :…
· 使用定理 `IsUniformEmbedding.isClosedEmbedding`：IsUniformEmbedding.isClosedEmbeddi
ng [UniformSpace α] [UniformSpace β] [CompleteSpace α] [T0Space β] {f : α -> β} 
(hf : IsUniformEmbedding f…
· 使用定理 `T3Space.toT0Space`：∀ {X : Type u} {inst : TopologicalSpace X} [self : T3
Space X], T0Space X
· 使用定理 `T4Space.t3Space`：∀ {X : Type u_1} [inst : TopologicalSpace X] [T4Space X
], T3Space X
· 使用定理 `instT4SpaceOfT1SpaceOfNormalSpace`：∀ {X : Type u_1} [inst : TopologicalS
pace X] [T1Space X] [NormalSpace X], T4Space X
· 使用定理 `T2Space.t1Space`：∀ {X : Type u_1} [inst : TopologicalSpace X] [T2Space X
], T1Space X
· 使用定理 `TopologicalSpace.t2Space_of_metrizableSpace`：∀ {X : Type u_2} [inst : To
pologicalSpace X] [TopologicalSpace.MetrizableSpace X], T2Space X
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α
· 使用定理 `CompletelyNormalSpace.toNormalSpace`：∀ {X : Type u_1} [inst : Topologica
lSpace X] [CompletelyNormalSpace X], NormalSpace X
· 使用定理 `UniformSpace.completelyNormalSpace_of_isCountablyGenerated_uniformity`：∀
 {α : Type u} [inst : UniformSpace α] [(uniformity α).IsCountablyGenerated], Com
pletelyNormalSpace α
· 使用定理 `EMetric.instIsCountablyGeneratedUniformity`：∀ {α : Type u} [inst : Pseud
oEMetricSpace α], (uniformity α).IsCountablyGenerated
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `SpectrumRestricts.cfcHom_eq_restrict`：cfcHom_eq_restrict (f : C(S, R)) {
a : A} (hpa : p a) (hqa : q a) (h : SpectrumRestricts a f) : cfcHom hpa = h.star
AlgHom (cfcHom hqa)
· 使用引理 `SpectrumRestricts.isClosedEmbedding_starAlgHom`：isClosedEmbedding_starAl
gHom {a : A} {φ : C(spectrum S a, S) ->⋆ₐ[S] A} (hφ : IsClosedEmbedding φ) {f : 
C(S, R)} (h : SpectrumRestricts a f)…
· 使用引理 `cfcHom_isClosedEmbedding`：cfcHom_isClosedEmbedding {R A : Type*} {p : A 
-> Prop} [CommSemiring R] [StarRing R] [MetricSpace R] [IsTopologicalSemiring R]
 [ContinuousSt…

--- 原说明 ---
Given a `ContinuousFunctionalCalculus S A q`. If we form the predicate `p` for `
a : A`
characterized by: `q a` and the spectrum of `a` restricts to the scalar subring 
`R` via
`f : C(S, R)`, then we can get a restricted functional calculus
`ContinuousFunctionalCalculus R A p`.
-/
protected theorem closedEmbeddingCFC (f : C(S, R)) (halg : IsUniformEmbedding (algebraMap R S))
    (h0 : p 0) (h : ∀ a, p a ↔ q a ∧ SpectrumRestricts a f) :
    ClosedEmbeddingContinuousFunctionalCalculus R A p where
  toContinuousFunctionalCalculus := SpectrumRestricts.cfc f halg.isClosedEmbedding h0 h
  isClosedEmbedding a ha := by
    have := SpectrumRestricts.cfc f halg.isClosedEmbedding h0 h
    rw [cfcHom_eq_restrict f ha ((h a).mp ha).1 ((h a).mp ha).2]
    exact isClosedEmbedding_starAlgHom (cfcHom_isClosedEmbedding ((h a).mp ha).1)
      ((h a).mp ha).2 halg

end SpectrumRestricts


namespace QuasispectrumRestricts

local notation "σₙ" => quasispectrum
open ContinuousMapZero Set

/-- The homeomorphism `quasispectrum S a ≃ₜ quasispectrum R a` induced by
`QuasispectrumRestricts a f`. -/
/-
**QuasispectrumRestricts.homeomorph** 是 Mathlib 中的一个定义，位于命名空间 `QuasispectrumRest
ricts`。
形式化陈述：homeomorph {R S A : Type*} [Semifield R] [Field S] [NonUnitalRing A] [Alge
bra R S] [Module R A] [Module S A] [IsScalarTower R S A] [TopologicalSpace R] [T
opologicalSpace S] [ContinuousSMul R S] [IsScalarTower S A A] [SMulCommClass S A
 A] {a : A} {f : C(S, R)} (h : QuasispectrumRestricts a f) : σₙ S a ≃ₜ σₙ R a wh
ere toFun
参数：S, R；h : QuasispectrumRestricts a f。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The homeomorphism `quasispectrum S a ≃ₜ quasispectrum R a` induced by
`QuasispectrumRestricts a f`.
-/
def homeomorph {R S A : Type*} [Semifield R] [Field S] [NonUnitalRing A]
    [Algebra R S] [Module R A] [Module S A] [IsScalarTower R S A] [TopologicalSpace R]
    [TopologicalSpace S] [ContinuousSMul R S] [IsScalarTower S A A] [SMulCommClass S A A]
    {a : A} {f : C(S, R)} (h : QuasispectrumRestricts a f) :
    σₙ S a ≃ₜ σₙ R a where
  toFun := MapsTo.restrict f _ _ h.subset_preimage
  invFun := MapsTo.restrict (algebraMap R S) _ _ (image_subset_iff.mp h.algebraMap_image.subset)
  left_inv x := Subtype.ext <| h.rightInvOn x.2
  right_inv x := Subtype.ext <| h.left_inv x

universe u v w

open ContinuousMapZero
set_option backward.isDefEq.respectTransparency.types false in
/-- If the quasispectrum of an element restricts to a smaller scalar ring, then a non-unital
continuous functional calculus over the larger scalar ring descends to the smaller one. -/
@[simps!]
/-
**QuasispectrumRestricts.nonUnitalStarAlgHom** 是 Mathlib 中的一个定义，位于命名空间 `Quasispe
ctrumRestricts`。
形式化陈述：nonUnitalStarAlgHom {R : Type u} {S : Type v} {A : Type w} [Semifield R] [
StarRing R] [TopologicalSpace R] [IsTopologicalSemiring R] [ContinuousStar R] [F
ield S] [StarRing S] [TopologicalSpace S] [IsTopologicalRing S] [ContinuousStar 
S] [NonUnitalRing A] [StarRing A] [Algebra R S] [Module R A] [Module S A] [IsSca
larTower S A A] [SMulCommClass S A A] [IsScalarTower R S A] [StarModule R S] [Co
ntinuousSMul R S] {a : A} (φ : C(σₙ S a, S)₀ ->⋆ₙₐ[S] A) {f : C(S, R)} (h : Quas
ispectrumRestricts a f) : 
参数：φ : C(σₙ S a, S)₀ ->⋆ₙₐ[S] A；S, R；h : QuasispectrumRestricts a f。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If the quasispectrum of an element restricts to a smaller scalar ring, then a no
n-unital
continuous functional calculus over the larger scalar ring descends to the small
er one.
-/
def nonUnitalStarAlgHom {R : Type u} {S : Type v} {A : Type w} [Semifield R]
    [StarRing R] [TopologicalSpace R] [IsTopologicalSemiring R] [ContinuousStar R] [Field S]
    [StarRing S] [TopologicalSpace S] [IsTopologicalRing S] [ContinuousStar S] [NonUnitalRing A]
    [StarRing A] [Algebra R S] [Module R A] [Module S A] [IsScalarTower S A A] [SMulCommClass S A A]
    [IsScalarTower R S A] [StarModule R S] [ContinuousSMul R S] {a : A}
    (φ : C(σₙ S a, S)₀ →⋆ₙₐ[S] A) {f : C(S, R)} (h : QuasispectrumRestricts a f) :
    C(σₙ R a, R)₀ →⋆ₙₐ[R] A :=
  (φ.restrictScalars R).comp <|
    (nonUnitalStarAlgHom_postcomp (σₙ S a) (StarAlgHom.ofId R S) (algebraMapCLM R S).continuous)
      |>.comp <| nonUnitalStarAlgHom_precomp R
        ⟨⟨Subtype.map f h.subset_preimage, (map_continuous f).subtype_map
          fun x (hx : x ∈ σₙ S a) => h.subset_preimage hx⟩, Subtype.ext h.map_zero⟩

variable {R S A : Type*} {p q : A → Prop}
variable [Semifield R] [StarRing R] [MetricSpace R] [IsTopologicalSemiring R] [ContinuousStar R]
variable [Field S] [StarRing S] [MetricSpace S] [IsTopologicalRing S] [ContinuousStar S]
variable [NonUnitalRing A] [StarRing A] [Module S A] [IsScalarTower S A A]
variable [SMulCommClass S A A]
variable [Algebra R S] [Module R A] [IsScalarTower R S A] [StarModule R S] [ContinuousSMul R S]
/-
**QuasispectrumRestricts.nonUnitalStarAlgHom_id** 是 Mathlib 中的一个引理，位于命名空间 `Quasi
spectrumRestricts`。
形式化陈述：nonUnitalStarAlgHom_id {a : A} {φ : C(σₙ S a, S)₀ ->⋆ₙₐ[S] A} {f : C(S, R)
} (h : QuasispectrumRestricts a f) (h_id : φ (.id _) = a) : h.nonUnitalStarAlgHo
m φ (.id _) = a
参数：σₙ S a, S；S, R；h : QuasispectrumRestricts a f；h_id : φ (.id _) = a。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `EuclideanDomain.toNontrivial`：∀ {R : Type u} [self : EuclideanDomain R],
 Nontrivial R
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
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `instFactMemSetQuasispectrumOfNat`：∀ {R : Type u_1} {A : Type u_2} [inst 
: CommSemiring R] [inst_1 : NonUnitalRing A] [inst_2 : _root_.Module R A]   [Non
trivial R] (a : A), Fa…
· 使用定理 `IsDomain.toNontrivial`：∀ {α : Type u} {inst : Semiring α} [self : IsDoma
in α], Nontrivial α
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `IsTopologicalSemiring.toIsSemitopologicalSemiring`：∀ (R : Type u_2) [ins
t : TopologicalSpace R] [inst_1 : NonUnitalNonAssocSemiring R] [IsTopologicalSem
iring R],   IsSemitopologicalSemiring R
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `QuasispectrumRestricts.nonUnitalStarAlgHom_apply`：∀ {R : Type u} {S : Ty
pe v} {A : Type w} [inst : Semifield R] [inst_1 : StarRing R] [inst_2 : Topologi
calSpace R]   [inst_3 : IsTopologicalS…
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `ContinuousMapZero.ext`：ext {f g : C(X, R)₀} (h : forall x, f x = g x) : 
f = g
· 使用定理 `QuasispectrumRestricts.rightInvOn`：∀ {R : Type u_3} {S : Type u_4} {A : 
Type u_5} [inst : CommSemiring R] [inst_1 : CommSemiring S]   [inst_2 : NonUnita
lRing A] [inst_3 : _roo…
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
-/
lemma nonUnitalStarAlgHom_id {a : A} {φ : C(σₙ S a, S)₀ →⋆ₙₐ[S] A} {f : C(S, R)}
    (h : QuasispectrumRestricts a f) (h_id : φ (.id _) = a) :
    h.nonUnitalStarAlgHom φ (.id _) = a := by
  simp only [QuasispectrumRestricts.nonUnitalStarAlgHom_apply]
  convert! h_id
  ext x
  exact h.rightInvOn x.2

open ContinuousMapZero in
/-
**QuasispectrumRestricts.nonUnitalStarAlgHom_injective** 是 Mathlib 中的一个引理，位于命名空间
 `QuasispectrumRestricts`。
形式化陈述：nonUnitalStarAlgHom_injective {a : A} {φ : C(σₙ S a, S)₀ ->⋆ₙₐ[S] A} (hφ :
 Function.Injective φ) {f : C(S, R)} (h : QuasispectrumRestricts a f) (halg : Fu
nction.Injective (algebraMap R S)) : Function.Injective (h.nonUnitalStarAlgHom φ
)
参数：σₙ S a, S；hφ : Function.Injective φ；S, R；h : QuasispectrumRestricts a f；halg 
: Function.Injective (algebraMap R S)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `EuclideanDomain.toNontrivial`：∀ {R : Type u} [self : EuclideanDomain R],
 Nontrivial R
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
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `IsDomain.toNontrivial`：∀ {α : Type u} {inst : Semiring α} [self : IsDoma
in α], Nontrivial α
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `Subtype.ext`：∀ {α : Sort u} {p : α → Prop} {a1 a2 : { x // p x }}, ↑a1 =
 ↑a2 → a1 = a2
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `MonoidWithZeroHomClass.toZeroHomClass`：∀ {F : Type u_7} {α : outParam (T
ype u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : MulZe
roOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `Function.Injective.comp`：∀ {α : Sort u_1} {β : Sort u_2} {γ : Sort u_3} 
{g : β → γ} {f : α → β},   Function.Injective g → Function.Injective f → Functio
n.Injective (…
· 使用定理 `ContinuousLinearMap.continuous`：∀ {R₁ : Type u_1} {R₂ : Type u_2} [inst 
: Semiring R₁] [inst_1 : Semiring R₂] {σ₁₂ : R₁ →+* R₂} {M₁ : Type u_4}   [inst_
2 : TopologicalSpace…
· 使用定理 `ContinuousMapZero.postcomp_injective`：postcomp_injective (g : C(Y, R)₀) 
(hg : Injective g) : Injective (g.comp : C(X, Y)₀ -> C(X, R)₀)
· 使用定理 `UniformEquiv.injective`：∀ {α : Type u} {β : Type u_1} [inst : UniformSpa
ce α] [inst_1 : UniformSpace β] (h : α ≃ᵤ β), Function.Injective ⇑h
-/
lemma nonUnitalStarAlgHom_injective {a : A} {φ : C(σₙ S a, S)₀ →⋆ₙₐ[S] A}
    (hφ : Function.Injective φ) {f : C(S, R)} (h : QuasispectrumRestricts a f)
    (halg : Function.Injective (algebraMap R S)) :
    Function.Injective (h.nonUnitalStarAlgHom φ) :=
  have : h.homeomorph.symm 0 = 0 := Subtype.ext (map_zero <| algebraMap _ _)
  hφ.comp <|
    (postcomp_injective ⟨⟨(StarAlgHom.ofId R S), (algebraMapCLM R S).continuous⟩, _⟩ halg).comp <|
    (UniformEquiv.arrowCongrLeft₀ h.homeomorph.symm this |>.injective)

variable [TopologicalSpace A]

section Generic

variable [NonUnitalContinuousFunctionalCalculus S A q]

open ContinuousMapZero in
/-
**QuasispectrumRestricts.continuous_nonUnitalStarAlgHom** 是 Mathlib 中的一个引理，位于命名空
间 `QuasispectrumRestricts`。
形式化陈述：continuous_nonUnitalStarAlgHom {a : A} {φ : C(σₙ S a, S)₀ ->⋆ₙₐ[S] A} (hφ 
: Continuous φ) {f : C(S, R)} (h : QuasispectrumRestricts a f) : Continuous (h.n
onUnitalStarAlgHom φ)
参数：σₙ S a, S；hφ : Continuous φ；S, R；h : QuasispectrumRestricts a f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `EuclideanDomain.toNontrivial`：∀ {R : Type u} [self : EuclideanDomain R],
 Nontrivial R
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
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `Continuous.comp`：Continuous.comp {g : Y -> Z} (hg : Continuous g) (hf : 
Continuous f) : Continuous (g ∘ f)
· 使用定理 `IsDomain.toNontrivial`：∀ {α : Type u} {inst : Semiring α} [self : IsDoma
in α], Nontrivial α
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `ContinuousMapZero.continuous_postcomp`：continuous_postcomp (g : C(Y, R)₀
) : Continuous (g.comp : C(X, Y)₀ -> C(X, R)₀)
· 使用引理 `ContinuousMapZero.continuous_precomp`：continuous_precomp (f : C(X, Y)₀) 
: Continuous fun g : C(Y, R)₀ => g.comp f
-/
lemma continuous_nonUnitalStarAlgHom {a : A} {φ : C(σₙ S a, S)₀ →⋆ₙₐ[S] A}
    (hφ : Continuous φ) {f : C(S, R)} (h : QuasispectrumRestricts a f) :
    Continuous (h.nonUnitalStarAlgHom φ) :=
  hφ.comp <| (continuous_postcomp _).comp (continuous_precomp _)

variable [CompleteSpace R] in
/-
**QuasispectrumRestricts.isClosedEmbedding_nonUnitalStarAlgHom** 是 Mathlib 中的一个引
理，位于命名空间 `QuasispectrumRestricts`。
形式化陈述：isClosedEmbedding_nonUnitalStarAlgHom {a : A} {φ : C(σₙ S a, S)₀ ->⋆ₙₐ[S] 
A} (hφ : IsClosedEmbedding φ) {f : C(S, R)} (h : QuasispectrumRestricts a f) (ha
lg : IsUniformEmbedding (algebraMap R S)) : IsClosedEmbedding (h.nonUnitalStarAl
gHom φ)
参数：σₙ S a, S；hφ : IsClosedEmbedding φ；S, R；h : QuasispectrumRestricts a f；halg :
 IsUniformEmbedding (algebraMap R S)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `EuclideanDomain.toNontrivial`：∀ {R : Type u} [self : EuclideanDomain R],
 Nontrivial R
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
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `IsDomain.toNontrivial`：∀ {α : Type u} {inst : Semiring α} [self : IsDoma
in α], Nontrivial α
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `Subtype.ext`：∀ {α : Sort u} {p : α → Prop} {a1 a2 : { x // p x }}, ↑a1 =
 ↑a2 → a1 = a2
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `MonoidWithZeroHomClass.toZeroHomClass`：∀ {F : Type u_7} {α : outParam (T
ype u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : MulZe
roOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `Topology.IsClosedEmbedding.comp`：∀ {X : Type u_1} {Y : Type u_2} {Z : Ty
pe u_3} {f : X → Y} {g : Y → Z} [inst : TopologicalSpace X]   [inst_1 : Topologi
calSpace Y] [inst_2 :…
· 使用定理 `IsUniformEmbedding.isClosedEmbedding`：IsUniformEmbedding.isClosedEmbeddi
ng [UniformSpace α] [UniformSpace β] [CompleteSpace α] [T0Space β] {f : α -> β} 
(hf : IsUniformEmbedding f…
· 使用定理 `ContinuousMapZero.instCompleteSpaceOfT1SpaceOfContinuousMap`：∀ {X : Type
 u_1} {R : Type u_2} [inst : Zero X] [inst_1 : TopologicalSpace X] [inst_2 : Zer
o R]   [inst_3 : UniformSpace R] [T1Space R] [Com…
· 使用定理 `T2Space.t1Space`：∀ {X : Type u_1} [inst : TopologicalSpace X] [T2Space X
], T1Space X
· 使用定理 `TopologicalSpace.t2Space_of_metrizableSpace`：∀ {X : Type u_2} [inst : To
pologicalSpace X] [TopologicalSpace.MetrizableSpace X], T2Space X
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α
· 使用定理 `FrechetUrysohnSpace.to_sequentialSpace`：∀ {X : Type u_1} [inst : Topolog
icalSpace X] [FrechetUrysohnSpace X], SequentialSpace X
· 使用定理 `FirstCountableTopology.frechetUrysohnSpace`：∀ {X : Type u_1} [inst : Top
ologicalSpace X] [FirstCountableTopology X], FrechetUrysohnSpace X
· 使用定理 `TopologicalSpace.PseudoMetrizableSpace.firstCountableTopology`：∀ {X : Ty
pe u_2} [inst : TopologicalSpace X] [h : TopologicalSpace.PseudoMetrizableSpace 
X], FirstCountableTopology X
· 使用定理 `PseudoEMetricSpace.pseudoMetrizableSpace`：∀ {α : Type u_2} [inst : Pseud
oEMetricSpace α], TopologicalSpace.PseudoMetrizableSpace α
· 使用定理 `ContinuousMapZero.instT0Space`：∀ {X : Type u_1} {R : Type u_3} [inst : Z
ero X] [inst_1 : Zero R] [inst_2 : TopologicalSpace X]   [inst_3 : TopologicalSp
ace R] [T0Space R],…
· 使用定理 `T3Space.toT0Space`：∀ {X : Type u} {inst : TopologicalSpace X} [self : T3
Space X], T0Space X
· 使用定理 `T4Space.t3Space`：∀ {X : Type u_1} [inst : TopologicalSpace X] [T4Space X
], T3Space X
· 使用定理 `instT4SpaceOfT1SpaceOfNormalSpace`：∀ {X : Type u_1} [inst : TopologicalS
pace X] [T1Space X] [NormalSpace X], T4Space X
· 使用定理 `CompletelyNormalSpace.toNormalSpace`：∀ {X : Type u_1} [inst : Topologica
lSpace X] [CompletelyNormalSpace X], NormalSpace X
· 使用定理 `UniformSpace.completelyNormalSpace_of_isCountablyGenerated_uniformity`：∀
 {α : Type u} [inst : UniformSpace α] [(uniformity α).IsCountablyGenerated], Com
pletelyNormalSpace α
· 使用定理 `EMetric.instIsCountablyGeneratedUniformity`：∀ {α : Type u} [inst : Pseud
oEMetricSpace α], (uniformity α).IsCountablyGenerated
· 使用定理 `IsUniformEmbedding.comp`：IsUniformEmbedding.comp {g : β -> γ} (hg : IsUn
iformEmbedding g) {f : α -> β} (hf : IsUniformEmbedding f) : IsUniformEmbedding 
(g ∘ f) where…
（共 32 条，此处仅展示前 30 条）
-/
lemma isClosedEmbedding_nonUnitalStarAlgHom {a : A} {φ : C(σₙ S a, S)₀ →⋆ₙₐ[S] A}
    (hφ : IsClosedEmbedding φ) {f : C(S, R)} (h : QuasispectrumRestricts a f)
    (halg : IsUniformEmbedding (algebraMap R S)) :
    IsClosedEmbedding (h.nonUnitalStarAlgHom φ) := by
  have : h.homeomorph.symm 0 = 0 := Subtype.ext (map_zero <| algebraMap _ _)
  refine hφ.comp <| IsUniformEmbedding.isClosedEmbedding <| .comp
    (ContinuousMapZero.isUniformEmbedding_comp _ halg)
    (UniformEquiv.arrowCongrLeft₀ h.homeomorph.symm this |>.isUniformEmbedding)

variable [IsScalarTower R A A] [SMulCommClass R A A]

set_option backward.isDefEq.respectTransparency.types false in
/-- Given a `NonUnitalContinuousFunctionalCalculus S A q`. If we form the predicate `p` for `a : A`
characterized by: `q a` and the quasispectrum of `a` restricts to the scalar subring `R` via
`f : C(S, R)`, then we can get a restricted functional calculus
`NonUnitalContinuousFunctionalCalculus R A p`. -/
/-
**QuasispectrumRestricts.cfc** 是 Mathlib 中的一个定理，位于命名空间 `QuasispectrumRestricts`。
形式化陈述：∀ {R : Type u_1} {S : Type u_2} {A : Type u_3} {p q : A → Prop} [inst : Se
mifield R] [inst_1 : StarRing R]   [inst_2 : MetricSpace R] [inst_3 : IsTopologi
calSemiring R] [inst_4 : ContinuousStar R] [inst_5 : Field S]   [inst_6 : StarRi
ng S] [inst_7 : MetricSpace S] [inst_8 : IsTopologicalRing S] [inst_9 : Continuo
usStar S]   [inst_10 : NonUnitalRing A] [inst_11 : StarRing A] [inst_12 : _root_
.Module S A] [inst_13 : IsScalarTower S A A]   [inst_14 : SMulCommClass S A A] [
inst_15 : Algebra R S] [inst_16 : _root_.Module R A] [IsScalarTower R S A]   [St
arModule R S] [ContinuousSMul R S] [inst_20 : TopologicalSpace A] [NonUnitalCont
inuousFunctionalCalculus S A q]   [inst_22 : IsScalarTower R A A] [inst_23 : SMu
lCommClass R A A] (f : C(S, R)),   Topology.IsClosedEmbedding ⇑(algebraMap R S) 
→     p 0 → (∀ (a : A), p a ↔ q a ∧ QuasispectrumRestricts a ⇑f) → NonUnitalCont
inuousFunctionalCalculus R A p
参数：f : C(S, R)；algebraMap R S；∀ (a : A), p a ↔ q a ∧ QuasispectrumRestricts a ⇑f
。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `EuclideanDomain.toNontrivial`：∀ {R : Type u} [self : EuclideanDomain R],
 Nontrivial R
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `IsDomain.toNontrivial`：∀ {α : Type u} {inst : Semiring α} [self : IsDoma
in α], Nontrivial α
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `NonUnitalContinuousFunctionalCalculus.compactSpace_quasispectrum`：∀ {R :
 Type u_1} {A : Type u_2} {p : outParam (A → Prop)} {inst : CommSemiring R} {ins
t_1 : Nontrivial R}   {inst_2 : StarRing R} {inst_3 : …
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `isCompact_iff_compactSpace`：isCompact_iff_compactSpace : IsCompact s ↔ C
ompactSpace s
· 使用定理 `quasispectrum.preimage_algebraMap`：quasispectrum.preimage_algebraMap (S 
: Type*) {R A : Type*} [Semifield R] [Field S] [NonUnitalRing A] [Algebra R S] [
Module S A] [IsScalarTo…
· 使用定理 `Topology.IsClosedEmbedding.isCompact_preimage`：Topology.IsClosedEmbeddin
g.isCompact_preimage (hf : IsClosedEmbedding f) {K : Set Y} (hK : IsCompact K) :
 IsCompact (f ⁻¹' K)
· 使用定理 `IsSemitopologicalSemiring.toContinuousAdd`：∀ {R : Type u_2} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSemitopologic
alSemiring R], ContinuousAdd R
· 使用定理 `IsTopologicalSemiring.toIsSemitopologicalSemiring`：∀ (R : Type u_2) [ins
t : TopologicalSpace R] [inst_1 : NonUnitalNonAssocSemiring R] [IsTopologicalSem
iring R],   IsSemitopologicalSemiring R
· 使用定理 `IsSemitopologicalSemiring.toSeparatelyContinuousMul`：∀ {R : Type u_2} {i
nst : TopologicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSem
itopologicalSemiring R], SeparatelyContin…
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用引理 `QuasispectrumRestricts.continuous_nonUnitalStarAlgHom`：continuous_nonUni
talStarAlgHom {a : A} {φ : C(σₙ S a, S)₀ ->⋆ₙₐ[S] A} (hφ : Continuous φ) {f : C(
S, R)} (h : QuasispectrumRestricts a f) : C…
· 使用引理 `cfcₙHom_continuous`：cfcₙHom_continuous : Continuous (cfcₙHom ha : C(σₙ R
 a, R)₀ ->⋆ₙₐ[R] A)
· 使用引理 `QuasispectrumRestricts.nonUnitalStarAlgHom_injective`：nonUnitalStarAlgHo
m_injective {a : A} {φ : C(σₙ S a, S)₀ ->⋆ₙₐ[S] A} (hφ : Function.Injective φ) {
f : C(S, R)} (h : QuasispectrumRestricts a…
· 使用引理 `cfcₙHom_injective`：cfcₙHom_injective : Function.Injective (cfcₙHom ha : 
C(σₙ R a, R)₀ ->⋆ₙₐ[R] A)
· 使用定理 `Topology.IsEmbedding.injective`：∀ {X : Type u_1} {Y : Type u_2} [tX : To
pologicalSpace X] [tY : TopologicalSpace Y] {f : X → Y},   Topology.IsEmbedding 
f → Function.Injecti…
· 使用定理 `Topology.IsClosedEmbedding.toIsEmbedding`：∀ {X : Type u_1} {Y : Type u_2
} [tX : TopologicalSpace X] [tY : TopologicalSpace Y] {f : X → Y},   Topology.Is
ClosedEmbedding f → Topology.I…
· 使用引理 `QuasispectrumRestricts.nonUnitalStarAlgHom_id`：nonUnitalStarAlgHom_id {a
 : A} {φ : C(σₙ S a, S)₀ ->⋆ₙₐ[S] A} {f : C(S, R)} (h : QuasispectrumRestricts a
 f) (h_id : φ (.id _) = a) : h.nonU…
· 使用引理 `cfcₙHom_id`：cfcₙHom_id : cfcₙHom ha (.id (σₙ R a)) = a
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `QuasispectrumRestricts.nonUnitalStarAlgHom_apply`：∀ {R : Type u} {S : Ty
pe v} {A : Type w} [inst : Semifield R] [inst_1 : StarRing R] [inst_2 : Topologi
calSpace R]   [inst_3 : IsTopologicalS…
· 使用引理 `cfcₙHom_map_quasispectrum`：cfcₙHom_map_quasispectrum (f : C(σₙ R a, R)₀)
 : σₙ R (cfcₙHom ha f) = Set.range f
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
（共 39 条，此处仅展示前 30 条）

--- 原说明 ---
Given a `NonUnitalContinuousFunctionalCalculus S A q`. If we form the predicate 
`p` for `a : A`
characterized by: `q a` and the quasispectrum of `a` restricts to the scalar sub
ring `R` via
`f : C(S, R)`, then we can get a restricted functional calculus
`NonUnitalContinuousFunctionalCalculus R A p`.
-/
protected theorem cfc (f : C(S, R)) (halg : IsClosedEmbedding (algebraMap R S)) (h0 : p 0)
    (h : ∀ a, p a ↔ q a ∧ QuasispectrumRestricts a f) :
    NonUnitalContinuousFunctionalCalculus R A p where
  predicate_zero := h0
  compactSpace_quasispectrum a := by
    have := NonUnitalContinuousFunctionalCalculus.compactSpace_quasispectrum (R := S) a
    rw [← isCompact_iff_compactSpace] at this ⊢
    simpa using halg.isCompact_preimage this
  exists_cfc_of_predicate a ha := by
    refine ⟨((h a).mp ha).2.nonUnitalStarAlgHom (cfcₙHom ((h a).mp ha).1 (R := S)),
      ?hom_continuous, ?hom_injective, ?hom_id, ?hom_map_spectrum, ?predicate_hom⟩
    case hom_continuous => exact continuous_nonUnitalStarAlgHom (cfcₙHom_continuous _) _
    case hom_injective => exact nonUnitalStarAlgHom_injective (cfcₙHom_injective _) _ halg.injective
    case hom_id => exact ((h a).mp ha).2.nonUnitalStarAlgHom_id <| cfcₙHom_id ((h a).mp ha).1
    case hom_map_spectrum =>
      simp only [nonUnitalStarAlgHom_apply, ← @quasispectrum.preimage_algebraMap (R := R) S,
        cfcₙHom_map_quasispectrum, Set.ext_iff, Set.mem_preimage, Set.mem_range, comp_apply, coe_mk,
        ContinuousMap.coe_mk, StarAlgHom.ofId_apply, halg.injective.eq_iff]
      exact fun _ _ ↦ ((h a).mp ha).2.homeomorph.exists_congr fun b ↦ Iff.rfl
    case predicate_hom =>
      intro g
      rw [h]
      refine ⟨cfcₙHom_predicate _ _, ?_⟩
      refine { rightInvOn := fun s hs ↦ ?_, left_inv := ((h a).mp ha).2.left_inv }
      rw [nonUnitalStarAlgHom_apply,
        cfcₙHom_map_quasispectrum] at hs
      obtain ⟨r, rfl⟩ := hs
      simp [((h a).mp ha).2.left_inv _]

variable [NonUnitalContinuousFunctionalCalculus R A p]
variable [ContinuousMapZero.UniqueHom R A]
/-
**QuasispectrumRestricts.cfc** 是 Mathlib 中的一个定理，位于命名空间 `QuasispectrumRestricts`。
形式化陈述：∀ {R : Type u_1} {S : Type u_2} {A : Type u_3} {p q : A → Prop} [inst : Se
mifield R] [inst_1 : StarRing R]   [inst_2 : MetricSpace R] [inst_3 : IsTopologi
calSemiring R] [inst_4 : ContinuousStar R] [inst_5 : Field S]   [inst_6 : StarRi
ng S] [inst_7 : MetricSpace S] [inst_8 : IsTopologicalRing S] [inst_9 : Continuo
usStar S]   [inst_10 : NonUnitalRing A] [inst_11 : StarRing A] [inst_12 : _root_
.Module S A] [inst_13 : IsScalarTower S A A]   [inst_14 : SMulCommClass S A A] [
inst_15 : Algebra R S] [inst_16 : _root_.Module R A] [IsScalarTower R S A]   [St
arModule R S] [ContinuousSMul R S] [inst_20 : TopologicalSpace A] [NonUnitalCont
inuousFunctionalCalculus S A q]   [inst_22 : IsScalarTower R A A] [inst_23 : SMu
lCommClass R A A] (f : C(S, R)),   Topology.IsClosedEmbedding ⇑(algebraMap R S) 
→     p 0 → (∀ (a : A), p a ↔ q a ∧ QuasispectrumRestricts a ⇑f) → NonUnitalCont
inuousFunctionalCalculus R A p
参数：f : C(S, R)；algebraMap R S；∀ (a : A), p a ↔ q a ∧ QuasispectrumRestricts a ⇑f
。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `EuclideanDomain.toNontrivial`：∀ {R : Type u} [self : EuclideanDomain R],
 Nontrivial R
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `IsDomain.toNontrivial`：∀ {α : Type u} {inst : Semiring α} [self : IsDoma
in α], Nontrivial α
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `NonUnitalContinuousFunctionalCalculus.compactSpace_quasispectrum`：∀ {R :
 Type u_1} {A : Type u_2} {p : outParam (A → Prop)} {inst : CommSemiring R} {ins
t_1 : Nontrivial R}   {inst_2 : StarRing R} {inst_3 : …
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `isCompact_iff_compactSpace`：isCompact_iff_compactSpace : IsCompact s ↔ C
ompactSpace s
· 使用定理 `quasispectrum.preimage_algebraMap`：quasispectrum.preimage_algebraMap (S 
: Type*) {R A : Type*} [Semifield R] [Field S] [NonUnitalRing A] [Algebra R S] [
Module S A] [IsScalarTo…
· 使用定理 `Topology.IsClosedEmbedding.isCompact_preimage`：Topology.IsClosedEmbeddin
g.isCompact_preimage (hf : IsClosedEmbedding f) {K : Set Y} (hK : IsCompact K) :
 IsCompact (f ⁻¹' K)
· 使用定理 `IsSemitopologicalSemiring.toContinuousAdd`：∀ {R : Type u_2} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSemitopologic
alSemiring R], ContinuousAdd R
· 使用定理 `IsTopologicalSemiring.toIsSemitopologicalSemiring`：∀ (R : Type u_2) [ins
t : TopologicalSpace R] [inst_1 : NonUnitalNonAssocSemiring R] [IsTopologicalSem
iring R],   IsSemitopologicalSemiring R
· 使用定理 `IsSemitopologicalSemiring.toSeparatelyContinuousMul`：∀ {R : Type u_2} {i
nst : TopologicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSem
itopologicalSemiring R], SeparatelyContin…
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用引理 `QuasispectrumRestricts.continuous_nonUnitalStarAlgHom`：continuous_nonUni
talStarAlgHom {a : A} {φ : C(σₙ S a, S)₀ ->⋆ₙₐ[S] A} (hφ : Continuous φ) {f : C(
S, R)} (h : QuasispectrumRestricts a f) : C…
· 使用引理 `cfcₙHom_continuous`：cfcₙHom_continuous : Continuous (cfcₙHom ha : C(σₙ R
 a, R)₀ ->⋆ₙₐ[R] A)
· 使用引理 `QuasispectrumRestricts.nonUnitalStarAlgHom_injective`：nonUnitalStarAlgHo
m_injective {a : A} {φ : C(σₙ S a, S)₀ ->⋆ₙₐ[S] A} (hφ : Function.Injective φ) {
f : C(S, R)} (h : QuasispectrumRestricts a…
· 使用引理 `cfcₙHom_injective`：cfcₙHom_injective : Function.Injective (cfcₙHom ha : 
C(σₙ R a, R)₀ ->⋆ₙₐ[R] A)
· 使用定理 `Topology.IsEmbedding.injective`：∀ {X : Type u_1} {Y : Type u_2} [tX : To
pologicalSpace X] [tY : TopologicalSpace Y] {f : X → Y},   Topology.IsEmbedding 
f → Function.Injecti…
· 使用定理 `Topology.IsClosedEmbedding.toIsEmbedding`：∀ {X : Type u_1} {Y : Type u_2
} [tX : TopologicalSpace X] [tY : TopologicalSpace Y] {f : X → Y},   Topology.Is
ClosedEmbedding f → Topology.I…
· 使用引理 `QuasispectrumRestricts.nonUnitalStarAlgHom_id`：nonUnitalStarAlgHom_id {a
 : A} {φ : C(σₙ S a, S)₀ ->⋆ₙₐ[S] A} {f : C(S, R)} (h : QuasispectrumRestricts a
 f) (h_id : φ (.id _) = a) : h.nonU…
· 使用引理 `cfcₙHom_id`：cfcₙHom_id : cfcₙHom ha (.id (σₙ R a)) = a
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `QuasispectrumRestricts.nonUnitalStarAlgHom_apply`：∀ {R : Type u} {S : Ty
pe v} {A : Type w} [inst : Semifield R] [inst_1 : StarRing R] [inst_2 : Topologi
calSpace R]   [inst_3 : IsTopologicalS…
· 使用引理 `cfcₙHom_map_quasispectrum`：cfcₙHom_map_quasispectrum (f : C(σₙ R a, R)₀)
 : σₙ R (cfcₙHom ha f) = Set.range f
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
（共 39 条，此处仅展示前 30 条）
-/
lemma cfcₙHom_eq_restrict (f : C(S, R)) {a : A} (hpa : p a) (hqa : q a)
    (h : QuasispectrumRestricts a f) :
    cfcₙHom hpa = h.nonUnitalStarAlgHom (cfcₙHom hqa) := by
  apply cfcₙHom_eq_of_continuous_of_map_id
  · exact h.continuous_nonUnitalStarAlgHom (cfcₙHom_continuous hqa)
  · exact h.nonUnitalStarAlgHom_id (cfcₙHom_id hqa)

set_option backward.isDefEq.respectTransparency.types false in
/-
**QuasispectrumRestricts.cfc** 是 Mathlib 中的一个定理，位于命名空间 `QuasispectrumRestricts`。
形式化陈述：∀ {R : Type u_1} {S : Type u_2} {A : Type u_3} {p q : A → Prop} [inst : Se
mifield R] [inst_1 : StarRing R]   [inst_2 : MetricSpace R] [inst_3 : IsTopologi
calSemiring R] [inst_4 : ContinuousStar R] [inst_5 : Field S]   [inst_6 : StarRi
ng S] [inst_7 : MetricSpace S] [inst_8 : IsTopologicalRing S] [inst_9 : Continuo
usStar S]   [inst_10 : NonUnitalRing A] [inst_11 : StarRing A] [inst_12 : _root_
.Module S A] [inst_13 : IsScalarTower S A A]   [inst_14 : SMulCommClass S A A] [
inst_15 : Algebra R S] [inst_16 : _root_.Module R A] [IsScalarTower R S A]   [St
arModule R S] [ContinuousSMul R S] [inst_20 : TopologicalSpace A] [NonUnitalCont
inuousFunctionalCalculus S A q]   [inst_22 : IsScalarTower R A A] [inst_23 : SMu
lCommClass R A A] (f : C(S, R)),   Topology.IsClosedEmbedding ⇑(algebraMap R S) 
→     p 0 → (∀ (a : A), p a ↔ q a ∧ QuasispectrumRestricts a ⇑f) → NonUnitalCont
inuousFunctionalCalculus R A p
参数：f : C(S, R)；algebraMap R S；∀ (a : A), p a ↔ q a ∧ QuasispectrumRestricts a ⇑f
。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `EuclideanDomain.toNontrivial`：∀ {R : Type u} [self : EuclideanDomain R],
 Nontrivial R
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `IsDomain.toNontrivial`：∀ {α : Type u} {inst : Semiring α} [self : IsDoma
in α], Nontrivial α
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `NonUnitalContinuousFunctionalCalculus.compactSpace_quasispectrum`：∀ {R :
 Type u_1} {A : Type u_2} {p : outParam (A → Prop)} {inst : CommSemiring R} {ins
t_1 : Nontrivial R}   {inst_2 : StarRing R} {inst_3 : …
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `isCompact_iff_compactSpace`：isCompact_iff_compactSpace : IsCompact s ↔ C
ompactSpace s
· 使用定理 `quasispectrum.preimage_algebraMap`：quasispectrum.preimage_algebraMap (S 
: Type*) {R A : Type*} [Semifield R] [Field S] [NonUnitalRing A] [Algebra R S] [
Module S A] [IsScalarTo…
· 使用定理 `Topology.IsClosedEmbedding.isCompact_preimage`：Topology.IsClosedEmbeddin
g.isCompact_preimage (hf : IsClosedEmbedding f) {K : Set Y} (hK : IsCompact K) :
 IsCompact (f ⁻¹' K)
· 使用定理 `IsSemitopologicalSemiring.toContinuousAdd`：∀ {R : Type u_2} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSemitopologic
alSemiring R], ContinuousAdd R
· 使用定理 `IsTopologicalSemiring.toIsSemitopologicalSemiring`：∀ (R : Type u_2) [ins
t : TopologicalSpace R] [inst_1 : NonUnitalNonAssocSemiring R] [IsTopologicalSem
iring R],   IsSemitopologicalSemiring R
· 使用定理 `IsSemitopologicalSemiring.toSeparatelyContinuousMul`：∀ {R : Type u_2} {i
nst : TopologicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSem
itopologicalSemiring R], SeparatelyContin…
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用引理 `QuasispectrumRestricts.continuous_nonUnitalStarAlgHom`：continuous_nonUni
talStarAlgHom {a : A} {φ : C(σₙ S a, S)₀ ->⋆ₙₐ[S] A} (hφ : Continuous φ) {f : C(
S, R)} (h : QuasispectrumRestricts a f) : C…
· 使用引理 `cfcₙHom_continuous`：cfcₙHom_continuous : Continuous (cfcₙHom ha : C(σₙ R
 a, R)₀ ->⋆ₙₐ[R] A)
· 使用引理 `QuasispectrumRestricts.nonUnitalStarAlgHom_injective`：nonUnitalStarAlgHo
m_injective {a : A} {φ : C(σₙ S a, S)₀ ->⋆ₙₐ[S] A} (hφ : Function.Injective φ) {
f : C(S, R)} (h : QuasispectrumRestricts a…
· 使用引理 `cfcₙHom_injective`：cfcₙHom_injective : Function.Injective (cfcₙHom ha : 
C(σₙ R a, R)₀ ->⋆ₙₐ[R] A)
· 使用定理 `Topology.IsEmbedding.injective`：∀ {X : Type u_1} {Y : Type u_2} [tX : To
pologicalSpace X] [tY : TopologicalSpace Y] {f : X → Y},   Topology.IsEmbedding 
f → Function.Injecti…
· 使用定理 `Topology.IsClosedEmbedding.toIsEmbedding`：∀ {X : Type u_1} {Y : Type u_2
} [tX : TopologicalSpace X] [tY : TopologicalSpace Y] {f : X → Y},   Topology.Is
ClosedEmbedding f → Topology.I…
· 使用引理 `QuasispectrumRestricts.nonUnitalStarAlgHom_id`：nonUnitalStarAlgHom_id {a
 : A} {φ : C(σₙ S a, S)₀ ->⋆ₙₐ[S] A} {f : C(S, R)} (h : QuasispectrumRestricts a
 f) (h_id : φ (.id _) = a) : h.nonU…
· 使用引理 `cfcₙHom_id`：cfcₙHom_id : cfcₙHom ha (.id (σₙ R a)) = a
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `QuasispectrumRestricts.nonUnitalStarAlgHom_apply`：∀ {R : Type u} {S : Ty
pe v} {A : Type w} [inst : Semifield R] [inst_1 : StarRing R] [inst_2 : Topologi
calSpace R]   [inst_3 : IsTopologicalS…
· 使用引理 `cfcₙHom_map_quasispectrum`：cfcₙHom_map_quasispectrum (f : C(σₙ R a, R)₀)
 : σₙ R (cfcₙHom ha f) = Set.range f
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
（共 39 条，此处仅展示前 30 条）
-/
lemma cfcₙ_eq_restrict (f : C(S, R)) (halg : IsClosedEmbedding (algebraMap R S)) {a : A}
    (hpa : p a) (hqa : q a) (h : QuasispectrumRestricts a f) (g : R → R) :
    cfcₙ g a = cfcₙ (fun x ↦ algebraMap R S (g (f x))) a := by
  by_cases hg : ContinuousOn g (σₙ R a) ∧ g 0 = 0
  · obtain ⟨hg, hg0⟩ := hg
    rw [cfcₙ_apply g a, cfcₙHom_eq_restrict f hpa hqa h, nonUnitalStarAlgHom_apply,
      cfcₙHom_eq_cfcₙ_extend 0]
    apply cfcₙ_congr fun x hx ↦ ?_
    lift x to σₙ S a using hx
    simp
  · simp only [not_and_or] at hg
    obtain (hg | hg) := hg
    · have : ¬ ContinuousOn (fun x ↦ algebraMap R S (g (f x)) : S → S) (σₙ S a) := by
        refine fun hg' ↦ hg ?_
        rw [halg.isEmbedding.continuousOn_iff]
        simpa [halg.isEmbedding.continuousOn_iff, Function.comp_def, h.left_inv _] using
          hg'.comp halg.isEmbedding.continuous.continuousOn
          (fun _ : R ↦ quasispectrum.algebraMap_mem S)
      rw [cfcₙ_apply_of_not_continuousOn a hg, cfcₙ_apply_of_not_continuousOn a this]
    · rw [cfcₙ_apply_of_not_map_zero a hg, cfcₙ_apply_of_not_map_zero a (by simpa [h.map_zero])]

end Generic

variable [NonUnitalClosedEmbeddingContinuousFunctionalCalculus S A q]
  [IsScalarTower R A A] [SMulCommClass R A A]
  [ContinuousMapZero.UniqueHom R A] [CompleteSpace R]

open NonUnitalContinuousFunctionalCalculus in
/-- Given a `NonUnitalContinuousFunctionalCalculus S A q`. If we form the predicate `p` for `a : A`
characterized by: `q a` and the quasispectrum of `a` restricts to the scalar subring `R` via
`f : C(S, R)`, then we can get a restricted functional calculus
`NonUnitalContinuousFunctionalCalculus R A p`. -/
/-
**QuasispectrumRestricts.nonUnitalClosedEmbeddingCFC** 是 Mathlib 中的一个定理，位于命名空间 `
QuasispectrumRestricts`。
形式化陈述：∀ {R : Type u_1} {S : Type u_2} {A : Type u_3} {p q : A → Prop} [inst : Se
mifield R] [inst_1 : StarRing R]   [inst_2 : MetricSpace R] [inst_3 : IsTopologi
calSemiring R] [inst_4 : ContinuousStar R] [inst_5 : Field S]   [inst_6 : StarRi
ng S] [inst_7 : MetricSpace S] [inst_8 : IsTopologicalRing S] [inst_9 : Continuo
usStar S]   [inst_10 : NonUnitalRing A] [inst_11 : StarRing A] [inst_12 : _root_
.Module S A] [inst_13 : IsScalarTower S A A]   [inst_14 : SMulCommClass S A A] [
inst_15 : Algebra R S] [inst_16 : _root_.Module R A] [IsScalarTower R S A]   [St
arModule R S] [ContinuousSMul R S] [inst_20 : TopologicalSpace A]   [NonUnitalCl
osedEmbeddingContinuousFunctionalCalculus S A q] [inst_22 : IsScalarTower R A A]
   [inst_23 : SMulCommClass R A A] [ContinuousMapZero.UniqueHom R A] [CompleteSp
ace R] (f : C(S, R)),   IsUniformEmbedding ⇑(algebraMap R S) →     p 0 →       (
∀ (a : A), p a ↔ q a ∧ QuasispectrumRestricts a ⇑f) → NonUnitalClosedEmbeddingCo
ntinuousFunctionalCalculus R A p
参数：f : C(S, R)；algebraMap R S；∀ (a : A), p a ↔ q a ∧ QuasispectrumRestricts a ⇑f
。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `EuclideanDomain.toNontrivial`：∀ {R : Type u} [self : EuclideanDomain R],
 Nontrivial R
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `IsDomain.toNontrivial`：∀ {α : Type u} {inst : Semiring α} [self : IsDoma
in α], Nontrivial α
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `QuasispectrumRestricts.cfc`：∀ {R : Type u_1} {S : Type u_2} {A : Type u_
3} {p q : A → Prop} [inst : Semifield R] [inst_1 : StarRing R]   [inst_2 : Metri
cSpace R] [inst_…
· 使用定理 `NonUnitalClosedEmbeddingContinuousFunctionalCalculus.toNonUnitalContinuo
usFunctionalCalculus`：∀ {R : Type u_1} {A : Type u_2} {p : outParam (A → Prop)} 
{inst : CommSemiring R} {inst_1 : Nontrivial R}   {inst_2 : StarRing R} {inst_3 
: …
· 使用定理 `IsUniformEmbedding.isClosedEmbedding`：IsUniformEmbedding.isClosedEmbeddi
ng [UniformSpace α] [UniformSpace β] [CompleteSpace α] [T0Space β] {f : α -> β} 
(hf : IsUniformEmbedding f…
· 使用定理 `T3Space.toT0Space`：∀ {X : Type u} {inst : TopologicalSpace X} [self : T3
Space X], T0Space X
· 使用定理 `T4Space.t3Space`：∀ {X : Type u_1} [inst : TopologicalSpace X] [T4Space X
], T3Space X
· 使用定理 `instT4SpaceOfT1SpaceOfNormalSpace`：∀ {X : Type u_1} [inst : TopologicalS
pace X] [T1Space X] [NormalSpace X], T4Space X
· 使用定理 `T2Space.t1Space`：∀ {X : Type u_1} [inst : TopologicalSpace X] [T2Space X
], T1Space X
· 使用定理 `TopologicalSpace.t2Space_of_metrizableSpace`：∀ {X : Type u_2} [inst : To
pologicalSpace X] [TopologicalSpace.MetrizableSpace X], T2Space X
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α
· 使用定理 `CompletelyNormalSpace.toNormalSpace`：∀ {X : Type u_1} [inst : Topologica
lSpace X] [CompletelyNormalSpace X], NormalSpace X
· 使用定理 `UniformSpace.completelyNormalSpace_of_isCountablyGenerated_uniformity`：∀
 {α : Type u} [inst : UniformSpace α] [(uniformity α).IsCountablyGenerated], Com
pletelyNormalSpace α
· 使用定理 `EMetric.instIsCountablyGeneratedUniformity`：∀ {α : Type u} [inst : Pseud
oEMetricSpace α], (uniformity α).IsCountablyGenerated
· 使用定理 `IsSemitopologicalSemiring.toContinuousAdd`：∀ {R : Type u_2} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSemitopologic
alSemiring R], ContinuousAdd R
· 使用定理 `IsTopologicalSemiring.toIsSemitopologicalSemiring`：∀ (R : Type u_2) [ins
t : TopologicalSpace R] [inst_1 : NonUnitalNonAssocSemiring R] [IsTopologicalSem
iring R],   IsSemitopologicalSemiring R
· 使用定理 `IsSemitopologicalSemiring.toSeparatelyContinuousMul`：∀ {R : Type u_2} {i
nst : TopologicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSem
itopologicalSemiring R], SeparatelyContin…
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `QuasispectrumRestricts.cfcₙHom_eq_restrict`：cfcₙHom_eq_restrict (f : C(S
, R)) {a : A} (hpa : p a) (hqa : q a) (h : QuasispectrumRestricts a f) : cfcₙHom
 hpa = h.nonUnitalStarAlgHom (cf…
· 使用引理 `QuasispectrumRestricts.isClosedEmbedding_nonUnitalStarAlgHom`：isClosedEm
bedding_nonUnitalStarAlgHom {a : A} {φ : C(σₙ S a, S)₀ ->⋆ₙₐ[S] A} (hφ : IsClose
dEmbedding φ) {f : C(S, R)} (h : QuasispectrumRest…
· 使用引理 `cfcₙHom_isClosedEmbedding`：cfcₙHom_isClosedEmbedding {R A : Type*} {p : 
A -> Prop} [CommSemiring R] [Nontrivial R] [StarRing R] [MetricSpace R] [IsTopol
ogicalSemiring …

--- 原说明 ---
Given a `NonUnitalContinuousFunctionalCalculus S A q`. If we form the predicate 
`p` for `a : A`
characterized by: `q a` and the quasispectrum of `a` restricts to the scalar sub
ring `R` via
`f : C(S, R)`, then we can get a restricted functional calculus
`NonUnitalContinuousFunctionalCalculus R A p`.
-/
protected theorem nonUnitalClosedEmbeddingCFC (f : C(S, R))
    (halg : IsUniformEmbedding (algebraMap R S))
    (h0 : p 0) (h : ∀ a, p a ↔ q a ∧ QuasispectrumRestricts a f) :
    NonUnitalClosedEmbeddingContinuousFunctionalCalculus R A p where
  toNonUnitalContinuousFunctionalCalculus :=
    QuasispectrumRestricts.cfc f halg.isClosedEmbedding h0 h
  isClosedEmbedding a ha := by
    have := QuasispectrumRestricts.cfc f halg.isClosedEmbedding h0 h
    rw [cfcₙHom_eq_restrict f ha ((h a).mp ha).1 ((h a).mp ha).2]
    exact isClosedEmbedding_nonUnitalStarAlgHom (cfcₙHom_isClosedEmbedding ((h a).mp ha).1)
      ((h a).mp ha).2 halg

end QuasispectrumRestricts

