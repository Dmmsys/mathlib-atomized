/-
Copyright (c) 2024 Jireh Loreaux. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jireh Loreaux
-/
module

public import Mathlib.Algebra.Algebra.Spectrum.Quasispectrum
public import Mathlib.Topology.ContinuousMap.Compact
public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Unital
public import Mathlib.Topology.UniformSpace.CompactConvergence

/-!
# The continuous functional calculus for non-unital algebras

This file defines a generic API for the *continuous functional calculus* in *non-unital* algebras
which is suitable in a wide range of settings. The design is intended to match as closely as
possible that for unital algebras in
`Mathlib/Analysis/CStarAlgebra/ContinuousFunctionalCalculus/Unital.lean`. Changes to either file
should be mirrored in its counterpart whenever possible. The underlying reasons for the design
decisions in the unital case apply equally in the non-unital case. See the module documentation in
that file for more information.

A continuous functional calculus for an element `a : A` in a non-unital topological `R`-algebra is
a continuous extension of the polynomial functional calculus (i.e., `Polynomial.aeval`) for
polynomials with no constant term to continuous `R`-valued functions on `quasispectrum R a` which
vanish at zero. More precisely, it is a continuous star algebra homomorphism
`C(quasispectrum R a, R)₀ →⋆ₙₐ[R] A` that sends `(ContinuousMap.id R).restrict (quasispectrum R a)`
to `a`. In all cases of interest (e.g., when `quasispectrum R a` is compact and `R` is `ℝ≥0`, `ℝ`,
or `ℂ`), this is sufficient to uniquely determine the continuous functional calculus which is
encoded in the `ContinuousMapZero.UniqueHom` class.

## Main declarations

+ `NonUnitalContinuousFunctionalCalculus R A (p : A → Prop)`: a class stating that every `a : A`
  satisfying `p a` has a non-unital star algebra homomorphism from the continuous `R`-valued
  functions on the `R`-quasispectrum of `a` vanishing at zero into the algebra `A`. This map is a
  closed embedding, and satisfies the **spectral mapping theorem**.
+ `cfcₙHom : p a → C(quasispectrum R a, R)₀ →⋆ₐ[R] A`: the underlying non-unital star algebra
  homomorphism for an element satisfying property `p`.
+ `cfcₙ : (R → R) → A → A`: an unbundled version of `cfcₙHom` which takes the junk value `0` when
  `cfcₙHom` is not defined.

## Main theorems

+ `cfcₙ_comp : cfcₙ (x ↦ g (f x)) a = cfcₙ g (cfcₙ f a)`

-/

@[expose] public section
local notation "σₙ" => quasispectrum

open Topology ContinuousMapZero

/--
Definition of `NonUnitalContinuousFunctionalCalculus` / `NonUnitalContinuousFunctionalCalculus` 的定义

English:
class NonUnitalContinuousFunctionalCalculus
  parameters: (R A : Type*) (p : outParam (A -> Prop))
  axioms and operations (3):
    - predicate_zero : p 0
    - [compactSpace_quasispectrum : forall a : A, CompactSpace (σₙ R a)]
    - exists_cfc_of_predicate : forall a, p a -> exists φ : C(σₙ R a, R)₀ ->⋆ₙₐ[R] A,

中文:
类 非幺余ntinuousFunctionalCalculus
  参数: (R A : 类型) (p : outParam (A -> 命题))
  公理与运算 (3 个):
    - predicate_zero : p 0
    - [compactSpace_quasispectrum : 对任意 a : A, 紧空间 (σₙ R a)]
    - exists_cfc_of_predicate : 对任意 a, p a -> 存在 φ : C(σₙ R a, R)₀ ->⋆ₙₐ[R] A,
-/
class NonUnitalContinuousFunctionalCalculus (R A : Type*) (p : outParam (A -> Prop))
    [CommSemiring R] [Nontrivial R] [StarRing R] [MetricSpace R] [IsTopologicalSemiring R]
    [ContinuousStar R] [NonUnitalRing A] [StarRing A] [TopologicalSpace A] [Module R A]
    [IsScalarTower R A A] [SMulCommClass R A A] : Prop where
  predicate_zero : p 0
  [compactSpace_quasispectrum : forall a : A, CompactSpace (σₙ R a)]
  exists_cfc_of_predicate : forall a, p a -> exists φ : C(σₙ R a, R)₀ ->⋆ₙₐ[R] A,
Continuous φ ∧ Function.Injective φ ∧ φ ⟨(ContinuousMap.id R).restrict σₙ R a, rfl⟩ = a ∧
      (forall f, σₙ R (φ f) = Set.range f) ∧ forall f, p (φ f)

-- this instance should not be activated everywhere but it is useful when developing generic API
-- for the continuous functional calculus
scoped[NonUnitalContinuousFunctionalCalculus]
attribute [instance] NonUnitalContinuousFunctionalCalculus.compactSpace_quasispectrum

/--
Definition of `ContinuousMapZero.UniqueHom` / `ContinuousMapZero.UniqueHom` 的定义

English:
class ContinuousMapZero.UniqueHom
  parameters: (R A : Type*) [CommSemiring R] [StarRing R]
  axioms and operations (1):
    - eq_of_continuous_of_map_id((s : Set R) [CompactSpace s] [Fact (0 in s)] (φ ψ : C(s, R)₀ ->⋆ₙₐ[R] A) (hφ : Continuous φ) (hψ : Continuous ψ) (h : φ (.id s) = ψ (.id s))) : φ = ψ

中文:
类 余ntinuousMapZero.唯一态射
  参数: (R A : 类型) [交换半环 R] [对合环 R]
  公理与运算 (1 个):
    - eq_of_continuous_of_map_id((s : 集合 R) [紧空间 s] [Fact (0 in s)] (φ ψ : C(s, R)₀ ->⋆ₙₐ[R] A) (hφ : 连续 φ) (hψ : 连续 ψ) (h : φ (.id s) = ψ (.id s))) : φ = ψ
-/
class ContinuousMapZero.UniqueHom (R A : Type*) [CommSemiring R] [StarRing R]
    [MetricSpace R] [IsTopologicalSemiring R] [ContinuousStar R] [NonUnitalRing A] [StarRing A]
    [TopologicalSpace A] [Module R A] [IsScalarTower R A A] [SMulCommClass R A A] : Prop where
  eq_of_continuous_of_map_id (s : Set R) [CompactSpace s] [Fact (0 in s)]
    (φ ψ : C(s, R)₀ ->⋆ₙₐ[R] A) (hφ : Continuous φ) (hψ : Continuous ψ)
    (h : φ (.id s) = ψ (.id s)) :
    φ = ψ

instance {R A : Type*} [CommSemiring R] [NonUnitalRing A] [Module R A] [Nontrivial R] (a : A) :
    Fact (0 in σₙ R a) :=
  ⟨quasispectrum.zero_mem R a⟩

section Main

variable {R A : Type*} {p : A -> Prop} [CommSemiring R] [Nontrivial R] [StarRing R] [MetricSpace R]
variable [IsTopologicalSemiring R] [ContinuousStar R] [NonUnitalRing A] [StarRing A]
variable [TopologicalSpace A] [Module R A] [IsScalarTower R A A] [SMulCommClass R A A]
variable [instCFCₙ : NonUnitalContinuousFunctionalCalculus R A p]

include instCFCₙ in
/--
lemma `NonUnitalContinuousFunctionalCalculus.isCompact_quasispectrum` / 引理 `NonUnitalContinuousFunctionalCalculus.isCompact_quasispectrum`

English:
lemma NonUnitalContinuousFunctionalCalculus.isCompact_quasispectrum
  given: (a : A)
  proof: isCompact_iff_compactSpace.mpr inferInstance

中文:
引理 非幺余ntinuousFunctionalCalculus.isCompact_quasispectrum
  条件: (a : A)
  证明: isCompact_iff_compactSpace.mpr inferInstance

Depends on / 依赖: isCompact_iff_compactSpace, isCompact_iff_compactSpace.mpr
-/
lemma NonUnitalContinuousFunctionalCalculus.isCompact_quasispectrum (a : A) :
    IsCompact (σₙ R a) :=
  isCompact_iff_compactSpace.mpr inferInstance

/--
lemma `NonUnitalStarAlgHom.ext_continuousMap` / 引理 `NonUnitalStarAlgHom.ext_continuousMap`

English:
lemma NonUnitalStarAlgHom.ext_continuousMap
  statement: [UniqueHom R A]
  proof: UniqueHom.eq_of_continuous_of_map_id _ φ ψ hφ hψ h

中文:
引理 非幺StarAlg态射.ext_continuousMap
  结论: [唯一态射 R A]
  证明: UniqueHom.eq_of_continuous_of_map_id _ φ ψ hφ hψ h

Depends on / 依赖: UniqueHom, UniqueHom.eq_of_continuous_of_map_id, eq_of_continuous_of_map_id
-/
lemma NonUnitalStarAlgHom.ext_continuousMap [UniqueHom R A]
    (a : A) [CompactSpace (σₙ R a)] (φ ψ : C(σₙ R a, R)₀ ->⋆ₙₐ[R] A)
    (hφ : Continuous φ) (hψ : Continuous ψ) (h : φ (.id (σₙ R a)) = ψ (.id (σₙ R a))) :
    φ = ψ :=
  UniqueHom.eq_of_continuous_of_map_id _ φ ψ hφ hψ h

section cfcₙHom

variable {a : A} (ha : p a)

/--
Definition of `cfcₙHom` / `cfcₙHom` 的定义

English:
definition cfcₙHom
  signature: : C(σₙ R a, R)₀ ->⋆ₙₐ[R] A
  body: (NonUnitalContinuousFunctionalCalculus.exists_cfc_of_predicate a ha).choose

@[fun_prop]

中文:
定义 cfcₙHom
  签名: : C(σₙ R a, R)₀ ->⋆ₙₐ[R] A
  定义体: (NonUnitalContinuousFunctionalCalculus.exists_cfc_of_predicate a ha).choose

@[fun_prop]

Depends on / 依赖: NonUnitalContinuousFunctionalCalculus, NonUnitalContinuousFunctionalCalculus.exists_cfc_of_predicate, exists_cfc_of_predicate
-/
noncomputable def cfcₙHom : C(σₙ R a, R)₀ ->⋆ₙₐ[R] A :=
  (NonUnitalContinuousFunctionalCalculus.exists_cfc_of_predicate a ha).choose

@[fun_prop]
/--
lemma `cfcₙHom_continuous` / 引理 `cfcₙHom_continuous`

English:
lemma cfcₙHom_continuous
  statement: Continuous (cfcₙHom ha : C(σₙ R a, R)₀ ->⋆ₙₐ[R] A)
  proof: (NonUnitalContinuousFunctionalCalculus.exists_cfc_of_predicate a ha).choose_spec.1

中文:
引理 cfcₙHom_continuous
  结论: 连续 (cfcₙHom ha : C(σₙ R a, R)₀ ->⋆ₙₐ[R] A)
  证明: (NonUnitalContinuousFunctionalCalculus.exists_cfc_of_predicate a ha).choose_spec.1

Depends on / 依赖: NonUnitalContinuousFunctionalCalculus, NonUnitalContinuousFunctionalCalculus.exists_cfc_of_predicate, choose_spec, exists_cfc_of_predicate
-/
lemma cfcₙHom_continuous : Continuous (cfcₙHom ha : C(σₙ R a, R)₀ ->⋆ₙₐ[R] A) :=
  (NonUnitalContinuousFunctionalCalculus.exists_cfc_of_predicate a ha).choose_spec.1

/--
lemma `cfcₙHom_injective` / 引理 `cfcₙHom_injective`

English:
lemma cfcₙHom_injective
  statement: Function.Injective (cfcₙHom ha : C(σₙ R a, R)₀ ->⋆ₙₐ[R] A)
  proof: (NonUnitalContinuousFunctionalCalculus.exists_cfc_of_predicate a ha).choose_spec.2.1

中文:
引理 cfcₙHom_injective
  结论: 函数.单射 (cfcₙHom ha : C(σₙ R a, R)₀ ->⋆ₙₐ[R] A)
  证明: (NonUnitalContinuousFunctionalCalculus.exists_cfc_of_predicate a ha).choose_spec.2.1

Depends on / 依赖: NonUnitalContinuousFunctionalCalculus, NonUnitalContinuousFunctionalCalculus.exists_cfc_of_predicate, choose_spec, exists_cfc_of_predicate
-/
lemma cfcₙHom_injective : Function.Injective (cfcₙHom ha : C(σₙ R a, R)₀ ->⋆ₙₐ[R] A) :=
  (NonUnitalContinuousFunctionalCalculus.exists_cfc_of_predicate a ha).choose_spec.2.1

/--
lemma `cfcₙHom_id` / 引理 `cfcₙHom_id`

English:
lemma cfcₙHom_id
  statement: cfcₙHom ha (.id (σₙ R a)) = a
  proof: (NonUnitalContinuousFunctionalCalculus.exists_cfc_of_predicate a ha).choose_spec.2.2.1

中文:
引理 cfcₙHom_id
  结论: cfcₙHom ha (.id (σₙ R a)) = a
  证明: (NonUnitalContinuousFunctionalCalculus.exists_cfc_of_predicate a ha).choose_spec.2.2.1

Depends on / 依赖: NonUnitalContinuousFunctionalCalculus, NonUnitalContinuousFunctionalCalculus.exists_cfc_of_predicate, choose_spec, exists_cfc_of_predicate
-/
lemma cfcₙHom_id : cfcₙHom ha (.id (σₙ R a)) = a :=
  (NonUnitalContinuousFunctionalCalculus.exists_cfc_of_predicate a ha).choose_spec.2.2.1

/--
lemma `cfcₙHom_map_quasispectrum` / 引理 `cfcₙHom_map_quasispectrum`

English:
lemma cfcₙHom_map_quasispectrum
  given: (f : C(σₙ R a, R)₀)
  proof: (NonUnitalContinuousFunctionalCalculus.exists_cfc_of_predicate a ha).choose_spec.2.2.2.1 f

中文:
引理 cfcₙHom_map_quasispectrum
  条件: (f : C(σₙ R a, R)₀)
  证明: (NonUnitalContinuousFunctionalCalculus.exists_cfc_of_predicate a ha).choose_spec.2.2.2.1 f

Depends on / 依赖: NonUnitalContinuousFunctionalCalculus, NonUnitalContinuousFunctionalCalculus.exists_cfc_of_predicate, choose_spec, exists_cfc_of_predicate
-/
lemma cfcₙHom_map_quasispectrum (f : C(σₙ R a, R)₀) :
    σₙ R (cfcₙHom ha f) = Set.range f :=
  (NonUnitalContinuousFunctionalCalculus.exists_cfc_of_predicate a ha).choose_spec.2.2.2.1 f

/--
lemma `cfcₙHom_predicate` / 引理 `cfcₙHom_predicate`

English:
lemma cfcₙHom_predicate
  given: (f : C(σₙ R a, R)₀)
  proof: (NonUnitalContinuousFunctionalCalculus.exists_cfc_of_predicate a ha).choose_spec.2.2.2.2 f

中文:
引理 cfcₙHom_predicate
  条件: (f : C(σₙ R a, R)₀)
  证明: (NonUnitalContinuousFunctionalCalculus.exists_cfc_of_predicate a ha).choose_spec.2.2.2.2 f

Depends on / 依赖: NonUnitalContinuousFunctionalCalculus, NonUnitalContinuousFunctionalCalculus.exists_cfc_of_predicate, choose_spec, exists_cfc_of_predicate
-/
lemma cfcₙHom_predicate (f : C(σₙ R a, R)₀) :
    p (cfcₙHom ha f) :=
  (NonUnitalContinuousFunctionalCalculus.exists_cfc_of_predicate a ha).choose_spec.2.2.2.2 f

open scoped NonUnitalContinuousFunctionalCalculus in
/--
lemma `cfcₙHom_eq_of_continuous_of_map_id` / 引理 `cfcₙHom_eq_of_continuous_of_map_id`

English:
lemma cfcₙHom_eq_of_continuous_of_map_id
  statement: [UniqueHom R A]
  proof: (cfcₙHom ha).ext_continuousMap a φ (cfcₙHom_continuous ha) hφ₁ by
    rw [cfcₙHom_id ha]; rw [hφ₂]

中文:
引理 cfcₙHom_eq_of_continuous_of_map_id
  结论: [唯一态射 R A]
  证明: (cfcₙHom ha).ext_continuousMap a φ (cfcₙHom_continuous ha) hφ₁ by
    rw [cfcₙHom_id ha]; rw [hφ₂]

Depends on / 依赖: ext_continuousMap
-/
lemma cfcₙHom_eq_of_continuous_of_map_id [UniqueHom R A]
    (φ : C(σₙ R a, R)₀ ->⋆ₙₐ[R] A) (hφ₁ : Continuous φ) (hφ₂ : φ (.id (σₙ R a)) = a) :
    cfcₙHom ha = φ :=
(cfcₙHom ha).ext_continuousMap a φ (cfcₙHom_continuous ha) hφ₁ by
    rw [cfcₙHom_id ha]; rw [hφ₂]

set_option backward.isDefEq.respectTransparency false in
/--
theorem `cfcₙHom_comp` / 定理 `cfcₙHom_comp`

English:
theorem cfcₙHom_comp
  statement: [UniqueHom R A] (f : C(σₙ R a, R)₀)
  proof: by
  let ψ : C(σₙ R (cfcₙHom ha f), R)₀ ->⋆ₙₐ[R] C(σₙ R a, R)₀ :=
    { toFun := (ContinuousMapZero.comp · f')
      map_smul' := fun _ _ => rfl
      map_add' := fun _ _ => rfl
      map_mul' := fun _ _ => rfl
      map_zero' := rfl
      map_star' := fun _ => rfl }
  let φ : C(σₙ R (cfcₙHom ha f),

中文:
定理 cfcₙHom_comp
  结论: [唯一态射 R A] (f : C(σₙ R a, R)₀)
  证明: by
  let ψ : C(σₙ R (cfcₙHom ha f), R)₀ ->⋆ₙₐ[R] C(σₙ R a, R)₀ :=
    { toFun := (ContinuousMapZero.comp · f')
      map_smul' := fun _ _ => rfl
      map_add' := fun _ _ => rfl
      map_mul' := fun _ _ => rfl
      map_zero' := rfl
      map_star' := fun _ => rfl }
  let φ : C(σₙ R (cfcₙHom ha f),

Depends on / 依赖: ContinuousMapZero, ContinuousMapZero.comp, DFunLike, DFunLike.congr_fun, congr_fun, map_add, map_mul, map_smul, map_star, map_zero, this.symm
-/
theorem cfcₙHom_comp [UniqueHom R A] (f : C(σₙ R a, R)₀)
    (f' : C(σₙ R a, σₙ R (cfcₙHom ha f))₀)
    (hff' : forall x, f x = f' x) (g : C(σₙ R (cfcₙHom ha f), R)₀) :
    cfcₙHom ha (g.comp f') = cfcₙHom (cfcₙHom_predicate ha f) g := by
  let ψ : C(σₙ R (cfcₙHom ha f), R)₀ ->⋆ₙₐ[R] C(σₙ R a, R)₀ :=
    { toFun := (ContinuousMapZero.comp · f')
      map_smul' := fun _ _ => rfl
      map_add' := fun _ _ => rfl
      map_mul' := fun _ _ => rfl
      map_zero' := rfl
      map_star' := fun _ => rfl }
  let φ : C(σₙ R (cfcₙHom ha f), R)₀ ->⋆ₙₐ[R] A := (cfcₙHom ha).comp ψ
  suffices cfcₙHom (cfcₙHom_predicate ha f) = φ from DFunLike.congr_fun this.symm g
  refine cfcₙHom_eq_of_continuous_of_map_id (cfcₙHom_predicate ha f) φ ?_ ?_
· refine (cfcₙHom_continuous ha).comp continuous_induced_rng.mpr ?_
    exact f'.toContinuousMap.continuous_precomp.comp continuous_induced_dom
  · simp only [φ, ψ, NonUnitalStarAlgHom.comp_apply, NonUnitalStarAlgHom.coe_mk',
      NonUnitalAlgHom.coe_mk]
    congr
    ext x
    simp [hff']

end cfcₙHom

section cfcₙL

/-- `cfcₙHom` bundled as a continuous linear map. -/
@[simps apply]
/--
Definition of `cfcₙL` / `cfcₙL` 的定义

English:
definition cfcₙL
  signature: {a : A} (ha : p a)
  body: { cfcₙHom ha with
    toFun := cfcₙHom ha
    map_smul' := map_smul _ }

中文:
定义 cfcₙL
  签名: {a : A} (ha : p a)
  定义体: { cfcₙHom ha with
    toFun := cfcₙHom ha
    map_smul' := map_smul _ }

Depends on / 依赖: map_smul
-/
noncomputable def cfcₙL {a : A} (ha : p a) : C(σₙ R a, R)₀ ->L[R] A :=
  { cfcₙHom ha with
    toFun := cfcₙHom ha
    map_smul' := map_smul _ }

end cfcₙL

section CFCn

open scoped Classical in
/-- This is the *continuous functional calculus* of an element `a : A` in a non-unital algebra
applied to bare functions. When either `a` does not satisfy the predicate `p` (i.e., `a` is not
`IsStarNormal`, `IsSelfAdjoint`, or `0 ≤ a` when `R` is `ℂ`, `ℝ`, or `ℝ≥0`, respectively), or when
`f : R → R` is not continuous on the quasispectrum of `a` or `f 0 ≠ 0`, then `cfcₙ f a` returns the
junk value `0`.

This is the primary declaration intended for widespread use of the continuous functional calculus
for non-unital algebras, and all the API applies to this declaration. For more information, see the
module documentation for `Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Unital`. -/
noncomputable irreducible_def cfcₙ (f : R -> R) (a : A) : A :=
  if h : p a ∧ ContinuousOn f (σₙ R a) ∧ f 0 = 0
    then cfcₙHom h.1 ⟨⟨_, h.2.1.domRestrict⟩, h.2.2⟩
    else 0

variable (f g : R -> R) (a : A)
variable (hf : ContinuousOn f (σₙ R a) := by cfc_cont_tac) (hf0 : f 0 = 0 := by cfc_zero_tac)
variable (hg : ContinuousOn g (σₙ R a) := by cfc_cont_tac) (hg0 : g 0 = 0 := by cfc_zero_tac)
variable (ha : p a := by cfc_tac)

set_option backward.privateInPublic true in
/--
lemma `cfcₙ_apply` / 引理 `cfcₙ_apply`

English:
lemma cfcₙ_apply
  statement: cfcₙ f a = cfcₙHom (a := a) ha ⟨⟨_, hf.domRestrict⟩, hf0⟩
  proof: by
  rw [cfcₙ_def]; rw [dif_pos ⟨ha]; rw [hf]; rw [hf0⟩]

中文:
引理 cfcₙ_apply
  结论: cfcₙ f a = cfcₙHom (a := a) ha ⟨⟨_, hf.domRestrict⟩, hf0⟩
  证明: by
  rw [cfcₙ_def]; rw [dif_pos ⟨ha]; rw [hf]; rw [hf0⟩]

Depends on / 依赖: dif_pos, domRestrict, hf.domRestrict
-/
lemma cfcₙ_apply : cfcₙ f a = cfcₙHom (a := a) ha ⟨⟨_, hf.domRestrict⟩, hf0⟩ := by
  rw [cfcₙ_def]; rw [dif_pos ⟨ha]; rw [hf]; rw [hf0⟩]

/--
lemma `cfcₙ_apply_pi` / 引理 `cfcₙ_apply_pi`

English:
lemma cfcₙ_apply_pi
  statement: {ι : Type*} (f : ι -> R -> R) (a : A) (ha := by cfc_tac)
  proof: by
  ext i
  simp only [cfcₙ_apply (f i) a (hf i) (hf0 i)]

中文:
引理 cfcₙ_apply_pi
  结论: {ι : 类型} (f : ι -> R -> R) (a : A) (ha := by cfc_tac)
  证明: by
  ext i
  simp only [cfcₙ_apply (f i) a (hf i) (hf0 i)]

Depends on / 依赖: ContinuousOn, cfc_cont_tac, cfc_tac, cfc_zero_tac, domRestrict
-/
lemma cfcₙ_apply_pi {ι : Type*} (f : ι -> R -> R) (a : A) (ha := by cfc_tac)
    (hf : forall i, ContinuousOn (f i) (σₙ R a) := by cfc_cont_tac)
    (hf0 : forall i, f i 0 = 0 := by cfc_zero_tac) :
    (fun i => cfcₙ (f i) a) = (fun i => cfcₙHom (a := a) ha ⟨⟨_, (hf i).domRestrict⟩, hf0 i⟩) := by
  ext i
  simp only [cfcₙ_apply (f i) a (hf i) (hf0 i)]

/--
lemma `cfcₙ_apply_of_not_and_and` / 引理 `cfcₙ_apply_of_not_and_and`

English:
lemma cfcₙ_apply_of_not_and_and
  statement: {f : R -> R} (a : A)
  proof: by
  rw [cfcₙ_def]; rw [dif_neg ha]

中文:
引理 cfcₙ_apply_of_not_and_and
  结论: {f : R -> R} (a : A)
  证明: by
  rw [cfcₙ_def]; rw [dif_neg ha]

Depends on / 依赖: dif_neg
-/
lemma cfcₙ_apply_of_not_and_and {f : R -> R} (a : A)
    (ha : ¬ (p a ∧ ContinuousOn f (σₙ R a) ∧ f 0 = 0)) :
    cfcₙ f a = 0 := by
  rw [cfcₙ_def]; rw [dif_neg ha]

/--
lemma `cfcₙ_apply_of_not_predicate` / 引理 `cfcₙ_apply_of_not_predicate`

English:
lemma cfcₙ_apply_of_not_predicate
  given: {f : R -> R} (a : A) (ha : ¬ p a)
  proof: by
  rw [cfcₙ_def]; rw [dif_neg (not_and_of_not_left _ ha)]

中文:
引理 cfcₙ_apply_of_not_predicate
  条件: {f : R -> R} (a : A) (ha : ¬ p a)
  证明: by
  rw [cfcₙ_def]; rw [dif_neg (not_and_of_not_left _ ha)]

Depends on / 依赖: dif_neg, not_and_of_not_left
-/
lemma cfcₙ_apply_of_not_predicate {f : R -> R} (a : A) (ha : ¬ p a) :
    cfcₙ f a = 0 := by
  rw [cfcₙ_def]; rw [dif_neg (not_and_of_not_left _ ha)]

/--
lemma `cfcₙ_apply_of_not_continuousOn` / 引理 `cfcₙ_apply_of_not_continuousOn`

English:
lemma cfcₙ_apply_of_not_continuousOn
  given: {f : R -> R} (a : A) (hf : ¬ ContinuousOn f (σₙ R a))
  proof: by
  rw [cfcₙ_def]; rw [dif_neg (not_and_of_not_right _ (not_and_of_not_left _ hf))]

中文:
引理 cfcₙ_apply_of_not_continuousOn
  条件: {f : R -> R} (a : A) (hf : ¬ ContinuousOn f (σₙ R a))
  证明: by
  rw [cfcₙ_def]; rw [dif_neg (not_and_of_not_right _ (not_and_of_not_left _ hf))]

Depends on / 依赖: dif_neg, not_and_of_not_left, not_and_of_not_right
-/
lemma cfcₙ_apply_of_not_continuousOn {f : R -> R} (a : A) (hf : ¬ ContinuousOn f (σₙ R a)) :
    cfcₙ f a = 0 := by
  rw [cfcₙ_def]; rw [dif_neg (not_and_of_not_right _ (not_and_of_not_left _ hf))]

/--
lemma `cfcₙ_apply_of_not_map_zero` / 引理 `cfcₙ_apply_of_not_map_zero`

English:
lemma cfcₙ_apply_of_not_map_zero
  given: {f : R -> R} (a : A) (hf : ¬ f 0 = 0)
  proof: by
  rw [cfcₙ_def]; rw [dif_neg (not_and_of_not_right _ (not_and_of_not_right _ hf))]

中文:
引理 cfcₙ_apply_of_not_map_zero
  条件: {f : R -> R} (a : A) (hf : ¬ f 0 = 0)
  证明: by
  rw [cfcₙ_def]; rw [dif_neg (not_and_of_not_right _ (not_and_of_not_right _ hf))]

Depends on / 依赖: dif_neg, not_and_of_not_right
-/
lemma cfcₙ_apply_of_not_map_zero {f : R -> R} (a : A) (hf : ¬ f 0 = 0) :
    cfcₙ f a = 0 := by
  rw [cfcₙ_def]; rw [dif_neg (not_and_of_not_right _ (not_and_of_not_right _ hf))]

set_option backward.isDefEq.respectTransparency false in
/--
lemma `cfcₙHom_eq_cfcₙ_extend` / 引理 `cfcₙHom_eq_cfcₙ_extend`

English:
lemma cfcₙHom_eq_cfcₙ_extend
  given: {a : A} (g : R -> R) (ha : p a) (f : C(σₙ R a, R)₀)
  proof: by
  have h : f = (σₙ R a).domRestrict (Function.extend Subtype.val f g) := by
    ext; simp
  have hg : ContinuousOn (Function.extend Subtype.val f g) (σₙ R a) :=
continuousOn_iff_continuous_domRestrict.mpr h ▸ map_continuous f
  have hg0 : (Function.extend Subtype.val f g) 0 = 0 := by
    rw [← qu

中文:
引理 cfcₙHom_eq_cfcₙ_extend
  条件: {a : A} (g : R -> R) (ha : p a) (f : C(σₙ R a, R)₀)
  证明: by
  have h : f = (σₙ R a).domRestrict (Function.extend Subtype.val f g) := by
    ext; simp
  have hg : ContinuousOn (Function.extend Subtype.val f g) (σₙ R a) :=
continuousOn_iff_continuous_domRestrict.mpr h ▸ map_continuous f
  have hg0 : (Function.extend Subtype.val f g) 0 = 0 := by
    rw [← qu

Depends on / 依赖: ContinuousOn, Function, Function.extend, Subtype, Subtype.val, Subtype.val_injective.extend_apply, coe_zero, continuousOn_iff_continuous_domRestrict, continuousOn_iff_continuous_domRestrict.mpr, domRestrict, extend, extend_apply, generalize, map_continuous, map_zero, quasispectrum, quasispectrum.coe_zero, val_injective
-/
lemma cfcₙHom_eq_cfcₙ_extend {a : A} (g : R -> R) (ha : p a) (f : C(σₙ R a, R)₀) :
    cfcₙHom ha f = cfcₙ (Function.extend Subtype.val f g) a := by
  have h : f = (σₙ R a).domRestrict (Function.extend Subtype.val f g) := by
    ext; simp
  have hg : ContinuousOn (Function.extend Subtype.val f g) (σₙ R a) :=
continuousOn_iff_continuous_domRestrict.mpr h ▸ map_continuous f
  have hg0 : (Function.extend Subtype.val f g) 0 = 0 := by
    rw [← quasispectrum.coe_zero (R := R) a]; rw [Subtype.val_injective.extend_apply]
    exact map_zero f
  generalize Function.extend Subtype.val f g = f' at *
  rw [cfcₙ_apply ..]
  congr!

/--
lemma `cfcₙ_eq_cfcₙL` / 引理 `cfcₙ_eq_cfcₙL`

English:
lemma cfcₙ_eq_cfcₙL
  given: {a : A} {f : R -> R} (ha : p a) (hf : ContinuousOn f (σₙ R a)) (hf0 : f 0 = 0)
  proof: by
  rw [cfcₙ_def]; rw [dif_pos ⟨ha]; rw [hf]; rw [hf0⟩]; rw [cfcₙL_apply]

中文:
引理 cfcₙ_eq_cfcₙL
  条件: {a : A} {f : R -> R} (ha : p a) (hf : ContinuousOn f (σₙ R a)) (hf0 : f 0 = 0)
  证明: by
  rw [cfcₙ_def]; rw [dif_pos ⟨ha]; rw [hf]; rw [hf0⟩]; rw [cfcₙL_apply]

Depends on / 依赖: dif_pos
-/
lemma cfcₙ_eq_cfcₙL {a : A} {f : R -> R} (ha : p a) (hf : ContinuousOn f (σₙ R a)) (hf0 : f 0 = 0) :
    cfcₙ f a = cfcₙL ha ⟨⟨_, hf.domRestrict⟩, hf0⟩ := by
  rw [cfcₙ_def]; rw [dif_pos ⟨ha]; rw [hf]; rw [hf0⟩]; rw [cfcₙL_apply]

set_option backward.privateInPublic true in
/--
lemma `cfcₙ_apply_mkD` / 引理 `cfcₙ_apply_mkD`

English:
lemma cfcₙ_apply_mkD
  proof: by
  by_cases f_cont : ContinuousOn f (quasispectrum R a)
  · by_cases f_zero : f 0 = 0
    · rw [cfcₙ_apply f a, mkD_of_continuousOn f_cont f_zero]
    · rw [cfcₙ_apply_of_not_map_zero a f_zero, mkD_of_not_zero, map_zero]
      exact f_zero
  · rw [cfcₙ_apply_of_not_continuousOn a f_cont, mkD_of_no

中文:
引理 cfcₙ_apply_mkD
  证明: by
  by_cases f_cont : ContinuousOn f (quasispectrum R a)
  · by_cases f_zero : f 0 = 0
    · rw [cfcₙ_apply f a, mkD_of_continuousOn f_cont f_zero]
    · rw [cfcₙ_apply_of_not_map_zero a f_zero, mkD_of_not_zero, map_zero]
      exact f_zero
  · rw [cfcₙ_apply_of_not_continuousOn a f_cont, mkD_of_no

Depends on / 依赖: ContinuousOn, domRestrict, f_cont, f_zero, map_zero, mkD_of_continuousOn, mkD_of_not_continuousOn, mkD_of_not_zero, quasispectrum
-/
lemma cfcₙ_apply_mkD :
    cfcₙ f a = cfcₙHom (a := a) ha (mkD ((quasispectrum R a).domRestrict f) 0) := by
  by_cases f_cont : ContinuousOn f (quasispectrum R a)
  · by_cases f_zero : f 0 = 0
    · rw [cfcₙ_apply f a, mkD_of_continuousOn f_cont f_zero]
    · rw [cfcₙ_apply_of_not_map_zero a f_zero, mkD_of_not_zero, map_zero]
      exact f_zero
  · rw [cfcₙ_apply_of_not_continuousOn a f_cont, mkD_of_not_continuousOn f_cont, map_zero]

set_option backward.privateInPublic true in
/--
lemma `cfcₙ_eq_cfcₙL_mkD` / 引理 `cfcₙ_eq_cfcₙL_mkD`

English:
lemma cfcₙ_eq_cfcₙL_mkD
  proof: cfcₙ_apply_mkD _ _

中文:
引理 cfcₙ_eq_cfcₙL_mkD
  证明: cfcₙ_apply_mkD _ _

Depends on / 依赖: domRestrict, quasispectrum
-/
lemma cfcₙ_eq_cfcₙL_mkD :
    cfcₙ f a = cfcₙL (a := a) ha (mkD ((quasispectrum R a).domRestrict f) 0) :=
  cfcₙ_apply_mkD _ _

/--
lemma `cfcₙ_cases` / 引理 `cfcₙ_cases`

English:
lemma cfcₙ_cases
  statement: (P : A -> Prop) (a : A) (f : R -> R) (h₀ : P 0)
  proof: by
  by_cases h : ContinuousOn f (σₙ R a) ∧ f 0 = 0 ∧ p a
  · rw [cfcₙ_apply f a h.1 h.2.1 h.2.2]
    exact haf h.1 h.2.1 h.2.2
  · simp only [not_and_or] at h
    obtain (h | h | h) := h
    · rwa [cfcₙ_apply_of_not_continuousOn _ h]
    · rwa [cfcₙ_apply_of_not_map_zero _ h]
    · rwa [cfcₙ_apply_

中文:
引理 cfcₙ_cases
  结论: (P : A -> 命题) (a : A) (f : R -> R) (h₀ : P 0)
  证明: by
  by_cases h : ContinuousOn f (σₙ R a) ∧ f 0 = 0 ∧ p a
  · rw [cfcₙ_apply f a h.1 h.2.1 h.2.2]
    exact haf h.1 h.2.1 h.2.2
  · simp only [not_and_or] at h
    obtain (h | h | h) := h
    · rwa [cfcₙ_apply_of_not_continuousOn _ h]
    · rwa [cfcₙ_apply_of_not_map_zero _ h]
    · rwa [cfcₙ_apply_

Depends on / 依赖: ContinuousOn, not_and_or
-/
lemma cfcₙ_cases (P : A -> Prop) (a : A) (f : R -> R) (h₀ : P 0)
    (haf : forall (hf : ContinuousOn f (σₙ R a)) h0 ha, P (cfcₙHom ha ⟨⟨_, hf.domRestrict⟩, h0⟩)) :
    P (cfcₙ f a) := by
  by_cases h : ContinuousOn f (σₙ R a) ∧ f 0 = 0 ∧ p a
  · rw [cfcₙ_apply f a h.1 h.2.1 h.2.2]
    exact haf h.1 h.2.1 h.2.2
  · simp only [not_and_or] at h
    obtain (h | h | h) := h
    · rwa [cfcₙ_apply_of_not_continuousOn _ h]
    · rwa [cfcₙ_apply_of_not_map_zero _ h]
    · rwa [cfcₙ_apply_of_not_predicate _ h]

/--
lemma `cfcₙ_commute_cfcₙ` / 引理 `cfcₙ_commute_cfcₙ`

English:
lemma cfcₙ_commute_cfcₙ
  given: (f g : R -> R) (a : A)
  statement: Commute (cfcₙ f a) (cfcₙ g a)
  proof: by
  refine cfcₙ_cases (fun x => Commute x (cfcₙ g a)) a f (by simp) fun hf hf0 ha => ?_
  refine cfcₙ_cases (fun x => Commute _ x) a g (by simp) fun hg hg0 _ => ?_
.map _ exact Commute.all _ _

中文:
引理 cfcₙ_commute_cfcₙ
  条件: (f g : R -> R) (a : A)
  结论: Commute (cfcₙ f a) (cfcₙ g a)
  证明: by
  refine cfcₙ_cases (fun x => Commute x (cfcₙ g a)) a f (by simp) fun hf hf0 ha => ?_
  refine cfcₙ_cases (fun x => Commute _ x) a g (by simp) fun hg hg0 _ => ?_
.map _ exact Commute.all _ _

Depends on / 依赖: Commute, Commute.all
-/
lemma cfcₙ_commute_cfcₙ (f g : R -> R) (a : A) : Commute (cfcₙ f a) (cfcₙ g a) := by
  refine cfcₙ_cases (fun x => Commute x (cfcₙ g a)) a f (by simp) fun hf hf0 ha => ?_
  refine cfcₙ_cases (fun x => Commute _ x) a g (by simp) fun hg hg0 _ => ?_
.map _ exact Commute.all _ _

set_option backward.privateInPublic true in
variable (R) in
include ha in
/--
lemma `cfcₙ_id` / 引理 `cfcₙ_id`

English:
lemma cfcₙ_id
  statement: cfcₙ (id : R -> R) a = a
  proof: cfcₙ_apply (id : R -> R) a ▸ cfcₙHom_id (p := p) ha

中文:
引理 cfcₙ_id
  结论: cfcₙ (id : R -> R) a = a
  证明: cfcₙ_apply (id : R -> R) a ▸ cfcₙHom_id (p := p) ha
-/
lemma cfcₙ_id : cfcₙ (id : R -> R) a = a :=
  cfcₙ_apply (id : R -> R) a ▸ cfcₙHom_id (p := p) ha

set_option backward.privateInPublic true in
variable (R) in
include ha in
/--
lemma `cfcₙ_id'` / 引理 `cfcₙ_id'`

English:
lemma cfcₙ_id'
  statement: cfcₙ (fun x : R => x) a = a
  proof: cfcₙ_id R a

中文:
引理 cfcₙ_id'
  结论: cfcₙ (fun x : R => x) a = a
  证明: cfcₙ_id R a
-/
lemma cfcₙ_id' : cfcₙ (fun x : R => x) a = a := cfcₙ_id R a

set_option backward.isDefEq.respectTransparency false in
set_option backward.privateInPublic true in
include ha hf hf0 in
/--
lemma `cfcₙ_map_quasispectrum` / 引理 `cfcₙ_map_quasispectrum`

English:
lemma cfcₙ_map_quasispectrum
  statement: σₙ R (cfcₙ f a) = f '' σₙ R a
  proof: by
  simp [cfcₙ_apply f a, cfcₙHom_map_quasispectrum (p := p)]

中文:
引理 cfcₙ_map_quasispectrum
  结论: σₙ R (cfcₙ f a) = f '' σₙ R a
  证明: by
  simp [cfcₙ_apply f a, cfcₙHom_map_quasispectrum (p := p)]
-/
lemma cfcₙ_map_quasispectrum : σₙ R (cfcₙ f a) = f '' σₙ R a := by
  simp [cfcₙ_apply f a, cfcₙHom_map_quasispectrum (p := p)]

variable (R) in
include R in
/--
lemma `cfcₙ_predicate_zero` / 引理 `cfcₙ_predicate_zero`

English:
lemma cfcₙ_predicate_zero
  statement: p 0
  proof: NonUnitalContinuousFunctionalCalculus.predicate_zero (R := R)

中文:
引理 cfcₙ_predicate_zero
  结论: p 0
  证明: NonUnitalContinuousFunctionalCalculus.predicate_zero (R := R)

Depends on / 依赖: NonUnitalContinuousFunctionalCalculus, NonUnitalContinuousFunctionalCalculus.predicate_zero, predicate_zero
-/
lemma cfcₙ_predicate_zero : p 0 :=
  NonUnitalContinuousFunctionalCalculus.predicate_zero (R := R)

/--
lemma `cfcₙ_predicate` / 引理 `cfcₙ_predicate`

English:
lemma cfcₙ_predicate
  given: (f : R -> R) (a : A)
  statement: p (cfcₙ f a)
  proof: cfcₙ_cases p a f (cfcₙ_predicate_zero R) fun _ _ _ => cfcₙHom_predicate ..

中文:
引理 cfcₙ_predicate
  条件: (f : R -> R) (a : A)
  结论: p (cfcₙ f a)
  证明: cfcₙ_cases p a f (cfcₙ_predicate_zero R) fun _ _ _ => cfcₙHom_predicate ..
-/
lemma cfcₙ_predicate (f : R -> R) (a : A) : p (cfcₙ f a) :=
  cfcₙ_cases p a f (cfcₙ_predicate_zero R) fun _ _ _ => cfcₙHom_predicate ..

/--
lemma `cfcₙ_congr` / 引理 `cfcₙ_congr`

English:
lemma cfcₙ_congr
  given: {f g : R -> R} {a : A} (hfg : (σₙ R a).EqOn f g)
  proof: by
  by_cases h : p a ∧ ContinuousOn g (σₙ R a) ∧ g 0 = 0
  · rw [cfcₙ_apply f a (h.2.1.congr hfg) (hfg (quasispectrum.zero_mem R a) ▸ h.2.2) h.1,
      cfcₙ_apply g a h.2.1 h.2.2 h.1]
    congr 3
    exact Set.domRestrict_eq_iff.mpr hfg
  · simp only [not_and_or] at h
    obtain (ha | hg | h0) := h

中文:
引理 cfcₙ_congr
  条件: {f g : R -> R} {a : A} (hfg : (σₙ R a).EqOn f g)
  证明: by
  by_cases h : p a ∧ ContinuousOn g (σₙ R a) ∧ g 0 = 0
  · rw [cfcₙ_apply f a (h.2.1.congr hfg) (hfg (quasispectrum.zero_mem R a) ▸ h.2.2) h.1,
      cfcₙ_apply g a h.2.1 h.2.2 h.1]
    congr 3
    exact Set.domRestrict_eq_iff.mpr hfg
  · simp only [not_and_or] at h
    obtain (ha | hg | h0) := h

Depends on / 依赖: ContinuousOn, Set.domRestrict_eq_iff.mpr, domRestrict_eq_iff, hf.congr, hfg.symm, not_and_or, quasispectrum, quasispectrum.zero_mem, zero_mem
-/
lemma cfcₙ_congr {f g : R -> R} {a : A} (hfg : (σₙ R a).EqOn f g) :
    cfcₙ f a = cfcₙ g a := by
  by_cases h : p a ∧ ContinuousOn g (σₙ R a) ∧ g 0 = 0
  · rw [cfcₙ_apply f a (h.2.1.congr hfg) (hfg (quasispectrum.zero_mem R a) ▸ h.2.2) h.1,
      cfcₙ_apply g a h.2.1 h.2.2 h.1]
    congr 3
    exact Set.domRestrict_eq_iff.mpr hfg
  · simp only [not_and_or] at h
    obtain (ha | hg | h0) := h
    · simp [cfcₙ_apply_of_not_predicate a ha]
    · rw [cfcₙ_apply_of_not_continuousOn a hg, cfcₙ_apply_of_not_continuousOn]
      exact fun hf => hg (hf.congr hfg.symm)
    · rw [cfcₙ_apply_of_not_map_zero a h0, cfcₙ_apply_of_not_map_zero]
      exact fun hf => h0 (hfg (quasispectrum.zero_mem R a) ▸ hf)

/--
lemma `eqOn_of_cfcₙ_eq_cfcₙ` / 引理 `eqOn_of_cfcₙ_eq_cfcₙ`

English:
lemma eqOn_of_cfcₙ_eq_cfcₙ
  statement: {f g : R -> R} {a : A} (h : cfcₙ f a = cfcₙ g a) (ha : p a := by cfc_tac)
  proof: by
  rw [cfcₙ_apply f a]; rw [cfcₙ_apply g a] at h
  exact fun x hx => congr($(cfcₙHom_injective ha h) ⟨x, hx⟩)

中文:
引理 eqOn_of_cfcₙ_eq_cfcₙ
  结论: {f g : R -> R} {a : A} (h : cfcₙ f a = cfcₙ g a) (ha : p a := by cfc_tac)
  证明: by
  rw [cfcₙ_apply f a]; rw [cfcₙ_apply g a] at h
  exact fun x hx => congr($(cfcₙHom_injective ha h) ⟨x, hx⟩)

Depends on / 依赖: ContinuousOn, cfc_cont_tac, cfc_tac, cfc_zero_tac
-/
lemma eqOn_of_cfcₙ_eq_cfcₙ {f g : R -> R} {a : A} (h : cfcₙ f a = cfcₙ g a) (ha : p a := by cfc_tac)
    (hf : ContinuousOn f (σₙ R a) := by cfc_cont_tac) (hf0 : f 0 = 0 := by cfc_zero_tac)
    (hg : ContinuousOn g (σₙ R a) := by cfc_cont_tac) (hg0 : g 0 = 0 := by cfc_zero_tac) :
    (σₙ R a).EqOn f g := by
  rw [cfcₙ_apply f a]; rw [cfcₙ_apply g a] at h
  exact fun x hx => congr($(cfcₙHom_injective ha h) ⟨x, hx⟩)

/--
lemma `cfcₙ_eq_cfcₙ_iff_eqOn` / 引理 `cfcₙ_eq_cfcₙ_iff_eqOn`

English:
lemma cfcₙ_eq_cfcₙ_iff_eqOn
  statement: {f g : R -> R} {a : A} (ha : p a := by cfc_tac)
  proof: ⟨eqOn_of_cfcₙ_eq_cfcₙ, cfcₙ_congr⟩

中文:
引理 cfcₙ_eq_cfcₙ_iff_eqOn
  结论: {f g : R -> R} {a : A} (ha : p a := by cfc_tac)
  证明: ⟨eqOn_of_cfcₙ_eq_cfcₙ, cfcₙ_congr⟩

Depends on / 依赖: ContinuousOn, cfc_cont_tac, cfc_tac, cfc_zero_tac
-/
lemma cfcₙ_eq_cfcₙ_iff_eqOn {f g : R -> R} {a : A} (ha : p a := by cfc_tac)
    (hf : ContinuousOn f (σₙ R a) := by cfc_cont_tac) (hf0 : f 0 = 0 := by cfc_zero_tac)
    (hg : ContinuousOn g (σₙ R a) := by cfc_cont_tac) (hg0 : g 0 = 0 := by cfc_zero_tac) :
    cfcₙ f a = cfcₙ g a ↔ (σₙ R a).EqOn f g :=
  ⟨eqOn_of_cfcₙ_eq_cfcₙ, cfcₙ_congr⟩

variable (R)

@[simp]
/--
lemma `cfcₙ_zero` / 引理 `cfcₙ_zero`

English:
lemma cfcₙ_zero
  statement: cfcₙ (0 : R -> R) a = 0
  proof: by
  by_cases ha : p a
  · exact cfcₙ_apply (0 : R -> R) a ▸ map_zero (cfcₙHom ha)
  · rw [cfcₙ_apply_of_not_predicate a ha]

@[simp]

中文:
引理 cfcₙ_zero
  结论: cfcₙ (0 : R -> R) a = 0
  证明: by
  by_cases ha : p a
  · exact cfcₙ_apply (0 : R -> R) a ▸ map_zero (cfcₙHom ha)
  · rw [cfcₙ_apply_of_not_predicate a ha]

@[simp]

Depends on / 依赖: map_zero
-/
lemma cfcₙ_zero : cfcₙ (0 : R -> R) a = 0 := by
  by_cases ha : p a
  · exact cfcₙ_apply (0 : R -> R) a ▸ map_zero (cfcₙHom ha)
  · rw [cfcₙ_apply_of_not_predicate a ha]

@[simp]
/--
lemma `cfcₙ_const_zero` / 引理 `cfcₙ_const_zero`

English:
lemma cfcₙ_const_zero
  statement: cfcₙ (fun _ : R => 0) a = 0
  proof: cfcₙ_zero R a

中文:
引理 cfcₙ_const_zero
  结论: cfcₙ (fun _ : R => 0) a = 0
  证明: cfcₙ_zero R a
-/
lemma cfcₙ_const_zero : cfcₙ (fun _ : R => 0) a = 0 := cfcₙ_zero R a

variable {R}

set_option backward.privateInPublic true in
include hf hf0 hg hg0 in
/--
lemma `cfcₙ_mul` / 引理 `cfcₙ_mul`

English:
lemma cfcₙ_mul
  statement: cfcₙ (fun x => f x * g x) a = cfcₙ f a * cfcₙ g a
  proof: by
  by_cases ha : p a
  · rw [cfcₙ_apply f a, cfcₙ_apply g a, ← map_mul, cfcₙ_apply _ a]
    congr
  · simp [cfcₙ_apply_of_not_predicate a ha]

中文:
引理 cfcₙ_mul
  结论: cfcₙ (fun x => f x * g x) a = cfcₙ f a * cfcₙ g a
  证明: by
  by_cases ha : p a
  · rw [cfcₙ_apply f a, cfcₙ_apply g a, ← map_mul, cfcₙ_apply _ a]
    congr
  · simp [cfcₙ_apply_of_not_predicate a ha]

Depends on / 依赖: map_mul
-/
lemma cfcₙ_mul : cfcₙ (fun x => f x * g x) a = cfcₙ f a * cfcₙ g a := by
  by_cases ha : p a
  · rw [cfcₙ_apply f a, cfcₙ_apply g a, ← map_mul, cfcₙ_apply _ a]
    congr
  · simp [cfcₙ_apply_of_not_predicate a ha]

set_option backward.privateInPublic true in
include hf hf0 hg hg0 in
/--
lemma `cfcₙ_add` / 引理 `cfcₙ_add`

English:
lemma cfcₙ_add
  statement: cfcₙ (fun x => f x + g x) a = cfcₙ f a + cfcₙ g a
  proof: by
  by_cases ha : p a
  · rw [cfcₙ_apply f a, cfcₙ_apply g a, cfcₙ_apply _ a]
    simp_rw [← map_add]
    congr
  · simp [cfcₙ_apply_of_not_predicate a ha]

中文:
引理 cfcₙ_add
  结论: cfcₙ (fun x => f x + g x) a = cfcₙ f a + cfcₙ g a
  证明: by
  by_cases ha : p a
  · rw [cfcₙ_apply f a, cfcₙ_apply g a, cfcₙ_apply _ a]
    simp_rw [← map_add]
    congr
  · simp [cfcₙ_apply_of_not_predicate a ha]

Depends on / 依赖: map_add, simp_rw
-/
lemma cfcₙ_add : cfcₙ (fun x => f x + g x) a = cfcₙ f a + cfcₙ g a := by
  by_cases ha : p a
  · rw [cfcₙ_apply f a, cfcₙ_apply g a, cfcₙ_apply _ a]
    simp_rw [← map_add]
    congr
  · simp [cfcₙ_apply_of_not_predicate a ha]

set_option backward.isDefEq.respectTransparency false in
open Finset in
/--
lemma `cfcₙ_sum` / 引理 `cfcₙ_sum`

English:
lemma cfcₙ_sum
  statement: {ι : Type*} (f : ι -> R -> R) (a : A) (s : Finset ι)
  proof: by
  by_cases ha : p a
  · have hsum : s.sum f = fun z => ∑ i in s, f i z := by ext; simp
    have hf' : ContinuousOn (∑ i : s, f i) (σₙ R a) := by
      rw [sum_coe_sort s]; rw [hsum]
      exact continuousOn_finsetSum s fun i hi => hf i hi
    rw [← sum_coe_sort s]; rw [← sum_coe_sort s]
    rw [c

中文:
引理 cfcₙ_sum
  结论: {ι : 类型} (f : ι -> R -> R) (a : A) (s : 有限集 ι)
  证明: by
  by_cases ha : p a
  · have hsum : s.sum f = fun z => ∑ i in s, f i z := by ext; simp
    have hf' : ContinuousOn (∑ i : s, f i) (σₙ R a) := by
      rw [sum_coe_sort s]; rw [hsum]
      exact continuousOn_finsetSum s fun i hi => hf i hi
    rw [← sum_coe_sort s]; rw [← sum_coe_sort s]
    rw [c

Depends on / 依赖: ContinuousOn, cfc_cont_tac, cfc_zero_tac, continuousOn_finsetSum, map_sum, s.sum, sum_coe_sort
-/
lemma cfcₙ_sum {ι : Type*} (f : ι -> R -> R) (a : A) (s : Finset ι)
    (hf : forall i in s, ContinuousOn (f i) (σₙ R a) := by cfc_cont_tac)
    (hf0 : forall i in s, f i 0 = 0 := by cfc_zero_tac) :
    cfcₙ (∑ i in s, f i) a = ∑ i in s, cfcₙ (f i) a := by
  by_cases ha : p a
  · have hsum : s.sum f = fun z => ∑ i in s, f i z := by ext; simp
    have hf' : ContinuousOn (∑ i : s, f i) (σₙ R a) := by
      rw [sum_coe_sort s]; rw [hsum]
      exact continuousOn_finsetSum s fun i hi => hf i hi
    rw [← sum_coe_sort s]; rw [← sum_coe_sort s]
    rw [cfcₙ_apply_pi _ a ha (fun ⟨i]; rw [hi⟩ => hf i hi)]; rw [← map_sum]; rw [cfcₙ_apply _ a hf']
    congr 1
    ext
    simp
  · simp [cfcₙ_apply_of_not_predicate a ha]

open Finset in
/--
lemma `cfcₙ_sum_univ` / 引理 `cfcₙ_sum_univ`

English:
lemma cfcₙ_sum_univ
  statement: {ι : Type*} [Fintype ι] (f : ι -> R -> R) (a : A)
  proof: cfcₙ_sum f a _ (fun i _ => hf i) (fun i _ => hf0 i)

中文:
引理 cfcₙ_sum_univ
  结论: {ι : 类型} [有限类型 ι] (f : ι -> R -> R) (a : A)
  证明: cfcₙ_sum f a _ (fun i _ => hf i) (fun i _ => hf0 i)

Depends on / 依赖: cfc_cont_tac, cfc_zero_tac
-/
lemma cfcₙ_sum_univ {ι : Type*} [Fintype ι] (f : ι -> R -> R) (a : A)
    (hf : forall i, ContinuousOn (f i) (σₙ R a) := by cfc_cont_tac)
    (hf0 : forall i, f i 0 = 0 := by cfc_zero_tac) :
    cfcₙ (∑ i, f i) a = ∑ i, cfcₙ (f i) a :=
  cfcₙ_sum f a _ (fun i _ => hf i) (fun i _ => hf0 i)

/--
lemma `cfcₙ_smul` / 引理 `cfcₙ_smul`

English:
lemma cfcₙ_smul
  statement: {S : Type*} [SMulZeroClass S R] [ContinuousConstSMul S R]
  proof: by
  by_cases ha : p a
  · rw [cfcₙ_apply f a, cfcₙ_apply _ a]
    simp_rw [← Pi.smul_def, ← smul_one_smul R s _]
    rw [← map_smul]
    congr
  · simp [cfcₙ_apply_of_not_predicate a ha]

中文:
引理 cfcₙ_smul
  结论: {S : 类型} [SMulZero类 S R] [连续常数标量乘法 S R]
  证明: by
  by_cases ha : p a
  · rw [cfcₙ_apply f a, cfcₙ_apply _ a]
    simp_rw [← Pi.smul_def, ← smul_one_smul R s _]
    rw [← map_smul]
    congr
  · simp [cfcₙ_apply_of_not_predicate a ha]

Depends on / 依赖: Pi.smul_def, cfc_cont_tac, cfc_zero_tac, map_smul, simp_rw, smul_def, smul_one_smul
-/
lemma cfcₙ_smul {S : Type*} [SMulZeroClass S R] [ContinuousConstSMul S R]
    [SMulZeroClass S A] [IsScalarTower S R A] [IsScalarTower S R (R -> R)]
    (s : S) (f : R -> R) (a : A) (hf : ContinuousOn f (σₙ R a) := by cfc_cont_tac)
    (h0 : f 0 = 0 := by cfc_zero_tac) :
    cfcₙ (fun x => s • f x) a = s • cfcₙ f a := by
  by_cases ha : p a
  · rw [cfcₙ_apply f a, cfcₙ_apply _ a]
    simp_rw [← Pi.smul_def, ← smul_one_smul R s _]
    rw [← map_smul]
    congr
  · simp [cfcₙ_apply_of_not_predicate a ha]

/--
lemma `cfcₙ_const_mul` / 引理 `cfcₙ_const_mul`

English:
lemma cfcₙ_const_mul
  statement: (r : R) (f : R -> R) (a : A) (hf : ContinuousOn f (σₙ R a) := by cfc_cont_tac)
  proof: cfcₙ_smul r f a

中文:
引理 cfcₙ_const_mul
  结论: (r : R) (f : R -> R) (a : A) (hf : ContinuousOn f (σₙ R a) := by cfc_cont_tac)
  证明: cfcₙ_smul r f a

Depends on / 依赖: cfc_cont_tac, cfc_zero_tac
-/
lemma cfcₙ_const_mul (r : R) (f : R -> R) (a : A) (hf : ContinuousOn f (σₙ R a) := by cfc_cont_tac)
    (h0 : f 0 = 0 := by cfc_zero_tac) :
    cfcₙ (fun x => r * f x) a = r • cfcₙ f a :=
  cfcₙ_smul r f a

/--
lemma `cfcₙ_star` / 引理 `cfcₙ_star`

English:
lemma cfcₙ_star
  statement: cfcₙ (fun x => star (f x)) a = star (cfcₙ f a)
  proof: by
  by_cases h : p a ∧ ContinuousOn f (σₙ R a) ∧ f 0 = 0
  · obtain ⟨ha, hf, h0⟩ := h
    rw [cfcₙ_apply f a]; rw [← map_star]; rw [cfcₙ_apply _ a]
    congr
  · simp only [not_and_or] at h
    obtain (ha | hf | h0) := h
    · simp [cfcₙ_apply_of_not_predicate a ha]
    · rw [cfcₙ_apply_of_not_cont

中文:
引理 cfcₙ_star
  结论: cfcₙ (fun x => star (f x)) a = star (cfcₙ f a)
  证明: by
  by_cases h : p a ∧ ContinuousOn f (σₙ R a) ∧ f 0 = 0
  · obtain ⟨ha, hf, h0⟩ := h
    rw [cfcₙ_apply f a]; rw [← map_star]; rw [cfcₙ_apply _ a]
    congr
  · simp only [not_and_or] at h
    obtain (ha | hf | h0) := h
    · simp [cfcₙ_apply_of_not_predicate a ha]
    · rw [cfcₙ_apply_of_not_cont

Depends on / 依赖: ContinuousOn, hf_star, hf_star.star, map_star, not_and_or, star_zero
-/
lemma cfcₙ_star : cfcₙ (fun x => star (f x)) a = star (cfcₙ f a) := by
  by_cases h : p a ∧ ContinuousOn f (σₙ R a) ∧ f 0 = 0
  · obtain ⟨ha, hf, h0⟩ := h
    rw [cfcₙ_apply f a]; rw [← map_star]; rw [cfcₙ_apply _ a]
    congr
  · simp only [not_and_or] at h
    obtain (ha | hf | h0) := h
    · simp [cfcₙ_apply_of_not_predicate a ha]
    · rw [cfcₙ_apply_of_not_continuousOn a hf, cfcₙ_apply_of_not_continuousOn, star_zero]
exact fun hf_star => hf by simpa using hf_star.star
    · rw [cfcₙ_apply_of_not_map_zero a h0, cfcₙ_apply_of_not_map_zero, star_zero]
exact fun hf0 => h0 by simpa using congr(star $(hf0))

/--
lemma `cfcₙ_smul_id` / 引理 `cfcₙ_smul_id`

English:
lemma cfcₙ_smul_id
  statement: {S : Type*} [SMulZeroClass S R] [ContinuousConstSMul S R]
  proof: by
  rw [cfcₙ_smul s _ a]; rw [cfcₙ_id' R a]

中文:
引理 cfcₙ_smul_id
  结论: {S : 类型} [SMulZero类 S R] [连续常数标量乘法 S R]
  证明: by
  rw [cfcₙ_smul s _ a]; rw [cfcₙ_id' R a]

Depends on / 依赖: cfc_tac
-/
lemma cfcₙ_smul_id {S : Type*} [SMulZeroClass S R] [ContinuousConstSMul S R]
    [SMulZeroClass S A] [IsScalarTower S R A] [IsScalarTower S R (R -> R)]
    (s : S) (a : A) (ha : p a := by cfc_tac) : cfcₙ (s • · : R -> R) a = s • a := by
  rw [cfcₙ_smul s _ a]; rw [cfcₙ_id' R a]

/--
lemma `cfcₙ_const_mul_id` / 引理 `cfcₙ_const_mul_id`

English:
lemma cfcₙ_const_mul_id
  given: (r : R) (a : A) (ha : p a := by cfc_tac)
  statement: cfcₙ (r * ·) a = r • a
  proof: cfcₙ_smul_id r a

中文:
引理 cfcₙ_const_mul_id
  条件: (r : R) (a : A) (ha : p a := by cfc_tac)
  结论: cfcₙ (r * ·) a = r • a
  证明: cfcₙ_smul_id r a

Depends on / 依赖: cfc_tac
-/
lemma cfcₙ_const_mul_id (r : R) (a : A) (ha : p a := by cfc_tac) : cfcₙ (r * ·) a = r • a :=
  cfcₙ_smul_id r a

set_option backward.privateInPublic true in
include ha in
/--
lemma `cfcₙ_star_id` / 引理 `cfcₙ_star_id`

English:
lemma cfcₙ_star_id
  statement: cfcₙ (star · : R -> R) a = star a
  proof: by
  rw [cfcₙ_star _ a]; rw [cfcₙ_id' R a]

中文:
引理 cfcₙ_star_id
  结论: cfcₙ (star · : R -> R) a = star a
  证明: by
  rw [cfcₙ_star _ a]; rw [cfcₙ_id' R a]
-/
lemma cfcₙ_star_id : cfcₙ (star · : R -> R) a = star a := by
  rw [cfcₙ_star _ a]; rw [cfcₙ_id' R a]

variable (R) in
/--
theorem `range_cfcₙ_eq_range_cfcₙHom` / 定理 `range_cfcₙ_eq_range_cfcₙHom`

English:
theorem range_cfcₙ_eq_range_cfcₙHom
  given: {a : A} (ha : p a)
  proof: by
  ext
  constructor
  all_goals rintro ⟨f, rfl⟩
  · exact cfcₙ_cases _ a f (zero_mem _) fun hf hf₀ ha => ⟨_, rfl⟩
.symm⟩ · exact ⟨Subtype.val.extend f 0, cfcₙHom_eq_cfcₙ_extend _ ha _

中文:
定理 range_cfcₙ_eq_range_cfcₙHom
  条件: {a : A} (ha : p a)
  证明: by
  ext
  constructor
  all_goals rintro ⟨f, rfl⟩
  · exact cfcₙ_cases _ a f (zero_mem _) fun hf hf₀ ha => ⟨_, rfl⟩
.symm⟩ · exact ⟨Subtype.val.extend f 0, cfcₙHom_eq_cfcₙ_extend _ ha _

Depends on / 依赖: NonUnitalStarAlgHom, NonUnitalStarAlgHom.range, Subtype, Subtype.val.extend, all_goals, extend, zero_mem
-/
theorem range_cfcₙ_eq_range_cfcₙHom {a : A} (ha : p a) :
    Set.range (cfcₙ (R := R) · a) = NonUnitalStarAlgHom.range (cfcₙHom ha (R := R)) := by
  ext
  constructor
  all_goals rintro ⟨f, rfl⟩
  · exact cfcₙ_cases _ a f (zero_mem _) fun hf hf₀ ha => ⟨_, rfl⟩
.symm⟩ · exact ⟨Subtype.val.extend f 0, cfcₙHom_eq_cfcₙ_extend _ ha _

section Comp

variable [UniqueHom R A]

set_option backward.isDefEq.respectTransparency false in
/--
lemma `cfcₙ_comp` / 引理 `cfcₙ_comp`

English:
lemma cfcₙ_comp
  statement: (g f : R -> R) (a : A)
  proof: by
have := hg.comp hf (σₙ R a).mapsTo_image f
  have sp_eq :
      σₙ R (cfcₙHom (show p a from ha) ⟨ContinuousMap.mk _ hf.domRestrict, hf0⟩) =
        f '' (σₙ R a) := by
    rw [cfcₙHom_map_quasispectrum (by exact ha) _]
    ext
    simp
  rw [cfcₙ_apply ..]; rw [cfcₙ_apply f a]; rw [cfcₙ_apply _ 

中文:
引理 cfcₙ_comp
  结论: (g f : R -> R) (a : A)
  证明: by
have := hg.comp hf (σₙ R a).mapsTo_image f
  have sp_eq :
      σₙ R (cfcₙHom (show p a from ha) ⟨ContinuousMap.mk _ hf.domRestrict, hf0⟩) =
        f '' (σₙ R a) := by
    rw [cfcₙHom_map_quasispectrum (by exact ha) _]
    ext
    simp
  rw [cfcₙ_apply ..]; rw [cfcₙ_apply f a]; rw [cfcₙ_apply _ 

Depends on / 依赖: ContinuousMap, ContinuousMap.mk, ContinuousOn, cfc_cont_tac, cfc_tac, cfc_zero_tac, convert, domRestrict, hf.domRestrict, hg.comp, mapsTo_image, sp_eq
-/
lemma cfcₙ_comp (g f : R -> R) (a : A)
    (hg : ContinuousOn g (f '' σₙ R a) := by cfc_cont_tac) (hg0 : g 0 = 0 := by cfc_zero_tac)
    (hf : ContinuousOn f (σₙ R a) := by cfc_cont_tac) (hf0 : f 0 = 0 := by cfc_zero_tac)
    (ha : p a := by cfc_tac) :
    cfcₙ (g ∘ f) a = cfcₙ g (cfcₙ f a) := by
have := hg.comp hf (σₙ R a).mapsTo_image f
  have sp_eq :
      σₙ R (cfcₙHom (show p a from ha) ⟨ContinuousMap.mk _ hf.domRestrict, hf0⟩) =
        f '' (σₙ R a) := by
    rw [cfcₙHom_map_quasispectrum (by exact ha) _]
    ext
    simp
  rw [cfcₙ_apply ..]; rw [cfcₙ_apply f a]; rw [cfcₙ_apply _ _ (by convert! hg) (ha := cfcₙHom_predicate (show p a from ha) _)]; rw [← cfcₙHom_comp _ _]
  swap
· exact ⟨.mk _ hf.domRestrict.codRestrict fun x => by rw [sp_eq]; use x.1; simp,
      Subtype.ext hf0⟩
  · congr
  · exact fun _ => rfl

/--
lemma `cfcₙ_comp'` / 引理 `cfcₙ_comp'`

English:
lemma cfcₙ_comp'
  statement: (g f : R -> R) (a : A)
  proof: cfcₙ_comp g f a

中文:
引理 cfcₙ_comp'
  结论: (g f : R -> R) (a : A)
  证明: cfcₙ_comp g f a

Depends on / 依赖: ContinuousOn, cfc_cont_tac, cfc_tac, cfc_zero_tac
-/
lemma cfcₙ_comp' (g f : R -> R) (a : A)
    (hg : ContinuousOn g (f '' σₙ R a) := by cfc_cont_tac) (hg0 : g 0 = 0 := by cfc_zero_tac)
    (hf : ContinuousOn f (σₙ R a) := by cfc_cont_tac) (hf0 : f 0 = 0 := by cfc_zero_tac)
    (ha : p a := by cfc_tac) :
    cfcₙ (g <| f ·) a = cfcₙ g (cfcₙ f a) :=
  cfcₙ_comp g f a

/--
lemma `cfcₙ_comp_smul` / 引理 `cfcₙ_comp_smul`

English:
lemma cfcₙ_comp_smul
  statement: {S : Type*} [SMulZeroClass S R] [ContinuousConstSMul S R]
  proof: by
  rw [cfcₙ_comp' f (s • ·) a]; rw [cfcₙ_smul_id s a]

中文:
引理 cfcₙ_comp_smul
  结论: {S : 类型} [SMulZero类 S R] [连续常数标量乘法 S R]
  证明: by
  rw [cfcₙ_comp' f (s • ·) a]; rw [cfcₙ_smul_id s a]

Depends on / 依赖: cfc_cont_tac, cfc_tac, cfc_zero_tac
-/
lemma cfcₙ_comp_smul {S : Type*} [SMulZeroClass S R] [ContinuousConstSMul S R]
    [SMulZeroClass S A] [IsScalarTower S R A] [IsScalarTower S R (R -> R)]
    (s : S) (f : R -> R) (a : A) (hf : ContinuousOn f ((s • ·) '' (σₙ R a)) := by cfc_cont_tac)
    (hf0 : f 0 = 0 := by cfc_zero_tac) (ha : p a := by cfc_tac) :
    cfcₙ (f <| s • ·) a = cfcₙ f (s • a) := by
  rw [cfcₙ_comp' f (s • ·) a]; rw [cfcₙ_smul_id s a]

/--
lemma `cfcₙ_comp_const_mul` / 引理 `cfcₙ_comp_const_mul`

English:
lemma cfcₙ_comp_const_mul
  statement: (r : R) (f : R -> R) (a : A)
  proof: by
  rw [cfcₙ_comp' f (r * ·) a]; rw [cfcₙ_const_mul_id r a]

中文:
引理 cfcₙ_comp_const_mul
  结论: (r : R) (f : R -> R) (a : A)
  证明: by
  rw [cfcₙ_comp' f (r * ·) a]; rw [cfcₙ_const_mul_id r a]

Depends on / 依赖: cfc_cont_tac, cfc_tac, cfc_zero_tac
-/
lemma cfcₙ_comp_const_mul (r : R) (f : R -> R) (a : A)
    (hf : ContinuousOn f ((r * ·) '' (σₙ R a)) := by cfc_cont_tac)
    (hf0 : f 0 = 0 := by cfc_zero_tac) (ha : p a := by cfc_tac) :
    cfcₙ (f <| r * ·) a = cfcₙ f (r • a) := by
  rw [cfcₙ_comp' f (r * ·) a]; rw [cfcₙ_const_mul_id r a]

/--
lemma `cfcₙ_comp_star` / 引理 `cfcₙ_comp_star`

English:
lemma cfcₙ_comp_star
  statement: (hf : ContinuousOn f (star '' (σₙ R a)) := by cfc_cont_tac)
  proof: by
  rw [cfcₙ_comp' f star a]; rw [cfcₙ_star_id a]

中文:
引理 cfcₙ_comp_star
  结论: (hf : ContinuousOn f (star '' (σₙ R a)) := by cfc_cont_tac)
  证明: by
  rw [cfcₙ_comp' f star a]; rw [cfcₙ_star_id a]

Depends on / 依赖: cfc_cont_tac, cfc_tac, cfc_zero_tac
-/
lemma cfcₙ_comp_star (hf : ContinuousOn f (star '' (σₙ R a)) := by cfc_cont_tac)
    (hf0 : f 0 = 0 := by cfc_zero_tac) (ha : p a := by cfc_tac) :
    cfcₙ (f <| star ·) a = cfcₙ f (star a) := by
  rw [cfcₙ_comp' f star a]; rw [cfcₙ_star_id a]

end Comp

/--
lemma `CFC.eq_zero_of_quasispectrum_eq_zero` / 引理 `CFC.eq_zero_of_quasispectrum_eq_zero`

English:
lemma CFC.eq_zero_of_quasispectrum_eq_zero
  given: (h_spec : σₙ R a subseteq {0}) (ha : p a := by cfc_tac)
  proof: by
  simpa [cfcₙ_id R a] using cfcₙ_congr (a := a) (f := id) (g := fun _ : R => 0) fun x => by simp_all

include instCFCₙ in

中文:
引理 CFC.eq_zero_of_quasispectrum_eq_zero
  条件: (h_spec : σₙ R a subseteq {0}) (ha : p a := by cfc_tac)
  证明: by
  simpa [cfcₙ_id R a] using cfcₙ_congr (a := a) (f := id) (g := fun _ : R => 0) fun x => by simp_all

include instCFCₙ in

Depends on / 依赖: cfc_tac
-/
lemma CFC.eq_zero_of_quasispectrum_eq_zero (h_spec : σₙ R a subseteq {0}) (ha : p a := by cfc_tac) :
    a = 0 := by
  simpa [cfcₙ_id R a] using cfcₙ_congr (a := a) (f := id) (g := fun _ : R => 0) fun x => by simp_all

include instCFCₙ in
/--
lemma `CFC.quasispectrum_zero_eq` / 引理 `CFC.quasispectrum_zero_eq`

English:
lemma CFC.quasispectrum_zero_eq
  statement: σₙ R (0 : A) = {0}
  proof: by
  refine Set.eq_singleton_iff_unique_mem.mpr ⟨quasispectrum.zero_mem R 0, fun x hx => ?_⟩
  rw [← cfcₙ_zero R (0 : A)]; rw [cfcₙ_map_quasispectrum _ _ (by cfc_cont_tac) (by cfc_zero_tac) (cfcₙ_predicate_zero R)] at hx
  simp_all

中文:
引理 CFC.quasispectrum_zero_eq
  结论: σₙ R (0 : A) = {0}
  证明: by
  refine Set.eq_singleton_iff_unique_mem.mpr ⟨quasispectrum.zero_mem R 0, fun x hx => ?_⟩
  rw [← cfcₙ_zero R (0 : A)]; rw [cfcₙ_map_quasispectrum _ _ (by cfc_cont_tac) (by cfc_zero_tac) (cfcₙ_predicate_zero R)] at hx
  simp_all

Depends on / 依赖: Set.eq_singleton_iff_unique_mem.mpr, cfc_cont_tac, cfc_zero_tac, eq_singleton_iff_unique_mem, quasispectrum, quasispectrum.zero_mem, zero_mem
-/
lemma CFC.quasispectrum_zero_eq : σₙ R (0 : A) = {0} := by
  refine Set.eq_singleton_iff_unique_mem.mpr ⟨quasispectrum.zero_mem R 0, fun x hx => ?_⟩
  rw [← cfcₙ_zero R (0 : A)]; rw [cfcₙ_map_quasispectrum _ _ (by cfc_cont_tac) (by cfc_zero_tac) (cfcₙ_predicate_zero R)] at hx
  simp_all

/--
lemma `cfcₙ_apply_zero` / 引理 `cfcₙ_apply_zero`

English:
lemma cfcₙ_apply_zero
  given: {f : R -> R}
  statement: cfcₙ f (0 : A) = 0
  proof: by
  by_cases hf0 : f 0 = 0
  · nth_rw 2 [← cfcₙ_zero R 0]
    apply cfcₙ_congr
    simpa [CFC.quasispectrum_zero_eq]
  · exact cfcₙ_apply_of_not_map_zero _ hf0

@[simp]

中文:
引理 cfcₙ_apply_zero
  条件: {f : R -> R}
  结论: cfcₙ f (0 : A) = 0
  证明: by
  by_cases hf0 : f 0 = 0
  · nth_rw 2 [← cfcₙ_zero R 0]
    apply cfcₙ_congr
    simpa [CFC.quasispectrum_zero_eq]
  · exact cfcₙ_apply_of_not_map_zero _ hf0

@[simp]
-/
@[simp] lemma cfcₙ_apply_zero {f : R -> R} : cfcₙ f (0 : A) = 0 := by
  by_cases hf0 : f 0 = 0
  · nth_rw 2 [← cfcₙ_zero R 0]
    apply cfcₙ_congr
    simpa [CFC.quasispectrum_zero_eq]
  · exact cfcₙ_apply_of_not_map_zero _ hf0

@[simp]
/--
Instance `IsStarNormal.cfcₙ_map` / 实例 `IsStarNormal.cfcₙ_map`

English:
instance IsStarNormal.cfcₙ_map
  signature: (f : R -> R) (a : A)
  body: by
    refine cfcₙ_cases (fun x => Commute (star x) x) _ _ (Commute.zero_right _) fun _ _ _ => ?_
    simp only [Commute, SemiconjBy]
    rw [← cfcₙ_apply f a]; rw [← cfcₙ_star]; rw [← cfcₙ_mul ..]; rw [← cfcₙ_mul ..]
    congr! 2
    exact mul_comm _ _

中文:
实例 是StarNormal.cfcₙ_map
  签名: (f : R -> R) (a : A)
  定义体: by
    refine cfcₙ_cases (fun x => Commute (star x) x) _ _ (Commute.zero_right _) fun _ _ _ => ?_
    simp only [Commute, SemiconjBy]
    rw [← cfcₙ_apply f a]; rw [← cfcₙ_star]; rw [← cfcₙ_mul ..]; rw [← cfcₙ_mul ..]
    congr! 2
    exact mul_comm _ _

Depends on / 依赖: Commute, Commute.zero_right, SemiconjBy, mul_comm, zero_right
-/
instance IsStarNormal.cfcₙ_map (f : R -> R) (a : A) : IsStarNormal (cfcₙ f a) where
  star_comm_self := by
    refine cfcₙ_cases (fun x => Commute (star x) x) _ _ (Commute.zero_right _) fun _ _ _ => ?_
    simp only [Commute, SemiconjBy]
    rw [← cfcₙ_apply f a]; rw [← cfcₙ_star]; rw [← cfcₙ_mul ..]; rw [← cfcₙ_mul ..]
    congr! 2
    exact mul_comm _ _

-- The following two lemmas are just `cfcₙ_predicate`, but specific enough for the `@[simp]` tag.
@[simp]
/--
lemma `IsSelfAdjoint.cfcₙ` / 引理 `IsSelfAdjoint.cfcₙ`

English:
lemma IsSelfAdjoint.cfcₙ
  proof: cfcₙ_predicate _ _

@[simp]

中文:
引理 IsSelfAdjoint.cfcₙ
  证明: cfcₙ_predicate _ _

@[simp]
-/
protected lemma IsSelfAdjoint.cfcₙ
    [NonUnitalContinuousFunctionalCalculus R A IsSelfAdjoint] {f : R -> R} {a : A} :
    IsSelfAdjoint (cfcₙ f a) :=
  cfcₙ_predicate _ _

@[simp]
/--
lemma `cfcₙ_nonneg_of_predicate` / 引理 `cfcₙ_nonneg_of_predicate`

English:
lemma cfcₙ_nonneg_of_predicate
  statement: [LE A]
  proof: cfcₙ_predicate _ _

中文:
引理 cfcₙ_nonneg_of_predicate
  结论: [LE A]
  证明: cfcₙ_predicate _ _
-/
lemma cfcₙ_nonneg_of_predicate [LE A]
    [NonUnitalContinuousFunctionalCalculus R A (0 <= ·)] {f : R -> R} {a : A} :
    0 <= cfcₙ f a :=
  cfcₙ_predicate _ _

end CFCn

end Main

section Neg

variable {R A : Type*} {p : A -> Prop} [CommRing R] [Nontrivial R] [StarRing R] [MetricSpace R]
variable [IsTopologicalRing R] [ContinuousStar R] [TopologicalSpace A] [NonUnitalRing A]
variable [StarRing A] [Module R A] [IsScalarTower R A A] [SMulCommClass R A A]
variable [NonUnitalContinuousFunctionalCalculus R A p]
variable (f g : R -> R) (a : A)
variable (hf : ContinuousOn f (σₙ R a) := by cfc_cont_tac) (hf0 : f 0 = 0 := by cfc_zero_tac)
variable (hg : ContinuousOn g (σₙ R a) := by cfc_cont_tac) (hg0 : g 0 = 0 := by cfc_zero_tac)

set_option backward.privateInPublic true in
include hf hf0 hg hg0 in
/--
lemma `cfcₙ_sub` / 引理 `cfcₙ_sub`

English:
lemma cfcₙ_sub
  statement: cfcₙ (fun x => f x - g x) a = cfcₙ f a - cfcₙ g a
  proof: by
  by_cases ha : p a
  · rw [cfcₙ_apply f a, cfcₙ_apply g a, ← map_sub, cfcₙ_apply ..]
    congr
  · simp [cfcₙ_apply_of_not_predicate a ha]

中文:
引理 cfcₙ_sub
  结论: cfcₙ (fun x => f x - g x) a = cfcₙ f a - cfcₙ g a
  证明: by
  by_cases ha : p a
  · rw [cfcₙ_apply f a, cfcₙ_apply g a, ← map_sub, cfcₙ_apply ..]
    congr
  · simp [cfcₙ_apply_of_not_predicate a ha]

Depends on / 依赖: map_sub
-/
lemma cfcₙ_sub : cfcₙ (fun x => f x - g x) a = cfcₙ f a - cfcₙ g a := by
  by_cases ha : p a
  · rw [cfcₙ_apply f a, cfcₙ_apply g a, ← map_sub, cfcₙ_apply ..]
    congr
  · simp [cfcₙ_apply_of_not_predicate a ha]

/--
lemma `cfcₙ_neg` / 引理 `cfcₙ_neg`

English:
lemma cfcₙ_neg
  statement: cfcₙ (fun x => -(f x)) a = -(cfcₙ f a)
  proof: by
  by_cases h : p a ∧ ContinuousOn f (σₙ R a) ∧ f 0 = 0
  · obtain ⟨ha, hf, h0⟩ := h
    rw [cfcₙ_apply f a]; rw [← map_neg]; rw [cfcₙ_apply ..]
    congr
  · simp only [not_and_or] at h
    obtain (ha | hf | h0) := h
    · simp [cfcₙ_apply_of_not_predicate a ha]
    · rw [cfcₙ_apply_of_not_contin

中文:
引理 cfcₙ_neg
  结论: cfcₙ (fun x => -(f x)) a = -(cfcₙ f a)
  证明: by
  by_cases h : p a ∧ ContinuousOn f (σₙ R a) ∧ f 0 = 0
  · obtain ⟨ha, hf, h0⟩ := h
    rw [cfcₙ_apply f a]; rw [← map_neg]; rw [cfcₙ_apply ..]
    congr
  · simp only [not_and_or] at h
    obtain (ha | hf | h0) := h
    · simp [cfcₙ_apply_of_not_predicate a ha]
    · rw [cfcₙ_apply_of_not_contin

Depends on / 依赖: ContinuousOn, fun_neg, hf_neg, hf_neg.fun_neg, map_neg, neg_eq_zero, neg_eq_zero.mp, neg_zero, not_and_or
-/
lemma cfcₙ_neg : cfcₙ (fun x => -(f x)) a = -(cfcₙ f a) := by
  by_cases h : p a ∧ ContinuousOn f (σₙ R a) ∧ f 0 = 0
  · obtain ⟨ha, hf, h0⟩ := h
    rw [cfcₙ_apply f a]; rw [← map_neg]; rw [cfcₙ_apply ..]
    congr
  · simp only [not_and_or] at h
    obtain (ha | hf | h0) := h
    · simp [cfcₙ_apply_of_not_predicate a ha]
    · rw [cfcₙ_apply_of_not_continuousOn a hf, cfcₙ_apply_of_not_continuousOn, neg_zero]
exact fun hf_neg => hf by simpa using hf_neg.fun_neg
    · rw [cfcₙ_apply_of_not_map_zero a h0, cfcₙ_apply_of_not_map_zero, neg_zero]
      exact (h0 <| neg_eq_zero.mp ·)

/--
lemma `cfcₙ_neg'` / 引理 `cfcₙ_neg'`

English:
lemma cfcₙ_neg'
  statement: cfcₙ (-f) = (-cfcₙ f : A -> A)
  proof: by ext1 a; exact (cfcₙ_neg f a)

中文:
引理 cfcₙ_neg'
  结论: cfcₙ (-f) = (-cfcₙ f : A -> A)
  证明: by ext1 a; exact (cfcₙ_neg f a)
-/
lemma cfcₙ_neg' : cfcₙ (-f) = (-cfcₙ f : A -> A) := by ext1 a; exact (cfcₙ_neg f a)

/--
lemma `cfcₙ_neg_id` / 引理 `cfcₙ_neg_id`

English:
lemma cfcₙ_neg_id
  given: (ha : p a := by cfc_tac)
  proof: by
  rw [cfcₙ_neg ..]; rw [cfcₙ_id' R a]

中文:
引理 cfcₙ_neg_id
  条件: (ha : p a := by cfc_tac)
  证明: by
  rw [cfcₙ_neg ..]; rw [cfcₙ_id' R a]

Depends on / 依赖: cfc_tac
-/
lemma cfcₙ_neg_id (ha : p a := by cfc_tac) :
    cfcₙ (- · : R -> R) a = -a := by
  rw [cfcₙ_neg ..]; rw [cfcₙ_id' R a]

variable [UniqueHom R A]

/--
lemma `cfcₙ_comp_neg` / 引理 `cfcₙ_comp_neg`

English:
lemma cfcₙ_comp_neg
  statement: (hf : ContinuousOn f ((-·) '' (σₙ R a)) := by cfc_cont_tac)
  proof: by
  rw [cfcₙ_comp' ..]; rw [cfcₙ_neg_id _]

中文:
引理 cfcₙ_comp_neg
  结论: (hf : ContinuousOn f ((-·) '' (σₙ R a)) := by cfc_cont_tac)
  证明: by
  rw [cfcₙ_comp' ..]; rw [cfcₙ_neg_id _]

Depends on / 依赖: cfc_cont_tac, cfc_tac, cfc_zero_tac
-/
lemma cfcₙ_comp_neg (hf : ContinuousOn f ((-·) '' (σₙ R a)) := by cfc_cont_tac)
    (h0 : f 0 = 0 := by cfc_zero_tac) (ha : p a := by cfc_tac) :
    cfcₙ (f <| - ·) a = cfcₙ f (-a) := by
  rw [cfcₙ_comp' ..]; rw [cfcₙ_neg_id _]

end Neg

section Order

section Semiring

variable {R A : Type*} {p : A -> Prop} [CommSemiring R] [PartialOrder R] [Nontrivial R]
variable [StarRing R] [MetricSpace R] [IsTopologicalSemiring R] [ContinuousStar R]
variable [ContinuousSqrt R] [StarOrderedRing R] [NoZeroDivisors R]
variable [TopologicalSpace A] [NonUnitalRing A] [StarRing A] [PartialOrder A] [StarOrderedRing A]
variable [Module R A] [IsScalarTower R A A] [SMulCommClass R A A]
variable [NonUnitalContinuousFunctionalCalculus R A p]

/--
lemma `cfcₙHom_mono` / 引理 `cfcₙHom_mono`

English:
lemma cfcₙHom_mono
  given: {a : A} (ha : p a) {f g : C(σₙ R a, R)₀} (hfg : f <= g)
  proof: OrderHomClass.mono (cfcₙHom ha) hfg

中文:
引理 cfcₙHom_mono
  条件: {a : A} (ha : p a) {f g : C(σₙ R a, R)₀} (hfg : f <= g)
  证明: OrderHomClass.mono (cfcₙHom ha) hfg

Depends on / 依赖: OrderHomClass, OrderHomClass.mono
-/
lemma cfcₙHom_mono {a : A} (ha : p a) {f g : C(σₙ R a, R)₀} (hfg : f <= g) :
    cfcₙHom ha f <= cfcₙHom ha g :=
  OrderHomClass.mono (cfcₙHom ha) hfg

/--
lemma `cfcₙHom_nonneg_iff` / 引理 `cfcₙHom_nonneg_iff`

English:
lemma cfcₙHom_nonneg_iff
  given: [NonnegSpectrumClass R A] {a : A} (ha : p a) {f : C(σₙ R a, R)₀}
  proof: by
  constructor
  · exact fun hf x =>
      (cfcₙHom_map_quasispectrum ha (R := R) _ ▸ quasispectrum_nonneg_of_nonneg (cfcₙHom ha f) hf)
      _ ⟨x, rfl⟩
  · simpa using (cfcₙHom_mono ha (f := 0) (g := f) ·)

中文:
引理 cfcₙHom_nonneg_iff
  条件: [NonnegSpectrum类 R A] {a : A} (ha : p a) {f : C(σₙ R a, R)₀}
  证明: by
  constructor
  · exact fun hf x =>
      (cfcₙHom_map_quasispectrum ha (R := R) _ ▸ quasispectrum_nonneg_of_nonneg (cfcₙHom ha f) hf)
      _ ⟨x, rfl⟩
  · simpa using (cfcₙHom_mono ha (f := 0) (g := f) ·)

Depends on / 依赖: quasispectrum_nonneg_of_nonneg
-/
lemma cfcₙHom_nonneg_iff [NonnegSpectrumClass R A] {a : A} (ha : p a) {f : C(σₙ R a, R)₀} :
    0 <= cfcₙHom ha f ↔ 0 <= f := by
  constructor
  · exact fun hf x =>
      (cfcₙHom_map_quasispectrum ha (R := R) _ ▸ quasispectrum_nonneg_of_nonneg (cfcₙHom ha f) hf)
      _ ⟨x, rfl⟩
  · simpa using (cfcₙHom_mono ha (f := 0) (g := f) ·)

/--
lemma `cfcₙ_mono` / 引理 `cfcₙ_mono`

English:
lemma cfcₙ_mono
  statement: {f g : R -> R} {a : A} (h : forall x in σₙ R a, f x <= g x)
  proof: by
  by_cases ha : p a
  · rw [cfcₙ_apply f a, cfcₙ_apply g a]
    exact cfcₙHom_mono ha fun x => h x.1 x.2
  · simp only [cfcₙ_apply_of_not_predicate _ ha, le_rfl]

中文:
引理 cfcₙ_mono
  结论: {f g : R -> R} {a : A} (h : 对任意 x in σₙ R a, f x <= g x)
  证明: by
  by_cases ha : p a
  · rw [cfcₙ_apply f a, cfcₙ_apply g a]
    exact cfcₙHom_mono ha fun x => h x.1 x.2
  · simp only [cfcₙ_apply_of_not_predicate _ ha, le_rfl]

Depends on / 依赖: ContinuousOn, cfc_cont_tac, cfc_zero_tac, le_rfl
-/
lemma cfcₙ_mono {f g : R -> R} {a : A} (h : forall x in σₙ R a, f x <= g x)
    (hf : ContinuousOn f (σₙ R a) := by cfc_cont_tac)
    (hg : ContinuousOn g (σₙ R a) := by cfc_cont_tac)
    (hf0 : f 0 = 0 := by cfc_zero_tac) (hg0 : g 0 = 0 := by cfc_zero_tac) :
    cfcₙ f a <= cfcₙ g a := by
  by_cases ha : p a
  · rw [cfcₙ_apply f a, cfcₙ_apply g a]
    exact cfcₙHom_mono ha fun x => h x.1 x.2
  · simp only [cfcₙ_apply_of_not_predicate _ ha, le_rfl]

/--
lemma `cfcₙ_nonneg_iff` / 引理 `cfcₙ_nonneg_iff`

English:
lemma cfcₙ_nonneg_iff
  statement: [NonnegSpectrumClass R A] (f : R -> R) (a : A)
  proof: by
  rw [cfcₙ_apply ..]; rw [cfcₙHom_nonneg_iff]; rw [ContinuousMapZero.le_def]
  simp only [Subtype.forall]
  congr!

中文:
引理 cfcₙ_nonneg_iff
  结论: [NonnegSpectrum类 R A] (f : R -> R) (a : A)
  证明: by
  rw [cfcₙ_apply ..]; rw [cfcₙHom_nonneg_iff]; rw [ContinuousMapZero.le_def]
  simp only [Subtype.forall]
  congr!

Depends on / 依赖: ContinuousMapZero, ContinuousMapZero.le_def, Subtype, Subtype.forall, cfc_cont_tac, cfc_tac, cfc_zero_tac, le_def
-/
lemma cfcₙ_nonneg_iff [NonnegSpectrumClass R A] (f : R -> R) (a : A)
    (hf : ContinuousOn f (σₙ R a) := by cfc_cont_tac)
    (h0 : f 0 = 0 := by cfc_zero_tac) (ha : p a := by cfc_tac) :
    0 <= cfcₙ f a ↔ forall x in σₙ R a, 0 <= f x := by
  rw [cfcₙ_apply ..]; rw [cfcₙHom_nonneg_iff]; rw [ContinuousMapZero.le_def]
  simp only [Subtype.forall]
  congr!

/--
lemma `StarOrderedRing.nonneg_iff_quasispectrum_nonneg` / 引理 `StarOrderedRing.nonneg_iff_quasispectrum_nonneg`

English:
lemma StarOrderedRing.nonneg_iff_quasispectrum_nonneg
  statement: [NonnegSpectrumClass R A] (a : A)
  proof: by
  have := cfcₙ_nonneg_iff (id : R -> R) a (by fun_prop)
  simpa [cfcₙ_id _ a ha] using this

中文:
引理 StarOrdered环.nonneg_iff_quasispectrum_nonneg
  结论: [NonnegSpectrum类 R A] (a : A)
  证明: by
  have := cfcₙ_nonneg_iff (id : R -> R) a (by fun_prop)
  simpa [cfcₙ_id _ a ha] using this

Depends on / 依赖: cfc_tac, fun_prop, quasispectrum
-/
lemma StarOrderedRing.nonneg_iff_quasispectrum_nonneg [NonnegSpectrumClass R A] (a : A)
    (ha : p a := by cfc_tac) : 0 <= a ↔ forall x in quasispectrum R a, 0 <= x := by
  have := cfcₙ_nonneg_iff (id : R -> R) a (by fun_prop)
  simpa [cfcₙ_id _ a ha] using this

/--
lemma `cfcₙ_nonneg` / 引理 `cfcₙ_nonneg`

English:
lemma cfcₙ_nonneg
  given: {f : R -> R} {a : A} (h : forall x in σₙ R a, 0 <= f x)
  proof: by
  by_cases hf : ContinuousOn f (σₙ R a) ∧ f 0 = 0
  · obtain ⟨h₁, h₂⟩ := hf
    simpa using cfcₙ_mono h
  · simp only [not_and_or] at hf
    obtain (hf | hf) := hf
    · simp only [cfcₙ_apply_of_not_continuousOn _ hf, le_rfl]
    · simp only [cfcₙ_apply_of_not_map_zero _ hf, le_rfl]

中文:
引理 cfcₙ_nonneg
  条件: {f : R -> R} {a : A} (h : 对任意 x in σₙ R a, 0 <= f x)
  证明: by
  by_cases hf : ContinuousOn f (σₙ R a) ∧ f 0 = 0
  · obtain ⟨h₁, h₂⟩ := hf
    simpa using cfcₙ_mono h
  · simp only [not_and_or] at hf
    obtain (hf | hf) := hf
    · simp only [cfcₙ_apply_of_not_continuousOn _ hf, le_rfl]
    · simp only [cfcₙ_apply_of_not_map_zero _ hf, le_rfl]

Depends on / 依赖: ContinuousOn, le_rfl, not_and_or
-/
lemma cfcₙ_nonneg {f : R -> R} {a : A} (h : forall x in σₙ R a, 0 <= f x) :
    0 <= cfcₙ f a := by
  by_cases hf : ContinuousOn f (σₙ R a) ∧ f 0 = 0
  · obtain ⟨h₁, h₂⟩ := hf
    simpa using cfcₙ_mono h
  · simp only [not_and_or] at hf
    obtain (hf | hf) := hf
    · simp only [cfcₙ_apply_of_not_continuousOn _ hf, le_rfl]
    · simp only [cfcₙ_apply_of_not_map_zero _ hf, le_rfl]

/--
lemma `cfcₙ_nonpos` / 引理 `cfcₙ_nonpos`

English:
lemma cfcₙ_nonpos
  given: (f : R -> R) (a : A) (h : forall x in σₙ R a, f x <= 0)
  proof: by
  by_cases hf : ContinuousOn f (σₙ R a) ∧ f 0 = 0
  · obtain ⟨h₁, h₂⟩ := hf
    simpa using cfcₙ_mono h
  · simp only [not_and_or] at hf
    obtain (hf | hf) := hf
    · simp only [cfcₙ_apply_of_not_continuousOn _ hf, le_rfl]
    · simp only [cfcₙ_apply_of_not_map_zero _ hf, le_rfl]

中文:
引理 cfcₙ_nonpos
  条件: (f : R -> R) (a : A) (h : 对任意 x in σₙ R a, f x <= 0)
  证明: by
  by_cases hf : ContinuousOn f (σₙ R a) ∧ f 0 = 0
  · obtain ⟨h₁, h₂⟩ := hf
    simpa using cfcₙ_mono h
  · simp only [not_and_or] at hf
    obtain (hf | hf) := hf
    · simp only [cfcₙ_apply_of_not_continuousOn _ hf, le_rfl]
    · simp only [cfcₙ_apply_of_not_map_zero _ hf, le_rfl]

Depends on / 依赖: ContinuousOn, le_rfl, not_and_or
-/
lemma cfcₙ_nonpos (f : R -> R) (a : A) (h : forall x in σₙ R a, f x <= 0) :
    cfcₙ f a <= 0 := by
  by_cases hf : ContinuousOn f (σₙ R a) ∧ f 0 = 0
  · obtain ⟨h₁, h₂⟩ := hf
    simpa using cfcₙ_mono h
  · simp only [not_and_or] at hf
    obtain (hf | hf) := hf
    · simp only [cfcₙ_apply_of_not_continuousOn _ hf, le_rfl]
    · simp only [cfcₙ_apply_of_not_map_zero _ hf, le_rfl]

end Semiring

section Ring

variable {R A : Type*} {p : A -> Prop} [CommRing R] [PartialOrder R] [Nontrivial R]
variable [StarRing R] [MetricSpace R] [IsTopologicalRing R] [ContinuousStar R]
variable [ContinuousSqrt R] [StarOrderedRing R] [NoZeroDivisors R]
variable [TopologicalSpace A] [NonUnitalRing A] [StarRing A] [PartialOrder A] [StarOrderedRing A]
variable [Module R A] [IsScalarTower R A A] [SMulCommClass R A A]
variable [NonUnitalContinuousFunctionalCalculus R A p] [NonnegSpectrumClass R A]

/--
lemma `cfcₙHom_le_iff` / 引理 `cfcₙHom_le_iff`

English:
lemma cfcₙHom_le_iff
  given: {a : A} (ha : p a) {f g : C(σₙ R a, R)₀}
  proof: by
  rw [← sub_nonneg]; rw [← map_sub]; rw [cfcₙHom_nonneg_iff]; rw [sub_nonneg]

中文:
引理 cfcₙHom_le_iff
  条件: {a : A} (ha : p a) {f g : C(σₙ R a, R)₀}
  证明: by
  rw [← sub_nonneg]; rw [← map_sub]; rw [cfcₙHom_nonneg_iff]; rw [sub_nonneg]

Depends on / 依赖: map_sub, sub_nonneg
-/
lemma cfcₙHom_le_iff {a : A} (ha : p a) {f g : C(σₙ R a, R)₀} :
    cfcₙHom ha f <= cfcₙHom ha g ↔ f <= g := by
  rw [← sub_nonneg]; rw [← map_sub]; rw [cfcₙHom_nonneg_iff]; rw [sub_nonneg]

set_option backward.isDefEq.respectTransparency false in
/--
lemma `cfcₙ_le_iff` / 引理 `cfcₙ_le_iff`

English:
lemma cfcₙ_le_iff
  statement: (f g : R -> R) (a : A) (hf : ContinuousOn f (σₙ R a) := by cfc_cont_tac)
  proof: by
  rw [cfcₙ_apply f a]; rw [cfcₙ_apply g a]; rw [cfcₙHom_le_iff (show p a from ha)]; rw [ContinuousMapZero.le_def]
  simp

中文:
引理 cfcₙ_le_iff
  结论: (f g : R -> R) (a : A) (hf : ContinuousOn f (σₙ R a) := by cfc_cont_tac)
  证明: by
  rw [cfcₙ_apply f a]; rw [cfcₙ_apply g a]; rw [cfcₙHom_le_iff (show p a from ha)]; rw [ContinuousMapZero.le_def]
  simp

Depends on / 依赖: ContinuousMapZero, ContinuousMapZero.le_def, ContinuousOn, cfc_cont_tac, cfc_tac, cfc_zero_tac, le_def
-/
lemma cfcₙ_le_iff (f g : R -> R) (a : A) (hf : ContinuousOn f (σₙ R a) := by cfc_cont_tac)
    (hg : ContinuousOn g (σₙ R a) := by cfc_cont_tac) (hf0 : f 0 = 0 := by cfc_zero_tac)
    (hg0 : g 0 = 0 := by cfc_zero_tac) (ha : p a := by cfc_tac) :
    cfcₙ f a <= cfcₙ g a ↔ forall x in σₙ R a, f x <= g x := by
  rw [cfcₙ_apply f a]; rw [cfcₙ_apply g a]; rw [cfcₙHom_le_iff (show p a from ha)]; rw [ContinuousMapZero.le_def]
  simp

/--
lemma `cfcₙ_nonpos_iff` / 引理 `cfcₙ_nonpos_iff`

English:
lemma cfcₙ_nonpos_iff
  statement: (f : R -> R) (a : A) (hf : ContinuousOn f (σₙ R a) := by cfc_cont_tac)
  proof: by
  simp_rw [← neg_nonneg, ← cfcₙ_neg]
  exact cfcₙ_nonneg_iff (fun x => -f x) a

中文:
引理 cfcₙ_nonpos_iff
  结论: (f : R -> R) (a : A) (hf : ContinuousOn f (σₙ R a) := by cfc_cont_tac)
  证明: by
  simp_rw [← neg_nonneg, ← cfcₙ_neg]
  exact cfcₙ_nonneg_iff (fun x => -f x) a

Depends on / 依赖: NormMulClass, NormMulClass.toNormSMulClass, cfc_cont_tac, cfc_tac, cfc_zero_tac, neg_nonneg, simp_rw, toNormSMulClass
-/
lemma cfcₙ_nonpos_iff (f : R -> R) (a : A) (hf : ContinuousOn f (σₙ R a) := by cfc_cont_tac)
    (h0 : f 0 = 0 := by cfc_zero_tac) (ha : p a := by cfc_tac) :
    cfcₙ f a <= 0 ↔ forall x in σₙ R a, f x <= 0 := by
  simp_rw [← neg_nonneg, ← cfcₙ_neg]
  exact cfcₙ_nonneg_iff (fun x => -f x) a

end Ring

end Order

/-! ### `cfcₙHom` on a superset of the quasispectrum -/

section Superset

open ContinuousMapZero

variable {R A : Type*} {p : A -> Prop} [CommSemiring R] [Nontrivial R] [StarRing R]
    [MetricSpace R] [IsTopologicalSemiring R] [ContinuousStar R] [NonUnitalRing A] [StarRing A]
    [TopologicalSpace A] [Module R A] [IsScalarTower R A A] [SMulCommClass R A A]
    [instCFCₙ : NonUnitalContinuousFunctionalCalculus R A p]

/-- The composition of `cfcₙHom` with the natural embedding `C(s, R)₀ → C(quasispectrum R a, R)₀`
whenever `quasispectrum R a ⊆ s`.

This is sometimes necessary in order to consider the same continuous functions applied to multiple
distinct elements, with the added constraint that `cfcₙ` does not suffice. This can occur, for
example, if it is necessary to use uniqueness of this continuous functional calculus. A practical
example can be found in the proof of `CFC.posPart_negPart_unique`. -/
@[simps!]
/--
Definition of `cfcₙHomSuperset` / `cfcₙHomSuperset` 的定义

English:
definition cfcₙHomSuperset
  signature: {a : A} (ha : p a) {s : Set R} (hs : σₙ R a subseteq s)
  body: ⟨hs (quasispectrum.zero_mem R a)⟩
    C(s, R)₀ ->⋆ₙₐ[R] A :=
  have : Fact (0 in s) := ⟨hs (quasispectrum.zero_mem R a)⟩
.comp ContinuousMapZero.nonUnitalStarAlgHom_precomp R cfcₙHom ha (R := R)
    ⟨⟨_, continuous_id.subtype_map hs⟩, rfl⟩

中文:
定义 cfcₙHomSuperset
  签名: {a : A} (ha : p a) {s : 集合 R} (hs : σₙ R a subseteq s)
  定义体: ⟨hs (quasispectrum.zero_mem R a)⟩
    C(s, R)₀ ->⋆ₙₐ[R] A :=
  have : Fact (0 in s) := ⟨hs (quasispectrum.zero_mem R a)⟩
.comp ContinuousMapZero.nonUnitalStarAlgHom_precomp R cfcₙHom ha (R := R)
    ⟨⟨_, continuous_id.subtype_map hs⟩, rfl⟩

Depends on / 依赖: NormMulClass, NormMulClass.toNormSMulClass_op, SeminormedRing, quasispectrum, quasispectrum.zero_mem, toNormSMulClass_op, zero_mem
-/
noncomputable def cfcₙHomSuperset {a : A} (ha : p a) {s : Set R} (hs : σₙ R a subseteq s) :
    haveI : Fact (0 in s) := ⟨hs (quasispectrum.zero_mem R a)⟩
    C(s, R)₀ ->⋆ₙₐ[R] A :=
  have : Fact (0 in s) := ⟨hs (quasispectrum.zero_mem R a)⟩
.comp ContinuousMapZero.nonUnitalStarAlgHom_precomp R cfcₙHom ha (R := R)
    ⟨⟨_, continuous_id.subtype_map hs⟩, rfl⟩

/--
lemma `cfcₙHomSuperset_continuous` / 引理 `cfcₙHomSuperset_continuous`

English:
lemma cfcₙHomSuperset_continuous
  given: {a : A} (ha : p a) {s : Set R} (hs : σₙ R a subseteq s)
  proof: have : Fact (0 in s) := ⟨hs (quasispectrum.zero_mem R a)⟩
(cfcₙHom_continuous ha).comp ContinuousMapZero.continuous_precomp _

中文:
引理 cfcₙHomSuperset_continuous
  条件: {a : A} (ha : p a) {s : 集合 R} (hs : σₙ R a subseteq s)
  证明: have : Fact (0 in s) := ⟨hs (quasispectrum.zero_mem R a)⟩
(cfcₙHom_continuous ha).comp ContinuousMapZero.continuous_precomp _

Depends on / 依赖: ContinuousMapZero, ContinuousMapZero.continuous_precomp, continuous_precomp, quasispectrum, quasispectrum.zero_mem, zero_mem
-/
lemma cfcₙHomSuperset_continuous {a : A} (ha : p a) {s : Set R} (hs : σₙ R a subseteq s) :
    Continuous (cfcₙHomSuperset ha hs) :=
  have : Fact (0 in s) := ⟨hs (quasispectrum.zero_mem R a)⟩
(cfcₙHom_continuous ha).comp ContinuousMapZero.continuous_precomp _

/--
lemma `cfcₙHomSuperset_id` / 引理 `cfcₙHomSuperset_id`

English:
lemma cfcₙHomSuperset_id
  given: {a : A} (ha : p a) {s : Set R} (hs : σₙ R a subseteq s)
  proof: ⟨hs (quasispectrum.zero_mem R a)⟩
    cfcₙHomSuperset ha hs (.id s) = a :=
  cfcₙHom_id ha

中文:
引理 cfcₙHomSuperset_id
  条件: {a : A} (ha : p a) {s : 集合 R} (hs : σₙ R a subseteq s)
  证明: ⟨hs (quasispectrum.zero_mem R a)⟩
    cfcₙHomSuperset ha hs (.id s) = a :=
  cfcₙHom_id ha

Depends on / 依赖: quasispectrum, quasispectrum.zero_mem, zero_mem
-/
lemma cfcₙHomSuperset_id {a : A} (ha : p a) {s : Set R} (hs : σₙ R a subseteq s) :
    haveI : Fact (0 in s) := ⟨hs (quasispectrum.zero_mem R a)⟩
    cfcₙHomSuperset ha hs (.id s) = a :=
  cfcₙHom_id ha

end Superset

section IsClosedEmbedding

/--
Definition of `NonUnitalClosedEmbeddingContinuousFunctionalCalculus` / `NonUnitalClosedEmbeddingContinuousFunctionalCalculus` 的定义

English:
class NonUnitalClosedEmbeddingContinuousFunctionalCalculus
  parameters: (R A : Type*)
  axioms and operations (1):
    - isClosedEmbedding((a : A) (ha : p a)) : Topology.IsClosedEmbedding (cfcₙHom (R := R) ha)

中文:
类 非幺ClosedEmbeddingContinuousFunctionalCalculus
  参数: (R A : 类型)
  公理与运算 (1 个):
    - isClosedEmbedding((a : A) (ha : p a)) : 拓扑.是闭嵌入 (cfcₙHom (R := R) ha)
-/
class NonUnitalClosedEmbeddingContinuousFunctionalCalculus (R A : Type*)
    (p : outParam (A -> Prop)) [CommSemiring R] [Nontrivial R] [StarRing R] [MetricSpace R]
    [IsTopologicalSemiring R] [ContinuousStar R] [NonUnitalRing A] [StarRing A] [TopologicalSpace A]
    [Module R A] [IsScalarTower R A A] [SMulCommClass R A A] extends
    NonUnitalContinuousFunctionalCalculus R A p where
  isClosedEmbedding (a : A) (ha : p a) : Topology.IsClosedEmbedding (cfcₙHom (R := R) ha)

open scoped NonUnitalContinuousFunctionalCalculus in
/--
lemma `cfcₙHom_isClosedEmbedding` / 引理 `cfcₙHom_isClosedEmbedding`

English:
lemma cfcₙHom_isClosedEmbedding
  statement: {R A : Type*} {p : A -> Prop} [CommSemiring R] [Nontrivial R]
  proof: NonUnitalClosedEmbeddingContinuousFunctionalCalculus.isClosedEmbedding a ha

中文:
引理 cfcₙHom_isClosedEmbedding
  结论: {R A : 类型} {p : A -> 命题} [交换半环 R] [非平凡 R]
  证明: NonUnitalClosedEmbeddingContinuousFunctionalCalculus.isClosedEmbedding a ha

Depends on / 依赖: ENormSMulClass, NonUnitalClosedEmbeddingContinuousFunctionalCalculus, NonUnitalClosedEmbeddingContinuousFunctionalCalculus.isClosedEmbedding, isClosedEmbedding
-/
lemma cfcₙHom_isClosedEmbedding {R A : Type*} {p : A -> Prop} [CommSemiring R] [Nontrivial R]
    [StarRing R] [MetricSpace R] [IsTopologicalSemiring R] [ContinuousStar R] [NonUnitalRing A]
    [StarRing A] [TopologicalSpace A] [Module R A] [IsScalarTower R A A] [SMulCommClass R A A]
    [instCFC : NonUnitalClosedEmbeddingContinuousFunctionalCalculus R A p]
    {a : A} (ha : p a) :
IsClosedEmbedding (cfcₙHom ha : C(σₙ R a, R)₀ ->⋆ₙₐ[R] A) :=
  NonUnitalClosedEmbeddingContinuousFunctionalCalculus.isClosedEmbedding a ha

end IsClosedEmbedding

/-! ### Obtain a non-unital continuous functional calculus from a unital one -/

section UnitalToNonUnital

open ContinuousMapZero Set Uniformity ContinuousMap

variable {R A : Type*} {p : A -> Prop} [Semifield R] [StarRing R] [MetricSpace R]
variable [IsTopologicalSemiring R] [ContinuousStar R] [Ring A] [StarRing A] [TopologicalSpace A]
variable [Algebra R A]

variable (R) in
/--
Definition of `cfcₙHom_of_cfcHom` / `cfcₙHom_of_cfcHom` 的定义

English:
definition cfcₙHom_of_cfcHom
  signature: [ContinuousFunctionalCalculus R A p] {a : A} (ha : p a)
  body: let e := ContinuousMapZero.toContinuousMapHom (X := σₙ R a) (R := R)
  let f : C(spectrum R a, quasispectrum R a) :=
⟨_, continuous_inclusion spectrum_subset_quasispectrum R a⟩
  let ψ := ContinuousMap.compStarAlgHom' R R f
(cfcHom ha (R := R) : C(spectrum R a, R) ->⋆ₙₐ[R] A).comp
    (ψ : C(σₙ R a,

中文:
定义 cfcₙHom_of_cfcHom
  签名: [余ntinuousFunctionalCalculus R A p] {a : A} (ha : p a)
  定义体: let e := ContinuousMapZero.toContinuousMapHom (X := σₙ R a) (R := R)
  let f : C(spectrum R a, quasispectrum R a) :=
⟨_, continuous_inclusion spectrum_subset_quasispectrum R a⟩
  let ψ := ContinuousMap.compStarAlgHom' R R f
(cfcHom ha (R := R) : C(spectrum R a, R) ->⋆ₙₐ[R] A).comp
    (ψ : C(σₙ R a,

Depends on / 依赖: ContinuousMap, ContinuousMap.compStarAlgHom, ContinuousMapZero, ContinuousMapZero.toContinuousMapHom, cfcHom, compStarAlgHom, continuous_inclusion, quasispectrum, spectrum, spectrum_subset_quasispectrum, toContinuousMapHom
-/
noncomputable def cfcₙHom_of_cfcHom [ContinuousFunctionalCalculus R A p] {a : A} (ha : p a) :
    C(σₙ R a, R)₀ ->⋆ₙₐ[R] A :=
  let e := ContinuousMapZero.toContinuousMapHom (X := σₙ R a) (R := R)
  let f : C(spectrum R a, quasispectrum R a) :=
⟨_, continuous_inclusion spectrum_subset_quasispectrum R a⟩
  let ψ := ContinuousMap.compStarAlgHom' R R f
(cfcHom ha (R := R) : C(spectrum R a, R) ->⋆ₙₐ[R] A).comp
    (ψ : C(σₙ R a, R) ->⋆ₙₐ[R] C(spectrum R a, R)).comp e

/--
lemma `continuous_cfcₙHom_of_cfcHom` / 引理 `continuous_cfcₙHom_of_cfcHom`

English:
lemma continuous_cfcₙHom_of_cfcHom
  given: [ContinuousFunctionalCalculus R A p] {a : A} (ha : p a)
  proof: (cfcHom_continuous ha).comp (ContinuousMap.continuous_precomp _).comp by fun_prop

中文:
引理 continuous_cfcₙHom_of_cfcHom
  条件: [余ntinuousFunctionalCalculus R A p] {a : A} (ha : p a)
  证明: (cfcHom_continuous ha).comp (ContinuousMap.continuous_precomp _).comp by fun_prop

Depends on / 依赖: ContinuousMap, ContinuousMap.continuous_precomp, cfcHom_continuous, continuous_precomp, fun_prop
-/
lemma continuous_cfcₙHom_of_cfcHom [ContinuousFunctionalCalculus R A p] {a : A} (ha : p a) :
    Continuous (cfcₙHom_of_cfcHom R ha) :=
(cfcHom_continuous ha).comp (ContinuousMap.continuous_precomp _).comp by fun_prop

/--
lemma `cfcₙHom_of_cfcHom_injective` / 引理 `cfcₙHom_of_cfcHom_injective`

English:
lemma cfcₙHom_of_cfcHom_injective
  given: [ContinuousFunctionalCalculus R A p] {a : A} (ha : p a)
  proof: by
  refine (cfcHom_injective ha).comp fun f g h => ?_
  ext x
  obtain rfl | hx := eq_or_ne x 0
  · simp
  · have := by simpa [quasispectrum_eq_spectrum_union_zero] using x.prop
    replace := this.resolve_left (Subtype.val_injective.ne_iff.mpr hx)
    congrm($h ⟨x, this⟩)

中文:
引理 cfcₙHom_of_cfcHom_injective
  条件: [余ntinuousFunctionalCalculus R A p] {a : A} (ha : p a)
  证明: by
  refine (cfcHom_injective ha).comp fun f g h => ?_
  ext x
  obtain rfl | hx := eq_or_ne x 0
  · simp
  · have := by simpa [quasispectrum_eq_spectrum_union_zero] using x.prop
    replace := this.resolve_left (Subtype.val_injective.ne_iff.mpr hx)
    congrm($h ⟨x, this⟩)

Depends on / 依赖: Subtype, Subtype.val_injective.ne_iff.mpr, cfcHom_injective, congrm, eq_or_ne, ne_iff, quasispectrum_eq_spectrum_union_zero, replace, resolve_left, this.resolve_left, val_injective, x.prop
-/
lemma cfcₙHom_of_cfcHom_injective [ContinuousFunctionalCalculus R A p] {a : A} (ha : p a) :
    Function.Injective (cfcₙHom_of_cfcHom R ha) := by
  refine (cfcHom_injective ha).comp fun f g h => ?_
  ext x
  obtain rfl | hx := eq_or_ne x 0
  · simp
  · have := by simpa [quasispectrum_eq_spectrum_union_zero] using x.prop
    replace := this.resolve_left (Subtype.val_injective.ne_iff.mpr hx)
    congrm($h ⟨x, this⟩)

/--
lemma `cfcₙHom_of_cfcHom_map_quasispectrum` / 引理 `cfcₙHom_of_cfcHom_map_quasispectrum`

English:
lemma cfcₙHom_of_cfcHom_map_quasispectrum
  given: [ContinuousFunctionalCalculus R A p] {a : A} (ha : p a)
  proof: by
  intro f
  simp only [cfcₙHom_of_cfcHom]
  rw [quasispectrum_eq_spectrum_union_zero]
  simp only [NonUnitalStarAlgHom.comp_apply, NonUnitalStarAlgHom.coe_coe]
  rw [cfcHom_map_spectrum ha]
  ext x
  constructor
  · rintro (⟨x, rfl⟩ | rfl)
    · exact ⟨⟨x.1, spectrum_subset_quasispectrum R a x.2⟩

中文:
引理 cfcₙHom_of_cfcHom_map_quasispectrum
  条件: [余ntinuousFunctionalCalculus R A p] {a : A} (ha : p a)
  证明: by
  intro f
  simp only [cfcₙHom_of_cfcHom]
  rw [quasispectrum_eq_spectrum_union_zero]
  simp only [NonUnitalStarAlgHom.comp_apply, NonUnitalStarAlgHom.coe_coe]
  rw [cfcHom_map_spectrum ha]
  ext x
  constructor
  · rintro (⟨x, rfl⟩ | rfl)
    · exact ⟨⟨x.1, spectrum_subset_quasispectrum R a x.2⟩

Depends on / 依赖: NonUnitalStarAlgHom, NonUnitalStarAlgHom.coe_coe, NonUnitalStarAlgHom.comp_apply, Or.inl, Or.inr, cfcHom_map_spectrum, coe_coe, comp_apply, map_zero, quasispectrum_eq_spectrum_union_zero, simp_rw, spectrum_subset_quasispectrum
-/
lemma cfcₙHom_of_cfcHom_map_quasispectrum [ContinuousFunctionalCalculus R A p] {a : A} (ha : p a) :
    forall f : C(σₙ R a, R)₀, σₙ R (cfcₙHom_of_cfcHom R ha f) = range f := by
  intro f
  simp only [cfcₙHom_of_cfcHom]
  rw [quasispectrum_eq_spectrum_union_zero]
  simp only [NonUnitalStarAlgHom.comp_apply, NonUnitalStarAlgHom.coe_coe]
  rw [cfcHom_map_spectrum ha]
  ext x
  constructor
  · rintro (⟨x, rfl⟩ | rfl)
    · exact ⟨⟨x.1, spectrum_subset_quasispectrum R a x.2⟩, rfl⟩
    · exact ⟨0, map_zero f⟩
  · rintro ⟨x, rfl⟩
    have hx := x.2
    simp_rw [quasispectrum_eq_spectrum_union_zero R a] at hx
    obtain (hx | hx) := hx
    · exact Or.inl ⟨⟨x.1, hx⟩, rfl⟩
    · apply Or.inr
      push _ in _ at hx ⊢
      rw [show x = 0 from Subtype.val_injective hx]; rw [map_zero]

-- gives access to the `ContinuousFunctionalCalculus.compactSpace_spectrum` instance
open scoped ContinuousFunctionalCalculus

/--
lemma `isClosedEmbedding_cfcₙHom_of_cfcHom` / 引理 `isClosedEmbedding_cfcₙHom_of_cfcHom`

English:
lemma isClosedEmbedding_cfcₙHom_of_cfcHom
  statement: [ClosedEmbeddingContinuousFunctionalCalculus R A p]
  proof: by
  let f : C(spectrum R a, σₙ R a) :=
⟨_, continuous_inclusion spectrum_subset_quasispectrum R a⟩
refine (cfcHom_isClosedEmbedding ha).comp
    (IsUniformInducing.isUniformEmbedding ⟨?_⟩).isClosedEmbedding
  have := uniformSpace_eq_inf_precomp_of_cover (β := R) f (0 : C(Unit, σₙ R a))
(map_continu

中文:
引理 isClosedEmbedding_cfcₙHom_of_cfcHom
  结论: [ClosedEmbeddingContinuousFunctionalCalculus R A p]
  证明: by
  let f : C(spectrum R a, σₙ R a) :=
⟨_, continuous_inclusion spectrum_subset_quasispectrum R a⟩
refine (cfcHom_isClosedEmbedding ha).comp
    (IsUniformInducing.isUniformEmbedding ⟨?_⟩).isClosedEmbedding
  have := uniformSpace_eq_inf_precomp_of_cover (β := R) f (0 : C(Unit, σₙ R a))
(map_continu

Depends on / 依赖: ContinuousMap, ContinuousMap.coe_mk, ContinuousMap.coe_zero, IsUniformInducing, IsUniformInducing.isUniformEmbedding, Subtype, Subtype.val_injective.image_injective.eq_iff, cfcHom_isClosedEmbedding, coe_mk, coe_zero, continuous_inclusion, eq_iff, image_injective, image_singleton, image_union, isClosedEmbedding, isProperMap, isUniformEmbedding, map_continuous, range_zero
-/
lemma isClosedEmbedding_cfcₙHom_of_cfcHom [ClosedEmbeddingContinuousFunctionalCalculus R A p]
    [CompleteSpace R] {a : A} (ha : p a) :
    IsClosedEmbedding (cfcₙHom_of_cfcHom R ha) := by
  let f : C(spectrum R a, σₙ R a) :=
⟨_, continuous_inclusion spectrum_subset_quasispectrum R a⟩
refine (cfcHom_isClosedEmbedding ha).comp
    (IsUniformInducing.isUniformEmbedding ⟨?_⟩).isClosedEmbedding
  have := uniformSpace_eq_inf_precomp_of_cover (β := R) f (0 : C(Unit, σₙ R a))
(map_continuous f).isProperMap (map_continuous 0).isProperMap by
      simp only [← Subtype.val_injective.image_injective.eq_iff, f, ContinuousMap.coe_mk,
        ContinuousMap.coe_zero, range_zero, image_union, image_singleton,
        quasispectrum.coe_zero, ← range_comp, val_comp_inclusion, image_univ, Subtype.range_coe,
        quasispectrum_eq_spectrum_union_zero]
  simp_rw +instances [← isUniformEmbedding_toContinuousMap.comap_uniformity, this,
    @inf_uniformity _ (.comap _ _) (.comap _ _), uniformity_comap, Filter.comap_inf,
    Filter.comap_comap]
refine .symm inf_eq_left.mpr le_top.trans eq_top_iff.mp ?_
  have : forall U in 𝓤 (C(Unit, R)), (0, 0) in U := fun U hU => refl_mem_uniformity hU
  convert! Filter.comap_const_of_mem this with ⟨u, v⟩ <;>
  ext ⟨x, rfl⟩ <;> [exact map_zero u; exact map_zero v]

/--
Instance `ContinuousFunctionalCalculus.toNonUnital` / 实例 `ContinuousFunctionalCalculus.toNonUnital`

English:
instance ContinuousFunctionalCalculus.toNonUnital
  signature: [ContinuousFunctionalCalculus R A p]
  body: cfc_predicate_zero R
  compactSpace_quasispectrum a := by
    have h_cpct : CompactSpace (spectrum R a) := inferInstance
    simp only [← isCompact_iff_compactSpace, quasispectrum_eq_spectrum_union_zero] at h_cpct ⊢
.union isCompact_singleton exact h_cpct
  exists_cfc_of_predicate _ ha :=
    ⟨cfcₙH

中文:
实例 余ntinuousFunctionalCalculus.toNonUnital
  签名: [余ntinuousFunctionalCalculus R A p]
  定义体: cfc_predicate_zero R
  compactSpace_quasispectrum a := by
    have h_cpct : CompactSpace (spectrum R a) := inferInstance
    simp only [← isCompact_iff_compactSpace, quasispectrum_eq_spectrum_union_zero] at h_cpct ⊢
.union isCompact_singleton exact h_cpct
  exists_cfc_of_predicate _ ha :=
    ⟨cfcₙH

Depends on / 依赖: cfc_predicate_zero
-/
instance ContinuousFunctionalCalculus.toNonUnital [ContinuousFunctionalCalculus R A p] :
    NonUnitalContinuousFunctionalCalculus R A p where
  predicate_zero := cfc_predicate_zero R
  compactSpace_quasispectrum a := by
    have h_cpct : CompactSpace (spectrum R a) := inferInstance
    simp only [← isCompact_iff_compactSpace, quasispectrum_eq_spectrum_union_zero] at h_cpct ⊢
.union isCompact_singleton exact h_cpct
  exists_cfc_of_predicate _ ha :=
    ⟨cfcₙHom_of_cfcHom R ha,
      continuous_cfcₙHom_of_cfcHom ha,
      cfcₙHom_of_cfcHom_injective ha,
      cfcHom_id ha,
      cfcₙHom_of_cfcHom_map_quasispectrum ha,
      fun _ => cfcHom_predicate ha _⟩

open scoped NonUnitalContinuousFunctionalCalculus in
/--
lemma `cfcₙHom_eq_cfcₙHom_of_cfcHom` / 引理 `cfcₙHom_eq_cfcₙHom_of_cfcHom`

English:
lemma cfcₙHom_eq_cfcₙHom_of_cfcHom
  statement: [ContinuousFunctionalCalculus R A p]
  proof: cfcₙHom_eq_of_continuous_of_map_id ha _ (continuous_cfcₙHom_of_cfcHom ha) by
    simpa only [cfcₙHom_id ha] using! cfcHom_id ha

中文:
引理 cfcₙHom_eq_cfcₙHom_of_cfcHom
  结论: [余ntinuousFunctionalCalculus R A p]
  证明: cfcₙHom_eq_of_continuous_of_map_id ha _ (continuous_cfcₙHom_of_cfcHom ha) by
    simpa only [cfcₙHom_id ha] using! cfcHom_id ha

Depends on / 依赖: cfcHom_id
-/
lemma cfcₙHom_eq_cfcₙHom_of_cfcHom [ContinuousFunctionalCalculus R A p]
    [ContinuousMapZero.UniqueHom R A] {a : A} (ha : p a) :
    cfcₙHom ha = cfcₙHom_of_cfcHom R ha :=
cfcₙHom_eq_of_continuous_of_map_id ha _ (continuous_cfcₙHom_of_cfcHom ha) by
    simpa only [cfcₙHom_id ha] using! cfcHom_id ha

/--
lemma `cfcₙ_eq_cfc` / 引理 `cfcₙ_eq_cfc`

English:
lemma cfcₙ_eq_cfc
  statement: [ContinuousFunctionalCalculus R A p] [ContinuousMapZero.UniqueHom R A] {f : R -> R}
  proof: by
  by_cases ha : p a
· have hf' := hf.mono spectrum_subset_quasispectrum R a
    rw [cfc_apply f a ha hf']; rw [cfcₙ_apply f a hf]; rw [cfcₙHom_eq_cfcₙHom_of_cfcHom]; rw [cfcₙHom_of_cfcHom]
    dsimp only [NonUnitalStarAlgHom.comp_apply,
      NonUnitalStarAlgHom.coe_coe, compStarAlgHom'_apply]
  

中文:
引理 cfcₙ_eq_cfc
  结论: [余ntinuousFunctionalCalculus R A p] [余ntinuousMapZero.唯一态射 R A] {f : R -> R}
  证明: by
  by_cases ha : p a
· have hf' := hf.mono spectrum_subset_quasispectrum R a
    rw [cfc_apply f a ha hf']; rw [cfcₙ_apply f a hf]; rw [cfcₙHom_eq_cfcₙHom_of_cfcHom]; rw [cfcₙHom_of_cfcHom]
    dsimp only [NonUnitalStarAlgHom.comp_apply,
      NonUnitalStarAlgHom.coe_coe, compStarAlgHom'_apply]
  

Depends on / 依赖: NonUnitalStarAlgHom, NonUnitalStarAlgHom.coe_coe, NonUnitalStarAlgHom.comp_apply, _apply, cfc_apply, cfc_apply_of_not_predicate, cfc_cont_tac, cfc_zero_tac, coe_coe, compStarAlgHom, comp_apply, hf.mono, spectrum_subset_quasispectrum
-/
lemma cfcₙ_eq_cfc [ContinuousFunctionalCalculus R A p] [ContinuousMapZero.UniqueHom R A] {f : R -> R}
    {a : A} (hf : ContinuousOn f (σₙ R a) := by cfc_cont_tac) (hf0 : f 0 = 0 := by cfc_zero_tac) :
    cfcₙ f a = cfc f a := by
  by_cases ha : p a
· have hf' := hf.mono spectrum_subset_quasispectrum R a
    rw [cfc_apply f a ha hf']; rw [cfcₙ_apply f a hf]; rw [cfcₙHom_eq_cfcₙHom_of_cfcHom]; rw [cfcₙHom_of_cfcHom]
    dsimp only [NonUnitalStarAlgHom.comp_apply,
      NonUnitalStarAlgHom.coe_coe, compStarAlgHom'_apply]
    congr
  · simp [cfc_apply_of_not_predicate a ha, cfcₙ_apply_of_not_predicate (R := R) a ha]

/--
Instance `ClosedEmbeddingContinuousFunctionalCalculus.toNonUnital` / 实例 `ClosedEmbeddingContinuousFunctionalCalculus.toNonUnital`

English:
instance ClosedEmbeddingContinuousFunctionalCalculus.toNonUnital
  body: by
    rw [cfcₙHom_eq_cfcₙHom_of_cfcHom (R := R) ha]
    exact isClosedEmbedding_cfcₙHom_of_cfcHom ha

中文:
实例 ClosedEmbeddingContinuousFunctionalCalculus.toNonUnital
  定义体: by
    rw [cfcₙHom_eq_cfcₙHom_of_cfcHom (R := R) ha]
    exact isClosedEmbedding_cfcₙHom_of_cfcHom ha
-/
instance ClosedEmbeddingContinuousFunctionalCalculus.toNonUnital
    [ClosedEmbeddingContinuousFunctionalCalculus R A p] [ContinuousMapZero.UniqueHom R A]
    [CompleteSpace R] : NonUnitalClosedEmbeddingContinuousFunctionalCalculus R A p where
  isClosedEmbedding a ha := by
    rw [cfcₙHom_eq_cfcₙHom_of_cfcHom (R := R) ha]
    exact isClosedEmbedding_cfcₙHom_of_cfcHom ha

end UnitalToNonUnital
