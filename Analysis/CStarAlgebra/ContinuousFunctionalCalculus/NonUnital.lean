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
`Mathlib/Analysis/CStarAlgebra/ContinuousFunctionalCalculus/Unital.lean`.  Changes to either file
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

/-- A non-unital star `R`-algebra `A` has a *continuous functional calculus* for elements
satisfying the property `p : A → Prop` if

+ for every such element `a : A` there is a non-unital star algebra homomorphism
  `cfcₙHom : C(quasispectrum R a, R)₀ →⋆ₙₐ[R] A` sending the (restriction of) the identity map
  to `a`.
+ `cfcHom` is continuous and injective and the quasispectrum of the image of function `f` is
  its range.
+ `cfcₙHom` preserves the property `p`.

The property `p` is marked as an `outParam` so that the user need not specify it. In practice,

+ for `R := ℂ`, we choose `p := IsStarNormal`,
+ for `R := ℝ`, we choose `p := IsSelfAdjoint`,
+ for `R := ℝ≥0`, we choose `p := (0 ≤ ·)`.

Instead of directly providing the data we opt instead for a `Prop` class. In all relevant cases,
the continuous functional calculus is uniquely determined, and utilizing this approach
prevents diamonds or problems arising from multiple instances. -/
/-
**NonUnitalContinuousFunctionalCalculus** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：(R : Type u_1) →   (A : Type u_2) →     outParam (A → Prop) →       [inst 
: CommSemiring R] →         [Nontrivial R] →           [inst_2 : StarRing R] →  
           [inst_3 : MetricSpace R] →               [IsTopologicalSemiring R] → 
                [ContinuousStar R] →                   [inst_6 : NonUnitalRing A
] →                     [StarRing A] →                       [TopologicalSpace A
] →                         [inst_9 : _root_.Module R A] → [IsScalarTower R A A]
 → [SMulCommClass R A A] → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A non-unital star `R`-algebra `A` has a *continuous functional calculus* for ele
ments
satisfying the property `p : A → Prop` if

+ for every such element `a : A` there is a non-unital star algebra homomorphism
  `cfcₙHom : C(quasispectrum R a, R)₀ →⋆ₙₐ[R] A` sending the (restriction of) th
e identity map
  to `a`.
+ `cfcHom` is continuous and injective and the quasispectrum of the image of fun
ction `f` is
  its range.
+ `cfcₙHom` preserves the property `p`.

The property `p` is marked as an `outParam` so that the user need not specify it
. In practice,

+ for `R := ℂ`, we choose `p := IsStarNormal`,
+ for `R := ℝ`, we choose `p := IsSelfAdjoint`,
+ for `R := ℝ≥0`, we choose `p := (0 ≤ ·)`.

Instead of directly providing the data we opt instead for a `Prop` class. In all
 relevant cases,
the continuous functional calculus is uniquely determined, and utilizing this ap
proach
prevents diamonds or problems arising from multiple instances.
-/
class NonUnitalContinuousFunctionalCalculus (R A : Type*) (p : outParam (A → Prop))
    [CommSemiring R] [Nontrivial R] [StarRing R] [MetricSpace R] [IsTopologicalSemiring R]
    [ContinuousStar R] [NonUnitalRing A] [StarRing A] [TopologicalSpace A] [Module R A]
    [IsScalarTower R A A] [SMulCommClass R A A] : Prop where
  predicate_zero : p 0
  [compactSpace_quasispectrum : ∀ a : A, CompactSpace (σₙ R a)]
  exists_cfc_of_predicate : ∀ a, p a → ∃ φ : C(σₙ R a, R)₀ →⋆ₙₐ[R] A,
    Continuous φ ∧ Function.Injective φ ∧ φ ⟨(ContinuousMap.id R).restrict <| σₙ R a, rfl⟩ = a ∧
      (∀ f, σₙ R (φ f) = Set.range f) ∧ ∀ f, p (φ f)

-- this instance should not be activated everywhere but it is useful when developing generic API
-- for the continuous functional calculus
scoped[NonUnitalContinuousFunctionalCalculus]
attribute [instance] NonUnitalContinuousFunctionalCalculus.compactSpace_quasispectrum

/-- A class guaranteeing that the non-unital continuous functional calculus is uniquely determined
by the properties that it is a continuous non-unital star algebra homomorphism mapping the
(restriction of) the identity to `a`. This is the necessary tool used to establish `cfcₙHom_comp`
and the more common variant `cfcₙ_comp`.

This class will have instances in each of the common cases `ℂ`, `ℝ` and `ℝ≥0` as a consequence of
the Stone-Weierstrass theorem. -/
/-
**ContinuousMapZero.UniqueHom** 是 Mathlib 中的一个归纳类型，位于命名空间 `ContinuousMapZero`。
形式化陈述：(R : Type u_1) →   (A : Type u_2) →     [inst : CommSemiring R] →       [i
nst_1 : StarRing R] →         [inst_2 : MetricSpace R] →           [IsTopologica
lSemiring R] →             [ContinuousStar R] →               [inst_5 : NonUnita
lRing A] →                 [StarRing A] →                   [TopologicalSpace A]
 →                     [inst_8 : _root_.Module R A] → [IsScalarTower R A A] → [S
MulCommClass R A A] → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A class guaranteeing that the non-unital continuous functional calculus is uniqu
ely determined
by the properties that it is a continuous non-unital star algebra homomorphism m
apping the
(restriction of) the identity to `a`. This is the necessary tool used to establi
sh `cfcₙHom_comp`
and the more common variant `cfcₙ_comp`.

This class will have instances in each of the common cases `ℂ`, `ℝ` and `ℝ≥0` as
 a consequence of
the Stone-Weierstrass theorem.
-/
class ContinuousMapZero.UniqueHom (R A : Type*) [CommSemiring R] [StarRing R]
    [MetricSpace R] [IsTopologicalSemiring R] [ContinuousStar R] [NonUnitalRing A] [StarRing A]
    [TopologicalSpace A] [Module R A] [IsScalarTower R A A] [SMulCommClass R A A] : Prop where
  eq_of_continuous_of_map_id (s : Set R) [CompactSpace s] [Fact (0 ∈ s)]
    (φ ψ : C(s, R)₀ →⋆ₙₐ[R] A) (hφ : Continuous φ) (hψ : Continuous ψ)
    (h : φ (.id s) = ψ (.id s)) :
    φ = ψ
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {R A : Type*} [CommSemiring R] [NonUnitalRing A] [Module R A] [Nontrivial R] (a : A) :
    Fact (0 ∈ σₙ R a) :=
  ⟨quasispectrum.zero_mem R a⟩

section Main

variable {R A : Type*} {p : A → Prop} [CommSemiring R] [Nontrivial R] [StarRing R] [MetricSpace R]
variable [IsTopologicalSemiring R] [ContinuousStar R] [NonUnitalRing A] [StarRing A]
variable [TopologicalSpace A] [Module R A] [IsScalarTower R A A] [SMulCommClass R A A]
variable [instCFCₙ : NonUnitalContinuousFunctionalCalculus R A p]

include instCFCₙ in
/-
**NonUnitalContinuousFunctionalCalculus.isCompact_quasispectrum** 是 Mathlib 中的一个
引理，位于命名空间 ``。
形式化陈述：NonUnitalContinuousFunctionalCalculus.isCompact_quasispectrum (a : A) : Is
Compact (σₙ R a)
参数：a : A。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `isCompact_iff_compactSpace`：isCompact_iff_compactSpace : IsCompact s ↔ C
ompactSpace s
· 使用定理 `NonUnitalContinuousFunctionalCalculus.compactSpace_quasispectrum`：∀ {R :
 Type u_1} {A : Type u_2} {p : outParam (A → Prop)} {inst : CommSemiring R} {ins
t_1 : Nontrivial R}   {inst_2 : StarRing R} {inst_3 : …
-/
lemma NonUnitalContinuousFunctionalCalculus.isCompact_quasispectrum (a : A) :
    IsCompact (σₙ R a) :=
  isCompact_iff_compactSpace.mpr inferInstance
/-
**NonUnitalStarAlgHom.ext_continuousMap** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：NonUnitalStarAlgHom.ext_continuousMap [UniqueHom R A] (a : A) [CompactSpac
e (σₙ R a)] (φ ψ : C(σₙ R a, R)₀ ->⋆ₙₐ[R] A) (hφ : Continuous φ) (hψ : Continuou
s ψ) (h : φ (.id (σₙ R a)) = ψ (.id (σₙ R a))) : φ = ψ
参数：a : A；σₙ R a；φ ψ : C(σₙ R a, R)₀ ->⋆ₙₐ[R] A；hφ : Continuous φ；hψ : Continuous
 ψ；h : φ (.id (σₙ R a)) = ψ (.id (σₙ R a))。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsSemitopologicalSemiring.toContinuousAdd`：∀ {R : Type u_2} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSemitopologic
alSemiring R], ContinuousAdd R
· 使用定理 `IsTopologicalSemiring.toIsSemitopologicalSemiring`：∀ (R : Type u_2) [ins
t : TopologicalSpace R] [inst_1 : NonUnitalNonAssocSemiring R] [IsTopologicalSem
iring R],   IsSemitopologicalSemiring R
· 使用定理 `IsSemitopologicalSemiring.toSeparatelyContinuousMul`：∀ {R : Type u_2} {i
nst : TopologicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSem
itopologicalSemiring R], SeparatelyContin…
· 使用定理 `instFactMemSetQuasispectrumOfNat`：∀ {R : Type u_1} {A : Type u_2} [inst 
: CommSemiring R] [inst_1 : NonUnitalRing A] [inst_2 : _root_.Module R A]   [Non
trivial R] (a : A), Fa…
· 使用定理 `ContinuousMapZero.UniqueHom.eq_of_continuous_of_map_id`：∀ {R : Type u_1}
 {A : Type u_2} {inst : CommSemiring R} {inst_1 : StarRing R} {inst_2 : MetricSp
ace R}   {inst_3 : IsTopologicalSemiring R} …
-/
lemma NonUnitalStarAlgHom.ext_continuousMap [UniqueHom R A]
    (a : A) [CompactSpace (σₙ R a)] (φ ψ : C(σₙ R a, R)₀ →⋆ₙₐ[R] A)
    (hφ : Continuous φ) (hψ : Continuous ψ) (h : φ (.id (σₙ R a)) = ψ (.id (σₙ R a))) :
    φ = ψ :=
  UniqueHom.eq_of_continuous_of_map_id _ φ ψ hφ hψ h

section cfcₙHom

variable {a : A} (ha : p a)

/-- The non-unital star algebra homomorphism underlying an instance of the continuous functional
calculus for non-unital algebras; a version for continuous functions on the quasispectrum.

In this case, the user must supply the fact that `a` satisfies the predicate `p`.

While `NonUnitalContinuousFunctionalCalculus` is stated in terms of these homomorphisms, in practice
the user should instead prefer `cfcₙ` over `cfcₙHom`.
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
The non-unital star algebra homomorphism underlying an instance of the continuou
s functional
calculus for non-unital algebras; a version for continuous functions on the quas
ispectrum.

In this case, the user must supply the fact that `a` satisfies the predicate `p`
.

While `NonUnitalContinuousFunctionalCalculus` is stated in terms of these homomo
rphisms, in practice
the user should instead prefer `cfcₙ` over `cfcₙHom`.
-/
noncomputable def cfcₙHom : C(σₙ R a, R)₀ →⋆ₙₐ[R] A :=
  (NonUnitalContinuousFunctionalCalculus.exists_cfc_of_predicate a ha).choose

@[fun_prop]
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
lemma cfcₙHom_continuous : Continuous (cfcₙHom ha : C(σₙ R a, R)₀ →⋆ₙₐ[R] A) :=
  (NonUnitalContinuousFunctionalCalculus.exists_cfc_of_predicate a ha).choose_spec.1
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
lemma cfcₙHom_injective : Function.Injective (cfcₙHom ha : C(σₙ R a, R)₀ →⋆ₙₐ[R] A) :=
  (NonUnitalContinuousFunctionalCalculus.exists_cfc_of_predicate a ha).choose_spec.2.1
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
lemma cfcₙHom_id : cfcₙHom ha (.id (σₙ R a)) = a :=
  (NonUnitalContinuousFunctionalCalculus.exists_cfc_of_predicate a ha).choose_spec.2.2.1

/-- The **spectral mapping theorem** for the non-unital continuous functional calculus. -/
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
The **spectral mapping theorem** for the non-unital continuous functional calcul
us.
-/
lemma cfcₙHom_map_quasispectrum (f : C(σₙ R a, R)₀) :
    σₙ R (cfcₙHom ha f) = Set.range f :=
  (NonUnitalContinuousFunctionalCalculus.exists_cfc_of_predicate a ha).choose_spec.2.2.2.1 f
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
lemma cfcₙHom_predicate (f : C(σₙ R a, R)₀) :
    p (cfcₙHom ha f) :=
  (NonUnitalContinuousFunctionalCalculus.exists_cfc_of_predicate a ha).choose_spec.2.2.2.2 f

open scoped NonUnitalContinuousFunctionalCalculus in
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
lemma cfcₙHom_eq_of_continuous_of_map_id [UniqueHom R A]
    (φ : C(σₙ R a, R)₀ →⋆ₙₐ[R] A) (hφ₁ : Continuous φ) (hφ₂ : φ (.id (σₙ R a)) = a) :
    cfcₙHom ha = φ :=
  (cfcₙHom ha).ext_continuousMap a φ (cfcₙHom_continuous ha) hφ₁ <| by
    rw [cfcₙHom_id ha, hφ₂]

set_option backward.isDefEq.respectTransparency false in
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
theorem cfcₙHom_comp [UniqueHom R A] (f : C(σₙ R a, R)₀)
    (f' : C(σₙ R a, σₙ R (cfcₙHom ha f))₀)
    (hff' : ∀ x, f x = f' x) (g : C(σₙ R (cfcₙHom ha f), R)₀) :
    cfcₙHom ha (g.comp f') = cfcₙHom (cfcₙHom_predicate ha f) g := by
  let ψ : C(σₙ R (cfcₙHom ha f), R)₀ →⋆ₙₐ[R] C(σₙ R a, R)₀ :=
    { toFun := (ContinuousMapZero.comp · f')
      map_smul' := fun _ _ ↦ rfl
      map_add' := fun _ _ ↦ rfl
      map_mul' := fun _ _ ↦ rfl
      map_zero' := rfl
      map_star' := fun _ ↦ rfl }
  let φ : C(σₙ R (cfcₙHom ha f), R)₀ →⋆ₙₐ[R] A := (cfcₙHom ha).comp ψ
  suffices cfcₙHom (cfcₙHom_predicate ha f) = φ from DFunLike.congr_fun this.symm g
  refine cfcₙHom_eq_of_continuous_of_map_id (cfcₙHom_predicate ha f) φ ?_ ?_
  · refine (cfcₙHom_continuous ha).comp <| continuous_induced_rng.mpr ?_
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
`cfcₙHom` bundled as a continuous linear map.
-/
noncomputable def cfcₙL {a : A} (ha : p a) : C(σₙ R a, R)₀ →L[R] A :=
  { cfcₙHom ha with
    toFun := cfcₙHom ha
    map_smul' := map_smul _ }

end cfcₙL

section CFCn

open scoped Classical in
/-- This is the *continuous functional calculus* of an element `a : A` in a non-unital algebra
applied to bare functions.  When either `a` does not satisfy the predicate `p` (i.e., `a` is not
`IsStarNormal`, `IsSelfAdjoint`, or `0 ≤ a` when `R` is `ℂ`, `ℝ`, or `ℝ≥0`, respectively), or when
`f : R → R` is not continuous on the quasispectrum of `a` or `f 0 ≠ 0`, then `cfcₙ f a` returns the
junk value `0`.

This is the primary declaration intended for widespread use of the continuous functional calculus
for non-unital algebras, and all the API applies to this declaration. For more information, see the
module documentation for `Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Unital`. -/
noncomputable irreducible_def cfcₙ (f : R → R) (a : A) : A :=
  if h : p a ∧ ContinuousOn f (σₙ R a) ∧ f 0 = 0
    then cfcₙHom h.1 ⟨⟨_, h.2.1.domRestrict⟩, h.2.2⟩
    else 0

variable (f g : R → R) (a : A)
variable (hf : ContinuousOn f (σₙ R a) := by cfc_cont_tac) (hf0 : f 0 = 0 := by cfc_zero_tac)
variable (hg : ContinuousOn g (σₙ R a) := by cfc_cont_tac) (hg0 : g 0 = 0 := by cfc_zero_tac)
variable (ha : p a := by cfc_tac)

set_option backward.privateInPublic true in
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
lemma cfcₙ_apply : cfcₙ f a = cfcₙHom (a := a) ha ⟨⟨_, hf.domRestrict⟩, hf0⟩ := by
  rw [cfcₙ_def, dif_pos ⟨ha, hf, hf0⟩]
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
lemma cfcₙ_apply_pi {ι : Type*} (f : ι → R → R) (a : A) (ha := by cfc_tac)
    (hf : ∀ i, ContinuousOn (f i) (σₙ R a) := by cfc_cont_tac)
    (hf0 : ∀ i, f i 0 = 0 := by cfc_zero_tac) :
    (fun i => cfcₙ (f i) a) = (fun i => cfcₙHom (a := a) ha ⟨⟨_, (hf i).domRestrict⟩, hf0 i⟩) := by
  ext i
  simp only [cfcₙ_apply (f i) a (hf i) (hf0 i)]
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
lemma cfcₙ_apply_of_not_and_and {f : R → R} (a : A)
    (ha : ¬ (p a ∧ ContinuousOn f (σₙ R a) ∧ f 0 = 0)) :
    cfcₙ f a = 0 := by
  rw [cfcₙ_def, dif_neg ha]
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
lemma cfcₙ_apply_of_not_predicate {f : R → R} (a : A) (ha : ¬ p a) :
    cfcₙ f a = 0 := by
  rw [cfcₙ_def, dif_neg (not_and_of_not_left _ ha)]
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
lemma cfcₙ_apply_of_not_continuousOn {f : R → R} (a : A) (hf : ¬ ContinuousOn f (σₙ R a)) :
    cfcₙ f a = 0 := by
  rw [cfcₙ_def, dif_neg (not_and_of_not_right _ (not_and_of_not_left _ hf))]
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
lemma cfcₙ_apply_of_not_map_zero {f : R → R} (a : A) (hf : ¬ f 0 = 0) :
    cfcₙ f a = 0 := by
  rw [cfcₙ_def, dif_neg (not_and_of_not_right _ (not_and_of_not_right _ hf))]

set_option backward.isDefEq.respectTransparency false in
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
lemma cfcₙHom_eq_cfcₙ_extend {a : A} (g : R → R) (ha : p a) (f : C(σₙ R a, R)₀) :
    cfcₙHom ha f = cfcₙ (Function.extend Subtype.val f g) a := by
  have h : f = (σₙ R a).domRestrict (Function.extend Subtype.val f g) := by
    ext; simp
  have hg : ContinuousOn (Function.extend Subtype.val f g) (σₙ R a) :=
    continuousOn_iff_continuous_domRestrict.mpr <| h ▸ map_continuous f
  have hg0 : (Function.extend Subtype.val f g) 0 = 0 := by
    rw [← quasispectrum.coe_zero (R := R) a, Subtype.val_injective.extend_apply]
    exact map_zero f
  generalize Function.extend Subtype.val f g = f' at *
  rw [cfcₙ_apply ..]
  congr!
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
lemma cfcₙ_eq_cfcₙL {a : A} {f : R → R} (ha : p a) (hf : ContinuousOn f (σₙ R a)) (hf0 : f 0 = 0) :
    cfcₙ f a = cfcₙL ha ⟨⟨_, hf.domRestrict⟩, hf0⟩ := by
  rw [cfcₙ_def, dif_pos ⟨ha, hf, hf0⟩, cfcₙL_apply]

set_option backward.privateInPublic true in
/-- A version of `cfcₙ_apply` in terms of `ContinuousMapZero.mkD` -/
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
A version of `cfcₙ_apply` in terms of `ContinuousMapZero.mkD`
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
/-- A version of `cfcₙ_eq_cfcₙL` in terms of `ContinuousMapZero.mkD` -/
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
A version of `cfcₙ_eq_cfcₙL` in terms of `ContinuousMapZero.mkD`
-/
lemma cfcₙ_eq_cfcₙL_mkD :
    cfcₙ f a = cfcₙL (a := a) ha (mkD ((quasispectrum R a).domRestrict f) 0) :=
  cfcₙ_apply_mkD _ _
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
lemma cfcₙ_cases (P : A → Prop) (a : A) (f : R → R) (h₀ : P 0)
    (haf : ∀ (hf : ContinuousOn f (σₙ R a)) h0 ha, P (cfcₙHom ha ⟨⟨_, hf.domRestrict⟩, h0⟩)) :
    P (cfcₙ f a) := by
  by_cases h : ContinuousOn f (σₙ R a) ∧ f 0 = 0 ∧ p a
  · rw [cfcₙ_apply f a h.1 h.2.1 h.2.2]
    exact haf h.1 h.2.1 h.2.2
  · simp only [not_and_or] at h
    obtain (h | h | h) := h
    · rwa [cfcₙ_apply_of_not_continuousOn _ h]
    · rwa [cfcₙ_apply_of_not_map_zero _ h]
    · rwa [cfcₙ_apply_of_not_predicate _ h]
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
lemma cfcₙ_commute_cfcₙ (f g : R → R) (a : A) : Commute (cfcₙ f a) (cfcₙ g a) := by
  refine cfcₙ_cases (fun x ↦ Commute x (cfcₙ g a)) a f (by simp) fun hf hf0 ha ↦ ?_
  refine cfcₙ_cases (fun x ↦ Commute _ x) a g (by simp) fun hg hg0 _ ↦ ?_
  exact Commute.all _ _ |>.map _

set_option backward.privateInPublic true in
variable (R) in
include ha in
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
lemma cfcₙ_id : cfcₙ (id : R → R) a = a :=
  cfcₙ_apply (id : R → R) a ▸ cfcₙHom_id (p := p) ha

set_option backward.privateInPublic true in
variable (R) in
include ha in
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
lemma cfcₙ_id' : cfcₙ (fun x : R ↦ x) a = a := cfcₙ_id R a

set_option backward.isDefEq.respectTransparency false in
set_option backward.privateInPublic true in
include ha hf hf0 in
/-- The **spectral mapping theorem** for the non-unital continuous functional calculus. -/
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
The **spectral mapping theorem** for the non-unital continuous functional calcul
us.
-/
lemma cfcₙ_map_quasispectrum : σₙ R (cfcₙ f a) = f '' σₙ R a := by
  simp [cfcₙ_apply f a, cfcₙHom_map_quasispectrum (p := p)]

variable (R) in
include R in
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
lemma cfcₙ_predicate_zero : p 0 :=
  NonUnitalContinuousFunctionalCalculus.predicate_zero (R := R)
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
lemma cfcₙ_predicate (f : R → R) (a : A) : p (cfcₙ f a) :=
  cfcₙ_cases p a f (cfcₙ_predicate_zero R) fun _ _ _ ↦ cfcₙHom_predicate ..
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
lemma cfcₙ_congr {f g : R → R} {a : A} (hfg : (σₙ R a).EqOn f g) :
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
      exact fun hf ↦ hg (hf.congr hfg.symm)
    · rw [cfcₙ_apply_of_not_map_zero a h0, cfcₙ_apply_of_not_map_zero]
      exact fun hf ↦ h0 (hfg (quasispectrum.zero_mem R a) ▸ hf)
/-
**eqOn_of_cfc** 是 Mathlib 中的一个引理，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma eqOn_of_cfcₙ_eq_cfcₙ {f g : R → R} {a : A} (h : cfcₙ f a = cfcₙ g a) (ha : p a := by cfc_tac)
    (hf : ContinuousOn f (σₙ R a) := by cfc_cont_tac) (hf0 : f 0 = 0 := by cfc_zero_tac)
    (hg : ContinuousOn g (σₙ R a) := by cfc_cont_tac) (hg0 : g 0 = 0 := by cfc_zero_tac) :
    (σₙ R a).EqOn f g := by
  rw [cfcₙ_apply f a, cfcₙ_apply g a] at h
  exact fun x hx ↦ congr($(cfcₙHom_injective ha h) ⟨x, hx⟩)
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
lemma cfcₙ_eq_cfcₙ_iff_eqOn {f g : R → R} {a : A} (ha : p a := by cfc_tac)
    (hf : ContinuousOn f (σₙ R a) := by cfc_cont_tac) (hf0 : f 0 = 0 := by cfc_zero_tac)
    (hg : ContinuousOn g (σₙ R a) := by cfc_cont_tac) (hg0 : g 0 = 0 := by cfc_zero_tac) :
    cfcₙ f a = cfcₙ g a ↔ (σₙ R a).EqOn f g :=
  ⟨eqOn_of_cfcₙ_eq_cfcₙ, cfcₙ_congr⟩

variable (R)

@[simp]
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
lemma cfcₙ_zero : cfcₙ (0 : R → R) a = 0 := by
  by_cases ha : p a
  · exact cfcₙ_apply (0 : R → R) a ▸ map_zero (cfcₙHom ha)
  · rw [cfcₙ_apply_of_not_predicate a ha]

@[simp]
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
lemma cfcₙ_const_zero : cfcₙ (fun _ : R ↦ 0) a = 0 := cfcₙ_zero R a

variable {R}

set_option backward.privateInPublic true in
include hf hf0 hg hg0 in
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
lemma cfcₙ_mul : cfcₙ (fun x ↦ f x * g x) a = cfcₙ f a * cfcₙ g a := by
  by_cases ha : p a
  · rw [cfcₙ_apply f a, cfcₙ_apply g a, ← map_mul, cfcₙ_apply _ a]
    congr
  · simp [cfcₙ_apply_of_not_predicate a ha]

set_option backward.privateInPublic true in
include hf hf0 hg hg0 in
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
lemma cfcₙ_add : cfcₙ (fun x ↦ f x + g x) a = cfcₙ f a + cfcₙ g a := by
  by_cases ha : p a
  · rw [cfcₙ_apply f a, cfcₙ_apply g a, cfcₙ_apply _ a]
    simp_rw [← map_add]
    congr
  · simp [cfcₙ_apply_of_not_predicate a ha]

set_option backward.isDefEq.respectTransparency false in
open Finset in
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
lemma cfcₙ_sum {ι : Type*} (f : ι → R → R) (a : A) (s : Finset ι)
    (hf : ∀ i ∈ s, ContinuousOn (f i) (σₙ R a) := by cfc_cont_tac)
    (hf0 : ∀ i ∈ s, f i 0 = 0 := by cfc_zero_tac) :
    cfcₙ (∑ i ∈ s, f i) a = ∑ i ∈ s, cfcₙ (f i) a := by
  by_cases ha : p a
  · have hsum : s.sum f = fun z => ∑ i ∈ s, f i z := by ext; simp
    have hf' : ContinuousOn (∑ i : s, f i) (σₙ R a) := by
      rw [sum_coe_sort s, hsum]
      exact continuousOn_finsetSum s fun i hi => hf i hi
    rw [← sum_coe_sort s, ← sum_coe_sort s]
    rw [cfcₙ_apply_pi _ a ha (fun ⟨i, hi⟩ => hf i hi), ← map_sum, cfcₙ_apply _ a hf']
    congr 1
    ext
    simp
  · simp [cfcₙ_apply_of_not_predicate a ha]

open Finset in
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
lemma cfcₙ_sum_univ {ι : Type*} [Fintype ι] (f : ι → R → R) (a : A)
    (hf : ∀ i, ContinuousOn (f i) (σₙ R a) := by cfc_cont_tac)
    (hf0 : ∀ i, f i 0 = 0 := by cfc_zero_tac) :
    cfcₙ (∑ i, f i) a = ∑ i, cfcₙ (f i) a :=
  cfcₙ_sum f a _ (fun i _ ↦ hf i) (fun i _ ↦ hf0 i)
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
lemma cfcₙ_smul {S : Type*} [SMulZeroClass S R] [ContinuousConstSMul S R]
    [SMulZeroClass S A] [IsScalarTower S R A] [IsScalarTower S R (R → R)]
    (s : S) (f : R → R) (a : A) (hf : ContinuousOn f (σₙ R a) := by cfc_cont_tac)
    (h0 : f 0 = 0 := by cfc_zero_tac) :
    cfcₙ (fun x ↦ s • f x) a = s • cfcₙ f a := by
  by_cases ha : p a
  · rw [cfcₙ_apply f a, cfcₙ_apply _ a]
    simp_rw [← Pi.smul_def, ← smul_one_smul R s _]
    rw [← map_smul]
    congr
  · simp [cfcₙ_apply_of_not_predicate a ha]
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
lemma cfcₙ_const_mul (r : R) (f : R → R) (a : A) (hf : ContinuousOn f (σₙ R a) := by cfc_cont_tac)
    (h0 : f 0 = 0 := by cfc_zero_tac) :
    cfcₙ (fun x ↦ r * f x) a = r • cfcₙ f a :=
  cfcₙ_smul r f a
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
lemma cfcₙ_star : cfcₙ (fun x ↦ star (f x)) a = star (cfcₙ f a) := by
  by_cases h : p a ∧ ContinuousOn f (σₙ R a) ∧ f 0 = 0
  · obtain ⟨ha, hf, h0⟩ := h
    rw [cfcₙ_apply f a, ← map_star, cfcₙ_apply _ a]
    congr
  · simp only [not_and_or] at h
    obtain (ha | hf | h0) := h
    · simp [cfcₙ_apply_of_not_predicate a ha]
    · rw [cfcₙ_apply_of_not_continuousOn a hf, cfcₙ_apply_of_not_continuousOn, star_zero]
      exact fun hf_star ↦ hf <| by simpa using hf_star.star
    · rw [cfcₙ_apply_of_not_map_zero a h0, cfcₙ_apply_of_not_map_zero, star_zero]
      exact fun hf0 ↦ h0 <| by simpa using congr(star $(hf0))
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
lemma cfcₙ_smul_id {S : Type*} [SMulZeroClass S R] [ContinuousConstSMul S R]
    [SMulZeroClass S A] [IsScalarTower S R A] [IsScalarTower S R (R → R)]
    (s : S) (a : A) (ha : p a := by cfc_tac) : cfcₙ (s • · : R → R) a = s • a := by
  rw [cfcₙ_smul s _ a, cfcₙ_id' R a]
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
lemma cfcₙ_const_mul_id (r : R) (a : A) (ha : p a := by cfc_tac) : cfcₙ (r * ·) a = r • a :=
  cfcₙ_smul_id r a

set_option backward.privateInPublic true in
include ha in
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
lemma cfcₙ_star_id : cfcₙ (star · : R → R) a = star a := by
  rw [cfcₙ_star _ a, cfcₙ_id' R a]

variable (R) in
/-
**range_cfc** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：range_cfc {a : A} (ha : p a) : Set.range (cfc (R
参数：ha : p a。
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
· 使用定理 `ClosedEmbeddingContinuousFunctionalCalculus.toContinuousFunctionalCalcul
us`：∀ {R : Type u_1} {A : Type u_2} {p : outParam (A → Prop)} {inst : CommSemiri
ng R} {inst_1 : StarRing R}   {inst_2 : MetricSpace R} {inst_3 :…
· 使用定理 `IsSemitopologicalRing.toIsSemitopologicalSemiring`：∀ {R : Type u_2} {ins
t : TopologicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopolog
icalRing R],   IsSemitopologicalSemirin…
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `range_cfc_eq_range_cfcHom`：range_cfc_eq_range_cfcHom [StarModule R A] {a
 : A} (ha : p a) : Set.range (cfc (R
· 使用定理 `range_cfcHom`：range_cfcHom {a : A} (ha : p a) : (cfcHom ha (R
-/
theorem range_cfcₙ_eq_range_cfcₙHom {a : A} (ha : p a) :
    Set.range (cfcₙ (R := R) · a) = NonUnitalStarAlgHom.range (cfcₙHom ha (R := R)) := by
  ext
  constructor
  all_goals rintro ⟨f, rfl⟩
  · exact cfcₙ_cases _ a f (zero_mem _) fun hf hf₀ ha ↦ ⟨_, rfl⟩
  · exact ⟨Subtype.val.extend f 0, cfcₙHom_eq_cfcₙ_extend _ ha _ |>.symm⟩

section Comp

variable [UniqueHom R A]

set_option backward.isDefEq.respectTransparency false in
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
lemma cfcₙ_comp (g f : R → R) (a : A)
    (hg : ContinuousOn g (f '' σₙ R a) := by cfc_cont_tac) (hg0 : g 0 = 0 := by cfc_zero_tac)
    (hf : ContinuousOn f (σₙ R a) := by cfc_cont_tac) (hf0 : f 0 = 0 := by cfc_zero_tac)
    (ha : p a := by cfc_tac) :
    cfcₙ (g ∘ f) a = cfcₙ g (cfcₙ f a) := by
  have := hg.comp hf <| (σₙ R a).mapsTo_image f
  have sp_eq :
      σₙ R (cfcₙHom (show p a from ha) ⟨ContinuousMap.mk _ hf.domRestrict, hf0⟩) =
        f '' (σₙ R a) := by
    rw [cfcₙHom_map_quasispectrum (by exact ha) _]
    ext
    simp
  rw [cfcₙ_apply .., cfcₙ_apply f a,
    cfcₙ_apply _ _ (by convert! hg) (ha := cfcₙHom_predicate (show p a from ha) _),
    ← cfcₙHom_comp _ _]
  swap
  · exact ⟨.mk _ <| hf.domRestrict.codRestrict fun x ↦ by rw [sp_eq]; use x.1; simp,
      Subtype.ext hf0⟩
  · congr
  · exact fun _ ↦ rfl
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
lemma cfcₙ_comp' (g f : R → R) (a : A)
    (hg : ContinuousOn g (f '' σₙ R a) := by cfc_cont_tac) (hg0 : g 0 = 0 := by cfc_zero_tac)
    (hf : ContinuousOn f (σₙ R a) := by cfc_cont_tac) (hf0 : f 0 = 0 := by cfc_zero_tac)
    (ha : p a := by cfc_tac) :
    cfcₙ (g <| f ·) a = cfcₙ g (cfcₙ f a) :=
  cfcₙ_comp g f a
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
lemma cfcₙ_comp_smul {S : Type*} [SMulZeroClass S R] [ContinuousConstSMul S R]
    [SMulZeroClass S A] [IsScalarTower S R A] [IsScalarTower S R (R → R)]
    (s : S) (f : R → R) (a : A) (hf : ContinuousOn f ((s • ·) '' (σₙ R a)) := by cfc_cont_tac)
    (hf0 : f 0 = 0 := by cfc_zero_tac) (ha : p a := by cfc_tac) :
    cfcₙ (f <| s • ·) a = cfcₙ f (s • a) := by
  rw [cfcₙ_comp' f (s • ·) a, cfcₙ_smul_id s a]
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
lemma cfcₙ_comp_const_mul (r : R) (f : R → R) (a : A)
    (hf : ContinuousOn f ((r * ·) '' (σₙ R a)) := by cfc_cont_tac)
    (hf0 : f 0 = 0 := by cfc_zero_tac) (ha : p a := by cfc_tac) :
    cfcₙ (f <| r * ·) a = cfcₙ f (r • a) := by
  rw [cfcₙ_comp' f (r * ·) a, cfcₙ_const_mul_id r a]
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
lemma cfcₙ_comp_star (hf : ContinuousOn f (star '' (σₙ R a)) := by cfc_cont_tac)
    (hf0 : f 0 = 0 := by cfc_zero_tac) (ha : p a := by cfc_tac) :
    cfcₙ (f <| star ·) a = cfcₙ f (star a) := by
  rw [cfcₙ_comp' f star a, cfcₙ_star_id a]

end Comp

/-
**CFC.eq_zero_of_quasispectrum_eq_zero** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：CFC.eq_zero_of_quasispectrum_eq_zero (h_spec : σₙ R a subseteq {0}) (ha : 
p a
参数：h_spec : σₙ R a subseteq {0}。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `cfcₙ_id`：cfcₙ_id : cfcₙ (id : R -> R) a = a
· 使用引理 `cfcₙ_const_zero`：cfcₙ_const_zero : cfcₙ (fun _ : R => 0) a = 0
· 使用引理 `cfcₙ_congr`：cfcₙ_congr {f g : R -> R} {a : A} (hfg : (σₙ R a).EqOn f g) 
: cfcₙ f a = cfcₙ g a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `implies_congr_ctx`：∀ {p₁ p₂ q₁ q₂ : Prop}, p₁ = p₂ → (p₂ → q₁ = q₂) → (p
₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
lemma CFC.eq_zero_of_quasispectrum_eq_zero (h_spec : σₙ R a ⊆ {0}) (ha : p a := by cfc_tac) :
    a = 0 := by
  simpa [cfcₙ_id R a] using cfcₙ_congr (a := a) (f := id) (g := fun _ : R ↦ 0) fun x ↦ by simp_all

include instCFCₙ in
/-
**CFC.quasispectrum_zero_eq** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：CFC.quasispectrum_zero_eq : σₙ R (0 : A) = {0}
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.eq_singleton_iff_unique_mem`：eq_singleton_iff_unique_mem : s = {a} ↔
 a in s ∧ forall x in s, x = a
· 使用引理 `quasispectrum.zero_mem`：quasispectrum.zero_mem [Nontrivial R] (a : A) : 
0 in quasispectrum R a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Set.image_congr`：image_congr {f g : α -> β} {s : Set α} (h : forall a in
 s, f a = g a) : f '' s = g '' s
· 使用引理 `cfcₙ_map_quasispectrum`：cfcₙ_map_quasispectrum : σₙ R (cfcₙ f a) = f '' 
σₙ R a
· 使用定理 `Continuous.continuousOn`：Continuous.continuousOn (h : Continuous f) : Co
ntinuousOn f s
· 使用定理 `continuous_zero`：∀ {M : Type u_3} {X : Type u_5} [inst : TopologicalSpac
e X] [inst_1 : TopologicalSpace M] [inst_2 : Zero M],   Continuous 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用引理 `cfcₙ_predicate_zero`：cfcₙ_predicate_zero : p 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `cfcₙ_zero`：cfcₙ_zero : cfcₙ (0 : R -> R) a = 0
-/
lemma CFC.quasispectrum_zero_eq : σₙ R (0 : A) = {0} := by
  refine Set.eq_singleton_iff_unique_mem.mpr ⟨quasispectrum.zero_mem R 0, fun x hx ↦ ?_⟩
  rw [← cfcₙ_zero R (0 : A),
    cfcₙ_map_quasispectrum _ _ (by cfc_cont_tac) (by cfc_zero_tac) (cfcₙ_predicate_zero R)] at hx
  simp_all
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
@[simp] lemma cfcₙ_apply_zero {f : R → R} : cfcₙ f (0 : A) = 0 := by
  by_cases hf0 : f 0 = 0
  · nth_rw 2 [← cfcₙ_zero R 0]
    apply cfcₙ_congr
    simpa [CFC.quasispectrum_zero_eq]
  · exact cfcₙ_apply_of_not_map_zero _ hf0

@[simp]
/-
**IsStarNormal.cfc** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance IsStarNormal.cfcₙ_map (f : R → R) (a : A) : IsStarNormal (cfcₙ f a) where
  star_comm_self := by
    refine cfcₙ_cases (fun x ↦ Commute (star x) x) _ _ (Commute.zero_right _) fun _ _ _ ↦ ?_
    simp only [Commute, SemiconjBy]
    rw [← cfcₙ_apply f a, ← cfcₙ_star, ← cfcₙ_mul .., ← cfcₙ_mul ..]
    congr! 2
    exact mul_comm _ _

-- The following two lemmas are just `cfcₙ_predicate`, but specific enough for the `@[simp]` tag.
@[simp]
/-
**IsSelfAdjoint.cfc** 是 Mathlib 中的一个定理，位于命名空间 `IsSelfAdjoint`。
形式化陈述：∀ {R : Type u_1} {A : Type u_2} [inst : CommSemiring R] [inst_1 : StarRing
 R] [inst_2 : MetricSpace R]   [inst_3 : IsTopologicalSemiring R] [inst_4 : Cont
inuousStar R] [inst_5 : TopologicalSpace A] [inst_6 : Ring A]   [inst_7 : StarRi
ng A] [inst_8 : Algebra R A] [inst_9 : ContinuousFunctionalCalculus R A IsSelfAd
joint] {f : R → R}   {a : A}, IsSelfAdjoint (cfc f a)
参数：cfc f a。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `cfc_predicate`：cfc_predicate (f : R -> R) (a : A) : p (cfc f a)
-/
protected lemma IsSelfAdjoint.cfcₙ
    [NonUnitalContinuousFunctionalCalculus R A IsSelfAdjoint] {f : R → R} {a : A} :
    IsSelfAdjoint (cfcₙ f a) :=
  cfcₙ_predicate _ _

@[simp]
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
lemma cfcₙ_nonneg_of_predicate [LE A]
    [NonUnitalContinuousFunctionalCalculus R A (0 ≤ ·)] {f : R → R} {a : A} :
    0 ≤ cfcₙ f a :=
  cfcₙ_predicate _ _

end CFCn

end Main

section Neg

variable {R A : Type*} {p : A → Prop} [CommRing R] [Nontrivial R] [StarRing R] [MetricSpace R]
variable [IsTopologicalRing R] [ContinuousStar R] [TopologicalSpace A] [NonUnitalRing A]
variable [StarRing A] [Module R A] [IsScalarTower R A A] [SMulCommClass R A A]
variable [NonUnitalContinuousFunctionalCalculus R A p]
variable (f g : R → R) (a : A)
variable (hf : ContinuousOn f (σₙ R a) := by cfc_cont_tac) (hf0 : f 0 = 0 := by cfc_zero_tac)
variable (hg : ContinuousOn g (σₙ R a) := by cfc_cont_tac) (hg0 : g 0 = 0 := by cfc_zero_tac)

set_option backward.privateInPublic true in
include hf hf0 hg hg0 in
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
lemma cfcₙ_sub : cfcₙ (fun x ↦ f x - g x) a = cfcₙ f a - cfcₙ g a := by
  by_cases ha : p a
  · rw [cfcₙ_apply f a, cfcₙ_apply g a, ← map_sub, cfcₙ_apply ..]
    congr
  · simp [cfcₙ_apply_of_not_predicate a ha]
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
lemma cfcₙ_neg : cfcₙ (fun x ↦ -(f x)) a = -(cfcₙ f a) := by
  by_cases h : p a ∧ ContinuousOn f (σₙ R a) ∧ f 0 = 0
  · obtain ⟨ha, hf, h0⟩ := h
    rw [cfcₙ_apply f a, ← map_neg, cfcₙ_apply ..]
    congr
  · simp only [not_and_or] at h
    obtain (ha | hf | h0) := h
    · simp [cfcₙ_apply_of_not_predicate a ha]
    · rw [cfcₙ_apply_of_not_continuousOn a hf, cfcₙ_apply_of_not_continuousOn, neg_zero]
      exact fun hf_neg ↦ hf <| by simpa using hf_neg.fun_neg
    · rw [cfcₙ_apply_of_not_map_zero a h0, cfcₙ_apply_of_not_map_zero, neg_zero]
      exact (h0 <| neg_eq_zero.mp ·)
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
lemma cfcₙ_neg' : cfcₙ (-f) = (-cfcₙ f : A → A) := by ext1 a; exact (cfcₙ_neg f a)
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
lemma cfcₙ_neg_id (ha : p a := by cfc_tac) :
    cfcₙ (- · : R → R) a = -a := by
  rw [cfcₙ_neg .., cfcₙ_id' R a]

variable [UniqueHom R A]
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
lemma cfcₙ_comp_neg (hf : ContinuousOn f ((-·) '' (σₙ R a)) := by cfc_cont_tac)
    (h0 : f 0 = 0 := by cfc_zero_tac) (ha : p a := by cfc_tac) :
    cfcₙ (f <| - ·) a = cfcₙ f (-a) := by
  rw [cfcₙ_comp' .., cfcₙ_neg_id _]

end Neg

section Order

section Semiring

variable {R A : Type*} {p : A → Prop} [CommSemiring R] [PartialOrder R] [Nontrivial R]
variable [StarRing R] [MetricSpace R] [IsTopologicalSemiring R] [ContinuousStar R]
variable [ContinuousSqrt R] [StarOrderedRing R] [NoZeroDivisors R]
variable [TopologicalSpace A] [NonUnitalRing A] [StarRing A] [PartialOrder A] [StarOrderedRing A]
variable [Module R A] [IsScalarTower R A A] [SMulCommClass R A A]
variable [NonUnitalContinuousFunctionalCalculus R A p]

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
lemma cfcₙHom_mono {a : A} (ha : p a) {f g : C(σₙ R a, R)₀} (hfg : f ≤ g) :
    cfcₙHom ha f ≤ cfcₙHom ha g :=
  OrderHomClass.mono (cfcₙHom ha) hfg
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
lemma cfcₙHom_nonneg_iff [NonnegSpectrumClass R A] {a : A} (ha : p a) {f : C(σₙ R a, R)₀} :
    0 ≤ cfcₙHom ha f ↔ 0 ≤ f := by
  constructor
  · exact fun hf x ↦
      (cfcₙHom_map_quasispectrum ha (R := R) _ ▸ quasispectrum_nonneg_of_nonneg (cfcₙHom ha f) hf)
      _ ⟨x, rfl⟩
  · simpa using (cfcₙHom_mono ha (f := 0) (g := f) ·)
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
lemma cfcₙ_mono {f g : R → R} {a : A} (h : ∀ x ∈ σₙ R a, f x ≤ g x)
    (hf : ContinuousOn f (σₙ R a) := by cfc_cont_tac)
    (hg : ContinuousOn g (σₙ R a) := by cfc_cont_tac)
    (hf0 : f 0 = 0 := by cfc_zero_tac) (hg0 : g 0 = 0 := by cfc_zero_tac) :
    cfcₙ f a ≤ cfcₙ g a := by
  by_cases ha : p a
  · rw [cfcₙ_apply f a, cfcₙ_apply g a]
    exact cfcₙHom_mono ha fun x ↦ h x.1 x.2
  · simp only [cfcₙ_apply_of_not_predicate _ ha, le_rfl]
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
lemma cfcₙ_nonneg_iff [NonnegSpectrumClass R A] (f : R → R) (a : A)
    (hf : ContinuousOn f (σₙ R a) := by cfc_cont_tac)
    (h0 : f 0 = 0 := by cfc_zero_tac) (ha : p a := by cfc_tac) :
    0 ≤ cfcₙ f a ↔ ∀ x ∈ σₙ R a, 0 ≤ f x := by
  rw [cfcₙ_apply .., cfcₙHom_nonneg_iff, ContinuousMapZero.le_def]
  simp only [Subtype.forall]
  congr!
/-
**StarOrderedRing.nonneg_iff_quasispectrum_nonneg** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：StarOrderedRing.nonneg_iff_quasispectrum_nonneg [NonnegSpectrumClass R A] 
(a : A) (ha : p a
参数：a : A。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `cfcₙ_nonneg_iff`：cfcₙ_nonneg_iff [NonnegSpectrumClass R A] (f : R -> R) 
(a : A) (hf : ContinuousOn f (σₙ R a)
· 使用定理 `continuousOn_id'`：continuousOn_id' (s : Set α) : ContinuousOn (fun x : α
 => x) s
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `cfcₙ_id`：cfcₙ_id : cfcₙ (id : R -> R) a = a
-/
lemma StarOrderedRing.nonneg_iff_quasispectrum_nonneg [NonnegSpectrumClass R A] (a : A)
    (ha : p a := by cfc_tac) : 0 ≤ a ↔ ∀ x ∈ quasispectrum R a, 0 ≤ x := by
  have := cfcₙ_nonneg_iff (id : R → R) a (by fun_prop)
  simpa [cfcₙ_id _ a ha] using this
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
lemma cfcₙ_nonneg {f : R → R} {a : A} (h : ∀ x ∈ σₙ R a, 0 ≤ f x) :
    0 ≤ cfcₙ f a := by
  by_cases hf : ContinuousOn f (σₙ R a) ∧ f 0 = 0
  · obtain ⟨h₁, h₂⟩ := hf
    simpa using cfcₙ_mono h
  · simp only [not_and_or] at hf
    obtain (hf | hf) := hf
    · simp only [cfcₙ_apply_of_not_continuousOn _ hf, le_rfl]
    · simp only [cfcₙ_apply_of_not_map_zero _ hf, le_rfl]
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
lemma cfcₙ_nonpos (f : R → R) (a : A) (h : ∀ x ∈ σₙ R a, f x ≤ 0) :
    cfcₙ f a ≤ 0 := by
  by_cases hf : ContinuousOn f (σₙ R a) ∧ f 0 = 0
  · obtain ⟨h₁, h₂⟩ := hf
    simpa using cfcₙ_mono h
  · simp only [not_and_or] at hf
    obtain (hf | hf) := hf
    · simp only [cfcₙ_apply_of_not_continuousOn _ hf, le_rfl]
    · simp only [cfcₙ_apply_of_not_map_zero _ hf, le_rfl]

end Semiring

section Ring

variable {R A : Type*} {p : A → Prop} [CommRing R] [PartialOrder R] [Nontrivial R]
variable [StarRing R] [MetricSpace R] [IsTopologicalRing R] [ContinuousStar R]
variable [ContinuousSqrt R] [StarOrderedRing R] [NoZeroDivisors R]
variable [TopologicalSpace A] [NonUnitalRing A] [StarRing A] [PartialOrder A] [StarOrderedRing A]
variable [Module R A] [IsScalarTower R A A] [SMulCommClass R A A]
variable [NonUnitalContinuousFunctionalCalculus R A p] [NonnegSpectrumClass R A]

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
lemma cfcₙHom_le_iff {a : A} (ha : p a) {f g : C(σₙ R a, R)₀} :
    cfcₙHom ha f ≤ cfcₙHom ha g ↔ f ≤ g := by
  rw [← sub_nonneg, ← map_sub, cfcₙHom_nonneg_iff, sub_nonneg]

set_option backward.isDefEq.respectTransparency false in
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
lemma cfcₙ_le_iff (f g : R → R) (a : A) (hf : ContinuousOn f (σₙ R a) := by cfc_cont_tac)
    (hg : ContinuousOn g (σₙ R a) := by cfc_cont_tac) (hf0 : f 0 = 0 := by cfc_zero_tac)
    (hg0 : g 0 = 0 := by cfc_zero_tac) (ha : p a := by cfc_tac) :
    cfcₙ f a ≤ cfcₙ g a ↔ ∀ x ∈ σₙ R a, f x ≤ g x := by
  rw [cfcₙ_apply f a, cfcₙ_apply g a, cfcₙHom_le_iff (show p a from ha), ContinuousMapZero.le_def]
  simp
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
lemma cfcₙ_nonpos_iff (f : R → R) (a : A) (hf : ContinuousOn f (σₙ R a) := by cfc_cont_tac)
    (h0 : f 0 = 0 := by cfc_zero_tac) (ha : p a := by cfc_tac) :
    cfcₙ f a ≤ 0 ↔ ∀ x ∈ σₙ R a, f x ≤ 0 := by
  simp_rw [← neg_nonneg, ← cfcₙ_neg]
  exact cfcₙ_nonneg_iff (fun x ↦ -f x) a

end Ring

end Order

/-! ### `cfcₙHom` on a superset of the quasispectrum -/

section Superset

open ContinuousMapZero

variable {R A : Type*} {p : A → Prop} [CommSemiring R] [Nontrivial R] [StarRing R]
    [MetricSpace R] [IsTopologicalSemiring R] [ContinuousStar R] [NonUnitalRing A] [StarRing A]
    [TopologicalSpace A] [Module R A] [IsScalarTower R A A] [SMulCommClass R A A]
    [instCFCₙ : NonUnitalContinuousFunctionalCalculus R A p]

/-- The composition of `cfcₙHom` with the natural embedding `C(s, R)₀ → C(quasispectrum R a, R)₀`
whenever `quasispectrum R a ⊆ s`.

This is sometimes necessary in order to consider the same continuous functions applied to multiple
distinct elements, with the added constraint that `cfcₙ` does not suffice. This can occur, for
example, if it is necessary to use uniqueness of this continuous functional calculus. A practical
/-
**can** 是 Mathlib 中的一个示例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
example can be found in the proof of `CFC.posPart_negPart_unique`. -/
@[simps!]
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
The composition of `cfcₙHom` with the natural embedding `C(s, R)₀ → C(quasispect
rum R a, R)₀`
whenever `quasispectrum R a ⊆ s`.

This is sometimes necessary in order to consider the same continuous functions a
pplied to multiple
distinct elements, with the added constraint that `cfcₙ` does not suffice. This 
can occur, for
example, if it is necessary to use uniqueness of this continuous functional calc
ulus. A practical
example can be found in the proof of `CFC.posPart_negPart_unique`.
-/
noncomputable def cfcₙHomSuperset {a : A} (ha : p a) {s : Set R} (hs : σₙ R a ⊆ s) :
    haveI : Fact (0 ∈ s) := ⟨hs (quasispectrum.zero_mem R a)⟩
    C(s, R)₀ →⋆ₙₐ[R] A :=
  have : Fact (0 ∈ s) := ⟨hs (quasispectrum.zero_mem R a)⟩
  cfcₙHom ha (R := R) |>.comp <| ContinuousMapZero.nonUnitalStarAlgHom_precomp R <|
    ⟨⟨_, continuous_id.subtype_map hs⟩, rfl⟩
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
lemma cfcₙHomSuperset_continuous {a : A} (ha : p a) {s : Set R} (hs : σₙ R a ⊆ s) :
    Continuous (cfcₙHomSuperset ha hs) :=
  have : Fact (0 ∈ s) := ⟨hs (quasispectrum.zero_mem R a)⟩
  (cfcₙHom_continuous ha).comp <| ContinuousMapZero.continuous_precomp _
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
lemma cfcₙHomSuperset_id {a : A} (ha : p a) {s : Set R} (hs : σₙ R a ⊆ s) :
    haveI : Fact (0 ∈ s) := ⟨hs (quasispectrum.zero_mem R a)⟩
    cfcₙHomSuperset ha hs (.id s) = a :=
  cfcₙHom_id ha

end Superset

section IsClosedEmbedding

/-- A class for the non-unital continuous functional calculus which requires the homomorphisms
`C(quasispectrum R a, R)₀ → A` to be closed embeddings, as opposed to only continuous and injective.
The primary advantage of this is that one can conclude the range of this map is the non-unital
closed star subalgebra generated by `a`. However, unless the topology on `A` is induced by a
C⋆-norm, this is unlikely to occur. -/
/-
**NonUnitalClosedEmbeddingContinuousFunctionalCalculus** 是 Mathlib 中的一个类，位于命名空间 
``。
形式化陈述：NonUnitalClosedEmbeddingContinuousFunctionalCalculus (R A : Type*) (p : ou
tParam (A -> Prop)) [CommSemiring R] [Nontrivial R] [StarRing R] [MetricSpace R]
 [IsTopologicalSemiring R] [ContinuousStar R] [NonUnitalRing A] [StarRing A] [To
pologicalSpace A] [Module R A] [IsScalarTower R A A] [SMulCommClass R A A] exten
ds NonUnitalContinuousFunctionalCalculus R A p where isClosedEmbedding (a : A) (
ha : p a) : Topology.IsClosedEmbedding (cfcₙHom (R
参数：R A : Type*；p : outParam (A -> Prop)；a : A；ha : p a。
继承自：NonUnitalContinuousFunctionalCalculus R A p。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A class for the non-unital continuous functional calculus which requires the hom
omorphisms
`C(quasispectrum R a, R)₀ → A` to be closed embeddings, as opposed to only conti
nuous and injective.
The primary advantage of this is that one can conclude the range of this map is 
the non-unital
closed star subalgebra generated by `a`. However, unless the topology on `A` is 
induced by a
C⋆-norm, this is unlikely to occur.
-/
class NonUnitalClosedEmbeddingContinuousFunctionalCalculus (R A : Type*)
    (p : outParam (A → Prop)) [CommSemiring R] [Nontrivial R] [StarRing R] [MetricSpace R]
    [IsTopologicalSemiring R] [ContinuousStar R] [NonUnitalRing A] [StarRing A] [TopologicalSpace A]
    [Module R A] [IsScalarTower R A A] [SMulCommClass R A A] extends
    NonUnitalContinuousFunctionalCalculus R A p where
  isClosedEmbedding (a : A) (ha : p a) : Topology.IsClosedEmbedding (cfcₙHom (R := R) ha)

open scoped NonUnitalContinuousFunctionalCalculus in
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
lemma cfcₙHom_isClosedEmbedding {R A : Type*} {p : A → Prop} [CommSemiring R] [Nontrivial R]
    [StarRing R] [MetricSpace R] [IsTopologicalSemiring R] [ContinuousStar R] [NonUnitalRing A]
    [StarRing A] [TopologicalSpace A] [Module R A] [IsScalarTower R A A] [SMulCommClass R A A]
    [instCFC : NonUnitalClosedEmbeddingContinuousFunctionalCalculus R A p]
    {a : A} (ha : p a) :
    IsClosedEmbedding <| (cfcₙHom ha : C(σₙ R a, R)₀ →⋆ₙₐ[R] A) :=
  NonUnitalClosedEmbeddingContinuousFunctionalCalculus.isClosedEmbedding a ha

end IsClosedEmbedding

/-! ### Obtain a non-unital continuous functional calculus from a unital one -/

section UnitalToNonUnital

open ContinuousMapZero Set Uniformity ContinuousMap

variable {R A : Type*} {p : A → Prop} [Semifield R] [StarRing R] [MetricSpace R]
variable [IsTopologicalSemiring R] [ContinuousStar R] [Ring A] [StarRing A] [TopologicalSpace A]
variable [Algebra R A]

variable (R) in
/-- The non-unital continuous functional calculus obtained by restricting a unital calculus
to functions that map zero to zero. This is an auxiliary definition and is not
intended for use outside this file. The equality between the non-unital and unital
calculi in this case is encoded in the lemma `cfcₙ_eq_cfc`. -/
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
The non-unital continuous functional calculus obtained by restricting a unital c
alculus
to functions that map zero to zero. This is an auxiliary definition and is not
intended for use outside this file. The equality between the non-unital and unit
al
calculi in this case is encoded in the lemma `cfcₙ_eq_cfc`.
-/
noncomputable def cfcₙHom_of_cfcHom [ContinuousFunctionalCalculus R A p] {a : A} (ha : p a) :
    C(σₙ R a, R)₀ →⋆ₙₐ[R] A :=
  let e := ContinuousMapZero.toContinuousMapHom (X := σₙ R a) (R := R)
  let f : C(spectrum R a, quasispectrum R a) :=
    ⟨_, continuous_inclusion <| spectrum_subset_quasispectrum R a⟩
  let ψ := ContinuousMap.compStarAlgHom' R R f
  (cfcHom ha (R := R) : C(spectrum R a, R) →⋆ₙₐ[R] A).comp <|
    (ψ : C(σₙ R a, R) →⋆ₙₐ[R] C(spectrum R a, R)).comp e
/-
**continuous_cfc** 是 Mathlib 中的一个引理，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma continuous_cfcₙHom_of_cfcHom [ContinuousFunctionalCalculus R A p] {a : A} (ha : p a) :
    Continuous (cfcₙHom_of_cfcHom R ha) :=
  (cfcHom_continuous ha).comp <| (ContinuousMap.continuous_precomp _).comp <| by fun_prop
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
lemma cfcₙHom_of_cfcHom_injective [ContinuousFunctionalCalculus R A p] {a : A} (ha : p a) :
    Function.Injective (cfcₙHom_of_cfcHom R ha) := by
  refine (cfcHom_injective ha).comp fun f g h ↦ ?_
  ext x
  obtain rfl | hx := eq_or_ne x 0
  · simp
  · have := by simpa [quasispectrum_eq_spectrum_union_zero] using x.prop
    replace := this.resolve_left (Subtype.val_injective.ne_iff.mpr hx)
    congrm($h ⟨x, this⟩)
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
lemma cfcₙHom_of_cfcHom_map_quasispectrum [ContinuousFunctionalCalculus R A p] {a : A} (ha : p a) :
    ∀ f : C(σₙ R a, R)₀, σₙ R (cfcₙHom_of_cfcHom R ha f) = range f := by
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
      push _ ∈ _ at hx ⊢
      rw [show x = 0 from Subtype.val_injective hx, map_zero]

-- gives access to the `ContinuousFunctionalCalculus.compactSpace_spectrum` instance
open scoped ContinuousFunctionalCalculus
/-
**isClosedEmbedding_cfc** 是 Mathlib 中的一个引理，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma isClosedEmbedding_cfcₙHom_of_cfcHom [ClosedEmbeddingContinuousFunctionalCalculus R A p]
    [CompleteSpace R] {a : A} (ha : p a) :
    IsClosedEmbedding (cfcₙHom_of_cfcHom R ha) := by
  let f : C(spectrum R a, σₙ R a) :=
    ⟨_, continuous_inclusion <| spectrum_subset_quasispectrum R a⟩
  refine (cfcHom_isClosedEmbedding ha).comp <|
    (IsUniformInducing.isUniformEmbedding ⟨?_⟩).isClosedEmbedding
  have := uniformSpace_eq_inf_precomp_of_cover (β := R) f (0 : C(Unit, σₙ R a))
    (map_continuous f).isProperMap (map_continuous 0).isProperMap <| by
      simp only [← Subtype.val_injective.image_injective.eq_iff, f, ContinuousMap.coe_mk,
        ContinuousMap.coe_zero, range_zero, image_union, image_singleton,
        quasispectrum.coe_zero, ← range_comp, val_comp_inclusion, image_univ, Subtype.range_coe,
        quasispectrum_eq_spectrum_union_zero]
  simp_rw +instances [← isUniformEmbedding_toContinuousMap.comap_uniformity, this,
    @inf_uniformity _ (.comap _ _) (.comap _ _), uniformity_comap, Filter.comap_inf,
    Filter.comap_comap]
  refine .symm <| inf_eq_left.mpr <| le_top.trans <| eq_top_iff.mp ?_
  have : ∀ U ∈ 𝓤 (C(Unit, R)), (0, 0) ∈ U := fun U hU ↦ refl_mem_uniformity hU
  convert! Filter.comap_const_of_mem this with ⟨u, v⟩ <;>
  ext ⟨x, rfl⟩ <;> [exact map_zero u; exact map_zero v]
/-
**ContinuousFunctionalCalculus.toNonUnital** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：ContinuousFunctionalCalculus.toNonUnital [ContinuousFunctionalCalculus R A
 p] : NonUnitalContinuousFunctionalCalculus R A p where predicate_zero
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `IsDomain.toNontrivial`：∀ {α : Type u} {inst : Semiring α} [self : IsDoma
in α], Nontrivial α
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用引理 `cfc_predicate_zero`：cfc_predicate_zero : p 0
· 使用定理 `ContinuousFunctionalCalculus.compactSpace_spectrum`：∀ {R : Type u_1} {A 
: Type u_2} {p : outParam (A → Prop)} {inst : CommSemiring R} {inst_1 : StarRing
 R}   {inst_2 : MetricSpace R} {inst_3 :…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `quasispectrum_eq_spectrum_union_zero`：quasispectrum_eq_spectrum_union_ze
ro (R : Type*) {A : Type*} [Semifield R] [Ring A] [Algebra R A] (a : A) : quasis
pectrum R a = spectrum R a…
· 使用定理 `IsCompact.union`：IsCompact.union (hs : IsCompact s) (ht : IsCompact t) :
 IsCompact (s union t)
· 使用定理 `isCompact_singleton`：isCompact_singleton {x : X} : IsCompact ({x} : Set 
X)
· 使用定理 `IsSemitopologicalSemiring.toContinuousAdd`：∀ {R : Type u_2} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSemitopologic
alSemiring R], ContinuousAdd R
· 使用定理 `IsTopologicalSemiring.toIsSemitopologicalSemiring`：∀ (R : Type u_2) [ins
t : TopologicalSpace R] [inst_1 : NonUnitalNonAssocSemiring R] [IsTopologicalSem
iring R],   IsSemitopologicalSemiring R
· 使用定理 `IsSemitopologicalSemiring.toSeparatelyContinuousMul`：∀ {R : Type u_2} {i
nst : TopologicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSem
itopologicalSemiring R], SeparatelyContin…
· 使用引理 `continuous_cfcₙHom_of_cfcHom`：continuous_cfcₙHom_of_cfcHom [ContinuousFu
nctionalCalculus R A p] {a : A} (ha : p a) : Continuous (cfcₙHom_of_cfcHom R ha)
· 使用引理 `cfcₙHom_of_cfcHom_injective`：cfcₙHom_of_cfcHom_injective [ContinuousFunc
tionalCalculus R A p] {a : A} (ha : p a) : Function.Injective (cfcₙHom_of_cfcHom
 R ha)
· 使用引理 `cfcHom_id`：cfcHom_id : cfcHom ha ((ContinuousMap.id R).restrict <| spect
rum R a) = a
· 使用引理 `cfcₙHom_of_cfcHom_map_quasispectrum`：cfcₙHom_of_cfcHom_map_quasispectrum
 [ContinuousFunctionalCalculus R A p] {a : A} (ha : p a) : forall f : C(σₙ R a, 
R)₀, σₙ R (cfcₙHom_of_cfc…
· 使用引理 `cfcHom_predicate`：cfcHom_predicate (f : C(spectrum R a, R)) : p (cfcHom 
ha f)
-/
instance ContinuousFunctionalCalculus.toNonUnital [ContinuousFunctionalCalculus R A p] :
    NonUnitalContinuousFunctionalCalculus R A p where
  predicate_zero := cfc_predicate_zero R
  compactSpace_quasispectrum a := by
    have h_cpct : CompactSpace (spectrum R a) := inferInstance
    simp only [← isCompact_iff_compactSpace, quasispectrum_eq_spectrum_union_zero] at h_cpct ⊢
    exact h_cpct |>.union isCompact_singleton
  exists_cfc_of_predicate _ ha :=
    ⟨cfcₙHom_of_cfcHom R ha,
      continuous_cfcₙHom_of_cfcHom ha,
      cfcₙHom_of_cfcHom_injective ha,
      cfcHom_id ha,
      cfcₙHom_of_cfcHom_map_quasispectrum ha,
      fun _ ↦ cfcHom_predicate ha _⟩

open scoped NonUnitalContinuousFunctionalCalculus in
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
lemma cfcₙHom_eq_cfcₙHom_of_cfcHom [ContinuousFunctionalCalculus R A p]
    [ContinuousMapZero.UniqueHom R A] {a : A} (ha : p a) :
    cfcₙHom ha = cfcₙHom_of_cfcHom R ha :=
  cfcₙHom_eq_of_continuous_of_map_id ha _ (continuous_cfcₙHom_of_cfcHom ha) <| by
    simpa only [cfcₙHom_id ha] using! cfcHom_id ha

/-- When `cfc` is applied to a function that maps zero to zero, it is equivalent to using
`cfcₙ`. -/
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
When `cfc` is applied to a function that maps zero to zero, it is equivalent to 
using
`cfcₙ`.
-/
lemma cfcₙ_eq_cfc [ContinuousFunctionalCalculus R A p] [ContinuousMapZero.UniqueHom R A] {f : R → R}
    {a : A} (hf : ContinuousOn f (σₙ R a) := by cfc_cont_tac) (hf0 : f 0 = 0 := by cfc_zero_tac) :
    cfcₙ f a = cfc f a := by
  by_cases ha : p a
  · have hf' := hf.mono <| spectrum_subset_quasispectrum R a
    rw [cfc_apply f a ha hf', cfcₙ_apply f a hf, cfcₙHom_eq_cfcₙHom_of_cfcHom, cfcₙHom_of_cfcHom]
    dsimp only [NonUnitalStarAlgHom.comp_apply,
      NonUnitalStarAlgHom.coe_coe, compStarAlgHom'_apply]
    congr
  · simp [cfc_apply_of_not_predicate a ha, cfcₙ_apply_of_not_predicate (R := R) a ha]
/-
**ClosedEmbeddingContinuousFunctionalCalculus.toNonUnital** 是 Mathlib 中的一个实例，位于命
名空间 ``。
形式化陈述：ClosedEmbeddingContinuousFunctionalCalculus.toNonUnital [ClosedEmbeddingCo
ntinuousFunctionalCalculus R A p] [ContinuousMapZero.UniqueHom R A] [CompleteSpa
ce R] : NonUnitalClosedEmbeddingContinuousFunctionalCalculus R A p where isClose
dEmbedding a ha
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `IsDomain.toNontrivial`：∀ {α : Type u} {inst : Semiring α} [self : IsDoma
in α], Nontrivial α
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `ClosedEmbeddingContinuousFunctionalCalculus.toContinuousFunctionalCalcul
us`：∀ {R : Type u_1} {A : Type u_2} {p : outParam (A → Prop)} {inst : CommSemiri
ng R} {inst_1 : StarRing R}   {inst_2 : MetricSpace R} {inst_3 :…
· 使用定理 `IsSemitopologicalSemiring.toContinuousAdd`：∀ {R : Type u_2} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSemitopologic
alSemiring R], ContinuousAdd R
· 使用定理 `IsTopologicalSemiring.toIsSemitopologicalSemiring`：∀ (R : Type u_2) [ins
t : TopologicalSpace R] [inst_1 : NonUnitalNonAssocSemiring R] [IsTopologicalSem
iring R],   IsSemitopologicalSemiring R
· 使用定理 `IsSemitopologicalSemiring.toSeparatelyContinuousMul`：∀ {R : Type u_2} {i
nst : TopologicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSem
itopologicalSemiring R], SeparatelyContin…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `cfcₙHom_eq_cfcₙHom_of_cfcHom`：cfcₙHom_eq_cfcₙHom_of_cfcHom [ContinuousFu
nctionalCalculus R A p] [ContinuousMapZero.UniqueHom R A] {a : A} (ha : p a) : c
fcₙHom ha = cfcₙHo…
· 使用引理 `isClosedEmbedding_cfcₙHom_of_cfcHom`：isClosedEmbedding_cfcₙHom_of_cfcHom
 [ClosedEmbeddingContinuousFunctionalCalculus R A p] [CompleteSpace R] {a : A} (
ha : p a) : IsClosedEmbed…
-/
instance ClosedEmbeddingContinuousFunctionalCalculus.toNonUnital
    [ClosedEmbeddingContinuousFunctionalCalculus R A p] [ContinuousMapZero.UniqueHom R A]
    [CompleteSpace R] : NonUnitalClosedEmbeddingContinuousFunctionalCalculus R A p where
  isClosedEmbedding a ha := by
    rw [cfcₙHom_eq_cfcₙHom_of_cfcHom (R := R) ha]
    exact isClosedEmbedding_cfcₙHom_of_cfcHom ha

end UnitalToNonUnital

