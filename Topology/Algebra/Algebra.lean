/-
Copyright (c) 2021 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison, Antoine Chambert-Loir, María Inés de Frutos-Fernández
-/
module

public import Mathlib.Algebra.Algebra.Subalgebra.Lattice
public import Mathlib.Algebra.Algebra.Tower
public import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Basic
public import Mathlib.Algebra.Order.Interval.Set.Instances

/-!
# Topological (sub)algebras

A topological algebra over a topological semiring `R` is a topological semiring with a compatible
continuous scalar multiplication by elements of `R`. We reuse typeclass `ContinuousSMul` for
topological algebras.

## Results

The topological closure of a subalgebra is still a subalgebra, which as an algebra is a
topological algebra.

In this file we define continuous algebra homomorphisms, as algebra homomorphisms between
topological (semi-)rings which are continuous. The type `ContinuousAlgHom R A B` of continuous
algebra homomorphisms between the topological `R`-algebras `A` and `B` is denoted by `A →A[R] B`.

See also `ContinuousAlgEquiv R A B`, denoted by `A ≃A[R] B`, for the type of isomorphisms between
the topological `R`-algebras `A` and `B`.

-/

@[expose] public section

assert_not_exists Module.Basis

open Algebra Set TopologicalSpace Topology

universe u v w

section TopologicalAlgebra

variable (R : Type*) (A : Type u)
variable [CommSemiring R] [Semiring A] [Algebra R A]
variable [TopologicalSpace R] [TopologicalSpace A]

@[continuity, fun_prop]
/--
theorem `continuous_algebraMap` / 定理 `continuous_algebraMap`

English:
theorem continuous_algebraMap
  given: [ContinuousSMul R A]
  statement: Continuous (algebraMap R A)
  proof: by
  rw [algebraMap_eq_smul_one']
  fun_prop

中文:
定理 continuous_algebraMap
  条件: [连续标量乘法 R A]
  结论: 连续 (algebraMap R A)
  证明: by
  rw [algebraMap_eq_smul_one']
  fun_prop

Depends on / 依赖: algebraMap_eq_smul_one, fun_prop
-/
theorem continuous_algebraMap [ContinuousSMul R A] : Continuous (algebraMap R A) := by
  rw [algebraMap_eq_smul_one']
  fun_prop

/--
theorem `continuous_algebraMap_iff_smul` / 定理 `continuous_algebraMap_iff_smul`

English:
theorem continuous_algebraMap_iff_smul
  given: [ContinuousMul A]
  proof: by
  refine ⟨fun h => ?_, fun h => have : ContinuousSMul R A := ⟨h⟩; continuous_algebraMap _ _⟩
  simp only [Algebra.smul_def]
  exact (h.comp continuous_fst).mul continuous_snd

中文:
定理 continuous_algebraMap_iff_smul
  条件: [连续乘法 A]
  证明: by
  refine ⟨fun h => ?_, fun h => have : ContinuousSMul R A := ⟨h⟩; continuous_algebraMap _ _⟩
  simp only [Algebra.smul_def]
  exact (h.comp continuous_fst).mul continuous_snd

Depends on / 依赖: Algebra, Algebra.smul_def, ContinuousSMul, continuous_algebraMap, continuous_fst, continuous_snd, h.comp, smul_def
-/
theorem continuous_algebraMap_iff_smul [ContinuousMul A] :
    Continuous (algebraMap R A) ↔ Continuous fun p : R × A => p.1 • p.2 := by
  refine ⟨fun h => ?_, fun h => have : ContinuousSMul R A := ⟨h⟩; continuous_algebraMap _ _⟩
  simp only [Algebra.smul_def]
  exact (h.comp continuous_fst).mul continuous_snd

/--
theorem `continuousSMul_of_algebraMap` / 定理 `continuousSMul_of_algebraMap`

English:
theorem continuousSMul_of_algebraMap
  given: [ContinuousMul A] (h : Continuous (algebraMap R A))
  proof: ⟨(continuous_algebraMap_iff_smul R A).1 h⟩

中文:
定理 continuousSMul_of_algebraMap
  条件: [连续乘法 A] (h : 连续 (algebraMap R A))
  证明: ⟨(continuous_algebraMap_iff_smul R A).1 h⟩

Depends on / 依赖: continuous_algebraMap_iff_smul
-/
theorem continuousSMul_of_algebraMap [ContinuousMul A] (h : Continuous (algebraMap R A)) :
    ContinuousSMul R A :=
  ⟨(continuous_algebraMap_iff_smul R A).1 h⟩

/--
Instance `Subalgebra.continuousSMul` / 实例 `Subalgebra.continuousSMul`

English:
instance Subalgebra.continuousSMul
  signature: (S : Subalgebra R A) (X) [TopologicalSpace X] [MulAction A X]
  body: Subsemiring.continuousSMul S.toSubsemiring X

中文:
实例 子代数.continuousSMul
  签名: (S : 子代数 R A) (X) [拓扑空间 X] [乘法作用 A X]
  定义体: Subsemiring.continuousSMul S.toSubsemiring X

Depends on / 依赖: S.toSubsemiring, Subsemiring, Subsemiring.continuousSMul, continuousSMul, toSubsemiring
-/
instance Subalgebra.continuousSMul (S : Subalgebra R A) (X) [TopologicalSpace X] [MulAction A X]
    [ContinuousSMul A X] : ContinuousSMul S X :=
  Subsemiring.continuousSMul S.toSubsemiring X

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [PartialOrder
  signature: A] [IsOrderedRing A] [ContinuousMul A] :
  body: Topology.IsInducing.subtypeVal.continuousMul Icc.coeMonoidWithZeroHom

中文:
实例 [偏序
  签名: A] [是Ordered环 A] [连续乘法 A] :
  定义体: Topology.IsInducing.subtypeVal.continuousMul Icc.coeMonoidWithZeroHom

Depends on / 依赖: Icc.coeMonoidWithZeroHom, IsInducing, Topology, Topology.IsInducing.subtypeVal.continuousMul, coeMonoidWithZeroHom, continuousMul, subtypeVal
-/
instance [PartialOrder A] [IsOrderedRing A] [ContinuousMul A] :
    ContinuousMul (Icc (0 : A) 1) :=
  Topology.IsInducing.subtypeVal.continuousMul Icc.coeMonoidWithZeroHom

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [PartialOrder
  signature: A] [IsOrderedRing A] [ContinuousMul A] :
  body: Topology.IsInducing.subtypeVal.continuousMul Ico.coeMulHom

中文:
实例 [偏序
  签名: A] [是Ordered环 A] [连续乘法 A] :
  定义体: Topology.IsInducing.subtypeVal.continuousMul Ico.coeMulHom

Depends on / 依赖: Ico.coeMulHom, IsInducing, Topology, Topology.IsInducing.subtypeVal.continuousMul, coeMulHom, continuousMul, subtypeVal
-/
instance [PartialOrder A] [IsOrderedRing A] [ContinuousMul A] :
    ContinuousMul (Ico (0 : A) 1) :=
  Topology.IsInducing.subtypeVal.continuousMul Ico.coeMulHom

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [PartialOrder
  signature: A] [IsStrictOrderedRing A] [ContinuousMul A] :
  body: Topology.IsInducing.subtypeVal.continuousMul Ioc.coeMonoidHom

中文:
实例 [偏序
  签名: A] [是StrictOrdered环 A] [连续乘法 A] :
  定义体: Topology.IsInducing.subtypeVal.continuousMul Ioc.coeMonoidHom

Depends on / 依赖: Ioc.coeMonoidHom, IsInducing, Sum.uniformity, Topology, Topology.IsInducing.subtypeVal.continuousMul, coeMonoidHom, continuousMul, infer_instance, subtypeVal, uniformity
-/
instance [PartialOrder A] [IsStrictOrderedRing A] [ContinuousMul A] :
    ContinuousMul (Ioc (0 : A) 1) :=
  Topology.IsInducing.subtypeVal.continuousMul Ioc.coeMonoidHom

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [PartialOrder
  signature: A] [IsStrictOrderedRing A] [ContinuousMul A] :
  body: Topology.IsInducing.subtypeVal.continuousMul Ioo.coeMulHom

中文:
实例 [偏序
  签名: A] [是StrictOrdered环 A] [连续乘法 A] :
  定义体: Topology.IsInducing.subtypeVal.continuousMul Ioo.coeMulHom

Depends on / 依赖: Ioo.coeMulHom, IsInducing, Topology, Topology.IsInducing.subtypeVal.continuousMul, coeMulHom, continuousMul, subtypeVal
-/
instance [PartialOrder A] [IsStrictOrderedRing A] [ContinuousMul A] :
    ContinuousMul (Ioo (0 : A) 1) :=
  Topology.IsInducing.subtypeVal.continuousMul Ioo.coeMulHom

section
variable [ContinuousSMul R A]

/-- The inclusion of the base ring in a topological algebra as a continuous linear map. -/
@[simps]
/--
Definition of `algebraMapCLM` / `algebraMapCLM` 的定义

English:
definition algebraMapCLM
  signature: : R ->L[R] A
  body: { Algebra.linearMap R A with
    toFun := algebraMap R A }

中文:
定义 algebraMapCLM
  签名: : R ->L[R] A
  定义体: { Algebra.linearMap R A with
    toFun := algebraMap R A }

Depends on / 依赖: Algebra, Algebra.linearMap, algebraMap, linearMap
-/
def algebraMapCLM : R ->L[R] A :=
  { Algebra.linearMap R A with
    toFun := algebraMap R A }

/--
theorem `coe_algebraMapCLM` / 定理 `coe_algebraMapCLM`

English:
theorem coe_algebraMapCLM
  statement: ⇑(algebraMapCLM R A) = algebraMap R A
  proof: rfl

中文:
定理 coe_algebraMapCLM
  结论: ⇑(algebraMapCLM R A) = algebraMap R A
  证明: rfl
-/
theorem coe_algebraMapCLM : ⇑(algebraMapCLM R A) = algebraMap R A :=
  rfl

/--
theorem `toLinearMap_algebraMapCLM` / 定理 `toLinearMap_algebraMapCLM`

English:
theorem toLinearMap_algebraMapCLM
  statement: (algebraMapCLM R A).toLinearMap = Algebra.linearMap R A
  proof: rfl

中文:
定理 toLinearMap_algebraMapCLM
  结论: (algebraMapCLM R A).toLinearMap = 代数.linearMap R A
  证明: rfl

Depends on / 依赖: ContinuousAt, tendsto_nhds_left
-/
theorem toLinearMap_algebraMapCLM : (algebraMapCLM R A).toLinearMap = Algebra.linearMap R A :=
  rfl

/--
lemma `ContinuousLinearMap.toSpanSingleton_one_eq_algebraMapCLM` / 引理 `ContinuousLinearMap.toSpanSingleton_one_eq_algebraMapCLM`

English:
lemma ContinuousLinearMap.toSpanSingleton_one_eq_algebraMapCLM
  proof: by
  ext; simp

中文:
引理 连续线性映射.toSpanSingleton_one_eq_algebraMapCLM
  证明: by
  ext; simp

Depends on / 依赖: algebraMapCLM
-/
lemma ContinuousLinearMap.toSpanSingleton_one_eq_algebraMapCLM :
    toSpanSingleton R (M₁ := A) 1 = algebraMapCLM R A := by
  ext; simp

end

/--
theorem `DiscreteTopology.instContinuousSMul` / 定理 `DiscreteTopology.instContinuousSMul`

English:
theorem DiscreteTopology.instContinuousSMul
  given: [IsTopologicalSemiring A] [DiscreteTopology R]
  proof: continuousSMul_of_algebraMap _ _ continuous_of_discreteTopology

中文:
定理 离散拓扑.instContinuousSMul
  条件: [是TopologicalSemiring A] [离散拓扑 R]
  证明: continuousSMul_of_algebraMap _ _ continuous_of_discreteTopology

Depends on / 依赖: continuousSMul_of_algebraMap, continuous_of_discreteTopology
-/
theorem DiscreteTopology.instContinuousSMul [IsTopologicalSemiring A] [DiscreteTopology R] :
    ContinuousSMul R A := continuousSMul_of_algebraMap _ _ continuous_of_discreteTopology

end TopologicalAlgebra

section TopologicalAlgebra

section

variable (R : Type*) [CommSemiring R]
  (A : Type*) [Semiring A]

/--
Definition of `ContinuousAlgHom` / `ContinuousAlgHom` 的定义

English:
structure ContinuousAlgHom
  parameters: (R : Type*) [CommSemiring R] (A : Type*) [Semiring A]
  extends: A ->ₐ[R] B
  axioms and operations (1):
    - cont : Continuous toFun  [default: by fun_prop]

中文:
结构 余ntinuousAlg态射
  参数: (R : 类型) [交换半环 R] (A : 类型) [半环 A]
  继承: A ->ₐ[R] B
  公理与运算 (1 个):
    - cont : 连续 toFun  [默认: by fun_prop]

Depends on / 依赖: ContinuousWithinAt, fun_prop, tendsto_nhds_left
-/
structure ContinuousAlgHom (R : Type*) [CommSemiring R] (A : Type*) [Semiring A]
    [TopologicalSpace A] (B : Type*) [Semiring B] [TopologicalSpace B] [Algebra R A] [Algebra R B]
    extends A ->ₐ[R] B where
  cont : Continuous toFun := by fun_prop

@[inherit_doc]
notation:25 A " ->A[" R "] " B => ContinuousAlgHom R A B

namespace ContinuousAlgHom

open Subalgebra

section Semiring

variable {R} {A}
variable [TopologicalSpace A]

variable {B : Type*} [Semiring B] [TopologicalSpace B] [Algebra R A] [Algebra R B]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: FunLike (A ->A[R] B) A B
  body: f.toAlgHom
  coe_injective f g h := by
    cases f; cases g
    simp only [mk.injEq]
    exact AlgHom.ext (congrFun h)

中文:
实例 :
  签名: 函数状 (A ->A[R] B) A B
  定义体: f.toAlgHom
  coe_injective f g h := by
    cases f; cases g
    simp only [mk.injEq]
    exact AlgHom.ext (congrFun h)

Depends on / 依赖: f.toAlgHom, toAlgHom
-/
instance : FunLike (A ->A[R] B) A B where
  coe f := f.toAlgHom
  coe_injective f g h := by
    cases f; cases g
    simp only [mk.injEq]
    exact AlgHom.ext (congrFun h)

set_option linter.style.whitespace false in -- manual alignment is not recognised
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: AlgHomClass (A ->A[R] B) R A B
  body: map_mul f.toAlgHom x y
  map_one f := map_one f.toAlgHom
  map_add f := map_add f.toAlgHom
  map_zero f := map_zero f.toAlgHom
  commutes f r := f.toAlgHom.commutes r

中文:
实例 :
  签名: 代数态射类 (A ->A[R] B) R A B
  定义体: map_mul f.toAlgHom x y
  map_one f := map_one f.toAlgHom
  map_add f := map_add f.toAlgHom
  map_zero f := map_zero f.toAlgHom
  commutes f r := f.toAlgHom.commutes r

Depends on / 依赖: ContinuousOn, _left, continuousWithinAt_iff, f.toAlgHom, map_mul, toAlgHom
-/
instance : AlgHomClass (A ->A[R] B) R A B where
  map_mul f x y := map_mul f.toAlgHom x y
  map_one f := map_one f.toAlgHom
  map_add f := map_add f.toAlgHom
  map_zero f := map_zero f.toAlgHom
  commutes f r := f.toAlgHom.commutes r

attribute [coe] ContinuousAlgHom.toAlgHom

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Coe (A ->A[R] B) (A ->ₐ[R] B)
  body: toAlgHom

@[deprecated "Now a syntactic equality" (since := "2026-04-29"), nolint synTaut]

中文:
实例 :
  签名: Coe (A ->A[R] B) (A ->ₐ[R] B)
  定义体: toAlgHom

@[deprecated "Now a syntactic equality" (since := "2026-04-29"), nolint synTaut]

Depends on / 依赖: toAlgHom
-/
instance : Coe (A ->A[R] B) (A ->ₐ[R] B) where coe := toAlgHom

@[deprecated "Now a syntactic equality" (since := "2026-04-29"), nolint synTaut]
/--
theorem `toAlgHom_eq_coe` / 定理 `toAlgHom_eq_coe`

English:
theorem toAlgHom_eq_coe
  given: (f : A ->A[R] B)
  statement: f.toAlgHom = f
  proof: rfl

@[simp, norm_cast]

中文:
定理 toAlgHom_eq_coe
  条件: (f : A ->A[R] B)
  结论: f.toAlgHom = f
  证明: rfl

@[simp, norm_cast]

Depends on / 依赖: continuous_iff_continuousAt, continuous_iff_continuousAt.trans, forall_congr, tendsto_nhds_left
-/
theorem toAlgHom_eq_coe (f : A ->A[R] B) : f.toAlgHom = f := rfl

@[simp, norm_cast]
/--
theorem `coe_inj` / 定理 `coe_inj`

English:
theorem coe_inj
  given: {f g : A ->A[R] B}
  statement: (f : A ->ₐ[R] B) = g ↔ f = g
  proof: by
  cases f; cases g; simp only [mk.injEq]

中文:
定理 coe_inj
  条件: {f g : A ->A[R] B}
  结论: (f : A ->ₐ[R] B) = g ↔ f = g
  证明: by
  cases f; cases g; simp only [mk.injEq]

Depends on / 依赖: mk.injEq
-/
theorem coe_inj {f g : A ->A[R] B} : (f : A ->ₐ[R] B) = g ↔ f = g := by
  cases f; cases g; simp only [mk.injEq]

/--
theorem `coe_mk` / 定理 `coe_mk`

English:
theorem coe_mk
  given: (f : A ->ₐ[R] B) (h)
  statement: (mk f h : A ->ₐ[R] B) = f
  proof: rfl

@[simp]

中文:
定理 coe_mk
  条件: (f : A ->ₐ[R] B) (h)
  结论: (mk f h : A ->ₐ[R] B) = f
  证明: rfl

@[simp]
-/
theorem coe_mk (f : A ->ₐ[R] B) (h) : (mk f h : A ->ₐ[R] B) = f := rfl

@[simp]
/--
theorem `coe_mk'` / 定理 `coe_mk'`

English:
theorem coe_mk'
  given: (f : A ->ₐ[R] B) (h)
  statement: (mk f h : A -> B) = f
  proof: rfl

@[simp, norm_cast]

中文:
定理 coe_mk'
  条件: (f : A ->ₐ[R] B) (h)
  结论: (mk f h : A -> B) = f
  证明: rfl

@[simp, norm_cast]
-/
theorem coe_mk' (f : A ->ₐ[R] B) (h) : (mk f h : A -> B) = f := rfl

@[simp, norm_cast]
/--
theorem `coe_coe` / 定理 `coe_coe`

English:
theorem coe_coe
  given: (f : A ->A[R] B)
  statement: ⇑(f : A ->ₐ[R] B) = f
  proof: rfl

中文:
定理 coe_coe
  条件: (f : A ->A[R] B)
  结论: ⇑(f : A ->ₐ[R] B) = f
  证明: rfl
-/
theorem coe_coe (f : A ->A[R] B) : ⇑(f : A ->ₐ[R] B) = f := rfl

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: ContinuousMapClass (A ->A[R] B) A B
  body: f.2

@[fun_prop]

中文:
实例 :
  签名: 连续映射类 (A ->A[R] B) A B
  定义体: f.2

@[fun_prop]
-/
instance : ContinuousMapClass (A ->A[R] B) A B where
  map_continuous f := f.2

@[fun_prop]
/--
theorem `continuous` / 定理 `continuous`

English:
theorem continuous
  given: (f : A ->A[R] B)
  statement: Continuous f
  proof: f.2

中文:
定理 continuous
  条件: (f : A ->A[R] B)
  结论: 连续 f
  证明: f.2
-/
protected theorem continuous (f : A ->A[R] B) : Continuous f := f.2

/--
theorem `uniformContinuous` / 定理 `uniformContinuous`

English:
theorem uniformContinuous
  statement: {E₁ E₂ : Type*} [UniformSpace E₁] [UniformSpace E₂]
  proof: uniformContinuous_addMonoidHom_of_continuous f.continuous

中文:
定理 uniformContinuous
  结论: {E₁ E₂ : 类型} [一致空间 E₁] [一致空间 E₂]
  证明: uniformContinuous_addMonoidHom_of_continuous f.continuous
-/
protected theorem uniformContinuous {E₁ E₂ : Type*} [UniformSpace E₁] [UniformSpace E₂]
    [Ring E₁] [Ring E₂] [Algebra R E₁] [Algebra R E₂] [IsUniformAddGroup E₁]
    [IsUniformAddGroup E₂] (f : E₁ ->A[R] E₂) : UniformContinuous f :=
  uniformContinuous_addMonoidHom_of_continuous f.continuous

/--
Definition of `Simps.apply` / `Simps.apply` 的定义

English:
definition Simps.apply
  signature: (h : A ->A[R] B)
  body: h

中文:
定义 Simps.apply
  签名: (h : A ->A[R] B)
  定义体: h
-/
def Simps.apply (h : A ->A[R] B) : A -> B := h

/--
Definition of `Simps.coe` / `Simps.coe` 的定义

English:
definition Simps.coe
  signature: (h : A ->A[R] B)
  body: h

initialize_simps_projections ContinuousAlgHom (toFun -> apply, toAlgHom -> coe)

@[ext]

中文:
定义 Simps.coe
  签名: (h : A ->A[R] B)
  定义体: h

initialize_simps_projections ContinuousAlgHom (toFun -> apply, toAlgHom -> coe)

@[ext]
-/
def Simps.coe (h : A ->A[R] B) : A ->ₐ[R] B := h

initialize_simps_projections ContinuousAlgHom (toFun -> apply, toAlgHom -> coe)

@[ext]
/--
theorem `ext` / 定理 `ext`

English:
theorem ext
  given: {f g : A ->A[R] B} (h : forall x, f x = g x)
  statement: f = g
  proof: DFunLike.ext f g h

中文:
定理 ext
  条件: {f g : A ->A[R] B} (h : 对任意 x, f x = g x)
  结论: f = g
  证明: DFunLike.ext f g h

Depends on / 依赖: DFunLike, DFunLike.ext
-/
theorem ext {f g : A ->A[R] B} (h : forall x, f x = g x) : f = g := DFunLike.ext f g h

/--
Definition of `copy` / `copy` 的定义

English:
definition copy
  signature: (f : A ->A[R] B) (f' : A -> B) (h : f' = ⇑f)
  body: {
    toRingHom := (f : A ->A[R] B).toRingHom.copy f' h
    commutes' := fun r => by
      simp only [AlgHom.toRingHom_eq_coe, h, RingHom.toMonoidHom_eq_coe, OneHom.toFun_eq_coe,
        MonoidHom.toOneHom_coe, MonoidHom.coe_coe, RingHom.coe_copy, AlgHomClass.commutes f r] }
  cont := show Continuou

中文:
定义 copy
  签名: (f : A ->A[R] B) (f' : A -> B) (h : f' = ⇑f)
  定义体: {
    toRingHom := (f : A ->A[R] B).toRingHom.copy f' h
    commutes' := fun r => by
      simp only [AlgHom.toRingHom_eq_coe, h, RingHom.toMonoidHom_eq_coe, OneHom.toFun_eq_coe,
        MonoidHom.toOneHom_coe, MonoidHom.coe_coe, RingHom.coe_copy, AlgHomClass.commutes f r] }
  cont := show Continuou
-/
def copy (f : A ->A[R] B) (f' : A -> B) (h : f' = ⇑f) : A ->A[R] B where
  toAlgHom := {
    toRingHom := (f : A ->A[R] B).toRingHom.copy f' h
    commutes' := fun r => by
      simp only [AlgHom.toRingHom_eq_coe, h, RingHom.toMonoidHom_eq_coe, OneHom.toFun_eq_coe,
        MonoidHom.toOneHom_coe, MonoidHom.coe_coe, RingHom.coe_copy, AlgHomClass.commutes f r] }
  cont := show Continuous f' from h.symm ▸ f.continuous

@[simp]
/--
theorem `coe_copy` / 定理 `coe_copy`

English:
theorem coe_copy
  given: (f : A ->A[R] B) (f' : A -> B) (h : f' = ⇑f)
  statement: ⇑(f.copy f' h) = f'
  proof: rfl

中文:
定理 coe_copy
  条件: (f : A ->A[R] B) (f' : A -> B) (h : f' = ⇑f)
  结论: ⇑(f.copy f' h) = f'
  证明: rfl
-/
theorem coe_copy (f : A ->A[R] B) (f' : A -> B) (h : f' = ⇑f) : ⇑(f.copy f' h) = f' := rfl

/--
theorem `copy_eq` / 定理 `copy_eq`

English:
theorem copy_eq
  given: (f : A ->A[R] B) (f' : A -> B) (h : f' = ⇑f)
  statement: f.copy f' h = f
  proof: DFunLike.ext' h

中文:
定理 copy_eq
  条件: (f : A ->A[R] B) (f' : A -> B) (h : f' = ⇑f)
  结论: f.copy f' h = f
  证明: DFunLike.ext' h

Depends on / 依赖: DFunLike, DFunLike.ext
-/
theorem copy_eq (f : A ->A[R] B) (f' : A -> B) (h : f' = ⇑f) : f.copy f' h = f := DFunLike.ext' h

/--
theorem `map_zero` / 定理 `map_zero`

English:
theorem map_zero
  given: (f : A ->A[R] B)
  statement: f (0 : A) = 0
  proof: map_zero f

中文:
定理 map_zero
  条件: (f : A ->A[R] B)
  结论: f (0 : A) = 0
  证明: map_zero f
-/
protected theorem map_zero (f : A ->A[R] B) : f (0 : A) = 0 := map_zero f

/--
theorem `map_add` / 定理 `map_add`

English:
theorem map_add
  given: (f : A ->A[R] B) (x y : A)
  statement: f (x + y) = f x + f y
  proof: map_add f x y

中文:
定理 map_add
  条件: (f : A ->A[R] B) (x y : A)
  结论: f (x + y) = f x + f y
  证明: map_add f x y
-/
protected theorem map_add (f : A ->A[R] B) (x y : A) : f (x + y) = f x + f y := map_add f x y

/--
theorem `map_smul` / 定理 `map_smul`

English:
theorem map_smul
  given: (f : A ->A[R] B) (c : R) (x : A)
  proof: map_smul ..

中文:
定理 map_smul
  条件: (f : A ->A[R] B) (c : R) (x : A)
  证明: map_smul ..
-/
protected theorem map_smul (f : A ->A[R] B) (c : R) (x : A) :
    f (c • x) = c • f x :=
  map_smul ..

/--
theorem `map_smul_of_tower` / 定理 `map_smul_of_tower`

English:
theorem map_smul_of_tower
  statement: {R S : Type*} [CommSemiring S] [SMul R A] [Algebra S A] [SMul R B]
  proof: map_smul f c x

中文:
定理 map_smul_of_tower
  结论: {R S : 类型} [交换半环 S] [标量乘法 R A] [代数 S A] [标量乘法 R B]
  证明: map_smul f c x

Depends on / 依赖: map_smul
-/
theorem map_smul_of_tower {R S : Type*} [CommSemiring S] [SMul R A] [Algebra S A] [SMul R B]
    [Algebra S B] [MulActionHomClass (A ->A[S] B) R A B] (f : A ->A[S] B) (c : R) (x : A) :
    f (c • x) = c • f x :=
  map_smul f c x

/--
theorem `map_sum` / 定理 `map_sum`

English:
theorem map_sum
  given: {ι : Type*} (f : A ->A[R] B) (s : Finset ι) (g : ι -> A)
  proof: map_sum ..

中文:
定理 map_sum
  条件: {ι : 类型} (f : A ->A[R] B) (s : 有限集 ι) (g : ι -> A)
  证明: map_sum ..
-/
protected theorem map_sum {ι : Type*} (f : A ->A[R] B) (s : Finset ι) (g : ι -> A) :
    f (∑ i in s, g i) = ∑ i in s, f (g i) :=
  map_sum ..

/-- Any two continuous `R`-algebra morphisms from `R` are equal -/
@[ext (iff := false)]
/--
theorem `ext_ring` / 定理 `ext_ring`

English:
theorem ext_ring
  given: [TopologicalSpace R] {f g : R ->A[R] A}
  statement: f = g
  proof: coe_inj.mp (ext_id _ _ _)

中文:
定理 ext_ring
  条件: [拓扑空间 R] {f g : R ->A[R] A}
  结论: f = g
  证明: coe_inj.mp (ext_id _ _ _)

Depends on / 依赖: coe_inj, coe_inj.mp, ext_id
-/
theorem ext_ring [TopologicalSpace R] {f g : R ->A[R] A} : f = g :=
  coe_inj.mp (ext_id _ _ _)

/--
theorem `ext_ring_iff` / 定理 `ext_ring_iff`

English:
theorem ext_ring_iff
  given: [TopologicalSpace R] {f g : R ->A[R] A}
  statement: f = g ↔ f 1 = g 1
  proof: ⟨fun h => h ▸ rfl, fun _ => ext_ring ⟩

中文:
定理 ext_ring_iff
  条件: [拓扑空间 R] {f g : R ->A[R] A}
  结论: f = g ↔ f 1 = g 1
  证明: ⟨fun h => h ▸ rfl, fun _ => ext_ring ⟩

Depends on / 依赖: ext_ring
-/
theorem ext_ring_iff [TopologicalSpace R] {f g : R ->A[R] A} : f = g ↔ f 1 = g 1 :=
  ⟨fun h => h ▸ rfl, fun _ => ext_ring ⟩

/--
theorem `eqOn_closure_adjoin` / 定理 `eqOn_closure_adjoin`

English:
theorem eqOn_closure_adjoin
  given: [T2Space B] {s : Set A} {f g : A ->A[R] B} (h : Set.EqOn f g s)
  proof: Set.EqOn.closure (AlgHom.eqOn_adjoin_iff.mpr h) f.continuous g.continuous

中文:
定理 eqOn_closure_adjoin
  条件: [T2空间 B] {s : 集合 A} {f g : A ->A[R] B} (h : 集合.EqOn f g s)
  证明: Set.EqOn.closure (AlgHom.eqOn_adjoin_iff.mpr h) f.continuous g.continuous

Depends on / 依赖: AlgHom, AlgHom.eqOn_adjoin_iff.mpr, Set.EqOn.closure, closure, continuous, eqOn_adjoin_iff, f.continuous, g.continuous
-/
theorem eqOn_closure_adjoin [T2Space B] {s : Set A} {f g : A ->A[R] B} (h : Set.EqOn f g s) :
    Set.EqOn f g (closure (Algebra.adjoin R s : Set A)) :=
  Set.EqOn.closure (AlgHom.eqOn_adjoin_iff.mpr h) f.continuous g.continuous

/--
theorem `ext_on` / 定理 `ext_on`

English:
theorem ext_on
  statement: [T2Space B] {s : Set A} (hs : Dense (Algebra.adjoin R s : Set A))
  proof: ext fun x => eqOn_closure_adjoin h (hs x)

中文:
定理 ext_on
  结论: [T2空间 B] {s : 集合 A} (hs : 稠密 (代数.adjoin R s : 集合 A))
  证明: ext fun x => eqOn_closure_adjoin h (hs x)

Depends on / 依赖: eqOn_closure_adjoin
-/
theorem ext_on [T2Space B] {s : Set A} (hs : Dense (Algebra.adjoin R s : Set A))
    {f g : A ->A[R] B} (h : Set.EqOn f g s) : f = g :=
  ext fun x => eqOn_closure_adjoin h (hs x)

/--
Definition of `toContinuousLinearMap` / `toContinuousLinearMap` 的定义

English:
definition toContinuousLinearMap
  signature: (e : A ->A[R] B)
  body: e.toAlgHom.toLinearMap

中文:
定义 toContinuousLinearMap
  签名: (e : A ->A[R] B)
  定义体: e.toAlgHom.toLinearMap

Depends on / 依赖: e.toAlgHom.toLinearMap, toAlgHom, toLinearMap
-/
def toContinuousLinearMap (e : A ->A[R] B) : A ->L[R] B where
  toLinearMap := e.toAlgHom.toLinearMap

/--
theorem `coe_toContinuousLinearMap` / 定理 `coe_toContinuousLinearMap`

English:
theorem coe_toContinuousLinearMap
  given: (e : A ->A[R] B)
  statement: ⇑e.toContinuousLinearMap = e
  proof: rfl

中文:
定理 coe_toContinuousLinearMap
  条件: (e : A ->A[R] B)
  结论: ⇑e.toContinuousLinearMap = e
  证明: rfl
-/
@[simp] theorem coe_toContinuousLinearMap (e : A ->A[R] B) : ⇑e.toContinuousLinearMap = e := rfl

variable [IsSemitopologicalSemiring A]

/--
Definition of `_root_.Subalgebra.topologicalClosure` / `_root_.Subalgebra.topologicalClosure` 的定义

English:
definition _root_.Subalgebra.topologicalClosure
  signature: (s : Subalgebra R A)
  body: s.toSubsemiring.topologicalClosure
  algebraMap_mem' r := by
    simp only [Subsemiring.coe_carrier_toSubmonoid, Subsemiring.topologicalClosure_coe,
      Subalgebra.coe_toSubsemiring]
    apply subset_closure
    exact algebraMap_mem s r

中文:
定义 _root_.子代数.topologicalClosure
  签名: (s : 子代数 R A)
  定义体: s.toSubsemiring.topologicalClosure
  algebraMap_mem' r := by
    simp only [Subsemiring.coe_carrier_toSubmonoid, Subsemiring.topologicalClosure_coe,
      Subalgebra.coe_toSubsemiring]
    apply subset_closure
    exact algebraMap_mem s r

Depends on / 依赖: s.toSubsemiring.topologicalClosure, toSubsemiring, topologicalClosure
-/
def _root_.Subalgebra.topologicalClosure (s : Subalgebra R A) : Subalgebra R A where
  toSubsemiring := s.toSubsemiring.topologicalClosure
  algebraMap_mem' r := by
    simp only [Subsemiring.coe_carrier_toSubmonoid, Subsemiring.topologicalClosure_coe,
      Subalgebra.coe_toSubsemiring]
    apply subset_closure
    exact algebraMap_mem s r

/--
theorem `_root_.Subalgebra.map_topologicalClosure_le` / 定理 `_root_.Subalgebra.map_topologicalClosure_le`

English:
theorem _root_.Subalgebra.map_topologicalClosure_le
  proof: image_closure_subset_closure_image f.continuous

中文:
定理 _root_.子代数.map_topologicalClosure_le
  证明: image_closure_subset_closure_image f.continuous

Depends on / 依赖: continuous, f.continuous, image_closure_subset_closure_image
-/
theorem _root_.Subalgebra.map_topologicalClosure_le
    [IsSemitopologicalSemiring B] (f : A ->A[R] B) (s : Subalgebra R A) :
    map f s.topologicalClosure <= (map f.toAlgHom s).topologicalClosure :=
  image_closure_subset_closure_image f.continuous

/--
lemma `_root_.Subalgebra.topologicalClosure_map_le` / 引理 `_root_.Subalgebra.topologicalClosure_map_le`

English:
lemma _root_.Subalgebra.topologicalClosure_map_le
  statement: [IsSemitopologicalSemiring B]
  proof: hf.closure_image_subset _

中文:
引理 _root_.子代数.topologicalClosure_map_le
  结论: [是SemitopologicalSemiring B]
  证明: hf.closure_image_subset _

Depends on / 依赖: closure_image_subset, hf.closure_image_subset
-/
lemma _root_.Subalgebra.topologicalClosure_map_le [IsSemitopologicalSemiring B]
    (f : A ->ₐ[R] B) (hf : IsClosedMap f) (s : Subalgebra R A) :
    (map f s).topologicalClosure <= map f s.topologicalClosure :=
  hf.closure_image_subset _

/--
lemma `_root_.Subalgebra.topologicalClosure_map` / 引理 `_root_.Subalgebra.topologicalClosure_map`

English:
lemma _root_.Subalgebra.topologicalClosure_map
  statement: [IsSemitopologicalSemiring B]
  proof: SetLike.coe_injective hf.closure_image_eq_of_continuous f.continuous _

@[simp]

中文:
引理 _root_.子代数.topologicalClosure_map
  结论: [是SemitopologicalSemiring B]
  证明: SetLike.coe_injective hf.closure_image_eq_of_continuous f.continuous _

@[simp]

Depends on / 依赖: SetLike, SetLike.coe_injective, closure_image_eq_of_continuous, coe_injective, continuous, f.continuous, hf.closure_image_eq_of_continuous
-/
lemma _root_.Subalgebra.topologicalClosure_map [IsSemitopologicalSemiring B]
    (f : A ->A[R] B) (hf : IsClosedMap f) (s : Subalgebra R A) :
    (map f.toAlgHom s).topologicalClosure = map f.toAlgHom s.topologicalClosure :=
SetLike.coe_injective hf.closure_image_eq_of_continuous f.continuous _

@[simp]
/--
theorem `_root_.Subalgebra.topologicalClosure_coe` / 定理 `_root_.Subalgebra.topologicalClosure_coe`

English:
theorem _root_.Subalgebra.topologicalClosure_coe
  given: (s : Subalgebra R A)
  proof: rfl

中文:
定理 _root_.子代数.topologicalClosure_coe
  条件: (s : 子代数 R A)
  证明: rfl
-/
theorem _root_.Subalgebra.topologicalClosure_coe (s : Subalgebra R A) :
    (s.topologicalClosure : Set A) = closure ↑s := rfl

/--
theorem `_root_.DenseRange.topologicalClosure_map_subalgebra` / 定理 `_root_.DenseRange.topologicalClosure_map_subalgebra`

English:
theorem _root_.DenseRange.topologicalClosure_map_subalgebra
  proof: by
  rw [SetLike.ext'_iff] at hs ⊢
  simp only [Subalgebra.topologicalClosure_coe, coe_top, ← dense_iff_closure_eq,
    Subalgebra.coe_map] at hs ⊢
  exact hf'.dense_image f.continuous hs

中文:
定理 _root_.DenseRange.topologicalClosure_map_subalgebra
  证明: by
  rw [SetLike.ext'_iff] at hs ⊢
  simp only [Subalgebra.topologicalClosure_coe, coe_top, ← dense_iff_closure_eq,
    Subalgebra.coe_map] at hs ⊢
  exact hf'.dense_image f.continuous hs

Depends on / 依赖: SetLike, SetLike.ext, Subalgebra, Subalgebra.coe_map, Subalgebra.topologicalClosure_coe, _iff, coe_map, coe_top, continuous, dense_iff_closure_eq, dense_image, f.continuous, topologicalClosure_coe
-/
theorem _root_.DenseRange.topologicalClosure_map_subalgebra
    [IsSemitopologicalSemiring B] {f : A ->A[R] B} (hf' : DenseRange f) {s : Subalgebra R A}
    (hs : s.topologicalClosure = ⊤) : (s.map (f : A ->ₐ[R] B)).topologicalClosure = ⊤ := by
  rw [SetLike.ext'_iff] at hs ⊢
  simp only [Subalgebra.topologicalClosure_coe, coe_top, ← dense_iff_closure_eq,
    Subalgebra.coe_map] at hs ⊢
  exact hf'.dense_image f.continuous hs

end Semiring

section id

variable [TopologicalSpace A]
variable [Algebra R A]

/--
Definition of `id` / `id` 的定义

English:
definition id
  signature: : A ->A[R] A
  body: ⟨AlgHom.id R A, continuous_id⟩

中文:
定义 id
  签名: : A ->A[R] A
  定义体: ⟨AlgHom.id R A, continuous_id⟩
-/
protected def id : A ->A[R] A := ⟨AlgHom.id R A, continuous_id⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: One (A ->A[R] A)
  body: ⟨ContinuousAlgHom.id R A⟩

中文:
实例 :
  签名: 幺 (A ->A[R] A)
  定义体: ⟨ContinuousAlgHom.id R A⟩

Depends on / 依赖: ContinuousAlgHom, ContinuousAlgHom.id
-/
instance : One (A ->A[R] A) := ⟨ContinuousAlgHom.id R A⟩

/--
theorem `one_def` / 定理 `one_def`

English:
theorem one_def
  statement: (1 : A ->A[R] A) = ContinuousAlgHom.id R A
  proof: rfl

中文:
定理 one_def
  结论: (1 : A ->A[R] A) = 余ntinuousAlg态射.id R A
  证明: rfl
-/
theorem one_def : (1 : A ->A[R] A) = ContinuousAlgHom.id R A := rfl

/--
theorem `id_apply` / 定理 `id_apply`

English:
theorem id_apply
  given: (x : A)
  statement: ContinuousAlgHom.id R A x = x
  proof: rfl

@[simp, norm_cast]

中文:
定理 id_apply
  条件: (x : A)
  结论: 余ntinuousAlg态射.id R A x = x
  证明: rfl

@[simp, norm_cast]
-/
theorem id_apply (x : A) : ContinuousAlgHom.id R A x = x := rfl

@[simp, norm_cast]
/--
theorem `coe_id` / 定理 `coe_id`

English:
theorem coe_id
  statement: ((ContinuousAlgHom.id R A) : A ->ₐ[R] A) = AlgHom.id R A
  proof: rfl

@[simp, norm_cast]

中文:
定理 coe_id
  结论: ((余ntinuousAlg态射.id R A) : A ->ₐ[R] A) = 代数态射.id R A
  证明: rfl

@[simp, norm_cast]
-/
theorem coe_id : ((ContinuousAlgHom.id R A) : A ->ₐ[R] A) = AlgHom.id R A := rfl

@[simp, norm_cast]
/--
theorem `coe_id'` / 定理 `coe_id'`

English:
theorem coe_id'
  statement: ⇑(ContinuousAlgHom.id R A) = _root_.id
  proof: rfl

@[simp, norm_cast]

中文:
定理 coe_id'
  结论: ⇑(余ntinuousAlg态射.id R A) = _root_.id
  证明: rfl

@[simp, norm_cast]
-/
theorem coe_id' : ⇑(ContinuousAlgHom.id R A) = _root_.id := rfl

@[simp, norm_cast]
/--
theorem `coe_eq_id` / 定理 `coe_eq_id`

English:
theorem coe_eq_id
  given: {f : A ->A[R] A}
  proof: by
  rw [← coe_id]; rw [coe_inj]

@[simp]

中文:
定理 coe_eq_id
  条件: {f : A ->A[R] A}
  证明: by
  rw [← coe_id]; rw [coe_inj]

@[simp]

Depends on / 依赖: coe_id, coe_inj
-/
theorem coe_eq_id {f : A ->A[R] A} :
    (f : A ->ₐ[R] A) = AlgHom.id R A ↔ f = ContinuousAlgHom.id R A := by
  rw [← coe_id]; rw [coe_inj]

@[simp]
/--
theorem `one_apply` / 定理 `one_apply`

English:
theorem one_apply
  given: (x : A)
  statement: (1 : A ->A[R] A) x = x
  proof: rfl

中文:
定理 one_apply
  条件: (x : A)
  结论: (1 : A ->A[R] A) x = x
  证明: rfl
-/
theorem one_apply (x : A) : (1 : A ->A[R] A) x = x := rfl

end id

section comp

variable {R} {A}
variable [TopologicalSpace A]
variable {B : Type*} [Semiring B] [TopologicalSpace B] [Algebra R A] [Algebra R B]
  {C : Type*} [Semiring C] [Algebra R C] [TopologicalSpace C]

/--
Definition of `comp` / `comp` 的定义

English:
definition comp
  signature: (g : B ->A[R] C) (f : A ->A[R] B)
  body: ⟨(g : B ->ₐ[R] C).comp (f : A ->ₐ[R] B), g.2.comp f.2⟩

@[simp, norm_cast]

中文:
定义 comp
  签名: (g : B ->A[R] C) (f : A ->A[R] B)
  定义体: ⟨(g : B ->ₐ[R] C).comp (f : A ->ₐ[R] B), g.2.comp f.2⟩

@[simp, norm_cast]
-/
def comp (g : B ->A[R] C) (f : A ->A[R] B) : A ->A[R] C :=
  ⟨(g : B ->ₐ[R] C).comp (f : A ->ₐ[R] B), g.2.comp f.2⟩

@[simp, norm_cast]
/--
theorem `coe_comp` / 定理 `coe_comp`

English:
theorem coe_comp
  given: (h : B ->A[R] C) (f : A ->A[R] B)
  proof: rfl

@[simp, norm_cast]

中文:
定理 coe_comp
  条件: (h : B ->A[R] C) (f : A ->A[R] B)
  证明: rfl

@[simp, norm_cast]
-/
theorem coe_comp (h : B ->A[R] C) (f : A ->A[R] B) :
    (h.comp f : A ->ₐ[R] C) = (h : B ->ₐ[R] C).comp (f : A ->ₐ[R] B) := rfl

@[simp, norm_cast]
/--
theorem `coe_comp'` / 定理 `coe_comp'`

English:
theorem coe_comp'
  given: (h : B ->A[R] C) (f : A ->A[R] B)
  statement: ⇑(h.comp f) = h ∘ f
  proof: rfl

中文:
定理 coe_comp'
  条件: (h : B ->A[R] C) (f : A ->A[R] B)
  结论: ⇑(h.comp f) = h ∘ f
  证明: rfl
-/
theorem coe_comp' (h : B ->A[R] C) (f : A ->A[R] B) : ⇑(h.comp f) = h ∘ f := rfl

/--
theorem `comp_apply` / 定理 `comp_apply`

English:
theorem comp_apply
  given: (g : B ->A[R] C) (f : A ->A[R] B) (x : A)
  statement: (g.comp f) x = g (f x)
  proof: rfl

@[simp]

中文:
定理 comp_apply
  条件: (g : B ->A[R] C) (f : A ->A[R] B) (x : A)
  结论: (g.comp f) x = g (f x)
  证明: rfl

@[simp]
-/
theorem comp_apply (g : B ->A[R] C) (f : A ->A[R] B) (x : A) : (g.comp f) x = g (f x) := rfl

@[simp]
/--
theorem `comp_id` / 定理 `comp_id`

English:
theorem comp_id
  given: (f : A ->A[R] B)
  statement: f.comp (ContinuousAlgHom.id R A) = f
  proof: ext fun _x => rfl

@[simp]

中文:
定理 comp_id
  条件: (f : A ->A[R] B)
  结论: f.comp (余ntinuousAlg态射.id R A) = f
  证明: ext fun _x => rfl

@[simp]
-/
theorem comp_id (f : A ->A[R] B) : f.comp (ContinuousAlgHom.id R A) = f :=
  ext fun _x => rfl

@[simp]
/--
theorem `id_comp` / 定理 `id_comp`

English:
theorem id_comp
  given: (f : A ->A[R] B)
  statement: (ContinuousAlgHom.id R B).comp f = f
  proof: ext fun _x => rfl

中文:
定理 id_comp
  条件: (f : A ->A[R] B)
  结论: (余ntinuousAlg态射.id R B).comp f = f
  证明: ext fun _x => rfl
-/
theorem id_comp (f : A ->A[R] B) : (ContinuousAlgHom.id R B).comp f = f :=
  ext fun _x => rfl

/--
theorem `comp_assoc` / 定理 `comp_assoc`

English:
theorem comp_assoc
  statement: {D : Type*} [Semiring D] [Algebra R D] [TopologicalSpace D] (h : C ->A[R] D)
  proof: rfl

中文:
定理 comp_assoc
  结论: {D : 类型} [半环 D] [代数 R D] [拓扑空间 D] (h : C ->A[R] D)
  证明: rfl
-/
theorem comp_assoc {D : Type*} [Semiring D] [Algebra R D] [TopologicalSpace D] (h : C ->A[R] D)
    (g : B ->A[R] C) (f : A ->A[R] B) : (h.comp g).comp f = h.comp (g.comp f) :=
  rfl

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Mul (A ->A[R] A)
  body: ⟨comp⟩

中文:
实例 :
  签名: 乘法 (A ->A[R] A)
  定义体: ⟨comp⟩
-/
instance : Mul (A ->A[R] A) := ⟨comp⟩

/--
theorem `mul_def` / 定理 `mul_def`

English:
theorem mul_def
  given: (f g : A ->A[R] A)
  statement: f * g = f.comp g
  proof: rfl

@[simp]

中文:
定理 mul_def
  条件: (f g : A ->A[R] A)
  结论: f * g = f.comp g
  证明: rfl

@[simp]
-/
theorem mul_def (f g : A ->A[R] A) : f * g = f.comp g := rfl

@[simp]
/--
theorem `coe_mul` / 定理 `coe_mul`

English:
theorem coe_mul
  given: (f g : A ->A[R] A)
  statement: ⇑(f * g) = f ∘ g
  proof: rfl

中文:
定理 coe_mul
  条件: (f g : A ->A[R] A)
  结论: ⇑(f * g) = f ∘ g
  证明: rfl
-/
theorem coe_mul (f g : A ->A[R] A) : ⇑(f * g) = f ∘ g := rfl

/--
theorem `mul_apply` / 定理 `mul_apply`

English:
theorem mul_apply
  given: (f g : A ->A[R] A) (x : A)
  statement: (f * g) x = f (g x)
  proof: rfl

中文:
定理 mul_apply
  条件: (f g : A ->A[R] A) (x : A)
  结论: (f * g) x = f (g x)
  证明: rfl
-/
theorem mul_apply (f g : A ->A[R] A) (x : A) : (f * g) x = f (g x) := rfl

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Monoid (A ->A[R] A)
  body: ext fun _ => rfl
  one_mul _ := ext fun _ => rfl
  mul_assoc _ _ _ := ext fun _ => rfl

中文:
实例 :
  签名: 幺半群 (A ->A[R] A)
  定义体: ext fun _ => rfl
  one_mul _ := ext fun _ => rfl
  mul_assoc _ _ _ := ext fun _ => rfl
-/
instance : Monoid (A ->A[R] A) where
  mul_one _ := ext fun _ => rfl
  one_mul _ := ext fun _ => rfl
  mul_assoc _ _ _ := ext fun _ => rfl

/--
theorem `coe_pow` / 定理 `coe_pow`

English:
theorem coe_pow
  given: (f : A ->A[R] A) (n : Nat)
  statement: ⇑(f ^ n) = f^[n]
  proof: hom_coe_pow _ rfl (fun _ _ => rfl) _ _

中文:
定理 coe_pow
  条件: (f : A ->A[R] A) (n : 自然数)
  结论: ⇑(f ^ n) = f^[n]
  证明: hom_coe_pow _ rfl (fun _ _ => rfl) _ _

Depends on / 依赖: hom_coe_pow
-/
theorem coe_pow (f : A ->A[R] A) (n : Nat) : ⇑(f ^ n) = f^[n] :=
  hom_coe_pow _ rfl (fun _ _ => rfl) _ _

set_option linter.style.whitespace false in -- manual alignment is not recognised
/-- coercion from `ContinuousAlgHom` to `AlgHom` as a `RingHom`. -/
@[simps]
/--
Definition of `toAlgHomMonoidHom` / `toAlgHomMonoidHom` 的定义

English:
definition toAlgHomMonoidHom
  signature: : (A ->A[R] A) ->* A ->ₐ[R] A where
  body: (↑)
  map_one' := rfl
  map_mul' _ _ := rfl

中文:
定义 toAlgHomMonoidHom
  签名: : (A ->A[R] A) ->* A ->ₐ[R] A where
  定义体: (↑)
  map_one' := rfl
  map_mul' _ _ := rfl
-/
def toAlgHomMonoidHom : (A ->A[R] A) ->* A ->ₐ[R] A where
  toFun := (↑)
  map_one' := rfl
  map_mul' _ _ := rfl

end comp

section prod

variable {R} {A}
variable [TopologicalSpace A]
variable {B : Type*} [Semiring B] [TopologicalSpace B] [Algebra R A] [Algebra R B]
  {C : Type*} [Semiring C] [Algebra R C] [TopologicalSpace C]

/--
Definition of `prod` / `prod` 的定义

English:
definition prod
  signature: (f₁ : A ->A[R] B) (f₂ : A ->A[R] C)
  body: ⟨(f₁ : A ->ₐ[R] B).prod f₂, f₁.2.prodMk f₂.2⟩

@[simp, norm_cast]

中文:
定义 乘积
  签名: (f₁ : A ->A[R] B) (f₂ : A ->A[R] C)
  定义体: ⟨(f₁ : A ->ₐ[R] B).prod f₂, f₁.2.prodMk f₂.2⟩

@[simp, norm_cast]
-/
protected def prod (f₁ : A ->A[R] B) (f₂ : A ->A[R] C) :
    A ->A[R] B × C :=
  ⟨(f₁ : A ->ₐ[R] B).prod f₂, f₁.2.prodMk f₂.2⟩

@[simp, norm_cast]
/--
theorem `coe_prod` / 定理 `coe_prod`

English:
theorem coe_prod
  given: (f₁ : A ->A[R] B) (f₂ : A ->A[R] C)
  proof: rfl

@[simp, norm_cast]

中文:
定理 coe_prod
  条件: (f₁ : A ->A[R] B) (f₂ : A ->A[R] C)
  证明: rfl

@[simp, norm_cast]
-/
theorem coe_prod (f₁ : A ->A[R] B) (f₂ : A ->A[R] C) :
    (f₁.prod f₂ : A ->ₐ[R] B × C) = AlgHom.prod f₁ f₂ :=
  rfl

@[simp, norm_cast]
/--
theorem `prod_apply` / 定理 `prod_apply`

English:
theorem prod_apply
  given: (f₁ : A ->A[R] B) (f₂ : A ->A[R] C) (x : A)
  proof: rfl

中文:
定理 prod_apply
  条件: (f₁ : A ->A[R] B) (f₂ : A ->A[R] C) (x : A)
  证明: rfl
-/
theorem prod_apply (f₁ : A ->A[R] B) (f₂ : A ->A[R] C) (x : A) :
    f₁.prod f₂ x = (f₁ x, f₂ x) :=
  rfl

instance {D : Type*} [UniformSpace D] [CompleteSpace D]
    [Semiring D] [Algebra R D] [T2Space B]
    (f g : D ->A[R] B) : CompleteSpace (AlgHom.equalizer f.toAlgHom g.toAlgHom) :=
.completeSpace_coe isClosed_eq (map_continuous f) (map_continuous g)

variable (R A B)

set_option linter.style.whitespace false in -- manual alignment is not recognised
/--
Definition of `fst` / `fst` 的定义

English:
definition fst
  signature: : A × B ->A[R] A where
  body: continuous_fst
  toAlgHom := AlgHom.fst R A B

中文:
定义 fst
  签名: : A × B ->A[R] A where
  定义体: continuous_fst
  toAlgHom := AlgHom.fst R A B

Depends on / 依赖: continuous_fst
-/
def fst : A × B ->A[R] A where
  cont := continuous_fst
  toAlgHom := AlgHom.fst R A B

/--
Definition of `snd` / `snd` 的定义

English:
definition snd
  signature: : A × B ->A[R] B where
  body: continuous_snd
  toAlgHom := AlgHom.snd R A B

中文:
定义 snd
  签名: : A × B ->A[R] B where
  定义体: continuous_snd
  toAlgHom := AlgHom.snd R A B

Depends on / 依赖: continuous_snd
-/
def snd : A × B ->A[R] B where
  cont := continuous_snd
  toAlgHom := AlgHom.snd R A B

variable {R A B}

@[simp, norm_cast]
/--
theorem `coe_fst` / 定理 `coe_fst`

English:
theorem coe_fst
  statement: ↑(fst R A B) = AlgHom.fst R A B
  proof: rfl

@[simp, norm_cast]

中文:
定理 coe_fst
  结论: ↑(fst R A B) = 代数态射.fst R A B
  证明: rfl

@[simp, norm_cast]
-/
theorem coe_fst : ↑(fst R A B) = AlgHom.fst R A B :=
  rfl

@[simp, norm_cast]
/--
theorem `coe_fst'` / 定理 `coe_fst'`

English:
theorem coe_fst'
  statement: ⇑(fst R A B) = Prod.fst
  proof: rfl

@[simp, norm_cast]

中文:
定理 coe_fst'
  结论: ⇑(fst R A B) = 积类型.fst
  证明: rfl

@[simp, norm_cast]
-/
theorem coe_fst' : ⇑(fst R A B) = Prod.fst :=
  rfl

@[simp, norm_cast]
/--
theorem `coe_snd` / 定理 `coe_snd`

English:
theorem coe_snd
  statement: ↑(snd R A B) = AlgHom.snd R A B
  proof: rfl

@[simp, norm_cast]

中文:
定理 coe_snd
  结论: ↑(snd R A B) = 代数态射.snd R A B
  证明: rfl

@[simp, norm_cast]
-/
theorem coe_snd : ↑(snd R A B) = AlgHom.snd R A B :=
  rfl

@[simp, norm_cast]
/--
theorem `coe_snd'` / 定理 `coe_snd'`

English:
theorem coe_snd'
  statement: ⇑(snd R A B) = Prod.snd
  proof: rfl

@[simp]

中文:
定理 coe_snd'
  结论: ⇑(snd R A B) = 积类型.snd
  证明: rfl

@[simp]
-/
theorem coe_snd' : ⇑(snd R A B) = Prod.snd :=
  rfl

@[simp]
/--
theorem `fst_prod_snd` / 定理 `fst_prod_snd`

English:
theorem fst_prod_snd
  statement: (fst R A B).prod (snd R A B) = ContinuousAlgHom.id R (A × B)
  proof: ext fun ⟨_x, _y⟩ => rfl

@[simp]

中文:
定理 fst_prod_snd
  结论: (fst R A B).乘积 (snd R A B) = 余ntinuousAlg态射.id R (A × B)
  证明: ext fun ⟨_x, _y⟩ => rfl

@[simp]
-/
theorem fst_prod_snd : (fst R A B).prod (snd R A B) = ContinuousAlgHom.id R (A × B) :=
  ext fun ⟨_x, _y⟩ => rfl

@[simp]
/--
theorem `fst_comp_prod` / 定理 `fst_comp_prod`

English:
theorem fst_comp_prod
  given: (f : A ->A[R] B) (g : A ->A[R] C)
  proof: ext fun _x => rfl

@[simp]

中文:
定理 fst_comp_prod
  条件: (f : A ->A[R] B) (g : A ->A[R] C)
  证明: ext fun _x => rfl

@[simp]
-/
theorem fst_comp_prod (f : A ->A[R] B) (g : A ->A[R] C) :
    (fst R B C).comp (f.prod g) = f :=
  ext fun _x => rfl

@[simp]
/--
theorem `snd_comp_prod` / 定理 `snd_comp_prod`

English:
theorem snd_comp_prod
  given: (f : A ->A[R] B) (g : A ->A[R] C)
  proof: ext fun _x => rfl

中文:
定理 snd_comp_prod
  条件: (f : A ->A[R] B) (g : A ->A[R] C)
  证明: ext fun _x => rfl
-/
theorem snd_comp_prod (f : A ->A[R] B) (g : A ->A[R] C) :
    (snd R B C).comp (f.prod g) = g :=
  ext fun _x => rfl

/--
Definition of `prodMap` / `prodMap` 的定义

English:
definition prodMap
  signature: {D : Type*} [Semiring D] [TopologicalSpace D] [Algebra R D] (f₁ : A ->A[R] B)
  body: (f₁.comp (fst R A C)).prod (f₂.comp (snd R A C))


@[simp, norm_cast]

中文:
定义 prodMap
  签名: {D : 类型} [半环 D] [拓扑空间 D] [代数 R D] (f₁ : A ->A[R] B)
  定义体: (f₁.comp (fst R A C)).prod (f₂.comp (snd R A C))


@[simp, norm_cast]
-/
def prodMap {D : Type*} [Semiring D] [TopologicalSpace D] [Algebra R D] (f₁ : A ->A[R] B)
    (f₂ : C ->A[R] D) : A × C ->A[R] B × D :=
  (f₁.comp (fst R A C)).prod (f₂.comp (snd R A C))


@[simp, norm_cast]
/--
theorem `coe_prodMap` / 定理 `coe_prodMap`

English:
theorem coe_prodMap
  statement: {D : Type*} [Semiring D] [TopologicalSpace D] [Algebra R D] (f₁ : A ->A[R] B)
  proof: rfl

@[simp, norm_cast]

中文:
定理 coe_prodMap
  结论: {D : 类型} [半环 D] [拓扑空间 D] [代数 R D] (f₁ : A ->A[R] B)
  证明: rfl

@[simp, norm_cast]
-/
theorem coe_prodMap {D : Type*} [Semiring D] [TopologicalSpace D] [Algebra R D] (f₁ : A ->A[R] B)
    (f₂ : C ->A[R] D) :
    (f₁.prodMap f₂ : A × C ->ₐ[R] B × D) = (f₁ : A ->ₐ[R] B).prodMap (f₂ : C ->ₐ[R] D) :=
  rfl

@[simp, norm_cast]
/--
theorem `coe_prodMap'` / 定理 `coe_prodMap'`

English:
theorem coe_prodMap'
  statement: {D : Type*} [Semiring D] [TopologicalSpace D] [Algebra R D] (f₁ : A ->A[R] B)
  proof: rfl

中文:
定理 coe_prodMap'
  结论: {D : 类型} [半环 D] [拓扑空间 D] [代数 R D] (f₁ : A ->A[R] B)
  证明: rfl
-/
theorem coe_prodMap' {D : Type*} [Semiring D] [TopologicalSpace D] [Algebra R D] (f₁ : A ->A[R] B)
    (f₂ : C ->A[R] D) : ⇑(f₁.prodMap f₂) = Prod.map f₁ f₂ :=
  rfl

set_option linter.style.whitespace false in -- manual alignment is not recognised
/-- `ContinuousAlgHom.prod` as an `Equiv`. -/
@[simps apply]
/--
Definition of `prodEquiv` / `prodEquiv` 的定义

English:
definition prodEquiv
  signature: : (A ->A[R] B) × (A ->A[R] C) ≃ (A ->A[R] B × C) where
  body: f.1.prod f.2
  invFun f := ⟨(fst _ _ _).comp f, (snd _ _ _).comp f⟩

中文:
定义 prodEquiv
  签名: : (A ->A[R] B) × (A ->A[R] C) ≃ (A ->A[R] B × C) where
  定义体: f.1.prod f.2
  invFun f := ⟨(fst _ _ _).comp f, (snd _ _ _).comp f⟩
-/
def prodEquiv : (A ->A[R] B) × (A ->A[R] C) ≃ (A ->A[R] B × C) where
  toFun f := f.1.prod f.2
  invFun f := ⟨(fst _ _ _).comp f, (snd _ _ _).comp f⟩

end prod

section subalgebra

variable {R A}
variable [TopologicalSpace A]
variable {B : Type*} [Semiring B] [TopologicalSpace B] [Algebra R A] [Algebra R B]

set_option linter.style.whitespace false in -- manual alignment is not recognised
/--
Definition of `codRestrict` / `codRestrict` 的定义

English:
definition codRestrict
  signature: (f : A ->A[R] B) (p : Subalgebra R B) (h : forall x, f x in p)
  body: f.continuous.subtype_mk _
  toAlgHom := (f : A ->ₐ[R] B).codRestrict p h

@[norm_cast]

中文:
定义 codRestrict
  签名: (f : A ->A[R] B) (p : 子代数 R B) (h : 对任意 x, f x in p)
  定义体: f.continuous.subtype_mk _
  toAlgHom := (f : A ->ₐ[R] B).codRestrict p h

@[norm_cast]

Depends on / 依赖: continuous, f.continuous.subtype_mk, subtype_mk
-/
def codRestrict (f : A ->A[R] B) (p : Subalgebra R B) (h : forall x, f x in p) : A ->A[R] p where
  cont := f.continuous.subtype_mk _
  toAlgHom := (f : A ->ₐ[R] B).codRestrict p h

@[norm_cast]
/--
theorem `coe_codRestrict` / 定理 `coe_codRestrict`

English:
theorem coe_codRestrict
  given: (f : A ->A[R] B) (p : Subalgebra R B) (h : forall x, f x in p)
  proof: rfl

@[simp]

中文:
定理 coe_codRestrict
  条件: (f : A ->A[R] B) (p : 子代数 R B) (h : 对任意 x, f x in p)
  证明: rfl

@[simp]
-/
theorem coe_codRestrict (f : A ->A[R] B) (p : Subalgebra R B) (h : forall x, f x in p) :
    (f.codRestrict p h : A ->ₐ[R] p) = (f : A ->ₐ[R] B).codRestrict p h :=
  rfl

@[simp]
/--
theorem `coe_codRestrict_apply` / 定理 `coe_codRestrict_apply`

English:
theorem coe_codRestrict_apply
  given: (f : A ->A[R] B) (p : Subalgebra R B) (h : forall x, f x in p) (x)
  proof: rfl

中文:
定理 coe_codRestrict_apply
  条件: (f : A ->A[R] B) (p : 子代数 R B) (h : 对任意 x, f x in p) (x)
  证明: rfl
-/
theorem coe_codRestrict_apply (f : A ->A[R] B) (p : Subalgebra R B) (h : forall x, f x in p) (x) :
    (f.codRestrict p h x : B) = f x :=
  rfl

/-- Restrict the codomain of a continuous algebra homomorphism `f` to `f.range`. -/
@[reducible]
/--
Definition of `rangeRestrict` / `rangeRestrict` 的定义

English:
definition rangeRestrict
  signature: (f : A ->A[R] B)
  body: f.codRestrict (@AlgHom.range R A B _ _ _ _ _ f) (@AlgHom.mem_range_self R A B _ _ _ _ _ f)

@[simp]

中文:
定义 rangeRestrict
  签名: (f : A ->A[R] B)
  定义体: f.codRestrict (@AlgHom.range R A B _ _ _ _ _ f) (@AlgHom.mem_range_self R A B _ _ _ _ _ f)

@[simp]

Depends on / 依赖: AlgHom, AlgHom.mem_range_self, AlgHom.range, codRestrict, f.codRestrict, mem_range_self
-/
def rangeRestrict (f : A ->A[R] B) :=
  f.codRestrict (@AlgHom.range R A B _ _ _ _ _ f) (@AlgHom.mem_range_self R A B _ _ _ _ _ f)

@[simp]
/--
theorem `coe_rangeRestrict` / 定理 `coe_rangeRestrict`

English:
theorem coe_rangeRestrict
  given: (f : A ->A[R] B)
  proof: rfl

中文:
定理 coe_rangeRestrict
  条件: (f : A ->A[R] B)
  证明: rfl
-/
theorem coe_rangeRestrict (f : A ->A[R] B) :
    (f.rangeRestrict : A ->ₐ[R] (@AlgHom.range R A B _ _ _ _ _ f)) =
      (f : A ->ₐ[R] B).rangeRestrict :=
  rfl

/--
Definition of `_root_.Subalgebra.valA` / `_root_.Subalgebra.valA` 的定义

English:
definition _root_.Subalgebra.valA
  signature: (p : Subalgebra R A)
  body: continuous_subtype_val
  toAlgHom := p.val

@[simp, norm_cast]

中文:
定义 _root_.子代数.valA
  签名: (p : 子代数 R A)
  定义体: continuous_subtype_val
  toAlgHom := p.val

@[simp, norm_cast]

Depends on / 依赖: continuous_subtype_val
-/
def _root_.Subalgebra.valA (p : Subalgebra R A) : p ->A[R] A where
  cont := continuous_subtype_val
  toAlgHom := p.val

@[simp, norm_cast]
/--
theorem `_root_.Subalgebra.coe_valA` / 定理 `_root_.Subalgebra.coe_valA`

English:
theorem _root_.Subalgebra.coe_valA
  given: (p : Subalgebra R A)
  statement: p.valA = p.subtype
  proof: rfl

@[simp]

中文:
定理 _root_.子代数.coe_valA
  条件: (p : 子代数 R A)
  结论: p.valA = p.subtype
  证明: rfl

@[simp]
-/
theorem _root_.Subalgebra.coe_valA (p : Subalgebra R A) : p.valA = p.subtype :=
  rfl

@[simp]
/--
theorem `_root_.Subalgebra.coe_valA'` / 定理 `_root_.Subalgebra.coe_valA'`

English:
theorem _root_.Subalgebra.coe_valA'
  given: (p : Subalgebra R A)
  statement: ⇑p.valA = p.subtype
  proof: rfl

@[simp]

中文:
定理 _root_.子代数.coe_valA'
  条件: (p : 子代数 R A)
  结论: ⇑p.valA = p.subtype
  证明: rfl

@[simp]
-/
theorem _root_.Subalgebra.coe_valA' (p : Subalgebra R A) : ⇑p.valA = p.subtype :=
  rfl

@[simp]
/--
theorem `_root_.Subalgebra.valA_apply` / 定理 `_root_.Subalgebra.valA_apply`

English:
theorem _root_.Subalgebra.valA_apply
  given: (p : Subalgebra R A) (x : p)
  statement: p.valA x = x
  proof: rfl

@[simp]

中文:
定理 _root_.子代数.valA_apply
  条件: (p : 子代数 R A) (x : p)
  结论: p.valA x = x
  证明: rfl

@[simp]
-/
theorem _root_.Subalgebra.valA_apply (p : Subalgebra R A) (x : p) : p.valA x = x :=
  rfl

@[simp]
/--
theorem `_root_.Submodule.range_valA` / 定理 `_root_.Submodule.range_valA`

English:
theorem _root_.Submodule.range_valA
  given: (p : Subalgebra R A)
  proof: Subalgebra.range_val p

中文:
定理 _root_.子模.range_valA
  条件: (p : 子代数 R A)
  证明: Subalgebra.range_val p

Depends on / 依赖: Subalgebra, Subalgebra.range_val, range_val
-/
theorem _root_.Submodule.range_valA (p : Subalgebra R A) :
    @AlgHom.range R p A _ _ _ _ _ p.valA = p :=
  Subalgebra.range_val p

end subalgebra

section Ring


variable {S : Type*} [Ring S] [TopologicalSpace S] [Algebra R S] {B : Type*} [Ring B]
  [TopologicalSpace B] [Algebra R B]

/--
theorem `map_neg` / 定理 `map_neg`

English:
theorem map_neg
  given: (f : S ->A[R] B) (x : S)
  statement: f (-x) = -f x
  proof: map_neg f x

中文:
定理 map_neg
  条件: (f : S ->A[R] B) (x : S)
  结论: f (-x) = -f x
  证明: map_neg f x
-/
protected theorem map_neg (f : S ->A[R] B) (x : S) : f (-x) = -f x := map_neg f x

/--
theorem `map_sub` / 定理 `map_sub`

English:
theorem map_sub
  given: (f : S ->A[R] B) (x y : S)
  statement: f (x - y) = f x - f y
  proof: map_sub f x y

中文:
定理 map_sub
  条件: (f : S ->A[R] B) (x y : S)
  结论: f (x - y) = f x - f y
  证明: map_sub f x y
-/
protected theorem map_sub (f : S ->A[R] B) (x y : S) : f (x - y) = f x - f y := map_sub f x y

end Ring


section RestrictScalars

variable {S : Type*} [CommSemiring S] [Algebra R S] {B : Type*} [Ring B] [TopologicalSpace B]
  [Algebra R B] [Algebra S B] [IsScalarTower R S B] {C : Type*} [Ring C] [TopologicalSpace C]
  [Algebra R C] [Algebra S C] [IsScalarTower R S C]

/--
Definition of `restrictScalars` / `restrictScalars` 的定义

English:
definition restrictScalars
  signature: (f : B ->A[S] C)
  body: ⟨(f : B ->ₐ[S] C).restrictScalars R, f.continuous⟩

中文:
定义 restrictScalars
  签名: (f : B ->A[S] C)
  定义体: ⟨(f : B ->ₐ[S] C).restrictScalars R, f.continuous⟩

Depends on / 依赖: continuous, f.continuous, restrictScalars
-/
def restrictScalars (f : B ->A[S] C) : B ->A[R] C :=
  ⟨(f : B ->ₐ[S] C).restrictScalars R, f.continuous⟩

variable {R}

@[simp]
/--
theorem `coe_restrictScalars` / 定理 `coe_restrictScalars`

English:
theorem coe_restrictScalars
  given: (f : B ->A[S] C)
  proof: rfl

@[simp]

中文:
定理 coe_restrictScalars
  条件: (f : B ->A[S] C)
  证明: rfl

@[simp]
-/
theorem coe_restrictScalars (f : B ->A[S] C) :
    (f.restrictScalars R : B ->ₐ[R] C) = (f : B ->ₐ[S] C).restrictScalars R :=
  rfl

@[simp]
/--
theorem `coe_restrictScalars'` / 定理 `coe_restrictScalars'`

English:
theorem coe_restrictScalars'
  given: (f : B ->A[S] C)
  statement: ⇑(f.restrictScalars R) = f
  proof: rfl

中文:
定理 coe_restrictScalars'
  条件: (f : B ->A[S] C)
  结论: ⇑(f.restrictScalars R) = f
  证明: rfl
-/
theorem coe_restrictScalars' (f : B ->A[S] C) : ⇑(f.restrictScalars R) = f :=
  rfl

end RestrictScalars

end ContinuousAlgHom

end

variable {R : Type*} [CommSemiring R]
variable {A : Type u} [TopologicalSpace A]
variable [Semiring A] [Algebra R A]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [IsTopologicalSemiring
  signature: A] (s
  body: s.toSubsemiring.topologicalSemiring

中文:
实例 [是TopologicalSemiring
  签名: A] (s
  定义体: s.toSubsemiring.topologicalSemiring

Depends on / 依赖: s.toSubsemiring.topologicalSemiring, toSubsemiring, topologicalSemiring
-/
instance [IsTopologicalSemiring A] (s : Subalgebra R A) : IsTopologicalSemiring s :=
  s.toSubsemiring.topologicalSemiring

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [IsSemitopologicalSemiring
  signature: A] (s
  body: s.toSubsemiring.semitopologicalSemiring

中文:
实例 [是SemitopologicalSemiring
  签名: A] (s
  定义体: s.toSubsemiring.semitopologicalSemiring

Depends on / 依赖: s.toSubsemiring.semitopologicalSemiring, semitopologicalSemiring, toSubsemiring
-/
instance [IsSemitopologicalSemiring A] (s : Subalgebra R A) : IsSemitopologicalSemiring s :=
  s.toSubsemiring.semitopologicalSemiring

variable [IsSemitopologicalSemiring A]

/--
theorem `Subalgebra.le_topologicalClosure` / 定理 `Subalgebra.le_topologicalClosure`

English:
theorem Subalgebra.le_topologicalClosure
  given: (s : Subalgebra R A)
  statement: s <= s.topologicalClosure
  proof: subset_closure

中文:
定理 子代数.le_topologicalClosure
  条件: (s : 子代数 R A)
  结论: s <= s.topologicalClosure
  证明: subset_closure

Depends on / 依赖: subset_closure
-/
theorem Subalgebra.le_topologicalClosure (s : Subalgebra R A) : s <= s.topologicalClosure :=
  subset_closure

/--
theorem `Subalgebra.isClosed_topologicalClosure` / 定理 `Subalgebra.isClosed_topologicalClosure`

English:
theorem Subalgebra.isClosed_topologicalClosure
  given: (s : Subalgebra R A)
  proof: by convert! @isClosed_closure A _ s

中文:
定理 子代数.isClosed_topologicalClosure
  条件: (s : 子代数 R A)
  证明: by convert! @isClosed_closure A _ s

Depends on / 依赖: convert, isClosed_closure
-/
theorem Subalgebra.isClosed_topologicalClosure (s : Subalgebra R A) :
    IsClosed (s.topologicalClosure : Set A) := by convert! @isClosed_closure A _ s

/--
theorem `Subalgebra.topologicalClosure_minimal` / 定理 `Subalgebra.topologicalClosure_minimal`

English:
theorem Subalgebra.topologicalClosure_minimal
  statement: {s t : Subalgebra R A} (h : s <= t)
  proof: closure_minimal h ht

@[gcongr]

中文:
定理 子代数.topologicalClosure_minimal
  结论: {s t : 子代数 R A} (h : s <= t)
  证明: closure_minimal h ht

@[gcongr]

Depends on / 依赖: closure_minimal
-/
theorem Subalgebra.topologicalClosure_minimal {s t : Subalgebra R A} (h : s <= t)
    (ht : IsClosed (t : Set A)) : s.topologicalClosure <= t :=
  closure_minimal h ht

@[gcongr]
/--
theorem `Subalgebra.topologicalClosure_mono` / 定理 `Subalgebra.topologicalClosure_mono`

English:
theorem Subalgebra.topologicalClosure_mono
  given: {s t : Subalgebra R A} (h : s <= t)
  proof: closure_mono h

中文:
定理 子代数.topologicalClosure_mono
  条件: {s t : 子代数 R A} (h : s <= t)
  证明: closure_mono h

Depends on / 依赖: closure_mono
-/
theorem Subalgebra.topologicalClosure_mono {s t : Subalgebra R A} (h : s <= t) :
    s.topologicalClosure <= t.topologicalClosure :=
  closure_mono h

variable (R) in
open Algebra in
/--
lemma `Subalgebra.topologicalClosure_adjoin_le_centralizer_centralizer` / 引理 `Subalgebra.topologicalClosure_adjoin_le_centralizer_centralizer`

English:
lemma Subalgebra.topologicalClosure_adjoin_le_centralizer_centralizer
  given: [T2Space A] (s : Set A)
  proof: topologicalClosure_minimal (adjoin_le_centralizer_centralizer R s) (Set.isClosed_centralizer _)

中文:
引理 子代数.topologicalClosure_adjoin_le_centralizer_centralizer
  条件: [T2空间 A] (s : 集合 A)
  证明: topologicalClosure_minimal (adjoin_le_centralizer_centralizer R s) (Set.isClosed_centralizer _)

Depends on / 依赖: Set.isClosed_centralizer, adjoin_le_centralizer_centralizer, isClosed_centralizer, topologicalClosure_minimal
-/
lemma Subalgebra.topologicalClosure_adjoin_le_centralizer_centralizer [T2Space A] (s : Set A) :
    (adjoin R s).topologicalClosure <= centralizer R (centralizer R s) :=
  topologicalClosure_minimal (adjoin_le_centralizer_centralizer R s) (Set.isClosed_centralizer _)

/--
Definition of `Subalgebra.commSemiringTopologicalClosure` / `Subalgebra.commSemiringTopologicalClosure` 的定义

English:
abbreviation Subalgebra.commSemiringTopologicalClosure
  signature: [T2Space A] (s : Subalgebra R A)
  body: { s.topologicalClosure.toSemiring, s.toSubmonoid.commMonoidTopologicalClosure hs with }

中文:
缩写 子代数.commSemiringTopologicalClosure
  签名: [T2空间 A] (s : 子代数 R A)
  定义体: { s.topologicalClosure.toSemiring, s.toSubmonoid.commMonoidTopologicalClosure hs with }

Depends on / 依赖: commMonoidTopologicalClosure, s.toSubmonoid.commMonoidTopologicalClosure, s.topologicalClosure.toSemiring, toSemiring, toSubmonoid, topologicalClosure
-/
abbrev Subalgebra.commSemiringTopologicalClosure [T2Space A] (s : Subalgebra R A)
    (hs : forall x y : s, x * y = y * x) : CommSemiring s.topologicalClosure :=
  { s.topologicalClosure.toSemiring, s.toSubmonoid.commMonoidTopologicalClosure hs with }

/--
theorem `Subalgebra.topologicalClosure_comap_homeomorph` / 定理 `Subalgebra.topologicalClosure_comap_homeomorph`

English:
theorem Subalgebra.topologicalClosure_comap_homeomorph
  statement: (s : Subalgebra R A) {B : Type*}
  proof: by
  apply SetLike.ext'
  simp only [Subalgebra.topologicalClosure_coe]
  simp only [Subalgebra.coe_comap]
  rw [w]
  exact f'.preimage_closure _

中文:
定理 子代数.topologicalClosure_comap_homeomorph
  结论: (s : 子代数 R A) {B : 类型}
  证明: by
  apply SetLike.ext'
  simp only [Subalgebra.topologicalClosure_coe]
  simp only [Subalgebra.coe_comap]
  rw [w]
  exact f'.preimage_closure _

Depends on / 依赖: SetLike, SetLike.ext, Subalgebra, Subalgebra.coe_comap, Subalgebra.topologicalClosure_coe, coe_comap, preimage_closure, topologicalClosure_coe
-/
theorem Subalgebra.topologicalClosure_comap_homeomorph (s : Subalgebra R A) {B : Type*}
    [TopologicalSpace B] [Ring B] [IsSemitopologicalRing B] [Algebra R B] (f : B ->ₐ[R] A)
    (f' : B ≃ₜ A) (w : (f : B -> A) = f') :
    s.topologicalClosure.comap f = (s.comap f).topologicalClosure := by
  apply SetLike.ext'
  simp only [Subalgebra.topologicalClosure_coe]
  simp only [Subalgebra.coe_comap]
  rw [w]
  exact f'.preimage_closure _

variable (R)

open Subalgebra

/--
Definition of `Algebra.elemental` / `Algebra.elemental` 的定义

English:
definition Algebra.elemental
  signature: (x : A)
  body: (Algebra.adjoin R ({x} : Set A)).topologicalClosure

中文:
定义 代数.elemental
  签名: (x : A)
  定义体: (Algebra.adjoin R ({x} : Set A)).topologicalClosure

Depends on / 依赖: Algebra, Algebra.adjoin, adjoin, topologicalClosure
-/
def Algebra.elemental (x : A) : Subalgebra R A :=
  (Algebra.adjoin R ({x} : Set A)).topologicalClosure

namespace Algebra.elemental

@[simp, aesop safe (rule_sets := [SetLike])]
/--
theorem `self_mem` / 定理 `self_mem`

English:
theorem self_mem
  given: (x : A)
  statement: x in elemental R x
  proof: le_topologicalClosure _ self_mem_adjoin_singleton R x

中文:
定理 self_mem
  条件: (x : A)
  结论: x in elemental R x
  证明: le_topologicalClosure _ self_mem_adjoin_singleton R x

Depends on / 依赖: le_topologicalClosure, self_mem_adjoin_singleton
-/
theorem self_mem (x : A) : x in elemental R x :=
le_topologicalClosure _ self_mem_adjoin_singleton R x

variable {R} in
/--
theorem `le_of_mem` / 定理 `le_of_mem`

English:
theorem le_of_mem
  given: {x : A} {s : Subalgebra R A} (hs : IsClosed (s : Set A)) (hx : x in s)
  proof: topologicalClosure_minimal (adjoin_le <| by simpa using hx) hs

中文:
定理 le_of_mem
  条件: {x : A} {s : 子代数 R A} (hs : 是闭集 (s : 集合 A)) (hx : x in s)
  证明: topologicalClosure_minimal (adjoin_le <| by simpa using hx) hs

Depends on / 依赖: adjoin_le, topologicalClosure_minimal
-/
theorem le_of_mem {x : A} {s : Subalgebra R A} (hs : IsClosed (s : Set A)) (hx : x in s) :
    elemental R x <= s :=
  topologicalClosure_minimal (adjoin_le <| by simpa using hx) hs

variable {R} in
/--
theorem `le_iff_mem` / 定理 `le_iff_mem`

English:
theorem le_iff_mem
  given: {x : A} {s : Subalgebra R A} (hs : IsClosed (s : Set A))
  proof: ⟨fun h => h (self_mem R x), fun h => le_of_mem hs h⟩

中文:
定理 le_iff_mem
  条件: {x : A} {s : 子代数 R A} (hs : 是闭集 (s : 集合 A))
  证明: ⟨fun h => h (self_mem R x), fun h => le_of_mem hs h⟩

Depends on / 依赖: le_of_mem, self_mem
-/
theorem le_iff_mem {x : A} {s : Subalgebra R A} (hs : IsClosed (s : Set A)) :
    elemental R x <= s ↔ x in s :=
  ⟨fun h => h (self_mem R x), fun h => le_of_mem hs h⟩

/--
Instance `isClosed` / 实例 `isClosed`

English:
instance isClosed
  signature: (x : A)
  body: isClosed_topologicalClosure _

中文:
实例 isClosed
  签名: (x : A)
  定义体: isClosed_topologicalClosure _

Depends on / 依赖: isClosed_topologicalClosure
-/
instance isClosed (x : A) : IsClosed (elemental R x : Set A) :=
  isClosed_topologicalClosure _

open scoped IsMulCommutative in
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [T2Space
  signature: A] {x
  body: fast_instance% commSemiringTopologicalClosure _ mul_comm

中文:
实例 [T2空间
  签名: A] {x
  定义体: fast_instance% commSemiringTopologicalClosure _ mul_comm

Depends on / 依赖: commSemiringTopologicalClosure, fast_instance, mul_comm
-/
instance [T2Space A] {x : A} : CommSemiring (elemental R x) :=
  fast_instance% commSemiringTopologicalClosure _ mul_comm

instance {A : Type*} [UniformSpace A] [CompleteSpace A] [Semiring A]
    [IsSemitopologicalSemiring A] [Algebra R A] (x : A) :
    CompleteSpace (elemental R x) :=
  isClosed_closure.completeSpace_coe

/--
theorem `isClosedEmbedding_coe` / 定理 `isClosedEmbedding_coe`

English:
theorem isClosedEmbedding_coe
  given: (x : A)
  statement: IsClosedEmbedding ((↑) : elemental R x -> A) where
  proof: rfl
  injective := Subtype.coe_injective
  isClosed_range := by simpa using isClosed R x

中文:
定理 isClosedEmbedding_coe
  条件: (x : A)
  结论: 是闭嵌入 ((↑) : elemental R x -> A) where
  证明: rfl
  injective := Subtype.coe_injective
  isClosed_range := by simpa using isClosed R x
-/
theorem isClosedEmbedding_coe (x : A) : IsClosedEmbedding ((↑) : elemental R x -> A) where
  eq_induced := rfl
  injective := Subtype.coe_injective
  isClosed_range := by simpa using isClosed R x

/--
lemma `le_centralizer_centralizer` / 引理 `le_centralizer_centralizer`

English:
lemma le_centralizer_centralizer
  given: [T2Space A] (x : A)
  proof: topologicalClosure_adjoin_le_centralizer_centralizer ..

中文:
引理 le_centralizer_centralizer
  条件: [T2空间 A] (x : A)
  证明: topologicalClosure_adjoin_le_centralizer_centralizer ..

Depends on / 依赖: topologicalClosure_adjoin_le_centralizer_centralizer
-/
lemma le_centralizer_centralizer [T2Space A] (x : A) :
    elemental R x <= centralizer R (centralizer R {x}) :=
  topologicalClosure_adjoin_le_centralizer_centralizer ..

end Algebra.elemental

end TopologicalAlgebra

section Ring

variable {R : Type*} [CommRing R]
variable {A : Type u} [TopologicalSpace A]
variable [Ring A]
variable [Algebra R A] [IsSemitopologicalRing A]

/--
Definition of `Subalgebra.commRingTopologicalClosure` / `Subalgebra.commRingTopologicalClosure` 的定义

English:
abbreviation Subalgebra.commRingTopologicalClosure
  signature: [T2Space A] (s : Subalgebra R A)
  body: { s.topologicalClosure.toRing, s.toSubmonoid.commMonoidTopologicalClosure hs with }

中文:
缩写 子代数.commRingTopologicalClosure
  签名: [T2空间 A] (s : 子代数 R A)
  定义体: { s.topologicalClosure.toRing, s.toSubmonoid.commMonoidTopologicalClosure hs with }

Depends on / 依赖: commMonoidTopologicalClosure, s.toSubmonoid.commMonoidTopologicalClosure, s.topologicalClosure.toRing, toRing, toSubmonoid, topologicalClosure
-/
abbrev Subalgebra.commRingTopologicalClosure [T2Space A] (s : Subalgebra R A)
    (hs : forall x y : s, x * y = y * x) : CommRing s.topologicalClosure :=
  { s.topologicalClosure.toRing, s.toSubmonoid.commMonoidTopologicalClosure hs with }

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [T2Space
  signature: A] {x
  body: mul_comm

中文:
实例 [T2空间
  签名: A] {x
  定义体: mul_comm

Depends on / 依赖: mul_comm
-/
instance [T2Space A] {x : A} : CommRing (elemental R x) where
  mul_comm := mul_comm

end Ring
