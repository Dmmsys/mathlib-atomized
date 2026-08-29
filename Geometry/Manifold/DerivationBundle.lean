/-
Copyright (c) 2020 Nicolò Cavalleri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nicolò Cavalleri
-/
module

public import Mathlib.Geometry.Manifold.Algebra.SmoothFunctions
public import Mathlib.RingTheory.Derivation.Basic

/-!

# Derivation bundle

In this file we define the derivations at a point of a manifold on the algebra of smooth functions.
Moreover, we define the differential of a function in terms of derivations.

The content of this file is not meant to be regarded as an alternative definition to the current
tangent bundle but rather as a purely algebraic theory that provides a purely algebraic definition
of the Lie algebra for a Lie group. This theory coincides with the usual tangent bundle in the
case of finite-dimensional `C^∞` real manifolds, but not in the general case.
-/

@[expose] public section


variable (𝕜 : Type*) [NontriviallyNormedField 𝕜] {E : Type*} [NormedAddCommGroup E]
  [NormedSpace 𝕜 E] {H : Type*} [TopologicalSpace H] (I : ModelWithCorners 𝕜 E H) (M : Type*)
  [TopologicalSpace M] [ChartedSpace H M] (n : WithTop Nat∞)

open scoped Manifold ContDiff

-- the following two instances prevent poorly understood typeclass inference timeout problems
/--
Instance `smoothFunctionsAlgebra` / 实例 `smoothFunctionsAlgebra`

English:
instance smoothFunctionsAlgebra
  signature: : Algebra 𝕜 C^∞⟮I, M; 𝕜⟯
  body: by infer_instance

中文:
实例 smoothFunctionsAlgebra
  签名: : Algebra 𝕜 C^∞⟮I, M; 𝕜⟯
  定义体: by infer_instance

Depends on / 依赖: infer_instance
-/
instance smoothFunctionsAlgebra : Algebra 𝕜 C^∞⟮I, M; 𝕜⟯ := by infer_instance

/--
Instance `smooth_functions_tower` / 实例 `smooth_functions_tower`

English:
instance smooth_functions_tower
  signature: : IsScalarTower 𝕜 C^∞⟮I, M; 𝕜⟯ C^∞⟮I, M; 𝕜⟯
  body: by infer_instance

中文:
实例 smooth_functions_tower
  签名: : IsScalarTower 𝕜 C^∞⟮I, M; 𝕜⟯ C^∞⟮I, M; 𝕜⟯
  定义体: by infer_instance

Depends on / 依赖: infer_instance
-/
instance smooth_functions_tower : IsScalarTower 𝕜 C^∞⟮I, M; 𝕜⟯ C^∞⟮I, M; 𝕜⟯ := by infer_instance

/-- Type synonym, introduced to put a different `SMul` action on `C^n⟮I, M; 𝕜⟯`
which is defined as `f • r = f(x) * r`.
Denoted as `C^n⟮I, M; 𝕜⟯⟨x⟩` within the `Derivation` namespace. -/
@[nolint unusedArguments]
/--
Definition of `PointedContMDiffMap` / `PointedContMDiffMap` 的定义

English:
definition PointedContMDiffMap
  signature: (_ : M)
  body: C^n⟮I, M; 𝕜⟯
deriving FunLike, CommRing, Algebra 𝕜

@[inherit_doc]
scoped[Derivation] notation "C^" n "⟮" I ", " M "; " 𝕜 "⟯⟨" x "⟩" => PointedContMDiffMap 𝕜 I M n x

中文:
定义 PointedContMDiffMap
  签名: (_ : M)
  定义体: C^n⟮I, M; 𝕜⟯
deriving FunLike, CommRing, Algebra 𝕜

@[inherit_doc]
scoped[Derivation] notation "C^" n "⟮" I ", " M "; " 𝕜 "⟯⟨" x "⟩" => PointedContMDiffMap 𝕜 I M n x
-/
def PointedContMDiffMap (_ : M) :=
  C^n⟮I, M; 𝕜⟯
deriving FunLike, CommRing, Algebra 𝕜

@[inherit_doc]
scoped[Derivation] notation "C^" n "⟮" I ", " M "; " 𝕜 "⟯⟨" x "⟩" => PointedContMDiffMap 𝕜 I M n x

variable {𝕜 M}

namespace PointedContMDiffMap

open scoped Derivation

instance {x : M} : Inhabited C^∞⟮I, M; 𝕜⟯⟨x⟩ :=
  ⟨0⟩

instance {x : M} : Algebra C^∞⟮I, M; 𝕜⟯⟨x⟩ C^∞⟮I, M; 𝕜⟯ :=
inferInstanceAs Algebra C^∞⟮I, M; 𝕜⟯ C^∞⟮I, M; 𝕜⟯

instance {x : M} : IsScalarTower 𝕜 C^∞⟮I, M; 𝕜⟯⟨x⟩ C^∞⟮I, M; 𝕜⟯ :=
  IsScalarTower.right

variable {I}

/--
Instance `evalAlgebra` / 实例 `evalAlgebra`

English:
instance evalAlgebra
  signature: {x : M}
  body: fast_instance% (ContMDiffMap.evalRingHom x : C^∞⟮I, M; 𝕜⟯⟨x⟩ ->+* 𝕜).toAlgebra

中文:
实例 evalAlgebra
  签名: {x : M}
  定义体: fast_instance% (ContMDiffMap.evalRingHom x : C^∞⟮I, M; 𝕜⟯⟨x⟩ ->+* 𝕜).toAlgebra

Depends on / 依赖: ContMDiffMap, ContMDiffMap.evalRingHom, evalRingHom, fast_instance, toAlgebra
-/
instance evalAlgebra {x : M} : Algebra C^∞⟮I, M; 𝕜⟯⟨x⟩ 𝕜 :=
  fast_instance% (ContMDiffMap.evalRingHom x : C^∞⟮I, M; 𝕜⟯⟨x⟩ ->+* 𝕜).toAlgebra

/--
Definition of `eval` / `eval` 的定义

English:
definition eval
  signature: (x : M)
  body: Algebra.ofId C^∞⟮I, M; 𝕜⟯⟨x⟩ 𝕜

中文:
定义 eval
  签名: (x : M)
  定义体: Algebra.ofId C^∞⟮I, M; 𝕜⟯⟨x⟩ 𝕜

Depends on / 依赖: Algebra, Algebra.ofId
-/
def eval (x : M) : C^∞⟮I, M; 𝕜⟯ ->ₐ[C^∞⟮I, M; 𝕜⟯⟨x⟩] 𝕜 :=
  Algebra.ofId C^∞⟮I, M; 𝕜⟯⟨x⟩ 𝕜

/--
theorem `smul_def` / 定理 `smul_def`

English:
theorem smul_def
  given: (x : M) (f : C^∞⟮I, M; 𝕜⟯⟨x⟩) (k : 𝕜)
  statement: f • k = f x * k
  proof: rfl

中文:
定理 smul_def
  条件: (x : M) (f : C^∞⟮I, M; 𝕜⟯⟨x⟩) (k : 𝕜)
  结论: f • k = f x * k
  证明: rfl
-/
theorem smul_def (x : M) (f : C^∞⟮I, M; 𝕜⟯⟨x⟩) (k : 𝕜) : f • k = f x * k :=
  rfl

set_option backward.isDefEq.respectTransparency false in
instance (x : M) : IsScalarTower 𝕜 C^∞⟮I, M; 𝕜⟯⟨x⟩ 𝕜 where
  smul_assoc k f h := by
    rw [smul_def]; rw [smul_def]; rw [ContMDiffMap.coe_smul]; rw [Pi.smul_apply]; rw [smul_eq_mul]; rw [smul_eq_mul]; rw [mul_assoc]

end PointedContMDiffMap

open scoped Derivation

/--
Definition of `PointDerivation` / `PointDerivation` 的定义

English:
abbreviation PointDerivation
  signature: (x : M)
  body: Derivation 𝕜 C^∞⟮I, M; 𝕜⟯⟨x⟩ 𝕜

中文:
缩写 PointDerivation
  签名: (x : M)
  定义体: Derivation 𝕜 C^∞⟮I, M; 𝕜⟯⟨x⟩ 𝕜

Depends on / 依赖: Derivation
-/
abbrev PointDerivation (x : M) :=
  Derivation 𝕜 C^∞⟮I, M; 𝕜⟯⟨x⟩ 𝕜

section

open scoped Derivation

variable (X : Derivation 𝕜 C^∞⟮I, M; 𝕜⟯ C^∞⟮I, M; 𝕜⟯) (f : C^∞⟮I, M; 𝕜⟯)

/--
Definition of `ContMDiffFunction.evalAt` / `ContMDiffFunction.evalAt` 的定义

English:
definition ContMDiffFunction.evalAt
  signature: (x : M)
  body: (PointedContMDiffMap.eval x).toLinearMap

中文:
定义 ContMDiffFunction.evalAt
  签名: (x : M)
  定义体: (PointedContMDiffMap.eval x).toLinearMap

Depends on / 依赖: PointedContMDiffMap, PointedContMDiffMap.eval, toLinearMap
-/
def ContMDiffFunction.evalAt (x : M) : C^∞⟮I, M; 𝕜⟯ ->ₗ[C^∞⟮I, M; 𝕜⟯⟨x⟩] 𝕜 :=
  (PointedContMDiffMap.eval x).toLinearMap

namespace Derivation

variable {I}

set_option backward.isDefEq.respectTransparency false in
/--
Definition of `evalAt` / `evalAt` 的定义

English:
definition evalAt
  signature: (x : M)
  body: (ContMDiffFunction.evalAt I x).compDer

中文:
定义 evalAt
  签名: (x : M)
  定义体: (ContMDiffFunction.evalAt I x).compDer

Depends on / 依赖: ContMDiffFunction, ContMDiffFunction.evalAt, compDer, evalAt
-/
def evalAt (x : M) : Derivation 𝕜 C^∞⟮I, M; 𝕜⟯ C^∞⟮I, M; 𝕜⟯ ->ₗ[C^∞⟮I, M; 𝕜⟯⟨x⟩]
  PointDerivation I x := (ContMDiffFunction.evalAt I x).compDer

/--
theorem `evalAt_apply` / 定理 `evalAt_apply`

English:
theorem evalAt_apply
  given: (x : M)
  statement: evalAt x X f = (X f) x
  proof: rfl

中文:
定理 evalAt_apply
  条件: (x : M)
  结论: evalAt x X f = (X f) x
  证明: rfl
-/
theorem evalAt_apply (x : M) : evalAt x X f = (X f) x :=
  rfl

end Derivation

variable {I} {E' : Type*} [NormedAddCommGroup E'] [NormedSpace 𝕜 E'] {H' : Type*}
  [TopologicalSpace H'] {I' : ModelWithCorners 𝕜 E' H'} {M' : Type*} [TopologicalSpace M']
  [ChartedSpace H' M']

set_option backward.isDefEq.respectTransparency false in
/--
Definition of `hfdifferential` / `hfdifferential` 的定义

English:
definition hfdifferential
  signature: {f : C^∞⟮I, M; I', M'⟯} {x : M} {y : M'} (h : f x = y)
  body: Derivation.mk'
      { toFun := fun g => v (g.comp f)
        map_add' := fun g g' => by rw [ContMDiffMap.add_comp, Derivation.map_add]
        map_smul' := fun k g => by
          dsimp; rw [ContMDiffMap.smul_comp, Derivation.map_smul, smul_eq_mul] }
      fun g g' => by
        dsimp
        rw [C

中文:
定义 hfdifferential
  签名: {f : C^∞⟮I, M; I', M'⟯} {x : M} {y : M'} (h : f x = y)
  定义体: Derivation.mk'
      { toFun := fun g => v (g.comp f)
        map_add' := fun g g' => by rw [ContMDiffMap.add_comp, Derivation.map_add]
        map_smul' := fun k g => by
          dsimp; rw [ContMDiffMap.smul_comp, Derivation.map_smul, smul_eq_mul] }
      fun g g' => by
        dsimp
        rw [C

Depends on / 依赖: ContMDiffMap, ContMDiffMap.add_comp, ContMDiffMap.comp_apply, ContMDiffMap.mul_comp, ContMDiffMap.smul_comp, Derivation, Derivation.leibniz, Derivation.map_add, Derivation.map_smul, Derivation.mk, PointedContMDiffMap, PointedContMDiffMap.smul_def, add_comp, comp_apply, g.comp, leibniz, map_add, map_smul, mul_comp, smul_comp
-/
def hfdifferential {f : C^∞⟮I, M; I', M'⟯} {x : M} {y : M'} (h : f x = y) :
    PointDerivation I x ->ₗ[𝕜] PointDerivation I' y where
  toFun v :=
    Derivation.mk'
      { toFun := fun g => v (g.comp f)
        map_add' := fun g g' => by rw [ContMDiffMap.add_comp, Derivation.map_add]
        map_smul' := fun k g => by
          dsimp; rw [ContMDiffMap.smul_comp, Derivation.map_smul, smul_eq_mul] }
      fun g g' => by
        dsimp
        rw [ContMDiffMap.mul_comp]; rw [Derivation.leibniz]; rw [PointedContMDiffMap.smul_def]; rw [ContMDiffMap.comp_apply]; rw [PointedContMDiffMap.smul_def]; rw [ContMDiffMap.comp_apply]; rw [h]
        norm_cast
  map_smul' _ _ := rfl
  map_add' _ _ := rfl

/--
Definition of `fdifferential` / `fdifferential` 的定义

English:
definition fdifferential
  signature: (f : C^∞⟮I, M; I', M'⟯) (x : M)
  body: hfdifferential (rfl : f x = f x)

中文:
定义 fdifferential
  签名: (f : C^∞⟮I, M; I', M'⟯) (x : M)
  定义体: hfdifferential (rfl : f x = f x)

Depends on / 依赖: hfdifferential
-/
def fdifferential (f : C^∞⟮I, M; I', M'⟯) (x : M) :
    PointDerivation I x ->ₗ[𝕜] PointDerivation I' (f x) :=
  hfdifferential (rfl : f x = f x)

-- Standard notation for the differential. The abbreviation is `MId`.
@[inherit_doc] scoped[Manifold] notation "𝒅" => fdifferential

-- Standard notation for the differential. The abbreviation is `MId`.
@[inherit_doc] scoped[Manifold] notation "𝒅ₕ" => hfdifferential

@[simp]
/--
theorem `fdifferential_apply` / 定理 `fdifferential_apply`

English:
theorem fdifferential_apply
  statement: (f : C^∞⟮I, M; I', M'⟯) {x : M} (v : PointDerivation I x)
  proof: rfl
@[simp]

中文:
定理 fdifferential_apply
  结论: (f : C^∞⟮I, M; I', M'⟯) {x : M} (v : PointDerivation I x)
  证明: rfl
@[simp]
-/
theorem fdifferential_apply (f : C^∞⟮I, M; I', M'⟯) {x : M} (v : PointDerivation I x)
    (g : C^∞⟮I', M'; 𝕜⟯) : 𝒅 f x v g = v (g.comp f) :=
  rfl
@[simp]
/--
theorem `hfdifferential_apply` / 定理 `hfdifferential_apply`

English:
theorem hfdifferential_apply
  statement: {f : C^∞⟮I, M; I', M'⟯} {x : M} {y : M'} (h : f x = y)
  proof: rfl

中文:
定理 hfdifferential_apply
  结论: {f : C^∞⟮I, M; I', M'⟯} {x : M} {y : M'} (h : f x = y)
  证明: rfl

Depends on / 依赖: ChartedSpace, ModelWithCorners, NormedAddCommGroup, NormedSpace, TopologicalSpace, variable
-/
theorem hfdifferential_apply {f : C^∞⟮I, M; I', M'⟯} {x : M} {y : M'} (h : f x = y)
    (v : PointDerivation I x) (g : C^∞⟮I', M'; 𝕜⟯) : 𝒅ₕ h v g = 𝒅 f x v g :=
  rfl
variable {E'' : Type*} [NormedAddCommGroup E''] [NormedSpace 𝕜 E''] {H'' : Type*}
  [TopologicalSpace H''] {I'' : ModelWithCorners 𝕜 E'' H''} {M'' : Type*} [TopologicalSpace M'']
  [ChartedSpace H'' M'']

@[simp]
/--
theorem `fdifferential_comp` / 定理 `fdifferential_comp`

English:
theorem fdifferential_comp
  given: (g : C^∞⟮I', M'; I'', M''⟯) (f : C^∞⟮I, M; I', M'⟯) (x : M)
  proof: rfl

中文:
定理 fdifferential_comp
  条件: (g : C^∞⟮I', M'; I'', M''⟯) (f : C^∞⟮I, M; I', M'⟯) (x : M)
  证明: rfl
-/
theorem fdifferential_comp (g : C^∞⟮I', M'; I'', M''⟯) (f : C^∞⟮I, M; I', M'⟯) (x : M) :
    𝒅 (g.comp f) x = (𝒅 g (f x)).comp (𝒅 f x) :=
  rfl

end
