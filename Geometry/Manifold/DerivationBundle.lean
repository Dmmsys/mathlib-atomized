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
  [TopologicalSpace M] [ChartedSpace H M] (n : WithTop ℕ∞)

open scoped Manifold ContDiff

-- the following two instances prevent poorly understood typeclass inference timeout problems
/-
**smoothFunctionsAlgebra** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：smoothFunctionsAlgebra : Algebra 𝕜 C^∞⟮I, M; 𝕜⟯
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance smoothFunctionsAlgebra : Algebra 𝕜 C^∞⟮I, M; 𝕜⟯ := by infer_instance
/-
**smooth_functions_tower** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：smooth_functions_tower : IsScalarTower 𝕜 C^∞⟮I, M; 𝕜⟯ C^∞⟮I, M; 𝕜⟯
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `instContMDiffMulOfTopWithTopENat`：∀ {𝕜 : Type u_1} [inst : NontriviallyN
ormedField 𝕜] {H : Type u_2} [inst_1 : TopologicalSpace H] {E : Type u_3}   [ins
t_2 : NormedAddCommGro…
· 使用定理 `ContMDiffRing.toContMDiffMul`：∀ {𝕜 : Type u_1} [inst : NontriviallyNorme
dField 𝕜] {H : Type u_2} [inst_1 : TopologicalSpace H] {E : Type u_3}   [inst_2 
: NormedAddCommGro…
· 使用定理 `instFieldContMDiffRing`：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedField
 𝕜] {n : WithTop ℕ∞}, ContMDiffRing (modelWithCornersSelf 𝕜 𝕜) n 𝕜
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
-/
instance smooth_functions_tower : IsScalarTower 𝕜 C^∞⟮I, M; 𝕜⟯ C^∞⟮I, M; 𝕜⟯ := by infer_instance

/-- Type synonym, introduced to put a different `SMul` action on `C^n⟮I, M; 𝕜⟯`
which is defined as `f • r = f(x) * r`.
Denoted as `C^n⟮I, M; 𝕜⟯⟨x⟩` within the `Derivation` namespace. -/
@[nolint unusedArguments]
/-
**PointedContMDiffMap** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：PointedContMDiffMap (_ : M)
参数：_ : M。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Type synonym, introduced to put a different `SMul` action on `C^n⟮I, M; 𝕜⟯`
which is defined as `f • r = f(x) * r`.
Denoted as `C^n⟮I, M; 𝕜⟯⟨x⟩` within the `Derivation` namespace.
-/
def PointedContMDiffMap (_ : M) :=
  C^n⟮I, M; 𝕜⟯
deriving FunLike, CommRing, Algebra 𝕜

@[inherit_doc]
scoped[Derivation] notation "C^" n "⟮" I ", " M "; " 𝕜 "⟯⟨" x "⟩" => PointedContMDiffMap 𝕜 I M n x

variable {𝕜 M}

namespace PointedContMDiffMap

open scoped Derivation

/-
**PointedContMDiffMap.** 是 Mathlib 中的一个实例，位于命名空间 `PointedContMDiffMap`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {x : M} : Inhabited C^∞⟮I, M; 𝕜⟯⟨x⟩ :=
  ⟨0⟩
/-
**PointedContMDiffMap.** 是 Mathlib 中的一个实例，位于命名空间 `PointedContMDiffMap`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {x : M} : Algebra C^∞⟮I, M; 𝕜⟯⟨x⟩ C^∞⟮I, M; 𝕜⟯ :=
  inferInstanceAs <| Algebra C^∞⟮I, M; 𝕜⟯ C^∞⟮I, M; 𝕜⟯
/-
**PointedContMDiffMap.** 是 Mathlib 中的一个实例，位于命名空间 `PointedContMDiffMap`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {x : M} : IsScalarTower 𝕜 C^∞⟮I, M; 𝕜⟯⟨x⟩ C^∞⟮I, M; 𝕜⟯ :=
  IsScalarTower.right

variable {I}

/-- `ContMDiffMap.evalRingHom` gives rise to an algebra structure of `C^∞⟮I, M; 𝕜⟯` on `𝕜`. -/
/-
**PointedContMDiffMap.evalAlgebra** 是 Mathlib 中的一个实例，位于命名空间 `PointedContMDiffMap
`。
形式化陈述：evalAlgebra {x : M} : Algebra C^∞⟮I, M; 𝕜⟯⟨x⟩ 𝕜
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`ContMDiffMap.evalRingHom` gives rise to an algebra structure of `C^∞⟮I, M; 𝕜⟯` 
on `𝕜`.
-/
instance evalAlgebra {x : M} : Algebra C^∞⟮I, M; 𝕜⟯⟨x⟩ 𝕜 :=
  fast_instance% (ContMDiffMap.evalRingHom x : C^∞⟮I, M; 𝕜⟯⟨x⟩ →+* 𝕜).toAlgebra

/-- With the `evalAlgebra` algebra structure evaluation is actually an algebra morphism. -/
/-
**PointedContMDiffMap.eval** 是 Mathlib 中的一个定义，位于命名空间 `PointedContMDiffMap`。
形式化陈述：eval (x : M) : C^∞⟮I, M; 𝕜⟯ ->ₐ[C^∞⟮I, M; 𝕜⟯⟨x⟩] 𝕜
参数：x : M。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
With the `evalAlgebra` algebra structure evaluation is actually an algebra morph
ism.
-/
def eval (x : M) : C^∞⟮I, M; 𝕜⟯ →ₐ[C^∞⟮I, M; 𝕜⟯⟨x⟩] 𝕜 :=
  Algebra.ofId C^∞⟮I, M; 𝕜⟯⟨x⟩ 𝕜
/-
**PointedContMDiffMap.smul_def** 是 Mathlib 中的一个定理，位于命名空间 `PointedContMDiffMap`。
形式化陈述：smul_def (x : M) (f : C^∞⟮I, M; 𝕜⟯⟨x⟩) (k : 𝕜) : f • k = f x * k
参数：x : M；f : C^∞⟮I, M; 𝕜⟯⟨x⟩；k : 𝕜。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem smul_def (x : M) (f : C^∞⟮I, M; 𝕜⟯⟨x⟩) (k : 𝕜) : f • k = f x * k :=
  rfl

set_option backward.isDefEq.respectTransparency false in
/-
**PointedContMDiffMap.** 是 Mathlib 中的一个实例，位于命名空间 `PointedContMDiffMap`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (x : M) : IsScalarTower 𝕜 C^∞⟮I, M; 𝕜⟯⟨x⟩ 𝕜 where
  smul_assoc k f h := by
    rw [smul_def, smul_def, ContMDiffMap.coe_smul, Pi.smul_apply, smul_eq_mul, smul_eq_mul,
      mul_assoc]

end PointedContMDiffMap

open scoped Derivation

/-- The derivations at a point of a manifold. Some regard this as a possible definition of the
tangent space, as this coincides with the usual tangent space for finite-dimensional `C^∞` real
manifolds. The identification is not true in general, though. -/
/-
**PointDerivation** 是 Mathlib 中的一个缩写定义，位于命名空间 ``。
形式化陈述：PointDerivation (x : M)
参数：x : M。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The derivations at a point of a manifold. Some regard this as a possible definit
ion of the
tangent space, as this coincides with the usual tangent space for finite-dimensi
onal `C^∞` real
manifolds. The identification is not true in general, though.
-/
abbrev PointDerivation (x : M) :=
  Derivation 𝕜 C^∞⟮I, M; 𝕜⟯⟨x⟩ 𝕜

section

open scoped Derivation

variable (X : Derivation 𝕜 C^∞⟮I, M; 𝕜⟯ C^∞⟮I, M; 𝕜⟯) (f : C^∞⟮I, M; 𝕜⟯)

/-- Evaluation at a point gives rise to a `C^∞⟮I, M; 𝕜⟯`-linear map between `C^∞⟮I, M; 𝕜⟯` and `𝕜`.
-/
/-
**ContMDiffFunction.evalAt** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：ContMDiffFunction.evalAt (x : M) : C^∞⟮I, M; 𝕜⟯ ->ₗ[C^∞⟮I, M; 𝕜⟯⟨x⟩] 𝕜
参数：x : M。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Evaluation at a point gives rise to a `C^∞⟮I, M; 𝕜⟯`-linear map between `C^∞⟮I, 
M; 𝕜⟯` and `𝕜`.
-/
def ContMDiffFunction.evalAt (x : M) : C^∞⟮I, M; 𝕜⟯ →ₗ[C^∞⟮I, M; 𝕜⟯⟨x⟩] 𝕜 :=
  (PointedContMDiffMap.eval x).toLinearMap

namespace Derivation

variable {I}

set_option backward.isDefEq.respectTransparency false in
/-- The evaluation at a point as a linear map. -/
/-
**Derivation.evalAt** 是 Mathlib 中的一个定义，位于命名空间 `Derivation`。
形式化陈述：evalAt (x : M) : Derivation 𝕜 C^∞⟮I, M; 𝕜⟯ C^∞⟮I, M; 𝕜⟯ ->ₗ[C^∞⟮I, M; 𝕜⟯⟨x
⟩] PointDerivation I x
参数：x : M。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `PointedContMDiffMap.instIsScalarTowerSomeENatTopContMDiffMapModelWithCor
nersSelf`：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedField 𝕜] {E : Type u_2} [in
st_1 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜 E] {H : Type u_…
· 使用定理 `PointedContMDiffMap.instIsScalarTowerSomeENatTop`：∀ {𝕜 : Type u_1} [inst
 : NontriviallyNormedField 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [
inst_2 : NormedSpace 𝕜 E] {H : Type u_…

--- 原说明 ---
The evaluation at a point as a linear map.
-/
def evalAt (x : M) : Derivation 𝕜 C^∞⟮I, M; 𝕜⟯ C^∞⟮I, M; 𝕜⟯ →ₗ[C^∞⟮I, M; 𝕜⟯⟨x⟩]
  PointDerivation I x := (ContMDiffFunction.evalAt I x).compDer
/-
**Derivation.evalAt_apply** 是 Mathlib 中的一个定理，位于命名空间 `Derivation`。
形式化陈述：evalAt_apply (x : M) : evalAt x X f = (X f) x
参数：x : M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instFieldContMDiffRing`：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedField
 𝕜] {n : WithTop ℕ∞}, ContMDiffRing (modelWithCornersSelf 𝕜 𝕜) n 𝕜
· 使用定理 `IsScalarTower.to_smulCommClass`：∀ {R : Type u_1} [inst : CommSemiring R]
 {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [i
nst_3 : AddCommMonoi…
· 使用定理 `PointedContMDiffMap.instIsScalarTowerSomeENatTopContMDiffMapModelWithCor
nersSelf`：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedField 𝕜] {E : Type u_2} [in
st_1 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜 E] {H : Type u_…
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `PointedContMDiffMap.instIsScalarTowerSomeENatTop`：∀ {𝕜 : Type u_1} [inst
 : NontriviallyNormedField 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [
inst_2 : NormedSpace 𝕜 E] {H : Type u_…
-/
theorem evalAt_apply (x : M) : evalAt x X f = (X f) x :=
  rfl

end Derivation

variable {I} {E' : Type*} [NormedAddCommGroup E'] [NormedSpace 𝕜 E'] {H' : Type*}
  [TopologicalSpace H'] {I' : ModelWithCorners 𝕜 E' H'} {M' : Type*} [TopologicalSpace M']
  [ChartedSpace H' M']

set_option backward.isDefEq.respectTransparency false in
/-- The heterogeneous differential as a linear map, denoted as `𝒅ₕ` within the `Manifold` namespace.
Instead of taking a function as an argument, this
differential takes `h : f x = y`. It is particularly handy for situations where the points
at which it has to be evaluated are equal but not definitionally equal. -/
/-
**hfdifferential** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：hfdifferential {f : C^∞⟮I, M; I', M'⟯} {x : M} {y : M'} (h : f x = y) : Po
intDerivation I x ->ₗ[𝕜] PointDerivation I' y where toFun v
参数：h : f x = y。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The heterogeneous differential as a linear map, denoted as `𝒅ₕ` within the `Mani
fold` namespace.
Instead of taking a function as an argument, this
differential takes `h : f x = y`. It is particularly handy for situations where 
the points
at which it has to be evaluated are equal but not definitionally equal.
-/
def hfdifferential {f : C^∞⟮I, M; I', M'⟯} {x : M} {y : M'} (h : f x = y) :
    PointDerivation I x →ₗ[𝕜] PointDerivation I' y where
  toFun v :=
    Derivation.mk'
      { toFun := fun g => v (g.comp f)
        map_add' := fun g g' => by rw [ContMDiffMap.add_comp, Derivation.map_add]
        map_smul' := fun k g => by
          dsimp; rw [ContMDiffMap.smul_comp, Derivation.map_smul, smul_eq_mul] }
      fun g g' => by
        dsimp
        rw [ContMDiffMap.mul_comp, Derivation.leibniz,
          PointedContMDiffMap.smul_def, ContMDiffMap.comp_apply,
          PointedContMDiffMap.smul_def, ContMDiffMap.comp_apply, h]
        norm_cast
  map_smul' _ _ := rfl
  map_add' _ _ := rfl

/-- The homogeneous differential as a linear map, denoted as `𝒅` within the `Manifold` namespace. -/
/-
**fdifferential** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：fdifferential (f : C^∞⟮I, M; I', M'⟯) (x : M) : PointDerivation I x ->ₗ[𝕜]
 PointDerivation I' (f x)
参数：f : C^∞⟮I, M; I', M'⟯；x : M。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The homogeneous differential as a linear map, denoted as `𝒅` within the `Manifol
d` namespace.
-/
def fdifferential (f : C^∞⟮I, M; I', M'⟯) (x : M) :
    PointDerivation I x →ₗ[𝕜] PointDerivation I' (f x) :=
  hfdifferential (rfl : f x = f x)

-- Standard notation for the differential. The abbreviation is `MId`.
@[inherit_doc] scoped[Manifold] notation "𝒅" => fdifferential

-- Standard notation for the differential. The abbreviation is `MId`.
@[inherit_doc] scoped[Manifold] notation "𝒅ₕ" => hfdifferential

@[simp]
/-
**fdifferential_apply** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：fdifferential_apply (f : C^∞⟮I, M; I', M'⟯) {x : M} (v : PointDerivation I
 x) (g : C^∞⟮I', M'; 𝕜⟯) : 𝒅 f x v g = v (g.comp f)
参数：f : C^∞⟮I, M; I', M'⟯；v : PointDerivation I x；g : C^∞⟮I', M'; 𝕜⟯。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `IsScalarTower.to_smulCommClass`：∀ {R : Type u_1} [inst : CommSemiring R]
 {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [i
nst_3 : AddCommMonoi…
· 使用定理 `PointedContMDiffMap.instIsScalarTowerSomeENatTop`：∀ {𝕜 : Type u_1} [inst
 : NontriviallyNormedField 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [
inst_2 : NormedSpace 𝕜 E] {H : Type u_…
-/
theorem fdifferential_apply (f : C^∞⟮I, M; I', M'⟯) {x : M} (v : PointDerivation I x)
    (g : C^∞⟮I', M'; 𝕜⟯) : 𝒅 f x v g = v (g.comp f) :=
  rfl
@[simp]
/-
**hfdifferential_apply** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：hfdifferential_apply {f : C^∞⟮I, M; I', M'⟯} {x : M} {y : M'} (h : f x = y
) (v : PointDerivation I x) (g : C^∞⟮I', M'; 𝕜⟯) : 𝒅ₕ h v g = 𝒅 f x v g
参数：h : f x = y；v : PointDerivation I x；g : C^∞⟮I', M'; 𝕜⟯。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `IsScalarTower.to_smulCommClass`：∀ {R : Type u_1} [inst : CommSemiring R]
 {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [i
nst_3 : AddCommMonoi…
· 使用定理 `PointedContMDiffMap.instIsScalarTowerSomeENatTop`：∀ {𝕜 : Type u_1} [inst
 : NontriviallyNormedField 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [
inst_2 : NormedSpace 𝕜 E] {H : Type u_…
-/
theorem hfdifferential_apply {f : C^∞⟮I, M; I', M'⟯} {x : M} {y : M'} (h : f x = y)
    (v : PointDerivation I x) (g : C^∞⟮I', M'; 𝕜⟯) : 𝒅ₕ h v g = 𝒅 f x v g :=
  rfl
variable {E'' : Type*} [NormedAddCommGroup E''] [NormedSpace 𝕜 E''] {H'' : Type*}
  [TopologicalSpace H''] {I'' : ModelWithCorners 𝕜 E'' H''} {M'' : Type*} [TopologicalSpace M'']
  [ChartedSpace H'' M'']

@[simp]
/-
**fdifferential_comp** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：fdifferential_comp (g : C^∞⟮I', M'; I'', M''⟯) (f : C^∞⟮I, M; I', M'⟯) (x 
: M) : 𝒅 (g.comp f) x = (𝒅 g (f x)).comp (𝒅 f x)
参数：g : C^∞⟮I', M'; I'', M''⟯；f : C^∞⟮I, M; I', M'⟯；x : M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `IsScalarTower.to_smulCommClass`：∀ {R : Type u_1} [inst : CommSemiring R]
 {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [i
nst_3 : AddCommMonoi…
· 使用定理 `PointedContMDiffMap.instIsScalarTowerSomeENatTop`：∀ {𝕜 : Type u_1} [inst
 : NontriviallyNormedField 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [
inst_2 : NormedSpace 𝕜 E] {H : Type u_…
-/
theorem fdifferential_comp (g : C^∞⟮I', M'; I'', M''⟯) (f : C^∞⟮I, M; I', M'⟯) (x : M) :
    𝒅 (g.comp f) x = (𝒅 g (f x)).comp (𝒅 f x) :=
  rfl

end

