/-
Copyright (c) 2025 Yaël Dillies, Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Andrew Yang
-/
module

public import Mathlib.LinearAlgebra.BilinearMap
public import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Basic

/-!
# Continuous perfect pairings

This file defines continuous perfect pairings.

For a topological ring `R` and two topological modules `M` and `N`, a continuous perfect pairing is
a continuous bilinear map `M × N → R` that is bijective in both arguments.

We require continuity in the forward direction only so that we can put several different topologies
on the continuous dual (e.g., strong, weak, weak-\*). For example, if `M` is weakly reflexive then
there is a continuous perfect pairing between `M` and `WeakDual R M`, even though the map
`WeakDual R M ≃ₗ[R] StrongDual R M` (where `StrongDual R M` is equipped with its strong topology) is
not in general a homeomorphism.

## TODO

Adapt `PerfectPairing` to this Prop-valued typeclass paradigm
-/

@[expose] public section

open Function

namespace LinearMap
variable {R M N : Type*}
  [CommRing R] [TopologicalSpace R] [AddCommGroup M] [Module R M] [TopologicalSpace M]
  [AddCommGroup N] [Module R N] [TopologicalSpace N] (p : M →ₗ[R] N →ₗ[R] R) {x : M} {y : N}

/-- For a topological ring `R` and two topological modules `M` and `N`, a continuous perfect pairing
is a continuous bilinear map `M × N → R` that is bijective in both arguments.

We require continuity in the forward direction only so that we can put several different topologies
on the continuous dual: strong, weak, weak-\* topology... -/
@[ext]
/-
**LinearMap.IsContPerfPair** 是 Mathlib 中的一个类，位于命名空间 `LinearMap`。
形式化陈述：IsContPerfPair (p : M ->ₗ[R] N ->ₗ[R] R) where continuous_uncurry (p) : Co
ntinuous fun (x, y) => p x y bijective_left (p) : Bijective fun x => ContinuousL
inearMap.mk (p x) continuous_uncurry.comp .prodMk_right x bijective_right (p) : 
Bijective fun y => ContinuousLinearMap.mk (p.flip y) continuous_uncurry.comp .pr
odMk_left y  variable [p.IsContPerfPair]  alias continuous_uncurry_of_isContPerf
Pair
参数：p : M ->ₗ[R] N ->ₗ[R] R；p。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
For a topological ring `R` and two topological modules `M` and `N`, a continuous
 perfect pairing
is a continuous bilinear map `M × N → R` that is bijective in both arguments.

We require continuity in the forward direction only so that we can put several d
ifferent topologies
on the continuous dual: strong, weak, weak-\* topology...
-/
class IsContPerfPair (p : M →ₗ[R] N →ₗ[R] R) where
  continuous_uncurry (p) : Continuous fun (x, y) ↦ p x y
  bijective_left (p) :
    Bijective fun x ↦ ContinuousLinearMap.mk (p x) <| continuous_uncurry.comp <| .prodMk_right x
  bijective_right (p) :
    Bijective fun y ↦ ContinuousLinearMap.mk (p.flip y) <| continuous_uncurry.comp <| .prodMk_left y

variable [p.IsContPerfPair]

alias continuous_uncurry_of_isContPerfPair :=
  IsContPerfPair.continuous_uncurry

/-- Given a perfect pairing between `M` and `N`, we may interchange the roles of `M` and `N`. -/
/-
**LinearMap.flip.instIsContPerfPair** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap.flip`。
形式化陈述：∀ {R : Type u_1} {M : Type u_2} {N : Type u_3} [inst : CommRing R] [inst_1
 : TopologicalSpace R]   [inst_2 : AddCommGroup M] [inst_3 : _root_.Module R M] 
[inst_4 : TopologicalSpace M] [inst_5 : AddCommGroup N]   [inst_6 : _root_.Modul
e R N] [inst_7 : TopologicalSpace N] (p : M →ₗ[R] N →ₗ[R] R) [p.IsContPerfPair],
   p.flip.IsContPerfPair
参数：p : M →ₗ[R] N →ₗ[R] R。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `Continuous.comp`：Continuous.comp {g : Y -> Z} (hg : Continuous g) (hf : 
Continuous f) : Continuous (g ∘ f)
· 使用定理 `LinearMap.continuous_uncurry_of_isContPerfPair`：∀ {R : Type u_1} {M : Ty
pe u_2} {N : Type u_3} {inst : CommRing R} {inst_1 : TopologicalSpace R}   {inst
_2 : AddCommGroup M} {inst_3 : _root…
· 使用定理 `continuous_swap`：continuous_swap : Continuous (Prod.swap : X × Y -> Y × 
X)
· 使用定理 `LinearMap.IsContPerfPair.bijective_right`：∀ {R : Type u_1} {M : Type u_2
} {N : Type u_3} {inst : CommRing R} {inst_1 : TopologicalSpace R}   {inst_2 : A
ddCommGroup M} {inst_3 : _root…
· 使用定理 `LinearMap.IsContPerfPair.bijective_left`：∀ {R : Type u_1} {M : Type u_2}
 {N : Type u_3} {inst : CommRing R} {inst_1 : TopologicalSpace R}   {inst_2 : Ad
dCommGroup M} {inst_3 : _root…

--- 原说明 ---
Given a perfect pairing between `M` and `N`, we may interchange the roles of `M`
 and `N`.
-/
instance flip.instIsContPerfPair : p.flip.IsContPerfPair where
  continuous_uncurry := p.continuous_uncurry_of_isContPerfPair.comp continuous_swap
  bijective_left := IsContPerfPair.bijective_right p
  bijective_right := IsContPerfPair.bijective_left p
/-
**LinearMap.continuous_of_isContPerfPair** 是 Mathlib 中的一个引理，位于命名空间 `LinearMap`。
形式化陈述：continuous_of_isContPerfPair : Continuous (p x)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `Continuous.comp`：Continuous.comp {g : Y -> Z} (hg : Continuous g) (hf : 
Continuous f) : Continuous (g ∘ f)
· 使用定理 `LinearMap.continuous_uncurry_of_isContPerfPair`：∀ {R : Type u_1} {M : Ty
pe u_2} {N : Type u_3} {inst : CommRing R} {inst_1 : TopologicalSpace R}   {inst
_2 : AddCommGroup M} {inst_3 : _root…
· 使用定理 `Continuous.prodMk_right`：Continuous.prodMk_right (x : X) : Continuous fu
n y : Y => (x, y)
-/
lemma continuous_of_isContPerfPair : Continuous (p x) :=
  p.continuous_uncurry_of_isContPerfPair.comp <| .prodMk_right x

variable [IsTopologicalRing R]

/-- Turn a continuous perfect pairing between `M` and `N` into a map from `M` to continuous linear
maps `N → R`. -/
/-
**LinearMap.toContPerfPair** 是 Mathlib 中的一个定义，位于命名空间 `LinearMap`。
形式化陈述：toContPerfPair : M ≃ₗ[R] StrongDual R N
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `LinearMap.IsContPerfPair.bijective_left`：∀ {R : Type u_1} {M : Type u_2}
 {N : Type u_3} {inst : CommRing R} {inst_1 : TopologicalSpace R}   {inst_2 : Ad
dCommGroup M} {inst_3 : _root…

--- 原说明 ---
Turn a continuous perfect pairing between `M` and `N` into a map from `M` to con
tinuous linear
maps `N → R`.
-/
noncomputable def toContPerfPair : M ≃ₗ[R] StrongDual R N :=
  .ofBijective { toFun := _, map_add' x y := by ext; simp, map_smul' r x := by ext; simp } <|
    IsContPerfPair.bijective_left p
/-
**LinearMap.toLinearMap_toContPerfPair** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap`。
形式化陈述：∀ {R : Type u_1} {M : Type u_2} {N : Type u_3} [inst : CommRing R] [inst_1
 : TopologicalSpace R]   [inst_2 : AddCommGroup M] [inst_3 : _root_.Module R M] 
[inst_4 : TopologicalSpace M] [inst_5 : AddCommGroup N]   [inst_6 : _root_.Modul
e R N] [inst_7 : TopologicalSpace N] (p : M →ₗ[R] N →ₗ[R] R) [inst_8 : p.IsContP
erfPair]   [inst_9 : IsTopologicalRing R] (x : M), ↑(p.toContPerfPair x) = p x
参数：p : M →ₗ[R] N →ₗ[R] R；x : M；p.toContPerfPair x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
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
-/
@[simp] lemma toLinearMap_toContPerfPair (x : M) : p.toContPerfPair x = p x := rfl
/-
**LinearMap.toContPerfPair_apply** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap`。
形式化陈述：∀ {R : Type u_1} {M : Type u_2} {N : Type u_3} [inst : CommRing R] [inst_1
 : TopologicalSpace R]   [inst_2 : AddCommGroup M] [inst_3 : _root_.Module R M] 
[inst_4 : TopologicalSpace M] [inst_5 : AddCommGroup N]   [inst_6 : _root_.Modul
e R N] [inst_7 : TopologicalSpace N] (p : M →ₗ[R] N →ₗ[R] R) [inst_8 : p.IsContP
erfPair]   [inst_9 : IsTopologicalRing R] (x : M) (y : N), (p.toContPerfPair x) 
y = (p x) y
参数：p : M →ₗ[R] N →ₗ[R] R；x : M；y : N；p.toContPerfPair x；p x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
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
-/
@[simp] lemma toContPerfPair_apply (x : M) (y : N) : p.toContPerfPair x y = p x y := rfl

end LinearMap

