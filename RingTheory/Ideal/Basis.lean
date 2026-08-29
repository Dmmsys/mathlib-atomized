/-
Copyright (c) 2018 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anne Baanen
-/
module

public import Mathlib.Algebra.Algebra.Bilinear
public import Mathlib.LinearAlgebra.Basis.Defs
public import Mathlib.LinearAlgebra.Basis.Submodule
public import Mathlib.RingTheory.Ideal.Span

/-!
# The basis of ideals

Some results involving `Ideal` and `Basis`.
-/

@[expose] public section

open Module

namespace Ideal

variable {ι R S : Type*} [CommSemiring R] [CommRing S] [IsDomain S] [Algebra R S]

/--
Definition of `basisSpanSingleton` / `basisSpanSingleton` 的定义

English:
definition basisSpanSingleton
  signature: (b : Basis ι R S) {x : S} (hx : x != 0)
  body: b.map
    LinearEquiv.ofInjective (LinearMap.mulLeft R x) (mul_right_injective₀ hx) ≪≫ₗ
        LinearEquiv.ofEq _ _
          (by
            ext
            simp [mem_span_singleton', mul_comm]) ≪≫ₗ
      (Submodule.restrictScalarsEquiv R S S (Ideal.span ({x} : Set S))).restrictScalars R

中文:
定义 basisSpanSingleton
  签名: (b : 基 ι R S) {x : S} (hx : x != 0)
  定义体: b.map
    LinearEquiv.ofInjective (LinearMap.mulLeft R x) (mul_right_injective₀ hx) ≪≫ₗ
        LinearEquiv.ofEq _ _
          (by
            ext
            simp [mem_span_singleton', mul_comm]) ≪≫ₗ
      (Submodule.restrictScalarsEquiv R S S (Ideal.span ({x} : Set S))).restrictScalars R

Depends on / 依赖: Ideal.span, LinearEquiv, LinearEquiv.ofEq, LinearEquiv.ofInjective, LinearMap, LinearMap.mulLeft, Submodule, Submodule.restrictScalarsEquiv, b.map, mem_span_singleton, mulLeft, mul_comm, ofInjective, restrictScalars, restrictScalarsEquiv
-/
noncomputable def basisSpanSingleton (b : Basis ι R S) {x : S} (hx : x != 0) :
    Basis ι R (span ({x} : Set S)) :=
b.map
    LinearEquiv.ofInjective (LinearMap.mulLeft R x) (mul_right_injective₀ hx) ≪≫ₗ
        LinearEquiv.ofEq _ _
          (by
            ext
            simp [mem_span_singleton', mul_comm]) ≪≫ₗ
      (Submodule.restrictScalarsEquiv R S S (Ideal.span ({x} : Set S))).restrictScalars R

set_option backward.isDefEq.respectTransparency false in
@[simp]
/--
theorem `basisSpanSingleton_apply` / 定理 `basisSpanSingleton_apply`

English:
theorem basisSpanSingleton_apply
  given: (b : Basis ι R S) {x : S} (hx : x != 0) (i : ι)
  proof: by
  simp only [basisSpanSingleton, Basis.map_apply, LinearEquiv.trans_apply,
    Submodule.restrictScalarsEquiv_apply, LinearEquiv.ofInjective_apply, LinearEquiv.coe_ofEq_apply,
    LinearEquiv.restrictScalars_apply, LinearMap.mulLeft_apply]

@[simp]

中文:
定理 basisSpanSingleton_apply
  条件: (b : 基 ι R S) {x : S} (hx : x != 0) (i : ι)
  证明: by
  simp only [basisSpanSingleton, Basis.map_apply, LinearEquiv.trans_apply,
    Submodule.restrictScalarsEquiv_apply, LinearEquiv.ofInjective_apply, LinearEquiv.coe_ofEq_apply,
    LinearEquiv.restrictScalars_apply, LinearMap.mulLeft_apply]

@[simp]

Depends on / 依赖: Basis.map_apply, LinearEquiv, LinearEquiv.coe_ofEq_apply, LinearEquiv.ofInjective_apply, LinearEquiv.restrictScalars_apply, LinearEquiv.trans_apply, LinearMap, LinearMap.mulLeft_apply, Submodule, Submodule.restrictScalarsEquiv_apply, basisSpanSingleton, coe_ofEq_apply, map_apply, mulLeft_apply, ofInjective_apply, restrictScalarsEquiv_apply, restrictScalars_apply, trans_apply
-/
theorem basisSpanSingleton_apply (b : Basis ι R S) {x : S} (hx : x != 0) (i : ι) :
    (basisSpanSingleton b hx i : S) = x * b i := by
  simp only [basisSpanSingleton, Basis.map_apply, LinearEquiv.trans_apply,
    Submodule.restrictScalarsEquiv_apply, LinearEquiv.ofInjective_apply, LinearEquiv.coe_ofEq_apply,
    LinearEquiv.restrictScalars_apply, LinearMap.mulLeft_apply]

@[simp]
/--
theorem `constr_basisSpanSingleton` / 定理 `constr_basisSpanSingleton`

English:
theorem constr_basisSpanSingleton
  statement: {N : Type*} [Semiring N] [Module N S] [SMulCommClass R N S]
  proof: b.ext fun i => by simp

中文:
定理 constr_basisSpanSingleton
  结论: {N : 类型} [半环 N] [模 N S] [标量交换类 R N S]
  证明: b.ext fun i => by simp

Depends on / 依赖: b.ext
-/
theorem constr_basisSpanSingleton {N : Type*} [Semiring N] [Module N S] [SMulCommClass R N S]
    (b : Basis ι R S) {x : S} (hx : x != 0) :
    (b.constr N).toFun (((↑) : _ -> S) ∘ (basisSpanSingleton b hx)) = Algebra.lmul R S x :=
  b.ext fun i => by simp

end Ideal

/--
theorem `Basis.mem_ideal_iff` / 定理 `Basis.mem_ideal_iff`

English:
theorem Basis.mem_ideal_iff
  statement: {ι R S : Type*} [CommSemiring R] [Semiring S] [Algebra R S]
  proof: (b.map ((I.restrictScalarsEquiv R _ _).restrictScalars R).symm).mem_submodule_iff

中文:
定理 基.mem_ideal_iff
  结论: {ι R S : 类型} [交换半环 R] [半环 S] [代数 R S]
  证明: (b.map ((I.restrictScalarsEquiv R _ _).restrictScalars R).symm).mem_submodule_iff

Depends on / 依赖: I.restrictScalarsEquiv, b.map, mem_submodule_iff, restrictScalars, restrictScalarsEquiv
-/
theorem Basis.mem_ideal_iff {ι R S : Type*} [CommSemiring R] [Semiring S] [Algebra R S]
    {I : Ideal S} (b : Basis ι R I) {x : S} :
    x in I ↔ exists c : ι ->₀ R, x = Finsupp.sum c fun i x => x • (b i : S) :=
  (b.map ((I.restrictScalarsEquiv R _ _).restrictScalars R).symm).mem_submodule_iff

/--
theorem `Basis.mem_ideal_iff'` / 定理 `Basis.mem_ideal_iff'`

English:
theorem Basis.mem_ideal_iff'
  statement: {ι R S : Type*} [Fintype ι] [CommSemiring R] [Semiring S] [Algebra R S]
  proof: (b.map ((I.restrictScalarsEquiv R _ _).restrictScalars R).symm).mem_submodule_iff'

中文:
定理 基.mem_ideal_iff'
  结论: {ι R S : 类型} [有限类型 ι] [交换半环 R] [半环 S] [代数 R S]
  证明: (b.map ((I.restrictScalarsEquiv R _ _).restrictScalars R).symm).mem_submodule_iff'

Depends on / 依赖: I.restrictScalarsEquiv, b.map, mem_submodule_iff, restrictScalars, restrictScalarsEquiv
-/
theorem Basis.mem_ideal_iff' {ι R S : Type*} [Fintype ι] [CommSemiring R] [Semiring S] [Algebra R S]
    {I : Ideal S} (b : Basis ι R I) {x : S} : x in I ↔ exists c : ι -> R, x = ∑ i, c i • (b i : S) :=
  (b.map ((I.restrictScalarsEquiv R _ _).restrictScalars R).symm).mem_submodule_iff'
