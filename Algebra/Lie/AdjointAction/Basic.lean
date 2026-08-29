/-
Copyright (c) 2026 Janos Wolosz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Janos Wolosz
-/
module

public import Mathlib.Algebra.Algebra.Bilinear
public import Mathlib.Algebra.Lie.OfAssociative
public import Mathlib.LinearAlgebra.Semisimple
public import Mathlib.RingTheory.Nilpotent.Lemmas

/-!
# Properties of the adjoint action

Theorems about the adjoint action `LieAlgebra.ad` on associative algebras.

## Main results

* `LieAlgebra.commute_ad_of_commute`: commuting elements have commuting adjoints.
* `LieAlgebra.ad_nilpotent_of_nilpotent`: the adjoint of a nilpotent element is nilpotent.
* `LieAlgebra.ad_isSemisimple_of_isSemisimple`: the adjoint of a semisimple element is semisimple.
-/

public section

section CommRing

attribute [local instance 100] LieRing.ofAssociativeRing

variable {R A : Type*} [CommRing R] [Ring A] [Algebra R A]

set_option backward.isDefEq.respectTransparency false in
/--
theorem `LieAlgebra.commute_ad_of_commute` / 定理 `LieAlgebra.commute_ad_of_commute`

English:
theorem LieAlgebra.commute_ad_of_commute
  given: {a b : A} (h : Commute a b)
  proof: by
  rw [Commute]; rw [SemiconjBy]; rw [← sub_eq_zero]; rw [← Ring.lie_def]; rw [← (LieAlgebra.ad R A).map_lie]; rw [Ring.lie_def]; rw [sub_eq_zero.mpr h]; rw [map_zero]

中文:
定理 Lie代数.commute_ad_of_commute
  条件: {a b : A} (h : Commute a b)
  证明: by
  rw [Commute]; rw [SemiconjBy]; rw [← sub_eq_zero]; rw [← Ring.lie_def]; rw [← (LieAlgebra.ad R A).map_lie]; rw [Ring.lie_def]; rw [sub_eq_zero.mpr h]; rw [map_zero]

Depends on / 依赖: Commute, LieAlgebra, LieAlgebra.ad, Ring.lie_def, SemiconjBy, lie_def, map_lie, map_zero, sub_eq_zero, sub_eq_zero.mpr
-/
theorem LieAlgebra.commute_ad_of_commute {a b : A} (h : Commute a b) :
    Commute (LieAlgebra.ad R A a) (LieAlgebra.ad R A b) := by
  rw [Commute]; rw [SemiconjBy]; rw [← sub_eq_zero]; rw [← Ring.lie_def]; rw [← (LieAlgebra.ad R A).map_lie]; rw [Ring.lie_def]; rw [sub_eq_zero.mpr h]; rw [map_zero]

/--
theorem `LieAlgebra.ad_nilpotent_of_nilpotent` / 定理 `LieAlgebra.ad_nilpotent_of_nilpotent`

English:
theorem LieAlgebra.ad_nilpotent_of_nilpotent
  given: {a : A} (h : IsNilpotent a)
  proof: by
  rw [LieAlgebra.ad_eq_lmul_left_sub_lmul_right]
  have hl : IsNilpotent (LinearMap.mulLeft R a) := by rwa [LinearMap.isNilpotent_mulLeft_iff]
  have hr : IsNilpotent (LinearMap.mulRight R a) := by rwa [LinearMap.isNilpotent_mulRight_iff]
  exact (LinearMap.commute_mulLeft_right a a).isNilpotent_

中文:
定理 Lie代数.ad_nilpotent_of_nilpotent
  条件: {a : A} (h : 是幂零 a)
  证明: by
  rw [LieAlgebra.ad_eq_lmul_left_sub_lmul_right]
  have hl : IsNilpotent (LinearMap.mulLeft R a) := by rwa [LinearMap.isNilpotent_mulLeft_iff]
  have hr : IsNilpotent (LinearMap.mulRight R a) := by rwa [LinearMap.isNilpotent_mulRight_iff]
  exact (LinearMap.commute_mulLeft_right a a).isNilpotent_

Depends on / 依赖: IsNilpotent, LieAlgebra, LieAlgebra.ad_eq_lmul_left_sub_lmul_right, LinearMap, LinearMap.commute_mulLeft_right, LinearMap.isNilpotent_mulLeft_iff, LinearMap.isNilpotent_mulRight_iff, LinearMap.mulLeft, LinearMap.mulRight, ad_eq_lmul_left_sub_lmul_right, commute_mulLeft_right, isNilpotent_mulLeft_iff, isNilpotent_mulRight_iff, isNilpotent_sub, mulLeft, mulRight
-/
theorem LieAlgebra.ad_nilpotent_of_nilpotent {a : A} (h : IsNilpotent a) :
    IsNilpotent (LieAlgebra.ad R A a) := by
  rw [LieAlgebra.ad_eq_lmul_left_sub_lmul_right]
  have hl : IsNilpotent (LinearMap.mulLeft R a) := by rwa [LinearMap.isNilpotent_mulLeft_iff]
  have hr : IsNilpotent (LinearMap.mulRight R a) := by rwa [LinearMap.isNilpotent_mulRight_iff]
  exact (LinearMap.commute_mulLeft_right a a).isNilpotent_sub hl hr

/--
theorem `LieSubalgebra.isNilpotent_ad_of_isNilpotent_ad` / 定理 `LieSubalgebra.isNilpotent_ad_of_isNilpotent_ad`

English:
theorem LieSubalgebra.isNilpotent_ad_of_isNilpotent_ad
  statement: {L : Type*} [LieRing L] [LieAlgebra R L]
  proof: by
  obtain ⟨n, hn⟩ := h
  use n
  exact Module.End.submodule_pow_eq_zero_of_pow_eq_zero (K.ad_comp_incl_eq x) hn

中文:
定理 Lie子代数.isNilpotent_ad_of_isNilpotent_ad
  结论: {L : 类型} [Lie环 L] [Lie代数 R L]
  证明: by
  obtain ⟨n, hn⟩ := h
  use n
  exact Module.End.submodule_pow_eq_zero_of_pow_eq_zero (K.ad_comp_incl_eq x) hn

Depends on / 依赖: K.ad_comp_incl_eq, Module, Module.End.submodule_pow_eq_zero_of_pow_eq_zero, ad_comp_incl_eq, submodule_pow_eq_zero_of_pow_eq_zero
-/
theorem LieSubalgebra.isNilpotent_ad_of_isNilpotent_ad {L : Type*} [LieRing L] [LieAlgebra R L]
    (K : LieSubalgebra R L) {x : K} (h : IsNilpotent (LieAlgebra.ad R L ↑x)) :
    IsNilpotent (LieAlgebra.ad R K x) := by
  obtain ⟨n, hn⟩ := h
  use n
  exact Module.End.submodule_pow_eq_zero_of_pow_eq_zero (K.ad_comp_incl_eq x) hn

/--
theorem `LieAlgebra.isNilpotent_ad_of_isNilpotent` / 定理 `LieAlgebra.isNilpotent_ad_of_isNilpotent`

English:
theorem LieAlgebra.isNilpotent_ad_of_isNilpotent
  proof: L.isNilpotent_ad_of_isNilpotent_ad LieAlgebra.ad_nilpotent_of_nilpotent h

中文:
定理 Lie代数.isNilpotent_ad_of_isNilpotent
  证明: L.isNilpotent_ad_of_isNilpotent_ad LieAlgebra.ad_nilpotent_of_nilpotent h

Depends on / 依赖: L.isNilpotent_ad_of_isNilpotent_ad, LieAlgebra, LieAlgebra.ad_nilpotent_of_nilpotent, ad_nilpotent_of_nilpotent, isNilpotent_ad_of_isNilpotent_ad
-/
theorem LieAlgebra.isNilpotent_ad_of_isNilpotent
    {L : LieSubalgebra R A} {x : L} (h : IsNilpotent (x : A)) :
    IsNilpotent (LieAlgebra.ad R L x) :=
L.isNilpotent_ad_of_isNilpotent_ad LieAlgebra.ad_nilpotent_of_nilpotent h

end CommRing

section Field

variable {K V : Type*} [Field K] [PerfectField K] [AddCommGroup V] [Module K V]
variable [FiniteDimensional K V]

attribute [local instance 100] LieRing.ofAssociativeRing

/--
theorem `LieAlgebra.ad_isSemisimple_of_isSemisimple` / 定理 `LieAlgebra.ad_isSemisimple_of_isSemisimple`

English:
theorem LieAlgebra.ad_isSemisimple_of_isSemisimple
  given: {a : Module.End K V} (ha : a.IsSemisimple)
  proof: by
  rw [LieAlgebra.ad_eq_lmul_left_sub_lmul_right]
  have hl : Module.End.IsSemisimple (LinearMap.mulLeft K a) := by
    apply Module.End.isSemisimple_of_squarefree_aeval_eq_zero ha.minpoly_squarefree
    have : Polynomial.aeval (Algebra.lmul K (Module.End K V) a) (minpoly K a) = 0 := by
      rw [

中文:
定理 Lie代数.ad_isSemisimple_of_isSemisimple
  条件: {a : 模.End K V} (ha : a.是半单)
  证明: by
  rw [LieAlgebra.ad_eq_lmul_left_sub_lmul_right]
  have hl : Module.End.IsSemisimple (LinearMap.mulLeft K a) := by
    apply Module.End.isSemisimple_of_squarefree_aeval_eq_zero ha.minpoly_squarefree
    have : Polynomial.aeval (Algebra.lmul K (Module.End K V) a) (minpoly K a) = 0 := by
      rw [

Depends on / 依赖: Algebra, Algebra.lmul, IsSemisimple, LieAlgebra, LieAlgebra.ad_eq_lmul_left_sub_lmul_right, LinearMap, LinearMap.mulLeft, LinearMap.mulRight, Module, Module.End, Module.End.IsSemisimple, Module.End.isSemisimple_of_squarefree_aeval_eq_zero, Polynomial, Polynomial.aeval, Polynomial.aeval_algHom_apply, ad_eq_lmul_left_sub_lmul_right, aeval_algHom_apply, ha.minpoly_, ha.minpoly_squarefree, isSemisimple_of_squarefree_aeval_eq_zero
-/
theorem LieAlgebra.ad_isSemisimple_of_isSemisimple {a : Module.End K V} (ha : a.IsSemisimple) :
    (LieAlgebra.ad K (Module.End K V) a).IsSemisimple := by
  rw [LieAlgebra.ad_eq_lmul_left_sub_lmul_right]
  have hl : Module.End.IsSemisimple (LinearMap.mulLeft K a) := by
    apply Module.End.isSemisimple_of_squarefree_aeval_eq_zero ha.minpoly_squarefree
    have : Polynomial.aeval (Algebra.lmul K (Module.End K V) a) (minpoly K a) = 0 := by
      rw [Polynomial.aeval_algHom_apply]; rw [minpoly.aeval]; rw [map_zero]
    simpa using! this
  have hr : Module.End.IsSemisimple (LinearMap.mulRight K a) := by
    apply Module.End.isSemisimple_of_squarefree_aeval_eq_zero ha.minpoly_squarefree
    have hrw : LinearMap.mulRight K a =
        (Algebra.lsmul (A := (Module.End K V)ᵐᵒᵖ) K K (Module.End K V)) (.op a) := by
      ext; simp [Algebra.lsmul]
    rw [hrw]; rw [Polynomial.aeval_algHom_apply]; rw [Polynomial.aeval_op_apply]; rw [minpoly.aeval]; rw [MulOpposite.op_zero]; rw [map_zero]
  exact hl.sub_of_commute (LinearMap.commute_mulLeft_right a a) hr

end Field
