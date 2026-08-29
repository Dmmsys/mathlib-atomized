/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Mathlib.RingTheory.Bialgebra.Quotient
public import Mathlib.RingTheory.HopfAlgebra.Convolution

/-!
# Hopf algebra structure on quotients by Hopf ideals

A *Hopf ideal* of an `R`-Hopf algebra `A` is a biideal stable under the antipode. The quotient
by a Hopf ideal inherits a Hopf algebra structure.

## Main definitions

* `Ideal.IsHopfIdeal R I` : `I` is a coideal (as an `R`-submodule) stable under the antipode.

## Main results

* `HopfAlgebra.ofSurjective` : the Hopf algebra axioms transfer along a surjective bialgebra
  homomorphism intertwining the antipodes.
* `HopfAlgebra R (A ⧸ I)` instance when `[I.IsTwoSided]` and `[I.IsHopfIdeal R]`.
-/

public section

open Bialgebra Bialgebra.Quotient Coalgebra HopfAlgebra Ideal.Quotient LinearMap
  TensorProduct WithConv

namespace HopfAlgebra

section ofSurjective

variable {R A B : Type*} [CommSemiring R] [Semiring A] [Semiring B]
  [HopfAlgebra R A] [HopfAlgebraStruct R B]

/--
lemma `_root_.LinearMap.algHom_comp_convOne` / 引理 `_root_.LinearMap.algHom_comp_convOne`

English:
lemma _root_.LinearMap.algHom_comp_convOne
  given: (g : A ->ₐ[R] B)
  proof: by
  ext a; simp

中文:
引理 _root_.线性映射.algHom_comp_convOne
  条件: (g : A ->ₐ[R] B)
  证明: by
  ext a; simp
-/
lemma _root_.LinearMap.algHom_comp_convOne (g : A ->ₐ[R] B) :
    g.toLinearMap ∘ₗ (1 : WithConv (A ->ₗ[R] A)).ofConv = (1 : WithConv (A ->ₗ[R] B)).ofConv := by
  ext a; simp

/--
lemma `_root_.LinearMap.convOne_comp_coalgHom` / 引理 `_root_.LinearMap.convOne_comp_coalgHom`

English:
lemma _root_.LinearMap.convOne_comp_coalgHom
  given: (g : A ->ₗc[R] B)
  proof: by
  ext a; simp

中文:
引理 _root_.线性映射.convOne_comp_coalgHom
  条件: (g : A ->ₗc[R] B)
  证明: by
  ext a; simp
-/
lemma _root_.LinearMap.convOne_comp_coalgHom (g : A ->ₗc[R] B) :
    (1 : WithConv (B ->ₗ[R] B)).ofConv ∘ₗ g.toLinearMap = (1 : WithConv (A ->ₗ[R] B)).ofConv := by
  ext a; simp

/--
Definition of `ofSurjective` / `ofSurjective` 的定义

English:
abbreviation ofSurjective
  signature: (f : A ->ₐc[R] B) (hf : Function.Surjective f)
  body: by
  refine .ofConvInverse (antipode R) (ofConv_injective ?_) (ofConv_injective ?_) <;>
    rw [← LinearMap.cancel_right (show Function.Surjective f.toLinearMap from hf)]
  · calc (toConv (antipode R) * toConv .id : WithConv (B ->ₗ[R] B)).ofConv ∘ₗ
          f.toCoalgHom.toLinearMap
        = (toCon

中文:
缩写 ofSurjective
  签名: (f : A ->ₐc[R] B) (hf : 函数.满射 f)
  定义体: by
  refine .ofConvInverse (antipode R) (ofConv_injective ?_) (ofConv_injective ?_) <;>
    rw [← LinearMap.cancel_right (show Function.Surjective f.toLinearMap from hf)]
  · calc (toConv (antipode R) * toConv .id : WithConv (B ->ₗ[R] B)).ofConv ∘ₗ
          f.toCoalgHom.toLinearMap
        = (toCon

Depends on / 依赖: AlgHomClass, AlgHomClass.toAlgHom, Function, Function.Surjective, LinearMap, LinearMap.cancel_right, Surjective, WithConv, antipode, cancel_right, convMul_comp_coalgHom_distrib, f.toCoalgHom.toLinearMap, f.toLinearMap, ofConv, ofConvInverse, ofConv_injective, toAlgHom, toCoalgHom, toConv, toLinearMap
-/
noncomputable abbrev ofSurjective (f : A ->ₐc[R] B) (hf : Function.Surjective f)
    (hS : antipode R ∘ₗ f.toLinearMap = f.toLinearMap ∘ₗ antipode R) : HopfAlgebra R B := by
  refine .ofConvInverse (antipode R) (ofConv_injective ?_) (ofConv_injective ?_) <;>
    rw [← LinearMap.cancel_right (show Function.Surjective f.toLinearMap from hf)]
  · calc (toConv (antipode R) * toConv .id : WithConv (B ->ₗ[R] B)).ofConv ∘ₗ
          f.toCoalgHom.toLinearMap
        = (toConv (f.toLinearMap ∘ₗ antipode R) * toConv f.toLinearMap).ofConv := by
          rw [convMul_comp_coalgHom_distrib]; rw [hS]; rfl
      _ = (AlgHomClass.toAlgHom f).toLinearMap ∘ₗ
            (toConv (antipode R) * toConv .id : WithConv (A ->ₗ[R] A)).ofConv := by
          rw [algHom_comp_convMul_distrib]; rfl
      _ = (1 : WithConv (B ->ₗ[R] B)).ofConv ∘ₗ f.toLinearMap := by
          rw [antipode_mul_id]; rw [algHom_comp_convOne]; rw [← convOne_comp_coalgHom f.toCoalgHom]
  · calc (toConv .id * toConv (antipode R) : WithConv (B ->ₗ[R] B)).ofConv ∘ₗ
          f.toCoalgHom.toLinearMap
        = (toConv f.toLinearMap * toConv (f.toLinearMap ∘ₗ antipode R)).ofConv := by
          rw [convMul_comp_coalgHom_distrib]; rw [hS]; rfl
      _ = (AlgHomClass.toAlgHom f).toLinearMap ∘ₗ
            (toConv .id * toConv (antipode R) : WithConv (A ->ₗ[R] A)).ofConv := by
          rw [algHom_comp_convMul_distrib]; rfl
      _ = (1 : WithConv (B ->ₗ[R] B)).ofConv ∘ₗ f.toLinearMap := by
          rw [id_mul_antipode]; rw [algHom_comp_convOne]; rw [← convOne_comp_coalgHom f.toCoalgHom]

end ofSurjective

end HopfAlgebra

variable {R A : Type*} [CommRing R] [Ring A]

section HopfAlgebraStruct

variable [HopfAlgebraStruct R A]

variable (R) in
/-- An ideal whose underlying `R`-submodule is a coideal and which is stable under the
antipode (`S(I) ⊆ I`). Together with `I.IsTwoSided`, this makes `I` a *Hopf ideal*. -/
@[mk_iff]
/--
Definition of `Ideal.IsHopfIdeal` / `Ideal.IsHopfIdeal` 的定义

English:
class Ideal.IsHopfIdeal
  parameters: (I : Ideal A)
  extends: (I.restrictScalars R).IsCoideal
  axioms and operations (1):
    - antipode_mem : forall ⦃x : A⦄, x in I -> antipode R x in I

中文:
类 理想.是Hopf理想
  参数: (I : 理想 A)
  继承: (I.restrictScalars R).是余ideal
  公理与运算 (1 个):
    - antipode_mem : 对任意 ⦃x : A⦄, x in I -> antipode R x in I
-/
class Ideal.IsHopfIdeal (I : Ideal A) : Prop extends (I.restrictScalars R).IsCoideal where
  antipode_mem : forall ⦃x : A⦄, x in I -> antipode R x in I

end HopfAlgebraStruct

namespace HopfAlgebra.Quotient

section HopfAlgebraStruct

variable [HopfAlgebraStruct R A] (I : Ideal A) [I.IsTwoSided] [I.IsHopfIdeal R]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: HopfAlgebraStruct R (A ⧸ I)
  body: Submodule.mapQ (I.restrictScalars R) (I.restrictScalars R)
    (antipode R) (Ideal.IsHopfIdeal.antipode_mem (R := R))

@[simp]

中文:
实例 :
  签名: HopfAlgebraStruct R (A ⧸ I)
  定义体: Submodule.mapQ (I.restrictScalars R) (I.restrictScalars R)
    (antipode R) (Ideal.IsHopfIdeal.antipode_mem (R := R))

@[simp]

Depends on / 依赖: I.restrictScalars, Submodule, Submodule.mapQ, restrictScalars
-/
instance : HopfAlgebraStruct R (A ⧸ I) where
  antipode := Submodule.mapQ (I.restrictScalars R) (I.restrictScalars R)
    (antipode R) (Ideal.IsHopfIdeal.antipode_mem (R := R))

@[simp]
/--
lemma `antipode_mk` / 引理 `antipode_mk`

English:
lemma antipode_mk
  given: (a : A)
  proof: rfl

中文:
引理 antipode_mk
  条件: (a : A)
  证明: rfl
-/
lemma antipode_mk (a : A) :
    antipode R (Ideal.Quotient.mk I a) = Ideal.Quotient.mk I (antipode R a) := rfl

/--
lemma `antipode_comp_mkₐ` / 引理 `antipode_comp_mkₐ`

English:
lemma antipode_comp_mkₐ
  proof: by ext; simp

中文:
引理 antipode_comp_mkₐ
  证明: by ext; simp
-/
lemma antipode_comp_mkₐ :
    antipode R ∘ₗ (Ideal.Quotient.mkₐ R I).toLinearMap =
      (Ideal.Quotient.mkₐ R I).toLinearMap ∘ₗ antipode R := by ext; simp

end HopfAlgebraStruct

variable [HopfAlgebra R A] (I : Ideal A) [I.IsTwoSided] [I.IsHopfIdeal R]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: HopfAlgebra R (A ⧸ I)
  body: .ofSurjective (mkBialgHom I) mk_surjective (antipode_comp_mkₐ I)

中文:
实例 :
  签名: Hopf代数 R (A ⧸ I)
  定义体: .ofSurjective (mkBialgHom I) mk_surjective (antipode_comp_mkₐ I)

Depends on / 依赖: mkBialgHom, mk_surjective, ofSurjective
-/
noncomputable instance : HopfAlgebra R (A ⧸ I) :=
  .ofSurjective (mkBialgHom I) mk_surjective (antipode_comp_mkₐ I)

end HopfAlgebra.Quotient
