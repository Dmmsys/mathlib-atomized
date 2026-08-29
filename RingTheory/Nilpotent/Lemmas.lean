/-
Copyright (c) 2021 Oliver Nash. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Nash
-/
module

public import Mathlib.LinearAlgebra.Matrix.ToLin
public import Mathlib.LinearAlgebra.Quotient.Basic
public import Mathlib.RingTheory.Ideal.Maps
public import Mathlib.RingTheory.Nilpotent.Defs

/-!
# Nilpotent elements

This file contains results about nilpotent elements that involve ring theory.
-/

@[expose] public section

assert_not_exists Cardinal

universe u v

open Function Module Set

variable {R S : Type*} {x y : R}

/--
theorem `RingHom.ker_isRadical_iff_reduced_of_surjective` / 定理 `RingHom.ker_isRadical_iff_reduced_of_surjective`

English:
theorem RingHom.ker_isRadical_iff_reduced_of_surjective
  statement: {S F} [CommSemiring R] [Semiring S]
  proof: by
  simp_rw [isReduced_iff, hf.forall, IsNilpotent, ← map_pow, ← RingHom.mem_ker]
  rfl

中文:
定理 RingHom.ker_isRadical_iff_reduced_of_surjective
  结论: {S F} [CommSemiring R] [Semiring S]
  证明: by
  simp_rw [isReduced_iff, hf.forall, IsNilpotent, ← map_pow, ← RingHom.mem_ker]
  rfl

Depends on / 依赖: IsNilpotent, RingHom, RingHom.mem_ker, hf.forall, isReduced_iff, map_pow, mem_ker, simp_rw
-/
theorem RingHom.ker_isRadical_iff_reduced_of_surjective {S F} [CommSemiring R] [Semiring S]
    [FunLike F R S] [RingHomClass F R S] {f : F} (hf : Function.Surjective f) :
    (RingHom.ker f).IsRadical ↔ IsReduced S := by
  simp_rw [isReduced_iff, hf.forall, IsNilpotent, ← map_pow, ← RingHom.mem_ker]
  rfl

/--
theorem `isRadical_iff_span_singleton` / 定理 `isRadical_iff_span_singleton`

English:
theorem isRadical_iff_span_singleton
  given: [CommSemiring R]
  proof: by
  simp_rw [IsRadical, ← Ideal.mem_span_singleton]
  exact forall_comm.trans (forall_congr' fun r => exists_imp.symm)

中文:
定理 isRadical_iff_span_singleton
  条件: [CommSemiring R]
  证明: by
  simp_rw [IsRadical, ← Ideal.mem_span_singleton]
  exact forall_comm.trans (forall_congr' fun r => exists_imp.symm)

Depends on / 依赖: Ideal.mem_span_singleton, IsRadical, exists_imp, exists_imp.symm, forall_comm, forall_comm.trans, forall_congr, mem_span_singleton, simp_rw
-/
theorem isRadical_iff_span_singleton [CommSemiring R] :
    IsRadical y ↔ (Ideal.span ({y} : Set R)).IsRadical := by
  simp_rw [IsRadical, ← Ideal.mem_span_singleton]
  exact forall_comm.trans (forall_congr' fun r => exists_imp.symm)

/--
theorem `isNilpotent_iff_zero_mem_powers` / 定理 `isNilpotent_iff_zero_mem_powers`

English:
theorem isNilpotent_iff_zero_mem_powers
  given: [Monoid R] [Zero R] {x : R}
  proof: Iff.rfl

中文:
定理 isNilpotent_iff_zero_mem_powers
  条件: [Monoid R] [Zero R] {x : R}
  证明: Iff.rfl

Depends on / 依赖: Iff.rfl
-/
theorem isNilpotent_iff_zero_mem_powers [Monoid R] [Zero R] {x : R} :
    IsNilpotent x ↔ 0 in Submonoid.powers x := Iff.rfl

section CommSemiring

variable [CommSemiring R] {x y : R}

/--
Definition of `nilradical` / `nilradical` 的定义

English:
definition nilradical
  signature: (R : Type*) [CommSemiring R]
  body: (0 : Ideal R).radical

中文:
定义 nilradical
  签名: (R : 类型) [CommSemiring R]
  定义体: (0 : Ideal R).radical

Depends on / 依赖: radical
-/
def nilradical (R : Type*) [CommSemiring R] : Ideal R :=
  (0 : Ideal R).radical

/--
theorem `mem_nilradical` / 定理 `mem_nilradical`

English:
theorem mem_nilradical
  statement: x in nilradical R ↔ IsNilpotent x
  proof: Iff.rfl

中文:
定理 mem_nilradical
  结论: x in nilradical R ↔ IsNilpotent x
  证明: Iff.rfl

Depends on / 依赖: Iff.rfl
-/
theorem mem_nilradical : x in nilradical R ↔ IsNilpotent x :=
  Iff.rfl

/--
theorem `nilradical_eq_sInf` / 定理 `nilradical_eq_sInf`

English:
theorem nilradical_eq_sInf
  given: (R : Type*) [CommSemiring R]
  proof: (Ideal.radical_eq_sInf ⊥).trans by simp_rw [and_iff_right bot_le]

中文:
定理 nilradical_eq_sInf
  条件: (R : 类型) [CommSemiring R]
  证明: (Ideal.radical_eq_sInf ⊥).trans by simp_rw [and_iff_right bot_le]

Depends on / 依赖: Ideal.radical_eq_sInf, and_iff_right, bot_le, radical_eq_sInf, simp_rw
-/
theorem nilradical_eq_sInf (R : Type*) [CommSemiring R] :
    nilradical R = sInf { J : Ideal R | J.IsPrime } :=
(Ideal.radical_eq_sInf ⊥).trans by simp_rw [and_iff_right bot_le]

/--
theorem `nilpotent_iff_mem_prime` / 定理 `nilpotent_iff_mem_prime`

English:
theorem nilpotent_iff_mem_prime
  statement: IsNilpotent x ↔ forall J : Ideal R, J.IsPrime -> x in J
  proof: by
  rw [← mem_nilradical]; rw [nilradical_eq_sInf]; rw [Submodule.mem_sInf]
  rfl

中文:
定理 nilpotent_iff_mem_prime
  结论: IsNilpotent x ↔ 对任意 J : Ideal R, J.IsPrime -> x in J
  证明: by
  rw [← mem_nilradical]; rw [nilradical_eq_sInf]; rw [Submodule.mem_sInf]
  rfl

Depends on / 依赖: Submodule, Submodule.mem_sInf, mem_nilradical, mem_sInf, nilradical_eq_sInf
-/
theorem nilpotent_iff_mem_prime : IsNilpotent x ↔ forall J : Ideal R, J.IsPrime -> x in J := by
  rw [← mem_nilradical]; rw [nilradical_eq_sInf]; rw [Submodule.mem_sInf]
  rfl

/--
theorem `nilradical_le_prime` / 定理 `nilradical_le_prime`

English:
theorem nilradical_le_prime
  given: (J : Ideal R) [H : J.IsPrime]
  statement: nilradical R <= J
  proof: (nilradical_eq_sInf R).symm ▸ sInf_le H

@[simp]

中文:
定理 nilradical_le_prime
  条件: (J : Ideal R) [H : J.IsPrime]
  结论: nilradical R <= J
  证明: (nilradical_eq_sInf R).symm ▸ sInf_le H

@[simp]

Depends on / 依赖: nilradical_eq_sInf, sInf_le
-/
theorem nilradical_le_prime (J : Ideal R) [H : J.IsPrime] : nilradical R <= J :=
  (nilradical_eq_sInf R).symm ▸ sInf_le H

@[simp]
/--
theorem `nilradical_eq_zero` / 定理 `nilradical_eq_zero`

English:
theorem nilradical_eq_zero
  given: (R : Type*) [CommSemiring R] [IsReduced R]
  statement: nilradical R = 0
  proof: Ideal.ext fun _ => isNilpotent_iff_eq_zero

中文:
定理 nilradical_eq_zero
  条件: (R : 类型) [CommSemiring R] [IsReduced R]
  结论: nilradical R = 0
  证明: Ideal.ext fun _ => isNilpotent_iff_eq_zero

Depends on / 依赖: Ideal.ext, isNilpotent_iff_eq_zero
-/
theorem nilradical_eq_zero (R : Type*) [CommSemiring R] [IsReduced R] : nilradical R = 0 :=
  Ideal.ext fun _ => isNilpotent_iff_eq_zero

/--
theorem `nilradical_eq_bot_iff` / 定理 `nilradical_eq_bot_iff`

English:
theorem nilradical_eq_bot_iff
  given: {R : Type*} [CommSemiring R]
  statement: nilradical R = ⊥ ↔ IsReduced R
  proof: by
  simp_rw [eq_bot_iff, SetLike.le_def, Submodule.mem_bot, mem_nilradical, isReduced_iff]

中文:
定理 nilradical_eq_bot_iff
  条件: {R : 类型} [CommSemiring R]
  结论: nilradical R = ⊥ ↔ IsReduced R
  证明: by
  simp_rw [eq_bot_iff, SetLike.le_def, Submodule.mem_bot, mem_nilradical, isReduced_iff]

Depends on / 依赖: SetLike, SetLike.le_def, Submodule, Submodule.mem_bot, eq_bot_iff, isReduced_iff, le_def, mem_bot, mem_nilradical, simp_rw
-/
theorem nilradical_eq_bot_iff {R : Type*} [CommSemiring R] : nilradical R = ⊥ ↔ IsReduced R := by
  simp_rw [eq_bot_iff, SetLike.le_def, Submodule.mem_bot, mem_nilradical, isReduced_iff]

end CommSemiring

namespace LinearMap

variable (R) {A : Type v} [CommSemiring R] [Semiring A] [Algebra R A]

@[simp]
/--
theorem `isNilpotent_mulLeft_iff` / 定理 `isNilpotent_mulLeft_iff`

English:
theorem isNilpotent_mulLeft_iff
  given: (a : A)
  statement: IsNilpotent (mulLeft R a) ↔ IsNilpotent a
  proof: by
  constructor <;> rintro ⟨n, hn⟩ <;> use n <;>
      simp only [mulLeft_eq_zero_iff, pow_mulLeft] at hn ⊢ <;>
    exact hn

@[simp]

中文:
定理 isNilpotent_mulLeft_iff
  条件: (a : A)
  结论: IsNilpotent (mulLeft R a) ↔ IsNilpotent a
  证明: by
  constructor <;> rintro ⟨n, hn⟩ <;> use n <;>
      simp only [mulLeft_eq_zero_iff, pow_mulLeft] at hn ⊢ <;>
    exact hn

@[simp]

Depends on / 依赖: mulLeft_eq_zero_iff, pow_mulLeft
-/
theorem isNilpotent_mulLeft_iff (a : A) : IsNilpotent (mulLeft R a) ↔ IsNilpotent a := by
  constructor <;> rintro ⟨n, hn⟩ <;> use n <;>
      simp only [mulLeft_eq_zero_iff, pow_mulLeft] at hn ⊢ <;>
    exact hn

@[simp]
/--
theorem `isNilpotent_mulRight_iff` / 定理 `isNilpotent_mulRight_iff`

English:
theorem isNilpotent_mulRight_iff
  given: (a : A)
  statement: IsNilpotent (mulRight R a) ↔ IsNilpotent a
  proof: by
  constructor <;> rintro ⟨n, hn⟩ <;> use n <;>
      simp only [mulRight_eq_zero_iff, pow_mulRight] at hn ⊢ <;>
    exact hn

中文:
定理 isNilpotent_mulRight_iff
  条件: (a : A)
  结论: IsNilpotent (mulRight R a) ↔ IsNilpotent a
  证明: by
  constructor <;> rintro ⟨n, hn⟩ <;> use n <;>
      simp only [mulRight_eq_zero_iff, pow_mulRight] at hn ⊢ <;>
    exact hn

Depends on / 依赖: mulRight_eq_zero_iff, pow_mulRight
-/
theorem isNilpotent_mulRight_iff (a : A) : IsNilpotent (mulRight R a) ↔ IsNilpotent a := by
  constructor <;> rintro ⟨n, hn⟩ <;> use n <;>
      simp only [mulRight_eq_zero_iff, pow_mulRight] at hn ⊢ <;>
    exact hn

variable {R}
variable {ι M : Type*} [Fintype ι] [DecidableEq ι] [AddCommMonoid M] [Module R M]

@[simp]
/--
lemma `isNilpotent_toMatrix_iff` / 引理 `isNilpotent_toMatrix_iff`

English:
lemma isNilpotent_toMatrix_iff
  given: (b : Basis ι R M) (f : M ->ₗ[R] M)
  proof: by
  refine exists_congr fun k => ?_
  rw [toMatrix_pow]
  exact (toMatrix b b).map_eq_zero_iff

中文:
引理 isNilpotent_toMatrix_iff
  条件: (b : Basis ι R M) (f : M ->ₗ[R] M)
  证明: by
  refine exists_congr fun k => ?_
  rw [toMatrix_pow]
  exact (toMatrix b b).map_eq_zero_iff

Depends on / 依赖: exists_congr, map_eq_zero_iff, toMatrix, toMatrix_pow
-/
lemma isNilpotent_toMatrix_iff (b : Basis ι R M) (f : M ->ₗ[R] M) :
    IsNilpotent (toMatrix b b f) ↔ IsNilpotent f := by
  refine exists_congr fun k => ?_
  rw [toMatrix_pow]
  exact (toMatrix b b).map_eq_zero_iff

end LinearMap

@[simp]
/--
lemma `Matrix.isNilpotent_toLin'_iff` / 引理 `Matrix.isNilpotent_toLin'_iff`

English:
lemma Matrix.isNilpotent_toLin'_iff
  statement: {ι : Type*} [DecidableEq ι] [Fintype ι] [CommSemiring R]
  proof: by
  have : A.toLin'.toMatrix (Pi.basisFun R ι) (Pi.basisFun R ι) = A := LinearMap.toMatrix'_toLin' A
  conv_rhs => rw [← this]
  rw [LinearMap.isNilpotent_toMatrix_iff]

中文:
引理 Matrix.isNilpotent_toLin'_iff
  结论: {ι : 类型} [DecidableEq ι] [Fintype ι] [CommSemiring R]
  证明: by
  have : A.toLin'.toMatrix (Pi.basisFun R ι) (Pi.basisFun R ι) = A := LinearMap.toMatrix'_toLin' A
  conv_rhs => rw [← this]
  rw [LinearMap.isNilpotent_toMatrix_iff]

Depends on / 依赖: A.toLin, LinearMap, LinearMap.isNilpotent_toMatrix_iff, LinearMap.toMatrix, Pi.basisFun, _toLin, basisFun, conv_rhs, isNilpotent_toMatrix_iff, toMatrix
-/
lemma Matrix.isNilpotent_toLin'_iff {ι : Type*} [DecidableEq ι] [Fintype ι] [CommSemiring R]
    (A : Matrix ι ι R) :
    IsNilpotent A.toLin' ↔ IsNilpotent A := by
  have : A.toLin'.toMatrix (Pi.basisFun R ι) (Pi.basisFun R ι) = A := LinearMap.toMatrix'_toLin' A
  conv_rhs => rw [← this]
  rw [LinearMap.isNilpotent_toMatrix_iff]

namespace Module.End

section

variable {M : Type*} [Semiring R] [AddCommMonoid M] [Module R M]

set_option backward.isDefEq.respectTransparency false in
/--
lemma `isNilpotent_restrict_of_le` / 引理 `isNilpotent_restrict_of_le`

English:
lemma isNilpotent_restrict_of_le
  statement: {f : End R M} {p q : Submodule R M}
  proof: by
  obtain ⟨n, hn⟩ := hf
  use n
  ext ⟨x, hx⟩
  replace hn := DFunLike.congr_fun hn ⟨x, h hx⟩
  simp_rw [LinearMap.zero_apply, ZeroMemClass.coe_zero, ZeroMemClass.coe_eq_zero] at hn ⊢
  rw [Module.End.pow_restrict]; rw [LinearMap.restrict_apply] at hn ⊢
  ext
  exact (congr_arg Subtype.val hn :)

中文:
引理 isNilpotent_restrict_of_le
  结论: {f : End R M} {p q : Submodule R M}
  证明: by
  obtain ⟨n, hn⟩ := hf
  use n
  ext ⟨x, hx⟩
  replace hn := DFunLike.congr_fun hn ⟨x, h hx⟩
  simp_rw [LinearMap.zero_apply, ZeroMemClass.coe_zero, ZeroMemClass.coe_eq_zero] at hn ⊢
  rw [Module.End.pow_restrict]; rw [LinearMap.restrict_apply] at hn ⊢
  ext
  exact (congr_arg Subtype.val hn :)

Depends on / 依赖: DFunLike, DFunLike.congr_fun, LinearMap, LinearMap.restrict_apply, LinearMap.zero_apply, Module, Module.End.pow_restrict, Subtype, Subtype.val, ZeroMemClass, ZeroMemClass.coe_eq_zero, ZeroMemClass.coe_zero, coe_eq_zero, coe_zero, congr_arg, congr_fun, pow_restrict, replace, restrict_apply, simp_rw
-/
lemma isNilpotent_restrict_of_le {f : End R M} {p q : Submodule R M}
    {hp : MapsTo f p p} {hq : MapsTo f q q} (h : p <= q) (hf : IsNilpotent (f.restrict hq)) :
    IsNilpotent (f.restrict hp) := by
  obtain ⟨n, hn⟩ := hf
  use n
  ext ⟨x, hx⟩
  replace hn := DFunLike.congr_fun hn ⟨x, h hx⟩
  simp_rw [LinearMap.zero_apply, ZeroMemClass.coe_zero, ZeroMemClass.coe_eq_zero] at hn ⊢
  rw [Module.End.pow_restrict]; rw [LinearMap.restrict_apply] at hn ⊢
  ext
  exact (congr_arg Subtype.val hn :)

set_option backward.isDefEq.respectTransparency false in
/--
lemma `isNilpotent.restrict` / 引理 `isNilpotent.restrict`

English:
lemma isNilpotent.restrict
  proof: by
  obtain ⟨n, hn⟩ := hnil
  exact ⟨n, LinearMap.ext fun m => by simp only [Module.End.pow_restrict n, hn,
    LinearMap.restrict_apply, LinearMap.zero_apply]; rfl⟩

中文:
引理 isNilpotent.restrict
  证明: by
  obtain ⟨n, hn⟩ := hnil
  exact ⟨n, LinearMap.ext fun m => by simp only [Module.End.pow_restrict n, hn,
    LinearMap.restrict_apply, LinearMap.zero_apply]; rfl⟩

Depends on / 依赖: LinearMap, LinearMap.ext, LinearMap.restrict_apply, LinearMap.zero_apply, Module, Module.End.pow_restrict, pow_restrict, restrict_apply, zero_apply
-/
lemma isNilpotent.restrict
    {f : M ->ₗ[R] M} {p : Submodule R M} (hf : MapsTo f p p) (hnil : IsNilpotent f) :
    IsNilpotent (f.restrict hf) := by
  obtain ⟨n, hn⟩ := hnil
  exact ⟨n, LinearMap.ext fun m => by simp only [Module.End.pow_restrict n, hn,
    LinearMap.restrict_apply, LinearMap.zero_apply]; rfl⟩

end

variable {M : Type v} [Ring R] [AddCommGroup M] [Module R M]
variable {f : Module.End R M} {p : Submodule R M} (hp : p <= p.comap f)

/--
theorem `IsNilpotent.mapQ` / 定理 `IsNilpotent.mapQ`

English:
theorem IsNilpotent.mapQ
  given: (hnp : IsNilpotent f)
  statement: IsNilpotent (p.mapQ p f hp)
  proof: by
  obtain ⟨k, hk⟩ := hnp
  use k
  simp [← p.mapQ_pow, hk]

中文:
定理 IsNilpotent.mapQ
  条件: (hnp : IsNilpotent f)
  结论: IsNilpotent (p.mapQ p f hp)
  证明: by
  obtain ⟨k, hk⟩ := hnp
  use k
  simp [← p.mapQ_pow, hk]

Depends on / 依赖: mapQ_pow, p.mapQ_pow
-/
theorem IsNilpotent.mapQ (hnp : IsNilpotent f) : IsNilpotent (p.mapQ p f hp) := by
  obtain ⟨k, hk⟩ := hnp
  use k
  simp [← p.mapQ_pow, hk]

end Module.End
