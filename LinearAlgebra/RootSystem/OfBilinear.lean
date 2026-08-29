/-
Copyright (c) 2024 Scott Carnahan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Carnahan
-/
module

public import Mathlib.LinearAlgebra.RootSystem.Defs

/-!
# Root pairings made from bilinear forms

A common construction of root systems is given by taking the set of all vectors in an integral
lattice for which reflection yields an automorphism of the lattice. In this file, we generalize
this construction, replacing the ring of integers with an arbitrary commutative ring and the
integral lattice with an arbitrary reflexive module equipped with a bilinear form.

## Main definitions:
* `LinearMap.IsReflective`: Length is a regular value of `R`, and reflection is definable.
* `LinearMap.IsReflective.coroot`: The coroot corresponding to a reflective vector.
* `RootPairing.of_Bilinear`: The root pairing whose roots are reflective vectors.

## TODO
* properties
-/

@[expose] public section

open Set Function Module

noncomputable section

variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]

namespace LinearMap

/--
Definition of `IsReflective` / `IsReflective` 的定义

English:
structure IsReflective
  parameters: (B : M ->ₗ[R] M ->ₗ[R] R) (x : M)
  axioms and operations (2):
    - regular : IsRegular (B x x)
    - dvd_two_mul : forall y, B x x ∣ 2 * B x y

中文:
结构 是反射
  参数: (B : M ->ₗ[R] M ->ₗ[R] R) (x : M)
  公理与运算 (2 个):
    - regular : 是正则 (B x x)
    - dvd_two_mul : 对任意 y, B x x ∣ 2 * B x y
-/
structure IsReflective (B : M ->ₗ[R] M ->ₗ[R] R) (x : M) : Prop where
  regular : IsRegular (B x x)
  dvd_two_mul : forall y, B x x ∣ 2 * B x y

variable (B : M ->ₗ[R] M ->ₗ[R] R) {x : M}

namespace IsReflective

/--
lemma `of_dvd_two` / 引理 `of_dvd_two`

English:
lemma of_dvd_two
  given: [IsCancelMulZero R] [NeZero (2 : R)] (hx : B x x ∣ 2)
  proof: .of_ne_zero fun contra => by simp [contra, two_ne_zero (α := R)] at hx
  dvd_two_mul y := hx.mul_right (B x y)

中文:
引理 of_dvd_two
  条件: [是乘零消去 R] [NeZero (2 : R)] (hx : B x x ∣ 2)
  证明: .of_ne_zero fun contra => by simp [contra, two_ne_zero (α := R)] at hx
  dvd_two_mul y := hx.mul_right (B x y)

Depends on / 依赖: contra, of_ne_zero, two_ne_zero
-/
lemma of_dvd_two [IsCancelMulZero R] [NeZero (2 : R)] (hx : B x x ∣ 2) :
    IsReflective B x where
regular := .of_ne_zero fun contra => by simp [contra, two_ne_zero (α := R)] at hx
  dvd_two_mul y := hx.mul_right (B x y)

variable (hx : IsReflective B x)

/--
Definition of `coroot` / `coroot` 的定义

English:
definition coroot
  signature: : M ->ₗ[R] R where
  body: (hx.2 y).choose
  map_add' a b := by
    refine hx.1.1 ?_
    simp only
    rw [← (hx.2 (a + b)).choose_spec]; rw [mul_add]; rw [← (hx.2 a).choose_spec]; rw [← (hx.2 b).choose_spec]; rw [map_add]; rw [mul_add]
  map_smul' r a := by
    refine hx.1.1 ?_
    simp only [RingHom.id_apply]
    rw [← (hx.

中文:
定义 coroot
  签名: : M ->ₗ[R] R where
  定义体: (hx.2 y).choose
  map_add' a b := by
    refine hx.1.1 ?_
    simp only
    rw [← (hx.2 (a + b)).choose_spec]; rw [mul_add]; rw [← (hx.2 a).choose_spec]; rw [← (hx.2 b).choose_spec]; rw [map_add]; rw [mul_add]
  map_smul' r a := by
    refine hx.1.1 ?_
    simp only [RingHom.id_apply]
    rw [← (hx.
-/
def coroot : M ->ₗ[R] R where
  toFun y := (hx.2 y).choose
  map_add' a b := by
    refine hx.1.1 ?_
    simp only
    rw [← (hx.2 (a + b)).choose_spec]; rw [mul_add]; rw [← (hx.2 a).choose_spec]; rw [← (hx.2 b).choose_spec]; rw [map_add]; rw [mul_add]
  map_smul' r a := by
    refine hx.1.1 ?_
    simp only [RingHom.id_apply]
    rw [← (hx.2 (r • a)).choose_spec]; rw [smul_eq_mul]; rw [mul_left_comm]; rw [← (hx.2 a).choose_spec]; rw [map_smul]; rw [two_mul]; rw [smul_eq_mul]; rw [two_mul]; rw [mul_add]

@[simp]
/--
lemma `apply_self_mul_coroot_apply` / 引理 `apply_self_mul_coroot_apply`

English:
lemma apply_self_mul_coroot_apply
  given: {y : M}
  statement: B x x * coroot B hx y = 2 * B x y
  proof: (hx.dvd_two_mul y).choose_spec.symm

@[simp]

中文:
引理 apply_self_mul_coroot_apply
  条件: {y : M}
  结论: B x x * coroot B hx y = 2 * B x y
  证明: (hx.dvd_two_mul y).choose_spec.symm

@[simp]

Depends on / 依赖: choose_spec, choose_spec.symm, dvd_two_mul, hx.dvd_two_mul
-/
lemma apply_self_mul_coroot_apply {y : M} : B x x * coroot B hx y = 2 * B x y :=
  (hx.dvd_two_mul y).choose_spec.symm

@[simp]
/--
lemma `smul_coroot` / 引理 `smul_coroot`

English:
lemma smul_coroot
  statement: B x x • coroot B hx = 2 • B x
  proof: by
  ext y
  simp [smul_apply, smul_eq_mul, nsmul_eq_mul, Nat.cast_ofNat, apply_self_mul_coroot_apply]

@[simp]

中文:
引理 smul_coroot
  结论: B x x • coroot B hx = 2 • B x
  证明: by
  ext y
  simp [smul_apply, smul_eq_mul, nsmul_eq_mul, Nat.cast_ofNat, apply_self_mul_coroot_apply]

@[simp]

Depends on / 依赖: Nat.cast_ofNat, apply_self_mul_coroot_apply, cast_ofNat, nsmul_eq_mul, smul_apply, smul_eq_mul
-/
lemma smul_coroot : B x x • coroot B hx = 2 • B x := by
  ext y
  simp [smul_apply, smul_eq_mul, nsmul_eq_mul, Nat.cast_ofNat, apply_self_mul_coroot_apply]

@[simp]
/--
lemma `coroot_apply_self` / 引理 `coroot_apply_self`

English:
lemma coroot_apply_self
  statement: coroot B hx x = 2
  proof: hx.regular.left by simp [mul_comm _ (B x x)]

中文:
引理 coroot_apply_self
  结论: coroot B hx x = 2
  证明: hx.regular.left by simp [mul_comm _ (B x x)]

Depends on / 依赖: hx.regular.left, mul_comm, regular
-/
lemma coroot_apply_self : coroot B hx x = 2 :=
hx.regular.left by simp [mul_comm _ (B x x)]

set_option backward.isDefEq.respectTransparency false in
/--
lemma `isOrthogonal_reflection` / 引理 `isOrthogonal_reflection`

English:
lemma isOrthogonal_reflection
  given: (hSB : LinearMap.IsSymm B)
  proof: by
  intro y z
  simp only [reflection_apply, map_sub, map_smul, sub_apply,
    smul_apply, smul_eq_mul]
  refine hx.1.1 ?_
  simp only [mul_sub, ← mul_assoc, apply_self_mul_coroot_apply]
  rw [sub_eq_iff_eq_add]; rw [← hSB.eq x y]; rw [RingHom.id_apply]; rw [mul_assoc _ _ (B x x)]; rw [mul_comm _ (

中文:
引理 isOrthogonal_reflection
  条件: (hSB : 线性映射.是Symm B)
  证明: by
  intro y z
  simp only [reflection_apply, map_sub, map_smul, sub_apply,
    smul_apply, smul_eq_mul]
  refine hx.1.1 ?_
  simp only [mul_sub, ← mul_assoc, apply_self_mul_coroot_apply]
  rw [sub_eq_iff_eq_add]; rw [← hSB.eq x y]; rw [RingHom.id_apply]; rw [mul_assoc _ _ (B x x)]; rw [mul_comm _ (

Depends on / 依赖: RingHom, RingHom.id_apply, apply_self_mul_coroot_apply, hSB.eq, id_apply, map_smul, map_sub, mul_assoc, mul_comm, mul_sub, reflection_apply, smul_apply, smul_eq_mul, sub_apply, sub_eq_iff_eq_add
-/
lemma isOrthogonal_reflection (hSB : LinearMap.IsSymm B) :
    B.IsOrthogonal (Module.reflection (coroot_apply_self B hx)) := by
  intro y z
  simp only [reflection_apply, map_sub, map_smul, sub_apply,
    smul_apply, smul_eq_mul]
  refine hx.1.1 ?_
  simp only [mul_sub, ← mul_assoc, apply_self_mul_coroot_apply]
  rw [sub_eq_iff_eq_add]; rw [← hSB.eq x y]; rw [RingHom.id_apply]; rw [mul_assoc _ _ (B x x)]; rw [mul_comm _ (B x x)]; rw [apply_self_mul_coroot_apply]
  ring

/--
lemma `reflective_reflection` / 引理 `reflective_reflection`

English:
lemma reflective_reflection
  statement: (hSB : LinearMap.IsSymm B) {y : M}
  proof: by
  constructor
  · rw [isOrthogonal_reflection B hx hSB]
    exact hy.1
  · intro z
    have hz : Module.reflection (coroot_apply_self B hx)
        (Module.reflection (coroot_apply_self B hx) z) = z := by
      exact (LinearEquiv.eq_symm_apply (Module.reflection (coroot_apply_self B hx))).mp rfl


中文:
引理 reflective_reflection
  结论: (hSB : 线性映射.是Symm B) {y : M}
  证明: by
  constructor
  · rw [isOrthogonal_reflection B hx hSB]
    exact hy.1
  · intro z
    have hz : Module.reflection (coroot_apply_self B hx)
        (Module.reflection (coroot_apply_self B hx) z) = z := by
      exact (LinearEquiv.eq_symm_apply (Module.reflection (coroot_apply_self B hx))).mp rfl


Depends on / 依赖: LinearEquiv, LinearEquiv.eq_symm_apply, Module, Module.reflection, coroot_apply_self, eq_symm_apply, isOrthogonal_reflection, reflection
-/
lemma reflective_reflection (hSB : LinearMap.IsSymm B) {y : M}
    (hx : IsReflective B x) (hy : IsReflective B y) :
    IsReflective B (Module.reflection (coroot_apply_self B hx) y) := by
  constructor
  · rw [isOrthogonal_reflection B hx hSB]
    exact hy.1
  · intro z
    have hz : Module.reflection (coroot_apply_self B hx)
        (Module.reflection (coroot_apply_self B hx) z) = z := by
      exact (LinearEquiv.eq_symm_apply (Module.reflection (coroot_apply_self B hx))).mp rfl
    rw [← hz]; rw [isOrthogonal_reflection B hx hSB]; rw [isOrthogonal_reflection B hx hSB]
    exact hy.2 _

end IsReflective

end LinearMap

namespace RootPairing

open LinearMap IsReflective

set_option backward.isDefEq.respectTransparency false in
/--
Definition of `ofBilinear` / `ofBilinear` 的定义

English:
definition ofBilinear
  signature: [IsReflexive R M] (B : M ->ₗ[R] M ->ₗ[R] R) (hNB : LinearMap.Nondegenerate B)
  body: Dual.eval R M
  root := Embedding.subtype fun x => IsReflective B x
  coroot :=
    { toFun := fun x => IsReflective.coroot B x.2
      inj' := by
        intro x y hxy
        simp only [mem_ofPred_eq] at hxy -- x* = y*
        have h1 : forall z, IsReflective.coroot B x.2 z = IsReflective.coroot B

中文:
定义 ofBilinear
  签名: [是自反 R M] (B : M ->ₗ[R] M ->ₗ[R] R) (hNB : 线性映射.非退化 B)
  定义体: Dual.eval R M
  root := Embedding.subtype fun x => IsReflective B x
  coroot :=
    { toFun := fun x => IsReflective.coroot B x.2
      inj' := by
        intro x y hxy
        simp only [mem_ofPred_eq] at hxy -- x* = y*
        have h1 : forall z, IsReflective.coroot B x.2 z = IsReflective.coroot B

Depends on / 依赖: Dual.eval
-/
def ofBilinear [IsReflexive R M] (B : M ->ₗ[R] M ->ₗ[R] R) (hNB : LinearMap.Nondegenerate B)
    (hSB : LinearMap.IsSymm B) (h2 : IsRegular (2 : R)) :
    RootPairing {x : M | IsReflective B x} R M (Dual R M) where
  toLinearMap := Dual.eval R M
  root := Embedding.subtype fun x => IsReflective B x
  coroot :=
    { toFun := fun x => IsReflective.coroot B x.2
      inj' := by
        intro x y hxy
        simp only [mem_ofPred_eq] at hxy -- x* = y*
        have h1 : forall z, IsReflective.coroot B x.2 z = IsReflective.coroot B y.2 z :=
          fun z => congrFun (congrArg DFunLike.coe hxy) z
        have h2x : forall z, B x x * IsReflective.coroot B x.2 z =
            B x x * IsReflective.coroot B y.2 z :=
          fun z => congrArg (HMul.hMul ((B x) x)) (h1 z)
        have h2y : forall z, B y y * IsReflective.coroot B x.2 z =
            B y y * IsReflective.coroot B y.2 z :=
          fun z => congrArg (HMul.hMul ((B y) y)) (h1 z)
        simp_rw [apply_self_mul_coroot_apply B x.2] at h2x -- 2(x,z) = (x,x)y*(z)
        simp_rw [apply_self_mul_coroot_apply B y.2] at h2y -- (y,y)x*(z) = 2(y,z)
        have h2xy : B x x = B y y := by
          refine h2.1 ?_
          dsimp only
          specialize h2x y
          rw [coroot_apply_self] at h2x
          specialize h2y x
          rw [coroot_apply_self] at h2y
          rw [mul_comm]; rw [← h2x]; rw [← hSB.eq]; rw [RingHom.id_apply]; rw [← h2y]; rw [mul_comm]
        rw [Subtype.ext_iff]; rw [← sub_eq_zero]
        refine hNB.1 _ (fun z => ?_)
        rw [map_sub]; rw [LinearMap.sub_apply]; rw [sub_eq_zero]
        refine h2.1 ?_
        dsimp only
        rw [h2x z]; rw [← h2y z]; rw [hxy]; rw [h2xy] }
  root_coroot_two x := coroot_apply_self B x.2
  reflectionPerm x :=
    { toFun := fun y => ⟨(Module.reflection (coroot_apply_self B x.2) y),
        reflective_reflection B hSB x.2 y.2⟩
      invFun := fun y => ⟨(Module.reflection (coroot_apply_self B x.2) y),
        reflective_reflection B hSB x.2 y.2⟩
      left_inv := by
        intro y
        simp [involutive_reflection (coroot_apply_self B x.2) y]
      right_inv := by
        intro y
        simp [involutive_reflection (coroot_apply_self B x.2) y] }
  reflectionPerm_root := by
    simp [coe_ofPred, Module.reflection_apply]
  reflectionPerm_coroot x y := by
    simp only [coe_ofPred, mem_ofPred_eq, Embedding.coeFn_mk, Embedding.subtype_apply,
      Dual.eval_apply, Equiv.coe_fn_mk]
    ext z
    simp only [sub_apply, smul_apply, smul_eq_mul]
    refine y.2.1.1 ?_
    simp only [mem_ofPred_eq, mul_sub, apply_self_mul_coroot_apply B y.2, ← mul_assoc]
    rw [← isOrthogonal_reflection B x.2 hSB y y]; rw [apply_self_mul_coroot_apply]; rw [← hSB.eq z]; rw [← hSB.eq z]; rw [RingHom.id_apply]; rw [RingHom.id_apply]; rw [Module.reflection_apply]; rw [map_sub]; rw [mul_sub]; rw [sub_eq_sub_iff_comm]; rw [sub_left_inj]
    refine x.2.1.1 ?_
    simp only [mem_ofPred_eq, map_smul, smul_eq_mul]
    rw [← mul_assoc _ _ (B z x)]; rw [← mul_assoc _ _ (B z x)]; rw [mul_left_comm]; rw [apply_self_mul_coroot_apply B x.2]; rw [mul_left_comm (B x x)]; rw [apply_self_mul_coroot_apply B x.2]; rw [← hSB.eq x y]; rw [RingHom.id_apply]; rw [← hSB.eq x z]; rw [RingHom.id_apply]
    ring

end RootPairing
