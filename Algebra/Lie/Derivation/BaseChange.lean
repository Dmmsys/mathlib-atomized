/-
Copyright (c) 2026 Leonid Ryvkin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonid Ryvkin
-/
module

public import Mathlib.Algebra.Lie.BaseChange
public import Mathlib.Algebra.Lie.Derivation.Basic
public import Mathlib.RingTheory.Derivation.Lie

/-!
# LieDerivations of a Lie algebra created through BaseChange

When, given an `R`-algebra `A` and an `R`-Lie algebra `L` the (Lie algebra) basechange `A ⊗[R] L`,
both derivations of `A` and Lie derivations of `L` induce Lie derivations of `A ⊗[R] L`. Moreover,
both these procedures are Lie algebra homomorphisms themselves.


## Tags

lie algebra, extension of scalars, base change, derivation

-/

@[expose] public section
namespace Lie.Derivation

open TensorProduct
variable {R : Type*} [CommRing R]
variable {A : Type*} [CommRing A] [Algebra R A]
variable {L : Type*} [LieRing L] [LieAlgebra R L]
attribute [local instance 100] LieRing.ofAssociativeRing

variable (L) in
/--
Definition of `ofDerivation` / `ofDerivation` 的定义

English:
definition ofDerivation
  signature: : Derivation R A A ->ₗ⁅R⁆ LieDerivation R (A otimes[R] L) (A otimes[R] L) where
  body: { toFun := d.rTensor L
      map_add' := by simp
      map_smul' := by simp
      leibniz' x y := by
        simp only [LinearMap.coe_mk, AddHom.coe_mk]
        refine x.induction_on (by simp) (fun _ l => ?_) (fun _ _ h1 h2 => ?_)
        · refine y.induction_on (by simp) (fun _ l' => ?_) (fun _ _ h1 h2 => ?_)
          · simp [← lie_skew l' l, -lie_skew, add_tmul, tmul_neg]
          · simp [h1, h2, sub_add_sub_comm]
        · simp [h1, h2, sub_add_sub_comm] }
  map_add' _ _ := by ext; simp
  map_smul' _ _ := by ext; simp
  map_lie' {_ _} := by
    ext z
    refine z.induction_on (by simp) (by simp [sub_tmul]) (fun _ _ hx hy => ?_)
    simp_all
    abel

@[simp]

中文:
定义 ofDerivation
  签名: : 导子 R A A ->ₗ⁅R⁆ LieDerivation R (A otimes[R] L) (A otimes[R] L) where
  定义体: { toFun := d.rTensor L
      map_add' := by simp
      map_smul' := by simp
      leibniz' x y := by
        simp only [LinearMap.coe_mk, AddHom.coe_mk]
        refine x.induction_on (by simp) (fun _ l => ?_) (fun _ _ h1 h2 => ?_)
        · refine y.induction_on (by simp) (fun _ l' => ?_) (fun _ _ h1 h2 => ?_)
          · simp [← lie_skew l' l, -lie_skew, add_tmul, tmul_neg]
          · simp [h1, h2, sub_add_sub_comm]
        · simp [h1, h2, sub_add_sub_comm] }
  map_add' _ _ := by ext; simp
  map_smul' _ _ := by ext; simp
  map_lie' {_ _} := by
    ext z
    refine z.induction_on (by simp) (by simp [sub_tmul]) (fun _ _ hx hy => ?_)
    simp_all
    abel

@[simp]

Depends on / 依赖: AddHom, AddHom.coe_mk, LinearMap, LinearMap.coe_mk, add_tmul, coe_mk, d.rTensor, induction_on, leibniz, lie_skew, map_add, map_lie, map_smul, rTensor, sub_add_sub_comm, tmul_neg, x.induction_on, y.induction_on, z.induction
-/
def ofDerivation : Derivation R A A ->ₗ⁅R⁆ LieDerivation R (A otimes[R] L) (A otimes[R] L) where
  toFun d :=
    { toFun := d.rTensor L
      map_add' := by simp
      map_smul' := by simp
      leibniz' x y := by
        simp only [LinearMap.coe_mk, AddHom.coe_mk]
        refine x.induction_on (by simp) (fun _ l => ?_) (fun _ _ h1 h2 => ?_)
        · refine y.induction_on (by simp) (fun _ l' => ?_) (fun _ _ h1 h2 => ?_)
          · simp [← lie_skew l' l, -lie_skew, add_tmul, tmul_neg]
          · simp [h1, h2, sub_add_sub_comm]
        · simp [h1, h2, sub_add_sub_comm] }
  map_add' _ _ := by ext; simp
  map_smul' _ _ := by ext; simp
  map_lie' {_ _} := by
    ext z
    refine z.induction_on (by simp) (by simp [sub_tmul]) (fun _ _ hx hy => ?_)
    simp_all
    abel

@[simp]
/--
lemma `ofDerivation_apply` / 引理 `ofDerivation_apply`

English:
lemma ofDerivation_apply
  given: (d : Derivation R A A) (x : A otimes[R] L)
  proof: rfl

中文:
引理 ofDerivation_apply
  条件: (d : 导子 R A A) (x : A otimes[R] L)
  证明: rfl
-/
lemma ofDerivation_apply (d : Derivation R A A) (x : A otimes[R] L) :
    ofDerivation L d x = d.toLinearMap.rTensor L x :=
  rfl

variable (A) in
/--
Definition of `ofLieDerivation` / `ofLieDerivation` 的定义

English:
definition ofLieDerivation
  signature: : (LieDerivation R L L) ->ₗ⁅R⁆ (LieDerivation R (A otimes[R] L) (A otimes[R] L)) where
  body: { toFun := d.toLinearMap.lTensor A
      map_add' := by simp
      map_smul' := by simp
      leibniz' x y := by
        simp only [LinearMap.coe_mk, AddHom.coe_mk]
        refine x.induction_on (by simp) ?_ ?_
        · intros _ _
          refine y.induction_on (by simp) ?_ ?_
          · intros _ _
            simp [LieAlgebra.ExtendScalars.bracket_tmul, tmul_sub, mul_comm]
          · intros _ _ h1 h2
            simp [h1, h2]
            abel_nf
        · intros _ _ h1 h2
          simp [h1, h2]
          abel_nf }
  map_add' _ _ := by ext _; simp
  map_smul' _ _ := by ext _; simp
  map_lie' {_ _} := by
    ext z
    refine z.induction_on (by simp) (fun a l => ?_) (fun _ _ hx hy => ?_)
    · simp [tmul_sub]
    · simp_all [sub_add_sub_comm]

@[simp]

中文:
定义 ofLieDerivation
  签名: : (LieDerivation R L L) ->ₗ⁅R⁆ (LieDerivation R (A otimes[R] L) (A otimes[R] L)) where
  定义体: { toFun := d.toLinearMap.lTensor A
      map_add' := by simp
      map_smul' := by simp
      leibniz' x y := by
        simp only [LinearMap.coe_mk, AddHom.coe_mk]
        refine x.induction_on (by simp) ?_ ?_
        · intros _ _
          refine y.induction_on (by simp) ?_ ?_
          · intros _ _
            simp [LieAlgebra.ExtendScalars.bracket_tmul, tmul_sub, mul_comm]
          · intros _ _ h1 h2
            simp [h1, h2]
            abel_nf
        · intros _ _ h1 h2
          simp [h1, h2]
          abel_nf }
  map_add' _ _ := by ext _; simp
  map_smul' _ _ := by ext _; simp
  map_lie' {_ _} := by
    ext z
    refine z.induction_on (by simp) (fun a l => ?_) (fun _ _ hx hy => ?_)
    · simp [tmul_sub]
    · simp_all [sub_add_sub_comm]

@[simp]

Depends on / 依赖: AddHom, AddHom.coe_mk, ExtendScalars, LieAlgebra, LieAlgebra.ExtendScalars.bracket_tmul, LinearMap, LinearMap.coe_mk, abel_nf, bracket_tmul, coe_mk, d.toLinearMap.lTensor, induction_o, induction_on, intros, lTensor, leibniz, map_add, map_lie, map_smul, mul_comm
-/
def ofLieDerivation : (LieDerivation R L L) ->ₗ⁅R⁆ (LieDerivation R (A otimes[R] L) (A otimes[R] L)) where
  toFun d :=
    { toFun := d.toLinearMap.lTensor A
      map_add' := by simp
      map_smul' := by simp
      leibniz' x y := by
        simp only [LinearMap.coe_mk, AddHom.coe_mk]
        refine x.induction_on (by simp) ?_ ?_
        · intros _ _
          refine y.induction_on (by simp) ?_ ?_
          · intros _ _
            simp [LieAlgebra.ExtendScalars.bracket_tmul, tmul_sub, mul_comm]
          · intros _ _ h1 h2
            simp [h1, h2]
            abel_nf
        · intros _ _ h1 h2
          simp [h1, h2]
          abel_nf }
  map_add' _ _ := by ext _; simp
  map_smul' _ _ := by ext _; simp
  map_lie' {_ _} := by
    ext z
    refine z.induction_on (by simp) (fun a l => ?_) (fun _ _ hx hy => ?_)
    · simp [tmul_sub]
    · simp_all [sub_add_sub_comm]

@[simp]
/--
lemma `ofLieDerivation_apply` / 引理 `ofLieDerivation_apply`

English:
lemma ofLieDerivation_apply
  given: (d : LieDerivation R L L) (x : A otimes[R] L)
  proof: rfl

中文:
引理 ofLieDerivation_apply
  条件: (d : LieDerivation R L L) (x : A otimes[R] L)
  证明: rfl
-/
lemma ofLieDerivation_apply (d : LieDerivation R L L) (x : A otimes[R] L) :
    ofLieDerivation A d x = d.toLinearMap.lTensor A x :=
  rfl

end Lie.Derivation
end
