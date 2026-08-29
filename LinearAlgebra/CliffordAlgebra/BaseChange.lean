/-
Copyright (c) 2023 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser
-/
module

public import Mathlib.LinearAlgebra.QuadraticForm.TensorProduct
public import Mathlib.LinearAlgebra.CliffordAlgebra.Conjugation
public import Mathlib.LinearAlgebra.TensorProduct.Opposite
public import Mathlib.RingTheory.TensorProduct.Basic

/-!
# The base change of a clifford algebra

In this file we show the isomorphism

* `CliffordAlgebra.equivBaseChange A Q` :
  `CliffordAlgebra (Q.baseChange A) ≃ₐ[A] (A ⊗[R] CliffordAlgebra Q)`
  with forward direction `CliffordAlgebra.toBaseChange A Q` and reverse direction
  `CliffordAlgebra.ofBaseChange A Q`.

This covers a more general case of the complexification of clifford algebras (as described in §2.2
of https://empg.maths.ed.ac.uk/Activities/Spin/Lecture2.pdf), where ℂ and ℝ are replaced by an
`R`-algebra `A` (where `2 : R` is invertible).

We show the additional results:

* `CliffordAlgebra.toBaseChange_ι`: the effect of base-changing pure vectors.
* `CliffordAlgebra.ofBaseChange_tmul_ι`: the effect of un-base-changing a tensor of a pure vectors.
* `CliffordAlgebra.toBaseChange_involute`: the effect of base-changing an involution.
* `CliffordAlgebra.toBaseChange_reverse`: the effect of base-changing a reversal.
-/

@[expose] public section

variable {R A V : Type*}
variable [CommRing R] [CommRing A] [AddCommGroup V]
variable [Algebra R A] [Module R V]
variable [Invertible (2 : R)]

open scoped TensorProduct

namespace CliffordAlgebra

variable (A)

set_option backward.isDefEq.respectTransparency false in
/--
Definition of `ofBaseChangeAux` / `ofBaseChangeAux` 的定义

English:
definition ofBaseChangeAux
  signature: (Q : QuadraticForm R V)
  body: CliffordAlgebra.lift Q by
    refine ⟨(ι (Q.baseChange A)).restrictScalars R ∘ₗ TensorProduct.mk R A V 1, fun v => ?_⟩
    refine (CliffordAlgebra.ι_sq_scalar (Q.baseChange A) (1 otimesₜ v)).trans ?_
    rw [QuadraticForm.baseChange_tmul]; rw [one_mul]; rw [← Algebra.algebraMap_eq_smul_one]; rw [← IsScalarTower.algebraMap_apply]

中文:
定义 ofBaseChangeAux
  签名: (Q : QuadraticForm R V)
  定义体: CliffordAlgebra.lift Q by
    refine ⟨(ι (Q.baseChange A)).restrictScalars R ∘ₗ TensorProduct.mk R A V 1, fun v => ?_⟩
    refine (CliffordAlgebra.ι_sq_scalar (Q.baseChange A) (1 otimesₜ v)).trans ?_
    rw [QuadraticForm.baseChange_tmul]; rw [one_mul]; rw [← Algebra.algebraMap_eq_smul_one]; rw [← IsScalarTower.algebraMap_apply]

Depends on / 依赖: Algebra, Algebra.algebraMap_eq_smul_one, CliffordAlgebra, CliffordAlgebra.lift, IsScalarTower, IsScalarTower.algebraMap_apply, Q.baseChange, QuadraticForm, QuadraticForm.baseChange_tmul, TensorProduct, TensorProduct.mk, algebraMap_apply, algebraMap_eq_smul_one, baseChange, baseChange_tmul, one_mul, restrictScalars
-/
def ofBaseChangeAux (Q : QuadraticForm R V) :
    CliffordAlgebra Q ->ₐ[R] CliffordAlgebra (Q.baseChange A) :=
CliffordAlgebra.lift Q by
    refine ⟨(ι (Q.baseChange A)).restrictScalars R ∘ₗ TensorProduct.mk R A V 1, fun v => ?_⟩
    refine (CliffordAlgebra.ι_sq_scalar (Q.baseChange A) (1 otimesₜ v)).trans ?_
    rw [QuadraticForm.baseChange_tmul]; rw [one_mul]; rw [← Algebra.algebraMap_eq_smul_one]; rw [← IsScalarTower.algebraMap_apply]

/--
theorem `ofBaseChangeAux_ι` / 定理 `ofBaseChangeAux_ι`

English:
theorem ofBaseChangeAux_ι
  given: (Q : QuadraticForm R V) (v : V)
  proof: CliffordAlgebra.lift_ι_apply _ _ v

中文:
定理 ofBaseChangeAux_ι
  条件: (Q : QuadraticForm R V) (v : V)
  证明: CliffordAlgebra.lift_ι_apply _ _ v
-/
@[simp] theorem ofBaseChangeAux_ι (Q : QuadraticForm R V) (v : V) :
    ofBaseChangeAux A Q (ι Q v) = ι (Q.baseChange A) (1 otimesₜ v) :=
  CliffordAlgebra.lift_ι_apply _ _ v

set_option backward.isDefEq.respectTransparency false in
/--
Definition of `ofBaseChange` / `ofBaseChange` 的定义

English:
definition ofBaseChange
  signature: (Q : QuadraticForm R V)
  body: Algebra.TensorProduct.lift (Algebra.ofId _ _) (ofBaseChangeAux A Q)
    fun _a _x => Algebra.commutes _ _

中文:
定义 ofBaseChange
  签名: (Q : QuadraticForm R V)
  定义体: Algebra.TensorProduct.lift (Algebra.ofId _ _) (ofBaseChangeAux A Q)
    fun _a _x => Algebra.commutes _ _

Depends on / 依赖: Algebra, Algebra.TensorProduct.lift, Algebra.commutes, Algebra.ofId, TensorProduct, commutes, ofBaseChangeAux
-/
def ofBaseChange (Q : QuadraticForm R V) :
    A otimes[R] CliffordAlgebra Q ->ₐ[A] CliffordAlgebra (Q.baseChange A) :=
  Algebra.TensorProduct.lift (Algebra.ofId _ _) (ofBaseChangeAux A Q)
    fun _a _x => Algebra.commutes _ _

/--
theorem `ofBaseChange_tmul_ι` / 定理 `ofBaseChange_tmul_ι`

English:
theorem ofBaseChange_tmul_ι
  given: (Q : QuadraticForm R V) (z : A) (v : V)
  proof: by
  change algebraMap _ _ z * ofBaseChangeAux A Q (ι Q v) = ι (Q.baseChange A) (z otimesₜ[R] v)
  rw [ofBaseChangeAux_ι]; rw [← Algebra.smul_def]; rw [← map_smul]; rw [TensorProduct.smul_tmul']; rw [smul_eq_mul]; rw [mul_one]

中文:
定理 ofBaseChange_tmul_ι
  条件: (Q : QuadraticForm R V) (z : A) (v : V)
  证明: by
  change algebraMap _ _ z * ofBaseChangeAux A Q (ι Q v) = ι (Q.baseChange A) (z otimesₜ[R] v)
  rw [ofBaseChangeAux_ι]; rw [← Algebra.smul_def]; rw [← map_smul]; rw [TensorProduct.smul_tmul']; rw [smul_eq_mul]; rw [mul_one]
-/
@[simp] theorem ofBaseChange_tmul_ι (Q : QuadraticForm R V) (z : A) (v : V) :
    ofBaseChange A Q (z otimesₜ ι Q v) = ι (Q.baseChange A) (z otimesₜ v) := by
  change algebraMap _ _ z * ofBaseChangeAux A Q (ι Q v) = ι (Q.baseChange A) (z otimesₜ[R] v)
  rw [ofBaseChangeAux_ι]; rw [← Algebra.smul_def]; rw [← map_smul]; rw [TensorProduct.smul_tmul']; rw [smul_eq_mul]; rw [mul_one]

/--
theorem `ofBaseChange_tmul_one` / 定理 `ofBaseChange_tmul_one`

English:
theorem ofBaseChange_tmul_one
  given: (Q : QuadraticForm R V) (z : A)
  proof: by
  change algebraMap _ _ z * ofBaseChangeAux A Q 1 = _
  rw [map_one]; rw [mul_one]

中文:
定理 ofBaseChange_tmul_one
  条件: (Q : QuadraticForm R V) (z : A)
  证明: by
  change algebraMap _ _ z * ofBaseChangeAux A Q 1 = _
  rw [map_one]; rw [mul_one]
-/
@[simp] theorem ofBaseChange_tmul_one (Q : QuadraticForm R V) (z : A) :
    ofBaseChange A Q (z otimesₜ 1) = algebraMap _ _ z := by
  change algebraMap _ _ z * ofBaseChangeAux A Q 1 = _
  rw [map_one]; rw [mul_one]

set_option backward.defeqAttrib.useBackward true in
/--
Definition of `toBaseChange` / `toBaseChange` 的定义

English:
definition toBaseChange
  signature: (Q : QuadraticForm R V)
  body: CliffordAlgebra.lift _ by
    refine ⟨TensorProduct.AlgebraTensorModule.map (LinearMap.id : A ->ₗ[A] A) (ι Q), ?_⟩
    let : Invertible (2 : A) := (Invertible.map (algebraMap R A) 2).copy 2 (map_ofNat _ _).symm
    let : Invertible (2 : A otimes[R] CliffordAlgebra Q) :=
      (Invertible.map (algebraMap R _) 2).copy 2 (map_ofNat _ _).symm
    suffices hpure_tensor : forall v w, (1 * 1) otimesₜ[R] (ι Q v * ι Q w) + (1 * 1) otimesₜ[R] (ι Q w * ι Q v) =
        QuadraticMap.polarBilin (Q.baseChange A) (1 otimesₜ[R] v) (1 otimesₜ[R] w) otimesₜ[R] 1 by
      -- the crux is that by converting to a statement about linear maps instead of quadratic forms,
      -- we then have access to all the partially-applied `ext` lemmas.
      rw [CliffordAlgebra.forall_mul_self_eq_iff (isUnit_of_invertible _)]
      refine TensorProduct.AlgebraTensorModule.curry_injective ?_
      ext v w
      dsimp
      exact hpure_tensor v w
    intro v w
    rw [← TensorProduct.tmul_add]; rw [CliffordAlgebra.ι_mul_ι_add_swap]; rw [QuadraticForm.polarBilin_baseChange]; rw [LinearMap.BilinForm.baseChange_tmul]; rw [one_mul]; rw [TensorProduct.smul_tmul]; rw [Algebra.algebraMap_eq_smul_one]; rw [QuadraticMap.polarBilin_apply_apply]

中文:
定义 toBaseChange
  签名: (Q : QuadraticForm R V)
  定义体: CliffordAlgebra.lift _ by
    refine ⟨TensorProduct.AlgebraTensorModule.map (LinearMap.id : A ->ₗ[A] A) (ι Q), ?_⟩
    let : Invertible (2 : A) := (Invertible.map (algebraMap R A) 2).copy 2 (map_ofNat _ _).symm
    let : Invertible (2 : A otimes[R] CliffordAlgebra Q) :=
      (Invertible.map (algebraMap R _) 2).copy 2 (map_ofNat _ _).symm
    suffices hpure_tensor : forall v w, (1 * 1) otimesₜ[R] (ι Q v * ι Q w) + (1 * 1) otimesₜ[R] (ι Q w * ι Q v) =
        QuadraticMap.polarBilin (Q.baseChange A) (1 otimesₜ[R] v) (1 otimesₜ[R] w) otimesₜ[R] 1 by
      -- the crux is that by converting to a statement about linear maps instead of quadratic forms,
      -- we then have access to all the partially-applied `ext` lemmas.
      rw [CliffordAlgebra.forall_mul_self_eq_iff (isUnit_of_invertible _)]
      refine TensorProduct.AlgebraTensorModule.curry_injective ?_
      ext v w
      dsimp
      exact hpure_tensor v w
    intro v w
    rw [← TensorProduct.tmul_add]; rw [CliffordAlgebra.ι_mul_ι_add_swap]; rw [QuadraticForm.polarBilin_baseChange]; rw [LinearMap.BilinForm.baseChange_tmul]; rw [one_mul]; rw [TensorProduct.smul_tmul]; rw [Algebra.algebraMap_eq_smul_one]; rw [QuadraticMap.polarBilin_apply_apply]

Depends on / 依赖: AlgebraTensorModule, CliffordAlgebra, CliffordAlgebra.lift, Invertible, Invertible.map, LinearMap, LinearMap.id, Q.baseChange, QuadraticMap, QuadraticMap.polarBilin, TensorProduct, TensorProduct.AlgebraTensorModule.map, algebraMap, baseChange, hpure_tensor, map_ofNat, otimes, polarBilin
-/
def toBaseChange (Q : QuadraticForm R V) :
    CliffordAlgebra (Q.baseChange A) ->ₐ[A] A otimes[R] CliffordAlgebra Q :=
CliffordAlgebra.lift _ by
    refine ⟨TensorProduct.AlgebraTensorModule.map (LinearMap.id : A ->ₗ[A] A) (ι Q), ?_⟩
    let : Invertible (2 : A) := (Invertible.map (algebraMap R A) 2).copy 2 (map_ofNat _ _).symm
    let : Invertible (2 : A otimes[R] CliffordAlgebra Q) :=
      (Invertible.map (algebraMap R _) 2).copy 2 (map_ofNat _ _).symm
    suffices hpure_tensor : forall v w, (1 * 1) otimesₜ[R] (ι Q v * ι Q w) + (1 * 1) otimesₜ[R] (ι Q w * ι Q v) =
        QuadraticMap.polarBilin (Q.baseChange A) (1 otimesₜ[R] v) (1 otimesₜ[R] w) otimesₜ[R] 1 by
      -- the crux is that by converting to a statement about linear maps instead of quadratic forms,
      -- we then have access to all the partially-applied `ext` lemmas.
      rw [CliffordAlgebra.forall_mul_self_eq_iff (isUnit_of_invertible _)]
      refine TensorProduct.AlgebraTensorModule.curry_injective ?_
      ext v w
      dsimp
      exact hpure_tensor v w
    intro v w
    rw [← TensorProduct.tmul_add]; rw [CliffordAlgebra.ι_mul_ι_add_swap]; rw [QuadraticForm.polarBilin_baseChange]; rw [LinearMap.BilinForm.baseChange_tmul]; rw [one_mul]; rw [TensorProduct.smul_tmul]; rw [Algebra.algebraMap_eq_smul_one]; rw [QuadraticMap.polarBilin_apply_apply]

/--
theorem `toBaseChange_ι` / 定理 `toBaseChange_ι`

English:
theorem toBaseChange_ι
  given: (Q : QuadraticForm R V) (z : A) (v : V)
  proof: CliffordAlgebra.lift_ι_apply _ _ _

中文:
定理 toBaseChange_ι
  条件: (Q : QuadraticForm R V) (z : A) (v : V)
  证明: CliffordAlgebra.lift_ι_apply _ _ _
-/
@[simp] theorem toBaseChange_ι (Q : QuadraticForm R V) (z : A) (v : V) :
    toBaseChange A Q (ι (Q.baseChange A) (z otimesₜ v)) = z otimesₜ ι Q v :=
  CliffordAlgebra.lift_ι_apply _ _ _

/--
theorem `toBaseChange_comp_involute` / 定理 `toBaseChange_comp_involute`

English:
theorem toBaseChange_comp_involute
  given: (Q : QuadraticForm R V)
  proof: by
  ext v
  change toBaseChange A Q (involute (ι (Q.baseChange A) (1 otimesₜ[R] v)))
    = (Algebra.TensorProduct.map (AlgHom.id _ _) involute :
        A otimes[R] CliffordAlgebra Q ->ₐ[A] _)
      (toBaseChange A Q (ι (Q.baseChange A) (1 otimesₜ[R] v)))
  rw [toBaseChange_ι]; rw [involute_ι]; rw [map_neg (toBaseChange A Q)]; rw [toBaseChange_ι]; rw [Algebra.TensorProduct.map_tmul]; rw [AlgHom.id_apply]; rw [involute_ι]; rw [TensorProduct.tmul_neg]

中文:
定理 toBaseChange_comp_involute
  条件: (Q : QuadraticForm R V)
  证明: by
  ext v
  change toBaseChange A Q (involute (ι (Q.baseChange A) (1 otimesₜ[R] v)))
    = (Algebra.TensorProduct.map (AlgHom.id _ _) involute :
        A otimes[R] CliffordAlgebra Q ->ₐ[A] _)
      (toBaseChange A Q (ι (Q.baseChange A) (1 otimesₜ[R] v)))
  rw [toBaseChange_ι]; rw [involute_ι]; rw [map_neg (toBaseChange A Q)]; rw [toBaseChange_ι]; rw [Algebra.TensorProduct.map_tmul]; rw [AlgHom.id_apply]; rw [involute_ι]; rw [TensorProduct.tmul_neg]

Depends on / 依赖: AlgHom, AlgHom.id, AlgHom.id_apply, Algebra, Algebra.TensorProduct.map, Algebra.TensorProduct.map_tmul, CliffordAlgebra, Q.baseChange, TensorProduct, TensorProduct.tmul_neg, baseChange, id_apply, involute, map_neg, map_tmul, otimes, tmul_neg, toBaseChange
-/
theorem toBaseChange_comp_involute (Q : QuadraticForm R V) :
    (toBaseChange A Q).comp (involute : CliffordAlgebra (Q.baseChange A) ->ₐ[A] _) =
      (Algebra.TensorProduct.map (AlgHom.id _ _) involute).comp (toBaseChange A Q) := by
  ext v
  change toBaseChange A Q (involute (ι (Q.baseChange A) (1 otimesₜ[R] v)))
    = (Algebra.TensorProduct.map (AlgHom.id _ _) involute :
        A otimes[R] CliffordAlgebra Q ->ₐ[A] _)
      (toBaseChange A Q (ι (Q.baseChange A) (1 otimesₜ[R] v)))
  rw [toBaseChange_ι]; rw [involute_ι]; rw [map_neg (toBaseChange A Q)]; rw [toBaseChange_ι]; rw [Algebra.TensorProduct.map_tmul]; rw [AlgHom.id_apply]; rw [involute_ι]; rw [TensorProduct.tmul_neg]

/--
theorem `toBaseChange_involute` / 定理 `toBaseChange_involute`

English:
theorem toBaseChange_involute
  given: (Q : QuadraticForm R V) (x : CliffordAlgebra (Q.baseChange A))
  proof: DFunLike.congr_fun (toBaseChange_comp_involute A Q) x

中文:
定理 toBaseChange_involute
  条件: (Q : QuadraticForm R V) (x : CliffordAlgebra (Q.baseChange A))
  证明: DFunLike.congr_fun (toBaseChange_comp_involute A Q) x

Depends on / 依赖: DFunLike, DFunLike.congr_fun, congr_fun, toBaseChange_comp_involute
-/
theorem toBaseChange_involute (Q : QuadraticForm R V) (x : CliffordAlgebra (Q.baseChange A)) :
    toBaseChange A Q (involute x) =
      TensorProduct.map LinearMap.id (involute.toLinearMap) (toBaseChange A Q x) :=
  DFunLike.congr_fun (toBaseChange_comp_involute A Q) x

open MulOpposite

/--
theorem `toBaseChange_comp_reverseOp` / 定理 `toBaseChange_comp_reverseOp`

English:
theorem toBaseChange_comp_reverseOp
  given: (Q : QuadraticForm R V)
  proof: by
  ext v
  change op (toBaseChange A Q (reverse (ι (Q.baseChange A) (1 otimesₜ[R] v)))) =
    Algebra.TensorProduct.opAlgEquiv R A A (CliffordAlgebra Q)
      (Algebra.TensorProduct.map (AlgEquiv.toOpposite A A).toAlgHom (reverseOp (Q := Q))
        (toBaseChange A Q (ι (Q.baseChange A) (1 otimesₜ[R] v))))
  rw [toBaseChange_ι]; rw [reverse_ι]; rw [toBaseChange_ι]; rw [Algebra.TensorProduct.map_tmul]; rw [Algebra.TensorProduct.opAlgEquiv_tmul]; rw [reverseOp_ι]
  rfl

中文:
定理 toBaseChange_comp_reverseOp
  条件: (Q : QuadraticForm R V)
  证明: by
  ext v
  change op (toBaseChange A Q (reverse (ι (Q.baseChange A) (1 otimesₜ[R] v)))) =
    Algebra.TensorProduct.opAlgEquiv R A A (CliffordAlgebra Q)
      (Algebra.TensorProduct.map (AlgEquiv.toOpposite A A).toAlgHom (reverseOp (Q := Q))
        (toBaseChange A Q (ι (Q.baseChange A) (1 otimesₜ[R] v))))
  rw [toBaseChange_ι]; rw [reverse_ι]; rw [toBaseChange_ι]; rw [Algebra.TensorProduct.map_tmul]; rw [Algebra.TensorProduct.opAlgEquiv_tmul]; rw [reverseOp_ι]
  rfl
-/
theorem toBaseChange_comp_reverseOp (Q : QuadraticForm R V) :
    (toBaseChange A Q).op.comp reverseOp =
      ((Algebra.TensorProduct.opAlgEquiv R A A (CliffordAlgebra Q)).toAlgHom.comp <|
        (Algebra.TensorProduct.map
          (AlgEquiv.toOpposite A A).toAlgHom (reverseOp (Q := Q))).comp
        (toBaseChange A Q)) := by
  ext v
  change op (toBaseChange A Q (reverse (ι (Q.baseChange A) (1 otimesₜ[R] v)))) =
    Algebra.TensorProduct.opAlgEquiv R A A (CliffordAlgebra Q)
      (Algebra.TensorProduct.map (AlgEquiv.toOpposite A A).toAlgHom (reverseOp (Q := Q))
        (toBaseChange A Q (ι (Q.baseChange A) (1 otimesₜ[R] v))))
  rw [toBaseChange_ι]; rw [reverse_ι]; rw [toBaseChange_ι]; rw [Algebra.TensorProduct.map_tmul]; rw [Algebra.TensorProduct.opAlgEquiv_tmul]; rw [reverseOp_ι]
  rfl

/--
theorem `toBaseChange_reverse` / 定理 `toBaseChange_reverse`

English:
theorem toBaseChange_reverse
  given: (Q : QuadraticForm R V) (x : CliffordAlgebra (Q.baseChange A))
  proof: by
  have := DFunLike.congr_fun (toBaseChange_comp_reverseOp A Q) x
  refine (congr_arg unop this).trans ?_; clear this
  refine (LinearMap.congr_fun (TensorProduct.AlgebraTensorModule.map_comp _ _ _ _).symm _).trans ?_
  rw [reverse]; rw [AlgEquiv.toAlgHom_toLinearMap]; rw [AlgEquiv.toLinearEquiv_toOpposite]
  dsimp
  -- `simp` fails here due to a timeout looking for a `Subsingleton` instance!?
  rw [LinearEquiv.self_trans_symm]
  rfl

中文:
定理 toBaseChange_reverse
  条件: (Q : QuadraticForm R V) (x : CliffordAlgebra (Q.baseChange A))
  证明: by
  have := DFunLike.congr_fun (toBaseChange_comp_reverseOp A Q) x
  refine (congr_arg unop this).trans ?_; clear this
  refine (LinearMap.congr_fun (TensorProduct.AlgebraTensorModule.map_comp _ _ _ _).symm _).trans ?_
  rw [reverse]; rw [AlgEquiv.toAlgHom_toLinearMap]; rw [AlgEquiv.toLinearEquiv_toOpposite]
  dsimp
  -- `simp` fails here due to a timeout looking for a `Subsingleton` instance!?
  rw [LinearEquiv.self_trans_symm]
  rfl

Depends on / 依赖: AlgEquiv, AlgEquiv.toAlgHom_toLinearMap, AlgEquiv.toLinearEquiv_toOpposite, AlgebraTensorModule, DFunLike, DFunLike.congr_fun, LinearMap, LinearMap.congr_fun, TensorProduct, TensorProduct.AlgebraTensorModule.map_comp, congr_arg, congr_fun, map_comp, reverse, toAlgHom_toLinearMap, toBaseChange_comp_reverseOp, toLinearEquiv_toOpposite
-/
theorem toBaseChange_reverse (Q : QuadraticForm R V) (x : CliffordAlgebra (Q.baseChange A)) :
    toBaseChange A Q (reverse x) =
      TensorProduct.map LinearMap.id reverse (toBaseChange A Q x) := by
  have := DFunLike.congr_fun (toBaseChange_comp_reverseOp A Q) x
  refine (congr_arg unop this).trans ?_; clear this
  refine (LinearMap.congr_fun (TensorProduct.AlgebraTensorModule.map_comp _ _ _ _).symm _).trans ?_
  rw [reverse]; rw [AlgEquiv.toAlgHom_toLinearMap]; rw [AlgEquiv.toLinearEquiv_toOpposite]
  dsimp
  -- `simp` fails here due to a timeout looking for a `Subsingleton` instance!?
  rw [LinearEquiv.self_trans_symm]
  rfl

attribute [ext] TensorProduct.ext

/--
theorem `toBaseChange_comp_ofBaseChange` / 定理 `toBaseChange_comp_ofBaseChange`

English:
theorem toBaseChange_comp_ofBaseChange
  given: (Q : QuadraticForm R V)
  proof: by
  ext v
  simp

中文:
定理 toBaseChange_comp_ofBaseChange
  条件: (Q : QuadraticForm R V)
  证明: by
  ext v
  simp
-/
theorem toBaseChange_comp_ofBaseChange (Q : QuadraticForm R V) :
    (toBaseChange A Q).comp (ofBaseChange A Q) = AlgHom.id _ _ := by
  ext v
  simp

/--
theorem `toBaseChange_ofBaseChange` / 定理 `toBaseChange_ofBaseChange`

English:
theorem toBaseChange_ofBaseChange
  given: (Q : QuadraticForm R V) (x : A otimes[R] CliffordAlgebra Q)
  proof: AlgHom.congr_fun (toBaseChange_comp_ofBaseChange A Q :) x

中文:
定理 toBaseChange_ofBaseChange
  条件: (Q : QuadraticForm R V) (x : A otimes[R] CliffordAlgebra Q)
  证明: AlgHom.congr_fun (toBaseChange_comp_ofBaseChange A Q :) x
-/
@[simp] theorem toBaseChange_ofBaseChange (Q : QuadraticForm R V) (x : A otimes[R] CliffordAlgebra Q) :
    toBaseChange A Q (ofBaseChange A Q x) = x :=
  AlgHom.congr_fun (toBaseChange_comp_ofBaseChange A Q :) x

set_option backward.isDefEq.respectTransparency false in
/--
theorem `ofBaseChange_comp_toBaseChange` / 定理 `ofBaseChange_comp_toBaseChange`

English:
theorem ofBaseChange_comp_toBaseChange
  given: (Q : QuadraticForm R V)
  proof: by
  ext x
  change ofBaseChange A Q (toBaseChange A Q (ι (Q.baseChange A) (1 otimesₜ[R] x)))
    = ι (Q.baseChange A) (1 otimesₜ[R] x)
  rw [toBaseChange_ι]; rw [ofBaseChange_tmul_ι]

中文:
定理 ofBaseChange_comp_toBaseChange
  条件: (Q : QuadraticForm R V)
  证明: by
  ext x
  change ofBaseChange A Q (toBaseChange A Q (ι (Q.baseChange A) (1 otimesₜ[R] x)))
    = ι (Q.baseChange A) (1 otimesₜ[R] x)
  rw [toBaseChange_ι]; rw [ofBaseChange_tmul_ι]

Depends on / 依赖: Q.baseChange, baseChange, ofBaseChange, toBaseChange
-/
theorem ofBaseChange_comp_toBaseChange (Q : QuadraticForm R V) :
    (ofBaseChange A Q).comp (toBaseChange A Q) = AlgHom.id _ _ := by
  ext x
  change ofBaseChange A Q (toBaseChange A Q (ι (Q.baseChange A) (1 otimesₜ[R] x)))
    = ι (Q.baseChange A) (1 otimesₜ[R] x)
  rw [toBaseChange_ι]; rw [ofBaseChange_tmul_ι]

/--
theorem `ofBaseChange_toBaseChange` / 定理 `ofBaseChange_toBaseChange`

English:
theorem ofBaseChange_toBaseChange
  proof: AlgHom.congr_fun (ofBaseChange_comp_toBaseChange A Q :) x

中文:
定理 ofBaseChange_toBaseChange
  证明: AlgHom.congr_fun (ofBaseChange_comp_toBaseChange A Q :) x
-/
@[simp] theorem ofBaseChange_toBaseChange
    (Q : QuadraticForm R V) (x : CliffordAlgebra (Q.baseChange A)) :
    ofBaseChange A Q (toBaseChange A Q x) = x :=
  AlgHom.congr_fun (ofBaseChange_comp_toBaseChange A Q :) x

/-- Base-changing the vector space of a clifford algebra is isomorphic as an A-algebra to
base-changing the clifford algebra itself; $<|Cℓ(A ⊗_R V, Q_A) ≅ A ⊗_R Cℓ(V, Q)<|$.

This is `CliffordAlgebra.toBaseChange` and `CliffordAlgebra.ofBaseChange` as an equivalence. -/
@[simps!]
/--
Definition of `equivBaseChange` / `equivBaseChange` 的定义

English:
definition equivBaseChange
  signature: (Q : QuadraticForm R V)
  body: AlgEquiv.ofAlgHom (toBaseChange A Q) (ofBaseChange A Q)
    (toBaseChange_comp_ofBaseChange A Q)
    (ofBaseChange_comp_toBaseChange A Q)

中文:
定义 equivBaseChange
  签名: (Q : QuadraticForm R V)
  定义体: AlgEquiv.ofAlgHom (toBaseChange A Q) (ofBaseChange A Q)
    (toBaseChange_comp_ofBaseChange A Q)
    (ofBaseChange_comp_toBaseChange A Q)

Depends on / 依赖: AlgEquiv, AlgEquiv.ofAlgHom, ofAlgHom, ofBaseChange, ofBaseChange_comp_toBaseChange, toBaseChange, toBaseChange_comp_ofBaseChange
-/
def equivBaseChange (Q : QuadraticForm R V) :
    CliffordAlgebra (Q.baseChange A) ≃ₐ[A] A otimes[R] CliffordAlgebra Q :=
  AlgEquiv.ofAlgHom (toBaseChange A Q) (ofBaseChange A Q)
    (toBaseChange_comp_ofBaseChange A Q)
    (ofBaseChange_comp_toBaseChange A Q)

end CliffordAlgebra
