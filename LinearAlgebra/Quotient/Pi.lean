/-
Copyright (c) 2022 Anne Baanen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anne Baanen, Alex J. Best
-/
module

public import Mathlib.LinearAlgebra.Pi
public import Mathlib.LinearAlgebra.Quotient.Basic

/-!
# Submodule quotients and direct sums

This file contains some results on the quotient of a module by a direct sum of submodules,
and the direct sum of quotients of modules by submodules.

## Main definitions

* `Submodule.piQuotientLift`: create a map out of the direct sum of quotients
* `Submodule.quotientPiLift`: create a map out of the quotient of a direct sum
* `Submodule.quotientPi`: the quotient of a direct sum is the direct sum of quotients.

-/

@[expose] public section


namespace Submodule

open LinearMap

variable {ι R : Type*} [CommRing R]
variable {Ms : ι -> Type*} [forall i, AddCommGroup (Ms i)] [forall i, Module R (Ms i)]
variable {N : Type*} [AddCommGroup N] [Module R N]
variable {Ns : ι -> Type*} [forall i, AddCommGroup (Ns i)] [forall i, Module R (Ns i)]

/--
Definition of `piQuotientLift` / `piQuotientLift` 的定义

English:
definition piQuotientLift
  signature: [Fintype ι] [DecidableEq ι] (p : forall i, Submodule R (Ms i)) (q : Submodule R N)
  body: lsum R (fun i => Ms i ⧸ p i) R fun i => (p i).mapQ q (f i) (hf i)

@[simp]

中文:
定义 piQuotientLift
  签名: [有限类型 ι] [DecidableEq ι] (p : 对任意 i, 子模 R (Ms i)) (q : 子模 R N)
  定义体: lsum R (fun i => Ms i ⧸ p i) R fun i => (p i).mapQ q (f i) (hf i)

@[simp]
-/
def piQuotientLift [Fintype ι] [DecidableEq ι] (p : forall i, Submodule R (Ms i)) (q : Submodule R N)
    (f : forall i, Ms i ->ₗ[R] N) (hf : forall i, p i <= q.comap (f i)) : (forall i, Ms i ⧸ p i) ->ₗ[R] N ⧸ q :=
  lsum R (fun i => Ms i ⧸ p i) R fun i => (p i).mapQ q (f i) (hf i)

@[simp]
/--
theorem `piQuotientLift_mk` / 定理 `piQuotientLift_mk`

English:
theorem piQuotientLift_mk
  statement: [Fintype ι] [DecidableEq ι] (p : forall i, Submodule R (Ms i))
  proof: by
  rw [piQuotientLift]; rw [lsum_apply]; rw [sum_apply]; rw [← mkQ_apply]; rw [lsum_apply]; rw [sum_apply]; rw [_root_.map_sum]
  simp only [coe_proj, mapQ_apply, mkQ_apply, comp_apply]

@[simp]

中文:
定理 piQuotientLift_mk
  结论: [有限类型 ι] [DecidableEq ι] (p : 对任意 i, 子模 R (Ms i))
  证明: by
  rw [piQuotientLift]; rw [lsum_apply]; rw [sum_apply]; rw [← mkQ_apply]; rw [lsum_apply]; rw [sum_apply]; rw [_root_.map_sum]
  simp only [coe_proj, mapQ_apply, mkQ_apply, comp_apply]

@[simp]

Depends on / 依赖: _root_, _root_.map_sum, coe_proj, comp_apply, lsum_apply, mapQ_apply, map_sum, mkQ_apply, piQuotientLift, sum_apply
-/
theorem piQuotientLift_mk [Fintype ι] [DecidableEq ι] (p : forall i, Submodule R (Ms i))
    (q : Submodule R N) (f : forall i, Ms i ->ₗ[R] N) (hf : forall i, p i <= q.comap (f i)) (x : forall i, Ms i) :
    (piQuotientLift p q f hf fun i => Quotient.mk (x i)) = Quotient.mk (lsum _ _ R f x) := by
  rw [piQuotientLift]; rw [lsum_apply]; rw [sum_apply]; rw [← mkQ_apply]; rw [lsum_apply]; rw [sum_apply]; rw [_root_.map_sum]
  simp only [coe_proj, mapQ_apply, mkQ_apply, comp_apply]

@[simp]
/--
theorem `piQuotientLift_single` / 定理 `piQuotientLift_single`

English:
theorem piQuotientLift_single
  statement: [Fintype ι] [DecidableEq ι] (p : forall i, Submodule R (Ms i))
  proof: by
  simp_rw [piQuotientLift, lsum_apply, sum_apply, comp_apply, proj_apply]
  rw [Finset.sum_eq_single i]
  · rw [Pi.single_eq_same]
  · rintro j - hj
    rw [Pi.single_eq_of_ne hj]; rw [map_zero]
  · intros
    have := Finset.mem_univ i
    contradiction

中文:
定理 piQuotientLift_single
  结论: [有限类型 ι] [DecidableEq ι] (p : 对任意 i, 子模 R (Ms i))
  证明: by
  simp_rw [piQuotientLift, lsum_apply, sum_apply, comp_apply, proj_apply]
  rw [Finset.sum_eq_single i]
  · rw [Pi.single_eq_same]
  · rintro j - hj
    rw [Pi.single_eq_of_ne hj]; rw [map_zero]
  · intros
    have := Finset.mem_univ i
    contradiction

Depends on / 依赖: Finset, Finset.mem_univ, Finset.sum_eq_single, Pi.single_eq_of_ne, Pi.single_eq_same, comp_apply, intros, lsum_apply, map_zero, mem_univ, piQuotientLift, proj_apply, simp_rw, single_eq_of_ne, single_eq_same, sum_apply, sum_eq_single
-/
theorem piQuotientLift_single [Fintype ι] [DecidableEq ι] (p : forall i, Submodule R (Ms i))
    (q : Submodule R N) (f : forall i, Ms i ->ₗ[R] N) (hf : forall i, p i <= q.comap (f i)) (i)
    (x : Ms i ⧸ p i) : piQuotientLift p q f hf (Pi.single i x) = mapQ _ _ (f i) (hf i) x := by
  simp_rw [piQuotientLift, lsum_apply, sum_apply, comp_apply, proj_apply]
  rw [Finset.sum_eq_single i]
  · rw [Pi.single_eq_same]
  · rintro j - hj
    rw [Pi.single_eq_of_ne hj]; rw [map_zero]
  · intros
    have := Finset.mem_univ i
    contradiction

/--
Definition of `quotientPiLift` / `quotientPiLift` 的定义

English:
definition quotientPiLift
  signature: (p : forall i, Submodule R (Ms i)) (f : forall i, Ms i ->ₗ[R] Ns i)
  body: (pi Set.univ p).liftQ (LinearMap.pi fun i => (f i).comp (proj i)) fun x hx =>
mem_ker.mpr by
      ext i
      simpa using hf i (mem_pi.mp hx i (Set.mem_univ i))

@[simp]

中文:
定义 quotientPiLift
  签名: (p : 对任意 i, 子模 R (Ms i)) (f : 对任意 i, Ms i ->ₗ[R] Ns i)
  定义体: (pi Set.univ p).liftQ (LinearMap.pi fun i => (f i).comp (proj i)) fun x hx =>
mem_ker.mpr by
      ext i
      simpa using hf i (mem_pi.mp hx i (Set.mem_univ i))

@[simp]

Depends on / 依赖: LinearMap, LinearMap.pi, Set.mem_univ, Set.univ, mem_ker, mem_ker.mpr, mem_pi, mem_pi.mp, mem_univ
-/
def quotientPiLift (p : forall i, Submodule R (Ms i)) (f : forall i, Ms i ->ₗ[R] Ns i)
    (hf : forall i, p i <= ker (f i)) : (forall i, Ms i) ⧸ pi Set.univ p ->ₗ[R] forall i, Ns i :=
  (pi Set.univ p).liftQ (LinearMap.pi fun i => (f i).comp (proj i)) fun x hx =>
mem_ker.mpr by
      ext i
      simpa using hf i (mem_pi.mp hx i (Set.mem_univ i))

@[simp]
/--
theorem `quotientPiLift_mk` / 定理 `quotientPiLift_mk`

English:
theorem quotientPiLift_mk
  statement: (p : forall i, Submodule R (Ms i)) (f : forall i, Ms i ->ₗ[R] Ns i)
  proof: rfl

中文:
定理 quotientPiLift_mk
  结论: (p : 对任意 i, 子模 R (Ms i)) (f : 对任意 i, Ms i ->ₗ[R] Ns i)
  证明: rfl
-/
theorem quotientPiLift_mk (p : forall i, Submodule R (Ms i)) (f : forall i, Ms i ->ₗ[R] Ns i)
    (hf : forall i, p i <= ker (f i)) (x : forall i, Ms i) :
    quotientPiLift p f hf (Quotient.mk x) = fun i => f i (x i) :=
  rfl

namespace quotientPi_aux

variable (p : forall i, Submodule R (Ms i))

@[simp]
/--
Definition of `toFun` / `toFun` 的定义

English:
definition toFun
  signature: : ((forall i, Ms i) ⧸ pi Set.univ p) -> forall i, Ms i ⧸ p i
  body: quotientPiLift p (fun i => (p i).mkQ) fun i => (ker_mkQ (p i)).ge

中文:
定义 toFun
  签名: : ((对任意 i, Ms i) ⧸ pi 集合.univ p) -> 对任意 i, Ms i ⧸ p i
  定义体: quotientPiLift p (fun i => (p i).mkQ) fun i => (ker_mkQ (p i)).ge

Depends on / 依赖: ker_mkQ, quotientPiLift
-/
def toFun : ((forall i, Ms i) ⧸ pi Set.univ p) -> forall i, Ms i ⧸ p i :=
  quotientPiLift p (fun i => (p i).mkQ) fun i => (ker_mkQ (p i)).ge

/--
theorem `map_add` / 定理 `map_add`

English:
theorem map_add
  given: (x y : ((i : ι) -> Ms i) ⧸ pi Set.univ p)
  proof: LinearMap.map_add (quotientPiLift p (fun i => (p i).mkQ) fun i => (ker_mkQ (p i)).ge) x y

中文:
定理 map_add
  条件: (x y : ((i : ι) -> Ms i) ⧸ pi 集合.univ p)
  证明: LinearMap.map_add (quotientPiLift p (fun i => (p i).mkQ) fun i => (ker_mkQ (p i)).ge) x y

Depends on / 依赖: LinearMap, LinearMap.map_add, ker_mkQ, map_add, quotientPiLift
-/
theorem map_add (x y : ((i : ι) -> Ms i) ⧸ pi Set.univ p) :
    toFun p (x + y) = toFun p x + toFun p y :=
  LinearMap.map_add (quotientPiLift p (fun i => (p i).mkQ) fun i => (ker_mkQ (p i)).ge) x y

/--
theorem `map_smul` / 定理 `map_smul`

English:
theorem map_smul
  given: (r : R) (x : ((i : ι) -> Ms i) ⧸ pi Set.univ p)
  proof: LinearMap.map_smul (quotientPiLift p (fun i => (p i).mkQ) fun i => (ker_mkQ (p i)).ge) r x

中文:
定理 map_smul
  条件: (r : R) (x : ((i : ι) -> Ms i) ⧸ pi 集合.univ p)
  证明: LinearMap.map_smul (quotientPiLift p (fun i => (p i).mkQ) fun i => (ker_mkQ (p i)).ge) r x

Depends on / 依赖: LinearMap, LinearMap.map_smul, ker_mkQ, map_smul, quotientPiLift
-/
theorem map_smul (r : R) (x : ((i : ι) -> Ms i) ⧸ pi Set.univ p) :
    toFun p (r • x) = (RingHom.id R r) • toFun p x :=
  LinearMap.map_smul (quotientPiLift p (fun i => (p i).mkQ) fun i => (ker_mkQ (p i)).ge) r x

variable [Fintype ι] [DecidableEq ι]

@[simp]
/--
Definition of `invFun` / `invFun` 的定义

English:
definition invFun
  signature: : (forall i, Ms i ⧸ p i) -> (forall i, Ms i) ⧸ pi Set.univ p
  body: piQuotientLift p (pi Set.univ p) _ fun _ => le_comap_single_pi p

中文:
定义 invFun
  签名: : (对任意 i, Ms i ⧸ p i) -> (对任意 i, Ms i) ⧸ pi 集合.univ p
  定义体: piQuotientLift p (pi Set.univ p) _ fun _ => le_comap_single_pi p

Depends on / 依赖: Set.univ, le_comap_single_pi, piQuotientLift
-/
def invFun : (forall i, Ms i ⧸ p i) -> (forall i, Ms i) ⧸ pi Set.univ p :=
  piQuotientLift p (pi Set.univ p) _ fun _ => le_comap_single_pi p

/--
theorem `left_inv` / 定理 `left_inv`

English:
theorem left_inv
  statement: Function.LeftInverse (invFun p) (toFun p)
  proof: fun x =>
  Submodule.Quotient.induction_on _ x fun x' => by
    dsimp only [toFun, invFun]
    rw [quotientPiLift_mk p]; rw [funext fun i => (mkQ_apply (p i) (x' i))]; rw [piQuotientLift_mk p]; rw [lsum_single]; rw [id_apply]

中文:
定理 left_inv
  结论: 函数.左逆 (invFun p) (toFun p)
  证明: fun x =>
  Submodule.Quotient.induction_on _ x fun x' => by
    dsimp only [toFun, invFun]
    rw [quotientPiLift_mk p]; rw [funext fun i => (mkQ_apply (p i) (x' i))]; rw [piQuotientLift_mk p]; rw [lsum_single]; rw [id_apply]
-/
theorem left_inv : Function.LeftInverse (invFun p) (toFun p) := fun x =>
  Submodule.Quotient.induction_on _ x fun x' => by
    dsimp only [toFun, invFun]
    rw [quotientPiLift_mk p]; rw [funext fun i => (mkQ_apply (p i) (x' i))]; rw [piQuotientLift_mk p]; rw [lsum_single]; rw [id_apply]

/--
theorem `right_inv` / 定理 `right_inv`

English:
theorem right_inv
  statement: Function.RightInverse (invFun p) (toFun p)
  proof: by
  dsimp only [toFun, invFun]
  rw [Function.rightInverse_iff_comp]; rw [← coe_comp]; rw [← @id_coe R]
  congr
  refine pi_ext fun i x => ?_
  induction x using Submodule.Quotient.induction_on with | _ x'
  refine funext fun j => ?_
  rw [comp_apply]; rw [piQuotientLift_single]; rw [mapQ_apply]; r

中文:
定理 right_inv
  结论: 函数.右逆 (invFun p) (toFun p)
  证明: by
  dsimp only [toFun, invFun]
  rw [Function.rightInverse_iff_comp]; rw [← coe_comp]; rw [← @id_coe R]
  congr
  refine pi_ext fun i x => ?_
  induction x using Submodule.Quotient.induction_on with | _ x'
  refine funext fun j => ?_
  rw [comp_apply]; rw [piQuotientLift_single]; rw [mapQ_apply]; r

Depends on / 依赖: Function, Function.rightInverse_iff_comp, Ne.symm, Pi.single_eq_of_ne, Pi.single_eq_same, Quotient, Submodule, Submodule.Quotient.induction_on, coe_comp, coe_single, comp_apply, id_apply, id_coe, induction_on, invFun, mapQ_apply, mkQ_apply, piQuotientLift_single, pi_ext, quotientPiLift_mk
-/
theorem right_inv : Function.RightInverse (invFun p) (toFun p) := by
  dsimp only [toFun, invFun]
  rw [Function.rightInverse_iff_comp]; rw [← coe_comp]; rw [← @id_coe R]
  congr
  refine pi_ext fun i x => ?_
  induction x using Submodule.Quotient.induction_on with | _ x'
  refine funext fun j => ?_
  rw [comp_apply]; rw [piQuotientLift_single]; rw [mapQ_apply]; rw [quotientPiLift_mk]; rw [id_apply]
  by_cases hij : i = j <;> simp only [mkQ_apply, coe_single]
  · subst hij
    rw [Pi.single_eq_same]; rw [Pi.single_eq_same]
  · rw [Pi.single_eq_of_ne (Ne.symm hij), Pi.single_eq_of_ne (Ne.symm hij), Quotient.mk_zero]

end quotientPi_aux

open quotientPi_aux in
/-- The quotient of a direct sum is the direct sum of quotients. -/
@[simps!]
/--
Definition of `quotientPi` / `quotientPi` 的定义

English:
definition quotientPi
  signature: [Fintype ι] [DecidableEq ι] (p : forall i, Submodule R (Ms i))
  body: toFun p
  invFun := invFun p
  map_add' := map_add p
  map_smul' := quotientPi_aux.map_smul p
  left_inv := left_inv p
  right_inv := right_inv p

中文:
定义 quotientPi
  签名: [有限类型 ι] [DecidableEq ι] (p : 对任意 i, 子模 R (Ms i))
  定义体: toFun p
  invFun := invFun p
  map_add' := map_add p
  map_smul' := quotientPi_aux.map_smul p
  left_inv := left_inv p
  right_inv := right_inv p
-/
def quotientPi [Fintype ι] [DecidableEq ι] (p : forall i, Submodule R (Ms i)) :
    ((forall i, Ms i) ⧸ pi Set.univ p) ≃ₗ[R] forall i, Ms i ⧸ p i where
  toFun := toFun p
  invFun := invFun p
  map_add' := map_add p
  map_smul' := quotientPi_aux.map_smul p
  left_inv := left_inv p
  right_inv := right_inv p

end Submodule
