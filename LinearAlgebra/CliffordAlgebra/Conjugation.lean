/-
Copyright (c) 2020 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser
-/
module

public import Mathlib.LinearAlgebra.CliffordAlgebra.Grading
public import Mathlib.Algebra.Module.Opposite

/-!
# Conjugations

This file defines the grade reversal and grade involution functions on multivectors, `reverse` and
`involute`.
Together, these operations compose to form the "Clifford conjugate", hence the name of this file.

https://en.wikipedia.org/wiki/Clifford_algebra#Antiautomorphisms

## Main definitions

* `CliffordAlgebra.involute`: the grade involution, negating each basis vector
* `CliffordAlgebra.reverse`: the grade reversion, reversing the order of a product of vectors

## Main statements

* `CliffordAlgebra.involute_involutive`
* `CliffordAlgebra.reverse_involutive`
* `CliffordAlgebra.reverse_involute_commute`
* `CliffordAlgebra.involute_mem_evenOdd_iff`
* `CliffordAlgebra.reverse_mem_evenOdd_iff`

-/

@[expose] public section


variable {R : Type*} [CommRing R]
variable {M : Type*} [AddCommGroup M] [Module R M]
variable {Q : QuadraticForm R M}

namespace CliffordAlgebra

section Involute

/--
Definition of `involute` / `involute` 的定义

English:
definition involute
  signature: : CliffordAlgebra Q ->ₐ[R] CliffordAlgebra Q
  body: CliffordAlgebra.lift Q ⟨-ι Q, fun m => by simp⟩

@[simp]

中文:
定义 involute
  签名: : CliffordAlgebra Q ->ₐ[R] CliffordAlgebra Q
  定义体: CliffordAlgebra.lift Q ⟨-ι Q, fun m => by simp⟩

@[simp]

Depends on / 依赖: CliffordAlgebra, CliffordAlgebra.lift
-/
def involute : CliffordAlgebra Q ->ₐ[R] CliffordAlgebra Q :=
  CliffordAlgebra.lift Q ⟨-ι Q, fun m => by simp⟩

@[simp]
/--
theorem `involute_ι` / 定理 `involute_ι`

English:
theorem involute_ι
  given: (m : M)
  statement: involute (ι Q m) = -ι Q m
  proof: lift_ι_apply _ _ m

@[simp]

中文:
定理 involute_ι
  条件: (m : M)
  结论: involute (ι Q m) = -ι Q m
  证明: lift_ι_apply _ _ m

@[simp]
-/
theorem involute_ι (m : M) : involute (ι Q m) = -ι Q m :=
  lift_ι_apply _ _ m

@[simp]
/--
theorem `involute_comp_involute` / 定理 `involute_comp_involute`

English:
theorem involute_comp_involute
  statement: involute.comp involute = AlgHom.id R (CliffordAlgebra Q)
  proof: by
  ext; simp

中文:
定理 involute_comp_involute
  结论: involute.comp involute = 代数态射.id R (CliffordAlgebra Q)
  证明: by
  ext; simp
-/
theorem involute_comp_involute : involute.comp involute = AlgHom.id R (CliffordAlgebra Q) := by
  ext; simp

/--
theorem `involute_involutive` / 定理 `involute_involutive`

English:
theorem involute_involutive
  statement: Function.Involutive (involute : _ -> CliffordAlgebra Q)
  proof: AlgHom.congr_fun involute_comp_involute

@[simp]

中文:
定理 involute_involutive
  结论: 函数.对合 (involute : _ -> CliffordAlgebra Q)
  证明: AlgHom.congr_fun involute_comp_involute

@[simp]

Depends on / 依赖: AlgHom, AlgHom.congr_fun, congr_fun, involute_comp_involute
-/
theorem involute_involutive : Function.Involutive (involute : _ -> CliffordAlgebra Q) :=
  AlgHom.congr_fun involute_comp_involute

@[simp]
/--
theorem `involute_involute` / 定理 `involute_involute`

English:
theorem involute_involute
  statement: forall a : CliffordAlgebra Q, involute (involute a) = a
  proof: involute_involutive

中文:
定理 involute_involute
  结论: 对任意 a : CliffordAlgebra Q, involute (involute a) = a
  证明: involute_involutive

Depends on / 依赖: involute_involutive
-/
theorem involute_involute : forall a : CliffordAlgebra Q, involute (involute a) = a :=
  involute_involutive

/-- `CliffordAlgebra.involute` as an `AlgEquiv`. -/
@[simps!]
/--
Definition of `involuteEquiv` / `involuteEquiv` 的定义

English:
definition involuteEquiv
  signature: : CliffordAlgebra Q ≃ₐ[R] CliffordAlgebra Q
  body: AlgEquiv.ofAlgHom involute involute (AlgHom.ext <| involute_involute)
    (AlgHom.ext <| involute_involute)

中文:
定义 involuteEquiv
  签名: : CliffordAlgebra Q ≃ₐ[R] CliffordAlgebra Q
  定义体: AlgEquiv.ofAlgHom involute involute (AlgHom.ext <| involute_involute)
    (AlgHom.ext <| involute_involute)

Depends on / 依赖: AlgEquiv, AlgEquiv.ofAlgHom, AlgHom, AlgHom.ext, involute, involute_involute, ofAlgHom
-/
def involuteEquiv : CliffordAlgebra Q ≃ₐ[R] CliffordAlgebra Q :=
  AlgEquiv.ofAlgHom involute involute (AlgHom.ext <| involute_involute)
    (AlgHom.ext <| involute_involute)

end Involute

section Reverse

open MulOpposite

/--
Definition of `reverseOp` / `reverseOp` 的定义

English:
definition reverseOp
  signature: : CliffordAlgebra Q ->ₐ[R] (CliffordAlgebra Q)ᵐᵒᵖ
  body: CliffordAlgebra.lift Q
⟨(MulOpposite.opLinearEquiv R).toLinearMap ∘ₗ ι Q, fun m => unop_injective by simp⟩

@[simp]

中文:
定义 reverseOp
  签名: : CliffordAlgebra Q ->ₐ[R] (CliffordAlgebra Q)ᵐᵒᵖ
  定义体: CliffordAlgebra.lift Q
⟨(MulOpposite.opLinearEquiv R).toLinearMap ∘ₗ ι Q, fun m => unop_injective by simp⟩

@[simp]

Depends on / 依赖: CliffordAlgebra, CliffordAlgebra.lift, MulOpposite, MulOpposite.opLinearEquiv, opLinearEquiv, toLinearMap, unop_injective
-/
def reverseOp : CliffordAlgebra Q ->ₐ[R] (CliffordAlgebra Q)ᵐᵒᵖ :=
  CliffordAlgebra.lift Q
⟨(MulOpposite.opLinearEquiv R).toLinearMap ∘ₗ ι Q, fun m => unop_injective by simp⟩

@[simp]
/--
theorem `reverseOp_ι` / 定理 `reverseOp_ι`

English:
theorem reverseOp_ι
  given: (m : M)
  statement: reverseOp (ι Q m) = op (ι Q m)
  proof: lift_ι_apply _ _ _

中文:
定理 reverseOp_ι
  条件: (m : M)
  结论: reverseOp (ι Q m) = op (ι Q m)
  证明: lift_ι_apply _ _ _
-/
theorem reverseOp_ι (m : M) : reverseOp (ι Q m) = op (ι Q m) := lift_ι_apply _ _ _

/-- `CliffordAlgebra.reverseEquiv` as an `AlgEquiv` to the opposite algebra -/
@[simps! apply]
/--
Definition of `reverseOpEquiv` / `reverseOpEquiv` 的定义

English:
definition reverseOpEquiv
  signature: : CliffordAlgebra Q ≃ₐ[R] (CliffordAlgebra Q)ᵐᵒᵖ
  body: AlgEquiv.ofAlgHom reverseOp (AlgHom.opComm reverseOp)
    (AlgHom.unop.injective <| hom_ext <| LinearMap.ext fun _ => by simp)
    (hom_ext <| LinearMap.ext fun _ => by simp)

@[simp]

中文:
定义 reverseOpEquiv
  签名: : CliffordAlgebra Q ≃ₐ[R] (CliffordAlgebra Q)ᵐᵒᵖ
  定义体: AlgEquiv.ofAlgHom reverseOp (AlgHom.opComm reverseOp)
    (AlgHom.unop.injective <| hom_ext <| LinearMap.ext fun _ => by simp)
    (hom_ext <| LinearMap.ext fun _ => by simp)

@[simp]

Depends on / 依赖: AlgEquiv, AlgEquiv.ofAlgHom, AlgHom, AlgHom.opComm, AlgHom.unop.injective, LinearMap, LinearMap.ext, hom_ext, injective, ofAlgHom, opComm, reverseOp
-/
def reverseOpEquiv : CliffordAlgebra Q ≃ₐ[R] (CliffordAlgebra Q)ᵐᵒᵖ :=
  AlgEquiv.ofAlgHom reverseOp (AlgHom.opComm reverseOp)
    (AlgHom.unop.injective <| hom_ext <| LinearMap.ext fun _ => by simp)
    (hom_ext <| LinearMap.ext fun _ => by simp)

@[simp]
/--
theorem `reverseOpEquiv_opComm` / 定理 `reverseOpEquiv_opComm`

English:
theorem reverseOpEquiv_opComm
  proof: rfl

中文:
定理 reverseOpEquiv_opComm
  证明: rfl

Depends on / 依赖: reverseOpEquiv, reverseOpEquiv.symm
-/
theorem reverseOpEquiv_opComm :
    AlgEquiv.opComm (reverseOpEquiv (Q := Q)) = reverseOpEquiv.symm := rfl

/--
Definition of `reverse` / `reverse` 的定义

English:
definition reverse
  signature: : CliffordAlgebra Q ->ₗ[R] CliffordAlgebra Q
  body: (opLinearEquiv R).symm.toLinearMap.comp reverseOp.toLinearMap

中文:
定义 reverse
  签名: : CliffordAlgebra Q ->ₗ[R] CliffordAlgebra Q
  定义体: (opLinearEquiv R).symm.toLinearMap.comp reverseOp.toLinearMap

Depends on / 依赖: opLinearEquiv, reverseOp, reverseOp.toLinearMap, symm.toLinearMap.comp, toLinearMap
-/
def reverse : CliffordAlgebra Q ->ₗ[R] CliffordAlgebra Q :=
  (opLinearEquiv R).symm.toLinearMap.comp reverseOp.toLinearMap

/--
theorem `unop_reverseOp` / 定理 `unop_reverseOp`

English:
theorem unop_reverseOp
  given: (x : CliffordAlgebra Q)
  statement: (reverseOp x).unop = reverse x
  proof: rfl

中文:
定理 unop_reverseOp
  条件: (x : CliffordAlgebra Q)
  结论: (reverseOp x).unop = reverse x
  证明: rfl
-/
@[simp] theorem unop_reverseOp (x : CliffordAlgebra Q) : (reverseOp x).unop = reverse x := rfl

/--
theorem `op_reverse` / 定理 `op_reverse`

English:
theorem op_reverse
  given: (x : CliffordAlgebra Q)
  statement: op (reverse x) = reverseOp x
  proof: rfl

@[simp]

中文:
定理 op_reverse
  条件: (x : CliffordAlgebra Q)
  结论: op (reverse x) = reverseOp x
  证明: rfl

@[simp]
-/
@[simp] theorem op_reverse (x : CliffordAlgebra Q) : op (reverse x) = reverseOp x := rfl

@[simp]
/--
theorem `reverse_ι` / 定理 `reverse_ι`

English:
theorem reverse_ι
  given: (m : M)
  statement: reverse (ι Q m) = ι Q m
  proof: by simp [reverse]

@[simp]

中文:
定理 reverse_ι
  条件: (m : M)
  结论: reverse (ι Q m) = ι Q m
  证明: by simp [reverse]

@[simp]

Depends on / 依赖: reverse
-/
theorem reverse_ι (m : M) : reverse (ι Q m) = ι Q m := by simp [reverse]

@[simp]
/--
theorem `reverse.commutes` / 定理 `reverse.commutes`

English:
theorem reverse.commutes
  given: (r : R)
  proof: op_injective reverseOp.commutes r

@[simp]

中文:
定理 reverse.commutes
  条件: (r : R)
  证明: op_injective reverseOp.commutes r

@[simp]

Depends on / 依赖: commutes, op_injective, reverseOp, reverseOp.commutes
-/
theorem reverse.commutes (r : R) :
    reverse (algebraMap R (CliffordAlgebra Q) r) = algebraMap R _ r :=
op_injective reverseOp.commutes r

@[simp]
/--
theorem `reverse.map_one` / 定理 `reverse.map_one`

English:
theorem reverse.map_one
  statement: reverse (1 : CliffordAlgebra Q) = 1
  proof: op_injective (map_one reverseOp)

@[simp]

中文:
定理 reverse.map_one
  结论: reverse (1 : CliffordAlgebra Q) = 1
  证明: op_injective (map_one reverseOp)

@[simp]
-/
protected theorem reverse.map_one : reverse (1 : CliffordAlgebra Q) = 1 :=
  op_injective (map_one reverseOp)

@[simp]
/--
theorem `reverse.map_mul` / 定理 `reverse.map_mul`

English:
theorem reverse.map_mul
  given: (a b : CliffordAlgebra Q)
  proof: op_injective (map_mul reverseOp a b)

@[simp]

中文:
定理 reverse.map_mul
  条件: (a b : CliffordAlgebra Q)
  证明: op_injective (map_mul reverseOp a b)

@[simp]
-/
protected theorem reverse.map_mul (a b : CliffordAlgebra Q) :
    reverse (a * b) = reverse b * reverse a :=
  op_injective (map_mul reverseOp a b)

@[simp]
/--
theorem `reverse_involutive` / 定理 `reverse_involutive`

English:
theorem reverse_involutive
  statement: Function.Involutive (reverse (Q := Q))
  proof: AlgHom.congr_fun reverseOpEquiv.symm_comp

@[simp]

中文:
定理 reverse_involutive
  结论: 函数.对合 (reverse (Q := Q))
  证明: AlgHom.congr_fun reverseOpEquiv.symm_comp

@[simp]
-/
theorem reverse_involutive : Function.Involutive (reverse (Q := Q)) :=
  AlgHom.congr_fun reverseOpEquiv.symm_comp

@[simp]
/--
theorem `reverse_comp_reverse` / 定理 `reverse_comp_reverse`

English:
theorem reverse_comp_reverse
  proof: LinearMap.ext reverse_involutive

@[simp]

中文:
定理 reverse_comp_reverse
  证明: LinearMap.ext reverse_involutive

@[simp]

Depends on / 依赖: LinearMap, LinearMap.ext, reverse_involutive
-/
theorem reverse_comp_reverse :
    reverse.comp reverse = (LinearMap.id : _ ->ₗ[R] CliffordAlgebra Q) :=
  LinearMap.ext reverse_involutive

@[simp]
/--
theorem `reverse_reverse` / 定理 `reverse_reverse`

English:
theorem reverse_reverse
  statement: forall a : CliffordAlgebra Q, reverse (reverse a) = a
  proof: reverse_involutive

中文:
定理 reverse_reverse
  结论: 对任意 a : CliffordAlgebra Q, reverse (reverse a) = a
  证明: reverse_involutive

Depends on / 依赖: reverse_involutive
-/
theorem reverse_reverse : forall a : CliffordAlgebra Q, reverse (reverse a) = a :=
  reverse_involutive

/-- `CliffordAlgebra.reverse` as a `LinearEquiv`. -/
@[simps!]
/--
Definition of `reverseEquiv` / `reverseEquiv` 的定义

English:
definition reverseEquiv
  signature: : CliffordAlgebra Q ≃ₗ[R] CliffordAlgebra Q
  body: LinearEquiv.ofInvolutive reverse reverse_involutive

中文:
定义 reverseEquiv
  签名: : CliffordAlgebra Q ≃ₗ[R] CliffordAlgebra Q
  定义体: LinearEquiv.ofInvolutive reverse reverse_involutive

Depends on / 依赖: LinearEquiv, LinearEquiv.ofInvolutive, ofInvolutive, reverse, reverse_involutive
-/
def reverseEquiv : CliffordAlgebra Q ≃ₗ[R] CliffordAlgebra Q :=
  LinearEquiv.ofInvolutive reverse reverse_involutive

/--
theorem `reverse_comp_involute` / 定理 `reverse_comp_involute`

English:
theorem reverse_comp_involute
  proof: by
  ext x
  simp only [LinearMap.comp_apply, AlgHom.toLinearMap_apply]
  induction x using CliffordAlgebra.induction with
  | algebraMap => simp
  | ι => simp
  | mul a b ha hb => simp only [ha, hb, reverse.map_mul, map_mul]
  | add a b ha hb => simp only [ha, hb, reverse.map_add, map_add]

中文:
定理 reverse_comp_involute
  证明: by
  ext x
  simp only [LinearMap.comp_apply, AlgHom.toLinearMap_apply]
  induction x using CliffordAlgebra.induction with
  | algebraMap => simp
  | ι => simp
  | mul a b ha hb => simp only [ha, hb, reverse.map_mul, map_mul]
  | add a b ha hb => simp only [ha, hb, reverse.map_add, map_add]

Depends on / 依赖: AlgHom, AlgHom.toLinearMap_apply, CliffordAlgebra, CliffordAlgebra.induction, LinearMap, LinearMap.comp_apply, algebraMap, comp_apply, map_add, map_mul, reverse, reverse.map_add, reverse.map_mul, toLinearMap_apply
-/
theorem reverse_comp_involute :
    reverse.comp involute.toLinearMap =
      (involute.toLinearMap.comp reverse : _ ->ₗ[R] CliffordAlgebra Q) := by
  ext x
  simp only [LinearMap.comp_apply, AlgHom.toLinearMap_apply]
  induction x using CliffordAlgebra.induction with
  | algebraMap => simp
  | ι => simp
  | mul a b ha hb => simp only [ha, hb, reverse.map_mul, map_mul]
  | add a b ha hb => simp only [ha, hb, reverse.map_add, map_add]

/--
theorem `reverse_involute_commute` / 定理 `reverse_involute_commute`

English:
theorem reverse_involute_commute
  statement: Function.Commute (reverse (Q := Q)) involute
  proof: LinearMap.congr_fun reverse_comp_involute

中文:
定理 reverse_involute_commute
  结论: 函数.Commute (reverse (Q := Q)) involute
  证明: LinearMap.congr_fun reverse_comp_involute

Depends on / 依赖: involute
-/
theorem reverse_involute_commute : Function.Commute (reverse (Q := Q)) involute :=
  LinearMap.congr_fun reverse_comp_involute

/--
theorem `reverse_involute` / 定理 `reverse_involute`

English:
theorem reverse_involute
  proof: reverse_involute_commute

中文:
定理 reverse_involute
  证明: reverse_involute_commute

Depends on / 依赖: reverse_involute_commute
-/
theorem reverse_involute :
    forall a : CliffordAlgebra Q, reverse (involute a) = involute (reverse a) :=
  reverse_involute_commute

end Reverse

/-!
### Statements about conjugations of products of lists
-/


section List

/--
theorem `reverse_prod_map_ι` / 定理 `reverse_prod_map_ι`

English:
theorem reverse_prod_map_ι

中文:
定理 reverse_prod_map_ι
-/
theorem reverse_prod_map_ι :
    forall l : List M, reverse (l.map <| ι Q).prod = (l.map <| ι Q).reverse.prod
  | [] => by simp
  | x::xs => by simp [reverse_prod_map_ι xs]

/--
theorem `involute_prod_map_ι` / 定理 `involute_prod_map_ι`

English:
theorem involute_prod_map_ι

中文:
定理 involute_prod_map_ι
-/
theorem involute_prod_map_ι :
    forall l : List M, involute (l.map <| ι Q).prod = (-1 : R) ^ l.length • (l.map <| ι Q).prod
  | [] => by simp
  | x::xs => by simp [pow_succ, involute_prod_map_ι xs]

end List

/-!
### Statements about `Submodule.map` and `Submodule.comap`
-/


section Submodule

variable (Q)

section Involute

/--
theorem `submodule_map_involute_eq_comap` / 定理 `submodule_map_involute_eq_comap`

English:
theorem submodule_map_involute_eq_comap
  given: (p : Submodule R (CliffordAlgebra Q))
  proof: Submodule.map_equiv_eq_comap_symm involuteEquiv.toLinearEquiv _

@[simp]

中文:
定理 submodule_map_involute_eq_comap
  条件: (p : 子模 R (CliffordAlgebra Q))
  证明: Submodule.map_equiv_eq_comap_symm involuteEquiv.toLinearEquiv _

@[simp]

Depends on / 依赖: Submodule, Submodule.map_equiv_eq_comap_symm, involuteEquiv, involuteEquiv.toLinearEquiv, map_equiv_eq_comap_symm, toLinearEquiv
-/
theorem submodule_map_involute_eq_comap (p : Submodule R (CliffordAlgebra Q)) :
    p.map (involute : CliffordAlgebra Q ->ₐ[R] CliffordAlgebra Q).toLinearMap =
      p.comap (involute : CliffordAlgebra Q ->ₐ[R] CliffordAlgebra Q).toLinearMap :=
  Submodule.map_equiv_eq_comap_symm involuteEquiv.toLinearEquiv _

@[simp]
/--
theorem `ι_range_map_involute` / 定理 `ι_range_map_involute`

English:
theorem ι_range_map_involute
  proof: (ι_range_map_lift _ _).trans (LinearMap.range_neg _)

@[simp]

中文:
定理 ι_range_map_involute
  证明: (ι_range_map_lift _ _).trans (LinearMap.range_neg _)

@[simp]

Depends on / 依赖: LinearMap, LinearMap.range_neg, range_neg
-/
theorem ι_range_map_involute :
    (LinearMap.range (ι Q)).map (involute : CliffordAlgebra Q ->ₐ[R] CliffordAlgebra Q).toLinearMap =
      LinearMap.range (ι Q) :=
  (ι_range_map_lift _ _).trans (LinearMap.range_neg _)

@[simp]
/--
theorem `ι_range_comap_involute` / 定理 `ι_range_comap_involute`

English:
theorem ι_range_comap_involute
  proof: by
  rw [← submodule_map_involute_eq_comap]; rw [ι_range_map_involute]

@[simp]

中文:
定理 ι_range_comap_involute
  证明: by
  rw [← submodule_map_involute_eq_comap]; rw [ι_range_map_involute]

@[simp]

Depends on / 依赖: submodule_map_involute_eq_comap
-/
theorem ι_range_comap_involute :
    (LinearMap.range (ι Q)).comap
      (involute : CliffordAlgebra Q ->ₐ[R] CliffordAlgebra Q).toLinearMap =
      LinearMap.range (ι Q) := by
  rw [← submodule_map_involute_eq_comap]; rw [ι_range_map_involute]

@[simp]
/--
theorem `evenOdd_map_involute` / 定理 `evenOdd_map_involute`

English:
theorem evenOdd_map_involute
  given: (n : ZMod 2)
  proof: by
  simp_rw [evenOdd, Submodule.map_iSup, Submodule.map_pow, ι_range_map_involute]

@[simp]

中文:
定理 evenOdd_map_involute
  条件: (n : ZMod 2)
  证明: by
  simp_rw [evenOdd, Submodule.map_iSup, Submodule.map_pow, ι_range_map_involute]

@[simp]

Depends on / 依赖: Submodule, Submodule.map_iSup, Submodule.map_pow, evenOdd, map_iSup, map_pow, simp_rw
-/
theorem evenOdd_map_involute (n : ZMod 2) :
    (evenOdd Q n).map (involute : CliffordAlgebra Q ->ₐ[R] CliffordAlgebra Q).toLinearMap =
      evenOdd Q n := by
  simp_rw [evenOdd, Submodule.map_iSup, Submodule.map_pow, ι_range_map_involute]

@[simp]
/--
theorem `evenOdd_comap_involute` / 定理 `evenOdd_comap_involute`

English:
theorem evenOdd_comap_involute
  given: (n : ZMod 2)
  proof: by
  rw [← submodule_map_involute_eq_comap]; rw [evenOdd_map_involute]

中文:
定理 evenOdd_comap_involute
  条件: (n : ZMod 2)
  证明: by
  rw [← submodule_map_involute_eq_comap]; rw [evenOdd_map_involute]

Depends on / 依赖: evenOdd_map_involute, submodule_map_involute_eq_comap
-/
theorem evenOdd_comap_involute (n : ZMod 2) :
    (evenOdd Q n).comap (involute : CliffordAlgebra Q ->ₐ[R] CliffordAlgebra Q).toLinearMap =
      evenOdd Q n := by
  rw [← submodule_map_involute_eq_comap]; rw [evenOdd_map_involute]

end Involute

section Reverse

/--
theorem `submodule_map_reverse_eq_comap` / 定理 `submodule_map_reverse_eq_comap`

English:
theorem submodule_map_reverse_eq_comap
  given: (p : Submodule R (CliffordAlgebra Q))
  proof: Submodule.map_equiv_eq_comap_symm (reverseEquiv : _ ≃ₗ[R] _) _

@[simp]

中文:
定理 submodule_map_reverse_eq_comap
  条件: (p : 子模 R (CliffordAlgebra Q))
  证明: Submodule.map_equiv_eq_comap_symm (reverseEquiv : _ ≃ₗ[R] _) _

@[simp]

Depends on / 依赖: Submodule, Submodule.map_equiv_eq_comap_symm, map_equiv_eq_comap_symm, reverseEquiv
-/
theorem submodule_map_reverse_eq_comap (p : Submodule R (CliffordAlgebra Q)) :
    p.map (reverse : CliffordAlgebra Q ->ₗ[R] CliffordAlgebra Q) =
      p.comap (reverse : CliffordAlgebra Q ->ₗ[R] CliffordAlgebra Q) :=
  Submodule.map_equiv_eq_comap_symm (reverseEquiv : _ ≃ₗ[R] _) _

@[simp]
/--
theorem `ι_range_map_reverse` / 定理 `ι_range_map_reverse`

English:
theorem ι_range_map_reverse
  proof: by
  rw [reverse]; rw [reverseOp]; rw [Submodule.map_comp]; rw [ι_range_map_lift]; rw [LinearMap.range_comp]; rw [← Submodule.map_comp]
  exact Submodule.map_id _

@[simp]

中文:
定理 ι_range_map_reverse
  证明: by
  rw [reverse]; rw [reverseOp]; rw [Submodule.map_comp]; rw [ι_range_map_lift]; rw [LinearMap.range_comp]; rw [← Submodule.map_comp]
  exact Submodule.map_id _

@[simp]

Depends on / 依赖: LinearMap, LinearMap.range_comp, Submodule, Submodule.map_comp, Submodule.map_id, map_comp, map_id, range_comp, reverse, reverseOp
-/
theorem ι_range_map_reverse :
    (LinearMap.range (ι Q)).map (reverse : CliffordAlgebra Q ->ₗ[R] CliffordAlgebra Q)
      = LinearMap.range (ι Q) := by
  rw [reverse]; rw [reverseOp]; rw [Submodule.map_comp]; rw [ι_range_map_lift]; rw [LinearMap.range_comp]; rw [← Submodule.map_comp]
  exact Submodule.map_id _

@[simp]
/--
theorem `ι_range_comap_reverse` / 定理 `ι_range_comap_reverse`

English:
theorem ι_range_comap_reverse
  proof: by
  rw [← submodule_map_reverse_eq_comap]; rw [ι_range_map_reverse]

中文:
定理 ι_range_comap_reverse
  证明: by
  rw [← submodule_map_reverse_eq_comap]; rw [ι_range_map_reverse]

Depends on / 依赖: submodule_map_reverse_eq_comap
-/
theorem ι_range_comap_reverse :
    (LinearMap.range (ι Q)).comap (reverse : CliffordAlgebra Q ->ₗ[R] CliffordAlgebra Q)
      = LinearMap.range (ι Q) := by
  rw [← submodule_map_reverse_eq_comap]; rw [ι_range_map_reverse]

/--
theorem `submodule_map_mul_reverse` / 定理 `submodule_map_mul_reverse`

English:
theorem submodule_map_mul_reverse
  given: (p q : Submodule R (CliffordAlgebra Q))
  proof: by
  simp_rw [reverse, Submodule.map_comp, Submodule.map_mul, Submodule.map_unop_mul]

中文:
定理 submodule_map_mul_reverse
  条件: (p q : 子模 R (CliffordAlgebra Q))
  证明: by
  simp_rw [reverse, Submodule.map_comp, Submodule.map_mul, Submodule.map_unop_mul]

Depends on / 依赖: Submodule, Submodule.map_comp, Submodule.map_mul, Submodule.map_unop_mul, map_comp, map_mul, map_unop_mul, reverse, simp_rw
-/
theorem submodule_map_mul_reverse (p q : Submodule R (CliffordAlgebra Q)) :
    (p * q).map (reverse : CliffordAlgebra Q ->ₗ[R] CliffordAlgebra Q) =
      q.map (reverse : CliffordAlgebra Q ->ₗ[R] CliffordAlgebra Q) *
        p.map (reverse : CliffordAlgebra Q ->ₗ[R] CliffordAlgebra Q) := by
  simp_rw [reverse, Submodule.map_comp, Submodule.map_mul, Submodule.map_unop_mul]

/--
theorem `submodule_comap_mul_reverse` / 定理 `submodule_comap_mul_reverse`

English:
theorem submodule_comap_mul_reverse
  given: (p q : Submodule R (CliffordAlgebra Q))
  proof: by
  simp_rw [← submodule_map_reverse_eq_comap, submodule_map_mul_reverse]

中文:
定理 submodule_comap_mul_reverse
  条件: (p q : 子模 R (CliffordAlgebra Q))
  证明: by
  simp_rw [← submodule_map_reverse_eq_comap, submodule_map_mul_reverse]

Depends on / 依赖: simp_rw, submodule_map_mul_reverse, submodule_map_reverse_eq_comap
-/
theorem submodule_comap_mul_reverse (p q : Submodule R (CliffordAlgebra Q)) :
    (p * q).comap (reverse : CliffordAlgebra Q ->ₗ[R] CliffordAlgebra Q) =
      q.comap (reverse : CliffordAlgebra Q ->ₗ[R] CliffordAlgebra Q) *
        p.comap (reverse : CliffordAlgebra Q ->ₗ[R] CliffordAlgebra Q) := by
  simp_rw [← submodule_map_reverse_eq_comap, submodule_map_mul_reverse]

/--
theorem `submodule_map_pow_reverse` / 定理 `submodule_map_pow_reverse`

English:
theorem submodule_map_pow_reverse
  given: (p : Submodule R (CliffordAlgebra Q)) (n : Nat)
  proof: by
  simp_rw [reverse, Submodule.map_comp, Submodule.map_pow, Submodule.map_unop_pow]

中文:
定理 submodule_map_pow_reverse
  条件: (p : 子模 R (CliffordAlgebra Q)) (n : 自然数)
  证明: by
  simp_rw [reverse, Submodule.map_comp, Submodule.map_pow, Submodule.map_unop_pow]

Depends on / 依赖: Submodule, Submodule.map_comp, Submodule.map_pow, Submodule.map_unop_pow, map_comp, map_pow, map_unop_pow, reverse, simp_rw
-/
theorem submodule_map_pow_reverse (p : Submodule R (CliffordAlgebra Q)) (n : Nat) :
    (p ^ n).map (reverse : CliffordAlgebra Q ->ₗ[R] CliffordAlgebra Q) =
      p.map (reverse : CliffordAlgebra Q ->ₗ[R] CliffordAlgebra Q) ^ n := by
  simp_rw [reverse, Submodule.map_comp, Submodule.map_pow, Submodule.map_unop_pow]

/--
theorem `submodule_comap_pow_reverse` / 定理 `submodule_comap_pow_reverse`

English:
theorem submodule_comap_pow_reverse
  given: (p : Submodule R (CliffordAlgebra Q)) (n : Nat)
  proof: by
  simp_rw [← submodule_map_reverse_eq_comap, submodule_map_pow_reverse]

@[simp]

中文:
定理 submodule_comap_pow_reverse
  条件: (p : 子模 R (CliffordAlgebra Q)) (n : 自然数)
  证明: by
  simp_rw [← submodule_map_reverse_eq_comap, submodule_map_pow_reverse]

@[simp]

Depends on / 依赖: simp_rw, submodule_map_pow_reverse, submodule_map_reverse_eq_comap
-/
theorem submodule_comap_pow_reverse (p : Submodule R (CliffordAlgebra Q)) (n : Nat) :
    (p ^ n).comap (reverse : CliffordAlgebra Q ->ₗ[R] CliffordAlgebra Q) =
      p.comap (reverse : CliffordAlgebra Q ->ₗ[R] CliffordAlgebra Q) ^ n := by
  simp_rw [← submodule_map_reverse_eq_comap, submodule_map_pow_reverse]

@[simp]
/--
theorem `evenOdd_map_reverse` / 定理 `evenOdd_map_reverse`

English:
theorem evenOdd_map_reverse
  given: (n : ZMod 2)
  proof: by
  simp_rw [evenOdd, Submodule.map_iSup, submodule_map_pow_reverse, ι_range_map_reverse]

@[simp]

中文:
定理 evenOdd_map_reverse
  条件: (n : ZMod 2)
  证明: by
  simp_rw [evenOdd, Submodule.map_iSup, submodule_map_pow_reverse, ι_range_map_reverse]

@[simp]

Depends on / 依赖: Submodule, Submodule.map_iSup, evenOdd, map_iSup, simp_rw, submodule_map_pow_reverse
-/
theorem evenOdd_map_reverse (n : ZMod 2) :
    (evenOdd Q n).map (reverse : CliffordAlgebra Q ->ₗ[R] CliffordAlgebra Q) = evenOdd Q n := by
  simp_rw [evenOdd, Submodule.map_iSup, submodule_map_pow_reverse, ι_range_map_reverse]

@[simp]
/--
theorem `evenOdd_comap_reverse` / 定理 `evenOdd_comap_reverse`

English:
theorem evenOdd_comap_reverse
  given: (n : ZMod 2)
  proof: by
  rw [← submodule_map_reverse_eq_comap]; rw [evenOdd_map_reverse]

中文:
定理 evenOdd_comap_reverse
  条件: (n : ZMod 2)
  证明: by
  rw [← submodule_map_reverse_eq_comap]; rw [evenOdd_map_reverse]

Depends on / 依赖: evenOdd_map_reverse, submodule_map_reverse_eq_comap
-/
theorem evenOdd_comap_reverse (n : ZMod 2) :
    (evenOdd Q n).comap (reverse : CliffordAlgebra Q ->ₗ[R] CliffordAlgebra Q) = evenOdd Q n := by
  rw [← submodule_map_reverse_eq_comap]; rw [evenOdd_map_reverse]

end Reverse

@[simp]
/--
theorem `involute_mem_evenOdd_iff` / 定理 `involute_mem_evenOdd_iff`

English:
theorem involute_mem_evenOdd_iff
  given: {x : CliffordAlgebra Q} {n : ZMod 2}
  proof: SetLike.ext_iff.mp (evenOdd_comap_involute Q n) x

@[simp]

中文:
定理 involute_mem_evenOdd_iff
  条件: {x : CliffordAlgebra Q} {n : ZMod 2}
  证明: SetLike.ext_iff.mp (evenOdd_comap_involute Q n) x

@[simp]

Depends on / 依赖: SetLike, SetLike.ext_iff.mp, evenOdd_comap_involute, ext_iff
-/
theorem involute_mem_evenOdd_iff {x : CliffordAlgebra Q} {n : ZMod 2} :
    involute x in evenOdd Q n ↔ x in evenOdd Q n :=
  SetLike.ext_iff.mp (evenOdd_comap_involute Q n) x

@[simp]
/--
theorem `reverse_mem_evenOdd_iff` / 定理 `reverse_mem_evenOdd_iff`

English:
theorem reverse_mem_evenOdd_iff
  given: {x : CliffordAlgebra Q} {n : ZMod 2}
  proof: SetLike.ext_iff.mp (evenOdd_comap_reverse Q n) x

中文:
定理 reverse_mem_evenOdd_iff
  条件: {x : CliffordAlgebra Q} {n : ZMod 2}
  证明: SetLike.ext_iff.mp (evenOdd_comap_reverse Q n) x

Depends on / 依赖: SetLike, SetLike.ext_iff.mp, evenOdd_comap_reverse, ext_iff
-/
theorem reverse_mem_evenOdd_iff {x : CliffordAlgebra Q} {n : ZMod 2} :
    reverse x in evenOdd Q n ↔ x in evenOdd Q n :=
  SetLike.ext_iff.mp (evenOdd_comap_reverse Q n) x

end Submodule



/--
theorem `involute_eq_of_mem_even` / 定理 `involute_eq_of_mem_even`

English:
theorem involute_eq_of_mem_even
  given: {x : CliffordAlgebra Q} (h : x in evenOdd Q 0)
  statement: involute x = x
  proof: by
  induction x, h using even_induction with
  | algebraMap r => exact AlgHom.commutes _ _
  | add x y _hx _hy ihx ihy =>
    rw [map_add]; rw [ihx]; rw [ihy]
  | ι_mul_ι_mul m₁ m₂ x _hx ihx =>
    rw [map_mul]; rw [map_mul]; rw [involute_ι]; rw [involute_ι]; rw [ihx]; rw [neg_mul_neg]

中文:
定理 involute_eq_of_mem_even
  条件: {x : CliffordAlgebra Q} (h : x in evenOdd Q 0)
  结论: involute x = x
  证明: by
  induction x, h using even_induction with
  | algebraMap r => exact AlgHom.commutes _ _
  | add x y _hx _hy ihx ihy =>
    rw [map_add]; rw [ihx]; rw [ihy]
  | ι_mul_ι_mul m₁ m₂ x _hx ihx =>
    rw [map_mul]; rw [map_mul]; rw [involute_ι]; rw [involute_ι]; rw [ihx]; rw [neg_mul_neg]

Depends on / 依赖: AlgHom, AlgHom.commutes, algebraMap, commutes, even_induction, map_add, map_mul, neg_mul_neg
-/
theorem involute_eq_of_mem_even {x : CliffordAlgebra Q} (h : x in evenOdd Q 0) : involute x = x := by
  induction x, h using even_induction with
  | algebraMap r => exact AlgHom.commutes _ _
  | add x y _hx _hy ihx ihy =>
    rw [map_add]; rw [ihx]; rw [ihy]
  | ι_mul_ι_mul m₁ m₂ x _hx ihx =>
    rw [map_mul]; rw [map_mul]; rw [involute_ι]; rw [involute_ι]; rw [ihx]; rw [neg_mul_neg]

/--
theorem `involute_eq_of_mem_odd` / 定理 `involute_eq_of_mem_odd`

English:
theorem involute_eq_of_mem_odd
  given: {x : CliffordAlgebra Q} (h : x in evenOdd Q 1)
  statement: involute x = -x
  proof: by
  induction x, h using odd_induction with
  | ι m => exact involute_ι _
  | add x y _hx _hy ihx ihy =>
    rw [map_add]; rw [ihx]; rw [ihy]; rw [neg_add]
  | ι_mul_ι_mul m₁ m₂ x _hx ihx =>
    rw [map_mul]; rw [map_mul]; rw [involute_ι]; rw [involute_ι]; rw [ihx]; rw [neg_mul_neg]; rw [mul_neg]

中文:
定理 involute_eq_of_mem_odd
  条件: {x : CliffordAlgebra Q} (h : x in evenOdd Q 1)
  结论: involute x = -x
  证明: by
  induction x, h using odd_induction with
  | ι m => exact involute_ι _
  | add x y _hx _hy ihx ihy =>
    rw [map_add]; rw [ihx]; rw [ihy]; rw [neg_add]
  | ι_mul_ι_mul m₁ m₂ x _hx ihx =>
    rw [map_mul]; rw [map_mul]; rw [involute_ι]; rw [involute_ι]; rw [ihx]; rw [neg_mul_neg]; rw [mul_neg]

Depends on / 依赖: map_add, map_mul, mul_neg, neg_add, neg_mul_neg, odd_induction
-/
theorem involute_eq_of_mem_odd {x : CliffordAlgebra Q} (h : x in evenOdd Q 1) : involute x = -x := by
  induction x, h using odd_induction with
  | ι m => exact involute_ι _
  | add x y _hx _hy ihx ihy =>
    rw [map_add]; rw [ihx]; rw [ihy]; rw [neg_add]
  | ι_mul_ι_mul m₁ m₂ x _hx ihx =>
    rw [map_mul]; rw [map_mul]; rw [involute_ι]; rw [involute_ι]; rw [ihx]; rw [neg_mul_neg]; rw [mul_neg]

end CliffordAlgebra
