/-
Copyright (c) 2024 Sophie Morel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sophie Morel
-/
module

public import Mathlib.Algebra.DirectSum.Module
public import Mathlib.LinearAlgebra.Multilinear.DFinsupp

/-!
# Multilinear maps from direct sums

This file describes multilinear maps on direct sums.

## Main results

* `MultilinearMap.fromDirectSumEquiv` : If `ι` is a `Fintype`, `κ i` is a family of types
  indexed by `ι` and we are given an `R`-module `M i j` for every `i : ι` and `j : κ i`, this is
  the linear equivalence between `Π p : (i : ι) → κ i, MultilinearMap R (fun i ↦ M i (p i)) M'` and
  `MultilinearMap R (fun i ↦ ⨁ j : κ i, M i j) M'`.
-/

@[expose] public section

namespace MultilinearMap

open DirectSum

variable {R ι M' : Type*} {κ : ι -> Type*} {M : (i : ι) -> κ i -> Type*}
variable [CommSemiring R]
variable [forall i j, AddCommMonoid (M i j)] [forall i j, Module R (M i j)] [AddCommMonoid M'] [Module R M']

/-- Two multilinear maps from direct sums are equal if they agree on the generators. -/
@[ext]
/--
theorem `directSum_ext` / 定理 `directSum_ext`

English:
theorem directSum_ext
  statement: [Finite ι] [(i : ι) -> DecidableEq (κ i)]
  proof: dfinsupp_ext h

中文:
定理 directSum_ext
  结论: [Finite ι] [(i : ι) -> DecidableEq (κ i)]
  证明: dfinsupp_ext h

Depends on / 依赖: dfinsupp_ext
-/
theorem directSum_ext [Finite ι] [(i : ι) -> DecidableEq (κ i)]
    ⦃f g : MultilinearMap R (fun i => ⨁ j : κ i, M i j) M'⦄
    (h : forall p : (i : ι) -> κ i,
      f.compLinearMap (fun i => DirectSum.lof _ _ _ (p i)) =
      g.compLinearMap (fun i => DirectSum.lof _ _ _ (p i))) : f = g :=
  dfinsupp_ext h

variable [DecidableEq ι]

/--
Definition of `fromDirectSumEquiv` / `fromDirectSumEquiv` 的定义

English:
definition fromDirectSumEquiv
  signature: [Finite ι]
  body: haveI : Fintype ι := Fintype.ofFinite ι
  haveI : (i : ι) -> DecidableEq (κ i) := fun i => Classical.typeDecidableEq (κ i)
  fromDFinsuppEquiv _ _

中文:
定义 fromDirectSumEquiv
  签名: [Finite ι]
  定义体: haveI : Fintype ι := Fintype.ofFinite ι
  haveI : (i : ι) -> DecidableEq (κ i) := fun i => Classical.typeDecidableEq (κ i)
  fromDFinsuppEquiv _ _

Depends on / 依赖: Classical, Classical.typeDecidableEq, DecidableEq, Fintype, Fintype.ofFinite, fromDFinsuppEquiv, ofFinite, typeDecidableEq
-/
noncomputable def fromDirectSumEquiv [Finite ι] :
    ((p : (i : ι) -> κ i) -> MultilinearMap R (fun i => M i (p i)) M') ≃ₗ[R]
    MultilinearMap R (fun i => ⨁ j : κ i, M i j) M' :=
  haveI : Fintype ι := Fintype.ofFinite ι
  haveI : (i : ι) -> DecidableEq (κ i) := fun i => Classical.typeDecidableEq (κ i)
  fromDFinsuppEquiv _ _

set_option backward.isDefEq.respectTransparency false in
@[simp]
/--
theorem `fromDirectSumEquiv_lof` / 定理 `fromDirectSumEquiv_lof`

English:
theorem fromDirectSumEquiv_lof
  statement: [Finite ι] [(i : ι) -> DecidableEq (κ i)]
  proof: by
  have : Fintype ι := Fintype.ofFinite ι
  rw [fromDirectSumEquiv]; rw [← fromDFinsuppEquiv_single]
  convert! rfl

中文:
定理 fromDirectSumEquiv_lof
  结论: [Finite ι] [(i : ι) -> DecidableEq (κ i)]
  证明: by
  have : Fintype ι := Fintype.ofFinite ι
  rw [fromDirectSumEquiv]; rw [← fromDFinsuppEquiv_single]
  convert! rfl

Depends on / 依赖: Fintype, Fintype.ofFinite, convert, fromDFinsuppEquiv_single, fromDirectSumEquiv, ofFinite
-/
theorem fromDirectSumEquiv_lof [Finite ι] [(i : ι) -> DecidableEq (κ i)]
    (f : (p : (i : ι) -> κ i) -> MultilinearMap R (fun i => M i (p i)) M')
    (p : (i : ι) -> κ i) (x : (i : ι) -> M i (p i)) :
    fromDirectSumEquiv f (fun i => lof R _ _ _ (x i)) = f p x := by
  have : Fintype ι := Fintype.ofFinite ι
  rw [fromDirectSumEquiv]; rw [← fromDFinsuppEquiv_single]
  convert! rfl

set_option backward.isDefEq.respectTransparency false in
/--
theorem `fromDirectSumEquiv_apply` / 定理 `fromDirectSumEquiv_apply`

English:
theorem fromDirectSumEquiv_apply
  statement: [Fintype ι] [(i : ι) -> DecidableEq (κ i)]
  proof: by
  rw [fromDirectSumEquiv]; rw [← fromDFinsuppEquiv_apply]
  convert! rfl

中文:
定理 fromDirectSumEquiv_apply
  结论: [Fintype ι] [(i : ι) -> DecidableEq (κ i)]
  证明: by
  rw [fromDirectSumEquiv]; rw [← fromDFinsuppEquiv_apply]
  convert! rfl

Depends on / 依赖: convert, fromDFinsuppEquiv_apply, fromDirectSumEquiv
-/
theorem fromDirectSumEquiv_apply [Fintype ι] [(i : ι) -> DecidableEq (κ i)]
    [Π i (j : κ i) (x : M i j), Decidable (x != 0)]
    (f : (p : (i : ι) -> κ i) -> MultilinearMap R (fun i => M i (p i)) M')
    (x : ⨁ i, ⨁ (j : κ i), M i j) :
    fromDirectSumEquiv f x =
      ∑ p in Fintype.piFinset (fun i => (x i).support), f p (fun i => x i (p i)) := by
  rw [fromDirectSumEquiv]; rw [← fromDFinsuppEquiv_apply]
  convert! rfl

set_option backward.isDefEq.respectTransparency false in
@[simp]
/--
theorem `fromDirectSumEquiv_symm_apply` / 定理 `fromDirectSumEquiv_symm_apply`

English:
theorem fromDirectSumEquiv_symm_apply
  statement: [Finite ι] [(i : ι) -> DecidableEq (κ i)]
  proof: by
  have : Fintype ι := Fintype.ofFinite ι
  simp_rw [fromDirectSumEquiv, DirectSum.lof, ← fromDFinsuppEquiv_symm_apply]
  convert! rfl

中文:
定理 fromDirectSumEquiv_symm_apply
  结论: [Finite ι] [(i : ι) -> DecidableEq (κ i)]
  证明: by
  have : Fintype ι := Fintype.ofFinite ι
  simp_rw [fromDirectSumEquiv, DirectSum.lof, ← fromDFinsuppEquiv_symm_apply]
  convert! rfl

Depends on / 依赖: DirectSum, DirectSum.lof, Fintype, Fintype.ofFinite, convert, fromDFinsuppEquiv_symm_apply, fromDirectSumEquiv, ofFinite, simp_rw
-/
theorem fromDirectSumEquiv_symm_apply [Finite ι] [(i : ι) -> DecidableEq (κ i)]
    (f : MultilinearMap R (fun i => ⨁ j : κ i, M i j) M')
    (p : (i : ι) -> κ i) :
    fromDirectSumEquiv.symm f p = f.compLinearMap (fun i => DirectSum.lof _ _ _ (p i)) := by
  have : Fintype ι := Fintype.ofFinite ι
  simp_rw [fromDirectSumEquiv, DirectSum.lof, ← fromDFinsuppEquiv_symm_apply]
  convert! rfl

end MultilinearMap
