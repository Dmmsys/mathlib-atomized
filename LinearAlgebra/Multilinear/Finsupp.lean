/-
Copyright (c) 2025 Daniel Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Morrison
-/
module

public import Mathlib.LinearAlgebra.Multilinear.DFinsupp

/-!
# Interactions between finitely-supported functions and multilinear maps

## Main definitions

* `freeFinsuppEquiv` is an equivalence of multilinear maps over free modules with finitely
  supported maps.

-/

@[expose] public section

variable {ι ι' R : Type*} {κ : ι -> Type*}

namespace MultilinearMap

section freeFinsuppEquiv

variable [DecidableEq ι] [Fintype ι] [CommSemiring R] [DecidableEq R]
  [DecidableEq ι'] [forall i, Fintype (κ i)] [forall i, DecidableEq (κ i)]

/--
Definition of `freeFinsuppEquiv` / `freeFinsuppEquiv` 的定义

English:
definition freeFinsuppEquiv
  signature: :
  body: (finsuppLequivDFinsupp R) ≪≫ₗ freeDFinsuppEquiv ≪≫ₗ
  ((finsuppLequivDFinsupp R).multilinearMapCongrRight R).symm ≪≫ₗ
  LinearEquiv.multilinearMapCongrLeft (fun _ => finsuppLequivDFinsupp R)

中文:
定义 freeFinsuppEquiv
  签名: :
  定义体: (finsuppLequivDFinsupp R) ≪≫ₗ freeDFinsuppEquiv ≪≫ₗ
  ((finsuppLequivDFinsupp R).multilinearMapCongrRight R).symm ≪≫ₗ
  LinearEquiv.multilinearMapCongrLeft (fun _ => finsuppLequivDFinsupp R)

Depends on / 依赖: LinearEquiv, LinearEquiv.multilinearMapCongrLeft, finsuppLequivDFinsupp, freeDFinsuppEquiv, multilinearMapCongrLeft, multilinearMapCongrRight
-/
noncomputable def freeFinsuppEquiv :
    (((Π i, κ i) × ι') ->₀ R) ≃ₗ[R] MultilinearMap R (fun i => (κ i ->₀ R)) (ι' ->₀ R) :=
  (finsuppLequivDFinsupp R) ≪≫ₗ freeDFinsuppEquiv ≪≫ₗ
  ((finsuppLequivDFinsupp R).multilinearMapCongrRight R).symm ≪≫ₗ
  LinearEquiv.multilinearMapCongrLeft (fun _ => finsuppLequivDFinsupp R)

/--
theorem `freeFinsuppEquiv_def` / 定理 `freeFinsuppEquiv_def`

English:
theorem freeFinsuppEquiv_def
  given: (f : ((Π i, κ i) × ι') ->₀ R)
  proof: rfl

中文:
定理 freeFinsuppEquiv_def
  条件: (f : ((Π i, κ i) × ι') ->₀ R)
  证明: rfl
-/
theorem freeFinsuppEquiv_def (f : ((Π i, κ i) × ι') ->₀ R) :
    freeFinsuppEquiv f =
      LinearEquiv.multilinearMapCongrLeft (fun _ => finsuppLequivDFinsupp R)
      (((finsuppLequivDFinsupp R).multilinearMapCongrRight R).symm <|
      freeDFinsuppEquiv (finsuppLequivDFinsupp R f)) :=
  rfl

/--
When `freeFinsuppEquiv` is applied to a map with a single value the resulting multilinear
map sends inputs to a single value in the codomain, taking a product over images from each
component of the domain.
-/
@[simp]
/--
theorem `freeFinsuppEquiv_single` / 定理 `freeFinsuppEquiv_single`

English:
theorem freeFinsuppEquiv_single
  given: (p : ((Π i, κ i) × ι')) (r : R) (x : Π i, (κ i ->₀ R))
  proof: by
  simp [freeFinsuppEquiv_def]

中文:
定理 freeFinsuppEquiv_single
  条件: (p : ((Π i, κ i) × ι')) (r : R) (x : Π i, (κ i ->₀ R))
  证明: by
  simp [freeFinsuppEquiv_def]

Depends on / 依赖: freeFinsuppEquiv_def
-/
theorem freeFinsuppEquiv_single (p : ((Π i, κ i) × ι')) (r : R) (x : Π i, (κ i ->₀ R)) :
    freeFinsuppEquiv (Finsupp.single p r) x = r • Finsupp.single p.2 ((∏ i, (x i) (p.1 i))) := by
  simp [freeFinsuppEquiv_def]

/--
theorem `freeFinsuppEquiv_apply` / 定理 `freeFinsuppEquiv_apply`

English:
theorem freeFinsuppEquiv_apply
  statement: [Fintype ι']
  proof: by
  induction f using Finsupp.induction_linear with
  | zero => simp
  | add f g hf hg => simp [hf, hg, add_mul, Finset.sum_add_distrib]
  | single p r => simp [Finsupp.single_apply]

中文:
定理 freeFinsuppEquiv_apply
  结论: [Fintype ι']
  证明: by
  induction f using Finsupp.induction_linear with
  | zero => simp
  | add f g hf hg => simp [hf, hg, add_mul, Finset.sum_add_distrib]
  | single p r => simp [Finsupp.single_apply]

Depends on / 依赖: Finset, Finset.sum_add_distrib, Finsupp, Finsupp.induction_linear, Finsupp.single_apply, add_mul, induction_linear, single, single_apply, sum_add_distrib
-/
theorem freeFinsuppEquiv_apply [Fintype ι']
  (f : ((Π i, κ i) × ι') ->₀ R) (x : Π i, (κ i ->₀ R)) :
  freeFinsuppEquiv f x = ∑ p, f p • Finsupp.single p.2 ((∏ i, (x i) (p.1 i))) := by
  induction f using Finsupp.induction_linear with
  | zero => simp
  | add f g hf hg => simp [hf, hg, add_mul, Finset.sum_add_distrib]
  | single p r => simp [Finsupp.single_apply]

end freeFinsuppEquiv

end MultilinearMap
