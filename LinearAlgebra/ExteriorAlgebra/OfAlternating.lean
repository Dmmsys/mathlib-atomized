/-
Copyright (c) 2022 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser
-/
module

public import Mathlib.LinearAlgebra.CliffordAlgebra.Fold
public import Mathlib.LinearAlgebra.ExteriorAlgebra.Basic

/-!
# Extending an alternating map to the exterior algebra

## Main definitions

* `ExteriorAlgebra.liftAlternating`: construct a linear map out of the exterior algebra
  given alternating maps (corresponding to maps out of the exterior powers).
* `ExteriorAlgebra.liftAlternatingEquiv`: the above as a linear equivalence

## Main results

* `ExteriorAlgebra.lhom_ext`: linear maps from the exterior algebra agree if they agree on the
  exterior powers.

-/

@[expose] public section


variable {R M N N' : Type*}
variable [CommRing R] [AddCommGroup M] [AddCommGroup N] [AddCommGroup N']
variable [Module R M] [Module R N] [Module R N']

-- This instance can't be found where it's needed if we don't remind lean that it exists.
/--
Instance `AlternatingMap.instModuleAddCommGroup` / 实例 `AlternatingMap.instModuleAddCommGroup`

English:
instance AlternatingMap.instModuleAddCommGroup
  signature: {ι : Type*}
  body: by
  infer_instance

中文:
实例 AlternatingMap.instModuleAddCommGroup
  签名: {ι : 类型}
  定义体: by
  infer_instance

Depends on / 依赖: infer_instance
-/
instance AlternatingMap.instModuleAddCommGroup {ι : Type*} :
    Module R (M [⋀^ι]->ₗ[R] N) := by
  infer_instance

namespace ExteriorAlgebra

open CliffordAlgebra hiding ι

/--
Definition of `liftAlternating` / `liftAlternating` 的定义

English:
definition liftAlternating
  signature: : (forall i, M [⋀^Fin i]->ₗ[R] N) ->ₗ[R] ExteriorAlgebra R M ->ₗ[R] N
  body: by
  suffices
    (forall i, M [⋀^Fin i]->ₗ[R] N) ->ₗ[R]
      ExteriorAlgebra R M ->ₗ[R] forall i, M [⋀^Fin i]->ₗ[R] N by
    refine LinearMap.compr₂ this ?_
    refine (LinearEquiv.toLinearMap ?_).comp (LinearMap.proj 0)
    exact AlternatingMap.constLinearEquivOfIsEmpty.symm
  refine CliffordAlge

中文:
定义 liftAlternating
  签名: : (对任意 i, M [⋀^Fin i]->ₗ[R] N) ->ₗ[R] ExteriorAlgebra R M ->ₗ[R] N
  定义体: by
  suffices
    (forall i, M [⋀^Fin i]->ₗ[R] N) ->ₗ[R]
      ExteriorAlgebra R M ->ₗ[R] forall i, M [⋀^Fin i]->ₗ[R] N by
    refine LinearMap.compr₂ this ?_
    refine (LinearEquiv.toLinearMap ?_).comp (LinearMap.proj 0)
    exact AlternatingMap.constLinearEquivOfIsEmpty.symm
  refine CliffordAlge

Depends on / 依赖: AlternatingMap, AlternatingMap.constLinearEquivOfIsEmpty.symm, CliffordAlgebra, CliffordAlgebra.foldl, ExteriorAlgebra, LinearEquiv, LinearEquiv.toLinearMap, LinearMap, LinearMap.compr, LinearMap.mk, LinearMap.proj, Pi.add_apply, Pi.smul, add_apply, all_goals, constLinearEquivOfIsEmpty, curryLeft, i.succ, map_add, map_smul
-/
def liftAlternating : (forall i, M [⋀^Fin i]->ₗ[R] N) ->ₗ[R] ExteriorAlgebra R M ->ₗ[R] N := by
  suffices
    (forall i, M [⋀^Fin i]->ₗ[R] N) ->ₗ[R]
      ExteriorAlgebra R M ->ₗ[R] forall i, M [⋀^Fin i]->ₗ[R] N by
    refine LinearMap.compr₂ this ?_
    refine (LinearEquiv.toLinearMap ?_).comp (LinearMap.proj 0)
    exact AlternatingMap.constLinearEquivOfIsEmpty.symm
  refine CliffordAlgebra.foldl _ ?_ ?_
  · refine
      LinearMap.mk₂ R (fun m f i => (f i.succ).curryLeft m) (fun m₁ m₂ f => ?_) (fun c m f => ?_)
        (fun m f₁ f₂ => ?_) fun c m f => ?_
    all_goals
      ext i : 1
      simp only [map_smul, map_add, Pi.add_apply, Pi.smul_apply, AlternatingMap.curryLeft_add,
        AlternatingMap.curryLeft_smul, map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply]
  · -- when applied twice with the same `m`, this recursive step produces 0
    intro m x
    ext
    simp

set_option backward.defeqAttrib.useBackward true in
@[simp]
/--
theorem `liftAlternating_ι` / 定理 `liftAlternating_ι`

English:
theorem liftAlternating_ι
  given: (f : forall i, M [⋀^Fin i]->ₗ[R] N) (m : M)
  proof: by
  dsimp [liftAlternating]
  rw [foldl_ι]; rw [LinearMap.mk₂_apply]; rw [AlternatingMap.curryLeft_apply_apply]
  congr!

中文:
定理 liftAlternating_ι
  条件: (f : 对任意 i, M [⋀^Fin i]->ₗ[R] N) (m : M)
  证明: by
  dsimp [liftAlternating]
  rw [foldl_ι]; rw [LinearMap.mk₂_apply]; rw [AlternatingMap.curryLeft_apply_apply]
  congr!

Depends on / 依赖: AlternatingMap, AlternatingMap.curryLeft_apply_apply, LinearMap, LinearMap.mk, curryLeft_apply_apply, liftAlternating
-/
theorem liftAlternating_ι (f : forall i, M [⋀^Fin i]->ₗ[R] N) (m : M) :
    liftAlternating (R := R) (M := M) (N := N) f (ι R m) = f 1 ![m] := by
  dsimp [liftAlternating]
  rw [foldl_ι]; rw [LinearMap.mk₂_apply]; rw [AlternatingMap.curryLeft_apply_apply]
  congr!

/--
theorem `liftAlternating_ι_mul` / 定理 `liftAlternating_ι_mul`

English:
theorem liftAlternating_ι_mul
  statement: (f : forall i, M [⋀^Fin i]->ₗ[R] N) (m : M)
  proof: by
  dsimp [liftAlternating]
  rw [foldl_mul]; rw [foldl_ι]
  rfl

中文:
定理 liftAlternating_ι_mul
  结论: (f : 对任意 i, M [⋀^Fin i]->ₗ[R] N) (m : M)
  证明: by
  dsimp [liftAlternating]
  rw [foldl_mul]; rw [foldl_ι]
  rfl
-/
theorem liftAlternating_ι_mul (f : forall i, M [⋀^Fin i]->ₗ[R] N) (m : M)
    (x : ExteriorAlgebra R M) :
    liftAlternating (R := R) (M := M) (N := N) f (ι R m * x) =
    liftAlternating (R := R) (M := M) (N := N) (fun i => (f i.succ).curryLeft m) x := by
  dsimp [liftAlternating]
  rw [foldl_mul]; rw [foldl_ι]
  rfl

set_option backward.defeqAttrib.useBackward true in
@[simp]
/--
theorem `liftAlternating_one` / 定理 `liftAlternating_one`

English:
theorem liftAlternating_one
  given: (f : forall i, M [⋀^Fin i]->ₗ[R] N)
  proof: by
  dsimp [liftAlternating]
  rw [foldl_one]

@[simp]

中文:
定理 liftAlternating_one
  条件: (f : 对任意 i, M [⋀^Fin i]->ₗ[R] N)
  证明: by
  dsimp [liftAlternating]
  rw [foldl_one]

@[simp]

Depends on / 依赖: ExteriorAlgebra, foldl_one, liftAlternating
-/
theorem liftAlternating_one (f : forall i, M [⋀^Fin i]->ₗ[R] N) :
    liftAlternating (R := R) (M := M) (N := N) f (1 : ExteriorAlgebra R M) = f 0 0 := by
  dsimp [liftAlternating]
  rw [foldl_one]

@[simp]
/--
theorem `liftAlternating_algebraMap` / 定理 `liftAlternating_algebraMap`

English:
theorem liftAlternating_algebraMap
  given: (f : forall i, M [⋀^Fin i]->ₗ[R] N) (r : R)
  proof: by
  rw [Algebra.algebraMap_eq_smul_one]; rw [map_smul]; rw [liftAlternating_one]

@[simp]

中文:
定理 liftAlternating_algebraMap
  条件: (f : 对任意 i, M [⋀^Fin i]->ₗ[R] N) (r : R)
  证明: by
  rw [Algebra.algebraMap_eq_smul_one]; rw [map_smul]; rw [liftAlternating_one]

@[simp]

Depends on / 依赖: ExteriorAlgebra, algebraMap
-/
theorem liftAlternating_algebraMap (f : forall i, M [⋀^Fin i]->ₗ[R] N) (r : R) :
    liftAlternating (R := R) (M := M) (N := N) f (algebraMap _ (ExteriorAlgebra R M) r) =
    r • f 0 0 := by
  rw [Algebra.algebraMap_eq_smul_one]; rw [map_smul]; rw [liftAlternating_one]

@[simp]
/--
theorem `liftAlternating_apply_ιMulti` / 定理 `liftAlternating_apply_ιMulti`

English:
theorem liftAlternating_apply_ιMulti
  statement: {n : Nat} (f : forall i, M [⋀^Fin i]->ₗ[R] N)
  proof: by
  rw [ιMulti_apply]
  induction n generalizing f with
  | zero => rw [List.ofFn_zero, List.prod_nil, liftAlternating_one, Subsingleton.elim 0 v]
  | succ n ih =>
    rw [List.ofFn_succ]; rw [List.prod_cons]; rw [liftAlternating_ι_mul]; rw [ih]; rw [AlternatingMap.curryLeft_apply_apply]
    congr


中文:
定理 liftAlternating_apply_ιMulti
  结论: {n : 自然数} (f : 对任意 i, M [⋀^Fin i]->ₗ[R] N)
  证明: by
  rw [ιMulti_apply]
  induction n generalizing f with
  | zero => rw [List.ofFn_zero, List.prod_nil, liftAlternating_one, Subsingleton.elim 0 v]
  | succ n ih =>
    rw [List.ofFn_succ]; rw [List.prod_cons]; rw [liftAlternating_ι_mul]; rw [ih]; rw [AlternatingMap.curryLeft_apply_apply]
    congr


Depends on / 依赖: AlternatingMap, AlternatingMap.curryLeft_apply_apply, List.ofFn_succ, List.ofFn_zero, List.prod_cons, List.prod_nil, Matrix, Matrix.cons_head_tail, Subsingleton, Subsingleton.elim, cons_head_tail, curryLeft_apply_apply, generalizing, liftAlternating_one, ofFn_succ, ofFn_zero, prod_cons, prod_nil
-/
theorem liftAlternating_apply_ιMulti {n : Nat} (f : forall i, M [⋀^Fin i]->ₗ[R] N)
    (v : Fin n -> M) : liftAlternating (R := R) (M := M) (N := N) f (ιMulti R n v) = f n v := by
  rw [ιMulti_apply]
  induction n generalizing f with
  | zero => rw [List.ofFn_zero, List.prod_nil, liftAlternating_one, Subsingleton.elim 0 v]
  | succ n ih =>
    rw [List.ofFn_succ]; rw [List.prod_cons]; rw [liftAlternating_ι_mul]; rw [ih]; rw [AlternatingMap.curryLeft_apply_apply]
    congr
    exact Matrix.cons_head_tail _

@[simp]
/--
theorem `liftAlternating_comp_ιMulti` / 定理 `liftAlternating_comp_ιMulti`

English:
theorem liftAlternating_comp_ιMulti
  given: {n : Nat} (f : forall i, M [⋀^Fin i]->ₗ[R] N)
  proof: AlternatingMap.ext liftAlternating_apply_ιMulti f

@[simp]

中文:
定理 liftAlternating_comp_ιMulti
  条件: {n : 自然数} (f : 对任意 i, M [⋀^Fin i]->ₗ[R] N)
  证明: AlternatingMap.ext liftAlternating_apply_ιMulti f

@[simp]

Depends on / 依赖: compAlternatingMap
-/
theorem liftAlternating_comp_ιMulti {n : Nat} (f : forall i, M [⋀^Fin i]->ₗ[R] N) :
    (liftAlternating (R := R) (M := M) (N := N) f).compAlternatingMap (ιMulti R n) = f n :=
AlternatingMap.ext liftAlternating_apply_ιMulti f

@[simp]
/--
theorem `liftAlternating_comp` / 定理 `liftAlternating_comp`

English:
theorem liftAlternating_comp
  given: (g : N ->ₗ[R] N') (f : forall i, M [⋀^Fin i]->ₗ[R] N)
  proof: by
  ext v
  rw [LinearMap.comp_apply]
  induction v using CliffordAlgebra.left_induction generalizing f with
  | algebraMap =>
    rw [liftAlternating_algebraMap]; rw [liftAlternating_algebraMap]; rw [map_smul]; rw [LinearMap.compAlternatingMap_apply]
  | add _ _ hx hy => rw [map_add, map_add, map_

中文:
定理 liftAlternating_comp
  条件: (g : N ->ₗ[R] N') (f : 对任意 i, M [⋀^Fin i]->ₗ[R] N)
  证明: by
  ext v
  rw [LinearMap.comp_apply]
  induction v using CliffordAlgebra.left_induction generalizing f with
  | algebraMap =>
    rw [liftAlternating_algebraMap]; rw [liftAlternating_algebraMap]; rw [map_smul]; rw [LinearMap.compAlternatingMap_apply]
  | add _ _ hx hy => rw [map_add, map_add, map_

Depends on / 依赖: compAlternatingMap, g.compAlternatingMap
-/
theorem liftAlternating_comp (g : N ->ₗ[R] N') (f : forall i, M [⋀^Fin i]->ₗ[R] N) :
    (liftAlternating (R := R) (M := M) (N := N') fun i => g.compAlternatingMap (f i)) =
    g ∘ₗ liftAlternating (R := R) (M := M) (N := N) f := by
  ext v
  rw [LinearMap.comp_apply]
  induction v using CliffordAlgebra.left_induction generalizing f with
  | algebraMap =>
    rw [liftAlternating_algebraMap]; rw [liftAlternating_algebraMap]; rw [map_smul]; rw [LinearMap.compAlternatingMap_apply]
  | add _ _ hx hy => rw [map_add, map_add, map_add, hx, hy]
  | ι_mul _ _ hx =>
    rw [liftAlternating_ι_mul]; rw [liftAlternating_ι_mul]; rw [← hx]
    simp_rw [AlternatingMap.curryLeft_compAlternatingMap]

@[simp]
/--
theorem `liftAlternating_ιMulti` / 定理 `liftAlternating_ιMulti`

English:
theorem liftAlternating_ιMulti
  proof: by
  ext v
  dsimp
  induction v using CliffordAlgebra.left_induction with
  | algebraMap => rw [liftAlternating_algebraMap, ιMulti_zero_apply, Algebra.algebraMap_eq_smul_one]
  | add _ _ hx hy => rw [map_add, hx, hy]
  | ι_mul _ _ hx => simp_rw [liftAlternating_ι_mul, ιMulti_succ_curryLeft, liftAlt

中文:
定理 liftAlternating_ιMulti
  证明: by
  ext v
  dsimp
  induction v using CliffordAlgebra.left_induction with
  | algebraMap => rw [liftAlternating_algebraMap, ιMulti_zero_apply, Algebra.algebraMap_eq_smul_one]
  | add _ _ hx hy => rw [map_add, hx, hy]
  | ι_mul _ _ hx => simp_rw [liftAlternating_ι_mul, ιMulti_succ_curryLeft, liftAlt

Depends on / 依赖: ExteriorAlgebra
-/
theorem liftAlternating_ιMulti :
    liftAlternating (R := R) (M := M) (N := ExteriorAlgebra R M) (ιMulti R) =
    (LinearMap.id : ExteriorAlgebra R M ->ₗ[R] ExteriorAlgebra R M) := by
  ext v
  dsimp
  induction v using CliffordAlgebra.left_induction with
  | algebraMap => rw [liftAlternating_algebraMap, ιMulti_zero_apply, Algebra.algebraMap_eq_smul_one]
  | add _ _ hx hy => rw [map_add, hx, hy]
  | ι_mul _ _ hx => simp_rw [liftAlternating_ι_mul, ιMulti_succ_curryLeft, liftAlternating_comp,
      LinearMap.comp_apply, LinearMap.mulLeft_apply, hx]

/-- `ExteriorAlgebra.liftAlternating` is an equivalence. -/
@[simps apply symm_apply]
/--
Definition of `liftAlternatingEquiv` / `liftAlternatingEquiv` 的定义

English:
definition liftAlternatingEquiv
  signature: : (forall i, M [⋀^Fin i]->ₗ[R] N) ≃ₗ[R] ExteriorAlgebra R M ->ₗ[R] N where
  body: liftAlternating (R := R)
  map_add' := map_add _
  map_smul' := map_smul _
  invFun F i := F.compAlternatingMap (ιMulti R i)
  left_inv _ := funext fun _ => liftAlternating_comp_ιMulti _
  right_inv F :=
(liftAlternating_comp _ _).trans by rw [liftAlternating_ιMulti, LinearMap.comp_id]

中文:
定义 liftAlternatingEquiv
  签名: : (对任意 i, M [⋀^Fin i]->ₗ[R] N) ≃ₗ[R] ExteriorAlgebra R M ->ₗ[R] N where
  定义体: liftAlternating (R := R)
  map_add' := map_add _
  map_smul' := map_smul _
  invFun F i := F.compAlternatingMap (ιMulti R i)
  left_inv _ := funext fun _ => liftAlternating_comp_ιMulti _
  right_inv F :=
(liftAlternating_comp _ _).trans by rw [liftAlternating_ιMulti, LinearMap.comp_id]

Depends on / 依赖: liftAlternating
-/
def liftAlternatingEquiv : (forall i, M [⋀^Fin i]->ₗ[R] N) ≃ₗ[R] ExteriorAlgebra R M ->ₗ[R] N where
  toFun := liftAlternating (R := R)
  map_add' := map_add _
  map_smul' := map_smul _
  invFun F i := F.compAlternatingMap (ιMulti R i)
  left_inv _ := funext fun _ => liftAlternating_comp_ιMulti _
  right_inv F :=
(liftAlternating_comp _ _).trans by rw [liftAlternating_ιMulti, LinearMap.comp_id]

/-- To show that two linear maps from the exterior algebra agree, it suffices to show they agree on
the exterior powers.

See note [partially-applied ext lemmas] -/
@[ext]
/--
theorem `lhom_ext` / 定理 `lhom_ext`

English:
theorem lhom_ext
  given: ⦃f g
  statement: ExteriorAlgebra R M ->ₗ[R] N⦄
  proof: liftAlternatingEquiv.symm.injective funext h

中文:
定理 lhom_ext
  条件: ⦃f g
  结论: ExteriorAlgebra R M ->ₗ[R] N⦄
  证明: liftAlternatingEquiv.symm.injective funext h

Depends on / 依赖: injective, liftAlternatingEquiv, liftAlternatingEquiv.symm.injective
-/
theorem lhom_ext ⦃f g : ExteriorAlgebra R M ->ₗ[R] N⦄
    (h : forall i, f.compAlternatingMap (ιMulti R i) = g.compAlternatingMap (ιMulti R i)) : f = g :=
liftAlternatingEquiv.symm.injective funext h

end ExteriorAlgebra
