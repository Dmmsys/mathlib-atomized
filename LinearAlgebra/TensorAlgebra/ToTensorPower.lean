/-
Copyright (c) 2021 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser
-/
module

public import Mathlib.LinearAlgebra.TensorAlgebra.Basic
public import Mathlib.LinearAlgebra.TensorPower.Basic

/-!
# Tensor algebras as direct sums of tensor powers

In this file we show that `TensorAlgebra R M` is isomorphic to a direct sum of tensor powers, as
`TensorAlgebra.equivDirectSum`.
-/

@[expose] public section

open scoped DirectSum TensorProduct

variable {R M : Type*} [CommSemiring R] [AddCommMonoid M] [Module R M]

namespace TensorPower

/--
Definition of `toTensorAlgebra` / `toTensorAlgebra` 的定义

English:
definition toTensorAlgebra
  signature: {n}
  body: PiTensorProduct.lift (TensorAlgebra.tprod R M n)

@[simp]

中文:
定义 toTensorAlgebra
  签名: {n}
  定义体: PiTensorProduct.lift (TensorAlgebra.tprod R M n)

@[simp]

Depends on / 依赖: PiTensorProduct, PiTensorProduct.lift, TensorAlgebra, TensorAlgebra.tprod
-/
def toTensorAlgebra {n} : ⨂[R]^n M ->ₗ[R] TensorAlgebra R M :=
  PiTensorProduct.lift (TensorAlgebra.tprod R M n)

@[simp]
/--
theorem `toTensorAlgebra_tprod` / 定理 `toTensorAlgebra_tprod`

English:
theorem toTensorAlgebra_tprod
  given: {n} (x : Fin n -> M)
  proof: PiTensorProduct.lift.tprod _

@[simp]

中文:
定理 toTensorAlgebra_tprod
  条件: {n} (x : 有限集 n -> M)
  证明: PiTensorProduct.lift.tprod _

@[simp]

Depends on / 依赖: PiTensorProduct, PiTensorProduct.lift.tprod
-/
theorem toTensorAlgebra_tprod {n} (x : Fin n -> M) :
    TensorPower.toTensorAlgebra (PiTensorProduct.tprod R x) = TensorAlgebra.tprod R M n x :=
  PiTensorProduct.lift.tprod _

@[simp]
/--
theorem `toTensorAlgebra_gOne` / 定理 `toTensorAlgebra_gOne`

English:
theorem toTensorAlgebra_gOne
  proof: by
  simp [GradedMonoid.GOne.one, TensorPower.toTensorAlgebra_tprod]

@[simp]

中文:
定理 toTensorAlgebra_gOne
  证明: by
  simp [GradedMonoid.GOne.one, TensorPower.toTensorAlgebra_tprod]

@[simp]

Depends on / 依赖: GradedMonoid, GradedMonoid.GOne.one, TensorPower, TensorPower.toTensorAlgebra_tprod, toTensorAlgebra_tprod
-/
theorem toTensorAlgebra_gOne :
    TensorPower.toTensorAlgebra (@GradedMonoid.GOne.one _ (fun n => ⨂[R]^n M) _ _) = 1 := by
  simp [GradedMonoid.GOne.one, TensorPower.toTensorAlgebra_tprod]

@[simp]
/--
theorem `toTensorAlgebra_gMul` / 定理 `toTensorAlgebra_gMul`

English:
theorem toTensorAlgebra_gMul
  given: {i j} (a : (⨂[R]^i) M) (b : (⨂[R]^j) M)
  proof: by
  -- change `a` and `b` to `tprod R a` and `tprod R b`
  rw [TensorPower.gMul_eq_coe_linearMap]; rw [← LinearMap.compr₂_apply]; rw [← @LinearMap.mul_apply' R]; rw [←
    LinearMap.compl₂_apply]; rw [← LinearMap.comp_apply]
  refine LinearMap.congr_fun (LinearMap.congr_fun ?_ a) b
  clear! a b
  ext (a b)
  simp only [LinearMap.compMultilinearMap_apply, LinearMap.compr₂_apply, ← gMul_def,
    TensorProduct.mk_apply, LinearEquiv.coe_coe, tprod_mul_tprod, toTensorAlgebra_tprod,
    TensorAlgebra.tprod_apply, LinearMap.comp_apply, LinearMap.compl₂_apply]
  refine Eq.trans ?_ List.prod_append
  congr
  rw [List.ofFn_comp' _ (TensorAlgebra.ι R)]; rw [List.ofFn_comp' _ (TensorAlgebra.ι R)]; rw [List.ofFn_comp' _ (TensorAlgebra.ι R)]; rw [← List.map_append]; rw [List.ofFn_fin_append]

@[simp]

中文:
定理 toTensorAlgebra_gMul
  条件: {i j} (a : (⨂[R]^i) M) (b : (⨂[R]^j) M)
  证明: by
  -- change `a` and `b` to `tprod R a` and `tprod R b`
  rw [TensorPower.gMul_eq_coe_linearMap]; rw [← LinearMap.compr₂_apply]; rw [← @LinearMap.mul_apply' R]; rw [←
    LinearMap.compl₂_apply]; rw [← LinearMap.comp_apply]
  refine LinearMap.congr_fun (LinearMap.congr_fun ?_ a) b
  clear! a b
  ext (a b)
  simp only [LinearMap.compMultilinearMap_apply, LinearMap.compr₂_apply, ← gMul_def,
    TensorProduct.mk_apply, LinearEquiv.coe_coe, tprod_mul_tprod, toTensorAlgebra_tprod,
    TensorAlgebra.tprod_apply, LinearMap.comp_apply, LinearMap.compl₂_apply]
  refine Eq.trans ?_ List.prod_append
  congr
  rw [List.ofFn_comp' _ (TensorAlgebra.ι R)]; rw [List.ofFn_comp' _ (TensorAlgebra.ι R)]; rw [List.ofFn_comp' _ (TensorAlgebra.ι R)]; rw [← List.map_append]; rw [List.ofFn_fin_append]

@[simp]
-/
theorem toTensorAlgebra_gMul {i j} (a : (⨂[R]^i) M) (b : (⨂[R]^j) M) :
    TensorPower.toTensorAlgebra (@GradedMonoid.GMul.mul _ (fun n => ⨂[R]^n M) _ _ _ _ a b) =
      TensorPower.toTensorAlgebra a * TensorPower.toTensorAlgebra b := by
  -- change `a` and `b` to `tprod R a` and `tprod R b`
  rw [TensorPower.gMul_eq_coe_linearMap]; rw [← LinearMap.compr₂_apply]; rw [← @LinearMap.mul_apply' R]; rw [←
    LinearMap.compl₂_apply]; rw [← LinearMap.comp_apply]
  refine LinearMap.congr_fun (LinearMap.congr_fun ?_ a) b
  clear! a b
  ext (a b)
  simp only [LinearMap.compMultilinearMap_apply, LinearMap.compr₂_apply, ← gMul_def,
    TensorProduct.mk_apply, LinearEquiv.coe_coe, tprod_mul_tprod, toTensorAlgebra_tprod,
    TensorAlgebra.tprod_apply, LinearMap.comp_apply, LinearMap.compl₂_apply]
  refine Eq.trans ?_ List.prod_append
  congr
  rw [List.ofFn_comp' _ (TensorAlgebra.ι R)]; rw [List.ofFn_comp' _ (TensorAlgebra.ι R)]; rw [List.ofFn_comp' _ (TensorAlgebra.ι R)]; rw [← List.map_append]; rw [List.ofFn_fin_append]

@[simp]
/--
theorem `toTensorAlgebra_galgebra_toFun` / 定理 `toTensorAlgebra_galgebra_toFun`

English:
theorem toTensorAlgebra_galgebra_toFun
  given: (r : R)
  proof: by
  rw [TensorPower.galgebra_toFun_def]; rw [TensorPower.algebraMap₀_eq_smul_one]; rw [map_smul]; rw [TensorPower.toTensorAlgebra_gOne]; rw [Algebra.algebraMap_eq_smul_one]

中文:
定理 toTensorAlgebra_galgebra_toFun
  条件: (r : R)
  证明: by
  rw [TensorPower.galgebra_toFun_def]; rw [TensorPower.algebraMap₀_eq_smul_one]; rw [map_smul]; rw [TensorPower.toTensorAlgebra_gOne]; rw [Algebra.algebraMap_eq_smul_one]
-/
theorem toTensorAlgebra_galgebra_toFun (r : R) :
    TensorPower.toTensorAlgebra (DirectSum.GAlgebra.toFun (R := R) (A := fun n => ⨂[R]^n M) r) =
      algebraMap _ _ r := by
  rw [TensorPower.galgebra_toFun_def]; rw [TensorPower.algebraMap₀_eq_smul_one]; rw [map_smul]; rw [TensorPower.toTensorAlgebra_gOne]; rw [Algebra.algebraMap_eq_smul_one]

end TensorPower

namespace TensorAlgebra

/--
Definition of `ofDirectSum` / `ofDirectSum` 的定义

English:
definition ofDirectSum
  signature: : (⨁ n, ⨂[R]^n M) ->ₐ[R] TensorAlgebra R M
  body: DirectSum.toAlgebra _ _ (fun _ => TensorPower.toTensorAlgebra) TensorPower.toTensorAlgebra_gOne
    (fun {_ _} => TensorPower.toTensorAlgebra_gMul)

@[simp]

中文:
定义 ofDirectSum
  签名: : (⨁ n, ⨂[R]^n M) ->ₐ[R] TensorAlgebra R M
  定义体: DirectSum.toAlgebra _ _ (fun _ => TensorPower.toTensorAlgebra) TensorPower.toTensorAlgebra_gOne
    (fun {_ _} => TensorPower.toTensorAlgebra_gMul)

@[simp]

Depends on / 依赖: DirectSum, DirectSum.toAlgebra, TensorPower, TensorPower.toTensorAlgebra, TensorPower.toTensorAlgebra_gMul, TensorPower.toTensorAlgebra_gOne, toAlgebra, toTensorAlgebra, toTensorAlgebra_gMul, toTensorAlgebra_gOne
-/
def ofDirectSum : (⨁ n, ⨂[R]^n M) ->ₐ[R] TensorAlgebra R M :=
  DirectSum.toAlgebra _ _ (fun _ => TensorPower.toTensorAlgebra) TensorPower.toTensorAlgebra_gOne
    (fun {_ _} => TensorPower.toTensorAlgebra_gMul)

@[simp]
/--
theorem `ofDirectSum_of_tprod` / 定理 `ofDirectSum_of_tprod`

English:
theorem ofDirectSum_of_tprod
  given: {n} (x : Fin n -> M)
  proof: (DirectSum.toAddMonoid_of
    (fun _ => LinearMap.toAddMonoidHom TensorPower.toTensorAlgebra) _ _).trans
  (TensorPower.toTensorAlgebra_tprod _)

中文:
定理 ofDirectSum_of_tprod
  条件: {n} (x : 有限集 n -> M)
  证明: (DirectSum.toAddMonoid_of
    (fun _ => LinearMap.toAddMonoidHom TensorPower.toTensorAlgebra) _ _).trans
  (TensorPower.toTensorAlgebra_tprod _)

Depends on / 依赖: DirectSum, DirectSum.toAddMonoid_of, LinearMap, LinearMap.toAddMonoidHom, TensorPower, TensorPower.toTensorAlgebra, TensorPower.toTensorAlgebra_tprod, toAddMonoidHom, toAddMonoid_of, toTensorAlgebra, toTensorAlgebra_tprod
-/
theorem ofDirectSum_of_tprod {n} (x : Fin n -> M) :
    ofDirectSum (DirectSum.of _ n (PiTensorProduct.tprod R x)) = tprod R M n x :=
  (DirectSum.toAddMonoid_of
    (fun _ => LinearMap.toAddMonoidHom TensorPower.toTensorAlgebra) _ _).trans
  (TensorPower.toTensorAlgebra_tprod _)

/--
Definition of `toDirectSum` / `toDirectSum` 的定义

English:
definition toDirectSum
  signature: : TensorAlgebra R M ->ₐ[R] ⨁ n, ⨂[R]^n M
  body: TensorAlgebra.lift R
    DirectSum.lof R Nat (fun n => ⨂[R]^n M) _ ∘ₗ
      (LinearEquiv.symm <| PiTensorProduct.subsingletonEquiv (0 : Fin 1) : M ≃ₗ[R] _).toLinearMap

@[simp]

中文:
定义 toDirectSum
  签名: : TensorAlgebra R M ->ₐ[R] ⨁ n, ⨂[R]^n M
  定义体: TensorAlgebra.lift R
    DirectSum.lof R Nat (fun n => ⨂[R]^n M) _ ∘ₗ
      (LinearEquiv.symm <| PiTensorProduct.subsingletonEquiv (0 : Fin 1) : M ≃ₗ[R] _).toLinearMap

@[simp]

Depends on / 依赖: DirectSum, DirectSum.lof, LinearEquiv, LinearEquiv.symm, PiTensorProduct, PiTensorProduct.subsingletonEquiv, TensorAlgebra, TensorAlgebra.lift, subsingletonEquiv, toLinearMap
-/
def toDirectSum : TensorAlgebra R M ->ₐ[R] ⨁ n, ⨂[R]^n M :=
TensorAlgebra.lift R
    DirectSum.lof R Nat (fun n => ⨂[R]^n M) _ ∘ₗ
      (LinearEquiv.symm <| PiTensorProduct.subsingletonEquiv (0 : Fin 1) : M ≃ₗ[R] _).toLinearMap

@[simp]
/--
theorem `toDirectSum_ι` / 定理 `toDirectSum_ι`

English:
theorem toDirectSum_ι
  given: (x : M)
  proof: by
  simp [toDirectSum, TensorAlgebra.lift_ι_apply, DirectSum.lof_eq_of]

中文:
定理 toDirectSum_ι
  条件: (x : M)
  证明: by
  simp [toDirectSum, TensorAlgebra.lift_ι_apply, DirectSum.lof_eq_of]

Depends on / 依赖: DirectSum, DirectSum.lof_eq_of, TensorAlgebra, TensorAlgebra.lift_, lof_eq_of, toDirectSum
-/
theorem toDirectSum_ι (x : M) :
    toDirectSum (ι R x) =
      DirectSum.of (fun n => ⨂[R]^n M) _ (PiTensorProduct.tprod R fun _ : Fin 1 => x) := by
  simp [toDirectSum, TensorAlgebra.lift_ι_apply, DirectSum.lof_eq_of]

/--
theorem `ofDirectSum_comp_toDirectSum` / 定理 `ofDirectSum_comp_toDirectSum`

English:
theorem ofDirectSum_comp_toDirectSum
  proof: by
  ext
  simp [tprod_apply]

@[simp]

中文:
定理 ofDirectSum_comp_toDirectSum
  证明: by
  ext
  simp [tprod_apply]

@[simp]

Depends on / 依赖: tprod_apply
-/
theorem ofDirectSum_comp_toDirectSum :
    ofDirectSum.comp toDirectSum = AlgHom.id R (TensorAlgebra R M) := by
  ext
  simp [tprod_apply]

@[simp]
/--
theorem `ofDirectSum_toDirectSum` / 定理 `ofDirectSum_toDirectSum`

English:
theorem ofDirectSum_toDirectSum
  given: (x : TensorAlgebra R M)
  proof: AlgHom.congr_fun ofDirectSum_comp_toDirectSum x

@[simp]

中文:
定理 ofDirectSum_toDirectSum
  条件: (x : TensorAlgebra R M)
  证明: AlgHom.congr_fun ofDirectSum_comp_toDirectSum x

@[simp]

Depends on / 依赖: AlgHom, AlgHom.congr_fun, congr_fun, ofDirectSum_comp_toDirectSum
-/
theorem ofDirectSum_toDirectSum (x : TensorAlgebra R M) :
    ofDirectSum (TensorAlgebra.toDirectSum x) = x :=
  AlgHom.congr_fun ofDirectSum_comp_toDirectSum x

@[simp]
/--
theorem `mk_reindex_cast` / 定理 `mk_reindex_cast`

English:
theorem mk_reindex_cast
  given: {n m : Nat} (h : n = m) (x : ⨂[R]^n M)
  proof: Eq.symm (PiTensorProduct.gradedMonoid_eq_of_reindex_cast h rfl)

@[simp]

中文:
定理 mk_reindex_cast
  条件: {n m : 自然数} (h : n = m) (x : ⨂[R]^n M)
  证明: Eq.symm (PiTensorProduct.gradedMonoid_eq_of_reindex_cast h rfl)

@[simp]
-/
theorem mk_reindex_cast {n m : Nat} (h : n = m) (x : ⨂[R]^n M) :
    GradedMonoid.mk (A := fun i => (⨂[R]^i) M) m
    (PiTensorProduct.reindex R (fun _ => M) (Equiv.cast <| congr_arg Fin h) x) =
    GradedMonoid.mk n x :=
  Eq.symm (PiTensorProduct.gradedMonoid_eq_of_reindex_cast h rfl)

@[simp]
/--
theorem `mk_reindex_fin_cast` / 定理 `mk_reindex_fin_cast`

English:
theorem mk_reindex_fin_cast
  given: {n m : Nat} (h : n = m) (x : ⨂[R]^n M)
  proof: by
  rw [finCongr_eq_equivCast]; rw [mk_reindex_cast h]

中文:
定理 mk_reindex_fin_cast
  条件: {n m : 自然数} (h : n = m) (x : ⨂[R]^n M)
  证明: by
  rw [finCongr_eq_equivCast]; rw [mk_reindex_cast h]
-/
theorem mk_reindex_fin_cast {n m : Nat} (h : n = m) (x : ⨂[R]^n M) :
    GradedMonoid.mk (A := fun i => (⨂[R]^i) M) m
    (PiTensorProduct.reindex R (fun _ => M) (finCongr h) x) = GradedMonoid.mk n x := by
  rw [finCongr_eq_equivCast]; rw [mk_reindex_cast h]

set_option backward.isDefEq.respectTransparency false in
/--
theorem `_root_.TensorPower.list_prod_gradedMonoid_mk_single` / 定理 `_root_.TensorPower.list_prod_gradedMonoid_mk_single`

English:
theorem _root_.TensorPower.list_prod_gradedMonoid_mk_single
  given: (n : Nat) (x : Fin n -> M)
  proof: by
  refine Fin.consInduction ?_ ?_ x <;> clear x
  · rw [List.finRange_zero, List.map_nil, List.prod_nil]
    rfl
  · intro n x₀ x ih
    rw [List.finRange_succ]; rw [List.map_cons]; rw [List.prod_cons]; rw [List.map_map]
    simp_rw [Function.comp_def, Fin.cons_zero, Fin.cons_succ]
    rw [ih]; rw [GradedMonoid.mk_mul_mk]; rw [TensorPower.tprod_mul_tprod]
    refine TensorPower.gradedMonoid_eq_of_cast (add_comm _ _) ?_
    dsimp only [GradedMonoid.mk]
    rw [TensorPower.cast_tprod]
    simp_rw [Fin.append_left_eq_cons, Function.comp_def]
    congr 1 with i

中文:
定理 _root_.TensorPower.list_prod_gradedMonoid_mk_single
  条件: (n : 自然数) (x : 有限集 n -> M)
  证明: by
  refine Fin.consInduction ?_ ?_ x <;> clear x
  · rw [List.finRange_zero, List.map_nil, List.prod_nil]
    rfl
  · intro n x₀ x ih
    rw [List.finRange_succ]; rw [List.map_cons]; rw [List.prod_cons]; rw [List.map_map]
    simp_rw [Function.comp_def, Fin.cons_zero, Fin.cons_succ]
    rw [ih]; rw [GradedMonoid.mk_mul_mk]; rw [TensorPower.tprod_mul_tprod]
    refine TensorPower.gradedMonoid_eq_of_cast (add_comm _ _) ?_
    dsimp only [GradedMonoid.mk]
    rw [TensorPower.cast_tprod]
    simp_rw [Fin.append_left_eq_cons, Function.comp_def]
    congr 1 with i

Depends on / 依赖: Fin.append_left_eq_cons, Fin.consInduction, Fin.cons_succ, Fin.cons_zero, Function, Function.c, Function.comp_def, GradedMonoid, GradedMonoid.mk, GradedMonoid.mk_mul_mk, List.finRange_succ, List.finRange_zero, List.map_cons, List.map_map, List.map_nil, List.prod_cons, List.prod_nil, TensorPower, TensorPower.cast_tprod, TensorPower.gradedMonoid_eq_of_cast
-/
theorem _root_.TensorPower.list_prod_gradedMonoid_mk_single (n : Nat) (x : Fin n -> M) :
    ((List.finRange n).map fun a =>
          (GradedMonoid.mk _ (PiTensorProduct.tprod R fun _ : Fin 1 => x a) :
            GradedMonoid fun n => ⨂[R]^n M)).prod =
      GradedMonoid.mk n (PiTensorProduct.tprod R x) := by
  refine Fin.consInduction ?_ ?_ x <;> clear x
  · rw [List.finRange_zero, List.map_nil, List.prod_nil]
    rfl
  · intro n x₀ x ih
    rw [List.finRange_succ]; rw [List.map_cons]; rw [List.prod_cons]; rw [List.map_map]
    simp_rw [Function.comp_def, Fin.cons_zero, Fin.cons_succ]
    rw [ih]; rw [GradedMonoid.mk_mul_mk]; rw [TensorPower.tprod_mul_tprod]
    refine TensorPower.gradedMonoid_eq_of_cast (add_comm _ _) ?_
    dsimp only [GradedMonoid.mk]
    rw [TensorPower.cast_tprod]
    simp_rw [Fin.append_left_eq_cons, Function.comp_def]
    congr 1 with i

/--
theorem `toDirectSum_tensorPower_tprod` / 定理 `toDirectSum_tensorPower_tprod`

English:
theorem toDirectSum_tensorPower_tprod
  given: {n} (x : Fin n -> M)
  proof: by
  rw [tprod_apply]; rw [map_list_prod]; rw [List.map_ofFn]
  simp_rw [Function.comp_def, toDirectSum_ι]
  rw [DirectSum.list_prod_ofFn_of_eq_dProd]
  apply DirectSum.of_eq_of_gradedMonoid_eq
  rw [GradedMonoid.mk_list_dProd]
  rw [TensorPower.list_prod_gradedMonoid_mk_single]

中文:
定理 toDirectSum_tensorPower_tprod
  条件: {n} (x : 有限集 n -> M)
  证明: by
  rw [tprod_apply]; rw [map_list_prod]; rw [List.map_ofFn]
  simp_rw [Function.comp_def, toDirectSum_ι]
  rw [DirectSum.list_prod_ofFn_of_eq_dProd]
  apply DirectSum.of_eq_of_gradedMonoid_eq
  rw [GradedMonoid.mk_list_dProd]
  rw [TensorPower.list_prod_gradedMonoid_mk_single]

Depends on / 依赖: DirectSum, DirectSum.list_prod_ofFn_of_eq_dProd, DirectSum.of_eq_of_gradedMonoid_eq, Function, Function.comp_def, GradedMonoid, GradedMonoid.mk_list_dProd, List.map_ofFn, TensorPower, TensorPower.list_prod_gradedMonoid_mk_single, comp_def, list_prod_gradedMonoid_mk_single, list_prod_ofFn_of_eq_dProd, map_list_prod, map_ofFn, mk_list_dProd, of_eq_of_gradedMonoid_eq, simp_rw, tprod_apply
-/
theorem toDirectSum_tensorPower_tprod {n} (x : Fin n -> M) :
    toDirectSum (tprod R M n x) = DirectSum.of _ n (PiTensorProduct.tprod R x) := by
  rw [tprod_apply]; rw [map_list_prod]; rw [List.map_ofFn]
  simp_rw [Function.comp_def, toDirectSum_ι]
  rw [DirectSum.list_prod_ofFn_of_eq_dProd]
  apply DirectSum.of_eq_of_gradedMonoid_eq
  rw [GradedMonoid.mk_list_dProd]
  rw [TensorPower.list_prod_gradedMonoid_mk_single]

/--
theorem `toDirectSum_comp_ofDirectSum` / 定理 `toDirectSum_comp_ofDirectSum`

English:
theorem toDirectSum_comp_ofDirectSum
  proof: by
  ext
  simp [DirectSum.lof_eq_of, -tprod_apply, toDirectSum_tensorPower_tprod]

@[simp]

中文:
定理 toDirectSum_comp_ofDirectSum
  证明: by
  ext
  simp [DirectSum.lof_eq_of, -tprod_apply, toDirectSum_tensorPower_tprod]

@[simp]

Depends on / 依赖: DirectSum, DirectSum.lof_eq_of, lof_eq_of, toDirectSum_tensorPower_tprod, tprod_apply
-/
theorem toDirectSum_comp_ofDirectSum :
    toDirectSum.comp ofDirectSum = AlgHom.id R (⨁ n, ⨂[R]^n M) := by
  ext
  simp [DirectSum.lof_eq_of, -tprod_apply, toDirectSum_tensorPower_tprod]

@[simp]
/--
theorem `toDirectSum_ofDirectSum` / 定理 `toDirectSum_ofDirectSum`

English:
theorem toDirectSum_ofDirectSum
  given: (x : ⨁ n, ⨂[R]^n M)
  proof: AlgHom.congr_fun toDirectSum_comp_ofDirectSum x

中文:
定理 toDirectSum_ofDirectSum
  条件: (x : ⨁ n, ⨂[R]^n M)
  证明: AlgHom.congr_fun toDirectSum_comp_ofDirectSum x

Depends on / 依赖: AlgHom, AlgHom.congr_fun, congr_fun, toDirectSum_comp_ofDirectSum
-/
theorem toDirectSum_ofDirectSum (x : ⨁ n, ⨂[R]^n M) :
    TensorAlgebra.toDirectSum (ofDirectSum x) = x :=
  AlgHom.congr_fun toDirectSum_comp_ofDirectSum x

/-- The tensor algebra is isomorphic to a direct sum of tensor powers. -/
@[simps!]
/--
Definition of `equivDirectSum` / `equivDirectSum` 的定义

English:
definition equivDirectSum
  signature: : TensorAlgebra R M ≃ₐ[R] ⨁ n, ⨂[R]^n M
  body: AlgEquiv.ofAlgHom toDirectSum ofDirectSum toDirectSum_comp_ofDirectSum
    ofDirectSum_comp_toDirectSum

中文:
定义 equivDirectSum
  签名: : TensorAlgebra R M ≃ₐ[R] ⨁ n, ⨂[R]^n M
  定义体: AlgEquiv.ofAlgHom toDirectSum ofDirectSum toDirectSum_comp_ofDirectSum
    ofDirectSum_comp_toDirectSum

Depends on / 依赖: AlgEquiv, AlgEquiv.ofAlgHom, ofAlgHom, ofDirectSum, ofDirectSum_comp_toDirectSum, toDirectSum, toDirectSum_comp_ofDirectSum
-/
def equivDirectSum : TensorAlgebra R M ≃ₐ[R] ⨁ n, ⨂[R]^n M :=
  AlgEquiv.ofAlgHom toDirectSum ofDirectSum toDirectSum_comp_ofDirectSum
    ofDirectSum_comp_toDirectSum

end TensorAlgebra
