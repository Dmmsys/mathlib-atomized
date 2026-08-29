/-
Copyright (c) 2024 Jz Pan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jz Pan
-/
module

public import Mathlib.Algebra.Algebra.Operations
public import Mathlib.Algebra.Algebra.Subalgebra.Lattice
public import Mathlib.LinearAlgebra.DirectSum.Finsupp

/-!

# Some results on tensor product of submodules

## Linear maps induced by multiplication for submodules

Let `R` be a commutative ring, `S` be an `R`-algebra (not necessarily commutative).
Let `M` and `N` be `R`-submodules in `S` (`Submodule R S`). We define some linear maps
induced by the multiplication in `S` (see also `LinearMap.mul'`), which are
mainly used in the definition of linearly disjointness (`Submodule.LinearDisjoint`).

- `Submodule.mulMap`: the natural `R`-linear map `M ⊗[R] N →ₗ[R] S`
  induced by the multiplication in `S`, whose image is `M * N` (`Submodule.mulMap_range`).

- `Submodule.mulMap'`: the natural map `M ⊗[R] N →ₗ[R] M * N`
  induced by multiplication in `S`, which is surjective (`Submodule.mulMap'_surjective`).

- `Submodule.lTensorOne`, `Submodule.rTensorOne`: the natural isomorphism of `R`-modules between
  `i(R) ⊗[R] N` and `N`, resp. `M ⊗[R] i(R)` and `M`, induced by multiplication in `S`,
  here `i : R → S` is the structure map. They generalize `TensorProduct.lid`
  and `TensorProduct.rid`, as `i(R)` is not necessarily isomorphic to `R`.

  Note that we use `⊥ : Subalgebra R S` instead of `1 : Submodule R S`, since the map
  `R →ₗ[R] (1 : Submodule R S)` is not defined directly in mathlib yet.

There are also `Submodule.mulLeftMap` and `Submodule.mulRightMap`, defined in earlier files.

-/

@[expose] public section

open scoped TensorProduct

noncomputable section

universe u v w

namespace Submodule

variable {R : Type u} {S : Type v}

section Semiring

variable [CommSemiring R] [Semiring S] [Algebra R S]

variable (M N : Submodule R S)

-- can't use `LinearMap.mul' R S ∘ₗ TensorProduct.mapIncl M N` since it is not defeq to
-- `Subalgebra.mulMap` which is `(Algebra.TensorProduct.productMap A.val B.val).toLinearMap`

/--
Definition of `mulMap` / `mulMap` 的定义

English:
definition mulMap
  signature: : M otimes[R] N ->ₗ[R] S
  body: TensorProduct.lift ((LinearMap.mul R S).domRestrict₁₂ M N)

@[simp]

中文:
定义 mulMap
  签名: : M otimes[R] N ->ₗ[R] S
  定义体: TensorProduct.lift ((LinearMap.mul R S).domRestrict₁₂ M N)

@[simp]

Depends on / 依赖: LinearMap, LinearMap.mul, Substructure, Substructure.FG.of_finite, TensorProduct, TensorProduct.lift, fg_def, of_finite
-/
def mulMap : M otimes[R] N ->ₗ[R] S := TensorProduct.lift ((LinearMap.mul R S).domRestrict₁₂ M N)

@[simp]
/--
theorem `mulMap_tmul` / 定理 `mulMap_tmul`

English:
theorem mulMap_tmul
  given: (m : M) (n : N)
  statement: mulMap M N (m otimesₜ[R] n) = m.1 * n.1
  proof: rfl

中文:
定理 mulMap_tmul
  条件: (m : M) (n : N)
  结论: mulMap M N (m otimesₜ[R] n) = m.1 * n.1
  证明: rfl

Depends on / 依赖: Finite, Finite.of_finite_univ, Substructure, Substructure.FG.finite, fg_def, finite, of_finite_univ
-/
theorem mulMap_tmul (m : M) (n : N) : mulMap M N (m otimesₜ[R] n) = m.1 * n.1 := rfl

/--
theorem `mulMap_map_comp_eq` / 定理 `mulMap_map_comp_eq`

English:
theorem mulMap_map_comp_eq
  given: {T : Type w} [Semiring T] [Algebra R T] (f : S ->ₐ[R] T)
  proof: by
  ext
  simp only [TensorProduct.AlgebraTensorModule.curry_apply,
    TensorProduct.curry_apply, LinearMap.coe_comp, LinearMap.coe_restrictScalars,
    Function.comp_apply, TensorProduct.map_tmul, mulMap_tmul, LinearMap.coe_coe, map_mul]
  rfl

中文:
定理 mulMap_map_comp_eq
  条件: {T : Type w} [Semiring T] [Algebra R T] (f : S ->ₐ[R] T)
  证明: by
  ext
  simp only [TensorProduct.AlgebraTensorModule.curry_apply,
    TensorProduct.curry_apply, LinearMap.coe_comp, LinearMap.coe_restrictScalars,
    Function.comp_apply, TensorProduct.map_tmul, mulMap_tmul, LinearMap.coe_coe, map_mul]
  rfl

Depends on / 依赖: AlgebraTensorModule, Function, Function.comp_apply, LinearMap, LinearMap.coe_coe, LinearMap.coe_comp, LinearMap.coe_restrictScalars, TensorProduct, TensorProduct.AlgebraTensorModule.curry_apply, TensorProduct.curry_apply, TensorProduct.map_tmul, coe_coe, coe_comp, coe_restrictScalars, comp_apply, curry_apply, map_mul, map_tmul, mulMap_tmul
-/
theorem mulMap_map_comp_eq {T : Type w} [Semiring T] [Algebra R T] (f : S ->ₐ[R] T) :
    mulMap (M.map (f : S ->ₗ[R] T)) (N.map (f : S ->ₗ[R] T)) ∘ₗ
      TensorProduct.map ((f : S ->ₗ[R] T).submoduleMap M) ((f : S ->ₗ[R] T).submoduleMap N)
        = (f : S ->ₗ[R] T) ∘ₗ mulMap M N := by
  ext
  simp only [TensorProduct.AlgebraTensorModule.curry_apply,
    TensorProduct.curry_apply, LinearMap.coe_comp, LinearMap.coe_restrictScalars,
    Function.comp_apply, TensorProduct.map_tmul, mulMap_tmul, LinearMap.coe_coe, map_mul]
  rfl

/--
theorem `coe_mulMap_comp_eq` / 定理 `coe_mulMap_comp_eq`

English:
theorem coe_mulMap_comp_eq
  given: {T : Type w} [Semiring T] [Algebra R T] (f : S ->ₐ[R] T)
  proof: congr(⇑($(mulMap_map_comp_eq M N f)))

中文:
定理 coe_mulMap_comp_eq
  条件: {T : Type w} [Semiring T] [Algebra R T] (f : S ->ₐ[R] T)
  证明: congr(⇑($(mulMap_map_comp_eq M N f)))

Depends on / 依赖: mulMap_map_comp_eq
-/
theorem coe_mulMap_comp_eq {T : Type w} [Semiring T] [Algebra R T] (f : S ->ₐ[R] T) :
    mulMap (M.map (f : S ->ₗ[R] T)) (N.map (f : S ->ₗ[R] T)) ∘
      TensorProduct.map ((f : S ->ₗ[R] T).submoduleMap M) ((f : S ->ₗ[R] T).submoduleMap N)
        = f ∘ mulMap M N :=
  congr(⇑($(mulMap_map_comp_eq M N f)))

/--
theorem `mulMap_op` / 定理 `mulMap_op`

English:
theorem mulMap_op
  proof: TensorProduct.ext' fun _ _ => rfl

中文:
定理 mulMap_op
  证明: TensorProduct.ext' fun _ _ => rfl

Depends on / 依赖: TensorProduct, TensorProduct.ext
-/
theorem mulMap_op :
    mulMap (equivOpposite.symm (MulOpposite.op M)) (equivOpposite.symm (MulOpposite.op N)) =
    (MulOpposite.opLinearEquiv R).toLinearMap ∘ₗ mulMap N M ∘ₗ
    (TensorProduct.congr
      (LinearEquiv.ofSubmodule' (MulOpposite.opLinearEquiv R).symm M)
      (LinearEquiv.ofSubmodule' (MulOpposite.opLinearEquiv R).symm N) ≪≫ₗ
    TensorProduct.comm R M N).toLinearMap :=
  TensorProduct.ext' fun _ _ => rfl

/--
theorem `mulMap_comm_of_commute` / 定理 `mulMap_comm_of_commute`

English:
theorem mulMap_comm_of_commute
  given: (hc : forall (m : M) (n : N), Commute m.1 n.1)
  proof: by
  refine TensorProduct.ext' fun n m => ?_
  simp_rw [LinearMap.comp_apply, LinearEquiv.coe_coe, TensorProduct.comm_tmul, mulMap_tmul]
  exact (hc m n).symm

中文:
定理 mulMap_comm_of_commute
  条件: (hc : 对任意 (m : M) (n : N), Commute m.1 n.1)
  证明: by
  refine TensorProduct.ext' fun n m => ?_
  simp_rw [LinearMap.comp_apply, LinearEquiv.coe_coe, TensorProduct.comm_tmul, mulMap_tmul]
  exact (hc m n).symm

Depends on / 依赖: LinearEquiv, LinearEquiv.coe_coe, LinearMap, LinearMap.comp_apply, TensorProduct, TensorProduct.comm_tmul, TensorProduct.ext, coe_coe, comm_tmul, comp_apply, mulMap_tmul, simp_rw
-/
theorem mulMap_comm_of_commute (hc : forall (m : M) (n : N), Commute m.1 n.1) :
    mulMap N M = mulMap M N ∘ₗ TensorProduct.comm R N M := by
  refine TensorProduct.ext' fun n m => ?_
  simp_rw [LinearMap.comp_apply, LinearEquiv.coe_coe, TensorProduct.comm_tmul, mulMap_tmul]
  exact (hc m n).symm

variable {M} in
/--
theorem `mulMap_comp_rTensor` / 定理 `mulMap_comp_rTensor`

English:
theorem mulMap_comp_rTensor
  given: {M' : Submodule R S} (hM : M' <= M)
  proof: TensorProduct.ext' fun _ _ => rfl

中文:
定理 mulMap_comp_rTensor
  条件: {M' : Submodule R S} (hM : M' <= M)
  证明: TensorProduct.ext' fun _ _ => rfl

Depends on / 依赖: TensorProduct, TensorProduct.ext
-/
theorem mulMap_comp_rTensor {M' : Submodule R S} (hM : M' <= M) :
    mulMap M N ∘ₗ (inclusion hM).rTensor N = mulMap M' N :=
  TensorProduct.ext' fun _ _ => rfl

variable {N} in
/--
theorem `mulMap_comp_lTensor` / 定理 `mulMap_comp_lTensor`

English:
theorem mulMap_comp_lTensor
  given: {N' : Submodule R S} (hN : N' <= N)
  proof: TensorProduct.ext' fun _ _ => rfl

中文:
定理 mulMap_comp_lTensor
  条件: {N' : Submodule R S} (hN : N' <= N)
  证明: TensorProduct.ext' fun _ _ => rfl

Depends on / 依赖: TensorProduct, TensorProduct.ext
-/
theorem mulMap_comp_lTensor {N' : Submodule R S} (hN : N' <= N) :
    mulMap M N ∘ₗ (inclusion hN).lTensor M = mulMap M N' :=
  TensorProduct.ext' fun _ _ => rfl

variable {M N} in
/--
theorem `mulMap_comp_map_inclusion` / 定理 `mulMap_comp_map_inclusion`

English:
theorem mulMap_comp_map_inclusion
  given: {M' N' : Submodule R S} (hM : M' <= M) (hN : N' <= N)
  proof: TensorProduct.ext' fun _ _ => rfl

中文:
定理 mulMap_comp_map_inclusion
  条件: {M' N' : Submodule R S} (hM : M' <= M) (hN : N' <= N)
  证明: TensorProduct.ext' fun _ _ => rfl

Depends on / 依赖: TensorProduct, TensorProduct.ext
-/
theorem mulMap_comp_map_inclusion {M' N' : Submodule R S} (hM : M' <= M) (hN : N' <= N) :
    mulMap M N ∘ₗ TensorProduct.map (inclusion hM) (inclusion hN) = mulMap M' N' :=
  TensorProduct.ext' fun _ _ => rfl

/--
theorem `mulMap_eq_mul'_comp_mapIncl` / 定理 `mulMap_eq_mul'_comp_mapIncl`

English:
theorem mulMap_eq_mul'_comp_mapIncl
  statement: mulMap M N = .mul' R S ∘ₗ TensorProduct.mapIncl M N
  proof: TensorProduct.ext' fun _ _ => rfl

中文:
定理 mulMap_eq_mul'_comp_mapIncl
  结论: mulMap M N = .mul' R S ∘ₗ TensorProduct.mapIncl M N
  证明: TensorProduct.ext' fun _ _ => rfl

Depends on / 依赖: TensorProduct, TensorProduct.ext, cg_def, fg_def
-/
theorem mulMap_eq_mul'_comp_mapIncl : mulMap M N = .mul' R S ∘ₗ TensorProduct.mapIncl M N :=
  TensorProduct.ext' fun _ _ => rfl

/--
theorem `mulMap_range` / 定理 `mulMap_range`

English:
theorem mulMap_range
  statement: LinearMap.range (mulMap M N) = M * N
  proof: by
  refine le_antisymm ?_ (mul_le.2 fun m hm n hn => ⟨⟨m, hm⟩ otimesₜ[R] ⟨n, hn⟩, rfl⟩)
  rintro _ ⟨x, rfl⟩
  induction x with
  | zero => rw [map_zero]; exact zero_mem _
  | tmul a b => exact mul_mem_mul a.2 b.2
  | add a b ha hb => rw [map_add]; exact add_mem ha hb

中文:
定理 mulMap_range
  结论: LinearMap.range (mulMap M N) = M * N
  证明: by
  refine le_antisymm ?_ (mul_le.2 fun m hm n hn => ⟨⟨m, hm⟩ otimesₜ[R] ⟨n, hn⟩, rfl⟩)
  rintro _ ⟨x, rfl⟩
  induction x with
  | zero => rw [map_zero]; exact zero_mem _
  | tmul a b => exact mul_mem_mul a.2 b.2
  | add a b ha hb => rw [map_add]; exact add_mem ha hb

Depends on / 依赖: add_mem, cg_of_fg, le_antisymm, map_add, map_zero, mul_le, mul_mem_mul, zero_mem
-/
theorem mulMap_range : LinearMap.range (mulMap M N) = M * N := by
  refine le_antisymm ?_ (mul_le.2 fun m hm n hn => ⟨⟨m, hm⟩ otimesₜ[R] ⟨n, hn⟩, rfl⟩)
  rintro _ ⟨x, rfl⟩
  induction x with
  | zero => rw [map_zero]; exact zero_mem _
  | tmul a b => exact mul_mem_mul a.2 b.2
  | add a b ha hb => rw [map_add]; exact add_mem ha hb

/--
Definition of `mulMap'` / `mulMap'` 的定义

English:
definition mulMap'
  signature: : M otimes[R] N ->ₗ[R] ↥(M * N)
  body: (LinearEquiv.ofEq _ _ (mulMap_range M N)).toLinearMap ∘ₗ (mulMap M N).rangeRestrict

中文:
定义 mulMap'
  签名: : M otimes[R] N ->ₗ[R] ↥(M * N)
  定义体: (LinearEquiv.ofEq _ _ (mulMap_range M N)).toLinearMap ∘ₗ (mulMap M N).rangeRestrict

Depends on / 依赖: LinearEquiv, LinearEquiv.ofEq, mulMap, mulMap_range, rangeRestrict, toLinearMap
-/
def mulMap' : M otimes[R] N ->ₗ[R] ↥(M * N) :=
  (LinearEquiv.ofEq _ _ (mulMap_range M N)).toLinearMap ∘ₗ (mulMap M N).rangeRestrict

variable {M N} in
@[simp]
/--
theorem `val_mulMap'_tmul` / 定理 `val_mulMap'_tmul`

English:
theorem val_mulMap'_tmul
  given: (m : M) (n : N)
  statement: (mulMap' M N (m otimesₜ[R] n) : S) = m.1 * n.1
  proof: rfl

中文:
定理 val_mulMap'_tmul
  条件: (m : M) (n : N)
  结论: (mulMap' M N (m otimesₜ[R] n) : S) = m.1 * n.1
  证明: rfl
-/
theorem val_mulMap'_tmul (m : M) (n : N) : (mulMap' M N (m otimesₜ[R] n) : S) = m.1 * n.1 := rfl

/--
theorem `mulMap'_surjective` / 定理 `mulMap'_surjective`

English:
theorem mulMap'_surjective
  statement: Function.Surjective (mulMap' M N)
  proof: by
  simp_rw [mulMap', LinearMap.coe_comp, LinearEquiv.coe_coe, EquivLike.comp_surjective,
    LinearMap.surjective_rangeRestrict]

中文:
定理 mulMap'_surjective
  结论: Function.Surjective (mulMap' M N)
  证明: by
  simp_rw [mulMap', LinearMap.coe_comp, LinearEquiv.coe_coe, EquivLike.comp_surjective,
    LinearMap.surjective_rangeRestrict]
-/
theorem mulMap'_surjective : Function.Surjective (mulMap' M N) := by
  simp_rw [mulMap', LinearMap.coe_comp, LinearEquiv.coe_coe, EquivLike.comp_surjective,
    LinearMap.surjective_rangeRestrict]

/--
Definition of `lTensorOne'` / `lTensorOne'` 的定义

English:
definition lTensorOne'
  signature: : (⊥ : Subalgebra R S) otimes[R] N ->ₗ[R] N
  body: show Subalgebra.toSubmodule ⊥ otimes[R] N ->ₗ[R] N from
    (LinearEquiv.ofEq _ _ (by rw [Algebra.toSubmodule_bot, mulMap_range, one_mul])).toLinearMap ∘ₗ
      (mulMap _ N).rangeRestrict

中文:
定义 lTensorOne'
  签名: : (⊥ : Subalgebra R S) otimes[R] N ->ₗ[R] N
  定义体: show Subalgebra.toSubmodule ⊥ otimes[R] N ->ₗ[R] N from
    (LinearEquiv.ofEq _ _ (by rw [Algebra.toSubmodule_bot, mulMap_range, one_mul])).toLinearMap ∘ₗ
      (mulMap _ N).rangeRestrict

Depends on / 依赖: Algebra, Algebra.toSubmodule_bot, LinearEquiv, LinearEquiv.ofEq, Subalgebra, Subalgebra.toSubmodule, mulMap, mulMap_range, one_mul, otimes, rangeRestrict, toLinearMap, toSubmodule, toSubmodule_bot
-/
def lTensorOne' : (⊥ : Subalgebra R S) otimes[R] N ->ₗ[R] N :=
  show Subalgebra.toSubmodule ⊥ otimes[R] N ->ₗ[R] N from
    (LinearEquiv.ofEq _ _ (by rw [Algebra.toSubmodule_bot, mulMap_range, one_mul])).toLinearMap ∘ₗ
      (mulMap _ N).rangeRestrict

variable {N} in
@[simp]
/--
theorem `lTensorOne'_tmul` / 定理 `lTensorOne'_tmul`

English:
theorem lTensorOne'_tmul
  given: (y : R) (n : N)
  proof: Subtype.val_injective by
  simp_rw [lTensorOne', LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply,
    LinearEquiv.coe_ofEq_apply, LinearMap.codRestrict_apply, SetLike.val_smul, Algebra.smul_def]
  exact mulMap_tmul _ N _ _

中文:
定理 lTensorOne'_tmul
  条件: (y : R) (n : N)
  证明: Subtype.val_injective by
  simp_rw [lTensorOne', LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply,
    LinearEquiv.coe_ofEq_apply, LinearMap.codRestrict_apply, SetLike.val_smul, Algebra.smul_def]
  exact mulMap_tmul _ N _ _
-/
theorem lTensorOne'_tmul (y : R) (n : N) :
N.lTensorOne' (algebraMap R _ y otimesₜ[R] n) = y • n := Subtype.val_injective by
  simp_rw [lTensorOne', LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply,
    LinearEquiv.coe_ofEq_apply, LinearMap.codRestrict_apply, SetLike.val_smul, Algebra.smul_def]
  exact mulMap_tmul _ N _ _

variable {N} in
@[simp]
/--
theorem `lTensorOne'_one_tmul` / 定理 `lTensorOne'_one_tmul`

English:
theorem lTensorOne'_one_tmul
  given: (n : N)
  statement: N.lTensorOne' (1 otimesₜ[R] n) = n
  proof: by
  simpa using lTensorOne'_tmul 1 n

中文:
定理 lTensorOne'_one_tmul
  条件: (n : N)
  结论: N.lTensorOne' (1 otimesₜ[R] n) = n
  证明: by
  simpa using lTensorOne'_tmul 1 n
-/
theorem lTensorOne'_one_tmul (n : N) : N.lTensorOne' (1 otimesₜ[R] n) = n := by
  simpa using lTensorOne'_tmul 1 n

/--
Definition of `lTensorOne` / `lTensorOne` 的定义

English:
definition lTensorOne
  signature: : (⊥ : Subalgebra R S) otimes[R] N ≃ₗ[R] N
  body: LinearEquiv.ofLinearMap N.lTensorOne' (TensorProduct.mk R (⊥ : Subalgebra R S) N 1)
(by ext; simp) TensorProduct.ext' fun r n => by
  change 1 otimesₜ[R] lTensorOne' N _ = r otimesₜ[R] n
  obtain ⟨x, h⟩ := Algebra.mem_bot.1 r.2
  replace h : algebraMap R _ x = r := Subtype.val_injective h
  rw [← h]

中文:
定义 lTensorOne
  签名: : (⊥ : Subalgebra R S) otimes[R] N ≃ₗ[R] N
  定义体: LinearEquiv.ofLinearMap N.lTensorOne' (TensorProduct.mk R (⊥ : Subalgebra R S) N 1)
(by ext; simp) TensorProduct.ext' fun r n => by
  change 1 otimesₜ[R] lTensorOne' N _ = r otimesₜ[R] n
  obtain ⟨x, h⟩ := Algebra.mem_bot.1 r.2
  replace h : algebraMap R _ x = r := Subtype.val_injective h
  rw [← h]

Depends on / 依赖: Algebra, Algebra.mem_bot, Algebra.smul_def, LinearEquiv, LinearEquiv.ofLinearMap, N.lTensorOne, Subalgebra, Subtype, Subtype.val_injective, TensorProduct, TensorProduct.ext, TensorProduct.mk, TensorProduct.smul_tmul, _tmul, algebraMap, lTensorOne, mem_bot, mul_one, ofLinearMap, replace
-/
def lTensorOne : (⊥ : Subalgebra R S) otimes[R] N ≃ₗ[R] N :=
  LinearEquiv.ofLinearMap N.lTensorOne' (TensorProduct.mk R (⊥ : Subalgebra R S) N 1)
(by ext; simp) TensorProduct.ext' fun r n => by
  change 1 otimesₜ[R] lTensorOne' N _ = r otimesₜ[R] n
  obtain ⟨x, h⟩ := Algebra.mem_bot.1 r.2
  replace h : algebraMap R _ x = r := Subtype.val_injective h
  rw [← h]; rw [lTensorOne'_tmul]; rw [← TensorProduct.smul_tmul]; rw [Algebra.smul_def]; rw [mul_one]

variable {N} in
@[simp]
/--
theorem `lTensorOne_tmul` / 定理 `lTensorOne_tmul`

English:
theorem lTensorOne_tmul
  given: (y : R) (n : N)
  statement: N.lTensorOne (algebraMap R _ y otimesₜ[R] n) = y • n
  proof: N.lTensorOne'_tmul y n

中文:
定理 lTensorOne_tmul
  条件: (y : R) (n : N)
  结论: N.lTensorOne (algebraMap R _ y otimesₜ[R] n) = y • n
  证明: N.lTensorOne'_tmul y n

Depends on / 依赖: N.lTensorOne, _tmul, lTensorOne
-/
theorem lTensorOne_tmul (y : R) (n : N) : N.lTensorOne (algebraMap R _ y otimesₜ[R] n) = y • n :=
  N.lTensorOne'_tmul y n

variable {N} in
@[simp]
/--
theorem `lTensorOne_one_tmul` / 定理 `lTensorOne_one_tmul`

English:
theorem lTensorOne_one_tmul
  given: (n : N)
  statement: N.lTensorOne (1 otimesₜ[R] n) = n
  proof: N.lTensorOne'_one_tmul n

中文:
定理 lTensorOne_one_tmul
  条件: (n : N)
  结论: N.lTensorOne (1 otimesₜ[R] n) = n
  证明: N.lTensorOne'_one_tmul n

Depends on / 依赖: N.lTensorOne, _one_tmul, lTensorOne
-/
theorem lTensorOne_one_tmul (n : N) : N.lTensorOne (1 otimesₜ[R] n) = n :=
  N.lTensorOne'_one_tmul n

variable {N} in
@[simp]
/--
theorem `lTensorOne_symm_apply` / 定理 `lTensorOne_symm_apply`

English:
theorem lTensorOne_symm_apply
  given: (n : N)
  statement: N.lTensorOne.symm n = 1 otimesₜ[R] n
  proof: rfl

中文:
定理 lTensorOne_symm_apply
  条件: (n : N)
  结论: N.lTensorOne.symm n = 1 otimesₜ[R] n
  证明: rfl
-/
theorem lTensorOne_symm_apply (n : N) : N.lTensorOne.symm n = 1 otimesₜ[R] n := rfl

/--
theorem `mulMap_one_left_eq` / 定理 `mulMap_one_left_eq`

English:
theorem mulMap_one_left_eq
  proof: TensorProduct.ext' fun _ _ => rfl

中文:
定理 mulMap_one_left_eq
  证明: TensorProduct.ext' fun _ _ => rfl

Depends on / 依赖: TensorProduct, TensorProduct.ext
-/
theorem mulMap_one_left_eq :
    mulMap (Subalgebra.toSubmodule ⊥) N = N.subtype ∘ₗ N.lTensorOne.toLinearMap :=
  TensorProduct.ext' fun _ _ => rfl

/--
Definition of `rTensorOne'` / `rTensorOne'` 的定义

English:
definition rTensorOne'
  signature: : M otimes[R] (⊥ : Subalgebra R S) ->ₗ[R] M
  body: show M otimes[R] Subalgebra.toSubmodule ⊥ ->ₗ[R] M from
    (LinearEquiv.ofEq _ _ (by rw [Algebra.toSubmodule_bot, mulMap_range, mul_one])).toLinearMap ∘ₗ
      (mulMap M _).rangeRestrict

中文:
定义 rTensorOne'
  签名: : M otimes[R] (⊥ : Subalgebra R S) ->ₗ[R] M
  定义体: show M otimes[R] Subalgebra.toSubmodule ⊥ ->ₗ[R] M from
    (LinearEquiv.ofEq _ _ (by rw [Algebra.toSubmodule_bot, mulMap_range, mul_one])).toLinearMap ∘ₗ
      (mulMap M _).rangeRestrict

Depends on / 依赖: Algebra, Algebra.toSubmodule_bot, LinearEquiv, LinearEquiv.ofEq, Subalgebra, Subalgebra.toSubmodule, mulMap, mulMap_range, mul_one, otimes, rangeRestrict, toLinearMap, toSubmodule, toSubmodule_bot
-/
def rTensorOne' : M otimes[R] (⊥ : Subalgebra R S) ->ₗ[R] M :=
  show M otimes[R] Subalgebra.toSubmodule ⊥ ->ₗ[R] M from
    (LinearEquiv.ofEq _ _ (by rw [Algebra.toSubmodule_bot, mulMap_range, mul_one])).toLinearMap ∘ₗ
      (mulMap M _).rangeRestrict

variable {M} in
@[simp]
/--
theorem `rTensorOne'_tmul` / 定理 `rTensorOne'_tmul`

English:
theorem rTensorOne'_tmul
  given: (y : R) (m : M)
  proof: Subtype.val_injective by
  simp_rw [rTensorOne', LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply,
    LinearEquiv.coe_ofEq_apply, LinearMap.codRestrict_apply, SetLike.val_smul]
  rw [Algebra.smul_def]; rw [Algebra.commutes]
  exact mulMap_tmul M _ _ _

中文:
定理 rTensorOne'_tmul
  条件: (y : R) (m : M)
  证明: Subtype.val_injective by
  simp_rw [rTensorOne', LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply,
    LinearEquiv.coe_ofEq_apply, LinearMap.codRestrict_apply, SetLike.val_smul]
  rw [Algebra.smul_def]; rw [Algebra.commutes]
  exact mulMap_tmul M _ _ _
-/
theorem rTensorOne'_tmul (y : R) (m : M) :
M.rTensorOne' (m otimesₜ[R] algebraMap R _ y) = y • m := Subtype.val_injective by
  simp_rw [rTensorOne', LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply,
    LinearEquiv.coe_ofEq_apply, LinearMap.codRestrict_apply, SetLike.val_smul]
  rw [Algebra.smul_def]; rw [Algebra.commutes]
  exact mulMap_tmul M _ _ _

variable {M} in
@[simp]
/--
theorem `rTensorOne'_tmul_one` / 定理 `rTensorOne'_tmul_one`

English:
theorem rTensorOne'_tmul_one
  given: (m : M)
  statement: M.rTensorOne' (m otimesₜ[R] 1) = m
  proof: by
  simpa using rTensorOne'_tmul 1 m

中文:
定理 rTensorOne'_tmul_one
  条件: (m : M)
  结论: M.rTensorOne' (m otimesₜ[R] 1) = m
  证明: by
  simpa using rTensorOne'_tmul 1 m
-/
theorem rTensorOne'_tmul_one (m : M) : M.rTensorOne' (m otimesₜ[R] 1) = m := by
  simpa using rTensorOne'_tmul 1 m

/--
Definition of `rTensorOne` / `rTensorOne` 的定义

English:
definition rTensorOne
  signature: : M otimes[R] (⊥ : Subalgebra R S) ≃ₗ[R] M
  body: LinearEquiv.ofLinearMap M.rTensorOne' ((TensorProduct.comm R _ _).toLinearMap ∘ₗ
    TensorProduct.mk R (⊥ : Subalgebra R S) M 1) (by ext; simp) <| TensorProduct.ext' fun n r => by
  change rTensorOne' M _ otimesₜ[R] 1 = n otimesₜ[R] r
  obtain ⟨x, h⟩ := Algebra.mem_bot.1 r.2
  replace h : algebraMa

中文:
定义 rTensorOne
  签名: : M otimes[R] (⊥ : Subalgebra R S) ≃ₗ[R] M
  定义体: LinearEquiv.ofLinearMap M.rTensorOne' ((TensorProduct.comm R _ _).toLinearMap ∘ₗ
    TensorProduct.mk R (⊥ : Subalgebra R S) M 1) (by ext; simp) <| TensorProduct.ext' fun n r => by
  change rTensorOne' M _ otimesₜ[R] 1 = n otimesₜ[R] r
  obtain ⟨x, h⟩ := Algebra.mem_bot.1 r.2
  replace h : algebraMa

Depends on / 依赖: Algebra, Algebra.mem_bot, Algebra.smul_def, LinearEquiv, LinearEquiv.ofLinearMap, M.rTensorOne, Subalgebra, Subtype, Subtype.val_injective, TensorProduct, TensorProduct.comm, TensorProduct.ext, TensorProduct.mk, TensorProduct.smul_tmul, _tmul, algebraMap, mem_bot, mul_one, ofLinearMap, rTensorOne
-/
def rTensorOne : M otimes[R] (⊥ : Subalgebra R S) ≃ₗ[R] M :=
  LinearEquiv.ofLinearMap M.rTensorOne' ((TensorProduct.comm R _ _).toLinearMap ∘ₗ
    TensorProduct.mk R (⊥ : Subalgebra R S) M 1) (by ext; simp) <| TensorProduct.ext' fun n r => by
  change rTensorOne' M _ otimesₜ[R] 1 = n otimesₜ[R] r
  obtain ⟨x, h⟩ := Algebra.mem_bot.1 r.2
  replace h : algebraMap R _ x = r := Subtype.val_injective h
  rw [← h]; rw [rTensorOne'_tmul]; rw [TensorProduct.smul_tmul]; rw [Algebra.smul_def]; rw [mul_one]

variable {M} in
@[simp]
/--
theorem `rTensorOne_tmul` / 定理 `rTensorOne_tmul`

English:
theorem rTensorOne_tmul
  given: (y : R) (m : M)
  statement: M.rTensorOne (m otimesₜ[R] algebraMap R _ y) = y • m
  proof: M.rTensorOne'_tmul y m

中文:
定理 rTensorOne_tmul
  条件: (y : R) (m : M)
  结论: M.rTensorOne (m otimesₜ[R] algebraMap R _ y) = y • m
  证明: M.rTensorOne'_tmul y m

Depends on / 依赖: M.rTensorOne, _tmul, rTensorOne
-/
theorem rTensorOne_tmul (y : R) (m : M) : M.rTensorOne (m otimesₜ[R] algebraMap R _ y) = y • m :=
  M.rTensorOne'_tmul y m

variable {M} in
@[simp]
/--
theorem `rTensorOne_tmul_one` / 定理 `rTensorOne_tmul_one`

English:
theorem rTensorOne_tmul_one
  given: (m : M)
  statement: M.rTensorOne (m otimesₜ[R] 1) = m
  proof: M.rTensorOne'_tmul_one m

中文:
定理 rTensorOne_tmul_one
  条件: (m : M)
  结论: M.rTensorOne (m otimesₜ[R] 1) = m
  证明: M.rTensorOne'_tmul_one m

Depends on / 依赖: M.rTensorOne, _tmul_one, rTensorOne
-/
theorem rTensorOne_tmul_one (m : M) : M.rTensorOne (m otimesₜ[R] 1) = m :=
  M.rTensorOne'_tmul_one m

variable {M} in
@[simp]
/--
theorem `rTensorOne_symm_apply` / 定理 `rTensorOne_symm_apply`

English:
theorem rTensorOne_symm_apply
  given: (m : M)
  statement: M.rTensorOne.symm m = m otimesₜ[R] 1
  proof: rfl

中文:
定理 rTensorOne_symm_apply
  条件: (m : M)
  结论: M.rTensorOne.symm m = m otimesₜ[R] 1
  证明: rfl
-/
theorem rTensorOne_symm_apply (m : M) : M.rTensorOne.symm m = m otimesₜ[R] 1 := rfl

/--
theorem `mulMap_one_right_eq` / 定理 `mulMap_one_right_eq`

English:
theorem mulMap_one_right_eq
  proof: TensorProduct.ext' fun _ _ => rfl

@[simp]

中文:
定理 mulMap_one_right_eq
  证明: TensorProduct.ext' fun _ _ => rfl

@[simp]

Depends on / 依赖: TensorProduct, TensorProduct.ext
-/
theorem mulMap_one_right_eq :
    mulMap M (Subalgebra.toSubmodule ⊥) = M.subtype ∘ₗ M.rTensorOne.toLinearMap :=
  TensorProduct.ext' fun _ _ => rfl

@[simp]
/--
theorem `comm_trans_lTensorOne` / 定理 `comm_trans_lTensorOne`

English:
theorem comm_trans_lTensorOne
  proof: by
refine LinearEquiv.toLinearMap_injective TensorProduct.ext' fun m r => ?_
  obtain ⟨x, h⟩ := Algebra.mem_bot.1 r.2
  replace h : algebraMap R _ x = r := Subtype.val_injective h
  rw [← h]; simp

@[simp]

中文:
定理 comm_trans_lTensorOne
  证明: by
refine LinearEquiv.toLinearMap_injective TensorProduct.ext' fun m r => ?_
  obtain ⟨x, h⟩ := Algebra.mem_bot.1 r.2
  replace h : algebraMap R _ x = r := Subtype.val_injective h
  rw [← h]; simp

@[simp]

Depends on / 依赖: Algebra, Algebra.mem_bot, LinearEquiv, LinearEquiv.toLinearMap_injective, Subtype, Subtype.val_injective, TensorProduct, TensorProduct.ext, algebraMap, mem_bot, replace, toLinearMap_injective, val_injective
-/
theorem comm_trans_lTensorOne :
    (TensorProduct.comm R _ _).trans M.lTensorOne = M.rTensorOne := by
refine LinearEquiv.toLinearMap_injective TensorProduct.ext' fun m r => ?_
  obtain ⟨x, h⟩ := Algebra.mem_bot.1 r.2
  replace h : algebraMap R _ x = r := Subtype.val_injective h
  rw [← h]; simp

@[simp]
/--
theorem `comm_trans_rTensorOne` / 定理 `comm_trans_rTensorOne`

English:
theorem comm_trans_rTensorOne
  proof: by
refine LinearEquiv.toLinearMap_injective TensorProduct.ext' fun r m => ?_
  obtain ⟨x, h⟩ := Algebra.mem_bot.1 r.2
  replace h : algebraMap R _ x = r := Subtype.val_injective h
  rw [← h]; simp

中文:
定理 comm_trans_rTensorOne
  证明: by
refine LinearEquiv.toLinearMap_injective TensorProduct.ext' fun r m => ?_
  obtain ⟨x, h⟩ := Algebra.mem_bot.1 r.2
  replace h : algebraMap R _ x = r := Subtype.val_injective h
  rw [← h]; simp

Depends on / 依赖: Algebra, Algebra.mem_bot, LinearEquiv, LinearEquiv.toLinearMap_injective, Subtype, Subtype.val_injective, TensorProduct, TensorProduct.ext, algebraMap, mem_bot, replace, toLinearMap_injective, val_injective
-/
theorem comm_trans_rTensorOne :
    (TensorProduct.comm R _ _).trans M.rTensorOne = M.lTensorOne := by
refine LinearEquiv.toLinearMap_injective TensorProduct.ext' fun r m => ?_
  obtain ⟨x, h⟩ := Algebra.mem_bot.1 r.2
  replace h : algebraMap R _ x = r := Subtype.val_injective h
  rw [← h]; simp

variable {M} in
/--
theorem `mulLeftMap_eq_mulMap_comp` / 定理 `mulLeftMap_eq_mulMap_comp`

English:
theorem mulLeftMap_eq_mulMap_comp
  given: {ι : Type*} [DecidableEq ι] (m : ι -> M)
  proof: by
  ext; simp

中文:
定理 mulLeftMap_eq_mulMap_comp
  条件: {ι : 类型} [DecidableEq ι] (m : ι -> M)
  证明: by
  ext; simp
-/
theorem mulLeftMap_eq_mulMap_comp {ι : Type*} [DecidableEq ι] (m : ι -> M) :
    mulLeftMap N m = mulMap M N ∘ₗ LinearMap.rTensor N (Finsupp.linearCombination R m) ∘ₗ
      (TensorProduct.finsuppScalarLeft R N ι).symm.toLinearMap := by
  ext; simp

variable {N} in
/--
theorem `mulRightMap_eq_mulMap_comp` / 定理 `mulRightMap_eq_mulMap_comp`

English:
theorem mulRightMap_eq_mulMap_comp
  given: {ι : Type*} [DecidableEq ι] (n : ι -> N)
  proof: by
  ext; simp

中文:
定理 mulRightMap_eq_mulMap_comp
  条件: {ι : 类型} [DecidableEq ι] (n : ι -> N)
  证明: by
  ext; simp
-/
theorem mulRightMap_eq_mulMap_comp {ι : Type*} [DecidableEq ι] (n : ι -> N) :
    mulRightMap M n = mulMap M N ∘ₗ LinearMap.lTensor M (Finsupp.linearCombination R n) ∘ₗ
      (TensorProduct.finsuppScalarRight R R M ι).symm.toLinearMap := by
  ext; simp

end Semiring

section CommSemiring

variable [CommSemiring R] [CommSemiring S] [Algebra R S]

variable (M N : Submodule R S)

/--
theorem `mulMap_comm` / 定理 `mulMap_comm`

English:
theorem mulMap_comm
  statement: mulMap N M = (mulMap M N).comp (TensorProduct.comm R N M).toLinearMap
  proof: mulMap_comm_of_commute M N fun _ _ => mul_comm _ _

中文:
定理 mulMap_comm
  结论: mulMap N M = (mulMap M N).comp (TensorProduct.comm R N M).toLinearMap
  证明: mulMap_comm_of_commute M N fun _ _ => mul_comm _ _

Depends on / 依赖: mulMap_comm_of_commute, mul_comm
-/
theorem mulMap_comm : mulMap N M = (mulMap M N).comp (TensorProduct.comm R N M).toLinearMap :=
  mulMap_comm_of_commute M N fun _ _ => mul_comm _ _

end CommSemiring

end Submodule
