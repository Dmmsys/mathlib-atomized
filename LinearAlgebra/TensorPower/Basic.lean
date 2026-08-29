/-
Copyright (c) 2021 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser
-/
module

public import Mathlib.LinearAlgebra.PiTensorProduct.Basic
public import Mathlib.Logic.Equiv.Fin.Basic
public import Mathlib.Algebra.DirectSum.Algebra

/-!
# Tensor power of a semimodule over a commutative semiring

We define the `n`th tensor power of `M` as the n-ary tensor product indexed by `Fin n` of `M`,
`⨂[R] (i : Fin n), M`. This is a special case of `PiTensorProduct`.

This file introduces the notation `⨂[R]^n M` for `TensorPower R n M`, which in turn is an
abbreviation for `⨂[R] i : Fin n, M`.

## Main definitions:

* `TensorPower.gsemiring`: the tensor powers form a graded semiring.
* `TensorPower.galgebra`: the tensor powers form a graded algebra.

## Implementation notes

In this file we use `ₜ1` and `ₜ*` as local notation for the graded multiplicative structure on
tensor powers. Elsewhere, using `1` and `*` on `GradedMonoid` should be preferred.
-/

@[expose] public section

open scoped TensorProduct

/--
Definition of `TensorPower` / `TensorPower` 的定义

English:
abbreviation TensorPower
  signature: (R : Type*) (n : Nat) (M : Type*) [CommSemiring R] [AddCommMonoid M]
  body: ⨂[R] _ : Fin n, M

中文:
缩写 TensorPower
  签名: (R : 类型) (n : 自然数) (M : 类型) [交换半环 R] [加法交换幺半群 M]
  定义体: ⨂[R] _ : Fin n, M
-/
abbrev TensorPower (R : Type*) (n : Nat) (M : Type*) [CommSemiring R] [AddCommMonoid M]
    [Module R M] : Type _ :=
  ⨂[R] _ : Fin n, M

variable {R : Type*} {M : Type*} [CommSemiring R] [AddCommMonoid M] [Module R M]

@[inherit_doc] scoped[TensorProduct] notation:max "⨂[" R "]^" n:arg => TensorPower R n

namespace PiTensorProduct

set_option backward.isDefEq.respectTransparency false in
/-- Two dependent pairs of tensor products are equal if their index is equal and the contents
are equal after a canonical reindexing. -/
@[ext (iff := false)]
/--
theorem `gradedMonoid_eq_of_reindex_cast` / 定理 `gradedMonoid_eq_of_reindex_cast`

English:
theorem gradedMonoid_eq_of_reindex_cast
  given: {ιι : Type*} {ι : ιι -> Type*}

中文:
定理 gradedMonoid_eq_of_reindex_cast
  条件: {ιι : 类型} {ι : ιι -> 类型}
-/
theorem gradedMonoid_eq_of_reindex_cast {ιι : Type*} {ι : ιι -> Type*} :
    forall {a b : GradedMonoid fun ii => ⨂[R] _ : ι ii, M} (h : a.fst = b.fst),
      reindex R (fun _ => M) (Equiv.cast <| congr_arg ι h) a.snd = b.snd -> a = b
  | ⟨ai, a⟩, ⟨bi, b⟩ => fun (hi : ai = bi) (h : reindex R (fun _ => M) _ a = b) => by
    subst hi
    simp_all

end PiTensorProduct

namespace TensorPower

open scoped TensorProduct DirectSum

open PiTensorProduct

/--
Instance `gOne` / 实例 `gOne`

English:
instance gOne
  signature: : GradedMonoid.GOne fun i => ⨂[R]^i M where one
  body: tprod R @Fin.elim0 M

local notation "ₜ1" => @GradedMonoid.GOne.one Nat (fun i => ⨂[R]^i M) _ _

中文:
实例 gOne
  签名: : 分次幺半群.GOne fun i => ⨂[R]^i M where one
  定义体: tprod R @Fin.elim0 M

local notation "ₜ1" => @GradedMonoid.GOne.one Nat (fun i => ⨂[R]^i M) _ _

Depends on / 依赖: Fin.elim0
-/
instance gOne : GradedMonoid.GOne fun i => ⨂[R]^i M where one := tprod R @Fin.elim0 M

local notation "ₜ1" => @GradedMonoid.GOne.one Nat (fun i => ⨂[R]^i M) _ _

/--
theorem `gOne_def` / 定理 `gOne_def`

English:
theorem gOne_def
  statement: ₜ1 = tprod R (@Fin.elim0 M)
  proof: rfl

中文:
定理 gOne_def
  结论: ₜ1 = tprod R (@有限集.elim0 M)
  证明: rfl
-/
theorem gOne_def : ₜ1 = tprod R (@Fin.elim0 M) :=
  rfl

/--
Definition of `mulEquiv` / `mulEquiv` 的定义

English:
definition mulEquiv
  signature: {n m : Nat}
  body: (tmulEquiv R M).trans (reindex R (fun _ => M) finSumFinEquiv)

中文:
定义 mulEquiv
  签名: {n m : 自然数}
  定义体: (tmulEquiv R M).trans (reindex R (fun _ => M) finSumFinEquiv)

Depends on / 依赖: finSumFinEquiv, reindex, tmulEquiv
-/
def mulEquiv {n m : Nat} : ⨂[R]^n M otimes[R] (⨂[R]^m) M ≃ₗ[R] (⨂[R]^(n + m)) M :=
  (tmulEquiv R M).trans (reindex R (fun _ => M) finSumFinEquiv)

/--
Instance `gMul` / 实例 `gMul`

English:
instance gMul
  signature: : GradedMonoid.GMul fun i => ⨂[R]^i M where
  body: (TensorProduct.mk R _ _).compr₂ (↑(mulEquiv : _ ≃ₗ[R] (⨂[R]^(i + j)) M)) a b

local infixl:70 " ₜ* " => @GradedMonoid.GMul.mul Nat (fun i => ⨂[R]^i M) _ _ _ _

中文:
实例 gMul
  签名: : 分次幺半群.GMul fun i => ⨂[R]^i M where
  定义体: (TensorProduct.mk R _ _).compr₂ (↑(mulEquiv : _ ≃ₗ[R] (⨂[R]^(i + j)) M)) a b

local infixl:70 " ₜ* " => @GradedMonoid.GMul.mul Nat (fun i => ⨂[R]^i M) _ _ _ _

Depends on / 依赖: TensorProduct, TensorProduct.mk, mulEquiv
-/
instance gMul : GradedMonoid.GMul fun i => ⨂[R]^i M where
  mul {i j} a b :=
    (TensorProduct.mk R _ _).compr₂ (↑(mulEquiv : _ ≃ₗ[R] (⨂[R]^(i + j)) M)) a b

local infixl:70 " ₜ* " => @GradedMonoid.GMul.mul Nat (fun i => ⨂[R]^i M) _ _ _ _

/--
theorem `gMul_def` / 定理 `gMul_def`

English:
theorem gMul_def
  given: {i j} (a : ⨂[R]^i M) (b : (⨂[R]^j) M)
  proof: rfl

中文:
定理 gMul_def
  条件: {i j} (a : ⨂[R]^i M) (b : (⨂[R]^j) M)
  证明: rfl
-/
theorem gMul_def {i j} (a : ⨂[R]^i M) (b : (⨂[R]^j) M) :
    a ₜ* b = @mulEquiv R M _ _ _ i j (a otimesₜ b) :=
  rfl

/--
theorem `gMul_eq_coe_linearMap` / 定理 `gMul_eq_coe_linearMap`

English:
theorem gMul_eq_coe_linearMap
  given: {i j} (a : ⨂[R]^i M) (b : (⨂[R]^j) M)
  proof: rfl

中文:
定理 gMul_eq_coe_linearMap
  条件: {i j} (a : ⨂[R]^i M) (b : (⨂[R]^j) M)
  证明: rfl
-/
theorem gMul_eq_coe_linearMap {i j} (a : ⨂[R]^i M) (b : (⨂[R]^j) M) :
    a ₜ* b = ((TensorProduct.mk R _ _).compr₂ ↑(mulEquiv : _ ≃ₗ[R] (⨂[R]^(i + j)) M) :
      ⨂[R]^i M ->ₗ[R] (⨂[R]^j) M ->ₗ[R] (⨂[R]^(i + j)) M) a b :=
  rfl

variable (R M)

/--
Definition of `cast` / `cast` 的定义

English:
definition cast
  signature: {i j} (h : i = j)
  body: reindex R (fun _ => M) (finCongr h)

中文:
定义 cast
  签名: {i j} (h : i = j)
  定义体: reindex R (fun _ => M) (finCongr h)

Depends on / 依赖: finCongr, reindex
-/
def cast {i j} (h : i = j) : ⨂[R]^i M ≃ₗ[R] (⨂[R]^j) M := reindex R (fun _ => M) (finCongr h)

/--
theorem `cast_tprod` / 定理 `cast_tprod`

English:
theorem cast_tprod
  given: {i j} (h : i = j) (a : Fin i -> M)
  proof: reindex_tprod _ _

@[simp]

中文:
定理 cast_tprod
  条件: {i j} (h : i = j) (a : 有限集 i -> M)
  证明: reindex_tprod _ _

@[simp]

Depends on / 依赖: reindex_tprod
-/
theorem cast_tprod {i j} (h : i = j) (a : Fin i -> M) :
    cast R M h (tprod R a) = tprod R (a ∘ Fin.cast h.symm) :=
  reindex_tprod _ _

@[simp]
/--
theorem `cast_refl` / 定理 `cast_refl`

English:
theorem cast_refl
  given: {i} (h : i = i)
  statement: cast R M h = LinearEquiv.refl _ _
  proof: (congr_arg (reindex R fun _ => M) <| finCongr_refl h).trans reindex_refl

@[simp]

中文:
定理 cast_refl
  条件: {i} (h : i = i)
  结论: cast R M h = 线性等价.refl _ _
  证明: (congr_arg (reindex R fun _ => M) <| finCongr_refl h).trans reindex_refl

@[simp]

Depends on / 依赖: congr_arg, finCongr_refl, reindex, reindex_refl
-/
theorem cast_refl {i} (h : i = i) : cast R M h = LinearEquiv.refl _ _ :=
  (congr_arg (reindex R fun _ => M) <| finCongr_refl h).trans reindex_refl

@[simp]
/--
theorem `cast_symm` / 定理 `cast_symm`

English:
theorem cast_symm
  given: {i j} (h : i = j)
  statement: (cast R M h).symm = cast R M h.symm
  proof: reindex_symm _

@[simp]

中文:
定理 cast_symm
  条件: {i j} (h : i = j)
  结论: (cast R M h).symm = cast R M h.symm
  证明: reindex_symm _

@[simp]

Depends on / 依赖: reindex_symm
-/
theorem cast_symm {i j} (h : i = j) : (cast R M h).symm = cast R M h.symm :=
  reindex_symm _

@[simp]
/--
theorem `cast_trans` / 定理 `cast_trans`

English:
theorem cast_trans
  given: {i j k} (h : i = j) (h' : j = k)
  proof: reindex_trans _ _

中文:
定理 cast_trans
  条件: {i j k} (h : i = j) (h' : j = k)
  证明: reindex_trans _ _

Depends on / 依赖: reindex_trans
-/
theorem cast_trans {i j k} (h : i = j) (h' : j = k) :
    (cast R M h).trans (cast R M h') = cast R M (h.trans h') :=
  reindex_trans _ _

variable {R M}

@[simp]
/--
theorem `cast_cast` / 定理 `cast_cast`

English:
theorem cast_cast
  given: {i j k} (h : i = j) (h' : j = k) (a : ⨂[R]^i M)
  proof: reindex_reindex _ _ _

@[ext (iff := false)]

中文:
定理 cast_cast
  条件: {i j k} (h : i = j) (h' : j = k) (a : ⨂[R]^i M)
  证明: reindex_reindex _ _ _

@[ext (iff := false)]

Depends on / 依赖: reindex_reindex
-/
theorem cast_cast {i j k} (h : i = j) (h' : j = k) (a : ⨂[R]^i M) :
    cast R M h' (cast R M h a) = cast R M (h.trans h') a :=
  reindex_reindex _ _ _

@[ext (iff := false)]
/--
theorem `gradedMonoid_eq_of_cast` / 定理 `gradedMonoid_eq_of_cast`

English:
theorem gradedMonoid_eq_of_cast
  statement: {a b : GradedMonoid fun n => ⨂[R] _ : Fin n, M} (h : a.fst = b.fst)
  proof: by
  refine gradedMonoid_eq_of_reindex_cast h ?_
  rw [cast] at h2
  rw [← finCongr_eq_equivCast]; rw [← h2]

中文:
定理 gradedMonoid_eq_of_cast
  结论: {a b : 分次幺半群 fun n => ⨂[R] _ : 有限集 n, M} (h : a.fst = b.fst)
  证明: by
  refine gradedMonoid_eq_of_reindex_cast h ?_
  rw [cast] at h2
  rw [← finCongr_eq_equivCast]; rw [← h2]

Depends on / 依赖: finCongr_eq_equivCast, gradedMonoid_eq_of_reindex_cast
-/
theorem gradedMonoid_eq_of_cast {a b : GradedMonoid fun n => ⨂[R] _ : Fin n, M} (h : a.fst = b.fst)
    (h2 : cast R M h a.snd = b.snd) : a = b := by
  refine gradedMonoid_eq_of_reindex_cast h ?_
  rw [cast] at h2
  rw [← finCongr_eq_equivCast]; rw [← h2]

/--
theorem `cast_eq_cast` / 定理 `cast_eq_cast`

English:
theorem cast_eq_cast
  given: {i j} (h : i = j)
  proof: by
  subst h
  rw [cast_refl]
  rfl

中文:
定理 cast_eq_cast
  条件: {i j} (h : i = j)
  证明: by
  subst h
  rw [cast_refl]
  rfl

Depends on / 依赖: cast_refl
-/
theorem cast_eq_cast {i j} (h : i = j) :
    ⇑(cast R M h) = _root_.cast (congrArg (fun i => ⨂[R]^i M) h) := by
  subst h
  rw [cast_refl]
  rfl

set_option backward.isDefEq.respectTransparency false in
variable (R) in
/--
theorem `tprod_mul_tprod` / 定理 `tprod_mul_tprod`

English:
theorem tprod_mul_tprod
  given: {na nb} (a : Fin na -> M) (b : Fin nb -> M)
  proof: by
  dsimp [gMul_def, mulEquiv]
  rw [tmulEquiv_apply R M a b]
  refine (reindex_tprod _ _).trans ?_
  congr 1
  dsimp only [Fin.append, finSumFinEquiv, Equiv.coe_fn_symm_mk]
  apply funext
  apply Fin.addCases <;> simp

中文:
定理 tprod_mul_tprod
  条件: {na nb} (a : 有限集 na -> M) (b : 有限集 nb -> M)
  证明: by
  dsimp [gMul_def, mulEquiv]
  rw [tmulEquiv_apply R M a b]
  refine (reindex_tprod _ _).trans ?_
  congr 1
  dsimp only [Fin.append, finSumFinEquiv, Equiv.coe_fn_symm_mk]
  apply funext
  apply Fin.addCases <;> simp

Depends on / 依赖: Equiv.coe_fn_symm_mk, Fin.addCases, Fin.append, addCases, append, coe_fn_symm_mk, finSumFinEquiv, gMul_def, mulEquiv, reindex_tprod, tmulEquiv_apply
-/
theorem tprod_mul_tprod {na nb} (a : Fin na -> M) (b : Fin nb -> M) :
    tprod R a ₜ* tprod R b = tprod R (Fin.append a b) := by
  dsimp [gMul_def, mulEquiv]
  rw [tmulEquiv_apply R M a b]
  refine (reindex_tprod _ _).trans ?_
  congr 1
  dsimp only [Fin.append, finSumFinEquiv, Equiv.coe_fn_symm_mk]
  apply funext
  apply Fin.addCases <;> simp

/--
theorem `one_mul` / 定理 `one_mul`

English:
theorem one_mul
  given: {n} (a : ⨂[R]^n M)
  statement: cast R M (zero_add n) (ₜ1 ₜ* a) = a
  proof: by
  rw [gMul_def]; rw [gOne_def]
  induction a using PiTensorProduct.induction_on with
  | smul_tprod r a =>
    rw [TensorProduct.tmul_smul]; rw [map_smul]; rw [map_smul]; rw [← gMul_def]; rw [tprod_mul_tprod]; rw [cast_tprod]
    congr 2 with i
    rw [Fin.elim0_append]
    refine congr_arg a (Fi

中文:
定理 one_mul
  条件: {n} (a : ⨂[R]^n M)
  结论: cast R M (zero_add n) (ₜ1 ₜ* a) = a
  证明: by
  rw [gMul_def]; rw [gOne_def]
  induction a using PiTensorProduct.induction_on with
  | smul_tprod r a =>
    rw [TensorProduct.tmul_smul]; rw [map_smul]; rw [map_smul]; rw [← gMul_def]; rw [tprod_mul_tprod]; rw [cast_tprod]
    congr 2 with i
    rw [Fin.elim0_append]
    refine congr_arg a (Fi

Depends on / 依赖: Fin.elim0_append, Fin.ext, PiTensorProduct, PiTensorProduct.induction_on, TensorProduct, TensorProduct.tmul_add, TensorProduct.tmul_smul, cast_tprod, congr_arg, elim0_append, gMul_def, gOne_def, induction_on, map_add, map_smul, smul_tprod, tmul_add, tmul_smul, tprod_mul_tprod
-/
theorem one_mul {n} (a : ⨂[R]^n M) : cast R M (zero_add n) (ₜ1 ₜ* a) = a := by
  rw [gMul_def]; rw [gOne_def]
  induction a using PiTensorProduct.induction_on with
  | smul_tprod r a =>
    rw [TensorProduct.tmul_smul]; rw [map_smul]; rw [map_smul]; rw [← gMul_def]; rw [tprod_mul_tprod]; rw [cast_tprod]
    congr 2 with i
    rw [Fin.elim0_append]
    refine congr_arg a (Fin.ext ?_)
    simp
  | add x y hx hy =>
    rw [TensorProduct.tmul_add]; rw [map_add]; rw [map_add]; rw [hx]; rw [hy]

/--
theorem `mul_one` / 定理 `mul_one`

English:
theorem mul_one
  given: {n} (a : ⨂[R]^n M)
  statement: cast R M (add_zero _) (a ₜ* ₜ1) = a
  proof: by
  rw [gMul_def]; rw [gOne_def]
  induction a using PiTensorProduct.induction_on with
  | smul_tprod r a =>
    rw [← TensorProduct.smul_tmul']; rw [map_smul]; rw [map_smul]; rw [← gMul_def]; rw [tprod_mul_tprod R a _]; rw [cast_tprod]
    simp
  | add x y hx hy =>
    rw [TensorProduct.add_tmul];

中文:
定理 mul_one
  条件: {n} (a : ⨂[R]^n M)
  结论: cast R M (add_zero _) (a ₜ* ₜ1) = a
  证明: by
  rw [gMul_def]; rw [gOne_def]
  induction a using PiTensorProduct.induction_on with
  | smul_tprod r a =>
    rw [← TensorProduct.smul_tmul']; rw [map_smul]; rw [map_smul]; rw [← gMul_def]; rw [tprod_mul_tprod R a _]; rw [cast_tprod]
    simp
  | add x y hx hy =>
    rw [TensorProduct.add_tmul];

Depends on / 依赖: PiTensorProduct, PiTensorProduct.induction_on, TensorProduct, TensorProduct.add_tmul, TensorProduct.smul_tmul, add_tmul, cast_tprod, gMul_def, gOne_def, induction_on, map_add, map_smul, smul_tmul, smul_tprod, tprod_mul_tprod
-/
theorem mul_one {n} (a : ⨂[R]^n M) : cast R M (add_zero _) (a ₜ* ₜ1) = a := by
  rw [gMul_def]; rw [gOne_def]
  induction a using PiTensorProduct.induction_on with
  | smul_tprod r a =>
    rw [← TensorProduct.smul_tmul']; rw [map_smul]; rw [map_smul]; rw [← gMul_def]; rw [tprod_mul_tprod R a _]; rw [cast_tprod]
    simp
  | add x y hx hy =>
    rw [TensorProduct.add_tmul]; rw [map_add]; rw [map_add]; rw [hx]; rw [hy]

/--
theorem `mul_assoc` / 定理 `mul_assoc`

English:
theorem mul_assoc
  given: {na nb nc} (a : (⨂[R]^na) M) (b : (⨂[R]^nb) M) (c : (⨂[R]^nc) M)
  proof: by
  let mul : forall n m : Nat, ⨂[R]^n M ->ₗ[R] (⨂[R]^m) M ->ₗ[R] (⨂[R]^(n + m)) M := fun n m =>
    (TensorProduct.mk R _ _).compr₂ ↑(mulEquiv : _ ≃ₗ[R] (⨂[R]^(n + m)) M)
  -- replace `a`, `b`, `c` with `tprod R a`, `tprod R b`, `tprod R c`
  let e : (⨂[R]^(na + nb + nc)) M ≃ₗ[R] (⨂[R]^(na + (nb +

中文:
定理 mul_assoc
  条件: {na nb nc} (a : (⨂[R]^na) M) (b : (⨂[R]^nb) M) (c : (⨂[R]^nc) M)
  证明: by
  let mul : forall n m : Nat, ⨂[R]^n M ->ₗ[R] (⨂[R]^m) M ->ₗ[R] (⨂[R]^(n + m)) M := fun n m =>
    (TensorProduct.mk R _ _).compr₂ ↑(mulEquiv : _ ≃ₗ[R] (⨂[R]^(n + m)) M)
  -- replace `a`, `b`, `c` with `tprod R a`, `tprod R b`, `tprod R c`
  let e : (⨂[R]^(na + nb + nc)) M ≃ₗ[R] (⨂[R]^(na + (nb +

Depends on / 依赖: TensorProduct, TensorProduct.mk, mulEquiv
-/
theorem mul_assoc {na nb nc} (a : (⨂[R]^na) M) (b : (⨂[R]^nb) M) (c : (⨂[R]^nc) M) :
    cast R M (add_assoc _ _ _) (a ₜ* b ₜ* c) = a ₜ* (b ₜ* c) := by
  let mul : forall n m : Nat, ⨂[R]^n M ->ₗ[R] (⨂[R]^m) M ->ₗ[R] (⨂[R]^(n + m)) M := fun n m =>
    (TensorProduct.mk R _ _).compr₂ ↑(mulEquiv : _ ≃ₗ[R] (⨂[R]^(n + m)) M)
  -- replace `a`, `b`, `c` with `tprod R a`, `tprod R b`, `tprod R c`
  let e : (⨂[R]^(na + nb + nc)) M ≃ₗ[R] (⨂[R]^(na + (nb + nc))) M := cast R M (add_assoc _ _ _)
  let lhs : (⨂[R]^na) M ->ₗ[R] (⨂[R]^nb) M ->ₗ[R] (⨂[R]^nc) M ->ₗ[R] (⨂[R]^(na + (nb + nc))) M :=
    (LinearMap.llcomp R _ _ _ ((mul _ nc).compr₂ e.toLinearMap)).comp (mul na nb)
  have lhs_eq : forall a b c, lhs a b c = e (a ₜ* b ₜ* c) := fun _ _ _ => rfl
  let rhs : (⨂[R]^na) M ->ₗ[R] (⨂[R]^nb) M ->ₗ[R] (⨂[R]^nc) M ->ₗ[R] (⨂[R]^(na + (nb + nc))) M :=
    (LinearMap.llcomp R _ _ _ (LinearMap.lflip (R := R)).toLinearMap <|
        (LinearMap.llcomp R _ _ _ (mul na _).flip).comp (mul nb nc)).flip
  have rhs_eq : forall a b c, rhs a b c = a ₜ* (b ₜ* c) := fun _ _ _ => rfl
  suffices lhs = rhs from
    LinearMap.congr_fun (LinearMap.congr_fun (LinearMap.congr_fun this a) b) c
  ext a b c
  -- clean up
  simp only [e, LinearMap.compMultilinearMap_apply, lhs_eq, rhs_eq, tprod_mul_tprod, cast_tprod]
  congr 1 with j
  rw [Fin.append_assoc]
  refine congr_arg (Fin.append a (Fin.append b c)) (Fin.ext ?_)
  rw [Fin.val_cast]; rw [Fin.val_cast]

-- for now we just use the default for the `gnpow` field as it's easier.
/--
Instance `gmonoid` / 实例 `gmonoid`

English:
instance gmonoid
  signature: : GradedMonoid.GMonoid fun i => ⨂[R]^i M
  body: { TensorPower.gMul, TensorPower.gOne with
    one_mul := fun _ => gradedMonoid_eq_of_cast (zero_add _) (one_mul _)
    mul_one := fun _ => gradedMonoid_eq_of_cast (add_zero _) (mul_one _)
    mul_assoc := fun _ _ _ => gradedMonoid_eq_of_cast (add_assoc _ _ _) (mul_assoc _ _ _) }

中文:
实例 gmonoid
  签名: : 分次幺半群.G幺半群 fun i => ⨂[R]^i M
  定义体: { TensorPower.gMul, TensorPower.gOne with
    one_mul := fun _ => gradedMonoid_eq_of_cast (zero_add _) (one_mul _)
    mul_one := fun _ => gradedMonoid_eq_of_cast (add_zero _) (mul_one _)
    mul_assoc := fun _ _ _ => gradedMonoid_eq_of_cast (add_assoc _ _ _) (mul_assoc _ _ _) }

Depends on / 依赖: TensorPower, TensorPower.gMul, TensorPower.gOne, add_assoc, add_zero, gradedMonoid_eq_of_cast, mul_assoc, mul_one, one_mul, zero_add
-/
instance gmonoid : GradedMonoid.GMonoid fun i => ⨂[R]^i M :=
  { TensorPower.gMul, TensorPower.gOne with
    one_mul := fun _ => gradedMonoid_eq_of_cast (zero_add _) (one_mul _)
    mul_one := fun _ => gradedMonoid_eq_of_cast (add_zero _) (mul_one _)
    mul_assoc := fun _ _ _ => gradedMonoid_eq_of_cast (add_assoc _ _ _) (mul_assoc _ _ _) }

/--
Definition of `algebraMap₀` / `algebraMap₀` 的定义

English:
definition algebraMap₀
  signature: : R ≃ₗ[R] (⨂[R]^0) M
  body: LinearEquiv.symm isEmptyEquiv (Fin 0)

中文:
定义 algebraMap₀
  签名: : R ≃ₗ[R] (⨂[R]^0) M
  定义体: LinearEquiv.symm isEmptyEquiv (Fin 0)

Depends on / 依赖: LinearEquiv, LinearEquiv.symm, infer_instance, isEmptyEquiv, totalVariation
-/
def algebraMap₀ : R ≃ₗ[R] (⨂[R]^0) M :=
LinearEquiv.symm isEmptyEquiv (Fin 0)

/--
theorem `algebraMap₀_eq_smul_one` / 定理 `algebraMap₀_eq_smul_one`

English:
theorem algebraMap₀_eq_smul_one
  given: (r : R)
  statement: (algebraMap₀ r : (⨂[R]^0) M) = r • ₜ1
  proof: by
  simp [algebraMap₀]; congr

中文:
定理 algebraMap₀_eq_smul_one
  条件: (r : R)
  结论: (algebraMap₀ r : (⨂[R]^0) M) = r • ₜ1
  证明: by
  simp [algebraMap₀]; congr
-/
theorem algebraMap₀_eq_smul_one (r : R) : (algebraMap₀ r : (⨂[R]^0) M) = r • ₜ1 := by
  simp [algebraMap₀]; congr

/--
theorem `algebraMap₀_one` / 定理 `algebraMap₀_one`

English:
theorem algebraMap₀_one
  statement: (algebraMap₀ 1 : (⨂[R]^0) M) = ₜ1
  proof: (algebraMap₀_eq_smul_one 1).trans (one_smul _ _)

中文:
定理 algebraMap₀_one
  结论: (algebraMap₀ 1 : (⨂[R]^0) M) = ₜ1
  证明: (algebraMap₀_eq_smul_one 1).trans (one_smul _ _)

Depends on / 依赖: one_smul
-/
theorem algebraMap₀_one : (algebraMap₀ 1 : (⨂[R]^0) M) = ₜ1 :=
  (algebraMap₀_eq_smul_one 1).trans (one_smul _ _)

/--
theorem `algebraMap₀_mul` / 定理 `algebraMap₀_mul`

English:
theorem algebraMap₀_mul
  given: {n} (r : R) (a : ⨂[R]^n M)
  proof: by
  rw [gMul_eq_coe_linearMap]; rw [algebraMap₀_eq_smul_one]; rw [LinearMap.map_smul₂]; rw [map_smul]; rw [← gMul_eq_coe_linearMap]; rw [one_mul]

中文:
定理 algebraMap₀_mul
  条件: {n} (r : R) (a : ⨂[R]^n M)
  证明: by
  rw [gMul_eq_coe_linearMap]; rw [algebraMap₀_eq_smul_one]; rw [LinearMap.map_smul₂]; rw [map_smul]; rw [← gMul_eq_coe_linearMap]; rw [one_mul]

Depends on / 依赖: LinearMap, LinearMap.map_smul, gMul_eq_coe_linearMap, map_smul, one_mul
-/
theorem algebraMap₀_mul {n} (r : R) (a : ⨂[R]^n M) :
    cast R M (zero_add _) (algebraMap₀ r ₜ* a) = r • a := by
  rw [gMul_eq_coe_linearMap]; rw [algebraMap₀_eq_smul_one]; rw [LinearMap.map_smul₂]; rw [map_smul]; rw [← gMul_eq_coe_linearMap]; rw [one_mul]

/--
theorem `mul_algebraMap₀` / 定理 `mul_algebraMap₀`

English:
theorem mul_algebraMap₀
  given: {n} (r : R) (a : ⨂[R]^n M)
  proof: by
  rw [gMul_eq_coe_linearMap]; rw [algebraMap₀_eq_smul_one]; rw [map_smul]; rw [map_smul]; rw [← gMul_eq_coe_linearMap]; rw [mul_one]

中文:
定理 mul_algebraMap₀
  条件: {n} (r : R) (a : ⨂[R]^n M)
  证明: by
  rw [gMul_eq_coe_linearMap]; rw [algebraMap₀_eq_smul_one]; rw [map_smul]; rw [map_smul]; rw [← gMul_eq_coe_linearMap]; rw [mul_one]

Depends on / 依赖: gMul_eq_coe_linearMap, map_smul, mul_one
-/
theorem mul_algebraMap₀ {n} (r : R) (a : ⨂[R]^n M) :
    cast R M (add_zero _) (a ₜ* algebraMap₀ r) = r • a := by
  rw [gMul_eq_coe_linearMap]; rw [algebraMap₀_eq_smul_one]; rw [map_smul]; rw [map_smul]; rw [← gMul_eq_coe_linearMap]; rw [mul_one]

/--
theorem `algebraMap₀_mul_algebraMap₀` / 定理 `algebraMap₀_mul_algebraMap₀`

English:
theorem algebraMap₀_mul_algebraMap₀
  given: (r s : R)
  proof: by
  rw [← smul_eq_mul]; rw [map_smul]
  exact algebraMap₀_mul r (@algebraMap₀ R M _ _ _ s)

中文:
定理 algebraMap₀_mul_algebraMap₀
  条件: (r s : R)
  证明: by
  rw [← smul_eq_mul]; rw [map_smul]
  exact algebraMap₀_mul r (@algebraMap₀ R M _ _ _ s)

Depends on / 依赖: map_smul, smul_eq_mul
-/
theorem algebraMap₀_mul_algebraMap₀ (r s : R) :
    cast R M (add_zero _) (algebraMap₀ r ₜ* algebraMap₀ s) = algebraMap₀ (r * s) := by
  rw [← smul_eq_mul]; rw [map_smul]
  exact algebraMap₀_mul r (@algebraMap₀ R M _ _ _ s)

/--
Instance `gsemiring` / 实例 `gsemiring`

English:
instance gsemiring
  signature: : DirectSum.GSemiring fun i => ⨂[R]^i M
  body: { TensorPower.gmonoid with
    mul_zero := fun _ => map_zero _
    zero_mul := fun _ => LinearMap.map_zero₂ _ _
    mul_add := fun _ _ _ => map_add _ _ _
    add_mul := fun _ _ _ => LinearMap.map_add₂ _ _ _ _
    natCast := fun n => algebraMap₀ (n : R)
    natCast_zero := by simp only [Nat.cast_zero

中文:
实例 gsemiring
  签名: : 直和.GSemiring fun i => ⨂[R]^i M
  定义体: { TensorPower.gmonoid with
    mul_zero := fun _ => map_zero _
    zero_mul := fun _ => LinearMap.map_zero₂ _ _
    mul_add := fun _ _ _ => map_add _ _ _
    add_mul := fun _ _ _ => LinearMap.map_add₂ _ _ _ _
    natCast := fun n => algebraMap₀ (n : R)
    natCast_zero := by simp only [Nat.cast_zero

Depends on / 依赖: LinearMap, LinearMap.map_add, LinearMap.map_zero, Nat.cast_succ, Nat.cast_zero, TensorPower, TensorPower.gmonoid, add_mul, cast_succ, cast_zero, gmonoid, map_add, map_zero, mul_add, mul_zero, natCast, natCast_succ, natCast_zero, zero_mul
-/
instance gsemiring : DirectSum.GSemiring fun i => ⨂[R]^i M :=
  { TensorPower.gmonoid with
    mul_zero := fun _ => map_zero _
    zero_mul := fun _ => LinearMap.map_zero₂ _ _
    mul_add := fun _ _ _ => map_add _ _ _
    add_mul := fun _ _ _ => LinearMap.map_add₂ _ _ _ _
    natCast := fun n => algebraMap₀ (n : R)
    natCast_zero := by simp only [Nat.cast_zero, map_zero]
    natCast_succ := fun n => by simp only [Nat.cast_succ, map_add, algebraMap₀_one] }

example : Semiring (⨁ n : Nat, ⨂[R]^n M) := by infer_instance

set_option backward.isDefEq.respectTransparency false in
/--
Instance `galgebra` / 实例 `galgebra`

English:
instance galgebra
  signature: : DirectSum.GAlgebra R fun i => ⨂[R]^i M where
  body: (algebraMap₀ : R ≃ₗ[R] (⨂[R]^0) M).toLinearMap.toAddMonoidHom
  map_one := algebraMap₀_one
  map_mul r s := gradedMonoid_eq_of_cast rfl (by
    rw [← LinearEquiv.eq_symm_apply]
    have := algebraMap₀_mul_algebraMap₀ (M := M) r s
    exact this.symm)
  commutes r x := gradedMonoid_eq_of_cast (add_co

中文:
实例 galgebra
  签名: : 直和.G代数 R fun i => ⨂[R]^i M where
  定义体: (algebraMap₀ : R ≃ₗ[R] (⨂[R]^0) M).toLinearMap.toAddMonoidHom
  map_one := algebraMap₀_one
  map_mul r s := gradedMonoid_eq_of_cast rfl (by
    rw [← LinearEquiv.eq_symm_apply]
    have := algebraMap₀_mul_algebraMap₀ (M := M) r s
    exact this.symm)
  commutes r x := gradedMonoid_eq_of_cast (add_co

Depends on / 依赖: toAddMonoidHom, toLinearMap, toLinearMap.toAddMonoidHom
-/
instance galgebra : DirectSum.GAlgebra R fun i => ⨂[R]^i M where
  toFun := (algebraMap₀ : R ≃ₗ[R] (⨂[R]^0) M).toLinearMap.toAddMonoidHom
  map_one := algebraMap₀_one
  map_mul r s := gradedMonoid_eq_of_cast rfl (by
    rw [← LinearEquiv.eq_symm_apply]
    have := algebraMap₀_mul_algebraMap₀ (M := M) r s
    exact this.symm)
  commutes r x := gradedMonoid_eq_of_cast (add_comm _ _) (by
    have := (algebraMap₀_mul r x.snd).trans (mul_algebraMap₀ r x.snd).symm
    rw [← LinearEquiv.eq_symm_apply]; rw [cast_symm]
    rw [← LinearEquiv.eq_symm_apply]; rw [cast_symm]; rw [cast_cast] at this
    exact this)
  smul_def r x := gradedMonoid_eq_of_cast (zero_add x.fst).symm (by
    rw [← LinearEquiv.eq_symm_apply]; rw [cast_symm]
    exact (algebraMap₀_mul r x.snd).symm)

/--
theorem `galgebra_toFun_def` / 定理 `galgebra_toFun_def`

English:
theorem galgebra_toFun_def
  given: (r : R)
  proof: rfl

example : Algebra R (⨁ n : Nat, ⨂[R]^n M) := by infer_instance

中文:
定理 galgebra_toFun_def
  条件: (r : R)
  证明: rfl

example : Algebra R (⨁ n : Nat, ⨂[R]^n M) := by infer_instance
-/
theorem galgebra_toFun_def (r : R) :
    DirectSum.GAlgebra.toFun (A := fun i => ⨂[R]^i M) r = algebraMap₀ r :=
  rfl

example : Algebra R (⨁ n : Nat, ⨂[R]^n M) := by infer_instance

end TensorPower
