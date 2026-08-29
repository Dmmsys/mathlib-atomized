/-
Copyright (c) 2025 David Kurniadi Angdinata. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Kurniadi Angdinata
-/
module

public import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Formula
public import Mathlib.LinearAlgebra.FreeModule.Norm
public import Mathlib.RingTheory.ClassGroup.Basic
public import Mathlib.RingTheory.Polynomial.UniqueFactorization

/-!
# Nonsingular points and the group law in affine coordinates

Let `W` be a Weierstrass curve over a field `F` given by a Weierstrass equation `W(X, Y) = 0` in
affine coordinates. The type of nonsingular points in affine coordinates is an inductive, consisting
of the unique point at infinity `𝓞` and nonsingular affine points `(x, y)`. It can be endowed with a
group law, with `𝓞` as the identity nonsingular point, which is uniquely determined by the formulae
in `Mathlib/AlgebraicGeometry/EllipticCurve/Affine/Formula.lean`.

With this description, there is an addition-preserving injection from the nonsingular points to the
ideal class group of the *affine coordinate ring* `F[W] := F[X, Y] / ⟨W(X, Y)⟩`. This is given by
mapping `𝓞` to the trivial ideal class and a nonsingular affine point `(x, y)` to the ideal class of
the invertible ideal `⟨X - x, Y - y⟩`. Proving that this is well-defined and preserves addition
reduces to equalities of ideals checked in `WeierstrassCurve.Affine.CoordinateRing.XYIdeal_neg_mul`
and in `WeierstrassCurve.Affine.CoordinateRing.XYIdeal_mul_XYIdeal` via explicit ideal computations.
Now `F[W]` is a free rank two `F[X]`-algebra with basis `{1, Y}`, so every element of `F[W]` is of
the form `p + qY` for some `p, q` in `F[X]`, and there is an algebra norm `N : F[W] → F[X]`.
Injectivity can then be shown by computing the degree of such a norm `N(p + qY)` in two different
ways, which is done in `WeierstrassCurve.Affine.CoordinateRing.degree_norm_smul_basis` and in the
auxiliary lemmas in the proof of `WeierstrassCurve.Affine.Point.instAddCommGroup`.

This file defines the group law on nonsingular points in affine coordinates.

## Main definitions

* `WeierstrassCurve.Affine.CoordinateRing`: the affine coordinate ring `F[W]`.
* `WeierstrassCurve.Affine.CoordinateRing.basis`: the power basis of `F[W]` over `F[X]`.
* `WeierstrassCurve.Affine.Point`: a nonsingular point in affine coordinates.
* `WeierstrassCurve.Affine.Point.neg`: the negation of a nonsingular point in affine coordinates.
* `WeierstrassCurve.Affine.Point.add`: the addition of a nonsingular point in affine coordinates.

## Main statements

* `WeierstrassCurve.Affine.CoordinateRing.instIsDomainCoordinateRing`: the affine coordinate ring
  of a Weierstrass curve is an integral domain.
* `WeierstrassCurve.Affine.CoordinateRing.degree_norm_smul_basis`: the degree of the norm of an
  element in the affine coordinate ring in terms of its power basis.
* `WeierstrassCurve.Affine.Point.instAddCommGroup`: the type of nonsingular points in affine
  coordinates forms an abelian group under addition.

## References

* [J Silverman, *The Arithmetic of Elliptic Curves*][silverman2009]
* https://drops.dagstuhl.de/storage/00lipics/lipics-vol268-itp2023/LIPIcs.ITP.2023.6/LIPIcs.ITP.2023.6.pdf

## Tags

elliptic curve, affine, point, group law, class group
-/

@[expose] public section

open FractionalIdeal (coeIdeal_mul)

open Ideal hiding map_mul

open Module Polynomial

open scoped nonZeroDivisors Polynomial.Bivariate

local macro "C_simp" : tactic =>
  `(tactic| simp only [map_ofNat, C_0, C_1, C_neg, C_add, C_sub, C_mul, C_pow])

universe r s u v w

namespace WeierstrassCurve

variable {R : Type r} {S : Type s} {A F : Type u} {B K : Type v} {L : Type w} [CommRing R]
  [CommRing S] [CommRing A] [CommRing B] [Field F] [Field K] [Field L] {W' : Affine R}
  {W : Affine F}

namespace Affine

/-! ## The affine coordinate ring -/

variable (W') in
/--
Definition of `CoordinateRing` / `CoordinateRing` 的定义

English:
abbreviation CoordinateRing
  signature: : Type r
  body: AdjoinRoot W'.polynomial

中文:
缩写 CoordinateRing
  签名: : Type r
  定义体: AdjoinRoot W'.polynomial

Depends on / 依赖: AdjoinRoot, polynomial
-/
abbrev CoordinateRing : Type r :=
  AdjoinRoot W'.polynomial

variable (W') in
/--
Definition of `FunctionField` / `FunctionField` 的定义

English:
abbreviation FunctionField
  signature: : Type r
  body: FractionRing W'.CoordinateRing

中文:
缩写 FunctionField
  签名: : Type r
  定义体: FractionRing W'.CoordinateRing

Depends on / 依赖: CoordinateRing, FractionRing
-/
abbrev FunctionField : Type r :=
  FractionRing W'.CoordinateRing

namespace CoordinateRing

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Algebra R W'.CoordinateRing
  body: inferInstance

中文:
实例 :
  签名: Algebra R W'.CoordinateRing
  定义体: inferInstance
-/
noncomputable instance : Algebra R W'.CoordinateRing := inferInstance

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Algebra R[X] W'.CoordinateRing
  body: inferInstance

中文:
实例 :
  签名: Algebra R[X] W'.CoordinateRing
  定义体: inferInstance
-/
noncomputable instance : Algebra R[X] W'.CoordinateRing := inferInstance

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: IsScalarTower R R[X] W'.CoordinateRing
  body: inferInstance

中文:
实例 :
  签名: IsScalarTower R R[X] W'.CoordinateRing
  定义体: inferInstance
-/
instance : IsScalarTower R R[X] W'.CoordinateRing := inferInstance

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Subsingleton
  signature: R] : Subsingleton W'.CoordinateRing
  body: Module.subsingleton R[X] _

中文:
实例 [Subsingleton
  签名: R] : Subsingleton W'.CoordinateRing
  定义体: Module.subsingleton R[X] _

Depends on / 依赖: Module, Module.subsingleton, subsingleton
-/
instance [Subsingleton R] : Subsingleton W'.CoordinateRing :=
  Module.subsingleton R[X] _

variable (W') in
/--
Definition of `mk` / `mk` 的定义

English:
abbreviation mk
  signature: : R[X][Y] ->+* W'.CoordinateRing
  body: AdjoinRoot.mk W'.polynomial

中文:
缩写 mk
  签名: : R[X][Y] ->+* W'.CoordinateRing
  定义体: AdjoinRoot.mk W'.polynomial

Depends on / 依赖: AdjoinRoot, AdjoinRoot.mk, polynomial
-/
noncomputable abbrev mk : R[X][Y] ->+* W'.CoordinateRing :=
  AdjoinRoot.mk W'.polynomial

open scoped Classical in
variable (W') in
/--
Definition of `noncomputable` / `noncomputable` 的定义

English:
definition noncomputable
  signature: def basis
  body: (subsingleton_or_nontrivial R).by_cases (fun _ => default) fun _ =>
(AdjoinRoot.powerBasis' monic_polynomial).basis.reindex finCongr natDegree_polynomial

中文:
定义 noncomputable
  签名: def basis
  定义体: (subsingleton_or_nontrivial R).by_cases (fun _ => default) fun _ =>
(AdjoinRoot.powerBasis' monic_polynomial).basis.reindex finCongr natDegree_polynomial
-/
protected noncomputable def basis : Basis (Fin 2) R[X] W'.CoordinateRing :=
  (subsingleton_or_nontrivial R).by_cases (fun _ => default) fun _ =>
(AdjoinRoot.powerBasis' monic_polynomial).basis.reindex finCongr natDegree_polynomial

set_option backward.isDefEq.respectTransparency.types false in
/--
lemma `basis_apply` / 引理 `basis_apply`

English:
lemma basis_apply
  given: (n : Fin 2)
  proof: by
  classical
  nontriviality R
  rw [CoordinateRing.basis]; rw [Or.by_cases]; rw [dif_neg <| not_subsingleton R]; rw [Basis.reindex_apply]; rw [PowerBasis.basis_eq_pow]; rw [finCongr_symm_apply]; rw [Fin.val_cast]

@[simp]

中文:
引理 basis_apply
  条件: (n : Fin 2)
  证明: by
  classical
  nontriviality R
  rw [CoordinateRing.basis]; rw [Or.by_cases]; rw [dif_neg <| not_subsingleton R]; rw [Basis.reindex_apply]; rw [PowerBasis.basis_eq_pow]; rw [finCongr_symm_apply]; rw [Fin.val_cast]

@[simp]

Depends on / 依赖: Basis.reindex_apply, CoordinateRing, CoordinateRing.basis, Fin.val_cast, Or.by_cases, PowerBasis, PowerBasis.basis_eq_pow, basis_eq_pow, classical, dif_neg, finCongr_symm_apply, nontriviality, not_subsingleton, reindex_apply, val_cast
-/
lemma basis_apply (n : Fin 2) :
    CoordinateRing.basis W' n = (AdjoinRoot.powerBasis' monic_polynomial).gen ^ (n : Nat) := by
  classical
  nontriviality R
  rw [CoordinateRing.basis]; rw [Or.by_cases]; rw [dif_neg <| not_subsingleton R]; rw [Basis.reindex_apply]; rw [PowerBasis.basis_eq_pow]; rw [finCongr_symm_apply]; rw [Fin.val_cast]

@[simp]
/--
lemma `basis_zero` / 引理 `basis_zero`

English:
lemma basis_zero
  statement: CoordinateRing.basis W' 0 = 1
  proof: by
  simpa only [basis_apply] using! pow_zero _

@[simp]

中文:
引理 basis_zero
  结论: CoordinateRing.basis W' 0 = 1
  证明: by
  simpa only [basis_apply] using! pow_zero _

@[simp]

Depends on / 依赖: basis_apply, pow_zero
-/
lemma basis_zero : CoordinateRing.basis W' 0 = 1 := by
  simpa only [basis_apply] using! pow_zero _

@[simp]
/--
lemma `basis_one` / 引理 `basis_one`

English:
lemma basis_one
  statement: CoordinateRing.basis W' 1 = mk W' Y
  proof: by
  simpa only [basis_apply] using! pow_one _

中文:
引理 basis_one
  结论: CoordinateRing.basis W' 1 = mk W' Y
  证明: by
  simpa only [basis_apply] using! pow_one _

Depends on / 依赖: basis_apply, pow_one
-/
lemma basis_one : CoordinateRing.basis W' 1 = mk W' Y := by
  simpa only [basis_apply] using! pow_one _

/--
lemma `coe_basis` / 引理 `coe_basis`

English:
lemma coe_basis
  statement: (CoordinateRing.basis W' : Fin 2 -> W'.CoordinateRing) = ![1, mk W' Y]
  proof: by
  ext n
  fin_cases n
  exacts [basis_zero, basis_one]

中文:
引理 coe_basis
  结论: (CoordinateRing.basis W' : Fin 2 -> W'.CoordinateRing) = ![1, mk W' Y]
  证明: by
  ext n
  fin_cases n
  exacts [basis_zero, basis_one]

Depends on / 依赖: basis_one, basis_zero, exacts, fin_cases
-/
lemma coe_basis : (CoordinateRing.basis W' : Fin 2 -> W'.CoordinateRing) = ![1, mk W' Y] := by
  ext n
  fin_cases n
  exacts [basis_zero, basis_one]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Module.Free R[X] W'.CoordinateRing
  body: .of_basis (CoordinateRing.basis W')

中文:
实例 :
  签名: Module.Free R[X] W'.CoordinateRing
  定义体: .of_basis (CoordinateRing.basis W')

Depends on / 依赖: CoordinateRing, CoordinateRing.basis, of_basis
-/
instance : Module.Free R[X] W'.CoordinateRing := .of_basis (CoordinateRing.basis W')

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Module.Free R W'.CoordinateRing
  body: .trans (S := R[X])

中文:
实例 :
  签名: Module.Free R W'.CoordinateRing
  定义体: .trans (S := R[X])
-/
instance : Module.Free R W'.CoordinateRing := .trans (S := R[X])

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Nontrivial
  signature: R] : Nontrivial W'.CoordinateRing
  body: ⟨_, _, (CoordinateRing.basis W').ne_zero 0⟩

中文:
实例 [Nontrivial
  签名: R] : Nontrivial W'.CoordinateRing
  定义体: ⟨_, _, (CoordinateRing.basis W').ne_zero 0⟩

Depends on / 依赖: CoordinateRing, CoordinateRing.basis, ne_zero
-/
instance [Nontrivial R] : Nontrivial W'.CoordinateRing :=
  ⟨_, _, (CoordinateRing.basis W').ne_zero 0⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: FaithfulSMul R[X] W'.CoordinateRing
  body: by nontriviality R; infer_instance

中文:
实例 :
  签名: FaithfulSMul R[X] W'.CoordinateRing
  定义体: by nontriviality R; infer_instance

Depends on / 依赖: infer_instance, nontriviality
-/
instance : FaithfulSMul R[X] W'.CoordinateRing := by nontriviality R; infer_instance

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: FaithfulSMul R W'.CoordinateRing
  body: .trans R R[X] _

中文:
实例 :
  签名: FaithfulSMul R W'.CoordinateRing
  定义体: .trans R R[X] _
-/
instance : FaithfulSMul R W'.CoordinateRing := .trans R R[X] _

/--
lemma `smul` / 引理 `smul`

English:
lemma smul
  given: (x : R[X]) (y : W'.CoordinateRing)
  statement: x • y = mk W' (C x) * y
  proof: (algebraMap_smul W'.CoordinateRing x y).symm

中文:
引理 smul
  条件: (x : R[X]) (y : W'.CoordinateRing)
  结论: x • y = mk W' (C x) * y
  证明: (algebraMap_smul W'.CoordinateRing x y).symm

Depends on / 依赖: CoordinateRing, algebraMap_smul
-/
lemma smul (x : R[X]) (y : W'.CoordinateRing) : x • y = mk W' (C x) * y :=
  (algebraMap_smul W'.CoordinateRing x y).symm

/--
lemma `smul_basis_eq_zero` / 引理 `smul_basis_eq_zero`

English:
lemma smul_basis_eq_zero
  given: {p q : R[X]} (hpq : p • (1 : W'.CoordinateRing) + q • mk W' Y = 0)
  proof: by
  have h := Fintype.linearIndependent_iff.mp (CoordinateRing.basis W').linearIndependent ![p, q]
  rw [Fin.sum_univ_succ]; rw [basis_zero]; rw [Fin.sum_univ_one]; rw [Fin.succ_zero_eq_one]; rw [basis_one] at h
  exact ⟨h hpq 0, h hpq 1⟩

中文:
引理 smul_basis_eq_zero
  条件: {p q : R[X]} (hpq : p • (1 : W'.CoordinateRing) + q • mk W' Y = 0)
  证明: by
  have h := Fintype.linearIndependent_iff.mp (CoordinateRing.basis W').linearIndependent ![p, q]
  rw [Fin.sum_univ_succ]; rw [basis_zero]; rw [Fin.sum_univ_one]; rw [Fin.succ_zero_eq_one]; rw [basis_one] at h
  exact ⟨h hpq 0, h hpq 1⟩

Depends on / 依赖: CoordinateRing, CoordinateRing.basis, Fin.succ_zero_eq_one, Fin.sum_univ_one, Fin.sum_univ_succ, Fintype, Fintype.linearIndependent_iff.mp, basis_one, basis_zero, linearIndependent, linearIndependent_iff, succ_zero_eq_one, sum_univ_one, sum_univ_succ
-/
lemma smul_basis_eq_zero {p q : R[X]} (hpq : p • (1 : W'.CoordinateRing) + q • mk W' Y = 0) :
    p = 0 ∧ q = 0 := by
  have h := Fintype.linearIndependent_iff.mp (CoordinateRing.basis W').linearIndependent ![p, q]
  rw [Fin.sum_univ_succ]; rw [basis_zero]; rw [Fin.sum_univ_one]; rw [Fin.succ_zero_eq_one]; rw [basis_one] at h
  exact ⟨h hpq 0, h hpq 1⟩

/--
lemma `exists_smul_basis_eq` / 引理 `exists_smul_basis_eq`

English:
lemma exists_smul_basis_eq
  given: (x : W'.CoordinateRing)
  proof: by
  have h := (CoordinateRing.basis W').sum_equivFun x
  rw [Fin.sum_univ_succ]; rw [Fin.sum_univ_one]; rw [basis_zero]; rw [Fin.succ_zero_eq_one]; rw [basis_one] at h
  exact ⟨_, _, h⟩

中文:
引理 exists_smul_basis_eq
  条件: (x : W'.CoordinateRing)
  证明: by
  have h := (CoordinateRing.basis W').sum_equivFun x
  rw [Fin.sum_univ_succ]; rw [Fin.sum_univ_one]; rw [basis_zero]; rw [Fin.succ_zero_eq_one]; rw [basis_one] at h
  exact ⟨_, _, h⟩

Depends on / 依赖: CoordinateRing, CoordinateRing.basis, Fin.succ_zero_eq_one, Fin.sum_univ_one, Fin.sum_univ_succ, basis_one, basis_zero, succ_zero_eq_one, sum_equivFun, sum_univ_one, sum_univ_succ
-/
lemma exists_smul_basis_eq (x : W'.CoordinateRing) :
    exists p q : R[X], p • (1 : W'.CoordinateRing) + q • mk W' Y = x := by
  have h := (CoordinateRing.basis W').sum_equivFun x
  rw [Fin.sum_univ_succ]; rw [Fin.sum_univ_one]; rw [basis_zero]; rw [Fin.succ_zero_eq_one]; rw [basis_one] at h
  exact ⟨_, _, h⟩

/--
lemma `smul_basis_mul_C` / 引理 `smul_basis_mul_C`

English:
lemma smul_basis_mul_C
  given: (y : R[X]) (p q : R[X])
  proof: by
  simp only [smul, map_mul]
  ring1

中文:
引理 smul_basis_mul_C
  条件: (y : R[X]) (p q : R[X])
  证明: by
  simp only [smul, map_mul]
  ring1

Depends on / 依赖: map_mul
-/
lemma smul_basis_mul_C (y : R[X]) (p q : R[X]) :
    (p • (1 : W'.CoordinateRing) + q • mk W' Y) * mk W' (C y) =
      (p * y) • (1 : W'.CoordinateRing) + (q * y) • mk W' Y := by
  simp only [smul, map_mul]
  ring1

/--
lemma `smul_basis_mul_Y` / 引理 `smul_basis_mul_Y`

English:
lemma smul_basis_mul_Y
  given: (p q : R[X])
  statement: (p • (1 : W'.CoordinateRing) + q • mk W' Y) * mk W' Y =
  proof: by
  have Y_sq : mk W' Y ^ 2 = mk W' (C (X ^ 3 + C W'.a₂ * X ^ 2 + C W'.a₄ * X + C W'.a₆) -
      C (C W'.a₁ * X + C W'.a₃) * Y) := AdjoinRoot.mk_eq_mk.mpr ⟨1, by rw [polynomial]; ring1⟩
  simp only [smul, add_mul, mul_assoc, ← sq, Y_sq, map_sub, map_mul]
  ring1

中文:
引理 smul_basis_mul_Y
  条件: (p q : R[X])
  结论: (p • (1 : W'.CoordinateRing) + q • mk W' Y) * mk W' Y =
  证明: by
  have Y_sq : mk W' Y ^ 2 = mk W' (C (X ^ 3 + C W'.a₂ * X ^ 2 + C W'.a₄ * X + C W'.a₆) -
      C (C W'.a₁ * X + C W'.a₃) * Y) := AdjoinRoot.mk_eq_mk.mpr ⟨1, by rw [polynomial]; ring1⟩
  simp only [smul, add_mul, mul_assoc, ← sq, Y_sq, map_sub, map_mul]
  ring1

Depends on / 依赖: AdjoinRoot, AdjoinRoot.mk_eq_mk.mpr, Y_sq, add_mul, map_mul, map_sub, mk_eq_mk, mul_assoc, polynomial
-/
lemma smul_basis_mul_Y (p q : R[X]) : (p • (1 : W'.CoordinateRing) + q • mk W' Y) * mk W' Y =
    (q * (X ^ 3 + C W'.a₂ * X ^ 2 + C W'.a₄ * X + C W'.a₆)) • (1 : W'.CoordinateRing) +
      (p - q * (C W'.a₁ * X + C W'.a₃)) • mk W' Y := by
  have Y_sq : mk W' Y ^ 2 = mk W' (C (X ^ 3 + C W'.a₂ * X ^ 2 + C W'.a₄ * X + C W'.a₆) -
      C (C W'.a₁ * X + C W'.a₃) * Y) := AdjoinRoot.mk_eq_mk.mpr ⟨1, by rw [polynomial]; ring1⟩
  simp only [smul, add_mul, mul_assoc, ← sq, Y_sq, map_sub, map_mul]
  ring1

variable (W') in
/--
Definition of `map` / `map` 的定义

English:
definition map
  signature: (f : R ->+* S)
  body: AdjoinRoot.lift ((AdjoinRoot.of _).comp <| mapRingHom f) (AdjoinRoot.root (W'.map f).polynomial)
    (by rw [← eval₂_map, ← map_polynomial, AdjoinRoot.eval₂_root])

中文:
定义 map
  签名: (f : R ->+* S)
  定义体: AdjoinRoot.lift ((AdjoinRoot.of _).comp <| mapRingHom f) (AdjoinRoot.root (W'.map f).polynomial)
    (by rw [← eval₂_map, ← map_polynomial, AdjoinRoot.eval₂_root])

Depends on / 依赖: AdjoinRoot, AdjoinRoot.eval, AdjoinRoot.lift, AdjoinRoot.of, AdjoinRoot.root, mapRingHom, map_polynomial, polynomial
-/
noncomputable def map (f : R ->+* S) : W'.CoordinateRing ->+* (W'.map f).CoordinateRing :=
  AdjoinRoot.lift ((AdjoinRoot.of _).comp <| mapRingHom f) (AdjoinRoot.root (W'.map f).polynomial)
    (by rw [← eval₂_map, ← map_polynomial, AdjoinRoot.eval₂_root])

/--
lemma `map_mk` / 引理 `map_mk`

English:
lemma map_mk
  given: (f : R ->+* S) (x : R[X][Y])
  proof: by
  rw [map]; rw [AdjoinRoot.lift_mk]; rw [← eval₂_map]
exact AdjoinRoot.aeval_eq x.map mapRingHom f

中文:
引理 map_mk
  条件: (f : R ->+* S) (x : R[X][Y])
  证明: by
  rw [map]; rw [AdjoinRoot.lift_mk]; rw [← eval₂_map]
exact AdjoinRoot.aeval_eq x.map mapRingHom f

Depends on / 依赖: AdjoinRoot, AdjoinRoot.aeval_eq, AdjoinRoot.lift_mk, aeval_eq, lift_mk, mapRingHom, x.map
-/
lemma map_mk (f : R ->+* S) (x : R[X][Y]) :
    map W' f (mk W' x) = mk (W'.map f) (x.map <| mapRingHom f) := by
  rw [map]; rw [AdjoinRoot.lift_mk]; rw [← eval₂_map]
exact AdjoinRoot.aeval_eq x.map mapRingHom f

/--
lemma `map_smul` / 引理 `map_smul`

English:
lemma map_smul
  given: (f : R ->+* S) (x : R[X]) (y : W'.CoordinateRing)
  proof: by
  rw [smul]; rw [map_mul]; rw [map_mk]; rw [map_C]; rw [smul]
  rfl

中文:
引理 map_smul
  条件: (f : R ->+* S) (x : R[X]) (y : W'.CoordinateRing)
  证明: by
  rw [smul]; rw [map_mul]; rw [map_mk]; rw [map_C]; rw [smul]
  rfl
-/
protected lemma map_smul (f : R ->+* S) (x : R[X]) (y : W'.CoordinateRing) :
    map W' f (x • y) = x.map f • map W' f y := by
  rw [smul]; rw [map_mul]; rw [map_mk]; rw [map_C]; rw [smul]
  rfl

/--
lemma `map_injective` / 引理 `map_injective`

English:
lemma map_injective
  given: {f : R ->+* S} (hf : Function.Injective f)
  statement: Function.Injective map W' f
  proof: (injective_iff_map_eq_zero _).mpr fun y hy => by
    obtain ⟨p, q, rfl⟩ := exists_smul_basis_eq y
    simp_rw [map_add, CoordinateRing.map_smul, map_one, map_mk, map_X] at hy
    obtain ⟨hp, hq⟩ := smul_basis_eq_zero hy
    rw [Polynomial.map_eq_zero_iff hf] at hp hq
    simp_rw [hp, hq, zero_smul, 

中文:
引理 map_injective
  条件: {f : R ->+* S} (hf : Function.Injective f)
  结论: Function.Injective map W' f
  证明: (injective_iff_map_eq_zero _).mpr fun y hy => by
    obtain ⟨p, q, rfl⟩ := exists_smul_basis_eq y
    simp_rw [map_add, CoordinateRing.map_smul, map_one, map_mk, map_X] at hy
    obtain ⟨hp, hq⟩ := smul_basis_eq_zero hy
    rw [Polynomial.map_eq_zero_iff hf] at hp hq
    simp_rw [hp, hq, zero_smul, 

Depends on / 依赖: CoordinateRing, CoordinateRing.map_smul, Polynomial, Polynomial.map_eq_zero_iff, add_zero, exists_smul_basis_eq, injective_iff_map_eq_zero, map_X, map_add, map_eq_zero_iff, map_mk, map_one, map_smul, simp_rw, smul_basis_eq_zero, zero_smul
-/
lemma map_injective {f : R ->+* S} (hf : Function.Injective f) : Function.Injective map W' f :=
  (injective_iff_map_eq_zero _).mpr fun y hy => by
    obtain ⟨p, q, rfl⟩ := exists_smul_basis_eq y
    simp_rw [map_add, CoordinateRing.map_smul, map_one, map_mk, map_X] at hy
    obtain ⟨hp, hq⟩ := smul_basis_eq_zero hy
    rw [Polynomial.map_eq_zero_iff hf] at hp hq
    simp_rw [hp, hq, zero_smul, add_zero]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [IsDomain
  signature: R] : IsDomain W'.CoordinateRing
  body: have : IsDomain (W'.map <| algebraMap R <| FractionRing R).CoordinateRing :=
    AdjoinRoot.isDomain_of_prime irreducible_polynomial.prime
  (map_injective <| IsFractionRing.injective R <| FractionRing R).isDomain

中文:
实例 [IsDomain
  签名: R] : IsDomain W'.CoordinateRing
  定义体: have : IsDomain (W'.map <| algebraMap R <| FractionRing R).CoordinateRing :=
    AdjoinRoot.isDomain_of_prime irreducible_polynomial.prime
  (map_injective <| IsFractionRing.injective R <| FractionRing R).isDomain

Depends on / 依赖: AdjoinRoot, AdjoinRoot.isDomain_of_prime, CoordinateRing, FractionRing, IsDomain, IsFractionRing, IsFractionRing.injective, algebraMap, injective, irreducible_polynomial, irreducible_polynomial.prime, isDomain, isDomain_of_prime, map_injective
-/
instance [IsDomain R] : IsDomain W'.CoordinateRing :=
  have : IsDomain (W'.map <| algebraMap R <| FractionRing R).CoordinateRing :=
    AdjoinRoot.isDomain_of_prime irreducible_polynomial.prime
  (map_injective <| IsFractionRing.injective R <| FractionRing R).isDomain

/-! ## Ideals in the affine coordinate ring -/

variable (W') in
/--
Definition of `XClass` / `XClass` 的定义

English:
definition XClass
  signature: (x : R)
  body: mk W' C X - C x

中文:
定义 XClass
  签名: (x : R)
  定义体: mk W' C X - C x
-/
noncomputable def XClass (x : R) : W'.CoordinateRing :=
mk W' C X - C x

/--
lemma `XClass_ne_zero` / 引理 `XClass_ne_zero`

English:
lemma XClass_ne_zero
  given: [Nontrivial R] (x : R)
  statement: XClass W' x != 0
  proof: AdjoinRoot.mk_ne_zero_of_natDegree_lt monic_polynomial (C_ne_zero.mpr <| X_sub_C_ne_zero x)
    by rw [natDegree_polynomial, natDegree_C]; norm_num1

中文:
引理 XClass_ne_zero
  条件: [Nontrivial R] (x : R)
  结论: XClass W' x != 0
  证明: AdjoinRoot.mk_ne_zero_of_natDegree_lt monic_polynomial (C_ne_zero.mpr <| X_sub_C_ne_zero x)
    by rw [natDegree_polynomial, natDegree_C]; norm_num1

Depends on / 依赖: AdjoinRoot, AdjoinRoot.mk_ne_zero_of_natDegree_lt, C_ne_zero, C_ne_zero.mpr, X_sub_C_ne_zero, mk_ne_zero_of_natDegree_lt, monic_polynomial, natDegree_C, natDegree_polynomial, norm_num1
-/
lemma XClass_ne_zero [Nontrivial R] (x : R) : XClass W' x != 0 :=
AdjoinRoot.mk_ne_zero_of_natDegree_lt monic_polynomial (C_ne_zero.mpr <| X_sub_C_ne_zero x)
    by rw [natDegree_polynomial, natDegree_C]; norm_num1

variable (W') in
/--
Definition of `YClass` / `YClass` 的定义

English:
definition YClass
  signature: (y : R[X])
  body: mk W' Y - C y

中文:
定义 YClass
  签名: (y : R[X])
  定义体: mk W' Y - C y
-/
noncomputable def YClass (y : R[X]) : W'.CoordinateRing :=
mk W' Y - C y

/--
lemma `YClass_ne_zero` / 引理 `YClass_ne_zero`

English:
lemma YClass_ne_zero
  given: [Nontrivial R] (y : R[X])
  statement: YClass W' y != 0
  proof: AdjoinRoot.mk_ne_zero_of_natDegree_lt monic_polynomial (X_sub_C_ne_zero y)
    by rw [natDegree_polynomial, natDegree_X_sub_C]; norm_num1

中文:
引理 YClass_ne_zero
  条件: [Nontrivial R] (y : R[X])
  结论: YClass W' y != 0
  证明: AdjoinRoot.mk_ne_zero_of_natDegree_lt monic_polynomial (X_sub_C_ne_zero y)
    by rw [natDegree_polynomial, natDegree_X_sub_C]; norm_num1

Depends on / 依赖: AdjoinRoot, AdjoinRoot.mk_ne_zero_of_natDegree_lt, X_sub_C_ne_zero, mk_ne_zero_of_natDegree_lt, monic_polynomial, natDegree_X_sub_C, natDegree_polynomial, norm_num1
-/
lemma YClass_ne_zero [Nontrivial R] (y : R[X]) : YClass W' y != 0 :=
AdjoinRoot.mk_ne_zero_of_natDegree_lt monic_polynomial (X_sub_C_ne_zero y)
    by rw [natDegree_polynomial, natDegree_X_sub_C]; norm_num1

/--
lemma `C_addPolynomial` / 引理 `C_addPolynomial`

English:
lemma C_addPolynomial
  given: (x y ℓ : R)
  statement: mk W' (C <| W'.addPolynomial x y ℓ) =
  proof: AdjoinRoot.mk_eq_mk.mpr ⟨1, by rw [W'.C_addPolynomial, add_sub_cancel_left, mul_one]⟩

中文:
引理 C_addPolynomial
  条件: (x y ℓ : R)
  结论: mk W' (C <| W'.addPolynomial x y ℓ) =
  证明: AdjoinRoot.mk_eq_mk.mpr ⟨1, by rw [W'.C_addPolynomial, add_sub_cancel_left, mul_one]⟩

Depends on / 依赖: AdjoinRoot, AdjoinRoot.mk_eq_mk.mpr, C_addPolynomial, add_sub_cancel_left, mk_eq_mk, mul_one
-/
lemma C_addPolynomial (x y ℓ : R) : mk W' (C <| W'.addPolynomial x y ℓ) =
    mk W' ((Y - C (linePolynomial x y ℓ)) * (W'.negPolynomial - C (linePolynomial x y ℓ))) :=
  AdjoinRoot.mk_eq_mk.mpr ⟨1, by rw [W'.C_addPolynomial, add_sub_cancel_left, mul_one]⟩

/--
lemma `C_addPolynomial_slope` / 引理 `C_addPolynomial_slope`

English:
lemma C_addPolynomial_slope
  statement: [DecidableEq F] {x₁ x₂ y₁ y₂ : F}
  proof: congr_arg (mk W) W.C_addPolynomial_slope h₁ h₂ hxy

中文:
引理 C_addPolynomial_slope
  结论: [DecidableEq F] {x₁ x₂ y₁ y₂ : F}
  证明: congr_arg (mk W) W.C_addPolynomial_slope h₁ h₂ hxy

Depends on / 依赖: C_addPolynomial_slope, W.C_addPolynomial_slope, congr_arg
-/
lemma C_addPolynomial_slope [DecidableEq F] {x₁ x₂ y₁ y₂ : F}
    (h₁ : W.Equation x₁ y₁) (h₂ : W.Equation x₂ y₂) (hxy : ¬(x₁ = x₂ ∧ y₁ = W.negY x₂ y₂)) :
    mk W (C <| W.addPolynomial x₁ y₁ <| W.slope x₁ x₂ y₁ y₂) =
      -(XClass W x₁ * XClass W x₂ * XClass W (W.addX x₁ x₂ <| W.slope x₁ x₂ y₁ y₂)) :=
congr_arg (mk W) W.C_addPolynomial_slope h₁ h₂ hxy

variable (W') in
/--
Definition of `XIdeal` / `XIdeal` 的定义

English:
definition XIdeal
  signature: (x : R)
  body: .span {XClass W' x}

中文:
定义 XIdeal
  签名: (x : R)
  定义体: .span {XClass W' x}

Depends on / 依赖: XClass
-/
noncomputable def XIdeal (x : R) : Ideal W'.CoordinateRing :=
  .span {XClass W' x}

variable (W') in
/--
Definition of `YIdeal` / `YIdeal` 的定义

English:
definition YIdeal
  signature: (y : R[X])
  body: .span {YClass W' y}

中文:
定义 YIdeal
  签名: (y : R[X])
  定义体: .span {YClass W' y}

Depends on / 依赖: YClass
-/
noncomputable def YIdeal (y : R[X]) : Ideal W'.CoordinateRing :=
  .span {YClass W' y}

variable (W') in
/--
Definition of `XYIdeal` / `XYIdeal` 的定义

English:
definition XYIdeal
  signature: (x : R) (y : R[X])
  body: .span {XClass W' x, YClass W' y}

中文:
定义 XYIdeal
  签名: (x : R) (y : R[X])
  定义体: .span {XClass W' x, YClass W' y}

Depends on / 依赖: XClass, YClass
-/
noncomputable def XYIdeal (x : R) (y : R[X]) : Ideal W'.CoordinateRing :=
  .span {XClass W' x, YClass W' y}

set_option backward.isDefEq.respectTransparency.types false in
/--
Definition of `quotientXYIdealEquiv` / `quotientXYIdealEquiv` 的定义

English:
definition quotientXYIdealEquiv
  signature: {x : R} {y : R[X]} (h : (W'.polynomial.eval y).eval x = 0)
  body: ((quotientEquivAlgOfEq R <| by
      simp only [XYIdeal, XClass, YClass, ← Set.image_pair, ← map_span]; rfl).trans <|
DoubleQuot.quotQuotEquivQuotOfLEₐ R (span_singleton_le_iff_mem _).mpr
          mem_span_C_X_sub_C_X_sub_C_iff_eval_eval_eq_zero.mpr h).trans
    quotientSpanCXSubCXSubCAlgEquiv

中文:
定义 quotientXYIdealEquiv
  签名: {x : R} {y : R[X]} (h : (W'.polynomial.eval y).eval x = 0)
  定义体: ((quotientEquivAlgOfEq R <| by
      simp only [XYIdeal, XClass, YClass, ← Set.image_pair, ← map_span]; rfl).trans <|
DoubleQuot.quotQuotEquivQuotOfLEₐ R (span_singleton_le_iff_mem _).mpr
          mem_span_C_X_sub_C_X_sub_C_iff_eval_eval_eq_zero.mpr h).trans
    quotientSpanCXSubCXSubCAlgEquiv

Depends on / 依赖: DoubleQuot, DoubleQuot.quotQuotEquivQuotOfLE, Set.image_pair, XClass, XYIdeal, YClass, image_pair, map_span, mem_span_C_X_sub_C_X_sub_C_iff_eval_eval_eq_zero, mem_span_C_X_sub_C_X_sub_C_iff_eval_eval_eq_zero.mpr, quotientEquivAlgOfEq, quotientSpanCXSubCXSubCAlgEquiv, span_singleton_le_iff_mem
-/
noncomputable def quotientXYIdealEquiv {x : R} {y : R[X]} (h : (W'.polynomial.eval y).eval x = 0) :
    (W'.CoordinateRing ⧸ XYIdeal W' x y) ≃ₐ[R] R :=
  ((quotientEquivAlgOfEq R <| by
      simp only [XYIdeal, XClass, YClass, ← Set.image_pair, ← map_span]; rfl).trans <|
DoubleQuot.quotQuotEquivQuotOfLEₐ R (span_singleton_le_iff_mem _).mpr
          mem_span_C_X_sub_C_X_sub_C_iff_eval_eval_eq_zero.mpr h).trans
    quotientSpanCXSubCXSubCAlgEquiv

/--
lemma `XYIdeal_add_eq` / 引理 `XYIdeal_add_eq`

English:
lemma XYIdeal_add_eq
  given: (x₁ x₂ y₁ ℓ : R)
  statement: XYIdeal W' (W'.addX x₁ x₂ ℓ) (C <| W'.addY x₁ x₂ y₁ ℓ) =
  proof: by
  simp only [XYIdeal, XIdeal, XClass, YClass, addY, negAddY, negY, negPolynomial, linePolynomial]
  rw [sub_sub <| -(Y : R[X][Y]), neg_sub_left (Y : R[X][Y]), map_neg, span_singleton_neg, sup_comm,
← span_insert, ← span_pair_add_left_mul _ _ mk W' C C W'.a₁ + ℓ, ← map_mul,
    ← map_add]
  congr 

中文:
引理 XYIdeal_add_eq
  条件: (x₁ x₂ y₁ ℓ : R)
  结论: XYIdeal W' (W'.addX x₁ x₂ ℓ) (C <| W'.addY x₁ x₂ y₁ ℓ) =
  证明: by
  simp only [XYIdeal, XIdeal, XClass, YClass, addY, negAddY, negY, negPolynomial, linePolynomial]
  rw [sub_sub <| -(Y : R[X][Y]), neg_sub_left (Y : R[X][Y]), map_neg, span_singleton_neg, sup_comm,
← span_insert, ← span_pair_add_left_mul _ _ mk W' C C W'.a₁ + ℓ, ← map_mul,
    ← map_add]
  congr 

Depends on / 依赖: C_simp, XClass, XIdeal, XYIdeal, YClass, linePolynomial, map_add, map_mul, map_neg, negAddY, negPolynomial, neg_sub_left, span_insert, span_pair_add_left_mul, span_singleton_neg, sub_sub, sup_comm
-/
lemma XYIdeal_add_eq (x₁ x₂ y₁ ℓ : R) : XYIdeal W' (W'.addX x₁ x₂ ℓ) (C <| W'.addY x₁ x₂ y₁ ℓ) =
    .span {mk W' <| W'.negPolynomial - C (linePolynomial x₁ y₁ ℓ)} ⊔
      XIdeal W' (W'.addX x₁ x₂ ℓ) := by
  simp only [XYIdeal, XIdeal, XClass, YClass, addY, negAddY, negY, negPolynomial, linePolynomial]
  rw [sub_sub <| -(Y : R[X][Y]), neg_sub_left (Y : R[X][Y]), map_neg, span_singleton_neg, sup_comm,
← span_insert, ← span_pair_add_left_mul _ _ mk W' C C W'.a₁ + ℓ, ← map_mul,
    ← map_add]
  congr 4
  C_simp
  ring1

/--
lemma `XYIdeal_eq₁` / 引理 `XYIdeal_eq₁`

English:
lemma XYIdeal_eq₁
  given: (x y ℓ : R)
  statement: XYIdeal W' x (C y) = XYIdeal W' x (linePolynomial x y ℓ)
  proof: by
  simp only [XYIdeal, XClass, YClass, linePolynomial]
  rw [← span_pair_add_left_mul _ _ <| mk W' <| C <| C <| -ℓ]; rw [← map_mul]; rw [← map_add]
  congr 4
  C_simp
  ring1

中文:
引理 XYIdeal_eq₁
  条件: (x y ℓ : R)
  结论: XYIdeal W' x (C y) = XYIdeal W' x (linePolynomial x y ℓ)
  证明: by
  simp only [XYIdeal, XClass, YClass, linePolynomial]
  rw [← span_pair_add_left_mul _ _ <| mk W' <| C <| C <| -ℓ]; rw [← map_mul]; rw [← map_add]
  congr 4
  C_simp
  ring1

Depends on / 依赖: C_simp, XClass, XYIdeal, YClass, linePolynomial, map_add, map_mul, span_pair_add_left_mul
-/
lemma XYIdeal_eq₁ (x y ℓ : R) : XYIdeal W' x (C y) = XYIdeal W' x (linePolynomial x y ℓ) := by
  simp only [XYIdeal, XClass, YClass, linePolynomial]
  rw [← span_pair_add_left_mul _ _ <| mk W' <| C <| C <| -ℓ]; rw [← map_mul]; rw [← map_add]
  congr 4
  C_simp
  ring1

-- Non-terminal simp, used to be field_simp
set_option linter.flexible false in
/--
lemma `XYIdeal_eq₂` / 引理 `XYIdeal_eq₂`

English:
lemma XYIdeal_eq₂
  statement: [DecidableEq F] {x₁ x₂ y₁ y₂ : F} (h₁ : W.Equation x₁ y₁) (h₂ : W.Equation x₂ y₂)
  proof: by
  have hy₂ : y₂ = (linePolynomial x₁ y₁ <| W.slope x₁ x₂ y₁ y₂).eval x₂ := by
    by_cases hx : x₁ = x₂
    · have hy : y₁ != W.negY x₂ y₂ := fun h => hxy ⟨hx, h⟩
      rcases hx, Y_eq_of_Y_ne h₁ h₂ hx hy with ⟨rfl, rfl⟩
      simp [linePolynomial]
    · simp [field, linePolynomial, slope_of_X_ne

中文:
引理 XYIdeal_eq₂
  结论: [DecidableEq F] {x₁ x₂ y₁ y₂ : F} (h₁ : W.Equation x₁ y₁) (h₂ : W.Equation x₂ y₂)
  证明: by
  have hy₂ : y₂ = (linePolynomial x₁ y₁ <| W.slope x₁ x₂ y₁ y₂).eval x₂ := by
    by_cases hx : x₁ = x₂
    · have hy : y₁ != W.negY x₂ y₂ := fun h => hxy ⟨hx, h⟩
      rcases hx, Y_eq_of_Y_ne h₁ h₂ hx hy with ⟨rfl, rfl⟩
      simp [linePolynomial]
    · simp [field, linePolynomial, slope_of_X_ne

Depends on / 依赖: W.negY, W.slope, XClass, XYIdeal, YClass, Y_eq_of_Y_ne, eval_, eval_C, eval_X, linePolynomial, map_add, map_mul, nth_rw, slope_of_X_ne, span_pair_add_left_mul
-/
lemma XYIdeal_eq₂ [DecidableEq F] {x₁ x₂ y₁ y₂ : F} (h₁ : W.Equation x₁ y₁) (h₂ : W.Equation x₂ y₂)
    (hxy : ¬(x₁ = x₂ ∧ y₁ = W.negY x₂ y₂)) :
    XYIdeal W x₂ (C y₂) = XYIdeal W x₂ (linePolynomial x₁ y₁ <| W.slope x₁ x₂ y₁ y₂) := by
  have hy₂ : y₂ = (linePolynomial x₁ y₁ <| W.slope x₁ x₂ y₁ y₂).eval x₂ := by
    by_cases hx : x₁ = x₂
    · have hy : y₁ != W.negY x₂ y₂ := fun h => hxy ⟨hx, h⟩
      rcases hx, Y_eq_of_Y_ne h₁ h₂ hx hy with ⟨rfl, rfl⟩
      simp [linePolynomial]
    · simp [field, linePolynomial, slope_of_X_ne hx]
      ring1
  nth_rw 1 [hy₂]
  simp only [XYIdeal, XClass, YClass, linePolynomial]
  rw [← span_pair_add_left_mul _ _ <| mk W <| C <| C <| -W.slope x₁ x₂ y₁ y₂]; rw [← map_mul]; rw [← map_add]
  congr 4
  simp only [eval_C, eval_X, eval_add, eval_sub, eval_mul]
  C_simp
  ring1

/--
lemma `XYIdeal_neg_mul` / 引理 `XYIdeal_neg_mul`

English:
lemma XYIdeal_neg_mul
  given: {x y : F} (h : W.Nonsingular x y)
  proof: by
  have Y_rw : (Y - C (C y)) * (Y - C (C <| W.negY x y)) -
      C (X - C x) * (C (X ^ 2 + C (x + W.a₂) * X + C (x ^ 2 + W.a₂ * x + W.a₄)) - C (C W.a₁) * Y) =
        W.polynomial * 1 := by
    linear_combination (norm := (rw [negY, polynomial]; C_simp; ring1))
      congr_arg C (congr_arg C ((equ

中文:
引理 XYIdeal_neg_mul
  条件: {x y : F} (h : W.Nonsingular x y)
  证明: by
  have Y_rw : (Y - C (C y)) * (Y - C (C <| W.negY x y)) -
      C (X - C x) * (C (X ^ 2 + C (x + W.a₂) * X + C (x ^ 2 + W.a₂ * x + W.a₄)) - C (C W.a₁) * Y) =
        W.polynomial * 1 := by
    linear_combination (norm := (rw [negY, polynomial]; C_simp; ring1))
      congr_arg C (congr_arg C ((equ

Depends on / 依赖: AdjoinRoot, AdjoinRoot.mk_eq_mk.mpr, C_simp, Ideal.mul_sup, W.negY, W.polynomial, XClass, XYIdeal, YClass, Y_rw, congr_arg, equation_iff, h.left, linear_combination, map_mul, mk_eq_mk, mul_comm, mul_sup, polynomial, simp_rw
-/
lemma XYIdeal_neg_mul {x y : F} (h : W.Nonsingular x y) :
    XYIdeal W x (C <| W.negY x y) * XYIdeal W x (C y) = XIdeal W x := by
  have Y_rw : (Y - C (C y)) * (Y - C (C <| W.negY x y)) -
      C (X - C x) * (C (X ^ 2 + C (x + W.a₂) * X + C (x ^ 2 + W.a₂ * x + W.a₄)) - C (C W.a₁) * Y) =
        W.polynomial * 1 := by
    linear_combination (norm := (rw [negY, polynomial]; C_simp; ring1))
      congr_arg C (congr_arg C ((equation_iff ..).mp h.left).symm)
  simp_rw [XYIdeal, XClass, YClass, span_pair_mul_span_pair, mul_comm, ← map_mul,
    AdjoinRoot.mk_eq_mk.mpr ⟨1, Y_rw⟩, map_mul, span_insert, ← span_singleton_mul_span_singleton,
    ← Ideal.mul_sup, ← span_insert]
  convert! mul_top (_ : Ideal W.CoordinateRing) using 2
  on_goal 2 => infer_instance
  simp_rw [← Set.image_singleton (f := mk W), ← Set.image_insert_eq, ← map_span]
  convert! map_top (R := F[X][Y]) (mk W) using 1
  apply congr_arg
  simp_rw [eq_top_iff_one, mem_span_insert', mem_span_singleton']
  rcases ((nonsingular_iff' ..).mp h).right with hx | hy
  · let W_X := W.a₁ * y - (3 * x ^ 2 + 2 * W.a₂ * x + W.a₄)
    refine
⟨C C W_X⁻¹ * -(X + C (2 * x + W.a₂)), C C W_X⁻¹ * W.a₁, 0, C C W_X⁻¹ * -1, ?_⟩
    rw [← mul_right_inj' <| C_ne_zero.mpr <| C_ne_zero.mpr hx]
    simp only [W_X, mul_add, ← mul_assoc, ← C_mul, mul_inv_cancel₀ hx]
    C_simp
    ring1
  · let W_Y := 2 * y + W.a₁ * x + W.a₃
refine ⟨0, C C W_Y⁻¹, C C W_Y⁻¹ * -1, 0, ?_⟩
    rw [negY]; rw [← mul_right_inj' <| C_ne_zero.mpr <| C_ne_zero.mpr hy]
    simp only [W_Y, mul_add, ← mul_assoc, ← C_mul, mul_inv_cancel₀ hy]
    C_simp
    ring1

/--
lemma `XYIdeal_mul_XYIdeal` / 引理 `XYIdeal_mul_XYIdeal`

English:
lemma XYIdeal_mul_XYIdeal
  statement: [DecidableEq F] {x₁ x₂ y₁ y₂ : F}
  proof: by
  have sup_rw : forall a b c d : Ideal W.CoordinateRing, a ⊔ (b ⊔ (c ⊔ d)) = a ⊔ d ⊔ b ⊔ c :=
    fun _ _ c _ => by rw [← sup_assoc, sup_comm c, sup_sup_sup_comm, ← sup_assoc]
  rw [XYIdeal_add_eq]; rw [XIdeal]; rw [mul_comm]; rw [XYIdeal_eq₁ x₁ y₁ <| W.slope x₁ x₂ y₁ y₂]; rw [XYIdeal]; rw [XYIde

中文:
引理 XYIdeal_mul_XYIdeal
  结论: [DecidableEq F] {x₁ x₂ y₁ y₂ : F}
  证明: by
  have sup_rw : forall a b c d : Ideal W.CoordinateRing, a ⊔ (b ⊔ (c ⊔ d)) = a ⊔ d ⊔ b ⊔ c :=
    fun _ _ c _ => by rw [← sup_assoc, sup_comm c, sup_sup_sup_comm, ← sup_assoc]
  rw [XYIdeal_add_eq]; rw [XIdeal]; rw [mul_comm]; rw [XYIdeal_eq₁ x₁ y₁ <| W.slope x₁ x₂ y₁ y₂]; rw [XYIdeal]; rw [XYIde

Depends on / 依赖: C_addPolynomial_slope, CoordinateRing, Ideal.sup_mul, W.CoordinateRing, W.slope, XIdeal, XYIdeal, XYIdeal_add_eq, mul_comm, neg_eq_iff_eq_neg, neg_eq_iff_eq_neg.mpr, simp_rw, span_insert, span_pair_mul_span_pair, span_singleton_mul_span_singleton, sup_assoc, sup_comm, sup_mul, sup_rw, sup_sup_sup_comm
-/
lemma XYIdeal_mul_XYIdeal [DecidableEq F] {x₁ x₂ y₁ y₂ : F}
    (h₁ : W.Equation x₁ y₁) (h₂ : W.Equation x₂ y₂) (hxy : ¬(x₁ = x₂ ∧ y₁ = W.negY x₂ y₂)) :
    XIdeal W (W.addX x₁ x₂ <| W.slope x₁ x₂ y₁ y₂) * (XYIdeal W x₁ (C y₁) * XYIdeal W x₂ (C y₂)) =
      YIdeal W (linePolynomial x₁ y₁ <| W.slope x₁ x₂ y₁ y₂) *
        XYIdeal W (W.addX x₁ x₂ <| W.slope x₁ x₂ y₁ y₂)
          (C <| W.addY x₁ x₂ y₁ <| W.slope x₁ x₂ y₁ y₂) := by
  have sup_rw : forall a b c d : Ideal W.CoordinateRing, a ⊔ (b ⊔ (c ⊔ d)) = a ⊔ d ⊔ b ⊔ c :=
    fun _ _ c _ => by rw [← sup_assoc, sup_comm c, sup_sup_sup_comm, ← sup_assoc]
  rw [XYIdeal_add_eq]; rw [XIdeal]; rw [mul_comm]; rw [XYIdeal_eq₁ x₁ y₁ <| W.slope x₁ x₂ y₁ y₂]; rw [XYIdeal]; rw [XYIdeal_eq₂ h₁ h₂ hxy]; rw [XYIdeal]; rw [span_pair_mul_span_pair]
  simp_rw [span_insert, sup_rw, Ideal.sup_mul, span_singleton_mul_span_singleton]
  rw [← neg_eq_iff_eq_neg.mpr <| C_addPolynomial_slope h₁ h₂ hxy]; rw [span_singleton_neg]; rw [C_addPolynomial]; rw [map_mul]; rw [YClass]
  simp_rw [mul_comm <| XClass W x₁, mul_assoc, ← span_singleton_mul_span_singleton, ← Ideal.mul_sup]
  rw [span_singleton_mul_span_singleton]; rw [← span_insert]; rw [← span_pair_add_left_mul _ _ -(XClass W <| W.addX x₁ x₂ <| W.slope x₁ x₂ y₁ y₂)]; rw [mul_neg]; rw [← sub_eq_add_neg]; rw [← sub_mul]; rw [← map_sub mk W]; rw [sub_sub_sub_cancel_right]; rw [span_insert]; rw [← span_singleton_mul_span_singleton]; rw [← sup_rw]; rw [← Ideal.sup_mul]; rw [← Ideal.sup_mul]
  apply congr_arg (_ ∘ _)
  convert! top_mul (_ : Ideal W.CoordinateRing)
  simp_rw [XClass, ← Set.image_singleton (f := mk W), ← map_span, ← Ideal.map_sup, eq_top_iff_one,
    mem_map_iff_of_surjective _ AdjoinRoot.mk_surjective, ← span_insert, mem_span_insert',
    mem_span_singleton']
  by_cases hx : x₁ = x₂
  · have hy : y₁ != W.negY x₂ y₂ := fun h => hxy ⟨hx, h⟩
    rcases hx, Y_eq_of_Y_ne h₁ h₂ hx hy with ⟨rfl, rfl⟩
    let y := (y₁ - W.negY x₁ y₁) ^ 2
replace hxy := pow_ne_zero 2 sub_ne_zero_of_ne hy
    refine ⟨1 + C (C <| y⁻¹ * 4) * W.polynomial,
⟨C C y⁻¹ * (C 4 * X ^ 2 + C (4 * x₁ + W.b₂) * X + C (4 * x₁ ^ 2 + W.b₂ * x₁ + 2 * W.b₄)),
        0, C (C y⁻¹) * (Y - W.negPolynomial), ?_⟩, by
      rw [map_add]; rw [map_one]; rw [map_mul <| mk W]; rw [AdjoinRoot.mk_self]; rw [mul_zero]; rw [add_zero]⟩
    rw [polynomial]; rw [negPolynomial]; rw [← mul_right_inj' <| C_ne_zero.mpr <| C_ne_zero.mpr hxy]
    simp only [y, mul_add, ← mul_assoc, ← C_mul, mul_inv_cancel₀ hxy]
    linear_combination (norm := (rw [b₂, b₄, negY]; C_simp; ring1))
      -4 * congr_arg C (congr_arg C <| (equation_iff ..).mp h₁)
  · replace hx := sub_ne_zero_of_ne hx
refine ⟨_, ⟨⟨C C (x₁ - x₂)⁻¹, C C (x₁ - x₂)⁻¹ * -1, 0, ?_⟩, map_one _⟩⟩
    rw [← mul_right_inj' <| C_ne_zero.mpr <| C_ne_zero.mpr hx]
    simp only [← mul_assoc, mul_add, ← C_mul, mul_inv_cancel₀ hx]
    C_simp
    ring1

/--
Definition of `XYIdeal'` / `XYIdeal'` 的定义

English:
definition XYIdeal'
  signature: {x y : F} (h : W.Nonsingular x y)
  body: Units.mkOfMulEqOne (XYIdeal W x (C y)) (XYIdeal W x (C <| W.negY x y) *
      (XIdeal W x : FractionalIdeal W.CoordinateRing⁰ W.FunctionField)⁻¹) <| by
    rw [← mul_assoc]; rw [← coeIdeal_mul]; rw [mul_comm <| XYIdeal W ..]; rw [XYIdeal_neg_mul h]; rw [XIdeal]; rw [FractionalIdeal.coe_ideal_span_si

中文:
定义 XYIdeal'
  签名: {x y : F} (h : W.Nonsingular x y)
  定义体: Units.mkOfMulEqOne (XYIdeal W x (C y)) (XYIdeal W x (C <| W.negY x y) *
      (XIdeal W x : FractionalIdeal W.CoordinateRing⁰ W.FunctionField)⁻¹) <| by
    rw [← mul_assoc]; rw [← coeIdeal_mul]; rw [mul_comm <| XYIdeal W ..]; rw [XYIdeal_neg_mul h]; rw [XIdeal]; rw [FractionalIdeal.coe_ideal_span_si

Depends on / 依赖: FractionalIdeal, FractionalIdeal.coe_ideal_span_singleton_mul_inv, FunctionField, Units.mkOfMulEqOne, W.CoordinateRing, W.FunctionField, W.negY, XClass_ne_zero, XIdeal, XYIdeal, XYIdeal_neg_mul, coeIdeal_mul, coe_ideal_span_singleton_mul_inv, mkOfMulEqOne, mul_assoc, mul_comm
-/
noncomputable def XYIdeal' {x y : F} (h : W.Nonsingular x y) :
    (FractionalIdeal W.CoordinateRing⁰ W.FunctionField)ˣ :=
  Units.mkOfMulEqOne (XYIdeal W x (C y)) (XYIdeal W x (C <| W.negY x y) *
      (XIdeal W x : FractionalIdeal W.CoordinateRing⁰ W.FunctionField)⁻¹) <| by
    rw [← mul_assoc]; rw [← coeIdeal_mul]; rw [mul_comm <| XYIdeal W ..]; rw [XYIdeal_neg_mul h]; rw [XIdeal]; rw [FractionalIdeal.coe_ideal_span_singleton_mul_inv W.FunctionField XClass_ne_zero x]

/--
lemma `XYIdeal'_eq` / 引理 `XYIdeal'_eq`

English:
lemma XYIdeal'_eq
  given: {x y : F} (h : W.Nonsingular x y)
  proof: rfl

中文:
引理 XYIdeal'_eq
  条件: {x y : F} (h : W.Nonsingular x y)
  证明: rfl
-/
lemma XYIdeal'_eq {x y : F} (h : W.Nonsingular x y) :
    (XYIdeal' h : FractionalIdeal W.CoordinateRing⁰ W.FunctionField) = XYIdeal W x (C y) :=
  rfl

/--
lemma `mk_XYIdeal'_neg_mul` / 引理 `mk_XYIdeal'_neg_mul`

English:
lemma mk_XYIdeal'_neg_mul
  given: {x y : F} (h : W.Nonsingular x y)
  proof: by
  rw [← map_mul]
  exact (ClassGroup.mk_eq_one_of_coe_ideal <| (coeIdeal_mul ..).symm.trans <|
FractionalIdeal.coeIdeal_inj.mpr XYIdeal_neg_mul h).mpr ⟨_, XClass_ne_zero x, rfl⟩

中文:
引理 mk_XYIdeal'_neg_mul
  条件: {x y : F} (h : W.Nonsingular x y)
  证明: by
  rw [← map_mul]
  exact (ClassGroup.mk_eq_one_of_coe_ideal <| (coeIdeal_mul ..).symm.trans <|
FractionalIdeal.coeIdeal_inj.mpr XYIdeal_neg_mul h).mpr ⟨_, XClass_ne_zero x, rfl⟩

Depends on / 依赖: ClassGroup, ClassGroup.mk_eq_one_of_coe_ideal, FractionalIdeal, FractionalIdeal.coeIdeal_inj.mpr, XClass_ne_zero, XYIdeal_neg_mul, coeIdeal_inj, coeIdeal_mul, map_mul, mk_eq_one_of_coe_ideal, symm.trans
-/
lemma mk_XYIdeal'_neg_mul {x y : F} (h : W.Nonsingular x y) :
    ClassGroup.mk W.FunctionField (XYIdeal' <| (nonsingular_neg ..).mpr h) *
      ClassGroup.mk W.FunctionField (XYIdeal' h) = 1 := by
  rw [← map_mul]
  exact (ClassGroup.mk_eq_one_of_coe_ideal <| (coeIdeal_mul ..).symm.trans <|
FractionalIdeal.coeIdeal_inj.mpr XYIdeal_neg_mul h).mpr ⟨_, XClass_ne_zero x, rfl⟩

/--
lemma `mk_XYIdeal'_mul_mk_XYIdeal'` / 引理 `mk_XYIdeal'_mul_mk_XYIdeal'`

English:
lemma mk_XYIdeal'_mul_mk_XYIdeal'
  statement: [DecidableEq F] {x₁ x₂ y₁ y₂ : F} (h₁ : W.Nonsingular x₁ y₁)
  proof: by
  rw [← map_mul]
  exact (ClassGroup.mk_eq_mk_of_coe_ideal (coeIdeal_mul ..).symm <| XYIdeal'_eq _).mpr
    ⟨_, _, XClass_ne_zero _, YClass_ne_zero _, XYIdeal_mul_XYIdeal h₁.left h₂.left hxy⟩

中文:
引理 mk_XYIdeal'_mul_mk_XYIdeal'
  结论: [DecidableEq F] {x₁ x₂ y₁ y₂ : F} (h₁ : W.Nonsingular x₁ y₁)
  证明: by
  rw [← map_mul]
  exact (ClassGroup.mk_eq_mk_of_coe_ideal (coeIdeal_mul ..).symm <| XYIdeal'_eq _).mpr
    ⟨_, _, XClass_ne_zero _, YClass_ne_zero _, XYIdeal_mul_XYIdeal h₁.left h₂.left hxy⟩
-/
lemma mk_XYIdeal'_mul_mk_XYIdeal' [DecidableEq F] {x₁ x₂ y₁ y₂ : F} (h₁ : W.Nonsingular x₁ y₁)
    (h₂ : W.Nonsingular x₂ y₂) (hxy : ¬(x₁ = x₂ ∧ y₁ = W.negY x₂ y₂)) :
    ClassGroup.mk W.FunctionField (XYIdeal' h₁) *
        ClassGroup.mk W.FunctionField (XYIdeal' h₂) =
      ClassGroup.mk W.FunctionField (XYIdeal' <| nonsingular_add h₁ h₂ hxy) := by
  rw [← map_mul]
  exact (ClassGroup.mk_eq_mk_of_coe_ideal (coeIdeal_mul ..).symm <| XYIdeal'_eq _).mpr
    ⟨_, _, XClass_ne_zero _, YClass_ne_zero _, XYIdeal_mul_XYIdeal h₁.left h₂.left hxy⟩


/--
lemma `norm_smul_basis` / 引理 `norm_smul_basis`

English:
lemma norm_smul_basis
  given: (p q : R[X])
  statement: Algebra.norm R[X] (p • (1 : W'.CoordinateRing) + q • mk W' Y) =
  proof: by
  simp_rw [Algebra.norm_eq_matrix_det <| CoordinateRing.basis W', Matrix.det_fin_two,
    Algebra.leftMulMatrix_eq_repr_mul, basis_zero, mul_one, basis_one, smul_basis_mul_Y, map_add,
    Finsupp.add_apply, map_smul, Finsupp.smul_apply, ← basis_zero, ← basis_one,
    Basis.repr_self_apply, if_pos

中文:
引理 norm_smul_basis
  条件: (p q : R[X])
  结论: Algebra.norm R[X] (p • (1 : W'.CoordinateRing) + q • mk W' Y) =
  证明: by
  simp_rw [Algebra.norm_eq_matrix_det <| CoordinateRing.basis W', Matrix.det_fin_two,
    Algebra.leftMulMatrix_eq_repr_mul, basis_zero, mul_one, basis_one, smul_basis_mul_Y, map_add,
    Finsupp.add_apply, map_smul, Finsupp.smul_apply, ← basis_zero, ← basis_one,
    Basis.repr_self_apply, if_pos

Depends on / 依赖: Algebra, Algebra.leftMulMatrix_eq_repr_mul, Algebra.norm_eq_matrix_det, Basis.repr_self_apply, CoordinateRing, CoordinateRing.basis, Finsupp, Finsupp.add_apply, Finsupp.smul_apply, Matrix, Matrix.det_fin_two, add_apply, basis_one, basis_zero, det_fin_two, if_false, if_pos, leftMulMatrix_eq_repr_mul, map_add, map_smul
-/
lemma norm_smul_basis (p q : R[X]) : Algebra.norm R[X] (p • (1 : W'.CoordinateRing) + q • mk W' Y) =
    p ^ 2 - p * q * (C W'.a₁ * X + C W'.a₃) -
      q ^ 2 * (X ^ 3 + C W'.a₂ * X ^ 2 + C W'.a₄ * X + C W'.a₆) := by
  simp_rw [Algebra.norm_eq_matrix_det <| CoordinateRing.basis W', Matrix.det_fin_two,
    Algebra.leftMulMatrix_eq_repr_mul, basis_zero, mul_one, basis_one, smul_basis_mul_Y, map_add,
    Finsupp.add_apply, map_smul, Finsupp.smul_apply, ← basis_zero, ← basis_one,
    Basis.repr_self_apply, if_pos, one_ne_zero, if_false, smul_eq_mul]
  ring1

/--
lemma `coe_norm_smul_basis` / 引理 `coe_norm_smul_basis`

English:
lemma coe_norm_smul_basis
  given: (p q : R[X])
  statement: Algebra.norm R[X] (p • 1 + q • mk W' Y) =
  proof: AdjoinRoot.mk_eq_mk.mpr ⟨C q ^ 2, by simp only [norm_smul_basis, polynomial]; C_simp; ring1⟩

中文:
引理 coe_norm_smul_basis
  条件: (p q : R[X])
  结论: Algebra.norm R[X] (p • 1 + q • mk W' Y) =
  证明: AdjoinRoot.mk_eq_mk.mpr ⟨C q ^ 2, by simp only [norm_smul_basis, polynomial]; C_simp; ring1⟩

Depends on / 依赖: AdjoinRoot, AdjoinRoot.mk_eq_mk.mpr, C_simp, mk_eq_mk, norm_smul_basis, polynomial
-/
lemma coe_norm_smul_basis (p q : R[X]) : Algebra.norm R[X] (p • 1 + q • mk W' Y) =
    mk W' ((C p + C q * X) * (C p + C q * (-(Y : R[X][Y]) - C (C W'.a₁ * X + C W'.a₃)))) :=
  AdjoinRoot.mk_eq_mk.mpr ⟨C q ^ 2, by simp only [norm_smul_basis, polynomial]; C_simp; ring1⟩

/--
lemma `degree_norm_smul_basis` / 引理 `degree_norm_smul_basis`

English:
lemma degree_norm_smul_basis
  given: [IsDomain R] (p q : R[X])
  proof: by
  have hdp : (p ^ 2).degree = 2 • p.degree := degree_pow p 2
  have hdpq : (p * q * (C W'.a₁ * X + C W'.a₃)).degree <= p.degree + q.degree + 1 := by
    grw [degree_mul, degree_mul, degree_linear_le]
  have hdq :
      (q ^ 2 * (X ^ 3 + C W'.a₂ * X ^ 2 + C W'.a₄ * X + C W'.a₆)).degree = 2 • q.deg

中文:
引理 degree_norm_smul_basis
  条件: [IsDomain R] (p q : R[X])
  证明: by
  have hdp : (p ^ 2).degree = 2 • p.degree := degree_pow p 2
  have hdpq : (p * q * (C W'.a₁ * X + C W'.a₃)).degree <= p.degree + q.degree + 1 := by
    grw [degree_mul, degree_mul, degree_linear_le]
  have hdq :
      (q ^ 2 * (X ^ 3 + C W'.a₂ * X ^ 2 + C W'.a₄ * X + C W'.a₆)).degree = 2 • q.deg

Depends on / 依赖: degree, degree_cubic, degree_linear_le, degree_mul, degree_pow, neg_zero, norm_smul_basis, one_mul, one_ne_zero, p.degree, q.degree, zero_mul, zero_sub
-/
lemma degree_norm_smul_basis [IsDomain R] (p q : R[X]) :
    (Algebra.norm R[X] <| p • 1 + q • mk W' Y).degree = max (2 • p.degree) (2 • q.degree + 3) := by
  have hdp : (p ^ 2).degree = 2 • p.degree := degree_pow p 2
  have hdpq : (p * q * (C W'.a₁ * X + C W'.a₃)).degree <= p.degree + q.degree + 1 := by
    grw [degree_mul, degree_mul, degree_linear_le]
  have hdq :
      (q ^ 2 * (X ^ 3 + C W'.a₂ * X ^ 2 + C W'.a₄ * X + C W'.a₆)).degree = 2 • q.degree + 3 := by
    rw [degree_mul]; rw [degree_pow]; rw [← one_mul <| X ^ 3]; rw [← C_1]; rw [degree_cubic <| one_ne_zero' R]
  rw [norm_smul_basis]
  by_cases hp : p = 0
  · simp only [hp, hdq, neg_zero, zero_sub, zero_mul, zero_pow two_ne_zero, degree_neg]
    exact (max_bot_left _).symm
  · by_cases hq : q = 0
    · simp only [hq, hdp, sub_zero, zero_mul, mul_zero, zero_pow two_ne_zero]
      exact (max_bot_right _).symm
    · rw [← not_congr degree_eq_bot] at hp hq
      -- Porting note: BUG `cases` tactic does not modify assumptions in `hp'` and `hq'`
      rcases hp' : p.degree with _ | dp -- `hp' : ` should be redundant
      · exact (hp hp').elim -- `hp'` should be `rfl`
      · rw [hp'] at hdp hdpq -- line should be redundant
        rcases hq' : q.degree with _ | dq -- `hq' : ` should be redundant
        · exact (hq hq').elim -- `hq'` should be `rfl`
        · rw [hq'] at hdpq hdq -- line should be redundant
          rcases le_or_gt dp (dq + 1) with hpq | hpq
          · convert!
            (degree_sub_eq_right_of_degree_lt <|
(degree_sub_le _ _).trans_lt
                    max_lt_iff.mpr ⟨hdp.trans_lt _, hdpq.trans_lt _⟩).trans
              (max_eq_right_of_lt _).symm <;> rw [hdq] <;>
exact WithBot.coe_lt_coe.mpr by dsimp; linarith only [hpq]
          · rw [sub_sub]
            convert!
              (degree_sub_eq_left_of_degree_lt <|
(degree_add_le _ _).trans_lt
                      max_lt_iff.mpr ⟨hdpq.trans_lt _, hdq.trans_lt _⟩).trans
                (max_eq_left_of_lt _).symm <;> rw [hdp] <;>
exact WithBot.coe_lt_coe.mpr by dsimp; linarith only [hpq]

/--
lemma `degree_norm_ne_one` / 引理 `degree_norm_ne_one`

English:
lemma degree_norm_ne_one
  given: [IsDomain R] (x : W'.CoordinateRing)
  proof: by
  rcases exists_smul_basis_eq x with ⟨p, q, rfl⟩
  rw [degree_norm_smul_basis]
  rcases p.degree with (_ | _ | _ | _) <;> cases q.degree
  any_goals rintro (_ | _)
  exact (lt_max_of_lt_right <| (cmp_eq_lt_iff ..).mp rfl).ne'

中文:
引理 degree_norm_ne_one
  条件: [IsDomain R] (x : W'.CoordinateRing)
  证明: by
  rcases exists_smul_basis_eq x with ⟨p, q, rfl⟩
  rw [degree_norm_smul_basis]
  rcases p.degree with (_ | _ | _ | _) <;> cases q.degree
  any_goals rintro (_ | _)
  exact (lt_max_of_lt_right <| (cmp_eq_lt_iff ..).mp rfl).ne'

Depends on / 依赖: any_goals, cmp_eq_lt_iff, degree, degree_norm_smul_basis, exists_smul_basis_eq, lt_max_of_lt_right, p.degree, q.degree
-/
lemma degree_norm_ne_one [IsDomain R] (x : W'.CoordinateRing) :
    (Algebra.norm R[X] x).degree != 1 := by
  rcases exists_smul_basis_eq x with ⟨p, q, rfl⟩
  rw [degree_norm_smul_basis]
  rcases p.degree with (_ | _ | _ | _) <;> cases q.degree
  any_goals rintro (_ | _)
  exact (lt_max_of_lt_right <| (cmp_eq_lt_iff ..).mp rfl).ne'

/--
lemma `natDegree_norm_ne_one` / 引理 `natDegree_norm_ne_one`

English:
lemma natDegree_norm_ne_one
  given: [IsDomain R] (x : W'.CoordinateRing)
  proof: degree_norm_ne_one x ∘ (degree_eq_iff_natDegree_eq_of_pos zero_lt_one).mpr

中文:
引理 natDegree_norm_ne_one
  条件: [IsDomain R] (x : W'.CoordinateRing)
  证明: degree_norm_ne_one x ∘ (degree_eq_iff_natDegree_eq_of_pos zero_lt_one).mpr

Depends on / 依赖: degree_eq_iff_natDegree_eq_of_pos, degree_norm_ne_one, zero_lt_one
-/
lemma natDegree_norm_ne_one [IsDomain R] (x : W'.CoordinateRing) :
    (Algebra.norm R[X] x).natDegree != 1 :=
  degree_norm_ne_one x ∘ (degree_eq_iff_natDegree_eq_of_pos zero_lt_one).mpr

end CoordinateRing

/-! ## Nonsingular points in affine coordinates -/

variable (W') in
/--
Inductive type `Point` / 归纳类型 `Point`

English:
inductive Point
  constructors (2):
    - zero: 
    - some: (x y : R) (h : W'.Nonsingular x y)

中文:
归纳类型 Point
  构造子 (2 个):
    - zero: 
    - some: (x y : R) (h : W'.Nonsingular x y)
-/
inductive Point
  | zero
  | some (x y : R) (h : W'.Nonsingular x y)
deriving DecidableEq

/--
Definition of `nonsingularPointEquivSubtype` / `nonsingularPointEquivSubtype` 的定义

English:
definition nonsingularPointEquivSubtype
  signature: {p : W'.Point -> Prop} (p0 : p .zero)
  body: P.casesOn ⟨.zero, p0⟩ fun xy => ⟨.some _ _ xy.prop.choose, xy.prop.choose_spec⟩
  left_inv := by rintro (_ | _) <;> rfl
  right_inv := by rintro (_ | _) <;> rfl

@[simp]

中文:
定义 nonsingularPointEquivSubtype
  签名: {p : W'.Point -> 命题} (p0 : p .zero)
  定义体: P.casesOn ⟨.zero, p0⟩ fun xy => ⟨.some _ _ xy.prop.choose, xy.prop.choose_spec⟩
  left_inv := by rintro (_ | _) <;> rfl
  right_inv := by rintro (_ | _) <;> rfl

@[simp]

Depends on / 依赖: P.casesOn, casesOn, choose_spec, xy.prop.choose, xy.prop.choose_spec
-/
def nonsingularPointEquivSubtype {p : W'.Point -> Prop} (p0 : p .zero) : {P : W'.Point // p P} ≃
    WithZero {xy : R × R // exists h : W'.Nonsingular xy.fst xy.snd, p <| .some _ _ h} where
  toFun
    | ⟨.zero, _⟩ => none
    | ⟨.some _ _ h, ph⟩ => .some ⟨⟨_, _⟩, h, ph⟩
  invFun P := P.casesOn ⟨.zero, p0⟩ fun xy => ⟨.some _ _ xy.prop.choose, xy.prop.choose_spec⟩
  left_inv := by rintro (_ | _) <;> rfl
  right_inv := by rintro (_ | _) <;> rfl

@[simp]
/--
lemma `nonsingularPointEquivSubtype_zero` / 引理 `nonsingularPointEquivSubtype_zero`

English:
lemma nonsingularPointEquivSubtype_zero
  given: {p : W'.Point -> Prop} (p0 : p .zero)
  proof: rfl

@[simp]

中文:
引理 nonsingularPointEquivSubtype_zero
  条件: {p : W'.Point -> 命题} (p0 : p .zero)
  证明: rfl

@[simp]
-/
lemma nonsingularPointEquivSubtype_zero {p : W'.Point -> Prop} (p0 : p .zero) :
    nonsingularPointEquivSubtype p0 ⟨.zero, p0⟩ = none :=
  rfl

@[simp]
/--
lemma `nonsingularPointEquivSubtype_some` / 引理 `nonsingularPointEquivSubtype_some`

English:
lemma nonsingularPointEquivSubtype_some
  statement: {x y : R} {h : W'.Nonsingular x y} {p : W'.Point -> Prop}
  proof: rfl

@[simp]

中文:
引理 nonsingularPointEquivSubtype_some
  结论: {x y : R} {h : W'.Nonsingular x y} {p : W'.Point -> 命题}
  证明: rfl

@[simp]
-/
lemma nonsingularPointEquivSubtype_some {x y : R} {h : W'.Nonsingular x y} {p : W'.Point -> Prop}
    (p0 : p .zero) (ph : p <| .some _ _ h) :
    nonsingularPointEquivSubtype p0 ⟨.some _ _ h, ph⟩ = .some ⟨⟨x, y⟩, h, ph⟩ :=
  rfl

@[simp]
/--
lemma `nonsingularPointEquivSubtype_symm_none` / 引理 `nonsingularPointEquivSubtype_symm_none`

English:
lemma nonsingularPointEquivSubtype_symm_none
  given: {p : W'.Point -> Prop} (p0 : p .zero)
  proof: rfl

@[simp]

中文:
引理 nonsingularPointEquivSubtype_symm_none
  条件: {p : W'.Point -> 命题} (p0 : p .zero)
  证明: rfl

@[simp]
-/
lemma nonsingularPointEquivSubtype_symm_none {p : W'.Point -> Prop} (p0 : p .zero) :
    (nonsingularPointEquivSubtype p0).symm none = ⟨.zero, p0⟩ :=
  rfl

@[simp]
/--
lemma `nonsingularPointEquivSubtype_symm_some` / 引理 `nonsingularPointEquivSubtype_symm_some`

English:
lemma nonsingularPointEquivSubtype_symm_some
  statement: {x y : R} {h : W'.Nonsingular x y}
  proof: rfl

中文:
引理 nonsingularPointEquivSubtype_symm_some
  结论: {x y : R} {h : W'.Nonsingular x y}
  证明: rfl
-/
lemma nonsingularPointEquivSubtype_symm_some {x y : R} {h : W'.Nonsingular x y}
    {p : W'.Point -> Prop} (p0 : p .zero) (ph : p <| .some _ _ h) :
    (nonsingularPointEquivSubtype p0).symm (.some ⟨⟨x, y⟩, h, ph⟩) = ⟨.some _ _ h, ph⟩ :=
  rfl

variable (W') in
/--
Definition of `nonsingularPointEquiv` / `nonsingularPointEquiv` 的定义

English:
definition nonsingularPointEquiv
  signature: : W'.Point ≃ WithZero {xy : R × R // W'.Nonsingular xy.fst xy.snd}
  body: (Equiv.Set.univ W'.Point).symm.trans (nonsingularPointEquivSubtype trivial).trans
    (Equiv.subtypeEquivProp <| by simp).optionCongr

@[simp]

中文:
定义 nonsingularPointEquiv
  签名: : W'.Point ≃ WithZero {xy : R × R // W'.Nonsingular xy.fst xy.snd}
  定义体: (Equiv.Set.univ W'.Point).symm.trans (nonsingularPointEquivSubtype trivial).trans
    (Equiv.subtypeEquivProp <| by simp).optionCongr

@[simp]

Depends on / 依赖: Equiv.Set.univ, Equiv.subtypeEquivProp, nonsingularPointEquivSubtype, optionCongr, subtypeEquivProp, symm.trans
-/
def nonsingularPointEquiv : W'.Point ≃ WithZero {xy : R × R // W'.Nonsingular xy.fst xy.snd} :=
(Equiv.Set.univ W'.Point).symm.trans (nonsingularPointEquivSubtype trivial).trans
    (Equiv.subtypeEquivProp <| by simp).optionCongr

@[simp]
/--
lemma `nonsingularPointEquiv_zero` / 引理 `nonsingularPointEquiv_zero`

English:
lemma nonsingularPointEquiv_zero
  statement: nonsingularPointEquiv W' .zero = none
  proof: rfl

@[simp]

中文:
引理 nonsingularPointEquiv_zero
  结论: nonsingularPointEquiv W' .zero = none
  证明: rfl

@[simp]
-/
lemma nonsingularPointEquiv_zero : nonsingularPointEquiv W' .zero = none :=
  rfl

@[simp]
/--
lemma `nonsingularPointEquiv_some` / 引理 `nonsingularPointEquiv_some`

English:
lemma nonsingularPointEquiv_some
  given: {x y : R} (h : W'.Nonsingular x y)
  proof: by
  rfl

@[simp]

中文:
引理 nonsingularPointEquiv_some
  条件: {x y : R} (h : W'.Nonsingular x y)
  证明: by
  rfl

@[simp]
-/
lemma nonsingularPointEquiv_some {x y : R} (h : W'.Nonsingular x y) :
    W'.nonsingularPointEquiv (.some _ _ h) = .some ⟨⟨x, y⟩, h⟩ := by
  rfl

@[simp]
/--
lemma `nonsingularPointEquiv_symm_none` / 引理 `nonsingularPointEquiv_symm_none`

English:
lemma nonsingularPointEquiv_symm_none
  statement: W'.nonsingularPointEquiv.symm none = .zero
  proof: rfl

@[simp]

中文:
引理 nonsingularPointEquiv_symm_none
  结论: W'.nonsingularPointEquiv.symm none = .zero
  证明: rfl

@[simp]
-/
lemma nonsingularPointEquiv_symm_none : W'.nonsingularPointEquiv.symm none = .zero :=
  rfl

@[simp]
/--
lemma `nonsingularPointEquiv_symm_some` / 引理 `nonsingularPointEquiv_symm_some`

English:
lemma nonsingularPointEquiv_symm_some
  given: {x y : R} (h : W'.Nonsingular x y)
  proof: rfl

中文:
引理 nonsingularPointEquiv_symm_some
  条件: {x y : R} (h : W'.Nonsingular x y)
  证明: rfl
-/
lemma nonsingularPointEquiv_symm_some {x y : R} (h : W'.Nonsingular x y) :
    W'.nonsingularPointEquiv.symm (.some ⟨⟨x, y⟩, h⟩) = .some _ _ h :=
  rfl

section IsElliptic

variable [Nontrivial R] [W'.IsElliptic]

/--
Definition of `Point.mk` / `Point.mk` 的定义

English:
definition Point.mk
  signature: {x y : R} (h : W'.Equation x y)
  body: .some _ _ equation_iff_nonsingular.mp h

中文:
定义 Point.mk
  签名: {x y : R} (h : W'.Equation x y)
  定义体: .some _ _ equation_iff_nonsingular.mp h

Depends on / 依赖: equation_iff_nonsingular, equation_iff_nonsingular.mp
-/
def Point.mk {x y : R} (h : W'.Equation x y) : W'.Point :=
.some _ _ equation_iff_nonsingular.mp h

/--
Definition of `pointEquivSubtype` / `pointEquivSubtype` 的定义

English:
definition pointEquivSubtype
  signature: {p : W'.Point -> Prop} (p0 : p .zero)
  body: (nonsingularPointEquivSubtype p0).trans
    (Equiv.subtypeEquivProp <| by ext; simp [equation_iff_nonsingular, Point.mk]).optionCongr

@[simp]

中文:
定义 pointEquivSubtype
  签名: {p : W'.Point -> 命题} (p0 : p .zero)
  定义体: (nonsingularPointEquivSubtype p0).trans
    (Equiv.subtypeEquivProp <| by ext; simp [equation_iff_nonsingular, Point.mk]).optionCongr

@[simp]

Depends on / 依赖: Equiv.subtypeEquivProp, Point.mk, equation_iff_nonsingular, nonsingularPointEquivSubtype, optionCongr, subtypeEquivProp
-/
def pointEquivSubtype {p : W'.Point -> Prop} (p0 : p .zero) :
    {P : W'.Point // p P} ≃ WithZero {xy : R × R // exists h : W'.Equation xy.fst xy.snd, p <| .mk h} :=
  (nonsingularPointEquivSubtype p0).trans
    (Equiv.subtypeEquivProp <| by ext; simp [equation_iff_nonsingular, Point.mk]).optionCongr

@[simp]
/--
lemma `pointEquivSubtype_zero` / 引理 `pointEquivSubtype_zero`

English:
lemma pointEquivSubtype_zero
  given: {p : W'.Point -> Prop} (p0 : p .zero)
  proof: rfl

@[simp]

中文:
引理 pointEquivSubtype_zero
  条件: {p : W'.Point -> 命题} (p0 : p .zero)
  证明: rfl

@[simp]
-/
lemma pointEquivSubtype_zero {p : W'.Point -> Prop} (p0 : p .zero) :
    pointEquivSubtype p0 ⟨.zero, p0⟩ = none :=
  rfl

@[simp]
/--
lemma `pointEquivSubtype_some` / 引理 `pointEquivSubtype_some`

English:
lemma pointEquivSubtype_some
  statement: {x y : R} {h : W'.Equation x y} {p : W'.Point -> Prop} (p0 : p .zero)
  proof: rfl

@[simp]

中文:
引理 pointEquivSubtype_some
  结论: {x y : R} {h : W'.Equation x y} {p : W'.Point -> 命题} (p0 : p .zero)
  证明: rfl

@[simp]
-/
lemma pointEquivSubtype_some {x y : R} {h : W'.Equation x y} {p : W'.Point -> Prop} (p0 : p .zero)
    (ph : p <| .mk h) : pointEquivSubtype p0 ⟨.mk h, ph⟩ = .some ⟨⟨x, y⟩, h, ph⟩ :=
  rfl

@[simp]
/--
lemma `pointEquivSubtype_symm_none` / 引理 `pointEquivSubtype_symm_none`

English:
lemma pointEquivSubtype_symm_none
  given: {p : W'.Point -> Prop} (p0 : p .zero)
  proof: rfl

@[simp]

中文:
引理 pointEquivSubtype_symm_none
  条件: {p : W'.Point -> 命题} (p0 : p .zero)
  证明: rfl

@[simp]
-/
lemma pointEquivSubtype_symm_none {p : W'.Point -> Prop} (p0 : p .zero) :
    (pointEquivSubtype p0).symm none = ⟨.zero, p0⟩ :=
  rfl

@[simp]
/--
lemma `pointEquivSubtype_symm_some` / 引理 `pointEquivSubtype_symm_some`

English:
lemma pointEquivSubtype_symm_some
  statement: {x y : R} {h : W'.Equation x y} {p : W'.Point -> Prop}
  proof: rfl

中文:
引理 pointEquivSubtype_symm_some
  结论: {x y : R} {h : W'.Equation x y} {p : W'.Point -> 命题}
  证明: rfl
-/
lemma pointEquivSubtype_symm_some {x y : R} {h : W'.Equation x y} {p : W'.Point -> Prop}
    (p0 : p .zero) (ph : p <| .mk h) :
    (pointEquivSubtype p0).symm (.some ⟨⟨x, y⟩, h, ph⟩) = ⟨.mk h, ph⟩ :=
  rfl

variable (W') in
/--
Definition of `pointEquiv` / `pointEquiv` 的定义

English:
definition pointEquiv
  signature: : W'.Point ≃ WithZero {xy : R × R // W'.Equation xy.fst xy.snd}
  body: (Equiv.Set.univ W'.Point).symm.trans (pointEquivSubtype trivial).trans
    (Equiv.subtypeEquivProp <| by simp).optionCongr

@[simp]

中文:
定义 pointEquiv
  签名: : W'.Point ≃ WithZero {xy : R × R // W'.Equation xy.fst xy.snd}
  定义体: (Equiv.Set.univ W'.Point).symm.trans (pointEquivSubtype trivial).trans
    (Equiv.subtypeEquivProp <| by simp).optionCongr

@[simp]

Depends on / 依赖: Equiv.Set.univ, Equiv.subtypeEquivProp, optionCongr, pointEquivSubtype, subtypeEquivProp, symm.trans
-/
def pointEquiv : W'.Point ≃ WithZero {xy : R × R // W'.Equation xy.fst xy.snd} :=
(Equiv.Set.univ W'.Point).symm.trans (pointEquivSubtype trivial).trans
    (Equiv.subtypeEquivProp <| by simp).optionCongr

@[simp]
/--
lemma `pointEquiv_zero` / 引理 `pointEquiv_zero`

English:
lemma pointEquiv_zero
  statement: W'.pointEquiv .zero = none
  proof: rfl

@[simp]

中文:
引理 pointEquiv_zero
  结论: W'.pointEquiv .zero = none
  证明: rfl

@[simp]
-/
lemma pointEquiv_zero : W'.pointEquiv .zero = none :=
  rfl

@[simp]
/--
lemma `pointEquiv_some` / 引理 `pointEquiv_some`

English:
lemma pointEquiv_some
  given: {x y : R} (h : W'.Equation x y)
  proof: by
  rfl

@[simp]

中文:
引理 pointEquiv_some
  条件: {x y : R} (h : W'.Equation x y)
  证明: by
  rfl

@[simp]
-/
lemma pointEquiv_some {x y : R} (h : W'.Equation x y) :
    pointEquiv W' (.mk h) = .some ⟨⟨x, y⟩, h⟩ := by
  rfl

@[simp]
/--
lemma `pointEquiv_symm_none` / 引理 `pointEquiv_symm_none`

English:
lemma pointEquiv_symm_none
  statement: (pointEquiv W').symm none = .zero
  proof: rfl

@[simp]

中文:
引理 pointEquiv_symm_none
  结论: (pointEquiv W').symm none = .zero
  证明: rfl

@[simp]
-/
lemma pointEquiv_symm_none : (pointEquiv W').symm none = .zero :=
  rfl

@[simp]
/--
lemma `pointEquiv_symm_some` / 引理 `pointEquiv_symm_some`

English:
lemma pointEquiv_symm_some
  given: {x y : R} (h : W'.Equation x y)
  proof: rfl

中文:
引理 pointEquiv_symm_some
  条件: {x y : R} (h : W'.Equation x y)
  证明: rfl
-/
lemma pointEquiv_symm_some {x y : R} (h : W'.Equation x y) :
    (pointEquiv W').symm (.some ⟨⟨x, y⟩, h⟩) = .mk h :=
  rfl

end IsElliptic

namespace Point


/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Inhabited W'.Point
  body: ⟨zero⟩

中文:
实例 :
  签名: Inhabited W'.Point
  定义体: ⟨zero⟩
-/
instance : Inhabited W'.Point :=
  ⟨zero⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Zero W'.Point
  body: ⟨zero⟩

中文:
实例 :
  签名: Zero W'.Point
  定义体: ⟨zero⟩
-/
instance : Zero W'.Point :=
  ⟨zero⟩

/--
lemma `zero_def` / 引理 `zero_def`

English:
lemma zero_def
  statement: 0 = (zero : W'.Point)
  proof: rfl

中文:
引理 zero_def
  结论: 0 = (zero : W'.Point)
  证明: rfl
-/
lemma zero_def : 0 = (zero : W'.Point) :=
  rfl

/--
lemma `some_ne_zero` / 引理 `some_ne_zero`

English:
lemma some_ne_zero
  given: {x y : R} (h : W'.Nonsingular x y)
  statement: some _ _ h != 0
  proof: by
  rintro (_ | _)

中文:
引理 some_ne_zero
  条件: {x y : R} (h : W'.Nonsingular x y)
  结论: some _ _ h != 0
  证明: by
  rintro (_ | _)
-/
lemma some_ne_zero {x y : R} (h : W'.Nonsingular x y) : some _ _ h != 0 := by
  rintro (_ | _)

/--
Definition of `neg` / `neg` 的定义

English:
definition neg
  signature: : W'.Point -> W'.Point

中文:
定义 neg
  签名: : W'.Point -> W'.Point
-/
def neg : W'.Point -> W'.Point
  | 0 => 0
| some _ _ h => some _ _ (nonsingular_neg ..).mpr h

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Neg W'.Point
  body: ⟨neg⟩

中文:
实例 :
  签名: Neg W'.Point
  定义体: ⟨neg⟩
-/
instance : Neg W'.Point :=
  ⟨neg⟩

/--
lemma `neg_def` / 引理 `neg_def`

English:
lemma neg_def
  given: (P : W'.Point)
  statement: -P = P.neg
  proof: rfl

@[simp]

中文:
引理 neg_def
  条件: (P : W'.Point)
  结论: -P = P.neg
  证明: rfl

@[simp]
-/
lemma neg_def (P : W'.Point) : -P = P.neg :=
  rfl

@[simp]
/--
lemma `neg_zero` / 引理 `neg_zero`

English:
lemma neg_zero
  statement: (-0 : W'.Point) = 0
  proof: rfl

@[simp]

中文:
引理 neg_zero
  结论: (-0 : W'.Point) = 0
  证明: rfl

@[simp]
-/
lemma neg_zero : (-0 : W'.Point) = 0 :=
  rfl

@[simp]
/--
lemma `neg_some` / 引理 `neg_some`

English:
lemma neg_some
  given: {x y : R} (h : W'.Nonsingular x y)
  proof: rfl

中文:
引理 neg_some
  条件: {x y : R} (h : W'.Nonsingular x y)
  证明: rfl
-/
lemma neg_some {x y : R} (h : W'.Nonsingular x y) :
    -some _ _ h = some _ _ ((nonsingular_neg ..).mpr h) :=
  rfl

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: InvolutiveNeg W'.Point
  body: by
    rintro (_ | _)
    · rfl
    · simp only [neg_some, negY_negY]

中文:
实例 :
  签名: InvolutiveNeg W'.Point
  定义体: by
    rintro (_ | _)
    · rfl
    · simp only [neg_some, negY_negY]

Depends on / 依赖: negY_negY, neg_some
-/
instance : InvolutiveNeg W'.Point where
  neg_neg := by
    rintro (_ | _)
    · rfl
    · simp only [neg_some, negY_negY]

/--
lemma `X_eq_iff` / 引理 `X_eq_iff`

English:
lemma X_eq_iff
  given: {x₁ y₁ x₂ y₂ : F} {h₁ : W.Nonsingular x₁ y₁} {h₂ : W.Nonsingular x₂ y₂}
  proof: by
  refine ⟨fun H => ?_, fun H => by grind [neg_some]⟩
  simp_rw [neg_some, some.injEq, ← and_or_left]
  exact ⟨H, Y_eq_of_X_eq h₁.1 h₂.1 H⟩

中文:
引理 X_eq_iff
  条件: {x₁ y₁ x₂ y₂ : F} {h₁ : W.Nonsingular x₁ y₁} {h₂ : W.Nonsingular x₂ y₂}
  证明: by
  refine ⟨fun H => ?_, fun H => by grind [neg_some]⟩
  simp_rw [neg_some, some.injEq, ← and_or_left]
  exact ⟨H, Y_eq_of_X_eq h₁.1 h₂.1 H⟩

Depends on / 依赖: Y_eq_of_X_eq, and_or_left, neg_some, simp_rw, some.injEq
-/
lemma X_eq_iff {x₁ y₁ x₂ y₂ : F} {h₁ : W.Nonsingular x₁ y₁} {h₂ : W.Nonsingular x₂ y₂} :
    x₁ = x₂ ↔ some x₁ y₁ h₁ = some x₂ y₂ h₂ ∨ some x₁ y₁ h₁ = -some x₂ y₂ h₂ := by
  refine ⟨fun H => ?_, fun H => by grind [neg_some]⟩
  simp_rw [neg_some, some.injEq, ← and_or_left]
  exact ⟨H, Y_eq_of_X_eq h₁.1 h₂.1 H⟩

variable [DecidableEq F] [DecidableEq K] [DecidableEq L]

/--
Definition of `add` / `add` 的定义

English:
definition add
  signature: : W.Point -> W.Point -> W.Point

中文:
定义 add
  签名: : W.Point -> W.Point -> W.Point
-/
def add : W.Point -> W.Point -> W.Point
  | 0, P => P
  | P, 0 => P
  | some x₁ y₁ h₁, some x₂ y₂ h₂ =>
if hxy : x₁ = x₂ ∧ y₁ = W.negY x₂ y₂ then 0 else some _ _ nonsingular_add h₁ h₂ hxy

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Add W.Point
  body: ⟨add⟩

中文:
实例 :
  签名: Add W.Point
  定义体: ⟨add⟩
-/
instance : Add W.Point :=
  ⟨add⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: AddZeroClass W.Point
  body: by rintro (_ | _) <;> rfl
  add_zero := by rintro (_ | _) <;> rfl

中文:
实例 :
  签名: AddZeroClass W.Point
  定义体: by rintro (_ | _) <;> rfl
  add_zero := by rintro (_ | _) <;> rfl

Depends on / 依赖: add_zero
-/
instance : AddZeroClass W.Point where
  zero_add := by rintro (_ | _) <;> rfl
  add_zero := by rintro (_ | _) <;> rfl

/--
lemma `add_def` / 引理 `add_def`

English:
lemma add_def
  given: (P Q : W.Point)
  statement: P + Q = P.add Q
  proof: rfl

中文:
引理 add_def
  条件: (P Q : W.Point)
  结论: P + Q = P.add Q
  证明: rfl
-/
lemma add_def (P Q : W.Point) : P + Q = P.add Q :=
  rfl

/--
lemma `add_some` / 引理 `add_some`

English:
lemma add_some
  statement: {x₁ x₂ y₁ y₂ : F} (hxy : ¬(x₁ = x₂ ∧ y₁ = W.negY x₂ y₂)) {h₁ : W.Nonsingular x₁ y₁}
  proof: by
  simp only [add_def, add, dif_neg hxy]

@[simp]

中文:
引理 add_some
  结论: {x₁ x₂ y₁ y₂ : F} (hxy : ¬(x₁ = x₂ ∧ y₁ = W.negY x₂ y₂)) {h₁ : W.Nonsingular x₁ y₁}
  证明: by
  simp only [add_def, add, dif_neg hxy]

@[simp]

Depends on / 依赖: add_def, dif_neg
-/
lemma add_some {x₁ x₂ y₁ y₂ : F} (hxy : ¬(x₁ = x₂ ∧ y₁ = W.negY x₂ y₂)) {h₁ : W.Nonsingular x₁ y₁}
    {h₂ : W.Nonsingular x₂ y₂} :
    some _ _ h₁ + some _ _ h₂ = some _ _ (nonsingular_add h₁ h₂ hxy) := by
  simp only [add_def, add, dif_neg hxy]

@[simp]
/--
lemma `add_of_Y_eq` / 引理 `add_of_Y_eq`

English:
lemma add_of_Y_eq
  statement: {x₁ x₂ y₁ y₂ : F} {h₁ : W.Nonsingular x₁ y₁} {h₂ : W.Nonsingular x₂ y₂}
  proof: by
  simpa only [add_def, add] using dif_pos ⟨hx, hy⟩

中文:
引理 add_of_Y_eq
  结论: {x₁ x₂ y₁ y₂ : F} {h₁ : W.Nonsingular x₁ y₁} {h₂ : W.Nonsingular x₂ y₂}
  证明: by
  simpa only [add_def, add] using dif_pos ⟨hx, hy⟩

Depends on / 依赖: add_def, dif_pos
-/
lemma add_of_Y_eq {x₁ x₂ y₁ y₂ : F} {h₁ : W.Nonsingular x₁ y₁} {h₂ : W.Nonsingular x₂ y₂}
    (hx : x₁ = x₂) (hy : y₁ = W.negY x₂ y₂) : some _ _ h₁ + some _ _ h₂ = 0 := by
  simpa only [add_def, add] using dif_pos ⟨hx, hy⟩

-- Removing `@[simp]`, because `hy` causes a maximum recursion depth error in the simpNF linter.
/--
lemma `add_self_of_Y_eq` / 引理 `add_self_of_Y_eq`

English:
lemma add_self_of_Y_eq
  given: {x₁ y₁ : F} {h₁ : W.Nonsingular x₁ y₁} (hy : y₁ = W.negY x₁ y₁)
  proof: add_of_Y_eq rfl hy

中文:
引理 add_self_of_Y_eq
  条件: {x₁ y₁ : F} {h₁ : W.Nonsingular x₁ y₁} (hy : y₁ = W.negY x₁ y₁)
  证明: add_of_Y_eq rfl hy

Depends on / 依赖: add_of_Y_eq
-/
lemma add_self_of_Y_eq {x₁ y₁ : F} {h₁ : W.Nonsingular x₁ y₁} (hy : y₁ = W.negY x₁ y₁) :
    some _ _ h₁ + some _ _ h₁ = 0 :=
  add_of_Y_eq rfl hy

-- @[simp] -- Not a good simp lemma, since `hy` is not in simp normal form.
/--
lemma `add_of_Y_ne` / 引理 `add_of_Y_ne`

English:
lemma add_of_Y_ne
  statement: {x₁ x₂ y₁ y₂ : F} {h₁ : W.Nonsingular x₁ y₁} {h₂ : W.Nonsingular x₂ y₂}
  proof: add_some fun hxy => hy hxy.right

中文:
引理 add_of_Y_ne
  结论: {x₁ x₂ y₁ y₂ : F} {h₁ : W.Nonsingular x₁ y₁} {h₂ : W.Nonsingular x₂ y₂}
  证明: add_some fun hxy => hy hxy.right

Depends on / 依赖: add_some, hxy.right
-/
lemma add_of_Y_ne {x₁ x₂ y₁ y₂ : F} {h₁ : W.Nonsingular x₁ y₁} {h₂ : W.Nonsingular x₂ y₂}
    (hy : y₁ != W.negY x₂ y₂) :
    some _ _ h₁ + some _ _ h₂ = some _ _ (nonsingular_add h₁ h₂ fun hxy => hy hxy.right) :=
  add_some fun hxy => hy hxy.right

/--
lemma `add_of_Y_ne'` / 引理 `add_of_Y_ne'`

English:
lemma add_of_Y_ne'
  statement: {x₁ x₂ y₁ y₂ : F} {h₁ : W.Nonsingular x₁ y₁} {h₂ : W.Nonsingular x₂ y₂}
  proof: add_of_Y_ne hy

中文:
引理 add_of_Y_ne'
  结论: {x₁ x₂ y₁ y₂ : F} {h₁ : W.Nonsingular x₁ y₁} {h₂ : W.Nonsingular x₂ y₂}
  证明: add_of_Y_ne hy

Depends on / 依赖: add_of_Y_ne
-/
lemma add_of_Y_ne' {x₁ x₂ y₁ y₂ : F} {h₁ : W.Nonsingular x₁ y₁} {h₂ : W.Nonsingular x₂ y₂}
    (hy : y₁ != W.negY x₂ y₂) :
    some _ _ h₁ + some _ _ h₂ = -some _ _ (nonsingular_negAdd h₁ h₂ fun hxy => hy hxy.right) :=
  add_of_Y_ne hy

-- @[simp] -- Not a good simp lemma, since `hy` is not in simp normal form.
/--
lemma `add_self_of_Y_ne` / 引理 `add_self_of_Y_ne`

English:
lemma add_self_of_Y_ne
  given: {x₁ y₁ : F} {h₁ : W.Nonsingular x₁ y₁} (hy : y₁ != W.negY x₁ y₁)
  proof: add_of_Y_ne hy

中文:
引理 add_self_of_Y_ne
  条件: {x₁ y₁ : F} {h₁ : W.Nonsingular x₁ y₁} (hy : y₁ != W.negY x₁ y₁)
  证明: add_of_Y_ne hy

Depends on / 依赖: add_of_Y_ne
-/
lemma add_self_of_Y_ne {x₁ y₁ : F} {h₁ : W.Nonsingular x₁ y₁} (hy : y₁ != W.negY x₁ y₁) :
    some _ _ h₁ + some _ _ h₁ = some _ _ (nonsingular_add h₁ h₁ fun hxy => hy hxy.right) :=
  add_of_Y_ne hy

/--
lemma `add_self_of_Y_ne'` / 引理 `add_self_of_Y_ne'`

English:
lemma add_self_of_Y_ne'
  given: {x₁ y₁ : F} {h₁ : W.Nonsingular x₁ y₁} (hy : y₁ != W.negY x₁ y₁)
  proof: add_of_Y_ne hy

@[simp]

中文:
引理 add_self_of_Y_ne'
  条件: {x₁ y₁ : F} {h₁ : W.Nonsingular x₁ y₁} (hy : y₁ != W.negY x₁ y₁)
  证明: add_of_Y_ne hy

@[simp]

Depends on / 依赖: add_of_Y_ne
-/
lemma add_self_of_Y_ne' {x₁ y₁ : F} {h₁ : W.Nonsingular x₁ y₁} (hy : y₁ != W.negY x₁ y₁) :
    some _ _ h₁ + some _ _ h₁ = -some _ _ (nonsingular_negAdd h₁ h₁ fun hxy => hy hxy.right) :=
  add_of_Y_ne hy

@[simp]
/--
lemma `add_of_X_ne` / 引理 `add_of_X_ne`

English:
lemma add_of_X_ne
  statement: {x₁ x₂ y₁ y₂ : F} {h₁ : W.Nonsingular x₁ y₁} {h₂ : W.Nonsingular x₂ y₂}
  proof: add_some fun hxy => hx hxy.left

中文:
引理 add_of_X_ne
  结论: {x₁ x₂ y₁ y₂ : F} {h₁ : W.Nonsingular x₁ y₁} {h₂ : W.Nonsingular x₂ y₂}
  证明: add_some fun hxy => hx hxy.left

Depends on / 依赖: add_some, hxy.left
-/
lemma add_of_X_ne {x₁ x₂ y₁ y₂ : F} {h₁ : W.Nonsingular x₁ y₁} {h₂ : W.Nonsingular x₂ y₂}
    (hx : x₁ != x₂) :
    some _ _ h₁ + some _ _ h₂ = some _ _ (nonsingular_add h₁ h₂ fun hxy => hx hxy.left) :=
  add_some fun hxy => hx hxy.left

/--
lemma `add_of_X_ne'` / 引理 `add_of_X_ne'`

English:
lemma add_of_X_ne'
  statement: {x₁ x₂ y₁ y₂ : F} {h₁ : W.Nonsingular x₁ y₁} {h₂ : W.Nonsingular x₂ y₂}
  proof: add_of_X_ne hx

中文:
引理 add_of_X_ne'
  结论: {x₁ x₂ y₁ y₂ : F} {h₁ : W.Nonsingular x₁ y₁} {h₂ : W.Nonsingular x₂ y₂}
  证明: add_of_X_ne hx

Depends on / 依赖: add_of_X_ne
-/
lemma add_of_X_ne' {x₁ x₂ y₁ y₂ : F} {h₁ : W.Nonsingular x₁ y₁} {h₂ : W.Nonsingular x₂ y₂}
    (hx : x₁ != x₂) :
    some _ _ h₁ + some _ _ h₂ = -some _ _ (nonsingular_negAdd h₁ h₂ fun hxy => hx hxy.left) :=
  add_of_X_ne hx

set_option backward.isDefEq.respectTransparency.types false in
/-- The group homomorphism mapping a nonsingular affine point `(x, y)` of a Weierstrass curve `W` to
the class of the non-zero fractional ideal `⟨X - x, Y - y⟩` in the ideal class group of `F[W]`. -/
@[simps]
/--
Definition of `toClass` / `toClass` 的定义

English:
definition toClass
  signature: : W.Point ->+ Additive (ClassGroup W.CoordinateRing) where
  body: match P with
    | 0 => 0
| some _ _ h => ClassGroup.mk W.FunctionField CoordinateRing.XYIdeal' h
  map_zero' := rfl
  map_add' := by
    rintro (_ | ⟨x₁, y₁, h₁⟩) (_ | ⟨x₂, y₂, h₂⟩)
    any_goals simp only [← zero_def, zero_add, add_zero]
    by_cases hxy : x₁ = x₂ ∧ y₁ = W.negY x₂ y₂
    · simp on

中文:
定义 toClass
  签名: : W.Point ->+ Additive (ClassGroup W.CoordinateRing) where
  定义体: match P with
    | 0 => 0
| some _ _ h => ClassGroup.mk W.FunctionField CoordinateRing.XYIdeal' h
  map_zero' := rfl
  map_add' := by
    rintro (_ | ⟨x₁, y₁, h₁⟩) (_ | ⟨x₂, y₂, h₂⟩)
    any_goals simp only [← zero_def, zero_add, add_zero]
    by_cases hxy : x₁ = x₂ ∧ y₁ = W.negY x₂ y₂
    · simp on
-/
noncomputable def toClass : W.Point ->+ Additive (ClassGroup W.CoordinateRing) where
  toFun P := match P with
    | 0 => 0
| some _ _ h => ClassGroup.mk W.FunctionField CoordinateRing.XYIdeal' h
  map_zero' := rfl
  map_add' := by
    rintro (_ | ⟨x₁, y₁, h₁⟩) (_ | ⟨x₂, y₂, h₂⟩)
    any_goals simp only [← zero_def, zero_add, add_zero]
    by_cases hxy : x₁ = x₂ ∧ y₁ = W.negY x₂ y₂
    · simp only [hxy.left, hxy.right, add_of_Y_eq rfl rfl]
      exact (CoordinateRing.mk_XYIdeal'_neg_mul h₂).symm
    · simp only [add_some hxy]
      exact (CoordinateRing.mk_XYIdeal'_mul_mk_XYIdeal' h₁ h₂ hxy).symm

/--
lemma `toClass_zero` / 引理 `toClass_zero`

English:
lemma toClass_zero
  statement: toClass (0 : W.Point) = 0
  proof: rfl

中文:
引理 toClass_zero
  结论: toClass (0 : W.Point) = 0
  证明: rfl
-/
lemma toClass_zero : toClass (0 : W.Point) = 0 :=
  rfl

-- note: giving `W` to `XYIdeal'` explicitly hugely speeds up elaboration for some reason.
-- see https://leanprover.zulipchat.com/#narrow/channel/287929-mathlib4/topic/Field.20.28FunctionField.20.3Fm.2E19.29/near/594011283
/--
lemma `toClass_some` / 引理 `toClass_some`

English:
lemma toClass_some
  given: {x y : F} (h : W.Nonsingular x y)
  proof: rfl

中文:
引理 toClass_some
  条件: {x y : F} (h : W.Nonsingular x y)
  证明: rfl
-/
lemma toClass_some {x y : F} (h : W.Nonsingular x y) :
    toClass (some _ _ h) = ClassGroup.mk W.FunctionField (CoordinateRing.XYIdeal' (W := W) h) :=
  rfl

/--
lemma `add_eq_zero` / 引理 `add_eq_zero`

English:
lemma add_eq_zero
  given: (P Q : W.Point)
  statement: P + Q = 0 ↔ P = -Q
  proof: by
  rcases P, Q with ⟨_ | ⟨x₁, y₁, _⟩, _ | ⟨x₂, y₂, _⟩⟩
  any_goals rfl
  · rw [← zero_def, zero_add, eq_comm (a := 0), neg_eq_iff_eq_neg, neg_zero]
  · rw [neg_some, some.injEq]
    constructor
    · contrapose
      exact fun hxy => by simpa only [add_some hxy] using some_ne_zero _
    · exact fu

中文:
引理 add_eq_zero
  条件: (P Q : W.Point)
  结论: P + Q = 0 ↔ P = -Q
  证明: by
  rcases P, Q with ⟨_ | ⟨x₁, y₁, _⟩, _ | ⟨x₂, y₂, _⟩⟩
  any_goals rfl
  · rw [← zero_def, zero_add, eq_comm (a := 0), neg_eq_iff_eq_neg, neg_zero]
  · rw [neg_some, some.injEq]
    constructor
    · contrapose
      exact fun hxy => by simpa only [add_some hxy] using some_ne_zero _
    · exact fu
-/
private lemma add_eq_zero (P Q : W.Point) : P + Q = 0 ↔ P = -Q := by
  rcases P, Q with ⟨_ | ⟨x₁, y₁, _⟩, _ | ⟨x₂, y₂, _⟩⟩
  any_goals rfl
  · rw [← zero_def, zero_add, eq_comm (a := 0), neg_eq_iff_eq_neg, neg_zero]
  · rw [neg_some, some.injEq]
    constructor
    · contrapose
      exact fun hxy => by simpa only [add_some hxy] using some_ne_zero _
    · exact fun ⟨hx, hy⟩ => add_of_Y_eq hx hy

/--
lemma `toClass_eq_zero` / 引理 `toClass_eq_zero`

English:
lemma toClass_eq_zero
  given: (P : W.Point)
  statement: toClass P = 0 ↔ P = 0
  proof: by
  constructor
  · intro hP
    rcases P with (_ | ⟨_, _, h, _⟩)
    · rfl
    · rcases (ClassGroup.mk_eq_one_of_coe_ideal <| by rfl).mp hP with ⟨p, h0, hp⟩
      apply (p.natDegree_norm_ne_one _).elim
      rw [← finrank_quotient_span_eq_natDegree_norm (CoordinateRing.basis W) h0]; rw [← (quotien

中文:
引理 toClass_eq_zero
  条件: (P : W.Point)
  结论: toClass P = 0 ↔ P = 0
  证明: by
  constructor
  · intro hP
    rcases P with (_ | ⟨_, _, h, _⟩)
    · rfl
    · rcases (ClassGroup.mk_eq_one_of_coe_ideal <| by rfl).mp hP with ⟨p, h0, hp⟩
      apply (p.natDegree_norm_ne_one _).elim
      rw [← finrank_quotient_span_eq_natDegree_norm (CoordinateRing.basis W) h0]; rw [← (quotien

Depends on / 依赖: ClassGroup, ClassGroup.mk_eq_one_of_coe_ideal, CoordinateRing, CoordinateRing.basis, CoordinateRing.quotientXYIdealEquiv, Module, Module.finrank_self, congr_arg, finrank_eq, finrank_quotient_span_eq_natDegree_norm, finrank_self, mk_eq_one_of_coe_ideal, natDegree_norm_ne_one, p.natDegree_norm_ne_one, quotientEquivAlgOfEq, quotientXYIdealEquiv, toClass, toLinearEquiv, toLinearEquiv.finrank_eq
-/
lemma toClass_eq_zero (P : W.Point) : toClass P = 0 ↔ P = 0 := by
  constructor
  · intro hP
    rcases P with (_ | ⟨_, _, h, _⟩)
    · rfl
    · rcases (ClassGroup.mk_eq_one_of_coe_ideal <| by rfl).mp hP with ⟨p, h0, hp⟩
      apply (p.natDegree_norm_ne_one _).elim
      rw [← finrank_quotient_span_eq_natDegree_norm (CoordinateRing.basis W) h0]; rw [← (quotientEquivAlgOfEq F hp).toLinearEquiv.finrank_eq]; rw [(CoordinateRing.quotientXYIdealEquiv h).toLinearEquiv.finrank_eq]; rw [Module.finrank_self]
  · exact congr_arg toClass

/--
lemma `toClass_injective` / 引理 `toClass_injective`

English:
lemma toClass_injective
  statement: Function.Injective toClass (W := W)
  proof: by
  rintro (_ | ⟨_, _, h⟩) _ hP
  all_goals rw [← neg_inj, ← add_eq_zero, ← toClass_eq_zero, map_add, ← hP]
  · exact zero_add 0
  · exact CoordinateRing.mk_XYIdeal'_neg_mul h

中文:
引理 toClass_injective
  结论: Function.Injective toClass (W := W)
  证明: by
  rintro (_ | ⟨_, _, h⟩) _ hP
  all_goals rw [← neg_inj, ← add_eq_zero, ← toClass_eq_zero, map_add, ← hP]
  · exact zero_add 0
  · exact CoordinateRing.mk_XYIdeal'_neg_mul h

Depends on / 依赖: CoordinateRing, CoordinateRing.mk_XYIdeal, _neg_mul, add_eq_zero, all_goals, map_add, mk_XYIdeal, neg_inj, toClass_eq_zero, zero_add
-/
lemma toClass_injective : Function.Injective toClass (W := W) := by
  rintro (_ | ⟨_, _, h⟩) _ hP
  all_goals rw [← neg_inj, ← add_eq_zero, ← toClass_eq_zero, map_add, ← hP]
  · exact zero_add 0
  · exact CoordinateRing.mk_XYIdeal'_neg_mul h

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: AddCommSemigroup W.Point
  body: toClass_injective by simp only [map_add, add_comm]
add_assoc _ _ _ := toClass_injective by simp only [map_add, add_assoc]

中文:
实例 :
  签名: AddCommSemigroup W.Point
  定义体: toClass_injective by simp only [map_add, add_comm]
add_assoc _ _ _ := toClass_injective by simp only [map_add, add_assoc]

Depends on / 依赖: add_comm, map_add, toClass_injective
-/
instance : AddCommSemigroup W.Point where
add_comm _ _ := toClass_injective by simp only [map_add, add_comm]
add_assoc _ _ _ := toClass_injective by simp only [map_add, add_assoc]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: AddCommGroup W.Point
  body: nsmulBinRec
  nsmul_succ := nsmulBinRec_succ
  zsmul := zsmulRec nsmulBinRec
  zsmul_succ' := nsmulBinRec_succ
  zero_add := zero_add
  add_zero := add_zero
  neg_add_cancel _ := by rw [add_eq_zero]

中文:
实例 :
  签名: AddCommGroup W.Point
  定义体: nsmulBinRec
  nsmul_succ := nsmulBinRec_succ
  zsmul := zsmulRec nsmulBinRec
  zsmul_succ' := nsmulBinRec_succ
  zero_add := zero_add
  add_zero := add_zero
  neg_add_cancel _ := by rw [add_eq_zero]

Depends on / 依赖: nsmulBinRec
-/
instance : AddCommGroup W.Point where
  nsmul := nsmulBinRec
  nsmul_succ := nsmulBinRec_succ
  zsmul := zsmulRec nsmulBinRec
  zsmul_succ' := nsmulBinRec_succ
  zero_add := zero_add
  add_zero := add_zero
  neg_add_cancel _ := by rw [add_eq_zero]

/-! ## Maps and base changes -/

variable [Algebra R S] [Algebra R F] [Algebra S F] [IsScalarTower R S F] [Algebra R K] [Algebra S K]
  [IsScalarTower R S K] [Algebra R L] [Algebra S L] [IsScalarTower R S L] (f : F ->ₐ[S] K)
  (g : K ->ₐ[S] L)

/--
Definition of `map` / `map` 的定义

English:
definition map
  signature: : (W'⁄F).Point ->+ (W'⁄K).Point where
  body: match P with
    | 0 => 0
| some _ _ h => some _ _ (W'.baseChange_nonsingular f.injective ..).mpr h
  map_zero' := rfl
  map_add' := by
    rintro (_ | ⟨x₁, y₁, h₁⟩) (_ | ⟨x₂, y₂, h₂⟩)
    any_goals rfl
    by_cases hxy : x₁ = x₂ ∧ y₁ = (W'⁄F).negY x₂ y₂
    · rw [add_of_Y_eq hxy.left hxy.right,
add

中文:
定义 map
  签名: : (W'⁄F).Point ->+ (W'⁄K).Point where
  定义体: match P with
    | 0 => 0
| some _ _ h => some _ _ (W'.baseChange_nonsingular f.injective ..).mpr h
  map_zero' := rfl
  map_add' := by
    rintro (_ | ⟨x₁, y₁, h₁⟩) (_ | ⟨x₂, y₂, h₂⟩)
    any_goals rfl
    by_cases hxy : x₁ = x₂ ∧ y₁ = (W'⁄F).negY x₂ y₂
    · rw [add_of_Y_eq hxy.left hxy.right,
add
-/
noncomputable def map : (W'⁄F).Point ->+ (W'⁄K).Point where
  toFun P := match P with
    | 0 => 0
| some _ _ h => some _ _ (W'.baseChange_nonsingular f.injective ..).mpr h
  map_zero' := rfl
  map_add' := by
    rintro (_ | ⟨x₁, y₁, h₁⟩) (_ | ⟨x₂, y₂, h₂⟩)
    any_goals rfl
    by_cases hxy : x₁ = x₂ ∧ y₁ = (W'⁄F).negY x₂ y₂
    · rw [add_of_Y_eq hxy.left hxy.right,
add_of_Y_eq (congr_arg _ hxy.left) by rw [hxy.right, baseChange_negY]]
    · simpa only [add_some hxy, ← baseChange_addX, ← baseChange_addY, ← baseChange_slope] using!
        (add_some fun h => hxy ⟨f.injective h.1, f.injective (W'.baseChange_negY f .. ▸ h).2⟩).symm

/--
lemma `map_zero` / 引理 `map_zero`

English:
lemma map_zero
  statement: map f (0 : (W'⁄F).Point) = 0
  proof: rfl

中文:
引理 map_zero
  结论: map f (0 : (W'⁄F).Point) = 0
  证明: rfl
-/
lemma map_zero : map f (0 : (W'⁄F).Point) = 0 :=
  rfl

/--
lemma `map_some` / 引理 `map_some`

English:
lemma map_some
  given: {x y : F} (h : (W'⁄F).Nonsingular x y)
  proof: rfl

中文:
引理 map_some
  条件: {x y : F} (h : (W'⁄F).Nonsingular x y)
  证明: rfl
-/
lemma map_some {x y : F} (h : (W'⁄F).Nonsingular x y) :
    map f (some _ _ h) = some _ _ ((W'.baseChange_nonsingular f.injective ..).mpr h) :=
  rfl

/--
lemma `map_id` / 引理 `map_id`

English:
lemma map_id
  given: (P : (W'⁄F).Point)
  statement: map (Algebra.ofId F F) P = P
  proof: by
  cases P <;> rfl

中文:
引理 map_id
  条件: (P : (W'⁄F).Point)
  结论: map (Algebra.ofId F F) P = P
  证明: by
  cases P <;> rfl
-/
lemma map_id (P : (W'⁄F).Point) : map (Algebra.ofId F F) P = P := by
  cases P <;> rfl

/--
lemma `map_map` / 引理 `map_map`

English:
lemma map_map
  given: (P : (W'⁄F).Point)
  statement: map g (map f P) = map (g.comp f) P
  proof: by
  cases P <;> rfl

中文:
引理 map_map
  条件: (P : (W'⁄F).Point)
  结论: map g (map f P) = map (g.comp f) P
  证明: by
  cases P <;> rfl
-/
lemma map_map (P : (W'⁄F).Point) : map g (map f P) = map (g.comp f) P := by
  cases P <;> rfl

/--
lemma `map_injective` / 引理 `map_injective`

English:
lemma map_injective
  statement: Function.Injective map (W' := W') f
  proof: by
  rintro (_ | _) (_ | _) h
  any_goals contradiction
  · rfl
  · simpa only [some.injEq] using ⟨f.injective (some.inj h).left, f.injective (some.inj h).right⟩

中文:
引理 map_injective
  结论: Function.Injective map (W' := W') f
  证明: by
  rintro (_ | _) (_ | _) h
  any_goals contradiction
  · rfl
  · simpa only [some.injEq] using ⟨f.injective (some.inj h).left, f.injective (some.inj h).right⟩

Depends on / 依赖: any_goals, f.injective, injective, some.inj, some.injEq
-/
lemma map_injective : Function.Injective map (W' := W') f := by
  rintro (_ | _) (_ | _) h
  any_goals contradiction
  · rfl
  · simpa only [some.injEq] using ⟨f.injective (some.inj h).left, f.injective (some.inj h).right⟩

variable (F K) in
/--
Definition of `baseChange` / `baseChange` 的定义

English:
abbreviation baseChange
  signature: [Algebra F K] [IsScalarTower R F K]
  body: map Algebra.ofId F K

中文:
缩写 baseChange
  签名: [Algebra F K] [IsScalarTower R F K]
  定义体: map Algebra.ofId F K

Depends on / 依赖: Algebra, Algebra.ofId
-/
noncomputable abbrev baseChange [Algebra F K] [IsScalarTower R F K] :
    (W'⁄F).Point ->+ (W'⁄K).Point :=
map Algebra.ofId F K

/--
lemma `map_baseChange` / 引理 `map_baseChange`

English:
lemma map_baseChange
  statement: [Algebra F K] [IsScalarTower R F K] [Algebra F L] [IsScalarTower R F L]
  proof: by
  have : Subsingleton (F ->ₐ[F] L) := inferInstance
  convert! map_map (Algebra.ofId F K) f P

中文:
引理 map_baseChange
  结论: [Algebra F K] [IsScalarTower R F K] [Algebra F L] [IsScalarTower R F L]
  证明: by
  have : Subsingleton (F ->ₐ[F] L) := inferInstance
  convert! map_map (Algebra.ofId F K) f P

Depends on / 依赖: Algebra, Algebra.ofId, Subsingleton, convert, map_map
-/
lemma map_baseChange [Algebra F K] [IsScalarTower R F K] [Algebra F L] [IsScalarTower R F L]
    (f : K ->ₐ[F] L) (P : (W'⁄F).Point) : map f (baseChange F K P) = baseChange F L P := by
  have : Subsingleton (F ->ₐ[F] L) := inferInstance
  convert! map_map (Algebra.ofId F K) f P

end Point

/-!
### The x-coordinate map to ℙ¹

We define the map from points on an affine Weierstrass curve over `R` to the projective line
by producing a coordinate vector in `Fin 2 → R` that represents the projective point.
-/

namespace Point

/--
Definition of `xRep` / `xRep` 的定义

English:
definition xRep
  signature: : W'.Point -> Fin 2 -> R

中文:
定义 xRep
  签名: : W'.Point -> Fin 2 -> R
-/
noncomputable def xRep : W'.Point -> Fin 2 -> R
  | 0 => ![1, 0]
  | some x _ _ => ![x, 1]

@[simp]
/--
lemma `xRep_zero` / 引理 `xRep_zero`

English:
lemma xRep_zero
  statement: (0 : W'.Point).xRep = ![1, 0]
  proof: rfl

@[simp]

中文:
引理 xRep_zero
  结论: (0 : W'.Point).xRep = ![1, 0]
  证明: rfl

@[simp]
-/
lemma xRep_zero : (0 : W'.Point).xRep = ![1, 0] :=
  rfl

@[simp]
/--
lemma `xRep_some` / 引理 `xRep_some`

English:
lemma xRep_some
  given: {x y : R} (h : W'.Nonsingular x y)
  statement: (some x y h).xRep = ![x, 1]
  proof: rfl

中文:
引理 xRep_some
  条件: {x y : R} (h : W'.Nonsingular x y)
  结论: (some x y h).xRep = ![x, 1]
  证明: rfl
-/
lemma xRep_some {x y : R} (h : W'.Nonsingular x y) : (some x y h).xRep = ![x, 1] :=
  rfl

/--
lemma `xRep_ne_zero` / 引理 `xRep_ne_zero`

English:
lemma xRep_ne_zero
  given: [Nontrivial R] (P : W'.Point)
  statement: P.xRep != 0
  proof: by
  cases P <;> simp [xRep]

@[simp]

中文:
引理 xRep_ne_zero
  条件: [Nontrivial R] (P : W'.Point)
  结论: P.xRep != 0
  证明: by
  cases P <;> simp [xRep]

@[simp]
-/
lemma xRep_ne_zero [Nontrivial R] (P : W'.Point) : P.xRep != 0 := by
  cases P <;> simp [xRep]

@[simp]
/--
lemma `xRep_neg` / 引理 `xRep_neg`

English:
lemma xRep_neg
  given: (P : W'.Point)
  statement: (-P).xRep = P.xRep
  proof: by
  cases P <;> simp [← zero_def]

中文:
引理 xRep_neg
  条件: (P : W'.Point)
  结论: (-P).xRep = P.xRep
  证明: by
  cases P <;> simp [← zero_def]

Depends on / 依赖: zero_def
-/
lemma xRep_neg (P : W'.Point) : (-P).xRep = P.xRep := by
  cases P <;> simp [← zero_def]

-- The following lemmas need a field as base ring.

/--
lemma `eq_or_eq_neg_of_xRep_eq_xRep` / 引理 `eq_or_eq_neg_of_xRep_eq_xRep`

English:
lemma eq_or_eq_neg_of_xRep_eq_xRep
  given: {P Q : W.Point} (h : P.xRep = Q.xRep)
  statement: P = Q ∨ P = -Q
  proof: by
  match P, Q with
  | 0, 0 => exact .inl rfl
  | 0, some .. => simp [xRep] at h
  | some .., 0 => simp [xRep] at h
  | some x₁ .., some x₂ .. =>
    simp only [xRep, Matrix.vecCons_inj, and_true] at h
    exact X_eq_iff.mp h

中文:
引理 eq_or_eq_neg_of_xRep_eq_xRep
  条件: {P Q : W.Point} (h : P.xRep = Q.xRep)
  结论: P = Q ∨ P = -Q
  证明: by
  match P, Q with
  | 0, 0 => exact .inl rfl
  | 0, some .. => simp [xRep] at h
  | some .., 0 => simp [xRep] at h
  | some x₁ .., some x₂ .. =>
    simp only [xRep, Matrix.vecCons_inj, and_true] at h
    exact X_eq_iff.mp h

Depends on / 依赖: Matrix, Matrix.vecCons_inj, X_eq_iff, X_eq_iff.mp, and_true, vecCons_inj
-/
lemma eq_or_eq_neg_of_xRep_eq_xRep {P Q : W.Point} (h : P.xRep = Q.xRep) : P = Q ∨ P = -Q := by
  match P, Q with
  | 0, 0 => exact .inl rfl
  | 0, some .. => simp [xRep] at h
  | some .., 0 => simp [xRep] at h
  | some x₁ .., some x₂ .. =>
    simp only [xRep, Matrix.vecCons_inj, and_true] at h
    exact X_eq_iff.mp h

/--
lemma `xRep_eq_xRep_iff` / 引理 `xRep_eq_xRep_iff`

English:
lemma xRep_eq_xRep_iff
  given: {P Q : W.Point}
  statement: P.xRep = Q.xRep ↔ P = Q ∨ P = -Q
  proof: by
  refine ⟨eq_or_eq_neg_of_xRep_eq_xRep, fun H => ?_⟩
  rcases H with rfl | rfl <;> simp

中文:
引理 xRep_eq_xRep_iff
  条件: {P Q : W.Point}
  结论: P.xRep = Q.xRep ↔ P = Q ∨ P = -Q
  证明: by
  refine ⟨eq_or_eq_neg_of_xRep_eq_xRep, fun H => ?_⟩
  rcases H with rfl | rfl <;> simp

Depends on / 依赖: eq_or_eq_neg_of_xRep_eq_xRep
-/
lemma xRep_eq_xRep_iff {P Q : W.Point} : P.xRep = Q.xRep ↔ P = Q ∨ P = -Q := by
  refine ⟨eq_or_eq_neg_of_xRep_eq_xRep, fun H => ?_⟩
  rcases H with rfl | rfl <;> simp

end Point

end Affine

end WeierstrassCurve
