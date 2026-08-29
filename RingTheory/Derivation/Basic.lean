/-
Copyright (c) 2020 Nicolò Cavalleri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nicolò Cavalleri, Andrew Yang
-/
module

public import Mathlib.Algebra.Polynomial.AlgebraMap
public import Mathlib.Algebra.Polynomial.Derivative

/-!
# Derivations

This file defines derivation. A derivation `D` from the `R`-algebra `A` to the `A`-module `M` is an
`R`-linear map that satisfy the Leibniz rule `D (a * b) = a * D b + D a * b`.

## Main results

- `Derivation`: The type of `R`-derivations from `A` to `M`. This has an `A`-module structure.
- `Derivation.llcomp`: We may compose linear maps and derivations to obtain a derivation,
  and the composition is bilinear.

See `Mathlib/RingTheory/Derivation/Lie.lean` for
- `Derivation.instLieAlgebra`: The `R`-derivations from `A` to `A` form a Lie algebra over `R`.

and `Mathlib/RingTheory/Derivation/ToSquareZero.lean` for
- `derivationToSquareZeroEquivLift`: The `R`-derivations from `A` into a square-zero ideal `I`
  of `B` corresponds to the lifts `A →ₐ[R] B` of the map `A →ₐ[R] B ⧸ I`.

## Future project

- Generalize derivations into bimodules.

-/

@[expose] public section

open Algebra

/--
Definition of `Derivation` / `Derivation` 的定义

English:
structure Derivation
  parameters: (R : Type*) (A : Type*) (M : Type*)
  extends: A ->ₗ[R] M
  axioms and operations (2):
    - map_one_eq_zero' : toLinearMap 1 = 0
    - leibniz'((a b : A)) : toLinearMap (a * b) = a • toLinearMap b + b • toLinearMap a

中文:
结构 导子
  参数: (R : 类型) (A : 类型) (M : 类型)
  继承: A ->ₗ[R] M
  公理与运算 (2 个):
    - map_one_eq_zero' : toLinearMap 1 = 0
    - leibniz'((a b : A)) : toLinearMap (a * b) = a • toLinearMap b + b • toLinearMap a
-/
structure Derivation (R : Type*) (A : Type*) (M : Type*)
    [CommSemiring R] [CommSemiring A] [AddCommMonoid M] [Algebra R A] [Module A M] [Module R M]
    extends A ->ₗ[R] M where
  protected map_one_eq_zero' : toLinearMap 1 = 0
  protected leibniz' (a b : A) : toLinearMap (a * b) = a • toLinearMap b + b • toLinearMap a

/-- The `LinearMap` underlying a `Derivation`. -/
add_decl_doc Derivation.toLinearMap

namespace Derivation

section

variable {R : Type*} {A : Type*} {B : Type*} {M : Type*}
variable [CommSemiring R] [CommSemiring A] [CommSemiring B] [AddCommMonoid M]
variable [Algebra R A] [Algebra R B]
variable [Module A M] [Module B M] [Module R M]


variable (D : Derivation R A M) {D1 D2 : Derivation R A M} (r : R) (a b : A)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: FunLike (Derivation R A M) A M
  body: D.toFun
  coe_injective D1 D2 h := by cases D1; cases D2; congr; exact DFunLike.coe_injective h

中文:
实例 :
  签名: 函数状 (导子 R A M) A M
  定义体: D.toFun
  coe_injective D1 D2 h := by cases D1; cases D2; congr; exact DFunLike.coe_injective h

Depends on / 依赖: D.toFun
-/
instance : FunLike (Derivation R A M) A M where
  coe D := D.toFun
  coe_injective D1 D2 h := by cases D1; cases D2; congr; exact DFunLike.coe_injective h

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: AddMonoidHomClass (Derivation R A M) A M
  body: D.toLinearMap.map_add'
  map_zero D := D.toLinearMap.map_zero

中文:
实例 :
  签名: 加法幺半群态射类 (导子 R A M) A M
  定义体: D.toLinearMap.map_add'
  map_zero D := D.toLinearMap.map_zero

Depends on / 依赖: D.toLinearMap.map_add, map_add, toLinearMap
-/
instance : AddMonoidHomClass (Derivation R A M) A M where
  map_add D := D.toLinearMap.map_add'
  map_zero D := D.toLinearMap.map_zero

-- Not a simp lemma because it can be proved via `coeFn_coe` + `toLinearMap_eq_coe`
/--
theorem `toFun_eq_coe` / 定理 `toFun_eq_coe`

English:
theorem toFun_eq_coe
  statement: D.toFun = ⇑D
  proof: rfl

中文:
定理 toFun_eq_coe
  结论: D.toFun = ⇑D
  证明: rfl
-/
theorem toFun_eq_coe : D.toFun = ⇑D :=
  rfl

/--
Definition of `Simps.apply` / `Simps.apply` 的定义

English:
definition Simps.apply
  signature: (D : Derivation R A M)
  body: D

initialize_simps_projections Derivation (toFun -> apply)

中文:
定义 Simps.apply
  签名: (D : 导子 R A M)
  定义体: D

initialize_simps_projections Derivation (toFun -> apply)
-/
def Simps.apply (D : Derivation R A M) : A -> M := D

initialize_simps_projections Derivation (toFun -> apply)

attribute [coe] toLinearMap

/--
Instance `hasCoeToLinearMap` / 实例 `hasCoeToLinearMap`

English:
instance hasCoeToLinearMap
  signature: : Coe (Derivation R A M) (A ->ₗ[R] M)
  body: ⟨fun D => D.toLinearMap⟩

@[simp]

中文:
实例 hasCoeToLinearMap
  签名: : Coe (导子 R A M) (A ->ₗ[R] M)
  定义体: ⟨fun D => D.toLinearMap⟩

@[simp]

Depends on / 依赖: D.toLinearMap, toLinearMap
-/
instance hasCoeToLinearMap : Coe (Derivation R A M) (A ->ₗ[R] M) :=
  ⟨fun D => D.toLinearMap⟩

@[simp]
/--
theorem `mk_coe` / 定理 `mk_coe`

English:
theorem mk_coe
  given: (f : A ->ₗ[R] M) (h₁ h₂)
  statement: ((⟨f, h₁, h₂⟩ : Derivation R A M) : A -> M) = f
  proof: rfl

@[simp, norm_cast]

中文:
定理 mk_coe
  条件: (f : A ->ₗ[R] M) (h₁ h₂)
  结论: ((⟨f, h₁, h₂⟩ : 导子 R A M) : A -> M) = f
  证明: rfl

@[simp, norm_cast]
-/
theorem mk_coe (f : A ->ₗ[R] M) (h₁ h₂) : ((⟨f, h₁, h₂⟩ : Derivation R A M) : A -> M) = f :=
  rfl

@[simp, norm_cast]
/--
theorem `coeFn_coe` / 定理 `coeFn_coe`

English:
theorem coeFn_coe
  given: (f : Derivation R A M)
  statement: ⇑(f : A ->ₗ[R] M) = f
  proof: rfl

中文:
定理 coeFn_coe
  条件: (f : 导子 R A M)
  结论: ⇑(f : A ->ₗ[R] M) = f
  证明: rfl
-/
theorem coeFn_coe (f : Derivation R A M) : ⇑(f : A ->ₗ[R] M) = f :=
  rfl

/--
theorem `coe_injective` / 定理 `coe_injective`

English:
theorem coe_injective
  statement: @Function.Injective (Derivation R A M) (A -> M) DFunLike.coe
  proof: DFunLike.coe_injective

@[ext]

中文:
定理 coe_injective
  结论: @函数.单射 (导子 R A M) (A -> M) 依赖函数状.coe
  证明: DFunLike.coe_injective

@[ext]

Depends on / 依赖: DFunLike, DFunLike.coe_injective, coe_injective
-/
theorem coe_injective : @Function.Injective (Derivation R A M) (A -> M) DFunLike.coe :=
  DFunLike.coe_injective

@[ext]
/--
theorem `ext` / 定理 `ext`

English:
theorem ext
  given: (H : forall a, D1 a = D2 a)
  statement: D1 = D2
  proof: DFunLike.ext _ _ H

中文:
定理 ext
  条件: (H : 对任意 a, D1 a = D2 a)
  结论: D1 = D2
  证明: DFunLike.ext _ _ H

Depends on / 依赖: DFunLike, DFunLike.ext
-/
theorem ext (H : forall a, D1 a = D2 a) : D1 = D2 :=
  DFunLike.ext _ _ H

/--
theorem `congr_fun` / 定理 `congr_fun`

English:
theorem congr_fun
  given: (h : D1 = D2) (a : A)
  statement: D1 a = D2 a
  proof: DFunLike.congr_fun h a

中文:
定理 congr_fun
  条件: (h : D1 = D2) (a : A)
  结论: D1 a = D2 a
  证明: DFunLike.congr_fun h a

Depends on / 依赖: DFunLike, DFunLike.congr_fun, congr_fun
-/
theorem congr_fun (h : D1 = D2) (a : A) : D1 a = D2 a :=
  DFunLike.congr_fun h a

/--
theorem `map_add` / 定理 `map_add`

English:
theorem map_add
  statement: D (a + b) = D a + D b
  proof: map_add D a b

中文:
定理 map_add
  结论: D (a + b) = D a + D b
  证明: map_add D a b
-/
protected theorem map_add : D (a + b) = D a + D b :=
  map_add D a b

/--
theorem `map_zero` / 定理 `map_zero`

English:
theorem map_zero
  statement: D 0 = 0
  proof: map_zero D

@[simp]

中文:
定理 map_zero
  结论: D 0 = 0
  证明: map_zero D

@[simp]
-/
protected theorem map_zero : D 0 = 0 :=
  map_zero D

@[simp]
/--
theorem `map_smul` / 定理 `map_smul`

English:
theorem map_smul
  statement: D (r • a) = r • D a
  proof: D.toLinearMap.map_smul r a

@[simp]

中文:
定理 map_smul
  结论: D (r • a) = r • D a
  证明: D.toLinearMap.map_smul r a

@[simp]

Depends on / 依赖: D.toLinearMap.map_smul, map_smul, toLinearMap
-/
theorem map_smul : D (r • a) = r • D a :=
  D.toLinearMap.map_smul r a

@[simp]
/--
theorem `leibniz` / 定理 `leibniz`

English:
theorem leibniz
  statement: D (a * b) = a • D b + b • D a
  proof: D.leibniz' _ _

@[simp]

中文:
定理 leibniz
  结论: D (a * b) = a • D b + b • D a
  证明: D.leibniz' _ _

@[simp]

Depends on / 依赖: D.leibniz, leibniz
-/
theorem leibniz : D (a * b) = a • D b + b • D a :=
  D.leibniz' _ _

@[simp]
/--
theorem `map_smul_of_tower` / 定理 `map_smul_of_tower`

English:
theorem map_smul_of_tower
  statement: {S : Type*} [SMul S A] [SMul S M] [LinearMap.CompatibleSMul A M S R]
  proof: D.toLinearMap.map_smul_of_tower r a

@[simp]

中文:
定理 map_smul_of_tower
  结论: {S : 类型} [标量乘法 S A] [标量乘法 S M] [线性映射.余mpatibleSMul A M S R]
  证明: D.toLinearMap.map_smul_of_tower r a

@[simp]

Depends on / 依赖: D.toLinearMap.map_smul_of_tower, map_smul_of_tower, toLinearMap
-/
theorem map_smul_of_tower {S : Type*} [SMul S A] [SMul S M] [LinearMap.CompatibleSMul A M S R]
    (D : Derivation R A M) (r : S) (a : A) : D (r • a) = r • D a :=
  D.toLinearMap.map_smul_of_tower r a

@[simp]
/--
theorem `map_one_eq_zero` / 定理 `map_one_eq_zero`

English:
theorem map_one_eq_zero
  statement: D 1 = 0
  proof: D.map_one_eq_zero'

@[simp]

中文:
定理 map_one_eq_zero
  结论: D 1 = 0
  证明: D.map_one_eq_zero'

@[simp]

Depends on / 依赖: D.map_one_eq_zero, map_one_eq_zero
-/
theorem map_one_eq_zero : D 1 = 0 :=
  D.map_one_eq_zero'

@[simp]
/--
theorem `map_algebraMap` / 定理 `map_algebraMap`

English:
theorem map_algebraMap
  statement: D (algebraMap R A r) = 0
  proof: by
  rw [← mul_one r]; rw [map_mul]; rw [map_one]; rw [← smul_def]; rw [map_smul]; rw [map_one_eq_zero]; rw [smul_zero]

@[simp]

中文:
定理 map_algebraMap
  结论: D (algebraMap R A r) = 0
  证明: by
  rw [← mul_one r]; rw [map_mul]; rw [map_one]; rw [← smul_def]; rw [map_smul]; rw [map_one_eq_zero]; rw [smul_zero]

@[simp]

Depends on / 依赖: map_mul, map_one, map_one_eq_zero, map_smul, mul_one, smul_def, smul_zero
-/
theorem map_algebraMap : D (algebraMap R A r) = 0 := by
  rw [← mul_one r]; rw [map_mul]; rw [map_one]; rw [← smul_def]; rw [map_smul]; rw [map_one_eq_zero]; rw [smul_zero]

@[simp]
/--
theorem `map_natCast` / 定理 `map_natCast`

English:
theorem map_natCast
  given: (n : Nat)
  statement: D (n : A) = 0
  proof: by
  rw [← nsmul_one]; rw [D.map_smul_of_tower n]; rw [map_one_eq_zero]; rw [smul_zero]

@[simp]

中文:
定理 map_natCast
  条件: (n : 自然数)
  结论: D (n : A) = 0
  证明: by
  rw [← nsmul_one]; rw [D.map_smul_of_tower n]; rw [map_one_eq_zero]; rw [smul_zero]

@[simp]

Depends on / 依赖: D.map_smul_of_tower, map_one_eq_zero, map_smul_of_tower, nsmul_one, smul_zero
-/
theorem map_natCast (n : Nat) : D (n : A) = 0 := by
  rw [← nsmul_one]; rw [D.map_smul_of_tower n]; rw [map_one_eq_zero]; rw [smul_zero]

@[simp]
/--
theorem `leibniz_pow` / 定理 `leibniz_pow`

English:
theorem leibniz_pow
  given: (n : Nat)
  statement: D (a ^ n) = n • a ^ (n - 1) • D a
  proof: by
  induction n with
  | zero => rw [pow_zero, map_one_eq_zero, zero_smul]
  | succ n ihn =>
    rcases eq_zero_or_pos n with (rfl | hpos)
    · simp
    · have : a * a ^ (n - 1) = a ^ n := by rw [← pow_succ', Nat.sub_add_cancel hpos]
      simp only [pow_succ', leibniz, ihn, smul_comm a n (_ : M),

中文:
定理 leibniz_pow
  条件: (n : 自然数)
  结论: D (a ^ n) = n • a ^ (n - 1) • D a
  证明: by
  induction n with
  | zero => rw [pow_zero, map_one_eq_zero, zero_smul]
  | succ n ihn =>
    rcases eq_zero_or_pos n with (rfl | hpos)
    · simp
    · have : a * a ^ (n - 1) = a ^ n := by rw [← pow_succ', Nat.sub_add_cancel hpos]
      simp only [pow_succ', leibniz, ihn, smul_comm a n (_ : M),

Depends on / 依赖: Nat.add_succ_sub_one, Nat.sub_add_cancel, add_smul, add_succ_sub_one, add_zero, eq_zero_or_pos, leibniz, map_one_eq_zero, one_nsmul, pow_succ, pow_zero, smul_comm, smul_smul, sub_add_cancel, zero_smul
-/
theorem leibniz_pow (n : Nat) : D (a ^ n) = n • a ^ (n - 1) • D a := by
  induction n with
  | zero => rw [pow_zero, map_one_eq_zero, zero_smul]
  | succ n ihn =>
    rcases eq_zero_or_pos n with (rfl | hpos)
    · simp
    · have : a * a ^ (n - 1) = a ^ n := by rw [← pow_succ', Nat.sub_add_cancel hpos]
      simp only [pow_succ', leibniz, ihn, smul_comm a n (_ : M), smul_smul a, add_smul, this,
        Nat.add_succ_sub_one, add_zero, one_nsmul]

open Polynomial in
@[simp]
/--
theorem `map_aeval` / 定理 `map_aeval`

English:
theorem map_aeval
  given: (P : R[X]) (x : A)
  proof: by
  induction P using Polynomial.induction_on
  · simp
  · simp [add_smul, *]
  · simp [mul_smul, ← Nat.cast_smul_eq_nsmul A]

中文:
定理 map_aeval
  条件: (P : R[X]) (x : A)
  证明: by
  induction P using Polynomial.induction_on
  · simp
  · simp [add_smul, *]
  · simp [mul_smul, ← Nat.cast_smul_eq_nsmul A]

Depends on / 依赖: Nat.cast_smul_eq_nsmul, Polynomial, Polynomial.induction_on, add_smul, cast_smul_eq_nsmul, induction_on, mul_smul
-/
theorem map_aeval (P : R[X]) (x : A) :
    D (aeval x P) = aeval x (derivative P) • D x := by
  induction P using Polynomial.induction_on
  · simp
  · simp [add_smul, *]
  · simp [mul_smul, ← Nat.cast_smul_eq_nsmul A]

/--
theorem `eqOn_adjoin` / 定理 `eqOn_adjoin`

English:
theorem eqOn_adjoin
  given: {s : Set A} (h : Set.EqOn D1 D2 s)
  statement: Set.EqOn D1 D2 (adjoin R s)
  proof: fun _ hx =>
  Algebra.adjoin_induction (hx := hx) h
    (fun r => (D1.map_algebraMap r).trans (D2.map_algebraMap r).symm)
    (fun x y _ _ hx hy => by simp only [map_add, *]) fun x y _ _ hx hy => by simp only [leibniz, *]

中文:
定理 eqOn_adjoin
  条件: {s : 集合 A} (h : 集合.EqOn D1 D2 s)
  结论: 集合.EqOn D1 D2 (adjoin R s)
  证明: fun _ hx =>
  Algebra.adjoin_induction (hx := hx) h
    (fun r => (D1.map_algebraMap r).trans (D2.map_algebraMap r).symm)
    (fun x y _ _ hx hy => by simp only [map_add, *]) fun x y _ _ hx hy => by simp only [leibniz, *]
-/
theorem eqOn_adjoin {s : Set A} (h : Set.EqOn D1 D2 s) : Set.EqOn D1 D2 (adjoin R s) := fun _ hx =>
  Algebra.adjoin_induction (hx := hx) h
    (fun r => (D1.map_algebraMap r).trans (D2.map_algebraMap r).symm)
    (fun x y _ _ hx hy => by simp only [map_add, *]) fun x y _ _ hx hy => by simp only [leibniz, *]

/--
theorem `ext_of_adjoin_eq_top` / 定理 `ext_of_adjoin_eq_top`

English:
theorem ext_of_adjoin_eq_top
  given: (s : Set A) (hs : adjoin R s = ⊤) (h : Set.EqOn D1 D2 s)
  statement: D1 = D2
  proof: ext fun _ => eqOn_adjoin h hs.symm ▸ trivial

中文:
定理 ext_of_adjoin_eq_top
  条件: (s : 集合 A) (hs : adjoin R s = ⊤) (h : 集合.EqOn D1 D2 s)
  结论: D1 = D2
  证明: ext fun _ => eqOn_adjoin h hs.symm ▸ trivial

Depends on / 依赖: eqOn_adjoin, hs.symm
-/
theorem ext_of_adjoin_eq_top (s : Set A) (hs : adjoin R s = ⊤) (h : Set.EqOn D1 D2 s) : D1 = D2 :=
ext fun _ => eqOn_adjoin h hs.symm ▸ trivial

-- Data typeclasses
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Zero (Derivation R A M)
  body: ⟨{ toLinearMap := 0
      map_one_eq_zero' := rfl
      leibniz' := fun a b => by simp only [add_zero, LinearMap.zero_apply, smul_zero] }⟩

@[simp]

中文:
实例 :
  签名: 零 (导子 R A M)
  定义体: ⟨{ toLinearMap := 0
      map_one_eq_zero' := rfl
      leibniz' := fun a b => by simp only [add_zero, LinearMap.zero_apply, smul_zero] }⟩

@[simp]

Depends on / 依赖: LinearMap, LinearMap.zero_apply, add_zero, leibniz, map_one_eq_zero, smul_zero, toLinearMap, zero_apply
-/
instance : Zero (Derivation R A M) :=
  ⟨{ toLinearMap := 0
      map_one_eq_zero' := rfl
      leibniz' := fun a b => by simp only [add_zero, LinearMap.zero_apply, smul_zero] }⟩

@[simp]
/--
theorem `coe_zero` / 定理 `coe_zero`

English:
theorem coe_zero
  statement: ⇑(0 : Derivation R A M) = 0
  proof: rfl

@[simp]

中文:
定理 coe_zero
  结论: ⇑(0 : 导子 R A M) = 0
  证明: rfl

@[simp]
-/
theorem coe_zero : ⇑(0 : Derivation R A M) = 0 :=
  rfl

@[simp]
/--
theorem `coe_zero_linearMap` / 定理 `coe_zero_linearMap`

English:
theorem coe_zero_linearMap
  statement: ↑(0 : Derivation R A M) = (0 : A ->ₗ[R] M)
  proof: rfl

中文:
定理 coe_zero_linearMap
  结论: ↑(0 : 导子 R A M) = (0 : A ->ₗ[R] M)
  证明: rfl
-/
theorem coe_zero_linearMap : ↑(0 : Derivation R A M) = (0 : A ->ₗ[R] M) :=
  rfl

/--
theorem `zero_apply` / 定理 `zero_apply`

English:
theorem zero_apply
  given: (a : A)
  statement: (0 : Derivation R A M) a = 0
  proof: rfl

中文:
定理 zero_apply
  条件: (a : A)
  结论: (0 : 导子 R A M) a = 0
  证明: rfl
-/
theorem zero_apply (a : A) : (0 : Derivation R A M) a = 0 :=
  rfl

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Add (Derivation R A M)
  body: ⟨fun D1 D2 =>
    { toLinearMap := D1 + D2
      map_one_eq_zero' := by simp
      leibniz' := fun a b => by
        simp only [leibniz, LinearMap.add_apply, coeFn_coe, smul_add, add_add_add_comm] }⟩

@[simp]

中文:
实例 :
  签名: 加法 (导子 R A M)
  定义体: ⟨fun D1 D2 =>
    { toLinearMap := D1 + D2
      map_one_eq_zero' := by simp
      leibniz' := fun a b => by
        simp only [leibniz, LinearMap.add_apply, coeFn_coe, smul_add, add_add_add_comm] }⟩

@[simp]

Depends on / 依赖: LinearMap, LinearMap.add_apply, add_add_add_comm, add_apply, coeFn_coe, leibniz, map_one_eq_zero, smul_add, toLinearMap
-/
instance : Add (Derivation R A M) :=
  ⟨fun D1 D2 =>
    { toLinearMap := D1 + D2
      map_one_eq_zero' := by simp
      leibniz' := fun a b => by
        simp only [leibniz, LinearMap.add_apply, coeFn_coe, smul_add, add_add_add_comm] }⟩

@[simp]
/--
theorem `coe_add` / 定理 `coe_add`

English:
theorem coe_add
  given: (D1 D2 : Derivation R A M)
  statement: ⇑(D1 + D2) = D1 + D2
  proof: rfl

@[simp]

中文:
定理 coe_add
  条件: (D1 D2 : 导子 R A M)
  结论: ⇑(D1 + D2) = D1 + D2
  证明: rfl

@[simp]
-/
theorem coe_add (D1 D2 : Derivation R A M) : ⇑(D1 + D2) = D1 + D2 :=
  rfl

@[simp]
/--
theorem `coe_add_linearMap` / 定理 `coe_add_linearMap`

English:
theorem coe_add_linearMap
  given: (D1 D2 : Derivation R A M)
  statement: ↑(D1 + D2) = (D1 + D2 : A ->ₗ[R] M)
  proof: rfl

中文:
定理 coe_add_linearMap
  条件: (D1 D2 : 导子 R A M)
  结论: ↑(D1 + D2) = (D1 + D2 : A ->ₗ[R] M)
  证明: rfl
-/
theorem coe_add_linearMap (D1 D2 : Derivation R A M) : ↑(D1 + D2) = (D1 + D2 : A ->ₗ[R] M) :=
  rfl

/--
theorem `add_apply` / 定理 `add_apply`

English:
theorem add_apply
  statement: (D1 + D2) a = D1 a + D2 a
  proof: rfl

中文:
定理 add_apply
  结论: (D1 + D2) a = D1 a + D2 a
  证明: rfl
-/
theorem add_apply : (D1 + D2) a = D1 a + D2 a :=
  rfl

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Inhabited (Derivation R A M)
  body: ⟨0⟩

中文:
实例 :
  签名: 可居 (导子 R A M)
  定义体: ⟨0⟩
-/
instance : Inhabited (Derivation R A M) :=
  ⟨0⟩

section Scalar

variable {S T : Type*}
variable [Monoid S] [DistribMulAction S M] [SMulCommClass R S M] [SMulCommClass S A M]
variable [Monoid T] [DistribMulAction T M] [SMulCommClass R T M] [SMulCommClass T A M]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: SMul S (Derivation R A M)
  body: ⟨fun r D =>
    { toLinearMap := r • D.1
      map_one_eq_zero' := by rw [LinearMap.smul_apply, coeFn_coe, D.map_one_eq_zero, smul_zero]
      leibniz' := fun a b => by simp only [LinearMap.smul_apply, coeFn_coe, leibniz, smul_add,
        smul_comm r (_ : A) (_ : M)] }⟩

@[simp]

中文:
实例 :
  签名: 标量乘法 S (导子 R A M)
  定义体: ⟨fun r D =>
    { toLinearMap := r • D.1
      map_one_eq_zero' := by rw [LinearMap.smul_apply, coeFn_coe, D.map_one_eq_zero, smul_zero]
      leibniz' := fun a b => by simp only [LinearMap.smul_apply, coeFn_coe, leibniz, smul_add,
        smul_comm r (_ : A) (_ : M)] }⟩

@[simp]

Depends on / 依赖: D.map_one_eq_zero, LinearMap, LinearMap.smul_apply, coeFn_coe, leibniz, map_one_eq_zero, smul_add, smul_apply, smul_comm, smul_zero, toLinearMap
-/
instance : SMul S (Derivation R A M) :=
  ⟨fun r D =>
    { toLinearMap := r • D.1
      map_one_eq_zero' := by rw [LinearMap.smul_apply, coeFn_coe, D.map_one_eq_zero, smul_zero]
      leibniz' := fun a b => by simp only [LinearMap.smul_apply, coeFn_coe, leibniz, smul_add,
        smul_comm r (_ : A) (_ : M)] }⟩

@[simp]
/--
theorem `coe_smul` / 定理 `coe_smul`

English:
theorem coe_smul
  given: (r : S) (D : Derivation R A M)
  statement: ⇑(r • D) = r • ⇑D
  proof: rfl

@[simp]

中文:
定理 coe_smul
  条件: (r : S) (D : 导子 R A M)
  结论: ⇑(r • D) = r • ⇑D
  证明: rfl

@[simp]
-/
theorem coe_smul (r : S) (D : Derivation R A M) : ⇑(r • D) = r • ⇑D :=
  rfl

@[simp]
/--
theorem `coe_smul_linearMap` / 定理 `coe_smul_linearMap`

English:
theorem coe_smul_linearMap
  given: (r : S) (D : Derivation R A M)
  statement: ↑(r • D) = r • (D : A ->ₗ[R] M)
  proof: rfl

中文:
定理 coe_smul_linearMap
  条件: (r : S) (D : 导子 R A M)
  结论: ↑(r • D) = r • (D : A ->ₗ[R] M)
  证明: rfl
-/
theorem coe_smul_linearMap (r : S) (D : Derivation R A M) : ↑(r • D) = r • (D : A ->ₗ[R] M) :=
  rfl

/--
theorem `smul_apply` / 定理 `smul_apply`

English:
theorem smul_apply
  given: (r : S) (D : Derivation R A M)
  statement: (r • D) a = r • D a
  proof: rfl

中文:
定理 smul_apply
  条件: (r : S) (D : 导子 R A M)
  结论: (r • D) a = r • D a
  证明: rfl
-/
theorem smul_apply (r : S) (D : Derivation R A M) : (r • D) a = r • D a :=
  rfl

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: AddCommMonoid (Derivation R A M)
  body: coe_injective.addCommMonoid _ coe_zero coe_add fun _ _ => rfl

中文:
实例 :
  签名: 加法交换幺半群 (导子 R A M)
  定义体: coe_injective.addCommMonoid _ coe_zero coe_add fun _ _ => rfl

Depends on / 依赖: addCommMonoid, coe_add, coe_injective, coe_injective.addCommMonoid, coe_zero
-/
instance : AddCommMonoid (Derivation R A M) :=
  coe_injective.addCommMonoid _ coe_zero coe_add fun _ _ => rfl

/--
Definition of `coeFnAddMonoidHom` / `coeFnAddMonoidHom` 的定义

English:
definition coeFnAddMonoidHom
  signature: : Derivation R A M ->+ A -> M where
  body: (⇑)
  map_zero' := coe_zero
  map_add' := coe_add

@[simp]

中文:
定义 coeFnAddMonoidHom
  签名: : 导子 R A M ->+ A -> M where
  定义体: (⇑)
  map_zero' := coe_zero
  map_add' := coe_add

@[simp]
-/
def coeFnAddMonoidHom : Derivation R A M ->+ A -> M where
  toFun := (⇑)
  map_zero' := coe_zero
  map_add' := coe_add

@[simp]
/--
lemma `coeFnAddMonoidHom_apply` / 引理 `coeFnAddMonoidHom_apply`

English:
lemma coeFnAddMonoidHom_apply
  given: (D : Derivation R A M)
  statement: coeFnAddMonoidHom D = D
  proof: rfl

中文:
引理 coeFnAddMonoidHom_apply
  条件: (D : 导子 R A M)
  结论: coeFnAddMonoidHom D = D
  证明: rfl
-/
lemma coeFnAddMonoidHom_apply (D : Derivation R A M) : coeFnAddMonoidHom D = D := rfl

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: DistribMulAction S (Derivation R A M)
  body: Function.Injective.distribMulAction coeFnAddMonoidHom coe_injective coe_smul

中文:
实例 :
  签名: 分配乘法作用 S (导子 R A M)
  定义体: Function.Injective.distribMulAction coeFnAddMonoidHom coe_injective coe_smul

Depends on / 依赖: Function, Function.Injective.distribMulAction, Injective, coeFnAddMonoidHom, coe_injective, coe_smul, distribMulAction
-/
instance : DistribMulAction S (Derivation R A M) :=
  Function.Injective.distribMulAction coeFnAddMonoidHom coe_injective coe_smul

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [DistribMulAction
  signature: Sᵐᵒᵖ M] [IsCentralScalar S M] :
  body: ext fun _ => op_smul_eq_smul _ _

中文:
实例 [分配乘法作用
  签名: Sᵐᵒᵖ M] [中心标量 S M] :
  定义体: ext fun _ => op_smul_eq_smul _ _

Depends on / 依赖: op_smul_eq_smul
-/
instance [DistribMulAction Sᵐᵒᵖ M] [IsCentralScalar S M] :
    IsCentralScalar S (Derivation R A M) where
  op_smul_eq_smul _ _ := ext fun _ => op_smul_eq_smul _ _

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [SMul
  signature: S T] [IsScalarTower S T M] : IsScalarTower S T (Derivation R A M)
  body: ⟨fun _ _ _ => ext fun _ => smul_assoc _ _ _⟩

中文:
实例 [标量乘法
  签名: S T] [标量塔 S T M] : 标量塔 S T (导子 R A M)
  定义体: ⟨fun _ _ _ => ext fun _ => smul_assoc _ _ _⟩

Depends on / 依赖: smul_assoc
-/
instance [SMul S T] [IsScalarTower S T M] : IsScalarTower S T (Derivation R A M) :=
  ⟨fun _ _ _ => ext fun _ => smul_assoc _ _ _⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [SMulCommClass
  signature: S T M] : SMulCommClass S T (Derivation R A M)
  body: ⟨fun _ _ _ => ext fun _ => smul_comm _ _ _⟩

中文:
实例 [标量交换类
  签名: S T M] : 标量交换类 S T (导子 R A M)
  定义体: ⟨fun _ _ _ => ext fun _ => smul_comm _ _ _⟩

Depends on / 依赖: smul_comm
-/
instance [SMulCommClass S T M] : SMulCommClass S T (Derivation R A M) :=
  ⟨fun _ _ _ => ext fun _ => smul_comm _ _ _⟩

end Scalar

/--
Instance `instModule` / 实例 `instModule`

English:
instance instModule
  signature: {S : Type*} [Semiring S] [Module S M] [SMulCommClass R S M]
  body: Function.Injective.module S coeFnAddMonoidHom coe_injective coe_smul

中文:
实例 instModule
  签名: {S : 类型} [半环 S] [模 S M] [标量交换类 R S M]
  定义体: Function.Injective.module S coeFnAddMonoidHom coe_injective coe_smul

Depends on / 依赖: Function, Function.Injective.module, Injective, coeFnAddMonoidHom, coe_injective, coe_smul, module
-/
instance instModule {S : Type*} [Semiring S] [Module S M] [SMulCommClass R S M]
    [SMulCommClass S A M] : Module S (Derivation R A M) :=
  Function.Injective.module S coeFnAddMonoidHom coe_injective coe_smul

section PushForward

variable {N : Type*} [AddCommMonoid N] [Module A N] [Module R N] [IsScalarTower R A M]
  [IsScalarTower R A N]

variable (f : M ->ₗ[A] N) (e : M ≃ₗ[A] N)

set_option backward.isDefEq.respectTransparency false in
/--
Definition of `_root_.LinearMap.compDer` / `_root_.LinearMap.compDer` 的定义

English:
definition _root_.LinearMap.compDer
  signature: : Derivation R A M ->ₗ[A] Derivation R A N where
  body: { toLinearMap := (f : M ->ₗ[R] N).comp (D : A ->ₗ[R] M)
      map_one_eq_zero' := by simp only [LinearMap.comp_apply, coeFn_coe, map_one_eq_zero, map_zero]
      leibniz' := fun a b => by
        simp only [coeFn_coe, LinearMap.comp_apply, map_add, leibniz,
          LinearMap.coe_restrictScalars, L

中文:
定义 _root_.线性映射.compDer
  签名: : 导子 R A M ->ₗ[A] 导子 R A N where
  定义体: { toLinearMap := (f : M ->ₗ[R] N).comp (D : A ->ₗ[R] M)
      map_one_eq_zero' := by simp only [LinearMap.comp_apply, coeFn_coe, map_one_eq_zero, map_zero]
      leibniz' := fun a b => by
        simp only [coeFn_coe, LinearMap.comp_apply, map_add, leibniz,
          LinearMap.coe_restrictScalars, L

Depends on / 依赖: LinearMap, LinearMap.coe_restrictScalars, LinearMap.comp_apply, LinearMap.map_add, LinearMap.map_smul, _root_, _root_.map_smul, coeFn_coe, coe_restrictScalars, comp_apply, leibniz, map_add, map_one_eq_zero, map_smul, map_zero, toLinearMap
-/
def _root_.LinearMap.compDer : Derivation R A M ->ₗ[A] Derivation R A N where
  toFun D :=
    { toLinearMap := (f : M ->ₗ[R] N).comp (D : A ->ₗ[R] M)
      map_one_eq_zero' := by simp only [LinearMap.comp_apply, coeFn_coe, map_one_eq_zero, map_zero]
      leibniz' := fun a b => by
        simp only [coeFn_coe, LinearMap.comp_apply, map_add, leibniz,
          LinearMap.coe_restrictScalars, LinearMap.map_smul] }
  map_add' D₁ D₂ := by ext; exact LinearMap.map_add _ _ _
  map_smul' r D := by ext; dsimp; simp only [_root_.map_smul]

@[simp]
/--
theorem `coe_to_linearMap_comp` / 定理 `coe_to_linearMap_comp`

English:
theorem coe_to_linearMap_comp
  statement: (f.compDer D : A ->ₗ[R] N) = (f : M ->ₗ[R] N).comp (D : A ->ₗ[R] M)
  proof: rfl

@[simp]

中文:
定理 coe_to_linearMap_comp
  结论: (f.compDer D : A ->ₗ[R] N) = (f : M ->ₗ[R] N).comp (D : A ->ₗ[R] M)
  证明: rfl

@[simp]
-/
theorem coe_to_linearMap_comp : (f.compDer D : A ->ₗ[R] N) = (f : M ->ₗ[R] N).comp (D : A ->ₗ[R] M) :=
  rfl

@[simp]
/--
theorem `coe_comp` / 定理 `coe_comp`

English:
theorem coe_comp
  statement: (f.compDer D : A -> N) = (f : M ->ₗ[R] N).comp (D : A ->ₗ[R] M)
  proof: rfl

中文:
定理 coe_comp
  结论: (f.compDer D : A -> N) = (f : M ->ₗ[R] N).comp (D : A ->ₗ[R] M)
  证明: rfl
-/
theorem coe_comp : (f.compDer D : A -> N) = (f : M ->ₗ[R] N).comp (D : A ->ₗ[R] M) :=
  rfl

/-- The composition of a derivation with a linear map as a bilinear map -/
@[simps]
/--
Definition of `llcomp` / `llcomp` 的定义

English:
definition llcomp
  signature: : (M ->ₗ[A] N) ->ₗ[A] Derivation R A M ->ₗ[A] Derivation R A N where
  body: f.compDer
  map_add' f₁ f₂ := by ext; rfl
  map_smul' r D := by ext; rfl

中文:
定义 llcomp
  签名: : (M ->ₗ[A] N) ->ₗ[A] 导子 R A M ->ₗ[A] 导子 R A N where
  定义体: f.compDer
  map_add' f₁ f₂ := by ext; rfl
  map_smul' r D := by ext; rfl

Depends on / 依赖: compDer, f.compDer
-/
def llcomp : (M ->ₗ[A] N) ->ₗ[A] Derivation R A M ->ₗ[A] Derivation R A N where
  toFun f := f.compDer
  map_add' f₁ f₂ := by ext; rfl
  map_smul' r D := by ext; rfl

/--
Definition of `_root_.LinearEquiv.compDer` / `_root_.LinearEquiv.compDer` 的定义

English:
definition _root_.LinearEquiv.compDer
  signature: : Derivation R A M ≃ₗ[A] Derivation R A N
  body: { e.toLinearMap.compDer with
    invFun := e.symm.toLinearMap.compDer
    left_inv := fun D => by ext a; exact e.symm_apply_apply (D a)
    right_inv := fun D => by ext a; exact e.apply_symm_apply (D a) }

@[simp]

中文:
定义 _root_.线性等价.compDer
  签名: : 导子 R A M ≃ₗ[A] 导子 R A N
  定义体: { e.toLinearMap.compDer with
    invFun := e.symm.toLinearMap.compDer
    left_inv := fun D => by ext a; exact e.symm_apply_apply (D a)
    right_inv := fun D => by ext a; exact e.apply_symm_apply (D a) }

@[simp]

Depends on / 依赖: apply_symm_apply, compDer, e.apply_symm_apply, e.symm.toLinearMap.compDer, e.symm_apply_apply, e.toLinearMap.compDer, invFun, left_inv, right_inv, symm_apply_apply, toLinearMap
-/
def _root_.LinearEquiv.compDer : Derivation R A M ≃ₗ[A] Derivation R A N :=
  { e.toLinearMap.compDer with
    invFun := e.symm.toLinearMap.compDer
    left_inv := fun D => by ext a; exact e.symm_apply_apply (D a)
    right_inv := fun D => by ext a; exact e.apply_symm_apply (D a) }

@[simp]
/--
theorem `linearEquiv_coe_to_linearMap_comp` / 定理 `linearEquiv_coe_to_linearMap_comp`

English:
theorem linearEquiv_coe_to_linearMap_comp
  proof: rfl

@[simp]

中文:
定理 linearEquiv_coe_to_linearMap_comp
  证明: rfl

@[simp]
-/
theorem linearEquiv_coe_to_linearMap_comp :
    (e.compDer D : A ->ₗ[R] N) = (e.toLinearMap : M ->ₗ[R] N).comp (D : A ->ₗ[R] M) :=
  rfl

@[simp]
/--
theorem `linearEquiv_coe_comp` / 定理 `linearEquiv_coe_comp`

English:
theorem linearEquiv_coe_comp
  proof: rfl

中文:
定理 linearEquiv_coe_comp
  证明: rfl
-/
theorem linearEquiv_coe_comp :
    (e.compDer D : A -> N) = (e.toLinearMap : M ->ₗ[R] N).comp (D : A ->ₗ[R] M) :=
  rfl

end PushForward

variable (A) in
/-- For a tower `R → A → B` and an `R`-derivation `B → M`, we may compose with `A → B` to obtain an
`R`-derivation `A → M`. -/
@[simps!]
/--
Definition of `compAlgebraMap` / `compAlgebraMap` 的定义

English:
definition compAlgebraMap
  signature: [Algebra A B] [IsScalarTower R A B] [IsScalarTower A B M]
  body: by simp
  leibniz' a b := by simp
  toLinearMap := d.toLinearMap.comp (IsScalarTower.toAlgHom R A B).toLinearMap

中文:
定义 compAlgebraMap
  签名: [代数 A B] [标量塔 R A B] [标量塔 A B M]
  定义体: by simp
  leibniz' a b := by simp
  toLinearMap := d.toLinearMap.comp (IsScalarTower.toAlgHom R A B).toLinearMap

Depends on / 依赖: IsScalarTower, IsScalarTower.toAlgHom, d.toLinearMap.comp, leibniz, toAlgHom, toLinearMap
-/
def compAlgebraMap [Algebra A B] [IsScalarTower R A B] [IsScalarTower A B M]
    (d : Derivation R B M) : Derivation R A M where
  map_one_eq_zero' := by simp
  leibniz' a b := by simp
  toLinearMap := d.toLinearMap.comp (IsScalarTower.toAlgHom R A B).toLinearMap

variable (R A B M) in
/-- For a tower `R → A → B → M`, the precomposition defined in `compAlgebraMap`
is a `B`-linear map. -/
@[simps!]
/--
Definition of `compAlgebraMapL` / `compAlgebraMapL` 的定义

English:
definition compAlgebraMapL
  signature: [Algebra A B] [IsScalarTower R A B] [IsScalarTower A B M]
  body: d.compAlgebraMap A
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

中文:
定义 compAlgebraMapL
  签名: [代数 A B] [标量塔 R A B] [标量塔 A B M]
  定义体: d.compAlgebraMap A
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

Depends on / 依赖: compAlgebraMap, d.compAlgebraMap
-/
def compAlgebraMapL [Algebra A B] [IsScalarTower R A B] [IsScalarTower A B M]
    [IsScalarTower R B M] :
    Derivation R B M ->ₗ[B] Derivation R A M where
  toFun d := d.compAlgebraMap A
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

section RestrictScalars

variable {S : Type*} [CommSemiring S]
variable [Algebra S A] [Module S M] [LinearMap.CompatibleSMul A M R S]
variable (R)

/--
Definition of `restrictScalars` / `restrictScalars` 的定义

English:
definition restrictScalars
  signature: (d : Derivation S A M)
  body: d.map_one_eq_zero
  leibniz' := d.leibniz
  toLinearMap := d.toLinearMap.restrictScalars R

中文:
定义 restrictScalars
  签名: (d : 导子 S A M)
  定义体: d.map_one_eq_zero
  leibniz' := d.leibniz
  toLinearMap := d.toLinearMap.restrictScalars R
-/
protected def restrictScalars (d : Derivation S A M) : Derivation R A M where
  map_one_eq_zero' := d.map_one_eq_zero
  leibniz' := d.leibniz
  toLinearMap := d.toLinearMap.restrictScalars R

/--
lemma `coe_restrictScalars` / 引理 `coe_restrictScalars`

English:
lemma coe_restrictScalars
  given: (d : Derivation S A M)
  statement: ⇑(d.restrictScalars R) = ⇑d
  proof: rfl

@[simp]

中文:
引理 coe_restrictScalars
  条件: (d : 导子 S A M)
  结论: ⇑(d.restrictScalars R) = ⇑d
  证明: rfl

@[simp]
-/
lemma coe_restrictScalars (d : Derivation S A M) : ⇑(d.restrictScalars R) = ⇑d := rfl

@[simp]
/--
lemma `restrictScalars_apply` / 引理 `restrictScalars_apply`

English:
lemma restrictScalars_apply
  given: (d : Derivation S A M) (x : A)
  statement: d.restrictScalars R x = d x
  proof: rfl

中文:
引理 restrictScalars_apply
  条件: (d : 导子 S A M) (x : A)
  结论: d.restrictScalars R x = d x
  证明: rfl
-/
lemma restrictScalars_apply (d : Derivation S A M) (x : A) : d.restrictScalars R x = d x := rfl

end RestrictScalars

end

section Lift

variable {R : Type*} {A : Type*} {M : Type*}
variable [CommSemiring R] [CommRing A] [CommRing M]
variable [Algebra R A] [Algebra R M]
variable {F : Type*} [FunLike F A M] [AlgHomClass F R A M]

set_option backward.isDefEq.respectTransparency false in
/--
Definition of `liftOfRightInverse` / `liftOfRightInverse` 的定义

English:
definition liftOfRightInverse
  signature: {f : F} {f_inv : M -> A} (hf : Function.RightInverse f_inv f)
  body: f (d (f_inv x))
  map_add' x y := by
    suffices f (d (f_inv (x + y) - (f_inv x + f_inv y))) = 0 by simpa [sub_eq_zero]
    apply hd
    simp [hf _]
  map_smul' x y := by
    suffices f (d (f_inv (x • y) - x • f_inv y)) = 0 by simpa [sub_eq_zero]
    apply hd
    simp [hf _]
  map_one_eq_zero' := b

中文:
定义 liftOfRightInverse
  签名: {f : F} {f_inv : M -> A} (hf : 函数.右逆 f_inv f)
  定义体: f (d (f_inv x))
  map_add' x y := by
    suffices f (d (f_inv (x + y) - (f_inv x + f_inv y))) = 0 by simpa [sub_eq_zero]
    apply hd
    simp [hf _]
  map_smul' x y := by
    suffices f (d (f_inv (x • y) - x • f_inv y)) = 0 by simpa [sub_eq_zero]
    apply hd
    simp [hf _]
  map_one_eq_zero' := b

Depends on / 依赖: f_inv
-/
def liftOfRightInverse {f : F} {f_inv : M -> A} (hf : Function.RightInverse f_inv f)
    ⦃d : Derivation R A A⦄ (hd : forall x, f x = 0 -> f (d x) = 0) : Derivation R M M where
  toFun x := f (d (f_inv x))
  map_add' x y := by
    suffices f (d (f_inv (x + y) - (f_inv x + f_inv y))) = 0 by simpa [sub_eq_zero]
    apply hd
    simp [hf _]
  map_smul' x y := by
    suffices f (d (f_inv (x • y) - x • f_inv y)) = 0 by simpa [sub_eq_zero]
    apply hd
    simp [hf _]
  map_one_eq_zero' := by
    suffices f (d (f_inv 1 - 1)) = 0 by simpa [sub_eq_zero]
    apply hd
    simp [hf _]
  leibniz' x y := by
    suffices f (d (f_inv (x * y) - f_inv x * f_inv y)) = 0 by simpa [sub_eq_zero, hf _]
    apply hd
    simp [hf _]

@[simp]
/--
lemma `liftOfRightInverse_apply` / 引理 `liftOfRightInverse_apply`

English:
lemma liftOfRightInverse_apply
  statement: {f : F} {f_inv : M -> A} (hf : Function.RightInverse f_inv f)
  proof: by
  suffices f (d (f_inv (f x) - x)) = 0 by simpa [sub_eq_zero]
  apply hd
  simp [hf _]

中文:
引理 liftOfRightInverse_apply
  结论: {f : F} {f_inv : M -> A} (hf : 函数.右逆 f_inv f)
  证明: by
  suffices f (d (f_inv (f x) - x)) = 0 by simpa [sub_eq_zero]
  apply hd
  simp [hf _]

Depends on / 依赖: f_inv, sub_eq_zero
-/
lemma liftOfRightInverse_apply {f : F} {f_inv : M -> A} (hf : Function.RightInverse f_inv f)
    {d : Derivation R A A} (hd : forall x, f x = 0 -> f (d x) = 0) (x : A) :
    Derivation.liftOfRightInverse hf hd (f x) = f (d x) := by
  suffices f (d (f_inv (f x) - x)) = 0 by simpa [sub_eq_zero]
  apply hd
  simp [hf _]

/--
lemma `liftOfRightInverse_eq` / 引理 `liftOfRightInverse_eq`

English:
lemma liftOfRightInverse_eq
  statement: {f : F} {f_inv₁ f_inv₂ : M -> A} (hf₁ : Function.RightInverse f_inv₁ f)
  proof: by
  ext _ _ x
  obtain ⟨x, rfl⟩ := hf₁.surjective x
  simp

中文:
引理 liftOfRightInverse_eq
  结论: {f : F} {f_inv₁ f_inv₂ : M -> A} (hf₁ : 函数.右逆 f_inv₁ f)
  证明: by
  ext _ _ x
  obtain ⟨x, rfl⟩ := hf₁.surjective x
  simp

Depends on / 依赖: surjective
-/
lemma liftOfRightInverse_eq {f : F} {f_inv₁ f_inv₂ : M -> A} (hf₁ : Function.RightInverse f_inv₁ f)
    (hf₂ : Function.RightInverse f_inv₂ f) :
    liftOfRightInverse hf₁ = liftOfRightInverse hf₂ := by
  ext _ _ x
  obtain ⟨x, rfl⟩ := hf₁.surjective x
  simp

/--
Definition of `liftOfSurjective` / `liftOfSurjective` 的定义

English:
abbreviation liftOfSurjective
  signature: {f : F} (hf : Function.Surjective f)
  body: d.liftOfRightInverse (Function.rightInverse_surjInv hf) hd

中文:
缩写 liftOfSurjective
  签名: {f : F} (hf : 函数.满射 f)
  定义体: d.liftOfRightInverse (Function.rightInverse_surjInv hf) hd

Depends on / 依赖: Function, Function.rightInverse_surjInv, d.liftOfRightInverse, liftOfRightInverse, rightInverse_surjInv
-/
noncomputable abbrev liftOfSurjective {f : F} (hf : Function.Surjective f)
    ⦃d : Derivation R A A⦄ (hd : forall x, f x = 0 -> f (d x) = 0) : Derivation R M M :=
  d.liftOfRightInverse (Function.rightInverse_surjInv hf) hd

/--
lemma `liftOfSurjective_apply` / 引理 `liftOfSurjective_apply`

English:
lemma liftOfSurjective_apply
  statement: {f : F} (hf : Function.Surjective f)
  proof: by simp

中文:
引理 liftOfSurjective_apply
  结论: {f : F} (hf : 函数.满射 f)
  证明: by simp
-/
lemma liftOfSurjective_apply {f : F} (hf : Function.Surjective f)
    {d : Derivation R A A} (hd : forall x, f x = 0 -> f (d x) = 0) (x : A) :
    Derivation.liftOfSurjective hf hd (f x) = f (d x) := by simp

end Lift

section Cancel

variable {R : Type*} [CommSemiring R] {A : Type*} [CommSemiring A] [Algebra R A] {M : Type*}
  [AddCancelCommMonoid M] [Module R M] [Module A M]

/--
Definition of `mk'` / `mk'` 的定义

English:
definition mk'
  signature: (D : A ->ₗ[R] M) (h : forall a b, D (a * b) = a • D b + b • D a)
  body: D
map_one_eq_zero' := (add_eq_left (a := D 1)).1 by
    simpa only [one_smul, one_mul] using (h 1 1).symm
  leibniz' := h

@[simp]

中文:
定义 mk'
  签名: (D : A ->ₗ[R] M) (h : 对任意 a b, D (a * b) = a • D b + b • D a)
  定义体: D
map_one_eq_zero' := (add_eq_left (a := D 1)).1 by
    simpa only [one_smul, one_mul] using (h 1 1).symm
  leibniz' := h

@[simp]
-/
def mk' (D : A ->ₗ[R] M) (h : forall a b, D (a * b) = a • D b + b • D a) : Derivation R A M where
  toLinearMap := D
map_one_eq_zero' := (add_eq_left (a := D 1)).1 by
    simpa only [one_smul, one_mul] using (h 1 1).symm
  leibniz' := h

@[simp]
/--
theorem `coe_mk'` / 定理 `coe_mk'`

English:
theorem coe_mk'
  given: (D : A ->ₗ[R] M) (h)
  statement: ⇑(mk' D h) = D
  proof: rfl

@[simp]

中文:
定理 coe_mk'
  条件: (D : A ->ₗ[R] M) (h)
  结论: ⇑(mk' D h) = D
  证明: rfl

@[simp]
-/
theorem coe_mk' (D : A ->ₗ[R] M) (h) : ⇑(mk' D h) = D :=
  rfl

@[simp]
/--
theorem `coe_mk'_linearMap` / 定理 `coe_mk'_linearMap`

English:
theorem coe_mk'_linearMap
  given: (D : A ->ₗ[R] M) (h)
  statement: (mk' D h : A ->ₗ[R] M) = D
  proof: rfl

中文:
定理 coe_mk'_linearMap
  条件: (D : A ->ₗ[R] M) (h)
  结论: (mk' D h : A ->ₗ[R] M) = D
  证明: rfl
-/
theorem coe_mk'_linearMap (D : A ->ₗ[R] M) (h) : (mk' D h : A ->ₗ[R] M) = D :=
  rfl

end Cancel

section

variable {R : Type*} [CommRing R]
variable {A : Type*} [CommRing A] [Algebra R A]

section

variable {M : Type*} [AddCommGroup M] [Module A M] [Module R M]
variable (D : Derivation R A M) {D1 D2 : Derivation R A M} (r : R) (a b : A)

/--
theorem `map_neg` / 定理 `map_neg`

English:
theorem map_neg
  statement: D (-a) = -D a
  proof: map_neg D a

中文:
定理 map_neg
  结论: D (-a) = -D a
  证明: map_neg D a
-/
protected theorem map_neg : D (-a) = -D a :=
  map_neg D a

/--
theorem `map_sub` / 定理 `map_sub`

English:
theorem map_sub
  statement: D (a - b) = D a - D b
  proof: map_sub D a b

@[simp]

中文:
定理 map_sub
  结论: D (a - b) = D a - D b
  证明: map_sub D a b

@[simp]
-/
protected theorem map_sub : D (a - b) = D a - D b :=
  map_sub D a b

@[simp]
/--
theorem `map_intCast` / 定理 `map_intCast`

English:
theorem map_intCast
  given: (n : Int)
  statement: D (n : A) = 0
  proof: by
  rw [← zsmul_one]; rw [D.map_smul_of_tower n]; rw [map_one_eq_zero]; rw [smul_zero]

中文:
定理 map_intCast
  条件: (n : 整数)
  结论: D (n : A) = 0
  证明: by
  rw [← zsmul_one]; rw [D.map_smul_of_tower n]; rw [map_one_eq_zero]; rw [smul_zero]

Depends on / 依赖: D.map_smul_of_tower, map_one_eq_zero, map_smul_of_tower, smul_zero, zsmul_one
-/
theorem map_intCast (n : Int) : D (n : A) = 0 := by
  rw [← zsmul_one]; rw [D.map_smul_of_tower n]; rw [map_one_eq_zero]; rw [smul_zero]

/--
theorem `leibniz_of_mul_eq_one` / 定理 `leibniz_of_mul_eq_one`

English:
theorem leibniz_of_mul_eq_one
  given: {a b : A} (h : a * b = 1)
  statement: D a = -a ^ 2 • D b
  proof: by
  rw [neg_smul]
  refine eq_neg_of_add_eq_zero_left ?_
  calc
    D a + a ^ 2 • D b = a • b • D a + a • a • D b := by simp only [smul_smul, h, one_smul, sq]
    _ = a • D (a * b) := by rw [leibniz, smul_add, add_comm]
    _ = 0 := by rw [h, map_one_eq_zero, smul_zero]

中文:
定理 leibniz_of_mul_eq_one
  条件: {a b : A} (h : a * b = 1)
  结论: D a = -a ^ 2 • D b
  证明: by
  rw [neg_smul]
  refine eq_neg_of_add_eq_zero_left ?_
  calc
    D a + a ^ 2 • D b = a • b • D a + a • a • D b := by simp only [smul_smul, h, one_smul, sq]
    _ = a • D (a * b) := by rw [leibniz, smul_add, add_comm]
    _ = 0 := by rw [h, map_one_eq_zero, smul_zero]

Depends on / 依赖: add_comm, eq_neg_of_add_eq_zero_left, leibniz, map_one_eq_zero, neg_smul, one_smul, smul_add, smul_smul, smul_zero
-/
theorem leibniz_of_mul_eq_one {a b : A} (h : a * b = 1) : D a = -a ^ 2 • D b := by
  rw [neg_smul]
  refine eq_neg_of_add_eq_zero_left ?_
  calc
    D a + a ^ 2 • D b = a • b • D a + a • a • D b := by simp only [smul_smul, h, one_smul, sq]
    _ = a • D (a * b) := by rw [leibniz, smul_add, add_comm]
    _ = 0 := by rw [h, map_one_eq_zero, smul_zero]

/--
theorem `leibniz_invOf` / 定理 `leibniz_invOf`

English:
theorem leibniz_invOf
  given: [Invertible a]
  statement: D (⅟a) = -⅟a ^ 2 • D a
  proof: D.leibniz_of_mul_eq_one invOf_mul_self a

中文:
定理 leibniz_invOf
  条件: [可逆 a]
  结论: D (⅟a) = -⅟a ^ 2 • D a
  证明: D.leibniz_of_mul_eq_one invOf_mul_self a

Depends on / 依赖: D.leibniz_of_mul_eq_one, invOf_mul_self, leibniz_of_mul_eq_one
-/
theorem leibniz_invOf [Invertible a] : D (⅟a) = -⅟a ^ 2 • D a :=
D.leibniz_of_mul_eq_one invOf_mul_self a

section Field

variable {K : Type*} [Field K] [Module K M] [Algebra R K] (D : Derivation R K M)

/--
theorem `leibniz_inv` / 定理 `leibniz_inv`

English:
theorem leibniz_inv
  given: (a : K)
  statement: D a⁻¹ = -a⁻¹ ^ 2 • D a
  proof: by
  rcases eq_or_ne a 0 with (rfl | ha)
  · simp
  · exact D.leibniz_of_mul_eq_one (inv_mul_cancel₀ ha)

中文:
定理 leibniz_inv
  条件: (a : K)
  结论: D a⁻¹ = -a⁻¹ ^ 2 • D a
  证明: by
  rcases eq_or_ne a 0 with (rfl | ha)
  · simp
  · exact D.leibniz_of_mul_eq_one (inv_mul_cancel₀ ha)

Depends on / 依赖: D.leibniz_of_mul_eq_one, eq_or_ne, leibniz_of_mul_eq_one
-/
theorem leibniz_inv (a : K) : D a⁻¹ = -a⁻¹ ^ 2 • D a := by
  rcases eq_or_ne a 0 with (rfl | ha)
  · simp
  · exact D.leibniz_of_mul_eq_one (inv_mul_cancel₀ ha)

/--
theorem `leibniz_div` / 定理 `leibniz_div`

English:
theorem leibniz_div
  given: (a b : K)
  statement: D (a / b) = b⁻¹ ^ 2 • (b • D a - a • D b)
  proof: by
  simp only [div_eq_mul_inv, leibniz, leibniz_inv, inv_pow, neg_smul, smul_neg, smul_smul, add_comm,
    sub_eq_add_neg, smul_add]
  rw [← inv_mul_mul_self b⁻¹]; rw [inv_inv]
  ring_nf

中文:
定理 leibniz_div
  条件: (a b : K)
  结论: D (a / b) = b⁻¹ ^ 2 • (b • D a - a • D b)
  证明: by
  simp only [div_eq_mul_inv, leibniz, leibniz_inv, inv_pow, neg_smul, smul_neg, smul_smul, add_comm,
    sub_eq_add_neg, smul_add]
  rw [← inv_mul_mul_self b⁻¹]; rw [inv_inv]
  ring_nf

Depends on / 依赖: add_comm, div_eq_mul_inv, inv_inv, inv_mul_mul_self, inv_pow, leibniz, leibniz_inv, neg_smul, ring_nf, smul_add, smul_neg, smul_smul, sub_eq_add_neg
-/
theorem leibniz_div (a b : K) : D (a / b) = b⁻¹ ^ 2 • (b • D a - a • D b) := by
  simp only [div_eq_mul_inv, leibniz, leibniz_inv, inv_pow, neg_smul, smul_neg, smul_smul, add_comm,
    sub_eq_add_neg, smul_add]
  rw [← inv_mul_mul_self b⁻¹]; rw [inv_inv]
  ring_nf

/--
theorem `leibniz_div_const` / 定理 `leibniz_div_const`

English:
theorem leibniz_div_const
  given: (a b : K) (h : D b = 0)
  statement: D (a / b) = b⁻¹ • D a
  proof: by
  simp only [leibniz_div, inv_pow, h, smul_zero, sub_zero, smul_smul]
  rw [← mul_self_mul_inv b⁻¹]; rw [inv_inv]
  ring_nf

中文:
定理 leibniz_div_const
  条件: (a b : K) (h : D b = 0)
  结论: D (a / b) = b⁻¹ • D a
  证明: by
  simp only [leibniz_div, inv_pow, h, smul_zero, sub_zero, smul_smul]
  rw [← mul_self_mul_inv b⁻¹]; rw [inv_inv]
  ring_nf

Depends on / 依赖: inv_inv, inv_pow, leibniz_div, mul_self_mul_inv, ring_nf, smul_smul, smul_zero, sub_zero
-/
theorem leibniz_div_const (a b : K) (h : D b = 0) : D (a / b) = b⁻¹ • D a := by
  simp only [leibniz_div, inv_pow, h, smul_zero, sub_zero, smul_smul]
  rw [← mul_self_mul_inv b⁻¹]; rw [inv_inv]
  ring_nf

/--
lemma `leibniz_zpow` / 引理 `leibniz_zpow`

English:
lemma leibniz_zpow
  given: (a : K) (n : Int)
  statement: D (a ^ n) = n • a ^ (n - 1) • D a
  proof: by
  by_cases hn : n = 0
  · simp [hn]
  by_cases ha : a = 0
  · simp [ha, zero_zpow n hn]
  rcases Int.natAbs_eq n with h | h
  · rw [h]
    simp only [zpow_natCast, leibniz_pow, natCast_zsmul]
    rw [← zpow_natCast]
    congr
    lia
  · rw [h, zpow_neg, zpow_natCast, leibniz_inv, leibniz_pow, in

中文:
引理 leibniz_zpow
  条件: (a : K) (n : 整数)
  结论: D (a ^ n) = n • a ^ (n - 1) • D a
  证明: by
  by_cases hn : n = 0
  · simp [hn]
  by_cases ha : a = 0
  · simp [ha, zero_zpow n hn]
  rcases Int.natAbs_eq n with h | h
  · rw [h]
    simp only [zpow_natCast, leibniz_pow, natCast_zsmul]
    rw [← zpow_natCast]
    congr
    lia
  · rw [h, zpow_neg, zpow_natCast, leibniz_inv, leibniz_pow, in

Depends on / 依赖: Int.cast_smul_eq_zsmul, Int.natAbs_eq, Nat.cast_smul_eq_nsmul, cast_smul_eq_nsmul, cast_smul_eq_zsmul, inv_pow, leibniz_inv, leibniz_pow, n.natAbs, natAbs, natAbs_eq, natCast_zsmul, pow_mul, smul_smul, zero_zpow, zpow_natCast, zpow_neg
-/
lemma leibniz_zpow (a : K) (n : Int) : D (a ^ n) = n • a ^ (n - 1) • D a := by
  by_cases hn : n = 0
  · simp [hn]
  by_cases ha : a = 0
  · simp [ha, zero_zpow n hn]
  rcases Int.natAbs_eq n with h | h
  · rw [h]
    simp only [zpow_natCast, leibniz_pow, natCast_zsmul]
    rw [← zpow_natCast]
    congr
    lia
  · rw [h, zpow_neg, zpow_natCast, leibniz_inv, leibniz_pow, inv_pow, ← pow_mul, ← zpow_natCast,
      ← zpow_natCast, ← Nat.cast_smul_eq_nsmul K, ← Int.cast_smul_eq_zsmul K, smul_smul, smul_smul,
      smul_smul]
    trans (-n.natAbs * (a ^ ((n.natAbs - 1 : Nat) : Int) / (a ^ ((n.natAbs * 2 : Nat) : Int)))) • D a
    · ring_nf
    rw [← zpow_sub₀ ha]
    congr 3
    · norm_cast
    lia

end Field

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Neg (Derivation R A M)
  body: ⟨fun D =>
    mk' (-D) fun a b => by
      simp only [LinearMap.neg_apply, smul_neg, neg_add_rev, leibniz, coeFn_coe, add_comm]⟩

@[simp]

中文:
实例 :
  签名: 取负 (导子 R A M)
  定义体: ⟨fun D =>
    mk' (-D) fun a b => by
      simp only [LinearMap.neg_apply, smul_neg, neg_add_rev, leibniz, coeFn_coe, add_comm]⟩

@[simp]

Depends on / 依赖: LinearMap, LinearMap.neg_apply, add_comm, coeFn_coe, leibniz, neg_add_rev, neg_apply, smul_neg
-/
instance : Neg (Derivation R A M) :=
  ⟨fun D =>
    mk' (-D) fun a b => by
      simp only [LinearMap.neg_apply, smul_neg, neg_add_rev, leibniz, coeFn_coe, add_comm]⟩

@[simp]
/--
theorem `coe_neg` / 定理 `coe_neg`

English:
theorem coe_neg
  given: (D : Derivation R A M)
  statement: ⇑(-D) = -D
  proof: rfl

@[simp]

中文:
定理 coe_neg
  条件: (D : 导子 R A M)
  结论: ⇑(-D) = -D
  证明: rfl

@[simp]
-/
theorem coe_neg (D : Derivation R A M) : ⇑(-D) = -D :=
  rfl

@[simp]
/--
theorem `coe_neg_linearMap` / 定理 `coe_neg_linearMap`

English:
theorem coe_neg_linearMap
  given: (D : Derivation R A M)
  statement: ↑(-D) = (-D : A ->ₗ[R] M)
  proof: rfl

中文:
定理 coe_neg_linearMap
  条件: (D : 导子 R A M)
  结论: ↑(-D) = (-D : A ->ₗ[R] M)
  证明: rfl
-/
theorem coe_neg_linearMap (D : Derivation R A M) : ↑(-D) = (-D : A ->ₗ[R] M) :=
  rfl

/--
theorem `neg_apply` / 定理 `neg_apply`

English:
theorem neg_apply
  statement: (-D) a = -D a
  proof: rfl

中文:
定理 neg_apply
  结论: (-D) a = -D a
  证明: rfl
-/
theorem neg_apply : (-D) a = -D a :=
  rfl

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Sub (Derivation R A M)
  body: ⟨fun D1 D2 =>
    mk' (D1 - D2 : A ->ₗ[R] M) fun a b => by
      simp only [LinearMap.sub_apply, leibniz, coeFn_coe, smul_sub, add_sub_add_comm]⟩

@[simp]

中文:
实例 :
  签名: 减法 (导子 R A M)
  定义体: ⟨fun D1 D2 =>
    mk' (D1 - D2 : A ->ₗ[R] M) fun a b => by
      simp only [LinearMap.sub_apply, leibniz, coeFn_coe, smul_sub, add_sub_add_comm]⟩

@[simp]

Depends on / 依赖: LinearMap, LinearMap.sub_apply, add_sub_add_comm, coeFn_coe, leibniz, smul_sub, sub_apply
-/
instance : Sub (Derivation R A M) :=
  ⟨fun D1 D2 =>
    mk' (D1 - D2 : A ->ₗ[R] M) fun a b => by
      simp only [LinearMap.sub_apply, leibniz, coeFn_coe, smul_sub, add_sub_add_comm]⟩

@[simp]
/--
theorem `coe_sub` / 定理 `coe_sub`

English:
theorem coe_sub
  given: (D1 D2 : Derivation R A M)
  statement: ⇑(D1 - D2) = D1 - D2
  proof: rfl

@[simp]

中文:
定理 coe_sub
  条件: (D1 D2 : 导子 R A M)
  结论: ⇑(D1 - D2) = D1 - D2
  证明: rfl

@[simp]
-/
theorem coe_sub (D1 D2 : Derivation R A M) : ⇑(D1 - D2) = D1 - D2 :=
  rfl

@[simp]
/--
theorem `coe_sub_linearMap` / 定理 `coe_sub_linearMap`

English:
theorem coe_sub_linearMap
  given: (D1 D2 : Derivation R A M)
  statement: ↑(D1 - D2) = (D1 - D2 : A ->ₗ[R] M)
  proof: rfl

中文:
定理 coe_sub_linearMap
  条件: (D1 D2 : 导子 R A M)
  结论: ↑(D1 - D2) = (D1 - D2 : A ->ₗ[R] M)
  证明: rfl
-/
theorem coe_sub_linearMap (D1 D2 : Derivation R A M) : ↑(D1 - D2) = (D1 - D2 : A ->ₗ[R] M) :=
  rfl

/--
theorem `sub_apply` / 定理 `sub_apply`

English:
theorem sub_apply
  statement: (D1 - D2) a = D1 a - D2 a
  proof: rfl

中文:
定理 sub_apply
  结论: (D1 - D2) a = D1 a - D2 a
  证明: rfl
-/
theorem sub_apply : (D1 - D2) a = D1 a - D2 a :=
  rfl

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: AddCommGroup (Derivation R A M)
  body: coe_injective.addCommGroup _ coe_zero coe_add coe_neg coe_sub (fun _ _ => rfl) fun _ _ => rfl

中文:
实例 :
  签名: 加法交换群 (导子 R A M)
  定义体: coe_injective.addCommGroup _ coe_zero coe_add coe_neg coe_sub (fun _ _ => rfl) fun _ _ => rfl

Depends on / 依赖: addCommGroup, coe_add, coe_injective, coe_injective.addCommGroup, coe_neg, coe_sub, coe_zero
-/
instance : AddCommGroup (Derivation R A M) :=
  coe_injective.addCommGroup _ coe_zero coe_add coe_neg coe_sub (fun _ _ => rfl) fun _ _ => rfl

end

end

end Derivation
