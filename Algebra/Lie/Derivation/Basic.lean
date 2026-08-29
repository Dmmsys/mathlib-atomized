/-
Copyright (c) 2024 Frédéric Marbach. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frédéric Marbach
-/
module

public import Mathlib.Algebra.Lie.NonUnitalNonAssocAlgebra
public import Mathlib.Algebra.Lie.OfAssociative
public import Mathlib.Algebra.Lie.Subalgebra
public import Mathlib.RingTheory.Nilpotent.Exp
public import Mathlib.RingTheory.Noetherian.Basic

/-!
# Lie derivations

This file defines *Lie derivations* and establishes some basic properties.

## Main definitions

- `LieDerivation`: A Lie derivation `D` from the Lie `R`-algebra `L` to the `L`-module `M` is an
  `R`-linear map that satisfies the Leibniz rule `D [a, b] = [a, D b] - [b, D a]`.
- `LieDerivation.inner`: The natural map from a Lie module to the derivations taking values in it.

## Main statements

- `LieDerivation.eqOn_lieSpan`: two Lie derivations equal on a set are equal on its Lie span.
- `LieDerivation.instLieAlgebra`: the set of Lie derivations from a Lie algebra to itself is a Lie
  algebra.

## Implementation notes

- Mathematically, a Lie derivation is just a derivation on a Lie algebra. However, the current
  implementation of `RingTheory.Derivation` requires a commutative associative algebra, so is
  incompatible with the setting of Lie algebras. Initially, this file is a copy-pasted adaptation of
  the `RingTheory.Derivation.Basic.lean` file.
- Since we don't have right actions of Lie algebras, the second term in the Leibniz rule is written
  as `- [b, D a]`. Within Lie algebras, skew symmetry restores the expected definition `[D a, b]`.
-/

@[expose] public section

/--
Definition of `LieDerivation` / `LieDerivation` 的定义

English:
structure LieDerivation
  parameters: (R L M : Type*) [CommRing R] [LieRing L] [LieAlgebra R L]
  extends: L ->ₗ[R] M
  axioms and operations (1):
    - leibniz'((a b : L)) : toLinearMap ⁅a, b⁆ = ⁅a, toLinearMap b⁆ - ⁅b, toLinearMap a⁆

中文:
结构 LieDerivation
  参数: (R L M : 类型) [交换环 R] [Lie环 L] [Lie代数 R L]
  继承: L ->ₗ[R] M
  公理与运算 (1 个):
    - leibniz'((a b : L)) : toLinearMap ⁅a, b⁆ = ⁅a, toLinearMap b⁆ - ⁅b, toLinearMap a⁆
-/
structure LieDerivation (R L M : Type*) [CommRing R] [LieRing L] [LieAlgebra R L]
    [AddCommGroup M] [Module R M] [LieRingModule L M] [LieModule R L M]
    extends L ->ₗ[R] M where
  protected leibniz' (a b : L) : toLinearMap ⁅a, b⁆ = ⁅a, toLinearMap b⁆ - ⁅b, toLinearMap a⁆

/-- The `LinearMap` underlying a `LieDerivation`. -/
add_decl_doc LieDerivation.toLinearMap

namespace LieDerivation

section

variable {R L M : Type*} [CommRing R] [LieRing L] [LieAlgebra R L]
    [AddCommGroup M] [Module R M] [LieRingModule L M] [LieModule R L M]

variable (D : LieDerivation R L M) {D1 D2 : LieDerivation R L M} (a b : L)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: FunLike (LieDerivation R L M) L M
  body: D.toFun
  coe_injective D1 D2 h := by cases D1; cases D2; congr; exact DFunLike.coe_injective h

中文:
实例 :
  签名: 函数状 (LieDerivation R L M) L M
  定义体: D.toFun
  coe_injective D1 D2 h := by cases D1; cases D2; congr; exact DFunLike.coe_injective h

Depends on / 依赖: D.toFun
-/
instance : FunLike (LieDerivation R L M) L M where
  coe D := D.toFun
  coe_injective D1 D2 h := by cases D1; cases D2; congr; exact DFunLike.coe_injective h

/--
Instance `instLinearMapClass` / 实例 `instLinearMapClass`

English:
instance instLinearMapClass
  signature: : LinearMapClass (LieDerivation R L M) R L M where
  body: D.toLinearMap.map_add'
  map_smulₛₗ D := D.toLinearMap.map_smul

中文:
实例 instLinearMapClass
  签名: : 线性映射类 (LieDerivation R L M) R L M where
  定义体: D.toLinearMap.map_add'
  map_smulₛₗ D := D.toLinearMap.map_smul

Depends on / 依赖: D.toLinearMap.map_add, map_add, toLinearMap
-/
instance instLinearMapClass : LinearMapClass (LieDerivation R L M) R L M where
  map_add D := D.toLinearMap.map_add'
  map_smulₛₗ D := D.toLinearMap.map_smul

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
theorem toFun_eq_coe : D.toFun = ⇑D := rfl

/--
Definition of `Simps.apply` / `Simps.apply` 的定义

English:
definition Simps.apply
  signature: (D : LieDerivation R L M)
  body: D

initialize_simps_projections LieDerivation (toFun -> apply)

中文:
定义 Simps.apply
  签名: (D : LieDerivation R L M)
  定义体: D

initialize_simps_projections LieDerivation (toFun -> apply)
-/
def Simps.apply (D : LieDerivation R L M) : L -> M := D

initialize_simps_projections LieDerivation (toFun -> apply)

attribute [coe] toLinearMap

/--
Instance `instCoeToLinearMap` / 实例 `instCoeToLinearMap`

English:
instance instCoeToLinearMap
  signature: : Coe (LieDerivation R L M) (L ->ₗ[R] M)
  body: ⟨fun D => D.toLinearMap⟩

@[simp]

中文:
实例 instCoeToLinearMap
  签名: : Coe (LieDerivation R L M) (L ->ₗ[R] M)
  定义体: ⟨fun D => D.toLinearMap⟩

@[simp]

Depends on / 依赖: D.toLinearMap, toLinearMap
-/
instance instCoeToLinearMap : Coe (LieDerivation R L M) (L ->ₗ[R] M) :=
  ⟨fun D => D.toLinearMap⟩

@[simp]
/--
theorem `mk_coe` / 定理 `mk_coe`

English:
theorem mk_coe
  given: (f : L ->ₗ[R] M) (h₁)
  statement: ((⟨f, h₁⟩ : LieDerivation R L M) : L -> M) = f
  proof: rfl

@[simp, norm_cast]

中文:
定理 mk_coe
  条件: (f : L ->ₗ[R] M) (h₁)
  结论: ((⟨f, h₁⟩ : LieDerivation R L M) : L -> M) = f
  证明: rfl

@[simp, norm_cast]
-/
theorem mk_coe (f : L ->ₗ[R] M) (h₁) : ((⟨f, h₁⟩ : LieDerivation R L M) : L -> M) = f :=
  rfl

@[simp, norm_cast]
/--
theorem `coeFn_coe` / 定理 `coeFn_coe`

English:
theorem coeFn_coe
  given: (f : LieDerivation R L M)
  statement: ⇑(f : L ->ₗ[R] M) = f
  proof: rfl

中文:
定理 coeFn_coe
  条件: (f : LieDerivation R L M)
  结论: ⇑(f : L ->ₗ[R] M) = f
  证明: rfl
-/
theorem coeFn_coe (f : LieDerivation R L M) : ⇑(f : L ->ₗ[R] M) = f :=
  rfl

/--
theorem `coe_injective` / 定理 `coe_injective`

English:
theorem coe_injective
  statement: @Function.Injective (LieDerivation R L M) (L -> M) DFunLike.coe
  proof: DFunLike.coe_injective

@[ext]

中文:
定理 coe_injective
  结论: @函数.单射 (LieDerivation R L M) (L -> M) 依赖函数状.coe
  证明: DFunLike.coe_injective

@[ext]

Depends on / 依赖: DFunLike, DFunLike.coe_injective, coe_injective
-/
theorem coe_injective : @Function.Injective (LieDerivation R L M) (L -> M) DFunLike.coe :=
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
  given: (h : D1 = D2) (a : L)
  statement: D1 a = D2 a
  proof: DFunLike.congr_fun h a

@[simp]

中文:
定理 congr_fun
  条件: (h : D1 = D2) (a : L)
  结论: D1 a = D2 a
  证明: DFunLike.congr_fun h a

@[simp]

Depends on / 依赖: DFunLike, DFunLike.congr_fun, congr_fun
-/
theorem congr_fun (h : D1 = D2) (a : L) : D1 a = D2 a :=
  DFunLike.congr_fun h a

@[simp]
/--
lemma `apply_lie_eq_sub` / 引理 `apply_lie_eq_sub`

English:
lemma apply_lie_eq_sub
  given: (D : LieDerivation R L M) (a b : L)
  proof: D.leibniz' a b

中文:
引理 apply_lie_eq_sub
  条件: (D : LieDerivation R L M) (a b : L)
  证明: D.leibniz' a b

Depends on / 依赖: D.leibniz, leibniz
-/
lemma apply_lie_eq_sub (D : LieDerivation R L M) (a b : L) :
    D ⁅a, b⁆ = ⁅a, D b⁆ - ⁅b, D a⁆ :=
  D.leibniz' a b

/--
lemma `apply_lie_eq_add` / 引理 `apply_lie_eq_add`

English:
lemma apply_lie_eq_add
  given: (D : LieDerivation R L L) (a b : L)
  proof: by
  rw [LieDerivation.apply_lie_eq_sub]; rw [sub_eq_add_neg]; rw [lie_skew]

中文:
引理 apply_lie_eq_add
  条件: (D : LieDerivation R L L) (a b : L)
  证明: by
  rw [LieDerivation.apply_lie_eq_sub]; rw [sub_eq_add_neg]; rw [lie_skew]

Depends on / 依赖: LieDerivation, LieDerivation.apply_lie_eq_sub, apply_lie_eq_sub, lie_skew, sub_eq_add_neg
-/
lemma apply_lie_eq_add (D : LieDerivation R L L) (a b : L) :
    D ⁅a, b⁆ = ⁅a, D b⁆ + ⁅D a, b⁆ := by
  rw [LieDerivation.apply_lie_eq_sub]; rw [sub_eq_add_neg]; rw [lie_skew]

set_option backward.isDefEq.respectTransparency false in
/--
theorem `eqOn_lieSpan` / 定理 `eqOn_lieSpan`

English:
theorem eqOn_lieSpan
  given: {s : Set L} (h : Set.EqOn D1 D2 s)
  proof: by
  intro _ hx
  induction hx using LieSubalgebra.lieSpan_induction with
  | mem x hx => exact h hx
  | zero => simp
  | add x y _ _ hx hy => simp [hx, hy]
  | smul t x _ hx => simp [hx]
  | lie x y _ _ hx hy => simp [hx, hy]

中文:
定理 eqOn_lieSpan
  条件: {s : 集合 L} (h : 集合.EqOn D1 D2 s)
  证明: by
  intro _ hx
  induction hx using LieSubalgebra.lieSpan_induction with
  | mem x hx => exact h hx
  | zero => simp
  | add x y _ _ hx hy => simp [hx, hy]
  | smul t x _ hx => simp [hx]
  | lie x y _ _ hx hy => simp [hx, hy]

Depends on / 依赖: LieSubalgebra, LieSubalgebra.lieSpan_induction, lieSpan_induction
-/
theorem eqOn_lieSpan {s : Set L} (h : Set.EqOn D1 D2 s) :
    Set.EqOn D1 D2 (LieSubalgebra.lieSpan R L s) := by
  intro _ hx
  induction hx using LieSubalgebra.lieSpan_induction with
  | mem x hx => exact h hx
  | zero => simp
  | add x y _ _ hx hy => simp [hx, hy]
  | smul t x _ hx => simp [hx]
  | lie x y _ _ hx hy => simp [hx, hy]

/--
theorem `ext_of_lieSpan_eq_top` / 定理 `ext_of_lieSpan_eq_top`

English:
theorem ext_of_lieSpan_eq_top
  statement: (s : Set L) (hs : LieSubalgebra.lieSpan R L s = ⊤)
  proof: ext fun _ => eqOn_lieSpan h hs.symm ▸ trivial

中文:
定理 ext_of_lieSpan_eq_top
  结论: (s : 集合 L) (hs : Lie子代数.lieSpan R L s = ⊤)
  证明: ext fun _ => eqOn_lieSpan h hs.symm ▸ trivial

Depends on / 依赖: eqOn_lieSpan, hs.symm
-/
theorem ext_of_lieSpan_eq_top (s : Set L) (hs : LieSubalgebra.lieSpan R L s = ⊤)
    (h : Set.EqOn D1 D2 s) : D1 = D2 :=
ext fun _ => eqOn_lieSpan h hs.symm ▸ trivial

section

open Finset Nat

/--
theorem `iterate_apply_lie` / 定理 `iterate_apply_lie`

English:
theorem iterate_apply_lie
  given: (D : LieDerivation R L L) (n : Nat) (a b : L)
  proof: by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [sum_antidiagonal_choose_succ_nsmul (M := L) (fun i j => ⁅D^[i] a, D^[j] b⁆) n]
    simp only [Function.iterate_succ_apply', ih, map_sum, map_nsmul, apply_lie_eq_add, smul_add,
      sum_add_distrib, add_right_inj]
    refine sum_congr r

中文:
定理 iterate_apply_lie
  条件: (D : LieDerivation R L L) (n : 自然数) (a b : L)
  证明: by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [sum_antidiagonal_choose_succ_nsmul (M := L) (fun i j => ⁅D^[i] a, D^[j] b⁆) n]
    simp only [Function.iterate_succ_apply', ih, map_sum, map_nsmul, apply_lie_eq_add, smul_add,
      sum_add_distrib, add_right_inj]
    refine sum_congr r

Depends on / 依赖: Function, Function.iterate_succ_apply, add_right_inj, apply_lie_eq_add, choose_symm_of_eq_add, iterate_succ_apply, map_nsmul, map_sum, mem_antidiagonal, n.choose_symm_of_eq_add, smul_add, sum_add_distrib, sum_antidiagonal_choose_succ_nsmul, sum_congr
-/
theorem iterate_apply_lie (D : LieDerivation R L L) (n : Nat) (a b : L) :
    D^[n] ⁅a, b⁆ = ∑ ij in antidiagonal n, choose n ij.1 • ⁅D^[ij.1] a, D^[ij.2] b⁆ := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [sum_antidiagonal_choose_succ_nsmul (M := L) (fun i j => ⁅D^[i] a, D^[j] b⁆) n]
    simp only [Function.iterate_succ_apply', ih, map_sum, map_nsmul, apply_lie_eq_add, smul_add,
      sum_add_distrib, add_right_inj]
    refine sum_congr rfl fun ⟨i, j⟩ hij => ?_
    rw [n.choose_symm_of_eq_add (mem_antidiagonal.1 hij).symm]

/--
theorem `iterate_apply_lie'` / 定理 `iterate_apply_lie'`

English:
theorem iterate_apply_lie'
  given: (D : LieDerivation R L L) (n : Nat) (a b : L)
  proof: by
  rw [iterate_apply_lie D n a b]
  exact sum_antidiagonal_eq_sum_range_succ (fun i j => n.choose i • ⁅D^[i] a, D^[j] b⁆) n

中文:
定理 iterate_apply_lie'
  条件: (D : LieDerivation R L L) (n : 自然数) (a b : L)
  证明: by
  rw [iterate_apply_lie D n a b]
  exact sum_antidiagonal_eq_sum_range_succ (fun i j => n.choose i • ⁅D^[i] a, D^[j] b⁆) n

Depends on / 依赖: iterate_apply_lie, n.choose, sum_antidiagonal_eq_sum_range_succ
-/
theorem iterate_apply_lie' (D : LieDerivation R L L) (n : Nat) (a b : L) :
    D^[n] ⁅a, b⁆ = ∑ i in range (n + 1), n.choose i • ⁅D^[i] a, D^[n - i] b⁆ := by
  rw [iterate_apply_lie D n a b]
  exact sum_antidiagonal_eq_sum_range_succ (fun i j => n.choose i • ⁅D^[i] a, D^[j] b⁆) n

end

/--
Instance `instZero` / 实例 `instZero`

English:
instance instZero
  signature: : Zero (LieDerivation R L M) where
  body: { toLinearMap := 0
      leibniz' := fun a b => by simp only [LinearMap.zero_apply, lie_zero, sub_self] }

@[simp]

中文:
实例 instZero
  签名: : 零 (LieDerivation R L M) where
  定义体: { toLinearMap := 0
      leibniz' := fun a b => by simp only [LinearMap.zero_apply, lie_zero, sub_self] }

@[simp]

Depends on / 依赖: LinearMap, LinearMap.zero_apply, leibniz, lie_zero, sub_self, toLinearMap, zero_apply
-/
instance instZero : Zero (LieDerivation R L M) where
  zero :=
    { toLinearMap := 0
      leibniz' := fun a b => by simp only [LinearMap.zero_apply, lie_zero, sub_self] }

@[simp]
/--
theorem `coe_zero` / 定理 `coe_zero`

English:
theorem coe_zero
  statement: ⇑(0 : LieDerivation R L M) = 0
  proof: rfl

@[simp]

中文:
定理 coe_zero
  结论: ⇑(0 : LieDerivation R L M) = 0
  证明: rfl

@[simp]
-/
theorem coe_zero : ⇑(0 : LieDerivation R L M) = 0 :=
  rfl

@[simp]
/--
theorem `coe_zero_linearMap` / 定理 `coe_zero_linearMap`

English:
theorem coe_zero_linearMap
  statement: ↑(0 : LieDerivation R L M) = (0 : L ->ₗ[R] M)
  proof: rfl

中文:
定理 coe_zero_linearMap
  结论: ↑(0 : LieDerivation R L M) = (0 : L ->ₗ[R] M)
  证明: rfl
-/
theorem coe_zero_linearMap : ↑(0 : LieDerivation R L M) = (0 : L ->ₗ[R] M) :=
  rfl

/--
theorem `zero_apply` / 定理 `zero_apply`

English:
theorem zero_apply
  given: (a : L)
  statement: (0 : LieDerivation R L M) a = 0
  proof: rfl

中文:
定理 zero_apply
  条件: (a : L)
  结论: (0 : LieDerivation R L M) a = 0
  证明: rfl
-/
theorem zero_apply (a : L) : (0 : LieDerivation R L M) a = 0 :=
  rfl

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Inhabited (LieDerivation R L M)
  body: ⟨0⟩

中文:
实例 :
  签名: 可居 (LieDerivation R L M)
  定义体: ⟨0⟩
-/
instance : Inhabited (LieDerivation R L M) :=
  ⟨0⟩

/--
Instance `instAdd` / 实例 `instAdd`

English:
instance instAdd
  signature: : Add (LieDerivation R L M) where
  body: { toLinearMap := D1 + D2
      leibniz' := fun a b => by
        simp only [LinearMap.add_apply, coeFn_coe, apply_lie_eq_sub, lie_add, add_sub_add_comm] }

@[simp]

中文:
实例 instAdd
  签名: : 加法 (LieDerivation R L M) where
  定义体: { toLinearMap := D1 + D2
      leibniz' := fun a b => by
        simp only [LinearMap.add_apply, coeFn_coe, apply_lie_eq_sub, lie_add, add_sub_add_comm] }

@[simp]

Depends on / 依赖: LinearMap, LinearMap.add_apply, add_apply, add_sub_add_comm, apply_lie_eq_sub, coeFn_coe, leibniz, lie_add, toLinearMap
-/
instance instAdd : Add (LieDerivation R L M) where
  add D1 D2 :=
    { toLinearMap := D1 + D2
      leibniz' := fun a b => by
        simp only [LinearMap.add_apply, coeFn_coe, apply_lie_eq_sub, lie_add, add_sub_add_comm] }

@[simp]
/--
theorem `coe_add` / 定理 `coe_add`

English:
theorem coe_add
  given: (D1 D2 : LieDerivation R L M)
  statement: ⇑(D1 + D2) = D1 + D2
  proof: rfl

@[simp]

中文:
定理 coe_add
  条件: (D1 D2 : LieDerivation R L M)
  结论: ⇑(D1 + D2) = D1 + D2
  证明: rfl

@[simp]
-/
theorem coe_add (D1 D2 : LieDerivation R L M) : ⇑(D1 + D2) = D1 + D2 :=
  rfl

@[simp]
/--
theorem `coe_add_linearMap` / 定理 `coe_add_linearMap`

English:
theorem coe_add_linearMap
  given: (D1 D2 : LieDerivation R L M)
  statement: ↑(D1 + D2) = (D1 + D2 : L ->ₗ[R] M)
  proof: rfl

中文:
定理 coe_add_linearMap
  条件: (D1 D2 : LieDerivation R L M)
  结论: ↑(D1 + D2) = (D1 + D2 : L ->ₗ[R] M)
  证明: rfl
-/
theorem coe_add_linearMap (D1 D2 : LieDerivation R L M) : ↑(D1 + D2) = (D1 + D2 : L ->ₗ[R] M) :=
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

中文:
定理 map_sub
  结论: D (a - b) = D a - D b
  证明: map_sub D a b
-/
protected theorem map_sub : D (a - b) = D a - D b :=
  map_sub D a b

/--
Instance `instNeg` / 实例 `instNeg`

English:
instance instNeg
  signature: : Neg (LieDerivation R L M)
  body: ⟨fun D =>
    mk (-D) fun a b => by
      simp only [LinearMap.neg_apply, coeFn_coe, apply_lie_eq_sub,
        neg_sub, lie_neg, sub_neg_eq_add, add_comm, ← sub_eq_add_neg] ⟩

@[simp]

中文:
实例 instNeg
  签名: : 取负 (LieDerivation R L M)
  定义体: ⟨fun D =>
    mk (-D) fun a b => by
      simp only [LinearMap.neg_apply, coeFn_coe, apply_lie_eq_sub,
        neg_sub, lie_neg, sub_neg_eq_add, add_comm, ← sub_eq_add_neg] ⟩

@[simp]

Depends on / 依赖: LinearMap, LinearMap.neg_apply, add_comm, apply_lie_eq_sub, coeFn_coe, lie_neg, neg_apply, neg_sub, sub_eq_add_neg, sub_neg_eq_add
-/
instance instNeg : Neg (LieDerivation R L M) :=
  ⟨fun D =>
    mk (-D) fun a b => by
      simp only [LinearMap.neg_apply, coeFn_coe, apply_lie_eq_sub,
        neg_sub, lie_neg, sub_neg_eq_add, add_comm, ← sub_eq_add_neg] ⟩

@[simp]
/--
theorem `coe_neg` / 定理 `coe_neg`

English:
theorem coe_neg
  given: (D : LieDerivation R L M)
  statement: ⇑(-D) = -D
  proof: rfl

@[simp]

中文:
定理 coe_neg
  条件: (D : LieDerivation R L M)
  结论: ⇑(-D) = -D
  证明: rfl

@[simp]
-/
theorem coe_neg (D : LieDerivation R L M) : ⇑(-D) = -D :=
  rfl

@[simp]
/--
theorem `coe_neg_linearMap` / 定理 `coe_neg_linearMap`

English:
theorem coe_neg_linearMap
  given: (D : LieDerivation R L M)
  statement: ↑(-D) = (-D : L ->ₗ[R] M)
  proof: rfl

中文:
定理 coe_neg_linearMap
  条件: (D : LieDerivation R L M)
  结论: ↑(-D) = (-D : L ->ₗ[R] M)
  证明: rfl
-/
theorem coe_neg_linearMap (D : LieDerivation R L M) : ↑(-D) = (-D : L ->ₗ[R] M) :=
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
Instance `instSub` / 实例 `instSub`

English:
instance instSub
  signature: : Sub (LieDerivation R L M)
  body: ⟨fun D1 D2 =>
    mk (D1 - D2 : L ->ₗ[R] M) fun a b => by
      simp only [LinearMap.sub_apply, coeFn_coe, apply_lie_eq_sub, lie_sub, sub_sub_sub_comm]⟩

@[simp]

中文:
实例 instSub
  签名: : 减法 (LieDerivation R L M)
  定义体: ⟨fun D1 D2 =>
    mk (D1 - D2 : L ->ₗ[R] M) fun a b => by
      simp only [LinearMap.sub_apply, coeFn_coe, apply_lie_eq_sub, lie_sub, sub_sub_sub_comm]⟩

@[simp]

Depends on / 依赖: LinearMap, LinearMap.sub_apply, apply_lie_eq_sub, coeFn_coe, lie_sub, sub_apply, sub_sub_sub_comm
-/
instance instSub : Sub (LieDerivation R L M) :=
  ⟨fun D1 D2 =>
    mk (D1 - D2 : L ->ₗ[R] M) fun a b => by
      simp only [LinearMap.sub_apply, coeFn_coe, apply_lie_eq_sub, lie_sub, sub_sub_sub_comm]⟩

@[simp]
/--
theorem `coe_sub` / 定理 `coe_sub`

English:
theorem coe_sub
  given: (D1 D2 : LieDerivation R L M)
  statement: ⇑(D1 - D2) = D1 - D2
  proof: rfl

@[simp]

中文:
定理 coe_sub
  条件: (D1 D2 : LieDerivation R L M)
  结论: ⇑(D1 - D2) = D1 - D2
  证明: rfl

@[simp]
-/
theorem coe_sub (D1 D2 : LieDerivation R L M) : ⇑(D1 - D2) = D1 - D2 :=
  rfl

@[simp]
/--
theorem `coe_sub_linearMap` / 定理 `coe_sub_linearMap`

English:
theorem coe_sub_linearMap
  given: (D1 D2 : LieDerivation R L M)
  statement: ↑(D1 - D2) = (D1 - D2 : L ->ₗ[R] M)
  proof: rfl

中文:
定理 coe_sub_linearMap
  条件: (D1 D2 : LieDerivation R L M)
  结论: ↑(D1 - D2) = (D1 - D2 : L ->ₗ[R] M)
  证明: rfl
-/
theorem coe_sub_linearMap (D1 D2 : LieDerivation R L M) : ↑(D1 - D2) = (D1 - D2 : L ->ₗ[R] M) :=
  rfl

/--
theorem `sub_apply` / 定理 `sub_apply`

English:
theorem sub_apply
  given: {D1 D2 : LieDerivation R L M}
  statement: (D1 - D2) a = D1 a - D2 a
  proof: rfl

中文:
定理 sub_apply
  条件: {D1 D2 : LieDerivation R L M}
  结论: (D1 - D2) a = D1 a - D2 a
  证明: rfl
-/
theorem sub_apply {D1 D2 : LieDerivation R L M} : (D1 - D2) a = D1 a - D2 a :=
  rfl

section Scalar

/--
Definition of `SMulBracketCommClass` / `SMulBracketCommClass` 的定义

English:
class SMulBracketCommClass
  parameters: (S L α : Type*) [SMul S α] [LieRing L] [AddCommGroup α]
  axioms and operations (1):
    - smul_bracket_comm : forall (s : S) (l : L) (a : α), s • ⁅l, a⁆ = ⁅l, s • a⁆

中文:
类 SMulBracketComm类
  参数: (S L α : 类型) [标量乘法 S α] [Lie环 L] [加法交换群 α]
  公理与运算 (1 个):
    - smul_bracket_comm : 对任意 (s : S) (l : L) (a : α), s • ⁅l, a⁆ = ⁅l, s • a⁆
-/
class SMulBracketCommClass (S L α : Type*) [SMul S α] [LieRing L] [AddCommGroup α]
    [LieRingModule L α] : Prop where
  /-- `•` and `⁅⬝, ⬝⁆` are left commutative -/
  smul_bracket_comm : forall (s : S) (l : L) (a : α), s • ⁅l, a⁆ = ⁅l, s • a⁆

variable {S T : Type*}
variable [Monoid S] [DistribMulAction S M] [SMulCommClass R S M] [SMulBracketCommClass S L M]
variable [Monoid T] [DistribMulAction T M] [SMulCommClass R T M] [SMulBracketCommClass T L M]

/--
Instance `instSMul` / 实例 `instSMul`

English:
instance instSMul
  signature: : SMul S (LieDerivation R L M) where
  body: { toLinearMap := r • D
      leibniz' := fun a b => by simp only [LinearMap.smul_apply, coeFn_coe, apply_lie_eq_sub,
        smul_sub, SMulBracketCommClass.smul_bracket_comm] }

@[simp]

中文:
实例 instSMul
  签名: : 标量乘法 S (LieDerivation R L M) where
  定义体: { toLinearMap := r • D
      leibniz' := fun a b => by simp only [LinearMap.smul_apply, coeFn_coe, apply_lie_eq_sub,
        smul_sub, SMulBracketCommClass.smul_bracket_comm] }

@[simp]

Depends on / 依赖: LinearMap, LinearMap.smul_apply, SMulBracketCommClass, SMulBracketCommClass.smul_bracket_comm, apply_lie_eq_sub, coeFn_coe, leibniz, smul_apply, smul_bracket_comm, smul_sub, toLinearMap
-/
instance instSMul : SMul S (LieDerivation R L M) where
  smul r D :=
    { toLinearMap := r • D
      leibniz' := fun a b => by simp only [LinearMap.smul_apply, coeFn_coe, apply_lie_eq_sub,
        smul_sub, SMulBracketCommClass.smul_bracket_comm] }

@[simp]
/--
theorem `coe_smul` / 定理 `coe_smul`

English:
theorem coe_smul
  given: (r : S) (D : LieDerivation R L M)
  statement: ⇑(r • D) = r • ⇑D
  proof: rfl

@[simp]

中文:
定理 coe_smul
  条件: (r : S) (D : LieDerivation R L M)
  结论: ⇑(r • D) = r • ⇑D
  证明: rfl

@[simp]
-/
theorem coe_smul (r : S) (D : LieDerivation R L M) : ⇑(r • D) = r • ⇑D :=
  rfl

@[simp]
/--
theorem `coe_smul_linearMap` / 定理 `coe_smul_linearMap`

English:
theorem coe_smul_linearMap
  given: (r : S) (D : LieDerivation R L M)
  statement: ↑(r • D) = r • (D : L ->ₗ[R] M)
  proof: rfl

中文:
定理 coe_smul_linearMap
  条件: (r : S) (D : LieDerivation R L M)
  结论: ↑(r • D) = r • (D : L ->ₗ[R] M)
  证明: rfl
-/
theorem coe_smul_linearMap (r : S) (D : LieDerivation R L M) : ↑(r • D) = r • (D : L ->ₗ[R] M) :=
  rfl

/--
theorem `smul_apply` / 定理 `smul_apply`

English:
theorem smul_apply
  given: (r : S) (D : LieDerivation R L M)
  statement: (r • D) a = r • D a
  proof: rfl

中文:
定理 smul_apply
  条件: (r : S) (D : LieDerivation R L M)
  结论: (r • D) a = r • D a
  证明: rfl
-/
theorem smul_apply (r : S) (D : LieDerivation R L M) : (r • D) a = r • D a :=
  rfl

/--
Instance `instSMulBase` / 实例 `instSMulBase`

English:
instance instSMulBase
  signature: : SMulBracketCommClass R L M
  body: ⟨fun s l a => (lie_smul s l a).symm⟩

中文:
实例 instSMulBase
  签名: : SMulBracketComm类 R L M
  定义体: ⟨fun s l a => (lie_smul s l a).symm⟩

Depends on / 依赖: lie_smul
-/
instance instSMulBase : SMulBracketCommClass R L M := ⟨fun s l a => (lie_smul s l a).symm⟩

/--
Instance `instSMulNat` / 实例 `instSMulNat`

English:
instance instSMulNat
  signature: : SMulBracketCommClass Nat L M
  body: ⟨fun s l a => (lie_nsmul l a s).symm⟩

中文:
实例 instSMul自然数
  签名: : SMulBracketComm类 自然数 L M
  定义体: ⟨fun s l a => (lie_nsmul l a s).symm⟩

Depends on / 依赖: lie_nsmul
-/
instance instSMulNat : SMulBracketCommClass Nat L M := ⟨fun s l a => (lie_nsmul l a s).symm⟩

/--
Instance `instSMulInt` / 实例 `instSMulInt`

English:
instance instSMulInt
  signature: : SMulBracketCommClass Int L M
  body: ⟨fun s l a => (lie_zsmul l a s).symm⟩

中文:
实例 instSMul整数
  签名: : SMulBracketComm类 整数 L M
  定义体: ⟨fun s l a => (lie_zsmul l a s).symm⟩

Depends on / 依赖: lie_zsmul
-/
instance instSMulInt : SMulBracketCommClass Int L M := ⟨fun s l a => (lie_zsmul l a s).symm⟩

/--
Instance `instAddCommGroup` / 实例 `instAddCommGroup`

English:
instance instAddCommGroup
  signature: : AddCommGroup (LieDerivation R L M)
  body: coe_injective.addCommGroup _ coe_zero coe_add coe_neg coe_sub (fun _ _ => rfl) fun _ _ => rfl

中文:
实例 instAddCommGroup
  签名: : 加法交换群 (LieDerivation R L M)
  定义体: coe_injective.addCommGroup _ coe_zero coe_add coe_neg coe_sub (fun _ _ => rfl) fun _ _ => rfl

Depends on / 依赖: addCommGroup, coe_add, coe_injective, coe_injective.addCommGroup, coe_neg, coe_sub, coe_zero
-/
instance instAddCommGroup : AddCommGroup (LieDerivation R L M) :=
  coe_injective.addCommGroup _ coe_zero coe_add coe_neg coe_sub (fun _ _ => rfl) fun _ _ => rfl

/--
Definition of `coeFnAddMonoidHom` / `coeFnAddMonoidHom` 的定义

English:
definition coeFnAddMonoidHom
  signature: : LieDerivation R L M ->+ L -> M where
  body: (↑)
  map_zero' := coe_zero
  map_add' := coe_add

@[simp]

中文:
定义 coeFnAddMonoidHom
  签名: : LieDerivation R L M ->+ L -> M where
  定义体: (↑)
  map_zero' := coe_zero
  map_add' := coe_add

@[simp]
-/
def coeFnAddMonoidHom : LieDerivation R L M ->+ L -> M where
  toFun := (↑)
  map_zero' := coe_zero
  map_add' := coe_add

@[simp]
/--
lemma `coeFnAddMonoidHom_apply` / 引理 `coeFnAddMonoidHom_apply`

English:
lemma coeFnAddMonoidHom_apply
  given: (D : LieDerivation R L M)
  statement: coeFnAddMonoidHom D = D
  proof: rfl

中文:
引理 coeFnAddMonoidHom_apply
  条件: (D : LieDerivation R L M)
  结论: coeFnAddMonoidHom D = D
  证明: rfl
-/
lemma coeFnAddMonoidHom_apply (D : LieDerivation R L M) : coeFnAddMonoidHom D = D := rfl

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: DistribMulAction S (LieDerivation R L M)
  body: Function.Injective.distribMulAction coeFnAddMonoidHom coe_injective coe_smul

中文:
实例 :
  签名: 分配乘法作用 S (LieDerivation R L M)
  定义体: Function.Injective.distribMulAction coeFnAddMonoidHom coe_injective coe_smul

Depends on / 依赖: Function, Function.Injective.distribMulAction, Injective, coeFnAddMonoidHom, coe_injective, coe_smul, distribMulAction
-/
instance : DistribMulAction S (LieDerivation R L M) :=
  Function.Injective.distribMulAction coeFnAddMonoidHom coe_injective coe_smul

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [SMul
  signature: S T] [IsScalarTower S T M] : IsScalarTower S T (LieDerivation R L M)
  body: ⟨fun _ _ _ => ext fun _ => smul_assoc _ _ _⟩

中文:
实例 [标量乘法
  签名: S T] [标量塔 S T M] : 标量塔 S T (LieDerivation R L M)
  定义体: ⟨fun _ _ _ => ext fun _ => smul_assoc _ _ _⟩

Depends on / 依赖: smul_assoc
-/
instance [SMul S T] [IsScalarTower S T M] : IsScalarTower S T (LieDerivation R L M) :=
  ⟨fun _ _ _ => ext fun _ => smul_assoc _ _ _⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [SMulCommClass
  signature: S T M] : SMulCommClass S T (LieDerivation R L M)
  body: ⟨fun _ _ _ => ext fun _ => smul_comm _ _ _⟩

中文:
实例 [标量交换类
  签名: S T M] : 标量交换类 S T (LieDerivation R L M)
  定义体: ⟨fun _ _ _ => ext fun _ => smul_comm _ _ _⟩

Depends on / 依赖: smul_comm
-/
instance [SMulCommClass S T M] : SMulCommClass S T (LieDerivation R L M) :=
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
    [SMulBracketCommClass S L M] : Module S (LieDerivation R L M) :=
  Function.Injective.module S coeFnAddMonoidHom coe_injective coe_smul

end

section

variable {R L : Type*} [CommRing R] [LieRing L] [LieAlgebra R L]

/--
Instance `instBracket` / 实例 `instBracket`

English:
instance instBracket
  signature: : Bracket (LieDerivation R L L) (LieDerivation R L L) where
  body: LieDerivation.mk ⁅(D1 : Module.End R L), (D2 : Module.End R L)⁆ (fun a b => by
    simp only [Ring.lie_def, apply_lie_eq_add, coeFn_coe,
      LinearMap.sub_apply, Module.End.mul_apply, map_add, sub_lie, lie_sub, ← lie_skew b]
    abel)

中文:
实例 instBracket
  签名: : Bracket (LieDerivation R L L) (LieDerivation R L L) where
  定义体: LieDerivation.mk ⁅(D1 : Module.End R L), (D2 : Module.End R L)⁆ (fun a b => by
    simp only [Ring.lie_def, apply_lie_eq_add, coeFn_coe,
      LinearMap.sub_apply, Module.End.mul_apply, map_add, sub_lie, lie_sub, ← lie_skew b]
    abel)

Depends on / 依赖: LieDerivation, LieDerivation.mk, LinearMap, LinearMap.sub_apply, Module, Module.End, Module.End.mul_apply, Ring.lie_def, apply_lie_eq_add, coeFn_coe, lie_def, lie_skew, lie_sub, map_add, mul_apply, sub_apply, sub_lie
-/
instance instBracket : Bracket (LieDerivation R L L) (LieDerivation R L L) where
  bracket D1 D2 := LieDerivation.mk ⁅(D1 : Module.End R L), (D2 : Module.End R L)⁆ (fun a b => by
    simp only [Ring.lie_def, apply_lie_eq_add, coeFn_coe,
      LinearMap.sub_apply, Module.End.mul_apply, map_add, sub_lie, lie_sub, ← lie_skew b]
    abel)

variable {D1 D2 : LieDerivation R L L}

@[simp]
/--
lemma `commutator_coe_linear_map` / 引理 `commutator_coe_linear_map`

English:
lemma commutator_coe_linear_map
  statement: ↑⁅D1, D2⁆ = ⁅(D1 : Module.End R L), (D2 : Module.End R L)⁆
  proof: rfl

中文:
引理 commutator_coe_linear_map
  结论: ↑⁅D1, D2⁆ = ⁅(D1 : 模.End R L), (D2 : 模.End R L)⁆
  证明: rfl
-/
lemma commutator_coe_linear_map : ↑⁅D1, D2⁆ = ⁅(D1 : Module.End R L), (D2 : Module.End R L)⁆ :=
  rfl

/--
lemma `commutator_apply` / 引理 `commutator_apply`

English:
lemma commutator_apply
  given: (a : L)
  statement: ⁅D1, D2⁆ a = D1 (D2 a) - D2 (D1 a)
  proof: rfl

中文:
引理 commutator_apply
  条件: (a : L)
  结论: ⁅D1, D2⁆ a = D1 (D2 a) - D2 (D1 a)
  证明: rfl
-/
lemma commutator_apply (a : L) : ⁅D1, D2⁆ a = D1 (D2 a) - D2 (D1 a) :=
  rfl

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: LieRing (LieDerivation R L L)
  body: by
    ext a; simp only [commutator_apply, add_apply, map_add]; abel
  lie_add d e f := by
    ext a; simp only [commutator_apply, add_apply, map_add]; abel
  lie_self d := by
    ext a; simp only [commutator_apply, zero_apply]; abel
  leibniz_lie d e f := by
    ext a; simp only [commutator_apply, 

中文:
实例 :
  签名: Lie环 (LieDerivation R L L)
  定义体: by
    ext a; simp only [commutator_apply, add_apply, map_add]; abel
  lie_add d e f := by
    ext a; simp only [commutator_apply, add_apply, map_add]; abel
  lie_self d := by
    ext a; simp only [commutator_apply, zero_apply]; abel
  leibniz_lie d e f := by
    ext a; simp only [commutator_apply, 

Depends on / 依赖: add_apply, commutator_apply, leibniz_lie, lie_add, lie_self, map_add, map_sub, zero_apply
-/
instance : LieRing (LieDerivation R L L) where
  add_lie d e f := by
    ext a; simp only [commutator_apply, add_apply, map_add]; abel
  lie_add d e f := by
    ext a; simp only [commutator_apply, add_apply, map_add]; abel
  lie_self d := by
    ext a; simp only [commutator_apply, zero_apply]; abel
  leibniz_lie d e f := by
    ext a; simp only [commutator_apply, add_apply, map_sub]; abel

set_option backward.isDefEq.respectTransparency false in
/--
Instance `instLieAlgebra` / 实例 `instLieAlgebra`

English:
instance instLieAlgebra
  signature: : LieAlgebra R (LieDerivation R L L) where
  body: fun r d e => by ext a; simp only [commutator_apply, map_smul, smul_sub, smul_apply]

中文:
实例 instLieAlgebra
  签名: : Lie代数 R (LieDerivation R L L) where
  定义体: fun r d e => by ext a; simp only [commutator_apply, map_smul, smul_sub, smul_apply]

Depends on / 依赖: commutator_apply, map_smul, smul_apply, smul_sub
-/
instance instLieAlgebra : LieAlgebra R (LieDerivation R L L) where
  lie_smul := fun r d e => by ext a; simp only [commutator_apply, map_smul, smul_sub, smul_apply]

/--
lemma `lie_apply` / 引理 `lie_apply`

English:
lemma lie_apply
  given: (D₁ D₂ : LieDerivation R L L) (x : L)
  proof: rfl

中文:
引理 lie_apply
  条件: (D₁ D₂ : LieDerivation R L L) (x : L)
  证明: rfl
-/
@[simp] lemma lie_apply (D₁ D₂ : LieDerivation R L L) (x : L) :
    ⁅D₁, D₂⁆ x = D₁ (D₂ x) - D₂ (D₁ x) :=
  rfl

end

section

variable (R L : Type*) [CommRing R] [LieRing L] [LieAlgebra R L]

attribute [local instance 100] LieRing.ofAssociativeRing

set_option backward.isDefEq.respectTransparency false in
/--
Definition of `toLinearMapLieHom` / `toLinearMapLieHom` 的定义

English:
definition toLinearMapLieHom
  signature: : LieDerivation R L L ->ₗ⁅R⁆ L ->ₗ[R] L where
  body: toLinearMap
  map_add' := by intro D1 D2; dsimp
  map_smul' := by intro D1 D2; dsimp
  map_lie' := by intro D1 D2; dsimp

中文:
定义 toLinearMapLieHom
  签名: : LieDerivation R L L ->ₗ⁅R⁆ L ->ₗ[R] L where
  定义体: toLinearMap
  map_add' := by intro D1 D2; dsimp
  map_smul' := by intro D1 D2; dsimp
  map_lie' := by intro D1 D2; dsimp

Depends on / 依赖: toLinearMap
-/
def toLinearMapLieHom : LieDerivation R L L ->ₗ⁅R⁆ L ->ₗ[R] L where
  toFun := toLinearMap
  map_add' := by intro D1 D2; dsimp
  map_smul' := by intro D1 D2; dsimp
  map_lie' := by intro D1 D2; dsimp

/--
lemma `toLinearMapLieHom_injective` / 引理 `toLinearMapLieHom_injective`

English:
lemma toLinearMapLieHom_injective
  statement: Function.Injective (toLinearMapLieHom R L)
  proof: fun _ _ h => ext fun a => congrFun (congrArg DFunLike.coe h) a

中文:
引理 toLinearMapLieHom_injective
  结论: 函数.单射 (toLinearMapLieHom R L)
  证明: fun _ _ h => ext fun a => congrFun (congrArg DFunLike.coe h) a

Depends on / 依赖: DFunLike, DFunLike.coe
-/
lemma toLinearMapLieHom_injective : Function.Injective (toLinearMapLieHom R L) :=
  fun _ _ h => ext fun a => congrFun (congrArg DFunLike.coe h) a

set_option backward.isDefEq.respectTransparency false in
/--
Instance `instNoetherian` / 实例 `instNoetherian`

English:
instance instNoetherian
  signature: [IsNoetherian R L]
  body: isNoetherian_of_linearEquiv (LinearEquiv.ofInjective _ (toLinearMapLieHom_injective R L)).symm

中文:
实例 instNoetherian
  签名: [是Noether R L]
  定义体: isNoetherian_of_linearEquiv (LinearEquiv.ofInjective _ (toLinearMapLieHom_injective R L)).symm

Depends on / 依赖: LinearEquiv, LinearEquiv.ofInjective, isNoetherian_of_linearEquiv, ofInjective, toLinearMapLieHom_injective
-/
instance instNoetherian [IsNoetherian R L] : IsNoetherian R (LieDerivation R L L) :=
  isNoetherian_of_linearEquiv (LinearEquiv.ofInjective _ (toLinearMapLieHom_injective R L)).symm

end

section Inner

variable (R L M : Type*) [CommRing R] [LieRing L] [LieAlgebra R L]
    [AddCommGroup M] [Module R M] [LieRingModule L M] [LieModule R L M]

set_option backward.isDefEq.respectTransparency false in
/-- The natural map from a Lie module to the derivations taking values in it. -/
@[simps!]
/--
Definition of `inner` / `inner` 的定义

English:
definition inner
  signature: : M ->ₗ[R] LieDerivation R L M where
  body: { __ := (LieModule.toEnd R L M : L ->ₗ[R] Module.End R M).flip m
      leibniz' := by simp }
  map_add' m n := by ext; simp
  map_smul' t m := by ext; simp

中文:
定义 inner
  签名: : M ->ₗ[R] LieDerivation R L M where
  定义体: { __ := (LieModule.toEnd R L M : L ->ₗ[R] Module.End R M).flip m
      leibniz' := by simp }
  map_add' m n := by ext; simp
  map_smul' t m := by ext; simp

Depends on / 依赖: LieModule, LieModule.toEnd, Module, Module.End, leibniz, map_add, map_smul
-/
def inner : M ->ₗ[R] LieDerivation R L M where
  toFun m :=
    { __ := (LieModule.toEnd R L M : L ->ₗ[R] Module.End R M).flip m
      leibniz' := by simp }
  map_add' m n := by ext; simp
  map_smul' t m := by ext; simp

/--
Instance `instLieRingModule` / 实例 `instLieRingModule`

English:
instance instLieRingModule
  signature: : LieRingModule L (LieDerivation R L M) where
  body: inner R L M (D x)
  add_lie x y D := by simp
  lie_add x D₁ D₂ := by simp
  leibniz_lie x y D := by simp

中文:
实例 instLieRingModule
  签名: : Lie环模 L (LieDerivation R L M) where
  定义体: inner R L M (D x)
  add_lie x y D := by simp
  lie_add x D₁ D₂ := by simp
  leibniz_lie x y D := by simp
-/
instance instLieRingModule : LieRingModule L (LieDerivation R L M) where
  bracket x D := inner R L M (D x)
  add_lie x y D := by simp
  lie_add x D₁ D₂ := by simp
  leibniz_lie x y D := by simp

/--
lemma `lie_lieDerivation_apply` / 引理 `lie_lieDerivation_apply`

English:
lemma lie_lieDerivation_apply
  given: (x y : L) (D : LieDerivation R L M)
  proof: rfl

中文:
引理 lie_lieDerivation_apply
  条件: (x y : L) (D : LieDerivation R L M)
  证明: rfl
-/
@[simp] lemma lie_lieDerivation_apply (x y : L) (D : LieDerivation R L M) :
    ⁅x, D⁆ y = ⁅y, D x⁆ :=
  rfl

/--
lemma `lie_coe_lieDerivation_apply` / 引理 `lie_coe_lieDerivation_apply`

English:
lemma lie_coe_lieDerivation_apply
  given: (x : L) (D : LieDerivation R L M)
  proof: by
  ext; simp

中文:
引理 lie_coe_lieDerivation_apply
  条件: (x : L) (D : LieDerivation R L M)
  证明: by
  ext; simp
-/
@[simp] lemma lie_coe_lieDerivation_apply (x : L) (D : LieDerivation R L M) :
    ⁅x, (D : L ->ₗ[R] M)⁆ = ⁅x, D⁆ := by
  ext; simp

set_option backward.isDefEq.respectTransparency false in
/--
Instance `instLieModule` / 实例 `instLieModule`

English:
instance instLieModule
  signature: : LieModule R L (LieDerivation R L M) where
  body: by ext; simp
  lie_smul t x D := by ext; simp

中文:
实例 instLieModule
  签名: : Lie模 R L (LieDerivation R L M) where
  定义体: by ext; simp
  lie_smul t x D := by ext; simp

Depends on / 依赖: lie_smul
-/
instance instLieModule : LieModule R L (LieDerivation R L M) where
  smul_lie t x D := by ext; simp
  lie_smul t x D := by ext; simp

/--
lemma `leibniz_lie` / 引理 `leibniz_lie`

English:
lemma leibniz_lie
  given: (x : L) (D₁ D₂ : LieDerivation R L L)
  proof: by
  ext y
  simp [-lie_skew, ← lie_skew (D₁ x) (D₂ y), ← lie_skew (D₂ x) (D₁ y), sub_eq_neg_add]

中文:
引理 leibniz_lie
  条件: (x : L) (D₁ D₂ : LieDerivation R L L)
  证明: by
  ext y
  simp [-lie_skew, ← lie_skew (D₁ x) (D₂ y), ← lie_skew (D₂ x) (D₁ y), sub_eq_neg_add]
-/
protected lemma leibniz_lie (x : L) (D₁ D₂ : LieDerivation R L L) :
    ⁅x, ⁅D₁, D₂⁆⁆ = ⁅⁅x, D₁⁆, D₂⁆ + ⁅D₁, ⁅x, D₂⁆⁆ := by
  ext y
  simp [-lie_skew, ← lie_skew (D₁ x) (D₂ y), ← lie_skew (D₂ x) (D₁ y), sub_eq_neg_add]

end Inner

section ExpNilpotent

variable {R L : Type*} [CommRing R] [LieRing L] [LieAlgebra R L] [LieAlgebra Rat L]
  (D : LieDerivation R L L)

/--
Definition of `exp` / `exp` 的定义

English:
definition exp
  signature: (h : IsNilpotent D.toLinearMap)
  body: { toLinearMap := IsNilpotent.exp D.toLinearMap
    map_lie' := by
      let _i := LieRing.toNonUnitalNonAssocRing L
      have : SMulCommClass R L L := LieAlgebra.smulCommClass R L
      have : IsScalarTower R L L := LieAlgebra.isScalarTower R L
      exact Module.End.exp_mul_of_derivation R L D.toL

中文:
定义 exp
  签名: (h : 是幂零 D.toLinearMap)
  定义体: { toLinearMap := IsNilpotent.exp D.toLinearMap
    map_lie' := by
      let _i := LieRing.toNonUnitalNonAssocRing L
      have : SMulCommClass R L L := LieAlgebra.smulCommClass R L
      have : IsScalarTower R L L := LieAlgebra.isScalarTower R L
      exact Module.End.exp_mul_of_derivation R L D.toL

Depends on / 依赖: AddHom, AddHom.toFun_eq_coe, D.apply_lie_eq_add, D.toLinearMap, IsNilpotent, IsNilpotent.exp, IsScalarTower, LieAlgebra, LieAlgebra.isScalarTower, LieAlgebra.smulCommClass, LieRing, LieRing.toNonUnitalNonAssocRing, LinearMap, LinearMap.coe_toAddHom, LinearMap.comp_apply, Module, Module.End.exp_mul_of_derivation, Module.End.mul_eq_comp, SMulCommClass, apply_lie_eq_add
-/
noncomputable def exp (h : IsNilpotent D.toLinearMap) :
    L ≃ₗ⁅R⁆ L :=
  { toLinearMap := IsNilpotent.exp D.toLinearMap
    map_lie' := by
      let _i := LieRing.toNonUnitalNonAssocRing L
      have : SMulCommClass R L L := LieAlgebra.smulCommClass R L
      have : IsScalarTower R L L := LieAlgebra.isScalarTower R L
      exact Module.End.exp_mul_of_derivation R L D.toLinearMap D.apply_lie_eq_add h
    invFun x := IsNilpotent.exp (- D.toLinearMap) x
    left_inv x := by
      simp only [AddHom.toFun_eq_coe, LinearMap.coe_toAddHom, ← LinearMap.comp_apply,
        ← Module.End.mul_eq_comp, h.exp_neg_mul_exp_self, Module.End.one_apply]
    right_inv x := by
      simp only [AddHom.toFun_eq_coe, LinearMap.coe_toAddHom, ← LinearMap.comp_apply,
        ← Module.End.mul_eq_comp, h.exp_mul_exp_neg_self, Module.End.one_apply] }

/--
lemma `exp_apply` / 引理 `exp_apply`

English:
lemma exp_apply
  given: (h : IsNilpotent D.toLinearMap)
  proof: rfl

中文:
引理 exp_apply
  条件: (h : 是幂零 D.toLinearMap)
  证明: rfl
-/
lemma exp_apply (h : IsNilpotent D.toLinearMap) :
    exp D h = IsNilpotent.exp D.toLinearMap :=
  rfl

/--
lemma `exp_map_apply` / 引理 `exp_map_apply`

English:
lemma exp_map_apply
  given: (h : IsNilpotent D.toLinearMap) (l : L)
  proof: DFunLike.congr_fun (exp_apply D h) l

中文:
引理 exp_map_apply
  条件: (h : 是幂零 D.toLinearMap) (l : L)
  证明: DFunLike.congr_fun (exp_apply D h) l

Depends on / 依赖: DFunLike, DFunLike.congr_fun, congr_fun, exp_apply
-/
lemma exp_map_apply (h : IsNilpotent D.toLinearMap) (l : L) :
    exp D h l = IsNilpotent.exp D.toLinearMap l :=
  DFunLike.congr_fun (exp_apply D h) l

end ExpNilpotent

end LieDerivation
