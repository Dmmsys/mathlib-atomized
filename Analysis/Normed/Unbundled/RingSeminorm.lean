/-
Copyright (c) 2022 María Inés de Frutos-Fernández. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: María Inés de Frutos-Fernández, Yaël Dillies
-/
module

public import Mathlib.Algebra.Order.Ring.IsNonarchimedean
public import Mathlib.Analysis.Normed.Field.Lemmas
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Seminorms and norms on rings

This file defines seminorms and norms on rings. These definitions are useful when one needs to
consider multiple (semi)norms on a given ring.

## Main declarations

For a ring `R`:
* `RingSeminorm`: A seminorm on a ring `R` is a function `f : R → ℝ` that preserves zero, takes
  nonnegative values, is subadditive and submultiplicative and such that `f (-x) = f x` for all
  `x ∈ R`.
* `RingNorm`: A seminorm `f` is a norm if `f x = 0` if and only if `x = 0`.
* `MulRingSeminorm`: A multiplicative seminorm on a ring `R` is a ring seminorm that preserves
  multiplication.
* `MulRingNorm`: A multiplicative norm on a ring `R` is a ring norm that preserves multiplication.
  `MulRingNorm R` is essentially the same as `AbsoluteValue R ℝ`, and it is recommended to
  use the latter instead to avoid duplicating results.

## Notes

The corresponding hom classes are defined in `Mathlib/Algebra/Order/Hom/Basic.lean` to be used by
absolute values; see `Mathlib/Algebra/Order/AbsoluteValue/Basic.lean` for the bundled version.

## References

* [S. Bosch, U. Güntzer, R. Remmert, *Non-Archimedean Analysis*][bosch-guntzer-remmert]

## Tags
ring_seminorm, ring_norm
-/

@[expose] public section


open NNReal

variable {R : Type*}

/--
Definition of `RingSeminorm` / `RingSeminorm` 的定义

English:
structure RingSeminorm
  parameters: (R : Type*) [NonUnitalNonAssocRing R]
  extends: AddGroupSeminorm R
  axioms and operations (1):
    - mul_le' : forall x y : R, toFun (x * y) <= toFun x * toFun y

中文:
结构 RingSeminorm
  参数: (R : 类型) [NonUnitalNonAssocRing R]
  继承: AddGroupSeminorm R
  公理与运算 (1 个):
    - mul_le' : 对任意 x y : R, toFun (x * y) <= toFun x * toFun y
-/
structure RingSeminorm (R : Type*) [NonUnitalNonAssocRing R] extends AddGroupSeminorm R where
  /-- The property of a `RingSeminorm` that for all `x` and `y` in the ring, the norm of `x * y` is
  less than the norm of `x` times the norm of `y`. -/
  mul_le' : forall x y : R, toFun (x * y) <= toFun x * toFun y

/--
Definition of `RingNorm` / `RingNorm` 的定义

English:
structure RingNorm
  parameters: (R : Type*) [NonUnitalNonAssocRing R]
  extends: RingSeminorm R, AddGroupNorm R
  (no additional axioms)

中文:
结构 RingNorm
  参数: (R : 类型) [NonUnitalNonAssocRing R]
  继承: RingSeminorm R, AddGroupNorm R
  (无附加公理)
-/
structure RingNorm (R : Type*) [NonUnitalNonAssocRing R] extends RingSeminorm R, AddGroupNorm R

/--
Definition of `MulRingSeminorm` / `MulRingSeminorm` 的定义

English:
structure MulRingSeminorm
  parameters: (R : Type*) [NonAssocRing R]
  extends: AddGroupSeminorm R, 
  (no additional axioms)

中文:
结构 MulRingSeminorm
  参数: (R : 类型) [NonAssocRing R]
  继承: AddGroupSeminorm R, 
  (无附加公理)
-/
structure MulRingSeminorm (R : Type*) [NonAssocRing R] extends AddGroupSeminorm R,
  MonoidWithZeroHom R Real

/--
Definition of `MulRingNorm` / `MulRingNorm` 的定义

English:
structure MulRingNorm
  parameters: (R : Type*) [NonAssocRing R]
  extends: MulRingSeminorm R, AddGroupNorm R
  (no additional axioms)

中文:
结构 MulRingNorm
  参数: (R : 类型) [NonAssocRing R]
  继承: MulRingSeminorm R, AddGroupNorm R
  (无附加公理)
-/
structure MulRingNorm (R : Type*) [NonAssocRing R] extends MulRingSeminorm R, AddGroupNorm R

attribute [nolint docBlame]
  RingSeminorm.toAddGroupSeminorm RingNorm.toAddGroupNorm RingNorm.toRingSeminorm
    MulRingSeminorm.toAddGroupSeminorm MulRingSeminorm.toMonoidWithZeroHom
    MulRingNorm.toAddGroupNorm MulRingNorm.toMulRingSeminorm

namespace RingSeminorm

section NonUnitalRing

variable [NonUnitalRing R]

/--
Instance `funLike` / 实例 `funLike`

English:
instance funLike
  signature: : FunLike (RingSeminorm R) R Real where
  body: f.toFun
  coe_injective f g h := by
    cases f
    cases g
    congr
    ext x
    exact congr_fun h x

中文:
实例 funLike
  签名: : FunLike (RingSeminorm R) R 实数 where
  定义体: f.toFun
  coe_injective f g h := by
    cases f
    cases g
    congr
    ext x
    exact congr_fun h x

Depends on / 依赖: f.toFun
-/
instance funLike : FunLike (RingSeminorm R) R Real where
  coe f := f.toFun
  coe_injective f g h := by
    cases f
    cases g
    congr
    ext x
    exact congr_fun h x

/--
Instance `ringSeminormClass` / 实例 `ringSeminormClass`

English:
instance ringSeminormClass
  signature: : RingSeminormClass (RingSeminorm R) R Real where
  body: f.map_zero'
  map_add_le_add f := f.add_le'
  map_mul_le_mul f := f.mul_le'
  map_neg_eq_map f := f.neg'

@[simp]

中文:
实例 ringSeminormClass
  签名: : RingSeminormClass (RingSeminorm R) R 实数 where
  定义体: f.map_zero'
  map_add_le_add f := f.add_le'
  map_mul_le_mul f := f.mul_le'
  map_neg_eq_map f := f.neg'

@[simp]

Depends on / 依赖: f.map_zero, map_zero
-/
instance ringSeminormClass : RingSeminormClass (RingSeminorm R) R Real where
  map_zero f := f.map_zero'
  map_add_le_add f := f.add_le'
  map_mul_le_mul f := f.mul_le'
  map_neg_eq_map f := f.neg'

@[simp]
/--
theorem `toFun_eq_coe` / 定理 `toFun_eq_coe`

English:
theorem toFun_eq_coe
  given: (p : RingSeminorm R)
  statement: (p.toAddGroupSeminorm : R -> Real) = p
  proof: rfl

@[ext]

中文:
定理 toFun_eq_coe
  条件: (p : RingSeminorm R)
  结论: (p.toAddGroupSeminorm : R -> 实数) = p
  证明: rfl

@[ext]
-/
theorem toFun_eq_coe (p : RingSeminorm R) : (p.toAddGroupSeminorm : R -> Real) = p :=
  rfl

@[ext]
/--
theorem `ext` / 定理 `ext`

English:
theorem ext
  given: {p q : RingSeminorm R}
  statement: (forall x, p x = q x) -> p = q
  proof: DFunLike.ext p q

中文:
定理 ext
  条件: {p q : RingSeminorm R}
  结论: (对任意 x, p x = q x) -> p = q
  证明: DFunLike.ext p q

Depends on / 依赖: DFunLike, DFunLike.ext
-/
theorem ext {p q : RingSeminorm R} : (forall x, p x = q x) -> p = q :=
  DFunLike.ext p q

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Zero (RingSeminorm R)
  body: ⟨{ AddGroupSeminorm.instZeroAddGroupSeminorm.zero with mul_le' :=
    fun _ _ => (zero_mul _).ge }⟩

中文:
实例 :
  签名: Zero (RingSeminorm R)
  定义体: ⟨{ AddGroupSeminorm.instZeroAddGroupSeminorm.zero with mul_le' :=
    fun _ _ => (zero_mul _).ge }⟩

Depends on / 依赖: AddGroupSeminorm, AddGroupSeminorm.instZeroAddGroupSeminorm.zero, instZeroAddGroupSeminorm, mul_le, zero_mul
-/
instance : Zero (RingSeminorm R) :=
  ⟨{ AddGroupSeminorm.instZeroAddGroupSeminorm.zero with mul_le' :=
    fun _ _ => (zero_mul _).ge }⟩

/--
theorem `eq_zero_iff` / 定理 `eq_zero_iff`

English:
theorem eq_zero_iff
  given: {p : RingSeminorm R}
  statement: p = 0 ↔ forall x, p x = 0
  proof: DFunLike.ext_iff

中文:
定理 eq_zero_iff
  条件: {p : RingSeminorm R}
  结论: p = 0 ↔ 对任意 x, p x = 0
  证明: DFunLike.ext_iff

Depends on / 依赖: DFunLike, DFunLike.ext_iff, ext_iff
-/
theorem eq_zero_iff {p : RingSeminorm R} : p = 0 ↔ forall x, p x = 0 :=
  DFunLike.ext_iff

/--
theorem `ne_zero_iff` / 定理 `ne_zero_iff`

English:
theorem ne_zero_iff
  given: {p : RingSeminorm R}
  statement: p != 0 ↔ exists x, p x != 0
  proof: by simp [eq_zero_iff]

中文:
定理 ne_zero_iff
  条件: {p : RingSeminorm R}
  结论: p != 0 ↔ 存在 x, p x != 0
  证明: by simp [eq_zero_iff]

Depends on / 依赖: eq_zero_iff
-/
theorem ne_zero_iff {p : RingSeminorm R} : p != 0 ↔ exists x, p x != 0 := by simp [eq_zero_iff]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Inhabited (RingSeminorm R)
  body: ⟨0⟩

中文:
实例 :
  签名: Inhabited (RingSeminorm R)
  定义体: ⟨0⟩
-/
instance : Inhabited (RingSeminorm R) :=
  ⟨0⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [DecidableEq
  signature: R] : One (RingSeminorm R)
  body: ⟨{ (1 : AddGroupSeminorm R) with
      mul_le' := fun x y => by
        by_cases h : x * y = 0
        · refine (if_pos h).trans_le (mul_nonneg ?_ ?_) <;>
            · change _ <= ite _ _ _
              split_ifs
              exacts [le_rfl, zero_le_one]
        · change ite _ _ _ <= ite _ _ _ * 

中文:
实例 [DecidableEq
  签名: R] : One (RingSeminorm R)
  定义体: ⟨{ (1 : AddGroupSeminorm R) with
      mul_le' := fun x y => by
        by_cases h : x * y = 0
        · refine (if_pos h).trans_le (mul_nonneg ?_ ?_) <;>
            · change _ <= ite _ _ _
              split_ifs
              exacts [le_rfl, zero_le_one]
        · change ite _ _ _ <= ite _ _ _ * 

Depends on / 依赖: AddGroupSeminorm, exacts, if_false, if_pos, le_refl, le_rfl, left_ne_zero_of_mul, mul_le, mul_nonneg, mul_one, right_ne_zero_of_mul, split_ifs, trans_le, zero_le_one
-/
instance [DecidableEq R] : One (RingSeminorm R) :=
  ⟨{ (1 : AddGroupSeminorm R) with
      mul_le' := fun x y => by
        by_cases h : x * y = 0
        · refine (if_pos h).trans_le (mul_nonneg ?_ ?_) <;>
            · change _ <= ite _ _ _
              split_ifs
              exacts [le_rfl, zero_le_one]
        · change ite _ _ _ <= ite _ _ _ * ite _ _ _
          simp only [if_false, h, left_ne_zero_of_mul h, right_ne_zero_of_mul h, mul_one,
            le_refl] }⟩

@[simp]
/--
theorem `apply_one` / 定理 `apply_one`

English:
theorem apply_one
  given: [DecidableEq R] (x : R)
  statement: (1 : RingSeminorm R) x = if x = 0 then 0 else 1
  proof: rfl

中文:
定理 apply_one
  条件: [DecidableEq R] (x : R)
  结论: (1 : RingSeminorm R) x = if x = 0 then 0 else 1
  证明: rfl
-/
theorem apply_one [DecidableEq R] (x : R) : (1 : RingSeminorm R) x = if x = 0 then 0 else 1 :=
  rfl

end NonUnitalRing

section Ring

variable [Ring R] (p : RingSeminorm R)

/--
theorem `seminorm_one_eq_one_iff_ne_zero` / 定理 `seminorm_one_eq_one_iff_ne_zero`

English:
theorem seminorm_one_eq_one_iff_ne_zero
  given: (hp : p 1 <= 1)
  statement: p 1 = 1 ↔ p != 0
  proof: by
  refine
    ⟨fun h => ne_zero_iff.mpr ⟨1, by rw [h]; exact one_ne_zero⟩,
      fun h => ?_⟩
  obtain hp0 | hp0 := (apply_nonneg p (1 : R)).eq_or_lt'
  · exfalso
    refine h (ext fun x => (apply_nonneg _ _).antisymm' ?_)
    simpa only [hp0, mul_one, mul_zero] using map_mul_le_mul p x 1
  · refi

中文:
定理 seminorm_one_eq_one_iff_ne_zero
  条件: (hp : p 1 <= 1)
  结论: p 1 = 1 ↔ p != 0
  证明: by
  refine
    ⟨fun h => ne_zero_iff.mpr ⟨1, by rw [h]; exact one_ne_zero⟩,
      fun h => ?_⟩
  obtain hp0 | hp0 := (apply_nonneg p (1 : R)).eq_or_lt'
  · exfalso
    refine h (ext fun x => (apply_nonneg _ _).antisymm' ?_)
    simpa only [hp0, mul_one, mul_zero] using map_mul_le_mul p x 1
  · refi

Depends on / 依赖: antisymm, apply_nonneg, eq_or_lt, hp.antisymm, le_mul_iff_one_le_left, map_mul_le_mul, mul_one, mul_zero, ne_zero_iff, ne_zero_iff.mpr, one_mul, one_ne_zero
-/
theorem seminorm_one_eq_one_iff_ne_zero (hp : p 1 <= 1) : p 1 = 1 ↔ p != 0 := by
  refine
    ⟨fun h => ne_zero_iff.mpr ⟨1, by rw [h]; exact one_ne_zero⟩,
      fun h => ?_⟩
  obtain hp0 | hp0 := (apply_nonneg p (1 : R)).eq_or_lt'
  · exfalso
    refine h (ext fun x => (apply_nonneg _ _).antisymm' ?_)
    simpa only [hp0, mul_one, mul_zero] using map_mul_le_mul p x 1
  · refine hp.antisymm ((le_mul_iff_one_le_left hp0).1 ?_)
    simpa only [one_mul] using map_mul_le_mul p (1 : R) _

/--
Definition of `toSeminormedRing` / `toSeminormedRing` 的定义

English:
abbreviation toSeminormedRing
  signature: : SeminormedRing R where
  body: ‹Ring R›
  __ := p.toAddGroupSeminorm.toSeminormedAddCommGroup
  norm_mul_le := map_mul_le_mul p

中文:
缩写 toSeminormedRing
  签名: : SeminormedRing R where
  定义体: ‹Ring R›
  __ := p.toAddGroupSeminorm.toSeminormedAddCommGroup
  norm_mul_le := map_mul_le_mul p
-/
abbrev toSeminormedRing : SeminormedRing R where
  __ := ‹Ring R›
  __ := p.toAddGroupSeminorm.toSeminormedAddCommGroup
  norm_mul_le := map_mul_le_mul p

end Ring

section CommRing

variable [CommRing R] (p : RingSeminorm R)

/--
theorem `exists_index_pow_le` / 定理 `exists_index_pow_le`

English:
theorem exists_index_pow_le
  given: (hna : IsNonarchimedean p) (x y : R) (n : Nat)
  proof: by
  obtain ⟨m, hm_lt, hm⟩ := IsNonarchimedean.add_pow_le hna n x y
  exact ⟨m, hm_lt, by gcongr⟩

中文:
定理 exists_index_pow_le
  条件: (hna : IsNonarchimedean p) (x y : R) (n : 自然数)
  证明: by
  obtain ⟨m, hm_lt, hm⟩ := IsNonarchimedean.add_pow_le hna n x y
  exact ⟨m, hm_lt, by gcongr⟩

Depends on / 依赖: IsNonarchimedean, IsNonarchimedean.add_pow_le, add_pow_le, hm_lt
-/
theorem exists_index_pow_le (hna : IsNonarchimedean p) (x y : R) (n : Nat) :
    exists (m : Nat), m < n + 1 ∧ p ((x + y) ^ (n : Nat)) ^ (1 / (n : Real)) <=
      (p (x ^ m) * p (y ^ (n - m : Nat))) ^ (1 / (n : Real)) := by
  obtain ⟨m, hm_lt, hm⟩ := IsNonarchimedean.add_pow_le hna n x y
  exact ⟨m, hm_lt, by gcongr⟩

end CommRing

end RingSeminorm

/--
theorem `map_pow_le_pow` / 定理 `map_pow_le_pow`

English:
theorem map_pow_le_pow
  statement: {F α : Type*} [Ring α] [FunLike F α Real] [RingSeminormClass F α Real] (f : F)

中文:
定理 map_pow_le_pow
  结论: {F α : 类型} [Ring α] [FunLike F α 实数] [RingSeminormClass F α 实数] (f : F)
-/
theorem map_pow_le_pow {F α : Type*} [Ring α] [FunLike F α Real] [RingSeminormClass F α Real] (f : F)
    (a : α) : forall {n : Nat}, n != 0 -> f (a ^ n) <= f a ^ n
  | 0, h => absurd rfl h
  | 1, _ => by simp only [pow_one, le_refl]
  | n + 2, _ => by
    simp only [pow_succ _ (n + 1)]
    grw [map_mul_le_mul, map_pow_le_pow _ _ n.succ_ne_zero]

/--
theorem `map_pow_le_pow'` / 定理 `map_pow_le_pow'`

English:
theorem map_pow_le_pow'
  statement: {F α : Type*} [Ring α] [FunLike F α Real] [RingSeminormClass F α Real] {f : F}

中文:
定理 map_pow_le_pow'
  结论: {F α : 类型} [Ring α] [FunLike F α 实数] [RingSeminormClass F α 实数] {f : F}
-/
theorem map_pow_le_pow' {F α : Type*} [Ring α] [FunLike F α Real] [RingSeminormClass F α Real] {f : F}
    (hf1 : f 1 <= 1) (a : α) : forall n : Nat, f (a ^ n) <= f a ^ n
  | 0 => by simp only [pow_zero, hf1]
  | n + 1 => map_pow_le_pow _ _ n.succ_ne_zero

/--
Definition of `normRingSeminorm` / `normRingSeminorm` 的定义

English:
definition normRingSeminorm
  signature: (R : Type*) [NonUnitalSeminormedRing R]
  body: { normAddGroupSeminorm R with
    toFun := norm
    mul_le' := norm_mul_le }

中文:
定义 normRingSeminorm
  签名: (R : 类型) [NonUnitalSeminormedRing R]
  定义体: { normAddGroupSeminorm R with
    toFun := norm
    mul_le' := norm_mul_le }

Depends on / 依赖: mul_le, normAddGroupSeminorm, norm_mul_le
-/
def normRingSeminorm (R : Type*) [NonUnitalSeminormedRing R] : RingSeminorm R :=
  { normAddGroupSeminorm R with
    toFun := norm
    mul_le' := norm_mul_le }

namespace RingSeminorm

variable [Ring R] (p : RingSeminorm R)

open Filter Nat Real

/--
theorem `isBoundedUnder` / 定理 `isBoundedUnder`

English:
theorem isBoundedUnder
  given: (hp : p 1 <= 1) {s : Nat -> Nat} (hs_le : forall n : Nat, s n <= n) {x : R} (ψ : Nat -> Nat)
  proof: by
  have h_le : forall m : Nat, p (x ^ s (ψ m)) ^ (1 / (ψ m : Real)) <= p x ^ ((s (ψ m) : Real) / (ψ m : Real)) := by
    intro m
    rw [← mul_one_div (s (ψ m) : Real)]; rw [rpow_mul (apply_nonneg p x)]; rw [rpow_natCast]
    grw [map_pow_le_pow' hp x]
  apply isBoundedUnder_of
  cases le_or_gt (p

中文:
定理 isBoundedUnder
  条件: (hp : p 1 <= 1) {s : 自然数 -> 自然数} (hs_le : 对任意 n : 自然数, s n <= n) {x : R} (ψ : 自然数 -> 自然数)
  证明: by
  have h_le : forall m : Nat, p (x ^ s (ψ m)) ^ (1 / (ψ m : Real)) <= p x ^ ((s (ψ m) : Real) / (ψ m : Real)) := by
    intro m
    rw [← mul_one_div (s (ψ m) : Real)]; rw [rpow_mul (apply_nonneg p x)]; rw [rpow_natCast]
    grw [map_pow_le_pow' hp x]
  apply isBoundedUnder_of
  cases le_or_gt (p

Depends on / 依赖: apply_nonneg, div_le_one_of_le, h_le, hfx.le, isBoundedUnder_of, le_or_gt, le_trans, map_pow_le_pow, mul_one_div, rpow_le_one, rpow_le_self_of_one_le, rpow_mul, rpow_natCast
-/
theorem isBoundedUnder (hp : p 1 <= 1) {s : Nat -> Nat} (hs_le : forall n : Nat, s n <= n) {x : R} (ψ : Nat -> Nat) :
    IsBoundedUnder LE.le atTop fun n : Nat => p (x ^ s (ψ n)) ^ (1 / (ψ n : Real)) := by
  have h_le : forall m : Nat, p (x ^ s (ψ m)) ^ (1 / (ψ m : Real)) <= p x ^ ((s (ψ m) : Real) / (ψ m : Real)) := by
    intro m
    rw [← mul_one_div (s (ψ m) : Real)]; rw [rpow_mul (apply_nonneg p x)]; rw [rpow_natCast]
    grw [map_pow_le_pow' hp x]
  apply isBoundedUnder_of
  cases le_or_gt (p x) 1 with
  | inl hfx =>
    use 1, fun m => le_trans (h_le m) (rpow_le_one (by positivity) hfx (by positivity))
  | inr hfx =>
    use p x
refine fun m => le_trans (h_le m) rpow_le_self_of_one_le hfx.le ?_
    exact div_le_one_of_le₀ (mod_cast hs_le _) (cast_nonneg _)

end RingSeminorm

namespace RingNorm

section NonUnitalRing

variable [NonUnitalRing R]

/--
Instance `funLike` / 实例 `funLike`

English:
instance funLike
  signature: : FunLike (RingNorm R) R Real where
  body: f.toFun
  coe_injective f g h := by
    cases f
    cases g
    congr
    ext x
    exact congr_fun h x

中文:
实例 funLike
  签名: : FunLike (RingNorm R) R 实数 where
  定义体: f.toFun
  coe_injective f g h := by
    cases f
    cases g
    congr
    ext x
    exact congr_fun h x

Depends on / 依赖: f.toFun
-/
instance funLike : FunLike (RingNorm R) R Real where
  coe f := f.toFun
  coe_injective f g h := by
    cases f
    cases g
    congr
    ext x
    exact congr_fun h x

/--
Instance `ringNormClass` / 实例 `ringNormClass`

English:
instance ringNormClass
  signature: : RingNormClass (RingNorm R) R Real where
  body: f.map_zero'
  map_add_le_add f := f.add_le'
  map_mul_le_mul f := f.mul_le'
  map_neg_eq_map f := f.neg'
  eq_zero_of_map_eq_zero f := f.eq_zero_of_map_eq_zero' _

中文:
实例 ringNormClass
  签名: : RingNormClass (RingNorm R) R 实数 where
  定义体: f.map_zero'
  map_add_le_add f := f.add_le'
  map_mul_le_mul f := f.mul_le'
  map_neg_eq_map f := f.neg'
  eq_zero_of_map_eq_zero f := f.eq_zero_of_map_eq_zero' _

Depends on / 依赖: f.map_zero, map_zero
-/
instance ringNormClass : RingNormClass (RingNorm R) R Real where
  map_zero f := f.map_zero'
  map_add_le_add f := f.add_le'
  map_mul_le_mul f := f.mul_le'
  map_neg_eq_map f := f.neg'
  eq_zero_of_map_eq_zero f := f.eq_zero_of_map_eq_zero' _

/--
theorem `toFun_eq_coe` / 定理 `toFun_eq_coe`

English:
theorem toFun_eq_coe
  given: (p : RingNorm R)
  statement: p.toFun = p
  proof: rfl

@[ext]

中文:
定理 toFun_eq_coe
  条件: (p : RingNorm R)
  结论: p.toFun = p
  证明: rfl

@[ext]
-/
theorem toFun_eq_coe (p : RingNorm R) : p.toFun = p := rfl

@[ext]
/--
theorem `ext` / 定理 `ext`

English:
theorem ext
  given: {p q : RingNorm R}
  statement: (forall x, p x = q x) -> p = q
  proof: DFunLike.ext p q

中文:
定理 ext
  条件: {p q : RingNorm R}
  结论: (对任意 x, p x = q x) -> p = q
  证明: DFunLike.ext p q

Depends on / 依赖: DFunLike, DFunLike.ext
-/
theorem ext {p q : RingNorm R} : (forall x, p x = q x) -> p = q :=
  DFunLike.ext p q

variable (R)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [DecidableEq
  signature: R] : One (RingNorm R)
  body: ⟨{ (1 : RingSeminorm R), (1 : AddGroupNorm R) with }⟩

@[simp]

中文:
实例 [DecidableEq
  签名: R] : One (RingNorm R)
  定义体: ⟨{ (1 : RingSeminorm R), (1 : AddGroupNorm R) with }⟩

@[simp]

Depends on / 依赖: AddGroupNorm, RingSeminorm
-/
instance [DecidableEq R] : One (RingNorm R) :=
  ⟨{ (1 : RingSeminorm R), (1 : AddGroupNorm R) with }⟩

@[simp]
/--
theorem `apply_one` / 定理 `apply_one`

English:
theorem apply_one
  given: [DecidableEq R] (x : R)
  statement: (1 : RingNorm R) x = if x = 0 then 0 else 1
  proof: rfl

中文:
定理 apply_one
  条件: [DecidableEq R] (x : R)
  结论: (1 : RingNorm R) x = if x = 0 then 0 else 1
  证明: rfl
-/
theorem apply_one [DecidableEq R] (x : R) : (1 : RingNorm R) x = if x = 0 then 0 else 1 :=
  rfl

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [DecidableEq
  signature: R] : Inhabited (RingNorm R)
  body: ⟨1⟩

中文:
实例 [DecidableEq
  签名: R] : Inhabited (RingNorm R)
  定义体: ⟨1⟩
-/
instance [DecidableEq R] : Inhabited (RingNorm R) :=
  ⟨1⟩

end NonUnitalRing

-- See note |reducible non-instances]
/--
Definition of `toNormedRing` / `toNormedRing` 的定义

English:
abbreviation toNormedRing
  signature: [Ring R] (f : RingNorm R)
  body: ‹Ring R›
  __ := f.toAddGroupNorm.toNormedAddCommGroup
  norm_mul_le := map_mul_le_mul f

中文:
缩写 toNormedRing
  签名: [Ring R] (f : RingNorm R)
  定义体: ‹Ring R›
  __ := f.toAddGroupNorm.toNormedAddCommGroup
  norm_mul_le := map_mul_le_mul f
-/
abbrev toNormedRing [Ring R] (f : RingNorm R) : NormedRing R where
  __ := ‹Ring R›
  __ := f.toAddGroupNorm.toNormedAddCommGroup
  norm_mul_le := map_mul_le_mul f

end RingNorm

namespace MulRingSeminorm

variable [NonAssocRing R]

/--
Instance `funLike` / 实例 `funLike`

English:
instance funLike
  signature: : FunLike (MulRingSeminorm R) R Real where
  body: f.toFun
  coe_injective f g h := by
    cases f
    cases g
    congr
    ext x
    exact congr_fun h x

中文:
实例 funLike
  签名: : FunLike (MulRingSeminorm R) R 实数 where
  定义体: f.toFun
  coe_injective f g h := by
    cases f
    cases g
    congr
    ext x
    exact congr_fun h x

Depends on / 依赖: f.toFun
-/
instance funLike : FunLike (MulRingSeminorm R) R Real where
  coe f := f.toFun
  coe_injective f g h := by
    cases f
    cases g
    congr
    ext x
    exact congr_fun h x

/--
Instance `mulRingSeminormClass` / 实例 `mulRingSeminormClass`

English:
instance mulRingSeminormClass
  signature: : MulRingSeminormClass (MulRingSeminorm R) R Real where
  body: f.map_zero'
  map_one f := f.map_one'
  map_add_le_add f := f.add_le'
  map_mul f := f.map_mul'
  map_neg_eq_map f := f.neg'

@[simp]

中文:
实例 mulRingSeminormClass
  签名: : MulRingSeminormClass (MulRingSeminorm R) R 实数 where
  定义体: f.map_zero'
  map_one f := f.map_one'
  map_add_le_add f := f.add_le'
  map_mul f := f.map_mul'
  map_neg_eq_map f := f.neg'

@[simp]

Depends on / 依赖: f.map_zero, map_zero
-/
instance mulRingSeminormClass : MulRingSeminormClass (MulRingSeminorm R) R Real where
  map_zero f := f.map_zero'
  map_one f := f.map_one'
  map_add_le_add f := f.add_le'
  map_mul f := f.map_mul'
  map_neg_eq_map f := f.neg'

@[simp]
/--
theorem `toFun_eq_coe` / 定理 `toFun_eq_coe`

English:
theorem toFun_eq_coe
  given: (p : MulRingSeminorm R)
  statement: (p.toAddGroupSeminorm : R -> Real) = p
  proof: rfl

@[ext]

中文:
定理 toFun_eq_coe
  条件: (p : MulRingSeminorm R)
  结论: (p.toAddGroupSeminorm : R -> 实数) = p
  证明: rfl

@[ext]
-/
theorem toFun_eq_coe (p : MulRingSeminorm R) : (p.toAddGroupSeminorm : R -> Real) = p :=
  rfl

@[ext]
/--
theorem `ext` / 定理 `ext`

English:
theorem ext
  given: {p q : MulRingSeminorm R}
  statement: (forall x, p x = q x) -> p = q
  proof: DFunLike.ext p q

中文:
定理 ext
  条件: {p q : MulRingSeminorm R}
  结论: (对任意 x, p x = q x) -> p = q
  证明: DFunLike.ext p q

Depends on / 依赖: DFunLike, DFunLike.ext
-/
theorem ext {p q : MulRingSeminorm R} : (forall x, p x = q x) -> p = q :=
  DFunLike.ext p q

variable [DecidableEq R] [NoZeroDivisors R] [Nontrivial R]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: One (MulRingSeminorm R)
  body: ⟨{ (1 : AddGroupSeminorm R) with
      map_one' := if_neg one_ne_zero
      map_mul' := fun x y => by
        obtain rfl | hx := eq_or_ne x 0
        · simp
        obtain rfl | hy := eq_or_ne y 0
        · simp
        · simp [hx, hy] }⟩

@[simp]

中文:
实例 :
  签名: One (MulRingSeminorm R)
  定义体: ⟨{ (1 : AddGroupSeminorm R) with
      map_one' := if_neg one_ne_zero
      map_mul' := fun x y => by
        obtain rfl | hx := eq_or_ne x 0
        · simp
        obtain rfl | hy := eq_or_ne y 0
        · simp
        · simp [hx, hy] }⟩

@[simp]

Depends on / 依赖: AddGroupSeminorm, eq_or_ne, if_neg, map_mul, map_one, one_ne_zero
-/
instance : One (MulRingSeminorm R) :=
  ⟨{ (1 : AddGroupSeminorm R) with
      map_one' := if_neg one_ne_zero
      map_mul' := fun x y => by
        obtain rfl | hx := eq_or_ne x 0
        · simp
        obtain rfl | hy := eq_or_ne y 0
        · simp
        · simp [hx, hy] }⟩

@[simp]
/--
theorem `apply_one` / 定理 `apply_one`

English:
theorem apply_one
  given: (x : R)
  statement: (1 : MulRingSeminorm R) x = if x = 0 then 0 else 1
  proof: rfl

中文:
定理 apply_one
  条件: (x : R)
  结论: (1 : MulRingSeminorm R) x = if x = 0 then 0 else 1
  证明: rfl
-/
theorem apply_one (x : R) : (1 : MulRingSeminorm R) x = if x = 0 then 0 else 1 :=
  rfl

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Inhabited (MulRingSeminorm R)
  body: ⟨1⟩

中文:
实例 :
  签名: Inhabited (MulRingSeminorm R)
  定义体: ⟨1⟩
-/
instance : Inhabited (MulRingSeminorm R) :=
  ⟨1⟩

end MulRingSeminorm

namespace MulRingNorm

variable [NonAssocRing R]

/--
Instance `funLike` / 实例 `funLike`

English:
instance funLike
  signature: : FunLike (MulRingNorm R) R Real where
  body: f.toFun
  coe_injective f g h := by
    cases f
    cases g
    congr
    ext x
    exact congr_fun h x

中文:
实例 funLike
  签名: : FunLike (MulRingNorm R) R 实数 where
  定义体: f.toFun
  coe_injective f g h := by
    cases f
    cases g
    congr
    ext x
    exact congr_fun h x

Depends on / 依赖: f.toFun
-/
instance funLike : FunLike (MulRingNorm R) R Real where
  coe f := f.toFun
  coe_injective f g h := by
    cases f
    cases g
    congr
    ext x
    exact congr_fun h x

/--
Instance `mulRingNormClass` / 实例 `mulRingNormClass`

English:
instance mulRingNormClass
  signature: : MulRingNormClass (MulRingNorm R) R Real where
  body: f.map_zero'
  map_one f := f.map_one'
  map_add_le_add f := f.add_le'
  map_mul f := f.map_mul'
  map_neg_eq_map f := f.neg'
  eq_zero_of_map_eq_zero f := f.eq_zero_of_map_eq_zero' _

中文:
实例 mulRingNormClass
  签名: : MulRingNormClass (MulRingNorm R) R 实数 where
  定义体: f.map_zero'
  map_one f := f.map_one'
  map_add_le_add f := f.add_le'
  map_mul f := f.map_mul'
  map_neg_eq_map f := f.neg'
  eq_zero_of_map_eq_zero f := f.eq_zero_of_map_eq_zero' _

Depends on / 依赖: f.map_zero, map_zero
-/
instance mulRingNormClass : MulRingNormClass (MulRingNorm R) R Real where
  map_zero f := f.map_zero'
  map_one f := f.map_one'
  map_add_le_add f := f.add_le'
  map_mul f := f.map_mul'
  map_neg_eq_map f := f.neg'
  eq_zero_of_map_eq_zero f := f.eq_zero_of_map_eq_zero' _

/--
theorem `toFun_eq_coe` / 定理 `toFun_eq_coe`

English:
theorem toFun_eq_coe
  given: (p : MulRingNorm R)
  statement: p.toFun = p
  proof: rfl

@[ext]

中文:
定理 toFun_eq_coe
  条件: (p : MulRingNorm R)
  结论: p.toFun = p
  证明: rfl

@[ext]
-/
theorem toFun_eq_coe (p : MulRingNorm R) : p.toFun = p := rfl

@[ext]
/--
theorem `ext` / 定理 `ext`

English:
theorem ext
  given: {p q : MulRingNorm R}
  statement: (forall x, p x = q x) -> p = q
  proof: DFunLike.ext p q

中文:
定理 ext
  条件: {p q : MulRingNorm R}
  结论: (对任意 x, p x = q x) -> p = q
  证明: DFunLike.ext p q

Depends on / 依赖: DFunLike, DFunLike.ext
-/
theorem ext {p q : MulRingNorm R} : (forall x, p x = q x) -> p = q :=
  DFunLike.ext p q

variable (R)
variable [DecidableEq R] [NoZeroDivisors R] [Nontrivial R]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: One (MulRingNorm R)
  body: ⟨{ (1 : MulRingSeminorm R), (1 : AddGroupNorm R) with }⟩

@[simp]

中文:
实例 :
  签名: One (MulRingNorm R)
  定义体: ⟨{ (1 : MulRingSeminorm R), (1 : AddGroupNorm R) with }⟩

@[simp]

Depends on / 依赖: AddGroupNorm, MulRingSeminorm
-/
instance : One (MulRingNorm R) :=
  ⟨{ (1 : MulRingSeminorm R), (1 : AddGroupNorm R) with }⟩

@[simp]
/--
theorem `apply_one` / 定理 `apply_one`

English:
theorem apply_one
  given: (x : R)
  statement: (1 : MulRingNorm R) x = if x = 0 then 0 else 1
  proof: rfl

中文:
定理 apply_one
  条件: (x : R)
  结论: (1 : MulRingNorm R) x = if x = 0 then 0 else 1
  证明: rfl
-/
theorem apply_one (x : R) : (1 : MulRingNorm R) x = if x = 0 then 0 else 1 :=
  rfl

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Inhabited (MulRingNorm R)
  body: ⟨1⟩

中文:
实例 :
  签名: Inhabited (MulRingNorm R)
  定义体: ⟨1⟩
-/
instance : Inhabited (MulRingNorm R) :=
  ⟨1⟩

section MulRingNorm_equiv_AbsoluteValue

variable {R : Type*} [Ring R] [Nontrivial R]

/--
Definition of `mulRingNormEquivAbsoluteValue` / `mulRingNormEquivAbsoluteValue` 的定义

English:
definition mulRingNormEquivAbsoluteValue
  signature: : MulRingNorm R ≃ AbsoluteValue R Real where
  body: {
    toFun := N.toFun
    map_mul' := N.map_mul'
    nonneg' := apply_nonneg N
    eq_zero' x := ⟨N.eq_zero_of_map_eq_zero' x, fun h => h ▸ N.map_zero'⟩
    add_le' := N.add_le'
  }
  invFun v := {
    toFun := v.toFun
    map_zero' := (v.eq_zero' 0).mpr rfl
    add_le' := v.add_le'
    neg' := v.m

中文:
定义 mulRingNormEquivAbsoluteValue
  签名: : MulRingNorm R ≃ AbsoluteValue R 实数 where
  定义体: {
    toFun := N.toFun
    map_mul' := N.map_mul'
    nonneg' := apply_nonneg N
    eq_zero' x := ⟨N.eq_zero_of_map_eq_zero' x, fun h => h ▸ N.map_zero'⟩
    add_le' := N.add_le'
  }
  invFun v := {
    toFun := v.toFun
    map_zero' := (v.eq_zero' 0).mpr rfl
    add_le' := v.add_le'
    neg' := v.m
-/
def mulRingNormEquivAbsoluteValue : MulRingNorm R ≃ AbsoluteValue R Real where
  toFun N := {
    toFun := N.toFun
    map_mul' := N.map_mul'
    nonneg' := apply_nonneg N
    eq_zero' x := ⟨N.eq_zero_of_map_eq_zero' x, fun h => h ▸ N.map_zero'⟩
    add_le' := N.add_le'
  }
  invFun v := {
    toFun := v.toFun
    map_zero' := (v.eq_zero' 0).mpr rfl
    add_le' := v.add_le'
    neg' := v.map_neg
    map_one' := v.map_one
    map_mul' := v.map_mul'
    eq_zero_of_map_eq_zero' x := (v.eq_zero' x).mp
  }
  left_inv N := by constructor
  right_inv v := by ext1 x; simp

/--
lemma `mulRingNormEquivAbsoluteValue_apply` / 引理 `mulRingNormEquivAbsoluteValue_apply`

English:
lemma mulRingNormEquivAbsoluteValue_apply
  given: (N : MulRingNorm R) (x : R)
  proof: rfl

中文:
引理 mulRingNormEquivAbsoluteValue_apply
  条件: (N : MulRingNorm R) (x : R)
  证明: rfl
-/
lemma mulRingNormEquivAbsoluteValue_apply (N : MulRingNorm R) (x : R) :
    mulRingNormEquivAbsoluteValue N x = N x := rfl

/--
lemma `mulRingNormEquivAbsoluteValue_symm_apply` / 引理 `mulRingNormEquivAbsoluteValue_symm_apply`

English:
lemma mulRingNormEquivAbsoluteValue_symm_apply
  given: (v : AbsoluteValue R Real) (x : R)
  proof: rfl

中文:
引理 mulRingNormEquivAbsoluteValue_symm_apply
  条件: (v : AbsoluteValue R 实数) (x : R)
  证明: rfl
-/
lemma mulRingNormEquivAbsoluteValue_symm_apply (v : AbsoluteValue R Real) (x : R) :
    mulRingNormEquivAbsoluteValue.symm v x = v x := rfl

end MulRingNorm_equiv_AbsoluteValue

end MulRingNorm

/--
Definition of `RingSeminorm.toRingNorm` / `RingSeminorm.toRingNorm` 的定义

English:
definition RingSeminorm.toRingNorm
  signature: {K : Type*} [Field K] (f : RingSeminorm K) (hnt : f != 0)
  body: { f with
    eq_zero_of_map_eq_zero' := fun x hx => by
      obtain ⟨c, hc⟩ := RingSeminorm.ne_zero_iff.mp hnt
      by_contra hn0
      have hc0 : f c = 0 := by
        rw [← mul_one c]; rw [← mul_inv_cancel₀ hn0]; rw [← mul_assoc]; rw [mul_comm c]; rw [mul_assoc]
        exact
          le_antisym

中文:
定义 RingSeminorm.toRingNorm
  签名: {K : 类型} [Field K] (f : RingSeminorm K) (hnt : f != 0)
  定义体: { f with
    eq_zero_of_map_eq_zero' := fun x hx => by
      obtain ⟨c, hc⟩ := RingSeminorm.ne_zero_iff.mp hnt
      by_contra hn0
      have hc0 : f c = 0 := by
        rw [← mul_one c]; rw [← mul_inv_cancel₀ hn0]; rw [← mul_assoc]; rw [mul_comm c]; rw [mul_assoc]
        exact
          le_antisym

Depends on / 依赖: AddGroupSeminorm, AddGroupSeminorm.toFun_eq_coe, RingSeminorm, RingSeminorm.ne_zero_iff.mp, RingSeminorm.toFun_eq_coe, apply_nonneg, eq_zero_of_map_eq_zero, le_antisymm, le_trans, map_mul_le_mul, mul_assoc, mul_comm, mul_one, ne_zero_iff, toFun_eq_coe, zero_mul
-/
def RingSeminorm.toRingNorm {K : Type*} [Field K] (f : RingSeminorm K) (hnt : f != 0) :
    RingNorm K :=
  { f with
    eq_zero_of_map_eq_zero' := fun x hx => by
      obtain ⟨c, hc⟩ := RingSeminorm.ne_zero_iff.mp hnt
      by_contra hn0
      have hc0 : f c = 0 := by
        rw [← mul_one c]; rw [← mul_inv_cancel₀ hn0]; rw [← mul_assoc]; rw [mul_comm c]; rw [mul_assoc]
        exact
          le_antisymm
            (le_trans (map_mul_le_mul f _ _)
              (by rw [← RingSeminorm.toFun_eq_coe, ← AddGroupSeminorm.toFun_eq_coe, hx,
                zero_mul]))
            (apply_nonneg f _)
      exact hc hc0 }

/-- The norm of a `NonUnitalNormedRing` as a `RingNorm`. -/
@[simps!]
/--
Definition of `normRingNorm` / `normRingNorm` 的定义

English:
definition normRingNorm
  signature: (R : Type*) [NonUnitalNormedRing R]
  body: { normAddGroupNorm R, normRingSeminorm R with }

中文:
定义 normRingNorm
  签名: (R : 类型) [NonUnitalNormedRing R]
  定义体: { normAddGroupNorm R, normRingSeminorm R with }

Depends on / 依赖: normAddGroupNorm, normRingSeminorm
-/
def normRingNorm (R : Type*) [NonUnitalNormedRing R] : RingNorm R :=
  { normAddGroupNorm R, normRingSeminorm R with }

open Int

set_option linter.style.whitespace false in -- manual alignment is not recognised
/--
Definition of `SeminormedRing.toRingSeminorm` / `SeminormedRing.toRingSeminorm` 的定义

English:
definition SeminormedRing.toRingSeminorm
  signature: (R : Type*) [SeminormedRing R]
  body: norm
  map_zero' := norm_zero
  add_le' := norm_add_le
  mul_le' := norm_mul_le
  neg' := norm_neg

@[simp]

中文:
定义 SeminormedRing.toRingSeminorm
  签名: (R : 类型) [SeminormedRing R]
  定义体: norm
  map_zero' := norm_zero
  add_le' := norm_add_le
  mul_le' := norm_mul_le
  neg' := norm_neg

@[simp]
-/
def SeminormedRing.toRingSeminorm (R : Type*) [SeminormedRing R] : RingSeminorm R where
  toFun := norm
  map_zero' := norm_zero
  add_le' := norm_add_le
  mul_le' := norm_mul_le
  neg' := norm_neg

@[simp]
/--
theorem `SeminormedRing.toRingSeminorm_apply` / 定理 `SeminormedRing.toRingSeminorm_apply`

English:
theorem SeminormedRing.toRingSeminorm_apply
  given: (R : Type*) [SeminormedRing R] (x : R)
  proof: rfl

中文:
定理 SeminormedRing.toRingSeminorm_apply
  条件: (R : 类型) [SeminormedRing R] (x : R)
  证明: rfl
-/
theorem SeminormedRing.toRingSeminorm_apply (R : Type*) [SeminormedRing R] (x : R) :
    (SeminormedRing.toRingSeminorm R) x = ‖x‖ :=
  rfl

set_option linter.style.whitespace false in -- manual alignment is not recognised
/-- The norm on a `NormedRing`, as a `RingNorm`. -/
@[simps]
/--
Definition of `NormedRing.toRingNorm` / `NormedRing.toRingNorm` 的定义

English:
definition NormedRing.toRingNorm
  signature: (R : Type*) [NormedRing R]
  body: norm
  map_zero' := norm_zero
  add_le' := norm_add_le
  mul_le' := norm_mul_le
  neg' := norm_neg
  eq_zero_of_map_eq_zero' x hx := by rw [← norm_eq_zero]; exact hx

@[simp]

中文:
定义 NormedRing.toRingNorm
  签名: (R : 类型) [NormedRing R]
  定义体: norm
  map_zero' := norm_zero
  add_le' := norm_add_le
  mul_le' := norm_mul_le
  neg' := norm_neg
  eq_zero_of_map_eq_zero' x hx := by rw [← norm_eq_zero]; exact hx

@[simp]
-/
def NormedRing.toRingNorm (R : Type*) [NormedRing R] : RingNorm R where
  toFun := norm
  map_zero' := norm_zero
  add_le' := norm_add_le
  mul_le' := norm_mul_le
  neg' := norm_neg
  eq_zero_of_map_eq_zero' x hx := by rw [← norm_eq_zero]; exact hx

@[simp]
/--
theorem `NormedRing.toRingNorm_apply` / 定理 `NormedRing.toRingNorm_apply`

English:
theorem NormedRing.toRingNorm_apply
  given: (R : Type*) [NormedRing R] (x : R)
  proof: rfl

中文:
定理 NormedRing.toRingNorm_apply
  条件: (R : 类型) [NormedRing R] (x : R)
  证明: rfl
-/
theorem NormedRing.toRingNorm_apply (R : Type*) [NormedRing R] (x : R) :
    (NormedRing.toRingNorm R) x = ‖x‖ :=
  rfl

set_option linter.style.whitespace false in -- manual alignment is not recognised
/--
Definition of `NormedField.toMulRingNorm` / `NormedField.toMulRingNorm` 的定义

English:
definition NormedField.toMulRingNorm
  signature: (R : Type*) [NormedField R]
  body: norm
  map_zero' := norm_zero
  map_one' := norm_one
  add_le' := norm_add_le
  map_mul' := norm_mul
  neg' := norm_neg
  eq_zero_of_map_eq_zero' x hx := by rw [← norm_eq_zero]; exact hx

中文:
定义 NormedField.toMulRingNorm
  签名: (R : 类型) [NormedField R]
  定义体: norm
  map_zero' := norm_zero
  map_one' := norm_one
  add_le' := norm_add_le
  map_mul' := norm_mul
  neg' := norm_neg
  eq_zero_of_map_eq_zero' x hx := by rw [← norm_eq_zero]; exact hx
-/
def NormedField.toMulRingNorm (R : Type*) [NormedField R] : MulRingNorm R where
  toFun := norm
  map_zero' := norm_zero
  map_one' := norm_one
  add_le' := norm_add_le
  map_mul' := norm_mul
  neg' := norm_neg
  eq_zero_of_map_eq_zero' x hx := by rw [← norm_eq_zero]; exact hx

set_option linter.style.whitespace false in -- manual alignment is not recognised
/--
Definition of `NormedField.toAbsoluteValue` / `NormedField.toAbsoluteValue` 的定义

English:
definition NormedField.toAbsoluteValue
  signature: (R : Type*) [NormedField R]
  body: norm
  map_mul' := norm_mul
  nonneg' := norm_nonneg
  eq_zero' _ := norm_eq_zero
  add_le' := norm_add_le

中文:
定义 NormedField.toAbsoluteValue
  签名: (R : 类型) [NormedField R]
  定义体: norm
  map_mul' := norm_mul
  nonneg' := norm_nonneg
  eq_zero' _ := norm_eq_zero
  add_le' := norm_add_le
-/
def NormedField.toAbsoluteValue (R : Type*) [NormedField R] : AbsoluteValue R Real where
  toFun := norm
  map_mul' := norm_mul
  nonneg' := norm_nonneg
  eq_zero' _ := norm_eq_zero
  add_le' := norm_add_le
