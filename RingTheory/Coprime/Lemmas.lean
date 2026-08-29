/-
Copyright (c) 2020 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau, Ken Lee, Chris Hughes
-/
module

public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Int.GCD
public import Mathlib.RingTheory.Coprime.Basic

/-!
# Additional lemmas about elements of a ring satisfying `IsCoprime`

and elements of a monoid satisfying `IsRelPrime`

These lemmas are in a separate file to the definition of `IsCoprime` or `IsRelPrime`
as they require more imports.

Notably, this includes lemmas about `Finset.prod` as this requires importing BigOperators, and
lemmas about `Pow` since these are easiest to prove via `Finset.prod`.

-/

public section

universe u v

open scoped Function -- required for scoped `on` notation

section IsCoprime

variable {R : Type u} {I : Type v} [CommSemiring R] {x y z : R} {s : I -> R} {t : Finset I}

section

/--
theorem `Int.isCoprime_iff_gcd_eq_one` / 定理 `Int.isCoprime_iff_gcd_eq_one`

English:
theorem Int.isCoprime_iff_gcd_eq_one
  given: {m n : Int}
  statement: IsCoprime m n ↔ Int.gcd m n = 1
  proof: by
  constructor
  · rintro ⟨a, b, h⟩
    refine Nat.dvd_one.mp (Int.gcd_dvd_iff.mpr ⟨a, b, ?_⟩)
    rwa [mul_comm m, mul_comm n, eq_comm]
  · rw [← Int.ofNat_inj, IsCoprime, Int.gcd_eq_gcd_ab, mul_comm m, mul_comm n, Nat.cast_one]
    intro h
    exact ⟨_, _, h⟩

中文:
定理 整数.isCoprime_iff_gcd_eq_one
  条件: {m n : 整数}
  结论: IsCoprime m n ↔ 整数.最大公约数 m n = 1
  证明: by
  constructor
  · rintro ⟨a, b, h⟩
    refine Nat.dvd_one.mp (Int.gcd_dvd_iff.mpr ⟨a, b, ?_⟩)
    rwa [mul_comm m, mul_comm n, eq_comm]
  · rw [← Int.ofNat_inj, IsCoprime, Int.gcd_eq_gcd_ab, mul_comm m, mul_comm n, Nat.cast_one]
    intro h
    exact ⟨_, _, h⟩

Depends on / 依赖: Int.gcd_dvd_iff.mpr, Int.gcd_eq_gcd_ab, Int.ofNat_inj, IsCoprime, Nat.cast_one, Nat.dvd_one.mp, cast_one, dvd_one, eq_comm, gcd_dvd_iff, gcd_eq_gcd_ab, mul_comm, ofNat_inj
-/
theorem Int.isCoprime_iff_gcd_eq_one {m n : Int} : IsCoprime m n ↔ Int.gcd m n = 1 := by
  constructor
  · rintro ⟨a, b, h⟩
    refine Nat.dvd_one.mp (Int.gcd_dvd_iff.mpr ⟨a, b, ?_⟩)
    rwa [mul_comm m, mul_comm n, eq_comm]
  · rw [← Int.ofNat_inj, IsCoprime, Int.gcd_eq_gcd_ab, mul_comm m, mul_comm n, Nat.cast_one]
    intro h
    exact ⟨_, _, h⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: DecidableRel (IsCoprime : Int -> Int -> Prop)
  body: fun m n => decidable_of_iff (Int.gcd m n = 1) Int.isCoprime_iff_gcd_eq_one.symm

@[simp, norm_cast]

中文:
实例 :
  签名: DecidableRel (IsCoprime : 整数 -> 整数 -> 命题)
  定义体: fun m n => decidable_of_iff (Int.gcd m n = 1) Int.isCoprime_iff_gcd_eq_one.symm

@[simp, norm_cast]

Depends on / 依赖: Int.gcd, Int.isCoprime_iff_gcd_eq_one.symm, decidable_of_iff, isCoprime_iff_gcd_eq_one
-/
instance : DecidableRel (IsCoprime : Int -> Int -> Prop) :=
  fun m n => decidable_of_iff (Int.gcd m n = 1) Int.isCoprime_iff_gcd_eq_one.symm

@[simp, norm_cast]
/--
theorem `Nat.isCoprime_iff_coprime` / 定理 `Nat.isCoprime_iff_coprime`

English:
theorem Nat.isCoprime_iff_coprime
  given: {m n : Nat}
  statement: IsCoprime (m : Int) n ↔ Nat.Coprime m n
  proof: by
  rw [Int.isCoprime_iff_gcd_eq_one]; rw [Int.gcd_natCast_natCast]

alias ⟨IsCoprime.natCoprime, Nat.Coprime.isCoprime⟩ := Nat.isCoprime_iff_coprime

中文:
定理 自然数.isCoprime_iff_coprime
  条件: {m n : 自然数}
  结论: IsCoprime (m : 整数) n ↔ 自然数.Coprime m n
  证明: by
  rw [Int.isCoprime_iff_gcd_eq_one]; rw [Int.gcd_natCast_natCast]

alias ⟨IsCoprime.natCoprime, Nat.Coprime.isCoprime⟩ := Nat.isCoprime_iff_coprime

Depends on / 依赖: Int.gcd_natCast_natCast, Int.isCoprime_iff_gcd_eq_one, gcd_natCast_natCast, isCoprime_iff_gcd_eq_one
-/
theorem Nat.isCoprime_iff_coprime {m n : Nat} : IsCoprime (m : Int) n ↔ Nat.Coprime m n := by
  rw [Int.isCoprime_iff_gcd_eq_one]; rw [Int.gcd_natCast_natCast]

alias ⟨IsCoprime.natCoprime, Nat.Coprime.isCoprime⟩ := Nat.isCoprime_iff_coprime

/--
theorem `Nat.Coprime.cast` / 定理 `Nat.Coprime.cast`

English:
theorem Nat.Coprime.cast
  given: {R : Type*} [CommRing R] {a b : Nat} (h : Nat.Coprime a b)
  proof: mod_cast h.isCoprime.intCast

中文:
定理 自然数.Coprime.cast
  条件: {R : 类型} [交换环 R] {a b : 自然数} (h : 自然数.Coprime a b)
  证明: mod_cast h.isCoprime.intCast

Depends on / 依赖: h.isCoprime.intCast, intCast, isCoprime, mod_cast
-/
theorem Nat.Coprime.cast {R : Type*} [CommRing R] {a b : Nat} (h : Nat.Coprime a b) :
    IsCoprime (a : R) (b : R) :=
  mod_cast h.isCoprime.intCast

/--
theorem `Rat.isCoprime_num_den` / 定理 `Rat.isCoprime_num_den`

English:
theorem Rat.isCoprime_num_den
  given: (x : Rat)
  statement: IsCoprime x.num x.den
  proof: x.reduced.cast.of_isCoprime_of_dvd_left Int.dvd_natAbs_self

中文:
定理 有理数.isCoprime_num_den
  条件: (x : 有理数)
  结论: IsCoprime x.num x.den
  证明: x.reduced.cast.of_isCoprime_of_dvd_left Int.dvd_natAbs_self

Depends on / 依赖: Int.dvd_natAbs_self, dvd_natAbs_self, of_isCoprime_of_dvd_left, reduced, x.reduced.cast.of_isCoprime_of_dvd_left
-/
theorem Rat.isCoprime_num_den (x : Rat) : IsCoprime x.num x.den :=
  x.reduced.cast.of_isCoprime_of_dvd_left Int.dvd_natAbs_self

/--
theorem `Int.isCoprime_gcdA` / 定理 `Int.isCoprime_gcdA`

English:
theorem Int.isCoprime_gcdA
  given: {x y : Int} (h : IsCoprime x y)
  statement: IsCoprime (x.gcdA y) y
  proof: by
  use x, x.gcdB y
  rwa [mul_comm _ y, ← Int.gcd_eq_gcd_ab, Nat.cast_eq_one, ← Int.isCoprime_iff_gcd_eq_one]

中文:
定理 整数.isCoprime_gcdA
  条件: {x y : 整数} (h : IsCoprime x y)
  结论: IsCoprime (x.gcdA y) y
  证明: by
  use x, x.gcdB y
  rwa [mul_comm _ y, ← Int.gcd_eq_gcd_ab, Nat.cast_eq_one, ← Int.isCoprime_iff_gcd_eq_one]

Depends on / 依赖: Int.gcd_eq_gcd_ab, Int.isCoprime_iff_gcd_eq_one, Nat.cast_eq_one, cast_eq_one, gcd_eq_gcd_ab, isCoprime_iff_gcd_eq_one, mul_comm, x.gcdB
-/
theorem Int.isCoprime_gcdA {x y : Int} (h : IsCoprime x y) : IsCoprime (x.gcdA y) y := by
  use x, x.gcdB y
  rwa [mul_comm _ y, ← Int.gcd_eq_gcd_ab, Nat.cast_eq_one, ← Int.isCoprime_iff_gcd_eq_one]

/--
theorem `Int.isCoprime_gcdB` / 定理 `Int.isCoprime_gcdB`

English:
theorem Int.isCoprime_gcdB
  given: {x y : Int} (h : IsCoprime x y)
  statement: IsCoprime (x.gcdB y) x
  proof: by
  use y, x.gcdA y
  rwa [add_comm, mul_comm, ← Int.gcd_eq_gcd_ab, Nat.cast_eq_one, ← Int.isCoprime_iff_gcd_eq_one]

中文:
定理 整数.isCoprime_gcdB
  条件: {x y : 整数} (h : IsCoprime x y)
  结论: IsCoprime (x.gcdB y) x
  证明: by
  use y, x.gcdA y
  rwa [add_comm, mul_comm, ← Int.gcd_eq_gcd_ab, Nat.cast_eq_one, ← Int.isCoprime_iff_gcd_eq_one]

Depends on / 依赖: Int.gcd_eq_gcd_ab, Int.isCoprime_iff_gcd_eq_one, Nat.cast_eq_one, add_comm, cast_eq_one, gcd_eq_gcd_ab, isCoprime_iff_gcd_eq_one, mul_comm, x.gcdA
-/
theorem Int.isCoprime_gcdB {x y : Int} (h : IsCoprime x y) : IsCoprime (x.gcdB y) x := by
  use y, x.gcdA y
  rwa [add_comm, mul_comm, ← Int.gcd_eq_gcd_ab, Nat.cast_eq_one, ← Int.isCoprime_iff_gcd_eq_one]

/--
theorem `ne_zero_or_ne_zero_of_nat_coprime` / 定理 `ne_zero_or_ne_zero_of_nat_coprime`

English:
theorem ne_zero_or_ne_zero_of_nat_coprime
  statement: {A : Type u} [CommRing A] [Nontrivial A] {a b : Nat}
  proof: IsCoprime.ne_zero_or_ne_zero (R := A) by
    simpa only [map_natCast] using IsCoprime.map (Nat.Coprime.isCoprime h) (Int.castRingHom A)

中文:
定理 ne_zero_or_ne_zero_of_nat_coprime
  结论: {A : 类型u} [交换环 A] [非平凡 A] {a b : 自然数}
  证明: IsCoprime.ne_zero_or_ne_zero (R := A) by
    simpa only [map_natCast] using IsCoprime.map (Nat.Coprime.isCoprime h) (Int.castRingHom A)

Depends on / 依赖: Coprime, Int.castRingHom, IsCoprime, IsCoprime.map, IsCoprime.ne_zero_or_ne_zero, Nat.Coprime.isCoprime, castRingHom, isCoprime, map_natCast, ne_zero_or_ne_zero
-/
theorem ne_zero_or_ne_zero_of_nat_coprime {A : Type u} [CommRing A] [Nontrivial A] {a b : Nat}
    (h : Nat.Coprime a b) : (a : A) != 0 ∨ (b : A) != 0 :=
IsCoprime.ne_zero_or_ne_zero (R := A) by
    simpa only [map_natCast] using IsCoprime.map (Nat.Coprime.isCoprime h) (Int.castRingHom A)

/--
theorem `IsCoprime.prod_left` / 定理 `IsCoprime.prod_left`

English:
theorem IsCoprime.prod_left
  given: (h : forall i in t, IsCoprime (s i) x)
  statement: IsCoprime (∏ i in t, s i) x
  proof: by
  induction t using Finset.cons_induction with
  | empty => apply isCoprime_one_left
  | cons b t hbt ih =>
    rw [Finset.prod_cons]
    rw [Finset.forall_mem_cons] at h
    exact h.1.mul_left (ih h.2)

中文:
定理 IsCoprime.prod_left
  条件: (h : 对任意 i in t, IsCoprime (s i) x)
  结论: IsCoprime (∏ i in t, s i) x
  证明: by
  induction t using Finset.cons_induction with
  | empty => apply isCoprime_one_left
  | cons b t hbt ih =>
    rw [Finset.prod_cons]
    rw [Finset.forall_mem_cons] at h
    exact h.1.mul_left (ih h.2)

Depends on / 依赖: Finset, Finset.cons_induction, Finset.forall_mem_cons, Finset.prod_cons, cons_induction, forall_mem_cons, isCoprime_one_left, mul_left, prod_cons
-/
theorem IsCoprime.prod_left (h : forall i in t, IsCoprime (s i) x) : IsCoprime (∏ i in t, s i) x := by
  induction t using Finset.cons_induction with
  | empty => apply isCoprime_one_left
  | cons b t hbt ih =>
    rw [Finset.prod_cons]
    rw [Finset.forall_mem_cons] at h
    exact h.1.mul_left (ih h.2)

/--
theorem `IsCoprime.prod_right` / 定理 `IsCoprime.prod_right`

English:
theorem IsCoprime.prod_right
  statement: (forall i in t, IsCoprime x (s i)) -> IsCoprime x (∏ i in t, s i)
  proof: by
  simpa only [isCoprime_comm] using IsCoprime.prod_left (R := R)

中文:
定理 IsCoprime.prod_right
  结论: (对任意 i in t, IsCoprime x (s i)) -> IsCoprime x (∏ i in t, s i)
  证明: by
  simpa only [isCoprime_comm] using IsCoprime.prod_left (R := R)

Depends on / 依赖: IsCoprime, IsCoprime.prod_left, isCoprime_comm, prod_left
-/
theorem IsCoprime.prod_right : (forall i in t, IsCoprime x (s i)) -> IsCoprime x (∏ i in t, s i) := by
  simpa only [isCoprime_comm] using IsCoprime.prod_left (R := R)

/--
theorem `IsCoprime.prod_left_iff` / 定理 `IsCoprime.prod_left_iff`

English:
theorem IsCoprime.prod_left_iff
  statement: IsCoprime (∏ i in t, s i) x ↔ forall i in t, IsCoprime (s i) x
  proof: by
  classical
  refine Finset.induction_on t (iff_of_true isCoprime_one_left fun _ => by simp) fun b t hbt ih => ?_
  rw [Finset.prod_insert hbt]; rw [IsCoprime.mul_left_iff]; rw [ih]; rw [Finset.forall_mem_insert]

中文:
定理 IsCoprime.prod_left_iff
  结论: IsCoprime (∏ i in t, s i) x ↔ 对任意 i in t, IsCoprime (s i) x
  证明: by
  classical
  refine Finset.induction_on t (iff_of_true isCoprime_one_left fun _ => by simp) fun b t hbt ih => ?_
  rw [Finset.prod_insert hbt]; rw [IsCoprime.mul_left_iff]; rw [ih]; rw [Finset.forall_mem_insert]

Depends on / 依赖: Finset, Finset.forall_mem_insert, Finset.induction_on, Finset.prod_insert, IsCoprime, IsCoprime.mul_left_iff, classical, forall_mem_insert, iff_of_true, induction_on, isCoprime_one_left, mul_left_iff, prod_insert
-/
theorem IsCoprime.prod_left_iff : IsCoprime (∏ i in t, s i) x ↔ forall i in t, IsCoprime (s i) x := by
  classical
  refine Finset.induction_on t (iff_of_true isCoprime_one_left fun _ => by simp) fun b t hbt ih => ?_
  rw [Finset.prod_insert hbt]; rw [IsCoprime.mul_left_iff]; rw [ih]; rw [Finset.forall_mem_insert]

/--
theorem `IsCoprime.prod_right_iff` / 定理 `IsCoprime.prod_right_iff`

English:
theorem IsCoprime.prod_right_iff
  statement: IsCoprime x (∏ i in t, s i) ↔ forall i in t, IsCoprime x (s i)
  proof: by
  simpa only [isCoprime_comm] using IsCoprime.prod_left_iff (R := R)

中文:
定理 IsCoprime.prod_right_iff
  结论: IsCoprime x (∏ i in t, s i) ↔ 对任意 i in t, IsCoprime x (s i)
  证明: by
  simpa only [isCoprime_comm] using IsCoprime.prod_left_iff (R := R)

Depends on / 依赖: IsCoprime, IsCoprime.prod_left_iff, isCoprime_comm, prod_left_iff
-/
theorem IsCoprime.prod_right_iff : IsCoprime x (∏ i in t, s i) ↔ forall i in t, IsCoprime x (s i) := by
  simpa only [isCoprime_comm] using IsCoprime.prod_left_iff (R := R)

/--
theorem `IsCoprime.of_prod_left` / 定理 `IsCoprime.of_prod_left`

English:
theorem IsCoprime.of_prod_left
  given: (H1 : IsCoprime (∏ i in t, s i) x) (i : I) (hit : i in t)
  proof: IsCoprime.prod_left_iff.1 H1 i hit

中文:
定理 IsCoprime.of_prod_left
  条件: (H1 : IsCoprime (∏ i in t, s i) x) (i : I) (hit : i in t)
  证明: IsCoprime.prod_left_iff.1 H1 i hit

Depends on / 依赖: IsCoprime, IsCoprime.prod_left_iff, prod_left_iff
-/
theorem IsCoprime.of_prod_left (H1 : IsCoprime (∏ i in t, s i) x) (i : I) (hit : i in t) :
    IsCoprime (s i) x :=
  IsCoprime.prod_left_iff.1 H1 i hit

/--
theorem `IsCoprime.of_prod_right` / 定理 `IsCoprime.of_prod_right`

English:
theorem IsCoprime.of_prod_right
  given: (H1 : IsCoprime x (∏ i in t, s i)) (i : I) (hit : i in t)
  proof: IsCoprime.prod_right_iff.1 H1 i hit

中文:
定理 IsCoprime.of_prod_right
  条件: (H1 : IsCoprime x (∏ i in t, s i)) (i : I) (hit : i in t)
  证明: IsCoprime.prod_right_iff.1 H1 i hit

Depends on / 依赖: IsCoprime, IsCoprime.prod_right_iff, prod_right_iff
-/
theorem IsCoprime.of_prod_right (H1 : IsCoprime x (∏ i in t, s i)) (i : I) (hit : i in t) :
    IsCoprime x (s i) :=
  IsCoprime.prod_right_iff.1 H1 i hit

/--
theorem `Finset.prod_dvd_of_coprime` / 定理 `Finset.prod_dvd_of_coprime`

English:
theorem Finset.prod_dvd_of_coprime
  proof: by
  classical
  induction t using Finset.induction_on with
  | empty => simp
  | insert a r har ih =>
    rw [Finset.prod_insert har]
    refine IsCoprime.mul_dvd ?_ ?_ ?_
    · refine IsCoprime.prod_right fun i hir => ?_
      exact Hs (by simp) (by simp [hir]) (ne_of_mem_of_not_mem hir har).symm


中文:
定理 有限集.prod_dvd_of_coprime
  证明: by
  classical
  induction t using Finset.induction_on with
  | empty => simp
  | insert a r har ih =>
    rw [Finset.prod_insert har]
    refine IsCoprime.mul_dvd ?_ ?_ ?_
    · refine IsCoprime.prod_right fun i hir => ?_
      exact Hs (by simp) (by simp [hir]) (ne_of_mem_of_not_mem hir har).symm


Depends on / 依赖: Finset, Finset.coe_insert, Finset.induction_on, Finset.mem_insert_of_mem, Finset.mem_insert_self, Finset.prod_insert, Hs.mono, IsCoprime, IsCoprime.mul_dvd, IsCoprime.prod_right, Set.subset_insert, classical, coe_insert, induction_on, insert, mem_insert_of_mem, mem_insert_self, mul_dvd, ne_of_mem_of_not_mem, prod_insert
-/
theorem Finset.prod_dvd_of_coprime
    (Hs : (t : Set I).Pairwise (IsCoprime on s)) (Hs1 : (forall i in t, s i ∣ z)) :
    (∏ x in t, s x) ∣ z := by
  classical
  induction t using Finset.induction_on with
  | empty => simp
  | insert a r har ih =>
    rw [Finset.prod_insert har]
    refine IsCoprime.mul_dvd ?_ ?_ ?_
    · refine IsCoprime.prod_right fun i hir => ?_
      exact Hs (by simp) (by simp [hir]) (ne_of_mem_of_not_mem hir har).symm
    · exact Hs1 a (Finset.mem_insert_self a r)
· refine ih (Hs.mono ?_) fun i hi => Hs1 i Finset.mem_insert_of_mem hi
      simp only [Finset.coe_insert, Set.subset_insert]

/--
theorem `Fintype.prod_dvd_of_coprime` / 定理 `Fintype.prod_dvd_of_coprime`

English:
theorem Fintype.prod_dvd_of_coprime
  statement: [Fintype I] (Hs : Pairwise (IsCoprime on s))
  proof: Finset.prod_dvd_of_coprime (Hs.set_pairwise _) fun i _ => Hs1 i

中文:
定理 有限类型.prod_dvd_of_coprime
  结论: [有限类型 I] (Hs : 两两 (IsCoprime on s))
  证明: Finset.prod_dvd_of_coprime (Hs.set_pairwise _) fun i _ => Hs1 i

Depends on / 依赖: Finset, Finset.prod_dvd_of_coprime, Hs.set_pairwise, prod_dvd_of_coprime, set_pairwise
-/
theorem Fintype.prod_dvd_of_coprime [Fintype I] (Hs : Pairwise (IsCoprime on s))
    (Hs1 : forall i, s i ∣ z) : (∏ x, s x) ∣ z :=
  Finset.prod_dvd_of_coprime (Hs.set_pairwise _) fun i _ => Hs1 i

end

open Finset

/--
theorem `exists_sum_eq_one_iff_pairwise_coprime` / 定理 `exists_sum_eq_one_iff_pairwise_coprime`

English:
theorem exists_sum_eq_one_iff_pairwise_coprime
  given: [DecidableEq I] (h : t.Nonempty)
  proof: by
  induction h using Finset.Nonempty.cons_induction with
  | singleton =>
    simp [exists_apply_eq, Pairwise, Function.onFun]
  | cons a t hat h ih =>
    rw [pairwise_cons']
    have mem : forall x in t, a in insert a t \ {x} := fun x hx => by
      rw [mem_sdiff]; rw [mem_singleton]
      exact

中文:
定理 存在_sum_eq_one_iff_pairwise_coprime
  条件: [DecidableEq I] (h : t.非空)
  证明: by
  induction h using Finset.Nonempty.cons_induction with
  | singleton =>
    simp [exists_apply_eq, Pairwise, Function.onFun]
  | cons a t hat h ih =>
    rw [pairwise_cons']
    have mem : forall x in t, a in insert a t \ {x} := fun x hx => by
      rw [mem_sdiff]; rw [mem_singleton]
      exact

Depends on / 依赖: Finset, Finset.Nonempty.cons_induction, Function, Function.onFun, Nonempty, Pairwise, Pi.single, cons_eq_insert, cons_induction, erase_insert, exists_apply_eq, h.choose, ih.mp, insert, mem_insert_self, mem_sdiff, mem_singleton, pairwise_cons, sdiff_singleton_eq_erase, single
-/
theorem exists_sum_eq_one_iff_pairwise_coprime [DecidableEq I] (h : t.Nonempty) :
    (exists μ : I -> R, (∑ i in t, μ i * ∏ j in t \ {i}, s j) = 1) ↔
      Pairwise (IsCoprime on fun i : t => s i) := by
  induction h using Finset.Nonempty.cons_induction with
  | singleton =>
    simp [exists_apply_eq, Pairwise, Function.onFun]
  | cons a t hat h ih =>
    rw [pairwise_cons']
    have mem : forall x in t, a in insert a t \ {x} := fun x hx => by
      rw [mem_sdiff]; rw [mem_singleton]
      exact ⟨mem_insert_self _ _, fun ha => hat (ha ▸ hx)⟩
    constructor
    · rintro ⟨μ, hμ⟩
      rw [sum_cons]; rw [cons_eq_insert]; rw [sdiff_singleton_eq_erase]; rw [erase_insert hat] at hμ
      refine ⟨ih.mp ⟨Pi.single h.choose (μ a * s h.choose) + μ * fun _ => s a, ?_⟩, fun b hb => ?_⟩
      · rw [prod_eq_mul_prod_sdiff_singleton_of_mem h.choose_spec, ← mul_assoc, ←
          @if_pos _ _ h.choose_spec R (_ * _) 0, ← sum_pi_single', ← sum_add_distrib] at hμ
        rw [← hμ]; rw [sum_congr rfl]
        intro x hx
        convert! add_mul (R := R) _ _ _ using 2
        · by_cases hx : x = h.choose
          · rw [hx, Pi.single_eq_same, Pi.single_eq_same]
          · rw [Pi.single_eq_of_ne hx, Pi.single_eq_of_ne hx, zero_mul]
        · convert! (mul_assoc _ _ _).symm
          rw [prod_eq_prod_sdiff_singleton_mul (mem x hx)]; rw [mul_comm]; rw [sdiff_sdiff_comm]; rw [sdiff_singleton_eq_erase a]; rw [erase_insert hat]
      · have : IsCoprime (s b) (s a) :=
          ⟨μ a * ∏ i in t \ {b}, s i, ∑ i in t, μ i * ∏ j in t \ {i}, s j, ?_⟩
        · exact ⟨this.symm, this⟩
        rw [mul_assoc]; rw [← prod_eq_prod_sdiff_singleton_mul hb]; rw [sum_mul]; rw [← hμ]; rw [sum_congr rfl]
        intro x hx
        rw [mul_assoc]
        congr
        rw [prod_eq_prod_sdiff_singleton_mul (mem x hx) _]
        congr 2
        rw [sdiff_sdiff_comm]; rw [sdiff_singleton_eq_erase a]; rw [erase_insert hat]
    · rintro ⟨hs, Hb⟩
      obtain ⟨μ, hμ⟩ := ih.mpr hs
      obtain ⟨u, v, huv⟩ := IsCoprime.prod_left fun b hb => (Hb b hb).right
      use fun i => if i = a then u else v * μ i
      have hμ' : (∑ i in t, v * ((μ i * ∏ j in t \ {i}, s j) * s a)) = v * s a := by
        rw [← mul_sum]; rw [← sum_mul]; rw [hμ]; rw [one_mul]
      rw [sum_cons]; rw [cons_eq_insert]; rw [sdiff_singleton_eq_erase]; rw [erase_insert hat]
      simp only [↓reduceIte, ite_mul]
      rw [← huv]; rw [← hμ']; rw [sum_congr rfl]
      intro x hx
      rw [mul_assoc]; rw [if_neg fun ha : x = a => hat (ha.casesOn hx)]
      rw [mul_assoc]
      congr
      rw [prod_eq_prod_sdiff_singleton_mul (mem x hx) _]
      congr 2
      rw [sdiff_sdiff_comm]; rw [sdiff_singleton_eq_erase a]; rw [erase_insert hat]

/--
theorem `exists_sum_eq_one_iff_pairwise_coprime'` / 定理 `exists_sum_eq_one_iff_pairwise_coprime'`

English:
theorem exists_sum_eq_one_iff_pairwise_coprime'
  given: [Fintype I] [Nonempty I] [DecidableEq I]
  proof: by
  convert! exists_sum_eq_one_iff_pairwise_coprime Finset.univ_nonempty (s := s) using 1
  simp only [pairwise_subtype_iff_pairwise_finset', coe_univ, Set.pairwise_univ]

中文:
定理 存在_sum_eq_one_iff_pairwise_coprime'
  条件: [有限类型 I] [非空 I] [DecidableEq I]
  证明: by
  convert! exists_sum_eq_one_iff_pairwise_coprime Finset.univ_nonempty (s := s) using 1
  simp only [pairwise_subtype_iff_pairwise_finset', coe_univ, Set.pairwise_univ]

Depends on / 依赖: Finset, Finset.univ_nonempty, Set.pairwise_univ, coe_univ, convert, exists_sum_eq_one_iff_pairwise_coprime, pairwise_subtype_iff_pairwise_finset, pairwise_univ, univ_nonempty
-/
theorem exists_sum_eq_one_iff_pairwise_coprime' [Fintype I] [Nonempty I] [DecidableEq I] :
    (exists μ : I -> R, (∑ i : I, μ i * ∏ j in {i}ᶜ, s j) = 1) ↔ Pairwise (IsCoprime on s) := by
  convert! exists_sum_eq_one_iff_pairwise_coprime Finset.univ_nonempty (s := s) using 1
  simp only [pairwise_subtype_iff_pairwise_finset', coe_univ, Set.pairwise_univ]

/--
theorem `pairwise_coprime_iff_coprime_prod` / 定理 `pairwise_coprime_iff_coprime_prod`

English:
theorem pairwise_coprime_iff_coprime_prod
  given: [DecidableEq I]
  proof: by
  rw [Finset.pairwise_subtype_iff_pairwise_finset']
  refine ⟨fun hp i hi => IsCoprime.prod_right_iff.mpr fun j hj => ?_, fun hp => ?_⟩
  · rw [Finset.mem_sdiff, Finset.mem_singleton] at hj
    exact (hp hj.1 hi hj.2).symm
  · rintro i hi j hj h
    apply IsCoprime.prod_right_iff.mp (hp i hi)
   

中文:
定理 pairwise_coprime_iff_coprime_prod
  条件: [DecidableEq I]
  证明: by
  rw [Finset.pairwise_subtype_iff_pairwise_finset']
  refine ⟨fun hp i hi => IsCoprime.prod_right_iff.mpr fun j hj => ?_, fun hp => ?_⟩
  · rw [Finset.mem_sdiff, Finset.mem_singleton] at hj
    exact (hp hj.1 hi hj.2).symm
  · rintro i hi j hj h
    apply IsCoprime.prod_right_iff.mp (hp i hi)
   

Depends on / 依赖: Finset, Finset.mem_sdiff, Finset.mem_sdiff.mpr, Finset.mem_singleton, Finset.mem_singleton.mp, Finset.pairwise_subtype_iff_pairwise_finset, IsCoprime, IsCoprime.prod_right_iff.mp, IsCoprime.prod_right_iff.mpr, mem_sdiff, mem_singleton, pairwise_subtype_iff_pairwise_finset, prod_right_iff
-/
theorem pairwise_coprime_iff_coprime_prod [DecidableEq I] :
    Pairwise (IsCoprime on fun i : t => s i) ↔ forall i in t, IsCoprime (s i) (∏ j in t \ {i}, s j) := by
  rw [Finset.pairwise_subtype_iff_pairwise_finset']
  refine ⟨fun hp i hi => IsCoprime.prod_right_iff.mpr fun j hj => ?_, fun hp => ?_⟩
  · rw [Finset.mem_sdiff, Finset.mem_singleton] at hj
    exact (hp hj.1 hi hj.2).symm
  · rintro i hi j hj h
    apply IsCoprime.prod_right_iff.mp (hp i hi)
    exact Finset.mem_sdiff.mpr ⟨hj, fun f => h (Finset.mem_singleton.mp f).symm⟩

variable {m n : Nat}

/--
theorem `IsCoprime.pow_left` / 定理 `IsCoprime.pow_left`

English:
theorem IsCoprime.pow_left
  given: (H : IsCoprime x y)
  statement: IsCoprime (x ^ m) y
  proof: by
  rw [← Finset.card_range m]; rw [← Finset.prod_const]
  exact IsCoprime.prod_left fun _ _ => H

中文:
定理 IsCoprime.pow_left
  条件: (H : IsCoprime x y)
  结论: IsCoprime (x ^ m) y
  证明: by
  rw [← Finset.card_range m]; rw [← Finset.prod_const]
  exact IsCoprime.prod_left fun _ _ => H

Depends on / 依赖: Finset, Finset.card_range, Finset.prod_const, IsCoprime, IsCoprime.prod_left, card_range, prod_const, prod_left
-/
theorem IsCoprime.pow_left (H : IsCoprime x y) : IsCoprime (x ^ m) y := by
  rw [← Finset.card_range m]; rw [← Finset.prod_const]
  exact IsCoprime.prod_left fun _ _ => H

/--
theorem `IsCoprime.pow_right` / 定理 `IsCoprime.pow_right`

English:
theorem IsCoprime.pow_right
  given: (H : IsCoprime x y)
  statement: IsCoprime x (y ^ n)
  proof: by
  rw [← Finset.card_range n]; rw [← Finset.prod_const]
  exact IsCoprime.prod_right fun _ _ => H

中文:
定理 IsCoprime.pow_right
  条件: (H : IsCoprime x y)
  结论: IsCoprime x (y ^ n)
  证明: by
  rw [← Finset.card_range n]; rw [← Finset.prod_const]
  exact IsCoprime.prod_right fun _ _ => H

Depends on / 依赖: Finset, Finset.card_range, Finset.prod_const, IsCoprime, IsCoprime.prod_right, card_range, prod_const, prod_right
-/
theorem IsCoprime.pow_right (H : IsCoprime x y) : IsCoprime x (y ^ n) := by
  rw [← Finset.card_range n]; rw [← Finset.prod_const]
  exact IsCoprime.prod_right fun _ _ => H

/--
theorem `IsCoprime.pow` / 定理 `IsCoprime.pow`

English:
theorem IsCoprime.pow
  given: (H : IsCoprime x y)
  statement: IsCoprime (x ^ m) (y ^ n)
  proof: H.pow_left.pow_right

中文:
定理 IsCoprime.pow
  条件: (H : IsCoprime x y)
  结论: IsCoprime (x ^ m) (y ^ n)
  证明: H.pow_left.pow_right

Depends on / 依赖: H.pow_left.pow_right, pow_left, pow_right
-/
theorem IsCoprime.pow (H : IsCoprime x y) : IsCoprime (x ^ m) (y ^ n) :=
  H.pow_left.pow_right

/--
theorem `IsCoprime.pow_left_iff` / 定理 `IsCoprime.pow_left_iff`

English:
theorem IsCoprime.pow_left_iff
  given: (hm : 0 < m)
  statement: IsCoprime (x ^ m) y ↔ IsCoprime x y
  proof: by
  refine ⟨fun h => ?_, IsCoprime.pow_left⟩
  rw [← Finset.card_range m]; rw [← Finset.prod_const] at h
  exact h.of_prod_left 0 (Finset.mem_range.mpr hm)

中文:
定理 IsCoprime.pow_left_iff
  条件: (hm : 0 < m)
  结论: IsCoprime (x ^ m) y ↔ IsCoprime x y
  证明: by
  refine ⟨fun h => ?_, IsCoprime.pow_left⟩
  rw [← Finset.card_range m]; rw [← Finset.prod_const] at h
  exact h.of_prod_left 0 (Finset.mem_range.mpr hm)

Depends on / 依赖: Finset, Finset.card_range, Finset.mem_range.mpr, Finset.prod_const, IsCoprime, IsCoprime.pow_left, card_range, h.of_prod_left, mem_range, of_prod_left, pow_left, prod_const
-/
theorem IsCoprime.pow_left_iff (hm : 0 < m) : IsCoprime (x ^ m) y ↔ IsCoprime x y := by
  refine ⟨fun h => ?_, IsCoprime.pow_left⟩
  rw [← Finset.card_range m]; rw [← Finset.prod_const] at h
  exact h.of_prod_left 0 (Finset.mem_range.mpr hm)

/--
theorem `IsCoprime.pow_right_iff` / 定理 `IsCoprime.pow_right_iff`

English:
theorem IsCoprime.pow_right_iff
  given: (hm : 0 < m)
  statement: IsCoprime x (y ^ m) ↔ IsCoprime x y
  proof: isCoprime_comm.trans (IsCoprime.pow_left_iff hm).trans isCoprime_comm

中文:
定理 IsCoprime.pow_right_iff
  条件: (hm : 0 < m)
  结论: IsCoprime x (y ^ m) ↔ IsCoprime x y
  证明: isCoprime_comm.trans (IsCoprime.pow_left_iff hm).trans isCoprime_comm

Depends on / 依赖: IsCoprime, IsCoprime.pow_left_iff, isCoprime_comm, isCoprime_comm.trans, pow_left_iff
-/
theorem IsCoprime.pow_right_iff (hm : 0 < m) : IsCoprime x (y ^ m) ↔ IsCoprime x y :=
isCoprime_comm.trans (IsCoprime.pow_left_iff hm).trans isCoprime_comm

/--
theorem `IsCoprime.pow_iff` / 定理 `IsCoprime.pow_iff`

English:
theorem IsCoprime.pow_iff
  given: (hm : 0 < m) (hn : 0 < n)
  statement: IsCoprime (x ^ m) (y ^ n) ↔ IsCoprime x y
  proof: (IsCoprime.pow_left_iff hm).trans IsCoprime.pow_right_iff hn

中文:
定理 IsCoprime.pow_iff
  条件: (hm : 0 < m) (hn : 0 < n)
  结论: IsCoprime (x ^ m) (y ^ n) ↔ IsCoprime x y
  证明: (IsCoprime.pow_left_iff hm).trans IsCoprime.pow_right_iff hn

Depends on / 依赖: IsCoprime, IsCoprime.pow_left_iff, IsCoprime.pow_right_iff, pow_left_iff, pow_right_iff
-/
theorem IsCoprime.pow_iff (hm : 0 < m) (hn : 0 < n) : IsCoprime (x ^ m) (y ^ n) ↔ IsCoprime x y :=
(IsCoprime.pow_left_iff hm).trans IsCoprime.pow_right_iff hn

end IsCoprime

section RelPrime

variable {α I} [CommMonoid α] [DecompositionMonoid α] {x y z : α} {s : I -> α} {t : Finset I}

/--
theorem `IsRelPrime.prod_left` / 定理 `IsRelPrime.prod_left`

English:
theorem IsRelPrime.prod_left
  statement: (forall i in t, IsRelPrime (s i) x) -> IsRelPrime (∏ i in t, s i) x
  proof: by
  classical
  refine Finset.induction_on t (fun _ => isRelPrime_one_left) fun b t hbt ih H => ?_
  rw [Finset.prod_insert hbt]
  rw [Finset.forall_mem_insert] at H
  exact H.1.mul_left (ih H.2)

中文:
定理 IsRelPrime.prod_left
  结论: (对任意 i in t, IsRelPrime (s i) x) -> IsRelPrime (∏ i in t, s i) x
  证明: by
  classical
  refine Finset.induction_on t (fun _ => isRelPrime_one_left) fun b t hbt ih H => ?_
  rw [Finset.prod_insert hbt]
  rw [Finset.forall_mem_insert] at H
  exact H.1.mul_left (ih H.2)

Depends on / 依赖: Finset, Finset.forall_mem_insert, Finset.induction_on, Finset.prod_insert, classical, forall_mem_insert, induction_on, isRelPrime_one_left, mul_left, prod_insert
-/
theorem IsRelPrime.prod_left : (forall i in t, IsRelPrime (s i) x) -> IsRelPrime (∏ i in t, s i) x := by
  classical
  refine Finset.induction_on t (fun _ => isRelPrime_one_left) fun b t hbt ih H => ?_
  rw [Finset.prod_insert hbt]
  rw [Finset.forall_mem_insert] at H
  exact H.1.mul_left (ih H.2)

/--
theorem `IsRelPrime.prod_right` / 定理 `IsRelPrime.prod_right`

English:
theorem IsRelPrime.prod_right
  statement: (forall i in t, IsRelPrime x (s i)) -> IsRelPrime x (∏ i in t, s i)
  proof: by
  simpa only [isRelPrime_comm] using IsRelPrime.prod_left (α := α)

中文:
定理 IsRelPrime.prod_right
  结论: (对任意 i in t, IsRelPrime x (s i)) -> IsRelPrime x (∏ i in t, s i)
  证明: by
  simpa only [isRelPrime_comm] using IsRelPrime.prod_left (α := α)

Depends on / 依赖: IsRelPrime, IsRelPrime.prod_left, isRelPrime_comm, prod_left
-/
theorem IsRelPrime.prod_right : (forall i in t, IsRelPrime x (s i)) -> IsRelPrime x (∏ i in t, s i) := by
  simpa only [isRelPrime_comm] using IsRelPrime.prod_left (α := α)

/--
theorem `IsRelPrime.prod_left_iff` / 定理 `IsRelPrime.prod_left_iff`

English:
theorem IsRelPrime.prod_left_iff
  statement: IsRelPrime (∏ i in t, s i) x ↔ forall i in t, IsRelPrime (s i) x
  proof: by
  classical
  refine Finset.induction_on t (iff_of_true isRelPrime_one_left fun _ => by simp) fun b t hbt ih => ?_
  rw [Finset.prod_insert hbt]; rw [IsRelPrime.mul_left_iff]; rw [ih]; rw [Finset.forall_mem_insert]

中文:
定理 IsRelPrime.prod_left_iff
  结论: IsRelPrime (∏ i in t, s i) x ↔ 对任意 i in t, IsRelPrime (s i) x
  证明: by
  classical
  refine Finset.induction_on t (iff_of_true isRelPrime_one_left fun _ => by simp) fun b t hbt ih => ?_
  rw [Finset.prod_insert hbt]; rw [IsRelPrime.mul_left_iff]; rw [ih]; rw [Finset.forall_mem_insert]

Depends on / 依赖: Finset, Finset.forall_mem_insert, Finset.induction_on, Finset.prod_insert, IsRelPrime, IsRelPrime.mul_left_iff, classical, forall_mem_insert, iff_of_true, induction_on, isRelPrime_one_left, mul_left_iff, prod_insert
-/
theorem IsRelPrime.prod_left_iff : IsRelPrime (∏ i in t, s i) x ↔ forall i in t, IsRelPrime (s i) x := by
  classical
  refine Finset.induction_on t (iff_of_true isRelPrime_one_left fun _ => by simp) fun b t hbt ih => ?_
  rw [Finset.prod_insert hbt]; rw [IsRelPrime.mul_left_iff]; rw [ih]; rw [Finset.forall_mem_insert]

/--
theorem `IsRelPrime.prod_right_iff` / 定理 `IsRelPrime.prod_right_iff`

English:
theorem IsRelPrime.prod_right_iff
  statement: IsRelPrime x (∏ i in t, s i) ↔ forall i in t, IsRelPrime x (s i)
  proof: by
  simpa only [isRelPrime_comm] using IsRelPrime.prod_left_iff (α := α)

中文:
定理 IsRelPrime.prod_right_iff
  结论: IsRelPrime x (∏ i in t, s i) ↔ 对任意 i in t, IsRelPrime x (s i)
  证明: by
  simpa only [isRelPrime_comm] using IsRelPrime.prod_left_iff (α := α)

Depends on / 依赖: IsRelPrime, IsRelPrime.prod_left_iff, isRelPrime_comm, prod_left_iff
-/
theorem IsRelPrime.prod_right_iff : IsRelPrime x (∏ i in t, s i) ↔ forall i in t, IsRelPrime x (s i) := by
  simpa only [isRelPrime_comm] using IsRelPrime.prod_left_iff (α := α)

/--
theorem `IsRelPrime.of_prod_left` / 定理 `IsRelPrime.of_prod_left`

English:
theorem IsRelPrime.of_prod_left
  given: (H1 : IsRelPrime (∏ i in t, s i) x) (i : I) (hit : i in t)
  proof: IsRelPrime.prod_left_iff.1 H1 i hit

中文:
定理 IsRelPrime.of_prod_left
  条件: (H1 : IsRelPrime (∏ i in t, s i) x) (i : I) (hit : i in t)
  证明: IsRelPrime.prod_left_iff.1 H1 i hit

Depends on / 依赖: IsRelPrime, IsRelPrime.prod_left_iff, prod_left_iff
-/
theorem IsRelPrime.of_prod_left (H1 : IsRelPrime (∏ i in t, s i) x) (i : I) (hit : i in t) :
    IsRelPrime (s i) x :=
  IsRelPrime.prod_left_iff.1 H1 i hit

/--
theorem `IsRelPrime.of_prod_right` / 定理 `IsRelPrime.of_prod_right`

English:
theorem IsRelPrime.of_prod_right
  given: (H1 : IsRelPrime x (∏ i in t, s i)) (i : I) (hit : i in t)
  proof: IsRelPrime.prod_right_iff.1 H1 i hit

中文:
定理 IsRelPrime.of_prod_right
  条件: (H1 : IsRelPrime x (∏ i in t, s i)) (i : I) (hit : i in t)
  证明: IsRelPrime.prod_right_iff.1 H1 i hit

Depends on / 依赖: IsRelPrime, IsRelPrime.prod_right_iff, prod_right_iff
-/
theorem IsRelPrime.of_prod_right (H1 : IsRelPrime x (∏ i in t, s i)) (i : I) (hit : i in t) :
    IsRelPrime x (s i) :=
  IsRelPrime.prod_right_iff.1 H1 i hit

/--
theorem `Finset.prod_dvd_of_isRelPrime` / 定理 `Finset.prod_dvd_of_isRelPrime`

English:
theorem Finset.prod_dvd_of_isRelPrime
  proof: by
  classical
  exact Finset.induction_on t (fun _ _ => one_dvd z)
    (by
      intro a r har ih Hs Hs1
      rw [Finset.prod_insert har]
      have aux1 : a in (↑(insert a r) : Set I) := Finset.mem_insert_self a r
      refine
        (IsRelPrime.prod_right fun i hir =>
Hs aux1 (Finset.mem_insert

中文:
定理 有限集.prod_dvd_of_isRelPrime
  证明: by
  classical
  exact Finset.induction_on t (fun _ _ => one_dvd z)
    (by
      intro a r har ih Hs Hs1
      rw [Finset.prod_insert har]
      have aux1 : a in (↑(insert a r) : Set I) := Finset.mem_insert_self a r
      refine
        (IsRelPrime.prod_right fun i hir =>
Hs aux1 (Finset.mem_insert

Depends on / 依赖: Finset, Finset.coe_insert, Finset.induction_on, Finset.mem_insert_of_mem, Finset.mem_insert_self, Finset.prod_insert, Hs.mono, IsRelPrime, IsRelPrime.prod_right, Set.subset_insert, classical, coe_insert, induction_on, insert, mem_insert_of_mem, mem_insert_self, mul_dvd, one_dvd, prod_insert, prod_right
-/
theorem Finset.prod_dvd_of_isRelPrime :
    (t : Set I).Pairwise (IsRelPrime on s) -> (forall i in t, s i ∣ z) -> (∏ x in t, s x) ∣ z := by
  classical
  exact Finset.induction_on t (fun _ _ => one_dvd z)
    (by
      intro a r har ih Hs Hs1
      rw [Finset.prod_insert har]
      have aux1 : a in (↑(insert a r) : Set I) := Finset.mem_insert_self a r
      refine
        (IsRelPrime.prod_right fun i hir =>
Hs aux1 (Finset.mem_insert_of_mem hir) by
                rintro rfl
                exact har hir).mul_dvd
          (Hs1 a aux1) (ih (Hs.mono ?_) fun i hi => Hs1 i <| Finset.mem_insert_of_mem hi)
      simp only [Finset.coe_insert, Set.subset_insert])

/--
theorem `Fintype.prod_dvd_of_isRelPrime` / 定理 `Fintype.prod_dvd_of_isRelPrime`

English:
theorem Fintype.prod_dvd_of_isRelPrime
  statement: [Fintype I] (Hs : Pairwise (IsRelPrime on s))
  proof: Finset.prod_dvd_of_isRelPrime (Hs.set_pairwise _) fun i _ => Hs1 i

中文:
定理 有限类型.prod_dvd_of_isRelPrime
  结论: [有限类型 I] (Hs : 两两 (IsRelPrime on s))
  证明: Finset.prod_dvd_of_isRelPrime (Hs.set_pairwise _) fun i _ => Hs1 i

Depends on / 依赖: Finset, Finset.prod_dvd_of_isRelPrime, Hs.set_pairwise, prod_dvd_of_isRelPrime, set_pairwise
-/
theorem Fintype.prod_dvd_of_isRelPrime [Fintype I] (Hs : Pairwise (IsRelPrime on s))
    (Hs1 : forall i, s i ∣ z) : (∏ x, s x) ∣ z :=
  Finset.prod_dvd_of_isRelPrime (Hs.set_pairwise _) fun i _ => Hs1 i

/--
theorem `pairwise_isRelPrime_iff_isRelPrime_prod` / 定理 `pairwise_isRelPrime_iff_isRelPrime_prod`

English:
theorem pairwise_isRelPrime_iff_isRelPrime_prod
  given: [DecidableEq I]
  proof: by
  refine ⟨fun hp i hi => IsRelPrime.prod_right_iff.mpr fun j hj => ?_, fun hp => ?_⟩
  · rw [Finset.mem_sdiff, Finset.mem_singleton] at hj
    obtain ⟨hj, ji⟩ := hj
    exact @hp ⟨i, hi⟩ ⟨j, hj⟩ fun h => ji (congrArg Subtype.val h).symm
  · rintro ⟨i, hi⟩ ⟨j, hj⟩ h
    apply IsRelPrime.prod_right

中文:
定理 pairwise_isRelPrime_iff_isRelPrime_prod
  条件: [DecidableEq I]
  证明: by
  refine ⟨fun hp i hi => IsRelPrime.prod_right_iff.mpr fun j hj => ?_, fun hp => ?_⟩
  · rw [Finset.mem_sdiff, Finset.mem_singleton] at hj
    obtain ⟨hj, ji⟩ := hj
    exact @hp ⟨i, hi⟩ ⟨j, hj⟩ fun h => ji (congrArg Subtype.val h).symm
  · rintro ⟨i, hi⟩ ⟨j, hj⟩ h
    apply IsRelPrime.prod_right

Depends on / 依赖: Finset, Finset.mem_sdiff, Finset.mem_singleton, IsRelPrime, IsRelPrime.prod_right_iff.mp, IsRelPrime.prod_right_iff.mpr, Subtype, Subtype.val, mem_sdiff, mem_singleton, prod_right_iff
-/
theorem pairwise_isRelPrime_iff_isRelPrime_prod [DecidableEq I] :
    Pairwise (IsRelPrime on fun i : t => s i) ↔ forall i in t, IsRelPrime (s i) (∏ j in t \ {i}, s j) := by
  refine ⟨fun hp i hi => IsRelPrime.prod_right_iff.mpr fun j hj => ?_, fun hp => ?_⟩
  · rw [Finset.mem_sdiff, Finset.mem_singleton] at hj
    obtain ⟨hj, ji⟩ := hj
    exact @hp ⟨i, hi⟩ ⟨j, hj⟩ fun h => ji (congrArg Subtype.val h).symm
  · rintro ⟨i, hi⟩ ⟨j, hj⟩ h
    apply IsRelPrime.prod_right_iff.mp (hp i hi)
    grind

namespace IsRelPrime

variable {m n : Nat}

/--
theorem `pow_left` / 定理 `pow_left`

English:
theorem pow_left
  given: (H : IsRelPrime x y)
  statement: IsRelPrime (x ^ m) y
  proof: by
  rw [← Finset.card_range m]; rw [← Finset.prod_const]
  exact IsRelPrime.prod_left fun _ _ => H

中文:
定理 pow_left
  条件: (H : IsRelPrime x y)
  结论: IsRelPrime (x ^ m) y
  证明: by
  rw [← Finset.card_range m]; rw [← Finset.prod_const]
  exact IsRelPrime.prod_left fun _ _ => H

Depends on / 依赖: Finset, Finset.card_range, Finset.prod_const, IsRelPrime, IsRelPrime.prod_left, card_range, prod_const, prod_left
-/
theorem pow_left (H : IsRelPrime x y) : IsRelPrime (x ^ m) y := by
  rw [← Finset.card_range m]; rw [← Finset.prod_const]
  exact IsRelPrime.prod_left fun _ _ => H

/--
theorem `pow_right` / 定理 `pow_right`

English:
theorem pow_right
  given: (H : IsRelPrime x y)
  statement: IsRelPrime x (y ^ n)
  proof: by
  rw [← Finset.card_range n]; rw [← Finset.prod_const]
  exact IsRelPrime.prod_right fun _ _ => H

中文:
定理 pow_right
  条件: (H : IsRelPrime x y)
  结论: IsRelPrime x (y ^ n)
  证明: by
  rw [← Finset.card_range n]; rw [← Finset.prod_const]
  exact IsRelPrime.prod_right fun _ _ => H

Depends on / 依赖: Finset, Finset.card_range, Finset.prod_const, IsRelPrime, IsRelPrime.prod_right, card_range, prod_const, prod_right
-/
theorem pow_right (H : IsRelPrime x y) : IsRelPrime x (y ^ n) := by
  rw [← Finset.card_range n]; rw [← Finset.prod_const]
  exact IsRelPrime.prod_right fun _ _ => H

/--
theorem `pow` / 定理 `pow`

English:
theorem pow
  given: (H : IsRelPrime x y)
  statement: IsRelPrime (x ^ m) (y ^ n)
  proof: H.pow_left.pow_right

中文:
定理 pow
  条件: (H : IsRelPrime x y)
  结论: IsRelPrime (x ^ m) (y ^ n)
  证明: H.pow_left.pow_right

Depends on / 依赖: H.pow_left.pow_right, pow_left, pow_right
-/
theorem pow (H : IsRelPrime x y) : IsRelPrime (x ^ m) (y ^ n) :=
  H.pow_left.pow_right

/--
theorem `pow_left_iff` / 定理 `pow_left_iff`

English:
theorem pow_left_iff
  given: (hm : 0 < m)
  statement: IsRelPrime (x ^ m) y ↔ IsRelPrime x y
  proof: by
  refine ⟨fun h => ?_, IsRelPrime.pow_left⟩
  rw [← Finset.card_range m]; rw [← Finset.prod_const] at h
  exact h.of_prod_left 0 (Finset.mem_range.mpr hm)

中文:
定理 pow_left_iff
  条件: (hm : 0 < m)
  结论: IsRelPrime (x ^ m) y ↔ IsRelPrime x y
  证明: by
  refine ⟨fun h => ?_, IsRelPrime.pow_left⟩
  rw [← Finset.card_range m]; rw [← Finset.prod_const] at h
  exact h.of_prod_left 0 (Finset.mem_range.mpr hm)

Depends on / 依赖: Finset, Finset.card_range, Finset.mem_range.mpr, Finset.prod_const, IsRelPrime, IsRelPrime.pow_left, card_range, h.of_prod_left, mem_range, of_prod_left, pow_left, prod_const
-/
theorem pow_left_iff (hm : 0 < m) : IsRelPrime (x ^ m) y ↔ IsRelPrime x y := by
  refine ⟨fun h => ?_, IsRelPrime.pow_left⟩
  rw [← Finset.card_range m]; rw [← Finset.prod_const] at h
  exact h.of_prod_left 0 (Finset.mem_range.mpr hm)

/--
theorem `pow_right_iff` / 定理 `pow_right_iff`

English:
theorem pow_right_iff
  given: (hm : 0 < m)
  statement: IsRelPrime x (y ^ m) ↔ IsRelPrime x y
  proof: isRelPrime_comm.trans (IsRelPrime.pow_left_iff hm).trans isRelPrime_comm

中文:
定理 pow_right_iff
  条件: (hm : 0 < m)
  结论: IsRelPrime x (y ^ m) ↔ IsRelPrime x y
  证明: isRelPrime_comm.trans (IsRelPrime.pow_left_iff hm).trans isRelPrime_comm

Depends on / 依赖: IsRelPrime, IsRelPrime.pow_left_iff, isRelPrime_comm, isRelPrime_comm.trans, pow_left_iff
-/
theorem pow_right_iff (hm : 0 < m) : IsRelPrime x (y ^ m) ↔ IsRelPrime x y :=
isRelPrime_comm.trans (IsRelPrime.pow_left_iff hm).trans isRelPrime_comm

/--
theorem `pow_iff` / 定理 `pow_iff`

English:
theorem pow_iff
  given: (hm : 0 < m) (hn : 0 < n)
  proof: (IsRelPrime.pow_left_iff hm).trans (IsRelPrime.pow_right_iff hn)

中文:
定理 pow_iff
  条件: (hm : 0 < m) (hn : 0 < n)
  证明: (IsRelPrime.pow_left_iff hm).trans (IsRelPrime.pow_right_iff hn)

Depends on / 依赖: IsRelPrime, IsRelPrime.pow_left_iff, IsRelPrime.pow_right_iff, pow_left_iff, pow_right_iff
-/
theorem pow_iff (hm : 0 < m) (hn : 0 < n) :
    IsRelPrime (x ^ m) (y ^ n) ↔ IsRelPrime x y :=
  (IsRelPrime.pow_left_iff hm).trans (IsRelPrime.pow_right_iff hn)

end IsRelPrime

end RelPrime
