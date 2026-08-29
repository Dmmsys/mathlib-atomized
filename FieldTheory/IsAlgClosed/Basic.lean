/-
Copyright (c) 2020 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import Mathlib.Algebra.Ring.Hom.InjSurj
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
public import Mathlib.FieldTheory.Extension
public import Mathlib.FieldTheory.Perfect
public import Mathlib.RingTheory.Localization.Integral

/-!
# Algebraically Closed Field

In this file we define the typeclass for algebraically closed fields and algebraic closures,
and prove some of their properties.

## Main Definitions

- `IsAlgClosed k` is the typeclass saying `k` is an algebraically closed field, i.e. every
  polynomial in `k` splits.

- `IsAlgClosure R K` is the typeclass saying `K` is an algebraic closure of `R`, where `R` is a
  commutative ring. This means that the map from `R` to `K` is injective, and `K` is
  algebraically closed and algebraic over `R`

- `IsAlgClosed.lift` is a map from an algebraic extension `L` of `R`, into any algebraically
  closed extension of `R`.

- `IsAlgClosure.equiv` is a proof that any two algebraic closures of the
  same field are isomorphic.

## Tags

algebraic closure, algebraically closed

## Main results

- `IsAlgClosure.of_splits`: if `K / k` is algebraic, and every monic irreducible polynomial over
  `k` splits in `K`, then `K` is algebraically closed (in fact an algebraic closure of `k`).
  For the stronger fact that only requires every such polynomial has a root in `K`,
  see `IsAlgClosure.of_exists_root`.

  Reference: <https://kconrad.math.uconn.edu/blurbs/galoistheory/algclosure.pdf>, Theorem 2

-/

@[expose] public section

universe u v w

open Module Polynomial

variable (k : Type u) [Field k]

/-- An algebraically closed field is one where every polynomial splits. Equivalently, all
non-constant polynomials have a root. See `IsAlgClosed.exists_root` and
`IsAlgClosed.of_exists_root`. -/
@[stacks 09GR "The definition of `IsAlgClosed` in mathlib is 09GR (4)"]
/--
Definition of `IsAlgClosed` / `IsAlgClosed` 的定义

English:
class IsAlgClosed
  parameters: : Prop where
  axioms and operations (1):
    - splits : forall p : k[X], p.Splits

中文:
类 是代数闭
  参数: : 命题 where
  公理与运算 (1 个):
    - splits : 对任意 p : k[X], p.Splits
-/
class IsAlgClosed : Prop where
  splits : forall p : k[X], p.Splits

/--
theorem `IsAlgClosed.splits_domain` / 定理 `IsAlgClosed.splits_domain`

English:
theorem IsAlgClosed.splits_domain
  statement: {k K : Type*} [Field k] [IsAlgClosed k] [Field K] {f : k ->+* K}
  proof: (IsAlgClosed.splits p).map f

中文:
定理 是代数闭.splits_domain
  结论: {k K : 类型} [域 k] [是代数闭 k] [域 K] {f : k ->+* K}
  证明: (IsAlgClosed.splits p).map f

Depends on / 依赖: IsAlgClosed, IsAlgClosed.splits, splits
-/
theorem IsAlgClosed.splits_domain {k K : Type*} [Field k] [IsAlgClosed k] [Field K] {f : k ->+* K}
    (p : k[X]) : (p.map f).Splits :=
  (IsAlgClosed.splits p).map f

namespace IsAlgClosed

variable {k}

/--
If `k` is algebraically closed, then every nonconstant polynomial has a root.
-/
@[stacks 09GR "(4) ⟹ (3)"]
/--
theorem `exists_root` / 定理 `exists_root`

English:
theorem exists_root
  given: [IsAlgClosed k] (p : k[X]) (hp : p.degree != 0)
  statement: exists x, IsRoot p x
  proof: (IsAlgClosed.splits p).exists_eval_eq_zero hp

中文:
定理 存在_root
  条件: [是代数闭 k] (p : k[X]) (hp : p.degree != 0)
  结论: 存在 x, IsRoot p x
  证明: (IsAlgClosed.splits p).exists_eval_eq_zero hp

Depends on / 依赖: IsAlgClosed, IsAlgClosed.splits, exists_eval_eq_zero, splits
-/
theorem exists_root [IsAlgClosed k] (p : k[X]) (hp : p.degree != 0) : exists x, IsRoot p x :=
  (IsAlgClosed.splits p).exists_eval_eq_zero hp

/--
theorem `exists_pow_nat_eq` / 定理 `exists_pow_nat_eq`

English:
theorem exists_pow_nat_eq
  given: [IsAlgClosed k] (x : k) {n : Nat} (hn : 0 < n)
  statement: exists z, z ^ n = x
  proof: by
  have : degree (X ^ n - C x) != 0 := by
    rw [degree_X_pow_sub_C hn x]
    exact ne_of_gt (WithBot.coe_lt_coe.2 hn)
  obtain ⟨z, hz⟩ := exists_root (X ^ n - C x) this
  use z
  simp only [eval_C, eval_X, eval_pow, eval_sub, IsRoot.def] at hz
  exact sub_eq_zero.1 hz

中文:
定理 存在_pow_nat_eq
  条件: [是代数闭 k] (x : k) {n : 自然数} (hn : 0 < n)
  结论: 存在 z, z ^ n = x
  证明: by
  have : degree (X ^ n - C x) != 0 := by
    rw [degree_X_pow_sub_C hn x]
    exact ne_of_gt (WithBot.coe_lt_coe.2 hn)
  obtain ⟨z, hz⟩ := exists_root (X ^ n - C x) this
  use z
  simp only [eval_C, eval_X, eval_pow, eval_sub, IsRoot.def] at hz
  exact sub_eq_zero.1 hz

Depends on / 依赖: IsRoot, IsRoot.def, WithBot, WithBot.coe_lt_coe, coe_lt_coe, degree, degree_X_pow_sub_C, eval_C, eval_X, eval_pow, eval_sub, exists_root, ne_of_gt, sub_eq_zero
-/
theorem exists_pow_nat_eq [IsAlgClosed k] (x : k) {n : Nat} (hn : 0 < n) : exists z, z ^ n = x := by
  have : degree (X ^ n - C x) != 0 := by
    rw [degree_X_pow_sub_C hn x]
    exact ne_of_gt (WithBot.coe_lt_coe.2 hn)
  obtain ⟨z, hz⟩ := exists_root (X ^ n - C x) this
  use z
  simp only [eval_C, eval_X, eval_pow, eval_sub, IsRoot.def] at hz
  exact sub_eq_zero.1 hz

/--
theorem `exists_eq_mul_self` / 定理 `exists_eq_mul_self`

English:
theorem exists_eq_mul_self
  given: [IsAlgClosed k] (x : k)
  statement: exists z, x = z * z
  proof: by
  rcases exists_pow_nat_eq x zero_lt_two with ⟨z, rfl⟩
  exact ⟨z, sq z⟩

中文:
定理 存在_eq_mul_self
  条件: [是代数闭 k] (x : k)
  结论: 存在 z, x = z * z
  证明: by
  rcases exists_pow_nat_eq x zero_lt_two with ⟨z, rfl⟩
  exact ⟨z, sq z⟩

Depends on / 依赖: exists_pow_nat_eq, zero_lt_two
-/
theorem exists_eq_mul_self [IsAlgClosed k] (x : k) : exists z, x = z * z := by
  rcases exists_pow_nat_eq x zero_lt_two with ⟨z, rfl⟩
  exact ⟨z, sq z⟩

/--
theorem `roots_eq_zero_iff` / 定理 `roots_eq_zero_iff`

English:
theorem roots_eq_zero_iff
  given: [IsAlgClosed k] {p : k[X]}
  proof: by
  refine ⟨fun h => ?_, fun hp => by rw [hp, roots_C]⟩
  rcases le_or_gt (degree p) 0 with hd | hd
  · exact eq_C_of_degree_le_zero hd
  · obtain ⟨z, hz⟩ := IsAlgClosed.exists_root p hd.ne'
    rw [← mem_roots (ne_zero_of_degree_gt hd)]; rw [h] at hz
    simp at hz

中文:
定理 roots_eq_zero_iff
  条件: [是代数闭 k] {p : k[X]}
  证明: by
  refine ⟨fun h => ?_, fun hp => by rw [hp, roots_C]⟩
  rcases le_or_gt (degree p) 0 with hd | hd
  · exact eq_C_of_degree_le_zero hd
  · obtain ⟨z, hz⟩ := IsAlgClosed.exists_root p hd.ne'
    rw [← mem_roots (ne_zero_of_degree_gt hd)]; rw [h] at hz
    simp at hz

Depends on / 依赖: IsAlgClosed, IsAlgClosed.exists_root, IsKleinFour, IsKleinFour.card_four, card_four, degree, eq_C_of_degree_le_zero, exists_root, exponent_two, hd.ne, le_or_gt, mem_roots, ne_zero_of_degree_gt, roots_C
-/
theorem roots_eq_zero_iff [IsAlgClosed k] {p : k[X]} :
    p.roots = 0 ↔ p = Polynomial.C (p.coeff 0) := by
  refine ⟨fun h => ?_, fun hp => by rw [hp, roots_C]⟩
  rcases le_or_gt (degree p) 0 with hd | hd
  · exact eq_C_of_degree_le_zero hd
  · obtain ⟨z, hz⟩ := IsAlgClosed.exists_root p hd.ne'
    rw [← mem_roots (ne_zero_of_degree_gt hd)]; rw [h] at hz
    simp at hz

/--
theorem `roots_eq_zero_iff_natDegree_eq_zero` / 定理 `roots_eq_zero_iff_natDegree_eq_zero`

English:
theorem roots_eq_zero_iff_natDegree_eq_zero
  given: [IsAlgClosed k] {p : k[X]}
  proof: roots_eq_zero_iff.trans eq_C_coeff_zero_iff_natDegree_eq_zero

中文:
定理 roots_eq_zero_iff_natDegree_eq_zero
  条件: [是代数闭 k] {p : k[X]}
  证明: roots_eq_zero_iff.trans eq_C_coeff_zero_iff_natDegree_eq_zero

Depends on / 依赖: IsAddKleinFour, IsAddKleinFour.card_four, card_four, eq_C_coeff_zero_iff_natDegree_eq_zero, exponent_two, roots_eq_zero_iff, roots_eq_zero_iff.trans
-/
theorem roots_eq_zero_iff_natDegree_eq_zero [IsAlgClosed k] {p : k[X]} :
    p.roots = 0 ↔ p.natDegree = 0 :=
  roots_eq_zero_iff.trans eq_C_coeff_zero_iff_natDegree_eq_zero

/--
theorem `roots_eq_zero_iff_degree_nonpos` / 定理 `roots_eq_zero_iff_degree_nonpos`

English:
theorem roots_eq_zero_iff_degree_nonpos
  given: [IsAlgClosed k] {p : k[X]}
  statement: p.roots = 0 ↔ p.degree <= 0
  proof: roots_eq_zero_iff_natDegree_eq_zero.trans natDegree_eq_zero_iff_degree_le_zero

中文:
定理 roots_eq_zero_iff_degree_nonpos
  条件: [是代数闭 k] {p : k[X]}
  结论: p.roots = 0 ↔ p.degree <= 0
  证明: roots_eq_zero_iff_natDegree_eq_zero.trans natDegree_eq_zero_iff_degree_le_zero

Depends on / 依赖: natDegree_eq_zero_iff_degree_le_zero, roots_eq_zero_iff_natDegree_eq_zero, roots_eq_zero_iff_natDegree_eq_zero.trans
-/
theorem roots_eq_zero_iff_degree_nonpos [IsAlgClosed k] {p : k[X]} : p.roots = 0 ↔ p.degree <= 0 :=
  roots_eq_zero_iff_natDegree_eq_zero.trans natDegree_eq_zero_iff_degree_le_zero

/--
theorem `card_roots_eq_natDegree` / 定理 `card_roots_eq_natDegree`

English:
theorem card_roots_eq_natDegree
  given: [IsAlgClosed k] {p : k[X]}
  statement: p.roots.card = p.natDegree
  proof: by
  have ⟨_, _, hdeg, hroots⟩ := exists_prod_multiset_X_sub_C_mul p
  simp [← hdeg, roots_eq_zero_iff_natDegree_eq_zero.mp hroots]

中文:
定理 card_roots_eq_natDegree
  条件: [是代数闭 k] {p : k[X]}
  结论: p.roots.card = p.natDegree
  证明: by
  have ⟨_, _, hdeg, hroots⟩ := exists_prod_multiset_X_sub_C_mul p
  simp [← hdeg, roots_eq_zero_iff_natDegree_eq_zero.mp hroots]

Depends on / 依赖: exists_prod_multiset_X_sub_C_mul, hroots, roots_eq_zero_iff_natDegree_eq_zero, roots_eq_zero_iff_natDegree_eq_zero.mp
-/
theorem card_roots_eq_natDegree [IsAlgClosed k] {p : k[X]} : p.roots.card = p.natDegree := by
  have ⟨_, _, hdeg, hroots⟩ := exists_prod_multiset_X_sub_C_mul p
  simp [← hdeg, roots_eq_zero_iff_natDegree_eq_zero.mp hroots]

/--
theorem `card_roots_map_eq_natDegree_of_leadingCoeff_ne_zero` / 定理 `card_roots_map_eq_natDegree_of_leadingCoeff_ne_zero`

English:
theorem card_roots_map_eq_natDegree_of_leadingCoeff_ne_zero
  statement: {A B : Type*} [Semiring A] [Field B]
  proof: natDegree_map_of_leadingCoeff_ne_zero _ hf ▸ card_roots_eq_natDegree

中文:
定理 card_roots_map_eq_natDegree_of_leadingCoeff_ne_zero
  结论: {A B : 类型} [半环 A] [域 B]
  证明: natDegree_map_of_leadingCoeff_ne_zero _ hf ▸ card_roots_eq_natDegree

Depends on / 依赖: card_roots_eq_natDegree, natDegree_map_of_leadingCoeff_ne_zero
-/
theorem card_roots_map_eq_natDegree_of_leadingCoeff_ne_zero {A B : Type*} [Semiring A] [Field B]
    [IsAlgClosed B] {f : A ->+* B} {p : A[X]} (hf : f p.leadingCoeff != 0) :
    (p.map f).roots.card = p.natDegree :=
  natDegree_map_of_leadingCoeff_ne_zero _ hf ▸ card_roots_eq_natDegree

/--
theorem `card_roots_map_eq_natDegree_of_isUnit_leadingCoeff` / 定理 `card_roots_map_eq_natDegree_of_isUnit_leadingCoeff`

English:
theorem card_roots_map_eq_natDegree_of_isUnit_leadingCoeff
  statement: {A B : Type*} [Semiring A] [Field B]
  proof: natDegree_map_eq_of_isUnit_leadingCoeff f h ▸ card_roots_eq_natDegree

中文:
定理 card_roots_map_eq_natDegree_of_isUnit_leadingCoeff
  结论: {A B : 类型} [半环 A] [域 B]
  证明: natDegree_map_eq_of_isUnit_leadingCoeff f h ▸ card_roots_eq_natDegree

Depends on / 依赖: card_roots_eq_natDegree, natDegree_map_eq_of_isUnit_leadingCoeff
-/
theorem card_roots_map_eq_natDegree_of_isUnit_leadingCoeff {A B : Type*} [Semiring A] [Field B]
    [IsAlgClosed B] (f : A ->+* B) {p : A[X]} (h : IsUnit p.leadingCoeff) :
    (p.map f).roots.card = p.natDegree :=
  natDegree_map_eq_of_isUnit_leadingCoeff f h ▸ card_roots_eq_natDegree

/--
theorem `card_roots_map_eq_natDegree_of_injective` / 定理 `card_roots_map_eq_natDegree_of_injective`

English:
theorem card_roots_map_eq_natDegree_of_injective
  statement: {A B : Type*} [Semiring A] [Field B]
  proof: natDegree_map_eq_of_injective hf _ ▸ card_roots_eq_natDegree

中文:
定理 card_roots_map_eq_natDegree_of_injective
  结论: {A B : 类型} [半环 A] [域 B]
  证明: natDegree_map_eq_of_injective hf _ ▸ card_roots_eq_natDegree

Depends on / 依赖: card_roots_eq_natDegree, natDegree_map_eq_of_injective
-/
theorem card_roots_map_eq_natDegree_of_injective {A B : Type*} [Semiring A] [Field B]
    [IsAlgClosed B] {f : A ->+* B} (p : A[X]) (hf : Function.Injective f) :
    (p.map f).roots.card = p.natDegree :=
  natDegree_map_eq_of_injective hf _ ▸ card_roots_eq_natDegree

/--
theorem `card_roots_map_eq_natDegree_from_simpleRing` / 定理 `card_roots_map_eq_natDegree_from_simpleRing`

English:
theorem card_roots_map_eq_natDegree_from_simpleRing
  statement: {A B : Type*} [Ring A] [IsSimpleRing A]
  proof: natDegree_map f ▸ card_roots_eq_natDegree

中文:
定理 card_roots_map_eq_natDegree_from_simpleRing
  结论: {A B : 类型} [环 A] [是单环 A]
  证明: natDegree_map f ▸ card_roots_eq_natDegree

Depends on / 依赖: card_roots_eq_natDegree, natDegree_map
-/
theorem card_roots_map_eq_natDegree_from_simpleRing {A B : Type*} [Ring A] [IsSimpleRing A]
    [Field B] [IsAlgClosed B] (f : A ->+* B) (p : A[X]) : (p.map f).roots.card = p.natDegree :=
  natDegree_map f ▸ card_roots_eq_natDegree

/--
theorem `card_aroots_eq_natDegree_of_leadingCoeff_ne_zero` / 定理 `card_aroots_eq_natDegree_of_leadingCoeff_ne_zero`

English:
theorem card_aroots_eq_natDegree_of_leadingCoeff_ne_zero
  statement: {A B : Type*} [CommRing A] [Field B]
  proof: card_roots_map_eq_natDegree_of_leadingCoeff_ne_zero hf

中文:
定理 card_aroots_eq_natDegree_of_leadingCoeff_ne_zero
  结论: {A B : 类型} [交换环 A] [域 B]
  证明: card_roots_map_eq_natDegree_of_leadingCoeff_ne_zero hf

Depends on / 依赖: card_roots_map_eq_natDegree_of_leadingCoeff_ne_zero
-/
theorem card_aroots_eq_natDegree_of_leadingCoeff_ne_zero {A B : Type*} [CommRing A] [Field B]
    [IsAlgClosed B] [Algebra A B] {p : A[X]} (hf : algebraMap A B p.leadingCoeff != 0) :
    (p.aroots B).card = p.natDegree :=
  card_roots_map_eq_natDegree_of_leadingCoeff_ne_zero hf

/--
theorem `card_aroots_eq_natDegree_of_isUnit_leadingCoeff` / 定理 `card_aroots_eq_natDegree_of_isUnit_leadingCoeff`

English:
theorem card_aroots_eq_natDegree_of_isUnit_leadingCoeff
  statement: {A B : Type*} [CommRing A] [Field B]
  proof: card_roots_map_eq_natDegree_of_isUnit_leadingCoeff _ h

中文:
定理 card_aroots_eq_natDegree_of_isUnit_leadingCoeff
  结论: {A B : 类型} [交换环 A] [域 B]
  证明: card_roots_map_eq_natDegree_of_isUnit_leadingCoeff _ h

Depends on / 依赖: card_roots_map_eq_natDegree_of_isUnit_leadingCoeff
-/
theorem card_aroots_eq_natDegree_of_isUnit_leadingCoeff {A B : Type*} [CommRing A] [Field B]
    [IsAlgClosed B] [Algebra A B] {p : A[X]} (h : IsUnit p.leadingCoeff) :
    (p.aroots B).card = p.natDegree :=
  card_roots_map_eq_natDegree_of_isUnit_leadingCoeff _ h

/--
theorem `card_aroots_eq_natDegree` / 定理 `card_aroots_eq_natDegree`

English:
theorem card_aroots_eq_natDegree
  statement: {A B : Type*} [CommRing A] [Field B] [IsAlgClosed B] [Algebra A B]
  proof: card_roots_map_eq_natDegree_of_injective _ FaithfulSMul.algebraMap_injective _ _

中文:
定理 card_aroots_eq_natDegree
  结论: {A B : 类型} [交换环 A] [域 B] [是代数闭 B] [代数 A B]
  证明: card_roots_map_eq_natDegree_of_injective _ FaithfulSMul.algebraMap_injective _ _

Depends on / 依赖: FaithfulSMul, FaithfulSMul.algebraMap_injective, algebraMap_injective, card_roots_map_eq_natDegree_of_injective
-/
theorem card_aroots_eq_natDegree {A B : Type*} [CommRing A] [Field B] [IsAlgClosed B] [Algebra A B]
    [FaithfulSMul A B] {p : A[X]} : (p.aroots B).card = p.natDegree :=
card_roots_map_eq_natDegree_of_injective _ FaithfulSMul.algebraMap_injective _ _

/--
theorem `dvd_iff_roots_le_roots` / 定理 `dvd_iff_roots_le_roots`

English:
theorem dvd_iff_roots_le_roots
  given: [IsAlgClosed k] {p q : k[X]} (hp : p != 0) (hq : q != 0)
  proof: Splits.dvd_iff_roots_le_roots (splits _) hp hq

中文:
定理 dvd_iff_roots_le_roots
  条件: [是代数闭 k] {p q : k[X]} (hp : p != 0) (hq : q != 0)
  证明: Splits.dvd_iff_roots_le_roots (splits _) hp hq

Depends on / 依赖: Splits, Splits.dvd_iff_roots_le_roots, dvd_iff_roots_le_roots, splits
-/
theorem dvd_iff_roots_le_roots [IsAlgClosed k] {p q : k[X]} (hp : p != 0) (hq : q != 0) :
    p ∣ q ↔ p.roots <= q.roots :=
  Splits.dvd_iff_roots_le_roots (splits _) hp hq

/--
theorem `associated_iff_roots_eq_roots` / 定理 `associated_iff_roots_eq_roots`

English:
theorem associated_iff_roots_eq_roots
  given: [IsAlgClosed k] {p q : k[X]} (hp : p != 0) (hq : q != 0)
  proof: ⟨Associated.roots_eq, fun h => associated_of_dvd_dvd
    (dvd_iff_roots_le_roots hp hq |>.mpr <| le_of_eq h)
    (dvd_iff_roots_le_roots hq hp |>.mpr <| le_of_eq h.symm)⟩

中文:
定理 associated_iff_roots_eq_roots
  条件: [是代数闭 k] {p q : k[X]} (hp : p != 0) (hq : q != 0)
  证明: ⟨Associated.roots_eq, fun h => associated_of_dvd_dvd
    (dvd_iff_roots_le_roots hp hq |>.mpr <| le_of_eq h)
    (dvd_iff_roots_le_roots hq hp |>.mpr <| le_of_eq h.symm)⟩

Depends on / 依赖: Associated, Associated.roots_eq, associated_of_dvd_dvd, dvd_iff_roots_le_roots, h.symm, le_of_eq, roots_eq
-/
theorem associated_iff_roots_eq_roots [IsAlgClosed k] {p q : k[X]} (hp : p != 0) (hq : q != 0) :
    Associated p q ↔ p.roots = q.roots :=
  ⟨Associated.roots_eq, fun h => associated_of_dvd_dvd
    (dvd_iff_roots_le_roots hp hq |>.mpr <| le_of_eq h)
    (dvd_iff_roots_le_roots hq hp |>.mpr <| le_of_eq h.symm)⟩

/--
theorem `exists_eval₂_eq_zero_of_injective` / 定理 `exists_eval₂_eq_zero_of_injective`

English:
theorem exists_eval₂_eq_zero_of_injective
  statement: {R : Type*} [Semiring R] [IsAlgClosed k] (f : R ->+* k)
  proof: let ⟨x, hx⟩ := exists_root (p.map f) (by rwa [degree_map_eq_of_injective hf])
  ⟨x, by rwa [eval₂_eq_eval_map, ← IsRoot]⟩

中文:
定理 存在_eval₂_eq_zero_of_injective
  结论: {R : 类型} [半环 R] [是代数闭 k] (f : R ->+* k)
  证明: let ⟨x, hx⟩ := exists_root (p.map f) (by rwa [degree_map_eq_of_injective hf])
  ⟨x, by rwa [eval₂_eq_eval_map, ← IsRoot]⟩

Depends on / 依赖: IsRoot, degree_map_eq_of_injective, exists_root, p.map
-/
theorem exists_eval₂_eq_zero_of_injective {R : Type*} [Semiring R] [IsAlgClosed k] (f : R ->+* k)
    (hf : Function.Injective f) (p : R[X]) (hp : p.degree != 0) : exists x, p.eval₂ f x = 0 :=
  let ⟨x, hx⟩ := exists_root (p.map f) (by rwa [degree_map_eq_of_injective hf])
  ⟨x, by rwa [eval₂_eq_eval_map, ← IsRoot]⟩

/--
theorem `exists_eval₂_eq_zero` / 定理 `exists_eval₂_eq_zero`

English:
theorem exists_eval₂_eq_zero
  statement: {R : Type*} [Ring R] [IsSimpleRing R] [IsAlgClosed k] (f : R ->+* k)
  proof: exists_eval₂_eq_zero_of_injective _ f.injective _ hp

中文:
定理 存在_eval₂_eq_zero
  结论: {R : 类型} [环 R] [是单环 R] [是代数闭 k] (f : R ->+* k)
  证明: exists_eval₂_eq_zero_of_injective _ f.injective _ hp

Depends on / 依赖: f.injective, injective
-/
theorem exists_eval₂_eq_zero {R : Type*} [Ring R] [IsSimpleRing R] [IsAlgClosed k] (f : R ->+* k)
    (p : R[X]) (hp : p.degree != 0) : exists x, p.eval₂ f x = 0 :=
  exists_eval₂_eq_zero_of_injective _ f.injective _ hp

variable (k)

/--
theorem `exists_aeval_eq_zero_of_injective` / 定理 `exists_aeval_eq_zero_of_injective`

English:
theorem exists_aeval_eq_zero_of_injective
  statement: {R : Type*} [CommSemiring R] [IsAlgClosed k] [Algebra R k]
  proof: exists_eval₂_eq_zero_of_injective (algebraMap R k) hinj p hp

中文:
定理 存在_aeval_eq_zero_of_injective
  结论: {R : 类型} [交换半环 R] [是代数闭 k] [代数 R k]
  证明: exists_eval₂_eq_zero_of_injective (algebraMap R k) hinj p hp

Depends on / 依赖: algebraMap
-/
theorem exists_aeval_eq_zero_of_injective {R : Type*} [CommSemiring R] [IsAlgClosed k] [Algebra R k]
    (hinj : Function.Injective (algebraMap R k)) (p : R[X]) (hp : p.degree != 0) :
    exists x : k, aeval x p = 0 :=
  exists_eval₂_eq_zero_of_injective (algebraMap R k) hinj p hp

/--
theorem `exists_aeval_eq_zero` / 定理 `exists_aeval_eq_zero`

English:
theorem exists_aeval_eq_zero
  statement: {R : Type*} [CommSemiring R] [IsAlgClosed k] [Algebra R k]
  proof: exists_aeval_eq_zero_of_injective _ (FaithfulSMul.algebraMap_injective ..) _ hp

中文:
定理 存在_aeval_eq_zero
  结论: {R : 类型} [交换半环 R] [是代数闭 k] [代数 R k]
  证明: exists_aeval_eq_zero_of_injective _ (FaithfulSMul.algebraMap_injective ..) _ hp

Depends on / 依赖: FaithfulSMul, FaithfulSMul.algebraMap_injective, algebraMap_injective, exists_aeval_eq_zero_of_injective
-/
theorem exists_aeval_eq_zero {R : Type*} [CommSemiring R] [IsAlgClosed k] [Algebra R k]
    [FaithfulSMul R k] (p : R[X]) (hp : p.degree != 0) : exists x : k, p.aeval x = 0 :=
  exists_aeval_eq_zero_of_injective _ (FaithfulSMul.algebraMap_injective ..) _ hp

/--
If every nonconstant polynomial over `k` has a root, then `k` is algebraically closed.
-/
@[stacks 09GR "(3) ⟹ (4)"]
/--
theorem `of_exists_root` / 定理 `of_exists_root`

English:
theorem of_exists_root
  given: (H : forall p : k[X], p.Monic -> Irreducible p -> exists x, p.eval x = 0)
  proof: by
  replace H (p : k[X]) (hp : Irreducible p) : exists x, p.eval x = 0 := by
    obtain ⟨x, hx⟩ := H (p * C (leadingCoeff p)⁻¹) (monic_mul_leadingCoeff_inv hp.ne_zero)
      (irreducible_mul_leadingCoeff_inv.mpr hp)
    exact ⟨x, by simpa [hp.ne_zero] using hx⟩
  refine ⟨fun p => ?_⟩
  by_cases hp0 : p = 0
  · simp [hp0]
  obtain ⟨u, hu⟩ := UniqueFactorizationMonoid.factors_prod hp0
  rw [← hu]
  refine (Splits.multisetProd fun f hf => ?_).mul u.isUnit.splits
  let h := UniqueFactorizationMonoid.irreducible_of_factor f hf
  obtain ⟨x, hx⟩ := H f h
  exact Splits.of_degree_eq_one (degree_eq_one_of_irreducible_of_root h hx)

中文:
定理 of_存在_root
  条件: (H : 对任意 p : k[X], p.Monic -> 不可约 p -> 存在 x, p.eval x = 0)
  证明: by
  replace H (p : k[X]) (hp : Irreducible p) : exists x, p.eval x = 0 := by
    obtain ⟨x, hx⟩ := H (p * C (leadingCoeff p)⁻¹) (monic_mul_leadingCoeff_inv hp.ne_zero)
      (irreducible_mul_leadingCoeff_inv.mpr hp)
    exact ⟨x, by simpa [hp.ne_zero] using hx⟩
  refine ⟨fun p => ?_⟩
  by_cases hp0 : p = 0
  · simp [hp0]
  obtain ⟨u, hu⟩ := UniqueFactorizationMonoid.factors_prod hp0
  rw [← hu]
  refine (Splits.multisetProd fun f hf => ?_).mul u.isUnit.splits
  let h := UniqueFactorizationMonoid.irreducible_of_factor f hf
  obtain ⟨x, hx⟩ := H f h
  exact Splits.of_degree_eq_one (degree_eq_one_of_irreducible_of_root h hx)

Depends on / 依赖: Irreducible, Splits, Splits.multisetProd, UniqueFactorizationMonoid, UniqueFactorizationMonoid.factors_prod, UniqueFactorizationMonoid.irreducible_of_factor, factors_prod, hp.ne_zero, irreducible_mul_leadingCoeff_inv, irreducible_mul_leadingCoeff_inv.mpr, irreducible_of_factor, isUnit, leadingCoeff, monic_mul_leadingCoeff_inv, multisetProd, ne_zero, p.eval, replace, splits, u.isUnit.splits
-/
theorem of_exists_root (H : forall p : k[X], p.Monic -> Irreducible p -> exists x, p.eval x = 0) :
    IsAlgClosed k := by
  replace H (p : k[X]) (hp : Irreducible p) : exists x, p.eval x = 0 := by
    obtain ⟨x, hx⟩ := H (p * C (leadingCoeff p)⁻¹) (monic_mul_leadingCoeff_inv hp.ne_zero)
      (irreducible_mul_leadingCoeff_inv.mpr hp)
    exact ⟨x, by simpa [hp.ne_zero] using hx⟩
  refine ⟨fun p => ?_⟩
  by_cases hp0 : p = 0
  · simp [hp0]
  obtain ⟨u, hu⟩ := UniqueFactorizationMonoid.factors_prod hp0
  rw [← hu]
  refine (Splits.multisetProd fun f hf => ?_).mul u.isUnit.splits
  let h := UniqueFactorizationMonoid.irreducible_of_factor f hf
  obtain ⟨x, hx⟩ := H f h
  exact Splits.of_degree_eq_one (degree_eq_one_of_irreducible_of_root h hx)

/--
theorem `of_ringEquiv` / 定理 `of_ringEquiv`

English:
theorem of_ringEquiv
  statement: (k' : Type u) [Field k'] (e : k ≃+* k')
  proof: by
  apply IsAlgClosed.of_exists_root
  intro p hmp hp
  have hpe : degree (p.map e.symm.toRingHom) != 0 := by
    rw [degree_map]
    exact ne_of_gt (degree_pos_of_irreducible hp)
  rcases IsAlgClosed.exists_root (k := k) (p.map e.symm.toRingHom) hpe with ⟨x, hx⟩
  use e x
  rw [IsRoot] at hx
  apply e.symm.injective
  rw [map_zero]; rw [← hx]
  clear hx hpe hp hmp
  induction p using Polynomial.induction_on <;> simp_all

中文:
定理 of_ringEquiv
  结论: (k' : 类型u) [域 k'] (e : k ≃+* k')
  证明: by
  apply IsAlgClosed.of_exists_root
  intro p hmp hp
  have hpe : degree (p.map e.symm.toRingHom) != 0 := by
    rw [degree_map]
    exact ne_of_gt (degree_pos_of_irreducible hp)
  rcases IsAlgClosed.exists_root (k := k) (p.map e.symm.toRingHom) hpe with ⟨x, hx⟩
  use e x
  rw [IsRoot] at hx
  apply e.symm.injective
  rw [map_zero]; rw [← hx]
  clear hx hpe hp hmp
  induction p using Polynomial.induction_on <;> simp_all

Depends on / 依赖: IsAlgClosed, IsAlgClosed.exists_root, IsAlgClosed.of_exists_root, IsRoot, Polynomial, Polynomial.induction_on, degree, degree_map, degree_pos_of_irreducible, e.symm.injective, e.symm.toRingHom, exists_root, induction_on, injective, map_zero, ne_of_gt, of_exists_root, p.map, toRingHom
-/
theorem of_ringEquiv (k' : Type u) [Field k'] (e : k ≃+* k')
    [IsAlgClosed k] : IsAlgClosed k' := by
  apply IsAlgClosed.of_exists_root
  intro p hmp hp
  have hpe : degree (p.map e.symm.toRingHom) != 0 := by
    rw [degree_map]
    exact ne_of_gt (degree_pos_of_irreducible hp)
  rcases IsAlgClosed.exists_root (k := k) (p.map e.symm.toRingHom) hpe with ⟨x, hx⟩
  use e x
  rw [IsRoot] at hx
  apply e.symm.injective
  rw [map_zero]; rw [← hx]
  clear hx hpe hp hmp
  induction p using Polynomial.induction_on <;> simp_all

/--
If `k` is algebraically closed, then every irreducible polynomial over `k` is linear.
-/
@[stacks 09GR "(4) ⟹ (2)"]
/--
theorem `degree_eq_one_of_irreducible` / 定理 `degree_eq_one_of_irreducible`

English:
theorem degree_eq_one_of_irreducible
  given: [IsAlgClosed k] {p : k[X]} (hp : Irreducible p)
  proof: (IsAlgClosed.splits p).degree_eq_one_of_irreducible hp

中文:
定理 degree_eq_one_of_irreducible
  条件: [是代数闭 k] {p : k[X]} (hp : 不可约 p)
  证明: (IsAlgClosed.splits p).degree_eq_one_of_irreducible hp

Depends on / 依赖: IsAlgClosed, IsAlgClosed.splits, degree_eq_one_of_irreducible, splits
-/
theorem degree_eq_one_of_irreducible [IsAlgClosed k] {p : k[X]} (hp : Irreducible p) :
    p.degree = 1 :=
  (IsAlgClosed.splits p).degree_eq_one_of_irreducible hp

/--
theorem `algebraMap_bijective_of_isIntegral` / 定理 `algebraMap_bijective_of_isIntegral`

English:
theorem algebraMap_bijective_of_isIntegral
  statement: {k K : Type*} [Field k] [Ring K] [IsDomain K]
  proof: by
  refine ⟨RingHom.injective _, fun x => ⟨-(minpoly k x).coeff 0, ?_⟩⟩
  have hq : (minpoly k x).leadingCoeff = 1 := minpoly.monic (Algebra.IsIntegral.isIntegral x)
  have h : (minpoly k x).degree = 1 := degree_eq_one_of_irreducible k (minpoly.irreducible
    (Algebra.IsIntegral.isIntegral x))
  have : aeval x (minpoly k x) = 0 := minpoly.aeval k x
  rw [eq_X_add_C_of_degree_eq_one h]; rw [hq]; rw [C_1]; rw [one_mul]; rw [aeval_add]; rw [aeval_X]; rw [aeval_C]; rw [add_eq_zero_iff_eq_neg] at this
  exact (map_neg (algebraMap k K) ((minpoly k x).coeff 0)).symm ▸ this.symm

中文:
定理 algebraMap_bijective_of_is整数egral
  结论: {k K : 类型} [域 k] [环 K] [是整环 K]
  证明: by
  refine ⟨RingHom.injective _, fun x => ⟨-(minpoly k x).coeff 0, ?_⟩⟩
  have hq : (minpoly k x).leadingCoeff = 1 := minpoly.monic (Algebra.IsIntegral.isIntegral x)
  have h : (minpoly k x).degree = 1 := degree_eq_one_of_irreducible k (minpoly.irreducible
    (Algebra.IsIntegral.isIntegral x))
  have : aeval x (minpoly k x) = 0 := minpoly.aeval k x
  rw [eq_X_add_C_of_degree_eq_one h]; rw [hq]; rw [C_1]; rw [one_mul]; rw [aeval_add]; rw [aeval_X]; rw [aeval_C]; rw [add_eq_zero_iff_eq_neg] at this
  exact (map_neg (algebraMap k K) ((minpoly k x).coeff 0)).symm ▸ this.symm

Depends on / 依赖: Algebra, Algebra.IsIntegral.isIntegral, IsIntegral, RingHom, RingHom.injective, add_eq_zero_iff_eq_neg, aeval_C, aeval_X, aeval_add, degree, degree_eq_one_of_irreducible, eq_X_add_C_of_degree_eq_one, injective, irreducible, isIntegral, leadingCoeff, minpoly, minpoly.aeval, minpoly.irreducible, minpoly.monic
-/
theorem algebraMap_bijective_of_isIntegral {k K : Type*} [Field k] [Ring K] [IsDomain K]
    [hk : IsAlgClosed k] [Algebra k K] [Algebra.IsIntegral k K] :
    Function.Bijective (algebraMap k K) := by
  refine ⟨RingHom.injective _, fun x => ⟨-(minpoly k x).coeff 0, ?_⟩⟩
  have hq : (minpoly k x).leadingCoeff = 1 := minpoly.monic (Algebra.IsIntegral.isIntegral x)
  have h : (minpoly k x).degree = 1 := degree_eq_one_of_irreducible k (minpoly.irreducible
    (Algebra.IsIntegral.isIntegral x))
  have : aeval x (minpoly k x) = 0 := minpoly.aeval k x
  rw [eq_X_add_C_of_degree_eq_one h]; rw [hq]; rw [C_1]; rw [one_mul]; rw [aeval_add]; rw [aeval_X]; rw [aeval_C]; rw [add_eq_zero_iff_eq_neg] at this
  exact (map_neg (algebraMap k K) ((minpoly k x).coeff 0)).symm ▸ this.symm

/--
theorem `ringHom_bijective_of_isIntegral` / 定理 `ringHom_bijective_of_isIntegral`

English:
theorem ringHom_bijective_of_isIntegral
  statement: {k K : Type*} [Field k] [CommRing K] [IsDomain K]
  proof: let _ : Algebra k K := f.toAlgebra
  have : Algebra.IsIntegral k K := ⟨hf⟩
  algebraMap_bijective_of_isIntegral

中文:
定理 ringHom_bijective_of_is整数egral
  结论: {k K : 类型} [域 k] [交换环 K] [是整环 K]
  证明: let _ : Algebra k K := f.toAlgebra
  have : Algebra.IsIntegral k K := ⟨hf⟩
  algebraMap_bijective_of_isIntegral

Depends on / 依赖: Algebra, Algebra.IsIntegral, IsIntegral, algebraMap_bijective_of_isIntegral, f.toAlgebra, toAlgebra
-/
theorem ringHom_bijective_of_isIntegral {k K : Type*} [Field k] [CommRing K] [IsDomain K]
    [IsAlgClosed k] (f : k ->+* K) (hf : f.IsIntegral) : Function.Bijective f :=
  let _ : Algebra k K := f.toAlgebra
  have : Algebra.IsIntegral k K := ⟨hf⟩
  algebraMap_bijective_of_isIntegral

end IsAlgClosed

/-- If `k` is algebraically closed, `K / k` is a field extension, `L / k` is an intermediate field
which is algebraic, then `L` is equal to `k`. A corollary of
`IsAlgClosed.algebraMap_surjective_of_isAlgebraic`. -/
@[stacks 09GQ "The result is the definition of algebraically closedness in Stacks Project. \
This statement is 09GR (4) ⟹ (1)."]
/--
theorem `IntermediateField.eq_bot_of_isAlgClosed_of_isAlgebraic` / 定理 `IntermediateField.eq_bot_of_isAlgClosed_of_isAlgebraic`

English:
theorem IntermediateField.eq_bot_of_isAlgClosed_of_isAlgebraic
  statement: {k K : Type*} [Field k] [Field K]
  proof: bot_unique fun x hx => by
  obtain ⟨y, hy⟩ := (IsAlgClosed.algebraMap_bijective_of_isIntegral (k := k)).2 (⟨x, hx⟩ : L)
  exact ⟨y, congr_arg (algebraMap L K) hy⟩

中文:
定理 中间域.eq_bot_of_isAlgClosed_of_isAlgebraic
  结论: {k K : 类型} [域 k] [域 K]
  证明: bot_unique fun x hx => by
  obtain ⟨y, hy⟩ := (IsAlgClosed.algebraMap_bijective_of_isIntegral (k := k)).2 (⟨x, hx⟩ : L)
  exact ⟨y, congr_arg (algebraMap L K) hy⟩

Depends on / 依赖: IsAlgClosed, IsAlgClosed.algebraMap_bijective_of_isIntegral, algebraMap, algebraMap_bijective_of_isIntegral, bot_unique, congr_arg
-/
theorem IntermediateField.eq_bot_of_isAlgClosed_of_isAlgebraic {k K : Type*} [Field k] [Field K]
    [IsAlgClosed k] [Algebra k K] (L : IntermediateField k K) [Algebra.IsAlgebraic k L] :
    L = ⊥ := bot_unique fun x hx => by
  obtain ⟨y, hy⟩ := (IsAlgClosed.algebraMap_bijective_of_isIntegral (k := k)).2 (⟨x, hx⟩ : L)
  exact ⟨y, congr_arg (algebraMap L K) hy⟩

/--
lemma `Polynomial.isCoprime_iff_aeval_ne_zero_of_isAlgClosed` / 引理 `Polynomial.isCoprime_iff_aeval_ne_zero_of_isAlgClosed`

English:
lemma Polynomial.isCoprime_iff_aeval_ne_zero_of_isAlgClosed
  statement: (K : Type v) [Field K] [IsAlgClosed K]
  proof: by
  refine ⟨fun h => aeval_ne_zero_of_isCoprime h, fun h => isCoprime_of_dvd _ _ ?_ fun x hu h0 => ?_⟩
  · replace h := h 0
    contrapose! h
    rw [h.left]; rw [h.right]; rw [map_zero]; rw [and_self]
  · rintro ⟨_, rfl⟩ ⟨_, rfl⟩
obtain ⟨a, ha : _ = _⟩ := IsAlgClosed.exists_root (x.map <| algebraMap k K) by
      simpa only [degree_map] using (ne_of_lt <| degree_pos_of_ne_zero_of_nonunit h0 hu).symm
    exact not_and_or.mpr (h a) (by simp_rw [map_mul, ← eval_map_algebraMap, ha, zero_mul, true_and])

中文:
引理 多项式.isCoprime_iff_aeval_ne_zero_of_isAlgClosed
  结论: (K : 类型v) [域 K] [是代数闭 K]
  证明: by
  refine ⟨fun h => aeval_ne_zero_of_isCoprime h, fun h => isCoprime_of_dvd _ _ ?_ fun x hu h0 => ?_⟩
  · replace h := h 0
    contrapose! h
    rw [h.left]; rw [h.right]; rw [map_zero]; rw [and_self]
  · rintro ⟨_, rfl⟩ ⟨_, rfl⟩
obtain ⟨a, ha : _ = _⟩ := IsAlgClosed.exists_root (x.map <| algebraMap k K) by
      simpa only [degree_map] using (ne_of_lt <| degree_pos_of_ne_zero_of_nonunit h0 hu).symm
    exact not_and_or.mpr (h a) (by simp_rw [map_mul, ← eval_map_algebraMap, ha, zero_mul, true_and])

Depends on / 依赖: IsAlgClosed, IsAlgClosed.exists_root, aeval_ne_zero_of_isCoprime, algebraMap, and_self, contrapose, degree_map, degree_pos_of_ne_zero_of_nonunit, eval_map_algebraMap, exists_root, h.left, h.right, isCoprime_of_dvd, map_mul, map_zero, ne_of_lt, not_and_or, not_and_or.mpr, replace, simp_rw
-/
lemma Polynomial.isCoprime_iff_aeval_ne_zero_of_isAlgClosed (K : Type v) [Field K] [IsAlgClosed K]
    [Algebra k K] (p q : k[X]) : IsCoprime p q ↔ forall a : K, aeval a p != 0 ∨ aeval a q != 0 := by
  refine ⟨fun h => aeval_ne_zero_of_isCoprime h, fun h => isCoprime_of_dvd _ _ ?_ fun x hu h0 => ?_⟩
  · replace h := h 0
    contrapose! h
    rw [h.left]; rw [h.right]; rw [map_zero]; rw [and_self]
  · rintro ⟨_, rfl⟩ ⟨_, rfl⟩
obtain ⟨a, ha : _ = _⟩ := IsAlgClosed.exists_root (x.map <| algebraMap k K) by
      simpa only [degree_map] using (ne_of_lt <| degree_pos_of_ne_zero_of_nonunit h0 hu).symm
    exact not_and_or.mpr (h a) (by simp_rw [map_mul, ← eval_map_algebraMap, ha, zero_mul, true_and])

/-- Typeclass for an extension being an algebraic closure. -/
@[stacks 09GS]
/--
Definition of `IsAlgClosure` / `IsAlgClosure` 的定义

English:
class IsAlgClosure
  parameters: (R : Type u) (K : Type v) [CommRing R] [Field K] [Algebra R K]
  axioms and operations (2):
    - isAlgClosed : IsAlgClosed K
    - isAlgebraic : Algebra.IsAlgebraic R K

中文:
类 是AlgClosure
  参数: (R : 类型u) (K : 类型v) [交换环 R] [域 K] [代数 R K]
  公理与运算 (2 个):
    - isAlgClosed : 是代数闭 K
    - isAlgebraic : 代数.是代数 R K
-/
class IsAlgClosure (R : Type u) (K : Type v) [CommRing R] [Field K] [Algebra R K]
    [IsTorsionFree R K] : Prop where
  isAlgClosed : IsAlgClosed K
  isAlgebraic : Algebra.IsAlgebraic R K

attribute [instance] IsAlgClosure.isAlgebraic

/--
theorem `isAlgClosure_iff` / 定理 `isAlgClosure_iff`

English:
theorem isAlgClosure_iff
  given: (K : Type v) [Field K] [Algebra k K]
  proof: ⟨fun h => ⟨h.1, h.2⟩, fun h => ⟨h.1, h.2⟩⟩

中文:
定理 isAlgClosure_iff
  条件: (K : 类型v) [域 K] [代数 k K]
  证明: ⟨fun h => ⟨h.1, h.2⟩, fun h => ⟨h.1, h.2⟩⟩
-/
theorem isAlgClosure_iff (K : Type v) [Field K] [Algebra k K] :
    IsAlgClosure k K ↔ IsAlgClosed K ∧ Algebra.IsAlgebraic k K :=
  ⟨fun h => ⟨h.1, h.2⟩, fun h => ⟨h.1, h.2⟩⟩

instance (priority := 100) IsAlgClosure.normal (R K : Type*) [Field R] [Field K] [Algebra R K]
    [IsAlgClosure R K] : Normal R K where
  toIsAlgebraic := IsAlgClosure.isAlgebraic
  splits' _ := (IsAlgClosure.isAlgClosed R).splits _

instance (priority := 100) IsAlgClosure.separable (R K : Type*) [Field R] [Field K] [Algebra R K]
    [IsAlgClosure R K] [CharZero R] : Algebra.IsSeparable R K :=
  ⟨fun _ => (minpoly.irreducible (Algebra.IsIntegral.isIntegral _)).separable⟩

/--
Instance `IsAlgClosed.instIsAlgClosure` / 实例 `IsAlgClosed.instIsAlgClosure`

English:
instance IsAlgClosed.instIsAlgClosure
  signature: (F : Type*) [Field F] [IsAlgClosed F]
  body: ‹_›
  isAlgebraic := .of_finite F F

中文:
实例 是代数闭.instIsAlgClosure
  签名: (F : 类型) [域 F] [是代数闭 F]
  定义体: ‹_›
  isAlgebraic := .of_finite F F
-/
instance IsAlgClosed.instIsAlgClosure (F : Type*) [Field F] [IsAlgClosed F] : IsAlgClosure F F where
  isAlgClosed := ‹_›
  isAlgebraic := .of_finite F F

/--
theorem `IsAlgClosure.of_splits` / 定理 `IsAlgClosure.of_splits`

English:
theorem IsAlgClosure.of_splits
  statement: {R K} [CommRing R] [IsDomain R] [Field K] [Algebra R K]
  proof: inferInstance
  isAlgClosed := .of_exists_root _ fun _p _ p_irred =>
    have ⟨g, monic, irred, dvd⟩ := p_irred.exists_dvd_monic_irreducible_of_isIntegral (K := R)
((h g monic irred).of_dvd (map_monic_ne_zero monic) dvd).exists_eval_eq_zero
      degree_ne_of_natDegree_ne p_irred.natDegree_pos.ne'

中文:
定理 是AlgClosure.of_splits
  结论: {R K} [交换环 R] [是整环 R] [域 K] [代数 R K]
  证明: inferInstance
  isAlgClosed := .of_exists_root _ fun _p _ p_irred =>
    have ⟨g, monic, irred, dvd⟩ := p_irred.exists_dvd_monic_irreducible_of_isIntegral (K := R)
((h g monic irred).of_dvd (map_monic_ne_zero monic) dvd).exists_eval_eq_zero
      degree_ne_of_natDegree_ne p_irred.natDegree_pos.ne'
-/
theorem IsAlgClosure.of_splits {R K} [CommRing R] [IsDomain R] [Field K] [Algebra R K]
    [Algebra.IsIntegral R K] [IsTorsionFree R K]
    (h : forall p : R[X], p.Monic -> Irreducible p -> (p.map (algebraMap R K)).Splits) :
    IsAlgClosure R K where
  isAlgebraic := inferInstance
  isAlgClosed := .of_exists_root _ fun _p _ p_irred =>
    have ⟨g, monic, irred, dvd⟩ := p_irred.exists_dvd_monic_irreducible_of_isIntegral (K := R)
((h g monic irred).of_dvd (map_monic_ne_zero monic) dvd).exists_eval_eq_zero
      degree_ne_of_natDegree_ne p_irred.natDegree_pos.ne'

namespace IsAlgClosed

variable {K : Type u} [Field K] {L : Type v} {M : Type w} [Field L] [Algebra K L] [Field M]
  [Algebra K M] [IsAlgClosed M]

/--
theorem `eval_surjective` / 定理 `eval_surjective`

English:
theorem eval_surjective
  given: {p : M[X]} (hp : p.natDegree != 0)
  statement: Function.Surjective p.eval
  proof: fun x => by
    rw [← Nat.pos_iff_ne_zero]; rw [natDegree_pos_iff_degree_pos] at hp
have ⟨y, hy⟩ := (IsAlgClosed.splits (p - C x)).exists_eval_eq_zero by
      simpa only [degree_sub_C hp] using hp.ne'
    exact ⟨y, by simpa [eval_sub, sub_eq_zero] using hy⟩

中文:
定理 eval_surjective
  条件: {p : M[X]} (hp : p.natDegree != 0)
  结论: 函数.满射 p.eval
  证明: fun x => by
    rw [← Nat.pos_iff_ne_zero]; rw [natDegree_pos_iff_degree_pos] at hp
have ⟨y, hy⟩ := (IsAlgClosed.splits (p - C x)).exists_eval_eq_zero by
      simpa only [degree_sub_C hp] using hp.ne'
    exact ⟨y, by simpa [eval_sub, sub_eq_zero] using hy⟩

Depends on / 依赖: IsAlgClosed, IsAlgClosed.splits, Nat.pos_iff_ne_zero, degree_sub_C, eval_sub, exists_eval_eq_zero, hp.ne, natDegree_pos_iff_degree_pos, pos_iff_ne_zero, splits, sub_eq_zero
-/
theorem eval_surjective {p : M[X]} (hp : p.natDegree != 0) : Function.Surjective p.eval :=
  fun x => by
    rw [← Nat.pos_iff_ne_zero]; rw [natDegree_pos_iff_degree_pos] at hp
have ⟨y, hy⟩ := (IsAlgClosed.splits (p - C x)).exists_eval_eq_zero by
      simpa only [degree_sub_C hp] using hp.ne'
    exact ⟨y, by simpa [eval_sub, sub_eq_zero] using hy⟩

/--
theorem `surjective_domRestrict_of_isAlgebraic` / 定理 `surjective_domRestrict_of_isAlgebraic`

English:
theorem surjective_domRestrict_of_isAlgebraic
  statement: {E : Type*}
  proof: fun f => IntermediateField.exists_algHom_of_splits'
    (E := E) f fun s => ⟨Algebra.IsIntegral.isIntegral s, IsAlgClosed.splits _⟩

@[deprecated (since := "2026-07-19")]
alias surjective_restrictDomain_of_isAlgebraic := surjective_domRestrict_of_isAlgebraic

中文:
定理 surjective_domRestrict_of_isAlgebraic
  结论: {E : 类型}
  证明: fun f => IntermediateField.exists_algHom_of_splits'
    (E := E) f fun s => ⟨Algebra.IsIntegral.isIntegral s, IsAlgClosed.splits _⟩

@[deprecated (since := "2026-07-19")]
alias surjective_restrictDomain_of_isAlgebraic := surjective_domRestrict_of_isAlgebraic

Depends on / 依赖: Algebra, Algebra.IsIntegral.isIntegral, IntermediateField, IntermediateField.exists_algHom_of_splits, IsAlgClosed, IsAlgClosed.splits, IsIntegral, exists_algHom_of_splits, isIntegral, splits
-/
theorem surjective_domRestrict_of_isAlgebraic {E : Type*}
    [Field E] [Algebra K E] [Algebra L E] [IsScalarTower K L E] [Algebra.IsAlgebraic L E] :
    Function.Surjective fun φ : E ->ₐ[K] M => φ.domRestrict L :=
  fun f => IntermediateField.exists_algHom_of_splits'
    (E := E) f fun s => ⟨Algebra.IsIntegral.isIntegral s, IsAlgClosed.splits _⟩

@[deprecated (since := "2026-07-19")]
alias surjective_restrictDomain_of_isAlgebraic := surjective_domRestrict_of_isAlgebraic

variable [Algebra.IsAlgebraic K L] (K L M)

/--
Definition of `noncomputable` / `noncomputable` 的定义

English:
definition noncomputable
  signature: def liftAux
  body: Classical.choice IntermediateField.nonempty_algHom_of_adjoin_splits
    (fun x _ => ⟨Algebra.IsIntegral.isIntegral x, splits _⟩)
    (IntermediateField.adjoin_univ K L)

中文:
定义 noncomputable
  签名: def liftAux
  定义体: Classical.choice IntermediateField.nonempty_algHom_of_adjoin_splits
    (fun x _ => ⟨Algebra.IsIntegral.isIntegral x, splits _⟩)
    (IntermediateField.adjoin_univ K L)
-/
private noncomputable def liftAux : L ->ₐ[K] M :=
Classical.choice IntermediateField.nonempty_algHom_of_adjoin_splits
    (fun x _ => ⟨Algebra.IsIntegral.isIntegral x, splits _⟩)
    (IntermediateField.adjoin_univ K L)

variable {R : Type u} [CommRing R] [IsDomain R]
variable {S : Type v} [CommRing S] [IsDomain S] [Algebra R S] [Algebra R M]
  [IsTorsionFree R S] [IsTorsionFree R M] [Algebra.IsAlgebraic R S]

variable {M}

/--
Instance `FractionRing.isAlgebraic` / 实例 `FractionRing.isAlgebraic`

English:
instance FractionRing.isAlgebraic
  signature: :
  body: (FaithfulSMul.algebraMap_injective R S).isDomain _
    letI : Algebra (FractionRing R) (FractionRing S) := FractionRing.liftAlgebra R _
    Algebra.IsAlgebraic (FractionRing R) (FractionRing S) := by
  let : IsDomain R := (FaithfulSMul.algebraMap_injective R S).isDomain _
  let : Algebra (FractionRing R) (FractionRing S) := FractionRing.liftAlgebra R _
  have := FractionRing.isScalarTower_liftAlgebra R (FractionRing S)
  have := (IsFractionRing.isAlgebraic_iff' R S (FractionRing S)).1 inferInstance
  exact ⟨fun _ => (IsFractionRing.isAlgebraic_iff R (FractionRing R) (FractionRing S)).1
    (Algebra.IsAlgebraic.isAlgebraic _)⟩

中文:
实例 FractionRing.isAlgebraic
  签名: :
  定义体: (FaithfulSMul.algebraMap_injective R S).isDomain _
    letI : Algebra (FractionRing R) (FractionRing S) := FractionRing.liftAlgebra R _
    Algebra.IsAlgebraic (FractionRing R) (FractionRing S) := by
  let : IsDomain R := (FaithfulSMul.algebraMap_injective R S).isDomain _
  let : Algebra (FractionRing R) (FractionRing S) := FractionRing.liftAlgebra R _
  have := FractionRing.isScalarTower_liftAlgebra R (FractionRing S)
  have := (IsFractionRing.isAlgebraic_iff' R S (FractionRing S)).1 inferInstance
  exact ⟨fun _ => (IsFractionRing.isAlgebraic_iff R (FractionRing R) (FractionRing S)).1
    (Algebra.IsAlgebraic.isAlgebraic _)⟩
-/
private instance FractionRing.isAlgebraic :
    letI : IsDomain R := (FaithfulSMul.algebraMap_injective R S).isDomain _
    letI : Algebra (FractionRing R) (FractionRing S) := FractionRing.liftAlgebra R _
    Algebra.IsAlgebraic (FractionRing R) (FractionRing S) := by
  let : IsDomain R := (FaithfulSMul.algebraMap_injective R S).isDomain _
  let : Algebra (FractionRing R) (FractionRing S) := FractionRing.liftAlgebra R _
  have := FractionRing.isScalarTower_liftAlgebra R (FractionRing S)
  have := (IsFractionRing.isAlgebraic_iff' R S (FractionRing S)).1 inferInstance
  exact ⟨fun _ => (IsFractionRing.isAlgebraic_iff R (FractionRing R) (FractionRing S)).1
    (Algebra.IsAlgebraic.isAlgebraic _)⟩

/-- A (random) homomorphism from an algebraic extension of R into an algebraically
  closed extension of R. -/
@[stacks 09GU, no_expose]
/--
Definition of `lift` / `lift` 的定义

English:
definition lift
  signature: : S ->ₐ[R] M
  body: by
  letI : IsDomain R := (FaithfulSMul.algebraMap_injective R S).isDomain _
  letI := FractionRing.liftAlgebra R M
  letI := FractionRing.liftAlgebra R (FractionRing S)
  have := FractionRing.isScalarTower_liftAlgebra R M
  have := FractionRing.isScalarTower_liftAlgebra R (FractionRing S)
  let f : FractionRing S ->ₐ[FractionRing R] M := liftAux (FractionRing R) (FractionRing S) M
  exact (f.restrictScalars R).comp ((Algebra.ofId S (FractionRing S)).restrictScalars R)

中文:
定义 lift
  签名: : S ->ₐ[R] M
  定义体: by
  letI : IsDomain R := (FaithfulSMul.algebraMap_injective R S).isDomain _
  letI := FractionRing.liftAlgebra R M
  letI := FractionRing.liftAlgebra R (FractionRing S)
  have := FractionRing.isScalarTower_liftAlgebra R M
  have := FractionRing.isScalarTower_liftAlgebra R (FractionRing S)
  let f : FractionRing S ->ₐ[FractionRing R] M := liftAux (FractionRing R) (FractionRing S) M
  exact (f.restrictScalars R).comp ((Algebra.ofId S (FractionRing S)).restrictScalars R)

Depends on / 依赖: Algebra, Algebra.ofId, FaithfulSMul, FaithfulSMul.algebraMap_injective, FractionRing, FractionRing.isScalarTower_liftAlgebra, FractionRing.liftAlgebra, IsDomain, algebraMap_injective, f.restrictScalars, isDomain, isScalarTower_liftAlgebra, liftAlgebra, liftAux, restrictScalars
-/
noncomputable def lift : S ->ₐ[R] M := by
  letI : IsDomain R := (FaithfulSMul.algebraMap_injective R S).isDomain _
  letI := FractionRing.liftAlgebra R M
  letI := FractionRing.liftAlgebra R (FractionRing S)
  have := FractionRing.isScalarTower_liftAlgebra R M
  have := FractionRing.isScalarTower_liftAlgebra R (FractionRing S)
  let f : FractionRing S ->ₐ[FractionRing R] M := liftAux (FractionRing R) (FractionRing S) M
  exact (f.restrictScalars R).comp ((Algebra.ofId S (FractionRing S)).restrictScalars R)

/--
theorem `nonempty_algEquiv_or_of_finrank_eq_two` / 定理 `nonempty_algEquiv_or_of_finrank_eq_two`

English:
theorem nonempty_algEquiv_or_of_finrank_eq_two
  statement: {F F' : Type*} (E : Type*)
  proof: by
  have emb : E ->ₐ[F] F' := lift
  have e := AlgEquiv.ofInjectiveField emb
  have := Subalgebra.isSimpleOrder_of_finrank h
  obtain h | h := IsSimpleOrder.eq_bot_or_eq_top emb.range <;> rw [h] at e
  exacts [.inl ⟨e.trans <| Algebra.botEquiv ..⟩, .inr ⟨e.trans Subalgebra.topEquiv⟩]

中文:
定理 nonempty_algEquiv_or_of_finrank_eq_two
  结论: {F F' : 类型} (E : 类型)
  证明: by
  have emb : E ->ₐ[F] F' := lift
  have e := AlgEquiv.ofInjectiveField emb
  have := Subalgebra.isSimpleOrder_of_finrank h
  obtain h | h := IsSimpleOrder.eq_bot_or_eq_top emb.range <;> rw [h] at e
  exacts [.inl ⟨e.trans <| Algebra.botEquiv ..⟩, .inr ⟨e.trans Subalgebra.topEquiv⟩]

Depends on / 依赖: AlgEquiv, AlgEquiv.ofInjectiveField, Algebra, Algebra.botEquiv, IsSimpleOrder, IsSimpleOrder.eq_bot_or_eq_top, Subalgebra, Subalgebra.isSimpleOrder_of_finrank, Subalgebra.topEquiv, botEquiv, e.trans, emb.range, eq_bot_or_eq_top, exacts, isSimpleOrder_of_finrank, ofInjectiveField, topEquiv
-/
theorem nonempty_algEquiv_or_of_finrank_eq_two {F F' : Type*} (E : Type*)
    [Field F] [Field F'] [Field E] [Algebra F F'] [Algebra F E]
    [Algebra.IsAlgebraic F E] [IsAlgClosed F'] (h : Module.finrank F F' = 2) :
    Nonempty (E ≃ₐ[F] F) ∨ Nonempty (E ≃ₐ[F] F') := by
  have emb : E ->ₐ[F] F' := lift
  have e := AlgEquiv.ofInjectiveField emb
  have := Subalgebra.isSimpleOrder_of_finrank h
  obtain h | h := IsSimpleOrder.eq_bot_or_eq_top emb.range <;> rw [h] at e
  exacts [.inl ⟨e.trans <| Algebra.botEquiv ..⟩, .inr ⟨e.trans Subalgebra.topEquiv⟩]

noncomputable instance (priority := 100) perfectRing (p : Nat) [Fact p.Prime] [CharP k p]
    [IsAlgClosed k] : PerfectRing k p :=
PerfectRing.ofSurjective k p fun _ => IsAlgClosed.exists_pow_nat_eq _ NeZero.pos p

noncomputable instance (priority := 100) perfectField [IsAlgClosed k] : PerfectField k := by
  obtain _ | ⟨p, _, _⟩ := CharP.exists' k
  exacts [.ofCharZero, PerfectRing.toPerfectField k p]

/-- Algebraically closed fields are infinite since `Xⁿ⁺¹ - 1` is separable when `#K = n` -/
instance (priority := 500) {K : Type*} [Field K] [IsAlgClosed K] : Infinite K := by
  apply Infinite.of_not_fintype
  intro hfin
  set n := Fintype.card K
  set f := (X : K[X]) ^ (n + 1) - 1
  have hfsep : Separable f := separable_X_pow_sub_C 1 (by simp [n]) one_ne_zero
  apply Nat.not_succ_le_self (Fintype.card K)
  have hroot : n.succ = Fintype.card (f.rootSet K) := by
    rw [card_rootSet_eq_natDegree hfsep (IsAlgClosed.splits_domain _)]
    unfold f
    rw [← C_1]; rw [natDegree_X_pow_sub_C]
  rw [hroot]
  exact Fintype.card_le_of_injective _ Subtype.coe_injective

end IsAlgClosed

namespace IsAlgClosure

section

variable (R : Type u) [CommRing R] [IsDomain R] (L : Type v) (M : Type w) [Field L] [Field M]
variable [Algebra R M] [IsTorsionFree R M] [IsAlgClosure R M]
variable [Algebra R L] [IsTorsionFree R L] [IsAlgClosure R L]

attribute [local instance] IsAlgClosure.isAlgClosed in
/-- A (random) isomorphism between two algebraic closures of `R`. -/
@[stacks 09GV]
/--
Definition of `equiv` / `equiv` 的定义

English:
definition equiv
  signature: : L ≃ₐ[R] M
  body: AlgEquiv.ofBijective _ (IsAlgClosure.isAlgebraic.algHom_bijective₂
    (IsAlgClosed.lift : L ->ₐ[R] M)
    (IsAlgClosed.lift : M ->ₐ[R] L)).1

中文:
定义 equiv
  签名: : L ≃ₐ[R] M
  定义体: AlgEquiv.ofBijective _ (IsAlgClosure.isAlgebraic.algHom_bijective₂
    (IsAlgClosed.lift : L ->ₐ[R] M)
    (IsAlgClosed.lift : M ->ₐ[R] L)).1

Depends on / 依赖: AlgEquiv, AlgEquiv.ofBijective, IsAlgClosed, IsAlgClosed.lift, IsAlgClosure, IsAlgClosure.isAlgebraic.algHom_bijective, isAlgebraic, ofBijective
-/
noncomputable def equiv : L ≃ₐ[R] M :=
  AlgEquiv.ofBijective _ (IsAlgClosure.isAlgebraic.algHom_bijective₂
    (IsAlgClosed.lift : L ->ₐ[R] M)
    (IsAlgClosed.lift : M ->ₐ[R] L)).1

end

variable (K : Type*) (J : Type*) (R : Type u) (S : Type*) (L : Type v) (M : Type w)
  [Field K] [Field J] [CommRing R] [CommRing S] [Field L] [Field M]
  [Algebra R M] [IsTorsionFree R M] [IsAlgClosure R M] [Algebra K M] [IsAlgClosure K M]
  [Algebra S L] [IsTorsionFree S L] [IsAlgClosure S L]

section EquivOfAlgebraic

variable [Algebra R S] [Algebra R L] [IsScalarTower R S L]
variable [Algebra K J] [Algebra J L] [IsAlgClosure J L] [Algebra K L] [IsScalarTower K J L]

/--
theorem `ofAlgebraic` / 定理 `ofAlgebraic`

English:
theorem ofAlgebraic
  given: [Algebra.IsAlgebraic K J]
  statement: IsAlgClosure K L
  proof: ⟨IsAlgClosure.isAlgClosed J, .trans K J L⟩

中文:
定理 ofAlgebraic
  条件: [代数.是代数 K J]
  结论: 是AlgClosure K L
  证明: ⟨IsAlgClosure.isAlgClosed J, .trans K J L⟩

Depends on / 依赖: IsAlgClosure, IsAlgClosure.isAlgClosed, isAlgClosed
-/
theorem ofAlgebraic [Algebra.IsAlgebraic K J] : IsAlgClosure K L :=
  ⟨IsAlgClosure.isAlgClosed J, .trans K J L⟩

/--
Definition of `equivOfAlgebraic'` / `equivOfAlgebraic'` 的定义

English:
definition equivOfAlgebraic'
  signature: [IsDomain R] [IsDomain S] [IsTorsionFree R S]
  body: by
  have : IsTorsionFree R L := .trans_faithfulSMul R S L
  have : IsAlgClosure R L :=
    { isAlgClosed := IsAlgClosure.isAlgClosed S
      isAlgebraic := ‹_› }
  exact IsAlgClosure.equiv _ _ _

中文:
定义 equivOfAlgebraic'
  签名: [是整环 R] [是整环 S] [是无挠 R S]
  定义体: by
  have : IsTorsionFree R L := .trans_faithfulSMul R S L
  have : IsAlgClosure R L :=
    { isAlgClosed := IsAlgClosure.isAlgClosed S
      isAlgebraic := ‹_› }
  exact IsAlgClosure.equiv _ _ _

Depends on / 依赖: IsAlgClosure, IsAlgClosure.equiv, IsAlgClosure.isAlgClosed, IsTorsionFree, isAlgClosed, isAlgebraic, trans_faithfulSMul
-/
noncomputable def equivOfAlgebraic' [IsDomain R] [IsDomain S] [IsTorsionFree R S]
    [Algebra.IsAlgebraic R L] : L ≃ₐ[R] M := by
  have : IsTorsionFree R L := .trans_faithfulSMul R S L
  have : IsAlgClosure R L :=
    { isAlgClosed := IsAlgClosure.isAlgClosed S
      isAlgebraic := ‹_› }
  exact IsAlgClosure.equiv _ _ _

/--
Definition of `equivOfAlgebraic` / `equivOfAlgebraic` 的定义

English:
definition equivOfAlgebraic
  signature: [Algebra.IsAlgebraic K J]
  body: have := Algebra.IsAlgebraic.trans K J L
  equivOfAlgebraic' K J _ _

中文:
定义 equivOfAlgebraic
  签名: [代数.是代数 K J]
  定义体: have := Algebra.IsAlgebraic.trans K J L
  equivOfAlgebraic' K J _ _

Depends on / 依赖: Algebra, Algebra.IsAlgebraic.trans, IsAlgebraic, equivOfAlgebraic
-/
noncomputable def equivOfAlgebraic [Algebra.IsAlgebraic K J] : L ≃ₐ[K] M :=
  have := Algebra.IsAlgebraic.trans K J L
  equivOfAlgebraic' K J _ _

end EquivOfAlgebraic

section EquivOfEquiv

variable {R S} [IsDomain R] [IsDomain S]

/--
Definition of `equivOfEquivAux` / `equivOfEquivAux` 的定义

English:
definition equivOfEquivAux
  signature: (hSR : S ≃+* R)
  body: by
  letI : Algebra R S := RingHom.toAlgebra hSR.symm.toRingHom
  letI : Algebra S R := RingHom.toAlgebra hSR.toRingHom
  letI : Algebra R L := RingHom.toAlgebra ((algebraMap S L).comp (algebraMap R S))
  haveI : IsScalarTower R S L := .of_algebraMap_eq fun _ => rfl
  haveI : IsScalarTower S R L := .of_algebraMap_eq (by simp [RingHom.algebraMap_toAlgebra])
  have : FaithfulSMul R S := (faithfulSMul_iff_algebraMap_injective R S).mpr hSR.symm.injective
  have : Algebra.IsAlgebraic R L := (IsAlgClosure.isAlgebraic.extendScalars
    (show Function.Injective (algebraMap S R) from hSR.injective))
  refine ⟨equivOfAlgebraic' R S L M, ?_⟩
  ext x
  simp only [RingEquiv.toRingHom_eq_coe, Function.comp_apply, RingHom.coe_comp,
    AlgEquiv.coe_ringEquiv, RingEquiv.coe_toRingHom]
  conv_lhs => rw [← hSR.symm_apply_apply x]
  change equivOfAlgebraic' R S L M (algebraMap R L (hSR x)) = _
  rw [AlgEquiv.commutes]

中文:
定义 equivOfEquivAux
  签名: (hSR : S ≃+* R)
  定义体: by
  letI : Algebra R S := RingHom.toAlgebra hSR.symm.toRingHom
  letI : Algebra S R := RingHom.toAlgebra hSR.toRingHom
  letI : Algebra R L := RingHom.toAlgebra ((algebraMap S L).comp (algebraMap R S))
  haveI : IsScalarTower R S L := .of_algebraMap_eq fun _ => rfl
  haveI : IsScalarTower S R L := .of_algebraMap_eq (by simp [RingHom.algebraMap_toAlgebra])
  have : FaithfulSMul R S := (faithfulSMul_iff_algebraMap_injective R S).mpr hSR.symm.injective
  have : Algebra.IsAlgebraic R L := (IsAlgClosure.isAlgebraic.extendScalars
    (show Function.Injective (algebraMap S R) from hSR.injective))
  refine ⟨equivOfAlgebraic' R S L M, ?_⟩
  ext x
  simp only [RingEquiv.toRingHom_eq_coe, Function.comp_apply, RingHom.coe_comp,
    AlgEquiv.coe_ringEquiv, RingEquiv.coe_toRingHom]
  conv_lhs => rw [← hSR.symm_apply_apply x]
  change equivOfAlgebraic' R S L M (algebraMap R L (hSR x)) = _
  rw [AlgEquiv.commutes]

Depends on / 依赖: Algebra, Algebra.IsAlgebraic, FaithfulSMul, IsAlgClosure, IsAlgClosure.isAlgebra, IsAlgebraic, IsScalarTower, RingHom, RingHom.algebraMap_toAlgebra, RingHom.toAlgebra, algebraMap, algebraMap_toAlgebra, faithfulSMul_iff_algebraMap_injective, hSR.symm.injective, hSR.symm.toRingHom, hSR.toRingHom, injective, isAlgebra, of_algebraMap_eq, toAlgebra
-/
noncomputable def equivOfEquivAux (hSR : S ≃+* R) :
    { e : L ≃+* M // e.toRingHom.comp (algebraMap S L) = (algebraMap R M).comp hSR.toRingHom } := by
  letI : Algebra R S := RingHom.toAlgebra hSR.symm.toRingHom
  letI : Algebra S R := RingHom.toAlgebra hSR.toRingHom
  letI : Algebra R L := RingHom.toAlgebra ((algebraMap S L).comp (algebraMap R S))
  haveI : IsScalarTower R S L := .of_algebraMap_eq fun _ => rfl
  haveI : IsScalarTower S R L := .of_algebraMap_eq (by simp [RingHom.algebraMap_toAlgebra])
  have : FaithfulSMul R S := (faithfulSMul_iff_algebraMap_injective R S).mpr hSR.symm.injective
  have : Algebra.IsAlgebraic R L := (IsAlgClosure.isAlgebraic.extendScalars
    (show Function.Injective (algebraMap S R) from hSR.injective))
  refine ⟨equivOfAlgebraic' R S L M, ?_⟩
  ext x
  simp only [RingEquiv.toRingHom_eq_coe, Function.comp_apply, RingHom.coe_comp,
    AlgEquiv.coe_ringEquiv, RingEquiv.coe_toRingHom]
  conv_lhs => rw [← hSR.symm_apply_apply x]
  change equivOfAlgebraic' R S L M (algebraMap R L (hSR x)) = _
  rw [AlgEquiv.commutes]

/--
Definition of `equivOfEquiv` / `equivOfEquiv` 的定义

English:
definition equivOfEquiv
  signature: (hSR : S ≃+* R)
  body: equivOfEquivAux L M hSR

@[simp]

中文:
定义 equivOfEquiv
  签名: (hSR : S ≃+* R)
  定义体: equivOfEquivAux L M hSR

@[simp]

Depends on / 依赖: equivOfEquivAux
-/
noncomputable def equivOfEquiv (hSR : S ≃+* R) : L ≃+* M :=
  equivOfEquivAux L M hSR

@[simp]
/--
theorem `equivOfEquiv_comp_algebraMap` / 定理 `equivOfEquiv_comp_algebraMap`

English:
theorem equivOfEquiv_comp_algebraMap
  given: (hSR : S ≃+* R)
  proof: (equivOfEquivAux L M hSR).2

@[simp]

中文:
定理 equivOfEquiv_comp_algebraMap
  条件: (hSR : S ≃+* R)
  证明: (equivOfEquivAux L M hSR).2

@[simp]

Depends on / 依赖: equivOfEquivAux
-/
theorem equivOfEquiv_comp_algebraMap (hSR : S ≃+* R) :
    (↑(equivOfEquiv L M hSR) : L ->+* M).comp (algebraMap S L) = (algebraMap R M).comp hSR :=
  (equivOfEquivAux L M hSR).2

@[simp]
/--
theorem `equivOfEquiv_algebraMap` / 定理 `equivOfEquiv_algebraMap`

English:
theorem equivOfEquiv_algebraMap
  given: (hSR : S ≃+* R) (s : S)
  proof: RingHom.ext_iff.1 (equivOfEquiv_comp_algebraMap L M hSR) s

@[simp]

中文:
定理 equivOfEquiv_algebraMap
  条件: (hSR : S ≃+* R) (s : S)
  证明: RingHom.ext_iff.1 (equivOfEquiv_comp_algebraMap L M hSR) s

@[simp]

Depends on / 依赖: RingHom, RingHom.ext_iff, equivOfEquiv_comp_algebraMap, ext_iff
-/
theorem equivOfEquiv_algebraMap (hSR : S ≃+* R) (s : S) :
    equivOfEquiv L M hSR (algebraMap S L s) = algebraMap R M (hSR s) :=
  RingHom.ext_iff.1 (equivOfEquiv_comp_algebraMap L M hSR) s

@[simp]
/--
theorem `equivOfEquiv_symm_algebraMap` / 定理 `equivOfEquiv_symm_algebraMap`

English:
theorem equivOfEquiv_symm_algebraMap
  given: (hSR : S ≃+* R) (r : R)
  proof: (equivOfEquiv L M hSR).injective (by simp)

@[simp]

中文:
定理 equivOfEquiv_symm_algebraMap
  条件: (hSR : S ≃+* R) (r : R)
  证明: (equivOfEquiv L M hSR).injective (by simp)

@[simp]

Depends on / 依赖: equivOfEquiv, injective
-/
theorem equivOfEquiv_symm_algebraMap (hSR : S ≃+* R) (r : R) :
    (equivOfEquiv L M hSR).symm (algebraMap R M r) = algebraMap S L (hSR.symm r) :=
  (equivOfEquiv L M hSR).injective (by simp)

@[simp]
/--
theorem `equivOfEquiv_symm_comp_algebraMap` / 定理 `equivOfEquiv_symm_comp_algebraMap`

English:
theorem equivOfEquiv_symm_comp_algebraMap
  given: (hSR : S ≃+* R)
  proof: RingHom.ext_iff.2 (equivOfEquiv_symm_algebraMap L M hSR)

中文:
定理 equivOfEquiv_symm_comp_algebraMap
  条件: (hSR : S ≃+* R)
  证明: RingHom.ext_iff.2 (equivOfEquiv_symm_algebraMap L M hSR)

Depends on / 依赖: RingHom, RingHom.ext_iff, equivOfEquiv_symm_algebraMap, ext_iff
-/
theorem equivOfEquiv_symm_comp_algebraMap (hSR : S ≃+* R) :
    ((equivOfEquiv L M hSR).symm : M ->+* L).comp (algebraMap R M) =
      (algebraMap S L).comp hSR.symm :=
  RingHom.ext_iff.2 (equivOfEquiv_symm_algebraMap L M hSR)

end EquivOfEquiv

end IsAlgClosure

section Algebra.IsAlgebraic

variable {F K : Type*} (A : Type*) [Field F] [Field K] [Field A] [Algebra F K] [Algebra F A]
  [Algebra.IsAlgebraic F K]

/--
theorem `Algebra.IsAlgebraic.range_eval_eq_rootSet_minpoly` / 定理 `Algebra.IsAlgebraic.range_eval_eq_rootSet_minpoly`

English:
theorem Algebra.IsAlgebraic.range_eval_eq_rootSet_minpoly
  given: [IsAlgClosed A] (x : K)
  proof: range_eval_eq_rootSet_minpoly_of_splits A (fun _ => IsAlgClosed.splits _) x

中文:
定理 代数.是代数.range_eval_eq_rootSet_minpoly
  条件: [是代数闭 A] (x : K)
  证明: range_eval_eq_rootSet_minpoly_of_splits A (fun _ => IsAlgClosed.splits _) x

Depends on / 依赖: IsAlgClosed, IsAlgClosed.splits, range_eval_eq_rootSet_minpoly_of_splits, splits
-/
theorem Algebra.IsAlgebraic.range_eval_eq_rootSet_minpoly [IsAlgClosed A] (x : K) :
    (Set.range fun ψ : K ->ₐ[F] A => ψ x) = (minpoly F x).rootSet A :=
  range_eval_eq_rootSet_minpoly_of_splits A (fun _ => IsAlgClosed.splits _) x

/-- All `F`-embeddings of a field `K` into another field `A` factor through any intermediate
field of `A/F` in which the minimal polynomial of elements of `K` splits. -/
@[simps]
/--
Definition of `IntermediateField.algHomEquivAlgHomOfSplits` / `IntermediateField.algHomEquivAlgHomOfSplits` 的定义

English:
definition IntermediateField.algHomEquivAlgHomOfSplits
  signature: (L : IntermediateField F A)
  body: L.val.comp
  invFun f := f.codRestrict _ fun x =>
((Algebra.IsIntegral.isIntegral x).map f).mem_intermediateField_of_minpoly_splits by
      rw [minpoly.algHom_eq f f.injective]; exact hL x

中文:
定义 中间域.algHomEquivAlgHomOfSplits
  签名: (L : 中间域 F A)
  定义体: L.val.comp
  invFun f := f.codRestrict _ fun x =>
((Algebra.IsIntegral.isIntegral x).map f).mem_intermediateField_of_minpoly_splits by
      rw [minpoly.algHom_eq f f.injective]; exact hL x

Depends on / 依赖: L.val.comp
-/
def IntermediateField.algHomEquivAlgHomOfSplits (L : IntermediateField F A)
    (hL : forall x : K, ((minpoly F x).map (algebraMap F L)).Splits) :
    (K ->ₐ[F] L) ≃ (K ->ₐ[F] A) where
  toFun := L.val.comp
  invFun f := f.codRestrict _ fun x =>
((Algebra.IsIntegral.isIntegral x).map f).mem_intermediateField_of_minpoly_splits by
      rw [minpoly.algHom_eq f f.injective]; exact hL x

/--
theorem `IntermediateField.algHomEquivAlgHomOfSplits_apply_apply` / 定理 `IntermediateField.algHomEquivAlgHomOfSplits_apply_apply`

English:
theorem IntermediateField.algHomEquivAlgHomOfSplits_apply_apply
  statement: (L : IntermediateField F A)
  proof: rfl

中文:
定理 中间域.algHomEquivAlgHomOfSplits_apply_apply
  结论: (L : 中间域 F A)
  证明: rfl
-/
theorem IntermediateField.algHomEquivAlgHomOfSplits_apply_apply (L : IntermediateField F A)
    (hL : forall x : K, ((minpoly F x).map (algebraMap F L)).Splits) (f : K ->ₐ[F] L) (x : K) :
    algHomEquivAlgHomOfSplits A L hL f x = algebraMap L A (f x) := rfl

/--
Definition of `Algebra.IsAlgebraic.algHomEquivAlgHomOfSplits` / `Algebra.IsAlgebraic.algHomEquivAlgHomOfSplits` 的定义

English:
definition Algebra.IsAlgebraic.algHomEquivAlgHomOfSplits
  signature: (L : Type*) [Field L]
  body: (AlgEquiv.refl.arrowCongr (AlgEquiv.ofInjectiveField (IsScalarTower.toAlgHom F L A))).trans
    IntermediateField.algHomEquivAlgHomOfSplits A (IsScalarTower.toAlgHom F L A).fieldRange
    fun x => Splits.of_algHom (hL x) (AlgHom.rangeRestrict _)

中文:
定义 代数.是代数.algHomEquivAlgHomOfSplits
  签名: (L : 类型) [域 L]
  定义体: (AlgEquiv.refl.arrowCongr (AlgEquiv.ofInjectiveField (IsScalarTower.toAlgHom F L A))).trans
    IntermediateField.algHomEquivAlgHomOfSplits A (IsScalarTower.toAlgHom F L A).fieldRange
    fun x => Splits.of_algHom (hL x) (AlgHom.rangeRestrict _)

Depends on / 依赖: AlgEquiv, AlgEquiv.ofInjectiveField, AlgEquiv.refl.arrowCongr, AlgHom, AlgHom.rangeRestrict, IntermediateField, IntermediateField.algHomEquivAlgHomOfSplits, IsScalarTower, IsScalarTower.toAlgHom, Splits, Splits.of_algHom, algHomEquivAlgHomOfSplits, arrowCongr, fieldRange, ofInjectiveField, of_algHom, rangeRestrict, toAlgHom
-/
noncomputable def Algebra.IsAlgebraic.algHomEquivAlgHomOfSplits (L : Type*) [Field L]
    [Algebra F L] [Algebra L A] [IsScalarTower F L A]
    (hL : forall x : K, ((minpoly F x).map (algebraMap F L)).Splits) :
    (K ->ₐ[F] L) ≃ (K ->ₐ[F] A) :=
(AlgEquiv.refl.arrowCongr (AlgEquiv.ofInjectiveField (IsScalarTower.toAlgHom F L A))).trans
    IntermediateField.algHomEquivAlgHomOfSplits A (IsScalarTower.toAlgHom F L A).fieldRange
    fun x => Splits.of_algHom (hL x) (AlgHom.rangeRestrict _)

/--
theorem `Algebra.IsAlgebraic.algHomEquivAlgHomOfSplits_apply_apply` / 定理 `Algebra.IsAlgebraic.algHomEquivAlgHomOfSplits_apply_apply`

English:
theorem Algebra.IsAlgebraic.algHomEquivAlgHomOfSplits_apply_apply
  statement: (L : Type*) [Field L]
  proof: rfl

中文:
定理 代数.是代数.algHomEquivAlgHomOfSplits_apply_apply
  结论: (L : 类型) [域 L]
  证明: rfl
-/
theorem Algebra.IsAlgebraic.algHomEquivAlgHomOfSplits_apply_apply (L : Type*) [Field L]
    [Algebra F L] [Algebra L A] [IsScalarTower F L A]
    (hL : forall x : K, ((minpoly F x).map (algebraMap F L)).Splits) (f : K ->ₐ[F] L) (x : K) :
    Algebra.IsAlgebraic.algHomEquivAlgHomOfSplits A L hL f x = algebraMap L A (f x) := rfl

end Algebra.IsAlgebraic

/--
theorem `Polynomial.isRoot_of_isRoot_iff_dvd_derivative_mul` / 定理 `Polynomial.isRoot_of_isRoot_iff_dvd_derivative_mul`

English:
theorem Polynomial.isRoot_of_isRoot_iff_dvd_derivative_mul
  statement: {K : Type*} [Field K]
  proof: by
  refine ⟨?_, isRoot_of_isRoot_of_dvd_derivative_mul hf0⟩
  by_cases hg0 : g = 0
  · simp [hg0]
  by_cases hdf0 : derivative f = 0
  · rw [eq_C_of_derivative_eq_zero hdf0]
    simp only [derivative_C, zero_mul, dvd_zero, implies_true]
  have hdg : f.derivative * g != 0 := mul_ne_zero hdf0 hg0
  classical rw [IsAlgClosed.dvd_iff_roots_le_roots hf0 hdg, Multiset.le_iff_count]
  simp only [count_roots, rootMultiplicity_mul hdg]
  refine forall_imp fun a => ?_
  by_cases haf : f.eval a = 0
  · have h0 : 0 < f.rootMultiplicity a := (rootMultiplicity_pos hf0).2 haf
    rw [derivative_rootMultiplicity_of_root haf]
    intro h
    calc rootMultiplicity a f
        = rootMultiplicity a f - 1 + 1 := (Nat.sub_add_cancel (Nat.succ_le_iff.1 h0)).symm
      _ <= rootMultiplicity a f - 1 + rootMultiplicity a g := add_le_add le_rfl (Nat.succ_le_iff.1
        ((rootMultiplicity_pos hg0).2 (h haf)))
  · simp [haf, rootMultiplicity_eq_zero haf]

中文:
定理 多项式.isRoot_of_isRoot_iff_dvd_derivative_mul
  结论: {K : 类型} [域 K]
  证明: by
  refine ⟨?_, isRoot_of_isRoot_of_dvd_derivative_mul hf0⟩
  by_cases hg0 : g = 0
  · simp [hg0]
  by_cases hdf0 : derivative f = 0
  · rw [eq_C_of_derivative_eq_zero hdf0]
    simp only [derivative_C, zero_mul, dvd_zero, implies_true]
  have hdg : f.derivative * g != 0 := mul_ne_zero hdf0 hg0
  classical rw [IsAlgClosed.dvd_iff_roots_le_roots hf0 hdg, Multiset.le_iff_count]
  simp only [count_roots, rootMultiplicity_mul hdg]
  refine forall_imp fun a => ?_
  by_cases haf : f.eval a = 0
  · have h0 : 0 < f.rootMultiplicity a := (rootMultiplicity_pos hf0).2 haf
    rw [derivative_rootMultiplicity_of_root haf]
    intro h
    calc rootMultiplicity a f
        = rootMultiplicity a f - 1 + 1 := (Nat.sub_add_cancel (Nat.succ_le_iff.1 h0)).symm
      _ <= rootMultiplicity a f - 1 + rootMultiplicity a g := add_le_add le_rfl (Nat.succ_le_iff.1
        ((rootMultiplicity_pos hg0).2 (h haf)))
  · simp [haf, rootMultiplicity_eq_zero haf]

Depends on / 依赖: IsAlgClosed, IsAlgClosed.dvd_iff_roots_le_roots, Multiset, Multiset.le_iff_count, classical, count_roots, derivative, derivative_C, dvd_iff_roots_le_roots, dvd_zero, eq_C_of_derivative_eq_zero, f.derivative, f.eval, f.rootMultipli, forall_imp, implies_true, isRoot_of_isRoot_of_dvd_derivative_mul, le_iff_count, mul_ne_zero, rootMultipli
-/
theorem Polynomial.isRoot_of_isRoot_iff_dvd_derivative_mul {K : Type*} [Field K]
    [IsAlgClosed K] [CharZero K] {f g : K[X]} (hf0 : f != 0) :
    (forall x, IsRoot f x -> IsRoot g x) ↔ f ∣ f.derivative * g := by
  refine ⟨?_, isRoot_of_isRoot_of_dvd_derivative_mul hf0⟩
  by_cases hg0 : g = 0
  · simp [hg0]
  by_cases hdf0 : derivative f = 0
  · rw [eq_C_of_derivative_eq_zero hdf0]
    simp only [derivative_C, zero_mul, dvd_zero, implies_true]
  have hdg : f.derivative * g != 0 := mul_ne_zero hdf0 hg0
  classical rw [IsAlgClosed.dvd_iff_roots_le_roots hf0 hdg, Multiset.le_iff_count]
  simp only [count_roots, rootMultiplicity_mul hdg]
  refine forall_imp fun a => ?_
  by_cases haf : f.eval a = 0
  · have h0 : 0 < f.rootMultiplicity a := (rootMultiplicity_pos hf0).2 haf
    rw [derivative_rootMultiplicity_of_root haf]
    intro h
    calc rootMultiplicity a f
        = rootMultiplicity a f - 1 + 1 := (Nat.sub_add_cancel (Nat.succ_le_iff.1 h0)).symm
      _ <= rootMultiplicity a f - 1 + rootMultiplicity a g := add_le_add le_rfl (Nat.succ_le_iff.1
        ((rootMultiplicity_pos hg0).2 (h haf)))
  · simp [haf, rootMultiplicity_eq_zero haf]
