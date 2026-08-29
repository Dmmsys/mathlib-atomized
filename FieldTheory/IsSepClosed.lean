/-
Copyright (c) 2023 Jz Pan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jz Pan
-/
module

public import Mathlib.FieldTheory.Galois.Basic
public import Mathlib.FieldTheory.SeparableClosure

/-!
# Separably Closed Field

In this file we define the typeclass for separably closed fields and separable closures,
and prove some of their properties.

## Main Definitions

- `IsSepClosed k` is the typeclass saying `k` is a separably closed field, i.e. every separable
  polynomial in `k` splits.

- `IsSepClosure k K` is the typeclass saying `K` is a separable closure of `k`, where `k` is a
  field. This means that `K` is separably closed and separable over `k`.

- `IsSepClosed.lift` is a map from a separable extension `L` of `K`, into any separably
  closed extension `M` of `K`.

- `IsSepClosure.equiv` is a proof that any two separable closures of the
  same field are isomorphic.

- `IsSepClosure.isAlgClosure_of_perfectField`, `IsSepClosure.of_isAlgClosure_of_perfectField`:
  if `k` is a perfect field, then its separable closure coincides with its algebraic closure.

## Tags

separable closure, separably closed

## Related

- `separableClosure`: maximal separable subextension of `K/k`, consisting of all elements of `K`
  which are separable over `k`.

- `separableClosure.isSepClosure`: if `K` is a separably closed field containing `k`, then the
  maximal separable subextension of `K/k` is a separable closure of `k`.

- In particular, a separable closure (`SeparableClosure`) exists.

- `Algebra.IsAlgebraic.isPurelyInseparable_of_isSepClosed`: an algebraic extension of a separably
  closed field is purely inseparable.

-/

@[expose] public section

universe u v w

open Polynomial

variable (k : Type u) [Field k] (K : Type v) [Field K]

/--
Definition of `IsSepClosed` / `IsSepClosed` 的定义

English:
class IsSepClosed
  parameters: : Prop where
  axioms and operations (1):
    - splits_of_separable : forall p : k[X], p.Separable -> p.Splits

中文:
类 是SepClosed
  参数: : 命题 where
  公理与运算 (1 个):
    - splits_of_separable : 对任意 p : k[X], p.可分 -> p.Splits
-/
class IsSepClosed : Prop where
  splits_of_separable : forall p : k[X], p.Separable -> p.Splits

/--
Instance `IsSepClosed.of_isAlgClosed` / 实例 `IsSepClosed.of_isAlgClosed`

English:
instance IsSepClosed.of_isAlgClosed
  signature: [IsAlgClosed k]
  body: ⟨fun p _ => IsAlgClosed.splits p⟩

中文:
实例 是SepClosed.of_isAlgClosed
  签名: [是代数闭 k]
  定义体: ⟨fun p _ => IsAlgClosed.splits p⟩

Depends on / 依赖: IsAlgClosed, IsAlgClosed.splits, splits
-/
instance IsSepClosed.of_isAlgClosed [IsAlgClosed k] : IsSepClosed k :=
  ⟨fun p _ => IsAlgClosed.splits p⟩

variable {k} {K}

/--
theorem `IsSepClosed.splits_codomain` / 定理 `IsSepClosed.splits_codomain`

English:
theorem IsSepClosed.splits_codomain
  statement: [IsSepClosed K] {f : k ->+* K}
  proof: IsSepClosed.splits_of_separable (p.map f) (Separable.map h)

中文:
定理 是SepClosed.splits_codomain
  结论: [是SepClosed K] {f : k ->+* K}
  证明: IsSepClosed.splits_of_separable (p.map f) (Separable.map h)

Depends on / 依赖: IsSepClosed, IsSepClosed.splits_of_separable, Separable, Separable.map, p.map, splits_of_separable
-/
theorem IsSepClosed.splits_codomain [IsSepClosed K] {f : k ->+* K}
    (p : k[X]) (h : p.Separable) : (p.map f).Splits :=
  IsSepClosed.splits_of_separable (p.map f) (Separable.map h)

/--
theorem `IsSepClosed.splits_domain` / 定理 `IsSepClosed.splits_domain`

English:
theorem IsSepClosed.splits_domain
  statement: [IsSepClosed k] {f : k ->+* K}
  proof: (IsSepClosed.splits_of_separable _ h).map f

中文:
定理 是SepClosed.splits_domain
  结论: [是SepClosed k] {f : k ->+* K}
  证明: (IsSepClosed.splits_of_separable _ h).map f

Depends on / 依赖: IsSepClosed, IsSepClosed.splits_of_separable, splits_of_separable
-/
theorem IsSepClosed.splits_domain [IsSepClosed k] {f : k ->+* K}
    (p : k[X]) (h : p.Separable) : (p.map f).Splits :=
  (IsSepClosed.splits_of_separable _ h).map f

namespace IsSepClosed

/--
theorem `exists_root` / 定理 `exists_root`

English:
theorem exists_root
  given: [IsSepClosed k] (p : k[X]) (hp : p.degree != 0) (hsep : p.Separable)
  proof: (IsSepClosed.splits_of_separable p hsep).exists_eval_eq_zero hp

中文:
定理 存在_root
  条件: [是SepClosed k] (p : k[X]) (hp : p.degree != 0) (hsep : p.可分)
  证明: (IsSepClosed.splits_of_separable p hsep).exists_eval_eq_zero hp

Depends on / 依赖: IsSepClosed, IsSepClosed.splits_of_separable, exists_eval_eq_zero, splits_of_separable
-/
theorem exists_root [IsSepClosed k] (p : k[X]) (hp : p.degree != 0) (hsep : p.Separable) :
    exists x, IsRoot p x :=
  (IsSepClosed.splits_of_separable p hsep).exists_eval_eq_zero hp

/--
theorem `exists_root_C_mul_X_pow_add_C_mul_X_add_C` / 定理 `exists_root_C_mul_X_pow_add_C_mul_X_add_C`

English:
theorem exists_root_C_mul_X_pow_add_C_mul_X_add_C
  proof: by
  let f : k[X] := C a * X ^ n + C b * X + C c
  -- Specify `n := 0` below, otherwise Lean unfolds `0` to `Zero.zero`.
have hdeg : f.degree != 0 := degree_ne_of_natDegree_ne (n := 0) by
    have : C 0 * X ^ n + C b * X = 0 * X ^ n + C b * X := by grind
    by_cases ha : a = 0
    · grind [zero_add

中文:
定理 存在_root_C_mul_X_pow_add_C_mul_X_add_C
  证明: by
  let f : k[X] := C a * X ^ n + C b * X + C c
  -- Specify `n := 0` below, otherwise Lean unfolds `0` to `Zero.zero`.
have hdeg : f.degree != 0 := degree_ne_of_natDegree_ne (n := 0) by
    have : C 0 * X ^ n + C b * X = 0 * X ^ n + C b * X := by grind
    by_cases ha : a = 0
    · grind [zero_add
-/
theorem exists_root_C_mul_X_pow_add_C_mul_X_add_C
    [IsSepClosed k] {n : Nat} (a b c : k) (hn : (n : k) = 0) (hn' : 2 <= n) (hb : b != 0) :
    exists x, a * x ^ n + b * x + c = 0 := by
  let f : k[X] := C a * X ^ n + C b * X + C c
  -- Specify `n := 0` below, otherwise Lean unfolds `0` to `Zero.zero`.
have hdeg : f.degree != 0 := degree_ne_of_natDegree_ne (n := 0) by
    have : C 0 * X ^ n + C b * X = 0 * X ^ n + C b * X := by grind
    by_cases ha : a = 0
    · grind [zero_add]
    · grind [natDegree_add_eq_left_of_natDegree_lt]
  have hsep : f.Separable := separable_C_mul_X_pow_add_C_mul_X_add_C a b c hn hb.isUnit
  obtain ⟨x, hx⟩ := exists_root f hdeg hsep
  exact ⟨x, by simpa [f] using hx⟩

/--
theorem `exists_root_C_mul_X_pow_add_C_mul_X_add_C'` / 定理 `exists_root_C_mul_X_pow_add_C_mul_X_add_C'`

English:
theorem exists_root_C_mul_X_pow_add_C_mul_X_add_C'
  proof: exists_root_C_mul_X_pow_add_C_mul_X_add_C a b c ((CharP.cast_eq_zero_iff k p n).2 hn) hn' hb

中文:
定理 存在_root_C_mul_X_pow_add_C_mul_X_add_C'
  证明: exists_root_C_mul_X_pow_add_C_mul_X_add_C a b c ((CharP.cast_eq_zero_iff k p n).2 hn) hn' hb

Depends on / 依赖: CharP.cast_eq_zero_iff, cast_eq_zero_iff, exists_root_C_mul_X_pow_add_C_mul_X_add_C
-/
theorem exists_root_C_mul_X_pow_add_C_mul_X_add_C'
    [IsSepClosed k] (p n : Nat) (a b c : k) [CharP k p] (hn : p ∣ n) (hn' : 2 <= n) (hb : b != 0) :
    exists x, a * x ^ n + b * x + c = 0 :=
  exists_root_C_mul_X_pow_add_C_mul_X_add_C a b c ((CharP.cast_eq_zero_iff k p n).2 hn) hn' hb

variable (k) in
/-- A separably closed perfect field is also algebraically closed. -/
instance (priority := 100) isAlgClosed_of_perfectField [IsSepClosed k] [PerfectField k] :
    IsAlgClosed k :=
  IsAlgClosed.of_exists_root k fun p _ h => exists_root p ((degree_pos_of_irreducible h).ne')
    (PerfectField.separable_of_irreducible h)

/--
theorem `exists_pow_nat_eq` / 定理 `exists_pow_nat_eq`

English:
theorem exists_pow_nat_eq
  given: [IsSepClosed k] (x : k) (n : Nat) [hn : NeZero (n : k)]
  proof: by
  have hn' : 0 < n := Nat.pos_of_ne_zero fun h => by
    rw [h]; rw [Nat.cast_zero] at hn
    exact hn.out rfl
  have : degree (X ^ n - C x) != 0 := by
    rw [degree_X_pow_sub_C hn' x]
    exact (WithBot.coe_lt_coe.2 hn').ne'
  by_cases hx : x = 0
  · exact ⟨0, by rw [hx, pow_eq_zero_iff hn'.ne'

中文:
定理 存在_pow_nat_eq
  条件: [是SepClosed k] (x : k) (n : 自然数) [hn : NeZero (n : k)]
  证明: by
  have hn' : 0 < n := Nat.pos_of_ne_zero fun h => by
    rw [h]; rw [Nat.cast_zero] at hn
    exact hn.out rfl
  have : degree (X ^ n - C x) != 0 := by
    rw [degree_X_pow_sub_C hn' x]
    exact (WithBot.coe_lt_coe.2 hn').ne'
  by_cases hx : x = 0
  · exact ⟨0, by rw [hx, pow_eq_zero_iff hn'.ne'

Depends on / 依赖: IsRoot, IsRoot.def, Nat.cast_zero, Nat.pos_of_ne_zero, WithBot, WithBot.coe_lt_coe, cast_zero, coe_lt_coe, degree, degree_X_pow_sub_C, eval_C, eval_X, eval_pow, eval_sub, exists_root, hn.out, pos_of_ne_zero, pow_eq_zero_iff, separable_X_pow_sub_C, sub_eq_zero
-/
theorem exists_pow_nat_eq [IsSepClosed k] (x : k) (n : Nat) [hn : NeZero (n : k)] :
    exists z, z ^ n = x := by
  have hn' : 0 < n := Nat.pos_of_ne_zero fun h => by
    rw [h]; rw [Nat.cast_zero] at hn
    exact hn.out rfl
  have : degree (X ^ n - C x) != 0 := by
    rw [degree_X_pow_sub_C hn' x]
    exact (WithBot.coe_lt_coe.2 hn').ne'
  by_cases hx : x = 0
  · exact ⟨0, by rw [hx, pow_eq_zero_iff hn'.ne']⟩
· obtain ⟨z, hz⟩ := exists_root _ this separable_X_pow_sub_C x hn.out hx
    use z
    simpa [eval_C, eval_X, eval_pow, eval_sub, IsRoot.def, sub_eq_zero] using hz

/--
theorem `exists_eq_mul_self` / 定理 `exists_eq_mul_self`

English:
theorem exists_eq_mul_self
  given: [IsSepClosed k] (x : k) [h2 : NeZero (2 : k)]
  statement: exists z, x = z * z
  proof: by
  rcases exists_pow_nat_eq x 2 with ⟨z, rfl⟩
  exact ⟨z, sq z⟩

中文:
定理 存在_eq_mul_self
  条件: [是SepClosed k] (x : k) [h2 : NeZero (2 : k)]
  结论: 存在 z, x = z * z
  证明: by
  rcases exists_pow_nat_eq x 2 with ⟨z, rfl⟩
  exact ⟨z, sq z⟩

Depends on / 依赖: exists_pow_nat_eq
-/
theorem exists_eq_mul_self [IsSepClosed k] (x : k) [h2 : NeZero (2 : k)] : exists z, x = z * z := by
  rcases exists_pow_nat_eq x 2 with ⟨z, rfl⟩
  exact ⟨z, sq z⟩

/--
theorem `roots_eq_zero_iff` / 定理 `roots_eq_zero_iff`

English:
theorem roots_eq_zero_iff
  given: [IsSepClosed k] {p : k[X]} (hsep : p.Separable)
  proof: by
  refine ⟨fun h => ?_, fun hp => by rw [hp, roots_C]⟩
  rcases le_or_gt (degree p) 0 with hd | hd
  · exact eq_C_of_degree_le_zero hd
  · obtain ⟨z, hz⟩ := IsSepClosed.exists_root p hd.ne' hsep
    rw [← mem_roots (ne_zero_of_degree_gt hd)]; rw [h] at hz
    simp at hz

中文:
定理 roots_eq_zero_iff
  条件: [是SepClosed k] {p : k[X]} (hsep : p.可分)
  证明: by
  refine ⟨fun h => ?_, fun hp => by rw [hp, roots_C]⟩
  rcases le_or_gt (degree p) 0 with hd | hd
  · exact eq_C_of_degree_le_zero hd
  · obtain ⟨z, hz⟩ := IsSepClosed.exists_root p hd.ne' hsep
    rw [← mem_roots (ne_zero_of_degree_gt hd)]; rw [h] at hz
    simp at hz

Depends on / 依赖: IsSepClosed, IsSepClosed.exists_root, degree, eq_C_of_degree_le_zero, exists_root, hd.ne, le_or_gt, mem_roots, ne_zero_of_degree_gt, roots_C
-/
theorem roots_eq_zero_iff [IsSepClosed k] {p : k[X]} (hsep : p.Separable) :
    p.roots = 0 ↔ p = Polynomial.C (p.coeff 0) := by
  refine ⟨fun h => ?_, fun hp => by rw [hp, roots_C]⟩
  rcases le_or_gt (degree p) 0 with hd | hd
  · exact eq_C_of_degree_le_zero hd
  · obtain ⟨z, hz⟩ := IsSepClosed.exists_root p hd.ne' hsep
    rw [← mem_roots (ne_zero_of_degree_gt hd)]; rw [h] at hz
    simp at hz

/--
theorem `exists_eval₂_eq_zero_of_injective` / 定理 `exists_eval₂_eq_zero_of_injective`

English:
theorem exists_eval₂_eq_zero_of_injective
  statement: {k : Type*} [CommSemiring k] [IsSepClosed K] (f : k ->+* K)
  proof: let ⟨x, hx⟩ := exists_root (p.map f) (by rwa [degree_map_eq_of_injective hf])
    (Separable.map hsep)
  ⟨x, by rwa [eval₂_eq_eval_map, ← IsRoot]⟩

中文:
定理 存在_eval₂_eq_zero_of_injective
  结论: {k : 类型} [交换半环 k] [是SepClosed K] (f : k ->+* K)
  证明: let ⟨x, hx⟩ := exists_root (p.map f) (by rwa [degree_map_eq_of_injective hf])
    (Separable.map hsep)
  ⟨x, by rwa [eval₂_eq_eval_map, ← IsRoot]⟩

Depends on / 依赖: IsRoot, Separable, Separable.map, degree_map_eq_of_injective, exists_root, p.map
-/
theorem exists_eval₂_eq_zero_of_injective {k : Type*} [CommSemiring k] [IsSepClosed K] (f : k ->+* K)
    (hf : Function.Injective f) (p : k[X]) (hp : p.degree != 0) (hsep : p.Separable) :
    exists x, p.eval₂ f x = 0 :=
  let ⟨x, hx⟩ := exists_root (p.map f) (by rwa [degree_map_eq_of_injective hf])
    (Separable.map hsep)
  ⟨x, by rwa [eval₂_eq_eval_map, ← IsRoot]⟩

/--
theorem `exists_eval₂_eq_zero` / 定理 `exists_eval₂_eq_zero`

English:
theorem exists_eval₂_eq_zero
  statement: {k : Type*} [CommRing k] [IsSimpleRing k] [IsSepClosed K] (f : k ->+* K)
  proof: exists_eval₂_eq_zero_of_injective _ f.injective _ hp hsep

中文:
定理 存在_eval₂_eq_zero
  结论: {k : 类型} [交换环 k] [是单环 k] [是SepClosed K] (f : k ->+* K)
  证明: exists_eval₂_eq_zero_of_injective _ f.injective _ hp hsep

Depends on / 依赖: f.injective, injective
-/
theorem exists_eval₂_eq_zero {k : Type*} [CommRing k] [IsSimpleRing k] [IsSepClosed K] (f : k ->+* K)
    (p : k[X]) (hp : p.degree != 0) (hsep : p.Separable) : exists x, p.eval₂ f x = 0 :=
  exists_eval₂_eq_zero_of_injective _ f.injective _ hp hsep

variable (K)

/--
theorem `exists_aeval_eq_zero` / 定理 `exists_aeval_eq_zero`

English:
theorem exists_aeval_eq_zero
  statement: {k : Type*} [CommSemiring k] [IsSepClosed K] [Algebra k K]
  proof: exists_eval₂_eq_zero_of_injective _ (FaithfulSMul.algebraMap_injective ..) p hp hsep

中文:
定理 存在_aeval_eq_zero
  结论: {k : 类型} [交换半环 k] [是SepClosed K] [代数 k K]
  证明: exists_eval₂_eq_zero_of_injective _ (FaithfulSMul.algebraMap_injective ..) p hp hsep

Depends on / 依赖: FaithfulSMul, FaithfulSMul.algebraMap_injective, algebraMap_injective
-/
theorem exists_aeval_eq_zero {k : Type*} [CommSemiring k] [IsSepClosed K] [Algebra k K]
    [FaithfulSMul k K] (p : k[X]) (hp : p.degree != 0) (hsep : p.Separable) :
    exists x : K, p.aeval x = 0 :=
  exists_eval₂_eq_zero_of_injective _ (FaithfulSMul.algebraMap_injective ..) p hp hsep

variable (k) {K}

/--
theorem `of_exists_root` / 定理 `of_exists_root`

English:
theorem of_exists_root
  given: (H : forall p : k[X], p.Monic -> Irreducible p -> Separable p -> exists x, p.eval x = 0)
  proof: by
  replace H (p : k[X]) (hp : Irreducible p) (hs : Separable p) : exists x, p.eval x = 0 := by
    obtain ⟨x, hx⟩ := H (p * C (leadingCoeff p)⁻¹) (monic_mul_leadingCoeff_inv hp.ne_zero)
      (irreducible_mul_leadingCoeff_inv.mpr hp) (hs.mul_unit (by aesop))
    exact ⟨x, by simpa [hp.ne_zero] usi

中文:
定理 of_存在_root
  条件: (H : 对任意 p : k[X], p.Monic -> 不可约 p -> 可分 p -> 存在 x, p.eval x = 0)
  证明: by
  replace H (p : k[X]) (hp : Irreducible p) (hs : Separable p) : exists x, p.eval x = 0 := by
    obtain ⟨x, hx⟩ := H (p * C (leadingCoeff p)⁻¹) (monic_mul_leadingCoeff_inv hp.ne_zero)
      (irreducible_mul_leadingCoeff_inv.mpr hp) (hs.mul_unit (by aesop))
    exact ⟨x, by simpa [hp.ne_zero] usi

Depends on / 依赖: Irreducible, Separable, Splits, Splits.multisetProd, UniqueF, UniqueFactorizationMonoid, UniqueFactorizationMonoid.factors_prod, factors_prod, hp.ne_zero, hs.mul_unit, irreducible_mul_leadingCoeff_inv, irreducible_mul_leadingCoeff_inv.mpr, isUnit, leadingCoeff, monic_mul_leadingCoeff_inv, mul_unit, multisetProd, ne_zero, p.eval, replace
-/
theorem of_exists_root (H : forall p : k[X], p.Monic -> Irreducible p -> Separable p -> exists x, p.eval x = 0) :
    IsSepClosed k := by
  replace H (p : k[X]) (hp : Irreducible p) (hs : Separable p) : exists x, p.eval x = 0 := by
    obtain ⟨x, hx⟩ := H (p * C (leadingCoeff p)⁻¹) (monic_mul_leadingCoeff_inv hp.ne_zero)
      (irreducible_mul_leadingCoeff_inv.mpr hp) (hs.mul_unit (by aesop))
    exact ⟨x, by simpa [hp.ne_zero] using hx⟩
  refine ⟨fun p hp => ?_⟩
  by_cases hp0 : p = 0
  · simp [hp0]
  obtain ⟨u, hu⟩ := UniqueFactorizationMonoid.factors_prod hp0
  rw [← hu]
  refine (Splits.multisetProd fun f hf => ?_).mul u.isUnit.splits
  let h := UniqueFactorizationMonoid.irreducible_of_factor f hf
  obtain ⟨x, hx⟩ := H f h (hp.of_dvd (UniqueFactorizationMonoid.dvd_of_mem_factors hf))
  exact Splits.of_degree_eq_one (degree_eq_one_of_irreducible_of_root h hx)

/--
theorem `degree_eq_one_of_irreducible` / 定理 `degree_eq_one_of_irreducible`

English:
theorem degree_eq_one_of_irreducible
  statement: [IsSepClosed k] {p : k[X]}
  proof: (IsSepClosed.splits_of_separable p hsep).degree_eq_one_of_irreducible hp

中文:
定理 degree_eq_one_of_irreducible
  结论: [是SepClosed k] {p : k[X]}
  证明: (IsSepClosed.splits_of_separable p hsep).degree_eq_one_of_irreducible hp

Depends on / 依赖: IsSepClosed, IsSepClosed.splits_of_separable, degree_eq_one_of_irreducible, splits_of_separable
-/
theorem degree_eq_one_of_irreducible [IsSepClosed k] {p : k[X]}
    (hp : Irreducible p) (hsep : p.Separable) : p.degree = 1 :=
  (IsSepClosed.splits_of_separable p hsep).degree_eq_one_of_irreducible hp

variable (K)

/--
theorem `algebraMap_surjective` / 定理 `algebraMap_surjective`

English:
theorem algebraMap_surjective
  proof: by
  refine fun x => ⟨-(minpoly k x).coeff 0, ?_⟩
  have hq : (minpoly k x).leadingCoeff = 1 := minpoly.monic (Algebra.IsSeparable.isIntegral k x)
  have hsep : IsSeparable k x := Algebra.IsSeparable.isSeparable k x
  have h : (minpoly k x).degree = 1 :=
    degree_eq_one_of_irreducible k (minpoly.i

中文:
定理 algebraMap_surjective
  证明: by
  refine fun x => ⟨-(minpoly k x).coeff 0, ?_⟩
  have hq : (minpoly k x).leadingCoeff = 1 := minpoly.monic (Algebra.IsSeparable.isIntegral k x)
  have hsep : IsSeparable k x := Algebra.IsSeparable.isSeparable k x
  have h : (minpoly k x).degree = 1 :=
    degree_eq_one_of_irreducible k (minpoly.i

Depends on / 依赖: Algebra, Algebra.IsSeparable.isIntegral, Algebra.IsSeparable.isSeparable, IsSeparable, aeval_X, aeval_add, degree, degree_eq_one_of_irreducible, eq_X_add_C_of_degree_eq_one, irreducible, isIntegral, isSeparable, leadingCoeff, minpoly, minpoly.aeval, minpoly.irreducible, minpoly.monic, one_mul
-/
theorem algebraMap_surjective
    [IsSepClosed k] [Algebra k K] [Algebra.IsSeparable k K] :
    Function.Surjective (algebraMap k K) := by
  refine fun x => ⟨-(minpoly k x).coeff 0, ?_⟩
  have hq : (minpoly k x).leadingCoeff = 1 := minpoly.monic (Algebra.IsSeparable.isIntegral k x)
  have hsep : IsSeparable k x := Algebra.IsSeparable.isSeparable k x
  have h : (minpoly k x).degree = 1 :=
    degree_eq_one_of_irreducible k (minpoly.irreducible (Algebra.IsSeparable.isIntegral k x)) hsep
  have : aeval x (minpoly k x) = 0 := minpoly.aeval k x
  rw [eq_X_add_C_of_degree_eq_one h]; rw [hq]; rw [C_1]; rw [one_mul]; rw [aeval_add]; rw [aeval_X]; rw [aeval_C]; rw [add_eq_zero_iff_eq_neg] at this
  exact (map_neg (algebraMap k K) ((minpoly k x).coeff 0)).symm ▸ this.symm

/--
lemma `algebraMap_bijective` / 引理 `algebraMap_bijective`

English:
lemma algebraMap_bijective
  given: [IsSepClosed k] [Algebra k K] [Algebra.IsSeparable k K]
  proof: ⟨RingHom.injective _, IsSepClosed.algebraMap_surjective _ _⟩

中文:
引理 algebraMap_bijective
  条件: [是SepClosed k] [代数 k K] [代数.是可分 k K]
  证明: ⟨RingHom.injective _, IsSepClosed.algebraMap_surjective _ _⟩

Depends on / 依赖: IsSepClosed, IsSepClosed.algebraMap_surjective, RingHom, RingHom.injective, algebraMap_surjective, injective
-/
lemma algebraMap_bijective [IsSepClosed k] [Algebra k K] [Algebra.IsSeparable k K] :
    Function.Bijective (algebraMap k K) :=
  ⟨RingHom.injective _, IsSepClosed.algebraMap_surjective _ _⟩

end IsSepClosed

/--
theorem `IntermediateField.eq_bot_of_isSepClosed_of_isSeparable` / 定理 `IntermediateField.eq_bot_of_isSepClosed_of_isSeparable`

English:
theorem IntermediateField.eq_bot_of_isSepClosed_of_isSeparable
  statement: [IsSepClosed k] [Algebra k K]
  proof: bot_unique fun x hx => by
  obtain ⟨y, hy⟩ := IsSepClosed.algebraMap_surjective k L ⟨x, hx⟩
  exact ⟨y, congr_arg (algebraMap L K) hy⟩

中文:
定理 中间域.eq_bot_of_isSepClosed_of_isSeparable
  结论: [是SepClosed k] [代数 k K]
  证明: bot_unique fun x hx => by
  obtain ⟨y, hy⟩ := IsSepClosed.algebraMap_surjective k L ⟨x, hx⟩
  exact ⟨y, congr_arg (algebraMap L K) hy⟩

Depends on / 依赖: IsSepClosed, IsSepClosed.algebraMap_surjective, algebraMap, algebraMap_surjective, bot_unique, congr_arg
-/
theorem IntermediateField.eq_bot_of_isSepClosed_of_isSeparable [IsSepClosed k] [Algebra k K]
    (L : IntermediateField k K) [Algebra.IsSeparable k L] : L = ⊥ := bot_unique fun x hx => by
  obtain ⟨y, hy⟩ := IsSepClosed.algebraMap_surjective k L ⟨x, hx⟩
  exact ⟨y, congr_arg (algebraMap L K) hy⟩

variable (k) (K)

/--
Definition of `IsSepClosure` / `IsSepClosure` 的定义

English:
class IsSepClosure
  parameters: [Algebra k K]
  axioms and operations (2):
    - sep_closed : IsSepClosed K
    - separable : Algebra.IsSeparable k K

中文:
类 是SepClosure
  参数: [代数 k K]
  公理与运算 (2 个):
    - sep_closed : 是SepClosed K
    - separable : 代数.是可分 k K
-/
class IsSepClosure [Algebra k K] : Prop where
  sep_closed : IsSepClosed K
  separable : Algebra.IsSeparable k K

/--
Instance `IsSepClosure.self_of_isSepClosed` / 实例 `IsSepClosure.self_of_isSepClosed`

English:
instance IsSepClosure.self_of_isSepClosed
  signature: [IsSepClosed k]
  body: ⟨by assumption, Algebra.isSeparable_self k⟩

中文:
实例 是SepClosure.self_of_isSepClosed
  签名: [是SepClosed k]
  定义体: ⟨by assumption, Algebra.isSeparable_self k⟩

Depends on / 依赖: Algebra, Algebra.isSeparable_self, isSeparable_self
-/
instance IsSepClosure.self_of_isSepClosed [IsSepClosed k] : IsSepClosure k k :=
  ⟨by assumption, Algebra.isSeparable_self k⟩

/-- If `K` is perfect and is a separable closure of `k`,
then it is also an algebraic closure of `k`. -/
instance (priority := 100) IsSepClosure.isAlgClosure_of_perfectField_top
    [Algebra k K] [IsSepClosure k K] [PerfectField K] : IsAlgClosure k K :=
  haveI : IsSepClosed K := IsSepClosure.sep_closed k
  ⟨inferInstance, IsSepClosure.separable.isAlgebraic⟩

/-- If `k` is perfect, `K` is a separable closure of `k`,
then it is also an algebraic closure of `k`. -/
instance (priority := 100) IsSepClosure.isAlgClosure_of_perfectField
    [Algebra k K] [IsSepClosure k K] [PerfectField k] : IsAlgClosure k K :=
  have halg : Algebra.IsAlgebraic k K := IsSepClosure.separable.isAlgebraic
  haveI := halg.perfectField; inferInstance

/-- If `k` is perfect, `K` is an algebraic closure of `k`,
then it is also a separable closure of `k`. -/
instance (priority := 100) IsSepClosure.of_isAlgClosure_of_perfectField
    [Algebra k K] [IsAlgClosure k K] [PerfectField k] : IsSepClosure k K :=
  ⟨haveI := IsAlgClosure.isAlgClosed (R := k) (K := K); inferInstance,
    (IsAlgClosure.isAlgebraic (R := k) (K := K)).isSeparable_of_perfectField⟩

variable {k} {K}

/--
theorem `isSepClosure_iff` / 定理 `isSepClosure_iff`

English:
theorem isSepClosure_iff
  given: [Algebra k K]
  proof: ⟨fun h => ⟨h.1, h.2⟩, fun h => ⟨h.1, h.2⟩⟩

中文:
定理 isSepClosure_iff
  条件: [代数 k K]
  证明: ⟨fun h => ⟨h.1, h.2⟩, fun h => ⟨h.1, h.2⟩⟩
-/
theorem isSepClosure_iff [Algebra k K] :
    IsSepClosure k K ↔ IsSepClosed K ∧ Algebra.IsSeparable k K :=
  ⟨fun h => ⟨h.1, h.2⟩, fun h => ⟨h.1, h.2⟩⟩

namespace IsSepClosure

/--
Instance `isSeparable` / 实例 `isSeparable`

English:
instance isSeparable
  signature: [Algebra k K] [IsSepClosure k K]
  body: IsSepClosure.separable

中文:
实例 isSeparable
  签名: [代数 k K] [是SepClosure k K]
  定义体: IsSepClosure.separable

Depends on / 依赖: IsSepClosure, IsSepClosure.separable, separable
-/
instance isSeparable [Algebra k K] [IsSepClosure k K] : Algebra.IsSeparable k K :=
  IsSepClosure.separable

instance (priority := 100) isGalois [Algebra k K] [IsSepClosure k K] : IsGalois k K where
  to_isSeparable := IsSepClosure.separable
  to_normal.toIsAlgebraic := inferInstance
  to_normal.splits' x := (IsSepClosure.sep_closed k).splits_codomain _
    (Algebra.IsSeparable.isSeparable k x)

end IsSepClosure

namespace IsSepClosed

variable {K : Type u} (L : Type v) {M : Type w} [Field K] [Field L] [Algebra K L] [Field M]
  [Algebra K M] [IsSepClosed M]

/--
theorem `surjective_domRestrict_of_isSeparable` / 定理 `surjective_domRestrict_of_isSeparable`

English:
theorem surjective_domRestrict_of_isSeparable
  statement: {E : Type*}
  proof: fun f => IntermediateField.exists_algHom_of_splits' (E := E) f
    fun s => ⟨Algebra.IsSeparable.isIntegral L s,
IsSepClosed.splits_codomain _ Algebra.IsSeparable.isSeparable L s⟩

@[deprecated (since := "2026-07-19")]
alias surjective_restrictDomain_of_isSeparable := surjective_domRestrict_of_isSep

中文:
定理 surjective_domRestrict_of_isSeparable
  结论: {E : 类型}
  证明: fun f => IntermediateField.exists_algHom_of_splits' (E := E) f
    fun s => ⟨Algebra.IsSeparable.isIntegral L s,
IsSepClosed.splits_codomain _ Algebra.IsSeparable.isSeparable L s⟩

@[deprecated (since := "2026-07-19")]
alias surjective_restrictDomain_of_isSeparable := surjective_domRestrict_of_isSep

Depends on / 依赖: Algebra, Algebra.IsSeparable.isIntegral, Algebra.IsSeparable.isSeparable, IntermediateField, IntermediateField.exists_algHom_of_splits, IsSepClosed, IsSepClosed.splits_codomain, IsSeparable, exists_algHom_of_splits, isIntegral, isSeparable, splits_codomain
-/
theorem surjective_domRestrict_of_isSeparable {E : Type*}
    [Field E] [Algebra K E] [Algebra L E] [IsScalarTower K L E] [Algebra.IsSeparable L E] :
    Function.Surjective fun φ : E ->ₐ[K] M => φ.domRestrict L :=
  fun f => IntermediateField.exists_algHom_of_splits' (E := E) f
    fun s => ⟨Algebra.IsSeparable.isIntegral L s,
IsSepClosed.splits_codomain _ Algebra.IsSeparable.isSeparable L s⟩

@[deprecated (since := "2026-07-19")]
alias surjective_restrictDomain_of_isSeparable := surjective_domRestrict_of_isSeparable

variable [Algebra.IsSeparable K L] {L}

/-- A (random) homomorphism from a separable extension L of K into a separably
  closed extension M of K. -/
noncomputable irreducible_def lift : L ->ₐ[K] M :=
Classical.choice IntermediateField.nonempty_algHom_of_adjoin_splits
    (fun x _ => ⟨Algebra.IsSeparable.isIntegral K x,
      splits_codomain _ (Algebra.IsSeparable.isSeparable K x)⟩)
    (IntermediateField.adjoin_univ K L)

end IsSepClosed

namespace IsSepClosure

variable (K : Type u) [Field K] (L : Type v) (M : Type w) [Field L] [Field M]
variable [Algebra K M] [IsSepClosure K M]
variable [Algebra K L] [IsSepClosure K L]

attribute [local instance] IsSepClosure.sep_closed in
/--
Definition of `equiv` / `equiv` 的定义

English:
definition equiv
  signature: : L ≃ₐ[K] M
  body: AlgEquiv.ofBijective _ (Normal.toIsAlgebraic.algHom_bijective₂
    (IsSepClosed.lift : L ->ₐ[K] M) (IsSepClosed.lift : M ->ₐ[K] L)).1

中文:
定义 equiv
  签名: : L ≃ₐ[K] M
  定义体: AlgEquiv.ofBijective _ (Normal.toIsAlgebraic.algHom_bijective₂
    (IsSepClosed.lift : L ->ₐ[K] M) (IsSepClosed.lift : M ->ₐ[K] L)).1

Depends on / 依赖: AlgEquiv, AlgEquiv.ofBijective, IsSepClosed, IsSepClosed.lift, Normal, Normal.toIsAlgebraic.algHom_bijective, ofBijective, toIsAlgebraic
-/
noncomputable def equiv : L ≃ₐ[K] M :=
  AlgEquiv.ofBijective _ (Normal.toIsAlgebraic.algHom_bijective₂
    (IsSepClosed.lift : L ->ₐ[K] M) (IsSepClosed.lift : M ->ₐ[K] L)).1

end IsSepClosure

section separableClosure

variable (F E : Type*) [Field F] [Field E] [Algebra F E]

/-- If `E` is normal over `F`, then the separable closure of `F` in `E` is Galois (i.e.
normal and separable) over `F`. -/
@[stacks 0EXK]
/--
Instance `separableClosure.isGalois` / 实例 `separableClosure.isGalois`

English:
instance separableClosure.isGalois
  signature: [Normal F E]
  body: separableClosure.isSeparable F E
  to_normal := by
    rw [← separableClosure.normalClosure_eq_self]
    exact normalClosure.normal F _ E

中文:
实例 separableClosure.isGalois
  签名: [正规 F E]
  定义体: separableClosure.isSeparable F E
  to_normal := by
    rw [← separableClosure.normalClosure_eq_self]
    exact normalClosure.normal F _ E

Depends on / 依赖: isSeparable, separableClosure, separableClosure.isSeparable
-/
instance separableClosure.isGalois [Normal F E] : IsGalois F (separableClosure F E) where
  to_isSeparable := separableClosure.isSeparable F E
  to_normal := by
    rw [← separableClosure.normalClosure_eq_self]
    exact normalClosure.normal F _ E

/--
theorem `IsSepClosed.separableClosure_eq_bot_iff` / 定理 `IsSepClosed.separableClosure_eq_bot_iff`

English:
theorem IsSepClosed.separableClosure_eq_bot_iff
  given: [IsSepClosed E]
  proof: by
  refine ⟨fun h => IsSepClosed.of_exists_root _ fun p _ hirr hsep => ?_,
    fun _ => IntermediateField.eq_bot_of_isSepClosed_of_isSeparable _⟩
  obtain ⟨x, hx⟩ := IsSepClosed.exists_aeval_eq_zero E p (degree_pos_of_irreducible hirr).ne' hsep
  obtain ⟨x, rfl⟩ := h ▸ mem_separableClosure_iff.2 (h

中文:
定理 是SepClosed.separableClosure_eq_bot_iff
  条件: [是SepClosed E]
  证明: by
  refine ⟨fun h => IsSepClosed.of_exists_root _ fun p _ hirr hsep => ?_,
    fun _ => IntermediateField.eq_bot_of_isSepClosed_of_isSeparable _⟩
  obtain ⟨x, hx⟩ := IsSepClosed.exists_aeval_eq_zero E p (degree_pos_of_irreducible hirr).ne' hsep
  obtain ⟨x, rfl⟩ := h ▸ mem_separableClosure_iff.2 (h

Depends on / 依赖: Algebra, Algebra.ofId_apply, IntermediateField, IntermediateField.eq_bot_of_isSepClosed_of_isSeparable, IsSepClosed, IsSepClosed.exists_aeval_eq_zero, IsSepClosed.of_exists_root, degree_pos_of_irreducible, eq_bot_of_isSepClosed_of_isSeparable, exists_aeval_eq_zero, hsep.of_dvd, mem_separableClosure_iff, minpoly, minpoly.dvd, ofId_apply, of_dvd, of_exists_root
-/
theorem IsSepClosed.separableClosure_eq_bot_iff [IsSepClosed E] :
    separableClosure F E = ⊥ ↔ IsSepClosed F := by
  refine ⟨fun h => IsSepClosed.of_exists_root _ fun p _ hirr hsep => ?_,
    fun _ => IntermediateField.eq_bot_of_isSepClosed_of_isSeparable _⟩
  obtain ⟨x, hx⟩ := IsSepClosed.exists_aeval_eq_zero E p (degree_pos_of_irreducible hirr).ne' hsep
  obtain ⟨x, rfl⟩ := h ▸ mem_separableClosure_iff.2 (hsep.of_dvd <| minpoly.dvd _ x hx)
  exact ⟨x, by simpa [Algebra.ofId_apply] using hx⟩

/--
Instance `separableClosure.isSepClosure` / 实例 `separableClosure.isSepClosure`

English:
instance separableClosure.isSepClosure
  signature: [IsSepClosed E]
  body: ⟨(IsSepClosed.separableClosure_eq_bot_iff _ E).mp (separableClosure.separableClosure_eq_bot F E),
    isSeparable F E⟩

中文:
实例 separableClosure.isSepClosure
  签名: [是SepClosed E]
  定义体: ⟨(IsSepClosed.separableClosure_eq_bot_iff _ E).mp (separableClosure.separableClosure_eq_bot F E),
    isSeparable F E⟩

Depends on / 依赖: IsSepClosed, IsSepClosed.separableClosure_eq_bot_iff, isSeparable, separableClosure, separableClosure.separableClosure_eq_bot, separableClosure_eq_bot, separableClosure_eq_bot_iff
-/
instance separableClosure.isSepClosure [IsSepClosed E] : IsSepClosure F (separableClosure F E) :=
  ⟨(IsSepClosed.separableClosure_eq_bot_iff _ E).mp (separableClosure.separableClosure_eq_bot F E),
    isSeparable F E⟩

/--
Definition of `SeparableClosure` / `SeparableClosure` 的定义

English:
abbreviation SeparableClosure
  signature: : Type _
  body: separableClosure F (AlgebraicClosure F)

中文:
缩写 可分闭包
  签名: : 类型 _
  定义体: separableClosure F (AlgebraicClosure F)

Depends on / 依赖: AlgebraicClosure, separableClosure
-/
abbrev SeparableClosure : Type _ := separableClosure F (AlgebraicClosure F)

/--
Instance `SeparableClosure.isSepClosed` / 实例 `SeparableClosure.isSepClosed`

English:
instance SeparableClosure.isSepClosed
  signature: : IsSepClosed (SeparableClosure F)
  body: (inferInstance : IsSepClosure F (SeparableClosure F)).sep_closed

中文:
实例 可分闭包.isSepClosed
  签名: : 是SepClosed (可分闭包 F)
  定义体: (inferInstance : IsSepClosure F (SeparableClosure F)).sep_closed

Depends on / 依赖: IsSepClosure, SeparableClosure, sep_closed
-/
instance SeparableClosure.isSepClosed : IsSepClosed (SeparableClosure F) :=
  (inferInstance : IsSepClosure F (SeparableClosure F)).sep_closed

end separableClosure
