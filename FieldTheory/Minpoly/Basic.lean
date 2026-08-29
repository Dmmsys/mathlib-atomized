/-
Copyright (c) 2019 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes, Johan Commelin
-/
module

public import Mathlib.RingTheory.IntegralClosure.IsIntegral.Basic

/-!
# Minimal polynomials

This file defines the minimal polynomial of an element `x` of an `A`-algebra `B`,
under the assumption that x is integral over `A`, and derives some basic properties
such as irreducibility under the assumption `B` is a domain.

-/

@[expose] public section


open Polynomial Set Function

variable {A B B' : Type*}

section MinPolyDef

variable (A) [CommRing A] [Ring B] [Algebra A B]

open scoped Classical in
/-- Suppose `x : B`, where `B` is an `A`-algebra.

The minimal polynomial `minpoly A x` of `x`
is a monic polynomial with coefficients in `A` of smallest degree that has `x` as its root,
if such exists (`IsIntegral A x`) or zero otherwise.

For example, if `V` is a `𝕜`-vector space for some field `𝕜` and `f : V →ₗ[𝕜] V` then
the minimal polynomial of `f` is `minpoly 𝕜 f`.
-/
@[stacks 09GM]
/--
Definition of `minpoly` / `minpoly` 的定义

English:
definition minpoly
  signature: (x : B)
  body: if hx : IsIntegral A x then degree_lt_wf.min _ hx else 0

中文:
定义 minpoly
  签名: (x : B)
  定义体: if hx : IsIntegral A x then degree_lt_wf.min _ hx else 0

Depends on / 依赖: IsIntegral, Module, degree_lt_wf, degree_lt_wf.min
-/
noncomputable def minpoly (x : B) : A[X] :=
  if hx : IsIntegral A x then degree_lt_wf.min _ hx else 0

end MinPolyDef

namespace minpoly

section CommRing

variable [CommRing A] [Ring B] [Ring B'] [Algebra A B] [Algebra A B']
variable {x : B}

/--
theorem `monic` / 定理 `monic`

English:
theorem monic
  given: (hx : IsIntegral A x)
  statement: Monic (minpoly A x)
  proof: by
  delta minpoly
  rw [dif_pos hx]
  exact (degree_lt_wf.min_mem _ hx).1

中文:
定理 monic
  条件: (hx : 是整 A x)
  结论: Monic (minpoly A x)
  证明: by
  delta minpoly
  rw [dif_pos hx]
  exact (degree_lt_wf.min_mem _ hx).1

Depends on / 依赖: degree_lt_wf, degree_lt_wf.min_mem, dif_pos, min_mem, minpoly
-/
theorem monic (hx : IsIntegral A x) : Monic (minpoly A x) := by
  delta minpoly
  rw [dif_pos hx]
  exact (degree_lt_wf.min_mem _ hx).1

/--
theorem `ne_zero` / 定理 `ne_zero`

English:
theorem ne_zero
  given: [Nontrivial A] (hx : IsIntegral A x)
  statement: minpoly A x != 0
  proof: (monic hx).ne_zero

中文:
定理 ne_zero
  条件: [非平凡 A] (hx : 是整 A x)
  结论: minpoly A x != 0
  证明: (monic hx).ne_zero

Depends on / 依赖: ne_zero
-/
theorem ne_zero [Nontrivial A] (hx : IsIntegral A x) : minpoly A x != 0 :=
  (monic hx).ne_zero

/--
theorem `eq_zero` / 定理 `eq_zero`

English:
theorem eq_zero
  given: (hx : ¬IsIntegral A x)
  statement: minpoly A x = 0
  proof: dif_neg hx

中文:
定理 eq_zero
  条件: (hx : ¬是整 A x)
  结论: minpoly A x = 0
  证明: dif_neg hx

Depends on / 依赖: dif_neg
-/
theorem eq_zero (hx : ¬IsIntegral A x) : minpoly A x = 0 :=
  dif_neg hx

/--
theorem `ne_zero_iff` / 定理 `ne_zero_iff`

English:
theorem ne_zero_iff
  given: [Nontrivial A]
  statement: minpoly A x != 0 ↔ IsIntegral A x
  proof: ⟨fun h => of_not_not eq_zero.mt h, ne_zero⟩

中文:
定理 ne_zero_iff
  条件: [非平凡 A]
  结论: minpoly A x != 0 ↔ 是整 A x
  证明: ⟨fun h => of_not_not eq_zero.mt h, ne_zero⟩

Depends on / 依赖: eq_zero, eq_zero.mt, ne_zero, of_not_not
-/
theorem ne_zero_iff [Nontrivial A] : minpoly A x != 0 ↔ IsIntegral A x :=
⟨fun h => of_not_not eq_zero.mt h, ne_zero⟩

/--
theorem `algHom_eq` / 定理 `algHom_eq`

English:
theorem algHom_eq
  given: (f : B ->ₐ[A] B') (hf : Function.Injective f) (x : B)
  proof: by
  classical
  simp_rw [minpoly, isIntegral_algHom_iff _ hf, ← Polynomial.aeval_def, aeval_algHom,
    AlgHom.comp_apply, _root_.map_eq_zero_iff f hf]

中文:
定理 algHom_eq
  条件: (f : B ->ₐ[A] B') (hf : 函数.单射 f) (x : B)
  证明: by
  classical
  simp_rw [minpoly, isIntegral_algHom_iff _ hf, ← Polynomial.aeval_def, aeval_algHom,
    AlgHom.comp_apply, _root_.map_eq_zero_iff f hf]

Depends on / 依赖: AlgHom, AlgHom.comp_apply, Polynomial, Polynomial.aeval_def, _root_, _root_.map_eq_zero_iff, aeval_algHom, aeval_def, classical, comp_apply, isIntegral_algHom_iff, map_eq_zero_iff, minpoly, simp_rw
-/
theorem algHom_eq (f : B ->ₐ[A] B') (hf : Function.Injective f) (x : B) :
    minpoly A (f x) = minpoly A x := by
  classical
  simp_rw [minpoly, isIntegral_algHom_iff _ hf, ← Polynomial.aeval_def, aeval_algHom,
    AlgHom.comp_apply, _root_.map_eq_zero_iff f hf]

/--
theorem `algebraMap_eq` / 定理 `algebraMap_eq`

English:
theorem algebraMap_eq
  statement: {B} [CommRing B] [Algebra A B] [Algebra B B'] [IsScalarTower A B B']
  proof: algHom_eq (IsScalarTower.toAlgHom A B B') h x

@[simp]

中文:
定理 algebraMap_eq
  结论: {B} [交换环 B] [代数 A B] [代数 B B'] [标量塔 A B B']
  证明: algHom_eq (IsScalarTower.toAlgHom A B B') h x

@[simp]

Depends on / 依赖: IsScalarTower, IsScalarTower.toAlgHom, algHom_eq, toAlgHom
-/
theorem algebraMap_eq {B} [CommRing B] [Algebra A B] [Algebra B B'] [IsScalarTower A B B']
    (h : Function.Injective (algebraMap B B')) (x : B) :
    minpoly A (algebraMap B B' x) = minpoly A x :=
  algHom_eq (IsScalarTower.toAlgHom A B B') h x

@[simp]
/--
theorem `algEquiv_eq` / 定理 `algEquiv_eq`

English:
theorem algEquiv_eq
  given: (f : B ≃ₐ[A] B') (x : B)
  statement: minpoly A (f x) = minpoly A x
  proof: algHom_eq (f : B ->ₐ[A] B') f.injective x

中文:
定理 algEquiv_eq
  条件: (f : B ≃ₐ[A] B') (x : B)
  结论: minpoly A (f x) = minpoly A x
  证明: algHom_eq (f : B ->ₐ[A] B') f.injective x

Depends on / 依赖: algHom_eq, f.injective, injective
-/
theorem algEquiv_eq (f : B ≃ₐ[A] B') (x : B) : minpoly A (f x) = minpoly A x :=
  algHom_eq (f : B ->ₐ[A] B') f.injective x

section
variable (A x)

/-- An element is a root of its minimal polynomial. -/
@[simp]
/--
theorem `aeval` / 定理 `aeval`

English:
theorem aeval
  statement: aeval x (minpoly A x) = 0
  proof: by
  delta minpoly
  split_ifs with hx
  · exact (degree_lt_wf.min_mem _ hx).2
  · exact aeval_zero _

中文:
定理 aeval
  结论: aeval x (minpoly A x) = 0
  证明: by
  delta minpoly
  split_ifs with hx
  · exact (degree_lt_wf.min_mem _ hx).2
  · exact aeval_zero _

Depends on / 依赖: aeval_zero, degree_lt_wf, degree_lt_wf.min_mem, min_mem, minpoly, split_ifs
-/
theorem aeval : aeval x (minpoly A x) = 0 := by
  delta minpoly
  split_ifs with hx
  · exact (degree_lt_wf.min_mem _ hx).2
  · exact aeval_zero _

/-- Given any `f : B →ₐ[A] B'` and any `x : L`, the minimal polynomial of `x` vanishes at `f x`. -/
@[simp]
/--
theorem `aeval_algHom` / 定理 `aeval_algHom`

English:
theorem aeval_algHom
  given: (f : B ->ₐ[A] B') (x : B)
  statement: (Polynomial.aeval (f x)) (minpoly A x) = 0
  proof: by
  rw [Polynomial.aeval_algHom]; rw [AlgHom.coe_comp]; rw [comp_apply]; rw [aeval]; rw [map_zero]

中文:
定理 aeval_algHom
  条件: (f : B ->ₐ[A] B') (x : B)
  结论: (多项式.aeval (f x)) (minpoly A x) = 0
  证明: by
  rw [Polynomial.aeval_algHom]; rw [AlgHom.coe_comp]; rw [comp_apply]; rw [aeval]; rw [map_zero]

Depends on / 依赖: AlgHom, AlgHom.coe_comp, Polynomial, Polynomial.aeval_algHom, aeval_algHom, coe_comp, comp_apply, map_zero
-/
theorem aeval_algHom (f : B ->ₐ[A] B') (x : B) : (Polynomial.aeval (f x)) (minpoly A x) = 0 := by
  rw [Polynomial.aeval_algHom]; rw [AlgHom.coe_comp]; rw [comp_apply]; rw [aeval]; rw [map_zero]

/--
theorem `ne_one` / 定理 `ne_one`

English:
theorem ne_one
  given: [Nontrivial B]
  statement: minpoly A x != 1
  proof: by
  intro h
  refine (one_ne_zero : (1 : B) != 0) ?_
  simpa using congr_arg (Polynomial.aeval x) h

中文:
定理 ne_one
  条件: [非平凡 B]
  结论: minpoly A x != 1
  证明: by
  intro h
  refine (one_ne_zero : (1 : B) != 0) ?_
  simpa using congr_arg (Polynomial.aeval x) h

Depends on / 依赖: Polynomial, Polynomial.aeval, congr_arg, one_ne_zero
-/
theorem ne_one [Nontrivial B] : minpoly A x != 1 := by
  intro h
  refine (one_ne_zero : (1 : B) != 0) ?_
  simpa using congr_arg (Polynomial.aeval x) h

/--
theorem `map_ne_one` / 定理 `map_ne_one`

English:
theorem map_ne_one
  given: [Nontrivial B] {R : Type*} [Semiring R] [Nontrivial R] (f : A ->+* R)
  proof: by
  by_cases hx : IsIntegral A x
  · exact mt ((monic hx).eq_one_of_map_eq_one f) (ne_one A x)
  · rw [eq_zero hx, Polynomial.map_zero]
    exact zero_ne_one

中文:
定理 map_ne_one
  条件: [非平凡 B] {R : 类型} [半环 R] [非平凡 R] (f : A ->+* R)
  证明: by
  by_cases hx : IsIntegral A x
  · exact mt ((monic hx).eq_one_of_map_eq_one f) (ne_one A x)
  · rw [eq_zero hx, Polynomial.map_zero]
    exact zero_ne_one

Depends on / 依赖: IsIntegral, Polynomial, Polynomial.map_zero, eq_one_of_map_eq_one, eq_zero, map_zero, ne_one, zero_ne_one
-/
theorem map_ne_one [Nontrivial B] {R : Type*} [Semiring R] [Nontrivial R] (f : A ->+* R) :
    (minpoly A x).map f != 1 := by
  by_cases hx : IsIntegral A x
  · exact mt ((monic hx).eq_one_of_map_eq_one f) (ne_one A x)
  · rw [eq_zero hx, Polynomial.map_zero]
    exact zero_ne_one

/--
theorem `not_isUnit` / 定理 `not_isUnit`

English:
theorem not_isUnit
  given: [Nontrivial B]
  statement: ¬IsUnit (minpoly A x)
  proof: by
  have : Nontrivial A := (algebraMap A B).domain_nontrivial
  by_cases hx : IsIntegral A x
  · exact mt (monic hx).eq_one_of_isUnit (ne_one A x)
  · rw [eq_zero hx]
    exact not_isUnit_zero

中文:
定理 not_isUnit
  条件: [非平凡 B]
  结论: ¬是单位 (minpoly A x)
  证明: by
  have : Nontrivial A := (algebraMap A B).domain_nontrivial
  by_cases hx : IsIntegral A x
  · exact mt (monic hx).eq_one_of_isUnit (ne_one A x)
  · rw [eq_zero hx]
    exact not_isUnit_zero

Depends on / 依赖: IsIntegral, Nontrivial, algebraMap, domain_nontrivial, eq_one_of_isUnit, eq_zero, ne_one, not_isUnit_zero
-/
theorem not_isUnit [Nontrivial B] : ¬IsUnit (minpoly A x) := by
  have : Nontrivial A := (algebraMap A B).domain_nontrivial
  by_cases hx : IsIntegral A x
  · exact mt (monic hx).eq_one_of_isUnit (ne_one A x)
  · rw [eq_zero hx]
    exact not_isUnit_zero

/--
theorem `mem_range_of_degree_eq_one` / 定理 `mem_range_of_degree_eq_one`

English:
theorem mem_range_of_degree_eq_one
  given: (hx : (minpoly A x).degree = 1)
  proof: by
  have h : IsIntegral A x := by
    by_contra h
    rw [eq_zero h]; rw [degree_zero]; rw [← WithBot.coe_one] at hx
    exact ne_of_lt (show ⊥ < ↑1 from WithBot.bot_lt_coe 1) hx
  have key := minpoly.aeval A x
  rw [eq_X_add_C_of_degree_eq_one hx]; rw [(minpoly.monic h).leadingCoeff]; rw [C_1]; rw [one_mul]; rw [aeval_add]; rw [aeval_C]; rw [aeval_X]; rw [← eq_neg_iff_add_eq_zero]; rw [← map_neg] at key
  exact ⟨-(minpoly A x).coeff 0, key.symm⟩

中文:
定理 mem_range_of_degree_eq_one
  条件: (hx : (minpoly A x).degree = 1)
  证明: by
  have h : IsIntegral A x := by
    by_contra h
    rw [eq_zero h]; rw [degree_zero]; rw [← WithBot.coe_one] at hx
    exact ne_of_lt (show ⊥ < ↑1 from WithBot.bot_lt_coe 1) hx
  have key := minpoly.aeval A x
  rw [eq_X_add_C_of_degree_eq_one hx]; rw [(minpoly.monic h).leadingCoeff]; rw [C_1]; rw [one_mul]; rw [aeval_add]; rw [aeval_C]; rw [aeval_X]; rw [← eq_neg_iff_add_eq_zero]; rw [← map_neg] at key
  exact ⟨-(minpoly A x).coeff 0, key.symm⟩

Depends on / 依赖: IsIntegral, WithBot, WithBot.bot_lt_coe, WithBot.coe_one, aeval_C, aeval_X, aeval_add, bot_lt_coe, coe_one, degree_zero, eq_X_add_C_of_degree_eq_one, eq_neg_iff_add_eq_zero, eq_zero, key.symm, leadingCoeff, map_neg, minpoly, minpoly.aeval, minpoly.monic, ne_of_lt
-/
theorem mem_range_of_degree_eq_one (hx : (minpoly A x).degree = 1) :
    x in (algebraMap A B).range := by
  have h : IsIntegral A x := by
    by_contra h
    rw [eq_zero h]; rw [degree_zero]; rw [← WithBot.coe_one] at hx
    exact ne_of_lt (show ⊥ < ↑1 from WithBot.bot_lt_coe 1) hx
  have key := minpoly.aeval A x
  rw [eq_X_add_C_of_degree_eq_one hx]; rw [(minpoly.monic h).leadingCoeff]; rw [C_1]; rw [one_mul]; rw [aeval_add]; rw [aeval_C]; rw [aeval_X]; rw [← eq_neg_iff_add_eq_zero]; rw [← map_neg] at key
  exact ⟨-(minpoly A x).coeff 0, key.symm⟩

/--
theorem `min` / 定理 `min`

English:
theorem min
  given: {p : A[X]} (pmonic : p.Monic) (hp : Polynomial.aeval x p = 0)
  proof: by
  delta minpoly; split_ifs with hx
· refine le_of_not_gt degree_lt_wf.not_lt_min _ ?_
    exact ⟨pmonic, hp⟩
  · simp only [degree_zero, bot_le]

中文:
定理 最小值
  条件: {p : A[X]} (pmonic : p.Monic) (hp : 多项式.aeval x p = 0)
  证明: by
  delta minpoly; split_ifs with hx
· refine le_of_not_gt degree_lt_wf.not_lt_min _ ?_
    exact ⟨pmonic, hp⟩
  · simp only [degree_zero, bot_le]

Depends on / 依赖: bot_le, degree_lt_wf, degree_lt_wf.not_lt_min, degree_zero, le_of_not_gt, minpoly, not_lt_min, pmonic, split_ifs
-/
theorem min {p : A[X]} (pmonic : p.Monic) (hp : Polynomial.aeval x p = 0) :
    degree (minpoly A x) <= degree p := by
  delta minpoly; split_ifs with hx
· refine le_of_not_gt degree_lt_wf.not_lt_min _ ?_
    exact ⟨pmonic, hp⟩
  · simp only [degree_zero, bot_le]

/--
theorem `unique'` / 定理 `unique'`

English:
theorem unique'
  statement: {p : A[X]} (hm : p.Monic) (hp : Polynomial.aeval x p = 0)
  proof: by
  nontriviality A
  have hx : IsIntegral A x := ⟨p, hm, hp⟩
  obtain h | h := hl _ ((minpoly A x).degree_modByMonic_lt hm)
  swap
  · exact (h <| (aeval_modByMonic_eq_self_of_root hp).trans <| aeval A x).elim
  obtain ⟨r, hr⟩ := (modByMonic_eq_zero_iff_dvd hm).1 h
  rw [hr]
  have hlead := congr_arg leadingCoeff hr
  rw [mul_comm]; rw [leadingCoeff_mul_monic hm]; rw [(monic hx).leadingCoeff] at hlead
  have : natDegree r <= 0 := by
    have hr0 : r != 0 := by
      rintro rfl
      exact ne_zero hx (mul_zero p ▸ hr)
    apply_fun natDegree at hr
    rw [hm.natDegree_mul' hr0] at hr
    apply Nat.le_of_add_le_add_left
    rw [add_zero]
    exact hr.symm.trans_le (natDegree_le_natDegree <| min A x hm hp)
  rw [eq_C_of_natDegree_le_zero this]; rw [← Nat.eq_zero_of_le_zero this]; rw [← leadingCoeff]; rw [← hlead]; rw [C_1]; rw [mul_one]

中文:
定理 unique'
  结论: {p : A[X]} (hm : p.Monic) (hp : 多项式.aeval x p = 0)
  证明: by
  nontriviality A
  have hx : IsIntegral A x := ⟨p, hm, hp⟩
  obtain h | h := hl _ ((minpoly A x).degree_modByMonic_lt hm)
  swap
  · exact (h <| (aeval_modByMonic_eq_self_of_root hp).trans <| aeval A x).elim
  obtain ⟨r, hr⟩ := (modByMonic_eq_zero_iff_dvd hm).1 h
  rw [hr]
  have hlead := congr_arg leadingCoeff hr
  rw [mul_comm]; rw [leadingCoeff_mul_monic hm]; rw [(monic hx).leadingCoeff] at hlead
  have : natDegree r <= 0 := by
    have hr0 : r != 0 := by
      rintro rfl
      exact ne_zero hx (mul_zero p ▸ hr)
    apply_fun natDegree at hr
    rw [hm.natDegree_mul' hr0] at hr
    apply Nat.le_of_add_le_add_left
    rw [add_zero]
    exact hr.symm.trans_le (natDegree_le_natDegree <| min A x hm hp)
  rw [eq_C_of_natDegree_le_zero this]; rw [← Nat.eq_zero_of_le_zero this]; rw [← leadingCoeff]; rw [← hlead]; rw [C_1]; rw [mul_one]

Depends on / 依赖: IsIntegral, aeval_modByMonic_eq_self_of_root, apply_fun, congr_arg, degree_modByMonic_lt, leadingCoeff, leadingCoeff_mul_monic, minpoly, modByMonic_eq_zero_iff_dvd, mul_comm, mul_zero, natDegree, ne_zero, nontriviality
-/
theorem unique' {p : A[X]} (hm : p.Monic) (hp : Polynomial.aeval x p = 0)
    (hl : forall q : A[X], degree q < degree p -> q = 0 ∨ Polynomial.aeval x q != 0) :
    p = minpoly A x := by
  nontriviality A
  have hx : IsIntegral A x := ⟨p, hm, hp⟩
  obtain h | h := hl _ ((minpoly A x).degree_modByMonic_lt hm)
  swap
  · exact (h <| (aeval_modByMonic_eq_self_of_root hp).trans <| aeval A x).elim
  obtain ⟨r, hr⟩ := (modByMonic_eq_zero_iff_dvd hm).1 h
  rw [hr]
  have hlead := congr_arg leadingCoeff hr
  rw [mul_comm]; rw [leadingCoeff_mul_monic hm]; rw [(monic hx).leadingCoeff] at hlead
  have : natDegree r <= 0 := by
    have hr0 : r != 0 := by
      rintro rfl
      exact ne_zero hx (mul_zero p ▸ hr)
    apply_fun natDegree at hr
    rw [hm.natDegree_mul' hr0] at hr
    apply Nat.le_of_add_le_add_left
    rw [add_zero]
    exact hr.symm.trans_le (natDegree_le_natDegree <| min A x hm hp)
  rw [eq_C_of_natDegree_le_zero this]; rw [← Nat.eq_zero_of_le_zero this]; rw [← leadingCoeff]; rw [← hlead]; rw [C_1]; rw [mul_one]

open Polynomial in
/--
theorem `eq_of_linearIndependent` / 定理 `eq_of_linearIndependent`

English:
theorem eq_of_linearIndependent
  statement: {p : A[X]} (monic : p.Monic) (hp0 : p.aeval x = 0)
  proof: .symm unique' _ _ monic hp0 fun q lt => or_iff_not_imp_left.mpr fun ne hq => ne ext fun i => by
    rw [q.as_sum_range' _ ((natDegree_lt_iff_degree_lt ne).mpr (hpn ▸ lt))] at hq
    obtain lt | le := lt_or_ge i n
    · simpa using Fintype.linearIndependent_iff.mp ind (q.coeff ·)
        (by simpa [Finset.sum_range, Algebra.smul_def] using hq) ⟨i, lt⟩
    · exact coeff_eq_zero_of_degree_lt ((hpn ▸ lt).trans_le <| WithBot.coe_le_coe.mpr le)

@[nontriviality]

中文:
定理 eq_of_linearIndependent
  结论: {p : A[X]} (monic : p.Monic) (hp0 : p.aeval x = 0)
  证明: .symm unique' _ _ monic hp0 fun q lt => or_iff_not_imp_left.mpr fun ne hq => ne ext fun i => by
    rw [q.as_sum_range' _ ((natDegree_lt_iff_degree_lt ne).mpr (hpn ▸ lt))] at hq
    obtain lt | le := lt_or_ge i n
    · simpa using Fintype.linearIndependent_iff.mp ind (q.coeff ·)
        (by simpa [Finset.sum_range, Algebra.smul_def] using hq) ⟨i, lt⟩
    · exact coeff_eq_zero_of_degree_lt ((hpn ▸ lt).trans_le <| WithBot.coe_le_coe.mpr le)

@[nontriviality]

Depends on / 依赖: Algebra, Algebra.smul_def, Finset, Finset.sum_range, Fintype, Fintype.linearIndependent_iff.mp, WithBot, WithBot.coe_le_coe.mpr, as_sum_range, coe_le_coe, coeff_eq_zero_of_degree_lt, linearIndependent_iff, lt_or_ge, natDegree_lt_iff_degree_lt, or_iff_not_imp_left, or_iff_not_imp_left.mpr, q.as_sum_range, q.coeff, smul_def, sum_range
-/
theorem eq_of_linearIndependent {p : A[X]} (monic : p.Monic) (hp0 : p.aeval x = 0)
    (n : Nat) (hpn : p.degree = n) (ind : LinearIndependent A fun i : Fin n => x ^ i.val) :
    minpoly A x = p :=
.symm unique' _ _ monic hp0 fun q lt => or_iff_not_imp_left.mpr fun ne hq => ne ext fun i => by
    rw [q.as_sum_range' _ ((natDegree_lt_iff_degree_lt ne).mpr (hpn ▸ lt))] at hq
    obtain lt | le := lt_or_ge i n
    · simpa using Fintype.linearIndependent_iff.mp ind (q.coeff ·)
        (by simpa [Finset.sum_range, Algebra.smul_def] using hq) ⟨i, lt⟩
    · exact coeff_eq_zero_of_degree_lt ((hpn ▸ lt).trans_le <| WithBot.coe_le_coe.mpr le)

@[nontriviality]
/--
theorem `subsingleton` / 定理 `subsingleton`

English:
theorem subsingleton
  given: [Subsingleton B]
  statement: minpoly A x = 1
  proof: by
  nontriviality A
  have := minpoly.min A x monic_one (Subsingleton.elim _ _)
  rw [degree_one] at this
  rcases le_or_gt (minpoly A x).degree 0 with h | h
  · rwa [(monic ⟨1, monic_one, by simp [eq_iff_true_of_subsingleton]⟩ :
           (minpoly A x).Monic).degree_le_zero_iff_eq_one] at h
  · exact (this.not_gt h).elim

中文:
定理 subsingleton
  条件: [子单例 B]
  结论: minpoly A x = 1
  证明: by
  nontriviality A
  have := minpoly.min A x monic_one (Subsingleton.elim _ _)
  rw [degree_one] at this
  rcases le_or_gt (minpoly A x).degree 0 with h | h
  · rwa [(monic ⟨1, monic_one, by simp [eq_iff_true_of_subsingleton]⟩ :
           (minpoly A x).Monic).degree_le_zero_iff_eq_one] at h
  · exact (this.not_gt h).elim

Depends on / 依赖: Subsingleton, Subsingleton.elim, degree, degree_le_zero_iff_eq_one, degree_one, eq_iff_true_of_subsingleton, le_or_gt, minpoly, minpoly.min, monic_one, nontriviality, not_gt, this.not_gt
-/
theorem subsingleton [Subsingleton B] : minpoly A x = 1 := by
  nontriviality A
  have := minpoly.min A x monic_one (Subsingleton.elim _ _)
  rw [degree_one] at this
  rcases le_or_gt (minpoly A x).degree 0 with h | h
  · rwa [(monic ⟨1, monic_one, by simp [eq_iff_true_of_subsingleton]⟩ :
           (minpoly A x).Monic).degree_le_zero_iff_eq_one] at h
  · exact (this.not_gt h).elim

end

/--
theorem `natDegree_pos` / 定理 `natDegree_pos`

English:
theorem natDegree_pos
  given: [Nontrivial B] (hx : IsIntegral A x)
  statement: 0 < natDegree (minpoly A x)
  proof: by
  rw [pos_iff_ne_zero]
  intro ndeg_eq_zero
  have eq_one : minpoly A x = 1 := by
    rw [eq_C_of_natDegree_eq_zero ndeg_eq_zero]
    convert C_1 (R := A)
    simpa only [ndeg_eq_zero.symm] using! (monic hx).leadingCoeff
  simpa only [eq_one, map_one, one_ne_zero] using! aeval A x

中文:
定理 natDegree_pos
  条件: [非平凡 B] (hx : 是整 A x)
  结论: 0 < natDegree (minpoly A x)
  证明: by
  rw [pos_iff_ne_zero]
  intro ndeg_eq_zero
  have eq_one : minpoly A x = 1 := by
    rw [eq_C_of_natDegree_eq_zero ndeg_eq_zero]
    convert C_1 (R := A)
    simpa only [ndeg_eq_zero.symm] using! (monic hx).leadingCoeff
  simpa only [eq_one, map_one, one_ne_zero] using! aeval A x

Depends on / 依赖: convert, eq_C_of_natDegree_eq_zero, eq_one, leadingCoeff, map_one, minpoly, ndeg_eq_zero, ndeg_eq_zero.symm, one_ne_zero, pos_iff_ne_zero
-/
theorem natDegree_pos [Nontrivial B] (hx : IsIntegral A x) : 0 < natDegree (minpoly A x) := by
  rw [pos_iff_ne_zero]
  intro ndeg_eq_zero
  have eq_one : minpoly A x = 1 := by
    rw [eq_C_of_natDegree_eq_zero ndeg_eq_zero]
    convert C_1 (R := A)
    simpa only [ndeg_eq_zero.symm] using! (monic hx).leadingCoeff
  simpa only [eq_one, map_one, one_ne_zero] using! aeval A x

/--
theorem `degree_pos` / 定理 `degree_pos`

English:
theorem degree_pos
  given: [Nontrivial B] (hx : IsIntegral A x)
  statement: 0 < degree (minpoly A x)
  proof: natDegree_pos_iff_degree_pos.mp (natDegree_pos hx)

@[simp]

中文:
定理 degree_pos
  条件: [非平凡 B] (hx : 是整 A x)
  结论: 0 < degree (minpoly A x)
  证明: natDegree_pos_iff_degree_pos.mp (natDegree_pos hx)

@[simp]

Depends on / 依赖: natDegree_pos, natDegree_pos_iff_degree_pos, natDegree_pos_iff_degree_pos.mp
-/
theorem degree_pos [Nontrivial B] (hx : IsIntegral A x) : 0 < degree (minpoly A x) :=
  natDegree_pos_iff_degree_pos.mp (natDegree_pos hx)

@[simp]
/--
theorem `aeval_modByMonic_minpoly` / 定理 `aeval_modByMonic_minpoly`

English:
theorem aeval_modByMonic_minpoly
  given: (p : A[X]) (x : B)
  statement: (p %ₘ minpoly A x).aeval x = p.aeval x
  proof: aeval_modByMonic_eq_self_of_root (minpoly.aeval ..)

中文:
定理 aeval_modByMonic_minpoly
  条件: (p : A[X]) (x : B)
  结论: (p %ₘ minpoly A x).aeval x = p.aeval x
  证明: aeval_modByMonic_eq_self_of_root (minpoly.aeval ..)

Depends on / 依赖: aeval_modByMonic_eq_self_of_root, minpoly, minpoly.aeval
-/
theorem aeval_modByMonic_minpoly (p : A[X]) (x : B) : (p %ₘ minpoly A x).aeval x = p.aeval x :=
  aeval_modByMonic_eq_self_of_root (minpoly.aeval ..)

section
variable [Nontrivial B]

open Polynomial in
/--
theorem `degree_eq_one_iff` / 定理 `degree_eq_one_iff`

English:
theorem degree_eq_one_iff
  statement: (minpoly A x).degree = 1 ↔ x in (algebraMap A B).range
  proof: by
  refine ⟨minpoly.mem_range_of_degree_eq_one _ _, ?_⟩
  rintro ⟨x, rfl⟩
  have := Module.nontrivial A B
  exact (degree_X_sub_C x ▸ minpoly.min A (algebraMap A B x) (monic_X_sub_C x) (by simp)).antisymm
    (Nat.WithBot.add_one_le_of_lt <| minpoly.degree_pos isIntegral_algebraMap)

中文:
定理 degree_eq_one_iff
  结论: (minpoly A x).degree = 1 ↔ x in (algebraMap A B).range
  证明: by
  refine ⟨minpoly.mem_range_of_degree_eq_one _ _, ?_⟩
  rintro ⟨x, rfl⟩
  have := Module.nontrivial A B
  exact (degree_X_sub_C x ▸ minpoly.min A (algebraMap A B x) (monic_X_sub_C x) (by simp)).antisymm
    (Nat.WithBot.add_one_le_of_lt <| minpoly.degree_pos isIntegral_algebraMap)

Depends on / 依赖: Module, Module.nontrivial, Nat.WithBot.add_one_le_of_lt, WithBot, add_one_le_of_lt, algebraMap, antisymm, degree_X_sub_C, degree_pos, isIntegral_algebraMap, mem_range_of_degree_eq_one, minpoly, minpoly.degree_pos, minpoly.mem_range_of_degree_eq_one, minpoly.min, monic_X_sub_C, nontrivial
-/
theorem degree_eq_one_iff : (minpoly A x).degree = 1 ↔ x in (algebraMap A B).range := by
  refine ⟨minpoly.mem_range_of_degree_eq_one _ _, ?_⟩
  rintro ⟨x, rfl⟩
  have := Module.nontrivial A B
  exact (degree_X_sub_C x ▸ minpoly.min A (algebraMap A B x) (monic_X_sub_C x) (by simp)).antisymm
    (Nat.WithBot.add_one_le_of_lt <| minpoly.degree_pos isIntegral_algebraMap)

/--
theorem `natDegree_eq_one_iff` / 定理 `natDegree_eq_one_iff`

English:
theorem natDegree_eq_one_iff
  proof: by
  rw [← Polynomial.degree_eq_iff_natDegree_eq_of_pos zero_lt_one]
  exact degree_eq_one_iff

中文:
定理 natDegree_eq_one_iff
  证明: by
  rw [← Polynomial.degree_eq_iff_natDegree_eq_of_pos zero_lt_one]
  exact degree_eq_one_iff

Depends on / 依赖: Polynomial, Polynomial.degree_eq_iff_natDegree_eq_of_pos, degree_eq_iff_natDegree_eq_of_pos, degree_eq_one_iff, zero_lt_one
-/
theorem natDegree_eq_one_iff :
    (minpoly A x).natDegree = 1 ↔ x in (algebraMap A B).range := by
  rw [← Polynomial.degree_eq_iff_natDegree_eq_of_pos zero_lt_one]
  exact degree_eq_one_iff

/--
theorem `two_le_natDegree_iff` / 定理 `two_le_natDegree_iff`

English:
theorem two_le_natDegree_iff
  given: (int : IsIntegral A x)
  proof: by
  rw [iff_not_comm]; rw [← natDegree_eq_one_iff]; rw [not_le]
  exact ⟨fun h => h.trans_lt one_lt_two, fun h => by linarith only [minpoly.natDegree_pos int, h]⟩

中文:
定理 two_le_natDegree_iff
  条件: (int : 是整 A x)
  证明: by
  rw [iff_not_comm]; rw [← natDegree_eq_one_iff]; rw [not_le]
  exact ⟨fun h => h.trans_lt one_lt_two, fun h => by linarith only [minpoly.natDegree_pos int, h]⟩

Depends on / 依赖: h.trans_lt, iff_not_comm, minpoly, minpoly.natDegree_pos, natDegree_eq_one_iff, natDegree_pos, not_le, one_lt_two, trans_lt
-/
theorem two_le_natDegree_iff (int : IsIntegral A x) :
    2 <= (minpoly A x).natDegree ↔ x ∉ (algebraMap A B).range := by
  rw [iff_not_comm]; rw [← natDegree_eq_one_iff]; rw [not_le]
  exact ⟨fun h => h.trans_lt one_lt_two, fun h => by linarith only [minpoly.natDegree_pos int, h]⟩

/--
theorem `two_le_natDegree_subalgebra` / 定理 `two_le_natDegree_subalgebra`

English:
theorem two_le_natDegree_subalgebra
  statement: {B} [CommRing B] [Algebra A B] [Nontrivial B]
  proof: by
  rw [two_le_natDegree_iff int]; rw [Iff.not]
  apply Set.ext_iff.mp Subtype.range_val_subtype

中文:
定理 two_le_natDegree_subalgebra
  结论: {B} [交换环 B] [代数 A B] [非平凡 B]
  证明: by
  rw [two_le_natDegree_iff int]; rw [Iff.not]
  apply Set.ext_iff.mp Subtype.range_val_subtype

Depends on / 依赖: Iff.not, Set.ext_iff.mp, Subtype, Subtype.range_val_subtype, ext_iff, range_val_subtype, two_le_natDegree_iff
-/
theorem two_le_natDegree_subalgebra {B} [CommRing B] [Algebra A B] [Nontrivial B]
    {S : Subalgebra A B} {x : B} (int : IsIntegral S x) : 2 <= (minpoly S x).natDegree ↔ x ∉ S := by
  rw [two_le_natDegree_iff int]; rw [Iff.not]
  apply Set.ext_iff.mp Subtype.range_val_subtype

end

/--
theorem `eq_X_sub_C_of_algebraMap_inj` / 定理 `eq_X_sub_C_of_algebraMap_inj`

English:
theorem eq_X_sub_C_of_algebraMap_inj
  given: (a : A) (hf : Function.Injective (algebraMap A B))
  proof: by
  nontriviality A
  refine (unique' A _ (monic_X_sub_C a) ?_ ?_).symm
  · rw [map_sub, aeval_C, aeval_X, sub_self]
  simp_rw [or_iff_not_imp_left]
  intro q hl h0
  rw [← natDegree_lt_natDegree_iff h0]; rw [natDegree_X_sub_C]; rw [Nat.lt_one_iff] at hl
  rw [eq_C_of_natDegree_eq_zero hl] at h0 ⊢
  rwa [aeval_C, map_ne_zero_iff _ hf, ← C_ne_zero]

中文:
定理 eq_X_sub_C_of_algebraMap_inj
  条件: (a : A) (hf : 函数.单射 (algebraMap A B))
  证明: by
  nontriviality A
  refine (unique' A _ (monic_X_sub_C a) ?_ ?_).symm
  · rw [map_sub, aeval_C, aeval_X, sub_self]
  simp_rw [or_iff_not_imp_left]
  intro q hl h0
  rw [← natDegree_lt_natDegree_iff h0]; rw [natDegree_X_sub_C]; rw [Nat.lt_one_iff] at hl
  rw [eq_C_of_natDegree_eq_zero hl] at h0 ⊢
  rwa [aeval_C, map_ne_zero_iff _ hf, ← C_ne_zero]

Depends on / 依赖: C_ne_zero, Nat.lt_one_iff, aeval_C, aeval_X, eq_C_of_natDegree_eq_zero, lt_one_iff, map_ne_zero_iff, map_sub, monic_X_sub_C, natDegree_X_sub_C, natDegree_lt_natDegree_iff, nontriviality, or_iff_not_imp_left, simp_rw, sub_self, unique
-/
theorem eq_X_sub_C_of_algebraMap_inj (a : A) (hf : Function.Injective (algebraMap A B)) :
    minpoly A (algebraMap A B a) = X - C a := by
  nontriviality A
  refine (unique' A _ (monic_X_sub_C a) ?_ ?_).symm
  · rw [map_sub, aeval_C, aeval_X, sub_self]
  simp_rw [or_iff_not_imp_left]
  intro q hl h0
  rw [← natDegree_lt_natDegree_iff h0]; rw [natDegree_X_sub_C]; rw [Nat.lt_one_iff] at hl
  rw [eq_C_of_natDegree_eq_zero hl] at h0 ⊢
  rwa [aeval_C, map_ne_zero_iff _ hf, ← C_ne_zero]

/--
theorem `aeval_ne_zero_of_dvdNotUnit_minpoly` / 定理 `aeval_ne_zero_of_dvdNotUnit_minpoly`

English:
theorem aeval_ne_zero_of_dvdNotUnit_minpoly
  statement: {a : A[X]} (hx : IsIntegral A x) (hamonic : a.Monic)
  proof: by
  refine fun ha => (min A x hamonic ha).not_gt (degree_lt_degree ?_)
  obtain ⟨_, c, hu, he⟩ := hdvd
  have hcm := hamonic.of_mul_monic_left (he.subst <| monic hx)
  rw [he]; rw [hamonic.natDegree_mul hcm]
  -- TODO: port Nat.lt_add_of_zero_lt_left from lean3 core
  apply lt_add_of_pos_right
  refine (lt_of_not_ge fun h => hu ?_)
  rw [eq_C_of_natDegree_le_zero h]; rw [← Nat.eq_zero_of_le_zero h]; rw [← leadingCoeff]; rw [hcm.leadingCoeff]; rw [C_1]
  exact isUnit_one

中文:
定理 aeval_ne_zero_of_dvdNotUnit_minpoly
  结论: {a : A[X]} (hx : 是整 A x) (hamonic : a.Monic)
  证明: by
  refine fun ha => (min A x hamonic ha).not_gt (degree_lt_degree ?_)
  obtain ⟨_, c, hu, he⟩ := hdvd
  have hcm := hamonic.of_mul_monic_left (he.subst <| monic hx)
  rw [he]; rw [hamonic.natDegree_mul hcm]
  -- TODO: port Nat.lt_add_of_zero_lt_left from lean3 core
  apply lt_add_of_pos_right
  refine (lt_of_not_ge fun h => hu ?_)
  rw [eq_C_of_natDegree_le_zero h]; rw [← Nat.eq_zero_of_le_zero h]; rw [← leadingCoeff]; rw [hcm.leadingCoeff]; rw [C_1]
  exact isUnit_one

Depends on / 依赖: degree_lt_degree, hamonic, hamonic.natDegree_mul, hamonic.of_mul_monic_left, he.subst, natDegree_mul, not_gt, of_mul_monic_left
-/
theorem aeval_ne_zero_of_dvdNotUnit_minpoly {a : A[X]} (hx : IsIntegral A x) (hamonic : a.Monic)
    (hdvd : DvdNotUnit a (minpoly A x)) : Polynomial.aeval x a != 0 := by
  refine fun ha => (min A x hamonic ha).not_gt (degree_lt_degree ?_)
  obtain ⟨_, c, hu, he⟩ := hdvd
  have hcm := hamonic.of_mul_monic_left (he.subst <| monic hx)
  rw [he]; rw [hamonic.natDegree_mul hcm]
  -- TODO: port Nat.lt_add_of_zero_lt_left from lean3 core
  apply lt_add_of_pos_right
  refine (lt_of_not_ge fun h => hu ?_)
  rw [eq_C_of_natDegree_le_zero h]; rw [← Nat.eq_zero_of_le_zero h]; rw [← leadingCoeff]; rw [hcm.leadingCoeff]; rw [C_1]
  exact isUnit_one

section IsDomain

variable [IsDomain A] [IsDomain B]

/--
theorem `irreducible` / 定理 `irreducible`

English:
theorem irreducible
  given: (hx : IsIntegral A x)
  statement: Irreducible (minpoly A x)
  proof: by
  refine (irreducible_of_monic (monic hx) <| ne_one A x).2 fun f g hf hg he => ?_
  rw [← hf.isUnit_iff]; rw [← hg.isUnit_iff]
  by_contra! h
  have heval := congr_arg (Polynomial.aeval x) he
  rw [aeval A x]; rw [aeval_mul]; rw [mul_eq_zero] at heval
  rcases heval with heval | heval
  · exact aeval_ne_zero_of_dvdNotUnit_minpoly hx hf ⟨hf.ne_zero, g, h.2, he.symm⟩ heval
  · refine aeval_ne_zero_of_dvdNotUnit_minpoly hx hg ⟨hg.ne_zero, f, h.1, ?_⟩ heval
    rw [mul_comm]; rw [he]

中文:
定理 irreducible
  条件: (hx : 是整 A x)
  结论: 不可约 (minpoly A x)
  证明: by
  refine (irreducible_of_monic (monic hx) <| ne_one A x).2 fun f g hf hg he => ?_
  rw [← hf.isUnit_iff]; rw [← hg.isUnit_iff]
  by_contra! h
  have heval := congr_arg (Polynomial.aeval x) he
  rw [aeval A x]; rw [aeval_mul]; rw [mul_eq_zero] at heval
  rcases heval with heval | heval
  · exact aeval_ne_zero_of_dvdNotUnit_minpoly hx hf ⟨hf.ne_zero, g, h.2, he.symm⟩ heval
  · refine aeval_ne_zero_of_dvdNotUnit_minpoly hx hg ⟨hg.ne_zero, f, h.1, ?_⟩ heval
    rw [mul_comm]; rw [he]

Depends on / 依赖: Polynomial, Polynomial.aeval, aeval_mul, aeval_ne_zero_of_dvdNotUnit_minpoly, congr_arg, he.symm, hf.isUnit_iff, hf.ne_zero, hg.isUnit_iff, hg.ne_zero, irreducible_of_monic, isUnit_iff, mul_comm, mul_eq_zero, ne_one, ne_zero
-/
theorem irreducible (hx : IsIntegral A x) : Irreducible (minpoly A x) := by
  refine (irreducible_of_monic (monic hx) <| ne_one A x).2 fun f g hf hg he => ?_
  rw [← hf.isUnit_iff]; rw [← hg.isUnit_iff]
  by_contra! h
  have heval := congr_arg (Polynomial.aeval x) he
  rw [aeval A x]; rw [aeval_mul]; rw [mul_eq_zero] at heval
  rcases heval with heval | heval
  · exact aeval_ne_zero_of_dvdNotUnit_minpoly hx hf ⟨hf.ne_zero, g, h.2, he.symm⟩ heval
  · refine aeval_ne_zero_of_dvdNotUnit_minpoly hx hg ⟨hg.ne_zero, f, h.1, ?_⟩ heval
    rw [mul_comm]; rw [he]

end IsDomain

end CommRing

end minpoly
