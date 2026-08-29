/-
Copyright (c) 2020 Riccardo Brasca. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Riccardo Brasca
-/
module

public import Mathlib.RingTheory.Polynomial.Cyclotomic.Basic
public import Mathlib.RingTheory.RootsOfUnity.Minpoly

/-!
# Roots of cyclotomic polynomials.

We gather results about roots of cyclotomic polynomials. In particular we show in
`Polynomial.cyclotomic_eq_minpoly` that `cyclotomic n R` is the minimal polynomial of a primitive
root of unity.

## Main results

* `IsPrimitiveRoot.isRoot_cyclotomic` : Any `n`-th primitive root of unity is a root of
  `cyclotomic n R`.
* `isRoot_cyclotomic_iff` : if `NeZero (n : R)`, then `μ` is a root of `cyclotomic n R`
  if and only if `μ` is a primitive root of unity.
* `Polynomial.cyclotomic_eq_minpoly` : `cyclotomic n ℤ` is the minimal polynomial of a primitive
  `n`-th root of unity `μ`.
* `Polynomial.cyclotomic.irreducible` : `cyclotomic n ℤ` is irreducible.

## Implementation details

To prove `Polynomial.cyclotomic.irreducible`, the irreducibility of `cyclotomic n ℤ`, we show in
`Polynomial.cyclotomic_eq_minpoly` that `cyclotomic n ℤ` is the minimal polynomial of any `n`-th
primitive root of unity `μ : K`, where `K` is a field of characteristic `0`.
-/

public section


namespace Polynomial

variable {R : Type*} [CommRing R] {n : Nat}

/--
theorem `isRoot_of_unity_of_root_cyclotomic` / 定理 `isRoot_of_unity_of_root_cyclotomic`

English:
theorem isRoot_of_unity_of_root_cyclotomic
  statement: {ζ : R} {i : Nat} (hi : i in n.divisors)
  proof: by
  rcases n.eq_zero_or_pos with (rfl | hn)
  · exact pow_zero _
  have := congr_arg (eval ζ) (prod_cyclotomic_eq_X_pow_sub_one hn R).symm
  rw [eval_sub]; rw [eval_X_pow]; rw [eval_one] at this
  convert! eq_add_of_sub_eq' this
  convert! (add_zero (M := R) _).symm
  apply eval_eq_zero_of_dvd_of_e

中文:
定理 isRoot_of_unity_of_root_cyclotomic
  结论: {ζ : R} {i : 自然数} (hi : i in n.divisors)
  证明: by
  rcases n.eq_zero_or_pos with (rfl | hn)
  · exact pow_zero _
  have := congr_arg (eval ζ) (prod_cyclotomic_eq_X_pow_sub_one hn R).symm
  rw [eval_sub]; rw [eval_X_pow]; rw [eval_one] at this
  convert! eq_add_of_sub_eq' this
  convert! (add_zero (M := R) _).symm
  apply eval_eq_zero_of_dvd_of_e

Depends on / 依赖: Finset, Finset.dvd_prod_of_mem, add_zero, congr_arg, convert, dvd_prod_of_mem, eq_add_of_sub_eq, eq_zero_or_pos, eval_X_pow, eval_eq_zero_of_dvd_of_eval_eq_zero, eval_one, eval_sub, n.eq_zero_or_pos, pow_zero, prod_cyclotomic_eq_X_pow_sub_one
-/
theorem isRoot_of_unity_of_root_cyclotomic {ζ : R} {i : Nat} (hi : i in n.divisors)
    (h : (cyclotomic i R).IsRoot ζ) : ζ ^ n = 1 := by
  rcases n.eq_zero_or_pos with (rfl | hn)
  · exact pow_zero _
  have := congr_arg (eval ζ) (prod_cyclotomic_eq_X_pow_sub_one hn R).symm
  rw [eval_sub]; rw [eval_X_pow]; rw [eval_one] at this
  convert! eq_add_of_sub_eq' this
  convert! (add_zero (M := R) _).symm
  apply eval_eq_zero_of_dvd_of_eval_eq_zero _ h
  exact Finset.dvd_prod_of_mem _ hi

section IsDomain

variable [IsDomain R]

/--
theorem `_root_.isRoot_of_unity_iff` / 定理 `_root_.isRoot_of_unity_iff`

English:
theorem _root_.isRoot_of_unity_iff
  given: (h : 0 < n) (R : Type*) [CommRing R] [IsDomain R] {ζ : R}
  proof: by
  rw [← mem_nthRoots h]; rw [nthRoots]; rw [mem_roots <| X_pow_sub_C_ne_zero h _]; rw [C_1]; rw [←
      prod_cyclotomic_eq_X_pow_sub_one h]; rw [isRoot_prod]

中文:
定理 _root_.isRoot_of_unity_iff
  条件: (h : 0 < n) (R : 类型) [交换环 R] [是整环 R] {ζ : R}
  证明: by
  rw [← mem_nthRoots h]; rw [nthRoots]; rw [mem_roots <| X_pow_sub_C_ne_zero h _]; rw [C_1]; rw [←
      prod_cyclotomic_eq_X_pow_sub_one h]; rw [isRoot_prod]

Depends on / 依赖: X_pow_sub_C_ne_zero, isRoot_prod, mem_nthRoots, mem_roots, nthRoots, prod_cyclotomic_eq_X_pow_sub_one
-/
theorem _root_.isRoot_of_unity_iff (h : 0 < n) (R : Type*) [CommRing R] [IsDomain R] {ζ : R} :
    ζ ^ n = 1 ↔ exists i in n.divisors, (cyclotomic i R).IsRoot ζ := by
  rw [← mem_nthRoots h]; rw [nthRoots]; rw [mem_roots <| X_pow_sub_C_ne_zero h _]; rw [C_1]; rw [←
      prod_cyclotomic_eq_X_pow_sub_one h]; rw [isRoot_prod]

/--
theorem `_root_.IsPrimitiveRoot.isRoot_cyclotomic` / 定理 `_root_.IsPrimitiveRoot.isRoot_cyclotomic`

English:
theorem _root_.IsPrimitiveRoot.isRoot_cyclotomic
  given: (hpos : 0 < n) {μ : R} (h : IsPrimitiveRoot μ n)
  proof: by
  rw [← mem_roots (cyclotomic_ne_zero n R)]; rw [cyclotomic_eq_prod_X_sub_primitiveRoots h]; rw [roots_prod_X_sub_C]; rw [← Finset.mem_def]
  rwa [← mem_primitiveRoots hpos] at h

中文:
定理 _root_.是PrimitiveRoot.isRoot_cyclotomic
  条件: (hpos : 0 < n) {μ : R} (h : 是PrimitiveRoot μ n)
  证明: by
  rw [← mem_roots (cyclotomic_ne_zero n R)]; rw [cyclotomic_eq_prod_X_sub_primitiveRoots h]; rw [roots_prod_X_sub_C]; rw [← Finset.mem_def]
  rwa [← mem_primitiveRoots hpos] at h

Depends on / 依赖: Finset, Finset.mem_def, cyclotomic_eq_prod_X_sub_primitiveRoots, cyclotomic_ne_zero, mem_def, mem_primitiveRoots, mem_roots, roots_prod_X_sub_C
-/
theorem _root_.IsPrimitiveRoot.isRoot_cyclotomic (hpos : 0 < n) {μ : R} (h : IsPrimitiveRoot μ n) :
    IsRoot (cyclotomic n R) μ := by
  rw [← mem_roots (cyclotomic_ne_zero n R)]; rw [cyclotomic_eq_prod_X_sub_primitiveRoots h]; rw [roots_prod_X_sub_C]; rw [← Finset.mem_def]
  rwa [← mem_primitiveRoots hpos] at h

/--
theorem `isRoot_cyclotomic_iff'` / 定理 `isRoot_cyclotomic_iff'`

English:
theorem isRoot_cyclotomic_iff'
  given: {n : Nat} {K : Type*} [Field K] {μ : K} [NeZero (n : K)]
  proof: by
  -- in this proof, `o` stands for `orderOf μ`
  have hnpos : 0 < n := (NeZero.of_neZero_natCast K).out.bot_lt
  refine ⟨fun hμ => ?_, IsPrimitiveRoot.isRoot_cyclotomic hnpos⟩
  have hμn : μ ^ n = 1 := by
    rw [isRoot_of_unity_iff hnpos _]
    exact ⟨n, n.mem_divisors_self hnpos.ne', hμ⟩
  by_c

中文:
定理 isRoot_cyclotomic_iff'
  条件: {n : 自然数} {K : 类型} [域 K] {μ : K} [NeZero (n : K)]
  证明: by
  -- in this proof, `o` stands for `orderOf μ`
  have hnpos : 0 < n := (NeZero.of_neZero_natCast K).out.bot_lt
  refine ⟨fun hμ => ?_, IsPrimitiveRoot.isRoot_cyclotomic hnpos⟩
  have hμn : μ ^ n = 1 := by
    rw [isRoot_of_unity_iff hnpos _]
    exact ⟨n, n.mem_divisors_self hnpos.ne', hμ⟩
  by_c
-/
private theorem isRoot_cyclotomic_iff' {n : Nat} {K : Type*} [Field K] {μ : K} [NeZero (n : K)] :
    IsRoot (cyclotomic n K) μ ↔ IsPrimitiveRoot μ n := by
  -- in this proof, `o` stands for `orderOf μ`
  have hnpos : 0 < n := (NeZero.of_neZero_natCast K).out.bot_lt
  refine ⟨fun hμ => ?_, IsPrimitiveRoot.isRoot_cyclotomic hnpos⟩
  have hμn : μ ^ n = 1 := by
    rw [isRoot_of_unity_iff hnpos _]
    exact ⟨n, n.mem_divisors_self hnpos.ne', hμ⟩
  by_contra hnμ
  have ho : 0 < orderOf μ := (isOfFinOrder_iff_pow_eq_one.2 <| ⟨n, hnpos, hμn⟩).orderOf_pos
  have := pow_orderOf_eq_one μ
  rw [isRoot_of_unity_iff ho] at this
  obtain ⟨i, hio, hiμ⟩ := this
  replace hio := Nat.dvd_of_mem_divisors hio
  rw [IsPrimitiveRoot.not_iff] at hnμ
  rw [← orderOf_dvd_iff_pow_eq_one] at hμn
  have key : i < n := (Nat.le_of_dvd ho hio).trans_lt ((Nat.le_of_dvd hnpos hμn).lt_of_ne hnμ)
  have key' : i ∣ n := hio.trans hμn
  rw [← Polynomial.dvd_iff_isRoot] at hμ hiμ
  have hni : {i, n} subseteq n.divisors := by simpa [Finset.insert_subset_iff, key'] using hnpos.ne'
  obtain ⟨k, hk⟩ := hiμ
  obtain ⟨j, hj⟩ := hμ
  have := prod_cyclotomic_eq_X_pow_sub_one hnpos K
  rw [← Finset.prod_sdiff hni]; rw [Finset.prod_pair key.ne]; rw [hk]; rw [hj] at this
  have hn := (X_pow_sub_one_separable_iff.mpr <| NeZero.natCast_ne n K).squarefree
  rw [← this]; rw [Squarefree] at hn
  specialize hn (X - C μ) ⟨(∏ x in n.divisors \ {i, n}, cyclotomic x K) * k * j, by ring⟩
  simp [Polynomial.isUnit_iff_degree_eq_zero] at hn

/--
theorem `isRoot_cyclotomic_iff` / 定理 `isRoot_cyclotomic_iff`

English:
theorem isRoot_cyclotomic_iff
  given: [NeZero (n : R)] {μ : R}
  proof: by
  have hf : Function.Injective _ := IsFractionRing.injective R (FractionRing R)
  have : NeZero (n : FractionRing R) := NeZero.nat_of_injective hf
  rw [← isRoot_map_iff hf]; rw [← IsPrimitiveRoot.map_iff_of_injective hf]; rw [map_cyclotomic]; rw [←
    isRoot_cyclotomic_iff']

中文:
定理 isRoot_cyclotomic_iff
  条件: [NeZero (n : R)] {μ : R}
  证明: by
  have hf : Function.Injective _ := IsFractionRing.injective R (FractionRing R)
  have : NeZero (n : FractionRing R) := NeZero.nat_of_injective hf
  rw [← isRoot_map_iff hf]; rw [← IsPrimitiveRoot.map_iff_of_injective hf]; rw [map_cyclotomic]; rw [←
    isRoot_cyclotomic_iff']

Depends on / 依赖: FractionRing, Function, Function.Injective, Injective, IsFractionRing, IsFractionRing.injective, IsPrimitiveRoot, IsPrimitiveRoot.map_iff_of_injective, NeZero, NeZero.nat_of_injective, injective, isRoot_cyclotomic_iff, isRoot_map_iff, map_cyclotomic, map_iff_of_injective, nat_of_injective
-/
theorem isRoot_cyclotomic_iff [NeZero (n : R)] {μ : R} :
    IsRoot (cyclotomic n R) μ ↔ IsPrimitiveRoot μ n := by
  have hf : Function.Injective _ := IsFractionRing.injective R (FractionRing R)
  have : NeZero (n : FractionRing R) := NeZero.nat_of_injective hf
  rw [← isRoot_map_iff hf]; rw [← IsPrimitiveRoot.map_iff_of_injective hf]; rw [map_cyclotomic]; rw [←
    isRoot_cyclotomic_iff']

/--
theorem `roots_cyclotomic_nodup` / 定理 `roots_cyclotomic_nodup`

English:
theorem roots_cyclotomic_nodup
  given: [NeZero (n : R)]
  statement: (cyclotomic n R).roots.Nodup
  proof: by
  obtain h | ⟨ζ, hζ⟩ := (cyclotomic n R).roots.empty_or_exists_mem
  · exact h.symm ▸ Multiset.nodup_zero
  rw [mem_roots <| cyclotomic_ne_zero n R]; rw [isRoot_cyclotomic_iff] at hζ
  refine Multiset.nodup_of_le
    (roots.le_of_dvd (X_pow_sub_C_ne_zero (NeZero.pos_of_neZero_natCast R) 1) <|
   

中文:
定理 roots_cyclotomic_nodup
  条件: [NeZero (n : R)]
  结论: (cyclotomic n R).roots.Nodup
  证明: by
  obtain h | ⟨ζ, hζ⟩ := (cyclotomic n R).roots.empty_or_exists_mem
  · exact h.symm ▸ Multiset.nodup_zero
  rw [mem_roots <| cyclotomic_ne_zero n R]; rw [isRoot_cyclotomic_iff] at hζ
  refine Multiset.nodup_of_le
    (roots.le_of_dvd (X_pow_sub_C_ne_zero (NeZero.pos_of_neZero_natCast R) 1) <|
   

Depends on / 依赖: Multiset, Multiset.nodup_of_le, Multiset.nodup_zero, NeZero, NeZero.pos_of_neZero_natCast, X_pow_sub_C_ne_zero, cyclotomic, cyclotomic.dvd_X_pow_sub_one, cyclotomic_ne_zero, dvd_X_pow_sub_one, empty_or_exists_mem, h.symm, isRoot_cyclotomic_iff, le_of_dvd, mem_roots, nodup_of_le, nodup_zero, nthRoots_one_nodup, pos_of_neZero_natCast, roots.empty_or_exists_mem
-/
theorem roots_cyclotomic_nodup [NeZero (n : R)] : (cyclotomic n R).roots.Nodup := by
  obtain h | ⟨ζ, hζ⟩ := (cyclotomic n R).roots.empty_or_exists_mem
  · exact h.symm ▸ Multiset.nodup_zero
  rw [mem_roots <| cyclotomic_ne_zero n R]; rw [isRoot_cyclotomic_iff] at hζ
  refine Multiset.nodup_of_le
    (roots.le_of_dvd (X_pow_sub_C_ne_zero (NeZero.pos_of_neZero_natCast R) 1) <|
      cyclotomic.dvd_X_pow_sub_one n R) hζ.nthRoots_one_nodup

/--
theorem `cyclotomic.roots_to_finset_eq_primitiveRoots` / 定理 `cyclotomic.roots_to_finset_eq_primitiveRoots`

English:
theorem cyclotomic.roots_to_finset_eq_primitiveRoots
  given: [NeZero (n : R)]
  proof: by
  ext a
  simp [cyclotomic_ne_zero n R, ← isRoot_cyclotomic_iff, mem_primitiveRoots,
    NeZero.pos_of_neZero_natCast R]

中文:
定理 cyclotomic.roots_to_finset_eq_primitiveRoots
  条件: [NeZero (n : R)]
  证明: by
  ext a
  simp [cyclotomic_ne_zero n R, ← isRoot_cyclotomic_iff, mem_primitiveRoots,
    NeZero.pos_of_neZero_natCast R]

Depends on / 依赖: IsStrictOrderedRing, IsStrictOrderedRing.toIsTopologicalDivisionRing, NeZero, NeZero.pos_of_neZero_natCast, cyclotomic_ne_zero, isRoot_cyclotomic_iff, mem_primitiveRoots, pos_of_neZero_natCast, toIsTopologicalDivisionRing
-/
theorem cyclotomic.roots_to_finset_eq_primitiveRoots [NeZero (n : R)] :
    (⟨(cyclotomic n R).roots, roots_cyclotomic_nodup⟩ : Finset _) = primitiveRoots n R := by
  ext a
  simp [cyclotomic_ne_zero n R, ← isRoot_cyclotomic_iff, mem_primitiveRoots,
    NeZero.pos_of_neZero_natCast R]

/--
theorem `cyclotomic.roots_eq_primitiveRoots_val` / 定理 `cyclotomic.roots_eq_primitiveRoots_val`

English:
theorem cyclotomic.roots_eq_primitiveRoots_val
  given: [NeZero (n : R)]
  proof: by
  rw [← cyclotomic.roots_to_finset_eq_primitiveRoots]

中文:
定理 cyclotomic.roots_eq_primitiveRoots_val
  条件: [NeZero (n : R)]
  证明: by
  rw [← cyclotomic.roots_to_finset_eq_primitiveRoots]

Depends on / 依赖: cyclotomic, cyclotomic.roots_to_finset_eq_primitiveRoots, roots_to_finset_eq_primitiveRoots
-/
theorem cyclotomic.roots_eq_primitiveRoots_val [NeZero (n : R)] :
    (cyclotomic n R).roots = (primitiveRoots n R).val := by
  rw [← cyclotomic.roots_to_finset_eq_primitiveRoots]

/--
theorem `isRoot_cyclotomic_iff_charZero` / 定理 `isRoot_cyclotomic_iff_charZero`

English:
theorem isRoot_cyclotomic_iff_charZero
  statement: {n : Nat} {R : Type*} [CommRing R] [IsDomain R] [CharZero R]
  proof: letI := NeZero.of_gt hn
  isRoot_cyclotomic_iff

中文:
定理 isRoot_cyclotomic_iff_charZero
  结论: {n : 自然数} {R : 类型} [交换环 R] [是整环 R] [特征零 R]
  证明: letI := NeZero.of_gt hn
  isRoot_cyclotomic_iff

Depends on / 依赖: NeZero, NeZero.of_gt, isRoot_cyclotomic_iff, of_gt
-/
theorem isRoot_cyclotomic_iff_charZero {n : Nat} {R : Type*} [CommRing R] [IsDomain R] [CharZero R]
    {μ : R} (hn : 0 < n) : (Polynomial.cyclotomic n R).IsRoot μ ↔ IsPrimitiveRoot μ n :=
  letI := NeZero.of_gt hn
  isRoot_cyclotomic_iff

end IsDomain

/--
theorem `cyclotomic_injective` / 定理 `cyclotomic_injective`

English:
theorem cyclotomic_injective
  given: [CharZero R]
  statement: Function.Injective fun n => cyclotomic n R
  proof: by
  intro n m hnm
  simp only at hnm
  rcases eq_or_ne n 0 with (rfl | hzero)
  · rw [cyclotomic_zero] at hnm
    replace hnm := congr_arg natDegree hnm
    rwa [natDegree_one, natDegree_cyclotomic, eq_comm, Nat.totient_eq_zero, eq_comm] at hnm
  · have := NeZero.mk hzero
    rw [← map_cyclotomic_i

中文:
定理 cyclotomic_injective
  条件: [特征零 R]
  结论: 函数.单射 fun n => cyclotomic n R
  证明: by
  intro n m hnm
  simp only at hnm
  rcases eq_or_ne n 0 with (rfl | hzero)
  · rw [cyclotomic_zero] at hnm
    replace hnm := congr_arg natDegree hnm
    rwa [natDegree_one, natDegree_cyclotomic, eq_comm, Nat.totient_eq_zero, eq_comm] at hnm
  · have := NeZero.mk hzero
    rw [← map_cyclotomic_i

Depends on / 依赖: Int.castRingHom, Int.cast_injective, Nat.totient_eq_zero, NeZero, NeZero.mk, castRingHom, cast_injective, congr_arg, cyclotomic_zero, eq_comm, eq_or_ne, map_cyclotomic, map_cyclotomic_int, map_injective, natDegree, natDegree_cyclotomic, natDegree_one, replace, totient_eq_zero
-/
theorem cyclotomic_injective [CharZero R] : Function.Injective fun n => cyclotomic n R := by
  intro n m hnm
  simp only at hnm
  rcases eq_or_ne n 0 with (rfl | hzero)
  · rw [cyclotomic_zero] at hnm
    replace hnm := congr_arg natDegree hnm
    rwa [natDegree_one, natDegree_cyclotomic, eq_comm, Nat.totient_eq_zero, eq_comm] at hnm
  · have := NeZero.mk hzero
    rw [← map_cyclotomic_int _ R]; rw [← map_cyclotomic_int _ R] at hnm
    replace hnm := map_injective (Int.castRingHom R) Int.cast_injective hnm
    replace hnm := congr_arg (map (Int.castRingHom Complex)) hnm
    rw [map_cyclotomic_int]; rw [map_cyclotomic_int] at hnm
    have hprim := Complex.isPrimitiveRoot_exp _ hzero
    have hroot := isRoot_cyclotomic_iff (R := Complex).2 hprim
    rw [hnm] at hroot
    have hmzero : NeZero m := ⟨fun h => by simp [h] at hroot⟩
    rw [isRoot_cyclotomic_iff (R := Complex)] at hroot
    replace hprim := hprim.eq_orderOf
    rwa [← IsPrimitiveRoot.eq_orderOf hroot] at hprim

/--
theorem `_root_.IsPrimitiveRoot.minpoly_dvd_cyclotomic` / 定理 `_root_.IsPrimitiveRoot.minpoly_dvd_cyclotomic`

English:
theorem _root_.IsPrimitiveRoot.minpoly_dvd_cyclotomic
  statement: {n : Nat} {K : Type*} [Field K] {μ : K}
  proof: by
  apply minpoly.isIntegrallyClosed_dvd (h.isIntegral hpos)
  simpa [aeval_def, eval₂_eq_eval_map, IsRoot.def] using h.isRoot_cyclotomic hpos

中文:
定理 _root_.是PrimitiveRoot.minpoly_dvd_cyclotomic
  结论: {n : 自然数} {K : 类型} [域 K] {μ : K}
  证明: by
  apply minpoly.isIntegrallyClosed_dvd (h.isIntegral hpos)
  simpa [aeval_def, eval₂_eq_eval_map, IsRoot.def] using h.isRoot_cyclotomic hpos

Depends on / 依赖: IsRoot, IsRoot.def, aeval_def, h.isIntegral, h.isRoot_cyclotomic, isIntegral, isIntegrallyClosed_dvd, isRoot_cyclotomic, minpoly, minpoly.isIntegrallyClosed_dvd
-/
theorem _root_.IsPrimitiveRoot.minpoly_dvd_cyclotomic {n : Nat} {K : Type*} [Field K] {μ : K}
    (h : IsPrimitiveRoot μ n) (hpos : 0 < n) [CharZero K] : minpoly Int μ ∣ cyclotomic n Int := by
  apply minpoly.isIntegrallyClosed_dvd (h.isIntegral hpos)
  simpa [aeval_def, eval₂_eq_eval_map, IsRoot.def] using h.isRoot_cyclotomic hpos

section minpoly

open IsPrimitiveRoot Complex

/--
theorem `_root_.IsPrimitiveRoot.minpoly_eq_cyclotomic_of_irreducible` / 定理 `_root_.IsPrimitiveRoot.minpoly_eq_cyclotomic_of_irreducible`

English:
theorem _root_.IsPrimitiveRoot.minpoly_eq_cyclotomic_of_irreducible
  statement: {K : Type*} [Field K]
  proof: by
  have := NeZero.of_faithfulSMul K R n
  refine minpoly.eq_of_irreducible_of_monic h ?_ (cyclotomic.monic n K)
  rwa [aeval_def, eval₂_eq_eval_map, map_cyclotomic, ← IsRoot.def, isRoot_cyclotomic_iff]

中文:
定理 _root_.是PrimitiveRoot.minpoly_eq_cyclotomic_of_irreducible
  结论: {K : 类型} [域 K]
  证明: by
  have := NeZero.of_faithfulSMul K R n
  refine minpoly.eq_of_irreducible_of_monic h ?_ (cyclotomic.monic n K)
  rwa [aeval_def, eval₂_eq_eval_map, map_cyclotomic, ← IsRoot.def, isRoot_cyclotomic_iff]

Depends on / 依赖: IsRoot, IsRoot.def, NeZero, NeZero.of_faithfulSMul, aeval_def, cyclotomic, cyclotomic.monic, eq_of_irreducible_of_monic, isRoot_cyclotomic_iff, map_cyclotomic, minpoly, minpoly.eq_of_irreducible_of_monic, of_faithfulSMul
-/
theorem _root_.IsPrimitiveRoot.minpoly_eq_cyclotomic_of_irreducible {K : Type*} [Field K]
    {R : Type*} [CommRing R] [IsDomain R] {μ : R} {n : Nat} [Algebra K R] (hμ : IsPrimitiveRoot μ n)
    (h : Irreducible <| cyclotomic n K) [NeZero (n : K)] : cyclotomic n K = minpoly K μ := by
  have := NeZero.of_faithfulSMul K R n
  refine minpoly.eq_of_irreducible_of_monic h ?_ (cyclotomic.monic n K)
  rwa [aeval_def, eval₂_eq_eval_map, map_cyclotomic, ← IsRoot.def, isRoot_cyclotomic_iff]

/--
theorem `cyclotomic_eq_minpoly` / 定理 `cyclotomic_eq_minpoly`

English:
theorem cyclotomic_eq_minpoly
  statement: {n : Nat} {K : Type*} [Field K] {μ : K} (h : IsPrimitiveRoot μ n)
  proof: by
  refine eq_of_monic_of_dvd_of_natDegree_le (minpoly.monic (IsPrimitiveRoot.isIntegral h hpos))
    (cyclotomic.monic n Int) (h.minpoly_dvd_cyclotomic hpos) ?_
  simpa [natDegree_cyclotomic n Int] using totient_le_degree_minpoly h

中文:
定理 cyclotomic_eq_minpoly
  结论: {n : 自然数} {K : 类型} [域 K] {μ : K} (h : 是PrimitiveRoot μ n)
  证明: by
  refine eq_of_monic_of_dvd_of_natDegree_le (minpoly.monic (IsPrimitiveRoot.isIntegral h hpos))
    (cyclotomic.monic n Int) (h.minpoly_dvd_cyclotomic hpos) ?_
  simpa [natDegree_cyclotomic n Int] using totient_le_degree_minpoly h

Depends on / 依赖: IsPrimitiveRoot, IsPrimitiveRoot.isIntegral, cyclotomic, cyclotomic.monic, eq_of_monic_of_dvd_of_natDegree_le, h.minpoly_dvd_cyclotomic, isIntegral, minpoly, minpoly.monic, minpoly_dvd_cyclotomic, natDegree_cyclotomic, totient_le_degree_minpoly
-/
theorem cyclotomic_eq_minpoly {n : Nat} {K : Type*} [Field K] {μ : K} (h : IsPrimitiveRoot μ n)
    (hpos : 0 < n) [CharZero K] : cyclotomic n Int = minpoly Int μ := by
  refine eq_of_monic_of_dvd_of_natDegree_le (minpoly.monic (IsPrimitiveRoot.isIntegral h hpos))
    (cyclotomic.monic n Int) (h.minpoly_dvd_cyclotomic hpos) ?_
  simpa [natDegree_cyclotomic n Int] using totient_le_degree_minpoly h

/--
theorem `cyclotomic_eq_minpoly_rat` / 定理 `cyclotomic_eq_minpoly_rat`

English:
theorem cyclotomic_eq_minpoly_rat
  statement: {n : Nat} {K : Type*} [Field K] {μ : K} (h : IsPrimitiveRoot μ n)
  proof: by
  rw [← map_cyclotomic_int]; rw [cyclotomic_eq_minpoly h hpos]
  exact (minpoly.isIntegrallyClosed_eq_field_fractions' _ (IsPrimitiveRoot.isIntegral h hpos)).symm

中文:
定理 cyclotomic_eq_minpoly_rat
  结论: {n : 自然数} {K : 类型} [域 K] {μ : K} (h : 是PrimitiveRoot μ n)
  证明: by
  rw [← map_cyclotomic_int]; rw [cyclotomic_eq_minpoly h hpos]
  exact (minpoly.isIntegrallyClosed_eq_field_fractions' _ (IsPrimitiveRoot.isIntegral h hpos)).symm

Depends on / 依赖: IsPrimitiveRoot, IsPrimitiveRoot.isIntegral, cyclotomic_eq_minpoly, isIntegral, isIntegrallyClosed_eq_field_fractions, map_cyclotomic_int, minpoly, minpoly.isIntegrallyClosed_eq_field_fractions
-/
theorem cyclotomic_eq_minpoly_rat {n : Nat} {K : Type*} [Field K] {μ : K} (h : IsPrimitiveRoot μ n)
    (hpos : 0 < n) [CharZero K] : cyclotomic n Rat = minpoly Rat μ := by
  rw [← map_cyclotomic_int]; rw [cyclotomic_eq_minpoly h hpos]
  exact (minpoly.isIntegrallyClosed_eq_field_fractions' _ (IsPrimitiveRoot.isIntegral h hpos)).symm

/--
theorem `cyclotomic.irreducible` / 定理 `cyclotomic.irreducible`

English:
theorem cyclotomic.irreducible
  given: {n : Nat} (hpos : 0 < n)
  statement: Irreducible (cyclotomic n Int)
  proof: by
  rw [cyclotomic_eq_minpoly (isPrimitiveRoot_exp n hpos.ne') hpos]
  apply minpoly.irreducible
  exact (isPrimitiveRoot_exp n hpos.ne').isIntegral hpos

中文:
定理 cyclotomic.irreducible
  条件: {n : 自然数} (hpos : 0 < n)
  结论: 不可约 (cyclotomic n 整数)
  证明: by
  rw [cyclotomic_eq_minpoly (isPrimitiveRoot_exp n hpos.ne') hpos]
  apply minpoly.irreducible
  exact (isPrimitiveRoot_exp n hpos.ne').isIntegral hpos

Depends on / 依赖: cyclotomic_eq_minpoly, hpos.ne, irreducible, isIntegral, isPrimitiveRoot_exp, minpoly, minpoly.irreducible
-/
theorem cyclotomic.irreducible {n : Nat} (hpos : 0 < n) : Irreducible (cyclotomic n Int) := by
  rw [cyclotomic_eq_minpoly (isPrimitiveRoot_exp n hpos.ne') hpos]
  apply minpoly.irreducible
  exact (isPrimitiveRoot_exp n hpos.ne').isIntegral hpos

/--
theorem `cyclotomic.irreducible_rat` / 定理 `cyclotomic.irreducible_rat`

English:
theorem cyclotomic.irreducible_rat
  given: {n : Nat} (hpos : 0 < n)
  statement: Irreducible (cyclotomic n Rat)
  proof: by
  rw [← map_cyclotomic_int]
  exact (IsPrimitive.irreducible_iff_irreducible_map_fraction_map (cyclotomic.isPrimitive n Int)).1
    (cyclotomic.irreducible hpos)

中文:
定理 cyclotomic.irreducible_rat
  条件: {n : 自然数} (hpos : 0 < n)
  结论: 不可约 (cyclotomic n 有理数)
  证明: by
  rw [← map_cyclotomic_int]
  exact (IsPrimitive.irreducible_iff_irreducible_map_fraction_map (cyclotomic.isPrimitive n Int)).1
    (cyclotomic.irreducible hpos)

Depends on / 依赖: IsPrimitive, IsPrimitive.irreducible_iff_irreducible_map_fraction_map, cyclotomic, cyclotomic.irreducible, cyclotomic.isPrimitive, irreducible, irreducible_iff_irreducible_map_fraction_map, isPrimitive, map_cyclotomic_int
-/
theorem cyclotomic.irreducible_rat {n : Nat} (hpos : 0 < n) : Irreducible (cyclotomic n Rat) := by
  rw [← map_cyclotomic_int]
  exact (IsPrimitive.irreducible_iff_irreducible_map_fraction_map (cyclotomic.isPrimitive n Int)).1
    (cyclotomic.irreducible hpos)

/--
theorem `cyclotomic.isCoprime_rat` / 定理 `cyclotomic.isCoprime_rat`

English:
theorem cyclotomic.isCoprime_rat
  given: {n m : Nat} (h : n != m)
  proof: by
  rcases n.eq_zero_or_pos with (rfl | hnzero)
  · exact isCoprime_one_left
  rcases m.eq_zero_or_pos with (rfl | hmzero)
  · exact isCoprime_one_right
  rw [Irreducible.coprime_iff_not_dvd <| cyclotomic.irreducible_rat <| hnzero]
exact fun hdiv => h cyclotomic_injective
eq_of_monic_of_associated 

中文:
定理 cyclotomic.isCoprime_rat
  条件: {n m : 自然数} (h : n != m)
  证明: by
  rcases n.eq_zero_or_pos with (rfl | hnzero)
  · exact isCoprime_one_left
  rcases m.eq_zero_or_pos with (rfl | hmzero)
  · exact isCoprime_one_right
  rw [Irreducible.coprime_iff_not_dvd <| cyclotomic.irreducible_rat <| hnzero]
exact fun hdiv => h cyclotomic_injective
eq_of_monic_of_associated 

Depends on / 依赖: Irreducible, Irreducible.associated_of_dvd, Irreducible.coprime_iff_not_dvd, associated_of_dvd, coprime_iff_not_dvd, cyclotomic, cyclotomic.irreducible_rat, cyclotomic.monic, cyclotomic_injective, eq_of_monic_of_associated, eq_zero_or_pos, hmzero, hnzero, irreducible_rat, isCoprime_one_left, isCoprime_one_right, m.eq_zero_or_pos, n.eq_zero_or_pos
-/
theorem cyclotomic.isCoprime_rat {n m : Nat} (h : n != m) :
    IsCoprime (cyclotomic n Rat) (cyclotomic m Rat) := by
  rcases n.eq_zero_or_pos with (rfl | hnzero)
  · exact isCoprime_one_left
  rcases m.eq_zero_or_pos with (rfl | hmzero)
  · exact isCoprime_one_right
  rw [Irreducible.coprime_iff_not_dvd <| cyclotomic.irreducible_rat <| hnzero]
exact fun hdiv => h cyclotomic_injective
eq_of_monic_of_associated (cyclotomic.monic n Rat) (cyclotomic.monic m Rat)
      Irreducible.associated_of_dvd (cyclotomic.irreducible_rat hnzero)
        (cyclotomic.irreducible_rat hmzero) hdiv

end minpoly

end Polynomial

namespace IsPrimitiveRoot

open Polynomial

variable {K : Type*} [Field K] [CharZero K]
variable {p : Nat} {ζ : K}

/--
lemma `sum_eq_zero_iff_forall_eq` / 引理 `sum_eq_zero_iff_forall_eq`

English:
lemma sum_eq_zero_iff_forall_eq
  given: (hp : p.Prime) (hζ : IsPrimitiveRoot ζ p) (α : Fin p -> Rat)
  proof: by
  have : Fact p.Prime := ⟨hp⟩
  let P : Rat[X] := ∑ i, C (α i) * X ^ i.1
  have hP (i : Fin p) : α i = P.coeff i := by simp [P, ← Fin.ext_iff]
  have hP' : P.degree <= ↑(p - 1) :=
    (degree_sum_le ..).trans (Finset.sup_le fun _ _ => by grw [degree_C_mul_X_pow_le]; simp; grind)
  trans aeval ζ P

中文:
引理 sum_eq_zero_iff_对任意_eq
  条件: (hp : p.素) (hζ : 是PrimitiveRoot ζ p) (α : 有限集 p -> 有理数)
  证明: by
  have : Fact p.Prime := ⟨hp⟩
  let P : Rat[X] := ∑ i, C (α i) * X ^ i.1
  have hP (i : Fin p) : α i = P.coeff i := by simp [P, ← Fin.ext_iff]
  have hP' : P.degree <= ↑(p - 1) :=
    (degree_sum_le ..).trans (Finset.sup_le fun _ _ => by grw [degree_C_mul_X_pow_le]; simp; grind)
  trans aeval ζ P

Depends on / 依赖: Fin.ext_iff, Finset, Finset.sup_le, P.coeff, P.degree, Polynomial, Polynomial.ext, cyclotomic_eq_minpoly_rat, degree, degree_, degree_C_mul_X_pow_le, degree_mul, degree_sum_le, dvd_iff, ext_iff, hp.pos, minpoly, minpoly.dvd_iff, p.Prime, sup_le
-/
lemma sum_eq_zero_iff_forall_eq (hp : p.Prime) (hζ : IsPrimitiveRoot ζ p) (α : Fin p -> Rat) :
    ∑ i, α i * ζ ^ i.val = 0 ↔ forall i j, α i = α j := by
  have : Fact p.Prime := ⟨hp⟩
  let P : Rat[X] := ∑ i, C (α i) * X ^ i.1
  have hP (i : Fin p) : α i = P.coeff i := by simp [P, ← Fin.ext_iff]
  have hP' : P.degree <= ↑(p - 1) :=
    (degree_sum_le ..).trans (Finset.sup_le fun _ _ => by grw [degree_C_mul_X_pow_le]; simp; grind)
  trans aeval ζ P = 0; · simp [P]
  rw [← minpoly.dvd_iff]; rw [← cyclotomic_eq_minpoly_rat hζ hp.pos]
  refine ⟨fun ⟨c, hc⟩ => ?_, fun H => ⟨C (α 0), Polynomial.ext fun i => if h : i < p then ?_ else ?_⟩⟩
  · rw [hc, degree_mul, degree_cyclotomic, Nat.totient_prime hp] at hP'
    have : c.degree <= 0 := (WithBot.add_le_add_iff_left (x := ↑(p - 1)) (by simp)).mp (by simpa)
    obtain ⟨c, rfl⟩ := natDegree_eq_zero.mp (natDegree_eq_zero_iff_degree_le_zero.mpr this)
    simp [hP, hc, cyclotomic_prime]
  · lift i to Fin p using h; simp [cyclotomic_prime, ← hP, H i 0]
  · simp [cyclotomic_prime, P, h, Fin.forall_iff, @forall_comm _ (_ = _), Finset.sum_eq_zero]

/--
lemma `sum_eq_zero_iff_forall_eq_int` / 引理 `sum_eq_zero_iff_forall_eq_int`

English:
lemma sum_eq_zero_iff_forall_eq_int
  given: (hp : p.Prime) (hζ : IsPrimitiveRoot ζ p) (α : Fin p -> Int)
  proof: by
  simpa using sum_eq_zero_iff_forall_eq hp hζ (Int.cast ∘ α)

中文:
引理 sum_eq_zero_iff_对任意_eq_int
  条件: (hp : p.素) (hζ : 是PrimitiveRoot ζ p) (α : 有限集 p -> 整数)
  证明: by
  simpa using sum_eq_zero_iff_forall_eq hp hζ (Int.cast ∘ α)

Depends on / 依赖: Int.cast, sum_eq_zero_iff_forall_eq
-/
lemma sum_eq_zero_iff_forall_eq_int (hp : p.Prime) (hζ : IsPrimitiveRoot ζ p) (α : Fin p -> Int) :
    ∑ i, α i * ζ ^ i.val = 0 ↔ forall i j, α i = α j := by
  simpa using sum_eq_zero_iff_forall_eq hp hζ (Int.cast ∘ α)

end IsPrimitiveRoot
