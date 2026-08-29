/-
Copyright (c) 2019 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin
-/
module

public import Mathlib.Algebra.Polynomial.Expand
public import Mathlib.RingTheory.Adjoin.Polynomial.Basic
public import Mathlib.RingTheory.Algebraic.Defs
public import Mathlib.RingTheory.Polynomial.Tower
public import Mathlib.RingTheory.Polynomial.UniqueFactorization

/-!
# Algebraic elements and algebraic extensions

An element of an R-algebra is algebraic over R if it is the root of a nonzero polynomial.
An R-algebra is algebraic over R if and only if all its elements are algebraic over R.
The main result in this file proves transitivity of algebraicity:
a tower of algebraic field extensions is algebraic.
-/

@[expose] public section

universe u v w

open Module Polynomial nonZeroDivisors

section

variable (R : Type u) {A : Type v} [CommRing R] [Ring A] [Algebra R A]

@[nontriviality]
/--
theorem `is_transcendental_of_subsingleton` / 定理 `is_transcendental_of_subsingleton`

English:
theorem is_transcendental_of_subsingleton
  given: [Subsingleton R] (x : A)
  statement: Transcendental R x
  proof: fun ⟨p, h, _⟩ => h Subsingleton.elim p 0

中文:
定理 is_transcendental_of_subsingleton
  条件: [子单例 R] (x : A)
  结论: 超越 R x
  证明: fun ⟨p, h, _⟩ => h Subsingleton.elim p 0

Depends on / 依赖: Subsingleton, Subsingleton.elim
-/
theorem is_transcendental_of_subsingleton [Subsingleton R] (x : A) : Transcendental R x :=
fun ⟨p, h, _⟩ => h Subsingleton.elim p 0

variable {R}

/--
theorem `IsAlgebraic.nontrivial` / 定理 `IsAlgebraic.nontrivial`

English:
theorem IsAlgebraic.nontrivial
  given: {a : A} (h : IsAlgebraic R a)
  statement: Nontrivial R
  proof: by
  contrapose! h
  apply is_transcendental_of_subsingleton

中文:
定理 是代数.nontrivial
  条件: {a : A} (h : 是代数 R a)
  结论: 非平凡 R
  证明: by
  contrapose! h
  apply is_transcendental_of_subsingleton

Depends on / 依赖: contrapose, is_transcendental_of_subsingleton
-/
theorem IsAlgebraic.nontrivial {a : A} (h : IsAlgebraic R a) : Nontrivial R := by
  contrapose! h
  apply is_transcendental_of_subsingleton

variable (R A)

/--
theorem `Algebra.IsAlgebraic.nontrivial` / 定理 `Algebra.IsAlgebraic.nontrivial`

English:
theorem Algebra.IsAlgebraic.nontrivial
  given: [alg : Algebra.IsAlgebraic R A]
  statement: Nontrivial R
  proof: (alg.1 0).nontrivial

中文:
定理 代数.是代数.nontrivial
  条件: [alg : 代数.是代数 R A]
  结论: 非平凡 R
  证明: (alg.1 0).nontrivial

Depends on / 依赖: nontrivial
-/
theorem Algebra.IsAlgebraic.nontrivial [alg : Algebra.IsAlgebraic R A] : Nontrivial R :=
  (alg.1 0).nontrivial

instance (priority := low) Algebra.transcendental_of_subsingleton [Subsingleton R] :
    Algebra.Transcendental R A :=
  ⟨⟨0, is_transcendental_of_subsingleton R 0⟩⟩

/--
theorem `Polynomial.transcendental_X` / 定理 `Polynomial.transcendental_X`

English:
theorem Polynomial.transcendental_X
  statement: Transcendental R (X (R := R))
  proof: by
  simp [transcendental_iff]

中文:
定理 多项式.transcendental_X
  结论: 超越 R (X (R := R))
  证明: by
  simp [transcendental_iff]

Depends on / 依赖: transcendental_iff
-/
theorem Polynomial.transcendental_X : Transcendental R (X (R := R)) := by
  simp [transcendental_iff]

variable {R A}

/--
theorem `IsAlgebraic.of_aeval` / 定理 `IsAlgebraic.of_aeval`

English:
theorem IsAlgebraic.of_aeval
  statement: {r : A} (f : R[X]) (hf : f.natDegree != 0)
  proof: by
  obtain ⟨p, h1, h2⟩ := H
have : (p.comp f).coeff (p.natDegree * f.natDegree) != 0 := fun h => h1 by
    rwa [coeff_comp_degree_mul_degree hf,
      mul_right_mem_nonZeroDivisors_eq_zero_iff (pow_mem hf' _),
      leadingCoeff_eq_zero] at h
  exact ⟨p.comp f, fun h => this (by simp [h]), by rwa [aeval_comp]⟩

中文:
定理 是代数.of_aeval
  结论: {r : A} (f : R[X]) (hf : f.natDegree != 0)
  证明: by
  obtain ⟨p, h1, h2⟩ := H
have : (p.comp f).coeff (p.natDegree * f.natDegree) != 0 := fun h => h1 by
    rwa [coeff_comp_degree_mul_degree hf,
      mul_right_mem_nonZeroDivisors_eq_zero_iff (pow_mem hf' _),
      leadingCoeff_eq_zero] at h
  exact ⟨p.comp f, fun h => this (by simp [h]), by rwa [aeval_comp]⟩

Depends on / 依赖: aeval_comp, coeff_comp_degree_mul_degree, f.natDegree, leadingCoeff_eq_zero, mul_right_mem_nonZeroDivisors_eq_zero_iff, natDegree, p.comp, p.natDegree, pow_mem
-/
theorem IsAlgebraic.of_aeval {r : A} (f : R[X]) (hf : f.natDegree != 0)
    (hf' : f.leadingCoeff in R⁰) (H : IsAlgebraic R (aeval r f)) :
    IsAlgebraic R r := by
  obtain ⟨p, h1, h2⟩ := H
have : (p.comp f).coeff (p.natDegree * f.natDegree) != 0 := fun h => h1 by
    rwa [coeff_comp_degree_mul_degree hf,
      mul_right_mem_nonZeroDivisors_eq_zero_iff (pow_mem hf' _),
      leadingCoeff_eq_zero] at h
  exact ⟨p.comp f, fun h => this (by simp [h]), by rwa [aeval_comp]⟩

/--
theorem `Transcendental.aeval` / 定理 `Transcendental.aeval`

English:
theorem Transcendental.aeval
  statement: {r : A} (H : Transcendental R r) (f : R[X]) (hf : f.natDegree != 0)
  proof: fun h => H (h.of_aeval f hf hf')

中文:
定理 超越.aeval
  结论: {r : A} (H : 超越 R r) (f : R[X]) (hf : f.natDegree != 0)
  证明: fun h => H (h.of_aeval f hf hf')

Depends on / 依赖: h.of_aeval, of_aeval
-/
theorem Transcendental.aeval {r : A} (H : Transcendental R r) (f : R[X]) (hf : f.natDegree != 0)
    (hf' : f.leadingCoeff in R⁰) :
    Transcendental R (aeval r f) := fun h => H (h.of_aeval f hf hf')

/--
theorem `Transcendental.aeval_of_transcendental` / 定理 `Transcendental.aeval_of_transcendental`

English:
theorem Transcendental.aeval_of_transcendental
  statement: {r : A} (H : Transcendental R r)
  proof: by
  rw [transcendental_iff] at H hf ⊢
  intro p hp
  exact hf _ (H _ (by rwa [← aeval_comp, comp_eq_aeval] at hp))

中文:
定理 超越.aeval_of_transcendental
  结论: {r : A} (H : 超越 R r)
  证明: by
  rw [transcendental_iff] at H hf ⊢
  intro p hp
  exact hf _ (H _ (by rwa [← aeval_comp, comp_eq_aeval] at hp))

Depends on / 依赖: aeval_comp, comp_eq_aeval, transcendental_iff
-/
theorem Transcendental.aeval_of_transcendental {r : A} (H : Transcendental R r)
    {f : R[X]} (hf : Transcendental R f) : Transcendental R (Polynomial.aeval r f) := by
  rw [transcendental_iff] at H hf ⊢
  intro p hp
  exact hf _ (H _ (by rwa [← aeval_comp, comp_eq_aeval] at hp))

/--
theorem `Transcendental.of_aeval` / 定理 `Transcendental.of_aeval`

English:
theorem Transcendental.of_aeval
  statement: {r : A} {f : R[X]}
  proof: by
  rw [transcendental_iff] at H ⊢
  intro p hp
  exact H p (by rw [← aeval_comp, comp_eq_aeval, hp, map_zero])

中文:
定理 超越.of_aeval
  结论: {r : A} {f : R[X]}
  证明: by
  rw [transcendental_iff] at H ⊢
  intro p hp
  exact H p (by rw [← aeval_comp, comp_eq_aeval, hp, map_zero])

Depends on / 依赖: aeval_comp, comp_eq_aeval, map_zero, transcendental_iff
-/
theorem Transcendental.of_aeval {r : A} {f : R[X]}
    (H : Transcendental R (Polynomial.aeval r f)) : Transcendental R f := by
  rw [transcendental_iff] at H ⊢
  intro p hp
  exact H p (by rw [← aeval_comp, comp_eq_aeval, hp, map_zero])

/--
theorem `IsAlgebraic.of_aeval_of_transcendental` / 定理 `IsAlgebraic.of_aeval_of_transcendental`

English:
theorem IsAlgebraic.of_aeval_of_transcendental
  statement: {r : A} {f : R[X]}
  proof: by
  contrapose H
  exact Transcendental.aeval_of_transcendental H hf

中文:
定理 是代数.of_aeval_of_transcendental
  结论: {r : A} {f : R[X]}
  证明: by
  contrapose H
  exact Transcendental.aeval_of_transcendental H hf

Depends on / 依赖: Transcendental, Transcendental.aeval_of_transcendental, aeval_of_transcendental, contrapose
-/
theorem IsAlgebraic.of_aeval_of_transcendental {r : A} {f : R[X]}
    (H : IsAlgebraic R (aeval r f)) (hf : Transcendental R f) : IsAlgebraic R r := by
  contrapose H
  exact Transcendental.aeval_of_transcendental H hf

/--
theorem `Polynomial.transcendental` / 定理 `Polynomial.transcendental`

English:
theorem Polynomial.transcendental
  statement: (f : R[X]) (hf : f.natDegree != 0)
  proof: by
  simpa using (transcendental_X R).aeval f hf hf'

中文:
定理 多项式.transcendental
  结论: (f : R[X]) (hf : f.natDegree != 0)
  证明: by
  simpa using (transcendental_X R).aeval f hf hf'

Depends on / 依赖: transcendental_X
-/
theorem Polynomial.transcendental (f : R[X]) (hf : f.natDegree != 0)
    (hf' : f.leadingCoeff in R⁰) :
    Transcendental R f := by
  simpa using (transcendental_X R).aeval f hf hf'

/--
theorem `isAlgebraic_iff_not_injective` / 定理 `isAlgebraic_iff_not_injective`

English:
theorem isAlgebraic_iff_not_injective
  given: {x : A}
  proof: by
  simp only [IsAlgebraic, injective_iff_map_eq_zero, not_forall, and_comm, exists_prop]

中文:
定理 isAlgebraic_iff_not_injective
  条件: {x : A}
  证明: by
  simp only [IsAlgebraic, injective_iff_map_eq_zero, not_forall, and_comm, exists_prop]

Depends on / 依赖: IsAlgebraic, and_comm, exists_prop, injective_iff_map_eq_zero, not_forall
-/
theorem isAlgebraic_iff_not_injective {x : A} :
    IsAlgebraic R x ↔ ¬Function.Injective (Polynomial.aeval x : R[X] ->ₐ[R] A) := by
  simp only [IsAlgebraic, injective_iff_map_eq_zero, not_forall, and_comm, exists_prop]

/--
theorem `transcendental_iff_injective` / 定理 `transcendental_iff_injective`

English:
theorem transcendental_iff_injective
  given: {x : A}
  proof: isAlgebraic_iff_not_injective.not_left

中文:
定理 transcendental_iff_injective
  条件: {x : A}
  证明: isAlgebraic_iff_not_injective.not_left

Depends on / 依赖: isAlgebraic_iff_not_injective, isAlgebraic_iff_not_injective.not_left, not_left
-/
theorem transcendental_iff_injective {x : A} :
    Transcendental R x ↔ Function.Injective (Polynomial.aeval x : R[X] ->ₐ[R] A) :=
  isAlgebraic_iff_not_injective.not_left

/--
theorem `transcendental_iff_ker_eq_bot` / 定理 `transcendental_iff_ker_eq_bot`

English:
theorem transcendental_iff_ker_eq_bot
  given: {x : A}
  proof: by
  rw [transcendental_iff_injective]; rw [RingHom.injective_iff_ker_eq_bot]

中文:
定理 transcendental_iff_ker_eq_bot
  条件: {x : A}
  证明: by
  rw [transcendental_iff_injective]; rw [RingHom.injective_iff_ker_eq_bot]

Depends on / 依赖: RingHom, RingHom.injective_iff_ker_eq_bot, injective_iff_ker_eq_bot, transcendental_iff_injective
-/
theorem transcendental_iff_ker_eq_bot {x : A} :
    Transcendental R x ↔ RingHom.ker (aeval (R := R) x) = ⊥ := by
  rw [transcendental_iff_injective]; rw [RingHom.injective_iff_ker_eq_bot]

/--
theorem `Algebra.isAlgebraic_of_not_injective` / 定理 `Algebra.isAlgebraic_of_not_injective`

English:
theorem Algebra.isAlgebraic_of_not_injective
  given: (h : ¬ Function.Injective (algebraMap R A))
  proof: isAlgebraic_iff_not_injective.mpr
fun inj => h by convert! inj.comp C_injective; ext; simp

中文:
定理 代数.isAlgebraic_of_not_injective
  条件: (h : ¬ 函数.单射 (algebraMap R A))
  证明: isAlgebraic_iff_not_injective.mpr
fun inj => h by convert! inj.comp C_injective; ext; simp

Depends on / 依赖: isAlgebraic_iff_not_injective, isAlgebraic_iff_not_injective.mpr
-/
theorem Algebra.isAlgebraic_of_not_injective (h : ¬ Function.Injective (algebraMap R A)) :
    Algebra.IsAlgebraic R A where
  isAlgebraic a := isAlgebraic_iff_not_injective.mpr
fun inj => h by convert! inj.comp C_injective; ext; simp

/--
theorem `Algebra.injective_of_transcendental` / 定理 `Algebra.injective_of_transcendental`

English:
theorem Algebra.injective_of_transcendental
  given: [h : Algebra.Transcendental R A]
  proof: by
  rw [transcendental_iff_not_isAlgebraic] at h
  contrapose h
  exact isAlgebraic_of_not_injective h

中文:
定理 代数.injective_of_transcendental
  条件: [h : 代数.超越 R A]
  证明: by
  rw [transcendental_iff_not_isAlgebraic] at h
  contrapose h
  exact isAlgebraic_of_not_injective h

Depends on / 依赖: contrapose, isAlgebraic_of_not_injective, transcendental_iff_not_isAlgebraic
-/
theorem Algebra.injective_of_transcendental [h : Algebra.Transcendental R A] :
    Function.Injective (algebraMap R A) := by
  rw [transcendental_iff_not_isAlgebraic] at h
  contrapose h
  exact isAlgebraic_of_not_injective h

end

section zero_ne_one

variable {R : Type u} {S : Type*} {A : Type v} [CommRing R]
variable [CommRing S] [Ring A] [Algebra R A] [Algebra R S] [Algebra S A]
variable [IsScalarTower R S A]

/--
theorem `isAlgebraic_zero` / 定理 `isAlgebraic_zero`

English:
theorem isAlgebraic_zero
  given: [Nontrivial R]
  statement: IsAlgebraic R (0 : A)
  proof: ⟨_, X_ne_zero, aeval_X 0⟩

中文:
定理 isAlgebraic_zero
  条件: [非平凡 R]
  结论: 是代数 R (0 : A)
  证明: ⟨_, X_ne_zero, aeval_X 0⟩

Depends on / 依赖: X_ne_zero, aeval_X
-/
theorem isAlgebraic_zero [Nontrivial R] : IsAlgebraic R (0 : A) :=
  ⟨_, X_ne_zero, aeval_X 0⟩

/--
theorem `isAlgebraic_algebraMap` / 定理 `isAlgebraic_algebraMap`

English:
theorem isAlgebraic_algebraMap
  given: [Nontrivial R] (x : R)
  statement: IsAlgebraic R (algebraMap R A x)
  proof: ⟨_, X_sub_C_ne_zero x, by rw [map_sub, aeval_X, aeval_C, sub_self]⟩

中文:
定理 isAlgebraic_algebraMap
  条件: [非平凡 R] (x : R)
  结论: 是代数 R (algebraMap R A x)
  证明: ⟨_, X_sub_C_ne_zero x, by rw [map_sub, aeval_X, aeval_C, sub_self]⟩

Depends on / 依赖: X_sub_C_ne_zero, aeval_C, aeval_X, map_sub, sub_self
-/
theorem isAlgebraic_algebraMap [Nontrivial R] (x : R) : IsAlgebraic R (algebraMap R A x) :=
  ⟨_, X_sub_C_ne_zero x, by rw [map_sub, aeval_X, aeval_C, sub_self]⟩

/--
theorem `isAlgebraic_one` / 定理 `isAlgebraic_one`

English:
theorem isAlgebraic_one
  given: [Nontrivial R]
  statement: IsAlgebraic R (1 : A)
  proof: by
  rw [← map_one (algebraMap R A)]
  exact isAlgebraic_algebraMap 1

中文:
定理 isAlgebraic_one
  条件: [非平凡 R]
  结论: 是代数 R (1 : A)
  证明: by
  rw [← map_one (algebraMap R A)]
  exact isAlgebraic_algebraMap 1

Depends on / 依赖: algebraMap, isAlgebraic_algebraMap, map_one
-/
theorem isAlgebraic_one [Nontrivial R] : IsAlgebraic R (1 : A) := by
  rw [← map_one (algebraMap R A)]
  exact isAlgebraic_algebraMap 1

/--
theorem `isAlgebraic_natCast` / 定理 `isAlgebraic_natCast`

English:
theorem isAlgebraic_natCast
  given: [Nontrivial R] (n : Nat)
  statement: IsAlgebraic R (n : A)
  proof: by
  rw [← map_natCast (_ : R ->+* A) n]
  exact isAlgebraic_algebraMap (Nat.cast n)

中文:
定理 isAlgebraic_natCast
  条件: [非平凡 R] (n : 自然数)
  结论: 是代数 R (n : A)
  证明: by
  rw [← map_natCast (_ : R ->+* A) n]
  exact isAlgebraic_algebraMap (Nat.cast n)

Depends on / 依赖: Nat.cast, isAlgebraic_algebraMap, map_natCast
-/
theorem isAlgebraic_natCast [Nontrivial R] (n : Nat) : IsAlgebraic R (n : A) := by
  rw [← map_natCast (_ : R ->+* A) n]
  exact isAlgebraic_algebraMap (Nat.cast n)

/--
theorem `isAlgebraic_intCast` / 定理 `isAlgebraic_intCast`

English:
theorem isAlgebraic_intCast
  given: [Nontrivial R] (n : Int)
  statement: IsAlgebraic R (n : A)
  proof: by
  rw [← map_intCast (algebraMap R A)]
  exact isAlgebraic_algebraMap (Int.cast n)

中文:
定理 isAlgebraic_intCast
  条件: [非平凡 R] (n : 整数)
  结论: 是代数 R (n : A)
  证明: by
  rw [← map_intCast (algebraMap R A)]
  exact isAlgebraic_algebraMap (Int.cast n)

Depends on / 依赖: Int.cast, algebraMap, isAlgebraic_algebraMap, map_intCast
-/
theorem isAlgebraic_intCast [Nontrivial R] (n : Int) : IsAlgebraic R (n : A) := by
  rw [← map_intCast (algebraMap R A)]
  exact isAlgebraic_algebraMap (Int.cast n)

/--
theorem `isAlgebraic_ratCast` / 定理 `isAlgebraic_ratCast`

English:
theorem isAlgebraic_ratCast
  statement: (R : Type u) {A : Type v} [DivisionRing A] [Field R] [Algebra R A]
  proof: by
  rw [← map_ratCast (algebraMap R A)]
  exact isAlgebraic_algebraMap (Rat.cast n)

@[deprecated (since := "2026-07-14")] alias isAlgebraic_nat := isAlgebraic_natCast
@[deprecated (since := "2026-07-14")] alias isAlgebraic_int := isAlgebraic_intCast
@[deprecated (since := "2026-07-14")] alias isAlgebraic_rat := isAlgebraic_ratCast

中文:
定理 isAlgebraic_ratCast
  结论: (R : 类型u) {A : 类型v} [除环 A] [域 R] [代数 R A]
  证明: by
  rw [← map_ratCast (algebraMap R A)]
  exact isAlgebraic_algebraMap (Rat.cast n)

@[deprecated (since := "2026-07-14")] alias isAlgebraic_nat := isAlgebraic_natCast
@[deprecated (since := "2026-07-14")] alias isAlgebraic_int := isAlgebraic_intCast
@[deprecated (since := "2026-07-14")] alias isAlgebraic_rat := isAlgebraic_ratCast

Depends on / 依赖: Rat.cast, algebraMap, isAlgebraic_algebraMap, map_ratCast
-/
theorem isAlgebraic_ratCast (R : Type u) {A : Type v} [DivisionRing A] [Field R] [Algebra R A]
    (n : Rat) : IsAlgebraic R (n : A) := by
  rw [← map_ratCast (algebraMap R A)]
  exact isAlgebraic_algebraMap (Rat.cast n)

@[deprecated (since := "2026-07-14")] alias isAlgebraic_nat := isAlgebraic_natCast
@[deprecated (since := "2026-07-14")] alias isAlgebraic_int := isAlgebraic_intCast
@[deprecated (since := "2026-07-14")] alias isAlgebraic_rat := isAlgebraic_ratCast

/--
theorem `isAlgebraic_of_mem_rootSet` / 定理 `isAlgebraic_of_mem_rootSet`

English:
theorem isAlgebraic_of_mem_rootSet
  statement: {R : Type u} {A : Type v} [CommRing R] [Field A] [Algebra R A]
  proof: ⟨p, ne_zero_of_mem_rootSet hx, aeval_eq_zero_of_mem_rootSet hx⟩

中文:
定理 isAlgebraic_of_mem_rootSet
  结论: {R : 类型u} {A : 类型v} [交换环 R] [域 A] [代数 R A]
  证明: ⟨p, ne_zero_of_mem_rootSet hx, aeval_eq_zero_of_mem_rootSet hx⟩

Depends on / 依赖: aeval_eq_zero_of_mem_rootSet, ne_zero_of_mem_rootSet
-/
theorem isAlgebraic_of_mem_rootSet {R : Type u} {A : Type v} [CommRing R] [Field A] [Algebra R A]
    {p : R[X]} {x : A} (hx : x in p.rootSet A) : IsAlgebraic R x :=
  ⟨p, ne_zero_of_mem_rootSet hx, aeval_eq_zero_of_mem_rootSet hx⟩

variable (S) in
/--
theorem `IsLocalization.isAlgebraic` / 定理 `IsLocalization.isAlgebraic`

English:
theorem IsLocalization.isAlgebraic
  given: [Nontrivial R] (M : Submonoid R) [IsLocalization M S]
  proof: by
    obtain rfl | hx := eq_or_ne x 0
    · exact isAlgebraic_zero
    have ⟨⟨r, m⟩, h⟩ := surj M x
    refine ⟨C m.1 * X - C r, fun eq => hx ?_, by simpa [sub_eq_zero, mul_comm x] using h⟩
    rwa [← eq_mk'_iff_mul_eq, show r = 0 by simpa using congr(coeff $eq 0), mk'_zero] at h

中文:
定理 是Localization.isAlgebraic
  条件: [非平凡 R] (M : 子幺半群 R) [是Localization M S]
  证明: by
    obtain rfl | hx := eq_or_ne x 0
    · exact isAlgebraic_zero
    have ⟨⟨r, m⟩, h⟩ := surj M x
    refine ⟨C m.1 * X - C r, fun eq => hx ?_, by simpa [sub_eq_zero, mul_comm x] using h⟩
    rwa [← eq_mk'_iff_mul_eq, show r = 0 by simpa using congr(coeff $eq 0), mk'_zero] at h

Depends on / 依赖: _iff_mul_eq, _zero, eq_mk, eq_or_ne, isAlgebraic_zero, mul_comm, sub_eq_zero
-/
theorem IsLocalization.isAlgebraic [Nontrivial R] (M : Submonoid R) [IsLocalization M S] :
    Algebra.IsAlgebraic R S where
  isAlgebraic x := by
    obtain rfl | hx := eq_or_ne x 0
    · exact isAlgebraic_zero
    have ⟨⟨r, m⟩, h⟩ := surj M x
    refine ⟨C m.1 * X - C r, fun eq => hx ?_, by simpa [sub_eq_zero, mul_comm x] using h⟩
    rwa [← eq_mk'_iff_mul_eq, show r = 0 by simpa using congr(coeff $eq 0), mk'_zero] at h

open IsScalarTower

/--
theorem `IsAlgebraic.algebraMap` / 定理 `IsAlgebraic.algebraMap`

English:
theorem IsAlgebraic.algebraMap
  given: {a : S}
  proof: fun ⟨f, hf₁, hf₂⟩ =>
  ⟨f, hf₁, by rw [aeval_algebraMap_apply, hf₂, map_zero]⟩

中文:
定理 是代数.algebraMap
  条件: {a : S}
  证明: fun ⟨f, hf₁, hf₂⟩ =>
  ⟨f, hf₁, by rw [aeval_algebraMap_apply, hf₂, map_zero]⟩
-/
protected theorem IsAlgebraic.algebraMap {a : S} :
    IsAlgebraic R a -> IsAlgebraic R (algebraMap S A a) := fun ⟨f, hf₁, hf₂⟩ =>
  ⟨f, hf₁, by rw [aeval_algebraMap_apply, hf₂, map_zero]⟩

section

variable {B : Type*} [Ring B] [Algebra R B]

/--
theorem `IsAlgebraic.algHom` / 定理 `IsAlgebraic.algHom`

English:
theorem IsAlgebraic.algHom
  statement: (f : A ->ₐ[R] B) {a : A}
  proof: let ⟨p, hp, ha⟩ := h
  ⟨p, hp, by rw [aeval_algHom, f.comp_apply, ha, map_zero]⟩

中文:
定理 是代数.algHom
  结论: (f : A ->ₐ[R] B) {a : A}
  证明: let ⟨p, hp, ha⟩ := h
  ⟨p, hp, by rw [aeval_algHom, f.comp_apply, ha, map_zero]⟩
-/
protected theorem IsAlgebraic.algHom (f : A ->ₐ[R] B) {a : A}
    (h : IsAlgebraic R a) : IsAlgebraic R (f a) :=
  let ⟨p, hp, ha⟩ := h
  ⟨p, hp, by rw [aeval_algHom, f.comp_apply, ha, map_zero]⟩

/--
theorem `isAlgebraic_algHom_iff` / 定理 `isAlgebraic_algHom_iff`

English:
theorem isAlgebraic_algHom_iff
  statement: (f : A ->ₐ[R] B) (hf : Function.Injective f)
  proof: ⟨fun ⟨p, hp0, hp⟩ => ⟨p, hp0, hf by rwa [map_zero, ← f.comp_apply, ← aeval_algHom]⟩,
    IsAlgebraic.algHom f⟩

中文:
定理 isAlgebraic_algHom_iff
  结论: (f : A ->ₐ[R] B) (hf : 函数.单射 f)
  证明: ⟨fun ⟨p, hp0, hp⟩ => ⟨p, hp0, hf by rwa [map_zero, ← f.comp_apply, ← aeval_algHom]⟩,
    IsAlgebraic.algHom f⟩

Depends on / 依赖: IsAlgebraic, IsAlgebraic.algHom, aeval_algHom, algHom, comp_apply, f.comp_apply, map_zero
-/
theorem isAlgebraic_algHom_iff (f : A ->ₐ[R] B) (hf : Function.Injective f)
    {a : A} : IsAlgebraic R (f a) ↔ IsAlgebraic R a :=
⟨fun ⟨p, hp0, hp⟩ => ⟨p, hp0, hf by rwa [map_zero, ← f.comp_apply, ← aeval_algHom]⟩,
    IsAlgebraic.algHom f⟩

section RingHom

omit [Algebra R S] [Algebra S A] [IsScalarTower R S A] [Algebra R B]
variable [Algebra S B] {FRS FAB : Type*}

section

variable [FunLike FRS R S] [RingHomClass FRS R S] [FunLike FAB A B] [RingHomClass FAB A B]
  (f : FRS) (g : FAB) {a : A}

/--
theorem `IsAlgebraic.ringHom_of_comp_eq` / 定理 `IsAlgebraic.ringHom_of_comp_eq`

English:
theorem IsAlgebraic.ringHom_of_comp_eq
  statement: (halg : IsAlgebraic R a)
  proof: by
  obtain ⟨p, h1, h2⟩ := halg
  refine ⟨p.map f, (Polynomial.map_ne_zero_iff hf).2 h1, ?_⟩
  change aeval ((g : A ->+* B) a) _ = 0
  rw [← map_aeval_eq_aeval_map h]; rw [h2]; rw [map_zero]

中文:
定理 是代数.ringHom_of_comp_eq
  结论: (halg : 是代数 R a)
  证明: by
  obtain ⟨p, h1, h2⟩ := halg
  refine ⟨p.map f, (Polynomial.map_ne_zero_iff hf).2 h1, ?_⟩
  change aeval ((g : A ->+* B) a) _ = 0
  rw [← map_aeval_eq_aeval_map h]; rw [h2]; rw [map_zero]

Depends on / 依赖: Polynomial, Polynomial.map_ne_zero_iff, map_aeval_eq_aeval_map, map_ne_zero_iff, map_zero, p.map
-/
theorem IsAlgebraic.ringHom_of_comp_eq (halg : IsAlgebraic R a)
    (hf : Function.Injective f)
    (h : RingHom.comp (algebraMap S B) f = RingHom.comp g (algebraMap R A)) :
    IsAlgebraic S (g a) := by
  obtain ⟨p, h1, h2⟩ := halg
  refine ⟨p.map f, (Polynomial.map_ne_zero_iff hf).2 h1, ?_⟩
  change aeval ((g : A ->+* B) a) _ = 0
  rw [← map_aeval_eq_aeval_map h]; rw [h2]; rw [map_zero]

/--
theorem `Transcendental.of_ringHom_of_comp_eq` / 定理 `Transcendental.of_ringHom_of_comp_eq`

English:
theorem Transcendental.of_ringHom_of_comp_eq
  statement: (H : Transcendental S (g a))
  proof: fun halg => H (halg.ringHom_of_comp_eq f g hf h)

中文:
定理 超越.of_ringHom_of_comp_eq
  结论: (H : 超越 S (g a))
  证明: fun halg => H (halg.ringHom_of_comp_eq f g hf h)

Depends on / 依赖: halg.ringHom_of_comp_eq, ringHom_of_comp_eq
-/
theorem Transcendental.of_ringHom_of_comp_eq (H : Transcendental S (g a))
    (hf : Function.Injective f)
    (h : RingHom.comp (algebraMap S B) f = RingHom.comp g (algebraMap R A)) :
    Transcendental R a := fun halg => H (halg.ringHom_of_comp_eq f g hf h)

/--
theorem `Algebra.IsAlgebraic.ringHom_of_comp_eq` / 定理 `Algebra.IsAlgebraic.ringHom_of_comp_eq`

English:
theorem Algebra.IsAlgebraic.ringHom_of_comp_eq
  statement: [Algebra.IsAlgebraic R A]
  proof: by
  refine ⟨fun b => ?_⟩
  obtain ⟨a, rfl⟩ := hg b
  exact (Algebra.IsAlgebraic.isAlgebraic a).ringHom_of_comp_eq f g hf h

中文:
定理 代数.是代数.ringHom_of_comp_eq
  结论: [代数.是代数 R A]
  证明: by
  refine ⟨fun b => ?_⟩
  obtain ⟨a, rfl⟩ := hg b
  exact (Algebra.IsAlgebraic.isAlgebraic a).ringHom_of_comp_eq f g hf h

Depends on / 依赖: Algebra, Algebra.IsAlgebraic.isAlgebraic, IsAlgebraic, isAlgebraic, ringHom_of_comp_eq
-/
theorem Algebra.IsAlgebraic.ringHom_of_comp_eq [Algebra.IsAlgebraic R A]
    (hf : Function.Injective f) (hg : Function.Surjective g)
    (h : RingHom.comp (algebraMap S B) f = RingHom.comp g (algebraMap R A)) :
    Algebra.IsAlgebraic S B := by
  refine ⟨fun b => ?_⟩
  obtain ⟨a, rfl⟩ := hg b
  exact (Algebra.IsAlgebraic.isAlgebraic a).ringHom_of_comp_eq f g hf h

/--
theorem `Algebra.Transcendental.of_ringHom_of_comp_eq` / 定理 `Algebra.Transcendental.of_ringHom_of_comp_eq`

English:
theorem Algebra.Transcendental.of_ringHom_of_comp_eq
  statement: [H : Algebra.Transcendental S B]
  proof: by
  rw [Algebra.transcendental_iff_not_isAlgebraic] at H ⊢
  exact fun halg => H (halg.ringHom_of_comp_eq f g hf hg h)

中文:
定理 代数.超越.of_ringHom_of_comp_eq
  结论: [H : 代数.超越 S B]
  证明: by
  rw [Algebra.transcendental_iff_not_isAlgebraic] at H ⊢
  exact fun halg => H (halg.ringHom_of_comp_eq f g hf hg h)

Depends on / 依赖: Algebra, Algebra.transcendental_iff_not_isAlgebraic, halg.ringHom_of_comp_eq, ringHom_of_comp_eq, transcendental_iff_not_isAlgebraic
-/
theorem Algebra.Transcendental.of_ringHom_of_comp_eq [H : Algebra.Transcendental S B]
    (hf : Function.Injective f) (hg : Function.Surjective g)
    (h : RingHom.comp (algebraMap S B) f = RingHom.comp g (algebraMap R A)) :
    Algebra.Transcendental R A := by
  rw [Algebra.transcendental_iff_not_isAlgebraic] at H ⊢
  exact fun halg => H (halg.ringHom_of_comp_eq f g hf hg h)

/--
theorem `IsAlgebraic.of_ringHom_of_comp_eq` / 定理 `IsAlgebraic.of_ringHom_of_comp_eq`

English:
theorem IsAlgebraic.of_ringHom_of_comp_eq
  statement: (halg : IsAlgebraic S (g a))
  proof: by
  obtain ⟨p, h1, h2⟩ := halg
  obtain ⟨q, rfl⟩ := map_surjective (f : R ->+* S) hf p
  refine ⟨q, fun h' => by simp [h'] at h1, hg ?_⟩
  change aeval ((g : A ->+* B) a) _ = 0 at h2
  change (g : A ->+* B) _ = _
  rw [map_zero]; rw [map_aeval_eq_aeval_map h]; rw [h2]

中文:
定理 是代数.of_ringHom_of_comp_eq
  结论: (halg : 是代数 S (g a))
  证明: by
  obtain ⟨p, h1, h2⟩ := halg
  obtain ⟨q, rfl⟩ := map_surjective (f : R ->+* S) hf p
  refine ⟨q, fun h' => by simp [h'] at h1, hg ?_⟩
  change aeval ((g : A ->+* B) a) _ = 0 at h2
  change (g : A ->+* B) _ = _
  rw [map_zero]; rw [map_aeval_eq_aeval_map h]; rw [h2]

Depends on / 依赖: map_aeval_eq_aeval_map, map_surjective, map_zero
-/
theorem IsAlgebraic.of_ringHom_of_comp_eq (halg : IsAlgebraic S (g a))
    (hf : Function.Surjective f) (hg : Function.Injective g)
    (h : RingHom.comp (algebraMap S B) f = RingHom.comp g (algebraMap R A)) :
    IsAlgebraic R a := by
  obtain ⟨p, h1, h2⟩ := halg
  obtain ⟨q, rfl⟩ := map_surjective (f : R ->+* S) hf p
  refine ⟨q, fun h' => by simp [h'] at h1, hg ?_⟩
  change aeval ((g : A ->+* B) a) _ = 0 at h2
  change (g : A ->+* B) _ = _
  rw [map_zero]; rw [map_aeval_eq_aeval_map h]; rw [h2]

/--
theorem `Transcendental.ringHom_of_comp_eq` / 定理 `Transcendental.ringHom_of_comp_eq`

English:
theorem Transcendental.ringHom_of_comp_eq
  statement: (H : Transcendental R a)
  proof: fun halg => H (halg.of_ringHom_of_comp_eq f g hf hg h)

中文:
定理 超越.ringHom_of_comp_eq
  结论: (H : 超越 R a)
  证明: fun halg => H (halg.of_ringHom_of_comp_eq f g hf hg h)

Depends on / 依赖: halg.of_ringHom_of_comp_eq, of_ringHom_of_comp_eq
-/
theorem Transcendental.ringHom_of_comp_eq (H : Transcendental R a)
    (hf : Function.Surjective f) (hg : Function.Injective g)
    (h : RingHom.comp (algebraMap S B) f = RingHom.comp g (algebraMap R A)) :
    Transcendental S (g a) := fun halg => H (halg.of_ringHom_of_comp_eq f g hf hg h)

/--
theorem `Algebra.IsAlgebraic.of_ringHom_of_comp_eq` / 定理 `Algebra.IsAlgebraic.of_ringHom_of_comp_eq`

English:
theorem Algebra.IsAlgebraic.of_ringHom_of_comp_eq
  statement: [Algebra.IsAlgebraic S B]
  proof: ⟨fun a => (Algebra.IsAlgebraic.isAlgebraic (g a)).of_ringHom_of_comp_eq f g hf hg h⟩

中文:
定理 代数.是代数.of_ringHom_of_comp_eq
  结论: [代数.是代数 S B]
  证明: ⟨fun a => (Algebra.IsAlgebraic.isAlgebraic (g a)).of_ringHom_of_comp_eq f g hf hg h⟩

Depends on / 依赖: Algebra, Algebra.IsAlgebraic.isAlgebraic, IsAlgebraic, isAlgebraic, of_ringHom_of_comp_eq
-/
theorem Algebra.IsAlgebraic.of_ringHom_of_comp_eq [Algebra.IsAlgebraic S B]
    (hf : Function.Surjective f) (hg : Function.Injective g)
    (h : RingHom.comp (algebraMap S B) f = RingHom.comp g (algebraMap R A)) :
    Algebra.IsAlgebraic R A :=
  ⟨fun a => (Algebra.IsAlgebraic.isAlgebraic (g a)).of_ringHom_of_comp_eq f g hf hg h⟩

/--
theorem `Algebra.Transcendental.ringHom_of_comp_eq` / 定理 `Algebra.Transcendental.ringHom_of_comp_eq`

English:
theorem Algebra.Transcendental.ringHom_of_comp_eq
  statement: [H : Algebra.Transcendental R A]
  proof: by
  rw [Algebra.transcendental_iff_not_isAlgebraic] at H ⊢
  exact fun halg => H (halg.of_ringHom_of_comp_eq f g hf hg h)

中文:
定理 代数.超越.ringHom_of_comp_eq
  结论: [H : 代数.超越 R A]
  证明: by
  rw [Algebra.transcendental_iff_not_isAlgebraic] at H ⊢
  exact fun halg => H (halg.of_ringHom_of_comp_eq f g hf hg h)

Depends on / 依赖: Algebra, Algebra.transcendental_iff_not_isAlgebraic, halg.of_ringHom_of_comp_eq, of_ringHom_of_comp_eq, transcendental_iff_not_isAlgebraic
-/
theorem Algebra.Transcendental.ringHom_of_comp_eq [H : Algebra.Transcendental R A]
    (hf : Function.Surjective f) (hg : Function.Injective g)
    (h : RingHom.comp (algebraMap S B) f = RingHom.comp g (algebraMap R A)) :
    Algebra.Transcendental S B := by
  rw [Algebra.transcendental_iff_not_isAlgebraic] at H ⊢
  exact fun halg => H (halg.of_ringHom_of_comp_eq f g hf hg h)

end

section

variable [EquivLike FRS R S] [RingEquivClass FRS R S] [FunLike FAB A B] [RingHomClass FAB A B]
  (f : FRS) (g : FAB)

/--
theorem `isAlgebraic_ringHom_iff_of_comp_eq` / 定理 `isAlgebraic_ringHom_iff_of_comp_eq`

English:
theorem isAlgebraic_ringHom_iff_of_comp_eq
  proof: ⟨fun H => H.of_ringHom_of_comp_eq f g (EquivLike.surjective f) hg h,
    fun H => H.ringHom_of_comp_eq f g (EquivLike.injective f) h⟩

中文:
定理 isAlgebraic_ringHom_iff_of_comp_eq
  证明: ⟨fun H => H.of_ringHom_of_comp_eq f g (EquivLike.surjective f) hg h,
    fun H => H.ringHom_of_comp_eq f g (EquivLike.injective f) h⟩

Depends on / 依赖: EquivLike, EquivLike.injective, EquivLike.surjective, H.of_ringHom_of_comp_eq, H.ringHom_of_comp_eq, injective, of_ringHom_of_comp_eq, ringHom_of_comp_eq, surjective
-/
theorem isAlgebraic_ringHom_iff_of_comp_eq
    (hg : Function.Injective g)
    (h : RingHom.comp (algebraMap S B) f = RingHom.comp g (algebraMap R A)) {a : A} :
    IsAlgebraic S (g a) ↔ IsAlgebraic R a :=
  ⟨fun H => H.of_ringHom_of_comp_eq f g (EquivLike.surjective f) hg h,
    fun H => H.ringHom_of_comp_eq f g (EquivLike.injective f) h⟩

/--
theorem `transcendental_ringHom_iff_of_comp_eq` / 定理 `transcendental_ringHom_iff_of_comp_eq`

English:
theorem transcendental_ringHom_iff_of_comp_eq
  proof: not_congr (isAlgebraic_ringHom_iff_of_comp_eq f g hg h)

中文:
定理 transcendental_ringHom_iff_of_comp_eq
  证明: not_congr (isAlgebraic_ringHom_iff_of_comp_eq f g hg h)

Depends on / 依赖: isAlgebraic_ringHom_iff_of_comp_eq, not_congr
-/
theorem transcendental_ringHom_iff_of_comp_eq
    (hg : Function.Injective g)
    (h : RingHom.comp (algebraMap S B) f = RingHom.comp g (algebraMap R A)) {a : A} :
    Transcendental S (g a) ↔ Transcendental R a :=
  not_congr (isAlgebraic_ringHom_iff_of_comp_eq f g hg h)

end

section

variable [EquivLike FRS R S] [RingEquivClass FRS R S] [EquivLike FAB A B] [RingEquivClass FAB A B]
  (f : FRS) (g : FAB)

/--
theorem `Algebra.isAlgebraic_ringHom_iff_of_comp_eq` / 定理 `Algebra.isAlgebraic_ringHom_iff_of_comp_eq`

English:
theorem Algebra.isAlgebraic_ringHom_iff_of_comp_eq
  proof: ⟨fun H => H.of_ringHom_of_comp_eq f g (EquivLike.surjective f) (EquivLike.injective g) h,
    fun H => H.ringHom_of_comp_eq f g (EquivLike.injective f) (EquivLike.surjective g) h⟩

中文:
定理 代数.isAlgebraic_ringHom_iff_of_comp_eq
  证明: ⟨fun H => H.of_ringHom_of_comp_eq f g (EquivLike.surjective f) (EquivLike.injective g) h,
    fun H => H.ringHom_of_comp_eq f g (EquivLike.injective f) (EquivLike.surjective g) h⟩

Depends on / 依赖: EquivLike, EquivLike.injective, EquivLike.surjective, H.of_ringHom_of_comp_eq, H.ringHom_of_comp_eq, injective, of_ringHom_of_comp_eq, ringHom_of_comp_eq, surjective
-/
theorem Algebra.isAlgebraic_ringHom_iff_of_comp_eq
    (h : RingHom.comp (algebraMap S B) f = RingHom.comp g (algebraMap R A)) :
    Algebra.IsAlgebraic S B ↔ Algebra.IsAlgebraic R A :=
  ⟨fun H => H.of_ringHom_of_comp_eq f g (EquivLike.surjective f) (EquivLike.injective g) h,
    fun H => H.ringHom_of_comp_eq f g (EquivLike.injective f) (EquivLike.surjective g) h⟩

/--
theorem `Algebra.transcendental_ringHom_iff_of_comp_eq` / 定理 `Algebra.transcendental_ringHom_iff_of_comp_eq`

English:
theorem Algebra.transcendental_ringHom_iff_of_comp_eq
  proof: by
  simp_rw [Algebra.transcendental_iff_not_isAlgebraic,
    Algebra.isAlgebraic_ringHom_iff_of_comp_eq f g h]

中文:
定理 代数.transcendental_ringHom_iff_of_comp_eq
  证明: by
  simp_rw [Algebra.transcendental_iff_not_isAlgebraic,
    Algebra.isAlgebraic_ringHom_iff_of_comp_eq f g h]

Depends on / 依赖: Algebra, Algebra.isAlgebraic_ringHom_iff_of_comp_eq, Algebra.transcendental_iff_not_isAlgebraic, isAlgebraic_ringHom_iff_of_comp_eq, simp_rw, transcendental_iff_not_isAlgebraic
-/
theorem Algebra.transcendental_ringHom_iff_of_comp_eq
    (h : RingHom.comp (algebraMap S B) f = RingHom.comp g (algebraMap R A)) :
    Algebra.Transcendental S B ↔ Algebra.Transcendental R A := by
  simp_rw [Algebra.transcendental_iff_not_isAlgebraic,
    Algebra.isAlgebraic_ringHom_iff_of_comp_eq f g h]

end

end RingHom

/--
theorem `Algebra.IsAlgebraic.of_injective` / 定理 `Algebra.IsAlgebraic.of_injective`

English:
theorem Algebra.IsAlgebraic.of_injective
  statement: (f : A ->ₐ[R] B) (hf : Function.Injective f)
  proof: ⟨fun _ => (isAlgebraic_algHom_iff f hf).mp (Algebra.IsAlgebraic.isAlgebraic _)⟩

中文:
定理 代数.是代数.of_injective
  结论: (f : A ->ₐ[R] B) (hf : 函数.单射 f)
  证明: ⟨fun _ => (isAlgebraic_algHom_iff f hf).mp (Algebra.IsAlgebraic.isAlgebraic _)⟩

Depends on / 依赖: Algebra, Algebra.IsAlgebraic.isAlgebraic, IsAlgebraic, isAlgebraic, isAlgebraic_algHom_iff
-/
theorem Algebra.IsAlgebraic.of_injective (f : A ->ₐ[R] B) (hf : Function.Injective f)
    [Algebra.IsAlgebraic R B] : Algebra.IsAlgebraic R A :=
  ⟨fun _ => (isAlgebraic_algHom_iff f hf).mp (Algebra.IsAlgebraic.isAlgebraic _)⟩

/--
theorem `AlgEquiv.isAlgebraic` / 定理 `AlgEquiv.isAlgebraic`

English:
theorem AlgEquiv.isAlgebraic
  statement: (e : A ≃ₐ[R] B)
  proof: Algebra.IsAlgebraic.of_injective e.symm.toAlgHom e.symm.injective

中文:
定理 代数等价.isAlgebraic
  结论: (e : A ≃ₐ[R] B)
  证明: Algebra.IsAlgebraic.of_injective e.symm.toAlgHom e.symm.injective

Depends on / 依赖: Algebra, Algebra.IsAlgebraic.of_injective, IsAlgebraic, e.symm.injective, e.symm.toAlgHom, injective, of_injective, toAlgHom
-/
theorem AlgEquiv.isAlgebraic (e : A ≃ₐ[R] B)
    [Algebra.IsAlgebraic R A] : Algebra.IsAlgebraic R B :=
  Algebra.IsAlgebraic.of_injective e.symm.toAlgHom e.symm.injective

/--
theorem `AlgEquiv.isAlgebraic_iff` / 定理 `AlgEquiv.isAlgebraic_iff`

English:
theorem AlgEquiv.isAlgebraic_iff
  given: (e : A ≃ₐ[R] B)
  proof: ⟨fun _ => e.isAlgebraic, fun _ => e.symm.isAlgebraic⟩

中文:
定理 代数等价.isAlgebraic_iff
  条件: (e : A ≃ₐ[R] B)
  证明: ⟨fun _ => e.isAlgebraic, fun _ => e.symm.isAlgebraic⟩

Depends on / 依赖: e.isAlgebraic, e.symm.isAlgebraic, isAlgebraic
-/
theorem AlgEquiv.isAlgebraic_iff (e : A ≃ₐ[R] B) :
    Algebra.IsAlgebraic R A ↔ Algebra.IsAlgebraic R B :=
  ⟨fun _ => e.isAlgebraic, fun _ => e.symm.isAlgebraic⟩

end

/--
theorem `isAlgebraic_algebraMap_iff` / 定理 `isAlgebraic_algebraMap_iff`

English:
theorem isAlgebraic_algebraMap_iff
  given: {a : S} (h : Function.Injective (algebraMap S A))
  proof: isAlgebraic_algHom_iff (IsScalarTower.toAlgHom R S A) h

中文:
定理 isAlgebraic_algebraMap_iff
  条件: {a : S} (h : 函数.单射 (algebraMap S A))
  证明: isAlgebraic_algHom_iff (IsScalarTower.toAlgHom R S A) h

Depends on / 依赖: IsScalarTower, IsScalarTower.toAlgHom, isAlgebraic_algHom_iff, toAlgHom
-/
theorem isAlgebraic_algebraMap_iff {a : S} (h : Function.Injective (algebraMap S A)) :
    IsAlgebraic R (algebraMap S A a) ↔ IsAlgebraic R a :=
  isAlgebraic_algHom_iff (IsScalarTower.toAlgHom R S A) h

/--
theorem `transcendental_algebraMap_iff` / 定理 `transcendental_algebraMap_iff`

English:
theorem transcendental_algebraMap_iff
  given: {a : S} (h : Function.Injective (algebraMap S A))
  proof: by
  simp_rw [Transcendental, isAlgebraic_algebraMap_iff h]

中文:
定理 transcendental_algebraMap_iff
  条件: {a : S} (h : 函数.单射 (algebraMap S A))
  证明: by
  simp_rw [Transcendental, isAlgebraic_algebraMap_iff h]

Depends on / 依赖: Transcendental, isAlgebraic_algebraMap_iff, simp_rw
-/
theorem transcendental_algebraMap_iff {a : S} (h : Function.Injective (algebraMap S A)) :
    Transcendental R (algebraMap S A a) ↔ Transcendental R a := by
  simp_rw [Transcendental, isAlgebraic_algebraMap_iff h]

namespace Subalgebra

/--
theorem `isAlgebraic_iff_isAlgebraic_val` / 定理 `isAlgebraic_iff_isAlgebraic_val`

English:
theorem isAlgebraic_iff_isAlgebraic_val
  given: {S : Subalgebra R A} {x : S}
  proof: (isAlgebraic_algHom_iff S.val Subtype.val_injective).symm

中文:
定理 isAlgebraic_iff_isAlgebraic_val
  条件: {S : 子代数 R A} {x : S}
  证明: (isAlgebraic_algHom_iff S.val Subtype.val_injective).symm

Depends on / 依赖: S.val, Subtype, Subtype.val_injective, isAlgebraic_algHom_iff, val_injective
-/
theorem isAlgebraic_iff_isAlgebraic_val {S : Subalgebra R A} {x : S} :
    IsAlgebraic R x ↔ IsAlgebraic R x.1 :=
  (isAlgebraic_algHom_iff S.val Subtype.val_injective).symm

/--
theorem `transcendental_iff_transcendental_val` / 定理 `transcendental_iff_transcendental_val`

English:
theorem transcendental_iff_transcendental_val
  given: {S : Subalgebra R A} {x : S}
  proof: isAlgebraic_iff_isAlgebraic_val.not

中文:
定理 transcendental_iff_transcendental_val
  条件: {S : 子代数 R A} {x : S}
  证明: isAlgebraic_iff_isAlgebraic_val.not

Depends on / 依赖: isAlgebraic_iff_isAlgebraic_val, isAlgebraic_iff_isAlgebraic_val.not
-/
theorem transcendental_iff_transcendental_val {S : Subalgebra R A} {x : S} :
    Transcendental R x ↔ Transcendental R x.1 :=
  isAlgebraic_iff_isAlgebraic_val.not

/--
theorem `isAlgebraic_of_isAlgebraic_bot` / 定理 `isAlgebraic_of_isAlgebraic_bot`

English:
theorem isAlgebraic_of_isAlgebraic_bot
  given: {x : S} (halg : IsAlgebraic (⊥ : Subalgebra R S) x)
  proof: halg.of_ringHom_of_comp_eq (algebraMap R (⊥ : Subalgebra R S))
    (RingHom.id S) (by rintro ⟨_, r, rfl⟩; exact ⟨r, rfl⟩) Function.injective_id rfl

中文:
定理 isAlgebraic_of_isAlgebraic_bot
  条件: {x : S} (halg : 是代数 (⊥ : 子代数 R S) x)
  证明: halg.of_ringHom_of_comp_eq (algebraMap R (⊥ : Subalgebra R S))
    (RingHom.id S) (by rintro ⟨_, r, rfl⟩; exact ⟨r, rfl⟩) Function.injective_id rfl

Depends on / 依赖: Function, Function.injective_id, RingHom, RingHom.id, Subalgebra, algebraMap, halg.of_ringHom_of_comp_eq, injective_id, of_ringHom_of_comp_eq
-/
theorem isAlgebraic_of_isAlgebraic_bot {x : S} (halg : IsAlgebraic (⊥ : Subalgebra R S) x) :
    IsAlgebraic R x :=
  halg.of_ringHom_of_comp_eq (algebraMap R (⊥ : Subalgebra R S))
    (RingHom.id S) (by rintro ⟨_, r, rfl⟩; exact ⟨r, rfl⟩) Function.injective_id rfl

/--
theorem `isAlgebraic_bot_iff` / 定理 `isAlgebraic_bot_iff`

English:
theorem isAlgebraic_bot_iff
  given: (h : Function.Injective (algebraMap R S)) {x : S}
  proof: isAlgebraic_ringHom_iff_of_comp_eq (Algebra.botEquivOfInjective h).symm (RingHom.id S)
    Function.injective_id rfl

中文:
定理 isAlgebraic_bot_iff
  条件: (h : 函数.单射 (algebraMap R S)) {x : S}
  证明: isAlgebraic_ringHom_iff_of_comp_eq (Algebra.botEquivOfInjective h).symm (RingHom.id S)
    Function.injective_id rfl

Depends on / 依赖: Algebra, Algebra.botEquivOfInjective, Function, Function.injective_id, RingHom, RingHom.id, botEquivOfInjective, injective_id, isAlgebraic_ringHom_iff_of_comp_eq
-/
theorem isAlgebraic_bot_iff (h : Function.Injective (algebraMap R S)) {x : S} :
    IsAlgebraic (⊥ : Subalgebra R S) x ↔ IsAlgebraic R x :=
  isAlgebraic_ringHom_iff_of_comp_eq (Algebra.botEquivOfInjective h).symm (RingHom.id S)
    Function.injective_id rfl

variable (R S) in
/--
theorem `algebra_isAlgebraic_of_algebra_isAlgebraic_bot_left` / 定理 `algebra_isAlgebraic_of_algebra_isAlgebraic_bot_left`

English:
theorem algebra_isAlgebraic_of_algebra_isAlgebraic_bot_left
  proof: Algebra.IsAlgebraic.of_ringHom_of_comp_eq (algebraMap R (⊥ : Subalgebra R S))
    (RingHom.id S) (by rintro ⟨_, r, rfl⟩; exact ⟨r, rfl⟩) Function.injective_id (by ext; rfl)

中文:
定理 algebra_isAlgebraic_of_algebra_isAlgebraic_bot_left
  证明: Algebra.IsAlgebraic.of_ringHom_of_comp_eq (algebraMap R (⊥ : Subalgebra R S))
    (RingHom.id S) (by rintro ⟨_, r, rfl⟩; exact ⟨r, rfl⟩) Function.injective_id (by ext; rfl)

Depends on / 依赖: Algebra, Algebra.IsAlgebraic.of_ringHom_of_comp_eq, Function, Function.injective_id, IsAlgebraic, RingHom, RingHom.id, Subalgebra, algebraMap, injective_id, of_ringHom_of_comp_eq
-/
theorem algebra_isAlgebraic_of_algebra_isAlgebraic_bot_left
    [Algebra.IsAlgebraic (⊥ : Subalgebra R S) S] : Algebra.IsAlgebraic R S :=
  Algebra.IsAlgebraic.of_ringHom_of_comp_eq (algebraMap R (⊥ : Subalgebra R S))
    (RingHom.id S) (by rintro ⟨_, r, rfl⟩; exact ⟨r, rfl⟩) Function.injective_id (by ext; rfl)

/--
theorem `algebra_isAlgebraic_bot_left_iff` / 定理 `algebra_isAlgebraic_bot_left_iff`

English:
theorem algebra_isAlgebraic_bot_left_iff
  given: (h : Function.Injective (algebraMap R S))
  proof: by
  simp_rw [Algebra.isAlgebraic_def, isAlgebraic_bot_iff h]

中文:
定理 algebra_isAlgebraic_bot_left_iff
  条件: (h : 函数.单射 (algebraMap R S))
  证明: by
  simp_rw [Algebra.isAlgebraic_def, isAlgebraic_bot_iff h]

Depends on / 依赖: Algebra, Algebra.isAlgebraic_def, isAlgebraic_bot_iff, isAlgebraic_def, simp_rw
-/
theorem algebra_isAlgebraic_bot_left_iff (h : Function.Injective (algebraMap R S)) :
    Algebra.IsAlgebraic (⊥ : Subalgebra R S) S ↔ Algebra.IsAlgebraic R S := by
  simp_rw [Algebra.isAlgebraic_def, isAlgebraic_bot_iff h]

/--
Instance `algebra_isAlgebraic_bot_right` / 实例 `algebra_isAlgebraic_bot_right`

English:
instance algebra_isAlgebraic_bot_right
  signature: [Nontrivial R]
  body: ⟨by rintro ⟨_, x, rfl⟩; exact isAlgebraic_algebraMap _⟩

中文:
实例 algebra_isAlgebraic_bot_right
  签名: [非平凡 R]
  定义体: ⟨by rintro ⟨_, x, rfl⟩; exact isAlgebraic_algebraMap _⟩

Depends on / 依赖: isAlgebraic_algebraMap
-/
instance algebra_isAlgebraic_bot_right [Nontrivial R] :
    Algebra.IsAlgebraic R (⊥ : Subalgebra R S) :=
  ⟨by rintro ⟨_, x, rfl⟩; exact isAlgebraic_algebraMap _⟩

end Subalgebra

/--
theorem `IsAlgebraic.of_pow` / 定理 `IsAlgebraic.of_pow`

English:
theorem IsAlgebraic.of_pow
  given: {r : A} {n : Nat} (hn : 0 < n) (ht : IsAlgebraic R (r ^ n))
  proof: have ⟨p, p_nonzero, hp⟩ := ht
  ⟨_, by rwa [expand_ne_zero hn], by rwa [expand_aeval n p r]⟩

中文:
定理 是代数.of_pow
  条件: {r : A} {n : 自然数} (hn : 0 < n) (ht : 是代数 R (r ^ n))
  证明: have ⟨p, p_nonzero, hp⟩ := ht
  ⟨_, by rwa [expand_ne_zero hn], by rwa [expand_aeval n p r]⟩

Depends on / 依赖: expand_aeval, expand_ne_zero, p_nonzero
-/
theorem IsAlgebraic.of_pow {r : A} {n : Nat} (hn : 0 < n) (ht : IsAlgebraic R (r ^ n)) :
    IsAlgebraic R r :=
  have ⟨p, p_nonzero, hp⟩ := ht
  ⟨_, by rwa [expand_ne_zero hn], by rwa [expand_aeval n p r]⟩

/--
theorem `Transcendental.pow` / 定理 `Transcendental.pow`

English:
theorem Transcendental.pow
  given: {r : A} (ht : Transcendental R r) {n : Nat} (hn : 0 < n)
  proof: fun ht' => ht ht'.of_pow hn

中文:
定理 超越.pow
  条件: {r : A} (ht : 超越 R r) {n : 自然数} (hn : 0 < n)
  证明: fun ht' => ht ht'.of_pow hn

Depends on / 依赖: of_pow
-/
theorem Transcendental.pow {r : A} (ht : Transcendental R r) {n : Nat} (hn : 0 < n) :
Transcendental R (r ^ n) := fun ht' => ht ht'.of_pow hn

/--
lemma `IsAlgebraic.invOf` / 引理 `IsAlgebraic.invOf`

English:
lemma IsAlgebraic.invOf
  given: {x : S} [Invertible x] (h : IsAlgebraic R x)
  statement: IsAlgebraic R (⅟x)
  proof: by
  obtain ⟨p, hp, hp'⟩ := h
  refine ⟨p.reverse, by simpa using hp, ?_⟩
  rwa [Polynomial.aeval_def, Polynomial.eval₂_reverse_eq_zero_iff, ← Polynomial.aeval_def]

中文:
引理 是代数.invOf
  条件: {x : S} [可逆 x] (h : 是代数 R x)
  结论: 是代数 R (⅟x)
  证明: by
  obtain ⟨p, hp, hp'⟩ := h
  refine ⟨p.reverse, by simpa using hp, ?_⟩
  rwa [Polynomial.aeval_def, Polynomial.eval₂_reverse_eq_zero_iff, ← Polynomial.aeval_def]

Depends on / 依赖: Polynomial, Polynomial.aeval_def, Polynomial.eval, aeval_def, p.reverse, reverse
-/
lemma IsAlgebraic.invOf {x : S} [Invertible x] (h : IsAlgebraic R x) : IsAlgebraic R (⅟x) := by
  obtain ⟨p, hp, hp'⟩ := h
  refine ⟨p.reverse, by simpa using hp, ?_⟩
  rwa [Polynomial.aeval_def, Polynomial.eval₂_reverse_eq_zero_iff, ← Polynomial.aeval_def]

/--
lemma `IsAlgebraic.invOf_iff` / 引理 `IsAlgebraic.invOf_iff`

English:
lemma IsAlgebraic.invOf_iff
  given: {x : S} [Invertible x]
  proof: ⟨IsAlgebraic.invOf, IsAlgebraic.invOf⟩

中文:
引理 是代数.invOf_iff
  条件: {x : S} [可逆 x]
  证明: ⟨IsAlgebraic.invOf, IsAlgebraic.invOf⟩

Depends on / 依赖: IsAlgebraic, IsAlgebraic.invOf
-/
lemma IsAlgebraic.invOf_iff {x : S} [Invertible x] :
    IsAlgebraic R (⅟x) ↔ IsAlgebraic R x :=
  ⟨IsAlgebraic.invOf, IsAlgebraic.invOf⟩

/--
lemma `IsAlgebraic.inv_iff` / 引理 `IsAlgebraic.inv_iff`

English:
lemma IsAlgebraic.inv_iff
  given: {K} [Field K] [Algebra R K] {x : K}
  proof: by
  by_cases hx : x = 0
  · simp [hx]
  let := invertibleOfNonzero hx
  exact IsAlgebraic.invOf_iff (R := R) (x := x)

alias ⟨_, IsAlgebraic.inv⟩ := IsAlgebraic.inv_iff

中文:
引理 是代数.inv_iff
  条件: {K} [域 K] [代数 R K] {x : K}
  证明: by
  by_cases hx : x = 0
  · simp [hx]
  let := invertibleOfNonzero hx
  exact IsAlgebraic.invOf_iff (R := R) (x := x)

alias ⟨_, IsAlgebraic.inv⟩ := IsAlgebraic.inv_iff

Depends on / 依赖: IsAlgebraic, IsAlgebraic.invOf_iff, invOf_iff, invertibleOfNonzero
-/
lemma IsAlgebraic.inv_iff {K} [Field K] [Algebra R K] {x : K} :
    IsAlgebraic R (x⁻¹) ↔ IsAlgebraic R x := by
  by_cases hx : x = 0
  · simp [hx]
  let := invertibleOfNonzero hx
  exact IsAlgebraic.invOf_iff (R := R) (x := x)

alias ⟨_, IsAlgebraic.inv⟩ := IsAlgebraic.inv_iff

end zero_ne_one

section

variable {K L R S A : Type*}

section Ring

section CommRing

variable [CommRing R] [CommRing S] [Ring A]
variable [Algebra R S] [Algebra S A] [Algebra R A] [IsScalarTower R S A]

/--
theorem `IsAlgebraic.extendScalars` / 定理 `IsAlgebraic.extendScalars`

English:
theorem IsAlgebraic.extendScalars
  statement: (hinj : Function.Injective (algebraMap R S)) {x : A}
  proof: let ⟨p, hp₁, hp₂⟩ := A_alg
  ⟨p.map (algebraMap _ _), by
    rwa [Ne, ← degree_eq_bot, degree_map_eq_of_injective hinj, degree_eq_bot], by simpa⟩

中文:
定理 是代数.extendScalars
  结论: (hinj : 函数.单射 (algebraMap R S)) {x : A}
  证明: let ⟨p, hp₁, hp₂⟩ := A_alg
  ⟨p.map (algebraMap _ _), by
    rwa [Ne, ← degree_eq_bot, degree_map_eq_of_injective hinj, degree_eq_bot], by simpa⟩

Depends on / 依赖: A_alg, algebraMap, degree_eq_bot, degree_map_eq_of_injective, p.map
-/
theorem IsAlgebraic.extendScalars (hinj : Function.Injective (algebraMap R S)) {x : A}
    (A_alg : IsAlgebraic R x) : IsAlgebraic S x :=
  let ⟨p, hp₁, hp₂⟩ := A_alg
  ⟨p.map (algebraMap _ _), by
    rwa [Ne, ← degree_eq_bot, degree_map_eq_of_injective hinj, degree_eq_bot], by simpa⟩

/--
theorem `IsAlgebraic.tower_top_of_subalgebra_le` / 定理 `IsAlgebraic.tower_top_of_subalgebra_le`

English:
theorem IsAlgebraic.tower_top_of_subalgebra_le
  proof: by
  let : Algebra A B := (Subalgebra.inclusion hle).toAlgebra
  have : IsScalarTower A B S := .of_algebraMap_eq fun _ => rfl
  exact h.extendScalars (Subalgebra.inclusion_injective hle)

中文:
定理 是代数.tower_top_of_subalgebra_le
  证明: by
  let : Algebra A B := (Subalgebra.inclusion hle).toAlgebra
  have : IsScalarTower A B S := .of_algebraMap_eq fun _ => rfl
  exact h.extendScalars (Subalgebra.inclusion_injective hle)

Depends on / 依赖: Algebra, IsScalarTower, Subalgebra, Subalgebra.inclusion, Subalgebra.inclusion_injective, extendScalars, h.extendScalars, inclusion, inclusion_injective, of_algebraMap_eq, toAlgebra
-/
theorem IsAlgebraic.tower_top_of_subalgebra_le
    {A B : Subalgebra R S} (hle : A <= B) {x : S}
    (h : IsAlgebraic A x) : IsAlgebraic B x := by
  let : Algebra A B := (Subalgebra.inclusion hle).toAlgebra
  have : IsScalarTower A B S := .of_algebraMap_eq fun _ => rfl
  exact h.extendScalars (Subalgebra.inclusion_injective hle)

/--
theorem `Transcendental.restrictScalars` / 定理 `Transcendental.restrictScalars`

English:
theorem Transcendental.restrictScalars
  statement: (hinj : Function.Injective (algebraMap R S)) {x : A}
  proof: fun H => h (H.extendScalars hinj)

中文:
定理 超越.restrictScalars
  结论: (hinj : 函数.单射 (algebraMap R S)) {x : A}
  证明: fun H => h (H.extendScalars hinj)

Depends on / 依赖: H.extendScalars, extendScalars
-/
theorem Transcendental.restrictScalars (hinj : Function.Injective (algebraMap R S)) {x : A}
    (h : Transcendental S x) : Transcendental R x := fun H => h (H.extendScalars hinj)

/--
theorem `Transcendental.of_tower_top_of_subalgebra_le` / 定理 `Transcendental.of_tower_top_of_subalgebra_le`

English:
theorem Transcendental.of_tower_top_of_subalgebra_le
  proof: fun H => h (H.tower_top_of_subalgebra_le hle)

中文:
定理 超越.of_tower_top_of_subalgebra_le
  证明: fun H => h (H.tower_top_of_subalgebra_le hle)

Depends on / 依赖: H.tower_top_of_subalgebra_le, tower_top_of_subalgebra_le
-/
theorem Transcendental.of_tower_top_of_subalgebra_le
    {A B : Subalgebra R S} (hle : A <= B) {x : S}
    (h : Transcendental B x) : Transcendental A x :=
  fun H => h (H.tower_top_of_subalgebra_le hle)

/--
theorem `Algebra.IsAlgebraic.extendScalars` / 定理 `Algebra.IsAlgebraic.extendScalars`

English:
theorem Algebra.IsAlgebraic.extendScalars
  statement: (hinj : Function.Injective (algebraMap R S))
  proof: ⟨fun _ => (Algebra.IsAlgebraic.isAlgebraic _).extendScalars hinj⟩

中文:
定理 代数.是代数.extendScalars
  结论: (hinj : 函数.单射 (algebraMap R S))
  证明: ⟨fun _ => (Algebra.IsAlgebraic.isAlgebraic _).extendScalars hinj⟩

Depends on / 依赖: Algebra, Algebra.IsAlgebraic.isAlgebraic, IsAlgebraic, extendScalars, isAlgebraic
-/
theorem Algebra.IsAlgebraic.extendScalars (hinj : Function.Injective (algebraMap R S))
    [Algebra.IsAlgebraic R A] : Algebra.IsAlgebraic S A :=
  ⟨fun _ => (Algebra.IsAlgebraic.isAlgebraic _).extendScalars hinj⟩

/--
theorem `Algebra.IsAlgebraic.tower_bot_of_injective` / 定理 `Algebra.IsAlgebraic.tower_bot_of_injective`

English:
theorem Algebra.IsAlgebraic.tower_bot_of_injective
  statement: [Algebra.IsAlgebraic R A]
  proof: by
    simpa [isAlgebraic_algebraMap_iff hinj] using isAlgebraic (R := R) (A := A) (algebraMap _ _ x)

中文:
定理 代数.是代数.tower_bot_of_injective
  结论: [代数.是代数 R A]
  证明: by
    simpa [isAlgebraic_algebraMap_iff hinj] using isAlgebraic (R := R) (A := A) (algebraMap _ _ x)

Depends on / 依赖: algebraMap, isAlgebraic, isAlgebraic_algebraMap_iff
-/
theorem Algebra.IsAlgebraic.tower_bot_of_injective [Algebra.IsAlgebraic R A]
    (hinj : Function.Injective (algebraMap S A)) :
    Algebra.IsAlgebraic R S where
  isAlgebraic x := by
    simpa [isAlgebraic_algebraMap_iff hinj] using isAlgebraic (R := R) (A := A) (algebraMap _ _ x)

end CommRing

section Field

variable [Field K] [Field L] [Ring A]
variable [Algebra K L] [Algebra L A] [Algebra K A] [IsScalarTower K L A]
variable (L)

/-- If `x` is algebraic over `K`, then `x` is algebraic over `L` when `L` is an extension of `K` -/
@[stacks 09GF "part one"]
/--
theorem `IsAlgebraic.tower_top` / 定理 `IsAlgebraic.tower_top`

English:
theorem IsAlgebraic.tower_top
  given: {x : A} (A_alg : IsAlgebraic K x)
  proof: A_alg.extendScalars (algebraMap K L).injective

中文:
定理 是代数.tower_top
  条件: {x : A} (A_alg : 是代数 K x)
  证明: A_alg.extendScalars (algebraMap K L).injective

Depends on / 依赖: A_alg, A_alg.extendScalars, algebraMap, extendScalars, injective
-/
theorem IsAlgebraic.tower_top {x : A} (A_alg : IsAlgebraic K x) :
    IsAlgebraic L x :=
  A_alg.extendScalars (algebraMap K L).injective

variable {L} (K) in
/--
theorem `Transcendental.of_tower_top` / 定理 `Transcendental.of_tower_top`

English:
theorem Transcendental.of_tower_top
  given: {x : A} (h : Transcendental L x)
  proof: fun H => h (H.tower_top L)

中文:
定理 超越.of_tower_top
  条件: {x : A} (h : 超越 L x)
  证明: fun H => h (H.tower_top L)

Depends on / 依赖: H.tower_top, tower_top
-/
theorem Transcendental.of_tower_top {x : A} (h : Transcendental L x) :
    Transcendental K x := fun H => h (H.tower_top L)

/-- If A is an algebraic algebra over K, then A is algebraic over L when L is an extension of K -/
@[stacks 09GF "part two"]
/--
theorem `Algebra.IsAlgebraic.tower_top` / 定理 `Algebra.IsAlgebraic.tower_top`

English:
theorem Algebra.IsAlgebraic.tower_top
  given: [Algebra.IsAlgebraic K A]
  statement: Algebra.IsAlgebraic L A
  proof: Algebra.IsAlgebraic.extendScalars (algebraMap K L).injective

中文:
定理 代数.是代数.tower_top
  条件: [代数.是代数 K A]
  结论: 代数.是代数 L A
  证明: Algebra.IsAlgebraic.extendScalars (algebraMap K L).injective

Depends on / 依赖: Algebra, Algebra.IsAlgebraic.extendScalars, IsAlgebraic, algebraMap, extendScalars, injective
-/
theorem Algebra.IsAlgebraic.tower_top [Algebra.IsAlgebraic K A] : Algebra.IsAlgebraic L A :=
  Algebra.IsAlgebraic.extendScalars (algebraMap K L).injective

variable (K) (A)

/--
theorem `Algebra.IsAlgebraic.tower_bot` / 定理 `Algebra.IsAlgebraic.tower_bot`

English:
theorem Algebra.IsAlgebraic.tower_bot
  statement: (K L A : Type*) [CommRing K] [Field L] [Ring A]
  proof: tower_bot_of_injective (algebraMap L A).injective

中文:
定理 代数.是代数.tower_bot
  结论: (K L A : 类型) [交换环 K] [域 L] [环 A]
  证明: tower_bot_of_injective (algebraMap L A).injective

Depends on / 依赖: algebraMap, injective, tower_bot_of_injective
-/
theorem Algebra.IsAlgebraic.tower_bot (K L A : Type*) [CommRing K] [Field L] [Ring A]
    [Algebra K L] [Algebra L A] [Algebra K A] [IsScalarTower K L A]
    [Nontrivial A] [Algebra.IsAlgebraic K A] :
    Algebra.IsAlgebraic K L :=
  tower_bot_of_injective (algebraMap L A).injective

end Field

end Ring

section IsTorsionFree

namespace Algebra.IsAlgebraic

variable [CommRing K] [IsDomain K] [Field L] [Algebra K L]

/--
theorem `algHom_bijective` / 定理 `algHom_bijective`

English:
theorem algHom_bijective
  given: [IsTorsionFree K L] [Algebra.IsAlgebraic K L] (f : L ->ₐ[K] L)
  proof: by
  refine ⟨f.injective, fun b => ?_⟩
  obtain ⟨p, hp, he⟩ := Algebra.IsAlgebraic.isAlgebraic (R := K) b
  let f' : p.rootSet L -> p.rootSet L := (rootSet_maps_to' (fun x => x) f).restrict f _ _
  have : f'.Surjective := Finite.injective_iff_surjective.1
fun _ _ h => Subtype.ext f.injective Subtype.ext_iff.1 h
  obtain ⟨a, ha⟩ := this ⟨b, mem_rootSet.2 ⟨hp, he⟩⟩
  exact ⟨a, Subtype.ext_iff.1 ha⟩

中文:
定理 algHom_bijective
  条件: [是无挠 K L] [代数.是代数 K L] (f : L ->ₐ[K] L)
  证明: by
  refine ⟨f.injective, fun b => ?_⟩
  obtain ⟨p, hp, he⟩ := Algebra.IsAlgebraic.isAlgebraic (R := K) b
  let f' : p.rootSet L -> p.rootSet L := (rootSet_maps_to' (fun x => x) f).restrict f _ _
  have : f'.Surjective := Finite.injective_iff_surjective.1
fun _ _ h => Subtype.ext f.injective Subtype.ext_iff.1 h
  obtain ⟨a, ha⟩ := this ⟨b, mem_rootSet.2 ⟨hp, he⟩⟩
  exact ⟨a, Subtype.ext_iff.1 ha⟩

Depends on / 依赖: Algebra, Algebra.IsAlgebraic.isAlgebraic, Finite, Finite.injective_iff_surjective, IsAlgebraic, Subtype, Subtype.ext, Subtype.ext_iff, Surjective, ext_iff, f.injective, injective, injective_iff_surjective, isAlgebraic, mem_rootSet, p.rootSet, restrict, rootSet, rootSet_maps_to
-/
theorem algHom_bijective [IsTorsionFree K L] [Algebra.IsAlgebraic K L] (f : L ->ₐ[K] L) :
    Function.Bijective f := by
  refine ⟨f.injective, fun b => ?_⟩
  obtain ⟨p, hp, he⟩ := Algebra.IsAlgebraic.isAlgebraic (R := K) b
  let f' : p.rootSet L -> p.rootSet L := (rootSet_maps_to' (fun x => x) f).restrict f _ _
  have : f'.Surjective := Finite.injective_iff_surjective.1
fun _ _ h => Subtype.ext f.injective Subtype.ext_iff.1 h
  obtain ⟨a, ha⟩ := this ⟨b, mem_rootSet.2 ⟨hp, he⟩⟩
  exact ⟨a, Subtype.ext_iff.1 ha⟩

/--
theorem `algHom_bijective₂` / 定理 `algHom_bijective₂`

English:
theorem algHom_bijective₂
  statement: [IsTorsionFree K L] [DivisionRing R] [Algebra K R]
  proof: (g.injective.bijective₂_of_surjective f.injective (algHom_bijective <| g.comp f).2).symm

中文:
定理 algHom_bijective₂
  结论: [是无挠 K L] [除环 R] [代数 K R]
  证明: (g.injective.bijective₂_of_surjective f.injective (algHom_bijective <| g.comp f).2).symm

Depends on / 依赖: algHom_bijective, f.injective, g.comp, g.injective.bijective, injective
-/
theorem algHom_bijective₂ [IsTorsionFree K L] [DivisionRing R] [Algebra K R]
    [Algebra.IsAlgebraic K L] (f : L ->ₐ[K] R) (g : R ->ₐ[K] L) :
    Function.Bijective f ∧ Function.Bijective g :=
  (g.injective.bijective₂_of_surjective f.injective (algHom_bijective <| g.comp f).2).symm

/--
theorem `bijective_of_isScalarTower` / 定理 `bijective_of_isScalarTower`

English:
theorem bijective_of_isScalarTower
  statement: [IsTorsionFree K L] [Algebra.IsAlgebraic K L]
  proof: (algHom_bijective₂ (IsScalarTower.toAlgHom K L R) f).2

中文:
定理 bijective_of_isScalarTower
  结论: [是无挠 K L] [代数.是代数 K L]
  证明: (algHom_bijective₂ (IsScalarTower.toAlgHom K L R) f).2

Depends on / 依赖: IsScalarTower, IsScalarTower.toAlgHom, toAlgHom
-/
theorem bijective_of_isScalarTower [IsTorsionFree K L] [Algebra.IsAlgebraic K L]
    [DivisionRing R] [Algebra K R] [Algebra L R] [IsScalarTower K L R] (f : R ->ₐ[K] L) :
    Function.Bijective f :=
  (algHom_bijective₂ (IsScalarTower.toAlgHom K L R) f).2

/--
theorem `bijective_of_isScalarTower'` / 定理 `bijective_of_isScalarTower'`

English:
theorem bijective_of_isScalarTower'
  statement: [Field R] [Algebra K R]
  proof: (algHom_bijective₂ f (IsScalarTower.toAlgHom K L R)).1

中文:
定理 bijective_of_isScalarTower'
  结论: [域 R] [代数 K R]
  证明: (algHom_bijective₂ f (IsScalarTower.toAlgHom K L R)).1

Depends on / 依赖: IsScalarTower, IsScalarTower.toAlgHom, toAlgHom
-/
theorem bijective_of_isScalarTower' [Field R] [Algebra K R]
    [IsTorsionFree K R]
    [Algebra.IsAlgebraic K R] [Algebra L R] [IsScalarTower K L R] (f : R ->ₐ[K] L) :
    Function.Bijective f :=
  (algHom_bijective₂ f (IsScalarTower.toAlgHom K L R)).1

variable (K L)

/-- Bijection between algebra equivalences and algebra homomorphisms -/
@[simps]
/--
Definition of `algEquivEquivAlgHom` / `algEquivEquivAlgHom` 的定义

English:
definition algEquivEquivAlgHom
  signature: [IsTorsionFree K L] [Algebra.IsAlgebraic K L]
  body: ϕ.toAlgHom
  invFun ϕ := AlgEquiv.ofBijective ϕ (algHom_bijective ϕ)
  map_mul' _ _ := rfl

中文:
定义 algEquivEquivAlgHom
  签名: [是无挠 K L] [代数.是代数 K L]
  定义体: ϕ.toAlgHom
  invFun ϕ := AlgEquiv.ofBijective ϕ (algHom_bijective ϕ)
  map_mul' _ _ := rfl

Depends on / 依赖: toAlgHom
-/
noncomputable def algEquivEquivAlgHom [IsTorsionFree K L] [Algebra.IsAlgebraic K L] :
    (L ≃ₐ[K] L) ≃* (L ->ₐ[K] L) where
  toFun ϕ := ϕ.toAlgHom
  invFun ϕ := AlgEquiv.ofBijective ϕ (algHom_bijective ϕ)
  map_mul' _ _ := rfl

end Algebra.IsAlgebraic

end IsTorsionFree

end

section

variable {R S : Type*} [CommRing R]

section

open Algebra

variable [Ring S] [Algebra R S]

/--
theorem `IsAlgebraic.exists_nonzero_coeff_and_aeval_eq_zero` / 定理 `IsAlgebraic.exists_nonzero_coeff_and_aeval_eq_zero`

English:
theorem IsAlgebraic.exists_nonzero_coeff_and_aeval_eq_zero
  proof: by
  obtain ⟨p, hp0, hp⟩ := hRs
  obtain ⟨q, hpq, hq⟩ := exists_eq_pow_rootMultiplicity_mul_and_not_dvd p hp0 0
  simp only [C_0, sub_zero, X_pow_mul, X_dvd_iff] at hpq hq
  rw [hpq]; rw [map_mul]; rw [aeval_X_pow] at hp
  exact ⟨q, hq, (S⁰.pow_mem hs (rootMultiplicity 0 p)).2 (aeval s q) hp⟩

中文:
定理 是代数.存在_nonzero_coeff_and_aeval_eq_zero
  证明: by
  obtain ⟨p, hp0, hp⟩ := hRs
  obtain ⟨q, hpq, hq⟩ := exists_eq_pow_rootMultiplicity_mul_and_not_dvd p hp0 0
  simp only [C_0, sub_zero, X_pow_mul, X_dvd_iff] at hpq hq
  rw [hpq]; rw [map_mul]; rw [aeval_X_pow] at hp
  exact ⟨q, hq, (S⁰.pow_mem hs (rootMultiplicity 0 p)).2 (aeval s q) hp⟩

Depends on / 依赖: X_dvd_iff, X_pow_mul, aeval_X_pow, exists_eq_pow_rootMultiplicity_mul_and_not_dvd, map_mul, pow_mem, rootMultiplicity, sub_zero
-/
theorem IsAlgebraic.exists_nonzero_coeff_and_aeval_eq_zero
    {s : S} (hRs : IsAlgebraic R s) (hs : s in S⁰) :
    exists q : R[X], q.coeff 0 != 0 ∧ aeval s q = 0 := by
  obtain ⟨p, hp0, hp⟩ := hRs
  obtain ⟨q, hpq, hq⟩ := exists_eq_pow_rootMultiplicity_mul_and_not_dvd p hp0 0
  simp only [C_0, sub_zero, X_pow_mul, X_dvd_iff] at hpq hq
  rw [hpq]; rw [map_mul]; rw [aeval_X_pow] at hp
  exact ⟨q, hq, (S⁰.pow_mem hs (rootMultiplicity 0 p)).2 (aeval s q) hp⟩

/--
theorem `IsAlgebraic.exists_nonzero_eq_adjoin_mul` / 定理 `IsAlgebraic.exists_nonzero_eq_adjoin_mul`

English:
theorem IsAlgebraic.exists_nonzero_eq_adjoin_mul
  given: {s : S} (hRs : IsAlgebraic R s) (hs : s in S⁰)
  proof: by
  have ⟨q, hq0, hq⟩ := hRs.exists_nonzero_coeff_and_aeval_eq_zero hs
  have ⟨p, hp⟩ := X_dvd_sub_C (p := q)
  refine ⟨aeval s p, aeval_mem_adjoin_singleton _ _, _, neg_ne_zero.mpr hq0, ?_⟩
  apply_fun aeval s at hp
  rwa [map_sub, hq, zero_sub, map_mul, aeval_X, aeval_C, ← map_neg, eq_comm] at hp

中文:
定理 是代数.存在_nonzero_eq_adjoin_mul
  条件: {s : S} (hRs : 是代数 R s) (hs : s in S⁰)
  证明: by
  have ⟨q, hq0, hq⟩ := hRs.exists_nonzero_coeff_and_aeval_eq_zero hs
  have ⟨p, hp⟩ := X_dvd_sub_C (p := q)
  refine ⟨aeval s p, aeval_mem_adjoin_singleton _ _, _, neg_ne_zero.mpr hq0, ?_⟩
  apply_fun aeval s at hp
  rwa [map_sub, hq, zero_sub, map_mul, aeval_X, aeval_C, ← map_neg, eq_comm] at hp

Depends on / 依赖: X_dvd_sub_C, aeval_C, aeval_X, aeval_mem_adjoin_singleton, apply_fun, eq_comm, exists_nonzero_coeff_and_aeval_eq_zero, hRs.exists_nonzero_coeff_and_aeval_eq_zero, map_mul, map_neg, map_sub, neg_ne_zero, neg_ne_zero.mpr, zero_sub
-/
theorem IsAlgebraic.exists_nonzero_eq_adjoin_mul {s : S} (hRs : IsAlgebraic R s) (hs : s in S⁰) :
    existsᵉ (t in R[s]) (r != (0 : R)), s * t = algebraMap R S r := by
  have ⟨q, hq0, hq⟩ := hRs.exists_nonzero_coeff_and_aeval_eq_zero hs
  have ⟨p, hp⟩ := X_dvd_sub_C (p := q)
  refine ⟨aeval s p, aeval_mem_adjoin_singleton _ _, _, neg_ne_zero.mpr hq0, ?_⟩
  apply_fun aeval s at hp
  rwa [map_sub, hq, zero_sub, map_mul, aeval_X, aeval_C, ← map_neg, eq_comm] at hp

/--
theorem `IsAlgebraic.exists_nonzero_dvd` / 定理 `IsAlgebraic.exists_nonzero_dvd`

English:
theorem IsAlgebraic.exists_nonzero_dvd
  given: {s : S} (hRs : IsAlgebraic R s) (hs : s in S⁰)
  proof: by
  obtain ⟨q, hq0, hq⟩ := hRs.exists_nonzero_coeff_and_aeval_eq_zero hs
  have key := map_dvd (aeval s) (X_dvd_sub_C (p := q))
  rw [map_sub]; rw [hq]; rw [zero_sub]; rw [dvd_neg]; rw [aeval_X]; rw [aeval_C] at key
  exact ⟨q.coeff 0, hq0, key⟩

中文:
定理 是代数.存在_nonzero_dvd
  条件: {s : S} (hRs : 是代数 R s) (hs : s in S⁰)
  证明: by
  obtain ⟨q, hq0, hq⟩ := hRs.exists_nonzero_coeff_and_aeval_eq_zero hs
  have key := map_dvd (aeval s) (X_dvd_sub_C (p := q))
  rw [map_sub]; rw [hq]; rw [zero_sub]; rw [dvd_neg]; rw [aeval_X]; rw [aeval_C] at key
  exact ⟨q.coeff 0, hq0, key⟩

Depends on / 依赖: X_dvd_sub_C, aeval_C, aeval_X, dvd_neg, exists_nonzero_coeff_and_aeval_eq_zero, hRs.exists_nonzero_coeff_and_aeval_eq_zero, map_dvd, map_sub, q.coeff, zero_sub
-/
theorem IsAlgebraic.exists_nonzero_dvd {s : S} (hRs : IsAlgebraic R s) (hs : s in S⁰) :
    exists r : R, r != 0 ∧ s ∣ algebraMap R S r := by
  obtain ⟨q, hq0, hq⟩ := hRs.exists_nonzero_coeff_and_aeval_eq_zero hs
  have key := map_dvd (aeval s) (X_dvd_sub_C (p := q))
  rw [map_sub]; rw [hq]; rw [zero_sub]; rw [dvd_neg]; rw [aeval_X]; rw [aeval_C] at key
  exact ⟨q.coeff 0, hq0, key⟩

/--
theorem `IsAlgebraic.exists_smul_eq_mul` / 定理 `IsAlgebraic.exists_smul_eq_mul`

English:
theorem IsAlgebraic.exists_smul_eq_mul
  proof: have ⟨r, hr, s, h⟩ := hRb.exists_nonzero_dvd hb
  ⟨s * a, r, hr, by rw [smul_def, h, mul_assoc]⟩

中文:
定理 是代数.存在_smul_eq_mul
  证明: have ⟨r, hr, s, h⟩ := hRb.exists_nonzero_dvd hb
  ⟨s * a, r, hr, by rw [smul_def, h, mul_assoc]⟩

Depends on / 依赖: exists_nonzero_dvd, hRb.exists_nonzero_dvd, mul_assoc, smul_def
-/
theorem IsAlgebraic.exists_smul_eq_mul
    (a : S) {b : S} (hRb : IsAlgebraic R b) (hb : b in S⁰) :
    existsᵉ (c : S) (d != (0 : R)), d • a = b * c :=
  have ⟨r, hr, s, h⟩ := hRb.exists_nonzero_dvd hb
  ⟨s * a, r, hr, by rw [smul_def, h, mul_assoc]⟩

variable (R)

/--
theorem `Algebra.IsAlgebraic.exists_smul_eq_mul` / 定理 `Algebra.IsAlgebraic.exists_smul_eq_mul`

English:
theorem Algebra.IsAlgebraic.exists_smul_eq_mul
  statement: [NoZeroDivisors S] [Algebra.IsAlgebraic R S]
  proof: (isAlgebraic b).exists_smul_eq_mul a (mem_nonZeroDivisors_of_ne_zero hb)

中文:
定理 代数.是代数.存在_smul_eq_mul
  结论: [无零因子 S] [代数.是代数 R S]
  证明: (isAlgebraic b).exists_smul_eq_mul a (mem_nonZeroDivisors_of_ne_zero hb)

Depends on / 依赖: exists_smul_eq_mul, isAlgebraic, mem_nonZeroDivisors_of_ne_zero
-/
theorem Algebra.IsAlgebraic.exists_smul_eq_mul [NoZeroDivisors S] [Algebra.IsAlgebraic R S]
    (a : S) {b : S} (hb : b != 0) :
    existsᵉ (c : S) (d != (0 : R)), d • a = b * c :=
  (isAlgebraic b).exists_smul_eq_mul a (mem_nonZeroDivisors_of_ne_zero hb)

namespace Polynomial

/--
Definition of `algEquivOfTranscendental` / `algEquivOfTranscendental` 的定义

English:
definition algEquivOfTranscendental
  signature: (s : S) (h : Transcendental R s)
  body: AlgEquiv.ofBijective (aeval ⟨s, self_mem_adjoin_singleton R s⟩) by
    refine ⟨transcendental_iff_injective.mp ?_, ?_⟩
    · rwa [Subalgebra.transcendental_iff_transcendental_val]
    rw [← AlgHom.range_eq_top]; rw [_root_.eq_top_iff]
    rintro ⟨t, ht⟩ _
    obtain ⟨r, rfl⟩ := adjoin_mem_exists_aeval _ _ ht
    exact ⟨r, by ext; simp⟩

@[simp]

中文:
定义 algEquivOfTranscendental
  签名: (s : S) (h : 超越 R s)
  定义体: AlgEquiv.ofBijective (aeval ⟨s, self_mem_adjoin_singleton R s⟩) by
    refine ⟨transcendental_iff_injective.mp ?_, ?_⟩
    · rwa [Subalgebra.transcendental_iff_transcendental_val]
    rw [← AlgHom.range_eq_top]; rw [_root_.eq_top_iff]
    rintro ⟨t, ht⟩ _
    obtain ⟨r, rfl⟩ := adjoin_mem_exists_aeval _ _ ht
    exact ⟨r, by ext; simp⟩

@[simp]

Depends on / 依赖: AlgEquiv, AlgEquiv.ofBijective, AlgHom, AlgHom.range_eq_top, Subalgebra, Subalgebra.transcendental_iff_transcendental_val, _root_, _root_.eq_top_iff, adjoin_mem_exists_aeval, eq_top_iff, ofBijective, range_eq_top, self_mem_adjoin_singleton, transcendental_iff_injective, transcendental_iff_injective.mp, transcendental_iff_transcendental_val
-/
noncomputable def algEquivOfTranscendental (s : S) (h : Transcendental R s) :
    R[X] ≃ₐ[R] R[s] :=
AlgEquiv.ofBijective (aeval ⟨s, self_mem_adjoin_singleton R s⟩) by
    refine ⟨transcendental_iff_injective.mp ?_, ?_⟩
    · rwa [Subalgebra.transcendental_iff_transcendental_val]
    rw [← AlgHom.range_eq_top]; rw [_root_.eq_top_iff]
    rintro ⟨t, ht⟩ _
    obtain ⟨r, rfl⟩ := adjoin_mem_exists_aeval _ _ ht
    exact ⟨r, by ext; simp⟩

@[simp]
/--
theorem `algEquivOfTranscendental_coe` / 定理 `algEquivOfTranscendental_coe`

English:
theorem algEquivOfTranscendental_coe
  given: (s : S) (h : Transcendental R s)
  proof: rfl

@[simp]

中文:
定理 algEquivOfTranscendental_coe
  条件: (s : S) (h : 超越 R s)
  证明: rfl

@[simp]

Depends on / 依赖: self_mem_adjoin_singleton
-/
theorem algEquivOfTranscendental_coe (s : S) (h : Transcendental R s) :
    (algEquivOfTranscendental R s h : R[X] ->+* R[s]) =
    aeval (R := R) (A := R[s]) ⟨s, self_mem_adjoin_singleton R s⟩ := rfl

@[simp]
/--
theorem `algEquivOfTranscendental_apply` / 定理 `algEquivOfTranscendental_apply`

English:
theorem algEquivOfTranscendental_apply
  given: (s : S) (h : Transcendental R s) (f : R[X])
  proof: rfl

中文:
定理 algEquivOfTranscendental_apply
  条件: (s : S) (h : 超越 R s) (f : R[X])
  证明: rfl
-/
theorem algEquivOfTranscendental_apply (s : S) (h : Transcendental R s) (f : R[X]) :
    algEquivOfTranscendental R s h f = aeval (⟨s, self_mem_adjoin_singleton R s⟩) f := rfl

/--
lemma `algEquivOfTranscendental_apply_X` / 引理 `algEquivOfTranscendental_apply_X`

English:
lemma algEquivOfTranscendental_apply_X
  given: (s : S) (h : Transcendental R s)
  proof: by simp

@[simp]

中文:
引理 algEquivOfTranscendental_apply_X
  条件: (s : S) (h : 超越 R s)
  证明: by simp

@[simp]
-/
lemma algEquivOfTranscendental_apply_X (s : S) (h : Transcendental R s) :
    algEquivOfTranscendental R s h X = ⟨s, self_mem_adjoin_singleton R s⟩ := by simp

@[simp]
/--
theorem `algEquivOfTranscendental_symm_aeval` / 定理 `algEquivOfTranscendental_symm_aeval`

English:
theorem algEquivOfTranscendental_symm_aeval
  given: (s : S) (h : Transcendental R s) (f : R[X])
  proof: by
  apply (algEquivOfTranscendental R s h).toEquiv.injective
  simp

@[simp]

中文:
定理 algEquivOfTranscendental_symm_aeval
  条件: (s : S) (h : 超越 R s) (f : R[X])
  证明: by
  apply (algEquivOfTranscendental R s h).toEquiv.injective
  simp

@[simp]

Depends on / 依赖: algEquivOfTranscendental, injective, toEquiv, toEquiv.injective
-/
theorem algEquivOfTranscendental_symm_aeval (s : S) (h : Transcendental R s) (f : R[X]) :
    (algEquivOfTranscendental R s h).symm
      (aeval (⟨s, self_mem_adjoin_singleton R s⟩) f) = f := by
  apply (algEquivOfTranscendental R s h).toEquiv.injective
  simp

@[simp]
/--
theorem `algEquivOfTranscendental_symm_gen` / 定理 `algEquivOfTranscendental_symm_gen`

English:
theorem algEquivOfTranscendental_symm_gen
  given: (s : S) (h : Transcendental R s)
  proof: by
  apply (algEquivOfTranscendental R s h).toEquiv.injective
  simp

中文:
定理 algEquivOfTranscendental_symm_gen
  条件: (s : S) (h : 超越 R s)
  证明: by
  apply (algEquivOfTranscendental R s h).toEquiv.injective
  simp

Depends on / 依赖: algEquivOfTranscendental, injective, toEquiv, toEquiv.injective
-/
theorem algEquivOfTranscendental_symm_gen (s : S) (h : Transcendental R s) :
    (algEquivOfTranscendental R s h).symm ⟨s, self_mem_adjoin_singleton R s⟩ = X := by
  apply (algEquivOfTranscendental R s h).toEquiv.injective
  simp

end Polynomial

/--
theorem `Transcendental.uniqueFactorizationMonoid_adjoin` / 定理 `Transcendental.uniqueFactorizationMonoid_adjoin`

English:
theorem Transcendental.uniqueFactorizationMonoid_adjoin
  statement: [UniqueFactorizationMonoid R] {s : S}
  proof: (algEquivOfTranscendental R s h).toMulEquiv.uniqueFactorizationMonoid inferInstance

中文:
定理 超越.uniqueFactorizationMonoid_adjoin
  结论: [唯一分解幺半群 R] {s : S}
  证明: (algEquivOfTranscendental R s h).toMulEquiv.uniqueFactorizationMonoid inferInstance

Depends on / 依赖: algEquivOfTranscendental, toMulEquiv, toMulEquiv.uniqueFactorizationMonoid, uniqueFactorizationMonoid
-/
theorem Transcendental.uniqueFactorizationMonoid_adjoin [UniqueFactorizationMonoid R] {s : S}
      (h : Transcendental R s) : UniqueFactorizationMonoid (R[s]) :=
  (algEquivOfTranscendental R s h).toMulEquiv.uniqueFactorizationMonoid inferInstance

end

namespace Algebra.IsAlgebraic

variable (S) {A : Type*} [CommRing S] [NoZeroDivisors S] [Algebra R S]
  [alg : Algebra.IsAlgebraic R S] [Ring A] [Algebra R A] [Algebra S A] [IsScalarTower R S A]

open Function (Injective) in
/--
theorem `injective_tower_top` / 定理 `injective_tower_top`

English:
theorem injective_tower_top
  given: (inj : Injective (algebraMap R A))
  statement: Injective (algebraMap S A)
  proof: by
  refine (injective_iff_map_eq_zero _).mpr fun s eq => of_not_not fun ne => ?_
  have ⟨r, ne, dvd⟩ := (alg.1 s).exists_nonzero_dvd (mem_nonZeroDivisors_of_ne_zero ne)
  refine ne (inj <| map_zero (algebraMap R A) ▸ zero_dvd_iff.mp ?_)
  simp_rw [← eq, IsScalarTower.algebraMap_apply R S A, map_dvd (algebraMap S A) dvd]

中文:
定理 injective_tower_top
  条件: (inj : 单射 (algebraMap R A))
  结论: 单射 (algebraMap S A)
  证明: by
  refine (injective_iff_map_eq_zero _).mpr fun s eq => of_not_not fun ne => ?_
  have ⟨r, ne, dvd⟩ := (alg.1 s).exists_nonzero_dvd (mem_nonZeroDivisors_of_ne_zero ne)
  refine ne (inj <| map_zero (algebraMap R A) ▸ zero_dvd_iff.mp ?_)
  simp_rw [← eq, IsScalarTower.algebraMap_apply R S A, map_dvd (algebraMap S A) dvd]

Depends on / 依赖: IsScalarTower, IsScalarTower.algebraMap_apply, algebraMap, algebraMap_apply, exists_nonzero_dvd, injective_iff_map_eq_zero, map_dvd, map_zero, mem_nonZeroDivisors_of_ne_zero, of_not_not, simp_rw, zero_dvd_iff, zero_dvd_iff.mp
-/
theorem injective_tower_top (inj : Injective (algebraMap R A)) : Injective (algebraMap S A) := by
  refine (injective_iff_map_eq_zero _).mpr fun s eq => of_not_not fun ne => ?_
  have ⟨r, ne, dvd⟩ := (alg.1 s).exists_nonzero_dvd (mem_nonZeroDivisors_of_ne_zero ne)
  refine ne (inj <| map_zero (algebraMap R A) ▸ zero_dvd_iff.mp ?_)
  simp_rw [← eq, IsScalarTower.algebraMap_apply R S A, map_dvd (algebraMap S A) dvd]

variable (R A)

/--
theorem `faithfulSMul_tower_top` / 定理 `faithfulSMul_tower_top`

English:
theorem faithfulSMul_tower_top
  given: [FaithfulSMul R A]
  statement: FaithfulSMul S A
  proof: by
  rw [faithfulSMul_iff_algebraMap_injective] at *
  exact injective_tower_top S ‹_›

中文:
定理 faithfulSMul_tower_top
  条件: [忠实标量乘法 R A]
  结论: 忠实标量乘法 S A
  证明: by
  rw [faithfulSMul_iff_algebraMap_injective] at *
  exact injective_tower_top S ‹_›

Depends on / 依赖: faithfulSMul_iff_algebraMap_injective, injective_tower_top
-/
theorem faithfulSMul_tower_top [FaithfulSMul R A] : FaithfulSMul S A := by
  rw [faithfulSMul_iff_algebraMap_injective] at *
  exact injective_tower_top S ‹_›

end Algebra.IsAlgebraic

end

section Field

variable {K L : Type*} [Field K] [Field L] [Algebra K L] (A : Subalgebra K L)

/--
theorem `inv_eq_of_aeval_divX_ne_zero` / 定理 `inv_eq_of_aeval_divX_ne_zero`

English:
theorem inv_eq_of_aeval_divX_ne_zero
  given: {x : L} {p : K[X]} (aeval_ne : aeval x (divX p) != 0)
  proof: by
  rw [inv_eq_iff_eq_inv]; rw [inv_div]; rw [eq_comm]; rw [div_eq_iff]; rw [sub_eq_iff_eq_add]; rw [mul_comm]
  conv_lhs => rw [← divX_mul_X_add p]
  · rw [map_add, map_mul, aeval_X, aeval_C]
  · exact aeval_ne

中文:
定理 inv_eq_of_aeval_divX_ne_zero
  条件: {x : L} {p : K[X]} (aeval_ne : aeval x (divX p) != 0)
  证明: by
  rw [inv_eq_iff_eq_inv]; rw [inv_div]; rw [eq_comm]; rw [div_eq_iff]; rw [sub_eq_iff_eq_add]; rw [mul_comm]
  conv_lhs => rw [← divX_mul_X_add p]
  · rw [map_add, map_mul, aeval_X, aeval_C]
  · exact aeval_ne

Depends on / 依赖: aeval_C, aeval_X, aeval_ne, conv_lhs, divX_mul_X_add, div_eq_iff, eq_comm, inv_div, inv_eq_iff_eq_inv, map_add, map_mul, mul_comm, sub_eq_iff_eq_add
-/
theorem inv_eq_of_aeval_divX_ne_zero {x : L} {p : K[X]} (aeval_ne : aeval x (divX p) != 0) :
    x⁻¹ = aeval x (divX p) / (aeval x p - algebraMap _ _ (p.coeff 0)) := by
  rw [inv_eq_iff_eq_inv]; rw [inv_div]; rw [eq_comm]; rw [div_eq_iff]; rw [sub_eq_iff_eq_add]; rw [mul_comm]
  conv_lhs => rw [← divX_mul_X_add p]
  · rw [map_add, map_mul, aeval_X, aeval_C]
  · exact aeval_ne

/--
theorem `inv_eq_of_root_of_coeff_zero_ne_zero` / 定理 `inv_eq_of_root_of_coeff_zero_ne_zero`

English:
theorem inv_eq_of_root_of_coeff_zero_ne_zero
  statement: {x : L} {p : K[X]} (aeval_eq : aeval x p = 0)
  proof: by
  convert!
    inv_eq_of_aeval_divX_ne_zero (p := p) (L := L)
      (mt (fun h => (algebraMap K L).injective ?_) coeff_zero_ne) using 1
  · rw [aeval_eq, zero_sub, div_neg]
  rw [RingHom.map_zero]
  convert! aeval_eq
  conv_rhs => rw [← divX_mul_X_add p]
  rw [map_add]; rw [map_mul]; rw [h]; rw [zero_mul]; rw [zero_add]; rw [aeval_C]

中文:
定理 inv_eq_of_root_of_coeff_zero_ne_zero
  结论: {x : L} {p : K[X]} (aeval_eq : aeval x p = 0)
  证明: by
  convert!
    inv_eq_of_aeval_divX_ne_zero (p := p) (L := L)
      (mt (fun h => (algebraMap K L).injective ?_) coeff_zero_ne) using 1
  · rw [aeval_eq, zero_sub, div_neg]
  rw [RingHom.map_zero]
  convert! aeval_eq
  conv_rhs => rw [← divX_mul_X_add p]
  rw [map_add]; rw [map_mul]; rw [h]; rw [zero_mul]; rw [zero_add]; rw [aeval_C]

Depends on / 依赖: RingHom, RingHom.map_zero, aeval_C, aeval_eq, algebraMap, coeff_zero_ne, conv_rhs, convert, divX_mul_X_add, div_neg, injective, inv_eq_of_aeval_divX_ne_zero, map_add, map_mul, map_zero, zero_add, zero_mul, zero_sub
-/
theorem inv_eq_of_root_of_coeff_zero_ne_zero {x : L} {p : K[X]} (aeval_eq : aeval x p = 0)
    (coeff_zero_ne : p.coeff 0 != 0) : x⁻¹ = -(aeval x (divX p) / algebraMap _ _ (p.coeff 0)) := by
  convert!
    inv_eq_of_aeval_divX_ne_zero (p := p) (L := L)
      (mt (fun h => (algebraMap K L).injective ?_) coeff_zero_ne) using 1
  · rw [aeval_eq, zero_sub, div_neg]
  rw [RingHom.map_zero]
  convert! aeval_eq
  conv_rhs => rw [← divX_mul_X_add p]
  rw [map_add]; rw [map_mul]; rw [h]; rw [zero_mul]; rw [zero_add]; rw [aeval_C]

/--
theorem `Subalgebra.inv_mem_of_root_of_coeff_zero_ne_zero` / 定理 `Subalgebra.inv_mem_of_root_of_coeff_zero_ne_zero`

English:
theorem Subalgebra.inv_mem_of_root_of_coeff_zero_ne_zero
  statement: {x : A} {p : K[X]}
  proof: by
  suffices (x⁻¹ : L) = (-p.coeff 0)⁻¹ • aeval x (divX p) by
    rw [this]
    exact A.smul_mem (aeval x _).2 _
  have : aeval (x : L) p = 0 := by rw [Subalgebra.aeval_coe, aeval_eq, Subalgebra.coe_zero]
  rw [inv_eq_of_root_of_coeff_zero_ne_zero this coeff_zero_ne]; rw [div_eq_inv_mul]; rw [Algebra.smul_def]; rw [aeval_coe]; rw [map_inv₀]; rw [map_neg]; rw [inv_neg]; rw [neg_mul]

中文:
定理 子代数.inv_mem_of_root_of_coeff_zero_ne_zero
  结论: {x : A} {p : K[X]}
  证明: by
  suffices (x⁻¹ : L) = (-p.coeff 0)⁻¹ • aeval x (divX p) by
    rw [this]
    exact A.smul_mem (aeval x _).2 _
  have : aeval (x : L) p = 0 := by rw [Subalgebra.aeval_coe, aeval_eq, Subalgebra.coe_zero]
  rw [inv_eq_of_root_of_coeff_zero_ne_zero this coeff_zero_ne]; rw [div_eq_inv_mul]; rw [Algebra.smul_def]; rw [aeval_coe]; rw [map_inv₀]; rw [map_neg]; rw [inv_neg]; rw [neg_mul]

Depends on / 依赖: A.smul_mem, Algebra, Algebra.smul_def, Subalgebra, Subalgebra.aeval_coe, Subalgebra.coe_zero, aeval_coe, aeval_eq, coe_zero, coeff_zero_ne, div_eq_inv_mul, inv_eq_of_root_of_coeff_zero_ne_zero, inv_neg, map_neg, neg_mul, p.coeff, smul_def, smul_mem
-/
theorem Subalgebra.inv_mem_of_root_of_coeff_zero_ne_zero {x : A} {p : K[X]}
    (aeval_eq : aeval x p = 0) (coeff_zero_ne : p.coeff 0 != 0) : (x⁻¹ : L) in A := by
  suffices (x⁻¹ : L) = (-p.coeff 0)⁻¹ • aeval x (divX p) by
    rw [this]
    exact A.smul_mem (aeval x _).2 _
  have : aeval (x : L) p = 0 := by rw [Subalgebra.aeval_coe, aeval_eq, Subalgebra.coe_zero]
  rw [inv_eq_of_root_of_coeff_zero_ne_zero this coeff_zero_ne]; rw [div_eq_inv_mul]; rw [Algebra.smul_def]; rw [aeval_coe]; rw [map_inv₀]; rw [map_neg]; rw [inv_neg]; rw [neg_mul]

/--
theorem `Subalgebra.inv_mem_of_algebraic` / 定理 `Subalgebra.inv_mem_of_algebraic`

English:
theorem Subalgebra.inv_mem_of_algebraic
  given: {x : A} (hx : IsAlgebraic K (x : L))
  proof: by
  obtain ⟨p, ne_zero, aeval_eq⟩ := hx
  rw [Subalgebra.aeval_coe]; rw [Subalgebra.coe_eq_zero] at aeval_eq
  revert ne_zero aeval_eq
  refine p.recOnHorner ?_ ?_ ?_
  · intro h
    contradiction
  · intro p a hp ha _ih _ne_zero aeval_eq
    refine A.inv_mem_of_root_of_coeff_zero_ne_zero aeval_eq ?_
    rwa [coeff_add, hp, zero_add, coeff_C, if_pos rfl]
  · intro p hp ih _ne_zero aeval_eq
    rw [map_mul]; rw [aeval_X]; rw [mul_eq_zero] at aeval_eq
    rcases aeval_eq with aeval_eq | x_eq
    · exact ih hp aeval_eq
    · rw [x_eq, Subalgebra.coe_zero, inv_zero]
      exact A.zero_mem

中文:
定理 子代数.inv_mem_of_algebraic
  条件: {x : A} (hx : 是代数 K (x : L))
  证明: by
  obtain ⟨p, ne_zero, aeval_eq⟩ := hx
  rw [Subalgebra.aeval_coe]; rw [Subalgebra.coe_eq_zero] at aeval_eq
  revert ne_zero aeval_eq
  refine p.recOnHorner ?_ ?_ ?_
  · intro h
    contradiction
  · intro p a hp ha _ih _ne_zero aeval_eq
    refine A.inv_mem_of_root_of_coeff_zero_ne_zero aeval_eq ?_
    rwa [coeff_add, hp, zero_add, coeff_C, if_pos rfl]
  · intro p hp ih _ne_zero aeval_eq
    rw [map_mul]; rw [aeval_X]; rw [mul_eq_zero] at aeval_eq
    rcases aeval_eq with aeval_eq | x_eq
    · exact ih hp aeval_eq
    · rw [x_eq, Subalgebra.coe_zero, inv_zero]
      exact A.zero_mem

Depends on / 依赖: A.inv_mem_of_root_of_coeff_zero_ne_zero, Subalgebra, Subalgebra.aeval_coe, Subalgebra.coe_eq_zero, _ne_zero, aeval_X, aeval_coe, aeval_eq, coe_eq_zero, coeff_C, coeff_add, if_pos, inv_mem_of_root_of_coeff_zero_ne_zero, map_mul, mul_eq_zero, ne_zero, p.recOnHorner, recOnHorner, revert, x_eq
-/
theorem Subalgebra.inv_mem_of_algebraic {x : A} (hx : IsAlgebraic K (x : L)) :
    (x⁻¹ : L) in A := by
  obtain ⟨p, ne_zero, aeval_eq⟩ := hx
  rw [Subalgebra.aeval_coe]; rw [Subalgebra.coe_eq_zero] at aeval_eq
  revert ne_zero aeval_eq
  refine p.recOnHorner ?_ ?_ ?_
  · intro h
    contradiction
  · intro p a hp ha _ih _ne_zero aeval_eq
    refine A.inv_mem_of_root_of_coeff_zero_ne_zero aeval_eq ?_
    rwa [coeff_add, hp, zero_add, coeff_C, if_pos rfl]
  · intro p hp ih _ne_zero aeval_eq
    rw [map_mul]; rw [aeval_X]; rw [mul_eq_zero] at aeval_eq
    rcases aeval_eq with aeval_eq | x_eq
    · exact ih hp aeval_eq
    · rw [x_eq, Subalgebra.coe_zero, inv_zero]
      exact A.zero_mem

/-- In an algebraic extension L/K, an intermediate subalgebra is a field. -/
@[stacks 0BID]
/--
theorem `Subalgebra.isField_of_algebraic` / 定理 `Subalgebra.isField_of_algebraic`

English:
theorem Subalgebra.isField_of_algebraic
  given: [Algebra.IsAlgebraic K L]
  statement: IsField A
  proof: { show Nontrivial A by infer_instance, Subalgebra.toCommRing A with
    mul_inv_cancel := fun {a} ha =>
      ⟨⟨a⁻¹, A.inv_mem_of_algebraic (Algebra.IsAlgebraic.isAlgebraic (a : L))⟩,
        Subtype.ext (mul_inv_cancel₀ (mt (Subalgebra.coe_eq_zero _).mp ha))⟩ }

中文:
定理 子代数.isField_of_algebraic
  条件: [代数.是代数 K L]
  结论: 是域 A
  证明: { show Nontrivial A by infer_instance, Subalgebra.toCommRing A with
    mul_inv_cancel := fun {a} ha =>
      ⟨⟨a⁻¹, A.inv_mem_of_algebraic (Algebra.IsAlgebraic.isAlgebraic (a : L))⟩,
        Subtype.ext (mul_inv_cancel₀ (mt (Subalgebra.coe_eq_zero _).mp ha))⟩ }

Depends on / 依赖: A.inv_mem_of_algebraic, Algebra, Algebra.IsAlgebraic.isAlgebraic, IsAlgebraic, Nontrivial, Subalgebra, Subalgebra.coe_eq_zero, Subalgebra.toCommRing, Subtype, Subtype.ext, coe_eq_zero, infer_instance, inv_mem_of_algebraic, isAlgebraic, mul_inv_cancel, toCommRing
-/
theorem Subalgebra.isField_of_algebraic [Algebra.IsAlgebraic K L] : IsField A :=
  { show Nontrivial A by infer_instance, Subalgebra.toCommRing A with
    mul_inv_cancel := fun {a} ha =>
      ⟨⟨a⁻¹, A.inv_mem_of_algebraic (Algebra.IsAlgebraic.isAlgebraic (a : L))⟩,
        Subtype.ext (mul_inv_cancel₀ (mt (Subalgebra.coe_eq_zero _).mp ha))⟩ }

end Field

section Infinite

variable {R A : Type*} [CommRing R] [Ring A] [Algebra R A] [Nontrivial R]

/--
theorem `Transcendental.infinite` / 定理 `Transcendental.infinite`

English:
theorem Transcendental.infinite
  given: {x : A} (hx : Transcendental R x)
  statement: Infinite A
  proof: .of_injective _ (transcendental_iff_injective.mp hx)

中文:
定理 超越.infinite
  条件: {x : A} (hx : 超越 R x)
  结论: 无限 A
  证明: .of_injective _ (transcendental_iff_injective.mp hx)

Depends on / 依赖: of_injective, transcendental_iff_injective, transcendental_iff_injective.mp
-/
theorem Transcendental.infinite {x : A} (hx : Transcendental R x) : Infinite A :=
  .of_injective _ (transcendental_iff_injective.mp hx)

variable (R A) in
/--
theorem `Algebra.Transcendental.infinite` / 定理 `Algebra.Transcendental.infinite`

English:
theorem Algebra.Transcendental.infinite
  given: [Algebra.Transcendental R A]
  statement: Infinite A
  proof: have ⟨x, hx⟩ := ‹Algebra.Transcendental R A›
  hx.infinite

中文:
定理 代数.超越.infinite
  条件: [代数.超越 R A]
  结论: 无限 A
  证明: have ⟨x, hx⟩ := ‹Algebra.Transcendental R A›
  hx.infinite

Depends on / 依赖: Algebra, Algebra.Transcendental, Transcendental, hx.infinite, infinite
-/
theorem Algebra.Transcendental.infinite [Algebra.Transcendental R A] : Infinite A :=
  have ⟨x, hx⟩ := ‹Algebra.Transcendental R A›
  hx.infinite

end Infinite
