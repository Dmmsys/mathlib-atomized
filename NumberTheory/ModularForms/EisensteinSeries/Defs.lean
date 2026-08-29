/-
Copyright (c) 2024 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck, David Loeffler
-/
module

public import Mathlib.Algebra.EuclideanDomain.Int
public import Mathlib.NumberTheory.ModularForms.SlashInvariantForms
public import Mathlib.RingTheory.EuclideanDomain
public import Mathlib.NumberTheory.ModularForms.CongruenceSubgroups

/-!
# Eisenstein Series

## Main definitions

* We define Eisenstein series of level `Γ(N)` for any `N : ℕ` and weight `k : ℤ` as the infinite sum
  `∑' v : (Fin 2 → ℤ), (1 / (v 0 * z + v 1) ^ k)`, where `z : ℍ` and `v` ranges over all pairs of
  coprime integers congruent to a fixed pair `(a, b)` modulo `N`. Note that by using `(Fin 2 → ℤ)`
  instead of `ℤ × ℤ` we can state all of the required equivalences using matrices and vectors, which
  makes working with them more convenient.

* We show that they define a slash invariant form of level `Γ(N)` and weight `k`.

## References
* [F. Diamond and J. Shurman, *A First Course in Modular Forms*][diamondshurman2005]
-/

@[expose] public section

noncomputable section

open ModularForm UpperHalfPlane Complex Matrix CongruenceSubgroup Set

open scoped MatrixGroups

namespace EisensteinSeries

variable (N r : Nat) (a : Fin 2 -> ZMod N)

section gammaSet_def

/--
Definition of `gammaSet` / `gammaSet` 的定义

English:
definition gammaSet
  body: {v : Fin 2 -> Int | (↑) ∘ v = a ∧ (v 0).gcd (v 1) = r}

中文:
定义 gammaSet
  定义体: {v : Fin 2 -> Int | (↑) ∘ v = a ∧ (v 0).gcd (v 1) = r}
-/
def gammaSet := {v : Fin 2 -> Int | (↑) ∘ v = a ∧ (v 0).gcd (v 1) = r}

open scoped Function in -- required for scoped `on` notation
/--
lemma `pairwise_disjoint_gammaSet` / 引理 `pairwise_disjoint_gammaSet`

English:
lemma pairwise_disjoint_gammaSet
  statement: Pairwise (Disjoint on gammaSet N r)
  proof: by
  refine fun u v huv => ?_
  contrapose huv
  obtain ⟨f, hf⟩ := Set.not_disjoint_iff.mp huv
  exact hf.1.1.symm.trans hf.2.1

中文:
引理 pairwise_disjoint_gammaSet
  结论: 两两 (Disjoint on gammaSet N r)
  证明: by
  refine fun u v huv => ?_
  contrapose huv
  obtain ⟨f, hf⟩ := Set.not_disjoint_iff.mp huv
  exact hf.1.1.symm.trans hf.2.1

Depends on / 依赖: Set.not_disjoint_iff.mp, contrapose, not_disjoint_iff, symm.trans
-/
lemma pairwise_disjoint_gammaSet : Pairwise (Disjoint on gammaSet N r) := by
  refine fun u v huv => ?_
  contrapose huv
  obtain ⟨f, hf⟩ := Set.not_disjoint_iff.mp huv
  exact hf.1.1.symm.trans hf.2.1

/--
lemma `gammaSet_one_const` / 引理 `gammaSet_one_const`

English:
lemma gammaSet_one_const
  given: (a a' : Fin 2 -> ZMod 1)
  statement: gammaSet 1 r a = gammaSet 1 r a'
  proof: congr_arg _ (Subsingleton.elim _ _)

中文:
引理 gammaSet_one_const
  条件: (a a' : 有限集 2 -> ZMod 1)
  结论: gammaSet 1 r a = gammaSet 1 r a'
  证明: congr_arg _ (Subsingleton.elim _ _)

Depends on / 依赖: Subsingleton, Subsingleton.elim, congr_arg
-/
lemma gammaSet_one_const (a a' : Fin 2 -> ZMod 1) : gammaSet 1 r a = gammaSet 1 r a' :=
  congr_arg _ (Subsingleton.elim _ _)

/--
lemma `gammaSet_one_eq` / 引理 `gammaSet_one_eq`

English:
lemma gammaSet_one_eq
  given: (a : Fin 2 -> ZMod 1)
  proof: by
  simp [gammaSet, Subsingleton.eq_zero (α := Fin 2 -> ZMod 1)]

中文:
引理 gammaSet_one_eq
  条件: (a : 有限集 2 -> ZMod 1)
  证明: by
  simp [gammaSet, Subsingleton.eq_zero (α := Fin 2 -> ZMod 1)]

Depends on / 依赖: Subsingleton, Subsingleton.eq_zero, eq_zero, gammaSet
-/
lemma gammaSet_one_eq (a : Fin 2 -> ZMod 1) :
    gammaSet 1 r a = {v : Fin 2 -> Int | (v 0).gcd (v 1) = r} := by
  simp [gammaSet, Subsingleton.eq_zero (α := Fin 2 -> ZMod 1)]

/--
lemma `gammaSet_one_mem_iff` / 引理 `gammaSet_one_mem_iff`

English:
lemma gammaSet_one_mem_iff
  given: (v : Fin 2 -> Int)
  statement: v in gammaSet 1 r 0 ↔ (v 0).gcd (v 1) = r
  proof: by
  simp [gammaSet, Subsingleton.eq_zero (α := Fin 2 -> ZMod 1)]

中文:
引理 gammaSet_one_mem_iff
  条件: (v : 有限集 2 -> 整数)
  结论: v in gammaSet 1 r 0 ↔ (v 0).最大公约数 (v 1) = r
  证明: by
  simp [gammaSet, Subsingleton.eq_zero (α := Fin 2 -> ZMod 1)]

Depends on / 依赖: Subsingleton, Subsingleton.eq_zero, eq_zero, gammaSet
-/
lemma gammaSet_one_mem_iff (v : Fin 2 -> Int) : v in gammaSet 1 r 0 ↔ (v 0).gcd (v 1) = r := by
  simp [gammaSet, Subsingleton.eq_zero (α := Fin 2 -> ZMod 1)]

/--
Definition of `gammaSet_one_equiv` / `gammaSet_one_equiv` 的定义

English:
definition gammaSet_one_equiv
  signature: (a a' : Fin 2 -> ZMod 1)
  body: Equiv.setCongr (gammaSet_one_const r a a')

中文:
定义 gammaSet_one_equiv
  签名: (a a' : 有限集 2 -> ZMod 1)
  定义体: Equiv.setCongr (gammaSet_one_const r a a')

Depends on / 依赖: Equiv.setCongr, gammaSet_one_const, setCongr
-/
def gammaSet_one_equiv (a a' : Fin 2 -> ZMod 1) : gammaSet 1 r a ≃ gammaSet 1 r a' :=
  Equiv.setCongr (gammaSet_one_const r a a')

/--
Definition of `finGcdMap` / `finGcdMap` 的定义

English:
abbreviation finGcdMap
  signature: (v : Fin 2 -> Int)
  body: (v 0).gcd (v 1)

中文:
缩写 finGcdMap
  签名: (v : 有限集 2 -> 整数)
  定义体: (v 0).gcd (v 1)
-/
abbrev finGcdMap (v : Fin 2 -> Int) : Nat := (v 0).gcd (v 1)

/--
lemma `finGcdMap_div` / 引理 `finGcdMap_div`

English:
lemma finGcdMap_div
  given: {r : Nat} [NeZero r] (v : Fin 2 -> Int) (hv : finGcdMap v = r)
  proof: by
  rw [← hv]
  apply isCoprime_div_gcd_div_gcd_of_gcd_ne_zero
  have := NeZero.ne r
  aesop

中文:
引理 finGcdMap_div
  条件: {r : 自然数} [NeZero r] (v : 有限集 2 -> 整数) (hv : finGcdMap v = r)
  证明: by
  rw [← hv]
  apply isCoprime_div_gcd_div_gcd_of_gcd_ne_zero
  have := NeZero.ne r
  aesop

Depends on / 依赖: NeZero, NeZero.ne, isCoprime_div_gcd_div_gcd_of_gcd_ne_zero
-/
lemma finGcdMap_div {r : Nat} [NeZero r] (v : Fin 2 -> Int) (hv : finGcdMap v = r) :
    IsCoprime ((v / r) 0) ((v / r) 1) := by
  rw [← hv]
  apply isCoprime_div_gcd_div_gcd_of_gcd_ne_zero
  have := NeZero.ne r
  aesop

/--
lemma `finGcdMap_smul` / 引理 `finGcdMap_smul`

English:
lemma finGcdMap_smul
  given: {r : Nat} (a : Int) {v : Fin 2 -> Int} (hv : finGcdMap v = r)
  proof: by
  simp [finGcdMap, Int.gcd_mul_left, hv]

中文:
引理 finGcdMap_smul
  条件: {r : 自然数} (a : 整数) {v : 有限集 2 -> 整数} (hv : finGcdMap v = r)
  证明: by
  simp [finGcdMap, Int.gcd_mul_left, hv]

Depends on / 依赖: Int.gcd_mul_left, finGcdMap, gcd_mul_left
-/
lemma finGcdMap_smul {r : Nat} (a : Int) {v : Fin 2 -> Int} (hv : finGcdMap v = r) :
    finGcdMap (a • v) = a.natAbs * r := by
  simp [finGcdMap, Int.gcd_mul_left, hv]

/--
Definition of `divIntMap` / `divIntMap` 的定义

English:
abbreviation divIntMap
  signature: (r : Int) {m : Nat} (v : Fin m -> Int)
  body: v / r

中文:
缩写 div整数Map
  签名: (r : 整数) {m : 自然数} (v : 有限集 m -> 整数)
  定义体: v / r
-/
abbrev divIntMap (r : Int) {m : Nat} (v : Fin m -> Int) : Fin m -> Int := v / r

/--
lemma `mem_gammaSet_one` / 引理 `mem_gammaSet_one`

English:
lemma mem_gammaSet_one
  given: (v : Fin 2 -> Int)
  statement: v in gammaSet 1 1 0 ↔ IsCoprime (v 0) (v 1)
  proof: by
  rw [gammaSet_one_mem_iff]; rw [Int.isCoprime_iff_gcd_eq_one]

中文:
引理 mem_gammaSet_one
  条件: (v : 有限集 2 -> 整数)
  结论: v in gammaSet 1 1 0 ↔ IsCoprime (v 0) (v 1)
  证明: by
  rw [gammaSet_one_mem_iff]; rw [Int.isCoprime_iff_gcd_eq_one]

Depends on / 依赖: Int.isCoprime_iff_gcd_eq_one, gammaSet_one_mem_iff, isCoprime_iff_gcd_eq_one
-/
lemma mem_gammaSet_one (v : Fin 2 -> Int) : v in gammaSet 1 1 0 ↔ IsCoprime (v 0) (v 1) := by
  rw [gammaSet_one_mem_iff]; rw [Int.isCoprime_iff_gcd_eq_one]

/--
lemma `gammaSet_div_gcd` / 引理 `gammaSet_div_gcd`

English:
lemma gammaSet_div_gcd
  given: {r : Nat} {v : Fin 2 -> Int} (hv : v in (gammaSet 1 r 0)) (i : Fin 2)
  proof: by
  fin_cases i <;> simp [← hv.2, Int.gcd_dvd_left, Int.gcd_dvd_right]

中文:
引理 gammaSet_div_gcd
  条件: {r : 自然数} {v : 有限集 2 -> 整数} (hv : v in (gammaSet 1 r 0)) (i : 有限集 2)
  证明: by
  fin_cases i <;> simp [← hv.2, Int.gcd_dvd_left, Int.gcd_dvd_right]

Depends on / 依赖: Int.gcd_dvd_left, Int.gcd_dvd_right, fin_cases, gcd_dvd_left, gcd_dvd_right
-/
lemma gammaSet_div_gcd {r : Nat} {v : Fin 2 -> Int} (hv : v in (gammaSet 1 r 0)) (i : Fin 2) :
   (r : Int) ∣ v i := by
  fin_cases i <;> simp [← hv.2, Int.gcd_dvd_left, Int.gcd_dvd_right]

/--
lemma `gammaSet_div_gcd_to_gammaSet10_bijection` / 引理 `gammaSet_div_gcd_to_gammaSet10_bijection`

English:
lemma gammaSet_div_gcd_to_gammaSet10_bijection
  given: (r : Nat) [NeZero r]
  proof: by
  refine ⟨?_, ?_, ?_⟩
  · intro x hx
    simp only [divIntMap, mem_gammaSet_one] at *
    exact finGcdMap_div _ hx.2
  · intro x hx v hv hv2
    ext i
    exact (Int.ediv_left_inj (gammaSet_div_gcd hx i) (gammaSet_div_gcd hv i)).mp
      (congr_fun hv2 i)
  · intro x hx
    use r • x
    simp onl

中文:
引理 gammaSet_div_gcd_to_gammaSet10_bijection
  条件: (r : 自然数) [NeZero r]
  证明: by
  refine ⟨?_, ?_, ?_⟩
  · intro x hx
    simp only [divIntMap, mem_gammaSet_one] at *
    exact finGcdMap_div _ hx.2
  · intro x hx v hv hv2
    ext i
    exact (Int.ediv_left_inj (gammaSet_div_gcd hx i) (gammaSet_div_gcd hv i)).mp
      (congr_fun hv2 i)
  · intro x hx
    use r • x
    simp onl

Depends on / 依赖: Int.cast_natCast, Int.ediv_left_inj, Int.gcd_mul_left, Int.isCoprime_iff_gcd_eq_one, NeZero, NeZero.ne, Subsingleton, Subsingleton.eq_zero, cast_natCast, congr_fun, divIntMap, ediv_left_inj, eq_zero, finGcdMap_div, gammaSet_div_gcd, gcd_mul_left, isCoprime_iff_gcd_eq_one, mem_gammaSet_one, nsmul_eq_mul
-/
lemma gammaSet_div_gcd_to_gammaSet10_bijection (r : Nat) [NeZero r] :
    Set.BijOn (divIntMap r) (gammaSet 1 r 0) (gammaSet 1 1 0) := by
  refine ⟨?_, ?_, ?_⟩
  · intro x hx
    simp only [divIntMap, mem_gammaSet_one] at *
    exact finGcdMap_div _ hx.2
  · intro x hx v hv hv2
    ext i
    exact (Int.ediv_left_inj (gammaSet_div_gcd hx i) (gammaSet_div_gcd hv i)).mp
      (congr_fun hv2 i)
  · intro x hx
    use r • x
    simp only [nsmul_eq_mul, divIntMap, Int.cast_natCast]
    constructor
    · rw [mem_gammaSet_one, Int.isCoprime_iff_gcd_eq_one] at hx
      exact ⟨Subsingleton.eq_zero _, by simp [Int.gcd_mul_left, hx]⟩
    · ext i
      simp_all [NeZero.ne r]

/--
lemma `gammaSet_eq_gcd_mul_divIntMap` / 引理 `gammaSet_eq_gcd_mul_divIntMap`

English:
lemma gammaSet_eq_gcd_mul_divIntMap
  given: {r : Nat} {v : Fin 2 -> Int} (hv : v in gammaSet 1 r 0)
  proof: by
  by_cases hr : r = 0
  · have hv := hv.2
    simp only [hr, Fin.isValue, Int.gcd_eq_zero_iff, CharP.cast_eq_zero, zero_smul] at *
    ext i
    fin_cases i <;> simp [hv]
  · ext i
    simp_all [Pi.smul_apply, divIntMap, ← Int.mul_ediv_assoc _ (gammaSet_div_gcd hv i)]

中文:
引理 gammaSet_eq_gcd_mul_div整数Map
  条件: {r : 自然数} {v : 有限集 2 -> 整数} (hv : v in gammaSet 1 r 0)
  证明: by
  by_cases hr : r = 0
  · have hv := hv.2
    simp only [hr, Fin.isValue, Int.gcd_eq_zero_iff, CharP.cast_eq_zero, zero_smul] at *
    ext i
    fin_cases i <;> simp [hv]
  · ext i
    simp_all [Pi.smul_apply, divIntMap, ← Int.mul_ediv_assoc _ (gammaSet_div_gcd hv i)]

Depends on / 依赖: CharP.cast_eq_zero, Fin.isValue, Int.gcd_eq_zero_iff, Int.mul_ediv_assoc, Pi.smul_apply, cast_eq_zero, divIntMap, fin_cases, gammaSet_div_gcd, gcd_eq_zero_iff, isValue, mul_ediv_assoc, smul_apply, zero_smul
-/
lemma gammaSet_eq_gcd_mul_divIntMap {r : Nat} {v : Fin 2 -> Int} (hv : v in gammaSet 1 r 0) :
    v = r • (divIntMap r v) := by
  by_cases hr : r = 0
  · have hv := hv.2
    simp only [hr, Fin.isValue, Int.gcd_eq_zero_iff, CharP.cast_eq_zero, zero_smul] at *
    ext i
    fin_cases i <;> simp [hv]
  · ext i
    simp_all [Pi.smul_apply, divIntMap, ← Int.mul_ediv_assoc _ (gammaSet_div_gcd hv i)]

/--
Definition of `gammaSetDivGcdEquiv` / `gammaSetDivGcdEquiv` 的定义

English:
definition gammaSetDivGcdEquiv
  signature: (r : Nat) [NeZero r]
  body: Set.BijOn.equiv _ (gammaSet_div_gcd_to_gammaSet10_bijection r)

@[simp]

中文:
定义 gammaSetDivGcdEquiv
  签名: (r : 自然数) [NeZero r]
  定义体: Set.BijOn.equiv _ (gammaSet_div_gcd_to_gammaSet10_bijection r)

@[simp]

Depends on / 依赖: Set.BijOn.equiv, gammaSet_div_gcd_to_gammaSet10_bijection
-/
def gammaSetDivGcdEquiv (r : Nat) [NeZero r] : gammaSet 1 r 0 ≃ gammaSet 1 1 0 :=
    Set.BijOn.equiv _ (gammaSet_div_gcd_to_gammaSet10_bijection r)

@[simp]
/--
lemma `gammaSetDivGcdEquiv_eq` / 引理 `gammaSetDivGcdEquiv_eq`

English:
lemma gammaSetDivGcdEquiv_eq
  given: (r : Nat) [NeZero r] (v : gammaSet 1 r 0)
  proof: rfl

中文:
引理 gammaSetDivGcdEquiv_eq
  条件: (r : 自然数) [NeZero r] (v : gammaSet 1 r 0)
  证明: rfl
-/
lemma gammaSetDivGcdEquiv_eq (r : Nat) [NeZero r] (v : gammaSet 1 r 0) :
    (gammaSetDivGcdEquiv r) v = divIntMap r v.1 := rfl

/--
Definition of `gammaSetDivGcdSigmaEquiv` / `gammaSetDivGcdSigmaEquiv` 的定义

English:
definition gammaSetDivGcdSigmaEquiv
  signature: : (Fin 2 -> Int) ≃ (Σ r : Nat, gammaSet 1 r 0)
  body: by
  apply (Equiv.sigmaFiberEquiv finGcdMap).symm.trans
  refine Equiv.sigmaCongrRight fun b => ?_
  apply Equiv.subtypeEquivProp
  simp [gammaSet_one_eq]

@[simp]

中文:
定义 gammaSetDivGcdSigmaEquiv
  签名: : (有限集 2 -> 整数) ≃ (Σ r : 自然数, gammaSet 1 r 0)
  定义体: by
  apply (Equiv.sigmaFiberEquiv finGcdMap).symm.trans
  refine Equiv.sigmaCongrRight fun b => ?_
  apply Equiv.subtypeEquivProp
  simp [gammaSet_one_eq]

@[simp]

Depends on / 依赖: Equiv.sigmaCongrRight, Equiv.sigmaFiberEquiv, Equiv.subtypeEquivProp, finGcdMap, gammaSet_one_eq, sigmaCongrRight, sigmaFiberEquiv, subtypeEquivProp, symm.trans
-/
def gammaSetDivGcdSigmaEquiv : (Fin 2 -> Int) ≃ (Σ r : Nat, gammaSet 1 r 0) := by
  apply (Equiv.sigmaFiberEquiv finGcdMap).symm.trans
  refine Equiv.sigmaCongrRight fun b => ?_
  apply Equiv.subtypeEquivProp
  simp [gammaSet_one_eq]

@[simp]
/--
lemma `gammaSetDivGcdSigmaEquiv_symm_eq` / 引理 `gammaSetDivGcdSigmaEquiv_symm_eq`

English:
lemma gammaSetDivGcdSigmaEquiv_symm_eq
  given: (v : Σ r : Nat, gammaSet 1 r 0)
  proof: rfl

中文:
引理 gammaSetDivGcdSigmaEquiv_symm_eq
  条件: (v : Σ r : 自然数, gammaSet 1 r 0)
  证明: rfl
-/
lemma gammaSetDivGcdSigmaEquiv_symm_eq (v : Σ r : Nat, gammaSet 1 r 0) :
    (gammaSetDivGcdSigmaEquiv.symm v) = v.2 := rfl

end gammaSet_def

variable {N a r} [NeZero r]

section gamma_action

/--
lemma `vecMulSL_gcd` / 引理 `vecMulSL_gcd`

English:
lemma vecMulSL_gcd
  given: {v : Fin 2 -> Int} (hab : finGcdMap v = r) (A : SL(2, Int))
  proof: by
  have hvr : v = r • (v / r) := by
    ext i
    refine Eq.symm (Int.mul_ediv_cancel' ?_)
    fin_cases i <;> simp [← hab, Int.gcd_dvd_left, Int.gcd_dvd_right]
  rw [hvr]; rw [smul_vecMul]
  simpa using finGcdMap_smul r (Int.isCoprime_iff_gcd_eq_one.mp ((finGcdMap_div v hab).vecMulSL A))

中文:
引理 vecMulSL_gcd
  条件: {v : 有限集 2 -> 整数} (hab : finGcdMap v = r) (A : SL(2, 整数))
  证明: by
  have hvr : v = r • (v / r) := by
    ext i
    refine Eq.symm (Int.mul_ediv_cancel' ?_)
    fin_cases i <;> simp [← hab, Int.gcd_dvd_left, Int.gcd_dvd_right]
  rw [hvr]; rw [smul_vecMul]
  simpa using finGcdMap_smul r (Int.isCoprime_iff_gcd_eq_one.mp ((finGcdMap_div v hab).vecMulSL A))

Depends on / 依赖: Eq.symm, Int.gcd_dvd_left, Int.gcd_dvd_right, Int.isCoprime_iff_gcd_eq_one.mp, Int.mul_ediv_cancel, finGcdMap_div, finGcdMap_smul, fin_cases, gcd_dvd_left, gcd_dvd_right, isCoprime_iff_gcd_eq_one, mul_ediv_cancel, smul_vecMul, vecMulSL
-/
lemma vecMulSL_gcd {v : Fin 2 -> Int} (hab : finGcdMap v = r) (A : SL(2, Int)) :
    finGcdMap (v ᵥ* A.1) = r := by
  have hvr : v = r • (v / r) := by
    ext i
    refine Eq.symm (Int.mul_ediv_cancel' ?_)
    fin_cases i <;> simp [← hab, Int.gcd_dvd_left, Int.gcd_dvd_right]
  rw [hvr]; rw [smul_vecMul]
  simpa using finGcdMap_smul r (Int.isCoprime_iff_gcd_eq_one.mp ((finGcdMap_div v hab).vecMulSL A))

/--
lemma `vecMul_SL2_mem_gammaSet` / 引理 `vecMul_SL2_mem_gammaSet`

English:
lemma vecMul_SL2_mem_gammaSet
  statement: {v : Fin 2 -> Int} (hv : v in gammaSet N r a)
  proof: by
  refine ⟨?_, vecMulSL_gcd hv.2 γ⟩
  have := RingHom.map_vecMul (m := Fin 2) (n := Fin 2) (Int.castRingHom (ZMod N)) γ v
  simp only [eq_intCast, Int.coe_castRingHom] at this
  simp_rw [Function.comp_def, this, hv.1]
  simp

中文:
引理 vecMul_SL2_mem_gammaSet
  结论: {v : 有限集 2 -> 整数} (hv : v in gammaSet N r a)
  证明: by
  refine ⟨?_, vecMulSL_gcd hv.2 γ⟩
  have := RingHom.map_vecMul (m := Fin 2) (n := Fin 2) (Int.castRingHom (ZMod N)) γ v
  simp only [eq_intCast, Int.coe_castRingHom] at this
  simp_rw [Function.comp_def, this, hv.1]
  simp

Depends on / 依赖: Function, Function.comp_def, Int.castRingHom, Int.coe_castRingHom, RingHom, RingHom.map_vecMul, castRingHom, coe_castRingHom, comp_def, eq_intCast, map_vecMul, simp_rw, vecMulSL_gcd
-/
lemma vecMul_SL2_mem_gammaSet {v : Fin 2 -> Int} (hv : v in gammaSet N r a)
    (γ : SL(2, Int)) : v ᵥ* γ in gammaSet N r (a ᵥ* γ) := by
  refine ⟨?_, vecMulSL_gcd hv.2 γ⟩
  have := RingHom.map_vecMul (m := Fin 2) (n := Fin 2) (Int.castRingHom (ZMod N)) γ v
  simp only [eq_intCast, Int.coe_castRingHom] at this
  simp_rw [Function.comp_def, this, hv.1]
  simp

variable (a) in
/--
Definition of `gammaSetEquiv` / `gammaSetEquiv` 的定义

English:
definition gammaSetEquiv
  signature: (γ : SL(2, Int))
  body: ⟨v.1 ᵥ* γ, vecMul_SL2_mem_gammaSet v.2 γ⟩
  invFun v := ⟨v.1 ᵥ* ↑(γ⁻¹), by
      have := vecMul_SL2_mem_gammaSet v.2 γ⁻¹
      rw [vecMul_vecMul]; rw [← SpecialLinearGroup.coe_mul] at this
      simpa only [SpecialLinearGroup.map_apply_coe, RingHom.mapMatrix_apply, Int.coe_castRingHom,
        map_i

中文:
定义 gammaSetEquiv
  签名: (γ : SL(2, 整数))
  定义体: ⟨v.1 ᵥ* γ, vecMul_SL2_mem_gammaSet v.2 γ⟩
  invFun v := ⟨v.1 ᵥ* ↑(γ⁻¹), by
      have := vecMul_SL2_mem_gammaSet v.2 γ⁻¹
      rw [vecMul_vecMul]; rw [← SpecialLinearGroup.coe_mul] at this
      simpa only [SpecialLinearGroup.map_apply_coe, RingHom.mapMatrix_apply, Int.coe_castRingHom,
        map_i

Depends on / 依赖: vecMul_SL2_mem_gammaSet
-/
def gammaSetEquiv (γ : SL(2, Int)) : gammaSet N r a ≃ gammaSet N r (a ᵥ* γ) where
  toFun v := ⟨v.1 ᵥ* γ, vecMul_SL2_mem_gammaSet v.2 γ⟩
  invFun v := ⟨v.1 ᵥ* ↑(γ⁻¹), by
      have := vecMul_SL2_mem_gammaSet v.2 γ⁻¹
      rw [vecMul_vecMul]; rw [← SpecialLinearGroup.coe_mul] at this
      simpa only [SpecialLinearGroup.map_apply_coe, RingHom.mapMatrix_apply, Int.coe_castRingHom,
        map_inv, mul_inv_cancel, SpecialLinearGroup.coe_one, vecMul_one]⟩
  left_inv v := by simp_rw [vecMul_vecMul, ← SpecialLinearGroup.coe_mul, mul_inv_cancel,
    SpecialLinearGroup.coe_one, vecMul_one]
  right_inv v := by simp_rw [vecMul_vecMul, ← SpecialLinearGroup.coe_mul, inv_mul_cancel,
    SpecialLinearGroup.coe_one, vecMul_one]

end gamma_action

section eisSummand

/--
Definition of `eisSummand` / `eisSummand` 的定义

English:
definition eisSummand
  signature: (k : Int) (v : Fin 2 -> Int) (z : ℍ)
  body: (v 0 * z + v 1) ^ (-k)

中文:
定义 eisSummand
  签名: (k : 整数) (v : 有限集 2 -> 整数) (z : ℍ)
  定义体: (v 0 * z + v 1) ^ (-k)
-/
def eisSummand (k : Int) (v : Fin 2 -> Int) (z : ℍ) : Complex := (v 0 * z + v 1) ^ (-k)

/--
theorem `eisSummand_SL2_apply` / 定理 `eisSummand_SL2_apply`

English:
theorem eisSummand_SL2_apply
  given: (k : Int) (i : (Fin 2 -> Int)) (A : SL(2, Int)) (z : ℍ)
  proof: by
  simp only [eisSummand, vecMul, vec2_dotProduct, denom, UpperHalfPlane.specialLinearGroup_apply]
  have h (a b c d u v : Complex) (hc : c * z + d != 0) : (u * ((a * z + b) / (c * z + d)) + v) ^ (-k) =
      (c * z + d) ^ k * ((u * a + v * c) * z + (u * b + v * d)) ^ (-k) := by
    replace hc : z

中文:
定理 eisSummand_SL2_apply
  条件: (k : 整数) (i : (有限集 2 -> 整数)) (A : SL(2, 整数)) (z : ℍ)
  证明: by
  simp only [eisSummand, vecMul, vec2_dotProduct, denom, UpperHalfPlane.specialLinearGroup_apply]
  have h (a b c d u v : Complex) (hc : c * z + d != 0) : (u * ((a * z + b) / (c * z + d)) + v) ^ (-k) =
      (c * z + d) ^ k * ((u * a + v * c) * z + (u * b + v * d)) ^ (-k) := by
    replace hc : z

Depends on / 依赖: UpperHalfPlane, UpperHalfPlane.specialLinearGroup_apply, convert, denom_ne_zero, div_zpow, eisSummand, replace, ring_nf, specialLinearGroup_apply, vec2_dotProduct, vecMul
-/
theorem eisSummand_SL2_apply (k : Int) (i : (Fin 2 -> Int)) (A : SL(2, Int)) (z : ℍ) :
    eisSummand k i (A • z) = (denom A z) ^ k * eisSummand k (i ᵥ* A) z := by
  simp only [eisSummand, vecMul, vec2_dotProduct, denom, UpperHalfPlane.specialLinearGroup_apply]
  have h (a b c d u v : Complex) (hc : c * z + d != 0) : (u * ((a * z + b) / (c * z + d)) + v) ^ (-k) =
      (c * z + d) ^ k * ((u * a + v * c) * z + (u * b + v * d)) ^ (-k) := by
    replace hc : z * c + d != 0 := by convert! hc using 1; ring
    field_simp
    simp [div_zpow]
    ring_nf
  simpa using h (hc := denom_ne_zero A z) ..

end eisSummand

variable (a)

/--
Definition of `_root_.eisensteinSeries` / `_root_.eisensteinSeries` 的定义

English:
definition _root_.eisensteinSeries
  signature: (k : Int) (z : ℍ)
  body: ∑' x : gammaSet N 1 a, eisSummand k x z

中文:
定义 _root_.eisensteinSeries
  签名: (k : 整数) (z : ℍ)
  定义体: ∑' x : gammaSet N 1 a, eisSummand k x z

Depends on / 依赖: eisSummand, gammaSet
-/
def _root_.eisensteinSeries (k : Int) (z : ℍ) : Complex := ∑' x : gammaSet N 1 a, eisSummand k x z

/--
lemma `eisensteinSeries_slash_apply` / 引理 `eisensteinSeries_slash_apply`

English:
lemma eisensteinSeries_slash_apply
  given: (k : Int) (γ : SL(2, Int))
  proof: by
  ext1 z
  simp_rw [SL_slash_apply, zpow_neg,
    mul_inv_eq_iff_eq_mul₀ (zpow_ne_zero _ <| denom_ne_zero _ z),
    eisensteinSeries, eisSummand_SL2_apply, tsum_mul_left, mul_comm (_ ^ k)]
  congr 1
  exact (gammaSetEquiv a γ).tsum_eq (eisSummand k · z)

中文:
引理 eisensteinSeries_slash_apply
  条件: (k : 整数) (γ : SL(2, 整数))
  证明: by
  ext1 z
  simp_rw [SL_slash_apply, zpow_neg,
    mul_inv_eq_iff_eq_mul₀ (zpow_ne_zero _ <| denom_ne_zero _ z),
    eisensteinSeries, eisSummand_SL2_apply, tsum_mul_left, mul_comm (_ ^ k)]
  congr 1
  exact (gammaSetEquiv a γ).tsum_eq (eisSummand k · z)

Depends on / 依赖: SL_slash_apply, denom_ne_zero, eisSummand, eisSummand_SL2_apply, eisensteinSeries, gammaSetEquiv, mul_comm, simp_rw, tsum_eq, tsum_mul_left, zpow_ne_zero, zpow_neg
-/
lemma eisensteinSeries_slash_apply (k : Int) (γ : SL(2, Int)) :
    eisensteinSeries a k ∣[k] γ = eisensteinSeries (a ᵥ* γ) k := by
  ext1 z
  simp_rw [SL_slash_apply, zpow_neg,
    mul_inv_eq_iff_eq_mul₀ (zpow_ne_zero _ <| denom_ne_zero _ z),
    eisensteinSeries, eisSummand_SL2_apply, tsum_mul_left, mul_comm (_ ^ k)]
  congr 1
  exact (gammaSetEquiv a γ).tsum_eq (eisSummand k · z)

/--
Definition of `eisensteinSeriesSIF` / `eisensteinSeriesSIF` 的定义

English:
definition eisensteinSeriesSIF
  signature: (k : Int)
  body: eisensteinSeries a k
  slash_action_eq' A hA := by
    obtain ⟨A, (hA : A in Γ(N)), rfl⟩ := hA
    simp [SpecialLinearGroup.mapGL, ← SL_slash, eisensteinSeries_slash_apply, Gamma_mem'.mp hA]

@[deprecated (since := "2026-02-10")]
noncomputable alias eisensteinSeries_SIF := eisensteinSeriesSIF

中文:
定义 eisensteinSeriesSIF
  签名: (k : 整数)
  定义体: eisensteinSeries a k
  slash_action_eq' A hA := by
    obtain ⟨A, (hA : A in Γ(N)), rfl⟩ := hA
    simp [SpecialLinearGroup.mapGL, ← SL_slash, eisensteinSeries_slash_apply, Gamma_mem'.mp hA]

@[deprecated (since := "2026-02-10")]
noncomputable alias eisensteinSeries_SIF := eisensteinSeriesSIF

Depends on / 依赖: eisensteinSeries
-/
def eisensteinSeriesSIF (k : Int) : SlashInvariantForm (Gamma N) k where
  toFun := eisensteinSeries a k
  slash_action_eq' A hA := by
    obtain ⟨A, (hA : A in Γ(N)), rfl⟩ := hA
    simp [SpecialLinearGroup.mapGL, ← SL_slash, eisensteinSeries_slash_apply, Gamma_mem'.mp hA]

@[deprecated (since := "2026-02-10")]
noncomputable alias eisensteinSeries_SIF := eisensteinSeriesSIF

/--
lemma `eisensteinSeriesSIF_apply` / 引理 `eisensteinSeriesSIF_apply`

English:
lemma eisensteinSeriesSIF_apply
  given: (k : Int) (z : ℍ)
  proof: rfl

@[deprecated (since := "2026-02-10")] alias eisensteinSeries_SIF_apply := eisensteinSeriesSIF_apply

中文:
引理 eisensteinSeriesSIF_apply
  条件: (k : 整数) (z : ℍ)
  证明: rfl

@[deprecated (since := "2026-02-10")] alias eisensteinSeries_SIF_apply := eisensteinSeriesSIF_apply
-/
lemma eisensteinSeriesSIF_apply (k : Int) (z : ℍ) :
    eisensteinSeriesSIF a k z = eisensteinSeries a k z := rfl

@[deprecated (since := "2026-02-10")] alias eisensteinSeries_SIF_apply := eisensteinSeriesSIF_apply

end EisensteinSeries
