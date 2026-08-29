/-
Copyright (c) 2018 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes, Johannes Hölzl, Kim Morrison, Jens Wagemaker, Johan Commelin
-/
module

public import Mathlib.Algebra.Polynomial.AlgebraMap
public import Mathlib.Algebra.Polynomial.Div
public import Mathlib.RingTheory.Coprime.Basic
import Mathlib.Tactic.ComputeDegree

/-!
# Theory of univariate polynomials

We prove basic results about univariate polynomials.

-/

@[expose] public section

assert_not_exists Ideal.map

noncomputable section

open Polynomial

open Finset

namespace Polynomial

universe u v w z

variable {R : Type u} {S : Type v} {T : Type w} {a b : R} {n : Nat}

section CommRing

variable [CommRing R] {p q : R[X]}

section

variable [Semiring S]

/--
theorem `natDegree_pos_of_aeval_root` / 定理 `natDegree_pos_of_aeval_root`

English:
theorem natDegree_pos_of_aeval_root
  statement: [Algebra R S] {p : R[X]} (hp : p != 0) {z : S}
  proof: natDegree_pos_of_eval₂_root hp (algebraMap R S) hz inj

中文:
定理 natDegree_pos_of_aeval_root
  结论: [Algebra R S] {p : R[X]} (hp : p != 0) {z : S}
  证明: natDegree_pos_of_eval₂_root hp (algebraMap R S) hz inj

Depends on / 依赖: algebraMap
-/
theorem natDegree_pos_of_aeval_root [Algebra R S] {p : R[X]} (hp : p != 0) {z : S}
    (hz : aeval z p = 0) (inj : forall x : R, algebraMap R S x = 0 -> x = 0) : 0 < p.natDegree :=
  natDegree_pos_of_eval₂_root hp (algebraMap R S) hz inj

/--
theorem `degree_pos_of_aeval_root` / 定理 `degree_pos_of_aeval_root`

English:
theorem degree_pos_of_aeval_root
  statement: [Algebra R S] {p : R[X]} (hp : p != 0) {z : S} (hz : aeval z p = 0)
  proof: natDegree_pos_iff_degree_pos.mp (natDegree_pos_of_aeval_root hp hz inj)

中文:
定理 degree_pos_of_aeval_root
  结论: [Algebra R S] {p : R[X]} (hp : p != 0) {z : S} (hz : aeval z p = 0)
  证明: natDegree_pos_iff_degree_pos.mp (natDegree_pos_of_aeval_root hp hz inj)

Depends on / 依赖: natDegree_pos_iff_degree_pos, natDegree_pos_iff_degree_pos.mp, natDegree_pos_of_aeval_root
-/
theorem degree_pos_of_aeval_root [Algebra R S] {p : R[X]} (hp : p != 0) {z : S} (hz : aeval z p = 0)
    (inj : forall x : R, algebraMap R S x = 0 -> x = 0) : 0 < p.degree :=
  natDegree_pos_iff_degree_pos.mp (natDegree_pos_of_aeval_root hp hz inj)

end

/--
theorem `smul_modByMonic` / 定理 `smul_modByMonic`

English:
theorem smul_modByMonic
  given: (c : R) (p : R[X])
  statement: c • p %ₘ q = c • (p %ₘ q)
  proof: by
  by_cases hq : q.Monic
  · rcases subsingleton_or_nontrivial R with hR | hR
    · simp only [eq_iff_true_of_subsingleton]
    · exact
      (div_modByMonic_unique (c • (p /ₘ q)) (c • (p %ₘ q)) hq
          ⟨by rw [mul_smul_comm, ← smul_add, modByMonic_add_div],
            (degree_smul_le _ _).t

中文:
定理 smul_modByMonic
  条件: (c : R) (p : R[X])
  结论: c • p %ₘ q = c • (p %ₘ q)
  证明: by
  by_cases hq : q.Monic
  · rcases subsingleton_or_nontrivial R with hR | hR
    · simp only [eq_iff_true_of_subsingleton]
    · exact
      (div_modByMonic_unique (c • (p /ₘ q)) (c • (p %ₘ q)) hq
          ⟨by rw [mul_smul_comm, ← smul_add, modByMonic_add_div],
            (degree_smul_le _ _).t

Depends on / 依赖: degree_modByMonic_lt, degree_smul_le, div_modByMonic_unique, eq_iff_true_of_subsingleton, modByMonic_add_div, modByMonic_eq_of_not_monic, mul_smul_comm, q.Monic, simp_rw, smul_add, subsingleton_or_nontrivial, trans_lt
-/
theorem smul_modByMonic (c : R) (p : R[X]) : c • p %ₘ q = c • (p %ₘ q) := by
  by_cases hq : q.Monic
  · rcases subsingleton_or_nontrivial R with hR | hR
    · simp only [eq_iff_true_of_subsingleton]
    · exact
      (div_modByMonic_unique (c • (p /ₘ q)) (c • (p %ₘ q)) hq
          ⟨by rw [mul_smul_comm, ← smul_add, modByMonic_add_div],
            (degree_smul_le _ _).trans_lt (degree_modByMonic_lt _ hq)⟩).2
  · simp_rw [modByMonic_eq_of_not_monic _ hq]

/-- `_ %ₘ q` as an `R`-linear map. -/
@[simps]
/--
Definition of `modByMonicHom` / `modByMonicHom` 的定义

English:
definition modByMonicHom
  signature: (q : R[X])
  body: p %ₘ q
  map_add' := add_modByMonic
  map_smul' := smul_modByMonic

中文:
定义 modByMonicHom
  签名: (q : R[X])
  定义体: p %ₘ q
  map_add' := add_modByMonic
  map_smul' := smul_modByMonic
-/
def modByMonicHom (q : R[X]) : R[X] ->ₗ[R] R[X] where
  toFun p := p %ₘ q
  map_add' := add_modByMonic
  map_smul' := smul_modByMonic

/--
theorem `mem_ker_modByMonic` / 定理 `mem_ker_modByMonic`

English:
theorem mem_ker_modByMonic
  given: (hq : q.Monic) {p : R[X]}
  proof: LinearMap.mem_ker.trans (modByMonic_eq_zero_iff_dvd hq)

中文:
定理 mem_ker_modByMonic
  条件: (hq : q.Monic) {p : R[X]}
  证明: LinearMap.mem_ker.trans (modByMonic_eq_zero_iff_dvd hq)

Depends on / 依赖: LinearMap, LinearMap.mem_ker.trans, mem_ker, modByMonic_eq_zero_iff_dvd
-/
theorem mem_ker_modByMonic (hq : q.Monic) {p : R[X]} :
    p in LinearMap.ker (modByMonicHom q) ↔ q ∣ p :=
  LinearMap.mem_ker.trans (modByMonic_eq_zero_iff_dvd hq)

section

variable [Ring S]

/--
theorem `aeval_modByMonic_eq_self_of_root` / 定理 `aeval_modByMonic_eq_self_of_root`

English:
theorem aeval_modByMonic_eq_self_of_root
  statement: [Algebra R S] {p q : R[X]} {x : S}
  proof: by
  --`eval₂_modByMonic_eq_self_of_root` doesn't work here as it needs commutativity
  simp [modByMonic_eq_sub_mul_div, hx]

中文:
定理 aeval_modByMonic_eq_self_of_root
  结论: [Algebra R S] {p q : R[X]} {x : S}
  证明: by
  --`eval₂_modByMonic_eq_self_of_root` doesn't work here as it needs commutativity
  simp [modByMonic_eq_sub_mul_div, hx]
-/
theorem aeval_modByMonic_eq_self_of_root [Algebra R S] {p q : R[X]} {x : S}
    (hx : aeval x q = 0) : aeval x (p %ₘ q) = aeval x p := by
  --`eval₂_modByMonic_eq_self_of_root` doesn't work here as it needs commutativity
  simp [modByMonic_eq_sub_mul_div, hx]

end

end CommRing

section NoZeroDivisors

variable [Semiring R] [NoZeroDivisors R] {p q : R[X]}

/--
theorem `trailingDegree_mul` / 定理 `trailingDegree_mul`

English:
theorem trailingDegree_mul
  statement: (p * q).trailingDegree = p.trailingDegree + q.trailingDegree
  proof: by
  by_cases hp : p = 0
  · rw [hp, zero_mul, trailingDegree_zero, top_add]
  by_cases hq : q = 0
  · rw [hq, mul_zero, trailingDegree_zero, add_top]
  · rw [trailingDegree_eq_natTrailingDegree hp, trailingDegree_eq_natTrailingDegree hq,
    trailingDegree_eq_natTrailingDegree (mul_ne_zero hp hq), 

中文:
定理 trailingDegree_mul
  结论: (p * q).trailingDegree = p.trailingDegree + q.trailingDegree
  证明: by
  by_cases hp : p = 0
  · rw [hp, zero_mul, trailingDegree_zero, top_add]
  by_cases hq : q = 0
  · rw [hq, mul_zero, trailingDegree_zero, add_top]
  · rw [trailingDegree_eq_natTrailingDegree hp, trailingDegree_eq_natTrailingDegree hq,
    trailingDegree_eq_natTrailingDegree (mul_ne_zero hp hq), 

Depends on / 依赖: WithTop, WithTop.coe_add, add_top, coe_add, mul_ne_zero, mul_zero, natTrailingDegree_mul, top_add, trailingDegree_eq_natTrailingDegree, trailingDegree_zero, zero_mul
-/
theorem trailingDegree_mul : (p * q).trailingDegree = p.trailingDegree + q.trailingDegree := by
  by_cases hp : p = 0
  · rw [hp, zero_mul, trailingDegree_zero, top_add]
  by_cases hq : q = 0
  · rw [hq, mul_zero, trailingDegree_zero, add_top]
  · rw [trailingDegree_eq_natTrailingDegree hp, trailingDegree_eq_natTrailingDegree hq,
    trailingDegree_eq_natTrailingDegree (mul_ne_zero hp hq), natTrailingDegree_mul hp hq]
    apply WithTop.coe_add

end NoZeroDivisors


section CommRing

variable [CommRing R]

/--
theorem `rootMultiplicity_eq_rootMultiplicity` / 定理 `rootMultiplicity_eq_rootMultiplicity`

English:
theorem rootMultiplicity_eq_rootMultiplicity
  given: {p : R[X]} {t : R}
  proof: by
  classical
  simp_rw [rootMultiplicity_eq_multiplicity, comp_X_add_C_eq_zero_iff]
  congr 1
  rw [C_0]; rw [sub_zero]
  convert! (multiplicity_map_eq <| algEquivAevalXAddC t).symm using 2
  simp [C_eq_algebraMap]

中文:
定理 rootMultiplicity_eq_rootMultiplicity
  条件: {p : R[X]} {t : R}
  证明: by
  classical
  simp_rw [rootMultiplicity_eq_multiplicity, comp_X_add_C_eq_zero_iff]
  congr 1
  rw [C_0]; rw [sub_zero]
  convert! (multiplicity_map_eq <| algEquivAevalXAddC t).symm using 2
  simp [C_eq_algebraMap]

Depends on / 依赖: C_eq_algebraMap, algEquivAevalXAddC, classical, comp_X_add_C_eq_zero_iff, convert, multiplicity_map_eq, rootMultiplicity_eq_multiplicity, simp_rw, sub_zero
-/
theorem rootMultiplicity_eq_rootMultiplicity {p : R[X]} {t : R} :
    p.rootMultiplicity t = (p.comp (X + C t)).rootMultiplicity 0 := by
  classical
  simp_rw [rootMultiplicity_eq_multiplicity, comp_X_add_C_eq_zero_iff]
  congr 1
  rw [C_0]; rw [sub_zero]
  convert! (multiplicity_map_eq <| algEquivAevalXAddC t).symm using 2
  simp [C_eq_algebraMap]

/--
theorem `rootMultiplicity_eq_natTrailingDegree` / 定理 `rootMultiplicity_eq_natTrailingDegree`

English:
theorem rootMultiplicity_eq_natTrailingDegree
  given: {p : R[X]} {t : R}
  proof: rootMultiplicity_eq_rootMultiplicity.trans rootMultiplicity_eq_natTrailingDegree'

中文:
定理 rootMultiplicity_eq_natTrailingDegree
  条件: {p : R[X]} {t : R}
  证明: rootMultiplicity_eq_rootMultiplicity.trans rootMultiplicity_eq_natTrailingDegree'

Depends on / 依赖: rootMultiplicity_eq_natTrailingDegree, rootMultiplicity_eq_rootMultiplicity, rootMultiplicity_eq_rootMultiplicity.trans
-/
theorem rootMultiplicity_eq_natTrailingDegree {p : R[X]} {t : R} :
    p.rootMultiplicity t = (p.comp (X + C t)).natTrailingDegree :=
  rootMultiplicity_eq_rootMultiplicity.trans rootMultiplicity_eq_natTrailingDegree'

section nonZeroDivisors

open scoped nonZeroDivisors

/--
theorem `Monic.mem_nonZeroDivisors` / 定理 `Monic.mem_nonZeroDivisors`

English:
theorem Monic.mem_nonZeroDivisors
  given: {p : R[X]} (h : p.Monic)
  statement: p in R[X]⁰
  proof: mem_nonzeroDivisors_of_coeff_mem _ (h.coeff_natDegree ▸ one_mem R⁰)

中文:
定理 Monic.mem_nonZeroDivisors
  条件: {p : R[X]} (h : p.Monic)
  结论: p in R[X]⁰
  证明: mem_nonzeroDivisors_of_coeff_mem _ (h.coeff_natDegree ▸ one_mem R⁰)

Depends on / 依赖: coeff_natDegree, h.coeff_natDegree, mem_nonzeroDivisors_of_coeff_mem, one_mem
-/
theorem Monic.mem_nonZeroDivisors {p : R[X]} (h : p.Monic) : p in R[X]⁰ :=
  mem_nonzeroDivisors_of_coeff_mem _ (h.coeff_natDegree ▸ one_mem R⁰)

/--
theorem `mem_nonZeroDivisors_of_leadingCoeff` / 定理 `mem_nonZeroDivisors_of_leadingCoeff`

English:
theorem mem_nonZeroDivisors_of_leadingCoeff
  given: {p : R[X]} (h : p.leadingCoeff in R⁰)
  statement: p in R[X]⁰
  proof: mem_nonzeroDivisors_of_coeff_mem _ h

中文:
定理 mem_nonZeroDivisors_of_leadingCoeff
  条件: {p : R[X]} (h : p.leadingCoeff in R⁰)
  结论: p in R[X]⁰
  证明: mem_nonzeroDivisors_of_coeff_mem _ h

Depends on / 依赖: mem_nonzeroDivisors_of_coeff_mem
-/
theorem mem_nonZeroDivisors_of_leadingCoeff {p : R[X]} (h : p.leadingCoeff in R⁰) : p in R[X]⁰ :=
  mem_nonzeroDivisors_of_coeff_mem _ h

/--
theorem `mem_nonZeroDivisors_of_trailingCoeff` / 定理 `mem_nonZeroDivisors_of_trailingCoeff`

English:
theorem mem_nonZeroDivisors_of_trailingCoeff
  given: {p : R[X]} (h : p.trailingCoeff in R⁰)
  statement: p in R[X]⁰
  proof: mem_nonzeroDivisors_of_coeff_mem _ h

中文:
定理 mem_nonZeroDivisors_of_trailingCoeff
  条件: {p : R[X]} (h : p.trailingCoeff in R⁰)
  结论: p in R[X]⁰
  证明: mem_nonzeroDivisors_of_coeff_mem _ h

Depends on / 依赖: mem_nonzeroDivisors_of_coeff_mem
-/
theorem mem_nonZeroDivisors_of_trailingCoeff {p : R[X]} (h : p.trailingCoeff in R⁰) : p in R[X]⁰ :=
  mem_nonzeroDivisors_of_coeff_mem _ h

end nonZeroDivisors

/--
lemma `_root_.Irreducible.aeval_ne_zero_of_natDegree_ne_one` / 引理 `_root_.Irreducible.aeval_ne_zero_of_natDegree_ne_one`

English:
lemma _root_.Irreducible.aeval_ne_zero_of_natDegree_ne_one
  statement: [IsDomain R] [Ring S] [Algebra R S]
  proof: by
  obtain ⟨_, rfl⟩ := hx
  rw [aeval_algebraMap_apply_eq_algebraMap_eval]
exact fun heq => hp.not_isRoot_of_natDegree_ne_one hdeg
FaithfulSMul.algebraMap_injective _ _ map_zero (algebraMap R S) ▸ heq

中文:
引理 _root_.Irreducible.aeval_ne_zero_of_natDegree_ne_one
  结论: [IsDomain R] [Ring S] [Algebra R S]
  证明: by
  obtain ⟨_, rfl⟩ := hx
  rw [aeval_algebraMap_apply_eq_algebraMap_eval]
exact fun heq => hp.not_isRoot_of_natDegree_ne_one hdeg
FaithfulSMul.algebraMap_injective _ _ map_zero (algebraMap R S) ▸ heq

Depends on / 依赖: FaithfulSMul, FaithfulSMul.algebraMap_injective, aeval_algebraMap_apply_eq_algebraMap_eval, algebraMap, algebraMap_injective, hp.not_isRoot_of_natDegree_ne_one, map_zero, not_isRoot_of_natDegree_ne_one
-/
lemma _root_.Irreducible.aeval_ne_zero_of_natDegree_ne_one [IsDomain R] [Ring S] [Algebra R S]
    [FaithfulSMul R S] {p : R[X]} (hp : Irreducible p) (hdeg : p.natDegree != 1) {x : S}
    (hx : x in (algebraMap R S).range) : p.aeval x != 0 := by
  obtain ⟨_, rfl⟩ := hx
  rw [aeval_algebraMap_apply_eq_algebraMap_eval]
exact fun heq => hp.not_isRoot_of_natDegree_ne_one hdeg
FaithfulSMul.algebraMap_injective _ _ map_zero (algebraMap R S) ▸ heq

/--
theorem `natDegree_pos_of_monic_of_aeval_eq_zero` / 定理 `natDegree_pos_of_monic_of_aeval_eq_zero`

English:
theorem natDegree_pos_of_monic_of_aeval_eq_zero
  statement: [Nontrivial R] [Semiring S] [Algebra R S]
  proof: natDegree_pos_of_aeval_root (Monic.ne_zero hp) hx
    ((injective_iff_map_eq_zero (algebraMap R S)).mp (FaithfulSMul.algebraMap_injective R S))

中文:
定理 natDegree_pos_of_monic_of_aeval_eq_zero
  结论: [Nontrivial R] [Semiring S] [Algebra R S]
  证明: natDegree_pos_of_aeval_root (Monic.ne_zero hp) hx
    ((injective_iff_map_eq_zero (algebraMap R S)).mp (FaithfulSMul.algebraMap_injective R S))

Depends on / 依赖: FaithfulSMul, FaithfulSMul.algebraMap_injective, Monic.ne_zero, algebraMap, algebraMap_injective, injective_iff_map_eq_zero, natDegree_pos_of_aeval_root, ne_zero
-/
theorem natDegree_pos_of_monic_of_aeval_eq_zero [Nontrivial R] [Semiring S] [Algebra R S]
    [FaithfulSMul R S] {p : R[X]} (hp : p.Monic) {x : S} (hx : aeval x p = 0) :
    0 < p.natDegree :=
  natDegree_pos_of_aeval_root (Monic.ne_zero hp) hx
    ((injective_iff_map_eq_zero (algebraMap R S)).mp (FaithfulSMul.algebraMap_injective R S))

/--
theorem `rootMultiplicity_mul_X_sub_C_pow` / 定理 `rootMultiplicity_mul_X_sub_C_pow`

English:
theorem rootMultiplicity_mul_X_sub_C_pow
  given: {p : R[X]} {a : R} {n : Nat} (h : p != 0)
  proof: by
.mul_left_ne_zero h .pow n have h2 := monic_X_sub_C a
  refine le_antisymm ?_ ?_
  · rw [rootMultiplicity_le_iff h2, add_assoc, add_comm n, ← add_assoc, pow_add,
      dvd_cancel_right_mem_nonZeroDivisors (monic_X_sub_C a |>.pow n |>.mem_nonZeroDivisors)]
    exact pow_rootMultiplicity_not_dvd h 

中文:
定理 rootMultiplicity_mul_X_sub_C_pow
  条件: {p : R[X]} {a : R} {n : 自然数} (h : p != 0)
  证明: by
.mul_left_ne_zero h .pow n have h2 := monic_X_sub_C a
  refine le_antisymm ?_ ?_
  · rw [rootMultiplicity_le_iff h2, add_assoc, add_comm n, ← add_assoc, pow_add,
      dvd_cancel_right_mem_nonZeroDivisors (monic_X_sub_C a |>.pow n |>.mem_nonZeroDivisors)]
    exact pow_rootMultiplicity_not_dvd h 

Depends on / 依赖: add_assoc, add_comm, dvd_cancel_right_mem_nonZeroDivisors, le_antisymm, le_rootMultiplicity_iff, mem_nonZeroDivisors, monic_X_sub_C, mul_dvd_mul_right, mul_left_ne_zero, pow_add, pow_rootMultiplicity_dvd, pow_rootMultiplicity_not_dvd, rootMultiplicity_le_iff
-/
theorem rootMultiplicity_mul_X_sub_C_pow {p : R[X]} {a : R} {n : Nat} (h : p != 0) :
    (p * (X - C a) ^ n).rootMultiplicity a = p.rootMultiplicity a + n := by
.mul_left_ne_zero h .pow n have h2 := monic_X_sub_C a
  refine le_antisymm ?_ ?_
  · rw [rootMultiplicity_le_iff h2, add_assoc, add_comm n, ← add_assoc, pow_add,
      dvd_cancel_right_mem_nonZeroDivisors (monic_X_sub_C a |>.pow n |>.mem_nonZeroDivisors)]
    exact pow_rootMultiplicity_not_dvd h a
  · rw [le_rootMultiplicity_iff h2, pow_add]
    exact mul_dvd_mul_right (pow_rootMultiplicity_dvd p a) _

/--
theorem `rootMultiplicity_X_sub_C_pow` / 定理 `rootMultiplicity_X_sub_C_pow`

English:
theorem rootMultiplicity_X_sub_C_pow
  given: [Nontrivial R] (a : R) (n : Nat)
  proof: by
  have := rootMultiplicity_mul_X_sub_C_pow (a := a) (n := n) C.map_one_ne_zero
  rwa [rootMultiplicity_C, map_one, one_mul, zero_add] at this

中文:
定理 rootMultiplicity_X_sub_C_pow
  条件: [Nontrivial R] (a : R) (n : 自然数)
  证明: by
  have := rootMultiplicity_mul_X_sub_C_pow (a := a) (n := n) C.map_one_ne_zero
  rwa [rootMultiplicity_C, map_one, one_mul, zero_add] at this

Depends on / 依赖: C.map_one_ne_zero, map_one, map_one_ne_zero, one_mul, rootMultiplicity_C, rootMultiplicity_mul_X_sub_C_pow, zero_add
-/
theorem rootMultiplicity_X_sub_C_pow [Nontrivial R] (a : R) (n : Nat) :
    rootMultiplicity a ((X - C a) ^ n) = n := by
  have := rootMultiplicity_mul_X_sub_C_pow (a := a) (n := n) C.map_one_ne_zero
  rwa [rootMultiplicity_C, map_one, one_mul, zero_add] at this

/--
theorem `rootMultiplicity_X_sub_C_self` / 定理 `rootMultiplicity_X_sub_C_self`

English:
theorem rootMultiplicity_X_sub_C_self
  given: [Nontrivial R] {x : R}
  proof: pow_one (X - C x) ▸ rootMultiplicity_X_sub_C_pow x 1

中文:
定理 rootMultiplicity_X_sub_C_self
  条件: [Nontrivial R] {x : R}
  证明: pow_one (X - C x) ▸ rootMultiplicity_X_sub_C_pow x 1

Depends on / 依赖: pow_one, rootMultiplicity_X_sub_C_pow
-/
theorem rootMultiplicity_X_sub_C_self [Nontrivial R] {x : R} :
    rootMultiplicity x (X - C x) = 1 :=
  pow_one (X - C x) ▸ rootMultiplicity_X_sub_C_pow x 1

/--
theorem `rootMultiplicity_X_sub_C` / 定理 `rootMultiplicity_X_sub_C`

English:
theorem rootMultiplicity_X_sub_C
  given: [Nontrivial R] [DecidableEq R] {x y : R}
  proof: by
  split_ifs with hxy
  · rw [hxy]
    exact rootMultiplicity_X_sub_C_self
  exact rootMultiplicity_eq_zero (mt root_X_sub_C.mp (Ne.symm hxy))

中文:
定理 rootMultiplicity_X_sub_C
  条件: [Nontrivial R] [DecidableEq R] {x y : R}
  证明: by
  split_ifs with hxy
  · rw [hxy]
    exact rootMultiplicity_X_sub_C_self
  exact rootMultiplicity_eq_zero (mt root_X_sub_C.mp (Ne.symm hxy))

Depends on / 依赖: Ne.symm, rootMultiplicity_X_sub_C_self, rootMultiplicity_eq_zero, root_X_sub_C, root_X_sub_C.mp, split_ifs
-/
theorem rootMultiplicity_X_sub_C [Nontrivial R] [DecidableEq R] {x y : R} :
    rootMultiplicity x (X - C y) = if x = y then 1 else 0 := by
  split_ifs with hxy
  · rw [hxy]
    exact rootMultiplicity_X_sub_C_self
  exact rootMultiplicity_eq_zero (mt root_X_sub_C.mp (Ne.symm hxy))

/--
theorem `rootMultiplicity_comp_C_mul_X_add_C_le` / 定理 `rootMultiplicity_comp_C_mul_X_add_C_le`

English:
theorem rootMultiplicity_comp_C_mul_X_add_C_le
  given: (p : R[X]) (a b c : R) (ha : IsUnit a)
  proof: by
  let : Invertible a := ha.invertible
  rcases eq_or_ne p 0 with rfl | hp; · simp
  rw [le_rootMultiplicity_iff hp]
  have h := pow_rootMultiplicity_dvd (p.comp (C a * X + C b)) c
  rw [dvd_comp_C_mul_X_add_C_iff]; rw [pow_comp] at h
  refine (pow_dvd_pow_of_dvd ((isUnit_C.mpr ha).dvd_mul_left.mp

中文:
定理 rootMultiplicity_comp_C_mul_X_add_C_le
  条件: (p : R[X]) (a b c : R) (ha : IsUnit a)
  证明: by
  let : Invertible a := ha.invertible
  rcases eq_or_ne p 0 with rfl | hp; · simp
  rw [le_rootMultiplicity_iff hp]
  have h := pow_rootMultiplicity_dvd (p.comp (C a * X + C b)) c
  rw [dvd_comp_C_mul_X_add_C_iff]; rw [pow_comp] at h
  refine (pow_dvd_pow_of_dvd ((isUnit_C.mpr ha).dvd_mul_left.mp
-/
private theorem rootMultiplicity_comp_C_mul_X_add_C_le (p : R[X]) (a b c : R) (ha : IsUnit a) :
    (p.comp (C a * X + C b)).rootMultiplicity c <= p.rootMultiplicity (a * c + b) := by
  let : Invertible a := ha.invertible
  rcases eq_or_ne p 0 with rfl | hp; · simp
  rw [le_rootMultiplicity_iff hp]
  have h := pow_rootMultiplicity_dvd (p.comp (C a * X + C b)) c
  rw [dvd_comp_C_mul_X_add_C_iff]; rw [pow_comp] at h
  refine (pow_dvd_pow_of_dvd ((isUnit_C.mpr ha).dvd_mul_left.mp (dvd_of_eq ?_)) _).trans h
  simp [← map_mul, mul_sub, ← mul_assoc, sub_sub, add_comm, mul_add]

/--
theorem `rootMultiplicity_comp_C_mul_X_add_C` / 定理 `rootMultiplicity_comp_C_mul_X_add_C`

English:
theorem rootMultiplicity_comp_C_mul_X_add_C
  given: (p : R[X]) (a b c : R) (ha : IsUnit a)
  proof: by
  let : Invertible a := ha.invertible
  apply le_antisymm (rootMultiplicity_comp_C_mul_X_add_C_le p a b c ha)
  have := rootMultiplicity_comp_C_mul_X_add_C_le
    (p.comp (C a * X + C b)) ⅟a (- ⅟a * b) (a * c + b) (isUnit_of_invertible ⅟a)
  simpa [comp_assoc, mul_add, ← mul_assoc, ← map_mul] usi

中文:
定理 rootMultiplicity_comp_C_mul_X_add_C
  条件: (p : R[X]) (a b c : R) (ha : IsUnit a)
  证明: by
  let : Invertible a := ha.invertible
  apply le_antisymm (rootMultiplicity_comp_C_mul_X_add_C_le p a b c ha)
  have := rootMultiplicity_comp_C_mul_X_add_C_le
    (p.comp (C a * X + C b)) ⅟a (- ⅟a * b) (a * c + b) (isUnit_of_invertible ⅟a)
  simpa [comp_assoc, mul_add, ← mul_assoc, ← map_mul] usi

Depends on / 依赖: Invertible, comp_assoc, ha.invertible, invertible, isUnit_of_invertible, le_antisymm, map_mul, mul_add, mul_assoc, p.comp, rootMultiplicity_comp_C_mul_X_add_C_le
-/
theorem rootMultiplicity_comp_C_mul_X_add_C (p : R[X]) (a b c : R) (ha : IsUnit a) :
    (p.comp (C a * X + C b)).rootMultiplicity c = p.rootMultiplicity (a * c + b) := by
  let : Invertible a := ha.invertible
  apply le_antisymm (rootMultiplicity_comp_C_mul_X_add_C_le p a b c ha)
  have := rootMultiplicity_comp_C_mul_X_add_C_le
    (p.comp (C a * X + C b)) ⅟a (- ⅟a * b) (a * c + b) (isUnit_of_invertible ⅟a)
  simpa [comp_assoc, mul_add, ← mul_assoc, ← map_mul] using this

/--
theorem `rootMultiplicity_mul'` / 定理 `rootMultiplicity_mul'`

English:
theorem rootMultiplicity_mul'
  statement: {p q : R[X]} {x : R}
  proof: by
  simp_rw [eval_divByMonic_eq_trailingCoeff_comp] at hpq
  simp_rw [rootMultiplicity_eq_natTrailingDegree, mul_comp, natTrailingDegree_mul' hpq]

中文:
定理 rootMultiplicity_mul'
  结论: {p q : R[X]} {x : R}
  证明: by
  simp_rw [eval_divByMonic_eq_trailingCoeff_comp] at hpq
  simp_rw [rootMultiplicity_eq_natTrailingDegree, mul_comp, natTrailingDegree_mul' hpq]

Depends on / 依赖: eval_divByMonic_eq_trailingCoeff_comp, mul_comp, natTrailingDegree_mul, rootMultiplicity_eq_natTrailingDegree, simp_rw
-/
theorem rootMultiplicity_mul' {p q : R[X]} {x : R}
    (hpq : (p /ₘ (X - C x) ^ p.rootMultiplicity x).eval x *
      (q /ₘ (X - C x) ^ q.rootMultiplicity x).eval x != 0) :
    rootMultiplicity x (p * q) = rootMultiplicity x p + rootMultiplicity x q := by
  simp_rw [eval_divByMonic_eq_trailingCoeff_comp] at hpq
  simp_rw [rootMultiplicity_eq_natTrailingDegree, mul_comp, natTrailingDegree_mul' hpq]

/--
theorem `Monic.neg_one_pow_natDegree_mul_comp_neg_X` / 定理 `Monic.neg_one_pow_natDegree_mul_comp_neg_X`

English:
theorem Monic.neg_one_pow_natDegree_mul_comp_neg_X
  given: {p : R[X]} (hp : p.Monic)
  proof: by
  simp only [Monic]
  calc
    ((-1) ^ p.natDegree * p.comp (-X)).leadingCoeff =
        (p.comp (-X) * C ((-1) ^ p.natDegree)).leadingCoeff := by
      simp [mul_comm]
    _ = 1 := by
      apply monic_mul_C_of_leadingCoeff_mul_eq_one
      simp [← pow_add, hp]

中文:
定理 Monic.neg_one_pow_natDegree_mul_comp_neg_X
  条件: {p : R[X]} (hp : p.Monic)
  证明: by
  simp only [Monic]
  calc
    ((-1) ^ p.natDegree * p.comp (-X)).leadingCoeff =
        (p.comp (-X) * C ((-1) ^ p.natDegree)).leadingCoeff := by
      simp [mul_comm]
    _ = 1 := by
      apply monic_mul_C_of_leadingCoeff_mul_eq_one
      simp [← pow_add, hp]

Depends on / 依赖: leadingCoeff, monic_mul_C_of_leadingCoeff_mul_eq_one, mul_comm, natDegree, p.comp, p.natDegree, pow_add
-/
theorem Monic.neg_one_pow_natDegree_mul_comp_neg_X {p : R[X]} (hp : p.Monic) :
    ((-1) ^ p.natDegree * p.comp (-X)).Monic := by
  simp only [Monic]
  calc
    ((-1) ^ p.natDegree * p.comp (-X)).leadingCoeff =
        (p.comp (-X) * C ((-1) ^ p.natDegree)).leadingCoeff := by
      simp [mul_comm]
    _ = 1 := by
      apply monic_mul_C_of_leadingCoeff_mul_eq_one
      simp [← pow_add, hp]

variable [IsDomain R] {p q : R[X]}

/--
theorem `degree_eq_degree_of_associated` / 定理 `degree_eq_degree_of_associated`

English:
theorem degree_eq_degree_of_associated
  given: (h : Associated p q)
  statement: degree p = degree q
  proof: by
  let ⟨u, hu⟩ := h
  simp [hu.symm]

中文:
定理 degree_eq_degree_of_associated
  条件: (h : Associated p q)
  结论: degree p = degree q
  证明: by
  let ⟨u, hu⟩ := h
  simp [hu.symm]

Depends on / 依赖: hu.symm
-/
theorem degree_eq_degree_of_associated (h : Associated p q) : degree p = degree q := by
  let ⟨u, hu⟩ := h
  simp [hu.symm]

/--
theorem `prime_X_sub_C` / 定理 `prime_X_sub_C`

English:
theorem prime_X_sub_C
  given: (r : R)
  statement: Prime (X - C r)
  proof: ⟨X_sub_C_ne_zero r, not_isUnit_X_sub_C r, fun _ _ => by
    simp_rw [dvd_iff_isRoot, IsRoot.def, eval_mul, mul_eq_zero]
    exact id⟩

中文:
定理 prime_X_sub_C
  条件: (r : R)
  结论: Prime (X - C r)
  证明: ⟨X_sub_C_ne_zero r, not_isUnit_X_sub_C r, fun _ _ => by
    simp_rw [dvd_iff_isRoot, IsRoot.def, eval_mul, mul_eq_zero]
    exact id⟩

Depends on / 依赖: IsRoot, IsRoot.def, X_sub_C_ne_zero, dvd_iff_isRoot, eval_mul, mul_eq_zero, not_isUnit_X_sub_C, simp_rw
-/
theorem prime_X_sub_C (r : R) : Prime (X - C r) :=
  ⟨X_sub_C_ne_zero r, not_isUnit_X_sub_C r, fun _ _ => by
    simp_rw [dvd_iff_isRoot, IsRoot.def, eval_mul, mul_eq_zero]
    exact id⟩

/--
theorem `prime_X` / 定理 `prime_X`

English:
theorem prime_X
  statement: Prime (X : R[X])
  proof: by
  convert! prime_X_sub_C (0 : R)
  simp

中文:
定理 prime_X
  结论: Prime (X : R[X])
  证明: by
  convert! prime_X_sub_C (0 : R)
  simp

Depends on / 依赖: convert, prime_X_sub_C
-/
theorem prime_X : Prime (X : R[X]) := by
  convert! prime_X_sub_C (0 : R)
  simp

/--
theorem `Monic.prime_of_degree_eq_one` / 定理 `Monic.prime_of_degree_eq_one`

English:
theorem Monic.prime_of_degree_eq_one
  given: (hp1 : degree p = 1) (hm : Monic p)
  statement: Prime p
  proof: have : p = X - C (-p.coeff 0) := by simpa [hm.leadingCoeff] using eq_X_add_C_of_degree_eq_one hp1
  this.symm ▸ prime_X_sub_C _

中文:
定理 Monic.prime_of_degree_eq_one
  条件: (hp1 : degree p = 1) (hm : Monic p)
  结论: Prime p
  证明: have : p = X - C (-p.coeff 0) := by simpa [hm.leadingCoeff] using eq_X_add_C_of_degree_eq_one hp1
  this.symm ▸ prime_X_sub_C _

Depends on / 依赖: eq_X_add_C_of_degree_eq_one, hm.leadingCoeff, leadingCoeff, p.coeff, prime_X_sub_C, this.symm
-/
theorem Monic.prime_of_degree_eq_one (hp1 : degree p = 1) (hm : Monic p) : Prime p :=
  have : p = X - C (-p.coeff 0) := by simpa [hm.leadingCoeff] using eq_X_add_C_of_degree_eq_one hp1
  this.symm ▸ prime_X_sub_C _

/--
theorem `irreducible_X_sub_C` / 定理 `irreducible_X_sub_C`

English:
theorem irreducible_X_sub_C
  given: (r : R)
  statement: Irreducible (X - C r)
  proof: (prime_X_sub_C r).irreducible

中文:
定理 irreducible_X_sub_C
  条件: (r : R)
  结论: Irreducible (X - C r)
  证明: (prime_X_sub_C r).irreducible

Depends on / 依赖: irreducible, prime_X_sub_C
-/
theorem irreducible_X_sub_C (r : R) : Irreducible (X - C r) :=
  (prime_X_sub_C r).irreducible

/--
theorem `irreducible_X` / 定理 `irreducible_X`

English:
theorem irreducible_X
  statement: Irreducible (X : R[X])
  proof: Prime.irreducible prime_X

中文:
定理 irreducible_X
  结论: Irreducible (X : R[X])
  证明: Prime.irreducible prime_X

Depends on / 依赖: Prime.irreducible, irreducible, prime_X
-/
theorem irreducible_X : Irreducible (X : R[X]) :=
  Prime.irreducible prime_X

/--
theorem `Monic.irreducible_of_degree_eq_one` / 定理 `Monic.irreducible_of_degree_eq_one`

English:
theorem Monic.irreducible_of_degree_eq_one
  given: (hp1 : degree p = 1) (hm : Monic p)
  statement: Irreducible p
  proof: (hm.prime_of_degree_eq_one hp1).irreducible

中文:
定理 Monic.irreducible_of_degree_eq_one
  条件: (hp1 : degree p = 1) (hm : Monic p)
  结论: Irreducible p
  证明: (hm.prime_of_degree_eq_one hp1).irreducible

Depends on / 依赖: hm.prime_of_degree_eq_one, irreducible, prime_of_degree_eq_one
-/
theorem Monic.irreducible_of_degree_eq_one (hp1 : degree p = 1) (hm : Monic p) : Irreducible p :=
  (hm.prime_of_degree_eq_one hp1).irreducible

/--
theorem `irreducible_of_degree_eq_one_of_isRelPrime_coeff` / 定理 `irreducible_of_degree_eq_one_of_isRelPrime_coeff`

English:
theorem irreducible_of_degree_eq_one_of_isRelPrime_coeff
  proof: by
    obtain ⟨u, -, h⟩ := isUnit_iff.mp h
    apply not_le.mpr (zero_lt_one' (WithBot Nat))
    simp [← hp, ← h, degree_C_le]
  isUnit_or_isUnit f g h := by
    wlog! H : f.degree <= g.degree generalizing f g
    · rw [mul_comm] at h
      exact (this g f h H.le).symm
    left
    rw [h]; rw [degre

中文:
定理 irreducible_of_degree_eq_one_of_isRelPrime_coeff
  证明: by
    obtain ⟨u, -, h⟩ := isUnit_iff.mp h
    apply not_le.mpr (zero_lt_one' (WithBot Nat))
    simp [← hp, ← h, degree_C_le]
  isUnit_or_isUnit f g h := by
    wlog! H : f.degree <= g.degree generalizing f g
    · rw [mul_comm] at h
      exact (this g f h H.le).symm
    left
    rw [h]; rw [degre

Depends on / 依赖: H.le, IsUnit, IsUnit.map, Nat.WithBot.add_eq_one_iff, WithBot, add_eq_one_iff, coeff_C_mu, coeff_C_mul, degree, degree_C_le, degree_mul, eq_C_of_degree_eq_zero, f.degree, f.eq_C_of_degree_eq_zero, g.degree, generalizing, isUnit_iff, isUnit_iff.mp, isUnit_or_isUnit, mul_comm
-/
theorem irreducible_of_degree_eq_one_of_isRelPrime_coeff
    {p : R[X]} (hp : p.degree = 1) (hc : IsRelPrime (p.coeff 0) (p.coeff 1)) :
    Irreducible p where
  not_isUnit h := by
    obtain ⟨u, -, h⟩ := isUnit_iff.mp h
    apply not_le.mpr (zero_lt_one' (WithBot Nat))
    simp [← hp, ← h, degree_C_le]
  isUnit_or_isUnit f g h := by
    wlog! H : f.degree <= g.degree generalizing f g
    · rw [mul_comm] at h
      exact (this g f h H.le).symm
    left
    rw [h]; rw [degree_mul]; rw [Nat.WithBot.add_eq_one_iff] at hp
    rcases hp with ⟨hf, hg⟩ | ⟨hf, hg⟩; swap
    · simp [← not_lt, hf, hg] at H
    replace hf := f.eq_C_of_degree_eq_zero hf
    rw [hf]
    apply IsUnit.map C
    rw [h]; rw [hf]; rw [coeff_C_mul]; rw [coeff_C_mul] at hc
    apply hc <;> simp

/--
theorem `irreducible_C_mul_X_add_C` / 定理 `irreducible_C_mul_X_add_C`

English:
theorem irreducible_C_mul_X_add_C
  given: {a b : R} (ha : a != 0) (hab : IsRelPrime a b)
  proof: by
  apply irreducible_of_degree_eq_one_of_isRelPrime_coeff
  · compute_degree!
  · simpa using hab.symm

中文:
定理 irreducible_C_mul_X_add_C
  条件: {a b : R} (ha : a != 0) (hab : IsRelPrime a b)
  证明: by
  apply irreducible_of_degree_eq_one_of_isRelPrime_coeff
  · compute_degree!
  · simpa using hab.symm

Depends on / 依赖: compute_degree, hab.symm, irreducible_of_degree_eq_one_of_isRelPrime_coeff
-/
theorem irreducible_C_mul_X_add_C {a b : R} (ha : a != 0) (hab : IsRelPrime a b) :
    Irreducible (C a * X + C b) := by
  apply irreducible_of_degree_eq_one_of_isRelPrime_coeff
  · compute_degree!
  · simpa using hab.symm

/--
lemma `aeval_ne_zero_of_isCoprime` / 引理 `aeval_ne_zero_of_isCoprime`

English:
lemma aeval_ne_zero_of_isCoprime
  statement: {R} [CommSemiring R] [Nontrivial S] [Semiring S] [Algebra R S]
  proof: by
  by_contra! ⟨hp, hq⟩
  rcases h with ⟨_, _, h⟩
  apply_fun aeval s at h
  simp only [map_add, map_mul, map_one, hp, hq, mul_zero, add_zero, zero_ne_one] at h

中文:
引理 aeval_ne_zero_of_isCoprime
  结论: {R} [CommSemiring R] [Nontrivial S] [Semiring S] [Algebra R S]
  证明: by
  by_contra! ⟨hp, hq⟩
  rcases h with ⟨_, _, h⟩
  apply_fun aeval s at h
  simp only [map_add, map_mul, map_one, hp, hq, mul_zero, add_zero, zero_ne_one] at h

Depends on / 依赖: add_zero, apply_fun, map_add, map_mul, map_one, mul_zero, zero_ne_one
-/
lemma aeval_ne_zero_of_isCoprime {R} [CommSemiring R] [Nontrivial S] [Semiring S] [Algebra R S]
    {p q : R[X]} (h : IsCoprime p q) (s : S) : aeval s p != 0 ∨ aeval s q != 0 := by
  by_contra! ⟨hp, hq⟩
  rcases h with ⟨_, _, h⟩
  apply_fun aeval s at h
  simp only [map_add, map_mul, map_one, hp, hq, mul_zero, add_zero, zero_ne_one] at h

/--
theorem `isCoprime_X_sub_C_of_isUnit_sub` / 定理 `isCoprime_X_sub_C_of_isUnit_sub`

English:
theorem isCoprime_X_sub_C_of_isUnit_sub
  given: {R} [CommRing R] {a b : R} (h : IsUnit (a - b))
  proof: ⟨-C h.unit⁻¹.val, C h.unit⁻¹.val, by
    rw [neg_mul_comm]; rw [← left_distrib]; rw [neg_add_eq_sub]; rw [sub_sub_sub_cancel_left]; rw [← C_sub]; rw [← C_mul]
    rw [← C_1]
    congr
    exact h.val_inv_mul⟩

中文:
定理 isCoprime_X_sub_C_of_isUnit_sub
  条件: {R} [CommRing R] {a b : R} (h : IsUnit (a - b))
  证明: ⟨-C h.unit⁻¹.val, C h.unit⁻¹.val, by
    rw [neg_mul_comm]; rw [← left_distrib]; rw [neg_add_eq_sub]; rw [sub_sub_sub_cancel_left]; rw [← C_sub]; rw [← C_mul]
    rw [← C_1]
    congr
    exact h.val_inv_mul⟩

Depends on / 依赖: C_mul, C_sub, h.unit, h.val_inv_mul, left_distrib, neg_add_eq_sub, neg_mul_comm, sub_sub_sub_cancel_left, val_inv_mul
-/
theorem isCoprime_X_sub_C_of_isUnit_sub {R} [CommRing R] {a b : R} (h : IsUnit (a - b)) :
    IsCoprime (X - C a) (X - C b) :=
  ⟨-C h.unit⁻¹.val, C h.unit⁻¹.val, by
    rw [neg_mul_comm]; rw [← left_distrib]; rw [neg_add_eq_sub]; rw [sub_sub_sub_cancel_left]; rw [← C_sub]; rw [← C_mul]
    rw [← C_1]
    congr
    exact h.val_inv_mul⟩

open scoped Function in -- required for scoped `on` notation
/--
theorem `pairwise_coprime_X_sub_C` / 定理 `pairwise_coprime_X_sub_C`

English:
theorem pairwise_coprime_X_sub_C
  given: {K} [Field K] {I : Type v} {s : I -> K} (H : Function.Injective s)
  proof: fun _ _ hij =>
  isCoprime_X_sub_C_of_isUnit_sub (sub_ne_zero_of_ne <| H.ne hij).isUnit

中文:
定理 pairwise_coprime_X_sub_C
  条件: {K} [Field K] {I : 类型v} {s : I -> K} (H : Function.Injective s)
  证明: fun _ _ hij =>
  isCoprime_X_sub_C_of_isUnit_sub (sub_ne_zero_of_ne <| H.ne hij).isUnit
-/
theorem pairwise_coprime_X_sub_C {K} [Field K] {I : Type v} {s : I -> K} (H : Function.Injective s) :
    Pairwise (IsCoprime on fun i : I => X - C (s i)) := fun _ _ hij =>
  isCoprime_X_sub_C_of_isUnit_sub (sub_ne_zero_of_ne <| H.ne hij).isUnit

/--
theorem `rootMultiplicity_mul` / 定理 `rootMultiplicity_mul`

English:
theorem rootMultiplicity_mul
  given: {p q : R[X]} {x : R} (hpq : p * q != 0)
  proof: by
  classical
  have hp : p != 0 := left_ne_zero_of_mul hpq
  have hq : q != 0 := right_ne_zero_of_mul hpq
  rw [rootMultiplicity_eq_multiplicity (p * q)]; rw [if_neg hpq]; rw [rootMultiplicity_eq_multiplicity p]; rw [if_neg hp]; rw [rootMultiplicity_eq_multiplicity q]; rw [if_neg hq]; rw [multipli

中文:
定理 rootMultiplicity_mul
  条件: {p q : R[X]} {x : R} (hpq : p * q != 0)
  证明: by
  classical
  have hp : p != 0 := left_ne_zero_of_mul hpq
  have hq : q != 0 := right_ne_zero_of_mul hpq
  rw [rootMultiplicity_eq_multiplicity (p * q)]; rw [if_neg hpq]; rw [rootMultiplicity_eq_multiplicity p]; rw [if_neg hp]; rw [rootMultiplicity_eq_multiplicity q]; rw [if_neg hq]; rw [multipli

Depends on / 依赖: classical, finiteMultiplicity_X_sub_C, if_neg, left_ne_zero_of_mul, multiplicity_mul, prime_X_sub_C, right_ne_zero_of_mul, rootMultiplicity_eq_multiplicity
-/
theorem rootMultiplicity_mul {p q : R[X]} {x : R} (hpq : p * q != 0) :
    rootMultiplicity x (p * q) = rootMultiplicity x p + rootMultiplicity x q := by
  classical
  have hp : p != 0 := left_ne_zero_of_mul hpq
  have hq : q != 0 := right_ne_zero_of_mul hpq
  rw [rootMultiplicity_eq_multiplicity (p * q)]; rw [if_neg hpq]; rw [rootMultiplicity_eq_multiplicity p]; rw [if_neg hp]; rw [rootMultiplicity_eq_multiplicity q]; rw [if_neg hq]; rw [multiplicity_mul (prime_X_sub_C x) (finiteMultiplicity_X_sub_C _ hpq)]

open Multiset in
/--
theorem `exists_multiset_roots` / 定理 `exists_multiset_roots`

English:
theorem exists_multiset_roots
  given: [DecidableEq R]
  proof: Classical.propDecidable (exists x, IsRoot p x)
    if h : exists x, IsRoot p x then
      let ⟨x, hx⟩ := h
      have hpd : 0 < degree p := degree_pos_of_root hp hx
      have hd0 : p /ₘ (X - C x) != 0 := fun h => by
        rw [← mul_divByMonic_eq_iff_isRoot.2 hx]; rw [h]; rw [mul_zero] at hp; exac

中文:
定理 exists_multiset_roots
  条件: [DecidableEq R]
  证明: Classical.propDecidable (exists x, IsRoot p x)
    if h : exists x, IsRoot p x then
      let ⟨x, hx⟩ := h
      have hpd : 0 < degree p := degree_pos_of_root hp hx
      have hd0 : p /ₘ (X - C x) != 0 := fun h => by
        rw [← mul_divByMonic_eq_iff_isRoot.2 hx]; rw [h]; rw [mul_zero] at hp; exac

Depends on / 依赖: Classical, Classical.propDecidable, IsRoot, propDecidable
-/
theorem exists_multiset_roots [DecidableEq R] :
    forall {p : R[X]} (_ : p != 0), exists s : Multiset R,
      (Multiset.card s : WithBot Nat) <= degree p ∧ forall a, s.count a = rootMultiplicity a p
  | p, hp =>
    haveI := Classical.propDecidable (exists x, IsRoot p x)
    if h : exists x, IsRoot p x then
      let ⟨x, hx⟩ := h
      have hpd : 0 < degree p := degree_pos_of_root hp hx
      have hd0 : p /ₘ (X - C x) != 0 := fun h => by
        rw [← mul_divByMonic_eq_iff_isRoot.2 hx]; rw [h]; rw [mul_zero] at hp; exact hp rfl
      have wf : degree (p /ₘ (X - C x)) < degree p :=
        degree_divByMonic_lt _ _ hp ((degree_X_sub_C x).symm ▸ by decide)
      let ⟨t, htd, htr⟩ := @exists_multiset_roots _ (p /ₘ (X - C x)) hd0
      have hdeg : degree (X - C x) <= degree p := by
        simpa using Nat.WithBot.one_le_iff_zero_lt.mpr hpd
      have hdiv0 : p /ₘ (X - C x) != 0 :=
mt (divByMonic_eq_zero_iff (monic_X_sub_C x)).1 not_lt.2 hdeg
      ⟨x ::ₘ t,
        calc
          (card (x ::ₘ t) : WithBot Nat) = Multiset.card t + 1 := by
            congr
            exact mod_cast Multiset.card_cons _ _
          _ <= degree p := by
            rw [← degree_add_divByMonic (monic_X_sub_C x) hdeg]; rw [degree_X_sub_C]; rw [add_comm]
            exact add_le_add (le_refl (1 : WithBot Nat)) htd,
        by
          intro a
          conv_rhs => rw [← mul_divByMonic_eq_iff_isRoot.mpr hx]
          rw [rootMultiplicity_mul (mul_ne_zero (X_sub_C_ne_zero x) hdiv0)]; rw [rootMultiplicity_X_sub_C]; rw [← htr a]
          split_ifs with ha
          · rw [ha, count_cons_self, add_comm]
          · rw [count_cons_of_ne ha, zero_add]⟩
    else
      ⟨0, (degree_eq_natDegree hp).symm ▸ WithBot.coe_le_coe.2 (Nat.zero_le _), by
        intro a
        rw [count_zero]; rw [rootMultiplicity_eq_zero (not_exists.mp h a)]⟩
termination_by p => natDegree p
decreasing_by {
  apply (Nat.cast_lt (α := WithBot Nat)).mp
  simp only [degree_eq_natDegree hp, degree_eq_natDegree hd0] at wf
  assumption}

end CommRing

end Polynomial
