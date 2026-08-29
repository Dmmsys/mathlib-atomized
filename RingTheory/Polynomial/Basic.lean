/-
Copyright (c) 2019 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import Mathlib.Algebra.MvPolynomial.CommRing
public import Mathlib.Algebra.MvPolynomial.Equiv
public import Mathlib.Algebra.Polynomial.BigOperators
public import Mathlib.Algebra.Ring.GeomSum
public import Mathlib.RingTheory.Noetherian.Basic

/-!
# Ring-theoretic supplement of Algebra.Polynomial.

## Main results
* `MvPolynomial.isDomain`:
  If a ring is an integral domain, then so is its polynomial ring over finitely many variables.
* `Polynomial.isNoetherianRing`:
  Hilbert basis theorem, that if a ring is Noetherian then so is its polynomial ring.
-/

@[expose] public section

noncomputable section

open Polynomial

open Finset

universe u v w

variable {R : Type u} {S : Type*}

namespace Polynomial

section Semiring

variable [Semiring R]

/--
Instance `instCharP` / 实例 `instCharP`

English:
instance instCharP
  signature: (p : Nat) [h : CharP R p]
  body: let ⟨h⟩ := h
  ⟨fun n => by rw [← map_natCast C, ← C_0, C_inj, h]⟩

中文:
实例 instCharP
  签名: (p : 自然数) [h : 特征p R p]
  定义体: let ⟨h⟩ := h
  ⟨fun n => by rw [← map_natCast C, ← C_0, C_inj, h]⟩

Depends on / 依赖: C_inj, map_natCast
-/
instance instCharP (p : Nat) [h : CharP R p] : CharP R[X] p :=
  let ⟨h⟩ := h
  ⟨fun n => by rw [← map_natCast C, ← C_0, C_inj, h]⟩

/--
Instance `instExpChar` / 实例 `instExpChar`

English:
instance instExpChar
  signature: (p : Nat) [h : ExpChar R p]
  body: by
  cases h; exacts [ExpChar.zero, ExpChar.prime ‹_›]

中文:
实例 instExpChar
  签名: (p : 自然数) [h : ExpChar R p]
  定义体: by
  cases h; exacts [ExpChar.zero, ExpChar.prime ‹_›]

Depends on / 依赖: ExpChar, ExpChar.prime, ExpChar.zero, exacts
-/
instance instExpChar (p : Nat) [h : ExpChar R p] : ExpChar R[X] p := by
  cases h; exacts [ExpChar.zero, ExpChar.prime ‹_›]

variable (R)

/--
Definition of `degreeLE` / `degreeLE` 的定义

English:
definition degreeLE
  signature: (n : WithBot Nat)
  body: ⨅ k : Nat, ⨅ _ : ↑k > n, LinearMap.ker (lcoeff R k)

中文:
定义 degreeLE
  签名: (n : WithBot 自然数)
  定义体: ⨅ k : Nat, ⨅ _ : ↑k > n, LinearMap.ker (lcoeff R k)

Depends on / 依赖: LinearMap, LinearMap.ker, lcoeff
-/
def degreeLE (n : WithBot Nat) : Submodule R R[X] :=
  ⨅ k : Nat, ⨅ _ : ↑k > n, LinearMap.ker (lcoeff R k)

/--
Definition of `degreeLT` / `degreeLT` 的定义

English:
definition degreeLT
  signature: (n : Nat)
  body: ⨅ k : Nat, ⨅ (_ : k >= n), LinearMap.ker (lcoeff R k)

中文:
定义 degreeLT
  签名: (n : 自然数)
  定义体: ⨅ k : Nat, ⨅ (_ : k >= n), LinearMap.ker (lcoeff R k)

Depends on / 依赖: LinearMap, LinearMap.ker, lcoeff
-/
def degreeLT (n : Nat) : Submodule R R[X] :=
  ⨅ k : Nat, ⨅ (_ : k >= n), LinearMap.ker (lcoeff R k)

variable {R}

/--
theorem `mem_degreeLE` / 定理 `mem_degreeLE`

English:
theorem mem_degreeLE
  given: {n : WithBot Nat} {f : R[X]}
  statement: f in degreeLE R n ↔ degree f <= n
  proof: by
  simp only [degreeLE, Submodule.mem_iInf, degree_le_iff_coeff_zero, LinearMap.mem_ker]; rfl

@[gcongr, mono]

中文:
定理 mem_degreeLE
  条件: {n : WithBot 自然数} {f : R[X]}
  结论: f in degreeLE R n ↔ degree f <= n
  证明: by
  simp only [degreeLE, Submodule.mem_iInf, degree_le_iff_coeff_zero, LinearMap.mem_ker]; rfl

@[gcongr, mono]

Depends on / 依赖: LinearMap, LinearMap.mem_ker, Submodule, Submodule.mem_iInf, degreeLE, degree_le_iff_coeff_zero, mem_iInf, mem_ker
-/
theorem mem_degreeLE {n : WithBot Nat} {f : R[X]} : f in degreeLE R n ↔ degree f <= n := by
  simp only [degreeLE, Submodule.mem_iInf, degree_le_iff_coeff_zero, LinearMap.mem_ker]; rfl

@[gcongr, mono]
/--
theorem `degreeLE_mono` / 定理 `degreeLE_mono`

English:
theorem degreeLE_mono
  given: {m n : WithBot Nat} (H : m <= n)
  statement: degreeLE R m <= degreeLE R n
  proof: fun _ hf =>
  mem_degreeLE.2 (le_trans (mem_degreeLE.1 hf) H)

中文:
定理 degreeLE_mono
  条件: {m n : WithBot 自然数} (H : m <= n)
  结论: degreeLE R m <= degreeLE R n
  证明: fun _ hf =>
  mem_degreeLE.2 (le_trans (mem_degreeLE.1 hf) H)
-/
theorem degreeLE_mono {m n : WithBot Nat} (H : m <= n) : degreeLE R m <= degreeLE R n := fun _ hf =>
  mem_degreeLE.2 (le_trans (mem_degreeLE.1 hf) H)

/--
theorem `degreeLE_eq_span_X_pow` / 定理 `degreeLE_eq_span_X_pow`

English:
theorem degreeLE_eq_span_X_pow
  given: [DecidableEq R] {n : Nat}
  proof: by
  apply le_antisymm
  · intro p hp
    replace hp := mem_degreeLE.1 hp
    rw [← Polynomial.sum_monomial_eq p]; rw [Polynomial.sum]
    refine Submodule.sum_mem _ fun k hk => ?_
    have := WithBot.coe_le_coe.1 (Finset.sup_le_iff.1 hp k hk)
    rw [← C_mul_X_pow_eq_monomial]; rw [C_mul']
    refi

中文:
定理 degreeLE_eq_span_X_pow
  条件: [DecidableEq R] {n : 自然数}
  证明: by
  apply le_antisymm
  · intro p hp
    replace hp := mem_degreeLE.1 hp
    rw [← Polynomial.sum_monomial_eq p]; rw [Polynomial.sum]
    refine Submodule.sum_mem _ fun k hk => ?_
    have := WithBot.coe_le_coe.1 (Finset.sup_le_iff.1 hp k hk)
    rw [← C_mul_X_pow_eq_monomial]; rw [C_mul']
    refi

Depends on / 依赖: C_mul, C_mul_X_pow_eq_monomial, Finset, Finset.coe_image, Finset.mem_coe, Finset.mem_image, Finset.mem_range, Finset.sup_le_iff, Nat.lt_succ_of_le, Polynomial, Polynomial.sum, Polynomial.sum_monomial_eq, Set.image_subset_iff, Submodule, Submodule.smul_mem, Submodule.span_le, Submodule.subset_span, Submodule.sum_mem, WithBot, WithBot.coe_le_coe
-/
theorem degreeLE_eq_span_X_pow [DecidableEq R] {n : Nat} :
    degreeLE R n = Submodule.span R ↑((Finset.range (n + 1)).image fun n => (X : R[X]) ^ n) := by
  apply le_antisymm
  · intro p hp
    replace hp := mem_degreeLE.1 hp
    rw [← Polynomial.sum_monomial_eq p]; rw [Polynomial.sum]
    refine Submodule.sum_mem _ fun k hk => ?_
    have := WithBot.coe_le_coe.1 (Finset.sup_le_iff.1 hp k hk)
    rw [← C_mul_X_pow_eq_monomial]; rw [C_mul']
    refine
      Submodule.smul_mem _ _
        (Submodule.subset_span <|
Finset.mem_coe.2
            Finset.mem_image.2 ⟨_, Finset.mem_range.2 (Nat.lt_succ_of_le this), rfl⟩)
  rw [Submodule.span_le]; rw [Finset.coe_image]; rw [Set.image_subset_iff]
  intro k hk
  apply mem_degreeLE.2
  exact
    (degree_X_pow_le _).trans (WithBot.coe_le_coe.2 <| Nat.le_of_lt_succ <| Finset.mem_range.1 hk)

/--
theorem `mem_degreeLT` / 定理 `mem_degreeLT`

English:
theorem mem_degreeLT
  given: {n : Nat} {f : R[X]}
  statement: f in degreeLT R n ↔ degree f < n
  proof: by
  simpa [degreeLT, Submodule.mem_iInf] using (degree_lt_iff_coeff_zero _ _).symm

中文:
定理 mem_degreeLT
  条件: {n : 自然数} {f : R[X]}
  结论: f in degreeLT R n ↔ degree f < n
  证明: by
  simpa [degreeLT, Submodule.mem_iInf] using (degree_lt_iff_coeff_zero _ _).symm

Depends on / 依赖: Submodule, Submodule.mem_iInf, degreeLT, degree_lt_iff_coeff_zero, mem_iInf
-/
theorem mem_degreeLT {n : Nat} {f : R[X]} : f in degreeLT R n ↔ degree f < n := by
  simpa [degreeLT, Submodule.mem_iInf] using (degree_lt_iff_coeff_zero _ _).symm

/--
theorem `monomial_coe_mem_degreeLT` / 定理 `monomial_coe_mem_degreeLT`

English:
theorem monomial_coe_mem_degreeLT
  given: {n : Nat} (i : Fin n) (a : R)
  statement: monomial i a in degreeLT R n
  proof: mem_degreeLT.mpr .trans_lt by simp degree_monomial_le i a

@[gcongr, mono]

中文:
定理 monomial_coe_mem_degreeLT
  条件: {n : 自然数} (i : 有限集 n) (a : R)
  结论: monomial i a in degreeLT R n
  证明: mem_degreeLT.mpr .trans_lt by simp degree_monomial_le i a

@[gcongr, mono]

Depends on / 依赖: degree_monomial_le, mem_degreeLT, mem_degreeLT.mpr, trans_lt
-/
theorem monomial_coe_mem_degreeLT {n : Nat} (i : Fin n) (a : R) : monomial i a in degreeLT R n :=
mem_degreeLT.mpr .trans_lt by simp degree_monomial_le i a

@[gcongr, mono]
/--
theorem `degreeLT_mono` / 定理 `degreeLT_mono`

English:
theorem degreeLT_mono
  given: {m n : Nat} (H : m <= n)
  statement: degreeLT R m <= degreeLT R n
  proof: fun _ hf =>
  mem_degreeLT.2 (lt_of_lt_of_le (mem_degreeLT.1 hf) <| WithBot.coe_le_coe.2 H)

中文:
定理 degreeLT_mono
  条件: {m n : 自然数} (H : m <= n)
  结论: degreeLT R m <= degreeLT R n
  证明: fun _ hf =>
  mem_degreeLT.2 (lt_of_lt_of_le (mem_degreeLT.1 hf) <| WithBot.coe_le_coe.2 H)
-/
theorem degreeLT_mono {m n : Nat} (H : m <= n) : degreeLT R m <= degreeLT R n := fun _ hf =>
  mem_degreeLT.2 (lt_of_lt_of_le (mem_degreeLT.1 hf) <| WithBot.coe_le_coe.2 H)

/--
theorem `degreeLT_eq_span_X_pow` / 定理 `degreeLT_eq_span_X_pow`

English:
theorem degreeLT_eq_span_X_pow
  given: [DecidableEq R] {n : Nat}
  proof: by
  apply le_antisymm
  · intro p hp
    replace hp := mem_degreeLT.1 hp
    rw [← Polynomial.sum_monomial_eq p]; rw [Polynomial.sum]
    refine Submodule.sum_mem _ fun k hk => ?_
    have := WithBot.coe_lt_coe.1 ((Finset.sup_lt_iff <| WithBot.bot_lt_coe n).1 hp k hk)
    rw [← C_mul_X_pow_eq_monom

中文:
定理 degreeLT_eq_span_X_pow
  条件: [DecidableEq R] {n : 自然数}
  证明: by
  apply le_antisymm
  · intro p hp
    replace hp := mem_degreeLT.1 hp
    rw [← Polynomial.sum_monomial_eq p]; rw [Polynomial.sum]
    refine Submodule.sum_mem _ fun k hk => ?_
    have := WithBot.coe_lt_coe.1 ((Finset.sup_lt_iff <| WithBot.bot_lt_coe n).1 hp k hk)
    rw [← C_mul_X_pow_eq_monom

Depends on / 依赖: C_mul, C_mul_X_pow_eq_monomial, Finset, Finset.coe_image, Finset.sup_lt_iff, Polynomial, Polynomial.sum, Polynomial.sum_monomial_eq, Set.image_subset_iff, Submodule, Submodule.smul_mem, Submodule.span_le, Submodule.subset_span, Submodule.sum_mem, WithBot, WithBot.bot_lt_coe, WithBot.coe_lt_coe, bot_lt_coe, coe_image, coe_lt_coe
-/
theorem degreeLT_eq_span_X_pow [DecidableEq R] {n : Nat} :
    degreeLT R n = Submodule.span R ↑((Finset.range n).image fun n => X ^ n : Finset R[X]) := by
  apply le_antisymm
  · intro p hp
    replace hp := mem_degreeLT.1 hp
    rw [← Polynomial.sum_monomial_eq p]; rw [Polynomial.sum]
    refine Submodule.sum_mem _ fun k hk => ?_
    have := WithBot.coe_lt_coe.1 ((Finset.sup_lt_iff <| WithBot.bot_lt_coe n).1 hp k hk)
    rw [← C_mul_X_pow_eq_monomial]; rw [C_mul']
    refine Submodule.smul_mem _ _ (Submodule.subset_span <| by grind)
  rw [Submodule.span_le]; rw [Finset.coe_image]; rw [Set.image_subset_iff]
  intro k hk
  apply mem_degreeLT.2
.trans_lt WithBot.coe_lt_coe.2 Finset.mem_range.1 hk exact degree_X_pow_le _

variable (R) in
/--
Definition of `degreeLTEquiv` / `degreeLTEquiv` 的定义

English:
definition degreeLTEquiv
  signature: (n : Nat)
  body: (↑p : R[X]).coeff n
  invFun f :=
    ⟨∑ i : Fin n, monomial i (f i),
.sum_mem fun i _ => monomial_coe_mem_degreeLT i (f i)⟩ degreeLT R n
  map_add' p q := by ext; simp
  map_smul' x p := by ext; simp
  left_inv := fun ⟨p, hp⟩ => by simpa using p.sum_fin (monomial ·) (by simp) (mem_degreeLT.mp hp)
 

中文:
定义 degreeLTEquiv
  签名: (n : 自然数)
  定义体: (↑p : R[X]).coeff n
  invFun f :=
    ⟨∑ i : Fin n, monomial i (f i),
.sum_mem fun i _ => monomial_coe_mem_degreeLT i (f i)⟩ degreeLT R n
  map_add' p q := by ext; simp
  map_smul' x p := by ext; simp
  left_inv := fun ⟨p, hp⟩ => by simpa using p.sum_fin (monomial ·) (by simp) (mem_degreeLT.mp hp)
 
-/
def degreeLTEquiv (n : Nat) : degreeLT R n ≃ₗ[R] Fin n -> R where
  toFun p n := (↑p : R[X]).coeff n
  invFun f :=
    ⟨∑ i : Fin n, monomial i (f i),
.sum_mem fun i _ => monomial_coe_mem_degreeLT i (f i)⟩ degreeLT R n
  map_add' p q := by ext; simp
  map_smul' x p := by ext; simp
  left_inv := fun ⟨p, hp⟩ => by simpa using p.sum_fin (monomial ·) (by simp) (mem_degreeLT.mp hp)
  right_inv f := by ext i; grind [finsetSum_coeff, Finset.sum_eq_single i, coeff_monomial]

/--
theorem `degreeLTEquiv_eq_zero_iff_eq_zero` / 定理 `degreeLTEquiv_eq_zero_iff_eq_zero`

English:
theorem degreeLTEquiv_eq_zero_iff_eq_zero
  given: {n : Nat} {p : R[X]} (hp : p in degreeLT R n)
  proof: by simp

中文:
定理 degreeLTEquiv_eq_zero_iff_eq_zero
  条件: {n : 自然数} {p : R[X]} (hp : p in degreeLT R n)
  证明: by simp
-/
theorem degreeLTEquiv_eq_zero_iff_eq_zero {n : Nat} {p : R[X]} (hp : p in degreeLT R n) :
    degreeLTEquiv _ _ ⟨p, hp⟩ = 0 ↔ p = 0 := by simp

/--
theorem `eval_eq_sum_degreeLTEquiv` / 定理 `eval_eq_sum_degreeLTEquiv`

English:
theorem eval_eq_sum_degreeLTEquiv
  given: {n : Nat} {p : R[X]} (hp : p in degreeLT R n) (x : R)
  proof: by
  simp_rw [eval_eq_sum]
  exact (sum_fin _ (by simp_rw [zero_mul, forall_const]) (mem_degreeLT.mp hp)).symm

中文:
定理 eval_eq_sum_degreeLTEquiv
  条件: {n : 自然数} {p : R[X]} (hp : p in degreeLT R n) (x : R)
  证明: by
  simp_rw [eval_eq_sum]
  exact (sum_fin _ (by simp_rw [zero_mul, forall_const]) (mem_degreeLT.mp hp)).symm

Depends on / 依赖: eval_eq_sum, forall_const, mem_degreeLT, mem_degreeLT.mp, simp_rw, sum_fin, zero_mul
-/
theorem eval_eq_sum_degreeLTEquiv {n : Nat} {p : R[X]} (hp : p in degreeLT R n) (x : R) :
    p.eval x = ∑ i, degreeLTEquiv _ _ ⟨p, hp⟩ i * x ^ (i : Nat) := by
  simp_rw [eval_eq_sum]
  exact (sum_fin _ (by simp_rw [zero_mul, forall_const]) (mem_degreeLT.mp hp)).symm

/--
theorem `degreeLT_succ_eq_degreeLE` / 定理 `degreeLT_succ_eq_degreeLE`

English:
theorem degreeLT_succ_eq_degreeLE
  given: {n : Nat}
  statement: degreeLT R (n + 1) = degreeLE R n
  proof: by
  ext x
  by_cases x_zero : x = 0
  · simp_rw [x_zero, Submodule.zero_mem]
  · rw [mem_degreeLT, mem_degreeLE, ← natDegree_lt_iff_degree_lt (by rwa [ne_eq]),
      ← natDegree_le_iff_degree_le, Nat.lt_succ_iff]

中文:
定理 degreeLT_succ_eq_degreeLE
  条件: {n : 自然数}
  结论: degreeLT R (n + 1) = degreeLE R n
  证明: by
  ext x
  by_cases x_zero : x = 0
  · simp_rw [x_zero, Submodule.zero_mem]
  · rw [mem_degreeLT, mem_degreeLE, ← natDegree_lt_iff_degree_lt (by rwa [ne_eq]),
      ← natDegree_le_iff_degree_le, Nat.lt_succ_iff]

Depends on / 依赖: Nat.lt_succ_iff, Submodule, Submodule.zero_mem, lt_succ_iff, mem_degreeLE, mem_degreeLT, natDegree_le_iff_degree_le, natDegree_lt_iff_degree_lt, ne_eq, simp_rw, x_zero, zero_mem
-/
theorem degreeLT_succ_eq_degreeLE {n : Nat} : degreeLT R (n + 1) = degreeLE R n := by
  ext x
  by_cases x_zero : x = 0
  · simp_rw [x_zero, Submodule.zero_mem]
  · rw [mem_degreeLT, mem_degreeLE, ← natDegree_lt_iff_degree_lt (by rwa [ne_eq]),
      ← natDegree_le_iff_degree_le, Nat.lt_succ_iff]

/--
Definition of `monicEquivDegreeLT` / `monicEquivDegreeLT` 的定义

English:
definition monicEquivDegreeLT
  signature: [Nontrivial R] (n : Nat)
  body: ⟨p.1.eraseLead, by
    rcases p with ⟨p, hp, rfl⟩
    simp only [mem_degreeLT]
    refine lt_of_lt_of_le ?_ degree_le_natDegree
    exact degree_eraseLead_lt (Polynomial.Monic.ne_zero_of_polynomial_ne hp one_ne_zero)⟩
  invFun := fun p =>
    ⟨X^n + p.1, monic_X_pow_add (mem_degreeLT.1 p.2), by
    

中文:
定义 monicEquivDegreeLT
  签名: [非平凡 R] (n : 自然数)
  定义体: ⟨p.1.eraseLead, by
    rcases p with ⟨p, hp, rfl⟩
    simp only [mem_degreeLT]
    refine lt_of_lt_of_le ?_ degree_le_natDegree
    exact degree_eraseLead_lt (Polynomial.Monic.ne_zero_of_polynomial_ne hp one_ne_zero)⟩
  invFun := fun p =>
    ⟨X^n + p.1, monic_X_pow_add (mem_degreeLT.1 p.2), by
    

Depends on / 依赖: Monic.def, Polynomial, Polynomial.Monic.ne_zero_of_polynomial_ne, add_comm, conv_rhs, degree_eraseLead_lt, degree_le_natDegree, eraseLead, eraseLead_add_C_mul_X_pow, invFun, left_inv, lt_of_lt_of_le, mem_degreeLT, monic_X_pow_add, natDegree_add_eq_left_of_degree_lt, ne_zero_of_polynomial_ne, one_ne_zero, right_inv
-/
def monicEquivDegreeLT [Nontrivial R] (n : Nat) :
    { p : R[X] // p.Monic ∧ p.natDegree = n } ≃ degreeLT R n where
  toFun p := ⟨p.1.eraseLead, by
    rcases p with ⟨p, hp, rfl⟩
    simp only [mem_degreeLT]
    refine lt_of_lt_of_le ?_ degree_le_natDegree
    exact degree_eraseLead_lt (Polynomial.Monic.ne_zero_of_polynomial_ne hp one_ne_zero)⟩
  invFun := fun p =>
    ⟨X^n + p.1, monic_X_pow_add (mem_degreeLT.1 p.2), by
        rw [natDegree_add_eq_left_of_degree_lt]
        · simp
        · simp [mem_degreeLT.1 p.2]⟩
  left_inv := by
    rintro ⟨p, hp, rfl⟩
    ext1
    simp only
    conv_rhs => rw [← eraseLead_add_C_mul_X_pow p]
    simp [Monic.def.1 hp, add_comm]
  right_inv := by
    rintro ⟨p, hp⟩
    ext1
    simp only
    rw [eraseLead_add_of_degree_lt_left]
    · simp
    · simp [mem_degreeLT.1 hp]

/--
theorem `exists_degree_le_of_mem_span` / 定理 `exists_degree_le_of_mem_span`

English:
theorem exists_degree_le_of_mem_span
  statement: {s : Set R[X]} {p : R[X]}
  proof: by
  by_contra! h
  by_cases hp_zero : p = 0
  · rw [hp_zero, degree_zero] at h
    rcases hs with ⟨x, hx⟩
    exact not_lt_bot (h x hx)
  · have : p in degreeLT R (natDegree p) := by
      refine (Submodule.span_le.mpr fun p' p'_mem => ?_) hp
      rw [SetLike.mem_coe]; rw [mem_degreeLT]; rw [Nat.c

中文:
定理 存在_degree_le_of_mem_span
  结论: {s : 集合 R[X]} {p : R[X]}
  证明: by
  by_contra! h
  by_cases hp_zero : p = 0
  · rw [hp_zero, degree_zero] at h
    rcases hs with ⟨x, hx⟩
    exact not_lt_bot (h x hx)
  · have : p in degreeLT R (natDegree p) := by
      refine (Submodule.span_le.mpr fun p' p'_mem => ?_) hp
      rw [SetLike.mem_coe]; rw [mem_degreeLT]; rw [Nat.c

Depends on / 依赖: Nat.cast_withBot, SetLike, SetLike.mem_coe, Submodule, Submodule.span_le.mpr, _mem, cast_withBot, degreeLT, degree_eq_natDegree, degree_le_natDegree, degree_zero, hp_zero, lt_of_lt_of_le, lt_self_iff_false, mem_coe, mem_degreeLT, natDegree, not_lt_bot, span_le
-/
theorem exists_degree_le_of_mem_span {s : Set R[X]} {p : R[X]}
    (hs : s.Nonempty) (hp : p in Submodule.span R s) :
    exists p' in s, degree p <= degree p' := by
  by_contra! h
  by_cases hp_zero : p = 0
  · rw [hp_zero, degree_zero] at h
    rcases hs with ⟨x, hx⟩
    exact not_lt_bot (h x hx)
  · have : p in degreeLT R (natDegree p) := by
      refine (Submodule.span_le.mpr fun p' p'_mem => ?_) hp
      rw [SetLike.mem_coe]; rw [mem_degreeLT]; rw [Nat.cast_withBot]
      exact lt_of_lt_of_le (h p' p'_mem) degree_le_natDegree
    rwa [mem_degreeLT, Nat.cast_withBot, degree_eq_natDegree hp_zero,
      Nat.cast_withBot, lt_self_iff_false] at this

/--
theorem `exists_degree_le_of_mem_span_of_finite` / 定理 `exists_degree_le_of_mem_span_of_finite`

English:
theorem exists_degree_le_of_mem_span_of_finite
  given: {s : Set R[X]} (s_fin : s.Finite) (hs : s.Nonempty)
  proof: by
  obtain ⟨a, has, hmax⟩ := s_fin.exists_maximalFor degree s hs
  refine ⟨a, has, fun p hp => ?_⟩
  obtain ⟨p', hp', hpp'⟩ := exists_degree_le_of_mem_span hs hp
exact hpp'.trans not_lt.1 not_lt_iff_le_imp_ge.2 hmax hp'

中文:
定理 存在_degree_le_of_mem_span_of_finite
  条件: {s : 集合 R[X]} (s_fin : s.有限) (hs : s.非空)
  证明: by
  obtain ⟨a, has, hmax⟩ := s_fin.exists_maximalFor degree s hs
  refine ⟨a, has, fun p hp => ?_⟩
  obtain ⟨p', hp', hpp'⟩ := exists_degree_le_of_mem_span hs hp
exact hpp'.trans not_lt.1 not_lt_iff_le_imp_ge.2 hmax hp'

Depends on / 依赖: degree, exists_degree_le_of_mem_span, exists_maximalFor, not_lt, not_lt_iff_le_imp_ge, s_fin, s_fin.exists_maximalFor
-/
theorem exists_degree_le_of_mem_span_of_finite {s : Set R[X]} (s_fin : s.Finite) (hs : s.Nonempty) :
    exists p' in s, forall (p : R[X]), p in Submodule.span R s -> degree p <= degree p' := by
  obtain ⟨a, has, hmax⟩ := s_fin.exists_maximalFor degree s hs
  refine ⟨a, has, fun p hp => ?_⟩
  obtain ⟨p', hp', hpp'⟩ := exists_degree_le_of_mem_span hs hp
exact hpp'.trans not_lt.1 not_lt_iff_le_imp_ge.2 hmax hp'

/--
theorem `span_le_degreeLE_of_finite` / 定理 `span_le_degreeLE_of_finite`

English:
theorem span_le_degreeLE_of_finite
  given: {s : Set R[X]} (s_fin : s.Finite)
  proof: by
  by_cases s_emp : s.Nonempty
  · rcases exists_degree_le_of_mem_span_of_finite s_fin s_emp with ⟨p', _, hp'max⟩
    exact ⟨natDegree p', fun p hp => mem_degreeLE.mpr ((hp'max _ hp).trans degree_le_natDegree)⟩
  · rw [Set.not_nonempty_iff_eq_empty] at s_emp
    rw [s_emp]; rw [Submodule.span_empt

中文:
定理 span_le_degreeLE_of_finite
  条件: {s : 集合 R[X]} (s_fin : s.有限)
  证明: by
  by_cases s_emp : s.Nonempty
  · rcases exists_degree_le_of_mem_span_of_finite s_fin s_emp with ⟨p', _, hp'max⟩
    exact ⟨natDegree p', fun p hp => mem_degreeLE.mpr ((hp'max _ hp).trans degree_le_natDegree)⟩
  · rw [Set.not_nonempty_iff_eq_empty] at s_emp
    rw [s_emp]; rw [Submodule.span_empt

Depends on / 依赖: Nonempty, Set.not_nonempty_iff_eq_empty, Submodule, Submodule.span_empty, bot_le, degree_le_natDegree, exists_degree_le_of_mem_span_of_finite, mem_degreeLE, mem_degreeLE.mpr, natDegree, not_nonempty_iff_eq_empty, s.Nonempty, s_emp, s_fin, span_empty
-/
theorem span_le_degreeLE_of_finite {s : Set R[X]} (s_fin : s.Finite) :
    exists n : Nat, Submodule.span R s <= degreeLE R n := by
  by_cases s_emp : s.Nonempty
  · rcases exists_degree_le_of_mem_span_of_finite s_fin s_emp with ⟨p', _, hp'max⟩
    exact ⟨natDegree p', fun p hp => mem_degreeLE.mpr ((hp'max _ hp).trans degree_le_natDegree)⟩
  · rw [Set.not_nonempty_iff_eq_empty] at s_emp
    rw [s_emp]; rw [Submodule.span_empty]
    exact ⟨0, bot_le⟩

/--
theorem `span_of_finite_le_degreeLT` / 定理 `span_of_finite_le_degreeLT`

English:
theorem span_of_finite_le_degreeLT
  given: {s : Set R[X]} (s_fin : s.Finite)
  proof: by
  rcases span_le_degreeLE_of_finite s_fin with ⟨n, _⟩
  exact ⟨n + 1, by rwa [degreeLT_succ_eq_degreeLE]⟩

中文:
定理 span_of_finite_le_degreeLT
  条件: {s : 集合 R[X]} (s_fin : s.有限)
  证明: by
  rcases span_le_degreeLE_of_finite s_fin with ⟨n, _⟩
  exact ⟨n + 1, by rwa [degreeLT_succ_eq_degreeLE]⟩

Depends on / 依赖: degreeLT_succ_eq_degreeLE, s_fin, span_le_degreeLE_of_finite
-/
theorem span_of_finite_le_degreeLT {s : Set R[X]} (s_fin : s.Finite) :
    exists n : Nat, Submodule.span R s <= degreeLT R n := by
  rcases span_le_degreeLE_of_finite s_fin with ⟨n, _⟩
  exact ⟨n + 1, by rwa [degreeLT_succ_eq_degreeLE]⟩

/--
theorem `not_finite` / 定理 `not_finite`

English:
theorem not_finite
  given: [Nontrivial R]
  statement: ¬ Module.Finite R R[X]
  proof: by
  rw [Module.finite_def]; rw [Submodule.fg_def]
  push Not
  intro s hs contra
  rcases span_le_degreeLE_of_finite hs with ⟨n, hn⟩
  have : ((X : R[X]) ^ (n + 1)) in Polynomial.degreeLE R ↑n := by
    rw [contra] at hn
    exact hn Submodule.mem_top
  rw [mem_degreeLE]; rw [degree_X_pow]; rw [Nat

中文:
定理 not_finite
  条件: [非平凡 R]
  结论: ¬ 模.有限 R R[X]
  证明: by
  rw [Module.finite_def]; rw [Submodule.fg_def]
  push Not
  intro s hs contra
  rcases span_le_degreeLE_of_finite hs with ⟨n, hn⟩
  have : ((X : R[X]) ^ (n + 1)) in Polynomial.degreeLE R ↑n := by
    rw [contra] at hn
    exact hn Submodule.mem_top
  rw [mem_degreeLE]; rw [degree_X_pow]; rw [Nat

Depends on / 依赖: Module, Module.finite_def, Nat.cast_le, Polynomial, Polynomial.degreeLE, Submodule, Submodule.fg_def, Submodule.mem_top, add_le_iff_nonpos_right, cast_le, contra, degreeLE, degree_X_pow, fg_def, finite_def, mem_degreeLE, mem_top, nonpos_iff_eq_zero, one_ne_zero, span_le_degreeLE_of_finite
-/
theorem not_finite [Nontrivial R] : ¬ Module.Finite R R[X] := by
  rw [Module.finite_def]; rw [Submodule.fg_def]
  push Not
  intro s hs contra
  rcases span_le_degreeLE_of_finite hs with ⟨n, hn⟩
  have : ((X : R[X]) ^ (n + 1)) in Polynomial.degreeLE R ↑n := by
    rw [contra] at hn
    exact hn Submodule.mem_top
  rw [mem_degreeLE]; rw [degree_X_pow]; rw [Nat.cast_le]; rw [add_le_iff_nonpos_right]; rw [nonpos_iff_eq_zero] at this
  exact one_ne_zero this

set_option backward.defeqAttrib.useBackward true in
/--
theorem `geom_sum_X_comp_X_add_one_eq_sum` / 定理 `geom_sum_X_comp_X_add_one_eq_sum`

English:
theorem geom_sum_X_comp_X_add_one_eq_sum
  given: (n : Nat)
  proof: by
  ext i
  trans (n.choose (i + 1) : R); swap
  · simp only [finsetSum_coeff, ← C_eq_natCast, coeff_C_mul_X_pow]
    rw [Finset.sum_eq_single i]; rw [if_pos rfl]
    · simp +contextual only [@eq_comm _ i, if_false,
        imp_true_iff]
    · simp +contextual only [Nat.lt_add_one_iff, Nat.choose_e

中文:
定理 geom_sum_X_comp_X_add_one_eq_sum
  条件: (n : 自然数)
  证明: by
  ext i
  trans (n.choose (i + 1) : R); swap
  · simp only [finsetSum_coeff, ← C_eq_natCast, coeff_C_mul_X_pow]
    rw [Finset.sum_eq_single i]; rw [if_pos rfl]
    · simp +contextual only [@eq_comm _ i, if_false,
        imp_true_iff]
    · simp +contextual only [Nat.lt_add_one_iff, Nat.choose_e

Depends on / 依赖: C_eq_natCast, Finset, Finset.mem_range, Finset.sum_eq_single, Nat.cast_zero, Nat.choose_eq_zero_of_lt, Nat.lt_add_one_iff, add_, cast_zero, choose_eq_zero_of_lt, coeff_C_mul_X_pow, coeff_zero, contextual, eq_comm, finsetSum_coeff, generalizing, geom_sum_succ, if_false, if_pos, if_true
-/
theorem geom_sum_X_comp_X_add_one_eq_sum (n : Nat) :
    (∑ i in range n, (X : R[X]) ^ i).comp (X + 1) =
      (Finset.range n).sum fun i : Nat => (n.choose (i + 1) : R[X]) * X ^ i := by
  ext i
  trans (n.choose (i + 1) : R); swap
  · simp only [finsetSum_coeff, ← C_eq_natCast, coeff_C_mul_X_pow]
    rw [Finset.sum_eq_single i]; rw [if_pos rfl]
    · simp +contextual only [@eq_comm _ i, if_false,
        imp_true_iff]
    · simp +contextual only [Nat.lt_add_one_iff, Nat.choose_eq_zero_of_lt,
        Nat.cast_zero, Finset.mem_range, not_lt, if_true, imp_true_iff]
  induction n generalizing i with
  | zero => dsimp; simp only [zero_comp, coeff_zero, Nat.cast_zero]
  | succ n ih =>
    simp only [geom_sum_succ', ih, add_comp, X_pow_comp, coeff_add, Nat.choose_succ_succ,
      Nat.cast_add, coeff_X_add_one_pow]

/--
theorem `Monic.geom_sum` / 定理 `Monic.geom_sum`

English:
theorem Monic.geom_sum
  given: {P : R[X]} (hP : P.Monic) (hdeg : 0 < P.natDegree) {n : Nat} (hn : n != 0)
  proof: by
  nontriviality R
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn
  rw [geom_sum_succ']
  refine (hP.pow _).add_of_left ?_
  refine lt_of_le_of_lt (degree_sum_le _ _) ?_
  rw [Finset.sup_lt_iff]
  · simp only [Finset.mem_range, degree_eq_natDegree (hP.pow _).ne_zero]
    simp only [Nat.cast

中文:
定理 Monic.geom_sum
  条件: {P : R[X]} (hP : P.Monic) (hdeg : 0 < P.natDegree) {n : 自然数} (hn : n != 0)
  证明: by
  nontriviality R
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn
  rw [geom_sum_succ']
  refine (hP.pow _).add_of_left ?_
  refine lt_of_le_of_lt (degree_sum_le _ _) ?_
  rw [Finset.sup_lt_iff]
  · simp only [Finset.mem_range, degree_eq_natDegree (hP.pow _).ne_zero]
    simp only [Nat.cast

Depends on / 依赖: Finset, Finset.mem_range, Finset.sup_lt_iff, Nat.cast_lt, Nat.exists_eq_succ_of_ne_zero, add_of_left, bot_lt_iff_ne_bot, cast_lt, degree_eq_bot, degree_eq_natDegree, degree_sum_le, exists_eq_succ_of_ne_zero, geom_sum_succ, hP.natDegree_pow, hP.pow, lt_of_le_of_lt, mem_range, natDegree_pow, ne_zero, nontriviality
-/
theorem Monic.geom_sum {P : R[X]} (hP : P.Monic) (hdeg : 0 < P.natDegree) {n : Nat} (hn : n != 0) :
    (∑ i in range n, P ^ i).Monic := by
  nontriviality R
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn
  rw [geom_sum_succ']
  refine (hP.pow _).add_of_left ?_
  refine lt_of_le_of_lt (degree_sum_le _ _) ?_
  rw [Finset.sup_lt_iff]
  · simp only [Finset.mem_range, degree_eq_natDegree (hP.pow _).ne_zero]
    simp only [Nat.cast_lt, hP.natDegree_pow]
    intro k
    exact nsmul_lt_nsmul_left hdeg
  · rw [bot_lt_iff_ne_bot, Ne, degree_eq_bot]
    exact (hP.pow _).ne_zero

/--
theorem `Monic.geom_sum'` / 定理 `Monic.geom_sum'`

English:
theorem Monic.geom_sum'
  given: {P : R[X]} (hP : P.Monic) (hdeg : 0 < P.degree) {n : Nat} (hn : n != 0)
  proof: hP.geom_sum (natDegree_pos_iff_degree_pos.2 hdeg) hn

中文:
定理 Monic.geom_sum'
  条件: {P : R[X]} (hP : P.Monic) (hdeg : 0 < P.degree) {n : 自然数} (hn : n != 0)
  证明: hP.geom_sum (natDegree_pos_iff_degree_pos.2 hdeg) hn

Depends on / 依赖: geom_sum, hP.geom_sum, natDegree_pos_iff_degree_pos
-/
theorem Monic.geom_sum' {P : R[X]} (hP : P.Monic) (hdeg : 0 < P.degree) {n : Nat} (hn : n != 0) :
    (∑ i in range n, P ^ i).Monic :=
  hP.geom_sum (natDegree_pos_iff_degree_pos.2 hdeg) hn

/--
theorem `monic_geom_sum_X` / 定理 `monic_geom_sum_X`

English:
theorem monic_geom_sum_X
  given: {n : Nat} (hn : n != 0)
  statement: (∑ i in range n, (X : R[X]) ^ i).Monic
  proof: by
  nontriviality R
  apply monic_X.geom_sum _ hn
  simp only [natDegree_X, zero_lt_one]

中文:
定理 monic_geom_sum_X
  条件: {n : 自然数} (hn : n != 0)
  结论: (∑ i in range n, (X : R[X]) ^ i).Monic
  证明: by
  nontriviality R
  apply monic_X.geom_sum _ hn
  simp only [natDegree_X, zero_lt_one]

Depends on / 依赖: geom_sum, monic_X, monic_X.geom_sum, natDegree_X, nontriviality, zero_lt_one
-/
theorem monic_geom_sum_X {n : Nat} (hn : n != 0) : (∑ i in range n, (X : R[X]) ^ i).Monic := by
  nontriviality R
  apply monic_X.geom_sum _ hn
  simp only [natDegree_X, zero_lt_one]

end Semiring

section Ring

variable [Ring R]

/--
Definition of `restriction` / `restriction` 的定义

English:
definition restriction
  signature: (p : R[X])
  body: ∑ i in p.support,
    monomial i
      (⟨p.coeff i,
          letI := Classical.decEq R
          if H : p.coeff i = 0 then H.symm ▸ (Subring.closure _).zero_mem
          else Subring.subset_closure (p.coeff_mem_coeffs H)⟩ :
        Subring.closure (↑p.coeffs : Set R))

@[simp]

中文:
定义 restriction
  签名: (p : R[X])
  定义体: ∑ i in p.support,
    monomial i
      (⟨p.coeff i,
          letI := Classical.decEq R
          if H : p.coeff i = 0 then H.symm ▸ (Subring.closure _).zero_mem
          else Subring.subset_closure (p.coeff_mem_coeffs H)⟩ :
        Subring.closure (↑p.coeffs : Set R))

@[simp]

Depends on / 依赖: Classical, Classical.decEq, H.symm, Subring, Subring.closure, Subring.subset_closure, closure, coeff_mem_coeffs, coeffs, monomial, p.coeff, p.coeff_mem_coeffs, p.coeffs, p.support, subset_closure, support, zero_mem
-/
def restriction (p : R[X]) : Polynomial (Subring.closure (↑p.coeffs : Set R)) :=
  ∑ i in p.support,
    monomial i
      (⟨p.coeff i,
          letI := Classical.decEq R
          if H : p.coeff i = 0 then H.symm ▸ (Subring.closure _).zero_mem
          else Subring.subset_closure (p.coeff_mem_coeffs H)⟩ :
        Subring.closure (↑p.coeffs : Set R))

@[simp]
/--
theorem `coeff_restriction` / 定理 `coeff_restriction`

English:
theorem coeff_restriction
  given: {p : R[X]} {n : Nat}
  statement: ↑(coeff (restriction p) n) = coeff p n
  proof: by
  classical
  simp only [restriction, coeff_monomial, finsetSum_coeff, mem_support_iff, Finset.sum_ite_eq',
    Ne, ite_not]
  split_ifs with h
  · rw [h]
    rfl
  · rfl

中文:
定理 coeff_restriction
  条件: {p : R[X]} {n : 自然数}
  结论: ↑(coeff (restriction p) n) = coeff p n
  证明: by
  classical
  simp only [restriction, coeff_monomial, finsetSum_coeff, mem_support_iff, Finset.sum_ite_eq',
    Ne, ite_not]
  split_ifs with h
  · rw [h]
    rfl
  · rfl

Depends on / 依赖: Finset, Finset.sum_ite_eq, classical, coeff_monomial, finsetSum_coeff, ite_not, mem_support_iff, restriction, split_ifs, sum_ite_eq
-/
theorem coeff_restriction {p : R[X]} {n : Nat} : ↑(coeff (restriction p) n) = coeff p n := by
  classical
  simp only [restriction, coeff_monomial, finsetSum_coeff, mem_support_iff, Finset.sum_ite_eq',
    Ne, ite_not]
  split_ifs with h
  · rw [h]
    rfl
  · rfl

/--
theorem `coeff_restriction'` / 定理 `coeff_restriction'`

English:
theorem coeff_restriction'
  given: {p : R[X]} {n : Nat}
  statement: (coeff (restriction p) n).1 = coeff p n
  proof: by
  simp

@[simp]

中文:
定理 coeff_restriction'
  条件: {p : R[X]} {n : 自然数}
  结论: (coeff (restriction p) n).1 = coeff p n
  证明: by
  simp

@[simp]
-/
theorem coeff_restriction' {p : R[X]} {n : Nat} : (coeff (restriction p) n).1 = coeff p n := by
  simp

@[simp]
/--
theorem `support_restriction` / 定理 `support_restriction`

English:
theorem support_restriction
  given: (p : R[X])
  statement: support (restriction p) = support p
  proof: by
  ext i
  simp only [mem_support_iff, not_iff_not, Ne]
  conv_rhs => rw [← coeff_restriction]
  exact ⟨fun H => by rw [H, ZeroMemClass.coe_zero], fun H => Subtype.coe_injective H⟩

@[simp]

中文:
定理 support_restriction
  条件: (p : R[X])
  结论: support (restriction p) = support p
  证明: by
  ext i
  simp only [mem_support_iff, not_iff_not, Ne]
  conv_rhs => rw [← coeff_restriction]
  exact ⟨fun H => by rw [H, ZeroMemClass.coe_zero], fun H => Subtype.coe_injective H⟩

@[simp]

Depends on / 依赖: Subtype, Subtype.coe_injective, ZeroMemClass, ZeroMemClass.coe_zero, coe_injective, coe_zero, coeff_restriction, conv_rhs, mem_support_iff, not_iff_not
-/
theorem support_restriction (p : R[X]) : support (restriction p) = support p := by
  ext i
  simp only [mem_support_iff, not_iff_not, Ne]
  conv_rhs => rw [← coeff_restriction]
  exact ⟨fun H => by rw [H, ZeroMemClass.coe_zero], fun H => Subtype.coe_injective H⟩

@[simp]
/--
theorem `map_restriction` / 定理 `map_restriction`

English:
theorem map_restriction
  given: {R : Type u} [CommRing R] (p : R[X])
  proof: ext fun n => by rw [coeff_map, Algebra.algebraMap_ofSubsemiring_apply, coeff_restriction]

@[simp]

中文:
定理 map_restriction
  条件: {R : 类型u} [交换环 R] (p : R[X])
  证明: ext fun n => by rw [coeff_map, Algebra.algebraMap_ofSubsemiring_apply, coeff_restriction]

@[simp]

Depends on / 依赖: Algebra, Algebra.algebraMap_ofSubsemiring_apply, algebraMap_ofSubsemiring_apply, coeff_map, coeff_restriction
-/
theorem map_restriction {R : Type u} [CommRing R] (p : R[X]) :
    p.restriction.map (algebraMap _ _) = p :=
  ext fun n => by rw [coeff_map, Algebra.algebraMap_ofSubsemiring_apply, coeff_restriction]

@[simp]
/--
theorem `degree_restriction` / 定理 `degree_restriction`

English:
theorem degree_restriction
  given: {p : R[X]}
  statement: (restriction p).degree = p.degree
  proof: by simp [degree]

@[simp]

中文:
定理 degree_restriction
  条件: {p : R[X]}
  结论: (restriction p).degree = p.degree
  证明: by simp [degree]

@[simp]

Depends on / 依赖: degree
-/
theorem degree_restriction {p : R[X]} : (restriction p).degree = p.degree := by simp [degree]

@[simp]
/--
theorem `natDegree_restriction` / 定理 `natDegree_restriction`

English:
theorem natDegree_restriction
  given: {p : R[X]}
  statement: (restriction p).natDegree = p.natDegree
  proof: by
  simp [natDegree]

@[simp]

中文:
定理 natDegree_restriction
  条件: {p : R[X]}
  结论: (restriction p).natDegree = p.natDegree
  证明: by
  simp [natDegree]

@[simp]

Depends on / 依赖: natDegree
-/
theorem natDegree_restriction {p : R[X]} : (restriction p).natDegree = p.natDegree := by
  simp [natDegree]

@[simp]
/--
theorem `monic_restriction` / 定理 `monic_restriction`

English:
theorem monic_restriction
  given: {p : R[X]}
  statement: Monic (restriction p) ↔ Monic p
  proof: by
  simp only [Monic, leadingCoeff, natDegree_restriction]
  rw [← @coeff_restriction _ _ p]
  exact ⟨fun H => by rw [H, OneMemClass.coe_one], fun H => Subtype.coe_injective H⟩

@[simp]

中文:
定理 monic_restriction
  条件: {p : R[X]}
  结论: Monic (restriction p) ↔ Monic p
  证明: by
  simp only [Monic, leadingCoeff, natDegree_restriction]
  rw [← @coeff_restriction _ _ p]
  exact ⟨fun H => by rw [H, OneMemClass.coe_one], fun H => Subtype.coe_injective H⟩

@[simp]

Depends on / 依赖: OneMemClass, OneMemClass.coe_one, Subtype, Subtype.coe_injective, coe_injective, coe_one, coeff_restriction, leadingCoeff, natDegree_restriction
-/
theorem monic_restriction {p : R[X]} : Monic (restriction p) ↔ Monic p := by
  simp only [Monic, leadingCoeff, natDegree_restriction]
  rw [← @coeff_restriction _ _ p]
  exact ⟨fun H => by rw [H, OneMemClass.coe_one], fun H => Subtype.coe_injective H⟩

@[simp]
/--
theorem `restriction_zero` / 定理 `restriction_zero`

English:
theorem restriction_zero
  statement: restriction (0 : R[X]) = 0
  proof: by
  simp only [restriction, Finset.sum_empty, support_zero]

@[simp]

中文:
定理 restriction_zero
  结论: restriction (0 : R[X]) = 0
  证明: by
  simp only [restriction, Finset.sum_empty, support_zero]

@[simp]

Depends on / 依赖: Finset, Finset.sum_empty, restriction, sum_empty, support_zero
-/
theorem restriction_zero : restriction (0 : R[X]) = 0 := by
  simp only [restriction, Finset.sum_empty, support_zero]

@[simp]
/--
theorem `restriction_one` / 定理 `restriction_one`

English:
theorem restriction_one
  statement: restriction (1 : R[X]) = 1
  proof: ext fun i => Subtype.ext by rw [coeff_restriction', coeff_one, coeff_one]; split_ifs <;> rfl

中文:
定理 restriction_one
  结论: restriction (1 : R[X]) = 1
  证明: ext fun i => Subtype.ext by rw [coeff_restriction', coeff_one, coeff_one]; split_ifs <;> rfl

Depends on / 依赖: Subtype, Subtype.ext, coeff_one, coeff_restriction, split_ifs
-/
theorem restriction_one : restriction (1 : R[X]) = 1 :=
ext fun i => Subtype.ext by rw [coeff_restriction', coeff_one, coeff_one]; split_ifs <;> rfl

variable [Semiring S] {f : R ->+* S} {x : S}

/--
theorem `eval₂_restriction` / 定理 `eval₂_restriction`

English:
theorem eval₂_restriction
  given: {p : R[X]}
  proof: by
  simp only [eval₂_eq_sum, sum, support_restriction, ← @coeff_restriction _ _ p, RingHom.comp_apply,
    Subring.coe_subtype]

中文:
定理 eval₂_restriction
  条件: {p : R[X]}
  证明: by
  simp only [eval₂_eq_sum, sum, support_restriction, ← @coeff_restriction _ _ p, RingHom.comp_apply,
    Subring.coe_subtype]

Depends on / 依赖: RingHom, RingHom.comp_apply, Subring, Subring.coe_subtype, coe_subtype, coeff_restriction, comp_apply, support_restriction
-/
theorem eval₂_restriction {p : R[X]} :
    eval₂ f x p =
      eval₂ (f.comp (Subring.subtype (Subring.closure (p.coeffs : Set R)))) x p.restriction := by
  simp only [eval₂_eq_sum, sum, support_restriction, ← @coeff_restriction _ _ p, RingHom.comp_apply,
    Subring.coe_subtype]

end Ring

end Polynomial

namespace Ideal

open Polynomial

section Semiring

variable [Semiring R]

/--
Definition of `ofPolynomial` / `ofPolynomial` 的定义

English:
definition ofPolynomial
  signature: (I : Ideal R[X])
  body: I.carrier
  zero_mem' := I.zero_mem
  add_mem' := I.add_mem
  smul_mem' c x H := by
    rw [← C_mul']
    exact I.mul_mem_left _ H

中文:
定义 ofPolynomial
  签名: (I : 理想 R[X])
  定义体: I.carrier
  zero_mem' := I.zero_mem
  add_mem' := I.add_mem
  smul_mem' c x H := by
    rw [← C_mul']
    exact I.mul_mem_left _ H

Depends on / 依赖: I.carrier, carrier
-/
def ofPolynomial (I : Ideal R[X]) : Submodule R R[X] where
  carrier := I.carrier
  zero_mem' := I.zero_mem
  add_mem' := I.add_mem
  smul_mem' c x H := by
    rw [← C_mul']
    exact I.mul_mem_left _ H

variable {I : Ideal R[X]}

/--
theorem `mem_ofPolynomial` / 定理 `mem_ofPolynomial`

English:
theorem mem_ofPolynomial
  given: (x)
  statement: x in I.ofPolynomial ↔ x in I
  proof: Iff.rfl

中文:
定理 mem_ofPolynomial
  条件: (x)
  结论: x in I.ofPolynomial ↔ x in I
  证明: Iff.rfl

Depends on / 依赖: Iff.rfl
-/
theorem mem_ofPolynomial (x) : x in I.ofPolynomial ↔ x in I :=
  Iff.rfl

variable (I)

/--
Definition of `degreeLE` / `degreeLE` 的定义

English:
definition degreeLE
  signature: (n : WithBot Nat)
  body: Polynomial.degreeLE R n ⊓ I.ofPolynomial

中文:
定义 degreeLE
  签名: (n : WithBot 自然数)
  定义体: Polynomial.degreeLE R n ⊓ I.ofPolynomial

Depends on / 依赖: I.ofPolynomial, Polynomial, Polynomial.degreeLE, degreeLE, ofPolynomial
-/
def degreeLE (n : WithBot Nat) : Submodule R R[X] :=
  Polynomial.degreeLE R n ⊓ I.ofPolynomial

/--
Definition of `leadingCoeffNth` / `leadingCoeffNth` 的定义

English:
definition leadingCoeffNth
  signature: (n : Nat)
  body: (I.degreeLE n).map lcoeff R n

中文:
定义 leadingCoeffNth
  签名: (n : 自然数)
  定义体: (I.degreeLE n).map lcoeff R n

Depends on / 依赖: I.degreeLE, degreeLE, lcoeff
-/
def leadingCoeffNth (n : Nat) : Ideal R :=
(I.degreeLE n).map lcoeff R n

/--
Definition of `leadingCoeff` / `leadingCoeff` 的定义

English:
definition leadingCoeff
  signature: : Ideal R
  body: ⨆ n : Nat, I.leadingCoeffNth n

中文:
定义 leadingCoeff
  签名: : 理想 R
  定义体: ⨆ n : Nat, I.leadingCoeffNth n

Depends on / 依赖: I.leadingCoeffNth, leadingCoeffNth
-/
def leadingCoeff : Ideal R :=
  ⨆ n : Nat, I.leadingCoeffNth n

end Semiring

section CommSemiring

variable [CommSemiring R] [Semiring S]

/--
theorem `polynomial_mem_ideal_of_coeff_mem_ideal` / 定理 `polynomial_mem_ideal_of_coeff_mem_ideal`

English:
theorem polynomial_mem_ideal_of_coeff_mem_ideal
  statement: (I : Ideal R[X]) (p : R[X])
  proof: sum_C_mul_X_pow_eq p ▸ Submodule.sum_mem I fun n _ => I.mul_mem_right _ (hp n)

中文:
定理 polynomial_mem_ideal_of_coeff_mem_ideal
  结论: (I : 理想 R[X]) (p : R[X])
  证明: sum_C_mul_X_pow_eq p ▸ Submodule.sum_mem I fun n _ => I.mul_mem_right _ (hp n)

Depends on / 依赖: I.mul_mem_right, Submodule, Submodule.sum_mem, mul_mem_right, sum_C_mul_X_pow_eq, sum_mem
-/
theorem polynomial_mem_ideal_of_coeff_mem_ideal (I : Ideal R[X]) (p : R[X])
    (hp : forall n : Nat, p.coeff n in I.comap (C : R ->+* R[X])) : p in I :=
  sum_C_mul_X_pow_eq p ▸ Submodule.sum_mem I fun n _ => I.mul_mem_right _ (hp n)

/--
theorem `mem_map_C_iff` / 定理 `mem_map_C_iff`

English:
theorem mem_map_C_iff
  given: {I : Ideal R} {f : R[X]}
  proof: by
  constructor
  · intro hf
    refine Submodule.span_induction ?_ ?_ ?_ ?_ hf
    · intro f hf n
      obtain ⟨x, hx⟩ := (Set.mem_image _ _ _).mp hf
      rw [← hx.right]; rw [coeff_C]
      by_cases h : n = 0
      · simpa [h] using hx.left
      · simp [h]
    · simp
    · exact fun f g _ _ hf 

中文:
定理 mem_map_C_iff
  条件: {I : 理想 R} {f : R[X]}
  证明: by
  constructor
  · intro hf
    refine Submodule.span_induction ?_ ?_ ?_ ?_ hf
    · intro f hf n
      obtain ⟨x, hx⟩ := (Set.mem_image _ _ _).mp hf
      rw [← hx.right]; rw [coeff_C]
      by_cases h : n = 0
      · simpa [h] using hx.left
      · simp [h]
    · simp
    · exact fun f g _ _ hf 

Depends on / 依赖: I.add_mem, I.map, I.mul_mem_left, I.sum_mem, Set.mem_image, Submodule, Submodule.span_induction, add_mem, c.fst, c.snd, coeff_C, coeff_mul, f.coeff, hx.left, hx.right, mem_image, mul_mem_left, smul_eq_mul, span_induction, sum_mem
-/
theorem mem_map_C_iff {I : Ideal R} {f : R[X]} :
    f in (Ideal.map (C : R ->+* R[X]) I : Ideal R[X]) ↔ forall n : Nat, f.coeff n in I := by
  constructor
  · intro hf
    refine Submodule.span_induction ?_ ?_ ?_ ?_ hf
    · intro f hf n
      obtain ⟨x, hx⟩ := (Set.mem_image _ _ _).mp hf
      rw [← hx.right]; rw [coeff_C]
      by_cases h : n = 0
      · simpa [h] using hx.left
      · simp [h]
    · simp
    · exact fun f g _ _ hf hg n => by simp [I.add_mem (hf n) (hg n)]
    · intro f g _ hg n
      rw [smul_eq_mul]; rw [coeff_mul]
      exact I.sum_mem fun c _ => I.mul_mem_left (f.coeff c.fst) (hg c.snd)
  · intro hf
    rw [← sum_monomial_eq f]
    refine (I.map C : Ideal R[X]).sum_mem fun n _ => ?_
    simp only [← C_mul_X_pow_eq_monomial]
    rw [mul_comm]
    exact (I.map C : Ideal R[X]).mul_mem_left _ (mem_map_of_mem _ (hf n))

/--
theorem `_root_.Polynomial.ker_mapRingHom` / 定理 `_root_.Polynomial.ker_mapRingHom`

English:
theorem _root_.Polynomial.ker_mapRingHom
  given: (f : R ->+* S)
  proof: by
  ext
  simp only [RingHom.mem_ker, coe_mapRingHom]
  rw [mem_map_C_iff]; rw [Polynomial.ext_iff]
  simp [RingHom.mem_ker]

中文:
定理 _root_.多项式.ker_mapRingHom
  条件: (f : R ->+* S)
  证明: by
  ext
  simp only [RingHom.mem_ker, coe_mapRingHom]
  rw [mem_map_C_iff]; rw [Polynomial.ext_iff]
  simp [RingHom.mem_ker]

Depends on / 依赖: Polynomial, Polynomial.ext_iff, RingHom, RingHom.mem_ker, coe_mapRingHom, ext_iff, mem_ker, mem_map_C_iff
-/
theorem _root_.Polynomial.ker_mapRingHom (f : R ->+* S) :
    RingHom.ker (Polynomial.mapRingHom f) = (RingHom.ker f).map (C : R ->+* R[X]) := by
  ext
  simp only [RingHom.mem_ker, coe_mapRingHom]
  rw [mem_map_C_iff]; rw [Polynomial.ext_iff]
  simp [RingHom.mem_ker]

variable (I : Ideal R[X])

/--
theorem `mem_leadingCoeffNth` / 定理 `mem_leadingCoeffNth`

English:
theorem mem_leadingCoeffNth
  given: (n : Nat) (x)
  proof: by
  simp only [leadingCoeffNth, degreeLE, Submodule.mem_map, lcoeff_apply, Submodule.mem_inf,
    mem_degreeLE]
  constructor
  · rintro ⟨p, ⟨hpdeg, hpI⟩, rfl⟩
    rcases lt_or_eq_of_le hpdeg with hpdeg | hpdeg
    · refine ⟨0, I.zero_mem, bot_le, ?_⟩
      rw [leadingCoeff_zero]; rw [eq_comm]
    

中文:
定理 mem_leadingCoeffNth
  条件: (n : 自然数) (x)
  证明: by
  simp only [leadingCoeffNth, degreeLE, Submodule.mem_map, lcoeff_apply, Submodule.mem_inf,
    mem_degreeLE]
  constructor
  · rintro ⟨p, ⟨hpdeg, hpI⟩, rfl⟩
    rcases lt_or_eq_of_le hpdeg with hpdeg | hpdeg
    · refine ⟨0, I.zero_mem, bot_le, ?_⟩
      rw [leadingCoeff_zero]; rw [eq_comm]
    

Depends on / 依赖: I.zero_mem, Nat.cast_withBot, Polynomial, Polynomial.leadingCoeff, Submodule, Submodule.mem_inf, Submodule.mem_map, WithBot, WithBot.unbotD_coe, bot_le, cast_withBot, coeff_eq_zero_of_degree_lt, degreeLE, eq_comm, lcoeff_apply, le_of_eq, leadingCoeff, leadingCoeffNth, leadingCoeff_zero, lt_or_eq_of_le
-/
theorem mem_leadingCoeffNth (n : Nat) (x) :
    x in I.leadingCoeffNth n ↔ exists p in I, degree p <= n ∧ p.leadingCoeff = x := by
  simp only [leadingCoeffNth, degreeLE, Submodule.mem_map, lcoeff_apply, Submodule.mem_inf,
    mem_degreeLE]
  constructor
  · rintro ⟨p, ⟨hpdeg, hpI⟩, rfl⟩
    rcases lt_or_eq_of_le hpdeg with hpdeg | hpdeg
    · refine ⟨0, I.zero_mem, bot_le, ?_⟩
      rw [leadingCoeff_zero]; rw [eq_comm]
      exact coeff_eq_zero_of_degree_lt hpdeg
    · refine ⟨p, hpI, le_of_eq hpdeg, ?_⟩
      rw [Polynomial.leadingCoeff]; rw [natDegree]; rw [hpdeg]; rw [Nat.cast_withBot]; rw [WithBot.unbotD_coe]
  · rintro ⟨p, hpI, hpdeg, rfl⟩
    have : natDegree p + (n - natDegree p) = n :=
      add_tsub_cancel_of_le (natDegree_le_of_degree_le hpdeg)
    refine ⟨p * X ^ (n - natDegree p), ⟨?_, I.mul_mem_right _ hpI⟩, ?_⟩
    · apply le_trans (degree_mul_le _ _) _
      apply le_trans (add_le_add degree_le_natDegree (degree_X_pow_le _)) _
      rw [← Nat.cast_add]; rw [this]
    · rw [Polynomial.leadingCoeff, ← coeff_mul_X_pow p (n - natDegree p), this]

/--
theorem `mem_leadingCoeffNth_zero` / 定理 `mem_leadingCoeffNth_zero`

English:
theorem mem_leadingCoeffNth_zero
  given: (x)
  statement: x in I.leadingCoeffNth 0 ↔ C x in I
  proof: (mem_leadingCoeffNth _ _ _).trans
    ⟨fun ⟨p, hpI, hpdeg, hpx⟩ => by
      rwa [← hpx, Polynomial.leadingCoeff,
        Nat.eq_zero_of_le_zero (natDegree_le_of_degree_le hpdeg), ← eq_C_of_degree_le_zero hpdeg],
      fun hx => ⟨C x, hx, degree_C_le, leadingCoeff_C x⟩⟩

中文:
定理 mem_leadingCoeffNth_zero
  条件: (x)
  结论: x in I.leadingCoeffNth 0 ↔ C x in I
  证明: (mem_leadingCoeffNth _ _ _).trans
    ⟨fun ⟨p, hpI, hpdeg, hpx⟩ => by
      rwa [← hpx, Polynomial.leadingCoeff,
        Nat.eq_zero_of_le_zero (natDegree_le_of_degree_le hpdeg), ← eq_C_of_degree_le_zero hpdeg],
      fun hx => ⟨C x, hx, degree_C_le, leadingCoeff_C x⟩⟩

Depends on / 依赖: Nat.eq_zero_of_le_zero, Polynomial, Polynomial.leadingCoeff, degree_C_le, eq_C_of_degree_le_zero, eq_zero_of_le_zero, leadingCoeff, leadingCoeff_C, mem_leadingCoeffNth, natDegree_le_of_degree_le
-/
theorem mem_leadingCoeffNth_zero (x) : x in I.leadingCoeffNth 0 ↔ C x in I :=
  (mem_leadingCoeffNth _ _ _).trans
    ⟨fun ⟨p, hpI, hpdeg, hpx⟩ => by
      rwa [← hpx, Polynomial.leadingCoeff,
        Nat.eq_zero_of_le_zero (natDegree_le_of_degree_le hpdeg), ← eq_C_of_degree_le_zero hpdeg],
      fun hx => ⟨C x, hx, degree_C_le, leadingCoeff_C x⟩⟩

/--
theorem `leadingCoeffNth_mono` / 定理 `leadingCoeffNth_mono`

English:
theorem leadingCoeffNth_mono
  given: {m n : Nat} (H : m <= n)
  statement: I.leadingCoeffNth m <= I.leadingCoeffNth n
  proof: by
  intro r hr
  simp only [mem_leadingCoeffNth] at hr ⊢
  rcases hr with ⟨p, hpI, hpdeg, rfl⟩
  refine ⟨p * X ^ (n - m), I.mul_mem_right _ hpI, ?_, leadingCoeff_mul_X_pow⟩
  refine le_trans (degree_mul_le _ _) ?_
  grw [hpdeg, degree_X_pow_le]
  rw [← Nat.cast_add]; rw [add_tsub_cancel_of_le H]

中文:
定理 leadingCoeffNth_mono
  条件: {m n : 自然数} (H : m <= n)
  结论: I.leadingCoeffNth m <= I.leadingCoeffNth n
  证明: by
  intro r hr
  simp only [mem_leadingCoeffNth] at hr ⊢
  rcases hr with ⟨p, hpI, hpdeg, rfl⟩
  refine ⟨p * X ^ (n - m), I.mul_mem_right _ hpI, ?_, leadingCoeff_mul_X_pow⟩
  refine le_trans (degree_mul_le _ _) ?_
  grw [hpdeg, degree_X_pow_le]
  rw [← Nat.cast_add]; rw [add_tsub_cancel_of_le H]

Depends on / 依赖: I.mul_mem_right, Nat.cast_add, add_tsub_cancel_of_le, cast_add, degree_X_pow_le, degree_mul_le, le_trans, leadingCoeff_mul_X_pow, mem_leadingCoeffNth, mul_mem_right
-/
theorem leadingCoeffNth_mono {m n : Nat} (H : m <= n) : I.leadingCoeffNth m <= I.leadingCoeffNth n := by
  intro r hr
  simp only [mem_leadingCoeffNth] at hr ⊢
  rcases hr with ⟨p, hpI, hpdeg, rfl⟩
  refine ⟨p * X ^ (n - m), I.mul_mem_right _ hpI, ?_, leadingCoeff_mul_X_pow⟩
  refine le_trans (degree_mul_le _ _) ?_
  grw [hpdeg, degree_X_pow_le]
  rw [← Nat.cast_add]; rw [add_tsub_cancel_of_le H]

section leadingCoeff

/--
theorem `mem_leadingCoeff` / 定理 `mem_leadingCoeff`

English:
theorem mem_leadingCoeff
  given: (x)
  statement: x in I.leadingCoeff ↔ exists p in I, Polynomial.leadingCoeff p = x
  proof: by
  rw [leadingCoeff]; rw [Submodule.mem_iSup_of_directed]
  · simp only [mem_leadingCoeffNth]
    constructor
    · rintro ⟨i, p, hpI, _, rfl⟩
      exact ⟨p, hpI, rfl⟩
    rintro ⟨p, hpI, rfl⟩
    exact ⟨natDegree p, p, hpI, degree_le_natDegree, rfl⟩
  intro i j
  exact
    ⟨i + j, I.leadingCoeff

中文:
定理 mem_leadingCoeff
  条件: (x)
  结论: x in I.leadingCoeff ↔ 存在 p in I, 多项式.leadingCoeff p = x
  证明: by
  rw [leadingCoeff]; rw [Submodule.mem_iSup_of_directed]
  · simp only [mem_leadingCoeffNth]
    constructor
    · rintro ⟨i, p, hpI, _, rfl⟩
      exact ⟨p, hpI, rfl⟩
    rintro ⟨p, hpI, rfl⟩
    exact ⟨natDegree p, p, hpI, degree_le_natDegree, rfl⟩
  intro i j
  exact
    ⟨i + j, I.leadingCoeff

Depends on / 依赖: I.leadingCoeffNth_mono, Nat.le_add_left, Nat.le_add_right, Submodule, Submodule.mem_iSup_of_directed, degree_le_natDegree, le_add_left, le_add_right, leadingCoeff, leadingCoeffNth_mono, mem_iSup_of_directed, mem_leadingCoeffNth, natDegree
-/
theorem mem_leadingCoeff (x) : x in I.leadingCoeff ↔ exists p in I, Polynomial.leadingCoeff p = x := by
  rw [leadingCoeff]; rw [Submodule.mem_iSup_of_directed]
  · simp only [mem_leadingCoeffNth]
    constructor
    · rintro ⟨i, p, hpI, _, rfl⟩
      exact ⟨p, hpI, rfl⟩
    rintro ⟨p, hpI, rfl⟩
    exact ⟨natDegree p, p, hpI, degree_le_natDegree, rfl⟩
  intro i j
  exact
    ⟨i + j, I.leadingCoeffNth_mono (Nat.le_add_right _ _),
      I.leadingCoeffNth_mono (Nat.le_add_left _ _)⟩

@[gcongr]
/--
lemma `leadingCoeff_mono` / 引理 `leadingCoeff_mono`

English:
lemma leadingCoeff_mono
  given: {I J : Ideal R[X]} (hIJ : I <= J)
  statement: I.leadingCoeff <= J.leadingCoeff
  proof: by
  intro x hx
  rcases (I.mem_leadingCoeff x).1 hx with ⟨p, hpI, rfl⟩
  exact (J.mem_leadingCoeff p.leadingCoeff).2 ⟨p, hIJ hpI, rfl⟩

@[simp]

中文:
引理 leadingCoeff_mono
  条件: {I J : 理想 R[X]} (hIJ : I <= J)
  结论: I.leadingCoeff <= J.leadingCoeff
  证明: by
  intro x hx
  rcases (I.mem_leadingCoeff x).1 hx with ⟨p, hpI, rfl⟩
  exact (J.mem_leadingCoeff p.leadingCoeff).2 ⟨p, hIJ hpI, rfl⟩

@[simp]

Depends on / 依赖: I.mem_leadingCoeff, J.mem_leadingCoeff, leadingCoeff, mem_leadingCoeff, p.leadingCoeff
-/
lemma leadingCoeff_mono {I J : Ideal R[X]} (hIJ : I <= J) : I.leadingCoeff <= J.leadingCoeff := by
  intro x hx
  rcases (I.mem_leadingCoeff x).1 hx with ⟨p, hpI, rfl⟩
  exact (J.mem_leadingCoeff p.leadingCoeff).2 ⟨p, hIJ hpI, rfl⟩

@[simp]
/--
lemma `map_C_leadingCoeff` / 引理 `map_C_leadingCoeff`

English:
lemma map_C_leadingCoeff
  given: (p : Ideal R)
  statement: (map C p).leadingCoeff = p
  proof: by
  ext x
  constructor
  · intro hx
    rcases ((map C p).mem_leadingCoeff x).1 hx with ⟨f, hf, rfl⟩
    exact p.mem_map_C_iff.1 hf f.natDegree
  · intro hx
    exact ((map C p).mem_leadingCoeff x).2 ⟨C x, mem_map_of_mem C hx, leadingCoeff_C x⟩

@[simp]

中文:
引理 map_C_leadingCoeff
  条件: (p : 理想 R)
  结论: (map C p).leadingCoeff = p
  证明: by
  ext x
  constructor
  · intro hx
    rcases ((map C p).mem_leadingCoeff x).1 hx with ⟨f, hf, rfl⟩
    exact p.mem_map_C_iff.1 hf f.natDegree
  · intro hx
    exact ((map C p).mem_leadingCoeff x).2 ⟨C x, mem_map_of_mem C hx, leadingCoeff_C x⟩

@[simp]

Depends on / 依赖: f.natDegree, leadingCoeff_C, mem_leadingCoeff, mem_map_C_iff, mem_map_of_mem, natDegree, p.mem_map_C_iff
-/
lemma map_C_leadingCoeff (p : Ideal R) : (map C p).leadingCoeff = p := by
  ext x
  constructor
  · intro hx
    rcases ((map C p).mem_leadingCoeff x).1 hx with ⟨f, hf, rfl⟩
    exact p.mem_map_C_iff.1 hf f.natDegree
  · intro hx
    exact ((map C p).mem_leadingCoeff x).2 ⟨C x, mem_map_of_mem C hx, leadingCoeff_C x⟩

@[simp]
/--
lemma `leadingCoeff_top` / 引理 `leadingCoeff_top`

English:
lemma leadingCoeff_top
  statement: (⊤ : Ideal R[X]).leadingCoeff = ⊤
  proof: by simp [← map_top C]

中文:
引理 leadingCoeff_top
  结论: (⊤ : 理想 R[X]).leadingCoeff = ⊤
  证明: by simp [← map_top C]

Depends on / 依赖: map_top
-/
lemma leadingCoeff_top : (⊤ : Ideal R[X]).leadingCoeff = ⊤ := by simp [← map_top C]

/--
lemma `leadingCoeff_mul_le` / 引理 `leadingCoeff_mul_le`

English:
lemma leadingCoeff_mul_le
  given: [NoZeroDivisors R] (I J : Ideal R[X])
  proof: by
  refine (mul_le).2 ?_
  intro a ha b hb
  rcases (I.mem_leadingCoeff a).1 ha with ⟨p, hpI, hp⟩
  rcases (J.mem_leadingCoeff b).1 hb with ⟨q, hqJ, hq⟩
  exact ((I * J).mem_leadingCoeff (a * b)).2 ⟨p * q, mul_mem_mul hpI hqJ, by simp [hp, hq]⟩

中文:
引理 leadingCoeff_mul_le
  条件: [无零因子 R] (I J : 理想 R[X])
  证明: by
  refine (mul_le).2 ?_
  intro a ha b hb
  rcases (I.mem_leadingCoeff a).1 ha with ⟨p, hpI, hp⟩
  rcases (J.mem_leadingCoeff b).1 hb with ⟨q, hqJ, hq⟩
  exact ((I * J).mem_leadingCoeff (a * b)).2 ⟨p * q, mul_mem_mul hpI hqJ, by simp [hp, hq]⟩

Depends on / 依赖: I.mem_leadingCoeff, J.mem_leadingCoeff, mem_leadingCoeff, mul_le, mul_mem_mul
-/
lemma leadingCoeff_mul_le [NoZeroDivisors R] (I J : Ideal R[X]) :
    I.leadingCoeff * J.leadingCoeff <= (I * J).leadingCoeff := by
  refine (mul_le).2 ?_
  intro a ha b hb
  rcases (I.mem_leadingCoeff a).1 ha with ⟨p, hpI, hp⟩
  rcases (J.mem_leadingCoeff b).1 hb with ⟨q, hqJ, hq⟩
  exact ((I * J).mem_leadingCoeff (a * b)).2 ⟨p * q, mul_mem_mul hpI hqJ, by simp [hp, hq]⟩

/--
lemma `leadingCoeff_finset_prod_le` / 引理 `leadingCoeff_finset_prod_le`

English:
lemma leadingCoeff_finset_prod_le
  statement: [NoZeroDivisors R] {ι : Type*} (s : Finset ι)
  proof: by
  classical
  refine Finset.induction_on s (by simp) ?_
  intro i s hi hs
  simpa [hi] using (mul_mono_right hs).trans (leadingCoeff_mul_le (f i) (s.prod f))

中文:
引理 leadingCoeff_finset_prod_le
  结论: [无零因子 R] {ι : 类型} (s : 有限集 ι)
  证明: by
  classical
  refine Finset.induction_on s (by simp) ?_
  intro i s hi hs
  simpa [hi] using (mul_mono_right hs).trans (leadingCoeff_mul_le (f i) (s.prod f))

Depends on / 依赖: Finset, Finset.induction_on, classical, induction_on, leadingCoeff_mul_le, mul_mono_right, s.prod
-/
lemma leadingCoeff_finset_prod_le [NoZeroDivisors R] {ι : Type*} (s : Finset ι)
    (f : ι -> Ideal R[X]) : (s.prod fun i => (f i).leadingCoeff) <= (s.prod f).leadingCoeff := by
  classical
  refine Finset.induction_on s (by simp) ?_
  intro i s hi hs
  simpa [hi] using (mul_mono_right hs).trans (leadingCoeff_mul_le (f i) (s.prod f))

/--
lemma `leadingCoeff_pow_le` / 引理 `leadingCoeff_pow_le`

English:
lemma leadingCoeff_pow_le
  given: [NoZeroDivisors R] (n : Nat)
  proof: by
  simpa using leadingCoeff_finset_prod_le (Finset.range n) fun _ => I

中文:
引理 leadingCoeff_pow_le
  条件: [无零因子 R] (n : 自然数)
  证明: by
  simpa using leadingCoeff_finset_prod_le (Finset.range n) fun _ => I

Depends on / 依赖: Finset, Finset.range, leadingCoeff_finset_prod_le
-/
lemma leadingCoeff_pow_le [NoZeroDivisors R] (n : Nat) :
    I.leadingCoeff ^ n <= (I ^ n).leadingCoeff := by
  simpa using leadingCoeff_finset_prod_le (Finset.range n) fun _ => I

end leadingCoeff

/--
theorem `_root_.Polynomial.coeff_prod_mem_ideal_pow_tsub` / 定理 `_root_.Polynomial.coeff_prod_mem_ideal_pow_tsub`

English:
theorem _root_.Polynomial.coeff_prod_mem_ideal_pow_tsub
  statement: {ι : Type*} (s : Finset ι) (f : ι -> R[X])
  proof: by
  classical
    induction s using Finset.induction generalizing k with
    | empty =>
      rw [sum_empty]; rw [prod_empty]; rw [coeff_one]; rw [zero_tsub]; rw [pow_zero]; rw [Ideal.one_eq_top]
      exact Submodule.mem_top
    | insert a s ha hs =>
      rw [sum_insert ha]; rw [prod_insert ha]; 

中文:
定理 _root_.多项式.coeff_prod_mem_ideal_pow_tsub
  结论: {ι : 类型} (s : 有限集 ι) (f : ι -> R[X])
  证明: by
  classical
    induction s using Finset.induction generalizing k with
    | empty =>
      rw [sum_empty]; rw [prod_empty]; rw [coeff_one]; rw [zero_tsub]; rw [pow_zero]; rw [Ideal.one_eq_top]
      exact Submodule.mem_top
    | insert a s ha hs =>
      rw [sum_insert ha]; rw [prod_insert ha]; 

Depends on / 依赖: Finset, Finset.induction, Ideal.mul_mem_mul, Ideal.one_eq_top, Ideal.pow_le_pow_right, Submodule, Submodule.mem_top, add_tsub_add_le_tsub_add_tsub, classical, coeff_mul, coeff_one, generalizing, insert, mem_antidiagonal, mem_antidiagonal.mp, mem_top, mul_mem_mul, one_eq_top, pow_add, pow_le_pow_right
-/
theorem _root_.Polynomial.coeff_prod_mem_ideal_pow_tsub {ι : Type*} (s : Finset ι) (f : ι -> R[X])
    (I : Ideal R) (n : ι -> Nat) (h : forall i in s, forall (k), (f i).coeff k in I ^ (n i - k)) (k : Nat) :
    (s.prod f).coeff k in I ^ (s.sum n - k) := by
  classical
    induction s using Finset.induction generalizing k with
    | empty =>
      rw [sum_empty]; rw [prod_empty]; rw [coeff_one]; rw [zero_tsub]; rw [pow_zero]; rw [Ideal.one_eq_top]
      exact Submodule.mem_top
    | insert a s ha hs =>
      rw [sum_insert ha]; rw [prod_insert ha]; rw [coeff_mul]
      apply sum_mem
      rintro ⟨i, j⟩ e
      obtain rfl : i + j = k := mem_antidiagonal.mp e
      apply Ideal.pow_le_pow_right add_tsub_add_le_tsub_add_tsub
      rw [pow_add]
      exact Ideal.mul_mem_mul (by grind) (by grind)

end CommSemiring

section Ring

variable [Ring R]

variable (R) in
/--
theorem `_root_.Polynomial.not_isField` / 定理 `_root_.Polynomial.not_isField`

English:
theorem _root_.Polynomial.not_isField
  statement: ¬IsField R[X]
  proof: by
  nontriviality R
  intro hR
  obtain ⟨p, hp⟩ := hR.mul_inv_cancel X_ne_zero
  have hp0 : p != 0 := right_ne_zero_of_mul_eq_one hp
  have := degree_lt_degree_mul_X hp0
  rw [← X_mul]; rw [congr_arg degree hp]; rw [degree_one]; rw [Nat.WithBot.lt_zero_iff]; rw [degree_eq_bot] at this
  exact hp0 t

中文:
定理 _root_.多项式.not_isField
  结论: ¬是域 R[X]
  证明: by
  nontriviality R
  intro hR
  obtain ⟨p, hp⟩ := hR.mul_inv_cancel X_ne_zero
  have hp0 : p != 0 := right_ne_zero_of_mul_eq_one hp
  have := degree_lt_degree_mul_X hp0
  rw [← X_mul]; rw [congr_arg degree hp]; rw [degree_one]; rw [Nat.WithBot.lt_zero_iff]; rw [degree_eq_bot] at this
  exact hp0 t

Depends on / 依赖: Nat.WithBot.lt_zero_iff, WithBot, X_mul, X_ne_zero, congr_arg, degree, degree_eq_bot, degree_lt_degree_mul_X, degree_one, hR.mul_inv_cancel, lt_zero_iff, mul_inv_cancel, nontriviality, right_ne_zero_of_mul_eq_one
-/
theorem _root_.Polynomial.not_isField : ¬IsField R[X] := by
  nontriviality R
  intro hR
  obtain ⟨p, hp⟩ := hR.mul_inv_cancel X_ne_zero
  have hp0 : p != 0 := right_ne_zero_of_mul_eq_one hp
  have := degree_lt_degree_mul_X hp0
  rw [← X_mul]; rw [congr_arg degree hp]; rw [degree_one]; rw [Nat.WithBot.lt_zero_iff]; rw [degree_eq_bot] at this
  exact hp0 this

@[deprecated (since := "2026-08-01")]
alias polynomial_not_isField := Polynomial.not_isField

/--
theorem `eq_zero_of_constant_mem_of_maximal` / 定理 `eq_zero_of_constant_mem_of_maximal`

English:
theorem eq_zero_of_constant_mem_of_maximal
  statement: (hR : IsField R) (I : Ideal R[X]) [hI : I.IsMaximal]
  proof: by
  refine Classical.by_contradiction fun hx0 => hI.ne_top ((eq_top_iff_one I).2 ?_)
  obtain ⟨y, hy⟩ := hR.mul_inv_cancel hx0
  convert! I.mul_mem_left (C y) hx
  rw [← C.map_mul]; rw [hR.mul_comm y x]; rw [hy]; rw [map_one]

中文:
定理 eq_zero_of_constant_mem_of_maximal
  结论: (hR : 是域 R) (I : 理想 R[X]) [hI : I.是极大]
  证明: by
  refine Classical.by_contradiction fun hx0 => hI.ne_top ((eq_top_iff_one I).2 ?_)
  obtain ⟨y, hy⟩ := hR.mul_inv_cancel hx0
  convert! I.mul_mem_left (C y) hx
  rw [← C.map_mul]; rw [hR.mul_comm y x]; rw [hy]; rw [map_one]

Depends on / 依赖: C.map_mul, Classical, Classical.by_contradiction, I.mul_mem_left, by_contradiction, convert, eq_top_iff_one, hI.ne_top, hR.mul_comm, hR.mul_inv_cancel, map_mul, map_one, mul_comm, mul_inv_cancel, mul_mem_left, ne_top
-/
theorem eq_zero_of_constant_mem_of_maximal (hR : IsField R) (I : Ideal R[X]) [hI : I.IsMaximal]
    (x : R) (hx : C x in I) : x = 0 := by
  refine Classical.by_contradiction fun hx0 => hI.ne_top ((eq_top_iff_one I).2 ?_)
  obtain ⟨y, hy⟩ := hR.mul_inv_cancel hx0
  convert! I.mul_mem_left (C y) hx
  rw [← C.map_mul]; rw [hR.mul_comm y x]; rw [hy]; rw [map_one]

end Ring

section CommRing

variable [CommRing R]

/--
theorem `isPrime_map_C_iff_isPrime` / 定理 `isPrime_map_C_iff_isPrime`

English:
theorem isPrime_map_C_iff_isPrime
  given: (P : Ideal R)
  proof: by
  -- Note: the following proof avoids quotient rings
  -- It can be golfed substantially by using something like
  -- `(Quotient.isDomain_iff_prime (map C P : Ideal R[X]))`
  constructor
  · intro H
    have := comap_isPrime C (map C P)
    convert! this using 1
    ext x
    simp only [mem_comap

中文:
定理 isPrime_map_C_iff_isPrime
  条件: (P : 理想 R)
  证明: by
  -- Note: the following proof avoids quotient rings
  -- It can be golfed substantially by using something like
  -- `(Quotient.isDomain_iff_prime (map C P : Ideal R[X]))`
  constructor
  · intro H
    have := comap_isPrime C (map C P)
    convert! this using 1
    ext x
    simp only [mem_comap
-/
theorem isPrime_map_C_iff_isPrime (P : Ideal R) :
    IsPrime (map (C : R ->+* R[X]) P : Ideal R[X]) ↔ IsPrime P := by
  -- Note: the following proof avoids quotient rings
  -- It can be golfed substantially by using something like
  -- `(Quotient.isDomain_iff_prime (map C P : Ideal R[X]))`
  constructor
  · intro H
    have := comap_isPrime C (map C P)
    convert! this using 1
    ext x
    simp only [mem_comap, mem_map_C_iff]
    constructor
    · rintro h (- | n)
      · rwa [coeff_C_zero]
      · simp only [coeff_C_of_ne_zero (Nat.succ_ne_zero _), Submodule.zero_mem]
    · intro h
      simpa only [coeff_C_zero] using h 0
  · intro h
    constructor
    · rw [Ne, eq_top_iff_one, mem_map_C_iff, not_forall]
      use 0
      rw [coeff_one_zero]; rw [← eq_top_iff_one]
      exact h.1
    · intro f g
      simp only [mem_map_C_iff]
      contrapose!
      rintro ⟨hf, hg⟩
      classical
        let m := Nat.find hf
        let n := Nat.find hg
        refine ⟨m + n, ?_⟩
        rw [coeff_mul]; rw [← Finset.insert_erase ((Finset.mem_antidiagonal (a := (m]; rw [n))).mpr rfl)]; rw [Finset.sum_insert (Finset.notMem_erase _ _)]; rw [(P.add_mem_iff_left _).not]
        · apply mt h.2
          rw [not_or]
          exact ⟨Nat.find_spec hf, Nat.find_spec hg⟩
        apply P.sum_mem
        rintro ⟨i, j⟩ hij
        rw [Finset.mem_erase]; rw [Finset.mem_antidiagonal] at hij
        simp only [Ne, Prod.mk_inj, not_and_or] at hij
        obtain hi | hj : i < m ∨ j < n := by
          lia
        · rw [mul_comm]
          apply P.mul_mem_left
          exact Classical.not_not.1 (Nat.find_min hf hi)
        · apply P.mul_mem_left
          exact Classical.not_not.1 (Nat.find_min hg hj)

/--
Instance `isPrime_map_C_of_isPrime` / 实例 `isPrime_map_C_of_isPrime`

English:
instance isPrime_map_C_of_isPrime
  signature: {P : Ideal R} [IsPrime P]
  body: (isPrime_map_C_iff_isPrime P).mpr ‹_›

中文:
实例 isPrime_map_C_of_isPrime
  签名: {P : 理想 R} [是素 P]
  定义体: (isPrime_map_C_iff_isPrime P).mpr ‹_›

Depends on / 依赖: isPrime_map_C_iff_isPrime
-/
instance isPrime_map_C_of_isPrime {P : Ideal R} [IsPrime P] :
    IsPrime (map (C : R ->+* R[X]) P : Ideal R[X]) :=
  (isPrime_map_C_iff_isPrime P).mpr ‹_›

/--
theorem `is_fg_degreeLE` / 定理 `is_fg_degreeLE`

English:
theorem is_fg_degreeLE
  given: [IsNoetherianRing R] (I : Ideal R[X]) (n : Nat)
  proof: letI := Classical.decEq R
  isNoetherian_submodule_left.1
    (isNoetherian_of_fg_of_noetherian _ ⟨_, degreeLE_eq_span_X_pow.symm⟩) _

中文:
定理 is_fg_degreeLE
  条件: [是Noether环 R] (I : 理想 R[X]) (n : 自然数)
  证明: letI := Classical.decEq R
  isNoetherian_submodule_left.1
    (isNoetherian_of_fg_of_noetherian _ ⟨_, degreeLE_eq_span_X_pow.symm⟩) _

Depends on / 依赖: Classical, Classical.decEq, degreeLE_eq_span_X_pow, degreeLE_eq_span_X_pow.symm, isNoetherian_of_fg_of_noetherian, isNoetherian_submodule_left
-/
theorem is_fg_degreeLE [IsNoetherianRing R] (I : Ideal R[X]) (n : Nat) :
    Submodule.FG (I.degreeLE n) :=
  letI := Classical.decEq R
  isNoetherian_submodule_left.1
    (isNoetherian_of_fg_of_noetherian _ ⟨_, degreeLE_eq_span_X_pow.symm⟩) _

/--
lemma `map_C_comap_of_comap_eq_leadingCoeff` / 引理 `map_C_comap_of_comap_eq_leadingCoeff`

English:
lemma map_C_comap_of_comap_eq_leadingCoeff
  given: (I : Ideal R[X]) (hI : comap C I = I.leadingCoeff)
  proof: by
  refine le_antisymm map_comap_le (fun f hfI => ?_)
  induction hn : f.natDegree using Nat.strong_induction_on generalizing f with | _ _ ih
  have h : C f.leadingCoeff * X ^ f.natDegree in map C (comap C I) :=
(map C (comap C I)).mul_mem_right (X ^ f.natDegree) mem_map_of_mem C by
      simpa [hI

中文:
引理 map_C_comap_of_comap_eq_leadingCoeff
  条件: (I : 理想 R[X]) (hI : comap C I = I.leadingCoeff)
  证明: by
  refine le_antisymm map_comap_le (fun f hfI => ?_)
  induction hn : f.natDegree using Nat.strong_induction_on generalizing f with | _ _ ih
  have h : C f.leadingCoeff * X ^ f.natDegree in map C (comap C I) :=
(map C (comap C I)).mul_mem_right (X ^ f.natDegree) mem_map_of_mem C by
      simpa [hI

Depends on / 依赖: I.mem_leadingCoeff, I.sub_mem, Nat.strong_induction_on, eraseLead, eraseLead_natDegree_lt_or_eraseLead_eq_zero, f.eraseLead, f.eraseLead_natDegree_lt_or_eraseLead_eq_zero, f.leadingCoeff, f.natDegree, generalizing, le_antisymm, leadingCoeff, map_comap_le, mem_leadingCoeff, mem_map_of_mem, mul_mem_right, natDegree, strong_induction_on, sub_mem
-/
lemma map_C_comap_of_comap_eq_leadingCoeff (I : Ideal R[X]) (hI : comap C I = I.leadingCoeff) :
    map C (comap C I) = I := by
  refine le_antisymm map_comap_le (fun f hfI => ?_)
  induction hn : f.natDegree using Nat.strong_induction_on generalizing f with | _ _ ih
  have h : C f.leadingCoeff * X ^ f.natDegree in map C (comap C I) :=
(map C (comap C I)).mul_mem_right (X ^ f.natDegree) mem_map_of_mem C by
      simpa [hI] using (I.mem_leadingCoeff f.leadingCoeff).2 ⟨f, hfI, rfl⟩
  rcases f.eraseLead_natDegree_lt_or_eraseLead_eq_zero with hlt | hzero
  · have he : f.eraseLead in I := by simpa using I.sub_mem hfI (map_comap_le h)
    simpa using (map C (comap C I)).add_mem (ih _ (by simpa [hn] using hlt) _ he rfl) h
  · rwa [← f.eraseLead_add_C_mul_X_pow, hzero, zero_add]

end CommRing

end Ideal

section Ideal

open Submodule Set

variable [Semiring R] {f : R[X]} {I : Ideal R[X]}

/--
theorem `span_le_of_C_coeff_mem` / 定理 `span_le_of_C_coeff_mem`

English:
theorem span_le_of_C_coeff_mem
  given: (cf : forall i : Nat, C (f.coeff i) in I)
  proof: by
  simp only [@eq_comm _ _ (C _)]
  exact (Ideal.span_le.trans range_subset_iff).mpr cf

中文:
定理 span_le_of_C_coeff_mem
  条件: (cf : 对任意 i : 自然数, C (f.coeff i) in I)
  证明: by
  simp only [@eq_comm _ _ (C _)]
  exact (Ideal.span_le.trans range_subset_iff).mpr cf

Depends on / 依赖: Ideal.span_le.trans, eq_comm, range_subset_iff, span_le
-/
theorem span_le_of_C_coeff_mem (cf : forall i : Nat, C (f.coeff i) in I) :
    Ideal.span { g | exists i, g = C (f.coeff i) } <= I := by
  simp only [@eq_comm _ _ (C _)]
  exact (Ideal.span_le.trans range_subset_iff).mpr cf

/--
theorem `mem_span_C_coeff` / 定理 `mem_span_C_coeff`

English:
theorem mem_span_C_coeff
  statement: f in Ideal.span { g : R[X] | exists i : Nat, g = C (coeff f i) }
  proof: by
  let p := Ideal.span { g : R[X] | exists i : Nat, g = C (coeff f i) }
  nth_rw 2 [(sum_C_mul_X_pow_eq f).symm]
  refine Submodule.sum_mem _ fun n _hn => ?_
  dsimp
  have : C (coeff f n) in p := by
    apply subset_span
    rw [mem_ofPred_eq]
    use n
  have : monomial n (1 : R) • C (coeff f n)

中文:
定理 mem_span_C_coeff
  结论: f in 理想.span { g : R[X] | 存在 i : 自然数, g = C (coeff f i) }
  证明: by
  let p := Ideal.span { g : R[X] | exists i : Nat, g = C (coeff f i) }
  nth_rw 2 [(sum_C_mul_X_pow_eq f).symm]
  refine Submodule.sum_mem _ fun n _hn => ?_
  dsimp
  have : C (coeff f n) in p := by
    apply subset_span
    rw [mem_ofPred_eq]
    use n
  have : monomial n (1 : R) • C (coeff f n)

Depends on / 依赖: C_mul_X_pow_eq_monomial, Ideal.span, Submodule, Submodule.sum_mem, convert, mem_ofPred_eq, monomial, monomial_mul_C, nth_rw, one_mul, p.smul_mem, smul_eq_mul, smul_mem, subset_span, sum_C_mul_X_pow_eq, sum_mem
-/
theorem mem_span_C_coeff : f in Ideal.span { g : R[X] | exists i : Nat, g = C (coeff f i) } := by
  let p := Ideal.span { g : R[X] | exists i : Nat, g = C (coeff f i) }
  nth_rw 2 [(sum_C_mul_X_pow_eq f).symm]
  refine Submodule.sum_mem _ fun n _hn => ?_
  dsimp
  have : C (coeff f n) in p := by
    apply subset_span
    rw [mem_ofPred_eq]
    use n
  have : monomial n (1 : R) • C (coeff f n) in p := p.smul_mem _ this
  convert! this using 1
  simp only [monomial_mul_C, one_mul, smul_eq_mul]
  rw [← C_mul_X_pow_eq_monomial]

/--
theorem `exists_C_coeff_notMem` / 定理 `exists_C_coeff_notMem`

English:
theorem exists_C_coeff_notMem
  statement: f ∉ I -> exists i : Nat, C (coeff f i) ∉ I
  proof: Not.imp_symm fun cf => span_le_of_C_coeff_mem (not_exists_not.mp cf) mem_span_C_coeff

中文:
定理 存在_C_coeff_notMem
  结论: f ∉ I -> 存在 i : 自然数, C (coeff f i) ∉ I
  证明: Not.imp_symm fun cf => span_le_of_C_coeff_mem (not_exists_not.mp cf) mem_span_C_coeff

Depends on / 依赖: Not.imp_symm, imp_symm, mem_span_C_coeff, not_exists_not, not_exists_not.mp, span_le_of_C_coeff_mem
-/
theorem exists_C_coeff_notMem : f ∉ I -> exists i : Nat, C (coeff f i) ∉ I :=
  Not.imp_symm fun cf => span_le_of_C_coeff_mem (not_exists_not.mp cf) mem_span_C_coeff

end Ideal

variable {σ : Type v} {M : Type w}
variable [CommRing R] [CommRing S] [AddCommGroup M] [Module R M]

section Prime

variable (σ) {r : R}

namespace Polynomial

/--
theorem `prime_C_iff` / 定理 `prime_C_iff`

English:
theorem prime_C_iff
  statement: Prime (C r) ↔ Prime r
  proof: ⟨comap_prime C (evalRingHom (0 : R)) fun _ => eval_C, fun hr => by
    have := hr.1
    rw [← Ideal.span_singleton_prime] at hr ⊢
    · rw [← Set.image_singleton, ← Ideal.map_span]
      infer_instance
    · intro h; apply (this (C_eq_zero.mp h))
    · assumption⟩

中文:
定理 prime_C_iff
  结论: 素 (C r) ↔ 素 r
  证明: ⟨comap_prime C (evalRingHom (0 : R)) fun _ => eval_C, fun hr => by
    have := hr.1
    rw [← Ideal.span_singleton_prime] at hr ⊢
    · rw [← Set.image_singleton, ← Ideal.map_span]
      infer_instance
    · intro h; apply (this (C_eq_zero.mp h))
    · assumption⟩

Depends on / 依赖: C_eq_zero, C_eq_zero.mp, Ideal.map_span, Ideal.span_singleton_prime, Set.image_singleton, comap_prime, evalRingHom, eval_C, image_singleton, infer_instance, map_span, span_singleton_prime
-/
theorem prime_C_iff : Prime (C r) ↔ Prime r :=
  ⟨comap_prime C (evalRingHom (0 : R)) fun _ => eval_C, fun hr => by
    have := hr.1
    rw [← Ideal.span_singleton_prime] at hr ⊢
    · rw [← Set.image_singleton, ← Ideal.map_span]
      infer_instance
    · intro h; apply (this (C_eq_zero.mp h))
    · assumption⟩

end Polynomial

namespace MvPolynomial

instance {ι R : Type*} [CommSemiring R] [IsEmpty ι] : Module.Finite R (MvPolynomial ι R) :=
  Module.Finite.equiv (MvPolynomial.isEmptyAlgEquiv R ι).toLinearEquiv.symm

/--
theorem `prime_C_iff_of_fintype` / 定理 `prime_C_iff_of_fintype`

English:
theorem prime_C_iff_of_fintype
  given: {R : Type u} (σ : Type v) {r : R} [CommRing R] [Finite σ]
  proof: by
  have := Fintype.ofFinite σ
  rw [← MulEquiv.prime_iff (renameEquiv R (Fintype.equivFin σ))]
  convert_to Prime (C r) ↔ _
  · congr!
    simp only [renameEquiv_apply, algHom_C, algebraMap_eq]
  · induction Fintype.card σ with
    | zero => simpa using MulEquiv.prime_iff (isEmptyAlgEquiv R (Fin 0

中文:
定理 prime_C_iff_of_fintype
  条件: {R : 类型u} (σ : 类型v) {r : R} [交换环 R] [有限 σ]
  证明: by
  have := Fintype.ofFinite σ
  rw [← MulEquiv.prime_iff (renameEquiv R (Fintype.equivFin σ))]
  convert_to Prime (C r) ↔ _
  · congr!
    simp only [renameEquiv_apply, algHom_C, algebraMap_eq]
  · induction Fintype.card σ with
    | zero => simpa using MulEquiv.prime_iff (isEmptyAlgEquiv R (Fin 0
-/
private theorem prime_C_iff_of_fintype {R : Type u} (σ : Type v) {r : R} [CommRing R] [Finite σ] :
    Prime (C r : MvPolynomial σ R) ↔ Prime r := by
  have := Fintype.ofFinite σ
  rw [← MulEquiv.prime_iff (renameEquiv R (Fintype.equivFin σ))]
  convert_to Prime (C r) ↔ _
  · congr!
    simp only [renameEquiv_apply, algHom_C, algebraMap_eq]
  · induction Fintype.card σ with
    | zero => simpa using MulEquiv.prime_iff (isEmptyAlgEquiv R (Fin 0)).symm (p := r)
    | succ d hd =>
      convert! MulEquiv.prime_iff (finSuccEquiv R d).symm (p := Polynomial.C (C r))
      · simp [← finSuccEquiv_comp_C_eq_C]
      · simp [← hd, Polynomial.prime_C_iff]

/--
theorem `prime_C_iff` / 定理 `prime_C_iff`

English:
theorem prime_C_iff
  statement: Prime (C r : MvPolynomial σ R) ↔ Prime r
  proof: ⟨comap_prime C constantCoeff (constantCoeff_C _), fun hr =>
⟨fun h => hr.1 by
        rw [← C_inj]; rw [h]
        simp,
      fun h =>
hr.2.1 by
        rw [← constantCoeff_C _ r]
        exact h.map _,
      fun a b hd => by
      obtain ⟨s, a', b', rfl, rfl⟩ := exists_finset_rename₂ a b
      rw 

中文:
定理 prime_C_iff
  结论: 素 (C r : 多元多项式 σ R) ↔ 素 r
  证明: ⟨comap_prime C constantCoeff (constantCoeff_C _), fun hr =>
⟨fun h => hr.1 by
        rw [← C_inj]; rw [h]
        simp,
      fun h =>
hr.2.1 by
        rw [← constantCoeff_C _ r]
        exact h.map _,
      fun a b hd => by
      obtain ⟨s, a', b', rfl, rfl⟩ := exists_finset_rename₂ a b
      rw 

Depends on / 依赖: C_inj, Subtype, Subtype.val_injective, _root_, _root_.map_dvd, algebraMap, algebraMap_eq, comap_prime, constantCoeff, constantCoeff_C, convert, h.map, killCompl, map_dvd, prime_C_iff_of_fintype, rename_C, toRingHom, val_injective
-/
theorem prime_C_iff : Prime (C r : MvPolynomial σ R) ↔ Prime r :=
  ⟨comap_prime C constantCoeff (constantCoeff_C _), fun hr =>
⟨fun h => hr.1 by
        rw [← C_inj]; rw [h]
        simp,
      fun h =>
hr.2.1 by
        rw [← constantCoeff_C _ r]
        exact h.map _,
      fun a b hd => by
      obtain ⟨s, a', b', rfl, rfl⟩ := exists_finset_rename₂ a b
      rw [← algebraMap_eq] at hd
      have : algebraMap R _ r ∣ a' * b' := by
        convert! _root_.map_dvd (killCompl Subtype.val_injective) hd
        · simp
        · simp
      rw [← rename_C ((↑) : s -> σ)]
      let f := (rename (R := R) ((↑) : s -> σ)).toRingHom
      exact (((prime_C_iff_of_fintype s).2 hr).2.2 a' b' this).imp (map_dvd f) (map_dvd f)⟩⟩

variable {σ}

/--
theorem `prime_rename_iff` / 定理 `prime_rename_iff`

English:
theorem prime_rename_iff
  given: (s : Set σ) {p : MvPolynomial s R}
  proof: by
  classical
    symm
    let eqv :=
      (sumAlgEquiv R (↥sᶜ) s).symm.trans
        (renameEquiv R <| (Equiv.sumComm (↥sᶜ) s).trans <| Equiv.Set.sumCompl s)
    have : rename Subtype.val = eqv.toAlgHom.comp (Algebra.algHom _ (MvPolynomial s R) _) := by
      apply algHom_ext
      simp [eqv, ren

中文:
定理 prime_rename_iff
  条件: (s : 集合 σ) {p : 多元多项式 s R}
  证明: by
  classical
    symm
    let eqv :=
      (sumAlgEquiv R (↥sᶜ) s).symm.trans
        (renameEquiv R <| (Equiv.sumComm (↥sᶜ) s).trans <| Equiv.Set.sumCompl s)
    have : rename Subtype.val = eqv.toAlgHom.comp (Algebra.algHom _ (MvPolynomial s R) _) := by
      apply algHom_ext
      simp [eqv, ren

Depends on / 依赖: Algebra, Algebra.algHom, Equiv.Set.sumCompl, Equiv.sumComm, Finsupp, Finsupp.mapDomain.addMonoidHom, MulEquiv, MulEquiv.prime_iff, MvPolynomial, Subtype, Subtype.val, addMonoidHom, algHom, algHom_ext, apply_fun, classical, eqv.toAlgHom.comp, mapDomain, monomial, prime_C_iff
-/
theorem prime_rename_iff (s : Set σ) {p : MvPolynomial s R} :
    Prime (rename ((↑) : s -> σ) p) ↔ Prime (p : MvPolynomial s R) := by
  classical
    symm
    let eqv :=
      (sumAlgEquiv R (↥sᶜ) s).symm.trans
        (renameEquiv R <| (Equiv.sumComm (↥sᶜ) s).trans <| Equiv.Set.sumCompl s)
    have : rename Subtype.val = eqv.toAlgHom.comp (Algebra.algHom _ (MvPolynomial s R) _) := by
      apply algHom_ext
      simp [eqv, rename, X, monomial, Algebra.algHom, renameEquiv, Finsupp.mapDomain.addMonoidHom,
        sumAlgEquiv, C]
    apply_fun (· p) at this
    simpa [this, MulEquiv.prime_iff, Algebra.algHom] using (prime_C_iff _).symm

end MvPolynomial

end Prime

/--
theorem `Polynomial.isNoetherianRing` / 定理 `Polynomial.isNoetherianRing`

English:
theorem Polynomial.isNoetherianRing
  given: [inst : IsNoetherianRing R]
  statement: IsNoetherianRing R[X]
  proof: isNoetherianRing_iff.2
    ⟨fun I : Ideal R[X] =>
      let M := inst.wf.min (Set.range I.leadingCoeffNth) ⟨_, ⟨0, rfl⟩⟩
      have hm : M in Set.range I.leadingCoeffNth := WellFounded.min_mem _ _ _
      let ⟨N, HN⟩ := hm
      let ⟨s, hs⟩ := I.is_fg_degreeLE N
      have hm2 : forall k, I.leadingC

中文:
定理 多项式.isNoetherianRing
  条件: [inst : 是Noether环 R]
  结论: 是Noether环 R[X]
  证明: isNoetherianRing_iff.2
    ⟨fun I : Ideal R[X] =>
      let M := inst.wf.min (Set.range I.leadingCoeffNth) ⟨_, ⟨0, rfl⟩⟩
      have hm : M in Set.range I.leadingCoeffNth := WellFounded.min_mem _ _ _
      let ⟨N, HN⟩ := hm
      let ⟨s, hs⟩ := I.is_fg_degreeLE N
      have hm2 : forall k, I.leadingC
-/
protected theorem Polynomial.isNoetherianRing [inst : IsNoetherianRing R] : IsNoetherianRing R[X] :=
  isNoetherianRing_iff.2
    ⟨fun I : Ideal R[X] =>
      let M := inst.wf.min (Set.range I.leadingCoeffNth) ⟨_, ⟨0, rfl⟩⟩
      have hm : M in Set.range I.leadingCoeffNth := WellFounded.min_mem _ _ _
      let ⟨N, HN⟩ := hm
      let ⟨s, hs⟩ := I.is_fg_degreeLE N
      have hm2 : forall k, I.leadingCoeffNth k <= M := fun k =>
        Or.casesOn (le_or_gt k N) (fun h => HN ▸ I.leadingCoeffNth_mono h) fun h _ hx =>
          Classical.by_contradiction fun hxm =>
            have : ¬M < I.leadingCoeffNth k := by
              refine WellFounded.not_lt_min inst.wf _ ?_; exact ⟨k, rfl⟩
            this ⟨HN ▸ I.leadingCoeffNth_mono (le_of_lt h), fun H => hxm (H hx)⟩
      have hs2 : forall {x}, x in I.degreeLE N -> x in Ideal.span (↑s : Set R[X]) :=
        hs ▸ fun hx =>
          Submodule.span_induction (hx := hx) (fun _ hx => Ideal.subset_span hx) (Ideal.zero_mem _)
            (fun _ _ _ _ => Ideal.add_mem _) fun c f _ hf => f.C_mul' c ▸ Ideal.mul_mem_left _ _ hf
      ⟨s, le_antisymm (Ideal.span_le.2 fun x hx =>
          have : x in I.degreeLE N := hs ▸ Submodule.subset_span hx
          this.2) <| by
        have : Submodule.span R[X] ↑s = Ideal.span ↑s := rfl
        rw [this]
        intro p hp
        generalize hn : p.natDegree = k
        induction k using Nat.strong_induction_on generalizing p with | _ k ih
        rcases le_or_gt k N with h | h
        · subst k
          refine hs2 ⟨Polynomial.mem_degreeLE.2
            (le_trans Polynomial.degree_le_natDegree <| WithBot.coe_le_coe.2 h), hp⟩
        · have hp0 : p != 0 := by
            rintro rfl
            cases hn
            exact Nat.not_lt_zero _ h
          have : (0 : R) != 1 := by
            intro h
            apply hp0
            ext i
            refine (mul_one _).symm.trans ?_
            rw [← h]; rw [mul_zero]
            rfl
          have : Nontrivial R := ⟨⟨0, 1, this⟩⟩
          have : p.leadingCoeff in I.leadingCoeffNth N := by
            rw [HN]
            exact hm2 k ((I.mem_leadingCoeffNth _ _).2
              ⟨_, hp, hn ▸ Polynomial.degree_le_natDegree, rfl⟩)
          rw [I.mem_leadingCoeffNth] at this
          rcases this with ⟨q, hq, hdq, hlqp⟩
          have hq0 : q != 0 := by
            intro H
            rw [← Polynomial.leadingCoeff_eq_zero] at H
            rw [hlqp]; rw [Polynomial.leadingCoeff_eq_zero] at H
            exact hp0 H
          have h1 : p.degree = (q * Polynomial.X ^ (k - q.natDegree)).degree := by
            rw [Polynomial.degree_mul']; rw [Polynomial.degree_X_pow]
            · rw [Polynomial.degree_eq_natDegree hp0, Polynomial.degree_eq_natDegree hq0]
              rw [← Nat.cast_add]; rw [add_tsub_cancel_of_le]; rw [hn]
              · refine le_trans (Polynomial.natDegree_le_of_degree_le hdq) (le_of_lt h)
            rw [Polynomial.leadingCoeff_X_pow]; rw [mul_one]
            exact mt Polynomial.leadingCoeff_eq_zero.1 hq0
          have h2 : p.leadingCoeff = (q * Polynomial.X ^ (k - q.natDegree)).leadingCoeff := by
            rw [← hlqp]; rw [Polynomial.leadingCoeff_mul_X_pow]
          have := Polynomial.degree_sub_lt_left h1 hp0 h2
          rw [Polynomial.degree_eq_natDegree hp0] at this
          rw [← sub_add_cancel p (q * Polynomial.X ^ (k - q.natDegree))]
          convert! (Ideal.span ↑s).add_mem _ ((Ideal.span (s : Set R[X])).mul_mem_right _ _)
          · by_cases hpq : p - q * Polynomial.X ^ (k - q.natDegree) = 0
            · rw [hpq]
              exact Ideal.zero_mem _
            refine ih _ ?_ (I.sub_mem hp (I.mul_mem_right _ hq)) rfl
            rwa [Polynomial.degree_eq_natDegree hpq, Nat.cast_lt, hn] at this
          exact hs2 ⟨Polynomial.mem_degreeLE.2 hdq, hq⟩⟩⟩

attribute [instance] Polynomial.isNoetherianRing

namespace Polynomial

/--
theorem `linearIndependent_powers_iff_aeval` / 定理 `linearIndependent_powers_iff_aeval`

English:
theorem linearIndependent_powers_iff_aeval
  given: (f : M ->ₗ[R] M) (v : M)
  proof: by
  simp [linearIndependent_iff, Finsupp.linearCombination_apply, aeval_endomorphism, Finsupp.sum,
    forall_iff_forall_finsupp, AddMonoidAlgebra.coeffEquiv.forall_congr_left, Polynomial.sum]

中文:
定理 linearIndependent_powers_iff_aeval
  条件: (f : M ->ₗ[R] M) (v : M)
  证明: by
  simp [linearIndependent_iff, Finsupp.linearCombination_apply, aeval_endomorphism, Finsupp.sum,
    forall_iff_forall_finsupp, AddMonoidAlgebra.coeffEquiv.forall_congr_left, Polynomial.sum]

Depends on / 依赖: AddMonoidAlgebra, AddMonoidAlgebra.coeffEquiv.forall_congr_left, Finsupp, Finsupp.linearCombination_apply, Finsupp.sum, Polynomial, Polynomial.sum, aeval_endomorphism, coeffEquiv, forall_congr_left, forall_iff_forall_finsupp, linearCombination_apply, linearIndependent_iff
-/
theorem linearIndependent_powers_iff_aeval (f : M ->ₗ[R] M) (v : M) :
    (LinearIndependent R fun n : Nat => (f ^ n) v) ↔ forall p : R[X], aeval f p v = 0 -> p = 0 := by
  simp [linearIndependent_iff, Finsupp.linearCombination_apply, aeval_endomorphism, Finsupp.sum,
    forall_iff_forall_finsupp, AddMonoidAlgebra.coeffEquiv.forall_congr_left, Polynomial.sum]

/--
theorem `disjoint_ker_aeval_of_isCoprime` / 定理 `disjoint_ker_aeval_of_isCoprime`

English:
theorem disjoint_ker_aeval_of_isCoprime
  given: (f : M ->ₗ[R] M) {p q : R[X]} (hpq : IsCoprime p q)
  proof: by
  rw [disjoint_iff_inf_le]
  intro v hv
  rcases hpq with ⟨p', q', hpq'⟩
  simpa [LinearMap.mem_ker.1 (Submodule.mem_inf.1 hv).1,
    LinearMap.mem_ker.1 (Submodule.mem_inf.1 hv).2] using
    congr_arg (fun p : R[X] => aeval f p v) hpq'.symm

中文:
定理 disjoint_ker_aeval_of_isCoprime
  条件: (f : M ->ₗ[R] M) {p q : R[X]} (hpq : IsCoprime p q)
  证明: by
  rw [disjoint_iff_inf_le]
  intro v hv
  rcases hpq with ⟨p', q', hpq'⟩
  simpa [LinearMap.mem_ker.1 (Submodule.mem_inf.1 hv).1,
    LinearMap.mem_ker.1 (Submodule.mem_inf.1 hv).2] using
    congr_arg (fun p : R[X] => aeval f p v) hpq'.symm

Depends on / 依赖: LinearMap, LinearMap.mem_ker, Submodule, Submodule.mem_inf, congr_arg, disjoint_iff_inf_le, mem_inf, mem_ker
-/
theorem disjoint_ker_aeval_of_isCoprime (f : M ->ₗ[R] M) {p q : R[X]} (hpq : IsCoprime p q) :
    Disjoint (LinearMap.ker (aeval f p)) (LinearMap.ker (aeval f q)) := by
  rw [disjoint_iff_inf_le]
  intro v hv
  rcases hpq with ⟨p', q', hpq'⟩
  simpa [LinearMap.mem_ker.1 (Submodule.mem_inf.1 hv).1,
    LinearMap.mem_ker.1 (Submodule.mem_inf.1 hv).2] using
    congr_arg (fun p : R[X] => aeval f p v) hpq'.symm

/--
theorem `sup_aeval_range_eq_top_of_isCoprime` / 定理 `sup_aeval_range_eq_top_of_isCoprime`

English:
theorem sup_aeval_range_eq_top_of_isCoprime
  given: (f : M ->ₗ[R] M) {p q : R[X]} (hpq : IsCoprime p q)
  proof: by
  rw [eq_top_iff]
  intro v _
  rw [Submodule.mem_sup]
  rcases hpq with ⟨p', q', hpq'⟩
  use aeval f (p * p') v
  use LinearMap.mem_range.2 ⟨aeval f p' v, by simp only [Module.End.mul_apply, aeval_mul]⟩
  use aeval f (q * q') v
  use LinearMap.mem_range.2 ⟨aeval f q' v, by simp only [Module.End.

中文:
定理 sup_aeval_range_eq_top_of_isCoprime
  条件: (f : M ->ₗ[R] M) {p q : R[X]} (hpq : IsCoprime p q)
  证明: by
  rw [eq_top_iff]
  intro v _
  rw [Submodule.mem_sup]
  rcases hpq with ⟨p', q', hpq'⟩
  use aeval f (p * p') v
  use LinearMap.mem_range.2 ⟨aeval f p' v, by simp only [Module.End.mul_apply, aeval_mul]⟩
  use aeval f (q * q') v
  use LinearMap.mem_range.2 ⟨aeval f q' v, by simp only [Module.End.

Depends on / 依赖: LinearMap, LinearMap.mem_range, Module, Module.End.mul_apply, Submodule, Submodule.mem_sup, aeval_add, aeval_mul, aeval_one, congr_arg, eq_top_iff, mem_range, mem_sup, mul_apply, mul_comm
-/
theorem sup_aeval_range_eq_top_of_isCoprime (f : M ->ₗ[R] M) {p q : R[X]} (hpq : IsCoprime p q) :
    LinearMap.range (aeval f p) ⊔ LinearMap.range (aeval f q) = ⊤ := by
  rw [eq_top_iff]
  intro v _
  rw [Submodule.mem_sup]
  rcases hpq with ⟨p', q', hpq'⟩
  use aeval f (p * p') v
  use LinearMap.mem_range.2 ⟨aeval f p' v, by simp only [Module.End.mul_apply, aeval_mul]⟩
  use aeval f (q * q') v
  use LinearMap.mem_range.2 ⟨aeval f q' v, by simp only [Module.End.mul_apply, aeval_mul]⟩
  simpa only [mul_comm p p', mul_comm q q', aeval_one, aeval_add] using!
    congr_arg (fun p : R[X] => aeval f p v) hpq'

/--
theorem `sup_ker_aeval_le_ker_aeval_mul` / 定理 `sup_ker_aeval_le_ker_aeval_mul`

English:
theorem sup_ker_aeval_le_ker_aeval_mul
  given: {f : M ->ₗ[R] M} {p q : R[X]}
  proof: by
  intro v hv
  rcases Submodule.mem_sup.1 hv with ⟨x, hx, y, hy, hxy⟩
  have h_eval_x : aeval f (p * q) x = 0 := by
    rw [mul_comm]; rw [aeval_mul]; rw [Module.End.mul_apply]; rw [LinearMap.mem_ker.1 hx]; rw [map_zero]
  have h_eval_y : aeval f (p * q) y = 0 := by
    rw [aeval_mul]; rw [Module

中文:
定理 sup_ker_aeval_le_ker_aeval_mul
  条件: {f : M ->ₗ[R] M} {p q : R[X]}
  证明: by
  intro v hv
  rcases Submodule.mem_sup.1 hv with ⟨x, hx, y, hy, hxy⟩
  have h_eval_x : aeval f (p * q) x = 0 := by
    rw [mul_comm]; rw [aeval_mul]; rw [Module.End.mul_apply]; rw [LinearMap.mem_ker.1 hx]; rw [map_zero]
  have h_eval_y : aeval f (p * q) y = 0 := by
    rw [aeval_mul]; rw [Module

Depends on / 依赖: LinearMap, LinearMap.mem_ker, Module, Module.End.mul_apply, Submodule, Submodule.mem_sup, add_zero, aeval_mul, h_eval_x, h_eval_y, map_add, map_zero, mem_ker, mem_sup, mul_apply, mul_comm
-/
theorem sup_ker_aeval_le_ker_aeval_mul {f : M ->ₗ[R] M} {p q : R[X]} :
    LinearMap.ker (aeval f p) ⊔ LinearMap.ker (aeval f q) <= LinearMap.ker (aeval f (p * q)) := by
  intro v hv
  rcases Submodule.mem_sup.1 hv with ⟨x, hx, y, hy, hxy⟩
  have h_eval_x : aeval f (p * q) x = 0 := by
    rw [mul_comm]; rw [aeval_mul]; rw [Module.End.mul_apply]; rw [LinearMap.mem_ker.1 hx]; rw [map_zero]
  have h_eval_y : aeval f (p * q) y = 0 := by
    rw [aeval_mul]; rw [Module.End.mul_apply]; rw [LinearMap.mem_ker.1 hy]; rw [map_zero]
  rw [LinearMap.mem_ker]; rw [← hxy]; rw [map_add]; rw [h_eval_x]; rw [h_eval_y]; rw [add_zero]

/--
theorem `sup_ker_aeval_eq_ker_aeval_mul_of_coprime` / 定理 `sup_ker_aeval_eq_ker_aeval_mul_of_coprime`

English:
theorem sup_ker_aeval_eq_ker_aeval_mul_of_coprime
  statement: (f : M ->ₗ[R] M) {p q : R[X]}
  proof: by
  apply le_antisymm sup_ker_aeval_le_ker_aeval_mul
  intro v hv
  rw [Submodule.mem_sup]
  rcases hpq with ⟨p', q', hpq'⟩
  have h_eval₂_qpp' :=
    calc
      aeval f (q * (p * p')) v = aeval f (p' * (p * q)) v := by
        rw [mul_comm]; rw [mul_assoc]; rw [mul_comm]; rw [mul_assoc]; rw [mul_c

中文:
定理 sup_ker_aeval_eq_ker_aeval_mul_of_coprime
  结论: (f : M ->ₗ[R] M) {p q : R[X]}
  证明: by
  apply le_antisymm sup_ker_aeval_le_ker_aeval_mul
  intro v hv
  rw [Submodule.mem_sup]
  rcases hpq with ⟨p', q', hpq'⟩
  have h_eval₂_qpp' :=
    calc
      aeval f (q * (p * p')) v = aeval f (p' * (p * q)) v := by
        rw [mul_comm]; rw [mul_assoc]; rw [mul_comm]; rw [mul_assoc]; rw [mul_c

Depends on / 依赖: LinearMap, LinearMap.mem_ker, Module, Module.End.mul_apply, Submodule, Submodule.mem_sup, aeval_mul, le_antisymm, map_zero, mem_ker, mem_sup, mul_apply, mul_assoc, mul_comm, sup_ker_aeval_le_ker_aeval_mul
-/
theorem sup_ker_aeval_eq_ker_aeval_mul_of_coprime (f : M ->ₗ[R] M) {p q : R[X]}
    (hpq : IsCoprime p q) :
    LinearMap.ker (aeval f p) ⊔ LinearMap.ker (aeval f q) = LinearMap.ker (aeval f (p * q)) := by
  apply le_antisymm sup_ker_aeval_le_ker_aeval_mul
  intro v hv
  rw [Submodule.mem_sup]
  rcases hpq with ⟨p', q', hpq'⟩
  have h_eval₂_qpp' :=
    calc
      aeval f (q * (p * p')) v = aeval f (p' * (p * q)) v := by
        rw [mul_comm]; rw [mul_assoc]; rw [mul_comm]; rw [mul_assoc]; rw [mul_comm q p]
      _ = 0 := by rw [aeval_mul, Module.End.mul_apply, LinearMap.mem_ker.1 hv, map_zero]
  have h_eval₂_pqq' :=
    calc
      aeval f (p * (q * q')) v = aeval f (q' * (p * q)) v := by rw [← mul_assoc, mul_comm]
      _ = 0 := by rw [aeval_mul, Module.End.mul_apply, LinearMap.mem_ker.1 hv, map_zero]
  rw [aeval_mul] at h_eval₂_qpp' h_eval₂_pqq'
  refine
    ⟨aeval f (q * q') v, LinearMap.mem_ker.1 h_eval₂_pqq', aeval f (p * p') v,
      LinearMap.mem_ker.1 h_eval₂_qpp', ?_⟩
  rw [add_comm]; rw [mul_comm p p']; rw [mul_comm q q']
  simpa only [map_add, map_mul, aeval_one] using! congr_arg (fun p : R[X] => aeval f p v) hpq'

end Polynomial

namespace MvPolynomial

/--
lemma `aeval_natDegree_le` / 引理 `aeval_natDegree_le`

English:
lemma aeval_natDegree_le
  statement: {R : Type*} [CommSemiring R] {m n : Nat}
  proof: by
  rw [MvPolynomial.aeval_def]; rw [MvPolynomial.eval₂]
  apply (Polynomial.natDegree_sum_le _ _).trans
  apply Finset.sup_le
  intro d hd
  simp_rw [Function.comp_apply, ← Polynomial.C_eq_algebraMap]
  apply (Polynomial.natDegree_C_mul_le _ _).trans
  apply (Polynomial.natDegree_prod_le _ _).tran

中文:
引理 aeval_natDegree_le
  结论: {R : 类型} [交换半环 R] {m n : 自然数}
  证明: by
  rw [MvPolynomial.aeval_def]; rw [MvPolynomial.eval₂]
  apply (Polynomial.natDegree_sum_le _ _).trans
  apply Finset.sup_le
  intro d hd
  simp_rw [Function.comp_apply, ← Polynomial.C_eq_algebraMap]
  apply (Polynomial.natDegree_C_mul_le _ _).trans
  apply (Polynomial.natDegree_prod_le _ _).tran

Depends on / 依赖: C_eq_algebraMap, Finset, Finset.le_sup_of_le, Finset.sum_le_sum, Finset.sum_mul, Finset.sup_le, Function, Function.comp_apply, MvPolynomial, MvPolynomial.aeval_def, MvPolynomial.eval, MvPolynomial.totalDegree, Polynomial, Polynomial.C_eq_algebraMap, Polynomial.natDegree_C_mul_le, Polynomial.natDegree_prod_le, Polynomial.natDegree_sum_le, aeval_def, comp_apply, d.support
-/
lemma aeval_natDegree_le {R : Type*} [CommSemiring R] {m n : Nat}
    (F : MvPolynomial σ R) (hF : F.totalDegree <= m)
    (f : σ -> Polynomial R) (hf : forall i, (f i).natDegree <= n) :
    (MvPolynomial.aeval f F).natDegree <= m * n := by
  rw [MvPolynomial.aeval_def]; rw [MvPolynomial.eval₂]
  apply (Polynomial.natDegree_sum_le _ _).trans
  apply Finset.sup_le
  intro d hd
  simp_rw [Function.comp_apply, ← Polynomial.C_eq_algebraMap]
  apply (Polynomial.natDegree_C_mul_le _ _).trans
  apply (Polynomial.natDegree_prod_le _ _).trans
  have : ∑ i in d.support, (d i) * n <= m * n := by
    rw [← Finset.sum_mul]
    apply mul_le_mul' (.trans _ hF) le_rfl
    rw [MvPolynomial.totalDegree]
    exact Finset.le_sup_of_le hd le_rfl
  apply (Finset.sum_le_sum _).trans this
  rintro i -
  apply Polynomial.natDegree_pow_le.trans
  exact mul_le_mul' le_rfl (hf i)

/--
theorem `isNoetherianRing_fin_0` / 定理 `isNoetherianRing_fin_0`

English:
theorem isNoetherianRing_fin_0
  given: [IsNoetherianRing R]
  proof: by
  apply isNoetherianRing_of_ringEquiv R
  symm; apply MvPolynomial.isEmptyRingEquiv R (Fin 0)

中文:
定理 isNoetherianRing_fin_0
  条件: [是Noether环 R]
  证明: by
  apply isNoetherianRing_of_ringEquiv R
  symm; apply MvPolynomial.isEmptyRingEquiv R (Fin 0)

Depends on / 依赖: MvPolynomial, MvPolynomial.isEmptyRingEquiv, isEmptyRingEquiv, isNoetherianRing_of_ringEquiv
-/
theorem isNoetherianRing_fin_0 [IsNoetherianRing R] :
    IsNoetherianRing (MvPolynomial (Fin 0) R) := by
  apply isNoetherianRing_of_ringEquiv R
  symm; apply MvPolynomial.isEmptyRingEquiv R (Fin 0)

/--
theorem `isNoetherianRing_fin` / 定理 `isNoetherianRing_fin`

English:
theorem isNoetherianRing_fin
  given: [IsNoetherianRing R]

中文:
定理 isNoetherianRing_fin
  条件: [是Noether环 R]
-/
theorem isNoetherianRing_fin [IsNoetherianRing R] :
    forall {n : Nat}, IsNoetherianRing (MvPolynomial (Fin n) R)
  | 0 => isNoetherianRing_fin_0
  | n + 1 =>
    @isNoetherianRing_of_ringEquiv (Polynomial (MvPolynomial (Fin n) R)) _ _ _
      (MvPolynomial.finSuccEquiv _ n).toRingEquiv.symm
      (@Polynomial.isNoetherianRing (MvPolynomial (Fin n) R) _ isNoetherianRing_fin)

/--
Instance `isNoetherianRing` / 实例 `isNoetherianRing`

English:
instance isNoetherianRing
  signature: [Finite σ] [IsNoetherianRing R]
  body: by
  cases nonempty_fintype σ
  exact
    @isNoetherianRing_of_ringEquiv (MvPolynomial (Fin (Fintype.card σ)) R) _ _ _
      (renameEquiv R (Fintype.equivFin σ).symm).toRingEquiv isNoetherianRing_fin

中文:
实例 isNoetherianRing
  签名: [有限 σ] [是Noether环 R]
  定义体: by
  cases nonempty_fintype σ
  exact
    @isNoetherianRing_of_ringEquiv (MvPolynomial (Fin (Fintype.card σ)) R) _ _ _
      (renameEquiv R (Fintype.equivFin σ).symm).toRingEquiv isNoetherianRing_fin

Depends on / 依赖: Fintype, Fintype.card, Fintype.equivFin, MvPolynomial, equivFin, isNoetherianRing_fin, isNoetherianRing_of_ringEquiv, nonempty_fintype, renameEquiv, toRingEquiv
-/
instance isNoetherianRing [Finite σ] [IsNoetherianRing R] :
    IsNoetherianRing (MvPolynomial σ R) := by
  cases nonempty_fintype σ
  exact
    @isNoetherianRing_of_ringEquiv (MvPolynomial (Fin (Fintype.card σ)) R) _ _ _
      (renameEquiv R (Fintype.equivFin σ).symm).toRingEquiv isNoetherianRing_fin

/--
theorem `map_mvPolynomial_eq_eval₂` / 定理 `map_mvPolynomial_eq_eval₂`

English:
theorem map_mvPolynomial_eq_eval₂
  statement: {S : Type*} [CommSemiring S] [Finite σ]
  proof: by
  cases nonempty_fintype σ
  refine Trans.trans (congr_arg ϕ (MvPolynomial.as_sum p)) ?_
  rw [MvPolynomial.eval₂_eq']; rw [map_sum ϕ]
  congr
  ext
  simp only [monomial_eq, ϕ.map_pow, map_prod ϕ, ϕ.comp_apply, ϕ.map_mul, Finsupp.prod_pow]

中文:
定理 map_mvPolynomial_eq_eval₂
  结论: {S : 类型} [交换半环 S] [有限 σ]
  证明: by
  cases nonempty_fintype σ
  refine Trans.trans (congr_arg ϕ (MvPolynomial.as_sum p)) ?_
  rw [MvPolynomial.eval₂_eq']; rw [map_sum ϕ]
  congr
  ext
  simp only [monomial_eq, ϕ.map_pow, map_prod ϕ, ϕ.comp_apply, ϕ.map_mul, Finsupp.prod_pow]

Depends on / 依赖: Finsupp, Finsupp.prod_pow, MvPolynomial, MvPolynomial.as_sum, MvPolynomial.eval, Trans.trans, as_sum, comp_apply, congr_arg, map_mul, map_pow, map_prod, map_sum, monomial_eq, nonempty_fintype, prod_pow
-/
theorem map_mvPolynomial_eq_eval₂ {S : Type*} [CommSemiring S] [Finite σ]
    (ϕ : MvPolynomial σ R ->+* S) (p : MvPolynomial σ R) :
    ϕ p = MvPolynomial.eval₂ (ϕ.comp MvPolynomial.C) (fun s => ϕ (MvPolynomial.X s)) p := by
  cases nonempty_fintype σ
  refine Trans.trans (congr_arg ϕ (MvPolynomial.as_sum p)) ?_
  rw [MvPolynomial.eval₂_eq']; rw [map_sum ϕ]
  congr
  ext
  simp only [monomial_eq, ϕ.map_pow, map_prod ϕ, ϕ.comp_apply, ϕ.map_mul, Finsupp.prod_pow]

/--
theorem `mem_ideal_of_coeff_mem_ideal` / 定理 `mem_ideal_of_coeff_mem_ideal`

English:
theorem mem_ideal_of_coeff_mem_ideal
  statement: (I : Ideal (MvPolynomial σ R)) (p : MvPolynomial σ R)
  proof: by
  rw [as_sum p]
  suffices forall m in p.support, monomial m (MvPolynomial.coeff m p) in I by
    exact Submodule.sum_mem I this
  intro m _
  rw [← mul_one (coeff m p)]; rw [← C_mul_monomial]
  suffices C (coeff m p) in I by exact I.mul_mem_right (monomial m 1) this
  simpa [Ideal.mem_comap] usi

中文:
定理 mem_ideal_of_coeff_mem_ideal
  结论: (I : 理想 (多元多项式 σ R)) (p : 多元多项式 σ R)
  证明: by
  rw [as_sum p]
  suffices forall m in p.support, monomial m (MvPolynomial.coeff m p) in I by
    exact Submodule.sum_mem I this
  intro m _
  rw [← mul_one (coeff m p)]; rw [← C_mul_monomial]
  suffices C (coeff m p) in I by exact I.mul_mem_right (monomial m 1) this
  simpa [Ideal.mem_comap] usi

Depends on / 依赖: C_mul_monomial, I.mul_mem_right, Ideal.mem_comap, MvPolynomial, MvPolynomial.coeff, Submodule, Submodule.sum_mem, as_sum, mem_comap, monomial, mul_mem_right, mul_one, p.support, sum_mem, support
-/
theorem mem_ideal_of_coeff_mem_ideal (I : Ideal (MvPolynomial σ R)) (p : MvPolynomial σ R)
    (hcoe : forall m : σ ->₀ Nat, p.coeff m in I.comap (C : R ->+* MvPolynomial σ R)) : p in I := by
  rw [as_sum p]
  suffices forall m in p.support, monomial m (MvPolynomial.coeff m p) in I by
    exact Submodule.sum_mem I this
  intro m _
  rw [← mul_one (coeff m p)]; rw [← C_mul_monomial]
  suffices C (coeff m p) in I by exact I.mul_mem_right (monomial m 1) this
  simpa [Ideal.mem_comap] using hcoe m

/--
theorem `mem_map_C_iff` / 定理 `mem_map_C_iff`

English:
theorem mem_map_C_iff
  given: {I : Ideal R} {f : MvPolynomial σ R}
  proof: by
  classical
  constructor
  · intro hf
    refine Submodule.span_induction ?_ ?_ ?_ ?_ hf
    · intro f hf n
      obtain ⟨x, hx⟩ := (Set.mem_image _ _ _).mp hf
      rw [← hx.right]; rw [coeff_C]
      by_cases h : n = 0
      · simpa [h] using hx.left
      · simp [Ne.symm h]
    · simp
    · e

中文:
定理 mem_map_C_iff
  条件: {I : 理想 R} {f : 多元多项式 σ R}
  证明: by
  classical
  constructor
  · intro hf
    refine Submodule.span_induction ?_ ?_ ?_ ?_ hf
    · intro f hf n
      obtain ⟨x, hx⟩ := (Set.mem_image _ _ _).mp hf
      rw [← hx.right]; rw [coeff_C]
      by_cases h : n = 0
      · simpa [h] using hx.left
      · simp [Ne.symm h]
    · simp
    · e

Depends on / 依赖: I.add_mem, I.mul_mem_left, I.sum_mem, Ne.symm, Set.mem_image, Submodule, Submodule.span_induction, add_mem, as_sum, c.fst, c.snd, classical, coeff_C, coeff_mul, f.coeff, f.support, hx.left, hx.right, mem_image, monomial
-/
theorem mem_map_C_iff {I : Ideal R} {f : MvPolynomial σ R} :
    f in (Ideal.map (C : R ->+* MvPolynomial σ R) I : Ideal (MvPolynomial σ R)) ↔
      forall m : σ ->₀ Nat, f.coeff m in I := by
  classical
  constructor
  · intro hf
    refine Submodule.span_induction ?_ ?_ ?_ ?_ hf
    · intro f hf n
      obtain ⟨x, hx⟩ := (Set.mem_image _ _ _).mp hf
      rw [← hx.right]; rw [coeff_C]
      by_cases h : n = 0
      · simpa [h] using hx.left
      · simp [Ne.symm h]
    · simp
    · exact fun f g _ _ hf hg n => by simp [I.add_mem (hf n) (hg n)]
    · intro f g _ hg n
      rw [smul_eq_mul]; rw [coeff_mul]
      exact I.sum_mem fun c _ => I.mul_mem_left (f.coeff c.fst) (hg c.snd)
  · intro hf
    rw [as_sum f]
    suffices forall m in f.support, monomial m (coeff m f) in (Ideal.map C I : Ideal (MvPolynomial σ R)) by
      exact Submodule.sum_mem _ this
    intro m _
    rw [← mul_one (coeff m f)]; rw [← C_mul_monomial]
    suffices C (coeff m f) in (Ideal.map C I : Ideal (MvPolynomial σ R)) by
      exact Ideal.mul_mem_right _ _ this
    apply Ideal.mem_map_of_mem _
    exact hf m

/--
theorem `ker_map` / 定理 `ker_map`

English:
theorem ker_map
  given: (f : R ->+* S)
  proof: by
  ext
  rw [MvPolynomial.mem_map_C_iff]; rw [RingHom.mem_ker]; rw [MvPolynomial.ext_iff]
  simp_rw [coeff_map, coeff_zero, RingHom.mem_ker]

中文:
定理 ker_map
  条件: (f : R ->+* S)
  证明: by
  ext
  rw [MvPolynomial.mem_map_C_iff]; rw [RingHom.mem_ker]; rw [MvPolynomial.ext_iff]
  simp_rw [coeff_map, coeff_zero, RingHom.mem_ker]

Depends on / 依赖: MvPolynomial, MvPolynomial.ext_iff, MvPolynomial.mem_map_C_iff, RingHom, RingHom.mem_ker, coeff_map, coeff_zero, ext_iff, mem_ker, mem_map_C_iff, simp_rw
-/
theorem ker_map (f : R ->+* S) :
    RingHom.ker (map f : MvPolynomial σ R ->+* MvPolynomial σ S) =
    Ideal.map (C : R ->+* MvPolynomial σ R) (RingHom.ker f) := by
  ext
  rw [MvPolynomial.mem_map_C_iff]; rw [RingHom.mem_ker]; rw [MvPolynomial.ext_iff]
  simp_rw [coeff_map, coeff_zero, RingHom.mem_ker]

/--
lemma `ker_mapAlgHom` / 引理 `ker_mapAlgHom`

English:
lemma ker_mapAlgHom
  statement: {S₁ S₂ σ : Type*} [CommRing S₁] [CommRing S₂] [Algebra R S₁]
  proof: MvPolynomial.ker_map (f.toRingHom : S₁ ->+* S₂)

中文:
引理 ker_mapAlgHom
  结论: {S₁ S₂ σ : 类型} [交换环 S₁] [交换环 S₂] [代数 R S₁]
  证明: MvPolynomial.ker_map (f.toRingHom : S₁ ->+* S₂)

Depends on / 依赖: Ideal.map, MvPolynomial, MvPolynomial.C, RingHom, RingHom.ker
-/
lemma ker_mapAlgHom {S₁ S₂ σ : Type*} [CommRing S₁] [CommRing S₂] [Algebra R S₁]
    [Algebra R S₂] (f : S₁ ->ₐ[R] S₂) :
    RingHom.ker (MvPolynomial.mapAlgHom (σ := σ) f) = Ideal.map MvPolynomial.C (RingHom.ker f) :=
  MvPolynomial.ker_map (f.toRingHom : S₁ ->+* S₂)

end MvPolynomial
