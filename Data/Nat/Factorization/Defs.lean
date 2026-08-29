/-
Copyright (c) 2021 Stuart Presnell. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Stuart Presnell
-/
module

public import Batteries.Data.List.Count
public import Mathlib.Data.Finsupp.Multiset
public import Mathlib.Data.Finsupp.Order
public import Mathlib.Data.Nat.PrimeFin
public import Mathlib.NumberTheory.Padics.PadicVal.Defs

/-!
# Prime factorizations

`n.factorization` is the finitely supported function `ℕ →₀ ℕ`
mapping each prime factor of `n` to its multiplicity in `n`. For example, since 2000 = 2^4 * 5^3,
* `factorization 2000 2` is 4
* `factorization 2000 5` is 3
* `factorization 2000 k` is 0 for all other `k : ℕ`.

## TODO

* As discussed in this Zulip thread:
  https://leanprover.zulipchat.com/#narrow/stream/217875/topic/Multiplicity.20in.20the.20naturals
  We have lots of disparate ways of talking about the multiplicity of a prime
  in a natural number, including `factors.count`, `padicValNat`, `multiplicity`,
  and the material in `Data/PNat/Factors`. Move some of this material to this file,
  prove results about the relationships between these definitions,
  and (where appropriate) choose a uniform canonical way of expressing these ideas.

* Moreover, the results here should be generalised to an arbitrary unique factorization monoid
  with a normalization function, and then deduplicated. The basics of this have been started in
  `Mathlib/RingTheory/UniqueFactorizationDomain/`.

* Extend the inductions to any `NormalizationMonoid` with unique factorization.

-/

@[expose] public section

open Nat Finset List Finsupp

namespace Nat
variable {a b m n p : Nat}

/--
Definition of `factorization` / `factorization` 的定义

English:
definition factorization
  signature: (n : Nat)
  body: n.primeFactors
  toFun p := if p.Prime then padicValNat p n else 0
  mem_support_toFun := by simp [not_or]; aesop

中文:
定义 factorization
  签名: (n : 自然数)
  定义体: n.primeFactors
  toFun p := if p.Prime then padicValNat p n else 0
  mem_support_toFun := by simp [not_or]; aesop

Depends on / 依赖: n.primeFactors, primeFactors
-/
def factorization (n : Nat) : Nat ->₀ Nat where
  support := n.primeFactors
  toFun p := if p.Prime then padicValNat p n else 0
  mem_support_toFun := by simp [not_or]; aesop

/--
lemma `support_factorization` / 引理 `support_factorization`

English:
lemma support_factorization
  given: (n : Nat)
  statement: (factorization n).support = n.primeFactors
  proof: rfl

中文:
引理 support_factorization
  条件: (n : 自然数)
  结论: (factorization n).support = n.primeFactors
  证明: rfl
-/
@[simp] lemma support_factorization (n : Nat) : (factorization n).support = n.primeFactors := rfl

/--
theorem `factorization_def` / 定理 `factorization_def`

English:
theorem factorization_def
  given: (n : Nat) {p : Nat} (pp : p.Prime)
  statement: n.factorization p = padicValNat p n
  proof: by
  simpa [factorization] using absurd pp

中文:
定理 factorization_def
  条件: (n : 自然数) {p : 自然数} (pp : p.Prime)
  结论: n.factorization p = padicVal自然数 p n
  证明: by
  simpa [factorization] using absurd pp

Depends on / 依赖: absurd, factorization
-/
theorem factorization_def (n : Nat) {p : Nat} (pp : p.Prime) : n.factorization p = padicValNat p n := by
  simpa [factorization] using absurd pp

/-- We can write both `n.factorization p` and `n.factors.count p` to represent the power
of `p` in the factorization of `n`: we declare the former to be the simp-normal form. -/
@[simp]
/--
theorem `primeFactorsList_count_eq` / 定理 `primeFactorsList_count_eq`

English:
theorem primeFactorsList_count_eq
  given: {n p : Nat}
  statement: n.primeFactorsList.count p = n.factorization p
  proof: by
  rcases n.eq_zero_or_pos with (rfl | hn0)
  · simp [factorization, count]
  if pp : p.Prime then ?_ else
    rw [count_eq_zero_of_not_mem (mt prime_of_mem_primeFactorsList pp)]
    simp [factorization, pp]
  simp only [factorization_def _ pp]
  apply _root_.le_antisymm
  · rw [le_padicValNat_iff

中文:
定理 primeFactorsList_count_eq
  条件: {n p : 自然数}
  结论: n.primeFactorsList.count p = n.factorization p
  证明: by
  rcases n.eq_zero_or_pos with (rfl | hn0)
  · simp [factorization, count]
  if pp : p.Prime then ?_ else
    rw [count_eq_zero_of_not_mem (mt prime_of_mem_primeFactorsList pp)]
    simp [factorization, pp]
  simp only [factorization_def _ pp]
  apply _root_.le_antisymm
  · rw [le_padicValNat_iff

Depends on / 依赖: List.replicate_sublist_iff.mpr, Nat.lt_add_one_iff, _root_, _root_.le_antisymm, count_eq_zero_of_not_mem, eq_zero_or_pos, factorization, factorization_def, hn0.ne, le_antisymm, le_padicValNat_iff_replicate_subperm_primeFactorsList, le_rfl, lt_add_one_iff, lt_iff_not_ge, n.eq_zero_or_pos, p.Prime, prime_of_mem_primeFactorsList, replicate_sublist_iff, subperm
-/
theorem primeFactorsList_count_eq {n p : Nat} : n.primeFactorsList.count p = n.factorization p := by
  rcases n.eq_zero_or_pos with (rfl | hn0)
  · simp [factorization, count]
  if pp : p.Prime then ?_ else
    rw [count_eq_zero_of_not_mem (mt prime_of_mem_primeFactorsList pp)]
    simp [factorization, pp]
  simp only [factorization_def _ pp]
  apply _root_.le_antisymm
  · rw [le_padicValNat_iff_replicate_subperm_primeFactorsList pp hn0.ne']
.subperm exact List.replicate_sublist_iff.mpr le_rfl
  · rw [← Nat.lt_add_one_iff, lt_iff_not_ge,
      le_padicValNat_iff_replicate_subperm_primeFactorsList pp hn0.ne']
    intro h
    have := h.count_le p
    simp at this

/--
theorem `factorization_eq_primeFactorsList_multiset` / 定理 `factorization_eq_primeFactorsList_multiset`

English:
theorem factorization_eq_primeFactorsList_multiset
  given: (n : Nat)
  proof: by
  ext p
  simp

中文:
定理 factorization_eq_primeFactorsList_multiset
  条件: (n : 自然数)
  证明: by
  ext p
  simp
-/
theorem factorization_eq_primeFactorsList_multiset (n : Nat) :
    n.factorization = Multiset.toFinsupp (n.primeFactorsList : Multiset Nat) := by
  ext p
  simp

/--
theorem `Prime.factorization_pos_of_dvd` / 定理 `Prime.factorization_pos_of_dvd`

English:
theorem Prime.factorization_pos_of_dvd
  given: {n p : Nat} (hp : p.Prime) (hn : n != 0) (h : p ∣ n)
  proof: by
  rwa [← primeFactorsList_count_eq, count_pos_iff, mem_primeFactorsList_iff_dvd hn hp]

中文:
定理 Prime.factorization_pos_of_dvd
  条件: {n p : 自然数} (hp : p.Prime) (hn : n != 0) (h : p ∣ n)
  证明: by
  rwa [← primeFactorsList_count_eq, count_pos_iff, mem_primeFactorsList_iff_dvd hn hp]

Depends on / 依赖: count_pos_iff, mem_primeFactorsList_iff_dvd, primeFactorsList_count_eq
-/
theorem Prime.factorization_pos_of_dvd {n p : Nat} (hp : p.Prime) (hn : n != 0) (h : p ∣ n) :
    0 < n.factorization p := by
  rwa [← primeFactorsList_count_eq, count_pos_iff, mem_primeFactorsList_iff_dvd hn hp]

/--
theorem `multiplicity_eq_factorization` / 定理 `multiplicity_eq_factorization`

English:
theorem multiplicity_eq_factorization
  given: {n p : Nat} (pp : p.Prime) (hn : n != 0)
  proof: by
  simp [factorization, pp, padicValNat_def' pp.ne_one hn]

中文:
定理 multiplicity_eq_factorization
  条件: {n p : 自然数} (pp : p.Prime) (hn : n != 0)
  证明: by
  simp [factorization, pp, padicValNat_def' pp.ne_one hn]

Depends on / 依赖: factorization, ne_one, padicValNat_def, pp.ne_one
-/
theorem multiplicity_eq_factorization {n p : Nat} (pp : p.Prime) (hn : n != 0) :
    multiplicity p n = n.factorization p := by
  simp [factorization, pp, padicValNat_def' pp.ne_one hn]

/-! ### Basic facts about factorization -/


@[simp]
/--
theorem `prod_factorization_pow_eq_self` / 定理 `prod_factorization_pow_eq_self`

English:
theorem prod_factorization_pow_eq_self
  given: {n : Nat} (hn : n != 0)
  statement: n.factorization.prod (· ^ ·) = n
  proof: by
  rw [factorization_eq_primeFactorsList_multiset n]
  simp only [← prod_toMultiset, Multiset.prod_coe, Multiset.toFinsupp_toMultiset]
  exact prod_primeFactorsList hn

@[deprecated (since := "2026-03-19")]
alias factorization_prod_pow_eq_self := prod_factorization_pow_eq_self

中文:
定理 prod_factorization_pow_eq_self
  条件: {n : 自然数} (hn : n != 0)
  结论: n.factorization.prod (· ^ ·) = n
  证明: by
  rw [factorization_eq_primeFactorsList_multiset n]
  simp only [← prod_toMultiset, Multiset.prod_coe, Multiset.toFinsupp_toMultiset]
  exact prod_primeFactorsList hn

@[deprecated (since := "2026-03-19")]
alias factorization_prod_pow_eq_self := prod_factorization_pow_eq_self

Depends on / 依赖: Multiset, Multiset.prod_coe, Multiset.toFinsupp_toMultiset, factorization_eq_primeFactorsList_multiset, prod_coe, prod_primeFactorsList, prod_toMultiset, toFinsupp_toMultiset
-/
theorem prod_factorization_pow_eq_self {n : Nat} (hn : n != 0) : n.factorization.prod (· ^ ·) = n := by
  rw [factorization_eq_primeFactorsList_multiset n]
  simp only [← prod_toMultiset, Multiset.prod_coe, Multiset.toFinsupp_toMultiset]
  exact prod_primeFactorsList hn

@[deprecated (since := "2026-03-19")]
alias factorization_prod_pow_eq_self := prod_factorization_pow_eq_self

/--
theorem `eq_of_factorization_eq` / 定理 `eq_of_factorization_eq`

English:
theorem eq_of_factorization_eq
  statement: {a b : Nat} (ha : a != 0) (hb : b != 0)
  proof: eq_of_perm_primeFactorsList ha hb
    (by simpa only [List.perm_iff_count, primeFactorsList_count_eq] using h)

中文:
定理 eq_of_factorization_eq
  结论: {a b : 自然数} (ha : a != 0) (hb : b != 0)
  证明: eq_of_perm_primeFactorsList ha hb
    (by simpa only [List.perm_iff_count, primeFactorsList_count_eq] using h)

Depends on / 依赖: List.perm_iff_count, eq_of_perm_primeFactorsList, perm_iff_count, primeFactorsList_count_eq
-/
theorem eq_of_factorization_eq {a b : Nat} (ha : a != 0) (hb : b != 0)
    (h : forall p : Nat, a.factorization p = b.factorization p) : a = b :=
  eq_of_perm_primeFactorsList ha hb
    (by simpa only [List.perm_iff_count, primeFactorsList_count_eq] using h)

/--
theorem `eq_of_factorization_eq'` / 定理 `eq_of_factorization_eq'`

English:
theorem eq_of_factorization_eq'
  statement: {a b : Nat} (ha : a != 0) (hb : b != 0)
  proof: eq_of_factorization_eq ha hb (congrFun (congrArg DFunLike.coe h))

中文:
定理 eq_of_factorization_eq'
  结论: {a b : 自然数} (ha : a != 0) (hb : b != 0)
  证明: eq_of_factorization_eq ha hb (congrFun (congrArg DFunLike.coe h))

Depends on / 依赖: DFunLike, DFunLike.coe, eq_of_factorization_eq
-/
theorem eq_of_factorization_eq' {a b : Nat} (ha : a != 0) (hb : b != 0)
    (h : a.factorization = b.factorization) : a = b :=
  eq_of_factorization_eq ha hb (congrFun (congrArg DFunLike.coe h))


/--
theorem `factorization_inj` / 定理 `factorization_inj`

English:
theorem factorization_inj
  statement: Set.InjOn factorization { x : Nat | x != 0 }
  proof: fun a ha b hb h =>
  eq_of_factorization_eq ha hb fun p => by simp [h]

@[simp]

中文:
定理 factorization_inj
  结论: Set.InjOn factorization { x : 自然数 | x != 0 }
  证明: fun a ha b hb h =>
  eq_of_factorization_eq ha hb fun p => by simp [h]

@[simp]
-/
theorem factorization_inj : Set.InjOn factorization { x : Nat | x != 0 } := fun a ha b hb h =>
  eq_of_factorization_eq ha hb fun p => by simp [h]

@[simp]
/--
theorem `factorization_zero` / 定理 `factorization_zero`

English:
theorem factorization_zero
  statement: factorization 0 = 0
  proof: by ext; simp [factorization]

@[simp]

中文:
定理 factorization_zero
  结论: factorization 0 = 0
  证明: by ext; simp [factorization]

@[simp]

Depends on / 依赖: Algebra, Algebra.IsAlgebraic.tower_top, IsAlgebraic, adjoin, adjoin.finiteDimensional, factorization, finiteDimensional, isAlgebraic, isIntegral, tower_top
-/
theorem factorization_zero : factorization 0 = 0 := by ext; simp [factorization]

@[simp]
/--
theorem `factorization_one` / 定理 `factorization_one`

English:
theorem factorization_one
  statement: factorization 1 = 0
  proof: by ext; simp [factorization]

中文:
定理 factorization_one
  结论: factorization 1 = 0
  证明: by ext; simp [factorization]

Depends on / 依赖: factorization
-/
theorem factorization_one : factorization 1 = 0 := by ext; simp [factorization]


/--
theorem `factorization_eq_zero_iff` / 定理 `factorization_eq_zero_iff`

English:
theorem factorization_eq_zero_iff
  given: (n p : Nat)
  proof: by
  simp_rw [← notMem_support_iff, support_factorization, mem_primeFactors, not_and_or, not_ne_iff]

@[simp]

中文:
定理 factorization_eq_zero_iff
  条件: (n p : 自然数)
  证明: by
  simp_rw [← notMem_support_iff, support_factorization, mem_primeFactors, not_and_or, not_ne_iff]

@[simp]

Depends on / 依赖: mem_primeFactors, notMem_support_iff, not_and_or, not_ne_iff, simp_rw, support_factorization
-/
theorem factorization_eq_zero_iff (n p : Nat) :
    n.factorization p = 0 ↔ ¬p.Prime ∨ ¬p ∣ n ∨ n = 0 := by
  simp_rw [← notMem_support_iff, support_factorization, mem_primeFactors, not_and_or, not_ne_iff]

@[simp]
/--
theorem `factorization_eq_zero_of_not_prime` / 定理 `factorization_eq_zero_of_not_prime`

English:
theorem factorization_eq_zero_of_not_prime
  given: (n : Nat) {p : Nat} (hp : ¬p.Prime)
  proof: by simp [factorization_eq_zero_iff, hp]

@[simp]

中文:
定理 factorization_eq_zero_of_not_prime
  条件: (n : 自然数) {p : 自然数} (hp : ¬p.Prime)
  证明: by simp [factorization_eq_zero_iff, hp]

@[simp]

Depends on / 依赖: Algebra, Algebra.isSeparable_tower_bot_of_isSeparable, factorization_eq_zero_iff, isSeparable_tower_bot_of_isSeparable
-/
theorem factorization_eq_zero_of_not_prime (n : Nat) {p : Nat} (hp : ¬p.Prime) :
    n.factorization p = 0 := by simp [factorization_eq_zero_iff, hp]

@[simp]
/--
theorem `factorization_zero_right` / 定理 `factorization_zero_right`

English:
theorem factorization_zero_right
  given: (n : Nat)
  statement: n.factorization 0 = 0
  proof: factorization_eq_zero_of_not_prime _ not_prime_zero

@[simp]

中文:
定理 factorization_zero_right
  条件: (n : 自然数)
  结论: n.factorization 0 = 0
  证明: factorization_eq_zero_of_not_prime _ not_prime_zero

@[simp]

Depends on / 依赖: factorization_eq_zero_of_not_prime, not_prime_zero
-/
theorem factorization_zero_right (n : Nat) : n.factorization 0 = 0 :=
  factorization_eq_zero_of_not_prime _ not_prime_zero

@[simp]
/--
theorem `factorization_one_right` / 定理 `factorization_one_right`

English:
theorem factorization_one_right
  given: (n : Nat)
  statement: n.factorization 1 = 0
  proof: factorization_eq_zero_of_not_prime _ not_prime_one

中文:
定理 factorization_one_right
  条件: (n : 自然数)
  结论: n.factorization 1 = 0
  证明: factorization_eq_zero_of_not_prime _ not_prime_one

Depends on / 依赖: factorization_eq_zero_of_not_prime, not_prime_one
-/
theorem factorization_one_right (n : Nat) : n.factorization 1 = 0 :=
  factorization_eq_zero_of_not_prime _ not_prime_one

/--
theorem `factorization_eq_zero_of_not_dvd` / 定理 `factorization_eq_zero_of_not_dvd`

English:
theorem factorization_eq_zero_of_not_dvd
  given: {n p : Nat} (h : ¬p ∣ n)
  statement: n.factorization p = 0
  proof: by
  simp [factorization_eq_zero_iff, h]

中文:
定理 factorization_eq_zero_of_not_dvd
  条件: {n p : 自然数} (h : ¬p ∣ n)
  结论: n.factorization p = 0
  证明: by
  simp [factorization_eq_zero_iff, h]

Depends on / 依赖: factorization_eq_zero_iff
-/
theorem factorization_eq_zero_of_not_dvd {n p : Nat} (h : ¬p ∣ n) : n.factorization p = 0 := by
  simp [factorization_eq_zero_iff, h]

/--
theorem `factorization_eq_zero_of_remainder` / 定理 `factorization_eq_zero_of_remainder`

English:
theorem factorization_eq_zero_of_remainder
  given: {p r : Nat} (i : Nat) (hr : ¬p ∣ r)
  proof: by
  apply factorization_eq_zero_of_not_dvd
  rwa [← Nat.dvd_add_iff_right (Dvd.intro i rfl)]

中文:
定理 factorization_eq_zero_of_remainder
  条件: {p r : 自然数} (i : 自然数) (hr : ¬p ∣ r)
  证明: by
  apply factorization_eq_zero_of_not_dvd
  rwa [← Nat.dvd_add_iff_right (Dvd.intro i rfl)]

Depends on / 依赖: Dvd.intro, Nat.dvd_add_iff_right, dvd_add_iff_right, factorization_eq_zero_of_not_dvd
-/
theorem factorization_eq_zero_of_remainder {p r : Nat} (i : Nat) (hr : ¬p ∣ r) :
    (p * i + r).factorization p = 0 := by
  apply factorization_eq_zero_of_not_dvd
  rwa [← Nat.dvd_add_iff_right (Dvd.intro i rfl)]

/-! ## Lemmas about factorizations of products and powers -/

/-- For nonzero `a` and `b`, the power of `p` in `a * b` is the sum of the powers in `a` and `b` -/
@[simp]
/--
theorem `factorization_mul` / 定理 `factorization_mul`

English:
theorem factorization_mul
  given: {a b : Nat} (ha : a != 0) (hb : b != 0)
  proof: by
  ext p
  simp only [add_apply, ← primeFactorsList_count_eq,
    perm_iff_count.mp (perm_primeFactorsList_mul ha hb) p, count_append]

中文:
定理 factorization_mul
  条件: {a b : 自然数} (ha : a != 0) (hb : b != 0)
  证明: by
  ext p
  simp only [add_apply, ← primeFactorsList_count_eq,
    perm_iff_count.mp (perm_primeFactorsList_mul ha hb) p, count_append]

Depends on / 依赖: add_apply, count_append, perm_iff_count, perm_iff_count.mp, perm_primeFactorsList_mul, primeFactorsList_count_eq
-/
theorem factorization_mul {a b : Nat} (ha : a != 0) (hb : b != 0) :
    (a * b).factorization = a.factorization + b.factorization := by
  ext p
  simp only [add_apply, ← primeFactorsList_count_eq,
    perm_iff_count.mp (perm_primeFactorsList_mul ha hb) p, count_append]

/--
theorem `factorization_le_iff_dvd` / 定理 `factorization_le_iff_dvd`

English:
theorem factorization_le_iff_dvd
  given: {d n : Nat} (hd : d != 0) (hn : n != 0)
  proof: by
  refine ⟨fun hdn => ?_, fun ⟨c, h⟩ => ?_⟩
  · rw [← prod_factorization_pow_eq_self hn, ← prod_factorization_pow_eq_self hd]
    exact prod_dvd_prod_of_subset_of_dvd (support_mono hdn) fun a _ => pow_dvd_pow a (hdn a)
  · subst h
    rw [factorization_mul hd <| right_ne_zero_of_mul hn]
    apply 

中文:
定理 factorization_le_iff_dvd
  条件: {d n : 自然数} (hd : d != 0) (hn : n != 0)
  证明: by
  refine ⟨fun hdn => ?_, fun ⟨c, h⟩ => ?_⟩
  · rw [← prod_factorization_pow_eq_self hn, ← prod_factorization_pow_eq_self hd]
    exact prod_dvd_prod_of_subset_of_dvd (support_mono hdn) fun a _ => pow_dvd_pow a (hdn a)
  · subst h
    rw [factorization_mul hd <| right_ne_zero_of_mul hn]
    apply 

Depends on / 依赖: factorization_mul, pow_dvd_pow, prod_dvd_prod_of_subset_of_dvd, prod_factorization_pow_eq_self, right_ne_zero_of_mul, self_le_add_right, support_mono
-/
theorem factorization_le_iff_dvd {d n : Nat} (hd : d != 0) (hn : n != 0) :
    d.factorization <= n.factorization ↔ d ∣ n := by
  refine ⟨fun hdn => ?_, fun ⟨c, h⟩ => ?_⟩
  · rw [← prod_factorization_pow_eq_self hn, ← prod_factorization_pow_eq_self hd]
    exact prod_dvd_prod_of_subset_of_dvd (support_mono hdn) fun a _ => pow_dvd_pow a (hdn a)
  · subst h
    rw [factorization_mul hd <| right_ne_zero_of_mul hn]
    apply self_le_add_right

/--
theorem `factorization_prod` / 定理 `factorization_prod`

English:
theorem factorization_prod
  given: {α : Type*} {S : Finset α} {g : α -> Nat} (hS : forall x in S, g x != 0)
  proof: by
  classical
    refine Finset.induction_on' S ?_ ?_
    · simp
    · intro x T hxS hTS hxT IH
      have hT : T.prod g != 0 := prod_ne_zero_iff.mpr fun x hx => hS x (hTS hx)
      simp [prod_insert hxT, sum_insert hxT, IH, factorization_mul (hS x hxS) hT]

中文:
定理 factorization_prod
  条件: {α : 类型} {S : Finset α} {g : α -> 自然数} (hS : 对任意 x in S, g x != 0)
  证明: by
  classical
    refine Finset.induction_on' S ?_ ?_
    · simp
    · intro x T hxS hTS hxT IH
      have hT : T.prod g != 0 := prod_ne_zero_iff.mpr fun x hx => hS x (hTS hx)
      simp [prod_insert hxT, sum_insert hxT, IH, factorization_mul (hS x hxS) hT]

Depends on / 依赖: Finset, Finset.induction_on, T.prod, classical, factorization_mul, induction_on, prod_insert, prod_ne_zero_iff, prod_ne_zero_iff.mpr, sum_insert
-/
theorem factorization_prod {α : Type*} {S : Finset α} {g : α -> Nat} (hS : forall x in S, g x != 0) :
    (S.prod g).factorization = S.sum fun x => (g x).factorization := by
  classical
    refine Finset.induction_on' S ?_ ?_
    · simp
    · intro x T hxS hTS hxT IH
      have hT : T.prod g != 0 := prod_ne_zero_iff.mpr fun x hx => hS x (hTS hx)
      simp [prod_insert hxT, sum_insert hxT, IH, factorization_mul (hS x hxS) hT]

/-- For any `p`, the power of `p` in `n^k` is `k` times the power in `n` -/
@[simp]
/--
theorem `factorization_pow` / 定理 `factorization_pow`

English:
theorem factorization_pow
  given: (n k : Nat)
  statement: factorization (n ^ k) = k • n.factorization
  proof: by
  induction k with
  | zero => simp
  | succ k ih =>
    rcases eq_or_ne n 0 with (rfl | hn)
    · simp
    rw [Nat.pow_succ]; rw [mul_comm]; rw [factorization_mul hn (pow_ne_zero _ hn)]; rw [ih]; rw [add_smul]; rw [one_smul]; rw [add_comm]

中文:
定理 factorization_pow
  条件: (n k : 自然数)
  结论: factorization (n ^ k) = k • n.factorization
  证明: by
  induction k with
  | zero => simp
  | succ k ih =>
    rcases eq_or_ne n 0 with (rfl | hn)
    · simp
    rw [Nat.pow_succ]; rw [mul_comm]; rw [factorization_mul hn (pow_ne_zero _ hn)]; rw [ih]; rw [add_smul]; rw [one_smul]; rw [add_comm]

Depends on / 依赖: Nat.pow_succ, add_comm, add_smul, eq_or_ne, factorization_mul, mul_comm, one_smul, pow_ne_zero, pow_succ
-/
theorem factorization_pow (n k : Nat) : factorization (n ^ k) = k • n.factorization := by
  induction k with
  | zero => simp
  | succ k ih =>
    rcases eq_or_ne n 0 with (rfl | hn)
    · simp
    rw [Nat.pow_succ]; rw [mul_comm]; rw [factorization_mul hn (pow_ne_zero _ hn)]; rw [ih]; rw [add_smul]; rw [one_smul]; rw [add_comm]

/-! ## Lemmas about factorizations of primes and prime powers -/


/-- The only prime factor of prime `p` is `p` itself, with multiplicity `1` -/
@[simp]
/--
theorem `Prime.factorization` / 定理 `Prime.factorization`

English:
theorem Prime.factorization
  given: {p : Nat} (hp : Prime p)
  statement: p.factorization = single p 1
  proof: by
  ext q
  rw [← primeFactorsList_count_eq]; rw [primeFactorsList_prime hp]; rw [single_apply]; rw [count_singleton']; rw [if_congr eq_comm] <;> rfl

中文:
定理 Prime.factorization
  条件: {p : 自然数} (hp : Prime p)
  结论: p.factorization = single p 1
  证明: by
  ext q
  rw [← primeFactorsList_count_eq]; rw [primeFactorsList_prime hp]; rw [single_apply]; rw [count_singleton']; rw [if_congr eq_comm] <;> rfl
-/
protected theorem Prime.factorization {p : Nat} (hp : Prime p) : p.factorization = single p 1 := by
  ext q
  rw [← primeFactorsList_count_eq]; rw [primeFactorsList_prime hp]; rw [single_apply]; rw [count_singleton']; rw [if_congr eq_comm] <;> rfl

/--
theorem `Prime.factorization_pow` / 定理 `Prime.factorization_pow`

English:
theorem Prime.factorization_pow
  given: {p k : Nat} (hp : Prime p)
  statement: (p ^ k).factorization = single p k
  proof: by
  simp [hp]

中文:
定理 Prime.factorization_pow
  条件: {p k : 自然数} (hp : Prime p)
  结论: (p ^ k).factorization = single p k
  证明: by
  simp [hp]
-/
theorem Prime.factorization_pow {p k : Nat} (hp : Prime p) : (p ^ k).factorization = single p k := by
  simp [hp]

/--
theorem `pow_succ_factorization_not_dvd` / 定理 `pow_succ_factorization_not_dvd`

English:
theorem pow_succ_factorization_not_dvd
  given: {n p : Nat} (hn : n != 0) (hp : p.Prime)
  proof: by
  intro h
  rw [← factorization_le_iff_dvd (pow_ne_zero _ hp.ne_zero) hn] at h
  simpa [hp.factorization] using h p

中文:
定理 pow_succ_factorization_not_dvd
  条件: {n p : 自然数} (hn : n != 0) (hp : p.Prime)
  证明: by
  intro h
  rw [← factorization_le_iff_dvd (pow_ne_zero _ hp.ne_zero) hn] at h
  simpa [hp.factorization] using h p

Depends on / 依赖: factorization, factorization_le_iff_dvd, hp.factorization, hp.ne_zero, ne_zero, pow_ne_zero
-/
theorem pow_succ_factorization_not_dvd {n p : Nat} (hn : n != 0) (hp : p.Prime) :
    ¬p ^ (n.factorization p + 1) ∣ n := by
  intro h
  rw [← factorization_le_iff_dvd (pow_ne_zero _ hp.ne_zero) hn] at h
  simpa [hp.factorization] using h p

/--
lemma `factorization_minFac_ne_zero` / 引理 `factorization_minFac_ne_zero`

English:
lemma factorization_minFac_ne_zero
  given: {n : Nat} (hn : 1 < n)
  proof: by
  refine mt (factorization_eq_zero_iff _ _).mp ?_
  push Not
  exact ⟨minFac_prime (by lia), minFac_dvd n, Nat.ne_zero_of_lt hn⟩

中文:
引理 factorization_minFac_ne_zero
  条件: {n : 自然数} (hn : 1 < n)
  证明: by
  refine mt (factorization_eq_zero_iff _ _).mp ?_
  push Not
  exact ⟨minFac_prime (by lia), minFac_dvd n, Nat.ne_zero_of_lt hn⟩

Depends on / 依赖: Nat.ne_zero_of_lt, factorization_eq_zero_iff, minFac_dvd, minFac_prime, ne_zero_of_lt
-/
lemma factorization_minFac_ne_zero {n : Nat} (hn : 1 < n) :
    n.factorization n.minFac != 0 := by
  refine mt (factorization_eq_zero_iff _ _).mp ?_
  push Not
  exact ⟨minFac_prime (by lia), minFac_dvd n, Nat.ne_zero_of_lt hn⟩

/-! ### Equivalence between `ℕ+` and `ℕ →₀ ℕ` with support in the primes. -/

variable {f : Nat ->₀ Nat}

-- TODO: Rename to `factorization_prod_pow_eq_self`
/--
theorem `prod_pow_factorization_eq_self` / 定理 `prod_pow_factorization_eq_self`

English:
theorem prod_pow_factorization_eq_self
  given: (hf : forall p in f.support, Prime p)
  proof: by
  rw [Finsupp.prod]; rw [factorization_prod (pow_ne_zero _ <| hf · · |>.ne_zero)]; rw [sum_congr rfl (hf · · |>.factorization_pow)]
  exact sum_single f

中文:
定理 prod_pow_factorization_eq_self
  条件: (hf : 对任意 p in f.support, Prime p)
  证明: by
  rw [Finsupp.prod]; rw [factorization_prod (pow_ne_zero _ <| hf · · |>.ne_zero)]; rw [sum_congr rfl (hf · · |>.factorization_pow)]
  exact sum_single f

Depends on / 依赖: Finsupp, Finsupp.prod, factorization_pow, factorization_prod, ne_zero, pow_ne_zero, sum_congr, sum_single
-/
theorem prod_pow_factorization_eq_self (hf : forall p in f.support, Prime p) :
    (f.prod (· ^ ·)).factorization = f := by
  rw [Finsupp.prod]; rw [factorization_prod (pow_ne_zero _ <| hf · · |>.ne_zero)]; rw [sum_congr rfl (hf · · |>.factorization_pow)]
  exact sum_single f

/--
theorem `eq_factorization_iff` / 定理 `eq_factorization_iff`

English:
theorem eq_factorization_iff
  given: (hn : n != 0) (hf : forall p in f.support, Prime p)
  proof: by
  constructor <;> rintro rfl
  exacts [prod_factorization_pow_eq_self hn, prod_pow_factorization_eq_self hf |>.symm]

中文:
定理 eq_factorization_iff
  条件: (hn : n != 0) (hf : 对任意 p in f.support, Prime p)
  证明: by
  constructor <;> rintro rfl
  exacts [prod_factorization_pow_eq_self hn, prod_pow_factorization_eq_self hf |>.symm]

Depends on / 依赖: exacts, prod_factorization_pow_eq_self, prod_pow_factorization_eq_self
-/
theorem eq_factorization_iff (hn : n != 0) (hf : forall p in f.support, Prime p) :
    f = n.factorization ↔ f.prod (· ^ ·) = n := by
  constructor <;> rintro rfl
  exacts [prod_factorization_pow_eq_self hn, prod_pow_factorization_eq_self hf |>.symm]

/--
theorem `factorization_prod_pow_eq_self_of_le_factorization` / 定理 `factorization_prod_pow_eq_self_of_le_factorization`

English:
theorem factorization_prod_pow_eq_self_of_le_factorization
  given: (hf : f <= n.factorization)
  proof: prod_pow_factorization_eq_self fun _ hp => prime_of_mem_primeFactors support_mono hf hp

中文:
定理 factorization_prod_pow_eq_self_of_le_factorization
  条件: (hf : f <= n.factorization)
  证明: prod_pow_factorization_eq_self fun _ hp => prime_of_mem_primeFactors support_mono hf hp

Depends on / 依赖: prime_of_mem_primeFactors, prod_pow_factorization_eq_self, support_mono
-/
theorem factorization_prod_pow_eq_self_of_le_factorization (hf : f <= n.factorization) :
    (f.prod (· ^ ·)).factorization = f :=
prod_pow_factorization_eq_self fun _ hp => prime_of_mem_primeFactors support_mono hf hp

/--
theorem `prod_pow_dvd_of_le_factorization` / 定理 `prod_pow_dvd_of_le_factorization`

English:
theorem prod_pow_dvd_of_le_factorization
  given: (hf : f <= n.factorization)
  statement: f.prod (· ^ ·) ∣ n
  proof: by
  rcases eq_or_ne n 0 with (rfl | hn)
  · simp
  rwa [← factorization_le_iff_dvd ?_ hn, factorization_prod_pow_eq_self_of_le_factorization hf]
  refine f.prod_ne_zero_iff.mpr fun _ hp => ?_
  exact pow_ne_zero _ (prime_of_mem_primeFactors <| support_mono hf hp).ne_zero

中文:
定理 prod_pow_dvd_of_le_factorization
  条件: (hf : f <= n.factorization)
  结论: f.prod (· ^ ·) ∣ n
  证明: by
  rcases eq_or_ne n 0 with (rfl | hn)
  · simp
  rwa [← factorization_le_iff_dvd ?_ hn, factorization_prod_pow_eq_self_of_le_factorization hf]
  refine f.prod_ne_zero_iff.mpr fun _ hp => ?_
  exact pow_ne_zero _ (prime_of_mem_primeFactors <| support_mono hf hp).ne_zero

Depends on / 依赖: eq_or_ne, f.prod_ne_zero_iff.mpr, factorization_le_iff_dvd, factorization_prod_pow_eq_self_of_le_factorization, ne_zero, pow_ne_zero, prime_of_mem_primeFactors, prod_ne_zero_iff, support_mono
-/
theorem prod_pow_dvd_of_le_factorization (hf : f <= n.factorization) : f.prod (· ^ ·) ∣ n := by
  rcases eq_or_ne n 0 with (rfl | hn)
  · simp
  rwa [← factorization_le_iff_dvd ?_ hn, factorization_prod_pow_eq_self_of_le_factorization hf]
  refine f.prod_ne_zero_iff.mpr fun _ hp => ?_
  exact pow_ne_zero _ (prime_of_mem_primeFactors <| support_mono hf hp).ne_zero

/--
theorem `dvd_prod_pow_of_factorization_le` / 定理 `dvd_prod_pow_of_factorization_le`

English:
theorem dvd_prod_pow_of_factorization_le
  given: (hn : n != 0) (hf : n.factorization <= f)
  proof: by
  rw [← add_tsub_cancel_of_le hf]; rw [Finsupp.prod_add_index' (by simp) Nat.pow_add]; rw [prod_factorization_pow_eq_self hn]
  apply n.dvd_mul_right

中文:
定理 dvd_prod_pow_of_factorization_le
  条件: (hn : n != 0) (hf : n.factorization <= f)
  证明: by
  rw [← add_tsub_cancel_of_le hf]; rw [Finsupp.prod_add_index' (by simp) Nat.pow_add]; rw [prod_factorization_pow_eq_self hn]
  apply n.dvd_mul_right

Depends on / 依赖: Finsupp, Finsupp.prod_add_index, Nat.pow_add, add_tsub_cancel_of_le, dvd_mul_right, n.dvd_mul_right, pow_add, prod_add_index, prod_factorization_pow_eq_self
-/
theorem dvd_prod_pow_of_factorization_le (hn : n != 0) (hf : n.factorization <= f) :
    n ∣ f.prod (· ^ ·) := by
  rw [← add_tsub_cancel_of_le hf]; rw [Finsupp.prod_add_index' (by simp) Nat.pow_add]; rw [prod_factorization_pow_eq_self hn]
  apply n.dvd_mul_right

/--
theorem `dvd_iff_exists_le_factorization` / 定理 `dvd_iff_exists_le_factorization`

English:
theorem dvd_iff_exists_le_factorization
  given: {d : Nat} (hd : d != 0) (hn : n != 0)
  proof: by
  rw [← factorization_le_iff_dvd hd hn]
.symm⟩, fun ⟨f, hle, hprod⟩ => ?_⟩ refine ⟨fun h => ⟨_, h, prod_factorization_pow_eq_self hd
  rwa [hprod, factorization_prod_pow_eq_self_of_le_factorization hle]

中文:
定理 dvd_iff_exists_le_factorization
  条件: {d : 自然数} (hd : d != 0) (hn : n != 0)
  证明: by
  rw [← factorization_le_iff_dvd hd hn]
.symm⟩, fun ⟨f, hle, hprod⟩ => ?_⟩ refine ⟨fun h => ⟨_, h, prod_factorization_pow_eq_self hd
  rwa [hprod, factorization_prod_pow_eq_self_of_le_factorization hle]

Depends on / 依赖: factorization_le_iff_dvd, factorization_prod_pow_eq_self_of_le_factorization, prod_factorization_pow_eq_self
-/
theorem dvd_iff_exists_le_factorization {d : Nat} (hd : d != 0) (hn : n != 0) :
    d ∣ n ↔ exists f <= n.factorization, d = f.prod (· ^ ·) := by
  rw [← factorization_le_iff_dvd hd hn]
.symm⟩, fun ⟨f, hle, hprod⟩ => ?_⟩ refine ⟨fun h => ⟨_, h, prod_factorization_pow_eq_self hd
  rwa [hprod, factorization_prod_pow_eq_self_of_le_factorization hle]

/-- The equiv between `ℕ+` and `ℕ →₀ ℕ` with support in the primes. -/
@[simps]
/--
Definition of `factorizationEquiv` / `factorizationEquiv` 的定义

English:
definition factorizationEquiv
  signature: : Nat+ ≃ { f : Nat ->₀ Nat // forall p in f.support, Prime p } where
  body: fun ⟨n, _⟩ => ⟨n.factorization, fun _ => prime_of_mem_primeFactors⟩
  invFun := fun ⟨f, hf⟩ =>
    ⟨f.prod _, prod_pow_pos_of_zero_notMem_support fun H => not_prime_zero (hf 0 H)⟩
left_inv := fun ⟨_, hx⟩ => Subtype.ext prod_factorization_pow_eq_self hx.ne.symm
right_inv := fun ⟨_, hf⟩ => Subtype.ext

中文:
定义 factorizationEquiv
  签名: : 自然数+ ≃ { f : 自然数 ->₀ 自然数 // 对任意 p in f.support, Prime p } where
  定义体: fun ⟨n, _⟩ => ⟨n.factorization, fun _ => prime_of_mem_primeFactors⟩
  invFun := fun ⟨f, hf⟩ =>
    ⟨f.prod _, prod_pow_pos_of_zero_notMem_support fun H => not_prime_zero (hf 0 H)⟩
left_inv := fun ⟨_, hx⟩ => Subtype.ext prod_factorization_pow_eq_self hx.ne.symm
right_inv := fun ⟨_, hf⟩ => Subtype.ext

Depends on / 依赖: factorization, n.factorization, prime_of_mem_primeFactors
-/
def factorizationEquiv : Nat+ ≃ { f : Nat ->₀ Nat // forall p in f.support, Prime p } where
  toFun := fun ⟨n, _⟩ => ⟨n.factorization, fun _ => prime_of_mem_primeFactors⟩
  invFun := fun ⟨f, hf⟩ =>
    ⟨f.prod _, prod_pow_pos_of_zero_notMem_support fun H => not_prime_zero (hf 0 H)⟩
left_inv := fun ⟨_, hx⟩ => Subtype.ext prod_factorization_pow_eq_self hx.ne.symm
right_inv := fun ⟨_, hf⟩ => Subtype.ext prod_pow_factorization_eq_self hf

/-! ### Factorization and coprimes -/


/--
theorem `factorization_mul_apply_of_coprime` / 定理 `factorization_mul_apply_of_coprime`

English:
theorem factorization_mul_apply_of_coprime
  given: {p a b : Nat} (hab : Coprime a b)
  proof: by
  simp only [← primeFactorsList_count_eq,
    perm_iff_count.mp (perm_primeFactorsList_mul_of_coprime hab), count_append]

中文:
定理 factorization_mul_apply_of_coprime
  条件: {p a b : 自然数} (hab : Coprime a b)
  证明: by
  simp only [← primeFactorsList_count_eq,
    perm_iff_count.mp (perm_primeFactorsList_mul_of_coprime hab), count_append]

Depends on / 依赖: count_append, perm_iff_count, perm_iff_count.mp, perm_primeFactorsList_mul_of_coprime, primeFactorsList_count_eq
-/
theorem factorization_mul_apply_of_coprime {p a b : Nat} (hab : Coprime a b) :
    (a * b).factorization p = a.factorization p + b.factorization p := by
  simp only [← primeFactorsList_count_eq,
    perm_iff_count.mp (perm_primeFactorsList_mul_of_coprime hab), count_append]

/--
theorem `factorization_mul_of_coprime` / 定理 `factorization_mul_of_coprime`

English:
theorem factorization_mul_of_coprime
  given: {a b : Nat} (hab : Coprime a b)
  proof: by
  ext q
  rw [Finsupp.add_apply]; rw [factorization_mul_apply_of_coprime hab]

中文:
定理 factorization_mul_of_coprime
  条件: {a b : 自然数} (hab : Coprime a b)
  证明: by
  ext q
  rw [Finsupp.add_apply]; rw [factorization_mul_apply_of_coprime hab]

Depends on / 依赖: Finsupp, Finsupp.add_apply, add_apply, factorization_mul_apply_of_coprime
-/
theorem factorization_mul_of_coprime {a b : Nat} (hab : Coprime a b) :
    (a * b).factorization = a.factorization + b.factorization := by
  ext q
  rw [Finsupp.add_apply]; rw [factorization_mul_apply_of_coprime hab]

/-! ### Generalisation of the "even part" and "odd part" of a natural number -/

/-- We introduce the notations `ordProj[p] n` for the largest power of the prime `p` that
divides `n` and `ordCompl[p] n` for the complementary part. The `ord` naming comes from
the $p$-adic order/valuation of a number, and `proj` and `compl` are for the projection and
complementary projection. The term `n.factorization p` is the $p$-adic order itself.
For example, `ordProj[2] n` is the even part of `n` and `ordCompl[2] n` is the odd part. -/
notation "ordProj[" p "] " n:arg => p ^ Nat.factorization n p

@[inherit_doc «termOrdProj[_]_»]
notation "ordCompl[" p "] " n:arg => n / ordProj[p] n

/--
theorem `ordProj_dvd` / 定理 `ordProj_dvd`

English:
theorem ordProj_dvd
  given: (n p : Nat)
  statement: ordProj[p] n ∣ n
  proof: by
  if hp : p.Prime then ?_ else simp [hp]
  rw [← primeFactorsList_count_eq]
  apply dvd_of_primeFactorsList_subperm (pow_ne_zero _ hp.ne_zero)
  rw [hp.primeFactorsList_pow]; rw [List.subperm_ext_iff]
  intro q hq
  simp [List.eq_of_mem_replicate hq]

中文:
定理 ordProj_dvd
  条件: (n p : 自然数)
  结论: ordProj[p] n ∣ n
  证明: by
  if hp : p.Prime then ?_ else simp [hp]
  rw [← primeFactorsList_count_eq]
  apply dvd_of_primeFactorsList_subperm (pow_ne_zero _ hp.ne_zero)
  rw [hp.primeFactorsList_pow]; rw [List.subperm_ext_iff]
  intro q hq
  simp [List.eq_of_mem_replicate hq]

Depends on / 依赖: List.eq_of_mem_replicate, List.subperm_ext_iff, dvd_of_primeFactorsList_subperm, eq_of_mem_replicate, hp.ne_zero, hp.primeFactorsList_pow, ne_zero, p.Prime, pow_ne_zero, primeFactorsList_count_eq, primeFactorsList_pow, subperm_ext_iff
-/
theorem ordProj_dvd (n p : Nat) : ordProj[p] n ∣ n := by
  if hp : p.Prime then ?_ else simp [hp]
  rw [← primeFactorsList_count_eq]
  apply dvd_of_primeFactorsList_subperm (pow_ne_zero _ hp.ne_zero)
  rw [hp.primeFactorsList_pow]; rw [List.subperm_ext_iff]
  intro q hq
  simp [List.eq_of_mem_replicate hq]

/--
lemma `ordProj_dvd_ordProj_iff_dvd` / 引理 `ordProj_dvd_ordProj_iff_dvd`

English:
lemma ordProj_dvd_ordProj_iff_dvd
  given: (ha : a != 0) (hb : b != 0)
  proof: by
  rw [← factorization_le_iff_dvd ha hb]; rw [Finsupp.le_def]
  congr! 1 with p
  obtain _ | _ | p := p <;> simp [Nat.pow_dvd_pow_iff_le_right]

中文:
引理 ordProj_dvd_ordProj_iff_dvd
  条件: (ha : a != 0) (hb : b != 0)
  证明: by
  rw [← factorization_le_iff_dvd ha hb]; rw [Finsupp.le_def]
  congr! 1 with p
  obtain _ | _ | p := p <;> simp [Nat.pow_dvd_pow_iff_le_right]

Depends on / 依赖: Finsupp, Finsupp.le_def, Nat.pow_dvd_pow_iff_le_right, factorization_le_iff_dvd, le_def, pow_dvd_pow_iff_le_right
-/
lemma ordProj_dvd_ordProj_iff_dvd (ha : a != 0) (hb : b != 0) :
    (forall p : Nat, ordProj[p] a ∣ ordProj[p] b) ↔ a ∣ b := by
  rw [← factorization_le_iff_dvd ha hb]; rw [Finsupp.le_def]
  congr! 1 with p
  obtain _ | _ | p := p <;> simp [Nat.pow_dvd_pow_iff_le_right]

/-! ### Factorization LCM definitions -/


/--
Definition of `factorizationLCMLeft` / `factorizationLCMLeft` 的定义

English:
definition factorizationLCMLeft
  signature: (a b : Nat)
  body: (Nat.lcm a b).factorization.prod fun p n =>
    if b.factorization p <= a.factorization p then p ^ n else 1

中文:
定义 factorizationLCMLeft
  签名: (a b : 自然数)
  定义体: (Nat.lcm a b).factorization.prod fun p n =>
    if b.factorization p <= a.factorization p then p ^ n else 1

Depends on / 依赖: Nat.lcm, a.factorization, b.factorization, factorization, factorization.prod
-/
def factorizationLCMLeft (a b : Nat) : Nat :=
  (Nat.lcm a b).factorization.prod fun p n =>
    if b.factorization p <= a.factorization p then p ^ n else 1

/--
Definition of `factorizationLCMRight` / `factorizationLCMRight` 的定义

English:
definition factorizationLCMRight
  signature: (a b : Nat)
  body: (Nat.lcm a b).factorization.prod fun p n =>
    if b.factorization p <= a.factorization p then 1 else p ^ n

中文:
定义 factorizationLCMRight
  签名: (a b : 自然数)
  定义体: (Nat.lcm a b).factorization.prod fun p n =>
    if b.factorization p <= a.factorization p then 1 else p ^ n

Depends on / 依赖: Nat.lcm, a.factorization, b.factorization, factorization, factorization.prod
-/
def factorizationLCMRight (a b : Nat) :=
  (Nat.lcm a b).factorization.prod fun p n =>
    if b.factorization p <= a.factorization p then 1 else p ^ n

end Nat
