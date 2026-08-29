/-
Copyright (c) 2023 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll, Ralf Stephan
-/
module

public import Mathlib.Data.Nat.Factorization.Defs
public import Mathlib.Data.Nat.Squarefree
public import Mathlib.NumberTheory.PrimeCounting

/-!
# Smooth numbers

For `s : Finset ℕ` we define the set `Nat.factoredNumbers s` of "`s`-factored numbers"
consisting of the positive natural numbers all of whose prime factors are in `s`, and
we provide some API for this.

We then define the set `Nat.smoothNumbers n` consisting of the positive natural numbers all of
whose prime factors are strictly less than `n`. This is the special case `s = Finset.range n`
of the set of `s`-factored numbers.

The main definition `Nat.equivProdNatSmoothNumbers` establishes the bijection between
`ℕ × (smoothNumbers p)` and `smoothNumbers (p+1)` given by sending `(e, n)` to `p^e * n`.
Here `p` is a prime number. It is obtained from the more general bijection between
`ℕ × (factoredNumbers s)` and `factoredNumbers (s ∪ {p})`; see `Nat.equivProdNatFactoredNumbers`.

Additionally, we define `Nat.smoothNumbersUpTo N n` as the `Finset` of `n`-smooth numbers
up to and including `N`, and similarly `Nat.roughNumbersUpTo` for its complement in `{1, ..., N}`,
and we provide some API, in particular bounds for their cardinalities; see
`Nat.smoothNumbersUpTo_card_le` and `Nat.roughNumbersUpTo_card_le`.
-/

@[expose] public section

open scoped Finset
namespace Nat

/-!
### `s`-factored numbers
-/

/--
Definition of `factoredNumbers` / `factoredNumbers` 的定义

English:
definition factoredNumbers
  signature: (s : Finset Nat)
  body: {m | m != 0 ∧ forall p in primeFactorsList m, p in s}

中文:
定义 factoredNumbers
  签名: (s : Finset 自然数)
  定义体: {m | m != 0 ∧ forall p in primeFactorsList m, p in s}

Depends on / 依赖: primeFactorsList
-/
def factoredNumbers (s : Finset Nat) : Set Nat := {m | m != 0 ∧ forall p in primeFactorsList m, p in s}

/--
lemma `mem_factoredNumbers` / 引理 `mem_factoredNumbers`

English:
lemma mem_factoredNumbers
  given: {s : Finset Nat} {m : Nat}
  proof: Iff.rfl

中文:
引理 mem_factoredNumbers
  条件: {s : Finset 自然数} {m : 自然数}
  证明: Iff.rfl

Depends on / 依赖: Iff.rfl
-/
lemma mem_factoredNumbers {s : Finset Nat} {m : Nat} :
    m in factoredNumbers s ↔ m != 0 ∧ forall p in primeFactorsList m, p in s :=
  Iff.rfl

/-- Membership in `Nat.factoredNumbers n` is decidable. -/
instance (s : Finset Nat) : DecidablePred (· in factoredNumbers s) :=
inferInstanceAs DecidablePred fun x => x in {m | m != 0 ∧ forall p in primeFactorsList m, p in s}

/--
lemma `mem_factoredNumbers_of_dvd` / 引理 `mem_factoredNumbers_of_dvd`

English:
lemma mem_factoredNumbers_of_dvd
  statement: {s : Finset Nat} {m k : Nat} (h : m in factoredNumbers s)
  proof: by
  obtain ⟨h₁, h₂⟩ := h
  have hk := ne_zero_of_dvd_ne_zero h₁ h'
  refine ⟨hk, fun p hp => h₂ p ?_⟩
  rw [mem_primeFactorsList <| by assumption] at hp ⊢
  exact ⟨hp.1, hp.2.trans h'⟩

中文:
引理 mem_factoredNumbers_of_dvd
  结论: {s : Finset 自然数} {m k : 自然数} (h : m in factoredNumbers s)
  证明: by
  obtain ⟨h₁, h₂⟩ := h
  have hk := ne_zero_of_dvd_ne_zero h₁ h'
  refine ⟨hk, fun p hp => h₂ p ?_⟩
  rw [mem_primeFactorsList <| by assumption] at hp ⊢
  exact ⟨hp.1, hp.2.trans h'⟩

Depends on / 依赖: mem_primeFactorsList, ne_zero_of_dvd_ne_zero
-/
lemma mem_factoredNumbers_of_dvd {s : Finset Nat} {m k : Nat} (h : m in factoredNumbers s)
    (h' : k ∣ m) :
    k in factoredNumbers s := by
  obtain ⟨h₁, h₂⟩ := h
  have hk := ne_zero_of_dvd_ne_zero h₁ h'
  refine ⟨hk, fun p hp => h₂ p ?_⟩
  rw [mem_primeFactorsList <| by assumption] at hp ⊢
  exact ⟨hp.1, hp.2.trans h'⟩

/--
lemma `mem_factoredNumbers_iff_forall_le` / 引理 `mem_factoredNumbers_iff_forall_le`

English:
lemma mem_factoredNumbers_iff_forall_le
  given: {s : Finset Nat} {m : Nat}
  proof: by
  simp_rw [mem_factoredNumbers, mem_primeFactorsList']
  exact ⟨fun ⟨H₀, H₁⟩ => ⟨H₀, fun p _ hp₂ hp₃ => H₁ p ⟨hp₂, hp₃, H₀⟩⟩,
    fun ⟨H₀, H₁⟩ =>
      ⟨H₀, fun p ⟨hp₁, hp₂, hp₃⟩ => H₁ p (le_of_dvd (Nat.pos_of_ne_zero hp₃) hp₂) hp₁ hp₂⟩⟩

中文:
引理 mem_factoredNumbers_iff_forall_le
  条件: {s : Finset 自然数} {m : 自然数}
  证明: by
  simp_rw [mem_factoredNumbers, mem_primeFactorsList']
  exact ⟨fun ⟨H₀, H₁⟩ => ⟨H₀, fun p _ hp₂ hp₃ => H₁ p ⟨hp₂, hp₃, H₀⟩⟩,
    fun ⟨H₀, H₁⟩ =>
      ⟨H₀, fun p ⟨hp₁, hp₂, hp₃⟩ => H₁ p (le_of_dvd (Nat.pos_of_ne_zero hp₃) hp₂) hp₁ hp₂⟩⟩

Depends on / 依赖: Nat.pos_of_ne_zero, le_of_dvd, mem_factoredNumbers, mem_primeFactorsList, pos_of_ne_zero, simp_rw
-/
lemma mem_factoredNumbers_iff_forall_le {s : Finset Nat} {m : Nat} :
    m in factoredNumbers s ↔ m != 0 ∧ forall p <= m, p.Prime -> p ∣ m -> p in s := by
  simp_rw [mem_factoredNumbers, mem_primeFactorsList']
  exact ⟨fun ⟨H₀, H₁⟩ => ⟨H₀, fun p _ hp₂ hp₃ => H₁ p ⟨hp₂, hp₃, H₀⟩⟩,
    fun ⟨H₀, H₁⟩ =>
      ⟨H₀, fun p ⟨hp₁, hp₂, hp₃⟩ => H₁ p (le_of_dvd (Nat.pos_of_ne_zero hp₃) hp₂) hp₁ hp₂⟩⟩

/--
lemma `mem_factoredNumbers'` / 引理 `mem_factoredNumbers'`

English:
lemma mem_factoredNumbers'
  given: {s : Finset Nat} {m : Nat}
  proof: by
  obtain ⟨p, hp₁, hp₂⟩ := exists_infinite_primes (1 + Finset.sup s id)
  rw [mem_factoredNumbers_iff_forall_le]
  refine ⟨fun ⟨H₀, H₁⟩ => fun p hp₁ hp₂ => H₁ p (le_of_dvd (Nat.pos_of_ne_zero H₀) hp₂) hp₁ hp₂,
         fun H => ⟨fun h => lt_irrefl p ?_, fun p _ => H p⟩⟩
  calc
p <= s.sup id := Fin

中文:
引理 mem_factoredNumbers'
  条件: {s : Finset 自然数} {m : 自然数}
  证明: by
  obtain ⟨p, hp₁, hp₂⟩ := exists_infinite_primes (1 + Finset.sup s id)
  rw [mem_factoredNumbers_iff_forall_le]
  refine ⟨fun ⟨H₀, H₁⟩ => fun p hp₁ hp₂ => H₁ p (le_of_dvd (Nat.pos_of_ne_zero H₀) hp₂) hp₁ hp₂,
         fun H => ⟨fun h => lt_irrefl p ?_, fun p _ => H p⟩⟩
  calc
p <= s.sup id := Fin

Depends on / 依赖: Finset, Finset.le_sup, Finset.sup, Nat.pos_of_ne_zero, dvd_zero, exists_infinite_primes, h.symm, le_of_dvd, le_sup, lt_irrefl, lt_one_add, mem_factoredNumbers_iff_forall_le, pos_of_ne_zero, s.sup
-/
lemma mem_factoredNumbers' {s : Finset Nat} {m : Nat} :
    m in factoredNumbers s ↔ forall p, p.Prime -> p ∣ m -> p in s := by
  obtain ⟨p, hp₁, hp₂⟩ := exists_infinite_primes (1 + Finset.sup s id)
  rw [mem_factoredNumbers_iff_forall_le]
  refine ⟨fun ⟨H₀, H₁⟩ => fun p hp₁ hp₂ => H₁ p (le_of_dvd (Nat.pos_of_ne_zero H₀) hp₂) hp₁ hp₂,
         fun H => ⟨fun h => lt_irrefl p ?_, fun p _ => H p⟩⟩
  calc
p <= s.sup id := Finset.le_sup (f := @id Nat) H p hp₂ h.symm ▸ dvd_zero p
    _ < 1 + s.sup id := lt_one_add _
    _ <= p := hp₁

/--
lemma `ne_zero_of_mem_factoredNumbers` / 引理 `ne_zero_of_mem_factoredNumbers`

English:
lemma ne_zero_of_mem_factoredNumbers
  given: {s : Finset Nat} {m : Nat} (h : m in factoredNumbers s)
  statement: m != 0
  proof: h.1

中文:
引理 ne_zero_of_mem_factoredNumbers
  条件: {s : Finset 自然数} {m : 自然数} (h : m in factoredNumbers s)
  结论: m != 0
  证明: h.1
-/
lemma ne_zero_of_mem_factoredNumbers {s : Finset Nat} {m : Nat} (h : m in factoredNumbers s) : m != 0 :=
  h.1

/--
lemma `primeFactors_subset_of_mem_factoredNumbers` / 引理 `primeFactors_subset_of_mem_factoredNumbers`

English:
lemma primeFactors_subset_of_mem_factoredNumbers
  statement: {s : Finset Nat} {m : Nat}
  proof: by
  rw [mem_factoredNumbers] at hm
  exact fun n hn => hm.2 n (mem_primeFactors_iff_mem_primeFactorsList.mp hn)

中文:
引理 primeFactors_subset_of_mem_factoredNumbers
  结论: {s : Finset 自然数} {m : 自然数}
  证明: by
  rw [mem_factoredNumbers] at hm
  exact fun n hn => hm.2 n (mem_primeFactors_iff_mem_primeFactorsList.mp hn)

Depends on / 依赖: mem_factoredNumbers, mem_primeFactors_iff_mem_primeFactorsList, mem_primeFactors_iff_mem_primeFactorsList.mp
-/
lemma primeFactors_subset_of_mem_factoredNumbers {s : Finset Nat} {m : Nat}
    (hm : m in factoredNumbers s) :
    m.primeFactors subseteq s := by
  rw [mem_factoredNumbers] at hm
  exact fun n hn => hm.2 n (mem_primeFactors_iff_mem_primeFactorsList.mp hn)

/--
lemma `mem_factoredNumbers_of_primeFactors_subset` / 引理 `mem_factoredNumbers_of_primeFactors_subset`

English:
lemma mem_factoredNumbers_of_primeFactors_subset
  statement: {s : Finset Nat} {m : Nat} (hm : m != 0)
  proof: by
  rw [mem_factoredNumbers]
exact ⟨hm, fun p hp' => hp mem_primeFactors_iff_mem_primeFactorsList.mpr hp'⟩

中文:
引理 mem_factoredNumbers_of_primeFactors_subset
  结论: {s : Finset 自然数} {m : 自然数} (hm : m != 0)
  证明: by
  rw [mem_factoredNumbers]
exact ⟨hm, fun p hp' => hp mem_primeFactors_iff_mem_primeFactorsList.mpr hp'⟩

Depends on / 依赖: mem_factoredNumbers, mem_primeFactors_iff_mem_primeFactorsList, mem_primeFactors_iff_mem_primeFactorsList.mpr
-/
lemma mem_factoredNumbers_of_primeFactors_subset {s : Finset Nat} {m : Nat} (hm : m != 0)
    (hp : m.primeFactors subseteq s) :
    m in factoredNumbers s := by
  rw [mem_factoredNumbers]
exact ⟨hm, fun p hp' => hp mem_primeFactors_iff_mem_primeFactorsList.mpr hp'⟩

/--
lemma `mem_factoredNumbers_iff_primeFactors_subset` / 引理 `mem_factoredNumbers_iff_primeFactors_subset`

English:
lemma mem_factoredNumbers_iff_primeFactors_subset
  given: {s : Finset Nat} {m : Nat}
  proof: ⟨fun h => ⟨ne_zero_of_mem_factoredNumbers h, primeFactors_subset_of_mem_factoredNumbers h⟩,
   fun ⟨h₁, h₂⟩ => mem_factoredNumbers_of_primeFactors_subset h₁ h₂⟩

@[simp]

中文:
引理 mem_factoredNumbers_iff_primeFactors_subset
  条件: {s : Finset 自然数} {m : 自然数}
  证明: ⟨fun h => ⟨ne_zero_of_mem_factoredNumbers h, primeFactors_subset_of_mem_factoredNumbers h⟩,
   fun ⟨h₁, h₂⟩ => mem_factoredNumbers_of_primeFactors_subset h₁ h₂⟩

@[simp]

Depends on / 依赖: mem_factoredNumbers_of_primeFactors_subset, ne_zero_of_mem_factoredNumbers, primeFactors_subset_of_mem_factoredNumbers
-/
lemma mem_factoredNumbers_iff_primeFactors_subset {s : Finset Nat} {m : Nat} :
    m in factoredNumbers s ↔ m != 0 ∧ m.primeFactors subseteq s :=
  ⟨fun h => ⟨ne_zero_of_mem_factoredNumbers h, primeFactors_subset_of_mem_factoredNumbers h⟩,
   fun ⟨h₁, h₂⟩ => mem_factoredNumbers_of_primeFactors_subset h₁ h₂⟩

@[simp]
/--
lemma `factoredNumbers_empty` / 引理 `factoredNumbers_empty`

English:
lemma factoredNumbers_empty
  statement: factoredNumbers ∅ = {1}
  proof: by
  ext m
  simp only [mem_factoredNumbers, Finset.notMem_empty, ← List.eq_nil_iff_forall_not_mem,
    primeFactorsList_eq_nil, and_or_left, not_and_self_iff, ne_and_eq_iff_right zero_ne_one,
    false_or, Set.mem_singleton_iff]

中文:
引理 factoredNumbers_empty
  结论: factoredNumbers ∅ = {1}
  证明: by
  ext m
  simp only [mem_factoredNumbers, Finset.notMem_empty, ← List.eq_nil_iff_forall_not_mem,
    primeFactorsList_eq_nil, and_or_left, not_and_self_iff, ne_and_eq_iff_right zero_ne_one,
    false_or, Set.mem_singleton_iff]

Depends on / 依赖: Finset, Finset.notMem_empty, List.eq_nil_iff_forall_not_mem, Set.mem_singleton_iff, and_or_left, eq_nil_iff_forall_not_mem, false_or, mem_factoredNumbers, mem_singleton_iff, ne_and_eq_iff_right, notMem_empty, not_and_self_iff, primeFactorsList_eq_nil, zero_ne_one
-/
lemma factoredNumbers_empty : factoredNumbers ∅ = {1} := by
  ext m
  simp only [mem_factoredNumbers, Finset.notMem_empty, ← List.eq_nil_iff_forall_not_mem,
    primeFactorsList_eq_nil, and_or_left, not_and_self_iff, ne_and_eq_iff_right zero_ne_one,
    false_or, Set.mem_singleton_iff]

/--
lemma `mul_mem_factoredNumbers` / 引理 `mul_mem_factoredNumbers`

English:
lemma mul_mem_factoredNumbers
  statement: {s : Finset Nat} {m n : Nat} (hm : m in factoredNumbers s)
  proof: by
  have hm' := primeFactors_subset_of_mem_factoredNumbers hm
  have hn' := primeFactors_subset_of_mem_factoredNumbers hn
  exact mem_factoredNumbers_of_primeFactors_subset (mul_ne_zero hm.1 hn.1)
 primeFactors_mul hm.1 hn.1 ▸ Finset.union_subset hm' hn'

中文:
引理 mul_mem_factoredNumbers
  结论: {s : Finset 自然数} {m n : 自然数} (hm : m in factoredNumbers s)
  证明: by
  have hm' := primeFactors_subset_of_mem_factoredNumbers hm
  have hn' := primeFactors_subset_of_mem_factoredNumbers hn
  exact mem_factoredNumbers_of_primeFactors_subset (mul_ne_zero hm.1 hn.1)
 primeFactors_mul hm.1 hn.1 ▸ Finset.union_subset hm' hn'

Depends on / 依赖: Finset, Finset.union_subset, mem_factoredNumbers_of_primeFactors_subset, mul_ne_zero, primeFactors_mul, primeFactors_subset_of_mem_factoredNumbers, union_subset
-/
lemma mul_mem_factoredNumbers {s : Finset Nat} {m n : Nat} (hm : m in factoredNumbers s)
    (hn : n in factoredNumbers s) :
    m * n in factoredNumbers s := by
  have hm' := primeFactors_subset_of_mem_factoredNumbers hm
  have hn' := primeFactors_subset_of_mem_factoredNumbers hn
  exact mem_factoredNumbers_of_primeFactors_subset (mul_ne_zero hm.1 hn.1)
 primeFactors_mul hm.1 hn.1 ▸ Finset.union_subset hm' hn'

/--
lemma `prod_mem_factoredNumbers` / 引理 `prod_mem_factoredNumbers`

English:
lemma prod_mem_factoredNumbers
  given: (s : Finset Nat) (n : Nat)
  proof: by
  have h₀ : (n.primeFactorsList.filter (· in s)).prod != 0 :=
    List.prod_ne_zero fun h => (pos_of_mem_primeFactorsList (List.mem_of_mem_filter h)).false
  refine ⟨h₀, fun p hp => ?_⟩
  obtain ⟨H₁, H₂⟩ := (mem_primeFactorsList h₀).mp hp
simpa only [decide_eq_true_eq] using List.of_mem_filter me

中文:
引理 prod_mem_factoredNumbers
  条件: (s : Finset 自然数) (n : 自然数)
  证明: by
  have h₀ : (n.primeFactorsList.filter (· in s)).prod != 0 :=
    List.prod_ne_zero fun h => (pos_of_mem_primeFactorsList (List.mem_of_mem_filter h)).false
  refine ⟨h₀, fun p hp => ?_⟩
  obtain ⟨H₁, H₂⟩ := (mem_primeFactorsList h₀).mp hp
simpa only [decide_eq_true_eq] using List.of_mem_filter me

Depends on / 依赖: List.mem_of_mem_filter, List.of_mem_filter, List.prod_ne_zero, decide_eq_true_eq, filter, mem_list_primes_of_dvd_prod, mem_of_mem_filter, mem_primeFactorsList, n.primeFactorsList.filter, of_mem_filter, pos_of_mem_primeFactorsList, primeFactorsList, prime_of_mem_primeFactorsList, prod_ne_zero
-/
lemma prod_mem_factoredNumbers (s : Finset Nat) (n : Nat) :
    (n.primeFactorsList.filter (· in s)).prod in factoredNumbers s := by
  have h₀ : (n.primeFactorsList.filter (· in s)).prod != 0 :=
    List.prod_ne_zero fun h => (pos_of_mem_primeFactorsList (List.mem_of_mem_filter h)).false
  refine ⟨h₀, fun p hp => ?_⟩
  obtain ⟨H₁, H₂⟩ := (mem_primeFactorsList h₀).mp hp
simpa only [decide_eq_true_eq] using List.of_mem_filter mem_list_primes_of_dvd_prod H₁.prime
    (fun _ hq => (prime_of_mem_primeFactorsList (List.mem_of_mem_filter hq)).prime) H₂

/--
lemma `factoredNumbers_insert` / 引理 `factoredNumbers_insert`

English:
lemma factoredNumbers_insert
  given: (s : Finset Nat) {N : Nat} (hN : ¬ N.Prime)
  proof: by
  ext m
  refine ⟨fun hm => ⟨hm.1, fun p hp => ?_⟩,
fun hm => ⟨hm.1, fun p hp => Finset.mem_insert_of_mem hm.2 p hp⟩⟩
  exact Finset.mem_of_mem_insert_of_ne (hm.2 p hp)
fun h => hN h ▸ prime_of_mem_primeFactorsList hp

中文:
引理 factoredNumbers_insert
  条件: (s : Finset 自然数) {N : 自然数} (hN : ¬ N.Prime)
  证明: by
  ext m
  refine ⟨fun hm => ⟨hm.1, fun p hp => ?_⟩,
fun hm => ⟨hm.1, fun p hp => Finset.mem_insert_of_mem hm.2 p hp⟩⟩
  exact Finset.mem_of_mem_insert_of_ne (hm.2 p hp)
fun h => hN h ▸ prime_of_mem_primeFactorsList hp

Depends on / 依赖: Finset, Finset.mem_insert_of_mem, Finset.mem_of_mem_insert_of_ne, mem_insert_of_mem, mem_of_mem_insert_of_ne, prime_of_mem_primeFactorsList
-/
lemma factoredNumbers_insert (s : Finset Nat) {N : Nat} (hN : ¬ N.Prime) :
    factoredNumbers (insert N s) = factoredNumbers s := by
  ext m
  refine ⟨fun hm => ⟨hm.1, fun p hp => ?_⟩,
fun hm => ⟨hm.1, fun p hp => Finset.mem_insert_of_mem hm.2 p hp⟩⟩
  exact Finset.mem_of_mem_insert_of_ne (hm.2 p hp)
fun h => hN h ▸ prime_of_mem_primeFactorsList hp

/--
lemma `factoredNumbers_mono` / 引理 `factoredNumbers_mono`

English:
lemma factoredNumbers_mono
  given: {s t : Finset Nat} (hst : s <= t)
  proof: fun _ hx => ⟨hx.1, fun p hp => hst hx.2 p hp⟩

中文:
引理 factoredNumbers_mono
  条件: {s t : Finset 自然数} (hst : s <= t)
  证明: fun _ hx => ⟨hx.1, fun p hp => hst hx.2 p hp⟩
-/
@[gcongr] lemma factoredNumbers_mono {s t : Finset Nat} (hst : s <= t) :
    factoredNumbers s subseteq factoredNumbers t :=
fun _ hx => ⟨hx.1, fun p hp => hst hx.2 p hp⟩

/--
lemma `factoredNumbers_compl` / 引理 `factoredNumbers_compl`

English:
lemma factoredNumbers_compl
  given: {N : Nat} {s : Finset Nat} (h : primesBelow N <= s)
  proof: by
  intro n hn
  simp only [Set.mem_compl_iff, mem_factoredNumbers, Set.mem_sdiff, ne_eq, not_and, not_forall,
    exists_prop, Set.mem_singleton_iff] at hn
  simp only [Set.mem_ofPred_eq]
  obtain ⟨p, hp₁, hp₂⟩ := hn.1 hn.2
  have : N <= p := by
    contrapose! hp₂
exact h mem_primesBelow.mpr ⟨hp₂

中文:
引理 factoredNumbers_compl
  条件: {N : 自然数} {s : Finset 自然数} (h : primesBelow N <= s)
  证明: by
  intro n hn
  simp only [Set.mem_compl_iff, mem_factoredNumbers, Set.mem_sdiff, ne_eq, not_and, not_forall,
    exists_prop, Set.mem_singleton_iff] at hn
  simp only [Set.mem_ofPred_eq]
  obtain ⟨p, hp₁, hp₂⟩ := hn.1 hn.2
  have : N <= p := by
    contrapose! hp₂
exact h mem_primesBelow.mpr ⟨hp₂

Depends on / 依赖: Set.mem_compl_iff, Set.mem_ofPred_eq, Set.mem_sdiff, Set.mem_singleton_iff, contrapose, exists_prop, le_of_mem_primeFactorsList, mem_compl_iff, mem_factoredNumbers, mem_ofPred_eq, mem_primesBelow, mem_primesBelow.mpr, mem_sdiff, mem_singleton_iff, ne_eq, not_and, not_forall, prime_of_mem_primeFactorsList, this.trans
-/
lemma factoredNumbers_compl {N : Nat} {s : Finset Nat} (h : primesBelow N <= s) :
    (factoredNumbers s)ᶜ \ {0} subseteq {n | N <= n} := by
  intro n hn
  simp only [Set.mem_compl_iff, mem_factoredNumbers, Set.mem_sdiff, ne_eq, not_and, not_forall,
    exists_prop, Set.mem_singleton_iff] at hn
  simp only [Set.mem_ofPred_eq]
  obtain ⟨p, hp₁, hp₂⟩ := hn.1 hn.2
  have : N <= p := by
    contrapose! hp₂
exact h mem_primesBelow.mpr ⟨hp₂, prime_of_mem_primeFactorsList hp₁⟩
exact this.trans le_of_mem_primeFactorsList hp₁

/--
lemma `pow_mul_mem_factoredNumbers` / 引理 `pow_mul_mem_factoredNumbers`

English:
lemma pow_mul_mem_factoredNumbers
  statement: {s : Finset Nat} {p n : Nat} (hp : p.Prime) (e : Nat)
  proof: by
  have hp' := pow_ne_zero e hp.ne_zero
  refine ⟨mul_ne_zero hp' hn.1, fun q hq => ?_⟩
  rcases (mem_primeFactorsList_mul hp' hn.1).mp hq with H | H
  · rw [mem_primeFactorsList hp'] at H
    rw [(prime_dvd_prime_iff_eq H.1 hp).mp <| H.1.dvd_of_dvd_pow H.2]
    exact Finset.mem_insert_self p s
· 

中文:
引理 pow_mul_mem_factoredNumbers
  结论: {s : Finset 自然数} {p n : 自然数} (hp : p.Prime) (e : 自然数)
  证明: by
  have hp' := pow_ne_zero e hp.ne_zero
  refine ⟨mul_ne_zero hp' hn.1, fun q hq => ?_⟩
  rcases (mem_primeFactorsList_mul hp' hn.1).mp hq with H | H
  · rw [mem_primeFactorsList hp'] at H
    rw [(prime_dvd_prime_iff_eq H.1 hp).mp <| H.1.dvd_of_dvd_pow H.2]
    exact Finset.mem_insert_self p s
· 

Depends on / 依赖: Finset, Finset.mem_insert_of_mem, Finset.mem_insert_self, dvd_of_dvd_pow, hp.ne_zero, mem_insert_of_mem, mem_insert_self, mem_primeFactorsList, mem_primeFactorsList_mul, mul_ne_zero, ne_zero, pow_ne_zero, prime_dvd_prime_iff_eq
-/
lemma pow_mul_mem_factoredNumbers {s : Finset Nat} {p n : Nat} (hp : p.Prime) (e : Nat)
    (hn : n in factoredNumbers s) :
    p ^ e * n in factoredNumbers (insert p s) := by
  have hp' := pow_ne_zero e hp.ne_zero
  refine ⟨mul_ne_zero hp' hn.1, fun q hq => ?_⟩
  rcases (mem_primeFactorsList_mul hp' hn.1).mp hq with H | H
  · rw [mem_primeFactorsList hp'] at H
    rw [(prime_dvd_prime_iff_eq H.1 hp).mp <| H.1.dvd_of_dvd_pow H.2]
    exact Finset.mem_insert_self p s
· exact Finset.mem_insert_of_mem hn.2 _ H

/--
lemma `Prime.factoredNumbers_coprime` / 引理 `Prime.factoredNumbers_coprime`

English:
lemma Prime.factoredNumbers_coprime
  statement: {s : Finset Nat} {p n : Nat} (hp : p.Prime) (hs : p ∉ s)
  proof: by
  rw [hp.coprime_iff_not_dvd]; rw [← mem_primeFactorsList_iff_dvd hn.1 hp]
exact fun H => hs hn.2 p H

中文:
引理 Prime.factoredNumbers_coprime
  结论: {s : Finset 自然数} {p n : 自然数} (hp : p.Prime) (hs : p ∉ s)
  证明: by
  rw [hp.coprime_iff_not_dvd]; rw [← mem_primeFactorsList_iff_dvd hn.1 hp]
exact fun H => hs hn.2 p H

Depends on / 依赖: coprime_iff_not_dvd, hp.coprime_iff_not_dvd, mem_primeFactorsList_iff_dvd
-/
lemma Prime.factoredNumbers_coprime {s : Finset Nat} {p n : Nat} (hp : p.Prime) (hs : p ∉ s)
    (hn : n in factoredNumbers s) :
    Nat.Coprime p n := by
  rw [hp.coprime_iff_not_dvd]; rw [← mem_primeFactorsList_iff_dvd hn.1 hp]
exact fun H => hs hn.2 p H

/--
lemma `factoredNumbers.map_prime_pow_mul` / 引理 `factoredNumbers.map_prime_pow_mul`

English:
lemma factoredNumbers.map_prime_pow_mul
  statement: {F : Type*} [Mul F] {f : Nat -> F}
  proof: hmul Coprime.pow_left _ hp.factoredNumbers_coprime hs Subtype.mem m

中文:
引理 factoredNumbers.map_prime_pow_mul
  结论: {F : 类型} [Mul F] {f : 自然数 -> F}
  证明: hmul Coprime.pow_left _ hp.factoredNumbers_coprime hs Subtype.mem m

Depends on / 依赖: Coprime, Coprime.pow_left, Subtype, Subtype.mem, factoredNumbers_coprime, hp.factoredNumbers_coprime, pow_left
-/
lemma factoredNumbers.map_prime_pow_mul {F : Type*} [Mul F] {f : Nat -> F}
    (hmul : forall {m n}, Coprime m n -> f (m * n) = f m * f n) {s : Finset Nat} {p : Nat}
    (hp : p.Prime) (hs : p ∉ s) (e : Nat) {m : factoredNumbers s} :
    f (p ^ e * m) = f (p ^ e) * f m :=
hmul Coprime.pow_left _ hp.factoredNumbers_coprime hs Subtype.mem m

set_option backward.isDefEq.respectTransparency false in
open List Perm in
/--
Definition of `equivProdNatFactoredNumbers` / `equivProdNatFactoredNumbers` 的定义

English:
definition equivProdNatFactoredNumbers
  signature: {s : Finset Nat} {p : Nat} (hp : p.Prime) (hs : p ∉ s)
  body: fun ⟨e, n⟩ => ⟨p ^ e * n, pow_mul_mem_factoredNumbers hp e n.2⟩
  invFun := fun ⟨m, _⟩ => (m.factorization p,
                            ⟨(m.primeFactorsList.filter (· in s)).prod, prod_mem_factoredNumbers ..⟩)
  left_inv := by
    rintro ⟨e, m, hm₀, hm⟩
    have hpm : ¬ p ∣ m := by grind [mem_prim

中文:
定义 equivProdNatFactoredNumbers
  签名: {s : Finset 自然数} {p : 自然数} (hp : p.Prime) (hs : p ∉ s)
  定义体: fun ⟨e, n⟩ => ⟨p ^ e * n, pow_mul_mem_factoredNumbers hp e n.2⟩
  invFun := fun ⟨m, _⟩ => (m.factorization p,
                            ⟨(m.primeFactorsList.filter (· in s)).prod, prod_mem_factoredNumbers ..⟩)
  left_inv := by
    rintro ⟨e, m, hm₀, hm⟩
    have hpm : ¬ p ∣ m := by grind [mem_prim

Depends on / 依赖: pow_mul_mem_factoredNumbers
-/
def equivProdNatFactoredNumbers {s : Finset Nat} {p : Nat} (hp : p.Prime) (hs : p ∉ s) :
    Nat × factoredNumbers s ≃ factoredNumbers (insert p s) where
  toFun := fun ⟨e, n⟩ => ⟨p ^ e * n, pow_mul_mem_factoredNumbers hp e n.2⟩
  invFun := fun ⟨m, _⟩ => (m.factorization p,
                            ⟨(m.primeFactorsList.filter (· in s)).prod, prod_mem_factoredNumbers ..⟩)
  left_inv := by
    rintro ⟨e, m, hm₀, hm⟩
    have hpm : ¬ p ∣ m := by grind [mem_primeFactorsList]
    simp only [Prod.mk.injEq, Subtype.mk.injEq]
    constructor
    · rw [factorization_mul (pow_ne_zero e hp.ne_zero) hm₀, Finsupp.add_apply,
        factorization_pow_self hp, factorization_eq_zero_of_not_dvd hpm, add_zero]
    · conv_rhs => rw [← prod_primeFactorsList hm₀]
refine prod_eq
        (filter _ <| perm_primeFactorsList_mul (pow_ne_zero e hp.ne_zero) hm₀).trans ?_
      rw [filter_append]; rw [hp.primeFactorsList_pow]; rw [filter_eq_nil_iff.mpr <| by grind]; rw [nil_append]; rw [filter_eq_self.mpr by grind]
  right_inv := by
    rintro ⟨m, hm₀, hm⟩
    rw [Subtype.mk.injEq]; rw [← primeFactorsList_count_eq]; rw [← prod_replicate]; rw [← prod_append]
    conv_rhs => rw [← prod_primeFactorsList hm₀]
    have : m.primeFactorsList.filter (· = p) = m.primeFactorsList.filter (· ∉ s) :=
filter_congr by grind
refine prod_eq (filter_eq p).symm ▸ this ▸ perm_append_comm.trans ?_
    simp only [decide_not]
    exact filter_append_perm (· in s) (primeFactorsList m)

@[simp]
/--
lemma `equivProdNatFactoredNumbers_apply` / 引理 `equivProdNatFactoredNumbers_apply`

English:
lemma equivProdNatFactoredNumbers_apply
  statement: {s : Finset Nat} {p e m : Nat} (hp : p.Prime) (hs : p ∉ s)
  proof: rfl

@[simp]

中文:
引理 equivProdNatFactoredNumbers_apply
  结论: {s : Finset 自然数} {p e m : 自然数} (hp : p.Prime) (hs : p ∉ s)
  证明: rfl

@[simp]
-/
lemma equivProdNatFactoredNumbers_apply {s : Finset Nat} {p e m : Nat} (hp : p.Prime) (hs : p ∉ s)
    (hm : m in factoredNumbers s) :
    equivProdNatFactoredNumbers hp hs (e, ⟨m, hm⟩) = p ^ e * m := rfl

@[simp]
/--
lemma `equivProdNatFactoredNumbers_apply'` / 引理 `equivProdNatFactoredNumbers_apply'`

English:
lemma equivProdNatFactoredNumbers_apply'
  statement: {s : Finset Nat} {p : Nat} (hp : p.Prime) (hs : p ∉ s)
  proof: rfl

中文:
引理 equivProdNatFactoredNumbers_apply'
  结论: {s : Finset 自然数} {p : 自然数} (hp : p.Prime) (hs : p ∉ s)
  证明: rfl
-/
lemma equivProdNatFactoredNumbers_apply' {s : Finset Nat} {p : Nat} (hp : p.Prime) (hs : p ∉ s)
    (x : Nat × factoredNumbers s) :
    equivProdNatFactoredNumbers hp hs x = p ^ x.1 * x.2 := rfl


/-!
### `n`-smooth numbers
-/

/--
Definition of `smoothNumbers` / `smoothNumbers` 的定义

English:
definition smoothNumbers
  signature: (n : Nat)
  body: {m | m != 0 ∧ forall p in primeFactorsList m, p < n}

中文:
定义 smoothNumbers
  签名: (n : 自然数)
  定义体: {m | m != 0 ∧ forall p in primeFactorsList m, p < n}

Depends on / 依赖: primeFactorsList
-/
def smoothNumbers (n : Nat) : Set Nat := {m | m != 0 ∧ forall p in primeFactorsList m, p < n}

/--
lemma `mem_smoothNumbers` / 引理 `mem_smoothNumbers`

English:
lemma mem_smoothNumbers
  given: {n m : Nat}
  statement: m in smoothNumbers n ↔ m != 0 ∧ forall p in primeFactorsList m, p < n
  proof: Iff.rfl

中文:
引理 mem_smoothNumbers
  条件: {n m : 自然数}
  结论: m in smoothNumbers n ↔ m != 0 ∧ 对任意 p in primeFactorsList m, p < n
  证明: Iff.rfl

Depends on / 依赖: Iff.rfl
-/
lemma mem_smoothNumbers {n m : Nat} : m in smoothNumbers n ↔ m != 0 ∧ forall p in primeFactorsList m, p < n :=
  Iff.rfl

/--
lemma `smoothNumbers_eq_factoredNumbers` / 引理 `smoothNumbers_eq_factoredNumbers`

English:
lemma smoothNumbers_eq_factoredNumbers
  given: (n : Nat)
  proof: by
  simp only [smoothNumbers, ne_eq, mem_primeFactorsList', and_imp, factoredNumbers,
    Finset.mem_range]

中文:
引理 smoothNumbers_eq_factoredNumbers
  条件: (n : 自然数)
  证明: by
  simp only [smoothNumbers, ne_eq, mem_primeFactorsList', and_imp, factoredNumbers,
    Finset.mem_range]

Depends on / 依赖: Finset, Finset.mem_range, and_imp, factoredNumbers, mem_primeFactorsList, mem_range, ne_eq, smoothNumbers
-/
lemma smoothNumbers_eq_factoredNumbers (n : Nat) :
    smoothNumbers n = factoredNumbers (Finset.range n) := by
  simp only [smoothNumbers, ne_eq, mem_primeFactorsList', and_imp, factoredNumbers,
    Finset.mem_range]

/--
lemma `smoothNumbers_eq_factoredNumbers_primesBelow` / 引理 `smoothNumbers_eq_factoredNumbers_primesBelow`

English:
lemma smoothNumbers_eq_factoredNumbers_primesBelow
  given: (n : Nat)
  proof: by
  rw [smoothNumbers_eq_factoredNumbers]
refine Set.Subset.antisymm (fun m hm => ?_) factoredNumbers_mono Finset.mem_of_mem_filter
  simp_rw [mem_factoredNumbers'] at hm ⊢
exact fun p hp hp' => mem_primesBelow.mpr ⟨Finset.mem_range.mp hm p hp hp', hp⟩

中文:
引理 smoothNumbers_eq_factoredNumbers_primesBelow
  条件: (n : 自然数)
  证明: by
  rw [smoothNumbers_eq_factoredNumbers]
refine Set.Subset.antisymm (fun m hm => ?_) factoredNumbers_mono Finset.mem_of_mem_filter
  simp_rw [mem_factoredNumbers'] at hm ⊢
exact fun p hp hp' => mem_primesBelow.mpr ⟨Finset.mem_range.mp hm p hp hp', hp⟩

Depends on / 依赖: Finset, Finset.mem_of_mem_filter, Finset.mem_range.mp, Set.Subset.antisymm, Subset, antisymm, factoredNumbers_mono, mem_factoredNumbers, mem_of_mem_filter, mem_primesBelow, mem_primesBelow.mpr, mem_range, simp_rw, smoothNumbers_eq_factoredNumbers
-/
lemma smoothNumbers_eq_factoredNumbers_primesBelow (n : Nat) :
    smoothNumbers n = factoredNumbers n.primesBelow := by
  rw [smoothNumbers_eq_factoredNumbers]
refine Set.Subset.antisymm (fun m hm => ?_) factoredNumbers_mono Finset.mem_of_mem_filter
  simp_rw [mem_factoredNumbers'] at hm ⊢
exact fun p hp hp' => mem_primesBelow.mpr ⟨Finset.mem_range.mp hm p hp hp', hp⟩

/-- Membership in `Nat.smoothNumbers n` is decidable. -/
instance (n : Nat) : DecidablePred (· in smoothNumbers n) :=
inferInstanceAs DecidablePred fun x => x in {m | m != 0 ∧ forall p in primeFactorsList m, p < n}

/--
lemma `mem_smoothNumbers_of_dvd` / 引理 `mem_smoothNumbers_of_dvd`

English:
lemma mem_smoothNumbers_of_dvd
  given: {n m k : Nat} (h : m in smoothNumbers n) (h' : k ∣ m)
  proof: by
  simp only [smoothNumbers_eq_factoredNumbers] at h ⊢
  exact mem_factoredNumbers_of_dvd h h'

中文:
引理 mem_smoothNumbers_of_dvd
  条件: {n m k : 自然数} (h : m in smoothNumbers n) (h' : k ∣ m)
  证明: by
  simp only [smoothNumbers_eq_factoredNumbers] at h ⊢
  exact mem_factoredNumbers_of_dvd h h'

Depends on / 依赖: mem_factoredNumbers_of_dvd, smoothNumbers_eq_factoredNumbers
-/
lemma mem_smoothNumbers_of_dvd {n m k : Nat} (h : m in smoothNumbers n) (h' : k ∣ m) :
    k in smoothNumbers n := by
  simp only [smoothNumbers_eq_factoredNumbers] at h ⊢
  exact mem_factoredNumbers_of_dvd h h'

/--
lemma `mem_smoothNumbers_iff_forall_le` / 引理 `mem_smoothNumbers_iff_forall_le`

English:
lemma mem_smoothNumbers_iff_forall_le
  given: {n m : Nat}
  proof: by
  simp only [smoothNumbers_eq_factoredNumbers, mem_factoredNumbers_iff_forall_le, Finset.mem_range]

中文:
引理 mem_smoothNumbers_iff_forall_le
  条件: {n m : 自然数}
  证明: by
  simp only [smoothNumbers_eq_factoredNumbers, mem_factoredNumbers_iff_forall_le, Finset.mem_range]

Depends on / 依赖: Finset, Finset.mem_range, mem_factoredNumbers_iff_forall_le, mem_range, smoothNumbers_eq_factoredNumbers
-/
lemma mem_smoothNumbers_iff_forall_le {n m : Nat} :
    m in smoothNumbers n ↔ m != 0 ∧ forall p <= m, p.Prime -> p ∣ m -> p < n := by
  simp only [smoothNumbers_eq_factoredNumbers, mem_factoredNumbers_iff_forall_le, Finset.mem_range]

/--
lemma `mem_smoothNumbers'` / 引理 `mem_smoothNumbers'`

English:
lemma mem_smoothNumbers'
  given: {n m : Nat}
  statement: m in smoothNumbers n ↔ forall p, p.Prime -> p ∣ m -> p < n
  proof: by
  simp only [smoothNumbers_eq_factoredNumbers, mem_factoredNumbers', Finset.mem_range]

中文:
引理 mem_smoothNumbers'
  条件: {n m : 自然数}
  结论: m in smoothNumbers n ↔ 对任意 p, p.Prime -> p ∣ m -> p < n
  证明: by
  simp only [smoothNumbers_eq_factoredNumbers, mem_factoredNumbers', Finset.mem_range]

Depends on / 依赖: Finset, Finset.mem_range, mem_factoredNumbers, mem_range, smoothNumbers_eq_factoredNumbers
-/
lemma mem_smoothNumbers' {n m : Nat} : m in smoothNumbers n ↔ forall p, p.Prime -> p ∣ m -> p < n := by
  simp only [smoothNumbers_eq_factoredNumbers, mem_factoredNumbers', Finset.mem_range]

/--
lemma `primeFactors_subset_of_mem_smoothNumbers` / 引理 `primeFactors_subset_of_mem_smoothNumbers`

English:
lemma primeFactors_subset_of_mem_smoothNumbers
  given: {m n : Nat} (hms : m in n.smoothNumbers)
  proof: primeFactors_subset_of_mem_factoredNumbers
    smoothNumbers_eq_factoredNumbers_primesBelow n ▸ hms

中文:
引理 primeFactors_subset_of_mem_smoothNumbers
  条件: {m n : 自然数} (hms : m in n.smoothNumbers)
  证明: primeFactors_subset_of_mem_factoredNumbers
    smoothNumbers_eq_factoredNumbers_primesBelow n ▸ hms

Depends on / 依赖: primeFactors_subset_of_mem_factoredNumbers, smoothNumbers_eq_factoredNumbers_primesBelow
-/
lemma primeFactors_subset_of_mem_smoothNumbers {m n : Nat} (hms : m in n.smoothNumbers) :
    m.primeFactors subseteq n.primesBelow :=
primeFactors_subset_of_mem_factoredNumbers
    smoothNumbers_eq_factoredNumbers_primesBelow n ▸ hms

/--
lemma `mem_smoothNumbers_of_primeFactors_subset` / 引理 `mem_smoothNumbers_of_primeFactors_subset`

English:
lemma mem_smoothNumbers_of_primeFactors_subset
  statement: {m n : Nat} (hm : m != 0)
  proof: smoothNumbers_eq_factoredNumbers n ▸ mem_factoredNumbers_of_primeFactors_subset hm hp

中文:
引理 mem_smoothNumbers_of_primeFactors_subset
  结论: {m n : 自然数} (hm : m != 0)
  证明: smoothNumbers_eq_factoredNumbers n ▸ mem_factoredNumbers_of_primeFactors_subset hm hp

Depends on / 依赖: mem_factoredNumbers_of_primeFactors_subset, smoothNumbers_eq_factoredNumbers
-/
lemma mem_smoothNumbers_of_primeFactors_subset {m n : Nat} (hm : m != 0)
    (hp : m.primeFactors subseteq Finset.range n) : m in n.smoothNumbers :=
  smoothNumbers_eq_factoredNumbers n ▸ mem_factoredNumbers_of_primeFactors_subset hm hp

/--
lemma `mem_smoothNumbers_iff_primeFactors_subset` / 引理 `mem_smoothNumbers_iff_primeFactors_subset`

English:
lemma mem_smoothNumbers_iff_primeFactors_subset
  given: {m n : Nat}
  proof: ⟨fun h => ⟨h.1, primeFactors_subset_of_mem_smoothNumbers h⟩,
fun h => mem_smoothNumbers_of_primeFactors_subset h.1 h.2.trans Finset.filter_subset ..⟩

中文:
引理 mem_smoothNumbers_iff_primeFactors_subset
  条件: {m n : 自然数}
  证明: ⟨fun h => ⟨h.1, primeFactors_subset_of_mem_smoothNumbers h⟩,
fun h => mem_smoothNumbers_of_primeFactors_subset h.1 h.2.trans Finset.filter_subset ..⟩

Depends on / 依赖: Finset, Finset.filter_subset, filter_subset, mem_smoothNumbers_of_primeFactors_subset, primeFactors_subset_of_mem_smoothNumbers
-/
lemma mem_smoothNumbers_iff_primeFactors_subset {m n : Nat} :
    m in n.smoothNumbers ↔ m != 0 ∧ m.primeFactors subseteq n.primesBelow :=
  ⟨fun h => ⟨h.1, primeFactors_subset_of_mem_smoothNumbers h⟩,
fun h => mem_smoothNumbers_of_primeFactors_subset h.1 h.2.trans Finset.filter_subset ..⟩

/--
lemma `ne_zero_of_mem_smoothNumbers` / 引理 `ne_zero_of_mem_smoothNumbers`

English:
lemma ne_zero_of_mem_smoothNumbers
  given: {n m : Nat} (h : m in smoothNumbers n)
  statement: m != 0
  proof: h.1

@[simp]

中文:
引理 ne_zero_of_mem_smoothNumbers
  条件: {n m : 自然数} (h : m in smoothNumbers n)
  结论: m != 0
  证明: h.1

@[simp]
-/
lemma ne_zero_of_mem_smoothNumbers {n m : Nat} (h : m in smoothNumbers n) : m != 0 := h.1

@[simp]
/--
lemma `smoothNumbers_zero` / 引理 `smoothNumbers_zero`

English:
lemma smoothNumbers_zero
  statement: smoothNumbers 0 = {1}
  proof: by
  simp only [smoothNumbers_eq_factoredNumbers, Finset.range_zero, factoredNumbers_empty]

中文:
引理 smoothNumbers_zero
  结论: smoothNumbers 0 = {1}
  证明: by
  simp only [smoothNumbers_eq_factoredNumbers, Finset.range_zero, factoredNumbers_empty]

Depends on / 依赖: Finset, Finset.range_zero, factoredNumbers_empty, range_zero, smoothNumbers_eq_factoredNumbers
-/
lemma smoothNumbers_zero : smoothNumbers 0 = {1} := by
  simp only [smoothNumbers_eq_factoredNumbers, Finset.range_zero, factoredNumbers_empty]

/--
theorem `mul_mem_smoothNumbers` / 定理 `mul_mem_smoothNumbers`

English:
theorem mul_mem_smoothNumbers
  statement: {m₁ m₂ n : Nat}
  proof: by
  rw [smoothNumbers_eq_factoredNumbers] at hm1 hm2 ⊢
  exact mul_mem_factoredNumbers hm1 hm2

中文:
定理 mul_mem_smoothNumbers
  结论: {m₁ m₂ n : 自然数}
  证明: by
  rw [smoothNumbers_eq_factoredNumbers] at hm1 hm2 ⊢
  exact mul_mem_factoredNumbers hm1 hm2

Depends on / 依赖: mul_mem_factoredNumbers, smoothNumbers_eq_factoredNumbers
-/
theorem mul_mem_smoothNumbers {m₁ m₂ n : Nat}
    (hm1 : m₁ in n.smoothNumbers) (hm2 : m₂ in n.smoothNumbers) : m₁ * m₂ in n.smoothNumbers := by
  rw [smoothNumbers_eq_factoredNumbers] at hm1 hm2 ⊢
  exact mul_mem_factoredNumbers hm1 hm2

/--
lemma `prod_mem_smoothNumbers` / 引理 `prod_mem_smoothNumbers`

English:
lemma prod_mem_smoothNumbers
  given: (n N : Nat)
  proof: by
  simp only [smoothNumbers_eq_factoredNumbers, ← Finset.mem_range, prod_mem_factoredNumbers]

中文:
引理 prod_mem_smoothNumbers
  条件: (n N : 自然数)
  证明: by
  simp only [smoothNumbers_eq_factoredNumbers, ← Finset.mem_range, prod_mem_factoredNumbers]

Depends on / 依赖: Finset, Finset.mem_range, mem_range, prod_mem_factoredNumbers, smoothNumbers_eq_factoredNumbers
-/
lemma prod_mem_smoothNumbers (n N : Nat) :
    (n.primeFactorsList.filter (· < N)).prod in smoothNumbers N := by
  simp only [smoothNumbers_eq_factoredNumbers, ← Finset.mem_range, prod_mem_factoredNumbers]

/--
lemma `smoothNumbers_succ` / 引理 `smoothNumbers_succ`

English:
lemma smoothNumbers_succ
  given: {N : Nat} (hN : ¬ N.Prime)
  statement: (N + 1).smoothNumbers = N.smoothNumbers
  proof: by
  simp only [smoothNumbers_eq_factoredNumbers, Finset.range_add_one, factoredNumbers_insert _ hN]

中文:
引理 smoothNumbers_succ
  条件: {N : 自然数} (hN : ¬ N.Prime)
  结论: (N + 1).smoothNumbers = N.smoothNumbers
  证明: by
  simp only [smoothNumbers_eq_factoredNumbers, Finset.range_add_one, factoredNumbers_insert _ hN]

Depends on / 依赖: Finset, Finset.range_add_one, factoredNumbers_insert, range_add_one, smoothNumbers_eq_factoredNumbers
-/
lemma smoothNumbers_succ {N : Nat} (hN : ¬ N.Prime) : (N + 1).smoothNumbers = N.smoothNumbers := by
  simp only [smoothNumbers_eq_factoredNumbers, Finset.range_add_one, factoredNumbers_insert _ hN]

/--
lemma `smoothNumbers_one` / 引理 `smoothNumbers_one`

English:
lemma smoothNumbers_one
  statement: smoothNumbers 1 = {1}
  proof: by
  simp +decide only [not_false_eq_true, smoothNumbers_succ, smoothNumbers_zero]

中文:
引理 smoothNumbers_one
  结论: smoothNumbers 1 = {1}
  证明: by
  simp +decide only [not_false_eq_true, smoothNumbers_succ, smoothNumbers_zero]
-/
@[simp] lemma smoothNumbers_one : smoothNumbers 1 = {1} := by
  simp +decide only [not_false_eq_true, smoothNumbers_succ, smoothNumbers_zero]

/--
lemma `smoothNumbers_mono` / 引理 `smoothNumbers_mono`

English:
lemma smoothNumbers_mono
  given: {N M : Nat} (hNM : N <= M)
  statement: N.smoothNumbers subseteq M.smoothNumbers
  proof: fun _ hx => ⟨hx.1, fun p hp => (hx.2 p hp).trans_le hNM⟩

中文:
引理 smoothNumbers_mono
  条件: {N M : 自然数} (hNM : N <= M)
  结论: N.smoothNumbers subseteq M.smoothNumbers
  证明: fun _ hx => ⟨hx.1, fun p hp => (hx.2 p hp).trans_le hNM⟩
-/
@[gcongr] lemma smoothNumbers_mono {N M : Nat} (hNM : N <= M) : N.smoothNumbers subseteq M.smoothNumbers :=
  fun _ hx => ⟨hx.1, fun p hp => (hx.2 p hp).trans_le hNM⟩

/--
lemma `mem_smoothNumbers_of_lt` / 引理 `mem_smoothNumbers_of_lt`

English:
lemma mem_smoothNumbers_of_lt
  given: {m n : Nat} (hm : 0 < m) (hmn : m < n)
  statement: m in n.smoothNumbers
  proof: smoothNumbers_eq_factoredNumbers _ ▸ ⟨ne_zero_of_lt hm,
fun _ h => Finset.mem_range.mpr lt_of_le_of_lt (le_of_mem_primeFactorsList h) hmn⟩

中文:
引理 mem_smoothNumbers_of_lt
  条件: {m n : 自然数} (hm : 0 < m) (hmn : m < n)
  结论: m in n.smoothNumbers
  证明: smoothNumbers_eq_factoredNumbers _ ▸ ⟨ne_zero_of_lt hm,
fun _ h => Finset.mem_range.mpr lt_of_le_of_lt (le_of_mem_primeFactorsList h) hmn⟩

Depends on / 依赖: Finset, Finset.mem_range.mpr, le_of_mem_primeFactorsList, lt_of_le_of_lt, mem_range, ne_zero_of_lt, smoothNumbers_eq_factoredNumbers
-/
lemma mem_smoothNumbers_of_lt {m n : Nat} (hm : 0 < m) (hmn : m < n) : m in n.smoothNumbers :=
  smoothNumbers_eq_factoredNumbers _ ▸ ⟨ne_zero_of_lt hm,
fun _ h => Finset.mem_range.mpr lt_of_le_of_lt (le_of_mem_primeFactorsList h) hmn⟩

/--
lemma `smoothNumbers_compl` / 引理 `smoothNumbers_compl`

English:
lemma smoothNumbers_compl
  given: (N : Nat)
  statement: (N.smoothNumbers)ᶜ \ {0} subseteq {n | N <= n}
  proof: by
  simpa only [smoothNumbers_eq_factoredNumbers]
using factoredNumbers_compl Finset.filter_subset _ (Finset.range N)

中文:
引理 smoothNumbers_compl
  条件: (N : 自然数)
  结论: (N.smoothNumbers)ᶜ \ {0} subseteq {n | N <= n}
  证明: by
  simpa only [smoothNumbers_eq_factoredNumbers]
using factoredNumbers_compl Finset.filter_subset _ (Finset.range N)

Depends on / 依赖: Finset, Finset.filter_subset, Finset.range, factoredNumbers_compl, filter_subset, smoothNumbers_eq_factoredNumbers
-/
lemma smoothNumbers_compl (N : Nat) : (N.smoothNumbers)ᶜ \ {0} subseteq {n | N <= n} := by
  simpa only [smoothNumbers_eq_factoredNumbers]
using factoredNumbers_compl Finset.filter_subset _ (Finset.range N)

/--
lemma `pow_mul_mem_smoothNumbers` / 引理 `pow_mul_mem_smoothNumbers`

English:
lemma pow_mul_mem_smoothNumbers
  given: {p n : Nat} (hp : p != 0) (e : Nat) (hn : n in smoothNumbers p)
  proof: by
  -- This cannot be easily reduced to `pow_mul_mem_factoredNumbers`, as there `p.Prime` is needed.
  have : NoZeroDivisors Nat := inferInstance -- this is needed twice --> speed-up
  have hp' := pow_ne_zero e hp
  refine ⟨mul_ne_zero hp' hn.1, fun q hq => ?_⟩
  rcases (mem_primeFactorsList_mul hp

中文:
引理 pow_mul_mem_smoothNumbers
  条件: {p n : 自然数} (hp : p != 0) (e : 自然数) (hn : n in smoothNumbers p)
  证明: by
  -- This cannot be easily reduced to `pow_mul_mem_factoredNumbers`, as there `p.Prime` is needed.
  have : NoZeroDivisors Nat := inferInstance -- this is needed twice --> speed-up
  have hp' := pow_ne_zero e hp
  refine ⟨mul_ne_zero hp' hn.1, fun q hq => ?_⟩
  rcases (mem_primeFactorsList_mul hp
-/
lemma pow_mul_mem_smoothNumbers {p n : Nat} (hp : p != 0) (e : Nat) (hn : n in smoothNumbers p) :
    p ^ e * n in smoothNumbers (succ p) := by
  -- This cannot be easily reduced to `pow_mul_mem_factoredNumbers`, as there `p.Prime` is needed.
  have : NoZeroDivisors Nat := inferInstance -- this is needed twice --> speed-up
  have hp' := pow_ne_zero e hp
  refine ⟨mul_ne_zero hp' hn.1, fun q hq => ?_⟩
  rcases (mem_primeFactorsList_mul hp' hn.1).mp hq with H | H
  · rw [mem_primeFactorsList hp'] at H
exact Nat.lt_succ_of_le le_of_dvd hp.bot_lt H.1.dvd_of_dvd_pow H.2
· exact (hn.2 q H).trans lt_succ_self p

/--
lemma `Prime.smoothNumbers_coprime` / 引理 `Prime.smoothNumbers_coprime`

English:
lemma Prime.smoothNumbers_coprime
  given: {p n : Nat} (hp : p.Prime) (hn : n in smoothNumbers p)
  proof: by
  simp only [smoothNumbers_eq_factoredNumbers] at hn
  exact hp.factoredNumbers_coprime Finset.notMem_range_self hn

中文:
引理 Prime.smoothNumbers_coprime
  条件: {p n : 自然数} (hp : p.Prime) (hn : n in smoothNumbers p)
  证明: by
  simp only [smoothNumbers_eq_factoredNumbers] at hn
  exact hp.factoredNumbers_coprime Finset.notMem_range_self hn

Depends on / 依赖: Finset, Finset.notMem_range_self, factoredNumbers_coprime, hp.factoredNumbers_coprime, notMem_range_self, smoothNumbers_eq_factoredNumbers
-/
lemma Prime.smoothNumbers_coprime {p n : Nat} (hp : p.Prime) (hn : n in smoothNumbers p) :
    Nat.Coprime p n := by
  simp only [smoothNumbers_eq_factoredNumbers] at hn
  exact hp.factoredNumbers_coprime Finset.notMem_range_self hn

/--
lemma `map_prime_pow_mul` / 引理 `map_prime_pow_mul`

English:
lemma map_prime_pow_mul
  statement: {F : Type*} [Mul F] {f : Nat -> F}
  proof: hmul Coprime.pow_left _ hp.smoothNumbers_coprime Subtype.mem m

中文:
引理 map_prime_pow_mul
  结论: {F : 类型} [Mul F] {f : 自然数 -> F}
  证明: hmul Coprime.pow_left _ hp.smoothNumbers_coprime Subtype.mem m

Depends on / 依赖: Coprime, Coprime.pow_left, Subtype, Subtype.mem, hp.smoothNumbers_coprime, pow_left, smoothNumbers_coprime
-/
lemma map_prime_pow_mul {F : Type*} [Mul F] {f : Nat -> F}
    (hmul : forall {m n}, Nat.Coprime m n -> f (m * n) = f m * f n) {p : Nat} (hp : p.Prime) (e : Nat)
    {m : p.smoothNumbers} :
    f (p ^ e * m) = f (p ^ e) * f m :=
hmul Coprime.pow_left _ hp.smoothNumbers_coprime Subtype.mem m

open List Perm Equiv in
/--
Definition of `equivProdNatSmoothNumbers` / `equivProdNatSmoothNumbers` 的定义

English:
definition equivProdNatSmoothNumbers
  signature: {p : Nat} (hp : p.Prime)
  body: ((prodCongrRight fun _ => setCongr <| smoothNumbers_eq_factoredNumbers p).trans <|
    equivProdNatFactoredNumbers hp Finset.notMem_range_self).trans <|
setCongr (smoothNumbers_eq_factoredNumbers (p + 1)) ▸ Finset.range_add_one ▸ rfl

@[simp]

中文:
定义 equivProdNatSmoothNumbers
  签名: {p : 自然数} (hp : p.Prime)
  定义体: ((prodCongrRight fun _ => setCongr <| smoothNumbers_eq_factoredNumbers p).trans <|
    equivProdNatFactoredNumbers hp Finset.notMem_range_self).trans <|
setCongr (smoothNumbers_eq_factoredNumbers (p + 1)) ▸ Finset.range_add_one ▸ rfl

@[simp]

Depends on / 依赖: Finset, Finset.notMem_range_self, Finset.range_add_one, equivProdNatFactoredNumbers, notMem_range_self, prodCongrRight, range_add_one, setCongr, smoothNumbers_eq_factoredNumbers
-/
def equivProdNatSmoothNumbers {p : Nat} (hp : p.Prime) :
    Nat × smoothNumbers p ≃ smoothNumbers (p + 1) :=
  ((prodCongrRight fun _ => setCongr <| smoothNumbers_eq_factoredNumbers p).trans <|
    equivProdNatFactoredNumbers hp Finset.notMem_range_self).trans <|
setCongr (smoothNumbers_eq_factoredNumbers (p + 1)) ▸ Finset.range_add_one ▸ rfl

@[simp]
/--
lemma `equivProdNatSmoothNumbers_apply` / 引理 `equivProdNatSmoothNumbers_apply`

English:
lemma equivProdNatSmoothNumbers_apply
  given: {p e m : Nat} (hp : p.Prime) (hm : m in p.smoothNumbers)
  proof: rfl

@[simp]

中文:
引理 equivProdNatSmoothNumbers_apply
  条件: {p e m : 自然数} (hp : p.Prime) (hm : m in p.smoothNumbers)
  证明: rfl

@[simp]
-/
lemma equivProdNatSmoothNumbers_apply {p e m : Nat} (hp : p.Prime) (hm : m in p.smoothNumbers) :
    equivProdNatSmoothNumbers hp (e, ⟨m, hm⟩) = p ^ e * m := rfl

@[simp]
/--
lemma `equivProdNatSmoothNumbers_apply'` / 引理 `equivProdNatSmoothNumbers_apply'`

English:
lemma equivProdNatSmoothNumbers_apply'
  given: {p : Nat} (hp : p.Prime) (x : Nat × p.smoothNumbers)
  proof: rfl

中文:
引理 equivProdNatSmoothNumbers_apply'
  条件: {p : 自然数} (hp : p.Prime) (x : 自然数 × p.smoothNumbers)
  证明: rfl
-/
lemma equivProdNatSmoothNumbers_apply' {p : Nat} (hp : p.Prime) (x : Nat × p.smoothNumbers) :
    equivProdNatSmoothNumbers hp x = p ^ x.1 * x.2 := rfl


/-!
### Smooth and rough numbers up to a bound

We consider the sets of smooth and non-smooth ("rough") positive natural numbers `≤ N`
and prove bounds for their sizes.
-/

/--
Definition of `smoothNumbersUpTo` / `smoothNumbersUpTo` 的定义

English:
definition smoothNumbersUpTo
  signature: (N k : Nat)
  body: {n in Finset.range (N + 1) | n in smoothNumbers k}

中文:
定义 smoothNumbersUpTo
  签名: (N k : 自然数)
  定义体: {n in Finset.range (N + 1) | n in smoothNumbers k}

Depends on / 依赖: Finset, Finset.range, smoothNumbers
-/
def smoothNumbersUpTo (N k : Nat) : Finset Nat :=
  {n in Finset.range (N + 1) | n in smoothNumbers k}

/--
lemma `mem_smoothNumbersUpTo` / 引理 `mem_smoothNumbersUpTo`

English:
lemma mem_smoothNumbersUpTo
  given: {N k n : Nat}
  proof: by
  simp [smoothNumbersUpTo]

中文:
引理 mem_smoothNumbersUpTo
  条件: {N k n : 自然数}
  证明: by
  simp [smoothNumbersUpTo]

Depends on / 依赖: smoothNumbersUpTo
-/
lemma mem_smoothNumbersUpTo {N k n : Nat} :
    n in smoothNumbersUpTo N k ↔ n <= N ∧ n in smoothNumbers k := by
  simp [smoothNumbersUpTo]

/--
Definition of `roughNumbersUpTo` / `roughNumbersUpTo` 的定义

English:
definition roughNumbersUpTo
  signature: (N k : Nat)
  body: {n in Finset.range (N + 1) | n != 0 ∧ n ∉ smoothNumbers k}

中文:
定义 roughNumbersUpTo
  签名: (N k : 自然数)
  定义体: {n in Finset.range (N + 1) | n != 0 ∧ n ∉ smoothNumbers k}

Depends on / 依赖: Finset, Finset.range, smoothNumbers
-/
def roughNumbersUpTo (N k : Nat) : Finset Nat :=
  {n in Finset.range (N + 1) | n != 0 ∧ n ∉ smoothNumbers k}

/--
lemma `smoothNumbersUpTo_card_add_roughNumbersUpTo_card` / 引理 `smoothNumbersUpTo_card_add_roughNumbersUpTo_card`

English:
lemma smoothNumbersUpTo_card_add_roughNumbersUpTo_card
  given: (N k : Nat)
  proof: by
  rw [smoothNumbersUpTo]; rw [roughNumbersUpTo]; rw [← Finset.card_union_of_disjoint Finset.disjoint_filter.mpr fun n _ hn₂ h => h.2 hn₂]; rw [Finset.filter_union_right]
  suffices #{x in Finset.range (N + 1) | x != 0} = N by
    have hn' (n) : n in smoothNumbers k ∨ n != 0 ∧ n ∉ smoothNumbers k 

中文:
引理 smoothNumbersUpTo_card_add_roughNumbersUpTo_card
  条件: (N k : 自然数)
  证明: by
  rw [smoothNumbersUpTo]; rw [roughNumbersUpTo]; rw [← Finset.card_union_of_disjoint Finset.disjoint_filter.mpr fun n _ hn₂ h => h.2 hn₂]; rw [Finset.filter_union_right]
  suffices #{x in Finset.range (N + 1) | x != 0} = N by
    have hn' (n) : n in smoothNumbers k ∨ n != 0 ∧ n ∉ smoothNumbers k 

Depends on / 依赖: Finset, Finset.card_union_of_disjoint, Finset.disjoint_filter.mpr, Finset.filter_union_right, Finset.range, Or.elim, card_union_of_disjoint, disjoint_filter, filter_union_right, ne_eq, ne_zero_of_mem_smoothNumbers, not_false_eq_true, or_not, roughNumbersUpTo, smoothNumbers, smoothNumbersUpTo, true_and
-/
lemma smoothNumbersUpTo_card_add_roughNumbersUpTo_card (N k : Nat) :
    #(smoothNumbersUpTo N k) + #(roughNumbersUpTo N k) = N := by
  rw [smoothNumbersUpTo]; rw [roughNumbersUpTo]; rw [← Finset.card_union_of_disjoint Finset.disjoint_filter.mpr fun n _ hn₂ h => h.2 hn₂]; rw [Finset.filter_union_right]
  suffices #{x in Finset.range (N + 1) | x != 0} = N by
    have hn' (n) : n in smoothNumbers k ∨ n != 0 ∧ n ∉ smoothNumbers k ↔ n != 0 := by
      have : n in smoothNumbers k -> n != 0 := ne_zero_of_mem_smoothNumbers
      refine ⟨fun H => Or.elim H this fun H => H.1, fun H => ?_⟩
      simp only [ne_eq, H, not_false_eq_true, true_and, or_not]
    rwa [Finset.filter_congr (s := Finset.range (succ N)) fun n _ => hn' n]
  rw [Finset.filter_ne']; rw [Finset.card_erase_of_mem <| Finset.mem_range_succ_iff.mpr <| zero_le N]
  simp only [Finset.card_range, succ_sub_succ_eq_sub, Nat.sub_zero]

/--
lemma `eq_prod_primes_mul_sq_of_mem_smoothNumbers` / 引理 `eq_prod_primes_mul_sq_of_mem_smoothNumbers`

English:
lemma eq_prod_primes_mul_sq_of_mem_smoothNumbers
  given: {n k : Nat} (h : n in smoothNumbers k)
  proof: by
  obtain ⟨l, m, H₁, H₂⟩ := sq_mul_squarefree n
  have hl : l in smoothNumbers k := mem_smoothNumbers_of_dvd h (Dvd.intro_left (m ^ 2) H₁)
  refine ⟨l.primeFactorsList.toFinset, ?_, m, ?_⟩
  · simp only [toFinset_factors, Finset.mem_powerset]
    refine fun p hp => mem_primesBelow.mpr ⟨?_, (mem_pr

中文:
引理 eq_prod_primes_mul_sq_of_mem_smoothNumbers
  条件: {n k : 自然数} (h : n in smoothNumbers k)
  证明: by
  obtain ⟨l, m, H₁, H₂⟩ := sq_mul_squarefree n
  have hl : l in smoothNumbers k := mem_smoothNumbers_of_dvd h (Dvd.intro_left (m ^ 2) H₁)
  refine ⟨l.primeFactorsList.toFinset, ?_, m, ?_⟩
  · simp only [toFinset_factors, Finset.mem_powerset]
    refine fun p hp => mem_primesBelow.mpr ⟨?_, (mem_pr

Depends on / 依赖: Dvd.intro_left, Finset, Finset.mem_powerset, intro_left, l.primeFactorsList.toFinset, mem_powerset, mem_primeFactors, mem_primeFactors.mp, mem_primesBelow, mem_primesBelow.mpr, mem_smoothNumbers, mem_smoothNumbers_of_dvd, primeFactorsList, prod_primeFactors_of_squarefree, smoothNumbers, sq_mul_squarefree, toFinset, toFinset_factors
-/
lemma eq_prod_primes_mul_sq_of_mem_smoothNumbers {n k : Nat} (h : n in smoothNumbers k) :
    exists s in k.primesBelow.powerset, exists m, n = m ^ 2 * (s.prod id) := by
  obtain ⟨l, m, H₁, H₂⟩ := sq_mul_squarefree n
  have hl : l in smoothNumbers k := mem_smoothNumbers_of_dvd h (Dvd.intro_left (m ^ 2) H₁)
  refine ⟨l.primeFactorsList.toFinset, ?_, m, ?_⟩
  · simp only [toFinset_factors, Finset.mem_powerset]
    refine fun p hp => mem_primesBelow.mpr ⟨?_, (mem_primeFactors.mp hp).1⟩
    rw [mem_primeFactors] at hp
    exact mem_smoothNumbers'.mp hl p hp.1 hp.2.1
  rw [← H₁]
  congr
  simp only [toFinset_factors]
  exact (prod_primeFactors_of_squarefree H₂).symm

/--
lemma `smoothNumbersUpTo_subset_image` / 引理 `smoothNumbersUpTo_subset_image`

English:
lemma smoothNumbersUpTo_subset_image
  given: (N k : Nat)
  proof: by
  intro n hn
  obtain ⟨hn₁, hn₂⟩ := mem_smoothNumbersUpTo.mp hn
  obtain ⟨s, hs, m, hm⟩ := eq_prod_primes_mul_sq_of_mem_smoothNumbers hn₂
  simp only [id_eq, Finset.mem_range, Finset.mem_image,
    Finset.mem_product, Finset.mem_powerset, Finset.mem_erase, Prod.exists]
  refine ⟨s, m, ⟨Finset.mem

中文:
引理 smoothNumbersUpTo_subset_image
  条件: (N k : 自然数)
  证明: by
  intro n hn
  obtain ⟨hn₁, hn₂⟩ := mem_smoothNumbersUpTo.mp hn
  obtain ⟨s, hs, m, hm⟩ := eq_prod_primes_mul_sq_of_mem_smoothNumbers hn₂
  simp only [id_eq, Finset.mem_range, Finset.mem_image,
    Finset.mem_product, Finset.mem_powerset, Finset.mem_erase, Prod.exists]
  refine ⟨s, m, ⟨Finset.mem

Depends on / 依赖: Finset, Finset.mem_erase, Finset.mem_image, Finset.mem_powerset, Finset.mem_powerset.mp, Finset.mem_product, Finset.mem_range, LE.le.tr, Nat.lt_succ_iff, Prod.exists, _root_, _root_.mul_eq_zero, eq_prod_primes_mul_sq_of_mem_smoothNumbers, hm.symm, id_eq, le_sqrt, lt_succ_iff, mem_erase, mem_image, mem_powerset
-/
lemma smoothNumbersUpTo_subset_image (N k : Nat) :
    smoothNumbersUpTo N k subseteq Finset.image (fun (s, m) => m ^ 2 * (s.prod id))
      (k.primesBelow.powerset ×ˢ (Finset.range (N.sqrt + 1)).erase 0) := by
  intro n hn
  obtain ⟨hn₁, hn₂⟩ := mem_smoothNumbersUpTo.mp hn
  obtain ⟨s, hs, m, hm⟩ := eq_prod_primes_mul_sq_of_mem_smoothNumbers hn₂
  simp only [id_eq, Finset.mem_range, Finset.mem_image,
    Finset.mem_product, Finset.mem_powerset, Finset.mem_erase, Prod.exists]
  refine ⟨s, m, ⟨Finset.mem_powerset.mp hs, ?_, ?_⟩, hm.symm⟩
  · have := hm ▸ ne_zero_of_mem_smoothNumbers hn₂
    simp only [ne_eq, _root_.mul_eq_zero, sq_eq_zero_iff, not_or] at this
    exact this.1
  · rw [Nat.lt_succ_iff, le_sqrt']
    refine LE.le.trans ?_ (hm ▸ hn₁)
    nth_rw 1 [← mul_one (m ^ 2)]
    gcongr
    exact Finset.one_le_prod' fun p hp =>
      (prime_of_mem_primesBelow <| Finset.mem_powerset.mp hs hp).one_le

/--
lemma `smoothNumbersUpTo_card_le` / 引理 `smoothNumbersUpTo_card_le`

English:
lemma smoothNumbersUpTo_card_le
  given: (N k : Nat)
  proof: by
convert! (Finset.card_le_card <| smoothNumbersUpTo_subset_image N k).trans Finset.card_image_le
  simp only [Finset.card_product, Finset.card_powerset, Finset.mem_range, zero_lt_succ,
    Finset.card_erase_of_mem, Finset.card_range, succ_sub_succ_eq_sub, Nat.sub_zero]

中文:
引理 smoothNumbersUpTo_card_le
  条件: (N k : 自然数)
  证明: by
convert! (Finset.card_le_card <| smoothNumbersUpTo_subset_image N k).trans Finset.card_image_le
  simp only [Finset.card_product, Finset.card_powerset, Finset.mem_range, zero_lt_succ,
    Finset.card_erase_of_mem, Finset.card_range, succ_sub_succ_eq_sub, Nat.sub_zero]

Depends on / 依赖: Finset, Finset.card_erase_of_mem, Finset.card_image_le, Finset.card_le_card, Finset.card_powerset, Finset.card_product, Finset.card_range, Finset.mem_range, Nat.sub_zero, card_erase_of_mem, card_image_le, card_le_card, card_powerset, card_product, card_range, convert, mem_range, smoothNumbersUpTo_subset_image, sub_zero, succ_sub_succ_eq_sub
-/
lemma smoothNumbersUpTo_card_le (N k : Nat) :
    #(smoothNumbersUpTo N k) <= 2 ^ #k.primesBelow * N.sqrt := by
convert! (Finset.card_le_card <| smoothNumbersUpTo_subset_image N k).trans Finset.card_image_le
  simp only [Finset.card_product, Finset.card_powerset, Finset.mem_range, zero_lt_succ,
    Finset.card_erase_of_mem, Finset.card_range, succ_sub_succ_eq_sub, Nat.sub_zero]

/--
lemma `roughNumbersUpTo_eq_biUnion` / 引理 `roughNumbersUpTo_eq_biUnion`

English:
lemma roughNumbersUpTo_eq_biUnion
  given: (N k)
  proof: by
  ext m
  simp only [roughNumbersUpTo, mem_smoothNumbers_iff_forall_le, not_and, not_forall,
    not_lt, exists_prop, Finset.mem_range, Finset.mem_filter,
    Finset.mem_biUnion, Finset.mem_sdiff, mem_primesBelow,
    show forall P Q : Prop, P ∧ (P -> Q) ↔ P ∧ Q by tauto]
  simp_rw [← exists_and_

中文:
引理 roughNumbersUpTo_eq_biUnion
  条件: (N k)
  证明: by
  ext m
  simp only [roughNumbersUpTo, mem_smoothNumbers_iff_forall_le, not_and, not_forall,
    not_lt, exists_prop, Finset.mem_range, Finset.mem_filter,
    Finset.mem_biUnion, Finset.mem_sdiff, mem_primesBelow,
    show forall P Q : Prop, P ∧ (P -> Q) ↔ P ∧ Q by tauto]
  simp_rw [← exists_and_

Depends on / 依赖: Finset, Finset.mem_biUnion, Finset.mem_filter, Finset.mem_range, Finset.mem_sdiff, Nat.pos_of_ne_zero, exists_and_left, exists_congr, exists_prop, le_of_dvd, mem_biUnion, mem_filter, mem_primesBelow, mem_range, mem_sdiff, mem_smoothNumbers_iff_forall_le, not_and, not_forall, not_lt, not_lt.mpr
-/
lemma roughNumbersUpTo_eq_biUnion (N k) :
    roughNumbersUpTo N k =
      ((N + 1).primesBelow \ k.primesBelow).biUnion
        fun p => {m in Finset.range (N + 1) | m != 0 ∧ p ∣ m} := by
  ext m
  simp only [roughNumbersUpTo, mem_smoothNumbers_iff_forall_le, not_and, not_forall,
    not_lt, exists_prop, Finset.mem_range, Finset.mem_filter,
    Finset.mem_biUnion, Finset.mem_sdiff, mem_primesBelow,
    show forall P Q : Prop, P ∧ (P -> Q) ↔ P ∧ Q by tauto]
  simp_rw [← exists_and_left, ← not_lt]
  refine exists_congr fun p => ?_
  have H : m != 0 -> p ∣ m -> ¬ m < p :=
fun h₁ h₂ => not_lt.mpr le_of_dvd (Nat.pos_of_ne_zero h₁) h₂
  grind

/--
lemma `roughNumbersUpTo_card_le` / 引理 `roughNumbersUpTo_card_le`

English:
lemma roughNumbersUpTo_card_le
  given: (N k : Nat)
  proof: by
  rw [roughNumbersUpTo_eq_biUnion]
exact Finset.card_biUnion_le.trans Finset.sum_le_sum fun p _ => (card_multiples' N p).le

中文:
引理 roughNumbersUpTo_card_le
  条件: (N k : 自然数)
  证明: by
  rw [roughNumbersUpTo_eq_biUnion]
exact Finset.card_biUnion_le.trans Finset.sum_le_sum fun p _ => (card_multiples' N p).le

Depends on / 依赖: Finset, Finset.card_biUnion_le.trans, Finset.sum_le_sum, card_biUnion_le, card_multiples, roughNumbersUpTo_eq_biUnion, sum_le_sum
-/
lemma roughNumbersUpTo_card_le (N k : Nat) :
    #(roughNumbersUpTo N k) <= ((N + 1).primesBelow \ k.primesBelow).sum (fun p => N / p) := by
  rw [roughNumbersUpTo_eq_biUnion]
exact Finset.card_biUnion_le.trans Finset.sum_le_sum fun p _ => (card_multiples' N p).le

end Nat
