/-
Copyright (c) 2024 Arend Mellendijk. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arend Mellendijk
-/
module

public import Mathlib.Algebra.Order.Antidiag.Pi
public import Mathlib.Algebra.Order.BigOperators.Ring.Finset
public import Mathlib.NumberTheory.ArithmeticFunction.Misc
public import Mathlib.Tactic.FinCases

/-!
# Sets of tuples with a fixed product

This file defines the finite set of `d`-tuples of natural numbers with a fixed product `n` as
`Nat.finMulAntidiag`.

## Main Results
* There are `d^(ω n)` ways to write `n` as a product of `d` natural numbers, when `n` is squarefree
  (`card_finMulAntidiag_of_squarefree`)
* There are `3^(ω n)` pairs of natural numbers whose `lcm` is `n`, when `n` is squarefree
  (`card_pair_lcm_eq`)
-/

@[expose] public section

open Finset
open scoped ArithmeticFunction
namespace PNat

set_option backward.isDefEq.respectTransparency false in
/--
Instance `instHasAntidiagonal` / 实例 `instHasAntidiagonal`

English:
instance instHasAntidiagonal
  signature: : Finset.HasAntidiagonal (Additive Nat+)
  body: /- The set of divisors of a positive natural number.
This is `Nat.divisorsAntidiagonal` without a special case for `n = 0`. -/
  let divisorsAntidiagonal (n : Nat+) : Finset (Nat+ × Nat+) :=
    (Nat.divisorsAntidiagonal n).attach.map
      ⟨fun x =>
        (⟨x.val.1, Nat.pos_of_mem_divisors <| Nat

中文:
实例 instHasAntidiagonal
  签名: : 有限集.有Antidiagonal (加性 自然数+)
  定义体: /- The set of divisors of a positive natural number.
This is `Nat.divisorsAntidiagonal` without a special case for `n = 0`. -/
  let divisorsAntidiagonal (n : Nat+) : Finset (Nat+ × Nat+) :=
    (Nat.divisorsAntidiagonal n).attach.map
      ⟨fun x =>
        (⟨x.val.1, Nat.pos_of_mem_divisors <| Nat
-/
instance instHasAntidiagonal : Finset.HasAntidiagonal (Additive Nat+) :=
  /- The set of divisors of a positive natural number.
This is `Nat.divisorsAntidiagonal` without a special case for `n = 0`. -/
  let divisorsAntidiagonal (n : Nat+) : Finset (Nat+ × Nat+) :=
    (Nat.divisorsAntidiagonal n).attach.map
      ⟨fun x =>
        (⟨x.val.1, Nat.pos_of_mem_divisors <| Nat.fst_mem_divisors_of_mem_antidiagonal x.prop⟩,
⟨x.val.2, Nat.pos_of_mem_divisors Nat.snd_mem_divisors_of_mem_antidiagonal x.prop⟩),
fun _ _ h => Subtype.ext Prod.ext (congr_arg (·.1.val) h) (congr_arg (·.2.val) h)⟩
  have mem_divisorsAntidiagonal {n : Nat+} (x : Nat+ × Nat+) :
    x in divisorsAntidiagonal n ↔ x.1 * x.2 = n := by
    simp_rw [divisorsAntidiagonal, Finset.mem_map, Finset.mem_attach, Function.Embedding.coeFn_mk,
      Prod.ext_iff, true_and, ← coe_inj, Subtype.exists]
    simp
  { antidiagonal := fun n => divisorsAntidiagonal (Additive.toMul n) |>.map
      (.prodMap (Additive.ofMul.toEmbedding) (Additive.ofMul.toEmbedding))
    mem_antidiagonal := by simp [← ofMul_mul, mem_divisorsAntidiagonal] }

end PNat

namespace Nat

/--
Definition of `finMulAntidiag` / `finMulAntidiag` 的定义

English:
definition finMulAntidiag
  signature: (d : Nat) (n : Nat)
  body: if hn : 0 < n then
(Finset.finAntidiagonal d (Additive.ofMul (α := Nat+) ⟨n, hn⟩)).map
.arrowCongrRight Additive.toMul.toEmbedding.trans ⟨PNat.val, PNat.coe_injective⟩
  else
    ∅

中文:
定义 finMulAntidiag
  签名: (d : 自然数) (n : 自然数)
  定义体: if hn : 0 < n then
(Finset.finAntidiagonal d (Additive.ofMul (α := Nat+) ⟨n, hn⟩)).map
.arrowCongrRight Additive.toMul.toEmbedding.trans ⟨PNat.val, PNat.coe_injective⟩
  else
    ∅

Depends on / 依赖: Additive, Additive.ofMul, Additive.toMul.toEmbedding.trans, Finset, Finset.finAntidiagonal, PNat.coe_injective, PNat.val, arrowCongrRight, coe_injective, finAntidiagonal, toEmbedding
-/
def finMulAntidiag (d : Nat) (n : Nat) : Finset (Fin d -> Nat) :=
  if hn : 0 < n then
(Finset.finAntidiagonal d (Additive.ofMul (α := Nat+) ⟨n, hn⟩)).map
.arrowCongrRight Additive.toMul.toEmbedding.trans ⟨PNat.val, PNat.coe_injective⟩
  else
    ∅

set_option backward.isDefEq.respectTransparency false in
@[simp]
/--
theorem `mem_finMulAntidiag` / 定理 `mem_finMulAntidiag`

English:
theorem mem_finMulAntidiag
  given: {d n : Nat} {f : Fin d -> Nat}
  proof: by
  unfold finMulAntidiag
  split_ifs with h
  · simp_rw [mem_map, mem_finAntidiagonal, Function.Embedding.arrowCongrRight_apply,
      Function.comp_def, Function.Embedding.trans_apply, Equiv.coe_toEmbedding,
      Function.Embedding.coeFn_mk, ← Additive.ofMul.symm_apply_eq, Additive.ofMul_symm_eq

中文:
定理 mem_finMulAntidiag
  条件: {d n : 自然数} {f : 有限集 d -> 自然数}
  证明: by
  unfold finMulAntidiag
  split_ifs with h
  · simp_rw [mem_map, mem_finAntidiagonal, Function.Embedding.arrowCongrRight_apply,
      Function.comp_def, Function.Embedding.trans_apply, Equiv.coe_toEmbedding,
      Function.Embedding.coeFn_mk, ← Additive.ofMul.symm_apply_eq, Additive.ofMul_symm_eq

Depends on / 依赖: Additive, Additive.ofMul, Additive.ofMul.symm_apply_eq, Additive.ofMul_symm_eq, Embedding, Equiv.coe_toEmbedding, Equiv.piCongrRight, Equiv.piCongrRight_apply, Function, Function.Embedding.arrowCongrRight_apply, Function.Embedding.coeFn_mk, Function.Embedding.trans_apply, Function.comp_def, LinearOrderedCommGroup, LinearOrderedCommGroup.to_noMaxOrder, NoMaxOrder, Nontrivial, PNat.coe_inj, PNat.coe_prod, PNat.mk_coe
-/
theorem mem_finMulAntidiag {d n : Nat} {f : Fin d -> Nat} :
    f in finMulAntidiag d n ↔ ∏ i, f i = n ∧ n != 0 := by
  unfold finMulAntidiag
  split_ifs with h
  · simp_rw [mem_map, mem_finAntidiagonal, Function.Embedding.arrowCongrRight_apply,
      Function.comp_def, Function.Embedding.trans_apply, Equiv.coe_toEmbedding,
      Function.Embedding.coeFn_mk, ← Additive.ofMul.symm_apply_eq, Additive.ofMul_symm_eq,
      toMul_sum, (Equiv.piCongrRight fun _ => Additive.ofMul).surjective.exists,
      Equiv.piCongrRight_apply, Pi.map_apply, toMul_ofMul, ← PNat.coe_inj, PNat.mk_coe,
      PNat.coe_prod]
    constructor
    · rintro ⟨a, ha_mem, rfl⟩
      exact ⟨ha_mem, h.ne.symm⟩
    · rintro ⟨rfl, _⟩
      refine ⟨fun i => ⟨f i, ?_⟩, rfl, funext fun _ => rfl⟩
      apply Nat.pos_of_ne_zero
      exact Finset.prod_ne_zero_iff.mp h.ne.symm _ (mem_univ _)
  · simp only [not_lt, nonpos_iff_eq_zero] at h
    simp only [h, notMem_empty, ne_eq, not_true_eq_false, and_false]

@[simp]
/--
theorem `finMulAntidiag_zero_right` / 定理 `finMulAntidiag_zero_right`

English:
theorem finMulAntidiag_zero_right
  given: (d : Nat)
  proof: rfl

中文:
定理 finMulAntidiag_zero_right
  条件: (d : 自然数)
  证明: rfl

Depends on / 依赖: LinearOrderedCommGroup, LinearOrderedCommGroup.to_noMinOrder, NoMinOrder, Nontrivial, to_noMinOrder
-/
theorem finMulAntidiag_zero_right (d : Nat) :
    finMulAntidiag d 0 = ∅ := rfl

/--
theorem `finMulAntidiag_one` / 定理 `finMulAntidiag_one`

English:
theorem finMulAntidiag_one
  given: {d : Nat}
  proof: by
  ext
  simp only [mem_finMulAntidiag, prod_eq_one_iff, mem_univ, forall_const, ne_eq, one_ne_zero,
    not_false_eq_true, and_true, mem_singleton]
  grind

中文:
定理 finMulAntidiag_one
  条件: {d : 自然数}
  证明: by
  ext
  simp only [mem_finMulAntidiag, prod_eq_one_iff, mem_univ, forall_const, ne_eq, one_ne_zero,
    not_false_eq_true, and_true, mem_singleton]
  grind

Depends on / 依赖: and_true, forall_const, mem_finMulAntidiag, mem_singleton, mem_univ, ne_eq, not_false_eq_true, one_ne_zero, prod_eq_one_iff
-/
theorem finMulAntidiag_one {d : Nat} :
    finMulAntidiag d 1 = {fun _ => 1} := by
  ext
  simp only [mem_finMulAntidiag, prod_eq_one_iff, mem_univ, forall_const, ne_eq, one_ne_zero,
    not_false_eq_true, and_true, mem_singleton]
  grind

/--
theorem `finMulAntidiag_zero_left` / 定理 `finMulAntidiag_zero_left`

English:
theorem finMulAntidiag_zero_left
  given: {n : Nat} (hn : n != 1)
  proof: by
  ext
  simp [hn.symm]

中文:
定理 finMulAntidiag_zero_left
  条件: {n : 自然数} (hn : n != 1)
  证明: by
  ext
  simp [hn.symm]

Depends on / 依赖: hn.symm
-/
theorem finMulAntidiag_zero_left {n : Nat} (hn : n != 1) :
    finMulAntidiag 0 n = ∅ := by
  ext
  simp [hn.symm]

/--
theorem `dvd_of_mem_finMulAntidiag` / 定理 `dvd_of_mem_finMulAntidiag`

English:
theorem dvd_of_mem_finMulAntidiag
  statement: {n d : Nat} {f : Fin d -> Nat} (hf : f in finMulAntidiag d n)
  proof: by
  rw [mem_finMulAntidiag] at hf
  rw [← hf.1]
  exact dvd_prod_of_mem f (mem_univ i)

中文:
定理 dvd_of_mem_finMulAntidiag
  结论: {n d : 自然数} {f : 有限集 d -> 自然数} (hf : f in finMulAntidiag d n)
  证明: by
  rw [mem_finMulAntidiag] at hf
  rw [← hf.1]
  exact dvd_prod_of_mem f (mem_univ i)

Depends on / 依赖: dvd_prod_of_mem, mem_finMulAntidiag, mem_univ
-/
theorem dvd_of_mem_finMulAntidiag {n d : Nat} {f : Fin d -> Nat} (hf : f in finMulAntidiag d n)
    (i : Fin d) : f i ∣ n := by
  rw [mem_finMulAntidiag] at hf
  rw [← hf.1]
  exact dvd_prod_of_mem f (mem_univ i)

/--
theorem `ne_zero_of_mem_finMulAntidiag` / 定理 `ne_zero_of_mem_finMulAntidiag`

English:
theorem ne_zero_of_mem_finMulAntidiag
  statement: {d n : Nat} {f : Fin d -> Nat}
  proof: ne_zero_of_dvd_ne_zero (mem_finMulAntidiag.mp hf).2 (dvd_of_mem_finMulAntidiag hf i)

中文:
定理 ne_zero_of_mem_finMulAntidiag
  结论: {d n : 自然数} {f : 有限集 d -> 自然数}
  证明: ne_zero_of_dvd_ne_zero (mem_finMulAntidiag.mp hf).2 (dvd_of_mem_finMulAntidiag hf i)

Depends on / 依赖: dvd_of_mem_finMulAntidiag, mem_finMulAntidiag, mem_finMulAntidiag.mp, ne_zero_of_dvd_ne_zero
-/
theorem ne_zero_of_mem_finMulAntidiag {d n : Nat} {f : Fin d -> Nat}
    (hf : f in finMulAntidiag d n) (i : Fin d) : f i != 0 :=
  ne_zero_of_dvd_ne_zero (mem_finMulAntidiag.mp hf).2 (dvd_of_mem_finMulAntidiag hf i)

/--
theorem `prod_eq_of_mem_finMulAntidiag` / 定理 `prod_eq_of_mem_finMulAntidiag`

English:
theorem prod_eq_of_mem_finMulAntidiag
  statement: {d n : Nat} {f : Fin d -> Nat}
  proof: (mem_finMulAntidiag.mp hf).1

中文:
定理 prod_eq_of_mem_finMulAntidiag
  结论: {d n : 自然数} {f : 有限集 d -> 自然数}
  证明: (mem_finMulAntidiag.mp hf).1

Depends on / 依赖: mem_finMulAntidiag, mem_finMulAntidiag.mp
-/
theorem prod_eq_of_mem_finMulAntidiag {d n : Nat} {f : Fin d -> Nat}
    (hf : f in finMulAntidiag d n) : ∏ i, f i = n :=
  (mem_finMulAntidiag.mp hf).1

/--
theorem `finMulAntidiag_eq_piFinset_divisors_filter` / 定理 `finMulAntidiag_eq_piFinset_divisors_filter`

English:
theorem finMulAntidiag_eq_piFinset_divisors_filter
  given: {d m n : Nat} (hmn : m ∣ n) (hn : n != 0)
  proof: by
  ext f
  simp only [ne_eq,
    Fintype.mem_piFinset, mem_divisors, mem_filter]
  constructor
  · intro hf
    refine ⟨?_, prod_eq_of_mem_finMulAntidiag hf⟩
    exact fun i => ⟨(dvd_of_mem_finMulAntidiag hf i).trans hmn, hn⟩
  · rw [mem_finMulAntidiag]
    exact fun ⟨_, hprod⟩ => ⟨hprod, ne_zero_

中文:
定理 finMulAntidiag_eq_piFinset_divisors_filter
  条件: {d m n : 自然数} (hmn : m ∣ n) (hn : n != 0)
  证明: by
  ext f
  simp only [ne_eq,
    Fintype.mem_piFinset, mem_divisors, mem_filter]
  constructor
  · intro hf
    refine ⟨?_, prod_eq_of_mem_finMulAntidiag hf⟩
    exact fun i => ⟨(dvd_of_mem_finMulAntidiag hf i).trans hmn, hn⟩
  · rw [mem_finMulAntidiag]
    exact fun ⟨_, hprod⟩ => ⟨hprod, ne_zero_

Depends on / 依赖: Fintype, Fintype.mem_piFinset, dvd_of_mem_finMulAntidiag, mem_divisors, mem_filter, mem_finMulAntidiag, mem_piFinset, ne_eq, ne_zero_of_dvd_ne_zero, prod_eq_of_mem_finMulAntidiag
-/
theorem finMulAntidiag_eq_piFinset_divisors_filter {d m n : Nat} (hmn : m ∣ n) (hn : n != 0) :
    finMulAntidiag d m =
      {f in Fintype.piFinset fun _ : Fin d => n.divisors | ∏ i, f i = m} := by
  ext f
  simp only [ne_eq,
    Fintype.mem_piFinset, mem_divisors, mem_filter]
  constructor
  · intro hf
    refine ⟨?_, prod_eq_of_mem_finMulAntidiag hf⟩
    exact fun i => ⟨(dvd_of_mem_finMulAntidiag hf i).trans hmn, hn⟩
  · rw [mem_finMulAntidiag]
    exact fun ⟨_, hprod⟩ => ⟨hprod, ne_zero_of_dvd_ne_zero hn hmn⟩

/--
lemma `image_apply_finMulAntidiag` / 引理 `image_apply_finMulAntidiag`

English:
lemma image_apply_finMulAntidiag
  given: {d n : Nat} {i : Fin d} (hd : d != 1)
  proof: by
  ext k
  simp only [mem_image, ne_eq, mem_divisors]
  constructor
  · rintro ⟨f, hf, rfl⟩
    exact ⟨dvd_of_mem_finMulAntidiag hf _, (mem_finMulAntidiag.mp hf).2⟩
  · simp_rw [mem_finMulAntidiag]
    rintro ⟨⟨r, rfl⟩, hn⟩
    have hs : Nontrivial (Fin d) := by
      rw [Fin.nontrivial_iff_two_le

中文:
引理 image_apply_finMulAntidiag
  条件: {d n : 自然数} {i : 有限集 d} (hd : d != 1)
  证明: by
  ext k
  simp only [mem_image, ne_eq, mem_divisors]
  constructor
  · rintro ⟨f, hf, rfl⟩
    exact ⟨dvd_of_mem_finMulAntidiag hf _, (mem_finMulAntidiag.mp hf).2⟩
  · simp_rw [mem_finMulAntidiag]
    rintro ⟨⟨r, rfl⟩, hn⟩
    have hs : Nontrivial (Fin d) := by
      rw [Fin.nontrivial_iff_two_le

Depends on / 依赖: Fin.nontrivial_iff_two_le, Finset, Finset.mul_prod_erase, Nontrivial, and_true, dvd_of_mem_finMulAntidiag, eq_or_ne, exists_ne, hi_ne, i.elim0, ite_true, mem_divisors, mem_finMulAntidiag, mem_finMulAntidiag.mp, mem_image, mem_univ, mul_prod_erase, ne_eq, nontrivial_iff_two_le, simp_rw
-/
lemma image_apply_finMulAntidiag {d n : Nat} {i : Fin d} (hd : d != 1) :
    (finMulAntidiag d n).image (fun f => f i) = divisors n := by
  ext k
  simp only [mem_image, ne_eq, mem_divisors]
  constructor
  · rintro ⟨f, hf, rfl⟩
    exact ⟨dvd_of_mem_finMulAntidiag hf _, (mem_finMulAntidiag.mp hf).2⟩
  · simp_rw [mem_finMulAntidiag]
    rintro ⟨⟨r, rfl⟩, hn⟩
    have hs : Nontrivial (Fin d) := by
      rw [Fin.nontrivial_iff_two_le]
      obtain rfl | hd' := eq_or_ne d 0
      · exact i.elim0
      lia
    obtain ⟨i', hi_ne⟩ := exists_ne i
    use fun j => if j = i then k else if j = i' then r else 1
    simp only [ite_true, and_true]
    rw [← Finset.mul_prod_erase (h := mem_univ i)]; rw [← Finset.mul_prod_erase (a := i')]
    · simp_all
    exact mem_erase.mpr ⟨hi_ne, mem_univ _⟩

/--
lemma `image_piFinTwoEquiv_finMulAntidiag` / 引理 `image_piFinTwoEquiv_finMulAntidiag`

English:
lemma image_piFinTwoEquiv_finMulAntidiag
  given: {n : Nat}
  proof: by
  ext x
  simp [(piFinTwoEquiv <| fun _ => Nat).symm.surjective.exists]

中文:
引理 image_piFinTwoEquiv_finMulAntidiag
  条件: {n : 自然数}
  证明: by
  ext x
  simp [(piFinTwoEquiv <| fun _ => Nat).symm.surjective.exists]

Depends on / 依赖: piFinTwoEquiv, surjective, symm.surjective.exists
-/
lemma image_piFinTwoEquiv_finMulAntidiag {n : Nat} :
    (finMulAntidiag 2 n).image (piFinTwoEquiv <| fun _ => Nat) = divisorsAntidiagonal n := by
  ext x
  simp [(piFinTwoEquiv <| fun _ => Nat).symm.surjective.exists]

/--
lemma `finMulAntidiag_existsUnique_prime_dvd` / 引理 `finMulAntidiag_existsUnique_prime_dvd`

English:
lemma finMulAntidiag_existsUnique_prime_dvd
  statement: {d n p : Nat} (hn : Squarefree n)
  proof: by
  rw [mem_finMulAntidiag] at hf
  rw [mem_primeFactorsList hf.2]; rw [← hf.1]; rw [hp.1.prime.dvd_finsetProd_iff] at hp
  obtain ⟨i, his, hi⟩ := hp.2
  refine ⟨i, hi, ?_⟩
  intro j hj
  by_contra hij
  apply Nat.Prime.not_coprime_iff_dvd.mpr ⟨p, hp.1, hi, hj⟩
  apply Nat.coprime_of_squarefree_mul

中文:
引理 finMulAntidiag_存在Unique_prime_dvd
  结论: {d n p : 自然数} (hn : Squarefree n)
  证明: by
  rw [mem_finMulAntidiag] at hf
  rw [mem_primeFactorsList hf.2]; rw [← hf.1]; rw [hp.1.prime.dvd_finsetProd_iff] at hp
  obtain ⟨i, his, hi⟩ := hp.2
  refine ⟨i, hi, ?_⟩
  intro j hj
  by_contra hij
  apply Nat.Prime.not_coprime_iff_dvd.mpr ⟨p, hp.1, hi, hj⟩
  apply Nat.coprime_of_squarefree_mul

Depends on / 依赖: Finset, Finset.mul_prod_erase, Nat.Prime.not_coprime_iff_dvd.mpr, Nat.coprime_of_squarefree_mul, Nat.dvd_mul_right, coprime_of_squarefree_mul, dvd_finsetProd_iff, dvd_mul_right, hn.squarefree_of_dvd, mem_erase, mem_erase.mpr, mem_finMulAntidiag, mem_primeFactorsList, mem_univ, mul_assoc, mul_prod_erase, not_coprime_iff_dvd, prime.dvd_finsetProd_iff, squarefree_of_dvd
-/
lemma finMulAntidiag_existsUnique_prime_dvd {d n p : Nat} (hn : Squarefree n)
    (hp : p in n.primeFactorsList) (f : Fin d -> Nat) (hf : f in finMulAntidiag d n) :
    exists! i, p ∣ f i := by
  rw [mem_finMulAntidiag] at hf
  rw [mem_primeFactorsList hf.2]; rw [← hf.1]; rw [hp.1.prime.dvd_finsetProd_iff] at hp
  obtain ⟨i, his, hi⟩ := hp.2
  refine ⟨i, hi, ?_⟩
  intro j hj
  by_contra hij
  apply Nat.Prime.not_coprime_iff_dvd.mpr ⟨p, hp.1, hi, hj⟩
  apply Nat.coprime_of_squarefree_mul
  apply hn.squarefree_of_dvd
  rw [← hf.1]; rw [← Finset.mul_prod_erase _ _ his]; rw [← Finset.mul_prod_erase _ _ (mem_erase.mpr ⟨hij]; rw [mem_univ _⟩)]; rw [← mul_assoc]
  apply Nat.dvd_mul_right

/--
Definition of `primeFactorsPiBij` / `primeFactorsPiBij` 的定义

English:
definition primeFactorsPiBij
  signature: (d n : Nat)
  body: fun f _ i => ∏ p in {p in n.primeFactors.attach | f p.1 p.2 = i}, p

中文:
定义 primeFactorsPiBij
  签名: (d n : 自然数)
  定义体: fun f _ i => ∏ p in {p in n.primeFactors.attach | f p.1 p.2 = i}, p
-/
private def primeFactorsPiBij (d n : Nat) :
    forall f in (n.primeFactors.pi fun _ => (univ : Finset <| Fin d)), Fin d -> Nat :=
  fun f _ i => ∏ p in {p in n.primeFactors.attach | f p.1 p.2 = i}, p

/--
theorem `primeFactorsPiBij_img` / 定理 `primeFactorsPiBij_img`

English:
theorem primeFactorsPiBij_img
  statement: (d n : Nat) (hn : Squarefree n)
  proof: by
  rw [mem_finMulAntidiag]
  refine ⟨?_, hn.ne_zero⟩
  unfold Nat.primeFactorsPiBij
  rw [prod_fiberwise_of_maps_to]; rw [prod_attach (f := fun x => x)]
  · apply prod_primeFactors_of_squarefree hn
  · apply fun _ _ => mem_univ _

中文:
定理 primeFactorsPiBij_img
  结论: (d n : 自然数) (hn : Squarefree n)
  证明: by
  rw [mem_finMulAntidiag]
  refine ⟨?_, hn.ne_zero⟩
  unfold Nat.primeFactorsPiBij
  rw [prod_fiberwise_of_maps_to]; rw [prod_attach (f := fun x => x)]
  · apply prod_primeFactors_of_squarefree hn
  · apply fun _ _ => mem_univ _
-/
private theorem primeFactorsPiBij_img (d n : Nat) (hn : Squarefree n)
    (f : (p : Nat) -> p in n.primeFactors -> Fin d) (hf : f in pi n.primeFactors fun _ => univ) :
    Nat.primeFactorsPiBij d n f hf in finMulAntidiag d n := by
  rw [mem_finMulAntidiag]
  refine ⟨?_, hn.ne_zero⟩
  unfold Nat.primeFactorsPiBij
  rw [prod_fiberwise_of_maps_to]; rw [prod_attach (f := fun x => x)]
  · apply prod_primeFactors_of_squarefree hn
  · apply fun _ _ => mem_univ _

/--
theorem `primeFactorsPiBij_inj` / 定理 `primeFactorsPiBij_inj`

English:
theorem primeFactorsPiBij_inj
  statement: (d n : Nat)
  proof: by
  contrapose!
  simp_rw [Function.ne_iff]
  intro ⟨p, hp, hfg⟩
  use f p hp
  dsimp only [Nat.primeFactorsPiBij]
  apply ne_of_mem_of_not_mem (s := {x | p ∣ x}) <;> simp_rw [Set.mem_ofPred_eq]
  · rw [Finset.prod_filter]
    convert! Finset.dvd_prod_of_mem _ (mem_attach (n.primeFactors) ⟨p, hp⟩)


中文:
定理 primeFactorsPiBij_inj
  结论: (d n : 自然数)
  证明: by
  contrapose!
  simp_rw [Function.ne_iff]
  intro ⟨p, hp, hfg⟩
  use f p hp
  dsimp only [Nat.primeFactorsPiBij]
  apply ne_of_mem_of_not_mem (s := {x | p ∣ x}) <;> simp_rw [Set.mem_ofPred_eq]
  · rw [Finset.prod_filter]
    convert! Finset.dvd_prod_of_mem _ (mem_attach (n.primeFactors) ⟨p, hp⟩)

-/
private theorem primeFactorsPiBij_inj (d n : Nat)
    (f : (p : Nat) -> p in n.primeFactors -> Fin d) (hf : f in pi n.primeFactors fun _ => univ)
    (g : (p : Nat) -> p in n.primeFactors -> Fin d) (hg : g in pi n.primeFactors fun _ => univ) :
    Nat.primeFactorsPiBij d n f hf = Nat.primeFactorsPiBij d n g hg -> f = g := by
  contrapose!
  simp_rw [Function.ne_iff]
  intro ⟨p, hp, hfg⟩
  use f p hp
  dsimp only [Nat.primeFactorsPiBij]
  apply ne_of_mem_of_not_mem (s := {x | p ∣ x}) <;> simp_rw [Set.mem_ofPred_eq]
  · rw [Finset.prod_filter]
    convert! Finset.dvd_prod_of_mem _ (mem_attach (n.primeFactors) ⟨p, hp⟩)
    rw [if_pos rfl]
  · rw [mem_primeFactors] at hp
    rw [Prime.dvd_finsetProd_iff hp.1.prime]
    push Not
    intro q hq
    rw [Nat.prime_dvd_prime_iff_eq hp.1 (Nat.prime_of_mem_primeFactorsList
 List.mem_toFinset.mp q.2)]
    rintro rfl
    rw [(mem_filter.mp hq).2] at hfg
    exact hfg rfl

/--
theorem `primeFactorsPiBij_surj` / 定理 `primeFactorsPiBij_surj`

English:
theorem primeFactorsPiBij_surj
  statement: (d n : Nat) (hn : Squarefree n)
  proof: by
  have existsUnique := fun (p : Nat) (hp : p in n.primeFactors) =>
    (finMulAntidiag_existsUnique_prime_dvd hn
      (mem_primeFactors_iff_mem_primeFactorsList.mp hp) t ht)
  choose f hf hf_unique using existsUnique
  refine ⟨f, ?_, ?_⟩
  · simp only [mem_pi, mem_univ, forall_true_iff]
  funext

中文:
定理 primeFactorsPiBij_surj
  结论: (d n : 自然数) (hn : Squarefree n)
  证明: by
  have existsUnique := fun (p : Nat) (hp : p in n.primeFactors) =>
    (finMulAntidiag_existsUnique_prime_dvd hn
      (mem_primeFactors_iff_mem_primeFactorsList.mp hp) t ht)
  choose f hf hf_unique using existsUnique
  refine ⟨f, ?_, ?_⟩
  · simp only [mem_pi, mem_univ, forall_true_iff]
  funext
-/
private theorem primeFactorsPiBij_surj (d n : Nat) (hn : Squarefree n)
    (t : Fin d -> Nat) (ht : t in finMulAntidiag d n) : exists (g : _)
    (hg : g in pi n.primeFactors fun _ => univ), Nat.primeFactorsPiBij d n g hg = t := by
  have existsUnique := fun (p : Nat) (hp : p in n.primeFactors) =>
    (finMulAntidiag_existsUnique_prime_dvd hn
      (mem_primeFactors_iff_mem_primeFactorsList.mp hp) t ht)
  choose f hf hf_unique using existsUnique
  refine ⟨f, ?_, ?_⟩
  · simp only [mem_pi, mem_univ, forall_true_iff]
  funext i
  have : t i ∣ n := dvd_of_mem_finMulAntidiag ht _
  trans (∏ p in n.primeFactors.attach, if p.1 ∣ t i then p else 1)
  · rw [Nat.primeFactorsPiBij, ← prod_filter]
    congr
    grind
  rw [prod_attach (f := fun p => if p ∣ t i then p else 1)]; rw [← Finset.prod_filter]
  rw [primeFactors_filter_dvd_of_dvd hn.ne_zero this]
exact prod_primeFactors_of_squarefree hn.squarefree_of_dvd this

/--
theorem `card_finMulAntidiag_pi` / 定理 `card_finMulAntidiag_pi`

English:
theorem card_finMulAntidiag_pi
  given: (d n : Nat) (hn : Squarefree n)
  proof: by
  apply Finset.card_bij (Nat.primeFactorsPiBij d n) (primeFactorsPiBij_img d n hn)
    (primeFactorsPiBij_inj d n) (primeFactorsPiBij_surj d n hn)

中文:
定理 card_finMulAntidiag_pi
  条件: (d n : 自然数) (hn : Squarefree n)
  证明: by
  apply Finset.card_bij (Nat.primeFactorsPiBij d n) (primeFactorsPiBij_img d n hn)
    (primeFactorsPiBij_inj d n) (primeFactorsPiBij_surj d n hn)
-/
private theorem card_finMulAntidiag_pi (d n : Nat) (hn : Squarefree n) :
    #(n.primeFactors.pi fun _ => (univ : Finset <| Fin d)) =
      #(finMulAntidiag d n) := by
  apply Finset.card_bij (Nat.primeFactorsPiBij d n) (primeFactorsPiBij_img d n hn)
    (primeFactorsPiBij_inj d n) (primeFactorsPiBij_surj d n hn)

open scoped ArithmeticFunction.omega in -- access notation `ω`
/--
theorem `card_finMulAntidiag_of_squarefree` / 定理 `card_finMulAntidiag_of_squarefree`

English:
theorem card_finMulAntidiag_of_squarefree
  given: {d n : Nat} (hn : Squarefree n)
  proof: by
  rw [← card_finMulAntidiag_pi d n hn]; rw [Finset.card_pi]; rw [Finset.prod_const]; rw [ArithmeticFunction.cardDistinctFactors_apply]; rw [← List.card_toFinset]; rw [toFinset_factors]; rw [Finset.card_fin]

中文:
定理 card_finMulAntidiag_of_squarefree
  条件: {d n : 自然数} (hn : Squarefree n)
  证明: by
  rw [← card_finMulAntidiag_pi d n hn]; rw [Finset.card_pi]; rw [Finset.prod_const]; rw [ArithmeticFunction.cardDistinctFactors_apply]; rw [← List.card_toFinset]; rw [toFinset_factors]; rw [Finset.card_fin]

Depends on / 依赖: ArithmeticFunction, ArithmeticFunction.cardDistinctFactors_apply, Finset, Finset.card_fin, Finset.card_pi, Finset.prod_const, List.card_toFinset, cardDistinctFactors_apply, card_fin, card_finMulAntidiag_pi, card_pi, card_toFinset, prod_const, toFinset_factors
-/
theorem card_finMulAntidiag_of_squarefree {d n : Nat} (hn : Squarefree n) :
    #(finMulAntidiag d n) = d ^ ω n := by
  rw [← card_finMulAntidiag_pi d n hn]; rw [Finset.card_pi]; rw [Finset.prod_const]; rw [ArithmeticFunction.cardDistinctFactors_apply]; rw [← List.card_toFinset]; rw [toFinset_factors]; rw [Finset.card_fin]

/--
theorem `finMulAntidiag_three` / 定理 `finMulAntidiag_three`

English:
theorem finMulAntidiag_three
  given: {n : Nat} (a) (ha : a in finMulAntidiag 3 n)
  statement: a 0 * a 1 * a 2 = n
  proof: by
  rw [← (mem_finMulAntidiag.mp ha).1]; rw [Fin.prod_univ_three a]

中文:
定理 finMulAntidiag_three
  条件: {n : 自然数} (a) (ha : a in finMulAntidiag 3 n)
  结论: a 0 * a 1 * a 2 = n
  证明: by
  rw [← (mem_finMulAntidiag.mp ha).1]; rw [Fin.prod_univ_three a]

Depends on / 依赖: Fin.prod_univ_three, mem_finMulAntidiag, mem_finMulAntidiag.mp, prod_univ_three
-/
theorem finMulAntidiag_three {n : Nat} (a) (ha : a in finMulAntidiag 3 n) : a 0 * a 1 * a 2 = n := by
  rw [← (mem_finMulAntidiag.mp ha).1]; rw [Fin.prod_univ_three a]

namespace card_pair_lcm_eq

/-!
The following private declarations are ingredients for the proof of `card_pair_lcm_eq`.
-/

@[reducible]
/--
Definition of `f` / `f` 的定义

English:
definition f
  signature: {n : Nat}
  body: fun a _ => (a 0 * a 1, a 0 * a 2)

中文:
定义 f
  签名: {n : 自然数}
  定义体: fun a _ => (a 0 * a 1, a 0 * a 2)
-/
private def f {n : Nat} : forall a in finMulAntidiag 3 n, Nat × Nat := fun a _ => (a 0 * a 1, a 0 * a 2)

/--
theorem `f_img` / 定理 `f_img`

English:
theorem f_img
  statement: {n : Nat} (hn : Squarefree n) (a : Fin 3 -> Nat)
  proof: by
  rw [mem_filter]; rw [Finset.mem_product]; rw [mem_divisors]; rw [mem_divisors]
  refine ⟨⟨⟨?_, hn.ne_zero⟩, ⟨?_, hn.ne_zero⟩⟩, ?_⟩ <;> rw [f, ← finMulAntidiag_three a ha]
  · apply dvd_mul_right
  · use a 1; ring
  dsimp only
  rw [lcm_mul_left]; rw [Nat.Coprime.lcm_eq_mul]
  · ring
  refine co

中文:
定理 f_img
  结论: {n : 自然数} (hn : Squarefree n) (a : 有限集 3 -> 自然数)
  证明: by
  rw [mem_filter]; rw [Finset.mem_product]; rw [mem_divisors]; rw [mem_divisors]
  refine ⟨⟨⟨?_, hn.ne_zero⟩, ⟨?_, hn.ne_zero⟩⟩, ?_⟩ <;> rw [f, ← finMulAntidiag_three a ha]
  · apply dvd_mul_right
  · use a 1; ring
  dsimp only
  rw [lcm_mul_left]; rw [Nat.Coprime.lcm_eq_mul]
  · ring
  refine co
-/
private theorem f_img {n : Nat} (hn : Squarefree n) (a : Fin 3 -> Nat)
    (ha : a in finMulAntidiag 3 n) :
    f a ha in Finset.filter (fun ⟨x, y⟩ => x.lcm y = n) (n.divisors ×ˢ n.divisors) := by
  rw [mem_filter]; rw [Finset.mem_product]; rw [mem_divisors]; rw [mem_divisors]
  refine ⟨⟨⟨?_, hn.ne_zero⟩, ⟨?_, hn.ne_zero⟩⟩, ?_⟩ <;> rw [f, ← finMulAntidiag_three a ha]
  · apply dvd_mul_right
  · use a 1; ring
  dsimp only
  rw [lcm_mul_left]; rw [Nat.Coprime.lcm_eq_mul]
  · ring
  refine coprime_of_squarefree_mul (hn.squarefree_of_dvd ?_)
  use a 0; rw [← finMulAntidiag_three a ha]; ring

/--
theorem `f_inj` / 定理 `f_inj`

English:
theorem f_inj
  statement: {n : Nat} (a : Fin 3 -> Nat) (ha : a in finMulAntidiag 3 n)
  proof: by
  obtain ⟨hfab1, hfab2⟩ := Prod.mk.inj hfab
  have hprods : a 0 * a 1 * a 2 = a 0 * a 1 * b 2 := by
    rw [finMulAntidiag_three a ha]; rw [hfab1]; rw [finMulAntidiag_three b hb]
  have hab2 : a 2 = b 2 := by
    rw [← mul_right_inj' <| mul_ne_zero (ne_zero_of_mem_finMulAntidiag ha 0)
      (ne_z

中文:
定理 f_inj
  结论: {n : 自然数} (a : 有限集 3 -> 自然数) (ha : a in finMulAntidiag 3 n)
  证明: by
  obtain ⟨hfab1, hfab2⟩ := Prod.mk.inj hfab
  have hprods : a 0 * a 1 * a 2 = a 0 * a 1 * b 2 := by
    rw [finMulAntidiag_three a ha]; rw [hfab1]; rw [finMulAntidiag_three b hb]
  have hab2 : a 2 = b 2 := by
    rw [← mul_right_inj' <| mul_ne_zero (ne_zero_of_mem_finMulAntidiag ha 0)
      (ne_z
-/
private theorem f_inj {n : Nat} (a : Fin 3 -> Nat) (ha : a in finMulAntidiag 3 n)
    (b : Fin 3 -> Nat) (hb : b in finMulAntidiag 3 n) (hfab : f a ha = f b hb) :
    a = b := by
  obtain ⟨hfab1, hfab2⟩ := Prod.mk.inj hfab
  have hprods : a 0 * a 1 * a 2 = a 0 * a 1 * b 2 := by
    rw [finMulAntidiag_three a ha]; rw [hfab1]; rw [finMulAntidiag_three b hb]
  have hab2 : a 2 = b 2 := by
    rw [← mul_right_inj' <| mul_ne_zero (ne_zero_of_mem_finMulAntidiag ha 0)
      (ne_zero_of_mem_finMulAntidiag ha 1)]
    exact hprods
  have hab0 : a 0 = b 0 := by
    rw [hab2] at hfab2
    exact (mul_left_inj' <| ne_zero_of_mem_finMulAntidiag hb 2).mp hfab2;
  have hab1 : a 1 = b 1 := by
    rw [hab0] at hfab1
    exact (mul_right_inj' <| ne_zero_of_mem_finMulAntidiag hb 0).mp hfab1;
  funext i; fin_cases i <;> assumption

/--
theorem `f_surj` / 定理 `f_surj`

English:
theorem f_surj
  statement: {n : Nat} (hn : n != 0) (b : Nat × Nat)
  proof: by
  dsimp only at hb
  let g := b.fst.gcd b.snd
  let a := ![g, b.fst / g, b.snd / g]
  have ha : a in finMulAntidiag 3 n := by
    rw [mem_finMulAntidiag]
    rw [mem_filter]; rw [Finset.mem_product] at hb
    refine ⟨?_, hn⟩
    · rw [Fin.prod_univ_three a]
      dsimp only [a, Matrix.cons_val]
 

中文:
定理 f_surj
  结论: {n : 自然数} (hn : n != 0) (b : 自然数 × 自然数)
  证明: by
  dsimp only at hb
  let g := b.fst.gcd b.snd
  let a := ![g, b.fst / g, b.snd / g]
  have ha : a in finMulAntidiag 3 n := by
    rw [mem_finMulAntidiag]
    rw [mem_filter]; rw [Finset.mem_product] at hb
    refine ⟨?_, hn⟩
    · rw [Fin.prod_univ_three a]
      dsimp only [a, Matrix.cons_val]
 
-/
private theorem f_surj {n : Nat} (hn : n != 0) (b : Nat × Nat)
    (hb : b in Finset.filter (fun ⟨x, y⟩ => x.lcm y = n) (n.divisors ×ˢ n.divisors)) :
    exists (a : Fin 3 -> Nat) (ha : a in finMulAntidiag 3 n), f a ha = b := by
  dsimp only at hb
  let g := b.fst.gcd b.snd
  let a := ![g, b.fst / g, b.snd / g]
  have ha : a in finMulAntidiag 3 n := by
    rw [mem_finMulAntidiag]
    rw [mem_filter]; rw [Finset.mem_product] at hb
    refine ⟨?_, hn⟩
    · rw [Fin.prod_univ_three a]
      dsimp only [a, Matrix.cons_val]
      rw [Nat.mul_div_cancel_left' (Nat.gcd_dvd_left _ _)]; rw [← hb.2]; rw [lcm]; rw [Nat.mul_div_assoc b.fst (Nat.gcd_dvd_right b.fst b.snd)]
  use a; use ha
  apply Prod.ext <;> dsimp only [a, Matrix.cons_val]
    <;> apply Nat.mul_div_cancel'
  · apply Nat.gcd_dvd_left
  · apply Nat.gcd_dvd_right

end card_pair_lcm_eq

open card_pair_lcm_eq in
open scoped ArithmeticFunction.omega in -- access notation `ω`
/--
theorem `card_pair_lcm_eq` / 定理 `card_pair_lcm_eq`

English:
theorem card_pair_lcm_eq
  given: {n : Nat} (hn : Squarefree n)
  proof: by
  rw [← card_finMulAntidiag_of_squarefree hn]; rw [eq_comm]
  apply Finset.card_bij f (f_img hn) f_inj (f_surj hn.ne_zero)

中文:
定理 card_pair_lcm_eq
  条件: {n : 自然数} (hn : Squarefree n)
  证明: by
  rw [← card_finMulAntidiag_of_squarefree hn]; rw [eq_comm]
  apply Finset.card_bij f (f_img hn) f_inj (f_surj hn.ne_zero)

Depends on / 依赖: Finset, Finset.card_bij, card_bij, card_finMulAntidiag_of_squarefree, eq_comm, f_img, f_inj, f_surj, hn.ne_zero, ne_zero
-/
theorem card_pair_lcm_eq {n : Nat} (hn : Squarefree n) :
    #{p in (n.divisors ×ˢ n.divisors) | p.1.lcm p.2 = n} = 3 ^ ω n := by
  rw [← card_finMulAntidiag_of_squarefree hn]; rw [eq_comm]
  apply Finset.card_bij f (f_img hn) f_inj (f_surj hn.ne_zero)

end Nat
