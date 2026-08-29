/-
Copyright (c) 2025 Weiyi Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Weiyi Wang
-/
module

public import Mathlib.Combinatorics.Enumerative.Partition.Basic
public import Mathlib.RingTheory.PowerSeries.PiTopology

/-!
# Generating functions for partitions

This file defines generating functions related to partitions. Given a character function $f(i, c)$
of a part $i$ and the number of occurrences of the part $c$, the related generating function is
$$
G_f(X) = \sum_{n = 0}^{\infty} \left(\sum_{p \in P_{n}} \prod_{i \in p} f(i, \#i)\right) X^n
= \prod_{i = 1}^{\infty}\left(1 + \sum_{j = 1}^{\infty} f(i, j) X^{ij}\right)
$$
where $P_n$ is all partitions of $n$, $\#i$ is the count of $i$ in the partition $p$.
We give the definition `Nat.Partition.genFun` using the first equation, and prove the second
equation in `Nat.Partition.hasProd_genFun` (with shifted indices).

This generating function can be specialized to
* When $f(i, c) = 1$, this is the generating function for partition function $p(n)$
  (TODO: prove this).
* When $f(i, 1) = 1$ and $f(i, c) = 0$ for $c > 1$, this is the generating function for
  `#(Nat.Partition.distincts n)`. More generally, setting $f(i, c) = 1$ only for $c < m$ gives
  the generating function for `#(Nat.Partition.countRestricted n m)`.
  (See `Nat.Partition.hasProd_powerSeriesMk_card_countRestricted`).
* When $f(i, c) = 1$ for odd $i$ and $f(i, c) = 0$ for even $i$, this is the generating function for
  `#(Nat.Partition.odds n)`. More generally, setting $f(i, c) = 1$ only for $i$ satisfying certain
  `p : Prop` gives the generating function for `#(Nat.Partition.restricted n p)`.
  (See `Nat.Partition.hasProd_powerSeriesMk_card_restricted`)

The definition of `Nat.Partition.genFun` ignores the value of $f(0, c)$ and $f(i, 0)$. The formula
can be interpreted as assuming $f(i, 0) = 1$ and $f(0, c) = 0$ for $c \ne 0$. In theory we could
respect the actual value of $f(0, c)$ and $f(i, 0)$, but it makes the otherwise finite sum and
product potentially infinite.
-/

@[expose] public section

open Finset PowerSeries
open scoped PowerSeries.WithPiTopology

namespace Nat.Partition
variable {R : Type*} [CommSemiring R]

/--
Definition of `genFun` / `genFun` 的定义

English:
definition genFun
  signature: (f : Nat -> Nat -> R)
  body: PowerSeries.mk fun n => ∑ p : n.Partition, p.parts.toFinsupp.prod f

@[simp]

中文:
定义 genFun
  签名: (f : 自然数 -> 自然数 -> R)
  定义体: PowerSeries.mk fun n => ∑ p : n.Partition, p.parts.toFinsupp.prod f

@[simp]

Depends on / 依赖: Partition, PowerSeries, PowerSeries.mk, SequentialSpace, X.toTopCat, n.Partition, p.parts.toFinsupp.prod, toFinsupp, toTopCat
-/
noncomputable def genFun (f : Nat -> Nat -> R) : R⟦X⟧ :=
  PowerSeries.mk fun n => ∑ p : n.Partition, p.parts.toFinsupp.prod f

@[simp]
/--
lemma `coeff_genFun` / 引理 `coeff_genFun`

English:
lemma coeff_genFun
  given: (f : Nat -> Nat -> R) (n : Nat)
  proof: PowerSeries.coeff_mk _ _

中文:
引理 coeff_genFun
  条件: (f : 自然数 -> 自然数 -> R) (n : 自然数)
  证明: PowerSeries.coeff_mk _ _

Depends on / 依赖: PowerSeries, PowerSeries.coeff_mk, coeff_mk
-/
lemma coeff_genFun (f : Nat -> Nat -> R) (n : Nat) :
    (genFun f).coeff n = ∑ p : n.Partition, p.parts.toFinsupp.prod f :=
  PowerSeries.coeff_mk _ _

/--
theorem `tendsto_order_genFun_term_atTop_nhds_top` / 定理 `tendsto_order_genFun_term_atTop_nhds_top`

English:
theorem tendsto_order_genFun_term_atTop_nhds_top
  given: (f : Nat -> Nat -> R) (i : Nat)
  proof: by
  refine ENat.tendsto_nhds_top_iff_natCast_lt.mpr (fun n => Filter.eventually_atTop.mpr ⟨n, ?_⟩)
  intro m hm
  grw [PowerSeries.smul_eq_C_mul, ← le_order_mul]
  refine lt_add_of_nonneg_of_lt (by simp) ?_
  nontriviality R using Subsingleton.eq_zero (α := R⟦X⟧)
  rw [order_X_pow]
  norm_cast
  gr

中文:
定理 tendsto_order_genFun_term_atTop_nhds_top
  条件: (f : 自然数 -> 自然数 -> R) (i : 自然数)
  证明: by
  refine ENat.tendsto_nhds_top_iff_natCast_lt.mpr (fun n => Filter.eventually_atTop.mpr ⟨n, ?_⟩)
  intro m hm
  grw [PowerSeries.smul_eq_C_mul, ← le_order_mul]
  refine lt_add_of_nonneg_of_lt (by simp) ?_
  nontriviality R using Subsingleton.eq_zero (α := R⟦X⟧)
  rw [order_X_pow]
  norm_cast
  gr

Depends on / 依赖: ENat.tendsto_nhds_top_iff_natCast_lt.mpr, Filter, Filter.eventually_atTop.mpr, PowerSeries, PowerSeries.smul_eq_C_mul, Subsingleton, Subsingleton.eq_zero, eq_zero, eventually_atTop, le_order_mul, lt_add_of_nonneg_of_lt, nontriviality, order_X_pow, smul_eq_C_mul, tendsto_nhds_top_iff_natCast_lt
-/
theorem tendsto_order_genFun_term_atTop_nhds_top (f : Nat -> Nat -> R) (i : Nat) :
    Filter.Tendsto (fun j => (f (i + 1) (j + 1) • (X : R⟦X⟧) ^ ((i + 1) * (j + 1))).order)
    Filter.atTop (nhds ⊤) := by
  refine ENat.tendsto_nhds_top_iff_natCast_lt.mpr (fun n => Filter.eventually_atTop.mpr ⟨n, ?_⟩)
  intro m hm
  grw [PowerSeries.smul_eq_C_mul, ← le_order_mul]
  refine lt_add_of_nonneg_of_lt (by simp) ?_
  nontriviality R using Subsingleton.eq_zero (α := R⟦X⟧)
  rw [order_X_pow]
  norm_cast
  grind

variable [TopologicalSpace R]

/--
theorem `summable_genFun_term` / 定理 `summable_genFun_term`

English:
theorem summable_genFun_term
  given: (f : Nat -> Nat -> R) (i : Nat)
  proof: by
  apply WithPiTopology.summable_of_tendsto_order_atTop_nhds_top
  apply tendsto_order_genFun_term_atTop_nhds_top

中文:
定理 summable_genFun_term
  条件: (f : 自然数 -> 自然数 -> R) (i : 自然数)
  证明: by
  apply WithPiTopology.summable_of_tendsto_order_atTop_nhds_top
  apply tendsto_order_genFun_term_atTop_nhds_top

Depends on / 依赖: WithPiTopology, WithPiTopology.summable_of_tendsto_order_atTop_nhds_top, summable_of_tendsto_order_atTop_nhds_top, tendsto_order_genFun_term_atTop_nhds_top
-/
theorem summable_genFun_term (f : Nat -> Nat -> R) (i : Nat) :
    Summable fun j => f (i + 1) (j + 1) • (X : R⟦X⟧) ^ ((i + 1) * (j + 1)) := by
  apply WithPiTopology.summable_of_tendsto_order_atTop_nhds_top
  apply tendsto_order_genFun_term_atTop_nhds_top

/--
theorem `summable_genFun_term'` / 定理 `summable_genFun_term'`

English:
theorem summable_genFun_term'
  given: (f : Nat -> Nat -> R) {i : Nat} (hi : i != 0)
  proof: by
  obtain ⟨a, rfl⟩ := Nat.exists_eq_add_one_of_ne_zero hi
  apply summable_genFun_term

中文:
定理 summable_genFun_term'
  条件: (f : 自然数 -> 自然数 -> R) {i : 自然数} (hi : i != 0)
  证明: by
  obtain ⟨a, rfl⟩ := Nat.exists_eq_add_one_of_ne_zero hi
  apply summable_genFun_term

Depends on / 依赖: Nat.exists_eq_add_one_of_ne_zero, exists_eq_add_one_of_ne_zero, summable_genFun_term
-/
theorem summable_genFun_term' (f : Nat -> Nat -> R) {i : Nat} (hi : i != 0) :
    Summable fun j => f i (j + 1) • (X : R⟦X⟧) ^ (i * (j + 1)) := by
  obtain ⟨a, rfl⟩ := Nat.exists_eq_add_one_of_ne_zero hi
  apply summable_genFun_term

variable [T2Space R]

/--
theorem `aux_dvd_of_coeff_ne_zero` / 定理 `aux_dvd_of_coeff_ne_zero`

English:
theorem aux_dvd_of_coeff_ne_zero
  statement: {f : Nat -> Nat -> R} {d : Nat} {s : Finset Nat} (hs0 : 0 ∉ s)
  proof: by
  by_cases hx : x in s
  · specialize hprod x hx
    contrapose hprod
    have hx0 : x != 0 := fun h => hs0 (h ▸ hx)
    rw [map_add]; rw [(summable_genFun_term' f hx0).map_tsum _ (WithPiTopology.continuous_coeff _ _)]
    rw [show (0 : R) = 0 + ∑' (i : Nat)]; rw [0 by simp]
    congrm (?_ + ∑' (

中文:
定理 aux_dvd_of_coeff_ne_zero
  结论: {f : 自然数 -> 自然数 -> R} {d : 自然数} {s : 有限集 自然数} (hs0 : 0 ∉ s)
  证明: by
  by_cases hx : x in s
  · specialize hprod x hx
    contrapose hprod
    have hx0 : x != 0 := fun h => hs0 (h ▸ hx)
    rw [map_add]; rw [(summable_genFun_term' f hx0).map_tsum _ (WithPiTopology.continuous_coeff _ _)]
    rw [show (0 : R) = 0 + ∑' (i : Nat)]; rw [0 by simp]
    congrm (?_ + ∑' (
-/
private theorem aux_dvd_of_coeff_ne_zero {f : Nat -> Nat -> R} {d : Nat} {s : Finset Nat} (hs0 : 0 ∉ s)
    {g : Nat ->₀ Nat} (hg : g in s.finsuppAntidiag d)
    (hprod : forall i in s, (coeff (g i)) (1 + ∑' j, f i (j + 1) • X ^ (i * (j + 1))) != (0 : R)) (x : Nat) :
    x ∣ g x := by
  by_cases hx : x in s
  · specialize hprod x hx
    contrapose hprod
    have hx0 : x != 0 := fun h => hs0 (h ▸ hx)
    rw [map_add]; rw [(summable_genFun_term' f hx0).map_tsum _ (WithPiTopology.continuous_coeff _ _)]
    rw [show (0 : R) = 0 + ∑' (i : Nat)]; rw [0 by simp]
    congrm (?_ + ∑' (i : Nat), ?_)
    · suffices g x != 0 by simp [this]
      contrapose hprod
      simp [hprod]
    · rw [map_smul, coeff_X_pow]
      apply smul_eq_zero_of_right
      suffices g x != x * (i + 1) by simp [this]
      contrapose hprod
      simp [hprod]
  · suffices g x = 0 by simp [this]
    contrapose! hx
exact mem_of_subset (mem_finsuppAntidiag.mp hg).2 by simpa using hx

/--
theorem `aux_prod_coeff_eq_zero_of_notMem_range` / 定理 `aux_prod_coeff_eq_zero_of_notMem_range`

English:
theorem aux_prod_coeff_eq_zero_of_notMem_range
  statement: (f : Nat -> Nat -> R) {d : Nat} {s : Finset Nat}
  proof: by
  suffices exists i in s, (coeff (g i)) ((1 : R⟦X⟧) + ∑' j, f i (j + 1) • X ^ (i * (j + 1))) = 0 by
    obtain ⟨i, hi, hi'⟩ := this
    apply prod_eq_zero hi hi'
  contrapose! hg' with hprod
  rw [Set.mem_range]
  have hgne0 (i : Nat) : g i != 0 ↔ i != 0 ∧ i <= g i := by
    refine ⟨fun h => ⟨?_,

中文:
定理 aux_prod_coeff_eq_zero_of_notMem_range
  结论: (f : 自然数 -> 自然数 -> R) {d : 自然数} {s : 有限集 自然数}
  证明: by
  suffices exists i in s, (coeff (g i)) ((1 : R⟦X⟧) + ∑' j, f i (j + 1) • X ^ (i * (j + 1))) = 0 by
    obtain ⟨i, hi, hi'⟩ := this
    apply prod_eq_zero hi hi'
  contrapose! hg' with hprod
  rw [Set.mem_range]
  have hgne0 (i : Nat) : g i != 0 ↔ i != 0 ∧ i <= g i := by
    refine ⟨fun h => ⟨?_,
-/
private theorem aux_prod_coeff_eq_zero_of_notMem_range (f : Nat -> Nat -> R) {d : Nat} {s : Finset Nat}
    (hs0 : 0 ∉ s) {g : Nat ->₀ Nat} (hg : g in s.finsuppAntidiag d)
    (hg' : g ∉ Set.range (toFinsuppAntidiag (n := d))) :
    ∏ i in s, (coeff (g i)) (1 + ∑' j, f i (j + 1) • X ^ (i * (j + 1)) : R⟦X⟧) = 0 := by
  suffices exists i in s, (coeff (g i)) ((1 : R⟦X⟧) + ∑' j, f i (j + 1) • X ^ (i * (j + 1))) = 0 by
    obtain ⟨i, hi, hi'⟩ := this
    apply prod_eq_zero hi hi'
  contrapose! hg' with hprod
  rw [Set.mem_range]
  have hgne0 (i : Nat) : g i != 0 ↔ i != 0 ∧ i <= g i := by
    refine ⟨fun h => ⟨?_, ?_⟩, by grind⟩
    · contrapose hs0 with rfl
      exact mem_of_subset (mem_finsuppAntidiag.mp hg).2 (by simpa using h)
· exact Nat.le_of_dvd (Nat.pos_of_ne_zero h) aux_dvd_of_coeff_ne_zero hs0 hg hprod _
  refine ⟨Nat.Partition.mk (Finsupp.mk g.support (fun i => g i / i) ?_).toMultiset ?_ ?_, ?_⟩
  · simpa using hgne0
  · suffices forall i, g i != 0 -> i != 0 by simpa [Nat.pos_iff_ne_zero]
    exact fun i h => ((hgne0 i).mp h).1
  · obtain ⟨h1, h2⟩ := mem_finsuppAntidiag.mp hg
    refine Eq.trans ?_ h1
    suffices ∑ x in g.support, g x / x * x = ∑ x in s, g x by simpa [Finsupp.sum]
    apply sum_subset_zero_on_sdiff h2 (by simp)
exact fun x hx => Nat.div_mul_cancel aux_dvd_of_coeff_ne_zero hs0 hg hprod x
  · ext x
simpa [toFinsuppAntidiag] using Nat.div_mul_cancel aux_dvd_of_coeff_ne_zero hs0 hg hprod x

/--
theorem `aux_prod_f_eq_prod_coeff` / 定理 `aux_prod_f_eq_prod_coeff`

English:
theorem aux_prod_f_eq_prod_coeff
  statement: (f : Nat -> Nat -> R) {n : Nat} (p : Partition n) {s : Finset Nat}
  proof: by
  simp_rw [Finsupp.prod, Multiset.toFinsupp_support, Multiset.toFinsupp_apply]
  apply prod_subset_one_on_sdiff
  · grind
  · intro x hx
    rw [mem_sdiff]; rw [Multiset.mem_toFinset] at hx
    have hx0 : x != 0 := fun h => hs0 (h ▸ hx.1)
    have hsum := (summable_genFun_term' f hx0).map_tsum _


中文:
定理 aux_prod_f_eq_prod_coeff
  结论: (f : 自然数 -> 自然数 -> R) {n : 自然数} (p : 分拆 n) {s : 有限集 自然数}
  证明: by
  simp_rw [Finsupp.prod, Multiset.toFinsupp_support, Multiset.toFinsupp_apply]
  apply prod_subset_one_on_sdiff
  · grind
  · intro x hx
    rw [mem_sdiff]; rw [Multiset.mem_toFinset] at hx
    have hx0 : x != 0 := fun h => hs0 (h ▸ hx.1)
    have hsum := (summable_genFun_term' f hx0).map_tsum _

-/
private theorem aux_prod_f_eq_prod_coeff (f : Nat -> Nat -> R) {n : Nat} (p : Partition n) {s : Finset Nat}
    (hs : Icc 1 n subseteq s) (hs0 : 0 ∉ s) :
    p.parts.toFinsupp.prod f =
    ∏ i in s, coeff (p.toFinsuppAntidiag i) (1 + ∑' j, f i (j + 1) • X ^ (i * (j + 1))) := by
  simp_rw [Finsupp.prod, Multiset.toFinsupp_support, Multiset.toFinsupp_apply]
  apply prod_subset_one_on_sdiff
  · grind
  · intro x hx
    rw [mem_sdiff]; rw [Multiset.mem_toFinset] at hx
    have hx0 : x != 0 := fun h => hs0 (h ▸ hx.1)
    have hsum := (summable_genFun_term' f hx0).map_tsum _
      (WithPiTopology.continuous_constantCoeff R)
    simp [toFinsuppAntidiag, hsum, hx.2, hx0]
  · intro i hi
    rw [Multiset.mem_toFinset] at hi
    have hi0 : i != 0 := (p.parts_pos hi).ne.symm
    rw [map_add]; rw [(summable_genFun_term' f hi0).map_tsum _ (WithPiTopology.continuous_coeff _ _)]
    suffices f i (Multiset.count i p.parts) =
        ∑' j, if Multiset.count i p.parts * i = i * (j + 1) then f i (j + 1) else 0 by
      simpa [toFinsuppAntidiag, hi, hi0, coeff_X_pow]
    rw [tsum_eq_single (Multiset.count i p.parts - 1) ?_]
    · rw [mul_comm]
      simp [Nat.sub_add_cancel (Multiset.one_le_count_iff_mem.mpr hi)]
    intro b hb
    suffices Multiset.count i p.parts * i != i * (b + 1) by simp [this]
    rw [mul_comm i]; rw [(mul_left_inj' (Nat.ne_zero_of_lt (p.parts_pos hi))).ne]
    grind

/--
theorem `hasProd_genFun` / 定理 `hasProd_genFun`

English:
theorem hasProd_genFun
  given: (f : Nat -> Nat -> R)
  proof: by
  rw [HasProd]; rw [WithPiTopology.tendsto_iff_coeff_tendsto]
  refine fun d => tendsto_atTop_of_eventually_const (fun s (hs : s >= range d) => ?_)
  have : ∏ i in s, ((1 : R⟦X⟧) + ∑' j, f (i + 1) (j + 1) • X ^ ((i + 1) * (j + 1)))
      = ∏ i in s.map (addRightEmbedding 1), (1 + ∑' j, f i (j + 1

中文:
定理 hasProd_genFun
  条件: (f : 自然数 -> 自然数 -> R)
  证明: by
  rw [HasProd]; rw [WithPiTopology.tendsto_iff_coeff_tendsto]
  refine fun d => tendsto_atTop_of_eventually_const (fun s (hs : s >= range d) => ?_)
  have : ∏ i in s, ((1 : R⟦X⟧) + ∑' j, f (i + 1) (j + 1) • X ^ ((i + 1) * (j + 1)))
      = ∏ i in s.map (addRightEmbedding 1), (1 + ∑' j, f i (j + 1

Depends on / 依赖: HasProd, WithPiTopology, WithPiTopology.tendsto_iff_coeff_tendsto, addRightEmbedding, mem_of_su, s.map, subseteq, tendsto_atTop_of_eventually_const, tendsto_iff_coeff_tendsto
-/
theorem hasProd_genFun (f : Nat -> Nat -> R) :
    HasProd (fun i => 1 + ∑' j, f (i + 1) (j + 1) • X ^ ((i + 1) * (j + 1))) (genFun f) := by
  rw [HasProd]; rw [WithPiTopology.tendsto_iff_coeff_tendsto]
  refine fun d => tendsto_atTop_of_eventually_const (fun s (hs : s >= range d) => ?_)
  have : ∏ i in s, ((1 : R⟦X⟧) + ∑' j, f (i + 1) (j + 1) • X ^ ((i + 1) * (j + 1)))
      = ∏ i in s.map (addRightEmbedding 1), (1 + ∑' j, f i (j + 1) • X ^ (i * (j + 1))) := by simp
  rw [this]
  have hs : Icc 1 d subseteq s.map (addRightEmbedding 1) := by
    intro i
    suffices 1 <= i -> i <= d -> exists a in s, a + 1 = i by simpa
    intro h1 h2
    refine ⟨i - 1, mem_of_subset hs ?_, ?_⟩ <;> grind
  rw [coeff_genFun]; rw [coeff_prod]
  refine (sum_of_injOn toFinsuppAntidiag (toFinsuppAntidiag_injective d).injOn ?_ ?_ ?_).symm
  · intro p _
    exact mem_of_subset (finsuppAntidiag_mono hs _) p.toFinsuppAntidiag_mem_finsuppAntidiag
  · exact fun g hg hg' => aux_prod_coeff_eq_zero_of_notMem_range f (by simp) hg (by simpa using hg')
  · exact fun p _ => aux_prod_f_eq_prod_coeff f p hs (by simp)

/--
theorem `multipliable_genFun` / 定理 `multipliable_genFun`

English:
theorem multipliable_genFun
  given: (f : Nat -> Nat -> R)
  proof: (hasProd_genFun f).multipliable

中文:
定理 multipliable_genFun
  条件: (f : 自然数 -> 自然数 -> R)
  证明: (hasProd_genFun f).multipliable

Depends on / 依赖: hasProd_genFun, multipliable
-/
theorem multipliable_genFun (f : Nat -> Nat -> R) :
    Multipliable fun i => (1 : R⟦X⟧) + ∑' j, f (i + 1) (j + 1) • X ^ ((i + 1) * (j + 1)) :=
  (hasProd_genFun f).multipliable

/--
theorem `genFun_eq_tprod` / 定理 `genFun_eq_tprod`

English:
theorem genFun_eq_tprod
  given: (f : Nat -> Nat -> R)
  proof: (hasProd_genFun f).tprod_eq.symm

中文:
定理 genFun_eq_tprod
  条件: (f : 自然数 -> 自然数 -> R)
  证明: (hasProd_genFun f).tprod_eq.symm

Depends on / 依赖: hasProd_genFun, tprod_eq, tprod_eq.symm
-/
theorem genFun_eq_tprod (f : Nat -> Nat -> R) :
    genFun f = ∏' i, (1 + ∑' j, f (i + 1) (j + 1) • X ^ ((i + 1) * (j + 1))) :=
  (hasProd_genFun f).tprod_eq.symm

end Nat.Partition
