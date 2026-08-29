/-
Copyright (c) 2018 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl
-/
module

public import Mathlib.Algebra.Group.TypeTags.Finite
public import Mathlib.Algebra.Order.Hom.TypeTags
public import Mathlib.Data.Nat.Totient
public import Mathlib.Data.ZMod.Aut
public import Mathlib.GroupTheory.Exponent
public import Mathlib.GroupTheory.SpecificGroups.Cyclic.Basic
public import Mathlib.GroupTheory.Subgroup.Simple
public import Mathlib.Tactic.Group
public import Mathlib.Tactic.IntervalCases

/-!
# Further properties of cyclic groups

## Main statements

* `isSimpleGroup_of_prime_card`, `IsSimpleGroup.isCyclic`,
  and `IsSimpleGroup.prime_card` classify finite simple abelian groups.
* `IsCyclic.card_orderOf_eq_totient` computes the number of elements of given order
  in a cyclic group.
* `IsCyclic.exponent_eq_card`: For a finite cyclic group `G`, the exponent is equal to
  the group's cardinality.
* `IsCyclic.exponent_eq_zero_of_infinite`: Infinite cyclic groups have exponent zero.
* `IsCyclic.iff_exponent_eq_card`: A finite commutative group is cyclic iff its exponent
  is equal to its cardinality.
* `IsCyclic.card_mulAut`, cardinality of automorphisms of a finite group.
* `commGroupOfCyclicCenterQuotient`: if the quotient of a group by
  its center is cyclic, then the group is commutative.
* `Group.isCyclic_prod_iff`: the product of two finite cyclic groups is cyclic
  if and only if their orders are relatively prime.

## Tags

cyclic group, exponent, totient
-/

@[expose] public section

assert_not_exists Ideal TwoSidedIdeal

variable {α G G' : Type*} {a : α}

section Cyclic

open Subgroup

variable [Group α] [Group G] [Group G']

open Finset Nat

section Totient

variable [DecidableEq α] [Fintype α] (hn : forall n : Nat, 0 < n -> #{a : α | a ^ n = 1} <= n)
include hn

@[to_additive]
/--
theorem `card_pow_eq_one_eq_orderOf_aux` / 定理 `card_pow_eq_one_eq_orderOf_aux`

English:
theorem card_pow_eq_one_eq_orderOf_aux
  given: (a : α)
  statement: #{b : α | b ^ orderOf a = 1} = orderOf a
  proof: le_antisymm (hn _ (orderOf_pos a))
    (calc
      orderOf a = @Fintype.card (zpowers a) (id _) := Fintype.card_zpowers.symm
      _ <=
          @Fintype.card (({b : α | b ^ orderOf a = 1} : Finset _) : Set α)
            (Fintype.ofFinset _ fun _ => Iff.rfl) :=
        (@Fintype.card_le_of_injecti

中文:
定理 card_pow_eq_one_eq_orderOf_aux
  条件: (a : α)
  结论: #{b : α | b ^ orderOf a = 1} = orderOf a
  证明: le_antisymm (hn _ (orderOf_pos a))
    (calc
      orderOf a = @Fintype.card (zpowers a) (id _) := Fintype.card_zpowers.symm
      _ <=
          @Fintype.card (({b : α | b ^ orderOf a = 1} : Finset _) : Set α)
            (Fintype.ofFinset _ fun _ => Iff.rfl) :=
        (@Fintype.card_le_of_injecti
-/
private theorem card_pow_eq_one_eq_orderOf_aux (a : α) : #{b : α | b ^ orderOf a = 1} = orderOf a :=
  le_antisymm (hn _ (orderOf_pos a))
    (calc
      orderOf a = @Fintype.card (zpowers a) (id _) := Fintype.card_zpowers.symm
      _ <=
          @Fintype.card (({b : α | b ^ orderOf a = 1} : Finset _) : Set α)
            (Fintype.ofFinset _ fun _ => Iff.rfl) :=
        (@Fintype.card_le_of_injective (zpowers a)
          (({b : α | b ^ orderOf a = 1} : Finset _) : Set α) (id _) (id _)
          (fun b =>
            ⟨b.1,
              mem_filter.2
                ⟨mem_univ _, by
                  let ⟨i, hi⟩ := b.2
                  rw [← hi]; rw [← zpow_natCast]; rw [← zpow_mul]; rw [mul_comm]; rw [zpow_mul]; rw [zpow_natCast]; rw [pow_orderOf_eq_one]; rw [one_zpow]⟩⟩)
          fun _ _ h => Subtype.ext (Subtype.mk.inj h))
      _ = #{b : α | b ^ orderOf a = 1} := Fintype.card_ofFinset _ _)

-- Use φ for `Nat.totient`
open Nat
@[to_additive]
/--
theorem `card_orderOf_eq_totient_aux₁` / 定理 `card_orderOf_eq_totient_aux₁`

English:
theorem card_orderOf_eq_totient_aux₁
  statement: {d : Nat} (hd : d ∣ Fintype.card α)
  proof: by
  induction d using Nat.strong_induction_on with | _ d IH
  rcases Decidable.eq_or_ne d 0 with (rfl | hd0)
  · cases Fintype.card_ne_zero (eq_zero_of_zero_dvd hd)
  rcases Finset.card_pos.1 hpos with ⟨a, ha'⟩
  have ha : orderOf a = d := (mem_filter.1 ha').2
  have h1 :
    (∑ m in d.properDiviso

中文:
定理 card_orderOf_eq_totient_aux₁
  结论: {d : 自然数} (hd : d ∣ Fintype.card α)
  证明: by
  induction d using Nat.strong_induction_on with | _ d IH
  rcases Decidable.eq_or_ne d 0 with (rfl | hd0)
  · cases Fintype.card_ne_zero (eq_zero_of_zero_dvd hd)
  rcases Finset.card_pos.1 hpos with ⟨a, ha'⟩
  have ha : orderOf a = d := (mem_filter.1 ha').2
  have h1 :
    (∑ m in d.properDiviso
-/
private theorem card_orderOf_eq_totient_aux₁ {d : Nat} (hd : d ∣ Fintype.card α)
    (hpos : 0 < #{a : α | orderOf a = d}) : #{a : α | orderOf a = d} = φ d := by
  induction d using Nat.strong_induction_on with | _ d IH
  rcases Decidable.eq_or_ne d 0 with (rfl | hd0)
  · cases Fintype.card_ne_zero (eq_zero_of_zero_dvd hd)
  rcases Finset.card_pos.1 hpos with ⟨a, ha'⟩
  have ha : orderOf a = d := (mem_filter.1 ha').2
  have h1 :
    (∑ m in d.properDivisors, #{a : α | orderOf a = m}) =
      ∑ m in d.properDivisors, φ m := by
    refine Finset.sum_congr rfl fun m hm => ?_
    simp only [mem_properDivisors] at hm
    refine IH m hm.2 (hm.1.trans hd) (Finset.card_pos.2 ⟨a ^ (d / m), ?_⟩)
    rw [mem_filter_univ]; rw [orderOf_pow a]; rw [ha]; rw [Nat.gcd_eq_right (div_dvd_of_dvd hm.1)]; rw [Nat.div_div_self hm.1 hd0]
  have h2 :
    (∑ m in d.divisors, #{a : α | orderOf a = m}) =
      ∑ m in d.divisors, φ m := by
    rw [sum_card_orderOf_eq_card_pow_eq_one hd0]; rw [sum_totient]; rw [← ha]; rw [card_pow_eq_one_eq_orderOf_aux hn a]
  simpa [← cons_self_properDivisors hd0, ← h1] using h2

@[to_additive]
/--
theorem `card_orderOf_eq_totient_aux₂` / 定理 `card_orderOf_eq_totient_aux₂`

English:
theorem card_orderOf_eq_totient_aux₂
  given: {d : Nat} (hd : d ∣ Fintype.card α)
  proof: by
  let c := Fintype.card α
  have hc0 : 0 < c := Fintype.card_pos_iff.2 ⟨1⟩
  apply card_orderOf_eq_totient_aux₁ hn hd
  by_contra h0
  -- Must qualify `Finset.card_eq_zero` because of https://github.com/leanprover/lean4/issues/2849
  simp_rw [not_lt, Nat.le_zero, Finset.card_eq_zero] at h0
  appl

中文:
定理 card_orderOf_eq_totient_aux₂
  条件: {d : 自然数} (hd : d ∣ Fintype.card α)
  证明: by
  let c := Fintype.card α
  have hc0 : 0 < c := Fintype.card_pos_iff.2 ⟨1⟩
  apply card_orderOf_eq_totient_aux₁ hn hd
  by_contra h0
  -- Must qualify `Finset.card_eq_zero` because of https://github.com/leanprover/lean4/issues/2849
  simp_rw [not_lt, Nat.le_zero, Finset.card_eq_zero] at h0
  appl

Depends on / 依赖: Fintype, Fintype.card, Fintype.card_pos_iff, card_pos_iff
-/
theorem card_orderOf_eq_totient_aux₂ {d : Nat} (hd : d ∣ Fintype.card α) :
    #{a : α | orderOf a = d} = φ d := by
  let c := Fintype.card α
  have hc0 : 0 < c := Fintype.card_pos_iff.2 ⟨1⟩
  apply card_orderOf_eq_totient_aux₁ hn hd
  by_contra h0
  -- Must qualify `Finset.card_eq_zero` because of https://github.com/leanprover/lean4/issues/2849
  simp_rw [not_lt, Nat.le_zero, Finset.card_eq_zero] at h0
  apply lt_irrefl c
  calc
    c = ∑ m in c.divisors, #{a : α | orderOf a = m} := by
      simp only [sum_card_orderOf_eq_card_pow_eq_one hc0.ne']
      apply congr_arg card
      simp [c]
    _ = ∑ m in c.divisors.erase d, #{a : α | orderOf a = m} := by
      rw [eq_comm]
      refine sum_subset (erase_subset _ _) fun m hm₁ hm₂ => ?_
      have : m = d := by
        contrapose! hm₂
        exact mem_erase_of_ne_of_mem hm₂ hm₁
      simp [this, h0]
    _ <= ∑ m in c.divisors.erase d, φ m := by
      gcongr with m hm
      have hmc : m ∣ c := by
        simp only [mem_erase, mem_divisors] at hm
        tauto
      obtain h1 | h1 := (#{a : α | orderOf a = m}).eq_zero_or_pos
      · simp [h1]
      · simp [card_orderOf_eq_totient_aux₁ hn hmc h1]
    _ < ∑ m in c.divisors, φ m :=
      sum_erase_lt_of_pos (mem_divisors.2 ⟨hd, hc0.ne'⟩) (totient_pos.2 (pos_of_dvd_of_pos hd hc0))
    _ = c := sum_totient _

@[to_additive isAddCyclic_of_card_nsmul_eq_zero_le, stacks 09HX "This theorem is stronger than \
09HX. It removes the abelian condition, and requires only `<=` instead of `=`."]
/--
theorem `isCyclic_of_card_pow_eq_one_le` / 定理 `isCyclic_of_card_pow_eq_one_le`

English:
theorem isCyclic_of_card_pow_eq_one_le
  statement: IsCyclic α
  proof: have : Finset.Nonempty {a : α | orderOf a = Nat.card α} :=
card_pos.1 by
      rw [Nat.card_eq_fintype_card]; rw [card_orderOf_eq_totient_aux₂ hn dvd_rfl]; rw [totient_pos]
      apply Fintype.card_pos
  let ⟨x, hx⟩ := this
  isCyclic_of_orderOf_eq_card x (Finset.mem_filter.1 hx).2

中文:
定理 isCyclic_of_card_pow_eq_one_le
  结论: IsCyclic α
  证明: have : Finset.Nonempty {a : α | orderOf a = Nat.card α} :=
card_pos.1 by
      rw [Nat.card_eq_fintype_card]; rw [card_orderOf_eq_totient_aux₂ hn dvd_rfl]; rw [totient_pos]
      apply Fintype.card_pos
  let ⟨x, hx⟩ := this
  isCyclic_of_orderOf_eq_card x (Finset.mem_filter.1 hx).2

Depends on / 依赖: Finset, Finset.Nonempty, Finset.mem_filter, Fintype, Fintype.card_pos, Nat.card, Nat.card_eq_fintype_card, Nonempty, card_eq_fintype_card, card_pos, dvd_rfl, isCyclic_of_orderOf_eq_card, mem_filter, orderOf, totient_pos
-/
theorem isCyclic_of_card_pow_eq_one_le : IsCyclic α :=
  have : Finset.Nonempty {a : α | orderOf a = Nat.card α} :=
card_pos.1 by
      rw [Nat.card_eq_fintype_card]; rw [card_orderOf_eq_totient_aux₂ hn dvd_rfl]; rw [totient_pos]
      apply Fintype.card_pos
  let ⟨x, hx⟩ := this
  isCyclic_of_orderOf_eq_card x (Finset.mem_filter.1 hx).2

end Totient

@[to_additive]
/--
lemma `IsCyclic.card_orderOf_eq_totient` / 引理 `IsCyclic.card_orderOf_eq_totient`

English:
lemma IsCyclic.card_orderOf_eq_totient
  given: [IsCyclic α] [Fintype α] {d : Nat} (hd : d ∣ Fintype.card α)
  proof: by
  classical apply card_orderOf_eq_totient_aux₂ (fun n => IsCyclic.card_pow_eq_one_le) hd

中文:
引理 IsCyclic.card_orderOf_eq_totient
  条件: [IsCyclic α] [Fintype α] {d : 自然数} (hd : d ∣ Fintype.card α)
  证明: by
  classical apply card_orderOf_eq_totient_aux₂ (fun n => IsCyclic.card_pow_eq_one_le) hd

Depends on / 依赖: IsCyclic, IsCyclic.card_pow_eq_one_le, card_pow_eq_one_le, classical
-/
lemma IsCyclic.card_orderOf_eq_totient [IsCyclic α] [Fintype α] {d : Nat} (hd : d ∣ Fintype.card α) :
    #{a : α | orderOf a = d} = totient d := by
  classical apply card_orderOf_eq_totient_aux₂ (fun n => IsCyclic.card_pow_eq_one_le) hd

/-- A finite group of prime order is simple. -/
@[to_additive /-- A finite group of prime order is simple. -/]
/--
theorem `isSimpleGroup_of_prime_card` / 定理 `isSimpleGroup_of_prime_card`

English:
theorem isSimpleGroup_of_prime_card
  statement: {p : Nat} [hp : Fact p.Prime]
  proof: by
  subst h
  have : Finite α := Nat.finite_of_card_ne_zero hp.1.ne_zero
  have : Nontrivial α := Finite.one_lt_card_iff_nontrivial.mp hp.1.one_lt
  exact ⟨fun H _ => H.eq_bot_or_eq_top_of_prime_card⟩

中文:
定理 isSimpleGroup_of_prime_card
  结论: {p : 自然数} [hp : Fact p.Prime]
  证明: by
  subst h
  have : Finite α := Nat.finite_of_card_ne_zero hp.1.ne_zero
  have : Nontrivial α := Finite.one_lt_card_iff_nontrivial.mp hp.1.one_lt
  exact ⟨fun H _ => H.eq_bot_or_eq_top_of_prime_card⟩

Depends on / 依赖: Finite, Finite.one_lt_card_iff_nontrivial.mp, H.eq_bot_or_eq_top_of_prime_card, Nat.finite_of_card_ne_zero, Nontrivial, eq_bot_or_eq_top_of_prime_card, finite_of_card_ne_zero, ne_zero, one_lt, one_lt_card_iff_nontrivial
-/
theorem isSimpleGroup_of_prime_card {p : Nat} [hp : Fact p.Prime]
    (h : Nat.card α = p) : IsSimpleGroup α := by
  subst h
  have : Finite α := Nat.finite_of_card_ne_zero hp.1.ne_zero
  have : Nontrivial α := Finite.one_lt_card_iff_nontrivial.mp hp.1.one_lt
  exact ⟨fun H _ => H.eq_bot_or_eq_top_of_prime_card⟩

end Cyclic

section QuotientCenter

open Subgroup

variable [Group G] [Group G']

/-- A group is commutative if the quotient by the center is cyclic.
  Also see `commGroupOfCyclicCenterQuotient` for the `CommGroup` instance. -/
@[to_additive
/-- A group is commutative if the quotient by the center is cyclic.
Also see `addCommGroupOfCyclicCenterQuotient` for the `AddCommGroup` instance. -/]
/--
theorem `MonoidHom.isMulCommutative_of_isCyclic_of_ker_le_center` / 定理 `MonoidHom.isMulCommutative_of_isCyclic_of_ker_le_center`

English:
theorem MonoidHom.isMulCommutative_of_isCyclic_of_ker_le_center
  statement: [IsCyclic G'] (f : G ->* G')
  proof: by
  refine ⟨⟨fun a b => ?_⟩⟩
  let ⟨⟨x, y, (hxy : f y = x)⟩, (hx : forall a : f.range, a in zpowers _)⟩ :=
    IsCyclic.exists_generator (α := f.range)
  let ⟨m, hm⟩ := hx ⟨f a, a, rfl⟩
  let ⟨n, hn⟩ := hx ⟨f b, b, rfl⟩
  have hm : x ^ m = f a := by simpa [Subtype.ext_iff] using hm
  have hn : x ^ 

中文:
定理 MonoidHom.isMulCommutative_of_isCyclic_of_ker_le_center
  结论: [IsCyclic G'] (f : G ->* G')
  证明: by
  refine ⟨⟨fun a b => ?_⟩⟩
  let ⟨⟨x, y, (hxy : f y = x)⟩, (hx : forall a : f.range, a in zpowers _)⟩ :=
    IsCyclic.exists_generator (α := f.range)
  let ⟨m, hm⟩ := hx ⟨f a, a, rfl⟩
  let ⟨n, hn⟩ := hx ⟨f b, b, rfl⟩
  have hm : x ^ m = f a := by simpa [Subtype.ext_iff] using hm
  have hn : x ^ 

Depends on / 依赖: IsCyclic, IsCyclic.exists_generator, Subtype, Subtype.ext_iff, center, exists_generator, ext_iff, f.map_mul, f.map_zpow, f.mem_ker, f.range, inv_mul_cancel, map_mul, map_zpow, mem_ker, zpow_neg, zpowers
-/
theorem MonoidHom.isMulCommutative_of_isCyclic_of_ker_le_center [IsCyclic G'] (f : G ->* G')
    (hf : f.ker <= center G) : IsMulCommutative G := by
  refine ⟨⟨fun a b => ?_⟩⟩
  let ⟨⟨x, y, (hxy : f y = x)⟩, (hx : forall a : f.range, a in zpowers _)⟩ :=
    IsCyclic.exists_generator (α := f.range)
  let ⟨m, hm⟩ := hx ⟨f a, a, rfl⟩
  let ⟨n, hn⟩ := hx ⟨f b, b, rfl⟩
  have hm : x ^ m = f a := by simpa [Subtype.ext_iff] using hm
  have hn : x ^ n = f b := by simpa [Subtype.ext_iff] using hn
  have ha : y ^ (-m) * a in center G :=
    hf (by rw [f.mem_ker, f.map_mul, f.map_zpow, hxy, zpow_neg x m, hm, inv_mul_cancel])
  have hb : y ^ (-n) * b in center G :=
    hf (by rw [f.mem_ker, f.map_mul, f.map_zpow, hxy, zpow_neg x n, hn, inv_mul_cancel])
  calc
    a * b = y ^ m * (y ^ (-m) * a * y ^ n) * (y ^ (-n) * b) := by simp [mul_assoc]
    _ = y ^ m * (y ^ n * (y ^ (-m) * a)) * (y ^ (-n) * b) := by rw [mem_center_iff.1 ha]
    _ = y ^ m * y ^ n * y ^ (-m) * (a * (y ^ (-n) * b)) := by simp [mul_assoc]
    _ = y ^ m * y ^ n * y ^ (-m) * (y ^ (-n) * b * a) := by rw [mem_center_iff.1 hb]
    _ = b * a := by group

@[to_additive (attr := deprecated MonoidHom.isMulCommutative_of_isCyclic_of_ker_le_center
  (since := "2026-05-26"))]
/--
theorem `commutative_of_cyclic_center_quotient` / 定理 `commutative_of_cyclic_center_quotient`

English:
theorem commutative_of_cyclic_center_quotient
  statement: [IsCyclic G'] (f : G ->* G') (hf : f.ker <= center G)
  proof: .is_comm.comm a b f.isMulCommutative_of_isCyclic_of_ker_le_center hf

中文:
定理 commutative_of_cyclic_center_quotient
  结论: [IsCyclic G'] (f : G ->* G') (hf : f.ker <= center G)
  证明: .is_comm.comm a b f.isMulCommutative_of_isCyclic_of_ker_le_center hf

Depends on / 依赖: f.isMulCommutative_of_isCyclic_of_ker_le_center, isMulCommutative_of_isCyclic_of_ker_le_center, is_comm, is_comm.comm
-/
theorem commutative_of_cyclic_center_quotient [IsCyclic G'] (f : G ->* G') (hf : f.ker <= center G)
    (a b : G) : a * b = b * a :=
.is_comm.comm a b f.isMulCommutative_of_isCyclic_of_ker_le_center hf

/-- A group is commutative if the quotient by the center is cyclic. -/
@[to_additive (attr := instance_reducible)
/-- A group is commutative if the quotient by the center is cyclic. -/]
/--
Definition of `commGroupOfCyclicCenterQuotient` / `commGroupOfCyclicCenterQuotient` 的定义

English:
definition commGroupOfCyclicCenterQuotient
  signature: [IsCyclic G'] (f : G ->* G') (hf : f.ker <= center G)
  body: f.isMulCommutative_of_isCyclic_of_ker_le_center hf

中文:
定义 commGroupOfCyclicCenterQuotient
  签名: [IsCyclic G'] (f : G ->* G') (hf : f.ker <= center G)
  定义体: f.isMulCommutative_of_isCyclic_of_ker_le_center hf

Depends on / 依赖: f.isMulCommutative_of_isCyclic_of_ker_le_center, isMulCommutative_of_isCyclic_of_ker_le_center
-/
def commGroupOfCyclicCenterQuotient [IsCyclic G'] (f : G ->* G') (hf : f.ker <= center G) :
    CommGroup G where
.is_comm.comm mul_comm := f.isMulCommutative_of_isCyclic_of_ker_le_center hf

variable (G) in
/-- If the quotient by the center of a group is cyclic, then the group is commutative. -/
@[to_additive
/-- If the quotient by the center of a group is cyclic, then the group is commutative. -/]
/--
theorem `isMulCommutative_of_isCyclic_quotient_center_self` / 定理 `isMulCommutative_of_isCyclic_quotient_center_self`

English:
theorem isMulCommutative_of_isCyclic_quotient_center_self
  given: [IsCyclic (G ⧸ Subgroup.center G)]
  proof: by
  simp [(QuotientGroup.mk' <| .center G).isMulCommutative_of_isCyclic_of_ker_le_center]

中文:
定理 isMulCommutative_of_isCyclic_quotient_center_self
  条件: [IsCyclic (G ⧸ Subgroup.center G)]
  证明: by
  simp [(QuotientGroup.mk' <| .center G).isMulCommutative_of_isCyclic_of_ker_le_center]

Depends on / 依赖: QuotientGroup, QuotientGroup.mk, center, isMulCommutative_of_isCyclic_of_ker_le_center
-/
theorem isMulCommutative_of_isCyclic_quotient_center_self [IsCyclic (G ⧸ Subgroup.center G)] :
    IsMulCommutative G := by
  simp [(QuotientGroup.mk' <| .center G).isMulCommutative_of_isCyclic_of_ker_le_center]

end QuotientCenter

namespace IsSimpleGroup

section CommSimpleGroup

variable [CommGroup α] [IsSimpleGroup α]

@[to_additive]
instance (priority := 100) isCyclic : IsCyclic α := by
  nontriviality α
  obtain ⟨g, hg⟩ := exists_ne (1 : α)
  have : Subgroup.zpowers g = ⊤ :=
    (eq_bot_or_eq_top (Subgroup.zpowers g)).resolve_left (Subgroup.zpowers_ne_bot.2 hg)
  exact ⟨⟨g, (Subgroup.eq_top_iff' _).1 this⟩⟩

@[to_additive]
/--
theorem `prime_card` / 定理 `prime_card`

English:
theorem prime_card
  statement: (Nat.card α).Prime
  proof: by
  have hα : Nontrivial α := IsSimpleGroup.toNontrivial
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := α)
  replace hα : Nat.card α != 1 := by contrapose! hα; exact (Nat.card_eq_one_iff_unique.mp hα).1
  rw [← orderOf_eq_card_of_forall_mem_zpowers hg] at hα ⊢
  have h (n : Nat) : orderOf g ∣ 

中文:
定理 prime_card
  结论: (自然数.card α).Prime
  证明: by
  have hα : Nontrivial α := IsSimpleGroup.toNontrivial
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := α)
  replace hα : Nat.card α != 1 := by contrapose! hα; exact (Nat.card_eq_one_iff_unique.mp hα).1
  rw [← orderOf_eq_card_of_forall_mem_zpowers hg] at hα ⊢
  have h (n : Nat) : orderOf g ∣ 

Depends on / 依赖: Coprime, IsCyclic, IsCyclic.exists_generator, IsSimpleGroup, IsSimpleGroup.toNontrivial, IsSimpleOrder, IsSimpleOrder.eq_bot_or_eq_top, Nat.card, Nat.card_eq_one_iff_unique.mp, Nat.coprime_iff_gcd_eq_one, Nontrivial, Subgroup, Subgroup.zpowers, card_eq_one_iff_unique, contrapose, coprime_iff_gcd_eq_one, eq_bot_or_eq_top, exists_generator, n.Coprime, orderOf
-/
theorem prime_card : (Nat.card α).Prime := by
  have hα : Nontrivial α := IsSimpleGroup.toNontrivial
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := α)
  replace hα : Nat.card α != 1 := by contrapose! hα; exact (Nat.card_eq_one_iff_unique.mp hα).1
  rw [← orderOf_eq_card_of_forall_mem_zpowers hg] at hα ⊢
  have h (n : Nat) : orderOf g ∣ n ∨ n.Coprime (orderOf g) := by
    refine (IsSimpleOrder.eq_bot_or_eq_top (Subgroup.zpowers (g ^ n))).imp ?_ fun h => ?_
    · simp [orderOf_dvd_iff_pow_eq_one]
    · simp only [Nat.coprime_iff_gcd_eq_one]
      have hgn : g in Subgroup.zpowers (g ^ n) := by simp_all only [ne_eq, orderOf_eq_one_iff,
        Subgroup.mem_top]
      exact mem_zpowers_pow_iff.mp hgn
  apply Nat.prime_of_coprime
  · refine Nat.one_lt_iff_ne_zero_and_ne_one.mpr ⟨?_, hα⟩
    contrapose! h
    exact ⟨37, by simp [h]⟩
  · intro n hn hn0
    exact ((h n).resolve_left (Nat.not_dvd_of_pos_of_lt (Nat.pos_iff_ne_zero.mpr hn0) hn)).symm

/-- A commutative simple group is a finite group. -/
@[to_additive /-- A commutative simple group is a finite group. -/]
/--
theorem `finite` / 定理 `finite`

English:
theorem finite
  statement: Finite α
  proof: Nat.finite_of_card_ne_zero prime_card.ne_zero

中文:
定理 finite
  结论: Finite α
  证明: Nat.finite_of_card_ne_zero prime_card.ne_zero

Depends on / 依赖: Nat.finite_of_card_ne_zero, finite_of_card_ne_zero, ne_zero, prime_card, prime_card.ne_zero
-/
theorem finite : Finite α := Nat.finite_of_card_ne_zero prime_card.ne_zero

end CommSimpleGroup

end IsSimpleGroup

open scoped IsMulCommutative in
@[to_additive]
/--
theorem `Group.is_simple_iff_prime_card` / 定理 `Group.is_simple_iff_prime_card`

English:
theorem Group.is_simple_iff_prime_card
  given: [Group α] [IsMulCommutative α]
  proof: ⟨fun h => h.prime_card, fun h => isSimpleGroup_of_prime_card (hp := ⟨h⟩) rfl⟩

@[to_additive]

中文:
定理 Group.is_simple_iff_prime_card
  条件: [Group α] [IsMulCommutative α]
  证明: ⟨fun h => h.prime_card, fun h => isSimpleGroup_of_prime_card (hp := ⟨h⟩) rfl⟩

@[to_additive]

Depends on / 依赖: h.prime_card, isSimpleGroup_of_prime_card, prime_card
-/
theorem Group.is_simple_iff_prime_card [Group α] [IsMulCommutative α] :
    IsSimpleGroup α ↔ (Nat.card α).Prime :=
  ⟨fun h => h.prime_card, fun h => isSimpleGroup_of_prime_card (hp := ⟨h⟩) rfl⟩

@[to_additive]
/--
theorem `CommGroup.is_simple_iff_prime_card` / 定理 `CommGroup.is_simple_iff_prime_card`

English:
theorem CommGroup.is_simple_iff_prime_card
  given: [CommGroup α]
  statement: IsSimpleGroup α ↔ (Nat.card α).Prime
  proof: Group.is_simple_iff_prime_card

中文:
定理 CommGroup.is_simple_iff_prime_card
  条件: [CommGroup α]
  结论: IsSimpleGroup α ↔ (自然数.card α).Prime
  证明: Group.is_simple_iff_prime_card

Depends on / 依赖: Group.is_simple_iff_prime_card, is_simple_iff_prime_card
-/
theorem CommGroup.is_simple_iff_prime_card [CommGroup α] : IsSimpleGroup α ↔ (Nat.card α).Prime :=
  Group.is_simple_iff_prime_card

section SpecificInstances

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: IsAddCyclic Int
  body: ⟨1, fun n => ⟨n, by simp only [smul_eq_mul, mul_one]⟩⟩

中文:
实例 :
  签名: IsAddCyclic 整数
  定义体: ⟨1, fun n => ⟨n, by simp only [smul_eq_mul, mul_one]⟩⟩

Depends on / 依赖: mul_one, smul_eq_mul
-/
instance : IsAddCyclic Int := ⟨1, fun n => ⟨n, by simp only [smul_eq_mul, mul_one]⟩⟩

/--
Instance `ZMod.instIsAddCyclic` / 实例 `ZMod.instIsAddCyclic`

English:
instance ZMod.instIsAddCyclic
  signature: (n : Nat)
  body: isAddCyclic_of_surjective (Int.castRingHom _) ZMod.intCast_surjective

中文:
实例 ZMod.instIsAddCyclic
  签名: (n : 自然数)
  定义体: isAddCyclic_of_surjective (Int.castRingHom _) ZMod.intCast_surjective

Depends on / 依赖: Int.castRingHom, ZMod.intCast_surjective, castRingHom, intCast_surjective, isAddCyclic_of_surjective
-/
instance ZMod.instIsAddCyclic (n : Nat) : IsAddCyclic (ZMod n) :=
  isAddCyclic_of_surjective (Int.castRingHom _) ZMod.intCast_surjective

/--
Instance `ZMod.instIsSimpleAddGroup` / 实例 `ZMod.instIsSimpleAddGroup`

English:
instance ZMod.instIsSimpleAddGroup
  signature: {p : Nat} [hp : Fact p.Prime]
  body: AddCommGroup.is_simple_iff_prime_card.2 (by simpa using hp.out)

中文:
实例 ZMod.instIsSimpleAddGroup
  签名: {p : 自然数} [hp : Fact p.Prime]
  定义体: AddCommGroup.is_simple_iff_prime_card.2 (by simpa using hp.out)

Depends on / 依赖: AddCommGroup, AddCommGroup.is_simple_iff_prime_card, hp.out, is_simple_iff_prime_card
-/
instance ZMod.instIsSimpleAddGroup {p : Nat} [hp : Fact p.Prime] : IsSimpleAddGroup (ZMod p) :=
  AddCommGroup.is_simple_iff_prime_card.2 (by simpa using hp.out)

end SpecificInstances

section EquivInt

/--
lemma `LinearOrderedAddCommGroup.isAddCyclic_iff_nonempty_equiv_int` / 引理 `LinearOrderedAddCommGroup.isAddCyclic_iff_nonempty_equiv_int`

English:
lemma LinearOrderedAddCommGroup.isAddCyclic_iff_nonempty_equiv_int
  statement: {A : Type*}
  proof: by
  refine ⟨?_, fun ⟨e⟩ => e.isAddCyclic.mpr inferInstance⟩
  rintro ⟨g, hs⟩
  have h_ne : g != 0 := by
    obtain ⟨a, ha⟩ := exists_ne (0 : A)
    obtain ⟨m, rfl⟩ := hs a
    aesop
  wlog hg' : 0 < g
  · exact this (g := -g) (by simpa using! neg_surjective.comp hs) (by grind) (by grind)
  have hi 

中文:
引理 LinearOrderedAddCommGroup.isAddCyclic_iff_nonempty_equiv_int
  结论: {A : 类型}
  证明: by
  refine ⟨?_, fun ⟨e⟩ => e.isAddCyclic.mpr inferInstance⟩
  rintro ⟨g, hs⟩
  have h_ne : g != 0 := by
    obtain ⟨a, ha⟩ := exists_ne (0 : A)
    obtain ⟨m, rfl⟩ := hs a
    aesop
  wlog hg' : 0 < g
  · exact this (g := -g) (by simpa using! neg_surjective.comp hs) (by grind) (by grind)
  have hi 

Depends on / 依赖: Equiv.ofBijective, Injective, Unique, Unique.mk, add_zsmul, e.isAddCyclic.mpr, exists_ne, h_ne, injective_zsmul_iff_not_isOfFinAddOrder, injective_zsmul_iff_not_isOfFinAddOrder.mpr, isAddCyclic, map_add, map_le_map_iff, neg_surjective, neg_surjective.comp, not_isOfFinAddOrder_of_isAddTorsionFree, ofBijective, subsingleton_iff_isEmpty
-/
lemma LinearOrderedAddCommGroup.isAddCyclic_iff_nonempty_equiv_int {A : Type*}
    [AddCommGroup A] [LinearOrder A] [IsOrderedAddMonoid A] [Nontrivial A] :
    IsAddCyclic A ↔ Nonempty (A ≃+o Int) := by
  refine ⟨?_, fun ⟨e⟩ => e.isAddCyclic.mpr inferInstance⟩
  rintro ⟨g, hs⟩
  have h_ne : g != 0 := by
    obtain ⟨a, ha⟩ := exists_ne (0 : A)
    obtain ⟨m, rfl⟩ := hs a
    aesop
  wlog hg' : 0 < g
  · exact this (g := -g) (by simpa using! neg_surjective.comp hs) (by grind) (by grind)
  have hi : (fun n : Int => n • g).Injective := injective_zsmul_iff_not_isOfFinAddOrder.mpr
 not_isOfFinAddOrder_of_isAddTorsionFree h_ne
  exact ⟨.symm { Equiv.ofBijective _ ⟨hi, hs⟩ with
    map_add' := add_zsmul g
    map_le_map_iff' := zsmul_le_zsmul_iff_left hg' }⟩

set_option backward.isDefEq.respectTransparency false in
/--
lemma `LinearOrderedCommGroup.isCyclic_iff_nonempty_equiv_int` / 引理 `LinearOrderedCommGroup.isCyclic_iff_nonempty_equiv_int`

English:
lemma LinearOrderedCommGroup.isCyclic_iff_nonempty_equiv_int
  statement: {G : Type*}
  proof: by
  rw [← isAddCyclic_additive_iff]; rw [LinearOrderedAddCommGroup.isAddCyclic_iff_nonempty_equiv_int]; rw [OrderAddMonoidIso.toMultiplicativeRight.nonempty_congr]

中文:
引理 LinearOrderedCommGroup.isCyclic_iff_nonempty_equiv_int
  结论: {G : 类型}
  证明: by
  rw [← isAddCyclic_additive_iff]; rw [LinearOrderedAddCommGroup.isAddCyclic_iff_nonempty_equiv_int]; rw [OrderAddMonoidIso.toMultiplicativeRight.nonempty_congr]

Depends on / 依赖: LinearOrderedAddCommGroup, LinearOrderedAddCommGroup.isAddCyclic_iff_nonempty_equiv_int, OrderAddMonoidIso, OrderAddMonoidIso.toMultiplicativeRight.nonempty_congr, isAddCyclic_additive_iff, isAddCyclic_iff_nonempty_equiv_int, nonempty_congr, toMultiplicativeRight
-/
lemma LinearOrderedCommGroup.isCyclic_iff_nonempty_equiv_int {G : Type*}
    [CommGroup G] [LinearOrder G] [IsOrderedMonoid G] [Nontrivial G] :
    IsCyclic G ↔ Nonempty (G ≃*o Multiplicative Int) := by
  rw [← isAddCyclic_additive_iff]; rw [LinearOrderedAddCommGroup.isAddCyclic_iff_nonempty_equiv_int]; rw [OrderAddMonoidIso.toMultiplicativeRight.nonempty_congr]

end EquivInt

section Exponent

open Monoid

@[to_additive]
/--
theorem `IsCyclic.exponent_eq_card` / 定理 `IsCyclic.exponent_eq_card`

English:
theorem IsCyclic.exponent_eq_card
  given: [Group α] [IsCyclic α]
  proof: by
  obtain ⟨g, hg⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := α)
  apply Nat.dvd_antisymm Group.exponent_dvd_nat_card
  rw [← hg]
  exact order_dvd_exponent _

@[to_additive]

中文:
定理 IsCyclic.exponent_eq_card
  条件: [Group α] [IsCyclic α]
  证明: by
  obtain ⟨g, hg⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := α)
  apply Nat.dvd_antisymm Group.exponent_dvd_nat_card
  rw [← hg]
  exact order_dvd_exponent _

@[to_additive]

Depends on / 依赖: Group.exponent_dvd_nat_card, IsCyclic, IsCyclic.exists_ofOrder_eq_natCard, Nat.dvd_antisymm, dvd_antisymm, exists_ofOrder_eq_natCard, exponent_dvd_nat_card, order_dvd_exponent
-/
theorem IsCyclic.exponent_eq_card [Group α] [IsCyclic α] :
    exponent α = Nat.card α := by
  obtain ⟨g, hg⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := α)
  apply Nat.dvd_antisymm Group.exponent_dvd_nat_card
  rw [← hg]
  exact order_dvd_exponent _

@[to_additive]
/--
theorem `IsCyclic.of_exponent_eq_card` / 定理 `IsCyclic.of_exponent_eq_card`

English:
theorem IsCyclic.of_exponent_eq_card
  given: [CommGroup α] [Finite α] (h : exponent α = Nat.card α)
  proof: let ⟨_⟩ := nonempty_fintype α
  let ⟨g, _, hg⟩ := Finset.mem_image.mp (Finset.max'_mem _ _)
isCyclic_of_orderOf_eq_card g hg.trans exponent_eq_max'_orderOf.symm.trans h

@[to_additive]

中文:
定理 IsCyclic.of_exponent_eq_card
  条件: [CommGroup α] [Finite α] (h : exponent α = 自然数.card α)
  证明: let ⟨_⟩ := nonempty_fintype α
  let ⟨g, _, hg⟩ := Finset.mem_image.mp (Finset.max'_mem _ _)
isCyclic_of_orderOf_eq_card g hg.trans exponent_eq_max'_orderOf.symm.trans h

@[to_additive]

Depends on / 依赖: Finset, Finset.max, Finset.mem_image.mp, _mem, _orderOf, _orderOf.symm.trans, exponent_eq_max, hg.trans, isCyclic_of_orderOf_eq_card, mem_image, nonempty_fintype
-/
theorem IsCyclic.of_exponent_eq_card [CommGroup α] [Finite α] (h : exponent α = Nat.card α) :
    IsCyclic α :=
  let ⟨_⟩ := nonempty_fintype α
  let ⟨g, _, hg⟩ := Finset.mem_image.mp (Finset.max'_mem _ _)
isCyclic_of_orderOf_eq_card g hg.trans exponent_eq_max'_orderOf.symm.trans h

@[to_additive]
/--
theorem `IsCyclic.iff_exponent_eq_card` / 定理 `IsCyclic.iff_exponent_eq_card`

English:
theorem IsCyclic.iff_exponent_eq_card
  given: [CommGroup α] [Finite α]
  proof: ⟨fun _ => IsCyclic.exponent_eq_card, IsCyclic.of_exponent_eq_card⟩

@[to_additive]

中文:
定理 IsCyclic.iff_exponent_eq_card
  条件: [CommGroup α] [Finite α]
  证明: ⟨fun _ => IsCyclic.exponent_eq_card, IsCyclic.of_exponent_eq_card⟩

@[to_additive]

Depends on / 依赖: IsCyclic, IsCyclic.exponent_eq_card, IsCyclic.of_exponent_eq_card, exponent_eq_card, of_exponent_eq_card
-/
theorem IsCyclic.iff_exponent_eq_card [CommGroup α] [Finite α] :
    IsCyclic α ↔ exponent α = Nat.card α :=
  ⟨fun _ => IsCyclic.exponent_eq_card, IsCyclic.of_exponent_eq_card⟩

@[to_additive]
/--
theorem `IsCyclic.exponent_eq_zero_of_infinite` / 定理 `IsCyclic.exponent_eq_zero_of_infinite`

English:
theorem IsCyclic.exponent_eq_zero_of_infinite
  given: [Group α] [IsCyclic α] [Infinite α]
  proof: let ⟨_, hg⟩ := IsCyclic.exists_generator (α := α)
exponent_eq_zero_of_order_zero Infinite.orderOf_eq_zero_of_forall_mem_zpowers hg

@[simp]

中文:
定理 IsCyclic.exponent_eq_zero_of_infinite
  条件: [Group α] [IsCyclic α] [Infinite α]
  证明: let ⟨_, hg⟩ := IsCyclic.exists_generator (α := α)
exponent_eq_zero_of_order_zero Infinite.orderOf_eq_zero_of_forall_mem_zpowers hg

@[simp]

Depends on / 依赖: Infinite, Infinite.orderOf_eq_zero_of_forall_mem_zpowers, IsCyclic, IsCyclic.exists_generator, exists_generator, exponent_eq_zero_of_order_zero, orderOf_eq_zero_of_forall_mem_zpowers
-/
theorem IsCyclic.exponent_eq_zero_of_infinite [Group α] [IsCyclic α] [Infinite α] :
    exponent α = 0 :=
  let ⟨_, hg⟩ := IsCyclic.exists_generator (α := α)
exponent_eq_zero_of_order_zero Infinite.orderOf_eq_zero_of_forall_mem_zpowers hg

@[simp]
/--
theorem `ZMod.exponent` / 定理 `ZMod.exponent`

English:
theorem ZMod.exponent
  given: (n : Nat)
  statement: AddMonoid.exponent (ZMod n) = n
  proof: by
  rw [IsAddCyclic.exponent_eq_card]; rw [Nat.card_zmod]

中文:
定理 ZMod.exponent
  条件: (n : 自然数)
  结论: AddMonoid.exponent (ZMod n) = n
  证明: by
  rw [IsAddCyclic.exponent_eq_card]; rw [Nat.card_zmod]
-/
protected theorem ZMod.exponent (n : Nat) : AddMonoid.exponent (ZMod n) = n := by
  rw [IsAddCyclic.exponent_eq_card]; rw [Nat.card_zmod]

/-- A group of order `p ^ 2` is not cyclic if and only if its exponent is `p`. -/
@[to_additive]
/--
lemma `not_isCyclic_iff_exponent_eq_prime` / 引理 `not_isCyclic_iff_exponent_eq_prime`

English:
lemma not_isCyclic_iff_exponent_eq_prime
  statement: [Group α] {p : Nat} (hp : p.Prime)
  proof: by
  -- G is a nontrivial fintype of cardinality `p ^ 2`
  have : Finite α := Nat.finite_of_card_ne_zero (hα ▸ pow_ne_zero 2 hp.ne_zero)
  have : Nontrivial α := Finite.one_lt_card_iff_nontrivial.mp
    (hα ▸ one_lt_pow₀ hp.one_lt two_ne_zero)
  /- in the forward direction, we apply `exponent_eq_pri

中文:
引理 not_isCyclic_iff_exponent_eq_prime
  结论: [Group α] {p : 自然数} (hp : p.Prime)
  证明: by
  -- G is a nontrivial fintype of cardinality `p ^ 2`
  have : Finite α := Nat.finite_of_card_ne_zero (hα ▸ pow_ne_zero 2 hp.ne_zero)
  have : Nontrivial α := Finite.one_lt_card_iff_nontrivial.mp
    (hα ▸ one_lt_pow₀ hp.one_lt two_ne_zero)
  /- in the forward direction, we apply `exponent_eq_pri
-/
lemma not_isCyclic_iff_exponent_eq_prime [Group α] {p : Nat} (hp : p.Prime)
    (hα : Nat.card α = p ^ 2) : ¬ IsCyclic α ↔ Monoid.exponent α = p := by
  -- G is a nontrivial fintype of cardinality `p ^ 2`
  have : Finite α := Nat.finite_of_card_ne_zero (hα ▸ pow_ne_zero 2 hp.ne_zero)
  have : Nontrivial α := Finite.one_lt_card_iff_nontrivial.mp
    (hα ▸ one_lt_pow₀ hp.one_lt two_ne_zero)
  /- in the forward direction, we apply `exponent_eq_prime_iff`, and the reverse direction follows
  immediately because if `α` has exponent `p`, it has no element of order `p ^ 2`. -/
  refine ⟨fun h_cyc => (Monoid.exponent_eq_prime_iff hp).mpr fun g hg => ?_, fun h_exp h_cyc => by
obtain (rfl | rfl) := eq_zero_or_one_of_sq_eq_self hα ▸ h_exp ▸ (h_cyc.exponent_eq_card).symm
    · exact Nat.not_prime_zero hp
    · exact Nat.not_prime_one hp⟩
  /- we must show every non-identity element has order `p`. By Lagrange's theorem, the only possible
  orders of `g` are `1`, `p`, or `p ^ 2`. It can't be the former because `g ≠ 1`, and it can't
  the latter because the group isn't cyclic. -/
  have := (Nat.mem_divisors (m := p ^ 2)).mpr ⟨hα ▸ orderOf_dvd_natCard (x := g), by aesop⟩
  have : exists a < 3, p ^ a = orderOf g := by
    simpa [Nat.divisors_prime_pow hp 2] using this
  obtain ⟨a, ha, ha'⟩ := by simpa using this
  interval_cases a
· exact False.elim hg orderOf_eq_one_iff.mp by simp_all
  · simp_all
· exact False.elim h_cyc isCyclic_of_orderOf_eq_card g by lia

end Exponent

section ZMod

open Subgroup AddSubgroup

/--
theorem `zmultiplesHom_ker_eq` / 定理 `zmultiplesHom_ker_eq`

English:
theorem zmultiplesHom_ker_eq
  given: [AddGroup G] (g : G)
  proof: by
  ext
  simp_rw [AddMonoidHom.mem_ker, mem_zmultiples_iff, zmultiplesHom_apply,
    ← addOrderOf_dvd_iff_zsmul_eq_zero, zsmul_eq_mul', Int.cast_id, dvd_def, eq_comm]

中文:
定理 zmultiplesHom_ker_eq
  条件: [AddGroup G] (g : G)
  证明: by
  ext
  simp_rw [AddMonoidHom.mem_ker, mem_zmultiples_iff, zmultiplesHom_apply,
    ← addOrderOf_dvd_iff_zsmul_eq_zero, zsmul_eq_mul', Int.cast_id, dvd_def, eq_comm]

Depends on / 依赖: AddMonoidHom, AddMonoidHom.mem_ker, Int.cast_id, addOrderOf_dvd_iff_zsmul_eq_zero, cast_id, dvd_def, eq_comm, mem_ker, mem_zmultiples_iff, simp_rw, zmultiplesHom_apply, zsmul_eq_mul
-/
theorem zmultiplesHom_ker_eq [AddGroup G] (g : G) :
    (zmultiplesHom G g).ker = zmultiples ↑(addOrderOf g) := by
  ext
  simp_rw [AddMonoidHom.mem_ker, mem_zmultiples_iff, zmultiplesHom_apply,
    ← addOrderOf_dvd_iff_zsmul_eq_zero, zsmul_eq_mul', Int.cast_id, dvd_def, eq_comm]

/--
theorem `zpowersHom_ker_eq` / 定理 `zpowersHom_ker_eq`

English:
theorem zpowersHom_ker_eq
  given: [Group G] (g : G)
  proof: congr_arg AddSubgroup.toSubgroup zmultiplesHom_ker_eq (Additive.ofMul g)

中文:
定理 zpowersHom_ker_eq
  条件: [Group G] (g : G)
  证明: congr_arg AddSubgroup.toSubgroup zmultiplesHom_ker_eq (Additive.ofMul g)

Depends on / 依赖: AddSubgroup, AddSubgroup.toSubgroup, Additive, Additive.ofMul, congr_arg, toSubgroup, zmultiplesHom_ker_eq
-/
theorem zpowersHom_ker_eq [Group G] (g : G) :
    (zpowersHom G g).ker = zpowers (Multiplicative.ofAdd ↑(orderOf g)) :=
congr_arg AddSubgroup.toSubgroup zmultiplesHom_ker_eq (Additive.ofMul g)

section addGenerator
variable [AddGroup G] {g : G} (hg : forall x, x in zmultiples g) {n : Nat} (hn : Nat.card G = n)

/--
Definition of `zmodAddEquivOfGenerator` / `zmodAddEquivOfGenerator` 的定义

English:
definition zmodAddEquivOfGenerator
  signature: : ZMod n ≃+ G
  body: have kereq : zmultiples (n : Int) = ((zmultiplesHom G) g).ker := by
    rw [zmultiplesHom_ker_eq]; rw [← Nat.card_zmultiples]; rw [← hn]; rw [Nat.card_congr (Equiv.subtypeUnivEquiv hg)]
(Int.quotientZMultiplesNatEquivZMod n).symm.trans
    QuotientAddGroup.liftEquiv _ (φ := zmultiplesHom G g) hg ker

中文:
定义 zmodAddEquivOfGenerator
  签名: : ZMod n ≃+ G
  定义体: have kereq : zmultiples (n : Int) = ((zmultiplesHom G) g).ker := by
    rw [zmultiplesHom_ker_eq]; rw [← Nat.card_zmultiples]; rw [← hn]; rw [Nat.card_congr (Equiv.subtypeUnivEquiv hg)]
(Int.quotientZMultiplesNatEquivZMod n).symm.trans
    QuotientAddGroup.liftEquiv _ (φ := zmultiplesHom G g) hg ker

Depends on / 依赖: Equiv.subtypeUnivEquiv, Int.quotientZMultiplesNatEquivZMod, Nat.card_congr, Nat.card_zmultiples, QuotientAddGroup, QuotientAddGroup.liftEquiv, card_congr, card_zmultiples, liftEquiv, quotientZMultiplesNatEquivZMod, subtypeUnivEquiv, symm.trans, zmultiples, zmultiplesHom, zmultiplesHom_ker_eq
-/
noncomputable def zmodAddEquivOfGenerator : ZMod n ≃+ G :=
  have kereq : zmultiples (n : Int) = ((zmultiplesHom G) g).ker := by
    rw [zmultiplesHom_ker_eq]; rw [← Nat.card_zmultiples]; rw [← hn]; rw [Nat.card_congr (Equiv.subtypeUnivEquiv hg)]
(Int.quotientZMultiplesNatEquivZMod n).symm.trans
    QuotientAddGroup.liftEquiv _ (φ := zmultiplesHom G g) hg kereq

@[simp]
/--
theorem `zmodAddEquivOfGenerator_apply_intCast` / 定理 `zmodAddEquivOfGenerator_apply_intCast`

English:
theorem zmodAddEquivOfGenerator_apply_intCast
  given: (i : Int)
  proof: by
  change (ZMod.cast (i : ZMod n) : Int) • g = i • g
  rw [ZMod.coe_intCast]; rw [Int.emod_def]; rw [eq_comm]; rw [← sub_eq_zero]; rw [sub_eq_add_neg]; rw [← sub_zsmul]; rw [Int.sub_sub_self]; rw [mul_zsmul']; rw [natCast_zsmul]; rw [← hn]; rw [card_nsmul_eq_zero']; rw [zsmul_zero]

@[simp]

中文:
定理 zmodAddEquivOfGenerator_apply_intCast
  条件: (i : 整数)
  证明: by
  change (ZMod.cast (i : ZMod n) : Int) • g = i • g
  rw [ZMod.coe_intCast]; rw [Int.emod_def]; rw [eq_comm]; rw [← sub_eq_zero]; rw [sub_eq_add_neg]; rw [← sub_zsmul]; rw [Int.sub_sub_self]; rw [mul_zsmul']; rw [natCast_zsmul]; rw [← hn]; rw [card_nsmul_eq_zero']; rw [zsmul_zero]

@[simp]

Depends on / 依赖: Embedding, Embedding.toFun, Int.emod_def, Int.sub_sub_self, ZMod.cast, ZMod.coe_intCast, card_nsmul_eq_zero, coe_intCast, emod_def, eq_comm, mul_zsmul, natCast_zsmul, sub_eq_add_neg, sub_eq_zero, sub_sub_self, sub_zsmul, zsmul_zero
-/
theorem zmodAddEquivOfGenerator_apply_intCast (i : Int) :
    zmodAddEquivOfGenerator hg hn i = i • g := by
  change (ZMod.cast (i : ZMod n) : Int) • g = i • g
  rw [ZMod.coe_intCast]; rw [Int.emod_def]; rw [eq_comm]; rw [← sub_eq_zero]; rw [sub_eq_add_neg]; rw [← sub_zsmul]; rw [Int.sub_sub_self]; rw [mul_zsmul']; rw [natCast_zsmul]; rw [← hn]; rw [card_nsmul_eq_zero']; rw [zsmul_zero]

@[simp]
/--
theorem `zmodAddEquivOfGenerator_symm_apply_zsmul` / 定理 `zmodAddEquivOfGenerator_symm_apply_zsmul`

English:
theorem zmodAddEquivOfGenerator_symm_apply_zsmul
  given: (i : Int)
  proof: by
  rw [AddEquiv.symm_apply_eq]; rw [zmodAddEquivOfGenerator_apply_intCast]

@[simp]

中文:
定理 zmodAddEquivOfGenerator_symm_apply_zsmul
  条件: (i : 整数)
  证明: by
  rw [AddEquiv.symm_apply_eq]; rw [zmodAddEquivOfGenerator_apply_intCast]

@[simp]

Depends on / 依赖: AddEquiv, AddEquiv.symm_apply_eq, Embedding, Embedding.inj, symm_apply_eq, zmodAddEquivOfGenerator_apply_intCast
-/
theorem zmodAddEquivOfGenerator_symm_apply_zsmul (i : Int) :
    (zmodAddEquivOfGenerator hg hn).symm (i • g) = i := by
  rw [AddEquiv.symm_apply_eq]; rw [zmodAddEquivOfGenerator_apply_intCast]

@[simp]
/--
theorem `zmodAddEquivOfGenerator_apply_one` / 定理 `zmodAddEquivOfGenerator_apply_one`

English:
theorem zmodAddEquivOfGenerator_apply_one
  statement: zmodAddEquivOfGenerator hg hn 1 = g
  proof: by
  simpa using zmodAddEquivOfGenerator_apply_intCast hg hn 1

@[simp]

中文:
定理 zmodAddEquivOfGenerator_apply_one
  结论: zmodAddEquivOfGenerator hg hn 1 = g
  证明: by
  simpa using zmodAddEquivOfGenerator_apply_intCast hg hn 1

@[simp]

Depends on / 依赖: zmodAddEquivOfGenerator_apply_intCast
-/
theorem zmodAddEquivOfGenerator_apply_one : zmodAddEquivOfGenerator hg hn 1 = g := by
  simpa using zmodAddEquivOfGenerator_apply_intCast hg hn 1

@[simp]
/--
theorem `zmodAddEquivOfGenerator_symm_apply_generator` / 定理 `zmodAddEquivOfGenerator_symm_apply_generator`

English:
theorem zmodAddEquivOfGenerator_symm_apply_generator
  proof: by
  simpa using zmodAddEquivOfGenerator_symm_apply_zsmul hg hn 1

中文:
定理 zmodAddEquivOfGenerator_symm_apply_generator
  证明: by
  simpa using zmodAddEquivOfGenerator_symm_apply_zsmul hg hn 1

Depends on / 依赖: zmodAddEquivOfGenerator_symm_apply_zsmul
-/
theorem zmodAddEquivOfGenerator_symm_apply_generator :
    (zmodAddEquivOfGenerator hg hn).symm g = 1 := by
  simpa using zmodAddEquivOfGenerator_symm_apply_zsmul hg hn 1

end addGenerator

/--
Definition of `zmodAddCyclicAddEquiv` / `zmodAddCyclicAddEquiv` 的定义

English:
definition zmodAddCyclicAddEquiv
  signature: [AddGroup G] (h : IsAddCyclic G)
  body: zmodAddEquivOfGenerator h.exists_generator.choose_spec rfl

中文:
定义 zmodAddCyclicAddEquiv
  签名: [AddGroup G] (h : IsAddCyclic G)
  定义体: zmodAddEquivOfGenerator h.exists_generator.choose_spec rfl

Depends on / 依赖: choose_spec, exists_generator, h.exists_generator.choose_spec, zmodAddEquivOfGenerator
-/
noncomputable def zmodAddCyclicAddEquiv [AddGroup G] (h : IsAddCyclic G) :
    ZMod (Nat.card G) ≃+ G :=
  zmodAddEquivOfGenerator h.exists_generator.choose_spec rfl

/--
theorem `exists_prime_addEquiv_ZMod` / 定理 `exists_prime_addEquiv_ZMod`

English:
theorem exists_prime_addEquiv_ZMod
  given: [CommGroup G] [IsSimpleGroup G]
  proof: by
  obtain ⟨g, hg⟩ := isCyclic_iff_exists_zpowers_eq_top.mp (inferInstance : IsCyclic G)
  use orderOf g; rw [orderOf_eq_card_of_zpowers_eq_top hg]
  constructor
  · exact IsSimpleGroup.prime_card
  · exact ⟨(zmodAddCyclicAddEquiv (G := Additive G) inferInstance).symm⟩

中文:
定理 exists_prime_addEquiv_ZMod
  条件: [CommGroup G] [IsSimpleGroup G]
  证明: by
  obtain ⟨g, hg⟩ := isCyclic_iff_exists_zpowers_eq_top.mp (inferInstance : IsCyclic G)
  use orderOf g; rw [orderOf_eq_card_of_zpowers_eq_top hg]
  constructor
  · exact IsSimpleGroup.prime_card
  · exact ⟨(zmodAddCyclicAddEquiv (G := Additive G) inferInstance).symm⟩

Depends on / 依赖: Additive, IsCyclic, IsSimpleGroup, IsSimpleGroup.prime_card, isCyclic_iff_exists_zpowers_eq_top, isCyclic_iff_exists_zpowers_eq_top.mp, orderOf, orderOf_eq_card_of_zpowers_eq_top, prime_card, zmodAddCyclicAddEquiv
-/
theorem exists_prime_addEquiv_ZMod [CommGroup G] [IsSimpleGroup G] :
    exists p : Nat, Nat.Prime p ∧ Nonempty (Additive G ≃+ ZMod p) := by
  obtain ⟨g, hg⟩ := isCyclic_iff_exists_zpowers_eq_top.mp (inferInstance : IsCyclic G)
  use orderOf g; rw [orderOf_eq_card_of_zpowers_eq_top hg]
  constructor
  · exact IsSimpleGroup.prime_card
  · exact ⟨(zmodAddCyclicAddEquiv (G := Additive G) inferInstance).symm⟩

section mulGenerator
variable [Group G] {g : G} (hg : forall x, x in zpowers g) {n : Nat} (hn : Nat.card G = n)

/--
Definition of `zmodMulEquivOfGenerator` / `zmodMulEquivOfGenerator` 的定义

English:
definition zmodMulEquivOfGenerator
  signature: : Multiplicative (ZMod n) ≃* G
  body: AddEquiv.toMultiplicative zmodAddEquivOfGenerator (G := Additive G) hg hn

@[simp]

中文:
定义 zmodMulEquivOfGenerator
  签名: : Multiplicative (ZMod n) ≃* G
  定义体: AddEquiv.toMultiplicative zmodAddEquivOfGenerator (G := Additive G) hg hn

@[simp]

Depends on / 依赖: AddEquiv, AddEquiv.toMultiplicative, Additive, toMultiplicative, zmodAddEquivOfGenerator
-/
noncomputable def zmodMulEquivOfGenerator : Multiplicative (ZMod n) ≃* G :=
AddEquiv.toMultiplicative zmodAddEquivOfGenerator (G := Additive G) hg hn

@[simp]
/--
theorem `zmodMulEquivOfGenerator_apply_ofAdd_intCast` / 定理 `zmodMulEquivOfGenerator_apply_ofAdd_intCast`

English:
theorem zmodMulEquivOfGenerator_apply_ofAdd_intCast
  given: (i : Int)
  proof: zmodAddEquivOfGenerator_apply_intCast (G := Additive G) hg hn i

@[simp]

中文:
定理 zmodMulEquivOfGenerator_apply_ofAdd_intCast
  条件: (i : 整数)
  证明: zmodAddEquivOfGenerator_apply_intCast (G := Additive G) hg hn i

@[simp]

Depends on / 依赖: Additive, zmodAddEquivOfGenerator_apply_intCast
-/
theorem zmodMulEquivOfGenerator_apply_ofAdd_intCast (i : Int) :
    zmodMulEquivOfGenerator hg hn (Multiplicative.ofAdd i) = g ^ i :=
  zmodAddEquivOfGenerator_apply_intCast (G := Additive G) hg hn i

@[simp]
/--
theorem `zmodMulEquivOfGenerator_symm_apply_zpow` / 定理 `zmodMulEquivOfGenerator_symm_apply_zpow`

English:
theorem zmodMulEquivOfGenerator_symm_apply_zpow
  given: (i : Int)
  proof: zmodAddEquivOfGenerator_symm_apply_zsmul (G := Additive G) hg hn i

@[simp]

中文:
定理 zmodMulEquivOfGenerator_symm_apply_zpow
  条件: (i : 整数)
  证明: zmodAddEquivOfGenerator_symm_apply_zsmul (G := Additive G) hg hn i

@[simp]

Depends on / 依赖: Additive, zmodAddEquivOfGenerator_symm_apply_zsmul
-/
theorem zmodMulEquivOfGenerator_symm_apply_zpow (i : Int) :
    (zmodMulEquivOfGenerator hg hn).symm (g ^ i) = Multiplicative.ofAdd (i : ZMod n) :=
  zmodAddEquivOfGenerator_symm_apply_zsmul (G := Additive G) hg hn i

@[simp]
/--
theorem `zmodMulEquivOfGenerator_apply_ofAdd_one` / 定理 `zmodMulEquivOfGenerator_apply_ofAdd_one`

English:
theorem zmodMulEquivOfGenerator_apply_ofAdd_one
  proof: zmodAddEquivOfGenerator_apply_one (G := Additive G) hg hn

@[simp]

中文:
定理 zmodMulEquivOfGenerator_apply_ofAdd_one
  证明: zmodAddEquivOfGenerator_apply_one (G := Additive G) hg hn

@[simp]

Depends on / 依赖: Additive, zmodAddEquivOfGenerator_apply_one
-/
theorem zmodMulEquivOfGenerator_apply_ofAdd_one :
    zmodMulEquivOfGenerator hg hn (Multiplicative.ofAdd 1) = g :=
  zmodAddEquivOfGenerator_apply_one (G := Additive G) hg hn

@[simp]
/--
theorem `zmodMulEquivOfGenerator_symm_apply_generator` / 定理 `zmodMulEquivOfGenerator_symm_apply_generator`

English:
theorem zmodMulEquivOfGenerator_symm_apply_generator
  proof: zmodAddEquivOfGenerator_symm_apply_generator (G := Additive G) hg hn

中文:
定理 zmodMulEquivOfGenerator_symm_apply_generator
  证明: zmodAddEquivOfGenerator_symm_apply_generator (G := Additive G) hg hn

Depends on / 依赖: Additive, Function, Function.injective_of_subsingleton, injective_of_subsingleton, isEmptyElim, zmodAddEquivOfGenerator_symm_apply_generator
-/
theorem zmodMulEquivOfGenerator_symm_apply_generator :
    (zmodMulEquivOfGenerator hg hn).symm g = Multiplicative.ofAdd 1 :=
  zmodAddEquivOfGenerator_symm_apply_generator (G := Additive G) hg hn

end mulGenerator

/--
Definition of `zmodCyclicMulEquiv` / `zmodCyclicMulEquiv` 的定义

English:
definition zmodCyclicMulEquiv
  signature: [Group G] (h : IsCyclic G)
  body: AddEquiv.toMultiplicative zmodAddCyclicAddEquiv isAddCyclic_additive_iff.2 h

中文:
定义 zmodCyclicMulEquiv
  签名: [Group G] (h : IsCyclic G)
  定义体: AddEquiv.toMultiplicative zmodAddCyclicAddEquiv isAddCyclic_additive_iff.2 h

Depends on / 依赖: AddEquiv, AddEquiv.toMultiplicative, isAddCyclic_additive_iff, toMultiplicative, zmodAddCyclicAddEquiv
-/
noncomputable def zmodCyclicMulEquiv [Group G] (h : IsCyclic G) :
    Multiplicative (ZMod (Nat.card G)) ≃* G :=
AddEquiv.toMultiplicative zmodAddCyclicAddEquiv isAddCyclic_additive_iff.2 h

/--
Definition of `addEquivOfAddCyclicCardEq` / `addEquivOfAddCyclicCardEq` 的定义

English:
definition addEquivOfAddCyclicCardEq
  signature: [AddGroup G] [AddGroup G'] [hG : IsAddCyclic G]
  body: hcard ▸
.symm.trans (zmodAddCyclicAddEquiv hH) zmodAddCyclicAddEquiv hG

中文:
定义 addEquivOfAddCyclicCardEq
  签名: [AddGroup G] [AddGroup G'] [hG : IsAddCyclic G]
  定义体: hcard ▸
.symm.trans (zmodAddCyclicAddEquiv hH) zmodAddCyclicAddEquiv hG
-/
noncomputable def addEquivOfAddCyclicCardEq [AddGroup G] [AddGroup G'] [hG : IsAddCyclic G]
    [hH : IsAddCyclic G'] (hcard : Nat.card G = Nat.card G') : G ≃+ G' := hcard ▸
.symm.trans (zmodAddCyclicAddEquiv hH) zmodAddCyclicAddEquiv hG

/-- Two cyclic groups of the same cardinality are isomorphic. -/
@[to_additive existing]
/--
Definition of `mulEquivOfCyclicCardEq` / `mulEquivOfCyclicCardEq` 的定义

English:
definition mulEquivOfCyclicCardEq
  signature: [Group G] [Group G'] [hG : IsCyclic G]
  body: hcard ▸
.symm.trans (zmodCyclicMulEquiv hH) zmodCyclicMulEquiv hG

中文:
定义 mulEquivOfCyclicCardEq
  签名: [Group G] [Group G'] [hG : IsCyclic G]
  定义体: hcard ▸
.symm.trans (zmodCyclicMulEquiv hH) zmodCyclicMulEquiv hG
-/
noncomputable def mulEquivOfCyclicCardEq [Group G] [Group G'] [hG : IsCyclic G]
    [hH : IsCyclic G'] (hcard : Nat.card G = Nat.card G') : G ≃* G' := hcard ▸
.symm.trans (zmodCyclicMulEquiv hH) zmodCyclicMulEquiv hG

/-- Two groups of the same prime cardinality are isomorphic. -/
@[to_additive /-- Two additive groups of the same prime cardinality are isomorphic. -/]
/--
Definition of `mulEquivOfPrimeCardEq` / `mulEquivOfPrimeCardEq` 的定义

English:
definition mulEquivOfPrimeCardEq
  signature: {p : Nat} [Group G] [Group G']
  body: by
  have hGcyc := isCyclic_of_prime_card hG
  have hHcyc := isCyclic_of_prime_card hH
  apply mulEquivOfCyclicCardEq
  exact hG.trans hH.symm

中文:
定义 mulEquivOfPrimeCardEq
  签名: {p : 自然数} [Group G] [Group G']
  定义体: by
  have hGcyc := isCyclic_of_prime_card hG
  have hHcyc := isCyclic_of_prime_card hH
  apply mulEquivOfCyclicCardEq
  exact hG.trans hH.symm

Depends on / 依赖: hG.trans, hH.symm, isCyclic_of_prime_card, mulEquivOfCyclicCardEq
-/
noncomputable def mulEquivOfPrimeCardEq {p : Nat} [Group G] [Group G']
    [Fact p.Prime] (hG : Nat.card G = p) (hH : Nat.card G' = p) : G ≃* G' := by
  have hGcyc := isCyclic_of_prime_card hG
  have hHcyc := isCyclic_of_prime_card hH
  apply mulEquivOfCyclicCardEq
  exact hG.trans hH.symm

section Infinite

variable [Infinite G]

/--
lemma `zpowersHom_bijective` / 引理 `zpowersHom_bijective`

English:
lemma zpowersHom_bijective
  given: [Group G] {g : G} (hg : zpowers g = ⊤)
  proof: by
  refine ⟨(MonoidHom.ker_eq_bot_iff _).mp ?_, MonoidHom.range_eq_top.mp hg⟩
  simp [zpowersHom_ker_eq, ← infinite_zpowers, hg, Set.infinite_univ]

中文:
引理 zpowersHom_bijective
  条件: [Group G] {g : G} (hg : zpowers g = ⊤)
  证明: by
  refine ⟨(MonoidHom.ker_eq_bot_iff _).mp ?_, MonoidHom.range_eq_top.mp hg⟩
  simp [zpowersHom_ker_eq, ← infinite_zpowers, hg, Set.infinite_univ]

Depends on / 依赖: MonoidHom, MonoidHom.ker_eq_bot_iff, MonoidHom.range_eq_top.mp, Set.infinite_univ, infinite_univ, infinite_zpowers, ker_eq_bot_iff, range_eq_top, zpowersHom_ker_eq
-/
lemma zpowersHom_bijective [Group G] {g : G} (hg : zpowers g = ⊤) :
    Function.Bijective (zpowersHom G g) := by
  refine ⟨(MonoidHom.ker_eq_bot_iff _).mp ?_, MonoidHom.range_eq_top.mp hg⟩
  simp [zpowersHom_ker_eq, ← infinite_zpowers, hg, Set.infinite_univ]

/-- The isomorphism between `Multiplicative ℤ` and the infinite cyclic group `G` sending
`Multiplicative.ofAdd 1` to the generator `g : G`. -/
@[simps! apply]
/--
Definition of `intEquivOfZPowersEqTop` / `intEquivOfZPowersEqTop` 的定义

English:
definition intEquivOfZPowersEqTop
  signature: [Group G] (g : G) (hg : zpowers g = ⊤)
  body: .ofBijective (zpowersHom G g) (zpowersHom_bijective hg)

@[simp]

中文:
定义 intEquivOfZPowersEqTop
  签名: [Group G] (g : G) (hg : zpowers g = ⊤)
  定义体: .ofBijective (zpowersHom G g) (zpowersHom_bijective hg)

@[simp]

Depends on / 依赖: ofBijective, zpowersHom, zpowersHom_bijective
-/
noncomputable def intEquivOfZPowersEqTop [Group G] (g : G) (hg : zpowers g = ⊤) :
    Multiplicative Int ≃* G :=
  .ofBijective (zpowersHom G g) (zpowersHom_bijective hg)

@[simp]
/--
lemma `intEquivOfZPowersEqTop_symm_self` / 引理 `intEquivOfZPowersEqTop_symm_self`

English:
lemma intEquivOfZPowersEqTop_symm_self
  given: [Group G] {g : G} (hg : zpowers g = ⊤)
  proof: by
  simp [MulEquiv.symm_apply_eq]

中文:
引理 intEquivOfZPowersEqTop_symm_self
  条件: [Group G] {g : G} (hg : zpowers g = ⊤)
  证明: by
  simp [MulEquiv.symm_apply_eq]

Depends on / 依赖: MulEquiv, MulEquiv.symm_apply_eq, symm_apply_eq
-/
lemma intEquivOfZPowersEqTop_symm_self [Group G] {g : G} (hg : zpowers g = ⊤) :
    (intEquivOfZPowersEqTop g hg).symm g = Multiplicative.ofAdd 1 := by
  simp [MulEquiv.symm_apply_eq]

/--
lemma `mulintEquivOfZPowersEqTop_symm_apply_zpow` / 引理 `mulintEquivOfZPowersEqTop_symm_apply_zpow`

English:
lemma mulintEquivOfZPowersEqTop_symm_apply_zpow
  given: [Group G] {g : G} (hg : zpowers g = ⊤) (k : Int)
  proof: by
  simp [← ofAdd_zsmul]

中文:
引理 mulintEquivOfZPowersEqTop_symm_apply_zpow
  条件: [Group G] {g : G} (hg : zpowers g = ⊤) (k : 整数)
  证明: by
  simp [← ofAdd_zsmul]

Depends on / 依赖: ofAdd_zsmul
-/
lemma mulintEquivOfZPowersEqTop_symm_apply_zpow [Group G] {g : G} (hg : zpowers g = ⊤) (k : Int) :
    (intEquivOfZPowersEqTop g hg).symm (g ^ k) = Multiplicative.ofAdd k := by
  simp [← ofAdd_zsmul]

/--
lemma `mulintEquivOfZPowersEqTop_strictMono` / 引理 `mulintEquivOfZPowersEqTop_strictMono`

English:
lemma mulintEquivOfZPowersEqTop_strictMono
  statement: [CommGroup G] [PartialOrder G] [IsOrderedMonoid G]
  proof: by
  intro x y hxy
  simp only [intEquivOfZPowersEqTop, MulEquiv.ofBijective_apply, zpowersHom_apply]
  exact zpow_lt_zpow_right hg1 hxy

中文:
引理 mulintEquivOfZPowersEqTop_strictMono
  结论: [CommGroup G] [PartialOrder G] [IsOrderedMonoid G]
  证明: by
  intro x y hxy
  simp only [intEquivOfZPowersEqTop, MulEquiv.ofBijective_apply, zpowersHom_apply]
  exact zpow_lt_zpow_right hg1 hxy

Depends on / 依赖: MulEquiv, MulEquiv.ofBijective_apply, intEquivOfZPowersEqTop, ofBijective_apply, zpow_lt_zpow_right, zpowersHom_apply
-/
lemma mulintEquivOfZPowersEqTop_strictMono [CommGroup G] [PartialOrder G] [IsOrderedMonoid G]
    {g : G} (hg : zpowers g = ⊤) (hg1 : 1 < g) :
    StrictMono (intEquivOfZPowersEqTop g hg) := by
  intro x y hxy
  simp only [intEquivOfZPowersEqTop, MulEquiv.ofBijective_apply, zpowersHom_apply]
  exact zpow_lt_zpow_right hg1 hxy

/--
lemma `mulintEquivOfZPowersEqTop_strictAnti` / 引理 `mulintEquivOfZPowersEqTop_strictAnti`

English:
lemma mulintEquivOfZPowersEqTop_strictAnti
  statement: [CommGroup G] [PartialOrder G] [IsOrderedMonoid G]
  proof: by
  intro x y hxy
  simp only [intEquivOfZPowersEqTop, MulEquiv.ofBijective_apply, zpowersHom_apply]
  exact zpow_right_strictAnti hg1 hxy

中文:
引理 mulintEquivOfZPowersEqTop_strictAnti
  结论: [CommGroup G] [PartialOrder G] [IsOrderedMonoid G]
  证明: by
  intro x y hxy
  simp only [intEquivOfZPowersEqTop, MulEquiv.ofBijective_apply, zpowersHom_apply]
  exact zpow_right_strictAnti hg1 hxy

Depends on / 依赖: MulEquiv, MulEquiv.ofBijective_apply, intEquivOfZPowersEqTop, ofBijective_apply, zpow_right_strictAnti, zpowersHom_apply
-/
lemma mulintEquivOfZPowersEqTop_strictAnti [CommGroup G] [PartialOrder G] [IsOrderedMonoid G]
    {g : G} (hg : zpowers g = ⊤) (hg1 : g < 1) :
    StrictAnti (intEquivOfZPowersEqTop g hg) := by
  intro x y hxy
  simp only [intEquivOfZPowersEqTop, MulEquiv.ofBijective_apply, zpowersHom_apply]
  exact zpow_right_strictAnti hg1 hxy

/-- An infinite cyclic group is isomorphic to `Multiplicative ℤ`. -/
noncomputable
/--
Definition of `intCyclicMulEquiv` / `intCyclicMulEquiv` 的定义

English:
abbreviation intCyclicMulEquiv
  signature: [Group G] [IsCyclic G]
  body: intEquivOfZPowersEqTop _ (isCyclic_iff_exists_zpowers_eq_top.mp ‹IsCyclic G›).choose_spec

中文:
缩写 intCyclicMulEquiv
  签名: [Group G] [IsCyclic G]
  定义体: intEquivOfZPowersEqTop _ (isCyclic_iff_exists_zpowers_eq_top.mp ‹IsCyclic G›).choose_spec

Depends on / 依赖: IsCyclic, choose_spec, intEquivOfZPowersEqTop, isCyclic_iff_exists_zpowers_eq_top, isCyclic_iff_exists_zpowers_eq_top.mp
-/
abbrev intCyclicMulEquiv [Group G] [IsCyclic G] : Multiplicative Int ≃* G :=
  intEquivOfZPowersEqTop _ (isCyclic_iff_exists_zpowers_eq_top.mp ‹IsCyclic G›).choose_spec

/--
lemma `zmultiplesHom_bijective` / 引理 `zmultiplesHom_bijective`

English:
lemma zmultiplesHom_bijective
  given: [AddGroup G] {g : G} (hg : zmultiples g = ⊤)
  proof: by
  refine ⟨(AddMonoidHom.ker_eq_bot_iff _).mp ?_, AddMonoidHom.range_eq_top.mp hg⟩
  simp [zmultiplesHom_ker_eq, ← infinite_zmultiples, hg, Set.infinite_univ]

中文:
引理 zmultiplesHom_bijective
  条件: [AddGroup G] {g : G} (hg : zmultiples g = ⊤)
  证明: by
  refine ⟨(AddMonoidHom.ker_eq_bot_iff _).mp ?_, AddMonoidHom.range_eq_top.mp hg⟩
  simp [zmultiplesHom_ker_eq, ← infinite_zmultiples, hg, Set.infinite_univ]

Depends on / 依赖: AddMonoidHom, AddMonoidHom.ker_eq_bot_iff, AddMonoidHom.range_eq_top.mp, Set.infinite_univ, infinite_univ, infinite_zmultiples, ker_eq_bot_iff, range_eq_top, zmultiplesHom_ker_eq
-/
lemma zmultiplesHom_bijective [AddGroup G] {g : G} (hg : zmultiples g = ⊤) :
    Function.Bijective (zmultiplesHom G g) := by
  refine ⟨(AddMonoidHom.ker_eq_bot_iff _).mp ?_, AddMonoidHom.range_eq_top.mp hg⟩
  simp [zmultiplesHom_ker_eq, ← infinite_zmultiples, hg, Set.infinite_univ]

/-- The isomorphism between `ℤ` and the infinite cyclic group `G` sending
`1` to the generator `g : G`. -/
@[simps! apply]
/--
Definition of `intEquivOfZMultiplesEqTop` / `intEquivOfZMultiplesEqTop` 的定义

English:
definition intEquivOfZMultiplesEqTop
  signature: [AddGroup G] (g : G) (hg : zmultiples g = ⊤)
  body: .ofBijective (zmultiplesHom G g) (zmultiplesHom_bijective hg)

@[simp]

中文:
定义 intEquivOfZMultiplesEqTop
  签名: [AddGroup G] (g : G) (hg : zmultiples g = ⊤)
  定义体: .ofBijective (zmultiplesHom G g) (zmultiplesHom_bijective hg)

@[simp]

Depends on / 依赖: ofBijective, zmultiplesHom, zmultiplesHom_bijective
-/
noncomputable def intEquivOfZMultiplesEqTop [AddGroup G] (g : G) (hg : zmultiples g = ⊤) : Int ≃+ G :=
  .ofBijective (zmultiplesHom G g) (zmultiplesHom_bijective hg)

@[simp]
/--
lemma `intEquivOfZMultiplesEqTop_symm_self` / 引理 `intEquivOfZMultiplesEqTop_symm_self`

English:
lemma intEquivOfZMultiplesEqTop_symm_self
  given: [AddGroup G] (g : G) (hg : zmultiples g = ⊤)
  proof: by
  simp [AddEquiv.symm_apply_eq]

中文:
引理 intEquivOfZMultiplesEqTop_symm_self
  条件: [AddGroup G] (g : G) (hg : zmultiples g = ⊤)
  证明: by
  simp [AddEquiv.symm_apply_eq]

Depends on / 依赖: AddEquiv, AddEquiv.symm_apply_eq, symm_apply_eq
-/
lemma intEquivOfZMultiplesEqTop_symm_self [AddGroup G] (g : G) (hg : zmultiples g = ⊤) :
    (intEquivOfZMultiplesEqTop g hg).symm g = 1 := by
  simp [AddEquiv.symm_apply_eq]

/--
lemma `intEquivOfZMultiplesEqTop_symm_apply_zsmul` / 引理 `intEquivOfZMultiplesEqTop_symm_apply_zsmul`

English:
lemma intEquivOfZMultiplesEqTop_symm_apply_zsmul
  statement: [AddGroup G]
  proof: by
  simp

中文:
引理 intEquivOfZMultiplesEqTop_symm_apply_zsmul
  结论: [AddGroup G]
  证明: by
  simp
-/
lemma intEquivOfZMultiplesEqTop_symm_apply_zsmul [AddGroup G]
    {g : G} (hg : zmultiples g = ⊤) (k : Int) :
    (intEquivOfZMultiplesEqTop g hg).symm (k • g) = k := by
  simp

/-- An infinite cyclic additive group is isomorphic to `ℤ`. -/
noncomputable
/--
Definition of `intCyclicAddEquiv` / `intCyclicAddEquiv` 的定义

English:
abbreviation intCyclicAddEquiv
  signature: [AddGroup G] [IsAddCyclic G]
  body: intEquivOfZMultiplesEqTop _ (isAddCyclic_iff_exists_zmultiples_eq_top.mp ‹_›).choose_spec

中文:
缩写 intCyclicAddEquiv
  签名: [AddGroup G] [IsAddCyclic G]
  定义体: intEquivOfZMultiplesEqTop _ (isAddCyclic_iff_exists_zmultiples_eq_top.mp ‹_›).choose_spec

Depends on / 依赖: choose_spec, intEquivOfZMultiplesEqTop, isAddCyclic_iff_exists_zmultiples_eq_top, isAddCyclic_iff_exists_zmultiples_eq_top.mp
-/
abbrev intCyclicAddEquiv [AddGroup G] [IsAddCyclic G] : Int ≃+ G :=
  intEquivOfZMultiplesEqTop _ (isAddCyclic_iff_exists_zmultiples_eq_top.mp ‹_›).choose_spec

end Infinite

#adaptation_note
/-- `respectTransparency.types true` changes the auto-generated lemmas' signature -/
set_option backward.isDefEq.respectTransparency.types false in
variable (G) in
/-- The automorphism group of a cyclic group is isomorphic to the multiplicative group of ZMod. -/
@[simps!]
/--
Definition of `IsCyclic.mulAutMulEquiv` / `IsCyclic.mulAutMulEquiv` 的定义

English:
definition IsCyclic.mulAutMulEquiv
  signature: [Group G] [h : IsCyclic G]
  body: ((MulAut.congr (zmodCyclicMulEquiv h)).symm.trans
    (MulAutMultiplicative (ZMod (Nat.card G)))).trans
      (ZMod.AddAutEquivUnits (Nat.card G)).toMultiplicative

中文:
定义 IsCyclic.mulAutMulEquiv
  签名: [Group G] [h : IsCyclic G]
  定义体: ((MulAut.congr (zmodCyclicMulEquiv h)).symm.trans
    (MulAutMultiplicative (ZMod (Nat.card G)))).trans
      (ZMod.AddAutEquivUnits (Nat.card G)).toMultiplicative

Depends on / 依赖: AddAutEquivUnits, MulAut, MulAut.congr, MulAutMultiplicative, Nat.card, ZMod.AddAutEquivUnits, symm.trans, toMultiplicative, zmodCyclicMulEquiv
-/
noncomputable def IsCyclic.mulAutMulEquiv [Group G] [h : IsCyclic G] :
    MulAut G ≃* (ZMod (Nat.card G))ˣ :=
  ((MulAut.congr (zmodCyclicMulEquiv h)).symm.trans
    (MulAutMultiplicative (ZMod (Nat.card G)))).trans
      (ZMod.AddAutEquivUnits (Nat.card G)).toMultiplicative

variable (G) in
/--
theorem `IsCyclic.card_mulAut` / 定理 `IsCyclic.card_mulAut`

English:
theorem IsCyclic.card_mulAut
  given: [Group G] [Finite G] [h : IsCyclic G]
  proof: by
  rw [← ZMod.card_units_eq_totient]; rw [← Nat.card_eq_fintype_card]
  exact Nat.card_congr (mulAutMulEquiv G)

中文:
定理 IsCyclic.card_mulAut
  条件: [Group G] [Finite G] [h : IsCyclic G]
  证明: by
  rw [← ZMod.card_units_eq_totient]; rw [← Nat.card_eq_fintype_card]
  exact Nat.card_congr (mulAutMulEquiv G)

Depends on / 依赖: Nat.card_congr, Nat.card_eq_fintype_card, ZMod.card_units_eq_totient, card_congr, card_eq_fintype_card, card_units_eq_totient, mulAutMulEquiv
-/
theorem IsCyclic.card_mulAut [Group G] [Finite G] [h : IsCyclic G] :
    Nat.card (MulAut G) = Nat.totient (Nat.card G) := by
  rw [← ZMod.card_units_eq_totient]; rw [← Nat.card_eq_fintype_card]
  exact Nat.card_congr (mulAutMulEquiv G)

end ZMod

section powMonoidHom

variable (G)

-- Note. Even though cyclic groups only require `[Group G]`, we need `[CommGroup G]` for
-- `powMonoidHom` to be defined.

@[to_additive]
/--
theorem `IsCyclic.card_powMonoidHom_range` / 定理 `IsCyclic.card_powMonoidHom_range`

English:
theorem IsCyclic.card_powMonoidHom_range
  given: [CommGroup G] [hG : IsCyclic G] [Finite G] (d : Nat)
  proof: by
  obtain ⟨g, h⟩ := isCyclic_iff_exists_zpowers_eq_top.mp hG
  rw [MonoidHom.range_eq_map]; rw [← h]; rw [MonoidHom.map_zpowers]; rw [Nat.card_zpowers]; rw [powMonoidHom_apply]; rw [orderOf_pow]; rw [orderOf_eq_card_of_zpowers_eq_top h]

@[to_additive]

中文:
定理 IsCyclic.card_powMonoidHom_range
  条件: [CommGroup G] [hG : IsCyclic G] [Finite G] (d : 自然数)
  证明: by
  obtain ⟨g, h⟩ := isCyclic_iff_exists_zpowers_eq_top.mp hG
  rw [MonoidHom.range_eq_map]; rw [← h]; rw [MonoidHom.map_zpowers]; rw [Nat.card_zpowers]; rw [powMonoidHom_apply]; rw [orderOf_pow]; rw [orderOf_eq_card_of_zpowers_eq_top h]

@[to_additive]

Depends on / 依赖: MonoidHom, MonoidHom.map_zpowers, MonoidHom.range_eq_map, Nat.card_zpowers, card_zpowers, isCyclic_iff_exists_zpowers_eq_top, isCyclic_iff_exists_zpowers_eq_top.mp, map_zpowers, orderOf_eq_card_of_zpowers_eq_top, orderOf_pow, powMonoidHom_apply, range_eq_map
-/
theorem IsCyclic.card_powMonoidHom_range [CommGroup G] [hG : IsCyclic G] [Finite G] (d : Nat) :
    Nat.card (powMonoidHom d : G ->* G).range = Nat.card G / (Nat.card G).gcd d := by
  obtain ⟨g, h⟩ := isCyclic_iff_exists_zpowers_eq_top.mp hG
  rw [MonoidHom.range_eq_map]; rw [← h]; rw [MonoidHom.map_zpowers]; rw [Nat.card_zpowers]; rw [powMonoidHom_apply]; rw [orderOf_pow]; rw [orderOf_eq_card_of_zpowers_eq_top h]

@[to_additive]
/--
theorem `IsCyclic.index_powMonoidHom_ker` / 定理 `IsCyclic.index_powMonoidHom_ker`

English:
theorem IsCyclic.index_powMonoidHom_ker
  given: [CommGroup G] [IsCyclic G] [Finite G] (d : Nat)
  proof: by
  rw [Subgroup.index_ker]; rw [card_powMonoidHom_range]

@[to_additive]

中文:
定理 IsCyclic.index_powMonoidHom_ker
  条件: [CommGroup G] [IsCyclic G] [Finite G] (d : 自然数)
  证明: by
  rw [Subgroup.index_ker]; rw [card_powMonoidHom_range]

@[to_additive]

Depends on / 依赖: Subgroup, Subgroup.index_ker, card_powMonoidHom_range, index_ker
-/
theorem IsCyclic.index_powMonoidHom_ker [CommGroup G] [IsCyclic G] [Finite G] (d : Nat) :
    (powMonoidHom d : G ->* G).ker.index = Nat.card G / (Nat.card G).gcd d := by
  rw [Subgroup.index_ker]; rw [card_powMonoidHom_range]

@[to_additive]
/--
theorem `IsCyclic.card_powMonoidHom_ker` / 定理 `IsCyclic.card_powMonoidHom_ker`

English:
theorem IsCyclic.card_powMonoidHom_ker
  given: [CommGroup G] [IsCyclic G] [Finite G] (d : Nat)
  proof: by
  have h : (powMonoidHom d : G ->* G).ker.index != 0 := Subgroup.index_ne_zero_of_finite
  rw [← mul_left_inj' h]; rw [Subgroup.card_mul_index]; rw [index_powMonoidHom_ker]; rw [Nat.mul_div_cancel']
  exact Nat.gcd_dvd_left (Nat.card G) d

@[to_additive]

中文:
定理 IsCyclic.card_powMonoidHom_ker
  条件: [CommGroup G] [IsCyclic G] [Finite G] (d : 自然数)
  证明: by
  have h : (powMonoidHom d : G ->* G).ker.index != 0 := Subgroup.index_ne_zero_of_finite
  rw [← mul_left_inj' h]; rw [Subgroup.card_mul_index]; rw [index_powMonoidHom_ker]; rw [Nat.mul_div_cancel']
  exact Nat.gcd_dvd_left (Nat.card G) d

@[to_additive]

Depends on / 依赖: Nat.card, Nat.gcd_dvd_left, Nat.mul_div_cancel, Subgroup, Subgroup.card_mul_index, Subgroup.index_ne_zero_of_finite, card_mul_index, gcd_dvd_left, index_ne_zero_of_finite, index_powMonoidHom_ker, ker.index, mul_div_cancel, mul_left_inj, powMonoidHom
-/
theorem IsCyclic.card_powMonoidHom_ker [CommGroup G] [IsCyclic G] [Finite G] (d : Nat) :
    Nat.card (powMonoidHom d : G ->* G).ker = (Nat.card G).gcd d := by
  have h : (powMonoidHom d : G ->* G).ker.index != 0 := Subgroup.index_ne_zero_of_finite
  rw [← mul_left_inj' h]; rw [Subgroup.card_mul_index]; rw [index_powMonoidHom_ker]; rw [Nat.mul_div_cancel']
  exact Nat.gcd_dvd_left (Nat.card G) d

@[to_additive]
/--
theorem `IsCyclic.index_powMonoidHom_range` / 定理 `IsCyclic.index_powMonoidHom_range`

English:
theorem IsCyclic.index_powMonoidHom_range
  given: [CommGroup G] [IsCyclic G] [Finite G] (d : Nat)
  proof: by
  rw [Subgroup.index_range]; rw [card_powMonoidHom_ker]

中文:
定理 IsCyclic.index_powMonoidHom_range
  条件: [CommGroup G] [IsCyclic G] [Finite G] (d : 自然数)
  证明: by
  rw [Subgroup.index_range]; rw [card_powMonoidHom_ker]

Depends on / 依赖: Subgroup, Subgroup.index_range, card_powMonoidHom_ker, index_range
-/
theorem IsCyclic.index_powMonoidHom_range [CommGroup G] [IsCyclic G] [Finite G] (d : Nat) :
    (powMonoidHom d : G ->* G).range.index = (Nat.card G).gcd d := by
  rw [Subgroup.index_range]; rw [card_powMonoidHom_ker]

end powMonoidHom

section generator

/-!
### Groups with a given generator

We state some results in terms of an explicitly given generator.
The generating property is given as in `IsCyclic.exists_generator`.

The main statements are about the existence and uniqueness of homomorphisms and isomorphisms
specified by the image of the given generator.
-/

open Subgroup

variable [Group G] [Group G'] {g : G} (hg : forall x, x in zpowers g) {g' : G'}

section monoidHom

variable (hg' : orderOf g' ∣ orderOf (g : G))

/-- If `g` generates the group `G` and `g'` is an element of another group `G'` whose order
divides that of `g`, then there is a homomorphism `G →* G'` mapping `g` to `g'`. -/
@[to_additive
/-- If `g` generates the additive group `G` and `g'` is an element of another additive group `G'`
whose order divides that of `g`, then there is a homomorphism `G →+ G'` mapping `g` to `g'`. -/]
noncomputable
/--
Definition of `monoidHomOfForallMemZpowers` / `monoidHomOfForallMemZpowers` 的定义

English:
definition monoidHomOfForallMemZpowers
  signature: : G ->* G' where
  body: g' ^ (Classical.choose <| mem_zpowers_iff.mp <| hg x)
map_one' := orderOf_dvd_iff_zpow_eq_one.mp
(Int.natCast_dvd_natCast.mpr hg').trans orderOf_dvd_iff_zpow_eq_one.mpr
Classical.choose_spec mem_zpowers_iff.mp hg 1
  map_mul' x y := by
    simp only [← zpow_add, zpow_eq_zpow_iff_modEq]
    apply Int

中文:
定义 monoidHomOfForallMemZpowers
  签名: : G ->* G' where
  定义体: g' ^ (Classical.choose <| mem_zpowers_iff.mp <| hg x)
map_one' := orderOf_dvd_iff_zpow_eq_one.mp
(Int.natCast_dvd_natCast.mpr hg').trans orderOf_dvd_iff_zpow_eq_one.mpr
Classical.choose_spec mem_zpowers_iff.mp hg 1
  map_mul' x y := by
    simp only [← zpow_add, zpow_eq_zpow_iff_modEq]
    apply Int

Depends on / 依赖: Classical, Classical.choose, mem_zpowers_iff, mem_zpowers_iff.mp
-/
def monoidHomOfForallMemZpowers : G ->* G' where
  toFun x := g' ^ (Classical.choose <| mem_zpowers_iff.mp <| hg x)
map_one' := orderOf_dvd_iff_zpow_eq_one.mp
(Int.natCast_dvd_natCast.mpr hg').trans orderOf_dvd_iff_zpow_eq_one.mpr
Classical.choose_spec mem_zpowers_iff.mp hg 1
  map_mul' x y := by
    simp only [← zpow_add, zpow_eq_zpow_iff_modEq]
    apply Int.ModEq.of_dvd (Int.natCast_dvd_natCast.mpr hg')
    rw [← zpow_eq_zpow_iff_modEq]; rw [zpow_add]
    simp only [fun x => Classical.choose_spec <| mem_zpowers_iff.mp <| hg x]

@[to_additive (attr := simp)]
/--
lemma `monoidHomOfForallMemZpowers_apply_gen` / 引理 `monoidHomOfForallMemZpowers_apply_gen`

English:
lemma monoidHomOfForallMemZpowers_apply_gen
  proof: by
  simp only [monoidHomOfForallMemZpowers, MonoidHom.coe_mk, OneHom.coe_mk]
  nth_rw 2 [← zpow_one g']
  rw [zpow_eq_zpow_iff_modEq]
  apply Int.ModEq.of_dvd (Int.natCast_dvd_natCast.mpr hg')
  rw [← zpow_eq_zpow_iff_modEq]; rw [zpow_one]
exact Classical.choose_spec mem_zpowers_iff.mp hg g

中文:
引理 monoidHomOfForallMemZpowers_apply_gen
  证明: by
  simp only [monoidHomOfForallMemZpowers, MonoidHom.coe_mk, OneHom.coe_mk]
  nth_rw 2 [← zpow_one g']
  rw [zpow_eq_zpow_iff_modEq]
  apply Int.ModEq.of_dvd (Int.natCast_dvd_natCast.mpr hg')
  rw [← zpow_eq_zpow_iff_modEq]; rw [zpow_one]
exact Classical.choose_spec mem_zpowers_iff.mp hg g

Depends on / 依赖: Classical, Classical.choose_spec, Int.ModEq.of_dvd, Int.natCast_dvd_natCast.mpr, MonoidHom, MonoidHom.coe_mk, OneHom, OneHom.coe_mk, choose_spec, coe_mk, mem_zpowers_iff, mem_zpowers_iff.mp, monoidHomOfForallMemZpowers, natCast_dvd_natCast, nth_rw, of_dvd, zpow_eq_zpow_iff_modEq, zpow_one
-/
lemma monoidHomOfForallMemZpowers_apply_gen :
    monoidHomOfForallMemZpowers hg hg' g = g' := by
  simp only [monoidHomOfForallMemZpowers, MonoidHom.coe_mk, OneHom.coe_mk]
  nth_rw 2 [← zpow_one g']
  rw [zpow_eq_zpow_iff_modEq]
  apply Int.ModEq.of_dvd (Int.natCast_dvd_natCast.mpr hg')
  rw [← zpow_eq_zpow_iff_modEq]; rw [zpow_one]
exact Classical.choose_spec mem_zpowers_iff.mp hg g

end monoidHom

include hg in
/-- Two group homomorphisms `G →* G'` are equal if and only if they agree on a generator of `G`. -/
@[to_additive
/-- Two homomorphisms `G →+ G'` of additive groups are equal if and only if they agree
on a generator of `G`. -/]
/--
lemma `MonoidHom.eq_iff_eq_on_generator` / 引理 `MonoidHom.eq_iff_eq_on_generator`

English:
lemma MonoidHom.eq_iff_eq_on_generator
  given: (f₁ f₂ : G ->* G')
  statement: f₁ = f₂ ↔ f₁ g = f₂ g
  proof: by
  rw [DFunLike.ext_iff]
  refine ⟨fun H => H g, fun H x => ?_⟩
obtain ⟨n, hn⟩ := mem_zpowers_iff.mp hg x
  rw [← hn]; rw [map_zpow]; rw [map_zpow]; rw [H]

include hg in

中文:
引理 MonoidHom.eq_iff_eq_on_generator
  条件: (f₁ f₂ : G ->* G')
  结论: f₁ = f₂ ↔ f₁ g = f₂ g
  证明: by
  rw [DFunLike.ext_iff]
  refine ⟨fun H => H g, fun H x => ?_⟩
obtain ⟨n, hn⟩ := mem_zpowers_iff.mp hg x
  rw [← hn]; rw [map_zpow]; rw [map_zpow]; rw [H]

include hg in

Depends on / 依赖: DFunLike, DFunLike.ext_iff, ext_iff, map_zpow, mem_zpowers_iff, mem_zpowers_iff.mp
-/
lemma MonoidHom.eq_iff_eq_on_generator (f₁ f₂ : G ->* G') : f₁ = f₂ ↔ f₁ g = f₂ g := by
  rw [DFunLike.ext_iff]
  refine ⟨fun H => H g, fun H x => ?_⟩
obtain ⟨n, hn⟩ := mem_zpowers_iff.mp hg x
  rw [← hn]; rw [map_zpow]; rw [map_zpow]; rw [H]

include hg in
/-- Two group isomorphisms `G ≃* G'` are equal if and only if they agree on a generator of `G`. -/
@[to_additive
/-- Two isomorphisms `G ≃+ G'` of additive groups are equal if and only if they agree
on a generator of `G`. -/]
/--
lemma `MulEquiv.eq_iff_eq_on_generator` / 引理 `MulEquiv.eq_iff_eq_on_generator`

English:
lemma MulEquiv.eq_iff_eq_on_generator
  given: (f₁ f₂ : G ≃* G')
  statement: f₁ = f₂ ↔ f₁ g = f₂ g
  proof: (Function.Injective.eq_iff toMonoidHom_injective).symm.trans
    MonoidHom.eq_iff_eq_on_generator hg ..

中文:
引理 MulEquiv.eq_iff_eq_on_generator
  条件: (f₁ f₂ : G ≃* G')
  结论: f₁ = f₂ ↔ f₁ g = f₂ g
  证明: (Function.Injective.eq_iff toMonoidHom_injective).symm.trans
    MonoidHom.eq_iff_eq_on_generator hg ..

Depends on / 依赖: Function, Function.Injective.eq_iff, Injective, MonoidHom, MonoidHom.eq_iff_eq_on_generator, eq_iff, eq_iff_eq_on_generator, symm.trans, toMonoidHom_injective
-/
lemma MulEquiv.eq_iff_eq_on_generator (f₁ f₂ : G ≃* G') : f₁ = f₂ ↔ f₁ g = f₂ g :=
(Function.Injective.eq_iff toMonoidHom_injective).symm.trans
    MonoidHom.eq_iff_eq_on_generator hg ..

section mulEquiv

variable (hg' : forall x, x in zpowers g') (h : orderOf g = orderOf g')

/-- Given two groups that are generated by elements `g` and `g'` of the same order,
we obtain an isomorphism sending `g` to `g'`. -/
@[to_additive
/-- Given two additive groups that are generated by elements `g` and `g'` of the same order,
we obtain an isomorphism sending `g` to `g'`. -/]
noncomputable
/--
Definition of `mulEquivOfOrderOfEq` / `mulEquivOfOrderOfEq` 的定义

English:
definition mulEquivOfOrderOfEq
  signature: : G ≃* G'
  body: (monoidHomOfForallMemZpowers hg h.symm.dvd).toMulEquiv (monoidHomOfForallMemZpowers hg' h.dvd)
    (by simp [MonoidHom.eq_iff_eq_on_generator hg]) (by simp [MonoidHom.eq_iff_eq_on_generator hg'])

@[to_additive (attr := simp)]

中文:
定义 mulEquivOfOrderOfEq
  签名: : G ≃* G'
  定义体: (monoidHomOfForallMemZpowers hg h.symm.dvd).toMulEquiv (monoidHomOfForallMemZpowers hg' h.dvd)
    (by simp [MonoidHom.eq_iff_eq_on_generator hg]) (by simp [MonoidHom.eq_iff_eq_on_generator hg'])

@[to_additive (attr := simp)]

Depends on / 依赖: MonoidHom, MonoidHom.eq_iff_eq_on_generator, eq_iff_eq_on_generator, h.dvd, h.symm.dvd, monoidHomOfForallMemZpowers, toMulEquiv
-/
def mulEquivOfOrderOfEq : G ≃* G' :=
  (monoidHomOfForallMemZpowers hg h.symm.dvd).toMulEquiv (monoidHomOfForallMemZpowers hg' h.dvd)
    (by simp [MonoidHom.eq_iff_eq_on_generator hg]) (by simp [MonoidHom.eq_iff_eq_on_generator hg'])

@[to_additive (attr := simp)]
/--
lemma `mulEquivOfOrderOfEq_apply_gen` / 引理 `mulEquivOfOrderOfEq_apply_gen`

English:
lemma mulEquivOfOrderOfEq_apply_gen
  statement: mulEquivOfOrderOfEq hg hg' h g = g'
  proof: monoidHomOfForallMemZpowers_apply_gen hg h.symm.dvd

@[to_additive (attr := simp)]

中文:
引理 mulEquivOfOrderOfEq_apply_gen
  结论: mulEquivOfOrderOfEq hg hg' h g = g'
  证明: monoidHomOfForallMemZpowers_apply_gen hg h.symm.dvd

@[to_additive (attr := simp)]

Depends on / 依赖: h.symm.dvd, monoidHomOfForallMemZpowers_apply_gen
-/
lemma mulEquivOfOrderOfEq_apply_gen : mulEquivOfOrderOfEq hg hg' h g = g' :=
  monoidHomOfForallMemZpowers_apply_gen hg h.symm.dvd

@[to_additive (attr := simp)]
/--
lemma `mulEquivOfOrderOfEq_symm` / 引理 `mulEquivOfOrderOfEq_symm`

English:
lemma mulEquivOfOrderOfEq_symm
  proof: rfl

@[to_additive] -- `simp` can prove this by a combination of the two preceding lemmas

中文:
引理 mulEquivOfOrderOfEq_symm
  证明: rfl

@[to_additive] -- `simp` can prove this by a combination of the two preceding lemmas
-/
lemma mulEquivOfOrderOfEq_symm :
    (mulEquivOfOrderOfEq hg hg' h).symm = mulEquivOfOrderOfEq hg' hg h.symm := rfl

@[to_additive] -- `simp` can prove this by a combination of the two preceding lemmas
/--
lemma `mulEquivOfOrderOfEq_symm_apply_gen` / 引理 `mulEquivOfOrderOfEq_symm_apply_gen`

English:
lemma mulEquivOfOrderOfEq_symm_apply_gen
  statement: (mulEquivOfOrderOfEq hg hg' h).symm g' = g
  proof: monoidHomOfForallMemZpowers_apply_gen hg' h.dvd

中文:
引理 mulEquivOfOrderOfEq_symm_apply_gen
  结论: (mulEquivOfOrderOfEq hg hg' h).symm g' = g
  证明: monoidHomOfForallMemZpowers_apply_gen hg' h.dvd

Depends on / 依赖: h.dvd, monoidHomOfForallMemZpowers_apply_gen
-/
lemma mulEquivOfOrderOfEq_symm_apply_gen : (mulEquivOfOrderOfEq hg hg' h).symm g' = g :=
  monoidHomOfForallMemZpowers_apply_gen hg' h.dvd

end mulEquiv

end generator

section prod

/--
theorem `Group.isCyclic_of_coprime_card_range_card_ker` / 定理 `Group.isCyclic_of_coprime_card_range_card_ker`

English:
theorem Group.isCyclic_of_coprime_card_range_card_ker
  statement: {M N : Type*}
  proof: by
  cases (finite_or_infinite f.ker).symm
  · rw [Nat.card_eq_zero_of_infinite, Nat.coprime_zero_left] at h
    rw [← f.range.eq_bot_iff_card]; rw [f.range_eq_bot_iff]; rw [← f.ker_eq_top_iff] at h
    rwa [← Subgroup.topEquiv.isCyclic, ← h]
  cases (finite_or_infinite f.range).symm
  · rw [Nat.car

中文:
定理 Group.isCyclic_of_coprime_card_range_card_ker
  结论: {M N : 类型}
  证明: by
  cases (finite_or_infinite f.ker).symm
  · rw [Nat.card_eq_zero_of_infinite, Nat.coprime_zero_left] at h
    rw [← f.range.eq_bot_iff_card]; rw [f.range_eq_bot_iff]; rw [← f.ker_eq_top_iff] at h
    rwa [← Subgroup.topEquiv.isCyclic, ← h]
  cases (finite_or_infinite f.range).symm
  · rw [Nat.car
-/
@[to_additive] theorem Group.isCyclic_of_coprime_card_range_card_ker {M N : Type*}
    [CommGroup M] [Group N] (f : M ->* N) (h : (Nat.card f.ker).Coprime (Nat.card f.range))
    [IsCyclic f.ker] [IsCyclic f.range] : IsCyclic M := by
  cases (finite_or_infinite f.ker).symm
  · rw [Nat.card_eq_zero_of_infinite, Nat.coprime_zero_left] at h
    rw [← f.range.eq_bot_iff_card]; rw [f.range_eq_bot_iff]; rw [← f.ker_eq_top_iff] at h
    rwa [← Subgroup.topEquiv.isCyclic, ← h]
  cases (finite_or_infinite f.range).symm
  · rw [Nat.card_eq_zero_of_infinite (α := f.range), Nat.coprime_zero_right] at h
    rwa [(f.ofInjective (f.ker_eq_bot_iff.mp (f.ker.eq_bot_of_card_eq h))).isCyclic]
  have := f.finite_iff_finite_ker_range.mpr ⟨‹_›, ‹_›⟩
  rw [IsCyclic.iff_exponent_eq_card]
  apply dvd_antisymm Group.exponent_dvd_nat_card
  rw [← f.ker.card_mul_index]; rw [Subgroup.index_ker]
  apply h.mul_dvd_of_dvd_of_dvd <;> rw [← IsCyclic.exponent_eq_card]
  · exact Monoid.exponent_dvd_of_monoidHom _ f.ker.subtype_injective
  · exact MonoidHom.exponent_dvd f.rangeRestrict_surjective

/--
theorem `Group.isCyclic_of_coprime_card_ker` / 定理 `Group.isCyclic_of_coprime_card_ker`

English:
theorem Group.isCyclic_of_coprime_card_ker
  statement: {M N : Type*}
  proof: by
  rw [← Subgroup.topEquiv.isCyclic]; rw [← f.range_eq_top.mpr hf] at hN
  rw [← Subgroup.card_top (G := N)]; rw [← f.range_eq_top.mpr hf] at h
  exact isCyclic_of_coprime_card_range_card_ker f h

中文:
定理 Group.isCyclic_of_coprime_card_ker
  结论: {M N : 类型}
  证明: by
  rw [← Subgroup.topEquiv.isCyclic]; rw [← f.range_eq_top.mpr hf] at hN
  rw [← Subgroup.card_top (G := N)]; rw [← f.range_eq_top.mpr hf] at h
  exact isCyclic_of_coprime_card_range_card_ker f h
-/
@[to_additive] theorem Group.isCyclic_of_coprime_card_ker {M N : Type*}
    [CommGroup M] [Group N] (f : M ->* N) (h : (Nat.card f.ker).Coprime (Nat.card N))
    [IsCyclic f.ker] [hN : IsCyclic N] (hf : Function.Surjective f) : IsCyclic M := by
  rw [← Subgroup.topEquiv.isCyclic]; rw [← f.range_eq_top.mpr hf] at hN
  rw [← Subgroup.card_top (G := N)]; rw [← f.range_eq_top.mpr hf] at h
  exact isCyclic_of_coprime_card_range_card_ker f h

section

variable (M N : Type*) [Group M] [Group N] [cyc : IsCyclic (M × N)]
include M N

/--
theorem `isCyclic_left_of_prod` / 定理 `isCyclic_left_of_prod`

English:
theorem isCyclic_left_of_prod
  statement: IsCyclic M
  proof: isCyclic_of_surjective (MonoidHom.fst M N) Prod.fst_surjective

中文:
定理 isCyclic_left_of_prod
  结论: IsCyclic M
  证明: isCyclic_of_surjective (MonoidHom.fst M N) Prod.fst_surjective
-/
@[to_additive isAddCyclic_left_of_prod] theorem isCyclic_left_of_prod : IsCyclic M :=
    isCyclic_of_surjective (MonoidHom.fst M N) Prod.fst_surjective

/--
theorem `isCyclic_right_of_prod` / 定理 `isCyclic_right_of_prod`

English:
theorem isCyclic_right_of_prod
  statement: IsCyclic N
  proof: isCyclic_of_surjective (MonoidHom.snd M N) Prod.snd_surjective

中文:
定理 isCyclic_right_of_prod
  结论: IsCyclic N
  证明: isCyclic_of_surjective (MonoidHom.snd M N) Prod.snd_surjective
-/
@[to_additive isAddCyclic_right_of_prod] theorem isCyclic_right_of_prod : IsCyclic N :=
    isCyclic_of_surjective (MonoidHom.snd M N) Prod.snd_surjective

/--
theorem `coprime_card_of_isCyclic_prod` / 定理 `coprime_card_of_isCyclic_prod`

English:
theorem coprime_card_of_isCyclic_prod
  proof: by
  have hM := isCyclic_left_of_prod M N
  have hN := isCyclic_right_of_prod M N
  let _ := cyc.commGroup; let _ := hM.commGroup; let _ := hN.commGroup
  rw [IsCyclic.iff_exponent_eq_card]; rw [Monoid.exponent_prod]; rw [Nat.card_prod]; rw [lcm_eq_nat_lcm] at *
  simpa only [hM, hN, Nat.lcm_eq_mul_

中文:
定理 coprime_card_of_isCyclic_prod
  证明: by
  have hM := isCyclic_left_of_prod M N
  have hN := isCyclic_right_of_prod M N
  let _ := cyc.commGroup; let _ := hM.commGroup; let _ := hN.commGroup
  rw [IsCyclic.iff_exponent_eq_card]; rw [Monoid.exponent_prod]; rw [Nat.card_prod]; rw [lcm_eq_nat_lcm] at *
  simpa only [hM, hN, Nat.lcm_eq_mul_
-/
@[to_additive coprime_card_of_isAddCyclic_prod] theorem coprime_card_of_isCyclic_prod
    [Finite M] [Finite N] : (Nat.card M).Coprime (Nat.card N) := by
  have hM := isCyclic_left_of_prod M N
  have hN := isCyclic_right_of_prod M N
  let _ := cyc.commGroup; let _ := hM.commGroup; let _ := hN.commGroup
  rw [IsCyclic.iff_exponent_eq_card]; rw [Monoid.exponent_prod]; rw [Nat.card_prod]; rw [lcm_eq_nat_lcm] at *
  simpa only [hM, hN, Nat.lcm_eq_mul_iff, Nat.card_pos.ne', false_or] using cyc

end

/--
theorem `not_isAddCyclic_prod_of_infinite_nontrivial` / 定理 `not_isAddCyclic_prod_of_infinite_nontrivial`

English:
theorem not_isAddCyclic_prod_of_infinite_nontrivial
  statement: (M N : Type*) [AddGroup M] [AddGroup N]
  proof: fun hMN => by
  rw [← ((zmodAddCyclicAddEquiv <| isAddCyclic_left_of_prod M N).prodCongr (zmodAddCyclicAddEquiv <|
    isAddCyclic_right_of_prod M N)).isAddCyclic]; rw [Nat.card_eq_zero_of_infinite] at hMN
  cases (finite_or_infinite N).symm
  · rw [Nat.card_eq_zero_of_infinite] at hMN
    let f := 

中文:
定理 not_isAddCyclic_prod_of_infinite_nontrivial
  结论: (M N : 类型) [AddGroup M] [AddGroup N]
  证明: fun hMN => by
  rw [← ((zmodAddCyclicAddEquiv <| isAddCyclic_left_of_prod M N).prodCongr (zmodAddCyclicAddEquiv <|
    isAddCyclic_right_of_prod M N)).isAddCyclic]; rw [Nat.card_eq_zero_of_infinite] at hMN
  cases (finite_or_infinite N).symm
  · rw [Nat.card_eq_zero_of_infinite] at hMN
    let f := 

Depends on / 依赖: Nat.card_eq_zero_of_infinite, Prod.map_surjective.mpr, ZMod.castHom, ZMod.castHom_surjective, card_eq_zero_of_infinite, castHom, castHom_surjective, coprime_card_of_isA, dvd_zero, f.prodMap, finite_or_infinite, isAddCyclic, isAddCyclic_left_of_prod, isAddCyclic_of_surjective, isAddCyclic_right_of_prod, map_surjective, prodCongr, prodMap, toAddMonoidHom, zmodAddCyclicAddEquiv
-/
theorem not_isAddCyclic_prod_of_infinite_nontrivial (M N : Type*) [AddGroup M] [AddGroup N]
    [Infinite M] [Nontrivial N] : ¬ IsAddCyclic (M × N) := fun hMN => by
  rw [← ((zmodAddCyclicAddEquiv <| isAddCyclic_left_of_prod M N).prodCongr (zmodAddCyclicAddEquiv <|
    isAddCyclic_right_of_prod M N)).isAddCyclic]; rw [Nat.card_eq_zero_of_infinite] at hMN
  cases (finite_or_infinite N).symm
  · rw [Nat.card_eq_zero_of_infinite] at hMN
    let f := (ZMod.castHom (dvd_zero _) (ZMod 2)).toAddMonoidHom
    have hf := ZMod.castHom_surjective (dvd_zero 2)
    have := isAddCyclic_of_surjective (f.prodMap f) (Prod.map_surjective.mpr ⟨hf, hf⟩)
    simpa using coprime_card_of_isAddCyclic_prod (ZMod 2) (ZMod 2)
  let ZN := ZMod (Nat.card N)
  have := isAddCyclic_of_surjective ((ZMod.castHom (dvd_zero _) ZN).toAddMonoidHom.prodMap (.id ZN))
    (Prod.map_surjective.mpr ⟨ZMod.castHom_surjective (dvd_zero _), Function.surjective_id⟩)
  exact Finite.one_lt_card (α := N).ne' (by simpa [ZN] using coprime_card_of_isAddCyclic_prod ZN ZN)

@[to_additive existing not_isAddCyclic_prod_of_infinite_nontrivial]
/--
theorem `not_isCyclic_prod_of_infinite_nontrivial` / 定理 `not_isCyclic_prod_of_infinite_nontrivial`

English:
theorem not_isCyclic_prod_of_infinite_nontrivial
  statement: (M N : Type*) [Group M] [Group N]
  proof: by
  rw [← isAddCyclic_additive_iff]; rw [(AddEquiv.prodAdditive ..).isAddCyclic]
  apply not_isAddCyclic_prod_of_infinite_nontrivial

中文:
定理 not_isCyclic_prod_of_infinite_nontrivial
  结论: (M N : 类型) [Group M] [Group N]
  证明: by
  rw [← isAddCyclic_additive_iff]; rw [(AddEquiv.prodAdditive ..).isAddCyclic]
  apply not_isAddCyclic_prod_of_infinite_nontrivial

Depends on / 依赖: AddEquiv, AddEquiv.prodAdditive, isAddCyclic, isAddCyclic_additive_iff, not_isAddCyclic_prod_of_infinite_nontrivial, prodAdditive
-/
theorem not_isCyclic_prod_of_infinite_nontrivial (M N : Type*) [Group M] [Group N]
    [Infinite M] [Nontrivial N] : ¬ IsCyclic (M × N) := by
  rw [← isAddCyclic_additive_iff]; rw [(AddEquiv.prodAdditive ..).isAddCyclic]
  apply not_isAddCyclic_prod_of_infinite_nontrivial

/-- The product of two finite groups is cyclic iff
both of them are cyclic and their orders are coprime. -/
@[to_additive AddGroup.isAddCyclic_prod_iff /-- The product of two finite additive groups is cyclic
iff both of them are cyclic and their orders are coprime. -/]
/--
theorem `Group.isCyclic_prod_iff` / 定理 `Group.isCyclic_prod_iff`

English:
theorem Group.isCyclic_prod_iff
  given: {M N : Type*} [Group M] [Group N]
  proof: by
  refine ⟨fun h => ⟨isCyclic_left_of_prod M N, isCyclic_right_of_prod M N, ?_⟩, fun ⟨hM, hN, h⟩ => ?_⟩
  · cases (finite_or_infinite M).symm
    · cases subsingleton_or_nontrivial N; · simp
      exact (not_isCyclic_prod_of_infinite_nontrivial M N h).elim
    cases (finite_or_infinite N).symm
   

中文:
定理 Group.isCyclic_prod_iff
  条件: {M N : 类型} [Group M] [Group N]
  证明: by
  refine ⟨fun h => ⟨isCyclic_left_of_prod M N, isCyclic_right_of_prod M N, ?_⟩, fun ⟨hM, hN, h⟩ => ?_⟩
  · cases (finite_or_infinite M).symm
    · cases subsingleton_or_nontrivial N; · simp
      exact (not_isCyclic_prod_of_infinite_nontrivial M N h).elim
    cases (finite_or_infinite N).symm
   

Depends on / 依赖: MonoidHom, MonoidHom.snd, MulEquiv, MulEquiv.prodComm, coprime_card_of_isCyclic_prod, finite_or_infinite, isCyclic, isCyclic_left_of_prod, isCyclic_right_of_prod, not_isCyclic_prod_of_infinite_nontrivial, prodComm, subsingleton_or_nontrivial
-/
theorem Group.isCyclic_prod_iff {M N : Type*} [Group M] [Group N] :
    IsCyclic (M × N) ↔ IsCyclic M ∧ IsCyclic N ∧ (Nat.card M).Coprime (Nat.card N) := by
  refine ⟨fun h => ⟨isCyclic_left_of_prod M N, isCyclic_right_of_prod M N, ?_⟩, fun ⟨hM, hN, h⟩ => ?_⟩
  · cases (finite_or_infinite M).symm
    · cases subsingleton_or_nontrivial N; · simp
      exact (not_isCyclic_prod_of_infinite_nontrivial M N h).elim
    cases (finite_or_infinite N).symm
    · cases subsingleton_or_nontrivial M; · simp
      rw [(MulEquiv.prodComm ..).isCyclic] at h
      exact (not_isCyclic_prod_of_infinite_nontrivial N M h).elim
    apply coprime_card_of_isCyclic_prod
  · let f := MonoidHom.snd M N
    let e : f.ker ≃* M := by
      rw [MonoidHom.ker_snd]
      exact ((Subgroup.prodEquiv ..).trans .prodUnique).trans Subgroup.topEquiv
    let _ := hM.commGroup; let _ := hN.commGroup
    rw [← e.isCyclic] at hM
    rw [← Nat.card_congr e.toEquiv] at h
    exact isCyclic_of_coprime_card_ker f h Prod.snd_surjective

end prod

section WithZero

instance (G : Type*) [Group G] [IsCyclic G] : IsCyclic (WithZero G)ˣ := by
  apply isCyclic_of_injective (G := (WithZero G)ˣ) (WithZero.unitsWithZeroEquiv).toMonoidHom
  apply Equiv.injective

end WithZero
