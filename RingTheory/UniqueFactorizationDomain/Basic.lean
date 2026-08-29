/-
Copyright (c) 2018 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Jens Wagemaker, Aaron Anderson
-/
module

public import Mathlib.Algebra.BigOperators.Associated
public import Mathlib.Data.ENat.Basic
public import Mathlib.RingTheory.UniqueFactorizationDomain.Defs

/-!
# Basic results on unique factorization monoids

## Main results
* `prime_factors_unique`: the prime factors of an element in a cancellative
  commutative monoid with zero (e.g. an integral domain) are unique up to associates
* `UniqueFactorizationMonoid.factors_unique`: the irreducible factors of an element
  in a unique factorization monoid (e.g. a UFD) are unique up to associates
* `UniqueFactorizationMonoid.iff_exists_prime_factors`: unique factorization exists iff each nonzero
  elements factors into a product of primes
* `UniqueFactorizationMonoid.dvd_of_dvd_mul_left_of_no_prime_factors`: Euclid's lemma:
  if `a ∣ b * c` and `a` and `c` have no common prime factors, `a ∣ b`.
* `UniqueFactorizationMonoid.dvd_of_dvd_mul_right_of_no_prime_factors`: Euclid's lemma:
  if `a ∣ b * c` and `a` and `b` have no common prime factors, `a ∣ c`.
* `UniqueFactorizationMonoid.exists_reduced_factors`: in a UFM, we can divide out a common factor
  to get relatively prime elements.
-/

public section

assert_not_exists Field

variable {α : Type*}

local infixl:50 " ~ᵤ " => Associated

namespace WfDvdMonoid

variable [CommMonoidWithZero α]

open Associates Nat

/--
theorem `of_wfDvdMonoid_associates` / 定理 `of_wfDvdMonoid_associates`

English:
theorem of_wfDvdMonoid_associates
  given: (_ : WfDvdMonoid (Associates α))
  statement: WfDvdMonoid α
  proof: ⟨(mk_surjective.wellFounded_iff mk_dvdNotUnit_mk_iff.symm).2 wellFounded_dvdNotUnit⟩

中文:
定理 of_wfDvdMonoid_associates
  条件: (_ : WfDvdMonoid (Associates α))
  结论: WfDvdMonoid α
  证明: ⟨(mk_surjective.wellFounded_iff mk_dvdNotUnit_mk_iff.symm).2 wellFounded_dvdNotUnit⟩

Depends on / 依赖: mk_dvdNotUnit_mk_iff, mk_dvdNotUnit_mk_iff.symm, mk_surjective, mk_surjective.wellFounded_iff, wellFounded_dvdNotUnit, wellFounded_iff
-/
theorem of_wfDvdMonoid_associates (_ : WfDvdMonoid (Associates α)) : WfDvdMonoid α :=
  ⟨(mk_surjective.wellFounded_iff mk_dvdNotUnit_mk_iff.symm).2 wellFounded_dvdNotUnit⟩

variable [WfDvdMonoid α]

/--
Instance `wfDvdMonoid_associates` / 实例 `wfDvdMonoid_associates`

English:
instance wfDvdMonoid_associates
  signature: : WfDvdMonoid (Associates α)
  body: ⟨(mk_surjective.wellFounded_iff mk_dvdNotUnit_mk_iff.symm).1 wellFounded_dvdNotUnit⟩

中文:
实例 wfDvdMonoid_associates
  签名: : WfDvdMonoid (Associates α)
  定义体: ⟨(mk_surjective.wellFounded_iff mk_dvdNotUnit_mk_iff.symm).1 wellFounded_dvdNotUnit⟩

Depends on / 依赖: mk_dvdNotUnit_mk_iff, mk_dvdNotUnit_mk_iff.symm, mk_surjective, mk_surjective.wellFounded_iff, wellFounded_dvdNotUnit, wellFounded_iff
-/
instance wfDvdMonoid_associates : WfDvdMonoid (Associates α) :=
  ⟨(mk_surjective.wellFounded_iff mk_dvdNotUnit_mk_iff.symm).1 wellFounded_dvdNotUnit⟩

/--
theorem `wellFoundedLT_associates` / 定理 `wellFoundedLT_associates`

English:
theorem wellFoundedLT_associates
  statement: WellFoundedLT (Associates α)
  proof: ⟨Subrelation.wf dvdNotUnit_of_lt wellFounded_dvdNotUnit⟩

中文:
定理 wellFoundedLT_associates
  结论: WellFoundedLT (Associates α)
  证明: ⟨Subrelation.wf dvdNotUnit_of_lt wellFounded_dvdNotUnit⟩

Depends on / 依赖: Subrelation, Subrelation.wf, dvdNotUnit_of_lt, wellFounded_dvdNotUnit
-/
theorem wellFoundedLT_associates : WellFoundedLT (Associates α) :=
  ⟨Subrelation.wf dvdNotUnit_of_lt wellFounded_dvdNotUnit⟩

end WfDvdMonoid

/--
theorem `WfDvdMonoid.of_wellFoundedLT_associates` / 定理 `WfDvdMonoid.of_wellFoundedLT_associates`

English:
theorem WfDvdMonoid.of_wellFoundedLT_associates
  statement: [CommMonoidWithZero α] [IsCancelMulZero α]
  proof: WfDvdMonoid.of_wfDvdMonoid_associates
    ⟨by convert h.wf; exact Associates.dvdNotUnit_iff_lt⟩

中文:
定理 WfDvdMonoid.of_wellFoundedLT_associates
  结论: [带零交换幺半群 α] [是乘零消去 α]
  证明: WfDvdMonoid.of_wfDvdMonoid_associates
    ⟨by convert h.wf; exact Associates.dvdNotUnit_iff_lt⟩

Depends on / 依赖: Associates, Associates.dvdNotUnit_iff_lt, WfDvdMonoid, WfDvdMonoid.of_wfDvdMonoid_associates, convert, dvdNotUnit_iff_lt, h.wf, of_wfDvdMonoid_associates
-/
theorem WfDvdMonoid.of_wellFoundedLT_associates [CommMonoidWithZero α] [IsCancelMulZero α]
    (h : WellFoundedLT (Associates α)) : WfDvdMonoid α :=
  WfDvdMonoid.of_wfDvdMonoid_associates
    ⟨by convert h.wf; exact Associates.dvdNotUnit_iff_lt⟩

/--
theorem `WfDvdMonoid.iff_wellFounded_associates` / 定理 `WfDvdMonoid.iff_wellFounded_associates`

English:
theorem WfDvdMonoid.iff_wellFounded_associates
  given: [CommMonoidWithZero α] [IsCancelMulZero α]
  proof: ⟨by apply WfDvdMonoid.wellFoundedLT_associates, WfDvdMonoid.of_wellFoundedLT_associates⟩

中文:
定理 WfDvdMonoid.iff_wellFounded_associates
  条件: [带零交换幺半群 α] [是乘零消去 α]
  证明: ⟨by apply WfDvdMonoid.wellFoundedLT_associates, WfDvdMonoid.of_wellFoundedLT_associates⟩

Depends on / 依赖: WfDvdMonoid, WfDvdMonoid.of_wellFoundedLT_associates, WfDvdMonoid.wellFoundedLT_associates, of_wellFoundedLT_associates, wellFoundedLT_associates
-/
theorem WfDvdMonoid.iff_wellFounded_associates [CommMonoidWithZero α] [IsCancelMulZero α] :
    WfDvdMonoid α ↔ WellFoundedLT (Associates α) :=
  ⟨by apply WfDvdMonoid.wellFoundedLT_associates, WfDvdMonoid.of_wellFoundedLT_associates⟩

/--
Instance `Associates.ufm` / 实例 `Associates.ufm`

English:
instance Associates.ufm
  signature: [CommMonoidWithZero α] [UniqueFactorizationMonoid α]
  body: { (WfDvdMonoid.wfDvdMonoid_associates : WfDvdMonoid (Associates α)) with
    irreducible_iff_prime := by
      rw [← Associates.irreducible_iff_prime_iff]
      apply UniqueFactorizationMonoid.irreducible_iff_prime }

中文:
实例 Associates.ufm
  签名: [带零交换幺半群 α] [唯一分解幺半群 α]
  定义体: { (WfDvdMonoid.wfDvdMonoid_associates : WfDvdMonoid (Associates α)) with
    irreducible_iff_prime := by
      rw [← Associates.irreducible_iff_prime_iff]
      apply UniqueFactorizationMonoid.irreducible_iff_prime }

Depends on / 依赖: Associates, Associates.irreducible_iff_prime_iff, UniqueFactorizationMonoid, UniqueFactorizationMonoid.irreducible_iff_prime, WfDvdMonoid, WfDvdMonoid.wfDvdMonoid_associates, irreducible_iff_prime, irreducible_iff_prime_iff, wfDvdMonoid_associates
-/
instance Associates.ufm [CommMonoidWithZero α] [UniqueFactorizationMonoid α] :
    UniqueFactorizationMonoid (Associates α) :=
  { (WfDvdMonoid.wfDvdMonoid_associates : WfDvdMonoid (Associates α)) with
    irreducible_iff_prime := by
      rw [← Associates.irreducible_iff_prime_iff]
      apply UniqueFactorizationMonoid.irreducible_iff_prime }

/--
theorem `prime_factors_unique` / 定理 `prime_factors_unique`

English:
theorem prime_factors_unique
  given: [CommMonoidWithZero α] [IsCancelMulZero α]
  proof: by
  intro f
  induction f using Multiset.induction_on with
  | empty =>
    intro g _ hg h
exact Multiset.rel_zero_left.2
      Multiset.eq_zero_of_forall_notMem fun x hx =>
        have : IsUnit g.prod := by simpa [associated_one_iff_isUnit] using h.symm
(hg x hx).not_isUnit
isUnit_iff_dvd_one.2 (

中文:
定理 prime_factors_unique
  条件: [带零交换幺半群 α] [是乘零消去 α]
  证明: by
  intro f
  induction f using Multiset.induction_on with
  | empty =>
    intro g _ hg h
exact Multiset.rel_zero_left.2
      Multiset.eq_zero_of_forall_notMem fun x hx =>
        have : IsUnit g.prod := by simpa [associated_one_iff_isUnit] using h.symm
(hg x hx).not_isUnit
isUnit_iff_dvd_one.2 (

Depends on / 依赖: IsUnit, Multiset, Multiset.dvd_prod, Multiset.eq_zero_of_forall_notMem, Multiset.induction_on, Multiset.rel_zero_left, associated_one_iff_isUnit, dvd_iff_dvd_right, dvd_prod, eq_zero_of_forall_notMem, exists_associated_mem_of_dvd_prod, g.prod, h.symm, hfg.dvd_iff_dvd_right, induction_on, isUnit_iff_dvd_one, not_isUnit, rel_zero_left
-/
theorem prime_factors_unique [CommMonoidWithZero α] [IsCancelMulZero α] :
    forall {f g : Multiset α},
      (forall x in f, Prime x) -> (forall x in g, Prime x) -> f.prod ~ᵤ g.prod -> Multiset.Rel Associated f g := by
  intro f
  induction f using Multiset.induction_on with
  | empty =>
    intro g _ hg h
exact Multiset.rel_zero_left.2
      Multiset.eq_zero_of_forall_notMem fun x hx =>
        have : IsUnit g.prod := by simpa [associated_one_iff_isUnit] using h.symm
(hg x hx).not_isUnit
isUnit_iff_dvd_one.2 (Multiset.dvd_prod hx).trans (isUnit_iff_dvd_one.1 this)
  | cons p f ih =>
    intro g hf hg hfg
    let ⟨b, hbg, hb⟩ :=
(exists_associated_mem_of_dvd_prod (hf p (by simp)) fun q hq => hg _ hq)
        hfg.dvd_iff_dvd_right.1 (show p ∣ (p ::ₘ f).prod by simp)
    have := Classical.decEq α
    rw [← Multiset.cons_erase hbg]
    exact
      Multiset.Rel.cons hb
        (ih (fun q hq => hf _ (by simp [hq]))
          (fun {q} (hq : q in g.erase b) => hg q (Multiset.mem_of_mem_erase hq))
          (Associated.of_mul_left
            (by rwa [← Multiset.prod_cons, ← Multiset.prod_cons, Multiset.cons_erase hbg]) hb
            (hf p (by simp)).ne_zero))

namespace UniqueFactorizationMonoid

variable [CommMonoidWithZero α] [UniqueFactorizationMonoid α]

/--
theorem `factors_unique` / 定理 `factors_unique`

English:
theorem factors_unique
  statement: {f g : Multiset α} (hf : forall x in f, Irreducible x)
  proof: prime_factors_unique (fun x hx => UniqueFactorizationMonoid.irreducible_iff_prime.mp (hf x hx))
    (fun x hx => UniqueFactorizationMonoid.irreducible_iff_prime.mp (hg x hx)) h

中文:
定理 factors_unique
  结论: {f g : Multiset α} (hf : 对任意 x in f, 不可约 x)
  证明: prime_factors_unique (fun x hx => UniqueFactorizationMonoid.irreducible_iff_prime.mp (hf x hx))
    (fun x hx => UniqueFactorizationMonoid.irreducible_iff_prime.mp (hg x hx)) h

Depends on / 依赖: UniqueFactorizationMonoid, UniqueFactorizationMonoid.irreducible_iff_prime.mp, irreducible_iff_prime, prime_factors_unique
-/
theorem factors_unique {f g : Multiset α} (hf : forall x in f, Irreducible x)
    (hg : forall x in g, Irreducible x) (h : f.prod ~ᵤ g.prod) : Multiset.Rel Associated f g :=
  prime_factors_unique (fun x hx => UniqueFactorizationMonoid.irreducible_iff_prime.mp (hf x hx))
    (fun x hx => UniqueFactorizationMonoid.irreducible_iff_prime.mp (hg x hx)) h

/--
theorem `_root_.Associated.card_factors_eq` / 定理 `_root_.Associated.card_factors_eq`

English:
theorem _root_.Associated.card_factors_eq
  given: {a b : α} (h : Associated a b)
  proof: by
  by_cases hb : b = 0
  · simp_all
  have ha : a != 0 := h.ne_zero_iff.mpr hb
  apply Multiset.card_eq_card_of_rel
  apply factors_unique irreducible_of_factor irreducible_of_factor
exact (factors_prod ha).trans h.trans (factors_prod hb).symm

中文:
定理 _root_.Associated.card_factors_eq
  条件: {a b : α} (h : Associated a b)
  证明: by
  by_cases hb : b = 0
  · simp_all
  have ha : a != 0 := h.ne_zero_iff.mpr hb
  apply Multiset.card_eq_card_of_rel
  apply factors_unique irreducible_of_factor irreducible_of_factor
exact (factors_prod ha).trans h.trans (factors_prod hb).symm

Depends on / 依赖: Multiset, Multiset.card_eq_card_of_rel, card_eq_card_of_rel, factors_prod, factors_unique, h.ne_zero_iff.mpr, h.trans, irreducible_of_factor, ne_zero_iff
-/
theorem _root_.Associated.card_factors_eq {a b : α} (h : Associated a b) :
    (factors a).card = (factors b).card := by
  by_cases hb : b = 0
  · simp_all
  have ha : a != 0 := h.ne_zero_iff.mpr hb
  apply Multiset.card_eq_card_of_rel
  apply factors_unique irreducible_of_factor irreducible_of_factor
exact (factors_prod ha).trans h.trans (factors_prod hb).symm

end UniqueFactorizationMonoid

/--
theorem `prime_factors_irreducible` / 定理 `prime_factors_irreducible`

English:
theorem prime_factors_irreducible
  statement: [CommMonoidWithZero α] {a : α} {f : Multiset α}
  proof: by
  have := Classical.decEq α
  refine @Multiset.induction_on _
    (fun g => (g.prod ~ᵤ a) -> (forall b in g, Prime b) -> exists p, a ~ᵤ p ∧ g = {p}) f ?_ ?_ pfa.2 pfa.1
  · intro h; exact (ha.not_isUnit (associated_one_iff_isUnit.1 (Associated.symm h))).elim
  · rintro p s _ ⟨u, hu⟩ hs
    use p


中文:
定理 prime_factors_irreducible
  结论: [带零交换幺半群 α] {a : α} {f : Multiset α}
  证明: by
  have := Classical.decEq α
  refine @Multiset.induction_on _
    (fun g => (g.prod ~ᵤ a) -> (forall b in g, Prime b) -> exists p, a ~ᵤ p ∧ g = {p}) f ?_ ?_ pfa.2 pfa.1
  · intro h; exact (ha.not_isUnit (associated_one_iff_isUnit.1 (Associated.symm h))).elim
  · rintro p s _ ⟨u, hu⟩ hs
    use p


Depends on / 依赖: Associated, Associated.symm, Classical, Classical.decEq, Multiset, Multiset.exists_mem_of_ne_zero, Multiset.induction_on, associated_one_iff_isUnit, exists_mem_of_ne_zero, g.prod, ha.isUnit_or_isUnit, ha.not_isUnit, induction_on, isUnit_or_isUnit, not_isUnit, resolve_left, s.erase
-/
theorem prime_factors_irreducible [CommMonoidWithZero α] {a : α} {f : Multiset α}
    (ha : Irreducible a) (pfa : (forall b in f, Prime b) ∧ f.prod ~ᵤ a) : exists p, a ~ᵤ p ∧ f = {p} := by
  have := Classical.decEq α
  refine @Multiset.induction_on _
    (fun g => (g.prod ~ᵤ a) -> (forall b in g, Prime b) -> exists p, a ~ᵤ p ∧ g = {p}) f ?_ ?_ pfa.2 pfa.1
  · intro h; exact (ha.not_isUnit (associated_one_iff_isUnit.1 (Associated.symm h))).elim
  · rintro p s _ ⟨u, hu⟩ hs
    use p
    have hs0 : s = 0 := by
      by_contra hs0
      obtain ⟨q, hq⟩ := Multiset.exists_mem_of_ne_zero hs0
      apply (hs q (by simp [hq])).2.1
      refine (ha.isUnit_or_isUnit (?_ : _ = p * ↑u * (s.erase q).prod * _)).resolve_left ?_
      · rw [mul_right_comm _ _ q, mul_assoc, ← Multiset.prod_cons, Multiset.cons_erase hq, ← hu,
          mul_comm, mul_comm p _, mul_assoc]
        simp
      apply mt isUnit_of_mul_isUnit_left (mt isUnit_of_mul_isUnit_left _)
      apply (hs p (Multiset.mem_cons_self _ _)).2.1
    simp only [mul_one, Multiset.prod_cons, Multiset.prod_zero, hs0] at *
    exact ⟨Associated.symm ⟨u, hu⟩, rfl⟩

/--
theorem `irreducible_iff_prime_of_existsUnique_irreducible_factors` / 定理 `irreducible_iff_prime_of_existsUnique_irreducible_factors`

English:
theorem irreducible_iff_prime_of_existsUnique_irreducible_factors
  statement: [CommMonoidWithZero α]
  proof: letI := Classical.decEq α
  ⟨ fun hpi =>
    ⟨hpi.ne_zero, hpi.1, fun a b ⟨x, hx⟩ =>
      if hab0 : a * b = 0 then
        (eq_zero_or_eq_zero_of_mul_eq_zero hab0).elim (fun ha0 => by simp [ha0]) fun hb0 => by
          simp [hb0]
      else by
        have hx0 : x != 0 := fun hx0 => by simp_all
  

中文:
定理 irreducible_iff_prime_of_存在Unique_irreducible_factors
  结论: [带零交换幺半群 α]
  证明: letI := Classical.decEq α
  ⟨ fun hpi =>
    ⟨hpi.ne_zero, hpi.1, fun a b ⟨x, hx⟩ =>
      if hab0 : a * b = 0 then
        (eq_zero_or_eq_zero_of_mul_eq_zero hab0).elim (fun ha0 => by simp [ha0]) fun hb0 => by
          simp [hb0]
      else by
        have hx0 : x != 0 := fun hx0 => by simp_all
  

Depends on / 依赖: Associated, Classical, Classical.decEq, Multiset, Multiset.Rel, eq_zero_or_eq_zero_of_mul_eq_zero, hpi.ne_zero, left_ne_zero_of_mul, ne_zero, right_ne_zero_of_mul
-/
theorem irreducible_iff_prime_of_existsUnique_irreducible_factors [CommMonoidWithZero α]
    [IsCancelMulZero α]
    (eif : forall a : α, a != 0 -> exists f : Multiset α, (forall b in f, Irreducible b) ∧ f.prod ~ᵤ a)
    (uif :
      forall f g : Multiset α,
        (forall x in f, Irreducible x) ->
          (forall x in g, Irreducible x) -> f.prod ~ᵤ g.prod -> Multiset.Rel Associated f g)
    (p : α) : Irreducible p ↔ Prime p :=
  letI := Classical.decEq α
  ⟨ fun hpi =>
    ⟨hpi.ne_zero, hpi.1, fun a b ⟨x, hx⟩ =>
      if hab0 : a * b = 0 then
        (eq_zero_or_eq_zero_of_mul_eq_zero hab0).elim (fun ha0 => by simp [ha0]) fun hb0 => by
          simp [hb0]
      else by
        have hx0 : x != 0 := fun hx0 => by simp_all
        have ha0 : a != 0 := left_ne_zero_of_mul hab0
        have hb0 : b != 0 := right_ne_zero_of_mul hab0
        obtain ⟨fx, hfx⟩ := eif x hx0
        obtain ⟨fa, hfa⟩ := eif a ha0
        obtain ⟨fb, hfb⟩ := eif b hb0
        have h : Multiset.Rel Associated (p ::ₘ fx) (fa + fb) := by
          apply uif
          · exact fun i hi => (Multiset.mem_cons.1 hi).elim (fun hip => hip.symm ▸ hpi) (hfx.1 _)
          · exact fun i hi => (Multiset.mem_add.1 hi).elim (hfa.1 _) (hfb.1 _)
          calc
            Multiset.prod (p ::ₘ fx) ~ᵤ a * b := by
              rw [hx]; rw [Multiset.prod_cons]; exact hfx.2.mul_left _
            _ ~ᵤ fa.prod * fb.prod := hfa.2.symm.mul_mul hfb.2.symm
            _ = _ := by rw [Multiset.prod_add]
        exact
          let ⟨q, hqf, hq⟩ := Multiset.exists_mem_of_rel_of_mem h (Multiset.mem_cons_self p _)
          (Multiset.mem_add.1 hqf).elim
            (fun hqa =>
Or.inl hq.dvd_iff_dvd_left.2 hfa.2.dvd_iff_dvd_right.1 (Multiset.dvd_prod hqa))
            fun hqb =>
Or.inr hq.dvd_iff_dvd_left.2 hfb.2.dvd_iff_dvd_right.1 (Multiset.dvd_prod hqb)⟩,
    Prime.irreducible⟩

namespace UniqueFactorizationMonoid

open Multiset

variable [CommMonoidWithZero α]
variable [UniqueFactorizationMonoid α]

@[simp]
/--
theorem `factors_one` / 定理 `factors_one`

English:
theorem factors_one
  statement: factors (1 : α) = 0
  proof: by
  nontriviality α using factors
  rw [← rel_zero_right]
  refine factors_unique irreducible_of_factor (fun x hx => (notMem_zero x hx).elim) ?_
  rw [prod_zero]
  exact factors_prod one_ne_zero

中文:
定理 factors_one
  结论: factors (1 : α) = 0
  证明: by
  nontriviality α using factors
  rw [← rel_zero_right]
  refine factors_unique irreducible_of_factor (fun x hx => (notMem_zero x hx).elim) ?_
  rw [prod_zero]
  exact factors_prod one_ne_zero

Depends on / 依赖: factors, factors_prod, factors_unique, irreducible_of_factor, nontriviality, notMem_zero, one_ne_zero, prod_zero, rel_zero_right
-/
theorem factors_one : factors (1 : α) = 0 := by
  nontriviality α using factors
  rw [← rel_zero_right]
  refine factors_unique irreducible_of_factor (fun x hx => (notMem_zero x hx).elim) ?_
  rw [prod_zero]
  exact factors_prod one_ne_zero

/--
theorem `exists_mem_factors_of_dvd` / 定理 `exists_mem_factors_of_dvd`

English:
theorem exists_mem_factors_of_dvd
  given: {a p : α} (ha0 : a != 0) (hp : Irreducible p)
  proof: fun ⟨b, hb⟩ =>
  have hb0 : b != 0 := fun hb0 => by simp_all
  have : Rel Associated (p ::ₘ factors b) (factors a) :=
    factors_unique
      (fun _ hx => (mem_cons.1 hx).elim (fun h => h.symm ▸ hp) (irreducible_of_factor _))
      irreducible_of_factor
      (Associated.symm <|
        calc
      

中文:
定理 存在_mem_factors_of_dvd
  条件: {a p : α} (ha0 : a != 0) (hp : 不可约 p)
  证明: fun ⟨b, hb⟩ =>
  have hb0 : b != 0 := fun hb0 => by simp_all
  have : Rel Associated (p ::ₘ factors b) (factors a) :=
    factors_unique
      (fun _ hx => (mem_cons.1 hx).elim (fun h => h.symm ▸ hp) (irreducible_of_factor _))
      irreducible_of_factor
      (Associated.symm <|
        calc
      
-/
theorem exists_mem_factors_of_dvd {a p : α} (ha0 : a != 0) (hp : Irreducible p) :
    p ∣ a -> exists q in factors a, p ~ᵤ q := fun ⟨b, hb⟩ =>
  have hb0 : b != 0 := fun hb0 => by simp_all
  have : Rel Associated (p ::ₘ factors b) (factors a) :=
    factors_unique
      (fun _ hx => (mem_cons.1 hx).elim (fun h => h.symm ▸ hp) (irreducible_of_factor _))
      irreducible_of_factor
      (Associated.symm <|
        calc
          prod (factors a) ~ᵤ a := factors_prod ha0
          _ = p * b := hb
          _ ~ᵤ prod (p ::ₘ factors b) := by
            rw [prod_cons]; exact (factors_prod hb0).symm.mul_left _)
  exists_mem_of_rel_of_mem this (by simp)

/--
theorem `exists_mem_factors` / 定理 `exists_mem_factors`

English:
theorem exists_mem_factors
  given: {x : α} (hx : x != 0) (h : ¬IsUnit x)
  statement: exists p, p in factors x
  proof: by
  obtain ⟨p', hp', hp'x⟩ := WfDvdMonoid.exists_irreducible_factor h hx
  obtain ⟨p, hp, _⟩ := exists_mem_factors_of_dvd hx hp' hp'x
  exact ⟨p, hp⟩

中文:
定理 存在_mem_factors
  条件: {x : α} (hx : x != 0) (h : ¬是单位 x)
  结论: 存在 p, p in factors x
  证明: by
  obtain ⟨p', hp', hp'x⟩ := WfDvdMonoid.exists_irreducible_factor h hx
  obtain ⟨p, hp, _⟩ := exists_mem_factors_of_dvd hx hp' hp'x
  exact ⟨p, hp⟩

Depends on / 依赖: WfDvdMonoid, WfDvdMonoid.exists_irreducible_factor, exists_irreducible_factor, exists_mem_factors_of_dvd
-/
theorem exists_mem_factors {x : α} (hx : x != 0) (h : ¬IsUnit x) : exists p, p in factors x := by
  obtain ⟨p', hp', hp'x⟩ := WfDvdMonoid.exists_irreducible_factor h hx
  obtain ⟨p, hp, _⟩ := exists_mem_factors_of_dvd hx hp' hp'x
  exact ⟨p, hp⟩

/--
theorem `factors_eq_singleton_of_irreducible` / 定理 `factors_eq_singleton_of_irreducible`

English:
theorem factors_eq_singleton_of_irreducible
  given: {a : α} (ha : Irreducible a)
  proof: by
  obtain ⟨b, hbmem, hab⟩ := exists_mem_factors_of_dvd ha.ne_zero ha dvd_rfl
exact ⟨b, hab, .symm Multiset.eq_of_le_of_card_le (Multiset.singleton_le.mpr hbmem)
    (by rw [card_factors_of_irreducible ha, Multiset.card_singleton])⟩

中文:
定理 factors_eq_singleton_of_irreducible
  条件: {a : α} (ha : 不可约 a)
  证明: by
  obtain ⟨b, hbmem, hab⟩ := exists_mem_factors_of_dvd ha.ne_zero ha dvd_rfl
exact ⟨b, hab, .symm Multiset.eq_of_le_of_card_le (Multiset.singleton_le.mpr hbmem)
    (by rw [card_factors_of_irreducible ha, Multiset.card_singleton])⟩

Depends on / 依赖: Multiset, Multiset.card_singleton, Multiset.eq_of_le_of_card_le, Multiset.singleton_le.mpr, card_factors_of_irreducible, card_singleton, dvd_rfl, eq_of_le_of_card_le, exists_mem_factors_of_dvd, ha.ne_zero, ne_zero, singleton_le
-/
theorem factors_eq_singleton_of_irreducible {a : α} (ha : Irreducible a) :
    exists b, Associated a b ∧ factors a = {b} := by
  obtain ⟨b, hbmem, hab⟩ := exists_mem_factors_of_dvd ha.ne_zero ha dvd_rfl
exact ⟨b, hab, .symm Multiset.eq_of_le_of_card_le (Multiset.singleton_le.mpr hbmem)
    (by rw [card_factors_of_irreducible ha, Multiset.card_singleton])⟩

/--
theorem `factors_mul` / 定理 `factors_mul`

English:
theorem factors_mul
  given: {x y : α} (hx : x != 0) (hy : y != 0)
  proof: by
  classical
  refine
    factors_unique irreducible_of_factor
      (fun a ha =>
        (mem_add.mp ha).by_cases (irreducible_of_factor _) (irreducible_of_factor _))
      ((factors_prod (mul_ne_zero hx hy)).trans ?_)
  rw [prod_add]
  exact (Associated.mul_mul (factors_prod hx) (factors_prod hy

中文:
定理 factors_mul
  条件: {x y : α} (hx : x != 0) (hy : y != 0)
  证明: by
  classical
  refine
    factors_unique irreducible_of_factor
      (fun a ha =>
        (mem_add.mp ha).by_cases (irreducible_of_factor _) (irreducible_of_factor _))
      ((factors_prod (mul_ne_zero hx hy)).trans ?_)
  rw [prod_add]
  exact (Associated.mul_mul (factors_prod hx) (factors_prod hy

Depends on / 依赖: Associated, Associated.mul_mul, classical, factors_prod, factors_unique, irreducible_of_factor, mem_add, mem_add.mp, mul_mul, mul_ne_zero, prod_add
-/
theorem factors_mul {x y : α} (hx : x != 0) (hy : y != 0) :
    Rel Associated (factors (x * y)) (factors x + factors y) := by
  classical
  refine
    factors_unique irreducible_of_factor
      (fun a ha =>
        (mem_add.mp ha).by_cases (irreducible_of_factor _) (irreducible_of_factor _))
      ((factors_prod (mul_ne_zero hx hy)).trans ?_)
  rw [prod_add]
  exact (Associated.mul_mul (factors_prod hx) (factors_prod hy)).symm

/--
theorem `factors_pow` / 定理 `factors_pow`

English:
theorem factors_pow
  given: {x : α} (n : Nat)
  proof: by
  match n with
  | 0 => rw [zero_nsmul, pow_zero, factors_one, rel_zero_right]
  | n + 1 =>
    by_cases h0 : x = 0
    · simp [h0, zero_pow n.succ_ne_zero, nsmul_zero]
    · rw [pow_succ', succ_nsmul']
      refine Rel.trans _ (factors_mul h0 (pow_ne_zero n h0)) ?_
refine Rel.add ?_ factors_pow 

中文:
定理 factors_pow
  条件: {x : α} (n : 自然数)
  证明: by
  match n with
  | 0 => rw [zero_nsmul, pow_zero, factors_one, rel_zero_right]
  | n + 1 =>
    by_cases h0 : x = 0
    · simp [h0, zero_pow n.succ_ne_zero, nsmul_zero]
    · rw [pow_succ', succ_nsmul']
      refine Rel.trans _ (factors_mul h0 (pow_ne_zero n h0)) ?_
refine Rel.add ?_ factors_pow 

Depends on / 依赖: Associated, Associated.refl, Rel.add, Rel.trans, factors_mul, factors_one, factors_pow, n.succ_ne_zero, nsmul_zero, pow_ne_zero, pow_succ, pow_zero, rel_refl_of_refl_on, rel_zero_right, succ_ne_zero, succ_nsmul, zero_nsmul, zero_pow
-/
theorem factors_pow {x : α} (n : Nat) :
    Rel Associated (factors (x ^ n)) (n • factors x) := by
  match n with
  | 0 => rw [zero_nsmul, pow_zero, factors_one, rel_zero_right]
  | n + 1 =>
    by_cases h0 : x = 0
    · simp [h0, zero_pow n.succ_ne_zero, nsmul_zero]
    · rw [pow_succ', succ_nsmul']
      refine Rel.trans _ (factors_mul h0 (pow_ne_zero n h0)) ?_
refine Rel.add ?_ factors_pow n
      exact rel_refl_of_refl_on fun y _ => Associated.refl _

/--
theorem `factors_pow_count_prod` / 定理 `factors_pow_count_prod`

English:
theorem factors_pow_count_prod
  given: [DecidableEq α] {x : α} (hx : x != 0)
  proof: calc
  _ = prod (∑ a in toFinset (factors x), count a (factors x) • {a}) := by
    simp only [prod_sum, prod_nsmul, prod_singleton]
  _ = prod (factors x) := by rw [toFinset_sum_count_nsmul_eq (factors x)]
  _ ~ᵤ x := factors_prod hx

中文:
定理 factors_pow_count_prod
  条件: [DecidableEq α] {x : α} (hx : x != 0)
  证明: calc
  _ = prod (∑ a in toFinset (factors x), count a (factors x) • {a}) := by
    simp only [prod_sum, prod_nsmul, prod_singleton]
  _ = prod (factors x) := by rw [toFinset_sum_count_nsmul_eq (factors x)]
  _ ~ᵤ x := factors_prod hx

Depends on / 依赖: factors, factors_prod, prod_nsmul, prod_singleton, prod_sum, toFinset, toFinset_sum_count_nsmul_eq
-/
theorem factors_pow_count_prod [DecidableEq α] {x : α} (hx : x != 0) :
    (∏ p in (factors x).toFinset, p ^ (factors x).count p) ~ᵤ x :=
  calc
  _ = prod (∑ a in toFinset (factors x), count a (factors x) • {a}) := by
    simp only [prod_sum, prod_nsmul, prod_singleton]
  _ = prod (factors x) := by rw [toFinset_sum_count_nsmul_eq (factors x)]
  _ ~ᵤ x := factors_prod hx

/--
theorem `factors_rel_of_associated` / 定理 `factors_rel_of_associated`

English:
theorem factors_rel_of_associated
  given: {a b : α} (h : Associated a b)
  proof: by
  rcases iff_iff_and_or_not_and_not.mp h.eq_zero_iff with (⟨rfl, rfl⟩ | ⟨ha, hb⟩)
  · simp
  · refine factors_unique irreducible_of_factor irreducible_of_factor ?_
    exact ((factors_prod ha).trans h).trans (factors_prod hb).symm

中文:
定理 factors_rel_of_associated
  条件: {a b : α} (h : Associated a b)
  证明: by
  rcases iff_iff_and_or_not_and_not.mp h.eq_zero_iff with (⟨rfl, rfl⟩ | ⟨ha, hb⟩)
  · simp
  · refine factors_unique irreducible_of_factor irreducible_of_factor ?_
    exact ((factors_prod ha).trans h).trans (factors_prod hb).symm

Depends on / 依赖: eq_zero_iff, factors_prod, factors_unique, h.eq_zero_iff, iff_iff_and_or_not_and_not, iff_iff_and_or_not_and_not.mp, irreducible_of_factor
-/
theorem factors_rel_of_associated {a b : α} (h : Associated a b) :
    Rel Associated (factors a) (factors b) := by
  rcases iff_iff_and_or_not_and_not.mp h.eq_zero_iff with (⟨rfl, rfl⟩ | ⟨ha, hb⟩)
  · simp
  · refine factors_unique irreducible_of_factor irreducible_of_factor ?_
    exact ((factors_prod ha).trans h).trans (factors_prod hb).symm

/--
theorem `factors_of_isUnit` / 定理 `factors_of_isUnit`

English:
theorem factors_of_isUnit
  given: {x : α} (hx : IsUnit x)
  statement: factors x = 0
  proof: by
  simpa using factors_rel_of_associated (associated_one_iff_isUnit.mpr hx)

@[simp]

中文:
定理 factors_of_isUnit
  条件: {x : α} (hx : 是单位 x)
  结论: factors x = 0
  证明: by
  simpa using factors_rel_of_associated (associated_one_iff_isUnit.mpr hx)

@[simp]

Depends on / 依赖: associated_one_iff_isUnit, associated_one_iff_isUnit.mpr, factors_rel_of_associated
-/
theorem factors_of_isUnit {x : α} (hx : IsUnit x) : factors x = 0 := by
  simpa using factors_rel_of_associated (associated_one_iff_isUnit.mpr hx)

@[simp]
/--
theorem `factors_eq_zero` / 定理 `factors_eq_zero`

English:
theorem factors_eq_zero
  given: {x : α} (hx : x != 0)
  statement: factors x = 0 ↔ IsUnit x
  proof: ⟨fun h => by contrapose! h; simpa [eq_zero_iff_forall_notMem] using exists_mem_factors hx h,
    factors_of_isUnit⟩

@[simp]

中文:
定理 factors_eq_zero
  条件: {x : α} (hx : x != 0)
  结论: factors x = 0 ↔ 是单位 x
  证明: ⟨fun h => by contrapose! h; simpa [eq_zero_iff_forall_notMem] using exists_mem_factors hx h,
    factors_of_isUnit⟩

@[simp]

Depends on / 依赖: contrapose, eq_zero_iff_forall_notMem, exists_mem_factors, factors_of_isUnit
-/
theorem factors_eq_zero {x : α} (hx : x != 0) : factors x = 0 ↔ IsUnit x :=
  ⟨fun h => by contrapose! h; simpa [eq_zero_iff_forall_notMem] using exists_mem_factors hx h,
    factors_of_isUnit⟩

@[simp]
/--
theorem `factors_pos` / 定理 `factors_pos`

English:
theorem factors_pos
  given: {x : α} (hx : x != 0)
  statement: 0 < factors x ↔ ¬IsUnit x
  proof: bot_lt_iff_ne_bot.trans (not_iff_not.mpr (factors_eq_zero hx))

中文:
定理 factors_pos
  条件: {x : α} (hx : x != 0)
  结论: 0 < factors x ↔ ¬是单位 x
  证明: bot_lt_iff_ne_bot.trans (not_iff_not.mpr (factors_eq_zero hx))

Depends on / 依赖: bot_lt_iff_ne_bot, bot_lt_iff_ne_bot.trans, factors_eq_zero, not_iff_not, not_iff_not.mpr
-/
theorem factors_pos {x : α} (hx : x != 0) : 0 < factors x ↔ ¬IsUnit x :=
  bot_lt_iff_ne_bot.trans (not_iff_not.mpr (factors_eq_zero hx))

end UniqueFactorizationMonoid

namespace Associates

attribute [local instance] Associated.setoid

open Multiset UniqueFactorizationMonoid

variable [CommMonoidWithZero α] [UniqueFactorizationMonoid α]

set_option backward.isDefEq.respectTransparency false in
/--
theorem `unique'` / 定理 `unique'`

English:
theorem unique'
  given: {p q : Multiset (Associates α)}
  proof: by
  apply Multiset.induction_on_multiset_quot p
  apply Multiset.induction_on_multiset_quot q
  intro s t hs ht eq
  refine Multiset.map_mk_eq_map_mk_of_rel (UniqueFactorizationMonoid.factors_unique ?_ ?_ ?_)
· exact fun a ha => irreducible_mk.1 hs _ Multiset.mem_map_of_mem _ ha
· exact fun a ha =>

中文:
定理 unique'
  条件: {p q : Multiset (Associates α)}
  证明: by
  apply Multiset.induction_on_multiset_quot p
  apply Multiset.induction_on_multiset_quot q
  intro s t hs ht eq
  refine Multiset.map_mk_eq_map_mk_of_rel (UniqueFactorizationMonoid.factors_unique ?_ ?_ ?_)
· exact fun a ha => irreducible_mk.1 hs _ Multiset.mem_map_of_mem _ ha
· exact fun a ha =>

Depends on / 依赖: Associates, Associates.mk, Multiset, Multiset.induction_on_multiset_quot, Multiset.map_mk_eq_map_mk_of_rel, Multiset.mem_map_of_mem, Quot.mk, Setoid, Setoid.r, UniqueFactorizationMonoid, UniqueFactorizationMonoid.factors_unique, factors_unique, induction_on_multiset_quot, irreducible_mk, map_mk_eq_map_mk_of_rel, mem_map_of_mem, mk_eq_mk_iff_associated, prod_mk, quot_mk_eq_mk
-/
theorem unique' {p q : Multiset (Associates α)} :
    (forall a in p, Irreducible a) -> (forall a in q, Irreducible a) -> p.prod = q.prod -> p = q := by
  apply Multiset.induction_on_multiset_quot p
  apply Multiset.induction_on_multiset_quot q
  intro s t hs ht eq
  refine Multiset.map_mk_eq_map_mk_of_rel (UniqueFactorizationMonoid.factors_unique ?_ ?_ ?_)
· exact fun a ha => irreducible_mk.1 hs _ Multiset.mem_map_of_mem _ ha
· exact fun a ha => irreducible_mk.1 ht _ Multiset.mem_map_of_mem _ ha
  have eq' : (Quot.mk Setoid.r : α -> Associates α) = Associates.mk := funext quot_mk_eq_mk
  rwa [eq', prod_mk, prod_mk, mk_eq_mk_iff_associated] at eq

/--
theorem `prod_le_prod_iff_le` / 定理 `prod_le_prod_iff_le`

English:
theorem prod_le_prod_iff_le
  statement: [Nontrivial α] {p q : Multiset (Associates α)}
  proof: by
  refine ⟨?_, prod_le_prod⟩
  rintro ⟨c, eqc⟩
  refine Multiset.le_iff_exists_add.2 ⟨factors c, unique' hq (fun x hx => ?_) ?_⟩
  · obtain h | h := Multiset.mem_add.1 hx
    · exact hp x h
    · exact irreducible_of_factor _ h
  · rw [eqc, Multiset.prod_add]
    congr
    refine associated_iff_eq

中文:
定理 prod_le_prod_iff_le
  结论: [非平凡 α] {p q : Multiset (Associates α)}
  证明: by
  refine ⟨?_, prod_le_prod⟩
  rintro ⟨c, eqc⟩
  refine Multiset.le_iff_exists_add.2 ⟨factors c, unique' hq (fun x hx => ?_) ?_⟩
  · obtain h | h := Multiset.mem_add.1 hx
    · exact hp x h
    · exact irreducible_of_factor _ h
  · rw [eqc, Multiset.prod_add]
    congr
    refine associated_iff_eq

Depends on / 依赖: Multiset, Multiset.le_iff_exists_add, Multiset.mem_add, Multiset.prod_add, associated_iff_eq, associated_iff_eq.mp, factors, factors_prod, irreducible_of_factor, le_iff_exists_add, mem_add, mul_zero, not_irreducible_zero, prod_add, prod_eq_zero_iff, prod_le_prod, unique
-/
theorem prod_le_prod_iff_le [Nontrivial α] {p q : Multiset (Associates α)}
    (hp : forall a in p, Irreducible a) (hq : forall a in q, Irreducible a) : p.prod <= q.prod ↔ p <= q := by
  refine ⟨?_, prod_le_prod⟩
  rintro ⟨c, eqc⟩
  refine Multiset.le_iff_exists_add.2 ⟨factors c, unique' hq (fun x hx => ?_) ?_⟩
  · obtain h | h := Multiset.mem_add.1 hx
    · exact hp x h
    · exact irreducible_of_factor _ h
  · rw [eqc, Multiset.prod_add]
    congr
    refine associated_iff_eq.mp (factors_prod fun hc => ?_).symm
    refine not_irreducible_zero (hq _ ?_)
    rw [← prod_eq_zero_iff]; rw [eqc]; rw [hc]; rw [mul_zero]

end Associates

section ExistsPrimeFactors

variable [CommMonoidWithZero α] [IsCancelMulZero α]
variable (pf : forall a : α, a != 0 -> exists f : Multiset α, (forall b in f, Prime b) ∧ f.prod ~ᵤ a)
include pf

/--
theorem `WfDvdMonoid.of_exists_prime_factors` / 定理 `WfDvdMonoid.of_exists_prime_factors`

English:
theorem WfDvdMonoid.of_exists_prime_factors
  statement: WfDvdMonoid α
  proof: ⟨by
    refine RelHomClass.wellFounded
      (RelHom.mk ?_ ?_ : (DvdNotUnit : α -> α -> Prop) ->r ((· < ·) : Nat∞ -> Nat∞ -> Prop)) wellFounded_lt
    · intro a
      by_cases h : a = 0
      · exact ⊤
      exact ↑(Multiset.card (Classical.choose (pf a h)))
    rintro a b ⟨ane0, ⟨c, hc, b_eq⟩⟩
    

中文:
定理 WfDvdMonoid.of_存在_prime_factors
  结论: WfDvdMonoid α
  证明: ⟨by
    refine RelHomClass.wellFounded
      (RelHom.mk ?_ ?_ : (DvdNotUnit : α -> α -> Prop) ->r ((· < ·) : Nat∞ -> Nat∞ -> Prop)) wellFounded_lt
    · intro a
      by_cases h : a = 0
      · exact ⊤
      exact ↑(Multiset.card (Classical.choose (pf a h)))
    rintro a b ⟨ane0, ⟨c, hc, b_eq⟩⟩
    

Depends on / 依赖: Classical, Classical.choose, DvdNotUnit, Multiset, Multiset.card, Nat.cast_lt, RelHom, RelHom.mk, RelHomClass, RelHomClass.wellFounded, b_eq, cast_lt, dif_neg, lt_top_iff_ne_top, mul_zero, wellFounded, wellFounded_lt
-/
theorem WfDvdMonoid.of_exists_prime_factors : WfDvdMonoid α :=
  ⟨by
    refine RelHomClass.wellFounded
      (RelHom.mk ?_ ?_ : (DvdNotUnit : α -> α -> Prop) ->r ((· < ·) : Nat∞ -> Nat∞ -> Prop)) wellFounded_lt
    · intro a
      by_cases h : a = 0
      · exact ⊤
      exact ↑(Multiset.card (Classical.choose (pf a h)))
    rintro a b ⟨ane0, ⟨c, hc, b_eq⟩⟩
    rw [dif_neg ane0]
    by_cases h : b = 0
    · simp [h, lt_top_iff_ne_top]
    · rw [dif_neg h, Nat.cast_lt]
      have cne0 : c != 0 := by
        refine mt (fun con => ?_) h
        rw [b_eq]; rw [con]; rw [mul_zero]
      calc
        Multiset.card (Classical.choose (pf a ane0)) <
            _ + Multiset.card (Classical.choose (pf c cne0)) :=
          lt_add_of_pos_right _
            (Multiset.card_pos.mpr fun con => hc (associated_one_iff_isUnit.mp ?_))
        _ = Multiset.card (Classical.choose (pf a ane0) + Classical.choose (pf c cne0)) :=
          (Multiset.card_add _ _).symm
        _ = Multiset.card (Classical.choose (pf b h)) :=
          Multiset.card_eq_card_of_rel
          (prime_factors_unique ?_ (Classical.choose_spec (pf _ h)).1 ?_)
      · convert! (Classical.choose_spec (pf c cne0)).2.symm
        rw [con]; rw [Multiset.prod_zero]
      · intro x hadd
        rw [Multiset.mem_add] at hadd
        rcases hadd with h | h <;> apply (Classical.choose_spec (pf _ _)).1 _ h <;> assumption
      · rw [Multiset.prod_add]
        trans a * c
        · apply Associated.mul_mul <;> apply (Classical.choose_spec (pf _ _)).2 <;> assumption
        · rw [← b_eq]
          apply (Classical.choose_spec (pf _ _)).2.symm; assumption⟩

/--
theorem `irreducible_iff_prime_of_exists_prime_factors` / 定理 `irreducible_iff_prime_of_exists_prime_factors`

English:
theorem irreducible_iff_prime_of_exists_prime_factors
  given: {p : α}
  statement: Irreducible p ↔ Prime p
  proof: by
  by_cases hp0 : p = 0
  · simp [hp0]
  refine ⟨fun h => ?_, Prime.irreducible⟩
  obtain ⟨f, hf⟩ := pf p hp0
  obtain ⟨q, hq, rfl⟩ := prime_factors_irreducible h hf
  rw [hq.prime_iff]
  exact hf.1 q (Multiset.mem_singleton_self _)

中文:
定理 irreducible_iff_prime_of_存在_prime_factors
  条件: {p : α}
  结论: 不可约 p ↔ 素 p
  证明: by
  by_cases hp0 : p = 0
  · simp [hp0]
  refine ⟨fun h => ?_, Prime.irreducible⟩
  obtain ⟨f, hf⟩ := pf p hp0
  obtain ⟨q, hq, rfl⟩ := prime_factors_irreducible h hf
  rw [hq.prime_iff]
  exact hf.1 q (Multiset.mem_singleton_self _)

Depends on / 依赖: Multiset, Multiset.mem_singleton_self, Prime.irreducible, hq.prime_iff, irreducible, mem_singleton_self, prime_factors_irreducible, prime_iff
-/
theorem irreducible_iff_prime_of_exists_prime_factors {p : α} : Irreducible p ↔ Prime p := by
  by_cases hp0 : p = 0
  · simp [hp0]
  refine ⟨fun h => ?_, Prime.irreducible⟩
  obtain ⟨f, hf⟩ := pf p hp0
  obtain ⟨q, hq, rfl⟩ := prime_factors_irreducible h hf
  rw [hq.prime_iff]
  exact hf.1 q (Multiset.mem_singleton_self _)

/--
theorem `UniqueFactorizationMonoid.of_exists_prime_factors` / 定理 `UniqueFactorizationMonoid.of_exists_prime_factors`

English:
theorem UniqueFactorizationMonoid.of_exists_prime_factors
  statement: UniqueFactorizationMonoid α
  proof: { WfDvdMonoid.of_exists_prime_factors pf with
    irreducible_iff_prime := irreducible_iff_prime_of_exists_prime_factors pf }

中文:
定理 唯一分解幺半群.of_存在_prime_factors
  结论: 唯一分解幺半群 α
  证明: { WfDvdMonoid.of_exists_prime_factors pf with
    irreducible_iff_prime := irreducible_iff_prime_of_exists_prime_factors pf }

Depends on / 依赖: WfDvdMonoid, WfDvdMonoid.of_exists_prime_factors, irreducible_iff_prime, irreducible_iff_prime_of_exists_prime_factors, of_exists_prime_factors
-/
theorem UniqueFactorizationMonoid.of_exists_prime_factors : UniqueFactorizationMonoid α :=
  { WfDvdMonoid.of_exists_prime_factors pf with
    irreducible_iff_prime := irreducible_iff_prime_of_exists_prime_factors pf }

end ExistsPrimeFactors

/--
theorem `UniqueFactorizationMonoid.iff_exists_prime_factors` / 定理 `UniqueFactorizationMonoid.iff_exists_prime_factors`

English:
theorem UniqueFactorizationMonoid.iff_exists_prime_factors
  statement: [CommMonoidWithZero α]
  proof: ⟨fun h => @UniqueFactorizationMonoid.exists_prime_factors _ _ h,
    UniqueFactorizationMonoid.of_exists_prime_factors⟩

中文:
定理 唯一分解幺半群.iff_存在_prime_factors
  结论: [带零交换幺半群 α]
  证明: ⟨fun h => @UniqueFactorizationMonoid.exists_prime_factors _ _ h,
    UniqueFactorizationMonoid.of_exists_prime_factors⟩

Depends on / 依赖: UniqueFactorizationMonoid, UniqueFactorizationMonoid.exists_prime_factors, UniqueFactorizationMonoid.of_exists_prime_factors, exists_prime_factors, of_exists_prime_factors
-/
theorem UniqueFactorizationMonoid.iff_exists_prime_factors [CommMonoidWithZero α]
    [IsCancelMulZero α] :
    UniqueFactorizationMonoid α ↔
      forall a : α, a != 0 -> exists f : Multiset α, (forall b in f, Prime b) ∧ f.prod ~ᵤ a :=
  ⟨fun h => @UniqueFactorizationMonoid.exists_prime_factors _ _ h,
    UniqueFactorizationMonoid.of_exists_prime_factors⟩

section

variable {β : Type*} [CommMonoidWithZero α] [CommMonoidWithZero β]

/--
theorem `MulEquiv.uniqueFactorizationMonoid` / 定理 `MulEquiv.uniqueFactorizationMonoid`

English:
theorem MulEquiv.uniqueFactorizationMonoid
  given: (e : α ≃* β) (hα : UniqueFactorizationMonoid α)
  proof: by
  have := e.isCancelMulZero_iff.mp inferInstance
  rw [UniqueFactorizationMonoid.iff_exists_prime_factors] at hα ⊢
  intro a ha
  obtain ⟨w, hp, u, h⟩ :=
    hα (e.symm a) fun h =>
ha by
        convert! ← map_zero e
        simp [← h]
  exact
    ⟨w.map e, fun b hb =>
        let ⟨c, hc, he⟩ := 

中文:
定理 乘法等价.uniqueFactorizationMonoid
  条件: (e : α ≃* β) (hα : 唯一分解幺半群 α)
  证明: by
  have := e.isCancelMulZero_iff.mp inferInstance
  rw [UniqueFactorizationMonoid.iff_exists_prime_factors] at hα ⊢
  intro a ha
  obtain ⟨w, hp, u, h⟩ :=
    hα (e.symm a) fun h =>
ha by
        convert! ← map_zero e
        simp [← h]
  exact
    ⟨w.map e, fun b hb =>
        let ⟨c, hc, he⟩ := 

Depends on / 依赖: MonoidHom, MonoidHom.coe_coe, Multiset, Multiset.mem_map, Multiset.prod_hom, UniqueFactorizationMonoid, UniqueFactorizationMonoid.iff_exists_prime_factors, Units.coe_map, Units.map, apply_symm_apply, coe_coe, coe_map, convert, e.isCancelMulZero_iff.mp, e.symm, e.toMonoidHom, iff_exists_prime_factors, isCancelMulZero_iff, map_mul, map_zero
-/
theorem MulEquiv.uniqueFactorizationMonoid (e : α ≃* β) (hα : UniqueFactorizationMonoid α) :
    UniqueFactorizationMonoid β := by
  have := e.isCancelMulZero_iff.mp inferInstance
  rw [UniqueFactorizationMonoid.iff_exists_prime_factors] at hα ⊢
  intro a ha
  obtain ⟨w, hp, u, h⟩ :=
    hα (e.symm a) fun h =>
ha by
        convert! ← map_zero e
        simp [← h]
  exact
    ⟨w.map e, fun b hb =>
        let ⟨c, hc, he⟩ := Multiset.mem_map.1 hb
        he ▸ (prime_iff e).2 (hp c hc),
        Units.map e.toMonoidHom u,
      by
        rw [Multiset.prod_hom]; rw [toMonoidHom_eq_coe]; rw [Units.coe_map]; rw [MonoidHom.coe_coe]; rw [← map_mul e]; rw [h]; rw [apply_symm_apply]⟩

/--
theorem `MulEquiv.uniqueFactorizationMonoid_iff` / 定理 `MulEquiv.uniqueFactorizationMonoid_iff`

English:
theorem MulEquiv.uniqueFactorizationMonoid_iff
  given: (e : α ≃* β)
  proof: ⟨e.uniqueFactorizationMonoid, e.symm.uniqueFactorizationMonoid⟩

中文:
定理 乘法等价.uniqueFactorizationMonoid_iff
  条件: (e : α ≃* β)
  证明: ⟨e.uniqueFactorizationMonoid, e.symm.uniqueFactorizationMonoid⟩

Depends on / 依赖: e.symm.uniqueFactorizationMonoid, e.uniqueFactorizationMonoid, uniqueFactorizationMonoid
-/
theorem MulEquiv.uniqueFactorizationMonoid_iff (e : α ≃* β) :
    UniqueFactorizationMonoid α ↔ UniqueFactorizationMonoid β :=
  ⟨e.uniqueFactorizationMonoid, e.symm.uniqueFactorizationMonoid⟩

end

namespace UniqueFactorizationMonoid

/--
theorem `of_existsUnique_irreducible_factors` / 定理 `of_existsUnique_irreducible_factors`

English:
theorem of_existsUnique_irreducible_factors
  statement: [CommMonoidWithZero α] [IsCancelMulZero α]
  proof: UniqueFactorizationMonoid.of_exists_prime_factors
    (by
      convert! eif using 7
      simp_rw [irreducible_iff_prime_of_existsUnique_irreducible_factors eif uif])

中文:
定理 of_存在Unique_irreducible_factors
  结论: [带零交换幺半群 α] [是乘零消去 α]
  证明: UniqueFactorizationMonoid.of_exists_prime_factors
    (by
      convert! eif using 7
      simp_rw [irreducible_iff_prime_of_existsUnique_irreducible_factors eif uif])

Depends on / 依赖: UniqueFactorizationMonoid, UniqueFactorizationMonoid.of_exists_prime_factors, convert, irreducible_iff_prime_of_existsUnique_irreducible_factors, of_exists_prime_factors, simp_rw
-/
theorem of_existsUnique_irreducible_factors [CommMonoidWithZero α] [IsCancelMulZero α]
    (eif : forall a : α, a != 0 -> exists f : Multiset α, (forall b in f, Irreducible b) ∧ f.prod ~ᵤ a)
    (uif :
      forall f g : Multiset α,
        (forall x in f, Irreducible x) ->
          (forall x in g, Irreducible x) -> f.prod ~ᵤ g.prod -> Multiset.Rel Associated f g) :
    UniqueFactorizationMonoid α :=
  UniqueFactorizationMonoid.of_exists_prime_factors
    (by
      convert! eif using 7
      simp_rw [irreducible_iff_prime_of_existsUnique_irreducible_factors eif uif])

variable {R : Type*} [CommMonoidWithZero R] [UniqueFactorizationMonoid R]

/--
theorem `isRelPrime_iff_no_prime_factors` / 定理 `isRelPrime_iff_no_prime_factors`

English:
theorem isRelPrime_iff_no_prime_factors
  given: {a b : R} (ha : a != 0)
  proof: ⟨fun h _ ha hb => (·.not_isUnit <| h ha hb),
    fun h => WfDvdMonoid.isRelPrime_of_no_irreducible_factors
      (ha ·.1) fun _ irr ha hb => h ha hb (UniqueFactorizationMonoid.irreducible_iff_prime.mp irr)⟩

中文:
定理 isRelPrime_iff_no_prime_factors
  条件: {a b : R} (ha : a != 0)
  证明: ⟨fun h _ ha hb => (·.not_isUnit <| h ha hb),
    fun h => WfDvdMonoid.isRelPrime_of_no_irreducible_factors
      (ha ·.1) fun _ irr ha hb => h ha hb (UniqueFactorizationMonoid.irreducible_iff_prime.mp irr)⟩

Depends on / 依赖: UniqueFactorizationMonoid, UniqueFactorizationMonoid.irreducible_iff_prime.mp, WfDvdMonoid, WfDvdMonoid.isRelPrime_of_no_irreducible_factors, irreducible_iff_prime, isRelPrime_of_no_irreducible_factors, not_isUnit
-/
theorem isRelPrime_iff_no_prime_factors {a b : R} (ha : a != 0) :
    IsRelPrime a b ↔ forall ⦃d⦄, d ∣ a -> d ∣ b -> ¬Prime d :=
  ⟨fun h _ ha hb => (·.not_isUnit <| h ha hb),
    fun h => WfDvdMonoid.isRelPrime_of_no_irreducible_factors
      (ha ·.1) fun _ irr ha hb => h ha hb (UniqueFactorizationMonoid.irreducible_iff_prime.mp irr)⟩

/--
theorem `dvd_of_dvd_mul_left_of_no_prime_factors` / 定理 `dvd_of_dvd_mul_left_of_no_prime_factors`

English:
theorem dvd_of_dvd_mul_left_of_no_prime_factors
  statement: {a b c : R} (ha : a != 0)
  proof: ((isRelPrime_iff_no_prime_factors ha).mpr h).dvd_of_dvd_mul_right

中文:
定理 dvd_of_dvd_mul_left_of_no_prime_factors
  结论: {a b c : R} (ha : a != 0)
  证明: ((isRelPrime_iff_no_prime_factors ha).mpr h).dvd_of_dvd_mul_right

Depends on / 依赖: dvd_of_dvd_mul_right, isRelPrime_iff_no_prime_factors
-/
theorem dvd_of_dvd_mul_left_of_no_prime_factors {a b c : R} (ha : a != 0)
    (h : forall ⦃d⦄, d ∣ a -> d ∣ c -> ¬Prime d) : a ∣ b * c -> a ∣ b :=
  ((isRelPrime_iff_no_prime_factors ha).mpr h).dvd_of_dvd_mul_right

/--
theorem `dvd_of_dvd_mul_right_of_no_prime_factors` / 定理 `dvd_of_dvd_mul_right_of_no_prime_factors`

English:
theorem dvd_of_dvd_mul_right_of_no_prime_factors
  statement: {a b c : R} (ha : a != 0)
  proof: by
  simpa [mul_comm b c] using dvd_of_dvd_mul_left_of_no_prime_factors ha @no_factors

中文:
定理 dvd_of_dvd_mul_right_of_no_prime_factors
  结论: {a b c : R} (ha : a != 0)
  证明: by
  simpa [mul_comm b c] using dvd_of_dvd_mul_left_of_no_prime_factors ha @no_factors

Depends on / 依赖: dvd_of_dvd_mul_left_of_no_prime_factors, mul_comm, no_factors
-/
theorem dvd_of_dvd_mul_right_of_no_prime_factors {a b c : R} (ha : a != 0)
    (no_factors : forall {d}, d ∣ a -> d ∣ b -> ¬Prime d) : a ∣ b * c -> a ∣ c := by
  simpa [mul_comm b c] using dvd_of_dvd_mul_left_of_no_prime_factors ha @no_factors

/--
theorem `exists_reduced_factors` / 定理 `exists_reduced_factors`

English:
theorem exists_reduced_factors
  proof: by
  intro a
  refine induction_on_prime a ?_ ?_ ?_
  · intros
    contradiction
  · intro a a_unit _ b
    use a, b, 1
    constructor
    · intro p p_dvd_a _
      exact isUnit_of_dvd_unit p_dvd_a a_unit
    · simp
  · intro a p a_ne_zero p_prime ih_a pa_ne_zero b
    by_cases h : p ∣ b
    · rcas

中文:
定理 存在_reduced_factors
  证明: by
  intro a
  refine induction_on_prime a ?_ ?_ ?_
  · intros
    contradiction
  · intro a a_unit _ b
    use a, b, 1
    constructor
    · intro p p_dvd_a _
      exact isUnit_of_dvd_unit p_dvd_a a_unit
    · simp
  · intro a p a_ne_zero p_prime ih_a pa_ne_zero b
    by_cases h : p ∣ b
    · rcas

Depends on / 依赖: a_ne_zero, a_unit, coprime, ih_a, induction_on_prime, intros, isUnit_of_dvd_unit, mul_assoc, no_factor, p_dvd_a, p_prime, pa_ne_zero
-/
theorem exists_reduced_factors :
    forall a != (0 : R), forall b,
      exists a' b' c', IsRelPrime a' b' ∧ c' * a' = a ∧ c' * b' = b := by
  intro a
  refine induction_on_prime a ?_ ?_ ?_
  · intros
    contradiction
  · intro a a_unit _ b
    use a, b, 1
    constructor
    · intro p p_dvd_a _
      exact isUnit_of_dvd_unit p_dvd_a a_unit
    · simp
  · intro a p a_ne_zero p_prime ih_a pa_ne_zero b
    by_cases h : p ∣ b
    · rcases h with ⟨b, rfl⟩
      obtain ⟨a', b', c', no_factor, ha', hb'⟩ := ih_a a_ne_zero b
      refine ⟨a', b', p * c', @no_factor, ?_, ?_⟩
      · rw [mul_assoc, ha']
      · rw [mul_assoc, hb']
    · obtain ⟨a', b', c', coprime, rfl, rfl⟩ := ih_a a_ne_zero b
      refine ⟨p * a', b', c', ?_, mul_left_comm _ _ _, rfl⟩
      intro q q_dvd_pa' q_dvd_b'
      rcases p_prime.left_dvd_or_dvd_right_of_dvd_mul q_dvd_pa' with p_dvd_q | q_dvd_a'
      · have : p ∣ c' * b' := dvd_mul_of_dvd_right (p_dvd_q.trans q_dvd_b') _
        contradiction
      exact coprime q_dvd_a' q_dvd_b'

/--
theorem `exists_reduced_factors'` / 定理 `exists_reduced_factors'`

English:
theorem exists_reduced_factors'
  given: (a b : R) (hb : b != 0)
  proof: let ⟨b', a', c', no_factor, hb, ha⟩ := exists_reduced_factors b hb a
  ⟨a', b', c', fun _ hpb hpa => no_factor hpa hpb, ha, hb⟩

中文:
定理 存在_reduced_factors'
  条件: (a b : R) (hb : b != 0)
  证明: let ⟨b', a', c', no_factor, hb, ha⟩ := exists_reduced_factors b hb a
  ⟨a', b', c', fun _ hpb hpa => no_factor hpa hpb, ha, hb⟩

Depends on / 依赖: exists_reduced_factors, no_factor
-/
theorem exists_reduced_factors' (a b : R) (hb : b != 0) :
    exists a' b' c', IsRelPrime a' b' ∧ c' * a' = a ∧ c' * b' = b :=
  let ⟨b', a', c', no_factor, hb, ha⟩ := exists_reduced_factors b hb a
  ⟨a', b', c', fun _ hpb hpa => no_factor hpa hpb, ha, hb⟩

end UniqueFactorizationMonoid
