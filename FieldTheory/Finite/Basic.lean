/-
Copyright (c) 2018 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes, Joey van Langen, Casper Putz
-/
module

public import Mathlib.Algebra.CharP.Algebra
public import Mathlib.Algebra.Field.ZMod
public import Mathlib.Data.Nat.Prime.Int
public import Mathlib.Data.ZMod.ValMinAbs
public import Mathlib.LinearAlgebra.FreeModule.Finite.Matrix
public import Mathlib.FieldTheory.Finiteness
public import Mathlib.FieldTheory.Galois.Notation
public import Mathlib.FieldTheory.Perfect

/-!
# Finite fields

This file contains basic results about finite fields.
Throughout most of this file, `K` denotes a finite field
and `q` is notation for the cardinality of `K`.

See `RingTheory.IntegralDomain` for the fact that the unit group of a finite field is a
cyclic group, as well as the fact that every finite integral domain is a field
(`Fintype.fieldOfDomain`).

## Main results

1. `Fintype.card_units`: The unit group of a finite field has cardinality `q - 1`.
2. `sum_pow_units`: The sum of `x^i`, where `x` ranges over the units of `K`, is
  - `q-1` if `q-1 ∣ i`
  - `0` otherwise
3. `FiniteField.card`: The cardinality `q` is a power of the characteristic of `K`.
  See `FiniteField.card'` for a variant.

## Notation

Throughout most of this file, `K` denotes a finite field
and `q` is notation for the cardinality of `K`.

## Implementation notes

While `Fintype Kˣ` can be inferred from `Fintype K` in the presence of `DecidableEq K`,
in this file we take the `Fintype Kˣ` argument directly to reduce the chance of typeclass
diamonds, as `Fintype` carries data.

-/

@[expose] public section


variable {K : Type*} {R : Type*}

local notation "q" => Fintype.card K

open Finset

open scoped Polynomial

namespace FiniteField

section Polynomial

variable [CommRing R] [IsDomain R]

open Polynomial

/--
theorem `card_image_polynomial_eval` / 定理 `card_image_polynomial_eval`

English:
theorem card_image_polynomial_eval
  given: [DecidableEq R] [Fintype R] {p : R[X]} (hp : 0 < p.degree)
  proof: Finset.card_le_mul_card_image _ _ (fun a _ =>
    calc
      _ = #(p - C a).roots.toFinset :=
        congr_arg card (by simp [Finset.ext_iff, ← mem_roots_sub_C hp])
      _ <= Multiset.card (p - C a).roots := Multiset.toFinset_card_le _
      _ <= _ := card_roots_sub_C' hp)

中文:
定理 card_image_polynomial_eval
  条件: [DecidableEq R] [有限类型 R] {p : R[X]} (hp : 0 < p.degree)
  证明: Finset.card_le_mul_card_image _ _ (fun a _ =>
    calc
      _ = #(p - C a).roots.toFinset :=
        congr_arg card (by simp [Finset.ext_iff, ← mem_roots_sub_C hp])
      _ <= Multiset.card (p - C a).roots := Multiset.toFinset_card_le _
      _ <= _ := card_roots_sub_C' hp)

Depends on / 依赖: Finset, Finset.card_le_mul_card_image, Finset.ext_iff, Multiset, Multiset.card, Multiset.toFinset_card_le, card_le_mul_card_image, card_roots_sub_C, congr_arg, ext_iff, mem_roots_sub_C, roots.toFinset, toFinset, toFinset_card_le
-/
theorem card_image_polynomial_eval [DecidableEq R] [Fintype R] {p : R[X]} (hp : 0 < p.degree) :
    Fintype.card R <= natDegree p * #(univ.image fun x => eval x p) :=
  Finset.card_le_mul_card_image _ _ (fun a _ =>
    calc
      _ = #(p - C a).roots.toFinset :=
        congr_arg card (by simp [Finset.ext_iff, ← mem_roots_sub_C hp])
      _ <= Multiset.card (p - C a).roots := Multiset.toFinset_card_le _
      _ <= _ := card_roots_sub_C' hp)

/--
theorem `exists_root_sum_quadratic` / 定理 `exists_root_sum_quadratic`

English:
theorem exists_root_sum_quadratic
  statement: [Fintype R] {f g : R[X]} (hf2 : degree f = 2) (hg2 : degree g = 2)
  proof: letI := Classical.decEq R
  suffices ¬Disjoint (univ.image fun x : R => eval x f)
    (univ.image fun x : R => eval x (-g)) by
    simp only [disjoint_left, mem_image] at this
    push Not at this
    rcases this with ⟨x, ⟨a, _, ha⟩, ⟨b, _, hb⟩⟩
    exact ⟨a, b, by rw [ha, ← hb, eval_neg, neg_add_ca

中文:
定理 存在_root_sum_quadratic
  结论: [有限类型 R] {f g : R[X]} (hf2 : degree f = 2) (hg2 : degree g = 2)
  证明: letI := Classical.decEq R
  suffices ¬Disjoint (univ.image fun x : R => eval x f)
    (univ.image fun x : R => eval x (-g)) by
    simp only [disjoint_left, mem_image] at this
    push Not at this
    rcases this with ⟨x, ⟨a, _, ha⟩, ⟨b, _, hb⟩⟩
    exact ⟨a, b, by rw [ha, ← hb, eval_neg, neg_add_ca

Depends on / 依赖: Classical, Classical.decEq, Disjoint, disjoint_left, eval_neg, lt_irrefl, mem_image, neg_add_cancel, univ.image
-/
theorem exists_root_sum_quadratic [Fintype R] {f g : R[X]} (hf2 : degree f = 2) (hg2 : degree g = 2)
    (hR : Fintype.card R % 2 = 1) : exists a b, f.eval a + g.eval b = 0 :=
  letI := Classical.decEq R
  suffices ¬Disjoint (univ.image fun x : R => eval x f)
    (univ.image fun x : R => eval x (-g)) by
    simp only [disjoint_left, mem_image] at this
    push Not at this
    rcases this with ⟨x, ⟨a, _, ha⟩, ⟨b, _, hb⟩⟩
    exact ⟨a, b, by rw [ha, ← hb, eval_neg, neg_add_cancel]⟩
  fun hd : Disjoint _ _ =>
lt_irrefl (2 * #((univ.image fun x : R => eval x f) union univ.image fun x : R => eval x (-g)))
    calc 2 * #((univ.image fun x : R => eval x f) union univ.image fun x : R => eval x (-g))
        <= 2 * Fintype.card R := Nat.mul_le_mul_left _ (Finset.card_le_univ _)
      _ = Fintype.card R + Fintype.card R := two_mul _
      _ < natDegree f * #(univ.image fun x : R => eval x f) +
            natDegree (-g) * #(univ.image fun x : R => eval x (-g)) :=
        (add_lt_add_of_lt_of_le
          (lt_of_le_of_ne (card_image_polynomial_eval (by rw [hf2]; decide))
            (mt (congr_arg (· % 2)) (by simp [natDegree_eq_of_degree_eq_some hf2, hR])))
          (card_image_polynomial_eval (by rw [degree_neg, hg2]; decide)))
      _ = 2 * #((univ.image fun x : R => eval x f) union univ.image fun x : R => eval x (-g)) := by
        rw [card_union_of_disjoint hd]
        simp [natDegree_eq_of_degree_eq_some hf2, natDegree_eq_of_degree_eq_some hg2, mul_add]

end Polynomial

/--
theorem `prod_univ_units_id_eq_neg_one` / 定理 `prod_univ_units_id_eq_neg_one`

English:
theorem prod_univ_units_id_eq_neg_one
  given: [CommRing K] [IsDomain K] [Fintype Kˣ]
  proof: by
  classical
    have : (∏ x in (@univ Kˣ _).erase (-1), x) = 1 :=
      prod_involution (fun x _ => x⁻¹) (by simp)
        (fun a => by simp +contextual [Units.inv_eq_self_iff])
        (fun a => by simp [@inv_eq_iff_eq_inv _ _ a]) (by simp)
    rw [← insert_erase (mem_univ (-1 : Kˣ))]; rw [prod_

中文:
定理 prod_univ_units_id_eq_neg_one
  条件: [交换环 K] [是整环 K] [有限类型 Kˣ]
  证明: by
  classical
    have : (∏ x in (@univ Kˣ _).erase (-1), x) = 1 :=
      prod_involution (fun x _ => x⁻¹) (by simp)
        (fun a => by simp +contextual [Units.inv_eq_self_iff])
        (fun a => by simp [@inv_eq_iff_eq_inv _ _ a]) (by simp)
    rw [← insert_erase (mem_univ (-1 : Kˣ))]; rw [prod_

Depends on / 依赖: Units.inv_eq_self_iff, classical, contextual, insert_erase, inv_eq_iff_eq_inv, inv_eq_self_iff, mem_univ, mul_one, notMem_erase, prod_insert, prod_involution
-/
theorem prod_univ_units_id_eq_neg_one [CommRing K] [IsDomain K] [Fintype Kˣ] :
    ∏ x : Kˣ, x = (-1 : Kˣ) := by
  classical
    have : (∏ x in (@univ Kˣ _).erase (-1), x) = 1 :=
      prod_involution (fun x _ => x⁻¹) (by simp)
        (fun a => by simp +contextual [Units.inv_eq_self_iff])
        (fun a => by simp [@inv_eq_iff_eq_inv _ _ a]) (by simp)
    rw [← insert_erase (mem_univ (-1 : Kˣ))]; rw [prod_insert (notMem_erase _ _)]; rw [this]; rw [mul_one]

/--
theorem `card_cast_subgroup_card_ne_zero` / 定理 `card_cast_subgroup_card_ne_zero`

English:
theorem card_cast_subgroup_card_ne_zero
  statement: [Ring K] [NoZeroDivisors K] [Nontrivial K]
  proof: by
  let n := Fintype.card G
  intro nzero
  have ⟨p, char_p⟩ := CharP.exists K
  have hd : p ∣ n := (CharP.cast_eq_zero_iff K p n).mp nzero
  cases CharP.char_is_prime_or_zero K p with
  | inr pzero =>
exact (Fintype.card_pos).ne' Nat.eq_zero_of_zero_dvd pzero ▸ hd
  | inl pprime =>
    have fact_p

中文:
定理 card_cast_subgroup_card_ne_zero
  结论: [环 K] [无零因子 K] [非平凡 K]
  证明: by
  let n := Fintype.card G
  intro nzero
  have ⟨p, char_p⟩ := CharP.exists K
  have hd : p ∣ n := (CharP.cast_eq_zero_iff K p n).mp nzero
  cases CharP.char_is_prime_or_zero K p with
  | inr pzero =>
exact (Fintype.card_pos).ne' Nat.eq_zero_of_zero_dvd pzero ▸ hd
  | inl pprime =>
    have fact_p

Depends on / 依赖: CharP.cast_eq_zero_iff, CharP.char_is_prime_or_zero, CharP.exists, Fact.mk, Fintype, Fintype.card, Fintype.card_pos, Nat.eq_zero_of_zero_dvd, card_pos, cast_eq_zero_iff, char_is_prime_or_zero, char_p, eq_zero_of_zero_dvd, fact_pprime, pprime
-/
theorem card_cast_subgroup_card_ne_zero [Ring K] [NoZeroDivisors K] [Nontrivial K]
    (G : Subgroup Kˣ) [Fintype G] : (Fintype.card G : K) != 0 := by
  let n := Fintype.card G
  intro nzero
  have ⟨p, char_p⟩ := CharP.exists K
  have hd : p ∣ n := (CharP.cast_eq_zero_iff K p n).mp nzero
  cases CharP.char_is_prime_or_zero K p with
  | inr pzero =>
exact (Fintype.card_pos).ne' Nat.eq_zero_of_zero_dvd pzero ▸ hd
  | inl pprime =>
    have fact_pprime := Fact.mk pprime
    -- G has an element x of order p by Cauchy's theorem
    have ⟨x, hx⟩ := exists_prime_orderOf_dvd_card p hd
    -- F has an element u (= ↑↑x) of order p
    let u := ((x : Kˣ) : K)
    have hu : orderOf u = p := by rwa [orderOf_units, Subgroup.orderOf_coe]
    -- u ^ p = 1 implies (u - 1) ^ p = 0 and hence u = 1 ...
    have h : u = 1 := by
      rw [← sub_left_inj]; rw [sub_self 1]
      apply eq_zero_of_pow_eq_zero (n := p)
      rw [sub_pow_char_of_commute]; rw [one_pow]; rw [← hu]; rw [pow_orderOf_eq_one]; rw [sub_self]
      exact Commute.one_right u
    -- ... meaning x didn't have order p after all, contradiction
    apply pprime.one_lt.ne
    rw [← hu]; rw [h]; rw [orderOf_one]

/--
theorem `sum_subgroup_units_eq_zero` / 定理 `sum_subgroup_units_eq_zero`

English:
theorem sum_subgroup_units_eq_zero
  statement: [Ring K] [NoZeroDivisors K]
  proof: by
  rw [Subgroup.ne_bot_iff_exists_ne_one] at hg
  rcases hg with ⟨a, ha⟩
  -- The action of a on G as an embedding
  let a_mul_emb : G ↪ G := mulLeftEmbedding a
  -- ... and leaves G unchanged
  have h_unchanged : Finset.univ.map a_mul_emb = Finset.univ := by simp
  -- Therefore the sum of x over 

中文:
定理 sum_subgroup_units_eq_zero
  结论: [环 K] [无零因子 K]
  证明: by
  rw [Subgroup.ne_bot_iff_exists_ne_one] at hg
  rcases hg with ⟨a, ha⟩
  -- The action of a on G as an embedding
  let a_mul_emb : G ↪ G := mulLeftEmbedding a
  -- ... and leaves G unchanged
  have h_unchanged : Finset.univ.map a_mul_emb = Finset.univ := by simp
  -- Therefore the sum of x over 

Depends on / 依赖: Subgroup, Subgroup.ne_bot_iff_exists_ne_one, ne_bot_iff_exists_ne_one
-/
theorem sum_subgroup_units_eq_zero [Ring K] [NoZeroDivisors K]
    {G : Subgroup Kˣ} [Fintype G] (hg : G != ⊥) :
    ∑ x : G, (x.val : K) = 0 := by
  rw [Subgroup.ne_bot_iff_exists_ne_one] at hg
  rcases hg with ⟨a, ha⟩
  -- The action of a on G as an embedding
  let a_mul_emb : G ↪ G := mulLeftEmbedding a
  -- ... and leaves G unchanged
  have h_unchanged : Finset.univ.map a_mul_emb = Finset.univ := by simp
  -- Therefore the sum of x over a G is the sum of a x over G
  have h_sum_map := Finset.univ.sum_map a_mul_emb fun x => ((x : Kˣ) : K)
  -- ... and the former is the sum of x over G.
  -- By algebraic manipulation, we have Σ G, x = ∑ G, a x = a ∑ G, x
  simp only [h_unchanged, mulLeftEmbedding_apply, Subgroup.coe_mul, Units.val_mul, ← mul_sum,
    a_mul_emb] at h_sum_map
  -- thus one of (a - 1) or ∑ G, x is zero
  have hzero : (((a : Kˣ) : K) - 1) = 0 ∨ ∑ x : ↥G, ((x : Kˣ) : K) = 0 := by
    rw [← mul_eq_zero]; rw [sub_mul]; rw [← h_sum_map]; rw [one_mul]; rw [sub_self]
  apply Or.resolve_left hzero
  contrapose ha
  ext
  rwa [← sub_eq_zero]

/-- The sum of a subgroup of the units of a field is 1 if the subgroup is trivial and 1 otherwise -/
@[simp]
/--
theorem `sum_subgroup_units` / 定理 `sum_subgroup_units`

English:
theorem sum_subgroup_units
  statement: [Ring K] [NoZeroDivisors K]
  proof: by
  by_cases G_bot : G = ⊥
  · subst G_bot
    simp only [univ_unique, sum_singleton, ↓reduceIte, Units.val_eq_one, OneMemClass.coe_eq_one]
    rw [Set.default_coe_singleton]
    rfl
  · simp only [G_bot, ite_false]
    exact sum_subgroup_units_eq_zero G_bot

@[simp]

中文:
定理 sum_subgroup_units
  结论: [环 K] [无零因子 K]
  证明: by
  by_cases G_bot : G = ⊥
  · subst G_bot
    simp only [univ_unique, sum_singleton, ↓reduceIte, Units.val_eq_one, OneMemClass.coe_eq_one]
    rw [Set.default_coe_singleton]
    rfl
  · simp only [G_bot, ite_false]
    exact sum_subgroup_units_eq_zero G_bot

@[simp]

Depends on / 依赖: G_bot, OneMemClass, OneMemClass.coe_eq_one, Set.default_coe_singleton, Units.val_eq_one, coe_eq_one, default_coe_singleton, ite_false, reduceIte, sum_singleton, sum_subgroup_units_eq_zero, univ_unique, val_eq_one
-/
theorem sum_subgroup_units [Ring K] [NoZeroDivisors K]
    {G : Subgroup Kˣ} [Fintype G] [Decidable (G = ⊥)] :
    ∑ x : G, (x.val : K) = if G = ⊥ then 1 else 0 := by
  by_cases G_bot : G = ⊥
  · subst G_bot
    simp only [univ_unique, sum_singleton, ↓reduceIte, Units.val_eq_one, OneMemClass.coe_eq_one]
    rw [Set.default_coe_singleton]
    rfl
  · simp only [G_bot, ite_false]
    exact sum_subgroup_units_eq_zero G_bot

@[simp]
/--
theorem `sum_subgroup_pow_eq_zero` / 定理 `sum_subgroup_pow_eq_zero`

English:
theorem sum_subgroup_pow_eq_zero
  statement: [CommRing K] [NoZeroDivisors K]
  proof: by
  rw [← Nat.card_eq_fintype_card] at k_lt_card_G
  nontriviality K
  have := NoZeroDivisors.to_isDomain K
  rcases (exists_pow_ne_one_of_isCyclic k_pos k_lt_card_G) with ⟨a, ha⟩
  rw [Finset.sum_eq_multiset_sum]
  have h_multiset_map :
    Finset.univ.val.map (fun x : G => ((x : Kˣ) : K) ^ k) =
 

中文:
定理 sum_subgroup_pow_eq_zero
  结论: [交换环 K] [无零因子 K]
  证明: by
  rw [← Nat.card_eq_fintype_card] at k_lt_card_G
  nontriviality K
  have := NoZeroDivisors.to_isDomain K
  rcases (exists_pow_ne_one_of_isCyclic k_pos k_lt_card_G) with ⟨a, ha⟩
  rw [Finset.sum_eq_multiset_sum]
  have h_multiset_map :
    Finset.univ.val.map (fun x : G => ((x : Kˣ) : K) ^ k) =
 

Depends on / 依赖: Finset, Finset.sum_eq_multiset_sum, Finset.univ.val.map, Nat.card_eq_fintype_card, NoZeroDivisors, NoZeroDivisors.to_isDomain, as_comp, card_eq_fintype_card, exists_pow_ne_one_of_isCyclic, h_multiset_map, k_lt_card_G, k_pos, mul_pow, nontriviality, simp_rw, sum_eq_multiset_sum, to_isDomain
-/
theorem sum_subgroup_pow_eq_zero [CommRing K] [NoZeroDivisors K]
    {G : Subgroup Kˣ} [Fintype G] {k : Nat} (k_pos : k != 0) (k_lt_card_G : k < Fintype.card G) :
    ∑ x : G, ((x : Kˣ) : K) ^ k = 0 := by
  rw [← Nat.card_eq_fintype_card] at k_lt_card_G
  nontriviality K
  have := NoZeroDivisors.to_isDomain K
  rcases (exists_pow_ne_one_of_isCyclic k_pos k_lt_card_G) with ⟨a, ha⟩
  rw [Finset.sum_eq_multiset_sum]
  have h_multiset_map :
    Finset.univ.val.map (fun x : G => ((x : Kˣ) : K) ^ k) =
      Finset.univ.val.map (fun x : G => ((x : Kˣ) : K) ^ k * ((a : Kˣ) : K) ^ k) := by
    simp_rw [← mul_pow]
    have as_comp :
      (fun x : ↥G => (((x : Kˣ) : K) * ((a : Kˣ) : K)) ^ k)
        = (fun x : ↥G => ((x : Kˣ) : K) ^ k) ∘ fun x : ↥G => x * a := by
      funext x
      simp only [Function.comp_apply, Subgroup.coe_mul, Units.val_mul]
    rw [as_comp]; rw [← Multiset.map_map]
    congr
    rw [eq_comm]
    exact Multiset.map_univ_val_equiv (Equiv.mulRight a)
  have h_multiset_map_sum : (Multiset.map (fun x : G => ((x : Kˣ) : K) ^ k) Finset.univ.val).sum =
    (Multiset.map (fun x : G => ((x : Kˣ) : K) ^ k * ((a : Kˣ) : K) ^ k) Finset.univ.val).sum := by
    rw [h_multiset_map]
  rw [Multiset.sum_map_mul_right] at h_multiset_map_sum
  have hzero : (((a : Kˣ) : K) ^ k - 1 : K)
                  * (Multiset.map (fun i : G => (i.val : K) ^ k) Finset.univ.val).sum = 0 := by
    rw [sub_mul]; rw [mul_comm]; rw [← h_multiset_map_sum]; rw [one_mul]; rw [sub_self]
  rw [mul_eq_zero] at hzero
  refine hzero.resolve_left fun h => ha ?_
  ext
  rw [← sub_eq_zero]
  simp_rw [SubmonoidClass.coe_pow, Units.val_pow_eq_pow_val, OneMemClass.coe_one, Units.val_one, h]

section

variable [GroupWithZero K] [Fintype K]

/--
theorem `pow_card_sub_one_eq_one` / 定理 `pow_card_sub_one_eq_one`

English:
theorem pow_card_sub_one_eq_one
  given: (a : K) (ha : a != 0)
  statement: a ^ (q - 1) = 1
  proof: by
  calc
    a ^ (Fintype.card K - 1) = (Units.mk0 a ha ^ (Fintype.card K - 1) : Kˣ).1 := by
      rw [Units.val_pow_eq_pow_val]; rw [Units.val_mk0]
    _ = 1 := by
      classical
        rw [← Fintype.card_units]; rw [pow_card_eq_one]
        rfl

中文:
定理 pow_card_sub_one_eq_one
  条件: (a : K) (ha : a != 0)
  结论: a ^ (q - 1) = 1
  证明: by
  calc
    a ^ (Fintype.card K - 1) = (Units.mk0 a ha ^ (Fintype.card K - 1) : Kˣ).1 := by
      rw [Units.val_pow_eq_pow_val]; rw [Units.val_mk0]
    _ = 1 := by
      classical
        rw [← Fintype.card_units]; rw [pow_card_eq_one]
        rfl

Depends on / 依赖: Fintype, Fintype.card, Fintype.card_units, Units.mk0, Units.val_mk0, Units.val_pow_eq_pow_val, card_units, classical, pow_card_eq_one, val_mk0, val_pow_eq_pow_val
-/
theorem pow_card_sub_one_eq_one (a : K) (ha : a != 0) : a ^ (q - 1) = 1 := by
  calc
    a ^ (Fintype.card K - 1) = (Units.mk0 a ha ^ (Fintype.card K - 1) : Kˣ).1 := by
      rw [Units.val_pow_eq_pow_val]; rw [Units.val_mk0]
    _ = 1 := by
      classical
        rw [← Fintype.card_units]; rw [pow_card_eq_one]
        rfl

/--
theorem `pow_card` / 定理 `pow_card`

English:
theorem pow_card
  given: (a : K)
  statement: a ^ q = a
  proof: by
  by_cases h : a = 0; · rw [h]; apply zero_pow Fintype.card_ne_zero
  rw [← Nat.succ_pred_eq_of_pos Fintype.card_pos]; rw [pow_succ]; rw [Nat.pred_eq_sub_one]; rw [pow_card_sub_one_eq_one a h]; rw [one_mul]

中文:
定理 pow_card
  条件: (a : K)
  结论: a ^ q = a
  证明: by
  by_cases h : a = 0; · rw [h]; apply zero_pow Fintype.card_ne_zero
  rw [← Nat.succ_pred_eq_of_pos Fintype.card_pos]; rw [pow_succ]; rw [Nat.pred_eq_sub_one]; rw [pow_card_sub_one_eq_one a h]; rw [one_mul]

Depends on / 依赖: Fintype, Fintype.card_ne_zero, Fintype.card_pos, Nat.pred_eq_sub_one, Nat.succ_pred_eq_of_pos, card_ne_zero, card_pos, one_mul, pow_card_sub_one_eq_one, pow_succ, pred_eq_sub_one, succ_pred_eq_of_pos, zero_pow
-/
theorem pow_card (a : K) : a ^ q = a := by
  by_cases h : a = 0; · rw [h]; apply zero_pow Fintype.card_ne_zero
  rw [← Nat.succ_pred_eq_of_pos Fintype.card_pos]; rw [pow_succ]; rw [Nat.pred_eq_sub_one]; rw [pow_card_sub_one_eq_one a h]; rw [one_mul]

/--
theorem `pow_card_pow` / 定理 `pow_card_pow`

English:
theorem pow_card_pow
  given: (n : Nat) (a : K)
  statement: a ^ q ^ n = a
  proof: by
  induction n with
  | zero => simp
  | succ n ih => simp [pow_succ, pow_mul, ih, pow_card]

中文:
定理 pow_card_pow
  条件: (n : 自然数) (a : K)
  结论: a ^ q ^ n = a
  证明: by
  induction n with
  | zero => simp
  | succ n ih => simp [pow_succ, pow_mul, ih, pow_card]

Depends on / 依赖: pow_card, pow_mul, pow_succ
-/
theorem pow_card_pow (n : Nat) (a : K) : a ^ q ^ n = a := by
  induction n with
  | zero => simp
  | succ n ih => simp [pow_succ, pow_mul, ih, pow_card]

end

section

variable [Field K] [Fintype K]

open Lean in
/--
Instance `instGrindPowIdentity` / 实例 `instGrindPowIdentity`

English:
instance instGrindPowIdentity
  signature: : Grind.PowIdentity K (Fintype.card K) where
  body: pow_card

中文:
实例 instGrindPowIdentity
  签名: : Grind.PowIdentity K (有限类型.card K) where
  定义体: pow_card

Depends on / 依赖: pow_card
-/
instance instGrindPowIdentity : Grind.PowIdentity K (Fintype.card K) where
  pow_eq := pow_card

end

variable (K) [Field K] [Fintype K]

/-- The cardinality `q` is a power of the characteristic of `K`. -/
@[stacks 09HY "first part"]
/--
theorem `card` / 定理 `card`

English:
theorem card
  given: (p : Nat) [CharP K p]
  statement: exists n : Nat+, Nat.Prime p ∧ q = p ^ (n : Nat)
  proof: by
  have hp : Fact p.Prime := ⟨CharP.char_is_prime K p⟩
  let : Module (ZMod p) K := { (ZMod.castHom dvd_rfl K : ZMod p ->+* _).toModule with }
  obtain ⟨n, h⟩ := VectorSpace.card_fintype (ZMod p) K
  rw [ZMod.card] at h
  refine ⟨⟨n, ?_⟩, hp.1, h⟩
  apply Or.resolve_left (Nat.eq_zero_or_pos n)
  r

中文:
定理 card
  条件: (p : 自然数) [特征p K p]
  结论: 存在 n : 自然数+, 自然数.素 p ∧ q = p ^ (n : 自然数)
  证明: by
  have hp : Fact p.Prime := ⟨CharP.char_is_prime K p⟩
  let : Module (ZMod p) K := { (ZMod.castHom dvd_rfl K : ZMod p ->+* _).toModule with }
  obtain ⟨n, h⟩ := VectorSpace.card_fintype (ZMod p) K
  rw [ZMod.card] at h
  refine ⟨⟨n, ?_⟩, hp.1, h⟩
  apply Or.resolve_left (Nat.eq_zero_or_pos n)
  r

Depends on / 依赖: CharP.char_is_prime, Fintype, Fintype.card_le_one_iff.mp, Module, Nat.eq_zero_or_pos, Or.resolve_left, VectorSpace, VectorSpace.card_fintype, ZMod.card, ZMod.castHom, absurd, card_fintype, card_le_one_iff, castHom, char_is_prime, dvd_rfl, eq_zero_or_pos, le_of_eq, p.Prime, pow_zero
-/
theorem card (p : Nat) [CharP K p] : exists n : Nat+, Nat.Prime p ∧ q = p ^ (n : Nat) := by
  have hp : Fact p.Prime := ⟨CharP.char_is_prime K p⟩
  let : Module (ZMod p) K := { (ZMod.castHom dvd_rfl K : ZMod p ->+* _).toModule with }
  obtain ⟨n, h⟩ := VectorSpace.card_fintype (ZMod p) K
  rw [ZMod.card] at h
  refine ⟨⟨n, ?_⟩, hp.1, h⟩
  apply Or.resolve_left (Nat.eq_zero_or_pos n)
  rintro rfl
  rw [pow_zero] at h
  have : (0 : K) = 1 := by apply Fintype.card_le_one_iff.mp (le_of_eq h)
  exact absurd this zero_ne_one

-- this statement doesn't use `q` because we want `K` to be an explicit parameter
/--
theorem `card'` / 定理 `card'`

English:
theorem card'
  statement: exists (p : Nat), CharP K p ∧ exists (n : Nat+), Nat.Prime p ∧ Fintype.card K = p ^ (n : Nat)
  proof: let ⟨p, hc⟩ := CharP.exists K
  ⟨p, hc, @FiniteField.card K _ _ p hc⟩

中文:
定理 card'
  结论: 存在 (p : 自然数), 特征p K p ∧ 存在 (n : 自然数+), 自然数.素 p ∧ 有限类型.card K = p ^ (n : 自然数)
  证明: let ⟨p, hc⟩ := CharP.exists K
  ⟨p, hc, @FiniteField.card K _ _ p hc⟩

Depends on / 依赖: CharP.exists, FiniteField, FiniteField.card
-/
theorem card' : exists (p : Nat), CharP K p ∧ exists (n : Nat+), Nat.Prime p ∧ Fintype.card K = p ^ (n : Nat) :=
  let ⟨p, hc⟩ := CharP.exists K
  ⟨p, hc, @FiniteField.card K _ _ p hc⟩

/--
lemma `isPrimePow_card` / 引理 `isPrimePow_card`

English:
lemma isPrimePow_card
  statement: IsPrimePow (Fintype.card K)
  proof: by
  obtain ⟨p, _, n, hp, hn⟩ := card' K
  exact ⟨p, n, Nat.prime_iff.mp hp, n.prop, hn.symm⟩

中文:
引理 isPrimePow_card
  结论: IsPrimePow (有限类型.card K)
  证明: by
  obtain ⟨p, _, n, hp, hn⟩ := card' K
  exact ⟨p, n, Nat.prime_iff.mp hp, n.prop, hn.symm⟩

Depends on / 依赖: Nat.prime_iff.mp, hn.symm, n.prop, prime_iff
-/
lemma isPrimePow_card : IsPrimePow (Fintype.card K) := by
  obtain ⟨p, _, n, hp, hn⟩ := card' K
  exact ⟨p, n, Nat.prime_iff.mp hp, n.prop, hn.symm⟩

/--
theorem `cast_card_eq_zero` / 定理 `cast_card_eq_zero`

English:
theorem cast_card_eq_zero
  statement: (q : K) = 0
  proof: by
  simp

中文:
定理 cast_card_eq_zero
  结论: (q : K) = 0
  证明: by
  simp
-/
theorem cast_card_eq_zero : (q : K) = 0 := by
  simp

/--
theorem `forall_pow_eq_one_iff` / 定理 `forall_pow_eq_one_iff`

English:
theorem forall_pow_eq_one_iff
  given: (i : Nat)
  statement: (forall x : Kˣ, x ^ i = 1) ↔ q - 1 ∣ i
  proof: by
  obtain ⟨x, hx⟩ := IsCyclic.exists_generator (α := Kˣ)
  rw [← Nat.card_eq_fintype_card]; rw [← Nat.card_units]; rw [← orderOf_eq_card_of_forall_mem_zpowers hx]; rw [orderOf_dvd_iff_pow_eq_one]
  constructor
  · intro h; apply h
  · intro h y
    simp_rw [← mem_powers_iff_mem_zpowers] at hx
    

中文:
定理 对任意_pow_eq_one_iff
  条件: (i : 自然数)
  结论: (对任意 x : Kˣ, x ^ i = 1) ↔ q - 1 ∣ i
  证明: by
  obtain ⟨x, hx⟩ := IsCyclic.exists_generator (α := Kˣ)
  rw [← Nat.card_eq_fintype_card]; rw [← Nat.card_units]; rw [← orderOf_eq_card_of_forall_mem_zpowers hx]; rw [orderOf_dvd_iff_pow_eq_one]
  constructor
  · intro h; apply h
  · intro h y
    simp_rw [← mem_powers_iff_mem_zpowers] at hx
    

Depends on / 依赖: IsCyclic, IsCyclic.exists_generator, Nat.card_eq_fintype_card, Nat.card_units, card_eq_fintype_card, card_units, exists_generator, mem_powers_iff_mem_zpowers, mul_comm, one_pow, orderOf_dvd_iff_pow_eq_one, orderOf_eq_card_of_forall_mem_zpowers, pow_mul, simp_rw
-/
theorem forall_pow_eq_one_iff (i : Nat) : (forall x : Kˣ, x ^ i = 1) ↔ q - 1 ∣ i := by
  obtain ⟨x, hx⟩ := IsCyclic.exists_generator (α := Kˣ)
  rw [← Nat.card_eq_fintype_card]; rw [← Nat.card_units]; rw [← orderOf_eq_card_of_forall_mem_zpowers hx]; rw [orderOf_dvd_iff_pow_eq_one]
  constructor
  · intro h; apply h
  · intro h y
    simp_rw [← mem_powers_iff_mem_zpowers] at hx
    rcases hx y with ⟨j, rfl⟩
    rw [← pow_mul]; rw [mul_comm]; rw [pow_mul]; rw [h]; rw [one_pow]

/--
theorem `sum_pow_units` / 定理 `sum_pow_units`

English:
theorem sum_pow_units
  given: [DecidableEq K] (i : Nat)
  proof: by
  let φ : Kˣ ->* K :=
    { toFun := fun x => x ^ i
      map_one' := by simp
      map_mul' := by simp [mul_pow] }
  have : Decidable (φ = 1) := by classical infer_instance
  calc (∑ x : Kˣ, φ x) = if φ = 1 then Fintype.card Kˣ else 0 := sum_hom_units φ
      _ = if q - 1 ∣ i then -1 else 0 := b

中文:
定理 sum_pow_units
  条件: [DecidableEq K] (i : 自然数)
  证明: by
  let φ : Kˣ ->* K :=
    { toFun := fun x => x ^ i
      map_one' := by simp
      map_mul' := by simp [mul_pow] }
  have : Decidable (φ = 1) := by classical infer_instance
  calc (∑ x : Kˣ, φ x) = if φ = 1 then Fintype.card Kˣ else 0 := sum_hom_units φ
      _ = if q - 1 ∣ i then -1 else 0 := b

Depends on / 依赖: Decidable, Fintype, Fintype.card, Fintype.card_pos_iff.mpr, Fintype.card_units, Nat.cast_one, Nat.cast_sub, Nat.cast_zero, card_pos_iff, card_units, cast_card_eq_zero, cast_one, cast_sub, cast_zero, classical, infer_instance, map_mul, map_one, mul_pow, split_ifs
-/
theorem sum_pow_units [DecidableEq K] (i : Nat) :
    (∑ x : Kˣ, (x ^ i : K)) = if q - 1 ∣ i then -1 else 0 := by
  let φ : Kˣ ->* K :=
    { toFun := fun x => x ^ i
      map_one' := by simp
      map_mul' := by simp [mul_pow] }
  have : Decidable (φ = 1) := by classical infer_instance
  calc (∑ x : Kˣ, φ x) = if φ = 1 then Fintype.card Kˣ else 0 := sum_hom_units φ
      _ = if q - 1 ∣ i then -1 else 0 := by
        suffices q - 1 ∣ i ↔ φ = 1 by
          simp only [this]
          split_ifs; swap
          · exact Nat.cast_zero
          · rw [Fintype.card_units, Nat.cast_sub,
              cast_card_eq_zero, Nat.cast_one, zero_sub]
            show 1 <= q; exact Fintype.card_pos_iff.mpr ⟨0⟩
        rw [← forall_pow_eq_one_iff]; rw [DFunLike.ext_iff]
        apply forall_congr'; intro x; simp [φ, Units.ext_iff]

/--
theorem `sum_pow_lt_card_sub_one` / 定理 `sum_pow_lt_card_sub_one`

English:
theorem sum_pow_lt_card_sub_one
  given: (i : Nat) (h : i < q - 1)
  statement: ∑ x : K, x ^ i = 0
  proof: by
  by_cases hi : i = 0
  · simp only [hi, nsmul_one, sum_const, pow_zero, card_univ, cast_card_eq_zero]
  classical
    have hiq : ¬q - 1 ∣ i := by contrapose! h; exact Nat.le_of_dvd (Nat.pos_of_ne_zero hi) h
    let φ : Kˣ ↪ K := ⟨fun x => x, Units.val_injective⟩
    have : univ.map φ = univ \ {0

中文:
定理 sum_pow_lt_card_sub_one
  条件: (i : 自然数) (h : i < q - 1)
  结论: ∑ x : K, x ^ i = 0
  证明: by
  by_cases hi : i = 0
  · simp only [hi, nsmul_one, sum_const, pow_zero, card_univ, cast_card_eq_zero]
  classical
    have hiq : ¬q - 1 ∣ i := by contrapose! h; exact Nat.le_of_dvd (Nat.pos_of_ne_zero hi) h
    let φ : Kˣ ↪ K := ⟨fun x => x, Units.val_injective⟩
    have : univ.map φ = univ \ {0

Depends on / 依赖: Embedding, Function, Function.Embedding.coeFn_mk, Nat.le_of_dvd, Nat.pos_of_ne_zero, Units.val_injective, card_univ, cast_card_eq_zero, classical, coeFn_mk, contrapose, isUnit_iff_ne_zero, le_of_dvd, mem_map, mem_sdiff, mem_singleton, mem_univ, nsmul_one, pos_of_ne_zero, pow_zero
-/
theorem sum_pow_lt_card_sub_one (i : Nat) (h : i < q - 1) : ∑ x : K, x ^ i = 0 := by
  by_cases hi : i = 0
  · simp only [hi, nsmul_one, sum_const, pow_zero, card_univ, cast_card_eq_zero]
  classical
    have hiq : ¬q - 1 ∣ i := by contrapose! h; exact Nat.le_of_dvd (Nat.pos_of_ne_zero hi) h
    let φ : Kˣ ↪ K := ⟨fun x => x, Units.val_injective⟩
    have : univ.map φ = univ \ {0} := by
      ext x
      simpa only [mem_map, mem_univ, Function.Embedding.coeFn_mk, true_and, mem_sdiff,
        mem_singleton, φ] using! isUnit_iff_ne_zero
    calc
      ∑ x : K, x ^ i = ∑ x in univ \ {(0 : K)}, x ^ i := by
        rw [← sum_sdiff ({0} : Finset K).subset_univ]; rw [sum_singleton]; rw [zero_pow hi]; rw [add_zero]
      _ = ∑ x : Kˣ, (x ^ i : K) := by simp [φ, ← this, univ.sum_map φ]
      _ = 0 := by rw [sum_pow_units K i, if_neg]; exact hiq

section frobenius

variable (R) [CommRing R] [Algebra K R]

/--
Definition of `frobeniusAlgHom` / `frobeniusAlgHom` 的定义

English:
definition frobeniusAlgHom
  signature: : R ->ₐ[K] R where
  body: powMonoidHom q
  map_zero' := zero_pow Fintype.card_pos.ne'
  map_add' _ _ := by
    obtain ⟨p, _, _, hp, card_eq⟩ := card' K
    nontriviality R
    have : CharP R p := charP_of_injective_algebraMap' K p
    have : ExpChar R p := .prime hp
    simp only [OneHom.toFun_eq_coe, MonoidHom.toOneHom_coe,

中文:
定义 frobeniusAlgHom
  签名: : R ->ₐ[K] R where
  定义体: powMonoidHom q
  map_zero' := zero_pow Fintype.card_pos.ne'
  map_add' _ _ := by
    obtain ⟨p, _, _, hp, card_eq⟩ := card' K
    nontriviality R
    have : CharP R p := charP_of_injective_algebraMap' K p
    have : ExpChar R p := .prime hp
    simp only [OneHom.toFun_eq_coe, MonoidHom.toOneHom_coe,
-/
@[simps!] def frobeniusAlgHom : R ->ₐ[K] R where
  __ := powMonoidHom q
  map_zero' := zero_pow Fintype.card_pos.ne'
  map_add' _ _ := by
    obtain ⟨p, _, _, hp, card_eq⟩ := card' K
    nontriviality R
    have : CharP R p := charP_of_injective_algebraMap' K p
    have : ExpChar R p := .prime hp
    simp only [OneHom.toFun_eq_coe, MonoidHom.toOneHom_coe, powMonoidHom_apply, card_eq]
    exact add_pow_expChar_pow ..
  commutes' _ := by simp [← map_pow, pow_card]

/--
theorem `coe_frobeniusAlgHom` / 定理 `coe_frobeniusAlgHom`

English:
theorem coe_frobeniusAlgHom
  statement: ⇑(frobeniusAlgHom K R) = (· ^ q)
  proof: rfl

中文:
定理 coe_frobeniusAlgHom
  结论: ⇑(frobeniusAlgHom K R) = (· ^ q)
  证明: rfl
-/
theorem coe_frobeniusAlgHom : ⇑(frobeniusAlgHom K R) = (· ^ q) := rfl

/--
Definition of `frobeniusAlgEquiv` / `frobeniusAlgEquiv` 的定义

English:
definition frobeniusAlgEquiv
  signature: (p : Nat) [ExpChar R p] [PerfectRing R p]
  body: .ofBijective (frobeniusAlgHom K R) by
    obtain ⟨p', _, n, hp, card_eq⟩ := card' K
    rw [coe_frobeniusAlgHom]; rw [card_eq]
    have : ExpChar K p' := ExpChar.prime hp
    nontriviality R
    have := ExpChar.eq ‹_› (expChar_of_injective_algebraMap (algebraMap K R).injective p')
    subst this
   

中文:
定义 frobeniusAlgEquiv
  签名: (p : 自然数) [ExpChar R p] [完美环 R p]
  定义体: .ofBijective (frobeniusAlgHom K R) by
    obtain ⟨p', _, n, hp, card_eq⟩ := card' K
    rw [coe_frobeniusAlgHom]; rw [card_eq]
    have : ExpChar K p' := ExpChar.prime hp
    nontriviality R
    have := ExpChar.eq ‹_› (expChar_of_injective_algebraMap (algebraMap K R).injective p')
    subst this
   
-/
@[simps!] noncomputable def frobeniusAlgEquiv (p : Nat) [ExpChar R p] [PerfectRing R p] : R ≃ₐ[K] R :=
.ofBijective (frobeniusAlgHom K R) by
    obtain ⟨p', _, n, hp, card_eq⟩ := card' K
    rw [coe_frobeniusAlgHom]; rw [card_eq]
    have : ExpChar K p' := ExpChar.prime hp
    nontriviality R
    have := ExpChar.eq ‹_› (expChar_of_injective_algebraMap (algebraMap K R).injective p')
    subst this
    apply bijective_iterateFrobenius

variable (L : Type*) [Field L] [Algebra K L]

/--
Definition of `frobeniusAlgEquivOfAlgebraic` / `frobeniusAlgEquivOfAlgebraic` 的定义

English:
definition frobeniusAlgEquivOfAlgebraic
  signature: [Algebra.IsAlgebraic K L]
  body: (Algebra.IsAlgebraic.algEquivEquivAlgHom K L).symm (frobeniusAlgHom K L)

中文:
定义 frobeniusAlgEquivOfAlgebraic
  签名: [代数.是代数 K L]
  定义体: (Algebra.IsAlgebraic.algEquivEquivAlgHom K L).symm (frobeniusAlgHom K L)
-/
@[simps!] noncomputable def frobeniusAlgEquivOfAlgebraic [Algebra.IsAlgebraic K L] : Gal(L/K) :=
  (Algebra.IsAlgebraic.algEquivEquivAlgHom K L).symm (frobeniusAlgHom K L)

/--
theorem `coe_frobeniusAlgEquivOfAlgebraic` / 定理 `coe_frobeniusAlgEquivOfAlgebraic`

English:
theorem coe_frobeniusAlgEquivOfAlgebraic
  given: [Algebra.IsAlgebraic K L]
  proof: rfl

中文:
定理 coe_frobeniusAlgEquivOfAlgebraic
  条件: [代数.是代数 K L]
  证明: rfl
-/
theorem coe_frobeniusAlgEquivOfAlgebraic [Algebra.IsAlgebraic K L] :
    ⇑(frobeniusAlgEquivOfAlgebraic K L) = (· ^ q) := rfl

/--
lemma `coe_frobeniusAlgEquivOfAlgebraic_iterate` / 引理 `coe_frobeniusAlgEquivOfAlgebraic_iterate`

English:
lemma coe_frobeniusAlgEquivOfAlgebraic_iterate
  given: [Algebra.IsAlgebraic K L] (n : Nat)
  proof: pow_iterate (Fintype.card K) n

中文:
引理 coe_frobeniusAlgEquivOfAlgebraic_iterate
  条件: [代数.是代数 K L] (n : 自然数)
  证明: pow_iterate (Fintype.card K) n

Depends on / 依赖: Fintype, Fintype.card, pow_iterate
-/
lemma coe_frobeniusAlgEquivOfAlgebraic_iterate [Algebra.IsAlgebraic K L] (n : Nat) :
    (⇑(frobeniusAlgEquivOfAlgebraic K L))^[n] = (· ^ (Fintype.card K ^ n)) :=
  pow_iterate (Fintype.card K) n

variable [Finite L]

open Polynomial in
/--
theorem `orderOf_frobeniusAlgHom` / 定理 `orderOf_frobeniusAlgHom`

English:
theorem orderOf_frobeniusAlgHom
  statement: orderOf (frobeniusAlgHom K L) = Module.finrank K L
  proof: (orderOf_eq_iff Module.finrank_pos).mpr by
    have := Fintype.ofFinite L
    refine ⟨DFunLike.ext _ _ fun x => ?_, fun m lt pos eq => ?_⟩
    · simp_rw [AlgHom.coe_pow, coe_frobeniusAlgHom, pow_iterate, AlgHom.one_apply,
        ← Module.card_eq_pow_finrank, pow_card]
    have := card_le_degree_of_

中文:
定理 orderOf_frobeniusAlgHom
  结论: orderOf (frobeniusAlgHom K L) = 模.finrank K L
  证明: (orderOf_eq_iff Module.finrank_pos).mpr by
    have := Fintype.ofFinite L
    refine ⟨DFunLike.ext _ _ fun x => ?_, fun m lt pos eq => ?_⟩
    · simp_rw [AlgHom.coe_pow, coe_frobeniusAlgHom, pow_iterate, AlgHom.one_apply,
        ← Module.card_eq_pow_finrank, pow_card]
    have := card_le_degree_of_

Depends on / 依赖: AlgHom, AlgHom.coe_pow, AlgHom.one_apply, DFunLike, DFunLike.congr_fun, DFunLike.ext, Fintype, Fintype.ofFinite, IsRoot, Module, Module.card_eq_pow_finrank, Module.finrank_pos, card_eq_pow_finrank, card_le_degree_of_subset_roots, coe_frobeniusAlgHom, coe_pow, congr_fun, eval_X, eval_pow, eval_sub
-/
theorem orderOf_frobeniusAlgHom : orderOf (frobeniusAlgHom K L) = Module.finrank K L :=
(orderOf_eq_iff Module.finrank_pos).mpr by
    have := Fintype.ofFinite L
    refine ⟨DFunLike.ext _ _ fun x => ?_, fun m lt pos eq => ?_⟩
    · simp_rw [AlgHom.coe_pow, coe_frobeniusAlgHom, pow_iterate, AlgHom.one_apply,
        ← Module.card_eq_pow_finrank, pow_card]
    have := card_le_degree_of_subset_roots (R := L) (p := X ^ q ^ m - X) (Z := univ) fun x _ => by
      simp_rw [mem_roots', IsRoot, eval_sub, eval_pow, eval_X]
      have := DFunLike.congr_fun eq x
      rw [AlgHom.coe_pow]; rw [coe_frobeniusAlgHom]; rw [pow_iterate]; rw [AlgHom.one_apply]; rw [← sub_eq_zero] at this
      refine ⟨fun h => ?_, this⟩
      simpa [Fintype.one_lt_card.ne, pos.ne, eqComm] using congr_arg (coeff · 1) h
    refine this.not_gt (((natDegree_sub_le ..).trans_eq ?_).trans_lt <|
      (Nat.pow_lt_pow_right Fintype.one_lt_card lt).trans_eq Module.card_eq_pow_finrank.symm)
    simp [Nat.one_le_pow _ _ Fintype.card_pos]

/--
theorem `orderOf_frobeniusAlgEquivOfAlgebraic` / 定理 `orderOf_frobeniusAlgEquivOfAlgebraic`

English:
theorem orderOf_frobeniusAlgEquivOfAlgebraic
  proof: by
  simpa [orderOf_eq_iff Module.finrank_pos, DFunLike.ext_iff] using! orderOf_frobeniusAlgHom K L

中文:
定理 orderOf_frobeniusAlgEquivOfAlgebraic
  证明: by
  simpa [orderOf_eq_iff Module.finrank_pos, DFunLike.ext_iff] using! orderOf_frobeniusAlgHom K L

Depends on / 依赖: DFunLike, DFunLike.ext_iff, Module, Module.finrank_pos, ext_iff, finrank_pos, orderOf_eq_iff, orderOf_frobeniusAlgHom
-/
theorem orderOf_frobeniusAlgEquivOfAlgebraic :
    orderOf (frobeniusAlgEquivOfAlgebraic K L) = Module.finrank K L := by
  simpa [orderOf_eq_iff Module.finrank_pos, DFunLike.ext_iff] using! orderOf_frobeniusAlgHom K L

/--
theorem `bijective_frobeniusAlgHom_pow` / 定理 `bijective_frobeniusAlgHom_pow`

English:
theorem bijective_frobeniusAlgHom_pow
  proof: let e := (finCongr <| orderOf_frobeniusAlgHom K L).symm.trans
    finEquivPowers (orderOf_pos_iff.mp <| orderOf_frobeniusAlgHom K L ▸ Module.finrank_pos)
  (Subtype.val_injective.comp e.injective).bijective_of_nat_card_le
    ((card_algHom_le_finrank K L L).trans_eq <| by simp)

中文:
定理 bijective_frobeniusAlgHom_pow
  证明: let e := (finCongr <| orderOf_frobeniusAlgHom K L).symm.trans
    finEquivPowers (orderOf_pos_iff.mp <| orderOf_frobeniusAlgHom K L ▸ Module.finrank_pos)
  (Subtype.val_injective.comp e.injective).bijective_of_nat_card_le
    ((card_algHom_le_finrank K L L).trans_eq <| by simp)

Depends on / 依赖: Module, Module.finrank_pos, Subtype, Subtype.val_injective.comp, bijective_of_nat_card_le, card_algHom_le_finrank, e.injective, finCongr, finEquivPowers, finrank_pos, injective, orderOf_frobeniusAlgHom, orderOf_pos_iff, orderOf_pos_iff.mp, symm.trans, trans_eq, val_injective
-/
theorem bijective_frobeniusAlgHom_pow :
    Function.Bijective fun n : Fin (Module.finrank K L) => frobeniusAlgHom K L ^ n.1 :=
let e := (finCongr <| orderOf_frobeniusAlgHom K L).symm.trans
    finEquivPowers (orderOf_pos_iff.mp <| orderOf_frobeniusAlgHom K L ▸ Module.finrank_pos)
  (Subtype.val_injective.comp e.injective).bijective_of_nat_card_le
    ((card_algHom_le_finrank K L L).trans_eq <| by simp)

/--
theorem `bijective_frobeniusAlgEquivOfAlgebraic_pow` / 定理 `bijective_frobeniusAlgEquivOfAlgebraic_pow`

English:
theorem bijective_frobeniusAlgEquivOfAlgebraic_pow
  proof: ((Algebra.IsAlgebraic.algEquivEquivAlgHom K L).bijective.of_comp_iff' _).mp by
    simpa only [Function.comp_def, map_pow] using! bijective_frobeniusAlgHom_pow K L

中文:
定理 bijective_frobeniusAlgEquivOfAlgebraic_pow
  证明: ((Algebra.IsAlgebraic.algEquivEquivAlgHom K L).bijective.of_comp_iff' _).mp by
    simpa only [Function.comp_def, map_pow] using! bijective_frobeniusAlgHom_pow K L

Depends on / 依赖: Algebra, Algebra.IsAlgebraic.algEquivEquivAlgHom, Function, Function.comp_def, IsAlgebraic, algEquivEquivAlgHom, bijective, bijective.of_comp_iff, bijective_frobeniusAlgHom_pow, comp_def, map_pow, of_comp_iff
-/
theorem bijective_frobeniusAlgEquivOfAlgebraic_pow :
    Function.Bijective fun n : Fin (Module.finrank K L) => frobeniusAlgEquivOfAlgebraic K L ^ n.1 :=
((Algebra.IsAlgebraic.algEquivEquivAlgHom K L).bijective.of_comp_iff' _).mp by
    simpa only [Function.comp_def, map_pow] using! bijective_frobeniusAlgHom_pow K L

instance (K L) [Finite L] [Field K] [Field L] [Algebra K L] : IsCyclic Gal(L/K) where
  exists_zpow_surjective :=
    have := Finite.of_injective _ (algebraMap K L).injective
    have := Fintype.ofFinite K
    ⟨frobeniusAlgEquivOfAlgebraic K L,
      fun f => have ⟨n, hn⟩ := (bijective_frobeniusAlgEquivOfAlgebraic_pow K L).2 f; ⟨n, hn⟩⟩

open Polynomial in
/--
theorem `minpoly_frobeniusAlgHom` / 定理 `minpoly_frobeniusAlgHom`

English:
theorem minpoly_frobeniusAlgHom
  proof: minpoly.eq_of_linearIndependent _ _ (leadingCoeff_X_pow_sub_one Module.finrank_pos)
    (LinearMap.ext fun x => by
      simpa [sub_eq_zero, Module.End.coe_pow, orderOf_frobeniusAlgHom] using!
        congr($(pow_orderOf_eq_one (frobeniusAlgHom K L)) x)) _
(degree_X_pow_sub_C Module.finrank_pos _) b

中文:
定理 minpoly_frobeniusAlgHom
  证明: minpoly.eq_of_linearIndependent _ _ (leadingCoeff_X_pow_sub_one Module.finrank_pos)
    (LinearMap.ext fun x => by
      simpa [sub_eq_zero, Module.End.coe_pow, orderOf_frobeniusAlgHom] using!
        congr($(pow_orderOf_eq_one (frobeniusAlgHom K L)) x)) _
(degree_X_pow_sub_C Module.finrank_pos _) b

Depends on / 依赖: AlgHom, AlgHom.toEnd_apply, LinearMap, LinearMap.ext, Module, Module.End.coe_pow, Module.finrank_pos, bijective_frobeniusAlgHom_pow, coe_pow, degree_X_pow_sub_C, eq_of_linearIndependent, finrank_pos, frobeniusAlgHom, leadingCoeff_X_pow_sub_one, linearIndependent_algHom_toLinearMap, map_pow, minpoly, minpoly.eq_of_linearIndependent, orderOf_frobeniusAlgHom, pow_orderOf_eq_one
-/
theorem minpoly_frobeniusAlgHom :
    minpoly K (frobeniusAlgHom K L).toLinearMap = X ^ Module.finrank K L - 1 :=
  minpoly.eq_of_linearIndependent _ _ (leadingCoeff_X_pow_sub_one Module.finrank_pos)
    (LinearMap.ext fun x => by
      simpa [sub_eq_zero, Module.End.coe_pow, orderOf_frobeniusAlgHom] using!
        congr($(pow_orderOf_eq_one (frobeniusAlgHom K L)) x)) _
(degree_X_pow_sub_C Module.finrank_pos _) by
      simpa [← AlgHom.toEnd_apply, ← map_pow] using! (linearIndependent_algHom_toLinearMap K L L
.restrict_scalars' K).comp _ (bijective_frobeniusAlgHom_pow K L).1

end frobenius

open Polynomial

section

variable [Fintype K] (K' : Type*) [Field K'] {p n : Nat}

/--
theorem `X_pow_card_sub_X_natDegree_eq` / 定理 `X_pow_card_sub_X_natDegree_eq`

English:
theorem X_pow_card_sub_X_natDegree_eq
  given: (hp : 1 < p)
  statement: (X ^ p - X : K'[X]).natDegree = p
  proof: by
  have h1 : (X : K'[X]).degree < (X ^ p : K'[X]).degree := by
    rw [degree_X_pow]; rw [degree_X]
    exact mod_cast hp
  rw [natDegree_eq_of_degree_eq (degree_sub_eq_left_of_degree_lt h1)]; rw [natDegree_X_pow]

中文:
定理 X_pow_card_sub_X_natDegree_eq
  条件: (hp : 1 < p)
  结论: (X ^ p - X : K'[X]).natDegree = p
  证明: by
  have h1 : (X : K'[X]).degree < (X ^ p : K'[X]).degree := by
    rw [degree_X_pow]; rw [degree_X]
    exact mod_cast hp
  rw [natDegree_eq_of_degree_eq (degree_sub_eq_left_of_degree_lt h1)]; rw [natDegree_X_pow]

Depends on / 依赖: degree, degree_X, degree_X_pow, degree_sub_eq_left_of_degree_lt, mod_cast, natDegree_X_pow, natDegree_eq_of_degree_eq
-/
theorem X_pow_card_sub_X_natDegree_eq (hp : 1 < p) : (X ^ p - X : K'[X]).natDegree = p := by
  have h1 : (X : K'[X]).degree < (X ^ p : K'[X]).degree := by
    rw [degree_X_pow]; rw [degree_X]
    exact mod_cast hp
  rw [natDegree_eq_of_degree_eq (degree_sub_eq_left_of_degree_lt h1)]; rw [natDegree_X_pow]

/--
theorem `X_pow_card_pow_sub_X_natDegree_eq` / 定理 `X_pow_card_pow_sub_X_natDegree_eq`

English:
theorem X_pow_card_pow_sub_X_natDegree_eq
  given: (hn : n != 0) (hp : 1 < p)
  proof: X_pow_card_sub_X_natDegree_eq K' Nat.one_lt_pow hn hp

中文:
定理 X_pow_card_pow_sub_X_natDegree_eq
  条件: (hn : n != 0) (hp : 1 < p)
  证明: X_pow_card_sub_X_natDegree_eq K' Nat.one_lt_pow hn hp

Depends on / 依赖: Nat.one_lt_pow, X_pow_card_sub_X_natDegree_eq, one_lt_pow
-/
theorem X_pow_card_pow_sub_X_natDegree_eq (hn : n != 0) (hp : 1 < p) :
    (X ^ p ^ n - X : K'[X]).natDegree = p ^ n :=
X_pow_card_sub_X_natDegree_eq K' Nat.one_lt_pow hn hp

/--
theorem `X_pow_card_sub_X_ne_zero` / 定理 `X_pow_card_sub_X_ne_zero`

English:
theorem X_pow_card_sub_X_ne_zero
  given: (hp : 1 < p)
  statement: (X ^ p - X : K'[X]) != 0
  proof: ne_zero_of_natDegree_gt
    calc
      1 < _ := hp
      _ = _ := (X_pow_card_sub_X_natDegree_eq K' hp).symm

中文:
定理 X_pow_card_sub_X_ne_zero
  条件: (hp : 1 < p)
  结论: (X ^ p - X : K'[X]) != 0
  证明: ne_zero_of_natDegree_gt
    calc
      1 < _ := hp
      _ = _ := (X_pow_card_sub_X_natDegree_eq K' hp).symm

Depends on / 依赖: X_pow_card_sub_X_natDegree_eq, ne_zero_of_natDegree_gt
-/
theorem X_pow_card_sub_X_ne_zero (hp : 1 < p) : (X ^ p - X : K'[X]) != 0 :=
ne_zero_of_natDegree_gt
    calc
      1 < _ := hp
      _ = _ := (X_pow_card_sub_X_natDegree_eq K' hp).symm

/--
theorem `X_pow_card_pow_sub_X_ne_zero` / 定理 `X_pow_card_pow_sub_X_ne_zero`

English:
theorem X_pow_card_pow_sub_X_ne_zero
  given: (hn : n != 0) (hp : 1 < p)
  statement: (X ^ p ^ n - X : K'[X]) != 0
  proof: X_pow_card_sub_X_ne_zero K' Nat.one_lt_pow hn hp

中文:
定理 X_pow_card_pow_sub_X_ne_zero
  条件: (hn : n != 0) (hp : 1 < p)
  结论: (X ^ p ^ n - X : K'[X]) != 0
  证明: X_pow_card_sub_X_ne_zero K' Nat.one_lt_pow hn hp

Depends on / 依赖: Nat.one_lt_pow, X_pow_card_sub_X_ne_zero, one_lt_pow
-/
theorem X_pow_card_pow_sub_X_ne_zero (hn : n != 0) (hp : 1 < p) : (X ^ p ^ n - X : K'[X]) != 0 :=
X_pow_card_sub_X_ne_zero K' Nat.one_lt_pow hn hp

end

/--
theorem `roots_X_pow_card_sub_X` / 定理 `roots_X_pow_card_sub_X`

English:
theorem roots_X_pow_card_sub_X
  statement: roots (X ^ q - X : K[X]) = Finset.univ.val
  proof: by
  classical
    have aux : (X ^ q - X : K[X]) != 0 := X_pow_card_sub_X_ne_zero K Fintype.one_lt_card
    have : (roots (X ^ q - X : K[X])).toFinset = Finset.univ := by
      rw [eq_univ_iff_forall]
      intro x
      rw [Multiset.mem_toFinset]; rw [mem_roots aux]; rw [IsRoot.def]; rw [eval_sub];

中文:
定理 roots_X_pow_card_sub_X
  结论: roots (X ^ q - X : K[X]) = 有限集.univ.val
  证明: by
  classical
    have aux : (X ^ q - X : K[X]) != 0 := X_pow_card_sub_X_ne_zero K Fintype.one_lt_card
    have : (roots (X ^ q - X : K[X])).toFinset = Finset.univ := by
      rw [eq_univ_iff_forall]
      intro x
      rw [Multiset.mem_toFinset]; rw [mem_roots aux]; rw [IsRoot.def]; rw [eval_sub];

Depends on / 依赖: Finset, Finset.univ, Fintype, Fintype.one_lt_card, IsRoot, IsRoot.def, Multiset, Multiset.dedup_eq_self, Multiset.mem_toFinset, Multiset.toFinset_val, X_pow_card_sub_X_ne_zero, classical, convert, dedup_eq_self, eq_comm, eq_univ_iff_forall, eval_X, eval_pow, eval_sub, isCoprime_one_right
-/
theorem roots_X_pow_card_sub_X : roots (X ^ q - X : K[X]) = Finset.univ.val := by
  classical
    have aux : (X ^ q - X : K[X]) != 0 := X_pow_card_sub_X_ne_zero K Fintype.one_lt_card
    have : (roots (X ^ q - X : K[X])).toFinset = Finset.univ := by
      rw [eq_univ_iff_forall]
      intro x
      rw [Multiset.mem_toFinset]; rw [mem_roots aux]; rw [IsRoot.def]; rw [eval_sub]; rw [eval_pow]; rw [eval_X]; rw [sub_eq_zero]; rw [pow_card]
    rw [← this]; rw [Multiset.toFinset_val]; rw [eq_comm]; rw [Multiset.dedup_eq_self]
    apply nodup_roots
    rw [separable_def]
    convert! isCoprime_one_right.neg_right (R := K[X]) using 1
    rw [derivative_sub]; rw [derivative_X]; rw [derivative_X_pow]; rw [Nat.cast_card_eq_zero K]; rw [C_0]; rw [zero_mul]; rw [zero_sub]

variable {K}

/--
theorem `frobenius_pow` / 定理 `frobenius_pow`

English:
theorem frobenius_pow
  given: {p : Nat} [Fact p.Prime] [CharP K p] {n : Nat} (hcard : q = p ^ n)
  proof: by
  ext x; conv_rhs => rw [RingHom.one_def, RingHom.id_apply, ← pow_card x, hcard]
  clear hcard
  induction n with
  | zero => simp
  | succ n hn =>
    rw [pow_succ']; rw [pow_succ]; rw [pow_mul]; rw [RingHom.mul_def]; rw [RingHom.comp_apply]; rw [frobenius_def]; rw [hn]

中文:
定理 frobenius_pow
  条件: {p : 自然数} [Fact p.素] [特征p K p] {n : 自然数} (hcard : q = p ^ n)
  证明: by
  ext x; conv_rhs => rw [RingHom.one_def, RingHom.id_apply, ← pow_card x, hcard]
  clear hcard
  induction n with
  | zero => simp
  | succ n hn =>
    rw [pow_succ']; rw [pow_succ]; rw [pow_mul]; rw [RingHom.mul_def]; rw [RingHom.comp_apply]; rw [frobenius_def]; rw [hn]

Depends on / 依赖: RingHom, RingHom.comp_apply, RingHom.id_apply, RingHom.mul_def, RingHom.one_def, comp_apply, conv_rhs, frobenius_def, id_apply, mul_def, one_def, pow_card, pow_mul, pow_succ
-/
theorem frobenius_pow {p : Nat} [Fact p.Prime] [CharP K p] {n : Nat} (hcard : q = p ^ n) :
    frobenius K p ^ n = 1 := by
  ext x; conv_rhs => rw [RingHom.one_def, RingHom.id_apply, ← pow_card x, hcard]
  clear hcard
  induction n with
  | zero => simp
  | succ n hn =>
    rw [pow_succ']; rw [pow_succ]; rw [pow_mul]; rw [RingHom.mul_def]; rw [RingHom.comp_apply]; rw [frobenius_def]; rw [hn]

open Polynomial

/--
theorem `expand_card` / 定理 `expand_card`

English:
theorem expand_card
  given: (f : K[X])
  statement: expand K q f = f ^ q
  proof: by
  obtain ⟨p, hp⟩ := CharP.exists K
  rcases FiniteField.card K p with ⟨⟨n, npos⟩, ⟨hp, hn⟩⟩
  have : Fact p.Prime := ⟨hp⟩
  dsimp at hn
  rw [hn]; rw [← map_iterateFrobenius_expand]; rw [iterateFrobenius_eq_pow]; rw [frobenius_pow hn]; rw [RingHom.one_def]; rw [map_id]

中文:
定理 expand_card
  条件: (f : K[X])
  结论: expand K q f = f ^ q
  证明: by
  obtain ⟨p, hp⟩ := CharP.exists K
  rcases FiniteField.card K p with ⟨⟨n, npos⟩, ⟨hp, hn⟩⟩
  have : Fact p.Prime := ⟨hp⟩
  dsimp at hn
  rw [hn]; rw [← map_iterateFrobenius_expand]; rw [iterateFrobenius_eq_pow]; rw [frobenius_pow hn]; rw [RingHom.one_def]; rw [map_id]

Depends on / 依赖: CharP.exists, FiniteField, FiniteField.card, RingHom, RingHom.one_def, frobenius_pow, iterateFrobenius_eq_pow, map_id, map_iterateFrobenius_expand, one_def, p.Prime
-/
theorem expand_card (f : K[X]) : expand K q f = f ^ q := by
  obtain ⟨p, hp⟩ := CharP.exists K
  rcases FiniteField.card K p with ⟨⟨n, npos⟩, ⟨hp, hn⟩⟩
  have : Fact p.Prime := ⟨hp⟩
  dsimp at hn
  rw [hn]; rw [← map_iterateFrobenius_expand]; rw [iterateFrobenius_eq_pow]; rw [frobenius_pow hn]; rw [RingHom.one_def]; rw [map_id]

end FiniteField

namespace ZMod

open FiniteField Polynomial

set_option backward.isDefEq.respectTransparency false in
/--
theorem `sq_add_sq` / 定理 `sq_add_sq`

English:
theorem sq_add_sq
  given: (p : Nat) [hp : Fact p.Prime] (x : ZMod p)
  statement: exists a b : ZMod p, a ^ 2 + b ^ 2 = x
  proof: by
  rcases hp.1.eq_two_or_odd with rfl | hp_odd
  · change Fin 2 at x
    fin_cases x
    · use 0; simp
    · use 0, 1; simp
  let f : (ZMod p)[X] := X ^ 2
  let g : (ZMod p)[X] := X ^ 2 - C x
  obtain ⟨a, b, hab⟩ : exists a b, f.eval a + g.eval b = 0 :=
    @exists_root_sum_quadratic _ _ _ _ f g (

中文:
定理 sq_add_sq
  条件: (p : 自然数) [hp : Fact p.素] (x : ZMod p)
  结论: 存在 a b : ZMod p, a ^ 2 + b ^ 2 = x
  证明: by
  rcases hp.1.eq_two_or_odd with rfl | hp_odd
  · change Fin 2 at x
    fin_cases x
    · use 0; simp
    · use 0, 1; simp
  let f : (ZMod p)[X] := X ^ 2
  let g : (ZMod p)[X] := X ^ 2 - C x
  obtain ⟨a, b, hab⟩ : exists a b, f.eval a + g.eval b = 0 :=
    @exists_root_sum_quadratic _ _ _ _ f g (

Depends on / 依赖: ZMod.card, add_sub_assoc, degree_X_pow, degree_X_pow_sub_C, eq_two_or_odd, eval_C, eval_X, eval_pow, eval_sub, exists_root_sum_quadratic, f.eval, fin_cases, g.eval, hp_odd, sub_eq_zero
-/
theorem sq_add_sq (p : Nat) [hp : Fact p.Prime] (x : ZMod p) : exists a b : ZMod p, a ^ 2 + b ^ 2 = x := by
  rcases hp.1.eq_two_or_odd with rfl | hp_odd
  · change Fin 2 at x
    fin_cases x
    · use 0; simp
    · use 0, 1; simp
  let f : (ZMod p)[X] := X ^ 2
  let g : (ZMod p)[X] := X ^ 2 - C x
  obtain ⟨a, b, hab⟩ : exists a b, f.eval a + g.eval b = 0 :=
    @exists_root_sum_quadratic _ _ _ _ f g (degree_X_pow 2) (degree_X_pow_sub_C (by decide) _)
      (by rw [ZMod.card, hp_odd])
  refine ⟨a, b, ?_⟩
  rw [← sub_eq_zero]
  simpa only [f, g, eval_C, eval_X, eval_pow, eval_sub, ← add_sub_assoc] using hab

end ZMod

/--
theorem `Nat.sq_add_sq_zmodEq` / 定理 `Nat.sq_add_sq_zmodEq`

English:
theorem Nat.sq_add_sq_zmodEq
  given: (p : Nat) [Fact p.Prime] (x : Int)
  proof: by
  rcases ZMod.sq_add_sq p x with ⟨a, b, hx⟩
  refine ⟨a.valMinAbs.natAbs, b.valMinAbs.natAbs, ZMod.natAbs_valMinAbs_le _,
    ZMod.natAbs_valMinAbs_le _, ?_⟩
  rw [← a.coe_valMinAbs]; rw [← b.coe_valMinAbs] at hx
  push_cast
  rw [sq_abs]; rw [sq_abs]; rw [← ZMod.intCast_eq_intCast_iff]
  exact m

中文:
定理 自然数.sq_add_sq_zmodEq
  条件: (p : 自然数) [Fact p.素] (x : 整数)
  证明: by
  rcases ZMod.sq_add_sq p x with ⟨a, b, hx⟩
  refine ⟨a.valMinAbs.natAbs, b.valMinAbs.natAbs, ZMod.natAbs_valMinAbs_le _,
    ZMod.natAbs_valMinAbs_le _, ?_⟩
  rw [← a.coe_valMinAbs]; rw [← b.coe_valMinAbs] at hx
  push_cast
  rw [sq_abs]; rw [sq_abs]; rw [← ZMod.intCast_eq_intCast_iff]
  exact m

Depends on / 依赖: ZMod.intCast_eq_intCast_iff, ZMod.natAbs_valMinAbs_le, ZMod.sq_add_sq, a.coe_valMinAbs, a.valMinAbs.natAbs, b.coe_valMinAbs, b.valMinAbs.natAbs, coe_valMinAbs, intCast_eq_intCast_iff, mod_cast, natAbs, natAbs_valMinAbs_le, sq_abs, sq_add_sq, valMinAbs
-/
theorem Nat.sq_add_sq_zmodEq (p : Nat) [Fact p.Prime] (x : Int) :
    exists a b : Nat, a <= p / 2 ∧ b <= p / 2 ∧ (a : Int) ^ 2 + (b : Int) ^ 2 ≡ x [ZMOD p] := by
  rcases ZMod.sq_add_sq p x with ⟨a, b, hx⟩
  refine ⟨a.valMinAbs.natAbs, b.valMinAbs.natAbs, ZMod.natAbs_valMinAbs_le _,
    ZMod.natAbs_valMinAbs_le _, ?_⟩
  rw [← a.coe_valMinAbs]; rw [← b.coe_valMinAbs] at hx
  push_cast
  rw [sq_abs]; rw [sq_abs]; rw [← ZMod.intCast_eq_intCast_iff]
  exact mod_cast hx

/--
theorem `Nat.sq_add_sq_modEq` / 定理 `Nat.sq_add_sq_modEq`

English:
theorem Nat.sq_add_sq_modEq
  given: (p : Nat) [Fact p.Prime] (x : Nat)
  proof: by
  simpa only [← Int.natCast_modEq_iff] using! Nat.sq_add_sq_zmodEq p x

中文:
定理 自然数.sq_add_sq_modEq
  条件: (p : 自然数) [Fact p.素] (x : 自然数)
  证明: by
  simpa only [← Int.natCast_modEq_iff] using! Nat.sq_add_sq_zmodEq p x

Depends on / 依赖: Int.natCast_modEq_iff, Nat.sq_add_sq_zmodEq, natCast_modEq_iff, sq_add_sq_zmodEq
-/
theorem Nat.sq_add_sq_modEq (p : Nat) [Fact p.Prime] (x : Nat) :
    exists a b : Nat, a <= p / 2 ∧ b <= p / 2 ∧ a ^ 2 + b ^ 2 ≡ x [MOD p] := by
  simpa only [← Int.natCast_modEq_iff] using! Nat.sq_add_sq_zmodEq p x

namespace CharP

/--
theorem `sq_add_sq` / 定理 `sq_add_sq`

English:
theorem sq_add_sq
  given: (R : Type*) [Ring R] [IsDomain R] (p : Nat) [NeZero p] [CharP R p] (x : Int)
  proof: by
  have := char_is_prime_of_pos R p
  obtain ⟨a, b, hab⟩ := ZMod.sq_add_sq p x
  refine ⟨a.val, b.val, ?_⟩
  simpa using congr_arg (ZMod.castHom dvd_rfl R) hab

中文:
定理 sq_add_sq
  条件: (R : 类型) [环 R] [是整环 R] (p : 自然数) [NeZero p] [特征p R p] (x : 整数)
  证明: by
  have := char_is_prime_of_pos R p
  obtain ⟨a, b, hab⟩ := ZMod.sq_add_sq p x
  refine ⟨a.val, b.val, ?_⟩
  simpa using congr_arg (ZMod.castHom dvd_rfl R) hab

Depends on / 依赖: ZMod.castHom, ZMod.sq_add_sq, a.val, b.val, castHom, char_is_prime_of_pos, congr_arg, dvd_rfl, sq_add_sq
-/
theorem sq_add_sq (R : Type*) [Ring R] [IsDomain R] (p : Nat) [NeZero p] [CharP R p] (x : Int) :
    exists a b : Nat, ((a : R) ^ 2 + (b : R) ^ 2) = x := by
  have := char_is_prime_of_pos R p
  obtain ⟨a, b, hab⟩ := ZMod.sq_add_sq p x
  refine ⟨a.val, b.val, ?_⟩
  simpa using congr_arg (ZMod.castHom dvd_rfl R) hab

end CharP

open scoped Nat

open ZMod

/-- The **Fermat-Euler totient theorem**. `Nat.ModEq.pow_totient` is an alternative statement
  of the same theorem. -/
@[simp]
/--
theorem `ZMod.pow_totient` / 定理 `ZMod.pow_totient`

English:
theorem ZMod.pow_totient
  given: {n : Nat} (x : (ZMod n)ˣ)
  statement: x ^ φ n = 1
  proof: by
  cases n
  · rw [Nat.totient_zero, pow_zero]
  · rw [← card_units_eq_totient, pow_card_eq_one]

中文:
定理 ZMod.pow_totient
  条件: {n : 自然数} (x : (ZMod n)ˣ)
  结论: x ^ φ n = 1
  证明: by
  cases n
  · rw [Nat.totient_zero, pow_zero]
  · rw [← card_units_eq_totient, pow_card_eq_one]

Depends on / 依赖: Nat.totient_zero, card_units_eq_totient, pow_card_eq_one, pow_zero, totient_zero
-/
theorem ZMod.pow_totient {n : Nat} (x : (ZMod n)ˣ) : x ^ φ n = 1 := by
  cases n
  · rw [Nat.totient_zero, pow_zero]
  · rw [← card_units_eq_totient, pow_card_eq_one]

/--
theorem `Nat.ModEq.pow_totient` / 定理 `Nat.ModEq.pow_totient`

English:
theorem Nat.ModEq.pow_totient
  given: {x n : Nat} (h : Nat.Coprime x n)
  statement: x ^ φ n ≡ 1 [MOD n]
  proof: by
  rw [← ZMod.natCast_eq_natCast_iff]
  let x' : Units (ZMod n) := ZMod.unitOfCoprime _ h
  have := ZMod.pow_totient x'
  apply_fun ((fun (x : Units (ZMod n)) => (x : ZMod n)) : Units (ZMod n) -> ZMod n) at this
  simpa only [Nat.succ_eq_add_one, Nat.cast_pow, Units.val_one, Nat.cast_one,
    coe_

中文:
定理 自然数.ModEq.pow_totient
  条件: {x n : 自然数} (h : 自然数.Coprime x n)
  结论: x ^ φ n ≡ 1 [MOD n]
  证明: by
  rw [← ZMod.natCast_eq_natCast_iff]
  let x' : Units (ZMod n) := ZMod.unitOfCoprime _ h
  have := ZMod.pow_totient x'
  apply_fun ((fun (x : Units (ZMod n)) => (x : ZMod n)) : Units (ZMod n) -> ZMod n) at this
  simpa only [Nat.succ_eq_add_one, Nat.cast_pow, Units.val_one, Nat.cast_one,
    coe_

Depends on / 依赖: Nat.cast_one, Nat.cast_pow, Nat.succ_eq_add_one, Units.val_one, Units.val_pow_eq_pow_val, ZMod.natCast_eq_natCast_iff, ZMod.pow_totient, ZMod.unitOfCoprime, apply_fun, cast_one, cast_pow, coe_unitOfCoprime, natCast_eq_natCast_iff, pow_totient, succ_eq_add_one, unitOfCoprime, val_one, val_pow_eq_pow_val
-/
theorem Nat.ModEq.pow_totient {x n : Nat} (h : Nat.Coprime x n) : x ^ φ n ≡ 1 [MOD n] := by
  rw [← ZMod.natCast_eq_natCast_iff]
  let x' : Units (ZMod n) := ZMod.unitOfCoprime _ h
  have := ZMod.pow_totient x'
  apply_fun ((fun (x : Units (ZMod n)) => (x : ZMod n)) : Units (ZMod n) -> ZMod n) at this
  simpa only [Nat.succ_eq_add_one, Nat.cast_pow, Units.val_one, Nat.cast_one,
    coe_unitOfCoprime, Units.val_pow_eq_pow_val]

open FiniteField

namespace ZMod

variable {p : Nat} [Fact p.Prime]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Subsingleton (Subfield (ZMod p))
  body: subsingleton_of_bot_eq_top top_unique (a := ⊥) fun n _ =>
  have := zsmul_mem (one_mem (⊥ : Subfield (ZMod p))) n.val
  by rwa [natCast_zsmul, Nat.smul_one_eq_cast, ZMod.natCast_zmod_val] at this

中文:
实例 :
  签名: 子单例 (子域 (ZMod p))
  定义体: subsingleton_of_bot_eq_top top_unique (a := ⊥) fun n _ =>
  have := zsmul_mem (one_mem (⊥ : Subfield (ZMod p))) n.val
  by rwa [natCast_zsmul, Nat.smul_one_eq_cast, ZMod.natCast_zmod_val] at this

Depends on / 依赖: Nat.smul_one_eq_cast, Subfield, ZMod.natCast_zmod_val, n.val, natCast_zmod_val, natCast_zsmul, one_mem, smul_one_eq_cast, subsingleton_of_bot_eq_top, top_unique, zsmul_mem
-/
instance : Subsingleton (Subfield (ZMod p)) :=
subsingleton_of_bot_eq_top top_unique (a := ⊥) fun n _ =>
  have := zsmul_mem (one_mem (⊥ : Subfield (ZMod p))) n.val
  by rwa [natCast_zsmul, Nat.smul_one_eq_cast, ZMod.natCast_zmod_val] at this

/--
theorem `fieldRange_castHom_eq_bot` / 定理 `fieldRange_castHom_eq_bot`

English:
theorem fieldRange_castHom_eq_bot
  given: (p : Nat) [Fact p.Prime] [DivisionRing K] [CharP K p]
  proof: by
  rw [RingHom.fieldRange_eq_map]; rw [← Subfield.map_bot (K := ZMod p)]; rw [Subsingleton.elim ⊥]

中文:
定理 fieldRange_castHom_eq_bot
  条件: (p : 自然数) [Fact p.素] [除环 K] [特征p K p]
  证明: by
  rw [RingHom.fieldRange_eq_map]; rw [← Subfield.map_bot (K := ZMod p)]; rw [Subsingleton.elim ⊥]

Depends on / 依赖: RingHom, RingHom.fieldRange_eq_map, Subfield, Subfield.map_bot, Subsingleton, Subsingleton.elim, dvd_rfl, fieldRange, fieldRange_eq_map, map_bot
-/
theorem fieldRange_castHom_eq_bot (p : Nat) [Fact p.Prime] [DivisionRing K] [CharP K p] :
    (ZMod.castHom (m := p) dvd_rfl K).fieldRange = (⊥ : Subfield K) := by
  rw [RingHom.fieldRange_eq_map]; rw [← Subfield.map_bot (K := ZMod p)]; rw [Subsingleton.elim ⊥]

/-- A variation on Fermat's little theorem. See `ZMod.pow_card_sub_one_eq_one` -/
@[simp]
/--
theorem `pow_card` / 定理 `pow_card`

English:
theorem pow_card
  given: (x : ZMod p)
  statement: x ^ p = x
  proof: by
  have h := FiniteField.pow_card x; rwa [ZMod.card p] at h

@[simp]

中文:
定理 pow_card
  条件: (x : ZMod p)
  结论: x ^ p = x
  证明: by
  have h := FiniteField.pow_card x; rwa [ZMod.card p] at h

@[simp]

Depends on / 依赖: FiniteField, FiniteField.pow_card, ZMod.card, pow_card
-/
theorem pow_card (x : ZMod p) : x ^ p = x := by
  have h := FiniteField.pow_card x; rwa [ZMod.card p] at h

@[simp]
/--
theorem `pow_card_pow` / 定理 `pow_card_pow`

English:
theorem pow_card_pow
  given: {n : Nat} (x : ZMod p)
  statement: x ^ p ^ n = x
  proof: by
  induction n with
  | zero => simp
  | succ n ih => simp [pow_succ, pow_mul, ih, pow_card]

@[simp]

中文:
定理 pow_card_pow
  条件: {n : 自然数} (x : ZMod p)
  结论: x ^ p ^ n = x
  证明: by
  induction n with
  | zero => simp
  | succ n ih => simp [pow_succ, pow_mul, ih, pow_card]

@[simp]

Depends on / 依赖: pow_card, pow_mul, pow_succ
-/
theorem pow_card_pow {n : Nat} (x : ZMod p) : x ^ p ^ n = x := by
  induction n with
  | zero => simp
  | succ n ih => simp [pow_succ, pow_mul, ih, pow_card]

@[simp]
/--
theorem `frobenius_zmod` / 定理 `frobenius_zmod`

English:
theorem frobenius_zmod
  given: (p : Nat) [Fact p.Prime]
  statement: frobenius (ZMod p) p = RingHom.id _
  proof: by
  ext a
  rw [frobenius_def]; rw [ZMod.pow_card]; rw [RingHom.id_apply]

中文:
定理 frobenius_zmod
  条件: (p : 自然数) [Fact p.素]
  结论: frobenius (ZMod p) p = 环态射.id _
  证明: by
  ext a
  rw [frobenius_def]; rw [ZMod.pow_card]; rw [RingHom.id_apply]

Depends on / 依赖: RingHom, RingHom.id_apply, ZMod.pow_card, frobenius_def, id_apply, pow_card
-/
theorem frobenius_zmod (p : Nat) [Fact p.Prime] : frobenius (ZMod p) p = RingHom.id _ := by
  ext a
  rw [frobenius_def]; rw [ZMod.pow_card]; rw [RingHom.id_apply]

-- This was a `simp` lemma, but now the LHS simplifies to `φ p`.
/--
theorem `card_units` / 定理 `card_units`

English:
theorem card_units
  given: (p : Nat) [Fact p.Prime]
  statement: Fintype.card (ZMod p)ˣ = p - 1
  proof: by
  rw [Fintype.card_units]; rw [card]

中文:
定理 card_units
  条件: (p : 自然数) [Fact p.素]
  结论: 有限类型.card (ZMod p)ˣ = p - 1
  证明: by
  rw [Fintype.card_units]; rw [card]

Depends on / 依赖: Fintype, Fintype.card_units, card_units
-/
theorem card_units (p : Nat) [Fact p.Prime] : Fintype.card (ZMod p)ˣ = p - 1 := by
  rw [Fintype.card_units]; rw [card]

/--
theorem `units_pow_card_sub_one_eq_one` / 定理 `units_pow_card_sub_one_eq_one`

English:
theorem units_pow_card_sub_one_eq_one
  given: (p : Nat) [Fact p.Prime] (a : (ZMod p)ˣ)
  statement: a ^ (p - 1) = 1
  proof: by
  rw [← card_units p]; rw [pow_card_eq_one]

中文:
定理 units_pow_card_sub_one_eq_one
  条件: (p : 自然数) [Fact p.素] (a : (ZMod p)ˣ)
  结论: a ^ (p - 1) = 1
  证明: by
  rw [← card_units p]; rw [pow_card_eq_one]

Depends on / 依赖: card_units, pow_card_eq_one
-/
theorem units_pow_card_sub_one_eq_one (p : Nat) [Fact p.Prime] (a : (ZMod p)ˣ) : a ^ (p - 1) = 1 := by
  rw [← card_units p]; rw [pow_card_eq_one]

/--
theorem `pow_card_sub_one_eq_one` / 定理 `pow_card_sub_one_eq_one`

English:
theorem pow_card_sub_one_eq_one
  given: {a : ZMod p} (ha : a != 0)
  proof: by
  have h := FiniteField.pow_card_sub_one_eq_one a ha
  rwa [ZMod.card p] at h

中文:
定理 pow_card_sub_one_eq_one
  条件: {a : ZMod p} (ha : a != 0)
  证明: by
  have h := FiniteField.pow_card_sub_one_eq_one a ha
  rwa [ZMod.card p] at h

Depends on / 依赖: FiniteField, FiniteField.pow_card_sub_one_eq_one, ZMod.card, pow_card_sub_one_eq_one
-/
theorem pow_card_sub_one_eq_one {a : ZMod p} (ha : a != 0) :
    a ^ (p - 1) = 1 := by
  have h := FiniteField.pow_card_sub_one_eq_one a ha
  rwa [ZMod.card p] at h

/--
lemma `pow_card_sub_one` / 引理 `pow_card_sub_one`

English:
lemma pow_card_sub_one
  given: (a : ZMod p)
  proof: by
  split_ifs with ha
  · exact pow_card_sub_one_eq_one ha
  · simp [of_not_not ha, (Fact.out : p.Prime).one_lt, tsub_eq_zero_iff_le]

中文:
引理 pow_card_sub_one
  条件: (a : ZMod p)
  证明: by
  split_ifs with ha
  · exact pow_card_sub_one_eq_one ha
  · simp [of_not_not ha, (Fact.out : p.Prime).one_lt, tsub_eq_zero_iff_le]

Depends on / 依赖: Fact.out, of_not_not, one_lt, p.Prime, pow_card_sub_one_eq_one, split_ifs, tsub_eq_zero_iff_le
-/
lemma pow_card_sub_one (a : ZMod p) :
    a ^ (p - 1) = if a != 0 then 1 else 0 := by
  split_ifs with ha
  · exact pow_card_sub_one_eq_one ha
  · simp [of_not_not ha, (Fact.out : p.Prime).one_lt, tsub_eq_zero_iff_le]

/--
theorem `orderOf_units_dvd_card_sub_one` / 定理 `orderOf_units_dvd_card_sub_one`

English:
theorem orderOf_units_dvd_card_sub_one
  given: (u : (ZMod p)ˣ)
  statement: orderOf u ∣ p - 1
  proof: orderOf_dvd_of_pow_eq_one units_pow_card_sub_one_eq_one _ _

中文:
定理 orderOf_units_dvd_card_sub_one
  条件: (u : (ZMod p)ˣ)
  结论: orderOf u ∣ p - 1
  证明: orderOf_dvd_of_pow_eq_one units_pow_card_sub_one_eq_one _ _

Depends on / 依赖: orderOf_dvd_of_pow_eq_one, units_pow_card_sub_one_eq_one
-/
theorem orderOf_units_dvd_card_sub_one (u : (ZMod p)ˣ) : orderOf u ∣ p - 1 :=
orderOf_dvd_of_pow_eq_one units_pow_card_sub_one_eq_one _ _

/--
theorem `orderOf_dvd_card_sub_one` / 定理 `orderOf_dvd_card_sub_one`

English:
theorem orderOf_dvd_card_sub_one
  given: {a : ZMod p} (ha : a != 0)
  proof: orderOf_dvd_of_pow_eq_one pow_card_sub_one_eq_one ha

中文:
定理 orderOf_dvd_card_sub_one
  条件: {a : ZMod p} (ha : a != 0)
  证明: orderOf_dvd_of_pow_eq_one pow_card_sub_one_eq_one ha

Depends on / 依赖: orderOf_dvd_of_pow_eq_one, pow_card_sub_one_eq_one
-/
theorem orderOf_dvd_card_sub_one {a : ZMod p} (ha : a != 0) :
    orderOf a ∣ p - 1 :=
orderOf_dvd_of_pow_eq_one pow_card_sub_one_eq_one ha

open Polynomial

/--
theorem `expand_card` / 定理 `expand_card`

English:
theorem expand_card
  given: (f : Polynomial (ZMod p))
  proof: by have h := FiniteField.expand_card f; rwa [ZMod.card p] at h

中文:
定理 expand_card
  条件: (f : 多项式 (ZMod p))
  证明: by have h := FiniteField.expand_card f; rwa [ZMod.card p] at h

Depends on / 依赖: FiniteField, FiniteField.expand_card, ZMod.card, expand_card
-/
theorem expand_card (f : Polynomial (ZMod p)) :
    expand (ZMod p) p f = f ^ p := by have h := FiniteField.expand_card f; rwa [ZMod.card p] at h

end ZMod

/--
theorem `Int.ModEq.pow_card_sub_one_eq_one` / 定理 `Int.ModEq.pow_card_sub_one_eq_one`

English:
theorem Int.ModEq.pow_card_sub_one_eq_one
  given: {p : Nat} (hp : Nat.Prime p) {n : Int} (hpn : IsCoprime n p)
  proof: by
  have : Fact p.Prime := ⟨hp⟩
  have : ¬(n : ZMod p) = 0 := by
    rw [CharP.intCast_eq_zero_iff _ p]; rw [← (Nat.prime_iff_prime_int.mp hp).coprime_iff_not_dvd]
    · exact hpn.symm
  simpa [← ZMod.intCast_eq_intCast_iff] using ZMod.pow_card_sub_one_eq_one this

中文:
定理 整数.ModEq.pow_card_sub_one_eq_one
  条件: {p : 自然数} (hp : 自然数.素 p) {n : 整数} (hpn : IsCoprime n p)
  证明: by
  have : Fact p.Prime := ⟨hp⟩
  have : ¬(n : ZMod p) = 0 := by
    rw [CharP.intCast_eq_zero_iff _ p]; rw [← (Nat.prime_iff_prime_int.mp hp).coprime_iff_not_dvd]
    · exact hpn.symm
  simpa [← ZMod.intCast_eq_intCast_iff] using ZMod.pow_card_sub_one_eq_one this

Depends on / 依赖: CharP.intCast_eq_zero_iff, Nat.prime_iff_prime_int.mp, ZMod.intCast_eq_intCast_iff, ZMod.pow_card_sub_one_eq_one, coprime_iff_not_dvd, hpn.symm, intCast_eq_intCast_iff, intCast_eq_zero_iff, p.Prime, pow_card_sub_one_eq_one, prime_iff_prime_int
-/
theorem Int.ModEq.pow_card_sub_one_eq_one {p : Nat} (hp : Nat.Prime p) {n : Int} (hpn : IsCoprime n p) :
    n ^ (p - 1) ≡ 1 [ZMOD p] := by
  have : Fact p.Prime := ⟨hp⟩
  have : ¬(n : ZMod p) = 0 := by
    rw [CharP.intCast_eq_zero_iff _ p]; rw [← (Nat.prime_iff_prime_int.mp hp).coprime_iff_not_dvd]
    · exact hpn.symm
  simpa [← ZMod.intCast_eq_intCast_iff] using ZMod.pow_card_sub_one_eq_one this

/--
theorem `Int.prime_dvd_pow_sub_one` / 定理 `Int.prime_dvd_pow_sub_one`

English:
theorem Int.prime_dvd_pow_sub_one
  given: {p : Nat} (hp : Nat.Prime p) {n : Int} (hpn : IsCoprime n p)
  proof: (ModEq.pow_card_sub_one_eq_one hp hpn).symm.dvd

中文:
定理 整数.prime_dvd_pow_sub_one
  条件: {p : 自然数} (hp : 自然数.素 p) {n : 整数} (hpn : IsCoprime n p)
  证明: (ModEq.pow_card_sub_one_eq_one hp hpn).symm.dvd

Depends on / 依赖: ModEq.pow_card_sub_one_eq_one, pow_card_sub_one_eq_one, symm.dvd
-/
theorem Int.prime_dvd_pow_sub_one {p : Nat} (hp : Nat.Prime p) {n : Int} (hpn : IsCoprime n p) :
    (p : Int) ∣ n ^ (p - 1) - 1 :=
  (ModEq.pow_card_sub_one_eq_one hp hpn).symm.dvd

/--
theorem `Int.ModEq.pow_prime_eq_self` / 定理 `Int.ModEq.pow_prime_eq_self`

English:
theorem Int.ModEq.pow_prime_eq_self
  given: {p : Nat} (hp : Nat.Prime p) (n : Int)
  statement: n ^ p ≡ n [ZMOD p]
  proof: by
  have : Fact p.Prime := ⟨hp⟩
  simp [← ZMod.intCast_eq_intCast_iff]

中文:
定理 整数.ModEq.pow_prime_eq_self
  条件: {p : 自然数} (hp : 自然数.素 p) (n : 整数)
  结论: n ^ p ≡ n [ZMOD p]
  证明: by
  have : Fact p.Prime := ⟨hp⟩
  simp [← ZMod.intCast_eq_intCast_iff]

Depends on / 依赖: ZMod.intCast_eq_intCast_iff, intCast_eq_intCast_iff, p.Prime
-/
theorem Int.ModEq.pow_prime_eq_self {p : Nat} (hp : Nat.Prime p) (n : Int) : n ^ p ≡ n [ZMOD p] := by
  have : Fact p.Prime := ⟨hp⟩
  simp [← ZMod.intCast_eq_intCast_iff]

/--
theorem `Int.prime_dvd_pow_self_sub` / 定理 `Int.prime_dvd_pow_self_sub`

English:
theorem Int.prime_dvd_pow_self_sub
  given: {p : Nat} (hp : Nat.Prime p) (n : Int)
  statement: (p : Int) ∣ n ^ p - n
  proof: (ModEq.pow_prime_eq_self hp n).symm.dvd

中文:
定理 整数.prime_dvd_pow_self_sub
  条件: {p : 自然数} (hp : 自然数.素 p) (n : 整数)
  结论: (p : 整数) ∣ n ^ p - n
  证明: (ModEq.pow_prime_eq_self hp n).symm.dvd

Depends on / 依赖: ModEq.pow_prime_eq_self, pow_prime_eq_self, symm.dvd
-/
theorem Int.prime_dvd_pow_self_sub {p : Nat} (hp : Nat.Prime p) (n : Int) : (p : Int) ∣ n ^ p - n :=
  (ModEq.pow_prime_eq_self hp n).symm.dvd

/--
theorem `Int.ModEq.pow_eq_pow` / 定理 `Int.ModEq.pow_eq_pow`

English:
theorem Int.ModEq.pow_eq_pow
  statement: {p x y : Nat} (hp : Nat.Prime p) (h : p - 1 ∣ x - y) (hxy : y <= x)
  proof: by
  rw [← Nat.mul_div_eq_iff_dvd] at h
  by_cases hn : n ≡ 0 [ZMOD p]
  · grw [hn, zero_pow (hy.trans_le hxy).ne', zero_pow hy.ne']
  · rw [Int.modEq_zero_iff_dvd, ← (Nat.prime_iff_prime_int.mp hp).coprime_iff_not_dvd] at hn
    grw [← pow_sub_mul_pow n hxy, ← h, pow_mul, Int.ModEq.pow_card_sub_one

中文:
定理 整数.ModEq.pow_eq_pow
  结论: {p x y : 自然数} (hp : 自然数.素 p) (h : p - 1 ∣ x - y) (hxy : y <= x)
  证明: by
  rw [← Nat.mul_div_eq_iff_dvd] at h
  by_cases hn : n ≡ 0 [ZMOD p]
  · grw [hn, zero_pow (hy.trans_le hxy).ne', zero_pow hy.ne']
  · rw [Int.modEq_zero_iff_dvd, ← (Nat.prime_iff_prime_int.mp hp).coprime_iff_not_dvd] at hn
    grw [← pow_sub_mul_pow n hxy, ← h, pow_mul, Int.ModEq.pow_card_sub_one

Depends on / 依赖: Int.ModEq.pow_card_sub_one_eq_one, Int.modEq_zero_iff_dvd, Nat.mul_div_eq_iff_dvd, Nat.prime_iff_prime_int.mp, coprime_iff_not_dvd, hn.symm, hy.ne, hy.trans_le, modEq_zero_iff_dvd, mul_div_eq_iff_dvd, one_mul, one_pow, pow_card_sub_one_eq_one, pow_mul, pow_sub_mul_pow, prime_iff_prime_int, trans_le, zero_pow
-/
theorem Int.ModEq.pow_eq_pow {p x y : Nat} (hp : Nat.Prime p) (h : p - 1 ∣ x - y) (hxy : y <= x)
    (hy : 0 < y) (n : Int) : n ^ x ≡ n ^ y [ZMOD p] := by
  rw [← Nat.mul_div_eq_iff_dvd] at h
  by_cases hn : n ≡ 0 [ZMOD p]
  · grw [hn, zero_pow (hy.trans_le hxy).ne', zero_pow hy.ne']
  · rw [Int.modEq_zero_iff_dvd, ← (Nat.prime_iff_prime_int.mp hp).coprime_iff_not_dvd] at hn
    grw [← pow_sub_mul_pow n hxy, ← h, pow_mul, Int.ModEq.pow_card_sub_one_eq_one hp hn.symm,
      one_pow, one_mul]

/--
theorem `Nat.ModEq.pow_card_sub_one_eq_one` / 定理 `Nat.ModEq.pow_card_sub_one_eq_one`

English:
theorem Nat.ModEq.pow_card_sub_one_eq_one
  given: {p : Nat} (hp : p.Prime) {n : Nat} (hpn : n.Coprime p)
  proof: by
  rw [← Int.natCast_modEq_iff]; rw [Nat.cast_pow]; rw [Nat.cast_one]
  exact Int.ModEq.pow_card_sub_one_eq_one hp (isCoprime_iff_coprime.mpr hpn)

中文:
定理 自然数.ModEq.pow_card_sub_one_eq_one
  条件: {p : 自然数} (hp : p.素) {n : 自然数} (hpn : n.Coprime p)
  证明: by
  rw [← Int.natCast_modEq_iff]; rw [Nat.cast_pow]; rw [Nat.cast_one]
  exact Int.ModEq.pow_card_sub_one_eq_one hp (isCoprime_iff_coprime.mpr hpn)

Depends on / 依赖: Int.ModEq.pow_card_sub_one_eq_one, Int.natCast_modEq_iff, Nat.cast_one, Nat.cast_pow, cast_one, cast_pow, isCoprime_iff_coprime, isCoprime_iff_coprime.mpr, natCast_modEq_iff, pow_card_sub_one_eq_one
-/
theorem Nat.ModEq.pow_card_sub_one_eq_one {p : Nat} (hp : p.Prime) {n : Nat} (hpn : n.Coprime p) :
    n ^ (p - 1) ≡ 1 [MOD p] := by
  rw [← Int.natCast_modEq_iff]; rw [Nat.cast_pow]; rw [Nat.cast_one]
  exact Int.ModEq.pow_card_sub_one_eq_one hp (isCoprime_iff_coprime.mpr hpn)

/--
theorem `Nat.pow_card_sub_one_sub_one_mod_card` / 定理 `Nat.pow_card_sub_one_sub_one_mod_card`

English:
theorem Nat.pow_card_sub_one_sub_one_mod_card
  given: {p : Nat} (hp : p.Prime) {n : Nat} (hpn : n.Coprime p)
  proof: Nat.sub_mod_eq_zero_of_mod_eq (Nat.ModEq.pow_card_sub_one_eq_one hp hpn)

中文:
定理 自然数.pow_card_sub_one_sub_one_mod_card
  条件: {p : 自然数} (hp : p.素) {n : 自然数} (hpn : n.Coprime p)
  证明: Nat.sub_mod_eq_zero_of_mod_eq (Nat.ModEq.pow_card_sub_one_eq_one hp hpn)

Depends on / 依赖: Nat.ModEq.pow_card_sub_one_eq_one, Nat.sub_mod_eq_zero_of_mod_eq, pow_card_sub_one_eq_one, sub_mod_eq_zero_of_mod_eq
-/
theorem Nat.pow_card_sub_one_sub_one_mod_card {p : Nat} (hp : p.Prime) {n : Nat} (hpn : n.Coprime p) :
    (n ^ (p - 1) - 1) % p = 0 :=
  Nat.sub_mod_eq_zero_of_mod_eq (Nat.ModEq.pow_card_sub_one_eq_one hp hpn)

/--
theorem `pow_pow_modEq_one` / 定理 `pow_pow_modEq_one`

English:
theorem pow_pow_modEq_one
  given: (p m a : Nat)
  statement: (1 + p * a) ^ (p ^ m) ≡ 1 [MOD p ^ m]
  proof: by
  induction m with
  | zero => exact Nat.modEq_one
  | succ m hm =>
    rw [Nat.ModEq.comm]; rw [add_comm]; rw [Nat.modEq_iff_dvd' (Nat.one_le_pow' _ _)] at hm
    obtain ⟨d, hd⟩ := hm
    rw [tsub_eq_iff_eq_add_of_le (Nat.one_le_pow' _ _)]; rw [add_comm] at hd
    rw [pow_succ]; rw [pow_mul]; rw

中文:
定理 pow_pow_modEq_one
  条件: (p m a : 自然数)
  结论: (1 + p * a) ^ (p ^ m) ≡ 1 [MOD p ^ m]
  证明: by
  induction m with
  | zero => exact Nat.modEq_one
  | succ m hm =>
    rw [Nat.ModEq.comm]; rw [add_comm]; rw [Nat.modEq_iff_dvd' (Nat.one_le_pow' _ _)] at hm
    obtain ⟨d, hd⟩ := hm
    rw [tsub_eq_iff_eq_add_of_le (Nat.one_le_pow' _ _)]; rw [add_comm] at hd
    rw [pow_succ]; rw [pow_mul]; rw

Depends on / 依赖: Finset, Finset.sum_range_succ, Nat.ModEq.add_right, Nat.ModEq.comm, Nat.cast_one, Nat.choose_zero_right, Nat.modEq_iff_dvd, Nat.modEq_one, Nat.modEq_zero_iff_dvd.mpr, Nat.one_le_pow, add_comm, add_pow, add_right, cast_one, choose_zero_right, modEq_iff_dvd, modEq_one, modEq_zero_iff_dvd, one_le_pow, one_mul
-/
theorem pow_pow_modEq_one (p m a : Nat) : (1 + p * a) ^ (p ^ m) ≡ 1 [MOD p ^ m] := by
  induction m with
  | zero => exact Nat.modEq_one
  | succ m hm =>
    rw [Nat.ModEq.comm]; rw [add_comm]; rw [Nat.modEq_iff_dvd' (Nat.one_le_pow' _ _)] at hm
    obtain ⟨d, hd⟩ := hm
    rw [tsub_eq_iff_eq_add_of_le (Nat.one_le_pow' _ _)]; rw [add_comm] at hd
    rw [pow_succ]; rw [pow_mul]; rw [hd]; rw [add_pow]; rw [Finset.sum_range_succ']; rw [pow_zero]; rw [one_mul]; rw [one_pow]; rw [one_mul]; rw [Nat.choose_zero_right]; rw [Nat.cast_one]
    refine Nat.ModEq.add_right 1 (Nat.modEq_zero_iff_dvd.mpr ?_)
    simp_rw [one_pow, mul_one, pow_succ', mul_assoc, ← Finset.mul_sum]
    refine mul_dvd_mul_left (p ^ m) (dvd_mul_of_dvd_right (Finset.dvd_sum fun k hk => ?_) d)
    cases m
    · rw [pow_zero, pow_one, one_mul, add_comm, add_left_inj] at hd
      cases k <;> simp [← hd, mul_assoc, pow_succ']
    · cases k <;> simp [mul_assoc, pow_succ']

/--
theorem `ZMod.eq_one_or_isUnit_sub_one` / 定理 `ZMod.eq_one_or_isUnit_sub_one`

English:
theorem ZMod.eq_one_or_isUnit_sub_one
  statement: {n p k : Nat} [Fact p.Prime] (hn : n = p ^ k) (a : ZMod n)
  proof: by
  rcases eq_or_ne n 0 with rfl | hn0
  · exact Or.inl (orderOf_eq_one_iff.mp ((orderOf a).coprime_zero_right.mp ha))
  rcases eq_or_ne a 0 with rfl | ha0
  · exact Or.inr (zero_sub (1 : ZMod n) ▸ isUnit_neg_one)
  have : NeZero n := ⟨hn0⟩
  obtain ⟨a, rfl⟩ := ZMod.natCast_zmod_surjective a
  rw [

中文:
定理 ZMod.eq_one_or_isUnit_sub_one
  结论: {n p k : 自然数} [Fact p.素] (hn : n = p ^ k) (a : ZMod n)
  证明: by
  rcases eq_or_ne n 0 with rfl | hn0
  · exact Or.inl (orderOf_eq_one_iff.mp ((orderOf a).coprime_zero_right.mp ha))
  rcases eq_or_ne a 0 with rfl | ha0
  · exact Or.inr (zero_sub (1 : ZMod n) ▸ isUnit_neg_one)
  have : NeZero n := ⟨hn0⟩
  obtain ⟨a, rfl⟩ := ZMod.natCast_zmod_surjective a
  rw [

Depends on / 依赖: Nat.cast_one, Nat.cast_pow, NeZero, Or.inl, Or.inr, ZMod.natCast_eq_natCast_iff, ZMod.natCast_zmod_surjective, cast_one, cast_pow, coprime_zero_right, coprime_zero_right.mp, eq_one_of_dvd, eq_or_ne, ha.eq_one_of_dvd, isUnit_neg_one, natCast_eq_natCast_iff, natCast_zmod_surjective, or_iff_not_imp_right, orderOf, orderOf_dvd_iff_pow_eq_one
-/
theorem ZMod.eq_one_or_isUnit_sub_one {n p k : Nat} [Fact p.Prime] (hn : n = p ^ k) (a : ZMod n)
    (ha : (orderOf a).Coprime n) : a = 1 ∨ IsUnit (a - 1) := by
  rcases eq_or_ne n 0 with rfl | hn0
  · exact Or.inl (orderOf_eq_one_iff.mp ((orderOf a).coprime_zero_right.mp ha))
  rcases eq_or_ne a 0 with rfl | ha0
  · exact Or.inr (zero_sub (1 : ZMod n) ▸ isUnit_neg_one)
  have : NeZero n := ⟨hn0⟩
  obtain ⟨a, rfl⟩ := ZMod.natCast_zmod_surjective a
  rw [← orderOf_eq_one_iff]; rw [or_iff_not_imp_right]
  refine fun h => ha.eq_one_of_dvd ?_
  rw [orderOf_dvd_iff_pow_eq_one]; rw [← Nat.cast_pow]; rw [← Nat.cast_one]; rw [ZMod.natCast_eq_natCast_iff]; rw [hn]
  replace ha0 : 1 <= a := by
    contrapose! ha0
    rw [Nat.lt_one_iff.mp ha0]; rw [Nat.cast_zero]
  rw [← Nat.cast_one]; rw [← Nat.cast_sub ha0]; rw [ZMod.isUnit_iff_coprime]; rw [hn] at h
  obtain ⟨b, hb⟩ := not_imp_comm.mp (Nat.Prime.coprime_pow_of_not_dvd Fact.out) h
  rw [tsub_eq_iff_eq_add_of_le ha0]; rw [add_comm] at hb
  exact hb ▸ pow_pow_modEq_one p k b

section prime_subfield

variable {F : Type*} [Field F]

/--
theorem `mem_bot_iff_intCast` / 定理 `mem_bot_iff_intCast`

English:
theorem mem_bot_iff_intCast
  given: (p : Nat) [Fact p.Prime] (K) [DivisionRing K] [CharP K p] {x : K}
  proof: by
  simp [← fieldRange_castHom_eq_bot p, ZMod.intCast_surjective.exists]

中文:
定理 mem_bot_iff_intCast
  条件: (p : 自然数) [Fact p.素] (K) [除环 K] [特征p K p] {x : K}
  证明: by
  simp [← fieldRange_castHom_eq_bot p, ZMod.intCast_surjective.exists]

Depends on / 依赖: ZMod.intCast_surjective.exists, fieldRange_castHom_eq_bot, intCast_surjective
-/
theorem mem_bot_iff_intCast (p : Nat) [Fact p.Prime] (K) [DivisionRing K] [CharP K p] {x : K} :
    x in (⊥ : Subfield K) ↔ exists n : Int, n = x := by
  simp [← fieldRange_castHom_eq_bot p, ZMod.intCast_surjective.exists]

variable (F) (p : Nat) [Fact p.Prime] [CharP F p]

/--
theorem `Subfield.card_bot` / 定理 `Subfield.card_bot`

English:
theorem Subfield.card_bot
  statement: Nat.card (⊥ : Subfield F) = p
  proof: by
  rw [← fieldRange_castHom_eq_bot p]; rw [← Nat.card_eq_of_bijective _ (RingHom.rangeRestrictField_bijective _)]; rw [Nat.card_zmod]

中文:
定理 子域.card_bot
  结论: 自然数.card (⊥ : 子域 F) = p
  证明: by
  rw [← fieldRange_castHom_eq_bot p]; rw [← Nat.card_eq_of_bijective _ (RingHom.rangeRestrictField_bijective _)]; rw [Nat.card_zmod]

Depends on / 依赖: Nat.card_eq_of_bijective, Nat.card_zmod, RingHom, RingHom.rangeRestrictField_bijective, card_eq_of_bijective, card_zmod, fieldRange_castHom_eq_bot, rangeRestrictField_bijective
-/
theorem Subfield.card_bot : Nat.card (⊥ : Subfield F) = p := by
  rw [← fieldRange_castHom_eq_bot p]; rw [← Nat.card_eq_of_bijective _ (RingHom.rangeRestrictField_bijective _)]; rw [Nat.card_zmod]

/-- The prime subfield is finite. -/
@[instance_reducible]
/--
Definition of `Subfield.fintypeBot` / `Subfield.fintypeBot` 的定义

English:
definition Subfield.fintypeBot
  signature: : Fintype (⊥ : Subfield F)
  body: Fintype.subtype (univ.map ⟨_, (ZMod.castHom (m := p) dvd_rfl F).injective⟩)
    fun _ => by simp_rw [Finset.mem_map, mem_univ, true_and, ← fieldRange_castHom_eq_bot p]; rfl

中文:
定义 子域.fintypeBot
  签名: : 有限类型 (⊥ : 子域 F)
  定义体: Fintype.subtype (univ.map ⟨_, (ZMod.castHom (m := p) dvd_rfl F).injective⟩)
    fun _ => by simp_rw [Finset.mem_map, mem_univ, true_and, ← fieldRange_castHom_eq_bot p]; rfl

Depends on / 依赖: Finset, Finset.mem_map, Fintype, Fintype.subtype, ZMod.castHom, castHom, dvd_rfl, fieldRange_castHom_eq_bot, injective, mem_map, mem_univ, simp_rw, subtype, true_and, univ.map
-/
def Subfield.fintypeBot : Fintype (⊥ : Subfield F) :=
  Fintype.subtype (univ.map ⟨_, (ZMod.castHom (m := p) dvd_rfl F).injective⟩)
    fun _ => by simp_rw [Finset.mem_map, mem_univ, true_and, ← fieldRange_castHom_eq_bot p]; rfl

open Polynomial

/--
theorem `Subfield.roots_X_pow_char_sub_X_bot` / 定理 `Subfield.roots_X_pow_char_sub_X_bot`

English:
theorem Subfield.roots_X_pow_char_sub_X_bot
  proof: Subfield.fintypeBot F p
    (X ^ p - X : (⊥ : Subfield F)[X]).roots = Finset.univ.val := by
  let _ := Subfield.fintypeBot F p
  conv_lhs => rw [← card_bot F p, ← Fintype.card_eq_nat_card]
  exact FiniteField.roots_X_pow_card_sub_X _

中文:
定理 子域.roots_X_pow_char_sub_X_bot
  证明: Subfield.fintypeBot F p
    (X ^ p - X : (⊥ : Subfield F)[X]).roots = Finset.univ.val := by
  let _ := Subfield.fintypeBot F p
  conv_lhs => rw [← card_bot F p, ← Fintype.card_eq_nat_card]
  exact FiniteField.roots_X_pow_card_sub_X _

Depends on / 依赖: Subfield, Subfield.fintypeBot, fintypeBot
-/
theorem Subfield.roots_X_pow_char_sub_X_bot :
    letI := Subfield.fintypeBot F p
    (X ^ p - X : (⊥ : Subfield F)[X]).roots = Finset.univ.val := by
  let _ := Subfield.fintypeBot F p
  conv_lhs => rw [← card_bot F p, ← Fintype.card_eq_nat_card]
  exact FiniteField.roots_X_pow_card_sub_X _

/--
theorem `Subfield.splits_bot` / 定理 `Subfield.splits_bot`

English:
theorem Subfield.splits_bot
  proof: by
  let _ := Subfield.fintypeBot F p
  rw [splits_iff_card_roots]; rw [roots_X_pow_char_sub_X_bot]; rw [← Finset.card_def]; rw [Finset.card_univ]; rw [FiniteField.X_pow_card_sub_X_natDegree_eq _ (Fact.out (p := p.Prime)).one_lt]; rw [Fintype.card_eq_nat_card]; rw [card_bot F p]

中文:
定理 子域.splits_bot
  证明: by
  let _ := Subfield.fintypeBot F p
  rw [splits_iff_card_roots]; rw [roots_X_pow_char_sub_X_bot]; rw [← Finset.card_def]; rw [Finset.card_univ]; rw [FiniteField.X_pow_card_sub_X_natDegree_eq _ (Fact.out (p := p.Prime)).one_lt]; rw [Fintype.card_eq_nat_card]; rw [card_bot F p]

Depends on / 依赖: Fact.out, FiniteField, FiniteField.X_pow_card_sub_X_natDegree_eq, Finset, Finset.card_def, Finset.card_univ, Fintype, Fintype.card_eq_nat_card, Subfield, Subfield.fintypeBot, X_pow_card_sub_X_natDegree_eq, card_bot, card_def, card_eq_nat_card, card_univ, fintypeBot, one_lt, p.Prime, roots_X_pow_char_sub_X_bot, splits_iff_card_roots
-/
theorem Subfield.splits_bot :
    Splits (X ^ p - X : (⊥ : Subfield F)[X]) := by
  let _ := Subfield.fintypeBot F p
  rw [splits_iff_card_roots]; rw [roots_X_pow_char_sub_X_bot]; rw [← Finset.card_def]; rw [Finset.card_univ]; rw [FiniteField.X_pow_card_sub_X_natDegree_eq _ (Fact.out (p := p.Prime)).one_lt]; rw [Fintype.card_eq_nat_card]; rw [card_bot F p]

/--
theorem `Subfield.mem_bot_iff_pow_eq_self` / 定理 `Subfield.mem_bot_iff_pow_eq_self`

English:
theorem Subfield.mem_bot_iff_pow_eq_self
  given: {x : F}
  statement: x in (⊥ : Subfield F) ↔ x ^ p = x
  proof: by
  have := roots_X_pow_char_sub_X_bot F p ▸
      (splits_bot F p).roots_map (Subfield.subtype _) ▸ Multiset.mem_map (b := x)
  simpa [sub_eq_zero, iff_comm, FiniteField.X_pow_card_sub_X_ne_zero F (Fact.out : p.Prime).one_lt]

中文:
定理 子域.mem_bot_iff_pow_eq_self
  条件: {x : F}
  结论: x in (⊥ : 子域 F) ↔ x ^ p = x
  证明: by
  have := roots_X_pow_char_sub_X_bot F p ▸
      (splits_bot F p).roots_map (Subfield.subtype _) ▸ Multiset.mem_map (b := x)
  simpa [sub_eq_zero, iff_comm, FiniteField.X_pow_card_sub_X_ne_zero F (Fact.out : p.Prime).one_lt]

Depends on / 依赖: Fact.out, FiniteField, FiniteField.X_pow_card_sub_X_ne_zero, Multiset, Multiset.mem_map, Subfield, Subfield.subtype, X_pow_card_sub_X_ne_zero, iff_comm, mem_map, one_lt, p.Prime, roots_X_pow_char_sub_X_bot, roots_map, splits_bot, sub_eq_zero, subtype
-/
theorem Subfield.mem_bot_iff_pow_eq_self {x : F} : x in (⊥ : Subfield F) ↔ x ^ p = x := by
  have := roots_X_pow_char_sub_X_bot F p ▸
      (splits_bot F p).roots_map (Subfield.subtype _) ▸ Multiset.mem_map (b := x)
  simpa [sub_eq_zero, iff_comm, FiniteField.X_pow_card_sub_X_ne_zero F (Fact.out : p.Prime).one_lt]

end prime_subfield

namespace FiniteField

variable {F : Type*} [Field F]

section Finite

variable [Finite F]

/--
theorem `isSquare_of_char_two` / 定理 `isSquare_of_char_two`

English:
theorem isSquare_of_char_two
  given: (hF : ringChar F = 2) (a : F)
  statement: IsSquare a
  proof: have : CharP F 2 := ringChar.of_eq hF
  isSquare_of_charTwo' a

中文:
定理 isSquare_of_char_two
  条件: (hF : ringChar F = 2) (a : F)
  结论: IsSquare a
  证明: have : CharP F 2 := ringChar.of_eq hF
  isSquare_of_charTwo' a

Depends on / 依赖: isSquare_of_charTwo, of_eq, ringChar, ringChar.of_eq
-/
theorem isSquare_of_char_two (hF : ringChar F = 2) (a : F) : IsSquare a :=
  have : CharP F 2 := ringChar.of_eq hF
  isSquare_of_charTwo' a

/--
theorem `exists_nonsquare` / 定理 `exists_nonsquare`

English:
theorem exists_nonsquare
  given: (hF : ringChar F != 2)
  statement: exists a : F, ¬IsSquare a
  proof: by
  -- Idea: the squaring map on `F` is not injective, hence not surjective
  have h : ¬Function.Injective fun x : F => x * x := fun h =>
h.ne (Ring.neg_one_ne_one_of_char_ne_two hF) by simp
  simpa [Finite.injective_iff_surjective, Function.Surjective, IsSquare, eq_comm] using h

中文:
定理 存在_nonsquare
  条件: (hF : ringChar F != 2)
  结论: 存在 a : F, ¬IsSquare a
  证明: by
  -- Idea: the squaring map on `F` is not injective, hence not surjective
  have h : ¬Function.Injective fun x : F => x * x := fun h =>
h.ne (Ring.neg_one_ne_one_of_char_ne_two hF) by simp
  simpa [Finite.injective_iff_surjective, Function.Surjective, IsSquare, eq_comm] using h
-/
theorem exists_nonsquare (hF : ringChar F != 2) : exists a : F, ¬IsSquare a := by
  -- Idea: the squaring map on `F` is not injective, hence not surjective
  have h : ¬Function.Injective fun x : F => x * x := fun h =>
h.ne (Ring.neg_one_ne_one_of_char_ne_two hF) by simp
  simpa [Finite.injective_iff_surjective, Function.Surjective, IsSquare, eq_comm] using h

end Finite

variable [Fintype F]

/--
theorem `even_card_iff_char_two` / 定理 `even_card_iff_char_two`

English:
theorem even_card_iff_char_two
  statement: ringChar F = 2 ↔ Fintype.card F % 2 = 0
  proof: by
  rcases FiniteField.card F (ringChar F) with ⟨n, hp, h⟩
  rw [h]; rw [← Nat.even_iff]; rw [Nat.even_pow]; rw [hp.even_iff]
  simp

中文:
定理 even_card_iff_char_two
  结论: ringChar F = 2 ↔ 有限类型.card F % 2 = 0
  证明: by
  rcases FiniteField.card F (ringChar F) with ⟨n, hp, h⟩
  rw [h]; rw [← Nat.even_iff]; rw [Nat.even_pow]; rw [hp.even_iff]
  simp

Depends on / 依赖: FiniteField, FiniteField.card, Nat.even_iff, Nat.even_pow, even_iff, even_pow, hp.even_iff, ringChar
-/
theorem even_card_iff_char_two : ringChar F = 2 ↔ Fintype.card F % 2 = 0 := by
  rcases FiniteField.card F (ringChar F) with ⟨n, hp, h⟩
  rw [h]; rw [← Nat.even_iff]; rw [Nat.even_pow]; rw [hp.even_iff]
  simp

/--
theorem `even_card_of_char_two` / 定理 `even_card_of_char_two`

English:
theorem even_card_of_char_two
  given: (hF : ringChar F = 2)
  statement: Fintype.card F % 2 = 0
  proof: even_card_iff_char_two.mp hF

中文:
定理 even_card_of_char_two
  条件: (hF : ringChar F = 2)
  结论: 有限类型.card F % 2 = 0
  证明: even_card_iff_char_two.mp hF

Depends on / 依赖: even_card_iff_char_two, even_card_iff_char_two.mp
-/
theorem even_card_of_char_two (hF : ringChar F = 2) : Fintype.card F % 2 = 0 :=
  even_card_iff_char_two.mp hF

/--
theorem `odd_card_of_char_ne_two` / 定理 `odd_card_of_char_ne_two`

English:
theorem odd_card_of_char_ne_two
  given: (hF : ringChar F != 2)
  statement: Fintype.card F % 2 = 1
  proof: Nat.mod_two_ne_zero.mp (mt even_card_iff_char_two.mpr hF)

中文:
定理 odd_card_of_char_ne_two
  条件: (hF : ringChar F != 2)
  结论: 有限类型.card F % 2 = 1
  证明: Nat.mod_two_ne_zero.mp (mt even_card_iff_char_two.mpr hF)

Depends on / 依赖: Nat.mod_two_ne_zero.mp, even_card_iff_char_two, even_card_iff_char_two.mpr, mod_two_ne_zero
-/
theorem odd_card_of_char_ne_two (hF : ringChar F != 2) : Fintype.card F % 2 = 1 :=
  Nat.mod_two_ne_zero.mp (mt even_card_iff_char_two.mpr hF)

/--
theorem `pow_dichotomy` / 定理 `pow_dichotomy`

English:
theorem pow_dichotomy
  given: (hF : ringChar F != 2) {a : F} (ha : a != 0)
  proof: by
  have h₁ := FiniteField.pow_card_sub_one_eq_one a ha
  rw [← Nat.two_mul_odd_div_two (FiniteField.odd_card_of_char_ne_two hF)]; rw [mul_comm]; rw [pow_mul]; rw [pow_two] at h₁
  exact mul_self_eq_one_iff.mp h₁

中文:
定理 pow_dichotomy
  条件: (hF : ringChar F != 2) {a : F} (ha : a != 0)
  证明: by
  have h₁ := FiniteField.pow_card_sub_one_eq_one a ha
  rw [← Nat.two_mul_odd_div_two (FiniteField.odd_card_of_char_ne_two hF)]; rw [mul_comm]; rw [pow_mul]; rw [pow_two] at h₁
  exact mul_self_eq_one_iff.mp h₁

Depends on / 依赖: FiniteField, FiniteField.odd_card_of_char_ne_two, FiniteField.pow_card_sub_one_eq_one, Nat.two_mul_odd_div_two, mul_comm, mul_self_eq_one_iff, mul_self_eq_one_iff.mp, odd_card_of_char_ne_two, pow_card_sub_one_eq_one, pow_mul, pow_two, two_mul_odd_div_two
-/
theorem pow_dichotomy (hF : ringChar F != 2) {a : F} (ha : a != 0) :
    a ^ (Fintype.card F / 2) = 1 ∨ a ^ (Fintype.card F / 2) = -1 := by
  have h₁ := FiniteField.pow_card_sub_one_eq_one a ha
  rw [← Nat.two_mul_odd_div_two (FiniteField.odd_card_of_char_ne_two hF)]; rw [mul_comm]; rw [pow_mul]; rw [pow_two] at h₁
  exact mul_self_eq_one_iff.mp h₁

/--
theorem `unit_isSquare_iff` / 定理 `unit_isSquare_iff`

English:
theorem unit_isSquare_iff
  given: (hF : ringChar F != 2) (a : Fˣ)
  proof: by
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := Fˣ)
  obtain ⟨n, hn⟩ : a in Submonoid.powers g := by rw [mem_powers_iff_mem_zpowers]; apply hg
  have hodd := Nat.two_mul_odd_div_two (FiniteField.odd_card_of_char_ne_two hF)
  constructor
  · rintro ⟨y, rfl⟩
    rw [← pow_two]; rw [← pow_mul]; 

中文:
定理 unit_isSquare_iff
  条件: (hF : ringChar F != 2) (a : Fˣ)
  证明: by
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := Fˣ)
  obtain ⟨n, hn⟩ : a in Submonoid.powers g := by rw [mem_powers_iff_mem_zpowers]; apply hg
  have hodd := Nat.two_mul_odd_div_two (FiniteField.odd_card_of_char_ne_two hF)
  constructor
  · rintro ⟨y, rfl⟩
    rw [← pow_two]; rw [← pow_mul]; 

Depends on / 依赖: FiniteField, FiniteField.odd_card_of_char_ne_two, FiniteField.pow_card_sub_one_eq_one, IsCyclic, IsCyclic.exists_generator, Nat.card_eq_fintype_card, Nat.two_mul_odd_div_two, Submonoid, Submonoid.powers, Units.ne_zero, Units.val, Units.val_injective, apply_fun, card_eq_fintype_card, exists_generator, mem_powers_iff_mem_zpowers, ne_zero, odd_card_of_char_ne_two, pow_card_sub_one_eq_one, pow_mul
-/
theorem unit_isSquare_iff (hF : ringChar F != 2) (a : Fˣ) :
    IsSquare a ↔ a ^ (Fintype.card F / 2) = 1 := by
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := Fˣ)
  obtain ⟨n, hn⟩ : a in Submonoid.powers g := by rw [mem_powers_iff_mem_zpowers]; apply hg
  have hodd := Nat.two_mul_odd_div_two (FiniteField.odd_card_of_char_ne_two hF)
  constructor
  · rintro ⟨y, rfl⟩
    rw [← pow_two]; rw [← pow_mul]; rw [hodd]
    apply_fun Units.val using Units.val_injective
    push_cast
    exact FiniteField.pow_card_sub_one_eq_one (y : F) (Units.ne_zero y)
  · subst a; intro h
    rw [← Nat.card_eq_fintype_card] at hodd h
    have key : 2 * (Nat.card F / 2) ∣ n * (Nat.card F / 2) := by
      rw [← pow_mul] at h
      rw [hodd]; rw [← Nat.card_units]; rw [← orderOf_eq_card_of_forall_mem_zpowers hg]
      apply orderOf_dvd_of_pow_eq_one h
    have : 0 < Nat.card F / 2 := Nat.div_pos Finite.one_lt_card (by simp)
    obtain ⟨m, rfl⟩ := Nat.dvd_of_mul_dvd_mul_right this key
    refine ⟨g ^ m, ?_⟩
    dsimp
    rw [mul_comm]; rw [pow_mul]; rw [pow_two]

/--
theorem `isSquare_iff` / 定理 `isSquare_iff`

English:
theorem isSquare_iff
  given: (hF : ringChar F != 2) {a : F} (ha : a != 0)
  proof: by
  apply
    (iff_congr _ (by simp [Units.ext_iff])).mp (FiniteField.unit_isSquare_iff hF (Units.mk0 a ha))
  simp only [IsSquare, Units.ext_iff, Units.val_mk0, Units.val_mul]
  constructor
  · rintro ⟨y, hy⟩; exact ⟨y, hy⟩
  · rintro ⟨y, rfl⟩
    have hy : y != 0 := by rintro rfl; simp at ha
    

中文:
定理 isSquare_iff
  条件: (hF : ringChar F != 2) {a : F} (ha : a != 0)
  证明: by
  apply
    (iff_congr _ (by simp [Units.ext_iff])).mp (FiniteField.unit_isSquare_iff hF (Units.mk0 a ha))
  simp only [IsSquare, Units.ext_iff, Units.val_mk0, Units.val_mul]
  constructor
  · rintro ⟨y, hy⟩; exact ⟨y, hy⟩
  · rintro ⟨y, rfl⟩
    have hy : y != 0 := by rintro rfl; simp at ha
    

Depends on / 依赖: FiniteField, FiniteField.unit_isSquare_iff, IsSquare, Units.ext_iff, Units.mk0, Units.val_mk0, Units.val_mul, ext_iff, iff_congr, unit_isSquare_iff, val_mk0, val_mul
-/
theorem isSquare_iff (hF : ringChar F != 2) {a : F} (ha : a != 0) :
    IsSquare a ↔ a ^ (Fintype.card F / 2) = 1 := by
  apply
    (iff_congr _ (by simp [Units.ext_iff])).mp (FiniteField.unit_isSquare_iff hF (Units.mk0 a ha))
  simp only [IsSquare, Units.ext_iff, Units.val_mk0, Units.val_mul]
  constructor
  · rintro ⟨y, hy⟩; exact ⟨y, hy⟩
  · rintro ⟨y, rfl⟩
    have hy : y != 0 := by rintro rfl; simp at ha
    refine ⟨Units.mk0 y hy, ?_⟩; simp

end FiniteField
