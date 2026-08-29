/-
Copyright (c) 2020 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta, Daniel Weber
-/
module

public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Data.Finset.Density

/-!
# Results about big operators with values in a field
-/

public section

open Fintype

variable {ι K : Type*} [DivisionSemiring K]

/--
lemma `Multiset.sum_map_div` / 引理 `Multiset.sum_map_div`

English:
lemma Multiset.sum_map_div
  given: (s : Multiset ι) (f : ι -> K) (a : K)
  proof: by
  simp only [div_eq_mul_inv, Multiset.sum_map_mul_right]

中文:
引理 Multiset.sum_map_div
  条件: (s : Multiset ι) (f : ι -> K) (a : K)
  证明: by
  simp only [div_eq_mul_inv, Multiset.sum_map_mul_right]

Depends on / 依赖: Multiset, Multiset.sum_map_mul_right, div_eq_mul_inv, sum_map_mul_right
-/
lemma Multiset.sum_map_div (s : Multiset ι) (f : ι -> K) (a : K) :
    (s.map (fun x => f x / a)).sum = (s.map f).sum / a := by
  simp only [div_eq_mul_inv, Multiset.sum_map_mul_right]

/--
lemma `Finset.sum_div` / 引理 `Finset.sum_div`

English:
lemma Finset.sum_div
  given: (s : Finset ι) (f : ι -> K) (a : K)
  proof: by simp only [div_eq_mul_inv, sum_mul]

中文:
引理 Finset.sum_div
  条件: (s : Finset ι) (f : ι -> K) (a : K)
  证明: by simp only [div_eq_mul_inv, sum_mul]

Depends on / 依赖: div_eq_mul_inv, sum_mul
-/
lemma Finset.sum_div (s : Finset ι) (f : ι -> K) (a : K) :
    (∑ i in s, f i) / a = ∑ i in s, f i / a := by simp only [div_eq_mul_inv, sum_mul]

-- TODO: Move these to `Algebra.BigOperators.Group.Finset.Basic`, next to the corresponding `card`
-- lemmas, once `Finset.dens` doesn't depend on `Field` anymore.
namespace Finset
variable {α β : Type*} [Fintype β]

@[simp]
/--
lemma `dens_disjiUnion` / 引理 `dens_disjiUnion`

English:
lemma dens_disjiUnion
  given: (s : Finset α) (t : α -> Finset β) (h)
  proof: by
  simp [dens, sum_div]

中文:
引理 dens_disjiUnion
  条件: (s : Finset α) (t : α -> Finset β) (h)
  证明: by
  simp [dens, sum_div]

Depends on / 依赖: sum_div
-/
lemma dens_disjiUnion (s : Finset α) (t : α -> Finset β) (h) :
    (s.disjiUnion t h).dens = ∑ a in s, (t a).dens := by
  simp [dens, sum_div]

variable {s : Finset α} {t : α -> Finset β}

/--
lemma `dens_biUnion` / 引理 `dens_biUnion`

English:
lemma dens_biUnion
  given: [DecidableEq β] (h : (s : Set α).PairwiseDisjoint t)
  proof: by
  simp [dens, card_biUnion h, sum_div]

中文:
引理 dens_biUnion
  条件: [DecidableEq β] (h : (s : Set α).PairwiseDisjoint t)
  证明: by
  simp [dens, card_biUnion h, sum_div]

Depends on / 依赖: card_biUnion, sum_div
-/
lemma dens_biUnion [DecidableEq β] (h : (s : Set α).PairwiseDisjoint t) :
    (s.biUnion t).dens = ∑ u in s, (t u).dens := by
  simp [dens, card_biUnion h, sum_div]

/--
lemma `dens_biUnion_le` / 引理 `dens_biUnion_le`

English:
lemma dens_biUnion_le
  given: [DecidableEq β]
  statement: (s.biUnion t).dens <= ∑ a in s, (t a).dens
  proof: by
  simp only [dens, ← sum_div]
  gcongr
  exact mod_cast card_biUnion_le

中文:
引理 dens_biUnion_le
  条件: [DecidableEq β]
  结论: (s.biUnion t).dens <= ∑ a in s, (t a).dens
  证明: by
  simp only [dens, ← sum_div]
  gcongr
  exact mod_cast card_biUnion_le

Depends on / 依赖: card_biUnion_le, mod_cast, sum_div
-/
lemma dens_biUnion_le [DecidableEq β] : (s.biUnion t).dens <= ∑ a in s, (t a).dens := by
  simp only [dens, ← sum_div]
  gcongr
  exact mod_cast card_biUnion_le

/--
lemma `dens_eq_sum_dens_fiberwise` / 引理 `dens_eq_sum_dens_fiberwise`

English:
lemma dens_eq_sum_dens_fiberwise
  statement: [DecidableEq α] {f : β -> α} {t : Finset β}
  proof: by
  simp [dens, ← sum_div, card_eq_sum_card_fiberwise h]

中文:
引理 dens_eq_sum_dens_fiberwise
  结论: [DecidableEq α] {f : β -> α} {t : Finset β}
  证明: by
  simp [dens, ← sum_div, card_eq_sum_card_fiberwise h]

Depends on / 依赖: card_eq_sum_card_fiberwise, sum_div
-/
lemma dens_eq_sum_dens_fiberwise [DecidableEq α] {f : β -> α} {t : Finset β}
    (h : (t : Set β).MapsTo f s) : t.dens = ∑ a in s, {b in t | f b = a}.dens := by
  simp [dens, ← sum_div, card_eq_sum_card_fiberwise h]

/--
lemma `dens_eq_sum_dens_image` / 引理 `dens_eq_sum_dens_image`

English:
lemma dens_eq_sum_dens_image
  given: [DecidableEq α] (f : β -> α) (t : Finset β)
  proof: dens_eq_sum_dens_fiberwise fun _ => mem_image_of_mem _

中文:
引理 dens_eq_sum_dens_image
  条件: [DecidableEq α] (f : β -> α) (t : Finset β)
  证明: dens_eq_sum_dens_fiberwise fun _ => mem_image_of_mem _

Depends on / 依赖: dens_eq_sum_dens_fiberwise, mem_image_of_mem
-/
lemma dens_eq_sum_dens_image [DecidableEq α] (f : β -> α) (t : Finset β) :
    t.dens = ∑ a in t.image f, {b in t | f b = a}.dens :=
  dens_eq_sum_dens_fiberwise fun _ => mem_image_of_mem _

end Finset
