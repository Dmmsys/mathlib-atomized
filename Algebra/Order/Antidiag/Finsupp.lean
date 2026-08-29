/-
Copyright (c) 2023 Antoine Chambert-Loir and María Inés de Frutos-Fernández. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Antoine Chambert-Loir, María Inés de Frutos-Fernández, Eric Wieser, Bhavik Mehta,
  Yaël Dillies
-/
module

public import Mathlib.Algebra.BigOperators.Finsupp.Basic
public import Mathlib.Algebra.Order.Antidiag.Pi

/-!
# Antidiagonal of finitely supported functions as finsets

This file defines the finset of finitely functions summing to a specific value on a finset. Such
finsets should be thought of as the "antidiagonals" in the space of finitely supported functions.

Precisely, for a commutative monoid `μ` with antidiagonals (see `Finset.HasAntidiagonal`),
`Finset.finsuppAntidiag s n` is the finset of all finitely supported functions `f : ι →₀ μ` with
support contained in `s` and such that the sum of its values equals `n : μ`.

We define it using `Finset.piAntidiag s n`, the corresponding antidiagonal in `ι → μ`.

## Main declarations

* `Finset.finsuppAntidiag s n`: Finset of all finitely supported functions `f : ι →₀ μ` with support
  contained in `s` and such that the sum of its values equals `n : μ`.

-/

@[expose] public section

assert_not_exists Field

open Finsupp Function

variable {ι μ μ' : Type*}

namespace Finset
section AddCommMonoid
variable [DecidableEq ι] [AddCommMonoid μ] [HasAntidiagonal μ] [DecidableEq μ] {s : Finset ι}
  {n : μ} {f : ι ->₀ μ}

/--
Definition of `finsuppAntidiag` / `finsuppAntidiag` 的定义

English:
definition finsuppAntidiag
  signature: (s : Finset ι) (n : μ)
  body: (piAntidiag s n).attach.map ⟨fun f => ⟨s.filter (f.1 · != 0), f.1, by
    simpa using (mem_piAntidiag.1 f.2).2⟩, fun _ _ hfg => Subtype.ext (congr_arg (⇑) hfg)⟩

中文:
定义 finsuppAntidiag
  签名: (s : 有限集 ι) (n : μ)
  定义体: (piAntidiag s n).attach.map ⟨fun f => ⟨s.filter (f.1 · != 0), f.1, by
    simpa using (mem_piAntidiag.1 f.2).2⟩, fun _ _ hfg => Subtype.ext (congr_arg (⇑) hfg)⟩

Depends on / 依赖: Subtype, Subtype.ext, attach, attach.map, congr_arg, filter, mem_piAntidiag, piAntidiag, s.filter
-/
def finsuppAntidiag (s : Finset ι) (n : μ) : Finset (ι ->₀ μ) :=
  (piAntidiag s n).attach.map ⟨fun f => ⟨s.filter (f.1 · != 0), f.1, by
    simpa using (mem_piAntidiag.1 f.2).2⟩, fun _ _ hfg => Subtype.ext (congr_arg (⇑) hfg)⟩

set_option backward.isDefEq.respectTransparency false in
/--
lemma `mem_finsuppAntidiag` / 引理 `mem_finsuppAntidiag`

English:
lemma mem_finsuppAntidiag
  statement: f in finsuppAntidiag s n ↔ s.sum f = n ∧ f.support subseteq s
  proof: by
  simp [finsuppAntidiag, ← DFunLike.coe_fn_eq, subset_iff]

中文:
引理 mem_finsuppAntidiag
  结论: f in finsuppAntidiag s n ↔ s.求和 f = n ∧ f.support subseteq s
  证明: by
  simp [finsuppAntidiag, ← DFunLike.coe_fn_eq, subset_iff]
-/
@[simp] lemma mem_finsuppAntidiag : f in finsuppAntidiag s n ↔ s.sum f = n ∧ f.support subseteq s := by
  simp [finsuppAntidiag, ← DFunLike.coe_fn_eq, subset_iff]

/--
lemma `mem_finsuppAntidiag'` / 引理 `mem_finsuppAntidiag'`

English:
lemma mem_finsuppAntidiag'
  proof: by
  simp only [mem_finsuppAntidiag, and_congr_left_iff]
  rintro hf
  rw [sum_of_support_subset (N := μ) f hf (fun _ x => x) fun _ _ => rfl]

中文:
引理 mem_finsuppAntidiag'
  证明: by
  simp only [mem_finsuppAntidiag, and_congr_left_iff]
  rintro hf
  rw [sum_of_support_subset (N := μ) f hf (fun _ x => x) fun _ _ => rfl]

Depends on / 依赖: and_congr_left_iff, mem_finsuppAntidiag, sum_of_support_subset
-/
lemma mem_finsuppAntidiag' :
    f in finsuppAntidiag s n ↔ f.sum (fun _ x => x) = n ∧ f.support subseteq s := by
  simp only [mem_finsuppAntidiag, and_congr_left_iff]
  rintro hf
  rw [sum_of_support_subset (N := μ) f hf (fun _ x => x) fun _ _ => rfl]

/--
lemma `finsuppAntidiag_empty_zero` / 引理 `finsuppAntidiag_empty_zero`

English:
lemma finsuppAntidiag_empty_zero
  statement: finsuppAntidiag (∅ : Finset ι) (0 : μ) = {0}
  proof: by
  ext f; simp

中文:
引理 finsuppAntidiag_empty_zero
  结论: finsuppAntidiag (∅ : 有限集 ι) (0 : μ) = {0}
  证明: by
  ext f; simp
-/
@[simp] lemma finsuppAntidiag_empty_zero : finsuppAntidiag (∅ : Finset ι) (0 : μ) = {0} := by
  ext f; simp

/--
lemma `finsuppAntidiag_empty_of_ne_zero` / 引理 `finsuppAntidiag_empty_of_ne_zero`

English:
lemma finsuppAntidiag_empty_of_ne_zero
  given: (hn : n != 0)
  proof: eq_empty_of_forall_notMem (by simp [hn.symm])

中文:
引理 finsuppAntidiag_empty_of_ne_zero
  条件: (hn : n != 0)
  证明: eq_empty_of_forall_notMem (by simp [hn.symm])
-/
@[simp] lemma finsuppAntidiag_empty_of_ne_zero (hn : n != 0) :
    finsuppAntidiag (∅ : Finset ι) n = ∅ :=
  eq_empty_of_forall_notMem (by simp [hn.symm])

/--
lemma `finsuppAntidiag_empty` / 引理 `finsuppAntidiag_empty`

English:
lemma finsuppAntidiag_empty
  given: (n : μ)
  proof: by split_ifs with hn <;> simp [*]

中文:
引理 finsuppAntidiag_empty
  条件: (n : μ)
  证明: by split_ifs with hn <;> simp [*]

Depends on / 依赖: split_ifs
-/
lemma finsuppAntidiag_empty (n : μ) :
    finsuppAntidiag (∅ : Finset ι) n = if n = 0 then {0} else ∅ := by split_ifs with hn <;> simp [*]

/--
theorem `mem_finsuppAntidiag_insert` / 定理 `mem_finsuppAntidiag_insert`

English:
theorem mem_finsuppAntidiag_insert
  statement: {a : ι} {s : Finset ι}
  proof: by
  simp only [mem_finsuppAntidiag, mem_antidiagonal, Prod.exists, sum_insert h]
  constructor
  · rintro ⟨rfl, hsupp⟩
    refine ⟨_, _, rfl, Finsupp.erase a f, ?_, ?_, ?_⟩
    · rw [update_erase_eq_update, Finsupp.update_self]
    · apply sum_congr rfl
      intro x hx
      rw [Finsupp.erase_ne (ne_of_mem_of_not_mem hx h)]
    · rwa [support_erase, ← subset_insert_iff]
  · rintro ⟨n1, n2, rfl, g, rfl, rfl, hgsupp⟩
    refine ⟨?_, (support_update_subset _ _).trans (insert_subset_insert a hgsupp)⟩
    simp only [coe_update]
    apply congr_arg₂
    · rw [Function.update_self]
    · apply sum_congr rfl
      intro x hx
      rw [update_of_ne (ne_of_mem_of_not_mem hx h) n1 ⇑g]

中文:
定理 mem_finsuppAntidiag_insert
  结论: {a : ι} {s : 有限集 ι}
  证明: by
  simp only [mem_finsuppAntidiag, mem_antidiagonal, Prod.exists, sum_insert h]
  constructor
  · rintro ⟨rfl, hsupp⟩
    refine ⟨_, _, rfl, Finsupp.erase a f, ?_, ?_, ?_⟩
    · rw [update_erase_eq_update, Finsupp.update_self]
    · apply sum_congr rfl
      intro x hx
      rw [Finsupp.erase_ne (ne_of_mem_of_not_mem hx h)]
    · rwa [support_erase, ← subset_insert_iff]
  · rintro ⟨n1, n2, rfl, g, rfl, rfl, hgsupp⟩
    refine ⟨?_, (support_update_subset _ _).trans (insert_subset_insert a hgsupp)⟩
    simp only [coe_update]
    apply congr_arg₂
    · rw [Function.update_self]
    · apply sum_congr rfl
      intro x hx
      rw [update_of_ne (ne_of_mem_of_not_mem hx h) n1 ⇑g]

Depends on / 依赖: Finsupp, Finsupp.erase, Finsupp.erase_ne, Finsupp.update_self, Prod.exists, coe_update, congr_a, erase_ne, hgsupp, insert_subset_insert, mem_antidiagonal, mem_finsuppAntidiag, ne_of_mem_of_not_mem, subset_insert_iff, sum_congr, sum_insert, support_erase, support_update_subset, update_erase_eq_update, update_self
-/
theorem mem_finsuppAntidiag_insert {a : ι} {s : Finset ι}
    (h : a ∉ s) (n : μ) {f : ι ->₀ μ} :
    f in finsuppAntidiag (insert a s) n ↔
      exists m in antidiagonal n, exists (g : ι ->₀ μ),
        f = Finsupp.update g a m.1 ∧ g in finsuppAntidiag s m.2 := by
  simp only [mem_finsuppAntidiag, mem_antidiagonal, Prod.exists, sum_insert h]
  constructor
  · rintro ⟨rfl, hsupp⟩
    refine ⟨_, _, rfl, Finsupp.erase a f, ?_, ?_, ?_⟩
    · rw [update_erase_eq_update, Finsupp.update_self]
    · apply sum_congr rfl
      intro x hx
      rw [Finsupp.erase_ne (ne_of_mem_of_not_mem hx h)]
    · rwa [support_erase, ← subset_insert_iff]
  · rintro ⟨n1, n2, rfl, g, rfl, rfl, hgsupp⟩
    refine ⟨?_, (support_update_subset _ _).trans (insert_subset_insert a hgsupp)⟩
    simp only [coe_update]
    apply congr_arg₂
    · rw [Function.update_self]
    · apply sum_congr rfl
      intro x hx
      rw [update_of_ne (ne_of_mem_of_not_mem hx h) n1 ⇑g]

set_option backward.isDefEq.respectTransparency false in
/--
theorem `finsuppAntidiag_insert` / 定理 `finsuppAntidiag_insert`

English:
theorem finsuppAntidiag_insert
  statement: {a : ι} {s : Finset ι}
  proof: by
  ext f
  rw [mem_finsuppAntidiag_insert h]; rw [mem_biUnion]
  simp_rw [mem_map, mem_attach, true_and, Subtype.exists, Embedding.coeFn_mk, exists_prop, and_comm,
    eq_comm]

@[gcongr]

中文:
定理 finsuppAntidiag_insert
  结论: {a : ι} {s : 有限集 ι}
  证明: by
  ext f
  rw [mem_finsuppAntidiag_insert h]; rw [mem_biUnion]
  simp_rw [mem_map, mem_attach, true_and, Subtype.exists, Embedding.coeFn_mk, exists_prop, and_comm,
    eq_comm]

@[gcongr]

Depends on / 依赖: eq_or_ne
-/
theorem finsuppAntidiag_insert {a : ι} {s : Finset ι}
    (h : a ∉ s) (n : μ) :
    finsuppAntidiag (insert a s) n = (antidiagonal n).biUnion
      (fun p : μ × μ =>
        (finsuppAntidiag s p.snd).attach.map
        ⟨fun f => Finsupp.update f.val a p.fst,
        (fun ⟨f, hf⟩ ⟨g, hg⟩ hfg => Subtype.ext <| by
          simp only [mem_finsuppAntidiag] at hf hg
          simp only [DFunLike.ext_iff] at hfg ⊢
          intro x
          obtain rfl | hx := eq_or_ne x a
          · replace hf := mt (hf.2 ·) h
            replace hg := mt (hg.2 ·) h
            rw [notMem_support_iff.mp hf]; rw [notMem_support_iff.mp hg]
          · simpa only [coe_update, Function.update, dif_neg hx] using hfg x)⟩) := by
  ext f
  rw [mem_finsuppAntidiag_insert h]; rw [mem_biUnion]
  simp_rw [mem_map, mem_attach, true_and, Subtype.exists, Embedding.coeFn_mk, exists_prop, and_comm,
    eq_comm]

@[gcongr]
/--
theorem `finsuppAntidiag_mono` / 定理 `finsuppAntidiag_mono`

English:
theorem finsuppAntidiag_mono
  given: {s t : Finset ι} (h : s subseteq t) (n : μ)
  proof: by
  intro a
  simp_rw [mem_finsuppAntidiag']
  rintro ⟨hsum, hmem⟩
  exact ⟨hsum, hmem.trans h⟩

中文:
定理 finsuppAntidiag_mono
  条件: {s t : 有限集 ι} (h : s subseteq t) (n : μ)
  证明: by
  intro a
  simp_rw [mem_finsuppAntidiag']
  rintro ⟨hsum, hmem⟩
  exact ⟨hsum, hmem.trans h⟩

Depends on / 依赖: hmem.trans, mem_finsuppAntidiag, simp_rw
-/
theorem finsuppAntidiag_mono {s t : Finset ι} (h : s subseteq t) (n : μ) :
    finsuppAntidiag s n subseteq finsuppAntidiag t n := by
  intro a
  simp_rw [mem_finsuppAntidiag']
  rintro ⟨hsum, hmem⟩
  exact ⟨hsum, hmem.trans h⟩

variable [AddCommMonoid μ'] [HasAntidiagonal μ'] [DecidableEq μ']

set_option backward.isDefEq.respectTransparency false in
-- This should work under the assumption that e is an embedding and an AddHom
/--
lemma `mapRange_finsuppAntidiag_subset` / 引理 `mapRange_finsuppAntidiag_subset`

English:
lemma mapRange_finsuppAntidiag_subset
  given: {e : μ ≃+ μ'} {s : Finset ι} {n : μ}
  proof: by
  intro f
  simp only [mem_map, mem_finsuppAntidiag']
  rintro ⟨g, ⟨hsum, hsupp⟩, rfl⟩
  simp only [AddEquiv.toEquiv_eq_coe, mapRange.addEquiv_toEquiv, Equiv.coe_toEmbedding,
    mapRange.equiv_apply, EquivLike.coe_coe]
  constructor
  · rw [sum_mapRange_index (fun _ => rfl), ← hsum, _root_.map_finsuppSum]
  · exact subset_trans (support_mapRange) hsupp

中文:
引理 mapRange_finsuppAntidiag_subset
  条件: {e : μ ≃+ μ'} {s : 有限集 ι} {n : μ}
  证明: by
  intro f
  simp only [mem_map, mem_finsuppAntidiag']
  rintro ⟨g, ⟨hsum, hsupp⟩, rfl⟩
  simp only [AddEquiv.toEquiv_eq_coe, mapRange.addEquiv_toEquiv, Equiv.coe_toEmbedding,
    mapRange.equiv_apply, EquivLike.coe_coe]
  constructor
  · rw [sum_mapRange_index (fun _ => rfl), ← hsum, _root_.map_finsuppSum]
  · exact subset_trans (support_mapRange) hsupp

Depends on / 依赖: AddEquiv, AddEquiv.toEquiv_eq_coe, Equiv.coe_toEmbedding, EquivLike, EquivLike.coe_coe, _root_, _root_.map_finsuppSum, addEquiv_toEquiv, coe_coe, coe_toEmbedding, equiv_apply, mapRange, mapRange.addEquiv_toEquiv, mapRange.equiv_apply, map_finsuppSum, mem_finsuppAntidiag, mem_map, subset_trans, sum_mapRange_index, support_mapRange
-/
lemma mapRange_finsuppAntidiag_subset {e : μ ≃+ μ'} {s : Finset ι} {n : μ} :
    (finsuppAntidiag s n).map (mapRange.addEquiv e).toEmbedding subseteq finsuppAntidiag s (e n) := by
  intro f
  simp only [mem_map, mem_finsuppAntidiag']
  rintro ⟨g, ⟨hsum, hsupp⟩, rfl⟩
  simp only [AddEquiv.toEquiv_eq_coe, mapRange.addEquiv_toEquiv, Equiv.coe_toEmbedding,
    mapRange.equiv_apply, EquivLike.coe_coe]
  constructor
  · rw [sum_mapRange_index (fun _ => rfl), ← hsum, _root_.map_finsuppSum]
  · exact subset_trans (support_mapRange) hsupp

/--
lemma `mapRange_finsuppAntidiag_eq` / 引理 `mapRange_finsuppAntidiag_eq`

English:
lemma mapRange_finsuppAntidiag_eq
  given: {e : μ ≃+ μ'} {s : Finset ι} {n : μ}
  proof: by
  ext f
  constructor
  · apply mapRange_finsuppAntidiag_subset
  · set h := (mapRange.addEquiv e).toEquiv with hh
    intro hf
    have : n = e.symm (e n) := (AddEquiv.eq_symm_apply e).mpr rfl
    rw [mem_map_equiv]; rw [this]
    apply mapRange_finsuppAntidiag_subset
    rw [← mem_map_equiv]
    convert! hf
    rw [map_map]; rw [hh]
    convert! map_refl
    apply Function.Embedding.equiv_symm_toEmbedding_trans_toEmbedding

中文:
引理 mapRange_finsuppAntidiag_eq
  条件: {e : μ ≃+ μ'} {s : 有限集 ι} {n : μ}
  证明: by
  ext f
  constructor
  · apply mapRange_finsuppAntidiag_subset
  · set h := (mapRange.addEquiv e).toEquiv with hh
    intro hf
    have : n = e.symm (e n) := (AddEquiv.eq_symm_apply e).mpr rfl
    rw [mem_map_equiv]; rw [this]
    apply mapRange_finsuppAntidiag_subset
    rw [← mem_map_equiv]
    convert! hf
    rw [map_map]; rw [hh]
    convert! map_refl
    apply Function.Embedding.equiv_symm_toEmbedding_trans_toEmbedding

Depends on / 依赖: AddEquiv, AddEquiv.eq_symm_apply, Embedding, Function, Function.Embedding.equiv_symm_toEmbedding_trans_toEmbedding, addEquiv, convert, e.symm, eq_symm_apply, equiv_symm_toEmbedding_trans_toEmbedding, mapRange, mapRange.addEquiv, mapRange_finsuppAntidiag_subset, map_map, map_refl, mem_map_equiv, toEquiv
-/
lemma mapRange_finsuppAntidiag_eq {e : μ ≃+ μ'} {s : Finset ι} {n : μ} :
    (finsuppAntidiag s n).map (mapRange.addEquiv e).toEmbedding = finsuppAntidiag s (e n) := by
  ext f
  constructor
  · apply mapRange_finsuppAntidiag_subset
  · set h := (mapRange.addEquiv e).toEquiv with hh
    intro hf
    have : n = e.symm (e n) := (AddEquiv.eq_symm_apply e).mpr rfl
    rw [mem_map_equiv]; rw [this]
    apply mapRange_finsuppAntidiag_subset
    rw [← mem_map_equiv]
    convert! hf
    rw [map_map]; rw [hh]
    convert! map_refl
    apply Function.Embedding.equiv_symm_toEmbedding_trans_toEmbedding

end AddCommMonoid

section CanonicallyOrderedAddCommMonoid
variable [DecidableEq ι] [DecidableEq μ] [AddCommMonoid μ] [PartialOrder μ]
  [CanonicallyOrderedAdd μ] [HasAntidiagonal μ]

/--
lemma `finsuppAntidiag_zero` / 引理 `finsuppAntidiag_zero`

English:
lemma finsuppAntidiag_zero
  given: (s : Finset ι)
  statement: finsuppAntidiag s (0 : μ) = {0}
  proof: by
  ext f; simp [finsuppAntidiag, ← DFunLike.coe_fn_eq (g := f), eq_comm]

中文:
引理 finsuppAntidiag_zero
  条件: (s : 有限集 ι)
  结论: finsuppAntidiag s (0 : μ) = {0}
  证明: by
  ext f; simp [finsuppAntidiag, ← DFunLike.coe_fn_eq (g := f), eq_comm]
-/
@[simp] lemma finsuppAntidiag_zero (s : Finset ι) : finsuppAntidiag s (0 : μ) = {0} := by
  ext f; simp [finsuppAntidiag, ← DFunLike.coe_fn_eq (g := f), eq_comm]

end CanonicallyOrderedAddCommMonoid
end Finset
