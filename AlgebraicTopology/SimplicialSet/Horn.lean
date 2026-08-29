/-
Copyright (c) 2021 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin, Kim Morrison, Adam Topaz, Joël Riou
-/
module

public import Mathlib.AlgebraicTopology.SimplicialSet.StdSimplex
public import Mathlib.AlgebraicTopology.SimplicialSet.SubcomplexOp
public import Mathlib.CategoryTheory.Subfunctor.Equalizer

/-!
# Horns

This file introduces horns `Λ[n, i]`.

-/

@[expose] public section

universe u

open CategoryTheory Simplicial Opposite

namespace SSet

/-- `horn n i` (or `Λ[n, i]`) is the `i`-th horn of the `n`-th standard simplex,
where `i : n`. It consists of all `m`-simplices `α` of `Δ[n]`
for which the union of `{i}` and the range of `α` is not all of `n`
(when viewing `α` as monotone function `m → n`). -/
@[simps -isSimp obj]
/--
Definition of `horn` / `horn` 的定义

English:
definition horn
  signature: (n : Nat) (i : Fin (n + 1))
  body: Set.ofPred (fun s => Set.range (stdSimplex.asOrderHom s) union {i} != Set.univ)
  map φ s hs h := hs (by
    rw [Set.eq_univ_iff_forall] at h ⊢; intro j
    apply Or.imp _ id (h j)
    intro hj
    exact Set.range_comp_subset_range _ _ hj)

中文:
定义 horn
  签名: (n : 自然数) (i : 有限集 (n + 1))
  定义体: Set.ofPred (fun s => Set.range (stdSimplex.asOrderHom s) union {i} != Set.univ)
  map φ s hs h := hs (by
    rw [Set.eq_univ_iff_forall] at h ⊢; intro j
    apply Or.imp _ id (h j)
    intro hj
    exact Set.range_comp_subset_range _ _ hj)

Depends on / 依赖: Set.ofPred, Set.range, Set.univ, asOrderHom, ofPred, stdSimplex, stdSimplex.asOrderHom
-/
def horn (n : Nat) (i : Fin (n + 1)) : (Δ[n] : SSet.{u}).Subcomplex where
  obj _ := Set.ofPred (fun s => Set.range (stdSimplex.asOrderHom s) union {i} != Set.univ)
  map φ s hs h := hs (by
    rw [Set.eq_univ_iff_forall] at h ⊢; intro j
    apply Or.imp _ id (h j)
    intro hj
    exact Set.range_comp_subset_range _ _ hj)

/-- The `i`-th horn `Λ[n, i]` of the standard `n`-simplex -/
scoped[Simplicial] notation3 "Λ[" n ", " i "]" => SSet.horn (n : Nat) i

/--
lemma `mem_horn_iff` / 引理 `mem_horn_iff`

English:
lemma mem_horn_iff
  given: {n : Nat} (i : Fin (n + 1)) {m : SimplexCategoryᵒᵖ} (x : Δ[n].obj m)
  proof: Iff.rfl

中文:
引理 mem_horn_iff
  条件: {n : 自然数} (i : 有限集 (n + 1)) {m : SimplexCategoryᵒᵖ} (x : Δ[n].obj m)
  证明: Iff.rfl

Depends on / 依赖: Iff.rfl
-/
lemma mem_horn_iff {n : Nat} (i : Fin (n + 1)) {m : SimplexCategoryᵒᵖ} (x : Δ[n].obj m) :
    x in (horn n i).obj m ↔ Set.range (stdSimplex.asOrderHom x) union {i} != Set.univ := Iff.rfl

/--
lemma `horn_eq_iSup` / 引理 `horn_eq_iSup`

English:
lemma horn_eq_iSup
  given: (n : Nat) (i : Fin (n + 1))
  proof: by
  ext m j
  simp [stdSimplex.face_obj, horn, Set.eq_univ_iff_forall]
  rfl

中文:
引理 horn_eq_iSup
  条件: (n : 自然数) (i : 有限集 (n + 1))
  证明: by
  ext m j
  simp [stdSimplex.face_obj, horn, Set.eq_univ_iff_forall]
  rfl

Depends on / 依赖: Set.eq_univ_iff_forall, eq_univ_iff_forall, face_obj, stdSimplex, stdSimplex.face_obj
-/
lemma horn_eq_iSup (n : Nat) (i : Fin (n + 1)) :
    horn.{u} n i =
      ⨆ (j : ({i}ᶜ : Set (Fin (n + 1)))), stdSimplex.face {j.1}ᶜ := by
  ext m j
  simp [stdSimplex.face_obj, horn, Set.eq_univ_iff_forall]
  rfl

instance {n : Nat} (i : Fin (n + 1)) : HasDimensionLT (horn.{u} n i) n := by
  rw [horn_eq_iSup]; rw [hasDimensionLT_iSup_iff]
  intro i
  exact stdSimplex.hasDimensionLT_face _ _ (by simp [Finset.card_compl])

/--
lemma `mem_horn_iff_notMem_range` / 引理 `mem_horn_iff_notMem_range`

English:
lemma mem_horn_iff_notMem_range
  given: {n d : Nat} (s : Δ[n] _⦋d⦌) (i : Fin (n + 1))
  proof: by
  simp [horn_eq_iSup]

中文:
引理 mem_horn_iff_notMem_range
  条件: {n d : 自然数} (s : Δ[n] _⦋d⦌) (i : 有限集 (n + 1))
  证明: by
  simp [horn_eq_iSup]

Depends on / 依赖: horn_eq_iSup
-/
lemma mem_horn_iff_notMem_range {n d : Nat} (s : Δ[n] _⦋d⦌) (i : Fin (n + 1)) :
    s in (horn.{u} n i).obj _ ↔ exists (j : Fin (n + 1)) (_ : j != i), j ∉ Set.range s := by
  simp [horn_eq_iSup]

/--
lemma `face_le_horn` / 引理 `face_le_horn`

English:
lemma face_le_horn
  given: {n : Nat} (i j : Fin (n + 1)) (h : i != j)
  proof: by
  rw [horn_eq_iSup]
  exact le_iSup (fun (k : ({j}ᶜ : Set (Fin (n + 1)))) => stdSimplex.face.{u} {k.1}ᶜ) ⟨i, h⟩

@[simp]

中文:
引理 face_le_horn
  条件: {n : 自然数} (i j : 有限集 (n + 1)) (h : i != j)
  证明: by
  rw [horn_eq_iSup]
  exact le_iSup (fun (k : ({j}ᶜ : Set (Fin (n + 1)))) => stdSimplex.face.{u} {k.1}ᶜ) ⟨i, h⟩

@[simp]

Depends on / 依赖: horn_eq_iSup, le_iSup, stdSimplex, stdSimplex.face
-/
lemma face_le_horn {n : Nat} (i j : Fin (n + 1)) (h : i != j) :
    stdSimplex.face.{u} {i}ᶜ <= horn n j := by
  rw [horn_eq_iSup]
  exact le_iSup (fun (k : ({j}ᶜ : Set (Fin (n + 1)))) => stdSimplex.face.{u} {k.1}ᶜ) ⟨i, h⟩

@[simp]
/--
lemma `horn_obj_zero` / 引理 `horn_obj_zero`

English:
lemma horn_obj_zero
  given: (n : Nat) (i : Fin (n + 3))
  proof: by
  ext j
  -- this was produced using `simp? [horn_eq_iSup]`
  simp only [horn_eq_iSup, Subfunctor.iSup_obj, Set.iUnion_coe_set,
    Set.mem_compl_iff, Set.mem_singleton_iff, Set.mem_iUnion, stdSimplex.mem_face_iff,
    Nat.reduceAdd, Finset.mem_compl, Finset.mem_singleton, exists_prop, Set.top_eq_univ,
    Set.mem_univ, iff_true]
  let S : Finset (Fin (n + 3)) := {i, j 0}
  have hS : ¬ (S = Finset.univ) := fun hS => by
    have := Finset.card_le_card hS.symm.le
    simp only [Finset.card_univ, Fintype.card_fin, S] at this
    have := this.trans Finset.card_le_two
    lia
  rw [Finset.eq_univ_iff_forall]; rw [not_forall] at hS
  obtain ⟨k, hk⟩ := hS
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or, S] at hk
  refine ⟨k, hk.1, fun a => ?_⟩
  fin_cases a
  exact Ne.symm hk.2

中文:
引理 horn_obj_zero
  条件: (n : 自然数) (i : 有限集 (n + 3))
  证明: by
  ext j
  -- this was produced using `simp? [horn_eq_iSup]`
  simp only [horn_eq_iSup, Subfunctor.iSup_obj, Set.iUnion_coe_set,
    Set.mem_compl_iff, Set.mem_singleton_iff, Set.mem_iUnion, stdSimplex.mem_face_iff,
    Nat.reduceAdd, Finset.mem_compl, Finset.mem_singleton, exists_prop, Set.top_eq_univ,
    Set.mem_univ, iff_true]
  let S : Finset (Fin (n + 3)) := {i, j 0}
  have hS : ¬ (S = Finset.univ) := fun hS => by
    have := Finset.card_le_card hS.symm.le
    simp only [Finset.card_univ, Fintype.card_fin, S] at this
    have := this.trans Finset.card_le_two
    lia
  rw [Finset.eq_univ_iff_forall]; rw [not_forall] at hS
  obtain ⟨k, hk⟩ := hS
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or, S] at hk
  refine ⟨k, hk.1, fun a => ?_⟩
  fin_cases a
  exact Ne.symm hk.2
-/
lemma horn_obj_zero (n : Nat) (i : Fin (n + 3)) :
    (horn.{u} (n + 2) i).obj (op (.mk 0)) = ⊤ := by
  ext j
  -- this was produced using `simp? [horn_eq_iSup]`
  simp only [horn_eq_iSup, Subfunctor.iSup_obj, Set.iUnion_coe_set,
    Set.mem_compl_iff, Set.mem_singleton_iff, Set.mem_iUnion, stdSimplex.mem_face_iff,
    Nat.reduceAdd, Finset.mem_compl, Finset.mem_singleton, exists_prop, Set.top_eq_univ,
    Set.mem_univ, iff_true]
  let S : Finset (Fin (n + 3)) := {i, j 0}
  have hS : ¬ (S = Finset.univ) := fun hS => by
    have := Finset.card_le_card hS.symm.le
    simp only [Finset.card_univ, Fintype.card_fin, S] at this
    have := this.trans Finset.card_le_two
    lia
  rw [Finset.eq_univ_iff_forall]; rw [not_forall] at hS
  obtain ⟨k, hk⟩ := hS
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or, S] at hk
  refine ⟨k, hk.1, fun a => ?_⟩
  fin_cases a
  exact Ne.symm hk.2

/--
lemma `horn_obj_eq_univ` / 引理 `horn_obj_eq_univ`

English:
lemma horn_obj_eq_univ
  given: {n : Nat} (i : Fin (n + 1)) (m : Nat) (h : m + 1 < n := by lia)
  proof: by
  ext x
  obtain ⟨f, rfl⟩ := stdSimplex.objEquiv.symm.surjective x
  obtain ⟨j, hij, hj⟩ : exists (j : Fin (n + 1)), j != i ∧ j ∉ Set.range f.toOrderHom := by
    by_contra!
    have : Finset.image f.toOrderHom ⊤ union {i} = ⊤ := by ext k; by_cases k = i <;> aesop
    have := (congr_arg Finset.card this).symm.le.trans (Finset.card_union_le _ _)
    simp only [SimplexCategory.len_mk, Finset.top_eq_univ, Finset.card_univ, Fintype.card_fin,
      Finset.card_singleton, add_le_add_iff_right] at this
    have : n <= m + 1 := by simpa using this.trans Finset.card_image_le
    lia
  have : exists j, ¬j = i ∧ forall (i : Fin (m + 1)), ¬(stdSimplex.objEquiv.{u}.symm f) i = j :=
    ⟨j, hij, fun k hk => hj ⟨k, hk⟩⟩
  simpa [horn_eq_iSup] using this

中文:
引理 horn_obj_eq_univ
  条件: {n : 自然数} (i : 有限集 (n + 1)) (m : 自然数) (h : m + 1 < n := by lia)
  证明: by
  ext x
  obtain ⟨f, rfl⟩ := stdSimplex.objEquiv.symm.surjective x
  obtain ⟨j, hij, hj⟩ : exists (j : Fin (n + 1)), j != i ∧ j ∉ Set.range f.toOrderHom := by
    by_contra!
    have : Finset.image f.toOrderHom ⊤ union {i} = ⊤ := by ext k; by_cases k = i <;> aesop
    have := (congr_arg Finset.card this).symm.le.trans (Finset.card_union_le _ _)
    simp only [SimplexCategory.len_mk, Finset.top_eq_univ, Finset.card_univ, Fintype.card_fin,
      Finset.card_singleton, add_le_add_iff_right] at this
    have : n <= m + 1 := by simpa using this.trans Finset.card_image_le
    lia
  have : exists j, ¬j = i ∧ forall (i : Fin (m + 1)), ¬(stdSimplex.objEquiv.{u}.symm f) i = j :=
    ⟨j, hij, fun k hk => hj ⟨k, hk⟩⟩
  simpa [horn_eq_iSup] using this

Depends on / 依赖: Finset, Finset.card, Finset.card_singleton, Finset.card_union_le, Finset.card_univ, Finset.image, Finset.top_eq_univ, Fintype, Fintype.card_fin, Set.range, SimplexCategory, SimplexCategory.len_mk, add_l, card_fin, card_singleton, card_union_le, card_univ, congr_arg, f.toOrderHom, len_mk
-/
lemma horn_obj_eq_univ {n : Nat} (i : Fin (n + 1)) (m : Nat) (h : m + 1 < n := by lia) :
    (horn.{u} n i).obj (op ⦋m⦌) = .univ := by
  ext x
  obtain ⟨f, rfl⟩ := stdSimplex.objEquiv.symm.surjective x
  obtain ⟨j, hij, hj⟩ : exists (j : Fin (n + 1)), j != i ∧ j ∉ Set.range f.toOrderHom := by
    by_contra!
    have : Finset.image f.toOrderHom ⊤ union {i} = ⊤ := by ext k; by_cases k = i <;> aesop
    have := (congr_arg Finset.card this).symm.le.trans (Finset.card_union_le _ _)
    simp only [SimplexCategory.len_mk, Finset.top_eq_univ, Finset.card_univ, Fintype.card_fin,
      Finset.card_singleton, add_le_add_iff_right] at this
    have : n <= m + 1 := by simpa using this.trans Finset.card_image_le
    lia
  have : exists j, ¬j = i ∧ forall (i : Fin (m + 1)), ¬(stdSimplex.objEquiv.{u}.symm f) i = j :=
    ⟨j, hij, fun k hk => hj ⟨k, hk⟩⟩
  simpa [horn_eq_iSup] using this

/--
lemma `subcomplex_le_horn_iff` / 引理 `subcomplex_le_horn_iff`

English:
lemma subcomplex_le_horn_iff
  statement: {n : Nat}
  proof: by
  refine ⟨fun hA h => ?_, fun h => ?_⟩
  · replace h := h.trans hA
    rw [stdSimplex.face_singleton_compl]; rw [Subcomplex.ofSimplex_le_iff]; rw [mem_horn_iff] at h
    apply h
    rw [stdSimplex.coe_asOrderHom_objEquiv_symm]; rw [SimplexCategory.coe_δ]; rw [Fin.range_succAbove]; rw [Set.compl_union_self]
  · rw [Subcomplex.le_iff_contains_nonDegenerate]
    intro d x hx
    by_cases! hd : d < n
    · simp [horn_obj_eq_univ i d]
    · obtain ⟨⟨S, hS⟩, rfl⟩ := stdSimplex.nonDegenerateEquiv'.symm.surjective x
      dsimp at hS
      simp only [stdSimplex.nonDegenerateEquiv'_symm_mem_iff_face_le] at hx ⊢
      obtain hd | rfl := hd.lt_or_eq
      · obtain rfl : S = .univ := by
          rw [← Finset.card_eq_iff_eq_univ]; rw [Fintype.card_fin]
          exact le_antisymm (card_finset_fin_le S) (by lia)
        exact (h (le_trans (by simp) hx)).elim
      · replace hS : Sᶜ.card = 1 := by
          have := S.card_compl_add_card
          rw [Fintype.card_fin] at this
          lia
        obtain ⟨j, rfl⟩ : exists j, S = {j}ᶜ := by
          rw [Finset.card_eq_one] at hS
          obtain ⟨j, hS⟩ := hS
          exact ⟨j, by simp [← hS]⟩
        exact face_le_horn _ _ (by rintro rfl; tauto)

中文:
引理 subcomplex_le_horn_iff
  结论: {n : 自然数}
  证明: by
  refine ⟨fun hA h => ?_, fun h => ?_⟩
  · replace h := h.trans hA
    rw [stdSimplex.face_singleton_compl]; rw [Subcomplex.ofSimplex_le_iff]; rw [mem_horn_iff] at h
    apply h
    rw [stdSimplex.coe_asOrderHom_objEquiv_symm]; rw [SimplexCategory.coe_δ]; rw [Fin.range_succAbove]; rw [Set.compl_union_self]
  · rw [Subcomplex.le_iff_contains_nonDegenerate]
    intro d x hx
    by_cases! hd : d < n
    · simp [horn_obj_eq_univ i d]
    · obtain ⟨⟨S, hS⟩, rfl⟩ := stdSimplex.nonDegenerateEquiv'.symm.surjective x
      dsimp at hS
      simp only [stdSimplex.nonDegenerateEquiv'_symm_mem_iff_face_le] at hx ⊢
      obtain hd | rfl := hd.lt_or_eq
      · obtain rfl : S = .univ := by
          rw [← Finset.card_eq_iff_eq_univ]; rw [Fintype.card_fin]
          exact le_antisymm (card_finset_fin_le S) (by lia)
        exact (h (le_trans (by simp) hx)).elim
      · replace hS : Sᶜ.card = 1 := by
          have := S.card_compl_add_card
          rw [Fintype.card_fin] at this
          lia
        obtain ⟨j, rfl⟩ : exists j, S = {j}ᶜ := by
          rw [Finset.card_eq_one] at hS
          obtain ⟨j, hS⟩ := hS
          exact ⟨j, by simp [← hS]⟩
        exact face_le_horn _ _ (by rintro rfl; tauto)

Depends on / 依赖: Fin.range_succAbove, Set.compl_union_self, SimplexCategory, SimplexCategory.coe_, Subcomplex, Subcomplex.le_iff_contains_nonDegenerate, Subcomplex.ofSimplex_le_iff, coe_asOrderHom_objEquiv_symm, compl_union_self, face_singleton_compl, h.trans, horn_obj_eq_univ, le_iff_contains_nonDegenerate, mem_horn_iff, nonDegenerateEquiv, ofSimplex_le_iff, range_succAbove, replace, stdSimplex, stdSimplex.coe_asOrderHom_objEquiv_symm
-/
lemma subcomplex_le_horn_iff {n : Nat}
    (A : Δ[n + 1].Subcomplex) (i : Fin (n + 2)) :
    A <= horn.{u} (n + 1) i ↔ ¬ stdSimplex.face {i}ᶜ <= A := by
  refine ⟨fun hA h => ?_, fun h => ?_⟩
  · replace h := h.trans hA
    rw [stdSimplex.face_singleton_compl]; rw [Subcomplex.ofSimplex_le_iff]; rw [mem_horn_iff] at h
    apply h
    rw [stdSimplex.coe_asOrderHom_objEquiv_symm]; rw [SimplexCategory.coe_δ]; rw [Fin.range_succAbove]; rw [Set.compl_union_self]
  · rw [Subcomplex.le_iff_contains_nonDegenerate]
    intro d x hx
    by_cases! hd : d < n
    · simp [horn_obj_eq_univ i d]
    · obtain ⟨⟨S, hS⟩, rfl⟩ := stdSimplex.nonDegenerateEquiv'.symm.surjective x
      dsimp at hS
      simp only [stdSimplex.nonDegenerateEquiv'_symm_mem_iff_face_le] at hx ⊢
      obtain hd | rfl := hd.lt_or_eq
      · obtain rfl : S = .univ := by
          rw [← Finset.card_eq_iff_eq_univ]; rw [Fintype.card_fin]
          exact le_antisymm (card_finset_fin_le S) (by lia)
        exact (h (le_trans (by simp) hx)).elim
      · replace hS : Sᶜ.card = 1 := by
          have := S.card_compl_add_card
          rw [Fintype.card_fin] at this
          lia
        obtain ⟨j, rfl⟩ : exists j, S = {j}ᶜ := by
          rw [Finset.card_eq_one] at hS
          obtain ⟨j, hS⟩ := hS
          exact ⟨j, by simp [← hS]⟩
        exact face_le_horn _ _ (by rintro rfl; tauto)

/--
lemma `face_le_horn_iff` / 引理 `face_le_horn_iff`

English:
lemma face_le_horn_iff
  given: {n : Nat} (S : Finset (Fin (n + 2))) (j : Fin (n + 2))
  proof: by
  rw [subcomplex_le_horn_iff]; rw [stdSimplex.face_le_face_iff]; rw [← not_iff_not]
  simp only [Decidable.not_not, ne_eq, not_and_or]
  refine ⟨fun h => ?_, by aesop⟩
  rw [← Finset.compl_subset_compl]; rw [compl_compl]; rw [Finset.subset_singleton_iff]; rw [Finset.compl_eq_empty_iff] at h
  grind [eq_compl_comm]

中文:
引理 face_le_horn_iff
  条件: {n : 自然数} (S : 有限集 (有限集 (n + 2))) (j : 有限集 (n + 2))
  证明: by
  rw [subcomplex_le_horn_iff]; rw [stdSimplex.face_le_face_iff]; rw [← not_iff_not]
  simp only [Decidable.not_not, ne_eq, not_and_or]
  refine ⟨fun h => ?_, by aesop⟩
  rw [← Finset.compl_subset_compl]; rw [compl_compl]; rw [Finset.subset_singleton_iff]; rw [Finset.compl_eq_empty_iff] at h
  grind [eq_compl_comm]

Depends on / 依赖: Decidable, Decidable.not_not, Finset, Finset.compl_eq_empty_iff, Finset.compl_subset_compl, Finset.subset_singleton_iff, compl_compl, compl_eq_empty_iff, compl_subset_compl, eq_compl_comm, face_le_face_iff, ne_eq, not_and_or, not_iff_not, not_not, stdSimplex, stdSimplex.face_le_face_iff, subcomplex_le_horn_iff, subset_singleton_iff
-/
lemma face_le_horn_iff {n : Nat} (S : Finset (Fin (n + 2))) (j : Fin (n + 2)) :
    stdSimplex.face.{u} S <= Λ[n + 1, j] ↔ S != .univ ∧ S != {j}ᶜ := by
  rw [subcomplex_le_horn_iff]; rw [stdSimplex.face_le_face_iff]; rw [← not_iff_not]
  simp only [Decidable.not_not, ne_eq, not_and_or]
  refine ⟨fun h => ?_, by aesop⟩
  rw [← Finset.compl_subset_compl]; rw [compl_compl]; rw [Finset.subset_singleton_iff]; rw [Finset.compl_eq_empty_iff] at h
  grind [eq_compl_comm]

/--
lemma `objEquiv_symm_notMem_horn_of_isIso` / 引理 `objEquiv_symm_notMem_horn_of_isIso`

English:
lemma objEquiv_symm_notMem_horn_of_isIso
  statement: {n : Nat} (i : Fin (n + 1))
  proof: by
  rw [mem_horn_iff]; rw [ne_eq]; rw [not_not]
  ext i
  simpa using Or.inr ⟨inv f i, by simp [stdSimplex.coe_asOrderHom_objEquiv_symm.{u}]⟩

中文:
引理 objEquiv_symm_notMem_horn_of_isIso
  结论: {n : 自然数} (i : 有限集 (n + 1))
  证明: by
  rw [mem_horn_iff]; rw [ne_eq]; rw [not_not]
  ext i
  simpa using Or.inr ⟨inv f i, by simp [stdSimplex.coe_asOrderHom_objEquiv_symm.{u}]⟩

Depends on / 依赖: Or.inr, coe_asOrderHom_objEquiv_symm, mem_horn_iff, ne_eq, not_not, stdSimplex, stdSimplex.coe_asOrderHom_objEquiv_symm
-/
lemma objEquiv_symm_notMem_horn_of_isIso {n : Nat} (i : Fin (n + 1))
    {d : SimplexCategory} (f : d ⟶ ⦋n⦌) [IsIso f] :
    stdSimplex.objEquiv.{u}.symm f ∉ Λ[n, i].obj (op d) := by
  rw [mem_horn_iff]; rw [ne_eq]; rw [not_not]
  ext i
  simpa using Or.inr ⟨inv f i, by simp [stdSimplex.coe_asOrderHom_objEquiv_symm.{u}]⟩

/--
lemma `objEquiv_symm_δ_mem_horn_iff` / 引理 `objEquiv_symm_δ_mem_horn_iff`

English:
lemma objEquiv_symm_δ_mem_horn_iff
  given: {n : Nat} (i j : Fin (n + 2))
  proof: by
  dsimp
  rw [← Subcomplex.ofSimplex_le_iff]; rw [← stdSimplex.face_singleton_compl]; rw [face_le_horn_iff]
  simp

中文:
引理 objEquiv_symm_δ_mem_horn_iff
  条件: {n : 自然数} (i j : 有限集 (n + 2))
  证明: by
  dsimp
  rw [← Subcomplex.ofSimplex_le_iff]; rw [← stdSimplex.face_singleton_compl]; rw [face_le_horn_iff]
  simp
-/
lemma objEquiv_symm_δ_mem_horn_iff {n : Nat} (i j : Fin (n + 2)) :
    (stdSimplex.objEquiv (m := op ⦋n⦌)).symm
      (SimplexCategory.δ i) in (horn.{u} (n + 1) j).obj (op ⦋n⦌) ↔ i != j := by
  dsimp
  rw [← Subcomplex.ofSimplex_le_iff]; rw [← stdSimplex.face_singleton_compl]; rw [face_le_horn_iff]
  simp

/--
lemma `objEquiv_symm_δ_notMem_horn_iff` / 引理 `objEquiv_symm_δ_notMem_horn_iff`

English:
lemma objEquiv_symm_δ_notMem_horn_iff
  given: {n : Nat} (i j : Fin (n + 2))
  proof: by
  simp [objEquiv_symm_δ_mem_horn_iff.{u}]

中文:
引理 objEquiv_symm_δ_notMem_horn_iff
  条件: {n : 自然数} (i j : 有限集 (n + 2))
  证明: by
  simp [objEquiv_symm_δ_mem_horn_iff.{u}]
-/
lemma objEquiv_symm_δ_notMem_horn_iff {n : Nat} (i j : Fin (n + 2)) :
    (stdSimplex.objEquiv (m := op ⦋n⦌)).symm
      (SimplexCategory.δ i) ∉ (horn.{u} _ j).obj (op ⦋n⦌) ↔ i = j := by
  simp [objEquiv_symm_δ_mem_horn_iff.{u}]

/--
lemma `op_horn` / 引理 `op_horn`

English:
lemma op_horn
  given: {n : Nat} (i : Fin (n + 1))
  proof: by
  ext ⟨⟨d⟩⟩ j
  simp only [Subcomplex.preimage_obj, Set.mem_preimage, stdSimplex.opIso_inv_app_hom_apply,
    Subcomplex.mem_op_obj_iff, mem_horn_iff_notMem_range, Set.mem_range, not_exists, ne_eq,
    exists_prop, stdSimplex.opObjEquiv_opObjEquiv_symm_apply]
  constructor
  · rintro ⟨k, h₁, h₂⟩
    exact ⟨k.rev, by simpa, fun l hl => by grind [h₂ l.rev]⟩
  · rintro ⟨k, h₁, h₂⟩
    exact ⟨k.rev, by grind⟩

中文:
引理 op_horn
  条件: {n : 自然数} (i : 有限集 (n + 1))
  证明: by
  ext ⟨⟨d⟩⟩ j
  simp only [Subcomplex.preimage_obj, Set.mem_preimage, stdSimplex.opIso_inv_app_hom_apply,
    Subcomplex.mem_op_obj_iff, mem_horn_iff_notMem_range, Set.mem_range, not_exists, ne_eq,
    exists_prop, stdSimplex.opObjEquiv_opObjEquiv_symm_apply]
  constructor
  · rintro ⟨k, h₁, h₂⟩
    exact ⟨k.rev, by simpa, fun l hl => by grind [h₂ l.rev]⟩
  · rintro ⟨k, h₁, h₂⟩
    exact ⟨k.rev, by grind⟩

Depends on / 依赖: Set.mem_preimage, Set.mem_range, Subcomplex, Subcomplex.mem_op_obj_iff, Subcomplex.preimage_obj, exists_prop, k.rev, l.rev, mem_horn_iff_notMem_range, mem_op_obj_iff, mem_preimage, mem_range, ne_eq, not_exists, opIso_inv_app_hom_apply, opObjEquiv_opObjEquiv_symm_apply, preimage_obj, stdSimplex, stdSimplex.opIso_inv_app_hom_apply, stdSimplex.opObjEquiv_opObjEquiv_symm_apply
-/
lemma op_horn {n : Nat} (i : Fin (n + 1)) :
    Λ[n, i].op.preimage (stdSimplex.opIso.{u} ⦋n⦌).inv = Λ[n, i.rev] := by
  ext ⟨⟨d⟩⟩ j
  simp only [Subcomplex.preimage_obj, Set.mem_preimage, stdSimplex.opIso_inv_app_hom_apply,
    Subcomplex.mem_op_obj_iff, mem_horn_iff_notMem_range, Set.mem_range, not_exists, ne_eq,
    exists_prop, stdSimplex.opObjEquiv_opObjEquiv_symm_apply]
  constructor
  · rintro ⟨k, h₁, h₂⟩
    exact ⟨k.rev, by simpa, fun l hl => by grind [h₂ l.rev]⟩
  · rintro ⟨k, h₁, h₂⟩
    exact ⟨k.rev, by grind⟩

namespace horn

open SimplexCategory Finset Opposite

section

variable (n : Nat) (i k : Fin (n + 3))

/--
Definition of `const` / `const` 的定义

English:
definition const
  signature: (m : SimplexCategoryᵒᵖ)
  body: SSet.yonedaEquiv (X := Λ[n + 2, i])
    (SSet.const ⟨stdSimplex.obj₀Equiv.symm k, by simp⟩)

@[simp]

中文:
定义 const
  签名: (m : SimplexCategoryᵒᵖ)
  定义体: SSet.yonedaEquiv (X := Λ[n + 2, i])
    (SSet.const ⟨stdSimplex.obj₀Equiv.symm k, by simp⟩)

@[simp]

Depends on / 依赖: Equiv.symm, SSet.const, SSet.yonedaEquiv, stdSimplex, stdSimplex.obj, yonedaEquiv
-/
def const (m : SimplexCategoryᵒᵖ) : Λ[n + 2, i].obj m :=
  SSet.yonedaEquiv (X := Λ[n + 2, i])
    (SSet.const ⟨stdSimplex.obj₀Equiv.symm k, by simp⟩)

@[simp]
/--
lemma `const_val_apply` / 引理 `const_val_apply`

English:
lemma const_val_apply
  given: {m : Nat} (a : Fin (m + 1))
  proof: rfl

中文:
引理 const_val_apply
  条件: {m : 自然数} (a : 有限集 (m + 1))
  证明: rfl
-/
lemma const_val_apply {m : Nat} (a : Fin (m + 1)) :
    (const n i k (op (.mk m))).val a = k :=
  rfl

end

/-- The edge of `Λ[n, i]` with endpoints `a` and `b`.

This edge only exists if `{i, a, b}` has cardinality less than `n`. -/
@[simps]
/--
Definition of `edge` / `edge` 的定义

English:
definition edge
  signature: (n : Nat) (i a b : Fin (n + 1)) (hab : a <= b) (H : #{i, a, b} <= n)
  body: ⟨stdSimplex.edge n a b hab, by
    have hS : ¬ ({i, a, b} = Finset.univ) := fun hS => by
      have := Finset.card_le_card hS.symm.le
      simp only [card_univ, Fintype.card_fin] at this
      lia
    rw [Finset.eq_univ_iff_forall]; rw [not_forall] at hS
    obtain ⟨k, hk⟩ := hS
    simp only [mem_insert, mem_singleton, not_or] at hk
    -- this was produced by `simp? [horn_eq_iSup, -Fin.forall_fin_two]`
    simp only [horn_eq_iSup, Subfunctor.iSup_obj, Set.iUnion_coe_set, Set.mem_compl_iff,
      Set.mem_singleton_iff, Set.mem_iUnion, stdSimplex.mem_face_iff, Nat.reduceAdd, mem_compl,
      mem_singleton, exists_prop]
    refine ⟨k, hk.1, fun a => ?_⟩
    fin_cases a
    · exact Ne.symm hk.2.1
    · exact Ne.symm hk.2.2⟩

中文:
定义 edge
  签名: (n : 自然数) (i a b : 有限集 (n + 1)) (hab : a <= b) (H : #{i, a, b} <= n)
  定义体: ⟨stdSimplex.edge n a b hab, by
    have hS : ¬ ({i, a, b} = Finset.univ) := fun hS => by
      have := Finset.card_le_card hS.symm.le
      simp only [card_univ, Fintype.card_fin] at this
      lia
    rw [Finset.eq_univ_iff_forall]; rw [not_forall] at hS
    obtain ⟨k, hk⟩ := hS
    simp only [mem_insert, mem_singleton, not_or] at hk
    -- this was produced by `simp? [horn_eq_iSup, -Fin.forall_fin_two]`
    simp only [horn_eq_iSup, Subfunctor.iSup_obj, Set.iUnion_coe_set, Set.mem_compl_iff,
      Set.mem_singleton_iff, Set.mem_iUnion, stdSimplex.mem_face_iff, Nat.reduceAdd, mem_compl,
      mem_singleton, exists_prop]
    refine ⟨k, hk.1, fun a => ?_⟩
    fin_cases a
    · exact Ne.symm hk.2.1
    · exact Ne.symm hk.2.2⟩

Depends on / 依赖: Finset, Finset.card_le_card, Finset.eq_univ_iff_forall, Finset.univ, Fintype, Fintype.card_fin, NormedAddCommGroup, NormedSpace, card_fin, card_le_card, card_univ, eq_univ_iff_forall, hS.symm.le, mem_insert, mem_singleton, not_forall, not_or, stdSimplex, stdSimplex.edge
-/
def edge (n : Nat) (i a b : Fin (n + 1)) (hab : a <= b) (H : #{i, a, b} <= n) :
    (Λ[n, i] : SSet.{u}).obj (op ⦋1⦌) :=
  ⟨stdSimplex.edge n a b hab, by
    have hS : ¬ ({i, a, b} = Finset.univ) := fun hS => by
      have := Finset.card_le_card hS.symm.le
      simp only [card_univ, Fintype.card_fin] at this
      lia
    rw [Finset.eq_univ_iff_forall]; rw [not_forall] at hS
    obtain ⟨k, hk⟩ := hS
    simp only [mem_insert, mem_singleton, not_or] at hk
    -- this was produced by `simp? [horn_eq_iSup, -Fin.forall_fin_two]`
    simp only [horn_eq_iSup, Subfunctor.iSup_obj, Set.iUnion_coe_set, Set.mem_compl_iff,
      Set.mem_singleton_iff, Set.mem_iUnion, stdSimplex.mem_face_iff, Nat.reduceAdd, mem_compl,
      mem_singleton, exists_prop]
    refine ⟨k, hk.1, fun a => ?_⟩
    fin_cases a
    · exact Ne.symm hk.2.1
    · exact Ne.symm hk.2.2⟩

/-- Alternative constructor for the edge of `Λ[n, i]` with endpoints `a` and `b`,
assuming `3 ≤ n`. -/
@[simps!]
/--
Definition of `edge₃` / `edge₃` 的定义

English:
definition edge₃
  signature: (n : Nat) (i a b : Fin (n + 1)) (hab : a <= b) (H : 3 <= n)
  body: edge n i a b hab Finset.card_le_three.trans H

中文:
定义 edge₃
  签名: (n : 自然数) (i a b : 有限集 (n + 1)) (hab : a <= b) (H : 3 <= n)
  定义体: edge n i a b hab Finset.card_le_three.trans H

Depends on / 依赖: Finset, Finset.card_le_three.trans, card_le_three
-/
def edge₃ (n : Nat) (i a b : Fin (n + 1)) (hab : a <= b) (H : 3 <= n) :
    (Λ[n, i] : SSet.{u}) _⦋1⦌ :=
edge n i a b hab Finset.card_le_three.trans H

/-- The edge of `Λ[n, i]` with endpoints `j` and `j+1`.

This constructor assumes `0 < i < n`,
which is the type of horn that occurs in the horn-filling condition of quasicategories. -/
@[simps!]
/--
Definition of `primitiveEdge` / `primitiveEdge` 的定义

English:
definition primitiveEdge
  signature: {n : Nat} {i : Fin (n + 1)}
  body: by
  refine edge n i j.castSucc j.succ ?_ ?_
  · simp only [← Fin.val_fin_le, Fin.val_castSucc, Fin.val_succ, le_add_iff_nonneg_right, zero_le]
  simp only [← Fin.val_fin_lt, Fin.val_zero, Fin.val_last] at h₀ hₙ
  obtain rfl | hn : n = 2 ∨ 2 < n := by
    rw [eq_comm]; rw [or_comm]; rw [← le_iff_lt_or_eq]; lia
  · revert i j; decide
  · exact Finset.card_le_three.trans hn

中文:
定义 primitiveEdge
  签名: {n : 自然数} {i : 有限集 (n + 1)}
  定义体: by
  refine edge n i j.castSucc j.succ ?_ ?_
  · simp only [← Fin.val_fin_le, Fin.val_castSucc, Fin.val_succ, le_add_iff_nonneg_right, zero_le]
  simp only [← Fin.val_fin_lt, Fin.val_zero, Fin.val_last] at h₀ hₙ
  obtain rfl | hn : n = 2 ∨ 2 < n := by
    rw [eq_comm]; rw [or_comm]; rw [← le_iff_lt_or_eq]; lia
  · revert i j; decide
  · exact Finset.card_le_three.trans hn

Depends on / 依赖: Fin.val_castSucc, Fin.val_fin_le, Fin.val_fin_lt, Fin.val_last, Fin.val_succ, Fin.val_zero, Finset, Finset.card_le_three.trans, HasContDiffBump, card_le_three, castSucc, eq_comm, hasContDiffBump_of_innerProductSpace, j.castSucc, j.succ, le_add_iff_nonneg_right, le_iff_lt_or_eq, or_comm, revert, val_castSucc
-/
def primitiveEdge {n : Nat} {i : Fin (n + 1)}
    (h₀ : 0 < i) (hₙ : i < Fin.last n) (j : Fin n) :
    (Λ[n, i] : SSet.{u}) _⦋1⦌ := by
  refine edge n i j.castSucc j.succ ?_ ?_
  · simp only [← Fin.val_fin_le, Fin.val_castSucc, Fin.val_succ, le_add_iff_nonneg_right, zero_le]
  simp only [← Fin.val_fin_lt, Fin.val_zero, Fin.val_last] at h₀ hₙ
  obtain rfl | hn : n = 2 ∨ 2 < n := by
    rw [eq_comm]; rw [or_comm]; rw [← le_iff_lt_or_eq]; lia
  · revert i j; decide
  · exact Finset.card_le_three.trans hn

/-- The triangle in the standard simplex with vertices `k`, `k+1`, and `k+2`.

This constructor assumes `0 < i < n`,
which is the type of horn that occurs in the horn-filling condition of quasicategories. -/
@[simps]
/--
Definition of `primitiveTriangle` / `primitiveTriangle` 的定义

English:
definition primitiveTriangle
  signature: {n : Nat} (i : Fin (n + 4))
  body: by
  refine ⟨stdSimplex.triangle
    (n := n+3) ⟨k, by lia⟩ ⟨k+1, by lia⟩ ⟨k+2, by lia⟩ ?_ ?_, ?_⟩
  · simp only [Fin.mk_le_mk, le_add_iff_nonneg_right, zero_le]
  · simp only [Fin.mk_le_mk, add_le_add_iff_left, one_le_two]
  -- this was produced using `simp? [horn_eq_iSup]`
  simp only [horn_eq_iSup, Subfunctor.iSup_obj, Set.iUnion_coe_set,
    Set.mem_compl_iff, Set.mem_singleton_iff, Set.mem_iUnion, stdSimplex.mem_face_iff,
    Nat.reduceAdd, mem_compl, mem_singleton, exists_prop]
  have hS : ¬ ({i, (⟨k, by lia⟩ : Fin (n + 4)), (⟨k + 1, by lia⟩ : Fin (n + 4)),
      (⟨k + 2, by lia⟩ : Fin (n + 4))} = Finset.univ) := fun hS => by
    obtain ⟨i, hi⟩ := i
    by_cases hk : k = 0
    · subst hk
      have := Finset.mem_univ (Fin.last _ : Fin (n + 4))
      rw [← hS] at this
      -- this was produced using `simp? [Fin.ext_iff] at this`
      simp only [Fin.zero_eta, zero_add, Fin.mk_one, mem_insert, Fin.ext_iff, Fin.val_last,
        Fin.val_zero, AddLeftCancelMonoid.add_eq_zero, OfNat.ofNat_ne_zero, and_false,
        Fin.val_one, Nat.reduceEqDiff, mem_singleton, or_self, or_false] at this
      simp only [Fin.lt_def, Fin.val_last] at hₙ
      lia
    · have := Finset.mem_univ (0 : Fin (n + 4))
      rw [← hS] at this
      -- this was produced using `simp? [Fin.ext_iff] at this`
      simp only [mem_insert, Fin.ext_iff, Fin.val_zero, right_eq_add,
        AddLeftCancelMonoid.add_eq_zero, one_ne_zero, and_false, mem_singleton,
        OfNat.ofNat_ne_zero, or_self, or_false] at this
      obtain rfl | rfl := this <;> tauto
  rw [Finset.eq_univ_iff_forall]; rw [not_forall] at hS
  obtain ⟨l, hl⟩ := hS
  simp only [mem_insert, mem_singleton, not_or] at hl
  refine ⟨l, hl.1, fun a => ?_⟩
  fin_cases a
  · exact Ne.symm hl.2.1
  · exact Ne.symm hl.2.2.1
  · exact Ne.symm hl.2.2.2

中文:
定义 primitiveTriangle
  签名: {n : 自然数} (i : 有限集 (n + 4))
  定义体: by
  refine ⟨stdSimplex.triangle
    (n := n+3) ⟨k, by lia⟩ ⟨k+1, by lia⟩ ⟨k+2, by lia⟩ ?_ ?_, ?_⟩
  · simp only [Fin.mk_le_mk, le_add_iff_nonneg_right, zero_le]
  · simp only [Fin.mk_le_mk, add_le_add_iff_left, one_le_two]
  -- this was produced using `simp? [horn_eq_iSup]`
  simp only [horn_eq_iSup, Subfunctor.iSup_obj, Set.iUnion_coe_set,
    Set.mem_compl_iff, Set.mem_singleton_iff, Set.mem_iUnion, stdSimplex.mem_face_iff,
    Nat.reduceAdd, mem_compl, mem_singleton, exists_prop]
  have hS : ¬ ({i, (⟨k, by lia⟩ : Fin (n + 4)), (⟨k + 1, by lia⟩ : Fin (n + 4)),
      (⟨k + 2, by lia⟩ : Fin (n + 4))} = Finset.univ) := fun hS => by
    obtain ⟨i, hi⟩ := i
    by_cases hk : k = 0
    · subst hk
      have := Finset.mem_univ (Fin.last _ : Fin (n + 4))
      rw [← hS] at this
      -- this was produced using `simp? [Fin.ext_iff] at this`
      simp only [Fin.zero_eta, zero_add, Fin.mk_one, mem_insert, Fin.ext_iff, Fin.val_last,
        Fin.val_zero, AddLeftCancelMonoid.add_eq_zero, OfNat.ofNat_ne_zero, and_false,
        Fin.val_one, Nat.reduceEqDiff, mem_singleton, or_self, or_false] at this
      simp only [Fin.lt_def, Fin.val_last] at hₙ
      lia
    · have := Finset.mem_univ (0 : Fin (n + 4))
      rw [← hS] at this
      -- this was produced using `simp? [Fin.ext_iff] at this`
      simp only [mem_insert, Fin.ext_iff, Fin.val_zero, right_eq_add,
        AddLeftCancelMonoid.add_eq_zero, one_ne_zero, and_false, mem_singleton,
        OfNat.ofNat_ne_zero, or_self, or_false] at this
      obtain rfl | rfl := this <;> tauto
  rw [Finset.eq_univ_iff_forall]; rw [not_forall] at hS
  obtain ⟨l, hl⟩ := hS
  simp only [mem_insert, mem_singleton, not_or] at hl
  refine ⟨l, hl.1, fun a => ?_⟩
  fin_cases a
  · exact Ne.symm hl.2.1
  · exact Ne.symm hl.2.2.1
  · exact Ne.symm hl.2.2.2

Depends on / 依赖: Fin.mk_le_mk, add_le_add_iff_left, le_add_iff_nonneg_right, mk_le_mk, one_le_two, stdSimplex, stdSimplex.triangle, triangle, zero_le
-/
def primitiveTriangle {n : Nat} (i : Fin (n + 4))
    (h₀ : 0 < i) (hₙ : i < Fin.last (n + 3))
    (k : Nat) (h : k < n + 2) : (Λ[n + 3, i] : SSet.{u}).obj (op ⦋2⦌) := by
  refine ⟨stdSimplex.triangle
    (n := n+3) ⟨k, by lia⟩ ⟨k+1, by lia⟩ ⟨k+2, by lia⟩ ?_ ?_, ?_⟩
  · simp only [Fin.mk_le_mk, le_add_iff_nonneg_right, zero_le]
  · simp only [Fin.mk_le_mk, add_le_add_iff_left, one_le_two]
  -- this was produced using `simp? [horn_eq_iSup]`
  simp only [horn_eq_iSup, Subfunctor.iSup_obj, Set.iUnion_coe_set,
    Set.mem_compl_iff, Set.mem_singleton_iff, Set.mem_iUnion, stdSimplex.mem_face_iff,
    Nat.reduceAdd, mem_compl, mem_singleton, exists_prop]
  have hS : ¬ ({i, (⟨k, by lia⟩ : Fin (n + 4)), (⟨k + 1, by lia⟩ : Fin (n + 4)),
      (⟨k + 2, by lia⟩ : Fin (n + 4))} = Finset.univ) := fun hS => by
    obtain ⟨i, hi⟩ := i
    by_cases hk : k = 0
    · subst hk
      have := Finset.mem_univ (Fin.last _ : Fin (n + 4))
      rw [← hS] at this
      -- this was produced using `simp? [Fin.ext_iff] at this`
      simp only [Fin.zero_eta, zero_add, Fin.mk_one, mem_insert, Fin.ext_iff, Fin.val_last,
        Fin.val_zero, AddLeftCancelMonoid.add_eq_zero, OfNat.ofNat_ne_zero, and_false,
        Fin.val_one, Nat.reduceEqDiff, mem_singleton, or_self, or_false] at this
      simp only [Fin.lt_def, Fin.val_last] at hₙ
      lia
    · have := Finset.mem_univ (0 : Fin (n + 4))
      rw [← hS] at this
      -- this was produced using `simp? [Fin.ext_iff] at this`
      simp only [mem_insert, Fin.ext_iff, Fin.val_zero, right_eq_add,
        AddLeftCancelMonoid.add_eq_zero, one_ne_zero, and_false, mem_singleton,
        OfNat.ofNat_ne_zero, or_self, or_false] at this
      obtain rfl | rfl := this <;> tauto
  rw [Finset.eq_univ_iff_forall]; rw [not_forall] at hS
  obtain ⟨l, hl⟩ := hS
  simp only [mem_insert, mem_singleton, not_or] at hl
  refine ⟨l, hl.1, fun a => ?_⟩
  fin_cases a
  · exact Ne.symm hl.2.1
  · exact Ne.symm hl.2.2.1
  · exact Ne.symm hl.2.2.2

/--
Definition of `face` / `face` 的定义

English:
definition face
  signature: {n : Nat} (i j : Fin (n + 2)) (h : j != i)
  body: yonedaEquiv (Subfunctor.lift (stdSimplex.δ j) (by
    simpa using face_le_horn _ _ h))

中文:
定义 face
  签名: {n : 自然数} (i j : 有限集 (n + 2)) (h : j != i)
  定义体: yonedaEquiv (Subfunctor.lift (stdSimplex.δ j) (by
    simpa using face_le_horn _ _ h))

Depends on / 依赖: Subfunctor, Subfunctor.lift, face_le_horn, stdSimplex, yonedaEquiv
-/
def face {n : Nat} (i j : Fin (n + 2)) (h : j != i) : (Λ[n + 1, i] : SSet.{u}) _⦋n⦌ :=
  yonedaEquiv (Subfunctor.lift (stdSimplex.δ j) (by
    simpa using face_le_horn _ _ h))

/-- Two morphisms from a horn are equal if they are equal on all suitable faces. -/
protected
/--
lemma `hom_ext` / 引理 `hom_ext`

English:
lemma hom_ext
  statement: {n : Nat} {i : Fin (n + 2)} {S : SSet} (σ₁ σ₂ : (Λ[n + 1, i] : SSet.{u}) ⟶ S)
  proof: by
  rw [← Subfunctor.equalizer_eq_iff]
  apply le_antisymm (Subfunctor.equalizer_le σ₁ σ₂)
  simp only [horn_eq_iSup, iSup_le_iff,
    Subtype.forall, Set.mem_compl_iff, Set.mem_singleton_iff,
    ← stdSimplex.ofSimplex_yonedaEquiv_δ, Subcomplex.ofSimplex_le_iff]
  intro j hj
  exact (Subfunctor.mem_equalizer_iff σ₁ σ₂ (face i j hj)).2 (by apply h)

中文:
引理 hom_ext
  结论: {n : 自然数} {i : 有限集 (n + 2)} {S : SSet} (σ₁ σ₂ : (Λ[n + 1, i] : SSet.{u}) ⟶ S)
  证明: by
  rw [← Subfunctor.equalizer_eq_iff]
  apply le_antisymm (Subfunctor.equalizer_le σ₁ σ₂)
  simp only [horn_eq_iSup, iSup_le_iff,
    Subtype.forall, Set.mem_compl_iff, Set.mem_singleton_iff,
    ← stdSimplex.ofSimplex_yonedaEquiv_δ, Subcomplex.ofSimplex_le_iff]
  intro j hj
  exact (Subfunctor.mem_equalizer_iff σ₁ σ₂ (face i j hj)).2 (by apply h)

Depends on / 依赖: Set.mem_compl_iff, Set.mem_singleton_iff, Subcomplex, Subcomplex.ofSimplex_le_iff, Subfunctor, Subfunctor.equalizer_eq_iff, Subfunctor.equalizer_le, Subfunctor.mem_equalizer_iff, Subtype, Subtype.forall, equalizer_eq_iff, equalizer_le, horn_eq_iSup, iSup_le_iff, le_antisymm, mem_compl_iff, mem_equalizer_iff, mem_singleton_iff, ofSimplex_le_iff, stdSimplex
-/
lemma hom_ext {n : Nat} {i : Fin (n + 2)} {S : SSet} (σ₁ σ₂ : (Λ[n + 1, i] : SSet.{u}) ⟶ S)
    (h : forall (j) (h : j != i), σ₁.app _ (face i j h) = σ₂.app _ (face i j h)) :
    σ₁ = σ₂ := by
  rw [← Subfunctor.equalizer_eq_iff]
  apply le_antisymm (Subfunctor.equalizer_le σ₁ σ₂)
  simp only [horn_eq_iSup, iSup_le_iff,
    Subtype.forall, Set.mem_compl_iff, Set.mem_singleton_iff,
    ← stdSimplex.ofSimplex_yonedaEquiv_δ, Subcomplex.ofSimplex_le_iff]
  intro j hj
  exact (Subfunctor.mem_equalizer_iff σ₁ σ₂ (face i j hj)).2 (by apply h)


/--
Definition of `faceι` / `faceι` 的定义

English:
definition faceι
  signature: {n : Nat} (i : Fin (n + 1)) (j : Fin (n + 1)) (hij : j != i)
  body: Subcomplex.homOfLE (face_le_horn j i hij)

@[reassoc (attr := simp)]

中文:
定义 faceι
  签名: {n : 自然数} (i : 有限集 (n + 1)) (j : 有限集 (n + 1)) (hij : j != i)
  定义体: Subcomplex.homOfLE (face_le_horn j i hij)

@[reassoc (attr := simp)]

Depends on / 依赖: Subcomplex, Subcomplex.homOfLE, face_le_horn, homOfLE
-/
def faceι {n : Nat} (i : Fin (n + 1)) (j : Fin (n + 1)) (hij : j != i) :
    (stdSimplex.face {j}ᶜ : SSet.{u}) ⟶ (Λ[n, i] : SSet.{u}) :=
  Subcomplex.homOfLE (face_le_horn j i hij)

@[reassoc (attr := simp)]
/--
lemma `faceι_ι` / 引理 `faceι_ι`

English:
lemma faceι_ι
  given: {n : Nat} (i : Fin (n + 1)) (j : Fin (n + 1)) (hij : j != i)
  proof: by
  simp [faceι]

中文:
引理 faceι_ι
  条件: {n : 自然数} (i : 有限集 (n + 1)) (j : 有限集 (n + 1)) (hij : j != i)
  证明: by
  simp [faceι]
-/
lemma faceι_ι {n : Nat} (i : Fin (n + 1)) (j : Fin (n + 1)) (hij : j != i) :
    faceι i j hij ≫ Λ[n, i].ι = (stdSimplex.face {j}ᶜ).ι := by
  simp [faceι]

/--
Definition of `ι` / `ι` 的定义

English:
definition ι
  signature: {n : Nat} (i : Fin (n + 2)) (j : Fin (n + 2)) (hij : j != i)
  body: yonedaEquiv.symm (face i j hij)

中文:
定义 ι
  签名: {n : 自然数} (i : 有限集 (n + 2)) (j : 有限集 (n + 2)) (hij : j != i)
  定义体: yonedaEquiv.symm (face i j hij)

Depends on / 依赖: yonedaEquiv, yonedaEquiv.symm
-/
def ι {n : Nat} (i : Fin (n + 2)) (j : Fin (n + 2)) (hij : j != i) :
    Δ[n] ⟶ (Λ[n + 1, i] : SSet.{u}) :=
  yonedaEquiv.symm (face i j hij)

/--
lemma `yonedaEquiv_ι` / 引理 `yonedaEquiv_ι`

English:
lemma yonedaEquiv_ι
  given: {n : Nat} (i : Fin (n + 2)) (j : Fin (n + 2)) (hij : j != i)
  proof: by
  rw [ι]; rw [Equiv.apply_symm_apply]

@[reassoc (attr := simp)]

中文:
引理 yonedaEquiv_ι
  条件: {n : 自然数} (i : 有限集 (n + 2)) (j : 有限集 (n + 2)) (hij : j != i)
  证明: by
  rw [ι]; rw [Equiv.apply_symm_apply]

@[reassoc (attr := simp)]

Depends on / 依赖: Equiv.apply_symm_apply, apply_symm_apply
-/
lemma yonedaEquiv_ι {n : Nat} (i : Fin (n + 2)) (j : Fin (n + 2)) (hij : j != i) :
    yonedaEquiv (ι i j hij) = face i j hij := by
  rw [ι]; rw [Equiv.apply_symm_apply]

@[reassoc (attr := simp)]
/--
lemma `ι_ι` / 引理 `ι_ι`

English:
lemma ι_ι
  given: {n : Nat} (i : Fin (n + 2)) (j : Fin (n + 2)) (hij : j != i)
  proof: by
  rw [ι]; rw [face]; rw [Equiv.symm_apply_apply]; rw [Subfunctor.lift_ι]

@[reassoc (attr := simp)]

中文:
引理 ι_ι
  条件: {n : 自然数} (i : 有限集 (n + 2)) (j : 有限集 (n + 2)) (hij : j != i)
  证明: by
  rw [ι]; rw [face]; rw [Equiv.symm_apply_apply]; rw [Subfunctor.lift_ι]

@[reassoc (attr := simp)]

Depends on / 依赖: Equiv.symm_apply_apply, Subfunctor, Subfunctor.lift_, symm_apply_apply
-/
lemma ι_ι {n : Nat} (i : Fin (n + 2)) (j : Fin (n + 2)) (hij : j != i) :
    ι i j hij ≫ Λ[n + 1, i].ι =
      stdSimplex.{u}.δ j := by
  rw [ι]; rw [face]; rw [Equiv.symm_apply_apply]; rw [Subfunctor.lift_ι]

@[reassoc (attr := simp)]
/--
lemma `faceSingletonComplIso_inv_ι` / 引理 `faceSingletonComplIso_inv_ι`

English:
lemma faceSingletonComplIso_inv_ι
  given: {n : Nat} (i : Fin (n + 2)) (j : Fin (n + 2)) (hij : j != i)
  proof: by
  rw [← cancel_epi (stdSimplex.faceSingletonComplIso.{u} j).hom]; rw [Iso.hom_inv_id_assoc]
  rfl

中文:
引理 faceSingletonComplIso_inv_ι
  条件: {n : 自然数} (i : 有限集 (n + 2)) (j : 有限集 (n + 2)) (hij : j != i)
  证明: by
  rw [← cancel_epi (stdSimplex.faceSingletonComplIso.{u} j).hom]; rw [Iso.hom_inv_id_assoc]
  rfl

Depends on / 依赖: Iso.hom_inv_id_assoc, cancel_epi, faceSingletonComplIso, hom_inv_id_assoc, stdSimplex, stdSimplex.faceSingletonComplIso
-/
lemma faceSingletonComplIso_inv_ι {n : Nat} (i : Fin (n + 2)) (j : Fin (n + 2)) (hij : j != i) :
    (stdSimplex.faceSingletonComplIso.{u} j).inv ≫ ι i j hij = faceι i j hij := by
  rw [← cancel_epi (stdSimplex.faceSingletonComplIso.{u} j).hom]; rw [Iso.hom_inv_id_assoc]
  rfl

end horn

end SSet
