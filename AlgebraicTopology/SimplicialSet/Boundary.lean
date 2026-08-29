/-
Copyright (c) 2021 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin, Kim Morrison, Adam Topaz
-/
module

public import Mathlib.AlgebraicTopology.SimplicialSet.StdSimplex

/-!
# The boundary of the standard simplex

We introduce the boundary `∂Δ[n]` of the standard simplex `Δ[n]`.
(These notations become available by doing `open Simplicial`.)

## Future work

There isn't yet a complete API for simplices, boundaries, and horns.
As an example, we should have a function that constructs
from a non-surjective order-preserving function `Fin n → Fin n`
a morphism `Δ[n] ⟶ ∂Δ[n]`.


-/

@[expose] public section

universe u

open CategoryTheory Simplicial Opposite

namespace SSet

/--
Definition of `boundary` / `boundary` 的定义

English:
definition boundary
  signature: (n : Nat)
  body: Set.ofPred (fun s => ¬Function.Surjective (stdSimplex.asOrderHom s))
  map _ _ hs h := hs (Function.Surjective.of_comp h)

中文:
定义 boundary
  签名: (n : 自然数)
  定义体: Set.ofPred (fun s => ¬Function.Surjective (stdSimplex.asOrderHom s))
  map _ _ hs h := hs (Function.Surjective.of_comp h)

Depends on / 依赖: Function, Function.Surjective, Set.ofPred, Surjective, asOrderHom, ofPred, stdSimplex, stdSimplex.asOrderHom
-/
def boundary (n : Nat) : (Δ[n] : SSet.{u}).Subcomplex where
  obj _ := Set.ofPred (fun s => ¬Function.Surjective (stdSimplex.asOrderHom s))
  map _ _ hs h := hs (Function.Surjective.of_comp h)

/-- The boundary `∂Δ[n]` of the `n`-th standard simplex -/
scoped[Simplicial] notation3 "∂Δ[" n "]" => SSet.boundary n

/--
lemma `boundary_eq_iSup` / 引理 `boundary_eq_iSup`

English:
lemma boundary_eq_iSup
  given: (n : Nat)
  proof: by
  ext
  simp [stdSimplex.face_obj, boundary, Function.Surjective]
  tauto

中文:
引理 boundary_eq_iSup
  条件: (n : 自然数)
  证明: by
  ext
  simp [stdSimplex.face_obj, boundary, Function.Surjective]
  tauto

Depends on / 依赖: Function, Function.Surjective, Surjective, boundary, face_obj, stdSimplex, stdSimplex.face_obj
-/
lemma boundary_eq_iSup (n : Nat) :
    boundary.{u} n = ⨆ (i : Fin (n + 1)), stdSimplex.face {i}ᶜ := by
  ext
  simp [stdSimplex.face_obj, boundary, Function.Surjective]
  tauto

instance {n : Nat} : HasDimensionLT (boundary n) n := by
  rw [boundary_eq_iSup]; rw [hasDimensionLT_iSup_iff]
  intro i
  exact stdSimplex.hasDimensionLT_face _ _ (by simp [Finset.card_compl])

/--
lemma `mem_boundary_iff_notMem_range` / 引理 `mem_boundary_iff_notMem_range`

English:
lemma mem_boundary_iff_notMem_range
  given: {n d : Nat} (s : Δ[n] _⦋d⦌)
  proof: by
  rw [boundary_eq_iSup]
  simp

中文:
引理 mem_boundary_iff_notMem_range
  条件: {n d : 自然数} (s : Δ[n] _⦋d⦌)
  证明: by
  rw [boundary_eq_iSup]
  simp

Depends on / 依赖: boundary_eq_iSup
-/
lemma mem_boundary_iff_notMem_range {n d : Nat} (s : Δ[n] _⦋d⦌) :
    s in (boundary n).obj _ ↔ exists (j : Fin (n + 1)), j ∉ Set.range s := by
  rw [boundary_eq_iSup]
  simp

/--
lemma `face_singleton_compl_le_boundary` / 引理 `face_singleton_compl_le_boundary`

English:
lemma face_singleton_compl_le_boundary
  given: {n : Nat} (i : Fin (n + 1))
  proof: by
  rw [boundary_eq_iSup]
  exact le_iSup (fun (i : Fin (n +1)) => stdSimplex.face {i}ᶜ) i

中文:
引理 face_singleton_compl_le_boundary
  条件: {n : 自然数} (i : Fin (n + 1))
  证明: by
  rw [boundary_eq_iSup]
  exact le_iSup (fun (i : Fin (n +1)) => stdSimplex.face {i}ᶜ) i

Depends on / 依赖: boundary_eq_iSup, le_iSup, stdSimplex, stdSimplex.face
-/
lemma face_singleton_compl_le_boundary {n : Nat} (i : Fin (n + 1)) :
    stdSimplex.face.{u} {i}ᶜ <= boundary n := by
  rw [boundary_eq_iSup]
  exact le_iSup (fun (i : Fin (n +1)) => stdSimplex.face {i}ᶜ) i

/--
lemma `stdSimplex.notMem_boundary` / 引理 `stdSimplex.notMem_boundary`

English:
lemma stdSimplex.notMem_boundary
  given: (n : Nat)
  proof: by
  rw [boundary_eq_iSup]; rw [Subfunctor.iSup_obj]; rw [Set.mem_iUnion]; rw [not_exists]
  intro i hi
  simpa using @hi i (by aesop)

中文:
引理 stdSimplex.notMem_boundary
  条件: (n : 自然数)
  证明: by
  rw [boundary_eq_iSup]; rw [Subfunctor.iSup_obj]; rw [Set.mem_iUnion]; rw [not_exists]
  intro i hi
  simpa using @hi i (by aesop)

Depends on / 依赖: Set.mem_iUnion, Subfunctor, Subfunctor.iSup_obj, boundary, boundary_eq_iSup, iSup_obj, mem_iUnion, not_exists
-/
lemma stdSimplex.notMem_boundary (n : Nat) :
    stdSimplex.objMk (m := op ⦋n⦌) .id ∉ (boundary.{u} n).obj (op ⦋n⦌) := by
  rw [boundary_eq_iSup]; rw [Subfunctor.iSup_obj]; rw [Set.mem_iUnion]; rw [not_exists]
  intro i hi
  simpa using @hi i (by aesop)

/--
lemma `boundary_lt_top` / 引理 `boundary_lt_top`

English:
lemma boundary_lt_top
  given: (n : Nat)
  proof: lt_of_le_not_ge (by simp) (fun h => stdSimplex.notMem_boundary n (h _ (by simp)))

中文:
引理 boundary_lt_top
  条件: (n : 自然数)
  证明: lt_of_le_not_ge (by simp) (fun h => stdSimplex.notMem_boundary n (h _ (by simp)))

Depends on / 依赖: lt_of_le_not_ge, notMem_boundary, stdSimplex, stdSimplex.notMem_boundary
-/
lemma boundary_lt_top (n : Nat) :
    boundary.{u} n < ⊤ :=
  lt_of_le_not_ge (by simp) (fun h => stdSimplex.notMem_boundary n (h _ (by simp)))

/--
lemma `boundary_obj_eq_univ` / 引理 `boundary_obj_eq_univ`

English:
lemma boundary_obj_eq_univ
  given: (m n : Nat) (h : m < n := by lia)
  proof: by
  ext x
  obtain ⟨f, rfl⟩ := stdSimplex.objEquiv.symm.surjective x
  simp only [Set.mem_univ, iff_true]
  obtain _ | n := n
  · simp at h
  · obtain ⟨i, q, rfl⟩ := SimplexCategory.eq_comp_δ_of_not_surjective f (fun hf => by
      rw [← SimplexCategory.epi_iff_surjective] at hf
      have : n + 1 

中文:
引理 boundary_obj_eq_univ
  条件: (m n : 自然数) (h : m < n := by lia)
  证明: by
  ext x
  obtain ⟨f, rfl⟩ := stdSimplex.objEquiv.symm.surjective x
  simp only [Set.mem_univ, iff_true]
  obtain _ | n := n
  · simp at h
  · obtain ⟨i, q, rfl⟩ := SimplexCategory.eq_comp_δ_of_not_surjective f (fun hf => by
      rw [← SimplexCategory.epi_iff_surjective] at hf
      have : n + 1 

Depends on / 依赖: Set.mem_univ, SimplexCategory, SimplexCategory.epi_iff_surjective, SimplexCategory.eq_comp_, SimplexCategory.len_le_of_epi, Subcomp, boundary, epi_iff_surjective, face_singleton_compl, face_singleton_compl_le_boundary, iff_true, len_le_of_epi, mem_univ, objEquiv, objEquiv_symm_comp, stdSimplex, stdSimplex.face_singleton_compl, stdSimplex.objEquiv.symm.surjective, stdSimplex.objEquiv_symm_comp, surjective
-/
lemma boundary_obj_eq_univ (m n : Nat) (h : m < n := by lia) :
    (boundary.{u} n).obj (op ⦋m⦌) = .univ := by
  ext x
  obtain ⟨f, rfl⟩ := stdSimplex.objEquiv.symm.surjective x
  simp only [Set.mem_univ, iff_true]
  obtain _ | n := n
  · simp at h
  · obtain ⟨i, q, rfl⟩ := SimplexCategory.eq_comp_δ_of_not_surjective f (fun hf => by
      rw [← SimplexCategory.epi_iff_surjective] at hf
      have : n + 1 <= m := SimplexCategory.len_le_of_epi f
      lia)
    apply face_singleton_compl_le_boundary i
    rw [stdSimplex.face_singleton_compl]; rw [stdSimplex.objEquiv_symm_comp]; rw [← Subcomplex.ofSimplex_le_iff]
    apply Subcomplex.ofSimplex_map_le

@[simp]
/--
lemma `boundary_zero` / 引理 `boundary_zero`

English:
lemma boundary_zero
  statement: boundary.{u} 0 = ⊥
  proof: by
  ext m x
  simp only [boundary, Nat.reduceAdd, Set.mem_ofPred_eq, Subfunctor.bot_obj, Set.bot_eq_empty,
    Set.mem_empty_iff_false, iff_false, Decidable.not_not]
  intro x
  exact ⟨0, by subsingleton⟩

中文:
引理 boundary_zero
  结论: boundary.{u} 0 = ⊥
  证明: by
  ext m x
  simp only [boundary, Nat.reduceAdd, Set.mem_ofPred_eq, Subfunctor.bot_obj, Set.bot_eq_empty,
    Set.mem_empty_iff_false, iff_false, Decidable.not_not]
  intro x
  exact ⟨0, by subsingleton⟩

Depends on / 依赖: Decidable, Decidable.not_not, Nat.reduceAdd, Set.bot_eq_empty, Set.mem_empty_iff_false, Set.mem_ofPred_eq, Subfunctor, Subfunctor.bot_obj, bot_eq_empty, bot_obj, boundary, iff_false, mem_empty_iff_false, mem_ofPred_eq, not_not, reduceAdd, subsingleton
-/
lemma boundary_zero : boundary.{u} 0 = ⊥ := by
  ext m x
  simp only [boundary, Nat.reduceAdd, Set.mem_ofPred_eq, Subfunctor.bot_obj, Set.bot_eq_empty,
    Set.mem_empty_iff_false, iff_false, Decidable.not_not]
  intro x
  exact ⟨0, by subsingleton⟩

/--
lemma `op_boundary` / 引理 `op_boundary`

English:
lemma op_boundary
  given: (n : Nat)
  proof: by
  ext ⟨⟨d⟩⟩ j
  simp only [Subcomplex.preimage_obj, Set.mem_preimage, stdSimplex.opIso_inv_app_hom_apply,
    Subcomplex.mem_op_obj_iff, mem_boundary_iff_notMem_range, Set.mem_range,
    stdSimplex.opObjEquiv_opObjEquiv_symm_apply, not_exists]
  constructor
  all_goals
  · rintro ⟨k, hk⟩
    exac

中文:
引理 op_boundary
  条件: (n : 自然数)
  证明: by
  ext ⟨⟨d⟩⟩ j
  simp only [Subcomplex.preimage_obj, Set.mem_preimage, stdSimplex.opIso_inv_app_hom_apply,
    Subcomplex.mem_op_obj_iff, mem_boundary_iff_notMem_range, Set.mem_range,
    stdSimplex.opObjEquiv_opObjEquiv_symm_apply, not_exists]
  constructor
  all_goals
  · rintro ⟨k, hk⟩
    exac

Depends on / 依赖: Set.mem_preimage, Set.mem_range, Subcomplex, Subcomplex.mem_op_obj_iff, Subcomplex.preimage_obj, all_goals, k.rev, l.rev, mem_boundary_iff_notMem_range, mem_op_obj_iff, mem_preimage, mem_range, not_exists, opIso_inv_app_hom_apply, opObjEquiv_opObjEquiv_symm_apply, preimage_obj, stdSimplex, stdSimplex.opIso_inv_app_hom_apply, stdSimplex.opObjEquiv_opObjEquiv_symm_apply
-/
lemma op_boundary (n : Nat) :
    ∂Δ[n].op.preimage (stdSimplex.opIso.{u} ⦋n⦌).inv = ∂Δ[n] := by
  ext ⟨⟨d⟩⟩ j
  simp only [Subcomplex.preimage_obj, Set.mem_preimage, stdSimplex.opIso_inv_app_hom_apply,
    Subcomplex.mem_op_obj_iff, mem_boundary_iff_notMem_range, Set.mem_range,
    stdSimplex.opObjEquiv_opObjEquiv_symm_apply, not_exists]
  constructor
  all_goals
  · rintro ⟨k, hk⟩
    exact ⟨k.rev, fun l _ => hk l.rev (by aesop)⟩

namespace stdSimplex

variable {n : Nat} (A : (Δ[n] : SSet.{u}).Subcomplex)

set_option backward.isDefEq.respectTransparency false in
/--
lemma `subcomplex_hasDimensionLT_of_neq_top` / 引理 `subcomplex_hasDimensionLT_of_neq_top`

English:
lemma subcomplex_hasDimensionLT_of_neq_top
  given: (h : A != ⊤)
  proof: by
    ext ⟨a, ha⟩
    rw [A.mem_degenerate_iff]
    simp only [Set.top_eq_univ, Set.mem_univ, iff_true]
    obtain hi | rfl := hi.lt_or_eq
    · simp [Δ[n].degenerate_eq_univ_of_hasDimensionLT (n + 1) i]
    · rw [mem_degenerate_iff_notMem_nonDegenerate, nonDegenerate_top_dim]
      rintro rfl
    

中文:
引理 subcomplex_hasDimensionLT_of_neq_top
  条件: (h : A != ⊤)
  证明: by
    ext ⟨a, ha⟩
    rw [A.mem_degenerate_iff]
    simp only [Set.top_eq_univ, Set.mem_univ, iff_true]
    obtain hi | rfl := hi.lt_or_eq
    · simp [Δ[n].degenerate_eq_univ_of_hasDimensionLT (n + 1) i]
    · rw [mem_degenerate_iff_notMem_nonDegenerate, nonDegenerate_top_dim]
      rintro rfl
    

Depends on / 依赖: A.mem_degenerate_iff, Set.mem_univ, Set.top_eq_univ, degenerate_eq_univ_of_hasDimensionLT, hi.lt_or_eq, iff_true, le_antisymm, lt_or_eq, mem_degenerate_iff, mem_degenerate_iff_notMem_nonDegenerate, mem_univ, nonDegenerate_top_dim, ofSimplex_objEquiv_symm_id, top_eq_univ
-/
lemma subcomplex_hasDimensionLT_of_neq_top (h : A != ⊤) :
    HasDimensionLT A n where
  degenerate_eq_top i hi := by
    ext ⟨a, ha⟩
    rw [A.mem_degenerate_iff]
    simp only [Set.top_eq_univ, Set.mem_univ, iff_true]
    obtain hi | rfl := hi.lt_or_eq
    · simp [Δ[n].degenerate_eq_univ_of_hasDimensionLT (n + 1) i]
    · rw [mem_degenerate_iff_notMem_nonDegenerate, nonDegenerate_top_dim]
      rintro rfl
      exact h (le_antisymm (by simp) (by simpa [← ofSimplex_objEquiv_symm_id]))

set_option backward.isDefEq.respectTransparency false in
/--
lemma `le_boundary_iff` / 引理 `le_boundary_iff`

English:
lemma le_boundary_iff
  proof: by
  refine ⟨fun h => ?_, fun hA => ?_⟩
  · rintro rfl
    exact lt_irrefl _ (lt_of_le_of_lt h (boundary_lt_top n))
  · have := subcomplex_hasDimensionLT_of_neq_top A hA
    rw [Subcomplex.le_iff_contains_nonDegenerate]
    rintro m ⟨x, h₁⟩ h₂
    dsimp at h₂ ⊢
    by_cases! h₃ : m < n
    · simp [b

中文:
引理 le_boundary_iff
  证明: by
  refine ⟨fun h => ?_, fun hA => ?_⟩
  · rintro rfl
    exact lt_irrefl _ (lt_of_le_of_lt h (boundary_lt_top n))
  · have := subcomplex_hasDimensionLT_of_neq_top A hA
    rw [Subcomplex.le_iff_contains_nonDegenerate]
    rintro m ⟨x, h₁⟩ h₂
    dsimp at h₂ ⊢
    by_cases! h₃ : m < n
    · simp [b

Depends on / 依赖: A.mem_nonDegenerate_iff, Subcomplex, Subcomplex.le_iff_contains_nonDegenerate, boundary_lt_top, boundary_obj_eq_univ, le_iff_contains_nonDegenerate, lt_irrefl, lt_of_le_of_lt, mem_nonDegenerate_iff, nonDegenerate_eq_empty_of_hasDimensionLT, subcomplex_hasDimensionLT_of_neq_top
-/
lemma le_boundary_iff :
    A <= boundary.{u} n ↔ A != ⊤ := by
  refine ⟨fun h => ?_, fun hA => ?_⟩
  · rintro rfl
    exact lt_irrefl _ (lt_of_le_of_lt h (boundary_lt_top n))
  · have := subcomplex_hasDimensionLT_of_neq_top A hA
    rw [Subcomplex.le_iff_contains_nonDegenerate]
    rintro m ⟨x, h₁⟩ h₂
    dsimp at h₂ ⊢
    by_cases! h₃ : m < n
    · simp [boundary_obj_eq_univ m n h₃]
    · simp [← A.mem_nonDegenerate_iff ⟨x, h₂⟩,
        nonDegenerate_eq_empty_of_hasDimensionLT _ _ _ h₃] at h₁

/--
lemma `eq_boundary_iff` / 引理 `eq_boundary_iff`

English:
lemma eq_boundary_iff
  proof: by
  constructor
  · rintro rfl
    exact ⟨by rfl, (boundary_lt_top n).ne⟩
  · rintro ⟨h₁, h₂⟩
    exact le_antisymm (by rwa [le_boundary_iff]) h₁

中文:
引理 eq_boundary_iff
  证明: by
  constructor
  · rintro rfl
    exact ⟨by rfl, (boundary_lt_top n).ne⟩
  · rintro ⟨h₁, h₂⟩
    exact le_antisymm (by rwa [le_boundary_iff]) h₁

Depends on / 依赖: boundary_lt_top, le_antisymm, le_boundary_iff
-/
lemma eq_boundary_iff :
    A = boundary n ↔ boundary n <= A ∧ A != ⊤ := by
  constructor
  · rintro rfl
    exact ⟨by rfl, (boundary_lt_top n).ne⟩
  · rintro ⟨h₁, h₂⟩
    exact le_antisymm (by rwa [le_boundary_iff]) h₁

end stdSimplex

namespace boundary

/--
Definition of `faceι` / `faceι` 的定义

English:
definition faceι
  signature: {n : Nat} (i : Fin (n + 1))
  body: Subcomplex.homOfLE (face_singleton_compl_le_boundary i)

中文:
定义 faceι
  签名: {n : 自然数} (i : Fin (n + 1))
  定义体: Subcomplex.homOfLE (face_singleton_compl_le_boundary i)

Depends on / 依赖: Subcomplex, Subcomplex.homOfLE, face_singleton_compl_le_boundary, homOfLE
-/
def faceι {n : Nat} (i : Fin (n + 1)) :
    (stdSimplex.face {i}ᶜ : SSet.{u}) ⟶ ∂Δ[n] :=
  Subcomplex.homOfLE (face_singleton_compl_le_boundary i)

instance {n : Nat} (i : Fin (n + 1)) : Mono (faceι.{u} i) := by
  dsimp [faceι]; infer_instance

@[reassoc (attr := simp)]
/--
lemma `faceι_ι` / 引理 `faceι_ι`

English:
lemma faceι_ι
  given: {n : Nat} (i : Fin (n + 2))
  proof: by
  simp [faceι]

中文:
引理 faceι_ι
  条件: {n : 自然数} (i : Fin (n + 2))
  证明: by
  simp [faceι]
-/
lemma faceι_ι {n : Nat} (i : Fin (n + 2)) :
    faceι i ≫ (boundary.{u} (n + 1)).ι = (stdSimplex.face {i}ᶜ).ι := by
  simp [faceι]

/--
Definition of `ι` / `ι` 的定义

English:
definition ι
  signature: {n : Nat} (i : Fin (n + 2))
  body: Subcomplex.lift ((stdSimplex.{u}.map (SimplexCategory.δ i))) (by
    simp only [Subcomplex.range_eq_ofSimplex]
    refine le_trans ?_ (face_singleton_compl_le_boundary i)
    rw [stdSimplex.face_singleton_compl]; rw [yonedaEquiv_map])

@[reassoc (attr := simp)]

中文:
定义 ι
  签名: {n : 自然数} (i : Fin (n + 2))
  定义体: Subcomplex.lift ((stdSimplex.{u}.map (SimplexCategory.δ i))) (by
    simp only [Subcomplex.range_eq_ofSimplex]
    refine le_trans ?_ (face_singleton_compl_le_boundary i)
    rw [stdSimplex.face_singleton_compl]; rw [yonedaEquiv_map])

@[reassoc (attr := simp)]

Depends on / 依赖: SimplexCategory, Subcomplex, Subcomplex.lift, Subcomplex.range_eq_ofSimplex, face_singleton_compl, face_singleton_compl_le_boundary, le_trans, range_eq_ofSimplex, stdSimplex, stdSimplex.face_singleton_compl, yonedaEquiv_map
-/
def ι {n : Nat} (i : Fin (n + 2)) :
    Δ[n] ⟶ (∂Δ[n + 1] : SSet.{u}) :=
  Subcomplex.lift ((stdSimplex.{u}.map (SimplexCategory.δ i))) (by
    simp only [Subcomplex.range_eq_ofSimplex]
    refine le_trans ?_ (face_singleton_compl_le_boundary i)
    rw [stdSimplex.face_singleton_compl]; rw [yonedaEquiv_map])

@[reassoc (attr := simp)]
/--
lemma `ι_ι` / 引理 `ι_ι`

English:
lemma ι_ι
  given: {n : Nat} (i : Fin (n + 2))
  proof: rfl

@[reassoc (attr := simp)]

中文:
引理 ι_ι
  条件: {n : 自然数} (i : Fin (n + 2))
  证明: rfl

@[reassoc (attr := simp)]
-/
lemma ι_ι {n : Nat} (i : Fin (n + 2)) :
    ι.{u} i ≫ ∂Δ[n + 1].ι = stdSimplex.δ i := rfl

@[reassoc (attr := simp)]
/--
lemma `faceSingletonComplIso_inv_ι` / 引理 `faceSingletonComplIso_inv_ι`

English:
lemma faceSingletonComplIso_inv_ι
  given: {n : Nat} (i : Fin (n + 2))
  proof: by
  rw [← cancel_epi (stdSimplex.faceSingletonComplIso i).hom]; rw [Iso.hom_inv_id_assoc]
  rfl

中文:
引理 faceSingletonComplIso_inv_ι
  条件: {n : 自然数} (i : Fin (n + 2))
  证明: by
  rw [← cancel_epi (stdSimplex.faceSingletonComplIso i).hom]; rw [Iso.hom_inv_id_assoc]
  rfl

Depends on / 依赖: Iso.hom_inv_id_assoc, cancel_epi, faceSingletonComplIso, hom_inv_id_assoc, stdSimplex, stdSimplex.faceSingletonComplIso
-/
lemma faceSingletonComplIso_inv_ι {n : Nat} (i : Fin (n + 2)) :
    (stdSimplex.faceSingletonComplIso i).inv ≫ ι i = boundary.faceι i := by
  rw [← cancel_epi (stdSimplex.faceSingletonComplIso i).hom]; rw [Iso.hom_inv_id_assoc]
  rfl

instance {n : Nat} (i : Fin (n + 2)) : Mono (ι.{u} i) := by
  rw [← mono_comp_iff_of_isIso (stdSimplex.faceSingletonComplIso i).inv]; rw [faceSingletonComplIso_inv_ι]
  infer_instance

instance {n : Nat} (i : Fin (n + 2)) : Mono (stdSimplex.{u}.δ i) := by
  rw [← ι_ι]
  infer_instance

/--
lemma `hom_ext` / 引理 `hom_ext`

English:
lemma hom_ext
  statement: {n : Nat} {X : SSet.{u}} {f g : (∂Δ[n + 1] : SSet) ⟶ X}
  proof: by
  ext m ⟨x, hx⟩
  simp only [boundary_eq_iSup, stdSimplex.face_singleton_compl, Subfunctor.iSup_obj,
    Set.mem_iUnion, Subcomplex.mem_ofSimplex_obj_iff, op_unop] at hx
  obtain ⟨i, ⟨y, rfl⟩⟩ := hx
  exact ConcreteCategory.congr_hom (congr_app (h i) _) _

@[ext]

中文:
引理 hom_ext
  结论: {n : 自然数} {X : SSet.{u}} {f g : (∂Δ[n + 1] : SSet) ⟶ X}
  证明: by
  ext m ⟨x, hx⟩
  simp only [boundary_eq_iSup, stdSimplex.face_singleton_compl, Subfunctor.iSup_obj,
    Set.mem_iUnion, Subcomplex.mem_ofSimplex_obj_iff, op_unop] at hx
  obtain ⟨i, ⟨y, rfl⟩⟩ := hx
  exact ConcreteCategory.congr_hom (congr_app (h i) _) _

@[ext]

Depends on / 依赖: ConcreteCategory, ConcreteCategory.congr_hom, Set.mem_iUnion, Subcomplex, Subcomplex.mem_ofSimplex_obj_iff, Subfunctor, Subfunctor.iSup_obj, boundary_eq_iSup, congr_app, congr_hom, face_singleton_compl, iSup_obj, mem_iUnion, mem_ofSimplex_obj_iff, op_unop, stdSimplex, stdSimplex.face_singleton_compl
-/
lemma hom_ext {n : Nat} {X : SSet.{u}} {f g : (∂Δ[n + 1] : SSet) ⟶ X}
    (h : forall (i : Fin (n + 2)), ι i ≫ f = ι i ≫ g) :
    f = g := by
  ext m ⟨x, hx⟩
  simp only [boundary_eq_iSup, stdSimplex.face_singleton_compl, Subfunctor.iSup_obj,
    Set.mem_iUnion, Subcomplex.mem_ofSimplex_obj_iff, op_unop] at hx
  obtain ⟨i, ⟨y, rfl⟩⟩ := hx
  exact ConcreteCategory.congr_hom (congr_app (h i) _) _

@[ext]
/--
lemma `hom_ext₀` / 引理 `hom_ext₀`

English:
lemma hom_ext₀
  given: {X : SSet.{u}} {f g : (∂Δ[0] : SSet) ⟶ X}
  statement: f = g
  proof: by
  ext _ ⟨x, hx⟩
  simp at hx

中文:
引理 hom_ext₀
  条件: {X : SSet.{u}} {f g : (∂Δ[0] : SSet) ⟶ X}
  结论: f = g
  证明: by
  ext _ ⟨x, hx⟩
  simp at hx
-/
lemma hom_ext₀ {X : SSet.{u}} {f g : (∂Δ[0] : SSet) ⟶ X} : f = g := by
  ext _ ⟨x, hx⟩
  simp at hx

end boundary

end SSet
