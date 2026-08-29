/-
Copyright (c) 2022 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.AlgebraicTopology.DoldKan.Degeneracies
public import Mathlib.AlgebraicTopology.DoldKan.HomotopyEquivalence
public import Mathlib.AlgebraicTopology.SimplicialObject.Split

/-!

# Split simplicial objects in preadditive categories

In this file we define a functor `nondegComplex : SimplicialObject.Split C ⥤ ChainComplex C ℕ`
when `C` is a preadditive category with finite coproducts, and get an isomorphism
`toKaroubiNondegComplexFunctorIsoN₁ : nondegComplex ⋙ toKaroubi _ ≅ forget C ⋙ DoldKan.N₁`.

(See `Equivalence.lean` for the general strategy of proof of the Dold-Kan equivalence.)

-/

@[expose] public section


namespace CategoryTheory.SimplicialObject

open AlgebraicTopology Limits Category Preadditive Idempotents Opposite DoldKan Simplicial

namespace Splitting

variable {C : Type*} [Category* C] {X : SimplicialObject C}
  (s : Splitting X)

/--
Definition of `πSummand` / `πSummand` 的定义

English:
definition πSummand
  signature: [HasZeroMorphisms C] {Δ : SimplexCategoryᵒᵖ} (A : IndexSet Δ)
  body: s.desc Δ (fun B => by
    by_cases h : B = A
    · exact eqToHom (by subst h; rfl)
    · exact 0)

中文:
定义 πSummand
  签名: [有ZeroMorphisms C] {Δ : SimplexCategoryᵒᵖ} (A : IndexSet Δ)
  定义体: s.desc Δ (fun B => by
    by_cases h : B = A
    · exact eqToHom (by subst h; rfl)
    · exact 0)

Depends on / 依赖: eqToHom, s.desc
-/
noncomputable def πSummand [HasZeroMorphisms C] {Δ : SimplexCategoryᵒᵖ} (A : IndexSet Δ) :
    X.obj Δ ⟶ s.N A.1.unop.len :=
  s.desc Δ (fun B => by
    by_cases h : B = A
    · exact eqToHom (by subst h; rfl)
    · exact 0)

set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
/--
theorem `cofan_inj_πSummand_eq_id` / 定理 `cofan_inj_πSummand_eq_id`

English:
theorem cofan_inj_πSummand_eq_id
  given: [HasZeroMorphisms C] {Δ : SimplexCategoryᵒᵖ} (A : IndexSet Δ)
  proof: by
  simp [πSummand]

中文:
定理 cofan_inj_πSummand_eq_id
  条件: [有ZeroMorphisms C] {Δ : SimplexCategoryᵒᵖ} (A : IndexSet Δ)
  证明: by
  simp [πSummand]
-/
theorem cofan_inj_πSummand_eq_id [HasZeroMorphisms C] {Δ : SimplexCategoryᵒᵖ} (A : IndexSet Δ) :
    (s.cofan Δ).inj A ≫ s.πSummand A = 𝟙 _ := by
  simp [πSummand]

set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
/--
theorem `cofan_inj_πSummand_eq_zero` / 定理 `cofan_inj_πSummand_eq_zero`

English:
theorem cofan_inj_πSummand_eq_zero
  statement: [HasZeroMorphisms C] {Δ : SimplexCategoryᵒᵖ} (A B : IndexSet Δ)
  proof: by
  dsimp [πSummand]
  rw [ι_desc]; rw [dif_neg h.symm]

中文:
定理 cofan_inj_πSummand_eq_zero
  结论: [有ZeroMorphisms C] {Δ : SimplexCategoryᵒᵖ} (A B : IndexSet Δ)
  证明: by
  dsimp [πSummand]
  rw [ι_desc]; rw [dif_neg h.symm]

Depends on / 依赖: dif_neg, h.symm
-/
theorem cofan_inj_πSummand_eq_zero [HasZeroMorphisms C] {Δ : SimplexCategoryᵒᵖ} (A B : IndexSet Δ)
    (h : B != A) : (s.cofan Δ).inj A ≫ s.πSummand B = 0 := by
  dsimp [πSummand]
  rw [ι_desc]; rw [dif_neg h.symm]

variable [Preadditive C]

set_option backward.isDefEq.respectTransparency false in
/--
theorem `decomposition_id` / 定理 `decomposition_id`

English:
theorem decomposition_id
  given: (Δ : SimplexCategoryᵒᵖ)
  proof: by
  apply s.hom_ext'
  intro A
  dsimp
  erw [comp_id, comp_sum, Finset.sum_eq_single A, cofan_inj_πSummand_eq_id_assoc]
  · intro B _ h₂
    rw [s.cofan_inj_πSummand_eq_zero_assoc _ _ h₂]; rw [zero_comp]
  · simp

中文:
定理 decomposition_id
  条件: (Δ : SimplexCategoryᵒᵖ)
  证明: by
  apply s.hom_ext'
  intro A
  dsimp
  erw [comp_id, comp_sum, Finset.sum_eq_single A, cofan_inj_πSummand_eq_id_assoc]
  · intro B _ h₂
    rw [s.cofan_inj_πSummand_eq_zero_assoc _ _ h₂]; rw [zero_comp]
  · simp

Depends on / 依赖: Finset, Finset.sum_eq_single, comp_id, comp_sum, hom_ext, s.cofan_inj_, s.hom_ext, sum_eq_single, zero_comp
-/
theorem decomposition_id (Δ : SimplexCategoryᵒᵖ) :
    𝟙 (X.obj Δ) = ∑ A : IndexSet Δ, s.πSummand A ≫ (s.cofan Δ).inj A := by
  apply s.hom_ext'
  intro A
  dsimp
  erw [comp_id, comp_sum, Finset.sum_eq_single A, cofan_inj_πSummand_eq_id_assoc]
  · intro B _ h₂
    rw [s.cofan_inj_πSummand_eq_zero_assoc _ _ h₂]; rw [zero_comp]
  · simp

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
/--
theorem `σ_comp_πSummand_id_eq_zero` / 定理 `σ_comp_πSummand_id_eq_zero`

English:
theorem σ_comp_πSummand_id_eq_zero
  given: {n : Nat} (i : Fin (n + 1))
  proof: by
  apply s.hom_ext'
  intro A
  dsimp only [SimplicialObject.σ]
  rw [comp_zero]; rw [s.cofan_inj_epi_naturality_assoc A (SimplexCategory.σ i).op]; rw [cofan_inj_πSummand_eq_zero]
  rw [ne_comm]
  change ¬(A.epiComp (SimplexCategory.σ i).op).EqId
  rw [IndexSet.eqId_iff_len_eq]
  have h := Simplex

中文:
定理 σ_comp_πSummand_id_eq_zero
  条件: {n : 自然数} (i : 有限集 (n + 1))
  证明: by
  apply s.hom_ext'
  intro A
  dsimp only [SimplicialObject.σ]
  rw [comp_zero]; rw [s.cofan_inj_epi_naturality_assoc A (SimplexCategory.σ i).op]; rw [cofan_inj_πSummand_eq_zero]
  rw [ne_comm]
  change ¬(A.epiComp (SimplexCategory.σ i).op).EqId
  rw [IndexSet.eqId_iff_len_eq]
  have h := Simplex

Depends on / 依赖: A.epiComp, IndexSet, IndexSet.eqId_iff_len_eq, SimplexCategory, SimplexCategory.len_le_of_epi, SimplicialObject, cofan_inj_epi_naturality_assoc, comp_zero, epiComp, eqId_iff_len_eq, hom_ext, len_le_of_epi, ne_comm, s.cofan_inj_epi_naturality_assoc, s.hom_ext
-/
theorem σ_comp_πSummand_id_eq_zero {n : Nat} (i : Fin (n + 1)) :
    X.σ i ≫ s.πSummand (IndexSet.id (op ⦋n + 1⦌)) = 0 := by
  apply s.hom_ext'
  intro A
  dsimp only [SimplicialObject.σ]
  rw [comp_zero]; rw [s.cofan_inj_epi_naturality_assoc A (SimplexCategory.σ i).op]; rw [cofan_inj_πSummand_eq_zero]
  rw [ne_comm]
  change ¬(A.epiComp (SimplexCategory.σ i).op).EqId
  rw [IndexSet.eqId_iff_len_eq]
  have h := SimplexCategory.len_le_of_epi A.e
  dsimp at h ⊢
  lia

set_option backward.isDefEq.respectTransparency false in
/--
theorem `cofan_inj_comp_PInfty_eq_zero` / 定理 `cofan_inj_comp_PInfty_eq_zero`

English:
theorem cofan_inj_comp_PInfty_eq_zero
  statement: {X : SimplicialObject C} (s : SimplicialObject.Splitting X)
  proof: by
  rw [SimplicialObject.Splitting.IndexSet.eqId_iff_mono] at hA
  rw [SimplicialObject.Splitting.cofan_inj_eq]; rw [assoc]; rw [degeneracy_comp_PInfty X n A.e hA]; rw [comp_zero]

中文:
定理 cofan_inj_comp_PInfty_eq_zero
  结论: {X : SimplicialObject C} (s : SimplicialObject.Splitting X)
  证明: by
  rw [SimplicialObject.Splitting.IndexSet.eqId_iff_mono] at hA
  rw [SimplicialObject.Splitting.cofan_inj_eq]; rw [assoc]; rw [degeneracy_comp_PInfty X n A.e hA]; rw [comp_zero]

Depends on / 依赖: IndexSet, SimplicialObject, SimplicialObject.Splitting.IndexSet.eqId_iff_mono, SimplicialObject.Splitting.cofan_inj_eq, Splitting, cofan_inj_eq, comp_zero, degeneracy_comp_PInfty, eqId_iff_mono
-/
theorem cofan_inj_comp_PInfty_eq_zero {X : SimplicialObject C} (s : SimplicialObject.Splitting X)
    {n : Nat} (A : SimplicialObject.Splitting.IndexSet (op ⦋n⦌)) (hA : ¬A.EqId) :
    (s.cofan _).inj A ≫ PInfty.f n = 0 := by
  rw [SimplicialObject.Splitting.IndexSet.eqId_iff_mono] at hA
  rw [SimplicialObject.Splitting.cofan_inj_eq]; rw [assoc]; rw [degeneracy_comp_PInfty X n A.e hA]; rw [comp_zero]

set_option backward.isDefEq.respectTransparency false in
/--
theorem `comp_PInfty_eq_zero_iff` / 定理 `comp_PInfty_eq_zero_iff`

English:
theorem comp_PInfty_eq_zero_iff
  given: {Z : C} {n : Nat} (f : Z ⟶ X _⦋n⦌)
  proof: by
  constructor
  · intro h
    rcases n with _ | n
    · dsimp at h
      rw [comp_id] at h
      rw [h]; rw [zero_comp]
    · have h' := f ≫= PInfty_f_add_QInfty_f (n + 1)
      dsimp at h'
      rw [comp_id]; rw [comp_add]; rw [h]; rw [zero_add] at h'
      rw [← h']; rw [assoc]; rw [QInfty_f]; 

中文:
定理 comp_PInfty_eq_zero_iff
  条件: {Z : C} {n : 自然数} (f : Z ⟶ X _⦋n⦌)
  证明: by
  constructor
  · intro h
    rcases n with _ | n
    · dsimp at h
      rw [comp_id] at h
      rw [h]; rw [zero_comp]
    · have h' := f ≫= PInfty_f_add_QInfty_f (n + 1)
      dsimp at h'
      rw [comp_id]; rw [comp_add]; rw [h]; rw [zero_add] at h'
      rw [← h']; rw [assoc]; rw [QInfty_f]; 

Depends on / 依赖: Finset, Finset.sum_eq_zero, PInfty_f_add_QInfty_f, Preadditiv, Preadditive, Preadditive.comp_sum, Preadditive.sum_comp, QInfty_f, comp_add, comp_id, comp_sum, comp_zero, decomposition_Q, decomposition_id, s.decomposition_id, sum_comp, sum_eq_zero, zero_add, zero_comp
-/
theorem comp_PInfty_eq_zero_iff {Z : C} {n : Nat} (f : Z ⟶ X _⦋n⦌) :
    f ≫ PInfty.f n = 0 ↔ f ≫ s.πSummand (IndexSet.id (op ⦋n⦌)) = 0 := by
  constructor
  · intro h
    rcases n with _ | n
    · dsimp at h
      rw [comp_id] at h
      rw [h]; rw [zero_comp]
    · have h' := f ≫= PInfty_f_add_QInfty_f (n + 1)
      dsimp at h'
      rw [comp_id]; rw [comp_add]; rw [h]; rw [zero_add] at h'
      rw [← h']; rw [assoc]; rw [QInfty_f]; rw [decomposition_Q]; rw [Preadditive.sum_comp]; rw [Preadditive.comp_sum]; rw [Finset.sum_eq_zero]
      intro i _
      simp only [assoc, σ_comp_πSummand_id_eq_zero, comp_zero]
  · intro h
    rw [← comp_id f]; rw [assoc]; rw [s.decomposition_id]; rw [Preadditive.sum_comp]; rw [Preadditive.comp_sum]; rw [Fintype.sum_eq_zero]
    intro A
    by_cases hA : A.EqId
    · dsimp at hA
      subst hA
      rw [assoc]; rw [reassoc_of% h]; rw [zero_comp]
    · simp only [assoc, s.cofan_inj_comp_PInfty_eq_zero A hA, comp_zero]

set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
/--
theorem `PInfty_comp_πSummand_id` / 定理 `PInfty_comp_πSummand_id`

English:
theorem PInfty_comp_πSummand_id
  given: (n : Nat)
  proof: by
  conv_rhs => rw [← id_comp (s.πSummand _)]
  symm
  rw [← sub_eq_zero]; rw [← sub_comp]; rw [← comp_PInfty_eq_zero_iff]; rw [sub_comp]; rw [id_comp]; rw [PInfty_f_idem]; rw [sub_self]

中文:
定理 PInfty_comp_πSummand_id
  条件: (n : 自然数)
  证明: by
  conv_rhs => rw [← id_comp (s.πSummand _)]
  symm
  rw [← sub_eq_zero]; rw [← sub_comp]; rw [← comp_PInfty_eq_zero_iff]; rw [sub_comp]; rw [id_comp]; rw [PInfty_f_idem]; rw [sub_self]

Depends on / 依赖: PInfty_f_idem, comp_PInfty_eq_zero_iff, conv_rhs, id_comp, sub_comp, sub_eq_zero, sub_self
-/
theorem PInfty_comp_πSummand_id (n : Nat) :
    PInfty.f n ≫ s.πSummand (IndexSet.id (op ⦋n⦌)) = s.πSummand (IndexSet.id (op ⦋n⦌)) := by
  conv_rhs => rw [← id_comp (s.πSummand _)]
  symm
  rw [← sub_eq_zero]; rw [← sub_comp]; rw [← comp_PInfty_eq_zero_iff]; rw [sub_comp]; rw [id_comp]; rw [PInfty_f_idem]; rw [sub_self]

set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
/--
theorem `πSummand_comp_cofan_inj_id_comp_PInfty_eq_PInfty` / 定理 `πSummand_comp_cofan_inj_id_comp_PInfty_eq_PInfty`

English:
theorem πSummand_comp_cofan_inj_id_comp_PInfty_eq_PInfty
  given: (n : Nat)
  proof: by
  conv_rhs => rw [← id_comp (PInfty.f n)]
  dsimp only [AlternatingFaceMapComplex.obj_X]
  rw [s.decomposition_id]; rw [Preadditive.sum_comp]
  rw [Fintype.sum_eq_single (IndexSet.id (op ⦋n⦌))]; rw [assoc]
  rintro A (hA : ¬A.EqId)
  rw [assoc]; rw [s.cofan_inj_comp_PInfty_eq_zero A hA]; rw [comp

中文:
定理 πSummand_comp_cofan_inj_id_comp_PInfty_eq_PInfty
  条件: (n : 自然数)
  证明: by
  conv_rhs => rw [← id_comp (PInfty.f n)]
  dsimp only [AlternatingFaceMapComplex.obj_X]
  rw [s.decomposition_id]; rw [Preadditive.sum_comp]
  rw [Fintype.sum_eq_single (IndexSet.id (op ⦋n⦌))]; rw [assoc]
  rintro A (hA : ¬A.EqId)
  rw [assoc]; rw [s.cofan_inj_comp_PInfty_eq_zero A hA]; rw [comp

Depends on / 依赖: A.EqId, AlternatingFaceMapComplex, AlternatingFaceMapComplex.obj_X, Fintype, Fintype.sum_eq_single, IndexSet, IndexSet.id, PInfty, PInfty.f, Preadditive, Preadditive.sum_comp, cofan_inj_comp_PInfty_eq_zero, comp_zero, conv_rhs, decomposition_id, id_comp, obj_X, s.cofan_inj_comp_PInfty_eq_zero, s.decomposition_id, sum_comp
-/
theorem πSummand_comp_cofan_inj_id_comp_PInfty_eq_PInfty (n : Nat) :
    s.πSummand (IndexSet.id (op ⦋n⦌)) ≫ (s.cofan _).inj (IndexSet.id (op ⦋n⦌)) ≫ PInfty.f n =
      PInfty.f n := by
  conv_rhs => rw [← id_comp (PInfty.f n)]
  dsimp only [AlternatingFaceMapComplex.obj_X]
  rw [s.decomposition_id]; rw [Preadditive.sum_comp]
  rw [Fintype.sum_eq_single (IndexSet.id (op ⦋n⦌))]; rw [assoc]
  rintro A (hA : ¬A.EqId)
  rw [assoc]; rw [s.cofan_inj_comp_PInfty_eq_zero A hA]; rw [comp_zero]

/-- The differentials `s.d i j : s.N i ⟶ s.N j` on nondegenerate simplices of a split
simplicial object are induced by the differentials on the alternating face map complex. -/
@[simp]
/--
Definition of `d` / `d` 的定义

English:
definition d
  signature: (i j : Nat)
  body: (s.cofan _).inj (IndexSet.id (op ⦋i⦌)) ≫ K[X].d i j ≫ s.πSummand (IndexSet.id (op ⦋j⦌))

中文:
定义 d
  签名: (i j : 自然数)
  定义体: (s.cofan _).inj (IndexSet.id (op ⦋i⦌)) ≫ K[X].d i j ≫ s.πSummand (IndexSet.id (op ⦋j⦌))

Depends on / 依赖: IndexSet, IndexSet.id, s.cofan
-/
noncomputable def d (i j : Nat) : s.N i ⟶ s.N j :=
  (s.cofan _).inj (IndexSet.id (op ⦋i⦌)) ≫ K[X].d i j ≫ s.πSummand (IndexSet.id (op ⦋j⦌))

set_option backward.isDefEq.respectTransparency false in
/--
theorem `ιSummand_comp_d_comp_πSummand_eq_zero` / 定理 `ιSummand_comp_d_comp_πSummand_eq_zero`

English:
theorem ιSummand_comp_d_comp_πSummand_eq_zero
  given: (j k : Nat) (A : IndexSet (op ⦋j⦌)) (hA : ¬A.EqId)
  proof: by
  rw [A.eqId_iff_mono] at hA
  rw [← assoc]; rw [← s.comp_PInfty_eq_zero_iff]; rw [assoc]; rw [← PInfty.comm j k]; rw [s.cofan_inj_eq]; rw [assoc]; rw [degeneracy_comp_PInfty_assoc X j A.e hA]; rw [zero_comp]; rw [comp_zero]

中文:
定理 ιSummand_comp_d_comp_πSummand_eq_zero
  条件: (j k : 自然数) (A : IndexSet (op ⦋j⦌)) (hA : ¬A.EqId)
  证明: by
  rw [A.eqId_iff_mono] at hA
  rw [← assoc]; rw [← s.comp_PInfty_eq_zero_iff]; rw [assoc]; rw [← PInfty.comm j k]; rw [s.cofan_inj_eq]; rw [assoc]; rw [degeneracy_comp_PInfty_assoc X j A.e hA]; rw [zero_comp]; rw [comp_zero]

Depends on / 依赖: A.eqId_iff_mono, PInfty, PInfty.comm, cofan_inj_eq, comp_PInfty_eq_zero_iff, comp_zero, degeneracy_comp_PInfty_assoc, eqId_iff_mono, s.cofan_inj_eq, s.comp_PInfty_eq_zero_iff, zero_comp
-/
theorem ιSummand_comp_d_comp_πSummand_eq_zero (j k : Nat) (A : IndexSet (op ⦋j⦌)) (hA : ¬A.EqId) :
    (s.cofan _).inj A ≫ K[X].d j k ≫ s.πSummand (IndexSet.id (op ⦋k⦌)) = 0 := by
  rw [A.eqId_iff_mono] at hA
  rw [← assoc]; rw [← s.comp_PInfty_eq_zero_iff]; rw [assoc]; rw [← PInfty.comm j k]; rw [s.cofan_inj_eq]; rw [assoc]; rw [degeneracy_comp_PInfty_assoc X j A.e hA]; rw [zero_comp]; rw [comp_zero]

set_option backward.isDefEq.respectTransparency false in
/-- If `s` is a splitting of a simplicial object `X` in a preadditive category,
`s.nondegComplex` is a chain complex which is given in degree `n` by
the nondegenerate `n`-simplices of `X`. This chain complex should be thought
as the normalized chain complex of `X` because of the isomorphism
`toKaroubiNondegComplexIsoN₁`. -/
@[simps]
/--
Definition of `nondegComplex` / `nondegComplex` 的定义

English:
definition nondegComplex
  signature: : ChainComplex C Nat where
  body: s.N
  d := s.d
  shape i j hij := by simp only [d, K[X].shape i j hij, zero_comp, comp_zero]
  d_comp_d' i j k _ _ := by
    simp only [d, assoc]
    have eq : K[X].d i j ≫ 𝟙 (X.obj (op ⦋j⦌)) ≫ K[X].d j k ≫
        s.πSummand (IndexSet.id (op ⦋k⦌)) = 0 := by
      simp
    rw [s.decomposition_id] at

中文:
定义 nondegComplex
  签名: : 链复形 C 自然数 where
  定义体: s.N
  d := s.d
  shape i j hij := by simp only [d, K[X].shape i j hij, zero_comp, comp_zero]
  d_comp_d' i j k _ _ := by
    simp only [d, assoc]
    have eq : K[X].d i j ≫ 𝟙 (X.obj (op ⦋j⦌)) ≫ K[X].d j k ≫
        s.πSummand (IndexSet.id (op ⦋k⦌)) = 0 := by
      simp
    rw [s.decomposition_id] at
-/
noncomputable def nondegComplex : ChainComplex C Nat where
  X := s.N
  d := s.d
  shape i j hij := by simp only [d, K[X].shape i j hij, zero_comp, comp_zero]
  d_comp_d' i j k _ _ := by
    simp only [d, assoc]
    have eq : K[X].d i j ≫ 𝟙 (X.obj (op ⦋j⦌)) ≫ K[X].d j k ≫
        s.πSummand (IndexSet.id (op ⦋k⦌)) = 0 := by
      simp
    rw [s.decomposition_id] at eq
    classical
    rw [Fintype.sum_eq_add_sum_compl (IndexSet.id (op ⦋j⦌))]; rw [add_comp]; rw [comp_add]; rw [assoc]; rw [Preadditive.sum_comp]; rw [Preadditive.comp_sum]; rw [Finset.sum_eq_zero]; rw [add_zero] at eq
    swap
    · intro A hA
      simp only [Finset.mem_compl, Finset.mem_singleton] at hA
      simp only [assoc, ιSummand_comp_d_comp_πSummand_eq_zero _ _ _ _ hA, comp_zero]
    rw [eq]; rw [comp_zero]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The chain complex `s.nondegComplex` attached to a splitting of a simplicial object `X`
becomes isomorphic to the normalized Moore complex `N₁.obj X` defined as a formal direct
factor in the category `Karoubi (ChainComplex C ℕ)`. -/
@[simps]
/--
Definition of `toKaroubiNondegComplexIsoN₁` / `toKaroubiNondegComplexIsoN₁` 的定义

English:
definition toKaroubiNondegComplexIsoN₁
  signature: :
  body: { f :=
        { f := fun n => (s.cofan _).inj (IndexSet.id (op ⦋n⦌)) ≫ PInfty.f n
          comm' := fun i j _ => by
            dsimp
            rw [assoc]; rw [assoc]; rw [assoc]; rw [πSummand_comp_cofan_inj_id_comp_PInfty_eq_PInfty]; rw [HomologicalComplex.Hom.comm] }
      comm := by
        e

中文:
定义 toKaroubiNondegComplexIsoN₁
  签名: :
  定义体: { f :=
        { f := fun n => (s.cofan _).inj (IndexSet.id (op ⦋n⦌)) ≫ PInfty.f n
          comm' := fun i j _ => by
            dsimp
            rw [assoc]; rw [assoc]; rw [assoc]; rw [πSummand_comp_cofan_inj_id_comp_PInfty_eq_PInfty]; rw [HomologicalComplex.Hom.comm] }
      comm := by
        e

Depends on / 依赖: AlternatingFaceMapComplex, AlternatingFaceMapComplex.obj_X, HomologicalComplex, HomologicalComplex.Hom.comm, IndexSet, IndexSet.id, PInfty, PInfty.f, PInfty_f_idem, decompo, id_comp, obj_X, s.cofan, s.decompo, slice_rhs
-/
noncomputable def toKaroubiNondegComplexIsoN₁ :
    (toKaroubi _).obj s.nondegComplex ≅ N₁.obj X where
  hom :=
    { f :=
        { f := fun n => (s.cofan _).inj (IndexSet.id (op ⦋n⦌)) ≫ PInfty.f n
          comm' := fun i j _ => by
            dsimp
            rw [assoc]; rw [assoc]; rw [assoc]; rw [πSummand_comp_cofan_inj_id_comp_PInfty_eq_PInfty]; rw [HomologicalComplex.Hom.comm] }
      comm := by
        ext n
        dsimp
        rw [id_comp]; rw [assoc]; rw [PInfty_f_idem] }
  inv :=
    { f :=
        { f := fun n => s.πSummand (IndexSet.id (op ⦋n⦌))
          comm' := fun i j _ => by
            dsimp
            slice_rhs 1 1 => rw [← id_comp (K[X].d i j)]
            dsimp only [AlternatingFaceMapComplex.obj_X]
            rw [s.decomposition_id]; rw [sum_comp]; rw [sum_comp]; rw [Finset.sum_eq_single (IndexSet.id (op ⦋i⦌))]; rw [assoc]; rw [assoc]
            · intro A _ hA
              simp only [assoc, s.ιSummand_comp_d_comp_πSummand_eq_zero _ _ _ hA, comp_zero]
            · simp only [Finset.mem_univ, not_true, IsEmpty.forall_iff] }
      comm := by
        ext n
        dsimp
        simp only [comp_id, PInfty_comp_πSummand_id] }
  hom_inv_id := by
    ext n
    simp only [assoc, PInfty_comp_πSummand_id, Karoubi.comp_f, HomologicalComplex.comp_f,
      cofan_inj_πSummand_eq_id]
    rfl
  inv_hom_id := by
    ext n
    simp only [πSummand_comp_cofan_inj_id_comp_PInfty_eq_PInfty, Karoubi.comp_f,
      HomologicalComplex.comp_f, N₁_obj_p, Karoubi.id_f]

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
@[reassoc (attr := simp)]
/--
lemma `toKaroubiNondegComplexIsoN₁_hom_f_PInfty` / 引理 `toKaroubiNondegComplexIsoN₁_hom_f_PInfty`

English:
lemma toKaroubiNondegComplexIsoN₁_hom_f_PInfty
  proof: by
  simpa using s.toKaroubiNondegComplexIsoN₁.hom.comm

中文:
引理 toKaroubiNondegComplexIsoN₁_hom_f_PInfty
  证明: by
  simpa using s.toKaroubiNondegComplexIsoN₁.hom.comm

Depends on / 依赖: hom.comm, s.toKaroubiNondegComplexIsoN
-/
lemma toKaroubiNondegComplexIsoN₁_hom_f_PInfty :
    dsimp% s.toKaroubiNondegComplexIsoN₁.hom.f ≫ PInfty =
      s.toKaroubiNondegComplexIsoN₁.hom.f := by
  simpa using s.toKaroubiNondegComplexIsoN₁.hom.comm

set_option backward.defeqAttrib.useBackward true in
@[reassoc (attr := simp)]
/--
lemma `toKaroubiNondegComplexIsoN₁_hom_inv_id_f` / 引理 `toKaroubiNondegComplexIsoN₁_hom_inv_id_f`

English:
lemma toKaroubiNondegComplexIsoN₁_hom_inv_id_f
  proof: by
  rw [← dsimp% [-Karoubi.comp_f] Karoubi.comp_f s.toKaroubiNondegComplexIsoN₁.hom
    s.toKaroubiNondegComplexIsoN₁.inv, Iso.hom_inv_id]
  simp

中文:
引理 toKaroubiNondegComplexIsoN₁_hom_inv_id_f
  证明: by
  rw [← dsimp% [-Karoubi.comp_f] Karoubi.comp_f s.toKaroubiNondegComplexIsoN₁.hom
    s.toKaroubiNondegComplexIsoN₁.inv, Iso.hom_inv_id]
  simp

Depends on / 依赖: Iso.hom_inv_id, Karoubi, Karoubi.comp_f, comp_f, hom_inv_id, s.toKaroubiNondegComplexIsoN
-/
lemma toKaroubiNondegComplexIsoN₁_hom_inv_id_f :
    dsimp% s.toKaroubiNondegComplexIsoN₁.hom.f ≫ s.toKaroubiNondegComplexIsoN₁.inv.f = 𝟙 _ := by
  rw [← dsimp% [-Karoubi.comp_f] Karoubi.comp_f s.toKaroubiNondegComplexIsoN₁.hom
    s.toKaroubiNondegComplexIsoN₁.inv, Iso.hom_inv_id]
  simp

set_option backward.defeqAttrib.useBackward true in
/-- Given a splitting `s` of a simplicial object `X` in a preadditive category,
this is the split epimorphism from the alternating face map complex of `X` to the chain
complex `s.nondegComplex`. -/
@[no_expose]
/--
Definition of `toNondegComplex` / `toNondegComplex` 的定义

English:
definition toNondegComplex
  signature: : K[X] ⟶ s.nondegComplex
  body: (fullyFaithfulToKaroubi _).preimage
    ({ f := by exact PInfty } ≫ s.toKaroubiNondegComplexIsoN₁.inv)

中文:
定义 toNondegComplex
  签名: : K[X] ⟶ s.nondegComplex
  定义体: (fullyFaithfulToKaroubi _).preimage
    ({ f := by exact PInfty } ≫ s.toKaroubiNondegComplexIsoN₁.inv)

Depends on / 依赖: PInfty, fullyFaithfulToKaroubi, preimage, s.toKaroubiNondegComplexIsoN
-/
noncomputable def toNondegComplex : K[X] ⟶ s.nondegComplex :=
  (fullyFaithfulToKaroubi _).preimage
    ({ f := by exact PInfty } ≫ s.toKaroubiNondegComplexIsoN₁.inv)

set_option backward.defeqAttrib.useBackward true in
/-- Given a splitting `s` of a simplicial object `X` in a preadditive category,
this is the split monomormphism from the chain complex `s.nondegComplex` to
the alternating face map complex of `X`. -/
@[no_expose]
/--
Definition of `fromNondegComplex` / `fromNondegComplex` 的定义

English:
definition fromNondegComplex
  signature: : s.nondegComplex ⟶ K[X]
  body: (fullyFaithfulToKaroubi _).preimage
    (s.toKaroubiNondegComplexIsoN₁.hom ≫ { f := PInfty })

中文:
定义 fromNondegComplex
  签名: : s.nondegComplex ⟶ K[X]
  定义体: (fullyFaithfulToKaroubi _).preimage
    (s.toKaroubiNondegComplexIsoN₁.hom ≫ { f := PInfty })

Depends on / 依赖: PInfty, fullyFaithfulToKaroubi, preimage, s.toKaroubiNondegComplexIsoN
-/
noncomputable def fromNondegComplex : s.nondegComplex ⟶ K[X] :=
  (fullyFaithfulToKaroubi _).preimage
    (s.toKaroubiNondegComplexIsoN₁.hom ≫ { f := PInfty })

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
@[reassoc (attr := simp)]
/--
lemma `PInfty_toNondegComplex` / 引理 `PInfty_toNondegComplex`

English:
lemma PInfty_toNondegComplex
  statement: PInfty ≫ s.toNondegComplex = s.toNondegComplex
  proof: (toKaroubi _).map_injective (by simp [toNondegComplex])

中文:
引理 PInfty_toNondegComplex
  结论: PInfty ≫ s.toNondegComplex = s.toNondegComplex
  证明: (toKaroubi _).map_injective (by simp [toNondegComplex])

Depends on / 依赖: map_injective, toKaroubi, toNondegComplex
-/
lemma PInfty_toNondegComplex : PInfty ≫ s.toNondegComplex = s.toNondegComplex :=
  (toKaroubi _).map_injective (by simp [toNondegComplex])

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
@[reassoc (attr := simp)]
/--
lemma `fromNondegComplex_toNondegComplex` / 引理 `fromNondegComplex_toNondegComplex`

English:
lemma fromNondegComplex_toNondegComplex
  proof: (toKaroubi _).map_injective (by simp [toNondegComplex, fromNondegComplex])

中文:
引理 fromNondegComplex_toNondegComplex
  证明: (toKaroubi _).map_injective (by simp [toNondegComplex, fromNondegComplex])

Depends on / 依赖: fromNondegComplex, map_injective, toKaroubi, toNondegComplex
-/
lemma fromNondegComplex_toNondegComplex :
    s.fromNondegComplex ≫ s.toNondegComplex = 𝟙 _ :=
  (toKaroubi _).map_injective (by simp [toNondegComplex, fromNondegComplex])

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
@[reassoc]
/--
lemma `toNondegComplex_f` / 引理 `toNondegComplex_f`

English:
lemma toNondegComplex_f
  given: (n : Nat)
  proof: by
  simp [toNondegComplex, fullyFaithfulToKaroubi]

中文:
引理 toNondegComplex_f
  条件: (n : 自然数)
  证明: by
  simp [toNondegComplex, fullyFaithfulToKaroubi]

Depends on / 依赖: fullyFaithfulToKaroubi, toNondegComplex
-/
lemma toNondegComplex_f (n : Nat) :
    s.toNondegComplex.f n = PInfty.f n ≫ s.toKaroubiNondegComplexIsoN₁.inv.f.f n := by
  simp [toNondegComplex, fullyFaithfulToKaroubi]

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
@[reassoc]
/--
lemma `fromNondegComplex_f` / 引理 `fromNondegComplex_f`

English:
lemma fromNondegComplex_f
  given: (n : Nat)
  proof: by
  simp [fromNondegComplex, fullyFaithfulToKaroubi,
    cofan, IndexSet.id, IndexSet.e]

中文:
引理 fromNondegComplex_f
  条件: (n : 自然数)
  证明: by
  simp [fromNondegComplex, fullyFaithfulToKaroubi,
    cofan, IndexSet.id, IndexSet.e]

Depends on / 依赖: IndexSet, IndexSet.e, IndexSet.id, fromNondegComplex, fullyFaithfulToKaroubi
-/
lemma fromNondegComplex_f (n : Nat) :
    s.fromNondegComplex.f n = s.ι n ≫ PInfty.f n := by
  simp [fromNondegComplex, fullyFaithfulToKaroubi,
    cofan, IndexSet.id, IndexSet.e]

/--
Instance `isSplitEpi_toNondegComplex` / 实例 `isSplitEpi_toNondegComplex`

English:
instance isSplitEpi_toNondegComplex
  signature: : IsSplitEpi s.toNondegComplex where
  body: ⟨⟨s.fromNondegComplex, by simp⟩⟩

中文:
实例 isSplitEpi_toNondegComplex
  签名: : 是分裂满态射 s.toNondegComplex where
  定义体: ⟨⟨s.fromNondegComplex, by simp⟩⟩

Depends on / 依赖: fromNondegComplex, s.fromNondegComplex
-/
instance isSplitEpi_toNondegComplex : IsSplitEpi s.toNondegComplex where
  exists_splitEpi := ⟨⟨s.fromNondegComplex, by simp⟩⟩

/--
Instance `isSplitMono_fromNondegComplex` / 实例 `isSplitMono_fromNondegComplex`

English:
instance isSplitMono_fromNondegComplex
  signature: : IsSplitMono s.fromNondegComplex where
  body: ⟨⟨s.toNondegComplex, by simp⟩⟩

中文:
实例 isSplitMono_fromNondegComplex
  签名: : 是分裂单态射 s.fromNondegComplex where
  定义体: ⟨⟨s.toNondegComplex, by simp⟩⟩

Depends on / 依赖: s.toNondegComplex, toNondegComplex
-/
instance isSplitMono_fromNondegComplex : IsSplitMono s.fromNondegComplex where
  exists_splitMono := ⟨⟨s.toNondegComplex, by simp⟩⟩

set_option backward.defeqAttrib.useBackward true in
@[reassoc (attr := simp)]
/--
lemma `toNondegComplex_fromNondegComplex` / 引理 `toNondegComplex_fromNondegComplex`

English:
lemma toNondegComplex_fromNondegComplex
  proof: (toKaroubi _).map_injective (by simp [toNondegComplex, fromNondegComplex])

中文:
引理 toNondegComplex_fromNondegComplex
  证明: (toKaroubi _).map_injective (by simp [toNondegComplex, fromNondegComplex])

Depends on / 依赖: fromNondegComplex, map_injective, toKaroubi, toNondegComplex
-/
lemma toNondegComplex_fromNondegComplex :
    s.toNondegComplex ≫ s.fromNondegComplex = PInfty :=
  (toKaroubi _).map_injective (by simp [toNondegComplex, fromNondegComplex])

/-- Given a splitting `s` of a simplicial object `X` in a preadditive category,
this is the homotopy equivalence from the alternating face map complex of `X`
to the chain complex `s.nondegComplex`. -/
@[simps hom inv]
/--
Definition of `homotopyEquivNondegComplex` / `homotopyEquivNondegComplex` 的定义

English:
definition homotopyEquivNondegComplex
  signature: :
  body: s.toNondegComplex
  inv := s.fromNondegComplex
  homotopyHomInvId := .trans (.ofEq (by simp)) (homotopyPInftyToId X)
  homotopyInvHomId := .ofEq (by simp)

中文:
定义 homotopyEquivNondegComplex
  签名: :
  定义体: s.toNondegComplex
  inv := s.fromNondegComplex
  homotopyHomInvId := .trans (.ofEq (by simp)) (homotopyPInftyToId X)
  homotopyInvHomId := .ofEq (by simp)

Depends on / 依赖: s.toNondegComplex, toNondegComplex
-/
noncomputable def homotopyEquivNondegComplex :
    HomotopyEquiv K[X] s.nondegComplex where
  hom := s.toNondegComplex
  inv := s.fromNondegComplex
  homotopyHomInvId := .trans (.ofEq (by simp)) (homotopyPInftyToId X)
  homotopyInvHomId := .ofEq (by simp)

end Splitting

namespace Split

variable {C : Type*} [Category* C] [Preadditive C] [HasFiniteCoproducts C]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The functor which sends a split simplicial object in a preadditive category to
the chain complex which consists of nondegenerate simplices. -/
@[simps]
/--
Definition of `nondegComplexFunctor` / `nondegComplexFunctor` 的定义

English:
definition nondegComplexFunctor
  signature: : Split C ⥤ ChainComplex C Nat where
  body: S.s.nondegComplex
  map {S₁ S₂} Φ :=
    { f := Φ.f
      comm' := fun i j _ => by
        dsimp
        erw [← cofan_inj_naturality_symm_assoc Φ (Splitting.IndexSet.id (op ⦋i⦌)),
          ((alternatingFaceMapComplex C).map Φ.F).comm_assoc i j]
        simp only [assoc]
        congr 2
        appl

中文:
定义 nondegComplexFunctor
  签名: : 分裂 C ⥤ 链复形 C 自然数 where
  定义体: S.s.nondegComplex
  map {S₁ S₂} Φ :=
    { f := Φ.f
      comm' := fun i j _ => by
        dsimp
        erw [← cofan_inj_naturality_symm_assoc Φ (Splitting.IndexSet.id (op ⦋i⦌)),
          ((alternatingFaceMapComplex C).map Φ.F).comm_assoc i j]
        simp only [assoc]
        congr 2
        appl

Depends on / 依赖: S.s.nondegComplex, nondegComplex
-/
noncomputable def nondegComplexFunctor : Split C ⥤ ChainComplex C Nat where
  obj S := S.s.nondegComplex
  map {S₁ S₂} Φ :=
    { f := Φ.f
      comm' := fun i j _ => by
        dsimp
        erw [← cofan_inj_naturality_symm_assoc Φ (Splitting.IndexSet.id (op ⦋i⦌)),
          ((alternatingFaceMapComplex C).map Φ.F).comm_assoc i j]
        simp only [assoc]
        congr 2
        apply S₁.s.hom_ext'
        intro A
        dsimp [alternatingFaceMapComplex]
        rw [cofan_inj_naturality_symm_assoc Φ A]
        by_cases h : A.EqId
        · dsimp at h
          subst h
          rw [Splitting.cofan_inj_πSummand_eq_id]
          dsimp
          rw [comp_id]; rw [Splitting.cofan_inj_πSummand_eq_id_assoc]
        · rw [S₁.s.cofan_inj_πSummand_eq_zero_assoc _ _ (Ne.symm h),
            S₂.s.cofan_inj_πSummand_eq_zero _ _ (Ne.symm h), zero_comp, comp_zero] }

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The natural isomorphism (in `Karoubi (ChainComplex C ℕ)`) between the chain complex
of nondegenerate simplices of a split simplicial object and the normalized Moore complex
defined as a formal direct factor of the alternating face map complex. -/
@[simps!]
/--
Definition of `toKaroubiNondegComplexFunctorIsoN₁` / `toKaroubiNondegComplexFunctorIsoN₁` 的定义

English:
definition toKaroubiNondegComplexFunctorIsoN₁
  signature: :
  body: NatIso.ofComponents (fun S => S.s.toKaroubiNondegComplexIsoN₁) fun Φ => by
    ext n
    dsimp
    simp only [assoc, PInfty_f_idem_assoc]
    erw [← Split.cofan_inj_naturality_symm_assoc Φ (Splitting.IndexSet.id (op ⦋n⦌))]
    rw [PInfty_f_naturality]

中文:
定义 toKaroubiNondegComplexFunctorIsoN₁
  签名: :
  定义体: NatIso.ofComponents (fun S => S.s.toKaroubiNondegComplexIsoN₁) fun Φ => by
    ext n
    dsimp
    simp only [assoc, PInfty_f_idem_assoc]
    erw [← Split.cofan_inj_naturality_symm_assoc Φ (Splitting.IndexSet.id (op ⦋n⦌))]
    rw [PInfty_f_naturality]

Depends on / 依赖: IndexSet, NatIso, NatIso.ofComponents, PInfty_f_idem_assoc, PInfty_f_naturality, S.s.toKaroubiNondegComplexIsoN, Split.cofan_inj_naturality_symm_assoc, Splitting, Splitting.IndexSet.id, cofan_inj_naturality_symm_assoc, ofComponents
-/
noncomputable def toKaroubiNondegComplexFunctorIsoN₁ :
    nondegComplexFunctor ⋙ toKaroubi (ChainComplex C Nat) ≅ forget C ⋙ DoldKan.N₁ :=
  NatIso.ofComponents (fun S => S.s.toKaroubiNondegComplexIsoN₁) fun Φ => by
    ext n
    dsimp
    simp only [assoc, PInfty_f_idem_assoc]
    erw [← Split.cofan_inj_naturality_symm_assoc Φ (Splitting.IndexSet.id (op ⦋n⦌))]
    rw [PInfty_f_naturality]

end Split

end CategoryTheory.SimplicialObject
