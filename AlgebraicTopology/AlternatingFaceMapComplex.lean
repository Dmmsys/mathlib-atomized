/-
Copyright (c) 2021 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou, Adam Topaz, Johan Commelin
-/
module

public import Mathlib.Algebra.Homology.Additive
public import Mathlib.AlgebraicTopology.MooreComplex
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.CategoryTheory.Idempotents.FunctorCategories
public import Mathlib.CategoryTheory.Limits.FunctorCategory.EpiMono
public import Mathlib.CategoryTheory.Preadditive.Opposite

/-!

# The alternating face map complex of a simplicial object in a preadditive category

We construct the alternating face map complex, as a
functor `alternatingFaceMapComplex : SimplicialObject C ⥤ ChainComplex C ℕ`
for any preadditive category `C`. For any simplicial object `X` in `C`,
this is the homological complex `... → X_2 → X_1 → X_0`
where the differentials are alternating sums of faces.

The dual version `alternatingCofaceMapComplex : CosimplicialObject C ⥤ CochainComplex C ℕ`
is also constructed.

We also construct the natural transformation
`inclusionOfMooreComplex : normalizedMooreComplex A ⟶ alternatingFaceMapComplex A`
when `A` is an abelian category.

## References
* https://stacks.math.columbia.edu/tag/0194
* https://ncatlab.org/nlab/show/Moore+complex

-/

@[expose] public section


open CategoryTheory CategoryTheory.Limits CategoryTheory.Subobject

open CategoryTheory.Preadditive CategoryTheory.Category CategoryTheory.Idempotents

open Opposite

open Simplicial

noncomputable section

namespace AlgebraicTopology

namespace AlternatingFaceMapComplex

/-!
## Construction of the alternating face map complex
-/


variable {C : Type*} [Category* C] [Preadditive C]
variable (X : SimplicialObject C)
variable (Y : SimplicialObject C)

/-- The differential on the alternating face map complex is the alternate
sum of the face maps -/
@[simp]
/--
Definition of `objD` / `objD` 的定义

English:
definition objD
  signature: (n : Nat)
  body: ∑ i : Fin (n + 2), (-1 : Int) ^ (i : Nat) • X.δ i

中文:
定义 objD
  签名: (n : 自然数)
  定义体: ∑ i : Fin (n + 2), (-1 : Int) ^ (i : Nat) • X.δ i
-/
def objD (n : Nat) : X _⦋n + 1⦌ ⟶ X _⦋n⦌ :=
  ∑ i : Fin (n + 2), (-1 : Int) ^ (i : Nat) • X.δ i


/--
theorem `d_squared` / 定理 `d_squared`

English:
theorem d_squared
  given: (n : Nat)
  statement: objD X (n + 1) ≫ objD X n = 0
  proof: by
  -- we start by expanding d ≫ d as a double sum
  dsimp
  simp only [comp_sum, sum_comp, ← Finset.sum_product']
  -- then, we decompose the index set P into a subset S and its complement Sᶜ
  let P := Fin (n + 2) × Fin (n + 3)
  let S : Finset P := {ij : P | (ij.2 : Nat) <= (ij.1 : Nat)}
  rw [F

中文:
定理 d_squared
  条件: (n : 自然数)
  结论: objD X (n + 1) ≫ objD X n = 0
  证明: by
  -- we start by expanding d ≫ d as a double sum
  dsimp
  simp only [comp_sum, sum_comp, ← Finset.sum_product']
  -- then, we decompose the index set P into a subset S and its complement Sᶜ
  let P := Fin (n + 2) × Fin (n + 3)
  let S : Finset P := {ij : P | (ij.2 : Nat) <= (ij.1 : Nat)}
  rw [F
-/
theorem d_squared (n : Nat) : objD X (n + 1) ≫ objD X n = 0 := by
  -- we start by expanding d ≫ d as a double sum
  dsimp
  simp only [comp_sum, sum_comp, ← Finset.sum_product']
  -- then, we decompose the index set P into a subset S and its complement Sᶜ
  let P := Fin (n + 2) × Fin (n + 3)
  let S : Finset P := {ij : P | (ij.2 : Nat) <= (ij.1 : Nat)}
  rw [Finset.univ_product_univ]; rw [← Finset.sum_add_sum_compl S]; rw [← eq_neg_iff_add_eq_zero]; rw [← Finset.sum_neg_distrib]
  /- we are reduced to showing that two sums are equal, and this is obtained
    by constructing a bijection φ : S -> Sᶜ, which maps (i,j) to (j,i+1),
    and by comparing the terms -/
  let φ : forall ij : P, ij in S -> P := fun ij hij =>
    (Fin.castLT ij.2 (lt_of_le_of_lt (Finset.mem_filter.mp hij).right (Fin.is_lt ij.1)), ij.1.succ)
  apply Finset.sum_bij φ
  · -- φ(S) is contained in Sᶜ
    intro ij hij
    simp_rw [S, φ, Finset.compl_filter, Finset.mem_filter_univ, Fin.val_succ,
      Fin.val_castLT] at hij ⊢
    lia
  · -- φ : S → Sᶜ is injective
    rintro ⟨i, j⟩ hij ⟨i', j'⟩ hij' h
    rw [Prod.mk_inj]
    exact ⟨by simpa [φ] using! congr_arg Prod.snd h,
      by simpa [φ, Fin.castSucc_castLT] using! congr_arg Fin.castSucc (congr_arg Prod.fst h)⟩
  · -- φ : S → Sᶜ is surjective
    rintro ⟨i', j'⟩ hij'
    simp_rw [S, Finset.compl_filter, Finset.mem_filter_univ, not_le] at hij'
    refine ⟨(j'.pred <| ?_, Fin.castSucc i'), ?_, ?_⟩
    · rintro rfl
      simp only [Fin.val_zero, not_lt_zero] at hij'
    · simpa [S] using! Nat.le_sub_one_of_lt hij'
    · simp only [φ, Fin.castLT_castSucc, Fin.succ_pred]
  · -- identification of corresponding terms in both sums
    rintro ⟨i, j⟩ hij
    dsimp
    simp only [zsmul_comp, comp_zsmul, smul_smul, ← neg_smul]
    congr 1
    · simp only [φ, Fin.val_succ, pow_add, pow_one, mul_neg, neg_neg, mul_one]
      apply mul_comm
    · rw [CategoryTheory.SimplicialObject.δ_comp_δ'']
      simpa [S] using! hij

/-!
## Construction of the alternating face map complex functor
-/


/-- The alternating face map complex, on objects -/
@[implicit_reducible]
/--
Definition of `obj` / `obj` 的定义

English:
definition obj
  signature: : ChainComplex C Nat
  body: ChainComplex.of (fun n => X _⦋n⦌) (objD X) (d_squared X)

@[simp]

中文:
定义 obj
  签名: : ChainComplex C 自然数
  定义体: ChainComplex.of (fun n => X _⦋n⦌) (objD X) (d_squared X)

@[simp]

Depends on / 依赖: ChainComplex, ChainComplex.of, d_squared
-/
def obj : ChainComplex C Nat :=
  ChainComplex.of (fun n => X _⦋n⦌) (objD X) (d_squared X)

@[simp]
/--
theorem `obj_X` / 定理 `obj_X`

English:
theorem obj_X
  given: (X : SimplicialObject C) (n : Nat)
  statement: (AlternatingFaceMapComplex.obj X).X n = X _⦋n⦌
  proof: rfl

@[simp]

中文:
定理 obj_X
  条件: (X : SimplicialObject C) (n : 自然数)
  结论: (AlternatingFaceMapComplex.obj X).X n = X _⦋n⦌
  证明: rfl

@[simp]
-/
theorem obj_X (X : SimplicialObject C) (n : Nat) : (AlternatingFaceMapComplex.obj X).X n = X _⦋n⦌ :=
  rfl

@[simp]
/--
theorem `obj_d_eq` / 定理 `obj_d_eq`

English:
theorem obj_d_eq
  given: (X : SimplicialObject C) (n : Nat)
  proof: by
  simp [obj]

中文:
定理 obj_d_eq
  条件: (X : SimplicialObject C) (n : 自然数)
  证明: by
  simp [obj]
-/
theorem obj_d_eq (X : SimplicialObject C) (n : Nat) :
    (AlternatingFaceMapComplex.obj X).d (n + 1) n
      = ∑ i : Fin (n + 2), (-1 : Int) ^ (i : Nat) • X.δ i := by
  simp [obj]

variable {X} {Y}

/--
Definition of `map` / `map` 的定义

English:
definition map
  signature: (f : X ⟶ Y)
  body: ChainComplex.ofHom (fun n => f.app (op ⦋n⦌)) fun n => by
    simp only [obj, ChainComplex.of_d, objD, Int.reduceNeg]
    rw [comp_sum]; rw [sum_comp]
    refine Finset.sum_congr rfl fun _ _ => ?_
    rw [comp_zsmul]; rw [zsmul_comp]
    congr 1
    symm
    apply f.naturality

@[simp]

中文:
定义 map
  签名: (f : X ⟶ Y)
  定义体: ChainComplex.ofHom (fun n => f.app (op ⦋n⦌)) fun n => by
    simp only [obj, ChainComplex.of_d, objD, Int.reduceNeg]
    rw [comp_sum]; rw [sum_comp]
    refine Finset.sum_congr rfl fun _ _ => ?_
    rw [comp_zsmul]; rw [zsmul_comp]
    congr 1
    symm
    apply f.naturality

@[simp]

Depends on / 依赖: ChainComplex, ChainComplex.ofHom, ChainComplex.of_d, Finset, Finset.sum_congr, Int.reduceNeg, comp_sum, comp_zsmul, f.app, f.naturality, naturality, of_d, reduceNeg, sum_comp, sum_congr, zsmul_comp
-/
def map (f : X ⟶ Y) : obj X ⟶ obj Y :=
  ChainComplex.ofHom (fun n => f.app (op ⦋n⦌)) fun n => by
    simp only [obj, ChainComplex.of_d, objD, Int.reduceNeg]
    rw [comp_sum]; rw [sum_comp]
    refine Finset.sum_congr rfl fun _ _ => ?_
    rw [comp_zsmul]; rw [zsmul_comp]
    congr 1
    symm
    apply f.naturality

@[simp]
/--
theorem `map_f` / 定理 `map_f`

English:
theorem map_f
  given: (f : X ⟶ Y) (n : Nat)
  statement: (map f).f n = f.app (op ⦋n⦌)
  proof: rfl

中文:
定理 map_f
  条件: (f : X ⟶ Y) (n : 自然数)
  结论: (map f).f n = f.app (op ⦋n⦌)
  证明: rfl
-/
theorem map_f (f : X ⟶ Y) (n : Nat) : (map f).f n = f.app (op ⦋n⦌) :=
  rfl

end AlternatingFaceMapComplex

variable (C : Type*) [Category* C] [Preadditive C]

/-- The alternating face map complex, as a functor -/
@[implicit_reducible]
/--
Definition of `alternatingFaceMapComplex` / `alternatingFaceMapComplex` 的定义

English:
definition alternatingFaceMapComplex
  signature: : SimplicialObject C ⥤ ChainComplex C Nat where
  body: AlternatingFaceMapComplex.obj
  map f := AlternatingFaceMapComplex.map f

中文:
定义 alternatingFaceMapComplex
  签名: : SimplicialObject C ⥤ ChainComplex C 自然数 where
  定义体: AlternatingFaceMapComplex.obj
  map f := AlternatingFaceMapComplex.map f

Depends on / 依赖: AlternatingFaceMapComplex, AlternatingFaceMapComplex.obj
-/
def alternatingFaceMapComplex : SimplicialObject C ⥤ ChainComplex C Nat where
  obj := AlternatingFaceMapComplex.obj
  map f := AlternatingFaceMapComplex.map f

variable {C}

@[simp]
/--
theorem `alternatingFaceMapComplex_obj_X` / 定理 `alternatingFaceMapComplex_obj_X`

English:
theorem alternatingFaceMapComplex_obj_X
  given: (X : SimplicialObject C) (n : Nat)
  proof: rfl

@[simp]

中文:
定理 alternatingFaceMapComplex_obj_X
  条件: (X : SimplicialObject C) (n : 自然数)
  证明: rfl

@[simp]
-/
theorem alternatingFaceMapComplex_obj_X (X : SimplicialObject C) (n : Nat) :
    ((alternatingFaceMapComplex C).obj X).X n = X _⦋n⦌ :=
  rfl

@[simp]
/--
theorem `alternatingFaceMapComplex_obj_d` / 定理 `alternatingFaceMapComplex_obj_d`

English:
theorem alternatingFaceMapComplex_obj_d
  given: (X : SimplicialObject C) (n : Nat)
  proof: by
  simp [alternatingFaceMapComplex]

@[simp]

中文:
定理 alternatingFaceMapComplex_obj_d
  条件: (X : SimplicialObject C) (n : 自然数)
  证明: by
  simp [alternatingFaceMapComplex]

@[simp]

Depends on / 依赖: alternatingFaceMapComplex
-/
theorem alternatingFaceMapComplex_obj_d (X : SimplicialObject C) (n : Nat) :
    ((alternatingFaceMapComplex C).obj X).d (n + 1) n = AlternatingFaceMapComplex.objD X n := by
  simp [alternatingFaceMapComplex]

@[simp]
/--
theorem `alternatingFaceMapComplex_map_f` / 定理 `alternatingFaceMapComplex_map_f`

English:
theorem alternatingFaceMapComplex_map_f
  given: {X Y : SimplicialObject C} (f : X ⟶ Y) (n : Nat)
  proof: rfl

中文:
定理 alternatingFaceMapComplex_map_f
  条件: {X Y : SimplicialObject C} (f : X ⟶ Y) (n : 自然数)
  证明: rfl
-/
theorem alternatingFaceMapComplex_map_f {X Y : SimplicialObject C} (f : X ⟶ Y) (n : Nat) :
    ((alternatingFaceMapComplex C).map f).f n = f.app (op ⦋n⦌) :=
  rfl

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/--
theorem `map_alternatingFaceMapComplex` / 定理 `map_alternatingFaceMapComplex`

English:
theorem map_alternatingFaceMapComplex
  statement: {D : Type*} [Category* D] [Preadditive D] (F : C ⥤ D)
  proof: by
  apply CategoryTheory.Functor.ext
  · intro X Y f
    ext n
    simp only [Functor.comp_map, HomologicalComplex.comp_f, alternatingFaceMapComplex_map_f,
      Functor.mapHomologicalComplex_map_f, HomologicalComplex.eqToHom_f, eqToHom_refl, comp_id,
      id_comp, SimplicialObject.whiskering_obj_

中文:
定理 map_alternatingFaceMapComplex
  结论: {D : 类型} [Category* D] [Preadditive D] (F : C ⥤ D)
  证明: by
  apply CategoryTheory.Functor.ext
  · intro X Y f
    ext n
    simp only [Functor.comp_map, HomologicalComplex.comp_f, alternatingFaceMapComplex_map_f,
      Functor.mapHomologicalComplex_map_f, HomologicalComplex.eqToHom_f, eqToHom_refl, comp_id,
      id_comp, SimplicialObject.whiskering_obj_

Depends on / 依赖: CategoryTheory, CategoryTheory.Functor.ext, Functor, Functor.comp_map, Functor.comp_obj, Functor.mapHomologicalComplex_map_f, Functor.mapHomologicalComplex_obj_d, HomologicalComplex, HomologicalComplex.comp_f, HomologicalComplex.eqToHom_f, HomologicalComplex.ext, SimplicialObject, SimplicialObject.whiskering_obj_map_app, alternatingFaceMapComplex_map_f, alternatingFaceMapComplex_obj_d, comp_f, comp_id, comp_map, comp_obj, eqToHom_f
-/
theorem map_alternatingFaceMapComplex {D : Type*} [Category* D] [Preadditive D] (F : C ⥤ D)
    [F.Additive] :
    alternatingFaceMapComplex C ⋙ F.mapHomologicalComplex _ =
      (SimplicialObject.whiskering C D).obj F ⋙ alternatingFaceMapComplex D := by
  apply CategoryTheory.Functor.ext
  · intro X Y f
    ext n
    simp only [Functor.comp_map, HomologicalComplex.comp_f, alternatingFaceMapComplex_map_f,
      Functor.mapHomologicalComplex_map_f, HomologicalComplex.eqToHom_f, eqToHom_refl, comp_id,
      id_comp, SimplicialObject.whiskering_obj_map_app]
  · intro X
    apply HomologicalComplex.ext
    · rintro i j (rfl : j + 1 = i)
      dsimp only [Functor.comp_obj]
      simp only [Functor.mapHomologicalComplex_obj_d, alternatingFaceMapComplex_obj_d,
        eqToHom_refl, id_comp, comp_id, AlternatingFaceMapComplex.objD, Functor.map_sum,
        Functor.map_zsmul]
      rfl
    · ext n
      rfl

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: (alternatingFaceMapComplex C).Additive

中文:
实例 :
  签名: (alternatingFaceMapComplex C).Additive
-/
instance : (alternatingFaceMapComplex C).Additive where

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Limits.HasPullbacks
  signature: C] : (alternatingFaceMapComplex C).PreservesMonomorphisms where
  body: HomologicalComplex.mono_of_mono_f _ fun _ => by dsimp; infer_instance

中文:
实例 [Limits.HasPullbacks
  签名: C] : (alternatingFaceMapComplex C).PreservesMonomorphisms where
  定义体: HomologicalComplex.mono_of_mono_f _ fun _ => by dsimp; infer_instance

Depends on / 依赖: HomologicalComplex, HomologicalComplex.mono_of_mono_f, infer_instance, mono_of_mono_f
-/
instance [Limits.HasPullbacks C] : (alternatingFaceMapComplex C).PreservesMonomorphisms where
  preserves _ _ := HomologicalComplex.mono_of_mono_f _ fun _ => by dsimp; infer_instance

/--
theorem `karoubi_alternatingFaceMapComplex_d` / 定理 `karoubi_alternatingFaceMapComplex_d`

English:
theorem karoubi_alternatingFaceMapComplex_d
  given: (P : Karoubi (SimplicialObject C)) (n : Nat)
  proof: by
  dsimp
  simp only [AlternatingFaceMapComplex.obj_d_eq, Karoubi.sum_hom, Preadditive.comp_sum,
    Karoubi.zsmul_hom, Preadditive.comp_zsmul]
  rfl

中文:
定理 karoubi_alternatingFaceMapComplex_d
  条件: (P : Karoubi (SimplicialObject C)) (n : 自然数)
  证明: by
  dsimp
  simp only [AlternatingFaceMapComplex.obj_d_eq, Karoubi.sum_hom, Preadditive.comp_sum,
    Karoubi.zsmul_hom, Preadditive.comp_zsmul]
  rfl

Depends on / 依赖: AlternatingFaceMapComplex, AlternatingFaceMapComplex.obj_d_eq, Karoubi, Karoubi.sum_hom, Karoubi.zsmul_hom, Preadditive, Preadditive.comp_sum, Preadditive.comp_zsmul, comp_sum, comp_zsmul, obj_d_eq, sum_hom, zsmul_hom
-/
theorem karoubi_alternatingFaceMapComplex_d (P : Karoubi (SimplicialObject C)) (n : Nat) :
    ((AlternatingFaceMapComplex.obj (KaroubiFunctorCategoryEmbedding.obj P)).d (n + 1) n).f =
      P.p.app (op ⦋n + 1⦌) ≫ (AlternatingFaceMapComplex.obj P.X).d (n + 1) n := by
  dsimp
  simp only [AlternatingFaceMapComplex.obj_d_eq, Karoubi.sum_hom, Preadditive.comp_sum,
    Karoubi.zsmul_hom, Preadditive.comp_zsmul]
  rfl

namespace AlternatingFaceMapComplex

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/--
Definition of `ε` / `ε` 的定义

English:
definition ε
  signature: [Limits.HasZeroObject C]
  body: by
    refine (ChainComplex.toSingle₀Equiv _ _).symm ?_
    refine ⟨X.hom.app (op ⦋0⦌), ?_⟩
    dsimp
    rw [alternatingFaceMapComplex_obj_d]; rw [objD]; rw [Fin.sum_univ_two]; rw [Fin.val_zero]; rw [pow_zero]; rw [one_smul]; rw [Fin.val_one]; rw [pow_one]; rw [neg_smul]; rw [one_smul]; rw [add_com

中文:
定义 ε
  签名: [Limits.HasZeroObject C]
  定义体: by
    refine (ChainComplex.toSingle₀Equiv _ _).symm ?_
    refine ⟨X.hom.app (op ⦋0⦌), ?_⟩
    dsimp
    rw [alternatingFaceMapComplex_obj_d]; rw [objD]; rw [Fin.sum_univ_two]; rw [Fin.val_zero]; rw [pow_zero]; rw [one_smul]; rw [Fin.val_one]; rw [pow_one]; rw [neg_smul]; rw [one_smul]; rw [add_com

Depends on / 依赖: ChainComplex, ChainComplex.toSingle, Fin.sum_univ_two, Fin.val_one, Fin.val_zero, HomologicalComplex, HomologicalComplex.to_single_hom_ext, SimplicialObject, X.hom.app, adaptation_note, add_comp, add_neg_cancel, alternatingFaceMapComplex_obj_d, naturality, neg_comp, neg_smul, one_smul, pow_one, pow_zero, sum_univ_two
-/
def ε [Limits.HasZeroObject C] :
    SimplicialObject.Augmented.drop ⋙ AlgebraicTopology.alternatingFaceMapComplex C ⟶
      SimplicialObject.Augmented.point ⋙ ChainComplex.single₀ C where
  app X := by
    refine (ChainComplex.toSingle₀Equiv _ _).symm ?_
    refine ⟨X.hom.app (op ⦋0⦌), ?_⟩
    dsimp
    rw [alternatingFaceMapComplex_obj_d]; rw [objD]; rw [Fin.sum_univ_two]; rw [Fin.val_zero]; rw [pow_zero]; rw [one_smul]; rw [Fin.val_one]; rw [pow_one]; rw [neg_smul]; rw [one_smul]; rw [add_comp]; rw [neg_comp]; rw [SimplicialObject.δ_naturality]; rw [SimplicialObject.δ_naturality]
    apply add_neg_cancel
  naturality X Y f := by
    apply HomologicalComplex.to_single_hom_ext
    #adaptation_note /-- This proof broke at nightly-2026-04-28. It used to be:
    ```
    dsimp
    simp [ChainComplex.toSingle₀Equiv, SimplicialObject.Augmented.w₀]
    ```
    The proof below is an emergency repair, and I've asked the authors of this file to review.
    -/
    change f.left.app _ ≫ _ = _ ≫ ((ChainComplex.single₀ _).map f.right).f 0
    rw [ChainComplex.toSingle₀Equiv_symm_apply_f_zero]; rw [ChainComplex.toSingle₀Equiv_symm_apply_f_zero]; rw [ChainComplex.single₀_map_f_zero]
    exact SimplicialObject.Augmented.w₀ f

@[simp]
/--
lemma `ε_app_f_zero` / 引理 `ε_app_f_zero`

English:
lemma ε_app_f_zero
  given: [Limits.HasZeroObject C] (X : SimplicialObject.Augmented C)
  proof: ChainComplex.toSingle₀Equiv_symm_apply_f_zero _ _

@[simp]

中文:
引理 ε_app_f_zero
  条件: [Limits.HasZeroObject C] (X : SimplicialObject.Augmented C)
  证明: ChainComplex.toSingle₀Equiv_symm_apply_f_zero _ _

@[simp]

Depends on / 依赖: ChainComplex, ChainComplex.toSingle
-/
lemma ε_app_f_zero [Limits.HasZeroObject C] (X : SimplicialObject.Augmented C) :
    (ε.app X).f 0 = X.hom.app (op ⦋0⦌) :=
  ChainComplex.toSingle₀Equiv_symm_apply_f_zero _ _

@[simp]
/--
lemma `ε_app_f_succ` / 引理 `ε_app_f_succ`

English:
lemma ε_app_f_succ
  given: [Limits.HasZeroObject C] (X : SimplicialObject.Augmented C) (n : Nat)
  proof: rfl

中文:
引理 ε_app_f_succ
  条件: [Limits.HasZeroObject C] (X : SimplicialObject.Augmented C) (n : 自然数)
  证明: rfl
-/
lemma ε_app_f_succ [Limits.HasZeroObject C] (X : SimplicialObject.Augmented C) (n : Nat) :
    (ε.app X).f (n + 1) = 0 := rfl

end AlternatingFaceMapComplex

/-!
## Construction of the natural inclusion of the normalized Moore complex
-/

variable {A : Type*} [Category* A] [Abelian A]

set_option backward.isDefEq.respectTransparency.types false in
/--
Definition of `inclusionOfMooreComplexMap` / `inclusionOfMooreComplexMap` 的定义

English:
definition inclusionOfMooreComplexMap
  signature: (X : SimplicialObject A)
  body: ChainComplex.ofHom (fun n => (NormalizedMooreComplex.objX X n).arrow) fun i => by
  /- we have to show the compatibility of the differentials on the alternating
           face map complex with those defined on the normalized Moore complex:
           we first get rid of the terms of the alternating

中文:
定义 inclusionOfMooreComplexMap
  签名: (X : SimplicialObject A)
  定义体: ChainComplex.ofHom (fun n => (NormalizedMooreComplex.objX X n).arrow) fun i => by
  /- we have to show the compatibility of the differentials on the alternating
           face map complex with those defined on the normalized Moore complex:
           we first get rid of the terms of the alternating

Depends on / 依赖: ChainComplex, ChainComplex.ofHom, NormalizedMooreComplex, NormalizedMooreComplex.objX
-/
def inclusionOfMooreComplexMap (X : SimplicialObject A) :
    (normalizedMooreComplex A).obj X ⟶ (alternatingFaceMapComplex A).obj X :=
ChainComplex.ofHom (fun n => (NormalizedMooreComplex.objX X n).arrow) fun i => by
  /- we have to show the compatibility of the differentials on the alternating
           face map complex with those defined on the normalized Moore complex:
           we first get rid of the terms of the alternating sum that are obviously
           zero on the normalized_Moore_complex -/
  simp only [normalizedMooreComplex, NormalizedMooreComplex.obj, alternatingFaceMapComplex,
    AlternatingFaceMapComplex.obj, ChainComplex.of_d, AlternatingFaceMapComplex.objD, comp_sum]
  rw [Fin.sum_univ_succ]; rw [Fintype.sum_eq_zero]
  swap
  · intro j
    rw [NormalizedMooreComplex.objX_add_one]; rw [comp_zsmul]; rw [← factorThru_arrow _ _ (finset_inf_arrow_factors Finset.univ _ _ (Finset.mem_univ j))]; rw [Category.assoc]; rw [kernelSubobject_arrow_comp]; rw [comp_zero]; rw [smul_zero]
  -- finally, we study the remaining term which is induced by X.δ 0
  rw [add_zero]; rw [Fin.val_zero]; rw [pow_zero]; rw [one_zsmul]
  dsimp [NormalizedMooreComplex.objD, NormalizedMooreComplex.objX]
  cases i <;> simp

@[simp]
/--
theorem `inclusionOfMooreComplexMap_f` / 定理 `inclusionOfMooreComplexMap_f`

English:
theorem inclusionOfMooreComplexMap_f
  given: (X : SimplicialObject A) (n : Nat)
  proof: by
  dsimp [inclusionOfMooreComplexMap]

中文:
定理 inclusionOfMooreComplexMap_f
  条件: (X : SimplicialObject A) (n : 自然数)
  证明: by
  dsimp [inclusionOfMooreComplexMap]

Depends on / 依赖: inclusionOfMooreComplexMap
-/
theorem inclusionOfMooreComplexMap_f (X : SimplicialObject A) (n : Nat) :
    (inclusionOfMooreComplexMap X).f n = (NormalizedMooreComplex.objX X n).arrow := by
  dsimp [inclusionOfMooreComplexMap]

variable (A)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency.types false in
/-- The inclusion map of the Moore complex in the alternating face map complex,
as a natural transformation -/
@[simps]
/--
Definition of `inclusionOfMooreComplex` / `inclusionOfMooreComplex` 的定义

English:
definition inclusionOfMooreComplex
  signature: : normalizedMooreComplex A ⟶ alternatingFaceMapComplex A where
  body: inclusionOfMooreComplexMap

中文:
定义 inclusionOfMooreComplex
  签名: : normalizedMooreComplex A ⟶ alternatingFaceMapComplex A where
  定义体: inclusionOfMooreComplexMap

Depends on / 依赖: inclusionOfMooreComplexMap
-/
def inclusionOfMooreComplex : normalizedMooreComplex A ⟶ alternatingFaceMapComplex A where
  app := inclusionOfMooreComplexMap

namespace AlternatingCofaceMapComplex

variable (X Y : CosimplicialObject C)

/-- The differential on the alternating coface map complex is the alternate
sum of the coface maps -/
@[simp]
/--
Definition of `objD` / `objD` 的定义

English:
definition objD
  signature: (n : Nat)
  body: ∑ i : Fin (n + 2), (-1 : Int) ^ (i : Nat) • X.δ i

中文:
定义 objD
  签名: (n : 自然数)
  定义体: ∑ i : Fin (n + 2), (-1 : Int) ^ (i : Nat) • X.δ i
-/
def objD (n : Nat) : X.obj ⦋n⦌ ⟶ X.obj ⦋n + 1⦌ :=
  ∑ i : Fin (n + 2), (-1 : Int) ^ (i : Nat) • X.δ i

/--
theorem `d_eq_unop_d` / 定理 `d_eq_unop_d`

English:
theorem d_eq_unop_d
  given: (n : Nat)
  proof: by
  simp only [objD, AlternatingFaceMapComplex.objD, unop_sum, unop_zsmul]
  rfl

中文:
定理 d_eq_unop_d
  条件: (n : 自然数)
  证明: by
  simp only [objD, AlternatingFaceMapComplex.objD, unop_sum, unop_zsmul]
  rfl

Depends on / 依赖: AlternatingFaceMapComplex, AlternatingFaceMapComplex.objD, unop_sum, unop_zsmul
-/
theorem d_eq_unop_d (n : Nat) :
    objD X n =
      (AlternatingFaceMapComplex.objD ((cosimplicialSimplicialEquiv C).functor.obj (op X))
          n).unop := by
  simp only [objD, AlternatingFaceMapComplex.objD, unop_sum, unop_zsmul]
  rfl

set_option backward.isDefEq.respectTransparency false in
/--
theorem `d_squared` / 定理 `d_squared`

English:
theorem d_squared
  given: (n : Nat)
  statement: objD X n ≫ objD X (n + 1) = 0
  proof: by
  simp only [d_eq_unop_d, ← unop_comp, AlternatingFaceMapComplex.d_squared, unop_zero]

中文:
定理 d_squared
  条件: (n : 自然数)
  结论: objD X n ≫ objD X (n + 1) = 0
  证明: by
  simp only [d_eq_unop_d, ← unop_comp, AlternatingFaceMapComplex.d_squared, unop_zero]

Depends on / 依赖: AlternatingFaceMapComplex, AlternatingFaceMapComplex.d_squared, d_eq_unop_d, d_squared, unop_comp, unop_zero
-/
theorem d_squared (n : Nat) : objD X n ≫ objD X (n + 1) = 0 := by
  simp only [d_eq_unop_d, ← unop_comp, AlternatingFaceMapComplex.d_squared, unop_zero]

/--
Definition of `obj` / `obj` 的定义

English:
definition obj
  signature: : CochainComplex C Nat
  body: CochainComplex.of (fun n => X.obj ⦋n⦌) (objD X) (d_squared X)

中文:
定义 obj
  签名: : CochainComplex C 自然数
  定义体: CochainComplex.of (fun n => X.obj ⦋n⦌) (objD X) (d_squared X)

Depends on / 依赖: CochainComplex, CochainComplex.of, X.obj, d_squared
-/
def obj : CochainComplex C Nat :=
  CochainComplex.of (fun n => X.obj ⦋n⦌) (objD X) (d_squared X)

variable {X} {Y}

/-- The alternating face map complex, on morphisms -/
@[simp]
/--
Definition of `map` / `map` 的定义

English:
definition map
  signature: (f : X ⟶ Y)
  body: CochainComplex.ofHom (fun n => f.app ⦋n⦌) fun n => by
    simp only [obj, CochainComplex.of_d, objD, Int.reduceNeg]
    rw [comp_sum]; rw [sum_comp]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [comp_zsmul]; rw [zsmul_comp]
    congr 1
    symm
    apply f.naturality

中文:
定义 map
  签名: (f : X ⟶ Y)
  定义体: CochainComplex.ofHom (fun n => f.app ⦋n⦌) fun n => by
    simp only [obj, CochainComplex.of_d, objD, Int.reduceNeg]
    rw [comp_sum]; rw [sum_comp]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [comp_zsmul]; rw [zsmul_comp]
    congr 1
    symm
    apply f.naturality

Depends on / 依赖: CochainComplex, CochainComplex.ofHom, CochainComplex.of_d, Finset, Finset.sum_congr, Int.reduceNeg, comp_sum, comp_zsmul, f.app, f.naturality, naturality, of_d, reduceNeg, sum_comp, sum_congr, zsmul_comp
-/
def map (f : X ⟶ Y) : obj X ⟶ obj Y :=
  CochainComplex.ofHom (fun n => f.app ⦋n⦌) fun n => by
    simp only [obj, CochainComplex.of_d, objD, Int.reduceNeg]
    rw [comp_sum]; rw [sum_comp]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [comp_zsmul]; rw [zsmul_comp]
    congr 1
    symm
    apply f.naturality

end AlternatingCofaceMapComplex

variable (C)

/-- The alternating coface map complex, as a functor -/
@[simps]
/--
Definition of `alternatingCofaceMapComplex` / `alternatingCofaceMapComplex` 的定义

English:
definition alternatingCofaceMapComplex
  signature: : CosimplicialObject C ⥤ CochainComplex C Nat where
  body: AlternatingCofaceMapComplex.obj
  map f := AlternatingCofaceMapComplex.map f

中文:
定义 alternatingCofaceMapComplex
  签名: : CosimplicialObject C ⥤ CochainComplex C 自然数 where
  定义体: AlternatingCofaceMapComplex.obj
  map f := AlternatingCofaceMapComplex.map f

Depends on / 依赖: AlternatingCofaceMapComplex, AlternatingCofaceMapComplex.obj
-/
def alternatingCofaceMapComplex : CosimplicialObject C ⥤ CochainComplex C Nat where
  obj := AlternatingCofaceMapComplex.obj
  map f := AlternatingCofaceMapComplex.map f

end AlgebraicTopology
