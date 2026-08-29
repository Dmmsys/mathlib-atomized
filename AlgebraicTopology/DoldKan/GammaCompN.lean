/-
Copyright (c) 2022 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.AlgebraicTopology.DoldKan.FunctorGamma
public import Mathlib.AlgebraicTopology.DoldKan.SplitSimplicialObject
public import Mathlib.CategoryTheory.Idempotents.HomologicalComplex
public import Mathlib.Tactic.SuppressCompilation

/-! # The counit isomorphism of the Dold-Kan equivalence

The purpose of this file is to construct natural isomorphisms
`N₁Γ₀ : Γ₀ ⋙ N₁ ≅ toKaroubi (ChainComplex C ℕ)`
and `N₂Γ₂ : Γ₂ ⋙ N₂ ≅ 𝟭 (Karoubi (ChainComplex C ℕ))`.

(See `Equivalence.lean` for the general strategy of proof of the Dold-Kan equivalence.)

-/

@[expose] public section

suppress_compilation

noncomputable section

open CategoryTheory CategoryTheory.Category CategoryTheory.Functor CategoryTheory.Limits
  CategoryTheory.Idempotents Opposite SimplicialObject Simplicial

namespace AlgebraicTopology

namespace DoldKan

variable {C : Type*} [Category* C] [Preadditive C] [HasFiniteCoproducts C]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The isomorphism `(Γ₀.splitting K).nondegComplex ≅ K` for all `K : ChainComplex C ℕ`. -/
@[simps!]
/--
Definition of `Γ₀NondegComplexIso` / `Γ₀NondegComplexIso` 的定义

English:
definition Γ₀NondegComplexIso
  signature: (K : ChainComplex C Nat)
  body: HomologicalComplex.Hom.isoOfComponents (fun _ => Iso.refl _)
    (by
      rintro _ n (rfl : n + 1 = _)
      dsimp
      simp only [id_comp, comp_id, AlternatingFaceMapComplex.obj_d_eq, Preadditive.sum_comp,
        Preadditive.comp_sum]
      rw [Fintype.sum_eq_single (0 : Fin (n + 2))]
      · si

中文:
定义 Γ₀NondegComplexIso
  签名: (K : ChainComplex C 自然数)
  定义体: HomologicalComplex.Hom.isoOfComponents (fun _ => Iso.refl _)
    (by
      rintro _ n (rfl : n + 1 = _)
      dsimp
      simp only [id_comp, comp_id, AlternatingFaceMapComplex.obj_d_eq, Preadditive.sum_comp,
        Preadditive.comp_sum]
      rw [Fintype.sum_eq_single (0 : Fin (n + 2))]
      · si

Depends on / 依赖: AlternatingFaceMapComplex, AlternatingFaceMapComplex.obj_d_eq, Fin.val_zero, Fintype, Fintype.sum_eq_single, HomologicalComplex, HomologicalComplex.Hom.isoOfComponents, IndexSet, Iso.refl, Obj.Termwise.mapMono_, Obj.mapMono_on_summand_id_assoc, Preadditive, Preadditive.comp_sum, Preadditive.sum_comp, Splitting, Splitting.IndexSet.id_fst, Splitting.cofan_inj_, Splitting.summand.eq_1, Termwise, comp_id
-/
def Γ₀NondegComplexIso (K : ChainComplex C Nat) : (Γ₀.splitting K).nondegComplex ≅ K :=
  HomologicalComplex.Hom.isoOfComponents (fun _ => Iso.refl _)
    (by
      rintro _ n (rfl : n + 1 = _)
      dsimp
      simp only [id_comp, comp_id, AlternatingFaceMapComplex.obj_d_eq, Preadditive.sum_comp,
        Preadditive.comp_sum]
      rw [Fintype.sum_eq_single (0 : Fin (n + 2))]
      · simp only [Fin.val_zero, pow_zero, one_zsmul]
        rw [δ]; rw [Γ₀.Obj.mapMono_on_summand_id_assoc]; rw [Γ₀.Obj.Termwise.mapMono_δ₀]; rw [Splitting.cofan_inj_πSummand_eq_id]
        dsimp only [Γ₀.splitting, Splitting.summand.eq_1, Splitting.IndexSet.id_fst]
        rw [comp_id]
      · intro i hi
        dsimp
        simp only [Preadditive.zsmul_comp, Preadditive.comp_zsmul]
        rw [δ]; rw [Γ₀.Obj.mapMono_on_summand_id_assoc]; rw [Γ₀.Obj.Termwise.mapMono_eq_zero]; rw [zero_comp]; rw [zsmul_zero]
        · intro h
          replace h := congr_arg SimplexCategory.len h
          change n + 1 = n at h
          lia
        · simpa only [Isδ₀.iff] using hi)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/--
Definition of `Γ₀'CompNondegComplexFunctor` / `Γ₀'CompNondegComplexFunctor` 的定义

English:
definition Γ₀'CompNondegComplexFunctor
  signature: : Γ₀' ⋙ Split.nondegComplexFunctor ≅ 𝟭 (ChainComplex C Nat)
  body: NatIso.ofComponents Γ₀NondegComplexIso

中文:
定义 Γ₀'CompNondegComplexFunctor
  签名: : Γ₀' ⋙ Split.nondegComplexFunctor ≅ 𝟭 (ChainComplex C 自然数)
  定义体: NatIso.ofComponents Γ₀NondegComplexIso
-/
def Γ₀'CompNondegComplexFunctor : Γ₀' ⋙ Split.nondegComplexFunctor ≅ 𝟭 (ChainComplex C Nat) :=
  NatIso.ofComponents Γ₀NondegComplexIso

/--
Definition of `N₁Γ₀` / `N₁Γ₀` 的定义

English:
definition N₁Γ₀
  signature: : Γ₀ ⋙ N₁ ≅ toKaroubi (ChainComplex C Nat)
  body: calc
    Γ₀ ⋙ N₁ ≅ Γ₀' ⋙ Split.forget C ⋙ N₁ := Functor.associator _ _ _
    _ ≅ Γ₀' ⋙ Split.nondegComplexFunctor ⋙ toKaroubi _ :=
      (isoWhiskerLeft Γ₀' Split.toKaroubiNondegComplexFunctorIsoN₁.symm)
    _ ≅ (Γ₀' ⋙ Split.nondegComplexFunctor) ⋙ toKaroubi _ := (Functor.associator _ _ _).symm
    

中文:
定义 N₁Γ₀
  签名: : Γ₀ ⋙ N₁ ≅ toKaroubi (ChainComplex C 自然数)
  定义体: calc
    Γ₀ ⋙ N₁ ≅ Γ₀' ⋙ Split.forget C ⋙ N₁ := Functor.associator _ _ _
    _ ≅ Γ₀' ⋙ Split.nondegComplexFunctor ⋙ toKaroubi _ :=
      (isoWhiskerLeft Γ₀' Split.toKaroubiNondegComplexFunctorIsoN₁.symm)
    _ ≅ (Γ₀' ⋙ Split.nondegComplexFunctor) ⋙ toKaroubi _ := (Functor.associator _ _ _).symm
    

Depends on / 依赖: ChainComplex, CompNondegComplexFunctor, Functor, Functor.associator, Functor.leftUnitor, Split.forget, Split.nondegComplexFunctor, Split.toKaroubiNondegComplexFunctorIsoN, associator, forget, isoWhiskerLeft, isoWhiskerRight, leftUnitor, nondegComplexFunctor, toKaroubi
-/
def N₁Γ₀ : Γ₀ ⋙ N₁ ≅ toKaroubi (ChainComplex C Nat) :=
  calc
    Γ₀ ⋙ N₁ ≅ Γ₀' ⋙ Split.forget C ⋙ N₁ := Functor.associator _ _ _
    _ ≅ Γ₀' ⋙ Split.nondegComplexFunctor ⋙ toKaroubi _ :=
      (isoWhiskerLeft Γ₀' Split.toKaroubiNondegComplexFunctorIsoN₁.symm)
    _ ≅ (Γ₀' ⋙ Split.nondegComplexFunctor) ⋙ toKaroubi _ := (Functor.associator _ _ _).symm
    _ ≅ 𝟭 _ ⋙ toKaroubi (ChainComplex C Nat) := isoWhiskerRight Γ₀'CompNondegComplexFunctor _
    _ ≅ toKaroubi (ChainComplex C Nat) := Functor.leftUnitor _

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/--
theorem `N₁Γ₀_app` / 定理 `N₁Γ₀_app`

English:
theorem N₁Γ₀_app
  given: (K : ChainComplex C Nat)
  proof: by
  ext
  simp [N₁Γ₀, Γ₀'CompNondegComplexFunctor]

中文:
定理 N₁Γ₀_app
  条件: (K : ChainComplex C 自然数)
  证明: by
  ext
  simp [N₁Γ₀, Γ₀'CompNondegComplexFunctor]

Depends on / 依赖: CompNondegComplexFunctor
-/
theorem N₁Γ₀_app (K : ChainComplex C Nat) :
    N₁Γ₀.app K = (Γ₀.splitting K).toKaroubiNondegComplexIsoN₁.symm ≪≫
      (toKaroubi _).mapIso (Γ₀NondegComplexIso K) := by
  ext
  simp [N₁Γ₀, Γ₀'CompNondegComplexFunctor]

/--
theorem `N₁Γ₀_hom_app` / 定理 `N₁Γ₀_hom_app`

English:
theorem N₁Γ₀_hom_app
  given: (K : ChainComplex C Nat)
  proof: by
  change (N₁Γ₀.app K).hom = _
  simp only [N₁Γ₀_app]
  rfl

中文:
定理 N₁Γ₀_hom_app
  条件: (K : ChainComplex C 自然数)
  证明: by
  change (N₁Γ₀.app K).hom = _
  simp only [N₁Γ₀_app]
  rfl
-/
theorem N₁Γ₀_hom_app (K : ChainComplex C Nat) :
    N₁Γ₀.hom.app K = (Γ₀.splitting K).toKaroubiNondegComplexIsoN₁.inv ≫
        (toKaroubi _).map (Γ₀NondegComplexIso K).hom := by
  change (N₁Γ₀.app K).hom = _
  simp only [N₁Γ₀_app]
  rfl

/--
theorem `N₁Γ₀_inv_app` / 定理 `N₁Γ₀_inv_app`

English:
theorem N₁Γ₀_inv_app
  given: (K : ChainComplex C Nat)
  proof: by
  change (N₁Γ₀.app K).inv = _
  simp only [N₁Γ₀_app]
  rfl

@[simp]

中文:
定理 N₁Γ₀_inv_app
  条件: (K : ChainComplex C 自然数)
  证明: by
  change (N₁Γ₀.app K).inv = _
  simp only [N₁Γ₀_app]
  rfl

@[simp]
-/
theorem N₁Γ₀_inv_app (K : ChainComplex C Nat) :
    N₁Γ₀.inv.app K = (toKaroubi _).map (Γ₀NondegComplexIso K).inv ≫
        (Γ₀.splitting K).toKaroubiNondegComplexIsoN₁.hom := by
  change (N₁Γ₀.app K).inv = _
  simp only [N₁Γ₀_app]
  rfl

@[simp]
/--
theorem `N₁Γ₀_hom_app_f_f` / 定理 `N₁Γ₀_hom_app_f_f`

English:
theorem N₁Γ₀_hom_app_f_f
  given: (K : ChainComplex C Nat) (n : Nat)
  proof: by
  rw [N₁Γ₀_hom_app]
  apply comp_id

@[simp]

中文:
定理 N₁Γ₀_hom_app_f_f
  条件: (K : ChainComplex C 自然数) (n : 自然数)
  证明: by
  rw [N₁Γ₀_hom_app]
  apply comp_id

@[simp]

Depends on / 依赖: comp_id
-/
theorem N₁Γ₀_hom_app_f_f (K : ChainComplex C Nat) (n : Nat) :
    (N₁Γ₀.hom.app K).f.f n = (Γ₀.splitting K).toKaroubiNondegComplexIsoN₁.inv.f.f n := by
  rw [N₁Γ₀_hom_app]
  apply comp_id

@[simp]
/--
theorem `N₁Γ₀_inv_app_f_f` / 定理 `N₁Γ₀_inv_app_f_f`

English:
theorem N₁Γ₀_inv_app_f_f
  given: (K : ChainComplex C Nat) (n : Nat)
  proof: by
  rw [N₁Γ₀_inv_app]
  apply id_comp

中文:
定理 N₁Γ₀_inv_app_f_f
  条件: (K : ChainComplex C 自然数) (n : 自然数)
  证明: by
  rw [N₁Γ₀_inv_app]
  apply id_comp

Depends on / 依赖: id_comp
-/
theorem N₁Γ₀_inv_app_f_f (K : ChainComplex C Nat) (n : Nat) :
    (N₁Γ₀.inv.app K).f.f n = (Γ₀.splitting K).toKaroubiNondegComplexIsoN₁.hom.f.f n := by
  rw [N₁Γ₀_inv_app]
  apply id_comp

/--
Definition of `N₂Γ₂ToKaroubiIso` / `N₂Γ₂ToKaroubiIso` 的定义

English:
definition N₂Γ₂ToKaroubiIso
  signature: : toKaroubi (ChainComplex C Nat) ⋙ Γ₂ ⋙ N₂ ≅ Γ₀ ⋙ N₁
  body: calc
    toKaroubi (ChainComplex C Nat) ⋙ Γ₂ ⋙ N₂ ≅
      toKaroubi (ChainComplex C Nat) ⋙ (Γ₂ ⋙ N₂) := (Functor.associator _ _ _).symm
    _ ≅ (Γ₀ ⋙ toKaroubi (SimplicialObject C)) ⋙ N₂ :=
        isoWhiskerRight ((functorExtension₂CompWhiskeringLeftToKaroubiIso _ _).app Γ₀) N₂
    _ ≅ Γ₀ ⋙ toKarou

中文:
定义 N₂Γ₂ToKaroubiIso
  签名: : toKaroubi (ChainComplex C 自然数) ⋙ Γ₂ ⋙ N₂ ≅ Γ₀ ⋙ N₁
  定义体: calc
    toKaroubi (ChainComplex C Nat) ⋙ Γ₂ ⋙ N₂ ≅
      toKaroubi (ChainComplex C Nat) ⋙ (Γ₂ ⋙ N₂) := (Functor.associator _ _ _).symm
    _ ≅ (Γ₀ ⋙ toKaroubi (SimplicialObject C)) ⋙ N₂ :=
        isoWhiskerRight ((functorExtension₂CompWhiskeringLeftToKaroubiIso _ _).app Γ₀) N₂
    _ ≅ Γ₀ ⋙ toKarou

Depends on / 依赖: ChainComplex, Functor, Functor.associator, SimplicialObject, associator, isoWhiskerLeft, isoWhiskerRight, toKaroubi
-/
def N₂Γ₂ToKaroubiIso : toKaroubi (ChainComplex C Nat) ⋙ Γ₂ ⋙ N₂ ≅ Γ₀ ⋙ N₁ :=
  calc
    toKaroubi (ChainComplex C Nat) ⋙ Γ₂ ⋙ N₂ ≅
      toKaroubi (ChainComplex C Nat) ⋙ (Γ₂ ⋙ N₂) := (Functor.associator _ _ _).symm
    _ ≅ (Γ₀ ⋙ toKaroubi (SimplicialObject C)) ⋙ N₂ :=
        isoWhiskerRight ((functorExtension₂CompWhiskeringLeftToKaroubiIso _ _).app Γ₀) N₂
    _ ≅ Γ₀ ⋙ toKaroubi (SimplicialObject C) ⋙ N₂ := Functor.associator _ _ _
    _ ≅ Γ₀ ⋙ N₁ :=
      isoWhiskerLeft Γ₀ ((functorExtension₁CompWhiskeringLeftToKaroubiIso _ _).app N₁)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
@[simp]
/--
lemma `N₂Γ₂ToKaroubiIso_hom_app` / 引理 `N₂Γ₂ToKaroubiIso_hom_app`

English:
lemma N₂Γ₂ToKaroubiIso_hom_app
  given: (X : ChainComplex C Nat)
  proof: by
  ext n
  dsimp [N₂Γ₂ToKaroubiIso]
  simp only [comp_id, assoc, PInfty_f_idem]
  conv_rhs =>
    rw [← PInfty_f_idem]
  congr 1
  apply (Γ₀.splitting X).hom_ext'
  intro A
  rw [Splitting.ι_desc_assoc]; rw [assoc]
  apply id_comp

中文:
引理 N₂Γ₂ToKaroubiIso_hom_app
  条件: (X : ChainComplex C 自然数)
  证明: by
  ext n
  dsimp [N₂Γ₂ToKaroubiIso]
  simp only [comp_id, assoc, PInfty_f_idem]
  conv_rhs =>
    rw [← PInfty_f_idem]
  congr 1
  apply (Γ₀.splitting X).hom_ext'
  intro A
  rw [Splitting.ι_desc_assoc]; rw [assoc]
  apply id_comp

Depends on / 依赖: PInfty_f_idem, Splitting, comp_id, conv_rhs, hom_ext, id_comp, splitting
-/
lemma N₂Γ₂ToKaroubiIso_hom_app (X : ChainComplex C Nat) :
    (N₂Γ₂ToKaroubiIso.hom.app X).f = PInfty := by
  ext n
  dsimp [N₂Γ₂ToKaroubiIso]
  simp only [comp_id, assoc, PInfty_f_idem]
  conv_rhs =>
    rw [← PInfty_f_idem]
  congr 1
  apply (Γ₀.splitting X).hom_ext'
  intro A
  rw [Splitting.ι_desc_assoc]; rw [assoc]
  apply id_comp

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
@[simp]
/--
lemma `N₂Γ₂ToKaroubiIso_inv_app` / 引理 `N₂Γ₂ToKaroubiIso_inv_app`

English:
lemma N₂Γ₂ToKaroubiIso_inv_app
  given: (X : ChainComplex C Nat)
  proof: by
  ext n
  dsimp [N₂Γ₂ToKaroubiIso]
  simp only [comp_id, PInfty_f_idem_assoc, AlternatingFaceMapComplex.obj_X, Γ₀_obj_obj]
  convert! comp_id _
  apply (Γ₀.splitting X).hom_ext'
  intro A
  rw [Splitting.ι_desc]
  erw [comp_id, id_comp]

中文:
引理 N₂Γ₂ToKaroubiIso_inv_app
  条件: (X : ChainComplex C 自然数)
  证明: by
  ext n
  dsimp [N₂Γ₂ToKaroubiIso]
  simp only [comp_id, PInfty_f_idem_assoc, AlternatingFaceMapComplex.obj_X, Γ₀_obj_obj]
  convert! comp_id _
  apply (Γ₀.splitting X).hom_ext'
  intro A
  rw [Splitting.ι_desc]
  erw [comp_id, id_comp]

Depends on / 依赖: AlternatingFaceMapComplex, AlternatingFaceMapComplex.obj_X, PInfty_f_idem_assoc, Splitting, comp_id, convert, hom_ext, id_comp, obj_X, splitting
-/
lemma N₂Γ₂ToKaroubiIso_inv_app (X : ChainComplex C Nat) :
    (N₂Γ₂ToKaroubiIso.inv.app X).f = PInfty := by
  ext n
  dsimp [N₂Γ₂ToKaroubiIso]
  simp only [comp_id, PInfty_f_idem_assoc, AlternatingFaceMapComplex.obj_X, Γ₀_obj_obj]
  convert! comp_id _
  apply (Γ₀.splitting X).hom_ext'
  intro A
  rw [Splitting.ι_desc]
  erw [comp_id, id_comp]

/--
Definition of `N₂Γ₂` / `N₂Γ₂` 的定义

English:
definition N₂Γ₂
  signature: : Γ₂ ⋙ N₂ ≅ 𝟭 (Karoubi (ChainComplex C Nat))
  body: ((whiskeringLeft _ _ _).obj (toKaroubi (ChainComplex C Nat))).preimageIso
      (N₂Γ₂ToKaroubiIso ≪≫ N₁Γ₀)

中文:
定义 N₂Γ₂
  签名: : Γ₂ ⋙ N₂ ≅ 𝟭 (Karoubi (ChainComplex C 自然数))
  定义体: ((whiskeringLeft _ _ _).obj (toKaroubi (ChainComplex C Nat))).preimageIso
      (N₂Γ₂ToKaroubiIso ≪≫ N₁Γ₀)

Depends on / 依赖: ChainComplex, preimageIso, toKaroubi, whiskeringLeft
-/
def N₂Γ₂ : Γ₂ ⋙ N₂ ≅ 𝟭 (Karoubi (ChainComplex C Nat)) :=
  ((whiskeringLeft _ _ _).obj (toKaroubi (ChainComplex C Nat))).preimageIso
      (N₂Γ₂ToKaroubiIso ≪≫ N₁Γ₀)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
@[simp]
/--
theorem `N₂Γ₂_inv_app_f_f` / 定理 `N₂Γ₂_inv_app_f_f`

English:
theorem N₂Γ₂_inv_app_f_f
  given: (X : Karoubi (ChainComplex C Nat)) (n : Nat)
  proof: by
  dsimp [N₂Γ₂]
  simp only [whiskeringLeft_obj_preimage_app, NatTrans.comp_app, Functor.comp_map,
    Karoubi.comp_f, N₂Γ₂ToKaroubiIso_inv_app, HomologicalComplex.comp_f,
    N₁Γ₀_inv_app_f_f, toKaroubi_obj_X, Splitting.toKaroubiNondegComplexIsoN₁_hom_f_f,
    PInfty_on_Γ₀_splitting_summand_eq_se

中文:
定理 N₂Γ₂_inv_app_f_f
  条件: (X : Karoubi (ChainComplex C 自然数)) (n : 自然数)
  证明: by
  dsimp [N₂Γ₂]
  simp only [whiskeringLeft_obj_preimage_app, NatTrans.comp_app, Functor.comp_map,
    Karoubi.comp_f, N₂Γ₂ToKaroubiIso_inv_app, HomologicalComplex.comp_f,
    N₁Γ₀_inv_app_f_f, toKaroubi_obj_X, Splitting.toKaroubiNondegComplexIsoN₁_hom_f_f,
    PInfty_on_Γ₀_splitting_summand_eq_se

Depends on / 依赖: Functor, Functor.comp_map, HomologicalComplex, HomologicalComplex.comp_f, IndexSet, Karoubi, Karoubi.HomologicalComplex.p_idem_, Karoubi.comp_f, Karoubi.decompId_p_f, NatTrans, NatTrans.comp_app, SimplexCategory, SimplexCategory.len_mk, Splitting, Splitting.IndexSet.id_fst, Splitting.toKaroubiNondegComplexIsoN, comp_app, comp_f, comp_map, decompId_p_f
-/
theorem N₂Γ₂_inv_app_f_f (X : Karoubi (ChainComplex C Nat)) (n : Nat) :
    (N₂Γ₂.inv.app X).f.f n =
      X.p.f n ≫ ((Γ₀.splitting X.X).cofan _).inj (Splitting.IndexSet.id (op ⦋n⦌)) := by
  dsimp [N₂Γ₂]
  simp only [whiskeringLeft_obj_preimage_app, NatTrans.comp_app, Functor.comp_map,
    Karoubi.comp_f, N₂Γ₂ToKaroubiIso_inv_app, HomologicalComplex.comp_f,
    N₁Γ₀_inv_app_f_f, toKaroubi_obj_X, Splitting.toKaroubiNondegComplexIsoN₁_hom_f_f,
    PInfty_on_Γ₀_splitting_summand_eq_self, N₂_map_f_f, Γ₂_map_f_app, unop_op, Karoubi.decompId_p_f,
    PInfty_on_Γ₀_splitting_summand_eq_self_assoc, Splitting.IndexSet.id_fst, SimplexCategory.len_mk,
    Splitting.ι_desc]
  apply Karoubi.HomologicalComplex.p_idem_assoc

/--
lemma `whiskerLeft_toKaroubi_N₂Γ₂_hom` / 引理 `whiskerLeft_toKaroubi_N₂Γ₂_hom`

English:
lemma whiskerLeft_toKaroubi_N₂Γ₂_hom
  proof: by
  let e : _ ≅ toKaroubi (ChainComplex C Nat) ⋙ 𝟭 _ := N₂Γ₂ToKaroubiIso ≪≫ N₁Γ₀
  have h := ((whiskeringLeft _ _ (Karoubi (ChainComplex C Nat))).obj
    (toKaroubi (ChainComplex C Nat))).map_preimage e.hom
  dsimp only [whiskeringLeft, N₂Γ₂, Functor.preimageIso] at h ⊢
  exact h

中文:
引理 whiskerLeft_toKaroubi_N₂Γ₂_hom
  证明: by
  let e : _ ≅ toKaroubi (ChainComplex C Nat) ⋙ 𝟭 _ := N₂Γ₂ToKaroubiIso ≪≫ N₁Γ₀
  have h := ((whiskeringLeft _ _ (Karoubi (ChainComplex C Nat))).obj
    (toKaroubi (ChainComplex C Nat))).map_preimage e.hom
  dsimp only [whiskeringLeft, N₂Γ₂, Functor.preimageIso] at h ⊢
  exact h

Depends on / 依赖: ChainComplex, Functor, Functor.preimageIso, Karoubi, e.hom, map_preimage, preimageIso, toKaroubi, whiskeringLeft
-/
lemma whiskerLeft_toKaroubi_N₂Γ₂_hom :
    whiskerLeft (toKaroubi (ChainComplex C Nat)) N₂Γ₂.hom = N₂Γ₂ToKaroubiIso.hom ≫ N₁Γ₀.hom := by
  let e : _ ≅ toKaroubi (ChainComplex C Nat) ⋙ 𝟭 _ := N₂Γ₂ToKaroubiIso ≪≫ N₁Γ₀
  have h := ((whiskeringLeft _ _ (Karoubi (ChainComplex C Nat))).obj
    (toKaroubi (ChainComplex C Nat))).map_preimage e.hom
  dsimp only [whiskeringLeft, N₂Γ₂, Functor.preimageIso] at h ⊢
  exact h

/--
theorem `N₂Γ₂_compatible_with_N₁Γ₀` / 定理 `N₂Γ₂_compatible_with_N₁Γ₀`

English:
theorem N₂Γ₂_compatible_with_N₁Γ₀
  given: (K : ChainComplex C Nat)
  proof: congr_app whiskerLeft_toKaroubi_N₂Γ₂_hom K

中文:
定理 N₂Γ₂_compatible_with_N₁Γ₀
  条件: (K : ChainComplex C 自然数)
  证明: congr_app whiskerLeft_toKaroubi_N₂Γ₂_hom K

Depends on / 依赖: congr_app
-/
theorem N₂Γ₂_compatible_with_N₁Γ₀ (K : ChainComplex C Nat) :
    N₂Γ₂.hom.app ((toKaroubi _).obj K) = N₂Γ₂ToKaroubiIso.hom.app K ≫ N₁Γ₀.hom.app K :=
  congr_app whiskerLeft_toKaroubi_N₂Γ₂_hom K

end DoldKan

end AlgebraicTopology
