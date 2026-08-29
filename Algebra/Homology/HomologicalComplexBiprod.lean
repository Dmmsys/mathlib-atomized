/-
Copyright (c) 2023 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.Algebra.Homology.HomologicalComplexLimits
public import Mathlib.Algebra.Homology.Additive

/-! # Binary biproducts of homological complexes

In this file, it is shown that if two homological complex `K` and `L` in
a preadditive category are such that for all `i : ι`, the binary biproduct
`K.X i ⊞ L.X i` exists, then `K ⊞ L` exists, and there is an isomorphism
`biprodXIso K L i : (K ⊞ L).X i ≅ (K.X i) ⊞ (L.X i)`.

-/

@[expose] public section
open CategoryTheory Limits

namespace HomologicalComplex

variable {C ι : Type*} [Category* C] [Preadditive C] {c : ComplexShape ι}
  (K L : HomologicalComplex C c) [forall i, HasBinaryBiproduct (K.X i) (L.X i)]

instance (i : ι) : HasBinaryBiproduct ((eval C c i).obj K) ((eval C c i).obj L) := by
  dsimp [eval]
  infer_instance

instance (i : ι) : HasLimit ((pair K L) ⋙ (eval C c i)) := by
  have e : _ ≅ pair (K.X i) (L.X i) := diagramIsoPair (pair K L ⋙ eval C c i)
  exact hasLimit_of_iso e.symm

instance (i : ι) : HasColimit ((pair K L) ⋙ (eval C c i)) := by
  have e : _ ≅ pair (K.X i) (L.X i) := diagramIsoPair (pair K L ⋙ eval C c i)
  exact hasColimit_of_iso e

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: HasBinaryBiproduct K L
  body: HasBinaryBiproduct.of_hasBinaryProduct _ _

中文:
实例 :
  签名: HasBinaryBiproduct K L
  定义体: HasBinaryBiproduct.of_hasBinaryProduct _ _

Depends on / 依赖: HasBinaryBiproduct, HasBinaryBiproduct.of_hasBinaryProduct, of_hasBinaryProduct
-/
instance : HasBinaryBiproduct K L := HasBinaryBiproduct.of_hasBinaryProduct _ _

instance (i : ι) : PreservesBinaryBiproduct K L (eval C c i) :=
  preservesBinaryBiproduct_of_preservesBinaryProduct _

/--
Definition of `biprodXIso` / `biprodXIso` 的定义

English:
definition biprodXIso
  signature: (i : ι)
  body: (eval C c i).mapBiprod K L

中文:
定义 biprodXIso
  签名: (i : ι)
  定义体: (eval C c i).mapBiprod K L

Depends on / 依赖: mapBiprod
-/
noncomputable def biprodXIso (i : ι) : (K ⊞ L).X i ≅ (K.X i) ⊞ (L.X i) :=
  (eval C c i).mapBiprod K L

set_option backward.defeqAttrib.useBackward true in
@[reassoc (attr := simp)]
/--
lemma `inl_biprodXIso_inv` / 引理 `inl_biprodXIso_inv`

English:
lemma inl_biprodXIso_inv
  given: (i : ι)
  proof: by
  simp [biprodXIso]

中文:
引理 inl_biprodXIso_inv
  条件: (i : ι)
  证明: by
  simp [biprodXIso]

Depends on / 依赖: biprodXIso
-/
lemma inl_biprodXIso_inv (i : ι) :
    biprod.inl ≫ (biprodXIso K L i).inv = (biprod.inl : K ⟶ K ⊞ L).f i := by
  simp [biprodXIso]

set_option backward.defeqAttrib.useBackward true in
@[reassoc (attr := simp)]
/--
lemma `inr_biprodXIso_inv` / 引理 `inr_biprodXIso_inv`

English:
lemma inr_biprodXIso_inv
  given: (i : ι)
  proof: by
  simp [biprodXIso]

中文:
引理 inr_biprodXIso_inv
  条件: (i : ι)
  证明: by
  simp [biprodXIso]

Depends on / 依赖: biprodXIso
-/
lemma inr_biprodXIso_inv (i : ι) :
    biprod.inr ≫ (biprodXIso K L i).inv = (biprod.inr : L ⟶ K ⊞ L).f i := by
  simp [biprodXIso]

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
@[reassoc (attr := simp)]
/--
lemma `biprodXIso_hom_fst` / 引理 `biprodXIso_hom_fst`

English:
lemma biprodXIso_hom_fst
  given: (i : ι)
  proof: by
  simp [biprodXIso]

中文:
引理 biprodXIso_hom_fst
  条件: (i : ι)
  证明: by
  simp [biprodXIso]

Depends on / 依赖: biprodXIso
-/
lemma biprodXIso_hom_fst (i : ι) :
    (biprodXIso K L i).hom ≫ biprod.fst = (biprod.fst : K ⊞ L ⟶ K).f i := by
  simp [biprodXIso]

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
@[reassoc (attr := simp)]
/--
lemma `biprodXIso_hom_snd` / 引理 `biprodXIso_hom_snd`

English:
lemma biprodXIso_hom_snd
  given: (i : ι)
  proof: by
  simp [biprodXIso]

@[reassoc (attr := simp)]

中文:
引理 biprodXIso_hom_snd
  条件: (i : ι)
  证明: by
  simp [biprodXIso]

@[reassoc (attr := simp)]

Depends on / 依赖: biprodXIso
-/
lemma biprodXIso_hom_snd (i : ι) :
    (biprodXIso K L i).hom ≫ biprod.snd = (biprod.snd : K ⊞ L ⟶ L).f i := by
  simp [biprodXIso]

@[reassoc (attr := simp)]
/--
lemma `biprod_inl_fst_f` / 引理 `biprod_inl_fst_f`

English:
lemma biprod_inl_fst_f
  given: (i : ι)
  proof: by
  rw [← comp_f]; rw [biprod.inl_fst]; rw [id_f]

@[reassoc (attr := simp)]

中文:
引理 biprod_inl_fst_f
  条件: (i : ι)
  证明: by
  rw [← comp_f]; rw [biprod.inl_fst]; rw [id_f]

@[reassoc (attr := simp)]

Depends on / 依赖: biprod, biprod.inl_fst, comp_f, id_f, inl_fst
-/
lemma biprod_inl_fst_f (i : ι) :
    (biprod.inl : K ⟶ K ⊞ L).f i ≫ (biprod.fst : K ⊞ L ⟶ K).f i = 𝟙 _ := by
  rw [← comp_f]; rw [biprod.inl_fst]; rw [id_f]

@[reassoc (attr := simp)]
/--
lemma `biprod_inl_snd_f` / 引理 `biprod_inl_snd_f`

English:
lemma biprod_inl_snd_f
  given: (i : ι)
  proof: by
  rw [← comp_f]; rw [biprod.inl_snd]; rw [zero_f]

@[reassoc (attr := simp)]

中文:
引理 biprod_inl_snd_f
  条件: (i : ι)
  证明: by
  rw [← comp_f]; rw [biprod.inl_snd]; rw [zero_f]

@[reassoc (attr := simp)]

Depends on / 依赖: biprod, biprod.inl_snd, comp_f, inl_snd, zero_f
-/
lemma biprod_inl_snd_f (i : ι) :
    (biprod.inl : K ⟶ K ⊞ L).f i ≫ (biprod.snd : K ⊞ L ⟶ L).f i = 0 := by
  rw [← comp_f]; rw [biprod.inl_snd]; rw [zero_f]

@[reassoc (attr := simp)]
/--
lemma `biprod_inr_fst_f` / 引理 `biprod_inr_fst_f`

English:
lemma biprod_inr_fst_f
  given: (i : ι)
  proof: by
  rw [← comp_f]; rw [biprod.inr_fst]; rw [zero_f]

@[reassoc (attr := simp)]

中文:
引理 biprod_inr_fst_f
  条件: (i : ι)
  证明: by
  rw [← comp_f]; rw [biprod.inr_fst]; rw [zero_f]

@[reassoc (attr := simp)]

Depends on / 依赖: biprod, biprod.inr_fst, comp_f, inr_fst, zero_f
-/
lemma biprod_inr_fst_f (i : ι) :
    (biprod.inr : L ⟶ K ⊞ L).f i ≫ (biprod.fst : K ⊞ L ⟶ K).f i = 0 := by
  rw [← comp_f]; rw [biprod.inr_fst]; rw [zero_f]

@[reassoc (attr := simp)]
/--
lemma `biprod_inr_snd_f` / 引理 `biprod_inr_snd_f`

English:
lemma biprod_inr_snd_f
  given: (i : ι)
  proof: by
  rw [← comp_f]; rw [biprod.inr_snd]; rw [id_f]

@[simp]

中文:
引理 biprod_inr_snd_f
  条件: (i : ι)
  证明: by
  rw [← comp_f]; rw [biprod.inr_snd]; rw [id_f]

@[simp]

Depends on / 依赖: biprod, biprod.inr_snd, comp_f, id_f, inr_snd
-/
lemma biprod_inr_snd_f (i : ι) :
    (biprod.inr : L ⟶ K ⊞ L).f i ≫ (biprod.snd : K ⊞ L ⟶ L).f i = 𝟙 _ := by
  rw [← comp_f]; rw [biprod.inr_snd]; rw [id_f]

@[simp]
/--
lemma `biprod_total_f` / 引理 `biprod_total_f`

English:
lemma biprod_total_f
  given: (i : ι)
  proof: by
  simp [← comp_f, ← add_f_apply]

中文:
引理 biprod_total_f
  条件: (i : ι)
  证明: by
  simp [← comp_f, ← add_f_apply]

Depends on / 依赖: add_f_apply, comp_f, infer_instance, singleFunctors
-/
lemma biprod_total_f (i : ι) :
    (biprod.fst : K ⊞ L ⟶ K).f i ≫ (biprod.inl : K ⟶ K ⊞ L).f i +
      (biprod.snd : K ⊞ L ⟶ L).f i ≫ (biprod.inr : L ⟶ K ⊞ L).f i =
    𝟙 ((biprod K L).X i) := by
  simp [← comp_f, ← add_f_apply]

variable {K L}

section

variable {A : C} {i : ι}

/--
lemma `biprodX_ext_from_iff` / 引理 `biprodX_ext_from_iff`

English:
lemma biprodX_ext_from_iff
  given: {f g : (K ⊞ L).X i ⟶ A}
  proof: by
  refine ⟨by rintro rfl; simp, fun ⟨h₁, h₂⟩ => ?_⟩
  rw [← cancel_epi (𝟙 _)]
  simp [← biprod_total_f, h₁, h₂]

@[ext]

中文:
引理 biprodX_ext_from_iff
  条件: {f g : (K ⊞ L).X i ⟶ A}
  证明: by
  refine ⟨by rintro rfl; simp, fun ⟨h₁, h₂⟩ => ?_⟩
  rw [← cancel_epi (𝟙 _)]
  simp [← biprod_total_f, h₁, h₂]

@[ext]

Depends on / 依赖: CochainComplex, CochainComplex.singleFunctors, HomologicalComplex, HomologicalComplex.single, biprod_total_f, cancel_epi, single, singleFunctors
-/
lemma biprodX_ext_from_iff {f g : (K ⊞ L).X i ⟶ A} :
    f = g ↔ (biprod.inl : K ⟶ K ⊞ L).f i ≫ f = (biprod.inl : K ⟶ K ⊞ L).f i ≫ g ∧
      (biprod.inr : L ⟶ K ⊞ L).f i ≫ f = (biprod.inr : L ⟶ K ⊞ L).f i ≫ g := by
  refine ⟨by rintro rfl; simp, fun ⟨h₁, h₂⟩ => ?_⟩
  rw [← cancel_epi (𝟙 _)]
  simp [← biprod_total_f, h₁, h₂]

@[ext]
/--
lemma `biprodX_ext_from` / 引理 `biprodX_ext_from`

English:
lemma biprodX_ext_from
  statement: {f g : (K ⊞ L).X i ⟶ A}
  proof: by
  simp [biprodX_ext_from_iff, h₁, h₂]

中文:
引理 biprodX_ext_from
  结论: {f g : (K ⊞ L).X i ⟶ A}
  证明: by
  simp [biprodX_ext_from_iff, h₁, h₂]

Depends on / 依赖: biprodX_ext_from_iff
-/
lemma biprodX_ext_from {f g : (K ⊞ L).X i ⟶ A}
    (h₁ : (biprod.inl : K ⟶ K ⊞ L).f i ≫ f = (biprod.inl : K ⟶ K ⊞ L).f i ≫ g)
    (h₂ : (biprod.inr : L ⟶ K ⊞ L).f i ≫ f = (biprod.inr : L ⟶ K ⊞ L).f i ≫ g) :
    f = g := by
  simp [biprodX_ext_from_iff, h₁, h₂]

/--
lemma `biprodX_ext_to_iff` / 引理 `biprodX_ext_to_iff`

English:
lemma biprodX_ext_to_iff
  given: {f g : A ⟶ (K ⊞ L).X i}
  proof: by
  refine ⟨by rintro rfl; simp, fun ⟨h₁, h₂⟩ => ?_⟩
  rw [← cancel_mono (𝟙 _)]
  simp [← biprod_total_f, reassoc_of% h₁, reassoc_of% h₂]

@[ext]

中文:
引理 biprodX_ext_to_iff
  条件: {f g : A ⟶ (K ⊞ L).X i}
  证明: by
  refine ⟨by rintro rfl; simp, fun ⟨h₁, h₂⟩ => ?_⟩
  rw [← cancel_mono (𝟙 _)]
  simp [← biprod_total_f, reassoc_of% h₁, reassoc_of% h₂]

@[ext]

Depends on / 依赖: biprod_total_f, cancel_mono, reassoc_of
-/
lemma biprodX_ext_to_iff {f g : A ⟶ (K ⊞ L).X i} :
    f = g ↔ f ≫ (biprod.fst : K ⊞ L ⟶ K).f i = g ≫ (biprod.fst : K ⊞ L ⟶ K).f i ∧
      f ≫ (biprod.snd : K ⊞ L ⟶ L).f i = g ≫ (biprod.snd : K ⊞ L ⟶ L).f i := by
  refine ⟨by rintro rfl; simp, fun ⟨h₁, h₂⟩ => ?_⟩
  rw [← cancel_mono (𝟙 _)]
  simp [← biprod_total_f, reassoc_of% h₁, reassoc_of% h₂]

@[ext]
/--
lemma `biprodX_ext_to` / 引理 `biprodX_ext_to`

English:
lemma biprodX_ext_to
  statement: {f g : A ⟶ (K ⊞ L).X i}
  proof: by
  simp [biprodX_ext_to_iff, h₁, h₂]

中文:
引理 biprodX_ext_to
  结论: {f g : A ⟶ (K ⊞ L).X i}
  证明: by
  simp [biprodX_ext_to_iff, h₁, h₂]

Depends on / 依赖: biprodX_ext_to_iff, single
-/
lemma biprodX_ext_to {f g : A ⟶ (K ⊞ L).X i}
    (h₁ : f ≫ (biprod.fst : K ⊞ L ⟶ K).f i = g ≫ (biprod.fst : K ⊞ L ⟶ K).f i)
    (h₂ : f ≫ (biprod.snd : K ⊞ L ⟶ L).f i = g ≫ (biprod.snd : K ⊞ L ⟶ L).f i) :
    f = g := by
  simp [biprodX_ext_to_iff, h₁, h₂]

end

variable {M : HomologicalComplex C c}

@[reassoc (attr := simp)]
/--
lemma `biprod_inl_desc_f` / 引理 `biprod_inl_desc_f`

English:
lemma biprod_inl_desc_f
  given: (α : K ⟶ M) (β : L ⟶ M) (i : ι)
  proof: by
  rw [← comp_f]; rw [biprod.inl_desc]

@[reassoc (attr := simp)]

中文:
引理 biprod_inl_desc_f
  条件: (α : K ⟶ M) (β : L ⟶ M) (i : ι)
  证明: by
  rw [← comp_f]; rw [biprod.inl_desc]

@[reassoc (attr := simp)]

Depends on / 依赖: Faithful, biprod, biprod.inl_desc, comp_f, inl_desc, single
-/
lemma biprod_inl_desc_f (α : K ⟶ M) (β : L ⟶ M) (i : ι) :
    (biprod.inl : K ⟶ K ⊞ L).f i ≫ (biprod.desc α β).f i = α.f i := by
  rw [← comp_f]; rw [biprod.inl_desc]

@[reassoc (attr := simp)]
/--
lemma `biprod_inr_desc_f` / 引理 `biprod_inr_desc_f`

English:
lemma biprod_inr_desc_f
  given: (α : K ⟶ M) (β : L ⟶ M) (i : ι)
  proof: by
  rw [← comp_f]; rw [biprod.inr_desc]

@[reassoc (attr := simp)]

中文:
引理 biprod_inr_desc_f
  条件: (α : K ⟶ M) (β : L ⟶ M) (i : ι)
  证明: by
  rw [← comp_f]; rw [biprod.inr_desc]

@[reassoc (attr := simp)]

Depends on / 依赖: biprod, biprod.inr_desc, comp_f, inr_desc
-/
lemma biprod_inr_desc_f (α : K ⟶ M) (β : L ⟶ M) (i : ι) :
    (biprod.inr : L ⟶ K ⊞ L).f i ≫ (biprod.desc α β).f i = β.f i := by
  rw [← comp_f]; rw [biprod.inr_desc]

@[reassoc (attr := simp)]
/--
lemma `biprod_lift_fst_f` / 引理 `biprod_lift_fst_f`

English:
lemma biprod_lift_fst_f
  given: (α : M ⟶ K) (β : M ⟶ L) (i : ι)
  proof: by
  rw [← comp_f]; rw [biprod.lift_fst]

@[reassoc (attr := simp)]

中文:
引理 biprod_lift_fst_f
  条件: (α : M ⟶ K) (β : M ⟶ L) (i : ι)
  证明: by
  rw [← comp_f]; rw [biprod.lift_fst]

@[reassoc (attr := simp)]

Depends on / 依赖: biprod, biprod.lift_fst, comp_f, lift_fst
-/
lemma biprod_lift_fst_f (α : M ⟶ K) (β : M ⟶ L) (i : ι) :
    (biprod.lift α β).f i ≫ (biprod.fst : K ⊞ L ⟶ K).f i = α.f i := by
  rw [← comp_f]; rw [biprod.lift_fst]

@[reassoc (attr := simp)]
/--
lemma `biprod_lift_snd_f` / 引理 `biprod_lift_snd_f`

English:
lemma biprod_lift_snd_f
  given: (α : M ⟶ K) (β : M ⟶ L) (i : ι)
  proof: by
  rw [← comp_f]; rw [biprod.lift_snd]

中文:
引理 biprod_lift_snd_f
  条件: (α : M ⟶ K) (β : M ⟶ L) (i : ι)
  证明: by
  rw [← comp_f]; rw [biprod.lift_snd]

Depends on / 依赖: biprod, biprod.lift_snd, comp_f, lift_snd
-/
lemma biprod_lift_snd_f (α : M ⟶ K) (β : M ⟶ L) (i : ι) :
    (biprod.lift α β).f i ≫ (biprod.snd : K ⊞ L ⟶ L).f i = β.f i := by
  rw [← comp_f]; rw [biprod.lift_snd]

end HomologicalComplex
