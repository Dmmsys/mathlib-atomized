/-
Copyright (c) 2022 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
module

public import Mathlib.CategoryTheory.Comma.Over.Pullback
public import Mathlib.CategoryTheory.Limits.Shapes.KernelPair
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.Assoc

/-!
# The diagonal object of a morphism.

We provide various API and isomorphisms considering the diagonal object `Δ_{Y/X} := pullback f f`
of a morphism `f : X ⟶ Y`.

-/

@[expose] public section


open CategoryTheory

noncomputable section

namespace CategoryTheory.Limits

variable {C : Type*} [Category* C] {X Y Z : C}

namespace pullback

section Diagonal

variable (f : X ⟶ Y) [HasPullback f f]

/--
Definition of `diagonalObj` / `diagonalObj` 的定义

English:
abbreviation diagonalObj
  signature: : C
  body: pullback f f

中文:
缩写 diagonalObj
  签名: : C
  定义体: pullback f f

Depends on / 依赖: pullback
-/
abbrev diagonalObj : C :=
  pullback f f

/--
Definition of `diagonal` / `diagonal` 的定义

English:
definition diagonal
  signature: : X ⟶ diagonalObj f
  body: pullback.lift (𝟙 _) (𝟙 _) rfl

@[reassoc (attr := simp)]

中文:
定义 diagonal
  签名: : X ⟶ diagonalObj f
  定义体: pullback.lift (𝟙 _) (𝟙 _) rfl

@[reassoc (attr := simp)]

Depends on / 依赖: pullback, pullback.lift
-/
def diagonal : X ⟶ diagonalObj f :=
  pullback.lift (𝟙 _) (𝟙 _) rfl

@[reassoc (attr := simp)]
/--
theorem `diagonal_fst` / 定理 `diagonal_fst`

English:
theorem diagonal_fst
  statement: diagonal f ≫ pullback.fst _ _ = 𝟙 _
  proof: pullback.lift_fst _ _ _

@[reassoc (attr := simp)]

中文:
定理 diagonal_fst
  结论: diagonal f ≫ pullback.fst _ _ = 𝟙 _
  证明: pullback.lift_fst _ _ _

@[reassoc (attr := simp)]

Depends on / 依赖: lift_fst, pullback, pullback.lift_fst
-/
theorem diagonal_fst : diagonal f ≫ pullback.fst _ _ = 𝟙 _ :=
  pullback.lift_fst _ _ _

@[reassoc (attr := simp)]
/--
theorem `diagonal_snd` / 定理 `diagonal_snd`

English:
theorem diagonal_snd
  statement: diagonal f ≫ pullback.snd _ _ = 𝟙 _
  proof: pullback.lift_snd _ _ _

中文:
定理 diagonal_snd
  结论: diagonal f ≫ pullback.snd _ _ = 𝟙 _
  证明: pullback.lift_snd _ _ _

Depends on / 依赖: lift_snd, pullback, pullback.lift_snd
-/
theorem diagonal_snd : diagonal f ≫ pullback.snd _ _ = 𝟙 _ :=
  pullback.lift_snd _ _ _

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: IsSplitMono (diagonal f)
  body: ⟨⟨⟨pullback.fst _ _, diagonal_fst f⟩⟩⟩

中文:
实例 :
  签名: IsSplitMono (diagonal f)
  定义体: ⟨⟨⟨pullback.fst _ _, diagonal_fst f⟩⟩⟩

Depends on / 依赖: diagonal_fst, pullback, pullback.fst
-/
instance : IsSplitMono (diagonal f) :=
  ⟨⟨⟨pullback.fst _ _, diagonal_fst f⟩⟩⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: IsSplitEpi (pullback.fst f f)
  body: ⟨⟨⟨diagonal f, diagonal_fst f⟩⟩⟩

中文:
实例 :
  签名: IsSplitEpi (pullback.fst f f)
  定义体: ⟨⟨⟨diagonal f, diagonal_fst f⟩⟩⟩

Depends on / 依赖: diagonal, diagonal_fst
-/
instance : IsSplitEpi (pullback.fst f f) :=
  ⟨⟨⟨diagonal f, diagonal_fst f⟩⟩⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: IsSplitEpi (pullback.snd f f)
  body: ⟨⟨⟨diagonal f, diagonal_snd f⟩⟩⟩

中文:
实例 :
  签名: IsSplitEpi (pullback.snd f f)
  定义体: ⟨⟨⟨diagonal f, diagonal_snd f⟩⟩⟩

Depends on / 依赖: diagonal, diagonal_snd
-/
instance : IsSplitEpi (pullback.snd f f) :=
  ⟨⟨⟨diagonal f, diagonal_snd f⟩⟩⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Mono
  signature: f] : IsIso (diagonal f)
  body: by
  rw [(IsIso.inv_eq_of_inv_hom_id (diagonal_fst f)).symm]
  infer_instance

中文:
实例 [Mono
  签名: f] : IsIso (diagonal f)
  定义体: by
  rw [(IsIso.inv_eq_of_inv_hom_id (diagonal_fst f)).symm]
  infer_instance

Depends on / 依赖: IsIso.inv_eq_of_inv_hom_id, diagonal_fst, infer_instance, inv_eq_of_inv_hom_id
-/
instance [Mono f] : IsIso (diagonal f) := by
  rw [(IsIso.inv_eq_of_inv_hom_id (diagonal_fst f)).symm]
  infer_instance

/--
lemma `isIso_diagonal_iff` / 引理 `isIso_diagonal_iff`

English:
lemma isIso_diagonal_iff
  statement: IsIso (diagonal f) ↔ Mono f
  proof: ⟨fun H => ⟨fun _ _ e => by rw [← lift_fst _ _ e, (cancel_epi (g := fst f f) (h := snd f f)
    (diagonal f)).mp (by simp), lift_snd]⟩, fun _ => inferInstance⟩

中文:
引理 isIso_diagonal_iff
  结论: IsIso (diagonal f) ↔ Mono f
  证明: ⟨fun H => ⟨fun _ _ e => by rw [← lift_fst _ _ e, (cancel_epi (g := fst f f) (h := snd f f)
    (diagonal f)).mp (by simp), lift_snd]⟩, fun _ => inferInstance⟩

Depends on / 依赖: cancel_epi, diagonal, lift_fst, lift_snd
-/
lemma isIso_diagonal_iff : IsIso (diagonal f) ↔ Mono f :=
  ⟨fun H => ⟨fun _ _ e => by rw [← lift_fst _ _ e, (cancel_epi (g := fst f f) (h := snd f f)
    (diagonal f)).mp (by simp), lift_snd]⟩, fun _ => inferInstance⟩

/--
theorem `diagonal_isKernelPair` / 定理 `diagonal_isKernelPair`

English:
theorem diagonal_isKernelPair
  statement: IsKernelPair f (pullback.fst f f) (pullback.snd f f)
  proof: IsPullback.of_hasPullback f f

中文:
定理 diagonal_isKernelPair
  结论: IsKernelPair f (pullback.fst f f) (pullback.snd f f)
  证明: IsPullback.of_hasPullback f f

Depends on / 依赖: IsPullback, IsPullback.of_hasPullback, of_hasPullback
-/
theorem diagonal_isKernelPair : IsKernelPair f (pullback.fst f f) (pullback.snd f f) :=
  IsPullback.of_hasPullback f f

end Diagonal

end pullback

section Diagonal

variable [HasPullbacks C]

open pullback

section

variable {U V₁ V₂ : C} (f : X ⟶ Y) (i : U ⟶ Y)
variable (i₁ : V₁ ⟶ pullback f i) (i₂ : V₂ ⟶ pullback f i)

@[reassoc (attr := simp)]
/--
theorem `pullback_diagonal_map_snd_fst_fst` / 定理 `pullback_diagonal_map_snd_fst_fst`

English:
theorem pullback_diagonal_map_snd_fst_fst
  proof: by
  conv_rhs => rw [← Category.comp_id (pullback.fst _ _)]
  rw [← diagonal_fst f]; rw [pullback.condition_assoc]; rw [pullback.lift_fst]

@[reassoc (attr := simp)]

中文:
定理 pullback_diagonal_map_snd_fst_fst
  证明: by
  conv_rhs => rw [← Category.comp_id (pullback.fst _ _)]
  rw [← diagonal_fst f]; rw [pullback.condition_assoc]; rw [pullback.lift_fst]

@[reassoc (attr := simp)]

Depends on / 依赖: Category, Category.comp_id, comp_id, condition_assoc, conv_rhs, diagonal_fst, lift_fst, pullback, pullback.condition_assoc, pullback.fst, pullback.lift_fst
-/
theorem pullback_diagonal_map_snd_fst_fst :
    (pullback.snd (diagonal f)
      (map (i₁ ≫ snd f i) (i₂ ≫ snd f i) f f (i₁ ≫ fst f i) (i₂ ≫ fst f i) i
        (by simp [condition]) (by simp [condition]))) ≫
      fst _ _ ≫ i₁ ≫ fst _ _ =
      pullback.fst _ _ := by
  conv_rhs => rw [← Category.comp_id (pullback.fst _ _)]
  rw [← diagonal_fst f]; rw [pullback.condition_assoc]; rw [pullback.lift_fst]

@[reassoc (attr := simp)]
/--
theorem `pullback_diagonal_map_snd_snd_fst` / 定理 `pullback_diagonal_map_snd_snd_fst`

English:
theorem pullback_diagonal_map_snd_snd_fst
  proof: by
  conv_rhs => rw [← Category.comp_id (pullback.fst _ _)]
  rw [← diagonal_snd f]; rw [pullback.condition_assoc]; rw [pullback.lift_snd]

中文:
定理 pullback_diagonal_map_snd_snd_fst
  证明: by
  conv_rhs => rw [← Category.comp_id (pullback.fst _ _)]
  rw [← diagonal_snd f]; rw [pullback.condition_assoc]; rw [pullback.lift_snd]

Depends on / 依赖: Category, Category.comp_id, comp_id, condition_assoc, conv_rhs, diagonal_snd, lift_snd, pullback, pullback.condition_assoc, pullback.fst, pullback.lift_snd
-/
theorem pullback_diagonal_map_snd_snd_fst :
    (pullback.snd (diagonal f)
      (map (i₁ ≫ snd f i) (i₂ ≫ snd f i) f f (i₁ ≫ fst f i) (i₂ ≫ fst f i) i
        (by simp [condition]) (by simp [condition]))) ≫
      snd _ _ ≫ i₂ ≫ fst _ _ =
      pullback.fst _ _ := by
  conv_rhs => rw [← Category.comp_id (pullback.fst _ _)]
  rw [← diagonal_snd f]; rw [pullback.condition_assoc]; rw [pullback.lift_snd]

variable [HasPullback i₁ i₂]

/--
Definition of `pullbackDiagonalMapIso.hom` / `pullbackDiagonalMapIso.hom` 的定义

English:
abbreviation pullbackDiagonalMapIso.hom
  signature: :
  body: pullback.lift (pullback.snd _ _ ≫ pullback.fst _ _) (pullback.snd _ _ ≫ pullback.snd _ _) (by
  ext
  · simp only [Category.assoc, pullback_diagonal_map_snd_fst_fst,
      pullback_diagonal_map_snd_snd_fst]
  · simp only [Category.assoc, condition])

中文:
缩写 pullbackDiagonalMapIso.hom
  签名: :
  定义体: pullback.lift (pullback.snd _ _ ≫ pullback.fst _ _) (pullback.snd _ _ ≫ pullback.snd _ _) (by
  ext
  · simp only [Category.assoc, pullback_diagonal_map_snd_fst_fst,
      pullback_diagonal_map_snd_snd_fst]
  · simp only [Category.assoc, condition])

Depends on / 依赖: Category, Category.assoc, condition, pullback, pullback.fst, pullback.lift, pullback.snd, pullback_diagonal_map_snd_fst_fst, pullback_diagonal_map_snd_snd_fst
-/
abbrev pullbackDiagonalMapIso.hom :
    pullback (diagonal f)
        (map (i₁ ≫ snd _ _) (i₂ ≫ snd _ _) f f (i₁ ≫ fst _ _) (i₂ ≫ fst _ _) i
          (by simp only [Category.assoc, condition])
          (by simp only [Category.assoc, condition])) ⟶
      pullback i₁ i₂ :=
  pullback.lift (pullback.snd _ _ ≫ pullback.fst _ _) (pullback.snd _ _ ≫ pullback.snd _ _) (by
  ext
  · simp only [Category.assoc, pullback_diagonal_map_snd_fst_fst,
      pullback_diagonal_map_snd_snd_fst]
  · simp only [Category.assoc, condition])

set_option backward.isDefEq.respectTransparency false in
/--
Definition of `pullbackDiagonalMapIso.inv` / `pullbackDiagonalMapIso.inv` 的定义

English:
abbreviation pullbackDiagonalMapIso.inv
  signature: : pullback i₁ i₂ ⟶
  body: pullback.lift (pullback.fst _ _ ≫ i₁ ≫ pullback.fst _ _)
      (pullback.map _ _ _ _ (𝟙 _) (𝟙 _) (pullback.snd _ _) (Category.id_comp _).symm
        (Category.id_comp _).symm) (by
        ext
        · simp only [Category.assoc, diagonal_fst, Category.comp_id, limit.lift_π,
          PullbackCone.m

中文:
缩写 pullbackDiagonalMapIso.inv
  签名: : pullback i₁ i₂ ⟶
  定义体: pullback.lift (pullback.fst _ _ ≫ i₁ ≫ pullback.fst _ _)
      (pullback.map _ _ _ _ (𝟙 _) (𝟙 _) (pullback.snd _ _) (Category.id_comp _).symm
        (Category.id_comp _).symm) (by
        ext
        · simp only [Category.assoc, diagonal_fst, Category.comp_id, limit.lift_π,
          PullbackCone.m

Depends on / 依赖: Category, Category.assoc, Category.comp_id, Category.id_comp, PullbackCone, PullbackCone.mk_, comp_id, condition_assoc, cospan_left, cospan_right, diagonal_fst, diagonal_snd, id_comp, limit.lift_, pullback, pullback.fst, pullback.lift, pullback.map, pullback.snd
-/
abbrev pullbackDiagonalMapIso.inv : pullback i₁ i₂ ⟶
    pullback (diagonal f)
        (map (i₁ ≫ snd _ _) (i₂ ≫ snd _ _) f f (i₁ ≫ fst _ _) (i₂ ≫ fst _ _) i
          (by simp only [Category.assoc, condition])
          (by simp only [Category.assoc, condition])) :=
    pullback.lift (pullback.fst _ _ ≫ i₁ ≫ pullback.fst _ _)
      (pullback.map _ _ _ _ (𝟙 _) (𝟙 _) (pullback.snd _ _) (Category.id_comp _).symm
        (Category.id_comp _).symm) (by
        ext
        · simp only [Category.assoc, diagonal_fst, Category.comp_id, limit.lift_π,
          PullbackCone.mk_π_app, limit.lift_π_assoc, cospan_left]
        · simp only [condition_assoc, Category.assoc, diagonal_snd, Category.comp_id, limit.lift_π,
          PullbackCone.mk_π_app, limit.lift_π_assoc, cospan_right])

set_option backward.isDefEq.respectTransparency false in
/--
Definition of `pullbackDiagonalMapIso` / `pullbackDiagonalMapIso` 的定义

English:
definition pullbackDiagonalMapIso
  signature: :
  body: pullbackDiagonalMapIso.hom f i i₁ i₂
  inv := pullbackDiagonalMapIso.inv f i i₁ i₂

中文:
定义 pullbackDiagonalMapIso
  签名: :
  定义体: pullbackDiagonalMapIso.hom f i i₁ i₂
  inv := pullbackDiagonalMapIso.inv f i i₁ i₂

Depends on / 依赖: pullbackDiagonalMapIso, pullbackDiagonalMapIso.hom
-/
def pullbackDiagonalMapIso :
    pullback (diagonal f)
        (map (i₁ ≫ snd _ _) (i₂ ≫ snd _ _) f f (i₁ ≫ fst _ _) (i₂ ≫ fst _ _) i
          (by simp only [Category.assoc, condition])
          (by simp only [Category.assoc, condition])) ≅
      pullback i₁ i₂ where
  hom := pullbackDiagonalMapIso.hom f i i₁ i₂
  inv := pullbackDiagonalMapIso.inv f i i₁ i₂

set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
/--
theorem `pullbackDiagonalMapIso.hom_fst` / 定理 `pullbackDiagonalMapIso.hom_fst`

English:
theorem pullbackDiagonalMapIso.hom_fst
  proof: by
  delta pullbackDiagonalMapIso
  simp only [limit.lift_π, PullbackCone.mk_π_app]

中文:
定理 pullbackDiagonalMapIso.hom_fst
  证明: by
  delta pullbackDiagonalMapIso
  simp only [limit.lift_π, PullbackCone.mk_π_app]

Depends on / 依赖: PullbackCone, PullbackCone.mk_, limit.lift_, pullbackDiagonalMapIso
-/
theorem pullbackDiagonalMapIso.hom_fst :
    (pullbackDiagonalMapIso f i i₁ i₂).hom ≫ pullback.fst _ _ =
      pullback.snd _ _ ≫ pullback.fst _ _ := by
  delta pullbackDiagonalMapIso
  simp only [limit.lift_π, PullbackCone.mk_π_app]

set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
/--
theorem `pullbackDiagonalMapIso.hom_snd` / 定理 `pullbackDiagonalMapIso.hom_snd`

English:
theorem pullbackDiagonalMapIso.hom_snd
  proof: by
  delta pullbackDiagonalMapIso
  simp only [limit.lift_π, PullbackCone.mk_π_app]

中文:
定理 pullbackDiagonalMapIso.hom_snd
  证明: by
  delta pullbackDiagonalMapIso
  simp only [limit.lift_π, PullbackCone.mk_π_app]

Depends on / 依赖: PullbackCone, PullbackCone.mk_, limit.lift_, pullbackDiagonalMapIso
-/
theorem pullbackDiagonalMapIso.hom_snd :
    (pullbackDiagonalMapIso f i i₁ i₂).hom ≫ pullback.snd _ _ =
      pullback.snd _ _ ≫ pullback.snd _ _ := by
  delta pullbackDiagonalMapIso
  simp only [limit.lift_π, PullbackCone.mk_π_app]

set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
/--
theorem `pullbackDiagonalMapIso.inv_fst` / 定理 `pullbackDiagonalMapIso.inv_fst`

English:
theorem pullbackDiagonalMapIso.inv_fst
  proof: by
  delta pullbackDiagonalMapIso
  simp only [limit.lift_π, PullbackCone.mk_π_app]

中文:
定理 pullbackDiagonalMapIso.inv_fst
  证明: by
  delta pullbackDiagonalMapIso
  simp only [limit.lift_π, PullbackCone.mk_π_app]

Depends on / 依赖: PullbackCone, PullbackCone.mk_, limit.lift_, pullbackDiagonalMapIso
-/
theorem pullbackDiagonalMapIso.inv_fst :
    (pullbackDiagonalMapIso f i i₁ i₂).inv ≫ pullback.fst _ _ =
      pullback.fst _ _ ≫ i₁ ≫ pullback.fst _ _ := by
  delta pullbackDiagonalMapIso
  simp only [limit.lift_π, PullbackCone.mk_π_app]

set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
/--
theorem `pullbackDiagonalMapIso.inv_snd_fst` / 定理 `pullbackDiagonalMapIso.inv_snd_fst`

English:
theorem pullbackDiagonalMapIso.inv_snd_fst
  proof: by
  delta pullbackDiagonalMapIso
  simp

中文:
定理 pullbackDiagonalMapIso.inv_snd_fst
  证明: by
  delta pullbackDiagonalMapIso
  simp

Depends on / 依赖: pullbackDiagonalMapIso
-/
theorem pullbackDiagonalMapIso.inv_snd_fst :
    (pullbackDiagonalMapIso f i i₁ i₂).inv ≫ pullback.snd _ _ ≫ pullback.fst _ _ =
      pullback.fst _ _ := by
  delta pullbackDiagonalMapIso
  simp

set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
/--
theorem `pullbackDiagonalMapIso.inv_snd_snd` / 定理 `pullbackDiagonalMapIso.inv_snd_snd`

English:
theorem pullbackDiagonalMapIso.inv_snd_snd
  proof: by
  delta pullbackDiagonalMapIso
  simp

中文:
定理 pullbackDiagonalMapIso.inv_snd_snd
  证明: by
  delta pullbackDiagonalMapIso
  simp

Depends on / 依赖: pullbackDiagonalMapIso
-/
theorem pullbackDiagonalMapIso.inv_snd_snd :
    (pullbackDiagonalMapIso f i i₁ i₂).inv ≫ pullback.snd _ _ ≫ pullback.snd _ _ =
      pullback.snd _ _ := by
  delta pullbackDiagonalMapIso
  simp

set_option backward.isDefEq.respectTransparency false in
/--
theorem `pullback_fst_map_snd_isPullback` / 定理 `pullback_fst_map_snd_isPullback`

English:
theorem pullback_fst_map_snd_isPullback
  proof: IsPullback.of_iso_pullback ⟨by ext <;> simp [condition_assoc]⟩
    (pullbackDiagonalMapIso f i i₁ i₂).symm (pullbackDiagonalMapIso.inv_fst f i i₁ i₂)
    (by cat_disch)

中文:
定理 pullback_fst_map_snd_isPullback
  证明: IsPullback.of_iso_pullback ⟨by ext <;> simp [condition_assoc]⟩
    (pullbackDiagonalMapIso f i i₁ i₂).symm (pullbackDiagonalMapIso.inv_fst f i i₁ i₂)
    (by cat_disch)

Depends on / 依赖: IsPullback, IsPullback.of_iso_pullback, cat_disch, condition_assoc, inv_fst, of_iso_pullback, pullbackDiagonalMapIso, pullbackDiagonalMapIso.inv_fst
-/
theorem pullback_fst_map_snd_isPullback :
    IsPullback (fst _ _ ≫ i₁ ≫ fst _ _)
      (map i₁ i₂ (i₁ ≫ snd _ _) (i₂ ≫ snd _ _) _ _ _
        (Category.id_comp _).symm (Category.id_comp _).symm)
      (diagonal f)
      (map (i₁ ≫ snd _ _) (i₂ ≫ snd _ _) f f (i₁ ≫ fst _ _) (i₂ ≫ fst _ _) i (by simp [condition])
        (by simp [condition])) :=
  IsPullback.of_iso_pullback ⟨by ext <;> simp [condition_assoc]⟩
    (pullbackDiagonalMapIso f i i₁ i₂).symm (pullbackDiagonalMapIso.inv_fst f i i₁ i₂)
    (by cat_disch)

end

section

variable {S T : C} (f : X ⟶ T) (g : Y ⟶ T) (i : T ⟶ S)
variable [HasPullback i i] [HasPullback f g] [HasPullback (f ≫ i) (g ≫ i)]
variable
  [HasPullback (diagonal i)
      (pullback.map (f ≫ i) (g ≫ i) i i f g (𝟙 _) (Category.comp_id _) (Category.comp_id _))]

set_option backward.isDefEq.respectTransparency false in
/--
Definition of `pullbackDiagonalMapIdIso` / `pullbackDiagonalMapIdIso` 的定义

English:
definition pullbackDiagonalMapIdIso
  signature: :
  body: by
  refine ?_ ≪≫
    pullbackDiagonalMapIso i (𝟙 _) (f ≫ inv (pullback.fst _ _)) (g ≫ inv (pullback.fst _ _)) ≪≫ ?_
  · refine @asIso _ _ _ _ (pullback.map _ _ _ _ (𝟙 T) ((pullback.congrHom ?_ ?_).hom) (𝟙 _) ?_ ?_)
      ?_
    · rw [← Category.comp_id (pullback.snd ..), ← condition, Category.assoc

中文:
定义 pullbackDiagonalMapIdIso
  签名: :
  定义体: by
  refine ?_ ≪≫
    pullbackDiagonalMapIso i (𝟙 _) (f ≫ inv (pullback.fst _ _)) (g ≫ inv (pullback.fst _ _)) ≪≫ ?_
  · refine @asIso _ _ _ _ (pullback.map _ _ _ _ (𝟙 T) ((pullback.congrHom ?_ ?_).hom) (𝟙 _) ?_ ?_)
      ?_
    · rw [← Category.comp_id (pullback.snd ..), ← condition, Category.assoc

Depends on / 依赖: Category, Category.assoc, Category.comp_id, Category.id_comp, IsIso.inv_hom_id_assoc, comp_id, condition, congrHom, id_comp, infer_instance, inv_hom_id_assoc, pullback, pullback.congrHom, pullback.fst, pullback.map, pullback.snd, pullbackDiagonalMapIso
-/
def pullbackDiagonalMapIdIso :
    pullback (diagonal i)
        (pullback.map (f ≫ i) (g ≫ i) i i f g (𝟙 _) (Category.comp_id _) (Category.comp_id _)) ≅
      pullback f g := by
  refine ?_ ≪≫
    pullbackDiagonalMapIso i (𝟙 _) (f ≫ inv (pullback.fst _ _)) (g ≫ inv (pullback.fst _ _)) ≪≫ ?_
  · refine @asIso _ _ _ _ (pullback.map _ _ _ _ (𝟙 T) ((pullback.congrHom ?_ ?_).hom) (𝟙 _) ?_ ?_)
      ?_
    · rw [← Category.comp_id (pullback.snd ..), ← condition, Category.assoc, IsIso.inv_hom_id_assoc]
    · rw [← Category.comp_id (pullback.snd ..), ← condition, Category.assoc, IsIso.inv_hom_id_assoc]
    · rw [Category.comp_id, Category.id_comp]
    · ext <;> simp
    · infer_instance
  · refine @asIso _ _ _ _ (pullback.map _ _ _ _ (𝟙 _) (𝟙 _) (pullback.fst _ _) ?_ ?_) ?_
    · rw [Category.assoc, IsIso.inv_hom_id, Category.comp_id, Category.id_comp]
    · rw [Category.assoc, IsIso.inv_hom_id, Category.comp_id, Category.id_comp]
    · infer_instance

set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
/--
theorem `pullbackDiagonalMapIdIso_hom_fst` / 定理 `pullbackDiagonalMapIdIso_hom_fst`

English:
theorem pullbackDiagonalMapIdIso_hom_fst
  proof: by
  delta pullbackDiagonalMapIdIso
  simp

中文:
定理 pullbackDiagonalMapIdIso_hom_fst
  证明: by
  delta pullbackDiagonalMapIdIso
  simp

Depends on / 依赖: pullbackDiagonalMapIdIso
-/
theorem pullbackDiagonalMapIdIso_hom_fst :
    (pullbackDiagonalMapIdIso f g i).hom ≫ pullback.fst _ _ =
      pullback.snd _ _ ≫ pullback.fst _ _ := by
  delta pullbackDiagonalMapIdIso
  simp

set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
/--
theorem `pullbackDiagonalMapIdIso_hom_snd` / 定理 `pullbackDiagonalMapIdIso_hom_snd`

English:
theorem pullbackDiagonalMapIdIso_hom_snd
  proof: by
  delta pullbackDiagonalMapIdIso
  simp

中文:
定理 pullbackDiagonalMapIdIso_hom_snd
  证明: by
  delta pullbackDiagonalMapIdIso
  simp

Depends on / 依赖: pullbackDiagonalMapIdIso
-/
theorem pullbackDiagonalMapIdIso_hom_snd :
    (pullbackDiagonalMapIdIso f g i).hom ≫ pullback.snd _ _ =
      pullback.snd _ _ ≫ pullback.snd _ _ := by
  delta pullbackDiagonalMapIdIso
  simp

set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
/--
theorem `pullbackDiagonalMapIdIso_inv_fst` / 定理 `pullbackDiagonalMapIdIso_inv_fst`

English:
theorem pullbackDiagonalMapIdIso_inv_fst
  proof: by
  rw [Iso.inv_comp_eq]; rw [← Category.comp_id (pullback.fst _ _)]; rw [← diagonal_fst i]; rw [pullback.condition_assoc]
  simp

@[reassoc (attr := simp)]

中文:
定理 pullbackDiagonalMapIdIso_inv_fst
  证明: by
  rw [Iso.inv_comp_eq]; rw [← Category.comp_id (pullback.fst _ _)]; rw [← diagonal_fst i]; rw [pullback.condition_assoc]
  simp

@[reassoc (attr := simp)]

Depends on / 依赖: Category, Category.comp_id, Iso.inv_comp_eq, comp_id, condition_assoc, diagonal_fst, inv_comp_eq, pullback, pullback.condition_assoc, pullback.fst
-/
theorem pullbackDiagonalMapIdIso_inv_fst :
    (pullbackDiagonalMapIdIso f g i).inv ≫ pullback.fst _ _ = pullback.fst _ _ ≫ f := by
  rw [Iso.inv_comp_eq]; rw [← Category.comp_id (pullback.fst _ _)]; rw [← diagonal_fst i]; rw [pullback.condition_assoc]
  simp

@[reassoc (attr := simp)]
/--
theorem `pullbackDiagonalMapIdIso_inv_snd_fst` / 定理 `pullbackDiagonalMapIdIso_inv_snd_fst`

English:
theorem pullbackDiagonalMapIdIso_inv_snd_fst
  proof: by
  rw [Iso.inv_comp_eq]
  simp

@[reassoc (attr := simp)]

中文:
定理 pullbackDiagonalMapIdIso_inv_snd_fst
  证明: by
  rw [Iso.inv_comp_eq]
  simp

@[reassoc (attr := simp)]

Depends on / 依赖: Iso.inv_comp_eq, inv_comp_eq
-/
theorem pullbackDiagonalMapIdIso_inv_snd_fst :
    (pullbackDiagonalMapIdIso f g i).inv ≫ pullback.snd _ _ ≫ pullback.fst _ _ =
      pullback.fst _ _ := by
  rw [Iso.inv_comp_eq]
  simp

@[reassoc (attr := simp)]
/--
theorem `pullbackDiagonalMapIdIso_inv_snd_snd` / 定理 `pullbackDiagonalMapIdIso_inv_snd_snd`

English:
theorem pullbackDiagonalMapIdIso_inv_snd_snd
  proof: by
  rw [Iso.inv_comp_eq]
  simp

中文:
定理 pullbackDiagonalMapIdIso_inv_snd_snd
  证明: by
  rw [Iso.inv_comp_eq]
  simp

Depends on / 依赖: Iso.inv_comp_eq, inv_comp_eq
-/
theorem pullbackDiagonalMapIdIso_inv_snd_snd :
    (pullbackDiagonalMapIdIso f g i).inv ≫ pullback.snd _ _ ≫ pullback.snd _ _ =
      pullback.snd _ _ := by
  rw [Iso.inv_comp_eq]
  simp

/--
theorem `pullback.diagonal_comp` / 定理 `pullback.diagonal_comp`

English:
theorem pullback.diagonal_comp
  given: (f : X ⟶ Y) (g : Y ⟶ Z)
  proof: by
  ext <;> simp

中文:
定理 pullback.diagonal_comp
  条件: (f : X ⟶ Y) (g : Y ⟶ Z)
  证明: by
  ext <;> simp
-/
theorem pullback.diagonal_comp (f : X ⟶ Y) (g : Y ⟶ Z) :
    diagonal (f ≫ g) = diagonal f ≫ (pullbackDiagonalMapIdIso f f g).inv ≫ pullback.snd _ _ := by
  ext <;> simp

set_option backward.isDefEq.respectTransparency false in
@[reassoc]
/--
lemma `pullback.comp_diagonal` / 引理 `pullback.comp_diagonal`

English:
lemma pullback.comp_diagonal
  given: (f : X ⟶ Y) (g : Y ⟶ Z)
  proof: by
  ext <;> simp

中文:
引理 pullback.comp_diagonal
  条件: (f : X ⟶ Y) (g : Y ⟶ Z)
  证明: by
  ext <;> simp
-/
lemma pullback.comp_diagonal (f : X ⟶ Y) (g : Y ⟶ Z) :
    f ≫ pullback.diagonal g = pullback.diagonal (f ≫ g) ≫
      pullback.map (f ≫ g) (f ≫ g) g g f f (𝟙 Z) (by simp) (by simp) := by
  ext <;> simp

set_option backward.isDefEq.respectTransparency false in
/--
theorem `pullback_map_diagonal_isPullback` / 定理 `pullback_map_diagonal_isPullback`

English:
theorem pullback_map_diagonal_isPullback
  proof: by
  apply IsPullback.of_iso_pullback _ (pullbackDiagonalMapIdIso f g i).symm
  · simp
  · ext <;> simp
  · constructor
    ext <;> simp [condition]

中文:
定理 pullback_map_diagonal_isPullback
  证明: by
  apply IsPullback.of_iso_pullback _ (pullbackDiagonalMapIdIso f g i).symm
  · simp
  · ext <;> simp
  · constructor
    ext <;> simp [condition]

Depends on / 依赖: IsPullback, IsPullback.of_iso_pullback, condition, of_iso_pullback, pullbackDiagonalMapIdIso
-/
theorem pullback_map_diagonal_isPullback :
    IsPullback (pullback.fst _ _ ≫ f)
      (pullback.map f g (f ≫ i) (g ≫ i) _ _ i (Category.id_comp _).symm (Category.id_comp _).symm)
      (diagonal i)
      (pullback.map (f ≫ i) (g ≫ i) i i f g (𝟙 _) (Category.comp_id _) (Category.comp_id _)) := by
  apply IsPullback.of_iso_pullback _ (pullbackDiagonalMapIdIso f g i).symm
  · simp
  · ext <;> simp
  · constructor
    ext <;> simp [condition]

/--
Definition of `diagonalObjPullbackFstIso` / `diagonalObjPullbackFstIso` 的定义

English:
definition diagonalObjPullbackFstIso
  signature: {X Y Z : C} (f : X ⟶ Z) (g : Y ⟶ Z)
  body: pullbackRightPullbackFstIso _ _ _ ≪≫
    pullback.congrHom pullback.condition rfl ≪≫
      pullbackAssoc _ _ _ _ ≪≫ pullbackSymmetry _ _ ≪≫ pullback.congrHom pullback.condition rfl

中文:
定义 diagonalObjPullbackFstIso
  签名: {X Y Z : C} (f : X ⟶ Z) (g : Y ⟶ Z)
  定义体: pullbackRightPullbackFstIso _ _ _ ≪≫
    pullback.congrHom pullback.condition rfl ≪≫
      pullbackAssoc _ _ _ _ ≪≫ pullbackSymmetry _ _ ≪≫ pullback.congrHom pullback.condition rfl

Depends on / 依赖: condition, congrHom, pullback, pullback.condition, pullback.congrHom, pullbackAssoc, pullbackRightPullbackFstIso, pullbackSymmetry
-/
def diagonalObjPullbackFstIso {X Y Z : C} (f : X ⟶ Z) (g : Y ⟶ Z) :
    diagonalObj (pullback.fst f g) ≅
      pullback (pullback.snd _ _ ≫ g : diagonalObj g ⟶ Z) f :=
  pullbackRightPullbackFstIso _ _ _ ≪≫
    pullback.congrHom pullback.condition rfl ≪≫
      pullbackAssoc _ _ _ _ ≪≫ pullbackSymmetry _ _ ≪≫ pullback.congrHom pullback.condition rfl

set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
/--
theorem `diagonalObjPullbackFstIso_hom_fst_fst` / 定理 `diagonalObjPullbackFstIso_hom_fst_fst`

English:
theorem diagonalObjPullbackFstIso_hom_fst_fst
  given: {X Y Z : C} (f : X ⟶ Z) (g : Y ⟶ Z)
  proof: by
  delta diagonalObjPullbackFstIso
  simp

中文:
定理 diagonalObjPullbackFstIso_hom_fst_fst
  条件: {X Y Z : C} (f : X ⟶ Z) (g : Y ⟶ Z)
  证明: by
  delta diagonalObjPullbackFstIso
  simp

Depends on / 依赖: diagonalObjPullbackFstIso
-/
theorem diagonalObjPullbackFstIso_hom_fst_fst {X Y Z : C} (f : X ⟶ Z) (g : Y ⟶ Z) :
    (diagonalObjPullbackFstIso f g).hom ≫ pullback.fst _ _ ≫ pullback.fst _ _ =
      pullback.fst _ _ ≫ pullback.snd _ _ := by
  delta diagonalObjPullbackFstIso
  simp

set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
/--
theorem `diagonalObjPullbackFstIso_hom_fst_snd` / 定理 `diagonalObjPullbackFstIso_hom_fst_snd`

English:
theorem diagonalObjPullbackFstIso_hom_fst_snd
  given: {X Y Z : C} (f : X ⟶ Z) (g : Y ⟶ Z)
  proof: by
  delta diagonalObjPullbackFstIso
  simp

中文:
定理 diagonalObjPullbackFstIso_hom_fst_snd
  条件: {X Y Z : C} (f : X ⟶ Z) (g : Y ⟶ Z)
  证明: by
  delta diagonalObjPullbackFstIso
  simp

Depends on / 依赖: diagonalObjPullbackFstIso
-/
theorem diagonalObjPullbackFstIso_hom_fst_snd {X Y Z : C} (f : X ⟶ Z) (g : Y ⟶ Z) :
    (diagonalObjPullbackFstIso f g).hom ≫ pullback.fst _ _ ≫ pullback.snd _ _ =
      pullback.snd _ _ ≫ pullback.snd _ _ := by
  delta diagonalObjPullbackFstIso
  simp

set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
/--
theorem `diagonalObjPullbackFstIso_hom_snd` / 定理 `diagonalObjPullbackFstIso_hom_snd`

English:
theorem diagonalObjPullbackFstIso_hom_snd
  given: {X Y Z : C} (f : X ⟶ Z) (g : Y ⟶ Z)
  proof: by
  delta diagonalObjPullbackFstIso
  simp

中文:
定理 diagonalObjPullbackFstIso_hom_snd
  条件: {X Y Z : C} (f : X ⟶ Z) (g : Y ⟶ Z)
  证明: by
  delta diagonalObjPullbackFstIso
  simp

Depends on / 依赖: diagonalObjPullbackFstIso
-/
theorem diagonalObjPullbackFstIso_hom_snd {X Y Z : C} (f : X ⟶ Z) (g : Y ⟶ Z) :
    (diagonalObjPullbackFstIso f g).hom ≫ pullback.snd _ _ =
      pullback.fst _ _ ≫ pullback.fst _ _ := by
  delta diagonalObjPullbackFstIso
  simp

set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
/--
theorem `diagonalObjPullbackFstIso_inv_fst_fst` / 定理 `diagonalObjPullbackFstIso_inv_fst_fst`

English:
theorem diagonalObjPullbackFstIso_inv_fst_fst
  given: {X Y Z : C} (f : X ⟶ Z) (g : Y ⟶ Z)
  proof: by
  delta diagonalObjPullbackFstIso
  simp

中文:
定理 diagonalObjPullbackFstIso_inv_fst_fst
  条件: {X Y Z : C} (f : X ⟶ Z) (g : Y ⟶ Z)
  证明: by
  delta diagonalObjPullbackFstIso
  simp

Depends on / 依赖: diagonalObjPullbackFstIso
-/
theorem diagonalObjPullbackFstIso_inv_fst_fst {X Y Z : C} (f : X ⟶ Z) (g : Y ⟶ Z) :
    (diagonalObjPullbackFstIso f g).inv ≫ pullback.fst _ _ ≫ pullback.fst _ _ =
      pullback.snd _ _ := by
  delta diagonalObjPullbackFstIso
  simp

set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
/--
theorem `diagonalObjPullbackFstIso_inv_fst_snd` / 定理 `diagonalObjPullbackFstIso_inv_fst_snd`

English:
theorem diagonalObjPullbackFstIso_inv_fst_snd
  given: {X Y Z : C} (f : X ⟶ Z) (g : Y ⟶ Z)
  proof: by
  delta diagonalObjPullbackFstIso
  simp

中文:
定理 diagonalObjPullbackFstIso_inv_fst_snd
  条件: {X Y Z : C} (f : X ⟶ Z) (g : Y ⟶ Z)
  证明: by
  delta diagonalObjPullbackFstIso
  simp

Depends on / 依赖: diagonalObjPullbackFstIso
-/
theorem diagonalObjPullbackFstIso_inv_fst_snd {X Y Z : C} (f : X ⟶ Z) (g : Y ⟶ Z) :
    (diagonalObjPullbackFstIso f g).inv ≫ pullback.fst _ _ ≫ pullback.snd _ _ =
      pullback.fst _ _ ≫ pullback.fst _ _ := by
  delta diagonalObjPullbackFstIso
  simp

set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
/--
theorem `diagonalObjPullbackFstIso_inv_snd_fst` / 定理 `diagonalObjPullbackFstIso_inv_snd_fst`

English:
theorem diagonalObjPullbackFstIso_inv_snd_fst
  given: {X Y Z : C} (f : X ⟶ Z) (g : Y ⟶ Z)
  proof: by
  delta diagonalObjPullbackFstIso
  simp

中文:
定理 diagonalObjPullbackFstIso_inv_snd_fst
  条件: {X Y Z : C} (f : X ⟶ Z) (g : Y ⟶ Z)
  证明: by
  delta diagonalObjPullbackFstIso
  simp

Depends on / 依赖: diagonalObjPullbackFstIso
-/
theorem diagonalObjPullbackFstIso_inv_snd_fst {X Y Z : C} (f : X ⟶ Z) (g : Y ⟶ Z) :
    (diagonalObjPullbackFstIso f g).inv ≫ pullback.snd _ _ ≫ pullback.fst _ _ =
      pullback.snd _ _ := by
  delta diagonalObjPullbackFstIso
  simp

set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
/--
theorem `diagonalObjPullbackFstIso_inv_snd_snd` / 定理 `diagonalObjPullbackFstIso_inv_snd_snd`

English:
theorem diagonalObjPullbackFstIso_inv_snd_snd
  given: {X Y Z : C} (f : X ⟶ Z) (g : Y ⟶ Z)
  proof: by
  delta diagonalObjPullbackFstIso
  simp

中文:
定理 diagonalObjPullbackFstIso_inv_snd_snd
  条件: {X Y Z : C} (f : X ⟶ Z) (g : Y ⟶ Z)
  证明: by
  delta diagonalObjPullbackFstIso
  simp

Depends on / 依赖: diagonalObjPullbackFstIso
-/
theorem diagonalObjPullbackFstIso_inv_snd_snd {X Y Z : C} (f : X ⟶ Z) (g : Y ⟶ Z) :
    (diagonalObjPullbackFstIso f g).inv ≫ pullback.snd _ _ ≫ pullback.snd _ _ =
      pullback.fst _ _ ≫ pullback.snd _ _ := by
  delta diagonalObjPullbackFstIso
  simp

set_option backward.isDefEq.respectTransparency false in
/--
theorem `diagonal_pullback_fst` / 定理 `diagonal_pullback_fst`

English:
theorem diagonal_pullback_fst
  given: {X Y Z : C} (f : X ⟶ Z) (g : Y ⟶ Z)
  proof: by
  ext <;> simp

中文:
定理 diagonal_pullback_fst
  条件: {X Y Z : C} (f : X ⟶ Z) (g : Y ⟶ Z)
  证明: by
  ext <;> simp
-/
theorem diagonal_pullback_fst {X Y Z : C} (f : X ⟶ Z) (g : Y ⟶ Z) :
    diagonal (pullback.fst f g) =
      (pullbackSymmetry _ _).hom ≫
        ((Over.pullback f).map
              (Over.homMk (diagonal g) : Over.mk g ⟶ Over.mk (pullback.snd _ _ ≫ g))).left ≫
          (diagonalObjPullbackFstIso f g).inv := by
  ext <;> simp

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/--
lemma `pullback_lift_diagonal_isPullback` / 引理 `pullback_lift_diagonal_isPullback`

English:
lemma pullback_lift_diagonal_isPullback
  given: (g : Y ⟶ X) (f : X ⟶ S)
  proof: by
  let i : pullback (g ≫ f) f ≅ pullback (g ≫ f) (𝟙 X ≫ f) := congrHom rfl (by simp)
  let e : pullback (diagonal f) (map (g ≫ f) f f f g (𝟙 X) (𝟙 S) (by simp) (by simp)) ≅
      pullback (diagonal f) (map (g ≫ f) (𝟙 X ≫ f) f f g (𝟙 X) (𝟙 S) (by simp) (by simp)) :=
    (asIso (map _ _ _ _ (𝟙 _) i.

中文:
引理 pullback_lift_diagonal_isPullback
  条件: (g : Y ⟶ X) (f : X ⟶ S)
  证明: by
  let i : pullback (g ≫ f) f ≅ pullback (g ≫ f) (𝟙 X ≫ f) := congrHom rfl (by simp)
  let e : pullback (diagonal f) (map (g ≫ f) f f f g (𝟙 X) (𝟙 S) (by simp) (by simp)) ≅
      pullback (diagonal f) (map (g ≫ f) (𝟙 X ≫ f) f f g (𝟙 X) (𝟙 S) (by simp) (by simp)) :=
    (asIso (map _ _ _ _ (𝟙 _) i.

Depends on / 依赖: IsPullback, IsPullback.of_iso_pullback, congrHom, diagonal, i.inv, of_iso_pullback, pullback, pullback.fst, pullbackDiagonalMapIdIso
-/
lemma pullback_lift_diagonal_isPullback (g : Y ⟶ X) (f : X ⟶ S) :
    IsPullback g (pullback.lift (𝟙 Y) g (by simp)) (diagonal f)
      (pullback.map (g ≫ f) f f f g (𝟙 X) (𝟙 S) (by simp) (by simp)) := by
  let i : pullback (g ≫ f) f ≅ pullback (g ≫ f) (𝟙 X ≫ f) := congrHom rfl (by simp)
  let e : pullback (diagonal f) (map (g ≫ f) f f f g (𝟙 X) (𝟙 S) (by simp) (by simp)) ≅
      pullback (diagonal f) (map (g ≫ f) (𝟙 X ≫ f) f f g (𝟙 X) (𝟙 S) (by simp) (by simp)) :=
    (asIso (map _ _ _ _ (𝟙 _) i.inv (𝟙 _) (by simp) (by ext <;> simp [i]))).symm
  apply IsPullback.of_iso_pullback _
      (e ≪≫ pullbackDiagonalMapIdIso (T := X) (S := S) g (𝟙 X) f ≪≫ asIso (pullback.fst _ _)).symm
  · simp [e]
  · ext <;> simp [e, i]
  · constructor
    ext <;> simp

end

set_option backward.isDefEq.respectTransparency false in
/-- Given the following diagram with `S ⟶ S'` a monomorphism,

```
    X ⟶ X'
      ↘ ↘
        S ⟶ S'
      ↗ ↗
    Y ⟶ Y'
```

This iso witnesses the fact that

```
      X ×[S] Y ⟶ (X' ×[S'] Y') ×[Y'] Y
          | |
          | |
          ↓ ↓
(X' ×[S'] Y') ×[X'] X ⟶ X' ×[S'] Y'
```

is a pullback square. The diagonal map of this square is `pullback.map`.
Also see `pullback_lift_map_is_pullback`.
-/
@[simps]
/--
Definition of `pullbackFstFstIso` / `pullbackFstFstIso` 的定义

English:
definition pullbackFstFstIso
  signature: {X Y S X' Y' S' : C} (f : X ⟶ S) (g : Y ⟶ S) (f' : X' ⟶ S') (g' : Y' ⟶ S')
  body: pullback.lift (pullback.fst _ _ ≫ pullback.snd _ _) (pullback.snd _ _ ≫ pullback.snd _ _)
      (by
        rw [← cancel_mono i₃]; rw [Category.assoc]; rw [Category.assoc]; rw [Category.assoc]; rw [Category.assoc]; rw [e₁]; rw [e₂]; rw [← pullback.condition_assoc]; rw [pullback.condition_assoc]; rw 

中文:
定义 pullbackFstFstIso
  签名: {X Y S X' Y' S' : C} (f : X ⟶ S) (g : Y ⟶ S) (f' : X' ⟶ S') (g' : Y' ⟶ S')
  定义体: pullback.lift (pullback.fst _ _ ≫ pullback.snd _ _) (pullback.snd _ _ ≫ pullback.snd _ _)
      (by
        rw [← cancel_mono i₃]; rw [Category.assoc]; rw [Category.assoc]; rw [Category.assoc]; rw [Category.assoc]; rw [e₁]; rw [e₂]; rw [← pullback.condition_assoc]; rw [pullback.condition_assoc]; rw 

Depends on / 依赖: Category, Category.assoc, cancel_mono, condition, condition_assoc, lift_fst, pullback, pullback.condition, pullback.condition_assoc, pullback.fst, pullback.lift, pullback.lift_fst, pullback.map, pullback.snd
-/
def pullbackFstFstIso {X Y S X' Y' S' : C} (f : X ⟶ S) (g : Y ⟶ S) (f' : X' ⟶ S') (g' : Y' ⟶ S')
    (i₁ : X ⟶ X') (i₂ : Y ⟶ Y') (i₃ : S ⟶ S') (e₁ : f ≫ i₃ = i₁ ≫ f') (e₂ : g ≫ i₃ = i₂ ≫ g')
    [Mono i₃] :
    pullback (pullback.fst _ _ : pullback (pullback.fst _ _ : pullback f' g' ⟶ _) i₁ ⟶ _)
        (pullback.fst _ _ : pullback (pullback.snd _ _ : pullback f' g' ⟶ _) i₂ ⟶ _) ≅
      pullback f g where
  hom :=
    pullback.lift (pullback.fst _ _ ≫ pullback.snd _ _) (pullback.snd _ _ ≫ pullback.snd _ _)
      (by
        rw [← cancel_mono i₃]; rw [Category.assoc]; rw [Category.assoc]; rw [Category.assoc]; rw [Category.assoc]; rw [e₁]; rw [e₂]; rw [← pullback.condition_assoc]; rw [pullback.condition_assoc]; rw [pullback.condition]; rw [pullback.condition_assoc])
  inv :=
    pullback.lift
      (pullback.lift (pullback.map _ _ _ _ _ _ _ e₁ e₂) (pullback.fst _ _) (pullback.lift_fst ..))
      (pullback.lift (pullback.map _ _ _ _ _ _ _ e₁ e₂) (pullback.snd _ _) (pullback.lift_snd ..))
      (by rw [pullback.lift_fst, pullback.lift_fst])
  hom_inv_id := by
    -- We could use `ext` here to immediately descend to the leaf goals,
    -- but it only obscures the structure.
    apply pullback.hom_ext
    · apply pullback.hom_ext
      · apply pullback.hom_ext
        · simp only [Category.assoc, lift_fst, lift_fst_assoc, Category.id_comp]
          rw [condition]
        · simp [Category.assoc, condition]
      · simp only [Category.assoc, lift_snd, lift_fst, Category.id_comp]
    · apply pullback.hom_ext
      · apply pullback.hom_ext
        · simp only [Category.assoc, lift_snd_assoc, lift_fst_assoc, lift_fst, Category.id_comp]
          rw [← condition_assoc]; rw [condition]
        · simp only [Category.assoc, lift_snd, lift_fst_assoc, lift_snd_assoc, Category.id_comp]
          rw [condition]
      · simp only [Category.assoc, lift_snd, Category.id_comp]
  inv_hom_id := by
    apply pullback.hom_ext
    · simp only [Category.assoc, lift_fst, lift_fst_assoc, lift_snd, Category.id_comp]
    · simp only [Category.assoc, lift_snd, lift_snd_assoc, Category.id_comp]

/--
theorem `pullback_map_eq_pullbackFstFstIso_inv` / 定理 `pullback_map_eq_pullbackFstFstIso_inv`

English:
theorem pullback_map_eq_pullbackFstFstIso_inv
  statement: {X Y S X' Y' S' : C} (f : X ⟶ S) (g : Y ⟶ S)
  proof: by
  simp only [pullbackFstFstIso_inv, lift_snd_assoc, lift_fst]

中文:
定理 pullback_map_eq_pullbackFstFstIso_inv
  结论: {X Y S X' Y' S' : C} (f : X ⟶ S) (g : Y ⟶ S)
  证明: by
  simp only [pullbackFstFstIso_inv, lift_snd_assoc, lift_fst]

Depends on / 依赖: lift_fst, lift_snd_assoc, pullbackFstFstIso_inv
-/
theorem pullback_map_eq_pullbackFstFstIso_inv {X Y S X' Y' S' : C} (f : X ⟶ S) (g : Y ⟶ S)
    (f' : X' ⟶ S') (g' : Y' ⟶ S') (i₁ : X ⟶ X') (i₂ : Y ⟶ Y') (i₃ : S ⟶ S')
    (e₁ : f ≫ i₃ = i₁ ≫ f') (e₂ : g ≫ i₃ = i₂ ≫ g') [Mono i₃] :
    pullback.map f g f' g' i₁ i₂ i₃ e₁ e₂ =
      (pullbackFstFstIso f g f' g' i₁ i₂ i₃ e₁ e₂).inv ≫ pullback.snd _ _ ≫ pullback.fst _ _ := by
  simp only [pullbackFstFstIso_inv, lift_snd_assoc, lift_fst]

set_option backward.isDefEq.respectTransparency false in
/--
theorem `pullback_lift_map_isPullback` / 定理 `pullback_lift_map_isPullback`

English:
theorem pullback_lift_map_isPullback
  statement: {X Y S X' Y' S' : C} (f : X ⟶ S) (g : Y ⟶ S) (f' : X' ⟶ S')
  proof: IsPullback.of_iso_pullback ⟨by rw [lift_fst, lift_fst]⟩
    (pullbackFstFstIso f g f' g' i₁ i₂ i₃ e₁ e₂).symm (by simp) (by simp)

中文:
定理 pullback_lift_map_isPullback
  结论: {X Y S X' Y' S' : C} (f : X ⟶ S) (g : Y ⟶ S) (f' : X' ⟶ S')
  证明: IsPullback.of_iso_pullback ⟨by rw [lift_fst, lift_fst]⟩
    (pullbackFstFstIso f g f' g' i₁ i₂ i₃ e₁ e₂).symm (by simp) (by simp)

Depends on / 依赖: IsPullback, IsPullback.of_iso_pullback, lift_fst, of_iso_pullback, pullbackFstFstIso
-/
theorem pullback_lift_map_isPullback {X Y S X' Y' S' : C} (f : X ⟶ S) (g : Y ⟶ S) (f' : X' ⟶ S')
    (g' : Y' ⟶ S') (i₁ : X ⟶ X') (i₂ : Y ⟶ Y') (i₃ : S ⟶ S') (e₁ : f ≫ i₃ = i₁ ≫ f')
    (e₂ : g ≫ i₃ = i₂ ≫ g') [Mono i₃] :
    IsPullback (pullback.lift (pullback.map f g f' g' i₁ i₂ i₃ e₁ e₂) (fst _ _) (lift_fst _ _ _))
      (pullback.lift (pullback.map f g f' g' i₁ i₂ i₃ e₁ e₂) (snd _ _) (lift_snd _ _ _))
      (pullback.fst _ _) (pullback.fst _ _) :=
  IsPullback.of_iso_pullback ⟨by rw [lift_fst, lift_fst]⟩
    (pullbackFstFstIso f g f' g' i₁ i₂ i₃ e₁ e₂).symm (by simp) (by simp)

set_option backward.isDefEq.respectTransparency false in
/--
lemma `isPullback_map_snd_snd` / 引理 `isPullback_map_snd_snd`

English:
lemma isPullback_map_snd_snd
  given: {X Y Z S : C} (f : X ⟶ S) (g : Y ⟶ S) (h : Z ⟶ S)
  proof: by
  refine ⟨⟨by simp⟩, ⟨PullbackCone.IsLimit.mk _ ?_ ?_ ?_ ?_⟩⟩
  · intro c
    refine pullback.lift c.snd
        (pullback.lift (c.snd ≫ pullback.fst _ _) (c.fst ≫ pullback.snd _ _) ?_) ?_
    · simp [pullback.condition, ← c.condition_assoc]
    · simp
  · intro c
    apply pullback.hom_ext <;> s

中文:
引理 isPullback_map_snd_snd
  条件: {X Y Z S : C} (f : X ⟶ S) (g : Y ⟶ S) (h : Z ⟶ S)
  证明: by
  refine ⟨⟨by simp⟩, ⟨PullbackCone.IsLimit.mk _ ?_ ?_ ?_ ?_⟩⟩
  · intro c
    refine pullback.lift c.snd
        (pullback.lift (c.snd ≫ pullback.fst _ _) (c.fst ≫ pullback.snd _ _) ?_) ?_
    · simp [pullback.condition, ← c.condition_assoc]
    · simp
  · intro c
    apply pullback.hom_ext <;> s

Depends on / 依赖: IsLimit, PullbackCone, PullbackCone.IsLimit.mk, c.condition, c.condition_assoc, c.fst, c.snd, condition, condition_assoc, hom_ext, pullback, pullback.condition, pullback.fst, pullback.hom_ext, pullback.lift, pullback.snd
-/
lemma isPullback_map_snd_snd {X Y Z S : C} (f : X ⟶ S) (g : Y ⟶ S) (h : Z ⟶ S) :
    IsPullback (pullback.map _ _ _ _ (pullback.snd f g) (pullback.snd f h) f
        pullback.condition pullback.condition)
      (pullback.fst (pullback.fst f g) (pullback.fst f h))
      (pullback.fst g h) (pullback.snd f g) := by
  refine ⟨⟨by simp⟩, ⟨PullbackCone.IsLimit.mk _ ?_ ?_ ?_ ?_⟩⟩
  · intro c
    refine pullback.lift c.snd
        (pullback.lift (c.snd ≫ pullback.fst _ _) (c.fst ≫ pullback.snd _ _) ?_) ?_
    · simp [pullback.condition, ← c.condition_assoc]
    · simp
  · intro c
    apply pullback.hom_ext <;> simp [c.condition]
  · intro c
    apply pullback.hom_ext <;> simp
  · intro c m hfst hsnd
    refine pullback.hom_ext (by simpa) ?_
    apply pullback.hom_ext <;> simp [← hsnd, pullback.condition, ← hfst]

end Diagonal

section Codiagonal

namespace pushout

variable {X Y : C} (f : X ⟶ Y) [HasPushout f f]

/--
Definition of `codiagonalObj` / `codiagonalObj` 的定义

English:
abbreviation codiagonalObj
  signature: (f : X ⟶ Y) [HasPushout f f]
  body: pushout f f

中文:
缩写 codiagonalObj
  签名: (f : X ⟶ Y) [HasPushout f f]
  定义体: pushout f f

Depends on / 依赖: pushout
-/
noncomputable abbrev codiagonalObj (f : X ⟶ Y) [HasPushout f f] : C :=
  pushout f f

/--
Definition of `codiagonal` / `codiagonal` 的定义

English:
definition codiagonal
  signature: (f : X ⟶ Y) [HasPushout f f]
  body: pushout.desc (𝟙 Y) (𝟙 Y) rfl

@[reassoc (attr := simp)]

中文:
定义 codiagonal
  签名: (f : X ⟶ Y) [HasPushout f f]
  定义体: pushout.desc (𝟙 Y) (𝟙 Y) rfl

@[reassoc (attr := simp)]

Depends on / 依赖: pushout, pushout.desc
-/
noncomputable def codiagonal (f : X ⟶ Y) [HasPushout f f] : codiagonalObj f ⟶ Y :=
  pushout.desc (𝟙 Y) (𝟙 Y) rfl

@[reassoc (attr := simp)]
/--
theorem `inl_codiagonal` / 定理 `inl_codiagonal`

English:
theorem inl_codiagonal
  statement: pushout.inl _ _ ≫ codiagonal f = 𝟙 _
  proof: pushout.inl_desc _ _ _

@[reassoc (attr := simp)]

中文:
定理 inl_codiagonal
  结论: pushout.inl _ _ ≫ codiagonal f = 𝟙 _
  证明: pushout.inl_desc _ _ _

@[reassoc (attr := simp)]

Depends on / 依赖: inl_desc, pushout, pushout.inl_desc
-/
theorem inl_codiagonal : pushout.inl _ _ ≫ codiagonal f = 𝟙 _ :=
  pushout.inl_desc _ _ _

@[reassoc (attr := simp)]
/--
theorem `inr_codiagonal` / 定理 `inr_codiagonal`

English:
theorem inr_codiagonal
  statement: pushout.inr _ _ ≫ codiagonal f = 𝟙 _
  proof: pushout.inr_desc _ _ _

中文:
定理 inr_codiagonal
  结论: pushout.inr _ _ ≫ codiagonal f = 𝟙 _
  证明: pushout.inr_desc _ _ _

Depends on / 依赖: inr_desc, pushout, pushout.inr_desc
-/
theorem inr_codiagonal : pushout.inr _ _ ≫ codiagonal f = 𝟙 _ :=
  pushout.inr_desc _ _ _

set_option backward.isDefEq.respectTransparency false in
/--
lemma `op_codiagonal` / 引理 `op_codiagonal`

English:
lemma op_codiagonal
  proof: by
  rw [← Iso.comp_inv_eq]
  ext <;> simp [← op_comp]

中文:
引理 op_codiagonal
  证明: by
  rw [← Iso.comp_inv_eq]
  ext <;> simp [← op_comp]

Depends on / 依赖: Iso.comp_inv_eq, comp_inv_eq, op_comp
-/
lemma op_codiagonal :
    (pushout.codiagonal f).op = pullback.diagonal f.op ≫ (pullbackIsoOpPushout _ _).hom := by
  rw [← Iso.comp_inv_eq]
  ext <;> simp [← op_comp]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: IsSplitEpi (codiagonal f)
  body: ⟨⟨⟨pushout.inl _ _, inl_codiagonal f⟩⟩⟩

中文:
实例 :
  签名: IsSplitEpi (codiagonal f)
  定义体: ⟨⟨⟨pushout.inl _ _, inl_codiagonal f⟩⟩⟩

Depends on / 依赖: inl_codiagonal, pushout, pushout.inl
-/
instance : IsSplitEpi (codiagonal f) :=
  ⟨⟨⟨pushout.inl _ _, inl_codiagonal f⟩⟩⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: IsSplitMono (pushout.inl f f)
  body: ⟨⟨⟨codiagonal f, inl_codiagonal f⟩⟩⟩

中文:
实例 :
  签名: IsSplitMono (pushout.inl f f)
  定义体: ⟨⟨⟨codiagonal f, inl_codiagonal f⟩⟩⟩

Depends on / 依赖: codiagonal, inl_codiagonal
-/
instance : IsSplitMono (pushout.inl f f) :=
  ⟨⟨⟨codiagonal f, inl_codiagonal f⟩⟩⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: IsSplitMono (pushout.inr f f)
  body: ⟨⟨⟨codiagonal f, inr_codiagonal f⟩⟩⟩

中文:
实例 :
  签名: IsSplitMono (pushout.inr f f)
  定义体: ⟨⟨⟨codiagonal f, inr_codiagonal f⟩⟩⟩

Depends on / 依赖: codiagonal, inr_codiagonal
-/
instance : IsSplitMono (pushout.inr f f) :=
  ⟨⟨⟨codiagonal f, inr_codiagonal f⟩⟩⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Epi
  signature: f] : IsIso (codiagonal f)
  body: by
  rw [(IsIso.inv_eq_of_hom_inv_id (inl_codiagonal f)).symm]
  infer_instance

中文:
实例 [Epi
  签名: f] : IsIso (codiagonal f)
  定义体: by
  rw [(IsIso.inv_eq_of_hom_inv_id (inl_codiagonal f)).symm]
  infer_instance

Depends on / 依赖: IsIso.inv_eq_of_hom_inv_id, infer_instance, inl_codiagonal, inv_eq_of_hom_inv_id
-/
instance [Epi f] : IsIso (codiagonal f) := by
  rw [(IsIso.inv_eq_of_hom_inv_id (inl_codiagonal f)).symm]
  infer_instance

/--
lemma `isIso_codiagonal_iff` / 引理 `isIso_codiagonal_iff`

English:
lemma isIso_codiagonal_iff
  statement: IsIso (codiagonal f) ↔ Epi f
  proof: ⟨fun H => ⟨fun _ _ e => by rw [← inl_desc _ _ e, (cancel_mono (g := inl f f) (h := inr f f)
    (codiagonal f)).mp (by simp), inr_desc]⟩, fun _ => inferInstance⟩

中文:
引理 isIso_codiagonal_iff
  结论: IsIso (codiagonal f) ↔ Epi f
  证明: ⟨fun H => ⟨fun _ _ e => by rw [← inl_desc _ _ e, (cancel_mono (g := inl f f) (h := inr f f)
    (codiagonal f)).mp (by simp), inr_desc]⟩, fun _ => inferInstance⟩

Depends on / 依赖: cancel_mono, codiagonal, inl_desc, inr_desc
-/
lemma isIso_codiagonal_iff : IsIso (codiagonal f) ↔ Epi f :=
  ⟨fun H => ⟨fun _ _ e => by rw [← inl_desc _ _ e, (cancel_mono (g := inl f f) (h := inr f f)
    (codiagonal f)).mp (by simp), inr_desc]⟩, fun _ => inferInstance⟩

end pushout

variable [HasPushouts C]

set_option backward.isDefEq.respectTransparency false in
/--
theorem `isPushout_map_codiagonal` / 定理 `isPushout_map_codiagonal`

English:
theorem isPushout_map_codiagonal
  given: {S T : C} (f : T ⟶ X) (g : T ⟶ Y) (i : S ⟶ T)
  proof: by
  rw [← IsPullback.op_iff]
  simp only [op_pushoutMap, Quiver.Hom.unop_op, op_comp, unop_comp, op_id, pushout.op_codiagonal]
  exact .of_iso (pullback_map_diagonal_isPullback f.op g.op i.op)
    (pullbackIsoOpPushout _ _) (.refl _) (pullbackIsoOpPushout _ _) (pullbackIsoOpPushout _ _)
    (by sim

中文:
定理 isPushout_map_codiagonal
  条件: {S T : C} (f : T ⟶ X) (g : T ⟶ Y) (i : S ⟶ T)
  证明: by
  rw [← IsPullback.op_iff]
  simp only [op_pushoutMap, Quiver.Hom.unop_op, op_comp, unop_comp, op_id, pushout.op_codiagonal]
  exact .of_iso (pullback_map_diagonal_isPullback f.op g.op i.op)
    (pullbackIsoOpPushout _ _) (.refl _) (pullbackIsoOpPushout _ _) (pullbackIsoOpPushout _ _)
    (by sim

Depends on / 依赖: IsPullback, IsPullback.op_iff, Iso.inv_comp_eq, Quiver, Quiver.Hom.unop_op, f.op, g.op, i.op, inv_comp_eq, of_iso, op_codiagonal, op_comp, op_id, op_iff, op_pushoutMap, pullbackIsoOpPushout, pullback_map_diagonal_isPullback, pushout, pushout.op_codiagonal, unop_comp
-/
theorem isPushout_map_codiagonal {S T : C} (f : T ⟶ X) (g : T ⟶ Y) (i : S ⟶ T) :
    IsPushout
      (pushout.map i i (i ≫ f) (i ≫ g) f g (𝟙 _) (by simp) (by simp))
      (pushout.codiagonal i)
      (pushout.map (i ≫ f) (i ≫ g) f g (𝟙 _) (𝟙 _) i (by simp) (by simp))
      (f ≫ pushout.inl _ _) := by
  rw [← IsPullback.op_iff]
  simp only [op_pushoutMap, Quiver.Hom.unop_op, op_comp, unop_comp, op_id, pushout.op_codiagonal]
  exact .of_iso (pullback_map_diagonal_isPullback f.op g.op i.op)
    (pullbackIsoOpPushout _ _) (.refl _) (pullbackIsoOpPushout _ _) (pullbackIsoOpPushout _ _)
    (by simp [← Iso.inv_comp_eq]) (by simp) (by simp) (by simp)

end Codiagonal

end CategoryTheory.Limits
