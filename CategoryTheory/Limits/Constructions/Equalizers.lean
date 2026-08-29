/-
Copyright (c) 2020 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta, Andrew Yang
-/
module

public import Mathlib.CategoryTheory.Limits.Shapes.Equalizers
public import Mathlib.CategoryTheory.Limits.Shapes.BinaryProducts
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Pullbacks
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.BinaryProducts

/-!
# Constructing equalizers from pullbacks and binary products.

If a category has pullbacks and binary products, then it has equalizers.

TODO: generalize universe
-/

@[expose] public section


noncomputable section

universe v v' u u'

open CategoryTheory CategoryTheory.Category

namespace CategoryTheory.Limits

variable {C : Type u} [Category.{v} C]
variable {D : Type u'} [Category.{v'} D] (G : C ⥤ D)

-- We hide the "implementation details" inside a namespace
namespace HasEqualizersOfHasPullbacksAndBinaryProducts

variable [HasBinaryProducts C] [HasPullbacks C]

/--
Definition of `constructEqualizer` / `constructEqualizer` 的定义

English:
abbreviation constructEqualizer
  signature: (F : WalkingParallelPair ⥤ C)
  body: pullback (prod.lift (𝟙 _) (F.map WalkingParallelPairHom.left))
    (prod.lift (𝟙 _) (F.map WalkingParallelPairHom.right))

中文:
缩写 constructEqualizer
  签名: (F : WalkingParallelPair ⥤ C)
  定义体: pullback (prod.lift (𝟙 _) (F.map WalkingParallelPairHom.left))
    (prod.lift (𝟙 _) (F.map WalkingParallelPairHom.right))

Depends on / 依赖: F.map, WalkingParallelPairHom, WalkingParallelPairHom.left, WalkingParallelPairHom.right, hasPullback_of_comp_mono, prod.lift, pullback
-/
abbrev constructEqualizer (F : WalkingParallelPair ⥤ C) : C :=
  pullback (prod.lift (𝟙 _) (F.map WalkingParallelPairHom.left))
    (prod.lift (𝟙 _) (F.map WalkingParallelPairHom.right))

/--
Definition of `pullbackFst` / `pullbackFst` 的定义

English:
abbreviation pullbackFst
  signature: (F : WalkingParallelPair ⥤ C)
  body: pullback.fst _ _

中文:
缩写 pullbackFst
  签名: (F : WalkingParallelPair ⥤ C)
  定义体: pullback.fst _ _

Depends on / 依赖: pullback, pullback.fst
-/
abbrev pullbackFst (F : WalkingParallelPair ⥤ C) :
    constructEqualizer F ⟶ F.obj WalkingParallelPair.zero :=
  pullback.fst _ _

set_option backward.isDefEq.respectTransparency false in
/--
theorem `pullbackFst_eq_pullback_snd` / 定理 `pullbackFst_eq_pullback_snd`

English:
theorem pullbackFst_eq_pullback_snd
  given: (F : WalkingParallelPair ⥤ C)
  proof: by
  convert!
    (eq_whisker pullback.condition Limits.prod.fst :
      (_ : constructEqualizer F ⟶ F.obj WalkingParallelPair.zero) = _) <;> simp

中文:
定理 pullbackFst_eq_pullback_snd
  条件: (F : WalkingParallelPair ⥤ C)
  证明: by
  convert!
    (eq_whisker pullback.condition Limits.prod.fst :
      (_ : constructEqualizer F ⟶ F.obj WalkingParallelPair.zero) = _) <;> simp

Depends on / 依赖: F.obj, IsPushout, IsPushout.of_horiz_isIso_epi, IsPushout.paste_horiz, Limits, Limits.prod.fst, WalkingParallelPair, WalkingParallelPair.zero, condition, constructEqualizer, convert, eq_whisker, hasPushout, of_hasPushout, of_horiz_isIso_epi, paste_horiz, pullback, pullback.condition, pushout, pushout.inl
-/
theorem pullbackFst_eq_pullback_snd (F : WalkingParallelPair ⥤ C) :
    pullbackFst F = pullback.snd _ _ := by
  convert!
    (eq_whisker pullback.condition Limits.prod.fst :
      (_ : constructEqualizer F ⟶ F.obj WalkingParallelPair.zero) = _) <;> simp

set_option backward.isDefEq.respectTransparency false in
/--
Definition of `equalizerCone` / `equalizerCone` 的定义

English:
abbreviation equalizerCone
  signature: (F : WalkingParallelPair ⥤ C)
  body: Cone.ofFork
    (Fork.ofι (pullbackFst F)
      (by
        conv_rhs => rw [pullbackFst_eq_pullback_snd]
        convert!
          (eq_whisker pullback.condition Limits.prod.snd :
            (_ : constructEqualizer F ⟶ F.obj WalkingParallelPair.one) = _) using
          1 <;> simp))

中文:
缩写 equalizerCone
  签名: (F : WalkingParallelPair ⥤ C)
  定义体: Cone.ofFork
    (Fork.ofι (pullbackFst F)
      (by
        conv_rhs => rw [pullbackFst_eq_pullback_snd]
        convert!
          (eq_whisker pullback.condition Limits.prod.snd :
            (_ : constructEqualizer F ⟶ F.obj WalkingParallelPair.one) = _) using
          1 <;> simp))

Depends on / 依赖: Cone.ofFork, F.obj, Fork.of, Limits, Limits.prod.snd, WalkingParallelPair, WalkingParallelPair.one, condition, constructEqualizer, conv_rhs, convert, eq_whisker, ofFork, pullback, pullback.condition, pullbackFst, pullbackFst_eq_pullback_snd
-/
abbrev equalizerCone (F : WalkingParallelPair ⥤ C) : Cone F :=
  Cone.ofFork
    (Fork.ofι (pullbackFst F)
      (by
        conv_rhs => rw [pullbackFst_eq_pullback_snd]
        convert!
          (eq_whisker pullback.condition Limits.prod.snd :
            (_ : constructEqualizer F ⟶ F.obj WalkingParallelPair.one) = _) using
          1 <;> simp))

set_option backward.isDefEq.respectTransparency false in
/--
Definition of `equalizerConeIsLimit` / `equalizerConeIsLimit` 的定义

English:
definition equalizerConeIsLimit
  signature: (F : WalkingParallelPair ⥤ C)
  body: pullback.lift (c.π.app _) (c.π.app _)
  fac := by rintro c (_ | _) <;> simp
  uniq := by
    intro c _ J
    have J0 := J WalkingParallelPair.zero
    apply pullback.hom_ext
    · simpa [limit.lift_π] using J0
    · simp [← J0, pullbackFst_eq_pullback_snd]

中文:
定义 equalizerConeIsLimit
  签名: (F : WalkingParallelPair ⥤ C)
  定义体: pullback.lift (c.π.app _) (c.π.app _)
  fac := by rintro c (_ | _) <;> simp
  uniq := by
    intro c _ J
    have J0 := J WalkingParallelPair.zero
    apply pullback.hom_ext
    · simpa [limit.lift_π] using J0
    · simp [← J0, pullbackFst_eq_pullback_snd]

Depends on / 依赖: hasPushout_of_epi_comp, pullback, pullback.lift
-/
def equalizerConeIsLimit (F : WalkingParallelPair ⥤ C) : IsLimit (equalizerCone F) where
  lift c := pullback.lift (c.π.app _) (c.π.app _)
  fac := by rintro c (_ | _) <;> simp
  uniq := by
    intro c _ J
    have J0 := J WalkingParallelPair.zero
    apply pullback.hom_ext
    · simpa [limit.lift_π] using J0
    · simp [← J0, pullbackFst_eq_pullback_snd]

end HasEqualizersOfHasPullbacksAndBinaryProducts

open HasEqualizersOfHasPullbacksAndBinaryProducts

-- This is not an instance, as it is not always how one wants to construct equalizers!
/--
theorem `hasEqualizers_of_hasPullbacks_and_binary_products` / 定理 `hasEqualizers_of_hasPullbacks_and_binary_products`

English:
theorem hasEqualizers_of_hasPullbacks_and_binary_products
  given: [HasBinaryProducts C] [HasPullbacks C]
  proof: { has_limit := fun F =>
      HasLimit.mk
        { cone := equalizerCone F
          isLimit := equalizerConeIsLimit F } }

中文:
定理 hasEqualizers_of_hasPullbacks_and_binary_products
  条件: [HasBinaryProducts C] [有Pullbacks C]
  证明: { has_limit := fun F =>
      HasLimit.mk
        { cone := equalizerCone F
          isLimit := equalizerConeIsLimit F } }

Depends on / 依赖: HasLimit, HasLimit.mk, equalizerCone, equalizerConeIsLimit, has_limit, isLimit
-/
theorem hasEqualizers_of_hasPullbacks_and_binary_products [HasBinaryProducts C] [HasPullbacks C] :
    HasEqualizers C :=
  { has_limit := fun F =>
      HasLimit.mk
        { cone := equalizerCone F
          isLimit := equalizerConeIsLimit F } }

attribute [local instance] hasPullback_of_preservesPullback

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/--
lemma `preservesEqualizers_of_preservesPullbacks_and_binaryProducts` / 引理 `preservesEqualizers_of_preservesPullbacks_and_binaryProducts`

English:
lemma preservesEqualizers_of_preservesPullbacks_and_binaryProducts
  proof: ⟨fun {K} =>
preservesLimit_of_preserves_limit_cone (equalizerConeIsLimit K)
      { lift := fun c => by
          refine pullback.lift ?_ ?_ ?_ ≫ (PreservesPullback.iso _ _ _ ).inv
          · exact c.π.app WalkingParallelPair.zero
          · exact c.π.app WalkingParallelPair.zero
          apply (mapIsLimitOfPreservesOfIsLimit G _ _ (prodIsProd _ _)).hom_ext
          rintro (_ | _)
          · simp only [Category.assoc, ← G.map_comp, prod.lift_fst, BinaryFan.π_app_left,
              BinaryFan.mk_fst]
          · simp only [BinaryFan.π_app_right, BinaryFan.mk_snd, Category.assoc, ← G.map_comp,
              prod.lift_snd]
            exact
              (c.π.naturality WalkingParallelPairHom.left).symm.trans
                (c.π.naturality WalkingParallelPairHom.right)
        fac := fun c j => by
          rcases j with (_ | _) <;>
            simp only [Category.comp_id, PreservesPullback.iso_inv_fst, Cone.ofFork_π, G.map_comp,
              PreservesPullback.iso_inv_fst_assoc, Functor.mapCone_π_app, eqToHom_refl,
              Category.assoc, Fork.ofι_π_app, pullback.lift_fst, pullback.lift_fst_assoc]
          exact (c.π.naturality WalkingParallelPairHom.left).symm.trans (Category.id_comp _)
        uniq := fun s m h => by
          rw [Iso.eq_comp_inv]
          have := h WalkingParallelPair.zero
          dsimp [equalizerCone] at this
          ext <;>
            simp only [PreservesPullback.iso_hom_snd, Category.assoc,
              PreservesPullback.iso_hom_fst, pullback.lift_fst, pullback.lift_snd,
              Category.comp_id, ← pullbackFst_eq_pullback_snd, ← this] }⟩

中文:
引理 preservesEqualizers_of_preservesPullbacks_and_binaryProducts
  证明: ⟨fun {K} =>
preservesLimit_of_preserves_limit_cone (equalizerConeIsLimit K)
      { lift := fun c => by
          refine pullback.lift ?_ ?_ ?_ ≫ (PreservesPullback.iso _ _ _ ).inv
          · exact c.π.app WalkingParallelPair.zero
          · exact c.π.app WalkingParallelPair.zero
          apply (mapIsLimitOfPreservesOfIsLimit G _ _ (prodIsProd _ _)).hom_ext
          rintro (_ | _)
          · simp only [Category.assoc, ← G.map_comp, prod.lift_fst, BinaryFan.π_app_left,
              BinaryFan.mk_fst]
          · simp only [BinaryFan.π_app_right, BinaryFan.mk_snd, Category.assoc, ← G.map_comp,
              prod.lift_snd]
            exact
              (c.π.naturality WalkingParallelPairHom.left).symm.trans
                (c.π.naturality WalkingParallelPairHom.right)
        fac := fun c j => by
          rcases j with (_ | _) <;>
            simp only [Category.comp_id, PreservesPullback.iso_inv_fst, Cone.ofFork_π, G.map_comp,
              PreservesPullback.iso_inv_fst_assoc, Functor.mapCone_π_app, eqToHom_refl,
              Category.assoc, Fork.ofι_π_app, pullback.lift_fst, pullback.lift_fst_assoc]
          exact (c.π.naturality WalkingParallelPairHom.left).symm.trans (Category.id_comp _)
        uniq := fun s m h => by
          rw [Iso.eq_comp_inv]
          have := h WalkingParallelPair.zero
          dsimp [equalizerCone] at this
          ext <;>
            simp only [PreservesPullback.iso_hom_snd, Category.assoc,
              PreservesPullback.iso_hom_fst, pullback.lift_fst, pullback.lift_snd,
              Category.comp_id, ← pullbackFst_eq_pullback_snd, ← this] }⟩

Depends on / 依赖: BinaryFan, BinaryFan.mk_fst, BinaryFan.mk_snd, Category, Category.assoc, G.map_comp, PreservesPullback, PreservesPullback.iso, WalkingParallelPair, WalkingParallelPair.zero, equalizerConeIsLimit, hom_ext, lift_fst, mapIsLimitOfPreservesOfIsLimit, map_comp, mk_fst, mk_snd, preservesLimit_of_preserves_limit_cone, prod.lift_fst, prodIsProd
-/
lemma preservesEqualizers_of_preservesPullbacks_and_binaryProducts
    [HasBinaryProducts C] [HasPullbacks C]
    [PreservesLimitsOfShape (Discrete WalkingPair) G] [PreservesLimitsOfShape WalkingCospan G] :
    PreservesLimitsOfShape WalkingParallelPair G :=
  ⟨fun {K} =>
preservesLimit_of_preserves_limit_cone (equalizerConeIsLimit K)
      { lift := fun c => by
          refine pullback.lift ?_ ?_ ?_ ≫ (PreservesPullback.iso _ _ _ ).inv
          · exact c.π.app WalkingParallelPair.zero
          · exact c.π.app WalkingParallelPair.zero
          apply (mapIsLimitOfPreservesOfIsLimit G _ _ (prodIsProd _ _)).hom_ext
          rintro (_ | _)
          · simp only [Category.assoc, ← G.map_comp, prod.lift_fst, BinaryFan.π_app_left,
              BinaryFan.mk_fst]
          · simp only [BinaryFan.π_app_right, BinaryFan.mk_snd, Category.assoc, ← G.map_comp,
              prod.lift_snd]
            exact
              (c.π.naturality WalkingParallelPairHom.left).symm.trans
                (c.π.naturality WalkingParallelPairHom.right)
        fac := fun c j => by
          rcases j with (_ | _) <;>
            simp only [Category.comp_id, PreservesPullback.iso_inv_fst, Cone.ofFork_π, G.map_comp,
              PreservesPullback.iso_inv_fst_assoc, Functor.mapCone_π_app, eqToHom_refl,
              Category.assoc, Fork.ofι_π_app, pullback.lift_fst, pullback.lift_fst_assoc]
          exact (c.π.naturality WalkingParallelPairHom.left).symm.trans (Category.id_comp _)
        uniq := fun s m h => by
          rw [Iso.eq_comp_inv]
          have := h WalkingParallelPair.zero
          dsimp [equalizerCone] at this
          ext <;>
            simp only [PreservesPullback.iso_hom_snd, Category.assoc,
              PreservesPullback.iso_hom_fst, pullback.lift_fst, pullback.lift_snd,
              Category.comp_id, ← pullbackFst_eq_pullback_snd, ← this] }⟩

-- We hide the "implementation details" inside a namespace
namespace HasCoequalizersOfHasPushoutsAndBinaryCoproducts

variable [HasBinaryCoproducts C] [HasPushouts C]

/--
Definition of `constructCoequalizer` / `constructCoequalizer` 的定义

English:
abbreviation constructCoequalizer
  signature: (F : WalkingParallelPair ⥤ C)
  body: pushout (coprod.desc (𝟙 _) (F.map WalkingParallelPairHom.left))
    (coprod.desc (𝟙 _) (F.map WalkingParallelPairHom.right))

中文:
缩写 constructCoequalizer
  签名: (F : WalkingParallelPair ⥤ C)
  定义体: pushout (coprod.desc (𝟙 _) (F.map WalkingParallelPairHom.left))
    (coprod.desc (𝟙 _) (F.map WalkingParallelPairHom.right))

Depends on / 依赖: F.map, WalkingParallelPairHom, WalkingParallelPairHom.left, WalkingParallelPairHom.right, coprod, coprod.desc, pushout
-/
abbrev constructCoequalizer (F : WalkingParallelPair ⥤ C) : C :=
  pushout (coprod.desc (𝟙 _) (F.map WalkingParallelPairHom.left))
    (coprod.desc (𝟙 _) (F.map WalkingParallelPairHom.right))

/--
Definition of `pushoutInl` / `pushoutInl` 的定义

English:
abbreviation pushoutInl
  signature: (F : WalkingParallelPair ⥤ C)
  body: pushout.inl _ _

中文:
缩写 pushoutInl
  签名: (F : WalkingParallelPair ⥤ C)
  定义体: pushout.inl _ _

Depends on / 依赖: pushout, pushout.inl
-/
abbrev pushoutInl (F : WalkingParallelPair ⥤ C) :
    F.obj WalkingParallelPair.one ⟶ constructCoequalizer F :=
  pushout.inl _ _

set_option backward.isDefEq.respectTransparency false in
/--
theorem `pushoutInl_eq_pushout_inr` / 定理 `pushoutInl_eq_pushout_inr`

English:
theorem pushoutInl_eq_pushout_inr
  given: (F : WalkingParallelPair ⥤ C)
  proof: by
  convert!
      (whisker_eq Limits.coprod.inl pushout.condition : (_ : F.obj _ ⟶ constructCoequalizer _) = _)
    <;> simp

中文:
定理 pushoutInl_eq_pushout_inr
  条件: (F : WalkingParallelPair ⥤ C)
  证明: by
  convert!
      (whisker_eq Limits.coprod.inl pushout.condition : (_ : F.obj _ ⟶ constructCoequalizer _) = _)
    <;> simp

Depends on / 依赖: F.obj, Limits, Limits.coprod.inl, condition, constructCoequalizer, convert, coprod, pushout, pushout.condition, whisker_eq
-/
theorem pushoutInl_eq_pushout_inr (F : WalkingParallelPair ⥤ C) :
    pushoutInl F = pushout.inr _ _ := by
  convert!
      (whisker_eq Limits.coprod.inl pushout.condition : (_ : F.obj _ ⟶ constructCoequalizer _) = _)
    <;> simp

set_option backward.isDefEq.respectTransparency false in
/--
Definition of `coequalizerCocone` / `coequalizerCocone` 的定义

English:
abbreviation coequalizerCocone
  signature: (F : WalkingParallelPair ⥤ C)
  body: Cocone.ofCofork
    (Cofork.ofπ (pushoutInl F) (by
        conv_rhs => rw [pushoutInl_eq_pushout_inr]
        convert!
          (whisker_eq Limits.coprod.inr pushout.condition :
            (_ : F.obj _ ⟶ constructCoequalizer _) = _) using
          1 <;> simp))

中文:
缩写 coequalizerCocone
  签名: (F : WalkingParallelPair ⥤ C)
  定义体: Cocone.ofCofork
    (Cofork.ofπ (pushoutInl F) (by
        conv_rhs => rw [pushoutInl_eq_pushout_inr]
        convert!
          (whisker_eq Limits.coprod.inr pushout.condition :
            (_ : F.obj _ ⟶ constructCoequalizer _) = _) using
          1 <;> simp))

Depends on / 依赖: Cocone, Cocone.ofCofork, Cofork, Cofork.of, F.obj, Limits, Limits.coprod.inr, condition, constructCoequalizer, conv_rhs, convert, coprod, ofCofork, pushout, pushout.condition, pushoutInl, pushoutInl_eq_pushout_inr, whisker_eq
-/
abbrev coequalizerCocone (F : WalkingParallelPair ⥤ C) : Cocone F :=
  Cocone.ofCofork
    (Cofork.ofπ (pushoutInl F) (by
        conv_rhs => rw [pushoutInl_eq_pushout_inr]
        convert!
          (whisker_eq Limits.coprod.inr pushout.condition :
            (_ : F.obj _ ⟶ constructCoequalizer _) = _) using
          1 <;> simp))

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/--
Definition of `coequalizerCoconeIsColimit` / `coequalizerCoconeIsColimit` 的定义

English:
definition coequalizerCoconeIsColimit
  signature: (F : WalkingParallelPair ⥤ C)
  body: pushout.desc (c.ι.app _) (c.ι.app _)
  fac := by rintro c (_ | _) <;> simp
  uniq := by
    intro c m J
    have J1 : pushoutInl F ≫ m = c.ι.app WalkingParallelPair.one := by
      simpa using J WalkingParallelPair.one
    apply pushout.hom_ext
    · rw [colimit.ι_desc]
      exact J1
    · rw [colimit.ι_desc, ← pushoutInl_eq_pushout_inr]
      exact J1

中文:
定义 coequalizerCoconeIsColimit
  签名: (F : WalkingParallelPair ⥤ C)
  定义体: pushout.desc (c.ι.app _) (c.ι.app _)
  fac := by rintro c (_ | _) <;> simp
  uniq := by
    intro c m J
    have J1 : pushoutInl F ≫ m = c.ι.app WalkingParallelPair.one := by
      simpa using J WalkingParallelPair.one
    apply pushout.hom_ext
    · rw [colimit.ι_desc]
      exact J1
    · rw [colimit.ι_desc, ← pushoutInl_eq_pushout_inr]
      exact J1

Depends on / 依赖: pushout, pushout.desc
-/
def coequalizerCoconeIsColimit (F : WalkingParallelPair ⥤ C) : IsColimit (coequalizerCocone F) where
  desc c := pushout.desc (c.ι.app _) (c.ι.app _)
  fac := by rintro c (_ | _) <;> simp
  uniq := by
    intro c m J
    have J1 : pushoutInl F ≫ m = c.ι.app WalkingParallelPair.one := by
      simpa using J WalkingParallelPair.one
    apply pushout.hom_ext
    · rw [colimit.ι_desc]
      exact J1
    · rw [colimit.ι_desc, ← pushoutInl_eq_pushout_inr]
      exact J1

end HasCoequalizersOfHasPushoutsAndBinaryCoproducts

open HasCoequalizersOfHasPushoutsAndBinaryCoproducts

-- This is not an instance, as it is not always how one wants to construct equalizers!
/--
theorem `hasCoequalizers_of_hasPushouts_and_binary_coproducts` / 定理 `hasCoequalizers_of_hasPushouts_and_binary_coproducts`

English:
theorem hasCoequalizers_of_hasPushouts_and_binary_coproducts
  statement: [HasBinaryCoproducts C]
  proof: {
    has_colimit := fun F =>
      HasColimit.mk
        { cocone := coequalizerCocone F
          isColimit := coequalizerCoconeIsColimit F } }

中文:
定理 hasCoequalizers_of_hasPushouts_and_binary_coproducts
  结论: [HasBinaryCoproducts C]
  证明: {
    has_colimit := fun F =>
      HasColimit.mk
        { cocone := coequalizerCocone F
          isColimit := coequalizerCoconeIsColimit F } }

Depends on / 依赖: HasColimit, HasColimit.mk, cocone, coequalizerCocone, coequalizerCoconeIsColimit, has_colimit, isColimit
-/
theorem hasCoequalizers_of_hasPushouts_and_binary_coproducts [HasBinaryCoproducts C]
    [HasPushouts C] : HasCoequalizers C :=
  {
    has_colimit := fun F =>
      HasColimit.mk
        { cocone := coequalizerCocone F
          isColimit := coequalizerCoconeIsColimit F } }

attribute [local instance] hasPushout_of_preservesPushout

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/--
lemma `preservesCoequalizers_of_preservesPushouts_and_binaryCoproducts` / 引理 `preservesCoequalizers_of_preservesPushouts_and_binaryCoproducts`

English:
lemma preservesCoequalizers_of_preservesPushouts_and_binaryCoproducts
  statement: [HasBinaryCoproducts C]
  proof: ⟨fun {K} =>
preservesColimit_of_preserves_colimit_cocone (coequalizerCoconeIsColimit K)
      { desc := fun c => by
          refine (PreservesPushout.iso _ _ _).inv ≫ pushout.desc ?_ ?_ ?_
          · exact c.ι.app WalkingParallelPair.one
          · exact c.ι.app WalkingParallelPair.one
          apply (mapIsColimitOfPreservesOfIsColimit G _ _ (coprodIsCoprod _ _)).hom_ext
          rintro (_ | _)
          · simp only [BinaryCofan.ι_app_left, BinaryCofan.mk_inl, ←
              G.map_comp_assoc, coprod.inl_desc]
          · simp only [BinaryCofan.ι_app_right, BinaryCofan.mk_inr, ←
              G.map_comp_assoc, coprod.inr_desc]
            exact
              (c.ι.naturality WalkingParallelPairHom.left).trans
                (c.ι.naturality WalkingParallelPairHom.right).symm
        fac := fun c j => by
          rcases j with (_ | _) <;>
            simp only [Functor.mapCocone_ι_app, Cocone.ofCofork_ι, Category.id_comp,
              eqToHom_refl, Category.assoc, Functor.map_comp, Cofork.ofπ_ι_app, pushout.inl_desc,
              PreservesPushout.inl_iso_inv_assoc]
          exact (c.ι.naturality WalkingParallelPairHom.left).trans (Category.comp_id _)
        uniq := fun s m h => by
          rw [Iso.eq_inv_comp]
          have := h WalkingParallelPair.one
          dsimp [coequalizerCocone] at this
          ext <;>
            simp only [PreservesPushout.inl_iso_hom_assoc, Category.id_comp, pushout.inl_desc,
              pushout.inr_desc, PreservesPushout.inr_iso_hom_assoc, ← pushoutInl_eq_pushout_inr, ←
              this] }⟩

中文:
引理 preservesCoequalizers_of_preservesPushouts_and_binaryCoproducts
  结论: [HasBinaryCoproducts C]
  证明: ⟨fun {K} =>
preservesColimit_of_preserves_colimit_cocone (coequalizerCoconeIsColimit K)
      { desc := fun c => by
          refine (PreservesPushout.iso _ _ _).inv ≫ pushout.desc ?_ ?_ ?_
          · exact c.ι.app WalkingParallelPair.one
          · exact c.ι.app WalkingParallelPair.one
          apply (mapIsColimitOfPreservesOfIsColimit G _ _ (coprodIsCoprod _ _)).hom_ext
          rintro (_ | _)
          · simp only [BinaryCofan.ι_app_left, BinaryCofan.mk_inl, ←
              G.map_comp_assoc, coprod.inl_desc]
          · simp only [BinaryCofan.ι_app_right, BinaryCofan.mk_inr, ←
              G.map_comp_assoc, coprod.inr_desc]
            exact
              (c.ι.naturality WalkingParallelPairHom.left).trans
                (c.ι.naturality WalkingParallelPairHom.right).symm
        fac := fun c j => by
          rcases j with (_ | _) <;>
            simp only [Functor.mapCocone_ι_app, Cocone.ofCofork_ι, Category.id_comp,
              eqToHom_refl, Category.assoc, Functor.map_comp, Cofork.ofπ_ι_app, pushout.inl_desc,
              PreservesPushout.inl_iso_inv_assoc]
          exact (c.ι.naturality WalkingParallelPairHom.left).trans (Category.comp_id _)
        uniq := fun s m h => by
          rw [Iso.eq_inv_comp]
          have := h WalkingParallelPair.one
          dsimp [coequalizerCocone] at this
          ext <;>
            simp only [PreservesPushout.inl_iso_hom_assoc, Category.id_comp, pushout.inl_desc,
              pushout.inr_desc, PreservesPushout.inr_iso_hom_assoc, ← pushoutInl_eq_pushout_inr, ←
              this] }⟩

Depends on / 依赖: BinaryCofan, BinaryCofan.mk_inl, BinaryCofan.mk_inr, G.map_comp_assoc, PreservesPushout, PreservesPushout.iso, WalkingParallelPair, WalkingParallelPair.one, coequalizerCoconeIsColimit, coprod, coprod.inl_desc, coprodIsCoprod, hom_ext, inl_desc, mapIsColimitOfPreservesOfIsColimit, map_comp_assoc, mk_inl, mk_inr, preservesColimit_of_preserves_colimit_cocone, pushout
-/
lemma preservesCoequalizers_of_preservesPushouts_and_binaryCoproducts [HasBinaryCoproducts C]
    [HasPushouts C] [PreservesColimitsOfShape (Discrete WalkingPair) G]
    [PreservesColimitsOfShape WalkingSpan G] : PreservesColimitsOfShape WalkingParallelPair G :=
  ⟨fun {K} =>
preservesColimit_of_preserves_colimit_cocone (coequalizerCoconeIsColimit K)
      { desc := fun c => by
          refine (PreservesPushout.iso _ _ _).inv ≫ pushout.desc ?_ ?_ ?_
          · exact c.ι.app WalkingParallelPair.one
          · exact c.ι.app WalkingParallelPair.one
          apply (mapIsColimitOfPreservesOfIsColimit G _ _ (coprodIsCoprod _ _)).hom_ext
          rintro (_ | _)
          · simp only [BinaryCofan.ι_app_left, BinaryCofan.mk_inl, ←
              G.map_comp_assoc, coprod.inl_desc]
          · simp only [BinaryCofan.ι_app_right, BinaryCofan.mk_inr, ←
              G.map_comp_assoc, coprod.inr_desc]
            exact
              (c.ι.naturality WalkingParallelPairHom.left).trans
                (c.ι.naturality WalkingParallelPairHom.right).symm
        fac := fun c j => by
          rcases j with (_ | _) <;>
            simp only [Functor.mapCocone_ι_app, Cocone.ofCofork_ι, Category.id_comp,
              eqToHom_refl, Category.assoc, Functor.map_comp, Cofork.ofπ_ι_app, pushout.inl_desc,
              PreservesPushout.inl_iso_inv_assoc]
          exact (c.ι.naturality WalkingParallelPairHom.left).trans (Category.comp_id _)
        uniq := fun s m h => by
          rw [Iso.eq_inv_comp]
          have := h WalkingParallelPair.one
          dsimp [coequalizerCocone] at this
          ext <;>
            simp only [PreservesPushout.inl_iso_hom_assoc, Category.id_comp, pushout.inl_desc,
              pushout.inr_desc, PreservesPushout.inr_iso_hom_assoc, ← pushoutInl_eq_pushout_inr, ←
              this] }⟩

end CategoryTheory.Limits
