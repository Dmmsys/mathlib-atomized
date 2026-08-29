/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.CategoryTheory.LiftingProperties.Basic
public import Mathlib.CategoryTheory.Adjunction.Parametrized
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.PullbackObjObj

/-!
# Lifting properties and parametrized adjunctions

If we have a parametrized adjunction `adj₂ : F ⊣₂ G`,
`sq₁₂ : F.PushoutObjObj f₁ f₂` and `sq₁₃ : G.PullbackObjObj f₁ f₃`,
we show that `sq₁₂.ι` has the left lifting property with respect to
`f₃` if and only if `f₂` has the left lifting property with respect
to `sq₁₃.π`: this is the lemma `ParametrizedAdjunction.hasLiftingProperty_iff`.

-/

@[expose] public section

universe v₁ v₂ v₃ u₁ u₂ u₃

namespace CategoryTheory

open Opposite Limits

variable {C₁ : Type u₁} {C₂ : Type u₂} {C₃ : Type u₃}
  [Category.{v₁} C₁] [Category.{v₂} C₂] [Category.{v₃} C₃]
  (F : C₁ ⥤ C₂ ⥤ C₃) (G : C₁ᵒᵖ ⥤ C₃ ⥤ C₂)

namespace ParametrizedAdjunction

variable {F G} (adj₂ : F ⊣₂ G)
  {X₁ Y₁ : C₁} {f₁ : X₁ ⟶ Y₁} {X₂ Y₂ : C₂} {f₂ : X₂ ⟶ Y₂}
  {X₃ Y₃ : C₃} {f₃ : X₃ ⟶ Y₃}
  (sq₁₂ : F.PushoutObjObj f₁ f₂) (sq₁₃ : G.PullbackObjObj f₁ f₃)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- Given a parametrized adjunction `F ⊣₂ G` between bifunctors, and structures
`sq₁₂ : F.PushoutObjObj f₁ f₂` and `sq₁₃ : G.PullbackObjObj f₁ f₃`, there are
as many commutative squares with left map `sq₁₂.ι` and right map `f₃`
as commutative squares with left map `f₂` and right map `sq₁₃.π`. -/
@[simps! apply_left symm_apply_right]
/--
Definition of `arrowHomEquiv` / `arrowHomEquiv` 的定义

English:
definition arrowHomEquiv
  signature: :
  body: Arrow.homMk (adj₂.homEquiv (sq₁₂.inl ≫ α.left))
      (sq₁₃.isPullback.lift
        (adj₂.homEquiv (sq₁₂.inr ≫ α.left)) (adj₂.homEquiv α.right)
          (by simp [← adj₂.homEquiv_naturality_one,
              ← adj₂.homEquiv_naturality_three])) (by
            apply sq₁₃.isPullback.hom_ext
        

中文:
定义 arrowHomEquiv
  签名: :
  定义体: Arrow.homMk (adj₂.homEquiv (sq₁₂.inl ≫ α.left))
      (sq₁₃.isPullback.lift
        (adj₂.homEquiv (sq₁₂.inr ≫ α.left)) (adj₂.homEquiv α.right)
          (by simp [← adj₂.homEquiv_naturality_one,
              ← adj₂.homEquiv_naturality_three])) (by
            apply sq₁₃.isPullback.hom_ext
        

Depends on / 依赖: Arrow.homMk, homEquiv, homEquiv.symm, homEquiv_naturality_one, homEquiv_naturality_three, homEquiv_naturality_two, hom_ext, invFun, isPullback, isPullback.hom_ext, isPullback.lift, isPushout, isPushout.desc, isPushout.w_assoc, w_assoc
-/
noncomputable def arrowHomEquiv :
    (Arrow.mk sq₁₂.ι ⟶ Arrow.mk f₃) ≃
      (Arrow.mk f₂ ⟶ Arrow.mk sq₁₃.π) where
  toFun α :=
    Arrow.homMk (adj₂.homEquiv (sq₁₂.inl ≫ α.left))
      (sq₁₃.isPullback.lift
        (adj₂.homEquiv (sq₁₂.inr ≫ α.left)) (adj₂.homEquiv α.right)
          (by simp [← adj₂.homEquiv_naturality_one,
              ← adj₂.homEquiv_naturality_three])) (by
            apply sq₁₃.isPullback.hom_ext
            · simp [← adj₂.homEquiv_naturality_two,
                ← adj₂.homEquiv_naturality_one,
                sq₁₂.isPushout.w_assoc]
            · simp [← adj₂.homEquiv_naturality_two,
                ← adj₂.homEquiv_naturality_three])
  invFun β :=
    Arrow.homMk
      (sq₁₂.isPushout.desc
        (adj₂.homEquiv.symm β.left)
        (adj₂.homEquiv.symm (β.right ≫ sq₁₃.fst)) (by
          have := Arrow.w β =≫ sq₁₃.fst
          dsimp at this
          simp only [Category.assoc, sq₁₃.π_fst] at this
          simp only [← adj₂.homEquiv_symm_naturality_one,
            ← adj₂.homEquiv_symm_naturality_two,
            Arrow.mk_left, Arrow.mk_right, this]))
      (adj₂.homEquiv.symm (β.right ≫ sq₁₃.snd)) (by
        apply sq₁₂.isPushout.hom_ext
        · have := Arrow.w β =≫ sq₁₃.snd
          dsimp at this
          simp only [Category.assoc, sq₁₃.π_snd] at this
          simp [← adj₂.homEquiv_symm_naturality_two,
            ← adj₂.homEquiv_symm_naturality_three, this]
        · simp [← adj₂.homEquiv_symm_naturality_one,
            ← adj₂.homEquiv_symm_naturality_three, sq₁₃.isPullback.w])
  left_inv α := by
    ext
    · apply sq₁₂.isPushout.hom_ext <;> simp
    · simp
  right_inv β := by
    ext
    · simp
    · apply sq₁₃.isPullback.hom_ext <;> simp

@[reassoc (attr := simp)]
/--
lemma `arrowHomEquiv_apply_right_fst` / 引理 `arrowHomEquiv_apply_right_fst`

English:
lemma arrowHomEquiv_apply_right_fst
  given: (α : Arrow.mk sq₁₂.ι ⟶ Arrow.mk f₃)
  proof: IsPullback.lift_fst _ _ _ _

@[reassoc (attr := simp)]

中文:
引理 arrowHomEquiv_apply_right_fst
  条件: (α : Arrow.mk sq₁₂.ι ⟶ Arrow.mk f₃)
  证明: IsPullback.lift_fst _ _ _ _

@[reassoc (attr := simp)]

Depends on / 依赖: IsPullback, IsPullback.lift_fst, lift_fst
-/
lemma arrowHomEquiv_apply_right_fst (α : Arrow.mk sq₁₂.ι ⟶ Arrow.mk f₃) :
    ((adj₂.arrowHomEquiv sq₁₂ sq₁₃) α).right ≫ sq₁₃.fst = adj₂.homEquiv (sq₁₂.inr ≫ α.left) :=
  IsPullback.lift_fst _ _ _ _

@[reassoc (attr := simp)]
/--
lemma `arrowHomEquiv_apply_right_snd` / 引理 `arrowHomEquiv_apply_right_snd`

English:
lemma arrowHomEquiv_apply_right_snd
  given: (α : Arrow.mk sq₁₂.ι ⟶ Arrow.mk f₃)
  proof: IsPullback.lift_snd _ _ _ _

@[reassoc (attr := simp)]

中文:
引理 arrowHomEquiv_apply_right_snd
  条件: (α : Arrow.mk sq₁₂.ι ⟶ Arrow.mk f₃)
  证明: IsPullback.lift_snd _ _ _ _

@[reassoc (attr := simp)]

Depends on / 依赖: IsPullback, IsPullback.lift_snd, lift_snd
-/
lemma arrowHomEquiv_apply_right_snd (α : Arrow.mk sq₁₂.ι ⟶ Arrow.mk f₃) :
    ((adj₂.arrowHomEquiv sq₁₂ sq₁₃) α).right ≫ sq₁₃.snd = adj₂.homEquiv α.right :=
  IsPullback.lift_snd _ _ _ _

@[reassoc (attr := simp)]
/--
lemma `inl_arrowHomEquiv_symm_apply_left` / 引理 `inl_arrowHomEquiv_symm_apply_left`

English:
lemma inl_arrowHomEquiv_symm_apply_left
  given: (β : Arrow.mk f₂ ⟶ Arrow.mk sq₁₃.π)
  proof: IsPushout.inl_desc _ _ _ _

@[reassoc (attr := simp)]

中文:
引理 inl_arrowHomEquiv_symm_apply_left
  条件: (β : Arrow.mk f₂ ⟶ Arrow.mk sq₁₃.π)
  证明: IsPushout.inl_desc _ _ _ _

@[reassoc (attr := simp)]

Depends on / 依赖: IsPushout, IsPushout.inl_desc, inl_desc
-/
lemma inl_arrowHomEquiv_symm_apply_left (β : Arrow.mk f₂ ⟶ Arrow.mk sq₁₃.π) :
    sq₁₂.inl ≫ ((adj₂.arrowHomEquiv sq₁₂ sq₁₃).symm β).left = adj₂.homEquiv.symm β.left :=
  IsPushout.inl_desc _ _ _ _

@[reassoc (attr := simp)]
/--
lemma `inr_arrowHomEquiv_symm_apply_left` / 引理 `inr_arrowHomEquiv_symm_apply_left`

English:
lemma inr_arrowHomEquiv_symm_apply_left
  given: (β : Arrow.mk f₂ ⟶ Arrow.mk sq₁₃.π)
  proof: IsPushout.inr_desc _ _ _ _

中文:
引理 inr_arrowHomEquiv_symm_apply_left
  条件: (β : Arrow.mk f₂ ⟶ Arrow.mk sq₁₃.π)
  证明: IsPushout.inr_desc _ _ _ _

Depends on / 依赖: IsPushout, IsPushout.inr_desc, WalkingCospan, WalkingCospan.left, WalkingCospan.right, fac_left, fac_right, inr_desc, isLimitAux
-/
lemma inr_arrowHomEquiv_symm_apply_left (β : Arrow.mk f₂ ⟶ Arrow.mk sq₁₃.π) :
    sq₁₂.inr ≫ ((adj₂.arrowHomEquiv sq₁₂ sq₁₃).symm β).left =
    adj₂.homEquiv.symm (β.right ≫ sq₁₃.fst) :=
  IsPushout.inr_desc _ _ _ _

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/--
Definition of `liftStructEquiv` / `liftStructEquiv` 的定义

English:
definition liftStructEquiv
  signature: (α : Arrow.mk sq₁₂.ι ⟶ Arrow.mk f₃)
  body: { l := adj₂.homEquiv l.l
      fac_left := by
        have := l.fac_left
        dsimp at this ⊢
        simp only [← adj₂.homEquiv_naturality_two, ← this,
          sq₁₂.inl_ι_assoc]
      fac_right := by
        apply sq₁₃.isPullback.hom_ext
        · have := l.fac_left
          dsimp at this ⊢
 

中文:
定义 liftStructEquiv
  签名: (α : Arrow.mk sq₁₂.ι ⟶ Arrow.mk f₃)
  定义体: { l := adj₂.homEquiv l.l
      fac_left := by
        have := l.fac_left
        dsimp at this ⊢
        simp only [← adj₂.homEquiv_naturality_two, ← this,
          sq₁₂.inl_ι_assoc]
      fac_right := by
        apply sq₁₃.isPullback.hom_ext
        · have := l.fac_left
          dsimp at this ⊢
 

Depends on / 依赖: Arrow.mk_left, Category, Category.assoc, arrowHomEquiv, arrowHomEquiv_apply_right_fst, equalizer_ext, fac_left, fac_right, homEquiv, homEquiv_naturality_one, homEquiv_naturality_three, homEquiv_naturality_two, hom_ext, ht.hom_ext, isPullback, isPullback.hom_ext, l.fac_left, l.fac_right, mk_left
-/
noncomputable def liftStructEquiv (α : Arrow.mk sq₁₂.ι ⟶ Arrow.mk f₃) :
    Arrow.LiftStruct α ≃ Arrow.LiftStruct (adj₂.arrowHomEquiv sq₁₂ sq₁₃ α) where
  toFun l :=
    { l := adj₂.homEquiv l.l
      fac_left := by
        have := l.fac_left
        dsimp at this ⊢
        simp only [← adj₂.homEquiv_naturality_two, ← this,
          sq₁₂.inl_ι_assoc]
      fac_right := by
        apply sq₁₃.isPullback.hom_ext
        · have := l.fac_left
          dsimp at this ⊢
          simp only [Category.assoc, sq₁₃.π_fst, ← adj₂.homEquiv_naturality_one,
            arrowHomEquiv_apply_right_fst, Arrow.mk_left, ← this, sq₁₂.inr_ι_assoc]
        · have := l.fac_right
          dsimp at this ⊢
          simp only [Category.assoc, sq₁₃.π_snd, ← this, adj₂.homEquiv_naturality_three,
            arrowHomEquiv_apply_right_snd, Arrow.mk_right] }
  invFun l :=
    { l := adj₂.homEquiv.symm l.l
      fac_left := by
        apply sq₁₂.isPushout.hom_ext
        · have := l.fac_left
          dsimp at this ⊢
          simp only [sq₁₂.inl_ι_assoc, ← adj₂.homEquiv_symm_naturality_two,
            this, Equiv.symm_apply_apply]
        · have := l.fac_right =≫ sq₁₃.fst
          dsimp at this ⊢
          simp only [Category.assoc, sq₁₃.π_fst] at this
          simp only [sq₁₂.inr_ι_assoc, ← adj₂.homEquiv_symm_naturality_one,
            this, Equiv.symm_apply_apply, arrowHomEquiv_apply_right_fst, Arrow.mk_left]
      fac_right := by
        have := l.fac_right =≫ sq₁₃.snd
        dsimp at this ⊢
        simp only [Category.assoc, sq₁₃.π_snd, arrowHomEquiv_apply_right_snd,
          Arrow.mk_right] at this
        rw [← adj₂.homEquiv_symm_naturality_three]; rw [this]; rw [Equiv.symm_apply_apply] }
  left_inv _ := by aesop
  right_inv _ := by aesop

include adj₂ in
/--
lemma `hasLiftingProperty_iff` / 引理 `hasLiftingProperty_iff`

English:
lemma hasLiftingProperty_iff
  proof: by
  simp only [Arrow.hasLiftingProperty_iff]
  constructor
  · intro h β
    obtain ⟨α, rfl⟩ := (adj₂.arrowHomEquiv sq₁₂ sq₁₃).surjective β
    exact ⟨adj₂.liftStructEquiv sq₁₂ sq₁₃ α (h α).some⟩
  · intro h α
    exact ⟨(adj₂.liftStructEquiv sq₁₂ sq₁₃ α).symm (h _).some⟩

中文:
引理 hasLiftingProperty_iff
  证明: by
  simp only [Arrow.hasLiftingProperty_iff]
  constructor
  · intro h β
    obtain ⟨α, rfl⟩ := (adj₂.arrowHomEquiv sq₁₂ sq₁₃).surjective β
    exact ⟨adj₂.liftStructEquiv sq₁₂ sq₁₃ α (h α).some⟩
  · intro h α
    exact ⟨(adj₂.liftStructEquiv sq₁₂ sq₁₃ α).symm (h _).some⟩

Depends on / 依赖: Arrow.hasLiftingProperty_iff, PullbackCone, PullbackCone.mk, arrowHomEquiv, hasLiftingProperty_iff, ht.lift, liftStructEquiv, surjective
-/
lemma hasLiftingProperty_iff :
    HasLiftingProperty sq₁₂.ι f₃ ↔ HasLiftingProperty f₂ sq₁₃.π := by
  simp only [Arrow.hasLiftingProperty_iff]
  constructor
  · intro h β
    obtain ⟨α, rfl⟩ := (adj₂.arrowHomEquiv sq₁₂ sq₁₃).surjective β
    exact ⟨adj₂.liftStructEquiv sq₁₂ sq₁₃ α (h α).some⟩
  · intro h α
    exact ⟨(adj₂.liftStructEquiv sq₁₂ sq₁₃ α).symm (h _).some⟩

end ParametrizedAdjunction

end CategoryTheory
