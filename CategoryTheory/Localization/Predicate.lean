/-
Copyright (c) 2022 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.CategoryTheory.Localization.Construction

/-!

# Predicate for localized categories

In this file, a predicate `L.IsLocalization W` is introduced for a functor `L : C ⥤ D`
and `W : MorphismProperty C`: it expresses that `L` identifies `D` with the localized
category of `C` with respect to `W` (up to equivalence).

We introduce a universal property `StrictUniversalPropertyFixedTarget L W E` which
states that `L` inverts the morphisms in `W` and that all functors `C ⥤ E` inverting
`W` uniquely factor as a composition of `L ⋙ G` with `G : D ⥤ E`. Such universal
properties are inputs for the constructor `IsLocalization.mk'` for `L.IsLocalization W`.

When `L : C ⥤ D` is a localization functor for `W : MorphismProperty` (i.e. when
`[L.IsLocalization W]` holds), for any category `E`, there is
an equivalence `FunctorEquivalence L W E : (D ⥤ E) ≌ (W.FunctorsInverting E)`
that is induced by the composition with the functor `L`. When two functors
`F : C ⥤ E` and `F' : D ⥤ E` correspond via this equivalence, we shall say
that `F'` lifts `F`, and the associated isomorphism `L ⋙ F' ≅ F` is the
datum that is part of the class `Lifting L W F F'`. The functions
`liftNatTrans` and `liftNatIso` can be used to lift natural transformations
and natural isomorphisms between functors.

-/

@[expose] public section


noncomputable section

namespace CategoryTheory

open Category CategoryTheory.Functor

variable {C D : Type*} [Category* C] [Category* D] (L : C ⥤ D) (W : MorphismProperty C) (E : Type*)
  [Category* E]

namespace Functor

/--
Definition of `IsLocalization` / `IsLocalization` 的定义

English:
class IsLocalization
  parameters: : Prop where
  axioms and operations (2):
    - inverts : W.IsInvertedBy L
    - isEquivalence : IsEquivalence (Localization.Construction.lift L inverts)

中文:
类 是Localization
  参数: : 命题 where
  公理与运算 (2 个):
    - inverts : W.IsInvertedBy L
    - isEquivalence : 是等价 (Localization.Construction.lift L inverts)
-/
class IsLocalization : Prop where
  /-- the functor inverts the given `MorphismProperty` -/
  inverts : W.IsInvertedBy L
  /-- the induced functor from the constructed localized category is an equivalence -/
  isEquivalence : IsEquivalence (Localization.Construction.lift L inverts)

/--
Instance `q_isLocalization` / 实例 `q_isLocalization`

English:
instance q_isLocalization
  signature: : W.Q.IsLocalization W where
  body: W.Q_inverts
  isEquivalence := by
    suffices Localization.Construction.lift W.Q W.Q_inverts = 𝟭 _ by
      rw [this]
      infer_instance
    apply Localization.Construction.uniq
    simp only [Localization.Construction.fac]
    rfl

中文:
实例 q_isLocalization
  签名: : W.Q.是Localization W where
  定义体: W.Q_inverts
  isEquivalence := by
    suffices Localization.Construction.lift W.Q W.Q_inverts = 𝟭 _ by
      rw [this]
      infer_instance
    apply Localization.Construction.uniq
    simp only [Localization.Construction.fac]
    rfl

Depends on / 依赖: Q_inverts, W.Q_inverts
-/
instance q_isLocalization : W.Q.IsLocalization W where
  inverts := W.Q_inverts
  isEquivalence := by
    suffices Localization.Construction.lift W.Q W.Q_inverts = 𝟭 _ by
      rw [this]
      infer_instance
    apply Localization.Construction.uniq
    simp only [Localization.Construction.fac]
    rfl

end Functor

namespace Localization

/--
Definition of `StrictUniversalPropertyFixedTarget` / `StrictUniversalPropertyFixedTarget` 的定义

English:
structure StrictUniversalPropertyFixedTarget
  parameters: where
  axioms and operations (4):
    - inverts : W.IsInvertedBy L
    - lift : forall (F : C ⥤ E) (_ : W.IsInvertedBy F), D ⥤ E
    - fac : forall (F : C ⥤ E) (hF : W.IsInvertedBy F), L ⋙ lift F hF = F
    - uniq : forall (F₁ F₂ : D ⥤ E) (_ : L ⋙ F₁ = L ⋙ F₂), F₁ = F₂

中文:
结构 StrictUniversalPropertyFixedTarget
  参数: where
  公理与运算 (4 个):
    - inverts : W.IsInvertedBy L
    - lift : 对任意 (F : C ⥤ E) (_ : W.IsInvertedBy F), D ⥤ E
    - fac : 对任意 (F : C ⥤ E) (hF : W.IsInvertedBy F), L ⋙ lift F hF = F
    - uniq : 对任意 (F₁ F₂ : D ⥤ E) (_ : L ⋙ F₁ = L ⋙ F₂), F₁ = F₂
-/
structure StrictUniversalPropertyFixedTarget where
  /-- the functor `L` inverts `W` -/
  inverts : W.IsInvertedBy L
  /-- any functor `C ⥤ E` which inverts `W` can be lifted as a functor `D ⥤ E` -/
  lift : forall (F : C ⥤ E) (_ : W.IsInvertedBy F), D ⥤ E
  /-- there is a factorisation involving the lifted functor -/
  fac : forall (F : C ⥤ E) (hF : W.IsInvertedBy F), L ⋙ lift F hF = F
  /-- uniqueness of the lifted functor -/
  uniq : forall (F₁ F₂ : D ⥤ E) (_ : L ⋙ F₁ = L ⋙ F₂), F₁ = F₂

/-- The localized category `W.Localization` that was constructed satisfies
the universal property of the localization. -/
@[simps]
/--
Definition of `strictUniversalPropertyFixedTargetQ` / `strictUniversalPropertyFixedTargetQ` 的定义

English:
definition strictUniversalPropertyFixedTargetQ
  signature: : StrictUniversalPropertyFixedTarget W.Q W E where
  body: W.Q_inverts
  lift := Construction.lift
  fac := Construction.fac
  uniq := Construction.uniq

中文:
定义 strictUniversalPropertyFixedTargetQ
  签名: : StrictUniversalPropertyFixedTarget W.Q W E where
  定义体: W.Q_inverts
  lift := Construction.lift
  fac := Construction.fac
  uniq := Construction.uniq

Depends on / 依赖: Q_inverts, W.Q_inverts
-/
def strictUniversalPropertyFixedTargetQ : StrictUniversalPropertyFixedTarget W.Q W E where
  inverts := W.Q_inverts
  lift := Construction.lift
  fac := Construction.fac
  uniq := Construction.uniq

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Inhabited (StrictUniversalPropertyFixedTarget W.Q W E)
  body: ⟨strictUniversalPropertyFixedTargetQ _ _⟩

中文:
实例 :
  签名: 可居 (StrictUniversalPropertyFixedTarget W.Q W E)
  定义体: ⟨strictUniversalPropertyFixedTargetQ _ _⟩

Depends on / 依赖: strictUniversalPropertyFixedTargetQ
-/
instance : Inhabited (StrictUniversalPropertyFixedTarget W.Q W E) :=
  ⟨strictUniversalPropertyFixedTargetQ _ _⟩

/-- When `W` consists of isomorphisms, the identity satisfies the universal property
of the localization. -/
@[simps]
/--
Definition of `strictUniversalPropertyFixedTargetId` / `strictUniversalPropertyFixedTargetId` 的定义

English:
definition strictUniversalPropertyFixedTargetId
  signature: (hW : W <= MorphismProperty.isomorphisms C)
  body: hW f hf
  lift F _ := F
  fac F hF := by
    cases F
    rfl
  uniq F₁ F₂ eq := by
    cases F₁
    cases F₂
    exact eq

中文:
定义 strictUniversalPropertyFixedTargetId
  签名: (hW : W <= MorphismProperty.isomorphisms C)
  定义体: hW f hf
  lift F _ := F
  fac F hF := by
    cases F
    rfl
  uniq F₁ F₂ eq := by
    cases F₁
    cases F₂
    exact eq

Depends on / 依赖: _eq_shiftFunctorAdd, oppositeShiftFunctorAdd_hom_app, shiftFunctorAdd
-/
def strictUniversalPropertyFixedTargetId (hW : W <= MorphismProperty.isomorphisms C) :
    StrictUniversalPropertyFixedTarget (𝟭 C) W E where
  inverts _ _ f hf := hW f hf
  lift F _ := F
  fac F hF := by
    cases F
    rfl
  uniq F₁ F₂ eq := by
    cases F₁
    cases F₂
    exact eq

end Localization

namespace Functor

/--
theorem `IsLocalization.mk'` / 定理 `IsLocalization.mk'`

English:
theorem IsLocalization.mk'
  statement: (h₁ : Localization.StrictUniversalPropertyFixedTarget L W D)
  proof: { inverts := h₁.inverts
    isEquivalence := IsEquivalence.mk' (h₂.lift W.Q W.Q_inverts)
      (eqToIso (Localization.Construction.uniq _ _ (by
        simp only [← Functor.assoc, Localization.Construction.fac, h₂.fac, Functor.comp_id])))
      (eqToIso (h₁.uniq _ _ (by
        simp only [← Functor.assoc, h₂.fac, Localization.Construction.fac, Functor.comp_id]))) }

中文:
定理 是Localization.mk'
  结论: (h₁ : Localization.StrictUniversalPropertyFixedTarget L W D)
  证明: { inverts := h₁.inverts
    isEquivalence := IsEquivalence.mk' (h₂.lift W.Q W.Q_inverts)
      (eqToIso (Localization.Construction.uniq _ _ (by
        simp only [← Functor.assoc, Localization.Construction.fac, h₂.fac, Functor.comp_id])))
      (eqToIso (h₁.uniq _ _ (by
        simp only [← Functor.assoc, h₂.fac, Localization.Construction.fac, Functor.comp_id]))) }
-/
theorem IsLocalization.mk' (h₁ : Localization.StrictUniversalPropertyFixedTarget L W D)
    (h₂ : Localization.StrictUniversalPropertyFixedTarget L W W.Localization) :
    IsLocalization L W :=
  { inverts := h₁.inverts
    isEquivalence := IsEquivalence.mk' (h₂.lift W.Q W.Q_inverts)
      (eqToIso (Localization.Construction.uniq _ _ (by
        simp only [← Functor.assoc, Localization.Construction.fac, h₂.fac, Functor.comp_id])))
      (eqToIso (h₁.uniq _ _ (by
        simp only [← Functor.assoc, h₂.fac, Localization.Construction.fac, Functor.comp_id]))) }

/--
theorem `IsLocalization.for_id` / 定理 `IsLocalization.for_id`

English:
theorem IsLocalization.for_id
  given: (hW : W <= MorphismProperty.isomorphisms C)
  statement: (𝟭 C).IsLocalization W
  proof: IsLocalization.mk' _ _ (Localization.strictUniversalPropertyFixedTargetId W _ hW)
    (Localization.strictUniversalPropertyFixedTargetId W _ hW)

中文:
定理 是Localization.for_id
  条件: (hW : W <= MorphismProperty.isomorphisms C)
  结论: (𝟭 C).是Localization W
  证明: IsLocalization.mk' _ _ (Localization.strictUniversalPropertyFixedTargetId W _ hW)
    (Localization.strictUniversalPropertyFixedTargetId W _ hW)

Depends on / 依赖: IsLocalization, IsLocalization.mk, Localization, Localization.strictUniversalPropertyFixedTargetId, strictUniversalPropertyFixedTargetId
-/
theorem IsLocalization.for_id (hW : W <= MorphismProperty.isomorphisms C) : (𝟭 C).IsLocalization W :=
  IsLocalization.mk' _ _ (Localization.strictUniversalPropertyFixedTargetId W _ hW)
    (Localization.strictUniversalPropertyFixedTargetId W _ hW)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: (𝟭 C).IsLocalization (MorphismProperty.isomorphisms C)
  body: IsLocalization.for_id _ (by rfl)

中文:
实例 :
  签名: (𝟭 C).是Localization (MorphismProperty.isomorphisms C)
  定义体: IsLocalization.for_id _ (by rfl)

Depends on / 依赖: IsLocalization, IsLocalization.for_id, for_id
-/
instance : (𝟭 C).IsLocalization (MorphismProperty.isomorphisms C) :=
  IsLocalization.for_id _ (by rfl)

end Functor

namespace Localization

variable [L.IsLocalization W]

/--
theorem `inverts` / 定理 `inverts`

English:
theorem inverts
  statement: W.IsInvertedBy L
  proof: (inferInstance : L.IsLocalization W).inverts

中文:
定理 inverts
  结论: W.IsInvertedBy L
  证明: (inferInstance : L.IsLocalization W).inverts

Depends on / 依赖: IsLocalization, L.IsLocalization, inverts
-/
theorem inverts : W.IsInvertedBy L :=
  (inferInstance : L.IsLocalization W).inverts

/-- The isomorphism `L.obj X ≅ L.obj Y` that is deduced from a morphism `f : X ⟶ Y` which
belongs to `W`, when `L.IsLocalization W`. -/
@[simps! hom]
/--
Definition of `isoOfHom` / `isoOfHom` 的定义

English:
definition isoOfHom
  signature: {X Y : C} (f : X ⟶ Y) (hf : W f)
  body: haveI : IsIso (L.map f) := inverts L W f hf
  asIso (L.map f)

@[reassoc (attr := simp)]

中文:
定义 isoOfHom
  签名: {X Y : C} (f : X ⟶ Y) (hf : W f)
  定义体: haveI : IsIso (L.map f) := inverts L W f hf
  asIso (L.map f)

@[reassoc (attr := simp)]

Depends on / 依赖: L.map, inverts
-/
def isoOfHom {X Y : C} (f : X ⟶ Y) (hf : W f) : L.obj X ≅ L.obj Y :=
  haveI : IsIso (L.map f) := inverts L W f hf
  asIso (L.map f)

@[reassoc (attr := simp)]
/--
lemma `isoOfHom_hom_inv_id` / 引理 `isoOfHom_hom_inv_id`

English:
lemma isoOfHom_hom_inv_id
  given: {X Y : C} (f : X ⟶ Y) (hf : W f)
  proof: (isoOfHom L W f hf).hom_inv_id

@[reassoc (attr := simp)]

中文:
引理 isoOfHom_hom_inv_id
  条件: {X Y : C} (f : X ⟶ Y) (hf : W f)
  证明: (isoOfHom L W f hf).hom_inv_id

@[reassoc (attr := simp)]

Depends on / 依赖: hom_inv_id, isoOfHom
-/
lemma isoOfHom_hom_inv_id {X Y : C} (f : X ⟶ Y) (hf : W f) :
    L.map f ≫ (isoOfHom L W f hf).inv = 𝟙 _ :=
  (isoOfHom L W f hf).hom_inv_id

@[reassoc (attr := simp)]
/--
lemma `isoOfHom_inv_hom_id` / 引理 `isoOfHom_inv_hom_id`

English:
lemma isoOfHom_inv_hom_id
  given: {X Y : C} (f : X ⟶ Y) (hf : W f)
  proof: (isoOfHom L W f hf).inv_hom_id

@[simp]

中文:
引理 isoOfHom_inv_hom_id
  条件: {X Y : C} (f : X ⟶ Y) (hf : W f)
  证明: (isoOfHom L W f hf).inv_hom_id

@[simp]

Depends on / 依赖: inv_hom_id, isoOfHom
-/
lemma isoOfHom_inv_hom_id {X Y : C} (f : X ⟶ Y) (hf : W f) :
    (isoOfHom L W f hf).inv ≫ L.map f = 𝟙 _ :=
  (isoOfHom L W f hf).inv_hom_id

@[simp]
/--
lemma `isoOfHom_id_inv` / 引理 `isoOfHom_id_inv`

English:
lemma isoOfHom_id_inv
  given: (X : C) (hX : W (𝟙 X))
  proof: by
  rw [← cancel_mono (isoOfHom L W (𝟙 X) hX).hom]; rw [Iso.inv_hom_id]; rw [id_comp]; rw [isoOfHom_hom]; rw [Functor.map_id]

中文:
引理 isoOfHom_id_inv
  条件: (X : C) (hX : W (𝟙 X))
  证明: by
  rw [← cancel_mono (isoOfHom L W (𝟙 X) hX).hom]; rw [Iso.inv_hom_id]; rw [id_comp]; rw [isoOfHom_hom]; rw [Functor.map_id]

Depends on / 依赖: Functor, Functor.map_id, Iso.inv_hom_id, cancel_mono, id_comp, inv_hom_id, isoOfHom, isoOfHom_hom, map_id
-/
lemma isoOfHom_id_inv (X : C) (hX : W (𝟙 X)) :
    (isoOfHom L W (𝟙 X) hX).inv = 𝟙 _ := by
  rw [← cancel_mono (isoOfHom L W (𝟙 X) hX).hom]; rw [Iso.inv_hom_id]; rw [id_comp]; rw [isoOfHom_hom]; rw [Functor.map_id]

variable {W}

/--
lemma `Construction.wIso_eq_isoOfHom` / 引理 `Construction.wIso_eq_isoOfHom`

English:
lemma Construction.wIso_eq_isoOfHom
  given: {X Y : C} (f : X ⟶ Y) (hf : W f)
  proof: by ext; rfl

中文:
引理 Construction.wIso_eq_isoOfHom
  条件: {X Y : C} (f : X ⟶ Y) (hf : W f)
  证明: by ext; rfl
-/
lemma Construction.wIso_eq_isoOfHom {X Y : C} (f : X ⟶ Y) (hf : W f) :
    Construction.wIso f hf = isoOfHom W.Q W f hf := by ext; rfl

/--
lemma `Construction.wInv_eq_isoOfHom_inv` / 引理 `Construction.wInv_eq_isoOfHom_inv`

English:
lemma Construction.wInv_eq_isoOfHom_inv
  given: {X Y : C} (f : X ⟶ Y) (hf : W f)
  proof: congr_arg Iso.inv (wIso_eq_isoOfHom f hf)

中文:
引理 Construction.wInv_eq_isoOfHom_inv
  条件: {X Y : C} (f : X ⟶ Y) (hf : W f)
  证明: congr_arg Iso.inv (wIso_eq_isoOfHom f hf)

Depends on / 依赖: Iso.inv, congr_arg, wIso_eq_isoOfHom
-/
lemma Construction.wInv_eq_isoOfHom_inv {X Y : C} (f : X ⟶ Y) (hf : W f) :
    Construction.wInv f hf = (isoOfHom W.Q W f hf).inv :=
  congr_arg Iso.inv (wIso_eq_isoOfHom f hf)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: (Localization.Construction.lift L (inverts L W)).IsEquivalence
  body: (inferInstance : L.IsLocalization W).isEquivalence

中文:
实例 :
  签名: (Localization.Construction.lift L (inverts L W)).是等价
  定义体: (inferInstance : L.IsLocalization W).isEquivalence

Depends on / 依赖: IsLocalization, L.IsLocalization, isEquivalence
-/
instance : (Localization.Construction.lift L (inverts L W)).IsEquivalence :=
  (inferInstance : L.IsLocalization W).isEquivalence

variable (W)

/--
Definition of `equivalenceFromModel` / `equivalenceFromModel` 的定义

English:
definition equivalenceFromModel
  signature: : W.Localization ≌ D
  body: (Localization.Construction.lift L (inverts L W)).asEquivalence

中文:
定义 equivalenceFromModel
  签名: : W.Localization ≌ D
  定义体: (Localization.Construction.lift L (inverts L W)).asEquivalence

Depends on / 依赖: Construction, Localization, Localization.Construction.lift, asEquivalence, inverts
-/
def equivalenceFromModel : W.Localization ≌ D :=
  (Localization.Construction.lift L (inverts L W)).asEquivalence

/--
Definition of `qCompEquivalenceFromModelFunctorIso` / `qCompEquivalenceFromModelFunctorIso` 的定义

English:
definition qCompEquivalenceFromModelFunctorIso
  signature: : W.Q ⋙ (equivalenceFromModel L W).functor ≅ L
  body: eqToIso (Construction.fac _ _)

中文:
定义 qCompEquivalenceFromModelFunctorIso
  签名: : W.Q ⋙ (equivalenceFromModel L W).functor ≅ L
  定义体: eqToIso (Construction.fac _ _)

Depends on / 依赖: Construction, Construction.fac, eqToIso
-/
def qCompEquivalenceFromModelFunctorIso : W.Q ⋙ (equivalenceFromModel L W).functor ≅ L :=
  eqToIso (Construction.fac _ _)

/--
Definition of `compEquivalenceFromModelInverseIso` / `compEquivalenceFromModelInverseIso` 的定义

English:
definition compEquivalenceFromModelInverseIso
  signature: : L ⋙ (equivalenceFromModel L W).inverse ≅ W.Q
  body: calc
    L ⋙ (equivalenceFromModel L W).inverse ≅ _ :=
      isoWhiskerRight (qCompEquivalenceFromModelFunctorIso L W).symm _
    _ ≅ W.Q ⋙ (equivalenceFromModel L W).functor ⋙ (equivalenceFromModel L W).inverse :=
      (associator _ _ _)
    _ ≅ W.Q ⋙ 𝟭 _ := isoWhiskerLeft _ (equivalenceFromModel L W).unitIso.symm
    _ ≅ W.Q := rightUnitor _

中文:
定义 compEquivalenceFromModelInverseIso
  签名: : L ⋙ (equivalenceFromModel L W).inverse ≅ W.Q
  定义体: calc
    L ⋙ (equivalenceFromModel L W).inverse ≅ _ :=
      isoWhiskerRight (qCompEquivalenceFromModelFunctorIso L W).symm _
    _ ≅ W.Q ⋙ (equivalenceFromModel L W).functor ⋙ (equivalenceFromModel L W).inverse :=
      (associator _ _ _)
    _ ≅ W.Q ⋙ 𝟭 _ := isoWhiskerLeft _ (equivalenceFromModel L W).unitIso.symm
    _ ≅ W.Q := rightUnitor _

Depends on / 依赖: associator, equivalenceFromModel, functor, inverse, isoWhiskerLeft, isoWhiskerRight, qCompEquivalenceFromModelFunctorIso, rightUnitor, unitIso, unitIso.symm
-/
def compEquivalenceFromModelInverseIso : L ⋙ (equivalenceFromModel L W).inverse ≅ W.Q :=
  calc
    L ⋙ (equivalenceFromModel L W).inverse ≅ _ :=
      isoWhiskerRight (qCompEquivalenceFromModelFunctorIso L W).symm _
    _ ≅ W.Q ⋙ (equivalenceFromModel L W).functor ⋙ (equivalenceFromModel L W).inverse :=
      (associator _ _ _)
    _ ≅ W.Q ⋙ 𝟭 _ := isoWhiskerLeft _ (equivalenceFromModel L W).unitIso.symm
    _ ≅ W.Q := rightUnitor _

/--
theorem `essSurj` / 定理 `essSurj`

English:
theorem essSurj
  given: (W) [L.IsLocalization W]
  statement: L.EssSurj
  proof: ⟨fun X =>
    ⟨(Construction.objEquiv W).invFun ((equivalenceFromModel L W).inverse.obj X),
      Nonempty.intro
        ((qCompEquivalenceFromModelFunctorIso L W).symm.app _ ≪≫
          (equivalenceFromModel L W).counitIso.app X)⟩⟩

中文:
定理 essSurj
  条件: (W) [L.是Localization W]
  结论: L.本质满射
  证明: ⟨fun X =>
    ⟨(Construction.objEquiv W).invFun ((equivalenceFromModel L W).inverse.obj X),
      Nonempty.intro
        ((qCompEquivalenceFromModelFunctorIso L W).symm.app _ ≪≫
          (equivalenceFromModel L W).counitIso.app X)⟩⟩

Depends on / 依赖: Construction, Construction.objEquiv, Nonempty, Nonempty.intro, counitIso, counitIso.app, equivalenceFromModel, invFun, inverse, inverse.obj, objEquiv, qCompEquivalenceFromModelFunctorIso, symm.app
-/
theorem essSurj (W) [L.IsLocalization W] : L.EssSurj :=
  ⟨fun X =>
    ⟨(Construction.objEquiv W).invFun ((equivalenceFromModel L W).inverse.obj X),
      Nonempty.intro
        ((qCompEquivalenceFromModelFunctorIso L W).symm.app _ ≪≫
          (equivalenceFromModel L W).counitIso.app X)⟩⟩

/--
Definition of `whiskeringLeftFunctor` / `whiskeringLeftFunctor` 的定义

English:
definition whiskeringLeftFunctor
  signature: : (D ⥤ E) ⥤ W.FunctorsInverting E
  body: ObjectProperty.lift _ ((whiskeringLeft _ _ E).obj L)
    (MorphismProperty.IsInvertedBy.of_comp W L (inverts L W))

中文:
定义 whiskeringLeftFunctor
  签名: : (D ⥤ E) ⥤ W.FunctorsInverting E
  定义体: ObjectProperty.lift _ ((whiskeringLeft _ _ E).obj L)
    (MorphismProperty.IsInvertedBy.of_comp W L (inverts L W))

Depends on / 依赖: IsInvertedBy, MorphismProperty, MorphismProperty.IsInvertedBy.of_comp, ObjectProperty, ObjectProperty.lift, inverts, of_comp, whiskeringLeft
-/
def whiskeringLeftFunctor : (D ⥤ E) ⥤ W.FunctorsInverting E :=
  ObjectProperty.lift _ ((whiskeringLeft _ _ E).obj L)
    (MorphismProperty.IsInvertedBy.of_comp W L (inverts L W))

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: (whiskeringLeftFunctor L W E).IsEquivalence
  body: by
  let iso : (whiskeringLeft (MorphismProperty.Localization W) D E).obj
    (equivalenceFromModel L W).functor ⋙
      (Construction.whiskeringLeftEquivalence W E).functor ≅ whiskeringLeftFunctor L W E :=
    NatIso.ofComponents (fun F => eqToIso (by
      ext
      change (W.Q ⋙ Localization.Construction.lift L (inverts L W)) ⋙ F = L ⋙ F
      rw [Construction.fac])) (fun τ => by
        ext
        dsimp [Construction.whiskeringLeftEquivalence, equivalenceFromModel, whiskerLeft]
        rw [ObjectProperty.eqToHom_hom]; rw [ObjectProperty.eqToHom_hom]; rw [eqToHom_app]; rw [eqToHom_app]; rw [eqToHom_refl]; rw [eqToHom_refl]
        dsimp
        rw [comp_id]; rw [id_comp]
        rfl)
  exact Functor.isEquivalence_of_iso iso

中文:
实例 :
  签名: (whiskeringLeftFunctor L W E).是等价
  定义体: by
  let iso : (whiskeringLeft (MorphismProperty.Localization W) D E).obj
    (equivalenceFromModel L W).functor ⋙
      (Construction.whiskeringLeftEquivalence W E).functor ≅ whiskeringLeftFunctor L W E :=
    NatIso.ofComponents (fun F => eqToIso (by
      ext
      change (W.Q ⋙ Localization.Construction.lift L (inverts L W)) ⋙ F = L ⋙ F
      rw [Construction.fac])) (fun τ => by
        ext
        dsimp [Construction.whiskeringLeftEquivalence, equivalenceFromModel, whiskerLeft]
        rw [ObjectProperty.eqToHom_hom]; rw [ObjectProperty.eqToHom_hom]; rw [eqToHom_app]; rw [eqToHom_app]; rw [eqToHom_refl]; rw [eqToHom_refl]
        dsimp
        rw [comp_id]; rw [id_comp]
        rfl)
  exact Functor.isEquivalence_of_iso iso

Depends on / 依赖: Construction, Construction.fac, Construction.whiskeringLeftEquivalence, Localization, Localization.Construction.lift, MorphismProperty, MorphismProperty.Localization, NatIso, NatIso.ofComponents, ObjectProperty, ObjectProperty.eqToHom_ho, ObjectProperty.eqToHom_hom, eqToHom_ho, eqToHom_hom, eqToIso, equivalenceFromModel, functor, inverts, ofComponents, whiskerLeft
-/
instance : (whiskeringLeftFunctor L W E).IsEquivalence := by
  let iso : (whiskeringLeft (MorphismProperty.Localization W) D E).obj
    (equivalenceFromModel L W).functor ⋙
      (Construction.whiskeringLeftEquivalence W E).functor ≅ whiskeringLeftFunctor L W E :=
    NatIso.ofComponents (fun F => eqToIso (by
      ext
      change (W.Q ⋙ Localization.Construction.lift L (inverts L W)) ⋙ F = L ⋙ F
      rw [Construction.fac])) (fun τ => by
        ext
        dsimp [Construction.whiskeringLeftEquivalence, equivalenceFromModel, whiskerLeft]
        rw [ObjectProperty.eqToHom_hom]; rw [ObjectProperty.eqToHom_hom]; rw [eqToHom_app]; rw [eqToHom_app]; rw [eqToHom_refl]; rw [eqToHom_refl]
        dsimp
        rw [comp_id]; rw [id_comp]
        rfl)
  exact Functor.isEquivalence_of_iso iso

/--
Definition of `functorEquivalence` / `functorEquivalence` 的定义

English:
definition functorEquivalence
  signature: : D ⥤ E ≌ W.FunctorsInverting E
  body: (whiskeringLeftFunctor L W E).asEquivalence

中文:
定义 functorEquivalence
  签名: : D ⥤ E ≌ W.FunctorsInverting E
  定义体: (whiskeringLeftFunctor L W E).asEquivalence

Depends on / 依赖: asEquivalence, whiskeringLeftFunctor
-/
def functorEquivalence : D ⥤ E ≌ W.FunctorsInverting E :=
  (whiskeringLeftFunctor L W E).asEquivalence

set_option linter.overlappingInstances false in
/-- The functor `(D ⥤ E) ⥤ (C ⥤ E)` given by the composition with a localization
functor `L : C ⥤ D` with respect to `W : MorphismProperty C`. -/
@[nolint unusedArguments]
/--
Definition of `whiskeringLeftFunctor'` / `whiskeringLeftFunctor'` 的定义

English:
definition whiskeringLeftFunctor'
  signature: [L.IsLocalization W] (E : Type*) [Category* E]
  body: (whiskeringLeft C D E).obj L

中文:
定义 whiskeringLeftFunctor'
  签名: [L.是Localization W] (E : 类型) [范畴* E]
  定义体: (whiskeringLeft C D E).obj L

Depends on / 依赖: whiskeringLeft
-/
def whiskeringLeftFunctor' [L.IsLocalization W] (E : Type*) [Category* E] :
    (D ⥤ E) ⥤ C ⥤ E :=
  (whiskeringLeft C D E).obj L

/--
theorem `whiskeringLeftFunctor'_eq` / 定理 `whiskeringLeftFunctor'_eq`

English:
theorem whiskeringLeftFunctor'_eq
  proof: rfl

中文:
定理 whiskeringLeftFunctor'_eq
  证明: rfl
-/
theorem whiskeringLeftFunctor'_eq :
    whiskeringLeftFunctor' L W E = Localization.whiskeringLeftFunctor L W E ⋙ inducedFunctor _ :=
  rfl

variable {E} in
@[simp]
/--
theorem `whiskeringLeftFunctor'_obj` / 定理 `whiskeringLeftFunctor'_obj`

English:
theorem whiskeringLeftFunctor'_obj
  given: (F : D ⥤ E)
  statement: (whiskeringLeftFunctor' L W E).obj F = L ⋙ F
  proof: rfl

中文:
定理 whiskeringLeftFunctor'_obj
  条件: (F : D ⥤ E)
  结论: (whiskeringLeftFunctor' L W E).obj F = L ⋙ F
  证明: rfl
-/
theorem whiskeringLeftFunctor'_obj (F : D ⥤ E) : (whiskeringLeftFunctor' L W E).obj F = L ⋙ F :=
  rfl

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: (whiskeringLeftFunctor' L W E).Full
  body: by
  rw [whiskeringLeftFunctor'_eq]
  apply @Functor.Full.comp _ _ _ _ _ _ _ _ ?_ ?_
  · infer_instance
  apply InducedCategory.full -- why is it not found automatically ???

中文:
实例 :
  签名: (whiskeringLeftFunctor' L W E).满
  定义体: by
  rw [whiskeringLeftFunctor'_eq]
  apply @Functor.Full.comp _ _ _ _ _ _ _ _ ?_ ?_
  · infer_instance
  apply InducedCategory.full -- why is it not found automatically ???

Depends on / 依赖: Functor, Functor.Full.comp, InducedCategory, InducedCategory.full, Iso.inv_hom_id_app, Iso.inv_hom_id_app_assoc, _inv_app, automatically, cancel_epi, infer_instance, inv.app, inv_hom_id_app, inv_hom_id_app_assoc, pullbackShiftFunctorZero, shiftFunctorZero, whiskeringLeftFunctor
-/
instance : (whiskeringLeftFunctor' L W E).Full := by
  rw [whiskeringLeftFunctor'_eq]
  apply @Functor.Full.comp _ _ _ _ _ _ _ _ ?_ ?_
  · infer_instance
  apply InducedCategory.full -- why is it not found automatically ???

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: (whiskeringLeftFunctor' L W E).Faithful
  body: by
  rw [whiskeringLeftFunctor'_eq]
  apply @Functor.Faithful.comp _ _ _ _ _ _ _ _ ?_ ?_
  · infer_instance
  apply InducedCategory.faithful -- why is it not found automatically ???

中文:
实例 :
  签名: (whiskeringLeftFunctor' L W E).忠实
  定义体: by
  rw [whiskeringLeftFunctor'_eq]
  apply @Functor.Faithful.comp _ _ _ _ _ _ _ _ ?_ ?_
  · infer_instance
  apply InducedCategory.faithful -- why is it not found automatically ???

Depends on / 依赖: Faithful, Functor, Functor.Faithful.comp, InducedCategory, InducedCategory.faithful, automatically, faithful, infer_instance, whiskeringLeftFunctor
-/
instance : (whiskeringLeftFunctor' L W E).Faithful := by
  rw [whiskeringLeftFunctor'_eq]
  apply @Functor.Faithful.comp _ _ _ _ _ _ _ _ ?_ ?_
  · infer_instance
  apply InducedCategory.faithful -- why is it not found automatically ???

/--
lemma `full_whiskeringLeft` / 引理 `full_whiskeringLeft`

English:
lemma full_whiskeringLeft
  given: (L : C ⥤ D) (W) [L.IsLocalization W] (E : Type*) [Category* E]
  proof: inferInstanceAs (whiskeringLeftFunctor' L W E).Full

中文:
引理 full_whiskeringLeft
  条件: (L : C ⥤ D) (W) [L.是Localization W] (E : 类型) [范畴* E]
  证明: inferInstanceAs (whiskeringLeftFunctor' L W E).Full

Depends on / 依赖: Functor, Functor.map_comp, Functor.map_id, Iso.hom_inv_id_app, Iso.hom_inv_id_app_assoc, Iso.inv_hom_id_app, Iso.inv_hom_id_app_assoc, _inv_app, cancel_epi, hom_inv_id_app, hom_inv_id_app_assoc, inv.app, inv_hom_id_app, inv_hom_id_app_assoc, map_comp, map_id, pullbackShiftFunctorAdd, shiftFunctorAdd, whiskeringLeftFunctor
-/
lemma full_whiskeringLeft (L : C ⥤ D) (W) [L.IsLocalization W] (E : Type*) [Category* E] :
    ((whiskeringLeft C D E).obj L).Full :=
  inferInstanceAs (whiskeringLeftFunctor' L W E).Full

/--
lemma `faithful_whiskeringLeft` / 引理 `faithful_whiskeringLeft`

English:
lemma faithful_whiskeringLeft
  given: (L : C ⥤ D) (W) [L.IsLocalization W] (E : Type*) [Category* E]
  proof: inferInstanceAs (whiskeringLeftFunctor' L W E).Faithful

中文:
引理 faithful_whiskeringLeft
  条件: (L : C ⥤ D) (W) [L.是Localization W] (E : 类型) [范畴* E]
  证明: inferInstanceAs (whiskeringLeftFunctor' L W E).Faithful

Depends on / 依赖: Faithful, whiskeringLeftFunctor
-/
lemma faithful_whiskeringLeft (L : C ⥤ D) (W) [L.IsLocalization W] (E : Type*) [Category* E] :
    ((whiskeringLeft C D E).obj L).Faithful :=
  inferInstanceAs (whiskeringLeftFunctor' L W E).Faithful

/--
Definition of `fullyFaithfulWhiskeringLeft` / `fullyFaithfulWhiskeringLeft` 的定义

English:
definition fullyFaithfulWhiskeringLeft
  signature: (L : C ⥤ D) (W) [L.IsLocalization W] (E : Type*) [Category* E]
  body: by
  have := full_whiskeringLeft L W E
  have := faithful_whiskeringLeft L W E
  exact FullyFaithful.ofFullyFaithful _

中文:
定义 fullyFaithfulWhiskeringLeft
  签名: (L : C ⥤ D) (W) [L.是Localization W] (E : 类型) [范畴* E]
  定义体: by
  have := full_whiskeringLeft L W E
  have := faithful_whiskeringLeft L W E
  exact FullyFaithful.ofFullyFaithful _

Depends on / 依赖: FullyFaithful, FullyFaithful.ofFullyFaithful, faithful_whiskeringLeft, full_whiskeringLeft, ofFullyFaithful
-/
def fullyFaithfulWhiskeringLeft (L : C ⥤ D) (W) [L.IsLocalization W] (E : Type*) [Category* E] :
    ((whiskeringLeft C D E).obj L).FullyFaithful := by
  have := full_whiskeringLeft L W E
  have := faithful_whiskeringLeft L W E
  exact FullyFaithful.ofFullyFaithful _

variable {E}

/--
theorem `natTrans_ext` / 定理 `natTrans_ext`

English:
theorem natTrans_ext
  statement: (L : C ⥤ D) (W) [L.IsLocalization W] {F₁ F₂ : D ⥤ E} {τ τ' : F₁ ⟶ F₂}
  proof: by
  have := essSurj L W
  ext Y
  rw [← cancel_epi (F₁.map (L.objObjPreimageIso Y).hom)]; rw [τ.naturality]; rw [τ'.naturality]; rw [h]

中文:
定理 natTrans_ext
  结论: (L : C ⥤ D) (W) [L.是Localization W] {F₁ F₂ : D ⥤ E} {τ τ' : F₁ ⟶ F₂}
  证明: by
  have := essSurj L W
  ext Y
  rw [← cancel_epi (F₁.map (L.objObjPreimageIso Y).hom)]; rw [τ.naturality]; rw [τ'.naturality]; rw [h]

Depends on / 依赖: L.objObjPreimageIso, cancel_epi, essSurj, naturality, objObjPreimageIso
-/
theorem natTrans_ext (L : C ⥤ D) (W) [L.IsLocalization W] {F₁ F₂ : D ⥤ E} {τ τ' : F₁ ⟶ F₂}
    (h : forall X : C, τ.app (L.obj X) = τ'.app (L.obj X)) : τ = τ' := by
  have := essSurj L W
  ext Y
  rw [← cancel_epi (F₁.map (L.objObjPreimageIso Y).hom)]; rw [τ.naturality]; rw [τ'.naturality]; rw [h]

/--
Definition of `Lifting` / `Lifting` 的定义

English:
class Lifting
  parameters: (L : C ⥤ D) (W : MorphismProperty C) (F : C ⥤ E) (F' : D ⥤ E)
  axioms and operations (1):
    - iso((L W F F')) : L ⋙ F' ≅ F

中文:
类 提升
  参数: (L : C ⥤ D) (W : MorphismProperty C) (F : C ⥤ E) (F' : D ⥤ E)
  公理与运算 (1 个):
    - iso((L W F F')) : L ⋙ F' ≅ F
-/
class Lifting (L : C ⥤ D) (W : MorphismProperty C) (F : C ⥤ E) (F' : D ⥤ E) where
  /-- the isomorphism relating the localization functor and the two other given functors -/
  iso (L W F F') : L ⋙ F' ≅ F

variable {W}

/--
Definition of `lift` / `lift` 的定义

English:
definition lift
  signature: (F : C ⥤ E) (hF : W.IsInvertedBy F) (L : C ⥤ D) [L.IsLocalization W]
  body: (functorEquivalence L W E).inverse.obj ⟨F, hF⟩

中文:
定义 lift
  签名: (F : C ⥤ E) (hF : W.IsInvertedBy F) (L : C ⥤ D) [L.是Localization W]
  定义体: (functorEquivalence L W E).inverse.obj ⟨F, hF⟩

Depends on / 依赖: functorEquivalence, inverse, inverse.obj
-/
def lift (F : C ⥤ E) (hF : W.IsInvertedBy F) (L : C ⥤ D) [L.IsLocalization W] : D ⥤ E :=
  (functorEquivalence L W E).inverse.obj ⟨F, hF⟩

/--
Instance `liftingLift` / 实例 `liftingLift`

English:
instance liftingLift
  signature: (F : C ⥤ E) (hF : W.IsInvertedBy F) (L : C ⥤ D) [L.IsLocalization W]
  body: ⟨(inducedFunctor _).mapIso ((functorEquivalence L W E).counitIso.app ⟨F, hF⟩)⟩

中文:
实例 liftingLift
  签名: (F : C ⥤ E) (hF : W.IsInvertedBy F) (L : C ⥤ D) [L.是Localization W]
  定义体: ⟨(inducedFunctor _).mapIso ((functorEquivalence L W E).counitIso.app ⟨F, hF⟩)⟩

Depends on / 依赖: counitIso, counitIso.app, functorEquivalence, inducedFunctor, mapIso
-/
instance liftingLift (F : C ⥤ E) (hF : W.IsInvertedBy F) (L : C ⥤ D) [L.IsLocalization W] :
    Lifting L W F (lift F hF L) :=
  ⟨(inducedFunctor _).mapIso ((functorEquivalence L W E).counitIso.app ⟨F, hF⟩)⟩

/--
Definition of `fac` / `fac` 的定义

English:
definition fac
  signature: (F : C ⥤ E) (hF : W.IsInvertedBy F) (L : C ⥤ D) [L.IsLocalization W]
  body: Lifting.iso L W F _

中文:
定义 fac
  签名: (F : C ⥤ E) (hF : W.IsInvertedBy F) (L : C ⥤ D) [L.是Localization W]
  定义体: Lifting.iso L W F _

Depends on / 依赖: Lifting, Lifting.iso
-/
def fac (F : C ⥤ E) (hF : W.IsInvertedBy F) (L : C ⥤ D) [L.IsLocalization W] :
    L ⋙ lift F hF L ≅ F :=
  Lifting.iso L W F _

/--
Instance `liftingConstructionLift` / 实例 `liftingConstructionLift`

English:
instance liftingConstructionLift
  signature: (F : C ⥤ D) (hF : W.IsInvertedBy F)
  body: ⟨eqToIso (Construction.fac F hF)⟩

中文:
实例 liftingConstructionLift
  签名: (F : C ⥤ D) (hF : W.IsInvertedBy F)
  定义体: ⟨eqToIso (Construction.fac F hF)⟩

Depends on / 依赖: Construction, Construction.fac, eqToIso
-/
instance liftingConstructionLift (F : C ⥤ D) (hF : W.IsInvertedBy F) :
    Lifting W.Q W F (Construction.lift F hF) :=
  ⟨eqToIso (Construction.fac F hF)⟩

variable (W)

/--
Definition of `liftNatTrans` / `liftNatTrans` 的定义

English:
definition liftNatTrans
  signature: (F₁ F₂ : C ⥤ E) (F₁' F₂' : D ⥤ E) [Lifting L W F₁ F₁'] [Lifting L W F₂ F₂']
  body: (whiskeringLeftFunctor' L W E).preimage
    ((Lifting.iso L W F₁ F₁').hom ≫ τ ≫ (Lifting.iso L W F₂ F₂').inv)

@[simp]

中文:
定义 lift自然数Trans
  签名: (F₁ F₂ : C ⥤ E) (F₁' F₂' : D ⥤ E) [提升 L W F₁ F₁'] [提升 L W F₂ F₂']
  定义体: (whiskeringLeftFunctor' L W E).preimage
    ((Lifting.iso L W F₁ F₁').hom ≫ τ ≫ (Lifting.iso L W F₂ F₂').inv)

@[simp]

Depends on / 依赖: Lifting, Lifting.iso, preimage, whiskeringLeftFunctor
-/
def liftNatTrans (F₁ F₂ : C ⥤ E) (F₁' F₂' : D ⥤ E) [Lifting L W F₁ F₁'] [Lifting L W F₂ F₂']
    (τ : F₁ ⟶ F₂) : F₁' ⟶ F₂' :=
  (whiskeringLeftFunctor' L W E).preimage
    ((Lifting.iso L W F₁ F₁').hom ≫ τ ≫ (Lifting.iso L W F₂ F₂').inv)

@[simp]
/--
theorem `liftNatTrans_app` / 定理 `liftNatTrans_app`

English:
theorem liftNatTrans_app
  statement: (F₁ F₂ : C ⥤ E) (F₁' F₂' : D ⥤ E) [Lifting L W F₁ F₁'] [Lifting L W F₂ F₂']
  proof: congr_app (Functor.map_preimage (whiskeringLeftFunctor' L W E) _) X

@[reassoc (attr := simp)]

中文:
定理 lift自然数Trans_app
  结论: (F₁ F₂ : C ⥤ E) (F₁' F₂' : D ⥤ E) [提升 L W F₁ F₁'] [提升 L W F₂ F₂']
  证明: congr_app (Functor.map_preimage (whiskeringLeftFunctor' L W E) _) X

@[reassoc (attr := simp)]

Depends on / 依赖: Functor, Functor.map_preimage, congr_app, map_preimage, whiskeringLeftFunctor
-/
theorem liftNatTrans_app (F₁ F₂ : C ⥤ E) (F₁' F₂' : D ⥤ E) [Lifting L W F₁ F₁'] [Lifting L W F₂ F₂']
    (τ : F₁ ⟶ F₂) (X : C) :
    (liftNatTrans L W F₁ F₂ F₁' F₂' τ).app (L.obj X) =
      (Lifting.iso L W F₁ F₁').hom.app X ≫ τ.app X ≫ (Lifting.iso L W F₂ F₂').inv.app X :=
  congr_app (Functor.map_preimage (whiskeringLeftFunctor' L W E) _) X

@[reassoc (attr := simp)]
/--
theorem `comp_liftNatTrans` / 定理 `comp_liftNatTrans`

English:
theorem comp_liftNatTrans
  statement: (F₁ F₂ F₃ : C ⥤ E) (F₁' F₂' F₃' : D ⥤ E) [h₁ : Lifting L W F₁ F₁']
  proof: natTrans_ext L W fun X => by
    simp only [NatTrans.comp_app, liftNatTrans_app, assoc, Iso.inv_hom_id_app_assoc]

@[simp]

中文:
定理 comp_lift自然数Trans
  结论: (F₁ F₂ F₃ : C ⥤ E) (F₁' F₂' F₃' : D ⥤ E) [h₁ : 提升 L W F₁ F₁']
  证明: natTrans_ext L W fun X => by
    simp only [NatTrans.comp_app, liftNatTrans_app, assoc, Iso.inv_hom_id_app_assoc]

@[simp]

Depends on / 依赖: Iso.inv_hom_id_app_assoc, NatTrans, NatTrans.comp_app, comp_app, inv_hom_id_app_assoc, liftNatTrans_app, natTrans_ext
-/
theorem comp_liftNatTrans (F₁ F₂ F₃ : C ⥤ E) (F₁' F₂' F₃' : D ⥤ E) [h₁ : Lifting L W F₁ F₁']
    [h₂ : Lifting L W F₂ F₂'] [h₃ : Lifting L W F₃ F₃'] (τ : F₁ ⟶ F₂) (τ' : F₂ ⟶ F₃) :
    liftNatTrans L W F₁ F₂ F₁' F₂' τ ≫ liftNatTrans L W F₂ F₃ F₂' F₃' τ' =
      liftNatTrans L W F₁ F₃ F₁' F₃' (τ ≫ τ') :=
  natTrans_ext L W fun X => by
    simp only [NatTrans.comp_app, liftNatTrans_app, assoc, Iso.inv_hom_id_app_assoc]

@[simp]
/--
theorem `liftNatTrans_id` / 定理 `liftNatTrans_id`

English:
theorem liftNatTrans_id
  given: (F : C ⥤ E) (F' : D ⥤ E) [h : Lifting L W F F']
  proof: natTrans_ext L W fun X => by
    simp only [liftNatTrans_app, NatTrans.id_app, id_comp, Iso.hom_inv_id_app]
    rfl

中文:
定理 lift自然数Trans_id
  条件: (F : C ⥤ E) (F' : D ⥤ E) [h : 提升 L W F F']
  证明: natTrans_ext L W fun X => by
    simp only [liftNatTrans_app, NatTrans.id_app, id_comp, Iso.hom_inv_id_app]
    rfl

Depends on / 依赖: Iso.hom_inv_id_app, NatTrans, NatTrans.id_app, hom_inv_id_app, id_app, id_comp, liftNatTrans_app, natTrans_ext
-/
theorem liftNatTrans_id (F : C ⥤ E) (F' : D ⥤ E) [h : Lifting L W F F'] :
    liftNatTrans L W F F F' F' (𝟙 F) = 𝟙 F' :=
  natTrans_ext L W fun X => by
    simp only [liftNatTrans_app, NatTrans.id_app, id_comp, Iso.hom_inv_id_app]
    rfl

/-- Given a localization functor `L : C ⥤ D` for `W : MorphismProperty C`,
if `(F₁' F₂' : D ⥤ E)` are functors which lift functors `(F₁ F₂ : C ⥤ E)`,
a natural isomorphism `τ : F₁ ⟶ F₂` lifts to a natural isomorphism `F₁' ⟶ F₂'`. -/
@[simps]
/--
Definition of `liftNatIso` / `liftNatIso` 的定义

English:
definition liftNatIso
  signature: (F₁ F₂ : C ⥤ E) (F₁' F₂' : D ⥤ E) [h₁ : Lifting L W F₁ F₁'] [h₂ : Lifting L W F₂ F₂']
  body: liftNatTrans L W F₁ F₂ F₁' F₂' e.hom
  inv := liftNatTrans L W F₂ F₁ F₂' F₁' e.inv

中文:
定义 lift自然数Iso
  签名: (F₁ F₂ : C ⥤ E) (F₁' F₂' : D ⥤ E) [h₁ : 提升 L W F₁ F₁'] [h₂ : 提升 L W F₂ F₂']
  定义体: liftNatTrans L W F₁ F₂ F₁' F₂' e.hom
  inv := liftNatTrans L W F₂ F₁ F₂' F₁' e.inv

Depends on / 依赖: e.hom, liftNatTrans
-/
def liftNatIso (F₁ F₂ : C ⥤ E) (F₁' F₂' : D ⥤ E) [h₁ : Lifting L W F₁ F₁'] [h₂ : Lifting L W F₂ F₂']
    (e : F₁ ≅ F₂) : F₁' ≅ F₂' where
  hom := liftNatTrans L W F₁ F₂ F₁' F₂' e.hom
  inv := liftNatTrans L W F₂ F₁ F₂' F₁' e.inv

namespace Lifting

@[simps]
/--
Instance `compRight` / 实例 `compRight`

English:
instance compRight
  signature: {E' : Type*} [Category* E'] (F : C ⥤ E) (F' : D ⥤ E) [Lifting L W F F']
  body: ⟨isoWhiskerRight (iso L W F F') G⟩

@[simps]

中文:
实例 compRight
  签名: {E' : 类型} [范畴* E'] (F : C ⥤ E) (F' : D ⥤ E) [提升 L W F F']
  定义体: ⟨isoWhiskerRight (iso L W F F') G⟩

@[simps]

Depends on / 依赖: isoWhiskerRight
-/
instance compRight {E' : Type*} [Category* E'] (F : C ⥤ E) (F' : D ⥤ E) [Lifting L W F F']
    (G : E ⥤ E') : Lifting L W (F ⋙ G) (F' ⋙ G) :=
  ⟨isoWhiskerRight (iso L W F F') G⟩

@[simps]
/--
Instance `id` / 实例 `id`

English:
instance id
  signature: : Lifting L W L (𝟭 D)
  body: ⟨rightUnitor L⟩

@[simps]

中文:
实例 id
  签名: : 提升 L W L (𝟭 D)
  定义体: ⟨rightUnitor L⟩

@[simps]

Depends on / 依赖: rightUnitor
-/
instance id : Lifting L W L (𝟭 D) :=
  ⟨rightUnitor L⟩

@[simps]
/--
Instance `compLeft` / 实例 `compLeft`

English:
instance compLeft
  signature: (F : D ⥤ E)
  body: ⟨Iso.refl _⟩

中文:
实例 compLeft
  签名: (F : D ⥤ E)
  定义体: ⟨Iso.refl _⟩

Depends on / 依赖: Iso.refl
-/
instance compLeft (F : D ⥤ E) : Localization.Lifting L W (L ⋙ F) F := ⟨Iso.refl _⟩

/-- Given a localization functor `L : C ⥤ D` for `W : MorphismProperty C`,
if `F₁' : D ⥤ E` lifts a functor `F₁ : C ⥤ D`, then a functor `F₂'` which
is isomorphic to `F₁'` also lifts a functor `F₂` that is isomorphic to `F₁`. -/
@[simps, instance_reducible]
/--
Definition of `ofIsos` / `ofIsos` 的定义

English:
definition ofIsos
  signature: {F₁ F₂ : C ⥤ E} {F₁' F₂' : D ⥤ E} (e : F₁ ≅ F₂) (e' : F₁' ≅ F₂') [Lifting L W F₁ F₁']
  body: ⟨isoWhiskerLeft L e'.symm ≪≫ iso L W F₁ F₁' ≪≫ e⟩

中文:
定义 ofIsos
  签名: {F₁ F₂ : C ⥤ E} {F₁' F₂' : D ⥤ E} (e : F₁ ≅ F₂) (e' : F₁' ≅ F₂') [提升 L W F₁ F₁']
  定义体: ⟨isoWhiskerLeft L e'.symm ≪≫ iso L W F₁ F₁' ≪≫ e⟩

Depends on / 依赖: isoWhiskerLeft
-/
def ofIsos {F₁ F₂ : C ⥤ E} {F₁' F₂' : D ⥤ E} (e : F₁ ≅ F₂) (e' : F₁' ≅ F₂') [Lifting L W F₁ F₁'] :
    Lifting L W F₂ F₂' :=
  ⟨isoWhiskerLeft L e'.symm ≪≫ iso L W F₁ F₁' ≪≫ e⟩

end Lifting

end Localization

namespace Functor

namespace IsLocalization

open Localization

/--
theorem `of_iso` / 定理 `of_iso`

English:
theorem of_iso
  given: {L₁ L₂ : C ⥤ D} (e : L₁ ≅ L₂) [L₁.IsLocalization W]
  statement: L₂.IsLocalization W
  proof: by
  have h := Localization.inverts L₁ W
  rw [MorphismProperty.IsInvertedBy.iff_of_iso W e] at h
  let F₁ := Localization.Construction.lift L₁ (Localization.inverts L₁ W)
  let F₂ := Localization.Construction.lift L₂ h
  exact
    { inverts := h
      isEquivalence := Functor.isEquivalence_of_iso (liftNatIso W.Q W L₁ L₂ F₁ F₂ e) }

中文:
定理 of_iso
  条件: {L₁ L₂ : C ⥤ D} (e : L₁ ≅ L₂) [L₁.是Localization W]
  结论: L₂.是Localization W
  证明: by
  have h := Localization.inverts L₁ W
  rw [MorphismProperty.IsInvertedBy.iff_of_iso W e] at h
  let F₁ := Localization.Construction.lift L₁ (Localization.inverts L₁ W)
  let F₂ := Localization.Construction.lift L₂ h
  exact
    { inverts := h
      isEquivalence := Functor.isEquivalence_of_iso (liftNatIso W.Q W L₁ L₂ F₁ F₂ e) }

Depends on / 依赖: Construction, Functor, Functor.isEquivalence_of_iso, IsInvertedBy, Localization, Localization.Construction.lift, Localization.inverts, MorphismProperty, MorphismProperty.IsInvertedBy.iff_of_iso, iff_of_iso, inverts, isEquivalence, isEquivalence_of_iso, liftNatIso
-/
theorem of_iso {L₁ L₂ : C ⥤ D} (e : L₁ ≅ L₂) [L₁.IsLocalization W] : L₂.IsLocalization W := by
  have h := Localization.inverts L₁ W
  rw [MorphismProperty.IsInvertedBy.iff_of_iso W e] at h
  let F₁ := Localization.Construction.lift L₁ (Localization.inverts L₁ W)
  let F₂ := Localization.Construction.lift L₂ h
  exact
    { inverts := h
      isEquivalence := Functor.isEquivalence_of_iso (liftNatIso W.Q W L₁ L₂ F₁ F₂ e) }

/--
theorem `of_equivalence_target` / 定理 `of_equivalence_target`

English:
theorem of_equivalence_target
  statement: {E : Type*} [Category* E] (L' : C ⥤ E) (eq : D ≌ E)
  proof: by
  have h : W.IsInvertedBy L' := by
    rw [← MorphismProperty.IsInvertedBy.iff_of_iso W e]
    exact MorphismProperty.IsInvertedBy.of_comp W L (Localization.inverts L W) eq.functor
  let F₁ := Localization.Construction.lift L (Localization.inverts L W)
  let F₂ := Localization.Construction.lift L' h
  let e' : F₁ ⋙ eq.functor ≅ F₂ := liftNatIso W.Q W (L ⋙ eq.functor) L' _ _ e
  exact
    { inverts := h
      isEquivalence := Functor.isEquivalence_of_iso e' }

中文:
定理 of_equivalence_target
  结论: {E : 类型} [范畴* E] (L' : C ⥤ E) (eq : D ≌ E)
  证明: by
  have h : W.IsInvertedBy L' := by
    rw [← MorphismProperty.IsInvertedBy.iff_of_iso W e]
    exact MorphismProperty.IsInvertedBy.of_comp W L (Localization.inverts L W) eq.functor
  let F₁ := Localization.Construction.lift L (Localization.inverts L W)
  let F₂ := Localization.Construction.lift L' h
  let e' : F₁ ⋙ eq.functor ≅ F₂ := liftNatIso W.Q W (L ⋙ eq.functor) L' _ _ e
  exact
    { inverts := h
      isEquivalence := Functor.isEquivalence_of_iso e' }

Depends on / 依赖: Construction, Functor, Functor.isEquivalence_of_iso, IsInvertedBy, Localization, Localization.Construction.lift, Localization.inverts, MorphismProperty, MorphismProperty.IsInvertedBy.iff_of_iso, MorphismProperty.IsInvertedBy.of_comp, W.IsInvertedBy, eq.functor, functor, iff_of_iso, inverts, isEquivalence, isEquivalence_of_iso, liftNatIso, of_comp
-/
theorem of_equivalence_target {E : Type*} [Category* E] (L' : C ⥤ E) (eq : D ≌ E)
    [L.IsLocalization W] (e : L ⋙ eq.functor ≅ L') : L'.IsLocalization W := by
  have h : W.IsInvertedBy L' := by
    rw [← MorphismProperty.IsInvertedBy.iff_of_iso W e]
    exact MorphismProperty.IsInvertedBy.of_comp W L (Localization.inverts L W) eq.functor
  let F₁ := Localization.Construction.lift L (Localization.inverts L W)
  let F₂ := Localization.Construction.lift L' h
  let e' : F₁ ⋙ eq.functor ≅ F₂ := liftNatIso W.Q W (L ⋙ eq.functor) L' _ _ e
  exact
    { inverts := h
      isEquivalence := Functor.isEquivalence_of_iso e' }

instance (F : D ⥤ E) [F.IsEquivalence] [L.IsLocalization W] :
    (L ⋙ F).IsLocalization W :=
  of_equivalence_target L W _ F.asEquivalence (Iso.refl _)

/--
lemma `of_isEquivalence` / 引理 `of_isEquivalence`

English:
lemma of_isEquivalence
  statement: (L : C ⥤ D) (W : MorphismProperty C)
  proof: by
  have : (𝟭 C).IsLocalization W := for_id W hW
  exact of_equivalence_target (𝟭 C) W L L.asEquivalence L.leftUnitor

中文:
引理 of_isEquivalence
  结论: (L : C ⥤ D) (W : MorphismProperty C)
  证明: by
  have : (𝟭 C).IsLocalization W := for_id W hW
  exact of_equivalence_target (𝟭 C) W L L.asEquivalence L.leftUnitor

Depends on / 依赖: IsLocalization, L.asEquivalence, L.leftUnitor, asEquivalence, for_id, leftUnitor, of_equivalence_target
-/
lemma of_isEquivalence (L : C ⥤ D) (W : MorphismProperty C)
    (hW : W <= MorphismProperty.isomorphisms C) [IsEquivalence L] :
    L.IsLocalization W := by
  have : (𝟭 C).IsLocalization W := for_id W hW
  exact of_equivalence_target (𝟭 C) W L L.asEquivalence L.leftUnitor

end IsLocalization

end Functor

namespace Localization

variable {D₁ D₂ : Type _} [Category* D₁] [Category* D₂] (L₁ : C ⥤ D₁) (L₂ : C ⥤ D₂)
  (W' : MorphismProperty C) [L₁.IsLocalization W'] [L₂.IsLocalization W']

/--
Definition of `uniq` / `uniq` 的定义

English:
definition uniq
  signature: : D₁ ≌ D₂
  body: (equivalenceFromModel L₁ W').symm.trans (equivalenceFromModel L₂ W')

中文:
定义 uniq
  签名: : D₁ ≌ D₂
  定义体: (equivalenceFromModel L₁ W').symm.trans (equivalenceFromModel L₂ W')

Depends on / 依赖: equivalenceFromModel, symm.trans
-/
def uniq : D₁ ≌ D₂ :=
  (equivalenceFromModel L₁ W').symm.trans (equivalenceFromModel L₂ W')

set_option backward.isDefEq.respectTransparency.types false in
/--
lemma `uniq_symm` / 引理 `uniq_symm`

English:
lemma uniq_symm
  statement: (uniq L₁ L₂ W').symm = uniq L₂ L₁ W'
  proof: by
  dsimp [uniq, Equivalence.trans]
  ext <;> aesop

中文:
引理 uniq_symm
  结论: (uniq L₁ L₂ W').symm = uniq L₂ L₁ W'
  证明: by
  dsimp [uniq, Equivalence.trans]
  ext <;> aesop

Depends on / 依赖: Equivalence, Equivalence.trans
-/
lemma uniq_symm : (uniq L₁ L₂ W').symm = uniq L₂ L₁ W' := by
  dsimp [uniq, Equivalence.trans]
  ext <;> aesop

/--
Definition of `compUniqFunctor` / `compUniqFunctor` 的定义

English:
definition compUniqFunctor
  signature: : L₁ ⋙ (uniq L₁ L₂ W').functor ≅ L₂
  body: calc
    L₁ ⋙ (uniq L₁ L₂ W').functor ≅ (L₁ ⋙ (equivalenceFromModel L₁ W').inverse) ⋙
      (equivalenceFromModel L₂ W').functor := (associator _ _ _).symm
    _ ≅ W'.Q ⋙ (equivalenceFromModel L₂ W').functor :=
      isoWhiskerRight (compEquivalenceFromModelInverseIso L₁ W') _
    _ ≅ L₂ := qCompEquivalenceFromModelFunctorIso L₂ W'

中文:
定义 compUniqFunctor
  签名: : L₁ ⋙ (uniq L₁ L₂ W').functor ≅ L₂
  定义体: calc
    L₁ ⋙ (uniq L₁ L₂ W').functor ≅ (L₁ ⋙ (equivalenceFromModel L₁ W').inverse) ⋙
      (equivalenceFromModel L₂ W').functor := (associator _ _ _).symm
    _ ≅ W'.Q ⋙ (equivalenceFromModel L₂ W').functor :=
      isoWhiskerRight (compEquivalenceFromModelInverseIso L₁ W') _
    _ ≅ L₂ := qCompEquivalenceFromModelFunctorIso L₂ W'

Depends on / 依赖: associator, compEquivalenceFromModelInverseIso, equivalenceFromModel, functor, inverse, isoWhiskerRight, qCompEquivalenceFromModelFunctorIso
-/
def compUniqFunctor : L₁ ⋙ (uniq L₁ L₂ W').functor ≅ L₂ :=
  calc
    L₁ ⋙ (uniq L₁ L₂ W').functor ≅ (L₁ ⋙ (equivalenceFromModel L₁ W').inverse) ⋙
      (equivalenceFromModel L₂ W').functor := (associator _ _ _).symm
    _ ≅ W'.Q ⋙ (equivalenceFromModel L₂ W').functor :=
      isoWhiskerRight (compEquivalenceFromModelInverseIso L₁ W') _
    _ ≅ L₂ := qCompEquivalenceFromModelFunctorIso L₂ W'

/--
Definition of `compUniqInverse` / `compUniqInverse` 的定义

English:
definition compUniqInverse
  signature: : L₂ ⋙ (uniq L₁ L₂ W').inverse ≅ L₁
  body: compUniqFunctor L₂ L₁ W'

中文:
定义 compUniqInverse
  签名: : L₂ ⋙ (uniq L₁ L₂ W').inverse ≅ L₁
  定义体: compUniqFunctor L₂ L₁ W'

Depends on / 依赖: compUniqFunctor
-/
def compUniqInverse : L₂ ⋙ (uniq L₁ L₂ W').inverse ≅ L₁ := compUniqFunctor L₂ L₁ W'

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Lifting L₁ W' L₂ (uniq L₁ L₂ W').functor
  body: ⟨compUniqFunctor L₁ L₂ W'⟩

中文:
实例 :
  签名: 提升 L₁ W' L₂ (uniq L₁ L₂ W').functor
  定义体: ⟨compUniqFunctor L₁ L₂ W'⟩

Depends on / 依赖: compUniqFunctor
-/
instance : Lifting L₁ W' L₂ (uniq L₁ L₂ W').functor := ⟨compUniqFunctor L₁ L₂ W'⟩
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Lifting L₂ W' L₁ (uniq L₁ L₂ W').inverse
  body: ⟨compUniqInverse L₁ L₂ W'⟩

中文:
实例 :
  签名: 提升 L₂ W' L₁ (uniq L₁ L₂ W').inverse
  定义体: ⟨compUniqInverse L₁ L₂ W'⟩

Depends on / 依赖: compUniqInverse
-/
instance : Lifting L₂ W' L₁ (uniq L₁ L₂ W').inverse := ⟨compUniqInverse L₁ L₂ W'⟩

/--
Definition of `isoUniqFunctor` / `isoUniqFunctor` 的定义

English:
definition isoUniqFunctor
  signature: (F : D₁ ⥤ D₂) (e : L₁ ⋙ F ≅ L₂)
  body: letI : Lifting L₁ W' L₂ F := ⟨e⟩
  liftNatIso L₁ W' L₂ L₂ F (uniq L₁ L₂ W').functor (Iso.refl L₂)

中文:
定义 isoUniqFunctor
  签名: (F : D₁ ⥤ D₂) (e : L₁ ⋙ F ≅ L₂)
  定义体: letI : Lifting L₁ W' L₂ F := ⟨e⟩
  liftNatIso L₁ W' L₂ L₂ F (uniq L₁ L₂ W').functor (Iso.refl L₂)

Depends on / 依赖: Iso.refl, Lifting, functor, liftNatIso
-/
def isoUniqFunctor (F : D₁ ⥤ D₂) (e : L₁ ⋙ F ≅ L₂) :
    F ≅ (uniq L₁ L₂ W').functor :=
  letI : Lifting L₁ W' L₂ F := ⟨e⟩
  liftNatIso L₁ W' L₂ L₂ F (uniq L₁ L₂ W').functor (Iso.refl L₂)

set_option backward.defeqAttrib.useBackward true in
/--
lemma `morphismProperty_eq_top` / 引理 `morphismProperty_eq_top`

English:
lemma morphismProperty_eq_top
  statement: [L.IsLocalization W] (P : MorphismProperty D) [P.RespectsIso]
  proof: by
  let e := compUniqFunctor W.Q L W
  have hP : P.inverseImage (uniq W.Q L W).functor = ⊤ :=
    Construction.morphismProperty_eq_top _
      (fun _ _ f => (P.arrow_mk_iso_iff
        (((Functor.mapArrowFunctor _ _).mapIso e).app (Arrow.mk f))).2 (h₁ f))
      (fun X Y f hf => by
        refine (P.arrow_mk_iso_iff (Arrow.isoMk (e.app _) (e.app _) ?_)).2 (h₂ f hf)
        dsimp
        rw [Construction.wInv_eq_isoOfHom_inv]; rw [← cancel_mono (isoOfHom L W f hf).hom]; rw [assoc]; rw [assoc]; rw [Iso.inv_hom_id]; rw [comp_id]; rw [isoOfHom_hom]; rw [← NatTrans.naturality]; rw [Functor.comp_map]; rw [← Functor.map_comp_assoc]; rw [isoOfHom_inv_hom_id]; rw [map_id]; rw [id_comp])
  rw [← P.map_inverseImage_eq_of_isEquivalence (uniq W.Q L W).functor]; rw [hP]; rw [MorphismProperty.map_top_eq_top_of_essSurj_of_full]

中文:
引理 morphismProperty_eq_top
  结论: [L.是Localization W] (P : MorphismProperty D) [P.RespectsIso]
  证明: by
  let e := compUniqFunctor W.Q L W
  have hP : P.inverseImage (uniq W.Q L W).functor = ⊤ :=
    Construction.morphismProperty_eq_top _
      (fun _ _ f => (P.arrow_mk_iso_iff
        (((Functor.mapArrowFunctor _ _).mapIso e).app (Arrow.mk f))).2 (h₁ f))
      (fun X Y f hf => by
        refine (P.arrow_mk_iso_iff (Arrow.isoMk (e.app _) (e.app _) ?_)).2 (h₂ f hf)
        dsimp
        rw [Construction.wInv_eq_isoOfHom_inv]; rw [← cancel_mono (isoOfHom L W f hf).hom]; rw [assoc]; rw [assoc]; rw [Iso.inv_hom_id]; rw [comp_id]; rw [isoOfHom_hom]; rw [← NatTrans.naturality]; rw [Functor.comp_map]; rw [← Functor.map_comp_assoc]; rw [isoOfHom_inv_hom_id]; rw [map_id]; rw [id_comp])
  rw [← P.map_inverseImage_eq_of_isEquivalence (uniq W.Q L W).functor]; rw [hP]; rw [MorphismProperty.map_top_eq_top_of_essSurj_of_full]

Depends on / 依赖: Arrow.isoMk, Arrow.mk, Construction, Construction.morphismProperty_eq_top, Construction.wInv_eq_isoOfHom_inv, Functor, Functor.mapArrowFunctor, Iso.inv_hom_id, P.arrow_mk_iso_iff, P.inverseImage, arrow_mk_iso_iff, cancel_mono, compUniqFunctor, comp_id, e.app, functor, inv_hom_id, inverseImage, isoOfHom, isoOfHom_hom
-/
lemma morphismProperty_eq_top [L.IsLocalization W] (P : MorphismProperty D) [P.RespectsIso]
    [P.IsMultiplicative] (h₁ : forall ⦃X Y : C⦄ (f : X ⟶ Y), P (L.map f))
    (h₂ : forall ⦃X Y : C⦄ (f : X ⟶ Y) (hf : W f), P (isoOfHom L W f hf).inv) :
    P = ⊤ := by
  let e := compUniqFunctor W.Q L W
  have hP : P.inverseImage (uniq W.Q L W).functor = ⊤ :=
    Construction.morphismProperty_eq_top _
      (fun _ _ f => (P.arrow_mk_iso_iff
        (((Functor.mapArrowFunctor _ _).mapIso e).app (Arrow.mk f))).2 (h₁ f))
      (fun X Y f hf => by
        refine (P.arrow_mk_iso_iff (Arrow.isoMk (e.app _) (e.app _) ?_)).2 (h₂ f hf)
        dsimp
        rw [Construction.wInv_eq_isoOfHom_inv]; rw [← cancel_mono (isoOfHom L W f hf).hom]; rw [assoc]; rw [assoc]; rw [Iso.inv_hom_id]; rw [comp_id]; rw [isoOfHom_hom]; rw [← NatTrans.naturality]; rw [Functor.comp_map]; rw [← Functor.map_comp_assoc]; rw [isoOfHom_inv_hom_id]; rw [map_id]; rw [id_comp])
  rw [← P.map_inverseImage_eq_of_isEquivalence (uniq W.Q L W).functor]; rw [hP]; rw [MorphismProperty.map_top_eq_top_of_essSurj_of_full]

/--
lemma `isGroupoid` / 引理 `isGroupoid`

English:
lemma isGroupoid
  given: [L.IsLocalization ⊤]
  proof: by
  rw [isGroupoid_iff_isomorphisms_eq_top]
  exact morphismProperty_eq_top L ⊤ _
    (fun _ _ f => inverts L ⊤ _ (by simp))
    (fun _ _ f hf => Iso.isIso_inv _)

中文:
引理 isGroupoid
  条件: [L.是Localization ⊤]
  证明: by
  rw [isGroupoid_iff_isomorphisms_eq_top]
  exact morphismProperty_eq_top L ⊤ _
    (fun _ _ f => inverts L ⊤ _ (by simp))
    (fun _ _ f hf => Iso.isIso_inv _)

Depends on / 依赖: Iso.isIso_inv, inverts, isGroupoid_iff_isomorphisms_eq_top, isIso_inv, morphismProperty_eq_top
-/
lemma isGroupoid [L.IsLocalization ⊤] :
    IsGroupoid D := by
  rw [isGroupoid_iff_isomorphisms_eq_top]
  exact morphismProperty_eq_top L ⊤ _
    (fun _ _ f => inverts L ⊤ _ (by simp))
    (fun _ _ f hf => Iso.isIso_inv _)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: IsGroupoid (⊤ : MorphismProperty C).Localization
  body: isGroupoid MorphismProperty.Q ⊤

中文:
实例 :
  签名: 是群胚 (⊤ : MorphismProperty C).Localization
  定义体: isGroupoid MorphismProperty.Q ⊤

Depends on / 依赖: MorphismProperty, MorphismProperty.Q, isGroupoid
-/
instance : IsGroupoid (⊤ : MorphismProperty C).Localization :=
isGroupoid MorphismProperty.Q ⊤

/-- Localization of a category with respect to all morphisms results in a groupoid. -/
@[instance_reducible]
/--
Definition of `groupoid` / `groupoid` 的定义

English:
definition groupoid
  signature: : Groupoid (⊤ : MorphismProperty C).Localization
  body: Groupoid.ofIsGroupoid

中文:
定义 groupoid
  签名: : 群胚 (⊤ : MorphismProperty C).Localization
  定义体: Groupoid.ofIsGroupoid

Depends on / 依赖: Groupoid, Groupoid.ofIsGroupoid, ofIsGroupoid
-/
def groupoid : Groupoid (⊤ : MorphismProperty C).Localization :=
  Groupoid.ofIsGroupoid

end Localization

section

variable {X Y : C} (f g : X ⟶ Y)

/--
Definition of `AreEqualizedByLocalization` / `AreEqualizedByLocalization` 的定义

English:
definition AreEqualizedByLocalization
  signature: : Prop
  body: W.Q.map f = W.Q.map g

中文:
定义 AreEqualizedByLocalization
  签名: : 命题
  定义体: W.Q.map f = W.Q.map g

Depends on / 依赖: W.Q.map
-/
def AreEqualizedByLocalization : Prop := W.Q.map f = W.Q.map g

/--
lemma `areEqualizedByLocalization_iff` / 引理 `areEqualizedByLocalization_iff`

English:
lemma areEqualizedByLocalization_iff
  given: [L.IsLocalization W]
  proof: by
  dsimp [AreEqualizedByLocalization]
  constructor
  · intro h
    let e := Localization.compUniqFunctor W.Q L W
    rw [← NatIso.naturality_1 e f]; rw [← NatIso.naturality_1 e g]
    dsimp
    rw [h]
  · intro h
    let e := Localization.compUniqFunctor L W.Q W
    rw [← NatIso.naturality_1 e f]; rw [← NatIso.naturality_1 e g]
    dsimp
    rw [h]

中文:
引理 areEqualizedByLocalization_iff
  条件: [L.是Localization W]
  证明: by
  dsimp [AreEqualizedByLocalization]
  constructor
  · intro h
    let e := Localization.compUniqFunctor W.Q L W
    rw [← NatIso.naturality_1 e f]; rw [← NatIso.naturality_1 e g]
    dsimp
    rw [h]
  · intro h
    let e := Localization.compUniqFunctor L W.Q W
    rw [← NatIso.naturality_1 e f]; rw [← NatIso.naturality_1 e g]
    dsimp
    rw [h]

Depends on / 依赖: AreEqualizedByLocalization, Localization, Localization.compUniqFunctor, NatIso, NatIso.naturality_1, compUniqFunctor, naturality_1
-/
lemma areEqualizedByLocalization_iff [L.IsLocalization W] :
    AreEqualizedByLocalization W f g ↔ L.map f = L.map g := by
  dsimp [AreEqualizedByLocalization]
  constructor
  · intro h
    let e := Localization.compUniqFunctor W.Q L W
    rw [← NatIso.naturality_1 e f]; rw [← NatIso.naturality_1 e g]
    dsimp
    rw [h]
  · intro h
    let e := Localization.compUniqFunctor L W.Q W
    rw [← NatIso.naturality_1 e f]; rw [← NatIso.naturality_1 e g]
    dsimp
    rw [h]

namespace AreEqualizedByLocalization

/--
lemma `mk` / 引理 `mk`

English:
lemma mk
  given: (L : C ⥤ D) [L.IsLocalization W] (h : L.map f = L.map g)
  proof: (areEqualizedByLocalization_iff L W f g).2 h

中文:
引理 mk
  条件: (L : C ⥤ D) [L.是Localization W] (h : L.map f = L.map g)
  证明: (areEqualizedByLocalization_iff L W f g).2 h

Depends on / 依赖: areEqualizedByLocalization_iff
-/
lemma mk (L : C ⥤ D) [L.IsLocalization W] (h : L.map f = L.map g) :
    AreEqualizedByLocalization W f g :=
  (areEqualizedByLocalization_iff L W f g).2 h

variable {W f g}

/--
lemma `map_eq` / 引理 `map_eq`

English:
lemma map_eq
  given: (h : AreEqualizedByLocalization W f g) (L : C ⥤ D) [L.IsLocalization W]
  proof: (areEqualizedByLocalization_iff L W f g).1 h

中文:
引理 map_eq
  条件: (h : AreEqualizedByLocalization W f g) (L : C ⥤ D) [L.是Localization W]
  证明: (areEqualizedByLocalization_iff L W f g).1 h

Depends on / 依赖: areEqualizedByLocalization_iff
-/
lemma map_eq (h : AreEqualizedByLocalization W f g) (L : C ⥤ D) [L.IsLocalization W] :
    L.map f = L.map g :=
  (areEqualizedByLocalization_iff L W f g).1 h

/--
lemma `map_eq_of_isInvertedBy` / 引理 `map_eq_of_isInvertedBy`

English:
lemma map_eq_of_isInvertedBy
  statement: (h : AreEqualizedByLocalization W f g)
  proof: by
  simp [← NatIso.naturality_1 (Localization.fac F hF W.Q), h.map_eq W.Q]

中文:
引理 map_eq_of_isInvertedBy
  结论: (h : AreEqualizedByLocalization W f g)
  证明: by
  simp [← NatIso.naturality_1 (Localization.fac F hF W.Q), h.map_eq W.Q]

Depends on / 依赖: F.shiftIso_add, Localization, Localization.fac, NatIso, NatIso.naturality_1, h.map_eq, map_eq, naturality_1, shiftIso_add
-/
lemma map_eq_of_isInvertedBy (h : AreEqualizedByLocalization W f g)
    (F : C ⥤ D) (hF : W.IsInvertedBy F) :
    F.map f = F.map g := by
  simp [← NatIso.naturality_1 (Localization.fac F hF W.Q), h.map_eq W.Q]

end AreEqualizedByLocalization

end

end CategoryTheory
