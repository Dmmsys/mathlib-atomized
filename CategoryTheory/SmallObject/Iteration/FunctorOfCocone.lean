/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.CategoryTheory.SmallObject.Iteration.Basic

/-!
# The functor from `Set.Iic j` deduced from a cocone

Given a functor `F : Set.Iio j ⥤ C` and `c : Cocone F`, we define
an extension of `F` as a functor `Set.Iic j ⥤ C` for which
the top element is mapped to `c.pt`.

-/

@[expose] public section

universe u

namespace CategoryTheory

open Category Limits

namespace SmallObject

namespace SuccStruct

variable {C : Type*} [Category* C]
  {J : Type u} [LinearOrder J]
  {j : J} {F : Set.Iio j ⥤ C} (c : Cocone F)

namespace ofCocone

/--
Definition of `obj` / `obj` 的定义

English:
definition obj
  signature: (i : J)
  body: if hi : i < j then
    F.obj ⟨i, hi⟩
  else c.pt

中文:
定义 obj
  签名: (i : J)
  定义体: if hi : i < j then
    F.obj ⟨i, hi⟩
  else c.pt

Depends on / 依赖: F.obj, c.pt
-/
def obj (i : J) : C :=
  if hi : i < j then
    F.obj ⟨i, hi⟩
  else c.pt

/--
Definition of `objIso` / `objIso` 的定义

English:
definition objIso
  signature: (i : J) (hi : i < j)
  body: eqToIso (dif_pos hi)

中文:
定义 objIso
  签名: (i : J) (hi : i < j)
  定义体: eqToIso (dif_pos hi)

Depends on / 依赖: dif_pos, eqToIso
-/
def objIso (i : J) (hi : i < j) :
    obj c i ≅ F.obj ⟨i, hi⟩ :=
  eqToIso (dif_pos hi)

/--
Definition of `objIsoPt` / `objIsoPt` 的定义

English:
definition objIsoPt
  signature: :
  body: eqToIso (dif_neg (by simp))

中文:
定义 objIsoPt
  签名: :
  定义体: eqToIso (dif_neg (by simp))

Depends on / 依赖: dif_neg, eqToIso
-/
def objIsoPt :
    obj c j ≅ c.pt :=
  eqToIso (dif_neg (by simp))

/--
Definition of `map` / `map` 的定义

English:
definition map
  signature: (i₁ i₂ : J) (hi : i₁ <= i₂) (hi₂ : i₂ <= j)
  body: if h₂ : i₂ < j then
    (objIso c i₁ (lt_of_le_of_lt hi h₂)).hom ≫ F.map (homOfLE hi) ≫ (objIso c i₂ h₂).inv
  else
    have h₂' : i₂ = j := le_antisymm hi₂ (by simpa using h₂)
    if h₁ : i₁ < j then
      (objIso c i₁ h₁).hom ≫ c.ι.app ⟨i₁, h₁⟩ ≫ (objIsoPt c).inv ≫ eqToHom (by subst h₂'; rfl)
    else
      have h₁' : i₁ = j := le_antisymm (hi.trans hi₂) (by simpa using h₁)
      eqToHom (by subst h₁' h₂'; rfl)

中文:
定义 map
  签名: (i₁ i₂ : J) (hi : i₁ <= i₂) (hi₂ : i₂ <= j)
  定义体: if h₂ : i₂ < j then
    (objIso c i₁ (lt_of_le_of_lt hi h₂)).hom ≫ F.map (homOfLE hi) ≫ (objIso c i₂ h₂).inv
  else
    have h₂' : i₂ = j := le_antisymm hi₂ (by simpa using h₂)
    if h₁ : i₁ < j then
      (objIso c i₁ h₁).hom ≫ c.ι.app ⟨i₁, h₁⟩ ≫ (objIsoPt c).inv ≫ eqToHom (by subst h₂'; rfl)
    else
      have h₁' : i₁ = j := le_antisymm (hi.trans hi₂) (by simpa using h₁)
      eqToHom (by subst h₁' h₂'; rfl)

Depends on / 依赖: F.map, eqToHom, hi.trans, homOfLE, le_antisymm, lt_of_le_of_lt, objIso, objIsoPt
-/
def map (i₁ i₂ : J) (hi : i₁ <= i₂) (hi₂ : i₂ <= j) :
    obj c i₁ ⟶ obj c i₂ :=
  if h₂ : i₂ < j then
    (objIso c i₁ (lt_of_le_of_lt hi h₂)).hom ≫ F.map (homOfLE hi) ≫ (objIso c i₂ h₂).inv
  else
    have h₂' : i₂ = j := le_antisymm hi₂ (by simpa using h₂)
    if h₁ : i₁ < j then
      (objIso c i₁ h₁).hom ≫ c.ι.app ⟨i₁, h₁⟩ ≫ (objIsoPt c).inv ≫ eqToHom (by subst h₂'; rfl)
    else
      have h₁' : i₁ = j := le_antisymm (hi.trans hi₂) (by simpa using h₁)
      eqToHom (by subst h₁' h₂'; rfl)

/--
lemma `map_id` / 引理 `map_id`

English:
lemma map_id
  given: (i : J) (hi : i <= j)
  proof: by
  dsimp [map]
  grind

中文:
引理 map_id
  条件: (i : J) (hi : i <= j)
  证明: by
  dsimp [map]
  grind
-/
lemma map_id (i : J) (hi : i <= j) :
    map c i i (by rfl) hi = 𝟙 _ := by
  dsimp [map]
  grind

set_option backward.defeqAttrib.useBackward true in
/--
lemma `map_comp` / 引理 `map_comp`

English:
lemma map_comp
  given: (i₁ i₂ i₃ : J) (hi : i₁ <= i₂) (hi' : i₂ <= i₃) (hi₃ : i₃ <= j)
  proof: by
  obtain hi₁₂ | rfl := hi.lt_or_eq
  · obtain hi₂₃ | rfl := hi'.lt_or_eq
    · dsimp [map]
      obtain hi₃' | rfl := hi₃.lt_or_eq
      · rw [dif_pos hi₃', dif_pos (hi₂₃.trans hi₃'), dif_pos hi₃', assoc, assoc,
          Iso.inv_hom_id_assoc, ← Functor.map_comp_assoc, homOfLE_comp]
      · rw [dif_neg (by simp), dif_pos (hi₁₂.trans hi₂₃), dif_pos hi₂₃, dif_neg (by simp),
          dif_pos hi₂₃, eqToHom_refl, comp_id, assoc, assoc, Iso.inv_hom_id_assoc,
          Cocone.w_assoc]
    · rw [map_id, comp_id]
  · rw [map_id, id_comp]

中文:
引理 map_comp
  条件: (i₁ i₂ i₃ : J) (hi : i₁ <= i₂) (hi' : i₂ <= i₃) (hi₃ : i₃ <= j)
  证明: by
  obtain hi₁₂ | rfl := hi.lt_or_eq
  · obtain hi₂₃ | rfl := hi'.lt_or_eq
    · dsimp [map]
      obtain hi₃' | rfl := hi₃.lt_or_eq
      · rw [dif_pos hi₃', dif_pos (hi₂₃.trans hi₃'), dif_pos hi₃', assoc, assoc,
          Iso.inv_hom_id_assoc, ← Functor.map_comp_assoc, homOfLE_comp]
      · rw [dif_neg (by simp), dif_pos (hi₁₂.trans hi₂₃), dif_pos hi₂₃, dif_neg (by simp),
          dif_pos hi₂₃, eqToHom_refl, comp_id, assoc, assoc, Iso.inv_hom_id_assoc,
          Cocone.w_assoc]
    · rw [map_id, comp_id]
  · rw [map_id, id_comp]

Depends on / 依赖: Cocone, Cocone.w_assoc, Functor, Functor.map_comp_assoc, Iso.inv_hom_id_assoc, comp_id, dif_neg, dif_pos, eqToHom_refl, hi.lt_or_eq, homOfLE_comp, id_comp, inv_hom_id_assoc, lt_or_eq, map_comp_assoc, map_id, w_assoc
-/
lemma map_comp (i₁ i₂ i₃ : J) (hi : i₁ <= i₂) (hi' : i₂ <= i₃) (hi₃ : i₃ <= j) :
    map c i₁ i₃ (hi.trans hi') hi₃ =
      map c i₁ i₂ hi (hi'.trans hi₃) ≫
        map c i₂ i₃ hi' hi₃ := by
  obtain hi₁₂ | rfl := hi.lt_or_eq
  · obtain hi₂₃ | rfl := hi'.lt_or_eq
    · dsimp [map]
      obtain hi₃' | rfl := hi₃.lt_or_eq
      · rw [dif_pos hi₃', dif_pos (hi₂₃.trans hi₃'), dif_pos hi₃', assoc, assoc,
          Iso.inv_hom_id_assoc, ← Functor.map_comp_assoc, homOfLE_comp]
      · rw [dif_neg (by simp), dif_pos (hi₁₂.trans hi₂₃), dif_pos hi₂₃, dif_neg (by simp),
          dif_pos hi₂₃, eqToHom_refl, comp_id, assoc, assoc, Iso.inv_hom_id_assoc,
          Cocone.w_assoc]
    · rw [map_id, comp_id]
  · rw [map_id, id_comp]

end ofCocone

/--
Definition of `ofCocone` / `ofCocone` 的定义

English:
definition ofCocone
  signature: : Set.Iic j ⥤ C where
  body: ofCocone.obj c i.1
  map {_ j} f := ofCocone.map c _ _ (leOfHom f) j.2
  map_id i := ofCocone.map_id _ _ i.2
  map_comp {_ _ i₃} _ _ := ofCocone.map_comp _ _ _ _ _ _ i₃.2

中文:
定义 ofCocone
  签名: : 集合.左无界右闭区间 j ⥤ C where
  定义体: ofCocone.obj c i.1
  map {_ j} f := ofCocone.map c _ _ (leOfHom f) j.2
  map_id i := ofCocone.map_id _ _ i.2
  map_comp {_ _ i₃} _ _ := ofCocone.map_comp _ _ _ _ _ _ i₃.2

Depends on / 依赖: ofCocone, ofCocone.obj
-/
def ofCocone : Set.Iic j ⥤ C where
  obj i := ofCocone.obj c i.1
  map {_ j} f := ofCocone.map c _ _ (leOfHom f) j.2
  map_id i := ofCocone.map_id _ _ i.2
  map_comp {_ _ i₃} _ _ := ofCocone.map_comp _ _ _ _ _ _ i₃.2

/--
lemma `ofCocone_obj_eq` / 引理 `ofCocone_obj_eq`

English:
lemma ofCocone_obj_eq
  given: (i : J) (hi : i < j)
  proof: dif_pos hi

中文:
引理 ofCocone_obj_eq
  条件: (i : J) (hi : i < j)
  证明: dif_pos hi

Depends on / 依赖: dif_pos
-/
lemma ofCocone_obj_eq (i : J) (hi : i < j) :
    (ofCocone c).obj ⟨i, hi.le⟩ = F.obj ⟨i, hi⟩ :=
  dif_pos hi

/--
Definition of `ofCoconeObjIso` / `ofCoconeObjIso` 的定义

English:
definition ofCoconeObjIso
  signature: (i : J) (hi : i < j)
  body: ofCocone.objIso c _ _

中文:
定义 ofCoconeObjIso
  签名: (i : J) (hi : i < j)
  定义体: ofCocone.objIso c _ _

Depends on / 依赖: objIso, ofCocone, ofCocone.objIso
-/
def ofCoconeObjIso (i : J) (hi : i < j) :
    (ofCocone c).obj ⟨i, hi.le⟩ ≅ F.obj ⟨i, hi⟩ :=
  ofCocone.objIso c _ _

/--
lemma `ofCocone_obj_eq_pt` / 引理 `ofCocone_obj_eq_pt`

English:
lemma ofCocone_obj_eq_pt
  proof: dif_neg (by simp)

中文:
引理 ofCocone_obj_eq_pt
  证明: dif_neg (by simp)

Depends on / 依赖: dif_neg
-/
lemma ofCocone_obj_eq_pt :
    (ofCocone c).obj ⟨j, by simp⟩ = c.pt :=
  dif_neg (by simp)

/--
Definition of `ofCoconeObjIsoPt` / `ofCoconeObjIsoPt` 的定义

English:
definition ofCoconeObjIsoPt
  signature: :
  body: ofCocone.objIsoPt c

中文:
定义 ofCoconeObjIsoPt
  签名: :
  定义体: ofCocone.objIsoPt c

Depends on / 依赖: objIsoPt, ofCocone, ofCocone.objIsoPt
-/
def ofCoconeObjIsoPt :
    (ofCocone c).obj ⟨j, by simp⟩ ≅ c.pt :=
  ofCocone.objIsoPt c

/--
lemma `ofCocone_map_to_top` / 引理 `ofCocone_map_to_top`

English:
lemma ofCocone_map_to_top
  given: (i : J) (hi : i < j)
  proof: by
  dsimp [ofCocone, ofCocone.map, ofCoconeObjIso, ofCoconeObjIsoPt]
  rw [dif_neg (by simp)]; rw [dif_pos hi]; rw [comp_id]

@[reassoc]

中文:
引理 ofCocone_map_to_top
  条件: (i : J) (hi : i < j)
  证明: by
  dsimp [ofCocone, ofCocone.map, ofCoconeObjIso, ofCoconeObjIsoPt]
  rw [dif_neg (by simp)]; rw [dif_pos hi]; rw [comp_id]

@[reassoc]

Depends on / 依赖: comp_id, dif_neg, dif_pos, ofCocone, ofCocone.map, ofCoconeObjIso, ofCoconeObjIsoPt
-/
lemma ofCocone_map_to_top (i : J) (hi : i < j) :
    (ofCocone c).map (homOfLE hi.le) =
      (ofCoconeObjIso c i hi).hom ≫ c.ι.app ⟨i, hi⟩ ≫ (ofCoconeObjIsoPt c).inv := by
  dsimp [ofCocone, ofCocone.map, ofCoconeObjIso, ofCoconeObjIsoPt]
  rw [dif_neg (by simp)]; rw [dif_pos hi]; rw [comp_id]

@[reassoc]
/--
lemma `ofCocone_map` / 引理 `ofCocone_map`

English:
lemma ofCocone_map
  given: (i₁ i₂ : J) (hi : i₁ <= i₂) (hi₂ : i₂ < j)
  proof: by
  dsimp [ofCocone, ofCoconeObjIso, ofCocone.map]
  rw [dif_pos hi₂]

@[reassoc]

中文:
引理 ofCocone_map
  条件: (i₁ i₂ : J) (hi : i₁ <= i₂) (hi₂ : i₂ < j)
  证明: by
  dsimp [ofCocone, ofCoconeObjIso, ofCocone.map]
  rw [dif_pos hi₂]

@[reassoc]

Depends on / 依赖: dif_pos, ofCocone, ofCocone.map, ofCoconeObjIso
-/
lemma ofCocone_map (i₁ i₂ : J) (hi : i₁ <= i₂) (hi₂ : i₂ < j) :
    (ofCocone c).map (homOfLE hi : ⟨i₁, hi.trans hi₂.le⟩ ⟶ ⟨i₂, hi₂.le⟩) =
      (ofCoconeObjIso c i₁ (lt_of_le_of_lt hi hi₂)).hom ≫ F.map (homOfLE hi) ≫
        (ofCoconeObjIso c i₂ hi₂).inv := by
  dsimp [ofCocone, ofCoconeObjIso, ofCocone.map]
  rw [dif_pos hi₂]

@[reassoc]
/--
lemma `ofCoconeObjIso_hom_naturality` / 引理 `ofCoconeObjIso_hom_naturality`

English:
lemma ofCoconeObjIso_hom_naturality
  given: (i₁ i₂ : J) (hi : i₁ <= i₂) (hi₂ : i₂ < j)
  proof: by
  rw [ofCocone_map c i₁ i₂ hi hi₂]; rw [assoc]; rw [assoc]; rw [Iso.inv_hom_id]; rw [comp_id]

中文:
引理 ofCoconeObjIso_hom_naturality
  条件: (i₁ i₂ : J) (hi : i₁ <= i₂) (hi₂ : i₂ < j)
  证明: by
  rw [ofCocone_map c i₁ i₂ hi hi₂]; rw [assoc]; rw [assoc]; rw [Iso.inv_hom_id]; rw [comp_id]

Depends on / 依赖: Iso.inv_hom_id, comp_id, inv_hom_id, ofCocone_map
-/
lemma ofCoconeObjIso_hom_naturality (i₁ i₂ : J) (hi : i₁ <= i₂) (hi₂ : i₂ < j) :
    (ofCocone c).map (homOfLE hi : ⟨i₁, hi.trans hi₂.le⟩ ⟶ ⟨i₂, hi₂.le⟩) ≫
      (ofCoconeObjIso c i₂ hi₂).hom =
      (ofCoconeObjIso c i₁ (lt_of_le_of_lt hi hi₂)).hom ≫ F.map (homOfLE hi) := by
  rw [ofCocone_map c i₁ i₂ hi hi₂]; rw [assoc]; rw [assoc]; rw [Iso.inv_hom_id]; rw [comp_id]

/-- The isomorphism expressing that `ofCocone c` extends the functor `F`
when `c : Cocone F`. -/
@[simps!]
/--
Definition of `restrictionLTOfCoconeIso` / `restrictionLTOfCoconeIso` 的定义

English:
definition restrictionLTOfCoconeIso
  signature: :
  body: NatIso.ofComponents (fun ⟨i, hi⟩ => ofCoconeObjIso c i hi)
    (by intros; apply ofCoconeObjIso_hom_naturality)

中文:
定义 restrictionLTOfCoconeIso
  签名: :
  定义体: NatIso.ofComponents (fun ⟨i, hi⟩ => ofCoconeObjIso c i hi)
    (by intros; apply ofCoconeObjIso_hom_naturality)

Depends on / 依赖: NatIso, NatIso.ofComponents, intros, ofCoconeObjIso, ofCoconeObjIso_hom_naturality, ofComponents
-/
def restrictionLTOfCoconeIso :
    SmallObject.restrictionLT (ofCocone c) (le_refl j) ≅ F :=
  NatIso.ofComponents (fun ⟨i, hi⟩ => ofCoconeObjIso c i hi)
    (by intros; apply ofCoconeObjIso_hom_naturality)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
variable {c} in
/--
Definition of `isColimitCoconeOfLEOfCocone` / `isColimitCoconeOfLEOfCocone` 的定义

English:
definition isColimitCoconeOfLEOfCocone
  signature: (hc : IsColimit c)
  body: (IsColimit.precomposeInvEquiv (restrictionLTOfCoconeIso c) _).1
    (IsColimit.ofIsoColimit hc
      (Cocone.ext (ofCoconeObjIsoPt c).symm (fun ⟨i, hi⟩ => by
        dsimp
        rw [ofCocone_map_to_top _ _ hi]; rw [Iso.inv_hom_id_assoc])))

中文:
定义 isColimitCoconeOfLEOfCocone
  签名: (hc : 是余极限 c)
  定义体: (IsColimit.precomposeInvEquiv (restrictionLTOfCoconeIso c) _).1
    (IsColimit.ofIsoColimit hc
      (Cocone.ext (ofCoconeObjIsoPt c).symm (fun ⟨i, hi⟩ => by
        dsimp
        rw [ofCocone_map_to_top _ _ hi]; rw [Iso.inv_hom_id_assoc])))

Depends on / 依赖: Cocone, Cocone.ext, IsColimit, IsColimit.ofIsoColimit, IsColimit.precomposeInvEquiv, Iso.inv_hom_id_assoc, inv_hom_id_assoc, ofCoconeObjIsoPt, ofCocone_map_to_top, ofIsoColimit, precomposeInvEquiv, restrictionLTOfCoconeIso
-/
def isColimitCoconeOfLEOfCocone (hc : IsColimit c) :
    IsColimit (coconeOfLE (ofCocone c) (le_refl j)) :=
  (IsColimit.precomposeInvEquiv (restrictionLTOfCoconeIso c) _).1
    (IsColimit.ofIsoColimit hc
      (Cocone.ext (ofCoconeObjIsoPt c).symm (fun ⟨i, hi⟩ => by
        dsimp
        rw [ofCocone_map_to_top _ _ hi]; rw [Iso.inv_hom_id_assoc])))

/--
lemma `arrowMap_ofCocone` / 引理 `arrowMap_ofCocone`

English:
lemma arrowMap_ofCocone
  given: (i₁ i₂ : J) (h₁₂ : i₁ <= i₂) (h₂ : i₂ < j)
  proof: Arrow.ext (ofCocone_obj_eq _ _ _) (ofCocone_obj_eq _ _ _) (ofCocone_map _ _ _ _ _)

中文:
引理 arrowMap_ofCocone
  条件: (i₁ i₂ : J) (h₁₂ : i₁ <= i₂) (h₂ : i₂ < j)
  证明: Arrow.ext (ofCocone_obj_eq _ _ _) (ofCocone_obj_eq _ _ _) (ofCocone_map _ _ _ _ _)

Depends on / 依赖: Arrow.ext, ofCocone_map, ofCocone_obj_eq
-/
lemma arrowMap_ofCocone (i₁ i₂ : J) (h₁₂ : i₁ <= i₂) (h₂ : i₂ < j) :
    arrowMap (ofCocone c) i₁ i₂ h₁₂ h₂.le =
      Arrow.mk (F.map (homOfLE h₁₂ : ⟨i₁, lt_of_le_of_lt h₁₂ h₂⟩ ⟶ ⟨i₂, h₂⟩)) :=
  Arrow.ext (ofCocone_obj_eq _ _ _) (ofCocone_obj_eq _ _ _) (ofCocone_map _ _ _ _ _)

/--
lemma `arrowMap_ofCocone_to_top` / 引理 `arrowMap_ofCocone_to_top`

English:
lemma arrowMap_ofCocone_to_top
  given: (i : J) (hi : i < j)
  proof: by
  rw [arrowMap]; rw [ofCocone_map_to_top _ _ hi]
  exact Arrow.ext (ofCocone_obj_eq _ _ _) (ofCocone_obj_eq_pt _) rfl

中文:
引理 arrowMap_ofCocone_to_top
  条件: (i : J) (hi : i < j)
  证明: by
  rw [arrowMap]; rw [ofCocone_map_to_top _ _ hi]
  exact Arrow.ext (ofCocone_obj_eq _ _ _) (ofCocone_obj_eq_pt _) rfl

Depends on / 依赖: Arrow.ext, arrowMap, ofCocone_map_to_top, ofCocone_obj_eq, ofCocone_obj_eq_pt
-/
lemma arrowMap_ofCocone_to_top (i : J) (hi : i < j) :
    arrowMap (ofCocone c) i j hi.le (by simp) = Arrow.mk (c.ι.app ⟨i, hi⟩) := by
  rw [arrowMap]; rw [ofCocone_map_to_top _ _ hi]
  exact Arrow.ext (ofCocone_obj_eq _ _ _) (ofCocone_obj_eq_pt _) rfl

end SuccStruct

end SmallObject

end CategoryTheory
