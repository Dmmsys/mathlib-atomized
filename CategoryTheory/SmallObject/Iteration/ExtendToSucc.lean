/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.CategoryTheory.SmallObject.Iteration.Basic

/-!
# Extension of a functor from `Set.Iic j` to `Set.Iic (Order.succ j)`

Given a linearly ordered type `J` with `SuccOrder J`, `j : J` that is not maximal,
we define the extension of a functor `F : Set.Iic j ⥤ C` as a
functor `Set.Iic (Order.succ j) ⥤ C` when an object `X : C` and a morphism
`τ : F.obj ⟨j, _⟩ ⟶ X` is given.

-/

@[expose] public section

universe u

namespace CategoryTheory

open Category

namespace SmallObject

variable {C : Type*} [Category* C]
  {J : Type u} [LinearOrder J] [SuccOrder J] {j : J} (hj : ¬IsMax j)
  (F : Set.Iic j ⥤ C) {X : C} (τ : F.obj ⟨j, by simp⟩ ⟶ X)

namespace SuccStruct

namespace extendToSucc

variable (X)

set_option backward.privateInPublic true in
/--
Definition of `obj` / `obj` 的定义

English:
definition obj
  signature: (i : Set.Iic (Order.succ j))
  body: if hij : i.1 <= j then F.obj ⟨i.1, hij⟩ else X

中文:
定义 obj
  签名: (i : Set.Iic (Order.succ j))
  定义体: if hij : i.1 <= j then F.obj ⟨i.1, hij⟩ else X

Depends on / 依赖: F.obj
-/
def obj (i : Set.Iic (Order.succ j)) : C :=
  if hij : i.1 <= j then F.obj ⟨i.1, hij⟩ else X

/--
lemma `obj_eq` / 引理 `obj_eq`

English:
lemma obj_eq
  given: (i : Set.Iic j)
  proof: dif_pos i.2

中文:
引理 obj_eq
  条件: (i : Set.Iic j)
  证明: dif_pos i.2

Depends on / 依赖: Set.fintypeSubset, dif_pos, fintypeSubset, neighborSet_subset_verts
-/
lemma obj_eq (i : Set.Iic j) :
    obj F X ⟨i, i.2.trans (Order.le_succ j)⟩ = F.obj i := dif_pos i.2

/--
Definition of `objIso` / `objIso` 的定义

English:
definition objIso
  signature: (i : Set.Iic j)
  body: eqToIso (obj_eq _ _ _)

include hj in

中文:
定义 objIso
  签名: (i : Set.Iic j)
  定义体: eqToIso (obj_eq _ _ _)

include hj in

Depends on / 依赖: eqToIso, obj_eq
-/
def objIso (i : Set.Iic j) :
    obj F X ⟨i, i.2.trans (Order.le_succ j)⟩ ≅ F.obj i :=
  eqToIso (obj_eq _ _ _)

include hj in
/--
lemma `obj_succ_eq` / 引理 `obj_succ_eq`

English:
lemma obj_succ_eq
  statement: obj F X ⟨Order.succ j, by simp⟩ = X
  proof: dif_neg (by simpa only [Order.succ_le_iff_isMax] using hj)

中文:
引理 obj_succ_eq
  结论: obj F X ⟨Order.succ j, by simp⟩ = X
  证明: dif_neg (by simpa only [Order.succ_le_iff_isMax] using hj)

Depends on / 依赖: Order.succ_le_iff_isMax, dif_neg, succ_le_iff_isMax
-/
lemma obj_succ_eq : obj F X ⟨Order.succ j, by simp⟩ = X :=
  dif_neg (by simpa only [Order.succ_le_iff_isMax] using hj)

/--
Definition of `objSuccIso` / `objSuccIso` 的定义

English:
definition objSuccIso
  signature: :
  body: eqToIso (obj_succ_eq hj _ _)

中文:
定义 objSuccIso
  签名: :
  定义体: eqToIso (obj_succ_eq hj _ _)

Depends on / 依赖: eqToIso, obj_succ_eq
-/
def objSuccIso :
    obj F X ⟨Order.succ j, by simp⟩ ≅ X :=
  eqToIso (obj_succ_eq hj _ _)

variable {X}

/--
Definition of `map` / `map` 的定义

English:
definition map
  signature: (i₁ i₂ : J) (hi : i₁ <= i₂) (hi₂ : i₂ <= Order.succ j)
  body: if h₁ : i₂ <= j then
    (objIso F X ⟨i₁, hi.trans h₁⟩).hom ≫ F.map (homOfLE hi) ≫ (objIso F X ⟨i₂, h₁⟩).inv
  else
    if h₂ : i₁ <= j then
      (objIso F X ⟨i₁, h₂⟩).hom ≫ F.map (homOfLE h₂) ≫ τ ≫
        (objSuccIso hj F X).inv ≫ eqToHom (by
          congr
          exact le_antisymm (Order.suc

中文:
定义 map
  签名: (i₁ i₂ : J) (hi : i₁ <= i₂) (hi₂ : i₂ <= Order.succ j)
  定义体: if h₁ : i₂ <= j then
    (objIso F X ⟨i₁, hi.trans h₁⟩).hom ≫ F.map (homOfLE hi) ≫ (objIso F X ⟨i₂, h₁⟩).inv
  else
    if h₂ : i₁ <= j then
      (objIso F X ⟨i₁, h₂⟩).hom ≫ F.map (homOfLE h₂) ≫ τ ≫
        (objSuccIso hj F X).inv ≫ eqToHom (by
          congr
          exact le_antisymm (Order.suc

Depends on / 依赖: F.map, Order.succ_le_of_lt, eqToHom, hi.trans, homOfLE, le_antisymm, not_le, objIso, objSuccIso, succ_le_of_lt
-/
def map (i₁ i₂ : J) (hi : i₁ <= i₂) (hi₂ : i₂ <= Order.succ j) :
    obj F X ⟨i₁, hi.trans hi₂⟩ ⟶ obj F X ⟨i₂, hi₂⟩ :=
  if h₁ : i₂ <= j then
    (objIso F X ⟨i₁, hi.trans h₁⟩).hom ≫ F.map (homOfLE hi) ≫ (objIso F X ⟨i₂, h₁⟩).inv
  else
    if h₂ : i₁ <= j then
      (objIso F X ⟨i₁, h₂⟩).hom ≫ F.map (homOfLE h₂) ≫ τ ≫
        (objSuccIso hj F X).inv ≫ eqToHom (by
          congr
          exact le_antisymm (Order.succ_le_of_lt (not_le.1 h₁)) hi₂)
    else
      eqToHom (by
        congr
        rw [le_antisymm hi₂ (Order.succ_le_of_lt (not_le.1 h₁))]; rw [le_antisymm (hi.trans hi₂) (Order.succ_le_of_lt (not_le.1 h₂))])

/--
lemma `map_eq` / 引理 `map_eq`

English:
lemma map_eq
  given: (i₁ i₂ : J) (hi : i₁ <= i₂) (hi₂ : i₂ <= j)
  proof: dif_pos hi₂

中文:
引理 map_eq
  条件: (i₁ i₂ : J) (hi : i₁ <= i₂) (hi₂ : i₂ <= j)
  证明: dif_pos hi₂

Depends on / 依赖: dif_pos
-/
lemma map_eq (i₁ i₂ : J) (hi : i₁ <= i₂) (hi₂ : i₂ <= j) :
    map hj F τ i₁ i₂ hi (hi₂.trans (Order.le_succ j)) =
      (objIso F X ⟨i₁, hi.trans hi₂⟩).hom ≫ F.map (homOfLE hi) ≫
        (objIso F X ⟨i₂, hi₂⟩).inv :=
  dif_pos hi₂

/--
lemma `map_self_succ` / 引理 `map_self_succ`

English:
lemma map_self_succ
  proof: by
  dsimp [map]
  rw [dif_neg (by simpa only [Order.succ_le_iff_isMax] using hj),
    dif_pos (by rfl), Functor.map_id, comp_id, id_comp]

@[simp]

中文:
引理 map_self_succ
  证明: by
  dsimp [map]
  rw [dif_neg (by simpa only [Order.succ_le_iff_isMax] using hj),
    dif_pos (by rfl), Functor.map_id, comp_id, id_comp]

@[simp]

Depends on / 依赖: Functor, Functor.map_id, Order.succ_le_iff_isMax, comp_id, dif_neg, dif_pos, id_comp, map_id, succ_le_iff_isMax
-/
lemma map_self_succ :
    map hj F τ j (Order.succ j) (Order.le_succ j) (by rfl) =
      (objIso F X ⟨j, by simp⟩).hom ≫ τ ≫ (objSuccIso hj F X).inv := by
  dsimp [map]
  rw [dif_neg (by simpa only [Order.succ_le_iff_isMax] using hj),
    dif_pos (by rfl), Functor.map_id, comp_id, id_comp]

@[simp]
/--
lemma `map_id` / 引理 `map_id`

English:
lemma map_id
  given: (i : J) (hi : i <= Order.succ j)
  proof: by
  dsimp [map]
  by_cases h₁ : i <= j
  · rw [dif_pos h₁, CategoryTheory.Functor.map_id, id_comp, Iso.hom_inv_id]
  · obtain rfl : i = Order.succ j := le_antisymm hi (Order.succ_le_of_lt (not_le.1 h₁))
    rw [dif_neg (by simpa only [Order.succ_le_iff_isMax] using hj),
      dif_neg h₁]

中文:
引理 map_id
  条件: (i : J) (hi : i <= Order.succ j)
  证明: by
  dsimp [map]
  by_cases h₁ : i <= j
  · rw [dif_pos h₁, CategoryTheory.Functor.map_id, id_comp, Iso.hom_inv_id]
  · obtain rfl : i = Order.succ j := le_antisymm hi (Order.succ_le_of_lt (not_le.1 h₁))
    rw [dif_neg (by simpa only [Order.succ_le_iff_isMax] using hj),
      dif_neg h₁]

Depends on / 依赖: CategoryTheory, CategoryTheory.Functor.map_id, Functor, Iso.hom_inv_id, Order.succ, Order.succ_le_iff_isMax, Order.succ_le_of_lt, dif_neg, dif_pos, hom_inv_id, id_comp, le_antisymm, map_id, not_le, succ_le_iff_isMax, succ_le_of_lt
-/
lemma map_id (i : J) (hi : i <= Order.succ j) :
    map hj F τ i i (by rfl) hi = 𝟙 _ := by
  dsimp [map]
  by_cases h₁ : i <= j
  · rw [dif_pos h₁, CategoryTheory.Functor.map_id, id_comp, Iso.hom_inv_id]
  · obtain rfl : i = Order.succ j := le_antisymm hi (Order.succ_le_of_lt (not_le.1 h₁))
    rw [dif_neg (by simpa only [Order.succ_le_iff_isMax] using hj),
      dif_neg h₁]

/--
lemma `map_comp` / 引理 `map_comp`

English:
lemma map_comp
  given: (i₁ i₂ i₃ : J) (h₁₂ : i₁ <= i₂) (h₂₃ : i₂ <= i₃) (h : i₃ <= Order.succ j)
  proof: by
  by_cases h₁ : i₃ <= j
  · rw [map_eq hj F τ i₁ i₂ _ (h₂₃.trans h₁), map_eq hj F τ i₂ i₃ _ h₁,
      map_eq hj F τ i₁ i₃ _ h₁, assoc, assoc, Iso.inv_hom_id_assoc, ← Functor.map_comp_assoc,
      homOfLE_comp]
  · obtain rfl : i₃ = Order.succ j := le_antisymm h (Order.succ_le_of_lt (not_le.1 h₁))

中文:
引理 map_comp
  条件: (i₁ i₂ i₃ : J) (h₁₂ : i₁ <= i₂) (h₂₃ : i₂ <= i₃) (h : i₃ <= Order.succ j)
  证明: by
  by_cases h₁ : i₃ <= j
  · rw [map_eq hj F τ i₁ i₂ _ (h₂₃.trans h₁), map_eq hj F τ i₂ i₃ _ h₁,
      map_eq hj F τ i₁ i₃ _ h₁, assoc, assoc, Iso.inv_hom_id_assoc, ← Functor.map_comp_assoc,
      homOfLE_comp]
  · obtain rfl : i₃ = Order.succ j := le_antisymm h (Order.succ_le_of_lt (not_le.1 h₁))

Depends on / 依赖: Functor, Functor.map_comp_assoc, Iso.inv_hom_id_assoc, Order.lt_succ_iff_of_not_isMax, Order.succ, Order.succ_le_of_lt, dif_neg, dif_pos, homOfLE_comp, inv_hom_id_assoc, le_antisymm, lt_or_eq, lt_succ_iff_of_not_isMax, map_comp_assoc, map_eq, not_le, succ_le_of_lt
-/
lemma map_comp (i₁ i₂ i₃ : J) (h₁₂ : i₁ <= i₂) (h₂₃ : i₂ <= i₃) (h : i₃ <= Order.succ j) :
    map hj F τ i₁ i₃ (h₁₂.trans h₂₃) h =
      map hj F τ i₁ i₂ h₁₂ (h₂₃.trans h) ≫ map hj F τ i₂ i₃ h₂₃ h := by
  by_cases h₁ : i₃ <= j
  · rw [map_eq hj F τ i₁ i₂ _ (h₂₃.trans h₁), map_eq hj F τ i₂ i₃ _ h₁,
      map_eq hj F τ i₁ i₃ _ h₁, assoc, assoc, Iso.inv_hom_id_assoc, ← Functor.map_comp_assoc,
      homOfLE_comp]
  · obtain rfl : i₃ = Order.succ j := le_antisymm h (Order.succ_le_of_lt (not_le.1 h₁))
    obtain h₂ | rfl := h₂₃.lt_or_eq
    · rw [Order.lt_succ_iff_of_not_isMax hj] at h₂
      rw [map_eq hj F τ i₁ i₂ _ h₂]
      dsimp [map]
      rw [dif_neg h₁]; rw [dif_pos (h₁₂.trans h₂)]; rw [dif_neg h₁]; rw [dif_pos h₂]; rw [assoc]; rw [assoc]; rw [Iso.inv_hom_id_assoc]; rw [comp_id]; rw [← Functor.map_comp_assoc]; rw [homOfLE_comp]
    · rw [map_id, comp_id]

end extendToSucc

open extendToSucc in
include hj in
/--
Definition of `extendToSucc` / `extendToSucc` 的定义

English:
definition extendToSucc
  signature: : Set.Iic (Order.succ j) ⥤ C where
  body: obj F X
  map {i₁ i₂} f := map hj F τ i₁ i₂ (leOfHom f) i₂.2
  map_id _ := extendToSucc.map_id _ F τ _ _
  map_comp {i₁ i₂ i₃} f g := extendToSucc.map_comp hj F τ i₁ i₂ i₃ (leOfHom f) (leOfHom g) i₃.2

中文:
定义 extendToSucc
  签名: : Set.Iic (Order.succ j) ⥤ C where
  定义体: obj F X
  map {i₁ i₂} f := map hj F τ i₁ i₂ (leOfHom f) i₂.2
  map_id _ := extendToSucc.map_id _ F τ _ _
  map_comp {i₁ i₂ i₃} f g := extendToSucc.map_comp hj F τ i₁ i₂ i₃ (leOfHom f) (leOfHom g) i₃.2
-/
def extendToSucc : Set.Iic (Order.succ j) ⥤ C where
  obj := obj F X
  map {i₁ i₂} f := map hj F τ i₁ i₂ (leOfHom f) i₂.2
  map_id _ := extendToSucc.map_id _ F τ _ _
  map_comp {i₁ i₂ i₃} f g := extendToSucc.map_comp hj F τ i₁ i₂ i₃ (leOfHom f) (leOfHom g) i₃.2

/--
lemma `extendToSucc_obj_eq` / 引理 `extendToSucc_obj_eq`

English:
lemma extendToSucc_obj_eq
  given: (i : J) (hi : i <= j)
  proof: extendToSucc.obj_eq F X ⟨i, hi⟩

中文:
引理 extendToSucc_obj_eq
  条件: (i : J) (hi : i <= j)
  证明: extendToSucc.obj_eq F X ⟨i, hi⟩

Depends on / 依赖: extendToSucc, extendToSucc.obj_eq, obj_eq
-/
lemma extendToSucc_obj_eq (i : J) (hi : i <= j) :
    (extendToSucc hj F τ).obj ⟨i, hi.trans (Order.le_succ j)⟩ = F.obj ⟨i, hi⟩ :=
  extendToSucc.obj_eq F X ⟨i, hi⟩

/--
Definition of `extendToSuccObjIso` / `extendToSuccObjIso` 的定义

English:
definition extendToSuccObjIso
  signature: (i : J) (hi : i <= j)
  body: extendToSucc.objIso F X ⟨i, hi⟩

中文:
定义 extendToSuccObjIso
  签名: (i : J) (hi : i <= j)
  定义体: extendToSucc.objIso F X ⟨i, hi⟩

Depends on / 依赖: extendToSucc, extendToSucc.objIso, objIso
-/
def extendToSuccObjIso (i : J) (hi : i <= j) :
    (extendToSucc hj F τ).obj ⟨i, hi.trans (Order.le_succ j)⟩ ≅ F.obj ⟨i, hi⟩ :=
  extendToSucc.objIso F X ⟨i, hi⟩

/--
lemma `extendToSucc_obj_succ_eq` / 引理 `extendToSucc_obj_succ_eq`

English:
lemma extendToSucc_obj_succ_eq
  proof: extendToSucc.obj_succ_eq hj F X

中文:
引理 extendToSucc_obj_succ_eq
  证明: extendToSucc.obj_succ_eq hj F X

Depends on / 依赖: extendToSucc, extendToSucc.obj_succ_eq, obj_succ_eq
-/
lemma extendToSucc_obj_succ_eq :
    (extendToSucc hj F τ).obj ⟨Order.succ j, by simp⟩ = X :=
  extendToSucc.obj_succ_eq hj F X

/--
Definition of `extendToSuccObjSuccIso` / `extendToSuccObjSuccIso` 的定义

English:
definition extendToSuccObjSuccIso
  signature: :
  body: extendToSucc.objSuccIso hj F X

@[reassoc]

中文:
定义 extendToSuccObjSuccIso
  签名: :
  定义体: extendToSucc.objSuccIso hj F X

@[reassoc]

Depends on / 依赖: extendToSucc, extendToSucc.objSuccIso, objSuccIso
-/
def extendToSuccObjSuccIso :
    (extendToSucc hj F τ).obj ⟨Order.succ j, by simp⟩ ≅ X :=
  extendToSucc.objSuccIso hj F X

@[reassoc]
/--
lemma `extendToSuccObjIso_hom_naturality` / 引理 `extendToSuccObjIso_hom_naturality`

English:
lemma extendToSuccObjIso_hom_naturality
  given: (i₁ i₂ : J) (hi : i₁ <= i₂) (hi₂ : i₂ <= j)
  proof: by
  dsimp [extendToSucc, extendToSuccObjIso]
  rw [extendToSucc.map_eq _ _ _ _ _ _ hi₂]; rw [assoc]; rw [assoc]; rw [Iso.inv_hom_id]; rw [comp_id]

中文:
引理 extendToSuccObjIso_hom_naturality
  条件: (i₁ i₂ : J) (hi : i₁ <= i₂) (hi₂ : i₂ <= j)
  证明: by
  dsimp [extendToSucc, extendToSuccObjIso]
  rw [extendToSucc.map_eq _ _ _ _ _ _ hi₂]; rw [assoc]; rw [assoc]; rw [Iso.inv_hom_id]; rw [comp_id]

Depends on / 依赖: Iso.inv_hom_id, comp_id, extendToSucc, extendToSucc.map_eq, extendToSuccObjIso, inv_hom_id, map_eq
-/
lemma extendToSuccObjIso_hom_naturality (i₁ i₂ : J) (hi : i₁ <= i₂) (hi₂ : i₂ <= j) :
    (extendToSucc hj F τ).map (homOfLE hi :
      ⟨i₁, hi.trans (hi₂.trans (Order.le_succ j))⟩ ⟶ ⟨i₂, hi₂.trans (Order.le_succ j)⟩) ≫
    (extendToSuccObjIso hj F τ i₂ hi₂).hom =
      (extendToSuccObjIso hj F τ i₁ (hi.trans hi₂)).hom ≫ F.map (homOfLE hi) := by
  dsimp [extendToSucc, extendToSuccObjIso]
  rw [extendToSucc.map_eq _ _ _ _ _ _ hi₂]; rw [assoc]; rw [assoc]; rw [Iso.inv_hom_id]; rw [comp_id]

/-- The isomorphism expressing that `extendToSucc hj F τ` extends `F`. -/
@[simps!]
/--
Definition of `extendToSuccRestrictionLEIso` / `extendToSuccRestrictionLEIso` 的定义

English:
definition extendToSuccRestrictionLEIso
  signature: :
  body: NatIso.ofComponents (fun i => extendToSuccObjIso hj F τ i.1 i.2) (by
    rintro ⟨i₁, h₁⟩ ⟨i₂, h₂⟩ f
    apply extendToSuccObjIso_hom_naturality)

中文:
定义 extendToSuccRestrictionLEIso
  签名: :
  定义体: NatIso.ofComponents (fun i => extendToSuccObjIso hj F τ i.1 i.2) (by
    rintro ⟨i₁, h₁⟩ ⟨i₂, h₂⟩ f
    apply extendToSuccObjIso_hom_naturality)

Depends on / 依赖: NatIso, NatIso.ofComponents, extendToSuccObjIso, extendToSuccObjIso_hom_naturality, ofComponents
-/
def extendToSuccRestrictionLEIso :
    SmallObject.restrictionLE (extendToSucc hj F τ) (Order.le_succ j) ≅ F :=
  NatIso.ofComponents (fun i => extendToSuccObjIso hj F τ i.1 i.2) (by
    rintro ⟨i₁, h₁⟩ ⟨i₂, h₂⟩ f
    apply extendToSuccObjIso_hom_naturality)

/--
lemma `extendToSucc_map` / 引理 `extendToSucc_map`

English:
lemma extendToSucc_map
  given: (i₁ i₂ : J) (hi : i₁ <= i₂) (hi₂ : i₂ <= j)
  proof: by
  rw [← extendToSuccObjIso_hom_naturality_assoc]; rw [Iso.hom_inv_id]; rw [comp_id]

中文:
引理 extendToSucc_map
  条件: (i₁ i₂ : J) (hi : i₁ <= i₂) (hi₂ : i₂ <= j)
  证明: by
  rw [← extendToSuccObjIso_hom_naturality_assoc]; rw [Iso.hom_inv_id]; rw [comp_id]

Depends on / 依赖: Iso.hom_inv_id, comp_id, extendToSuccObjIso_hom_naturality_assoc, hom_inv_id
-/
lemma extendToSucc_map (i₁ i₂ : J) (hi : i₁ <= i₂) (hi₂ : i₂ <= j) :
    (extendToSucc hj F τ).map (homOfLE hi :
      ⟨i₁, hi.trans (hi₂.trans (Order.le_succ j))⟩ ⟶ ⟨i₂, hi₂.trans (Order.le_succ j)⟩) =
      (extendToSuccObjIso hj F τ i₁ (hi.trans hi₂)).hom ≫ F.map (homOfLE hi) ≫
      (extendToSuccObjIso hj F τ i₂ hi₂).inv := by
  rw [← extendToSuccObjIso_hom_naturality_assoc]; rw [Iso.hom_inv_id]; rw [comp_id]

/--
lemma `extendToSucc_map_le_succ` / 引理 `extendToSucc_map_le_succ`

English:
lemma extendToSucc_map_le_succ
  proof: extendToSucc.map_self_succ _ _ _

中文:
引理 extendToSucc_map_le_succ
  证明: extendToSucc.map_self_succ _ _ _

Depends on / 依赖: extendToSucc, extendToSucc.map_self_succ, map_self_succ
-/
lemma extendToSucc_map_le_succ :
    (extendToSucc hj F τ).map (homOfLE (Order.le_succ j)) =
        (extendToSuccObjIso hj F τ j (by simp)).hom ≫ τ ≫
          (extendToSuccObjSuccIso hj F τ).inv :=
  extendToSucc.map_self_succ _ _ _

set_option backward.isDefEq.respectTransparency false in
/--
lemma `arrowMap_extendToSucc` / 引理 `arrowMap_extendToSucc`

English:
lemma arrowMap_extendToSucc
  given: (i₁ i₂ : J) (hi : i₁ <= i₂) (hi₂ : i₂ <= j)
  proof: by
  simp [arrowMap, extendToSucc_map hj F τ i₁ i₂ hi hi₂,
    extendToSuccObjIso, extendToSucc.objIso]

中文:
引理 arrowMap_extendToSucc
  条件: (i₁ i₂ : J) (hi : i₁ <= i₂) (hi₂ : i₂ <= j)
  证明: by
  simp [arrowMap, extendToSucc_map hj F τ i₁ i₂ hi hi₂,
    extendToSuccObjIso, extendToSucc.objIso]

Depends on / 依赖: Set.uniqueSingleton, arrowMap, extendToSucc, extendToSucc.objIso, extendToSuccObjIso, extendToSucc_map, objIso, uniqueSingleton
-/
lemma arrowMap_extendToSucc (i₁ i₂ : J) (hi : i₁ <= i₂) (hi₂ : i₂ <= j) :
    arrowMap (extendToSucc hj F τ) i₁ i₂ hi (hi₂.trans (Order.le_succ j)) =
      arrowMap F i₁ i₂ hi hi₂ := by
  simp [arrowMap, extendToSucc_map hj F τ i₁ i₂ hi hi₂,
    extendToSuccObjIso, extendToSucc.objIso]

set_option backward.isDefEq.respectTransparency false in
/--
lemma `arrowSucc_extendToSucc` / 引理 `arrowSucc_extendToSucc`

English:
lemma arrowSucc_extendToSucc
  proof: by
  simp [arrowSucc, arrowMap, extendToSucc_map_le_succ, extendToSuccObjIso,
    extendToSucc.objIso, extendToSuccObjSuccIso, extendToSucc.objSuccIso]

中文:
引理 arrowSucc_extendToSucc
  证明: by
  simp [arrowSucc, arrowMap, extendToSucc_map_le_succ, extendToSuccObjIso,
    extendToSucc.objIso, extendToSuccObjSuccIso, extendToSucc.objSuccIso]

Depends on / 依赖: arrowMap, arrowSucc, extendToSucc, extendToSucc.objIso, extendToSucc.objSuccIso, extendToSuccObjIso, extendToSuccObjSuccIso, extendToSucc_map_le_succ, objIso, objSuccIso
-/
lemma arrowSucc_extendToSucc :
    arrowSucc (extendToSucc hj F τ) j (Order.lt_succ_of_not_isMax hj) =
      Arrow.mk τ := by
  simp [arrowSucc, arrowMap, extendToSucc_map_le_succ, extendToSuccObjIso,
    extendToSucc.objIso, extendToSuccObjSuccIso, extendToSucc.objSuccIso]

end SuccStruct

end SmallObject

end CategoryTheory
