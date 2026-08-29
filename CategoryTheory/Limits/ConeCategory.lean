/-
Copyright (c) 2021 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
module

public import Mathlib.CategoryTheory.Adjunction.Comma
public import Mathlib.CategoryTheory.Comma.Over.Basic
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Terminal
public import Mathlib.CategoryTheory.Limits.Shapes.Equivalence

/-!
# Limits and the category of (co)cones

This file contains results that stem from the limit API. For the definition and the category
instance of `Cone`, please refer to `Mathlib/CategoryTheory/Limits/Cones.lean`.

## Main results
* The category of cones on `F : J ⥤ C` is equivalent to the category
  `CostructuredArrow (const J) F`.
* A cone is limiting iff it is terminal in the category of cones. As a corollary, an equivalence of
  categories of cones preserves limiting properties.

-/

@[expose] public section


namespace CategoryTheory.Limits

open CategoryTheory CategoryTheory.Functor

universe v₁ v₂ v₃ v₄ u₁ u₂ u₃ u₄

variable {J : Type u₁} [Category.{v₁} J] {K : Type u₂} [Category.{v₂} K]
variable {C : Type u₃} [Category.{v₃} C] {D : Type u₄} [Category.{v₄} D]

/-- Given a cone `c` over `F`, we can interpret the legs of `c` as structured arrows
    `c.pt ⟶ F.obj -`. -/
@[simps, implicit_reducible]
/--
Definition of `Cone.toStructuredArrow` / `Cone.toStructuredArrow` 的定义

English:
definition Cone.toStructuredArrow
  signature: {F : J ⥤ C} (c : Cone F)
  body: StructuredArrow.mk (c.π.app j)
  map f := StructuredArrow.homMk f

中文:
定义 锥.toStructuredArrow
  签名: {F : J ⥤ C} (c : 锥 F)
  定义体: StructuredArrow.mk (c.π.app j)
  map f := StructuredArrow.homMk f

Depends on / 依赖: StructuredArrow, StructuredArrow.mk
-/
def Cone.toStructuredArrow {F : J ⥤ C} (c : Cone F) : J ⥤ StructuredArrow c.pt F where
  obj j := StructuredArrow.mk (c.π.app j)
  map f := StructuredArrow.homMk f

/-- If `F` has a limit, then the limit projections can be interpreted as structured arrows
    `limit F ⟶ F.obj -`. -/
@[simps, implicit_reducible]
/--
Definition of `limit.toStructuredArrow` / `limit.toStructuredArrow` 的定义

English:
definition limit.toStructuredArrow
  signature: (F : J ⥤ C) [HasLimit F]
  body: StructuredArrow.mk (limit.π F j)
  map f := StructuredArrow.homMk f

中文:
定义 limit.toStructuredArrow
  签名: (F : J ⥤ C) [有极限 F]
  定义体: StructuredArrow.mk (limit.π F j)
  map f := StructuredArrow.homMk f

Depends on / 依赖: StructuredArrow, StructuredArrow.mk
-/
noncomputable def limit.toStructuredArrow (F : J ⥤ C) [HasLimit F] :
    J ⥤ StructuredArrow (limit F) F where
  obj j := StructuredArrow.mk (limit.π F j)
  map f := StructuredArrow.homMk f

/--
Definition of `Cone.toStructuredArrowIsoToStructuredArrow` / `Cone.toStructuredArrowIsoToStructuredArrow` 的定义

English:
definition Cone.toStructuredArrowIsoToStructuredArrow
  signature: {F : J ⥤ C} (c : Cone F)
  body: Iso.refl _

中文:
定义 锥.toStructuredArrowIsoToStructuredArrow
  签名: {F : J ⥤ C} (c : 锥 F)
  定义体: Iso.refl _

Depends on / 依赖: Iso.refl
-/
def Cone.toStructuredArrowIsoToStructuredArrow {F : J ⥤ C} (c : Cone F) :
    c.toStructuredArrow ≅ (𝟭 J).toStructuredArrow c.pt F c.π.app (by simp) :=
  Iso.refl _

set_option backward.defeqAttrib.useBackward true in
/--
Definition of `_root_.CategoryTheory.Functor.toStructuredArrowIsoToStructuredArrow` / `_root_.CategoryTheory.Functor.toStructuredArrowIsoToStructuredArrow` 的定义

English:
definition _root_.CategoryTheory.Functor.toStructuredArrowIsoToStructuredArrow
  signature: (G : J ⥤ K) (X : C)
  body: Iso.refl _

中文:
定义 _root_.范畴论.函子.toStructuredArrowIsoToStructuredArrow
  签名: (G : J ⥤ K) (X : C)
  定义体: Iso.refl _

Depends on / 依赖: Iso.refl
-/
def _root_.CategoryTheory.Functor.toStructuredArrowIsoToStructuredArrow (G : J ⥤ K) (X : C)
    (F : K ⥤ C) (f : (Y : J) -> X ⟶ F.obj (G.obj Y))
    (h : forall {Y Z : J} (g : Y ⟶ Z), f Y ≫ F.map (G.map g) = f Z) :
    G.toStructuredArrow X F f h ≅
      (Cone.mk X ⟨f, by simp [h]⟩).toStructuredArrow ⋙ StructuredArrow.pre _ _ _ :=
  Iso.refl _

/-- Interpreting the legs of a cone as a structured arrow and then forgetting the arrow again does
    nothing. -/
@[simps!]
/--
Definition of `Cone.toStructuredArrowCompProj` / `Cone.toStructuredArrowCompProj` 的定义

English:
definition Cone.toStructuredArrowCompProj
  signature: {F : J ⥤ C} (c : Cone F)
  body: Iso.refl _

@[simp]

中文:
定义 锥.toStructuredArrowCompProj
  签名: {F : J ⥤ C} (c : 锥 F)
  定义体: Iso.refl _

@[simp]

Depends on / 依赖: Iso.refl
-/
def Cone.toStructuredArrowCompProj {F : J ⥤ C} (c : Cone F) :
    c.toStructuredArrow ⋙ StructuredArrow.proj _ _ ≅ 𝟭 J :=
  Iso.refl _

@[simp]
/--
lemma `Cone.toStructuredArrow_comp_proj` / 引理 `Cone.toStructuredArrow_comp_proj`

English:
lemma Cone.toStructuredArrow_comp_proj
  given: {F : J ⥤ C} (c : Cone F)
  proof: rfl

中文:
引理 锥.toStructuredArrow_comp_proj
  条件: {F : J ⥤ C} (c : 锥 F)
  证明: rfl
-/
lemma Cone.toStructuredArrow_comp_proj {F : J ⥤ C} (c : Cone F) :
    c.toStructuredArrow ⋙ StructuredArrow.proj _ _ = 𝟭 J :=
  rfl

/-- Interpreting the legs of a cone as a structured arrow, interpreting this arrow as an arrow over
    the cone point, and finally forgetting the arrow is the same as just applying the functor the
    cone was over. -/
@[simps!]
/--
Definition of `Cone.toStructuredArrowCompToUnderCompForget` / `Cone.toStructuredArrowCompToUnderCompForget` 的定义

English:
definition Cone.toStructuredArrowCompToUnderCompForget
  signature: {F : J ⥤ C} (c : Cone F)
  body: Iso.refl _

@[simp]

中文:
定义 锥.toStructuredArrowCompToUnderCompForget
  签名: {F : J ⥤ C} (c : 锥 F)
  定义体: Iso.refl _

@[simp]

Depends on / 依赖: Iso.refl
-/
def Cone.toStructuredArrowCompToUnderCompForget {F : J ⥤ C} (c : Cone F) :
    c.toStructuredArrow ⋙ StructuredArrow.toUnder _ _ ⋙ Under.forget _ ≅ F :=
  Iso.refl _

@[simp]
/--
lemma `Cone.toStructuredArrow_comp_toUnder_comp_forget` / 引理 `Cone.toStructuredArrow_comp_toUnder_comp_forget`

English:
lemma Cone.toStructuredArrow_comp_toUnder_comp_forget
  given: {F : J ⥤ C} (c : Cone F)
  proof: rfl

中文:
引理 锥.toStructuredArrow_comp_toUnder_comp_forget
  条件: {F : J ⥤ C} (c : 锥 F)
  证明: rfl
-/
lemma Cone.toStructuredArrow_comp_toUnder_comp_forget {F : J ⥤ C} (c : Cone F) :
    c.toStructuredArrow ⋙ StructuredArrow.toUnder _ _ ⋙ Under.forget _ = F :=
  rfl

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- A cone `c` on `F : J ⥤ C` lifts to a cone in `Over c.pt` with cone point `𝟙 c.pt`. -/
@[simps]
/--
Definition of `Cone.toUnder` / `Cone.toUnder` 的定义

English:
definition Cone.toUnder
  signature: {F : J ⥤ C} (c : Cone F)
  body: Under.mk (𝟙 c.pt)
  π := { app := fun j => Under.homMk (c.π.app j) (by simp) }

中文:
定义 锥.toUnder
  签名: {F : J ⥤ C} (c : 锥 F)
  定义体: Under.mk (𝟙 c.pt)
  π := { app := fun j => Under.homMk (c.π.app j) (by simp) }

Depends on / 依赖: Under.mk, c.pt
-/
def Cone.toUnder {F : J ⥤ C} (c : Cone F) :
    Cone (c.toStructuredArrow ⋙ StructuredArrow.toUnder _ _) where
  pt := Under.mk (𝟙 c.pt)
  π := { app := fun j => Under.homMk (c.π.app j) (by simp) }

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/--
Definition of `limit.toUnder` / `limit.toUnder` 的定义

English:
definition limit.toUnder
  signature: (F : J ⥤ C) [HasLimit F]
  body: Under.mk (𝟙 (limit F))
  π := { app := fun j => Under.homMk (limit.π F j) (by simp) }

中文:
定义 limit.toUnder
  签名: (F : J ⥤ C) [有极限 F]
  定义体: Under.mk (𝟙 (limit F))
  π := { app := fun j => Under.homMk (limit.π F j) (by simp) }

Depends on / 依赖: Under.mk
-/
noncomputable def limit.toUnder (F : J ⥤ C) [HasLimit F] :
    Cone (limit.toStructuredArrow F ⋙ StructuredArrow.toUnder _ _) where
  pt := Under.mk (𝟙 (limit F))
  π := { app := fun j => Under.homMk (limit.π F j) (by simp) }

set_option backward.isDefEq.respectTransparency.types false in
/-- `c.toUnder` is a lift of `c` under the forgetful functor. -/
@[simps!]
/--
Definition of `Cone.mapConeToUnder` / `Cone.mapConeToUnder` 的定义

English:
definition Cone.mapConeToUnder
  signature: {F : J ⥤ C} (c : Cone F)
  body: Iso.refl _

中文:
定义 锥.mapConeToUnder
  签名: {F : J ⥤ C} (c : 锥 F)
  定义体: Iso.refl _

Depends on / 依赖: Iso.refl
-/
def Cone.mapConeToUnder {F : J ⥤ C} (c : Cone F) : (Under.forget c.pt).mapCone c.toUnder ≅ c :=
  Iso.refl _

set_option backward.defeqAttrib.useBackward true in
/-- Given a diagram of `StructuredArrow X F`s, we may obtain a cone with cone point `X`. -/
@[simps!]
/--
Definition of `Cone.fromStructuredArrow` / `Cone.fromStructuredArrow` 的定义

English:
definition Cone.fromStructuredArrow
  signature: (F : C ⥤ D) {X : D} (G : J ⥤ StructuredArrow X F)
  body: X
  π := { app := fun j => (G.obj j).hom }

中文:
定义 锥.fromStructuredArrow
  签名: (F : C ⥤ D) {X : D} (G : J ⥤ 结构化箭头 X F)
  定义体: X
  π := { app := fun j => (G.obj j).hom }
-/
def Cone.fromStructuredArrow (F : C ⥤ D) {X : D} (G : J ⥤ StructuredArrow X F) :
    Cone (G ⋙ StructuredArrow.proj X F ⋙ F) where
  pt := X
  π := { app := fun j => (G.obj j).hom }

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- Given a cone `c : Cone K` and a map `f : X ⟶ F.obj c.X`, we can construct a cone of structured
arrows over `X` with `f` as the cone point.
-/
@[simps]
/--
Definition of `Cone.toStructuredArrowCone` / `Cone.toStructuredArrowCone` 的定义

English:
definition Cone.toStructuredArrowCone
  signature: {K : J ⥤ C} (c : Cone K) (F : C ⥤ D) {X : D} (f : X ⟶ F.obj c.pt)
  body: StructuredArrow.mk f
  π := { app := fun j => StructuredArrow.homMk (c.π.app j) rfl }

中文:
定义 锥.toStructuredArrowCone
  签名: {K : J ⥤ C} (c : 锥 K) (F : C ⥤ D) {X : D} (f : X ⟶ F.obj c.pt)
  定义体: StructuredArrow.mk f
  π := { app := fun j => StructuredArrow.homMk (c.π.app j) rfl }

Depends on / 依赖: StructuredArrow, StructuredArrow.mk
-/
def Cone.toStructuredArrowCone {K : J ⥤ C} (c : Cone K) (F : C ⥤ D) {X : D} (f : X ⟶ F.obj c.pt) :
    Cone ((F.mapCone c).toStructuredArrow ⋙ StructuredArrow.map f ⋙ StructuredArrow.pre _ K F) where
  pt := StructuredArrow.mk f
  π := { app := fun j => StructuredArrow.homMk (c.π.app j) rfl }

set_option backward.defeqAttrib.useBackward true in
/-- Construct an object of the category `(Δ ↓ F)` from a cone on `F`. This is part of an
    equivalence, see `Cone.equivCostructuredArrow`. -/
@[simps]
/--
Definition of `Cone.toCostructuredArrow` / `Cone.toCostructuredArrow` 的定义

English:
definition Cone.toCostructuredArrow
  signature: (F : J ⥤ C)
  body: CostructuredArrow.mk c.π
  map f := CostructuredArrow.homMk f.hom

中文:
定义 锥.toCostructuredArrow
  签名: (F : J ⥤ C)
  定义体: CostructuredArrow.mk c.π
  map f := CostructuredArrow.homMk f.hom

Depends on / 依赖: CostructuredArrow, CostructuredArrow.mk
-/
def Cone.toCostructuredArrow (F : J ⥤ C) : Cone F ⥤ CostructuredArrow (const J) F where
  obj c := CostructuredArrow.mk c.π
  map f := CostructuredArrow.homMk f.hom

set_option backward.defeqAttrib.useBackward true in
/-- Construct a cone on `F` from an object of the category `(Δ ↓ F)`. This is part of an
    equivalence, see `Cone.equivCostructuredArrow`. -/
@[simps]
/--
Definition of `Cone.fromCostructuredArrow` / `Cone.fromCostructuredArrow` 的定义

English:
definition Cone.fromCostructuredArrow
  signature: (F : J ⥤ C)
  body: ⟨c.left, c.hom⟩
  map f :=
    { hom := f.left
      w := fun j => by
        convert! congr_fun (congr_arg NatTrans.app f.w) j
        simp }

中文:
定义 锥.fromCostructuredArrow
  签名: (F : J ⥤ C)
  定义体: ⟨c.left, c.hom⟩
  map f :=
    { hom := f.left
      w := fun j => by
        convert! congr_fun (congr_arg NatTrans.app f.w) j
        simp }

Depends on / 依赖: c.hom, c.left
-/
def Cone.fromCostructuredArrow (F : J ⥤ C) : CostructuredArrow (const J) F ⥤ Cone F where
  obj c := ⟨c.left, c.hom⟩
  map f :=
    { hom := f.left
      w := fun j => by
        convert! congr_fun (congr_arg NatTrans.app f.w) j
        simp }

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- The category of cones on `F` is just the comma category `(Δ ↓ F)`, where `Δ` is the constant
    functor. -/
@[simps]
/--
Definition of `Cone.equivCostructuredArrow` / `Cone.equivCostructuredArrow` 的定义

English:
definition Cone.equivCostructuredArrow
  signature: (F : J ⥤ C)
  body: Cone.toCostructuredArrow F
  inverse := Cone.fromCostructuredArrow F
  unitIso := NatIso.ofComponents Cone.eta
  counitIso := NatIso.ofComponents fun _ => (CostructuredArrow.eta _).symm

中文:
定义 锥.equivCostructuredArrow
  签名: (F : J ⥤ C)
  定义体: Cone.toCostructuredArrow F
  inverse := Cone.fromCostructuredArrow F
  unitIso := NatIso.ofComponents Cone.eta
  counitIso := NatIso.ofComponents fun _ => (CostructuredArrow.eta _).symm

Depends on / 依赖: Cone.toCostructuredArrow, toCostructuredArrow
-/
def Cone.equivCostructuredArrow (F : J ⥤ C) : Cone F ≌ CostructuredArrow (const J) F where
  functor := Cone.toCostructuredArrow F
  inverse := Cone.fromCostructuredArrow F
  unitIso := NatIso.ofComponents Cone.eta
  counitIso := NatIso.ofComponents fun _ => (CostructuredArrow.eta _).symm

/--
Definition of `Cone.isLimitEquivIsTerminal` / `Cone.isLimitEquivIsTerminal` 的定义

English:
definition Cone.isLimitEquivIsTerminal
  signature: {F : J ⥤ C} (c : Cone F)
  body: IsLimit.isoUniqueConeMorphism.toEquiv.trans
    { toFun := fun _ => IsTerminal.ofUnique _
      invFun := fun h s => ⟨⟨IsTerminal.from h s⟩, fun a => IsTerminal.hom_ext h a _⟩
      left_inv := by cat_disch
      right_inv := by cat_disch }

中文:
定义 锥.isLimitEquivIsTerminal
  签名: {F : J ⥤ C} (c : 锥 F)
  定义体: IsLimit.isoUniqueConeMorphism.toEquiv.trans
    { toFun := fun _ => IsTerminal.ofUnique _
      invFun := fun h s => ⟨⟨IsTerminal.from h s⟩, fun a => IsTerminal.hom_ext h a _⟩
      left_inv := by cat_disch
      right_inv := by cat_disch }

Depends on / 依赖: IsLimit, IsLimit.isoUniqueConeMorphism.toEquiv.trans, IsTerminal, IsTerminal.from, IsTerminal.hom_ext, IsTerminal.ofUnique, cat_disch, hom_ext, invFun, isoUniqueConeMorphism, left_inv, ofUnique, right_inv, toEquiv
-/
def Cone.isLimitEquivIsTerminal {F : J ⥤ C} (c : Cone F) : IsLimit c ≃ IsTerminal c :=
  IsLimit.isoUniqueConeMorphism.toEquiv.trans
    { toFun := fun _ => IsTerminal.ofUnique _
      invFun := fun h s => ⟨⟨IsTerminal.from h s⟩, fun a => IsTerminal.hom_ext h a _⟩
      left_inv := by cat_disch
      right_inv := by cat_disch }

/--
theorem `hasLimit_iff_hasTerminal_cone` / 定理 `hasLimit_iff_hasTerminal_cone`

English:
theorem hasLimit_iff_hasTerminal_cone
  given: (F : J ⥤ C)
  statement: HasLimit F ↔ HasTerminal (Cone F)
  proof: ⟨fun _ => (Cone.isLimitEquivIsTerminal _ (limit.isLimit F)).hasTerminal, fun h =>
    haveI : HasTerminal (Cone F) := h
    ⟨⟨⟨⊤_ _, (Cone.isLimitEquivIsTerminal _).symm terminalIsTerminal⟩⟩⟩⟩

中文:
定理 hasLimit_iff_hasTerminal_cone
  条件: (F : J ⥤ C)
  结论: 有极限 F ↔ 有终止 (锥 F)
  证明: ⟨fun _ => (Cone.isLimitEquivIsTerminal _ (limit.isLimit F)).hasTerminal, fun h =>
    haveI : HasTerminal (Cone F) := h
    ⟨⟨⟨⊤_ _, (Cone.isLimitEquivIsTerminal _).symm terminalIsTerminal⟩⟩⟩⟩

Depends on / 依赖: Cone.isLimitEquivIsTerminal, HasTerminal, hasTerminal, isLimit, isLimitEquivIsTerminal, limit.isLimit, terminalIsTerminal
-/
theorem hasLimit_iff_hasTerminal_cone (F : J ⥤ C) : HasLimit F ↔ HasTerminal (Cone F) :=
  ⟨fun _ => (Cone.isLimitEquivIsTerminal _ (limit.isLimit F)).hasTerminal, fun h =>
    haveI : HasTerminal (Cone F) := h
    ⟨⟨⟨⊤_ _, (Cone.isLimitEquivIsTerminal _).symm terminalIsTerminal⟩⟩⟩⟩

/--
theorem `hasLimitsOfShape_iff_isLeftAdjoint_const` / 定理 `hasLimitsOfShape_iff_isLeftAdjoint_const`

English:
theorem hasLimitsOfShape_iff_isLeftAdjoint_const
  proof: calc
    HasLimitsOfShape J C ↔ forall F : J ⥤ C, HasLimit F :=
      ⟨fun h => h.has_limit, fun h => HasLimitsOfShape.mk⟩
    _ ↔ forall F : J ⥤ C, HasTerminal (Cone F) := forall_congr' hasLimit_iff_hasTerminal_cone
    _ ↔ forall F : J ⥤ C, HasTerminal (CostructuredArrow (const J) F) :=
      (for

中文:
定理 hasLimitsOfShape_iff_isLeftAdjoint_const
  证明: calc
    HasLimitsOfShape J C ↔ forall F : J ⥤ C, HasLimit F :=
      ⟨fun h => h.has_limit, fun h => HasLimitsOfShape.mk⟩
    _ ↔ forall F : J ⥤ C, HasTerminal (Cone F) := forall_congr' hasLimit_iff_hasTerminal_cone
    _ ↔ forall F : J ⥤ C, HasTerminal (CostructuredArrow (const J) F) :=
      (for

Depends on / 依赖: Cone.equivCostructuredArrow, CostructuredArrow, HasLimit, HasLimitsOfShape, HasLimitsOfShape.mk, HasTerminal, IsLeftAdjoint, equivCostructuredArrow, forall_congr, h.has_limit, hasLimit_iff_hasTerminal_cone, hasTerminal_iff, has_limit, isLeftAdjoint_iff_hasTerminal_costructuredArrow, isLeftAdjoint_iff_hasTerminal_costructuredArrow.symm
-/
theorem hasLimitsOfShape_iff_isLeftAdjoint_const :
    HasLimitsOfShape J C ↔ IsLeftAdjoint (const J : C ⥤ _) :=
  calc
    HasLimitsOfShape J C ↔ forall F : J ⥤ C, HasLimit F :=
      ⟨fun h => h.has_limit, fun h => HasLimitsOfShape.mk⟩
    _ ↔ forall F : J ⥤ C, HasTerminal (Cone F) := forall_congr' hasLimit_iff_hasTerminal_cone
    _ ↔ forall F : J ⥤ C, HasTerminal (CostructuredArrow (const J) F) :=
      (forall_congr' fun F => (Cone.equivCostructuredArrow F).hasTerminal_iff)
    _ ↔ (IsLeftAdjoint (const J : C ⥤ _)) :=
      isLeftAdjoint_iff_hasTerminal_costructuredArrow.symm

/--
theorem `IsLimit.liftConeMorphism_eq_isTerminal_from` / 定理 `IsLimit.liftConeMorphism_eq_isTerminal_from`

English:
theorem IsLimit.liftConeMorphism_eq_isTerminal_from
  statement: {F : J ⥤ C} {c : Cone F} (hc : IsLimit c)
  proof: rfl

中文:
定理 是极限.liftConeMorphism_eq_isTerminal_from
  结论: {F : J ⥤ C} {c : 锥 F} (hc : 是极限 c)
  证明: rfl
-/
theorem IsLimit.liftConeMorphism_eq_isTerminal_from {F : J ⥤ C} {c : Cone F} (hc : IsLimit c)
    (s : Cone F) : hc.liftConeMorphism s = IsTerminal.from (Cone.isLimitEquivIsTerminal _ hc) _ :=
  rfl

/--
theorem `IsTerminal.from_eq_liftConeMorphism` / 定理 `IsTerminal.from_eq_liftConeMorphism`

English:
theorem IsTerminal.from_eq_liftConeMorphism
  statement: {F : J ⥤ C} {c : Cone F} (hc : IsTerminal c)
  proof: (IsLimit.liftConeMorphism_eq_isTerminal_from (c.isLimitEquivIsTerminal.symm hc) s).symm

中文:
定理 是终止.from_eq_liftConeMorphism
  结论: {F : J ⥤ C} {c : 锥 F} (hc : 是终止 c)
  证明: (IsLimit.liftConeMorphism_eq_isTerminal_from (c.isLimitEquivIsTerminal.symm hc) s).symm

Depends on / 依赖: IsLimit, IsLimit.liftConeMorphism_eq_isTerminal_from, c.isLimitEquivIsTerminal.symm, isLimitEquivIsTerminal, liftConeMorphism_eq_isTerminal_from
-/
theorem IsTerminal.from_eq_liftConeMorphism {F : J ⥤ C} {c : Cone F} (hc : IsTerminal c)
    (s : Cone F) :
    IsTerminal.from hc s = ((Cone.isLimitEquivIsTerminal _).symm hc).liftConeMorphism s :=
  (IsLimit.liftConeMorphism_eq_isTerminal_from (c.isLimitEquivIsTerminal.symm hc) s).symm

/--
Definition of `IsLimit.ofPreservesConeTerminal` / `IsLimit.ofPreservesConeTerminal` 的定义

English:
definition IsLimit.ofPreservesConeTerminal
  signature: {F : J ⥤ C} {F' : K ⥤ D} (G : Cone F ⥤ Cone F')
  body: (Cone.isLimitEquivIsTerminal _).symm (Cone.isLimitEquivIsTerminal _ hc).isTerminalObj _ _

中文:
定义 是极限.ofPreservesConeTerminal
  签名: {F : J ⥤ C} {F' : K ⥤ D} (G : 锥 F ⥤ 锥 F')
  定义体: (Cone.isLimitEquivIsTerminal _).symm (Cone.isLimitEquivIsTerminal _ hc).isTerminalObj _ _

Depends on / 依赖: Cone.isLimitEquivIsTerminal, isLimitEquivIsTerminal, isTerminalObj
-/
noncomputable def IsLimit.ofPreservesConeTerminal {F : J ⥤ C} {F' : K ⥤ D} (G : Cone F ⥤ Cone F')
    [PreservesLimit (Functor.empty.{0} _) G] {c : Cone F} (hc : IsLimit c) : IsLimit (G.obj c) :=
(Cone.isLimitEquivIsTerminal _).symm (Cone.isLimitEquivIsTerminal _ hc).isTerminalObj _ _

/--
Definition of `IsLimit.ofReflectsConeTerminal` / `IsLimit.ofReflectsConeTerminal` 的定义

English:
definition IsLimit.ofReflectsConeTerminal
  signature: {F : J ⥤ C} {F' : K ⥤ D} (G : Cone F ⥤ Cone F')
  body: (Cone.isLimitEquivIsTerminal _).symm (Cone.isLimitEquivIsTerminal _ hc).isTerminalOfObj _ _

中文:
定义 是极限.ofReflectsConeTerminal
  签名: {F : J ⥤ C} {F' : K ⥤ D} (G : 锥 F ⥤ 锥 F')
  定义体: (Cone.isLimitEquivIsTerminal _).symm (Cone.isLimitEquivIsTerminal _ hc).isTerminalOfObj _ _

Depends on / 依赖: Cone.isLimitEquivIsTerminal, isLimitEquivIsTerminal, isTerminalOfObj
-/
noncomputable def IsLimit.ofReflectsConeTerminal {F : J ⥤ C} {F' : K ⥤ D} (G : Cone F ⥤ Cone F')
    [ReflectsLimit (Functor.empty.{0} _) G] {c : Cone F} (hc : IsLimit (G.obj c)) : IsLimit c :=
(Cone.isLimitEquivIsTerminal _).symm (Cone.isLimitEquivIsTerminal _ hc).isTerminalOfObj _ _

/-- Given a cocone `c` over `F`, we can interpret the legs of `c` as costructured arrows
    `F.obj - ⟶ c.pt`. -/
@[simps]
/--
Definition of `Cocone.toCostructuredArrow` / `Cocone.toCostructuredArrow` 的定义

English:
definition Cocone.toCostructuredArrow
  signature: {F : J ⥤ C} (c : Cocone F)
  body: CostructuredArrow.mk (c.ι.app j)
  map f := CostructuredArrow.homMk f

中文:
定义 余锥.toCostructuredArrow
  签名: {F : J ⥤ C} (c : 余锥 F)
  定义体: CostructuredArrow.mk (c.ι.app j)
  map f := CostructuredArrow.homMk f

Depends on / 依赖: CostructuredArrow, CostructuredArrow.mk
-/
def Cocone.toCostructuredArrow {F : J ⥤ C} (c : Cocone F) : J ⥤ CostructuredArrow F c.pt where
  obj j := CostructuredArrow.mk (c.ι.app j)
  map f := CostructuredArrow.homMk f

/-- If `F` has a colimit, then the colimit inclusions can be interpreted as costructured arrows
    `F.obj - ⟶ colimit F`. -/
@[simps]
/--
Definition of `colimit.toCostructuredArrow` / `colimit.toCostructuredArrow` 的定义

English:
definition colimit.toCostructuredArrow
  signature: (F : J ⥤ C) [HasColimit F]
  body: CostructuredArrow.mk (colimit.ι F j)
  map f := CostructuredArrow.homMk f

中文:
定义 colimit.toCostructuredArrow
  签名: (F : J ⥤ C) [有余极限 F]
  定义体: CostructuredArrow.mk (colimit.ι F j)
  map f := CostructuredArrow.homMk f

Depends on / 依赖: CostructuredArrow, CostructuredArrow.mk, colimit
-/
noncomputable def colimit.toCostructuredArrow (F : J ⥤ C) [HasColimit F] :
    J ⥤ CostructuredArrow F (colimit F) where
  obj j := CostructuredArrow.mk (colimit.ι F j)
  map f := CostructuredArrow.homMk f

set_option backward.isDefEq.respectTransparency.types false in
/--
Definition of `Cocone.toCostructuredArrowIsoToCostructuredArrow` / `Cocone.toCostructuredArrowIsoToCostructuredArrow` 的定义

English:
definition Cocone.toCostructuredArrowIsoToCostructuredArrow
  signature: {F : J ⥤ C} (c : Cocone F)
  body: Iso.refl _

中文:
定义 余锥.toCostructuredArrowIsoToCostructuredArrow
  签名: {F : J ⥤ C} (c : 余锥 F)
  定义体: Iso.refl _

Depends on / 依赖: Iso.refl
-/
def Cocone.toCostructuredArrowIsoToCostructuredArrow {F : J ⥤ C} (c : Cocone F) :
    c.toCostructuredArrow ≅ (𝟭 J).toCostructuredArrow F c.pt c.ι.app (by simp) :=
  Iso.refl _

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/--
Definition of `_root_.CategoryTheory.Functor.toCostructuredArrowIsoToCostructuredArrow` / `_root_.CategoryTheory.Functor.toCostructuredArrowIsoToCostructuredArrow` 的定义

English:
definition _root_.CategoryTheory.Functor.toCostructuredArrowIsoToCostructuredArrow
  signature: (G : J ⥤ K)
  body: Iso.refl _

中文:
定义 _root_.范畴论.函子.toCostructuredArrowIsoToCostructuredArrow
  签名: (G : J ⥤ K)
  定义体: Iso.refl _

Depends on / 依赖: Iso.refl
-/
def _root_.CategoryTheory.Functor.toCostructuredArrowIsoToCostructuredArrow (G : J ⥤ K)
    (F : K ⥤ C) (X : C) (f : (Y : J) -> F.obj (G.obj Y) ⟶ X)
    (h : forall {Y Z : J} (g : Y ⟶ Z), F.map (G.map g) ≫ f Z = f Y) :
    G.toCostructuredArrow F X f h ≅
      (Cocone.mk X ⟨f, by simp [h]⟩).toCostructuredArrow ⋙ CostructuredArrow.pre _ _ _ :=
  Iso.refl _

set_option backward.isDefEq.respectTransparency.types false in
/-- Interpreting the legs of a cocone as a costructured arrow and then forgetting the arrow again
    does nothing. -/
@[simps!]
/--
Definition of `Cocone.toCostructuredArrowCompProj` / `Cocone.toCostructuredArrowCompProj` 的定义

English:
definition Cocone.toCostructuredArrowCompProj
  signature: {F : J ⥤ C} (c : Cocone F)
  body: Iso.refl _

中文:
定义 余锥.toCostructuredArrowCompProj
  签名: {F : J ⥤ C} (c : 余锥 F)
  定义体: Iso.refl _

Depends on / 依赖: Iso.refl
-/
def Cocone.toCostructuredArrowCompProj {F : J ⥤ C} (c : Cocone F) :
    c.toCostructuredArrow ⋙ CostructuredArrow.proj _ _ ≅ 𝟭 J :=
  Iso.refl _

set_option backward.isDefEq.respectTransparency.types false in
@[simp]
/--
lemma `Cocone.toCostructuredArrow_comp_proj` / 引理 `Cocone.toCostructuredArrow_comp_proj`

English:
lemma Cocone.toCostructuredArrow_comp_proj
  given: {F : J ⥤ C} (c : Cocone F)
  proof: rfl

中文:
引理 余锥.toCostructuredArrow_comp_proj
  条件: {F : J ⥤ C} (c : 余锥 F)
  证明: rfl
-/
lemma Cocone.toCostructuredArrow_comp_proj {F : J ⥤ C} (c : Cocone F) :
    c.toCostructuredArrow ⋙ CostructuredArrow.proj _ _ = 𝟭 J :=
  rfl

set_option backward.isDefEq.respectTransparency.types false in
/-- Interpreting the legs of a cocone as a costructured arrow, interpreting this arrow as an arrow
    over the cocone point, and finally forgetting the arrow is the same as just applying the
    functor the cocone was over. -/
@[simps!]
/--
Definition of `Cocone.toCostructuredArrowCompToOverCompForget` / `Cocone.toCostructuredArrowCompToOverCompForget` 的定义

English:
definition Cocone.toCostructuredArrowCompToOverCompForget
  signature: {F : J ⥤ C} (c : Cocone F)
  body: Iso.refl _

中文:
定义 余锥.toCostructuredArrowCompToOverCompForget
  签名: {F : J ⥤ C} (c : 余锥 F)
  定义体: Iso.refl _

Depends on / 依赖: Iso.refl
-/
def Cocone.toCostructuredArrowCompToOverCompForget {F : J ⥤ C} (c : Cocone F) :
    c.toCostructuredArrow ⋙ CostructuredArrow.toOver _ _ ⋙ Over.forget _ ≅ F :=
  Iso.refl _

set_option backward.isDefEq.respectTransparency.types false in
@[simp]
/--
lemma `Cocone.toCostructuredArrow_comp_toOver_comp_forget` / 引理 `Cocone.toCostructuredArrow_comp_toOver_comp_forget`

English:
lemma Cocone.toCostructuredArrow_comp_toOver_comp_forget
  given: {F : J ⥤ C} (c : Cocone F)
  proof: rfl

中文:
引理 余锥.toCostructuredArrow_comp_toOver_comp_forget
  条件: {F : J ⥤ C} (c : 余锥 F)
  证明: rfl
-/
lemma Cocone.toCostructuredArrow_comp_toOver_comp_forget {F : J ⥤ C} (c : Cocone F) :
    c.toCostructuredArrow ⋙ CostructuredArrow.toOver _ _ ⋙ Over.forget _ = F :=
  rfl

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- A cocone `c` on `F : J ⥤ C` lifts to a cocone in `Over c.pt` with cone point `𝟙 c.pt`. -/
@[simps]
/--
Definition of `Cocone.toOver` / `Cocone.toOver` 的定义

English:
definition Cocone.toOver
  signature: {F : J ⥤ C} (c : Cocone F)
  body: Over.mk (𝟙 c.pt)
  ι := { app := fun j => Over.homMk (c.ι.app j) (by simp) }

中文:
定义 余锥.toOver
  签名: {F : J ⥤ C} (c : 余锥 F)
  定义体: Over.mk (𝟙 c.pt)
  ι := { app := fun j => Over.homMk (c.ι.app j) (by simp) }

Depends on / 依赖: Over.mk, c.pt
-/
def Cocone.toOver {F : J ⥤ C} (c : Cocone F) :
    Cocone (c.toCostructuredArrow ⋙ CostructuredArrow.toOver _ _) where
  pt := Over.mk (𝟙 c.pt)
  ι := { app := fun j => Over.homMk (c.ι.app j) (by simp) }

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- The colimit cocone for `F : J ⥤ C` lifts to a cocone in `Over (colimit F)` with cone point
    `𝟙 (colimit F)`. This is automatically also a colimit cocone. -/
@[simps]
/--
Definition of `colimit.toOver` / `colimit.toOver` 的定义

English:
definition colimit.toOver
  signature: (F : J ⥤ C) [HasColimit F]
  body: Over.mk (𝟙 (colimit F))
  ι := { app := fun j => Over.homMk (colimit.ι F j) (by simp) }

中文:
定义 colimit.toOver
  签名: (F : J ⥤ C) [有余极限 F]
  定义体: Over.mk (𝟙 (colimit F))
  ι := { app := fun j => Over.homMk (colimit.ι F j) (by simp) }

Depends on / 依赖: Over.mk, colimit
-/
noncomputable def colimit.toOver (F : J ⥤ C) [HasColimit F] :
    Cocone (colimit.toCostructuredArrow F ⋙ CostructuredArrow.toOver _ _) where
  pt := Over.mk (𝟙 (colimit F))
  ι := { app := fun j => Over.homMk (colimit.ι F j) (by simp) }

set_option backward.isDefEq.respectTransparency.types false in
/-- `c.toOver` is a lift of `c` under the forgetful functor. -/
@[simps!]
/--
Definition of `Cocone.mapCoconeToOver` / `Cocone.mapCoconeToOver` 的定义

English:
definition Cocone.mapCoconeToOver
  signature: {F : J ⥤ C} (c : Cocone F)
  body: Iso.refl _

中文:
定义 余锥.mapCoconeToOver
  签名: {F : J ⥤ C} (c : 余锥 F)
  定义体: Iso.refl _

Depends on / 依赖: Iso.refl
-/
def Cocone.mapCoconeToOver {F : J ⥤ C} (c : Cocone F) : (Over.forget c.pt).mapCocone c.toOver ≅ c :=
  Iso.refl _

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- Given a diagram `CostructuredArrow F X`s, we may obtain a cocone with cone point `X`. -/
@[simps!]
/--
Definition of `Cocone.fromCostructuredArrow` / `Cocone.fromCostructuredArrow` 的定义

English:
definition Cocone.fromCostructuredArrow
  signature: (F : C ⥤ D) {X : D} (G : J ⥤ CostructuredArrow F X)
  body: X
  ι := { app := fun j => (G.obj j).hom }

中文:
定义 余锥.fromCostructuredArrow
  签名: (F : C ⥤ D) {X : D} (G : J ⥤ CostructuredArrow F X)
  定义体: X
  ι := { app := fun j => (G.obj j).hom }
-/
def Cocone.fromCostructuredArrow (F : C ⥤ D) {X : D} (G : J ⥤ CostructuredArrow F X) :
    Cocone (G ⋙ CostructuredArrow.proj F X ⋙ F) where
  pt := X
  ι := { app := fun j => (G.obj j).hom }

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- Given a cocone `c : Cocone K` and a map `f : F.obj c.X ⟶ X`, we can construct a cocone of
    costructured arrows over `X` with `f` as the cone point. -/
@[simps]
/--
Definition of `Cocone.toCostructuredArrowCocone` / `Cocone.toCostructuredArrowCocone` 的定义

English:
definition Cocone.toCostructuredArrowCocone
  signature: {K : J ⥤ C} (c : Cocone K) (F : C ⥤ D) {X : D}
  body: CostructuredArrow.mk f
  ι := { app := fun j => CostructuredArrow.homMk (c.ι.app j) rfl }

中文:
定义 余锥.toCostructuredArrowCocone
  签名: {K : J ⥤ C} (c : 余锥 K) (F : C ⥤ D) {X : D}
  定义体: CostructuredArrow.mk f
  ι := { app := fun j => CostructuredArrow.homMk (c.ι.app j) rfl }

Depends on / 依赖: CostructuredArrow, CostructuredArrow.mk
-/
def Cocone.toCostructuredArrowCocone {K : J ⥤ C} (c : Cocone K) (F : C ⥤ D) {X : D}
    (f : F.obj c.pt ⟶ X) : Cocone ((F.mapCocone c).toCostructuredArrow ⋙
      CostructuredArrow.map f ⋙ CostructuredArrow.pre _ _ _) where
  pt := CostructuredArrow.mk f
  ι := { app := fun j => CostructuredArrow.homMk (c.ι.app j) rfl }

set_option backward.defeqAttrib.useBackward true in
/-- Construct an object of the category `(F ↓ Δ)` from a cocone on `F`. This is part of an
    equivalence, see `Cocone.equivStructuredArrow`. -/
@[simps]
/--
Definition of `Cocone.toStructuredArrow` / `Cocone.toStructuredArrow` 的定义

English:
definition Cocone.toStructuredArrow
  signature: (F : J ⥤ C)
  body: StructuredArrow.mk c.ι
  map f := StructuredArrow.homMk f.hom

中文:
定义 余锥.toStructuredArrow
  签名: (F : J ⥤ C)
  定义体: StructuredArrow.mk c.ι
  map f := StructuredArrow.homMk f.hom

Depends on / 依赖: StructuredArrow, StructuredArrow.mk
-/
def Cocone.toStructuredArrow (F : J ⥤ C) : Cocone F ⥤ StructuredArrow F (const J) where
  obj c := StructuredArrow.mk c.ι
  map f := StructuredArrow.homMk f.hom

set_option backward.defeqAttrib.useBackward true in
/-- Construct a cocone on `F` from an object of the category `(F ↓ Δ)`. This is part of an
    equivalence, see `Cocone.equivStructuredArrow`. -/
@[simps]
/--
Definition of `Cocone.fromStructuredArrow` / `Cocone.fromStructuredArrow` 的定义

English:
definition Cocone.fromStructuredArrow
  signature: (F : J ⥤ C)
  body: ⟨c.right, c.hom⟩
  map f :=
    { hom := f.right
      w j := by simp [dsimp% congr_app f.w j] }

中文:
定义 余锥.fromStructuredArrow
  签名: (F : J ⥤ C)
  定义体: ⟨c.right, c.hom⟩
  map f :=
    { hom := f.right
      w j := by simp [dsimp% congr_app f.w j] }

Depends on / 依赖: c.hom, c.right
-/
def Cocone.fromStructuredArrow (F : J ⥤ C) : StructuredArrow F (const J) ⥤ Cocone F where
  obj c := ⟨c.right, c.hom⟩
  map f :=
    { hom := f.right
      w j := by simp [dsimp% congr_app f.w j] }

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- The category of cocones on `F` is just the comma category `(F ↓ Δ)`, where `Δ` is the constant
    functor. -/
@[simps]
/--
Definition of `Cocone.equivStructuredArrow` / `Cocone.equivStructuredArrow` 的定义

English:
definition Cocone.equivStructuredArrow
  signature: (F : J ⥤ C)
  body: Cocone.toStructuredArrow F
  inverse := Cocone.fromStructuredArrow F
  unitIso := NatIso.ofComponents Cocone.eta
  counitIso := NatIso.ofComponents fun _ => (StructuredArrow.eta _).symm

中文:
定义 余锥.equivStructuredArrow
  签名: (F : J ⥤ C)
  定义体: Cocone.toStructuredArrow F
  inverse := Cocone.fromStructuredArrow F
  unitIso := NatIso.ofComponents Cocone.eta
  counitIso := NatIso.ofComponents fun _ => (StructuredArrow.eta _).symm

Depends on / 依赖: Cocone, Cocone.toStructuredArrow, toStructuredArrow
-/
def Cocone.equivStructuredArrow (F : J ⥤ C) : Cocone F ≌ StructuredArrow F (const J) where
  functor := Cocone.toStructuredArrow F
  inverse := Cocone.fromStructuredArrow F
  unitIso := NatIso.ofComponents Cocone.eta
  counitIso := NatIso.ofComponents fun _ => (StructuredArrow.eta _).symm

/--
Definition of `Cocone.isColimitEquivIsInitial` / `Cocone.isColimitEquivIsInitial` 的定义

English:
definition Cocone.isColimitEquivIsInitial
  signature: {F : J ⥤ C} (c : Cocone F)
  body: IsColimit.isoUniqueCoconeMorphism.toEquiv.trans
    { toFun := fun _ => IsInitial.ofUnique _
      invFun := fun h s => ⟨⟨IsInitial.to h s⟩, fun a => IsInitial.hom_ext h a _⟩
      left_inv := by cat_disch
      right_inv := by cat_disch }

中文:
定义 余锥.isColimitEquivIsInitial
  签名: {F : J ⥤ C} (c : 余锥 F)
  定义体: IsColimit.isoUniqueCoconeMorphism.toEquiv.trans
    { toFun := fun _ => IsInitial.ofUnique _
      invFun := fun h s => ⟨⟨IsInitial.to h s⟩, fun a => IsInitial.hom_ext h a _⟩
      left_inv := by cat_disch
      right_inv := by cat_disch }

Depends on / 依赖: IsColimit, IsColimit.isoUniqueCoconeMorphism.toEquiv.trans, IsInitial, IsInitial.hom_ext, IsInitial.ofUnique, IsInitial.to, cat_disch, hom_ext, invFun, isoUniqueCoconeMorphism, left_inv, ofUnique, right_inv, toEquiv
-/
def Cocone.isColimitEquivIsInitial {F : J ⥤ C} (c : Cocone F) : IsColimit c ≃ IsInitial c :=
  IsColimit.isoUniqueCoconeMorphism.toEquiv.trans
    { toFun := fun _ => IsInitial.ofUnique _
      invFun := fun h s => ⟨⟨IsInitial.to h s⟩, fun a => IsInitial.hom_ext h a _⟩
      left_inv := by cat_disch
      right_inv := by cat_disch }

/--
theorem `hasColimit_iff_hasInitial_cocone` / 定理 `hasColimit_iff_hasInitial_cocone`

English:
theorem hasColimit_iff_hasInitial_cocone
  given: (F : J ⥤ C)
  statement: HasColimit F ↔ HasInitial (Cocone F)
  proof: ⟨fun _ => (Cocone.isColimitEquivIsInitial _ (colimit.isColimit F)).hasInitial, fun h =>
    haveI : HasInitial (Cocone F) := h
    ⟨⟨⟨⊥_ _, (Cocone.isColimitEquivIsInitial _).symm initialIsInitial⟩⟩⟩⟩

中文:
定理 hasColimit_iff_hasInitial_cocone
  条件: (F : J ⥤ C)
  结论: 有余极限 F ↔ HasInitial (余锥 F)
  证明: ⟨fun _ => (Cocone.isColimitEquivIsInitial _ (colimit.isColimit F)).hasInitial, fun h =>
    haveI : HasInitial (Cocone F) := h
    ⟨⟨⟨⊥_ _, (Cocone.isColimitEquivIsInitial _).symm initialIsInitial⟩⟩⟩⟩

Depends on / 依赖: Cocone, Cocone.isColimitEquivIsInitial, HasInitial, colimit, colimit.isColimit, hasInitial, initialIsInitial, isColimit, isColimitEquivIsInitial
-/
theorem hasColimit_iff_hasInitial_cocone (F : J ⥤ C) : HasColimit F ↔ HasInitial (Cocone F) :=
  ⟨fun _ => (Cocone.isColimitEquivIsInitial _ (colimit.isColimit F)).hasInitial, fun h =>
    haveI : HasInitial (Cocone F) := h
    ⟨⟨⟨⊥_ _, (Cocone.isColimitEquivIsInitial _).symm initialIsInitial⟩⟩⟩⟩

/--
theorem `hasColimitsOfShape_iff_isRightAdjoint_const` / 定理 `hasColimitsOfShape_iff_isRightAdjoint_const`

English:
theorem hasColimitsOfShape_iff_isRightAdjoint_const
  proof: calc
    HasColimitsOfShape J C ↔ forall F : J ⥤ C, HasColimit F :=
      ⟨fun h => h.has_colimit, fun h => HasColimitsOfShape.mk⟩
    _ ↔ forall F : J ⥤ C, HasInitial (Cocone F) := forall_congr' hasColimit_iff_hasInitial_cocone
    _ ↔ forall F : J ⥤ C, HasInitial (StructuredArrow F (const J)) :=
 

中文:
定理 hasColimitsOfShape_iff_isRightAdjoint_const
  证明: calc
    HasColimitsOfShape J C ↔ forall F : J ⥤ C, HasColimit F :=
      ⟨fun h => h.has_colimit, fun h => HasColimitsOfShape.mk⟩
    _ ↔ forall F : J ⥤ C, HasInitial (Cocone F) := forall_congr' hasColimit_iff_hasInitial_cocone
    _ ↔ forall F : J ⥤ C, HasInitial (StructuredArrow F (const J)) :=
 

Depends on / 依赖: Cocone, Cocone.equivStructuredArrow, HasColimit, HasColimitsOfShape, HasColimitsOfShape.mk, HasInitial, IsRightAdjoint, StructuredArrow, equivStructuredArrow, forall_congr, h.has_colimit, hasColimit_iff_hasInitial_cocone, hasInitial_iff, has_colimit, isRightAdjoint_iff_hasInitial_structuredArrow, isRightAdjoint_iff_hasInitial_structuredArrow.symm
-/
theorem hasColimitsOfShape_iff_isRightAdjoint_const :
    HasColimitsOfShape J C ↔ IsRightAdjoint (const J : C ⥤ _) :=
  calc
    HasColimitsOfShape J C ↔ forall F : J ⥤ C, HasColimit F :=
      ⟨fun h => h.has_colimit, fun h => HasColimitsOfShape.mk⟩
    _ ↔ forall F : J ⥤ C, HasInitial (Cocone F) := forall_congr' hasColimit_iff_hasInitial_cocone
    _ ↔ forall F : J ⥤ C, HasInitial (StructuredArrow F (const J)) :=
      (forall_congr' fun F => (Cocone.equivStructuredArrow F).hasInitial_iff)
    _ ↔ (IsRightAdjoint (const J : C ⥤ _)) :=
      isRightAdjoint_iff_hasInitial_structuredArrow.symm

/--
theorem `IsColimit.descCoconeMorphism_eq_isInitial_to` / 定理 `IsColimit.descCoconeMorphism_eq_isInitial_to`

English:
theorem IsColimit.descCoconeMorphism_eq_isInitial_to
  statement: {F : J ⥤ C} {c : Cocone F} (hc : IsColimit c)
  proof: rfl

中文:
定理 是余极限.descCoconeMorphism_eq_isInitial_to
  结论: {F : J ⥤ C} {c : 余锥 F} (hc : 是余极限 c)
  证明: rfl
-/
theorem IsColimit.descCoconeMorphism_eq_isInitial_to {F : J ⥤ C} {c : Cocone F} (hc : IsColimit c)
    (s : Cocone F) :
    hc.descCoconeMorphism s = IsInitial.to (Cocone.isColimitEquivIsInitial _ hc) _ :=
  rfl

/--
theorem `IsInitial.to_eq_descCoconeMorphism` / 定理 `IsInitial.to_eq_descCoconeMorphism`

English:
theorem IsInitial.to_eq_descCoconeMorphism
  statement: {F : J ⥤ C} {c : Cocone F} (hc : IsInitial c)
  proof: (IsColimit.descCoconeMorphism_eq_isInitial_to (c.isColimitEquivIsInitial.symm hc) s).symm

中文:
定理 IsInitial.to_eq_descCoconeMorphism
  结论: {F : J ⥤ C} {c : 余锥 F} (hc : IsInitial c)
  证明: (IsColimit.descCoconeMorphism_eq_isInitial_to (c.isColimitEquivIsInitial.symm hc) s).symm

Depends on / 依赖: IsColimit, IsColimit.descCoconeMorphism_eq_isInitial_to, c.isColimitEquivIsInitial.symm, descCoconeMorphism_eq_isInitial_to, isColimitEquivIsInitial
-/
theorem IsInitial.to_eq_descCoconeMorphism {F : J ⥤ C} {c : Cocone F} (hc : IsInitial c)
    (s : Cocone F) :
    IsInitial.to hc s = ((Cocone.isColimitEquivIsInitial _).symm hc).descCoconeMorphism s :=
  (IsColimit.descCoconeMorphism_eq_isInitial_to (c.isColimitEquivIsInitial.symm hc) s).symm

/--
Definition of `IsColimit.ofPreservesCoconeInitial` / `IsColimit.ofPreservesCoconeInitial` 的定义

English:
definition IsColimit.ofPreservesCoconeInitial
  signature: {F : J ⥤ C} {F' : K ⥤ D}
  body: (Cocone.isColimitEquivIsInitial _).symm (Cocone.isColimitEquivIsInitial _ hc).isInitialObj _ _

中文:
定义 是余极限.ofPreservesCoconeInitial
  签名: {F : J ⥤ C} {F' : K ⥤ D}
  定义体: (Cocone.isColimitEquivIsInitial _).symm (Cocone.isColimitEquivIsInitial _ hc).isInitialObj _ _

Depends on / 依赖: Cocone, Cocone.isColimitEquivIsInitial, isColimitEquivIsInitial, isInitialObj
-/
noncomputable def IsColimit.ofPreservesCoconeInitial {F : J ⥤ C} {F' : K ⥤ D}
    (G : Cocone F ⥤ Cocone F')
    [PreservesColimit (Functor.empty.{0} _) G] {c : Cocone F} (hc : IsColimit c) :
    IsColimit (G.obj c) :=
(Cocone.isColimitEquivIsInitial _).symm (Cocone.isColimitEquivIsInitial _ hc).isInitialObj _ _

/--
Definition of `IsColimit.ofReflectsCoconeInitial` / `IsColimit.ofReflectsCoconeInitial` 的定义

English:
definition IsColimit.ofReflectsCoconeInitial
  signature: {F : J ⥤ C} {F' : K ⥤ D}
  body: (Cocone.isColimitEquivIsInitial _).symm
    (Cocone.isColimitEquivIsInitial _ hc).isInitialOfObj _ _

中文:
定义 是余极限.ofReflectsCoconeInitial
  签名: {F : J ⥤ C} {F' : K ⥤ D}
  定义体: (Cocone.isColimitEquivIsInitial _).symm
    (Cocone.isColimitEquivIsInitial _ hc).isInitialOfObj _ _

Depends on / 依赖: Cocone, Cocone.isColimitEquivIsInitial, isColimitEquivIsInitial, isInitialOfObj
-/
noncomputable def IsColimit.ofReflectsCoconeInitial {F : J ⥤ C} {F' : K ⥤ D}
    (G : Cocone F ⥤ Cocone F')
    [ReflectsColimit (Functor.empty.{0} _) G] {c : Cocone F} (hc : IsColimit (G.obj c)) :
    IsColimit c :=
(Cocone.isColimitEquivIsInitial _).symm
    (Cocone.isColimitEquivIsInitial _ hc).isInitialOfObj _ _

end CategoryTheory.Limits
