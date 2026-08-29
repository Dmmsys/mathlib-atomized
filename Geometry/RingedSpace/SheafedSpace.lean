/-
Copyright (c) 2019 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import Mathlib.Geometry.RingedSpace.PresheafedSpace.HasColimits
public import Mathlib.Geometry.RingedSpace.Stalks
public import Mathlib.Topology.Sheaves.Functors

/-!
# Sheafed spaces

Introduces the category of topological spaces equipped with a sheaf (taking values in an
arbitrary target category `C`).

We further describe how to apply functors and natural transformations to the values of the
presheaves.
-/

@[expose] public section

open CategoryTheory TopCat TopologicalSpace Opposite CategoryTheory.Limits CategoryTheory.Category
  CategoryTheory.Functor Topology

universe u v w' w

variable (C : Type u) [Category.{v} C]


-- We could enable the following line:
-- attribute [local aesop safe cases (rule_sets := [CategoryTheory])] Opposite
-- but may need
-- https://github.com/leanprover-community/aesop/issues/59

namespace AlgebraicGeometry

/--
Definition of `SheafedSpace` / `SheafedSpace` 的定义

English:
structure SheafedSpace
  parameters: extends PresheafedSpace C
  extends: PresheafedSpace C
  axioms and operations (1):
    - IsSheaf : presheaf.IsSheaf

中文:
结构 SheafedSpace
  参数: extends PresheafedSpace C
  继承: PresheafedSpace C
  公理与运算 (1 个):
    - IsSheaf : presheaf.IsSheaf
-/
structure SheafedSpace extends PresheafedSpace C where
  /-- A sheafed space is a presheafed space which happens to be a sheaf. -/
  IsSheaf : presheaf.IsSheaf

variable {C}

namespace SheafedSpace

/--
Instance `coeCarrier` / 实例 `coeCarrier`

English:
instance coeCarrier
  signature: : CoeOut (SheafedSpace C) TopCat where coe X
  body: X.carrier

中文:
实例 coeCarrier
  签名: : CoeOut (SheafedSpace C) TopCat where coe X
  定义体: X.carrier

Depends on / 依赖: X.carrier, carrier
-/
instance coeCarrier : CoeOut (SheafedSpace C) TopCat where coe X := X.carrier

/--
Instance `coeSort` / 实例 `coeSort`

English:
instance coeSort
  signature: : CoeSort (SheafedSpace C) Type* where
  body: X.1

中文:
实例 coeSort
  签名: : CoeSort (SheafedSpace C) 类型 where
  定义体: X.1
-/
instance coeSort : CoeSort (SheafedSpace C) Type* where
  coe X := X.1

/--
Definition of `sheaf` / `sheaf` 的定义

English:
definition sheaf
  signature: (X : SheafedSpace C)
  body: ⟨X.presheaf, X.IsSheaf⟩

中文:
定义 sheaf
  签名: (X : SheafedSpace C)
  定义体: ⟨X.presheaf, X.IsSheaf⟩

Depends on / 依赖: IsSheaf, X.IsSheaf, X.presheaf, presheaf
-/
def sheaf (X : SheafedSpace C) : Sheaf C (X : TopCat) :=
  ⟨X.presheaf, X.IsSheaf⟩

/--
theorem `mk_coe` / 定理 `mk_coe`

English:
theorem mk_coe
  given: (carrier) (presheaf) (h)
  proof: rfl

中文:
定理 mk_coe
  条件: (carrier) (presheaf) (h)
  证明: rfl

Depends on / 依赖: SheafedSpace, TopCat, carrier
-/
theorem mk_coe (carrier) (presheaf) (h) :
    (({ carrier
        presheaf
        IsSheaf := h } : SheafedSpace C) : TopCat) = carrier :=
  rfl

instance (X : SheafedSpace C) : TopologicalSpace X :=
  X.carrier.str

/--
Definition of `unit` / `unit` 的定义

English:
definition unit
  signature: (X : TopCat)
  body: { @PresheafedSpace.const (Discrete Unit) _ X ⟨⟨⟩⟩ with IsSheaf := Presheaf.isSheaf_unit _ }

中文:
定义 unit
  签名: (X : TopCat)
  定义体: { @PresheafedSpace.const (Discrete Unit) _ X ⟨⟨⟩⟩ with IsSheaf := Presheaf.isSheaf_unit _ }

Depends on / 依赖: Discrete, IsSheaf, Presheaf, Presheaf.isSheaf_unit, PresheafedSpace, PresheafedSpace.const, isSheaf_unit
-/
def unit (X : TopCat) : SheafedSpace (Discrete Unit) :=
  { @PresheafedSpace.const (Discrete Unit) _ X ⟨⟨⟩⟩ with IsSheaf := Presheaf.isSheaf_unit _ }

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Inhabited (SheafedSpace (Discrete Unit))
  body: ⟨unit (TopCat.of PEmpty)⟩

中文:
实例 :
  签名: Inhabited (SheafedSpace (Discrete Unit))
  定义体: ⟨unit (TopCat.of PEmpty)⟩

Depends on / 依赖: PEmpty, TopCat, TopCat.of
-/
instance : Inhabited (SheafedSpace (Discrete Unit)) :=
  ⟨unit (TopCat.of PEmpty)⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Category (SheafedSpace C)
  body: inferInstanceAs Category (InducedCategory (PresheafedSpace C) SheafedSpace.toPresheafedSpace)

@[ext (iff := false)]

中文:
实例 :
  签名: Category (SheafedSpace C)
  定义体: inferInstanceAs Category (InducedCategory (PresheafedSpace C) SheafedSpace.toPresheafedSpace)

@[ext (iff := false)]

Depends on / 依赖: Category, InducedCategory, PresheafedSpace, SheafedSpace, SheafedSpace.toPresheafedSpace, toPresheafedSpace
-/
instance : Category (SheafedSpace C) :=
inferInstanceAs Category (InducedCategory (PresheafedSpace C) SheafedSpace.toPresheafedSpace)

@[ext (iff := false)]
/--
theorem `ext` / 定理 `ext`

English:
theorem ext
  statement: {X Y : SheafedSpace C} (α β : X ⟶ Y) (w : α.hom.base = β.hom.base)
  proof: InducedCategory.hom_ext (PresheafedSpace.ext _ _ w h)

中文:
定理 ext
  结论: {X Y : SheafedSpace C} (α β : X ⟶ Y) (w : α.hom.base = β.hom.base)
  证明: InducedCategory.hom_ext (PresheafedSpace.ext _ _ w h)

Depends on / 依赖: InducedCategory, InducedCategory.hom_ext, PresheafedSpace, PresheafedSpace.ext, hom_ext
-/
theorem ext {X Y : SheafedSpace C} (α β : X ⟶ Y) (w : α.hom.base = β.hom.base)
    (h : α.hom.c ≫ whiskerRight (eqToHom (by rw [w])) _ = β.hom.c) : α = β :=
  InducedCategory.hom_ext (PresheafedSpace.ext _ _ w h)

/-- Constructor for isomorphisms in the category `SheafedSpace C`. -/
@[simps]
/--
Definition of `isoMk` / `isoMk` 的定义

English:
definition isoMk
  signature: {X Y : SheafedSpace C} (e : X.toPresheafedSpace ≅ Y.toPresheafedSpace)
  body: InducedCategory.homMk e.hom
  inv := InducedCategory.homMk e.inv
  hom_inv_id := InducedCategory.hom_ext e.hom_inv_id
  inv_hom_id := InducedCategory.hom_ext e.inv_hom_id

中文:
定义 isoMk
  签名: {X Y : SheafedSpace C} (e : X.toPresheafedSpace ≅ Y.toPresheafedSpace)
  定义体: InducedCategory.homMk e.hom
  inv := InducedCategory.homMk e.inv
  hom_inv_id := InducedCategory.hom_ext e.hom_inv_id
  inv_hom_id := InducedCategory.hom_ext e.inv_hom_id

Depends on / 依赖: InducedCategory, InducedCategory.homMk, e.hom
-/
def isoMk {X Y : SheafedSpace C} (e : X.toPresheafedSpace ≅ Y.toPresheafedSpace) : X ≅ Y where
  hom := InducedCategory.homMk e.hom
  inv := InducedCategory.homMk e.inv
  hom_inv_id := InducedCategory.hom_ext e.hom_inv_id
  inv_hom_id := InducedCategory.hom_ext e.inv_hom_id

/-- Forgetting the sheaf condition is a functor from `SheafedSpace C` to `PresheafedSpace C`. -/
@[simps! obj map]
/--
Definition of `forgetToPresheafedSpace` / `forgetToPresheafedSpace` 的定义

English:
definition forgetToPresheafedSpace
  signature: : SheafedSpace C ⥤ PresheafedSpace C
  body: inducedFunctor _

中文:
定义 forgetToPresheafedSpace
  签名: : SheafedSpace C ⥤ PresheafedSpace C
  定义体: inducedFunctor _

Depends on / 依赖: inducedFunctor
-/
def forgetToPresheafedSpace : SheafedSpace C ⥤ PresheafedSpace C :=
  inducedFunctor _
-- The `Full, Faithful` instances should be constructed by a deriving handler.
-- https://github.com/leanprover-community/mathlib4/issues/380

/--
Definition of `fullyFaithfulForgetToPresheafedSpace` / `fullyFaithfulForgetToPresheafedSpace` 的定义

English:
definition fullyFaithfulForgetToPresheafedSpace
  signature: :
  body: InducedCategory.homMk f

@[simp]

中文:
定义 fullyFaithfulForgetToPresheafedSpace
  签名: :
  定义体: InducedCategory.homMk f

@[simp]

Depends on / 依赖: FullyFaithful
-/
def fullyFaithfulForgetToPresheafedSpace :
    (forgetToPresheafedSpace (C := C)).FullyFaithful where
  preimage f := InducedCategory.homMk f

@[simp]
/--
lemma `fullyFaithfulForgetToPresheafedSpace_preimage_hom` / 引理 `fullyFaithfulForgetToPresheafedSpace_preimage_hom`

English:
lemma fullyFaithfulForgetToPresheafedSpace_preimage_hom
  statement: {X Y : SheafedSpace C}
  proof: rfl

中文:
引理 fullyFaithfulForgetToPresheafedSpace_preimage_hom
  结论: {X Y : SheafedSpace C}
  证明: rfl
-/
lemma fullyFaithfulForgetToPresheafedSpace_preimage_hom {X Y : SheafedSpace C}
    (f : forgetToPresheafedSpace.obj X ⟶ forgetToPresheafedSpace.obj Y) :
    (fullyFaithfulForgetToPresheafedSpace.preimage f).hom = f := rfl

/--
Instance `forgetToPresheafedSpace_full` / 实例 `forgetToPresheafedSpace_full`

English:
instance forgetToPresheafedSpace_full
  signature: : (forgetToPresheafedSpace (C := C)).Full
  body: fullyFaithfulForgetToPresheafedSpace.full

中文:
实例 forgetToPresheafedSpace_full
  签名: : (forgetToPresheafedSpace (C := C)).Full
  定义体: fullyFaithfulForgetToPresheafedSpace.full
-/
instance forgetToPresheafedSpace_full : (forgetToPresheafedSpace (C := C)).Full :=
  fullyFaithfulForgetToPresheafedSpace.full

/--
Instance `forgetToPresheafedSpace_faithful` / 实例 `forgetToPresheafedSpace_faithful`

English:
instance forgetToPresheafedSpace_faithful
  signature: : (forgetToPresheafedSpace (C := C)).Faithful
  body: fullyFaithfulForgetToPresheafedSpace.faithful

中文:
实例 forgetToPresheafedSpace_faithful
  签名: : (forgetToPresheafedSpace (C := C)).Faithful
  定义体: fullyFaithfulForgetToPresheafedSpace.faithful

Depends on / 依赖: Faithful
-/
instance forgetToPresheafedSpace_faithful : (forgetToPresheafedSpace (C := C)).Faithful :=
  fullyFaithfulForgetToPresheafedSpace.faithful

/--
Instance `is_presheafedSpace_iso` / 实例 `is_presheafedSpace_iso`

English:
instance is_presheafedSpace_iso
  signature: {X Y : SheafedSpace C} (f : X ⟶ Y) [IsIso f]
  body: SheafedSpace.forgetToPresheafedSpace.map_isIso f

中文:
实例 is_presheafedSpace_iso
  签名: {X Y : SheafedSpace C} (f : X ⟶ Y) [IsIso f]
  定义体: SheafedSpace.forgetToPresheafedSpace.map_isIso f

Depends on / 依赖: SheafedSpace, SheafedSpace.forgetToPresheafedSpace.map_isIso, forgetToPresheafedSpace, map_isIso
-/
instance is_presheafedSpace_iso {X Y : SheafedSpace C} (f : X ⟶ Y) [IsIso f] :
    IsIso f.hom :=
  SheafedSpace.forgetToPresheafedSpace.map_isIso f

section

attribute [local simp] id comp

@[simp]
/--
theorem `id_hom` / 定理 `id_hom`

English:
theorem id_hom
  given: (X : SheafedSpace C)
  statement: (𝟙 X : X ⟶ X).hom = 𝟙 X.toPresheafedSpace
  proof: rfl

@[simp]

中文:
定理 id_hom
  条件: (X : SheafedSpace C)
  结论: (𝟙 X : X ⟶ X).hom = 𝟙 X.toPresheafedSpace
  证明: rfl

@[simp]
-/
theorem id_hom (X : SheafedSpace C) : (𝟙 X : X ⟶ X).hom = 𝟙 X.toPresheafedSpace :=
  rfl

@[simp]
/--
theorem `id_hom_base` / 定理 `id_hom_base`

English:
theorem id_hom_base
  given: (X : SheafedSpace C)
  statement: (𝟙 X : X ⟶ X).hom.base = 𝟙 (X : TopCat)
  proof: rfl

中文:
定理 id_hom_base
  条件: (X : SheafedSpace C)
  结论: (𝟙 X : X ⟶ X).hom.base = 𝟙 (X : TopCat)
  证明: rfl
-/
theorem id_hom_base (X : SheafedSpace C) : (𝟙 X : X ⟶ X).hom.base = 𝟙 (X : TopCat) :=
  rfl

/--
theorem `id_hom_c` / 定理 `id_hom_c`

English:
theorem id_hom_c
  given: (X : SheafedSpace C)
  proof: rfl

中文:
定理 id_hom_c
  条件: (X : SheafedSpace C)
  证明: rfl
-/
theorem id_hom_c (X : SheafedSpace C) :
    (𝟙 X : X ⟶ X).hom.c = eqToHom (Presheaf.Pushforward.id_eq X.presheaf).symm :=
  rfl

/--
theorem `id_hom_c_app` / 定理 `id_hom_c_app`

English:
theorem id_hom_c_app
  given: (X : SheafedSpace C) (U)
  proof: rfl

@[simp]

中文:
定理 id_hom_c_app
  条件: (X : SheafedSpace C) (U)
  证明: rfl

@[simp]
-/
theorem id_hom_c_app (X : SheafedSpace C) (U) :
    (𝟙 X : X ⟶ X).hom.c.app U = 𝟙 _ := rfl

@[simp]
/--
theorem `comp_hom_base` / 定理 `comp_hom_base`

English:
theorem comp_hom_base
  given: {X Y Z : SheafedSpace C} (f : X ⟶ Y) (g : Y ⟶ Z)
  proof: rfl

@[simp]

中文:
定理 comp_hom_base
  条件: {X Y Z : SheafedSpace C} (f : X ⟶ Y) (g : Y ⟶ Z)
  证明: rfl

@[simp]
-/
theorem comp_hom_base {X Y Z : SheafedSpace C} (f : X ⟶ Y) (g : Y ⟶ Z) :
    (f ≫ g).hom.base = f.hom.base ≫ g.hom.base :=
  rfl

@[simp]
/--
theorem `comp_hom_c_app` / 定理 `comp_hom_c_app`

English:
theorem comp_hom_c_app
  given: {X Y Z : SheafedSpace C} (α : X ⟶ Y) (β : Y ⟶ Z) (U)
  proof: rfl

中文:
定理 comp_hom_c_app
  条件: {X Y Z : SheafedSpace C} (α : X ⟶ Y) (β : Y ⟶ Z) (U)
  证明: rfl
-/
theorem comp_hom_c_app {X Y Z : SheafedSpace C} (α : X ⟶ Y) (β : Y ⟶ Z) (U) :
    (α ≫ β).hom.c.app U =
      β.hom.c.app U ≫ α.hom.c.app (op ((Opens.map β.hom.base).obj (unop U))) :=
  rfl

/--
theorem `comp_hom_c_app'` / 定理 `comp_hom_c_app'`

English:
theorem comp_hom_c_app'
  given: {X Y Z : SheafedSpace C} (α : X ⟶ Y) (β : Y ⟶ Z) (U)
  proof: rfl

中文:
定理 comp_hom_c_app'
  条件: {X Y Z : SheafedSpace C} (α : X ⟶ Y) (β : Y ⟶ Z) (U)
  证明: rfl
-/
theorem comp_hom_c_app' {X Y Z : SheafedSpace C} (α : X ⟶ Y) (β : Y ⟶ Z) (U) :
    (α ≫ β).hom.c.app (op U) =
      β.hom.c.app (op U) ≫ α.hom.c.app (op ((Opens.map β.hom.base).obj U)) :=
  rfl

/--
theorem `congr_hom_app` / 定理 `congr_hom_app`

English:
theorem congr_hom_app
  given: {X Y : SheafedSpace C} {α β : X ⟶ Y} (h : α = β) (U)
  proof: (PresheafedSpace.congr_app (by rw [h]) U)

中文:
定理 congr_hom_app
  条件: {X Y : SheafedSpace C} {α β : X ⟶ Y} (h : α = β) (U)
  证明: (PresheafedSpace.congr_app (by rw [h]) U)

Depends on / 依赖: PresheafedSpace, PresheafedSpace.congr_app, congr_app
-/
theorem congr_hom_app {X Y : SheafedSpace C} {α β : X ⟶ Y} (h : α = β) (U) :
    α.hom.c.app U = β.hom.c.app U ≫ X.presheaf.map (eqToHom (by subst h; rfl)) :=
  (PresheafedSpace.congr_app (by rw [h]) U)

variable (C)

/--
Definition of `forget` / `forget` 的定义

English:
definition forget
  signature: : SheafedSpace C ⥤ TopCat where
  body: (X : TopCat)
  map {_ _} f := f.hom.base

中文:
定义 forget
  签名: : SheafedSpace C ⥤ TopCat where
  定义体: (X : TopCat)
  map {_ _} f := f.hom.base

Depends on / 依赖: TopCat
-/
def forget : SheafedSpace C ⥤ TopCat where
  obj X := (X : TopCat)
  map {_ _} f := f.hom.base

end

open TopCat.Presheaf

/--
Definition of `restrict` / `restrict` 的定义

English:
definition restrict
  signature: {U : TopCat} (X : SheafedSpace C) {f : U ⟶ (X : TopCat)} (h : IsOpenEmbedding f)
  body: { X.toPresheafedSpace.restrict h with IsSheaf := isSheaf_of_isOpenEmbedding h X.IsSheaf }

中文:
定义 restrict
  签名: {U : TopCat} (X : SheafedSpace C) {f : U ⟶ (X : TopCat)} (h : IsOpenEmbedding f)
  定义体: { X.toPresheafedSpace.restrict h with IsSheaf := isSheaf_of_isOpenEmbedding h X.IsSheaf }

Depends on / 依赖: IsSheaf, X.IsSheaf, X.toPresheafedSpace.restrict, isSheaf_of_isOpenEmbedding, restrict, toPresheafedSpace
-/
def restrict {U : TopCat} (X : SheafedSpace C) {f : U ⟶ (X : TopCat)} (h : IsOpenEmbedding f) :
    SheafedSpace C :=
  { X.toPresheafedSpace.restrict h with IsSheaf := isSheaf_of_isOpenEmbedding h X.IsSheaf }

/-- The map from the restriction of a presheafed space.
-/
@[simps!]
/--
Definition of `ofRestrict` / `ofRestrict` 的定义

English:
definition ofRestrict
  signature: {U : TopCat} (X : SheafedSpace C) {f : U ⟶ (X : TopCat)}
  body: InducedCategory.homMk (X.toPresheafedSpace.ofRestrict h)

中文:
定义 ofRestrict
  签名: {U : TopCat} (X : SheafedSpace C) {f : U ⟶ (X : TopCat)}
  定义体: InducedCategory.homMk (X.toPresheafedSpace.ofRestrict h)

Depends on / 依赖: InducedCategory, InducedCategory.homMk, X.toPresheafedSpace.ofRestrict, ofRestrict, toPresheafedSpace
-/
def ofRestrict {U : TopCat} (X : SheafedSpace C) {f : U ⟶ (X : TopCat)}
    (h : IsOpenEmbedding f) : X.restrict h ⟶ X :=
  InducedCategory.homMk (X.toPresheafedSpace.ofRestrict h)

/-- The restriction of a sheafed space `X` to the top subspace is isomorphic to `X` itself.
-/
@[simps! hom inv]
/--
Definition of `restrictTopIso` / `restrictTopIso` 的定义

English:
definition restrictTopIso
  signature: (X : SheafedSpace C)
  body: isoMk (X.toPresheafedSpace.restrictTopIso)

中文:
定义 restrictTopIso
  签名: (X : SheafedSpace C)
  定义体: isoMk (X.toPresheafedSpace.restrictTopIso)

Depends on / 依赖: X.toPresheafedSpace.restrictTopIso, restrictTopIso, toPresheafedSpace
-/
def restrictTopIso (X : SheafedSpace C) : X.restrict (Opens.isOpenEmbedding ⊤) ≅ X :=
  isoMk (X.toPresheafedSpace.restrictTopIso)

/--
Definition of `Γ` / `Γ` 的定义

English:
definition Γ
  signature: : (SheafedSpace C)ᵒᵖ ⥤ C
  body: forgetToPresheafedSpace.op ⋙ PresheafedSpace.Γ

中文:
定义 Γ
  签名: : (SheafedSpace C)ᵒᵖ ⥤ C
  定义体: forgetToPresheafedSpace.op ⋙ PresheafedSpace.Γ

Depends on / 依赖: PresheafedSpace, forgetToPresheafedSpace, forgetToPresheafedSpace.op
-/
def Γ : (SheafedSpace C)ᵒᵖ ⥤ C :=
  forgetToPresheafedSpace.op ⋙ PresheafedSpace.Γ

/--
theorem `Γ_def` / 定理 `Γ_def`

English:
theorem Γ_def
  statement: (Γ : _ ⥤ C) = forgetToPresheafedSpace.op ⋙ PresheafedSpace.Γ
  proof: rfl

@[simp]

中文:
定理 Γ_def
  结论: (Γ : _ ⥤ C) = forgetToPresheafedSpace.op ⋙ PresheafedSpace.Γ
  证明: rfl

@[simp]
-/
theorem Γ_def : (Γ : _ ⥤ C) = forgetToPresheafedSpace.op ⋙ PresheafedSpace.Γ :=
  rfl

@[simp]
/--
theorem `Γ_obj` / 定理 `Γ_obj`

English:
theorem Γ_obj
  given: (X : (SheafedSpace C)ᵒᵖ)
  statement: Γ.obj X = (unop X).presheaf.obj (op ⊤)
  proof: rfl

中文:
定理 Γ_obj
  条件: (X : (SheafedSpace C)ᵒᵖ)
  结论: Γ.obj X = (unop X).presheaf.obj (op ⊤)
  证明: rfl
-/
theorem Γ_obj (X : (SheafedSpace C)ᵒᵖ) : Γ.obj X = (unop X).presheaf.obj (op ⊤) :=
  rfl

/--
theorem `Γ_obj_op` / 定理 `Γ_obj_op`

English:
theorem Γ_obj_op
  given: (X : SheafedSpace C)
  statement: Γ.obj (op X) = X.presheaf.obj (op ⊤)
  proof: rfl

@[simp]

中文:
定理 Γ_obj_op
  条件: (X : SheafedSpace C)
  结论: Γ.obj (op X) = X.presheaf.obj (op ⊤)
  证明: rfl

@[simp]
-/
theorem Γ_obj_op (X : SheafedSpace C) : Γ.obj (op X) = X.presheaf.obj (op ⊤) :=
  rfl

@[simp]
/--
theorem `Γ_map` / 定理 `Γ_map`

English:
theorem Γ_map
  given: {X Y : (SheafedSpace C)ᵒᵖ} (f : X ⟶ Y)
  statement: Γ.map f = f.unop.hom.c.app (op ⊤)
  proof: rfl

中文:
定理 Γ_map
  条件: {X Y : (SheafedSpace C)ᵒᵖ} (f : X ⟶ Y)
  结论: Γ.map f = f.unop.hom.c.app (op ⊤)
  证明: rfl
-/
theorem Γ_map {X Y : (SheafedSpace C)ᵒᵖ} (f : X ⟶ Y) : Γ.map f = f.unop.hom.c.app (op ⊤) :=
  rfl

/--
theorem `Γ_map_op` / 定理 `Γ_map_op`

English:
theorem Γ_map_op
  given: {X Y : SheafedSpace C} (f : X ⟶ Y)
  statement: Γ.map f.op = f.hom.c.app (op ⊤)
  proof: rfl

中文:
定理 Γ_map_op
  条件: {X Y : SheafedSpace C} (f : X ⟶ Y)
  结论: Γ.map f.op = f.hom.c.app (op ⊤)
  证明: rfl
-/
theorem Γ_map_op {X Y : SheafedSpace C} (f : X ⟶ Y) : Γ.map f.op = f.hom.c.app (op ⊤) :=
  rfl

noncomputable instance (J : Type w) [Category.{w'} J] [Small.{v} J] [HasLimitsOfShape Jᵒᵖ C] :
    CreatesColimitsOfShape J (forgetToPresheafedSpace : SheafedSpace.{_, _, v} C ⥤ _) :=
  ⟨fun {K} =>
    createsColimitOfFullyFaithfulOfIso
      ⟨(PresheafedSpace.colimitCocone (K ⋙ forgetToPresheafedSpace)).pt,
        limit_isSheaf _ fun j => Sheaf.pushforward_sheaf_of_sheaf _ (K.obj (unop j)).2⟩
      (colimit.isoColimitCocone ⟨_, PresheafedSpace.colimitCoconeIsColimit _⟩).symm⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [HasLimits
  signature: C] :

中文:
实例 [HasLimits
  签名: C] :
-/
noncomputable instance [HasLimits C] :
    CreatesColimits (forgetToPresheafedSpace : SheafedSpace C ⥤ _) where

instance (J : Type w) [Category.{w'} J] [Small.{v} J] [HasLimitsOfShape Jᵒᵖ C] :
    HasColimitsOfShape J (SheafedSpace.{_, _, v} C) :=
  hasColimitsOfShape_of_hasColimitsOfShape_createsColimitsOfShape forgetToPresheafedSpace

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [HasLimits
  signature: C] : HasColimits.{v} (SheafedSpace C) where

中文:
实例 [HasLimits
  签名: C] : HasColimits.{v} (SheafedSpace C) where
-/
instance [HasLimits C] : HasColimits.{v} (SheafedSpace C) where

instance (J : Type w) [Category.{w'} J] [Small.{v} J] [HasLimitsOfShape Jᵒᵖ C] :
    PreservesColimitsOfShape J (forget.{_, _, v} C) :=
  Limits.comp_preservesColimitsOfShape forgetToPresheafedSpace (PresheafedSpace.forget C)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [HasLimits
  signature: C] : PreservesColimits (forget.{_, _, v} C) where

中文:
实例 [HasLimits
  签名: C] : PreservesColimits (forget.{_, _, v} C) where
-/
noncomputable instance [HasLimits C] : PreservesColimits (forget.{_, _, v} C) where

section ConcreteCategory

variable {FC : C -> C -> Type*} {CC : C -> Type v} [forall X Y, FunLike (FC X Y) (CC X) (CC Y)]
variable [instCC : ConcreteCategory.{v} C FC] [HasColimits C] [HasLimits C]
variable [PreservesLimits (CategoryTheory.forget C)]
variable [PreservesFilteredColimits (CategoryTheory.forget C)]
variable [(CategoryTheory.forget C).ReflectsIsomorphisms]

set_option backward.isDefEq.respectTransparency.types false in
attribute [local ext] DFunLike.ext in
include instCC in
/--
lemma `hom_stalk_ext` / 引理 `hom_stalk_ext`

English:
lemma hom_stalk_ext
  statement: {X Y : SheafedSpace C} (f g : X ⟶ Y) (h : f.hom.base = g.hom.base)
  proof: by
  obtain ⟨f, fc⟩ := f
  obtain ⟨g, gc⟩ := g
  obtain rfl : f = g := h
  congr
  ext U s
  refine section_ext X.sheaf _ _ _ fun x hx =>
    show X.presheaf.germ _ x _ _ = X.presheaf.germ _ x _ _ from ?_
  erw [← PresheafedSpace.stalkMap_germ_apply ⟨f, fc⟩, ← PresheafedSpace.stalkMap_germ_apply ⟨f,

中文:
引理 hom_stalk_ext
  结论: {X Y : SheafedSpace C} (f g : X ⟶ Y) (h : f.hom.base = g.hom.base)
  证明: by
  obtain ⟨f, fc⟩ := f
  obtain ⟨g, gc⟩ := g
  obtain rfl : f = g := h
  congr
  ext U s
  refine section_ext X.sheaf _ _ _ fun x hx =>
    show X.presheaf.germ _ x _ _ = X.presheaf.germ _ x _ _ from ?_
  erw [← PresheafedSpace.stalkMap_germ_apply ⟨f, fc⟩, ← PresheafedSpace.stalkMap_germ_apply ⟨f,

Depends on / 依赖: PresheafedSpace, PresheafedSpace.stalkMap_germ_apply, X.presheaf.germ, X.sheaf, presheaf, section_ext, stalkMap_germ_apply
-/
lemma hom_stalk_ext {X Y : SheafedSpace C} (f g : X ⟶ Y) (h : f.hom.base = g.hom.base)
    (h' : forall x, f.hom.stalkMap x = (Y.presheaf.stalkCongr (h ▸ rfl)).hom ≫ g.hom.stalkMap x) :
    f = g := by
  obtain ⟨f, fc⟩ := f
  obtain ⟨g, gc⟩ := g
  obtain rfl : f = g := h
  congr
  ext U s
  refine section_ext X.sheaf _ _ _ fun x hx =>
    show X.presheaf.germ _ x _ _ = X.presheaf.germ _ x _ _ from ?_
  erw [← PresheafedSpace.stalkMap_germ_apply ⟨f, fc⟩, ← PresheafedSpace.stalkMap_germ_apply ⟨f, gc⟩]
  simp [h']

attribute [local ext] DFunLike.ext in
include instCC in
/--
lemma `mono_of_base_injective_of_stalk_epi` / 引理 `mono_of_base_injective_of_stalk_epi`

English:
lemma mono_of_base_injective_of_stalk_epi
  statement: {X Y : SheafedSpace C} (f : X ⟶ Y)
  proof: by
  constructor
  intro Z ⟨g, gc⟩ ⟨h, hc⟩ e
  obtain rfl : g = h := ConcreteCategory.hom_ext _ _ fun x => h₁ congr(($e).hom.base x)
  refine SheafedSpace.hom_stalk_ext ⟨g, gc⟩ ⟨g, hc⟩ rfl fun x => ?_
  rw [← cancel_epi (f.hom.stalkMap (g x))]; rw [stalkCongr_hom]; rw [stalkSpecializes_refl]; rw [Ca

中文:
引理 mono_of_base_injective_of_stalk_epi
  结论: {X Y : SheafedSpace C} (f : X ⟶ Y)
  证明: by
  constructor
  intro Z ⟨g, gc⟩ ⟨h, hc⟩ e
  obtain rfl : g = h := ConcreteCategory.hom_ext _ _ fun x => h₁ congr(($e).hom.base x)
  refine SheafedSpace.hom_stalk_ext ⟨g, gc⟩ ⟨g, hc⟩ rfl fun x => ?_
  rw [← cancel_epi (f.hom.stalkMap (g x))]; rw [stalkCongr_hom]; rw [stalkSpecializes_refl]; rw [Ca

Depends on / 依赖: Category, Category.id_comp, ConcreteCategory, ConcreteCategory.hom_ext, InducedCategory, InducedCategory.Hom.hom, PresheafedSpace, PresheafedSpace.stalkMap.comp, SheafedSpace, SheafedSpace.hom_stalk_ext, cancel_epi, congr_arg, f.hom, f.hom.stalkMap, hom.base, hom_ext, hom_stalk_ext, id_comp, replace, stalkCongr_hom
-/
lemma mono_of_base_injective_of_stalk_epi {X Y : SheafedSpace C} (f : X ⟶ Y)
    (h₁ : Function.Injective f.hom.base)
    (h₂ : forall x, Epi (f.hom.stalkMap x)) : Mono f := by
  constructor
  intro Z ⟨g, gc⟩ ⟨h, hc⟩ e
  obtain rfl : g = h := ConcreteCategory.hom_ext _ _ fun x => h₁ congr(($e).hom.base x)
  refine SheafedSpace.hom_stalk_ext ⟨g, gc⟩ ⟨g, hc⟩ rfl fun x => ?_
  rw [← cancel_epi (f.hom.stalkMap (g x))]; rw [stalkCongr_hom]; rw [stalkSpecializes_refl]; rw [Category.id_comp]; rw [← PresheafedSpace.stalkMap.comp ⟨g]; rw [gc⟩ f.hom]; rw [← PresheafedSpace.stalkMap.comp ⟨g]; rw [hc⟩ f.hom]
  replace e := congr_arg InducedCategory.Hom.hom e
  congr 1

set_option backward.isDefEq.respectTransparency.types false in
attribute [local ext] DFunLike.ext in
include instCC in
/--
lemma `epi_of_base_surjective_of_stalk_mono` / 引理 `epi_of_base_surjective_of_stalk_mono`

English:
lemma epi_of_base_surjective_of_stalk_mono
  statement: {X Y : SheafedSpace C} (f : X ⟶ Y)
  proof: by
  constructor
  intro Z ⟨g, gc⟩ ⟨h, hc⟩ e
  apply_fun InducedCategory.Hom.hom at e
  obtain rfl : g = h := ConcreteCategory.hom_ext _ _ fun y => by
    rw [← (h₁ y).choose_spec]
    simpa using congr(($e).base.hom (h₁ y).choose)
  refine SheafedSpace.hom_stalk_ext ⟨g, gc⟩ ⟨g, hc⟩ rfl fun y => ?_


中文:
引理 epi_of_base_surjective_of_stalk_mono
  结论: {X Y : SheafedSpace C} (f : X ⟶ Y)
  证明: by
  constructor
  intro Z ⟨g, gc⟩ ⟨h, hc⟩ e
  apply_fun InducedCategory.Hom.hom at e
  obtain rfl : g = h := ConcreteCategory.hom_ext _ _ fun y => by
    rw [← (h₁ y).choose_spec]
    simpa using congr(($e).base.hom (h₁ y).choose)
  refine SheafedSpace.hom_stalk_ext ⟨g, gc⟩ ⟨g, hc⟩ rfl fun y => ?_


Depends on / 依赖: Category, Category.id_comp, ConcreteCategory, ConcreteCategory.hom_ext, InducedCategory, InducedCategory.Hom.hom, PresheafedSpace, PresheafedSpace.stalkMap.comp, SheafedSpace, SheafedSpace.hom_stalk_ext, apply_fun, base.hom, cancel_mono, choose_spec, f.hom, f.hom.stalkMap, hom_ext, hom_stalk_ext, id_comp, stalkCongr_hom
-/
lemma epi_of_base_surjective_of_stalk_mono {X Y : SheafedSpace C} (f : X ⟶ Y)
    (h₁ : Function.Surjective f.hom.base)
    (h₂ : forall x, Mono (f.hom.stalkMap x)) : Epi f := by
  constructor
  intro Z ⟨g, gc⟩ ⟨h, hc⟩ e
  apply_fun InducedCategory.Hom.hom at e
  obtain rfl : g = h := ConcreteCategory.hom_ext _ _ fun y => by
    rw [← (h₁ y).choose_spec]
    simpa using congr(($e).base.hom (h₁ y).choose)
  refine SheafedSpace.hom_stalk_ext ⟨g, gc⟩ ⟨g, hc⟩ rfl fun y => ?_
  rw [← (h₁ y).choose_spec]; rw [← cancel_mono (f.hom.stalkMap (h₁ y).choose)]; rw [stalkCongr_hom]; rw [stalkSpecializes_refl]; rw [Category.id_comp]; rw [← PresheafedSpace.stalkMap.comp f.hom ⟨g]; rw [gc⟩]; rw [← PresheafedSpace.stalkMap.comp f.hom ⟨g]; rw [hc⟩]
  congr 1

end ConcreteCategory

end SheafedSpace

end AlgebraicGeometry
