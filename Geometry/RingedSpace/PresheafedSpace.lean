/-
Copyright (c) 2019 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import Mathlib.CategoryTheory.Adjunction.FullyFaithful
public import Mathlib.CategoryTheory.Elementwise
public import Mathlib.Topology.Sheaves.Presheaf

/-!
# Presheafed spaces

Introduces the category of topological spaces equipped with a presheaf (taking values in an
arbitrary target category `C`).

We further describe how to apply functors and natural transformations to the values of the
presheaves.
-/

@[expose] public section


open Opposite CategoryTheory CategoryTheory.Category CategoryTheory.Functor TopCat TopologicalSpace
  Topology

variable (C : Type*) [Category* C]

-- We could enable:
-- attribute [local aesop safe cases (rule_sets := [CategoryTheory])] Opens
-- although it doesn't appear to help in this file, in any case.

-- We could enable:
-- attribute [local aesop safe cases (rule_sets := [CategoryTheory])] Opposite
-- but this would probably require https://github.com/leanprover-community/aesop/issues/59
-- In any case, it doesn't seem to help in this file.

namespace AlgebraicGeometry

/--
Definition of `PresheafedSpace.` / `PresheafedSpace.` 的定义

English:
structure PresheafedSpace.{u}
  parameters: where
  axioms and operations (2):
    - carrier : TopCat.{u}
    - presheaf : carrier.Presheaf C

中文:
结构 Presheafed空间.{u}
  参数: where
  公理与运算 (2 个):
    - carrier : 顶元素范畴.{u}
    - presheaf : carrier.预层 C
-/
structure PresheafedSpace.{u} where
  carrier : TopCat.{u}
  protected presheaf : carrier.Presheaf C

variable {C}

namespace PresheafedSpace

/--
Instance `coeCarrier` / 实例 `coeCarrier`

English:
instance coeCarrier
  signature: : CoeOut (PresheafedSpace C) TopCat where coe X
  body: X.carrier

中文:
实例 coeCarrier
  签名: : CoeOut (Presheafed空间 C) 顶元素范畴 where coe X
  定义体: X.carrier

Depends on / 依赖: X.carrier, carrier
-/
instance coeCarrier : CoeOut (PresheafedSpace C) TopCat where coe X := X.carrier

attribute [coe] PresheafedSpace.carrier

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: CoeSort (PresheafedSpace C) Type*
  body: X.carrier

中文:
实例 :
  签名: CoeSort (Presheafed空间 C) 类型
  定义体: X.carrier

Depends on / 依赖: X.carrier, carrier
-/
instance : CoeSort (PresheafedSpace C) Type* where coe X := X.carrier

instance (X : PresheafedSpace C) : TopologicalSpace X :=
  X.carrier.str

/--
Definition of `const` / `const` 的定义

English:
definition const
  signature: (X : TopCat) (Z : C)
  body: X
  presheaf := (Functor.const _).obj Z

中文:
定义 const
  签名: (X : 顶元素范畴) (Z : C)
  定义体: X
  presheaf := (Functor.const _).obj Z
-/
def const (X : TopCat) (Z : C) : PresheafedSpace C where
  carrier := X
  presheaf := (Functor.const _).obj Z

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Inhabited
  signature: C] : Inhabited (PresheafedSpace C)
  body: ⟨const (TopCat.of PEmpty) default⟩

中文:
实例 [可居
  签名: C] : 可居 (Presheafed空间 C)
  定义体: ⟨const (TopCat.of PEmpty) default⟩

Depends on / 依赖: PEmpty, TopCat, TopCat.of
-/
instance [Inhabited C] : Inhabited (PresheafedSpace C) :=
  ⟨const (TopCat.of PEmpty) default⟩

/--
Definition of `Hom` / `Hom` 的定义

English:
structure Hom
  parameters: (X Y : PresheafedSpace C)
  axioms and operations (2):
    - base : (X : TopCat) ⟶ (Y : TopCat)
    - c : Y.presheaf ⟶ base _* X.presheaf

中文:
结构 态射
  参数: (X Y : Presheafed空间 C)
  公理与运算 (2 个):
    - base : (X : 顶元素范畴) ⟶ (Y : 顶元素范畴)
    - c : Y.presheaf ⟶ base _* X.presheaf
-/
structure Hom (X Y : PresheafedSpace C) where
  base : (X : TopCat) ⟶ (Y : TopCat)
  c : Y.presheaf ⟶ base _* X.presheaf

@[ext (iff := false)]
/--
theorem `Hom.ext` / 定理 `Hom.ext`

English:
theorem Hom.ext
  statement: {X Y : PresheafedSpace C} (α β : Hom X Y) (w : α.base = β.base)
  proof: by
  rcases α with ⟨base, c⟩
  rcases β with ⟨base', c'⟩
  dsimp at w
  subst w
  dsimp at h
  erw [whiskerRight_id', comp_id] at h
  subst h
  rfl

中文:
定理 态射.ext
  结论: {X Y : Presheafed空间 C} (α β : 态射 X Y) (w : α.base = β.base)
  证明: by
  rcases α with ⟨base, c⟩
  rcases β with ⟨base', c'⟩
  dsimp at w
  subst w
  dsimp at h
  erw [whiskerRight_id', comp_id] at h
  subst h
  rfl
-/
theorem Hom.ext {X Y : PresheafedSpace C} (α β : Hom X Y) (w : α.base = β.base)
    (h : α.c ≫ whiskerRight (eqToHom (by rw [w])) _ = β.c) : α = β := by
  rcases α with ⟨base, c⟩
  rcases β with ⟨base', c'⟩
  dsimp at w
  subst w
  dsimp at h
  erw [whiskerRight_id', comp_id] at h
  subst h
  rfl

-- TODO including `injections` would make tidy work earlier.
/--
theorem `hext` / 定理 `hext`

English:
theorem hext
  given: {X Y : PresheafedSpace C} (α β : Hom X Y) (w : α.base = β.base) (h : α.c ≍ β.c)
  proof: by
  cases α
  cases β
  congr

中文:
定理 hext
  条件: {X Y : Presheafed空间 C} (α β : 态射 X Y) (w : α.base = β.base) (h : α.c ≍ β.c)
  证明: by
  cases α
  cases β
  congr
-/
theorem hext {X Y : PresheafedSpace C} (α β : Hom X Y) (w : α.base = β.base) (h : α.c ≍ β.c) :
    α = β := by
  cases α
  cases β
  congr

/--
Definition of `id` / `id` 的定义

English:
definition id
  signature: (X : PresheafedSpace C)
  body: 𝟙 (X : TopCat)
  c := 𝟙 _

中文:
定义 id
  签名: (X : Presheafed空间 C)
  定义体: 𝟙 (X : TopCat)
  c := 𝟙 _

Depends on / 依赖: TopCat
-/
def id (X : PresheafedSpace C) : Hom X X where
  base := 𝟙 (X : TopCat)
  c := 𝟙 _

/--
Instance `homInhabited` / 实例 `homInhabited`

English:
instance homInhabited
  signature: (X : PresheafedSpace C)
  body: ⟨id X⟩

中文:
实例 homInhabited
  签名: (X : Presheafed空间 C)
  定义体: ⟨id X⟩
-/
instance homInhabited (X : PresheafedSpace C) : Inhabited (Hom X X) :=
  ⟨id X⟩

/--
Definition of `comp` / `comp` 的定义

English:
definition comp
  signature: {X Y Z : PresheafedSpace C} (α : Hom X Y) (β : Hom Y Z)
  body: α.base ≫ β.base
  c := β.c ≫ (Presheaf.pushforward _ β.base).map α.c

中文:
定义 comp
  签名: {X Y Z : Presheafed空间 C} (α : 态射 X Y) (β : 态射 Y Z)
  定义体: α.base ≫ β.base
  c := β.c ≫ (Presheaf.pushforward _ β.base).map α.c
-/
def comp {X Y Z : PresheafedSpace C} (α : Hom X Y) (β : Hom Y Z) : Hom X Z where
  base := α.base ≫ β.base
  c := β.c ≫ (Presheaf.pushforward _ β.base).map α.c

/--
theorem `comp_c` / 定理 `comp_c`

English:
theorem comp_c
  given: {X Y Z : PresheafedSpace C} (α : Hom X Y) (β : Hom Y Z)
  proof: rfl

中文:
定理 comp_c
  条件: {X Y Z : Presheafed空间 C} (α : 态射 X Y) (β : 态射 Y Z)
  证明: rfl
-/
theorem comp_c {X Y Z : PresheafedSpace C} (α : Hom X Y) (β : Hom Y Z) :
    (comp α β).c = β.c ≫ (Presheaf.pushforward _ β.base).map α.c :=
  rfl

variable (C)

section

attribute [local simp] id comp

set_option backward.isDefEq.respectTransparency false in
/--
Instance `categoryOfPresheafedSpaces` / 实例 `categoryOfPresheafedSpaces`

English:
instance categoryOfPresheafedSpaces
  signature: : Category (PresheafedSpace C) where
  body: Hom
  id := id
  comp := comp

中文:
实例 categoryOfPresheafedSpaces
  签名: : 范畴 (Presheafed空间 C) where
  定义体: Hom
  id := id
  comp := comp
-/
instance categoryOfPresheafedSpaces : Category (PresheafedSpace C) where
  Hom := Hom
  id := id
  comp := comp

variable {C}

/--
Definition of `Hom.toPshHom` / `Hom.toPshHom` 的定义

English:
abbreviation Hom.toPshHom
  signature: {X Y : PresheafedSpace C} (f : Hom X Y)
  body: f

@[ext (iff := false)]

中文:
缩写 态射.toPshHom
  签名: {X Y : Presheafed空间 C} (f : 态射 X Y)
  定义体: f

@[ext (iff := false)]
-/
abbrev Hom.toPshHom {X Y : PresheafedSpace C} (f : Hom X Y) : X ⟶ Y := f

@[ext (iff := false)]
/--
theorem `ext` / 定理 `ext`

English:
theorem ext
  statement: {X Y : PresheafedSpace C} (α β : X ⟶ Y) (w : α.base = β.base)
  proof: Hom.ext α β w h

中文:
定理 ext
  结论: {X Y : Presheafed空间 C} (α β : X ⟶ Y) (w : α.base = β.base)
  证明: Hom.ext α β w h

Depends on / 依赖: Hom.ext
-/
theorem ext {X Y : PresheafedSpace C} (α β : X ⟶ Y) (w : α.base = β.base)
    (h : α.c ≫ whiskerRight (eqToHom (by rw [w])) _ = β.c) : α = β :=
  Hom.ext α β w h

end

variable {C}

attribute [local simp] eqToHom_map

@[simp]
/--
theorem `id_base` / 定理 `id_base`

English:
theorem id_base
  given: (X : PresheafedSpace C)
  statement: (𝟙 X : X ⟶ X).base = 𝟙 (X : TopCat)
  proof: rfl

中文:
定理 id_base
  条件: (X : Presheafed空间 C)
  结论: (𝟙 X : X ⟶ X).base = 𝟙 (X : 顶元素范畴)
  证明: rfl
-/
theorem id_base (X : PresheafedSpace C) : (𝟙 X : X ⟶ X).base = 𝟙 (X : TopCat) :=
  rfl

/--
theorem `id_c` / 定理 `id_c`

English:
theorem id_c
  given: (X : PresheafedSpace C)
  proof: rfl

中文:
定理 id_c
  条件: (X : Presheafed空间 C)
  证明: rfl
-/
theorem id_c (X : PresheafedSpace C) :
    (𝟙 X : X ⟶ X).c = 𝟙 X.presheaf :=
  rfl

set_option backward.isDefEq.respectTransparency.types false in
@[simp]
/--
theorem `id_c_app` / 定理 `id_c_app`

English:
theorem id_c_app
  given: (X : PresheafedSpace C) (U)
  proof: by
  rw [id_c]; rw [map_id]
  rfl

@[simp, reassoc]

中文:
定理 id_c_app
  条件: (X : Presheafed空间 C) (U)
  证明: by
  rw [id_c]; rw [map_id]
  rfl

@[simp, reassoc]

Depends on / 依赖: CommSemiring, CommSemiring.strongRankCondition_of_nontrivial, Nontrivial, id_c, map_id, strongRankCondition_of_nontrivial
-/
theorem id_c_app (X : PresheafedSpace C) (U) :
    (𝟙 X : X ⟶ X).c.app U = X.presheaf.map (𝟙 U) := by
  rw [id_c]; rw [map_id]
  rfl

@[simp, reassoc]
/--
theorem `comp_base` / 定理 `comp_base`

English:
theorem comp_base
  given: {X Y Z : PresheafedSpace C} (f : X ⟶ Y) (g : Y ⟶ Z)
  proof: rfl

中文:
定理 comp_base
  条件: {X Y Z : Presheafed空间 C} (f : X ⟶ Y) (g : Y ⟶ Z)
  证明: rfl
-/
theorem comp_base {X Y Z : PresheafedSpace C} (f : X ⟶ Y) (g : Y ⟶ Z) :
    (f ≫ g).base = f.base ≫ g.base :=
  rfl

instance (X Y : PresheafedSpace C) : CoeFun (X ⟶ Y) fun _ => (↑X -> ↑Y) :=
  ⟨fun f => f.base⟩

/-!
Note that we don't include a `ConcreteCategory` instance, since equality of morphisms `X ⟶ Y`
does not follow from equality of their coercions `X → Y`.
-/

-- The `reassoc` attribute was added despite the LHS not being a composition of two homs,
-- for the reasons explained in the docstring.
-- As there is no composition in the LHS it is purposely `@[reassoc, simp]` rather
-- than `@[reassoc (attr := simp)]`
set_option backward.isDefEq.respectTransparency false in -- Needed in HasColimits.lean
/-- Sometimes rewriting with `comp_c_app` doesn't work because of dependent type issues.
In that case, `erw comp_c_app_assoc` might make progress.
The lemma `comp_c_app_assoc` is also better suited for rewrites in the opposite direction. -/
@[reassoc, simp]
/--
theorem `comp_c_app` / 定理 `comp_c_app`

English:
theorem comp_c_app
  given: {X Y Z : PresheafedSpace C} (α : X ⟶ Y) (β : Y ⟶ Z) (U)
  proof: rfl

中文:
定理 comp_c_app
  条件: {X Y Z : Presheafed空间 C} (α : X ⟶ Y) (β : Y ⟶ Z) (U)
  证明: rfl
-/
theorem comp_c_app {X Y Z : PresheafedSpace C} (α : X ⟶ Y) (β : Y ⟶ Z) (U) :
    (α ≫ β).c.app U = β.c.app U ≫ α.c.app (op ((Opens.map β.base).obj (unop U))) :=
  rfl

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/--
theorem `congr_app` / 定理 `congr_app`

English:
theorem congr_app
  given: {X Y : PresheafedSpace C} {α β : X ⟶ Y} (h : α = β) (U)
  proof: by
  subst h
  simp

中文:
定理 congr_app
  条件: {X Y : Presheafed空间 C} {α β : X ⟶ Y} (h : α = β) (U)
  证明: by
  subst h
  simp
-/
theorem congr_app {X Y : PresheafedSpace C} {α β : X ⟶ Y} (h : α = β) (U) :
    α.c.app U = β.c.app U ≫ X.presheaf.map (eqToHom (by subst h; rfl)) := by
  subst h
  simp

section

variable (C)

/-- The forgetful functor from `PresheafedSpace` to `TopCat`. -/
@[simps]
/--
Definition of `forget` / `forget` 的定义

English:
definition forget
  signature: : PresheafedSpace C ⥤ TopCat where
  body: (X : TopCat)
  map f := f.base

中文:
定义 forget
  签名: : Presheafed空间 C ⥤ 顶元素范畴 where
  定义体: (X : TopCat)
  map f := f.base

Depends on / 依赖: TopCat
-/
def forget : PresheafedSpace C ⥤ TopCat where
  obj X := (X : TopCat)
  map f := f.base

end

section Iso

variable {X Y : PresheafedSpace C}

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- An isomorphism of `PresheafedSpace`s is a homeomorphism of the underlying space, and a
natural transformation between the sheaves.
-/
@[simps hom inv]
/--
Definition of `isoOfComponents` / `isoOfComponents` 的定义

English:
definition isoOfComponents
  signature: (H : X.1 ≅ Y.1) (α : H.hom _* X.2 ≅ Y.2)
  body: { base := H.hom
      c := α.inv }
  inv :=
    { base := H.inv
      c := Presheaf.toPushforwardOfIso H α.hom }
  hom_inv_id := by ext <;> simp
  inv_hom_id := by
    ext
    · dsimp
      exact H.inv_hom_id_apply _
    dsimp
    simp only [Presheaf.toPushforwardOfIso_app, assoc, ← α.hom.naturality]
    simp only [eqToHom_map, eqToHom_app, eqToHom_trans_assoc, eqToHom_refl, id_comp]
    apply Iso.inv_hom_id_app

中文:
定义 isoOfComponents
  签名: (H : X.1 ≅ Y.1) (α : H.hom _* X.2 ≅ Y.2)
  定义体: { base := H.hom
      c := α.inv }
  inv :=
    { base := H.inv
      c := Presheaf.toPushforwardOfIso H α.hom }
  hom_inv_id := by ext <;> simp
  inv_hom_id := by
    ext
    · dsimp
      exact H.inv_hom_id_apply _
    dsimp
    simp only [Presheaf.toPushforwardOfIso_app, assoc, ← α.hom.naturality]
    simp only [eqToHom_map, eqToHom_app, eqToHom_trans_assoc, eqToHom_refl, id_comp]
    apply Iso.inv_hom_id_app

Depends on / 依赖: H.hom, H.inv, H.inv_hom_id_apply, Iso.inv_hom_id_app, Presheaf, Presheaf.toPushforwardOfIso, Presheaf.toPushforwardOfIso_app, eqToHom_app, eqToHom_map, eqToHom_refl, eqToHom_trans_assoc, hom.naturality, hom_inv_id, id_comp, inv_hom_id, inv_hom_id_app, inv_hom_id_apply, naturality, toPushforwardOfIso, toPushforwardOfIso_app
-/
def isoOfComponents (H : X.1 ≅ Y.1) (α : H.hom _* X.2 ≅ Y.2) : X ≅ Y where
  hom :=
    { base := H.hom
      c := α.inv }
  inv :=
    { base := H.inv
      c := Presheaf.toPushforwardOfIso H α.hom }
  hom_inv_id := by ext <;> simp
  inv_hom_id := by
    ext
    · dsimp
      exact H.inv_hom_id_apply _
    dsimp
    simp only [Presheaf.toPushforwardOfIso_app, assoc, ← α.hom.naturality]
    simp only [eqToHom_map, eqToHom_app, eqToHom_trans_assoc, eqToHom_refl, id_comp]
    apply Iso.inv_hom_id_app

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- Isomorphic `PresheafedSpace`s have naturally isomorphic presheaves. -/
@[simps]
/--
Definition of `sheafIsoOfIso` / `sheafIsoOfIso` 的定义

English:
definition sheafIsoOfIso
  signature: (H : X ≅ Y)
  body: H.hom.c
  inv := Presheaf.pushforwardToOfIso ((forget _).mapIso H).symm H.inv.c
  hom_inv_id := by
    ext U
    rw [NatTrans.comp_app]
    simpa using! congr_arg (fun f => f ≫ eqToHom _) (congr_app H.inv_hom_id (op U))
  inv_hom_id := by
    ext U
    dsimp
    rw [NatTrans.id_app]
    simp only [Presheaf.pushforwardToOfIso_app, Iso.symm_inv, mapIso_hom, forget_map,
      Iso.symm_hom, mapIso_inv, eqToHom_map, assoc]
    have eq₁ := congr_app H.hom_inv_id (op ((Opens.map H.hom.base).obj U))
    have eq₂ := H.hom.c.naturality (eqToHom (congr_obj (congr_arg Opens.map
      ((forget C).congr_map H.inv_hom_id.symm)) U)).op
    rw [id_c]; rw [NatTrans.id_app]; rw [id_comp]; rw [eqToHom_map]; rw [comp_c_app] at eq₁
    rw [eqToHom_op]; rw [eqToHom_map] at eq₂
    erw [eq₂, reassoc_of% eq₁]
    simp

中文:
定义 sheafIsoOfIso
  签名: (H : X ≅ Y)
  定义体: H.hom.c
  inv := Presheaf.pushforwardToOfIso ((forget _).mapIso H).symm H.inv.c
  hom_inv_id := by
    ext U
    rw [NatTrans.comp_app]
    simpa using! congr_arg (fun f => f ≫ eqToHom _) (congr_app H.inv_hom_id (op U))
  inv_hom_id := by
    ext U
    dsimp
    rw [NatTrans.id_app]
    simp only [Presheaf.pushforwardToOfIso_app, Iso.symm_inv, mapIso_hom, forget_map,
      Iso.symm_hom, mapIso_inv, eqToHom_map, assoc]
    have eq₁ := congr_app H.hom_inv_id (op ((Opens.map H.hom.base).obj U))
    have eq₂ := H.hom.c.naturality (eqToHom (congr_obj (congr_arg Opens.map
      ((forget C).congr_map H.inv_hom_id.symm)) U)).op
    rw [id_c]; rw [NatTrans.id_app]; rw [id_comp]; rw [eqToHom_map]; rw [comp_c_app] at eq₁
    rw [eqToHom_op]; rw [eqToHom_map] at eq₂
    erw [eq₂, reassoc_of% eq₁]
    simp

Depends on / 依赖: H.hom.c
-/
def sheafIsoOfIso (H : X ≅ Y) : Y.2 ≅ H.hom.base _* X.2 where
  hom := H.hom.c
  inv := Presheaf.pushforwardToOfIso ((forget _).mapIso H).symm H.inv.c
  hom_inv_id := by
    ext U
    rw [NatTrans.comp_app]
    simpa using! congr_arg (fun f => f ≫ eqToHom _) (congr_app H.inv_hom_id (op U))
  inv_hom_id := by
    ext U
    dsimp
    rw [NatTrans.id_app]
    simp only [Presheaf.pushforwardToOfIso_app, Iso.symm_inv, mapIso_hom, forget_map,
      Iso.symm_hom, mapIso_inv, eqToHom_map, assoc]
    have eq₁ := congr_app H.hom_inv_id (op ((Opens.map H.hom.base).obj U))
    have eq₂ := H.hom.c.naturality (eqToHom (congr_obj (congr_arg Opens.map
      ((forget C).congr_map H.inv_hom_id.symm)) U)).op
    rw [id_c]; rw [NatTrans.id_app]; rw [id_comp]; rw [eqToHom_map]; rw [comp_c_app] at eq₁
    rw [eqToHom_op]; rw [eqToHom_map] at eq₂
    erw [eq₂, reassoc_of% eq₁]
    simp

/--
Instance `base_isIso_of_iso` / 实例 `base_isIso_of_iso`

English:
instance base_isIso_of_iso
  signature: (f : X ⟶ Y) [IsIso f]
  body: ((forget _).mapIso (asIso f)).isIso_hom

中文:
实例 base_isIso_of_iso
  签名: (f : X ⟶ Y) [是同构 f]
  定义体: ((forget _).mapIso (asIso f)).isIso_hom

Depends on / 依赖: forget, isIso_hom, mapIso
-/
instance base_isIso_of_iso (f : X ⟶ Y) [IsIso f] : IsIso f.base :=
  ((forget _).mapIso (asIso f)).isIso_hom

/--
Instance `c_isIso_of_iso` / 实例 `c_isIso_of_iso`

English:
instance c_isIso_of_iso
  signature: (f : X ⟶ Y) [IsIso f]
  body: (sheafIsoOfIso (asIso f)).isIso_hom

中文:
实例 c_isIso_of_iso
  签名: (f : X ⟶ Y) [是同构 f]
  定义体: (sheafIsoOfIso (asIso f)).isIso_hom

Depends on / 依赖: isIso_hom, sheafIsoOfIso
-/
instance c_isIso_of_iso (f : X ⟶ Y) [IsIso f] : IsIso f.c :=
  (sheafIsoOfIso (asIso f)).isIso_hom

/--
theorem `isIso_of_components` / 定理 `isIso_of_components`

English:
theorem isIso_of_components
  given: (f : X ⟶ Y) [IsIso f.base] [IsIso f.c]
  statement: IsIso f
  proof: (isoOfComponents (asIso f.base) (asIso f.c).symm).isIso_hom

中文:
定理 isIso_of_components
  条件: (f : X ⟶ Y) [是同构 f.base] [是同构 f.c]
  结论: 是同构 f
  证明: (isoOfComponents (asIso f.base) (asIso f.c).symm).isIso_hom

Depends on / 依赖: f.base, isIso_hom, isoOfComponents
-/
theorem isIso_of_components (f : X ⟶ Y) [IsIso f.base] [IsIso f.c] : IsIso f :=
  (isoOfComponents (asIso f.base) (asIso f.c).symm).isIso_hom

end Iso

section Restrict

/-- The restriction of a presheafed space along an open embedding into the space.
-/
@[simps]
/--
Definition of `restrict` / `restrict` 的定义

English:
definition restrict
  signature: {U : TopCat} (X : PresheafedSpace C) {f : U ⟶ (X : TopCat)}
  body: U
  presheaf := h.functor.op ⋙ X.presheaf

中文:
定义 restrict
  签名: {U : 顶元素范畴} (X : Presheafed空间 C) {f : U ⟶ (X : 顶元素范畴)}
  定义体: U
  presheaf := h.functor.op ⋙ X.presheaf
-/
def restrict {U : TopCat} (X : PresheafedSpace C) {f : U ⟶ (X : TopCat)}
    (h : IsOpenEmbedding f) : PresheafedSpace C where
  carrier := U
  presheaf := h.functor.op ⋙ X.presheaf

set_option backward.isDefEq.respectTransparency false in
/-- The map from the restriction of a presheafed space.
-/
@[simps]
/--
Definition of `ofRestrict` / `ofRestrict` 的定义

English:
definition ofRestrict
  signature: {U : TopCat} (X : PresheafedSpace C) {f : U ⟶ (X : TopCat)}
  body: f
  c :=
    { app := fun V => X.presheaf.map (h.isOpenMap.adjunction.counit.app V.unop).op
      naturality := fun U V f =>
        show _ = _ ≫ X.presheaf.map _ by
          rw [← map_comp]; rw [← map_comp]
          rfl }

中文:
定义 ofRestrict
  签名: {U : 顶元素范畴} (X : Presheafed空间 C) {f : U ⟶ (X : 顶元素范畴)}
  定义体: f
  c :=
    { app := fun V => X.presheaf.map (h.isOpenMap.adjunction.counit.app V.unop).op
      naturality := fun U V f =>
        show _ = _ ≫ X.presheaf.map _ by
          rw [← map_comp]; rw [← map_comp]
          rfl }
-/
def ofRestrict {U : TopCat} (X : PresheafedSpace C) {f : U ⟶ (X : TopCat)}
    (h : IsOpenEmbedding f) : X.restrict h ⟶ X where
  base := f
  c :=
    { app := fun V => X.presheaf.map (h.isOpenMap.adjunction.counit.app V.unop).op
      naturality := fun U V f =>
        show _ = _ ≫ X.presheaf.map _ by
          rw [← map_comp]; rw [← map_comp]
          rfl }

set_option backward.isDefEq.respectTransparency false in
/--
Instance `ofRestrict_mono` / 实例 `ofRestrict_mono`

English:
instance ofRestrict_mono
  signature: {U : TopCat} (X : PresheafedSpace C) (f : U ⟶ X.1)
  body: by
  have : Mono f := (TopCat.mono_iff_injective _).mpr hf.injective
  constructor
  intro Z g₁ g₂ eq
  ext1
  · have := congr_arg PresheafedSpace.Hom.base eq
    simp only [PresheafedSpace.comp_base, PresheafedSpace.ofRestrict_base] at this
    rw [cancel_mono] at this
    exact this
  · ext V
    have hV : (Opens.map (X.ofRestrict hf).base).obj (hf.functor.obj V) = V := by
      ext1
      exact Set.preimage_image_eq _ hf.injective
    have :
      IsIso (hf.isOpenMap.adjunction.counit.app (unop (op (hf.functor.obj V)))) :=
        NatIso.isIso_app_of_isIso
          (whiskerLeft hf.functor hf.isOpenMap.adjunction.counit) V
    have := PresheafedSpace.congr_app eq (op (hf.functor.obj V))
    rw [PresheafedSpace.comp_c_app]; rw [PresheafedSpace.comp_c_app]; rw [PresheafedSpace.ofRestrict_c_app]; rw [Category.assoc]; rw [cancel_epi] at this
    have h : _ ≫ _ = _ ≫ _ ≫ _ :=
      congr_arg (fun f => (X.restrict hf).presheaf.map (eqToHom hV).op ≫ f) this
    simp only [g₁.c.naturality, g₂.c.naturality_assoc] at h
    simp only [eqToHom_op, eqToHom_map, eqToHom_trans,
      ← IsIso.comp_inv_eq, inv_eqToHom, Category.assoc] at h
    simpa using h

中文:
实例 ofRestrict_mono
  签名: {U : 顶元素范畴} (X : Presheafed空间 C) (f : U ⟶ X.1)
  定义体: by
  have : Mono f := (TopCat.mono_iff_injective _).mpr hf.injective
  constructor
  intro Z g₁ g₂ eq
  ext1
  · have := congr_arg PresheafedSpace.Hom.base eq
    simp only [PresheafedSpace.comp_base, PresheafedSpace.ofRestrict_base] at this
    rw [cancel_mono] at this
    exact this
  · ext V
    have hV : (Opens.map (X.ofRestrict hf).base).obj (hf.functor.obj V) = V := by
      ext1
      exact Set.preimage_image_eq _ hf.injective
    have :
      IsIso (hf.isOpenMap.adjunction.counit.app (unop (op (hf.functor.obj V)))) :=
        NatIso.isIso_app_of_isIso
          (whiskerLeft hf.functor hf.isOpenMap.adjunction.counit) V
    have := PresheafedSpace.congr_app eq (op (hf.functor.obj V))
    rw [PresheafedSpace.comp_c_app]; rw [PresheafedSpace.comp_c_app]; rw [PresheafedSpace.ofRestrict_c_app]; rw [Category.assoc]; rw [cancel_epi] at this
    have h : _ ≫ _ = _ ≫ _ ≫ _ :=
      congr_arg (fun f => (X.restrict hf).presheaf.map (eqToHom hV).op ≫ f) this
    simp only [g₁.c.naturality, g₂.c.naturality_assoc] at h
    simp only [eqToHom_op, eqToHom_map, eqToHom_trans,
      ← IsIso.comp_inv_eq, inv_eqToHom, Category.assoc] at h
    simpa using h

Depends on / 依赖: NatIso, NatIso.isIso_app_o, Opens.map, PresheafedSpace, PresheafedSpace.Hom.base, PresheafedSpace.comp_base, PresheafedSpace.ofRestrict_base, Set.preimage_image_eq, TopCat, TopCat.mono_iff_injective, X.ofRestrict, adjunction, cancel_mono, comp_base, congr_arg, counit, functor, hf.functor.obj, hf.injective, hf.isOpenMap.adjunction.counit.app
-/
instance ofRestrict_mono {U : TopCat} (X : PresheafedSpace C) (f : U ⟶ X.1)
    (hf : IsOpenEmbedding f) : Mono (X.ofRestrict hf) := by
  have : Mono f := (TopCat.mono_iff_injective _).mpr hf.injective
  constructor
  intro Z g₁ g₂ eq
  ext1
  · have := congr_arg PresheafedSpace.Hom.base eq
    simp only [PresheafedSpace.comp_base, PresheafedSpace.ofRestrict_base] at this
    rw [cancel_mono] at this
    exact this
  · ext V
    have hV : (Opens.map (X.ofRestrict hf).base).obj (hf.functor.obj V) = V := by
      ext1
      exact Set.preimage_image_eq _ hf.injective
    have :
      IsIso (hf.isOpenMap.adjunction.counit.app (unop (op (hf.functor.obj V)))) :=
        NatIso.isIso_app_of_isIso
          (whiskerLeft hf.functor hf.isOpenMap.adjunction.counit) V
    have := PresheafedSpace.congr_app eq (op (hf.functor.obj V))
    rw [PresheafedSpace.comp_c_app]; rw [PresheafedSpace.comp_c_app]; rw [PresheafedSpace.ofRestrict_c_app]; rw [Category.assoc]; rw [cancel_epi] at this
    have h : _ ≫ _ = _ ≫ _ ≫ _ :=
      congr_arg (fun f => (X.restrict hf).presheaf.map (eqToHom hV).op ≫ f) this
    simp only [g₁.c.naturality, g₂.c.naturality_assoc] at h
    simp only [eqToHom_op, eqToHom_map, eqToHom_trans,
      ← IsIso.comp_inv_eq, inv_eqToHom, Category.assoc] at h
    simpa using h

set_option backward.defeqAttrib.useBackward true in
/--
theorem `restrict_top_presheaf` / 定理 `restrict_top_presheaf`

English:
theorem restrict_top_presheaf
  given: (X : PresheafedSpace C)
  proof: by
  dsimp
  rw [Opens.inclusion'_top_functor X.carrier]
  rfl

中文:
定理 restrict_top_presheaf
  条件: (X : Presheafed空间 C)
  证明: by
  dsimp
  rw [Opens.inclusion'_top_functor X.carrier]
  rfl

Depends on / 依赖: Opens.inclusion, X.carrier, _top_functor, carrier, inclusion
-/
theorem restrict_top_presheaf (X : PresheafedSpace C) :
    (X.restrict (Opens.isOpenEmbedding ⊤)).presheaf =
      (Opens.inclusionTopIso X.carrier).inv _* X.presheaf := by
  dsimp
  rw [Opens.inclusion'_top_functor X.carrier]
  rfl

set_option backward.isDefEq.respectTransparency false in
/--
theorem `ofRestrict_top_c` / 定理 `ofRestrict_top_c`

English:
theorem ofRestrict_top_c
  given: (X : PresheafedSpace C)
  proof: by
  /- another approach would be to prove the left-hand side
       is a natural isomorphism, but I encountered a universe
       issue when `apply NatIso.isIso_of_isIso_app`. -/
  ext
  dsimp [ofRestrict]
  erw [eqToHom_map, eqToHom_app]
  simp

中文:
定理 ofRestrict_top_c
  条件: (X : Presheafed空间 C)
  证明: by
  /- another approach would be to prove the left-hand side
       is a natural isomorphism, but I encountered a universe
       issue when `apply NatIso.isIso_of_isIso_app`. -/
  ext
  dsimp [ofRestrict]
  erw [eqToHom_map, eqToHom_app]
  simp
-/
theorem ofRestrict_top_c (X : PresheafedSpace C) :
    (X.ofRestrict (Opens.isOpenEmbedding ⊤)).c =
      eqToHom
        (by
          rw [restrict_top_presheaf]; rw [← Presheaf.Pushforward.comp_eq]
          tauto) := by
  /- another approach would be to prove the left-hand side
       is a natural isomorphism, but I encountered a universe
       issue when `apply NatIso.isIso_of_isIso_app`. -/
  ext
  dsimp [ofRestrict]
  erw [eqToHom_map, eqToHom_app]
  simp

/-- The map to the restriction of a presheafed space along the canonical inclusion from the top
subspace.
-/
@[simps]
/--
Definition of `toRestrictTop` / `toRestrictTop` 的定义

English:
definition toRestrictTop
  signature: (X : PresheafedSpace C)
  body: (Opens.inclusionTopIso X.carrier).inv
  c := eqToHom (restrict_top_presheaf X)

中文:
定义 toRestrictTop
  签名: (X : Presheafed空间 C)
  定义体: (Opens.inclusionTopIso X.carrier).inv
  c := eqToHom (restrict_top_presheaf X)

Depends on / 依赖: Opens.inclusionTopIso, X.carrier, carrier, inclusionTopIso
-/
def toRestrictTop (X : PresheafedSpace C) : X ⟶ X.restrict (Opens.isOpenEmbedding ⊤) where
  base := (Opens.inclusionTopIso X.carrier).inv
  c := eqToHom (restrict_top_presheaf X)

/-- The isomorphism from the restriction to the top subspace.
-/
@[simps]
/--
Definition of `restrictTopIso` / `restrictTopIso` 的定义

English:
definition restrictTopIso
  signature: (X : PresheafedSpace C)
  body: X.ofRestrict _
  inv := X.toRestrictTop
  hom_inv_id := by
    ext
    · rfl
    · erw [comp_c, toRestrictTop_c, whiskerRight_id',
        comp_id, ofRestrict_top_c, eqToHom_map, eqToHom_trans, eqToHom_refl]
      rfl
  inv_hom_id := by
    ext
    · rfl
    · erw [comp_c, ofRestrict_top_c, toRestrictTop_c, eqToHom_map, whiskerRight_id', comp_id,
        eqToHom_trans, eqToHom_refl]
      rfl

中文:
定义 restrictTopIso
  签名: (X : Presheafed空间 C)
  定义体: X.ofRestrict _
  inv := X.toRestrictTop
  hom_inv_id := by
    ext
    · rfl
    · erw [comp_c, toRestrictTop_c, whiskerRight_id',
        comp_id, ofRestrict_top_c, eqToHom_map, eqToHom_trans, eqToHom_refl]
      rfl
  inv_hom_id := by
    ext
    · rfl
    · erw [comp_c, ofRestrict_top_c, toRestrictTop_c, eqToHom_map, whiskerRight_id', comp_id,
        eqToHom_trans, eqToHom_refl]
      rfl

Depends on / 依赖: X.ofRestrict, ofRestrict
-/
def restrictTopIso (X : PresheafedSpace C) : X.restrict (Opens.isOpenEmbedding ⊤) ≅ X where
  hom := X.ofRestrict _
  inv := X.toRestrictTop
  hom_inv_id := by
    ext
    · rfl
    · erw [comp_c, toRestrictTop_c, whiskerRight_id',
        comp_id, ofRestrict_top_c, eqToHom_map, eqToHom_trans, eqToHom_refl]
      rfl
  inv_hom_id := by
    ext
    · rfl
    · erw [comp_c, ofRestrict_top_c, toRestrictTop_c, eqToHom_map, whiskerRight_id', comp_id,
        eqToHom_trans, eqToHom_refl]
      rfl

end Restrict

/-- The global sections, notated Gamma.
-/
@[simps]
/--
Definition of `Γ` / `Γ` 的定义

English:
definition Γ
  signature: : (PresheafedSpace C)ᵒᵖ ⥤ C where
  body: (unop X).presheaf.obj (op ⊤)
  map f := f.unop.c.app (op ⊤)

中文:
定义 Γ
  签名: : (Presheafed空间 C)ᵒᵖ ⥤ C where
  定义体: (unop X).presheaf.obj (op ⊤)
  map f := f.unop.c.app (op ⊤)

Depends on / 依赖: presheaf, presheaf.obj
-/
def Γ : (PresheafedSpace C)ᵒᵖ ⥤ C where
  obj X := (unop X).presheaf.obj (op ⊤)
  map f := f.unop.c.app (op ⊤)

/--
theorem `Γ_obj_op` / 定理 `Γ_obj_op`

English:
theorem Γ_obj_op
  given: (X : PresheafedSpace C)
  statement: Γ.obj (op X) = X.presheaf.obj (op ⊤)
  proof: rfl

中文:
定理 Γ_obj_op
  条件: (X : Presheafed空间 C)
  结论: Γ.obj (op X) = X.presheaf.obj (op ⊤)
  证明: rfl
-/
theorem Γ_obj_op (X : PresheafedSpace C) : Γ.obj (op X) = X.presheaf.obj (op ⊤) :=
  rfl

/--
theorem `Γ_map_op` / 定理 `Γ_map_op`

English:
theorem Γ_map_op
  given: {X Y : PresheafedSpace C} (f : X ⟶ Y)
  statement: Γ.map f.op = f.c.app (op ⊤)
  proof: rfl

中文:
定理 Γ_map_op
  条件: {X Y : Presheafed空间 C} (f : X ⟶ Y)
  结论: Γ.map f.op = f.c.app (op ⊤)
  证明: rfl
-/
theorem Γ_map_op {X Y : PresheafedSpace C} (f : X ⟶ Y) : Γ.map f.op = f.c.app (op ⊤) :=
  rfl

end PresheafedSpace

end AlgebraicGeometry

open AlgebraicGeometry AlgebraicGeometry.PresheafedSpace

variable {C}

namespace CategoryTheory

variable {D : Type*} [Category* D]

namespace Functor

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/--
Definition of `mapPresheaf` / `mapPresheaf` 的定义

English:
definition mapPresheaf
  signature: (F : C ⥤ D)
  body: { carrier := X.carrier
      presheaf := X.presheaf ⋙ F }
  map f :=
    { base := f.base
      c := whiskerRight f.c F }
  -- Porting note: these proofs were automatic in mathlib3
  map_id X := by ext <;> cat_disch
  map_comp f g := by ext <;> cat_disch

@[simp]

中文:
定义 mapPresheaf
  签名: (F : C ⥤ D)
  定义体: { carrier := X.carrier
      presheaf := X.presheaf ⋙ F }
  map f :=
    { base := f.base
      c := whiskerRight f.c F }
  -- Porting note: these proofs were automatic in mathlib3
  map_id X := by ext <;> cat_disch
  map_comp f g := by ext <;> cat_disch

@[simp]

Depends on / 依赖: X.carrier, X.presheaf, carrier, f.base, presheaf, whiskerRight
-/
def mapPresheaf (F : C ⥤ D) : PresheafedSpace C ⥤ PresheafedSpace D where
  obj X :=
    { carrier := X.carrier
      presheaf := X.presheaf ⋙ F }
  map f :=
    { base := f.base
      c := whiskerRight f.c F }
  -- Porting note: these proofs were automatic in mathlib3
  map_id X := by ext <;> cat_disch
  map_comp f g := by ext <;> cat_disch

@[simp]
/--
theorem `mapPresheaf_obj_X` / 定理 `mapPresheaf_obj_X`

English:
theorem mapPresheaf_obj_X
  given: (F : C ⥤ D) (X : PresheafedSpace C)
  proof: rfl

@[simp]

中文:
定理 mapPresheaf_obj_X
  条件: (F : C ⥤ D) (X : Presheafed空间 C)
  证明: rfl

@[simp]
-/
theorem mapPresheaf_obj_X (F : C ⥤ D) (X : PresheafedSpace C) :
    (F.mapPresheaf.obj X : TopCat) = (X : TopCat) :=
  rfl

@[simp]
/--
theorem `mapPresheaf_obj_presheaf` / 定理 `mapPresheaf_obj_presheaf`

English:
theorem mapPresheaf_obj_presheaf
  given: (F : C ⥤ D) (X : PresheafedSpace C)
  proof: rfl

@[simp]

中文:
定理 mapPresheaf_obj_presheaf
  条件: (F : C ⥤ D) (X : Presheafed空间 C)
  证明: rfl

@[simp]
-/
theorem mapPresheaf_obj_presheaf (F : C ⥤ D) (X : PresheafedSpace C) :
    (F.mapPresheaf.obj X).presheaf = X.presheaf ⋙ F :=
  rfl

@[simp]
/--
theorem `mapPresheaf_map_f` / 定理 `mapPresheaf_map_f`

English:
theorem mapPresheaf_map_f
  given: (F : C ⥤ D) {X Y : PresheafedSpace C} (f : X ⟶ Y)
  proof: rfl

@[simp]

中文:
定理 mapPresheaf_map_f
  条件: (F : C ⥤ D) {X Y : Presheafed空间 C} (f : X ⟶ Y)
  证明: rfl

@[simp]
-/
theorem mapPresheaf_map_f (F : C ⥤ D) {X Y : PresheafedSpace C} (f : X ⟶ Y) :
    (F.mapPresheaf.map f).base = f.base :=
  rfl

@[simp]
/--
theorem `mapPresheaf_map_c` / 定理 `mapPresheaf_map_c`

English:
theorem mapPresheaf_map_c
  given: (F : C ⥤ D) {X Y : PresheafedSpace C} (f : X ⟶ Y)
  proof: rfl

中文:
定理 mapPresheaf_map_c
  条件: (F : C ⥤ D) {X Y : Presheafed空间 C} (f : X ⟶ Y)
  证明: rfl
-/
theorem mapPresheaf_map_c (F : C ⥤ D) {X Y : PresheafedSpace C} (f : X ⟶ Y) :
    (F.mapPresheaf.map f).c = whiskerRight f.c F :=
  rfl

end Functor

namespace NatTrans

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/--
Definition of `onPresheaf` / `onPresheaf` 的定义

English:
definition onPresheaf
  signature: {F G : C ⥤ D} (α : F ⟶ G)
  body: { base := 𝟙 _
      c := whiskerLeft X.presheaf α ≫ eqToHom (Presheaf.Pushforward.id_eq _).symm }

中文:
定义 onPresheaf
  签名: {F G : C ⥤ D} (α : F ⟶ G)
  定义体: { base := 𝟙 _
      c := whiskerLeft X.presheaf α ≫ eqToHom (Presheaf.Pushforward.id_eq _).symm }

Depends on / 依赖: Presheaf, Presheaf.Pushforward.id_eq, Pushforward, X.presheaf, eqToHom, id_eq, presheaf, whiskerLeft
-/
def onPresheaf {F G : C ⥤ D} (α : F ⟶ G) : G.mapPresheaf ⟶ F.mapPresheaf where
  app X :=
    { base := 𝟙 _
      c := whiskerLeft X.presheaf α ≫ eqToHom (Presheaf.Pushforward.id_eq _).symm }

-- TODO Assemble the last two constructions into a functor
-- `(C ⥤ D) ⥤ (PresheafedSpace C ⥤ PresheafedSpace D)`
end NatTrans

end CategoryTheory
