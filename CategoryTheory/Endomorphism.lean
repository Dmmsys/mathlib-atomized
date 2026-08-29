/-
Copyright (c) 2019 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov, Kim Morrison, Simon Hudon
-/
module

public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Group.Equiv.Defs
public import Mathlib.Algebra.Group.Opposite
public import Mathlib.Algebra.Group.Units.Hom
public import Mathlib.CategoryTheory.Groupoid

/-!
# Endomorphisms

Definition and basic properties of endomorphisms and automorphisms of an object in a category.

For each `X : C`, we provide `CategoryTheory.End X := X ⟶ X` with a monoid structure,
and `CategoryTheory.Aut X := X ≅ X` with a group structure.
-/

@[expose] public section


universe v v' u u'

namespace CategoryTheory

/-- Endomorphisms of an object in a category. Arguments order in multiplication agrees with
`Function.comp`, not with `CategoryTheory.CategoryStruct.comp`. -/
@[implicit_reducible]
/--
Definition of `End` / `End` 的定义

English:
definition End
  signature: {C : Type u} [CategoryStruct.{v} C] (X : C)
  body: X ⟶ X

中文:
定义 End
  签名: {C : 类型u} [CategoryStruct.{v} C] (X : C)
  定义体: X ⟶ X
-/
def End {C : Type u} [CategoryStruct.{v} C] (X : C) := X ⟶ X

namespace End

section Struct

variable {C : Type u} [CategoryStruct.{v} C] (X : C)

/--
Instance `one` / 实例 `one`

English:
instance one
  signature: : One (End X)
  body: ⟨𝟙 X⟩

中文:
实例 one
  签名: : One (End X)
  定义体: ⟨𝟙 X⟩
-/
protected instance one : One (End X) := ⟨𝟙 X⟩

/--
Instance `inhabited` / 实例 `inhabited`

English:
instance inhabited
  signature: : Inhabited (End X)
  body: ⟨𝟙 X⟩

中文:
实例 inhabited
  签名: : Inhabited (End X)
  定义体: ⟨𝟙 X⟩
-/
protected instance inhabited : Inhabited (End X) := ⟨𝟙 X⟩

/--
Instance `mul` / 实例 `mul`

English:
instance mul
  signature: : Mul (End X)
  body: ⟨fun x y => y ≫ x⟩

中文:
实例 mul
  签名: : Mul (End X)
  定义体: ⟨fun x y => y ≫ x⟩
-/
protected instance mul : Mul (End X) := ⟨fun x y => y ≫ x⟩

variable {X}

/--
Definition of `of` / `of` 的定义

English:
abbreviation of
  signature: (f : X ⟶ X)
  body: f

中文:
缩写 of
  签名: (f : X ⟶ X)
  定义体: f
-/
abbrev of (f : X ⟶ X) : End X := f

/--
Definition of `asHom` / `asHom` 的定义

English:
abbreviation asHom
  signature: (f : End X)
  body: f

中文:
缩写 asHom
  签名: (f : End X)
  定义体: f
-/
abbrev asHom (f : End X) : X ⟶ X := f

-- TODO: to fix defeq abuse, this should be `(1 : End x) = of (𝟙 X)`.
-- But that would require many more extra simp lemmas to get rid of the `of`.
@[simp]
/--
theorem `one_def` / 定理 `one_def`

English:
theorem one_def
  statement: (1 : End X) = 𝟙 X
  proof: rfl

中文:
定理 one_def
  结论: (1 : End X) = 𝟙 X
  证明: rfl
-/
theorem one_def : (1 : End X) = 𝟙 X := rfl

-- TODO: to fix defeq abuse, this should be `xs * ys = of (ys ≫ xs)`.
-- But that would require many more extra simp lemmas to get rid of the `of`.
@[simp]
/--
theorem `mul_def` / 定理 `mul_def`

English:
theorem mul_def
  given: (xs ys : End X)
  statement: xs * ys = ys ≫ xs
  proof: rfl

中文:
定理 mul_def
  条件: (xs ys : End X)
  结论: xs * ys = ys ≫ xs
  证明: rfl
-/
theorem mul_def (xs ys : End X) : xs * ys = ys ≫ xs := rfl

/--
lemma `ext` / 引理 `ext`

English:
lemma ext
  given: {x y : End X} (h : asHom x = asHom y)
  statement: x = y
  proof: h

中文:
引理 ext
  条件: {x y : End X} (h : asHom x = asHom y)
  结论: x = y
  证明: h
-/
lemma ext {x y : End X} (h : asHom x = asHom y) : x = y := h

end Struct

/--
Instance `monoid` / 实例 `monoid`

English:
instance monoid
  signature: {C : Type u} [Category.{v} C] {X : C}
  body: Category.id_comp
  one_mul := Category.comp_id
  mul_assoc := fun x y z => (Category.assoc z y x).symm

中文:
实例 monoid
  签名: {C : 类型u} [Category.{v} C] {X : C}
  定义体: Category.id_comp
  one_mul := Category.comp_id
  mul_assoc := fun x y z => (Category.assoc z y x).symm

Depends on / 依赖: Category, Category.id_comp, Functor, Functor.map_comp, id_comp, map_comp
-/
instance monoid {C : Type u} [Category.{v} C] {X : C} : Monoid (End X) where
  mul_one := Category.id_comp
  one_mul := Category.comp_id
  mul_assoc := fun x y z => (Category.assoc z y x).symm

section MulAction

variable {C : Type u} [Category.{v} C]

open Opposite

/--
Instance `mulActionRight` / 实例 `mulActionRight`

English:
instance mulActionRight
  signature: {X Y : C}
  body: f ≫ r
  one_smul := Category.comp_id
mul_smul _ _ _ := Eq.symm Category.assoc _ _ _

中文:
实例 mulActionRight
  签名: {X Y : C}
  定义体: f ≫ r
  one_smul := Category.comp_id
mul_smul _ _ _ := Eq.symm Category.assoc _ _ _
-/
instance mulActionRight {X Y : C} : MulAction (End Y) (X ⟶ Y) where
  smul r f := f ≫ r
  one_smul := Category.comp_id
mul_smul _ _ _ := Eq.symm Category.assoc _ _ _

/--
Instance `mulActionLeft` / 实例 `mulActionLeft`

English:
instance mulActionLeft
  signature: {X Y : C}
  body: r.unop ≫ f
  one_smul := Category.id_comp
  mul_smul _ _ _ := Category.assoc _ _ _

中文:
实例 mulActionLeft
  签名: {X Y : C}
  定义体: r.unop ≫ f
  one_smul := Category.id_comp
  mul_smul _ _ _ := Category.assoc _ _ _

Depends on / 依赖: r.unop
-/
instance mulActionLeft {X Y : C} : MulAction (End X)ᵐᵒᵖ (X ⟶ Y) where
  smul r f := r.unop ≫ f
  one_smul := Category.id_comp
  mul_smul _ _ _ := Category.assoc _ _ _

/--
theorem `smul_right` / 定理 `smul_right`

English:
theorem smul_right
  given: {X Y : C} {r : End Y} {f : X ⟶ Y}
  statement: r • f = f ≫ r
  proof: rfl

中文:
定理 smul_right
  条件: {X Y : C} {r : End Y} {f : X ⟶ Y}
  结论: r • f = f ≫ r
  证明: rfl
-/
theorem smul_right {X Y : C} {r : End Y} {f : X ⟶ Y} : r • f = f ≫ r :=
  rfl

/--
theorem `smul_left` / 定理 `smul_left`

English:
theorem smul_left
  given: {X Y : C} {r : (End X)ᵐᵒᵖ} {f : X ⟶ Y}
  statement: r • f = r.unop ≫ f
  proof: rfl

中文:
定理 smul_left
  条件: {X Y : C} {r : (End X)ᵐᵒᵖ} {f : X ⟶ Y}
  结论: r • f = r.unop ≫ f
  证明: rfl
-/
theorem smul_left {X Y : C} {r : (End X)ᵐᵒᵖ} {f : X ⟶ Y} : r • f = r.unop ≫ f :=
  rfl

end MulAction

/--
Instance `group` / 实例 `group`

English:
instance group
  signature: {C : Type u} [Groupoid.{v} C] (X : C)
  body: Groupoid.comp_inv
  inv := Groupoid.inv

中文:
实例 group
  签名: {C : 类型u} [Groupoid.{v} C] (X : C)
  定义体: Groupoid.comp_inv
  inv := Groupoid.inv

Depends on / 依赖: Groupoid, Groupoid.comp_inv, comp_inv
-/
instance group {C : Type u} [Groupoid.{v} C] (X : C) : Group (End X) where
  inv_mul_cancel := Groupoid.comp_inv
  inv := Groupoid.inv

end End

set_option backward.isDefEq.respectTransparency.types false in
/--
theorem `isUnit_iff_isIso` / 定理 `isUnit_iff_isIso`

English:
theorem isUnit_iff_isIso
  given: {C : Type u} [Category.{v} C] {X : C} (f : End X)
  proof: ⟨fun h => { out := ⟨h.unit.inv, ⟨h.unit.inv_val, h.unit.val_inv⟩⟩ }, fun h =>
    ⟨⟨f, inv f, by simp, by simp⟩, rfl⟩⟩

中文:
定理 isUnit_iff_isIso
  条件: {C : 类型u} [Category.{v} C] {X : C} (f : End X)
  证明: ⟨fun h => { out := ⟨h.unit.inv, ⟨h.unit.inv_val, h.unit.val_inv⟩⟩ }, fun h =>
    ⟨⟨f, inv f, by simp, by simp⟩, rfl⟩⟩

Depends on / 依赖: h.unit.inv, h.unit.inv_val, h.unit.val_inv, inv_val, val_inv
-/
theorem isUnit_iff_isIso {C : Type u} [Category.{v} C] {X : C} (f : End X) :
    IsUnit (f : End X) ↔ IsIso f :=
  ⟨fun h => { out := ⟨h.unit.inv, ⟨h.unit.inv_val, h.unit.val_inv⟩⟩ }, fun h =>
    ⟨⟨f, inv f, by simp, by simp⟩, rfl⟩⟩

variable {C : Type u} [Category.{v} C] (X : C)

/--
Definition of `Aut` / `Aut` 的定义

English:
definition Aut
  signature: (X : C)
  body: X ≅ X

中文:
定义 Aut
  签名: (X : C)
  定义体: X ≅ X
-/
def Aut (X : C) := X ≅ X

namespace Aut

@[ext]
/--
lemma `ext` / 引理 `ext`

English:
lemma ext
  given: {X : C} {φ₁ φ₂ : Aut X} (h : φ₁.hom = φ₂.hom)
  statement: φ₁ = φ₂
  proof: Iso.ext h

中文:
引理 ext
  条件: {X : C} {φ₁ φ₂ : Aut X} (h : φ₁.hom = φ₂.hom)
  结论: φ₁ = φ₂
  证明: Iso.ext h

Depends on / 依赖: Iso.ext
-/
lemma ext {X : C} {φ₁ φ₂ : Aut X} (h : φ₁.hom = φ₂.hom) : φ₁ = φ₂ :=
  Iso.ext h

/--
Instance `inhabited` / 实例 `inhabited`

English:
instance inhabited
  signature: : Inhabited (Aut X)
  body: ⟨Iso.refl X⟩

中文:
实例 inhabited
  签名: : Inhabited (Aut X)
  定义体: ⟨Iso.refl X⟩
-/
protected instance inhabited : Inhabited (Aut X) := ⟨Iso.refl X⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Group (Aut X)
  body: Iso.refl X
  inv := Iso.symm
  mul x y := Iso.trans y x
  mul_assoc _ _ _ := (Iso.trans_assoc _ _ _).symm
  one_mul := Iso.trans_refl
  mul_one := Iso.refl_trans
  inv_mul_cancel := Iso.self_symm_id

中文:
实例 :
  签名: Group (Aut X)
  定义体: Iso.refl X
  inv := Iso.symm
  mul x y := Iso.trans y x
  mul_assoc _ _ _ := (Iso.trans_assoc _ _ _).symm
  one_mul := Iso.trans_refl
  mul_one := Iso.refl_trans
  inv_mul_cancel := Iso.self_symm_id

Depends on / 依赖: Iso.refl
-/
instance : Group (Aut X) where
  one := Iso.refl X
  inv := Iso.symm
  mul x y := Iso.trans y x
  mul_assoc _ _ _ := (Iso.trans_assoc _ _ _).symm
  one_mul := Iso.trans_refl
  mul_one := Iso.refl_trans
  inv_mul_cancel := Iso.self_symm_id

/--
theorem `Aut_mul_def` / 定理 `Aut_mul_def`

English:
theorem Aut_mul_def
  given: (f g : Aut X)
  statement: f * g = g.trans f
  proof: rfl

中文:
定理 Aut_mul_def
  条件: (f g : Aut X)
  结论: f * g = g.trans f
  证明: rfl
-/
theorem Aut_mul_def (f g : Aut X) : f * g = g.trans f := rfl

/--
theorem `Aut_inv_def` / 定理 `Aut_inv_def`

English:
theorem Aut_inv_def
  given: (f : Aut X)
  statement: f⁻¹ = f.symm
  proof: rfl

中文:
定理 Aut_inv_def
  条件: (f : Aut X)
  结论: f⁻¹ = f.symm
  证明: rfl
-/
theorem Aut_inv_def (f : Aut X) : f⁻¹ = f.symm := rfl

/--
Definition of `unitsEndEquivAut` / `unitsEndEquivAut` 的定义

English:
definition unitsEndEquivAut
  signature: : (End X)ˣ ≃* Aut X where
  body: ⟨f.1, f.2, f.4, f.3⟩
  invFun f := ⟨f.1, f.2, f.4, f.3⟩
  map_mul' f g := by cases f; cases g; rfl

中文:
定义 unitsEndEquivAut
  签名: : (End X)ˣ ≃* Aut X where
  定义体: ⟨f.1, f.2, f.4, f.3⟩
  invFun f := ⟨f.1, f.2, f.4, f.3⟩
  map_mul' f g := by cases f; cases g; rfl
-/
def unitsEndEquivAut : (End X)ˣ ≃* Aut X where
  toFun f := ⟨f.1, f.2, f.4, f.3⟩
  invFun f := ⟨f.1, f.2, f.4, f.3⟩
  map_mul' f g := by cases f; cases g; rfl

/-- The inclusion of `Aut X` to `End X` as a monoid homomorphism. -/
@[simps!]
/--
Definition of `toEnd` / `toEnd` 的定义

English:
definition toEnd
  signature: (X : C)
  body: (Units.coeHom (End X)).comp (Aut.unitsEndEquivAut X).symm

中文:
定义 toEnd
  签名: (X : C)
  定义体: (Units.coeHom (End X)).comp (Aut.unitsEndEquivAut X).symm

Depends on / 依赖: Aut.unitsEndEquivAut, Units.coeHom, coeHom, unitsEndEquivAut
-/
def toEnd (X : C) : Aut X ->* End X := (Units.coeHom (End X)).comp (Aut.unitsEndEquivAut X).symm

set_option backward.isDefEq.respectTransparency.types false in
/--
Definition of `autMulEquivOfIso` / `autMulEquivOfIso` 的定义

English:
definition autMulEquivOfIso
  signature: {X Y : C} (h : X ≅ Y)
  body: { hom := h.inv ≫ x.hom ≫ h.hom, inv := h.inv ≫ x.inv ≫ h.hom }
  invFun y := { hom := h.hom ≫ y.hom ≫ h.inv, inv := h.hom ≫ y.inv ≫ h.inv }
  left_inv _ := by cat_disch
  right_inv _ := by cat_disch
  map_mul' := by simp [Aut_mul_def]

中文:
定义 autMulEquivOfIso
  签名: {X Y : C} (h : X ≅ Y)
  定义体: { hom := h.inv ≫ x.hom ≫ h.hom, inv := h.inv ≫ x.inv ≫ h.hom }
  invFun y := { hom := h.hom ≫ y.hom ≫ h.inv, inv := h.hom ≫ y.inv ≫ h.inv }
  left_inv _ := by cat_disch
  right_inv _ := by cat_disch
  map_mul' := by simp [Aut_mul_def]

Depends on / 依赖: h.hom, h.inv, x.hom, x.inv
-/
def autMulEquivOfIso {X Y : C} (h : X ≅ Y) : Aut X ≃* Aut Y where
  toFun x := { hom := h.inv ≫ x.hom ≫ h.hom, inv := h.inv ≫ x.inv ≫ h.hom }
  invFun y := { hom := h.hom ≫ y.hom ≫ h.inv, inv := h.hom ≫ y.inv ≫ h.inv }
  left_inv _ := by cat_disch
  right_inv _ := by cat_disch
  map_mul' := by simp [Aut_mul_def]

end Aut

namespace Functor

variable {D : Type u'} [Category.{v'} D] (f : C ⥤ D)

/-- `f.map` as a monoid hom between endomorphism monoids. -/
@[simps]
/--
Definition of `mapEnd` / `mapEnd` 的定义

English:
definition mapEnd
  signature: : End X ->* End (f.obj X) where
  body: f.map
  map_mul' x y := f.map_comp y x
  map_one' := f.map_id X

中文:
定义 mapEnd
  签名: : End X ->* End (f.obj X) where
  定义体: f.map
  map_mul' x y := f.map_comp y x
  map_one' := f.map_id X

Depends on / 依赖: f.map
-/
def mapEnd : End X ->* End (f.obj X) where
  toFun := f.map
  map_mul' x y := f.map_comp y x
  map_one' := f.map_id X

/--
Definition of `mapAut` / `mapAut` 的定义

English:
definition mapAut
  signature: : Aut X ->* Aut (f.obj X) where
  body: f.mapIso
  map_mul' x y := f.mapIso_trans y x
  map_one' := f.mapIso_refl X

中文:
定义 mapAut
  签名: : Aut X ->* Aut (f.obj X) where
  定义体: f.mapIso
  map_mul' x y := f.mapIso_trans y x
  map_one' := f.mapIso_refl X

Depends on / 依赖: f.mapIso, mapIso
-/
def mapAut : Aut X ->* Aut (f.obj X) where
  toFun := f.mapIso
  map_mul' x y := f.mapIso_trans y x
  map_one' := f.mapIso_refl X

namespace FullyFaithful

variable {f}
variable (hf : FullyFaithful f)

/-- `mulEquivEnd` as an isomorphism between endomorphism monoids. -/
@[simps!]
/--
Definition of `mulEquivEnd` / `mulEquivEnd` 的定义

English:
definition mulEquivEnd
  signature: (X : C)
  body: hf.homEquiv
  __ := mapEnd X f

中文:
定义 mulEquivEnd
  签名: (X : C)
  定义体: hf.homEquiv
  __ := mapEnd X f

Depends on / 依赖: hf.homEquiv, homEquiv
-/
noncomputable def mulEquivEnd (X : C) :
    End X ≃* End (f.obj X) where
  toEquiv := hf.homEquiv
  __ := mapEnd X f

/-- `mulEquivAut` as an isomorphism between automorphism groups. -/
@[simps!]
/--
Definition of `autMulEquivOfFullyFaithful` / `autMulEquivOfFullyFaithful` 的定义

English:
definition autMulEquivOfFullyFaithful
  signature: (X : C)
  body: hf.isoEquiv
  __ := mapAut X f

中文:
定义 autMulEquivOfFullyFaithful
  签名: (X : C)
  定义体: hf.isoEquiv
  __ := mapAut X f

Depends on / 依赖: hf.isoEquiv, isoEquiv
-/
noncomputable def autMulEquivOfFullyFaithful (X : C) :
    Aut X ≃* Aut (f.obj X) where
  toEquiv := hf.isoEquiv
  __ := mapAut X f

end FullyFaithful

end Functor

/-- The multiplicative bijection `End X ≃* End (F X)` when `X : InducedCategory C F`. -/
@[simps!]
/--
Definition of `InducedCategory.endEquiv` / `InducedCategory.endEquiv` 的定义

English:
definition InducedCategory.endEquiv
  signature: {D : Type*} {F : D -> C}
  body: InducedCategory.homEquiv
  map_mul' _ _ := rfl

中文:
定义 InducedCategory.endEquiv
  签名: {D : 类型} {F : D -> C}
  定义体: InducedCategory.homEquiv
  map_mul' _ _ := rfl

Depends on / 依赖: InducedCategory, InducedCategory.homEquiv, homEquiv
-/
def InducedCategory.endEquiv {D : Type*} {F : D -> C}
    {X : InducedCategory C F} : End X ≃* End (F X) where
  toEquiv := InducedCategory.homEquiv
  map_mul' _ _ := rfl

end CategoryTheory
