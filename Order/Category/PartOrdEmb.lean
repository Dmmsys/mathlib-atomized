/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou, Johan Commelin
-/
module

public import Mathlib.Order.Category.PartOrd
public import Mathlib.CategoryTheory.Limits.Filtered
public import Mathlib.CategoryTheory.Limits.Preserves.Filtered
public import Mathlib.CategoryTheory.Limits.Types.Filtered

/-!
# Category of partial orders, with order embeddings as morphisms

This defines `PartOrdEmb`, the category of partial orders with order embeddings
as morphisms. We also show that `PartOrdEmb` has filtered colimits.

-/

@[expose] public section

open CategoryTheory Limits

universe u

/--
Definition of `PartOrdEmb` / `PartOrdEmb` 的定义

English:
structure PartOrdEmb
  parameters: where
  axioms and operations (3):
    - of : :
    - (carrier : Type*)
    - [str : PartialOrder carrier]

中文:
结构 PartOrdEmb
  参数: where
  公理与运算 (3 个):
    - of : :
    - (carrier : 类型)
    - [str : PartialOrder carrier]
-/
structure PartOrdEmb where
  /-- Construct a bundled `PartOrdEmb` from the underlying type and typeclass. -/
  of ::
  /-- The underlying partially ordered type. -/
  (carrier : Type*)
  [str : PartialOrder carrier]

attribute [instance] PartOrdEmb.str

initialize_simps_projections PartOrdEmb (carrier -> coe, -str)

namespace PartOrdEmb

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: CoeSort PartOrdEmb (Type _)
  body: ⟨PartOrdEmb.carrier⟩

中文:
实例 :
  签名: CoeSort PartOrdEmb (Type _)
  定义体: ⟨PartOrdEmb.carrier⟩

Depends on / 依赖: PartOrdEmb, PartOrdEmb.carrier, carrier
-/
instance : CoeSort PartOrdEmb (Type _) :=
  ⟨PartOrdEmb.carrier⟩

attribute [coe] PartOrdEmb.carrier

/-- The type of morphisms in `PartOrdEmb R`. -/
@[ext]
/--
Definition of `Hom` / `Hom` 的定义

English:
structure Hom
  parameters: (X Y : PartOrdEmb.{u})
  axioms and operations (2):
    - private(mk) : :
    - hom' : X ↪o Y

中文:
结构 Hom
  参数: (X Y : PartOrdEmb.{u})
  公理与运算 (2 个):
    - private(mk) : :
    - hom' : X ↪o Y
-/
structure Hom (X Y : PartOrdEmb.{u}) where
  private mk ::
  /-- The underlying `OrderEmbedding`. -/
  hom' : X ↪o Y

set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Category PartOrdEmb.{u}
  body: Hom X Y
  id _ := ⟨RelEmbedding.refl _⟩
  comp f g := ⟨f.hom'.trans g.hom'⟩

中文:
实例 :
  签名: Category PartOrdEmb.{u}
  定义体: Hom X Y
  id _ := ⟨RelEmbedding.refl _⟩
  comp f g := ⟨f.hom'.trans g.hom'⟩
-/
instance : Category PartOrdEmb.{u} where
  Hom X Y := Hom X Y
  id _ := ⟨RelEmbedding.refl _⟩
  comp f g := ⟨f.hom'.trans g.hom'⟩

set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: ConcreteCategory PartOrdEmb (· ↪o ·)
  body: Hom.hom'
  ofHom := Hom.mk

中文:
实例 :
  签名: ConcreteCategory PartOrdEmb (· ↪o ·)
  定义体: Hom.hom'
  ofHom := Hom.mk

Depends on / 依赖: Hom.hom
-/
instance : ConcreteCategory PartOrdEmb (· ↪o ·) where
  hom := Hom.hom'
  ofHom := Hom.mk

/--
Definition of `Hom.hom` / `Hom.hom` 的定义

English:
abbreviation Hom.hom
  signature: {X Y : PartOrdEmb.{u}} (f : Hom X Y)
  body: ConcreteCategory.hom (C := PartOrdEmb) f

中文:
缩写 Hom.hom
  签名: {X Y : PartOrdEmb.{u}} (f : Hom X Y)
  定义体: ConcreteCategory.hom (C := PartOrdEmb) f
-/
abbrev Hom.hom {X Y : PartOrdEmb.{u}} (f : Hom X Y) :=
  ConcreteCategory.hom (C := PartOrdEmb) f

/--
Definition of `ofHom` / `ofHom` 的定义

English:
abbreviation ofHom
  signature: {X Y : Type u} [PartialOrder X] [PartialOrder Y] (f : X ↪o Y)
  body: ConcreteCategory.ofHom (C := PartOrdEmb) f

中文:
缩写 ofHom
  签名: {X Y : 类型u} [PartialOrder X] [PartialOrder Y] (f : X ↪o Y)
  定义体: ConcreteCategory.ofHom (C := PartOrdEmb) f

Depends on / 依赖: ConcreteCategory, ConcreteCategory.ofHom, PartOrdEmb
-/
abbrev ofHom {X Y : Type u} [PartialOrder X] [PartialOrder Y] (f : X ↪o Y) : of X ⟶ of Y :=
  ConcreteCategory.ofHom (C := PartOrdEmb) f

variable {R} in
/--
Definition of `Hom.Simps.hom` / `Hom.Simps.hom` 的定义

English:
definition Hom.Simps.hom
  signature: (X Y : PartOrdEmb.{u}) (f : Hom X Y)
  body: f.hom

initialize_simps_projections Hom (hom' -> hom)

中文:
定义 Hom.Simps.hom
  签名: (X Y : PartOrdEmb.{u}) (f : Hom X Y)
  定义体: f.hom

initialize_simps_projections Hom (hom' -> hom)
-/
def Hom.Simps.hom (X Y : PartOrdEmb.{u}) (f : Hom X Y) :=
  f.hom

initialize_simps_projections Hom (hom' -> hom)

/-!
The results below duplicate the `ConcreteCategory` simp lemmas, but we can keep them for `dsimp`.
-/

@[simp]
/--
lemma `coe_id` / 引理 `coe_id`

English:
lemma coe_id
  given: {X : PartOrdEmb}
  statement: (𝟙 X : X -> X) = id
  proof: rfl

@[simp]

中文:
引理 coe_id
  条件: {X : PartOrdEmb}
  结论: (𝟙 X : X -> X) = id
  证明: rfl

@[simp]
-/
lemma coe_id {X : PartOrdEmb} : (𝟙 X : X -> X) = id := rfl

@[simp]
/--
lemma `coe_comp` / 引理 `coe_comp`

English:
lemma coe_comp
  given: {X Y Z : PartOrdEmb} {f : X ⟶ Y} {g : Y ⟶ Z}
  statement: (f ≫ g : X -> Z) = g ∘ f
  proof: rfl

@[simp]

中文:
引理 coe_comp
  条件: {X Y Z : PartOrdEmb} {f : X ⟶ Y} {g : Y ⟶ Z}
  结论: (f ≫ g : X -> Z) = g ∘ f
  证明: rfl

@[simp]
-/
lemma coe_comp {X Y Z : PartOrdEmb} {f : X ⟶ Y} {g : Y ⟶ Z} : (f ≫ g : X -> Z) = g ∘ f := rfl

@[simp]
/--
lemma `forget_map` / 引理 `forget_map`

English:
lemma forget_map
  given: {X Y : PartOrdEmb} (f : X ⟶ Y)
  proof: rfl

@[ext]

中文:
引理 forget_map
  条件: {X Y : PartOrdEmb} (f : X ⟶ Y)
  证明: rfl

@[ext]
-/
lemma forget_map {X Y : PartOrdEmb} (f : X ⟶ Y) :
    (forget PartOrdEmb).map f = (f : _ -> _) := rfl

@[ext]
/--
lemma `ext` / 引理 `ext`

English:
lemma ext
  given: {X Y : PartOrdEmb} {f g : X ⟶ Y} (w : forall x : X, f x = g x)
  statement: f = g
  proof: ConcreteCategory.hom_ext _ _ w

中文:
引理 ext
  条件: {X Y : PartOrdEmb} {f g : X ⟶ Y} (w : 对任意 x : X, f x = g x)
  结论: f = g
  证明: ConcreteCategory.hom_ext _ _ w

Depends on / 依赖: ConcreteCategory, ConcreteCategory.hom_ext, hom_ext
-/
lemma ext {X Y : PartOrdEmb} {f g : X ⟶ Y} (w : forall x : X, f x = g x) : f = g :=
  ConcreteCategory.hom_ext _ _ w

-- This is not `simp` to avoid rewriting in types of terms.
/--
theorem `coe_of` / 定理 `coe_of`

English:
theorem coe_of
  given: (X : Type u) [PartialOrder X]
  statement: (PartOrdEmb.of X : Type u) = X
  proof: rfl

中文:
定理 coe_of
  条件: (X : 类型u) [PartialOrder X]
  结论: (PartOrdEmb.of X : 类型u) = X
  证明: rfl
-/
theorem coe_of (X : Type u) [PartialOrder X] : (PartOrdEmb.of X : Type u) = X := rfl

/--
lemma `hom_id` / 引理 `hom_id`

English:
lemma hom_id
  given: {X : PartOrdEmb}
  statement: (𝟙 X : X ⟶ X).hom = RelEmbedding.refl _
  proof: rfl

中文:
引理 hom_id
  条件: {X : PartOrdEmb}
  结论: (𝟙 X : X ⟶ X).hom = RelEmbedding.refl _
  证明: rfl
-/
lemma hom_id {X : PartOrdEmb} : (𝟙 X : X ⟶ X).hom = RelEmbedding.refl _ := rfl

/--
lemma `id_apply` / 引理 `id_apply`

English:
lemma id_apply
  given: (X : PartOrdEmb) (x : X)
  proof: by simp

@[simp]

中文:
引理 id_apply
  条件: (X : PartOrdEmb) (x : X)
  证明: by simp

@[simp]
-/
lemma id_apply (X : PartOrdEmb) (x : X) :
    (𝟙 X : X ⟶ X) x = x := by simp

@[simp]
/--
lemma `hom_comp` / 引理 `hom_comp`

English:
lemma hom_comp
  given: {X Y Z : PartOrdEmb} (f : X ⟶ Y) (g : Y ⟶ Z)
  proof: rfl

中文:
引理 hom_comp
  条件: {X Y Z : PartOrdEmb} (f : X ⟶ Y) (g : Y ⟶ Z)
  证明: rfl
-/
lemma hom_comp {X Y Z : PartOrdEmb} (f : X ⟶ Y) (g : Y ⟶ Z) :
    (f ≫ g).hom = f.hom.trans g.hom := rfl

/--
lemma `comp_apply` / 引理 `comp_apply`

English:
lemma comp_apply
  given: {X Y Z : PartOrdEmb} (f : X ⟶ Y) (g : Y ⟶ Z) (x : X)
  proof: by simp

中文:
引理 comp_apply
  条件: {X Y Z : PartOrdEmb} (f : X ⟶ Y) (g : Y ⟶ Z) (x : X)
  证明: by simp
-/
lemma comp_apply {X Y Z : PartOrdEmb} (f : X ⟶ Y) (g : Y ⟶ Z) (x : X) :
    (f ≫ g) x = g (f x) := by simp

/--
lemma `Hom.injective` / 引理 `Hom.injective`

English:
lemma Hom.injective
  given: {X Y : PartOrdEmb.{u}} (f : X ⟶ Y)
  statement: Function.Injective f
  proof: f.hom'.injective

中文:
引理 Hom.injective
  条件: {X Y : PartOrdEmb.{u}} (f : X ⟶ Y)
  结论: Function.Injective f
  证明: f.hom'.injective
-/
lemma Hom.injective {X Y : PartOrdEmb.{u}} (f : X ⟶ Y) : Function.Injective f :=
  f.hom'.injective

/--
lemma `Hom.le_iff_le` / 引理 `Hom.le_iff_le`

English:
lemma Hom.le_iff_le
  given: {X Y : PartOrdEmb.{u}} (f : X ⟶ Y) (x₁ x₂ : X)
  proof: f.hom'.le_iff_le

@[ext]

中文:
引理 Hom.le_iff_le
  条件: {X Y : PartOrdEmb.{u}} (f : X ⟶ Y) (x₁ x₂ : X)
  证明: f.hom'.le_iff_le

@[ext]
-/
lemma Hom.le_iff_le {X Y : PartOrdEmb.{u}} (f : X ⟶ Y) (x₁ x₂ : X) :
    f x₁ <= f x₂ ↔ x₁ <= x₂ :=
  f.hom'.le_iff_le

@[ext]
/--
lemma `hom_ext` / 引理 `hom_ext`

English:
lemma hom_ext
  given: {X Y : PartOrdEmb} {f g : X ⟶ Y} (hf : f.hom = g.hom)
  statement: f = g
  proof: Hom.ext hf

@[simp]

中文:
引理 hom_ext
  条件: {X Y : PartOrdEmb} {f g : X ⟶ Y} (hf : f.hom = g.hom)
  结论: f = g
  证明: Hom.ext hf

@[simp]

Depends on / 依赖: Hom.ext
-/
lemma hom_ext {X Y : PartOrdEmb} {f g : X ⟶ Y} (hf : f.hom = g.hom) : f = g :=
  Hom.ext hf

@[simp]
/--
lemma `hom_ofHom` / 引理 `hom_ofHom`

English:
lemma hom_ofHom
  given: {X Y : Type u} [PartialOrder X] [PartialOrder Y] (f : X ↪o Y)
  proof: rfl

@[simp]

中文:
引理 hom_ofHom
  条件: {X Y : 类型u} [PartialOrder X] [PartialOrder Y] (f : X ↪o Y)
  证明: rfl

@[simp]
-/
lemma hom_ofHom {X Y : Type u} [PartialOrder X] [PartialOrder Y] (f : X ↪o Y) :
    (ofHom f).hom = f :=
  rfl

@[simp]
/--
lemma `ofHom_hom` / 引理 `ofHom_hom`

English:
lemma ofHom_hom
  given: {X Y : PartOrdEmb} (f : X ⟶ Y)
  statement: ofHom (Hom.hom f) = f
  proof: rfl

@[simp]

中文:
引理 ofHom_hom
  条件: {X Y : PartOrdEmb} (f : X ⟶ Y)
  结论: ofHom (Hom.hom f) = f
  证明: rfl

@[simp]
-/
lemma ofHom_hom {X Y : PartOrdEmb} (f : X ⟶ Y) : ofHom (Hom.hom f) = f := rfl

@[simp]
/--
lemma `ofHom_id` / 引理 `ofHom_id`

English:
lemma ofHom_id
  given: {X : Type u} [PartialOrder X]
  statement: ofHom (RelEmbedding.refl _) = 𝟙 (of X)
  proof: rfl

@[simp]

中文:
引理 ofHom_id
  条件: {X : 类型u} [PartialOrder X]
  结论: ofHom (RelEmbedding.refl _) = 𝟙 (of X)
  证明: rfl

@[simp]
-/
lemma ofHom_id {X : Type u} [PartialOrder X] : ofHom (RelEmbedding.refl _) = 𝟙 (of X) := rfl

@[simp]
/--
lemma `ofHom_comp` / 引理 `ofHom_comp`

English:
lemma ofHom_comp
  statement: {X Y Z : Type u} [PartialOrder X] [PartialOrder Y] [PartialOrder Z]
  proof: rfl

中文:
引理 ofHom_comp
  结论: {X Y Z : 类型u} [PartialOrder X] [PartialOrder Y] [PartialOrder Z]
  证明: rfl
-/
lemma ofHom_comp {X Y Z : Type u} [PartialOrder X] [PartialOrder Y] [PartialOrder Z]
    (f : X ↪o Y) (g : Y ↪o Z) :
    ofHom (f.trans g) = ofHom f ≫ ofHom g :=
  rfl

/--
lemma `ofHom_apply` / 引理 `ofHom_apply`

English:
lemma ofHom_apply
  given: {X Y : Type u} [PartialOrder X] [PartialOrder Y] (f : X ↪o Y) (x : X)
  proof: rfl

中文:
引理 ofHom_apply
  条件: {X Y : 类型u} [PartialOrder X] [PartialOrder Y] (f : X ↪o Y) (x : X)
  证明: rfl
-/
lemma ofHom_apply {X Y : Type u} [PartialOrder X] [PartialOrder Y] (f : X ↪o Y) (x : X) :
    (ofHom f) x = f x := rfl

/--
lemma `inv_hom_apply` / 引理 `inv_hom_apply`

English:
lemma inv_hom_apply
  given: {X Y : PartOrdEmb} (e : X ≅ Y) (x : X)
  statement: e.inv (e.hom x) = x
  proof: by
  simp

中文:
引理 inv_hom_apply
  条件: {X Y : PartOrdEmb} (e : X ≅ Y) (x : X)
  结论: e.inv (e.hom x) = x
  证明: by
  simp
-/
lemma inv_hom_apply {X Y : PartOrdEmb} (e : X ≅ Y) (x : X) : e.inv (e.hom x) = x := by
  simp

/--
lemma `hom_inv_apply` / 引理 `hom_inv_apply`

English:
lemma hom_inv_apply
  given: {X Y : PartOrdEmb} (e : X ≅ Y) (s : Y)
  statement: e.hom (e.inv s) = s
  proof: by
  simp

中文:
引理 hom_inv_apply
  条件: {X Y : PartOrdEmb} (e : X ≅ Y) (s : Y)
  结论: e.hom (e.inv s) = s
  证明: by
  simp
-/
lemma hom_inv_apply {X Y : PartOrdEmb} (e : X ≅ Y) (s : Y) : e.hom (e.inv s) = s := by
  simp

/--
Instance `hasForgetToPartOrd` / 实例 `hasForgetToPartOrd`

English:
instance hasForgetToPartOrd
  signature: : HasForget₂ PartOrdEmb PartOrd where
  body: .of X
  forget₂.map f := PartOrd.ofHom f.hom

中文:
实例 hasForgetToPartOrd
  签名: : HasForget₂ PartOrdEmb PartOrd where
  定义体: .of X
  forget₂.map f := PartOrd.ofHom f.hom
-/
instance hasForgetToPartOrd : HasForget₂ PartOrdEmb PartOrd where
  forget₂.obj X := .of X
  forget₂.map f := PartOrd.ofHom f.hom

/-- Constructs an equivalence between partial orders from an order isomorphism between them. -/
@[simps]
/--
Definition of `Iso.mk` / `Iso.mk` 的定义

English:
definition Iso.mk
  signature: {α β : PartOrdEmb.{u}} (e : α ≃o β)
  body: ofHom e
  inv := ofHom e.symm

中文:
定义 Iso.mk
  签名: {α β : PartOrdEmb.{u}} (e : α ≃o β)
  定义体: ofHom e
  inv := ofHom e.symm
-/
def Iso.mk {α β : PartOrdEmb.{u}} (e : α ≃o β) : α ≅ β where
  hom := ofHom e
  inv := ofHom e.symm

/-- The order isomorphism corresponding to an isomorphism in `PartOrdEmb`. -/
@[simps]
/--
Definition of `orderIsoOfIso` / `orderIsoOfIso` 的定义

English:
definition orderIsoOfIso
  signature: {α β : PartOrdEmb.{u}} (e : α ≅ β)
  body: e.hom
  invFun := e.inv
  left_inv := ConcreteCategory.congr_hom e.hom_inv_id
  right_inv := ConcreteCategory.congr_hom e.inv_hom_id
  map_rel_iff' := Hom.le_iff_le _ _ _

中文:
定义 orderIsoOfIso
  签名: {α β : PartOrdEmb.{u}} (e : α ≅ β)
  定义体: e.hom
  invFun := e.inv
  left_inv := ConcreteCategory.congr_hom e.hom_inv_id
  right_inv := ConcreteCategory.congr_hom e.inv_hom_id
  map_rel_iff' := Hom.le_iff_le _ _ _

Depends on / 依赖: e.hom
-/
def orderIsoOfIso {α β : PartOrdEmb.{u}} (e : α ≅ β) :
    α ≃o β where
  toFun := e.hom
  invFun := e.inv
  left_inv := ConcreteCategory.congr_hom e.hom_inv_id
  right_inv := ConcreteCategory.congr_hom e.inv_hom_id
  map_rel_iff' := Hom.le_iff_le _ _ _

/-- Isomorphisms in `PartOrdEmb` correspond to order isomorphisms. -/
@[simps]
/--
Definition of `orderIsoEquivIso` / `orderIsoEquivIso` 的定义

English:
definition orderIsoEquivIso
  signature: {α β : PartOrdEmb.{u}}
  body: orderIsoOfIso
  invFun := Iso.mk

中文:
定义 orderIsoEquivIso
  签名: {α β : PartOrdEmb.{u}}
  定义体: orderIsoOfIso
  invFun := Iso.mk

Depends on / 依赖: orderIsoOfIso
-/
def orderIsoEquivIso {α β : PartOrdEmb.{u}} :
    (α ≅ β) ≃ (α ≃o β) where
  toFun := orderIsoOfIso
  invFun := Iso.mk

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: (forget PartOrdEmb.{u}).ReflectsIsomorphisms
  body: by
    rw [CategoryTheory.isIso_iff_bijective] at hf
    let e : α ≃o β :=
      { toEquiv := Equiv.ofBijective _ hf
        map_rel_iff' := by simp }
    exact (Iso.mk e).isIso_hom

中文:
实例 :
  签名: (forget PartOrdEmb.{u}).ReflectsIsomorphisms
  定义体: by
    rw [CategoryTheory.isIso_iff_bijective] at hf
    let e : α ≃o β :=
      { toEquiv := Equiv.ofBijective _ hf
        map_rel_iff' := by simp }
    exact (Iso.mk e).isIso_hom

Depends on / 依赖: CategoryTheory, CategoryTheory.isIso_iff_bijective, Equiv.ofBijective, Iso.mk, isIso_hom, isIso_iff_bijective, map_rel_iff, ofBijective, toEquiv
-/
instance : (forget PartOrdEmb.{u}).ReflectsIsomorphisms where
  reflects {α β} f hf := by
    rw [CategoryTheory.isIso_iff_bijective] at hf
    let e : α ≃o β :=
      { toEquiv := Equiv.ofBijective _ hf
        map_rel_iff' := by simp }
    exact (Iso.mk e).isIso_hom

/-- `OrderDual` as a functor. -/
@[simps map]
/--
Definition of `dual` / `dual` 的定义

English:
definition dual
  signature: : PartOrdEmb ⥤ PartOrdEmb where
  body: of Xᵒᵈ
  map f := ofHom f.hom.dual

中文:
定义 dual
  签名: : PartOrdEmb ⥤ PartOrdEmb where
  定义体: of Xᵒᵈ
  map f := ofHom f.hom.dual
-/
def dual : PartOrdEmb ⥤ PartOrdEmb where
  obj X := of Xᵒᵈ
  map f := ofHom f.hom.dual

/-- The equivalence between `PartOrdEmb` and itself induced by `OrderDual` both ways. -/
@[simps functor inverse]
/--
Definition of `dualEquiv` / `dualEquiv` 的定义

English:
definition dualEquiv
  signature: : PartOrdEmb ≌ PartOrdEmb where
  body: dual
  inverse := dual
unitIso := NatIso.ofComponents fun X => Iso.mk OrderIso.dualDual X
counitIso := NatIso.ofComponents fun X => Iso.mk OrderIso.dualDual X

中文:
定义 dualEquiv
  签名: : PartOrdEmb ≌ PartOrdEmb where
  定义体: dual
  inverse := dual
unitIso := NatIso.ofComponents fun X => Iso.mk OrderIso.dualDual X
counitIso := NatIso.ofComponents fun X => Iso.mk OrderIso.dualDual X
-/
def dualEquiv : PartOrdEmb ≌ PartOrdEmb where
  functor := dual
  inverse := dual
unitIso := NatIso.ofComponents fun X => Iso.mk OrderIso.dualDual X
counitIso := NatIso.ofComponents fun X => Iso.mk OrderIso.dualDual X

end PartOrdEmb

/--
theorem `partOrdEmb_dual_comp_forget_to_pardOrd` / 定理 `partOrdEmb_dual_comp_forget_to_pardOrd`

English:
theorem partOrdEmb_dual_comp_forget_to_pardOrd
  proof: rfl

中文:
定理 partOrdEmb_dual_comp_forget_to_pardOrd
  证明: rfl
-/
theorem partOrdEmb_dual_comp_forget_to_pardOrd :
    PartOrdEmb.dual ⋙ forget₂ PartOrdEmb PartOrd =
      forget₂ PartOrdEmb PartOrd ⋙ PartOrd.dual :=
  rfl

namespace PartOrdEmb

namespace Limits

variable {J : Type u} [SmallCategory J] [IsFiltered J] {F : J ⥤ PartOrdEmb.{u}}
  {c : Cocone (F ⋙ forget _)} (hc : IsColimit c)

/-- Given a functor `F : J ⥤ PartOrdEmb` and a colimit cocone `c` for
`F ⋙ forget _`, this is the type `c.pt` on which we define a partial order
which makes it the colimit of `F`. -/
@[nolint unusedArguments]
/--
Definition of `CoconePt` / `CoconePt` 的定义

English:
definition CoconePt
  signature: (_ : IsColimit c)
  body: c.pt

中文:
定义 CoconePt
  签名: (_ : IsColimit c)
  定义体: c.pt

Depends on / 依赖: c.pt
-/
def CoconePt (_ : IsColimit c) : Type u := c.pt

open IsFiltered

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: PartialOrder (CoconePt hc)
  body: exists (j : J) (x' y' : F.obj j) (hx : c.ι.app j x' = x)
      (hy : c.ι.app j y' = y), x' <= y'
  le_refl x := by
    obtain ⟨j, x', hx⟩ := Types.jointly_surjective_of_isColimit hc x
    exact ⟨j, x', x', hx, hx, le_rfl⟩
  le_trans := by
    rintro x y z ⟨j, x₁, y₁, hx₁, hy₁, hxy⟩ ⟨k, y₂, z₁, hy₂, 

中文:
实例 :
  签名: PartialOrder (CoconePt hc)
  定义体: exists (j : J) (x' y' : F.obj j) (hx : c.ι.app j x' = x)
      (hy : c.ι.app j y' = y), x' <= y'
  le_refl x := by
    obtain ⟨j, x', hx⟩ := Types.jointly_surjective_of_isColimit hc x
    exact ⟨j, x', x', hx, hx, le_rfl⟩
  le_trans := by
    rintro x y z ⟨j, x₁, y₁, hx₁, hy₁, hxy⟩ ⟨k, y₂, z₁, hy₂, 

Depends on / 依赖: F.obj
-/
instance : PartialOrder (CoconePt hc) where
  le x y := exists (j : J) (x' y' : F.obj j) (hx : c.ι.app j x' = x)
      (hy : c.ι.app j y' = y), x' <= y'
  le_refl x := by
    obtain ⟨j, x', hx⟩ := Types.jointly_surjective_of_isColimit hc x
    exact ⟨j, x', x', hx, hx, le_rfl⟩
  le_trans := by
    rintro x y z ⟨j, x₁, y₁, hx₁, hy₁, hxy⟩ ⟨k, y₂, z₁, hy₂, hz₁, hyz⟩
    obtain ⟨l, a, b, h⟩ :=
      (Types.FilteredColimit.isColimit_eq_iff _ hc (xi := y₁) (xj := y₂)).1
        (hy₁.trans hy₂.symm)
    exact ⟨l, F.map a x₁, F.map b z₁,
      (ConcreteCategory.congr_hom (c.w a) x₁).trans hx₁,
      (ConcreteCategory.congr_hom (c.w b) z₁).trans hz₁,
      ((F.map a).hom.monotone hxy).trans
        (le_of_eq_of_le h ((F.map b).hom.monotone hyz))⟩
  le_antisymm := by
    rintro x y ⟨j, x₁, y₁, hx₁, hy₁, h₁⟩ ⟨k, y₂, x₂, hy₂, hx₂, h₂⟩
    obtain ⟨l, a, b, x₃, y₃, h₃, h₄, h₅, h₆⟩ :
        exists (l : J) (a : j ⟶ l) (b : k ⟶ l) (x₃ y₃ : _),
        x₃ = F.map a x₁ ∧ x₃ = F.map b x₂ ∧ y₃ = F.map a y₁ ∧ y₃ = F.map b y₂ := by
      obtain ⟨l₁, a, b, h₃⟩ :=
        (Types.FilteredColimit.isColimit_eq_iff _ hc (xi := x₁) (xj := x₂)).1
          (hx₁.trans hx₂.symm)
      obtain ⟨l₂, a', b', h₄⟩ :=
        (Types.FilteredColimit.isColimit_eq_iff _ hc (xi := y₁) (xj := y₂)).1
          (hy₁.trans hy₂.symm)
      obtain ⟨l, d, d', h₅, h₆⟩ := IsFiltered.bowtie a a' b b'
      exact ⟨l, a ≫ d, b ≫ d, F.map (a ≫ d) x₁, F.map (a' ≫ d') y₁, rfl,
        by simpa, by rw [h₅], by simpa [h₆]⟩
    have h₇ : x₃ = y₃ :=
      le_antisymm
        (by simpa only [h₃, h₅] using (F.map a).hom.monotone h₁)
        (by simpa only [h₄, h₆] using (F.map b).hom.monotone h₂)
    exact hx₁.symm.trans ((ConcreteCategory.congr_hom (c.w a) x₁).symm.trans
      ((congr_arg (c.ι.app l) (h₃.symm.trans (h₇.trans h₅))).trans
        ((ConcreteCategory.congr_hom (c.w a) y₁).trans hy₁)))

/-- The colimit cocone for a functor `F : J ⥤ PartOrdEmb` from a filtered
category that is constructed from a colimit cocone for `F ⋙ forget _`. -/
@[simps]
/--
Definition of `cocone` / `cocone` 的定义

English:
definition cocone
  signature: : Cocone F where
  body: .of (CoconePt hc)
  ι.app j := ofHom
    { toFun := c.ι.app j
      inj' x y h := by
        obtain ⟨k, a, ha⟩ := (Types.FilteredColimit.isColimit_eq_iff' hc x y).1 h
        exact (F.map a).injective ha
      map_rel_iff' {x y} := by
        refine ⟨?_, fun h => ⟨j, x, y, rfl, rfl, h⟩⟩
        rint

中文:
定义 cocone
  签名: : Cocone F where
  定义体: .of (CoconePt hc)
  ι.app j := ofHom
    { toFun := c.ι.app j
      inj' x y h := by
        obtain ⟨k, a, ha⟩ := (Types.FilteredColimit.isColimit_eq_iff' hc x y).1 h
        exact (F.map a).injective ha
      map_rel_iff' {x y} := by
        refine ⟨?_, fun h => ⟨j, x, y, rfl, rfl, h⟩⟩
        rint

Depends on / 依赖: CoconePt
-/
def cocone : Cocone F where
  pt := .of (CoconePt hc)
  ι.app j := ofHom
    { toFun := c.ι.app j
      inj' x y h := by
        obtain ⟨k, a, ha⟩ := (Types.FilteredColimit.isColimit_eq_iff' hc x y).1 h
        exact (F.map a).injective ha
      map_rel_iff' {x y} := by
        refine ⟨?_, fun h => ⟨j, x, y, rfl, rfl, h⟩⟩
        rintro ⟨k, x', y', hx, hy, h⟩
        obtain ⟨l₁, a₁, b₁, hl₁⟩ := (Types.FilteredColimit.isColimit_eq_iff _ hc).1 hx
        obtain ⟨l₂, a₂, b₂, hl₂⟩ := (Types.FilteredColimit.isColimit_eq_iff _ hc).1 hy
        dsimp at hx hy hl₁ hl₂
        obtain ⟨m, d, d', h₁, h₂⟩ := bowtie a₁ a₂ b₁ b₂
        rw [← (F.map (a₁ ≫ d)).le_iff_le] at h
        rw [← (F.map (b₁ ≫ d)).le_iff_le]
        conv_rhs => rw [h₂]
        conv_rhs at h => rw [h₁]
        simpa [← hl₁, ← hl₂] using h }
  ι.naturality _ _ f := by ext x; exact ConcreteCategory.congr_hom (c.w f) x

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/--
Definition of `CoconePt.desc` / `CoconePt.desc` 的定义

English:
definition CoconePt.desc
  signature: (s : Cocone F)
  body: hc.desc ((forget _).mapCocone s)
  inj' x y h := by
    obtain ⟨j, x', y', rfl, rfl⟩ :=
      Types.FilteredColimit.jointly_surjective_of_isColimit₂ hc x y
    obtain rfl := (s.ι.app j).injective
      (((ConcreteCategory.congr_hom (hc.fac ((forget _).mapCocone s) j) x').symm.trans h).trans
        

中文:
定义 CoconePt.desc
  签名: (s : Cocone F)
  定义体: hc.desc ((forget _).mapCocone s)
  inj' x y h := by
    obtain ⟨j, x', y', rfl, rfl⟩ :=
      Types.FilteredColimit.jointly_surjective_of_isColimit₂ hc x y
    obtain rfl := (s.ι.app j).injective
      (((ConcreteCategory.congr_hom (hc.fac ((forget _).mapCocone s) j) x').symm.trans h).trans
        

Depends on / 依赖: forget, hc.desc, mapCocone
-/
def CoconePt.desc (s : Cocone F) : CoconePt hc ↪o s.pt where
  toFun := hc.desc ((forget _).mapCocone s)
  inj' x y h := by
    obtain ⟨j, x', y', rfl, rfl⟩ :=
      Types.FilteredColimit.jointly_surjective_of_isColimit₂ hc x y
    obtain rfl := (s.ι.app j).injective
      (((ConcreteCategory.congr_hom (hc.fac ((forget _).mapCocone s) j) x').symm.trans h).trans
        (ConcreteCategory.congr_hom (hc.fac ((forget _).mapCocone s) j) y'))
    rfl
  map_rel_iff' {x y} := by
    obtain ⟨j, x', y', rfl, rfl⟩ :=
      Types.FilteredColimit.jointly_surjective_of_isColimit₂ hc x y
    have hx := ConcreteCategory.congr_hom (hc.fac ((forget _).mapCocone s) j) x'
    have hy := ConcreteCategory.congr_hom (hc.fac ((forget _).mapCocone s) j) y'
    simp only [Functor.mapCocone_pt, Functor.comp_obj, Functor.const_obj_obj,
      CategoryTheory.comp_apply, Functor.mapCocone_ι_app, ConcreteCategory.hom_ofHom,
      TypeCat.Fun.coe_mk, Function.Embedding.coeFn_mk] at hx hy ⊢
    rw [hx]; rw [hy]; rw [OrderEmbedding.le_iff_le]
    refine ⟨fun h => ⟨j, _, _, rfl, rfl, h⟩, fun ⟨k, x, y, hx', hy', h⟩ => ?_⟩
    obtain ⟨l, f, g, hl⟩ := (Types.FilteredColimit.isColimit_eq_iff _ hc).1 hx'
    obtain ⟨l', f', g', hl'⟩ := (Types.FilteredColimit.isColimit_eq_iff _ hc).1 hy'
    obtain ⟨m, a, b, h₁, h₂⟩ := bowtie f f' g g'
    dsimp at hl hl'
    rw [← (F.map (f ≫ a)).le_iff_le] at h
    rw [← (F.map (g ≫ a)).le_iff_le]
    exact le_of_eq_of_le (by simp [hl]) (le_of_le_of_eq h (by simp [h₁, h₂, hl']))

@[simp]
/--
lemma `CoconePt.fac_apply` / 引理 `CoconePt.fac_apply`

English:
lemma CoconePt.fac_apply
  given: (s : Cocone F) (j : J) (x : F.obj j)
  proof: ConcreteCategory.congr_hom (hc.fac ((forget _).mapCocone s) j) x

中文:
引理 CoconePt.fac_apply
  条件: (s : Cocone F) (j : J) (x : F.obj j)
  证明: ConcreteCategory.congr_hom (hc.fac ((forget _).mapCocone s) j) x

Depends on / 依赖: ConcreteCategory, ConcreteCategory.congr_hom, congr_hom, forget, hc.fac, mapCocone
-/
lemma CoconePt.fac_apply (s : Cocone F) (j : J) (x : F.obj j) :
    dsimp% CoconePt.desc hc s (c.ι.app j x) = s.ι.app j x :=
  ConcreteCategory.congr_hom (hc.fac ((forget _).mapCocone s) j) x

/--
Definition of `isColimitCocone` / `isColimitCocone` 的定义

English:
definition isColimitCocone
  signature: : IsColimit (cocone hc) where
  body: ofHom (CoconePt.desc hc s)
  fac s j := by
    ext x
    exact ConcreteCategory.congr_hom (hc.fac ((forget _).mapCocone s) j) x
  uniq s m hm := by
    ext x
    obtain ⟨j, x, rfl⟩ := Types.jointly_surjective_of_isColimit hc x
    exact ((ConcreteCategory.congr_hom (hm j)) x).trans (CoconePt.fac_app

中文:
定义 isColimitCocone
  签名: : IsColimit (cocone hc) where
  定义体: ofHom (CoconePt.desc hc s)
  fac s j := by
    ext x
    exact ConcreteCategory.congr_hom (hc.fac ((forget _).mapCocone s) j) x
  uniq s m hm := by
    ext x
    obtain ⟨j, x, rfl⟩ := Types.jointly_surjective_of_isColimit hc x
    exact ((ConcreteCategory.congr_hom (hm j)) x).trans (CoconePt.fac_app

Depends on / 依赖: CoconePt, CoconePt.desc
-/
def isColimitCocone : IsColimit (cocone hc) where
  desc s := ofHom (CoconePt.desc hc s)
  fac s j := by
    ext x
    exact ConcreteCategory.congr_hom (hc.fac ((forget _).mapCocone s) j) x
  uniq s m hm := by
    ext x
    obtain ⟨j, x, rfl⟩ := Types.jointly_surjective_of_isColimit hc x
    exact ((ConcreteCategory.congr_hom (hm j)) x).trans (CoconePt.fac_apply hc s j x).symm

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: HasColimit F
  body: ⟨_, isColimitCocone (colimit.isColimit (F ⋙ forget _))⟩

中文:
实例 :
  签名: HasColimit F
  定义体: ⟨_, isColimitCocone (colimit.isColimit (F ⋙ forget _))⟩

Depends on / 依赖: colimit, colimit.isColimit, forget, isColimit, isColimitCocone
-/
instance : HasColimit F where
  exists_colimit := ⟨_, isColimitCocone (colimit.isColimit (F ⋙ forget _))⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: PreservesColimit F (forget _)
  body: preservesColimit_of_preserves_colimit_cocone
    (isColimitCocone (colimit.isColimit (F ⋙ forget _)))
    (colimit.isColimit (F ⋙ forget _))

中文:
实例 :
  签名: PreservesColimit F (forget _)
  定义体: preservesColimit_of_preserves_colimit_cocone
    (isColimitCocone (colimit.isColimit (F ⋙ forget _)))
    (colimit.isColimit (F ⋙ forget _))

Depends on / 依赖: colimit, colimit.isColimit, forget, isColimit, isColimitCocone, preservesColimit_of_preserves_colimit_cocone
-/
instance : PreservesColimit F (forget _) :=
  preservesColimit_of_preserves_colimit_cocone
    (isColimitCocone (colimit.isColimit (F ⋙ forget _)))
    (colimit.isColimit (F ⋙ forget _))

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: HasColimitsOfShape J PartOrdEmb.{u}

中文:
实例 :
  签名: HasColimitsOfShape J PartOrdEmb.{u}
-/
instance : HasColimitsOfShape J PartOrdEmb.{u} where

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: PreservesColimitsOfShape J (forget PartOrdEmb.{u})

中文:
实例 :
  签名: PreservesColimitsOfShape J (forget PartOrdEmb.{u})
-/
instance : PreservesColimitsOfShape J (forget PartOrdEmb.{u}) where

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: ReflectsColimitsOfShape J (forget PartOrdEmb.{u})
  body: reflectsColimitsOfShape_of_reflectsIsomorphisms

中文:
实例 :
  签名: ReflectsColimitsOfShape J (forget PartOrdEmb.{u})
  定义体: reflectsColimitsOfShape_of_reflectsIsomorphisms

Depends on / 依赖: reflectsColimitsOfShape_of_reflectsIsomorphisms
-/
instance : ReflectsColimitsOfShape J (forget PartOrdEmb.{u}) :=
  reflectsColimitsOfShape_of_reflectsIsomorphisms

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: HasFilteredColimitsOfSize.{u, u} PartOrdEmb.{u}
  body: inferInstance

中文:
实例 :
  签名: HasFilteredColimitsOfSize.{u, u} PartOrdEmb.{u}
  定义体: inferInstance
-/
instance : HasFilteredColimitsOfSize.{u, u} PartOrdEmb.{u} where
  HasColimitsOfShape _ := inferInstance

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: PreservesFilteredColimitsOfSize.{u, u} (forget PartOrdEmb.{u})
  body: inferInstance

中文:
实例 :
  签名: PreservesFilteredColimitsOfSize.{u, u} (forget PartOrdEmb.{u})
  定义体: inferInstance
-/
instance : PreservesFilteredColimitsOfSize.{u, u} (forget PartOrdEmb.{u}) where
  preserves_filtered_colimits _ := inferInstance

end Limits

variable {α : PartOrdEmb.{u}} (P : Set α -> Prop)

/-- Given a predicate `P : Set α → Prop` on the underlying type of `α : PartOrdEmb.{u}`,
this is the functor `Subtype P ⥤ PartOrdEmb.{u}` which sends a subset `J` of `α`
satisfying `P` to the induced partially ordered type `J`. -/
@[simps obj map]
/--
Definition of `functorOfPredicateSet` / `functorOfPredicateSet` 的定义

English:
definition functorOfPredicateSet
  signature: : Subtype P ⥤ PartOrdEmb.{u} where
  body: .of J.val
  map f :=
    ofHom {
      toFun x := ⟨x, leOfHom f x.prop⟩
      inj' _ _ _ := by aesop
      map_rel_iff' := by rfl }

中文:
定义 functorOfPredicateSet
  签名: : Subtype P ⥤ PartOrdEmb.{u} where
  定义体: .of J.val
  map f :=
    ofHom {
      toFun x := ⟨x, leOfHom f x.prop⟩
      inj' _ _ _ := by aesop
      map_rel_iff' := by rfl }

Depends on / 依赖: J.val
-/
def functorOfPredicateSet : Subtype P ⥤ PartOrdEmb.{u} where
  obj J := .of J.val
  map f :=
    ofHom {
      toFun x := ⟨x, leOfHom f x.prop⟩
      inj' _ _ _ := by aesop
      map_rel_iff' := by rfl }

/-- Given a predicate `P : Set α → Prop` on the underlying type of `α : PartOrdEmb.{u}`,
this is the cocone with point `α` given by all the inclusions of the subsets
satisfying `P`. -/
@[simps]
/--
Definition of `coconeOfPredicateSet` / `coconeOfPredicateSet` 的定义

English:
definition coconeOfPredicateSet
  signature: : Cocone (functorOfPredicateSet P) where
  body: α
  ι.app J := ofHom (OrderEmbedding.subtype _)

中文:
定义 coconeOfPredicateSet
  签名: : Cocone (functorOfPredicateSet P) where
  定义体: α
  ι.app J := ofHom (OrderEmbedding.subtype _)
-/
def coconeOfPredicateSet : Cocone (functorOfPredicateSet P) where
  pt := α
  ι.app J := ofHom (OrderEmbedding.subtype _)

/--
Definition of `isColimitOfPredicateSet` / `isColimitOfPredicateSet` 的定义

English:
definition isColimitOfPredicateSet
  body: isColimitOfReflects (forget PartOrdEmb.{u}) (by
    refine Types.FilteredColimit.isColimitOf' _ _ (fun a => ?_)
      (fun J x y h => ⟨J, 𝟙 _, Subtype.ext h⟩)
    obtain ⟨J, hJ, ha⟩ := hP a
    exact ⟨⟨J, hJ⟩, ⟨a, ha⟩, rfl⟩)

中文:
定义 isColimitOfPredicateSet
  定义体: isColimitOfReflects (forget PartOrdEmb.{u}) (by
    refine Types.FilteredColimit.isColimitOf' _ _ (fun a => ?_)
      (fun J x y h => ⟨J, 𝟙 _, Subtype.ext h⟩)
    obtain ⟨J, hJ, ha⟩ := hP a
    exact ⟨⟨J, hJ⟩, ⟨a, ha⟩, rfl⟩)

Depends on / 依赖: FilteredColimit, PartOrdEmb, Subtype, Subtype.ext, Types.FilteredColimit.isColimitOf, forget, isColimitOf, isColimitOfReflects
-/
noncomputable def isColimitOfPredicateSet
    [IsDirectedOrder (Subtype P)] [Nonempty (Subtype P)]
    (hP : forall (a : α), exists (J : Set α), P J ∧ a in J) :
    IsColimit (coconeOfPredicateSet P) :=
  isColimitOfReflects (forget PartOrdEmb.{u}) (by
    refine Types.FilteredColimit.isColimitOf' _ _ (fun a => ?_)
      (fun J x y h => ⟨J, 𝟙 _, Subtype.ext h⟩)
    obtain ⟨J, hJ, ha⟩ := hP a
    exact ⟨⟨J, hJ⟩, ⟨a, ha⟩, rfl⟩)

end PartOrdEmb
