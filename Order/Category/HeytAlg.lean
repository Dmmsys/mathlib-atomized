/-
Copyright (c) 2022 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
module

public import Mathlib.Order.Category.BddDistLat
public import Mathlib.Order.Heyting.Hom

/-!
# The category of Heyting algebras

This file defines `HeytAlg`, the category of Heyting algebras.
-/

@[expose] public section


universe u

open CategoryTheory Opposite Order

/--
Definition of `HeytAlg` / `HeytAlg` 的定义

English:
structure HeytAlg
  parameters: where
  axioms and operations (2):
    - carrier : Type*
    - [str : HeytingAlgebra carrier]

中文:
结构 HeytAlg
  参数: where
  公理与运算 (2 个):
    - carrier : 类型
    - [str : Heyting代数 carrier]
-/
structure HeytAlg where
  /-- The underlying Heyting algebra. -/
  carrier : Type*
  [str : HeytingAlgebra carrier]

attribute [instance] HeytAlg.str

initialize_simps_projections HeytAlg (carrier -> coe, -str)

namespace HeytAlg

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: CoeSort HeytAlg (Type _)
  body: ⟨HeytAlg.carrier⟩

中文:
实例 :
  签名: CoeSort HeytAlg (类型 _)
  定义体: ⟨HeytAlg.carrier⟩

Depends on / 依赖: HeytAlg, HeytAlg.carrier, carrier
-/
instance : CoeSort HeytAlg (Type _) :=
  ⟨HeytAlg.carrier⟩

attribute [coe] HeytAlg.carrier

/--
Definition of `of` / `of` 的定义

English:
abbreviation of
  signature: (X : Type*) [HeytingAlgebra X]
  body: ⟨X⟩

中文:
缩写 of
  签名: (X : 类型) [Heyting代数 X]
  定义体: ⟨X⟩
-/
abbrev of (X : Type*) [HeytingAlgebra X] : HeytAlg := ⟨X⟩

/-- The type of morphisms in `HeytAlg R`. -/
@[ext]
/--
Definition of `Hom` / `Hom` 的定义

English:
structure Hom
  parameters: (X Y : HeytAlg.{u})
  axioms and operations (2):
    - private(mk) : :
    - hom' : HeytingHom X Y

中文:
结构 态射
  参数: (X Y : HeytAlg.{u})
  公理与运算 (2 个):
    - private(mk) : :
    - hom' : Heyting态射 X Y
-/
structure Hom (X Y : HeytAlg.{u}) where
  private mk ::
  /-- The underlying `HeytingHom`. -/
  hom' : HeytingHom X Y

set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Category HeytAlg.{u}
  body: Hom X Y
  id X := ⟨HeytingHom.id X⟩
  comp f g := ⟨g.hom'.comp f.hom'⟩

中文:
实例 :
  签名: 范畴 HeytAlg.{u}
  定义体: Hom X Y
  id X := ⟨HeytingHom.id X⟩
  comp f g := ⟨g.hom'.comp f.hom'⟩
-/
instance : Category HeytAlg.{u} where
  Hom X Y := Hom X Y
  id X := ⟨HeytingHom.id X⟩
  comp f g := ⟨g.hom'.comp f.hom'⟩

set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: ConcreteCategory HeytAlg (HeytingHom · ·)
  body: Hom.hom'
  ofHom := Hom.mk

中文:
实例 :
  签名: 余ncrete范畴 HeytAlg (Heyting态射 · ·)
  定义体: Hom.hom'
  ofHom := Hom.mk

Depends on / 依赖: Hom.hom
-/
instance : ConcreteCategory HeytAlg (HeytingHom · ·) where
  hom := Hom.hom'
  ofHom := Hom.mk

/--
Definition of `Hom.hom` / `Hom.hom` 的定义

English:
abbreviation Hom.hom
  signature: {X Y : HeytAlg.{u}} (f : Hom X Y)
  body: ConcreteCategory.hom (C := HeytAlg) f

中文:
缩写 态射.hom
  签名: {X Y : HeytAlg.{u}} (f : 态射 X Y)
  定义体: ConcreteCategory.hom (C := HeytAlg) f
-/
abbrev Hom.hom {X Y : HeytAlg.{u}} (f : Hom X Y) :=
  ConcreteCategory.hom (C := HeytAlg) f

/--
Definition of `ofHom` / `ofHom` 的定义

English:
abbreviation ofHom
  signature: {X Y : Type u} [HeytingAlgebra X] [HeytingAlgebra Y] (f : HeytingHom X Y)
  body: ConcreteCategory.ofHom (C := HeytAlg) f

中文:
缩写 ofHom
  签名: {X Y : 类型u} [Heyting代数 X] [Heyting代数 Y] (f : Heyting态射 X Y)
  定义体: ConcreteCategory.ofHom (C := HeytAlg) f

Depends on / 依赖: ConcreteCategory, ConcreteCategory.ofHom, HeytAlg
-/
abbrev ofHom {X Y : Type u} [HeytingAlgebra X] [HeytingAlgebra Y] (f : HeytingHom X Y) :
    of X ⟶ of Y :=
  ConcreteCategory.ofHom (C := HeytAlg) f

variable {R} in
/--
Definition of `Hom.Simps.hom` / `Hom.Simps.hom` 的定义

English:
definition Hom.Simps.hom
  signature: (X Y : HeytAlg.{u}) (f : Hom X Y)
  body: f.hom

initialize_simps_projections Hom (hom' -> hom)

中文:
定义 态射.Simps.hom
  签名: (X Y : HeytAlg.{u}) (f : 态射 X Y)
  定义体: f.hom

initialize_simps_projections Hom (hom' -> hom)
-/
def Hom.Simps.hom (X Y : HeytAlg.{u}) (f : Hom X Y) :=
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
  given: {X : HeytAlg}
  statement: (𝟙 X : X -> X) = id
  proof: rfl

@[simp]

中文:
引理 coe_id
  条件: {X : HeytAlg}
  结论: (𝟙 X : X -> X) = id
  证明: rfl

@[simp]
-/
lemma coe_id {X : HeytAlg} : (𝟙 X : X -> X) = id := rfl

@[simp]
/--
lemma `coe_comp` / 引理 `coe_comp`

English:
lemma coe_comp
  given: {X Y Z : HeytAlg} {f : X ⟶ Y} {g : Y ⟶ Z}
  statement: (f ≫ g : X -> Z) = g ∘ f
  proof: rfl

@[simp]

中文:
引理 coe_comp
  条件: {X Y Z : HeytAlg} {f : X ⟶ Y} {g : Y ⟶ Z}
  结论: (f ≫ g : X -> Z) = g ∘ f
  证明: rfl

@[simp]
-/
lemma coe_comp {X Y Z : HeytAlg} {f : X ⟶ Y} {g : Y ⟶ Z} : (f ≫ g : X -> Z) = g ∘ f := rfl

@[simp]
/--
lemma `forget_map` / 引理 `forget_map`

English:
lemma forget_map
  given: {X Y : HeytAlg} (f : X ⟶ Y)
  proof: rfl

@[ext]

中文:
引理 forget_map
  条件: {X Y : HeytAlg} (f : X ⟶ Y)
  证明: rfl

@[ext]
-/
lemma forget_map {X Y : HeytAlg} (f : X ⟶ Y) :
    (forget HeytAlg).map f = (f : _ -> _) := rfl

@[ext]
/--
lemma `ext` / 引理 `ext`

English:
lemma ext
  given: {X Y : HeytAlg} {f g : X ⟶ Y} (w : forall x : X, f x = g x)
  statement: f = g
  proof: ConcreteCategory.hom_ext _ _ w

中文:
引理 ext
  条件: {X Y : HeytAlg} {f g : X ⟶ Y} (w : 对任意 x : X, f x = g x)
  结论: f = g
  证明: ConcreteCategory.hom_ext _ _ w

Depends on / 依赖: ConcreteCategory, ConcreteCategory.hom_ext, hom_ext
-/
lemma ext {X Y : HeytAlg} {f g : X ⟶ Y} (w : forall x : X, f x = g x) : f = g :=
  ConcreteCategory.hom_ext _ _ w

-- This is not `simp` to avoid rewriting in types of terms.
/--
theorem `coe_of` / 定理 `coe_of`

English:
theorem coe_of
  given: (X : Type u) [HeytingAlgebra X]
  statement: (HeytAlg.of X : Type u) = X
  proof: rfl

@[simp]

中文:
定理 coe_of
  条件: (X : 类型u) [Heyting代数 X]
  结论: (HeytAlg.of X : 类型u) = X
  证明: rfl

@[simp]
-/
theorem coe_of (X : Type u) [HeytingAlgebra X] : (HeytAlg.of X : Type u) = X := rfl

@[simp]
/--
lemma `hom_id` / 引理 `hom_id`

English:
lemma hom_id
  given: {X : HeytAlg}
  statement: (𝟙 X : X ⟶ X).hom = HeytingHom.id _
  proof: rfl

中文:
引理 hom_id
  条件: {X : HeytAlg}
  结论: (𝟙 X : X ⟶ X).hom = Heyting态射.id _
  证明: rfl
-/
lemma hom_id {X : HeytAlg} : (𝟙 X : X ⟶ X).hom = HeytingHom.id _ := rfl

/--
lemma `id_apply` / 引理 `id_apply`

English:
lemma id_apply
  given: (X : HeytAlg) (x : X)
  proof: by simp

@[simp]

中文:
引理 id_apply
  条件: (X : HeytAlg) (x : X)
  证明: by simp

@[simp]
-/
lemma id_apply (X : HeytAlg) (x : X) :
    (𝟙 X : X ⟶ X) x = x := by simp

@[simp]
/--
lemma `hom_comp` / 引理 `hom_comp`

English:
lemma hom_comp
  given: {X Y Z : HeytAlg} (f : X ⟶ Y) (g : Y ⟶ Z)
  proof: rfl

中文:
引理 hom_comp
  条件: {X Y Z : HeytAlg} (f : X ⟶ Y) (g : Y ⟶ Z)
  证明: rfl
-/
lemma hom_comp {X Y Z : HeytAlg} (f : X ⟶ Y) (g : Y ⟶ Z) :
    (f ≫ g).hom = g.hom.comp f.hom := rfl

/--
lemma `comp_apply` / 引理 `comp_apply`

English:
lemma comp_apply
  given: {X Y Z : HeytAlg} (f : X ⟶ Y) (g : Y ⟶ Z) (x : X)
  proof: by simp

@[ext]

中文:
引理 comp_apply
  条件: {X Y Z : HeytAlg} (f : X ⟶ Y) (g : Y ⟶ Z) (x : X)
  证明: by simp

@[ext]
-/
lemma comp_apply {X Y Z : HeytAlg} (f : X ⟶ Y) (g : Y ⟶ Z) (x : X) :
    (f ≫ g) x = g (f x) := by simp

@[ext]
/--
lemma `hom_ext` / 引理 `hom_ext`

English:
lemma hom_ext
  given: {X Y : HeytAlg} {f g : X ⟶ Y} (hf : f.hom = g.hom)
  statement: f = g
  proof: Hom.ext hf

@[simp]

中文:
引理 hom_ext
  条件: {X Y : HeytAlg} {f g : X ⟶ Y} (hf : f.hom = g.hom)
  结论: f = g
  证明: Hom.ext hf

@[simp]

Depends on / 依赖: Hom.ext
-/
lemma hom_ext {X Y : HeytAlg} {f g : X ⟶ Y} (hf : f.hom = g.hom) : f = g :=
  Hom.ext hf

@[simp]
/--
lemma `hom_ofHom` / 引理 `hom_ofHom`

English:
lemma hom_ofHom
  given: {X Y : Type u} [HeytingAlgebra X] [HeytingAlgebra Y] (f : HeytingHom X Y)
  proof: rfl

@[simp]

中文:
引理 hom_ofHom
  条件: {X Y : 类型u} [Heyting代数 X] [Heyting代数 Y] (f : Heyting态射 X Y)
  证明: rfl

@[simp]
-/
lemma hom_ofHom {X Y : Type u} [HeytingAlgebra X] [HeytingAlgebra Y] (f : HeytingHom X Y) :
    (ofHom f).hom = f :=
  rfl

@[simp]
/--
lemma `ofHom_hom` / 引理 `ofHom_hom`

English:
lemma ofHom_hom
  given: {X Y : HeytAlg} (f : X ⟶ Y)
  proof: rfl

@[simp]

中文:
引理 ofHom_hom
  条件: {X Y : HeytAlg} (f : X ⟶ Y)
  证明: rfl

@[simp]
-/
lemma ofHom_hom {X Y : HeytAlg} (f : X ⟶ Y) :
    ofHom (Hom.hom f) = f := rfl

@[simp]
/--
lemma `ofHom_id` / 引理 `ofHom_id`

English:
lemma ofHom_id
  given: {X : Type u} [HeytingAlgebra X]
  statement: ofHom (HeytingHom.id _) = 𝟙 (of X)
  proof: rfl

@[simp]

中文:
引理 ofHom_id
  条件: {X : 类型u} [Heyting代数 X]
  结论: ofHom (Heyting态射.id _) = 𝟙 (of X)
  证明: rfl

@[simp]
-/
lemma ofHom_id {X : Type u} [HeytingAlgebra X] : ofHom (HeytingHom.id _) = 𝟙 (of X) := rfl

@[simp]
/--
lemma `ofHom_comp` / 引理 `ofHom_comp`

English:
lemma ofHom_comp
  statement: {X Y Z : Type u} [HeytingAlgebra X] [HeytingAlgebra Y] [HeytingAlgebra Z]
  proof: rfl

中文:
引理 ofHom_comp
  结论: {X Y Z : 类型u} [Heyting代数 X] [Heyting代数 Y] [Heyting代数 Z]
  证明: rfl
-/
lemma ofHom_comp {X Y Z : Type u} [HeytingAlgebra X] [HeytingAlgebra Y] [HeytingAlgebra Z]
    (f : HeytingHom X Y) (g : HeytingHom Y Z) :
    ofHom (g.comp f) = ofHom f ≫ ofHom g :=
  rfl

/--
lemma `ofHom_apply` / 引理 `ofHom_apply`

English:
lemma ofHom_apply
  statement: {X Y : Type u} [HeytingAlgebra X] [HeytingAlgebra Y]
  proof: rfl

中文:
引理 ofHom_apply
  结论: {X Y : 类型u} [Heyting代数 X] [Heyting代数 Y]
  证明: rfl
-/
lemma ofHom_apply {X Y : Type u} [HeytingAlgebra X] [HeytingAlgebra Y]
    (f : HeytingHom X Y) (x : X) :
    (ofHom f) x = f x := rfl

/--
lemma `inv_hom_apply` / 引理 `inv_hom_apply`

English:
lemma inv_hom_apply
  given: {X Y : HeytAlg} (e : X ≅ Y) (x : X)
  statement: e.inv (e.hom x) = x
  proof: by
  simp

中文:
引理 inv_hom_apply
  条件: {X Y : HeytAlg} (e : X ≅ Y) (x : X)
  结论: e.inv (e.hom x) = x
  证明: by
  simp
-/
lemma inv_hom_apply {X Y : HeytAlg} (e : X ≅ Y) (x : X) : e.inv (e.hom x) = x := by
  simp

/--
lemma `hom_inv_apply` / 引理 `hom_inv_apply`

English:
lemma hom_inv_apply
  given: {X Y : HeytAlg} (e : X ≅ Y) (s : Y)
  statement: e.hom (e.inv s) = s
  proof: by
  simp

中文:
引理 hom_inv_apply
  条件: {X Y : HeytAlg} (e : X ≅ Y) (s : Y)
  结论: e.hom (e.inv s) = s
  证明: by
  simp
-/
lemma hom_inv_apply {X Y : HeytAlg} (e : X ≅ Y) (s : Y) : e.hom (e.inv s) = s := by
  simp

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Inhabited HeytAlg
  body: ⟨of PUnit⟩

@[simps]

中文:
实例 :
  签名: 可居 HeytAlg
  定义体: ⟨of PUnit⟩

@[simps]
-/
instance : Inhabited HeytAlg :=
  ⟨of PUnit⟩

@[simps]
/--
Instance `hasForgetToLat` / 实例 `hasForgetToLat`

English:
instance hasForgetToLat
  signature: : HasForget₂ HeytAlg BddDistLat where
  body: .of X
  forget₂.map f := BddDistLat.ofHom f.hom

中文:
实例 hasForgetToLat
  签名: : 有Forget₂ HeytAlg 有界分配格 where
  定义体: .of X
  forget₂.map f := BddDistLat.ofHom f.hom
-/
instance hasForgetToLat : HasForget₂ HeytAlg BddDistLat where
  forget₂.obj X := .of X
  forget₂.map f := BddDistLat.ofHom f.hom

/-- Constructs an isomorphism of Heyting algebras from an order isomorphism between them. -/
@[simps]
/--
Definition of `Iso.mk` / `Iso.mk` 的定义

English:
definition Iso.mk
  signature: {α β : HeytAlg.{u}} (e : α ≃o β)
  body: ofHom e
  inv := ofHom e.symm
  hom_inv_id := by ext; exact e.symm_apply_apply _
  inv_hom_id := by ext; exact e.apply_symm_apply _

中文:
定义 同构.mk
  签名: {α β : HeytAlg.{u}} (e : α ≃o β)
  定义体: ofHom e
  inv := ofHom e.symm
  hom_inv_id := by ext; exact e.symm_apply_apply _
  inv_hom_id := by ext; exact e.apply_symm_apply _
-/
def Iso.mk {α β : HeytAlg.{u}} (e : α ≃o β) : α ≅ β where
  hom := ofHom e
  inv := ofHom e.symm
  hom_inv_id := by ext; exact e.symm_apply_apply _
  inv_hom_id := by ext; exact e.apply_symm_apply _

end HeytAlg
