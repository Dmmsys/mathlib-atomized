/-
Copyright (c) 2022 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
module

public import Mathlib.Order.Category.HeytAlg
public import Mathlib.Order.Hom.CompleteLattice

/-!
# The category of Boolean algebras

This defines `BoolAlg`, the category of Boolean algebras.
-/

@[expose] public section


open OrderDual Opposite Set

universe u

open CategoryTheory

/--
Definition of `BoolAlg` / `BoolAlg` 的定义

English:
structure BoolAlg
  parameters: where
  axioms and operations (3):
    - of : :
    - carrier : Type*
    - [str : BooleanAlgebra carrier]

中文:
结构 BoolAlg
  参数: where
  公理与运算 (3 个):
    - of : :
    - carrier : 类型
    - [str : 布尔eanAlgebra carrier]
-/
structure BoolAlg where
  /-- Construct a bundled `BoolAlg` from the underlying type and typeclass. -/
  of ::
  /-- The underlying Boolean algebra. -/
  carrier : Type*
  [str : BooleanAlgebra carrier]

attribute [instance] BoolAlg.str

initialize_simps_projections BoolAlg (carrier -> coe, -str)

namespace BoolAlg

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: CoeSort BoolAlg (Type _)
  body: ⟨BoolAlg.carrier⟩

中文:
实例 :
  签名: CoeSort 布尔Alg (Type _)
  定义体: ⟨BoolAlg.carrier⟩

Depends on / 依赖: BoolAlg, BoolAlg.carrier, carrier
-/
instance : CoeSort BoolAlg (Type _) :=
  ⟨BoolAlg.carrier⟩

attribute [coe] BoolAlg.carrier

/-- The type of morphisms in `BoolAlg R`. -/
@[ext]
/--
Definition of `Hom` / `Hom` 的定义

English:
structure Hom
  parameters: (X Y : BoolAlg.{u})
  axioms and operations (2):
    - private(mk) : :
    - hom' : BoundedLatticeHom X Y

中文:
结构 Hom
  参数: (X Y : 布尔Alg.{u})
  公理与运算 (2 个):
    - private(mk) : :
    - hom' : BoundedLatticeHom X Y
-/
structure Hom (X Y : BoolAlg.{u}) where
  private mk ::
  /-- The underlying `BoundedLatticeHom`. -/
  hom' : BoundedLatticeHom X Y

set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Category BoolAlg.{u}
  body: Hom X Y
  id X := ⟨BoundedLatticeHom.id X⟩
  comp f g := ⟨g.hom'.comp f.hom'⟩

中文:
实例 :
  签名: Category 布尔Alg.{u}
  定义体: Hom X Y
  id X := ⟨BoundedLatticeHom.id X⟩
  comp f g := ⟨g.hom'.comp f.hom'⟩
-/
instance : Category BoolAlg.{u} where
  Hom X Y := Hom X Y
  id X := ⟨BoundedLatticeHom.id X⟩
  comp f g := ⟨g.hom'.comp f.hom'⟩

set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: ConcreteCategory BoolAlg (BoundedLatticeHom · ·)
  body: Hom.hom'
  ofHom := Hom.mk

中文:
实例 :
  签名: ConcreteCategory 布尔Alg (BoundedLatticeHom · ·)
  定义体: Hom.hom'
  ofHom := Hom.mk

Depends on / 依赖: Hom.hom
-/
instance : ConcreteCategory BoolAlg (BoundedLatticeHom · ·) where
  hom := Hom.hom'
  ofHom := Hom.mk

/--
Definition of `Hom.hom` / `Hom.hom` 的定义

English:
abbreviation Hom.hom
  signature: {X Y : BoolAlg.{u}} (f : Hom X Y)
  body: ConcreteCategory.hom (C := BoolAlg) f

中文:
缩写 Hom.hom
  签名: {X Y : 布尔Alg.{u}} (f : Hom X Y)
  定义体: ConcreteCategory.hom (C := BoolAlg) f
-/
abbrev Hom.hom {X Y : BoolAlg.{u}} (f : Hom X Y) :=
  ConcreteCategory.hom (C := BoolAlg) f

/--
Definition of `ofHom` / `ofHom` 的定义

English:
abbreviation ofHom
  signature: {X Y : Type u} [BooleanAlgebra X] [BooleanAlgebra Y] (f : BoundedLatticeHom X Y)
  body: ConcreteCategory.ofHom (C := BoolAlg) f

中文:
缩写 ofHom
  签名: {X Y : 类型u} [布尔eanAlgebra X] [布尔eanAlgebra Y] (f : BoundedLatticeHom X Y)
  定义体: ConcreteCategory.ofHom (C := BoolAlg) f

Depends on / 依赖: BoolAlg, ConcreteCategory, ConcreteCategory.ofHom
-/
abbrev ofHom {X Y : Type u} [BooleanAlgebra X] [BooleanAlgebra Y] (f : BoundedLatticeHom X Y) :
    of X ⟶ of Y :=
  ConcreteCategory.ofHom (C := BoolAlg) f

variable {R} in
/--
Definition of `Hom.Simps.hom` / `Hom.Simps.hom` 的定义

English:
definition Hom.Simps.hom
  signature: (X Y : BoolAlg.{u}) (f : Hom X Y)
  body: f.hom

initialize_simps_projections Hom (hom' -> hom)

中文:
定义 Hom.Simps.hom
  签名: (X Y : 布尔Alg.{u}) (f : Hom X Y)
  定义体: f.hom

initialize_simps_projections Hom (hom' -> hom)
-/
def Hom.Simps.hom (X Y : BoolAlg.{u}) (f : Hom X Y) :=
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
  given: {X : BoolAlg}
  statement: (𝟙 X : X -> X) = id
  proof: rfl

@[simp]

中文:
引理 coe_id
  条件: {X : 布尔Alg}
  结论: (𝟙 X : X -> X) = id
  证明: rfl

@[simp]
-/
lemma coe_id {X : BoolAlg} : (𝟙 X : X -> X) = id := rfl

@[simp]
/--
lemma `coe_comp` / 引理 `coe_comp`

English:
lemma coe_comp
  given: {X Y Z : BoolAlg} {f : X ⟶ Y} {g : Y ⟶ Z}
  statement: (f ≫ g : X -> Z) = g ∘ f
  proof: rfl

@[simp]

中文:
引理 coe_comp
  条件: {X Y Z : 布尔Alg} {f : X ⟶ Y} {g : Y ⟶ Z}
  结论: (f ≫ g : X -> Z) = g ∘ f
  证明: rfl

@[simp]
-/
lemma coe_comp {X Y Z : BoolAlg} {f : X ⟶ Y} {g : Y ⟶ Z} : (f ≫ g : X -> Z) = g ∘ f := rfl

@[simp]
/--
lemma `forget_map` / 引理 `forget_map`

English:
lemma forget_map
  given: {X Y : BoolAlg} (f : X ⟶ Y)
  proof: rfl

@[ext]

中文:
引理 forget_map
  条件: {X Y : 布尔Alg} (f : X ⟶ Y)
  证明: rfl

@[ext]
-/
lemma forget_map {X Y : BoolAlg} (f : X ⟶ Y) :
    (forget BoolAlg).map f = (f : _ -> _) := rfl

@[ext]
/--
lemma `ext` / 引理 `ext`

English:
lemma ext
  given: {X Y : BoolAlg} {f g : X ⟶ Y} (w : forall x : X, f x = g x)
  statement: f = g
  proof: ConcreteCategory.hom_ext _ _ w

中文:
引理 ext
  条件: {X Y : 布尔Alg} {f g : X ⟶ Y} (w : 对任意 x : X, f x = g x)
  结论: f = g
  证明: ConcreteCategory.hom_ext _ _ w

Depends on / 依赖: ConcreteCategory, ConcreteCategory.hom_ext, hom_ext
-/
lemma ext {X Y : BoolAlg} {f g : X ⟶ Y} (w : forall x : X, f x = g x) : f = g :=
  ConcreteCategory.hom_ext _ _ w

-- This is not `simp` to avoid rewriting in types of terms.
/--
theorem `coe_of` / 定理 `coe_of`

English:
theorem coe_of
  given: (X : Type u) [BooleanAlgebra X]
  statement: (BoolAlg.of X : Type u) = X
  proof: rfl

@[simp]

中文:
定理 coe_of
  条件: (X : 类型u) [布尔eanAlgebra X]
  结论: (布尔Alg.of X : 类型u) = X
  证明: rfl

@[simp]
-/
theorem coe_of (X : Type u) [BooleanAlgebra X] : (BoolAlg.of X : Type u) = X := rfl

@[simp]
/--
lemma `hom_id` / 引理 `hom_id`

English:
lemma hom_id
  given: {X : BoolAlg}
  statement: (𝟙 X : X ⟶ X).hom = BoundedLatticeHom.id _
  proof: rfl

中文:
引理 hom_id
  条件: {X : 布尔Alg}
  结论: (𝟙 X : X ⟶ X).hom = BoundedLatticeHom.id _
  证明: rfl
-/
lemma hom_id {X : BoolAlg} : (𝟙 X : X ⟶ X).hom = BoundedLatticeHom.id _ := rfl

/--
lemma `id_apply` / 引理 `id_apply`

English:
lemma id_apply
  given: (X : BoolAlg) (x : X)
  proof: by simp

@[simp]

中文:
引理 id_apply
  条件: (X : 布尔Alg) (x : X)
  证明: by simp

@[simp]
-/
lemma id_apply (X : BoolAlg) (x : X) :
    (𝟙 X : X ⟶ X) x = x := by simp

@[simp]
/--
lemma `hom_comp` / 引理 `hom_comp`

English:
lemma hom_comp
  given: {X Y Z : BoolAlg} (f : X ⟶ Y) (g : Y ⟶ Z)
  proof: rfl

中文:
引理 hom_comp
  条件: {X Y Z : 布尔Alg} (f : X ⟶ Y) (g : Y ⟶ Z)
  证明: rfl
-/
lemma hom_comp {X Y Z : BoolAlg} (f : X ⟶ Y) (g : Y ⟶ Z) :
    (f ≫ g).hom = g.hom.comp f.hom := rfl

/--
lemma `comp_apply` / 引理 `comp_apply`

English:
lemma comp_apply
  given: {X Y Z : BoolAlg} (f : X ⟶ Y) (g : Y ⟶ Z) (x : X)
  proof: by simp

@[ext]

中文:
引理 comp_apply
  条件: {X Y Z : 布尔Alg} (f : X ⟶ Y) (g : Y ⟶ Z) (x : X)
  证明: by simp

@[ext]
-/
lemma comp_apply {X Y Z : BoolAlg} (f : X ⟶ Y) (g : Y ⟶ Z) (x : X) :
    (f ≫ g) x = g (f x) := by simp

@[ext]
/--
lemma `hom_ext` / 引理 `hom_ext`

English:
lemma hom_ext
  given: {X Y : BoolAlg} {f g : X ⟶ Y} (hf : f.hom = g.hom)
  statement: f = g
  proof: Hom.ext hf

@[simp]

中文:
引理 hom_ext
  条件: {X Y : 布尔Alg} {f g : X ⟶ Y} (hf : f.hom = g.hom)
  结论: f = g
  证明: Hom.ext hf

@[simp]

Depends on / 依赖: Hom.ext
-/
lemma hom_ext {X Y : BoolAlg} {f g : X ⟶ Y} (hf : f.hom = g.hom) : f = g :=
  Hom.ext hf

@[simp]
/--
lemma `hom_ofHom` / 引理 `hom_ofHom`

English:
lemma hom_ofHom
  given: {X Y : Type u} [BooleanAlgebra X] [BooleanAlgebra Y] (f : BoundedLatticeHom X Y)
  proof: rfl

@[simp]

中文:
引理 hom_ofHom
  条件: {X Y : 类型u} [布尔eanAlgebra X] [布尔eanAlgebra Y] (f : BoundedLatticeHom X Y)
  证明: rfl

@[simp]
-/
lemma hom_ofHom {X Y : Type u} [BooleanAlgebra X] [BooleanAlgebra Y] (f : BoundedLatticeHom X Y) :
    (ofHom f).hom = f :=
  rfl

@[simp]
/--
lemma `ofHom_hom` / 引理 `ofHom_hom`

English:
lemma ofHom_hom
  given: {X Y : BoolAlg} (f : X ⟶ Y)
  proof: rfl

@[simp]

中文:
引理 ofHom_hom
  条件: {X Y : 布尔Alg} (f : X ⟶ Y)
  证明: rfl

@[simp]
-/
lemma ofHom_hom {X Y : BoolAlg} (f : X ⟶ Y) :
    ofHom (Hom.hom f) = f := rfl

@[simp]
/--
lemma `ofHom_id` / 引理 `ofHom_id`

English:
lemma ofHom_id
  given: {X : Type u} [BooleanAlgebra X]
  statement: ofHom (BoundedLatticeHom.id _) = 𝟙 (of X)
  proof: rfl

@[simp]

中文:
引理 ofHom_id
  条件: {X : 类型u} [布尔eanAlgebra X]
  结论: ofHom (BoundedLatticeHom.id _) = 𝟙 (of X)
  证明: rfl

@[simp]
-/
lemma ofHom_id {X : Type u} [BooleanAlgebra X] : ofHom (BoundedLatticeHom.id _) = 𝟙 (of X) := rfl

@[simp]
/--
lemma `ofHom_comp` / 引理 `ofHom_comp`

English:
lemma ofHom_comp
  statement: {X Y Z : Type u} [BooleanAlgebra X] [BooleanAlgebra Y] [BooleanAlgebra Z]
  proof: rfl

中文:
引理 ofHom_comp
  结论: {X Y Z : 类型u} [布尔eanAlgebra X] [布尔eanAlgebra Y] [布尔eanAlgebra Z]
  证明: rfl
-/
lemma ofHom_comp {X Y Z : Type u} [BooleanAlgebra X] [BooleanAlgebra Y] [BooleanAlgebra Z]
    (f : BoundedLatticeHom X Y) (g : BoundedLatticeHom Y Z) :
    ofHom (g.comp f) = ofHom f ≫ ofHom g :=
  rfl

/--
lemma `ofHom_apply` / 引理 `ofHom_apply`

English:
lemma ofHom_apply
  statement: {X Y : Type u} [BooleanAlgebra X] [BooleanAlgebra Y]
  proof: rfl

中文:
引理 ofHom_apply
  结论: {X Y : 类型u} [布尔eanAlgebra X] [布尔eanAlgebra Y]
  证明: rfl
-/
lemma ofHom_apply {X Y : Type u} [BooleanAlgebra X] [BooleanAlgebra Y]
    (f : BoundedLatticeHom X Y) (x : X) :
    (ofHom f) x = f x := rfl

/--
lemma `inv_hom_apply` / 引理 `inv_hom_apply`

English:
lemma inv_hom_apply
  given: {X Y : BoolAlg} (e : X ≅ Y) (x : X)
  statement: e.inv (e.hom x) = x
  proof: by
  simp

中文:
引理 inv_hom_apply
  条件: {X Y : 布尔Alg} (e : X ≅ Y) (x : X)
  结论: e.inv (e.hom x) = x
  证明: by
  simp
-/
lemma inv_hom_apply {X Y : BoolAlg} (e : X ≅ Y) (x : X) : e.inv (e.hom x) = x := by
  simp

/--
lemma `hom_inv_apply` / 引理 `hom_inv_apply`

English:
lemma hom_inv_apply
  given: {X Y : BoolAlg} (e : X ≅ Y) (s : Y)
  statement: e.hom (e.inv s) = s
  proof: by
  simp

中文:
引理 hom_inv_apply
  条件: {X Y : 布尔Alg} (e : X ≅ Y) (s : Y)
  结论: e.hom (e.inv s) = s
  证明: by
  simp
-/
lemma hom_inv_apply {X Y : BoolAlg} (e : X ≅ Y) (s : Y) : e.hom (e.inv s) = s := by
  simp

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Inhabited BoolAlg
  body: ⟨of PUnit⟩

中文:
实例 :
  签名: Inhabited 布尔Alg
  定义体: ⟨of PUnit⟩
-/
instance : Inhabited BoolAlg :=
  ⟨of PUnit⟩

/--
Definition of `toBddDistLat` / `toBddDistLat` 的定义

English:
definition toBddDistLat
  signature: (X : BoolAlg)
  body: .of X

@[simp]

中文:
定义 toBddDistLat
  签名: (X : 布尔Alg)
  定义体: .of X

@[simp]
-/
def toBddDistLat (X : BoolAlg) : BddDistLat :=
  .of X

@[simp]
/--
theorem `coe_toBddDistLat` / 定理 `coe_toBddDistLat`

English:
theorem coe_toBddDistLat
  given: (X : BoolAlg)
  statement: ↥X.toBddDistLat = ↥X
  proof: rfl

中文:
定理 coe_toBddDistLat
  条件: (X : 布尔Alg)
  结论: ↥X.toBddDistLat = ↥X
  证明: rfl
-/
theorem coe_toBddDistLat (X : BoolAlg) : ↥X.toBddDistLat = ↥X :=
  rfl

/--
Instance `hasForgetToBddDistLat` / 实例 `hasForgetToBddDistLat`

English:
instance hasForgetToBddDistLat
  signature: : HasForget₂ BoolAlg BddDistLat where
  body: .of X
  forget₂.map f := BddDistLat.ofHom f.hom

中文:
实例 hasForgetToBddDistLat
  签名: : HasForget₂ 布尔Alg BddDistLat where
  定义体: .of X
  forget₂.map f := BddDistLat.ofHom f.hom
-/
instance hasForgetToBddDistLat : HasForget₂ BoolAlg BddDistLat where
  forget₂.obj X := .of X
  forget₂.map f := BddDistLat.ofHom f.hom

section

attribute [local instance] BoundedLatticeHomClass.toBiheytingHomClass

@[simps]
/--
Instance `hasForgetToHeytAlg` / 实例 `hasForgetToHeytAlg`

English:
instance hasForgetToHeytAlg
  signature: : HasForget₂ BoolAlg HeytAlg where
  body: .of X
  forget₂.map {X Y} f := HeytAlg.ofHom f.hom

中文:
实例 hasForgetToHeytAlg
  签名: : HasForget₂ 布尔Alg HeytAlg where
  定义体: .of X
  forget₂.map {X Y} f := HeytAlg.ofHom f.hom
-/
instance hasForgetToHeytAlg : HasForget₂ BoolAlg HeytAlg where
  forget₂.obj X := .of X
  forget₂.map {X Y} f := HeytAlg.ofHom f.hom

end

/-- Constructs an equivalence between Boolean algebras from an order isomorphism between them. -/
@[simps]
/--
Definition of `Iso.mk` / `Iso.mk` 的定义

English:
definition Iso.mk
  signature: {α β : BoolAlg.{u}} (e : α ≃o β)
  body: ofHom e
  inv := ofHom e.symm

中文:
定义 Iso.mk
  签名: {α β : 布尔Alg.{u}} (e : α ≃o β)
  定义体: ofHom e
  inv := ofHom e.symm
-/
def Iso.mk {α β : BoolAlg.{u}} (e : α ≃o β) : α ≅ β where
  hom := ofHom e
  inv := ofHom e.symm

/-- `OrderDual` as a functor. -/
@[simps map]
/--
Definition of `dual` / `dual` 的定义

English:
definition dual
  signature: : BoolAlg ⥤ BoolAlg where
  body: of Xᵒᵈ
  map f := ofHom f.hom.dual

中文:
定义 dual
  签名: : 布尔Alg ⥤ 布尔Alg where
  定义体: of Xᵒᵈ
  map f := ofHom f.hom.dual
-/
def dual : BoolAlg ⥤ BoolAlg where
  obj X := of Xᵒᵈ
  map f := ofHom f.hom.dual

/-- The equivalence between `BoolAlg` and itself induced by `OrderDual` both ways. -/
@[simps functor inverse]
/--
Definition of `dualEquiv` / `dualEquiv` 的定义

English:
definition dualEquiv
  signature: : BoolAlg ≌ BoolAlg where
  body: dual
  inverse := dual
unitIso := NatIso.ofComponents fun X => Iso.mk OrderIso.dualDual X
counitIso := NatIso.ofComponents fun X => Iso.mk OrderIso.dualDual X

中文:
定义 dualEquiv
  签名: : 布尔Alg ≌ 布尔Alg where
  定义体: dual
  inverse := dual
unitIso := NatIso.ofComponents fun X => Iso.mk OrderIso.dualDual X
counitIso := NatIso.ofComponents fun X => Iso.mk OrderIso.dualDual X
-/
def dualEquiv : BoolAlg ≌ BoolAlg where
  functor := dual
  inverse := dual
unitIso := NatIso.ofComponents fun X => Iso.mk OrderIso.dualDual X
counitIso := NatIso.ofComponents fun X => Iso.mk OrderIso.dualDual X

end BoolAlg

/--
theorem `boolAlg_dual_comp_forget_to_bddDistLat` / 定理 `boolAlg_dual_comp_forget_to_bddDistLat`

English:
theorem boolAlg_dual_comp_forget_to_bddDistLat
  proof: rfl

中文:
定理 boolAlg_dual_comp_forget_to_bddDistLat
  证明: rfl
-/
theorem boolAlg_dual_comp_forget_to_bddDistLat :
    BoolAlg.dual ⋙ forget₂ BoolAlg BddDistLat =
    forget₂ BoolAlg BddDistLat ⋙ BddDistLat.dual :=
  rfl

/-- The powerset functor. `Set` as a contravariant functor. -/
@[simps]
/--
Definition of `typeToBoolAlgOp` / `typeToBoolAlgOp` 的定义

English:
definition typeToBoolAlgOp
  signature: : Type u ⥤ BoolAlgᵒᵖ where
  body: op .of (Set X)
  map {X Y} f := Quiver.Hom.op (BoolAlg.ofHom (CompleteLatticeHom.setPreimage f))

中文:
定义 typeToBoolAlgOp
  签名: : 类型u ⥤ 布尔Algᵒᵖ where
  定义体: op .of (Set X)
  map {X Y} f := Quiver.Hom.op (BoolAlg.ofHom (CompleteLatticeHom.setPreimage f))
-/
def typeToBoolAlgOp : Type u ⥤ BoolAlgᵒᵖ where
obj X := op .of (Set X)
  map {X Y} f := Quiver.Hom.op (BoolAlg.ofHom (CompleteLatticeHom.setPreimage f))
