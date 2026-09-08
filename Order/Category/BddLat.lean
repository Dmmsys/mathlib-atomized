/-
Copyright (c) 2022 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
module

public import Mathlib.CategoryTheory.Adjunction.Unique
public import Mathlib.Order.Category.BddOrd
public import Mathlib.Order.Category.Lat
public import Mathlib.Order.Category.Semilat
public import Mathlib.Order.Hom.WithTopBot

/-!
# The category of bounded lattices

This file defines `BddLat`, the category of bounded lattices.

In literature, this is sometimes called `Lat`, the category of lattices, because being a lattice is
understood to entail having a bottom and a top element.
-/

@[expose] public section


universe u

open CategoryTheory

/-- The category of bounded lattices with bounded lattice morphisms. -/
/-
**BddLat** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：Type (u_1 + 1)
参数：u_1 + 1。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The category of bounded lattices with bounded lattice morphisms.
-/
structure BddLat extends Lat where
  [isBoundedOrder : BoundedOrder toLat]

/-- The underlying lattice of a bounded lattice. -/
add_decl_doc BddLat.toLat

namespace BddLat

/-
**BddLat.** 是 Mathlib 中的一个实例，位于命名空间 `BddLat`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : CoeSort BddLat Type* :=
  ⟨fun X => X.toLat⟩

attribute [instance] BddLat.isBoundedOrder

/-- Construct a bundled `BddLat` from `Lattice` + `BoundedOrder`. -/
/-
**BddLat.of** 是 Mathlib 中的一个缩写定义，位于命名空间 `BddLat`。
形式化陈述：of (α : Type*) [Lattice α] [BoundedOrder α] : BddLat where carrier
参数：α : Type*。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Construct a bundled `BddLat` from `Lattice` + `BoundedOrder`.
-/
abbrev of (α : Type*) [Lattice α] [BoundedOrder α] : BddLat where
  carrier := α
/-
**BddLat.coe_of** 是 Mathlib 中的一个定理，位于命名空间 `BddLat`。
形式化陈述：coe_of (α : Type*) [Lattice α] [BoundedOrder α] : ↥(of α) = α
参数：α : Type*。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_of (α : Type*) [Lattice α] [BoundedOrder α] : ↥(of α) = α :=
  rfl

/-- The type of morphisms in `BddLat`. -/
@[ext]
/-
**BddLat.Hom** 是 Mathlib 中的一个归纳类型，位于命名空间 `BddLat`。
形式化陈述：BddLat → BddLat → Type u
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The type of morphisms in `BddLat`.
-/
structure Hom (X Y : BddLat.{u}) where
  private mk ::
  /-- The underlying `BoundedLatticeHom`. -/
  hom' : BoundedLatticeHom X Y
/-
**BddLat.** 是 Mathlib 中的一个实例，位于命名空间 `BddLat`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Inhabited BddLat :=
  ⟨of PUnit⟩

set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
/-
**BddLat.** 是 Mathlib 中的一个实例，位于命名空间 `BddLat`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : LargeCategory.{u} BddLat where
  Hom := Hom
  id X := ⟨BoundedLatticeHom.id X⟩
  comp f g := ⟨g.hom'.comp f.hom'⟩

set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
/-
**BddLat.** 是 Mathlib 中的一个实例，位于命名空间 `BddLat`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : ConcreteCategory BddLat (BoundedLatticeHom · ·) where
  hom := Hom.hom'
  ofHom := Hom.mk

/-- Turn a morphism in `BddLat` back into a `BoundedLatticeHom`. -/
/-
**BddLat.Hom.hom** 是 Mathlib 中的一个定义，位于命名空间 `BddLat.Hom`。
形式化陈述：{X Y : BddLat} → X.Hom Y → BoundedLatticeHom ↑X.toLat ↑Y.toLat
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Turn a morphism in `BddLat` back into a `BoundedLatticeHom`.
-/
abbrev Hom.hom {X Y : BddLat.{u}} (f : Hom X Y) :=
  ConcreteCategory.hom (C := BddLat) f

/-- Typecheck a `BoundedLatticeHom` as a morphism in `BddLat`. -/
/-
**BddLat.ofHom** 是 Mathlib 中的一个缩写定义，位于命名空间 `BddLat`。
形式化陈述：ofHom {X Y : Type u} [Lattice X] [BoundedOrder X] [Lattice Y] [BoundedOrde
r Y] (f : BoundedLatticeHom X Y) : of X ⟶ of Y
参数：f : BoundedLatticeHom X Y。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Typecheck a `BoundedLatticeHom` as a morphism in `BddLat`.
-/
abbrev ofHom {X Y : Type u} [Lattice X] [BoundedOrder X] [Lattice Y] [BoundedOrder Y]
    (f : BoundedLatticeHom X Y) : of X ⟶ of Y :=
  ConcreteCategory.ofHom (C := BddLat) f

variable {R} in
/-- Use the `ConcreteCategory.hom` projection for `@[simps]` lemmas. -/
/-
**BddLat.Hom.Simps.hom** 是 Mathlib 中的一个定义，位于命名空间 `BddLat.Hom.Simps`。
形式化陈述：(X Y : BddLat) → X.Hom Y → BoundedLatticeHom ↑X.toLat ↑Y.toLat
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Use the `ConcreteCategory.hom` projection for `@[simps]` lemmas.
-/
def Hom.Simps.hom (X Y : BddLat.{u}) (f : Hom X Y) :=
  f.hom

initialize_simps_projections Hom (hom' → hom)

@[simp]
/-
**BddLat.hom_id** 是 Mathlib 中的一个引理，位于命名空间 `BddLat`。
形式化陈述：hom_id {X : Lat} : (𝟙 X : X ⟶ X).hom = LatticeHom.id _
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma hom_id {X : Lat} : (𝟙 X : X ⟶ X).hom = LatticeHom.id _ := rfl

/- Provided for rewriting. -/
/-
**BddLat.id_apply** 是 Mathlib 中的一个引理，位于命名空间 `BddLat`。
形式化陈述：id_apply (X : Lat) (x : X) : (𝟙 X : X ⟶ X) x = x
参数：X : Lat；x : X。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
Provided for rewriting.
-/
lemma id_apply (X : Lat) (x : X) :
    (𝟙 X : X ⟶ X) x = x := by simp

@[simp]
/-
**BddLat.hom_comp** 是 Mathlib 中的一个引理，位于命名空间 `BddLat`。
形式化陈述：hom_comp {X Y Z : Lat} (f : X ⟶ Y) (g : Y ⟶ Z) : (f ≫ g).hom = g.hom.comp 
f.hom
参数：f : X ⟶ Y；g : Y ⟶ Z。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma hom_comp {X Y Z : Lat} (f : X ⟶ Y) (g : Y ⟶ Z) :
    (f ≫ g).hom = g.hom.comp f.hom := rfl

/- Provided for rewriting. -/
/-
**BddLat.comp_apply** 是 Mathlib 中的一个引理，位于命名空间 `BddLat`。
形式化陈述：comp_apply {X Y Z : Lat} (f : X ⟶ Y) (g : Y ⟶ Z) (x : X) : (f ≫ g) x = g (
f x)
参数：f : X ⟶ Y；g : Y ⟶ Z；x : X。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
Provided for rewriting.
-/
lemma comp_apply {X Y Z : Lat} (f : X ⟶ Y) (g : Y ⟶ Z) (x : X) :
    (f ≫ g) x = g (f x) := by simp

@[ext]
/-
**BddLat.ext** 是 Mathlib 中的一个引理，位于命名空间 `BddLat`。
形式化陈述：ext {X Y : BddLat} {f g : X ⟶ Y} (w : forall x : X, f x = g x) : f = g
参数：w : forall x : X, f x = g x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.ConcreteCategory.hom_ext`：hom_ext {X Y : C} (f g : X ⟶ Y)
 (w : forall x, f x = g x) : f = g
-/
lemma ext {X Y : BddLat} {f g : X ⟶ Y} (w : ∀ x : X, f x = g x) : f = g :=
  ConcreteCategory.hom_ext _ _ w

@[ext]
/-
**BddLat.hom_ext** 是 Mathlib 中的一个引理，位于命名空间 `BddLat`。
形式化陈述：hom_ext {X Y : BddLat} {f g : X ⟶ Y} (hf : f.hom = g.hom) : f = g
参数：hf : f.hom = g.hom。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `BddLat.Hom.ext`：∀ {X Y : BddLat} {x y : X.Hom Y}, x.hom' = y.hom' → x = 
y
-/
lemma hom_ext {X Y : BddLat} {f g : X ⟶ Y} (hf : f.hom = g.hom) : f = g :=
  Hom.ext hf
/-
**BddLat.hasForgetToBddOrd** 是 Mathlib 中的一个实例，位于命名空间 `BddLat`。
形式化陈述：hasForgetToBddOrd : HasForget₂ BddLat BddOrd where forget₂.obj X
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance hasForgetToBddOrd : HasForget₂ BddLat BddOrd where
  forget₂.obj X := .of X
  forget₂.map f := BddOrd.ofHom f.hom.toBoundedOrderHom
/-
**BddLat.hasForgetToLat** 是 Mathlib 中的一个实例，位于命名空间 `BddLat`。
形式化陈述：hasForgetToLat : HasForget₂ BddLat Lat where forget₂.obj X
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance hasForgetToLat : HasForget₂ BddLat Lat where
  forget₂.obj X := .of X
  forget₂.map f := Lat.ofHom f.hom.toLatticeHom
/-
**BddLat.hasForgetToSemilatSup** 是 Mathlib 中的一个实例，位于命名空间 `BddLat`。
形式化陈述：hasForgetToSemilatSup : HasForget₂ BddLat SemilatSupCat where forget₂.obj 
X
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance hasForgetToSemilatSup : HasForget₂ BddLat SemilatSupCat where
  forget₂.obj X := .of X
  forget₂.map f := f.hom.toSupBotHom
/-
**BddLat.hasForgetToSemilatInf** 是 Mathlib 中的一个实例，位于命名空间 `BddLat`。
形式化陈述：hasForgetToSemilatInf : HasForget₂ BddLat SemilatInfCat where forget₂.obj 
X
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance hasForgetToSemilatInf : HasForget₂ BddLat SemilatInfCat where
  forget₂.obj X := .of X
  forget₂.map f := f.hom.toInfTopHom

@[simp]
/-
**BddLat.coe_forget_to_bddOrd** 是 Mathlib 中的一个定理，位于命名空间 `BddLat`。
形式化陈述：coe_forget_to_bddOrd (X : BddLat) : ↥((forget₂ BddLat BddOrd).obj X) = ↥X
参数：X : BddLat。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_forget_to_bddOrd (X : BddLat) : ↥((forget₂ BddLat BddOrd).obj X) = ↥X :=
  rfl

@[simp]
/-
**BddLat.coe_forget_to_lat** 是 Mathlib 中的一个定理，位于命名空间 `BddLat`。
形式化陈述：coe_forget_to_lat (X : BddLat) : ↥((forget₂ BddLat Lat).obj X) = ↥X
参数：X : BddLat。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_forget_to_lat (X : BddLat) : ↥((forget₂ BddLat Lat).obj X) = ↥X :=
  rfl

@[simp]
/-
**BddLat.coe_forget_to_semilatSup** 是 Mathlib 中的一个定理，位于命名空间 `BddLat`。
形式化陈述：coe_forget_to_semilatSup (X : BddLat) : ↥((forget₂ BddLat SemilatSupCat).o
bj X) = ↥X
参数：X : BddLat。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_forget_to_semilatSup (X : BddLat) :
    ↥((forget₂ BddLat SemilatSupCat).obj X) = ↥X :=
  rfl

@[simp]
/-
**BddLat.coe_forget_to_semilatInf** 是 Mathlib 中的一个定理，位于命名空间 `BddLat`。
形式化陈述：coe_forget_to_semilatInf (X : BddLat) : ↥((forget₂ BddLat SemilatInfCat).o
bj X) = ↥X
参数：X : BddLat。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_forget_to_semilatInf (X : BddLat) :
    ↥((forget₂ BddLat SemilatInfCat).obj X) = ↥X :=
  rfl
/-
**BddLat.forget_lat_partOrd_eq_forget_bddOrd_partOrd** 是 Mathlib 中的一个定理，位于命名空间 `
BddLat`。
形式化陈述：forget_lat_partOrd_eq_forget_bddOrd_partOrd : forget₂ BddLat Lat ⋙ forget₂
 Lat PartOrd = forget₂ BddLat BddOrd ⋙ forget₂ BddOrd PartOrd
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem forget_lat_partOrd_eq_forget_bddOrd_partOrd :
    forget₂ BddLat Lat ⋙ forget₂ Lat PartOrd =
      forget₂ BddLat BddOrd ⋙ forget₂ BddOrd PartOrd :=
  rfl
/-
**BddLat.forget_semilatSup_partOrd_eq_forget_bddOrd_partOrd** 是 Mathlib 中的一个定理，位
于命名空间 `BddLat`。
形式化陈述：forget_semilatSup_partOrd_eq_forget_bddOrd_partOrd : forget₂ BddLat Semila
tSupCat ⋙ forget₂ SemilatSupCat PartOrd = forget₂ BddLat BddOrd ⋙ forget₂ BddOrd
 PartOrd
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem forget_semilatSup_partOrd_eq_forget_bddOrd_partOrd :
    forget₂ BddLat SemilatSupCat ⋙ forget₂ SemilatSupCat PartOrd =
      forget₂ BddLat BddOrd ⋙ forget₂ BddOrd PartOrd :=
  rfl
/-
**BddLat.forget_semilatInf_partOrd_eq_forget_bddOrd_partOrd** 是 Mathlib 中的一个定理，位
于命名空间 `BddLat`。
形式化陈述：forget_semilatInf_partOrd_eq_forget_bddOrd_partOrd : forget₂ BddLat Semila
tInfCat ⋙ forget₂ SemilatInfCat PartOrd = forget₂ BddLat BddOrd ⋙ forget₂ BddOrd
 PartOrd
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem forget_semilatInf_partOrd_eq_forget_bddOrd_partOrd :
    forget₂ BddLat SemilatInfCat ⋙ forget₂ SemilatInfCat PartOrd =
      forget₂ BddLat BddOrd ⋙ forget₂ BddOrd PartOrd :=
  rfl

/-- Constructs an equivalence between bounded lattices from an order isomorphism
between them. -/
@[simps]
/-
**BddLat.Iso.mk** 是 Mathlib 中的一个定义，位于命名空间 `BddLat.Iso`。
形式化陈述：{α β : BddLat} → ↑α.toLat ≃o ↑β.toLat → (α ≅ β)
参数：α ≅ β。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Constructs an equivalence between bounded lattices from an order isomorphism
between them.
-/
def Iso.mk {α β : BddLat.{u}} (e : α ≃o β) : α ≅ β where
  hom := ofHom e
  inv := ofHom e.symm
  hom_inv_id := by ext; exact e.symm_apply_apply _
  inv_hom_id := by ext; exact e.apply_symm_apply _

/-- `OrderDual` as a functor. -/
@[simps map]
/-
**BddLat.dual** 是 Mathlib 中的一个定义，位于命名空间 `BddLat`。
形式化陈述：dual : BddLat ⥤ BddLat where obj X
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`OrderDual` as a functor.
-/
def dual : BddLat ⥤ BddLat where
  obj X := of Xᵒᵈ
  map f := ofHom f.hom.dual

/-- The equivalence between `BddLat` and itself induced by `OrderDual` both ways. -/
@[simps functor inverse]
/-
**BddLat.dualEquiv** 是 Mathlib 中的一个定义，位于命名空间 `BddLat`。
形式化陈述：dualEquiv : BddLat ≌ BddLat where functor
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The equivalence between `BddLat` and itself induced by `OrderDual` both ways.
-/
def dualEquiv : BddLat ≌ BddLat where
  functor := dual
  inverse := dual
  unitIso := NatIso.ofComponents fun X => Iso.mk <| OrderIso.dualDual X
  counitIso := NatIso.ofComponents fun X => Iso.mk <| OrderIso.dualDual X

end BddLat

/-
**bddLat_dual_comp_forget_to_bddOrd** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：bddLat_dual_comp_forget_to_bddOrd : BddLat.dual ⋙ forget₂ BddLat BddOrd = 
forget₂ BddLat BddOrd ⋙ BddOrd.dual
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem bddLat_dual_comp_forget_to_bddOrd :
    BddLat.dual ⋙ forget₂ BddLat BddOrd =
    forget₂ BddLat BddOrd ⋙ BddOrd.dual :=
  rfl
/-
**bddLat_dual_comp_forget_to_lat** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：bddLat_dual_comp_forget_to_lat : BddLat.dual ⋙ forget₂ BddLat Lat = forget
₂ BddLat Lat ⋙ Lat.dual
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem bddLat_dual_comp_forget_to_lat :
    BddLat.dual ⋙ forget₂ BddLat Lat = forget₂ BddLat Lat ⋙ Lat.dual :=
  rfl
/-
**bddLat_dual_comp_forget_to_semilatSupCat** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：bddLat_dual_comp_forget_to_semilatSupCat : BddLat.dual ⋙ forget₂ BddLat Se
milatSupCat = forget₂ BddLat SemilatInfCat ⋙ SemilatInfCat.dual
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem bddLat_dual_comp_forget_to_semilatSupCat :
    BddLat.dual ⋙ forget₂ BddLat SemilatSupCat =
    forget₂ BddLat SemilatInfCat ⋙ SemilatInfCat.dual :=
  rfl
/-
**bddLat_dual_comp_forget_to_semilatInfCat** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：bddLat_dual_comp_forget_to_semilatInfCat : BddLat.dual ⋙ forget₂ BddLat Se
milatInfCat = forget₂ BddLat SemilatSupCat ⋙ SemilatSupCat.dual
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem bddLat_dual_comp_forget_to_semilatInfCat :
    BddLat.dual ⋙ forget₂ BddLat SemilatInfCat =
    forget₂ BddLat SemilatSupCat ⋙ SemilatSupCat.dual :=
  rfl

/-- The functor that adds a bottom and a top element to a lattice. This is the free functor. -/
/-
**latToBddLat** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：latToBddLat : Lat.{u} ⥤ BddLat where obj X
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The functor that adds a bottom and a top element to a lattice. This is the free 
functor.
-/
def latToBddLat : Lat.{u} ⥤ BddLat where
  obj X := .of <| WithTop <| WithBot X
  map f := BddLat.ofHom <| LatticeHom.withTopWithBot f.hom

/-- `latToBddLat` is left adjoint to the forgetful functor, meaning it is the free
functor from `Lat` to `BddLat`. -/
/-
**latToBddLatForgetAdjunction** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：latToBddLatForgetAdjunction : latToBddLat.{u} ⊣ forget₂ BddLat Lat
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`latToBddLat` is left adjoint to the forgetful functor, meaning it is the free
functor from `Lat` to `BddLat`.
-/
def latToBddLatForgetAdjunction : latToBddLat.{u} ⊣ forget₂ BddLat Lat :=
  Adjunction.mkOfHomEquiv
    { homEquiv X _ :=
        { toFun f := Lat.ofHom
            { toFun := f ∘ some ∘ some
              map_sup' := fun a b => (congr_arg f <| by rfl).trans (f.hom.map_sup' _ _)
              map_inf' := fun a b => (congr_arg f <| by rfl).trans (f.hom.map_inf' _ _) }
          invFun f := BddLat.ofHom <| LatticeHom.withTopWithBot' f.hom
          left_inv := fun f =>
            BddLat.ext fun a =>
              match a with
              | none => f.hom.map_top'.symm
              | some none => f.hom.map_bot'.symm
              | some (some _) => rfl }
      homEquiv_naturality_left_symm := fun _ _ =>
        BddLat.ext fun a =>
          match a with
          | none => rfl
          | some none => rfl
          | some (some _) => rfl
      homEquiv_naturality_right := fun _ _ => Lat.ext fun _ => rfl }

/-- `latToBddLat` and `OrderDual` commute. -/
/-
**latToBddLatCompDualIsoDualCompLatToBddLat** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：latToBddLatCompDualIsoDualCompLatToBddLat : latToBddLat.{u} ⋙ BddLat.dual 
≅ Lat.dual ⋙ latToBddLat
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`latToBddLat` and `OrderDual` commute.
-/
def latToBddLatCompDualIsoDualCompLatToBddLat :
    latToBddLat.{u} ⋙ BddLat.dual ≅ Lat.dual ⋙ latToBddLat :=
  Adjunction.leftAdjointUniq (latToBddLatForgetAdjunction.comp BddLat.dualEquiv.toAdjunction)
    (Lat.dualEquiv.toAdjunction.comp latToBddLatForgetAdjunction)
