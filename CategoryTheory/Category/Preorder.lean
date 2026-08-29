/-
Copyright (c) 2017 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Stephen Morgan, Kim Morrison, Johannes Hölzl, Reid Barton
-/
module

public import Mathlib.CategoryTheory.EqToHom
public import Mathlib.Order.Hom.Basic
public import Mathlib.Data.ULift

/-!

# Preorders as categories

We install a category instance on any preorder. This is not to be confused with the category _of_
preorders, defined in `Order.Category.Preorder`.

We show that monotone functions between preorders correspond to functors of the associated
categories.

## Main definitions

* `homOfLE` and `leOfHom` provide translations between inequalities in the preorder, and
  morphisms in the associated category.
* `Monotone.functor` is the functor associated to a monotone function.

-/

@[expose] public section


universe u v

namespace Preorder

open CategoryTheory

-- see Note [lower instance priority]
/--
The category structure coming from a preorder. There is a morphism `X ⟶ Y` if and only if `X ≤ Y`.

Because we don't allow morphisms to live in `Prop`,
we have to define `X ⟶ Y` as `ULift (PLift (X ≤ Y))`.
See `CategoryTheory.homOfLE` and `CategoryTheory.leOfHom`. -/
@[stacks 00D3]
instance (priority := 100) smallCategory (α : Type u) [Preorder α] : SmallCategory α where
  Hom U V := ULift (PLift (U <= V))
  id X := ⟨⟨le_refl X⟩⟩
  comp f g := ⟨⟨le_trans f.down.down g.down.down⟩⟩

/--
Instance `subsingleton_hom` / 实例 `subsingleton_hom`

English:
instance subsingleton_hom
  signature: {α : Type u} [Preorder α] (U V : α)
  body: ⟨fun _ _ => ULift.ext _ _ (Subsingleton.elim _ _ )⟩

中文:
实例 subsingleton_hom
  签名: {α : 类型u} [Preorder α] (U V : α)
  定义体: ⟨fun _ _ => ULift.ext _ _ (Subsingleton.elim _ _ )⟩

Depends on / 依赖: Subsingleton, Subsingleton.elim, ULift.ext
-/
instance subsingleton_hom {α : Type u} [Preorder α] (U V : α) : Subsingleton (U ⟶ V) :=
  ⟨fun _ _ => ULift.ext _ _ (Subsingleton.elim _ _ )⟩

end Preorder

namespace CategoryTheory

open Opposite

variable {X : Type u} [Preorder X]

/--
Definition of `homOfLE` / `homOfLE` 的定义

English:
definition homOfLE
  signature: {x y : X} (h : x <= y)
  body: ULift.up (PLift.up h)

@[inherit_doc homOfLE]

中文:
定义 homOfLE
  签名: {x y : X} (h : x <= y)
  定义体: ULift.up (PLift.up h)

@[inherit_doc homOfLE]

Depends on / 依赖: PLift.up, ULift.up
-/
def homOfLE {x y : X} (h : x <= y) : x ⟶ y :=
  ULift.up (PLift.up h)

@[inherit_doc homOfLE]
/--
Definition of `_root_.LE.le.hom` / `_root_.LE.le.hom` 的定义

English:
abbreviation _root_.LE.le.hom
  body: @homOfLE

@[simp]

中文:
缩写 _root_.LE.le.hom
  定义体: @homOfLE

@[simp]

Depends on / 依赖: homOfLE
-/
abbrev _root_.LE.le.hom := @homOfLE

@[simp]
/--
theorem `homOfLE_refl` / 定理 `homOfLE_refl`

English:
theorem homOfLE_refl
  given: {x : X} (h : x <= x)
  statement: h.hom = 𝟙 x
  proof: rfl

@[simp]

中文:
定理 homOfLE_refl
  条件: {x : X} (h : x <= x)
  结论: h.hom = 𝟙 x
  证明: rfl

@[simp]
-/
theorem homOfLE_refl {x : X} (h : x <= x) : h.hom = 𝟙 x :=
  rfl

@[simp]
/--
theorem `homOfLE_comp` / 定理 `homOfLE_comp`

English:
theorem homOfLE_comp
  given: {x y z : X} (h : x <= y) (k : y <= z)
  proof: rfl

中文:
定理 homOfLE_comp
  条件: {x y z : X} (h : x <= y) (k : y <= z)
  证明: rfl
-/
theorem homOfLE_comp {x y z : X} (h : x <= y) (k : y <= z) :
    homOfLE h ≫ homOfLE k = homOfLE (h.trans k) :=
  rfl

/--
theorem `leOfHom` / 定理 `leOfHom`

English:
theorem leOfHom
  given: {x y : X} (h : x ⟶ y)
  statement: x <= y
  proof: h.down.down

中文:
定理 leOfHom
  条件: {x y : X} (h : x ⟶ y)
  结论: x <= y
  证明: h.down.down

Depends on / 依赖: h.down.down
-/
theorem leOfHom {x y : X} (h : x ⟶ y) : x <= y :=
  h.down.down

set_option linter.defProp false in
@[inherit_doc leOfHom]
/--
Definition of `_root_.Quiver.Hom.le` / `_root_.Quiver.Hom.le` 的定义

English:
abbreviation _root_.Quiver.Hom.le
  body: @leOfHom

@[simp]

中文:
缩写 _root_.Quiver.Hom.le
  定义体: @leOfHom

@[simp]

Depends on / 依赖: leOfHom
-/
abbrev _root_.Quiver.Hom.le := @leOfHom

@[simp]
/--
theorem `homOfLE_leOfHom` / 定理 `homOfLE_leOfHom`

English:
theorem homOfLE_leOfHom
  given: {x y : X} (h : x ⟶ y)
  statement: h.le.hom = h
  proof: rfl

中文:
定理 homOfLE_leOfHom
  条件: {x y : X} (h : x ⟶ y)
  结论: h.le.hom = h
  证明: rfl
-/
theorem homOfLE_leOfHom {x y : X} (h : x ⟶ y) : h.le.hom = h :=
  rfl

/--
lemma `homOfLE_isIso_of_eq` / 引理 `homOfLE_isIso_of_eq`

English:
lemma homOfLE_isIso_of_eq
  given: {x y : X} (h : x <= y) (heq : x = y)
  proof: ⟨homOfLE (le_of_eq heq.symm), by simp⟩

中文:
引理 homOfLE_isIso_of_eq
  条件: {x y : X} (h : x <= y) (heq : x = y)
  证明: ⟨homOfLE (le_of_eq heq.symm), by simp⟩

Depends on / 依赖: heq.symm, homOfLE, le_of_eq
-/
lemma homOfLE_isIso_of_eq {x y : X} (h : x <= y) (heq : x = y) :
    IsIso (homOfLE h) :=
  ⟨homOfLE (le_of_eq heq.symm), by simp⟩

/--
lemma `isIso_homOfLE` / 引理 `isIso_homOfLE`

English:
lemma isIso_homOfLE
  given: {x y : X} (h : x = y)
  proof: by
  subst h
  change IsIso (𝟙 _)
  infer_instance

@[simp, reassoc]

中文:
引理 isIso_homOfLE
  条件: {x y : X} (h : x = y)
  证明: by
  subst h
  change IsIso (𝟙 _)
  infer_instance

@[simp, reassoc]

Depends on / 依赖: infer_instance
-/
lemma isIso_homOfLE {x y : X} (h : x = y) :
    IsIso (homOfLE (by rw [h]) : x ⟶ y) := by
  subst h
  change IsIso (𝟙 _)
  infer_instance

@[simp, reassoc]
/--
lemma `homOfLE_comp_eqToHom` / 引理 `homOfLE_comp_eqToHom`

English:
lemma homOfLE_comp_eqToHom
  given: {a b c : X} (hab : a <= b) (hbc : b = c)
  proof: rfl

@[simp, reassoc]

中文:
引理 homOfLE_comp_eqToHom
  条件: {a b c : X} (hab : a <= b) (hbc : b = c)
  证明: rfl

@[simp, reassoc]
-/
lemma homOfLE_comp_eqToHom {a b c : X} (hab : a <= b) (hbc : b = c) :
    homOfLE hab ≫ eqToHom hbc = homOfLE (hab.trans (le_of_eq hbc)) :=
  rfl

@[simp, reassoc]
/--
lemma `eqToHom_comp_homOfLE` / 引理 `eqToHom_comp_homOfLE`

English:
lemma eqToHom_comp_homOfLE
  given: {a b c : X} (hab : a = b) (hbc : b <= c)
  proof: rfl

@[simp, reassoc]

中文:
引理 eqToHom_comp_homOfLE
  条件: {a b c : X} (hab : a = b) (hbc : b <= c)
  证明: rfl

@[simp, reassoc]
-/
lemma eqToHom_comp_homOfLE {a b c : X} (hab : a = b) (hbc : b <= c) :
    eqToHom hab ≫ homOfLE hbc = homOfLE ((le_of_eq hab).trans hbc) :=
  rfl

@[simp, reassoc]
/--
lemma `homOfLE_op_comp_eqToHom` / 引理 `homOfLE_op_comp_eqToHom`

English:
lemma homOfLE_op_comp_eqToHom
  given: {a b c : X} (hab : b <= a) (hbc : op b = op c)
  proof: rfl

@[simp, reassoc]

中文:
引理 homOfLE_op_comp_eqToHom
  条件: {a b c : X} (hab : b <= a) (hbc : op b = op c)
  证明: rfl

@[simp, reassoc]
-/
lemma homOfLE_op_comp_eqToHom {a b c : X} (hab : b <= a) (hbc : op b = op c) :
    (homOfLE hab).op ≫ eqToHom hbc = (homOfLE ((le_of_eq (op_injective hbc.symm)).trans hab)).op :=
  rfl

@[simp, reassoc]
/--
lemma `eqToHom_comp_homOfLE_op` / 引理 `eqToHom_comp_homOfLE_op`

English:
lemma eqToHom_comp_homOfLE_op
  given: {a b c : X} (hab : op a = op b) (hbc : c <= b)
  proof: rfl

中文:
引理 eqToHom_comp_homOfLE_op
  条件: {a b c : X} (hab : op a = op b) (hbc : c <= b)
  证明: rfl
-/
lemma eqToHom_comp_homOfLE_op {a b c : X} (hab : op a = op b) (hbc : c <= b) :
    eqToHom hab ≫ (homOfLE hbc).op = (homOfLE (hbc.trans (le_of_eq (op_injective hab.symm)))).op :=
  rfl

/--
Definition of `opHomOfLE` / `opHomOfLE` 的定义

English:
definition opHomOfLE
  signature: {x y : Xᵒᵖ} (h : unop x <= unop y)
  body: (homOfLE h).op

中文:
定义 opHomOfLE
  签名: {x y : Xᵒᵖ} (h : unop x <= unop y)
  定义体: (homOfLE h).op

Depends on / 依赖: homOfLE
-/
def opHomOfLE {x y : Xᵒᵖ} (h : unop x <= unop y) : y ⟶ x :=
  (homOfLE h).op

/--
theorem `le_of_op_hom` / 定理 `le_of_op_hom`

English:
theorem le_of_op_hom
  given: {x y : Xᵒᵖ} (h : x ⟶ y)
  statement: unop y <= unop x
  proof: h.unop.le

中文:
定理 le_of_op_hom
  条件: {x y : Xᵒᵖ} (h : x ⟶ y)
  结论: unop y <= unop x
  证明: h.unop.le

Depends on / 依赖: h.unop.le
-/
theorem le_of_op_hom {x y : Xᵒᵖ} (h : x ⟶ y) : unop y <= unop x :=
  h.unop.le

/--
Instance `uniqueToTop` / 实例 `uniqueToTop`

English:
instance uniqueToTop
  signature: [OrderTop X] {x : X}
  body: homOfLE le_top
  uniq := fun a => by rfl

中文:
实例 uniqueToTop
  签名: [OrderTop X] {x : X}
  定义体: homOfLE le_top
  uniq := fun a => by rfl

Depends on / 依赖: homOfLE, le_top
-/
instance uniqueToTop [OrderTop X] {x : X} : Unique (x ⟶ ⊤) where
  default := homOfLE le_top
  uniq := fun a => by rfl

/--
Instance `uniqueFromBot` / 实例 `uniqueFromBot`

English:
instance uniqueFromBot
  signature: [OrderBot X] {x : X}
  body: homOfLE bot_le
  uniq := fun a => by rfl

中文:
实例 uniqueFromBot
  签名: [OrderBot X] {x : X}
  定义体: homOfLE bot_le
  uniq := fun a => by rfl

Depends on / 依赖: bot_le, homOfLE
-/
instance uniqueFromBot [OrderBot X] {x : X} : Unique (⊥ ⟶ x) where
  default := homOfLE bot_le
  uniq := fun a => by rfl

variable (X) in
/-- The equivalence of categories from the order dual of a preordered type `X`
to the opposite category of the preorder `X`. -/
@[simps]
/--
Definition of `orderDualEquivalence` / `orderDualEquivalence` 的定义

English:
definition orderDualEquivalence
  signature: : Xᵒᵈ ≌ Xᵒᵖ where
  body: { obj := fun x => op (OrderDual.ofDual x)
      map := fun f => (homOfLE (leOfHom f)).op }
  inverse :=
    { obj := fun x => OrderDual.toDual x.unop
      map := fun f => (homOfLE (leOfHom f.unop)) }
  unitIso := Iso.refl _
  counitIso := Iso.refl _

中文:
定义 orderDualEquivalence
  签名: : Xᵒᵈ ≌ Xᵒᵖ where
  定义体: { obj := fun x => op (OrderDual.ofDual x)
      map := fun f => (homOfLE (leOfHom f)).op }
  inverse :=
    { obj := fun x => OrderDual.toDual x.unop
      map := fun f => (homOfLE (leOfHom f.unop)) }
  unitIso := Iso.refl _
  counitIso := Iso.refl _

Depends on / 依赖: Iso.refl, OrderDual, OrderDual.ofDual, OrderDual.toDual, counitIso, f.unop, homOfLE, inverse, leOfHom, ofDual, toDual, unitIso, x.unop
-/
def orderDualEquivalence : Xᵒᵈ ≌ Xᵒᵖ where
  functor :=
    { obj := fun x => op (OrderDual.ofDual x)
      map := fun f => (homOfLE (leOfHom f)).op }
  inverse :=
    { obj := fun x => OrderDual.toDual x.unop
      map := fun f => (homOfLE (leOfHom f.unop)) }
  unitIso := Iso.refl _
  counitIso := Iso.refl _

end CategoryTheory

section

open CategoryTheory

variable {X : Type u} {Y : Type v} [Preorder X] [Preorder Y]

/--
Definition of `Monotone.functor` / `Monotone.functor` 的定义

English:
definition Monotone.functor
  signature: {f : X -> Y} (h : Monotone f)
  body: f
  map g := CategoryTheory.homOfLE (h g.le)

@[simp]

中文:
定义 Monotone.functor
  签名: {f : X -> Y} (h : Monotone f)
  定义体: f
  map g := CategoryTheory.homOfLE (h g.le)

@[simp]
-/
def Monotone.functor {f : X -> Y} (h : Monotone f) : X ⥤ Y where
  obj := f
  map g := CategoryTheory.homOfLE (h g.le)

@[simp]
/--
theorem `Monotone.functor_obj` / 定理 `Monotone.functor_obj`

English:
theorem Monotone.functor_obj
  given: {f : X -> Y} (h : Monotone f)
  statement: h.functor.obj = f
  proof: rfl

中文:
定理 Monotone.functor_obj
  条件: {f : X -> Y} (h : Monotone f)
  结论: h.functor.obj = f
  证明: rfl
-/
theorem Monotone.functor_obj {f : X -> Y} (h : Monotone f) : h.functor.obj = f :=
  rfl

-- Faithfulness is automatic because preorder categories are thin
instance (f : X ↪o Y) : f.monotone.functor.Full where
  map_surjective h := ⟨homOfLE (f.map_rel_iff.1 h.le), rfl⟩

/-- The equivalence of categories `X ≌ Y` induced by `e : X ≃o Y`. -/
@[simps]
/--
Definition of `OrderIso.equivalence` / `OrderIso.equivalence` 的定义

English:
definition OrderIso.equivalence
  signature: (e : X ≃o Y)
  body: e.monotone.functor
  inverse := e.symm.monotone.functor
  unitIso := NatIso.ofComponents (fun _ => eqToIso (by simp))
  counitIso := NatIso.ofComponents (fun _ => eqToIso (by simp))

中文:
定义 OrderIso.equivalence
  签名: (e : X ≃o Y)
  定义体: e.monotone.functor
  inverse := e.symm.monotone.functor
  unitIso := NatIso.ofComponents (fun _ => eqToIso (by simp))
  counitIso := NatIso.ofComponents (fun _ => eqToIso (by simp))

Depends on / 依赖: e.monotone.functor, functor, monotone
-/
def OrderIso.equivalence (e : X ≃o Y) : X ≌ Y where
  functor := e.monotone.functor
  inverse := e.symm.monotone.functor
  unitIso := NatIso.ofComponents (fun _ => eqToIso (by simp))
  counitIso := NatIso.ofComponents (fun _ => eqToIso (by simp))

end

section Preorder

variable {X : Type u} {Y : Type v} [Preorder X] [Preorder Y]

namespace CategoryTheory.Functor

/-- A functor between preorder categories is monotone. -/
@[gcongr, mono]
/--
theorem `monotone` / 定理 `monotone`

English:
theorem monotone
  given: (f : X ⥤ Y)
  statement: Monotone f.obj
  proof: fun _ _ hxy => (f.map hxy.hom).le

中文:
定理 monotone
  条件: (f : X ⥤ Y)
  结论: Monotone f.obj
  证明: fun _ _ hxy => (f.map hxy.hom).le

Depends on / 依赖: f.map, hxy.hom
-/
theorem monotone (f : X ⥤ Y) : Monotone f.obj := fun _ _ hxy => (f.map hxy.hom).le

/-- A functor `X ⥤ Y` between preorder categories as an `OrderHom`. -/
@[simps!]
/--
Definition of `toOrderHom` / `toOrderHom` 的定义

English:
definition toOrderHom
  signature: (F : X ⥤ Y)
  body: F.obj
  monotone' := F.monotone

中文:
定义 toOrderHom
  签名: (F : X ⥤ Y)
  定义体: F.obj
  monotone' := F.monotone

Depends on / 依赖: F.obj
-/
def toOrderHom (F : X ⥤ Y) : X ->o Y where
  toFun := F.obj
  monotone' := F.monotone

end CategoryTheory.Functor

namespace OrderHom

open CategoryTheory

/--
Definition of `toFunctor` / `toFunctor` 的定义

English:
abbreviation toFunctor
  signature: (f : X ->o Y)
  body: f.monotone.functor

中文:
缩写 toFunctor
  签名: (f : X ->o Y)
  定义体: f.monotone.functor

Depends on / 依赖: f.monotone.functor, functor, monotone
-/
abbrev toFunctor (f : X ->o Y) : X ⥤ Y := f.monotone.functor

/-- The equivalence between `X →o Y` and the type of functors `X ⥤ Y` between preorder categories
`X` and `Y`. -/
@[simps]
/--
Definition of `equivFunctor` / `equivFunctor` 的定义

English:
definition equivFunctor
  signature: : (X ->o Y) ≃ (X ⥤ Y) where
  body: toFunctor
  invFun F := F.toOrderHom

中文:
定义 equivFunctor
  签名: : (X ->o Y) ≃ (X ⥤ Y) where
  定义体: toFunctor
  invFun F := F.toOrderHom

Depends on / 依赖: toFunctor
-/
def equivFunctor : (X ->o Y) ≃ (X ⥤ Y) where
  toFun := toFunctor
  invFun F := F.toOrderHom

/-- The categorical equivalence between the category of monotone functions `X →o Y` and the category
of functors `X ⥤ Y`, where `X` and `Y` are preorder categories. -/
@[simps! functor_obj_obj inverse_obj unitIso_hom_app unitIso_inv_app counitIso_inv_app_app
  counitIso_hom_app_app]
/--
Definition of `equivalenceFunctor` / `equivalenceFunctor` 的定义

English:
definition equivalenceFunctor
  signature: : (X ->o Y) ≌ (X ⥤ Y) where
  body: { obj f := f.toFunctor
      map f := { app x := homOfLE <| leOfHom f x } }
  inverse :=
    { obj F := F.toOrderHom
map f := homOfLE fun x => leOfHom f.app x }
  unitIso := Iso.refl _
  counitIso := Iso.refl _

中文:
定义 equivalenceFunctor
  签名: : (X ->o Y) ≌ (X ⥤ Y) where
  定义体: { obj f := f.toFunctor
      map f := { app x := homOfLE <| leOfHom f x } }
  inverse :=
    { obj F := F.toOrderHom
map f := homOfLE fun x => leOfHom f.app x }
  unitIso := Iso.refl _
  counitIso := Iso.refl _

Depends on / 依赖: F.toOrderHom, Iso.refl, counitIso, f.app, f.toFunctor, homOfLE, inverse, leOfHom, toFunctor, toOrderHom, unitIso
-/
def equivalenceFunctor : (X ->o Y) ≌ (X ⥤ Y) where
  functor :=
    { obj f := f.toFunctor
      map f := { app x := homOfLE <| leOfHom f x } }
  inverse :=
    { obj F := F.toOrderHom
map f := homOfLE fun x => leOfHom f.app x }
  unitIso := Iso.refl _
  counitIso := Iso.refl _

end OrderHom

end Preorder

section PartialOrder

namespace CategoryTheory

variable {X : Type u} {Y : Type v} [PartialOrder X] [PartialOrder Y]

/--
theorem `Iso.to_eq` / 定理 `Iso.to_eq`

English:
theorem Iso.to_eq
  given: {x y : X} (f : x ≅ y)
  statement: x = y
  proof: le_antisymm f.hom.le f.inv.le

中文:
定理 Iso.to_eq
  条件: {x y : X} (f : x ≅ y)
  结论: x = y
  证明: le_antisymm f.hom.le f.inv.le

Depends on / 依赖: f.hom.le, f.inv.le, le_antisymm
-/
theorem Iso.to_eq {x y : X} (f : x ≅ y) : x = y :=
  le_antisymm f.hom.le f.inv.le

/--
Definition of `Equivalence.toOrderIso` / `Equivalence.toOrderIso` 的定义

English:
definition Equivalence.toOrderIso
  signature: (e : X ≌ Y)
  body: e.functor.obj
  invFun := e.inverse.obj
  left_inv a := (e.unitIso.app a).to_eq.symm
  right_inv b := (e.counitIso.app b).to_eq
  map_rel_iff' {a a'} :=
    ⟨fun h =>
      ((Equivalence.unit e).app a ≫ e.inverse.map h.hom ≫ (Equivalence.unitInv e).app a').le,
      fun h : a <= a' => (e.functor.map

中文:
定义 Equivalence.toOrderIso
  签名: (e : X ≌ Y)
  定义体: e.functor.obj
  invFun := e.inverse.obj
  left_inv a := (e.unitIso.app a).to_eq.symm
  right_inv b := (e.counitIso.app b).to_eq
  map_rel_iff' {a a'} :=
    ⟨fun h =>
      ((Equivalence.unit e).app a ≫ e.inverse.map h.hom ≫ (Equivalence.unitInv e).app a').le,
      fun h : a <= a' => (e.functor.map

Depends on / 依赖: e.functor.obj, functor
-/
def Equivalence.toOrderIso (e : X ≌ Y) : X ≃o Y where
  toFun := e.functor.obj
  invFun := e.inverse.obj
  left_inv a := (e.unitIso.app a).to_eq.symm
  right_inv b := (e.counitIso.app b).to_eq
  map_rel_iff' {a a'} :=
    ⟨fun h =>
      ((Equivalence.unit e).app a ≫ e.inverse.map h.hom ≫ (Equivalence.unitInv e).app a').le,
      fun h : a <= a' => (e.functor.map h.hom).le⟩

-- `@[simps]` on `Equivalence.toOrderIso` produces lemmas that fail the `simpNF` linter,
-- so we provide them by hand:
@[simp]
/--
theorem `Equivalence.toOrderIso_apply` / 定理 `Equivalence.toOrderIso_apply`

English:
theorem Equivalence.toOrderIso_apply
  given: (e : X ≌ Y) (x : X)
  statement: e.toOrderIso x = e.functor.obj x
  proof: rfl

@[simp]

中文:
定理 Equivalence.toOrderIso_apply
  条件: (e : X ≌ Y) (x : X)
  结论: e.toOrderIso x = e.functor.obj x
  证明: rfl

@[simp]
-/
theorem Equivalence.toOrderIso_apply (e : X ≌ Y) (x : X) : e.toOrderIso x = e.functor.obj x :=
  rfl

@[simp]
/--
theorem `Equivalence.toOrderIso_symm_apply` / 定理 `Equivalence.toOrderIso_symm_apply`

English:
theorem Equivalence.toOrderIso_symm_apply
  given: (e : X ≌ Y) (y : Y)
  proof: rfl

中文:
定理 Equivalence.toOrderIso_symm_apply
  条件: (e : X ≌ Y) (y : Y)
  证明: rfl
-/
theorem Equivalence.toOrderIso_symm_apply (e : X ≌ Y) (y : Y) :
    e.toOrderIso.symm y = e.inverse.obj y :=
  rfl

end CategoryTheory

end PartialOrder

open CategoryTheory

/--
lemma `PartialOrder.isIso_iff_eq` / 引理 `PartialOrder.isIso_iff_eq`

English:
lemma PartialOrder.isIso_iff_eq
  statement: {X : Type u} [PartialOrder X]
  proof: by
  constructor
  · intro _
    exact (asIso f).to_eq
  · rintro rfl
    rw [Subsingleton.elim f (𝟙 _)]
    infer_instance

中文:
引理 PartialOrder.isIso_iff_eq
  结论: {X : 类型u} [PartialOrder X]
  证明: by
  constructor
  · intro _
    exact (asIso f).to_eq
  · rintro rfl
    rw [Subsingleton.elim f (𝟙 _)]
    infer_instance

Depends on / 依赖: Subsingleton, Subsingleton.elim, infer_instance, to_eq
-/
lemma PartialOrder.isIso_iff_eq {X : Type u} [PartialOrder X]
    {a b : X} (f : a ⟶ b) : IsIso f ↔ a = b := by
  constructor
  · intro _
    exact (asIso f).to_eq
  · rintro rfl
    rw [Subsingleton.elim f (𝟙 _)]
    infer_instance
