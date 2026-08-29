/-
Copyright (c) 2025 Sina Hazratpour. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sina Hazratpour
-/
module

public import Mathlib.CategoryTheory.Monoidal.Braided.Basic
public import Mathlib.CategoryTheory.Monoidal.Closed.Basic

/-!
# The pointwise monoidal structure on the product of families of monoidal categories

Given a family of monoidal categories `C i`, we define a monoidal structure on
`Π i, C i` where the tensor product is defined pointwise.

-/

@[expose] public section

universe w₁ v₁ v₂ u₁ u₂

namespace CategoryTheory

namespace Pi

open Category MonoidalCategory

variable {I : Type w₁} {C : I -> Type u₁} [forall i, Category.{v₁} (C i)]
  [forall i, MonoidalCategory (C i)]

@[simps tensorObj tensorHom whiskerLeft whiskerRight tensorUnit]
/--
Instance `monoidalCategoryStruct` / 实例 `monoidalCategoryStruct`

English:
instance monoidalCategoryStruct
  signature: : MonoidalCategoryStruct (forall i, C i) where
  body: X i otimes Y i
  tensorHom f g i := f i otimesₘ g i
  whiskerLeft X _ _ f i := X i ◁ f i
  whiskerRight f Y i := f i ▷ Y i
  tensorUnit i := 𝟙_ (C i)
  leftUnitor X := isoMk (fun i => fun_ (X i))
  rightUnitor X := isoMk (fun i => ρ_ (X i))
  associator X Y Z := isoMk (fun i => α_ (X i) (Y i) (Z i))

@[simp]

中文:
实例 monoidalCategoryStruct
  签名: : 幺半群范畴结构 (对任意 i, C i) where
  定义体: X i otimes Y i
  tensorHom f g i := f i otimesₘ g i
  whiskerLeft X _ _ f i := X i ◁ f i
  whiskerRight f Y i := f i ▷ Y i
  tensorUnit i := 𝟙_ (C i)
  leftUnitor X := isoMk (fun i => fun_ (X i))
  rightUnitor X := isoMk (fun i => ρ_ (X i))
  associator X Y Z := isoMk (fun i => α_ (X i) (Y i) (Z i))

@[simp]

Depends on / 依赖: otimes
-/
instance monoidalCategoryStruct : MonoidalCategoryStruct (forall i, C i) where
  tensorObj X Y i := X i otimes Y i
  tensorHom f g i := f i otimesₘ g i
  whiskerLeft X _ _ f i := X i ◁ f i
  whiskerRight f Y i := f i ▷ Y i
  tensorUnit i := 𝟙_ (C i)
  leftUnitor X := isoMk (fun i => fun_ (X i))
  rightUnitor X := isoMk (fun i => ρ_ (X i))
  associator X Y Z := isoMk (fun i => α_ (X i) (Y i) (Z i))

@[simp]
/--
theorem `associator_hom_apply` / 定理 `associator_hom_apply`

English:
theorem associator_hom_apply
  given: {X Y Z : forall i, C i} {i : I}
  proof: rfl

@[simp]

中文:
定理 associator_hom_apply
  条件: {X Y Z : 对任意 i, C i} {i : I}
  证明: rfl

@[simp]
-/
theorem associator_hom_apply {X Y Z : forall i, C i} {i : I} :
    (α_ X Y Z).hom i = (α_ (X i) (Y i) (Z i)).hom := rfl

@[simp]
/--
theorem `associator_inv_apply` / 定理 `associator_inv_apply`

English:
theorem associator_inv_apply
  given: {X Y Z : forall i, C i} {i : I}
  proof: rfl

@[simp]

中文:
定理 associator_inv_apply
  条件: {X Y Z : 对任意 i, C i} {i : I}
  证明: rfl

@[simp]
-/
theorem associator_inv_apply {X Y Z : forall i, C i} {i : I} :
    (α_ X Y Z).inv i = (α_ (X i) (Y i) (Z i)).inv := rfl

@[simp]
/--
theorem `isoApp_associator` / 定理 `isoApp_associator`

English:
theorem isoApp_associator
  given: {X Y Z : forall i, C i} {i : I}
  proof: rfl

@[simp]

中文:
定理 isoApp_associator
  条件: {X Y Z : 对任意 i, C i} {i : I}
  证明: rfl

@[simp]
-/
theorem isoApp_associator {X Y Z : forall i, C i} {i : I} :
    isoApp (α_ X Y Z) i = α_ (X i) (Y i) (Z i) := rfl

@[simp]
/--
theorem `left_unitor_hom_apply` / 定理 `left_unitor_hom_apply`

English:
theorem left_unitor_hom_apply
  given: {X : forall i, C i} {i : I}
  proof: rfl

@[simp]

中文:
定理 left_unitor_hom_apply
  条件: {X : 对任意 i, C i} {i : I}
  证明: rfl

@[simp]
-/
theorem left_unitor_hom_apply {X : forall i, C i} {i : I} :
    (fun_ X).hom i = (fun_ (X i)).hom := rfl

@[simp]
/--
theorem `left_unitor_inv_apply` / 定理 `left_unitor_inv_apply`

English:
theorem left_unitor_inv_apply
  given: {X : forall i, C i} {i : I}
  proof: rfl

@[simp]

中文:
定理 left_unitor_inv_apply
  条件: {X : 对任意 i, C i} {i : I}
  证明: rfl

@[simp]
-/
theorem left_unitor_inv_apply {X : forall i, C i} {i : I} :
    (fun_ X).inv i = (fun_ (X i)).inv := rfl

@[simp]
/--
theorem `isoApp_left_unitor` / 定理 `isoApp_left_unitor`

English:
theorem isoApp_left_unitor
  given: {X : forall i, C i} {i : I}
  proof: rfl

@[simp]

中文:
定理 isoApp_left_unitor
  条件: {X : 对任意 i, C i} {i : I}
  证明: rfl

@[simp]
-/
theorem isoApp_left_unitor {X : forall i, C i} {i : I} :
    isoApp (fun_ X) i = fun_ (X i) := rfl

@[simp]
/--
theorem `right_unitor_hom_apply` / 定理 `right_unitor_hom_apply`

English:
theorem right_unitor_hom_apply
  given: {X : forall i, C i} {i : I}
  proof: rfl

@[simp]

中文:
定理 right_unitor_hom_apply
  条件: {X : 对任意 i, C i} {i : I}
  证明: rfl

@[simp]
-/
theorem right_unitor_hom_apply {X : forall i, C i} {i : I} :
    (ρ_ X).hom i = (ρ_ (X i)).hom := rfl

@[simp]
/--
theorem `right_unitor_inv_apply` / 定理 `right_unitor_inv_apply`

English:
theorem right_unitor_inv_apply
  given: {X : forall i, C i} {i : I}
  proof: rfl

@[simp]

中文:
定理 right_unitor_inv_apply
  条件: {X : 对任意 i, C i} {i : I}
  证明: rfl

@[simp]
-/
theorem right_unitor_inv_apply {X : forall i, C i} {i : I} :
    (ρ_ X).inv i = (ρ_ (X i)).inv := rfl

@[simp]
/--
theorem `isoApp_right_unitor` / 定理 `isoApp_right_unitor`

English:
theorem isoApp_right_unitor
  given: {X : forall i, C i} {i : I}
  proof: rfl

中文:
定理 isoApp_right_unitor
  条件: {X : 对任意 i, C i} {i : I}
  证明: rfl
-/
theorem isoApp_right_unitor {X : forall i, C i} {i : I} :
    isoApp (ρ_ X) i = ρ_ (X i) := rfl

/--
Instance `monoidalCategory` / 实例 `monoidalCategory`

English:
instance monoidalCategory
  signature: : MonoidalCategory.{max w₁ v₁} (forall i, C i) where
  body: by ext i; simp [tensorHom_def, whiskerLeft]

中文:
实例 monoidalCategory
  签名: : 幺半群范畴.{最大值 w₁ v₁} (对任意 i, C i) where
  定义体: by ext i; simp [tensorHom_def, whiskerLeft]

Depends on / 依赖: tensorHom_def, whiskerLeft
-/
instance monoidalCategory : MonoidalCategory.{max w₁ v₁} (forall i, C i) where
  tensorHom_def {A B X Y} f g := by ext i; simp [tensorHom_def, whiskerLeft]

section BraidedCategory

open CategoryTheory.BraidedCategory

variable [forall i, BraidedCategory (C i)]

/--
Instance `braidedCategory` / 实例 `braidedCategory`

English:
instance braidedCategory
  signature: : BraidedCategory (forall i, C i) where
  body: isoMk fun i => β_ (X i) (Y i)
  hexagon_forward X Y Z := by ext i; apply hexagon_forward
  hexagon_reverse X Y Z := by ext i; apply hexagon_reverse

@[simp]

中文:
实例 braidedCategory
  签名: : 辫范畴 (对任意 i, C i) where
  定义体: isoMk fun i => β_ (X i) (Y i)
  hexagon_forward X Y Z := by ext i; apply hexagon_forward
  hexagon_reverse X Y Z := by ext i; apply hexagon_reverse

@[simp]
-/
instance braidedCategory : BraidedCategory (forall i, C i) where
  braiding X Y := isoMk fun i => β_ (X i) (Y i)
  hexagon_forward X Y Z := by ext i; apply hexagon_forward
  hexagon_reverse X Y Z := by ext i; apply hexagon_reverse

@[simp]
/--
theorem `braiding_hom_apply` / 定理 `braiding_hom_apply`

English:
theorem braiding_hom_apply
  given: {X Y : forall i, C i} {i : I}
  proof: rfl

@[simp]

中文:
定理 braiding_hom_apply
  条件: {X Y : 对任意 i, C i} {i : I}
  证明: rfl

@[simp]
-/
theorem braiding_hom_apply {X Y : forall i, C i} {i : I} :
    (β_ X Y).hom i = (β_ (X i) (Y i)).hom := rfl

@[simp]
/--
theorem `braiding_inv_apply` / 定理 `braiding_inv_apply`

English:
theorem braiding_inv_apply
  given: {X Y : forall i, C i} {i : I}
  proof: rfl

@[simp]

中文:
定理 braiding_inv_apply
  条件: {X Y : 对任意 i, C i} {i : I}
  证明: rfl

@[simp]
-/
theorem braiding_inv_apply {X Y : forall i, C i} {i : I} :
    (β_ X Y).inv i = (β_ (X i) (Y i)).inv := rfl

@[simp]
/--
theorem `isoApp_braiding` / 定理 `isoApp_braiding`

English:
theorem isoApp_braiding
  given: {X Y : forall i, C i} {i : I}
  proof: rfl

中文:
定理 isoApp_braiding
  条件: {X Y : 对任意 i, C i} {i : I}
  证明: rfl
-/
theorem isoApp_braiding {X Y : forall i, C i} {i : I} :
    isoApp (β_ X Y) i = β_ (X i) (Y i) := rfl

end BraidedCategory

section SymmetricCategory

open CategoryTheory.SymmetricCategory

variable [forall i, SymmetricCategory (C i)]

/--
Instance `symmetricCategory` / 实例 `symmetricCategory`

English:
instance symmetricCategory
  signature: : SymmetricCategory (forall i, C i) where
  body: by ext i; apply symmetry

中文:
实例 symmetricCategory
  签名: : 对称范畴 (对任意 i, C i) where
  定义体: by ext i; apply symmetry

Depends on / 依赖: symmetry
-/
instance symmetricCategory : SymmetricCategory (forall i, C i) where
  symmetry X Y := by ext i; apply symmetry

end SymmetricCategory

section Closed

open ihom

variable {I : Type w₁} {C : I -> Type u₁} [forall i, Category.{v₁} (C i)]
  [forall i, MonoidalCategory (C i)] [forall i, MonoidalClosed (C i)]

/-- The internal hom functor `X ⟶[∀ i, C i] -` -/
@[simps!]
/--
Definition of `ihom` / `ihom` 的定义

English:
definition ihom
  signature: (X : forall i, C i)
  body: fun i => (X i ⟶[C i] Y i)
  map {Y Z} f := fun i => (CategoryTheory.ihom (X i)).map (f i)

中文:
定义 ihom
  签名: (X : 对任意 i, C i)
  定义体: fun i => (X i ⟶[C i] Y i)
  map {Y Z} f := fun i => (CategoryTheory.ihom (X i)).map (f i)
-/
def ihom (X : forall i, C i) : (forall i, C i) ⥤ (forall i, C i) where
  obj Y := fun i => (X i ⟶[C i] Y i)
  map {Y Z} f := fun i => (CategoryTheory.ihom (X i)).map (f i)

set_option backward.isDefEq.respectTransparency false in
/-- The unit for the adjunction `tensorLeft X ⊣ ihom X`. -/
@[simps]
/--
Definition of `closedUnit` / `closedUnit` 的定义

English:
definition closedUnit
  signature: (X : forall i, C i)
  body: fun i => (ihom.coev (X i)).app (Y i)

中文:
定义 closedUnit
  签名: (X : 对任意 i, C i)
  定义体: fun i => (ihom.coev (X i)).app (Y i)

Depends on / 依赖: ihom.coev
-/
def closedUnit (X : forall i, C i) : 𝟭 (forall i, C i) ⟶ tensorLeft X ⋙ ihom X where
  app Y := fun i => (ihom.coev (X i)).app (Y i)

set_option backward.isDefEq.respectTransparency false in
/-- The counit for the adjunction `tensorLeft X ⊣ ihom X`. -/
@[simps]
/--
Definition of `closedCounit` / `closedCounit` 的定义

English:
definition closedCounit
  signature: (X : forall i, C i)
  body: fun i => (ihom.ev (X i)).app (Y i)

中文:
定义 closedCounit
  签名: (X : 对任意 i, C i)
  定义体: fun i => (ihom.ev (X i)).app (Y i)

Depends on / 依赖: ihom.ev
-/
def closedCounit (X : forall i, C i) : ihom X ⋙ tensorLeft X ⟶ 𝟭 (forall i, C i) where
  app Y := fun i => (ihom.ev (X i)).app (Y i)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- Equips the product of a family of closed monoidal categories with
a pointwise closed monoidal structure. -/
@[simps]
/--
Instance `monoidalClosed` / 实例 `monoidalClosed`

English:
instance monoidalClosed
  signature: : MonoidalClosed (forall i, C i) where
  body: {
    rightAdj := ihom X
    adj.unit := closedUnit X
    adj.counit := closedCounit X }

中文:
实例 monoidalClosed
  签名: : 幺半群闭 (对任意 i, C i) where
  定义体: {
    rightAdj := ihom X
    adj.unit := closedUnit X
    adj.counit := closedCounit X }
-/
instance monoidalClosed : MonoidalClosed (forall i, C i) where
  closed X := {
    rightAdj := ihom X
    adj.unit := closedUnit X
    adj.counit := closedCounit X }

end Closed

set_option backward.defeqAttrib.useBackward true in
@[simps!]
instance (i : I) : (Pi.eval C i).Monoidal where
  ε := 𝟙 _
  μ X Y := 𝟙 _
  η := 𝟙 _
  δ X Y := 𝟙 _

set_option backward.defeqAttrib.useBackward true in
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [forall
  signature: i, BraidedCategory (C i)] (i

中文:
实例 [对任意
  签名: i, 辫范畴 (C i)] (i
-/
instance [forall i, BraidedCategory (C i)] (i : I) : (Pi.eval C i).Braided where

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
@[simps]
/--
Instance `laxMonoidalPi'` / 实例 `laxMonoidalPi'`

English:
instance laxMonoidalPi'
  signature: {D : Type*} [Category* D] [MonoidalCategory D] (F : forall i : I, D ⥤ C i)
  body: fun i => Functor.LaxMonoidal.ε (F i)
  μ X Y := fun i => Functor.LaxMonoidal.μ (F i) X Y

中文:
实例 laxMonoidalPi'
  签名: {D : 类型} [范畴* D] [幺半群范畴 D] (F : 对任意 i : I, D ⥤ C i)
  定义体: fun i => Functor.LaxMonoidal.ε (F i)
  μ X Y := fun i => Functor.LaxMonoidal.μ (F i) X Y

Depends on / 依赖: Functor, Functor.LaxMonoidal, LaxMonoidal
-/
instance laxMonoidalPi' {D : Type*} [Category* D] [MonoidalCategory D] (F : forall i : I, D ⥤ C i)
    [forall i, (F i).LaxMonoidal] :
    (Functor.pi' F).LaxMonoidal where
  ε := fun i => Functor.LaxMonoidal.ε (F i)
  μ X Y := fun i => Functor.LaxMonoidal.μ (F i) X Y

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
@[simps]
/--
Instance `opLaxMonoidalPi'` / 实例 `opLaxMonoidalPi'`

English:
instance opLaxMonoidalPi'
  signature: {D : Type*} [Category* D] [MonoidalCategory D]
  body: fun i => Functor.OplaxMonoidal.η (F i)
  δ X Y := fun i => Functor.OplaxMonoidal.δ (F i) X Y
  oplax_left_unitality X := by ext; simp
  oplax_right_unitality X := by ext; simp

中文:
实例 opLaxMonoidalPi'
  签名: {D : 类型} [范畴* D] [幺半群范畴 D]
  定义体: fun i => Functor.OplaxMonoidal.η (F i)
  δ X Y := fun i => Functor.OplaxMonoidal.δ (F i) X Y
  oplax_left_unitality X := by ext; simp
  oplax_right_unitality X := by ext; simp

Depends on / 依赖: Functor, Functor.OplaxMonoidal, OplaxMonoidal, Subgroup, Subgroup.mem_mk, Submonoid, Submonoid.mem_mk, Subsemigroup, Subsemigroup.mem_mk, coe_mul, infer_instance, invMulSubgroup, mem_coe, mem_mk
-/
instance opLaxMonoidalPi' {D : Type*} [Category* D] [MonoidalCategory D]
    (F : forall i : I, D ⥤ C i)
    [forall i, (F i).OplaxMonoidal] :
    (Functor.pi' F).OplaxMonoidal where
  η := fun i => Functor.OplaxMonoidal.η (F i)
  δ X Y := fun i => Functor.OplaxMonoidal.δ (F i) X Y
  oplax_left_unitality X := by ext; simp
  oplax_right_unitality X := by ext; simp

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
@[simps!]
/--
Instance `monoidalPi'` / 实例 `monoidalPi'`

English:
instance monoidalPi'
  signature: {D : Type*} [Category* D] [MonoidalCategory D]

中文:
实例 monoidalPi'
  签名: {D : 类型} [范畴* D] [幺半群范畴 D]
-/
instance monoidalPi' {D : Type*} [Category* D] [MonoidalCategory D]
    (F : forall i : I, D ⥤ C i) [forall i, (F i).Monoidal] :
    (Functor.pi' F).Monoidal where

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [forall
  signature: i, BraidedCategory (C i)]
  body: by intros; ext i; exact Functor.LaxBraided.braided _ _

中文:
实例 [对任意
  签名: i, 辫范畴 (C i)]
  定义体: by intros; ext i; exact Functor.LaxBraided.braided _ _

Depends on / 依赖: Functor, Functor.LaxBraided.braided, LaxBraided, braided, intros
-/
instance [forall i, BraidedCategory (C i)]
    {D : Type*} [Category* D] [MonoidalCategory D] [BraidedCategory D]
    (F : forall i : I, D ⥤ C i) [forall i, (F i).LaxBraided] :
    (Functor.pi' F).LaxBraided where
  braided := by intros; ext i; exact Functor.LaxBraided.braided _ _

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [forall
  signature: i, BraidedCategory (C i)]

中文:
实例 [对任意
  签名: i, 辫范畴 (C i)]
-/
instance [forall i, BraidedCategory (C i)]
    {D : Type*} [Category* D] [MonoidalCategory D] [BraidedCategory D]
    (F : forall i : I, D ⥤ C i) [forall i, (F i).Braided] :
    (Functor.pi' F).Braided where

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
@[simps]
/--
Instance `laxMonoidalPi` / 实例 `laxMonoidalPi`

English:
instance laxMonoidalPi
  signature: {D : I -> Type u₂} [forall i, Category.{v₂} (D i)]
  body: fun i => Functor.LaxMonoidal.ε (F i)
  μ X Y := fun i => Functor.LaxMonoidal.μ (F i) (X i) (Y i)

中文:
实例 laxMonoidalPi
  签名: {D : I -> 类型u₂} [对任意 i, 范畴.{v₂} (D i)]
  定义体: fun i => Functor.LaxMonoidal.ε (F i)
  μ X Y := fun i => Functor.LaxMonoidal.μ (F i) (X i) (Y i)

Depends on / 依赖: Functor, Functor.LaxMonoidal, LaxMonoidal
-/
instance laxMonoidalPi {D : I -> Type u₂} [forall i, Category.{v₂} (D i)]
    [forall i, MonoidalCategory (D i)] (F : forall i : I, D i ⥤ C i)
    [forall i, (F i).LaxMonoidal] :
    (Functor.pi F).LaxMonoidal where
  ε := fun i => Functor.LaxMonoidal.ε (F i)
  μ X Y := fun i => Functor.LaxMonoidal.μ (F i) (X i) (Y i)

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
@[simps]
/--
Instance `opLaxMonoidalPi` / 实例 `opLaxMonoidalPi`

English:
instance opLaxMonoidalPi
  signature: {D : I -> Type u₂} [forall i, Category.{v₂} (D i)]
  body: fun i => Functor.OplaxMonoidal.η (F i)
  δ X Y := fun i => Functor.OplaxMonoidal.δ (F i) (X i) (Y i)
  oplax_left_unitality X := by ext; simp
  oplax_right_unitality X := by ext; simp

中文:
实例 opLaxMonoidalPi
  签名: {D : I -> 类型u₂} [对任意 i, 范畴.{v₂} (D i)]
  定义体: fun i => Functor.OplaxMonoidal.η (F i)
  δ X Y := fun i => Functor.OplaxMonoidal.δ (F i) (X i) (Y i)
  oplax_left_unitality X := by ext; simp
  oplax_right_unitality X := by ext; simp

Depends on / 依赖: Functor, Functor.OplaxMonoidal, OplaxMonoidal
-/
instance opLaxMonoidalPi {D : I -> Type u₂} [forall i, Category.{v₂} (D i)]
    [forall i, MonoidalCategory (D i)] (F : forall i : I, D i ⥤ C i)
    [forall i, (F i).OplaxMonoidal] :
    (Functor.pi F).OplaxMonoidal where
  η := fun i => Functor.OplaxMonoidal.η (F i)
  δ X Y := fun i => Functor.OplaxMonoidal.δ (F i) (X i) (Y i)
  oplax_left_unitality X := by ext; simp
  oplax_right_unitality X := by ext; simp

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
@[simps!]
/--
Instance `monoidalPi` / 实例 `monoidalPi`

English:
instance monoidalPi
  signature: {D : I -> Type u₂} [forall i, Category.{v₂} (D i)]

中文:
实例 monoidalPi
  签名: {D : I -> 类型u₂} [对任意 i, 范畴.{v₂} (D i)]
-/
instance monoidalPi {D : I -> Type u₂} [forall i, Category.{v₂} (D i)]
    [forall i, MonoidalCategory (D i)] (F : forall i : I, D i ⥤ C i)
    [forall i, (F i).Monoidal] :
    (Functor.pi F).Monoidal where

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [forall
  signature: i, BraidedCategory (C i)]
  body: by intros; ext i; exact Functor.LaxBraided.braided _ _

中文:
实例 [对任意
  签名: i, 辫范畴 (C i)]
  定义体: by intros; ext i; exact Functor.LaxBraided.braided _ _

Depends on / 依赖: Functor, Functor.LaxBraided.braided, LaxBraided, braided, intros
-/
instance [forall i, BraidedCategory (C i)]
    {D : I -> Type u₂} [forall i, Category.{v₂} (D i)]
    [forall i, MonoidalCategory (D i)] [forall i, BraidedCategory (D i)]
    (F : forall i : I, D i ⥤ C i) [forall i, (F i).LaxBraided] :
    (Functor.pi F).LaxBraided where
  braided := by intros; ext i; exact Functor.LaxBraided.braided _ _

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [forall
  signature: i, BraidedCategory (C i)]

中文:
实例 [对任意
  签名: i, 辫范畴 (C i)]
-/
instance [forall i, BraidedCategory (C i)]
    {D : I -> Type u₂} [forall i, Category.{v₂} (D i)]
    [forall i, MonoidalCategory (D i)] [forall i, BraidedCategory (D i)]
    (F : forall i : I, D i ⥤ C i) [forall i, (F i).Braided] :
    (Functor.pi F).Braided where

set_option backward.defeqAttrib.useBackward true in
instance {D : Type*} [Category* D] [MonoidalCategory D]
    {F G : D ⥤ (forall i, C i)} [F.LaxMonoidal] [G.LaxMonoidal]
    (τ : forall i, F ⋙ Pi.eval C i ⟶ G ⋙ Pi.eval C i)
    [forall i, (τ i).IsMonoidal] :
    (NatTrans.pi' τ).IsMonoidal where
  unit := by ext i; simpa using NatTrans.IsMonoidal.unit (τ := τ i)
  tensor X Y := by ext i; simpa using NatTrans.IsMonoidal.tensor _ _ (τ := τ i)

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
instance {D : I -> Type u₂} [forall i, Category.{v₂} (D i)]
    [forall i, MonoidalCategory (D i)]
    {F G : forall i : I, (D i ⥤ C i)} [forall i, (F i).LaxMonoidal]
    [forall i, (G i).LaxMonoidal] (τ : forall i : I, (F i) ⟶ (G i))
    [forall i, (τ i).IsMonoidal] :
    (NatTrans.pi τ).IsMonoidal where

end Pi

end CategoryTheory
