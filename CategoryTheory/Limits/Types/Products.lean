/-
Copyright (c) 2020 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import Mathlib.CategoryTheory.Limits.Shapes.Products
public import Mathlib.CategoryTheory.Limits.Shapes.BinaryProducts
public import Mathlib.CategoryTheory.Limits.Types.Limits
public import Mathlib.Tactic.CategoryTheory.Elementwise

/-!
# Products in `Type`

We describe arbitrary products in the category of types, as well as binary products,
and the terminal object.

-/

@[expose] public section

universe v u

open CategoryTheory Limits

namespace CategoryTheory.Limits.Types

example : HasProducts.{v} (Type v) := inferInstance
example [UnivLE.{v, u}] : HasProducts.{v} (Type u) := inferInstance

-- This shortcut instance is required in `Mathlib/CategoryTheory/Closed/Types.lean`,
-- although I don't understand why, and wish it wasn't.
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: HasProducts.{v} (Type v)
  body: inferInstance

中文:
实例 :
  签名: HasProducts.{v} (类型v)
  定义体: inferInstance
-/
instance : HasProducts.{v} (Type v) := inferInstance

/-- A restatement of `Types.Limit.lift_π_apply` that uses `Pi.π` and `Pi.lift`. -/
-- The increased `@[simp]` priority here results in a minor speed up in
-- `Mathlib/CategoryTheory/Sites/EqualizerSheafCondition.lean`.
@[simp 1001]
/--
theorem `pi_lift_π_apply` / 定理 `pi_lift_π_apply`

English:
theorem pi_lift_π_apply
  statement: {β : Type v} [Small.{u} β] (f : β -> Type u) {P : Type u}
  proof: ConcreteCategory.congr_hom (limit.lift_π (Fan.mk P s) ⟨b⟩) x

中文:
定理 pi_lift_π_apply
  结论: {β : 类型v} [Small.{u} β] (f : β -> 类型u) {P : 类型u}
  证明: ConcreteCategory.congr_hom (limit.lift_π (Fan.mk P s) ⟨b⟩) x

Depends on / 依赖: ConcreteCategory, ConcreteCategory.congr_hom, Fan.mk, congr_hom, limit.lift_
-/
theorem pi_lift_π_apply {β : Type v} [Small.{u} β] (f : β -> Type u) {P : Type u}
    (s : forall b, P ⟶ f b) (b : β) (x : P) :
    (Pi.π f b) (@Pi.lift β _ _ f _ P s x) = s b x :=
  ConcreteCategory.congr_hom (limit.lift_π (Fan.mk P s) ⟨b⟩) x

/--
theorem `pi_lift_π_apply'` / 定理 `pi_lift_π_apply'`

English:
theorem pi_lift_π_apply'
  statement: {β : Type v} (f : β -> Type v) {P : Type v}
  proof: by
  simp

中文:
定理 pi_lift_π_apply'
  结论: {β : 类型v} (f : β -> 类型v) {P : 类型v}
  证明: by
  simp
-/
theorem pi_lift_π_apply' {β : Type v} (f : β -> Type v) {P : Type v}
    (s : forall b, P ⟶ f b) (b : β) (x : P) :
    Pi.π f b (@Pi.lift β _ _ f _ P s x) = s b x := by
  simp

-- Not `@[simp]` since `simp` can prove it.
/--
theorem `pi_map_π_apply` / 定理 `pi_map_π_apply`

English:
theorem pi_map_π_apply
  statement: {β : Type v} [Small.{u} β] {f g : β -> Type u}
  proof: limMap_π_apply _ _ _

中文:
定理 pi_map_π_apply
  结论: {β : 类型v} [Small.{u} β] {f g : β -> 类型u}
  证明: limMap_π_apply _ _ _
-/
theorem pi_map_π_apply {β : Type v} [Small.{u} β] {f g : β -> Type u}
    (α : forall j, f j ⟶ g j) (b : β) (x) :
    Pi.π g b (Pi.map α x) = α b ((Pi.π f b) x) :=
  limMap_π_apply _ _ _

/--
theorem `pi_map_π_apply'` / 定理 `pi_map_π_apply'`

English:
theorem pi_map_π_apply'
  given: {β : Type v} {f g : β -> Type v} (α : forall j, f j ⟶ g j) (b : β) (x)
  proof: by
  simp [pi_map_π_apply]

中文:
定理 pi_map_π_apply'
  条件: {β : 类型v} {f g : β -> 类型v} (α : 对任意 j, f j ⟶ g j) (b : β) (x)
  证明: by
  simp [pi_map_π_apply]
-/
theorem pi_map_π_apply' {β : Type v} {f g : β -> Type v} (α : forall j, f j ⟶ g j) (b : β) (x) :
    Pi.π g b (Pi.map α x) = α b ((Pi.π f b) x) := by
  simp [pi_map_π_apply]

/--
Definition of `isTerminalPUnit` / `isTerminalPUnit` 的定义

English:
definition isTerminalPUnit
  signature: : IsTerminal (PUnit : Type u)
  body: letI (X : Type u) : Unique (X ⟶ PUnit) := TypeCat.homEquiv.unique
  .ofUnique _

@[simp]

中文:
定义 isTerminalPUnit
  签名: : 是终止 (命题单元 : 类型u)
  定义体: letI (X : Type u) : Unique (X ⟶ PUnit) := TypeCat.homEquiv.unique
  .ofUnique _

@[simp]

Depends on / 依赖: TypeCat, TypeCat.homEquiv.unique, Unique, homEquiv, ofUnique, unique
-/
def isTerminalPUnit : IsTerminal (PUnit : Type u) :=
  letI (X : Type u) : Unique (X ⟶ PUnit) := TypeCat.homEquiv.unique
  .ofUnique _

@[simp]
/--
lemma `isTerminalPUnit_from_apply` / 引理 `isTerminalPUnit_from_apply`

English:
lemma isTerminalPUnit_from_apply
  given: {X : Type u} (x : X)
  statement: isTerminalPUnit.from X x = .unit
  proof: rfl

@[deprecated (since := "2026-02-08")] alias isTerminalPunit := isTerminalPUnit

中文:
引理 isTerminalPUnit_from_apply
  条件: {X : 类型u} (x : X)
  结论: isTerminalPUnit.from X x = .unit
  证明: rfl

@[deprecated (since := "2026-02-08")] alias isTerminalPunit := isTerminalPUnit
-/
lemma isTerminalPUnit_from_apply {X : Type u} (x : X) : isTerminalPUnit.from X x = .unit := rfl

@[deprecated (since := "2026-02-08")] alias isTerminalPunit := isTerminalPUnit

/--
Definition of `terminalLimitCone` / `terminalLimitCone` 的定义

English:
definition terminalLimitCone
  signature: : Limits.LimitCone (Functor.empty (Type u))
  body: ⟨_, isTerminalPUnit⟩

中文:
定义 terminalLimitCone
  签名: : Limits.极限锥 (函子.empty (类型u))
  定义体: ⟨_, isTerminalPUnit⟩

Depends on / 依赖: isTerminalPUnit
-/
def terminalLimitCone : Limits.LimitCone (Functor.empty (Type u)) := ⟨_, isTerminalPUnit⟩

/--
Definition of `terminalIso` / `terminalIso` 的定义

English:
definition terminalIso
  signature: : ⊤_ Type u ≅ PUnit
  body: terminalIsTerminal.uniqueUpToIso isTerminalPUnit

中文:
定义 terminalIso
  签名: : ⊤_ 类型u ≅ 命题单元
  定义体: terminalIsTerminal.uniqueUpToIso isTerminalPUnit

Depends on / 依赖: isTerminalPUnit, terminalIsTerminal, terminalIsTerminal.uniqueUpToIso, uniqueUpToIso
-/
noncomputable def terminalIso : ⊤_ Type u ≅ PUnit :=
  terminalIsTerminal.uniqueUpToIso isTerminalPUnit

/--
Definition of `isTerminalEquivUnique` / `isTerminalEquivUnique` 的定义

English:
definition isTerminalEquivUnique
  signature: (X : Type u)
  body: equivOfSubsingletonOfSubsingleton
    (fun h => (IsTerminal.uniqueUpToIso h isTerminalPUnit).toEquiv.unique)
    (fun _ => IsTerminal.ofIso isTerminalPUnit (Equiv.toIso (Equiv.ofUnique _ _)))

中文:
定义 isTerminalEquivUnique
  签名: (X : 类型u)
  定义体: equivOfSubsingletonOfSubsingleton
    (fun h => (IsTerminal.uniqueUpToIso h isTerminalPUnit).toEquiv.unique)
    (fun _ => IsTerminal.ofIso isTerminalPUnit (Equiv.toIso (Equiv.ofUnique _ _)))

Depends on / 依赖: Equiv.ofUnique, Equiv.toIso, IsTerminal, IsTerminal.ofIso, IsTerminal.uniqueUpToIso, equivOfSubsingletonOfSubsingleton, isTerminalPUnit, ofUnique, toEquiv, toEquiv.unique, unique, uniqueUpToIso
-/
def isTerminalEquivUnique (X : Type u) : IsTerminal X ≃ Unique X :=
  equivOfSubsingletonOfSubsingleton
    (fun h => (IsTerminal.uniqueUpToIso h isTerminalPUnit).toEquiv.unique)
    (fun _ => IsTerminal.ofIso isTerminalPUnit (Equiv.toIso (Equiv.ofUnique _ _)))

/--
Definition of `isTerminalEquivIsoPUnit` / `isTerminalEquivIsoPUnit` 的定义

English:
definition isTerminalEquivIsoPUnit
  signature: (X : Type u)
  body: by
  calc
    IsTerminal X ≃ Unique X := isTerminalEquivUnique _
    _ ≃ (X ≃ PUnit) := uniqueEquivEquivUnique _ _
    _ ≃ (X ≅ PUnit) := equivEquivIso

中文:
定义 isTerminalEquivIsoPUnit
  签名: (X : 类型u)
  定义体: by
  calc
    IsTerminal X ≃ Unique X := isTerminalEquivUnique _
    _ ≃ (X ≃ PUnit) := uniqueEquivEquivUnique _ _
    _ ≃ (X ≅ PUnit) := equivEquivIso

Depends on / 依赖: IsTerminal, Unique, equivEquivIso, isTerminalEquivUnique, uniqueEquivEquivUnique
-/
def isTerminalEquivIsoPUnit (X : Type u) : IsTerminal X ≃ (X ≅ PUnit) := by
  calc
    IsTerminal X ≃ Unique X := isTerminalEquivUnique _
    _ ≃ (X ≃ PUnit) := uniqueEquivEquivUnique _ _
    _ ≃ (X ≅ PUnit) := equivEquivIso

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Unique (⊤_ (Type u))
  body: isTerminalEquivUnique _ terminalIsTerminal

中文:
实例 :
  签名: 唯一 (⊤_ (类型u))
  定义体: isTerminalEquivUnique _ terminalIsTerminal

Depends on / 依赖: isTerminalEquivUnique, terminalIsTerminal
-/
noncomputable instance : Unique (⊤_ (Type u)) := isTerminalEquivUnique _ terminalIsTerminal

open CategoryTheory.Limits.WalkingPair

-- We manually generate the other projection lemmas since the simp-normal form for the legs is
-- otherwise not created correctly.
/-- The product type `X × Y` forms a cone for the binary product of `X` and `Y`. -/
@[simps! pt]
/--
Definition of `binaryProductCone` / `binaryProductCone` 的定义

English:
definition binaryProductCone
  signature: (X Y : Type u)
  body: BinaryFan.mk (↾_root_.Prod.fst) (↾_root_.Prod.snd)

@[simp]

中文:
定义 binaryProductCone
  签名: (X Y : 类型u)
  定义体: BinaryFan.mk (↾_root_.Prod.fst) (↾_root_.Prod.snd)

@[simp]

Depends on / 依赖: BinaryFan, BinaryFan.mk, _root_, _root_.Prod.fst, _root_.Prod.snd
-/
def binaryProductCone (X Y : Type u) : BinaryFan X Y :=
  BinaryFan.mk (↾_root_.Prod.fst) (↾_root_.Prod.snd)

@[simp]
/--
theorem `binaryProductCone_fst` / 定理 `binaryProductCone_fst`

English:
theorem binaryProductCone_fst
  given: (X Y : Type u)
  proof: rfl

@[simp]

中文:
定理 binaryProductCone_fst
  条件: (X Y : 类型u)
  证明: rfl

@[simp]
-/
theorem binaryProductCone_fst (X Y : Type u) :
    (binaryProductCone X Y).fst = ↾_root_.Prod.fst :=
  rfl

@[simp]
/--
theorem `binaryProductCone_snd` / 定理 `binaryProductCone_snd`

English:
theorem binaryProductCone_snd
  given: (X Y : Type u)
  proof: rfl

中文:
定理 binaryProductCone_snd
  条件: (X Y : 类型u)
  证明: rfl
-/
theorem binaryProductCone_snd (X Y : Type u) :
    (binaryProductCone X Y).snd = ↾_root_.Prod.snd :=
  rfl

/-- The product type `X × Y` is a binary product for `X` and `Y`. -/
@[simps]
/--
Definition of `binaryProductLimit` / `binaryProductLimit` 的定义

English:
definition binaryProductLimit
  signature: (X Y : Type u)
  body: ↾fun x => (s.fst x, s.snd x)
  fac _ j := Discrete.recOn j fun j => WalkingPair.casesOn j rfl rfl
  uniq _ _ w := by
    ext x
    apply Prod.ext
    exacts [ConcreteCategory.congr_hom (w ⟨left⟩) x, ConcreteCategory.congr_hom (w ⟨right⟩) x]

中文:
定义 binaryProductLimit
  签名: (X Y : 类型u)
  定义体: ↾fun x => (s.fst x, s.snd x)
  fac _ j := Discrete.recOn j fun j => WalkingPair.casesOn j rfl rfl
  uniq _ _ w := by
    ext x
    apply Prod.ext
    exacts [ConcreteCategory.congr_hom (w ⟨left⟩) x, ConcreteCategory.congr_hom (w ⟨right⟩) x]

Depends on / 依赖: s.fst, s.snd
-/
def binaryProductLimit (X Y : Type u) : IsLimit (binaryProductCone X Y) where
  lift (s : BinaryFan X Y) := ↾fun x => (s.fst x, s.snd x)
  fac _ j := Discrete.recOn j fun j => WalkingPair.casesOn j rfl rfl
  uniq _ _ w := by
    ext x
    apply Prod.ext
    exacts [ConcreteCategory.congr_hom (w ⟨left⟩) x, ConcreteCategory.congr_hom (w ⟨right⟩) x]

/-- The category of types has `X × Y`, the usual Cartesian product,
as the binary product of `X` and `Y`.
-/
@[simps]
/--
Definition of `binaryProductLimitCone` / `binaryProductLimitCone` 的定义

English:
definition binaryProductLimitCone
  signature: (X Y : Type u)
  body: ⟨_, binaryProductLimit X Y⟩

中文:
定义 binaryProductLimitCone
  签名: (X Y : 类型u)
  定义体: ⟨_, binaryProductLimit X Y⟩

Depends on / 依赖: binaryProductLimit
-/
def binaryProductLimitCone (X Y : Type u) : Limits.LimitCone (pair X Y) :=
  ⟨_, binaryProductLimit X Y⟩

/--
Definition of `binaryProductIso` / `binaryProductIso` 的定义

English:
definition binaryProductIso
  signature: (X Y : Type u)
  body: limit.isoLimitCone (binaryProductLimitCone X Y)

@[elementwise (attr := simp)]

中文:
定义 binaryProductIso
  签名: (X Y : 类型u)
  定义体: limit.isoLimitCone (binaryProductLimitCone X Y)

@[elementwise (attr := simp)]

Depends on / 依赖: binaryProductLimitCone, isoLimitCone, limit.isoLimitCone
-/
noncomputable def binaryProductIso (X Y : Type u) : Limits.prod X Y ≅ X × Y :=
  limit.isoLimitCone (binaryProductLimitCone X Y)

@[elementwise (attr := simp)]
/--
theorem `binaryProductIso_hom_comp_fst` / 定理 `binaryProductIso_hom_comp_fst`

English:
theorem binaryProductIso_hom_comp_fst
  given: (X Y : Type u)
  proof: limit.isoLimitCone_hom_π (binaryProductLimitCone X Y) ⟨WalkingPair.left⟩

@[elementwise (attr := simp)]

中文:
定理 binaryProductIso_hom_comp_fst
  条件: (X Y : 类型u)
  证明: limit.isoLimitCone_hom_π (binaryProductLimitCone X Y) ⟨WalkingPair.left⟩

@[elementwise (attr := simp)]

Depends on / 依赖: WalkingPair, WalkingPair.left, binaryProductLimitCone, limit.isoLimitCone_hom_
-/
theorem binaryProductIso_hom_comp_fst (X Y : Type u) :
    (binaryProductIso X Y).hom ≫ ↾_root_.Prod.fst = Limits.prod.fst :=
  limit.isoLimitCone_hom_π (binaryProductLimitCone X Y) ⟨WalkingPair.left⟩

@[elementwise (attr := simp)]
/--
theorem `binaryProductIso_hom_comp_snd` / 定理 `binaryProductIso_hom_comp_snd`

English:
theorem binaryProductIso_hom_comp_snd
  given: (X Y : Type u)
  proof: limit.isoLimitCone_hom_π (binaryProductLimitCone X Y) ⟨WalkingPair.right⟩

@[elementwise (attr := simp)]

中文:
定理 binaryProductIso_hom_comp_snd
  条件: (X Y : 类型u)
  证明: limit.isoLimitCone_hom_π (binaryProductLimitCone X Y) ⟨WalkingPair.right⟩

@[elementwise (attr := simp)]

Depends on / 依赖: WalkingPair, WalkingPair.right, binaryProductLimitCone, limit.isoLimitCone_hom_
-/
theorem binaryProductIso_hom_comp_snd (X Y : Type u) :
    (binaryProductIso X Y).hom ≫ ↾_root_.Prod.snd = Limits.prod.snd :=
  limit.isoLimitCone_hom_π (binaryProductLimitCone X Y) ⟨WalkingPair.right⟩

@[elementwise (attr := simp)]
/--
theorem `binaryProductIso_inv_comp_fst` / 定理 `binaryProductIso_inv_comp_fst`

English:
theorem binaryProductIso_inv_comp_fst
  given: (X Y : Type u)
  proof: limit.isoLimitCone_inv_π (binaryProductLimitCone X Y) ⟨WalkingPair.left⟩

@[elementwise (attr := simp)]

中文:
定理 binaryProductIso_inv_comp_fst
  条件: (X Y : 类型u)
  证明: limit.isoLimitCone_inv_π (binaryProductLimitCone X Y) ⟨WalkingPair.left⟩

@[elementwise (attr := simp)]

Depends on / 依赖: WalkingPair, WalkingPair.left, binaryProductLimitCone, limit.isoLimitCone_inv_
-/
theorem binaryProductIso_inv_comp_fst (X Y : Type u) :
    (binaryProductIso X Y).inv ≫ Limits.prod.fst = ↾_root_.Prod.fst :=
  limit.isoLimitCone_inv_π (binaryProductLimitCone X Y) ⟨WalkingPair.left⟩

@[elementwise (attr := simp)]
/--
theorem `binaryProductIso_inv_comp_snd` / 定理 `binaryProductIso_inv_comp_snd`

English:
theorem binaryProductIso_inv_comp_snd
  given: (X Y : Type u)
  proof: limit.isoLimitCone_inv_π (binaryProductLimitCone X Y) ⟨WalkingPair.right⟩

中文:
定理 binaryProductIso_inv_comp_snd
  条件: (X Y : 类型u)
  证明: limit.isoLimitCone_inv_π (binaryProductLimitCone X Y) ⟨WalkingPair.right⟩

Depends on / 依赖: WalkingPair, WalkingPair.right, binaryProductLimitCone, limit.isoLimitCone_inv_
-/
theorem binaryProductIso_inv_comp_snd (X Y : Type u) :
    (binaryProductIso X Y).inv ≫ Limits.prod.snd = ↾_root_.Prod.snd :=
  limit.isoLimitCone_inv_π (binaryProductLimitCone X Y) ⟨WalkingPair.right⟩

/-- The functor which sends `X, Y` to the product type `X × Y`. -/
@[simps]
/--
Definition of `binaryProductFunctor` / `binaryProductFunctor` 的定义

English:
definition binaryProductFunctor
  signature: : Type u ⥤ Type u ⥤ Type u where
  body: { obj := fun Y => X × Y
      map := fun {_ Y₂} f => (binaryProductLimit X Y₂).lift
        (BinaryFan.mk (↾_root_.Prod.fst) (↾_root_.Prod.snd ≫ f)) }
  map {X₁ X₂} f :=
    { app := fun Y =>
      BinaryFan.IsLimit.lift (binaryProductLimit X₂ Y) (↾_root_.Prod.fst ≫ f) (↾_root_.Prod.snd) }

中文:
定义 binaryProductFunctor
  签名: : 类型u ⥤ 类型u ⥤ 类型u where
  定义体: { obj := fun Y => X × Y
      map := fun {_ Y₂} f => (binaryProductLimit X Y₂).lift
        (BinaryFan.mk (↾_root_.Prod.fst) (↾_root_.Prod.snd ≫ f)) }
  map {X₁ X₂} f :=
    { app := fun Y =>
      BinaryFan.IsLimit.lift (binaryProductLimit X₂ Y) (↾_root_.Prod.fst ≫ f) (↾_root_.Prod.snd) }

Depends on / 依赖: BinaryFan, BinaryFan.IsLimit.lift, BinaryFan.mk, IsLimit, _root_, _root_.Prod.fst, _root_.Prod.snd, binaryProductLimit
-/
def binaryProductFunctor : Type u ⥤ Type u ⥤ Type u where
  obj X :=
    { obj := fun Y => X × Y
      map := fun {_ Y₂} f => (binaryProductLimit X Y₂).lift
        (BinaryFan.mk (↾_root_.Prod.fst) (↾_root_.Prod.snd ≫ f)) }
  map {X₁ X₂} f :=
    { app := fun Y =>
      BinaryFan.IsLimit.lift (binaryProductLimit X₂ Y) (↾_root_.Prod.fst ≫ f) (↾_root_.Prod.snd) }

set_option backward.isDefEq.respectTransparency false in
/--
Definition of `binaryProductIsoProd` / `binaryProductIsoProd` 的定义

English:
definition binaryProductIsoProd
  signature: :
  body: by
  refine NatIso.ofComponents (fun X => ?_) (fun _ => ?_)
  · refine NatIso.ofComponents (fun Y => ?_) (fun _ => ?_)
    · exact ((limit.isLimit _).conePointUniqueUpToIso (binaryProductLimit X Y)).symm
    · apply Limits.prod.hom_ext <;> simp <;> rfl
  · ext : 2
    apply Limits.prod.hom_ext <;> simp <;> rfl

中文:
定义 binaryProductIsoProd
  签名: :
  定义体: by
  refine NatIso.ofComponents (fun X => ?_) (fun _ => ?_)
  · refine NatIso.ofComponents (fun Y => ?_) (fun _ => ?_)
    · exact ((limit.isLimit _).conePointUniqueUpToIso (binaryProductLimit X Y)).symm
    · apply Limits.prod.hom_ext <;> simp <;> rfl
  · ext : 2
    apply Limits.prod.hom_ext <;> simp <;> rfl

Depends on / 依赖: Limits, Limits.prod.hom_ext, NatIso, NatIso.ofComponents, binaryProductLimit, conePointUniqueUpToIso, hom_ext, isLimit, limit.isLimit, ofComponents
-/
noncomputable def binaryProductIsoProd :
    binaryProductFunctor ≅ (prod.functor : Type u ⥤ _) := by
  refine NatIso.ofComponents (fun X => ?_) (fun _ => ?_)
  · refine NatIso.ofComponents (fun Y => ?_) (fun _ => ?_)
    · exact ((limit.isLimit _).conePointUniqueUpToIso (binaryProductLimit X Y)).symm
    · apply Limits.prod.hom_ext <;> simp <;> rfl
  · ext : 2
    apply Limits.prod.hom_ext <;> simp <;> rfl

/--
Definition of `productLimitCone` / `productLimitCone` 的定义

English:
definition productLimitCone
  signature: {J : Type v} (F : J -> Type (max v u))
  body: { pt := (forall j, F j)
      π := Discrete.natTrans (fun ⟨j⟩ => ↾fun f => f j) }
  isLimit :=
    { lift := fun s => ↾fun x j => s.π.app ⟨j⟩ x
      uniq := fun _ _ w => by
        ext x j
        exact ConcreteCategory.congr_hom (w ⟨j⟩) x }

中文:
定义 productLimitCone
  签名: {J : 类型v} (F : J -> 类型 (最大值 v u))
  定义体: { pt := (forall j, F j)
      π := Discrete.natTrans (fun ⟨j⟩ => ↾fun f => f j) }
  isLimit :=
    { lift := fun s => ↾fun x j => s.π.app ⟨j⟩ x
      uniq := fun _ _ w => by
        ext x j
        exact ConcreteCategory.congr_hom (w ⟨j⟩) x }

Depends on / 依赖: ConcreteCategory, ConcreteCategory.congr_hom, Discrete, Discrete.natTrans, congr_hom, isLimit, natTrans
-/
def productLimitCone {J : Type v} (F : J -> Type (max v u)) :
    Limits.LimitCone (Discrete.functor F) where
  cone :=
    { pt := (forall j, F j)
      π := Discrete.natTrans (fun ⟨j⟩ => ↾fun f => f j) }
  isLimit :=
    { lift := fun s => ↾fun x j => s.π.app ⟨j⟩ x
      uniq := fun _ _ w => by
        ext x j
        exact ConcreteCategory.congr_hom (w ⟨j⟩) x }

/--
Definition of `productIso` / `productIso` 的定义

English:
definition productIso
  signature: {J : Type v} (F : J -> Type (max v u))
  body: limit.isoLimitCone (productLimitCone.{v, u} F)

@[elementwise (attr := simp)]

中文:
定义 productIso
  签名: {J : 类型v} (F : J -> 类型 (最大值 v u))
  定义体: limit.isoLimitCone (productLimitCone.{v, u} F)

@[elementwise (attr := simp)]

Depends on / 依赖: isoLimitCone, limit.isoLimitCone, productLimitCone
-/
noncomputable def productIso {J : Type v} (F : J -> Type (max v u)) :
    ∏ᶜ F ≅ (forall j, F j) :=
  limit.isoLimitCone (productLimitCone.{v, u} F)

@[elementwise (attr := simp)]
/--
theorem `productIso_hom_comp_eval` / 定理 `productIso_hom_comp_eval`

English:
theorem productIso_hom_comp_eval
  given: {J : Type v} (F : J -> Type (max v u)) (j : J)
  proof: by
  rfl

中文:
定理 productIso_hom_comp_eval
  条件: {J : 类型v} (F : J -> 类型 (最大值 v u)) (j : J)
  证明: by
  rfl
-/
theorem productIso_hom_comp_eval {J : Type v} (F : J -> Type (max v u)) (j : J) :
    (productIso.{v, u} F).hom ≫ (↾fun f => f j) = Pi.π F j := by
  rfl

-- -- Used to be generated by `elementwise`
-- @[simp]
-- theorem productIso_hom_comp_eval_apply {J : Type v} (F : J → Type (max v u)) (j : J)
-- (x : ∏ᶜ F) : (Types.productIso F).hom x j = Pi.π F j x :=
-- rfl

@[elementwise (attr := simp)]
/--
theorem `productIso_inv_comp_π` / 定理 `productIso_inv_comp_π`

English:
theorem productIso_inv_comp_π
  given: {J : Type v} (F : J -> Type max v u) (j : J)
  proof: limit.isoLimitCone_inv_π (productLimitCone.{v, u} F) ⟨j⟩

中文:
定理 productIso_inv_comp_π
  条件: {J : 类型v} (F : J -> 类型 最大值 v u) (j : J)
  证明: limit.isoLimitCone_inv_π (productLimitCone.{v, u} F) ⟨j⟩

Depends on / 依赖: limit.isoLimitCone_inv_, productLimitCone
-/
theorem productIso_inv_comp_π {J : Type v} (F : J -> Type max v u) (j : J) :
    (productIso.{v, u} F).inv ≫ Pi.π F j = ↾fun f => f j :=
  limit.isoLimitCone_inv_π (productLimitCone.{v, u} F) ⟨j⟩

namespace Small

variable {J : Type v} (F : J -> Type u) [Small.{u} J]

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/--
Definition of `productLimitCone` / `productLimitCone` 的定义

English:
definition productLimitCone
  signature: :
  body: { pt := Shrink (forall j, F j)
      π := Discrete.natTrans (fun ⟨j⟩ =>
        ↾fun f => (equivShrink (forall j, F j)).symm f j) }
  isLimit :=
    { lift := fun s => ↾fun x => (equivShrink _) (fun j => s.π.app ⟨j⟩ x)
      uniq := fun s m w => ConcreteCategory.hom_ext _ _ fun x => Shrink.ext (funext fun j => by
        simpa using! ConcreteCategory.congr_hom (w ⟨j⟩) x) }

中文:
定义 productLimitCone
  签名: :
  定义体: { pt := Shrink (forall j, F j)
      π := Discrete.natTrans (fun ⟨j⟩ =>
        ↾fun f => (equivShrink (forall j, F j)).symm f j) }
  isLimit :=
    { lift := fun s => ↾fun x => (equivShrink _) (fun j => s.π.app ⟨j⟩ x)
      uniq := fun s m w => ConcreteCategory.hom_ext _ _ fun x => Shrink.ext (funext fun j => by
        simpa using! ConcreteCategory.congr_hom (w ⟨j⟩) x) }

Depends on / 依赖: ConcreteCategory, ConcreteCategory.congr_hom, ConcreteCategory.hom_ext, Discrete, Discrete.natTrans, Shrink, Shrink.ext, congr_hom, equivShrink, hom_ext, isLimit, natTrans
-/
noncomputable def productLimitCone :
    Limits.LimitCone (Discrete.functor F) where
  cone :=
    { pt := Shrink (forall j, F j)
      π := Discrete.natTrans (fun ⟨j⟩ =>
        ↾fun f => (equivShrink (forall j, F j)).symm f j) }
  isLimit :=
    { lift := fun s => ↾fun x => (equivShrink _) (fun j => s.π.app ⟨j⟩ x)
      uniq := fun s m w => ConcreteCategory.hom_ext _ _ fun x => Shrink.ext (funext fun j => by
        simpa using! ConcreteCategory.congr_hom (w ⟨j⟩) x) }

set_option backward.isDefEq.respectTransparency.types false in
/--
Definition of `productIso` / `productIso` 的定义

English:
definition productIso
  signature: :
  body: limit.isoLimitCone (productLimitCone.{v, u} F)

中文:
定义 productIso
  签名: :
  定义体: limit.isoLimitCone (productLimitCone.{v, u} F)

Depends on / 依赖: isoLimitCone, limit.isoLimitCone, productLimitCone
-/
noncomputable def productIso :
    (∏ᶜ F : Type u) ≅ Shrink (forall j, F j) :=
  limit.isoLimitCone (productLimitCone.{v, u} F)

set_option backward.isDefEq.respectTransparency.types false in
@[elementwise (attr := simp)]
/--
theorem `productIso_hom_comp_eval` / 定理 `productIso_hom_comp_eval`

English:
theorem productIso_hom_comp_eval
  given: (j : J)
  proof: limit.isoLimitCone_hom_π (productLimitCone.{v, u} F) ⟨j⟩

中文:
定理 productIso_hom_comp_eval
  条件: (j : J)
  证明: limit.isoLimitCone_hom_π (productLimitCone.{v, u} F) ⟨j⟩

Depends on / 依赖: limit.isoLimitCone_hom_, productLimitCone
-/
theorem productIso_hom_comp_eval (j : J) :
    (productIso.{v, u} F).hom ≫ (↾fun f => (equivShrink (forall j, F j)).symm f j) =
      Pi.π F j :=
  limit.isoLimitCone_hom_π (productLimitCone.{v, u} F) ⟨j⟩

set_option backward.isDefEq.respectTransparency.types false in
@[elementwise (attr := simp)]
/--
theorem `productIso_inv_comp_π` / 定理 `productIso_inv_comp_π`

English:
theorem productIso_inv_comp_π
  given: (j : J)
  proof: limit.isoLimitCone_inv_π (productLimitCone.{v, u} F) ⟨j⟩

中文:
定理 productIso_inv_comp_π
  条件: (j : J)
  证明: limit.isoLimitCone_inv_π (productLimitCone.{v, u} F) ⟨j⟩

Depends on / 依赖: limit.isoLimitCone_inv_, productLimitCone
-/
theorem productIso_inv_comp_π (j : J) :
    (productIso.{v, u} F).inv ≫ Pi.π F j =
      ↾fun f => ((equivShrink (forall j, F j)).symm f) j :=
  limit.isoLimitCone_inv_π (productLimitCone.{v, u} F) ⟨j⟩

end Small

end CategoryTheory.Limits.Types
