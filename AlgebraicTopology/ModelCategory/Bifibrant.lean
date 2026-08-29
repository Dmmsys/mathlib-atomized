/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.AlgebraicTopology.ModelCategory.IsCofibrant

/-!
# Bifibrant objects

In this file, we introduce the full subcategories `CofibrantObject C`,
`FibrantObject C` and `BifibrantObject C` of a model category `C` which
respectively consist of cofibrant objects, fibrant objects,
and bifibrant objects, where "bifibrant" means both cofibrant and fibrant.

-/

@[expose] public section

universe v u

open CategoryTheory Limits

namespace HomotopicalAlgebra

variable {C : Type u} [Category.{v} C]

section Cofibrant

variable [CategoryWithCofibrations C] [HasInitial C]

variable (C) in
/--
Definition of `cofibrantObjects` / `cofibrantObjects` 的定义

English:
definition cofibrantObjects
  signature: : ObjectProperty C
  body: IsCofibrant

中文:
定义 cofibrantObjects
  签名: : ObjectProperty C
  定义体: IsCofibrant

Depends on / 依赖: IsCofibrant
-/
def cofibrantObjects : ObjectProperty C := IsCofibrant

variable (C) in
/--
Definition of `CofibrantObject` / `CofibrantObject` 的定义

English:
abbreviation CofibrantObject
  signature: : Type u
  body: (cofibrantObjects C).FullSubcategory

中文:
缩写 CofibrantObject
  签名: : 类型u
  定义体: (cofibrantObjects C).FullSubcategory

Depends on / 依赖: FullSubcategory, cofibrantObjects
-/
abbrev CofibrantObject : Type u := (cofibrantObjects C).FullSubcategory

namespace CofibrantObject

/--
Definition of `mk` / `mk` 的定义

English:
abbreviation mk
  signature: (X : C) [IsCofibrant X]
  body: ⟨X, by assumption⟩

中文:
缩写 mk
  签名: (X : C) [IsCofibrant X]
  定义体: ⟨X, by assumption⟩
-/
abbrev mk (X : C) [IsCofibrant X] : CofibrantObject C :=
  ⟨X, by assumption⟩

/--
lemma `mk_surjective` / 引理 `mk_surjective`

English:
lemma mk_surjective
  given: (X : CofibrantObject C)
  proof: ⟨X.obj, X.property, rfl⟩

中文:
引理 mk_surjective
  条件: (X : CofibrantObject C)
  证明: ⟨X.obj, X.property, rfl⟩

Depends on / 依赖: X.obj, X.property, property
-/
lemma mk_surjective (X : CofibrantObject C) :
    exists (Y : C) (_ : IsCofibrant Y), X = mk Y := ⟨X.obj, X.property, rfl⟩

/--
Definition of `homMk` / `homMk` 的定义

English:
abbreviation homMk
  signature: {X Y : C} [IsCofibrant X] [IsCofibrant Y] (f : X ⟶ Y)
  body: ObjectProperty.homMk f

中文:
缩写 homMk
  签名: {X Y : C} [IsCofibrant X] [IsCofibrant Y] (f : X ⟶ Y)
  定义体: ObjectProperty.homMk f

Depends on / 依赖: ObjectProperty, ObjectProperty.homMk
-/
abbrev homMk {X Y : C} [IsCofibrant X] [IsCofibrant Y] (f : X ⟶ Y) :
    mk X ⟶ mk Y := ObjectProperty.homMk f

/--
lemma `homMk_surjective` / 引理 `homMk_surjective`

English:
lemma homMk_surjective
  statement: {X Y : C} [IsCofibrant X] [IsCofibrant Y]
  proof: ⟨f.hom, rfl⟩

@[simp]

中文:
引理 homMk_surjective
  结论: {X Y : C} [IsCofibrant X] [IsCofibrant Y]
  证明: ⟨f.hom, rfl⟩

@[simp]

Depends on / 依赖: f.hom
-/
lemma homMk_surjective {X Y : C} [IsCofibrant X] [IsCofibrant Y]
    (f : mk X ⟶ mk Y) :
    exists (g : X ⟶ Y), f = homMk g := ⟨f.hom, rfl⟩

@[simp]
/--
lemma `weakEquivalence_homMk_iff` / 引理 `weakEquivalence_homMk_iff`

English:
lemma weakEquivalence_homMk_iff
  statement: [CategoryWithWeakEquivalences C] {X Y : C}
  proof: by
  simp only [weakEquivalence_iff]
  rfl

@[simp]

中文:
引理 weakEquivalence_homMk_iff
  结论: [带弱等价范畴 C] {X Y : C}
  证明: by
  simp only [weakEquivalence_iff]
  rfl

@[simp]

Depends on / 依赖: weakEquivalence_iff
-/
lemma weakEquivalence_homMk_iff [CategoryWithWeakEquivalences C] {X Y : C}
    [IsCofibrant X] [IsCofibrant Y] (f : X ⟶ Y) :
    WeakEquivalence (homMk f) ↔ WeakEquivalence f := by
  simp only [weakEquivalence_iff]
  rfl

@[simp]
/--
lemma `homMk_id` / 引理 `homMk_id`

English:
lemma homMk_id
  given: (X : C) [IsCofibrant X]
  statement: homMk (𝟙 X) = 𝟙 (mk X)
  proof: rfl

@[reassoc (attr := simp)]

中文:
引理 homMk_id
  条件: (X : C) [IsCofibrant X]
  结论: homMk (𝟙 X) = 𝟙 (mk X)
  证明: rfl

@[reassoc (attr := simp)]
-/
lemma homMk_id (X : C) [IsCofibrant X] : homMk (𝟙 X) = 𝟙 (mk X) := rfl

@[reassoc (attr := simp)]
/--
lemma `homMk_homMk` / 引理 `homMk_homMk`

English:
lemma homMk_homMk
  statement: {X Y Z : C} [IsCofibrant X] [IsCofibrant Y] [IsCofibrant Z]
  proof: rfl

中文:
引理 homMk_homMk
  结论: {X Y Z : C} [IsCofibrant X] [IsCofibrant Y] [IsCofibrant Z]
  证明: rfl
-/
lemma homMk_homMk {X Y Z : C} [IsCofibrant X] [IsCofibrant Y] [IsCofibrant Z]
    (f : X ⟶ Y) (g : Y ⟶ Z) :
    homMk f ≫ homMk g = homMk (f ≫ g) := rfl

/--
Definition of `ι` / `ι` 的定义

English:
abbreviation ι
  signature: : CofibrantObject C ⥤ C
  body: (cofibrantObjects C).ι

中文:
缩写 ι
  签名: : CofibrantObject C ⥤ C
  定义体: (cofibrantObjects C).ι

Depends on / 依赖: cofibrantObjects
-/
abbrev ι : CofibrantObject C ⥤ C := (cofibrantObjects C).ι

instance (X : CofibrantObject C) : IsCofibrant X.1 := X.2
instance (X : CofibrantObject C) : IsCofibrant (CofibrantObject.ι.obj X) := X.2

end CofibrantObject

end Cofibrant

section Fibrant

variable [CategoryWithFibrations C] [HasTerminal C]

variable (C) in
/--
Definition of `fibrantObjects` / `fibrantObjects` 的定义

English:
definition fibrantObjects
  signature: : ObjectProperty C
  body: fun X => IsFibrant X

中文:
定义 fibrantObjects
  签名: : ObjectProperty C
  定义体: fun X => IsFibrant X

Depends on / 依赖: IsFibrant
-/
def fibrantObjects : ObjectProperty C := fun X => IsFibrant X

variable (C) in
/--
Definition of `FibrantObject` / `FibrantObject` 的定义

English:
abbreviation FibrantObject
  signature: : Type u
  body: (fibrantObjects C).FullSubcategory

中文:
缩写 FibrantObject
  签名: : 类型u
  定义体: (fibrantObjects C).FullSubcategory

Depends on / 依赖: FullSubcategory, fibrantObjects
-/
abbrev FibrantObject : Type u := (fibrantObjects C).FullSubcategory

namespace FibrantObject

/--
Definition of `mk` / `mk` 的定义

English:
abbreviation mk
  signature: (X : C) [IsFibrant X]
  body: ⟨X, by assumption⟩

中文:
缩写 mk
  签名: (X : C) [IsFibrant X]
  定义体: ⟨X, by assumption⟩
-/
abbrev mk (X : C) [IsFibrant X] : FibrantObject C :=
  ⟨X, by assumption⟩

/--
lemma `mk_surjective` / 引理 `mk_surjective`

English:
lemma mk_surjective
  given: (X : FibrantObject C)
  proof: ⟨X.obj, X.property, rfl⟩

中文:
引理 mk_surjective
  条件: (X : FibrantObject C)
  证明: ⟨X.obj, X.property, rfl⟩

Depends on / 依赖: X.obj, X.property, property
-/
lemma mk_surjective (X : FibrantObject C) :
    exists (Y : C) (_ : IsFibrant Y), X = mk Y := ⟨X.obj, X.property, rfl⟩

/--
Definition of `homMk` / `homMk` 的定义

English:
abbreviation homMk
  signature: {X Y : C} [IsFibrant X] [IsFibrant Y] (f : X ⟶ Y)
  body: ObjectProperty.homMk f

中文:
缩写 homMk
  签名: {X Y : C} [IsFibrant X] [IsFibrant Y] (f : X ⟶ Y)
  定义体: ObjectProperty.homMk f

Depends on / 依赖: ObjectProperty, ObjectProperty.homMk
-/
abbrev homMk {X Y : C} [IsFibrant X] [IsFibrant Y] (f : X ⟶ Y) :
    mk X ⟶ mk Y := ObjectProperty.homMk f

/--
lemma `homMk_surjective` / 引理 `homMk_surjective`

English:
lemma homMk_surjective
  statement: {X Y : C} [IsFibrant X] [IsFibrant Y]
  proof: ⟨f.hom, rfl⟩

@[simp]

中文:
引理 homMk_surjective
  结论: {X Y : C} [IsFibrant X] [IsFibrant Y]
  证明: ⟨f.hom, rfl⟩

@[simp]

Depends on / 依赖: f.hom
-/
lemma homMk_surjective {X Y : C} [IsFibrant X] [IsFibrant Y]
    (f : mk X ⟶ mk Y) :
    exists (g : X ⟶ Y), f = homMk g := ⟨f.hom, rfl⟩

@[simp]
/--
lemma `weakEquivalence_homMk_iff` / 引理 `weakEquivalence_homMk_iff`

English:
lemma weakEquivalence_homMk_iff
  statement: [CategoryWithWeakEquivalences C] {X Y : C}
  proof: by
  simp only [weakEquivalence_iff]
  rfl

@[simp]

中文:
引理 weakEquivalence_homMk_iff
  结论: [带弱等价范畴 C] {X Y : C}
  证明: by
  simp only [weakEquivalence_iff]
  rfl

@[simp]

Depends on / 依赖: weakEquivalence_iff
-/
lemma weakEquivalence_homMk_iff [CategoryWithWeakEquivalences C] {X Y : C}
    [IsFibrant X] [IsFibrant Y] (f : X ⟶ Y) :
    WeakEquivalence (homMk f) ↔ WeakEquivalence f := by
  simp only [weakEquivalence_iff]
  rfl

@[simp]
/--
lemma `homMk_id` / 引理 `homMk_id`

English:
lemma homMk_id
  given: (X : C) [IsFibrant X]
  statement: homMk (𝟙 X) = 𝟙 (mk X)
  proof: rfl

@[reassoc (attr := simp)]

中文:
引理 homMk_id
  条件: (X : C) [IsFibrant X]
  结论: homMk (𝟙 X) = 𝟙 (mk X)
  证明: rfl

@[reassoc (attr := simp)]
-/
lemma homMk_id (X : C) [IsFibrant X] : homMk (𝟙 X) = 𝟙 (mk X) := rfl

@[reassoc (attr := simp)]
/--
lemma `homMk_homMk` / 引理 `homMk_homMk`

English:
lemma homMk_homMk
  statement: {X Y Z : C} [IsFibrant X] [IsFibrant Y] [IsFibrant Z]
  proof: rfl

中文:
引理 homMk_homMk
  结论: {X Y Z : C} [IsFibrant X] [IsFibrant Y] [IsFibrant Z]
  证明: rfl
-/
lemma homMk_homMk {X Y Z : C} [IsFibrant X] [IsFibrant Y] [IsFibrant Z]
    (f : X ⟶ Y) (g : Y ⟶ Z) :
    homMk f ≫ homMk g = homMk (f ≫ g) := rfl

/--
Definition of `ι` / `ι` 的定义

English:
abbreviation ι
  signature: : FibrantObject C ⥤ C
  body: (fibrantObjects C).ι

中文:
缩写 ι
  签名: : FibrantObject C ⥤ C
  定义体: (fibrantObjects C).ι

Depends on / 依赖: fibrantObjects
-/
abbrev ι : FibrantObject C ⥤ C := (fibrantObjects C).ι

instance (X : FibrantObject C) : IsFibrant X.1 := X.2
instance (X : FibrantObject C) : IsFibrant (FibrantObject.ι.obj X) := X.2

end FibrantObject

end Fibrant

section Bifibrant

variable [CategoryWithCofibrations C] [HasInitial C]
  [CategoryWithFibrations C] [HasTerminal C]

variable (C) in
/--
Definition of `bifibrantObjects` / `bifibrantObjects` 的定义

English:
definition bifibrantObjects
  signature: : ObjectProperty C
  body: cofibrantObjects C ⊓ fibrantObjects C

中文:
定义 bifibrantObjects
  签名: : ObjectProperty C
  定义体: cofibrantObjects C ⊓ fibrantObjects C

Depends on / 依赖: cofibrantObjects, fibrantObjects
-/
def bifibrantObjects : ObjectProperty C :=
  cofibrantObjects C ⊓ fibrantObjects C

variable (C) in
/--
lemma `bifibrantObjects_le_cofibrantObject` / 引理 `bifibrantObjects_le_cofibrantObject`

English:
lemma bifibrantObjects_le_cofibrantObject
  proof: fun _ h => h.1

中文:
引理 bifibrantObjects_le_cofibrantObject
  证明: fun _ h => h.1
-/
lemma bifibrantObjects_le_cofibrantObject :
    bifibrantObjects C <= cofibrantObjects C :=
  fun _ h => h.1

variable (C) in
/--
lemma `bifibrantObjects_le_fibrantObject` / 引理 `bifibrantObjects_le_fibrantObject`

English:
lemma bifibrantObjects_le_fibrantObject
  proof: fun _ h => h.2

中文:
引理 bifibrantObjects_le_fibrantObject
  证明: fun _ h => h.2
-/
lemma bifibrantObjects_le_fibrantObject :
    bifibrantObjects C <= fibrantObjects C :=
  fun _ h => h.2

variable (C) in
/--
Definition of `BifibrantObject` / `BifibrantObject` 的定义

English:
abbreviation BifibrantObject
  signature: : Type u
  body: (bifibrantObjects C).FullSubcategory

中文:
缩写 BifibrantObject
  签名: : 类型u
  定义体: (bifibrantObjects C).FullSubcategory

Depends on / 依赖: FullSubcategory, bifibrantObjects
-/
abbrev BifibrantObject : Type u := (bifibrantObjects C).FullSubcategory

namespace BifibrantObject

/--
Definition of `mk` / `mk` 的定义

English:
abbreviation mk
  signature: (X : C) [IsCofibrant X] [IsFibrant X]
  body: ⟨X, by assumption, by assumption⟩

中文:
缩写 mk
  签名: (X : C) [IsCofibrant X] [IsFibrant X]
  定义体: ⟨X, by assumption, by assumption⟩
-/
abbrev mk (X : C) [IsCofibrant X] [IsFibrant X] :
    BifibrantObject C :=
  ⟨X, by assumption, by assumption⟩

/--
lemma `mk_surjective` / 引理 `mk_surjective`

English:
lemma mk_surjective
  given: (X : BifibrantObject C)
  proof: ⟨X.obj, X.property.1, X.property.2, rfl⟩

中文:
引理 mk_surjective
  条件: (X : BifibrantObject C)
  证明: ⟨X.obj, X.property.1, X.property.2, rfl⟩

Depends on / 依赖: X.obj, X.property, property
-/
lemma mk_surjective (X : BifibrantObject C) :
    exists (Y : C) (_ : IsCofibrant Y) (_ : IsFibrant Y), X = mk Y :=
  ⟨X.obj, X.property.1, X.property.2, rfl⟩

/--
Definition of `homMk` / `homMk` 的定义

English:
abbreviation homMk
  signature: {X Y : C} [IsCofibrant X] [IsCofibrant Y]
  body: ObjectProperty.homMk f

中文:
缩写 homMk
  签名: {X Y : C} [IsCofibrant X] [IsCofibrant Y]
  定义体: ObjectProperty.homMk f

Depends on / 依赖: ObjectProperty, ObjectProperty.homMk
-/
abbrev homMk {X Y : C} [IsCofibrant X] [IsCofibrant Y]
    [IsFibrant X] [IsFibrant Y] (f : X ⟶ Y) :
    mk X ⟶ mk Y := ObjectProperty.homMk f

/--
lemma `homMk_surjective` / 引理 `homMk_surjective`

English:
lemma homMk_surjective
  statement: {X Y : C} [IsCofibrant X] [IsCofibrant Y]
  proof: ⟨f.hom, rfl⟩

@[simp]

中文:
引理 homMk_surjective
  结论: {X Y : C} [IsCofibrant X] [IsCofibrant Y]
  证明: ⟨f.hom, rfl⟩

@[simp]

Depends on / 依赖: f.hom
-/
lemma homMk_surjective {X Y : C} [IsCofibrant X] [IsCofibrant Y]
    [IsFibrant X] [IsFibrant Y]
    (f : mk X ⟶ mk Y) :
    exists (g : X ⟶ Y), f = homMk g := ⟨f.hom, rfl⟩

@[simp]
/--
lemma `weakEquivalence_homMk_iff` / 引理 `weakEquivalence_homMk_iff`

English:
lemma weakEquivalence_homMk_iff
  statement: [CategoryWithWeakEquivalences C] {X Y : C}
  proof: by
  simp only [weakEquivalence_iff]
  rfl

@[simp]

中文:
引理 weakEquivalence_homMk_iff
  结论: [带弱等价范畴 C] {X Y : C}
  证明: by
  simp only [weakEquivalence_iff]
  rfl

@[simp]

Depends on / 依赖: weakEquivalence_iff
-/
lemma weakEquivalence_homMk_iff [CategoryWithWeakEquivalences C] {X Y : C}
    [IsCofibrant X] [IsFibrant X] [IsCofibrant Y] [IsFibrant Y] (f : X ⟶ Y) :
    WeakEquivalence (homMk f) ↔ WeakEquivalence f := by
  simp only [weakEquivalence_iff]
  rfl

@[simp]
/--
lemma `homMk_id` / 引理 `homMk_id`

English:
lemma homMk_id
  given: (X : C) [IsCofibrant X] [IsFibrant X]
  proof: rfl

@[reassoc (attr := simp)]

中文:
引理 homMk_id
  条件: (X : C) [IsCofibrant X] [IsFibrant X]
  证明: rfl

@[reassoc (attr := simp)]
-/
lemma homMk_id (X : C) [IsCofibrant X] [IsFibrant X] :
    homMk (𝟙 X) = 𝟙 (mk X) := rfl

@[reassoc (attr := simp)]
/--
lemma `homMk_homMk` / 引理 `homMk_homMk`

English:
lemma homMk_homMk
  statement: {X Y Z : C} [IsCofibrant X] [IsCofibrant Y] [IsCofibrant Z]
  proof: rfl

中文:
引理 homMk_homMk
  结论: {X Y Z : C} [IsCofibrant X] [IsCofibrant Y] [IsCofibrant Z]
  证明: rfl
-/
lemma homMk_homMk {X Y Z : C} [IsCofibrant X] [IsCofibrant Y] [IsCofibrant Z]
    [IsFibrant X] [IsFibrant Y] [IsFibrant Z]
    (f : X ⟶ Y) (g : Y ⟶ Z) :
    homMk f ≫ homMk g = homMk (f ≫ g) := rfl

/--
Definition of `ι` / `ι` 的定义

English:
abbreviation ι
  signature: : BifibrantObject C ⥤ C
  body: (bifibrantObjects C).ι

中文:
缩写 ι
  签名: : BifibrantObject C ⥤ C
  定义体: (bifibrantObjects C).ι

Depends on / 依赖: bifibrantObjects
-/
abbrev ι : BifibrantObject C ⥤ C := (bifibrantObjects C).ι

instance (X : BifibrantObject C) : IsCofibrant X.obj := X.property.1
instance (X : BifibrantObject C) : IsFibrant X.obj := X.property.2
instance (X : BifibrantObject C) : IsCofibrant (BifibrantObject.ι.obj X) := X.property.1
instance (X : BifibrantObject C) : IsFibrant (BifibrantObject.ι.obj X) := X.property.2

/--
Definition of `ιCofibrantObject` / `ιCofibrantObject` 的定义

English:
abbreviation ιCofibrantObject
  signature: : BifibrantObject C ⥤ CofibrantObject C
  body: ObjectProperty.ιOfLE (bifibrantObjects_le_cofibrantObject C)

中文:
缩写 ιCofibrantObject
  签名: : BifibrantObject C ⥤ CofibrantObject C
  定义体: ObjectProperty.ιOfLE (bifibrantObjects_le_cofibrantObject C)

Depends on / 依赖: ObjectProperty, bifibrantObjects_le_cofibrantObject
-/
abbrev ιCofibrantObject : BifibrantObject C ⥤ CofibrantObject C :=
  ObjectProperty.ιOfLE (bifibrantObjects_le_cofibrantObject C)

/--
Definition of `ιFibrantObject` / `ιFibrantObject` 的定义

English:
abbreviation ιFibrantObject
  signature: : BifibrantObject C ⥤ FibrantObject C
  body: ObjectProperty.ιOfLE (bifibrantObjects_le_fibrantObject C)

中文:
缩写 ιFibrantObject
  签名: : BifibrantObject C ⥤ FibrantObject C
  定义体: ObjectProperty.ιOfLE (bifibrantObjects_le_fibrantObject C)

Depends on / 依赖: ObjectProperty, bifibrantObjects_le_fibrantObject
-/
abbrev ιFibrantObject : BifibrantObject C ⥤ FibrantObject C :=
  ObjectProperty.ιOfLE (bifibrantObjects_le_fibrantObject C)

instance (X : BifibrantObject C) : IsCofibrant (ιFibrantObject.obj X).obj := X.property.1

instance (X : BifibrantObject C) : IsFibrant (ιCofibrantObject.obj X).obj := X.property.2

end BifibrantObject

end Bifibrant

end HomotopicalAlgebra
