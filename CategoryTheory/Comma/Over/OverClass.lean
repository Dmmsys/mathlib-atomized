/-
Copyright (c) 2024 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
module

public import Mathlib.Tactic.CategoryTheory.Reassoc
public import Mathlib.CategoryTheory.Comma.Over.Basic

/-!
# Typeclasses for `S`-objects and `S`-morphisms

**Warning**: This is not usually how typeclasses should be used.
This is only a sensible approach when the morphism is considered as a structure on `X`,
typically in algebraic geometry.

This is analogous to how we view ringhoms as structures via the `Algebra` typeclass.

For other applications use unbundled arrows or `CategoryTheory.Over`.

## Main definition
- `CategoryTheory.OverClass`: `OverClass X S` equips `X` with a morphism into `S`.
  `X ↘ S : X ⟶ S` is the structure morphism.
- `CategoryTheory.HomIsOver`:
  `HomIsOver f S` asserts that `f` commutes with the structure morphisms.

-/

@[expose] public section

namespace CategoryTheory

universe v u

variable {C : Type u} [Category.{v} C]

variable {X Y Z : C} (f : X ⟶ Y) (S S' : C)

/--
Definition of `OverClass` / `OverClass` 的定义

English:
class OverClass
  parameters: (X S : C)
  axioms and operations (2):
    - ofHom : :
    - hom : X ⟶ S

中文:
类 OverClass
  参数: (X S : C)
  公理与运算 (2 个):
    - ofHom : :
    - hom : X ⟶ S
-/
class OverClass (X S : C) : Type v where
  ofHom ::
  /-- The structure morphism. Use `X ↘ S` instead. -/
  hom : X ⟶ S

/--
Definition of `over` / `over` 的定义

English:
definition over
  signature: (X S : C) (_ : OverClass X S := by infer_instance)
  body: OverClass.hom

中文:
定义 over
  签名: (X S : C) (_ : OverClass X S := by infer_instance)
  定义体: OverClass.hom

Depends on / 依赖: OverClass, OverClass.hom, infer_instance
-/
def over (X S : C) (_ : OverClass X S := by infer_instance) : X ⟶ S := OverClass.hom

/-- The structure morphism `X ↘ S : X ⟶ S` given `OverClass X S`. -/
notation:90 X:90 " ↘ " S:90 => CategoryTheory.over X S inferInstance

/--
Definition of `OverClass.Simps.over` / `OverClass.Simps.over` 的定义

English:
definition OverClass.Simps.over
  signature: (X S : C) [OverClass X S]
  body: X ↘ S

initialize_simps_projections OverClass (hom -> over)

中文:
定义 OverClass.Simps.over
  签名: (X S : C) [OverClass X S]
  定义体: X ↘ S

initialize_simps_projections OverClass (hom -> over)
-/
def OverClass.Simps.over (X S : C) [OverClass X S] : X ⟶ S := X ↘ S

initialize_simps_projections OverClass (hom -> over)

/--
Definition of `CanonicallyOverClass` / `CanonicallyOverClass` 的定义

English:
class CanonicallyOverClass
  parameters: (X : C) (S : semiOutParam C)
  extends: OverClass X S
  (no additional axioms)

中文:
类 CanonicallyOverClass
  参数: (X : C) (S : semiOutParam C)
  继承: OverClass X S
  (无附加公理)
-/
class CanonicallyOverClass (X : C) (S : semiOutParam C) extends OverClass X S where

/--
Definition of `CanonicallyOverClass.Simps.over` / `CanonicallyOverClass.Simps.over` 的定义

English:
definition CanonicallyOverClass.Simps.over
  signature: (X S : C) [CanonicallyOverClass X S]
  body: X ↘ S

initialize_simps_projections CanonicallyOverClass (hom -> over)

@[simps]

中文:
定义 CanonicallyOverClass.Simps.over
  签名: (X S : C) [CanonicallyOverClass X S]
  定义体: X ↘ S

initialize_simps_projections CanonicallyOverClass (hom -> over)

@[simps]
-/
def CanonicallyOverClass.Simps.over (X S : C) [CanonicallyOverClass X S] : X ⟶ S := X ↘ S

initialize_simps_projections CanonicallyOverClass (hom -> over)

@[simps]
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: OverClass X X
  body: ⟨𝟙 _⟩

中文:
实例 :
  签名: OverClass X X
  定义体: ⟨𝟙 _⟩
-/
instance : OverClass X X := ⟨𝟙 _⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: IsIso (S ↘ S)
  body: inferInstanceAs (IsIso (𝟙 S))

中文:
实例 :
  签名: IsIso (S ↘ S)
  定义体: inferInstanceAs (IsIso (𝟙 S))
-/
instance : IsIso (S ↘ S) := inferInstanceAs (IsIso (𝟙 S))

namespace CanonicallyOverClass
-- This cannot be a simp lemma because it loops with `comp_over`.
@[simps -isSimp]
instance (priority := 900) [CanonicallyOverClass X Y] [OverClass Y S] : OverClass X S :=
  ⟨X ↘ Y ≫ Y ↘ S⟩
end CanonicallyOverClass

/--
Definition of `HomIsOver` / `HomIsOver` 的定义

English:
class HomIsOver
  parameters: (f : X ⟶ Y) (S : C) [OverClass X S] [OverClass Y S]
  axioms and operations (1):
    - comp_over : f ≫ Y ↘ S = X ↘ S  [default: by aesop]

中文:
类 HomIsOver
  参数: (f : X ⟶ Y) (S : C) [OverClass X S] [OverClass Y S]
  公理与运算 (1 个):
    - comp_over : f ≫ Y ↘ S = X ↘ S  [默认: by aesop]
-/
class HomIsOver (f : X ⟶ Y) (S : C) [OverClass X S] [OverClass Y S] : Prop where
  comp_over : f ≫ Y ↘ S = X ↘ S := by aesop

@[reassoc (attr := simp)]
/--
lemma `comp_over` / 引理 `comp_over`

English:
lemma comp_over
  given: [OverClass X S] [OverClass Y S] [HomIsOver f S]
  proof: HomIsOver.comp_over

中文:
引理 comp_over
  条件: [OverClass X S] [OverClass Y S] [HomIsOver f S]
  证明: HomIsOver.comp_over

Depends on / 依赖: HomIsOver, HomIsOver.comp_over, comp_over
-/
lemma comp_over [OverClass X S] [OverClass Y S] [HomIsOver f S] :
    f ≫ Y ↘ S = X ↘ S :=
  HomIsOver.comp_over

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [OverClass
  signature: X S] : HomIsOver (𝟙 X) S where

中文:
实例 [OverClass
  签名: X S] : HomIsOver (𝟙 X) S where
-/
instance [OverClass X S] : HomIsOver (𝟙 X) S where

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [OverClass
  signature: X S] [OverClass Y S] [OverClass Z S]

中文:
实例 [OverClass
  签名: X S] [OverClass Y S] [OverClass Z S]
-/
instance [OverClass X S] [OverClass Y S] [OverClass Z S]
    (f : X ⟶ Y) (g : Y ⟶ Z) [HomIsOver f S] [HomIsOver g S] :
    HomIsOver (f ≫ g) S where

/--
Definition of `IsOverTower` / `IsOverTower` 的定义

English:
abbreviation IsOverTower
  signature: (X Y S : C) [OverClass X S] [OverClass Y S] [OverClass X Y]
  body: HomIsOver (X ↘ Y) S

中文:
缩写 IsOverTower
  签名: (X Y S : C) [OverClass X S] [OverClass Y S] [OverClass X Y]
  定义体: HomIsOver (X ↘ Y) S

Depends on / 依赖: HomIsOver
-/
abbrev IsOverTower (X Y S : C) [OverClass X S] [OverClass Y S] [OverClass X Y] :=
  HomIsOver (X ↘ Y) S

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [OverClass
  signature: X S] : IsOverTower X X S where

中文:
实例 [OverClass
  签名: X S] : IsOverTower X X S where
-/
instance [OverClass X S] : IsOverTower X X S where
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [OverClass
  signature: X S] : IsOverTower X S S where

中文:
实例 [OverClass
  签名: X S] : IsOverTower X S S where
-/
instance [OverClass X S] : IsOverTower X S S where

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [CanonicallyOverClass
  signature: X Y] [OverClass Y S] : IsOverTower X Y S
  body: ⟨rfl⟩

中文:
实例 [CanonicallyOverClass
  签名: X Y] [OverClass Y S] : IsOverTower X Y S
  定义体: ⟨rfl⟩
-/
instance [CanonicallyOverClass X Y] [OverClass Y S] : IsOverTower X Y S :=
  ⟨rfl⟩

/--
lemma `homIsOver_of_isOverTower` / 引理 `homIsOver_of_isOverTower`

English:
lemma homIsOver_of_isOverTower
  statement: [OverClass X S] [OverClass X S'] [OverClass Y S]
  proof: by
  constructor
  rw [← comp_over (Y ↘ S)]; rw [comp_over_assoc f]; rw [comp_over]

中文:
引理 homIsOver_of_isOverTower
  结论: [OverClass X S] [OverClass X S'] [OverClass Y S]
  证明: by
  constructor
  rw [← comp_over (Y ↘ S)]; rw [comp_over_assoc f]; rw [comp_over]

Depends on / 依赖: comp_over, comp_over_assoc
-/
lemma homIsOver_of_isOverTower [OverClass X S] [OverClass X S'] [OverClass Y S]
    [OverClass Y S'] [OverClass S S']
    [IsOverTower X S S'] [IsOverTower Y S S'] [HomIsOver f S] : HomIsOver f S' := by
  constructor
  rw [← comp_over (Y ↘ S)]; rw [comp_over_assoc f]; rw [comp_over]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [CanonicallyOverClass
  signature: X S]
  body: homIsOver_of_isOverTower f S S'

中文:
实例 [CanonicallyOverClass
  签名: X S]
  定义体: homIsOver_of_isOverTower f S S'

Depends on / 依赖: homIsOver_of_isOverTower
-/
instance [CanonicallyOverClass X S]
    [OverClass X S'] [OverClass Y S] [OverClass Y S'] [OverClass S S']
    [IsOverTower X S S'] [IsOverTower Y S S'] [HomIsOver f S] : HomIsOver f S' :=
  homIsOver_of_isOverTower f S S'

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [OverClass
  signature: X S]
  body: homIsOver_of_isOverTower f S S'

中文:
实例 [OverClass
  签名: X S]
  定义体: homIsOver_of_isOverTower f S S'

Depends on / 依赖: homIsOver_of_isOverTower
-/
instance [OverClass X S]
    [OverClass X S'] [CanonicallyOverClass Y S] [OverClass Y S'] [OverClass S S']
    [IsOverTower X S S'] [IsOverTower Y S S'] [HomIsOver f S] : HomIsOver f S' :=
  homIsOver_of_isOverTower f S S'

variable (X) in
/-- Bundle `X` with an `OverClass X S` instance into `Over S`. -/
@[simps! hom left]
/--
Definition of `OverClass.asOver` / `OverClass.asOver` 的定义

English:
definition OverClass.asOver
  signature: [OverClass X S]
  body: Over.mk (X ↘ S)

中文:
定义 OverClass.asOver
  签名: [OverClass X S]
  定义体: Over.mk (X ↘ S)

Depends on / 依赖: Over.mk
-/
def OverClass.asOver [OverClass X S] : Over S := Over.mk (X ↘ S)

/-- Bundle a morphism `f : X ⟶ Y` with `HomIsOver f S` into a morphism in `Over S`. -/
@[simps! left]
/--
Definition of `OverClass.asOverHom` / `OverClass.asOverHom` 的定义

English:
definition OverClass.asOverHom
  signature: [OverClass X S] [OverClass Y S] (f : X ⟶ Y) [HomIsOver f S]
  body: Over.homMk f (comp_over f S)

@[simps]

中文:
定义 OverClass.asOverHom
  签名: [OverClass X S] [OverClass Y S] (f : X ⟶ Y) [HomIsOver f S]
  定义体: Over.homMk f (comp_over f S)

@[simps]

Depends on / 依赖: Over.homMk, comp_over
-/
def OverClass.asOverHom [OverClass X S] [OverClass Y S] (f : X ⟶ Y) [HomIsOver f S] :
    OverClass.asOver X S ⟶ OverClass.asOver Y S :=
  Over.homMk f (comp_over f S)

@[simps]
/--
Instance `OverClass.fromOver` / 实例 `OverClass.fromOver`

English:
instance OverClass.fromOver
  signature: {S : C} (X : Over S)
  body: X.hom

中文:
实例 OverClass.fromOver
  签名: {S : C} (X : Over S)
  定义体: X.hom

Depends on / 依赖: X.hom
-/
instance OverClass.fromOver {S : C} (X : Over S) : OverClass X.left S where
  hom := X.hom

instance {S : C} {X Y : Over S} (f : X ⟶ Y) : HomIsOver f.left S where
  comp_over := Over.w f

variable [OverClass X S] [OverClass Y S] [OverClass Z S]

namespace OverClass

instance (f : X ⟶ Y) [IsIso f] [HomIsOver f S] : IsIso (asOverHom S f) :=
  have : IsIso ((Over.forget S).map (asOverHom S f)) := ‹_›
  isIso_of_reflects_iso _ (Over.forget _)

attribute [local simp] Iso.inv_comp_eq in
instance {e : X ≅ Y} [HomIsOver e.hom S] : HomIsOver e.inv S where

set_option linter.style.whitespace false in -- linter false positive
attribute [local simp ←] Iso.eq_inv_comp in
instance {e : X ≅ Y} [HomIsOver e.inv S] : HomIsOver e.hom S where

instance {f : X ⟶ Y} [IsIso f] [HomIsOver f S] : HomIsOver (asIso f).hom S where
instance {f : X ⟶ Y} [IsIso f] [HomIsOver f S] : HomIsOver (asIso f).inv S where
instance {f : X ⟶ Y} [IsIso f] [HomIsOver f S] : HomIsOver (inv f) S where

/--
lemma `asOverHom_id` / 引理 `asOverHom_id`

English:
lemma asOverHom_id
  statement: asOverHom S (𝟙 X) = 𝟙 (asOver X S)
  proof: rfl

中文:
引理 asOverHom_id
  结论: asOverHom S (𝟙 X) = 𝟙 (asOver X S)
  证明: rfl
-/
@[simp] lemma asOverHom_id : asOverHom S (𝟙 X) = 𝟙 (asOver X S) := rfl

/--
lemma `asOverHom_comp` / 引理 `asOverHom_comp`

English:
lemma asOverHom_comp
  given: (f : X ⟶ Y) (g : Y ⟶ Z) [HomIsOver f S] [HomIsOver g S]
  proof: rfl

中文:
引理 asOverHom_comp
  条件: (f : X ⟶ Y) (g : Y ⟶ Z) [HomIsOver f S] [HomIsOver g S]
  证明: rfl
-/
@[simp, reassoc] lemma asOverHom_comp (f : X ⟶ Y) (g : Y ⟶ Z) [HomIsOver f S] [HomIsOver g S] :
    asOverHom S (f ≫ g) = asOverHom S f ≫ asOverHom S g := rfl

/--
lemma `asOverHom_inv` / 引理 `asOverHom_inv`

English:
lemma asOverHom_inv
  given: (f : X ⟶ Y) [IsIso f] [HomIsOver f S]
  proof: by simp [← hom_comp_eq_id, ← asOverHom_comp]

中文:
引理 asOverHom_inv
  条件: (f : X ⟶ Y) [IsIso f] [HomIsOver f S]
  证明: by simp [← hom_comp_eq_id, ← asOverHom_comp]
-/
@[simp] lemma asOverHom_inv (f : X ⟶ Y) [IsIso f] [HomIsOver f S] :
    asOverHom S (inv f) = inv (asOverHom S f) := by simp [← hom_comp_eq_id, ← asOverHom_comp]

end OverClass

set_option backward.isDefEq.respectTransparency.types false in
/-- Reinterpret an isomorphism over an object `S` into an isomorphism in the category over `S`. -/
@[simps]
/--
Definition of `Iso.asOver` / `Iso.asOver` 的定义

English:
definition Iso.asOver
  signature: (e : X ≅ Y) [HomIsOver e.hom S]
  body: OverClass.asOverHom S e.hom
  inv := OverClass.asOverHom S e.inv

中文:
定义 Iso.asOver
  签名: (e : X ≅ Y) [HomIsOver e.hom S]
  定义体: OverClass.asOverHom S e.hom
  inv := OverClass.asOverHom S e.inv

Depends on / 依赖: OverClass, OverClass.asOverHom, asOverHom, e.hom
-/
def Iso.asOver (e : X ≅ Y) [HomIsOver e.hom S] : OverClass.asOver X S ≅ OverClass.asOver Y S where
  hom := OverClass.asOverHom S e.hom
  inv := OverClass.asOverHom S e.inv

end CategoryTheory
