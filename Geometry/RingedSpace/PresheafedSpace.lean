/-
Copyright (c) 2019 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import Mathlib.CategoryTheory.Adjunction.FullyFaithful
public import Mathlib.CategoryTheory.Elementwise
public import Mathlib.Topology.Sheaves.Presheaf

/-!
# Presheafed spaces

Introduces the category of topological spaces equipped with a presheaf (taking values in an
arbitrary target category `C`).

We further describe how to apply functors and natural transformations to the values of the
presheaves.
-/

@[expose] public section


open Opposite CategoryTheory CategoryTheory.Category CategoryTheory.Functor TopCat TopologicalSpace
  Topology

variable (C : Type*) [Category* C]

-- We could enable:
-- attribute [local aesop safe cases (rule_sets := [CategoryTheory])] Opens
-- although it doesn't appear to help in this file, in any case.

-- We could enable:
-- attribute [local aesop safe cases (rule_sets := [CategoryTheory])] Opposite
-- but this would probably require https://github.com/leanprover-community/aesop/issues/59
-- In any case, it doesn't seem to help in this file.

namespace AlgebraicGeometry

/-- A `PresheafedSpace C` is a topological space equipped with a presheaf of `C`s. -/
/-
**AlgebraicGeometry.PresheafedSpace.** 是 Mathlib 中的一个结构，位于命名空间 `AlgebraicGeometr
y`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A `PresheafedSpace C` is a topological space equipped with a presheaf of `C`s.
-/
structure PresheafedSpace.{u} where
  carrier : TopCat.{u}
  protected presheaf : carrier.Presheaf C

variable {C}

namespace PresheafedSpace

/-
**AlgebraicGeometry.PresheafedSpace.coeCarrier** 是 Mathlib 中的一个实例，位于命名空间 `Algebr
aicGeometry.PresheafedSpace`。
形式化陈述：coeCarrier : CoeOut (PresheafedSpace C) TopCat where coe X
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance coeCarrier : CoeOut (PresheafedSpace C) TopCat where coe X := X.carrier

attribute [coe] PresheafedSpace.carrier
/-
**AlgebraicGeometry.PresheafedSpace.** 是 Mathlib 中的一个实例，位于命名空间 `AlgebraicGeometr
y.PresheafedSpace`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : CoeSort (PresheafedSpace C) Type* where coe X := X.carrier
/-
**AlgebraicGeometry.PresheafedSpace.** 是 Mathlib 中的一个实例，位于命名空间 `AlgebraicGeometr
y.PresheafedSpace`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (X : PresheafedSpace C) : TopologicalSpace X :=
  X.carrier.str

/-- The constant presheaf on `X` with value `Z`. -/
/-
**AlgebraicGeometry.PresheafedSpace.const** 是 Mathlib 中的一个定义，位于命名空间 `AlgebraicGe
ometry.PresheafedSpace`。
形式化陈述：const (X : TopCat) (Z : C) : PresheafedSpace C where carrier
参数：X : TopCat；Z : C。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The constant presheaf on `X` with value `Z`.
-/
def const (X : TopCat) (Z : C) : PresheafedSpace C where
  carrier := X
  presheaf := (Functor.const _).obj Z
/-
**AlgebraicGeometry.PresheafedSpace.** 是 Mathlib 中的一个实例，位于命名空间 `AlgebraicGeometr
y.PresheafedSpace`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Inhabited C] : Inhabited (PresheafedSpace C) :=
  ⟨const (TopCat.of PEmpty) default⟩

/-- A morphism between presheafed spaces `X` and `Y` consists of a continuous map
`f` between the underlying topological spaces, and a (note: contravariant!) map
from the presheaf on `Y` to the pushforward of the presheaf on `X` via `f`. -/
/-
**AlgebraicGeometry.PresheafedSpace.Hom** 是 Mathlib 中的一个归纳类型，位于命名空间 `AlgebraicGe
ometry.PresheafedSpace`。
形式化陈述：{C : Type u_1} →   [inst : CategoryTheory.Category.{v_1, u_1} C] →     Alg
ebraicGeometry.PresheafedSpace C → AlgebraicGeometry.PresheafedSpace C → Type (m
ax u_2 v_1)
参数：max u_2 v_1。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A morphism between presheafed spaces `X` and `Y` consists of a continuous map
`f` between the underlying topological spaces, and a (note: contravariant!) map
from the presheaf on `Y` to the pushforward of the presheaf on `X` via `f`.
-/
structure Hom (X Y : PresheafedSpace C) where
  base : (X : TopCat) ⟶ (Y : TopCat)
  c : Y.presheaf ⟶ base _* X.presheaf

@[ext (iff := false)]
/-
**AlgebraicGeometry.PresheafedSpace.Hom.ext** 是 Mathlib 中的一个定理，位于命名空间 `Algebraic
Geometry.PresheafedSpace.Hom`。
形式化陈述：∀ {C : Type u_1} [inst : CategoryTheory.Category.{v_1, u_1} C] {X Y : Alge
braicGeometry.PresheafedSpace C}   (α β : X.Hom Y) (w : α.base = β.base),   Cate
goryTheory.CategoryStruct.comp α.c (CategoryTheory.Functor.whiskerRight (Categor
yTheory.eqToHom ⋯) X.presheaf) =       β.c →     α = β
参数：α β : X.Hom Y；w : α.base = β.base；CategoryTheory.Functor.whiskerRight (Catego
ryTheory.eqToHom ⋯) X.presheaf。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `CategoryTheory.Functor.whiskerRight_id'`：whiskerRight_id' {G : C ⥤ D} (F
 : D ⥤ E) : whiskerRight (𝟙 G) F = 𝟙 (G.comp F)
-/
theorem Hom.ext {X Y : PresheafedSpace C} (α β : Hom X Y) (w : α.base = β.base)
    (h : α.c ≫ whiskerRight (eqToHom (by rw [w])) _ = β.c) : α = β := by
  rcases α with ⟨base, c⟩
  rcases β with ⟨base', c'⟩
  dsimp at w
  subst w
  dsimp at h
  erw [whiskerRight_id', comp_id] at h
  subst h
  rfl

-- TODO including `injections` would make tidy work earlier.
/-
**AlgebraicGeometry.PresheafedSpace.hext** 是 Mathlib 中的一个定理，位于命名空间 `AlgebraicGeo
metry.PresheafedSpace`。
形式化陈述：hext {X Y : PresheafedSpace C} (α β : Hom X Y) (w : α.base = β.base) (h : 
α.c ≍ β.c) : α = β
参数：α β : Hom X Y；w : α.base = β.base；h : α.c ≍ β.c。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `heq_of_eq`：∀ {α : Sort u_1} {a a' : α}, a = a' → a ≍ a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem hext {X Y : PresheafedSpace C} (α β : Hom X Y) (w : α.base = β.base) (h : α.c ≍ β.c) :
    α = β := by
  cases α
  cases β
  congr

/-- The identity morphism of a `PresheafedSpace`. -/
/-
**AlgebraicGeometry.PresheafedSpace.id** 是 Mathlib 中的一个定义，位于命名空间 `AlgebraicGeome
try.PresheafedSpace`。
形式化陈述：id (X : PresheafedSpace C) : Hom X X where base
参数：X : PresheafedSpace C。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The identity morphism of a `PresheafedSpace`.
-/
def id (X : PresheafedSpace C) : Hom X X where
  base := 𝟙 (X : TopCat)
  c := 𝟙 _
/-
**AlgebraicGeometry.PresheafedSpace.homInhabited** 是 Mathlib 中的一个实例，位于命名空间 `Alge
braicGeometry.PresheafedSpace`。
形式化陈述：homInhabited (X : PresheafedSpace C) : Inhabited (Hom X X)
参数：X : PresheafedSpace C。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance homInhabited (X : PresheafedSpace C) : Inhabited (Hom X X) :=
  ⟨id X⟩

/-- Composition of morphisms of `PresheafedSpace`s. -/
/-
**AlgebraicGeometry.PresheafedSpace.comp** 是 Mathlib 中的一个定义，位于命名空间 `AlgebraicGeo
metry.PresheafedSpace`。
形式化陈述：comp {X Y Z : PresheafedSpace C} (α : Hom X Y) (β : Hom Y Z) : Hom X Z whe
re base
参数：α : Hom X Y；β : Hom Y Z。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Composition of morphisms of `PresheafedSpace`s.
-/
def comp {X Y Z : PresheafedSpace C} (α : Hom X Y) (β : Hom Y Z) : Hom X Z where
  base := α.base ≫ β.base
  c := β.c ≫ (Presheaf.pushforward _ β.base).map α.c
/-
**AlgebraicGeometry.PresheafedSpace.comp_c** 是 Mathlib 中的一个定理，位于命名空间 `AlgebraicG
eometry.PresheafedSpace`。
形式化陈述：comp_c {X Y Z : PresheafedSpace C} (α : Hom X Y) (β : Hom Y Z) : (comp α β
).c = β.c ≫ (Presheaf.pushforward _ β.base).map α.c
参数：α : Hom X Y；β : Hom Y Z。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem comp_c {X Y Z : PresheafedSpace C} (α : Hom X Y) (β : Hom Y Z) :
    (comp α β).c = β.c ≫ (Presheaf.pushforward _ β.base).map α.c :=
  rfl

variable (C)

section

attribute [local simp] id comp

set_option backward.isDefEq.respectTransparency false in
/-- The category of PresheafedSpaces. Morphisms are pairs, a continuous map and a presheaf map
from the presheaf on the target to the pushforward of the presheaf on the source. -/
/-
**AlgebraicGeometry.PresheafedSpace.categoryOfPresheafedSpaces** 是 Mathlib 中的一个实
例，位于命名空间 `AlgebraicGeometry.PresheafedSpace`。
形式化陈述：categoryOfPresheafedSpaces : Category (PresheafedSpace C) where Hom
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The category of PresheafedSpaces. Morphisms are pairs, a continuous map and a pr
esheaf map
from the presheaf on the target to the pushforward of the presheaf on the source
.
-/
instance categoryOfPresheafedSpaces : Category (PresheafedSpace C) where
  Hom := Hom
  id := id
  comp := comp

variable {C}

/-- Cast `Hom X Y` as an arrow `X ⟶ Y` of presheaves. -/
/-
**AlgebraicGeometry.PresheafedSpace.Hom.toPshHom** 是 Mathlib 中的一个定义，位于命名空间 `Alge
braicGeometry.PresheafedSpace.Hom`。
形式化陈述：{C : Type u_1} →   [inst : CategoryTheory.Category.{v_1, u_1} C] → {X Y : 
AlgebraicGeometry.PresheafedSpace C} → X.Hom Y → (X ⟶ Y)
参数：X ⟶ Y。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Cast `Hom X Y` as an arrow `X ⟶ Y` of presheaves.
-/
abbrev Hom.toPshHom {X Y : PresheafedSpace C} (f : Hom X Y) : X ⟶ Y := f

@[ext (iff := false)]
/-
**AlgebraicGeometry.PresheafedSpace.ext** 是 Mathlib 中的一个定理，位于命名空间 `AlgebraicGeom
etry.PresheafedSpace`。
形式化陈述：ext {X Y : PresheafedSpace C} (α β : X ⟶ Y) (w : α.base = β.base) (h : α.c
 ≫ whiskerRight (eqToHom (by rw [w])) _ = β.c) : α = β
参数：α β : X ⟶ Y；w : α.base = β.base；h : α.c ≫ whiskerRight (eqToHom (by rw [w])) 
_ = β.c。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AlgebraicGeometry.PresheafedSpace.Hom.ext`：∀ {C : Type u_1} [inst : Cate
goryTheory.Category.{v_1, u_1} C] {X Y : AlgebraicGeometry.PresheafedSpace C}   
(α β : X.Hom Y) (w : α.base = β…
-/
theorem ext {X Y : PresheafedSpace C} (α β : X ⟶ Y) (w : α.base = β.base)
    (h : α.c ≫ whiskerRight (eqToHom (by rw [w])) _ = β.c) : α = β :=
  Hom.ext α β w h

end

variable {C}

attribute [local simp] eqToHom_map

@[simp]
/-
**AlgebraicGeometry.PresheafedSpace.id_base** 是 Mathlib 中的一个定理，位于命名空间 `Algebraic
Geometry.PresheafedSpace`。
形式化陈述：id_base (X : PresheafedSpace C) : (𝟙 X : X ⟶ X).base = 𝟙 (X : TopCat)
参数：X : PresheafedSpace C。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem id_base (X : PresheafedSpace C) : (𝟙 X : X ⟶ X).base = 𝟙 (X : TopCat) :=
  rfl
/-
**AlgebraicGeometry.PresheafedSpace.id_c** 是 Mathlib 中的一个定理，位于命名空间 `AlgebraicGeo
metry.PresheafedSpace`。
形式化陈述：id_c (X : PresheafedSpace C) : (𝟙 X : X ⟶ X).c = 𝟙 X.presheaf
参数：X : PresheafedSpace C。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem id_c (X : PresheafedSpace C) :
    (𝟙 X : X ⟶ X).c = 𝟙 X.presheaf :=
  rfl

set_option backward.isDefEq.respectTransparency.types false in
@[simp]
/-
**AlgebraicGeometry.PresheafedSpace.id_c_app** 是 Mathlib 中的一个定理，位于命名空间 `Algebrai
cGeometry.PresheafedSpace`。
形式化陈述：id_c_app (X : PresheafedSpace C) (U) : (𝟙 X : X ⟶ X).c.app U = X.presheaf.
map (𝟙 U)
参数：X : PresheafedSpace C；U。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `AlgebraicGeometry.PresheafedSpace.id_c`：id_c (X : PresheafedSpace C) : (
𝟙 X : X ⟶ X).c = 𝟙 X.presheaf
· 使用定理 `CategoryTheory.Functor.map_id`：∀ {C : Type u₁} [inst : CategoryTheory.Ca
tegory.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]  
 (self : CategoryTh…
-/
theorem id_c_app (X : PresheafedSpace C) (U) :
    (𝟙 X : X ⟶ X).c.app U = X.presheaf.map (𝟙 U) := by
  rw [id_c, map_id]
  rfl

@[simp, reassoc]
/-
**AlgebraicGeometry.PresheafedSpace.comp_base** 是 Mathlib 中的一个定理，位于命名空间 `Algebra
icGeometry.PresheafedSpace`。
形式化陈述：comp_base {X Y Z : PresheafedSpace C} (f : X ⟶ Y) (g : Y ⟶ Z) : (f ≫ g).ba
se = f.base ≫ g.base
参数：f : X ⟶ Y；g : Y ⟶ Z。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem comp_base {X Y Z : PresheafedSpace C} (f : X ⟶ Y) (g : Y ⟶ Z) :
    (f ≫ g).base = f.base ≫ g.base :=
  rfl
/-
**AlgebraicGeometry.PresheafedSpace.** 是 Mathlib 中的一个实例，位于命名空间 `AlgebraicGeometr
y.PresheafedSpace`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (X Y : PresheafedSpace C) : CoeFun (X ⟶ Y) fun _ => (↑X → ↑Y) :=
  ⟨fun f => f.base⟩

/-!
Note that we don't include a `ConcreteCategory` instance, since equality of morphisms `X ⟶ Y`
does not follow from equality of their coercions `X → Y`.
-/

-- The `reassoc` attribute was added despite the LHS not being a composition of two homs,
-- for the reasons explained in the docstring.
-- As there is no composition in the LHS it is purposely `@[reassoc, simp]` rather
-- than `@[reassoc (attr := simp)]`
set_option backward.isDefEq.respectTransparency false in -- Needed in HasColimits.lean
/-- Sometimes rewriting with `comp_c_app` doesn't work because of dependent type issues.
In that case, `erw comp_c_app_assoc` might make progress.
The lemma `comp_c_app_assoc` is also better suited for rewrites in the opposite direction. -/
@[reassoc, simp]
/-
**AlgebraicGeometry.PresheafedSpace.comp_c_app** 是 Mathlib 中的一个定理，位于命名空间 `Algebr
aicGeometry.PresheafedSpace`。
形式化陈述：comp_c_app {X Y Z : PresheafedSpace C} (α : X ⟶ Y) (β : Y ⟶ Z) (U) : (α ≫ 
β).c.app U = β.c.app U ≫ α.c.app (op ((Opens.map β.base).obj (unop U)))
参数：α : X ⟶ Y；β : Y ⟶ Z；U。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Sometimes rewriting with `comp_c_app` doesn't work because of dependent type iss
ues.
In that case, `erw comp_c_app_assoc` might make progress.
The lemma `comp_c_app_assoc` is also better suited for rewrites in the opposite 
direction.
-/
theorem comp_c_app {X Y Z : PresheafedSpace C} (α : X ⟶ Y) (β : Y ⟶ Z) (U) :
    (α ≫ β).c.app U = β.c.app U ≫ α.c.app (op ((Opens.map β.base).obj (unop U))) :=
  rfl

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-
**AlgebraicGeometry.PresheafedSpace.congr_app** 是 Mathlib 中的一个定理，位于命名空间 `Algebra
icGeometry.PresheafedSpace`。
形式化陈述：congr_app {X Y : PresheafedSpace C} {α β : X ⟶ Y} (h : α = β) (U) : α.c.ap
p U = β.c.app U ≫ X.presheaf.map (eqToHom (by subst h; rfl))
参数：h : α = β；U。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Functor.map_id`：∀ {C : Type u₁} [inst : CategoryTheory.Ca
tegory.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]  
 (self : CategoryTh…
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem congr_app {X Y : PresheafedSpace C} {α β : X ⟶ Y} (h : α = β) (U) :
    α.c.app U = β.c.app U ≫ X.presheaf.map (eqToHom (by subst h; rfl)) := by
  subst h
  simp

section

variable (C)

/-- The forgetful functor from `PresheafedSpace` to `TopCat`. -/
@[simps]
/-
**AlgebraicGeometry.PresheafedSpace.forget** 是 Mathlib 中的一个定义，位于命名空间 `AlgebraicG
eometry.PresheafedSpace`。
形式化陈述：forget : PresheafedSpace C ⥤ TopCat where obj X
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The forgetful functor from `PresheafedSpace` to `TopCat`.
-/
def forget : PresheafedSpace C ⥤ TopCat where
  obj X := (X : TopCat)
  map f := f.base

end

section Iso

variable {X Y : PresheafedSpace C}

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- An isomorphism of `PresheafedSpace`s is a homeomorphism of the underlying space, and a
natural transformation between the sheaves.
-/
@[simps hom inv]
/-
**AlgebraicGeometry.PresheafedSpace.isoOfComponents** 是 Mathlib 中的一个定义，位于命名空间 `A
lgebraicGeometry.PresheafedSpace`。
形式化陈述：isoOfComponents (H : X.1 ≅ Y.1) (α : H.hom _* X.2 ≅ Y.2) : X ≅ Y where hom
参数：H : X.1 ≅ Y.1；α : H.hom _* X.2 ≅ Y.2。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An isomorphism of `PresheafedSpace`s is a homeomorphism of the underlying space,
 and a
natural transformation between the sheaves.
-/
def isoOfComponents (H : X.1 ≅ Y.1) (α : H.hom _* X.2 ≅ Y.2) : X ≅ Y where
  hom :=
    { base := H.hom
      c := α.inv }
  inv :=
    { base := H.inv
      c := Presheaf.toPushforwardOfIso H α.hom }
  hom_inv_id := by ext <;> simp
  inv_hom_id := by
    ext
    · dsimp
      exact H.inv_hom_id_apply _
    dsimp
    simp only [Presheaf.toPushforwardOfIso_app, assoc, ← α.hom.naturality]
    simp only [eqToHom_map, eqToHom_app, eqToHom_trans_assoc, eqToHom_refl, id_comp]
    apply Iso.inv_hom_id_app

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- Isomorphic `PresheafedSpace`s have naturally isomorphic presheaves. -/
@[simps]
/-
**AlgebraicGeometry.PresheafedSpace.sheafIsoOfIso** 是 Mathlib 中的一个定义，位于命名空间 `Alg
ebraicGeometry.PresheafedSpace`。
形式化陈述：sheafIsoOfIso (H : X ≅ Y) : Y.2 ≅ H.hom.base _* X.2 where hom
参数：H : X ≅ Y。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Isomorphic `PresheafedSpace`s have naturally isomorphic presheaves.
-/
def sheafIsoOfIso (H : X ≅ Y) : Y.2 ≅ H.hom.base _* X.2 where
  hom := H.hom.c
  inv := Presheaf.pushforwardToOfIso ((forget _).mapIso H).symm H.inv.c
  hom_inv_id := by
    ext U
    rw [NatTrans.comp_app]
    simpa using! congr_arg (fun f => f ≫ eqToHom _) (congr_app H.inv_hom_id (op U))
  inv_hom_id := by
    ext U
    dsimp
    rw [NatTrans.id_app]
    simp only [Presheaf.pushforwardToOfIso_app, Iso.symm_inv, mapIso_hom, forget_map,
      Iso.symm_hom, mapIso_inv, eqToHom_map, assoc]
    have eq₁ := congr_app H.hom_inv_id (op ((Opens.map H.hom.base).obj U))
    have eq₂ := H.hom.c.naturality (eqToHom (congr_obj (congr_arg Opens.map
      ((forget C).congr_map H.inv_hom_id.symm)) U)).op
    rw [id_c, NatTrans.id_app, id_comp, eqToHom_map, comp_c_app] at eq₁
    rw [eqToHom_op, eqToHom_map] at eq₂
    erw [eq₂, reassoc_of% eq₁]
    simp
/-
**AlgebraicGeometry.PresheafedSpace.base_isIso_of_iso** 是 Mathlib 中的一个实例，位于命名空间 
`AlgebraicGeometry.PresheafedSpace`。
形式化陈述：base_isIso_of_iso (f : X ⟶ Y) [IsIso f] : IsIso f.base
参数：f : X ⟶ Y。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Iso.isIso_hom`：∀ {C : Type u} [inst : CategoryTheory.Cate
gory.{v, u} C] {X Y : C} (e : X ≅ Y), CategoryTheory.IsIso e.hom
-/
instance base_isIso_of_iso (f : X ⟶ Y) [IsIso f] : IsIso f.base :=
  ((forget _).mapIso (asIso f)).isIso_hom
/-
**AlgebraicGeometry.PresheafedSpace.c_isIso_of_iso** 是 Mathlib 中的一个实例，位于命名空间 `Al
gebraicGeometry.PresheafedSpace`。
形式化陈述：c_isIso_of_iso (f : X ⟶ Y) [IsIso f] : IsIso f.c
参数：f : X ⟶ Y。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Iso.isIso_hom`：∀ {C : Type u} [inst : CategoryTheory.Cate
gory.{v, u} C] {X Y : C} (e : X ≅ Y), CategoryTheory.IsIso e.hom
-/
instance c_isIso_of_iso (f : X ⟶ Y) [IsIso f] : IsIso f.c :=
  (sheafIsoOfIso (asIso f)).isIso_hom

/-- This could be used in conjunction with `CategoryTheory.NatIso.isIso_of_isIso_app`. -/
/-
**AlgebraicGeometry.PresheafedSpace.isIso_of_components** 是 Mathlib 中的一个定理，位于命名空
间 `AlgebraicGeometry.PresheafedSpace`。
形式化陈述：isIso_of_components (f : X ⟶ Y) [IsIso f.base] [IsIso f.c] : IsIso f
参数：f : X ⟶ Y。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Iso.isIso_hom`：∀ {C : Type u} [inst : CategoryTheory.Cate
gory.{v, u} C] {X Y : C} (e : X ≅ Y), CategoryTheory.IsIso e.hom

--- 原说明 ---
This could be used in conjunction with `CategoryTheory.NatIso.isIso_of_isIso_app
`.
-/
theorem isIso_of_components (f : X ⟶ Y) [IsIso f.base] [IsIso f.c] : IsIso f :=
  (isoOfComponents (asIso f.base) (asIso f.c).symm).isIso_hom

end Iso

section Restrict

/-- The restriction of a presheafed space along an open embedding into the space.
-/
@[simps]
/-
**AlgebraicGeometry.PresheafedSpace.restrict** 是 Mathlib 中的一个定义，位于命名空间 `Algebrai
cGeometry.PresheafedSpace`。
形式化陈述：restrict {U : TopCat} (X : PresheafedSpace C) {f : U ⟶ (X : TopCat)} (h : 
IsOpenEmbedding f) : PresheafedSpace C where carrier
参数：X : PresheafedSpace C；X : TopCat；h : IsOpenEmbedding f。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The restriction of a presheafed space along an open embedding into the space.
-/
def restrict {U : TopCat} (X : PresheafedSpace C) {f : U ⟶ (X : TopCat)}
    (h : IsOpenEmbedding f) : PresheafedSpace C where
  carrier := U
  presheaf := h.functor.op ⋙ X.presheaf

set_option backward.isDefEq.respectTransparency false in
/-- The map from the restriction of a presheafed space.
-/
@[simps]
/-
**AlgebraicGeometry.PresheafedSpace.ofRestrict** 是 Mathlib 中的一个定义，位于命名空间 `Algebr
aicGeometry.PresheafedSpace`。
形式化陈述：ofRestrict {U : TopCat} (X : PresheafedSpace C) {f : U ⟶ (X : TopCat)} (h 
: IsOpenEmbedding f) : X.restrict h ⟶ X where base
参数：X : PresheafedSpace C；X : TopCat；h : IsOpenEmbedding f。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The map from the restriction of a presheafed space.
-/
def ofRestrict {U : TopCat} (X : PresheafedSpace C) {f : U ⟶ (X : TopCat)}
    (h : IsOpenEmbedding f) : X.restrict h ⟶ X where
  base := f
  c :=
    { app := fun V => X.presheaf.map (h.isOpenMap.adjunction.counit.app V.unop).op
      naturality := fun U V f =>
        show _ = _ ≫ X.presheaf.map _ by
          rw [← map_comp, ← map_comp]
          rfl }

set_option backward.isDefEq.respectTransparency false in
/-
**AlgebraicGeometry.PresheafedSpace.ofRestrict_mono** 是 Mathlib 中的一个实例，位于命名空间 `A
lgebraicGeometry.PresheafedSpace`。
形式化陈述：ofRestrict_mono {U : TopCat} (X : PresheafedSpace C) (f : U ⟶ X.1) (hf : I
sOpenEmbedding f) : Mono (X.ofRestrict hf)
参数：X : PresheafedSpace C；f : U ⟶ X.1；hf : IsOpenEmbedding f。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `TopCat.mono_iff_injective`：mono_iff_injective {X Y : TopCat.{u}} (f : X 
⟶ Y) : Mono f ↔ Function.Injective f
· 使用定理 `Topology.IsEmbedding.injective`：∀ {X : Type u_1} {Y : Type u_2} [tX : To
pologicalSpace X] [tY : TopologicalSpace Y] {f : X → Y},   Topology.IsEmbedding 
f → Function.Injecti…
· 使用定理 `Topology.IsOpenEmbedding.toIsEmbedding`：∀ {X : Type u_1} {Y : Type u_2} 
[tX : TopologicalSpace X] [tY : TopologicalSpace Y] {f : X → Y},   Topology.IsOp
enEmbedding f → Topology.IsE…
· 使用定理 `AlgebraicGeometry.PresheafedSpace.ext`：ext {X Y : PresheafedSpace C} (α 
β : X ⟶ Y) (w : α.base = β.base) (h : α.c ≫ whiskerRight (eqToHom (by rw [w])) _
 = β.c) : α = β
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.cancel_mono`：∀ {C : Type u} [inst : CategoryTheory.Catego
ry.{v, u} C] {X Y Z : C} (f : Y ⟶ X) [CategoryTheory.Mono f] {g h : Z ⟶ Y},   Ca
tegoryTheory.Cat…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `AlgebraicGeometry.PresheafedSpace.ofRestrict_base`：∀ {C : Type u_1} [ins
t : CategoryTheory.Category.{v_1, u_1} C] {U : TopCat} (X : AlgebraicGeometry.Pr
esheafedSpace C)   {f : U ⟶ ↑X} (h : To…
· 使用引理 `TopCat.Presheaf.ext`：ext {X : TopCat.{w}} {P Q : Presheaf C X} {f g : P 
⟶ Q} (w : forall U : Opens X, f.app (op U) = g.app (op U)) : f = g
· 使用定理 `TopologicalSpace.Opens.ext`：ext {U V : Opens α} (h : (U : Set α) = V) : 
U = V
· 使用定理 `Set.preimage_image_eq`：preimage_image_eq {f : α -> β} (s : Set α) (h : I
njective f) : f ⁻¹' f '' s = s
· 使用定理 `Topology.IsOpenEmbedding.isOpenMap`：∀ {X : Type u_1} {Y : Type u_2} {f :
 X → Y} [inst : TopologicalSpace X] [inst_1 : TopologicalSpace Y],   Topology.Is
OpenEmbedding f → IsOpen…
· 使用定理 `CategoryTheory.NatIso.isIso_app_of_isIso`：∀ {C : Type u₁} [inst : Catego
ryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v
₂, u₂} D]   {F G : CategoryThe…
· 使用定理 `IsOpenMap.functor_faithful`：∀ {X Y : TopCat} {f : X ⟶ Y} (hf : IsOpenMap
 ⇑(CategoryTheory.ConcreteCategory.hom f)), hf.functor.Faithful
· 使用定理 `AlgebraicGeometry.PresheafedSpace.congr_app`：congr_app {X Y : Presheafed
Space C} {α β : X ⟶ Y} (h : α = β) (U) : α.c.app U = β.c.app U ≫ X.presheaf.map 
(eqToHom (by subst h; rfl))
· 使用定理 `CategoryTheory.cancel_epi`：cancel_epi (f : X ⟶ Y) [Epi f] {g h : Y ⟶ Z} 
: f ≫ g = f ≫ h ↔ g = h
· 使用定理 `CategoryTheory.StrongEpi.epi`：∀ {C : Type u} {inst : CategoryTheory.Cate
gory.{v, u} C} {P Q : C} {f : P ⟶ Q} [self : CategoryTheory.StrongEpi f],   Cate
goryTheory.Epi f
· 使用定理 `CategoryTheory.strongEpi_of_isIso`：∀ {C : Type u} [inst : CategoryTheory
.Category.{v, u} C] {P Q : C} (f : P ⟶ Q) [CategoryTheory.IsIso f],   CategoryTh
eory.StrongEpi f
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `AlgebraicGeometry.PresheafedSpace.ofRestrict_c_app`：∀ {C : Type u_1} [in
st : CategoryTheory.Category.{v_1, u_1} C] {U : TopCat} (X : AlgebraicGeometry.P
resheafedSpace C)   {f : U ⟶ ↑X} (h : To…
· 使用定理 `AlgebraicGeometry.PresheafedSpace.comp_c_app`：comp_c_app {X Y Z : Preshe
afedSpace C} (α : X ⟶ Y) (β : Y ⟶ Z) (U) : (α ≫ β).c.app U = β.c.app U ≫ α.c.app
 (op ((Opens.map β.base).obj (unop…
· 使用定理 `CategoryTheory.Functor.congr_obj`：congr_obj {F G : C ⥤ D} (h : F = G) (X
) : F.obj X = G.obj X
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `CategoryTheory.eqToHom_app`：eqToHom_app {F G : C ⥤ D} (h : F = G) (X : C
) : (eqToHom h : F ⟶ G).app X = eqToHom (Functor.congr_obj h X)
· 使用定理 `CategoryTheory.eqToHom_map`：eqToHom_map (F : C ⥤ D) {X Y : C} (p : X = Y
) : F.map (eqToHom p) = eqToHom (congr_arg F.obj p)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.instIsIsoEqToHom`：∀ {C : Type u₁} [inst : CategoryTheory.
Category.{v₁, u₁} C] {X Y : C} (h : X = Y),   CategoryTheory.IsIso (CategoryTheo
ry.eqToHom h)
（共 35 条，此处仅展示前 30 条）
-/
instance ofRestrict_mono {U : TopCat} (X : PresheafedSpace C) (f : U ⟶ X.1)
    (hf : IsOpenEmbedding f) : Mono (X.ofRestrict hf) := by
  have : Mono f := (TopCat.mono_iff_injective _).mpr hf.injective
  constructor
  intro Z g₁ g₂ eq
  ext1
  · have := congr_arg PresheafedSpace.Hom.base eq
    simp only [PresheafedSpace.comp_base, PresheafedSpace.ofRestrict_base] at this
    rw [cancel_mono] at this
    exact this
  · ext V
    have hV : (Opens.map (X.ofRestrict hf).base).obj (hf.functor.obj V) = V := by
      ext1
      exact Set.preimage_image_eq _ hf.injective
    have :
      IsIso (hf.isOpenMap.adjunction.counit.app (unop (op (hf.functor.obj V)))) :=
        NatIso.isIso_app_of_isIso
          (whiskerLeft hf.functor hf.isOpenMap.adjunction.counit) V
    have := PresheafedSpace.congr_app eq (op (hf.functor.obj V))
    rw [PresheafedSpace.comp_c_app, PresheafedSpace.comp_c_app,
      PresheafedSpace.ofRestrict_c_app, Category.assoc, cancel_epi] at this
    have h : _ ≫ _ = _ ≫ _ ≫ _ :=
      congr_arg (fun f => (X.restrict hf).presheaf.map (eqToHom hV).op ≫ f) this
    simp only [g₁.c.naturality, g₂.c.naturality_assoc] at h
    simp only [eqToHom_op, eqToHom_map, eqToHom_trans,
      ← IsIso.comp_inv_eq, inv_eqToHom, Category.assoc] at h
    simpa using h

set_option backward.defeqAttrib.useBackward true in
/-
**AlgebraicGeometry.PresheafedSpace.restrict_top_presheaf** 是 Mathlib 中的一个定理，位于命
名空间 `AlgebraicGeometry.PresheafedSpace`。
形式化陈述：restrict_top_presheaf (X : PresheafedSpace C) : (X.restrict (Opens.isOpenE
mbedding ⊤)).presheaf = (Opens.inclusionTopIso X.carrier).inv _* X.presheaf
参数：X : PresheafedSpace C。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `TopologicalSpace.Opens.isOpenEmbedding`：isOpenEmbedding {X : TopCat.{u}}
 (U : Opens X) : IsOpenEmbedding (inclusion' U)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `TopologicalSpace.Opens.inclusion'_top_functor`：∀ (X : TopCat), ⋯.functor
 = TopologicalSpace.Opens.map (TopologicalSpace.Opens.inclusionTopIso X).inv
-/
theorem restrict_top_presheaf (X : PresheafedSpace C) :
    (X.restrict (Opens.isOpenEmbedding ⊤)).presheaf =
      (Opens.inclusionTopIso X.carrier).inv _* X.presheaf := by
  dsimp
  rw [Opens.inclusion'_top_functor X.carrier]
  rfl

set_option backward.isDefEq.respectTransparency false in
/-
**AlgebraicGeometry.PresheafedSpace.ofRestrict_top_c** 是 Mathlib 中的一个定理，位于命名空间 `
AlgebraicGeometry.PresheafedSpace`。
形式化陈述：ofRestrict_top_c (X : PresheafedSpace C) : (X.ofRestrict (Opens.isOpenEmbe
dding ⊤)).c = eqToHom (by rw [restrict_top_presheaf]; rw [← Presheaf.Pushforward
.comp_eq] tauto)
参数：X : PresheafedSpace C。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `TopCat.Presheaf.ext`：ext {X : TopCat.{w}} {P Q : Presheaf C X} {f g : P 
⟶ Q} (w : forall U : Opens X, f.app (op U) = g.app (op U)) : f = g
· 使用定理 `TopologicalSpace.Opens.isOpenEmbedding`：isOpenEmbedding {X : TopCat.{u}}
 (U : Opens X) : IsOpenEmbedding (inclusion' U)
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `TopologicalSpace.Opens.functor_map_eq_inf`：functor_map_eq_inf {X : TopCa
t.{u}} (U V : Opens X) : U.isOpenEmbedding.functor.obj ((Opens.map U.inclusion')
.obj V) = V ⊓ U
· 使用定理 `inf_of_le_left`：∀ {α : Type u} [inst : SemilatticeInf α] {a b : α}, a ≤ 
b → a ⊓ b = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `CategoryTheory.eqToHom_map`：eqToHom_map (F : C ⥤ D) {X Y : C} (p : X = Y
) : F.map (eqToHom p) = eqToHom (congr_arg F.obj p)
· 使用定理 `CategoryTheory.Functor.congr_obj`：congr_obj {F G : C ⥤ D} (h : F = G) (X
) : F.obj X = G.obj X
· 使用定理 `CategoryTheory.eqToHom_app`：eqToHom_app {F G : C ⥤ D} (h : F = G) (X : C
) : (eqToHom h : F ⟶ G).app X = eqToHom (Functor.congr_obj h X)
-/
theorem ofRestrict_top_c (X : PresheafedSpace C) :
    (X.ofRestrict (Opens.isOpenEmbedding ⊤)).c =
      eqToHom
        (by
          rw [restrict_top_presheaf, ← Presheaf.Pushforward.comp_eq]
          tauto) := by
  /- another approach would be to prove the left-hand side
       is a natural isomorphism, but I encountered a universe
       issue when `apply NatIso.isIso_of_isIso_app`. -/
  ext
  dsimp [ofRestrict]
  erw [eqToHom_map, eqToHom_app]
  simp

/-- The map to the restriction of a presheafed space along the canonical inclusion from the top
subspace.
-/
@[simps]
/-
**AlgebraicGeometry.PresheafedSpace.toRestrictTop** 是 Mathlib 中的一个定义，位于命名空间 `Alg
ebraicGeometry.PresheafedSpace`。
形式化陈述：toRestrictTop (X : PresheafedSpace C) : X ⟶ X.restrict (Opens.isOpenEmbedd
ing ⊤) where base
参数：X : PresheafedSpace C。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `AlgebraicGeometry.PresheafedSpace.restrict_top_presheaf`：restrict_top_pr
esheaf (X : PresheafedSpace C) : (X.restrict (Opens.isOpenEmbedding ⊤)).presheaf
 = (Opens.inclusionTopIso X.carrier).inv _* X…

--- 原说明 ---
The map to the restriction of a presheafed space along the canonical inclusion f
rom the top
subspace.
-/
def toRestrictTop (X : PresheafedSpace C) : X ⟶ X.restrict (Opens.isOpenEmbedding ⊤) where
  base := (Opens.inclusionTopIso X.carrier).inv
  c := eqToHom (restrict_top_presheaf X)

/-- The isomorphism from the restriction to the top subspace.
-/
@[simps]
/-
**AlgebraicGeometry.PresheafedSpace.restrictTopIso** 是 Mathlib 中的一个定义，位于命名空间 `Al
gebraicGeometry.PresheafedSpace`。
形式化陈述：restrictTopIso (X : PresheafedSpace C) : X.restrict (Opens.isOpenEmbedding
 ⊤) ≅ X where hom
参数：X : PresheafedSpace C。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The isomorphism from the restriction to the top subspace.
-/
def restrictTopIso (X : PresheafedSpace C) : X.restrict (Opens.isOpenEmbedding ⊤) ≅ X where
  hom := X.ofRestrict _
  inv := X.toRestrictTop
  hom_inv_id := by
    ext
    · rfl
    · erw [comp_c, toRestrictTop_c, whiskerRight_id',
        comp_id, ofRestrict_top_c, eqToHom_map, eqToHom_trans, eqToHom_refl]
      rfl
  inv_hom_id := by
    ext
    · rfl
    · erw [comp_c, ofRestrict_top_c, toRestrictTop_c, eqToHom_map, whiskerRight_id', comp_id,
        eqToHom_trans, eqToHom_refl]
      rfl

end Restrict

/-- The global sections, notated Gamma.
-/
@[simps]
/-
**AlgebraicGeometry.PresheafedSpace.** 是 Mathlib 中的一个定义，位于命名空间 `AlgebraicGeometr
y.PresheafedSpace`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The global sections, notated Gamma.
-/
def Γ : (PresheafedSpace C)ᵒᵖ ⥤ C where
  obj X := (unop X).presheaf.obj (op ⊤)
  map f := f.unop.c.app (op ⊤)
/-
**AlgebraicGeometry.PresheafedSpace.** 是 Mathlib 中的一个定理，位于命名空间 `AlgebraicGeometr
y.PresheafedSpace`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem Γ_obj_op (X : PresheafedSpace C) : Γ.obj (op X) = X.presheaf.obj (op ⊤) :=
  rfl
/-
**AlgebraicGeometry.PresheafedSpace.** 是 Mathlib 中的一个定理，位于命名空间 `AlgebraicGeometr
y.PresheafedSpace`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem Γ_map_op {X Y : PresheafedSpace C} (f : X ⟶ Y) : Γ.map f.op = f.c.app (op ⊤) :=
  rfl

end PresheafedSpace

end AlgebraicGeometry

open AlgebraicGeometry AlgebraicGeometry.PresheafedSpace

variable {C}

namespace CategoryTheory

variable {D : Type*} [Category* D]

namespace Functor

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- We can apply a functor `F : C ⥤ D` to the values of the presheaf in any `PresheafedSpace C`,
giving a functor `PresheafedSpace C ⥤ PresheafedSpace D` -/
/-
**CategoryTheory.Functor.mapPresheaf** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.F
unctor`。
形式化陈述：mapPresheaf (F : C ⥤ D) : PresheafedSpace C ⥤ PresheafedSpace D where obj 
X
参数：F : C ⥤ D。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
We can apply a functor `F : C ⥤ D` to the values of the presheaf in any `Preshea
fedSpace C`,
giving a functor `PresheafedSpace C ⥤ PresheafedSpace D`
-/
def mapPresheaf (F : C ⥤ D) : PresheafedSpace C ⥤ PresheafedSpace D where
  obj X :=
    { carrier := X.carrier
      presheaf := X.presheaf ⋙ F }
  map f :=
    { base := f.base
      c := whiskerRight f.c F }
  -- Porting note: these proofs were automatic in mathlib3
  map_id X := by ext <;> cat_disch
  map_comp f g := by ext <;> cat_disch

@[simp]
/-
**CategoryTheory.Functor.mapPresheaf_obj_X** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTh
eory.Functor`。
形式化陈述：mapPresheaf_obj_X (F : C ⥤ D) (X : PresheafedSpace C) : (F.mapPresheaf.obj
 X : TopCat) = (X : TopCat)
参数：F : C ⥤ D；X : PresheafedSpace C。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem mapPresheaf_obj_X (F : C ⥤ D) (X : PresheafedSpace C) :
    (F.mapPresheaf.obj X : TopCat) = (X : TopCat) :=
  rfl

@[simp]
/-
**CategoryTheory.Functor.mapPresheaf_obj_presheaf** 是 Mathlib 中的一个定理，位于命名空间 `Cat
egoryTheory.Functor`。
形式化陈述：mapPresheaf_obj_presheaf (F : C ⥤ D) (X : PresheafedSpace C) : (F.mapPresh
eaf.obj X).presheaf = X.presheaf ⋙ F
参数：F : C ⥤ D；X : PresheafedSpace C。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem mapPresheaf_obj_presheaf (F : C ⥤ D) (X : PresheafedSpace C) :
    (F.mapPresheaf.obj X).presheaf = X.presheaf ⋙ F :=
  rfl

@[simp]
/-
**CategoryTheory.Functor.mapPresheaf_map_f** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTh
eory.Functor`。
形式化陈述：mapPresheaf_map_f (F : C ⥤ D) {X Y : PresheafedSpace C} (f : X ⟶ Y) : (F.m
apPresheaf.map f).base = f.base
参数：F : C ⥤ D；f : X ⟶ Y。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem mapPresheaf_map_f (F : C ⥤ D) {X Y : PresheafedSpace C} (f : X ⟶ Y) :
    (F.mapPresheaf.map f).base = f.base :=
  rfl

@[simp]
/-
**CategoryTheory.Functor.mapPresheaf_map_c** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTh
eory.Functor`。
形式化陈述：mapPresheaf_map_c (F : C ⥤ D) {X Y : PresheafedSpace C} (f : X ⟶ Y) : (F.m
apPresheaf.map f).c = whiskerRight f.c F
参数：F : C ⥤ D；f : X ⟶ Y。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem mapPresheaf_map_c (F : C ⥤ D) {X Y : PresheafedSpace C} (f : X ⟶ Y) :
    (F.mapPresheaf.map f).c = whiskerRight f.c F :=
  rfl

end Functor

namespace NatTrans

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- A natural transformation induces a natural transformation between the `map_presheaf` functors.
-/
/-
**CategoryTheory.NatTrans.onPresheaf** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.N
atTrans`。
形式化陈述：onPresheaf {F G : C ⥤ D} (α : F ⟶ G) : G.mapPresheaf ⟶ F.mapPresheaf where
 app X
参数：α : F ⟶ G。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A natural transformation induces a natural transformation between the `map_presh
eaf` functors.
-/
def onPresheaf {F G : C ⥤ D} (α : F ⟶ G) : G.mapPresheaf ⟶ F.mapPresheaf where
  app X :=
    { base := 𝟙 _
      c := whiskerLeft X.presheaf α ≫ eqToHom (Presheaf.Pushforward.id_eq _).symm }

-- TODO Assemble the last two constructions into a functor
--   `(C ⥤ D) ⥤ (PresheafedSpace C ⥤ PresheafedSpace D)`
end NatTrans

end CategoryTheory

