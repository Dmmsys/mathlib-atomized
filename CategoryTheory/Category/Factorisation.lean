/-
Copyright (c) 2023 Jakob von Raumer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jakob von Raumer
-/
module

public import Mathlib.CategoryTheory.Comma.Arrow
public import Mathlib.CategoryTheory.Limits.Shapes.Terminal

/-!
# The Factorisation Category of a Category

`Factorisation f` is the category containing as objects all factorisations of a morphism `f`.

We show that `Factorisation f` always has an initial and a terminal object.

TODO: Show that `Factorisation f` is isomorphic to a comma category in two ways.

TODO: Make `MonoFactorisation f` a special case of a `Factorisation f`.
-/

@[expose] public section

namespace CategoryTheory

universe v u

variable {C : Type u} [Category.{v} C]

set_option linter.style.whitespace false in -- manual alignment is not recognised
/-- Factorisations of a morphism `f` as a structure, containing, one object, two morphisms,
and the condition that their composition equals `f`. -/
/-
**CategoryTheory.Factorisation** 是 Mathlib 中的一个结构，位于命名空间 `CategoryTheory`。
形式化陈述：Factorisation {X Y : C} (f : X ⟶ Y) where /-- The midpoint of the factoris
ation. -/ mid : C /-- The morphism into the factorisation midpoint. -/ ι : X ⟶ m
id /-- The morphism out of the factorisation midpoint. -/ π : mid ⟶ Y /-- The fa
ctorisation condition. -/ ι_π : ι ≫ π = f
参数：f : X ⟶ Y。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Factorisations of a morphism `f` as a structure, containing, one object, two mor
phisms,
and the condition that their composition equals `f`.
-/
structure Factorisation {X Y : C} (f : X ⟶ Y) where
  /-- The midpoint of the factorisation. -/
  mid : C
  /-- The morphism into the factorisation midpoint. -/
  ι   : X ⟶ mid
  /-- The morphism out of the factorisation midpoint. -/
  π   : mid ⟶ Y
  /-- The factorisation condition. -/
  ι_π : ι ≫ π = f := by cat_disch

attribute [reassoc (attr := simp)] Factorisation.ι_π

namespace Factorisation

variable {X Y : C} {f : X ⟶ Y}

/-- Morphisms of `Factorisation f` consist of morphism between their midpoints and the obvious
commutativity conditions. -/
@[ext]
/-
**CategoryTheory.Factorisation.Hom** 是 Mathlib 中的一个归纳类型，位于命名空间 `CategoryTheory.F
actorisation`。
形式化陈述：{C : Type u} →   [inst : CategoryTheory.Category.{v, u} C] →     {X Y : C}
 → {f : X ⟶ Y} → CategoryTheory.Factorisation f → CategoryTheory.Factorisation f
 → Type (max u v)
参数：max u v。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Morphisms of `Factorisation f` consist of morphism between their midpoints and t
he obvious
commutativity conditions.
-/
protected structure Hom (d e : Factorisation f) : Type (max u v) where
  /-- The morphism between the midpoints of the factorizations. -/
  h : d.mid ⟶ e.mid
  /-- The left commuting triangle of the factorization morphism. -/
  ι_h : d.ι ≫ h = e.ι := by cat_disch
  /-- The right commuting triangle of the factorization morphism. -/
  h_π : h ≫ e.π = d.π := by cat_disch

attribute [reassoc (attr := simp)] Factorisation.Hom.ι_h Factorisation.Hom.h_π
/-
**CategoryTheory.Factorisation.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Factor
isation`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Quiver (Factorisation f) where
  Hom d e := Factorisation.Hom d e

@[simps]
/-
**CategoryTheory.Factorisation.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Factor
isation`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Category.{max u v} (Factorisation f) where
  id d := { h := 𝟙 _ }
  comp f g := { h := f.h ≫ g.h }

attribute [reassoc] comp_h

variable (d : Factorisation f)

/-- The initial object in `Factorisation f`, with the domain of `f` as its midpoint. -/
@[simps]
/-
**CategoryTheory.Factorisation.initial** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory
.Factorisation`。
形式化陈述：{C : Type u} → [inst : CategoryTheory.Category.{v, u} C] → {X Y : C} → {f 
: X ⟶ Y} → CategoryTheory.Factorisation f
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The initial object in `Factorisation f`, with the domain of `f` as its midpoint.
-/
protected def initial : Factorisation f where
  mid := X
  ι := 𝟙 _
  π := f

set_option backward.defeqAttrib.useBackward true in
/-- The unique morphism out of `Factorisation.initial f`. -/
@[simps]
/-
**CategoryTheory.Factorisation.initialHom** 是 Mathlib 中的一个定义，位于命名空间 `CategoryThe
ory.Factorisation`。
形式化陈述：{C : Type u} →   [inst : CategoryTheory.Category.{v, u} C] →     {X Y : C}
 → {f : X ⟶ Y} → (d : CategoryTheory.Factorisation f) → CategoryTheory.Factorisa
tion.initial.Hom d
参数：d : CategoryTheory.Factorisation f。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The unique morphism out of `Factorisation.initial f`.
-/
protected def initialHom (d : Factorisation f) :
    Factorisation.Hom (Factorisation.initial : Factorisation f) d where
  h := d.ι

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-
**CategoryTheory.Factorisation.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Factor
isation`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Unique ((Factorisation.initial : Factorisation f) ⟶ d) where
  default := Factorisation.initialHom d
  uniq f := by apply Factorisation.Hom.ext; simp [← f.ι_h]

/-- The terminal object in `Factorisation f`, with the codomain of `f` as its midpoint. -/
@[simps]
/-
**CategoryTheory.Factorisation.terminal** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheor
y.Factorisation`。
形式化陈述：{C : Type u} → [inst : CategoryTheory.Category.{v, u} C] → {X Y : C} → {f 
: X ⟶ Y} → CategoryTheory.Factorisation f
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The terminal object in `Factorisation f`, with the codomain of `f` as its midpoi
nt.
-/
protected def terminal : Factorisation f where
  mid := Y
  ι := f
  π := 𝟙 _

set_option backward.defeqAttrib.useBackward true in
/-- The unique morphism into `Factorisation.terminal f`. -/
@[simps]
/-
**CategoryTheory.Factorisation.terminalHom** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTh
eory.Factorisation`。
形式化陈述：{C : Type u} →   [inst : CategoryTheory.Category.{v, u} C] →     {X Y : C}
 → {f : X ⟶ Y} → (d : CategoryTheory.Factorisation f) → d.Hom CategoryTheory.Fac
torisation.terminal
参数：d : CategoryTheory.Factorisation f。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The unique morphism into `Factorisation.terminal f`.
-/
protected def terminalHom (d : Factorisation f) :
    Factorisation.Hom d (Factorisation.terminal : Factorisation f) where
  h := d.π

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-
**CategoryTheory.Factorisation.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Factor
isation`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Unique (d ⟶ (Factorisation.terminal : Factorisation f)) where
  default := Factorisation.terminalHom d
  uniq f := by apply Factorisation.Hom.ext; simp [← f.h_π]

open Limits

/-- The initial factorisation is an initial object -/
/-
**CategoryTheory.Factorisation.IsInitial_initial** 是 Mathlib 中的一个定义，位于命名空间 `Cate
goryTheory.Factorisation`。
形式化陈述：IsInitial_initial : IsInitial (Factorisation.initial : Factorisation f)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The initial factorisation is an initial object
-/
def IsInitial_initial : IsInitial (Factorisation.initial : Factorisation f) := IsInitial.ofUnique _
/-
**CategoryTheory.Factorisation.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Factor
isation`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : HasInitial (Factorisation f) := Limits.hasInitial_of_unique Factorisation.initial

/-- The terminal factorisation is a terminal object -/
/-
**CategoryTheory.Factorisation.IsTerminal_terminal** 是 Mathlib 中的一个定义，位于命名空间 `Ca
tegoryTheory.Factorisation`。
形式化陈述：IsTerminal_terminal : IsTerminal (Factorisation.terminal : Factorisation f
)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The terminal factorisation is a terminal object
-/
def IsTerminal_terminal : IsTerminal (Factorisation.terminal : Factorisation f) :=
IsTerminal.ofUnique _
/-
**CategoryTheory.Factorisation.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Factor
isation`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : HasTerminal (Factorisation f) := Limits.hasTerminal_of_unique Factorisation.terminal

/-- The forgetful functor from `Factorisation f` to the underlying category `C`. -/
@[simps]
/-
**CategoryTheory.Factorisation.forget** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.
Factorisation`。
形式化陈述：forget : Factorisation f ⥤ C where obj
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The forgetful functor from `Factorisation f` to the underlying category `C`.
-/
def forget : Factorisation f ⥤ C where
  obj := Factorisation.mid
  map f := f.h

end Factorisation

end CategoryTheory

