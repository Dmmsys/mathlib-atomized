/-
Copyright (c) 2019 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import Mathlib.CategoryTheory.Functor.Basic

/-!
# Unbundled functors, as a typeclass decorating the object-level function.
-/

@[expose] public section


namespace CategoryTheory

-- declare the `v`'s first; see `CategoryTheory.Category` for an explanation
universe v v₁ v₂ v₃ u u₁ u₂ u₃

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]

-- Perhaps in the future we could redefine `Functor` in terms of this, but that isn't the
-- immediate plan.
/-- An unbundled functor. -/
/-
**CategoryTheory.Functorial** 是 Mathlib 中的一个类，位于命名空间 `CategoryTheory`。
形式化陈述：Functorial (F : C -> D) : Type max v₁ v₂ u₁ u₂ where /-- If `F : C → D` (j
ust a function) has `[Functorial F]`, we can write `map F f : F X ⟶ F Y` for the
 action of `F` on a morphism `f : X ⟶ Y`. -/ map (F) : forall {X Y : C}, (X ⟶ Y)
 -> (F X ⟶ F Y) /-- A functorial map preserves identities. -/ map_id : forall {X
 : C}, map (𝟙 X) = 𝟙 (F X)
参数：F : C -> D。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An unbundled functor.
-/
class Functorial (F : C → D) : Type max v₁ v₂ u₁ u₂ where
  /-- If `F : C → D` (just a function) has `[Functorial F]`,
  we can write `map F f : F X ⟶ F Y` for the action of `F` on a morphism `f : X ⟶ Y`. -/
  map (F) : ∀ {X Y : C}, (X ⟶ Y) → (F X ⟶ F Y)
  /-- A functorial map preserves identities. -/
  map_id : ∀ {X : C}, map (𝟙 X) = 𝟙 (F X) := by cat_disch
  /-- A functorial map preserves composition of morphisms. -/
  map_comp : ∀ {X Y Z : C} {f : X ⟶ Y} {g : Y ⟶ Z}, map (f ≫ g) = map f ≫ map g := by
    cat_disch

attribute [simp, grind =] Functorial.map_id Functorial.map_comp
export Functorial (map)

namespace Functor

/-- Bundle a functorial function as a functor.
-/
/-
**CategoryTheory.Functor.of** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Functor`。
形式化陈述：of (F : C -> D) [I : Functorial.{v₁, v₂} F] : C ⥤ D
参数：F : C -> D。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Functorial.map_id`：∀ {C : Type u₁} {inst : CategoryTheory
.Category.{v₁, u₁} C} {D : Type u₂} {inst_1 : CategoryTheory.Category.{v₂, u₂} D
}   {F : C → D} [self …
· 使用定理 `CategoryTheory.Functorial.map_comp`：∀ {C : Type u₁} {inst : CategoryTheo
ry.Category.{v₁, u₁} C} {D : Type u₂} {inst_1 : CategoryTheory.Category.{v₂, u₂}
 D}   {F : C → D} [self …

--- 原说明 ---
Bundle a functorial function as a functor.
-/
def of (F : C → D) [I : Functorial.{v₁, v₂} F] : C ⥤ D :=
  { I with obj := F
           map := Functorial.map F }

end Functor

/-
**CategoryTheory.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (F : C ⥤ D) : Functorial.{v₁, v₂} F.obj :=
  { F with map := F.map }

@[simp, grind =]
/-
**CategoryTheory.map_functorial_obj** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory`。
形式化陈述：map_functorial_obj (F : C ⥤ D) {X Y : C} (f : X ⟶ Y) : map F.obj f = F.map
 f
参数：F : C ⥤ D；f : X ⟶ Y。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem map_functorial_obj (F : C ⥤ D) {X Y : C} (f : X ⟶ Y) : map F.obj f = F.map f :=
  rfl
/-
**CategoryTheory.functorial_id** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory`。
形式化陈述：functorial_id : Functorial.{v₁, v₁} (id : C -> C) where map f
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance functorial_id : Functorial.{v₁, v₁} (id : C → C) where map f := f

section

variable {E : Type u₃} [Category.{v₃} E]

-- This is no longer viable as an instance in Lean 3.7,
-- #lint reports an instance loop
-- Will this be a problem?
/-- `G ∘ F` is a functorial if both `F` and `G` are.
-/
@[instance_reducible]
/-
**CategoryTheory.functorial_comp** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory`。
形式化陈述：functorial_comp (F : C -> D) [Functorial.{v₁, v₂} F] (G : D -> E) [Functor
ial.{v₂, v₃} G] : Functorial.{v₁, v₃} (G ∘ F)
参数：F : C -> D；G : D -> E。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Functor.map_id`：∀ {C : Type u₁} [inst : CategoryTheory.Ca
tegory.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]  
 (self : CategoryTh…
· 使用定理 `CategoryTheory.Functor.map_comp`：∀ {C : Type u₁} [inst : CategoryTheory.
Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]
   (self : CategoryTh…

--- 原说明 ---
`G ∘ F` is a functorial if both `F` and `G` are.
-/
def functorial_comp (F : C → D) [Functorial.{v₁, v₂} F] (G : D → E) [Functorial.{v₂, v₃} G] :
    Functorial.{v₁, v₃} (G ∘ F) :=
  { Functor.of F ⋙ Functor.of G with map := fun f => map G (map F f) }

end

end CategoryTheory

