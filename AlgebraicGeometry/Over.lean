/-
Copyright (c) 2024 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
module

public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.CategoryTheory.Comma.Over.OverClass

/-!
# Typeclasses for `S`-schemes and `S`-morphisms

We define these as thin wrappers around `CategoryTheory/Comma/OverClass`.

## Main definition
- `AlgebraicGeometry.Scheme.Over`: `X.Over S` equips `X` with an `S`-scheme structure.
  `X ↘ S : X ⟶ S` is the structure morphism.
- `AlgebraicGeometry.Scheme.Hom.IsOver`: `f.IsOver S` asserts that `f` is an `S`-morphism.

-/

public section

namespace AlgebraicGeometry.Scheme

universe u

open CategoryTheory

variable {X Y : Scheme.{u}} (f : X.Hom Y) (S S' : Scheme.{u})

/--
`X.Over S` is the typeclass containing the data of a structure morphism `X ↘ S : X ⟶ S`.
-/
/-
**AlgebraicGeometry.Scheme.Over** 是 Mathlib 中的一个定义，位于命名空间 `AlgebraicGeometry.Sch
eme`。
形式化陈述：AlgebraicGeometry.Scheme → AlgebraicGeometry.Scheme → Type u
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`X.Over S` is the typeclass containing the data of a structure morphism `X ↘ S :
 X ⟶ S`.
-/
protected abbrev Over (X S : Scheme.{u}) := OverClass X S

/--
`X.CanonicallyOver S` is the typeclass containing the data of a structure morphism `X ↘ S : X ⟶ S`,
and that `S` is (uniquely) inferable from the structure of `X`.
-/
/-
**AlgebraicGeometry.Scheme.CanonicallyOver** 是 Mathlib 中的一个缩写定义，位于命名空间 `Algebrai
cGeometry.Scheme`。
形式化陈述：CanonicallyOver (X S : Scheme.{u})
参数：X S : Scheme.{u}。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`X.CanonicallyOver S` is the typeclass containing the data of a structure morphi
sm `X ↘ S : X ⟶ S`,
and that `S` is (uniquely) inferable from the structure of `X`.
-/
abbrev CanonicallyOver (X S : Scheme.{u}) := CanonicallyOverClass X S

/-- Given `X.Over S` and `Y.Over S` and `f : X ⟶ Y`,
`f.IsOver S` is the typeclass asserting `f` commutes with the structure morphisms. -/
/-
**AlgebraicGeometry.Scheme.Hom.IsOver** 是 Mathlib 中的一个定义，位于命名空间 `AlgebraicGeomet
ry.Scheme.Hom`。
形式化陈述：{X Y : AlgebraicGeometry.Scheme} → X.Hom Y → (S : AlgebraicGeometry.Scheme
) → [X.Over S] → [Y.Over S] → Prop
参数：S : AlgebraicGeometry.Scheme。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given `X.Over S` and `Y.Over S` and `f : X ⟶ Y`,
`f.IsOver S` is the typeclass asserting `f` commutes with the structure morphism
s.
-/
abbrev Hom.IsOver (f : X.Hom Y) (S : Scheme.{u}) [X.Over S] [Y.Over S] := HomIsOver f S

@[simp]
/-
**AlgebraicGeometry.Scheme.Hom.isOver_iff** 是 Mathlib 中的一个定理，位于命名空间 `AlgebraicGe
ometry.Scheme.Hom`。
形式化陈述：∀ {X Y : AlgebraicGeometry.Scheme} (S : AlgebraicGeometry.Scheme) [inst : 
X.Over S] [inst_1 : Y.Over S] {f : X ⟶ Y},   AlgebraicGeometry.Scheme.Hom.IsOver
 f S ↔ CategoryTheory.CategoryStruct.comp f (Y ↘ S) = X ↘ S
参数：S : AlgebraicGeometry.Scheme；Y ↘ S。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.HomIsOver.comp_over`：∀ {C : Type u} {inst : CategoryTheor
y.Category.{v, u} C} {X Y : C} {f : X ⟶ Y} {S : C}   {inst_1 : CategoryTheory.Ov
erClass X S} {inst_2 : C…
-/
lemma Hom.isOver_iff [X.Over S] [Y.Over S] {f : X ⟶ Y} : f.IsOver S ↔ f ≫ Y ↘ S = X ↘ S :=
  ⟨fun H ↦ H.1, fun h ↦ ⟨h⟩⟩

/-! Also note the existence of `CategoryTheory.IsOverTower X Y S`. -/

/-- Given `X.Over S`, this is the bundled object of `Over S`. -/
/-
**AlgebraicGeometry.Scheme.asOver** 是 Mathlib 中的一个缩写定义，位于命名空间 `AlgebraicGeometry
.Scheme`。
形式化陈述：asOver (X S : Scheme.{u}) [X.Over S]
参数：X S : Scheme.{u}。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given `X.Over S`, this is the bundled object of `Over S`.
-/
abbrev asOver (X S : Scheme.{u}) [X.Over S] := OverClass.asOver X S

/-- Given a morphism `X ⟶ Y` with `f.IsOver S`, this is the bundled morphism in `Over S`. -/
/-
**AlgebraicGeometry.Scheme.Hom.asOver** 是 Mathlib 中的一个定义，位于命名空间 `AlgebraicGeomet
ry.Scheme.Hom`。
形式化陈述：{X Y : AlgebraicGeometry.Scheme} →   (f : X.Hom Y) →     (S : AlgebraicGeo
metry.Scheme) →       [inst : X.Over S] →         [inst_1 : Y.Over S] → [f.IsOve
r S] → CategoryTheory.OverClass.asOver X S ⟶ CategoryTheory.OverClass.asOver Y S
参数：f : X.Hom Y；S : AlgebraicGeometry.Scheme。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given a morphism `X ⟶ Y` with `f.IsOver S`, this is the bundled morphism in `Ove
r S`.
-/
abbrev Hom.asOver (f : X.Hom Y) (S : Scheme.{u}) [X.Over S] [Y.Over S] [f.IsOver S] :=
  OverClass.asOverHom S f

end AlgebraicGeometry.Scheme

