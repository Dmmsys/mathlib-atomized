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
Definition of `Over` / `Over` 的定义

English:
abbreviation Over
  signature: (X S : Scheme.{u})
  body: OverClass X S

中文:
缩写 Over
  签名: (X S : Scheme.{u})
  定义体: OverClass X S
-/
protected abbrev Over (X S : Scheme.{u}) := OverClass X S

/--
Definition of `CanonicallyOver` / `CanonicallyOver` 的定义

English:
abbreviation CanonicallyOver
  signature: (X S : Scheme.{u})
  body: CanonicallyOverClass X S

中文:
缩写 CanonicallyOver
  签名: (X S : Scheme.{u})
  定义体: CanonicallyOverClass X S

Depends on / 依赖: CanonicallyOverClass
-/
abbrev CanonicallyOver (X S : Scheme.{u}) := CanonicallyOverClass X S

/--
Definition of `Hom.IsOver` / `Hom.IsOver` 的定义

English:
abbreviation Hom.IsOver
  signature: (f : X.Hom Y) (S : Scheme.{u}) [X.Over S] [Y.Over S]
  body: HomIsOver f S

@[simp]

中文:
缩写 Hom.IsOver
  签名: (f : X.Hom Y) (S : Scheme.{u}) [X.Over S] [Y.Over S]
  定义体: HomIsOver f S

@[simp]

Depends on / 依赖: HomIsOver
-/
abbrev Hom.IsOver (f : X.Hom Y) (S : Scheme.{u}) [X.Over S] [Y.Over S] := HomIsOver f S

@[simp]
/--
lemma `Hom.isOver_iff` / 引理 `Hom.isOver_iff`

English:
lemma Hom.isOver_iff
  given: [X.Over S] [Y.Over S] {f : X ⟶ Y}
  statement: f.IsOver S ↔ f ≫ Y ↘ S = X ↘ S
  proof: ⟨fun H => H.1, fun h => ⟨h⟩⟩

中文:
引理 Hom.isOver_iff
  条件: [X.Over S] [Y.Over S] {f : X ⟶ Y}
  结论: f.IsOver S ↔ f ≫ Y ↘ S = X ↘ S
  证明: ⟨fun H => H.1, fun h => ⟨h⟩⟩
-/
lemma Hom.isOver_iff [X.Over S] [Y.Over S] {f : X ⟶ Y} : f.IsOver S ↔ f ≫ Y ↘ S = X ↘ S :=
  ⟨fun H => H.1, fun h => ⟨h⟩⟩

/-! Also note the existence of `CategoryTheory.IsOverTower X Y S`. -/

/--
Definition of `asOver` / `asOver` 的定义

English:
abbreviation asOver
  signature: (X S : Scheme.{u}) [X.Over S]
  body: OverClass.asOver X S

中文:
缩写 asOver
  签名: (X S : Scheme.{u}) [X.Over S]
  定义体: OverClass.asOver X S

Depends on / 依赖: OverClass, OverClass.asOver, asOver
-/
abbrev asOver (X S : Scheme.{u}) [X.Over S] := OverClass.asOver X S

/--
Definition of `Hom.asOver` / `Hom.asOver` 的定义

English:
abbreviation Hom.asOver
  signature: (f : X.Hom Y) (S : Scheme.{u}) [X.Over S] [Y.Over S] [f.IsOver S]
  body: OverClass.asOverHom S f

中文:
缩写 Hom.asOver
  签名: (f : X.Hom Y) (S : Scheme.{u}) [X.Over S] [Y.Over S] [f.IsOver S]
  定义体: OverClass.asOverHom S f

Depends on / 依赖: OverClass, OverClass.asOverHom, asOverHom
-/
abbrev Hom.asOver (f : X.Hom Y) (S : Scheme.{u}) [X.Over S] [Y.Over S] [f.IsOver S] :=
  OverClass.asOverHom S f

end AlgebraicGeometry.Scheme
