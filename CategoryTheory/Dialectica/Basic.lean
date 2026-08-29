/-
Copyright (c) 2024 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
module

public import Mathlib.CategoryTheory.Subobject.Basic

/-!
# Dialectica category

We define the category `Dial` of the Dialectica interpretation, after [dialectica1989].

## Background

Dialectica categories are important models of linear type theory. They satisfy most of the
distinctions that linear logic was meant to introduce and many models do not satisfy, like the
independence of constants. Many linear type theories are being used at the
moment--[nLab] describes some of them: for quantum systems, for effects in programming, for linear
dependent types. In particular, dialectica categories are connected to polynomial functors, being a
slightly more sophisticated version of polynomial types, as discussed, for instance, in Moss and
von Glehn's [*Dialectica models of type theory*]. As such they are related to the polynomial
constructions being [developed][Poly] by Awodey, Riehl, and Hazratpour. For the non-dependent
version developed here several applications are known to Petri Nets, small cardinals
in Set Theory, state in imperative programming, and others, see [Dialectica Categories].

## References

* [Valeria de Paiva, The Dialectica Categories.][dialectica1989]
  ([pdf](https://www.cl.cam.ac.uk/techreports/UCAM-CL-TR-213.pdf))

[nLab]: https://ncatlab.org/nlab/show/linear+type+theory
[*Dialectica models of type theory*]: https://arxiv.org/abs/2105.00283
[Poly]: https://github.com/sinhp/Poly
[Dialectica Categories]: https://github.com/vcvpaiva/DialecticaCategories

-/

@[expose] public section

noncomputable section

namespace CategoryTheory

open Limits

universe v u
variable {C : Type u} [Category.{v} C] [HasFiniteProducts C] [HasPullbacks C]

variable (C) in
/--
Definition of `Dial` / `Dial` 的定义

English:
structure Dial
  parameters: where
  axioms and operations (3):
    - src : C
    - tgt : C
    - rel : Subobject (src ⨯ tgt)

中文:
结构 Dial
  参数: where
  公理与运算 (3 个):
    - src : C
    - tgt : C
    - rel : Subobject (src ⨯ tgt)
-/
structure Dial where
  /-- The source object -/
  src : C
  /-- The target object -/
  tgt : C
  /-- A subobject of `src ⨯ tgt`, interpreted as a relation -/
  rel : Subobject (src ⨯ tgt)

namespace Dial

local notation "π₁" => prod.fst
local notation "π₂" => prod.snd
local notation "π(" a ", " b ")" => prod.lift a b

/--
Definition of `Hom` / `Hom` 的定义

English:
structure Hom
  parameters: (X Y : Dial C)
  axioms and operations (3):
    - f : X.src ⟶ Y.src
    - F : X.src ⨯ Y.tgt ⟶ X.tgt
    - le : (Subobject.pullback π(π₁, F)).obj X.rel <= (Subobject.pullback (prod.map f (𝟙 _))).obj Y.rel

中文:
结构 态射
  参数: (X Y : Dial C)
  公理与运算 (3 个):
    - f : X.src ⟶ Y.src
    - F : X.src ⨯ Y.tgt ⟶ X.tgt
    - le : (Subobject.pullback π(π₁, F)).obj X.rel <= (Subobject.pullback (乘积.map f (𝟙 _))).obj Y.rel
-/
@[ext] structure Hom (X Y : Dial C) where
  /-- Maps the sources -/
  f : X.src ⟶ Y.src
  /-- Maps the targets (contravariantly) -/
  F : X.src ⨯ Y.tgt ⟶ X.tgt
  /-- This says `{(u, y) | α(u, F(u, y))} ⊆ {(u, y) | β(f(u), y)}` using subobject pullbacks -/
  le :
    (Subobject.pullback π(π₁, F)).obj X.rel <=
    (Subobject.pullback (prod.map f (𝟙 _))).obj Y.rel

set_option backward.isDefEq.respectTransparency false in
/--
theorem `comp_le_lemma` / 定理 `comp_le_lemma`

English:
theorem comp_le_lemma
  given: {X Y Z : Dial C} (F : Dial.Hom X Y) (G : Dial.Hom Y Z)
  proof: by
  refine
le_trans ?_ ((Subobject.pullback (π(π₁, prod.map F.f (𝟙 _) ≫ G.F))).monotone F.le).trans
le_trans ?_ ((Subobject.pullback (prod.map F.f (𝟙 Z.tgt))).monotone G.le).trans ?_
    <;> simp [← Subobject.pullback_comp]

中文:
定理 comp_le_lemma
  条件: {X Y Z : Dial C} (F : Dial.态射 X Y) (G : Dial.态射 Y Z)
  证明: by
  refine
le_trans ?_ ((Subobject.pullback (π(π₁, prod.map F.f (𝟙 _) ≫ G.F))).monotone F.le).trans
le_trans ?_ ((Subobject.pullback (prod.map F.f (𝟙 Z.tgt))).monotone G.le).trans ?_
    <;> simp [← Subobject.pullback_comp]

Depends on / 依赖: F.le, G.le, Subobject, Subobject.pullback, Subobject.pullback_comp, Z.tgt, le_trans, monotone, prod.map, pullback, pullback_comp
-/
theorem comp_le_lemma {X Y Z : Dial C} (F : Dial.Hom X Y) (G : Dial.Hom Y Z) :
    (Subobject.pullback π(π₁, π(π₁, prod.map F.f (𝟙 _) ≫ G.F) ≫ F.F)).obj X.rel <=
    (Subobject.pullback (prod.map (F.f ≫ G.f) (𝟙 Z.tgt))).obj Z.rel := by
  refine
le_trans ?_ ((Subobject.pullback (π(π₁, prod.map F.f (𝟙 _) ≫ G.F))).monotone F.le).trans
le_trans ?_ ((Subobject.pullback (prod.map F.f (𝟙 Z.tgt))).monotone G.le).trans ?_
    <;> simp [← Subobject.pullback_comp]

set_option backward.isDefEq.respectTransparency false in
@[simps]
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Category (Dial C)
  body: Dial.Hom
  id X := {
    f := 𝟙 _
    F := π₂
    le := by simp
  }
  comp {_ _ _} (F G : Dial.Hom ..) := {
    f := F.f ≫ G.f
    F := π(π₁, prod.map F.f (𝟙 _) ≫ G.F) ≫ F.F
    le := comp_le_lemma F G
  }
  assoc f g h := by
    simp only [Category.assoc, Hom.mk.injEq, true_and]
    rw [← Category.assoc]; rw [← Category.assoc]; congr 1
    ext <;> simp

中文:
实例 :
  签名: 范畴 (Dial C)
  定义体: Dial.Hom
  id X := {
    f := 𝟙 _
    F := π₂
    le := by simp
  }
  comp {_ _ _} (F G : Dial.Hom ..) := {
    f := F.f ≫ G.f
    F := π(π₁, prod.map F.f (𝟙 _) ≫ G.F) ≫ F.F
    le := comp_le_lemma F G
  }
  assoc f g h := by
    simp only [Category.assoc, Hom.mk.injEq, true_and]
    rw [← Category.assoc]; rw [← Category.assoc]; congr 1
    ext <;> simp

Depends on / 依赖: Dial.Hom
-/
instance : Category (Dial C) where
  Hom := Dial.Hom
  id X := {
    f := 𝟙 _
    F := π₂
    le := by simp
  }
  comp {_ _ _} (F G : Dial.Hom ..) := {
    f := F.f ≫ G.f
    F := π(π₁, prod.map F.f (𝟙 _) ≫ G.F) ≫ F.F
    le := comp_le_lemma F G
  }
  assoc f g h := by
    simp only [Category.assoc, Hom.mk.injEq, true_and]
    rw [← Category.assoc]; rw [← Category.assoc]; congr 1
    ext <;> simp

/--
theorem `hom_ext` / 定理 `hom_ext`

English:
theorem hom_ext
  given: {X Y : Dial C} {x y : X ⟶ Y} (hf : x.f = y.f) (hF : x.F = y.F)
  statement: x = y
  proof: Hom.ext hf hF

中文:
定理 hom_ext
  条件: {X Y : Dial C} {x y : X ⟶ Y} (hf : x.f = y.f) (hF : x.F = y.F)
  结论: x = y
  证明: Hom.ext hf hF
-/
@[ext] theorem hom_ext {X Y : Dial C} {x y : X ⟶ Y} (hf : x.f = y.f) (hF : x.F = y.F) : x = y :=
  Hom.ext hf hF

set_option backward.isDefEq.respectTransparency false in
/--
Definition of `isoMk` / `isoMk` 的定义

English:
definition isoMk
  signature: {X Y : Dial C} (e₁ : X.src ≅ Y.src) (e₂ : X.tgt ≅ Y.tgt)
  body: {
    f := e₁.hom
    F := π₂ ≫ e₂.inv
    le := by rw [eq, ← Subobject.pullback_comp]; apply le_of_eq; congr; ext <;> simp
  }
  inv := {
    f := e₁.inv
    F := π₂ ≫ e₂.hom
    le := by rw [eq, ← Subobject.pullback_comp]; apply le_of_eq; congr; ext <;> simp
  }

中文:
定义 isoMk
  签名: {X Y : Dial C} (e₁ : X.src ≅ Y.src) (e₂ : X.tgt ≅ Y.tgt)
  定义体: {
    f := e₁.hom
    F := π₂ ≫ e₂.inv
    le := by rw [eq, ← Subobject.pullback_comp]; apply le_of_eq; congr; ext <;> simp
  }
  inv := {
    f := e₁.inv
    F := π₂ ≫ e₂.hom
    le := by rw [eq, ← Subobject.pullback_comp]; apply le_of_eq; congr; ext <;> simp
  }
-/
@[simps] def isoMk {X Y : Dial C} (e₁ : X.src ≅ Y.src) (e₂ : X.tgt ≅ Y.tgt)
    (eq : X.rel = (Subobject.pullback (prod.map e₁.hom e₂.hom)).obj Y.rel) : X ≅ Y where
  hom := {
    f := e₁.hom
    F := π₂ ≫ e₂.inv
    le := by rw [eq, ← Subobject.pullback_comp]; apply le_of_eq; congr; ext <;> simp
  }
  inv := {
    f := e₁.inv
    F := π₂ ≫ e₂.hom
    le := by rw [eq, ← Subobject.pullback_comp]; apply le_of_eq; congr; ext <;> simp
  }

end Dial

end CategoryTheory
