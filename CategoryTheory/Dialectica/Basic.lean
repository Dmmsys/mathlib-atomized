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
/-- The Dialectica category. An object of the category is a triple `⟨U, X, α ⊆ U × X⟩`,
and a morphism from `⟨U, X, α⟩` to `⟨V, Y, β⟩` is a pair `(f : U ⟶ V, F : U ⨯ Y ⟶ X)` such that
`{(u,y) | α(u, F(u, y))} ⊆ {(u,y) | β(f(u), y)}`. The subset `α` is actually encoded as an element
of `Subobject (U × X)`, and the above inequality is expressed using pullbacks. -/
/-
**CategoryTheory.Dial** 是 Mathlib 中的一个归纳类型，位于命名空间 `CategoryTheory`。
形式化陈述：(C : Type u) → [inst : CategoryTheory.Category.{v, u} C] → [CategoryTheory
.Limits.HasFiniteProducts C] → Type (max u v)
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The Dialectica category. An object of the category is a triple `⟨U, X, α ⊆ U × X
⟩`,
and a morphism from `⟨U, X, α⟩` to `⟨V, Y, β⟩` is a pair `(f : U ⟶ V, F : U ⨯ Y 
⟶ X)` such that
`{(u,y) | α(u, F(u, y))} ⊆ {(u,y) | β(f(u), y)}`. The subset `α` is actually enc
oded as an element
of `Subobject (U × X)`, and the above inequality is expressed using pullbacks.
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

/-- A morphism in the `Dial C` category from `⟨U, X, α⟩` to `⟨V, Y, β⟩` is a pair
`(f : U ⟶ V, F : U ⨯ Y ⟶ X)` such that `{(u,y) | α(u, F(u, y))} ≤ {(u,y) | β(f(u), y)}`. -/
/-
**CategoryTheory.Dial.Hom** 是 Mathlib 中的一个归纳类型，位于命名空间 `CategoryTheory.Dial`。
形式化陈述：{C : Type u} →   [inst : CategoryTheory.Category.{v, u} C] →     [inst_1 :
 CategoryTheory.Limits.HasFiniteProducts C] →       [CategoryTheory.Limits.HasPu
llbacks C] → CategoryTheory.Dial C → CategoryTheory.Dial C → Type v
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A morphism in the `Dial C` category from `⟨U, X, α⟩` to `⟨V, Y, β⟩` is a pair
`(f : U ⟶ V, F : U ⨯ Y ⟶ X)` such that `{(u,y) | α(u, F(u, y))} ≤ {(u,y) | β(f(u
), y)}`.
-/
@[ext] structure Hom (X Y : Dial C) where
  /-- Maps the sources -/
  f : X.src ⟶ Y.src
  /-- Maps the targets (contravariantly) -/
  F : X.src ⨯ Y.tgt ⟶ X.tgt
  /-- This says `{(u, y) | α(u, F(u, y))} ⊆ {(u, y) | β(f(u), y)}` using subobject pullbacks -/
  le :
    (Subobject.pullback π(π₁, F)).obj X.rel ≤
    (Subobject.pullback (prod.map f (𝟙 _))).obj Y.rel

set_option backward.isDefEq.respectTransparency false in
/-
**CategoryTheory.Dial.comp_le_lemma** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.Di
al`。
形式化陈述：comp_le_lemma {X Y Z : Dial C} (F : Dial.Hom X Y) (G : Dial.Hom Y Z) : (Su
bobject.pullback π(π₁, π(π₁, prod.map F.f (𝟙 _) ≫ G.F) ≫ F.F)).obj X.rel <= (Sub
object.pullback (prod.map (F.f ≫ G.f) (𝟙 Z.tgt))).obj Z.rel
参数：F : Dial.Hom X Y；G : Dial.Hom Y Z。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_trans`：le_trans : a <= b -> b <= c -> a <= c
· 使用定理 `CategoryTheory.Limits.instHasLimitOfHasLimitsOfShape`：∀ {C : Type u} [in
st : CategoryTheory.Category.{v, u} C] {J : Type u₁} [inst_1 : CategoryTheory.Ca
tegory.{v₁, u₁} J]   [CategoryTheory.Limit…
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CategoryTheory.Subobject.pullback.congr_simp`：∀ {C : Type u₁} [inst : Ca
tegoryTheory.Category.{v₁, u₁} C] {X Y : C} [inst_1 : CategoryTheory.Limits.HasP
ullbacks C]   (f f_1 : X ⟶ Y), f =…
· 使用定理 `CategoryTheory.Limits.prod.comp_lift`：∀ {C : Type u} [inst : CategoryThe
ory.Category.{v, u} C] {V W X Y : C}   [inst_1 : CategoryTheory.Limits.HasBinary
Product X Y] (f : V ⟶ W) (…
· 使用定理 `CategoryTheory.Limits.limit.lift_π`：∀ {J : Type u₁} [inst : CategoryTheo
ry.Category.{v₁, u₁} J] {C : Type u} [inst_1 : CategoryTheory.Category.{v, u} C]
   {F : CategoryTheory.F…
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `CategoryTheory.Functor.monotone`：monotone (f : X ⥤ Y) : Monotone f.obj
· 使用定理 `CategoryTheory.Dial.Hom.le`：∀ {C : Type u} [inst : CategoryTheory.Catego
ry.{v, u} C] [inst_1 : CategoryTheory.Limits.HasFiniteProducts C]   [inst_2 : Ca
tegoryTheory.Lim…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `CategoryTheory.Limits.prod.lift_map`：∀ {C : Type u} [inst : CategoryTheo
ry.Category.{v, u} C] {V W X Y Z : C}   [inst_1 : CategoryTheory.Limits.HasBinar
yProduct W X] [inst_2 : C…
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `CategoryTheory.Limits.prod.map_fst`：∀ {C : Type u} [inst : CategoryTheor
y.Category.{v, u} C] {W X Y Z : C}   [inst_1 : CategoryTheory.Limits.HasBinaryPr
oduct W X] [inst_2 : Cat…
· 使用定理 `CategoryTheory.Limits.prod.map_map`：∀ {C : Type u} [inst : CategoryTheor
y.Category.{v, u} C] {A₁ A₂ A₃ B₁ B₂ B₃ : C}   [inst_1 : CategoryTheory.Limits.H
asBinaryProduct A₁ B₁] […
-/
theorem comp_le_lemma {X Y Z : Dial C} (F : Dial.Hom X Y) (G : Dial.Hom Y Z) :
    (Subobject.pullback π(π₁, π(π₁, prod.map F.f (𝟙 _) ≫ G.F) ≫ F.F)).obj X.rel ≤
    (Subobject.pullback (prod.map (F.f ≫ G.f) (𝟙 Z.tgt))).obj Z.rel := by
  refine
    le_trans ?_ <| ((Subobject.pullback (π(π₁, prod.map F.f (𝟙 _) ≫ G.F))).monotone F.le).trans <|
    le_trans ?_ <| ((Subobject.pullback (prod.map F.f (𝟙 Z.tgt))).monotone G.le).trans ?_
    <;> simp [← Subobject.pullback_comp]

set_option backward.isDefEq.respectTransparency false in
@[simps]
/-
**CategoryTheory.Dial.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Dial`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
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
    rw [← Category.assoc, ← Category.assoc]; congr 1
    ext <;> simp
/-
**CategoryTheory.Dial.hom_ext** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.Dial`。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] [inst_1 : Categor
yTheory.Limits.HasFiniteProducts C]   [inst_2 : CategoryTheory.Limits.HasPullbac
ks C] {X Y : CategoryTheory.Dial C} {x y : X ⟶ Y},   x.f = y.f → x.F = y.F → x =
 y
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.instHasLimitOfHasLimitsOfShape`：∀ {C : Type u} [in
st : CategoryTheory.Category.{v, u} C] {J : Type u₁} [inst_1 : CategoryTheory.Ca
tegory.{v₁, u₁} J]   [CategoryTheory.Limit…
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `CategoryTheory.Dial.Hom.ext`：∀ {C : Type u} {inst : CategoryTheory.Categ
ory.{v, u} C} {inst_1 : CategoryTheory.Limits.HasFiniteProducts C}   {inst_2 : C
ategoryTheory.Lim…
-/
@[ext] theorem hom_ext {X Y : Dial C} {x y : X ⟶ Y} (hf : x.f = y.f) (hF : x.F = y.F) : x = y :=
  Hom.ext hf hF

set_option backward.isDefEq.respectTransparency false in
/--
An isomorphism in `Dial C` can be induced by isomorphisms on the source and target,
which respect the respective relations on `X` and `Y`.
-/
/-
**CategoryTheory.Dial.isoMk** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Dial`。
形式化陈述：{C : Type u} →   [inst : CategoryTheory.Category.{v, u} C] →     [inst_1 :
 CategoryTheory.Limits.HasFiniteProducts C] →       [inst_2 : CategoryTheory.Lim
its.HasPullbacks C] →         {X Y : CategoryTheory.Dial C} →           (e₁ : X.
src ≅ Y.src) →             (e₂ : X.tgt ≅ Y.tgt) →               X.rel = (Categor
yTheory.Subobject.pullback (CategoryTheory.Limits.prod.map e₁.hom e₂.hom)).obj Y
.rel →                 (X ≅ Y)
参数：e₁ : X.src ≅ Y.src；e₂ : X.tgt ≅ Y.tgt；CategoryTheory.Subobject.pullback (Cate
goryTheory.Limits.prod.map e₁.hom e₂.hom)；X ≅ Y。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An isomorphism in `Dial C` can be induced by isomorphisms on the source and targ
et,
which respect the respective relations on `X` and `Y`.
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

