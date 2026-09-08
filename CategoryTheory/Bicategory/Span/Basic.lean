/-
Copyright (c) 2025 Robin Carlier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robin Carlier
-/
module

public import Mathlib.CategoryTheory.MorphismProperty.Limits
public import Mathlib.CategoryTheory.LocallyCartesianClosed.ChosenPullbacksAlong

/-! # Bicategories of spans in a category

In this file, given a category `C` and two morphism properties
Wₗ and Wᵣ in C that are stable under compositions, contain identities and
such that for any morphism `b : x₃ ⟶ x₄` in Wₗ and any morphism `r : x₂ → x₃` in Wᵣ,
there exists a pullback square
```
     t
  x₁ --> x₂
  |      |
l |      | r
  v      v
  x₃ --> x₄
     b
```
in `C` such that `t` satisfies `Wₗ` and `l` satisfies `Wᵣ`,
we construct the bicategory of spans in C with left morphism in Wₗ and right morphism
in Wᵣ (TODO @robin-carlier).

-/

@[expose] public section

namespace CategoryTheory

variable {C : Type*} [Category* C]
  (Wₗ : MorphismProperty C)
  (Wᵣ : MorphismProperty C)

/-- A (Wₗ, Wᵣ)-span from c to c' is the data of an
object `a : C`, together with a morphism `a ⟶ c` in Wₗ,
and a morphism `a ⟶ c'` in Wᵣ. -/
/-
**CategoryTheory.Span** 是 Mathlib 中的一个归纳类型，位于命名空间 `CategoryTheory`。
形式化陈述：{C : Type u_1} →   [inst : CategoryTheory.Category.{v_1, u_1} C] →     Cat
egoryTheory.MorphismProperty C → CategoryTheory.MorphismProperty C → C → C → Typ
e (max u_1 v_1)
参数：max u_1 v_1。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A (Wₗ, Wᵣ)-span from c to c' is the data of an
object `a : C`, together with a morphism `a ⟶ c` in Wₗ,
and a morphism `a ⟶ c'` in Wᵣ.
-/
structure Span (c c' : C) where
  /-- the apex of the span -/
  apex : C
  /-- the left map -/
  l : apex ⟶ c
  /-- the right map -/
  r : apex ⟶ c'
  wl : Wₗ l
  wr : Wᵣ r

namespace Span

variable {Wₗ Wᵣ} {c c' : C}

/-- A morphism of spans is a morphism between the apices compatible
with the projections. -/
/-
**CategoryTheory.Span.Hom** 是 Mathlib 中的一个结构，位于命名空间 `CategoryTheory.Span`。
形式化陈述：Hom (S₁ S₂ : Span Wₗ Wᵣ c c') : Type _ where /-- the map between the apice
s -/ hom : S₁.apex ⟶ S₂.apex hom_l : hom ≫ S₂.l = S₁.l
参数：S₁ S₂ : Span Wₗ Wᵣ c c'。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A morphism of spans is a morphism between the apices compatible
with the projections.
-/
structure Hom (S₁ S₂ : Span Wₗ Wᵣ c c') : Type _ where
  /-- the map between the apices -/
  hom : S₁.apex ⟶ S₂.apex
  hom_l : hom ≫ S₂.l = S₁.l := by cat_disch
  hom_r : hom ≫ S₂.r = S₁.r := by cat_disch

attribute [reassoc (attr := simp)] Hom.hom_l Hom.hom_r
attribute [grind =] Hom.hom_l Hom.hom_r

@[simps!]
/-
**CategoryTheory.Span.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Span`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Category (Span Wₗ Wᵣ c c') where
  Hom := Hom
  comp φ φ' := { hom := φ.hom ≫ φ'.hom }
  id S := { hom := 𝟙 _ }

attribute [grind =] id_hom comp_hom

@[ext, grind ext]
/-
**CategoryTheory.Span.hom_ext** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.Span`。
形式化陈述：hom_ext {S S' : Span Wₗ Wᵣ c c'} {f g : S ⟶ S'} (h : f.hom = g.hom) : f = 
g
参数：h : f.hom = g.hom。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
lemma hom_ext {S S' : Span Wₗ Wᵣ c c'} {f g : S ⟶ S'} (h : f.hom = g.hom) :
    f = g := by
  cases f
  cases g
  grind

set_option mathlib.tactic.category.grind true in
/-- Construct an isomorphism of spans from an isomorphism between the
apices that is compatible with the projections. -/
@[simps (attr := grind =)]
/-
**CategoryTheory.Span.mkIso** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Span`。
形式化陈述：mkIso {S S' : Span Wₗ Wᵣ c c'} (e : S.apex ≅ S'.apex) (hₗ : e.hom ≫ S'.l =
 S.l
参数：e : S.apex ≅ S'.apex。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Construct an isomorphism of spans from an isomorphism between the
apices that is compatible with the projections.
-/
def mkIso {S S' : Span Wₗ Wᵣ c c'} (e : S.apex ≅ S'.apex)
    (hₗ : e.hom ≫ S'.l = S.l := by cat_disch)
    (hᵣ : e.hom ≫ S'.r = S.r := by cat_disch) :
    S ≅ S' where
  hom.hom := e.hom
  inv.hom := e.inv

variable [Wₗ.ContainsIdentities] [Wᵣ.ContainsIdentities] [Wₗ.HasPullbacksAgainst Wᵣ]
    [Wₗ.IsStableUnderBaseChangeAgainst Wᵣ] [Wᵣ.IsStableUnderBaseChangeAgainst Wₗ]
    [Wₗ.IsStableUnderComposition] [Wᵣ.IsStableUnderComposition]

open Limits in
/-
**CategoryTheory.Span.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Span`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {c c' c'' : C} (S₁ : Span Wₗ Wᵣ c c') (S₂ : Span Wₗ Wᵣ c' c'') : HasPullback S₁.r S₂.l :=
  letI : HasPullback S₂.l S₁.r := hasPullback_ofHasPullbacksAgainst S₂.wl S₁.wr
  hasPullback_symmetry _ _
/-
**CategoryTheory.Span.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Span`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (S₁ : Span Wₗ Wᵣ c c') : Wₗ.IsStableUnderBaseChangeAlong S₁.r :=
  MorphismProperty.IsStableUnderBaseChangeAgainst.isStableUnderBaseChangeAlong _ S₁.wr
/-
**CategoryTheory.Span.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Span`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (S₁ : Span Wₗ Wᵣ c c') : Wᵣ.IsStableUnderBaseChangeAlong S₁.l :=
  MorphismProperty.IsStableUnderBaseChangeAgainst.isStableUnderBaseChangeAlong _ S₁.wl

/-- The identity span, where both legs are identity morphisms. -/
@[simps (attr := grind =)]
/-
**CategoryTheory.Span.id** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Span`。
形式化陈述：id (c : C) : Span Wₗ Wᵣ c c where apex
参数：c : C。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.MorphismProperty.ContainsIdentities.id_mem`：∀ {C : Type u
} {inst : CategoryTheory.Category.{v, u} C} {W : CategoryTheory.MorphismProperty
 C}   [self : W.ContainsIdentities] (X : C), W …

--- 原说明 ---
The identity span, where both legs are identity morphisms.
-/
def id (c : C) :
    Span Wₗ Wᵣ c c where
  apex := c
  l := 𝟙 _
  r := 𝟙 _
  wl := MorphismProperty.ContainsIdentities.id_mem _
  wr := MorphismProperty.ContainsIdentities.id_mem _

open Limits MorphismProperty in
/-- The composition of two spans: if the relevant pullback exists and if the
morphism properties are stable under the relevant base change, it is given by the
total span
```
     P
    /  \
   /    \
  X₁     X₂
 /  \   /  \
c     c'    c''
```
where the top diamond is a pullback square
-/
@[simps (attr := grind =)]
/-
**CategoryTheory.Span.comp** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Span`。
形式化陈述：comp {c c' c'' : C} (S₁ : Span Wₗ Wᵣ c c') (S₂ : Span Wₗ Wᵣ c' c'') : Span
 Wₗ Wᵣ c c'' where apex
参数：S₁ : Span Wₗ Wᵣ c c'；S₂ : Span Wₗ Wᵣ c' c''。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Span.instHasPullbackRL`：∀ {C : Type u_1} [inst : Category
Theory.Category.{v_1, u_1} C] {Wₗ Wᵣ : CategoryTheory.MorphismProperty C}   [Wₗ.
HasPullbacksAgainst Wᵣ] {c …

--- 原说明 ---
The composition of two spans: if the relevant pullback exists and if the
morphism properties are stable under the relevant base change, it is given by th
e
total span
```
     P
    /  \
   /    \
  X₁     X₂
 /  \   /  \
c     c'    c''
```
where the top diamond is a pullback square
-/
noncomputable def comp {c c' c'' : C}
    (S₁ : Span Wₗ Wᵣ c c') (S₂ : Span Wₗ Wᵣ c' c'') :
    Span Wₗ Wᵣ c c'' where
  apex := pullback S₁.r S₂.l
  l := pullback.fst S₁.r S₂.l ≫ S₁.l
  r := pullback.snd S₁.r S₂.l ≫ S₂.r
  wl :=
    IsStableUnderComposition.comp_mem
      _ _ (IsStableUnderBaseChangeAlong.of_isPullback
      (.flip <| .of_hasPullback S₁.r S₂.l) S₂.wl) S₁.wl
  wr :=
    IsStableUnderComposition.comp_mem
    _ _ (IsStableUnderBaseChangeAlong.of_isPullback
      (.of_hasPullback S₁.r S₂.l) S₁.wr) S₂.wr

end Span

end CategoryTheory

