/-
Copyright (c) 2022 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.CategoryTheory.Triangulated.Pretriangulated

/-!
# Triangulated Categories

This file contains the definition of triangulated categories, which are
pretriangulated categories which satisfy the octahedron axiom.

-/

@[expose] public section

assert_not_exists TwoSidedIdeal

noncomputable section

namespace CategoryTheory

open Limits Category Preadditive Pretriangulated

open ZeroObject

variable (C : Type*) [Category* C] [Preadditive C] [HasZeroObject C] [HasShift C ℤ]
  [∀ n : ℤ, Functor.Additive (shiftFunctor C n)] [Pretriangulated C]

namespace Triangulated

variable {C}

/-- An octahedron is a type of datum whose existence is asserted by the
octahedron axiom (TR 4). The input is given by the following diagram:
```
     u₁₃      v₂₃
  X₁ ────> X₃ ────> Z₂₃       Z₁₂⟦1⟧
   \      ^ \        \       ^
 u₁₂\ u₂₃/   \v₁₃     \w₂₃  /v₁₂⟦1⟧'
     V  /     V        V   /
      X₂       Z₁₃       X₂⟦1⟧
       \        \        ^
     v₁₂\        \w₁₃   /u₁₂⟦1⟧'
         V        V    /
          Z₁₂ ───> X₁⟦1⟧
              w₁₂
```
where `u₁₂ ≫ u₂₃ = u₁₃` and `(u₁₂,v₁₂,w₁₂), (u₁₃,v₁₃,w₁₃)` and `(u₂₃,v₂₃,w₂₃)`
are distinguished triangles.. An `Octahedron` for this data consists of
maps `m₁ : Z₁₂ ⟶ Z₁₃` and `m₃ : Z₁₃ ⟶ Z₂₃` such that `(m₁, m₃, w₂₃ ≫ v₁₂⟦1⟧')` is
a distinguished triangle and the completed diagram commutes:
```
     u₁₃      v₂₃
  X₁ ────> X₃ ────> Z₂₃ ────> Z₁₂⟦1⟧
   \      ^ \      ^  \       ^
 u₁₂\ u₂₃/   \v₁₃ /m₃  \w₂₃  /v₁₂⟦1⟧'
     V  /     V  /       V   /
      X₂       Z₁₃       X₂⟦1⟧
       \      ^  \        ^
     v₁₂\    /m₁  \w₁₃   /u₁₂⟦1⟧'
         V  /      V    /
          Z₁₂ ───> X₁⟦1⟧
              w₁₂
```
-/
@[stacks 05QK]
/-
**CategoryTheory.Triangulated.Octahedron** 是 Mathlib 中的一个归纳类型，位于命名空间 `CategoryTh
eory.Triangulated`。
形式化陈述：{C : Type u_1} →   [inst : CategoryTheory.Category.{v_1, u_1} C] →     [in
st_1 : CategoryTheory.Preadditive C] →       [inst_2 : CategoryTheory.Limits.Has
ZeroObject C] →         [inst_3 : CategoryTheory.HasShift C ℤ] →           [inst
_4 : ∀ (n : ℤ), (CategoryTheory.shiftFunctor C n).Additive] →             [inst_
5 : CategoryTheory.Pretriangulated C] →               {X₁ X₂ X₃ Z₁₂ Z₂₃ Z₁₃ : C}
 →                 {u₁₂ : X₁ ⟶ X₂} →                   {u₂₃ : X₂ ⟶ X₃} →        
             {u₁₃ : X₁ ⟶ X₃} →                       CategoryTheory.CategoryStru
ct.comp u₁₂ u₂₃ = u₁₃ →                         {v₁₂ : X₂ ⟶ Z₁₂} →              
             {w₁₂ : Z₁₂ ⟶ (CategoryTheory.shiftFunctor C 1).obj X₁} →           
                  CategoryTheory.Pretriangulated.Triangle.mk u₁₂ v₁₂ w₁₂ ∈      
                           CategoryTheory.Pretriangulated.distinguishedTriangles
 →                               {v₂₃ : X₃ ⟶ Z₂₃} →                             
    {w₂₃ : Z₂₃ ⟶ (CategoryTheory.shiftFunctor C 1).obj X₂} →                    
               CategoryTheory.Pretriangulated.Triangle.mk u₂₃ v₂₃ w₂₃ ∈         
                              CategoryTheory.Pretriangulated.distinguishedTriang
les →                                     {v₁₃ : X₃ ⟶ Z₁₃} →                    
                   {w₁₃ : Z₁₃ ⟶ (CategoryTheory.shiftFunctor C 1).obj X₁} →     
                                    CategoryTheory.Pretriangulated.Triangle.mk u
₁₃ v₁₃ w₁₃ ∈                                             CategoryTheory.Pretrian
gulated.distinguishedTriangles →                                           Type 
v_1
参数：n : ℤ；CategoryTheory.shiftFunctor C n；CategoryTheory.shiftFunctor C 1；Categor
yTheory.shiftFunctor C 1；CategoryTheory.shiftFunctor C 1。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An octahedron is a type of datum whose existence is asserted by the
octahedron axiom (TR 4). The input is given by the following diagram:
```
     u₁₃      v₂₃
  X₁ ────> X₃ ────> Z₂₃       Z₁₂⟦1⟧
   \      ^ \        \       ^
 u₁₂\ u₂₃/   \v₁₃     \w₂₃  /v₁₂⟦1⟧'
     V  /     V        V   /
      X₂       Z₁₃       X₂⟦1⟧
       \        \        ^
     v₁₂\        \w₁₃   /u₁₂⟦1⟧'
         V        V    /
          Z₁₂ ───> X₁⟦1⟧
              w₁₂
```
where `u₁₂ ≫ u₂₃ = u₁₃` and `(u₁₂,v₁₂,w₁₂), (u₁₃,v₁₃,w₁₃)` and `(u₂₃,v₂₃,w₂₃)`
are distinguished triangles.. An `Octahedron` for this data consists of
maps `m₁ : Z₁₂ ⟶ Z₁₃` and `m₃ : Z₁₃ ⟶ Z₂₃` such that `(m₁, m₃, w₂₃ ≫ v₁₂⟦1⟧')` i
s
a distinguished triangle and the completed diagram commutes:
```
     u₁₃      v₂₃
  X₁ ────> X₃ ────> Z₂₃ ────> Z₁₂⟦1⟧
   \      ^ \      ^  \       ^
 u₁₂\ u₂₃/   \v₁₃ /m₃  \w₂₃  /v₁₂⟦1⟧'
     V  /     V  /       V   /
      X₂       Z₁₃       X₂⟦1⟧
       \      ^  \        ^
     v₁₂\    /m₁  \w₁₃   /u₁₂⟦1⟧'
         V  /      V    /
          Z₁₂ ───> X₁⟦1⟧
              w₁₂
```
-/
structure Octahedron
  {X₁ X₂ X₃ Z₁₂ Z₂₃ Z₁₃ : C}
  {u₁₂ : X₁ ⟶ X₂} {u₂₃ : X₂ ⟶ X₃} {u₁₃ : X₁ ⟶ X₃} (comm : u₁₂ ≫ u₂₃ = u₁₃)
  {v₁₂ : X₂ ⟶ Z₁₂} {w₁₂ : Z₁₂ ⟶ X₁⟦(1 : ℤ)⟧} (h₁₂ : Triangle.mk u₁₂ v₁₂ w₁₂ ∈ distTriang C)
  {v₂₃ : X₃ ⟶ Z₂₃} {w₂₃ : Z₂₃ ⟶ X₂⟦(1 : ℤ)⟧} (h₂₃ : Triangle.mk u₂₃ v₂₃ w₂₃ ∈ distTriang C)
  {v₁₃ : X₃ ⟶ Z₁₃} {w₁₃ : Z₁₃ ⟶ X₁⟦(1 : ℤ)⟧} (h₁₃ : Triangle.mk u₁₃ v₁₃ w₁₃ ∈ distTriang C) where
  /-- `m₁` is the morphism `a` of (TR 4) as presented in Stacks. -/
  m₁ : Z₁₂ ⟶ Z₁₃
  /-- `m₃` is the morphism `b` of (TR 4) as presented in Stacks. -/
  m₃ : Z₁₃ ⟶ Z₂₃
  comm₁ : v₁₂ ≫ m₁ = u₂₃ ≫ v₁₃
  comm₂ : m₁ ≫ w₁₃ = w₁₂
  comm₃ : v₁₃ ≫ m₃ = v₂₃
  comm₄ : w₁₃ ≫ u₁₂⟦1⟧' = m₃ ≫ w₂₃
  mem : Triangle.mk m₁ m₃ (w₂₃ ≫ v₁₂⟦1⟧') ∈ distTriang C

set_option backward.defeqAttrib.useBackward true in
/-
**CategoryTheory.Triangulated.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Triangu
lated`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (X : C) :
    Nonempty (Octahedron (comp_id (𝟙 X)) (contractible_distinguished X)
      (contractible_distinguished X) (contractible_distinguished X)) := by
  refine ⟨⟨0, 0, ?_, ?_, ?_, ?_, isomorphic_distinguished _ (contractible_distinguished (0 : C)) _
    (Triangle.isoMk _ _ (by rfl) (by rfl) (by rfl))⟩⟩
  all_goals apply Subsingleton.elim

namespace Octahedron

attribute [reassoc] comm₁ comm₂ comm₃ comm₄

variable {X₁ X₂ X₃ Z₁₂ Z₂₃ Z₁₃ : C}
  {u₁₂ : X₁ ⟶ X₂} {u₂₃ : X₂ ⟶ X₃} {u₁₃ : X₁ ⟶ X₃} {comm : u₁₂ ≫ u₂₃ = u₁₃}
  {v₁₂ : X₂ ⟶ Z₁₂} {w₁₂ : Z₁₂ ⟶ X₁⟦(1 : ℤ)⟧} {h₁₂ : Triangle.mk u₁₂ v₁₂ w₁₂ ∈ distTriang C}
  {v₂₃ : X₃ ⟶ Z₂₃} {w₂₃ : Z₂₃ ⟶ X₂⟦(1 : ℤ)⟧} {h₂₃ : Triangle.mk u₂₃ v₂₃ w₂₃ ∈ distTriang C}
  {v₁₃ : X₃ ⟶ Z₁₃} {w₁₃ : Z₁₃ ⟶ X₁⟦(1 : ℤ)⟧} {h₁₃ : Triangle.mk u₁₃ v₁₃ w₁₃ ∈ distTriang C}
  (h : Octahedron comm h₁₂ h₂₃ h₁₃)

/-- The triangle `Z₁₂ ⟶ Z₁₃ ⟶ Z₂₃ ⟶ Z₁₂⟦1⟧` given by an octahedron. -/
@[simps!]
/-
**CategoryTheory.Triangulated.Octahedron.triangle** 是 Mathlib 中的一个定义，位于命名空间 `Cat
egoryTheory.Triangulated.Octahedron`。
形式化陈述：triangle : Triangle C
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The triangle `Z₁₂ ⟶ Z₁₃ ⟶ Z₂₃ ⟶ Z₁₂⟦1⟧` given by an octahedron.
-/
def triangle : Triangle C :=
  Triangle.mk h.m₁ h.m₃ (w₂₃ ≫ v₁₂⟦1⟧')

set_option backward.defeqAttrib.useBackward true in
/-- The first morphism of triangles given by an octahedron. -/
@[simps]
/-
**CategoryTheory.Triangulated.Octahedron.triangleMorphism** 是 Mathlib 中的一个定义，位于命
名空间 `CategoryTheory.Triangulated.Octahedron`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The first morphism of triangles given by an octahedron.
-/
def triangleMorphism₁ : Triangle.mk u₁₂ v₁₂ w₁₂ ⟶ Triangle.mk u₁₃ v₁₃ w₁₃ where
  hom₁ := 𝟙 X₁
  hom₂ := u₂₃
  hom₃ := h.m₁
  comm₁ := by
    dsimp
    rw [id_comp, comm]
  comm₂ := h.comm₁
  comm₃ := by
    dsimp
    simpa only [Functor.map_id, comp_id] using h.comm₂.symm

set_option backward.defeqAttrib.useBackward true in
/-- The second morphism of triangles given an octahedron. -/
@[simps]
/-
**CategoryTheory.Triangulated.Octahedron.triangleMorphism** 是 Mathlib 中的一个定义，位于命
名空间 `CategoryTheory.Triangulated.Octahedron`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The second morphism of triangles given an octahedron.
-/
def triangleMorphism₂ : Triangle.mk u₁₃ v₁₃ w₁₃ ⟶ Triangle.mk u₂₃ v₂₃ w₂₃ where
  hom₁ := u₁₂
  hom₂ := 𝟙 X₃
  hom₃ := h.m₃
  comm₁ := by
    dsimp
    rw [comp_id, comm]
  comm₂ := by
    dsimp
    rw [id_comp, h.comm₃]
  comm₃ := h.comm₄


variable (u₁₂ u₁₃ u₂₃ comm h₁₂ h₁₃ h₂₃)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- When two diagrams are isomorphic, an octahedron for one gives an octahedron for the other. -/
/-
**CategoryTheory.Triangulated.Octahedron.ofIso** 是 Mathlib 中的一个定义，位于命名空间 `Catego
ryTheory.Triangulated.Octahedron`。
形式化陈述：ofIso {X₁' X₂' X₃' Z₁₂' Z₂₃' Z₁₃' : C} (u₁₂' : X₁' ⟶ X₂') (u₂₃' : X₂' ⟶ X₃
') (u₁₃' : X₁' ⟶ X₃') (comm' : u₁₂' ≫ u₂₃' = u₁₃') (e₁ : X₁ ≅ X₁') (e₂ : X₂ ≅ X₂
') (e₃ : X₃ ≅ X₃') (comm₁₂ : u₁₂ ≫ e₂.hom = e₁.hom ≫ u₁₂') (comm₂₃ : u₂₃ ≫ e₃.ho
m = e₂.hom ≫ u₂₃') (v₁₂' : X₂' ⟶ Z₁₂') (w₁₂' : Z₁₂' ⟶ X₁'⟦(1 : Int)⟧) (h₁₂' : Tr
iangle.mk u₁₂' v₁₂' w₁₂' in distTriang C) (v₂₃' : X₃' ⟶ Z₂₃') (w₂₃' : Z₂₃' ⟶ X₂'
⟦(1 : Int)⟧) (h₂₃' : Triangle.mk u₂₃' v₂₃' w₂₃' in distTriang C) (v₁₃' : X₃' ⟶ Z
₁₃') (w₁₃' : Z₁₃' ⟶ X₁'⟦(1
参数：u₁₂' : X₁' ⟶ X₂'；u₂₃' : X₂' ⟶ X₃'；u₁₃' : X₁' ⟶ X₃'；comm' : u₁₂' ≫ u₂₃' = u₁₃'
；e₁ : X₁ ≅ X₁'；e₂ : X₂ ≅ X₂'；e₃ : X₃ ≅ X₃'；comm₁₂ : u₁₂ ≫ e₂.hom = e₁.hom ≫ u₁₂'
；comm₂₃ : u₂₃ ≫ e₃.hom = e₂.hom ≫ u₂₃'；v₁₂' : X₂' ⟶ Z₁₂'；w₁₂' : Z₁₂' ⟶ X₁'⟦(1 : 
Int)⟧；h₁₂' : Triangle.mk u₁₂' v₁₂' w₁₂' in distTriang C；v₂₃' : X₃' ⟶ Z₂₃'；w₂₃' :
 Z₂₃' ⟶ X₂'⟦(1 : Int)⟧；h₂₃' : Triangle.mk u₂₃' v₂₃' w₂₃' in distTriang C；v₁₃' : 
X₃' ⟶ Z₁₃'。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
When two diagrams are isomorphic, an octahedron for one gives an octahedron for 
the other.
-/
def ofIso {X₁' X₂' X₃' Z₁₂' Z₂₃' Z₁₃' : C} (u₁₂' : X₁' ⟶ X₂') (u₂₃' : X₂' ⟶ X₃') (u₁₃' : X₁' ⟶ X₃')
    (comm' : u₁₂' ≫ u₂₃' = u₁₃')
    (e₁ : X₁ ≅ X₁') (e₂ : X₂ ≅ X₂') (e₃ : X₃ ≅ X₃')
    (comm₁₂ : u₁₂ ≫ e₂.hom = e₁.hom ≫ u₁₂') (comm₂₃ : u₂₃ ≫ e₃.hom = e₂.hom ≫ u₂₃')
    (v₁₂' : X₂' ⟶ Z₁₂') (w₁₂' : Z₁₂' ⟶ X₁'⟦(1 : ℤ)⟧)
    (h₁₂' : Triangle.mk u₁₂' v₁₂' w₁₂' ∈ distTriang C)
    (v₂₃' : X₃' ⟶ Z₂₃') (w₂₃' : Z₂₃' ⟶ X₂'⟦(1 : ℤ)⟧)
    (h₂₃' : Triangle.mk u₂₃' v₂₃' w₂₃' ∈ distTriang C)
    (v₁₃' : X₃' ⟶ Z₁₃') (w₁₃' : Z₁₃' ⟶ X₁'⟦(1 : ℤ)⟧)
    (h₁₃' : Triangle.mk (u₁₃') v₁₃' w₁₃' ∈ distTriang C)
    (H : Octahedron comm' h₁₂' h₂₃' h₁₃') : Octahedron comm h₁₂ h₂₃ h₁₃ := by
  let iso₁₂ := isoTriangleOfIso₁₂ _ _ h₁₂ h₁₂' e₁ e₂ comm₁₂
  let iso₂₃ := isoTriangleOfIso₁₂ _ _ h₂₃ h₂₃' e₂ e₃ comm₂₃
  let iso₁₃ := isoTriangleOfIso₁₂ _ _ h₁₃ h₁₃' e₁ e₃ (by
    dsimp; rw [← comm, assoc, ← comm', ← reassoc_of% comm₁₂, comm₂₃])
  have eq₁₂ := iso₁₂.hom.comm₂
  have eq₁₂' := iso₁₂.hom.comm₃
  have eq₁₃ := iso₁₃.hom.comm₂
  have eq₁₃' := iso₁₃.hom.comm₃
  have eq₂₃ := iso₂₃.hom.comm₂
  have eq₂₃' := iso₂₃.hom.comm₃
  have rel₁₂ := H.triangleMorphism₁.comm₂
  have rel₁₃ := H.triangleMorphism₁.comm₃
  have rel₂₂ := H.triangleMorphism₂.comm₂
  have rel₂₃ := H.triangleMorphism₂.comm₃
  dsimp [iso₁₂, iso₂₃, iso₁₃] at eq₁₂ eq₁₂' eq₁₃ eq₁₃' eq₂₃ eq₂₃' rel₁₂ rel₁₃ rel₂₂ rel₂₃
  rw [Functor.map_id, comp_id] at rel₁₃
  rw [id_comp] at rel₂₂
  refine ⟨iso₁₂.hom.hom₃ ≫ H.m₁ ≫ iso₁₃.inv.hom₃,
    iso₁₃.hom.hom₃ ≫ H.m₃ ≫ iso₂₃.inv.hom₃, ?_, ?_, ?_, ?_, ?_⟩
  · rw [reassoc_of% eq₁₂, ← cancel_mono iso₁₃.hom.hom₃, assoc, assoc, assoc, assoc,
      iso₁₃.inv_hom_id_triangle_hom₃, eq₁₃, reassoc_of% comm₂₃, ← rel₁₂]
    dsimp
    rw [comp_id]
  · rw [← cancel_mono (e₁.hom⟦(1 : ℤ)⟧'), eq₁₂', assoc, assoc, assoc, eq₁₃',
      iso₁₃.inv_hom_id_triangle_hom₃_assoc, ← rel₁₃]
  · rw [reassoc_of% eq₁₃, reassoc_of% rel₂₂, ← cancel_mono iso₂₃.hom.hom₃, assoc, assoc,
      iso₂₃.inv_hom_id_triangle_hom₃, eq₂₃]
    dsimp
    rw [comp_id]
  · rw [← cancel_mono (e₂.hom⟦(1 : ℤ)⟧'), assoc, assoc, assoc, assoc, eq₂₃',
      iso₂₃.inv_hom_id_triangle_hom₃_assoc, ← rel₂₃, ← Functor.map_comp, comm₁₂,
      Functor.map_comp, reassoc_of% eq₁₃']
  · refine isomorphic_distinguished _ H.mem _ ?_
    refine Triangle.isoMk _ _ (Triangle.π₃.mapIso iso₁₂) (Triangle.π₃.mapIso iso₁₃)
      (Triangle.π₃.mapIso iso₂₃) (by simp) (by simp) ?_
    dsimp
    rw [assoc, ← Functor.map_comp, eq₁₂, Functor.map_comp, reassoc_of% eq₂₃']

end Octahedron

/-- An octahedron' is a type of datum whose existence follows from
the octahedron axiom (TR 4). It is a rotated version of an octahedron.
The input is given by the following diagram:
```
       v₁₂       u₁₃      w₂₃
  Z₁₂ ────> X₁ ─────> X₃ ─────> Z₂₃⟦1⟧
          ^  \       ^  \
      v₁₃/ u₁₂\  u₂₃/    \w₁₃
        /     V    /      V
      Z₁₃       X₂       Z₁₃⟦1⟧
                ^ \
            v₂₃/   \w₁₂
              /     V
           Z₂₃      Z₁₂⟦1⟧
```
where `u₁₂ ≫ u₂₃ = u₁₃` and `(v₁₂,u₁₂,w₁₂), (v₁₃,u₁₃,w₁₃)` and `(v₂₃,u₂₃,w₂₃)`
are distinguished triangles.. An `Octahedron'` for this data consists of
maps `m₁ : Z₁₂ ⟶ Z₁₃` and `m₃ : Z₁₃ ⟶ Z₂₃` such that `(m₁, m₃, v₂₃ ≫ w₁₂)` is
a distinguished triangle and the completed diagram commutes:
```
       v₁₂       u₁₃      w₂₃
  Z₁₂ ────> X₁ ─────> X₃ ─────> Z₂₃⟦1⟧
   \       ^  \       ^  \      ^
  m₁\  v₁₃/ u₁₂\  u₂₃/    \w₁₃ /m₃⟦1⟧'
     V   /     V    /      V  /
      Z₁₃       X₂       Z₁₃⟦1⟧
       \        ^ \      ^
      m₃\   v₂₃/   \w₁₂ /m₁⟦1⟧'
         V    /     V  /
          Z₂₃  ────> Z₁₂⟦1⟧
```
-/
/-
**CategoryTheory.Triangulated.Octahedron'** 是 Mathlib 中的一个归纳类型，位于命名空间 `CategoryT
heory.Triangulated`。
形式化陈述：{C : Type u_1} →   [inst : CategoryTheory.Category.{v_1, u_1} C] →     [in
st_1 : CategoryTheory.Preadditive C] →       [inst_2 : CategoryTheory.Limits.Has
ZeroObject C] →         [inst_3 : CategoryTheory.HasShift C ℤ] →           [inst
_4 : ∀ (n : ℤ), (CategoryTheory.shiftFunctor C n).Additive] →             [inst_
5 : CategoryTheory.Pretriangulated C] →               {X₁ X₂ X₃ Z₁₂ Z₂₃ Z₁₃ : C}
 →                 {u₁₂ : X₁ ⟶ X₂} →                   {u₂₃ : X₂ ⟶ X₃} →        
             {u₁₃ : X₁ ⟶ X₃} →                       CategoryTheory.CategoryStru
ct.comp u₁₂ u₂₃ = u₁₃ →                         {v₁₂ : Z₁₂ ⟶ X₁} →              
             {w₁₂ : X₂ ⟶ (CategoryTheory.shiftFunctor C 1).obj Z₁₂} →           
                  CategoryTheory.Pretriangulated.Triangle.mk v₁₂ u₁₂ w₁₂ ∈      
                           CategoryTheory.Pretriangulated.distinguishedTriangles
 →                               {v₂₃ : Z₂₃ ⟶ X₂} →                             
    {w₂₃ : X₃ ⟶ (CategoryTheory.shiftFunctor C 1).obj Z₂₃} →                    
               CategoryTheory.Pretriangulated.Triangle.mk v₂₃ u₂₃ w₂₃ ∈         
                              CategoryTheory.Pretriangulated.distinguishedTriang
les →                                     {v₁₃ : Z₁₃ ⟶ X₁} →                    
                   {w₁₃ : X₃ ⟶ (CategoryTheory.shiftFunctor C 1).obj Z₁₃} →     
                                    CategoryTheory.Pretriangulated.Triangle.mk v
₁₃ u₁₃ w₁₃ ∈                                             CategoryTheory.Pretrian
gulated.distinguishedTriangles →                                           Type 
v_1
参数：n : ℤ；CategoryTheory.shiftFunctor C n；CategoryTheory.shiftFunctor C 1；Categor
yTheory.shiftFunctor C 1；CategoryTheory.shiftFunctor C 1。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An octahedron' is a type of datum whose existence follows from
the octahedron axiom (TR 4). It is a rotated version of an octahedron.
The input is given by the following diagram:
```
       v₁₂       u₁₃      w₂₃
  Z₁₂ ────> X₁ ─────> X₃ ─────> Z₂₃⟦1⟧
          ^  \       ^  \
      v₁₃/ u₁₂\  u₂₃/    \w₁₃
        /     V    /      V
      Z₁₃       X₂       Z₁₃⟦1⟧
                ^ \
            v₂₃/   \w₁₂
              /     V
           Z₂₃      Z₁₂⟦1⟧
```
where `u₁₂ ≫ u₂₃ = u₁₃` and `(v₁₂,u₁₂,w₁₂), (v₁₃,u₁₃,w₁₃)` and `(v₂₃,u₂₃,w₂₃)`
are distinguished triangles.. An `Octahedron'` for this data consists of
maps `m₁ : Z₁₂ ⟶ Z₁₃` and `m₃ : Z₁₃ ⟶ Z₂₃` such that `(m₁, m₃, v₂₃ ≫ w₁₂)` is
a distinguished triangle and the completed diagram commutes:
```
       v₁₂       u₁₃      w₂₃
  Z₁₂ ────> X₁ ─────> X₃ ─────> Z₂₃⟦1⟧
   \       ^  \       ^  \      ^
  m₁\  v₁₃/ u₁₂\  u₂₃/    \w₁₃ /m₃⟦1⟧'
     V   /     V    /      V  /
      Z₁₃       X₂       Z₁₃⟦1⟧
       \        ^ \      ^
      m₃\   v₂₃/   \w₁₂ /m₁⟦1⟧'
         V    /     V  /
          Z₂₃  ────> Z₁₂⟦1⟧
```
-/
structure Octahedron'
  {X₁ X₂ X₃ Z₁₂ Z₂₃ Z₁₃ : C}
  {u₁₂ : X₁ ⟶ X₂} {u₂₃ : X₂ ⟶ X₃} {u₁₃ : X₁ ⟶ X₃} (comm : u₁₂ ≫ u₂₃ = u₁₃)
  {v₁₂ : Z₁₂ ⟶ X₁} {w₁₂ : X₂ ⟶ Z₁₂⟦(1 : ℤ)⟧} (h₁₂ : Triangle.mk v₁₂ u₁₂ w₁₂ ∈ distTriang C)
  {v₂₃ : Z₂₃ ⟶ X₂} {w₂₃ : X₃ ⟶ Z₂₃⟦(1 : ℤ)⟧} (h₂₃ : Triangle.mk v₂₃ u₂₃ w₂₃ ∈ distTriang C)
  {v₁₃ : Z₁₃ ⟶ X₁} {w₁₃ : X₃ ⟶ Z₁₃⟦(1 : ℤ)⟧} (h₁₃ : Triangle.mk v₁₃ u₁₃ w₁₃ ∈ distTriang C) where
  /-- `m₁` is the morphism `a` of (TR 4) as presented in Stacks. -/
  m₁ : Z₁₂ ⟶ Z₁₃
  /-- `m₁` is the morphism `b` of (TR 4) as presented in Stacks. -/
  m₃ : Z₁₃ ⟶ Z₂₃
  comm₁ : m₁ ≫ v₁₃ = v₁₂
  comm₂ : w₁₂ ≫ m₁⟦1⟧' = u₂₃ ≫ w₁₃
  comm₃ : w₁₃ ≫ m₃⟦1⟧' = w₂₃
  comm₄ : m₃ ≫ v₂₃ = v₁₃ ≫ u₁₂
  mem : Triangle.mk m₁ m₃ (v₂₃ ≫ w₁₂) ∈ distTriang C

namespace Octahedron'

attribute [reassoc] comm₁ comm₂ comm₃ comm₄

variable {X₁ X₂ X₃ Z₁₂ Z₂₃ Z₁₃ : C}
  {u₁₂ : X₁ ⟶ X₂} {u₂₃ : X₂ ⟶ X₃} {u₁₃ : X₁ ⟶ X₃} (comm : u₁₂ ≫ u₂₃ = u₁₃)
  {v₁₂ : Z₁₂ ⟶ X₁} {w₁₂ : X₂ ⟶ Z₁₂⟦(1 : ℤ)⟧} (h₁₂ : Triangle.mk v₁₂ u₁₂ w₁₂ ∈ distTriang C)
  {v₂₃ : Z₂₃ ⟶ X₂} {w₂₃ : X₃ ⟶ Z₂₃⟦(1 : ℤ)⟧} (h₂₃ : Triangle.mk v₂₃ u₂₃ w₂₃ ∈ distTriang C)
  {v₁₃ : Z₁₃ ⟶ X₁} {w₁₃ : X₃ ⟶ Z₁₃⟦(1 : ℤ)⟧} (h₁₃ : Triangle.mk v₁₃ u₁₃ w₁₃ ∈ distTriang C)
  (h : Octahedron' comm h₁₂ h₂₃ h₁₃)

/-- The triangle `Z₁₂ ⟶ Z₁₃ ⟶ Z₂₃ ⟶ Z₁₂⟦1⟧` given by an `Octahedron'`. -/
@[simps!]
/-
**CategoryTheory.Triangulated.Octahedron.triangle** 是 Mathlib 中的一个定义，位于命名空间 `Cat
egoryTheory.Triangulated.Octahedron`。
形式化陈述：triangle : Triangle C
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The triangle `Z₁₂ ⟶ Z₁₃ ⟶ Z₂₃ ⟶ Z₁₂⟦1⟧` given by an `Octahedron'`.
-/
def triangle : Triangle C :=
  Triangle.mk h.m₁ h.m₃ (v₂₃ ≫ w₁₂)

set_option backward.defeqAttrib.useBackward true in
/-- The first morphism of triangles given by an `Octahedron'`. -/
@[simps]
/-
**CategoryTheory.Triangulated.Octahedron.triangleMorphism** 是 Mathlib 中的一个定义，位于命
名空间 `CategoryTheory.Triangulated.Octahedron`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The first morphism of triangles given by an `Octahedron'`.
-/
def triangleMorphism₁ : Triangle.mk v₁₂ u₁₂ w₁₂ ⟶ Triangle.mk v₁₃ u₁₃ w₁₃ where
  hom₁ := h.m₁
  hom₂ := 𝟙 X₁
  hom₃ := u₂₃
  comm₁ := by
    dsimp
    rw [comp_id, h.comm₁]
  comm₂ := by
    dsimp
    rw [id_comp, comm]
  comm₃ := by
    dsimp
    rw [h.comm₂]

set_option backward.defeqAttrib.useBackward true in
/-- The second morphism of triangles given by an `Octahedron'`. -/
@[simps]
/-
**CategoryTheory.Triangulated.Octahedron.triangleMorphism** 是 Mathlib 中的一个定义，位于命
名空间 `CategoryTheory.Triangulated.Octahedron`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The second morphism of triangles given by an `Octahedron'`.
-/
def triangleMorphism₂ : Triangle.mk v₁₃ u₁₃ w₁₃ ⟶ Triangle.mk v₂₃ u₂₃ w₂₃ where
  hom₁ := h.m₃
  hom₂ := u₁₂
  hom₃ := 𝟙 X₃
  comm₁ := by
    dsimp
    rw [h.comm₄]
  comm₂ := by
    dsimp
    rw [comp_id, comm]
  comm₃ := by
    dsimp
    rw [id_comp, h.comm₃]

end Octahedron'

end Triangulated

open Triangulated

/-- A triangulated category is a pretriangulated category which satisfies
the octahedron axiom (TR 4). -/
@[stacks 05QK]
/-
**CategoryTheory.IsTriangulated** 是 Mathlib 中的一个归纳类型，位于命名空间 `CategoryTheory`。
形式化陈述：(C : Type u_1) →   [inst : CategoryTheory.Category.{v_1, u_1} C] →     [in
st_1 : CategoryTheory.Preadditive C] →       [inst_2 : CategoryTheory.Limits.Has
ZeroObject C] →         [inst_3 : CategoryTheory.HasShift C ℤ] →           [inst
_4 : ∀ (n : ℤ), (CategoryTheory.shiftFunctor C n).Additive] → [CategoryTheory.Pr
etriangulated C] → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A triangulated category is a pretriangulated category which satisfies
the octahedron axiom (TR 4).
-/
class IsTriangulated : Prop where
  /-- the octahedron axiom (TR 4) -/
  octahedron_axiom :
    ∀ {X₁ X₂ X₃ Z₁₂ Z₂₃ Z₁₃ : C}
      {u₁₂ : X₁ ⟶ X₂} {u₂₃ : X₂ ⟶ X₃} {u₁₃ : X₁ ⟶ X₃} (comm : u₁₂ ≫ u₂₃ = u₁₃)
      {v₁₂ : X₂ ⟶ Z₁₂} {w₁₂ : Z₁₂ ⟶ X₁⟦(1 : ℤ)⟧} (h₁₂ : Triangle.mk u₁₂ v₁₂ w₁₂ ∈ distTriang C)
      {v₂₃ : X₃ ⟶ Z₂₃} {w₂₃ : Z₂₃ ⟶ X₂⟦(1 : ℤ)⟧} (h₂₃ : Triangle.mk u₂₃ v₂₃ w₂₃ ∈ distTriang C)
      {v₁₃ : X₃ ⟶ Z₁₃} {w₁₃ : Z₁₃ ⟶ X₁⟦(1 : ℤ)⟧} (h₁₃ : Triangle.mk u₁₃ v₁₃ w₁₃ ∈ distTriang C),
      Nonempty (Octahedron comm h₁₂ h₂₃ h₁₃)

variable {C}

/-- A choice of octahedron given by the octahedron axiom. -/
/-
**CategoryTheory.Triangulated.someOctahedron** 是 Mathlib 中的一个定义，位于命名空间 `Category
Theory.Triangulated`。
形式化陈述：{C : Type u_1} →   [inst : CategoryTheory.Category.{v_1, u_1} C] →     [in
st_1 : CategoryTheory.Preadditive C] →       [inst_2 : CategoryTheory.Limits.Has
ZeroObject C] →         [inst_3 : CategoryTheory.HasShift C ℤ] →           [inst
_4 : ∀ (n : ℤ), (CategoryTheory.shiftFunctor C n).Additive] →             [inst_
5 : CategoryTheory.Pretriangulated C] →               [CategoryTheory.IsTriangul
ated C] →                 {X₁ X₂ X₃ Z₁₂ Z₂₃ Z₁₃ : C} →                   {u₁₂ : 
X₁ ⟶ X₂} →                     {u₂₃ : X₂ ⟶ X₃} →                       {u₁₃ : X₁
 ⟶ X₃} →                         (comm : CategoryTheory.CategoryStruct.comp u₁₂ 
u₂₃ = u₁₃) →                           {v₁₂ : X₂ ⟶ Z₁₂} →                       
      {w₁₂ : Z₁₂ ⟶ (CategoryTheory.shiftFunctor C 1).obj X₁} →                  
             (h₁₂ :                                   CategoryTheory.Pretriangul
ated.Triangle.mk u₁₂ v₁₂ w₁₂ ∈                                     CategoryTheor
y.Pretriangulated.distinguishedTriangles) →                                 {v₂₃
 : X₃ ⟶ Z₂₃} →                                   {w₂₃ : Z₂₃ ⟶ (CategoryTheory.sh
iftFunctor C 1).obj X₂} →                                     (h₂₃ :            
                             CategoryTheory.Pretriangulated.Triangle.mk u₂₃ v₂₃ 
w₂₃ ∈                                           CategoryTheory.Pretriangulated.d
istinguishedTriangles) →                                       {v₁₃ : X₃ ⟶ Z₁₃} 
→                                         {w₁₃ : Z₁₃ ⟶ (CategoryTheory.shiftFunc
tor C 1).obj X₁} →                                           (h₁₃ :             
                                  CategoryTheory.Pretriangulated.Triangle.mk u₁₃
 v₁₃ w₁₃ ∈                                                 CategoryTheory.Pretri
angulated.distinguishedTriangles) →                                             
CategoryTheory.Triangulated.Octahedron comm h₁₂ h₂₃ h₁₃
参数：n : ℤ；CategoryTheory.shiftFunctor C n；comm : CategoryTheory.CategoryStruct.co
mp u₁₂ u₂₃ = u₁₃；CategoryTheory.shiftFunctor C 1；h₁₂ :                          
         CategoryTheory.Pretriangulated.Triangle.mk u₁₂ v₁₂ w₁₂ ∈               
                      CategoryTheory.Pretriangulated.distinguishedTriangles；Cate
goryTheory.shiftFunctor C 1；h₂₃ :                                         Catego
ryTheory.Pretriangulated.Triangle.mk u₂₃ v₂₃ w₂₃ ∈                              
             CategoryTheory.Pretriangulated.distinguishedTriangles；CategoryTheor
y.shiftFunctor C 1；h₁₃ :                                               CategoryT
heory.Pretriangulated.Triangle.mk u₁₃ v₁₃ w₁₃ ∈                                 
                CategoryTheory.Pretriangulated.distinguishedTriangles。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.IsTriangulated.octahedron_axiom`：∀ {C : Type u_1} {inst :
 CategoryTheory.Category.{v_1, u_1} C} {inst_1 : CategoryTheory.Preadditive C}  
 {inst_2 : CategoryTheory.Limits.Has…

--- 原说明 ---
A choice of octahedron given by the octahedron axiom.
-/
@[no_expose] def Triangulated.someOctahedron [IsTriangulated C]
    {X₁ X₂ X₃ Z₁₂ Z₂₃ Z₁₃ : C}
    {u₁₂ : X₁ ⟶ X₂} {u₂₃ : X₂ ⟶ X₃} {u₁₃ : X₁ ⟶ X₃} (comm : u₁₂ ≫ u₂₃ = u₁₃)
    {v₁₂ : X₂ ⟶ Z₁₂} {w₁₂ : Z₁₂ ⟶ X₁⟦(1 : ℤ)⟧} (h₁₂ : Triangle.mk u₁₂ v₁₂ w₁₂ ∈ distTriang C)
    {v₂₃ : X₃ ⟶ Z₂₃} {w₂₃ : Z₂₃ ⟶ X₂⟦(1 : ℤ)⟧} (h₂₃ : Triangle.mk u₂₃ v₂₃ w₂₃ ∈ distTriang C)
    {v₁₃ : X₃ ⟶ Z₁₃} {w₁₃ : Z₁₃ ⟶ X₁⟦(1 : ℤ)⟧} (h₁₃ : Triangle.mk u₁₃ v₁₃ w₁₃ ∈ distTriang C) :
    Octahedron comm h₁₂ h₂₃ h₁₃ :=
  (IsTriangulated.octahedron_axiom comm h₁₂ h₂₃ h₁₃).some

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- A choice of octahedron' given by the octahedron axiom. -/
/-
**CategoryTheory.Triangulated.someOctahedron'** 是 Mathlib 中的一个定义，位于命名空间 `Categor
yTheory.Triangulated`。
形式化陈述：{C : Type u_1} →   [inst : CategoryTheory.Category.{v_1, u_1} C] →     [in
st_1 : CategoryTheory.Preadditive C] →       [inst_2 : CategoryTheory.Limits.Has
ZeroObject C] →         [inst_3 : CategoryTheory.HasShift C ℤ] →           [inst
_4 : ∀ (n : ℤ), (CategoryTheory.shiftFunctor C n).Additive] →             [inst_
5 : CategoryTheory.Pretriangulated C] →               [CategoryTheory.IsTriangul
ated C] →                 {X₁ X₂ X₃ Z₁₂ Z₂₃ Z₁₃ : C} →                   {u₁₂ : 
X₁ ⟶ X₂} →                     {u₂₃ : X₂ ⟶ X₃} →                       {u₁₃ : X₁
 ⟶ X₃} →                         (comm : CategoryTheory.CategoryStruct.comp u₁₂ 
u₂₃ = u₁₃) →                           {v₁₂ : Z₁₂ ⟶ X₁} →                       
      {w₁₂ : X₂ ⟶ (CategoryTheory.shiftFunctor C 1).obj Z₁₂} →                  
             (h₁₂ :                                   CategoryTheory.Pretriangul
ated.Triangle.mk v₁₂ u₁₂ w₁₂ ∈                                     CategoryTheor
y.Pretriangulated.distinguishedTriangles) →                                 {v₂₃
 : Z₂₃ ⟶ X₂} →                                   {w₂₃ : X₃ ⟶ (CategoryTheory.shi
ftFunctor C 1).obj Z₂₃} →                                     (h₂₃ :            
                             CategoryTheory.Pretriangulated.Triangle.mk v₂₃ u₂₃ 
w₂₃ ∈                                           CategoryTheory.Pretriangulated.d
istinguishedTriangles) →                                       {v₁₃ : Z₁₃ ⟶ X₁} 
→                                         {w₁₃ : X₃ ⟶ (CategoryTheory.shiftFunct
or C 1).obj Z₁₃} →                                           (h₁₃ :             
                                  CategoryTheory.Pretriangulated.Triangle.mk v₁₃
 u₁₃ w₁₃ ∈                                                 CategoryTheory.Pretri
angulated.distinguishedTriangles) →                                             
CategoryTheory.Triangulated.Octahedron' comm h₁₂ h₂₃ h₁₃
参数：n : ℤ；CategoryTheory.shiftFunctor C n；comm : CategoryTheory.CategoryStruct.co
mp u₁₂ u₂₃ = u₁₃；CategoryTheory.shiftFunctor C 1；h₁₂ :                          
         CategoryTheory.Pretriangulated.Triangle.mk v₁₂ u₁₂ w₁₂ ∈               
                      CategoryTheory.Pretriangulated.distinguishedTriangles；Cate
goryTheory.shiftFunctor C 1；h₂₃ :                                         Catego
ryTheory.Pretriangulated.Triangle.mk v₂₃ u₂₃ w₂₃ ∈                              
             CategoryTheory.Pretriangulated.distinguishedTriangles；CategoryTheor
y.shiftFunctor C 1；h₁₃ :                                               CategoryT
heory.Pretriangulated.Triangle.mk v₁₃ u₁₃ w₁₃ ∈                                 
                CategoryTheory.Pretriangulated.distinguishedTriangles。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A choice of octahedron' given by the octahedron axiom.
-/
@[no_expose] def Triangulated.someOctahedron' [IsTriangulated C]
    {X₁ X₂ X₃ Z₁₂ Z₂₃ Z₁₃ : C}
    {u₁₂ : X₁ ⟶ X₂} {u₂₃ : X₂ ⟶ X₃} {u₁₃ : X₁ ⟶ X₃} (comm : u₁₂ ≫ u₂₃ = u₁₃)
    {v₁₂ : Z₁₂ ⟶ X₁} {w₁₂ : X₂ ⟶ Z₁₂⟦(1 : ℤ)⟧} (h₁₂ : Triangle.mk v₁₂ u₁₂ w₁₂ ∈ distTriang C)
    {v₂₃ : Z₂₃ ⟶ X₂} {w₂₃ : X₃ ⟶ Z₂₃⟦(1 : ℤ)⟧} (h₂₃ : Triangle.mk v₂₃ u₂₃ w₂₃ ∈ distTriang C)
    {v₁₃ : Z₁₃ ⟶ X₁} {w₁₃ : X₃ ⟶ Z₁₃⟦(1 : ℤ)⟧} (h₁₃ : Triangle.mk v₁₃ u₁₃ w₁₃ ∈ distTriang C) :
    Octahedron' comm h₁₂ h₂₃ h₁₃ := by
  let o := someOctahedron comm (rot_of_distTriang _ h₁₂) (rot_of_distTriang _ h₂₃)
    (rot_of_distTriang _ h₁₃)
  let m₁ := (shiftShiftNeg Z₁₂ 1).inv ≫ o.m₁⟦-1⟧' ≫ (shiftShiftNeg Z₁₃ 1).hom
  let m₃ := (shiftShiftNeg Z₁₃ 1).inv ≫ o.m₃⟦-1⟧' ≫ (shiftShiftNeg Z₂₃ 1).hom
  have eq₁ := o.comm₁
  have eq₂ := o.comm₂
  have eq₃ := o.comm₃
  have eq₄ := o.comm₄
  dsimp only [Triangle.mk_obj₁, Triangle.mk_obj₂, Triangle.mk_mor₁, Triangle.mk_mor₃]
    at eq₁ eq₂ eq₃ eq₄
  rw [comp_neg, neg_inj] at eq₂
  rw [neg_comp, comp_neg, neg_inj] at eq₄
  refine ⟨m₁, m₃, ?_, ?_, ?_, ?_, ?_⟩
  · rw [← shiftFunctorCompIsoId_naturality_1 v₁₃ 1 (-1) (Int.add_right_neg 1)]
    dsimp [m₁]
    rw [assoc, assoc, Iso.hom_inv_id_app_assoc]
    nth_rw 2 [← assoc]
    rw [← Functor.map_comp, eq₂, shiftFunctorCompIsoId_naturality_1]
  · dsimp [m₁]
    rw [Functor.map_comp, Functor.map_comp, shift_shiftFunctorCompIsoId_hom_app,
      shift_shiftFunctorCompIsoId_inv_app, shiftFunctorCompIsoId_naturality_1, eq₁]
  · dsimp [m₃]
    rw [Functor.map_comp, Functor.map_comp, shift_shiftFunctorCompIsoId_hom_app,
      shift_shiftFunctorCompIsoId_inv_app, shiftFunctorCompIsoId_naturality_1, eq₃]
  · rw [← shiftFunctorCompIsoId_naturality_1 v₂₃ 1 (-1) (Int.add_right_neg 1)]
    dsimp [m₃]
    rw [assoc, assoc, Iso.hom_inv_id_app_assoc]
    nth_rw 2 [← assoc]
    rw [← Functor.map_comp, ← eq₄, ← Functor.map_comp, shiftFunctorCompIsoId_naturality_1]
  · apply isomorphic_distinguished _ ((Triangle.shift_distinguished_iff _ (-1 : ℤ)).mpr o.mem)
    refine Triangle.isoMk _ _ (shiftShiftNeg Z₁₂ (1 : ℤ)).symm
      (-(shiftShiftNeg Z₁₃ (1 : ℤ)).symm) (shiftShiftNeg Z₂₃ (1 : ℤ)).symm (comm₃ := ?_)
    dsimp
    simp only [Int.reduceNeg, assoc, Int.negOnePow_neg, Int.negOnePow_one, neg_comp,
      Functor.map_neg, Functor.map_comp, smul_neg, Units.neg_smul, one_smul, neg_neg]
    rw [shift_shift_neg', shift_shift_neg', shift_shiftFunctorCompIsoId_inv_app,
      shiftFunctorComm_hom_app_of_add_eq_zero _ _ (Int.add_right_neg 1)]
    simp

/-- Constructor for `IsTriangulated C` which shows that it suffices to obtain an octahedron
for a suitable isomorphic diagram instead of the given diagram. -/
/-
**CategoryTheory.IsTriangulated.mk'** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.Is
Triangulated`。
形式化陈述：∀ {C : Type u_1} [inst : CategoryTheory.Category.{v_1, u_1} C] [inst_1 : C
ategoryTheory.Preadditive C]   [inst_2 : CategoryTheory.Limits.HasZeroObject C] 
[inst_3 : CategoryTheory.HasShift C ℤ]   [inst_4 : ∀ (n : ℤ), (CategoryTheory.sh
iftFunctor C n).Additive] [inst_5 : CategoryTheory.Pretriangulated C],   (∀ ⦃X₁'
 X₂' X₃' : C⦄ (u₁₂' : X₁' ⟶ X₂') (u₂₃' : X₂' ⟶ X₃'),       ∃ X₁ X₂ X₃ Z₁₂ Z₂₃ Z₁
₃ u₁₂ u₂₃ e₁ e₂ e₃,         ∃ (_ : CategoryTheory.CategoryStruct.comp u₁₂' e₂.ho
m = CategoryTheory.CategoryStruct.comp e₁.hom u₁₂) (_ :           CategoryTheory
.CategoryStruct.comp u₂₃' e₃.hom = CategoryTheory.CategoryStruct.comp e₂.hom u₂₃
),           ∃ v₁₂ w₁₂,             ∃ (h₁₂ :               CategoryTheory.Pretri
angulated.Triangle.mk u₁₂ v₁₂ w₁₂ ∈                 CategoryTheory.Pretriangulat
ed.distinguishedTriangles),               ∃ v₂₃ w₂₃,                 ∃ (h₂₃ :   
                CategoryTheory.Pretriangulated.Triangle.mk u₂₃ v₂₃ w₂₃ ∈        
             CategoryTheory.Pretriangulated.distinguishedTriangles),            
       ∃ v₁₃ w₁₃,                     ∃ (h₁₃ :                       CategoryThe
ory.Pretriangulated.Triangle.mk (CategoryTheory.CategoryStruct.comp u₁₂ u₂₃) v₁₃
 w₁₃ ∈                         CategoryTheory.Pretriangulated.distinguishedTrian
gles),                       Nonempty (CategoryTheory.Triangulated.Octahedron ⋯ 
h₁₂ h₂₃ h₁₃)) →     CategoryTheory.IsTriangulated C
参数：n : ℤ；CategoryTheory.shiftFunctor C n；∀ ⦃X₁' X₂' X₃' : C⦄ (u₁₂' : X₁' ⟶ X₂') 
(u₂₃' : X₂' ⟶ X₃'),       ∃ X₁ X₂ X₃ Z₁₂ Z₂₃ Z₁₃ u₁₂ u₂₃ e₁ e₂ e₃,         ∃ (_ 
: CategoryTheory.CategoryStruct.comp u₁₂' e₂.hom = CategoryTheory.CategoryStruct
.comp e₁.hom u₁₂) (_ :           CategoryTheory.CategoryStruct.comp u₂₃' e₃.hom 
= CategoryTheory.CategoryStruct.comp e₂.hom u₂₃),           ∃ v₁₂ w₁₂,          
   ∃ (h₁₂ :               CategoryTheory.Pretriangulated.Triangle.mk u₁₂ v₁₂ w₁₂
 ∈                 CategoryTheory.Pretriangulated.distinguishedTriangles),      
         ∃ v₂₃ w₂₃,                 ∃ (h₂₃ :                   CategoryTheory.Pr
etriangulated.Triangle.mk u₂₃ v₂₃ w₂₃ ∈                     CategoryTheory.Pretr
iangulated.distinguishedTriangles),                   ∃ v₁₃ w₁₃,                
     ∃ (h₁₃ :                       CategoryTheory.Pretriangulated.Triangle.mk (
CategoryTheory.CategoryStruct.comp u₁₂ u₂₃) v₁₃ w₁₃ ∈                         Ca
tegoryTheory.Pretriangulated.distinguishedTriangles),                       None
mpty (CategoryTheory.Triangulated.Octahedron ⋯ h₁₂ h₂₃ h₁₃)。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Constructor for `IsTriangulated C` which shows that it suffices to obtain an oct
ahedron
for a suitable isomorphic diagram instead of the given diagram.
-/
lemma IsTriangulated.mk' (h : ∀ ⦃X₁' X₂' X₃' : C⦄ (u₁₂' : X₁' ⟶ X₂') (u₂₃' : X₂' ⟶ X₃'),
    ∃ (X₁ X₂ X₃ Z₁₂ Z₂₃ Z₁₃ : C) (u₁₂ : X₁ ⟶ X₂) (u₂₃ : X₂ ⟶ X₃) (e₁ : X₁' ≅ X₁) (e₂ : X₂' ≅ X₂)
    (e₃ : X₃' ≅ X₃) (_ : u₁₂' ≫ e₂.hom = e₁.hom ≫ u₁₂)
    (_ : u₂₃' ≫ e₃.hom = e₂.hom ≫ u₂₃)
    (v₁₂ : X₂ ⟶ Z₁₂) (w₁₂ : Z₁₂ ⟶ X₁⟦1⟧) (h₁₂ : Triangle.mk u₁₂ v₁₂ w₁₂ ∈ distTriang C)
    (v₂₃ : X₃ ⟶ Z₂₃) (w₂₃ : Z₂₃ ⟶ X₂⟦1⟧) (h₂₃ : Triangle.mk u₂₃ v₂₃ w₂₃ ∈ distTriang C)
    (v₁₃ : X₃ ⟶ Z₁₃) (w₁₃ : Z₁₃ ⟶ X₁⟦1⟧)
      (h₁₃ : Triangle.mk (u₁₂ ≫ u₂₃) v₁₃ w₁₃ ∈ distTriang C),
        Nonempty (Octahedron rfl h₁₂ h₂₃ h₁₃)) :
    IsTriangulated C where
  octahedron_axiom {X₁' X₂' X₃' Z₁₂' Z₂₃' Z₁₃' u₁₂' u₂₃' u₁₃'} comm'
    {v₁₂' w₁₂'} h₁₂' {v₂₃' w₂₃'} h₂₃' {v₁₃' w₁₃'} h₁₃' := by
    obtain ⟨X₁, X₂, X₃, Z₁₂, Z₂₃, Z₁₃, u₁₂, u₂₃, e₁, e₂, e₃, comm₁₂, comm₂₃,
      v₁₂, w₁₂, h₁₂, v₂₃, w₂₃, h₂₃, v₁₃, w₁₃, h₁₃, H⟩ := h u₁₂' u₂₃'
    exact ⟨Octahedron.ofIso u₁₂' u₂₃' u₁₃' comm' h₁₂' h₂₃' h₁₃'
      u₁₂ u₂₃ _ rfl e₁ e₂ e₃ comm₁₂ comm₂₃ v₁₂ w₁₂ h₁₂ v₂₃ w₂₃ h₂₃ v₁₃ w₁₃ h₁₃ H.some⟩

end CategoryTheory

