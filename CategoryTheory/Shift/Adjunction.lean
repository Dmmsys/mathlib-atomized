/-
Copyright (c) 2024 Sophie Morel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sophie Morel, Joël Riou
-/
module

public import Mathlib.CategoryTheory.Shift.CommShift
public import Mathlib.CategoryTheory.Adjunction.Mates
public import Mathlib.Tactic.CategoryTheory.CancelIso

/-!
# Adjoints commute with shifts

Given categories `C` and `D` that have shifts by an additive group `A`, functors `F : C ⥤ D`
and `G : C ⥤ D`, an adjunction `F ⊣ G` and a `CommShift` structure on `F`, this file constructs
a `CommShift` structure on `G`. We also do the construction in the other direction: given a
`CommShift` structure on `G`, we construct a `CommShift` structure on `G`; we could do this
using opposite categories, but the construction is simple enough that it is not really worth it.
As an easy application, if `E : C ≌ D` is an equivalence and `E.functor` has a `CommShift`
structure, we get a `CommShift` structure on `E.inverse`.

We now explain the construction of a `CommShift` structure on `G` given a `CommShift` structure
on `F`; the other direction is similar. The `CommShift` structure on `G` must be compatible with
the one on `F` in the following sense (cf. `Adjunction.CommShift`):
for every `a` in `A`, the natural transformation `adj.unit : 𝟭 C ⟶ G ⋙ F` commutes with
the isomorphism `shiftFunctor C A ⋙ G ⋙ F ≅ G ⋙ F ⋙ shiftFunctor C A` induces by
`F.commShiftIso a` and `G.commShiftIso a`. We actually require a similar condition for
`adj.counit`, but it follows from the one for `adj.unit`.

In order to simplify the construction of the `CommShift` structure on `G`, we first introduce
the compatibility condition on `adj.unit` for a fixed `a` in `A` and for isomorphisms
`e₁ : shiftFunctor C a ⋙ F ≅ F ⋙ shiftFunctor D a` and
`e₂ : shiftFunctor D a ⋙ G ≅ G ⋙ shiftFunctor C a`. We then prove that:
- If `e₁` and `e₂` satisfy this condition, then `e₁` uniquely determines `e₂` and vice versa.
- If `a = 0`, the isomorphisms `Functor.CommShift.isoZero F` and `Functor.CommShift.isoZero G`
  satisfy the condition.
- The condition is stable by addition on `A`, if we use `Functor.CommShift.isoAdd` to deduce
  commutation isomorphism for `a + b` from such isomorphism from `a` and `b`.
- Given commutation isomorphisms for `F`, our candidate commutation isomorphisms for `G`,
  constructed in `Adjunction.RightAdjointCommShift.iso`, satisfy the compatibility condition.

Once we have established all this, the compatibility of the commutation isomorphism for
`F` expressed in `CommShift.zero` and `CommShift.add` immediately implies the similar
statements for the commutation isomorphisms for `G`.

-/

@[expose] public section

namespace CategoryTheory

open Category

namespace Adjunction

variable {C D : Type*} [Category* C] [Category* D]
  {F : C ⥤ D} {G : D ⥤ C} (adj : F ⊣ G) {A : Type*} [AddMonoid A] [HasShift C A] [HasShift D A]

namespace CommShift

variable {a b : A} (e₁ : shiftFunctor C a ⋙ F ≅ F ⋙ shiftFunctor D a)
    (e₁' : shiftFunctor C a ⋙ F ≅ F ⋙ shiftFunctor D a)
    (f₁ : shiftFunctor C b ⋙ F ≅ F ⋙ shiftFunctor D b)
    (e₂ : shiftFunctor D a ⋙ G ≅ G ⋙ shiftFunctor C a)
    (e₂' : shiftFunctor D a ⋙ G ≅ G ⋙ shiftFunctor C a)
    (f₂ : shiftFunctor D b ⋙ G ≅ G ⋙ shiftFunctor C b)

/-- Given an adjunction `adj : F ⊣ G`, `a` in `A` and commutation isomorphisms
`e₁ : shiftFunctor C a ⋙ F ≅ F ⋙ shiftFunctor D a` and
`e₂ : shiftFunctor D a ⋙ G ≅ G ⋙ shiftFunctor C a`, this expresses the compatibility of
`e₁` and `e₂` with the unit of the adjunction `adj`.
-/
/-
**CategoryTheory.Adjunction.CommShift.CompatibilityUnit** 是 Mathlib 中的一个缩写定义，位于命
名空间 `CategoryTheory.Adjunction.CommShift`。
形式化陈述：CompatibilityUnit
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given an adjunction `adj : F ⊣ G`, `a` in `A` and commutation isomorphisms
`e₁ : shiftFunctor C a ⋙ F ≅ F ⋙ shiftFunctor D a` and
`e₂ : shiftFunctor D a ⋙ G ≅ G ⋙ shiftFunctor C a`, this expresses the compatibi
lity of
`e₁` and `e₂` with the unit of the adjunction `adj`.
-/
abbrev CompatibilityUnit :=
  ∀ (X : C), (adj.unit.app X)⟦a⟧' = adj.unit.app (X⟦a⟧) ≫ G.map (e₁.hom.app X) ≫ e₂.hom.app _

/-- Given an adjunction `adj : F ⊣ G`, `a` in `A` and commutation isomorphisms
`e₁ : shiftFunctor C a ⋙ F ≅ F ⋙ shiftFunctor D a` and
`e₂ : shiftFunctor D a ⋙ G ≅ G ⋙ shiftFunctor C a`, this expresses the compatibility of
`e₁` and `e₂` with the counit of the adjunction `adj`.
-/
/-
**CategoryTheory.Adjunction.CommShift.CompatibilityCounit** 是 Mathlib 中的一个缩写定义，位
于命名空间 `CategoryTheory.Adjunction.CommShift`。
形式化陈述：CompatibilityCounit
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given an adjunction `adj : F ⊣ G`, `a` in `A` and commutation isomorphisms
`e₁ : shiftFunctor C a ⋙ F ≅ F ⋙ shiftFunctor D a` and
`e₂ : shiftFunctor D a ⋙ G ≅ G ⋙ shiftFunctor C a`, this expresses the compatibi
lity of
`e₁` and `e₂` with the counit of the adjunction `adj`.
-/
abbrev CompatibilityCounit :=
  ∀ (Y : D), adj.counit.app (Y⟦a⟧) = F.map (e₂.hom.app Y) ≫ e₁.hom.app _ ≫ (adj.counit.app Y)⟦a⟧'

set_option backward.defeqAttrib.useBackward true in
/-- Given an adjunction `adj : F ⊣ G`, `a` in `A` and commutation isomorphisms
`e₁ : shiftFunctor C a ⋙ F ≅ F ⋙ shiftFunctor D a` and
`e₂ : shiftFunctor D a ⋙ G ≅ G ⋙ shiftFunctor C a`, compatibility of `e₁` and `e₂` with the
unit of the adjunction `adj` implies compatibility with the counit of `adj`.
-/
/-
**CategoryTheory.Adjunction.CommShift.compatibilityCounit_of_compatibilityUnit**
 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.Adjunction.CommShift`。
形式化陈述：compatibilityCounit_of_compatibilityUnit (h : CompatibilityUnit adj e₁ e₂)
 : CompatibilityCounit adj e₁ e₂
参数：h : CompatibilityUnit adj e₁ e₂。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.injective`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β), Function.Injec
tive ⇑e
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Adjunction.homEquiv_unit`：∀ {C : Type u₁} [inst : Categor
yTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂
, u₂} D]   {F : CategoryTheor…
· 使用定理 `CategoryTheory.Functor.map_comp`：∀ {C : Type u₁} [inst : CategoryTheory.
Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]
   (self : CategoryTh…
· 使用定理 `CategoryTheory.Adjunction.unit_naturality_assoc`：∀ {C : Type u₁} [inst :
 CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Cate
gory.{v₂, u₂} D]   {F : CategoryTheor…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `CategoryTheory.cancel_mono`：∀ {C : Type u} [inst : CategoryTheory.Catego
ry.{v, u} C] {X Y Z : C} (f : Y ⟶ X) [CategoryTheory.Mono f] {g h : Z ⟶ Y},   Ca
tegoryTheory.Cat…
· 使用定理 `CategoryTheory.mono_comp`：∀ {C : Type u} [inst : CategoryTheory.Category
.{v, u} C] {X Y Z : C} (g : Z ⟶ Y) [CategoryTheory.Mono g] (f : Y ⟶ X)   [Catego
ryTheory.Mono …
· 使用定理 `CategoryTheory.StrongMono.mono`：∀ {C : Type u} {inst : CategoryTheory.Ca
tegory.{v, u} C} {P Q : C} {f : P ⟶ Q} [self : CategoryTheory.StrongMono f],   C
ategoryTheory.Mono f
· 使用定理 `CategoryTheory.strongMono_of_isIso`：∀ {C : Type u} [inst : CategoryTheor
y.Category.{v, u} C] {P Q : C} (f : Q ⟶ P) [CategoryTheory.IsIso f],   CategoryT
heory.StrongMono f
· 使用定理 `CategoryTheory.NatIso.inv_app_isIso`：∀ {C : Type u₁} [inst : CategoryThe
ory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂
} D]   {F G : CategoryThe…
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.Iso.hom_inv_id_app_assoc`：∀ {C : Type u₁} [inst : Categor
yTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂
, u₂} D]   {F G : CategoryThe…
· 使用定理 `CategoryTheory.Iso.hom_inv_id_app`：∀ {C : Type u₁} [inst : CategoryTheor
y.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} 
D]   {F G : CategoryThe…
· 使用定理 `CategoryTheory.Functor.map_id`：∀ {C : Type u₁} [inst : CategoryTheory.Ca
tegory.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]  
 (self : CategoryTh…
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `CategoryTheory.Iso.inv_hom_id_app_assoc`：∀ {C : Type u₁} [inst : Categor
yTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂
, u₂} D]   {F G : CategoryThe…
· 使用定理 `CategoryTheory.NatTrans.naturality`：∀ {C : Type u₁} [inst : CategoryTheo
ry.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂}
 D]   {F G : CategoryThe…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `CategoryTheory.Adjunction.right_triangle_components`：∀ {C : Type u₁} [in
st : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.
Category.{v₂, u₂} D]   {F : CategoryTheor…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
Given an adjunction `adj : F ⊣ G`, `a` in `A` and commutation isomorphisms
`e₁ : shiftFunctor C a ⋙ F ≅ F ⋙ shiftFunctor D a` and
`e₂ : shiftFunctor D a ⋙ G ≅ G ⋙ shiftFunctor C a`, compatibility of `e₁` and `e
₂` with the
unit of the adjunction `adj` implies compatibility with the counit of `adj`.
-/
lemma compatibilityCounit_of_compatibilityUnit (h : CompatibilityUnit adj e₁ e₂) :
    CompatibilityCounit adj e₁ e₂ := by
  intro Y
  have eq := h (G.obj Y)
  simp only [← cancel_mono (e₂.inv.app _ ≫ G.map (e₁.inv.app _)),
    assoc, Iso.hom_inv_id_app_assoc, comp_id, ← Functor.map_comp,
    Iso.hom_inv_id_app, Functor.comp_obj, Functor.map_id] at eq
  apply (adj.homEquiv _ _).injective
  dsimp
  rw [adj.homEquiv_unit, adj.homEquiv_unit, G.map_comp, adj.unit_naturality_assoc, ← eq]
  simp only [assoc, ← Functor.map_comp, Iso.inv_hom_id_app_assoc]
  erw [← e₂.inv.naturality]
  dsimp
  simp only [right_triangle_components, ← Functor.map_comp_assoc, Functor.map_id, id_comp,
    Iso.hom_inv_id_app, Functor.comp_obj]

set_option backward.defeqAttrib.useBackward true in
/-- Given an adjunction `adj : F ⊣ G`, `a` in `A` and commutation isomorphisms
`e₁ : shiftFunctor C a ⋙ F ≅ F ⋙ shiftFunctor D a` and
`e₂ : shiftFunctor D a ⋙ G ≅ G ⋙ shiftFunctor C a`, if `e₁` and `e₂` are compatible with the
unit of the adjunction `adj`, then we get a formula for `e₂.inv` in terms of `e₁`.
-/
/-
**CategoryTheory.Adjunction.CommShift.compatibilityUnit_right** 是 Mathlib 中的一个引理
，位于命名空间 `CategoryTheory.Adjunction.CommShift`。
形式化陈述：compatibilityUnit_right (h : CompatibilityUnit adj e₁ e₂) (Y : D) : e₂.inv
.app Y = adj.unit.app _ ≫ G.map (e₁.hom.app _) ≫ G.map ((adj.counit.app _)⟦a⟧')
参数：h : CompatibilityUnit adj e₁ e₂；Y : D。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `CategoryTheory.Iso.hom_inv_id_app`：∀ {C : Type u₁} [inst : CategoryTheor
y.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} 
D]   {F G : CategoryThe…
· 使用定理 `CategoryTheory.cancel_mono`：∀ {C : Type u} [inst : CategoryTheory.Catego
ry.{v, u} C] {X Y Z : C} (f : Y ⟶ X) [CategoryTheory.Mono f] {g h : Z ⟶ Y},   Ca
tegoryTheory.Cat…
· 使用定理 `CategoryTheory.StrongMono.mono`：∀ {C : Type u} {inst : CategoryTheory.Ca
tegory.{v, u} C} {P Q : C} {f : P ⟶ Q} [self : CategoryTheory.StrongMono f],   C
ategoryTheory.Mono f
· 使用定理 `CategoryTheory.strongMono_of_isIso`：∀ {C : Type u} [inst : CategoryTheor
y.Category.{v, u} C] {P Q : C} (f : Q ⟶ P) [CategoryTheory.IsIso f],   CategoryT
heory.StrongMono f
· 使用定理 `CategoryTheory.NatIso.inv_app_isIso`：∀ {C : Type u₁} [inst : CategoryThe
ory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂
} D]   {F G : CategoryThe…
· 使用定理 `CategoryTheory.NatTrans.naturality`：∀ {C : Type u₁} [inst : CategoryTheo
ry.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂}
 D]   {F G : CategoryThe…
· 使用定理 `CategoryTheory.NatIso.hom_app_isIso`：∀ {C : Type u₁} [inst : CategoryThe
ory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂
} D]   {F G : CategoryThe…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `CategoryTheory.Iso.inv_hom_id_app`：∀ {C : Type u₁} [inst : CategoryTheor
y.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} 
D]   {F G : CategoryThe…
· 使用定理 `CategoryTheory.Functor.map_comp`：∀ {C : Type u₁} [inst : CategoryTheory.
Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]
   (self : CategoryTh…
· 使用定理 `CategoryTheory.Adjunction.right_triangle_components`：∀ {C : Type u₁} [in
st : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.
Category.{v₂, u₂} D]   {F : CategoryTheor…
· 使用定理 `CategoryTheory.Functor.map_id`：∀ {C : Type u₁} [inst : CategoryTheory.Ca
tegory.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]  
 (self : CategoryTh…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
Given an adjunction `adj : F ⊣ G`, `a` in `A` and commutation isomorphisms
`e₁ : shiftFunctor C a ⋙ F ≅ F ⋙ shiftFunctor D a` and
`e₂ : shiftFunctor D a ⋙ G ≅ G ⋙ shiftFunctor C a`, if `e₁` and `e₂` are compati
ble with the
unit of the adjunction `adj`, then we get a formula for `e₂.inv` in terms of `e₁
`.
-/
lemma compatibilityUnit_right (h : CompatibilityUnit adj e₁ e₂) (Y : D) :
    e₂.inv.app Y = adj.unit.app _ ≫ G.map (e₁.hom.app _) ≫ G.map ((adj.counit.app _)⟦a⟧') := by
  have := h (G.obj Y)
  rw [← cancel_mono (e₂.inv.app _), assoc, assoc, Iso.hom_inv_id_app] at this
  erw [comp_id] at this
  rw [← assoc, ← this, assoc]; erw [← e₂.inv.naturality]
  rw [← cancel_mono (e₂.hom.app _)]
  simp only [Functor.comp_obj, Iso.inv_hom_id_app, Functor.id_obj, Functor.comp_map, assoc, comp_id,
    ← (shiftFunctor C a).map_comp, right_triangle_components, Functor.map_id]

set_option backward.defeqAttrib.useBackward true in
/-- Given an adjunction `adj : F ⊣ G`, `a` in `A` and commutation isomorphisms
`e₁ : shiftFunctor C a ⋙ F ≅ F ⋙ shiftFunctor D a` and
`e₂ : shiftFunctor D a ⋙ G ≅ G ⋙ shiftFunctor C a`, if `e₁` and `e₂` are compatible with the
counit of the adjunction `adj`, then we get a formula for `e₁.hom` in terms of `e₂`.
-/
/-
**CategoryTheory.Adjunction.CommShift.compatibilityCounit_left** 是 Mathlib 中的一个引
理，位于命名空间 `CategoryTheory.Adjunction.CommShift`。
形式化陈述：compatibilityCounit_left (h : CompatibilityCounit adj e₁ e₂) (X : C) : e₁.
hom.app X = F.map ((adj.unit.app X)⟦a⟧') ≫ F.map (e₂.inv.app _) ≫ adj.counit.app
 _
参数：h : CompatibilityCounit adj e₁ e₂；X : C。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用定理 `CategoryTheory.Functor.map_id`：∀ {C : Type u₁} [inst : CategoryTheory.Ca
tegory.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]  
 (self : CategoryTh…
· 使用定理 `CategoryTheory.Iso.inv_hom_id_app`：∀ {C : Type u₁} [inst : CategoryTheor
y.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} 
D]   {F G : CategoryThe…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.Functor.map_comp`：∀ {C : Type u₁} [inst : CategoryTheory.
Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]
   (self : CategoryTh…
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.cancel_epi`：cancel_epi (f : X ⟶ Y) [Epi f] {g h : Y ⟶ Z} 
: f ≫ g = f ≫ h ↔ g = h
· 使用定理 `CategoryTheory.StrongEpi.epi`：∀ {C : Type u} {inst : CategoryTheory.Cate
gory.{v, u} C} {P Q : C} {f : P ⟶ Q} [self : CategoryTheory.StrongEpi f],   Cate
goryTheory.Epi f
· 使用定理 `CategoryTheory.strongEpi_of_isIso`：∀ {C : Type u} [inst : CategoryTheory
.Category.{v, u} C] {P Q : C} (f : P ⟶ Q) [CategoryTheory.IsIso f],   CategoryTh
eory.StrongEpi f
· 使用定理 `CategoryTheory.NatIso.inv_app_isIso`：∀ {C : Type u₁} [inst : CategoryThe
ory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂
} D]   {F G : CategoryThe…
· 使用定理 `CategoryTheory.NatTrans.naturality_assoc`：∀ {C : Type u₁} [inst : Catego
ryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v
₂, u₂} D]   {F G : CategoryThe…
· 使用定理 `CategoryTheory.Adjunction.left_triangle_components`：∀ {C : Type u₁} [ins
t : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.C
ategory.{v₂, u₂} D]   {F : CategoryTheor…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
Given an adjunction `adj : F ⊣ G`, `a` in `A` and commutation isomorphisms
`e₁ : shiftFunctor C a ⋙ F ≅ F ⋙ shiftFunctor D a` and
`e₂ : shiftFunctor D a ⋙ G ≅ G ⋙ shiftFunctor C a`, if `e₁` and `e₂` are compati
ble with the
counit of the adjunction `adj`, then we get a formula for `e₁.hom` in terms of `
e₂`.
-/
lemma compatibilityCounit_left (h : CompatibilityCounit adj e₁ e₂) (X : C) :
    e₁.hom.app X = F.map ((adj.unit.app X)⟦a⟧') ≫ F.map (e₂.inv.app _) ≫ adj.counit.app _ := by
  have := h (F.obj X)
  rw [← cancel_epi (F.map (e₂.inv.app _)), ← assoc, ← F.map_comp, Iso.inv_hom_id_app, F.map_id,
    id_comp] at this
  dsimp only [Functor.comp_obj, Functor.id_obj]
  rw [this, dsimp% e₁.hom.naturality_assoc, ← Functor.map_comp, left_triangle_components]
  simp only [Functor.map_id, comp_id]

/-- Given an adjunction `adj : F ⊣ G`, `a` in `A` and commutation isomorphisms
`e₁ : shiftFunctor C a ⋙ F ≅ F ⋙ shiftFunctor D a` and
`e₂ : shiftFunctor D a ⋙ G ≅ G ⋙ shiftFunctor C a`, if `e₁` and `e₂` are compatible with the
unit of the adjunction `adj`, then `e₁` uniquely determines `e₂`.
-/
/-
**CategoryTheory.Adjunction.CommShift.compatibilityUnit_unique_right** 是 Mathlib
 中的一个引理，位于命名空间 `CategoryTheory.Adjunction.CommShift`。
形式化陈述：compatibilityUnit_unique_right (h : CompatibilityUnit adj e₁ e₂) (h' : Com
patibilityUnit adj e₁ e₂') : e₂ = e₂'
参数：h : CompatibilityUnit adj e₁ e₂；h' : CompatibilityUnit adj e₁ e₂'。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.Iso.symm_eq_iff`：symm_eq_iff {X Y : C} {α β : X ≅ Y} : α.
symm = β.symm ↔ α = β
· 使用定理 `CategoryTheory.Iso.ext`：ext ⦃α β : X ≅ Y⦄ (w : α.hom = β.hom) : α = β
· 使用定理 `CategoryTheory.NatTrans.ext'`：ext' {α β : F ⟶ G} (w : α.app = β.app) : α
 = β
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `CategoryTheory.Iso.symm_hom`：symm_hom (α : X ≅ Y) : α.symm.hom = α.inv
· 使用引理 `CategoryTheory.Adjunction.CommShift.compatibilityUnit_right`：compatibili
tyUnit_right (h : CompatibilityUnit adj e₁ e₂) (Y : D) : e₂.inv.app Y = adj.unit
.app _ ≫ G.map (e₁.hom.app _) ≫ G.map ((adj.couni…

--- 原说明 ---
Given an adjunction `adj : F ⊣ G`, `a` in `A` and commutation isomorphisms
`e₁ : shiftFunctor C a ⋙ F ≅ F ⋙ shiftFunctor D a` and
`e₂ : shiftFunctor D a ⋙ G ≅ G ⋙ shiftFunctor C a`, if `e₁` and `e₂` are compati
ble with the
unit of the adjunction `adj`, then `e₁` uniquely determines `e₂`.
-/
lemma compatibilityUnit_unique_right (h : CompatibilityUnit adj e₁ e₂)
    (h' : CompatibilityUnit adj e₁ e₂') : e₂ = e₂' := by
  rw [← Iso.symm_eq_iff]
  ext
  rw [Iso.symm_hom, Iso.symm_hom, compatibilityUnit_right adj e₁ e₂ h,
    compatibilityUnit_right adj e₁ e₂' h']

/-- Given an adjunction `adj : F ⊣ G`, `a` in `A` and commutation isomorphisms
`e₁ : shiftFunctor C a ⋙ F ≅ F ⋙ shiftFunctor D a` and
`e₂ : shiftFunctor D a ⋙ G ≅ G ⋙ shiftFunctor C a`, if `e₁` and `e₂` are compatible with the
unit of the adjunction `adj`, then `e₂` uniquely determines `e₁`.
-/
/-
**CategoryTheory.Adjunction.CommShift.compatibilityUnit_unique_left** 是 Mathlib 
中的一个引理，位于命名空间 `CategoryTheory.Adjunction.CommShift`。
形式化陈述：compatibilityUnit_unique_left (h : CompatibilityUnit adj e₁ e₂) (h' : Comp
atibilityUnit adj e₁' e₂) : e₁ = e₁'
参数：h : CompatibilityUnit adj e₁ e₂；h' : CompatibilityUnit adj e₁' e₂。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Iso.ext`：ext ⦃α β : X ≅ Y⦄ (w : α.hom = β.hom) : α = β
· 使用定理 `CategoryTheory.NatTrans.ext'`：ext' {α β : F ⟶ G} (w : α.app = β.app) : α
 = β
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `CategoryTheory.Adjunction.CommShift.compatibilityCounit_left`：compatibil
ityCounit_left (h : CompatibilityCounit adj e₁ e₂) (X : C) : e₁.hom.app X = F.ma
p ((adj.unit.app X)⟦a⟧') ≫ F.map (e₂.inv.app _) ≫ …
· 使用引理 `CategoryTheory.Adjunction.CommShift.compatibilityCounit_of_compatibility
Unit`：compatibilityCounit_of_compatibilityUnit (h : CompatibilityUnit adj e₁ e₂)
 : CompatibilityCounit adj e₁ e₂

--- 原说明 ---
Given an adjunction `adj : F ⊣ G`, `a` in `A` and commutation isomorphisms
`e₁ : shiftFunctor C a ⋙ F ≅ F ⋙ shiftFunctor D a` and
`e₂ : shiftFunctor D a ⋙ G ≅ G ⋙ shiftFunctor C a`, if `e₁` and `e₂` are compati
ble with the
unit of the adjunction `adj`, then `e₂` uniquely determines `e₁`.
-/
lemma compatibilityUnit_unique_left (h : CompatibilityUnit adj e₁ e₂)
    (h' : CompatibilityUnit adj e₁' e₂) : e₁ = e₁' := by
  ext
  rw [compatibilityCounit_left adj e₁ e₂ (compatibilityCounit_of_compatibilityUnit adj _ _ h),
    compatibilityCounit_left adj e₁' e₂ (compatibilityCounit_of_compatibilityUnit adj _ _ h')]

set_option backward.defeqAttrib.useBackward true in
/--
The isomorphisms `Functor.CommShift.isoZero F` and `Functor.CommShift.isoZero G` are
compatible with the unit of an adjunction `F ⊣ G`.
-/
/-
**CategoryTheory.Adjunction.CommShift.compatibilityUnit_isoZero** 是 Mathlib 中的一个
引理，位于命名空间 `CategoryTheory.Adjunction.CommShift`。
形式化陈述：compatibilityUnit_isoZero : CompatibilityUnit adj (Functor.CommShift.isoZe
ro F A) (Functor.CommShift.isoZero G A)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `CategoryTheory.Functor.CommShift.isoZero_hom_app`：∀ {C : Type u_1} {D : 
Type u_2} [inst : CategoryTheory.Category.{v_1, u_1} C]   [inst_1 : CategoryTheo
ry.Category.{v_2, u_2} D] (F : Categor…
· 使用定理 `CategoryTheory.Functor.map_comp`：∀ {C : Type u₁} [inst : CategoryTheory.
Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]
   (self : CategoryTh…
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.Functor.map_comp_assoc`：∀ {C : Type u₁} [inst : CategoryT
heory.Category.{v_1, u₁} C] {D : Type u₂}   [inst_1 : CategoryTheory.Category.{v
_2, u₂} D] (F : CategoryThe…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CategoryTheory.Iso.inv_hom_id_app`：∀ {C : Type u₁} [inst : CategoryTheor
y.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} 
D]   {F G : CategoryThe…
· 使用定理 `CategoryTheory.Functor.map_id`：∀ {C : Type u₁} [inst : CategoryTheory.Ca
tegory.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]  
 (self : CategoryTh…
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用定理 `CategoryTheory.Adjunction.unit_naturality_assoc`：∀ {C : Type u₁} [inst :
 CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Cate
gory.{v₂, u₂} D]   {F : CategoryTheor…
· 使用定理 `CategoryTheory.cancel_mono`：∀ {C : Type u} [inst : CategoryTheory.Catego
ry.{v, u} C] {X Y Z : C} (f : Y ⟶ X) [CategoryTheory.Mono f] {g h : Z ⟶ Y},   Ca
tegoryTheory.Cat…
· 使用定理 `CategoryTheory.StrongMono.mono`：∀ {C : Type u} {inst : CategoryTheory.Ca
tegory.{v, u} C} {P Q : C} {f : P ⟶ Q} [self : CategoryTheory.StrongMono f],   C
ategoryTheory.Mono f
· 使用定理 `CategoryTheory.strongMono_of_isIso`：∀ {C : Type u} [inst : CategoryTheor
y.Category.{v, u} C] {P Q : C} (f : Q ⟶ P) [CategoryTheory.IsIso f],   CategoryT
heory.StrongMono f
· 使用定理 `CategoryTheory.NatIso.hom_app_isIso`：∀ {C : Type u₁} [inst : CategoryThe
ory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂
} D]   {F G : CategoryThe…
· 使用定理 `CategoryTheory.NatTrans.naturality`：∀ {C : Type u₁} [inst : CategoryTheo
ry.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂}
 D]   {F G : CategoryThe…
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
The isomorphisms `Functor.CommShift.isoZero F` and `Functor.CommShift.isoZero G`
 are
compatible with the unit of an adjunction `F ⊣ G`.
-/
lemma compatibilityUnit_isoZero : CompatibilityUnit adj (Functor.CommShift.isoZero F A)
    (Functor.CommShift.isoZero G A) := by
  intro
  simp only [Functor.id_obj, Functor.comp_obj, Functor.CommShift.isoZero_hom_app,
    Functor.map_comp, assoc, unit_naturality_assoc,
    ← cancel_mono ((shiftFunctorZero C A).hom.app _), ← G.map_comp_assoc, Iso.inv_hom_id_app,
    Functor.id_obj, Functor.map_id, id_comp, NatTrans.naturality, Functor.id_map, assoc, comp_id]

set_option backward.defeqAttrib.useBackward true in
/-- Given an adjunction `adj : F ⊣ G`, `a, b` in `A` and commutation isomorphisms
between shifts by `a` (resp. `b`) and `F` and `G`, if these commutation isomorphisms are
compatible with the unit of `adj`, then so are the commutation isomorphisms between shifts
by `a + b` and `F` and `G` constructed by `Functor.CommShift.isoAdd`.
-/
/-
**CategoryTheory.Adjunction.CommShift.compatibilityUnit_isoAdd** 是 Mathlib 中的一个引
理，位于命名空间 `CategoryTheory.Adjunction.CommShift`。
形式化陈述：compatibilityUnit_isoAdd (h : CompatibilityUnit adj e₁ e₂) (h' : Compatibi
lityUnit adj f₁ f₂) : CompatibilityUnit adj (Functor.CommShift.isoAdd e₁ f₁) (Fu
nctor.CommShift.isoAdd e₂ f₂)
参数：h : CompatibilityUnit adj e₁ e₂；h' : CompatibilityUnit adj f₁ f₂。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用引理 `CategoryTheory.Functor.CommShift.isoAdd_hom_app`：isoAdd_hom_app {a b : A
} (e₁ : shiftFunctor C a ⋙ F ≅ F ⋙ shiftFunctor D a) (e₂ : shiftFunctor C b ⋙ F 
≅ F ⋙ shiftFunctor D b) (X : C) : (Co…
· 使用定理 `CategoryTheory.Functor.map_comp`：∀ {C : Type u₁} [inst : CategoryTheory.
Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]
   (self : CategoryTh…
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.Adjunction.unit_naturality_assoc`：∀ {C : Type u₁} [inst :
 CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Cate
gory.{v₂, u₂} D]   {F : CategoryTheor…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.Iso.inv_hom_id_app`：∀ {C : Type u₁} [inst : CategoryTheor
y.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} 
D]   {F G : CategoryThe…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CategoryTheory.Functor.map_id`：∀ {C : Type u₁} [inst : CategoryTheory.Ca
tegory.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]  
 (self : CategoryTh…
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用定理 `CategoryTheory.NatTrans.naturality_assoc`：∀ {C : Type u₁} [inst : Catego
ryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v
₂, u₂} D]   {F G : CategoryThe…
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `Mathlib.Tactic.Reassoc.eq_whisker'`：eq_whisker' {C : Type*} [Category* C
] {X Y : C} {f g : X ⟶ Y} (w : f = g) {Z : C} (h : Y ⟶ Z) : f ≫ h = g ≫ h
· 使用定理 `CategoryTheory.cancel_mono`：∀ {C : Type u} [inst : CategoryTheory.Catego
ry.{v, u} C] {X Y Z : C} (f : Y ⟶ X) [CategoryTheory.Mono f] {g h : Z ⟶ Y},   Ca
tegoryTheory.Cat…
· 使用定理 `CategoryTheory.StrongMono.mono`：∀ {C : Type u} {inst : CategoryTheory.Ca
tegory.{v, u} C} {P Q : C} {f : P ⟶ Q} [self : CategoryTheory.StrongMono f],   C
ategoryTheory.Mono f
· 使用定理 `CategoryTheory.strongMono_of_isIso`：∀ {C : Type u} [inst : CategoryTheor
y.Category.{v, u} C] {P Q : C} (f : Q ⟶ P) [CategoryTheory.IsIso f],   CategoryT
heory.StrongMono f
· 使用定理 `CategoryTheory.NatIso.inv_app_isIso`：∀ {C : Type u₁} [inst : CategoryThe
ory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂
} D]   {F G : CategoryThe…
· 使用定理 `CategoryTheory.Iso.hom_inv_id_app`：∀ {C : Type u₁} [inst : CategoryTheor
y.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} 
D]   {F G : CategoryThe…
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `CategoryTheory.NatIso.hom_app_isIso`：∀ {C : Type u₁} [inst : CategoryThe
ory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂
} D]   {F G : CategoryThe…
· 使用定理 `CategoryTheory.Iso.inv_hom_id_app_assoc`：∀ {C : Type u₁} [inst : Categor
yTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂
, u₂} D]   {F G : CategoryThe…
· 使用定理 `CategoryTheory.Functor.map_comp_assoc`：∀ {C : Type u₁} [inst : CategoryT
heory.Category.{v_1, u₁} C] {D : Type u₂}   [inst_1 : CategoryTheory.Category.{v
_2, u₂} D] (F : CategoryThe…
· 使用定理 `CategoryTheory.NatTrans.naturality`：∀ {C : Type u₁} [inst : CategoryTheo
ry.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂}
 D]   {F G : CategoryThe…

--- 原说明 ---
Given an adjunction `adj : F ⊣ G`, `a, b` in `A` and commutation isomorphisms
between shifts by `a` (resp. `b`) and `F` and `G`, if these commutation isomorph
isms are
compatible with the unit of `adj`, then so are the commutation isomorphisms betw
een shifts
by `a + b` and `F` and `G` constructed by `Functor.CommShift.isoAdd`.
-/
lemma compatibilityUnit_isoAdd (h : CompatibilityUnit adj e₁ e₂)
    (h' : CompatibilityUnit adj f₁ f₂) :
    CompatibilityUnit adj (Functor.CommShift.isoAdd e₁ f₁) (Functor.CommShift.isoAdd e₂ f₂) := by
  intro X
  have := h' (X⟦a⟧)
  simp only [← cancel_mono (f₂.inv.app _), assoc, Iso.hom_inv_id_app,
    Functor.id_obj, Functor.comp_obj, comp_id] at this
  simp only [Functor.id_obj, Functor.comp_obj, Functor.CommShift.isoAdd_hom_app,
    Functor.map_comp, assoc, unit_naturality_assoc]
  slice_rhs 5 6 => rw [← G.map_comp, Iso.inv_hom_id_app]
  simp only [Functor.comp_obj, Functor.map_id, id_comp, assoc]
  erw [f₂.hom.naturality_assoc]
  rw [← reassoc_of% this, ← cancel_mono ((shiftFunctorAdd C a b).hom.app _),
    assoc, assoc, assoc, assoc, assoc, assoc, Iso.inv_hom_id_app_assoc, Iso.inv_hom_id_app]
  dsimp
  rw [← (shiftFunctor C b).map_comp_assoc, ← (shiftFunctor C b).map_comp_assoc,
    assoc, ← h X, NatTrans.naturality]
  dsimp
  rw [comp_id]

end CommShift

variable (A) [F.CommShift A] [G.CommShift A]

/--
The property for `CommShift` structures on `F` and `G` to be compatible with an
adjunction `F ⊣ G`.
-/
/-
**CategoryTheory.Adjunction.CommShift** 是 Mathlib 中的一个类，位于命名空间 `CategoryTheory.A
djunction`。
形式化陈述：CommShift : Prop where commShift_unit : NatTrans.CommShift adj.unit A
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The property for `CommShift` structures on `F` and `G` to be compatible with an
adjunction `F ⊣ G`.
-/
class CommShift : Prop where
  commShift_unit : NatTrans.CommShift adj.unit A := by infer_instance
  commShift_counit : NatTrans.CommShift adj.counit A := by infer_instance

open CommShift in
attribute [instance] commShift_unit commShift_counit

set_option backward.defeqAttrib.useBackward true in
@[reassoc (attr := simp)]
/-
**CategoryTheory.Adjunction.unit_app_commShiftIso_hom_app** 是 Mathlib 中的一个引理，位于命
名空间 `CategoryTheory.Adjunction`。
形式化陈述：unit_app_commShiftIso_hom_app [adj.CommShift A] (a : A) (X : C) : adj.unit
.app (X⟦a⟧) ≫ ((F ⋙ G).commShiftIso a).hom.app X = (adj.unit.app X)⟦a⟧'
参数：a : A；X : C。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CategoryTheory.Functor.commShiftIso_id_hom_app`：∀ (C : Type u_1) [inst :
 CategoryTheory.Category.{v_1, u_1} C] {A : Type u_4} [inst_1 : AddMonoid A]   [
inst_2 : CategoryTheory.HasShift C A…
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `CategoryTheory.NatTrans.shift_app_comm`：shift_app_comm (a : A) (X : C) :
 (F₁.commShiftIso a).hom.app X ≫ (τ.app X)⟦a⟧' = τ.app (X⟦a⟧) ≫ (F₂.commShiftIso
 a).hom.app X
· 使用定理 `CategoryTheory.Adjunction.CommShift.commShift_unit`：∀ {C : Type u_1} {D 
: Type u_2} {inst : CategoryTheory.Category.{v_1, u_1} C}   {inst_1 : CategoryTh
eory.Category.{v_2, u_2} D} {F : Categor…
-/
lemma unit_app_commShiftIso_hom_app [adj.CommShift A] (a : A) (X : C) :
    adj.unit.app (X⟦a⟧) ≫ ((F ⋙ G).commShiftIso a).hom.app X = (adj.unit.app X)⟦a⟧' := by
  simpa using (NatTrans.shift_app_comm adj.unit a X).symm

set_option backward.defeqAttrib.useBackward true in
@[reassoc (attr := simp)]
/-
**CategoryTheory.Adjunction.unit_app_shift_commShiftIso_inv_app** 是 Mathlib 中的一个
引理，位于命名空间 `CategoryTheory.Adjunction`。
形式化陈述：unit_app_shift_commShiftIso_inv_app [adj.CommShift A] (a : A) (X : C) : (a
dj.unit.app X)⟦a⟧' ≫ ((F ⋙ G).commShiftIso a).inv.app X = adj.unit.app (X⟦a⟧)
参数：a : A；X : C。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.cancel_mono`：∀ {C : Type u} [inst : CategoryTheory.Catego
ry.{v, u} C] {X Y Z : C} (f : Y ⟶ X) [CategoryTheory.Mono f] {g h : Z ⟶ Y},   Ca
tegoryTheory.Cat…
· 使用定理 `CategoryTheory.StrongMono.mono`：∀ {C : Type u} {inst : CategoryTheory.Ca
tegory.{v, u} C} {P Q : C} {f : P ⟶ Q} [self : CategoryTheory.StrongMono f],   C
ategoryTheory.Mono f
· 使用定理 `CategoryTheory.strongMono_of_isIso`：∀ {C : Type u} [inst : CategoryTheor
y.Category.{v, u} C] {P Q : C} (f : Q ⟶ P) [CategoryTheory.IsIso f],   CategoryT
heory.StrongMono f
· 使用定理 `CategoryTheory.NatIso.hom_app_isIso`：∀ {C : Type u₁} [inst : CategoryThe
ory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂
} D]   {F G : CategoryThe…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.Iso.inv_hom_id_app`：∀ {C : Type u₁} [inst : CategoryTheor
y.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} 
D]   {F G : CategoryThe…
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用引理 `CategoryTheory.Adjunction.unit_app_commShiftIso_hom_app`：unit_app_commSh
iftIso_hom_app [adj.CommShift A] (a : A) (X : C) : adj.unit.app (X⟦a⟧) ≫ ((F ⋙ G
).commShiftIso a).hom.app X = (adj.unit.app X…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma unit_app_shift_commShiftIso_inv_app [adj.CommShift A] (a : A) (X : C) :
    (adj.unit.app X)⟦a⟧' ≫ ((F ⋙ G).commShiftIso a).inv.app X = adj.unit.app (X⟦a⟧) := by
  simp [← cancel_mono (((F ⋙ G).commShiftIso _).hom.app _)]

set_option backward.defeqAttrib.useBackward true in
@[reassoc (attr := simp)]
/-
**CategoryTheory.Adjunction.commShiftIso_hom_app_counit_app_shift** 是 Mathlib 中的
一个引理，位于命名空间 `CategoryTheory.Adjunction`。
形式化陈述：commShiftIso_hom_app_counit_app_shift [adj.CommShift A] (a : A) (Y : D) : 
((G ⋙ F).commShiftIso a).hom.app Y ≫ (adj.counit.app Y)⟦a⟧' = adj.counit.app (Y⟦
a⟧)
参数：a : A；Y : D。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `CategoryTheory.Functor.commShiftIso_id_hom_app`：∀ (C : Type u_1) [inst :
 CategoryTheory.Category.{v_1, u_1} C] {A : Type u_4} [inst_1 : AddMonoid A]   [
inst_2 : CategoryTheory.HasShift C A…
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用引理 `CategoryTheory.NatTrans.shift_app_comm`：shift_app_comm (a : A) (X : C) :
 (F₁.commShiftIso a).hom.app X ≫ (τ.app X)⟦a⟧' = τ.app (X⟦a⟧) ≫ (F₂.commShiftIso
 a).hom.app X
· 使用定理 `CategoryTheory.Adjunction.CommShift.commShift_counit`：∀ {C : Type u_1} {
D : Type u_2} {inst : CategoryTheory.Category.{v_1, u_1} C}   {inst_1 : Category
Theory.Category.{v_2, u_2} D} {F : Categor…
-/
lemma commShiftIso_hom_app_counit_app_shift [adj.CommShift A] (a : A) (Y : D) :
    ((G ⋙ F).commShiftIso a).hom.app Y ≫ (adj.counit.app Y)⟦a⟧' = adj.counit.app (Y⟦a⟧) := by
  simpa using (NatTrans.shift_app_comm adj.counit a Y)

@[reassoc (attr := simp)]
/-
**CategoryTheory.Adjunction.commShiftIso_inv_app_counit_app** 是 Mathlib 中的一个引理，位
于命名空间 `CategoryTheory.Adjunction`。
形式化陈述：commShiftIso_inv_app_counit_app [adj.CommShift A] (a : A) (Y : D) : ((G ⋙ 
F).commShiftIso a).inv.app Y ≫ adj.counit.app (Y⟦a⟧) = (adj.counit.app Y)⟦a⟧'
参数：a : A；Y : D。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.cancel_epi`：cancel_epi (f : X ⟶ Y) [Epi f] {g h : Y ⟶ Z} 
: f ≫ g = f ≫ h ↔ g = h
· 使用定理 `CategoryTheory.StrongEpi.epi`：∀ {C : Type u} {inst : CategoryTheory.Cate
gory.{v, u} C} {P Q : C} {f : P ⟶ Q} [self : CategoryTheory.StrongEpi f],   Cate
goryTheory.Epi f
· 使用定理 `CategoryTheory.strongEpi_of_isIso`：∀ {C : Type u} [inst : CategoryTheory
.Category.{v, u} C] {P Q : C} (f : P ⟶ Q) [CategoryTheory.IsIso f],   CategoryTh
eory.StrongEpi f
· 使用定理 `CategoryTheory.NatIso.hom_app_isIso`：∀ {C : Type u₁} [inst : CategoryThe
ory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂
} D]   {F G : CategoryThe…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Iso.hom_inv_id_app_assoc`：∀ {C : Type u₁} [inst : Categor
yTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂
, u₂} D]   {F G : CategoryThe…
· 使用引理 `CategoryTheory.Adjunction.commShiftIso_hom_app_counit_app_shift`：commShi
ftIso_hom_app_counit_app_shift [adj.CommShift A] (a : A) (Y : D) : ((G ⋙ F).comm
ShiftIso a).hom.app Y ≫ (adj.counit.app Y)⟦a⟧' = adj.…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma commShiftIso_inv_app_counit_app [adj.CommShift A] (a : A) (Y : D) :
    ((G ⋙ F).commShiftIso a).inv.app Y ≫ adj.counit.app (Y⟦a⟧) = (adj.counit.app Y)⟦a⟧' := by
  simp [← cancel_epi (((G ⋙ F).commShiftIso _).hom.app _)]

namespace CommShift


set_option backward.defeqAttrib.useBackward true in
/-- Constructor for `Adjunction.CommShift`. -/
/-
**CategoryTheory.Adjunction.CommShift.mk'** 是 Mathlib 中的一个引理，位于命名空间 `CategoryThe
ory.Adjunction.CommShift`。
形式化陈述：mk' (_ : NatTrans.CommShift adj.unit A) : adj.CommShift A where commShift_
counit
参数：_ : NatTrans.CommShift adj.unit A。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.NatTrans.ext'`：ext' {α β : F ⟶ G} (w : α.app = β.app) : α
 = β
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CategoryTheory.Functor.commShiftIso_comp_hom_app`：∀ {C : Type u_1} {D : 
Type u_2} {E : Type u_3} [inst : CategoryTheory.Category.{v_1, u_1} C]   [inst_1
 : CategoryTheory.Category.{v_2, u_2} …
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.Functor.commShiftIso_id_hom_app`：∀ (C : Type u_1) [inst :
 CategoryTheory.Category.{v_1, u_1} C] {A : Type u_4} [inst_1 : AddMonoid A]   [
inst_2 : CategoryTheory.HasShift C A…
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `CategoryTheory.Adjunction.CommShift.compatibilityCounit_of_compatibility
Unit`：compatibilityCounit_of_compatibilityUnit (h : CompatibilityUnit adj e₁ e₂)
 : CompatibilityCounit adj e₁ e₂
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用引理 `CategoryTheory.NatTrans.shift_app_comm`：shift_app_comm (a : A) (X : C) :
 (F₁.commShiftIso a).hom.app X ≫ (τ.app X)⟦a⟧' = τ.app (X⟦a⟧) ≫ (F₂.commShiftIso
 a).hom.app X

--- 原说明 ---
Constructor for `Adjunction.CommShift`.
-/
lemma mk' (_ : NatTrans.CommShift adj.unit A) :
    adj.CommShift A where
  commShift_counit := ⟨fun a ↦ by
    ext
    simp only [Functor.comp_obj, Functor.id_obj, NatTrans.comp_app,
      Functor.commShiftIso_comp_hom_app, Functor.whiskerRight_app, assoc, Functor.whiskerLeft_app,
      Functor.commShiftIso_id_hom_app, comp_id]
    refine (compatibilityCounit_of_compatibilityUnit adj _ _ (fun X ↦ ?_) _).symm
    simpa [Functor.commShiftIso_comp_hom_app] using NatTrans.shift_app_comm adj.unit a X⟩

/-- The identity adjunction is compatible with the trivial `CommShift` structure on the
identity functor.
-/
/-
**CategoryTheory.Adjunction.CommShift.instId** 是 Mathlib 中的一个实例，位于命名空间 `Category
Theory.Adjunction.CommShift`。
形式化陈述：instId : (Adjunction.id (C
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The identity adjunction is compatible with the trivial `CommShift` structure on 
the
identity functor.
-/
instance instId : (Adjunction.id (C := C)).CommShift A where
  commShift_counit :=
    inferInstanceAs (NatTrans.CommShift (𝟭 C).leftUnitor.hom A)
  commShift_unit :=
    inferInstanceAs (NatTrans.CommShift (𝟭 C).leftUnitor.inv A)

variable {E : Type*} [Category* E] {F' : D ⥤ E} {G' : E ⥤ D} (adj' : F' ⊣ G')
  [HasShift E A] [F'.CommShift A] [G'.CommShift A] [adj.CommShift A] [adj'.CommShift A]

/-- Compatibility of `Adjunction.Commshift` with the composition of adjunctions.
-/
/-
**CategoryTheory.Adjunction.CommShift.instComp** 是 Mathlib 中的一个实例，位于命名空间 `Catego
ryTheory.Adjunction.CommShift`。
形式化陈述：instComp : (adj.comp adj').CommShift A where commShift_counit
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Adjunction.comp_unit`：∀ {C : Type u₁} [inst : CategoryThe
ory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂
} D]   {E : Type u₃} [ins…
· 使用定理 `CategoryTheory.NatTrans.CommShift.comp`：∀ {C : Type u_1} {D : Type u_2} 
[inst : CategoryTheory.Category.{v_1, u_1} C]   [inst_1 : CategoryTheory.Categor
y.{v_2, u_2} D] {F₁ F₂ F₃ : …
· 使用定理 `CategoryTheory.Adjunction.CommShift.commShift_unit`：∀ {C : Type u_1} {D 
: Type u_2} {inst : CategoryTheory.Category.{v_1, u_1} C}   {inst_1 : CategoryTh
eory.Category.{v_2, u_2} D} {F : Categor…
· 使用定理 `CategoryTheory.NatTrans.CommShift.rightUnitor`：∀ {C : Type u_1} {D : Typ
e u_2} [inst : CategoryTheory.Category.{v_1, u_1} C]   [inst_1 : CategoryTheory.
Category.{v_2, u_2} D] {F₁ : Catego…
· 使用定理 `CategoryTheory.NatTrans.CommShift.whiskerLeft`：∀ {C : Type u_1} {D : Typ
e u_2} {E : Type u_3} [inst : CategoryTheory.Category.{v_1, u_1} C]   [inst_1 : 
CategoryTheory.Category.{v_2, u_2} …
· 使用定理 `CategoryTheory.NatTrans.CommShift.associator`：∀ {C : Type u_1} {D : Type
 u_2} {E : Type u_3} {J : Type u_4} [inst : CategoryTheory.Category.{v_1, u_1} C
]   [inst_1 : CategoryTheory.Categ…
· 使用定理 `CategoryTheory.Adjunction.comp_counit`：∀ {C : Type u₁} [inst : CategoryT
heory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, 
u₂} D]   {E : Type u₃} [ins…
· 使用定理 `CategoryTheory.Adjunction.CommShift.commShift_counit`：∀ {C : Type u_1} {
D : Type u_2} {inst : CategoryTheory.Category.{v_1, u_1} C}   {inst_1 : Category
Theory.Category.{v_2, u_2} D} {F : Categor…

--- 原说明 ---
Compatibility of `Adjunction.Commshift` with the composition of adjunctions.
-/
instance instComp : (adj.comp adj').CommShift A where
  commShift_counit := by
    rw [comp_counit]
    infer_instance
  commShift_unit := by
    rw [comp_unit]
    infer_instance

end CommShift

variable {A}

set_option backward.defeqAttrib.useBackward true in
@[reassoc]
/-
**CategoryTheory.Adjunction.shift_unit_app** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTh
eory.Adjunction`。
形式化陈述：shift_unit_app [adj.CommShift A] (a : A) (X : C) : (adj.unit.app X)⟦a⟧' = 
adj.unit.app (X⟦a⟧) ≫ G.map ((F.commShiftIso a).hom.app X) ≫ (G.commShiftIso a).
hom.app (F.obj X)
参数：a : A；X : C。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CategoryTheory.Functor.commShiftIso_id_hom_app`：∀ (C : Type u_1) [inst :
 CategoryTheory.Category.{v_1, u_1} C] {A : Type u_4} [inst_1 : AddMonoid A]   [
inst_2 : CategoryTheory.HasShift C A…
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用定理 `CategoryTheory.Functor.commShiftIso_comp_hom_app`：∀ {C : Type u_1} {D : 
Type u_2} {E : Type u_3} [inst : CategoryTheory.Category.{v_1, u_1} C]   [inst_1
 : CategoryTheory.Category.{v_2, u_2} …
· 使用引理 `CategoryTheory.NatTrans.shift_app_comm`：shift_app_comm (a : A) (X : C) :
 (F₁.commShiftIso a).hom.app X ≫ (τ.app X)⟦a⟧' = τ.app (X⟦a⟧) ≫ (F₂.commShiftIso
 a).hom.app X
· 使用定理 `CategoryTheory.Adjunction.CommShift.commShift_unit`：∀ {C : Type u_1} {D 
: Type u_2} {inst : CategoryTheory.Category.{v_1, u_1} C}   {inst_1 : CategoryTh
eory.Category.{v_2, u_2} D} {F : Categor…
-/
lemma shift_unit_app [adj.CommShift A] (a : A) (X : C) :
    (adj.unit.app X)⟦a⟧' =
      adj.unit.app (X⟦a⟧) ≫
        G.map ((F.commShiftIso a).hom.app X) ≫
          (G.commShiftIso a).hom.app (F.obj X) := by
  simpa [Functor.commShiftIso_comp_hom_app] using NatTrans.shift_app_comm adj.unit a X

set_option backward.defeqAttrib.useBackward true in
@[reassoc]
/-
**CategoryTheory.Adjunction.shift_counit_app** 是 Mathlib 中的一个引理，位于命名空间 `Category
Theory.Adjunction`。
形式化陈述：shift_counit_app [adj.CommShift A] (a : A) (Y : D) : (adj.counit.app Y)⟦a⟧
' = (F.commShiftIso a).inv.app (G.obj Y) ≫ F.map ((G.commShiftIso a).inv.app Y) 
≫ adj.counit.app (Y⟦a⟧)
参数：a : A；Y : D。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.NatTrans.shift_app_comm`：shift_app_comm (a : A) (X : C) :
 (F₁.commShiftIso a).hom.app X ≫ (τ.app X)⟦a⟧' = τ.app (X⟦a⟧) ≫ (F₂.commShiftIso
 a).hom.app X
· 使用定理 `CategoryTheory.Adjunction.CommShift.commShift_counit`：∀ {C : Type u_1} {
D : Type u_2} {inst : CategoryTheory.Category.{v_1, u_1} C}   {inst_1 : Category
Theory.Category.{v_2, u_2} D} {F : Categor…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CategoryTheory.Functor.commShiftIso_comp_hom_app`：∀ {C : Type u_1} {D : 
Type u_2} {E : Type u_3} [inst : CategoryTheory.Category.{v_1, u_1} C]   [inst_1
 : CategoryTheory.Category.{v_2, u_2} …
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.Functor.commShiftIso_id_hom_app`：∀ (C : Type u_1) [inst :
 CategoryTheory.Category.{v_1, u_1} C] {A : Type u_4} [inst_1 : AddMonoid A]   [
inst_2 : CategoryTheory.HasShift C A…
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `CategoryTheory.Functor.map_comp_assoc`：∀ {C : Type u₁} [inst : CategoryT
heory.Category.{v_1, u₁} C] {D : Type u₂}   [inst_1 : CategoryTheory.Category.{v
_2, u₂} D] (F : CategoryThe…
· 使用定理 `CategoryTheory.Iso.inv_hom_id_app`：∀ {C : Type u₁} [inst : CategoryTheor
y.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} 
D]   {F G : CategoryThe…
· 使用定理 `CategoryTheory.Functor.map_id`：∀ {C : Type u₁} [inst : CategoryTheory.Ca
tegory.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]  
 (self : CategoryTh…
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用定理 `CategoryTheory.Iso.inv_hom_id_app_assoc`：∀ {C : Type u₁} [inst : Categor
yTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂
, u₂} D]   {F G : CategoryThe…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma shift_counit_app [adj.CommShift A] (a : A) (Y : D) :
    (adj.counit.app Y)⟦a⟧' =
      (F.commShiftIso a).inv.app (G.obj Y) ≫ F.map ((G.commShiftIso a).inv.app Y) ≫
        adj.counit.app (Y⟦a⟧) := by
  have eq := NatTrans.shift_app_comm adj.counit a Y
  simp only [Functor.comp_obj, Functor.id_obj, Functor.commShiftIso_comp_hom_app, assoc,
    Functor.commShiftIso_id_hom_app, comp_id] at eq
  simp only [← eq, Functor.comp_obj, Functor.id_obj, ← F.map_comp_assoc, Iso.inv_hom_id_app,
    F.map_id, id_comp, Iso.inv_hom_id_app_assoc]

end Adjunction

namespace Adjunction

variable {C D : Type*} [Category* C] [Category* D]
  {F : C ⥤ D} {G : D ⥤ C} (adj : F ⊣ G) {A : Type*} [AddGroup A] [HasShift C A] [HasShift D A]

namespace RightAdjointCommShift

variable (a b : A) (h : b + a = 0) [F.CommShift A]

/-- Auxiliary definition for `iso`. -/
/-
**CategoryTheory.Adjunction.RightAdjointCommShift.iso'** 是 Mathlib 中的一个定义，位于命名空间
 `CategoryTheory.Adjunction.RightAdjointCommShift`。
形式化陈述：iso' : shiftFunctor D a ⋙ G ≅ G ⋙ shiftFunctor C a
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Auxiliary definition for `iso`.
-/
noncomputable def iso' : shiftFunctor D a ⋙ G ≅ G ⋙ shiftFunctor C a :=
  (conjugateIsoEquiv (Adjunction.comp adj (shiftEquiv' D b a h).toAdjunction)
    (Adjunction.comp (shiftEquiv' C b a h).toAdjunction adj)).toFun (F.commShiftIso b)

/--
Given an adjunction `F ⊣ G` and a `CommShift` structure on `F`, these are the candidate
`CommShift.iso a` isomorphisms for a compatible `CommShift` structure on `G`.
-/
/-
**CategoryTheory.Adjunction.RightAdjointCommShift.iso** 是 Mathlib 中的一个定义，位于命名空间 
`CategoryTheory.Adjunction.RightAdjointCommShift`。
形式化陈述：iso : shiftFunctor D a ⋙ G ≅ G ⋙ shiftFunctor C a
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `neg_add_cancel`：∀ {G : Type u_1} [inst : AddGroup G] (a : G), -a + a = 0

--- 原说明 ---
Given an adjunction `F ⊣ G` and a `CommShift` structure on `F`, these are the ca
ndidate
`CommShift.iso a` isomorphisms for a compatible `CommShift` structure on `G`.
-/
noncomputable def iso : shiftFunctor D a ⋙ G ≅ G ⋙ shiftFunctor C a :=
  iso' adj _ _ (neg_add_cancel a)

set_option backward.defeqAttrib.useBackward true in
@[reassoc]
/-
**CategoryTheory.Adjunction.RightAdjointCommShift.iso_hom_app** 是 Mathlib 中的一个引理
，位于命名空间 `CategoryTheory.Adjunction.RightAdjointCommShift`。
形式化陈述：iso_hom_app (X : D) : (iso adj a).hom.app X = (shiftFunctorCompIsoId C b a
 h).inv.app (G.obj ((shiftFunctor D a).obj X)) ≫ (adj.unit.app ((shiftFunctor C 
b).obj (G.obj ((shiftFunctor D a).obj X))))⟦a⟧' ≫ (G.map ((F.commShiftIso b).hom
.app (G.obj ((shiftFunctor D a).obj X))))⟦a⟧' ≫ (G.map ((shiftFunctor D b).map (
adj.counit.app ((shiftFunctor D a).obj X))))⟦a⟧' ≫ (G.map ((shiftFunctorCompIsoI
d D a b (by rw [← add_left_inj a, add_assoc, h, zero_add, add_zero])).hom.app X)
)⟦a⟧'
参数：X : D。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `neg_add_cancel`：∀ {G : Type u_1} [inst : AddGroup G] (a : G), -a + a = 0
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.conjugateEquiv_apply_app`：∀ {C : Type u₁} {D : Type u₂} [
inst : CategoryTheory.Category.{v₁, u₁} C] [inst_1 : CategoryTheory.Category.{v₂
, u₂} D]   {L₁ L₂ : CategoryT…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用引理 `CategoryTheory.Adjunction.comp_unit_app`：comp_unit_app (X : C) : dsimp% 
(adj₁.comp adj₂).unit.app X = adj₁.unit.app X ≫ G.map (adj₂.unit.app (F.obj X))
· 使用引理 `CategoryTheory.Adjunction.comp_counit_app`：comp_counit_app (X : E) : dsi
mp% (adj₁.comp adj₂).counit.app X = H.map (adj₁.counit.app (I.obj X)) ≫ adj₂.cou
nit.app X
· 使用定理 `CategoryTheory.Functor.map_comp`：∀ {C : Type u₁} [inst : CategoryTheory.
Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]
   (self : CategoryTh…
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `add_left_inj`：∀ {G : Type u_1} [inst : Add G] [IsRightCancelAdd G] (a : 
G) {b c : G}, b + a = c + a ↔ b = c
· 使用定理 `AddRightCancelSemigroup.toIsRightCancelAdd`：∀ {G : Type u} [self : AddRi
ghtCancelSemigroup G], IsRightCancelAdd G
-/
lemma iso_hom_app (X : D) :
    (iso adj a).hom.app X =
      (shiftFunctorCompIsoId C b a h).inv.app (G.obj ((shiftFunctor D a).obj X)) ≫
        (adj.unit.app ((shiftFunctor C b).obj (G.obj ((shiftFunctor D a).obj X))))⟦a⟧' ≫
          (G.map ((F.commShiftIso b).hom.app (G.obj ((shiftFunctor D a).obj X))))⟦a⟧' ≫
            (G.map ((shiftFunctor D b).map (adj.counit.app ((shiftFunctor D a).obj X))))⟦a⟧' ≫
              (G.map ((shiftFunctorCompIsoId D a b
                (by rw [← add_left_inj a, add_assoc, h, zero_add, add_zero])).hom.app X))⟦a⟧' := by
  obtain rfl : b = -a := by rw [← add_left_inj a, h, neg_add_cancel]
  simp [iso, iso', shiftEquiv']

set_option backward.defeqAttrib.useBackward true in
@[reassoc]
/-
**CategoryTheory.Adjunction.RightAdjointCommShift.iso_inv_app** 是 Mathlib 中的一个引理
，位于命名空间 `CategoryTheory.Adjunction.RightAdjointCommShift`。
形式化陈述：iso_inv_app (Y : D) : (iso adj a).inv.app Y = adj.unit.app ((shiftFunctor 
C a).obj (G.obj Y)) ≫ G.map ((shiftFunctorCompIsoId D b a h).inv.app (F.obj ((sh
iftFunctor C a).obj (G.obj Y)))) ≫ G.map ((shiftFunctor D a).map ((shiftFunctor 
D b).map ((F.commShiftIso a).hom.app (G.obj Y)))) ≫ G.map ((shiftFunctor D a).ma
p ((shiftFunctorCompIsoId D a b (by rw [eq_neg_of_add_eq_zero_left h, add_neg_ca
ncel])).hom.app (F.obj (G.obj Y)))) ≫ G.map ((shiftFunctor D a).map (adj.counit.
app Y))
参数：Y : D。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `neg_add_cancel`：∀ {G : Type u_1} [inst : AddGroup G] (a : G), -a + a = 0
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `CategoryTheory.conjugateEquiv_apply_app`：∀ {C : Type u₁} {D : Type u₂} [
inst : CategoryTheory.Category.{v₁, u₁} C] [inst_1 : CategoryTheory.Category.{v₂
, u₂} D]   {L₁ L₂ : CategoryT…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用引理 `CategoryTheory.Adjunction.comp_unit_app`：comp_unit_app (X : C) : dsimp% 
(adj₁.comp adj₂).unit.app X = adj₁.unit.app X ≫ G.map (adj₂.unit.app (F.obj X))
· 使用引理 `CategoryTheory.Adjunction.comp_counit_app`：comp_counit_app (X : E) : dsi
mp% (adj₁.comp adj₂).counit.app X = H.map (adj₁.counit.app (I.obj X)) ≫ adj₂.cou
nit.app X
· 使用引理 `CategoryTheory.Functor.map_shiftFunctorCompIsoId_hom_app`：map_shiftFunct
orCompIsoId_hom_app [F.CommShift A] (X : C) (a b : A) (h : a + b = 0) : F.map ((
shiftFunctorCompIsoId C a b h).hom.app X) = (F…
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.Functor.map_comp`：∀ {C : Type u₁} [inst : CategoryTheory.
Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]
   (self : CategoryTh…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.Iso.inv_hom_id_app`：∀ {C : Type u₁} [inst : CategoryTheor
y.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} 
D]   {F G : CategoryThe…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `CategoryTheory.Functor.map_id`：∀ {C : Type u₁} [inst : CategoryTheory.Ca
tegory.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]  
 (self : CategoryTh…
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `add_left_inj`：∀ {G : Type u_1} [inst : Add G] [IsRightCancelAdd G] (a : 
G) {b c : G}, b + a = c + a ↔ b = c
· 使用定理 `AddRightCancelSemigroup.toIsRightCancelAdd`：∀ {G : Type u} [self : AddRi
ghtCancelSemigroup G], IsRightCancelAdd G
-/
lemma iso_inv_app (Y : D) :
    (iso adj a).inv.app Y =
      adj.unit.app ((shiftFunctor C a).obj (G.obj Y)) ≫
          G.map ((shiftFunctorCompIsoId D b a h).inv.app
              (F.obj ((shiftFunctor C a).obj (G.obj Y)))) ≫
            G.map ((shiftFunctor D a).map ((shiftFunctor D b).map
                ((F.commShiftIso a).hom.app (G.obj Y)))) ≫
              G.map ((shiftFunctor D a).map ((shiftFunctorCompIsoId D a b
                  (by rw [eq_neg_of_add_eq_zero_left h, add_neg_cancel])).hom.app
                    (F.obj (G.obj Y)))) ≫
                G.map ((shiftFunctor D a).map (adj.counit.app Y)) := by
  obtain rfl : b = -a := by rw [← add_left_inj a, h, neg_add_cancel]
  simp only [iso, iso', shiftEquiv', Equiv.toFun_as_coe, conjugateIsoEquiv_apply_inv,
    conjugateEquiv_apply_app, Functor.comp_obj, comp_unit_app, Functor.id_obj,
    Equivalence.toAdjunction_unit, Equivalence.Equivalence_mk'_unit, Iso.symm_hom, Functor.comp_map,
    comp_counit_app, Equivalence.toAdjunction_counit, Equivalence.Equivalence_mk'_counit,
    Functor.map_shiftFunctorCompIsoId_hom_app, assoc, Functor.map_comp]
  slice_lhs 3 4 => rw [← Functor.map_comp, ← Functor.map_comp, Iso.inv_hom_id_app]
  simp only [Functor.comp_obj, Functor.map_id, id_comp, assoc]

set_option backward.defeqAttrib.useBackward true in
/--
The commutation isomorphisms of `Adjunction.RightAdjointCommShift.iso` are compatible with
the unit of the adjunction.
-/
/-
**CategoryTheory.Adjunction.RightAdjointCommShift.compatibilityUnit_iso** 是 Math
lib 中的一个引理，位于命名空间 `CategoryTheory.Adjunction.RightAdjointCommShift`。
形式化陈述：compatibilityUnit_iso (a : A) : CommShift.CompatibilityUnit adj (F.commShi
ftIso a) (iso adj a)
参数：a : A。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.cancel_mono`：∀ {C : Type u} [inst : CategoryTheory.Catego
ry.{v, u} C] {X Y Z : C} (f : Y ⟶ X) [CategoryTheory.Mono f] {g h : Z ⟶ Y},   Ca
tegoryTheory.Cat…
· 使用定理 `CategoryTheory.StrongMono.mono`：∀ {C : Type u} {inst : CategoryTheory.Ca
tegory.{v, u} C} {P Q : C} {f : P ⟶ Q} [self : CategoryTheory.StrongMono f],   C
ategoryTheory.Mono f
· 使用定理 `CategoryTheory.strongMono_of_isIso`：∀ {C : Type u} [inst : CategoryTheor
y.Category.{v, u} C] {P Q : C} (f : Q ⟶ P) [CategoryTheory.IsIso f],   CategoryT
heory.StrongMono f
· 使用定理 `CategoryTheory.NatIso.inv_app_isIso`：∀ {C : Type u₁} [inst : CategoryThe
ory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂
} D]   {F G : CategoryThe…
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.Iso.hom_inv_id_app`：∀ {C : Type u₁} [inst : CategoryTheor
y.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} 
D]   {F G : CategoryThe…
· 使用定理 `neg_add_cancel`：∀ {G : Type u_1} [inst : AddGroup G] (a : G), -a + a = 0
· 使用引理 `CategoryTheory.Adjunction.RightAdjointCommShift.iso_inv_app`：iso_inv_app
 (Y : D) : (iso adj a).inv.app Y = adj.unit.app ((shiftFunctor C a).obj (G.obj Y
)) ≫ G.map ((shiftFunctorCompIsoId D b a h).inv.a…
· 使用定理 `Equiv.injective`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β), Function.Injec
tive ⇑e
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `CategoryTheory.Adjunction.homEquiv_counit`：∀ {C : Type u₁} [inst : Categ
oryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{
v₂, u₂} D]   {F : CategoryTheor…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CategoryTheory.Functor.map_comp`：∀ {C : Type u₁} [inst : CategoryTheory.
Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]
   (self : CategoryTh…
· 使用定理 `CategoryTheory.Adjunction.counit_naturality`：∀ {C : Type u₁} [inst : Cat
egoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category
.{v₂, u₂} D]   {F : CategoryTheor…
· 使用定理 `CategoryTheory.Adjunction.counit_naturality_assoc`：∀ {C : Type u₁} [inst
 : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Ca
tegory.{v₂, u₂} D]   {F : CategoryTheor…
· 使用定理 `CategoryTheory.Adjunction.left_triangle_components_assoc`：∀ {C : Type u₁
} [inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTh
eory.Category.{v₂, u₂} D]   {F : CategoryTheor…
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `CategoryTheory.NatTrans.naturality_assoc`：∀ {C : Type u₁} [inst : Catego
ryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v
₂, u₂} D]   {F G : CategoryThe…
· 使用定理 `CategoryTheory.shift_shiftFunctorCompIsoId_hom_app`：shift_shiftFunctorCo
mpIsoId_hom_app (n m : A) (h : n + m = 0) (X : C) : ((shiftFunctorCompIsoId C n 
m h).hom.app X)⟦n⟧' = (shiftFunctorCompI…
· 使用定理 `CategoryTheory.Iso.inv_hom_id_app_assoc`：∀ {C : Type u₁} [inst : Categor
yTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂
, u₂} D]   {F G : CategoryThe…
· 使用定理 `CategoryTheory.Functor.commShiftIso_hom_naturality_assoc`：∀ {C : Type u_
1} {D : Type u_2} [inst : CategoryTheory.Category.{v_1, u_1} C]   [inst_1 : Cate
goryTheory.Category.{v_2, u_2} D] (F : Categor…
· 使用定理 `CategoryTheory.Adjunction.left_triangle_components`：∀ {C : Type u₁} [ins
t : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.C
ategory.{v₂, u₂} D]   {F : CategoryTheor…
· 使用定理 `CategoryTheory.Functor.map_id`：∀ {C : Type u₁} [inst : CategoryTheory.Ca
tegory.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]  
 (self : CategoryTh…

--- 原说明 ---
The commutation isomorphisms of `Adjunction.RightAdjointCommShift.iso` are compa
tible with
the unit of the adjunction.
-/
lemma compatibilityUnit_iso (a : A) :
    CommShift.CompatibilityUnit adj (F.commShiftIso a) (iso adj a) := by
  intro
  rw [← cancel_mono ((RightAdjointCommShift.iso adj a).inv.app _), assoc, assoc,
    Iso.hom_inv_id_app, RightAdjointCommShift.iso_inv_app adj _ _ (neg_add_cancel a)]
  apply (adj.homEquiv _ _).symm.injective
  dsimp
  simp only [comp_id, homEquiv_counit, Functor.map_comp, assoc, counit_naturality,
    counit_naturality_assoc, left_triangle_components_assoc]
  erw [← NatTrans.naturality_assoc]
  dsimp
  rw [shift_shiftFunctorCompIsoId_hom_app, Iso.inv_hom_id_app_assoc,
    Functor.commShiftIso_hom_naturality_assoc, ← Functor.map_comp,
    left_triangle_components, Functor.map_id, comp_id]

end RightAdjointCommShift

variable (A)

open RightAdjointCommShift in
/--
Given an adjunction `F ⊣ G` and a `CommShift` structure on `F`, this constructs
the unique compatible `CommShift` structure on `G`.
-/
@[simps -isSimp, instance_reducible]
/-
**CategoryTheory.Adjunction.rightAdjointCommShift** 是 Mathlib 中的一个定义，位于命名空间 `Cat
egoryTheory.Adjunction`。
形式化陈述：rightAdjointCommShift [F.CommShift A] : G.CommShift A where commShiftIso a
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given an adjunction `F ⊣ G` and a `CommShift` structure on `F`, this constructs
the unique compatible `CommShift` structure on `G`.
-/
noncomputable def rightAdjointCommShift [F.CommShift A] : G.CommShift A where
  commShiftIso a := iso adj a
  commShiftIso_zero := by
    refine CommShift.compatibilityUnit_unique_right adj (F.commShiftIso 0) _ _
      (compatibilityUnit_iso adj 0) ?_
    rw [F.commShiftIso_zero]
    exact CommShift.compatibilityUnit_isoZero adj
  commShiftIso_add a b := by
    refine CommShift.compatibilityUnit_unique_right adj (F.commShiftIso (a + b)) _ _
      (compatibilityUnit_iso adj (a + b)) ?_
    rw [F.commShiftIso_add]
    exact CommShift.compatibilityUnit_isoAdd adj _ _ _ _
      (compatibilityUnit_iso adj a) (compatibilityUnit_iso adj b)

set_option backward.defeqAttrib.useBackward true in
/-
**CategoryTheory.Adjunction.commShift_of_leftAdjoint** 是 Mathlib 中的一个引理，位于命名空间 `
CategoryTheory.Adjunction`。
形式化陈述：commShift_of_leftAdjoint [F.CommShift A] : letI
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Adjunction.CommShift.mk'`：mk' (_ : NatTrans.CommShift adj
.unit A) : adj.CommShift A where commShift_counit
· 使用定理 `CategoryTheory.NatTrans.ext'`：ext' {α β : F ⟶ G} (w : α.app = β.app) : α
 = β
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CategoryTheory.Functor.commShiftIso_id_hom_app`：∀ (C : Type u_1) [inst :
 CategoryTheory.Category.{v_1, u_1} C] {A : Type u_4} [inst_1 : AddMonoid A]   [
inst_2 : CategoryTheory.HasShift C A…
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用定理 `CategoryTheory.Functor.commShiftIso_comp_hom_app`：∀ {C : Type u_1} {D : 
Type u_2} {E : Type u_3} [inst : CategoryTheory.Category.{v_1, u_1} C]   [inst_1
 : CategoryTheory.Category.{v_2, u_2} …
· 使用引理 `CategoryTheory.Adjunction.RightAdjointCommShift.compatibilityUnit_iso`：c
ompatibilityUnit_iso (a : A) : CommShift.CompatibilityUnit adj (F.commShiftIso a
) (iso adj a)
-/
lemma commShift_of_leftAdjoint [F.CommShift A] :
    letI := adj.rightAdjointCommShift A
    adj.CommShift A := by
  let := adj.rightAdjointCommShift A
  refine CommShift.mk' _ _ ⟨fun a ↦ ?_⟩
  ext X
  dsimp
  simpa only [Functor.commShiftIso_id_hom_app, Functor.comp_obj, Functor.id_obj, id_comp,
    Functor.commShiftIso_comp_hom_app] using! RightAdjointCommShift.compatibilityUnit_iso adj a X

namespace LeftAdjointCommShift

variable {A} (a b : A) (h : a + b = 0) [G.CommShift A]

/-- Auxiliary definition for `iso`. -/
/-
**CategoryTheory.Adjunction.LeftAdjointCommShift.iso'** 是 Mathlib 中的一个定义，位于命名空间 
`CategoryTheory.Adjunction.LeftAdjointCommShift`。
形式化陈述：iso' : shiftFunctor C a ⋙ F ≅ F ⋙ shiftFunctor D a
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Auxiliary definition for `iso`.
-/
noncomputable def iso' : shiftFunctor C a ⋙ F ≅ F ⋙ shiftFunctor D a :=
  (conjugateIsoEquiv (Adjunction.comp adj (shiftEquiv' D a b h).toAdjunction)
    (Adjunction.comp (shiftEquiv' C a b h).toAdjunction adj)).invFun (G.commShiftIso b)

/--
Given an adjunction `F ⊣ G` and a `CommShift` structure on `G`, these are the candidate
`CommShift.iso a` isomorphisms for a compatible `CommShift` structure on `F`.
-/
/-
**CategoryTheory.Adjunction.LeftAdjointCommShift.iso** 是 Mathlib 中的一个定义，位于命名空间 `
CategoryTheory.Adjunction.LeftAdjointCommShift`。
形式化陈述：iso : shiftFunctor C a ⋙ F ≅ F ⋙ shiftFunctor D a
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `add_neg_cancel`：∀ {G : Type u_1} [inst : AddGroup G] (a : G), a + -a = 0

--- 原说明 ---
Given an adjunction `F ⊣ G` and a `CommShift` structure on `G`, these are the ca
ndidate
`CommShift.iso a` isomorphisms for a compatible `CommShift` structure on `F`.
-/
noncomputable def iso : shiftFunctor C a ⋙ F ≅ F ⋙ shiftFunctor D a :=
  iso' adj _ _ (add_neg_cancel a)

set_option backward.defeqAttrib.useBackward true in
@[reassoc]
/-
**CategoryTheory.Adjunction.LeftAdjointCommShift.iso_hom_app** 是 Mathlib 中的一个引理，
位于命名空间 `CategoryTheory.Adjunction.LeftAdjointCommShift`。
形式化陈述：iso_hom_app (X : C) : (iso adj a).hom.app X = F.map ((adj.unit.app X)⟦a⟧')
 ≫ F.map (G.map (((shiftFunctorCompIsoId D a b h).inv.app (F.obj X)))⟦a⟧') ≫ F.m
ap (((G.commShiftIso b).hom.app ((F.obj X)⟦a⟧))⟦a⟧') ≫ F.map ((shiftFunctorCompI
soId C b a (by simp [eq_neg_of_add_eq_zero_left h])).hom.app (G.obj ((F.obj X)⟦a
⟧))) ≫ adj.counit.app ((F.obj X)⟦a⟧)
参数：X : C。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `add_neg_cancel`：∀ {G : Type u_1} [inst : AddGroup G] (a : G), a + -a = 0
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `CategoryTheory.conjugateEquiv_symm_apply_app`：∀ {C : Type u₁} {D : Type 
u₂} [inst : CategoryTheory.Category.{v₁, u₁} C] [inst_1 : CategoryTheory.Categor
y.{v₂, u₂} D]   {L₁ L₂ : CategoryT…
· 使用引理 `CategoryTheory.Adjunction.comp_unit_app`：comp_unit_app (X : C) : dsimp% 
(adj₁.comp adj₂).unit.app X = adj₁.unit.app X ≫ G.map (adj₂.unit.app (F.obj X))
· 使用引理 `CategoryTheory.Functor.map_shiftFunctorCompIsoId_inv_app`：map_shiftFunct
orCompIsoId_inv_app [F.CommShift A] (X : C) (a b : A) (h : a + b = 0) : F.map ((
shiftFunctorCompIsoId C a b h).inv.app X) = (s…
· 使用定理 `CategoryTheory.Functor.map_comp`：∀ {C : Type u₁} [inst : CategoryTheory.
Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]
   (self : CategoryTh…
· 使用引理 `CategoryTheory.Adjunction.comp_counit_app`：comp_counit_app (X : E) : dsi
mp% (adj₁.comp adj₂).counit.app X = H.map (adj₁.counit.app (I.obj X)) ≫ adj₂.cou
nit.app X
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用引理 `Mathlib.Tactic.CategoryTheory.CancelIso.hom_inv_id_of_eq_assoc`：hom_inv_
id_of_eq_assoc {C : Type*} [Category* C] {x y : C} (f : x ⟶ y) [IsIso f] (g : y 
⟶ x) (h : inv f = g) {z : C} (k : x ⟶ z) : f ≫ g ≫ k…
· 使用定理 `CategoryTheory.NatIso.inv_app_isIso`：∀ {C : Type u₁} [inst : CategoryThe
ory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂
} D]   {F G : CategoryThe…
· 使用定理 `CategoryTheory.NatIso.isIso_app_of_isIso`：∀ {C : Type u₁} [inst : Catego
ryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v
₂, u₂} D]   {F G : CategoryThe…
· 使用定理 `CategoryTheory.Iso.isIso_inv`：∀ {C : Type u} [inst : CategoryTheory.Cate
gory.{v, u} C] {X Y : C} (e : X ≅ Y), CategoryTheory.IsIso e.inv
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `CategoryTheory.IsIso.Iso.inv_inv`：∀ {C : Type u} [inst : CategoryTheory.
Category.{v, u} C] {X Y : C} (f : X ≅ Y), CategoryTheory.inv f.inv = f.hom
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `eq_neg_of_add_eq_zero_right`：∀ {α : Type u_1} [inst : SubtractionMonoid 
α] {a b : α}, a + b = 0 → b = -a
-/
lemma iso_hom_app (X : C) :
    (iso adj a).hom.app X = F.map ((adj.unit.app X)⟦a⟧') ≫
      F.map (G.map (((shiftFunctorCompIsoId D a b h).inv.app (F.obj X)))⟦a⟧') ≫
        F.map (((G.commShiftIso b).hom.app ((F.obj X)⟦a⟧))⟦a⟧') ≫
          F.map ((shiftFunctorCompIsoId C b a (by simp [eq_neg_of_add_eq_zero_left h])).hom.app
            (G.obj ((F.obj X)⟦a⟧))) ≫ adj.counit.app ((F.obj X)⟦a⟧) := by
  obtain rfl : b = -a := eq_neg_of_add_eq_zero_right h
  simp [iso, iso', shiftEquiv']

set_option backward.defeqAttrib.useBackward true in
@[reassoc]
/-
**CategoryTheory.Adjunction.LeftAdjointCommShift.iso_inv_app** 是 Mathlib 中的一个引理，
位于命名空间 `CategoryTheory.Adjunction.LeftAdjointCommShift`。
形式化陈述：iso_inv_app (Y : C) : (iso adj a).inv.app Y = (F.map ((shiftFunctorCompIso
Id C a b h).inv.app Y))⟦a⟧' ≫ (F.map ((adj.unit.app (Y⟦a⟧))⟦b⟧'))⟦a⟧' ≫ (F.map (
(G.commShiftIso b).inv.app (F.obj (Y⟦a⟧))))⟦a⟧' ≫ (adj.counit.app ((F.obj (Y⟦a⟧)
)⟦b⟧))⟦a⟧' ≫ (shiftFunctorCompIsoId D b a (by simp [eq_neg_of_add_eq_zero_left h
])).hom.app (F.obj (Y⟦a⟧))
参数：Y : C。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `add_neg_cancel`：∀ {G : Type u_1} [inst : AddGroup G] (a : G), a + -a = 0
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `CategoryTheory.conjugateEquiv_symm_apply_app`：∀ {C : Type u₁} {D : Type 
u₂} [inst : CategoryTheory.Category.{v₁, u₁} C] [inst_1 : CategoryTheory.Categor
y.{v₂, u₂} D]   {L₁ L₂ : CategoryT…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用引理 `CategoryTheory.Adjunction.comp_unit_app`：comp_unit_app (X : C) : dsimp% 
(adj₁.comp adj₂).unit.app X = adj₁.unit.app X ≫ G.map (adj₂.unit.app (F.obj X))
· 使用定理 `CategoryTheory.Functor.map_comp`：∀ {C : Type u₁} [inst : CategoryTheory.
Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]
   (self : CategoryTh…
· 使用引理 `CategoryTheory.Adjunction.comp_counit_app`：comp_counit_app (X : E) : dsi
mp% (adj₁.comp adj₂).counit.app X = H.map (adj₁.counit.app (I.obj X)) ≫ adj₂.cou
nit.app X
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `eq_neg_of_add_eq_zero_right`：∀ {α : Type u_1} [inst : SubtractionMonoid 
α] {a b : α}, a + b = 0 → b = -a
-/
lemma iso_inv_app (Y : C) :
    (iso adj a).inv.app Y = (F.map ((shiftFunctorCompIsoId C a b h).inv.app Y))⟦a⟧' ≫
      (F.map ((adj.unit.app (Y⟦a⟧))⟦b⟧'))⟦a⟧' ≫ (F.map ((G.commShiftIso b).inv.app
        (F.obj (Y⟦a⟧))))⟦a⟧' ≫ (adj.counit.app ((F.obj (Y⟦a⟧))⟦b⟧))⟦a⟧' ≫
          (shiftFunctorCompIsoId D b a (by simp [eq_neg_of_add_eq_zero_left h])).hom.app
            (F.obj (Y⟦a⟧)) := by
  obtain rfl : b = -a := eq_neg_of_add_eq_zero_right h
  simp [iso, iso', shiftEquiv']

set_option backward.defeqAttrib.useBackward true in
/--
The commutation isomorphisms of `Adjunction.LeftAdjointCommShift.iso` are compatible with
the unit of the adjunction.
-/
/-
**CategoryTheory.Adjunction.LeftAdjointCommShift.compatibilityUnit_iso** 是 Mathl
ib 中的一个引理，位于命名空间 `CategoryTheory.Adjunction.LeftAdjointCommShift`。
形式化陈述：compatibilityUnit_iso (a : A) : CommShift.CompatibilityUnit adj (iso adj a
) (G.commShiftIso a)
参数：a : A。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `add_neg_cancel`：∀ {G : Type u_1} [inst : AddGroup G] (a : G), a + -a = 0
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `CategoryTheory.Adjunction.LeftAdjointCommShift.iso_hom_app`：iso_hom_app 
(X : C) : (iso adj a).hom.app X = F.map ((adj.unit.app X)⟦a⟧') ≫ F.map (G.map ((
(shiftFunctorCompIsoId D a b h).inv.app (F.obj X…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用引理 `CategoryTheory.Functor.map_shiftFunctorCompIsoId_inv_app`：map_shiftFunct
orCompIsoId_inv_app [F.CommShift A] (X : C) (a b : A) (h : a + b = 0) : F.map ((
shiftFunctorCompIsoId C a b h).inv.app X) = (s…
· 使用定理 `CategoryTheory.Functor.map_comp`：∀ {C : Type u₁} [inst : CategoryTheory.
Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]
   (self : CategoryTh…
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.Adjunction.unit_naturality_assoc`：∀ {C : Type u₁} [inst :
 CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Cate
gory.{v₂, u₂} D]   {F : CategoryTheor…
· 使用定理 `CategoryTheory.Adjunction.right_triangle_components_assoc`：∀ {C : Type u
₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryT
heory.Category.{v₂, u₂} D]   {F : CategoryTheor…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.Iso.inv_hom_id_app`：∀ {C : Type u₁} [inst : CategoryTheor
y.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} 
D]   {F G : CategoryThe…
· 使用定理 `CategoryTheory.Functor.map_id`：∀ {C : Type u₁} [inst : CategoryTheory.Ca
tegory.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]  
 (self : CategoryTh…
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用定理 `CategoryTheory.shift_shiftFunctorCompIsoId_inv_app`：shift_shiftFunctorCo
mpIsoId_inv_app (n m : A) (h : n + m = 0) (X : C) : ((shiftFunctorCompIsoId C n 
m h).inv.app X)⟦n⟧' = ((shiftFunctorComp…
· 使用定理 `CategoryTheory.Functor.comp_map`：comp_map (F : C ⥤ D) (G : D ⥤ E) {X Y :
 C} (f : X ⟶ Y) : (F ⋙ G).map f = G.map (F.map f)
· 使用定理 `neg_add_cancel`：∀ {G : Type u_1} [inst : AddGroup G] (a : G), -a + a = 0
· 使用定理 `CategoryTheory.NatTrans.naturality_assoc`：∀ {C : Type u₁} [inst : Catego
ryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v
₂, u₂} D]   {F G : CategoryThe…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
The commutation isomorphisms of `Adjunction.LeftAdjointCommShift.iso` are compat
ible with
the unit of the adjunction.
-/
lemma compatibilityUnit_iso (a : A) :
    CommShift.CompatibilityUnit adj (iso adj a) (G.commShiftIso a) := by
  intro
  rw [LeftAdjointCommShift.iso_hom_app adj _ _ (add_neg_cancel a)]
  simp only [Functor.id_obj, Functor.comp_obj, Functor.map_shiftFunctorCompIsoId_inv_app,
    Functor.map_comp, assoc, unit_naturality_assoc, right_triangle_components_assoc]
  slice_rhs 4 5 => rw [← Functor.map_comp, Iso.inv_hom_id_app]
  simp only [Functor.comp_obj, Functor.map_id, id_comp]
  rw [shift_shiftFunctorCompIsoId_inv_app, ← Functor.comp_map,
    (shiftFunctorCompIsoId C _ _ (neg_add_cancel a)).hom.naturality_assoc]
  simp

end LeftAdjointCommShift

open LeftAdjointCommShift in
/--
Given an adjunction `F ⊣ G` and a `CommShift` structure on `G`, this constructs
the unique compatible `CommShift` structure on `F`.
-/
@[simps -isSimp, instance_reducible]
/-
**CategoryTheory.Adjunction.leftAdjointCommShift** 是 Mathlib 中的一个定义，位于命名空间 `Cate
goryTheory.Adjunction`。
形式化陈述：leftAdjointCommShift [G.CommShift A] : F.CommShift A where commShiftIso a
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given an adjunction `F ⊣ G` and a `CommShift` structure on `G`, this constructs
the unique compatible `CommShift` structure on `F`.
-/
noncomputable def leftAdjointCommShift [G.CommShift A] : F.CommShift A where
  commShiftIso a := iso adj a
  commShiftIso_zero := by
    refine CommShift.compatibilityUnit_unique_left adj _ _ (G.commShiftIso 0)
      (compatibilityUnit_iso adj 0) ?_
    rw [G.commShiftIso_zero]
    exact CommShift.compatibilityUnit_isoZero adj
  commShiftIso_add a b := by
    refine CommShift.compatibilityUnit_unique_left adj _ _ (G.commShiftIso (a + b))
      (compatibilityUnit_iso adj (a + b)) ?_
    rw [G.commShiftIso_add]
    exact CommShift.compatibilityUnit_isoAdd adj _ _ _ _
      (compatibilityUnit_iso adj a) (compatibilityUnit_iso adj b)

set_option backward.defeqAttrib.useBackward true in
/-
**CategoryTheory.Adjunction.commShift_of_rightAdjoint** 是 Mathlib 中的一个引理，位于命名空间 
`CategoryTheory.Adjunction`。
形式化陈述：commShift_of_rightAdjoint [G.CommShift A] : letI
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Adjunction.CommShift.mk'`：mk' (_ : NatTrans.CommShift adj
.unit A) : adj.CommShift A where commShift_counit
· 使用定理 `CategoryTheory.NatTrans.ext'`：ext' {α β : F ⟶ G} (w : α.app = β.app) : α
 = β
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CategoryTheory.Functor.commShiftIso_id_hom_app`：∀ (C : Type u_1) [inst :
 CategoryTheory.Category.{v_1, u_1} C] {A : Type u_4} [inst_1 : AddMonoid A]   [
inst_2 : CategoryTheory.HasShift C A…
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用定理 `CategoryTheory.Functor.commShiftIso_comp_hom_app`：∀ {C : Type u_1} {D : 
Type u_2} {E : Type u_3} [inst : CategoryTheory.Category.{v_1, u_1} C]   [inst_1
 : CategoryTheory.Category.{v_2, u_2} …
· 使用引理 `CategoryTheory.Adjunction.LeftAdjointCommShift.compatibilityUnit_iso`：co
mpatibilityUnit_iso (a : A) : CommShift.CompatibilityUnit adj (iso adj a) (G.com
mShiftIso a)
-/
lemma commShift_of_rightAdjoint [G.CommShift A] :
    letI := adj.leftAdjointCommShift A
    adj.CommShift A := by
  let := adj.leftAdjointCommShift A
  refine CommShift.mk' _ _ ⟨fun a ↦ ?_⟩
  ext X
  dsimp
  simpa only [Functor.commShiftIso_id_hom_app, Functor.comp_obj, Functor.id_obj, id_comp,
    Functor.commShiftIso_comp_hom_app] using! LeftAdjointCommShift.compatibilityUnit_iso adj a X

end Adjunction

namespace Equivalence

variable {C D : Type*} [Category* C] [Category* D] (E : C ≌ D)

section

variable (A : Type*) [AddMonoid A] [HasShift C A] [HasShift D A]

/--
If `E : C ≌ D` is an equivalence, this expresses the compatibility of `CommShift`
structures on `E.functor` and `E.inverse`.
-/
/-
**CategoryTheory.Equivalence.CommShift** 是 Mathlib 中的一个缩写定义，位于命名空间 `CategoryTheo
ry.Equivalence`。
形式化陈述：CommShift [E.functor.CommShift A] [E.inverse.CommShift A] : Prop
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `E : C ≌ D` is an equivalence, this expresses the compatibility of `CommShift
`
structures on `E.functor` and `E.inverse`.
-/
abbrev CommShift [E.functor.CommShift A] [E.inverse.CommShift A] : Prop :=
  E.toAdjunction.CommShift A

namespace CommShift

variable [E.functor.CommShift A] [E.inverse.CommShift A]

/-
**CategoryTheory.Equivalence.CommShift.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheor
y.Equivalence.CommShift`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [E.CommShift A] : NatTrans.CommShift E.unitIso.hom A :=
  inferInstanceAs (NatTrans.CommShift E.toAdjunction.unit A)
/-
**CategoryTheory.Equivalence.CommShift.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheor
y.Equivalence.CommShift`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [E.CommShift A] : NatTrans.CommShift E.counitIso.hom A :=
  inferInstanceAs (NatTrans.CommShift E.toAdjunction.counit A)
/-
**CategoryTheory.Equivalence.CommShift.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheor
y.Equivalence.CommShift`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : E.symm.inverse.CommShift A := inferInstanceAs (E.functor.CommShift A)
/-
**CategoryTheory.Equivalence.CommShift.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheor
y.Equivalence.CommShift`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : E.symm.functor.CommShift A := inferInstanceAs (E.inverse.CommShift A)

/-- Constructor for `Equivalence.CommShift`. -/
/-
**CategoryTheory.Equivalence.CommShift.mk'** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTh
eory.Equivalence.CommShift`。
形式化陈述：mk' (h : NatTrans.CommShift E.unitIso.hom A) : E.CommShift A where commShi
ft_unit
参数：h : NatTrans.CommShift E.unitIso.hom A。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Adjunction.CommShift.commShift_counit`：∀ {C : Type u_1} {
D : Type u_2} {inst : CategoryTheory.Category.{v_1, u_1} C}   {inst_1 : Category
Theory.Category.{v_2, u_2} D} {F : Categor…
· 使用引理 `CategoryTheory.Adjunction.CommShift.mk'`：mk' (_ : NatTrans.CommShift adj
.unit A) : adj.CommShift A where commShift_counit

--- 原说明 ---
Constructor for `Equivalence.CommShift`.
-/
lemma mk' (h : NatTrans.CommShift E.unitIso.hom A) :
    E.CommShift A where
  commShift_unit := h
  commShift_counit := (Adjunction.CommShift.mk' E.toAdjunction A h).commShift_counit

/--
The forward functor of the identity equivalence is compatible with shifts.
-/
/-
**CategoryTheory.Equivalence.CommShift.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheor
y.Equivalence.CommShift`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The forward functor of the identity equivalence is compatible with shifts.
-/
instance : (Equivalence.refl (C := C)).functor.CommShift A :=
  inferInstanceAs <| (𝟭 C).CommShift A

/--
The inverse functor of the identity equivalence is compatible with shifts.
-/
/-
**CategoryTheory.Equivalence.CommShift.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheor
y.Equivalence.CommShift`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The inverse functor of the identity equivalence is compatible with shifts.
-/
instance : (Equivalence.refl (C := C)).inverse.CommShift A :=
  inferInstanceAs <| (𝟭 C).CommShift A


/--
The identity equivalence is compatible with shifts.
-/
/-
**CategoryTheory.Equivalence.CommShift.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheor
y.Equivalence.CommShift`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The identity equivalence is compatible with shifts.
-/
instance : (Equivalence.refl (C := C)).CommShift A :=
  inferInstanceAs <| Adjunction.id.CommShift A

/--
If an equivalence `E : C ≌ D` is compatible with shifts, so is `E.symm`.
-/
/-
**CategoryTheory.Equivalence.CommShift.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheor
y.Equivalence.CommShift`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If an equivalence `E : C ≌ D` is compatible with shifts, so is `E.symm`.
-/
instance [E.CommShift A] : E.symm.CommShift A :=
  mk' E.symm A (inferInstanceAs (NatTrans.CommShift E.counitIso.inv A))

/-- Constructor for `Equivalence.CommShift`. -/
/-
**CategoryTheory.Equivalence.CommShift.mk''** 是 Mathlib 中的一个引理，位于命名空间 `CategoryT
heory.Equivalence.CommShift`。
形式化陈述：mk'' (h : NatTrans.CommShift E.counitIso.hom A) : E.CommShift A
参数：h : NatTrans.CommShift E.counitIso.hom A。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Equivalence.CommShift.mk'`：mk' (h : NatTrans.CommShift E.
unitIso.hom A) : E.CommShift A where commShift_unit

--- 原说明 ---
Constructor for `Equivalence.CommShift`.
-/
lemma mk'' (h : NatTrans.CommShift E.counitIso.hom A) :
    E.CommShift A :=
  have := mk' E.symm A (inferInstanceAs (NatTrans.CommShift E.counitIso.inv A))
  inferInstanceAs (E.symm.symm.CommShift A)

variable {F : Type*} [Category* F] [HasShift F A] {E' : D ≌ F} [E.CommShift A]
    [E'.functor.CommShift A] [E'.inverse.CommShift A] [E'.CommShift A]

set_option backward.defeqAttrib.useBackward true in
/--
If `E : C ≌ D` and `E' : D ≌ F` are equivalences whose forward functors are compatible with shifts,
so is `(E.trans E').functor`.
-/
/-
**CategoryTheory.Equivalence.CommShift.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheor
y.Equivalence.CommShift`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `E : C ≌ D` and `E' : D ≌ F` are equivalences whose forward functors are comp
atible with shifts,
so is `(E.trans E').functor`.
-/
instance : (E.trans E').functor.CommShift A := by
  dsimp
  infer_instance

set_option backward.defeqAttrib.useBackward true in
/--
If `E : C ≌ D` and `E' : D ≌ F` are equivalences whose inverse functors are compatible with shifts,
so is `(E.trans E').inverse`.
-/
/-
**CategoryTheory.Equivalence.CommShift.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheor
y.Equivalence.CommShift`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `E : C ≌ D` and `E' : D ≌ F` are equivalences whose inverse functors are comp
atible with shifts,
so is `(E.trans E').inverse`.
-/
instance : (E.trans E').inverse.CommShift A := by
  dsimp
  infer_instance

/--
If equivalences `E : C ≌ D` and `E' : D ≌ F` are compatible with shifts, so is `E.trans E'`.
-/
/-
**CategoryTheory.Equivalence.CommShift.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheor
y.Equivalence.CommShift`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If equivalences `E : C ≌ D` and `E' : D ≌ F` are compatible with shifts, so is `
E.trans E'`.
-/
instance : (E.trans E').CommShift A :=
  inferInstanceAs ((E.toAdjunction.comp E'.toAdjunction).CommShift A)

end CommShift

end

variable (A : Type*) [AddGroup A] [HasShift C A] [HasShift D A]

/--
If `E : C ≌ D` is an equivalence and we have a `CommShift` structure on `E.functor`,
this constructs the unique compatible `CommShift` structure on `E.inverse`.
-/
@[instance_reducible]
/-
**CategoryTheory.Equivalence.commShiftInverse** 是 Mathlib 中的一个定义，位于命名空间 `Categor
yTheory.Equivalence`。
形式化陈述：commShiftInverse [E.functor.CommShift A] : E.inverse.CommShift A
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `E : C ≌ D` is an equivalence and we have a `CommShift` structure on `E.funct
or`,
this constructs the unique compatible `CommShift` structure on `E.inverse`.
-/
noncomputable def commShiftInverse [E.functor.CommShift A] : E.inverse.CommShift A :=
  E.toAdjunction.rightAdjointCommShift A
/-
**CategoryTheory.Equivalence.commShift_of_functor** 是 Mathlib 中的一个引理，位于命名空间 `Cat
egoryTheory.Equivalence`。
形式化陈述：commShift_of_functor [E.functor.CommShift A] : letI
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Equivalence.CommShift.mk'`：mk' (h : NatTrans.CommShift E.
unitIso.hom A) : E.CommShift A where commShift_unit
· 使用定理 `CategoryTheory.Adjunction.CommShift.commShift_unit`：∀ {C : Type u_1} {D 
: Type u_2} {inst : CategoryTheory.Category.{v_1, u_1} C}   {inst_1 : CategoryTh
eory.Category.{v_2, u_2} D} {F : Categor…
· 使用引理 `CategoryTheory.Adjunction.commShift_of_leftAdjoint`：commShift_of_leftAdj
oint [F.CommShift A] : letI
-/
lemma commShift_of_functor [E.functor.CommShift A] :
    letI := E.commShiftInverse A
    E.CommShift A := by
  let := E.commShiftInverse A
  exact CommShift.mk' _ _ (E.toAdjunction.commShift_of_leftAdjoint A).commShift_unit

/--
If `E : C ≌ D` is an equivalence and we have a `CommShift` structure on `E.inverse`,
this constructs the unique compatible `CommShift` structure on `E.functor`.
-/
@[instance_reducible]
/-
**CategoryTheory.Equivalence.commShiftFunctor** 是 Mathlib 中的一个定义，位于命名空间 `Categor
yTheory.Equivalence`。
形式化陈述：commShiftFunctor [E.inverse.CommShift A] : E.functor.CommShift A
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `E : C ≌ D` is an equivalence and we have a `CommShift` structure on `E.inver
se`,
this constructs the unique compatible `CommShift` structure on `E.functor`.
-/
noncomputable def commShiftFunctor [E.inverse.CommShift A] : E.functor.CommShift A :=
  E.symm.toAdjunction.rightAdjointCommShift A

set_option backward.isDefEq.respectTransparency false in
/-
**CategoryTheory.Equivalence.commShift_of_inverse** 是 Mathlib 中的一个引理，位于命名空间 `Cat
egoryTheory.Equivalence`。
形式化陈述：commShift_of_inverse [E.inverse.CommShift A] : letI
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Equivalence.commShift_of_functor`：commShift_of_functor [E
.functor.CommShift A] : letI
-/
lemma commShift_of_inverse [E.inverse.CommShift A] :
    letI := E.commShiftFunctor A
    E.CommShift A := by
  let := E.commShiftFunctor A
  have := E.symm.commShift_of_functor A
  exact inferInstanceAs (E.symm.symm.CommShift A)

end Equivalence

end CategoryTheory

