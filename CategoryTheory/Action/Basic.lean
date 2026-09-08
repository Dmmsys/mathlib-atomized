/-
Copyright (c) 2020 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import Mathlib.Algebra.Category.Grp.Basic
public import Mathlib.Algebra.Ring.PUnit
public import Mathlib.CategoryTheory.Adjunction.Limits
public import Mathlib.CategoryTheory.Conj
public import Mathlib.CategoryTheory.Limits.FunctorCategory.Basic
public import Mathlib.CategoryTheory.Limits.Preserves.Basic
public import Mathlib.CategoryTheory.SingleObj
public import Mathlib.Tactic.ApplyFun

/-!
# `Action V G`, the category of actions of a monoid `G` inside some category `V`.

The prototypical example is `V = ModuleCat R`,
where `Action (ModuleCat R) G` is the category of `R`-linear representations of `G`.

We check `Action V G ≌ (CategoryTheory.SingleObj G ⥤ V)`,
and construct the restriction functors
`res {G H} [Monoid G] [Monoid H] (f : G →* H) : Action V H ⥤ Action V G`.
-/

@[expose] public section


universe u v

open CategoryTheory Limits

variable (V : Type*) [Category* V]

-- Note: this is _not_ a categorical action of `G` on `V`.
/-- An `Action V G` represents a bundled action of
the monoid `G` on an object of some category `V`.

As an example, when `V = ModuleCat R`, this is an `R`-linear representation of `G`,
while when `V = Type` this is a `G`-action.
-/
/-
**Action** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：(V : Type u_1) → [CategoryTheory.Category.{v_1, u_1} V] → (G : Type u_2) →
 [Monoid G] → Type (max (max u_1 u_2) v_1)
参数：max u_1 u_2。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An `Action V G` represents a bundled action of
the monoid `G` on an object of some category `V`.

As an example, when `V = ModuleCat R`, this is an `R`-linear representation of `
G`,
while when `V = Type` this is a `G`-action.
-/
structure Action (G : Type*) [Monoid G] where
  /-- The object this action acts on -/
  V : V
  /-- The underlying monoid homomorphism of this action -/
  ρ : G →* End V

namespace Action

variable {V}

set_option backward.isDefEq.respectTransparency.types false in
/-
**Action.** 是 Mathlib 中的一个定理，位于命名空间 `Action`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem ρ_one {G : Type*} [Monoid G] (A : Action V G) : A.ρ 1 = 𝟙 A.V := by simp

/-- When a group acts, we can lift the action to the group of automorphisms. -/
@[simps]
/-
**Action.** 是 Mathlib 中的一个定义，位于命名空间 `Action`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
When a group acts, we can lift the action to the group of automorphisms.
-/
def ρAut {G : Type*} [Group G] (A : Action V G) : G →* Aut A.V where
  toFun g :=
    { hom := A.ρ g
      inv := A.ρ (g⁻¹ : G)
      hom_inv_id := (A.ρ.map_mul (g⁻¹ : G) g).symm.trans (by rw [inv_mul_cancel, ρ_one])
      inv_hom_id := (A.ρ.map_mul g (g⁻¹ : G)).symm.trans (by rw [mul_inv_cancel, ρ_one]) }
  map_one' := Aut.ext A.ρ.map_one
  map_mul' x y := Aut.ext (A.ρ.map_mul x y)

variable (G : Type*) [Monoid G]

section

/-- The action defined by sending every monoid element to the identity. -/
@[simps]
/-
**Action.trivial** 是 Mathlib 中的一个定义，位于命名空间 `Action`。
形式化陈述：trivial (X : V) : Action V G
参数：X : V。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The action defined by sending every monoid element to the identity.
-/
def trivial (X : V) : Action V G := { V := X, ρ := 1 }
/-
**Action.inhabited'** 是 Mathlib 中的一个实例，位于命名空间 `Action`。
形式化陈述：inhabited' : Inhabited (Action Type* G)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance inhabited' : Inhabited (Action Type* G) :=
  ⟨⟨PUnit, 1⟩⟩
/-
**Action.** 是 Mathlib 中的一个实例，位于命名空间 `Action`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Inhabited (Action AddCommGrpCat G) :=
  ⟨trivial G <| AddCommGrpCat.of PUnit⟩

end

variable {G}

/-- A homomorphism of `Action V G`s is a morphism between the underlying objects,
commuting with the action of `G`.
-/
@[ext]
/-
**Action.Hom** 是 Mathlib 中的一个结构，位于命名空间 `Action`。
形式化陈述：Hom (M N : Action V G) where /-- The morphism between the underlying objec
ts of this action -/ hom : M.V ⟶ N.V comm : forall g : G, M.ρ g ≫ hom = hom ≫ N.
ρ g
参数：M N : Action V G。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A homomorphism of `Action V G`s is a morphism between the underlying objects,
commuting with the action of `G`.
-/
structure Hom (M N : Action V G) where
  /-- The morphism between the underlying objects of this action -/
  hom : M.V ⟶ N.V
  comm : ∀ g : G, M.ρ g ≫ hom = hom ≫ N.ρ g := by cat_disch

namespace Hom

attribute [reassoc] comm
attribute [local simp] comm comm_assoc

set_option backward.isDefEq.respectTransparency.types false in
/-- The identity morphism on an `Action V G`. -/
@[simps]
/-
**Action.Hom.id** 是 Mathlib 中的一个定义，位于命名空间 `Action.Hom`。
形式化陈述：id (M : Action V G) : Action.Hom M M where hom
参数：M : Action V G。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The identity morphism on an `Action V G`.
-/
def id (M : Action V G) : Action.Hom M M where hom := 𝟙 M.V
/-
**Action.Hom.** 是 Mathlib 中的一个实例，位于命名空间 `Action.Hom`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (M : Action V G) : Inhabited (Action.Hom M M) :=
  ⟨id M⟩

set_option backward.isDefEq.respectTransparency.types false in
/-- The composition of two `Action V G` homomorphisms is the composition of the underlying maps.
-/
@[simps]
/-
**Action.Hom.comp** 是 Mathlib 中的一个定义，位于命名空间 `Action.Hom`。
形式化陈述：comp {M N K : Action V G} (p : Action.Hom M N) (q : Action.Hom N K) : Acti
on.Hom M K where hom
参数：p : Action.Hom M N；q : Action.Hom N K。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The composition of two `Action V G` homomorphisms is the composition of the unde
rlying maps.
-/
def comp {M N K : Action V G} (p : Action.Hom M N) (q : Action.Hom N K) : Action.Hom M K where
  hom := p.hom ≫ q.hom
  comm := by
    intro g
    simp_all only [comm_assoc, comm, Category.assoc]

end Hom

/-
**Action.** 是 Mathlib 中的一个实例，位于命名空间 `Action`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Category (Action V G) where
  Hom M N := Hom M N
  id M := Hom.id M
  comp f g := Hom.comp f g
/-
**Action.hom_injective** 是 Mathlib 中的一个引理，位于命名空间 `Action`。
形式化陈述：hom_injective {M N : Action V G} : Function.Injective (Hom.hom : (M ⟶ N) -
> (M.V ⟶ N.V))
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Action.Hom.ext`：∀ {V : Type u_1} {inst : CategoryTheory.Category.{v_1, u
_1} V} {G : Type u_2} {inst_1 : Monoid G} {M N : Action V G}   {x y : M.Hom N}, 
x.ho…
-/
lemma hom_injective {M N : Action V G} : Function.Injective (Hom.hom : (M ⟶ N) → (M.V ⟶ N.V)) :=
  fun _ _ ↦ Hom.ext

@[ext]
/-
**Action.hom_ext** 是 Mathlib 中的一个引理，位于命名空间 `Action`。
形式化陈述：hom_ext {M N : Action V G} (φ₁ φ₂ : M ⟶ N) (h : φ₁.hom = φ₂.hom) : φ₁ = φ₂
参数：φ₁ φ₂ : M ⟶ N；h : φ₁.hom = φ₂.hom。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Action.Hom.ext`：∀ {V : Type u_1} {inst : CategoryTheory.Category.{v_1, u
_1} V} {G : Type u_2} {inst_1 : Monoid G} {M N : Action V G}   {x y : M.Hom N}, 
x.ho…
-/
lemma hom_ext {M N : Action V G} (φ₁ φ₂ : M ⟶ N) (h : φ₁.hom = φ₂.hom) : φ₁ = φ₂ :=
  Hom.ext h

set_option backward.isDefEq.respectTransparency.types false in
@[simp]
/-
**Action.id_hom** 是 Mathlib 中的一个定理，位于命名空间 `Action`。
形式化陈述：id_hom (M : Action V G) : (𝟙 M : Hom M M).hom = 𝟙 M.V
参数：M : Action V G。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem id_hom (M : Action V G) : (𝟙 M : Hom M M).hom = 𝟙 M.V :=
  rfl

set_option backward.isDefEq.respectTransparency.types false in
@[simp, reassoc]
/-
**Action.comp_hom** 是 Mathlib 中的一个定理，位于命名空间 `Action`。
形式化陈述：comp_hom {M N K : Action V G} (f : M ⟶ N) (g : N ⟶ K) : (f ≫ g : Hom M K).
hom = f.hom ≫ g.hom
参数：f : M ⟶ N；g : N ⟶ K。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem comp_hom {M N K : Action V G} (f : M ⟶ N) (g : N ⟶ K) :
    (f ≫ g : Hom M K).hom = f.hom ≫ g.hom :=
  rfl

@[reassoc (attr := simp)]
/-
**Action.hom_inv_hom** 是 Mathlib 中的一个定理，位于命名空间 `Action`。
形式化陈述：hom_inv_hom {M N : Action V G} (f : M ≅ N) : f.hom.hom ≫ f.inv.hom = 𝟙 M.V
参数：f : M ≅ N。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Action.comp_hom`：comp_hom {M N K : Action V G} (f : M ⟶ N) (g : N ⟶ K) :
 (f ≫ g : Hom M K).hom = f.hom ≫ g.hom
· 使用定理 `CategoryTheory.Iso.hom_inv_id`：∀ {C : Type u} [inst : CategoryTheory.Cat
egory.{v, u} C] {X Y : C} (self : X ≅ Y),   CategoryTheory.CategoryStruct.comp s
elf.hom self.inv = …
· 使用定理 `Action.id_hom`：id_hom (M : Action V G) : (𝟙 M : Hom M M).hom = 𝟙 M.V
-/
theorem hom_inv_hom {M N : Action V G} (f : M ≅ N) :
    f.hom.hom ≫ f.inv.hom = 𝟙 M.V := by
  rw [← comp_hom, Iso.hom_inv_id, id_hom]

@[reassoc (attr := simp)]
/-
**Action.inv_hom_hom** 是 Mathlib 中的一个定理，位于命名空间 `Action`。
形式化陈述：inv_hom_hom {M N : Action V G} (f : M ≅ N) : f.inv.hom ≫ f.hom.hom = 𝟙 N.V
参数：f : M ≅ N。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Action.comp_hom`：comp_hom {M N K : Action V G} (f : M ⟶ N) (g : N ⟶ K) :
 (f ≫ g : Hom M K).hom = f.hom ≫ g.hom
· 使用定理 `CategoryTheory.Iso.inv_hom_id`：∀ {C : Type u} [inst : CategoryTheory.Cat
egory.{v, u} C] {X Y : C} (self : X ≅ Y),   CategoryTheory.CategoryStruct.comp s
elf.inv self.hom = …
· 使用定理 `Action.id_hom`：id_hom (M : Action V G) : (𝟙 M : Hom M M).hom = 𝟙 M.V
-/
theorem inv_hom_hom {M N : Action V G} (f : M ≅ N) :
    f.inv.hom ≫ f.hom.hom = 𝟙 N.V := by
  rw [← comp_hom, Iso.inv_hom_id, id_hom]

set_option backward.isDefEq.respectTransparency.types false in
/-- Construct an isomorphism of `G` actions/representations
from an isomorphism of the underlying objects,
where the forward direction commutes with the group action. -/
@[simps]
/-
**Action.mkIso** 是 Mathlib 中的一个定义，位于命名空间 `Action`。
形式化陈述：mkIso {M N : Action V G} (f : M.V ≅ N.V) (comm : forall g : G, M.ρ g ≫ f.h
om = f.hom ≫ N.ρ g
参数：f : M.V ≅ N.V。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Construct an isomorphism of `G` actions/representations
from an isomorphism of the underlying objects,
where the forward direction commutes with the group action.
-/
def mkIso {M N : Action V G} (f : M.V ≅ N.V)
    (comm : ∀ g : G, M.ρ g ≫ f.hom = f.hom ≫ N.ρ g := by cat_disch) : M ≅ N where
  hom :=
    { hom := f.hom
      comm := comm }
  inv :=
    { hom := f.inv
      comm := fun g => by have w := comm g =≫ f.inv; simp at w; simp [w] }

set_option backward.isDefEq.respectTransparency.types false in
/-
**Action.** 是 Mathlib 中的一个实例，位于命名空间 `Action`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 100) isIso_of_hom_isIso {M N : Action V G} (f : M ⟶ N) [IsIso f.hom] :
    IsIso f := (mkIso (asIso f.hom) f.comm).isIso_hom

set_option backward.isDefEq.respectTransparency.types false in
/-
**Action.isIso_hom_mk** 是 Mathlib 中的一个实例，位于命名空间 `Action`。
形式化陈述：isIso_hom_mk {M N : Action V G} (f : M.V ⟶ N.V) [IsIso f] (w) : @IsIso _ _
 M N (Hom.mk f w)
参数：f : M.V ⟶ N.V；w。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Iso.isIso_hom`：∀ {C : Type u} [inst : CategoryTheory.Cate
gory.{v, u} C] {X Y : C} (e : X ≅ Y), CategoryTheory.IsIso e.hom
-/
instance isIso_hom_mk {M N : Action V G} (f : M.V ⟶ N.V) [IsIso f] (w) :
    @IsIso _ _ M N (Hom.mk f w) :=
  (mkIso (asIso f) w).isIso_hom
/-
**Action.** 是 Mathlib 中的一个实例，位于命名空间 `Action`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {M N : Action V G} (f : M ≅ N) : IsIso f.hom.hom where
  out := ⟨f.inv.hom, by simp⟩
/-
**Action.** 是 Mathlib 中的一个实例，位于命名空间 `Action`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {M N : Action V G} (f : M ≅ N) : IsIso f.inv.hom where
  out := ⟨f.hom.hom, by simp⟩

namespace FunctorCategoryEquivalence

set_option backward.isDefEq.respectTransparency.types false in
/-- Auxiliary definition for `functorCategoryEquivalence`. -/
@[simps]
/-
**Action.FunctorCategoryEquivalence.functor** 是 Mathlib 中的一个定义，位于命名空间 `Action.Fu
nctorCategoryEquivalence`。
形式化陈述：functor : Action V G ⥤ SingleObj G ⥤ V where obj M
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Action.Hom.comm`：∀ {V : Type u_1} [inst : CategoryTheory.Category.{v_1, 
u_1} V] {G : Type u_2} [inst_1 : Monoid G] {M N : Action V G}   (self : M.Hom N)
 (g :…

--- 原说明 ---
Auxiliary definition for `functorCategoryEquivalence`.
-/
def functor : Action V G ⥤ SingleObj G ⥤ V where
  obj M :=
    { obj := fun _ => M.V
      map := fun g => M.ρ g
      map_id := fun _ => M.ρ.map_one
      map_comp := fun g h => M.ρ.map_mul h g }
  map f :=
    { app := fun _ => f.hom
      naturality := fun _ _ g => f.comm g }

set_option backward.isDefEq.respectTransparency.types false in
/-- Auxiliary definition for `functorCategoryEquivalence`. -/
@[simps]
/-
**Action.FunctorCategoryEquivalence.inverse** 是 Mathlib 中的一个定义，位于命名空间 `Action.Fu
nctorCategoryEquivalence`。
形式化陈述：inverse : (SingleObj G ⥤ V) ⥤ Action V G where obj F
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Auxiliary definition for `functorCategoryEquivalence`.
-/
def inverse : (SingleObj G ⥤ V) ⥤ Action V G where
  obj F :=
    { V := F.obj PUnit.unit
      ρ :=
        { toFun := fun g => F.map g
          map_one' := F.map_id PUnit.unit
          map_mul' := fun g h => F.map_comp h g } }
  map f :=
    { hom := f.app PUnit.unit
      comm := fun g => f.naturality g }

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- Auxiliary definition for `functorCategoryEquivalence`. -/
@[simps!]
/-
**Action.FunctorCategoryEquivalence.unitIso** 是 Mathlib 中的一个定义，位于命名空间 `Action.Fu
nctorCategoryEquivalence`。
形式化陈述：unitIso : 𝟭 (Action V G) ≅ functor ⋙ inverse
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Auxiliary definition for `functorCategoryEquivalence`.
-/
def unitIso : 𝟭 (Action V G) ≅ functor ⋙ inverse :=
  NatIso.ofComponents fun M => mkIso (Iso.refl _)

set_option backward.isDefEq.respectTransparency false in
/-- Auxiliary definition for `functorCategoryEquivalence`. -/
@[simps!]
/-
**Action.FunctorCategoryEquivalence.counitIso** 是 Mathlib 中的一个定义，位于命名空间 `Action.
FunctorCategoryEquivalence`。
形式化陈述：counitIso : inverse ⋙ functor ≅ 𝟭 (SingleObj G ⥤ V)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Auxiliary definition for `functorCategoryEquivalence`.
-/
def counitIso : inverse ⋙ functor ≅ 𝟭 (SingleObj G ⥤ V) :=
  NatIso.ofComponents fun M => NatIso.ofComponents fun _ => Iso.refl _

end FunctorCategoryEquivalence

section

open FunctorCategoryEquivalence

variable (V G)

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- The category of actions of `G` in the category `V`
is equivalent to the functor category `SingleObj G ⥤ V`.
-/
@[simps]
/-
**Action.functorCategoryEquivalence** 是 Mathlib 中的一个定义，位于命名空间 `Action`。
形式化陈述：functorCategoryEquivalence : Action V G ≌ SingleObj G ⥤ V where functor
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The category of actions of `G` in the category `V`
is equivalent to the functor category `SingleObj G ⥤ V`.
-/
def functorCategoryEquivalence : Action V G ≌ SingleObj G ⥤ V where
  functor := functor
  inverse := inverse
  unitIso := unitIso
  counitIso := counitIso

set_option backward.isDefEq.respectTransparency.types false in
/-
**Action.** 是 Mathlib 中的一个实例，位于命名空间 `Action`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : (FunctorCategoryEquivalence.functor (V := V) (G := G)).IsEquivalence :=
  (functorCategoryEquivalence V G).isEquivalence_functor

set_option backward.isDefEq.respectTransparency.types false in
/-
**Action.** 是 Mathlib 中的一个实例，位于命名空间 `Action`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : (FunctorCategoryEquivalence.inverse (V := V) (G := G)).IsEquivalence :=
  (functorCategoryEquivalence V G).isEquivalence_inverse

end

section Forget

variable (V G)

set_option backward.isDefEq.respectTransparency.types false in
/-- (implementation) The forgetful functor from bundled actions to the underlying objects.

Use the `CategoryTheory.forget` API provided by the `ConcreteCategory` instance below,
rather than using this directly.
-/
@[simps]
/-
**Action.forget** 是 Mathlib 中的一个定义，位于命名空间 `Action`。
形式化陈述：forget : Action V G ⥤ V where obj M
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
(implementation) The forgetful functor from bundled actions to the underlying ob
jects.

Use the `CategoryTheory.forget` API provided by the `ConcreteCategory` instance 
below,
rather than using this directly.
-/
def forget : Action V G ⥤ V where
  obj M := M.V
  map f := f.hom
/-
**Action.** 是 Mathlib 中的一个实例，位于命名空间 `Action`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : (forget V G).Faithful where map_injective w := Hom.ext w

/-- The type of `V`-morphisms that can be lifted back to morphisms in the category `Action`. -/
/-
**Action.HomSubtype** 是 Mathlib 中的一个缩写定义，位于命名空间 `Action`。
形式化陈述：HomSubtype {FV : V -> V -> Type*} {CV : V -> Type*} [forall X Y, FunLike (
FV X Y) (CV X) (CV Y)] [ConcreteCategory V FV] (M N : Action V G)
参数：FV X Y；CV X；CV Y；M N : Action V G。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The type of `V`-morphisms that can be lifted back to morphisms in the category `
Action`.
-/
abbrev HomSubtype {FV : V → V → Type*} {CV : V → Type*} [∀ X Y, FunLike (FV X Y) (CV X) (CV Y)]
    [ConcreteCategory V FV] (M N : Action V G) :=
  { f : FV M.V N.V // ∀ g : G,
      f ∘ ConcreteCategory.hom (M.ρ g) = ConcreteCategory.hom (N.ρ g) ∘ f }
/-
**Action.** 是 Mathlib 中的一个实例，位于命名空间 `Action`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {FV : V → V → Type*} {CV : V → Type*} [∀ X Y, FunLike (FV X Y) (CV X) (CV Y)]
    [ConcreteCategory V FV] (M N : Action V G) :
    FunLike (HomSubtype V G M N) (CV M.V) (CV N.V) where
  coe f := f.1
  coe_injective _ _ h := Subtype.ext (DFunLike.coe_injective h)

set_option backward.isDefEq.respectTransparency.types false in
/-
**Action.** 是 Mathlib 中的一个实例，位于命名空间 `Action`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {FV : V → V → Type*} {CV : V → Type*} [∀ X Y, FunLike (FV X Y) (CV X) (CV Y)]
    [ConcreteCategory V FV] : ConcreteCategory (Action V G) (HomSubtype V G) where
  hom f := ⟨ConcreteCategory.hom (C := V) f.1, fun g => by
    ext
    simpa using CategoryTheory.congr_fun (f.2 g) _⟩
  ofHom f := ⟨ConcreteCategory.ofHom (C := V) f, fun g => ConcreteCategory.ext_apply fun x => by
    simpa [ConcreteCategory.hom_ofHom] using congr_fun (f.2 g) x⟩
  hom_ofHom _ := by dsimp; ext; simp [ConcreteCategory.hom_ofHom]
  ofHom_hom _ := by ext; simp [ConcreteCategory.ofHom_hom]
  id_apply := ConcreteCategory.id_apply (C := V)
  comp_apply _ _ := ConcreteCategory.comp_apply (C := V) _ _

set_option backward.isDefEq.respectTransparency.types false in
/-
**Action.hasForgetToV** 是 Mathlib 中的一个实例，位于命名空间 `Action`。
形式化陈述：hasForgetToV {FV : V -> V -> Type*} {CV : V -> Type*} [forall X Y, FunLike
 (FV X Y) (CV X) (CV Y)] [ConcreteCategory V FV] : HasForget₂ (Action V G) V whe
re forget₂
参数：FV X Y；CV X；CV Y。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance hasForgetToV {FV : V → V → Type*} {CV : V → Type*} [∀ X Y, FunLike (FV X Y) (CV X) (CV Y)]
    [ConcreteCategory V FV] : HasForget₂ (Action V G) V where forget₂ := forget V G

set_option backward.isDefEq.respectTransparency.types false in
/-- The forgetful functor is intertwined by `functorCategoryEquivalence` with
evaluation at `PUnit.star`. -/
/-
**Action.functorCategoryEquivalenceCompEvaluation** 是 Mathlib 中的一个定义，位于命名空间 `Act
ion`。
形式化陈述：functorCategoryEquivalenceCompEvaluation : (functorCategoryEquivalence V G
).functor ⋙ (evaluation _ _).obj PUnit.unit ≅ forget V G
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The forgetful functor is intertwined by `functorCategoryEquivalence` with
evaluation at `PUnit.star`.
-/
def functorCategoryEquivalenceCompEvaluation :
    (functorCategoryEquivalence V G).functor ⋙ (evaluation _ _).obj PUnit.unit ≅ forget V G :=
  Iso.refl _

set_option backward.isDefEq.respectTransparency.types false in
/-
**Action.preservesLimits_forget** 是 Mathlib 中的一个实例，位于命名空间 `Action`。
形式化陈述：preservesLimits_forget [HasLimits V] : PreservesLimits (forget V G)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Limits.preservesLimits_of_natIso`：preservesLimits_of_natI
so {F G : C ⥤ D} (h : F ≅ G) [PreservesLimitsOfSize.{w, w'} F] : PreservesLimits
OfSize.{w, w'} G where preservesLimit…
· 使用定理 `CategoryTheory.Limits.comp_preservesLimits`：∀ {C : Type u₁} [inst : Cate
goryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.
{v₂, u₂} D]   {E : Type u₃} [ℰ :…
· 使用定理 `CategoryTheory.Functor.instPreservesLimitsOfSizeOfIsRightAdjoint`：∀ {C :
 Type u_2} {D : Type u_3} [inst : CategoryTheory.Category.{v_2, u_2} C]   [inst_
1 : CategoryTheory.Category.{v_3, u_3} D] (F : Categor…
· 使用定理 `CategoryTheory.Functor.isRightAdjoint_of_isEquivalence`：∀ {C : Type u₁} 
[inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheo
ry.Category.{v₂, u₂} D]   {F : CategoryTheor…
· 使用定理 `CategoryTheory.Equivalence.isEquivalence_functor`：∀ {C : Type u₁} [inst 
: CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Cat
egory.{v₂, u₂} D]   (F : C ≌ D), F.fun…
-/
noncomputable instance preservesLimits_forget [HasLimits V] :
    PreservesLimits (forget V G) :=
  Limits.preservesLimits_of_natIso (Action.functorCategoryEquivalenceCompEvaluation V G)

set_option backward.isDefEq.respectTransparency.types false in
/-
**Action.preservesColimits_forget** 是 Mathlib 中的一个实例，位于命名空间 `Action`。
形式化陈述：preservesColimits_forget [HasColimits V] : PreservesColimits (forget V G)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Limits.preservesColimits_of_natIso`：preservesColimits_of_
natIso {F G : C ⥤ D} (h : F ≅ G) [PreservesColimitsOfSize.{w, w'} F] : Preserves
ColimitsOfSize.{w, w'} G where preserve…
· 使用定理 `CategoryTheory.Limits.comp_preservesColimits`：∀ {C : Type u₁} [inst : Ca
tegoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Categor
y.{v₂, u₂} D]   {E : Type u₃} [ℰ :…
· 使用定理 `CategoryTheory.Functor.instPreservesColimitsOfSizeOfIsLeftAdjoint`：∀ {C 
: Type u_2} {D : Type u_3} [inst : CategoryTheory.Category.{v_2, u_2} C]   [inst
_1 : CategoryTheory.Category.{v_3, u_3} D] (F : Categor…
· 使用定理 `CategoryTheory.Functor.isLeftAdjoint_of_isEquivalence`：∀ {C : Type u₁} [
inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheor
y.Category.{v₂, u₂} D]   {F : CategoryTheor…
· 使用定理 `CategoryTheory.Equivalence.isEquivalence_functor`：∀ {C : Type u₁} [inst 
: CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Cat
egory.{v₂, u₂} D]   (F : C ≌ D), F.fun…
-/
noncomputable instance preservesColimits_forget [HasColimits V] :
    PreservesColimits (forget V G) :=
  preservesColimits_of_natIso (Action.functorCategoryEquivalenceCompEvaluation V G)

-- TODO construct categorical images?
end Forget

set_option backward.isDefEq.respectTransparency false in
/-
**Action.Iso.conj_** 是 Mathlib 中的一个定理，位于命名空间 `Action`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem Iso.conj_ρ {M N : Action V G} (f : M ≅ N) (g : G) :
    N.ρ g = ((forget V G).mapIso f).conj (M.ρ g) := by
      rw [Iso.conj_apply, Iso.eq_inv_comp]; simp [f.hom.comm]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- Actions/representations of the trivial monoid are just objects in the ambient category. -/
/-
**Action.actionPUnitEquivalence** 是 Mathlib 中的一个定义，位于命名空间 `Action`。
形式化陈述：actionPUnitEquivalence : Action V PUnit ≌ V where functor
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Actions/representations of the trivial monoid are just objects in the ambient ca
tegory.
-/
def actionPUnitEquivalence : Action V PUnit ≌ V where
  functor := forget V _
  inverse :=
    { obj := fun X => ⟨X, 1⟩
      map := fun f => ⟨f, fun ⟨⟩ => by simp⟩ }
  unitIso :=
    NatIso.ofComponents fun X => mkIso (Iso.refl _) fun ⟨⟩ => by
      simp only [Functor.id_obj, MonoidHom.one_apply, End.one_def, Functor.comp_obj,
        forget_obj, Iso.refl_hom, Category.comp_id]
      exact ρ_one X
  counitIso := NatIso.ofComponents fun _ => Iso.refl _

@[deprecated (since := "2026-02-08")] alias actionPunitEquivalence := actionPUnitEquivalence

variable (V)

set_option backward.isDefEq.respectTransparency.types false in
/-- The "restriction" functor along a monoid homomorphism `f : G →* H`,
taking actions of `H` to actions of `G`.

(This makes sense for any homomorphism, but the name is natural when `f` is a monomorphism.)
-/
@[simps]
/-
**Action.res** 是 Mathlib 中的一个定义，位于命名空间 `Action`。
形式化陈述：res {G H : Type*} [Monoid G] [Monoid H] (f : G ->* H) : Action V H ⥤ Actio
n V G where obj M
参数：f : G ->* H。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The "restriction" functor along a monoid homomorphism `f : G →* H`,
taking actions of `H` to actions of `G`.

(This makes sense for any homomorphism, but the name is natural when `f` is a mo
nomorphism.)
-/
def res {G H : Type*} [Monoid G] [Monoid H] (f : G →* H) : Action V H ⥤ Action V G where
  obj M :=
    { V := M.V
      ρ := M.ρ.comp f }
  map p :=
    { hom := p.hom
      comm := fun g => p.comm (f g) }

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- The natural isomorphism from restriction along the identity homomorphism to
the identity functor on `Action V G`.
-/
@[simps!]
/-
**Action.resId** 是 Mathlib 中的一个定义，位于命名空间 `Action`。
形式化陈述：resId {G : Type*} [Monoid G] : res V (MonoidHom.id G) ≅ 𝟭 (Action V G)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The natural isomorphism from restriction along the identity homomorphism to
the identity functor on `Action V G`.
-/
def resId {G : Type*} [Monoid G] : res V (MonoidHom.id G) ≅ 𝟭 (Action V G) :=
  NatIso.ofComponents fun M => mkIso (Iso.refl _)

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- The natural isomorphism from the composition of restrictions along homomorphisms
to the restriction along the composition of homomorphism.
-/
@[simps!]
/-
**Action.resComp** 是 Mathlib 中的一个定义，位于命名空间 `Action`。
形式化陈述：resComp {G H K : Type*} [Monoid G] [Monoid H] [Monoid K] (f : G ->* H) (g 
: H ->* K) : res V g ⋙ res V f ≅ res V (g.comp f)
参数：f : G ->* H；g : H ->* K。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The natural isomorphism from the composition of restrictions along homomorphisms
to the restriction along the composition of homomorphism.
-/
def resComp {G H K : Type*} [Monoid G] [Monoid H] [Monoid K]
    (f : G →* H) (g : H →* K) : res V g ⋙ res V f ≅ res V (g.comp f) :=
  NatIso.ofComponents fun M => mkIso (Iso.refl _)

set_option backward.isDefEq.respectTransparency.types false in
/-- Restricting scalars along equal maps is naturally isomorphic. -/
@[simps! hom inv]
/-
**Action.resCongr** 是 Mathlib 中的一个定义，位于命名空间 `Action`。
形式化陈述：resCongr {G H : Type*} [Monoid G] [Monoid H] {f f' : G ->* H} (h : f = f')
 : Action.res V f ≅ Action.res V f'
参数：h : f = f'。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Restricting scalars along equal maps is naturally isomorphic.
-/
def resCongr {G H : Type*} [Monoid G] [Monoid H] {f f' : G →* H} (h : f = f') :
    Action.res V f ≅ Action.res V f' :=
  NatIso.ofComponents (fun _ ↦ Action.mkIso (Iso.refl _))

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- Restricting scalars along a monoid isomorphism induces an equivalence of categories. -/
@[simps! functor inverse]
/-
**Action.resEquiv** 是 Mathlib 中的一个定义，位于命名空间 `Action`。
形式化陈述：resEquiv {G H : Type*} [Monoid G] [Monoid H] (f : G ≃* H) : Action V H ≌ A
ction V G where functor
参数：f : G ≃* H。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Restricting scalars along a monoid isomorphism induces an equivalence of categor
ies.
-/
def resEquiv {G H : Type*} [Monoid G] [Monoid H] (f : G ≃* H) :
    Action V H ≌ Action V G where
  functor := Action.res _ f
  inverse := Action.res _ f.symm
  unitIso := Action.resCongr (f := MonoidHom.id H) V (by ext; simp) ≪≫ (Action.resComp _ _ _).symm
  counitIso := Action.resComp _ _ _ ≪≫
    Action.resCongr (f' := MonoidHom.id G) V (by ext; simp)

-- TODO promote `res` to a pseudofunctor from
-- the locally discrete bicategory constructed from `Monᵒᵖ` to `Cat`, sending `G` to `Action V G`.

variable {G H : Type*} [Monoid G] [Monoid H] (f : G →* H)

/-- The functor from `Action V H` to `Action V G` induced by a monoid homomorphism
`f : G →* H` is faithful. -/
/-
**Action.** 是 Mathlib 中的一个实例，位于命名空间 `Action`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The functor from `Action V H` to `Action V G` induced by a monoid homomorphism
`f : G →* H` is faithful.
-/
instance : (res V f).Faithful where
  map_injective {X} {Y} g₁ g₂ h := by
    ext
    rw [← res_map_hom _ f g₁, ← res_map_hom _ f g₂, h]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The functor from `Action V H` to `Action V G` induced by a monoid homomorphism
`f : G →* H` is full if `f` is surjective. -/
/-
**Action.full_res** 是 Mathlib 中的一个引理，位于命名空间 `Action`。
形式化陈述：full_res (f_surj : Function.Surjective f) : (res V f).Full where map_surje
ctive {X} {Y} g
参数：f_surj : Function.Surjective f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Action.Hom.comm`：∀ {V : Type u_1} [inst : CategoryTheory.Category.{v_1, 
u_1} V] {G : Type u_2} [inst_1 : Monoid G] {M N : Action V G}   (self : M.Hom N)
 (g :…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用引理 `Action.hom_ext`：hom_ext {M N : Action V G} (φ₁ φ₂ : M ⟶ N) (h : φ₁.hom =
 φ₂.hom) : φ₁ = φ₂

--- 原说明 ---
The functor from `Action V H` to `Action V G` induced by a monoid homomorphism
`f : G →* H` is full if `f` is surjective.
-/
lemma full_res (f_surj : Function.Surjective f) : (res V f).Full where
  map_surjective {X} {Y} g := by
    use ⟨g.hom, fun h ↦ ?_⟩
    · ext
      simp
    · obtain ⟨a, rfl⟩ := f_surj h
      have : X.ρ (f a) = ((res V f).obj X).ρ a := rfl
      rw [this, g.comm a]
      simp

end Action

namespace CategoryTheory.Functor

variable {V} {W : Type*} [Category* W]

set_option backward.isDefEq.respectTransparency.types false in
/-- A functor between categories induces a functor between
the categories of `G`-actions within those categories. -/
@[simps]
/-
**CategoryTheory.Functor.mapAction** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Fun
ctor`。
形式化陈述：mapAction (F : V ⥤ W) (G : Type*) [Monoid G] : Action V G ⥤ Action W G whe
re obj M
参数：F : V ⥤ W；G : Type*。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A functor between categories induces a functor between
the categories of `G`-actions within those categories.
-/
def mapAction (F : V ⥤ W) (G : Type*) [Monoid G] : Action V G ⥤ Action W G where
  obj M :=
    { V := F.obj M.V
      ρ :=
        { toFun := fun g => F.map (M.ρ g)
          map_one' := by simp
          map_mul' := fun g h => by
            dsimp
            rw [map_mul, End.mul_def, F.map_comp] } }
  map f :=
    { hom := F.map f.hom
      comm := fun g => by dsimp; rw [← F.map_comp, f.comm, F.map_comp] }
  map_id M := by ext; simp only [Action.id_hom, F.map_id]
  map_comp f g := by ext; simp only [Action.comp_hom, F.map_comp]

set_option backward.isDefEq.respectTransparency.types false in
/-
**CategoryTheory.Functor.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Functor`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (F : V ⥤ W) (G : Type*) [Monoid G] [F.Faithful] : (F.mapAction G).Faithful where
  map_injective eq := by
    ext
    apply_fun (fun f ↦ f.hom) at eq
    exact F.map_injective eq

set_option backward.isDefEq.respectTransparency.types false in
/--
A fully faithful functor between categories induces a fully faithful functor between
the categories of `G`-actions within those categories. -/
/-
**CategoryTheory.Functor.FullyFaithful.mapAction** 是 Mathlib 中的一个定义，位于命名空间 `Cate
goryTheory.Functor.FullyFaithful`。
形式化陈述：{V : Type u_1} →   [inst : CategoryTheory.Category.{v_1, u_1} V] →     {W 
: Type u_2} →       [inst_1 : CategoryTheory.Category.{v_2, u_2} W] →         {F
 : CategoryTheory.Functor V W} →           F.FullyFaithful → (G : Type u_3) → [i
nst_2 : Monoid G] → (F.mapAction G).FullyFaithful
参数：G : Type u_3；F.mapAction G。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A fully faithful functor between categories induces a fully faithful functor bet
ween
the categories of `G`-actions within those categories.
-/
def FullyFaithful.mapAction {F : V ⥤ W} (h : F.FullyFaithful) (G : Type*) [Monoid G] :
    (F.mapAction G).FullyFaithful where
  preimage f := by
    refine ⟨h.preimage f.hom, fun _ ↦ h.map_injective ?_⟩
    simp only [map_comp, map_preimage]
    exact f.comm _
/-
**CategoryTheory.Functor.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Functor`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (F : V ⥤ W) (G : Type*) [Monoid G] [F.Faithful] [F.Full] : (F.mapAction G).Full :=
  ((Functor.FullyFaithful.ofFullyFaithful F).mapAction G).full

variable (G : Type*) [Monoid G]

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- `Functor.mapAction` is functorial in the functor. -/
@[simps! hom inv]
/-
**CategoryTheory.Functor.mapActionComp** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory
.Functor`。
形式化陈述：mapActionComp {T : Type*} [Category* T] (F : V ⥤ W) (F' : W ⥤ T) : (F ⋙ F'
).mapAction G ≅ F.mapAction G ⋙ F'.mapAction G
参数：F : V ⥤ W；F' : W ⥤ T。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`Functor.mapAction` is functorial in the functor.
-/
def mapActionComp {T : Type*} [Category* T] (F : V ⥤ W) (F' : W ⥤ T) :
    (F ⋙ F').mapAction G ≅ F.mapAction G ⋙ F'.mapAction G :=
  NatIso.ofComponents (fun X ↦ Iso.refl _)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- `Functor.mapAction` preserves isomorphisms of functors. -/
@[simps! hom inv]
/-
**CategoryTheory.Functor.mapActionCongr** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheor
y.Functor`。
形式化陈述：mapActionCongr {F F' : V ⥤ W} (e : F ≅ F') : F.mapAction G ≅ F'.mapAction 
G
参数：e : F ≅ F'。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`Functor.mapAction` preserves isomorphisms of functors.
-/
def mapActionCongr {F F' : V ⥤ W} (e : F ≅ F') :
    F.mapAction G ≅ F'.mapAction G :=
  NatIso.ofComponents (fun X ↦ Action.mkIso (e.app X.V))

end Functor

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- An equivalence of categories induces an equivalence of
the categories of `G`-actions within those categories. -/
@[simps functor inverse]
/-
**CategoryTheory.Equivalence.mapAction** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory
.Equivalence`。
形式化陈述：{V : Type u_2} →   {W : Type u_3} →     [inst : CategoryTheory.Category.{v
_2, u_2} V] →       [inst_1 : CategoryTheory.Category.{v_3, u_3} W] →         (G
 : Type u_4) → [inst_2 : Monoid G] → (V ≌ W) → (Action V G ≌ Action W G)
参数：G : Type u_4；V ≌ W；Action V G ≌ Action W G。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An equivalence of categories induces an equivalence of
the categories of `G`-actions within those categories.
-/
def Equivalence.mapAction {V W : Type*} [Category* V] [Category* W] (G : Type*) [Monoid G]
    (E : V ≌ W) : Action V G ≌ Action W G where
  functor := E.functor.mapAction G
  inverse := E.inverse.mapAction G
  unitIso := Functor.mapActionCongr G E.unitIso ≪≫ Functor.mapActionComp G _ _
  counitIso := (Functor.mapActionComp G _ _).symm ≪≫ Functor.mapActionCongr G E.counitIso
  functor_unitIso_comp X := by ext; simp

end CategoryTheory

