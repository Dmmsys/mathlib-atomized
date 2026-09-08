/-
Copyright (c) 2020 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison, Joël Riou
-/
module

public import Mathlib.CategoryTheory.Shift.Basic
public import Mathlib.Data.Set.Subsingleton
public import Mathlib.Algebra.Group.Int.Defs

/-!
# The category of graded objects

For any type `β`, a `β`-graded object over some category `C` is just
a function `β → C` into the objects of `C`.
We put the "pointwise" category structure on these, as the non-dependent specialization of
`CategoryTheory.Pi`.

We describe the `comap` functors obtained by precomposing with functions `β → γ`.

As a consequence a fixed element (e.g. `1`) in an additive group `β` provides a shift
functor on `β`-graded objects

When `C` has coproducts we construct the `total` functor `GradedObject β C ⥤ C`,
show that it is faithful, and deduce that when `C` is concrete so is `GradedObject β C`.

A covariant functoriality of `GradedObject β C` with respect to the index set `β` is also
introduced: if `p : I → J` is a map such that `C` has coproducts indexed by `p ⁻¹' {j}`, we
have a functor `map : GradedObject I C ⥤ GradedObject J C`.

-/

@[expose] public section

namespace CategoryTheory

open Category Limits

universe w v u

/-- A type synonym for `β → C`, used for `β`-graded objects in a category `C`. -/
@[implicit_reducible]
/-
**CategoryTheory.GradedObject** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory`。
形式化陈述：GradedObject (β : Type w) (C : Type u) : Type max w u
参数：β : Type w；C : Type u。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A type synonym for `β → C`, used for `β`-graded objects in a category `C`.
-/
def GradedObject (β : Type w) (C : Type u) : Type max w u :=
  β → C

-- Satisfying the inhabited linter...
/-
**CategoryTheory.inhabitedGradedObject** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory
`。
形式化陈述：inhabitedGradedObject (β : Type w) (C : Type u) [Inhabited C] : Inhabited 
(GradedObject β C)
参数：β : Type w；C : Type u。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance inhabitedGradedObject (β : Type w) (C : Type u) [Inhabited C] :
    Inhabited (GradedObject β C) :=
  ⟨fun _ => Inhabited.default⟩

-- `s` is here to distinguish type synonyms asking for different shifts
/-- A type synonym for `β → C`, used for `β`-graded objects in a category `C`
with a shift functor given by translation by `s`.
-/
@[nolint unusedArguments]
/-
**CategoryTheory.GradedObjectWithShift** 是 Mathlib 中的一个缩写定义，位于命名空间 `CategoryTheo
ry`。
形式化陈述：GradedObjectWithShift {β : Type w} [AddCommGroup β] (_ : β) (C : Type u) :
 Type max w u
参数：_ : β；C : Type u。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A type synonym for `β → C`, used for `β`-graded objects in a category `C`
with a shift functor given by translation by `s`.
-/
abbrev GradedObjectWithShift {β : Type w} [AddCommGroup β] (_ : β) (C : Type u) : Type max w u :=
  GradedObject β C

namespace GradedObject

variable {C : Type u} [Category.{v} C]

@[simps!]
/-
**CategoryTheory.GradedObject.categoryOfGradedObjects** 是 Mathlib 中的一个实例，位于命名空间 
`CategoryTheory.GradedObject`。
形式化陈述：categoryOfGradedObjects (β : Type w) : Category.{max w v} (GradedObject β 
C)
参数：β : Type w。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance categoryOfGradedObjects (β : Type w) : Category.{max w v} (GradedObject β C) :=
  CategoryTheory.pi fun _ => C

@[ext]
/-
**CategoryTheory.GradedObject.hom_ext** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.
GradedObject`。
形式化陈述：hom_ext {β : Type*} {X Y : GradedObject β C} (f g : X ⟶ Y) (h : forall x, 
f x = g x) : f = g
参数：f g : X ⟶ Y；h : forall x, f x = g x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
-/
lemma hom_ext {β : Type*} {X Y : GradedObject β C} (f g : X ⟶ Y) (h : ∀ x, f x = g x) : f = g := by
  funext
  apply h

/-- The projection of a graded object to its `i`-th component. -/
@[simps]
/-
**CategoryTheory.GradedObject.eval** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Gra
dedObject`。
形式化陈述：eval {β : Type w} (b : β) : GradedObject β C ⥤ C where obj X
参数：b : β。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The projection of a graded object to its `i`-th component.
-/
def eval {β : Type w} (b : β) : GradedObject β C ⥤ C where
  obj X := X b
  map f := f b

section

variable {β : Type*} (X Y : GradedObject β C)

set_option backward.isDefEq.respectTransparency.types false in
/-- Constructor for isomorphisms in `GradedObject` -/
@[simps]
/-
**CategoryTheory.GradedObject.isoMk** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Gr
adedObject`。
形式化陈述：isoMk (e : forall i, X i ≅ Y i) : X ≅ Y where hom i
参数：e : forall i, X i ≅ Y i。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Constructor for isomorphisms in `GradedObject`
-/
def isoMk (e : ∀ i, X i ≅ Y i) : X ≅ Y where
  hom i := (e i).hom
  inv i := (e i).inv

variable {X Y}

-- this lemma is not an instance as it may create a loop with `isIso_apply_of_isIso`
set_option backward.isDefEq.respectTransparency.types false in
/-
**CategoryTheory.GradedObject.isIso_of_isIso_apply** 是 Mathlib 中的一个引理，位于命名空间 `Ca
tegoryTheory.GradedObject`。
形式化陈述：isIso_of_isIso_apply (f : X ⟶ Y) [hf : forall i, IsIso (f i)] : IsIso f
参数：f : X ⟶ Y；f i。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Iso.isIso_hom`：∀ {C : Type u} [inst : CategoryTheory.Cate
gory.{v, u} C] {X Y : C} (e : X ≅ Y), CategoryTheory.IsIso e.hom
-/
lemma isIso_of_isIso_apply (f : X ⟶ Y) [hf : ∀ i, IsIso (f i)] :
    IsIso f := by
  change IsIso (isoMk X Y (fun i => asIso (f i))).hom
  infer_instance
/-
**CategoryTheory.GradedObject.isIso_apply_of_isIso** 是 Mathlib 中的一个实例，位于命名空间 `Ca
tegoryTheory.GradedObject`。
形式化陈述：isIso_apply_of_isIso (f : X ⟶ Y) [IsIso f] (i : β) : IsIso (f i)
参数：f : X ⟶ Y；i : β。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance isIso_apply_of_isIso (f : X ⟶ Y) [IsIso f] (i : β) : IsIso (f i) := by
  change IsIso ((eval i).map f)
  infer_instance

end

end GradedObject

namespace Iso

variable {C D E J : Type*} [Category* C] [Category* D] [Category* E]
  {X Y : GradedObject J C}

set_option backward.isDefEq.respectTransparency.types false in
@[reassoc (attr := simp)]
/-
**CategoryTheory.Iso.hom_inv_id_eval** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.I
so`。
形式化陈述：hom_inv_id_eval (e : X ≅ Y) (j : J) : e.hom j ≫ e.inv j = 𝟙 _
参数：e : X ≅ Y；j : J。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.GradedObject.categoryOfGradedObjects_comp`：∀ {C : Type u}
 [inst : CategoryTheory.Category.{v, u} C] (β : Type w) {X Y Z : (i : β) → (fun 
x => C) i}   (f : (i : β) → X i ⟶ Y i) (g : (i…
· 使用定理 `CategoryTheory.Iso.hom_inv_id`：∀ {C : Type u} [inst : CategoryTheory.Cat
egory.{v, u} C] {X Y : C} (self : X ≅ Y),   CategoryTheory.CategoryStruct.comp s
elf.hom self.inv = …
· 使用定理 `CategoryTheory.GradedObject.categoryOfGradedObjects_id`：∀ {C : Type u} [
inst : CategoryTheory.Category.{v, u} C] (β : Type w) (X : (i : β) → (fun x => C
) i) (i : β),   CategoryTheory.CategoryStruc…
-/
lemma hom_inv_id_eval (e : X ≅ Y) (j : J) :
    e.hom j ≫ e.inv j = 𝟙 _ := by
  rw [← GradedObject.categoryOfGradedObjects_comp, e.hom_inv_id,
    GradedObject.categoryOfGradedObjects_id]

set_option backward.isDefEq.respectTransparency.types false in
@[reassoc (attr := simp)]
/-
**CategoryTheory.Iso.inv_hom_id_eval** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.I
so`。
形式化陈述：inv_hom_id_eval (e : X ≅ Y) (j : J) : e.inv j ≫ e.hom j = 𝟙 _
参数：e : X ≅ Y；j : J。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.GradedObject.categoryOfGradedObjects_comp`：∀ {C : Type u}
 [inst : CategoryTheory.Category.{v, u} C] (β : Type w) {X Y Z : (i : β) → (fun 
x => C) i}   (f : (i : β) → X i ⟶ Y i) (g : (i…
· 使用定理 `CategoryTheory.Iso.inv_hom_id`：∀ {C : Type u} [inst : CategoryTheory.Cat
egory.{v, u} C] {X Y : C} (self : X ≅ Y),   CategoryTheory.CategoryStruct.comp s
elf.inv self.hom = …
· 使用定理 `CategoryTheory.GradedObject.categoryOfGradedObjects_id`：∀ {C : Type u} [
inst : CategoryTheory.Category.{v, u} C] (β : Type w) (X : (i : β) → (fun x => C
) i) (i : β),   CategoryTheory.CategoryStruc…
-/
lemma inv_hom_id_eval (e : X ≅ Y) (j : J) :
    e.inv j ≫ e.hom j = 𝟙 _ := by
  rw [← GradedObject.categoryOfGradedObjects_comp, e.inv_hom_id,
    GradedObject.categoryOfGradedObjects_id]

set_option backward.isDefEq.respectTransparency.types false in
@[reassoc (attr := simp)]
/-
**CategoryTheory.Iso.map_hom_inv_id_eval** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheo
ry.Iso`。
形式化陈述：map_hom_inv_id_eval (e : X ≅ Y) (F : C ⥤ D) (j : J) : F.map (e.hom j) ≫ F.
map (e.inv j) = 𝟙 _
参数：e : X ≅ Y；F : C ⥤ D；j : J。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.Functor.map_comp`：∀ {C : Type u₁} [inst : CategoryTheory.
Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]
   (self : CategoryTh…
· 使用定理 `CategoryTheory.GradedObject.categoryOfGradedObjects_comp`：∀ {C : Type u}
 [inst : CategoryTheory.Category.{v, u} C] (β : Type w) {X Y Z : (i : β) → (fun 
x => C) i}   (f : (i : β) → X i ⟶ Y i) (g : (i…
· 使用定理 `CategoryTheory.Iso.hom_inv_id`：∀ {C : Type u} [inst : CategoryTheory.Cat
egory.{v, u} C] {X Y : C} (self : X ≅ Y),   CategoryTheory.CategoryStruct.comp s
elf.hom self.inv = …
· 使用定理 `CategoryTheory.GradedObject.categoryOfGradedObjects_id`：∀ {C : Type u} [
inst : CategoryTheory.Category.{v, u} C] (β : Type w) (X : (i : β) → (fun x => C
) i) (i : β),   CategoryTheory.CategoryStruc…
· 使用定理 `CategoryTheory.Functor.map_id`：∀ {C : Type u₁} [inst : CategoryTheory.Ca
tegory.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]  
 (self : CategoryTh…
-/
lemma map_hom_inv_id_eval (e : X ≅ Y) (F : C ⥤ D) (j : J) :
    F.map (e.hom j) ≫ F.map (e.inv j) = 𝟙 _ := by
  rw [← F.map_comp, ← GradedObject.categoryOfGradedObjects_comp, e.hom_inv_id,
    GradedObject.categoryOfGradedObjects_id, Functor.map_id]

set_option backward.isDefEq.respectTransparency.types false in
@[reassoc (attr := simp)]
/-
**CategoryTheory.Iso.map_inv_hom_id_eval** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheo
ry.Iso`。
形式化陈述：map_inv_hom_id_eval (e : X ≅ Y) (F : C ⥤ D) (j : J) : F.map (e.inv j) ≫ F.
map (e.hom j) = 𝟙 _
参数：e : X ≅ Y；F : C ⥤ D；j : J。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.Functor.map_comp`：∀ {C : Type u₁} [inst : CategoryTheory.
Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]
   (self : CategoryTh…
· 使用定理 `CategoryTheory.GradedObject.categoryOfGradedObjects_comp`：∀ {C : Type u}
 [inst : CategoryTheory.Category.{v, u} C] (β : Type w) {X Y Z : (i : β) → (fun 
x => C) i}   (f : (i : β) → X i ⟶ Y i) (g : (i…
· 使用定理 `CategoryTheory.Iso.inv_hom_id`：∀ {C : Type u} [inst : CategoryTheory.Cat
egory.{v, u} C] {X Y : C} (self : X ≅ Y),   CategoryTheory.CategoryStruct.comp s
elf.inv self.hom = …
· 使用定理 `CategoryTheory.GradedObject.categoryOfGradedObjects_id`：∀ {C : Type u} [
inst : CategoryTheory.Category.{v, u} C] (β : Type w) (X : (i : β) → (fun x => C
) i) (i : β),   CategoryTheory.CategoryStruc…
· 使用定理 `CategoryTheory.Functor.map_id`：∀ {C : Type u₁} [inst : CategoryTheory.Ca
tegory.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]  
 (self : CategoryTh…
-/
lemma map_inv_hom_id_eval (e : X ≅ Y) (F : C ⥤ D) (j : J) :
    F.map (e.inv j) ≫ F.map (e.hom j) = 𝟙 _ := by
  rw [← F.map_comp, ← GradedObject.categoryOfGradedObjects_comp, e.inv_hom_id,
    GradedObject.categoryOfGradedObjects_id, Functor.map_id]

@[reassoc (attr := simp)]
/-
**CategoryTheory.Iso.map_hom_inv_id_eval_app** 是 Mathlib 中的一个引理，位于命名空间 `Category
Theory.Iso`。
形式化陈述：map_hom_inv_id_eval_app (e : X ≅ Y) (F : C ⥤ D ⥤ E) (j : J) (Y : D) : (F.m
ap (e.hom j)).app Y ≫ (F.map (e.inv j)).app Y = 𝟙 _
参数：e : X ≅ Y；F : C ⥤ D ⥤ E；j : J；Y : D。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.NatTrans.comp_app`：comp_app {F G H : C ⥤ D} (α : F ⟶ G) (
β : G ⟶ H) (X : C) : (α ≫ β).app X = α.app X ≫ β.app X
· 使用定理 `CategoryTheory.Functor.map_comp`：∀ {C : Type u₁} [inst : CategoryTheory.
Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]
   (self : CategoryTh…
· 使用引理 `CategoryTheory.Iso.hom_inv_id_eval`：hom_inv_id_eval (e : X ≅ Y) (j : J) 
: e.hom j ≫ e.inv j = 𝟙 _
· 使用定理 `CategoryTheory.Functor.map_id`：∀ {C : Type u₁} [inst : CategoryTheory.Ca
tegory.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]  
 (self : CategoryTh…
· 使用定理 `CategoryTheory.NatTrans.id_app`：id_app (F : C ⥤ D) (X : C) : (𝟙 F : F ⟶ 
F).app X = 𝟙 (F.obj X)
-/
lemma map_hom_inv_id_eval_app (e : X ≅ Y) (F : C ⥤ D ⥤ E) (j : J) (Y : D) :
    (F.map (e.hom j)).app Y ≫ (F.map (e.inv j)).app Y = 𝟙 _ := by
  rw [← NatTrans.comp_app, ← F.map_comp, hom_inv_id_eval,
    Functor.map_id, NatTrans.id_app]

@[reassoc (attr := simp)]
/-
**CategoryTheory.Iso.map_inv_hom_id_eval_app** 是 Mathlib 中的一个引理，位于命名空间 `Category
Theory.Iso`。
形式化陈述：map_inv_hom_id_eval_app (e : X ≅ Y) (F : C ⥤ D ⥤ E) (j : J) (Y : D) : (F.m
ap (e.inv j)).app Y ≫ (F.map (e.hom j)).app Y = 𝟙 _
参数：e : X ≅ Y；F : C ⥤ D ⥤ E；j : J；Y : D。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.NatTrans.comp_app`：comp_app {F G H : C ⥤ D} (α : F ⟶ G) (
β : G ⟶ H) (X : C) : (α ≫ β).app X = α.app X ≫ β.app X
· 使用定理 `CategoryTheory.Functor.map_comp`：∀ {C : Type u₁} [inst : CategoryTheory.
Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]
   (self : CategoryTh…
· 使用引理 `CategoryTheory.Iso.inv_hom_id_eval`：inv_hom_id_eval (e : X ≅ Y) (j : J) 
: e.inv j ≫ e.hom j = 𝟙 _
· 使用定理 `CategoryTheory.Functor.map_id`：∀ {C : Type u₁} [inst : CategoryTheory.Ca
tegory.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]  
 (self : CategoryTh…
· 使用定理 `CategoryTheory.NatTrans.id_app`：id_app (F : C ⥤ D) (X : C) : (𝟙 F : F ⟶ 
F).app X = 𝟙 (F.obj X)
-/
lemma map_inv_hom_id_eval_app (e : X ≅ Y) (F : C ⥤ D ⥤ E) (j : J) (Y : D) :
    (F.map (e.inv j)).app Y ≫ (F.map (e.hom j)).app Y = 𝟙 _ := by
  rw [← NatTrans.comp_app, ← F.map_comp, inv_hom_id_eval,
    Functor.map_id, NatTrans.id_app]

end Iso

namespace GradedObject

variable {C : Type u} [Category.{v} C]

section

variable (C)

/-- Pull back an `I`-graded object in `C` to a `J`-graded object along a function `J → I`. -/
/-
**CategoryTheory.GradedObject.comap** 是 Mathlib 中的一个缩写定义，位于命名空间 `CategoryTheory.
GradedObject`。
形式化陈述：comap {I J : Type*} (h : J -> I) : GradedObject I C ⥤ GradedObject J C
参数：h : J -> I。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Pull back an `I`-graded object in `C` to a `J`-graded object along a function `J
 → I`.
-/
abbrev comap {I J : Type*} (h : J → I) : GradedObject I C ⥤ GradedObject J C :=
  Pi.comap (fun _ => C) h

@[simp]
/-
**CategoryTheory.GradedObject.eqToHom_proj** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTh
eory.GradedObject`。
形式化陈述：eqToHom_proj {I : Type*} {x x' : GradedObject I C} (h : x = x') (i : I) : 
(eqToHom h : x ⟶ x') i = eqToHom (funext_iff.mp h i)
参数：h : x = x'；i : I。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `funext_iff`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g
 ↔ ∀ (x : α), f x = g x
-/
theorem eqToHom_proj {I : Type*} {x x' : GradedObject I C} (h : x = x') (i : I) :
    (eqToHom h : x ⟶ x') i = eqToHom (funext_iff.mp h i) := by
  subst h
  rfl

set_option backward.isDefEq.respectTransparency.types false in
/-- The natural isomorphism comparing between
pulling back along two propositionally equal functions.
-/
@[simps]
/-
**CategoryTheory.GradedObject.comapEq** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.
GradedObject`。
形式化陈述：comapEq {β γ : Type w} {f g : β -> γ} (h : f = g) : comap C f ≅ comap C g 
where hom
参数：h : f = g。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The natural isomorphism comparing between
pulling back along two propositionally equal functions.
-/
def comapEq {β γ : Type w} {f g : β → γ} (h : f = g) : comap C f ≅ comap C g where
  hom := { app := fun X b => eqToHom (by dsimp; simp only [h]) }
  inv := { app := fun X b => eqToHom (by dsimp; simp only [h]) }
/-
**CategoryTheory.GradedObject.comapEq_symm** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTh
eory.GradedObject`。
形式化陈述：comapEq_symm {β γ : Type w} {f g : β -> γ} (h : f = g) : comapEq C h.symm 
= (comapEq C h).symm
参数：h : f = g。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem comapEq_symm {β γ : Type w} {f g : β → γ} (h : f = g) :
    comapEq C h.symm = (comapEq C h).symm := by cat_disch

set_option backward.isDefEq.respectTransparency.types false in
/-
**CategoryTheory.GradedObject.comapEq_trans** 是 Mathlib 中的一个定理，位于命名空间 `CategoryT
heory.GradedObject`。
形式化陈述：comapEq_trans {β γ : Type w} {f g h : β -> γ} (k : f = g) (l : g = h) : co
mapEq C (k.trans l) = comapEq C k ≪≫ comapEq C l
参数：k : f = g；l : g = h。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `CategoryTheory.Iso.ext`：ext ⦃α β : X ≅ Y⦄ (w : α.hom = β.hom) : α = β
· 使用定理 `CategoryTheory.NatTrans.ext'`：ext' {α β : F ⟶ G} (w : α.app = β.app) : α
 = β
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用引理 `CategoryTheory.GradedObject.hom_ext`：hom_ext {β : Type*} {X Y : GradedOb
ject β C} (f g : X ⟶ Y) (h : forall x, f x = g x) : f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.GradedObject.comapEq_hom_app`：∀ (C : Type u) [inst : Cate
goryTheory.Category.{v, u} C] {β γ : Type w} {f g : β → γ} (h : f = g)   (X : Ca
tegoryTheory.GradedObject γ C) (b…
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem comapEq_trans {β γ : Type w} {f g h : β → γ} (k : f = g) (l : g = h) :
    comapEq C (k.trans l) = comapEq C k ≪≫ comapEq C l := by cat_disch
/-
**CategoryTheory.GradedObject.eqToHom_apply** 是 Mathlib 中的一个定理，位于命名空间 `CategoryT
heory.GradedObject`。
形式化陈述：eqToHom_apply {β : Type w} {X Y : β -> C} (h : X = Y) (b : β) : (eqToHom h
 : X ⟶ Y) b = eqToHom (by rw [h])
参数：h : X = Y；b : β。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem eqToHom_apply {β : Type w} {X Y : β → C} (h : X = Y) (b : β) :
    (eqToHom h : X ⟶ Y) b = eqToHom (by rw [h]) := by
  subst h
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- The equivalence between β-graded objects and γ-graded objects,
given an equivalence between β and γ.
-/
@[simps]
/-
**CategoryTheory.GradedObject.comapEquiv** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheo
ry.GradedObject`。
形式化陈述：comapEquiv {β γ : Type w} (e : β ≃ γ) : GradedObject β C ≌ GradedObject γ 
C where functor
参数：e : β ≃ γ。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s

--- 原说明 ---
The equivalence between β-graded objects and γ-graded objects,
given an equivalence between β and γ.
-/
def comapEquiv {β γ : Type w} (e : β ≃ γ) : GradedObject β C ≌ GradedObject γ C where
  functor := comap C (e.symm : γ → β)
  inverse := comap C (e : β → γ)
  counitIso :=
    (Pi.comapComp (fun _ => C) _ _).trans (comapEq C (by ext; simp))
  unitIso :=
    (comapEq C (by ext; simp)).trans (Pi.comapComp _ _ _).symm

end

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-
**CategoryTheory.GradedObject.hasShift** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory
.GradedObject`。
形式化陈述：hasShift {β : Type*} [AddCommGroup β] (s : β) : HasShift (GradedObjectWith
Shift s C) Int
参数：s : β。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance hasShift {β : Type*} [AddCommGroup β] (s : β) : HasShift (GradedObjectWithShift s C) ℤ :=
  hasShiftMk _ _
    { F := fun n => comap C fun b : β => b + n • s
      zero := comapEq C (by cat_disch) ≪≫ Pi.comapId β fun _ => C
      add := fun m n => comapEq C (by ext; dsimp; rw [add_comm m n, add_zsmul, add_assoc]) ≪≫
          (Pi.comapComp _ _ _).symm }

set_option backward.isDefEq.respectTransparency.types false in
@[simp]
/-
**CategoryTheory.GradedObject.shiftFunctor_obj_apply** 是 Mathlib 中的一个定理，位于命名空间 `
CategoryTheory.GradedObject`。
形式化陈述：shiftFunctor_obj_apply {β : Type*} [AddCommGroup β] (s : β) (X : β -> C) (
t : β) (n : Int) : (shiftFunctor (GradedObjectWithShift s C) n).obj X t = X (t +
 n • s)
参数：s : β；X : β -> C；t : β；n : Int。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem shiftFunctor_obj_apply {β : Type*} [AddCommGroup β] (s : β) (X : β → C) (t : β) (n : ℤ) :
    (shiftFunctor (GradedObjectWithShift s C) n).obj X t = X (t + n • s) :=
  rfl

set_option backward.isDefEq.respectTransparency.types false in
@[simp]
/-
**CategoryTheory.GradedObject.shiftFunctor_map_apply** 是 Mathlib 中的一个定理，位于命名空间 `
CategoryTheory.GradedObject`。
形式化陈述：shiftFunctor_map_apply {β : Type*} [AddCommGroup β] (s : β) {X Y : GradedO
bjectWithShift s C} (f : X ⟶ Y) (t : β) (n : Int) : (shiftFunctor (GradedObjectW
ithShift s C) n).map f t = f (t + n • s)
参数：s : β；f : X ⟶ Y；t : β；n : Int。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem shiftFunctor_map_apply {β : Type*} [AddCommGroup β] (s : β)
    {X Y : GradedObjectWithShift s C} (f : X ⟶ Y) (t : β) (n : ℤ) :
    (shiftFunctor (GradedObjectWithShift s C) n).map f t = f (t + n • s) :=
  rfl
/-
**CategoryTheory.GradedObject.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.GradedO
bject`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [HasZeroMorphisms C] (β : Type w) (X Y : GradedObject β C) : Zero (X ⟶ Y) :=
  ⟨fun _ => 0⟩

@[simp]
/-
**CategoryTheory.GradedObject.zero_apply** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheo
ry.GradedObject`。
形式化陈述：zero_apply [HasZeroMorphisms C] (β : Type w) (X Y : GradedObject β C) (b :
 β) : (0 : X ⟶ Y) b = 0
参数：β : Type w；X Y : GradedObject β C；b : β。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem zero_apply [HasZeroMorphisms C] (β : Type w) (X Y : GradedObject β C) (b : β) :
    (0 : X ⟶ Y) b = 0 :=
  rfl

set_option backward.isDefEq.respectTransparency.types false in
/-
**CategoryTheory.GradedObject.hasZeroMorphisms** 是 Mathlib 中的一个定义，位于命名空间 `Catego
ryTheory.GradedObject`。
形式化陈述：{C : Type u} →   [inst : CategoryTheory.Category.{v, u} C] →     [Category
Theory.Limits.HasZeroMorphisms C] →       (β : Type w) → CategoryTheory.Limits.H
asZeroMorphisms (CategoryTheory.GradedObject β C)
参数：β : Type w；CategoryTheory.GradedObject β C。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance hasZeroMorphisms [HasZeroMorphisms C] (β : Type w) :
    HasZeroMorphisms.{max w v} (GradedObject β C) where

section

open ZeroObject

/-
**CategoryTheory.GradedObject.hasZeroObject** 是 Mathlib 中的一个实例，位于命名空间 `CategoryT
heory.GradedObject`。
形式化陈述：hasZeroObject [HasZeroObject C] [HasZeroMorphisms C] (β : Type w) : HasZer
oObject.{max w v} (GradedObject β C)
参数：β : Type w。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.GradedObject.hom_ext`：hom_ext {β : Type*} {X Y : GradedOb
ject β C} (f g : X ⟶ Y) (h : forall x, f x = g x) : f = g
· 使用定理 `CategoryTheory.Limits.HasZeroObject.from_zero_ext`：from_zero_ext {X : C}
 (f g : 0 ⟶ X) : f = g
· 使用定理 `CategoryTheory.Limits.HasZeroObject.to_zero_ext`：to_zero_ext {X : C} (f 
g : X ⟶ 0) : f = g
-/
instance hasZeroObject [HasZeroObject C] [HasZeroMorphisms C] (β : Type w) :
    HasZeroObject.{max w v} (GradedObject β C) := by
  refine ⟨⟨fun _ => 0, fun X => ⟨⟨⟨fun b => 0⟩, fun f => ?_⟩⟩, fun X =>
    ⟨⟨⟨fun b => 0⟩, fun f => ?_⟩⟩⟩⟩ <;> cat_disch

end

end GradedObject

namespace GradedObject

-- The universes get a little hairy here, so we restrict the universe level for the grading to 0.
-- Since we're typically interested in grading by ℤ or a finite group, this should be okay.
-- If you're grading by things in higher universes, have fun!
variable (β : Type)
variable (C : Type u) [Category.{v} C]
variable [HasCoproducts.{0} C]

section

set_option backward.isDefEq.respectTransparency.types false in
/-- The total object of a graded object is the coproduct of the graded components.
-/
/-
**CategoryTheory.GradedObject.total** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Gr
adedObject`。
形式化陈述：total : GradedObject β C ⥤ C where obj X
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The total object of a graded object is the coproduct of the graded components.
-/
noncomputable def total : GradedObject β C ⥤ C where
  obj X := ∐ fun i : β => X i
  map f := Limits.Sigma.map fun i => f i

end

variable [HasZeroMorphisms C]

set_option backward.isDefEq.respectTransparency.types false in
/--
The `total` functor taking a graded object to the coproduct of its graded components is faithful.
To prove this, we need to know that the coprojections into the coproduct are monomorphisms,
which follows from the fact we have zero morphisms and decidable equality for the grading.
-/
/-
**CategoryTheory.GradedObject.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.GradedO
bject`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The `total` functor taking a graded object to the coproduct of its graded compon
ents is faithful.
To prove this, we need to know that the coprojections into the coproduct are mon
omorphisms,
which follows from the fact we have zero morphisms and decidable equality for th
e grading.
-/
instance : (total β C).Faithful where
  map_injective {X Y} f g w := by
    ext i
    replace w := Sigma.ι (fun i : β => X i) i ≫= w
    erw [colimit.ι_map, colimit.ι_map] at w
    replace w : f i ≫ colimit.ι (Discrete.functor Y) ⟨i⟩ =
      g i ≫ colimit.ι (Discrete.functor Y) ⟨i⟩ := by simpa
    exact Mono.right_cancellation _ _ w

end GradedObject

namespace GradedObject

variable {I J K : Type*} {C : Type*} [Category* C]
  (X Y Z : GradedObject I C) (φ : X ⟶ Y) (e : X ≅ Y) (ψ : Y ⟶ Z) (p : I → J)

/-- If `X : GradedObject I C` and `p : I → J`, `X.mapObjFun p j` is the family of objects `X i`
for `i : I` such that `p i = j`. -/
/-
**CategoryTheory.GradedObject.mapObjFun** 是 Mathlib 中的一个缩写定义，位于命名空间 `CategoryThe
ory.GradedObject`。
形式化陈述：mapObjFun (j : J) (i : p ⁻¹' {j}) : C
参数：j : J；i : p ⁻¹' {j}。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `X : GradedObject I C` and `p : I → J`, `X.mapObjFun p j` is the family of ob
jects `X i`
for `i : I` such that `p i = j`.
-/
abbrev mapObjFun (j : J) (i : p ⁻¹' {j}) : C := X i

variable (j : J)

/-- Given `X : GradedObject I C` and `p : I → J`, `X.HasMap p` is the condition that
for all `j : J`, the coproduct of all `X i` such `p i = j` exists. -/
/-
**CategoryTheory.GradedObject.HasMap** 是 Mathlib 中的一个缩写定义，位于命名空间 `CategoryTheory
.GradedObject`。
形式化陈述：HasMap : Prop
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given `X : GradedObject I C` and `p : I → J`, `X.HasMap p` is the condition that
for all `j : J`, the coproduct of all `X i` such `p i = j` exists.
-/
abbrev HasMap : Prop := ∀ (j : J), HasCoproduct (X.mapObjFun p j)

variable {X Y} in
/-
**CategoryTheory.GradedObject.hasMap_of_iso** 是 Mathlib 中的一个引理，位于命名空间 `CategoryT
heory.GradedObject`。
形式化陈述：hasMap_of_iso (e : X ≅ Y) (p : I -> J) [HasMap X p] : HasMap Y p
参数：e : X ≅ Y；p : I -> J。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.hasColimit_of_iso`：hasColimit_of_iso {F G : J ⥤ C}
 [HasColimit F] (α : G ≅ F) : HasColimit G
-/
lemma hasMap_of_iso (e : X ≅ Y) (p : I → J) [HasMap X p] : HasMap Y p := fun j => by
  have α : Discrete.functor (X.mapObjFun p j) ≅ Discrete.functor (Y.mapObjFun p j) :=
    Discrete.natIso (fun ⟨i, _⟩ => (GradedObject.eval i).mapIso e)
  exact hasColimit_of_iso α.symm

section
variable [X.HasMap p] [Y.HasMap p]

/-- Given `X : GradedObject I C` and `p : I → J`, `X.mapObj p` is the graded object by `J`
which in degree `j` consists of the coproduct of the `X i` such that `p i = j`. -/
/-
**CategoryTheory.GradedObject.mapObj** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.G
radedObject`。
形式化陈述：mapObj : GradedObject J C
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given `X : GradedObject I C` and `p : I → J`, `X.mapObj p` is the graded object 
by `J`
which in degree `j` consists of the coproduct of the `X i` such that `p i = j`.
-/
noncomputable def mapObj : GradedObject J C := fun j => ∐ (X.mapObjFun p j)

/-- The canonical inclusion `X i ⟶ X.mapObj p j` when `i : I` and `j : J` are such
that `p i = j`. -/
/-
**CategoryTheory.GradedObject.** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.GradedO
bject`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The canonical inclusion `X i ⟶ X.mapObj p j` when `i : I` and `j : J` are such
that `p i = j`.
-/
noncomputable def ιMapObj (i : I) (j : J) (hij : p i = j) : X i ⟶ X.mapObj p j :=
  Sigma.ι (X.mapObjFun p j) ⟨i, hij⟩

/-- Given `X : GradedObject I C`, `p : I → J` and `j : J`,
`CofanMapObjFun X p j` is the type `Cofan (X.mapObjFun p j)`. The point object of
such colimits cofans are isomorphic to `X.mapObj p j`, see `CofanMapObjFun.iso`. -/
/-
**CategoryTheory.GradedObject.CofanMapObjFun** 是 Mathlib 中的一个缩写定义，位于命名空间 `Catego
ryTheory.GradedObject`。
形式化陈述：CofanMapObjFun (j : J) : Type _
参数：j : J。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given `X : GradedObject I C`, `p : I → J` and `j : J`,
`CofanMapObjFun X p j` is the type `Cofan (X.mapObjFun p j)`. The point object o
f
such colimits cofans are isomorphic to `X.mapObj p j`, see `CofanMapObjFun.iso`.
-/
abbrev CofanMapObjFun (j : J) : Type _ := Cofan (X.mapObjFun p j)

-- in order to use the cofan API, some definitions below
-- have a `simp` attribute rather than `simps`
/-- Constructor for `CofanMapObjFun X p j`. -/
@[simp]
/-
**CategoryTheory.GradedObject.CofanMapObjFun.mk** 是 Mathlib 中的一个定义，位于命名空间 `Categ
oryTheory.GradedObject.CofanMapObjFun`。
形式化陈述：{I : Type u_1} →   {J : Type u_2} →     {C : Type u_4} →       [inst : Cat
egoryTheory.Category.{v_1, u_4} C] →         (X : CategoryTheory.GradedObject I 
C) →           (p : I → J) → (j : J) → (pt : C) → ((i : I) → p i = j → (X i ⟶ pt
)) → X.CofanMapObjFun p j
参数：X : CategoryTheory.GradedObject I C；p : I → J；j : J；pt : C；(i : I) → p i = j 
→ (X i ⟶ pt)。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Constructor for `CofanMapObjFun X p j`.
-/
def CofanMapObjFun.mk (j : J) (pt : C) (ι' : ∀ (i : I) (_ : p i = j), X i ⟶ pt) :
    CofanMapObjFun X p j :=
  Cofan.mk pt (fun ⟨i, hi⟩ => ι' i hi)

/-- The tautological cofan corresponding to the coproduct decomposition of `X.mapObj p j`. -/
@[simp]
/-
**CategoryTheory.GradedObject.cofanMapObj** 是 Mathlib 中的一个定义，位于命名空间 `CategoryThe
ory.GradedObject`。
形式化陈述：cofanMapObj (j : J) : CofanMapObjFun X p j
参数：j : J。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The tautological cofan corresponding to the coproduct decomposition of `X.mapObj
 p j`.
-/
noncomputable def cofanMapObj (j : J) : CofanMapObjFun X p j :=
  CofanMapObjFun.mk X p j (X.mapObj p j) (fun i hi => X.ιMapObj p i j hi)

/-- Given `X : GradedObject I C`, `p : I → J` and `j : J`, `X.mapObj p j` satisfies
the universal property of the coproduct of those `X i` such that `p i = j`. -/
/-
**CategoryTheory.GradedObject.isColimitCofanMapObj** 是 Mathlib 中的一个定义，位于命名空间 `Ca
tegoryTheory.GradedObject`。
形式化陈述：isColimitCofanMapObj (j : J) : IsColimit (X.cofanMapObj p j)
参数：j : J。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given `X : GradedObject I C`, `p : I → J` and `j : J`, `X.mapObj p j` satisfies
the universal property of the coproduct of those `X i` such that `p i = j`.
-/
noncomputable def isColimitCofanMapObj (j : J) : IsColimit (X.cofanMapObj p j) :=
  colimit.isColimit _

@[ext]
/-
**CategoryTheory.GradedObject.mapObj_ext** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheo
ry.GradedObject`。
形式化陈述：mapObj_ext {A : C} {j : J} (f g : X.mapObj p j ⟶ A) (hfg : forall (i : I) 
(hij : p i = j), X.ιMapObj p i j hij ≫ f = X.ιMapObj p i j hij ≫ g) : f = g
参数：f g : X.mapObj p j ⟶ A；hfg : forall (i : I) (hij : p i = j), X.ιMapObj p i j 
hij ≫ f = X.ιMapObj p i j hij ≫ g。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.Cofan.IsColimit.hom_ext`：∀ {C : Type u} [inst : Ca
tegoryTheory.Category.{v, u} C] {I : Type u_1} {F : I → C} {c : CategoryTheory.L
imits.Cofan F}   (hc : CategoryTheo…
-/
lemma mapObj_ext {A : C} {j : J} (f g : X.mapObj p j ⟶ A)
    (hfg : ∀ (i : I) (hij : p i = j), X.ιMapObj p i j hij ≫ f = X.ιMapObj p i j hij ≫ g) :
    f = g :=
  Cofan.IsColimit.hom_ext (X.isColimitCofanMapObj p j) _ _ (fun ⟨i, hij⟩ => hfg i hij)

/-- This is the morphism `X.mapObj p j ⟶ A` constructed from a family of
morphisms `X i ⟶ A` for all `i : I` such that `p i = j`. -/
/-
**CategoryTheory.GradedObject.descMapObj** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheo
ry.GradedObject`。
形式化陈述：descMapObj {A : C} {j : J} (φ : forall (i : I) (_ : p i = j), X i ⟶ A) : X
.mapObj p j ⟶ A
参数：φ : forall (i : I) (_ : p i = j), X i ⟶ A。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
This is the morphism `X.mapObj p j ⟶ A` constructed from a family of
morphisms `X i ⟶ A` for all `i : I` such that `p i = j`.
-/
noncomputable def descMapObj {A : C} {j : J} (φ : ∀ (i : I) (_ : p i = j), X i ⟶ A) :
    X.mapObj p j ⟶ A :=
  Cofan.IsColimit.desc (X.isColimitCofanMapObj p j) (fun ⟨i, hi⟩ => φ i hi)

@[reassoc (attr := simp)]
/-
**CategoryTheory.GradedObject.** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.GradedO
bject`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma ι_descMapObj {A : C} {j : J}
    (φ : ∀ (i : I) (_ : p i = j), X i ⟶ A) (i : I) (hi : p i = j) :
    X.ιMapObj p i j hi ≫ X.descMapObj p φ = φ i hi := by
  apply Cofan.IsColimit.fac

end
namespace CofanMapObjFun

/-
**CategoryTheory.GradedObject.CofanMapObjFun.hasMap** 是 Mathlib 中的一个引理，位于命名空间 `C
ategoryTheory.GradedObject.CofanMapObjFun`。
形式化陈述：hasMap (c : forall j, CofanMapObjFun X p j) (hc : forall j, IsColimit (c j
)) : X.HasMap p
参数：c : forall j, CofanMapObjFun X p j；hc : forall j, IsColimit (c j)。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma hasMap (c : ∀ j, CofanMapObjFun X p j) (hc : ∀ j, IsColimit (c j)) :
    X.HasMap p := fun j => ⟨_, hc j⟩

variable {j X p}
variable [X.HasMap p]
variable {c : CofanMapObjFun X p j} (hc : IsColimit c)

/-- If `c : CofanMapObjFun X p j` is a colimit cofan, this is the induced
isomorphism `c.pt ≅ X.mapObj p j`. -/
/-
**CategoryTheory.GradedObject.CofanMapObjFun.iso** 是 Mathlib 中的一个定义，位于命名空间 `Cate
goryTheory.GradedObject.CofanMapObjFun`。
形式化陈述：iso : c.pt ≅ X.mapObj p j
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `c : CofanMapObjFun X p j` is a colimit cofan, this is the induced
isomorphism `c.pt ≅ X.mapObj p j`.
-/
noncomputable def iso : c.pt ≅ X.mapObj p j :=
  IsColimit.coconePointUniqueUpToIso hc (X.isColimitCofanMapObj p j)

@[reassoc (attr := simp)]
/-
**CategoryTheory.GradedObject.CofanMapObjFun.inj_iso_hom** 是 Mathlib 中的一个引理，位于命名
空间 `CategoryTheory.GradedObject.CofanMapObjFun`。
形式化陈述：inj_iso_hom (i : I) (hi : p i = j) : c.inj ⟨i, hi⟩ ≫ (c.iso hc).hom = X.ιM
apObj p i j hi
参数：i : I；hi : p i = j。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.IsColimit.comp_coconePointUniqueUpToIso_hom`：∀ {J 
: Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} J] {C : Type u₃} [inst_1 : C
ategoryTheory.Category.{v₃, u₃} C]   {F : CategoryTheor…
-/
lemma inj_iso_hom (i : I) (hi : p i = j) :
    c.inj ⟨i, hi⟩ ≫ (c.iso hc).hom = X.ιMapObj p i j hi := by
  apply IsColimit.comp_coconePointUniqueUpToIso_hom

@[reassoc (attr := simp)]
/-
**CategoryTheory.GradedObject.CofanMapObjFun.** 是 Mathlib 中的一个引理，位于命名空间 `Categor
yTheory.GradedObject.CofanMapObjFun`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma ιMapObj_iso_inv (i : I) (hi : p i = j) :
    X.ιMapObj p i j hi ≫ (c.iso hc).inv = c.inj ⟨i, hi⟩ := by
  apply IsColimit.comp_coconePointUniqueUpToIso_inv

end CofanMapObjFun

variable {X Y}
variable [X.HasMap p] [Y.HasMap p]

/-- The canonical morphism of `J`-graded objects `X.mapObj p ⟶ Y.mapObj p` induced by
a morphism `X ⟶ Y` of `I`-graded objects and a map `p : I → J`. -/
/-
**CategoryTheory.GradedObject.mapMap** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.G
radedObject`。
形式化陈述：mapMap : X.mapObj p ⟶ Y.mapObj p
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The canonical morphism of `J`-graded objects `X.mapObj p ⟶ Y.mapObj p` induced b
y
a morphism `X ⟶ Y` of `I`-graded objects and a map `p : I → J`.
-/
noncomputable def mapMap : X.mapObj p ⟶ Y.mapObj p := fun j =>
  X.descMapObj p (fun i hi => φ i ≫ Y.ιMapObj p i j hi)

@[reassoc (attr := simp)]
/-
**CategoryTheory.GradedObject.** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.GradedO
bject`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma ι_mapMap (i : I) (j : J) (hij : p i = j) :
    X.ιMapObj p i j hij ≫ mapMap φ p j = φ i ≫ Y.ιMapObj p i j hij := by
  simp only [mapMap, ι_descMapObj]
/-
**CategoryTheory.GradedObject.congr_mapMap** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTh
eory.GradedObject`。
形式化陈述：congr_mapMap (φ₁ φ₂ : X ⟶ Y) (h : φ₁ = φ₂) : mapMap φ₁ p = mapMap φ₂ p
参数：φ₁ φ₂ : X ⟶ Y；h : φ₁ = φ₂。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma congr_mapMap (φ₁ φ₂ : X ⟶ Y) (h : φ₁ = φ₂) : mapMap φ₁ p = mapMap φ₂ p := by
  subst h
  rfl

variable (X)

set_option backward.isDefEq.respectTransparency.types false in
@[simp]
/-
**CategoryTheory.GradedObject.mapMap_id** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheor
y.GradedObject`。
形式化陈述：mapMap_id : mapMap (𝟙 X) p = 𝟙 _
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.GradedObject.hom_ext`：hom_ext {β : Type*} {X Y : GradedOb
ject β C} (f g : X ⟶ Y) (h : forall x, f x = g x) : f = g
· 使用引理 `CategoryTheory.GradedObject.mapObj_ext`：mapObj_ext {A : C} {j : J} (f g 
: X.mapObj p j ⟶ A) (hfg : forall (i : I) (hij : p i = j), X.ιMapObj p i j hij ≫
 f = X.ιMapObj p i j hij ≫ g…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `CategoryTheory.GradedObject.ι_mapMap`：ι_mapMap (i : I) (j : J) (hij : p 
i = j) : X.ιMapObj p i j hij ≫ mapMap φ p j = φ i ≫ Y.ιMapObj p i j hij
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma mapMap_id : mapMap (𝟙 X) p = 𝟙 _ := by cat_disch

variable {X Z}

set_option backward.isDefEq.respectTransparency.types false in
@[simp, reassoc]
/-
**CategoryTheory.GradedObject.mapMap_comp** 是 Mathlib 中的一个引理，位于命名空间 `CategoryThe
ory.GradedObject`。
形式化陈述：mapMap_comp [Z.HasMap p] : mapMap (φ ≫ ψ) p = mapMap φ p ≫ mapMap ψ p
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.GradedObject.hom_ext`：hom_ext {β : Type*} {X Y : GradedOb
ject β C} (f g : X ⟶ Y) (h : forall x, f x = g x) : f = g
· 使用引理 `CategoryTheory.GradedObject.mapObj_ext`：mapObj_ext {A : C} {j : J} (f g 
: X.mapObj p j ⟶ A) (hfg : forall (i : I) (hij : p i = j), X.ιMapObj p i j hij ≫
 f = X.ιMapObj p i j hij ≫ g…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `CategoryTheory.GradedObject.ι_mapMap`：ι_mapMap (i : I) (j : J) (hij : p 
i = j) : X.ιMapObj p i j hij ≫ mapMap φ p j = φ i ≫ Y.ιMapObj p i j hij
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.GradedObject.ι_mapMap_assoc`：∀ {I : Type u_1} {J : Type u
_2} {C : Type u_4} [inst : CategoryTheory.Category.{v_1, u_4} C]   {X Y : Catego
ryTheory.GradedObject I C} (φ : …
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma mapMap_comp [Z.HasMap p] : mapMap (φ ≫ ψ) p = mapMap φ p ≫ mapMap ψ p := by cat_disch

set_option backward.isDefEq.respectTransparency.types false in
/-- The isomorphism of `J`-graded objects `X.mapObj p ≅ Y.mapObj p` induced by an
isomorphism `X ≅ Y` of graded objects and a map `p : I → J`. -/
@[simps]
/-
**CategoryTheory.GradedObject.mapIso** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.G
radedObject`。
形式化陈述：mapIso : X.mapObj p ≅ Y.mapObj p where hom
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The isomorphism of `J`-graded objects `X.mapObj p ≅ Y.mapObj p` induced by an
isomorphism `X ≅ Y` of graded objects and a map `p : I → J`.
-/
noncomputable def mapIso : X.mapObj p ≅ Y.mapObj p where
  hom := mapMap e.hom p
  inv := mapMap e.inv p

variable (C)

/-- Given a map `p : I → J`, this is the functor `GradedObject I C ⥤ GradedObject J C` which
sends an `I`-object `X` to the graded object `X.mapObj p` which in degree `j : J` is given
by the coproduct of those `X i` such that `p i = j`. -/
@[simps]
/-
**CategoryTheory.GradedObject.map** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Grad
edObject`。
形式化陈述：map [forall (j : J), HasColimitsOfShape (Discrete (p ⁻¹' {j})) C] : Graded
Object I C ⥤ GradedObject J C where obj X
参数：j : J；Discrete (p ⁻¹' {j})。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given a map `p : I → J`, this is the functor `GradedObject I C ⥤ GradedObject J 
C` which
sends an `I`-object `X` to the graded object `X.mapObj p` which in degree `j : J
` is given
by the coproduct of those `X i` such that `p i = j`.
-/
noncomputable def map [∀ (j : J), HasColimitsOfShape (Discrete (p ⁻¹' {j})) C] :
    GradedObject I C ⥤ GradedObject J C where
  obj X := X.mapObj p
  map φ := mapMap φ p

variable {C} (X Y)
variable (q : J → K) (r : I → K) (hpqr : ∀ i, q (p i) = r i)

section

variable (k : K) (c : ∀ (j : J), q j = k → X.CofanMapObjFun p j)
  (hc : ∀ j hj, IsColimit (c j hj))
  (c' : Cofan (fun (j : q ⁻¹' {k}) => (c j.1 j.2).pt)) (hc' : IsColimit c')

/-- Given maps `p : I → J`, `q : J → K` and `r : I → K` such that `q.comp p = r`,
`X : GradedObject I C`, `k : K`, the datum of cofans `X.CofanMapObjFun p j` for all
`j : J` and of a cofan for all the points of these cofans, this is a cofan of
type `X.CofanMapObjFun r k`, which is a colimit (see `isColimitCofanMapObjComp`) if the
given cofans are. -/
@[simp]
/-
**CategoryTheory.GradedObject.cofanMapObjComp** 是 Mathlib 中的一个定义，位于命名空间 `Categor
yTheory.GradedObject`。
形式化陈述：cofanMapObjComp : X.CofanMapObjFun r k
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given maps `p : I → J`, `q : J → K` and `r : I → K` such that `q.comp p = r`,
`X : GradedObject I C`, `k : K`, the datum of cofans `X.CofanMapObjFun p j` for 
all
`j : J` and of a cofan for all the points of these cofans, this is a cofan of
type `X.CofanMapObjFun r k`, which is a colimit (see `isColimitCofanMapObjComp`)
 if the
given cofans are.
-/
def cofanMapObjComp : X.CofanMapObjFun r k :=
  CofanMapObjFun.mk _ _ _ c'.pt (fun i hi =>
    (c (p i) (by rw [hpqr, hi])).inj ⟨i, rfl⟩ ≫ c'.inj (⟨p i, by
      rw [Set.mem_preimage, Set.mem_singleton_iff, hpqr, hi]⟩))

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- Given maps `p : I → J`, `q : J → K` and `r : I → K` such that `q.comp p = r`,
`X : GradedObject I C`, `k : K`, the cofan constructed by `cofanMapObjComp` is a colimit.
In other words, if we have, for all `j : J` such that `hj : q j = k`,
a colimit cofan `c j hj` which computes the coproduct of the `X i` such that `p i = j`,
and also a colimit cofan which computes the coproduct of the points of these `c j hj`, then
the point of this latter cofan computes the coproduct of the `X i` such that `r i = k`. -/
@[simp]
/-
**CategoryTheory.GradedObject.isColimitCofanMapObjComp** 是 Mathlib 中的一个定义，位于命名空间
 `CategoryTheory.GradedObject`。
形式化陈述：isColimitCofanMapObjComp : IsColimit (cofanMapObjComp X p q r hpqr k c c')
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given maps `p : I → J`, `q : J → K` and `r : I → K` such that `q.comp p = r`,
`X : GradedObject I C`, `k : K`, the cofan constructed by `cofanMapObjComp` is a
 colimit.
In other words, if we have, for all `j : J` such that `hj : q j = k`,
a colimit cofan `c j hj` which computes the coproduct of the `X i` such that `p 
i = j`,
and also a colimit cofan which computes the coproduct of the points of these `c 
j hj`, then
the point of this latter cofan computes the coproduct of the `X i` such that `r 
i = k`.
-/
def isColimitCofanMapObjComp :
    IsColimit (cofanMapObjComp X p q r hpqr k c c') :=
  Cofan.IsColimit.mk _
    (fun s => Cofan.IsColimit.desc hc'
      (fun ⟨j, (hj : q j = k)⟩ => Cofan.IsColimit.desc (hc j hj)
        (fun ⟨i, (hi : p i = j)⟩ => s.inj ⟨i, by
          simp only [Set.mem_preimage, Set.mem_singleton_iff, ← hpqr, hi, hj]⟩)))
    (fun s ⟨i, (hi : r i = k)⟩ => by simp)
    (fun s m hm => by
      apply Cofan.IsColimit.hom_ext hc'
      rintro ⟨j, rfl : q j = k⟩
      apply Cofan.IsColimit.hom_ext (hc j rfl)
      rintro ⟨i, rfl : p i = j⟩
      dsimp
      rw [Cofan.IsColimit.fac, Cofan.IsColimit.fac, ← hm]
      dsimp
      rw [assoc])

include hpqr in
/-
**CategoryTheory.GradedObject.hasMap_comp** 是 Mathlib 中的一个引理，位于命名空间 `CategoryThe
ory.GradedObject`。
形式化陈述：hasMap_comp [(X.mapObj p).HasMap q] : X.HasMap r
参数：X.mapObj p。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma hasMap_comp [(X.mapObj p).HasMap q] : X.HasMap r :=
  fun k => ⟨_, isColimitCofanMapObjComp X p q r hpqr k _
    (fun j _ => X.isColimitCofanMapObj p j) _ ((X.mapObj p).isColimitCofanMapObj q k)⟩

end

variable [HasZeroMorphisms C] [DecidableEq J] (i : I) (j : J)

/-- The canonical inclusion `X i ⟶ X.mapObj p j` when `p i = j`, the zero morphism otherwise. -/
/-
**CategoryTheory.GradedObject.** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.GradedO
bject`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The canonical inclusion `X i ⟶ X.mapObj p j` when `p i = j`, the zero morphism o
therwise.
-/
noncomputable def ιMapObjOrZero : X i ⟶ X.mapObj p j :=
  if h : p i = j
    then X.ιMapObj p i j h
    else 0
/-
**CategoryTheory.GradedObject.** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.GradedO
bject`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma ιMapObjOrZero_eq (h : p i = j) : X.ιMapObjOrZero p i j = X.ιMapObj p i j h := dif_pos h
/-
**CategoryTheory.GradedObject.** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.GradedO
bject`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma ιMapObjOrZero_eq_zero (h : p i ≠ j) : X.ιMapObjOrZero p i j = 0 := dif_neg h

variable {X Y} in
@[reassoc (attr := simp)]
/-
**CategoryTheory.GradedObject.** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.GradedO
bject`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma ιMapObjOrZero_mapMap :
    X.ιMapObjOrZero p i j ≫ mapMap φ p j = φ i ≫ Y.ιMapObjOrZero p i j := by
  by_cases h : p i = j
  · simp only [ιMapObjOrZero_eq _ _ _ _ h, ι_mapMap]
  · simp only [ιMapObjOrZero_eq_zero _ _ _ _ h, zero_comp, comp_zero]

end GradedObject

end CategoryTheory

