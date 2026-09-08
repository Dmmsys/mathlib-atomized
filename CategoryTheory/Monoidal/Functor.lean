/-
Copyright (c) 2018 Michael Jendrusch. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Jendrusch, Kim Morrison, Bhavik Mehta
-/
module

public import Mathlib.CategoryTheory.Monoidal.Category
public import Mathlib.CategoryTheory.Adjunction.FullyFaithful

/-!
# (Lax) monoidal functors

A lax monoidal functor `F` between monoidal categories `C` and `D`
is a functor between the underlying categories equipped with morphisms
* `ε : 𝟙_ D ⟶ F.obj (𝟙_ C)` (called the unit morphism)
* `μ X Y : (F.obj X) ⊗ (F.obj Y) ⟶ F.obj (X ⊗ Y)` (called the tensorator, or strength).

satisfying various axioms. This is implemented as a typeclass `F.LaxMonoidal`.

Similarly, we define the typeclass `F.OplaxMonoidal`. For these oplax monoidal functors,
we have similar data `η` and `δ`, but with morphisms in the opposite direction.

A monoidal functor (`F.Monoidal`) is defined here as the combination of `F.LaxMonoidal`
and `F.OplaxMonoidal`, with the additional conditions that `ε`/`η` and `μ`/`δ` are
inverse isomorphisms.

We show that the composition of (lax) monoidal functors gives a (lax) monoidal functor.

See `Mathlib/CategoryTheory/Monoidal/NaturalTransformation.lean` for monoidal natural
transformations.

We show in `Mathlib.CategoryTheory.Monoidal.Mon_` that lax monoidal functors take monoid objects
to monoid objects.

## References

See <https://stacks.math.columbia.edu/tag/0FFL>.
-/

@[expose] public section


universe v₁ v₂ v₃ v₁' u₁ u₂ u₃ u₁'

namespace CategoryTheory

open Category CategoryTheory.Functor MonoidalCategory

variable {C : Type u₁} [Category.{v₁} C] [MonoidalCategory.{v₁} C]
  {D : Type u₂} [Category.{v₂} D] [MonoidalCategory.{v₂} D]
  {E : Type u₃} [Category.{v₃} E] [MonoidalCategory.{v₃} E]
  {C' : Type u₁'} [Category.{v₁'} C']

namespace Functor

-- The direction of `left_unitality` and `right_unitality` as simp lemmas may look strange:
-- remember the rule of thumb that component indices of natural transformations
-- "weigh more" than structural maps.
-- (However by this argument `associativity` is currently stated backwards!)
/-- A functor `F : C ⥤ D` between monoidal categories is lax monoidal if it is
equipped with morphisms `ε : 𝟙_ D ⟶ F.obj (𝟙_ C)` and `μ X Y : F.obj X ⊗ F.obj Y ⟶ F.obj (X ⊗ Y)`,
satisfying the appropriate coherences. -/
@[ext]
/-
**CategoryTheory.Functor.LaxMonoidal** 是 Mathlib 中的一个类，位于命名空间 `CategoryTheory.Fu
nctor`。
形式化陈述：LaxMonoidal (F : C ⥤ D) where /-- the unit morphism of a lax monoidal func
tor -/ ε (F) : 𝟙_ D ⟶ F.obj (𝟙_ C) /-- the tensorator of a lax monoidal functor 
-/ μ (F) : forall X Y : C, F.obj X otimes F.obj Y ⟶ F.obj (X otimes Y) μ_natural
_left (F) : forall {X Y : C} (f : X ⟶ Y) (X' : C), F.map f ▷ F.obj X' ≫ μ Y X' =
 μ X X' ≫ F.map (f ▷ X')
参数：F : C ⥤ D；F。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A functor `F : C ⥤ D` between monoidal categories is lax monoidal if it is
equipped with morphisms `ε : 𝟙_ D ⟶ F.obj (𝟙_ C)` and `μ X Y : F.obj X ⊗ F.obj Y
 ⟶ F.obj (X ⊗ Y)`,
satisfying the appropriate coherences.
-/
class LaxMonoidal (F : C ⥤ D) where
  /-- the unit morphism of a lax monoidal functor -/
  ε (F) : 𝟙_ D ⟶ F.obj (𝟙_ C)
  /-- the tensorator of a lax monoidal functor -/
  μ (F) : ∀ X Y : C, F.obj X ⊗ F.obj Y ⟶ F.obj (X ⊗ Y)
  μ_natural_left (F) :
    ∀ {X Y : C} (f : X ⟶ Y) (X' : C),
      F.map f ▷ F.obj X' ≫ μ Y X' = μ X X' ≫ F.map (f ▷ X') := by
    cat_disch
  μ_natural_right (F) :
    ∀ {X Y : C} (X' : C) (f : X ⟶ Y),
      F.obj X' ◁ F.map f ≫ μ X' Y = μ X' X ≫ F.map (X' ◁ f) := by
    cat_disch
  /-- associativity of the tensorator -/
  associativity (F) :
    ∀ X Y Z : C,
      μ X Y ▷ F.obj Z ≫ μ (X ⊗ Y) Z ≫ F.map (α_ X Y Z).hom =
        (α_ (F.obj X) (F.obj Y) (F.obj Z)).hom ≫ F.obj X ◁ μ Y Z ≫ μ X (Y ⊗ Z) := by
    cat_disch
  -- unitality
  left_unitality (F) :
    ∀ X : C, (λ_ (F.obj X)).hom = ε ▷ F.obj X ≫ μ (𝟙_ C) X ≫ F.map (λ_ X).hom := by
      cat_disch
  right_unitality (F) :
    ∀ X : C, (ρ_ (F.obj X)).hom = F.obj X ◁ ε ≫ μ X (𝟙_ C) ≫ F.map (ρ_ X).hom := by
    cat_disch

namespace LaxMonoidal

attribute [reassoc (attr := simp)] μ_natural_left μ_natural_right
  associativity

attribute [simp, reassoc] right_unitality left_unitality

section

variable (F : C ⥤ D) [F.LaxMonoidal]

@[reassoc (attr := simp)]
/-
**CategoryTheory.Functor.LaxMonoidal.** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.
Functor.LaxMonoidal`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem μ_natural {X Y X' Y' : C} (f : X ⟶ Y) (g : X' ⟶ Y') :
    (F.map f ⊗ₘ F.map g) ≫ μ F Y Y' = μ F X X' ≫ F.map (f ⊗ₘ g) := by
  simp [tensorHom_def]

@[reassoc (attr := simp)]
/-
**CategoryTheory.Functor.LaxMonoidal.left_unitality_inv** 是 Mathlib 中的一个定理，位于命名空
间 `CategoryTheory.Functor.LaxMonoidal`。
形式化陈述：left_unitality_inv (X : C) : (fun_ (F.obj X)).inv ≫ ε F ▷ F.obj X ≫ μ F (𝟙
_ C) X = F.map (fun_ X).inv
参数：X : C。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Iso.inv_comp_eq`：inv_comp_eq (α : X ≅ Y) {f : X ⟶ Z} {g :
 Y ⟶ Z} : α.inv ≫ f = g ↔ f = α.hom ≫ g
· 使用定理 `CategoryTheory.Functor.LaxMonoidal.left_unitality`：∀ {C : Type u₁} {inst
 : CategoryTheory.Category.{v₁, u₁} C} {inst_1 : CategoryTheory.MonoidalCategory
 C} {D : Type u₂}   {inst_2 : CategoryT…
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.Functor.map_comp`：∀ {C : Type u₁} [inst : CategoryTheory.
Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]
   (self : CategoryTh…
· 使用定理 `CategoryTheory.Iso.hom_inv_id`：∀ {C : Type u} [inst : CategoryTheory.Cat
egory.{v, u} C] {X Y : C} (self : X ≅ Y),   CategoryTheory.CategoryStruct.comp s
elf.hom self.inv = …
· 使用定理 `CategoryTheory.Functor.map_id`：∀ {C : Type u₁} [inst : CategoryTheory.Ca
tegory.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]  
 (self : CategoryTh…
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
-/
theorem left_unitality_inv (X : C) :
    (λ_ (F.obj X)).inv ≫ ε F ▷ F.obj X ≫ μ F (𝟙_ C) X = F.map (λ_ X).inv := by
  rw [Iso.inv_comp_eq, left_unitality, Category.assoc, Category.assoc, ← F.map_comp,
    Iso.hom_inv_id, F.map_id, comp_id]

@[reassoc (attr := simp)]
/-
**CategoryTheory.Functor.LaxMonoidal.right_unitality_inv** 是 Mathlib 中的一个定理，位于命名
空间 `CategoryTheory.Functor.LaxMonoidal`。
形式化陈述：right_unitality_inv (X : C) : (ρ_ (F.obj X)).inv ≫ F.obj X ◁ ε F ≫ μ F X (
𝟙_ C) = F.map (ρ_ X).inv
参数：X : C。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Iso.inv_comp_eq`：inv_comp_eq (α : X ≅ Y) {f : X ⟶ Z} {g :
 Y ⟶ Z} : α.inv ≫ f = g ↔ f = α.hom ≫ g
· 使用定理 `CategoryTheory.Functor.LaxMonoidal.right_unitality`：∀ {C : Type u₁} {ins
t : CategoryTheory.Category.{v₁, u₁} C} {inst_1 : CategoryTheory.MonoidalCategor
y C} {D : Type u₂}   {inst_2 : CategoryT…
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.Functor.map_comp`：∀ {C : Type u₁} [inst : CategoryTheory.
Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]
   (self : CategoryTh…
· 使用定理 `CategoryTheory.Iso.hom_inv_id`：∀ {C : Type u} [inst : CategoryTheory.Cat
egory.{v, u} C] {X Y : C} (self : X ≅ Y),   CategoryTheory.CategoryStruct.comp s
elf.hom self.inv = …
· 使用定理 `CategoryTheory.Functor.map_id`：∀ {C : Type u₁} [inst : CategoryTheory.Ca
tegory.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]  
 (self : CategoryTh…
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
-/
theorem right_unitality_inv (X : C) :
    (ρ_ (F.obj X)).inv ≫ F.obj X ◁ ε F ≫ μ F X (𝟙_ C) = F.map (ρ_ X).inv := by
  rw [Iso.inv_comp_eq, right_unitality, Category.assoc, Category.assoc, ← F.map_comp,
    Iso.hom_inv_id, F.map_id, comp_id]

@[reassoc (attr := simp)]
/-
**CategoryTheory.Functor.LaxMonoidal.associativity_inv** 是 Mathlib 中的一个定理，位于命名空间
 `CategoryTheory.Functor.LaxMonoidal`。
形式化陈述：associativity_inv (X Y Z : C) : F.obj X ◁ μ F Y Z ≫ μ F X (Y otimes Z) ≫ F
.map (α_ X Y Z).inv = (α_ (F.obj X) (F.obj Y) (F.obj Z)).inv ≫ μ F X Y ▷ F.obj Z
 ≫ μ F (X otimes Y) Z
参数：X Y Z : C。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Iso.eq_inv_comp`：eq_inv_comp (α : X ≅ Y) {f : X ⟶ Z} {g :
 Y ⟶ Z} : g = α.inv ≫ f ↔ α.hom ≫ g = f
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.Functor.LaxMonoidal.associativity_assoc`：∀ {C : Type u₁} 
{inst : CategoryTheory.Category.{v₁, u₁} C} {inst_1 : CategoryTheory.MonoidalCat
egory C} {D : Type u₂}   {inst_2 : CategoryT…
· 使用定理 `CategoryTheory.Functor.map_comp`：∀ {C : Type u₁} [inst : CategoryTheory.
Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]
   (self : CategoryTh…
· 使用定理 `CategoryTheory.Iso.hom_inv_id`：∀ {C : Type u} [inst : CategoryTheory.Cat
egory.{v, u} C] {X Y : C} (self : X ≅ Y),   CategoryTheory.CategoryStruct.comp s
elf.hom self.inv = …
· 使用定理 `CategoryTheory.Functor.map_id`：∀ {C : Type u₁} [inst : CategoryTheory.Ca
tegory.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]  
 (self : CategoryTh…
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
-/
theorem associativity_inv (X Y Z : C) :
    F.obj X ◁ μ F Y Z ≫ μ F X (Y ⊗ Z) ≫ F.map (α_ X Y Z).inv =
      (α_ (F.obj X) (F.obj Y) (F.obj Z)).inv ≫ μ F X Y ▷ F.obj Z ≫ μ F (X ⊗ Y) Z := by
  rw [Iso.eq_inv_comp, ← associativity_assoc, ← F.map_comp, Iso.hom_inv_id,
    F.map_id, comp_id]

@[reassoc]
/-
**CategoryTheory.Functor.LaxMonoidal.** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.
Functor.LaxMonoidal`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma ε_tensorHom_comp_μ {X : C} {Y : D} (f : Y ⟶ F.obj X) :
    (ε F ⊗ₘ f) ≫ μ F (𝟙_ C) X = 𝟙_ D ◁ f ≫ (λ_ (F.obj X)).hom ≫ F.map (λ_ X).inv := by
  simp [tensorHom_def']

@[reassoc]
/-
**CategoryTheory.Functor.LaxMonoidal.tensorHom_** 是 Mathlib 中的一个引理，位于命名空间 `Categ
oryTheory.Functor.LaxMonoidal`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma tensorHom_ε_comp_μ {X : C} {Y : D} (f : Y ⟶ F.obj X) :
    (f ⊗ₘ ε F) ≫ μ F X (𝟙_ C) = f ▷ 𝟙_ D ≫ (ρ_ (F.obj X)).hom ≫ F.map (ρ_ X).inv := by
  simp [tensorHom_def]

@[reassoc]
/-
**CategoryTheory.Functor.LaxMonoidal.tensorUnit_whiskerLeft_comp_leftUnitor_hom*
* 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.Functor.LaxMonoidal`。
形式化陈述：tensorUnit_whiskerLeft_comp_leftUnitor_hom {X : C} {Y : D} (f : Y ⟶ F.obj 
X) : 𝟙_ D ◁ f ≫ (fun_ (F.obj X)).hom = (ε F otimesₘ f) ≫ μ F (𝟙_ C) X ≫ F.map (f
un_ X).hom
参数：f : Y ⟶ F.obj X。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.MonoidalCategory.id_whiskerLeft`：id_whiskerLeft {X Y : C}
 (f : X ⟶ Y) : 𝟙_ C ◁ f = (fun_ X).hom ≫ f ≫ (fun_ Y).inv
· 使用定理 `CategoryTheory.Functor.LaxMonoidal.left_unitality`：∀ {C : Type u₁} {inst
 : CategoryTheory.Category.{v₁, u₁} C} {inst_1 : CategoryTheory.MonoidalCategory
 C} {D : Type u₂}   {inst_2 : CategoryT…
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.Functor.LaxMonoidal.left_unitality_inv_assoc`：∀ {C : Type
 u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] [inst_1 : CategoryTheory.Monoid
alCategory C] {D : Type u₂}   [inst_2 : CategoryT…
· 使用引理 `CategoryTheory.Iso.map_inv_hom_id`：map_inv_hom_id (F : C ⥤ D) : F.map e.
inv ≫ F.map e.hom = 𝟙 _
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CategoryTheory.MonoidalCategory.tensorHom_def'`：tensorHom_def' {X₁ Y₁ X₂
 Y₂ : C} (f : X₁ ⟶ Y₁) (g : X₂ ⟶ Y₂) : f otimesₘ g = X₁ ◁ g ≫ f ▷ Y₂
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma tensorUnit_whiskerLeft_comp_leftUnitor_hom {X : C} {Y : D} (f : Y ⟶ F.obj X) :
    𝟙_ D ◁ f ≫ (λ_ (F.obj X)).hom = (ε F ⊗ₘ f) ≫ μ F (𝟙_ C) X ≫ F.map (λ_ X).hom := by
  simp [tensorHom_def']

@[reassoc]
/-
**CategoryTheory.Functor.LaxMonoidal.whiskerRight_tensorUnit_comp_rightUnitor_ho
m** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.Functor.LaxMonoidal`。
形式化陈述：whiskerRight_tensorUnit_comp_rightUnitor_hom {X : C} {Y : D} (f : Y ⟶ F.ob
j X) : f ▷ 𝟙_ D ≫ (ρ_ (F.obj X)).hom = (f otimesₘ ε F) ≫ μ F X (𝟙_ C) ≫ F.map (ρ
_ X).hom
参数：f : Y ⟶ F.obj X。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.MonoidalCategory.whiskerRight_id`：whiskerRight_id {X Y : 
C} (f : X ⟶ Y) : f ▷ 𝟙_ C = (ρ_ X).hom ≫ f ≫ (ρ_ Y).inv
· 使用定理 `CategoryTheory.Functor.LaxMonoidal.right_unitality`：∀ {C : Type u₁} {ins
t : CategoryTheory.Category.{v₁, u₁} C} {inst_1 : CategoryTheory.MonoidalCategor
y C} {D : Type u₂}   {inst_2 : CategoryT…
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.Functor.LaxMonoidal.right_unitality_inv_assoc`：∀ {C : Typ
e u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] [inst_1 : CategoryTheory.Monoi
dalCategory C] {D : Type u₂}   [inst_2 : CategoryT…
· 使用引理 `CategoryTheory.Iso.map_inv_hom_id`：map_inv_hom_id (F : C ⥤ D) : F.map e.
inv ≫ F.map e.hom = 𝟙 _
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CategoryTheory.MonoidalCategory.tensorHom_def`：∀ {C : Type u} {𝒞 : Categ
oryTheory.Category.{v, u} C} [self : CategoryTheory.MonoidalCategory C] {X₁ Y₁ X
₂ Y₂ : C}   (f : X₁ ⟶ Y₁) (g : X₂ ⟶…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma whiskerRight_tensorUnit_comp_rightUnitor_hom {X : C} {Y : D} (f : Y ⟶ F.obj X) :
    f ▷ 𝟙_ D ≫ (ρ_ (F.obj X)).hom = (f ⊗ₘ ε F) ≫ μ F X (𝟙_ C) ≫ F.map (ρ_ X).hom := by
  simp [tensorHom_def]

@[reassoc]
/-
**CategoryTheory.Functor.LaxMonoidal.** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.
Functor.LaxMonoidal`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma μ_whiskerRight_comp_μ (X Y Z : C) :
    μ F X Y ▷ F.obj Z ≫ μ F (X ⊗ Y) Z = (α_ (F.obj X) (F.obj Y) (F.obj Z)).hom ≫
      F.obj X ◁ μ F Y Z ≫ μ F X (Y ⊗ Z) ≫ F.map (α_ X Y Z).inv := by
  rw [← associativity_assoc, ← F.map_comp, Iso.hom_inv_id, map_id, Category.comp_id]

@[reassoc]
/-
**CategoryTheory.Functor.LaxMonoidal.whiskerLeft_** 是 Mathlib 中的一个引理，位于命名空间 `Cat
egoryTheory.Functor.LaxMonoidal`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma whiskerLeft_μ_comp_μ (X Y Z : C) :
    F.obj X ◁ μ F Y Z ≫ μ F X (Y ⊗ Z) = (α_ (F.obj X) (F.obj Y) (F.obj Z)).inv ≫
      μ F X Y ▷ F.obj Z ≫ μ F (X ⊗ Y) Z ≫ F.map (α_ X Y Z).hom := by
  rw [associativity, Iso.inv_hom_id_assoc]

/-- Copy of a lax monoidal structure with new `ε` and `μ` fields equal to the old ones.

This is useful to fix definitional equalities. -/
@[implicit_reducible]
/-
**CategoryTheory.Functor.LaxMonoidal.copy** 是 Mathlib 中的一个定义，位于命名空间 `CategoryThe
ory.Functor.LaxMonoidal`。
形式化陈述：copy {F : C ⥤ D} (hF : F.LaxMonoidal) (ε' : 𝟙_ D ⟶ F.obj (𝟙_ C)) (μ' : for
all X Y : C, F.obj X otimes F.obj Y ⟶ F.obj (X otimes Y)) (hε : ε' = ε F
参数：hF : F.LaxMonoidal；ε' : 𝟙_ D ⟶ F.obj (𝟙_ C)；μ' : forall X Y : C, F.obj X otim
es F.obj Y ⟶ F.obj (X otimes Y)。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Copy of a lax monoidal structure with new `ε` and `μ` fields equal to the old on
es.

This is useful to fix definitional equalities.
-/
def copy {F : C ⥤ D} (hF : F.LaxMonoidal) (ε' : 𝟙_ D ⟶ F.obj (𝟙_ C))
    (μ' : ∀ X Y : C, F.obj X ⊗ F.obj Y ⟶ F.obj (X ⊗ Y))
    (hε : ε' = ε F := by cat_disch) (hμ : μ' = μ F := by cat_disch) : F.LaxMonoidal where
  ε := ε'
  μ := μ'

end

section

variable {F : C ⥤ D}
    /- unit morphism -/
    (ε : 𝟙_ D ⟶ F.obj (𝟙_ C))
    /- tensorator -/
    (μ : ∀ X Y : C, F.obj X ⊗ F.obj Y ⟶ F.obj (X ⊗ Y))
    (μ_natural :
      ∀ {X Y X' Y' : C} (f : X ⟶ Y) (g : X' ⟶ Y'),
        (F.map f ⊗ₘ F.map g) ≫ μ Y Y' = μ X X' ≫ F.map (f ⊗ₘ g) := by
      cat_disch)
    /- associativity of the tensorator -/
    (associativity :
      ∀ X Y Z : C,
        (μ X Y ⊗ₘ 𝟙 (F.obj Z)) ≫ μ (X ⊗ Y) Z ≫ F.map (α_ X Y Z).hom =
          (α_ (F.obj X) (F.obj Y) (F.obj Z)).hom ≫ (𝟙 (F.obj X) ⊗ₘ μ Y Z) ≫ μ X (Y ⊗ Z) := by
      cat_disch)
    /- unitality -/
    (left_unitality :
      ∀ X : C, (λ_ (F.obj X)).hom = (ε ⊗ₘ 𝟙 (F.obj X)) ≫ μ (𝟙_ C) X ≫ F.map (λ_ X).hom := by
        cat_disch)
    (right_unitality :
      ∀ X : C, (ρ_ (F.obj X)).hom = (𝟙 (F.obj X) ⊗ₘ ε) ≫ μ X (𝟙_ C) ≫ F.map (ρ_ X).hom := by
        cat_disch)

set_option backward.privateInPublic true in
/--
A constructor for lax monoidal functors whose axioms are described by `tensorHom` instead of
`whiskerLeft` and `whiskerRight`.
-/
@[instance_reducible]
/-
**CategoryTheory.Functor.LaxMonoidal.ofTensorHom** 是 Mathlib 中的一个定义，位于命名空间 `Cate
goryTheory.Functor.LaxMonoidal`。
形式化陈述：ofTensorHom : F.LaxMonoidal where ε
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A constructor for lax monoidal functors whose axioms are described by `tensorHom
` instead of
`whiskerLeft` and `whiskerRight`.
-/
def ofTensorHom : F.LaxMonoidal where
  ε := ε
  μ := μ
  μ_natural_left := fun f X' => by
    simp_rw [← tensorHom_id, ← F.map_id, μ_natural]
  μ_natural_right := fun X' f => by
    simp_rw [← id_tensorHom, ← F.map_id, μ_natural]
  associativity := fun X Y Z => by
    simp_rw [← tensorHom_id, ← id_tensorHom, associativity]
  left_unitality := fun X => by
    simp_rw [← tensorHom_id, left_unitality]
  right_unitality := fun X => by
    simp_rw [← id_tensorHom, right_unitality]

end

@[simps]
/-
**CategoryTheory.Functor.LaxMonoidal.id** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheor
y.Functor.LaxMonoidal`。
形式化陈述：id : (𝟭 C).LaxMonoidal where ε
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance id : (𝟭 C).LaxMonoidal where
  ε := 𝟙 _
  μ _ _ := 𝟙 _

section

variable (F : C ⥤ D) (G : D ⥤ E)

variable [F.LaxMonoidal] [G.LaxMonoidal]

set_option backward.defeqAttrib.useBackward true in
@[simps]
/-
**CategoryTheory.Functor.LaxMonoidal.comp** 是 Mathlib 中的一个实例，位于命名空间 `CategoryThe
ory.Functor.LaxMonoidal`。
形式化陈述：comp : (F ⋙ G).LaxMonoidal where ε
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance comp : (F ⋙ G).LaxMonoidal where
  ε := ε G ≫ G.map (ε F)
  μ X Y := μ G _ _ ≫ G.map (μ F X Y)
  μ_natural_left _ _ := by
    simp_rw [comp_obj, F.comp_map, μ_natural_left_assoc, assoc, ← G.map_comp, μ_natural_left]
  μ_natural_right _ _ := by
    simp_rw [comp_obj, F.comp_map, μ_natural_right_assoc, assoc, ← G.map_comp, μ_natural_right]
  associativity _ _ _ := by
    dsimp
    simp_rw [comp_whiskerRight, assoc, μ_natural_left_assoc, MonoidalCategory.whiskerLeft_comp,
      assoc, μ_natural_right_assoc, ← associativity_assoc, ← G.map_comp, associativity]

end

end LaxMonoidal

/-- A functor `F : C ⥤ D` between monoidal categories is oplax monoidal if it is
equipped with morphisms `η : F.obj (𝟙_ C) ⟶ 𝟙 _D` and `δ X Y : F.obj (X ⊗ Y) ⟶ F.obj X ⊗ F.obj Y`,
satisfying the appropriate coherences. -/
@[ext]
/-
**CategoryTheory.Functor.OplaxMonoidal** 是 Mathlib 中的一个类，位于命名空间 `CategoryTheory.
Functor`。
形式化陈述：OplaxMonoidal (F : C ⥤ D) where /-- the counit morphism of a lax monoidal 
functor -/ η (F) : F.obj (𝟙_ C) ⟶ 𝟙_ D /-- the cotensorator of an oplax monoidal
 functor -/ δ (F) : forall X Y : C, F.obj (X otimes Y) ⟶ F.obj X otimes F.obj Y 
δ_natural_left (F) : forall {X Y : C} (f : X ⟶ Y) (X' : C), δ X X' ≫ F.map f ▷ F
.obj X' = F.map (f ▷ X') ≫ δ Y X'
参数：F : C ⥤ D；F。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A functor `F : C ⥤ D` between monoidal categories is oplax monoidal if it is
equipped with morphisms `η : F.obj (𝟙_ C) ⟶ 𝟙 _D` and `δ X Y : F.obj (X ⊗ Y) ⟶ F
.obj X ⊗ F.obj Y`,
satisfying the appropriate coherences.
-/
class OplaxMonoidal (F : C ⥤ D) where
  /-- the counit morphism of a lax monoidal functor -/
  η (F) : F.obj (𝟙_ C) ⟶ 𝟙_ D
  /-- the cotensorator of an oplax monoidal functor -/
  δ (F) : ∀ X Y : C, F.obj (X ⊗ Y) ⟶ F.obj X ⊗ F.obj Y
  δ_natural_left (F) :
    ∀ {X Y : C} (f : X ⟶ Y) (X' : C),
      δ X X' ≫ F.map f ▷ F.obj X' = F.map (f ▷ X') ≫ δ Y X' := by
    cat_disch
  δ_natural_right (F) :
    ∀ {X Y : C} (X' : C) (f : X ⟶ Y),
      δ X' X ≫ F.obj X' ◁ F.map f = F.map (X' ◁ f) ≫ δ X' Y := by
    cat_disch
  /-- associativity of the tensorator -/
  oplax_associativity (F) :
    ∀ X Y Z : C,
      δ (X ⊗ Y) Z ≫ δ X Y ▷ F.obj Z ≫ (α_ (F.obj X) (F.obj Y) (F.obj Z)).hom =
        F.map (α_ X Y Z).hom ≫ δ X (Y ⊗ Z) ≫ F.obj X ◁ δ Y Z := by
    cat_disch
  -- unitality
  oplax_left_unitality (F) :
    ∀ X : C, (λ_ (F.obj X)).inv = F.map (λ_ X).inv ≫ δ (𝟙_ C) X ≫ η ▷ F.obj X := by
      cat_disch
  oplax_right_unitality (F) :
    ∀ X : C, (ρ_ (F.obj X)).inv = F.map (ρ_ X).inv ≫ δ X (𝟙_ C) ≫ F.obj X ◁ η := by
      cat_disch

namespace OplaxMonoidal

attribute [reassoc (attr := simp)] δ_natural_left δ_natural_right

@[reassoc (attr := simp)]
alias associativity := oplax_associativity

@[simp, reassoc]
alias left_unitality := oplax_left_unitality

@[simp, reassoc]
alias right_unitality := oplax_right_unitality

section

variable (F : C ⥤ D) [F.OplaxMonoidal]

@[reassoc (attr := simp)]
/-
**CategoryTheory.Functor.OplaxMonoidal.** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheor
y.Functor.OplaxMonoidal`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem δ_natural {X Y X' Y' : C} (f : X ⟶ Y) (g : X' ⟶ Y') :
    δ F X X' ≫ (F.map f ⊗ₘ F.map g) = F.map (f ⊗ₘ g) ≫ δ F Y Y' := by
  simp [tensorHom_def]

@[reassoc (attr := simp)]
/-
**CategoryTheory.Functor.OplaxMonoidal.left_unitality_hom** 是 Mathlib 中的一个定理，位于命
名空间 `CategoryTheory.Functor.OplaxMonoidal`。
形式化陈述：left_unitality_hom (X : C) : δ F (𝟙_ C) X ≫ η F ▷ F.obj X ≫ (fun_ (F.obj X
)).hom = F.map (fun_ X).hom
参数：X : C。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.Iso.eq_comp_inv`：eq_comp_inv (α : X ≅ Y) {f : Z ⟶ Y} {g :
 Z ⟶ X} : g = f ≫ α.inv ↔ g ≫ α.hom = f
· 使用定理 `CategoryTheory.Functor.OplaxMonoidal.left_unitality`：∀ {C : Type u₁} {in
st : CategoryTheory.Category.{v₁, u₁} C} {inst_1 : CategoryTheory.MonoidalCatego
ry C} {D : Type u₂}   {inst_2 : CategoryT…
· 使用定理 `CategoryTheory.Functor.map_comp`：∀ {C : Type u₁} [inst : CategoryTheory.
Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]
   (self : CategoryTh…
· 使用定理 `CategoryTheory.Iso.hom_inv_id`：∀ {C : Type u} [inst : CategoryTheory.Cat
egory.{v, u} C] {X Y : C} (self : X ≅ Y),   CategoryTheory.CategoryStruct.comp s
elf.hom self.inv = …
· 使用定理 `CategoryTheory.Functor.map_id`：∀ {C : Type u₁} [inst : CategoryTheory.Ca
tegory.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]  
 (self : CategoryTh…
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
-/
theorem left_unitality_hom (X : C) :
    δ F (𝟙_ C) X ≫ η F ▷ F.obj X ≫ (λ_ (F.obj X)).hom = F.map (λ_ X).hom := by
  rw [← Category.assoc, ← Iso.eq_comp_inv, left_unitality, ← Category.assoc,
    ← F.map_comp, Iso.hom_inv_id, F.map_id, id_comp]

@[reassoc (attr := simp)]
/-
**CategoryTheory.Functor.OplaxMonoidal.right_unitality_hom** 是 Mathlib 中的一个定理，位于
命名空间 `CategoryTheory.Functor.OplaxMonoidal`。
形式化陈述：right_unitality_hom (X : C) : δ F X (𝟙_ C) ≫ F.obj X ◁ η F ≫ (ρ_ (F.obj X)
).hom = F.map (ρ_ X).hom
参数：X : C。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.Iso.eq_comp_inv`：eq_comp_inv (α : X ≅ Y) {f : Z ⟶ Y} {g :
 Z ⟶ X} : g = f ≫ α.inv ↔ g ≫ α.hom = f
· 使用定理 `CategoryTheory.Functor.OplaxMonoidal.right_unitality`：∀ {C : Type u₁} {i
nst : CategoryTheory.Category.{v₁, u₁} C} {inst_1 : CategoryTheory.MonoidalCateg
ory C} {D : Type u₂}   {inst_2 : CategoryT…
· 使用定理 `CategoryTheory.Functor.map_comp`：∀ {C : Type u₁} [inst : CategoryTheory.
Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]
   (self : CategoryTh…
· 使用定理 `CategoryTheory.Iso.hom_inv_id`：∀ {C : Type u} [inst : CategoryTheory.Cat
egory.{v, u} C] {X Y : C} (self : X ≅ Y),   CategoryTheory.CategoryStruct.comp s
elf.hom self.inv = …
· 使用定理 `CategoryTheory.Functor.map_id`：∀ {C : Type u₁} [inst : CategoryTheory.Ca
tegory.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]  
 (self : CategoryTh…
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
-/
theorem right_unitality_hom (X : C) :
    δ F X (𝟙_ C) ≫ F.obj X ◁ η F ≫ (ρ_ (F.obj X)).hom = F.map (ρ_ X).hom := by
  rw [← Category.assoc, ← Iso.eq_comp_inv, right_unitality, ← Category.assoc,
    ← F.map_comp, Iso.hom_inv_id, F.map_id, id_comp]

@[reassoc (attr := simp)]
/-
**CategoryTheory.Functor.OplaxMonoidal.associativity_inv** 是 Mathlib 中的一个定理，位于命名
空间 `CategoryTheory.Functor.OplaxMonoidal`。
形式化陈述：associativity_inv (X Y Z : C) : δ F X (Y otimes Z) ≫ F.obj X ◁ δ F Y Z ≫ (
α_ (F.obj X) (F.obj Y) (F.obj Z)).inv = F.map (α_ X Y Z).inv ≫ δ F (X otimes Y) 
Z ≫ δ F X Y ▷ F.obj Z
参数：X Y Z : C。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.Iso.comp_inv_eq`：comp_inv_eq (α : X ≅ Y) {f : Z ⟶ Y} {g :
 Z ⟶ X} : f ≫ α.inv = g ↔ f = g ≫ α.hom
· 使用定理 `CategoryTheory.Functor.OplaxMonoidal.associativity`：∀ {C : Type u₁} {ins
t : CategoryTheory.Category.{v₁, u₁} C} {inst_1 : CategoryTheory.MonoidalCategor
y C} {D : Type u₂}   {inst_2 : CategoryT…
· 使用定理 `CategoryTheory.Functor.map_comp`：∀ {C : Type u₁} [inst : CategoryTheory.
Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]
   (self : CategoryTh…
· 使用定理 `CategoryTheory.Iso.inv_hom_id`：∀ {C : Type u} [inst : CategoryTheory.Cat
egory.{v, u} C] {X Y : C} (self : X ≅ Y),   CategoryTheory.CategoryStruct.comp s
elf.inv self.hom = …
· 使用定理 `CategoryTheory.Functor.map_id`：∀ {C : Type u₁} [inst : CategoryTheory.Ca
tegory.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]  
 (self : CategoryTh…
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
-/
theorem associativity_inv (X Y Z : C) :
    δ F X (Y ⊗ Z) ≫ F.obj X ◁ δ F Y Z ≫ (α_ (F.obj X) (F.obj Y) (F.obj Z)).inv =
      F.map (α_ X Y Z).inv ≫ δ F (X ⊗ Y) Z ≫ δ F X Y ▷ F.obj Z := by
  rw [← Category.assoc, Iso.comp_inv_eq, Category.assoc, Category.assoc, associativity,
    ← Category.assoc, ← F.map_comp, Iso.inv_hom_id, F.map_id, id_comp]

@[reassoc]
/-
**CategoryTheory.Functor.OplaxMonoidal.** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheor
y.Functor.OplaxMonoidal`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma δ_comp_η_tensorHom {X : C} {Y : D} (f : F.obj X ⟶ Y) :
    δ F (𝟙_ C) X ≫ (η F ⊗ₘ f) = F.map (λ_ X).hom ≫ (λ_ (F.obj X)).inv ≫ 𝟙_ D ◁ f := by
  simp [tensorHom_def]

@[reassoc]
/-
**CategoryTheory.Functor.OplaxMonoidal.** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheor
y.Functor.OplaxMonoidal`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma δ_comp_tensorHom_η {X : C} {Y : D} (f : F.obj X ⟶ Y) :
    δ F X (𝟙_ C) ≫ (f ⊗ₘ η F) = F.map (ρ_ X).hom ≫ (ρ_ (F.obj X)).inv ≫ f ▷ 𝟙_ D := by
  simp [tensorHom_def']

@[reassoc]
/-
**CategoryTheory.Functor.OplaxMonoidal.** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheor
y.Functor.OplaxMonoidal`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma δ_comp_δ_whiskerRight (X Y Z : C) :
    δ F (X ⊗ Y) Z ≫ δ F X Y ▷ F.obj Z = F.map (α_ X Y Z).hom ≫
      δ F X (Y ⊗ Z) ≫ F.obj X ◁ δ F Y Z ≫ (α_ (F.obj X) (F.obj Y) (F.obj Z)).inv := by
  rw [← associativity_assoc, Iso.hom_inv_id, Category.comp_id]

@[reassoc]
/-
**CategoryTheory.Functor.OplaxMonoidal.** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheor
y.Functor.OplaxMonoidal`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma δ_comp_whiskerLeft_δ (X Y Z : C) :
    δ F X (Y ⊗ Z) ≫ F.obj X ◁ δ F Y Z = F.map (α_ X Y Z).inv ≫
      δ F (X ⊗ Y) Z ≫ δ F X Y ▷ F.obj Z ≫ (α_ (F.obj X) (F.obj Y) (F.obj Z)).hom := by
  rw [associativity, ← F.map_comp_assoc, Iso.inv_hom_id, Functor.map_id, Category.id_comp]

end

/-- Copy of an oplax monoidal structure on a functor `F` with new `η` and `δ` fields equal to the
old ones.

This is useful to fix definitional equalities. -/
@[implicit_reducible]
/-
**CategoryTheory.Functor.OplaxMonoidal.copy** 是 Mathlib 中的一个定义，位于命名空间 `CategoryT
heory.Functor.OplaxMonoidal`。
形式化陈述：copy {F : C ⥤ D} (hF : F.OplaxMonoidal) (η' : F.obj (𝟙_ C) ⟶ 𝟙_ D) (δ' : f
orall X Y : C, F.obj (X otimes Y) ⟶ F.obj X otimes F.obj Y) (hη : η' = η F
参数：hF : F.OplaxMonoidal；η' : F.obj (𝟙_ C) ⟶ 𝟙_ D；δ' : forall X Y : C, F.obj (X o
times Y) ⟶ F.obj X otimes F.obj Y。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Copy of an oplax monoidal structure on a functor `F` with new `η` and `δ` fields
 equal to the
old ones.

This is useful to fix definitional equalities.
-/
def copy {F : C ⥤ D} (hF : F.OplaxMonoidal) (η' : F.obj (𝟙_ C) ⟶ 𝟙_ D)
    (δ' : ∀ X Y : C, F.obj (X ⊗ Y) ⟶ F.obj X ⊗ F.obj Y)
    (hη : η' = η F := by cat_disch) (hδ : δ' = δ F := by cat_disch) : F.OplaxMonoidal where
  η := η'
  δ := δ'

@[simps]
/-
**CategoryTheory.Functor.OplaxMonoidal.id** 是 Mathlib 中的一个实例，位于命名空间 `CategoryThe
ory.Functor.OplaxMonoidal`。
形式化陈述：id : (𝟭 C).OplaxMonoidal where η
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance id : (𝟭 C).OplaxMonoidal where
  η := 𝟙 _
  δ _ _ := 𝟙 _

section

variable (F : C ⥤ D) (G : D ⥤ E) [F.OplaxMonoidal] [G.OplaxMonoidal]

set_option backward.defeqAttrib.useBackward true in
@[simps]
/-
**CategoryTheory.Functor.OplaxMonoidal.comp** 是 Mathlib 中的一个实例，位于命名空间 `CategoryT
heory.Functor.OplaxMonoidal`。
形式化陈述：comp : (F ⋙ G).OplaxMonoidal where η
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance comp : (F ⋙ G).OplaxMonoidal where
  η := G.map (η F) ≫ η G
  δ X Y := G.map (δ F X Y) ≫ δ G _ _
  δ_natural_left {X Y} f X' := by
    dsimp
    rw [assoc, δ_natural_left, ← G.map_comp_assoc, δ_natural_left, map_comp, assoc]
  δ_natural_right _ _ := by
    dsimp
    rw [assoc, δ_natural_right, ← G.map_comp_assoc, δ_natural_right, map_comp, assoc]
  oplax_associativity X Y Z := by
    dsimp
    rw [comp_whiskerRight, assoc, assoc, assoc, δ_natural_left_assoc, associativity,
      ← G.map_comp_assoc, ← G.map_comp_assoc, assoc, associativity, map_comp, map_comp,
      assoc, assoc, MonoidalCategory.whiskerLeft_comp, δ_natural_right_assoc]

end

end OplaxMonoidal

open LaxMonoidal OplaxMonoidal

/-- A functor between monoidal categories is monoidal if it is lax and oplax monoidals,
and both data give inverse isomorphisms. -/
@[ext]
/-
**CategoryTheory.Functor.Monoidal** 是 Mathlib 中的一个类，位于命名空间 `CategoryTheory.Funct
or`。
形式化陈述：Monoidal (F : C ⥤ D) extends F.LaxMonoidal, F.OplaxMonoidal where ε_η (F) 
: ε ≫ η = 𝟙 _
参数：F : C ⥤ D；F。
继承自：F.LaxMonoidal, F.OplaxMonoidal。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A functor between monoidal categories is monoidal if it is lax and oplax monoida
ls,
and both data give inverse isomorphisms.
-/
class Monoidal (F : C ⥤ D) extends F.LaxMonoidal, F.OplaxMonoidal where
  ε_η (F) : ε ≫ η = 𝟙 _ := by cat_disch
  η_ε (F) : η ≫ ε = 𝟙 _ := by cat_disch
  μ_δ (F) (X Y : C) : μ X Y ≫ δ X Y = 𝟙 _ := by cat_disch
  δ_μ (F) (X Y : C) : δ X Y ≫ μ X Y = 𝟙 _ := by cat_disch

namespace Monoidal

attribute [reassoc (attr := simp)] ε_η η_ε μ_δ δ_μ

section

variable (F : C ⥤ D) [F.Monoidal]

/-- The isomorphism `𝟙_ D ≅ F.obj (𝟙_ C)` when `F` is a monoidal functor. -/
@[simps]
/-
**CategoryTheory.Functor.Monoidal.** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Fun
ctor.Monoidal`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The isomorphism `𝟙_ D ≅ F.obj (𝟙_ C)` when `F` is a monoidal functor.
-/
def εIso : 𝟙_ D ≅ F.obj (𝟙_ C) where
  hom := ε F
  inv := η F

/-- The isomorphism `F.obj X ⊗ F.obj Y ≅ F.obj (X ⊗ Y)` when `F` is a monoidal functor. -/
@[simps]
/-
**CategoryTheory.Functor.Monoidal.** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Fun
ctor.Monoidal`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The isomorphism `F.obj X ⊗ F.obj Y ≅ F.obj (X ⊗ Y)` when `F` is a monoidal funct
or.
-/
def μIso (X Y : C) : F.obj X ⊗ F.obj Y ≅ F.obj (X ⊗ Y) where
  hom := μ F X Y
  inv := δ F X Y
/-
**CategoryTheory.Functor.Monoidal.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Fun
ctor.Monoidal`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : IsIso (ε F) := (εIso F).isIso_hom
/-
**CategoryTheory.Functor.Monoidal.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Fun
ctor.Monoidal`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : IsIso (η F) := (εIso F).isIso_inv
/-
**CategoryTheory.Functor.Monoidal.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Fun
ctor.Monoidal`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (X Y : C) : IsIso (μ F X Y) := (μIso F X Y).isIso_hom
/-
**CategoryTheory.Functor.Monoidal.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Fun
ctor.Monoidal`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (X Y : C) : IsIso (δ F X Y) := (μIso F X Y).isIso_inv

@[reassoc (attr := simp)]
/-
**CategoryTheory.Functor.Monoidal.map_** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory
.Functor.Monoidal`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma map_ε_η (G : D ⥤ C') : G.map (ε F) ≫ G.map (η F) = 𝟙 _ :=
  (εIso F).map_hom_inv_id G

@[reassoc (attr := simp)]
/-
**CategoryTheory.Functor.Monoidal.map_** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory
.Functor.Monoidal`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma map_η_ε (G : D ⥤ C') : G.map (η F) ≫ G.map (ε F) = 𝟙 _ :=
  (εIso F).map_inv_hom_id G

@[reassoc (attr := simp)]
/-
**CategoryTheory.Functor.Monoidal.map_** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory
.Functor.Monoidal`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma map_μ_δ (G : D ⥤ C') (X Y : C) : G.map (μ F X Y) ≫ G.map (δ F X Y) = 𝟙 _ :=
  (μIso F X Y).map_hom_inv_id G

@[reassoc (attr := simp)]
/-
**CategoryTheory.Functor.Monoidal.map_** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory
.Functor.Monoidal`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma map_δ_μ (G : D ⥤ C') (X Y : C) : G.map (δ F X Y) ≫ G.map (μ F X Y) = 𝟙 _ :=
  (μIso F X Y).map_inv_hom_id G

@[reassoc (attr := simp)]
/-
**CategoryTheory.Functor.Monoidal.whiskerRight_** 是 Mathlib 中的一个引理，位于命名空间 `Categ
oryTheory.Functor.Monoidal`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma whiskerRight_ε_η (T : D) : ε F ▷ T ≫ η F ▷ T = 𝟙 _ := by
  rw [← MonoidalCategory.comp_whiskerRight, ε_η, id_whiskerRight]

@[reassoc (attr := simp)]
/-
**CategoryTheory.Functor.Monoidal.whiskerRight_** 是 Mathlib 中的一个引理，位于命名空间 `Categ
oryTheory.Functor.Monoidal`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma whiskerRight_η_ε (T : D) : η F ▷ T ≫ ε F ▷ T = 𝟙 _ := by
  rw [← MonoidalCategory.comp_whiskerRight, η_ε, id_whiskerRight]

@[reassoc (attr := simp)]
/-
**CategoryTheory.Functor.Monoidal.whiskerRight_** 是 Mathlib 中的一个引理，位于命名空间 `Categ
oryTheory.Functor.Monoidal`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma whiskerRight_μ_δ (X Y : C) (T : D) : μ F X Y ▷ T ≫ δ F X Y ▷ T = 𝟙 _ := by
  rw [← MonoidalCategory.comp_whiskerRight, μ_δ, id_whiskerRight]

@[reassoc (attr := simp)]
/-
**CategoryTheory.Functor.Monoidal.whiskerRight_** 是 Mathlib 中的一个引理，位于命名空间 `Categ
oryTheory.Functor.Monoidal`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma whiskerRight_δ_μ (X Y : C) (T : D) : δ F X Y ▷ T ≫ μ F X Y ▷ T = 𝟙 _ := by
  rw [← MonoidalCategory.comp_whiskerRight, δ_μ, id_whiskerRight]

@[reassoc (attr := simp)]
/-
**CategoryTheory.Functor.Monoidal.whiskerLeft_** 是 Mathlib 中的一个引理，位于命名空间 `Catego
ryTheory.Functor.Monoidal`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma whiskerLeft_ε_η (T : D) : T ◁ ε F ≫ T ◁ η F = 𝟙 _ := by
  rw [← MonoidalCategory.whiskerLeft_comp, ε_η, MonoidalCategory.whiskerLeft_id]

@[reassoc (attr := simp)]
/-
**CategoryTheory.Functor.Monoidal.whiskerLeft_** 是 Mathlib 中的一个引理，位于命名空间 `Catego
ryTheory.Functor.Monoidal`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma whiskerLeft_η_ε (T : D) : T ◁ η F ≫ T ◁ ε F = 𝟙 _ := by
  rw [← MonoidalCategory.whiskerLeft_comp, η_ε, MonoidalCategory.whiskerLeft_id]

@[reassoc (attr := simp)]
/-
**CategoryTheory.Functor.Monoidal.whiskerLeft_** 是 Mathlib 中的一个引理，位于命名空间 `Catego
ryTheory.Functor.Monoidal`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma whiskerLeft_μ_δ (X Y : C) (T : D) : T ◁ μ F X Y ≫ T ◁ δ F X Y = 𝟙 _ := by
  rw [← MonoidalCategory.whiskerLeft_comp, μ_δ, MonoidalCategory.whiskerLeft_id]

@[reassoc (attr := simp)]
/-
**CategoryTheory.Functor.Monoidal.whiskerLeft_** 是 Mathlib 中的一个引理，位于命名空间 `Catego
ryTheory.Functor.Monoidal`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma whiskerLeft_δ_μ (X Y : C) (T : D) : T ◁ δ F X Y ≫ T ◁ μ F X Y = 𝟙 _ := by
  rw [← MonoidalCategory.whiskerLeft_comp, δ_μ, MonoidalCategory.whiskerLeft_id]

@[reassoc]
/-
**CategoryTheory.Functor.Monoidal.map_tensor** 是 Mathlib 中的一个定理，位于命名空间 `Category
Theory.Functor.Monoidal`。
形式化陈述：map_tensor {X Y X' Y' : C} (f : X ⟶ Y) (g : X' ⟶ Y') : F.map (f otimesₘ g)
 = δ F X X' ≫ (F.map f otimesₘ F.map g) ≫ μ F Y Y'
参数：f : X ⟶ Y；g : X' ⟶ Y'。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Functor.LaxMonoidal.μ_natural`：μ_natural {X Y X' Y' : C} 
(f : X ⟶ Y) (g : X' ⟶ Y') : (F.map f otimesₘ F.map g) ≫ μ F Y Y' = μ F X X' ≫ F.
map (f otimesₘ g)
· 使用定理 `CategoryTheory.Functor.Monoidal.δ_μ_assoc`：∀ {C : Type u₁} {inst : Categ
oryTheory.Category.{v₁, u₁} C} {inst_1 : CategoryTheory.MonoidalCategory C} {D :
 Type u₂}   {inst_2 : CategoryT…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem map_tensor {X Y X' Y' : C} (f : X ⟶ Y) (g : X' ⟶ Y') :
    F.map (f ⊗ₘ g) = δ F X X' ≫ (F.map f ⊗ₘ F.map g) ≫ μ F Y Y' := by simp

@[reassoc]
/-
**CategoryTheory.Functor.Monoidal.map_whiskerLeft** 是 Mathlib 中的一个定理，位于命名空间 `Cat
egoryTheory.Functor.Monoidal`。
形式化陈述：map_whiskerLeft (X : C) {Y Z : C} (f : Y ⟶ Z) : F.map (X ◁ f) = δ F X Y ≫ 
F.obj X ◁ F.map f ≫ μ F X Z
参数：X : C；f : Y ⟶ Z。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Functor.LaxMonoidal.μ_natural_right`：∀ {C : Type u₁} {ins
t : CategoryTheory.Category.{v₁, u₁} C} {inst_1 : CategoryTheory.MonoidalCategor
y C} {D : Type u₂}   {inst_2 : CategoryT…
· 使用定理 `CategoryTheory.Functor.Monoidal.δ_μ_assoc`：∀ {C : Type u₁} {inst : Categ
oryTheory.Category.{v₁, u₁} C} {inst_1 : CategoryTheory.MonoidalCategory C} {D :
 Type u₂}   {inst_2 : CategoryT…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem map_whiskerLeft (X : C) {Y Z : C} (f : Y ⟶ Z) :
    F.map (X ◁ f) = δ F X Y ≫ F.obj X ◁ F.map f ≫ μ F X Z := by simp

@[reassoc]
/-
**CategoryTheory.Functor.Monoidal.map_whiskerRight** 是 Mathlib 中的一个定理，位于命名空间 `Ca
tegoryTheory.Functor.Monoidal`。
形式化陈述：map_whiskerRight {X Y : C} (f : X ⟶ Y) (Z : C) : F.map (f ▷ Z) = δ F X Z ≫
 F.map f ▷ F.obj Z ≫ μ F Y Z
参数：f : X ⟶ Y；Z : C。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Functor.LaxMonoidal.μ_natural_left`：∀ {C : Type u₁} {inst
 : CategoryTheory.Category.{v₁, u₁} C} {inst_1 : CategoryTheory.MonoidalCategory
 C} {D : Type u₂}   {inst_2 : CategoryT…
· 使用定理 `CategoryTheory.Functor.Monoidal.δ_μ_assoc`：∀ {C : Type u₁} {inst : Categ
oryTheory.Category.{v₁, u₁} C} {inst_1 : CategoryTheory.MonoidalCategory C} {D :
 Type u₂}   {inst_2 : CategoryT…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem map_whiskerRight {X Y : C} (f : X ⟶ Y) (Z : C) :
    F.map (f ▷ Z) = δ F X Z ≫ F.map f ▷ F.obj Z ≫ μ F Y Z := by simp

@[reassoc]
/-
**CategoryTheory.Functor.Monoidal.map_associator** 是 Mathlib 中的一个定理，位于命名空间 `Cate
goryTheory.Functor.Monoidal`。
形式化陈述：map_associator (X Y Z : C) : F.map (α_ X Y Z).hom = δ F (X otimes Y) Z ≫ δ
 F X Y ▷ F.obj Z ≫ (α_ (F.obj X) (F.obj Y) (F.obj Z)).hom ≫ F.obj X ◁ μ F Y Z ≫ 
μ F X (Y otimes Z)
参数：X Y Z : C。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.Functor.LaxMonoidal.associativity`：∀ {C : Type u₁} {inst 
: CategoryTheory.Category.{v₁, u₁} C} {inst_1 : CategoryTheory.MonoidalCategory 
C} {D : Type u₂}   {inst_2 : CategoryT…
· 使用定理 `CategoryTheory.Functor.Monoidal.whiskerRight_δ_μ_assoc`：∀ {C : Type u₁} 
[inst : CategoryTheory.Category.{v₁, u₁} C] [inst_1 : CategoryTheory.MonoidalCat
egory C] {D : Type u₂}   [inst_2 : CategoryT…
· 使用定理 `CategoryTheory.Functor.Monoidal.δ_μ_assoc`：∀ {C : Type u₁} {inst : Categ
oryTheory.Category.{v₁, u₁} C} {inst_1 : CategoryTheory.MonoidalCategory C} {D :
 Type u₂}   {inst_2 : CategoryT…
-/
theorem map_associator (X Y Z : C) :
    F.map (α_ X Y Z).hom =
      δ F (X ⊗ Y) Z ≫ δ F X Y ▷ F.obj Z ≫
        (α_ (F.obj X) (F.obj Y) (F.obj Z)).hom ≫ F.obj X ◁ μ F Y Z ≫ μ F X (Y ⊗ Z) := by
  rw [← LaxMonoidal.associativity F, whiskerRight_δ_μ_assoc, δ_μ_assoc]

@[reassoc]
/-
**CategoryTheory.Functor.Monoidal.map_associator_inv** 是 Mathlib 中的一个定理，位于命名空间 `
CategoryTheory.Functor.Monoidal`。
形式化陈述：map_associator_inv (X Y Z : C) : F.map (α_ X Y Z).inv = δ F X (Y otimes Z)
 ≫ F.obj X ◁ δ F Y Z ≫ (α_ (F.obj X) (F.obj Y) (F.obj Z)).inv ≫ μ F X Y ▷ F.obj 
Z ≫ μ F (X otimes Y) Z
参数：X Y Z : C。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.cancel_epi`：cancel_epi (f : X ⟶ Y) [Epi f] {g h : Y ⟶ Z} 
: f ≫ g = f ≫ h ↔ g = h
· 使用定理 `CategoryTheory.IsSplitEpi.epi`：∀ {C : Type u₁} [inst : CategoryTheory.Ca
tegory.{v₁, u₁} C] {X Y : C} (f : X ⟶ Y) [hf : CategoryTheory.IsSplitEpi f],   C
ategoryTheory.Epi f
· 使用定理 `CategoryTheory.instIsSplitEpiMap`：∀ {C : Type u₁} [inst : CategoryTheory
.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D
]   {X Y : C} (f : X ⟶…
· 使用定理 `CategoryTheory.IsSplitEpi.of_iso`：∀ {C : Type u₁} [inst : CategoryTheory
.Category.{v₁, u₁} C] {X Y : C} (f : X ⟶ Y) [CategoryTheory.IsIso f],   Category
Theory.IsSplitEpi f
· 使用定理 `CategoryTheory.Iso.isIso_hom`：∀ {C : Type u} [inst : CategoryTheory.Cate
gory.{v, u} C] {X Y : C} (e : X ≅ Y), CategoryTheory.IsIso e.hom
· 使用引理 `CategoryTheory.Iso.map_hom_inv_id`：map_hom_inv_id (F : C ⥤ D) : F.map e.
hom ≫ F.map e.inv = 𝟙 _
· 使用定理 `CategoryTheory.Functor.Monoidal.map_associator`：map_associator (X Y Z : 
C) : F.map (α_ X Y Z).hom = δ F (X otimes Y) Z ≫ δ F X Y ▷ F.obj Z ≫ (α_ (F.obj 
X) (F.obj Y) (F.obj Z)).hom ≫ F.obj …
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.Functor.OplaxMonoidal.associativity_inv_assoc`：∀ {C : Typ
e u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] [inst_1 : CategoryTheory.Monoi
dalCategory C] {D : Type u₂}   [inst_2 : CategoryT…
· 使用定理 `CategoryTheory.Functor.Monoidal.whiskerRight_δ_μ_assoc`：∀ {C : Type u₁} 
[inst : CategoryTheory.Category.{v₁, u₁} C] [inst_1 : CategoryTheory.MonoidalCat
egory C] {D : Type u₂}   [inst_2 : CategoryT…
· 使用定理 `CategoryTheory.Functor.Monoidal.δ_μ`：∀ {C : Type u₁} {inst : CategoryThe
ory.Category.{v₁, u₁} C} {inst_1 : CategoryTheory.MonoidalCategory C} {D : Type 
u₂}   {inst_2 : CategoryT…
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `CategoryTheory.Functor.LaxMonoidal.associativity_inv`：associativity_inv 
(X Y Z : C) : F.obj X ◁ μ F Y Z ≫ μ F X (Y otimes Z) ≫ F.map (α_ X Y Z).inv = (α
_ (F.obj X) (F.obj Y) (F.obj Z)).inv ≫ μ F…
· 使用定理 `CategoryTheory.Iso.hom_inv_id_assoc`：∀ {C : Type u} [inst : CategoryTheo
ry.Category.{v, u} C] {X Y : C} (self : X ≅ Y) {Z : C} (h : X ⟶ Z),   CategoryTh
eory.CategoryStruct.comp …
-/
theorem map_associator_inv (X Y Z : C) :
    F.map (α_ X Y Z).inv =
      δ F X (Y ⊗ Z) ≫ F.obj X ◁ δ F Y Z ≫
        (α_ (F.obj X) (F.obj Y) (F.obj Z)).inv ≫ μ F X Y ▷ F.obj Z ≫ μ F (X ⊗ Y) Z := by
  rw [← cancel_epi (F.map (α_ X Y Z).hom), Iso.map_hom_inv_id, map_associator,
    assoc, assoc, assoc, assoc, OplaxMonoidal.associativity_inv_assoc,
    whiskerRight_δ_μ_assoc, δ_μ, comp_id, LaxMonoidal.associativity_inv,
    Iso.hom_inv_id_assoc, whiskerRight_δ_μ_assoc, δ_μ]

@[reassoc]
/-
**CategoryTheory.Functor.Monoidal.map_associator'** 是 Mathlib 中的一个定理，位于命名空间 `Cat
egoryTheory.Functor.Monoidal`。
形式化陈述：map_associator' (X Y Z : C) : (α_ (F.obj X) (F.obj Y) (F.obj Z)).hom = μ F
 X Y ▷ F.obj Z ≫ μ F (X otimes Y) Z ≫ F.map (α_ X Y Z).hom ≫ δ F X (Y otimes Z) 
≫ F.obj X ◁ δ F Y Z
参数：X Y Z : C。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Functor.LaxMonoidal.associativity_assoc`：∀ {C : Type u₁} 
{inst : CategoryTheory.Category.{v₁, u₁} C} {inst_1 : CategoryTheory.MonoidalCat
egory C} {D : Type u₂}   {inst_2 : CategoryT…
· 使用定理 `CategoryTheory.Functor.Monoidal.μ_δ_assoc`：∀ {C : Type u₁} {inst : Categ
oryTheory.Category.{v₁, u₁} C} {inst_1 : CategoryTheory.MonoidalCategory C} {D :
 Type u₂}   {inst_2 : CategoryT…
· 使用引理 `CategoryTheory.Functor.Monoidal.whiskerLeft_μ_δ`：whiskerLeft_μ_δ (X Y : 
C) (T : D) : T ◁ μ F X Y ≫ T ◁ δ F X Y = 𝟙 _
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem map_associator' (X Y Z : C) :
    (α_ (F.obj X) (F.obj Y) (F.obj Z)).hom =
      μ F X Y ▷ F.obj Z ≫ μ F (X ⊗ Y) Z ≫ F.map (α_ X Y Z).hom ≫
        δ F X (Y ⊗ Z) ≫ F.obj X ◁ δ F Y Z := by
  simp

@[reassoc]
/-
**CategoryTheory.Functor.Monoidal.map_associator_inv'** 是 Mathlib 中的一个定理，位于命名空间 
`CategoryTheory.Functor.Monoidal`。
形式化陈述：map_associator_inv' (X Y Z : C) : (α_ (F.obj X) (F.obj Y) (F.obj Z)).inv =
 F.obj X ◁ μ F Y Z ≫ μ F X (Y otimes Z) ≫ F.map (α_ X Y Z).inv ≫ δ F (X otimes Y
) Z ≫ δ F X Y ▷ F.obj Z
参数：X Y Z : C。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.cancel_epi`：cancel_epi (f : X ⟶ Y) [Epi f] {g h : Y ⟶ Z} 
: f ≫ g = f ≫ h ↔ g = h
· 使用定理 `CategoryTheory.IsSplitEpi.epi`：∀ {C : Type u₁} [inst : CategoryTheory.Ca
tegory.{v₁, u₁} C] {X Y : C} (f : X ⟶ Y) [hf : CategoryTheory.IsSplitEpi f],   C
ategoryTheory.Epi f
· 使用定理 `CategoryTheory.IsSplitEpi.of_iso`：∀ {C : Type u₁} [inst : CategoryTheory
.Category.{v₁, u₁} C] {X Y : C} (f : X ⟶ Y) [CategoryTheory.IsIso f],   Category
Theory.IsSplitEpi f
· 使用定理 `CategoryTheory.Iso.isIso_hom`：∀ {C : Type u} [inst : CategoryTheory.Cate
gory.{v, u} C] {X Y : C} (e : X ≅ Y), CategoryTheory.IsIso e.hom
· 使用定理 `CategoryTheory.Functor.Monoidal.map_associator'`：map_associator' (X Y Z 
: C) : (α_ (F.obj X) (F.obj Y) (F.obj Z)).hom = μ F X Y ▷ F.obj Z ≫ μ F (X otime
s Y) Z ≫ F.map (α_ X Y Z).hom ≫ δ F X…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CategoryTheory.Functor.LaxMonoidal.associativity_assoc`：∀ {C : Type u₁} 
{inst : CategoryTheory.Category.{v₁, u₁} C} {inst_1 : CategoryTheory.MonoidalCat
egory C} {D : Type u₂}   {inst_2 : CategoryT…
· 使用定理 `CategoryTheory.Functor.Monoidal.μ_δ_assoc`：∀ {C : Type u₁} {inst : Categ
oryTheory.Category.{v₁, u₁} C} {inst_1 : CategoryTheory.MonoidalCategory C} {D :
 Type u₂}   {inst_2 : CategoryT…
· 使用引理 `CategoryTheory.Functor.Monoidal.whiskerLeft_μ_δ`：whiskerLeft_μ_δ (X Y : 
C) (T : D) : T ◁ μ F X Y ≫ T ◁ δ F X Y = 𝟙 _
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `CategoryTheory.Iso.hom_inv_id`：∀ {C : Type u} [inst : CategoryTheory.Cat
egory.{v, u} C] {X Y : C} (self : X ≅ Y),   CategoryTheory.CategoryStruct.comp s
elf.hom self.inv = …
· 使用定理 `CategoryTheory.Functor.LaxMonoidal.associativity_inv_assoc`：∀ {C : Type 
u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] [inst_1 : CategoryTheory.Monoida
lCategory C] {D : Type u₂}   [inst_2 : CategoryT…
· 使用引理 `CategoryTheory.Functor.Monoidal.whiskerRight_μ_δ`：whiskerRight_μ_δ (X Y 
: C) (T : D) : μ F X Y ▷ T ≫ δ F X Y ▷ T = 𝟙 _
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem map_associator_inv' (X Y Z : C) :
    (α_ (F.obj X) (F.obj Y) (F.obj Z)).inv =
      F.obj X ◁ μ F Y Z ≫ μ F X (Y ⊗ Z) ≫ F.map (α_ X Y Z).inv ≫
        δ F (X ⊗ Y) Z ≫ δ F X Y ▷ F.obj Z := by
  rw [← cancel_epi (α_ (F.obj X) (F.obj Y) (F.obj Z)).hom, map_associator']
  simp

@[reassoc]
/-
**CategoryTheory.Functor.Monoidal.map_leftUnitor** 是 Mathlib 中的一个定理，位于命名空间 `Cate
goryTheory.Functor.Monoidal`。
形式化陈述：map_leftUnitor (X : C) : F.map (fun_ X).hom = δ F (𝟙_ C) X ≫ η F ▷ F.obj X
 ≫ (fun_ (F.obj X)).hom
参数：X : C。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Functor.LaxMonoidal.left_unitality`：∀ {C : Type u₁} {inst
 : CategoryTheory.Category.{v₁, u₁} C} {inst_1 : CategoryTheory.MonoidalCategory
 C} {D : Type u₂}   {inst_2 : CategoryT…
· 使用定理 `CategoryTheory.Functor.Monoidal.whiskerRight_η_ε_assoc`：∀ {C : Type u₁} 
[inst : CategoryTheory.Category.{v₁, u₁} C] [inst_1 : CategoryTheory.MonoidalCat
egory C] {D : Type u₂}   [inst_2 : CategoryT…
· 使用定理 `CategoryTheory.Functor.Monoidal.δ_μ_assoc`：∀ {C : Type u₁} {inst : Categ
oryTheory.Category.{v₁, u₁} C} {inst_1 : CategoryTheory.MonoidalCategory C} {D :
 Type u₂}   {inst_2 : CategoryT…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem map_leftUnitor (X : C) :
    F.map (λ_ X).hom = δ F (𝟙_ C) X ≫ η F ▷ F.obj X ≫ (λ_ (F.obj X)).hom := by simp

@[reassoc]
/-
**CategoryTheory.Functor.Monoidal.map_leftUnitor_inv** 是 Mathlib 中的一个定理，位于命名空间 `
CategoryTheory.Functor.Monoidal`。
形式化陈述：map_leftUnitor_inv (X : C) : F.map (fun_ X).inv = (fun_ (F.obj X)).inv ≫ ε
 F ▷ F.obj X ≫ μ F (𝟙_ C) X
参数：X : C。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CategoryTheory.Functor.OplaxMonoidal.left_unitality`：∀ {C : Type u₁} {in
st : CategoryTheory.Category.{v₁, u₁} C} {inst_1 : CategoryTheory.MonoidalCatego
ry C} {D : Type u₂}   {inst_2 : CategoryT…
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.Functor.Monoidal.whiskerRight_η_ε_assoc`：∀ {C : Type u₁} 
[inst : CategoryTheory.Category.{v₁, u₁} C] [inst_1 : CategoryTheory.MonoidalCat
egory C] {D : Type u₂}   [inst_2 : CategoryT…
· 使用定理 `CategoryTheory.Functor.Monoidal.δ_μ`：∀ {C : Type u₁} {inst : CategoryThe
ory.Category.{v₁, u₁} C} {inst_1 : CategoryTheory.MonoidalCategory C} {D : Type 
u₂}   {inst_2 : CategoryT…
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem map_leftUnitor_inv (X : C) :
    F.map (λ_ X).inv = (λ_ (F.obj X)).inv ≫ ε F ▷ F.obj X ≫ μ F (𝟙_ C) X := by simp

@[reassoc]
/-
**CategoryTheory.Functor.Monoidal.map_rightUnitor** 是 Mathlib 中的一个定理，位于命名空间 `Cat
egoryTheory.Functor.Monoidal`。
形式化陈述：map_rightUnitor (X : C) : F.map (ρ_ X).hom = δ F X (𝟙_ C) ≫ F.obj X ◁ η F 
≫ (ρ_ (F.obj X)).hom
参数：X : C。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Functor.LaxMonoidal.right_unitality`：∀ {C : Type u₁} {ins
t : CategoryTheory.Category.{v₁, u₁} C} {inst_1 : CategoryTheory.MonoidalCategor
y C} {D : Type u₂}   {inst_2 : CategoryT…
· 使用定理 `CategoryTheory.Functor.Monoidal.whiskerLeft_η_ε_assoc`：∀ {C : Type u₁} [
inst : CategoryTheory.Category.{v₁, u₁} C] [inst_1 : CategoryTheory.MonoidalCate
gory C] {D : Type u₂}   [inst_2 : CategoryT…
· 使用定理 `CategoryTheory.Functor.Monoidal.δ_μ_assoc`：∀ {C : Type u₁} {inst : Categ
oryTheory.Category.{v₁, u₁} C} {inst_1 : CategoryTheory.MonoidalCategory C} {D :
 Type u₂}   {inst_2 : CategoryT…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem map_rightUnitor (X : C) :
    F.map (ρ_ X).hom = δ F X (𝟙_ C) ≫ F.obj X ◁ η F ≫ (ρ_ (F.obj X)).hom := by simp

@[reassoc]
/-
**CategoryTheory.Functor.Monoidal.map_rightUnitor_inv** 是 Mathlib 中的一个定理，位于命名空间 
`CategoryTheory.Functor.Monoidal`。
形式化陈述：map_rightUnitor_inv (X : C) : F.map (ρ_ X).inv = (ρ_ (F.obj X)).inv ≫ F.ob
j X ◁ ε F ≫ μ F X (𝟙_ C)
参数：X : C。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CategoryTheory.Functor.OplaxMonoidal.right_unitality`：∀ {C : Type u₁} {i
nst : CategoryTheory.Category.{v₁, u₁} C} {inst_1 : CategoryTheory.MonoidalCateg
ory C} {D : Type u₂}   {inst_2 : CategoryT…
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.Functor.Monoidal.whiskerLeft_η_ε_assoc`：∀ {C : Type u₁} [
inst : CategoryTheory.Category.{v₁, u₁} C] [inst_1 : CategoryTheory.MonoidalCate
gory C] {D : Type u₂}   [inst_2 : CategoryT…
· 使用定理 `CategoryTheory.Functor.Monoidal.δ_μ`：∀ {C : Type u₁} {inst : CategoryThe
ory.Category.{v₁, u₁} C} {inst_1 : CategoryTheory.MonoidalCategory C} {D : Type 
u₂}   {inst_2 : CategoryT…
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem map_rightUnitor_inv (X : C) :
    F.map (ρ_ X).inv = (ρ_ (F.obj X)).inv ≫ F.obj X ◁ ε F ≫ μ F X (𝟙_ C) := by simp
/-
**CategoryTheory.Functor.Monoidal.inv_** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory
.Functor.Monoidal`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma inv_η : CategoryTheory.inv (η F) = ε F := by
  rw [← εIso_hom, ← Iso.comp_inv_eq_id, εIso_inv, IsIso.inv_hom_id]
/-
**CategoryTheory.Functor.Monoidal.inv_** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory
.Functor.Monoidal`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma inv_ε : CategoryTheory.inv (ε F) = η F := by simp [← inv_η]
/-
**CategoryTheory.Functor.Monoidal.inv_** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory
.Functor.Monoidal`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma inv_μ (X Y : C) : CategoryTheory.inv (μ F X Y) = δ F X Y := by
  rw [← Monoidal.μIso_inv, ← CategoryTheory.IsIso.inv_eq_inv]
  simp only [IsIso.inv_inv, IsIso.Iso.inv_inv, μIso_hom]
/-
**CategoryTheory.Functor.Monoidal.inv_** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory
.Functor.Monoidal`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma inv_δ (X Y : C) : CategoryTheory.inv (δ F X Y) = μ F X Y := by simp [← inv_μ]

set_option backward.defeqAttrib.useBackward true in
/-- The tensorator as a natural isomorphism. -/
@[simps!]
/-
**CategoryTheory.Functor.Monoidal.** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Fun
ctor.Monoidal`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The tensorator as a natural isomorphism.
-/
def μNatIso :
    Functor.prod F F ⋙ tensor D ≅ tensor C ⋙ F :=
  NatIso.ofComponents (fun _ ↦ μIso F _ _)

set_option backward.defeqAttrib.useBackward true in
/-- Monoidal functors commute with left tensoring up to isomorphism -/
@[simps!]
/-
**CategoryTheory.Functor.Monoidal.commTensorLeft** 是 Mathlib 中的一个定义，位于命名空间 `Cate
goryTheory.Functor.Monoidal`。
形式化陈述：commTensorLeft (X : C) : F ⋙ tensorLeft (F.obj X) ≅ tensorLeft X ⋙ F
参数：X : C。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Monoidal functors commute with left tensoring up to isomorphism
-/
def commTensorLeft (X : C) :
    F ⋙ tensorLeft (F.obj X) ≅ tensorLeft X ⋙ F :=
  NatIso.ofComponents (fun Y => μIso F X Y)

set_option backward.defeqAttrib.useBackward true in
/-- Monoidal functors commute with right tensoring up to isomorphism -/
@[simps!]
/-
**CategoryTheory.Functor.Monoidal.commTensorRight** 是 Mathlib 中的一个定义，位于命名空间 `Cat
egoryTheory.Functor.Monoidal`。
形式化陈述：commTensorRight (X : C) : F ⋙ tensorRight (F.obj X) ≅ tensorRight X ⋙ F
参数：X : C。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Monoidal functors commute with right tensoring up to isomorphism
-/
def commTensorRight (X : C) :
    F ⋙ tensorRight (F.obj X) ≅ tensorRight X ⋙ F :=
  NatIso.ofComponents (fun Y => μIso F Y X)

end

/-
**CategoryTheory.Functor.Monoidal.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Fun
ctor.Monoidal`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : (𝟭 C).Monoidal where

variable (F : C ⥤ D) (G : D ⥤ E)

set_option backward.defeqAttrib.useBackward true in
/-
**CategoryTheory.Functor.Monoidal.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Fun
ctor.Monoidal`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [F.Monoidal] [G.Monoidal] : (F ⋙ G).Monoidal where
  ε_η := by simp
  η_ε := by simp
  μ_δ _ _ := by simp
  δ_μ _ _ := by simp
/-
**CategoryTheory.Functor.Monoidal.toLaxMonoidal_injective** 是 Mathlib 中的一个引理，位于命
名空间 `CategoryTheory.Functor.Monoidal`。
形式化陈述：toLaxMonoidal_injective : Function.Injective (@Monoidal.toLaxMonoidal _ _ 
_ _ _ _ _ : F.Monoidal -> F.LaxMonoidal)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Functor.Monoidal.ext`：∀ {C : Type u₁} {inst : CategoryThe
ory.Category.{v₁, u₁} C} {inst_1 : CategoryTheory.MonoidalCategory C} {D : Type 
u₂}   {inst_2 : CategoryT…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.cancel_epi`：cancel_epi (f : X ⟶ Y) [Epi f] {g h : Y ⟶ Z} 
: f ≫ g = f ≫ h ↔ g = h
· 使用定理 `CategoryTheory.IsSplitEpi.epi`：∀ {C : Type u₁} [inst : CategoryTheory.Ca
tegory.{v₁, u₁} C] {X Y : C} (f : X ⟶ Y) [hf : CategoryTheory.IsSplitEpi f],   C
ategoryTheory.Epi f
· 使用定理 `CategoryTheory.IsSplitEpi.of_iso`：∀ {C : Type u₁} [inst : CategoryTheory
.Category.{v₁, u₁} C] {X Y : C} (f : X ⟶ Y) [CategoryTheory.IsIso f],   Category
Theory.IsSplitEpi f
· 使用定理 `CategoryTheory.Iso.isIso_hom`：∀ {C : Type u} [inst : CategoryTheory.Cate
gory.{v, u} C] {X Y : C} (e : X ≅ Y), CategoryTheory.IsIso e.hom
· 使用定理 `CategoryTheory.Functor.Monoidal.εIso_hom`：∀ {C : Type u₁} [inst : Catego
ryTheory.Category.{v₁, u₁} C] [inst_1 : CategoryTheory.MonoidalCategory C] {D : 
Type u₂}   [inst_2 : CategoryT…
· 使用定理 `CategoryTheory.Functor.Monoidal.ε_η`：∀ {C : Type u₁} {inst : CategoryThe
ory.Category.{v₁, u₁} C} {inst_1 : CategoryTheory.MonoidalCategory C} {D : Type 
u₂}   {inst_2 : CategoryT…
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `CategoryTheory.Functor.Monoidal.μIso_hom`：∀ {C : Type u₁} [inst : Catego
ryTheory.Category.{v₁, u₁} C] [inst_1 : CategoryTheory.MonoidalCategory C] {D : 
Type u₂}   [inst_2 : CategoryT…
· 使用定理 `CategoryTheory.Functor.Monoidal.μ_δ`：∀ {C : Type u₁} {inst : CategoryThe
ory.Category.{v₁, u₁} C} {inst_1 : CategoryTheory.MonoidalCategory C} {D : Type 
u₂}   {inst_2 : CategoryT…
-/
lemma toLaxMonoidal_injective : Function.Injective
    (@Monoidal.toLaxMonoidal _ _ _ _ _ _ _ : F.Monoidal → F.LaxMonoidal) := by
  intro a b eq
  ext1
  · exact congr(($eq).ε)
  · exact congr(($eq).μ)
  · rw [← cancel_epi (εIso _).hom]
    rw [εIso_hom, ε_η, ← @ε_η _ _ _ _ _ _ _ a, ← εIso_hom]
    exact congr(($eq.symm).ε ≫ _)
  · ext
    rw [← cancel_epi (μIso F _ _).hom]
    rw [μIso_hom, μ_δ, ← @μ_δ _ _ _ _ _ _ _ a, ← μIso_hom]
    exact congr(($eq.symm).μ _ _ ≫ _)
/-
**CategoryTheory.Functor.Monoidal.toOplaxMonoidal_injective** 是 Mathlib 中的一个引理，位
于命名空间 `CategoryTheory.Functor.Monoidal`。
形式化陈述：toOplaxMonoidal_injective : Function.Injective (@Monoidal.toOplaxMonoidal 
_ _ _ _ _ _ _ : F.Monoidal -> F.OplaxMonoidal)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Functor.Monoidal.ext`：∀ {C : Type u₁} {inst : CategoryThe
ory.Category.{v₁, u₁} C} {inst_1 : CategoryTheory.MonoidalCategory C} {D : Type 
u₂}   {inst_2 : CategoryT…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.cancel_mono`：∀ {C : Type u} [inst : CategoryTheory.Catego
ry.{v, u} C] {X Y Z : C} (f : Y ⟶ X) [CategoryTheory.Mono f] {g h : Z ⟶ Y},   Ca
tegoryTheory.Cat…
· 使用定理 `CategoryTheory.IsSplitMono.mono`：∀ {C : Type u₁} [inst : CategoryTheory.
Category.{v₁, u₁} C] {X Y : C} (f : Y ⟶ X) [hf : CategoryTheory.IsSplitMono f], 
  CategoryTheory.Mono…
· 使用定理 `CategoryTheory.IsSplitMono.of_iso`：∀ {C : Type u₁} [inst : CategoryTheor
y.Category.{v₁, u₁} C] {X Y : C} (f : Y ⟶ X) [CategoryTheory.IsIso f],   Categor
yTheory.IsSplitMono f
· 使用定理 `CategoryTheory.Iso.isIso_inv`：∀ {C : Type u} [inst : CategoryTheory.Cate
gory.{v, u} C] {X Y : C} (e : X ≅ Y), CategoryTheory.IsIso e.inv
· 使用定理 `CategoryTheory.Functor.Monoidal.εIso_inv`：∀ {C : Type u₁} [inst : Catego
ryTheory.Category.{v₁, u₁} C] [inst_1 : CategoryTheory.MonoidalCategory C] {D : 
Type u₂}   [inst_2 : CategoryT…
· 使用定理 `CategoryTheory.Functor.Monoidal.ε_η`：∀ {C : Type u₁} {inst : CategoryThe
ory.Category.{v₁, u₁} C} {inst_1 : CategoryTheory.MonoidalCategory C} {D : Type 
u₂}   {inst_2 : CategoryT…
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `CategoryTheory.Functor.Monoidal.μIso_inv`：∀ {C : Type u₁} [inst : Catego
ryTheory.Category.{v₁, u₁} C] [inst_1 : CategoryTheory.MonoidalCategory C] {D : 
Type u₂}   [inst_2 : CategoryT…
· 使用定理 `CategoryTheory.Functor.Monoidal.μ_δ`：∀ {C : Type u₁} {inst : CategoryThe
ory.Category.{v₁, u₁} C} {inst_1 : CategoryTheory.MonoidalCategory C} {D : Type 
u₂}   {inst_2 : CategoryT…
-/
lemma toOplaxMonoidal_injective : Function.Injective
    (@Monoidal.toOplaxMonoidal _ _ _ _ _ _ _ : F.Monoidal → F.OplaxMonoidal) := by
  intro a b eq
  ext1
  · rw [← cancel_mono (εIso _).inv]
    rw [εIso_inv, ε_η, ← @ε_η _ _ _ _ _ _ _ a, ← εIso_inv]
    exact congr(_ ≫ ($eq.symm).η)
  · ext
    rw [← cancel_mono (μIso F _ _).inv]
    rw [μIso_inv, μ_δ, ← @μ_δ _ _ _ _ _ _ _ a, ← μIso_inv]
    exact congr(_ ≫ ($eq.symm).δ _ _)
  · exact congr(($eq).η)
  · exact congr(($eq).δ)

/-- Copy of a monoidal structure on a functor `F` with new `ε`, `μ`, `η` and `δ` fields equal to the
old ones.

This is useful to fix definitional equalities. -/
@[implicit_reducible]
/-
**CategoryTheory.Functor.Monoidal.copy** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory
.Functor.Monoidal`。
形式化陈述：copy {F : C ⥤ D} (hF : F.Monoidal) (ε' : 𝟙_ D ⟶ F.obj (𝟙_ C)) (μ' : forall
 X Y : C, F.obj X otimes F.obj Y ⟶ F.obj (X otimes Y)) (η' : F.obj (𝟙_ C) ⟶ 𝟙_ D
) (δ' : forall X Y : C, F.obj (X otimes Y) ⟶ F.obj X otimes F.obj Y) (hε : ε' = 
ε F
参数：hF : F.Monoidal；ε' : 𝟙_ D ⟶ F.obj (𝟙_ C)；μ' : forall X Y : C, F.obj X otimes 
F.obj Y ⟶ F.obj (X otimes Y)；η' : F.obj (𝟙_ C) ⟶ 𝟙_ D；δ' : forall X Y : C, F.obj
 (X otimes Y) ⟶ F.obj X otimes F.obj Y。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Copy of a monoidal structure on a functor `F` with new `ε`, `μ`, `η` and `δ` fie
lds equal to the
old ones.

This is useful to fix definitional equalities.
-/
def copy {F : C ⥤ D} (hF : F.Monoidal) (ε' : 𝟙_ D ⟶ F.obj (𝟙_ C))
    (μ' : ∀ X Y : C, F.obj X ⊗ F.obj Y ⟶ F.obj (X ⊗ Y)) (η' : F.obj (𝟙_ C) ⟶ 𝟙_ D)
    (δ' : ∀ X Y : C, F.obj (X ⊗ Y) ⟶ F.obj X ⊗ F.obj Y)
    (hε : ε' = ε F := by cat_disch) (hμ : μ' = μ F := by cat_disch)
    (hη : η' = η F := by cat_disch) (hδ : δ' = δ F := by cat_disch) : F.Monoidal where
  __ := hF.toLaxMonoidal.copy ε' μ' hε hμ
  __ := hF.toOplaxMonoidal.copy η' δ' hη hδ

end Monoidal

variable (F : C ⥤ D)
/-- Structure which is a helper in order to show that a functor is monoidal. It
consists of isomorphisms `εIso` and `μIso` such that the morphisms `.hom` induced
by these isomorphisms satisfy the axioms of lax monoidal functors. -/
/-
**CategoryTheory.Functor.CoreMonoidal** 是 Mathlib 中的一个结构，位于命名空间 `CategoryTheory.
Functor`。
形式化陈述：CoreMonoidal where /-- unit morphism -/ εIso : 𝟙_ D ≅ F.obj (𝟙_ C) /-- ten
sorator -/ μIso : forall X Y : C, F.obj X otimes F.obj Y ≅ F.obj (X otimes Y) μI
so_hom_natural_left : forall {X Y : C} (f : X ⟶ Y) (X' : C), F.map f ▷ F.obj X' 
≫ (μIso Y X').hom = (μIso X X').hom ≫ F.map (f ▷ X')
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Structure which is a helper in order to show that a functor is monoidal. It
consists of isomorphisms `εIso` and `μIso` such that the morphisms `.hom` induce
d
by these isomorphisms satisfy the axioms of lax monoidal functors.
-/
structure CoreMonoidal where
  /-- unit morphism -/
  εIso : 𝟙_ D ≅ F.obj (𝟙_ C)
  /-- tensorator -/
  μIso : ∀ X Y : C, F.obj X ⊗ F.obj Y ≅ F.obj (X ⊗ Y)
  μIso_hom_natural_left :
    ∀ {X Y : C} (f : X ⟶ Y) (X' : C),
      F.map f ▷ F.obj X' ≫ (μIso Y X').hom = (μIso X X').hom ≫ F.map (f ▷ X') := by
    cat_disch
  μIso_hom_natural_right :
    ∀ {X Y : C} (X' : C) (f : X ⟶ Y),
      F.obj X' ◁ F.map f ≫ (μIso X' Y).hom = (μIso X' X).hom ≫ F.map (X' ◁ f) := by
    cat_disch
  /-- associativity of the tensorator -/
  associativity :
    ∀ X Y Z : C,
      (μIso X Y).hom ▷ F.obj Z ≫ (μIso (X ⊗ Y) Z).hom ≫ F.map (α_ X Y Z).hom =
        (α_ (F.obj X) (F.obj Y) (F.obj Z)).hom ≫ F.obj X ◁ (μIso Y Z).hom ≫
          (μIso X (Y ⊗ Z)).hom := by
    cat_disch
  -- unitality
  left_unitality :
    ∀ X : C, (λ_ (F.obj X)).hom = εIso.hom ▷ F.obj X ≫ (μIso (𝟙_ C) X).hom ≫ F.map (λ_ X).hom := by
      cat_disch
  right_unitality :
    ∀ X : C, (ρ_ (F.obj X)).hom = F.obj X ◁ εIso.hom ≫ (μIso X (𝟙_ C)).hom ≫ F.map (ρ_ X).hom := by
    cat_disch

namespace CoreMonoidal

attribute [reassoc (attr := simp)] μIso_hom_natural_left
  μIso_hom_natural_right associativity

attribute [reassoc] left_unitality right_unitality

variable {F}

/-- Alternative constructor for `CoreMonoidal`, for which the axioms are stated
in terms on the inverses of `εIso` and `μIso`. -/
@[simps]
/-
**CategoryTheory.Functor.CoreMonoidal.mk'** 是 Mathlib 中的一个定义，位于命名空间 `CategoryThe
ory.Functor.CoreMonoidal`。
形式化陈述：mk' (εIso : 𝟙_ D ≅ F.obj (𝟙_ C)) (μIso : forall X Y : C, F.obj X otimes F.
obj Y ≅ F.obj (X otimes Y)) (μIso_inv_natural_left : forall {X Y : C} (f : X ⟶ Y
) (X' : C), (μIso X X').inv ≫ F.map f ▷ F.obj X' = F.map (f ▷ X') ≫ (μIso Y X').
inv
参数：εIso : 𝟙_ D ≅ F.obj (𝟙_ C)；μIso : forall X Y : C, F.obj X otimes F.obj Y ≅ F.
obj (X otimes Y)。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Alternative constructor for `CoreMonoidal`, for which the axioms are stated
in terms on the inverses of `εIso` and `μIso`.
-/
def mk' (εIso : 𝟙_ D ≅ F.obj (𝟙_ C))
    (μIso : ∀ X Y : C, F.obj X ⊗ F.obj Y ≅ F.obj (X ⊗ Y))
    (μIso_inv_natural_left : ∀ {X Y : C} (f : X ⟶ Y) (X' : C),
      (μIso X X').inv ≫ F.map f ▷ F.obj X' = F.map (f ▷ X') ≫ (μIso Y X').inv := by cat_disch)
    (μIso_inv_natural_right : ∀ {X Y : C} (X' : C) (f : X ⟶ Y),
      (μIso X' X).inv ≫ F.obj X' ◁ F.map f = F.map (X' ◁ f) ≫ (μIso X' Y).inv := by cat_disch)
    (oplax_associativity : ∀ X Y Z : C,
      (μIso (X ⊗ Y) Z).inv ≫ (μIso X Y).inv ▷ F.obj Z ≫
        (α_ (F.obj X) (F.obj Y) (F.obj Z)).hom =
      F.map (α_ X Y Z).hom ≫ (μIso X (Y ⊗ Z)).inv ≫ F.obj X ◁ (μIso Y Z).inv := by cat_disch)
    (oplax_left_unitality : ∀ X : C, (λ_ (F.obj X)).inv =
      F.map (λ_ X).inv ≫ (μIso (𝟙_ C) X).inv ≫ εIso.inv ▷ F.obj X := by cat_disch)
    (oplax_right_unitality : ∀ X : C, (ρ_ (F.obj X)).inv =
      F.map (ρ_ X).inv ≫ (μIso X (𝟙_ C)).inv ≫ F.obj X ◁ εIso.inv := by cat_disch) :
    F.CoreMonoidal where
  εIso := εIso
  μIso := μIso
  μIso_hom_natural_left {X Y} f X' := by
    simp [← cancel_epi (μIso X X').inv, reassoc_of% μIso_inv_natural_left f X']
  μIso_hom_natural_right {X Y} X' g := by
    simp [← cancel_mono (μIso X' Y).inv, ← (μIso_inv_natural_right X' g)]
  associativity X Y Z := by
    rw [← cancel_epi ((μIso X Y).inv ▷ F.obj Z), ← cancel_epi (μIso (X ⊗ Y) Z).inv,
      reassoc_of% oplax_associativity]
    simp
  left_unitality X := by
    rw [← cancel_mono (λ_ (F.obj X)).inv, Iso.hom_inv_id, oplax_left_unitality]
    simp
  right_unitality X := by
    rw [← cancel_mono (ρ_ (F.obj X)).inv, Iso.hom_inv_id, oplax_right_unitality]
    simp

variable (h : F.CoreMonoidal)

/-- The lax monoidal functor structure induced by a `Functor.CoreMonoidal` structure. -/
@[simps -isSimp, instance_reducible]
/-
**CategoryTheory.Functor.CoreMonoidal.toLaxMonoidal** 是 Mathlib 中的一个定义，位于命名空间 `C
ategoryTheory.Functor.CoreMonoidal`。
形式化陈述：toLaxMonoidal : F.LaxMonoidal where ε
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Functor.CoreMonoidal.left_unitality`：∀ {C : Type u₁} [ins
t : CategoryTheory.Category.{v₁, u₁} C] [inst_1 : CategoryTheory.MonoidalCategor
y C] {D : Type u₂}   [inst_2 : CategoryT…
· 使用定理 `CategoryTheory.Functor.CoreMonoidal.right_unitality`：∀ {C : Type u₁} [in
st : CategoryTheory.Category.{v₁, u₁} C] [inst_1 : CategoryTheory.MonoidalCatego
ry C] {D : Type u₂}   [inst_2 : CategoryT…

--- 原说明 ---
The lax monoidal functor structure induced by a `Functor.CoreMonoidal` structure
.
-/
def toLaxMonoidal : F.LaxMonoidal where
  ε := h.εIso.hom
  μ X Y := (h.μIso X Y).hom
  left_unitality := h.left_unitality
  right_unitality := h.right_unitality

/-- The oplax monoidal functor structure induced by a `Functor.CoreMonoidal` structure. -/
@[simps -isSimp, instance_reducible]
/-
**CategoryTheory.Functor.CoreMonoidal.toOplaxMonoidal** 是 Mathlib 中的一个定义，位于命名空间 
`CategoryTheory.Functor.CoreMonoidal`。
形式化陈述：toOplaxMonoidal : F.OplaxMonoidal where η
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The oplax monoidal functor structure induced by a `Functor.CoreMonoidal` structu
re.
-/
def toOplaxMonoidal : F.OplaxMonoidal where
  η := h.εIso.inv
  δ X Y := (h.μIso X Y).inv
  δ_natural_left _ _ := by
    rw [← cancel_epi (h.μIso _ _).hom, Iso.hom_inv_id_assoc,
      ← h.μIso_hom_natural_left_assoc, Iso.hom_inv_id, comp_id]
  δ_natural_right _ _ := by
    rw [← cancel_epi (h.μIso _ _).hom, Iso.hom_inv_id_assoc,
      ← h.μIso_hom_natural_right_assoc, Iso.hom_inv_id, comp_id]
  oplax_associativity X Y Z := by
    rw [← cancel_epi (h.μIso (X ⊗ Y) Z).hom, Iso.hom_inv_id_assoc,
      ← cancel_epi ((h.μIso X Y).hom ▷ F.obj Z), hom_inv_whiskerRight_assoc,
      associativity_assoc, Iso.hom_inv_id_assoc, whiskerLeft_hom_inv, comp_id]
  oplax_left_unitality _ := by
    rw [← cancel_epi (λ_ _).hom, Iso.hom_inv_id, h.left_unitality, assoc, assoc,
      Iso.map_hom_inv_id_assoc, Iso.hom_inv_id_assoc, hom_inv_whiskerRight]
  oplax_right_unitality _ := by
    rw [← cancel_epi (ρ_ _).hom, Iso.hom_inv_id, h.right_unitality, assoc, assoc,
      Iso.map_hom_inv_id_assoc, Iso.hom_inv_id_assoc, whiskerLeft_hom_inv]

attribute [local simp] toLaxMonoidal_ε toLaxMonoidal_μ toOplaxMonoidal_η toOplaxMonoidal_δ in
/-- The monoidal functor structure induced by a `Functor.CoreMonoidal` structure. -/
@[simps! toLaxMonoidal toOplaxMonoidal, instance_reducible]
/-
**CategoryTheory.Functor.CoreMonoidal.toMonoidal** 是 Mathlib 中的一个定义，位于命名空间 `Cate
goryTheory.Functor.CoreMonoidal`。
形式化陈述：toMonoidal : F.Monoidal where toLaxMonoidal
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The monoidal functor structure induced by a `Functor.CoreMonoidal` structure.
-/
def toMonoidal : F.Monoidal where
  toLaxMonoidal := h.toLaxMonoidal
  toOplaxMonoidal := h.toOplaxMonoidal

variable (F)

/-- The `Functor.CoreMonoidal` structure given by a lax monoidal functor such
that `ε` and `μ` are isomorphisms. -/
/-
**CategoryTheory.Functor.CoreMonoidal.ofLaxMonoidal** 是 Mathlib 中的一个定义，位于命名空间 `C
ategoryTheory.Functor.CoreMonoidal`。
形式化陈述：ofLaxMonoidal [F.LaxMonoidal] [IsIso (ε F)] [forall X Y, IsIso (μ F X Y)] 
: F.CoreMonoidal where εIso
参数：ε F；μ F X Y。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The `Functor.CoreMonoidal` structure given by a lax monoidal functor such
that `ε` and `μ` are isomorphisms.
-/
noncomputable def ofLaxMonoidal [F.LaxMonoidal] [IsIso (ε F)] [∀ X Y, IsIso (μ F X Y)] :
    F.CoreMonoidal where
  εIso := asIso (ε F)
  μIso X Y := asIso (μ F X Y)

/-- The `Functor.CoreMonoidal` structure given by an oplax monoidal functor such
that `η` and `δ` are isomorphisms. -/
@[simps]
/-
**CategoryTheory.Functor.CoreMonoidal.ofOplaxMonoidal** 是 Mathlib 中的一个定义，位于命名空间 
`CategoryTheory.Functor.CoreMonoidal`。
形式化陈述：ofOplaxMonoidal [F.OplaxMonoidal] [IsIso (η F)] [forall X Y, IsIso (δ F X 
Y)] : F.CoreMonoidal where εIso
参数：η F；δ F X Y。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The `Functor.CoreMonoidal` structure given by an oplax monoidal functor such
that `η` and `δ` are isomorphisms.
-/
noncomputable def ofOplaxMonoidal [F.OplaxMonoidal] [IsIso (η F)] [∀ X Y, IsIso (δ F X Y)] :
    F.CoreMonoidal where
  εIso := (asIso (η F)).symm
  μIso X Y := (asIso (δ F X Y)).symm
  associativity X Y Z := by
    simp [← cancel_epi (δ F X Y ▷ F.obj Z), ← cancel_epi (δ F (X ⊗ Y) Z)]
  left_unitality X := by simp [← cancel_epi (λ_ (F.obj X)).inv]
  right_unitality X := by simp [← cancel_epi (ρ_ (F.obj X)).inv]

end CoreMonoidal

/-- The `Functor.Monoidal` structure given by a lax monoidal functor such
that `ε` and `μ` are isomorphisms. -/
@[instance_reducible]
/-
**CategoryTheory.Functor.Monoidal.ofLaxMonoidal** 是 Mathlib 中的一个定义，位于命名空间 `Categ
oryTheory.Functor.Monoidal`。
形式化陈述：{C : Type u₁} →   [inst : CategoryTheory.Category.{v₁, u₁} C] →     [inst_
1 : CategoryTheory.MonoidalCategory C] →       {D : Type u₂} →         [inst_2 :
 CategoryTheory.Category.{v₂, u₂} D] →           [inst_3 : CategoryTheory.Monoid
alCategory D] →             (F : CategoryTheory.Functor C D) →               [in
st_4 : F.LaxMonoidal] →                 [CategoryTheory.IsIso (CategoryTheory.Fu
nctor.LaxMonoidal.ε F)] →                   [∀ (X Y : C), CategoryTheory.IsIso (
CategoryTheory.Functor.LaxMonoidal.μ F X Y)] → F.Monoidal
参数：F : CategoryTheory.Functor C D；CategoryTheory.Functor.LaxMonoidal.ε F；X Y : C
；CategoryTheory.Functor.LaxMonoidal.μ F X Y。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The `Functor.Monoidal` structure given by a lax monoidal functor such
that `ε` and `μ` are isomorphisms.
-/
noncomputable def Monoidal.ofLaxMonoidal
    [F.LaxMonoidal] [IsIso (ε F)] [∀ X Y, IsIso (μ F X Y)] :=
  (CoreMonoidal.ofLaxMonoidal F).toMonoidal

/-- The `Functor.Monoidal` structure given by an oplax monoidal functor such
that `η` and `δ` are isomorphisms. -/
@[instance_reducible]
/-
**CategoryTheory.Functor.Monoidal.ofOplaxMonoidal** 是 Mathlib 中的一个定义，位于命名空间 `Cat
egoryTheory.Functor.Monoidal`。
形式化陈述：{C : Type u₁} →   [inst : CategoryTheory.Category.{v₁, u₁} C] →     [inst_
1 : CategoryTheory.MonoidalCategory C] →       {D : Type u₂} →         [inst_2 :
 CategoryTheory.Category.{v₂, u₂} D] →           [inst_3 : CategoryTheory.Monoid
alCategory D] →             (F : CategoryTheory.Functor C D) →               [in
st_4 : F.OplaxMonoidal] →                 [CategoryTheory.IsIso (CategoryTheory.
Functor.OplaxMonoidal.η F)] →                   [∀ (X Y : C), CategoryTheory.IsI
so (CategoryTheory.Functor.OplaxMonoidal.δ F X Y)] → F.Monoidal
参数：F : CategoryTheory.Functor C D；CategoryTheory.Functor.OplaxMonoidal.η F；X Y :
 C；CategoryTheory.Functor.OplaxMonoidal.δ F X Y。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The `Functor.Monoidal` structure given by an oplax monoidal functor such
that `η` and `δ` are isomorphisms.
-/
noncomputable def Monoidal.ofOplaxMonoidal
    [F.OplaxMonoidal] [IsIso (η F)] [∀ X Y, IsIso (δ F X Y)] :=
  (CoreMonoidal.ofOplaxMonoidal F).toMonoidal

section Prod

open scoped CategoryTheory.Prod

variable (F : C ⥤ D) (G : E ⥤ C') [MonoidalCategory C']

section

variable [F.LaxMonoidal] [G.LaxMonoidal]

set_option backward.defeqAttrib.useBackward true in
/-
**CategoryTheory.Functor.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Functor`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : (prod F G).LaxMonoidal where
  ε := ε F ×ₘ ε G
  μ X Y := μ F _ _ ×ₘ μ G _ _
/-
**CategoryTheory.Functor.prod_** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.Functor
`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma prod_ε_fst : (ε (prod F G)).1 = ε F := rfl
/-
**CategoryTheory.Functor.prod_** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.Functor
`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma prod_ε_snd : (ε (prod F G)).2 = ε G := rfl
/-
**CategoryTheory.Functor.prod_** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.Functor
`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma prod_μ_fst (X Y : C × E) : (μ (prod F G) X Y).1 = μ F _ _ := rfl
/-
**CategoryTheory.Functor.prod_** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.Functor
`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma prod_μ_snd (X Y : C × E) : (μ (prod F G) X Y).2 = μ G _ _ := rfl

end

section


variable [F.OplaxMonoidal] [G.OplaxMonoidal]

set_option backward.defeqAttrib.useBackward true in
/-
**CategoryTheory.Functor.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Functor`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : (prod F G).OplaxMonoidal where
  η := η F ×ₘ η G
  δ X Y := δ F _ _ ×ₘ δ G _ _
/-
**CategoryTheory.Functor.prod_** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.Functor
`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma prod_η_fst : (η (prod F G)).1 = η F := rfl
/-
**CategoryTheory.Functor.prod_** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.Functor
`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma prod_η_snd : (η (prod F G)).2 = η G := rfl
/-
**CategoryTheory.Functor.prod_** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.Functor
`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma prod_δ_fst (X Y : C × E) : (δ (prod F G) X Y).1 = δ F _ _ := rfl
/-
**CategoryTheory.Functor.prod_** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.Functor
`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma prod_δ_snd (X Y : C × E) : (δ (prod F G) X Y).2 = δ G _ _ := rfl

end

/-
**CategoryTheory.Functor.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Functor`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [F.Monoidal] [G.Monoidal] : (prod F G).Monoidal where
  ε_η := by ext <;> apply Monoidal.ε_η
  η_ε := by ext <;> apply Monoidal.η_ε
  μ_δ _ _ := by ext <;> apply Monoidal.μ_δ
  δ_μ _ _ := by ext <;> apply Monoidal.δ_μ

end Prod

set_option backward.defeqAttrib.useBackward true in
/-
**CategoryTheory.Functor.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Functor`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : (diag C).Monoidal :=
  CoreMonoidal.toMonoidal
    { εIso := Iso.refl _
      μIso := fun _ _ ↦ Iso.refl _ }
/-
**CategoryTheory.Functor.diag_** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.Functor
`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma diag_ε : ε (diag C) = 𝟙 _ := rfl
/-
**CategoryTheory.Functor.diag_** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.Functor
`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma diag_η : η (diag C) = 𝟙 _ := rfl
/-
**CategoryTheory.Functor.diag_** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.Functor
`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma diag_μ (X Y : C) : μ (diag C) X Y = 𝟙 _ := rfl
/-
**CategoryTheory.Functor.diag_** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.Functor
`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma diag_δ (X Y : C) : δ (diag C) X Y = 𝟙 _ := rfl

section Prod'

variable (F : C ⥤ D) (G : C ⥤ E)

section

variable [F.LaxMonoidal] [G.LaxMonoidal]

/-- The functor `C ⥤ D × E` obtained from two lax monoidal functors is lax monoidal. -/
/-
**CategoryTheory.Functor.LaxMonoidal.prod'** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTh
eory.Functor.LaxMonoidal`。
形式化陈述：{C : Type u₁} →   [inst : CategoryTheory.Category.{v₁, u₁} C] →     [inst_
1 : CategoryTheory.MonoidalCategory C] →       {D : Type u₂} →         [inst_2 :
 CategoryTheory.Category.{v₂, u₂} D] →           [inst_3 : CategoryTheory.Monoid
alCategory D] →             {E : Type u₃} →               [inst_4 : CategoryTheo
ry.Category.{v₃, u₃} E] →                 [inst_5 : CategoryTheory.MonoidalCateg
ory E] →                   (F : CategoryTheory.Functor C D) →                   
  (G : CategoryTheory.Functor C E) → [F.LaxMonoidal] → [G.LaxMonoidal] → (F.prod
' G).LaxMonoidal
参数：F : CategoryTheory.Functor C D；G : CategoryTheory.Functor C E；F.prod' G。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The functor `C ⥤ D × E` obtained from two lax monoidal functors is lax monoidal.
-/
instance LaxMonoidal.prod' : (prod' F G).LaxMonoidal :=
  inferInstanceAs (diag C ⋙ prod F G).LaxMonoidal

set_option backward.isDefEq.respectTransparency.types false in
/-
**CategoryTheory.Functor.prod'_** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.Functo
r`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma prod'_ε_fst : (ε (prod' F G)).1 = ε F := by
  change _ ≫ F.map (𝟙 _) = _
  rw [Functor.map_id, Category.comp_id]
  rfl

set_option backward.isDefEq.respectTransparency.types false in
/-
**CategoryTheory.Functor.prod'_** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.Functo
r`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma prod'_ε_snd : (ε (prod' F G)).2 = ε G := by
  change _ ≫ G.map (𝟙 _) = _
  rw [Functor.map_id, Category.comp_id]
  rfl

set_option backward.isDefEq.respectTransparency.types false in
/-
**CategoryTheory.Functor.prod'_** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.Functo
r`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma prod'_μ_fst (X Y : C) : (μ (prod' F G) X Y).1 = μ F X Y := by
  change _ ≫ F.map (𝟙 _) = _
  rw [Functor.map_id, Category.comp_id]
  rfl

set_option backward.isDefEq.respectTransparency.types false in
/-
**CategoryTheory.Functor.prod'_** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.Functo
r`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma prod'_μ_snd (X Y : C) : (μ (prod' F G) X Y).2 = μ G X Y := by
  change _ ≫ G.map (𝟙 _) = _
  rw [Functor.map_id, Category.comp_id]
  rfl

end

section

variable [F.OplaxMonoidal] [G.OplaxMonoidal]

/-- The functor `C ⥤ D × E` obtained from two oplax monoidal functors is oplax monoidal. -/
/-
**CategoryTheory.Functor.OplaxMonoidal.prod'** 是 Mathlib 中的一个定义，位于命名空间 `Category
Theory.Functor.OplaxMonoidal`。
形式化陈述：{C : Type u₁} →   [inst : CategoryTheory.Category.{v₁, u₁} C] →     [inst_
1 : CategoryTheory.MonoidalCategory C] →       {D : Type u₂} →         [inst_2 :
 CategoryTheory.Category.{v₂, u₂} D] →           [inst_3 : CategoryTheory.Monoid
alCategory D] →             {E : Type u₃} →               [inst_4 : CategoryTheo
ry.Category.{v₃, u₃} E] →                 [inst_5 : CategoryTheory.MonoidalCateg
ory E] →                   (F : CategoryTheory.Functor C D) →                   
  (G : CategoryTheory.Functor C E) → [F.OplaxMonoidal] → [G.OplaxMonoidal] → (F.
prod' G).OplaxMonoidal
参数：F : CategoryTheory.Functor C D；G : CategoryTheory.Functor C E；F.prod' G。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The functor `C ⥤ D × E` obtained from two oplax monoidal functors is oplax monoi
dal.
-/
instance OplaxMonoidal.prod' : (prod' F G).OplaxMonoidal :=
  inferInstanceAs (diag C ⋙ prod F G).OplaxMonoidal

set_option backward.isDefEq.respectTransparency.types false in
/-
**CategoryTheory.Functor.prod'_** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.Functo
r`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma prod'_η_fst : (η (prod' F G)).1 = η F := by
  change F.map (𝟙 _) ≫ _ = _
  rw [Functor.map_id, Category.id_comp]
  rfl

set_option backward.isDefEq.respectTransparency.types false in
/-
**CategoryTheory.Functor.prod'_** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.Functo
r`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma prod'_η_snd : (η (prod' F G)).2 = η G := by
  change G.map (𝟙 _) ≫ _ = _
  rw [Functor.map_id, Category.id_comp]
  rfl

set_option backward.isDefEq.respectTransparency.types false in
/-
**CategoryTheory.Functor.prod'_** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.Functo
r`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma prod'_δ_fst (X Y : C) : (δ (prod' F G) X Y).1 = δ F X Y := by
  change F.map (𝟙 _) ≫ _ = _
  rw [Functor.map_id, Category.id_comp]
  rfl

set_option backward.isDefEq.respectTransparency.types false in
/-
**CategoryTheory.Functor.prod'_** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.Functo
r`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma prod'_δ_snd (X Y : C) : (δ (prod' F G) X Y).2 = δ G X Y := by
  change G.map (𝟙 _) ≫ _ = _
  rw [Functor.map_id, Category.id_comp]
  rfl

end

-- TODO: when clearing these deprecations, remove the `CategoryTheory.` in the proof below.

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The functor `C ⥤ D × E` obtained from two monoidal functors is monoidal. -/
/-
**CategoryTheory.Functor.Monoidal.prod'** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheor
y.Functor.Monoidal`。
形式化陈述：{C : Type u₁} →   [inst : CategoryTheory.Category.{v₁, u₁} C] →     [inst_
1 : CategoryTheory.MonoidalCategory C] →       {D : Type u₂} →         [inst_2 :
 CategoryTheory.Category.{v₂, u₂} D] →           [inst_3 : CategoryTheory.Monoid
alCategory D] →             {E : Type u₃} →               [inst_4 : CategoryTheo
ry.Category.{v₃, u₃} E] →                 [inst_5 : CategoryTheory.MonoidalCateg
ory E] →                   (F : CategoryTheory.Functor C D) →                   
  (G : CategoryTheory.Functor C E) → [F.Monoidal] → [G.Monoidal] → (F.prod' G).M
onoidal
参数：F : CategoryTheory.Functor C D；G : CategoryTheory.Functor C E；F.prod' G。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The functor `C ⥤ D × E` obtained from two monoidal functors is monoidal.
-/
instance Monoidal.prod' [F.Monoidal] [G.Monoidal] :
    (prod' F G).Monoidal where
  -- automation should work, but it is terribly slow
  ε_η := by
    ext
    · simp only [CategoryTheory.prod_comp_fst, prod'_ε_fst, prod'_η_fst, ε_η,
        prodMonoidal_tensorUnit, prod_id]
    · simp only [CategoryTheory.prod_comp_snd, prod'_ε_snd, prod'_η_snd, ε_η,
        prodMonoidal_tensorUnit, prod_id]
  η_ε := by
    ext
    · simp only [CategoryTheory.prod_comp_fst, prod'_ε_fst, prod'_η_fst, η_ε,
        prod_id, prod'_obj]
    · simp only [CategoryTheory.prod_comp_snd, prod'_ε_snd, prod'_η_snd, η_ε,
        prod_id, prod'_obj]
  μ_δ _ _ := by
    ext
    · simp only [CategoryTheory.prod_comp_fst, prod'_μ_fst, prod'_δ_fst, μ_δ,
        prod'_obj, prodMonoidal_tensorObj, prod_id]
    · simp only [CategoryTheory.prod_comp_snd, prod'_μ_snd, prod'_δ_snd, μ_δ,
        prod'_obj, prodMonoidal_tensorObj, prod_id]
  δ_μ _ _ := by
    ext
    · simp only [CategoryTheory.prod_comp_fst, prod'_μ_fst, prod'_δ_fst, δ_μ,
        prod'_obj, prod_id]
    · simp only [CategoryTheory.prod_comp_snd, prod'_μ_snd, prod'_δ_snd, δ_μ,
        prod'_obj, prod_id]

end Prod'

end Functor

namespace Adjunction

variable {F : C ⥤ D} {G : D ⥤ C} (adj : F ⊣ G)

open Functor.OplaxMonoidal Functor.LaxMonoidal

section LaxMonoidal
variable [F.OplaxMonoidal]

set_option backward.defeqAttrib.useBackward true in
/-- The right adjoint of an oplax monoidal functor is lax monoidal. -/
@[simps -isSimp, instance_reducible]
/-
**CategoryTheory.Adjunction.rightAdjointLaxMonoidal** 是 Mathlib 中的一个定义，位于命名空间 `C
ategoryTheory.Adjunction`。
形式化陈述：rightAdjointLaxMonoidal : G.LaxMonoidal where ε
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The right adjoint of an oplax monoidal functor is lax monoidal.
-/
def rightAdjointLaxMonoidal : G.LaxMonoidal where
  ε := adj.homEquiv _ _ (η F)
  μ X Y := adj.homEquiv _ _ (δ F _ _ ≫ (adj.counit.app X ⊗ₘ adj.counit.app Y))
  μ_natural_left {X Y} f X' := by
    simp only [Adjunction.homEquiv_apply, ← adj.unit_naturality_assoc, ← G.map_comp, assoc,
      ← δ_natural_left_assoc F]
    suffices F.map (G.map f) ▷ F.obj (G.obj X') ≫ _ =
      (adj.counit.app X ⊗ₘ adj.counit.app X') ≫ _ by rw [this]
    simpa using NatTrans.whiskerRight_app_tensor_app adj.counit adj.counit (f := f) X'
  μ_natural_right {X' Y'} X g := by
    simp only [Adjunction.homEquiv_apply, ← adj.unit_naturality_assoc, ← G.map_comp,
      assoc, ← δ_natural_right_assoc F]
    suffices F.obj (G.obj X) ◁ F.map (G.map g) ≫ _ =
      (adj.counit.app X ⊗ₘ adj.counit.app X') ≫ _ by rw [this]
    simpa using NatTrans.whiskerLeft_app_tensor_app adj.counit adj.counit (f := g) _
  associativity X Y Z := (adj.homEquiv _ _).symm.injective (by
    simp only [homEquiv_unit, comp_obj, map_comp, comp_whiskerRight, assoc, homEquiv_counit,
      counit_naturality, counit_naturality_assoc, left_triangle_components_assoc,
      MonoidalCategory.whiskerLeft_comp]
    rw [← δ_natural_left_assoc, ← δ_natural_left_assoc, ← δ_natural_left_assoc]
    have := @NatTrans.whiskerRight_app_tensor_app_assoc _ _ _ _ _ _ _ _ _ adj.counit adj.counit
    dsimp only [id_obj, comp_obj, Functor.comp_map, Functor.id_map] at this
    rw [this, this, tensorHom_def, assoc, ← comp_whiskerRight_assoc,
      left_triangle_components, id_whiskerRight, id_comp,
      whisker_exchange_assoc, whisker_exchange_assoc, ← tensorHom_def_assoc,
      associator_naturality, OplaxMonoidal.associativity_assoc]
    rw [← δ_natural_right_assoc, ← δ_natural_right_assoc, ← δ_natural_right_assoc]
    nth_rw 4 [tensorHom_def]
    rw [← whisker_exchange, ← MonoidalCategory.whiskerLeft_comp_assoc,
      ← MonoidalCategory.whiskerLeft_comp_assoc,
      ← MonoidalCategory.whiskerLeft_comp_assoc, assoc, assoc,
      counit_naturality, counit_naturality_assoc, left_triangle_components_assoc,
      MonoidalCategory.whiskerLeft_comp, assoc, tensorHom_def, whisker_exchange])
  left_unitality X := (adj.homEquiv _ _).symm.injective (by
    rw [homEquiv_counit, homEquiv_counit, homEquiv_unit, homEquiv_unit, comp_whiskerRight,
      map_comp, map_comp, map_comp, map_comp, map_comp, map_comp, assoc, assoc, assoc, assoc,
      assoc, counit_naturality, counit_naturality_assoc, counit_naturality_assoc,
      left_triangle_components_assoc, ← δ_natural_left_assoc, ← δ_natural_left_assoc,
      tensorHom_def, assoc, ← MonoidalCategory.comp_whiskerRight_assoc,
      ← MonoidalCategory.comp_whiskerRight_assoc, assoc, counit_naturality,
      left_triangle_components_assoc, id_whiskerLeft, assoc, assoc, Iso.inv_hom_id, comp_id,
      left_unitality_hom_assoc])
  right_unitality X := (adj.homEquiv _ _).symm.injective (by
    rw [homEquiv_counit, homEquiv_unit, MonoidalCategory.whiskerLeft_comp, homEquiv_unit,
      homEquiv_counit, map_comp, map_comp, map_comp, map_comp, map_comp, map_comp,
      assoc, assoc, assoc, assoc, assoc, counit_naturality, counit_naturality_assoc,
      counit_naturality_assoc, left_triangle_components_assoc, ← δ_natural_right_assoc,
      ← δ_natural_right_assoc, tensorHom_def, assoc, ← whisker_exchange_assoc,
      ← MonoidalCategory.whiskerLeft_comp_assoc, ← MonoidalCategory.whiskerLeft_comp_assoc,
      assoc, counit_naturality, left_triangle_components_assoc, MonoidalCategory.whiskerRight_id,
      assoc, assoc, Iso.inv_hom_id, comp_id, right_unitality_hom_assoc])

/-- When `adj : F ⊣ G` is an adjunction, with `F` oplax monoidal and `G` lax-monoidal,
this typeclass expresses compatibilities between the adjunction and the (op)lax
monoidal structures. -/
/-
**CategoryTheory.Adjunction.IsMonoidal** 是 Mathlib 中的一个类，位于命名空间 `CategoryTheory.
Adjunction`。
形式化陈述：IsMonoidal [G.LaxMonoidal] : Prop where leftAdjoint_ε : ε G = adj.unit.app
 _ ≫ G.map (η F)
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
When `adj : F ⊣ G` is an adjunction, with `F` oplax monoidal and `G` lax-monoida
l,
this typeclass expresses compatibilities between the adjunction and the (op)lax
monoidal structures.
-/
class IsMonoidal [G.LaxMonoidal] : Prop where
  leftAdjoint_ε : ε G = adj.unit.app _ ≫ G.map (η F) := by cat_disch
  leftAdjoint_μ (X Y : D) : μ G X Y =
    adj.unit.app _ ≫ G.map (δ F _ _ ≫ (adj.counit.app X ⊗ₘ adj.counit.app Y)) := by cat_disch
/-
**CategoryTheory.Adjunction.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Adjunctio
n`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance :
    letI := adj.rightAdjointLaxMonoidal
    adj.IsMonoidal := by
  let := adj.rightAdjointLaxMonoidal
  constructor
  · rfl
  · intro _ _
    rfl

variable [G.LaxMonoidal] [adj.IsMonoidal]

@[reassoc]
/-
**CategoryTheory.Adjunction.unit_app_unit_comp_map_** 是 Mathlib 中的一个引理，位于命名空间 `C
ategoryTheory.Adjunction`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma unit_app_unit_comp_map_η : adj.unit.app (𝟙_ C) ≫ G.map (η F) = ε G :=
  Adjunction.IsMonoidal.leftAdjoint_ε.symm

set_option backward.defeqAttrib.useBackward true in
@[reassoc]
/-
**CategoryTheory.Adjunction.unit_app_tensor_comp_map_** 是 Mathlib 中的一个引理，位于命名空间 
`CategoryTheory.Adjunction`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma unit_app_tensor_comp_map_δ (X Y : C) :
    adj.unit.app (X ⊗ Y) ≫ G.map (δ F X Y) = (adj.unit.app X ⊗ₘ adj.unit.app Y) ≫ μ G _ _ := by
  simp [IsMonoidal.leftAdjoint_μ (adj := adj), ← adj.unit_naturality_assoc,
    ← Functor.map_comp, ← δ_natural_assoc]

set_option backward.defeqAttrib.useBackward true in
@[reassoc]
/-
**CategoryTheory.Adjunction.map_** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.Adjun
ction`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma map_ε_comp_counit_app_unit : F.map (ε G) ≫ adj.counit.app (𝟙_ D) = η F := by
  simp [IsMonoidal.leftAdjoint_ε (adj := adj)]

set_option backward.defeqAttrib.useBackward true in
@[reassoc]
/-
**CategoryTheory.Adjunction.map_** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.Adjun
ction`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma map_μ_comp_counit_app_tensor (X Y : D) :
    F.map (μ G X Y) ≫ adj.counit.app (X ⊗ Y) =
      δ F _ _ ≫ (adj.counit.app X ⊗ₘ adj.counit.app Y) := by
  simp [IsMonoidal.leftAdjoint_μ (adj := adj)]

set_option backward.defeqAttrib.useBackward true in
/-
**CategoryTheory.Adjunction.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Adjunctio
n`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : (Adjunction.id (C := C)).IsMonoidal where

set_option backward.defeqAttrib.useBackward true in
/-
**CategoryTheory.Adjunction.isMonoidal_comp** 是 Mathlib 中的一个实例，位于命名空间 `CategoryT
heory.Adjunction`。
形式化陈述：isMonoidal_comp {F' : D ⥤ E} {G' : E ⥤ D} (adj' : F' ⊣ G') [F'.OplaxMonoid
al] [G'.LaxMonoidal] [adj'.IsMonoidal] : (adj.comp adj').IsMonoidal where leftAd
joint_ε
参数：adj' : F' ⊣ G'。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Adjunction.IsMonoidal.leftAdjoint_ε`：∀ {C : Type u₁} {ins
t : CategoryTheory.Category.{v₁, u₁} C} {inst_1 : CategoryTheory.MonoidalCategor
y C} {D : Type u₂}   {inst_2 : CategoryT…
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.Adjunction.unit_naturality_assoc`：∀ {C : Type u₁} [inst :
 CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Cate
gory.{v₂, u₂} D]   {F : CategoryTheor…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用引理 `CategoryTheory.Adjunction.comp_unit_app`：comp_unit_app (X : C) : dsimp% 
(adj₁.comp adj₂).unit.app X = adj₁.unit.app X ≫ G.map (adj₂.unit.app (F.obj X))
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `CategoryTheory.Adjunction.IsMonoidal.leftAdjoint_μ`：∀ {C : Type u₁} {ins
t : CategoryTheory.Category.{v₁, u₁} C} {inst_1 : CategoryTheory.MonoidalCategor
y C} {D : Type u₂}   {inst_2 : CategoryT…
· 使用引理 `CategoryTheory.Adjunction.comp_counit_app`：comp_counit_app (X : E) : dsi
mp% (adj₁.comp adj₂).counit.app X = H.map (adj₁.counit.app (I.obj X)) ≫ adj₂.cou
nit.app X
· 使用定理 `CategoryTheory.Functor.OplaxMonoidal.δ_natural_assoc`：∀ {C : Type u₁} [i
nst : CategoryTheory.Category.{v₁, u₁} C] [inst_1 : CategoryTheory.MonoidalCateg
ory C] {D : Type u₂}   [inst_2 : CategoryT…
· 使用定理 `CategoryTheory.Functor.map_comp`：∀ {C : Type u₁} [inst : CategoryTheory.
Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]
   (self : CategoryTh…
-/
instance isMonoidal_comp {F' : D ⥤ E} {G' : E ⥤ D} (adj' : F' ⊣ G')
    [F'.OplaxMonoidal] [G'.LaxMonoidal] [adj'.IsMonoidal] : (adj.comp adj').IsMonoidal where
  leftAdjoint_ε := by
    simp [IsMonoidal.leftAdjoint_ε (adj := adj'), IsMonoidal.leftAdjoint_ε (adj := adj),
      ← map_comp, ← adj'.unit_naturality_assoc]
  leftAdjoint_μ X Y := by
    simp only [comp_obj, comp_μ, IsMonoidal.leftAdjoint_μ (adj := adj), id_obj,
      IsMonoidal.leftAdjoint_μ (adj := adj'), assoc, ← map_comp, comp_unit_app, comp_δ,
      comp_counit_app, ← tensorHom_comp_tensorHom, δ_natural_assoc, Functor.comp_map]
    simp

end LaxMonoidal

section OplaxMonoidal
variable [G.LaxMonoidal]

set_option backward.defeqAttrib.useBackward true in
/-- The left adjoint of a lax monoidal functor is oplax monoidal. -/
@[simps -isSimp, instance_reducible]
/-
**CategoryTheory.Adjunction.leftAdjointOplaxMonoidal** 是 Mathlib 中的一个定义，位于命名空间 `
CategoryTheory.Adjunction`。
形式化陈述：leftAdjointOplaxMonoidal : F.OplaxMonoidal where η
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s

--- 原说明 ---
The left adjoint of a lax monoidal functor is oplax monoidal.
-/
def leftAdjointOplaxMonoidal : F.OplaxMonoidal where
  η := (adj.homEquiv _ _).symm (ε G)
  δ X Y := (adj.homEquiv _ _).symm ((adj.unit.app X ⊗ₘ adj.unit.app Y) ≫ μ G _ _)
  δ_natural_left _ _ := by
    rw [← Adjunction.homEquiv_naturality_right_symm,
      ← Adjunction.homEquiv_naturality_left_symm, assoc, ← μ_natural_left]
    simp [← tensorHom_id]
  δ_natural_right _ _ := by
    rw [← Adjunction.homEquiv_naturality_right_symm,
      ← Adjunction.homEquiv_naturality_left_symm, assoc, ← μ_natural_right]
    simp [← id_tensorHom]
  oplax_associativity X Y Z := (adj.homEquiv _ _).injective (by
    rw [← Adjunction.homEquiv_naturality_right_symm,
      ← Adjunction.homEquiv_naturality_right_symm,
      ← Adjunction.homEquiv_naturality_left_symm,
      Equiv.apply_symm_apply, Equiv.apply_symm_apply, assoc, assoc]
    conv_lhs =>
      rw [homEquiv_counit, map_comp_assoc, map_comp,
        ← μ_natural_left_assoc, map_comp, map_comp, tensorHom_def'_assoc]
      dsimp
      rw [← comp_whiskerRight_assoc]
    conv_rhs =>
      rw [← μ_natural_right, homEquiv_counit, map_comp_assoc,
        map_comp, tensorHom_def_assoc, ← associator_naturality_left_assoc]
      dsimp
      rw [← MonoidalCategory.whiskerLeft_comp_assoc, map_comp,
        unit_naturality_assoc, MonoidalCategory.whiskerLeft_comp,
        unit_naturality_assoc, right_triangle_components, comp_id, assoc,
        tensorHom_def, MonoidalCategory.whiskerLeft_comp_assoc,
        ← associator_naturality_middle_assoc, ← associator_naturality_right_assoc,
        ← associativity G, ← comp_whiskerRight_assoc, ← tensorHom_def,
        ← whisker_exchange_assoc, ← comp_whiskerRight_assoc]
    simp)
  oplax_left_unitality _ := (adj.homEquiv _ _).injective (by
    rw [Adjunction.homEquiv_naturality_left, Adjunction.homEquiv_naturality_right,
      Equiv.apply_symm_apply, assoc, ← μ_natural_left, ← tensorHom_id,
      tensorHom_comp_tensorHom_assoc]
    simp [tensorHom_def', homEquiv_unit, homEquiv_counit])
  oplax_right_unitality _ := (adj.homEquiv _ _).injective (by
    rw [Adjunction.homEquiv_naturality_left, Adjunction.homEquiv_naturality_right,
      Equiv.apply_symm_apply, assoc, ← μ_natural_right, ← id_tensorHom,
      tensorHom_comp_tensorHom_assoc]
    simp [tensorHom_def, homEquiv_unit, homEquiv_counit])

set_option backward.defeqAttrib.useBackward true in
/-
**CategoryTheory.Adjunction.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Adjunctio
n`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance :
    letI := adj.leftAdjointOplaxMonoidal
    adj.IsMonoidal := by
  let := adj.leftAdjointOplaxMonoidal
  refine ⟨?_, fun X Y ↦ ?_⟩
  · simp [homEquiv_counit, leftAdjointOplaxMonoidal_η]
  · simp [homEquiv_counit, ← μ_natural, leftAdjointOplaxMonoidal_δ]

end OplaxMonoidal

set_option backward.defeqAttrib.useBackward true in
attribute [local simp] leftAdjointOplaxMonoidal_η leftAdjointOplaxMonoidal_δ
  rightAdjointLaxMonoidal_ε rightAdjointLaxMonoidal_μ in
/-- If `F ⊣ G` is an adjunction, the `G` is lax monoidal iff `F` is oplax monoidal.
It is advisable to use `Adjunction.leftAdjointOplaxMonoidal` and
`Adjunction.rightAdjointLaxMonoidal`, because compatibilities between
the oplax monoidal left adjoint and the lax monoidal right adjoint
(`Adjunction.IsMonoidal`) have been stated for these definitions. -/
/-
**CategoryTheory.Adjunction.laxMonoidalEquivOplaxMonoidal** 是 Mathlib 中的一个定义，位于命
名空间 `CategoryTheory.Adjunction`。
形式化陈述：laxMonoidalEquivOplaxMonoidal : G.LaxMonoidal ≃ F.OplaxMonoidal where toFu
n _
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `F ⊣ G` is an adjunction, the `G` is lax monoidal iff `F` is oplax monoidal.
It is advisable to use `Adjunction.leftAdjointOplaxMonoidal` and
`Adjunction.rightAdjointLaxMonoidal`, because compatibilities between
the oplax monoidal left adjoint and the lax monoidal right adjoint
(`Adjunction.IsMonoidal`) have been stated for these definitions.
-/
def laxMonoidalEquivOplaxMonoidal : G.LaxMonoidal ≃ F.OplaxMonoidal where
  toFun _ := adj.leftAdjointOplaxMonoidal
  invFun _ := adj.rightAdjointLaxMonoidal
  left_inv _ := by
    ext
    · simp
    · simp [homEquiv_counit, homEquiv_unit, ← μ_natural]
  right_inv _ := by
    ext
    · simp
    · simp [homEquiv_counit, homEquiv_unit, ← δ_natural_assoc]

section Monoidal
variable [F.Monoidal] [G.Monoidal] [adj.IsMonoidal]

set_option backward.defeqAttrib.useBackward true in
@[reassoc]
/-
**CategoryTheory.Adjunction.** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.Adjunctio
n`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma ε_comp_map_ε : ε G ≫ G.map (ε F) = adj.unit.app (𝟙_ C) := by
  simp [← adj.unit_app_unit_comp_map_η]

@[reassoc]
/-
**CategoryTheory.Adjunction.map_** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.Adjun
ction`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma map_η_comp_η : F.map (η G) ≫ η F = adj.counit.app (𝟙_ D) := by
  simp [← adj.map_ε_comp_counit_app_unit]

end Monoidal
end Adjunction

namespace Equivalence

variable (e : C ≌ D)

/-
**CategoryTheory.Equivalence.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Equivale
nce`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [e.inverse.Monoidal] : e.symm.functor.Monoidal := inferInstanceAs (e.inverse.Monoidal)
/-
**CategoryTheory.Equivalence.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Equivale
nce`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [e.functor.Monoidal] : e.symm.inverse.Monoidal := inferInstanceAs (e.functor.Monoidal)

/-- If a monoidal functor `F` is an equivalence of categories then its inverse is also monoidal. -/
@[instance_reducible]
/-
**CategoryTheory.Equivalence.inverseMonoidal** 是 Mathlib 中的一个定义，位于命名空间 `Category
Theory.Equivalence`。
形式化陈述：inverseMonoidal [e.functor.Monoidal] : e.inverse.Monoidal
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If a monoidal functor `F` is an equivalence of categories then its inverse is al
so monoidal.
-/
noncomputable def inverseMonoidal [e.functor.Monoidal] : e.inverse.Monoidal := by
  letI := e.toAdjunction.rightAdjointLaxMonoidal
  have : IsIso (LaxMonoidal.ε e.inverse) := by
    simp only [this, Adjunction.rightAdjointLaxMonoidal_ε, Adjunction.homEquiv_unit]
    infer_instance
  have : ∀ (X Y : D), IsIso (LaxMonoidal.μ e.inverse X Y) := fun X Y ↦ by
    simp only [Adjunction.rightAdjointLaxMonoidal_μ, Adjunction.homEquiv_unit]
    infer_instance
  apply Monoidal.ofLaxMonoidal

/-- An equivalence of categories involving monoidal functors is monoidal if the underlying
adjunction satisfies certain compatibilities with respect to the monoidal functor data. -/
/-
**CategoryTheory.Equivalence.IsMonoidal** 是 Mathlib 中的一个缩写定义，位于命名空间 `CategoryThe
ory.Equivalence`。
形式化陈述：IsMonoidal [e.functor.Monoidal] [e.inverse.Monoidal] : Prop
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An equivalence of categories involving monoidal functors is monoidal if the unde
rlying
adjunction satisfies certain compatibilities with respect to the monoidal functo
r data.
-/
abbrev IsMonoidal [e.functor.Monoidal] [e.inverse.Monoidal] : Prop := e.toAdjunction.IsMonoidal

set_option backward.isDefEq.respectTransparency false in
/-
**CategoryTheory.Equivalence.** 是 Mathlib 中的一个示例，位于命名空间 `CategoryTheory.Equivale
nce`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
example [e.functor.Monoidal] : letI := e.inverseMonoidal; e.IsMonoidal := inferInstance

variable [e.functor.Monoidal] [e.inverse.Monoidal] [e.IsMonoidal]

open Functor.LaxMonoidal Functor.OplaxMonoidal

@[reassoc]
/-
**CategoryTheory.Equivalence.unitIso_hom_app_comp_inverse_map_** 是 Mathlib 中的一个引
理，位于命名空间 `CategoryTheory.Equivalence`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma unitIso_hom_app_comp_inverse_map_η_functor :
    e.unitIso.hom.app (𝟙_ C) ≫ e.inverse.map (η e.functor) = ε e.inverse :=
  e.toAdjunction.unit_app_unit_comp_map_η

@[reassoc]
/-
**CategoryTheory.Equivalence.unitIso_hom_app_tensor_comp_inverse_map_** 是 Mathli
b 中的一个引理，位于命名空间 `CategoryTheory.Equivalence`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma unitIso_hom_app_tensor_comp_inverse_map_δ_functor (X Y : C) :
    e.unitIso.hom.app (X ⊗ Y) ≫ e.inverse.map (δ e.functor X Y) =
      (e.unitIso.hom.app X ⊗ₘ e.unitIso.hom.app Y) ≫ μ e.inverse _ _ :=
  e.toAdjunction.unit_app_tensor_comp_map_δ X Y

@[reassoc]
/-
**CategoryTheory.Equivalence.functor_map_** 是 Mathlib 中的一个引理，位于命名空间 `CategoryThe
ory.Equivalence`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma functor_map_ε_inverse_comp_counitIso_hom_app :
    e.functor.map (ε e.inverse) ≫ e.counitIso.hom.app (𝟙_ D) = η e.functor :=
  e.toAdjunction.map_ε_comp_counit_app_unit

@[reassoc]
/-
**CategoryTheory.Equivalence.functor_map_** 是 Mathlib 中的一个引理，位于命名空间 `CategoryThe
ory.Equivalence`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma functor_map_μ_inverse_comp_counitIso_hom_app_tensor (X Y : D) :
    e.functor.map (μ e.inverse X Y) ≫ e.counitIso.hom.app (X ⊗ Y) =
      δ e.functor _ _ ≫ (e.counitIso.hom.app X ⊗ₘ e.counitIso.hom.app Y) :=
  e.toAdjunction.map_μ_comp_counit_app_tensor X Y

@[reassoc]
/-
**CategoryTheory.Equivalence.counitIso_inv_app_comp_functor_map_** 是 Mathlib 中的一
个引理，位于命名空间 `CategoryTheory.Equivalence`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma counitIso_inv_app_comp_functor_map_η_inverse :
    e.counitIso.inv.app (𝟙_ D) ≫ e.functor.map (η e.inverse) = ε e.functor := by
  rw [← cancel_epi (η e.functor), Monoidal.η_ε, ← functor_map_ε_inverse_comp_counitIso_hom_app,
    Category.assoc, Iso.hom_inv_id_app_assoc, Monoidal.map_ε_η]

set_option backward.defeqAttrib.useBackward true in
@[reassoc]
/-
**CategoryTheory.Equivalence.counitIso_inv_app_tensor_comp_functor_map_** 是 Math
lib 中的一个引理，位于命名空间 `CategoryTheory.Equivalence`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma counitIso_inv_app_tensor_comp_functor_map_δ_inverse (X Y : C) :
    e.counitIso.inv.app (e.functor.obj X ⊗ e.functor.obj Y) ≫
      e.functor.map (δ e.inverse (e.functor.obj X) (e.functor.obj Y)) =
      μ e.functor X Y ≫ e.functor.map (e.unitIso.hom.app X ⊗ₘ e.unitIso.hom.app Y) := by
  rw [← cancel_epi (δ e.functor _ _), Monoidal.δ_μ_assoc]
  apply e.inverse.map_injective
  simp [← cancel_epi (e.unitIso.hom.app (X ⊗ Y)), Functor.map_comp,
    unitIso_hom_app_tensor_comp_inverse_map_δ_functor_assoc]

@[reassoc]
/-
**CategoryTheory.Equivalence.unit_app_comp_inverse_map_** 是 Mathlib 中的一个引理，位于命名空
间 `CategoryTheory.Equivalence`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma unit_app_comp_inverse_map_η_functor :
    e.unit.app (𝟙_ C) ≫ e.inverse.map (η e.functor) = ε e.inverse :=
  e.toAdjunction.unit_app_unit_comp_map_η

@[reassoc]
/-
**CategoryTheory.Equivalence.unit_app_tensor_comp_inverse_map_** 是 Mathlib 中的一个引
理，位于命名空间 `CategoryTheory.Equivalence`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma unit_app_tensor_comp_inverse_map_δ_functor (X Y : C) :
    e.unit.app (X ⊗ Y) ≫ e.inverse.map (δ e.functor X Y) =
      (e.unit.app X ⊗ₘ e.unitIso.hom.app Y) ≫ μ e.inverse _ _ :=
  e.toAdjunction.unit_app_tensor_comp_map_δ X Y

@[reassoc (attr := simp)]
/-
**CategoryTheory.Equivalence.functor_map_** 是 Mathlib 中的一个引理，位于命名空间 `CategoryThe
ory.Equivalence`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma functor_map_ε_inverse_comp_counit_app :
    e.functor.map (ε e.inverse) ≫ e.counit.app (𝟙_ D) = η e.functor :=
  e.toAdjunction.map_ε_comp_counit_app_unit

@[reassoc]
/-
**CategoryTheory.Equivalence.functor_map_** 是 Mathlib 中的一个引理，位于命名空间 `CategoryThe
ory.Equivalence`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma functor_map_μ_inverse_comp_counit_app_tensor (X Y : D) :
    e.functor.map (μ e.inverse X Y) ≫ e.counit.app (X ⊗ Y) =
      δ e.functor _ _ ≫ (e.counit.app X ⊗ₘ e.counit.app Y) :=
  e.toAdjunction.map_μ_comp_counit_app_tensor X Y

@[reassoc]
/-
**CategoryTheory.Equivalence.counitInv_app_comp_functor_map_** 是 Mathlib 中的一个引理，
位于命名空间 `CategoryTheory.Equivalence`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma counitInv_app_comp_functor_map_η_inverse :
    e.counitInv.app (𝟙_ D) ≫ e.functor.map (η e.inverse) = ε e.functor := by
  rw [← cancel_epi (η e.functor), Monoidal.η_ε, ← functor_map_ε_inverse_comp_counitIso_hom_app,
    Category.assoc, Iso.hom_inv_id_app_assoc, Monoidal.map_ε_η]

@[reassoc]
/-
**CategoryTheory.Equivalence.counitInv_app_tensor_comp_functor_map_** 是 Mathlib 
中的一个引理，位于命名空间 `CategoryTheory.Equivalence`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma counitInv_app_tensor_comp_functor_map_δ_inverse (X Y : C) :
    e.counitInv.app (e.functor.obj X ⊗ e.functor.obj Y) ≫
      e.functor.map (δ e.inverse (e.functor.obj X) (e.functor.obj Y)) =
      μ e.functor X Y ≫ e.functor.map (e.unitIso.hom.app X ⊗ₘ e.unitIso.hom.app Y) :=
  counitIso_inv_app_tensor_comp_functor_map_δ_inverse e X Y

@[reassoc (attr := simp)]
/-
**CategoryTheory.Equivalence.** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.Equivale
nce`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma ε_comp_map_ε : ε e.inverse ≫ e.inverse.map (ε e.functor) = e.unit.app (𝟙_ C) :=
  e.toAdjunction.ε_comp_map_ε

@[reassoc (attr := simp)]
/-
**CategoryTheory.Equivalence.map_** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.Equi
valence`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma map_η_comp_η : e.functor.map (η e.inverse) ≫ η e.functor = e.counit.app (𝟙_ D) :=
  e.toAdjunction.map_η_comp_η
/-
**CategoryTheory.Equivalence.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Equivale
nce`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : (refl (C := C)).functor.Monoidal := inferInstanceAs (𝟭 C).Monoidal
/-
**CategoryTheory.Equivalence.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Equivale
nce`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : (refl (C := C)).inverse.Monoidal := inferInstanceAs (𝟭 C).Monoidal

/-- The obvious auto-equivalence of a monoidal category is monoidal. -/
/-
**CategoryTheory.Equivalence.isMonoidal_refl** 是 Mathlib 中的一个实例，位于命名空间 `Category
Theory.Equivalence`。
形式化陈述：isMonoidal_refl : (Equivalence.refl (C
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The obvious auto-equivalence of a monoidal category is monoidal.
-/
instance isMonoidal_refl : (Equivalence.refl (C := C)).IsMonoidal :=
  inferInstanceAs (Adjunction.id (C := C)).IsMonoidal

set_option backward.isDefEq.respectTransparency false in
/-- The inverse of a monoidal category equivalence is also a monoidal category equivalence. -/
/-
**CategoryTheory.Equivalence.isMonoidal_symm** 是 Mathlib 中的一个实例，位于命名空间 `Category
Theory.Equivalence`。
形式化陈述：isMonoidal_symm : e.symm.IsMonoidal where leftAdjoint_ε
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `CategoryTheory.Equivalence.counitIso_inv_app_comp_functor_map_η_inverse`
：counitIso_inv_app_comp_functor_map_η_inverse : e.counitIso.inv.app (𝟙_ D) ≫ e.f
unctor.map (η e.inverse) = ε e.functor
· 使用定理 `CategoryTheory.Functor.map_comp`：∀ {C : Type u₁} [inst : CategoryTheory.
Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]
   (self : CategoryTh…
· 使用定理 `CategoryTheory.Equivalence.counitIso_inv_app_tensor_comp_functor_map_δ_i
nverse_assoc`：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] [inst_
1 : CategoryTheory.MonoidalCategory C] {D : Type u₂}   [inst_2 : CategoryT…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `CategoryTheory.MonoidalCategory.tensorHom_comp_tensorHom`：∀ {C : Type u}
 {𝒞 : CategoryTheory.Category.{v, u} C} [self : CategoryTheory.MonoidalCategory 
C] {X₁ Y₁ Z₁ X₂ Y₂ Z₂ : C}   (f₁ : X₁ ⟶ Y₁) (f…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `CategoryTheory.Iso.hom_inv_id_app`：∀ {C : Type u₁} [inst : CategoryTheor
y.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} 
D]   {F G : CategoryThe…
· 使用定理 `CategoryTheory.MonoidalCategory.tensorHom_id`：tensorHom_id {X₁ X₂ : C} (
f : X₁ ⟶ X₂) (Y : C) : f otimesₘ 𝟙 Y = f ▷ Y
· 使用定理 `CategoryTheory.MonoidalCategory.id_whiskerRight`：∀ {C : Type u} {𝒞 : Cat
egoryTheory.Category.{v, u} C} [self : CategoryTheory.MonoidalCategory C] (X Y :
 C),   CategoryTheory.MonoidalCategor…
· 使用定理 `CategoryTheory.Functor.map_id`：∀ {C : Type u₁} [inst : CategoryTheory.Ca
tegory.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]  
 (self : CategoryTh…
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
The inverse of a monoidal category equivalence is also a monoidal category equiv
alence.
-/
instance isMonoidal_symm : e.symm.IsMonoidal where
  leftAdjoint_ε := by
    simp only [toAdjunction]
    dsimp [symm]
    rw [counitIso_inv_app_comp_functor_map_η_inverse]
  leftAdjoint_μ X Y := by
    simp only [toAdjunction]
    dsimp [symm]
    rw [map_comp, counitIso_inv_app_tensor_comp_functor_map_δ_inverse_assoc]
    simp [← map_comp]

section

variable (e' : D ≌ E)

/-
**CategoryTheory.Equivalence.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Equivale
nce`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [e'.functor.Monoidal] : (e.trans e').functor.Monoidal :=
  inferInstanceAs (e.functor ⋙ e'.functor).Monoidal
/-
**CategoryTheory.Equivalence.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Equivale
nce`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [e'.inverse.Monoidal] : (e.trans e').inverse.Monoidal :=
  inferInstanceAs (e'.inverse ⋙ e.inverse).Monoidal

set_option backward.isDefEq.respectTransparency false in
/-- The composition of two monoidal category equivalences is monoidal. -/
/-
**CategoryTheory.Equivalence.isMonoidal_trans** 是 Mathlib 中的一个实例，位于命名空间 `Categor
yTheory.Equivalence`。
形式化陈述：isMonoidal_trans [e'.functor.Monoidal] [e'.inverse.Monoidal] [e'.IsMonoida
l] : (e.trans e').IsMonoidal
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `CategoryTheory.Equivalence.trans_toAdjunction`：trans_toAdjunction {E : T
ype*} [Category* E] (e' : D ≌ E) : (e.trans e').toAdjunction = e.toAdjunction.co
mp e'.toAdjunction

--- 原说明 ---
The composition of two monoidal category equivalences is monoidal.
-/
instance isMonoidal_trans [e'.functor.Monoidal] [e'.inverse.Monoidal] [e'.IsMonoidal] :
    (e.trans e').IsMonoidal := by
  dsimp [Equivalence.IsMonoidal]
  rw [trans_toAdjunction]
  infer_instance

end

end Equivalence

variable (C D)

/-- Bundled version of lax monoidal functors. This type is equipped with a category
/-
**CategoryTheory.in** 是 Mathlib 中的一个结构，位于命名空间 `CategoryTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
structure in `CategoryTheory.Monoidal.NaturalTransformation`. -/
/-
**CategoryTheory.LaxMonoidalFunctor** 是 Mathlib 中的一个结构，位于命名空间 `CategoryTheory`。
形式化陈述：LaxMonoidalFunctor extends C ⥤ D where laxMonoidal : toFunctor.LaxMonoidal
继承自：C ⥤ D。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Bundled version of lax monoidal functors. This type is equipped with a category
structure in `CategoryTheory.Monoidal.NaturalTransformation`.
-/
structure LaxMonoidalFunctor extends C ⥤ D where
  laxMonoidal : toFunctor.LaxMonoidal := by infer_instance

namespace LaxMonoidalFunctor

attribute [instance] laxMonoidal

variable {C D}

/-- Constructor for `LaxMonoidalFunctor C D`. -/
@[simps toFunctor]
/-
**CategoryTheory.LaxMonoidalFunctor.of** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory
.LaxMonoidalFunctor`。
形式化陈述：of (F : C ⥤ D) [F.LaxMonoidal] : LaxMonoidalFunctor C D where toFunctor
参数：F : C ⥤ D。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Constructor for `LaxMonoidalFunctor C D`.
-/
def of (F : C ⥤ D) [F.LaxMonoidal] : LaxMonoidalFunctor C D where
  toFunctor := F

end LaxMonoidalFunctor

namespace Functor.Monoidal

variable {C D}

/--
Auxiliary definition for `Functor.Monoidal.transport`
-/
@[simps!]
/-
**CategoryTheory.Functor.Monoidal.coreMonoidalTransport** 是 Mathlib 中的一个定义，位于命名空
间 `CategoryTheory.Functor.Monoidal`。
形式化陈述：coreMonoidalTransport {F G : C ⥤ D} [F.Monoidal] (i : F ≅ G) : G.CoreMonoi
dal where εIso
参数：i : F ≅ G。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Auxiliary definition for `Functor.Monoidal.transport`
-/
def coreMonoidalTransport {F G : C ⥤ D} [F.Monoidal] (i : F ≅ G) : G.CoreMonoidal where
  εIso := εIso F ≪≫ i.app _
  μIso X Y := tensorIso (i.symm.app _) (i.symm.app _) ≪≫ μIso F X Y ≪≫ i.app _
  μIso_hom_natural_left _ _ := by simp [NatTrans.whiskerRight_app_tensor_app_assoc]
  μIso_hom_natural_right _ _ := by simp [NatTrans.whiskerLeft_app_tensor_app_assoc]
  associativity X Y Z := by
    simp only [Iso.trans_hom, tensorIso_hom, Iso.app_hom, Iso.symm_hom, μIso_hom, comp_whiskerRight,
      Category.assoc, MonoidalCategory.whiskerLeft_comp]
    rw [← i.hom.naturality, map_associator_assoc, Functor.OplaxMonoidal.associativity_assoc,
      whiskerLeft_δ_μ_assoc, δ_μ_assoc]
    simp only [← Category.assoc]
    congr 1
    slice_lhs 3 4 =>
      rw [← tensorHom_id, tensorHom_comp_tensorHom]
      simp only [Iso.hom_inv_id_app, Category.id_comp, id_tensorHom]
    simp only [Category.assoc]
    rw [← whisker_exchange_assoc]
    simp only [tensor_whiskerLeft, Functor.LaxMonoidal.associativity, Category.assoc,
      Iso.inv_hom_id_assoc]
    rw [← tensorHom_id, associator_naturality_assoc]
    simp [← id_tensorHom, -tensorHom_id]
  left_unitality X := by
    simp only [Iso.trans_hom, εIso_hom, Iso.app_hom, ← tensorHom_id, tensorIso_hom, Iso.symm_hom,
      μIso_hom, Category.assoc, tensorHom_comp_tensorHom_assoc, Iso.hom_inv_id_app,
      Category.comp_id, Category.id_comp]
    rw [← i.hom.naturality, ← Category.comp_id (i.inv.app X),
      ← Category.id_comp (Functor.LaxMonoidal.ε F), ← tensorHom_comp_tensorHom]
    simp
  right_unitality X := by
    simp only [Iso.trans_hom, εIso_hom, Iso.app_hom, ← id_tensorHom, tensorIso_hom, Iso.symm_hom,
      μIso_hom, Category.assoc, tensorHom_comp_tensorHom_assoc, Category.id_comp,
      Iso.hom_inv_id_app, Category.comp_id]
    rw [← i.hom.naturality, ← Category.comp_id (i.inv.app X),
      ← Category.id_comp (Functor.LaxMonoidal.ε F), ← tensorHom_comp_tensorHom]
    simp

/--
Transport the structure of a monoidal functor along a natural isomorphism of functors.
-/
@[instance_reducible]
/-
**CategoryTheory.Functor.Monoidal.transport** 是 Mathlib 中的一个定义，位于命名空间 `CategoryT
heory.Functor.Monoidal`。
形式化陈述：transport {F G : C ⥤ D} [F.Monoidal] (i : F ≅ G) : G.Monoidal
参数：i : F ≅ G。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Transport the structure of a monoidal functor along a natural isomorphism of fun
ctors.
-/
def transport {F G : C ⥤ D} [F.Monoidal] (i : F ≅ G) : G.Monoidal :=
  (coreMonoidalTransport i).toMonoidal

@[reassoc]
/-
**CategoryTheory.Functor.Monoidal.transport_** 是 Mathlib 中的一个引理，位于命名空间 `Category
Theory.Functor.Monoidal`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma transport_ε {F G : C ⥤ D} [F.Monoidal] (i : F ≅ G) : letI := transport i
    LaxMonoidal.ε G = LaxMonoidal.ε F ≫ i.hom.app (𝟙_ C) :=
  rfl

@[reassoc]
/-
**CategoryTheory.Functor.Monoidal.transport_** 是 Mathlib 中的一个引理，位于命名空间 `Category
Theory.Functor.Monoidal`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma transport_η {F G : C ⥤ D} [F.Monoidal] (i : F ≅ G) : letI := transport i
    OplaxMonoidal.η G = i.inv.app (𝟙_ C) ≫ OplaxMonoidal.η F :=
  rfl

@[reassoc]
/-
**CategoryTheory.Functor.Monoidal.transport_** 是 Mathlib 中的一个引理，位于命名空间 `Category
Theory.Functor.Monoidal`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma transport_μ {F G : C ⥤ D} [F.Monoidal] (i : F ≅ G) (X Y : C) : letI := transport i
    LaxMonoidal.μ G X Y = (i.inv.app X ⊗ₘ i.inv.app Y) ≫ LaxMonoidal.μ F X Y ≫ i.hom.app (X ⊗ Y) :=
  rfl

@[reassoc]
/-
**CategoryTheory.Functor.Monoidal.transport_** 是 Mathlib 中的一个引理，位于命名空间 `Category
Theory.Functor.Monoidal`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma transport_δ {F G : C ⥤ D} [F.Monoidal] (i : F ≅ G) (X Y : C) : letI := transport i
    OplaxMonoidal.δ G X Y =
      i.inv.app (X ⊗ Y) ≫ OplaxMonoidal.δ F X Y ≫ (i.hom.app X ⊗ₘ i.hom.app Y) :=
  coreMonoidalTransport_μIso_inv _ _ _

end Functor.Monoidal

namespace Equivalence

variable {C D}

/--
Given a functor `F` and an equivalence of categories `e` such that `e.inverse` and `e.functor ⋙ F`
are monoidal functors, `F` is monoidal as well.
-/
@[instance_reducible]
/-
**CategoryTheory.Equivalence.monoidalOfPrecompFunctor** 是 Mathlib 中的一个定义，位于命名空间 
`CategoryTheory.Equivalence`。
形式化陈述：monoidalOfPrecompFunctor (e : C ≌ D) (F : D ⥤ E) {F' : C ⥤ E} (i : e.funct
or ⋙ F ≅ F') [e.inverse.Monoidal] [F'.Monoidal] : F.Monoidal
参数：e : C ≌ D；F : D ⥤ E；i : e.functor ⋙ F ≅ F'。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given a functor `F` and an equivalence of categories `e` such that `e.inverse` a
nd `e.functor ⋙ F`
are monoidal functors, `F` is monoidal as well.
-/
def monoidalOfPrecompFunctor (e : C ≌ D) (F : D ⥤ E) {F' : C ⥤ E} (i : e.functor ⋙ F ≅ F')
    [e.inverse.Monoidal] [F'.Monoidal] : F.Monoidal :=
  letI : (e.functor ⋙ F).Monoidal := .transport i.symm
  .transport (e.invFunIdAssoc F)

/--
Given a functor `F` and an equivalence of categories `e` such that `e.functor` and `e.inverse ⋙ F`
are monoidal functors, `F` is monoidal as well.
-/
@[instance_reducible]
/-
**CategoryTheory.Equivalence.monoidalOfPrecompInverse** 是 Mathlib 中的一个定义，位于命名空间 
`CategoryTheory.Equivalence`。
形式化陈述：monoidalOfPrecompInverse (e : C ≌ D) (F : C ⥤ E) {F' : D ⥤ E} (i : e.inver
se ⋙ F ≅ F') [e.functor.Monoidal] [F'.Monoidal] : F.Monoidal
参数：e : C ≌ D；F : C ⥤ E；i : e.inverse ⋙ F ≅ F'。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given a functor `F` and an equivalence of categories `e` such that `e.functor` a
nd `e.inverse ⋙ F`
are monoidal functors, `F` is monoidal as well.
-/
def monoidalOfPrecompInverse (e : C ≌ D) (F : C ⥤ E) {F' : D ⥤ E} (i : e.inverse ⋙ F ≅ F')
    [e.functor.Monoidal] [F'.Monoidal] : F.Monoidal :=
  e.symm.monoidalOfPrecompFunctor F i

/--
Given a functor `F` and an equivalence of categories `e` such that `e.functor` and `F ⋙ e.inverse`
are monoidal functors, `F` is monoidal as well.
-/
@[instance_reducible]
/-
**CategoryTheory.Equivalence.monoidalOfPostcompInverse** 是 Mathlib 中的一个定义，位于命名空间
 `CategoryTheory.Equivalence`。
形式化陈述：monoidalOfPostcompInverse (e : C ≌ D) (F : E ⥤ D) {F' : E ⥤ C} (i : F ⋙ e.
inverse ≅ F') [e.functor.Monoidal] [F'.Monoidal] : F.Monoidal
参数：e : C ≌ D；F : E ⥤ D；i : F ⋙ e.inverse ≅ F'。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given a functor `F` and an equivalence of categories `e` such that `e.functor` a
nd `F ⋙ e.inverse`
are monoidal functors, `F` is monoidal as well.
-/
def monoidalOfPostcompInverse (e : C ≌ D) (F : E ⥤ D) {F' : E ⥤ C} (i : F ⋙ e.inverse ≅ F')
    [e.functor.Monoidal] [F'.Monoidal] : F.Monoidal :=
  .transport (Functor.isoWhiskerRight i.symm e.functor ≪≫ Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _ e.counitIso ≪≫ F.rightUnitor)

/--
Given a functor `F` and an equivalence of categories `e` such that `e.inverse` and `F ⋙ e.functor`
are monoidal functors, `F` is monoidal as well.
-/
@[instance_reducible]
/-
**CategoryTheory.Equivalence.monoidalOfPostcompFunctor** 是 Mathlib 中的一个定义，位于命名空间
 `CategoryTheory.Equivalence`。
形式化陈述：monoidalOfPostcompFunctor (e : C ≌ D) (F : E ⥤ C) {F' : E ⥤ D} (i : F ⋙ e.
functor ≅ F') [e.inverse.Monoidal] [F'.Monoidal] : F.Monoidal
参数：e : C ≌ D；F : E ⥤ C；i : F ⋙ e.functor ≅ F'。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given a functor `F` and an equivalence of categories `e` such that `e.inverse` a
nd `F ⋙ e.functor`
are monoidal functors, `F` is monoidal as well.
-/
def monoidalOfPostcompFunctor (e : C ≌ D) (F : E ⥤ C) {F' : E ⥤ D} (i : F ⋙ e.functor ≅ F')
    [e.inverse.Monoidal] [F'.Monoidal] : F.Monoidal :=
  e.symm.monoidalOfPostcompInverse _ i

end Equivalence

end CategoryTheory

