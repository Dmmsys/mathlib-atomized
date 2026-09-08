/-
Copyright (c) 2022 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison, Yuma Mizuno, Oleksandr Manzyuk
-/
module

public import Mathlib.CategoryTheory.Monoidal.Category

/-!
# Monoidal composition `⊗≫` (composition up to associators)

We provide `f ⊗≫ g`, the `monoidalComp` operation,
which automatically inserts associators and unitors as needed
to make the target of `f` match the source of `g`.

## Example

Suppose we have a braiding morphism `R X Y : X ⊗ Y ⟶ Y ⊗ X` in a monoidal category, and that we
want to define the morphism with the type `V₁ ⊗ V₂ ⊗ V₃ ⊗ V₄ ⊗ V₅ ⟶ V₁ ⊗ V₃ ⊗ V₂ ⊗ V₄ ⊗ V₅` that
transposes the second and third components by `R V₂ V₃`. How to do this? The first guess would be
to use the whiskering operators `◁` and `▷`, and define the morphism as `V₁ ◁ R V₂ V₃ ▷ V₄ ▷ V₅`.
However, this morphism has the type `V₁ ⊗ ((V₂ ⊗ V₃) ⊗ V₄) ⊗ V₅ ⟶ V₁ ⊗ ((V₃ ⊗ V₂) ⊗ V₄) ⊗ V₅`,
which is not what we need. We should insert suitable associators. The desired associators can,
in principle, be defined by using the primitive three-components associator
`α_ X Y Z : (X ⊗ Y) ⊗ Z ≅ X ⊗ (Y ⊗ Z)` as a building block, but writing down actual definitions
are quite tedious, and we usually don't want to see them.

The monoidal composition `⊗≫` is designed to solve such a problem. In this case, we can define the
desired morphism as `𝟙 _ ⊗≫ V₁ ◁ R V₂ V₃ ▷ V₄ ▷ V₅ ⊗≫ 𝟙 _`, where the first and the second `𝟙 _`
are completed as `𝟙 (V₁ ⊗ V₂ ⊗ V₃ ⊗ V₄ ⊗ V₅)` and `𝟙 (V₁ ⊗ V₃ ⊗ V₂ ⊗ V₄ ⊗ V₅)`, respectively.

-/

@[expose] public section

universe v u

open CategoryTheory MonoidalCategory

namespace CategoryTheory

variable {C : Type u} [Category.{v} C]

open scoped MonoidalCategory

/--
A typeclass carrying a choice of monoidal structural isomorphism between two objects.
Used by the `⊗≫` monoidal composition operator, and the `coherence` tactic.
-/
-- We could likely turn this into a `Prop`-valued existential if that proves useful.
/-
**CategoryTheory.MonoidalCoherence** 是 Mathlib 中的一个归纳类型，位于命名空间 `CategoryTheory`。
形式化陈述：{C : Type u} → [CategoryTheory.Category.{v, u} C] → C → C → Type v
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
class MonoidalCoherence (X Y : C) where
  /-- A monoidal structural isomorphism between two objects. -/
  iso : X ≅ Y

/-- Notation for identities up to unitors and associators. -/
scoped[CategoryTheory.MonoidalCategory] notation " ⊗𝟙 " =>
  MonoidalCoherence.iso -- type as \ot 𝟙

/-- Construct an isomorphism between two objects in a monoidal category
out of unitors and associators. -/
/-
**CategoryTheory.monoidalIso** 是 Mathlib 中的一个缩写定义，位于命名空间 `CategoryTheory`。
形式化陈述：monoidalIso (X Y : C) [MonoidalCoherence X Y] : X ≅ Y
参数：X Y : C。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Construct an isomorphism between two objects in a monoidal category
out of unitors and associators.
-/
abbrev monoidalIso (X Y : C) [MonoidalCoherence X Y] : X ≅ Y := MonoidalCoherence.iso

/-- Compose two morphisms in a monoidal category,
inserting unitors and associators between as necessary. -/
/-
**CategoryTheory.monoidalComp** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory`。
形式化陈述：monoidalComp {W X Y Z : C} [MonoidalCoherence X Y] (f : W ⟶ X) (g : Y ⟶ Z)
 : W ⟶ Z
参数：f : W ⟶ X；g : Y ⟶ Z。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Compose two morphisms in a monoidal category,
inserting unitors and associators between as necessary.
-/
def monoidalComp {W X Y Z : C} [MonoidalCoherence X Y] (f : W ⟶ X) (g : Y ⟶ Z) : W ⟶ Z :=
  f ≫ ⊗𝟙.hom ≫ g

@[inherit_doc monoidalComp]
scoped[CategoryTheory.MonoidalCategory] infixr:80 " ⊗≫ " =>
  monoidalComp -- type as \ot \gg

/-- Compose two isomorphisms in a monoidal category,
inserting unitors and associators between as necessary. -/
/-
**CategoryTheory.monoidalIsoComp** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory`。
形式化陈述：monoidalIsoComp {W X Y Z : C} [MonoidalCoherence X Y] (f : W ≅ X) (g : Y ≅
 Z) : W ≅ Z
参数：f : W ≅ X；g : Y ≅ Z。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Compose two isomorphisms in a monoidal category,
inserting unitors and associators between as necessary.
-/
def monoidalIsoComp {W X Y Z : C} [MonoidalCoherence X Y] (f : W ≅ X) (g : Y ≅ Z) : W ≅ Z :=
  f ≪≫ ⊗𝟙 ≪≫ g

@[inherit_doc monoidalIsoComp]
scoped[CategoryTheory.MonoidalCategory] infixr:80 " ≪⊗≫ " =>
  monoidalIsoComp -- type as \ll \ot \gg

namespace MonoidalCoherence

variable [MonoidalCategory C]

@[simps]
/-
**CategoryTheory.MonoidalCoherence.refl** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheor
y.MonoidalCoherence`。
形式化陈述：refl (X : C) : MonoidalCoherence X X
参数：X : C。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance refl (X : C) : MonoidalCoherence X X := ⟨Iso.refl _⟩

@[simps]
/-
**CategoryTheory.MonoidalCoherence.whiskerLeft** 是 Mathlib 中的一个实例，位于命名空间 `Catego
ryTheory.MonoidalCoherence`。
形式化陈述：whiskerLeft (X Y Z : C) [MonoidalCoherence Y Z] : MonoidalCoherence (X oti
mes Y) (X otimes Z)
参数：X Y Z : C。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance whiskerLeft (X Y Z : C) [MonoidalCoherence Y Z] :
    MonoidalCoherence (X ⊗ Y) (X ⊗ Z) :=
  ⟨whiskerLeftIso X ⊗𝟙⟩

@[simps]
/-
**CategoryTheory.MonoidalCoherence.whiskerRight** 是 Mathlib 中的一个实例，位于命名空间 `Categ
oryTheory.MonoidalCoherence`。
形式化陈述：whiskerRight (X Y Z : C) [MonoidalCoherence X Y] : MonoidalCoherence (X ot
imes Z) (Y otimes Z)
参数：X Y Z : C。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance whiskerRight (X Y Z : C) [MonoidalCoherence X Y] :
    MonoidalCoherence (X ⊗ Z) (Y ⊗ Z) :=
  ⟨whiskerRightIso ⊗𝟙 Z⟩

@[simps]
/-
**CategoryTheory.MonoidalCoherence.tensor_right** 是 Mathlib 中的一个实例，位于命名空间 `Categ
oryTheory.MonoidalCoherence`。
形式化陈述：tensor_right (X Y : C) [MonoidalCoherence (𝟙_ C) Y] : MonoidalCoherence X 
(X otimes Y)
参数：X Y : C；𝟙_ C。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance tensor_right (X Y : C) [MonoidalCoherence (𝟙_ C) Y] :
    MonoidalCoherence X (X ⊗ Y) :=
  ⟨(ρ_ X).symm ≪≫ (whiskerLeftIso X ⊗𝟙)⟩

@[simps]
/-
**CategoryTheory.MonoidalCoherence.tensor_right'** 是 Mathlib 中的一个实例，位于命名空间 `Cate
goryTheory.MonoidalCoherence`。
形式化陈述：tensor_right' (X Y : C) [MonoidalCoherence Y (𝟙_ C)] : MonoidalCoherence (
X otimes Y) X
参数：X Y : C；𝟙_ C。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance tensor_right' (X Y : C) [MonoidalCoherence Y (𝟙_ C)] :
    MonoidalCoherence (X ⊗ Y) X :=
  ⟨whiskerLeftIso X ⊗𝟙 ≪≫ (ρ_ X)⟩

@[simps]
/-
**CategoryTheory.MonoidalCoherence.left** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheor
y.MonoidalCoherence`。
形式化陈述：left (X Y : C) [MonoidalCoherence X Y] : MonoidalCoherence (𝟙_ C otimes X)
 Y
参数：X Y : C。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance left (X Y : C) [MonoidalCoherence X Y] :
    MonoidalCoherence (𝟙_ C ⊗ X) Y :=
  ⟨λ_ X ≪≫ ⊗𝟙⟩

@[simps]
/-
**CategoryTheory.MonoidalCoherence.left'** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheo
ry.MonoidalCoherence`。
形式化陈述：left' (X Y : C) [MonoidalCoherence X Y] : MonoidalCoherence X (𝟙_ C otimes
 Y)
参数：X Y : C。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance left' (X Y : C) [MonoidalCoherence X Y] :
    MonoidalCoherence X (𝟙_ C ⊗ Y) :=
  ⟨⊗𝟙 ≪≫ (λ_ Y).symm⟩

@[simps]
/-
**CategoryTheory.MonoidalCoherence.right** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheo
ry.MonoidalCoherence`。
形式化陈述：right (X Y : C) [MonoidalCoherence X Y] : MonoidalCoherence (X otimes 𝟙_ C
) Y
参数：X Y : C。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance right (X Y : C) [MonoidalCoherence X Y] :
    MonoidalCoherence (X ⊗ 𝟙_ C) Y :=
  ⟨ρ_ X ≪≫ ⊗𝟙⟩

@[simps]
/-
**CategoryTheory.MonoidalCoherence.right'** 是 Mathlib 中的一个实例，位于命名空间 `CategoryThe
ory.MonoidalCoherence`。
形式化陈述：right' (X Y : C) [MonoidalCoherence X Y] : MonoidalCoherence X (Y otimes 𝟙
_ C)
参数：X Y : C。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance right' (X Y : C) [MonoidalCoherence X Y] :
    MonoidalCoherence X (Y ⊗ 𝟙_ C) :=
  ⟨⊗𝟙 ≪≫ (ρ_ Y).symm⟩

@[simps]
/-
**CategoryTheory.MonoidalCoherence.assoc** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheo
ry.MonoidalCoherence`。
形式化陈述：assoc (X Y Z W : C) [MonoidalCoherence (X otimes (Y otimes Z)) W] : Monoid
alCoherence ((X otimes Y) otimes Z) W
参数：X Y Z W : C；X otimes (Y otimes Z)。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance assoc (X Y Z W : C) [MonoidalCoherence (X ⊗ (Y ⊗ Z)) W] :
    MonoidalCoherence ((X ⊗ Y) ⊗ Z) W :=
  ⟨α_ X Y Z ≪≫ ⊗𝟙⟩

@[simps]
/-
**CategoryTheory.MonoidalCoherence.assoc'** 是 Mathlib 中的一个实例，位于命名空间 `CategoryThe
ory.MonoidalCoherence`。
形式化陈述：assoc' (W X Y Z : C) [MonoidalCoherence W (X otimes (Y otimes Z))] : Monoi
dalCoherence W ((X otimes Y) otimes Z)
参数：W X Y Z : C；X otimes (Y otimes Z)。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance assoc' (W X Y Z : C) [MonoidalCoherence W (X ⊗ (Y ⊗ Z))] :
    MonoidalCoherence W ((X ⊗ Y) ⊗ Z) :=
  ⟨⊗𝟙 ≪≫ (α_ X Y Z).symm⟩

end MonoidalCoherence

/-
**CategoryTheory.monoidalComp_refl** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory`。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] {X Y Z : C} (f : 
X ⟶ Y) (g : Y ⟶ Z),   CategoryTheory.monoidalComp f g = CategoryTheory.CategoryS
truct.comp f g
参数：f : X ⟶ Y；g : Y ⟶ Z。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
@[simp] lemma monoidalComp_refl {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) :
    f ⊗≫ g = f ≫ g := by
  simp [monoidalComp]

end CategoryTheory

