/-
Copyright (c) 2022 Yuma Mizuno. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuma Mizuno
-/
module

public import Mathlib.CategoryTheory.Bicategory.Basic

/-!
# Bicategorical composition `⊗≫` (composition up to associators)

We provide `f ⊗≫ g`, the `bicategoricalComp` operation,
which automatically inserts associators and unitors as needed
to make the target of `f` match the source of `g`.
-/

@[expose] public section

universe w v u

open CategoryTheory Bicategory

namespace CategoryTheory

variable {B : Type u} [Bicategory.{w, v} B] {a b c d : B}

/-- A typeclass carrying a choice of bicategorical structural isomorphism between two objects.
Used by the `⊗≫` bicategorical composition operator, and the `coherence` tactic.
-/
/-
**CategoryTheory.BicategoricalCoherence** 是 Mathlib 中的一个归纳类型，位于命名空间 `CategoryThe
ory`。
形式化陈述：{B : Type u} → [inst : CategoryTheory.Bicategory B] → {a b : B} → (a ⟶ b) 
→ (a ⟶ b) → Type w
参数：a ⟶ b；a ⟶ b。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A typeclass carrying a choice of bicategorical structural isomorphism between tw
o objects.
Used by the `⊗≫` bicategorical composition operator, and the `coherence` tactic.
-/
class BicategoricalCoherence (f g : a ⟶ b) where
  /-- The chosen structural isomorphism between to 1-morphisms. -/
  iso : f ≅ g

/-- Notation for identities up to unitors and associators. -/
scoped[CategoryTheory.Bicategory] notation " ⊗𝟙 " =>
  BicategoricalCoherence.iso -- type as \ot 𝟙

/-- Construct an isomorphism between two objects in a bicategorical category
out of unitors and associators. -/
/-
**CategoryTheory.bicategoricalIso** 是 Mathlib 中的一个缩写定义，位于命名空间 `CategoryTheory`。
形式化陈述：bicategoricalIso (f g : a ⟶ b) [BicategoricalCoherence f g] : f ≅ g
参数：f g : a ⟶ b。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Construct an isomorphism between two objects in a bicategorical category
out of unitors and associators.
-/
abbrev bicategoricalIso (f g : a ⟶ b) [BicategoricalCoherence f g] : f ≅ g :=
  ⊗𝟙

/-- Compose two morphisms in a bicategorical category,
inserting unitors and associators between as necessary. -/
/-
**CategoryTheory.bicategoricalComp** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory`。
形式化陈述：bicategoricalComp {f g h i : a ⟶ b} [BicategoricalCoherence g h] (η : f ⟶ 
g) (θ : h ⟶ i) : f ⟶ i
参数：η : f ⟶ g；θ : h ⟶ i。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Compose two morphisms in a bicategorical category,
inserting unitors and associators between as necessary.
-/
def bicategoricalComp {f g h i : a ⟶ b} [BicategoricalCoherence g h]
    (η : f ⟶ g) (θ : h ⟶ i) : f ⟶ i :=
  η ≫ ⊗𝟙.hom ≫ θ

-- type as \ot \gg
@[inherit_doc bicategoricalComp]
scoped[CategoryTheory.Bicategory] infixr:80 " ⊗≫ " => bicategoricalComp

/-- Compose two isomorphisms in a bicategorical category,
inserting unitors and associators between as necessary. -/
/-
**CategoryTheory.bicategoricalIsoComp** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory`
。
形式化陈述：bicategoricalIsoComp {f g h i : a ⟶ b} [BicategoricalCoherence g h] (η : f
 ≅ g) (θ : h ≅ i) : f ≅ i
参数：η : f ≅ g；θ : h ≅ i。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Compose two isomorphisms in a bicategorical category,
inserting unitors and associators between as necessary.
-/
def bicategoricalIsoComp {f g h i : a ⟶ b} [BicategoricalCoherence g h]
    (η : f ≅ g) (θ : h ≅ i) : f ≅ i :=
  η ≪≫ ⊗𝟙 ≪≫ θ

@[inherit_doc bicategoricalIsoComp]
scoped[CategoryTheory.Bicategory] infixr:80 " ≪⊗≫ " =>
  bicategoricalIsoComp -- type as \ll \ot \gg

namespace BicategoricalCoherence

@[simps]
/-
**CategoryTheory.BicategoricalCoherence.refl** 是 Mathlib 中的一个实例，位于命名空间 `Category
Theory.BicategoricalCoherence`。
形式化陈述：refl (f : a ⟶ b) : BicategoricalCoherence f f
参数：f : a ⟶ b。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance refl (f : a ⟶ b) : BicategoricalCoherence f f :=
  ⟨Iso.refl _⟩

@[simps]
/-
**CategoryTheory.BicategoricalCoherence.whiskerLeft** 是 Mathlib 中的一个实例，位于命名空间 `C
ategoryTheory.BicategoricalCoherence`。
形式化陈述：whiskerLeft (f : a ⟶ b) (g h : b ⟶ c) [BicategoricalCoherence g h] : Bicat
egoricalCoherence (f ≫ g) (f ≫ h)
参数：f : a ⟶ b；g h : b ⟶ c。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance whiskerLeft (f : a ⟶ b) (g h : b ⟶ c)
    [BicategoricalCoherence g h] : BicategoricalCoherence (f ≫ g) (f ≫ h) :=
  ⟨whiskerLeftIso f ⊗𝟙⟩

@[simps]
/-
**CategoryTheory.BicategoricalCoherence.whiskerRight** 是 Mathlib 中的一个实例，位于命名空间 `
CategoryTheory.BicategoricalCoherence`。
形式化陈述：whiskerRight (f g : a ⟶ b) (h : b ⟶ c) [BicategoricalCoherence f g] : Bica
tegoricalCoherence (f ≫ h) (g ≫ h)
参数：f g : a ⟶ b；h : b ⟶ c。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance whiskerRight (f g : a ⟶ b) (h : b ⟶ c)
    [BicategoricalCoherence f g] : BicategoricalCoherence (f ≫ h) (g ≫ h) :=
  ⟨whiskerRightIso ⊗𝟙 h⟩

@[simps]
/-
**CategoryTheory.BicategoricalCoherence.tensorRight** 是 Mathlib 中的一个实例，位于命名空间 `C
ategoryTheory.BicategoricalCoherence`。
形式化陈述：tensorRight (f : a ⟶ b) (g : b ⟶ b) [BicategoricalCoherence (𝟙 b) g] : Bic
ategoricalCoherence f (f ≫ g)
参数：f : a ⟶ b；g : b ⟶ b；𝟙 b。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance tensorRight (f : a ⟶ b) (g : b ⟶ b)
    [BicategoricalCoherence (𝟙 b) g] : BicategoricalCoherence f (f ≫ g) :=
  ⟨(ρ_ f).symm ≪≫ (whiskerLeftIso f ⊗𝟙)⟩

@[simps]
/-
**CategoryTheory.BicategoricalCoherence.tensorRight'** 是 Mathlib 中的一个实例，位于命名空间 `
CategoryTheory.BicategoricalCoherence`。
形式化陈述：tensorRight' (f : a ⟶ b) (g : b ⟶ b) [BicategoricalCoherence g (𝟙 b)] : Bi
categoricalCoherence (f ≫ g) f
参数：f : a ⟶ b；g : b ⟶ b；𝟙 b。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance tensorRight' (f : a ⟶ b) (g : b ⟶ b)
    [BicategoricalCoherence g (𝟙 b)] : BicategoricalCoherence (f ≫ g) f :=
  ⟨whiskerLeftIso f ⊗𝟙 ≪≫ (ρ_ f)⟩

@[simps]
/-
**CategoryTheory.BicategoricalCoherence.left** 是 Mathlib 中的一个实例，位于命名空间 `Category
Theory.BicategoricalCoherence`。
形式化陈述：left (f g : a ⟶ b) [BicategoricalCoherence f g] : BicategoricalCoherence (
𝟙 a ≫ f) g
参数：f g : a ⟶ b。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance left (f g : a ⟶ b) [BicategoricalCoherence f g] :
    BicategoricalCoherence (𝟙 a ≫ f) g :=
  ⟨λ_ f ≪≫ ⊗𝟙⟩

@[simps]
/-
**CategoryTheory.BicategoricalCoherence.left'** 是 Mathlib 中的一个实例，位于命名空间 `Categor
yTheory.BicategoricalCoherence`。
形式化陈述：left' (f g : a ⟶ b) [BicategoricalCoherence f g] : BicategoricalCoherence 
f (𝟙 a ≫ g)
参数：f g : a ⟶ b。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance left' (f g : a ⟶ b) [BicategoricalCoherence f g] :
    BicategoricalCoherence f (𝟙 a ≫ g) :=
  ⟨⊗𝟙 ≪≫ (λ_ g).symm⟩

@[simps]
/-
**CategoryTheory.BicategoricalCoherence.right** 是 Mathlib 中的一个实例，位于命名空间 `Categor
yTheory.BicategoricalCoherence`。
形式化陈述：right (f g : a ⟶ b) [BicategoricalCoherence f g] : BicategoricalCoherence 
(f ≫ 𝟙 b) g
参数：f g : a ⟶ b。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance right (f g : a ⟶ b) [BicategoricalCoherence f g] :
    BicategoricalCoherence (f ≫ 𝟙 b) g :=
  ⟨ρ_ f ≪≫ ⊗𝟙⟩

@[simps]
/-
**CategoryTheory.BicategoricalCoherence.right'** 是 Mathlib 中的一个实例，位于命名空间 `Catego
ryTheory.BicategoricalCoherence`。
形式化陈述：right' (f g : a ⟶ b) [BicategoricalCoherence f g] : BicategoricalCoherence
 f (g ≫ 𝟙 b)
参数：f g : a ⟶ b。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance right' (f g : a ⟶ b) [BicategoricalCoherence f g] :
    BicategoricalCoherence f (g ≫ 𝟙 b) :=
  ⟨⊗𝟙 ≪≫ (ρ_ g).symm⟩

@[simps]
/-
**CategoryTheory.BicategoricalCoherence.assoc** 是 Mathlib 中的一个实例，位于命名空间 `Categor
yTheory.BicategoricalCoherence`。
形式化陈述：assoc (f : a ⟶ b) (g : b ⟶ c) (h : c ⟶ d) (i : a ⟶ d) [BicategoricalCohere
nce (f ≫ g ≫ h) i] : BicategoricalCoherence ((f ≫ g) ≫ h) i
参数：f : a ⟶ b；g : b ⟶ c；h : c ⟶ d；i : a ⟶ d；f ≫ g ≫ h。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance assoc (f : a ⟶ b) (g : b ⟶ c) (h : c ⟶ d) (i : a ⟶ d)
    [BicategoricalCoherence (f ≫ g ≫ h) i] :
    BicategoricalCoherence ((f ≫ g) ≫ h) i :=
  ⟨α_ f g h ≪≫ ⊗𝟙⟩

@[simps]
/-
**CategoryTheory.BicategoricalCoherence.assoc'** 是 Mathlib 中的一个实例，位于命名空间 `Catego
ryTheory.BicategoricalCoherence`。
形式化陈述：assoc' (f : a ⟶ b) (g : b ⟶ c) (h : c ⟶ d) (i : a ⟶ d) [BicategoricalCoher
ence i (f ≫ g ≫ h)] : BicategoricalCoherence i ((f ≫ g) ≫ h)
参数：f : a ⟶ b；g : b ⟶ c；h : c ⟶ d；i : a ⟶ d；f ≫ g ≫ h。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance assoc' (f : a ⟶ b) (g : b ⟶ c) (h : c ⟶ d) (i : a ⟶ d)
    [BicategoricalCoherence i (f ≫ g ≫ h)] :
    BicategoricalCoherence i ((f ≫ g) ≫ h) :=
  ⟨⊗𝟙 ≪≫ (α_ f g h).symm⟩

end BicategoricalCoherence

@[simp]
/-
**CategoryTheory.bicategoricalComp_refl** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheor
y`。
形式化陈述：bicategoricalComp_refl {f g h : a ⟶ b} (η : f ⟶ g) (θ : g ⟶ h) : η otimes≫
 θ = η ≫ θ
参数：η : f ⟶ g；θ : g ⟶ h。
该定理/引理给出了一组等式。
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
theorem bicategoricalComp_refl {f g h : a ⟶ b} (η : f ⟶ g) (θ : g ⟶ h) : η ⊗≫ θ = η ≫ θ := by
  dsimp [bicategoricalComp]; simp

end CategoryTheory

