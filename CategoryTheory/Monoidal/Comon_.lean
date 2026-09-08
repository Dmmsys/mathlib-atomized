/-
Copyright (c) 2024 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import Mathlib.CategoryTheory.Monoidal.Mon
public import Mathlib.CategoryTheory.Monoidal.Braided.Opposite
public import Mathlib.CategoryTheory.Monoidal.Transport
public import Mathlib.CategoryTheory.Monoidal.CoherenceLemmas
public import Mathlib.CategoryTheory.Limits.Shapes.Terminal

/-!
# The category of comonoids in a monoidal category.

We define comonoids in a monoidal category `C`,
and show that they are equivalently monoid objects in the opposite category.

We construct the monoidal structure on `Comon C`, when `C` is braided.

An oplax monoidal functor takes comonoid objects to comonoid objects.
That is, an oplax monoidal functor `F : C ⥤ D` induces a functor `Comon C ⥤ Comon D`.

## TODO
* Comonoid objects in `C` are "just"
  oplax monoidal functors from the trivial monoidal category to `C`.
-/

@[expose] public section

universe v₁ v₂ u₁ u₂ u

open CategoryTheory MonoidalCategory

namespace CategoryTheory
variable {C : Type u₁} [Category.{v₁} C] [MonoidalCategory.{v₁} C]

/-- A comonoid object internal to a monoidal category.

When the monoidal category is preadditive, this is also sometimes called a "coalgebra object".
-/
/-
**CategoryTheory.ComonObj** 是 Mathlib 中的一个类，位于命名空间 `CategoryTheory`。
形式化陈述：ComonObj (X : C) where /-- The counit morphism of a comonoid object. -/ co
unit : X ⟶ 𝟙_ C /-- The comultiplication morphism of a comonoid object. -/ comul
 : X ⟶ X otimes X counit_comul (X) : comul ≫ counit ▷ X = (fun_ X).inv
参数：X : C。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A comonoid object internal to a monoidal category.

When the monoidal category is preadditive, this is also sometimes called a "coal
gebra object".
-/
class ComonObj (X : C) where
  /-- The counit morphism of a comonoid object. -/
  counit : X ⟶ 𝟙_ C
  /-- The comultiplication morphism of a comonoid object. -/
  comul : X ⟶ X ⊗ X
  counit_comul (X) : comul ≫ counit ▷ X = (λ_ X).inv := by cat_disch
  comul_counit (X) : comul ≫ X ◁ counit = (ρ_ X).inv := by cat_disch
  comul_assoc (X) : comul ≫ X ◁ comul = comul ≫ (comul ▷ X) ≫ (α_ X X X).hom := by cat_disch

namespace ComonObj

@[inherit_doc] scoped notation "Δ" => ComonObj.comul
@[inherit_doc] scoped notation "Δ[" M "]" => ComonObj.comul (X := M)
@[inherit_doc] scoped notation "ε" => ComonObj.counit
@[inherit_doc] scoped notation "ε[" M "]" => ComonObj.counit (X := M)

attribute [reassoc (attr := simp)] counit_comul comul_counit comul_assoc

/-- The canonical comonoid structure on the monoidal unit.
This is not a global instance to avoid conflicts with other comonoid structures. -/
@[instance_reducible, simps]
/-
**CategoryTheory.ComonObj.instTensorUnit** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheo
ry.ComonObj`。
形式化陈述：instTensorUnit (C : Type u₁) [Category.{v₁} C] [MonoidalCategory.{v₁} C] :
 ComonObj (𝟙_ C) where counit
参数：C : Type u₁。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The canonical comonoid structure on the monoidal unit.
This is not a global instance to avoid conflicts with other comonoid structures.
-/
def instTensorUnit (C : Type u₁) [Category.{v₁} C] [MonoidalCategory.{v₁} C] : ComonObj (𝟙_ C) where
  counit := 𝟙 _
  comul := (λ_ _).inv
  counit_comul := by simp
  comul_counit := by monoidal_coherence
  comul_assoc := by monoidal_coherence

end ComonObj

open scoped ComonObj

variable {M N O : C} [ComonObj M] [ComonObj N] [ComonObj O]

/-- The property that a morphism between comonoid objects is a comonoid morphism. -/
/-
**CategoryTheory.IsComonHom** 是 Mathlib 中的一个类，位于命名空间 `CategoryTheory`。
形式化陈述：IsComonHom (f : M ⟶ N) : Prop where hom_counit (f) : f ≫ ε = ε
参数：f : M ⟶ N。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The property that a morphism between comonoid objects is a comonoid morphism.
-/
class IsComonHom (f : M ⟶ N) : Prop where
  hom_counit (f) : f ≫ ε = ε := by cat_disch
  hom_comul (f) : f ≫ Δ = Δ ≫ (f ⊗ₘ f) := by cat_disch

attribute [reassoc (attr := simp)] IsComonHom.hom_counit IsComonHom.hom_comul
/-
**CategoryTheory.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : IsComonHom (𝟙 M) where
/-
**CategoryTheory.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (f : M ⟶ N) (g : N ⟶ O) [IsComonHom f] [IsComonHom g] : IsComonHom (f ≫ g) where
/-
**CategoryTheory.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (f : M ≅ N) [IsComonHom f.hom] : IsComonHom f.inv where
  hom_counit := by simp [Iso.inv_comp_eq]
  hom_comul := by simp [Iso.inv_comp_eq]
/-
**CategoryTheory.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (f : M ⟶ N) [IsComonHom f] [IsIso f] : IsComonHom (inv f) where

variable (C) in
/-- A comonoid object internal to a monoidal category.

When the monoidal category is preadditive, this is also sometimes called a "coalgebra object".
-/
/-
**CategoryTheory.Comon** 是 Mathlib 中的一个归纳类型，位于命名空间 `CategoryTheory`。
形式化陈述：(C : Type u₁) → [inst : CategoryTheory.Category.{v₁, u₁} C] → [CategoryThe
ory.MonoidalCategory C] → Type (max u₁ v₁)
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A comonoid object internal to a monoidal category.

When the monoidal category is preadditive, this is also sometimes called a "coal
gebra object".
-/
structure Comon where
  /-- The underlying object of a comonoid object. -/
  X : C
  [comon : ComonObj X]

attribute [instance] Comon.comon

namespace Comon

attribute [local instance] ComonObj.instTensorUnit in
variable (C) in
/-- The trivial comonoid object. We later show this is terminal in `Comon C`.
-/
@[simps!]
/-
**CategoryTheory.Comon.trivial** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Comon`。
形式化陈述：trivial : Comon C
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The trivial comonoid object. We later show this is terminal in `Comon C`.
-/
def trivial : Comon C := mk (𝟙_ C)
/-
**CategoryTheory.Comon.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Comon`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Inhabited (Comon C) :=
  ⟨trivial C⟩

end Comon

namespace ComonObj

variable {M : C} [ComonObj M]

@[reassoc (attr := simp)]
/-
**CategoryTheory.ComonObj.counit_comul_hom** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTh
eory.ComonObj`。
形式化陈述：counit_comul_hom {Z : C} (f : M ⟶ Z) : Δ[M] ≫ (ε[M] otimesₘ f) = f ≫ (fun_
 Z).inv
参数：f : M ⟶ Z。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.MonoidalCategory.leftUnitor_inv_naturality`：leftUnitor_in
v_naturality {X Y : C} (f : X ⟶ Y) : f ≫ (fun_ Y).inv = (fun_ X).inv ≫ _ ◁ f
· 使用定理 `CategoryTheory.MonoidalCategory.tensorHom_def`：∀ {C : Type u} {𝒞 : Categ
oryTheory.Category.{v, u} C} [self : CategoryTheory.MonoidalCategory C] {X₁ Y₁ X
₂ Y₂ : C}   (f : X₁ ⟶ Y₁) (g : X₂ ⟶…
· 使用定理 `CategoryTheory.ComonObj.counit_comul_assoc`：∀ {C : Type u₁} {inst : Cate
goryTheory.Category.{v₁, u₁} C} {inst_1 : CategoryTheory.MonoidalCategory C} (X 
: C)   [self : CategoryTheory.Co…
-/
theorem counit_comul_hom {Z : C} (f : M ⟶ Z) : Δ[M] ≫ (ε[M] ⊗ₘ f) = f ≫ (λ_ Z).inv := by
  rw [leftUnitor_inv_naturality, tensorHom_def, counit_comul_assoc]

@[reassoc (attr := simp)]
/-
**CategoryTheory.ComonObj.comul_counit_hom** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTh
eory.ComonObj`。
形式化陈述：comul_counit_hom {Z : C} (f : M ⟶ Z) : Δ[M] ≫ (f otimesₘ ε[M]) = f ≫ (ρ_ Z
).inv
参数：f : M ⟶ Z。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.MonoidalCategory.rightUnitor_inv_naturality`：rightUnitor_
inv_naturality {X X' : C} (f : X ⟶ X') : f ≫ (ρ_ X').inv = (ρ_ X).inv ≫ f ▷ _
· 使用定理 `CategoryTheory.MonoidalCategory.tensorHom_def'`：tensorHom_def' {X₁ Y₁ X₂
 Y₂ : C} (f : X₁ ⟶ Y₁) (g : X₂ ⟶ Y₂) : f otimesₘ g = X₁ ◁ g ≫ f ▷ Y₂
· 使用定理 `CategoryTheory.ComonObj.comul_counit_assoc`：∀ {C : Type u₁} {inst : Cate
goryTheory.Category.{v₁, u₁} C} {inst_1 : CategoryTheory.MonoidalCategory C} (X 
: C)   [self : CategoryTheory.Co…
-/
theorem comul_counit_hom {Z : C} (f : M ⟶ Z) : Δ[M] ≫ (f ⊗ₘ ε[M]) = f ≫ (ρ_ Z).inv := by
  rw [rightUnitor_inv_naturality, tensorHom_def', comul_counit_assoc]

@[reassoc]
/-
**CategoryTheory.ComonObj.comul_assoc_flip** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTh
eory.ComonObj`。
形式化陈述：comul_assoc_flip (X : C) [ComonObj X] : Δ ≫ Δ ▷ X = Δ ≫ X ◁ Δ ≫ (α_ X X X)
.inv
参数：X : C。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.ComonObj.comul_assoc_assoc`：∀ {C : Type u₁} {inst : Categ
oryTheory.Category.{v₁, u₁} C} {inst_1 : CategoryTheory.MonoidalCategory C} (X :
 C)   [self : CategoryTheory.Co…
· 使用定理 `CategoryTheory.Iso.hom_inv_id`：∀ {C : Type u} [inst : CategoryTheory.Cat
egory.{v, u} C] {X Y : C} (self : X ≅ Y),   CategoryTheory.CategoryStruct.comp s
elf.hom self.inv = …
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem comul_assoc_flip (X : C) [ComonObj X] :
    Δ ≫ Δ ▷ X = Δ ≫ X ◁ Δ ≫ (α_ X X X).inv := by
  simp

end ComonObj

namespace Comon

open MonObj ComonObj

/-- A morphism of comonoid objects. -/
@[ext]
/-
**CategoryTheory.Comon.Hom** 是 Mathlib 中的一个归纳类型，位于命名空间 `CategoryTheory.Comon`。
形式化陈述：{C : Type u₁} →   [inst : CategoryTheory.Category.{v₁, u₁} C] →     [inst_
1 : CategoryTheory.MonoidalCategory C] → CategoryTheory.Comon C → CategoryTheory
.Comon C → Type v₁
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A morphism of comonoid objects.
-/
structure Hom (M N : Comon C) where
  /-- The underlying morphism of a morphism of comonoid objects. -/
  hom : M.X ⟶ N.X
  [isComonHom_hom : IsComonHom hom]

attribute [instance] Hom.isComonHom_hom

/-- Construct a morphism `M ⟶ N` of `Comon C` from a map `f : M ⟶ N` and a `IsComonHom f`
instance. -/
/-
**CategoryTheory.Comon.Hom.mk'** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Comon.H
om`。
形式化陈述：{C : Type u₁} →   [inst : CategoryTheory.Category.{v₁, u₁} C] →     [inst_
1 : CategoryTheory.MonoidalCategory C] →       {M N : CategoryTheory.Comon C} → 
        (f : M.X ⟶ N.X) →           autoParam               (CategoryTheory.Cate
goryStruct.comp f CategoryTheory.ComonObj.counit = CategoryTheory.ComonObj.couni
t)               CategoryTheory.Comon.Hom.mk'._auto_1 →             autoParam   
              (CategoryTheory.CategoryStruct.comp f CategoryTheory.ComonObj.comu
l =                   CategoryTheory.CategoryStruct.comp CategoryTheory.ComonObj
.comul                     (CategoryTheory.MonoidalCategoryStruct.tensorHom f f)
)                 CategoryTheory.Comon.Hom.mk'._auto_3 →               M.Hom N
参数：f : M.X ⟶ N.X；CategoryTheory.CategoryStruct.comp f CategoryTheory.ComonObj.co
unit = CategoryTheory.ComonObj.counit；CategoryTheory.CategoryStruct.comp f Categ
oryTheory.ComonObj.comul =                   CategoryTheory.CategoryStruct.comp 
CategoryTheory.ComonObj.comul                     (CategoryTheory.MonoidalCatego
ryStruct.tensorHom f f)。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Construct a morphism `M ⟶ N` of `Comon C` from a map `f : M ⟶ N` and a `IsComonH
om f`
instance.
-/
abbrev Hom.mk' {M N : Comon C} (f : M.X ⟶ N.X)
    (f_counit : f ≫ ε[N.X] = ε[M.X] := by cat_disch)
    (f_comul : f ≫ Δ[N.X] = Δ[M.X] ≫ (f ⊗ₘ f) := by cat_disch) :
    Hom M N :=
  have : IsComonHom f := ⟨f_counit, f_comul⟩
  .mk f

/-- The identity morphism on a comonoid object. -/
@[simps]
/-
**CategoryTheory.Comon.id** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Comon`。
形式化陈述：id (M : Comon C) : Hom M M where hom
参数：M : Comon C。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The identity morphism on a comonoid object.
-/
def id (M : Comon C) : Hom M M where
  hom := 𝟙 M.X
/-
**CategoryTheory.Comon.homInhabited** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Co
mon`。
形式化陈述：homInhabited (M : Comon C) : Inhabited (Hom M M)
参数：M : Comon C。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance homInhabited (M : Comon C) : Inhabited (Hom M M) :=
  ⟨id M⟩

/-- Composition of morphisms of monoid objects. -/
@[simps]
/-
**CategoryTheory.Comon.comp** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Comon`。
形式化陈述：comp {M N O : Comon C} (f : Hom M N) (g : Hom N O) : Hom M O where hom
参数：f : Hom M N；g : Hom N O。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Composition of morphisms of monoid objects.
-/
def comp {M N O : Comon C} (f : Hom M N) (g : Hom N O) : Hom M O where
  hom := f.hom ≫ g.hom
/-
**CategoryTheory.Comon.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Comon`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Category (Comon C) where
  Hom M N := Hom M N
  id := id
  comp f g := comp f g
/-
**CategoryTheory.Comon.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Comon`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {M N : Comon C} (f : M ⟶ N) : IsComonHom f.hom := inferInstanceAs (IsComonHom f.hom)
/-
**CategoryTheory.Comon.ext** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.Comon`。
形式化陈述：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] [inst_1 : Cate
goryTheory.MonoidalCategory C]   {X Y : CategoryTheory.Comon C} {f g : X ⟶ Y}, f
.hom = g.hom → f = g
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Comon.Hom.ext`：∀ {C : Type u₁} {inst : CategoryTheory.Cat
egory.{v₁, u₁} C} {inst_1 : CategoryTheory.MonoidalCategory C}   {M N : Category
Theory.Comon C} {x…
-/
@[ext] lemma ext {X Y : Comon C} {f g : X ⟶ Y} (w : f.hom = g.hom) : f = g := Hom.ext w
/-
**CategoryTheory.Comon.id_hom'** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.Comon`。
形式化陈述：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] [inst_1 : Cate
goryTheory.MonoidalCategory C]   (M : CategoryTheory.Comon C), (CategoryTheory.C
ategoryStruct.id M).hom = CategoryTheory.CategoryStruct.id M.X
参数：M : CategoryTheory.Comon C；CategoryTheory.CategoryStruct.id M。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] theorem id_hom' (M : Comon C) : (𝟙 M : Hom M M).hom = 𝟙 M.X := rfl

@[simp]
/-
**CategoryTheory.Comon.comp_hom'** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.Comon
`。
形式化陈述：comp_hom' {M N K : Comon C} (f : M ⟶ N) (g : N ⟶ K) : (f ≫ g).hom = f.hom 
≫ g.hom
参数：f : M ⟶ N；g : N ⟶ K。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem comp_hom' {M N K : Comon C} (f : M ⟶ N) (g : N ⟶ K) : (f ≫ g).hom = f.hom ≫ g.hom :=
  rfl

section

variable (C)

/-- The forgetful functor from comonoid objects to the ambient category. -/
@[simps]
/-
**CategoryTheory.Comon.forget** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Comon`。
形式化陈述：forget : Comon C ⥤ C where obj A
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The forgetful functor from comonoid objects to the ambient category.
-/
def forget : Comon C ⥤ C where
  obj A := A.X
  map f := f.hom

end

/-
**CategoryTheory.Comon.forget_faithful** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory
.Comon`。
形式化陈述：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] [inst_1 : Cate
goryTheory.MonoidalCategory C],   (CategoryTheory.Comon.forget C).Faithful
参数：CategoryTheory.Comon.forget C。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Comon.ext`：∀ {C : Type u₁} [inst : CategoryTheory.Categor
y.{v₁, u₁} C] [inst_1 : CategoryTheory.MonoidalCategory C]   {X Y : CategoryTheo
ry.Comon C} {f…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `CategoryTheory.Comon.forget_map`：∀ (C : Type u₁) [inst : CategoryTheory.
Category.{v₁, u₁} C] [inst_1 : CategoryTheory.MonoidalCategory C]   {X Y : Categ
oryTheory.Comon C} (f…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
instance forget_faithful : (@forget C _ _).Faithful where
/-
**CategoryTheory.Comon.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Comon`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {A B : Comon C} (f : A ⟶ B) [e : IsIso ((forget C).map f)] : IsIso f.hom := e

/-- The forgetful functor from comonoid objects to the ambient category reflects isomorphisms. -/
/-
**CategoryTheory.Comon.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Comon`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The forgetful functor from comonoid objects to the ambient category reflects iso
morphisms.
-/
instance : (forget C).ReflectsIsomorphisms where
  reflects f e :=
    ⟨⟨{ hom := inv f.hom }, by cat_disch⟩⟩

/-- Construct an isomorphism of comonoids by giving an isomorphism between the underlying objects
and checking compatibility with counit and comultiplication only in the forward direction.
-/
@[simps]
/-
**CategoryTheory.Comon.mkIso'** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Comon`。
形式化陈述：mkIso' {M N : Comon C} (f : M.X ≅ N.X) [IsComonHom f.hom] : M ≅ N where ho
m
参数：f : M.X ≅ N.X。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Construct an isomorphism of comonoids by giving an isomorphism between the under
lying objects
and checking compatibility with counit and comultiplication only in the forward 
direction.
-/
def mkIso' {M N : Comon C} (f : M.X ≅ N.X) [IsComonHom f.hom] : M ≅ N where
  hom := Hom.mk f.hom
  inv := Hom.mk f.inv

/-- Construct an isomorphism of comonoids by giving an isomorphism between the underlying objects
and checking compatibility with counit and comultiplication only in the forward direction.
-/
@[simps]
/-
**CategoryTheory.Comon.mkIso** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Comon`。
形式化陈述：mkIso {M N : Comon C} (f : M.X ≅ N.X) (f_counit : f.hom ≫ ε[N.X] = ε[M.X]
参数：f : M.X ≅ N.X。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Construct an isomorphism of comonoids by giving an isomorphism between the under
lying objects
and checking compatibility with counit and comultiplication only in the forward 
direction.
-/
def mkIso {M N : Comon C} (f : M.X ≅ N.X) (f_counit : f.hom ≫ ε[N.X] = ε[M.X] := by cat_disch)
    (f_comul : f.hom ≫ Δ[N.X] = Δ[M.X] ≫ (f.hom ⊗ₘ f.hom) := by cat_disch) : M ≅ N :=
  have : IsComonHom f.hom := ⟨f_counit, f_comul⟩
  ⟨⟨f.hom⟩, ⟨f.inv⟩, by cat_disch, by cat_disch⟩

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
@[simps]
/-
**CategoryTheory.Comon.uniqueHomToTrivial** 是 Mathlib 中的一个实例，位于命名空间 `CategoryThe
ory.Comon`。
形式化陈述：uniqueHomToTrivial (A : Comon C) : Unique (A ⟶ trivial C) where default.ho
m
参数：A : Comon C。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance uniqueHomToTrivial (A : Comon C) : Unique (A ⟶ trivial C) where
  default.hom := ε[A.X]
  default.isComonHom_hom.hom_comul := by simp [unitors_inv_equal]
  uniq f := by
    ext
    rw [← Category.comp_id f.hom]
    dsimp only [trivial_X]
    rw [← trivial_comon_counit, IsComonHom.hom_counit]

open CategoryTheory.Limits
/-
**CategoryTheory.Comon.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Comon`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : HasTerminal (Comon C) :=
  hasTerminal_of_unique (trivial C)

open Opposite

/-- Auxiliary definition for `ComonToMonOpOpObj`. -/
/-
**CategoryTheory.Comon.ComonToMonOpOpObjMon** 是 Mathlib 中的一个缩写定义，位于命名空间 `Categor
yTheory.Comon`。
形式化陈述：ComonToMonOpOpObjMon (A : Comon C) : MonObj (op A.X) where one
参数：A : Comon C。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Auxiliary definition for `ComonToMonOpOpObj`.
-/
abbrev ComonToMonOpOpObjMon (A : Comon C) : MonObj (op A.X) where
  one := ε[A.X].op
  mul := Δ[A.X].op
  one_mul := by
    rw [← op_whiskerRight, ← op_comp, counit_comul]
    rfl
  mul_one := by
    rw [← op_whiskerLeft, ← op_comp, comul_counit]
    rfl
  mul_assoc := by
    rw [← op_inv_associator, ← op_whiskerRight, ← op_comp, ← op_whiskerLeft, ← op_comp,
      comul_assoc_flip, op_comp, op_comp_assoc]
    rfl

/--
Turn a comonoid object into a monoid object in the opposite category.
-/
/-
**CategoryTheory.Comon.ComonToMonOpOpObj** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheo
ry.Comon`。
形式化陈述：{C : Type u₁} →   [inst : CategoryTheory.Category.{v₁, u₁} C] →     [inst_
1 : CategoryTheory.MonoidalCategory C] → CategoryTheory.Comon C → CategoryTheory
.Mon Cᵒᵖ
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Turn a comonoid object into a monoid object in the opposite category.
-/
@[simps] def ComonToMonOpOpObj (A : Comon C) : Mon Cᵒᵖ where
  X := op A.X
  mon := ComonToMonOpOpObjMon A

set_option backward.defeqAttrib.useBackward true in
variable (C) in
/--
The contravariant functor turning comonoid objects into monoid objects in the opposite category.
-/
/-
**CategoryTheory.Comon.ComonToMonOpOp** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.
Comon`。
形式化陈述：(C : Type u₁) →   [inst : CategoryTheory.Category.{v₁, u₁} C] →     [inst_
1 : CategoryTheory.MonoidalCategory C] →       CategoryTheory.Functor (CategoryT
heory.Comon C) (CategoryTheory.Mon Cᵒᵖ)ᵒᵖ
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The contravariant functor turning comonoid objects into monoid objects in the op
posite category.
-/
@[simps] def ComonToMonOpOp : Comon C ⥤ (Mon Cᵒᵖ)ᵒᵖ where
  obj A := op (ComonToMonOpOpObj A)
  map := fun f => op <|
    { hom := f.hom.op
      isMonHom_hom.one_hom := by apply Quiver.Hom.unop_inj; simp
      isMonHom_hom.mul_hom := by apply Quiver.Hom.unop_inj; simp }

/-- Auxiliary definition for `MonOpOpToComonObj`. -/
/-
**CategoryTheory.Comon.MonOpOpToComonObjComon** 是 Mathlib 中的一个缩写定义，位于命名空间 `Categ
oryTheory.Comon`。
形式化陈述：MonOpOpToComonObjComon (A : Mon Cᵒᵖ) : ComonObj (unop A.X) where counit
参数：A : Mon Cᵒᵖ。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Auxiliary definition for `MonOpOpToComonObj`.
-/
abbrev MonOpOpToComonObjComon (A : Mon Cᵒᵖ) : ComonObj (unop A.X) where
  counit := η[A.X].unop
  comul := μ[A.X].unop
  counit_comul := by rw [← unop_whiskerRight, ← unop_comp, MonObj.one_mul]; rfl
  comul_counit := by rw [← unop_whiskerLeft, ← unop_comp, MonObj.mul_one]; rfl
  comul_assoc := by
    rw [← unop_whiskerRight, ← unop_whiskerLeft, ← unop_comp_assoc, ← unop_comp,
      MonObj.mul_assoc_flip]
    rfl

/--
Turn a monoid object in the opposite category into a comonoid object.
-/
/-
**CategoryTheory.Comon.MonOpOpToComonObj** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheo
ry.Comon`。
形式化陈述：{C : Type u₁} →   [inst : CategoryTheory.Category.{v₁, u₁} C] →     [inst_
1 : CategoryTheory.MonoidalCategory C] → CategoryTheory.Mon Cᵒᵖ → CategoryTheory
.Comon C
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Turn a monoid object in the opposite category into a comonoid object.
-/
@[simps] def MonOpOpToComonObj (A : Mon Cᵒᵖ) : Comon C where
  X := unop A.X
  comon := MonOpOpToComonObjComon A

variable (C)

set_option backward.defeqAttrib.useBackward true in
/--
The contravariant functor turning monoid objects in the opposite category into comonoid objects.
-/
@[simps]
/-
**CategoryTheory.Comon.MonOpOpToComon** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.
Comon`。
形式化陈述：MonOpOpToComon : (Mon Cᵒᵖ)ᵒᵖ ⥤ Comon C where obj A
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The contravariant functor turning monoid objects in the opposite category into c
omonoid objects.
-/
def MonOpOpToComon : (Mon Cᵒᵖ)ᵒᵖ ⥤ Comon C where
  obj A := MonOpOpToComonObj (unop A)
  map := fun f =>
    { hom := f.unop.hom.unop
      isComonHom_hom.hom_counit := by apply Quiver.Hom.op_inj; simp
      isComonHom_hom.hom_comul := by apply Quiver.Hom.op_inj; simp [op_tensorHom] }

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/--
Comonoid objects are contravariantly equivalent to monoid objects in the opposite category.
-/
@[simps]
/-
**CategoryTheory.Comon.Comon_EquivMon_OpOp** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTh
eory.Comon`。
形式化陈述：Comon_EquivMon_OpOp : Comon C ≌ (Mon Cᵒᵖ)ᵒᵖ where functor
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Comonoid objects are contravariantly equivalent to monoid objects in the opposit
e category.
-/
def Comon_EquivMon_OpOp : Comon C ≌ (Mon Cᵒᵖ)ᵒᵖ where
  functor := ComonToMonOpOp C
  inverse := MonOpOpToComon C
  unitIso := NatIso.ofComponents fun _ => .refl _
  counitIso := NatIso.ofComponents fun _ => .refl _

#adaptation_note /-- After https://github.com/leanprover/lean4/pull/12179
the simpNF linter complains about `monoidal_tensorObj_comon_counit` being `@[simp]`.
So we spell out all the other ones.
-/
#adaptation_note
/-- `respectTransparency.types true` changes the auto-generated lemmas' signature -/
set_option backward.isDefEq.respectTransparency.types false in
/--
Comonoid objects in a braided category form a monoidal category.

This definition is via transporting back and forth to monoids in the opposite category.
-/
@[simps!
  tensorObj_X tensorObj_comon_comul
  whiskerLeft_hom whiskerRight_hom
  tensorHom_hom
  tensorUnit_X tensorUnit_comon_counit tensorUnit_comon_comul
  associator_hom_hom associator_inv_hom
  leftUnitor_hom_hom leftUnitor_inv_hom
  rightUnitor_hom_hom rightUnitor_inv_hom]
/-
**CategoryTheory.Comon.monoidal** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Comon`
。
形式化陈述：monoidal [BraidedCategory C] : MonoidalCategory (Comon C)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance monoidal [BraidedCategory C] : MonoidalCategory (Comon C) :=
  Monoidal.transport (Comon_EquivMon_OpOp C).symm

variable {C} [BraidedCategory C]
/-
**CategoryTheory.Comon.tensorObj_X** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.Com
on`。
形式化陈述：tensorObj_X (A B : Comon C) : (A otimes B).X = A.X otimes B.X
参数：A B : Comon C。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem tensorObj_X (A B : Comon C) : (A ⊗ B).X = A.X ⊗ B.X := rfl
/-
**CategoryTheory.Comon.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Comon`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (A B : C) [ComonObj A] [ComonObj B] : ComonObj (A ⊗ B) :=
  inferInstanceAs <| ComonObj (Comon.mk A ⊗ Comon.mk B).X

@[simp]
/-
**CategoryTheory.Comon.tensorObj_counit** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheor
y.Comon`。
形式化陈述：tensorObj_counit (A B : C) [ComonObj A] [ComonObj B] : ε[A otimes B] = (ε[
A] otimesₘ ε[B]) ≫ (fun_ _).hom
参数：A B : C。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem tensorObj_counit (A B : C) [ComonObj A] [ComonObj B] :
    ε[A ⊗ B] = (ε[A] ⊗ₘ ε[B]) ≫ (λ_ _).hom :=
  rfl

/--
Preliminary statement of the comultiplication for a tensor product of comonoids.
This version is the definitional equality provided by transport, and not quite as good as
the version provided in `tensorObj_comul` below.
-/
/-
**CategoryTheory.Comon.tensorObj_comul'** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheor
y.Comon`。
形式化陈述：tensorObj_comul' (A B : C) [ComonObj A] [ComonObj B] : Δ[A otimes B] = (Δ[
A] otimesₘ Δ[B]) ≫ (tensorμ (op A) (op B) (op A) (op B)).unop
参数：A B : C。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Preliminary statement of the comultiplication for a tensor product of comonoids.
This version is the definitional equality provided by transport, and not quite a
s good as
the version provided in `tensorObj_comul` below.
-/
theorem tensorObj_comul' (A B : C) [ComonObj A] [ComonObj B] :
    Δ[A ⊗ B] =
      (Δ[A] ⊗ₘ Δ[B]) ≫ (tensorμ (op A) (op B) (op A) (op B)).unop := by
  rfl

/--
The comultiplication on the tensor product of two comonoids is
the tensor product of the comultiplications followed by the tensor strength
(to shuffle the factors back into order).
-/
@[simp]
/-
**CategoryTheory.Comon.tensorObj_comul** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory
.Comon`。
形式化陈述：tensorObj_comul (A B : C) [ComonObj A] [ComonObj B] : Δ[A otimes B] = (Δ[A
] otimesₘ Δ[B]) ≫ tensorμ A A B B
参数：A B : C。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Comon.tensorObj_comul'`：tensorObj_comul' (A B : C) [Comon
Obj A] [ComonObj B] : Δ[A otimes B] = (Δ[A] otimesₘ Δ[B]) ≫ (tensorμ (op A) (op 
B) (op A) (op B)).unop
· 使用定理 `CategoryTheory.BraidedCategory.unop_tensorμ`：∀ {C : Type u_2} [inst : Ca
tegoryTheory.Category.{v_2, u_2} C] [inst_1 : CategoryTheory.MonoidalCategory C]
   [inst_2 : CategoryTheory.Braid…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
The comultiplication on the tensor product of two comonoids is
the tensor product of the comultiplications followed by the tensor strength
(to shuffle the factors back into order).
-/
theorem tensorObj_comul (A B : C) [ComonObj A] [ComonObj B] :
    Δ[A ⊗ B] = (Δ[A] ⊗ₘ Δ[B]) ≫ tensorμ A A B B := by
  simp [tensorObj_comul']

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The forgetful functor from `Comon C` to `C` is monoidal when `C` is monoidal. -/
/-
**CategoryTheory.Comon.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Comon`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The forgetful functor from `Comon C` to `C` is monoidal when `C` is monoidal.
-/
instance : (forget C).Monoidal :=
  Functor.CoreMonoidal.toMonoidal
    { εIso := Iso.refl _
      μIso := fun _ _ ↦ Iso.refl _ }

open Functor.LaxMonoidal Functor.OplaxMonoidal
/-
**CategoryTheory.Comon.forget_** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.Comon`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] theorem forget_ε : «ε» (forget C) = 𝟙 (𝟙_ C) := rfl
/-
**CategoryTheory.Comon.forget_** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.Comon`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] theorem forget_η : «η» (forget C) = 𝟙 (𝟙_ C) := rfl
/-
**CategoryTheory.Comon.forget_** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.Comon`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] theorem forget_μ (X Y : Comon C) : «μ» (forget C) X Y = 𝟙 (X.X ⊗ Y.X) := rfl
/-
**CategoryTheory.Comon.forget_** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.Comon`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] theorem forget_δ (X Y : Comon C) : δ (forget C) X Y = 𝟙 (X.X ⊗ Y.X) := rfl

end Comon

namespace Functor

variable {D : Type u₂} [Category.{v₂} D] [MonoidalCategory.{v₂} D]

open OplaxMonoidal ComonObj IsComonHom

/-- The image of a comonoid object under an oplax monoidal functor is a comonoid object. -/
/-
**CategoryTheory.Functor.obj.instComonObj** 是 Mathlib 中的一个定义，位于命名空间 `CategoryThe
ory.Functor.obj`。
形式化陈述：{C : Type u₁} →   [inst : CategoryTheory.Category.{v₁, u₁} C] →     [inst_
1 : CategoryTheory.MonoidalCategory C] →       {D : Type u₂} →         [inst_2 :
 CategoryTheory.Category.{v₂, u₂} D] →           [inst_3 : CategoryTheory.Monoid
alCategory D] →             (A : C) →               [CategoryTheory.ComonObj A] 
→                 (F : CategoryTheory.Functor C D) → [F.OplaxMonoidal] → Categor
yTheory.ComonObj (F.obj A)
参数：A : C；F : CategoryTheory.Functor C D；F.obj A。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The image of a comonoid object under an oplax monoidal functor is a comonoid obj
ect.
-/
abbrev obj.instComonObj (A : C) [ComonObj A] (F : C ⥤ D) [F.OplaxMonoidal] :
    ComonObj (F.obj A) where
  counit := F.map ε[A] ≫ η F
  comul := F.map Δ[A] ≫ δ F _ _
  counit_comul := by
    simp_rw [comp_whiskerRight, Category.assoc, δ_natural_left_assoc, left_unitality,
      ← F.map_comp_assoc, counit_comul]
  comul_counit := by
    simp_rw [MonoidalCategory.whiskerLeft_comp, Category.assoc, δ_natural_right_assoc,
      right_unitality, ← F.map_comp_assoc, comul_counit]
  comul_assoc := by
    simp_rw [comp_whiskerRight, Category.assoc, δ_natural_left_assoc,
      MonoidalCategory.whiskerLeft_comp, δ_natural_right_assoc,
      ← F.map_comp_assoc, comul_assoc, F.map_comp, Category.assoc, associativity]

attribute [local instance] obj.instComonObj
/-
**CategoryTheory.Functor.obj.** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.Functor`
。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[reassoc, simp] lemma obj.ε_def (F : C ⥤ D) [F.OplaxMonoidal] (X : C) [ComonObj X] :
    ε[F.obj X] = F.map ε ≫ η F :=
  rfl
/-
**CategoryTheory.Functor.obj.** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.Functor`
。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[reassoc, simp] lemma obj.Δ_def (F : C ⥤ D) [F.OplaxMonoidal] (X : C) [ComonObj X] :
    Δ[F.obj X] = F.map Δ ≫ δ F _ _ :=
  rfl
/-
**CategoryTheory.Functor.map.instIsComon_Hom** 是 Mathlib 中的一个定理，位于命名空间 `Category
Theory.Functor.map`。
形式化陈述：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] [inst_1 : Cate
goryTheory.MonoidalCategory C] {D : Type u₂}   [inst_2 : CategoryTheory.Category
.{v₂, u₂} D] [inst_3 : CategoryTheory.MonoidalCategory D]   (F : CategoryTheory.
Functor C D) [inst_4 : F.OplaxMonoidal] {X Y : C} [inst_5 : CategoryTheory.Comon
Obj X]   [inst_6 : CategoryTheory.ComonObj Y] (f : X ⟶ Y) [CategoryTheory.IsComo
nHom f], CategoryTheory.IsComonHom (F.map f)
参数：F : CategoryTheory.Functor C D；f : X ⟶ Y；F.map f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.Functor.map_comp_assoc`：∀ {C : Type u₁} [inst : CategoryT
heory.Category.{v_1, u₁} C] {D : Type u₂}   [inst_1 : CategoryTheory.Category.{v
_2, u₂} D] (F : CategoryThe…
· 使用定理 `CategoryTheory.IsComonHom.hom_counit`：∀ {C : Type u₁} {inst : CategoryTh
eory.Category.{v₁, u₁} C} {inst_1 : CategoryTheory.MonoidalCategory C} {M N : C}
   {inst_2 : CategoryTheor…
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.Functor.OplaxMonoidal.δ_natural`：δ_natural {X Y X' Y' : C
} (f : X ⟶ Y) (g : X' ⟶ Y') : δ F X X' ≫ (F.map f otimesₘ F.map g) = F.map (f ot
imesₘ g) ≫ δ F Y Y'
· 使用定理 `CategoryTheory.IsComonHom.hom_comul`：∀ {C : Type u₁} {inst : CategoryThe
ory.Category.{v₁, u₁} C} {inst_1 : CategoryTheory.MonoidalCategory C} {M N : C} 
  {inst_2 : CategoryTheor…
-/
instance map.instIsComon_Hom
    (F : C ⥤ D) [F.OplaxMonoidal]
    {X Y : C} [ComonObj X] [ComonObj Y] (f : X ⟶ Y) [IsComonHom f] :
    IsComonHom (F.map f) where
  hom_counit := by dsimp; rw [← F.map_comp_assoc, hom_counit]
  hom_comul := by
    dsimp
    rw [Category.assoc, δ_natural, ← F.map_comp_assoc, ← F.map_comp_assoc, hom_comul]

/-- An oplax monoidal functor takes comonoid objects to comonoid objects.

That is, an oplax monoidal functor `F : C ⥤ D` induces a functor `Comon C ⥤ Comon D`.
-/
@[simps]
/-
**CategoryTheory.Functor.mapComon** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Func
tor`。
形式化陈述：mapComon (F : C ⥤ D) [F.OplaxMonoidal] : Comon C ⥤ Comon D where obj A
参数：F : C ⥤ D。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An oplax monoidal functor takes comonoid objects to comonoid objects.

That is, an oplax monoidal functor `F : C ⥤ D` induces a functor `Comon C ⥤ Como
n D`.
-/
def mapComon (F : C ⥤ D) [F.OplaxMonoidal] : Comon C ⥤ Comon D where
  obj A :=
    { X := F.obj A.X }
  map f :=
    { hom := F.map f.hom }
  map_id A := by ext; simp
  map_comp f g := by ext; simp

-- TODO We haven't yet set up the category structure on `OplaxMonoidalFunctor C D`
-- and so can't state `mapComonFunctor : OplaxMonoidalFunctor C D ⥤ Comon C ⥤ Comon D`.

end Functor

variable [BraidedCategory.{v₁} C]

/-- Predicate for a comonoid object to be commutative. -/
/-
**CategoryTheory.IsCommComonObj** 是 Mathlib 中的一个类，位于命名空间 `CategoryTheory`。
形式化陈述：IsCommComonObj (X : C) [ComonObj X] where comul_comm (X) : Δ ≫ (β_ X X).ho
m = Δ
参数：X : C；X。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Predicate for a comonoid object to be commutative.
-/
class IsCommComonObj (X : C) [ComonObj X] where
  comul_comm (X) : Δ ≫ (β_ X X).hom = Δ := by cat_disch

open scoped ComonObj

attribute [reassoc (attr := simp)] IsCommComonObj.comul_comm

end CategoryTheory

