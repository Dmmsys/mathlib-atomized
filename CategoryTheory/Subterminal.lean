/-
Copyright (c) 2020 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public import Mathlib.CategoryTheory.Limits.Shapes.BinaryProducts
public import Mathlib.CategoryTheory.Limits.Shapes.Terminal
public import Mathlib.CategoryTheory.Subobject.MonoOver

/-!
# Subterminal objects

Subterminal objects are the objects which can be thought of as subobjects of the terminal object.
In fact, the definition can be constructed to not require a terminal object, by defining `A` to be
subterminal iff for any `Z`, there is at most one morphism `Z ⟶ A`.
An alternate definition is that the diagonal morphism `A ⟶ A ⨯ A` is an isomorphism.
In this file we define subterminal objects and show the equivalence of these three definitions.

We also construct the subcategory of subterminal objects.

## TODO

* Define exponential ideals, and show this subcategory is an exponential ideal.
* Use the above to show that in a locally Cartesian closed category, every subobject lattice
  is Cartesian closed (equivalently, a Heyting algebra).

-/

@[expose] public section


universe v₁ v₂ u₁ u₂

noncomputable section

namespace CategoryTheory

open Limits Category

variable {C : Type u₁} [Category.{v₁} C] {A : C}

/-- An object `A` is subterminal iff for any `Z`, there is at most one morphism `Z ⟶ A`. -/
/-
**CategoryTheory.IsSubterminal** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory`。
形式化陈述：IsSubterminal (A : C) : Prop
参数：A : C。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An object `A` is subterminal iff for any `Z`, there is at most one morphism `Z ⟶
 A`.
-/
def IsSubterminal (A : C) : Prop :=
  ∀ ⦃Z : C⦄ (f g : Z ⟶ A), f = g
/-
**CategoryTheory.IsSubterminal.def** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.IsS
ubterminal`。
形式化陈述：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {A : C},   Cat
egoryTheory.IsSubterminal A ↔ ∀ ⦃Z : C⦄ (f g : Z ⟶ A), f = g
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem IsSubterminal.def : IsSubterminal A ↔ ∀ ⦃Z : C⦄ (f g : Z ⟶ A), f = g :=
  Iff.rfl

/-- If `A` is subterminal, the unique morphism from it to a terminal object is a monomorphism.
The converse of `isSubterminal_of_mono_isTerminal_from`.
-/
/-
**CategoryTheory.IsSubterminal.mono_isTerminal_from** 是 Mathlib 中的一个定理，位于命名空间 `C
ategoryTheory.IsSubterminal`。
形式化陈述：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {A : C},   Cat
egoryTheory.IsSubterminal A → ∀ {T : C} (hT : CategoryTheory.Limits.IsTerminal T
), CategoryTheory.Mono (hT.from A)
参数：hT : CategoryTheory.Limits.IsTerminal T；hT.from A。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `A` is subterminal, the unique morphism from it to a terminal object is a mon
omorphism.
The converse of `isSubterminal_of_mono_isTerminal_from`.
-/
theorem IsSubterminal.mono_isTerminal_from (hA : IsSubterminal A) {T : C} (hT : IsTerminal T) :
    Mono (hT.from A) :=
  { right_cancellation := fun _ _ _ => hA _ _ }

/-- If `A` is subterminal, the unique morphism from it to the terminal object is a monomorphism.
The converse of `isSubterminal_of_mono_terminal_from`.
-/
/-
**CategoryTheory.IsSubterminal.mono_terminal_from** 是 Mathlib 中的一个定理，位于命名空间 `Cat
egoryTheory.IsSubterminal`。
形式化陈述：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {A : C} [inst_
1 : CategoryTheory.Limits.HasTerminal C],   CategoryTheory.IsSubterminal A → Cat
egoryTheory.Mono (CategoryTheory.Limits.terminal.from A)
参数：CategoryTheory.Limits.terminal.from A。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.IsSubterminal.mono_isTerminal_from`：∀ {C : Type u₁} [inst
 : CategoryTheory.Category.{v₁, u₁} C] {A : C},   CategoryTheory.IsSubterminal A
 → ∀ {T : C} (hT : CategoryTheory.Limit…

--- 原说明 ---
If `A` is subterminal, the unique morphism from it to the terminal object is a m
onomorphism.
The converse of `isSubterminal_of_mono_terminal_from`.
-/
theorem IsSubterminal.mono_terminal_from [HasTerminal C] (hA : IsSubterminal A) :
    Mono (terminal.from A) :=
  hA.mono_isTerminal_from terminalIsTerminal

/-- If the unique morphism from `A` to a terminal object is a monomorphism, `A` is subterminal.
The converse of `IsSubterminal.mono_isTerminal_from`.
-/
/-
**CategoryTheory.isSubterminal_of_mono_isTerminal_from** 是 Mathlib 中的一个定理，位于命名空间
 `CategoryTheory`。
形式化陈述：isSubterminal_of_mono_isTerminal_from {T : C} (hT : IsTerminal T) [Mono (h
T.from A)] : IsSubterminal A
参数：hT : IsTerminal T；hT.from A。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.cancel_mono`：∀ {C : Type u} [inst : CategoryTheory.Catego
ry.{v, u} C] {X Y Z : C} (f : Y ⟶ X) [CategoryTheory.Mono f] {g h : Z ⟶ Y},   Ca
tegoryTheory.Cat…
· 使用定理 `CategoryTheory.Limits.IsTerminal.hom_ext`：∀ {C : Type u₁} [inst : Catego
ryTheory.Category.{v₁, u₁} C] {X Y : C} (t : CategoryTheory.Limits.IsTerminal X)
   (f g : Y ⟶ X), f = g

--- 原说明 ---
If the unique morphism from `A` to a terminal object is a monomorphism, `A` is s
ubterminal.
The converse of `IsSubterminal.mono_isTerminal_from`.
-/
theorem isSubterminal_of_mono_isTerminal_from {T : C} (hT : IsTerminal T) [Mono (hT.from A)] :
    IsSubterminal A := fun Z f g => by
  rw [← cancel_mono (hT.from A)]
  apply hT.hom_ext

/-- If the unique morphism from `A` to the terminal object is a monomorphism, `A` is subterminal.
The converse of `IsSubterminal.mono_terminal_from`.
-/
/-
**CategoryTheory.isSubterminal_of_mono_terminal_from** 是 Mathlib 中的一个定理，位于命名空间 `
CategoryTheory`。
形式化陈述：isSubterminal_of_mono_terminal_from [HasTerminal C] [Mono (terminal.from A
)] : IsSubterminal A
参数：terminal.from A。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.cancel_mono`：∀ {C : Type u} [inst : CategoryTheory.Catego
ry.{v, u} C] {X Y Z : C} (f : Y ⟶ X) [CategoryTheory.Mono f] {g h : Z ⟶ Y},   Ca
tegoryTheory.Cat…
· 使用定理 `Subsingleton.elim`：∀ {α : Sort u} [h : Subsingleton α] (a b : α), a = b
· 使用定理 `Unique.instSubsingleton`：∀ {α : Sort u_1} [Unique α], Subsingleton α

--- 原说明 ---
If the unique morphism from `A` to the terminal object is a monomorphism, `A` is
 subterminal.
The converse of `IsSubterminal.mono_terminal_from`.
-/
theorem isSubterminal_of_mono_terminal_from [HasTerminal C] [Mono (terminal.from A)] :
    IsSubterminal A := fun Z f g => by
  rw [← cancel_mono (terminal.from A)]
  subsingleton
/-
**CategoryTheory.isSubterminal_of_isTerminal** 是 Mathlib 中的一个定理，位于命名空间 `Category
Theory`。
形式化陈述：isSubterminal_of_isTerminal {T : C} (hT : IsTerminal T) : IsSubterminal T
参数：hT : IsTerminal T。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.IsTerminal.hom_ext`：∀ {C : Type u₁} [inst : Catego
ryTheory.Category.{v₁, u₁} C] {X Y : C} (t : CategoryTheory.Limits.IsTerminal X)
   (f g : Y ⟶ X), f = g
-/
theorem isSubterminal_of_isTerminal {T : C} (hT : IsTerminal T) : IsSubterminal T := fun _ _ _ =>
  hT.hom_ext _ _
/-
**CategoryTheory.isSubterminal_of_terminal** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTh
eory`。
形式化陈述：isSubterminal_of_terminal [HasTerminal C] : IsSubterminal (⊤_ C)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subsingleton.elim`：∀ {α : Sort u} [h : Subsingleton α] (a b : α), a = b
· 使用定理 `Unique.instSubsingleton`：∀ {α : Sort u_1} [Unique α], Subsingleton α
-/
theorem isSubterminal_of_terminal [HasTerminal C] : IsSubterminal (⊤_ C) := fun _ _ _ => by
  subsingleton

set_option backward.isDefEq.respectTransparency false in
/-- If `A` is subterminal, its diagonal morphism is an isomorphism.
The converse of `isSubterminal_of_isIso_diag`.
-/
/-
**CategoryTheory.IsSubterminal.isIso_diag** 是 Mathlib 中的一个定理，位于命名空间 `CategoryThe
ory.IsSubterminal`。
形式化陈述：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {A : C},   Cat
egoryTheory.IsSubterminal A →     ∀ [inst_1 : CategoryTheory.Limits.HasBinaryPro
duct A A], CategoryTheory.IsIso (CategoryTheory.Limits.diag A)
参数：CategoryTheory.Limits.diag A。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Limits.limit.lift_π`：∀ {J : Type u₁} [inst : CategoryTheo
ry.Category.{v₁, u₁} J] {C : Type u} [inst_1 : CategoryTheory.Category.{v, u} C]
   {F : CategoryTheory.F…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `CategoryTheory.Limits.prod.comp_lift`：∀ {C : Type u} [inst : CategoryThe
ory.Category.{v, u} C] {V W X Y : C}   [inst_1 : CategoryTheory.Limits.HasBinary
Product X Y] (f : V ⟶ W) (…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `CategoryTheory.Limits.prod.hom_ext`：∀ {C : Type u} [inst : CategoryTheor
y.Category.{v, u} C] {W X Y : C}   [inst_1 : CategoryTheory.Limits.HasBinaryProd
uct X Y] {f g : W ⟶ X ⨯ …
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用定理 `CategoryTheory.IsSubterminal.def`：∀ {C : Type u₁} [inst : CategoryTheory
.Category.{v₁, u₁} C] {A : C},   CategoryTheory.IsSubterminal A ↔ ∀ ⦃Z : C⦄ (f g
 : Z ⟶ A), f = g

--- 原说明 ---
If `A` is subterminal, its diagonal morphism is an isomorphism.
The converse of `isSubterminal_of_isIso_diag`.
-/
theorem IsSubterminal.isIso_diag (hA : IsSubterminal A) [HasBinaryProduct A A] : IsIso (diag A) :=
  ⟨⟨Limits.prod.fst,
      ⟨by simp, by
        rw [IsSubterminal.def] at hA
        cat_disch⟩⟩⟩

set_option backward.isDefEq.respectTransparency false in
/-- If the diagonal morphism of `A` is an isomorphism, then it is subterminal.
The converse of `isSubterminal.isIso_diag`.
-/
/-
**CategoryTheory.isSubterminal_of_isIso_diag** 是 Mathlib 中的一个定理，位于命名空间 `Category
Theory`。
形式化陈述：isSubterminal_of_isIso_diag [HasBinaryProduct A A] [IsIso (diag A)] : IsSu
bterminal A
参数：diag A。
该定理/引理描述了相关对象所满足的性质。
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
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Limits.limit.lift_π`：∀ {J : Type u₁} [inst : CategoryTheo
ry.Category.{v₁, u₁} J] {C : Type u} [inst_1 : CategoryTheory.Category.{v, u} C]
   {F : CategoryTheory.F…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `CategoryTheory.Limits.prod.lift_fst`：∀ {C : Type u} [inst : CategoryTheo
ry.Category.{v, u} C] {W X Y : C}   [inst_1 : CategoryTheory.Limits.HasBinaryPro
duct X Y] (f : W ⟶ X) (g …
· 使用定理 `CategoryTheory.Limits.prod.lift_snd`：∀ {C : Type u} [inst : CategoryTheo
ry.Category.{v, u} C] {W X Y : C}   [inst_1 : CategoryTheory.Limits.HasBinaryPro
duct X Y] (f : W ⟶ X) (g …

--- 原说明 ---
If the diagonal morphism of `A` is an isomorphism, then it is subterminal.
The converse of `isSubterminal.isIso_diag`.
-/
theorem isSubterminal_of_isIso_diag [HasBinaryProduct A A] [IsIso (diag A)] : IsSubterminal A :=
  fun Z f g => by
  have : (Limits.prod.fst : A ⨯ A ⟶ _) = Limits.prod.snd := by simp [← cancel_epi (diag A)]
  rw [← prod.lift_fst f g, this, prod.lift_snd]

/-- If `A` is subterminal, it is isomorphic to `A ⨯ A`. -/
@[simps!]
/-
**CategoryTheory.IsSubterminal.isoDiag** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory
.IsSubterminal`。
形式化陈述：{C : Type u₁} →   [inst : CategoryTheory.Category.{v₁, u₁} C] →     {A : C
} → CategoryTheory.IsSubterminal A → [inst_1 : CategoryTheory.Limits.HasBinaryPr
oduct A A] → A ⨯ A ≅ A
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.IsSubterminal.isIso_diag`：∀ {C : Type u₁} [inst : Categor
yTheory.Category.{v₁, u₁} C] {A : C},   CategoryTheory.IsSubterminal A →     ∀ [
inst_1 : CategoryTheory.Limit…

--- 原说明 ---
If `A` is subterminal, it is isomorphic to `A ⨯ A`.
-/
def IsSubterminal.isoDiag (hA : IsSubterminal A) [HasBinaryProduct A A] : A ⨯ A ≅ A := by
  letI := IsSubterminal.isIso_diag hA
  apply (asIso (diag A)).symm

variable (C)

/-- The (full sub)category of subterminal objects.
TODO: If `C` is the category of sheaves on a topological space `X`, this category is equivalent
to the lattice of open subsets of `X`. More generally, if `C` is a topos, this is the lattice of
"external truth values".
-/
/-
**CategoryTheory.Subterminals** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory`。
形式化陈述：Subterminals (C : Type u₁) [Category.{v₁} C]
参数：C : Type u₁。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The (full sub)category of subterminal objects.
TODO: If `C` is the category of sheaves on a topological space `X`, this categor
y is equivalent
to the lattice of open subsets of `X`. More generally, if `C` is a topos, this i
s the lattice of
"external truth values".
-/
def Subterminals (C : Type u₁) [Category.{v₁} C] :=
  ObjectProperty.FullSubcategory fun A : C => IsSubterminal A
/-
**CategoryTheory.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (C : Type u₁) [Category.{v₁} C] : Category (Subterminals C) :=
  ObjectProperty.FullSubcategory.category _
/-
**CategoryTheory.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [HasTerminal C] : Inhabited (Subterminals C) :=
  ⟨⟨⊤_ C, isSubterminal_of_terminal⟩⟩

/-- The inclusion of the subterminal objects into the original category. -/
@[simps!]
/-
**CategoryTheory.subterminalInclusion** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory`
。
形式化陈述：subterminalInclusion : Subterminals C ⥤ C
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The inclusion of the subterminal objects into the original category.
-/
def subterminalInclusion : Subterminals C ⥤ C :=
  ObjectProperty.ι _
/-
**CategoryTheory.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (C : Type u₁) [Category.{v₁} C] : (subterminalInclusion C).Full :=
  ObjectProperty.full_ι _
/-
**CategoryTheory.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (C : Type u₁) [Category.{v₁} C] : (subterminalInclusion C).Faithful :=
  ObjectProperty.faithful_ι _
/-
**CategoryTheory.subterminals_thin** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory`。
形式化陈述：subterminals_thin (X Y : Subterminals C) : Subsingleton (X ⟶ Y) where allE
q _ _
参数：X Y : Subterminals C。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.ObjectProperty.hom_ext`：hom_ext {X Y : P.FullSubcategory}
 {f g : X ⟶ Y} (h : f.hom = g.hom) : f = g
· 使用定理 `CategoryTheory.ObjectProperty.FullSubcategory.property`：∀ {C : Type u} [
inst : CategoryTheory.Category.{v, u} C] {P : CategoryTheory.ObjectProperty C}  
 (self : P.FullSubcategory), P self.obj
-/
instance subterminals_thin (X Y : Subterminals C) : Subsingleton (X ⟶ Y) where
  allEq _ _ := ObjectProperty.hom_ext _ (Y.2 _ _)

/--
The category of subterminal objects is equivalent to the category of monomorphisms to the terminal
object (which is in turn equivalent to the subobjects of the terminal object).
-/
@[simps]
/-
**CategoryTheory.subterminalsEquivMonoOverTerminal** 是 Mathlib 中的一个定义，位于命名空间 `Ca
tegoryTheory`。
形式化陈述：subterminalsEquivMonoOverTerminal [HasTerminal C] : Subterminals C ≌ MonoO
ver (⊤_ C) where functor
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The category of subterminal objects is equivalent to the category of monomorphis
ms to the terminal
object (which is in turn equivalent to the subobjects of the terminal object).
-/
def subterminalsEquivMonoOverTerminal [HasTerminal C] : Subterminals C ≌ MonoOver (⊤_ C) where
  functor :=
    { obj := fun X => ⟨Over.mk (terminal.from X.1), X.2.mono_terminal_from⟩
      map := fun f => MonoOver.homMk f.hom (by ext1 ⟨⟨⟩⟩) }
  inverse :=
    { obj := fun X =>
        ⟨X.obj.left, fun Z f g => by
          rw [← cancel_mono X.arrow]
          subsingleton⟩
      map := fun f => ObjectProperty.homMk f.hom.1 }
  unitIso := NatIso.ofComponents (fun X => Iso.refl X) (by subsingleton)
  counitIso := NatIso.ofComponents (fun X => MonoOver.isoMk (Iso.refl _)) (by subsingleton)
  functor_unitIso_comp := by subsingleton

@[simp]
/-
**CategoryTheory.subterminals_to_monoOver_terminal_comp_forget** 是 Mathlib 中的一个定
理，位于命名空间 `CategoryTheory`。
形式化陈述：subterminals_to_monoOver_terminal_comp_forget [HasTerminal C] : (subtermin
alsEquivMonoOverTerminal C).functor ⋙ MonoOver.forget _ ⋙ Over.forget _ = subter
minalInclusion C
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem subterminals_to_monoOver_terminal_comp_forget [HasTerminal C] :
    (subterminalsEquivMonoOverTerminal C).functor ⋙ MonoOver.forget _ ⋙ Over.forget _ =
      subterminalInclusion C :=
  rfl

@[simp]
/-
**CategoryTheory.monoOver_terminal_to_subterminals_comp** 是 Mathlib 中的一个定理，位于命名空
间 `CategoryTheory`。
形式化陈述：monoOver_terminal_to_subterminals_comp [HasTerminal C] : (subterminalsEqui
vMonoOverTerminal C).inverse ⋙ subterminalInclusion C = MonoOver.forget _ ⋙ Over
.forget _
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem monoOver_terminal_to_subterminals_comp [HasTerminal C] :
    (subterminalsEquivMonoOverTerminal C).inverse ⋙ subterminalInclusion C =
      MonoOver.forget _ ⋙ Over.forget _ :=
  rfl

end CategoryTheory

