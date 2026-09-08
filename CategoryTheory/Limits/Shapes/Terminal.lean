/-
Copyright (c) 2019 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison, Bhavik Mehta
-/
module

public import Mathlib.CategoryTheory.Limits.Shapes.IsTerminal
public import Mathlib.CategoryTheory.Limits.HasLimits

/-!
# Initial and terminal objects in a category.

## References
* [Stacks: Initial and final objects](https://stacks.math.columbia.edu/tag/002B)
-/

@[expose] public section


noncomputable section

universe w w' v v₁ v₂ u u₁ u₂

open CategoryTheory

namespace CategoryTheory.Limits

variable {C : Type u₁} [Category.{v₁} C]

variable (C)

/-- A category has a terminal object if it has a limit over the empty diagram.
Use `hasTerminal_of_unique` to construct instances.
-/
/-
**CategoryTheory.Limits.HasTerminal** 是 Mathlib 中的一个缩写定义，位于命名空间 `CategoryTheory.
Limits`。
形式化陈述：HasTerminal
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A category has a terminal object if it has a limit over the empty diagram.
Use `hasTerminal_of_unique` to construct instances.
-/
abbrev HasTerminal :=
  HasLimitsOfShape (Discrete.{0} PEmpty) C

/-- A category has an initial object if it has a colimit over the empty diagram.
Use `hasInitial_of_unique` to construct instances.
-/
/-
**CategoryTheory.Limits.HasInitial** 是 Mathlib 中的一个缩写定义，位于命名空间 `CategoryTheory.L
imits`。
形式化陈述：HasInitial
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A category has an initial object if it has a colimit over the empty diagram.
Use `hasInitial_of_unique` to construct instances.
-/
abbrev HasInitial :=
  HasColimitsOfShape (Discrete.{0} PEmpty) C

section Univ

variable (X : C) {F₁ : Discrete.{w} PEmpty ⥤ C} {F₂ : Discrete.{w'} PEmpty ⥤ C}

/-
**CategoryTheory.Limits.hasTerminalChangeDiagram** 是 Mathlib 中的一个定理，位于命名空间 `Cate
goryTheory.Limits`。
形式化陈述：hasTerminalChangeDiagram (h : HasLimit F₁) : HasLimit F₂
参数：h : HasLimit F₁。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Aesop.BuiltinRules.pEmpty_false`：∀ (h : PEmpty.{u_1}), False
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用定理 `CategoryTheory.instIsEmptyDiscrete`：∀ (α : Type u_1) [IsEmpty α], IsEmpt
y (CategoryTheory.Discrete α)
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
theorem hasTerminalChangeDiagram (h : HasLimit F₁) : HasLimit F₂ :=
  ⟨⟨⟨⟨limit F₁, by cat_disch, by simp⟩,
    isLimitChangeEmptyCone C (limit.isLimit F₁) _ (eqToIso rfl)⟩⟩⟩
/-
**CategoryTheory.Limits.hasTerminalChangeUniverse** 是 Mathlib 中的一个定理，位于命名空间 `Cat
egoryTheory.Limits`。
形式化陈述：hasTerminalChangeUniverse [h : HasLimitsOfShape (Discrete.{w} PEmpty) C] :
 HasLimitsOfShape (Discrete.{w'} PEmpty) C where has_limit _
参数：Discrete.{w} PEmpty。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.hasTerminalChangeDiagram`：hasTerminalChangeDiagram
 (h : HasLimit F₁) : HasLimit F₂
· 使用定理 `CategoryTheory.Limits.HasLimitsOfShape.has_limit`：∀ {J : Type u₁} {inst 
: CategoryTheory.Category.{v₁, u₁} J} {C : Type u} {inst_1 : CategoryTheory.Cate
gory.{v, u} C}   [self : CategoryTheor…
-/
theorem hasTerminalChangeUniverse [h : HasLimitsOfShape (Discrete.{w} PEmpty) C] :
    HasLimitsOfShape (Discrete.{w'} PEmpty) C where
  has_limit _ := hasTerminalChangeDiagram C (h.1 (Functor.empty C))
/-
**CategoryTheory.Limits.hasInitialChangeDiagram** 是 Mathlib 中的一个定理，位于命名空间 `Categ
oryTheory.Limits`。
形式化陈述：hasInitialChangeDiagram (h : HasColimit F₁) : HasColimit F₂
参数：h : HasColimit F₁。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Aesop.BuiltinRules.pEmpty_false`：∀ (h : PEmpty.{u_1}), False
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `CategoryTheory.instIsEmptyDiscrete`：∀ (α : Type u_1) [IsEmpty α], IsEmpt
y (CategoryTheory.Discrete α)
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
theorem hasInitialChangeDiagram (h : HasColimit F₁) : HasColimit F₂ :=
  ⟨⟨⟨⟨colimit F₁, by cat_disch, by simp⟩,
    isColimitChangeEmptyCocone C (colimit.isColimit F₁) _ (eqToIso rfl)⟩⟩⟩
/-
**CategoryTheory.Limits.hasInitialChangeUniverse** 是 Mathlib 中的一个定理，位于命名空间 `Cate
goryTheory.Limits`。
形式化陈述：hasInitialChangeUniverse [h : HasColimitsOfShape (Discrete.{w} PEmpty) C] 
: HasColimitsOfShape (Discrete.{w'} PEmpty) C where has_colimit _
参数：Discrete.{w} PEmpty。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.hasInitialChangeDiagram`：hasInitialChangeDiagram (
h : HasColimit F₁) : HasColimit F₂
· 使用定理 `CategoryTheory.Limits.HasColimitsOfShape.has_colimit`：∀ {J : Type u₁} {i
nst : CategoryTheory.Category.{v₁, u₁} J} {C : Type u} {inst_1 : CategoryTheory.
Category.{v, u} C}   [self : CategoryTheor…
-/
theorem hasInitialChangeUniverse [h : HasColimitsOfShape (Discrete.{w} PEmpty) C] :
    HasColimitsOfShape (Discrete.{w'} PEmpty) C where
  has_colimit _ := hasInitialChangeDiagram C (h.1 (Functor.empty C))

end Univ

/-- An arbitrary choice of terminal object, if one exists.
You can use the notation `⊤_ C`.
This object is characterized by having a unique morphism from any object.
-/
/-
**CategoryTheory.Limits.terminal** 是 Mathlib 中的一个缩写定义，位于命名空间 `CategoryTheory.Lim
its`。
形式化陈述：terminal [HasTerminal C] : C
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An arbitrary choice of terminal object, if one exists.
You can use the notation `⊤_ C`.
This object is characterized by having a unique morphism from any object.
-/
abbrev terminal [HasTerminal C] : C :=
  limit (Functor.empty.{0} C)

/-- An arbitrary choice of initial object, if one exists.
You can use the notation `⊥_ C`.
This object is characterized by having a unique morphism to any object.
-/
/-
**CategoryTheory.Limits.initial** 是 Mathlib 中的一个缩写定义，位于命名空间 `CategoryTheory.Limi
ts`。
形式化陈述：initial [HasInitial C] : C
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An arbitrary choice of initial object, if one exists.
You can use the notation `⊥_ C`.
This object is characterized by having a unique morphism to any object.
-/
abbrev initial [HasInitial C] : C :=
  colimit (Functor.empty.{0} C)

/-- Notation for the terminal object in `C` -/
notation "⊤_ " C:20 => terminal C

/-- Notation for the initial object in `C` -/
notation "⊥_ " C:20 => initial C

section

variable {C}

/-- We can more explicitly show that a category has a terminal object by specifying the object,
and showing there is a unique morphism to it from any other object. -/
/-
**CategoryTheory.Limits.hasTerminal_of_unique** 是 Mathlib 中的一个定理，位于命名空间 `Categor
yTheory.Limits`。
形式化陈述：hasTerminal_of_unique (X : C) [forall Y, Nonempty (Y ⟶ X)] [forall Y, Subs
ingleton (Y ⟶ X)] : HasTerminal C where has_limit F
参数：X : C；Y ⟶ X；Y ⟶ X。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.HasLimit.mk`：∀ {J : Type u₁} [inst : CategoryTheor
y.Category.{v₁, u₁} J] {C : Type u} [inst_1 : CategoryTheory.Category.{v, u} C] 
  {F : CategoryTheory.F…
· 使用定理 `Aesop.BuiltinRules.pEmpty_false`：∀ (h : PEmpty.{u_1}), False
· 使用定理 `Subsingleton.elim`：∀ {α : Sort u} [h : Subsingleton α] (a b : α), a = b

--- 原说明 ---
We can more explicitly show that a category has a terminal object by specifying 
the object,
and showing there is a unique morphism to it from any other object.
-/
theorem hasTerminal_of_unique (X : C) [∀ Y, Nonempty (Y ⟶ X)] [∀ Y, Subsingleton (Y ⟶ X)] :
    HasTerminal C where
  has_limit F := .mk ⟨_, (isTerminalEquivUnique F X).invFun fun _ ↦
    ⟨Classical.inhabited_of_nonempty', (Subsingleton.elim · _)⟩⟩
/-
**CategoryTheory.Limits.IsTerminal.hasTerminal** 是 Mathlib 中的一个定理，位于命名空间 `Catego
ryTheory.Limits.IsTerminal`。
形式化陈述：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {X : C} (h : C
ategoryTheory.Limits.IsTerminal X),   CategoryTheory.Limits.HasTerminal C
参数：h : CategoryTheory.Limits.IsTerminal X。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.HasLimit.mk`：∀ {J : Type u₁} [inst : CategoryTheor
y.Category.{v₁, u₁} J] {C : Type u} [inst_1 : CategoryTheory.Category.{v, u} C] 
  {F : CategoryTheory.F…
· 使用定理 `Aesop.BuiltinRules.pEmpty_false`：∀ (h : PEmpty.{u_1}), False
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用定理 `CategoryTheory.instIsEmptyDiscrete`：∀ (α : Type u_1) [IsEmpty α], IsEmpt
y (CategoryTheory.Discrete α)
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
theorem IsTerminal.hasTerminal {X : C} (h : IsTerminal X) : HasTerminal C :=
  { has_limit := fun F => HasLimit.mk ⟨⟨X, by cat_disch, by simp⟩,
    isLimitChangeEmptyCone _ h _ (Iso.refl _)⟩ }

/-- We can more explicitly show that a category has an initial object by specifying the object,
and showing there is a unique morphism from it to any other object. -/
/-
**CategoryTheory.Limits.hasInitial_of_unique** 是 Mathlib 中的一个定理，位于命名空间 `Category
Theory.Limits`。
形式化陈述：hasInitial_of_unique (X : C) [forall Y, Nonempty (X ⟶ Y)] [forall Y, Subsi
ngleton (X ⟶ Y)] : HasInitial C where has_colimit F
参数：X : C；X ⟶ Y；X ⟶ Y。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.HasColimit.mk`：∀ {J : Type u₁} [inst : CategoryThe
ory.Category.{v₁, u₁} J] {C : Type u} [inst_1 : CategoryTheory.Category.{v, u} C
]   {F : CategoryTheory.F…
· 使用定理 `Aesop.BuiltinRules.pEmpty_false`：∀ (h : PEmpty.{u_1}), False
· 使用定理 `Subsingleton.elim`：∀ {α : Sort u} [h : Subsingleton α] (a b : α), a = b

--- 原说明 ---
We can more explicitly show that a category has an initial object by specifying 
the object,
and showing there is a unique morphism from it to any other object.
-/
theorem hasInitial_of_unique (X : C) [∀ Y, Nonempty (X ⟶ Y)] [∀ Y, Subsingleton (X ⟶ Y)] :
    HasInitial C where
  has_colimit F := .mk ⟨_, (isInitialEquivUnique F X).invFun fun _ ↦
    ⟨Classical.inhabited_of_nonempty', (Subsingleton.elim · _)⟩⟩
/-
**CategoryTheory.Limits.IsInitial.hasInitial** 是 Mathlib 中的一个定理，位于命名空间 `Category
Theory.Limits.IsInitial`。
形式化陈述：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {X : C} (h : C
ategoryTheory.Limits.IsInitial X),   CategoryTheory.Limits.HasInitial C
参数：h : CategoryTheory.Limits.IsInitial X。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.HasColimit.mk`：∀ {J : Type u₁} [inst : CategoryThe
ory.Category.{v₁, u₁} J] {C : Type u} [inst_1 : CategoryTheory.Category.{v, u} C
]   {F : CategoryTheory.F…
· 使用定理 `Aesop.BuiltinRules.pEmpty_false`：∀ (h : PEmpty.{u_1}), False
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `CategoryTheory.instIsEmptyDiscrete`：∀ (α : Type u_1) [IsEmpty α], IsEmpt
y (CategoryTheory.Discrete α)
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
theorem IsInitial.hasInitial {X : C} (h : IsInitial X) : HasInitial C where
  has_colimit F :=
    HasColimit.mk ⟨⟨X, by cat_disch, by simp⟩, isColimitChangeEmptyCocone _ h _ (Iso.refl _)⟩

/-- The map from an object to the terminal object. -/
/-
**CategoryTheory.Limits.terminal.from** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.
Limits.terminal`。
形式化陈述：{C : Type u₁} →   [inst : CategoryTheory.Category.{v₁, u₁} C] → [inst_1 : 
CategoryTheory.Limits.HasTerminal C] → (P : C) → P ⟶ ⊤_ C
参数：P : C。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The map from an object to the terminal object.
-/
abbrev terminal.from [HasTerminal C] (P : C) : P ⟶ ⊤_ C :=
  limit.lift (Functor.empty C) (asEmptyCone P)

/-- The map to an object from the initial object. -/
/-
**CategoryTheory.Limits.initial.to** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Lim
its.initial`。
形式化陈述：{C : Type u₁} →   [inst : CategoryTheory.Category.{v₁, u₁} C] → [inst_1 : 
CategoryTheory.Limits.HasInitial C] → (P : C) → ⊥_ C ⟶ P
参数：P : C。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The map to an object from the initial object.
-/
abbrev initial.to [HasInitial C] (P : C) : ⊥_ C ⟶ P :=
  colimit.desc (Functor.empty C) (asEmptyCocone P)

/-- A terminal object is terminal. -/
/-
**CategoryTheory.Limits.terminalIsTerminal** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTh
eory.Limits`。
形式化陈述：terminalIsTerminal [HasTerminal C] : IsTerminal (⊤_ C) where lift _
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A terminal object is terminal.
-/
def terminalIsTerminal [HasTerminal C] : IsTerminal (⊤_ C) where
  lift _ := terminal.from _

/-- An initial object is initial. -/
/-
**CategoryTheory.Limits.initialIsInitial** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheo
ry.Limits`。
形式化陈述：initialIsInitial [HasInitial C] : IsInitial (⊥_ C) where desc _
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An initial object is initial.
-/
def initialIsInitial [HasInitial C] : IsInitial (⊥_ C) where
  desc _ := initial.to _
/-
**CategoryTheory.Limits.uniqueToTerminal** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheo
ry.Limits`。
形式化陈述：uniqueToTerminal [HasTerminal C] (P : C) : Unique (P ⟶ ⊤_ C)
参数：P : C。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Aesop.BuiltinRules.pEmpty_false`：∀ (h : PEmpty.{u_1}), False
-/
instance uniqueToTerminal [HasTerminal C] (P : C) : Unique (P ⟶ ⊤_ C) :=
  isTerminalEquivUnique _ (⊤_ C) terminalIsTerminal P
/-
**CategoryTheory.Limits.uniqueFromInitial** 是 Mathlib 中的一个实例，位于命名空间 `CategoryThe
ory.Limits`。
形式化陈述：uniqueFromInitial [HasInitial C] (P : C) : Unique (⊥_ C ⟶ P)
参数：P : C。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Aesop.BuiltinRules.pEmpty_false`：∀ (h : PEmpty.{u_1}), False
-/
instance uniqueFromInitial [HasInitial C] (P : C) : Unique (⊥_ C ⟶ P) :=
  isInitialEquivUnique _ (⊥_ C) initialIsInitial P
/-
**CategoryTheory.Limits.terminal.hom_ext** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheo
ry.Limits.terminal`。
形式化陈述：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] [inst_1 : Cate
goryTheory.Limits.HasTerminal C] {P : C}   (f g : P ⟶ ⊤_ C), f = g
参数：f g : P ⟶ ⊤_ C。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.limit.hom_ext`：∀ {J : Type u₁} [inst : CategoryThe
ory.Category.{v₁, u₁} J] {C : Type u} [inst_1 : CategoryTheory.Category.{v, u} C
]   {F : CategoryTheory.F…
-/
@[ext] theorem terminal.hom_ext [HasTerminal C] {P : C} (f g : P ⟶ ⊤_ C) : f = g := by ext ⟨⟨⟩⟩
/-
**CategoryTheory.Limits.initial.hom_ext** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheor
y.Limits.initial`。
形式化陈述：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] [inst_1 : Cate
goryTheory.Limits.HasInitial C] {P : C}   (f g : ⊥_ C ⟶ P), f = g
参数：f g : ⊥_ C ⟶ P。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.colimit.hom_ext`：∀ {J : Type u₁} [inst : CategoryT
heory.Category.{v₁, u₁} J] {C : Type u} [inst_1 : CategoryTheory.Category.{v, u}
 C]   {F : CategoryTheory.F…
-/
@[ext] theorem initial.hom_ext [HasInitial C] {P : C} (f g : ⊥_ C ⟶ P) : f = g := by ext ⟨⟨⟩⟩

@[reassoc (attr := simp)]
/-
**CategoryTheory.Limits.terminal.comp_from** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTh
eory.Limits.terminal`。
形式化陈述：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] [inst_1 : Cate
goryTheory.Limits.HasTerminal C] {P Q : C}   (f : P ⟶ Q),   CategoryTheory.Categ
oryStruct.comp f (CategoryTheory.Limits.terminal.from Q) = CategoryTheory.Limits
.terminal.from P
参数：f : P ⟶ Q；CategoryTheory.Limits.terminal.from Q。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Unique.instSubsingleton`：∀ {α : Sort u_1} [Unique α], Subsingleton α
-/
theorem terminal.comp_from [HasTerminal C] {P Q : C} (f : P ⟶ Q) :
    f ≫ terminal.from Q = terminal.from P := by
  simp [eq_iff_true_of_subsingleton]

-- `initial.to_comp_assoc` does not need the `simp` attribute.
@[simp, reassoc]
/-
**CategoryTheory.Limits.initial.to_comp** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheor
y.Limits.initial`。
形式化陈述：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] [inst_1 : Cate
goryTheory.Limits.HasInitial C] {P Q : C}   (f : P ⟶ Q),   CategoryTheory.Catego
ryStruct.comp (CategoryTheory.Limits.initial.to P) f = CategoryTheory.Limits.ini
tial.to Q
参数：f : P ⟶ Q；CategoryTheory.Limits.initial.to P。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Unique.instSubsingleton`：∀ {α : Sort u_1} [Unique α], Subsingleton α
-/
theorem initial.to_comp [HasInitial C] {P Q : C} (f : P ⟶ Q) : initial.to P ≫ f = initial.to Q := by
  simp [eq_iff_true_of_subsingleton]

/-- The (unique) isomorphism between the chosen initial object and any other initial object. -/
@[simps!]
/-
**CategoryTheory.Limits.initialIsoIsInitial** 是 Mathlib 中的一个定义，位于命名空间 `CategoryT
heory.Limits`。
形式化陈述：initialIsoIsInitial [HasInitial C] {P : C} (t : IsInitial P) : ⊥_ C ≅ P
参数：t : IsInitial P。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The (unique) isomorphism between the chosen initial object and any other initial
 object.
-/
def initialIsoIsInitial [HasInitial C] {P : C} (t : IsInitial P) : ⊥_ C ≅ P :=
  initialIsInitial.uniqueUpToIso t

/-- The (unique) isomorphism between the chosen terminal object and any other terminal object. -/
@[simps!]
/-
**CategoryTheory.Limits.terminalIsoIsTerminal** 是 Mathlib 中的一个定义，位于命名空间 `Categor
yTheory.Limits`。
形式化陈述：terminalIsoIsTerminal [HasTerminal C] {P : C} (t : IsTerminal P) : ⊤_ C ≅ 
P
参数：t : IsTerminal P。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The (unique) isomorphism between the chosen terminal object and any other termin
al object.
-/
def terminalIsoIsTerminal [HasTerminal C] {P : C} (t : IsTerminal P) : ⊤_ C ≅ P :=
  terminalIsTerminal.uniqueUpToIso t

/-- Any morphism from a terminal object is split mono. -/
/-
**CategoryTheory.Limits.terminal.isSplitMono_from** 是 Mathlib 中的一个定理，位于命名空间 `Cat
egoryTheory.Limits.terminal`。
形式化陈述：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {Y : C} [inst_
1 : CategoryTheory.Limits.HasTerminal C]   (f : ⊤_ C ⟶ Y), CategoryTheory.IsSpli
tMono f
参数：f : ⊤_ C ⟶ Y。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.IsTerminal.isSplitMono_from`：∀ {C : Type u₁} [inst
 : CategoryTheory.Category.{v₁, u₁} C] {X Y : C} (t : CategoryTheory.Limits.IsTe
rminal X)   (f : X ⟶ Y), CategoryTheory…

--- 原说明 ---
Any morphism from a terminal object is split mono.
-/
instance terminal.isSplitMono_from {Y : C} [HasTerminal C] (f : ⊤_ C ⟶ Y) : IsSplitMono f :=
  IsTerminal.isSplitMono_from terminalIsTerminal _

/-- Any morphism to an initial object is split epi. -/
/-
**CategoryTheory.Limits.initial.isSplitEpi_to** 是 Mathlib 中的一个定理，位于命名空间 `Categor
yTheory.Limits.initial`。
形式化陈述：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {Y : C} [inst_
1 : CategoryTheory.Limits.HasInitial C]   (f : Y ⟶ ⊥_ C), CategoryTheory.IsSplit
Epi f
参数：f : Y ⟶ ⊥_ C。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.IsInitial.isSplitEpi_to`：∀ {C : Type u₁} [inst : C
ategoryTheory.Category.{v₁, u₁} C] {X Y : C} (t : CategoryTheory.Limits.IsInitia
l X)   (f : Y ⟶ X), CategoryTheory.…

--- 原说明 ---
Any morphism to an initial object is split epi.
-/
instance initial.isSplitEpi_to {Y : C} [HasInitial C] (f : Y ⟶ ⊥_ C) : IsSplitEpi f :=
  IsInitial.isSplitEpi_to initialIsInitial _
/-
**CategoryTheory.Limits.hasInitial_op_of_hasTerminal** 是 Mathlib 中的一个实例，位于命名空间 `
CategoryTheory.Limits`。
形式化陈述：hasInitial_op_of_hasTerminal [HasTerminal C] : HasInitial Cᵒᵖ
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.IsInitial.hasInitial`：∀ {C : Type u₁} [inst : Cate
goryTheory.Category.{v₁, u₁} C] {X : C} (h : CategoryTheory.Limits.IsInitial X),
   CategoryTheory.Limits.HasInit…
-/
instance hasInitial_op_of_hasTerminal [HasTerminal C] : HasInitial Cᵒᵖ :=
  (initialOpOfTerminal terminalIsTerminal).hasInitial
/-
**CategoryTheory.Limits.hasTerminal_op_of_hasInitial** 是 Mathlib 中的一个实例，位于命名空间 `
CategoryTheory.Limits`。
形式化陈述：hasTerminal_op_of_hasInitial [HasInitial C] : HasTerminal Cᵒᵖ
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.IsTerminal.hasTerminal`：∀ {C : Type u₁} [inst : Ca
tegoryTheory.Category.{v₁, u₁} C] {X : C} (h : CategoryTheory.Limits.IsTerminal 
X),   CategoryTheory.Limits.HasTer…
-/
instance hasTerminal_op_of_hasInitial [HasInitial C] : HasTerminal Cᵒᵖ :=
  (terminalOpOfInitial initialIsInitial).hasTerminal
/-
**CategoryTheory.Limits.hasTerminal_of_hasInitial_op** 是 Mathlib 中的一个定理，位于命名空间 `
CategoryTheory.Limits`。
形式化陈述：hasTerminal_of_hasInitial_op [HasInitial Cᵒᵖ] : HasTerminal C
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.IsTerminal.hasTerminal`：∀ {C : Type u₁} [inst : Ca
tegoryTheory.Category.{v₁, u₁} C] {X : C} (h : CategoryTheory.Limits.IsTerminal 
X),   CategoryTheory.Limits.HasTer…
-/
theorem hasTerminal_of_hasInitial_op [HasInitial Cᵒᵖ] : HasTerminal C :=
  (terminalUnopOfInitial initialIsInitial).hasTerminal
/-
**CategoryTheory.Limits.hasInitial_of_hasTerminal_op** 是 Mathlib 中的一个定理，位于命名空间 `
CategoryTheory.Limits`。
形式化陈述：hasInitial_of_hasTerminal_op [HasTerminal Cᵒᵖ] : HasInitial C
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.IsInitial.hasInitial`：∀ {C : Type u₁} [inst : Cate
goryTheory.Category.{v₁, u₁} C] {X : C} (h : CategoryTheory.Limits.IsInitial X),
   CategoryTheory.Limits.HasInit…
-/
theorem hasInitial_of_hasTerminal_op [HasTerminal Cᵒᵖ] : HasInitial C :=
  (initialUnopOfTerminal terminalIsTerminal).hasInitial
/-
**CategoryTheory.Limits.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Limits`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {J : Type*} [Category* J] {C : Type*} [Category* C] [HasTerminal C] :
    HasLimit ((CategoryTheory.Functor.const J).obj (⊤_ C)) :=
  HasLimit.mk
    { cone :=
        { pt := ⊤_ C
          π := { app := fun _ => terminal.from _ } }
      isLimit := { lift := fun _ => terminal.from _ } }

/-- The limit of the constant `⊤_ C` functor is `⊤_ C`. -/
@[simps hom]
/-
**CategoryTheory.Limits.limitConstTerminal** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTh
eory.Limits`。
形式化陈述：limitConstTerminal {J : Type*} [Category* J] {C : Type*} [Category* C] [Ha
sTerminal C] : limit ((CategoryTheory.Functor.const J).obj (⊤_ C)) ≅ ⊤_ C where 
hom
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.instHasLimitObjFunctorConstTerminal`：∀ {J : Type u
_1} [inst : CategoryTheory.Category.{v_1, u_1} J] {C : Type u_2}   [inst_1 : Cat
egoryTheory.Category.{v_2, u_2} C] [inst_2 : Ca…

--- 原说明 ---
The limit of the constant `⊤_ C` functor is `⊤_ C`.
-/
def limitConstTerminal {J : Type*} [Category* J] {C : Type*} [Category* C] [HasTerminal C] :
    limit ((CategoryTheory.Functor.const J).obj (⊤_ C)) ≅ ⊤_ C where
  hom := terminal.from _
  inv :=
    limit.lift ((CategoryTheory.Functor.const J).obj (⊤_ C))
      { pt := ⊤_ C
        π := { app := fun _ => terminal.from _ } }

@[reassoc (attr := simp)]
/-
**CategoryTheory.Limits.limitConstTerminal_inv_** 是 Mathlib 中的一个定理，位于命名空间 `Categ
oryTheory.Limits`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem limitConstTerminal_inv_π {J : Type*} [Category* J] {C : Type*} [Category* C] [HasTerminal C]
    {j : J} :
    limitConstTerminal.inv ≫ limit.π ((CategoryTheory.Functor.const J).obj (⊤_ C)) j =
      terminal.from _ := by cat_disch
/-
**CategoryTheory.Limits.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Limits`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {J : Type*} [Category* J] {C : Type*} [Category* C] [HasInitial C] :
    HasColimit ((CategoryTheory.Functor.const J).obj (⊥_ C)) :=
  HasColimit.mk
    { cocone :=
        { pt := ⊥_ C
          ι := { app := fun _ => initial.to _ } }
      isColimit := { desc := fun _ => initial.to _ } }

/-- The colimit of the constant `⊥_ C` functor is `⊥_ C`. -/
@[simps inv]
/-
**CategoryTheory.Limits.colimitConstInitial** 是 Mathlib 中的一个定义，位于命名空间 `CategoryT
heory.Limits`。
形式化陈述：colimitConstInitial {J : Type*} [Category* J] {C : Type*} [Category* C] [H
asInitial C] : colimit ((CategoryTheory.Functor.const J).obj (⊥_ C)) ≅ ⊥_ C wher
e hom
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.instHasColimitObjFunctorConstInitial`：∀ {J : Type 
u_1} [inst : CategoryTheory.Category.{v_1, u_1} J] {C : Type u_2}   [inst_1 : Ca
tegoryTheory.Category.{v_2, u_2} C] [inst_2 : Ca…

--- 原说明 ---
The colimit of the constant `⊥_ C` functor is `⊥_ C`.
-/
def colimitConstInitial {J : Type*} [Category* J] {C : Type*} [Category* C] [HasInitial C] :
    colimit ((CategoryTheory.Functor.const J).obj (⊥_ C)) ≅ ⊥_ C where
  hom :=
    colimit.desc ((CategoryTheory.Functor.const J).obj (⊥_ C))
      { pt := ⊥_ C
        ι := { app := fun _ => initial.to _ } }
  inv := initial.to _

@[reassoc (attr := simp)]
/-
**CategoryTheory.Limits.** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.Limits`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem ι_colimitConstInitial_hom {J : Type*} [Category* J] {C : Type*} [Category* C] [HasInitial C]
    {j : J} :
    colimit.ι ((CategoryTheory.Functor.const J).obj (⊥_ C)) j ≫ colimitConstInitial.hom =
      initial.to _ := by cat_disch
/-
**CategoryTheory.Limits.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Limits`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 100) initial.mono_from [HasInitial C] [InitialMonoClass C] (X : C)
    (f : ⊥_ C ⟶ X) : Mono f :=
  initialIsInitial.mono_from f

/-- To show a category is an `InitialMonoClass` it suffices to show every morphism out of the
initial object is a monomorphism. -/
/-
**CategoryTheory.Limits.InitialMonoClass.of_initial** 是 Mathlib 中的一个定理，位于命名空间 `C
ategoryTheory.Limits.InitialMonoClass`。
形式化陈述：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] [inst_1 : Cate
goryTheory.Limits.HasInitial C],   (∀ (X : C), CategoryTheory.Mono (CategoryTheo
ry.Limits.initial.to X)) → CategoryTheory.Limits.InitialMonoClass C
参数：∀ (X : C), CategoryTheory.Mono (CategoryTheory.Limits.initial.to X)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.InitialMonoClass.of_isInitial`：∀ {C : Type u₁} [in
st : CategoryTheory.Category.{v₁, u₁} C] {I : C} (hI : CategoryTheory.Limits.IsI
nitial I),   (∀ (X : C), CategoryTheory.M…

--- 原说明 ---
To show a category is an `InitialMonoClass` it suffices to show every morphism o
ut of the
initial object is a monomorphism.
-/
theorem InitialMonoClass.of_initial [HasInitial C] (h : ∀ X : C, Mono (initial.to X)) :
    InitialMonoClass C :=
  InitialMonoClass.of_isInitial initialIsInitial h

/-- To show a category is an `InitialMonoClass` it suffices to show the unique morphism from the
initial object to a terminal object is a monomorphism. -/
/-
**CategoryTheory.Limits.InitialMonoClass.of_terminal** 是 Mathlib 中的一个定理，位于命名空间 `
CategoryTheory.Limits.InitialMonoClass`。
形式化陈述：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] [inst_1 : Cate
goryTheory.Limits.HasInitial C]   [inst_2 : CategoryTheory.Limits.HasTerminal C]
,   CategoryTheory.Mono (CategoryTheory.Limits.initial.to (⊤_ C)) → CategoryTheo
ry.Limits.InitialMonoClass C
参数：CategoryTheory.Limits.initial.to (⊤_ C)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.InitialMonoClass.of_isTerminal`：∀ {C : Type u₁} [i
nst : CategoryTheory.Category.{v₁, u₁} C] {I T : C} (hI : CategoryTheory.Limits.
IsInitial I)   (hT : CategoryTheory.Limits…

--- 原说明 ---
To show a category is an `InitialMonoClass` it suffices to show the unique morph
ism from the
initial object to a terminal object is a monomorphism.
-/
theorem InitialMonoClass.of_terminal [HasInitial C] [HasTerminal C] (h : Mono (initial.to (⊤_ C))) :
    InitialMonoClass C :=
  InitialMonoClass.of_isTerminal initialIsInitial terminalIsTerminal h

section Comparison

variable {D : Type u₂} [Category.{v₂} D] (G : C ⥤ D)

/-- The comparison morphism from the image of a terminal object to the terminal object in the target
category.
This is an isomorphism iff `G` preserves terminal objects, see
`CategoryTheory.Limits.PreservesTerminal.ofIsoComparison`.
-/
/-
**CategoryTheory.Limits.terminalComparison** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTh
eory.Limits`。
形式化陈述：terminalComparison [HasTerminal C] [HasTerminal D] : G.obj (⊤_ C) ⟶ ⊤_ D
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The comparison morphism from the image of a terminal object to the terminal obje
ct in the target
category.
This is an isomorphism iff `G` preserves terminal objects, see
`CategoryTheory.Limits.PreservesTerminal.ofIsoComparison`.
-/
def terminalComparison [HasTerminal C] [HasTerminal D] : G.obj (⊤_ C) ⟶ ⊤_ D :=
  terminal.from _

-- TODO: Show this is an isomorphism if and only if `G` preserves initial objects.
/--
The comparison morphism from the initial object in the target category to the image of the initial
object.
-/
/-
**CategoryTheory.Limits.initialComparison** 是 Mathlib 中的一个定义，位于命名空间 `CategoryThe
ory.Limits`。
形式化陈述：initialComparison [HasInitial C] [HasInitial D] : ⊥_ D ⟶ G.obj (⊥_ C)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The comparison morphism from the initial object in the target category to the im
age of the initial
object.
-/
def initialComparison [HasInitial C] [HasInitial D] : ⊥_ D ⟶ G.obj (⊥_ C) :=
  initial.to _

end Comparison

variable {J : Type u} [Category.{v} J]

/-
**CategoryTheory.Limits.hasLimit_of_domain_hasInitial** 是 Mathlib 中的一个实例，位于命名空间 
`CategoryTheory.Limits`。
形式化陈述：hasLimit_of_domain_hasInitial [HasInitial J] {F : J ⥤ C} : HasLimit F
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.HasLimit.mk`：∀ {J : Type u₁} [inst : CategoryTheor
y.Category.{v₁, u₁} J] {C : Type u} [inst_1 : CategoryTheory.Category.{v, u} C] 
  {F : CategoryTheory.F…
-/
instance hasLimit_of_domain_hasInitial [HasInitial J] {F : J ⥤ C} : HasLimit F :=
  HasLimit.mk { cone := _, isLimit := limitOfDiagramInitial (initialIsInitial) F }

-- This is reducible to allow usage of lemmas about `cone_point_unique_up_to_iso`.
/-- For a functor `F : J ⥤ C`, if `J` has an initial object then the image of it is isomorphic
to the limit of `F`. -/
/-
**CategoryTheory.Limits.limitOfInitial** 是 Mathlib 中的一个缩写定义，位于命名空间 `CategoryTheo
ry.Limits`。
形式化陈述：limitOfInitial (F : J ⥤ C) [HasInitial J] : limit F ≅ F.obj (⊥_ J)
参数：F : J ⥤ C。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
For a functor `F : J ⥤ C`, if `J` has an initial object then the image of it is 
isomorphic
to the limit of `F`.
-/
abbrev limitOfInitial (F : J ⥤ C) [HasInitial J] : limit F ≅ F.obj (⊥_ J) :=
  IsLimit.conePointUniqueUpToIso (limit.isLimit _) (limitOfDiagramInitial initialIsInitial F)
/-
**CategoryTheory.Limits.hasLimit_of_domain_hasTerminal** 是 Mathlib 中的一个实例，位于命名空间
 `CategoryTheory.Limits`。
形式化陈述：hasLimit_of_domain_hasTerminal [HasTerminal J] {F : J ⥤ C} [forall (i j : 
J) (f : i ⟶ j), IsIso (F.map f)] : HasLimit F
参数：i j : J；f : i ⟶ j；F.map f。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.HasLimit.mk`：∀ {J : Type u₁} [inst : CategoryTheor
y.Category.{v₁, u₁} J] {C : Type u} [inst_1 : CategoryTheory.Category.{v, u} C] 
  {F : CategoryTheory.F…
-/
instance hasLimit_of_domain_hasTerminal [HasTerminal J] {F : J ⥤ C}
    [∀ (i j : J) (f : i ⟶ j), IsIso (F.map f)] : HasLimit F :=
  HasLimit.mk { cone := _, isLimit := limitOfDiagramTerminal (terminalIsTerminal) F }

-- This is reducible to allow usage of lemmas about `cone_point_unique_up_to_iso`.
/-- For a functor `F : J ⥤ C`, if `J` has a terminal object and all the morphisms in the diagram
are isomorphisms, then the image of the terminal object is isomorphic to the limit of `F`. -/
/-
**CategoryTheory.Limits.limitOfTerminal** 是 Mathlib 中的一个缩写定义，位于命名空间 `CategoryThe
ory.Limits`。
形式化陈述：limitOfTerminal (F : J ⥤ C) [HasTerminal J] [forall (i j : J) (f : i ⟶ j),
 IsIso (F.map f)] : limit F ≅ F.obj (⊤_ J)
参数：F : J ⥤ C；i j : J；f : i ⟶ j；F.map f。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
For a functor `F : J ⥤ C`, if `J` has a terminal object and all the morphisms in
 the diagram
are isomorphisms, then the image of the terminal object is isomorphic to the lim
it of `F`.
-/
abbrev limitOfTerminal (F : J ⥤ C) [HasTerminal J] [∀ (i j : J) (f : i ⟶ j), IsIso (F.map f)] :
    limit F ≅ F.obj (⊤_ J) :=
  IsLimit.conePointUniqueUpToIso (limit.isLimit _) (limitOfDiagramTerminal terminalIsTerminal F)
/-
**CategoryTheory.Limits.hasColimit_of_domain_hasTerminal** 是 Mathlib 中的一个实例，位于命名
空间 `CategoryTheory.Limits`。
形式化陈述：hasColimit_of_domain_hasTerminal [HasTerminal J] {F : J ⥤ C} : HasColimit 
F
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.HasColimit.mk`：∀ {J : Type u₁} [inst : CategoryThe
ory.Category.{v₁, u₁} J] {C : Type u} [inst_1 : CategoryTheory.Category.{v, u} C
]   {F : CategoryTheory.F…
-/
instance hasColimit_of_domain_hasTerminal [HasTerminal J] {F : J ⥤ C} : HasColimit F :=
  HasColimit.mk { cocone := _, isColimit := colimitOfDiagramTerminal (terminalIsTerminal) F }

-- This is reducible to allow usage of lemmas about `cocone_point_unique_up_to_iso`.
/-- For a functor `F : J ⥤ C`, if `J` has a terminal object then the image of it is isomorphic
to the colimit of `F`. -/
/-
**CategoryTheory.Limits.colimitOfTerminal** 是 Mathlib 中的一个缩写定义，位于命名空间 `CategoryT
heory.Limits`。
形式化陈述：colimitOfTerminal (F : J ⥤ C) [HasTerminal J] : colimit F ≅ F.obj (⊤_ J)
参数：F : J ⥤ C。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
For a functor `F : J ⥤ C`, if `J` has a terminal object then the image of it is 
isomorphic
to the colimit of `F`.
-/
abbrev colimitOfTerminal (F : J ⥤ C) [HasTerminal J] : colimit F ≅ F.obj (⊤_ J) :=
  IsColimit.coconePointUniqueUpToIso (colimit.isColimit _)
    (colimitOfDiagramTerminal terminalIsTerminal F)
/-
**CategoryTheory.Limits.hasColimit_of_domain_hasInitial** 是 Mathlib 中的一个实例，位于命名空
间 `CategoryTheory.Limits`。
形式化陈述：hasColimit_of_domain_hasInitial [HasInitial J] {F : J ⥤ C} [forall (i j : 
J) (f : i ⟶ j), IsIso (F.map f)] : HasColimit F
参数：i j : J；f : i ⟶ j；F.map f。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.HasColimit.mk`：∀ {J : Type u₁} [inst : CategoryThe
ory.Category.{v₁, u₁} J] {C : Type u} [inst_1 : CategoryTheory.Category.{v, u} C
]   {F : CategoryTheory.F…
-/
instance hasColimit_of_domain_hasInitial [HasInitial J] {F : J ⥤ C}
    [∀ (i j : J) (f : i ⟶ j), IsIso (F.map f)] : HasColimit F :=
  HasColimit.mk { cocone := _, isColimit := colimitOfDiagramInitial (initialIsInitial) F }

-- This is reducible to allow usage of lemmas about `cocone_point_unique_up_to_iso`.
/-- For a functor `F : J ⥤ C`, if `J` has an initial object and all the morphisms in the diagram
are isomorphisms, then the image of the initial object is isomorphic to the colimit of `F`. -/
/-
**CategoryTheory.Limits.colimitOfInitial** 是 Mathlib 中的一个缩写定义，位于命名空间 `CategoryTh
eory.Limits`。
形式化陈述：colimitOfInitial (F : J ⥤ C) [HasInitial J] [forall (i j : J) (f : i ⟶ j),
 IsIso (F.map f)] : colimit F ≅ F.obj (⊥_ J)
参数：F : J ⥤ C；i j : J；f : i ⟶ j；F.map f。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
For a functor `F : J ⥤ C`, if `J` has an initial object and all the morphisms in
 the diagram
are isomorphisms, then the image of the initial object is isomorphic to the coli
mit of `F`.
-/
abbrev colimitOfInitial (F : J ⥤ C) [HasInitial J] [∀ (i j : J) (f : i ⟶ j), IsIso (F.map f)] :
    colimit F ≅ F.obj (⊥_ J) :=
  IsColimit.coconePointUniqueUpToIso (colimit.isColimit _)
    (colimitOfDiagramInitial initialIsInitial _)

/-- If `j` is initial in the index category, then the map `limit.π F j` is an isomorphism.
-/
/-
**CategoryTheory.Limits.isIso_** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.Limits`
。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `j` is initial in the index category, then the map `limit.π F j` is an isomor
phism.
-/
theorem isIso_π_of_isInitial {j : J} (I : IsInitial j) (F : J ⥤ C) [HasLimit F] :
    IsIso (limit.π F j) :=
  ⟨⟨limit.lift _ (coneOfDiagramInitial I F), ⟨by ext; simp, by simp⟩⟩⟩
/-
**CategoryTheory.Limits.isIso_** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Limits`
。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance isIso_π_initial [HasInitial J] (F : J ⥤ C) : IsIso (limit.π F (⊥_ J)) :=
  isIso_π_of_isInitial initialIsInitial F
/-
**CategoryTheory.Limits.isIso_** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.Limits`
。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem isIso_π_of_isTerminal {j : J} (I : IsTerminal j) (F : J ⥤ C) [HasLimit F]
    [∀ (i j : J) (f : i ⟶ j), IsIso (F.map f)] : IsIso (limit.π F j) :=
  ⟨⟨limit.lift _ (coneOfDiagramTerminal I F), by ext; simp, by simp⟩⟩
/-
**CategoryTheory.Limits.isIso_** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Limits`
。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance isIso_π_terminal [HasTerminal J] (F : J ⥤ C) [∀ (i j : J) (f : i ⟶ j), IsIso (F.map f)] :
    IsIso (limit.π F (⊤_ J)) :=
  isIso_π_of_isTerminal terminalIsTerminal F

/-- If `j` is terminal in the index category, then the map `colimit.ι F j` is an isomorphism.
-/
/-
**CategoryTheory.Limits.isIso_** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.Limits`
。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `j` is terminal in the index category, then the map `colimit.ι F j` is an iso
morphism.
-/
theorem isIso_ι_of_isTerminal {j : J} (I : IsTerminal j) (F : J ⥤ C) [HasColimit F] :
    IsIso (colimit.ι F j) :=
  ⟨⟨colimit.desc _ (coconeOfDiagramTerminal I F), ⟨by simp, by ext; simp⟩⟩⟩
/-
**CategoryTheory.Limits.isIso_** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Limits`
。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance isIso_ι_terminal [HasTerminal J] (F : J ⥤ C) : IsIso (colimit.ι F (⊤_ J)) :=
  isIso_ι_of_isTerminal terminalIsTerminal F
/-
**CategoryTheory.Limits.isIso_** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.Limits`
。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem isIso_ι_of_isInitial {j : J} (I : IsInitial j) (F : J ⥤ C) [HasColimit F]
    [∀ (i j : J) (f : i ⟶ j), IsIso (F.map f)] : IsIso (colimit.ι F j) :=
  ⟨⟨colimit.desc _ (coconeOfDiagramInitial I F), by
    refine ⟨?_, by ext; simp⟩
    simp only [colimit.ι_desc, coconeOfDiagramInitial_pt, coconeOfDiagramInitial_ι_app,
      Functor.const_obj_obj, IsInitial.to_self]
    grind
  ⟩⟩
/-
**CategoryTheory.Limits.isIso_** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Limits`
。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance isIso_ι_initial [HasInitial J] (F : J ⥤ C) [∀ (i j : J) (f : i ⟶ j), IsIso (F.map f)] :
    IsIso (colimit.ι F (⊥_ J)) :=
  isIso_ι_of_isInitial initialIsInitial F

end

end CategoryTheory.Limits

