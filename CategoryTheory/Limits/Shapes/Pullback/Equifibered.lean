/-
Copyright (c) 2022 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
module

public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic
public import Mathlib.CategoryTheory.MorphismProperty.Composition

/-!

# Equifibered natural transformation

## Main definition
- `CategoryTheory.NatTrans.Equifibered`:
  A natural transformation `α : F ⟶ G` is equifibered if every commutative square of the following
  form is a pullback.
  ```
  F(X) → F(Y)
   ↓      ↓
  G(X) → G(Y)
  ```
- `CategoryTheory.NatTrans.Coequifibered`: The dual notion.

-/

@[expose] public section


open CategoryTheory.Limits CategoryTheory.Functor

namespace CategoryTheory

variable {J K C D ι : Type*} [Category* J] [Category* C] [Category* K] [Category* D]

namespace NatTrans

/-- A natural transformation is equifibered if every commutative square of the following form is
a pullback.
```
F(X) → F(Y)
 ↓      ↓
G(X) → G(Y)
```
-/
/-
**CategoryTheory.NatTrans.Equifibered** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.
NatTrans`。
形式化陈述：Equifibered : MorphismProperty (J ⥤ C)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A natural transformation is equifibered if every commutative square of the follo
wing form is
a pullback.
```
F(X) → F(Y)
 ↓      ↓
G(X) → G(Y)
```
-/
def Equifibered : MorphismProperty (J ⥤ C) :=
  fun {F G} α ↦ ∀ ⦃i j : J⦄ (f : i ⟶ j), IsPullback (F.map f) (α.app i) (α.app j) (G.map f)
/-
**CategoryTheory.NatTrans.Equifibered.of_isIso** 是 Mathlib 中的一个定理，位于命名空间 `Catego
ryTheory.NatTrans.Equifibered`。
形式化陈述：∀ {J : Type u_1} {C : Type u_3} [inst : CategoryTheory.Category.{v_1, u_1}
 J]   [inst_1 : CategoryTheory.Category.{v_2, u_3} C] {F G : CategoryTheory.Func
tor J C} (α : F ⟶ G)   [CategoryTheory.IsIso α], CategoryTheory.NatTrans.Equifib
ered α
参数：α : F ⟶ G。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.IsPullback.of_vert_isIso`：of_vert_isIso [IsIso snd] [IsIs
o f] (sq : CommSq fst snd f g) : IsPullback fst snd f g
· 使用定理 `CategoryTheory.NatIso.isIso_app_of_isIso`：∀ {C : Type u₁} [inst : Catego
ryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v
₂, u₂} D]   {F G : CategoryThe…
· 使用定理 `CategoryTheory.NatTrans.naturality`：∀ {C : Type u₁} [inst : CategoryTheo
ry.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂}
 D]   {F G : CategoryThe…
-/
theorem Equifibered.of_isIso {F G : J ⥤ C} (α : F ⟶ G) [IsIso α] : Equifibered α :=
  fun _ _ f => IsPullback.of_vert_isIso ⟨naturality _ f⟩

@[deprecated (since := "2026-02-01")] alias equifibered_of_isIso := Equifibered.of_isIso
/-
**CategoryTheory.NatTrans.Equifibered.comp** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTh
eory.NatTrans.Equifibered`。
形式化陈述：∀ {J : Type u_1} {C : Type u_3} [inst : CategoryTheory.Category.{v_1, u_1}
 J]   [inst_1 : CategoryTheory.Category.{v_2, u_3} C] {F G H : CategoryTheory.Fu
nctor J C} {α : F ⟶ G} {β : G ⟶ H},   CategoryTheory.NatTrans.Equifibered α →   
  CategoryTheory.NatTrans.Equifibered β → CategoryTheory.NatTrans.Equifibered (C
ategoryTheory.CategoryStruct.comp α β)
参数：CategoryTheory.CategoryStruct.comp α β。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.IsPullback.paste_vert`：paste_vert {X₁₁ X₁₂ X₂₁ X₂₂ X₃₁ X₃
₂ : C} {h₁₁ : X₁₁ ⟶ X₁₂} {h₂₁ : X₂₁ ⟶ X₂₂} {h₃₁ : X₃₁ ⟶ X₃₂} {v₁₁ : X₁₁ ⟶ X₂₁} {
v₁₂ : X₁₂ ⟶ X₂₂} {v₂₁ : X₂…
-/
theorem Equifibered.comp {F G H : J ⥤ C} {α : F ⟶ G} {β : G ⟶ H} (hα : Equifibered α)
    (hβ : Equifibered β) : Equifibered (α ≫ β) :=
  fun _ _ f => (hα f).paste_vert (hβ f)
/-
**CategoryTheory.NatTrans.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.NatTrans`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : (Equifibered (J := J) (C := C)).IsMultiplicative where
  id_mem _ := .of_isIso _
  comp_mem _ _ := .comp
/-
**CategoryTheory.NatTrans.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.NatTrans`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : (Equifibered (J := J) (C := C)).RespectsIso :=
  MorphismProperty.respectsIso_of_isStableUnderComposition fun _ _ ↦ .of_isIso
/-
**CategoryTheory.NatTrans.Equifibered.whiskerRight** 是 Mathlib 中的一个定理，位于命名空间 `Ca
tegoryTheory.NatTrans.Equifibered`。
形式化陈述：∀ {J : Type u_1} {C : Type u_3} {D : Type u_4} [inst : CategoryTheory.Cate
gory.{v_1, u_1} J]   [inst_1 : CategoryTheory.Category.{v_2, u_3} C] [inst_2 : C
ategoryTheory.Category.{v_4, u_4} D]   {F G : CategoryTheory.Functor J C} {α : F
 ⟶ G},   CategoryTheory.NatTrans.Equifibered α →     ∀ (H : CategoryTheory.Funct
or C D)       [∀ (i j : J) (f : j ⟶ i),           CategoryTheory.Limits.Preserve
sLimit (CategoryTheory.Limits.cospan (α.app i) (G.map f)) H],       CategoryTheo
ry.NatTrans.Equifibered (CategoryTheory.Functor.whiskerRight α H)
参数：H : CategoryTheory.Functor C D；i j : J；f : j ⟶ i；CategoryTheory.Limits.cospan
 (α.app i) (G.map f)；CategoryTheory.Functor.whiskerRight α H。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.IsPullback.map`：∀ {C : Type u₁} [inst : CategoryTheory.Ca
tegory.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]  
 (F : CategoryTheor…
-/
theorem Equifibered.whiskerRight {F G : J ⥤ C} {α : F ⟶ G} (hα : Equifibered α)
    (H : C ⥤ D) [∀ (i j : J) (f : j ⟶ i), PreservesLimit (cospan (α.app i) (G.map f)) H] :
    Equifibered (whiskerRight α H) :=
  fun _ _ f => (hα f).map H
/-
**CategoryTheory.NatTrans.Equifibered.whiskerLeft** 是 Mathlib 中的一个定理，位于命名空间 `Cat
egoryTheory.NatTrans.Equifibered`。
形式化陈述：∀ {J : Type u_1} {K : Type u_2} {C : Type u_3} [inst : CategoryTheory.Cate
gory.{v_1, u_1} J]   [inst_1 : CategoryTheory.Category.{v_2, u_3} C] [inst_2 : C
ategoryTheory.Category.{v_3, u_2} K]   {F G : CategoryTheory.Functor J C} {α : F
 ⟶ G},   CategoryTheory.NatTrans.Equifibered α →     ∀ (H : CategoryTheory.Funct
or K J), CategoryTheory.NatTrans.Equifibered (H.whiskerLeft α)
参数：H : CategoryTheory.Functor K J；H.whiskerLeft α。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem Equifibered.whiskerLeft {F G : J ⥤ C} {α : F ⟶ G} (hα : Equifibered α) (H : K ⥤ J) :
    Equifibered (whiskerLeft H α) :=
  fun _ _ f => hα (H.map f)
/-
**CategoryTheory.NatTrans.Equifibered.of_discrete** 是 Mathlib 中的一个定理，位于命名空间 `Cat
egoryTheory.NatTrans.Equifibered`。
形式化陈述：∀ {C : Type u_3} {ι : Type u_5} [inst : CategoryTheory.Category.{v_2, u_3}
 C]   {F G : CategoryTheory.Functor (CategoryTheory.Discrete ι) C} (α : F ⟶ G), 
CategoryTheory.NatTrans.Equifibered α
参数：CategoryTheory.Discrete ι；α : F ⟶ G。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Discrete.functor_map_id`：functor_map_id (F : Discrete J ⥤
 C) {j : Discrete J} (f : j ⟶ j) : F.map f = 𝟙 (F.obj j)
· 使用定理 `CategoryTheory.IsPullback.of_horiz_isIso`：of_horiz_isIso [IsIso fst] [Is
Iso g] (sq : CommSq fst snd f g) : IsPullback fst snd f g
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
-/
theorem Equifibered.of_discrete {F G : Discrete ι ⥤ C} (α : F ⟶ G) : Equifibered α := by
  rintro ⟨i⟩ ⟨j⟩ ⟨⟨rfl : i = j⟩⟩
  simp only [Discrete.functor_map_id]
  exact IsPullback.of_horiz_isIso ⟨by rw [Category.id_comp, Category.comp_id]⟩

@[deprecated (since := "2026-01-23")]
alias _root_.CategoryTheory.mapPair_equifibered := Equifibered.of_discrete

@[deprecated (since := "2026-01-23")] alias equifibered_of_discrete := Equifibered.of_discrete

/-- A natural transformation is co-equifibered if every commutative square of the following form is
a pushout.
```
F(X) → F(Y)
 ↓      ↓
G(X) → G(Y)
```
-/
/-
**CategoryTheory.NatTrans.Coequifibered** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheor
y.NatTrans`。
形式化陈述：Coequifibered : MorphismProperty (J ⥤ C)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A natural transformation is co-equifibered if every commutative square of the fo
llowing form is
a pushout.
```
F(X) → F(Y)
 ↓      ↓
G(X) → G(Y)
```
-/
def Coequifibered : MorphismProperty (J ⥤ C) :=
  fun {F G} α ↦ ∀ ⦃i j : J⦄ (f : i ⟶ j), IsPushout (F.map f) (α.app i) (α.app j) (G.map f)
/-
**CategoryTheory.NatTrans.Coequifibered.of_isIso** 是 Mathlib 中的一个定理，位于命名空间 `Cate
goryTheory.NatTrans.Coequifibered`。
形式化陈述：∀ {J : Type u_1} {C : Type u_3} [inst : CategoryTheory.Category.{v_1, u_1}
 J]   [inst_1 : CategoryTheory.Category.{v_2, u_3} C] {F G : CategoryTheory.Func
tor J C} (α : F ⟶ G)   [CategoryTheory.IsIso α], CategoryTheory.NatTrans.Coequif
ibered α
参数：α : F ⟶ G。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.IsPushout.of_vert_isIso`：of_vert_isIso [IsIso g] [IsIso i
nl] (sq : CommSq f g inl inr) : IsPushout f g inl inr
· 使用定理 `CategoryTheory.NatIso.isIso_app_of_isIso`：∀ {C : Type u₁} [inst : Catego
ryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v
₂, u₂} D]   {F G : CategoryThe…
· 使用定理 `CategoryTheory.NatTrans.naturality`：∀ {C : Type u₁} [inst : CategoryTheo
ry.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂}
 D]   {F G : CategoryThe…
-/
theorem Coequifibered.of_isIso {F G : J ⥤ C} (α : F ⟶ G) [IsIso α] : Coequifibered α :=
  fun _ _ f => .of_vert_isIso ⟨naturality _ f⟩

@[deprecated (since := "2026-02-01")] alias Coequifibered_of_isIso := Coequifibered.of_isIso
/-
**CategoryTheory.NatTrans.Coequifibered.comp** 是 Mathlib 中的一个定理，位于命名空间 `Category
Theory.NatTrans.Coequifibered`。
形式化陈述：∀ {J : Type u_1} {C : Type u_3} [inst : CategoryTheory.Category.{v_1, u_1}
 J]   [inst_1 : CategoryTheory.Category.{v_2, u_3} C] {F G H : CategoryTheory.Fu
nctor J C} {α : F ⟶ G} {β : G ⟶ H},   CategoryTheory.NatTrans.Coequifibered α → 
    CategoryTheory.NatTrans.Coequifibered β →       CategoryTheory.NatTrans.Coeq
uifibered (CategoryTheory.CategoryStruct.comp α β)
参数：CategoryTheory.CategoryStruct.comp α β。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.IsPushout.paste_vert`：paste_vert {X₁₁ X₁₂ X₂₁ X₂₂ X₃₁ X₃₂
 : C} {h₁₁ : X₁₁ ⟶ X₁₂} {h₂₁ : X₂₁ ⟶ X₂₂} {h₃₁ : X₃₁ ⟶ X₃₂} {v₁₁ : X₁₁ ⟶ X₂₁} {v
₁₂ : X₁₂ ⟶ X₂₂} {v₂₁ : X₂…
-/
theorem Coequifibered.comp {F G H : J ⥤ C} {α : F ⟶ G} {β : G ⟶ H} (hα : Coequifibered α)
    (hβ : Coequifibered β) : Coequifibered (α ≫ β) :=
  fun _ _ f => (hα f).paste_vert (hβ f)
/-
**CategoryTheory.NatTrans.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.NatTrans`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : (Coequifibered (J := J) (C := C)).IsMultiplicative where
  id_mem _ := .of_isIso _
  comp_mem _ _ := .comp
/-
**CategoryTheory.NatTrans.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.NatTrans`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : (Coequifibered (J := J) (C := C)).RespectsIso :=
  MorphismProperty.respectsIso_of_isStableUnderComposition fun _ _ ↦ .of_isIso
/-
**CategoryTheory.NatTrans.Coequifibered.whiskerRight** 是 Mathlib 中的一个定理，位于命名空间 `
CategoryTheory.NatTrans.Coequifibered`。
形式化陈述：∀ {J : Type u_1} {C : Type u_3} {D : Type u_4} [inst : CategoryTheory.Cate
gory.{v_1, u_1} J]   [inst_1 : CategoryTheory.Category.{v_2, u_3} C] [inst_2 : C
ategoryTheory.Category.{v_4, u_4} D]   {F G : CategoryTheory.Functor J C} {α : F
 ⟶ G},   CategoryTheory.NatTrans.Coequifibered α →     ∀ (H : CategoryTheory.Fun
ctor C D)       [∀ (i j : J) (f : j ⟶ i),           CategoryTheory.Limits.Preser
vesColimit (CategoryTheory.Limits.span (F.map f) (α.app j)) H],       CategoryTh
eory.NatTrans.Coequifibered (CategoryTheory.Functor.whiskerRight α H)
参数：H : CategoryTheory.Functor C D；i j : J；f : j ⟶ i；CategoryTheory.Limits.span (
F.map f) (α.app j)；CategoryTheory.Functor.whiskerRight α H。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.IsPushout.map`：∀ {C : Type u₁} [inst : CategoryTheory.Cat
egory.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]   
(F : CategoryTheor…
-/
theorem Coequifibered.whiskerRight {F G : J ⥤ C} {α : F ⟶ G} (hα : Coequifibered α)
    (H : C ⥤ D) [∀ (i j : J) (f : j ⟶ i), PreservesColimit (span (F.map f) (α.app j)) H] :
    Coequifibered (whiskerRight α H) :=
  fun _ _ f => (hα f).map H
/-
**CategoryTheory.NatTrans.Coequifibered.whiskerLeft** 是 Mathlib 中的一个定理，位于命名空间 `C
ategoryTheory.NatTrans.Coequifibered`。
形式化陈述：∀ {J : Type u_1} {K : Type u_2} {C : Type u_3} [inst : CategoryTheory.Cate
gory.{v_1, u_1} J]   [inst_1 : CategoryTheory.Category.{v_2, u_3} C] [inst_2 : C
ategoryTheory.Category.{v_3, u_2} K]   {F G : CategoryTheory.Functor J C} {α : F
 ⟶ G},   CategoryTheory.NatTrans.Coequifibered α →     ∀ (H : CategoryTheory.Fun
ctor K J), CategoryTheory.NatTrans.Coequifibered (H.whiskerLeft α)
参数：H : CategoryTheory.Functor K J；H.whiskerLeft α。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem Coequifibered.whiskerLeft {F G : J ⥤ C} {α : F ⟶ G} (hα : Coequifibered α) (H : K ⥤ J) :
    Coequifibered (whiskerLeft H α) :=
  fun _ _ f => hα (H.map f)
/-
**CategoryTheory.NatTrans.Coequifibered.of_discrete** 是 Mathlib 中的一个定理，位于命名空间 `C
ategoryTheory.NatTrans.Coequifibered`。
形式化陈述：∀ {C : Type u_3} [inst : CategoryTheory.Category.{v_2, u_3} C] {ι : Type u
_6}   {F G : CategoryTheory.Functor (CategoryTheory.Discrete ι) C} (α : F ⟶ G), 
CategoryTheory.NatTrans.Equifibered α
参数：CategoryTheory.Discrete ι；α : F ⟶ G。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Discrete.functor_map_id`：functor_map_id (F : Discrete J ⥤
 C) {j : Discrete J} (f : j ⟶ j) : F.map f = 𝟙 (F.obj j)
· 使用定理 `CategoryTheory.IsPullback.of_horiz_isIso`：of_horiz_isIso [IsIso fst] [Is
Iso g] (sq : CommSq fst snd f g) : IsPullback fst snd f g
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
-/
theorem Coequifibered.of_discrete {ι : Type*} {F G : Discrete ι ⥤ C}
    (α : F ⟶ G) : Equifibered α := by
  rintro ⟨i⟩ ⟨j⟩ ⟨⟨rfl : i = j⟩⟩
  simp only [Discrete.functor_map_id]
  exact IsPullback.of_horiz_isIso ⟨by rw [Category.id_comp, Category.comp_id]⟩

section Opposite

/-
**CategoryTheory.NatTrans.Coequifibered.op** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTh
eory.NatTrans.Coequifibered`。
形式化陈述：∀ {J : Type u_1} {C : Type u_3} [inst : CategoryTheory.Category.{v_1, u_1}
 J]   [inst_1 : CategoryTheory.Category.{v_2, u_3} C] {F G : CategoryTheory.Func
tor J C} {α : F ⟶ G},   CategoryTheory.NatTrans.Coequifibered α → CategoryTheory
.NatTrans.Equifibered (CategoryTheory.NatTrans.op α)
参数：CategoryTheory.NatTrans.op α。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.IsPushout.op`：op (h : IsPushout f g inl inr) : IsPullback
 inr.op inl.op g.op f.op
-/
theorem Coequifibered.op {F G : J ⥤ C} {α : F ⟶ G} (hα : Coequifibered α) :
    Equifibered (NatTrans.op α) := fun _ _ f ↦ (hα f.unop).op
/-
**CategoryTheory.NatTrans.Equifibered.op** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheo
ry.NatTrans.Equifibered`。
形式化陈述：∀ {J : Type u_1} {C : Type u_3} [inst : CategoryTheory.Category.{v_1, u_1}
 J]   [inst_1 : CategoryTheory.Category.{v_2, u_3} C] {F G : CategoryTheory.Func
tor J C} {α : F ⟶ G},   CategoryTheory.NatTrans.Equifibered α → CategoryTheory.N
atTrans.Coequifibered (CategoryTheory.NatTrans.op α)
参数：CategoryTheory.NatTrans.op α。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.IsPullback.op`：op (h : IsPullback fst snd f g) : IsPushou
t g.op f.op snd.op fst.op
-/
theorem Equifibered.op {F G : J ⥤ C} {α : F ⟶ G} (hα : Equifibered α) :
    Coequifibered (NatTrans.op α) := fun _ _ f ↦ (hα f.unop).op
/-
**CategoryTheory.NatTrans.Coequifibered.unop** 是 Mathlib 中的一个定理，位于命名空间 `Category
Theory.NatTrans.Coequifibered`。
形式化陈述：∀ {J : Type u_1} {C : Type u_3} [inst : CategoryTheory.Category.{v_1, u_1}
 J]   [inst_1 : CategoryTheory.Category.{v_2, u_3} C] {F G : CategoryTheory.Func
tor Jᵒᵖ Cᵒᵖ} {α : F ⟶ G},   CategoryTheory.NatTrans.Coequifibered α → CategoryTh
eory.NatTrans.Equifibered (CategoryTheory.NatTrans.unop α)
参数：CategoryTheory.NatTrans.unop α。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.IsPushout.unop`：unop {Z X Y P : Cᵒᵖ} {f : Z ⟶ X} {g : Z ⟶
 Y} {inl : X ⟶ P} {inr : Y ⟶ P} (h : IsPushout f g inl inr) : IsPullback inr.uno
p inl.unop g.unop f…
-/
theorem Coequifibered.unop {F G : Jᵒᵖ ⥤ Cᵒᵖ} {α : F ⟶ G} (hα : Coequifibered α) :
    Equifibered (NatTrans.unop α) := fun _ _ f ↦ (hα f.op).unop
/-
**CategoryTheory.NatTrans.Equifibered.unop** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTh
eory.NatTrans.Equifibered`。
形式化陈述：∀ {J : Type u_1} {C : Type u_3} [inst : CategoryTheory.Category.{v_1, u_1}
 J]   [inst_1 : CategoryTheory.Category.{v_2, u_3} C] {F G : CategoryTheory.Func
tor Jᵒᵖ Cᵒᵖ} {α : F ⟶ G},   CategoryTheory.NatTrans.Equifibered α → CategoryTheo
ry.NatTrans.Coequifibered (CategoryTheory.NatTrans.unop α)
参数：CategoryTheory.NatTrans.unop α。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.IsPullback.unop`：unop {P X Y Z : Cᵒᵖ} {fst : P ⟶ X} {snd 
: P ⟶ Y} {f : X ⟶ Z} {g : Y ⟶ Z} (h : IsPullback fst snd f g) : IsPushout g.unop
 f.unop snd.unop fst…
-/
theorem Equifibered.unop {F G : Jᵒᵖ ⥤ Cᵒᵖ} {α : F ⟶ G} (hα : Equifibered α) :
    Coequifibered (NatTrans.unop α) := fun _ _ f ↦ (hα f.op).unop
/-
**CategoryTheory.NatTrans.Equifibered.rightOp** 是 Mathlib 中的一个定理，位于命名空间 `Categor
yTheory.NatTrans.Equifibered`。
形式化陈述：∀ {J : Type u_1} {C : Type u_3} [inst : CategoryTheory.Category.{v_1, u_1}
 J]   [inst_1 : CategoryTheory.Category.{v_2, u_3} C] {F G : CategoryTheory.Func
tor Jᵒᵖ C} {α : F ⟶ G},   CategoryTheory.NatTrans.Equifibered α → CategoryTheory
.NatTrans.Coequifibered (CategoryTheory.NatTrans.rightOp α)
参数：CategoryTheory.NatTrans.rightOp α。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.IsPullback.op`：op (h : IsPullback fst snd f g) : IsPushou
t g.op f.op snd.op fst.op
-/
theorem Equifibered.rightOp {F G : Jᵒᵖ ⥤ C} {α : F ⟶ G} (hα : Equifibered α) :
    Coequifibered α.rightOp := fun _ _ f ↦ (hα f.op).op
/-
**CategoryTheory.NatTrans.Coequifibered.rightOp** 是 Mathlib 中的一个定理，位于命名空间 `Categ
oryTheory.NatTrans.Coequifibered`。
形式化陈述：∀ {J : Type u_1} {C : Type u_3} [inst : CategoryTheory.Category.{v_1, u_1}
 J]   [inst_1 : CategoryTheory.Category.{v_2, u_3} C] {F G : CategoryTheory.Func
tor Jᵒᵖ C} {α : F ⟶ G},   CategoryTheory.NatTrans.Coequifibered α → CategoryTheo
ry.NatTrans.Equifibered (CategoryTheory.NatTrans.rightOp α)
参数：CategoryTheory.NatTrans.rightOp α。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.IsPushout.op`：op (h : IsPushout f g inl inr) : IsPullback
 inr.op inl.op g.op f.op
-/
theorem Coequifibered.rightOp {F G : Jᵒᵖ ⥤ C} {α : F ⟶ G} (hα : Coequifibered α) :
    Equifibered α.rightOp := fun _ _ f ↦ (hα f.op).op
/-
**CategoryTheory.NatTrans.coequifibered_op_iff** 是 Mathlib 中的一个定理，位于命名空间 `Catego
ryTheory.NatTrans`。
形式化陈述：coequifibered_op_iff {F G : J ⥤ C} {α : F ⟶ G} : Coequifibered (NatTrans.o
p α) ↔ Equifibered α
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.NatTrans.Coequifibered.unop`：∀ {J : Type u_1} {C : Type u
_3} [inst : CategoryTheory.Category.{v_1, u_1} J]   [inst_1 : CategoryTheory.Cat
egory.{v_2, u_3} C] {F G : Categ…
· 使用定理 `CategoryTheory.NatTrans.Equifibered.op`：∀ {J : Type u_1} {C : Type u_3} 
[inst : CategoryTheory.Category.{v_1, u_1} J]   [inst_1 : CategoryTheory.Categor
y.{v_2, u_3} C] {F G : Categ…
-/
theorem coequifibered_op_iff {F G : J ⥤ C} {α : F ⟶ G} :
    Coequifibered (NatTrans.op α) ↔ Equifibered α := ⟨Coequifibered.unop, Equifibered.op⟩
/-
**CategoryTheory.NatTrans.equifibered_op_iff** 是 Mathlib 中的一个定理，位于命名空间 `Category
Theory.NatTrans`。
形式化陈述：equifibered_op_iff {F G : J ⥤ C} {α : F ⟶ G} : Equifibered (NatTrans.op α)
 ↔ Coequifibered α
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.NatTrans.Equifibered.unop`：∀ {J : Type u_1} {C : Type u_3
} [inst : CategoryTheory.Category.{v_1, u_1} J]   [inst_1 : CategoryTheory.Categ
ory.{v_2, u_3} C] {F G : Categ…
· 使用定理 `CategoryTheory.NatTrans.Coequifibered.op`：∀ {J : Type u_1} {C : Type u_3
} [inst : CategoryTheory.Category.{v_1, u_1} J]   [inst_1 : CategoryTheory.Categ
ory.{v_2, u_3} C] {F G : Categ…
-/
theorem equifibered_op_iff {F G : J ⥤ C} {α : F ⟶ G} :
    Equifibered (NatTrans.op α) ↔ Coequifibered α := ⟨Equifibered.unop, Coequifibered.op⟩
/-
**CategoryTheory.NatTrans.coequifibered_unop_iff** 是 Mathlib 中的一个定理，位于命名空间 `Cate
goryTheory.NatTrans`。
形式化陈述：coequifibered_unop_iff {F G : Jᵒᵖ ⥤ Cᵒᵖ} {α : F ⟶ G} : Coequifibered (NatT
rans.unop α) ↔ Equifibered α
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.NatTrans.Coequifibered.op`：∀ {J : Type u_1} {C : Type u_3
} [inst : CategoryTheory.Category.{v_1, u_1} J]   [inst_1 : CategoryTheory.Categ
ory.{v_2, u_3} C] {F G : Categ…
· 使用定理 `CategoryTheory.NatTrans.Equifibered.unop`：∀ {J : Type u_1} {C : Type u_3
} [inst : CategoryTheory.Category.{v_1, u_1} J]   [inst_1 : CategoryTheory.Categ
ory.{v_2, u_3} C] {F G : Categ…
-/
theorem coequifibered_unop_iff {F G : Jᵒᵖ ⥤ Cᵒᵖ} {α : F ⟶ G} :
    Coequifibered (NatTrans.unop α) ↔ Equifibered α := ⟨Coequifibered.op, Equifibered.unop⟩
/-
**CategoryTheory.NatTrans.equifibered_unop_iff** 是 Mathlib 中的一个定理，位于命名空间 `Catego
ryTheory.NatTrans`。
形式化陈述：equifibered_unop_iff {F G : Jᵒᵖ ⥤ Cᵒᵖ} {α : F ⟶ G} : Equifibered (NatTrans
.unop α) ↔ Coequifibered α
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.NatTrans.Equifibered.op`：∀ {J : Type u_1} {C : Type u_3} 
[inst : CategoryTheory.Category.{v_1, u_1} J]   [inst_1 : CategoryTheory.Categor
y.{v_2, u_3} C] {F G : Categ…
· 使用定理 `CategoryTheory.NatTrans.Coequifibered.unop`：∀ {J : Type u_1} {C : Type u
_3} [inst : CategoryTheory.Category.{v_1, u_1} J]   [inst_1 : CategoryTheory.Cat
egory.{v_2, u_3} C] {F G : Categ…
-/
theorem equifibered_unop_iff {F G : Jᵒᵖ ⥤ Cᵒᵖ} {α : F ⟶ G} :
    Equifibered (NatTrans.unop α) ↔ Coequifibered α := ⟨Equifibered.op, Coequifibered.unop⟩

end Opposite

end NatTrans

end CategoryTheory

