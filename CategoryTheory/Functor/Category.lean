/-
Copyright (c) 2017 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tim Baumann, Stephen Morgan, Kim Morrison, Floris van Doorn
-/
module

public import Mathlib.CategoryTheory.NatTrans
public import Mathlib.CategoryTheory.Iso

/-!
# The category of functors and natural transformations between two fixed categories.

We provide the category instance on `C ⥤ D`, with morphisms the natural transformations.

At the end of the file, we provide the left and right unitors, and the associator,
for functor composition.
(In fact functor composition is definitionally associative, but very often relying on this causes
extremely slow elaboration, so it is better to insert it explicitly.)

## Universes

If `C` and `D` are both small categories at the same universe level,
this is another small category at that level.
However if `C` and `D` are both large categories at the same universe level,
this is a small category at the next higher level.
-/

@[expose] public section

set_option mathlib.tactic.category.grind true

namespace CategoryTheory

-- declare the `v`'s first; see note [category theory universes].
universe v₁ v₂ v₃ v₄ u₁ u₂ u₃ u₄

open NatTrans Category CategoryTheory.Functor

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
variable {E : Type u₃} [Category.{v₃} E] {E' : Type u₄} [Category.{v₄} E']
variable {F G H I : C ⥤ D}

attribute [local grind =] NatTrans.id_app' in
/-- `Functor.category C D` gives the category structure on functors and natural transformations
between categories `C` and `D`.

Notice that if `C` and `D` are both small categories at the same universe level,
this is another small category at that level.
However if `C` and `D` are both large categories at the same universe level,
this is a small category at the next higher level.
-/
/-
**CategoryTheory.Functor.category** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Func
tor`。
形式化陈述：{C : Type u₁} →   [inst : CategoryTheory.Category.{v₁, u₁} C] →     {D : T
ype u₂} →       [inst_1 : CategoryTheory.Category.{v₂, u₂} D] →         Category
Theory.Category.{max u₁ v₂, max (max (max u₂ u₁) v₂) v₁} (CategoryTheory.Functor
 C D)
参数：max (max u₂ u₁) v₂；CategoryTheory.Functor C D。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`Functor.category C D` gives the category structure on functors and natural tran
sformations
between categories `C` and `D`.

Notice that if `C` and `D` are both small categories at the same universe level,
this is another small category at that level.
However if `C` and `D` are both large categories at the same universe level,
this is a small category at the next higher level.
-/
instance Functor.category : Category.{max u₁ v₂} (C ⥤ D) where
  Hom F G := NatTrans F G
  id F := NatTrans.id F
  comp α β := vcomp α β

namespace NatTrans

@[ext, grind ext, to_dual self]
/-
**CategoryTheory.NatTrans.ext'** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.NatTran
s`。
形式化陈述：ext' {α β : F ⟶ G} (w : α.app = β.app) : α = β
参数：w : α.app = β.app。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.NatTrans.ext`：∀ {C : Type u₁} {inst : CategoryTheory.Cate
gory.{v₁, u₁} C} {D : Type u₂} {inst_1 : CategoryTheory.Category.{v₂, u₂} D}   {
F G : CategoryThe…
-/
theorem ext' {α β : F ⟶ G} (w : α.app = β.app) : α = β := NatTrans.ext w

@[simp, to_dual self]
/-
**CategoryTheory.NatTrans.vcomp_eq_comp** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheor
y.NatTrans`。
形式化陈述：vcomp_eq_comp (α : F ⟶ G) (β : G ⟶ H) : vcomp α β = α ≫ β
参数：α : F ⟶ G；β : G ⟶ H。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem vcomp_eq_comp (α : F ⟶ G) (β : G ⟶ H) : vcomp α β = α ≫ β := rfl

@[to_dual self]
/-
**CategoryTheory.NatTrans.vcomp_app'** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.N
atTrans`。
形式化陈述：vcomp_app' (α : F ⟶ G) (β : G ⟶ H) (X : C) : (α ≫ β).app X = α.app X ≫ β.a
pp X
参数：α : F ⟶ G；β : G ⟶ H；X : C。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem vcomp_app' (α : F ⟶ G) (β : G ⟶ H) (X : C) : (α ≫ β).app X = α.app X ≫ β.app X := rfl

@[to_dual self]
/-
**CategoryTheory.NatTrans.congr_app** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.Na
tTrans`。
形式化陈述：congr_app {α β : F ⟶ G} (h : α = β) (X : C) : α.app X = β.app X
参数：h : α = β；X : C。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
-/
theorem congr_app {α β : F ⟶ G} (h : α = β) (X : C) : α.app X = β.app X := by rw [h]

@[simp, grind =]
/-
**CategoryTheory.NatTrans.id_app** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.NatTr
ans`。
形式化陈述：id_app (F : C ⥤ D) (X : C) : (𝟙 F : F ⟶ F).app X = 𝟙 (F.obj X)
参数：F : C ⥤ D；X : C。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem id_app (F : C ⥤ D) (X : C) : (𝟙 F : F ⟶ F).app X = 𝟙 (F.obj X) := rfl

@[simp, grind _=_, to_dual self, reassoc]
/-
**CategoryTheory.NatTrans.comp_app** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.Nat
Trans`。
形式化陈述：comp_app {F G H : C ⥤ D} (α : F ⟶ G) (β : G ⟶ H) (X : C) : (α ≫ β).app X =
 α.app X ≫ β.app X
参数：α : F ⟶ G；β : G ⟶ H；X : C。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem comp_app {F G H : C ⥤ D} (α : F ⟶ G) (β : G ⟶ H) (X : C) :
    (α ≫ β).app X = α.app X ≫ β.app X := rfl

@[to_dual none, reassoc]
/-
**CategoryTheory.NatTrans.app_naturality** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheo
ry.NatTrans`。
形式化陈述：app_naturality {F G : C ⥤ D ⥤ E} (T : F ⟶ G) (X : C) {Y Z : D} (f : Y ⟶ Z)
 : (F.obj X).map f ≫ (T.app X).app Z = (T.app X).app Y ≫ (G.obj X).map f
参数：T : F ⟶ G；X : C；f : Y ⟶ Z。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.NatTrans.naturality`：∀ {C : Type u₁} [inst : CategoryTheo
ry.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂}
 D]   {F G : CategoryThe…
-/
theorem app_naturality {F G : C ⥤ D ⥤ E} (T : F ⟶ G) (X : C) {Y Z : D} (f : Y ⟶ Z) :
    (F.obj X).map f ≫ (T.app X).app Z = (T.app X).app Y ≫ (G.obj X).map f :=
  (T.app X).naturality f

@[to_dual none, reassoc (attr := simp)]
/-
**CategoryTheory.NatTrans.naturality_app** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheo
ry.NatTrans`。
形式化陈述：naturality_app {F G : C ⥤ D ⥤ E} (T : F ⟶ G) (Z : D) {X Y : C} (f : X ⟶ Y)
 : (F.map f).app Z ≫ (T.app Y).app Z = (T.app X).app Z ≫ (G.map f).app Z
参数：T : F ⟶ G；Z : D；f : X ⟶ Y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr_fun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g 
→ ∀ (a : α), f a = g a
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `CategoryTheory.NatTrans.naturality`：∀ {C : Type u₁} [inst : CategoryTheo
ry.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂}
 D]   {F G : CategoryThe…
-/
theorem naturality_app {F G : C ⥤ D ⥤ E} (T : F ⟶ G) (Z : D) {X Y : C} (f : X ⟶ Y) :
    (F.map f).app Z ≫ (T.app Y).app Z = (T.app X).app Z ≫ (G.map f).app Z :=
  congr_fun (congr_arg app (T.naturality f)) Z

@[to_dual none, reassoc]
/-
**CategoryTheory.NatTrans.naturality_app_app** 是 Mathlib 中的一个定理，位于命名空间 `Category
Theory.NatTrans`。
形式化陈述：naturality_app_app {F G : C ⥤ D ⥤ E ⥤ E'} (α : F ⟶ G) {X₁ Y₁ : C} (f : X₁ 
⟶ Y₁) (X₂ : D) (X₃ : E) : ((F.map f).app X₂).app X₃ ≫ ((α.app Y₁).app X₂).app X₃
 = ((α.app X₁).app X₂).app X₃ ≫ ((G.map f).app X₂).app X₃
参数：α : F ⟶ G；f : X₁ ⟶ Y₁；X₂ : D；X₃ : E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.NatTrans.congr_app`：congr_app {α β : F ⟶ G} (h : α = β) (
X : C) : α.app X = β.app X
· 使用定理 `CategoryTheory.NatTrans.naturality_app`：naturality_app {F G : C ⥤ D ⥤ E}
 (T : F ⟶ G) (Z : D) {X Y : C} (f : X ⟶ Y) : (F.map f).app Z ≫ (T.app Y).app Z =
 (T.app X).app Z ≫ (G.map f)…
-/
theorem naturality_app_app {F G : C ⥤ D ⥤ E ⥤ E'}
    (α : F ⟶ G) {X₁ Y₁ : C} (f : X₁ ⟶ Y₁) (X₂ : D) (X₃ : E) :
    ((F.map f).app X₂).app X₃ ≫ ((α.app Y₁).app X₂).app X₃ =
      ((α.app X₁).app X₂).app X₃ ≫ ((G.map f).app X₂).app X₃ :=
  congr_app (NatTrans.naturality_app α X₂ f) X₃

@[reassoc]
/-
**CategoryTheory.NatTrans.naturality_inv** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheo
ry.NatTrans`。
形式化陈述：naturality_inv {F G : C ⥤ D} (α : F ⟶ G) {X Y : C} (f : X ⟶ Y) [IsIso (α.a
pp X)] [IsIso (α.app Y)] : inv (α.app X) ≫ F.map f = G.map f ≫ inv (α.app Y)
参数：α : F ⟶ G；f : X ⟶ Y；α.app X；α.app Y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.IsIso.inv_comp_eq`：inv_comp_eq (α : X ⟶ Y) [IsIso α] {f :
 X ⟶ Z} {g : Y ⟶ Z} : inv α ≫ f = g ↔ f = α ≫ g
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.IsIso.eq_comp_inv`：∀ {C : Type u} [inst : CategoryTheory.
Category.{v, u} C] {X Y Z : C} (α : Y ⟶ X) [inst_1 : CategoryTheory.IsIso α]   {
f : Z ⟶ X} {g : Z ⟶ Y}…
· 使用定理 `CategoryTheory.NatTrans.naturality`：∀ {C : Type u₁} [inst : CategoryTheo
ry.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂}
 D]   {F G : CategoryThe…
-/
lemma naturality_inv {F G : C ⥤ D} (α : F ⟶ G) {X Y : C} (f : X ⟶ Y) [IsIso (α.app X)]
    [IsIso (α.app Y)] :
    inv (α.app X) ≫ F.map f = G.map f ≫ inv (α.app Y) := by
  rw [IsIso.inv_comp_eq, ← Category.assoc, IsIso.eq_comp_inv]
  exact α.naturality f

/-- A natural transformation is an epimorphism if each component is. -/
@[to_dual /-- A natural transformation is a monomorphism if each component is. -/]
/-
**CategoryTheory.NatTrans.epi_of_epi_app** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheo
ry.NatTrans`。
形式化陈述：epi_of_epi_app (α : F ⟶ G) [forall X : C, Epi (α.app X)] : Epi α
参数：α : F ⟶ G；α.app X。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.NatTrans.ext'`：ext' {α β : F ⟶ G} (w : α.app = β.app) : α
 = β
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.cancel_epi`：cancel_epi (f : X ⟶ Y) [Epi f] {g h : Y ⟶ Z} 
: f ≫ g = f ≫ h ↔ g = h
· 使用定理 `CategoryTheory.NatTrans.comp_app`：comp_app {F G H : C ⥤ D} (α : F ⟶ G) (
β : G ⟶ H) (X : C) : (α ≫ β).app X = α.app X ≫ β.app X

--- 原说明 ---
A natural transformation is an epimorphism if each component is.
-/
theorem epi_of_epi_app (α : F ⟶ G) [∀ X : C, Epi (α.app X)] : Epi α :=
  ⟨fun g h eq => by
    ext X
    rw [← cancel_epi (α.app X), ← comp_app, eq, comp_app]⟩

/-- The monoid of natural transformations of the identity is commutative. -/
@[to_dual self]
/-
**CategoryTheory.NatTrans.id_comm** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.NatT
rans`。
形式化陈述：id_comm (α β : (𝟭 C) ⟶ (𝟭 C)) : α ≫ β = β ≫ α
参数：α β : (𝟭 C) ⟶ (𝟭 C)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.NatTrans.ext'`：ext' {α β : F ⟶ G} (w : α.app = β.app) : α
 = β
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.NatTrans.naturality`：∀ {C : Type u₁} [inst : CategoryTheo
ry.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂}
 D]   {F G : CategoryThe…

--- 原说明 ---
The monoid of natural transformations of the identity is commutative.
-/
lemma id_comm (α β : (𝟭 C) ⟶ (𝟭 C)) : α ≫ β = β ≫ α := by
  ext X
  exact (α.naturality (β.app X)).symm

/-- `hcomp α β` is the horizontal composition of natural transformations. -/
@[simps (attr := grind =), to_dual self]
/-
**CategoryTheory.NatTrans.hcomp** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.NatTra
ns`。
形式化陈述：hcomp {H I : D ⥤ E} (α : F ⟶ G) (β : H ⟶ I) : F ⋙ H ⟶ G ⋙ I where app
参数：α : F ⟶ G；β : H ⟶ I。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`hcomp α β` is the horizontal composition of natural transformations.
-/
def hcomp {H I : D ⥤ E} (α : F ⟶ G) (β : H ⟶ I) : F ⋙ H ⟶ G ⋙ I where
  app := fun X : C => β.app (F.obj X) ≫ I.map (α.app X)

-- Horizontal composition has two possible definitions that are dual to each other,
-- and we need to prove to `to_dual` that these are equivalent.
set_option linter.auxLemma false in
attribute [to_dual none] hcomp._proof_2 hcomp._proof_3
to_dual_insert_cast hcomp := by ext x; exact β.naturality' (α.app x)

/-- Notation for horizontal composition of natural transformations. -/
infixl:80 " ◫ " => hcomp

@[to_dual self]
/-
**CategoryTheory.NatTrans.hcomp_id_app** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory
.NatTrans`。
形式化陈述：hcomp_id_app {H : D ⥤ E} (α : F ⟶ G) (X : C) : (α ◫ 𝟙 H).app X = H.map (α.
app X)
参数：α : F ⟶ G；X : C。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.NatTrans.hcomp_app`：∀ {C : Type u₁} [inst : CategoryTheor
y.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} 
D]   {E : Type u₃} [ins…
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem hcomp_id_app {H : D ⥤ E} (α : F ⟶ G) (X : C) : (α ◫ 𝟙 H).app X = H.map (α.app X) := by
  simp

@[to_dual self]
/-
**CategoryTheory.NatTrans.id_hcomp_app** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory
.NatTrans`。
形式化陈述：id_hcomp_app {H : E ⥤ C} (α : F ⟶ G) (X : E) : (𝟙 H ◫ α).app X = α.app _
参数：α : F ⟶ G；X : E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.NatTrans.hcomp_app`：∀ {C : Type u₁} [inst : CategoryTheor
y.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} 
D]   {E : Type u₃} [ins…
· 使用定理 `CategoryTheory.Functor.map_id`：∀ {C : Type u₁} [inst : CategoryTheory.Ca
tegory.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]  
 (self : CategoryTh…
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem id_hcomp_app {H : E ⥤ C} (α : F ⟶ G) (X : E) : (𝟙 H ◫ α).app X = α.app _ := by simp

-- Note that we don't yet prove a `hcomp_assoc` lemma here: even stating it is painful, because we
-- need to use associativity of functor composition. (It's true without the explicit associator,
-- because functor composition is definitionally associative,
-- but relying on the definitional equality causes bad problems with elaboration later.)
@[to_dual self]
/-
**CategoryTheory.NatTrans.exchange** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.Nat
Trans`。
形式化陈述：exchange {I J K : D ⥤ E} (α : F ⟶ G) (β : G ⟶ H) (γ : I ⟶ J) (δ : J ⟶ K) :
 (α ≫ β) ◫ (γ ≫ δ) = (α ◫ γ) ≫ β ◫ δ
参数：α : F ⟶ G；β : G ⟶ H；γ : I ⟶ J；δ : J ⟶ K。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.NatTrans.ext'`：ext' {α β : F ⟶ G} (w : α.app = β.app) : α
 = β
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
-/
theorem exchange {I J K : D ⥤ E} (α : F ⟶ G) (β : G ⟶ H) (γ : I ⟶ J) (δ : J ⟶ K) :
    (α ≫ β) ◫ (γ ≫ δ) = (α ◫ γ) ≫ β ◫ δ := by
  cat_disch

end NatTrans

namespace Functor

/-- Flip the arguments of a bifunctor. See also `Currying.lean`. -/
@[implicit_reducible, simps (attr := grind =) obj_obj obj_map]
/-
**CategoryTheory.Functor.flip** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Functor`
。
形式化陈述：{C : Type u₁} →   [inst : CategoryTheory.Category.{v₁, u₁} C] →     {D : T
ype u₂} →       [inst_1 : CategoryTheory.Category.{v₂, u₂} D] →         {E : Typ
e u₃} →           [inst_2 : CategoryTheory.Category.{v₃, u₃} E] →             Ca
tegoryTheory.Functor C (CategoryTheory.Functor D E) →               CategoryTheo
ry.Functor D (CategoryTheory.Functor C E)
参数：CategoryTheory.Functor D E；CategoryTheory.Functor C E。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Flip the arguments of a bifunctor. See also `Currying.lean`.
-/
protected def flip (F : C ⥤ D ⥤ E) : D ⥤ C ⥤ E where
  obj k :=
    { obj := fun j => (F.obj j).obj k,
      map := fun f => (F.map f).app k, }
  map f := { app := fun j => (F.obj j).map f }

-- `@[simps]` doesn't produce a nicely stated lemma here:
-- the implicit arguments for `app` use the definition of `flip`, rather than `flip` itself.
/-
**CategoryTheory.Functor.flip_map_app** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.
Functor`。
形式化陈述：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} 
[inst_1 : CategoryTheory.Category.{v₂, u₂} D]   {E : Type u₃} [inst_2 : Category
Theory.Category.{v₃, u₃} E]   (F : CategoryTheory.Functor C (CategoryTheory.Func
tor D E)) {d d' : D} (f : d ⟶ d') (c : C),   (F.flip.map f).app c = (F.obj c).ma
p f
参数：F : CategoryTheory.Functor C (CategoryTheory.Functor D E)；f : d ⟶ d'；c : C；F.
flip.map f；F.obj c。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp, grind =] theorem flip_map_app (F : C ⥤ D ⥤ E) {d d' : D} (f : d ⟶ d') (c : C) :
    (F.flip.map f).app c = (F.obj c).map f := rfl

/-- The left unitor, a natural isomorphism `((𝟭 _) ⋙ F) ≅ F`.
-/
@[implicit_reducible, simps]
/-
**CategoryTheory.Functor.leftUnitor** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Fu
nctor`。
形式化陈述：leftUnitor (F : C ⥤ D) : 𝟭 C ⋙ F ≅ F where hom
参数：F : C ⥤ D。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The left unitor, a natural isomorphism `((𝟭 _) ⋙ F) ≅ F`.
-/
def leftUnitor (F : C ⥤ D) :
    𝟭 C ⋙ F ≅ F where
  hom := { app := fun X => 𝟙 (F.obj X) }
  inv := { app := fun X => 𝟙 (F.obj X) }

/-- The right unitor, a natural isomorphism `(F ⋙ (𝟭 B)) ≅ F`.
-/
@[implicit_reducible, simps]
/-
**CategoryTheory.Functor.rightUnitor** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.F
unctor`。
形式化陈述：rightUnitor (F : C ⥤ D) : F ⋙ 𝟭 D ≅ F where hom
参数：F : C ⥤ D。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The right unitor, a natural isomorphism `(F ⋙ (𝟭 B)) ≅ F`.
-/
def rightUnitor (F : C ⥤ D) :
    F ⋙ 𝟭 D ≅ F where
  hom := { app := fun X => 𝟙 (F.obj X) }
  inv := { app := fun X => 𝟙 (F.obj X) }

/-- The associator for functors, a natural isomorphism `((F ⋙ G) ⋙ H) ≅ (F ⋙ (G ⋙ H))`.

(In fact, `iso.refl _` will work here, but it tends to make Lean slow later,
and it's usually best to insert explicit associators.)
-/
@[implicit_reducible, simps]
/-
**CategoryTheory.Functor.associator** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Fu
nctor`。
形式化陈述：associator (F : C ⥤ D) (G : D ⥤ E) (H : E ⥤ E') : (F ⋙ G) ⋙ H ≅ F ⋙ G ⋙ H 
where hom
参数：F : C ⥤ D；G : D ⥤ E；H : E ⥤ E'。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The associator for functors, a natural isomorphism `((F ⋙ G) ⋙ H) ≅ (F ⋙ (G ⋙ H)
)`.

(In fact, `iso.refl _` will work here, but it tends to make Lean slow later,
and it's usually best to insert explicit associators.)
-/
def associator (F : C ⥤ D) (G : D ⥤ E) (H : E ⥤ E') :
    (F ⋙ G) ⋙ H ≅ F ⋙ G ⋙ H where
  hom := { app := fun _ => 𝟙 _ }
  inv := { app := fun _ => 𝟙 _ }
/-
**CategoryTheory.Functor.assoc** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.Functor
`。
形式化陈述：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} 
[inst_1 : CategoryTheory.Category.{v₂, u₂} D]   {E : Type u₃} [inst_2 : Category
Theory.Category.{v₃, u₃} E] {E' : Type u₄}   [inst_3 : CategoryTheory.Category.{
v₄, u₄} E'] (F : CategoryTheory.Functor C D) (G : CategoryTheory.Functor D E)   
(H : CategoryTheory.Functor E E'), (F.comp G).comp H = F.comp (G.comp H)
参数：F : CategoryTheory.Functor C D；G : CategoryTheory.Functor D E；H : CategoryThe
ory.Functor E E'；F.comp G；G.comp H。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
protected theorem assoc (F : C ⥤ D) (G : D ⥤ E) (H : E ⥤ E') : (F ⋙ G) ⋙ H = F ⋙ G ⋙ H :=
  rfl

end Functor

variable (C D E) in
/-- The functor `(C ⥤ D ⥤ E) ⥤ D ⥤ C ⥤ E` which flips the variables. -/
@[implicit_reducible, simps]
/-
**CategoryTheory.flipFunctor** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory`。
形式化陈述：flipFunctor : (C ⥤ D ⥤ E) ⥤ D ⥤ C ⥤ E where obj F
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The functor `(C ⥤ D ⥤ E) ⥤ D ⥤ C ⥤ E` which flips the variables.
-/
def flipFunctor : (C ⥤ D ⥤ E) ⥤ D ⥤ C ⥤ E where
  obj F := F.flip
  map {F₁ F₂} φ :=
    { app := fun Y =>
      { app := fun X => (φ.app X).app Y } }

namespace Iso

@[reassoc (attr := simp)]
/-
**CategoryTheory.Iso.map_hom_inv_id_app** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheor
y.Iso`。
形式化陈述：map_hom_inv_id_app {X Y : C} (e : X ≅ Y) (F : C ⥤ D ⥤ E) (Z : D) : (F.map 
e.hom).app Z ≫ (F.map e.inv).app Z = 𝟙 _
参数：e : X ≅ Y；F : C ⥤ D ⥤ E；Z : D。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem map_hom_inv_id_app {X Y : C} (e : X ≅ Y) (F : C ⥤ D ⥤ E) (Z : D) :
    (F.map e.hom).app Z ≫ (F.map e.inv).app Z = 𝟙 _ := by
  cat_disch

@[reassoc (attr := simp)]
/-
**CategoryTheory.Iso.map_inv_hom_id_app** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheor
y.Iso`。
形式化陈述：map_inv_hom_id_app {X Y : C} (e : X ≅ Y) (F : C ⥤ D ⥤ E) (Z : D) : (F.map 
e.inv).app Z ≫ (F.map e.hom).app Z = 𝟙 _
参数：e : X ≅ Y；F : C ⥤ D ⥤ E；Z : D。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem map_inv_hom_id_app {X Y : C} (e : X ≅ Y) (F : C ⥤ D ⥤ E) (Z : D) :
    (F.map e.inv).app Z ≫ (F.map e.hom).app Z = 𝟙 _ := by
  cat_disch

end Iso

/-- The natural transformation `G.flip.obj Y ⟶ G'.flip.obj Y` induced by
a natural transformation `τ : G ⟶ G'` between bifunctors. -/
/-
**CategoryTheory.NatTrans.flipApp** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.NatT
rans`。
形式化陈述：{C : Type u₁} →   [inst : CategoryTheory.Category.{v₁, u₁} C] →     {D : T
ype u₂} →       [inst_1 : CategoryTheory.Category.{v₂, u₂} D] →         {E : Typ
e u₃} →           [inst_2 : CategoryTheory.Category.{v₃, u₃} E] →             {G
 G' : CategoryTheory.Functor C (CategoryTheory.Functor D E)} →               (G 
⟶ G') → (Y : D) → G.flip.obj Y ⟶ G'.flip.obj Y
参数：CategoryTheory.Functor D E；G ⟶ G'；Y : D。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The natural transformation `G.flip.obj Y ⟶ G'.flip.obj Y` induced by
a natural transformation `τ : G ⟶ G'` between bifunctors.
-/
abbrev NatTrans.flipApp {G G' : C ⥤ D ⥤ E} (τ : G ⟶ G') (Y : D) :
    G.flip.obj Y ⟶ G'.flip.obj Y :=
  ((flipFunctor _ _ _).map τ).app Y

end CategoryTheory

