/-
Copyright (c) 2019 Reid Barton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Reid Barton, Kim Morrison
-/
module

public import Mathlib.CategoryTheory.Groupoid
public import Mathlib.CategoryTheory.CommSq

/-!
# Facts about epimorphisms and monomorphisms.

The definitions of `Epi` and `Mono` are in `CategoryTheory.Category`,
since they are used by some lemmas for `Iso`, which is used everywhere.
-/

@[expose] public section


universe v₁ v₂ u₁ u₂

namespace CategoryTheory

variable {C : Type u₁} [Category.{v₁} C]

@[to_dual unop_mono_of_epi]
/-
**CategoryTheory.unop_epi_of_mono** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory`。
形式化陈述：unop_epi_of_mono {A B : Cᵒᵖ} (f : A ⟶ B) [Mono f] : Epi f.unop
参数：f : A ⟶ B。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Quiver.Hom.op_inj`：Quiver.Hom.op_inj {X Y : C} : Function.Injective (Qui
ver.Hom.op : (X ⟶ Y) -> (Opposite.op Y ⟶ Opposite.op X))
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `CategoryTheory.cancel_mono`：∀ {C : Type u} [inst : CategoryTheory.Catego
ry.{v, u} C] {X Y Z : C} (f : Y ⟶ X) [CategoryTheory.Mono f] {g h : Z ⟶ Y},   Ca
tegoryTheory.Cat…
· 使用定理 `Quiver.Hom.unop_inj`：Quiver.Hom.unop_inj {X Y : Cᵒᵖ} : Function.Injectiv
e (Quiver.Hom.unop : (X ⟶ Y) -> (Opposite.unop Y ⟶ Opposite.unop X))
-/
instance unop_epi_of_mono {A B : Cᵒᵖ} (f : A ⟶ B) [Mono f] : Epi f.unop :=
  ⟨fun _ _ eq => Quiver.Hom.op_inj ((cancel_mono f).1 (Quiver.Hom.unop_inj eq))⟩

@[to_dual op_mono_of_epi]
/-
**CategoryTheory.op_epi_of_mono** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory`。
形式化陈述：op_epi_of_mono {A B : C} (f : A ⟶ B) [Mono f] : Epi f.op
参数：f : A ⟶ B。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Quiver.Hom.unop_inj`：Quiver.Hom.unop_inj {X Y : Cᵒᵖ} : Function.Injectiv
e (Quiver.Hom.unop : (X ⟶ Y) -> (Opposite.unop Y ⟶ Opposite.unop X))
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `CategoryTheory.cancel_mono`：∀ {C : Type u} [inst : CategoryTheory.Catego
ry.{v, u} C] {X Y Z : C} (f : Y ⟶ X) [CategoryTheory.Mono f] {g h : Z ⟶ Y},   Ca
tegoryTheory.Cat…
· 使用定理 `Quiver.Hom.op_inj`：Quiver.Hom.op_inj {X Y : C} : Function.Injective (Qui
ver.Hom.op : (X ⟶ Y) -> (Opposite.op Y ⟶ Opposite.op X))
-/
instance op_epi_of_mono {A B : C} (f : A ⟶ B) [Mono f] : Epi f.op :=
  ⟨fun _ _ eq => Quiver.Hom.unop_inj ((cancel_mono f).1 (Quiver.Hom.op_inj eq))⟩

@[to_dual (attr := simp)]
/-
**CategoryTheory.op_epi_iff** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory`。
形式化陈述：op_epi_iff {X Y : C} (f : X ⟶ Y) : Epi f.op ↔ Mono f
参数：f : X ⟶ Y。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.unop_mono_of_epi`：∀ {C : Type u₁} [inst : CategoryTheory.
Category.{v₁, u₁} C] {A B : Cᵒᵖ} (f : B ⟶ A) [CategoryTheory.Epi f],   CategoryT
heory.Mono f.unop
-/
lemma op_epi_iff {X Y : C} (f : X ⟶ Y) :
    Epi f.op ↔ Mono f :=
  ⟨fun _ ↦ unop_mono_of_epi f.op, fun _ ↦ inferInstance⟩

@[to_dual (attr := simp)]
/-
**CategoryTheory.unop_epi_iff** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory`。
形式化陈述：unop_epi_iff {X Y : Cᵒᵖ} (f : X ⟶ Y) : Epi f.unop ↔ Mono f
参数：f : X ⟶ Y。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.op_mono_of_epi`：∀ {C : Type u₁} [inst : CategoryTheory.Ca
tegory.{v₁, u₁} C] {A B : C} (f : B ⟶ A) [CategoryTheory.Epi f],   CategoryTheor
y.Mono f.op
-/
lemma unop_epi_iff {X Y : Cᵒᵖ} (f : X ⟶ Y) :
    Epi f.unop ↔ Mono f :=
  ⟨fun _ ↦ op_mono_of_epi f.unop, fun _ ↦ inferInstance⟩

/-- A split monomorphism is a morphism `f : X ⟶ Y` with a given retraction `retraction f : Y ⟶ X`
such that `f ≫ retraction f = 𝟙 X`.

Every split monomorphism is a monomorphism.
-/
/-
**CategoryTheory.SplitMono** 是 Mathlib 中的一个结构，位于命名空间 `CategoryTheory`。
形式化陈述：SplitMono {X Y : C} (f : X ⟶ Y) where /-- The map splitting `f` -/ retract
ion : Y ⟶ X /-- `f` composed with `retraction` is the identity -/ id : f ≫ retra
ction = 𝟙 X
参数：f : X ⟶ Y。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A split monomorphism is a morphism `f : X ⟶ Y` with a given retraction `retracti
on f : Y ⟶ X`
such that `f ≫ retraction f = 𝟙 X`.

Every split monomorphism is a monomorphism.
-/
structure SplitMono {X Y : C} (f : X ⟶ Y) where
  /-- The map splitting `f` -/
  retraction : Y ⟶ X
  /-- `f` composed with `retraction` is the identity -/
  id : f ≫ retraction = 𝟙 X := by cat_disch

/-- `IsSplitMono f` is the assertion that `f` admits a retraction -/
/-
**CategoryTheory.IsSplitMono** 是 Mathlib 中的一个归纳类型，位于命名空间 `CategoryTheory`。
形式化陈述：{C : Type u₁} → [inst : CategoryTheory.Category.{v₁, u₁} C] → {X Y : C} → 
(X ⟶ Y) → Prop
参数：X ⟶ Y。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`IsSplitMono f` is the assertion that `f` admits a retraction
-/
class IsSplitMono {X Y : C} (f : X ⟶ Y) : Prop where
  /-- There is a splitting -/
  exists_splitMono : Nonempty (SplitMono f)

/-- A split epimorphism is a morphism `f : X ⟶ Y` with a given section `section_ f : Y ⟶ X`
such that `section_ f ≫ f = 𝟙 Y`.
(Note that `section` is a reserved keyword, so we append an underscore.)

Every split epimorphism is an epimorphism.
-/
@[to_dual (attr := ext, aesop apply safe (rule_sets := [CategoryTheory]))]
/-
**CategoryTheory.SplitEpi** 是 Mathlib 中的一个归纳类型，位于命名空间 `CategoryTheory`。
形式化陈述：{C : Type u₁} → [inst : CategoryTheory.Category.{v₁, u₁} C] → {X Y : C} → 
(X ⟶ Y) → Type v₁
参数：X ⟶ Y。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A split epimorphism is a morphism `f : X ⟶ Y` with a given section `section_ f :
 Y ⟶ X`
such that `section_ f ≫ f = 𝟙 Y`.
(Note that `section` is a reserved keyword, so we append an underscore.)

Every split epimorphism is an epimorphism.
-/
structure SplitEpi {X Y : C} (f : X ⟶ Y) where
  /-- The map splitting `f` -/
  section_ : Y ⟶ X
  /-- `section_` composed with `f` is the identity -/
  id : section_ ≫ f = 𝟙 Y := by cat_disch

-- TODO: `to_dual` should add these automatically:
attribute [to_dual existing] SplitEpi.ext SplitEpi.ext_iff

/-- `IsSplitEpi f` is the assertion that `f` admits a section -/
@[to_dual]
/-
**CategoryTheory.IsSplitEpi** 是 Mathlib 中的一个类，位于命名空间 `CategoryTheory`。
形式化陈述：IsSplitEpi {X Y : C} (f : X ⟶ Y) : Prop where /-- There is a splitting -/ 
exists_splitEpi : Nonempty (SplitEpi f)  attribute [reassoc (attr
参数：f : X ⟶ Y。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`IsSplitEpi f` is the assertion that `f` admits a section
-/
class IsSplitEpi {X Y : C} (f : X ⟶ Y) : Prop where
  /-- There is a splitting -/
  exists_splitEpi : Nonempty (SplitEpi f)

attribute [reassoc (attr := simp)] SplitMono.id SplitEpi.id

/-- A composition of `SplitEpi` is a split `SplitEpi`. -/
@[to_dual (attr := simps) (reorder := X Z, f g, sef seg) (rename := f ↔ g, sef → smg, seg → smf)
/-- A composition of `SplitMono` is a `SplitMono`. -/]
/-
**CategoryTheory.SplitEpi.comp** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.SplitEp
i`。
形式化陈述：{C : Type u₁} →   [inst : CategoryTheory.Category.{v₁, u₁} C] →     {X Y Z
 : C} →       {f : X ⟶ Y} →         {g : Y ⟶ Z} →           CategoryTheory.Split
Epi f →             CategoryTheory.SplitEpi g → CategoryTheory.SplitEpi (Categor
yTheory.CategoryStruct.comp f g)
参数：CategoryTheory.CategoryStruct.comp f g。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def SplitEpi.comp {X Y Z : C} {f : X ⟶ Y} {g : Y ⟶ Z} (sef : SplitEpi f) (seg : SplitEpi g) :
    SplitEpi (f ≫ g) where
  section_ := seg.section_ ≫ sef.section_

/-- A constructor for `IsSplitEpi f` taking a `SplitEpi f` as an argument -/
@[to_dual /-- A constructor for `IsSplitMono f` taking a `SplitMono f` as an argument -/]
/-
**CategoryTheory.IsSplitEpi.mk'** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.IsSpli
tEpi`。
形式化陈述：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {X Y : C} {f :
 X ⟶ Y} (se : CategoryTheory.SplitEpi f),   CategoryTheory.IsSplitEpi f
参数：se : CategoryTheory.SplitEpi f。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A constructor for `IsSplitEpi f` taking a `SplitEpi f` as an argument
-/
theorem IsSplitEpi.mk' {X Y : C} {f : X ⟶ Y} (se : SplitEpi f) : IsSplitEpi f :=
  ⟨Nonempty.intro se⟩

/-- The chosen section of a split epimorphism.
(Note that `section` is a reserved keyword, so we append an underscore.)
-/
@[to_dual retraction /-- The chosen retraction of a split monomorphism. -/]
/-
**CategoryTheory.section_** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory`。
形式化陈述：section_ {X Y : C} (f : X ⟶ Y) [hf : IsSplitEpi f] : Y ⟶ X
参数：f : X ⟶ Y。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.IsSplitEpi.exists_splitEpi`：∀ {C : Type u₁} {inst : Categ
oryTheory.Category.{v₁, u₁} C} {X Y : C} {f : X ⟶ Y} [self : CategoryTheory.IsSp
litEpi f],   Nonempty (Category…

--- 原说明 ---
The chosen section of a split epimorphism.
(Note that `section` is a reserved keyword, so we append an underscore.)
-/
noncomputable def section_ {X Y : C} (f : X ⟶ Y) [hf : IsSplitEpi f] : Y ⟶ X :=
  hf.exists_splitEpi.some.section_

@[to_dual (attr := reassoc (attr := simp))]
/-
**CategoryTheory.IsSplitEpi.id** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.IsSplit
Epi`。
形式化陈述：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {X Y : C} (f :
 X ⟶ Y) [hf : CategoryTheory.IsSplitEpi f],   CategoryTheory.CategoryStruct.comp
 (CategoryTheory.section_ f) f = CategoryTheory.CategoryStruct.id Y
参数：f : X ⟶ Y；CategoryTheory.section_ f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.SplitEpi.id`：∀ {C : Type u₁} [inst : CategoryTheory.Categ
ory.{v₁, u₁} C] {X Y : C} {f : X ⟶ Y} (self : CategoryTheory.SplitEpi f),   Cate
goryTheory.Categ…
· 使用定理 `CategoryTheory.IsSplitEpi.exists_splitEpi`：∀ {C : Type u₁} {inst : Categ
oryTheory.Category.{v₁, u₁} C} {X Y : C} {f : X ⟶ Y} [self : CategoryTheory.IsSp
litEpi f],   Nonempty (Category…
-/
theorem IsSplitEpi.id {X Y : C} (f : X ⟶ Y) [hf : IsSplitEpi f] : section_ f ≫ f = 𝟙 Y :=
  hf.exists_splitEpi.some.id

/-- The section of a split epimorphism has an obvious retraction. -/
@[to_dual splitEpi /-- The retraction of a split monomorphism has an obvious section. -/]
/-
**CategoryTheory.SplitEpi.splitMono** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Sp
litEpi`。
形式化陈述：{C : Type u₁} →   [inst : CategoryTheory.Category.{v₁, u₁} C] →     {X Y :
 C} → {f : X ⟶ Y} → (se : CategoryTheory.SplitEpi f) → CategoryTheory.SplitMono 
se.section_
参数：se : CategoryTheory.SplitEpi f。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The section of a split epimorphism has an obvious retraction.
-/
def SplitEpi.splitMono {X Y : C} {f : X ⟶ Y} (se : SplitEpi f) : SplitMono se.section_ where
  retraction := f

/-- The section of a split epimorphism is itself a split monomorphism. -/
@[to_dual retraction_isSplitEpi
/-- The retraction of a split monomorphism is itself a split epimorphism. -/]
/-
**CategoryTheory.section_isSplitMono** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory`。
形式化陈述：section_isSplitMono {X Y : C} (f : X ⟶ Y) [IsSplitEpi f] : IsSplitMono (se
ction_ f)
参数：f : X ⟶ Y。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.IsSplitMono.mk'`：∀ {C : Type u₁} [inst : CategoryTheory.C
ategory.{v₁, u₁} C] {X Y : C} {f : Y ⟶ X} (se : CategoryTheory.SplitMono f),   C
ategoryTheory.IsSpli…
· 使用定理 `CategoryTheory.IsSplitEpi.exists_splitEpi`：∀ {C : Type u₁} {inst : Categ
oryTheory.Category.{v₁, u₁} C} {X Y : C} {f : X ⟶ Y} [self : CategoryTheory.IsSp
litEpi f],   Nonempty (Category…
-/
instance section_isSplitMono {X Y : C} (f : X ⟶ Y) [IsSplitEpi f] : IsSplitMono (section_ f) :=
  IsSplitMono.mk' (SplitEpi.splitMono _)

/-- A split epi which is mono is an iso. -/
@[to_dual isIso_of_epi_of_isSplitMono /-- A split mono which is epi is an iso. -/]
/-
**CategoryTheory.isIso_of_mono_of_isSplitEpi** 是 Mathlib 中的一个定理，位于命名空间 `Category
Theory`。
形式化陈述：isIso_of_mono_of_isSplitEpi {X Y : C} (f : X ⟶ Y) [Mono f] [IsSplitEpi f] 
: IsIso f
参数：f : X ⟶ Y。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.cancel_mono`：∀ {C : Type u} [inst : CategoryTheory.Catego
ry.{v, u} C] {X Y Z : C} (f : Y ⟶ X) [CategoryTheory.Mono f] {g h : Z ⟶ Y},   Ca
tegoryTheory.Cat…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.IsSplitEpi.id`：∀ {C : Type u₁} [inst : CategoryTheory.Cat
egory.{v₁, u₁} C] {X Y : C} (f : X ⟶ Y) [hf : CategoryTheory.IsSplitEpi f],   Ca
tegoryTheory.Categ…
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a

--- 原说明 ---
A split epi which is mono is an iso.
-/
theorem isIso_of_mono_of_isSplitEpi {X Y : C} (f : X ⟶ Y) [Mono f] [IsSplitEpi f] : IsIso f :=
  ⟨⟨section_ f, ⟨by simp [← cancel_mono f], by simp⟩⟩⟩

/-- Every iso is a split epi. -/
@[to_dual /-- Every iso is a split mono. -/]
/-
**CategoryTheory.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Every iso is a split epi.
-/
instance (priority := 100) IsSplitEpi.of_iso {X Y : C} (f : X ⟶ Y) [IsIso f] : IsSplitEpi f :=
  IsSplitEpi.mk' { section_ := inv f }

@[to_dual]
/-
**CategoryTheory.SplitEpi.epi** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.SplitEpi
`。
形式化陈述：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {X Y : C} {f :
 X ⟶ Y} (se : CategoryTheory.SplitEpi f),   CategoryTheory.Epi f
参数：se : CategoryTheory.SplitEpi f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.whisker_eq`：∀ {C : Type u} [inst : CategoryTheory.Categor
y.{v, u} C] {X Y Z : C} {f g : Y ⟶ X} (h : Z ⟶ Y),   f = g → CategoryTheory.Cate
goryStruct.comp…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.SplitEpi.id_assoc`：∀ {C : Type u₁} [inst : CategoryTheory
.Category.{v₁, u₁} C] {X Y : C} {f : X ⟶ Y} (self : CategoryTheory.SplitEpi f)  
 {Z : C} (h : Y ⟶ Z), …
-/
theorem SplitEpi.epi {X Y : C} {f : X ⟶ Y} (se : SplitEpi f) : Epi f :=
  { left_cancellation := fun g h w => by replace w := se.section_ ≫= w; simpa using w }

/-- Every split epi is an epi. -/
@[to_dual /-- Every split mono is a mono. -/]
/-
**CategoryTheory.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Every split epi is an epi.
-/
instance (priority := 100) IsSplitEpi.epi {X Y : C} (f : X ⟶ Y) [hf : IsSplitEpi f] : Epi f :=
  hf.exists_splitEpi.some.epi

@[to_dual]
/-
**CategoryTheory.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {X Y Z : C} {f : X ⟶ Y} {g : Y ⟶ Z} [hf : IsSplitEpi f] [hg : IsSplitEpi g] :
    IsSplitEpi (f ≫ g) := IsSplitEpi.mk' <| hf.exists_splitEpi.some.comp hg.exists_splitEpi.some

/-- Every split epi whose section is epi is an iso. -/
@[to_dual /-- Every split mono whose retraction is mono is an iso. -/]
/-
**CategoryTheory.IsIso.of_epi_section'** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory
.IsIso`。
形式化陈述：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {X Y : C} {f :
 X ⟶ Y} (hf : CategoryTheory.SplitEpi f)   [CategoryTheory.Epi hf.section_], Cat
egoryTheory.IsIso f
参数：hf : CategoryTheory.SplitEpi f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `CategoryTheory.cancel_epi_id`：cancel_epi_id (f : X ⟶ Y) [Epi f] {h : Y ⟶
 Y} : f ≫ h = f ↔ h = 𝟙 Y
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.SplitEpi.id_assoc`：∀ {C : Type u₁} [inst : CategoryTheory
.Category.{v₁, u₁} C] {X Y : C} {f : X ⟶ Y} (self : CategoryTheory.SplitEpi f)  
 {Z : C} (h : Y ⟶ Z), …
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `CategoryTheory.SplitEpi.id`：∀ {C : Type u₁} [inst : CategoryTheory.Categ
ory.{v₁, u₁} C] {X Y : C} {f : X ⟶ Y} (self : CategoryTheory.SplitEpi f),   Cate
goryTheory.Categ…

--- 原说明 ---
Every split epi whose section is epi is an iso.
-/
theorem IsIso.of_epi_section' {X Y : C} {f : X ⟶ Y} (hf : SplitEpi f) [Epi <| hf.section_] :
    IsIso f :=
  ⟨⟨hf.section_, ⟨(cancel_epi_id <| hf.section_).mp (by simp), by simp⟩⟩⟩

/-- Every split epi whose section is epi is an iso. -/
@[to_dual /-- Every split mono whose retraction is mono is an iso. -/]
/-
**CategoryTheory.IsIso.of_epi_section** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.
IsIso`。
形式化陈述：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {X Y : C} (f :
 X ⟶ Y) [hf : CategoryTheory.IsSplitEpi f]   [hf' : CategoryTheory.Epi (Category
Theory.section_ f)], CategoryTheory.IsIso f
参数：f : X ⟶ Y；CategoryTheory.section_ f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.IsIso.of_epi_section'`：∀ {C : Type u₁} [inst : CategoryTh
eory.Category.{v₁, u₁} C] {X Y : C} {f : X ⟶ Y} (hf : CategoryTheory.SplitEpi f)
   [CategoryTheory.Epi hf.…
· 使用定理 `CategoryTheory.IsSplitEpi.exists_splitEpi`：∀ {C : Type u₁} {inst : Categ
oryTheory.Category.{v₁, u₁} C} {X Y : C} {f : X ⟶ Y} [self : CategoryTheory.IsSp
litEpi f],   Nonempty (Category…

--- 原说明 ---
Every split epi whose section is epi is an iso.
-/
theorem IsIso.of_epi_section {X Y : C} (f : X ⟶ Y) [hf : IsSplitEpi f] [hf' : Epi <| section_ f] :
    IsIso f :=
  @IsIso.of_epi_section' _ _ _ _ _ hf.exists_splitEpi.some hf'

-- FIXME this has unnecessarily become noncomputable!
/-- A category where every morphism has a `Trunc` retraction is computably a groupoid. -/
@[instance_reducible]
/-
**CategoryTheory.Groupoid.ofTruncSplitMono** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTh
eory.Groupoid`。
形式化陈述：{C : Type u₁} →   [inst : CategoryTheory.Category.{v₁, u₁} C] →     (∀ {X 
Y : C} (f : X ⟶ Y), Trunc (CategoryTheory.IsSplitMono f)) → CategoryTheory.Group
oid C
参数：∀ {X Y : C} (f : X ⟶ Y), Trunc (CategoryTheory.IsSplitMono f)。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A category where every morphism has a `Trunc` retraction is computably a groupoi
d.
-/
noncomputable def Groupoid.ofTruncSplitMono
    (all_split_mono : ∀ {X Y : C} (f : X ⟶ Y), Trunc (IsSplitMono f)) : Groupoid.{v₁} C := by
  apply Groupoid.ofIsIso
  intro X Y f
  have ⟨a,_⟩ := Trunc.exists_rep <| all_split_mono f
  have ⟨b,_⟩ := Trunc.exists_rep <| all_split_mono <| retraction f
  apply IsIso.of_mono_retraction

section

variable (C)

/-- A split mono category is a category in which every monomorphism is split. -/
/-
**CategoryTheory.SplitMonoCategory** 是 Mathlib 中的一个归纳类型，位于命名空间 `CategoryTheory`。
形式化陈述：(C : Type u₁) → [CategoryTheory.Category.{v₁, u₁} C] → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A split mono category is a category in which every monomorphism is split.
-/
class SplitMonoCategory : Prop where
  /-- All monos are split -/
  isSplitMono_of_mono : ∀ {X Y : C} (f : X ⟶ Y) [Mono f], IsSplitMono f

/-- A split epi category is a category in which every epimorphism is split. -/
@[to_dual]
/-
**CategoryTheory.SplitEpiCategory** 是 Mathlib 中的一个归纳类型，位于命名空间 `CategoryTheory`。
形式化陈述：(C : Type u₁) → [CategoryTheory.Category.{v₁, u₁} C] → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A split epi category is a category in which every epimorphism is split.
-/
class SplitEpiCategory : Prop where
  /-- All epis are split -/
  isSplitEpi_of_epi : ∀ {X Y : C} (f : X ⟶ Y) [Epi f], IsSplitEpi f

end

/-- In a category in which every epimorphism is split, every epimorphism splits. This is not an
/-
**CategoryTheory.because** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance because it would create an instance loop. -/
@[to_dual
/-- In a category in which every monomorphism is split, every monomorphism splits. This is not an
/-
**CategoryTheory.because** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance because it would create an instance loop. -/]
/-
**CategoryTheory.isSplitEpi_of_epi** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory`。
形式化陈述：isSplitEpi_of_epi [SplitEpiCategory C] {X Y : C} (f : X ⟶ Y) [Epi f] : IsS
plitEpi f
参数：f : X ⟶ Y。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.SplitEpiCategory.isSplitEpi_of_epi`：∀ {C : Type u₁} {inst
 : CategoryTheory.Category.{v₁, u₁} C} [self : CategoryTheory.SplitEpiCategory C
] {X Y : C}   (f : X ⟶ Y) [CategoryTheo…
-/
theorem isSplitEpi_of_epi [SplitEpiCategory C] {X Y : C} (f : X ⟶ Y) [Epi f] : IsSplitEpi f :=
  SplitEpiCategory.isSplitEpi_of_epi _

section

variable {D : Type u₂} [Category.{v₂} D]

/-- Split epimorphisms are also absolute epimorphisms. -/
@[to_dual (attr := simps) /-- Split monomorphisms are also absolute monomorphisms. -/]
/-
**CategoryTheory.SplitEpi.map** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.SplitEpi
`。
形式化陈述：{C : Type u₁} →   [inst : CategoryTheory.Category.{v₁, u₁} C] →     {D : T
ype u₂} →       [inst_1 : CategoryTheory.Category.{v₂, u₂} D] →         {X Y : C
} →           {f : X ⟶ Y} → CategoryTheory.SplitEpi f → (F : CategoryTheory.Func
tor C D) → CategoryTheory.SplitEpi (F.map f)
参数：F : CategoryTheory.Functor C D；F.map f。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Split epimorphisms are also absolute epimorphisms.
-/
def SplitEpi.map {X Y : C} {f : X ⟶ Y} (se : SplitEpi f) (F : C ⥤ D) : SplitEpi (F.map f) where
  section_ := F.map se.section_
  id := by rw [← Functor.map_comp, SplitEpi.id, Functor.map_id]

@[to_dual]
/-
**CategoryTheory.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {X Y : C} (f : X ⟶ Y) [hf : IsSplitEpi f] (F : C ⥤ D) : IsSplitEpi (F.map f) :=
  IsSplitEpi.mk' (hf.exists_splitEpi.some.map F)

end

section

/-- When `f` is an epimorphism, `f ≫ g` is epic iff `g` is. -/
@[to_dual (attr := simp) (reorder := g f 7)
/-- When `g` is a monomorphism, `f ≫ g` is monic iff `f` is. -/]
/-
**CategoryTheory.epi_comp_iff_of_epi** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory`。
形式化陈述：epi_comp_iff_of_epi {X Y Z : C} (f : X ⟶ Y) [Epi f] (g : Y ⟶ Z) : Epi (f ≫
 g) ↔ Epi g
参数：f : X ⟶ Y；g : Y ⟶ Z。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.epi_of_epi`：epi_of_epi (f : X ⟶ Y) (g : Y ⟶ Z) [Epi (f ≫ 
g)] : Epi g
-/
lemma epi_comp_iff_of_epi {X Y Z : C} (f : X ⟶ Y) [Epi f] (g : Y ⟶ Z) :
    Epi (f ≫ g) ↔ Epi g :=
  ⟨fun _ ↦ epi_of_epi f _, fun _ ↦ inferInstance⟩

/-- When `g` is an isomorphism, `f ≫ g` is epic iff `f` is. -/
@[to_dual (attr := simp) (reorder := g f 8)
/-- When `f` is an isomorphism, `f ≫ g` is monic iff `g` is. -/]
/-
**CategoryTheory.epi_comp_iff_of_isIso** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory
`。
形式化陈述：epi_comp_iff_of_isIso {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) [IsIso g] : Epi 
(f ≫ g) ↔ Epi f
参数：f : X ⟶ Y；g : Y ⟶ Z。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.IsIso.hom_inv_id`：hom_inv_id (f : X ⟶ Y) [I : IsIso f] : 
f ≫ inv f = 𝟙 X
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `CategoryTheory.IsSplitEpi.epi`：∀ {C : Type u₁} [inst : CategoryTheory.Ca
tegory.{v₁, u₁} C] {X Y : C} (f : X ⟶ Y) [hf : CategoryTheory.IsSplitEpi f],   C
ategoryTheory.Epi f
· 使用定理 `CategoryTheory.IsSplitEpi.of_iso`：∀ {C : Type u₁} [inst : CategoryTheory
.Category.{v₁, u₁} C] {X Y : C} (f : X ⟶ Y) [CategoryTheory.IsIso f],   Category
Theory.IsSplitEpi f
-/
lemma epi_comp_iff_of_isIso {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) [IsIso g] :
    Epi (f ≫ g) ↔ Epi f := by
  refine ⟨fun h ↦ ?_, fun h ↦ inferInstance⟩
  simpa using (inferInstance : Epi ((f ≫ g) ≫ inv g))

end

section Opposite

variable {X Y : C} {f : X ⟶ Y}

/-- The opposite of a split epi is a split mono. -/
@[to_dual /-- The opposite of a split mono is a split epi. -/]
/-
**CategoryTheory.SplitEpi.op** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.SplitEpi`
。
形式化陈述：{C : Type u₁} →   [inst : CategoryTheory.Category.{v₁, u₁} C] →     {X Y :
 C} → {f : X ⟶ Y} → CategoryTheory.SplitEpi f → CategoryTheory.SplitMono f.op
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The opposite of a split epi is a split mono.
-/
def SplitEpi.op (h : SplitEpi f) : SplitMono f.op where
  retraction := h.section_.op
  id := Quiver.Hom.unop_inj (by simp)

@[to_dual]
/-
**CategoryTheory.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [IsSplitMono f] : IsSplitEpi f.op :=
  .mk' IsSplitMono.exists_splitMono.some.op

end Opposite


section cubeLemma

variable {M000 M001 M010 M011 M100 M101 M110 M111 : C}
  (f00x : M000 ⟶ M001) (f01x : M010 ⟶ M011) (f10x : M100 ⟶ M101) (f11x : M110 ⟶ M111)
  (f0x0 : M000 ⟶ M010) (f0x1 : M001 ⟶ M011) (f1x0 : M100 ⟶ M110) (f1x1 : M101 ⟶ M111)
  (fx00 : M000 ⟶ M100) (fx01 : M001 ⟶ M101) (fx10 : M010 ⟶ M110) (fx11 : M011 ⟶ M111)

/-- This is a theorem saying if five faces of a cube commute and one edge is an epimorphism,
  then the sixth face must also commute. -/
/-
**CategoryTheory.cube_lemma_of_epi** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory`。
形式化陈述：cube_lemma_of_epi (h0xx : f0x0 ≫ f01x = f00x ≫ f0x1) (h1xx : f1x0 ≫ f11x =
 f10x ≫ f1x1) (hx0x : fx00 ≫ f10x = f00x ≫ fx01) (hx1x : fx10 ≫ f11x = f01x ≫ fx
11) (hxx0 : f0x0 ≫ fx10 = fx00 ≫ f1x0) [Epi f00x] : f0x1 ≫ fx11 = fx01 ≫ f1x1
参数：h0xx : f0x0 ≫ f01x = f00x ≫ f0x1；h1xx : f1x0 ≫ f11x = f10x ≫ f1x1；hx0x : fx00
 ≫ f10x = f00x ≫ fx01；hx1x : fx10 ≫ f11x = f01x ≫ fx11；hxx0 : f0x0 ≫ fx10 = fx00
 ≫ f1x0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.cancel_epi`：cancel_epi (f : X ⟶ Y) [Epi f] {g h : Y ⟶ Z} 
: f ≫ g = f ≫ h ↔ g = h

--- 原说明 ---
This is a theorem saying if five faces of a cube commute and one edge is an epim
orphism,
  then the sixth face must also commute.
-/
theorem cube_lemma_of_epi (h0xx : f0x0 ≫ f01x = f00x ≫ f0x1) (h1xx : f1x0 ≫ f11x = f10x ≫ f1x1)
    (hx0x : fx00 ≫ f10x = f00x ≫ fx01) (hx1x : fx10 ≫ f11x = f01x ≫ fx11)
    (hxx0 : f0x0 ≫ fx10 = fx00 ≫ f1x0) [Epi f00x] : f0x1 ≫ fx11 = fx01 ≫ f1x1 := by
  rw [← cancel_epi f00x]
  grind

/-- This is a theorem saying if five faces of a cube commute and one edge is a monomorphism,
  then the sixth face must also commute. -/
/-
**CategoryTheory.cube_lemma_of_mono** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory`。
形式化陈述：cube_lemma_of_mono (h0xx : f0x0 ≫ f01x = f00x ≫ f0x1) (h1xx : f1x0 ≫ f11x 
= f10x ≫ f1x1) (hx0x : fx00 ≫ f10x = f00x ≫ fx01) (hx1x : fx10 ≫ f11x = f01x ≫ f
x11) (hxx1 : f0x1 ≫ fx11 = fx01 ≫ f1x1) [Mono f11x] : f0x0 ≫ fx10 = fx00 ≫ f1x0
参数：h0xx : f0x0 ≫ f01x = f00x ≫ f0x1；h1xx : f1x0 ≫ f11x = f10x ≫ f1x1；hx0x : fx00
 ≫ f10x = f00x ≫ fx01；hx1x : fx10 ≫ f11x = f01x ≫ fx11；hxx1 : f0x1 ≫ fx11 = fx01
 ≫ f1x1。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.cancel_mono`：∀ {C : Type u} [inst : CategoryTheory.Catego
ry.{v, u} C] {X Y Z : C} (f : Y ⟶ X) [CategoryTheory.Mono f] {g h : Z ⟶ Y},   Ca
tegoryTheory.Cat…

--- 原说明 ---
This is a theorem saying if five faces of a cube commute and one edge is a monom
orphism,
  then the sixth face must also commute.
-/
theorem cube_lemma_of_mono (h0xx : f0x0 ≫ f01x = f00x ≫ f0x1) (h1xx : f1x0 ≫ f11x = f10x ≫ f1x1)
    (hx0x : fx00 ≫ f10x = f00x ≫ fx01) (hx1x : fx10 ≫ f11x = f01x ≫ fx11)
    (hxx1 : f0x1 ≫ fx11 = fx01 ≫ f1x1) [Mono f11x] : f0x0 ≫ fx10 = fx00 ≫ f1x0 := by
  rw [← cancel_mono f11x]
  grind
/-
**CategoryTheory.CommSq.cube_lemma_of_epi** 是 Mathlib 中的一个定理，位于命名空间 `CategoryThe
ory.CommSq`。
形式化陈述：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {M000 M001 M01
0 M011 M100 M101 M110 M111 : C}   (f00x : M000 ⟶ M001) (f01x : M010 ⟶ M011) (f10
x : M100 ⟶ M101) (f11x : M110 ⟶ M111) (f0x0 : M000 ⟶ M010)   (f0x1 : M001 ⟶ M011
) (f1x0 : M100 ⟶ M110) (f1x1 : M101 ⟶ M111) (fx00 : M000 ⟶ M100) (fx01 : M001 ⟶ 
M101)   (fx10 : M010 ⟶ M110) (fx11 : M011 ⟶ M111),   CategoryTheory.CommSq f0x0 
f00x f01x f0x1 →     CategoryTheory.CommSq f1x0 f10x f11x f1x1 →       CategoryT
heory.CommSq fx00 f00x f10x fx01 →         CategoryTheory.CommSq fx10 f01x f11x 
fx11 →           CategoryTheory.CommSq f0x0 fx00 fx10 f1x0 →             ∀ [Cate
goryTheory.Epi f00x], CategoryTheory.CommSq f0x1 fx01 fx11 f1x1
参数：f00x : M000 ⟶ M001；f01x : M010 ⟶ M011；f10x : M100 ⟶ M101；f11x : M110 ⟶ M111；f
0x0 : M000 ⟶ M010；f0x1 : M001 ⟶ M011；f1x0 : M100 ⟶ M110；f1x1 : M101 ⟶ M111；fx00 
: M000 ⟶ M100；fx01 : M001 ⟶ M101；fx10 : M010 ⟶ M110；fx11 : M011 ⟶ M111。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.cube_lemma_of_epi`：cube_lemma_of_epi (h0xx : f0x0 ≫ f01x 
= f00x ≫ f0x1) (h1xx : f1x0 ≫ f11x = f10x ≫ f1x1) (hx0x : fx00 ≫ f10x = f00x ≫ f
x01) (hx1x : fx10 ≫ f1…
· 使用定理 `CategoryTheory.CommSq.w`：∀ {C : Type u_1} [inst : CategoryTheory.Categor
y.{v_1, u_1} C] {W X Y Z : C} {f : W ⟶ X} {g : W ⟶ Y} {h : X ⟶ Z}   {i : Y ⟶ Z},
   CategoryTh…
-/
theorem CommSq.cube_lemma_of_epi (h0xx : CommSq f0x0 f00x f01x f0x1)
    (h1xx : CommSq f1x0 f10x f11x f1x1) (hx0x : CommSq fx00 f00x f10x fx01)
    (hx1x : CommSq fx10 f01x f11x fx11) (hxx0 : CommSq f0x0 fx00 fx10 f1x0) [Epi f00x] :
    CommSq f0x1 fx01 fx11 f1x1 :=
  ⟨CategoryTheory.cube_lemma_of_epi f00x f01x f10x f11x
      f0x0 f0x1 f1x0 f1x1 fx00 fx01 fx10 fx11 h0xx.w h1xx.w hx0x.w hx1x.w hxx0.w⟩
/-
**CategoryTheory.CommSq.cube_lemma_of_mono** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTh
eory.CommSq`。
形式化陈述：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {M000 M001 M01
0 M011 M100 M101 M110 M111 : C}   (f00x : M000 ⟶ M001) (f01x : M010 ⟶ M011) (f10
x : M100 ⟶ M101) (f11x : M110 ⟶ M111) (f0x0 : M000 ⟶ M010)   (f0x1 : M001 ⟶ M011
) (f1x0 : M100 ⟶ M110) (f1x1 : M101 ⟶ M111) (fx00 : M000 ⟶ M100) (fx01 : M001 ⟶ 
M101)   (fx10 : M010 ⟶ M110) (fx11 : M011 ⟶ M111),   CategoryTheory.CommSq f0x0 
f00x f01x f0x1 →     CategoryTheory.CommSq f1x0 f10x f11x f1x1 →       CategoryT
heory.CommSq fx00 f00x f10x fx01 →         CategoryTheory.CommSq fx10 f01x f11x 
fx11 →           CategoryTheory.CommSq f0x1 fx01 fx11 f1x1 →             ∀ [Cate
goryTheory.Mono f11x], CategoryTheory.CommSq f0x0 fx00 fx10 f1x0
参数：f00x : M000 ⟶ M001；f01x : M010 ⟶ M011；f10x : M100 ⟶ M101；f11x : M110 ⟶ M111；f
0x0 : M000 ⟶ M010；f0x1 : M001 ⟶ M011；f1x0 : M100 ⟶ M110；f1x1 : M101 ⟶ M111；fx00 
: M000 ⟶ M100；fx01 : M001 ⟶ M101；fx10 : M010 ⟶ M110；fx11 : M011 ⟶ M111。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.cube_lemma_of_mono`：cube_lemma_of_mono (h0xx : f0x0 ≫ f01
x = f00x ≫ f0x1) (h1xx : f1x0 ≫ f11x = f10x ≫ f1x1) (hx0x : fx00 ≫ f10x = f00x ≫
 fx01) (hx1x : fx10 ≫ f…
· 使用定理 `CategoryTheory.CommSq.w`：∀ {C : Type u_1} [inst : CategoryTheory.Categor
y.{v_1, u_1} C] {W X Y Z : C} {f : W ⟶ X} {g : W ⟶ Y} {h : X ⟶ Z}   {i : Y ⟶ Z},
   CategoryTh…
-/
theorem CommSq.cube_lemma_of_mono (h0xx : CommSq f0x0 f00x f01x f0x1)
    (h1xx : CommSq f1x0 f10x f11x f1x1) (hx0x : CommSq fx00 f00x f10x fx01)
    (hx1x : CommSq fx10 f01x f11x fx11) (hxx1 : CommSq f0x1 fx01 fx11 f1x1) [Mono f11x] :
    CommSq f0x0 fx00 fx10 f1x0 :=
  ⟨CategoryTheory.cube_lemma_of_mono f00x f01x f10x f11x
      f0x0 f0x1 f1x0 f1x1 fx00 fx01 fx10 fx11 h0xx.w h1xx.w hx0x.w hx1x.w hxx1.w⟩

end cubeLemma

end CategoryTheory

