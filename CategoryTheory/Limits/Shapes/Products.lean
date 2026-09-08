/-
Copyright (c) 2018 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison, Bhavik Mehta
-/
module

public import Mathlib.CategoryTheory.Limits.HasLimits

/-!
# Categorical (co)products

This file defines (co)products as special cases of (co)limits.

A product is the categorical generalization of the object `Π i, f i` where `f : ι → C`. It is a
limit cone over the diagram formed by `f`, implemented by converting `f` into a functor
`Discrete ι ⥤ C`.

A coproduct is the dual concept.

## Main definitions

* a `Fan` is a cone over a discrete category
* `Fan.mk` constructs a fan from an indexed collection of maps
* a `Pi` is a `limit (Discrete.functor f)`

Each of these has a dual.

## Implementation notes
As with the other special shapes in the limits library, all the definitions here are given as
`abbrev`s of the general statements for limits, so all the `simp` lemmas and theorems about
general limits can be used.
-/

@[expose] public section

noncomputable section

universe w w' w₂ w₃ v v₂ u u₂

open CategoryTheory

namespace CategoryTheory.Limits

variable {β : Type w} {α : Type w₂} {γ : Type w₃}
variable {C : Type u} [Category.{v} C]

-- We don't need an analogue of `Pair` (for binary products), `ParallelPair` (for equalizers),
-- or `(Co)span`, since we already have `Discrete.functor`.

/-- A fan over `f : β → C` consists of a collection of maps from an object `P` to every `f b`. -/
/-
**CategoryTheory.Limits.Fan** 是 Mathlib 中的一个缩写定义，位于命名空间 `CategoryTheory.Limits`。
形式化陈述：Fan (f : β -> C)
参数：f : β -> C。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A fan over `f : β → C` consists of a collection of maps from an object `P` to ev
ery `f b`.
-/
abbrev Fan (f : β → C) :=
  Cone (Discrete.functor f)

/-- A cofan over `f : β → C` consists of a collection of maps from every `f b` to an object `P`. -/
/-
**CategoryTheory.Limits.Cofan** 是 Mathlib 中的一个缩写定义，位于命名空间 `CategoryTheory.Limits
`。
形式化陈述：Cofan (f : β -> C)
参数：f : β -> C。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A cofan over `f : β → C` consists of a collection of maps from every `f b` to an
 object `P`.
-/
abbrev Cofan (f : β → C) :=
  Cocone (Discrete.functor f)

/-- A fan over `f : β → C` consists of a collection of maps from an object `P` to every `f b`. -/
@[simps! pt π_app, implicit_reducible]
/-
**CategoryTheory.Limits.Fan.mk** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Limits.
Fan`。
形式化陈述：{β : Type w} →   {C : Type u} →     [inst : CategoryTheory.Category.{v, u}
 C] →       {f : β → C} → (P : C) → ((b : β) → P ⟶ f b) → CategoryTheory.Limits.
Fan f
参数：P : C；(b : β) → P ⟶ f b。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A fan over `f : β → C` consists of a collection of maps from an object `P` to ev
ery `f b`.
-/
def Fan.mk {f : β → C} (P : C) (p : ∀ b, P ⟶ f b) : Fan f where
  pt := P
  π := Discrete.natTrans (fun X => p X.as)

/-- A cofan over `f : β → C` consists of a collection of maps from every `f b` to an object `P`. -/
@[simps! pt ι_app, implicit_reducible]
/-
**CategoryTheory.Limits.Cofan.mk** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Limit
s.Cofan`。
形式化陈述：{β : Type w} →   {C : Type u} →     [inst : CategoryTheory.Category.{v, u}
 C] →       {f : β → C} → (P : C) → ((b : β) → f b ⟶ P) → CategoryTheory.Limits.
Cofan f
参数：P : C；(b : β) → f b ⟶ P。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A cofan over `f : β → C` consists of a collection of maps from every `f b` to an
 object `P`.
-/
def Cofan.mk {f : β → C} (P : C) (p : ∀ b, f b ⟶ P) : Cofan f where
  pt := P
  ι := Discrete.natTrans (fun X => p X.as)

/-- Get the `j`th "projection" in the fan.
(Note that the initial letter of `proj` matches the greek letter in `Cone.π`.) -/
/-
**CategoryTheory.Limits.Fan.proj** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Limit
s.Fan`。
形式化陈述：{β : Type w} →   {C : Type u} →     [inst : CategoryTheory.Category.{v, u}
 C] → {f : β → C} → (p : CategoryTheory.Limits.Fan f) → (j : β) → p.pt ⟶ f j
参数：p : CategoryTheory.Limits.Fan f；j : β。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Get the `j`th "projection" in the fan.
(Note that the initial letter of `proj` matches the greek letter in `Cone.π`.)
-/
def Fan.proj {f : β → C} (p : Fan f) (j : β) : p.pt ⟶ f j :=
  p.π.app (Discrete.mk j)

/-- Get the `j`th "injection" in the cofan.
(Note that the initial letter of `inj` matches the greek letter in `Cocone.ι`.) -/
/-
**CategoryTheory.Limits.Cofan.inj** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Limi
ts.Cofan`。
形式化陈述：{β : Type w} →   {C : Type u} →     [inst : CategoryTheory.Category.{v, u}
 C] → {f : β → C} → (p : CategoryTheory.Limits.Cofan f) → (j : β) → f j ⟶ p.pt
参数：p : CategoryTheory.Limits.Cofan f；j : β。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Get the `j`th "injection" in the cofan.
(Note that the initial letter of `inj` matches the greek letter in `Cocone.ι`.)
-/
def Cofan.inj {f : β → C} (p : Cofan f) (j : β) : f j ⟶ p.pt :=
  p.ι.app (Discrete.mk j)

@[simp]
/-
**CategoryTheory.Limits.fan_mk_proj** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.Li
mits`。
形式化陈述：fan_mk_proj {f : β -> C} (P : C) (p : forall b, P ⟶ f b) : (Fan.mk P p).pr
oj = p
参数：P : C；p : forall b, P ⟶ f b。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem fan_mk_proj {f : β → C} (P : C) (p : ∀ b, P ⟶ f b) : (Fan.mk P p).proj = p :=
  rfl

@[simp]
/-
**CategoryTheory.Limits.cofan_mk_inj** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.L
imits`。
形式化陈述：cofan_mk_inj {f : β -> C} (P : C) (p : forall b, f b ⟶ P) : (Cofan.mk P p)
.inj = p
参数：P : C；p : forall b, f b ⟶ P。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem cofan_mk_inj {f : β → C} (P : C) (p : ∀ b, f b ⟶ P) : (Cofan.mk P p).inj = p :=
  rfl

/-- An abbreviation for `HasLimit (Discrete.functor f)`. -/
/-
**CategoryTheory.Limits.HasProduct** 是 Mathlib 中的一个缩写定义，位于命名空间 `CategoryTheory.L
imits`。
形式化陈述：HasProduct (f : β -> C)
参数：f : β -> C。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An abbreviation for `HasLimit (Discrete.functor f)`.
-/
abbrev HasProduct (f : β → C) :=
  HasLimit (Discrete.functor f)

/-- An abbreviation for `HasColimit (Discrete.functor f)`. -/
/-
**CategoryTheory.Limits.HasCoproduct** 是 Mathlib 中的一个缩写定义，位于命名空间 `CategoryTheory
.Limits`。
形式化陈述：HasCoproduct (f : β -> C)
参数：f : β -> C。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An abbreviation for `HasColimit (Discrete.functor f)`.
-/
abbrev HasCoproduct (f : β → C) :=
  HasColimit (Discrete.functor f)
/-
**CategoryTheory.Limits.hasCoproduct_of_equiv_of_iso** 是 Mathlib 中的一个引理，位于命名空间 `
CategoryTheory.Limits`。
形式化陈述：hasCoproduct_of_equiv_of_iso (f : α -> C) (g : β -> C) [HasCoproduct f] (e
 : β ≃ α) (iso : forall j, g j ≅ f (e j)) : HasCoproduct g
参数：f : α -> C；g : β -> C；e : β ≃ α；iso : forall j, g j ≅ f (e j)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.hasColimit_of_iso`：hasColimit_of_iso {F G : J ⥤ C}
 [HasColimit F] (α : G ≅ F) : HasColimit G
-/
lemma hasCoproduct_of_equiv_of_iso (f : α → C) (g : β → C)
    [HasCoproduct f] (e : β ≃ α) (iso : ∀ j, g j ≅ f (e j)) : HasCoproduct g := by
  have α : Discrete.functor g ≅ (Discrete.equivalence e).functor ⋙ Discrete.functor f :=
    Discrete.natIso (fun ⟨j⟩ => iso j)
  exact hasColimit_of_iso α
/-
**CategoryTheory.Limits.hasProduct_of_equiv_of_iso** 是 Mathlib 中的一个引理，位于命名空间 `Ca
tegoryTheory.Limits`。
形式化陈述：hasProduct_of_equiv_of_iso (f : α -> C) (g : β -> C) [HasProduct f] (e : β
 ≃ α) (iso : forall j, g j ≅ f (e j)) : HasProduct g
参数：f : α -> C；g : β -> C；e : β ≃ α；iso : forall j, g j ≅ f (e j)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.hasLimit_of_iso`：hasLimit_of_iso {F G : J ⥤ C} [Ha
sLimit F] (α : F ≅ G) : HasLimit G
-/
lemma hasProduct_of_equiv_of_iso (f : α → C) (g : β → C)
    [HasProduct f] (e : β ≃ α) (iso : ∀ j, g j ≅ f (e j)) : HasProduct g := by
  have α : Discrete.functor g ≅ (Discrete.equivalence e).functor ⋙ Discrete.functor f :=
    Discrete.natIso (fun ⟨j⟩ => iso j)
  exact hasLimit_of_iso α.symm

/-- Make a fan `f` into a limit fan by providing `lift`, `fac`, and `uniq` --
  just a convenience lemma to avoid having to go through `Discrete` -/
@[simps]
/-
**CategoryTheory.Limits.Fan.IsLimit.mk** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory
.Limits.Fan.IsLimit`。
形式化陈述：{β : Type w} →   {C : Type u} →     [inst : CategoryTheory.Category.{v, u}
 C] →       {f : β → C} →         (t : CategoryTheory.Limits.Fan f) →           
(lift : (s : CategoryTheory.Limits.Fan f) → s.pt ⟶ t.pt) →             autoParam
                 (∀ (s : CategoryTheory.Limits.Fan f) (j : β),                  
 CategoryTheory.CategoryStruct.comp (lift s) (t.proj j) = s.proj j)             
    CategoryTheory.Limits.Fan.IsLimit.mk._auto_1 →               autoParam      
             (∀ (s : CategoryTheory.Limits.Fan f) (m : s.pt ⟶ t.pt),            
         (∀ (j : β), CategoryTheory.CategoryStruct.comp m (t.proj j) = s.proj j)
 → m = lift s)                   CategoryTheory.Limits.Fan.IsLimit.mk._auto_3 → 
                CategoryTheory.Limits.IsLimit t
参数：t : CategoryTheory.Limits.Fan f；lift : (s : CategoryTheory.Limits.Fan f) → s.
pt ⟶ t.pt；∀ (s : CategoryTheory.Limits.Fan f) (j : β),                   Categor
yTheory.CategoryStruct.comp (lift s) (t.proj j) = s.proj j；∀ (s : CategoryTheory
.Limits.Fan f) (m : s.pt ⟶ t.pt),                     (∀ (j : β), CategoryTheory
.CategoryStruct.comp m (t.proj j) = s.proj j) → m = lift s。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Make a fan `f` into a limit fan by providing `lift`, `fac`, and `uniq` --
  just a convenience lemma to avoid having to go through `Discrete`
-/
def Fan.IsLimit.mk {f : β → C} (t : Fan f) (lift : ∀ s : Fan f, s.pt ⟶ t.pt)
    (fac : ∀ (s : Fan f) (j : β), lift s ≫ t.proj j = s.proj j := by cat_disch)
    (uniq : ∀ (s : Fan f) (m : s.pt ⟶ t.pt) (_ : ∀ j : β, m ≫ t.proj j = s.proj j),
      m = lift s := by cat_disch) :
    IsLimit t :=
  { lift }

@[deprecated (since := "2026-05-19")]
alias mkFanLimit := Fan.IsLimit.mk

/-- Constructor for morphisms to the point of a limit fan. -/
/-
**CategoryTheory.Limits.Fan.IsLimit.lift** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheo
ry.Limits.Fan.IsLimit`。
形式化陈述：{β : Type w} →   {C : Type u} →     [inst : CategoryTheory.Category.{v, u}
 C] →       {F : β → C} →         {c : CategoryTheory.Limits.Fan F} → CategoryTh
eory.Limits.IsLimit c → {A : C} → ((i : β) → A ⟶ F i) → (A ⟶ c.pt)
参数：(i : β) → A ⟶ F i；A ⟶ c.pt。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Constructor for morphisms to the point of a limit fan.
-/
def Fan.IsLimit.lift {F : β → C} {c : Fan F} (hc : IsLimit c) {A : C}
    (f : ∀ i, A ⟶ F i) : A ⟶ c.pt :=
  hc.lift (Fan.mk A f)

@[deprecated (since := "2026-01-12")] alias Fan.IsLimit.desc := Fan.IsLimit.lift

@[reassoc (attr := simp)]
/-
**CategoryTheory.Limits.Fan.IsLimit.fac** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheor
y.Limits.Fan.IsLimit`。
形式化陈述：∀ {β : Type w} {C : Type u} [inst : CategoryTheory.Category.{v, u} C] {F :
 β → C} {c : CategoryTheory.Limits.Fan F}   (hc : CategoryTheory.Limits.IsLimit 
c) {A : C} (f : (i : β) → A ⟶ F i) (i : β),   CategoryTheory.CategoryStruct.comp
 (CategoryTheory.Limits.Fan.IsLimit.lift hc f) (c.proj i) = f i
参数：hc : CategoryTheory.Limits.IsLimit c；f : (i : β) → A ⟶ F i；i : β；CategoryTheo
ry.Limits.Fan.IsLimit.lift hc f；c.proj i。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.IsLimit.fac`：∀ {J : Type u₁} [inst : CategoryTheor
y.Category.{v₁, u₁} J] {C : Type u₃} [inst_1 : CategoryTheory.Category.{v₃, u₃} 
C]   {F : CategoryTheor…
-/
lemma Fan.IsLimit.fac {F : β → C} {c : Fan F} (hc : IsLimit c) {A : C}
    (f : ∀ i, A ⟶ F i) (i : β) :
    Fan.IsLimit.lift hc f ≫ c.proj i = f i :=
  hc.fac (Fan.mk A f) ⟨i⟩

@[reassoc (attr := simp)]
/-
**CategoryTheory.Limits.Fan.IsLimit.lift_proj** 是 Mathlib 中的一个定理，位于命名空间 `Categor
yTheory.Limits.Fan.IsLimit`。
形式化陈述：∀ {β : Type w} {C : Type u} [inst : CategoryTheory.Category.{v, u} C] {X :
 β → C} {c : CategoryTheory.Limits.Fan X}   (d : CategoryTheory.Limits.Fan X) (h
c : CategoryTheory.Limits.IsLimit c) (i : β),   CategoryTheory.CategoryStruct.co
mp (hc.lift d) (c.proj i) = d.proj i
参数：d : CategoryTheory.Limits.Fan X；hc : CategoryTheory.Limits.IsLimit c；i : β；hc
.lift d；c.proj i。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.IsLimit.fac`：∀ {J : Type u₁} [inst : CategoryTheor
y.Category.{v₁, u₁} J] {C : Type u₃} [inst_1 : CategoryTheory.Category.{v₃, u₃} 
C]   {F : CategoryTheor…
-/
lemma Fan.IsLimit.lift_proj {X : β → C} {c : Fan X} (d : Fan X) (hc : IsLimit c)
    (i : β) : hc.lift d ≫ c.proj i = d.proj i :=
  hc.fac _ _
/-
**CategoryTheory.Limits.Fan.IsLimit.hom_ext** 是 Mathlib 中的一个定理，位于命名空间 `CategoryT
heory.Limits.Fan.IsLimit`。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] {I : Type u_1} {F
 : I → C} {c : CategoryTheory.Limits.Fan F}   (hc : CategoryTheory.Limits.IsLimi
t c) {A : C} (f g : A ⟶ c.pt),   (∀ (i : I), CategoryTheory.CategoryStruct.comp 
f (c.proj i) = CategoryTheory.CategoryStruct.comp g (c.proj i)) → f = g
参数：hc : CategoryTheory.Limits.IsLimit c；f g : A ⟶ c.pt；∀ (i : I), CategoryTheory
.CategoryStruct.comp f (c.proj i) = CategoryTheory.CategoryStruct.comp g (c.proj
 i)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.IsLimit.hom_ext`：hom_ext (h : IsLimit t) {W : C} {
f f' : W ⟶ t.pt} (w : forall j, f ≫ t.π.app j = f' ≫ t.π.app j) : f = f'
-/
lemma Fan.IsLimit.hom_ext {I : Type*} {F : I → C} {c : Fan F} (hc : IsLimit c) {A : C}
    (f g : A ⟶ c.pt) (h : ∀ i, f ≫ c.proj i = g ≫ c.proj i) : f = g :=
  hc.hom_ext (fun ⟨i⟩ => h i)

/-- Make a cofan `f` into a colimit cofan by providing `desc`, `fac`, and `uniq` --
  just a convenience lemma to avoid having to go through `Discrete` -/
@[simps]
/-
**CategoryTheory.Limits.Cofan.IsColimit.mk** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTh
eory.Limits.Cofan.IsColimit`。
形式化陈述：{β : Type w} →   {C : Type u} →     [inst : CategoryTheory.Category.{v, u}
 C] →       {f : β → C} →         (s : CategoryTheory.Limits.Cofan f) →         
  (desc : (t : CategoryTheory.Limits.Cofan f) → s.pt ⟶ t.pt) →             autoP
aram                 (∀ (t : CategoryTheory.Limits.Cofan f) (j : β),            
       CategoryTheory.CategoryStruct.comp (s.inj j) (desc t) = t.inj j)         
        CategoryTheory.Limits.Cofan.IsColimit.mk._auto_1 →               autoPar
am                   (∀ (t : CategoryTheory.Limits.Cofan f) (m : s.pt ⟶ t.pt),  
                   (∀ (j : β), CategoryTheory.CategoryStruct.comp (s.inj j) m = 
t.inj j) → m = desc t)                   CategoryTheory.Limits.Cofan.IsColimit.m
k._auto_3 →                 CategoryTheory.Limits.IsColimit s
参数：s : CategoryTheory.Limits.Cofan f；desc : (t : CategoryTheory.Limits.Cofan f) 
→ s.pt ⟶ t.pt；∀ (t : CategoryTheory.Limits.Cofan f) (j : β),                   C
ategoryTheory.CategoryStruct.comp (s.inj j) (desc t) = t.inj j；∀ (t : CategoryTh
eory.Limits.Cofan f) (m : s.pt ⟶ t.pt),                     (∀ (j : β), Category
Theory.CategoryStruct.comp (s.inj j) m = t.inj j) → m = desc t。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Make a cofan `f` into a colimit cofan by providing `desc`, `fac`, and `uniq` --
  just a convenience lemma to avoid having to go through `Discrete`
-/
def Cofan.IsColimit.mk {f : β → C} (s : Cofan f) (desc : ∀ t : Cofan f, s.pt ⟶ t.pt)
    (fac : ∀ (t : Cofan f) (j : β), s.inj j ≫ desc t = t.inj j := by cat_disch)
    (uniq : ∀ (t : Cofan f) (m : s.pt ⟶ t.pt) (_ : ∀ j : β, s.inj j ≫ m = t.inj j),
      m = desc t := by cat_disch) :
    IsColimit s :=
  { desc }

@[deprecated (since := "2026-05-19")]
alias mkCofanColimit := Cofan.IsColimit.mk

/-- Constructor for morphisms from the point of a colimit cofan. -/
/-
**CategoryTheory.Limits.Cofan.IsColimit.desc** 是 Mathlib 中的一个定义，位于命名空间 `Category
Theory.Limits.Cofan.IsColimit`。
形式化陈述：{β : Type w} →   {C : Type u} →     [inst : CategoryTheory.Category.{v, u}
 C] →       {F : β → C} →         {c : CategoryTheory.Limits.Cofan F} →         
  CategoryTheory.Limits.IsColimit c → {A : C} → ((i : β) → F i ⟶ A) → (c.pt ⟶ A)
参数：(i : β) → F i ⟶ A；c.pt ⟶ A。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Constructor for morphisms from the point of a colimit cofan.
-/
def Cofan.IsColimit.desc {F : β → C} {c : Cofan F} (hc : IsColimit c) {A : C}
    (f : ∀ i, F i ⟶ A) : c.pt ⟶ A :=
  hc.desc (Cofan.mk A f)

@[reassoc (attr := simp)]
/-
**CategoryTheory.Limits.Cofan.IsColimit.fac** 是 Mathlib 中的一个定理，位于命名空间 `CategoryT
heory.Limits.Cofan.IsColimit`。
形式化陈述：∀ {β : Type w} {C : Type u} [inst : CategoryTheory.Category.{v, u} C] {F :
 β → C} {c : CategoryTheory.Limits.Cofan F}   (hc : CategoryTheory.Limits.IsColi
mit c) {A : C} (f : (i : β) → F i ⟶ A) (i : β),   CategoryTheory.CategoryStruct.
comp (c.inj i) (CategoryTheory.Limits.Cofan.IsColimit.desc hc f) = f i
参数：hc : CategoryTheory.Limits.IsColimit c；f : (i : β) → F i ⟶ A；i : β；c.inj i；Ca
tegoryTheory.Limits.Cofan.IsColimit.desc hc f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.IsColimit.fac`：∀ {J : Type u₁} [inst : CategoryThe
ory.Category.{v₁, u₁} J] {C : Type u₃} [inst_1 : CategoryTheory.Category.{v₃, u₃
} C]   {F : CategoryTheor…
-/
lemma Cofan.IsColimit.fac {F : β → C} {c : Cofan F} (hc : IsColimit c) {A : C}
    (f : ∀ i, F i ⟶ A) (i : β) :
    c.inj i ≫ Cofan.IsColimit.desc hc f = f i :=
  hc.fac (Cofan.mk A f) ⟨i⟩

@[reassoc (attr := simp)]
/-
**CategoryTheory.Limits.Cofan.IsColimit.inj_desc** 是 Mathlib 中的一个定理，位于命名空间 `Cate
goryTheory.Limits.Cofan.IsColimit`。
形式化陈述：∀ {β : Type w} {C : Type u} [inst : CategoryTheory.Category.{v, u} C] {X :
 β → C} {c : CategoryTheory.Limits.Cofan X}   (d : CategoryTheory.Limits.Cofan X
) (hc : CategoryTheory.Limits.IsColimit c) (i : β),   CategoryTheory.CategoryStr
uct.comp (c.inj i) (hc.desc d) = d.inj i
参数：d : CategoryTheory.Limits.Cofan X；hc : CategoryTheory.Limits.IsColimit c；i : 
β；c.inj i；hc.desc d。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.IsColimit.fac`：∀ {J : Type u₁} [inst : CategoryThe
ory.Category.{v₁, u₁} J] {C : Type u₃} [inst_1 : CategoryTheory.Category.{v₃, u₃
} C]   {F : CategoryTheor…
-/
lemma Cofan.IsColimit.inj_desc {X : β → C} {c : Cofan X} (d : Cofan X) (hc : IsColimit c)
    (i : β) : c.inj i ≫ hc.desc d = d.inj i :=
  hc.fac _ _
/-
**CategoryTheory.Limits.Cofan.IsColimit.hom_ext** 是 Mathlib 中的一个定理，位于命名空间 `Categ
oryTheory.Limits.Cofan.IsColimit`。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] {I : Type u_1} {F
 : I → C} {c : CategoryTheory.Limits.Cofan F}   (hc : CategoryTheory.Limits.IsCo
limit c) {A : C} (f g : c.pt ⟶ A),   (∀ (i : I), CategoryTheory.CategoryStruct.c
omp (c.inj i) f = CategoryTheory.CategoryStruct.comp (c.inj i) g) → f = g
参数：hc : CategoryTheory.Limits.IsColimit c；f g : c.pt ⟶ A；∀ (i : I), CategoryTheo
ry.CategoryStruct.comp (c.inj i) f = CategoryTheory.CategoryStruct.comp (c.inj i
) g。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.IsColimit.hom_ext`：∀ {J : Type u₁} [inst : Categor
yTheory.Category.{v₁, u₁} J] {C : Type u₃} [inst_1 : CategoryTheory.Category.{v₃
, u₃} C]   {F : CategoryTheor…
-/
lemma Cofan.IsColimit.hom_ext {I : Type*} {F : I → C} {c : Cofan F} (hc : IsColimit c) {A : C}
    (f g : c.pt ⟶ A) (h : ∀ i, c.inj i ≫ f = c.inj i ≫ g) : f = g :=
  hc.hom_ext (fun ⟨i⟩ => h i)

section

variable (C)

/-- An abbreviation for `HasLimitsOfShape (Discrete f)`. -/
/-
**CategoryTheory.Limits.HasProductsOfShape** 是 Mathlib 中的一个缩写定义，位于命名空间 `Category
Theory.Limits`。
形式化陈述：HasProductsOfShape (β : Type v)
参数：β : Type v。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An abbreviation for `HasLimitsOfShape (Discrete f)`.
-/
abbrev HasProductsOfShape (β : Type v) :=
  HasLimitsOfShape.{v} (Discrete β)

/-- An abbreviation for `HasColimitsOfShape (Discrete f)`. -/
/-
**CategoryTheory.Limits.HasCoproductsOfShape** 是 Mathlib 中的一个缩写定义，位于命名空间 `Catego
ryTheory.Limits`。
形式化陈述：HasCoproductsOfShape (β : Type v)
参数：β : Type v。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An abbreviation for `HasColimitsOfShape (Discrete f)`.
-/
abbrev HasCoproductsOfShape (β : Type v) :=
  HasColimitsOfShape.{v} (Discrete β)

end

/-- `piObj f` computes the product of a family of elements `f`.
(It is defined as an abbreviation for `limit (Discrete.functor f)`,
so for most facts about `piObj f`, you will just use general facts about limits.) -/
/-
**CategoryTheory.Limits.piObj** 是 Mathlib 中的一个缩写定义，位于命名空间 `CategoryTheory.Limits
`。
形式化陈述：piObj (f : β -> C) [HasProduct f]
参数：f : β -> C。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`piObj f` computes the product of a family of elements `f`.
(It is defined as an abbreviation for `limit (Discrete.functor f)`,
so for most facts about `piObj f`, you will just use general facts about limits.
)
-/
abbrev piObj (f : β → C) [HasProduct f] :=
  limit (Discrete.functor f)

/-- `sigmaObj f` computes the coproduct of a family of elements `f`.
(It is defined as an abbreviation for `colimit (Discrete.functor f)`,
so for most facts about `sigmaObj f`, you will just use general facts about colimits.) -/
/-
**CategoryTheory.Limits.sigmaObj** 是 Mathlib 中的一个缩写定义，位于命名空间 `CategoryTheory.Lim
its`。
形式化陈述：sigmaObj (f : β -> C) [HasCoproduct f]
参数：f : β -> C。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`sigmaObj f` computes the coproduct of a family of elements `f`.
(It is defined as an abbreviation for `colimit (Discrete.functor f)`,
so for most facts about `sigmaObj f`, you will just use general facts about coli
mits.)
-/
abbrev sigmaObj (f : β → C) [HasCoproduct f] :=
  colimit (Discrete.functor f)

/-- notation for categorical products. We need `ᶜ` to avoid conflict with `Finset.prod`. -/
notation "∏ᶜ " f:60 => piObj f

/-- notation for categorical coproducts -/
notation "∐ " f:60 => sigmaObj f

/-- The `b`-th projection from the pi object over `f` has the form `∏ᶜ f ⟶ f b`. -/
/-
**CategoryTheory.Limits.Pi.** 是 Mathlib 中的一个缩写定义，位于命名空间 `CategoryTheory.Limits`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The `b`-th projection from the pi object over `f` has the form `∏ᶜ f ⟶ f b`.
-/
abbrev Pi.π (f : β → C) [HasProduct f] (b : β) : ∏ᶜ f ⟶ f b :=
  limit.π (Discrete.functor f) (Discrete.mk b)

/-- The `b`-th inclusion into the sigma object over `f` has the form `f b ⟶ ∐ f`. -/
/-
**CategoryTheory.Limits.Sigma.** 是 Mathlib 中的一个缩写定义，位于命名空间 `CategoryTheory.Limit
s`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The `b`-th inclusion into the sigma object over `f` has the form `f b ⟶ ∐ f`.
-/
abbrev Sigma.ι (f : β → C) [HasCoproduct f] (b : β) : f b ⟶ ∐ f :=
  colimit.ι (Discrete.functor f) (Discrete.mk b)

/-- Without this lemma, `limit.hom_ext` would be applied, but the goal would involve terms
in `Discrete β` rather than `β` itself. -/
@[ext 1050]
/-
**CategoryTheory.Limits.Pi.hom_ext** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.Lim
its.Pi`。
形式化陈述：∀ {β : Type w} {C : Type u} [inst : CategoryTheory.Category.{v, u} C] {f :
 β → C}   [inst_1 : CategoryTheory.Limits.HasProduct f] {X : C} (g₁ g₂ : X ⟶ ∏ᶜ 
f),   (∀ (b : β),       CategoryTheory.CategoryStruct.comp g₁ (CategoryTheory.Li
mits.Pi.π f b) =         CategoryTheory.CategoryStruct.comp g₂ (CategoryTheory.L
imits.Pi.π f b)) →     g₁ = g₂
参数：g₁ g₂ : X ⟶ ∏ᶜ f；∀ (b : β),       CategoryTheory.CategoryStruct.comp g₁ (Cate
goryTheory.Limits.Pi.π f b) =         CategoryTheory.CategoryStruct.comp g₂ (Cat
egoryTheory.Limits.Pi.π f b)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.limit.hom_ext`：∀ {J : Type u₁} [inst : CategoryThe
ory.Category.{v₁, u₁} J] {C : Type u} [inst_1 : CategoryTheory.Category.{v, u} C
]   {F : CategoryTheory.F…

--- 原说明 ---
Without this lemma, `limit.hom_ext` would be applied, but the goal would involve
 terms
in `Discrete β` rather than `β` itself.
-/
lemma Pi.hom_ext {f : β → C} [HasProduct f] {X : C} (g₁ g₂ : X ⟶ ∏ᶜ f)
    (h : ∀ (b : β), g₁ ≫ Pi.π f b = g₂ ≫ Pi.π f b) : g₁ = g₂ :=
  limit.hom_ext (fun ⟨j⟩ => h j)

/-- Without this lemma, `limit.hom_ext` would be applied, but the goal would involve terms
in `Discrete β` rather than `β` itself. -/
@[ext 1050]
/-
**CategoryTheory.Limits.Sigma.hom_ext** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.
Limits.Sigma`。
形式化陈述：∀ {β : Type w} {C : Type u} [inst : CategoryTheory.Category.{v, u} C] {f :
 β → C}   [inst_1 : CategoryTheory.Limits.HasCoproduct f] {X : C} (g₁ g₂ : ∐ f ⟶
 X),   (∀ (b : β),       CategoryTheory.CategoryStruct.comp (CategoryTheory.Limi
ts.Sigma.ι f b) g₁ =         CategoryTheory.CategoryStruct.comp (CategoryTheory.
Limits.Sigma.ι f b) g₂) →     g₁ = g₂
参数：g₁ g₂ : ∐ f ⟶ X；∀ (b : β),       CategoryTheory.CategoryStruct.comp (Category
Theory.Limits.Sigma.ι f b) g₁ =         CategoryTheory.CategoryStruct.comp (Cate
goryTheory.Limits.Sigma.ι f b) g₂。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.colimit.hom_ext`：∀ {J : Type u₁} [inst : CategoryT
heory.Category.{v₁, u₁} J] {C : Type u} [inst_1 : CategoryTheory.Category.{v, u}
 C]   {F : CategoryTheory.F…

--- 原说明 ---
Without this lemma, `limit.hom_ext` would be applied, but the goal would involve
 terms
in `Discrete β` rather than `β` itself.
-/
lemma Sigma.hom_ext {f : β → C} [HasCoproduct f] {X : C} (g₁ g₂ : ∐ f ⟶ X)
    (h : ∀ (b : β), Sigma.ι f b ≫ g₁ = Sigma.ι f b ≫ g₂) : g₁ = g₂ :=
  colimit.hom_ext (fun ⟨j⟩ => h j)

/-- The fan constructed of the projections from the product is limiting. -/
/-
**CategoryTheory.Limits.productIsProduct** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheo
ry.Limits`。
形式化陈述：productIsProduct (f : β -> C) [HasProduct f] : IsLimit (Fan.mk _ (Pi.π f))
参数：f : β -> C。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The fan constructed of the projections from the product is limiting.
-/
def productIsProduct (f : β → C) [HasProduct f] : IsLimit (Fan.mk _ (Pi.π f)) :=
  IsLimit.ofIsoLimit (limit.isLimit (Discrete.functor f)) (Cone.ext (Iso.refl _))

/-- The cofan constructed of the inclusions from the coproduct is colimiting. -/
/-
**CategoryTheory.Limits.coproductIsCoproduct** 是 Mathlib 中的一个定义，位于命名空间 `Category
Theory.Limits`。
形式化陈述：coproductIsCoproduct (f : β -> C) [HasCoproduct f] : IsColimit (Cofan.mk _
 (Sigma.ι f))
参数：f : β -> C。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The cofan constructed of the inclusions from the coproduct is colimiting.
-/
def coproductIsCoproduct (f : β → C) [HasCoproduct f] : IsColimit (Cofan.mk _ (Sigma.ι f)) :=
  IsColimit.ofIsoColimit (colimit.isColimit (Discrete.functor f)) (Cocone.ext (Iso.refl _))

-- TODO?: simp can prove this using `eqToHom_naturality`
-- but `eqToHom_naturality` applies less easily than this lemma
@[reassoc]
/-
**CategoryTheory.Limits.Pi.** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.Limits`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem Pi.π_comp_eqToHom {J : Type*} (f : J → C) [HasProduct f] {j j' : J} (w : j = j') :
    Pi.π f j ≫ eqToHom (by simp [w]) = Pi.π f j' := by
  simp [*]

@[reassoc (attr := simp)]
/-
**CategoryTheory.Limits.Sigma.eqToHom_comp_** 是 Mathlib 中的一个定理，位于命名空间 `CategoryT
heory.Limits`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem Sigma.eqToHom_comp_ι {J : Type*} (f : J → C) [HasCoproduct f] {j j' : J} (w : j = j') :
    eqToHom (by simp [w]) ≫ Sigma.ι f j' = Sigma.ι f j := by
  cases w
  simp

/-- A collection of morphisms `P ⟶ f b` induces a morphism `P ⟶ ∏ᶜ f`. -/
/-
**CategoryTheory.Limits.Pi.lift** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Limits
.Pi`。
形式化陈述：{β : Type w} →   {C : Type u} →     [inst : CategoryTheory.Category.{v, u}
 C] →       {f : β → C} → [inst_1 : CategoryTheory.Limits.HasProduct f] → {P : C
} → ((b : β) → P ⟶ f b) → (P ⟶ ∏ᶜ f)
参数：(b : β) → P ⟶ f b；P ⟶ ∏ᶜ f。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A collection of morphisms `P ⟶ f b` induces a morphism `P ⟶ ∏ᶜ f`.
-/
abbrev Pi.lift {f : β → C} [HasProduct f] {P : C} (p : ∀ b, P ⟶ f b) : P ⟶ ∏ᶜ f :=
  limit.lift _ (Fan.mk P p)

@[reassoc, elementwise]
/-
**CategoryTheory.Limits.Pi.lift_** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.Limit
s`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem Pi.lift_π {β : Type w} {f : β → C} [HasProduct f] {P : C} (p : ∀ b, P ⟶ f b) (b : β) :
    Pi.lift p ≫ Pi.π f b = p b := by
  simp only [limit.lift_π, Fan.mk_π_app]

/-- A version of `Cone.ext` for `Fan`s. -/
@[simps!]
/-
**CategoryTheory.Limits.Fan.ext** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Limits
.Fan`。
形式化陈述：{β : Type w} →   {C : Type u} →     [inst : CategoryTheory.Category.{v, u}
 C] →       {f : β → C} →         {c₁ c₂ : CategoryTheory.Limits.Fan f} →       
    (e : c₁.pt ≅ c₂.pt) →             autoParam (∀ (b : β), c₁.proj b = Category
Theory.CategoryStruct.comp e.hom (c₂.proj b))                 CategoryTheory.Lim
its.Fan.ext._auto_1 →               (c₁ ≅ c₂)
参数：e : c₁.pt ≅ c₂.pt；∀ (b : β), c₁.proj b = CategoryTheory.CategoryStruct.comp e
.hom (c₂.proj b)；c₁ ≅ c₂。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A version of `Cone.ext` for `Fan`s.
-/
def Fan.ext {f : β → C} {c₁ c₂ : Fan f} (e : c₁.pt ≅ c₂.pt)
    (w : ∀ (b : β), c₁.proj b = e.hom ≫ c₂.proj b := by cat_disch) : c₁ ≅ c₂ :=
  Cone.ext e (fun ⟨j⟩ => w j)

/-- A fan `c` on `f` such that the induced map `c.pt ⟶ ∏ f` is an iso, is a product. -/
/-
**CategoryTheory.Limits.Fan.isLimitOfIsIsoPiLift** 是 Mathlib 中的一个定义，位于命名空间 `Cate
goryTheory.Limits.Fan`。
形式化陈述：{β : Type w} →   {C : Type u} →     [inst : CategoryTheory.Category.{v, u}
 C] →       {f : β → C} →         [inst_1 : CategoryTheory.Limits.HasProduct f] 
→           (c : CategoryTheory.Limits.Fan f) →             [hc : CategoryTheory
.IsIso (CategoryTheory.Limits.Pi.lift c.proj)] → CategoryTheory.Limits.IsLimit c
参数：c : CategoryTheory.Limits.Fan f；CategoryTheory.Limits.Pi.lift c.proj。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A fan `c` on `f` such that the induced map `c.pt ⟶ ∏ f` is an iso, is a product.
-/
def Fan.isLimitOfIsIsoPiLift {f : β → C} [HasProduct f] (c : Fan f)
    [hc : IsIso (Pi.lift c.proj)] : IsLimit c :=
  IsLimit.ofIsoLimit (limit.isLimit (Discrete.functor f))
    (Fan.ext (@asIso _ _ _ _ _ hc) (fun _ => (limit.lift_π _ _).symm)).symm
/-
**CategoryTheory.Limits.Fan.nonempty_isLimit_iff_isIso_piLift** 是 Mathlib 中的一个定理
，位于命名空间 `CategoryTheory.Limits.Fan`。
形式化陈述：∀ {β : Type w} {C : Type u} [inst : CategoryTheory.Category.{v, u} C] {f :
 β → C}   [inst_1 : CategoryTheory.Limits.HasProduct f] (c : CategoryTheory.Limi
ts.Fan f),   Nonempty (CategoryTheory.Limits.IsLimit c) ↔ CategoryTheory.IsIso (
CategoryTheory.Limits.Pi.lift c.proj)
参数：c : CategoryTheory.Limits.Fan f；CategoryTheory.Limits.IsLimit c；CategoryTheor
y.Limits.Pi.lift c.proj。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Limits.IsLimit.nonempty_isLimit_iff_isIso_lift`：nonempty_
isLimit_iff_isIso_lift {s t : Cone F} (hs : IsLimit s) : Nonempty (IsLimit t) ↔ 
IsIso (hs.lift t)
-/
lemma Fan.nonempty_isLimit_iff_isIso_piLift {f : β → C} [HasProduct f] (c : Fan f) :
    Nonempty (IsLimit c) ↔ IsIso (Pi.lift c.proj) :=
  (limit.isLimit (Discrete.functor f)).nonempty_isLimit_iff_isIso_lift

/-- A collection of morphisms `f b ⟶ P` induces a morphism `∐ f ⟶ P`. -/
/-
**CategoryTheory.Limits.Sigma.desc** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Lim
its.Sigma`。
形式化陈述：{β : Type w} →   {C : Type u} →     [inst : CategoryTheory.Category.{v, u}
 C] →       {f : β → C} → [inst_1 : CategoryTheory.Limits.HasCoproduct f] → {P :
 C} → ((b : β) → f b ⟶ P) → (∐ f ⟶ P)
参数：(b : β) → f b ⟶ P；∐ f ⟶ P。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A collection of morphisms `f b ⟶ P` induces a morphism `∐ f ⟶ P`.
-/
abbrev Sigma.desc {f : β → C} [HasCoproduct f] {P : C} (p : ∀ b, f b ⟶ P) : ∐ f ⟶ P :=
  colimit.desc _ (Cofan.mk P p)

@[reassoc]
/-
**CategoryTheory.Limits.Sigma.** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.Limits`
。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem Sigma.ι_desc {β : Type w} {f : β → C} [HasCoproduct f] {P : C} (p : ∀ b, f b ⟶ P) (b : β) :
    Sigma.ι f b ≫ Sigma.desc p = p b := by
  simp only [colimit.ι_desc, Cofan.mk_ι_app]
/-
**CategoryTheory.Limits.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Limits`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {f : β → C} [HasCoproduct f] : IsIso (Sigma.desc (fun a ↦ Sigma.ι f a)) := by
  convert! IsIso.id _
  ext
  simp

/-- A version of `Cocone.ext` for `Cofan`s. -/
@[simps!]
/-
**CategoryTheory.Limits.Cofan.ext** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Limi
ts.Cofan`。
形式化陈述：{β : Type w} →   {C : Type u} →     [inst : CategoryTheory.Category.{v, u}
 C] →       {f : β → C} →         {c₁ c₂ : CategoryTheory.Limits.Cofan f} →     
      (e : c₁.pt ≅ c₂.pt) →             autoParam (∀ (b : β), CategoryTheory.Cat
egoryStruct.comp (c₁.inj b) e.hom = c₂.inj b)                 CategoryTheory.Lim
its.Cofan.ext._auto_1 →               (c₁ ≅ c₂)
参数：e : c₁.pt ≅ c₂.pt；∀ (b : β), CategoryTheory.CategoryStruct.comp (c₁.inj b) e.
hom = c₂.inj b；c₁ ≅ c₂。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A version of `Cocone.ext` for `Cofan`s.
-/
def Cofan.ext {f : β → C} {c₁ c₂ : Cofan f} (e : c₁.pt ≅ c₂.pt)
    (w : ∀ (b : β), c₁.inj b ≫ e.hom = c₂.inj b := by cat_disch) : c₁ ≅ c₂ :=
  Cocone.ext e (fun ⟨j⟩ => w j)

/-- A cofan `c` on `f` such that the induced map `∐ f ⟶ c.pt` is an iso, is a coproduct. -/
/-
**CategoryTheory.Limits.Cofan.isColimitOfIsIsoSigmaDesc** 是 Mathlib 中的一个定义，位于命名空
间 `CategoryTheory.Limits.Cofan`。
形式化陈述：{β : Type w} →   {C : Type u} →     [inst : CategoryTheory.Category.{v, u}
 C] →       {f : β → C} →         [inst_1 : CategoryTheory.Limits.HasCoproduct f
] →           (c : CategoryTheory.Limits.Cofan f) →             [hc : CategoryTh
eory.IsIso (CategoryTheory.Limits.Sigma.desc c.inj)] → CategoryTheory.Limits.IsC
olimit c
参数：c : CategoryTheory.Limits.Cofan f；CategoryTheory.Limits.Sigma.desc c.inj。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A cofan `c` on `f` such that the induced map `∐ f ⟶ c.pt` is an iso, is a coprod
uct.
-/
def Cofan.isColimitOfIsIsoSigmaDesc {f : β → C} [HasCoproduct f] (c : Cofan f)
    [hc : IsIso (Sigma.desc c.inj)] : IsColimit c :=
  IsColimit.ofIsoColimit (colimit.isColimit (Discrete.functor f))
    (Cofan.ext (@asIso _ _ _ _ _ hc) (fun _ => colimit.ι_desc _ _))
/-
**CategoryTheory.Limits.Cofan.nonempty_isColimit_iff_isIso_sigmaDesc** 是 Mathlib
 中的一个定理，位于命名空间 `CategoryTheory.Limits.Cofan`。
形式化陈述：∀ {β : Type w} {C : Type u} [inst : CategoryTheory.Category.{v, u} C] {f :
 β → C}   [inst_1 : CategoryTheory.Limits.HasCoproduct f] (c : CategoryTheory.Li
mits.Cofan f),   Nonempty (CategoryTheory.Limits.IsColimit c) ↔ CategoryTheory.I
sIso (CategoryTheory.Limits.Sigma.desc c.inj)
参数：c : CategoryTheory.Limits.Cofan f；CategoryTheory.Limits.IsColimit c；CategoryT
heory.Limits.Sigma.desc c.inj。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.IsColimit.nonempty_isColimit_iff_isIso_desc`：∀ {J 
: Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} J] {C : Type u₃} [inst_1 : C
ategoryTheory.Category.{v₃, u₃} C]   {F : CategoryTheor…
-/
lemma Cofan.nonempty_isColimit_iff_isIso_sigmaDesc {f : β → C} [HasCoproduct f] (c : Cofan f) :
    Nonempty (IsColimit c) ↔ IsIso (Sigma.desc c.inj) :=
  (colimit.isColimit (Discrete.functor f)).nonempty_isColimit_iff_isIso_desc

@[deprecated (since := "2026-01-21")]
alias Cofan.isColimit_iff_isIso_sigmaDesc := Cofan.nonempty_isColimit_iff_isIso_sigmaDesc

/-- A coproduct of coproducts is a coproduct -/
/-
**CategoryTheory.Limits.Cofan.isColimitTrans** 是 Mathlib 中的一个定义，位于命名空间 `Category
Theory.Limits.Cofan`。
形式化陈述：{α : Type w₂} →   {C : Type u} →     [inst : CategoryTheory.Category.{v, u
} C] →       {X : α → C} →         (c : CategoryTheory.Limits.Cofan X) →        
   CategoryTheory.Limits.IsColimit c →             {β : α → Type u_1} →         
      {Y : (a : α) → β a → C} →                 (π : (a : α) → (b : β a) → Y a b
 ⟶ X a) →                   ((a : α) → CategoryTheory.Limits.IsColimit (Category
Theory.Limits.Cofan.mk (X a) (π a))) →                     CategoryTheory.Limits
.IsColimit                       (CategoryTheory.Limits.Cofan.mk c.pt fun x =>  
                       match x with                         | ⟨a, b⟩ => Category
Theory.CategoryStruct.comp (π a b) (c.inj a))
参数：c : CategoryTheory.Limits.Cofan X；a : α；π : (a : α) → (b : β a) → Y a b ⟶ X a
；(a : α) → CategoryTheory.Limits.IsColimit (CategoryTheory.Limits.Cofan.mk (X a)
 (π a))；CategoryTheory.Limits.Cofan.mk c.pt fun x =>                         mat
ch x with                         | ⟨a, b⟩ => CategoryTheory.CategoryStruct.comp
 (π a b) (c.inj a)。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A coproduct of coproducts is a coproduct
-/
def Cofan.isColimitTrans {X : α → C} (c : Cofan X) (hc : IsColimit c)
    {β : α → Type*} {Y : (a : α) → β a → C} (π : (a : α) → (b : β a) → Y a b ⟶ X a)
      (hs : ∀ a, IsColimit (Cofan.mk (X a) (π a))) :
        IsColimit (Cofan.mk (f := fun ⟨a,b⟩ => Y a b) c.pt
          (fun (⟨a, b⟩ : Σ a, _) ↦ π a b ≫ c.inj a)) := by
  refine Cofan.IsColimit.mk _ ?_ ?_ ?_
  · exact fun t ↦ hc.desc (Cofan.mk _ fun a ↦ (hs a).desc (Cofan.mk t.pt (fun b ↦ t.inj ⟨a, b⟩)))
  · intro t ⟨a, b⟩
    simp only [mk_pt, cofan_mk_inj, Category.assoc]
    erw [hc.fac, (hs a).fac]
    rfl
  · intro t m h
    refine hc.hom_ext fun ⟨a⟩ ↦ (hs a).hom_ext fun ⟨b⟩ ↦ ?_
    erw [hc.fac, (hs a).fac]
    simpa using! h ⟨a, b⟩

/-- Construct a morphism between categorical products (indexed by the same type)
from a family of morphisms between the factors.
-/
/-
**CategoryTheory.Limits.Pi.map** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Limits.
Pi`。
形式化陈述：{β : Type w} →   {C : Type u} →     [inst : CategoryTheory.Category.{v, u}
 C] →       {f g : β → C} →         [inst_1 : CategoryTheory.Limits.HasProduct f
] →           [inst_2 : CategoryTheory.Limits.HasProduct g] → ((b : β) → f b ⟶ g
 b) → (∏ᶜ f ⟶ ∏ᶜ g)
参数：(b : β) → f b ⟶ g b；∏ᶜ f ⟶ ∏ᶜ g。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Construct a morphism between categorical products (indexed by the same type)
from a family of morphisms between the factors.
-/
def Pi.map {f g : β → C} [HasProduct f] [HasProduct g] (p : ∀ b, f b ⟶ g b) : ∏ᶜ f ⟶ ∏ᶜ g :=
  limMap (Discrete.natTrans fun X => p X.as)

@[reassoc (attr := simp), elementwise nosimp]
/-
**CategoryTheory.Limits.Pi.map_** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.Limits
`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma Pi.map_π {f g : β → C} [HasProduct f] [HasProduct g] (p : ∀ b, f b ⟶ g b) (b : β) :
    Pi.map p ≫ Pi.π g b = Pi.π f b ≫ p b := by simp [Pi.map]

@[simp]
/-
**CategoryTheory.Limits.Pi.map_id** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.Limi
ts.Pi`。
形式化陈述：∀ {α : Type w₂} {C : Type u} [inst : CategoryTheory.Category.{v, u} C] {f 
: α → C}   [inst_1 : CategoryTheory.Limits.HasProduct f],   (CategoryTheory.Limi
ts.Pi.map fun a => CategoryTheory.CategoryStruct.id (f a)) =     CategoryTheory.
CategoryStruct.id (∏ᶜ f)
参数：CategoryTheory.Limits.Pi.map fun a => CategoryTheory.CategoryStruct.id (f a)；
∏ᶜ f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.Pi.hom_ext`：∀ {β : Type w} {C : Type u} [inst : Ca
tegoryTheory.Category.{v, u} C] {f : β → C}   [inst_1 : CategoryTheory.Limits.Ha
sProduct f] {X : C} (g…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Limits.Pi.map_π`：∀ {β : Type w} {C : Type u} [inst : Cate
goryTheory.Category.{v, u} C] {f g : β → C}   [inst_1 : CategoryTheory.Limits.Ha
sProduct f] [inst_2 …
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma Pi.map_id {f : α → C} [HasProduct f] : Pi.map (fun a => 𝟙 (f a)) = 𝟙 (∏ᶜ f) := by
  ext; simp
/-
**CategoryTheory.Limits.Pi.map_comp_map** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheor
y.Limits.Pi`。
形式化陈述：∀ {α : Type w₂} {C : Type u} [inst : CategoryTheory.Category.{v, u} C] {f 
g h : α → C}   [inst_1 : CategoryTheory.Limits.HasProduct f] [inst_2 : CategoryT
heory.Limits.HasProduct g]   [inst_3 : CategoryTheory.Limits.HasProduct h] (q : 
(a : α) → f a ⟶ g a) (q' : (a : α) → g a ⟶ h a),   CategoryTheory.CategoryStruct
.comp (CategoryTheory.Limits.Pi.map q) (CategoryTheory.Limits.Pi.map q') =     C
ategoryTheory.Limits.Pi.map fun a => CategoryTheory.CategoryStruct.comp (q a) (q
' a)
参数：q : (a : α) → f a ⟶ g a；q' : (a : α) → g a ⟶ h a；CategoryTheory.Limits.Pi.map
 q；CategoryTheory.Limits.Pi.map q'；q a；q' a。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.Pi.hom_ext`：∀ {β : Type w} {C : Type u} [inst : Ca
tegoryTheory.Category.{v, u} C] {f : β → C}   [inst_1 : CategoryTheory.Limits.Ha
sProduct f] {X : C} (g…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.Limits.Pi.map_π`：∀ {β : Type w} {C : Type u} [inst : Cate
goryTheory.Category.{v, u} C] {f g : β → C}   [inst_1 : CategoryTheory.Limits.Ha
sProduct f] [inst_2 …
· 使用定理 `CategoryTheory.Limits.Pi.map_π_assoc`：∀ {β : Type w} {C : Type u} [inst 
: CategoryTheory.Category.{v, u} C] {f g : β → C}   [inst_1 : CategoryTheory.Lim
its.HasProduct f] [inst_2 …
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma Pi.map_comp_map {f g h : α → C} [HasProduct f] [HasProduct g] [HasProduct h]
    (q : ∀ (a : α), f a ⟶ g a) (q' : ∀ (a : α), g a ⟶ h a) :
    Pi.map q ≫ Pi.map q' = Pi.map (fun a => q a ≫ q' a) := by
  ext; simp
/-
**CategoryTheory.Limits.Pi.map_mono** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.Li
mits.Pi`。
形式化陈述：∀ {β : Type w} {C : Type u} [inst : CategoryTheory.Category.{v, u} C] {f g
 : β → C}   [inst_1 : CategoryTheory.Limits.HasProduct f] [inst_2 : CategoryTheo
ry.Limits.HasProduct g] (p : (b : β) → f b ⟶ g b)   [∀ (i : β), CategoryTheory.M
ono (p i)], CategoryTheory.Mono (CategoryTheory.Limits.Pi.map p)
参数：p : (b : β) → f b ⟶ g b；i : β；p i；CategoryTheory.Limits.Pi.map p。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance Pi.map_mono {f g : β → C} [HasProduct f] [HasProduct g] (p : ∀ b, f b ⟶ g b)
    [∀ i, Mono (p i)] : Mono <| Pi.map p :=
  @Limits.limMap_mono _ _ _ _ (Discrete.functor f) (Discrete.functor g) _ _
    (Discrete.natTrans fun X => p X.as) (by dsimp; infer_instance)

/-- Construct a morphism between categorical products from a family of morphisms between the
factors. -/
/-
**CategoryTheory.Limits.Pi.map'** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Limits
.Pi`。
形式化陈述：{β : Type w} →   {α : Type w₂} →     {C : Type u} →       [inst : Category
Theory.Category.{v, u} C] →         {f : α → C} →           {g : β → C} →       
      [inst_1 : CategoryTheory.Limits.HasProduct f] →               [inst_2 : Ca
tegoryTheory.Limits.HasProduct g] → (p : β → α) → ((b : β) → f (p b) ⟶ g b) → (∏
ᶜ f ⟶ ∏ᶜ g)
参数：p : β → α；(b : β) → f (p b) ⟶ g b；∏ᶜ f ⟶ ∏ᶜ g。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Construct a morphism between categorical products from a family of morphisms bet
ween the
factors.
-/
def Pi.map' {f : α → C} {g : β → C} [HasProduct f] [HasProduct g] (p : β → α)
    (q : ∀ (b : β), f (p b) ⟶ g b) : ∏ᶜ f ⟶ ∏ᶜ g :=
  Pi.lift (fun a => Pi.π _ _ ≫ q a)

@[reassoc (attr := simp)]
/-
**CategoryTheory.Limits.Pi.map'_comp_** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.
Limits`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma Pi.map'_comp_π {f : α → C} {g : β → C} [HasProduct f] [HasProduct g] (p : β → α)
    (q : ∀ (b : β), f (p b) ⟶ g b) (b : β) : Pi.map' p q ≫ Pi.π g b = Pi.π f (p b) ≫ q b :=
  limit.lift_π _ _
/-
**CategoryTheory.Limits.Pi.map'_id_id** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.
Limits.Pi`。
形式化陈述：∀ {α : Type w₂} {C : Type u} [inst : CategoryTheory.Category.{v, u} C] {f 
: α → C}   [inst_1 : CategoryTheory.Limits.HasProduct f],   (CategoryTheory.Limi
ts.Pi.map' id fun a => CategoryTheory.CategoryStruct.id (f a)) =     CategoryThe
ory.CategoryStruct.id (∏ᶜ f)
参数：CategoryTheory.Limits.Pi.map' id fun a => CategoryTheory.CategoryStruct.id (f
 a)；∏ᶜ f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.Pi.hom_ext`：∀ {β : Type w} {C : Type u} [inst : Ca
tegoryTheory.Category.{v, u} C] {f : β → C}   [inst_1 : CategoryTheory.Limits.Ha
sProduct f] {X : C} (g…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Limits.Pi.map'_comp_π`：∀ {β : Type w} {α : Type w₂} {C : 
Type u} [inst : CategoryTheory.Category.{v, u} C] {f : α → C} {g : β → C}   [ins
t_1 : CategoryTheory.Limit…
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma Pi.map'_id_id {f : α → C} [HasProduct f] : Pi.map' id (fun a => 𝟙 (f a)) = 𝟙 (∏ᶜ f) := by
  ext; simp

@[simp]
/-
**CategoryTheory.Limits.Pi.map'_id** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.Lim
its.Pi`。
形式化陈述：∀ {α : Type w₂} {C : Type u} [inst : CategoryTheory.Category.{v, u} C] {f 
g : α → C}   [inst_1 : CategoryTheory.Limits.HasProduct f] [inst_2 : CategoryThe
ory.Limits.HasProduct g] (p : (b : α) → f b ⟶ g b),   CategoryTheory.Limits.Pi.m
ap' id p = CategoryTheory.Limits.Pi.map p
参数：p : (b : α) → f b ⟶ g b。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma Pi.map'_id {f g : α → C} [HasProduct f] [HasProduct g] (p : ∀ b, f b ⟶ g b) :
    Pi.map' id p = Pi.map p :=
  rfl
/-
**CategoryTheory.Limits.Pi.map'_comp_map'** 是 Mathlib 中的一个定理，位于命名空间 `CategoryThe
ory.Limits.Pi`。
形式化陈述：∀ {β : Type w} {α : Type w₂} {γ : Type w₃} {C : Type u} [inst : CategoryTh
eory.Category.{v, u} C] {f : α → C}   {g : β → C} {h : γ → C} [inst_1 : Category
Theory.Limits.HasProduct f] [inst_2 : CategoryTheory.Limits.HasProduct g]   [ins
t_3 : CategoryTheory.Limits.HasProduct h] (p : β → α) (p' : γ → β) (q : (b : β) 
→ f (p b) ⟶ g b)   (q' : (c : γ) → g (p' c) ⟶ h c),   CategoryTheory.CategoryStr
uct.comp (CategoryTheory.Limits.Pi.map' p q) (CategoryTheory.Limits.Pi.map' p' q
') =     CategoryTheory.Limits.Pi.map' (p ∘ p') fun c => CategoryTheory.Category
Struct.comp (q (p' c)) (q' c)
参数：p : β → α；p' : γ → β；q : (b : β) → f (p b) ⟶ g b；q' : (c : γ) → g (p' c) ⟶ h 
c；CategoryTheory.Limits.Pi.map' p q；CategoryTheory.Limits.Pi.map' p' q'；p ∘ p'；q
 (p' c)；q' c。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.Pi.hom_ext`：∀ {β : Type w} {C : Type u} [inst : Ca
tegoryTheory.Category.{v, u} C] {f : β → C}   [inst_1 : CategoryTheory.Limits.Ha
sProduct f] {X : C} (g…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.Limits.Pi.map'_comp_π`：∀ {β : Type w} {α : Type w₂} {C : 
Type u} [inst : CategoryTheory.Category.{v, u} C] {f : α → C} {g : β → C}   [ins
t_1 : CategoryTheory.Limit…
· 使用定理 `CategoryTheory.Limits.Pi.map'_comp_π_assoc`：∀ {β : Type w} {α : Type w₂}
 {C : Type u} [inst : CategoryTheory.Category.{v, u} C] {f : α → C} {g : β → C} 
  [inst_1 : CategoryTheory.Limit…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma Pi.map'_comp_map' {f : α → C} {g : β → C} {h : γ → C} [HasProduct f] [HasProduct g]
    [HasProduct h] (p : β → α) (p' : γ → β) (q : ∀ (b : β), f (p b) ⟶ g b)
    (q' : ∀ (c : γ), g (p' c) ⟶ h c) :
    Pi.map' p q ≫ Pi.map' p' q' = Pi.map' (p ∘ p') (fun c => q (p' c) ≫ q' c) := by
  ext; simp
/-
**CategoryTheory.Limits.Pi.map'_comp_map** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheo
ry.Limits.Pi`。
形式化陈述：∀ {β : Type w} {α : Type w₂} {C : Type u} [inst : CategoryTheory.Category.
{v, u} C] {f : α → C} {g h : β → C}   [inst_1 : CategoryTheory.Limits.HasProduct
 f] [inst_2 : CategoryTheory.Limits.HasProduct g]   [inst_3 : CategoryTheory.Lim
its.HasProduct h] (p : β → α) (q : (b : β) → f (p b) ⟶ g b) (q' : (b : β) → g b 
⟶ h b),   CategoryTheory.CategoryStruct.comp (CategoryTheory.Limits.Pi.map' p q)
 (CategoryTheory.Limits.Pi.map q') =     CategoryTheory.Limits.Pi.map' p fun b =
> CategoryTheory.CategoryStruct.comp (q b) (q' b)
参数：p : β → α；q : (b : β) → f (p b) ⟶ g b；q' : (b : β) → g b ⟶ h b；CategoryTheory
.Limits.Pi.map' p q；CategoryTheory.Limits.Pi.map q'；q b；q' b。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.Pi.hom_ext`：∀ {β : Type w} {C : Type u} [inst : Ca
tegoryTheory.Category.{v, u} C] {f : β → C}   [inst_1 : CategoryTheory.Limits.Ha
sProduct f] {X : C} (g…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.Limits.Pi.map_π`：∀ {β : Type w} {C : Type u} [inst : Cate
goryTheory.Category.{v, u} C] {f g : β → C}   [inst_1 : CategoryTheory.Limits.Ha
sProduct f] [inst_2 …
· 使用定理 `CategoryTheory.Limits.Pi.map'_comp_π_assoc`：∀ {β : Type w} {α : Type w₂}
 {C : Type u} [inst : CategoryTheory.Category.{v, u} C] {f : α → C} {g : β → C} 
  [inst_1 : CategoryTheory.Limit…
· 使用定理 `CategoryTheory.Limits.Pi.map'_comp_π`：∀ {β : Type w} {α : Type w₂} {C : 
Type u} [inst : CategoryTheory.Category.{v, u} C] {f : α → C} {g : β → C}   [ins
t_1 : CategoryTheory.Limit…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma Pi.map'_comp_map {f : α → C} {g h : β → C} [HasProduct f] [HasProduct g] [HasProduct h]
    (p : β → α) (q : ∀ (b : β), f (p b) ⟶ g b) (q' : ∀ (b : β), g b ⟶ h b) :
    Pi.map' p q ≫ Pi.map q' = Pi.map' p (fun b => q b ≫ q' b) := by
  ext; simp
/-
**CategoryTheory.Limits.Pi.map_comp_map'** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheo
ry.Limits.Pi`。
形式化陈述：∀ {β : Type w} {α : Type w₂} {C : Type u} [inst : CategoryTheory.Category.
{v, u} C] {f g : α → C} {h : β → C}   [inst_1 : CategoryTheory.Limits.HasProduct
 f] [inst_2 : CategoryTheory.Limits.HasProduct g]   [inst_3 : CategoryTheory.Lim
its.HasProduct h] (p : β → α) (q : (a : α) → f a ⟶ g a) (q' : (b : β) → g (p b) 
⟶ h b),   CategoryTheory.CategoryStruct.comp (CategoryTheory.Limits.Pi.map q) (C
ategoryTheory.Limits.Pi.map' p q') =     CategoryTheory.Limits.Pi.map' p fun b =
> CategoryTheory.CategoryStruct.comp (q (p b)) (q' b)
参数：p : β → α；q : (a : α) → f a ⟶ g a；q' : (b : β) → g (p b) ⟶ h b；CategoryTheory
.Limits.Pi.map q；CategoryTheory.Limits.Pi.map' p q'；q (p b)；q' b。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.Pi.hom_ext`：∀ {β : Type w} {C : Type u} [inst : Ca
tegoryTheory.Category.{v, u} C] {f : β → C}   [inst_1 : CategoryTheory.Limits.Ha
sProduct f] {X : C} (g…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.Limits.Pi.map'_comp_π`：∀ {β : Type w} {α : Type w₂} {C : 
Type u} [inst : CategoryTheory.Category.{v, u} C] {f : α → C} {g : β → C}   [ins
t_1 : CategoryTheory.Limit…
· 使用定理 `CategoryTheory.Limits.Pi.map_π_assoc`：∀ {β : Type w} {C : Type u} [inst 
: CategoryTheory.Category.{v, u} C] {f g : β → C}   [inst_1 : CategoryTheory.Lim
its.HasProduct f] [inst_2 …
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma Pi.map_comp_map' {f g : α → C} {h : β → C} [HasProduct f] [HasProduct g] [HasProduct h]
    (p : β → α) (q : ∀ (a : α), f a ⟶ g a) (q' : ∀ (b : β), g (p b) ⟶ h b) :
    Pi.map q ≫ Pi.map' p q' = Pi.map' p (fun b => q (p b) ≫ q' b) := by
  ext; simp
/-
**CategoryTheory.Limits.Pi.map'_eq** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.Lim
its.Pi`。
形式化陈述：∀ {β : Type w} {α : Type w₂} {C : Type u} [inst : CategoryTheory.Category.
{v, u} C] {f : α → C} {g : β → C}   [inst_1 : CategoryTheory.Limits.HasProduct f
] [inst_2 : CategoryTheory.Limits.HasProduct g] {p p' : β → α}   {q : (b : β) → 
f (p b) ⟶ g b} {q' : (b : β) → f (p' b) ⟶ g b} (hp : p = p'),   (∀ (b : β), Cate
goryTheory.CategoryStruct.comp (CategoryTheory.eqToHom ⋯) (q b) = q' b) →     Ca
tegoryTheory.Limits.Pi.map' p q = CategoryTheory.Limits.Pi.map' p' q'
参数：b : β；p b；b : β；p' b；hp : p = p'；∀ (b : β), CategoryTheory.CategoryStruct.com
p (CategoryTheory.eqToHom ⋯) (q b) = q' b。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.Pi.hom_ext`：∀ {β : Type w} {C : Type u} [inst : Ca
tegoryTheory.Category.{v, u} C] {f : β → C}   [inst_1 : CategoryTheory.Limits.Ha
sProduct f] {X : C} (g…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Limits.Pi.map'_comp_π`：∀ {β : Type w} {α : Type w₂} {C : 
Type u} [inst : CategoryTheory.Category.{v, u} C] {f : α → C} {g : β → C}   [ins
t_1 : CategoryTheory.Limit…
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma Pi.map'_eq {f : α → C} {g : β → C} [HasProduct f] [HasProduct g] {p p' : β → α}
    {q : ∀ (b : β), f (p b) ⟶ g b} {q' : ∀ (b : β), f (p' b) ⟶ g b} (hp : p = p')
    (hq : ∀ (b : β), eqToHom (hp ▸ rfl) ≫ q b = q' b) : Pi.map' p q = Pi.map' p' q' := by
  cat_disch

/-- Construct an isomorphism between categorical products (indexed by the same type)
from a family of isomorphisms between the factors.
-/
/-
**CategoryTheory.Limits.Pi.mapIso** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Limi
ts.Pi`。
形式化陈述：{β : Type w} →   {C : Type u} →     [inst : CategoryTheory.Category.{v, u}
 C] →       {f g : β → C} → [inst_1 : CategoryTheory.Limits.HasProductsOfShape β
 C] → ((b : β) → f b ≅ g b) → (∏ᶜ f ≅ ∏ᶜ g)
参数：(b : β) → f b ≅ g b；∏ᶜ f ≅ ∏ᶜ g。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Construct an isomorphism between categorical products (indexed by the same type)
from a family of isomorphisms between the factors.
-/
def Pi.mapIso {f g : β → C} [HasProductsOfShape β C] (p : ∀ b, f b ≅ g b) : ∏ᶜ f ≅ ∏ᶜ g :=
  lim.mapIso (Discrete.natIso fun X => p X.as)

@[reassoc (attr := simp)]
/-
**CategoryTheory.Limits.Pi.mapIso_hom_** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory
.Limits`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma Pi.mapIso_hom_π {f g : β → C} [HasProductsOfShape β C] (p : ∀ b, f b ≅ g b) (b : β) :
    (Pi.mapIso p).hom ≫ π _ _ = π _ _ ≫ (p b).hom :=
  limMap_π _ _

@[reassoc (attr := simp)]
/-
**CategoryTheory.Limits.Pi.mapIso_inv_** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory
.Limits`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma Pi.mapIso_inv_π {f g : β → C} [HasProductsOfShape β C] (p : ∀ b, f b ≅ g b) (b : β) :
    (Pi.mapIso p).inv ≫ π _ _ = π _ _ ≫ (p b).inv :=
  limMap_π _ _
/-
**CategoryTheory.Limits.Pi.map_isIso** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.L
imits.Pi`。
形式化陈述：∀ {β : Type w} {C : Type u} [inst : CategoryTheory.Category.{v, u} C] {f g
 : β → C}   [inst_1 : CategoryTheory.Limits.HasProductsOfShape β C] (p : (b : β)
 → f b ⟶ g b)   [∀ (b : β), CategoryTheory.IsIso (p b)], CategoryTheory.IsIso (C
ategoryTheory.Limits.Pi.map p)
参数：p : (b : β) → f b ⟶ g b；b : β；p b；CategoryTheory.Limits.Pi.map p。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance Pi.map_isIso {f g : β → C} [HasProductsOfShape β C] (p : ∀ b, f b ⟶ g b)
    [∀ b, IsIso <| p b] : IsIso <| Pi.map p :=
  inferInstanceAs (IsIso (Pi.mapIso (fun b ↦ asIso (p b))).hom)

section

/- In this section, we provide some API for products when we are given a functor
`Discrete α ⥤ C` instead of a map `α → C`. -/

variable (X : Discrete α ⥤ C) [HasProduct (fun j => X.obj (Discrete.mk j))]

/-- A limit cone for `X : Discrete α ⥤ C` that is given
by `∏ᶜ (fun j => X.obj (Discrete.mk j))`. -/
@[simps]
/-
**CategoryTheory.Limits.Pi.cone** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Limits
.Pi`。
形式化陈述：{α : Type w₂} →   {C : Type u} →     [inst : CategoryTheory.Category.{v, u
} C] →       (X : CategoryTheory.Functor (CategoryTheory.Discrete α) C) →       
  [CategoryTheory.Limits.HasProduct fun j => X.obj { as := j }] → CategoryTheory
.Limits.Cone X
参数：X : CategoryTheory.Functor (CategoryTheory.Discrete α) C。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A limit cone for `X : Discrete α ⥤ C` that is given
by `∏ᶜ (fun j => X.obj (Discrete.mk j))`.
-/
def Pi.cone : Cone X where
  pt := ∏ᶜ (fun j => X.obj (Discrete.mk j))
  π := Discrete.natTrans (fun _ => Pi.π _ _)

set_option backward.defeqAttrib.useBackward true in
/-- The cone `Pi.cone X` is a limit cone. -/
/-
**CategoryTheory.Limits.productIsProduct'** 是 Mathlib 中的一个定义，位于命名空间 `CategoryThe
ory.Limits`。
形式化陈述：productIsProduct' : IsLimit (Pi.cone X) where lift s
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The cone `Pi.cone X` is a limit cone.
-/
def productIsProduct' :
    IsLimit (Pi.cone X) where
  lift s := Pi.lift (fun j => s.π.app ⟨j⟩)
  fac s := by simp
  uniq s m hm := by
    dsimp
    ext
    simp only [limit.lift_π, Fan.mk_pt, Fan.mk_π_app]
    apply hm

variable [HasLimit X]

/-- The isomorphism `∏ᶜ (fun j => X.obj (Discrete.mk j)) ≅ limit X`. -/
/-
**CategoryTheory.Limits.Pi.isoLimit** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Li
mits.Pi`。
形式化陈述：{α : Type w₂} →   {C : Type u} →     [inst : CategoryTheory.Category.{v, u
} C] →       (X : CategoryTheory.Functor (CategoryTheory.Discrete α) C) →       
  [inst_1 : CategoryTheory.Limits.HasProduct fun j => X.obj { as := j }] →      
     [inst_2 : CategoryTheory.Limits.HasLimit X] → (∏ᶜ fun j => X.obj { as := j 
}) ≅ CategoryTheory.Limits.limit X
参数：X : CategoryTheory.Functor (CategoryTheory.Discrete α) C；∏ᶜ fun j => X.obj { 
as := j }。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The isomorphism `∏ᶜ (fun j => X.obj (Discrete.mk j)) ≅ limit X`.
-/
def Pi.isoLimit :
    ∏ᶜ (fun j => X.obj (Discrete.mk j)) ≅ limit X :=
  IsLimit.conePointUniqueUpToIso (productIsProduct' X) (limit.isLimit X)

@[reassoc (attr := simp)]
/-
**CategoryTheory.Limits.Pi.isoLimit_inv_** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheo
ry.Limits`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma Pi.isoLimit_inv_π (j : α) :
    (Pi.isoLimit X).inv ≫ Pi.π _ j = limit.π _ (Discrete.mk j) :=
  IsLimit.conePointUniqueUpToIso_inv_comp _ _ _

@[reassoc (attr := simp)]
/-
**CategoryTheory.Limits.Pi.isoLimit_hom_** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheo
ry.Limits`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma Pi.isoLimit_hom_π (j : α) :
    (Pi.isoLimit X).hom ≫ limit.π _ (Discrete.mk j) = Pi.π _ j :=
  IsLimit.conePointUniqueUpToIso_hom_comp _ _ _

end

/-- Construct a morphism between categorical coproducts (indexed by the same type)
from a family of morphisms between the factors.
-/
/-
**CategoryTheory.Limits.Sigma.map** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Limi
ts.Sigma`。
形式化陈述：{β : Type w} →   {C : Type u} →     [inst : CategoryTheory.Category.{v, u}
 C] →       {f g : β → C} →         [inst_1 : CategoryTheory.Limits.HasCoproduct
 f] →           [inst_2 : CategoryTheory.Limits.HasCoproduct g] → ((b : β) → f b
 ⟶ g b) → (∐ f ⟶ ∐ g)
参数：(b : β) → f b ⟶ g b；∐ f ⟶ ∐ g。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Construct a morphism between categorical coproducts (indexed by the same type)
from a family of morphisms between the factors.
-/
def Sigma.map {f g : β → C} [HasCoproduct f] [HasCoproduct g] (p : ∀ b, f b ⟶ g b) :
    ∐ f ⟶ ∐ g :=
  colimMap (Discrete.natTrans fun X => p X.as)

@[reassoc (attr := simp)]
/-
**CategoryTheory.Limits.Sigma.** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.Limits`
。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma Sigma.ι_map {f g : β → C} [HasCoproduct f] [HasCoproduct g] (p : ∀ b, f b ⟶ g b) (b : β) :
    Sigma.ι f b ≫ Sigma.map p = p b ≫ Sigma.ι g b := by simp [Sigma.map]

@[simp]
/-
**CategoryTheory.Limits.Sigma.map_id** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.L
imits.Sigma`。
形式化陈述：∀ {α : Type w₂} {C : Type u} [inst : CategoryTheory.Category.{v, u} C] {f 
: α → C}   [inst_1 : CategoryTheory.Limits.HasCoproduct f],   (CategoryTheory.Li
mits.Sigma.map fun a => CategoryTheory.CategoryStruct.id (f a)) =     CategoryTh
eory.CategoryStruct.id (∐ f)
参数：CategoryTheory.Limits.Sigma.map fun a => CategoryTheory.CategoryStruct.id (f 
a)；∐ f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.Sigma.hom_ext`：∀ {β : Type w} {C : Type u} [inst :
 CategoryTheory.Category.{v, u} C] {f : β → C}   [inst_1 : CategoryTheory.Limits
.HasCoproduct f] {X : C} …
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Limits.Sigma.ι_map`：∀ {β : Type w} {C : Type u} [inst : C
ategoryTheory.Category.{v, u} C] {f g : β → C}   [inst_1 : CategoryTheory.Limits
.HasCoproduct f] [inst_…
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma Sigma.map_id {f : α → C} [HasCoproduct f] : Sigma.map (fun a => 𝟙 (f a)) = 𝟙 (∐ f) := by
  ext; simp
/-
**CategoryTheory.Limits.Sigma.map_comp_map** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTh
eory.Limits.Sigma`。
形式化陈述：∀ {α : Type w₂} {C : Type u} [inst : CategoryTheory.Category.{v, u} C] {f 
g h : α → C}   [inst_1 : CategoryTheory.Limits.HasCoproduct f] [inst_2 : Categor
yTheory.Limits.HasCoproduct g]   [inst_3 : CategoryTheory.Limits.HasCoproduct h]
 (q : (a : α) → f a ⟶ g a) (q' : (a : α) → g a ⟶ h a),   CategoryTheory.Category
Struct.comp (CategoryTheory.Limits.Sigma.map q) (CategoryTheory.Limits.Sigma.map
 q') =     CategoryTheory.Limits.Sigma.map fun a => CategoryTheory.CategoryStruc
t.comp (q a) (q' a)
参数：q : (a : α) → f a ⟶ g a；q' : (a : α) → g a ⟶ h a；CategoryTheory.Limits.Sigma.
map q；CategoryTheory.Limits.Sigma.map q'；q a；q' a。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.Sigma.hom_ext`：∀ {β : Type w} {C : Type u} [inst :
 CategoryTheory.Category.{v, u} C] {f : β → C}   [inst_1 : CategoryTheory.Limits
.HasCoproduct f] {X : C} …
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Limits.Sigma.ι_map_assoc`：∀ {β : Type w} {C : Type u} [in
st : CategoryTheory.Category.{v, u} C] {f g : β → C}   [inst_1 : CategoryTheory.
Limits.HasCoproduct f] [inst_…
· 使用定理 `CategoryTheory.Limits.Sigma.ι_map`：∀ {β : Type w} {C : Type u} [inst : C
ategoryTheory.Category.{v, u} C] {f g : β → C}   [inst_1 : CategoryTheory.Limits
.HasCoproduct f] [inst_…
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma Sigma.map_comp_map {f g h : α → C} [HasCoproduct f] [HasCoproduct g] [HasCoproduct h]
    (q : ∀ (a : α), f a ⟶ g a) (q' : ∀ (a : α), g a ⟶ h a) :
    Sigma.map q ≫ Sigma.map q' = Sigma.map (fun a => q a ≫ q' a) := by
  ext; simp
/-
**CategoryTheory.Limits.Sigma.map_epi** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.
Limits.Sigma`。
形式化陈述：∀ {β : Type w} {C : Type u} [inst : CategoryTheory.Category.{v, u} C] {f g
 : β → C}   [inst_1 : CategoryTheory.Limits.HasCoproduct f] [inst_2 : CategoryTh
eory.Limits.HasCoproduct g]   (p : (b : β) → f b ⟶ g b) [∀ (i : β), CategoryTheo
ry.Epi (p i)],   CategoryTheory.Epi (CategoryTheory.Limits.Sigma.map p)
参数：p : (b : β) → f b ⟶ g b；i : β；p i；CategoryTheory.Limits.Sigma.map p。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance Sigma.map_epi {f g : β → C} [HasCoproduct f] [HasCoproduct g] (p : ∀ b, f b ⟶ g b)
    [∀ i, Epi (p i)] : Epi <| Sigma.map p :=
  @Limits.colimMap_epi _ _ _ _ (Discrete.functor f) (Discrete.functor g) _ _
    (Discrete.natTrans fun X => p X.as) (by dsimp; infer_instance)

/-- Construct a morphism between categorical coproducts from a family of morphisms between the
factors. -/
/-
**CategoryTheory.Limits.Sigma.map'** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Lim
its.Sigma`。
形式化陈述：{β : Type w} →   {α : Type w₂} →     {C : Type u} →       [inst : Category
Theory.Category.{v, u} C] →         {f : α → C} →           {g : β → C} →       
      [inst_1 : CategoryTheory.Limits.HasCoproduct f] →               [inst_2 : 
CategoryTheory.Limits.HasCoproduct g] → (p : α → β) → ((a : α) → f a ⟶ g (p a)) 
→ (∐ f ⟶ ∐ g)
参数：p : α → β；(a : α) → f a ⟶ g (p a)；∐ f ⟶ ∐ g。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Construct a morphism between categorical coproducts from a family of morphisms b
etween the
factors.
-/
def Sigma.map' {f : α → C} {g : β → C} [HasCoproduct f] [HasCoproduct g] (p : α → β)
    (q : ∀ (a : α), f a ⟶ g (p a)) : ∐ f ⟶ ∐ g :=
  Sigma.desc (fun a => q a ≫ Sigma.ι _ _)

@[reassoc (attr := simp)]
/-
**CategoryTheory.Limits.Sigma.** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.Limits`
。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma Sigma.ι_comp_map' {f : α → C} {g : β → C} [HasCoproduct f] [HasCoproduct g]
    (p : α → β) (q : ∀ (a : α), f a ⟶ g (p a)) (a : α) :
    Sigma.ι f a ≫ Sigma.map' p q = q a ≫ Sigma.ι g (p a) :=
  colimit.ι_desc _ _
/-
**CategoryTheory.Limits.Sigma.map'_id_id** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheo
ry.Limits.Sigma`。
形式化陈述：∀ {α : Type w₂} {C : Type u} [inst : CategoryTheory.Category.{v, u} C] {f 
: α → C}   [inst_1 : CategoryTheory.Limits.HasCoproduct f],   (CategoryTheory.Li
mits.Sigma.map' id fun a => CategoryTheory.CategoryStruct.id (f a)) =     Catego
ryTheory.CategoryStruct.id (∐ f)
参数：CategoryTheory.Limits.Sigma.map' id fun a => CategoryTheory.CategoryStruct.id
 (f a)；∐ f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.Sigma.hom_ext`：∀ {β : Type w} {C : Type u} [inst :
 CategoryTheory.Category.{v, u} C] {f : β → C}   [inst_1 : CategoryTheory.Limits
.HasCoproduct f] {X : C} …
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Limits.Sigma.ι_comp_map'`：∀ {β : Type w} {α : Type w₂} {C
 : Type u} [inst : CategoryTheory.Category.{v, u} C] {f : α → C} {g : β → C}   [
inst_1 : CategoryTheory.Limit…
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma Sigma.map'_id_id {f : α → C} [HasCoproduct f] :
    Sigma.map' id (fun a => 𝟙 (f a)) = 𝟙 (∐ f) := by
  ext; simp

@[simp]
/-
**CategoryTheory.Limits.Sigma.map'_id** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.
Limits.Sigma`。
形式化陈述：∀ {α : Type w₂} {C : Type u} [inst : CategoryTheory.Category.{v, u} C] {f 
g : α → C}   [inst_1 : CategoryTheory.Limits.HasCoproduct f] [inst_2 : CategoryT
heory.Limits.HasCoproduct g]   (p : (b : α) → f b ⟶ g b), CategoryTheory.Limits.
Sigma.map' id p = CategoryTheory.Limits.Sigma.map p
参数：p : (b : α) → f b ⟶ g b。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma Sigma.map'_id {f g : α → C} [HasCoproduct f] [HasCoproduct g] (p : ∀ b, f b ⟶ g b) :
    Sigma.map' id p = Sigma.map p :=
  rfl
/-
**CategoryTheory.Limits.Sigma.map'_comp_map'** 是 Mathlib 中的一个定理，位于命名空间 `Category
Theory.Limits.Sigma`。
形式化陈述：∀ {β : Type w} {α : Type w₂} {γ : Type w₃} {C : Type u} [inst : CategoryTh
eory.Category.{v, u} C] {f : α → C}   {g : β → C} {h : γ → C} [inst_1 : Category
Theory.Limits.HasCoproduct f]   [inst_2 : CategoryTheory.Limits.HasCoproduct g] 
[inst_3 : CategoryTheory.Limits.HasCoproduct h] (p : α → β)   (p' : β → γ) (q : 
(a : α) → f a ⟶ g (p a)) (q' : (b : β) → g b ⟶ h (p' b)),   CategoryTheory.Categ
oryStruct.comp (CategoryTheory.Limits.Sigma.map' p q) (CategoryTheory.Limits.Sig
ma.map' p' q') =     CategoryTheory.Limits.Sigma.map' (p' ∘ p) fun a => Category
Theory.CategoryStruct.comp (q a) (q' (p a))
参数：p : α → β；p' : β → γ；q : (a : α) → f a ⟶ g (p a)；q' : (b : β) → g b ⟶ h (p' b
)；CategoryTheory.Limits.Sigma.map' p q；CategoryTheory.Limits.Sigma.map' p' q'；p'
 ∘ p；q a；q' (p a)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.Sigma.hom_ext`：∀ {β : Type w} {C : Type u} [inst :
 CategoryTheory.Category.{v, u} C] {f : β → C}   [inst_1 : CategoryTheory.Limits
.HasCoproduct f] {X : C} …
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Limits.Sigma.ι_comp_map'_assoc`：∀ {β : Type w} {α : Type 
w₂} {C : Type u} [inst : CategoryTheory.Category.{v, u} C] {f : α → C} {g : β → 
C}   [inst_1 : CategoryTheory.Limit…
· 使用定理 `CategoryTheory.Limits.Sigma.ι_comp_map'`：∀ {β : Type w} {α : Type w₂} {C
 : Type u} [inst : CategoryTheory.Category.{v, u} C] {f : α → C} {g : β → C}   [
inst_1 : CategoryTheory.Limit…
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma Sigma.map'_comp_map' {f : α → C} {g : β → C} {h : γ → C} [HasCoproduct f] [HasCoproduct g]
    [HasCoproduct h] (p : α → β) (p' : β → γ) (q : ∀ (a : α), f a ⟶ g (p a))
    (q' : ∀ (b : β), g b ⟶ h (p' b)) :
    Sigma.map' p q ≫ Sigma.map' p' q' = Sigma.map' (p' ∘ p) (fun a => q a ≫ q' (p a)) := by
  ext; simp
/-
**CategoryTheory.Limits.Sigma.map'_comp_map** 是 Mathlib 中的一个定理，位于命名空间 `CategoryT
heory.Limits.Sigma`。
形式化陈述：∀ {β : Type w} {α : Type w₂} {C : Type u} [inst : CategoryTheory.Category.
{v, u} C] {f : α → C} {g h : β → C}   [inst_1 : CategoryTheory.Limits.HasCoprodu
ct f] [inst_2 : CategoryTheory.Limits.HasCoproduct g]   [inst_3 : CategoryTheory
.Limits.HasCoproduct h] (p : α → β) (q : (a : α) → f a ⟶ g (p a)) (q' : (b : β) 
→ g b ⟶ h b),   CategoryTheory.CategoryStruct.comp (CategoryTheory.Limits.Sigma.
map' p q) (CategoryTheory.Limits.Sigma.map q') =     CategoryTheory.Limits.Sigma
.map' p fun a => CategoryTheory.CategoryStruct.comp (q a) (q' (p a))
参数：p : α → β；q : (a : α) → f a ⟶ g (p a)；q' : (b : β) → g b ⟶ h b；CategoryTheory
.Limits.Sigma.map' p q；CategoryTheory.Limits.Sigma.map q'；q a；q' (p a)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.Sigma.hom_ext`：∀ {β : Type w} {C : Type u} [inst :
 CategoryTheory.Category.{v, u} C] {f : β → C}   [inst_1 : CategoryTheory.Limits
.HasCoproduct f] {X : C} …
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Limits.Sigma.ι_comp_map'_assoc`：∀ {β : Type w} {α : Type 
w₂} {C : Type u} [inst : CategoryTheory.Category.{v, u} C] {f : α → C} {g : β → 
C}   [inst_1 : CategoryTheory.Limit…
· 使用定理 `CategoryTheory.Limits.Sigma.ι_map`：∀ {β : Type w} {C : Type u} [inst : C
ategoryTheory.Category.{v, u} C] {f g : β → C}   [inst_1 : CategoryTheory.Limits
.HasCoproduct f] [inst_…
· 使用定理 `CategoryTheory.Limits.Sigma.ι_comp_map'`：∀ {β : Type w} {α : Type w₂} {C
 : Type u} [inst : CategoryTheory.Category.{v, u} C] {f : α → C} {g : β → C}   [
inst_1 : CategoryTheory.Limit…
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma Sigma.map'_comp_map {f : α → C} {g h : β → C} [HasCoproduct f] [HasCoproduct g]
    [HasCoproduct h] (p : α → β) (q : ∀ (a : α), f a ⟶ g (p a)) (q' : ∀ (b : β), g b ⟶ h b) :
    Sigma.map' p q ≫ Sigma.map q' = Sigma.map' p (fun a => q a ≫ q' (p a)) := by
  ext; simp
/-
**CategoryTheory.Limits.Sigma.map_comp_map'** 是 Mathlib 中的一个定理，位于命名空间 `CategoryT
heory.Limits.Sigma`。
形式化陈述：∀ {β : Type w} {α : Type w₂} {C : Type u} [inst : CategoryTheory.Category.
{v, u} C] {f g : α → C} {h : β → C}   [inst_1 : CategoryTheory.Limits.HasCoprodu
ct f] [inst_2 : CategoryTheory.Limits.HasCoproduct g]   [inst_3 : CategoryTheory
.Limits.HasCoproduct h] (p : α → β) (q : (a : α) → f a ⟶ g a) (q' : (a : α) → g 
a ⟶ h (p a)),   CategoryTheory.CategoryStruct.comp (CategoryTheory.Limits.Sigma.
map q) (CategoryTheory.Limits.Sigma.map' p q') =     CategoryTheory.Limits.Sigma
.map' p fun a => CategoryTheory.CategoryStruct.comp (q a) (q' a)
参数：p : α → β；q : (a : α) → f a ⟶ g a；q' : (a : α) → g a ⟶ h (p a)；CategoryTheory
.Limits.Sigma.map q；CategoryTheory.Limits.Sigma.map' p q'；q a；q' a。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.Sigma.hom_ext`：∀ {β : Type w} {C : Type u} [inst :
 CategoryTheory.Category.{v, u} C] {f : β → C}   [inst_1 : CategoryTheory.Limits
.HasCoproduct f] {X : C} …
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Limits.Sigma.ι_map_assoc`：∀ {β : Type w} {C : Type u} [in
st : CategoryTheory.Category.{v, u} C] {f g : β → C}   [inst_1 : CategoryTheory.
Limits.HasCoproduct f] [inst_…
· 使用定理 `CategoryTheory.Limits.Sigma.ι_comp_map'`：∀ {β : Type w} {α : Type w₂} {C
 : Type u} [inst : CategoryTheory.Category.{v, u} C] {f : α → C} {g : β → C}   [
inst_1 : CategoryTheory.Limit…
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma Sigma.map_comp_map' {f g : α → C} {h : β → C} [HasCoproduct f] [HasCoproduct g]
    [HasCoproduct h] (p : α → β) (q : ∀ (a : α), f a ⟶ g a) (q' : ∀ (a : α), g a ⟶ h (p a)) :
    Sigma.map q ≫ Sigma.map' p q' = Sigma.map' p (fun a => q a ≫ q' a) := by
  ext; simp
/-
**CategoryTheory.Limits.Sigma.map'_eq** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.
Limits.Sigma`。
形式化陈述：∀ {β : Type w} {α : Type w₂} {C : Type u} [inst : CategoryTheory.Category.
{v, u} C] {f : α → C} {g : β → C}   [inst_1 : CategoryTheory.Limits.HasCoproduct
 f] [inst_2 : CategoryTheory.Limits.HasCoproduct g] {p p' : α → β}   {q : (a : α
) → f a ⟶ g (p a)} {q' : (a : α) → f a ⟶ g (p' a)} (hp : p = p'),   (∀ (a : α), 
CategoryTheory.CategoryStruct.comp (q a) (CategoryTheory.eqToHom ⋯) = q' a) →   
  CategoryTheory.Limits.Sigma.map' p q = CategoryTheory.Limits.Sigma.map' p' q'
参数：a : α；p a；a : α；p' a；hp : p = p'；∀ (a : α), CategoryTheory.CategoryStruct.com
p (q a) (CategoryTheory.eqToHom ⋯) = q' a。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.Sigma.hom_ext`：∀ {β : Type w} {C : Type u} [inst :
 CategoryTheory.Category.{v, u} C] {f : β → C}   [inst_1 : CategoryTheory.Limits
.HasCoproduct f] {X : C} …
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Limits.Sigma.ι_comp_map'`：∀ {β : Type w} {α : Type w₂} {C
 : Type u} [inst : CategoryTheory.Category.{v, u} C] {f : α → C} {g : β → C}   [
inst_1 : CategoryTheory.Limit…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma Sigma.map'_eq {f : α → C} {g : β → C} [HasCoproduct f] [HasCoproduct g]
    {p p' : α → β} {q : ∀ (a : α), f a ⟶ g (p a)} {q' : ∀ (a : α), f a ⟶ g (p' a)}
    (hp : p = p') (hq : ∀ (a : α), q a ≫ eqToHom (hp ▸ rfl) = q' a) :
    Sigma.map' p q = Sigma.map' p' q' := by
  cat_disch

/-- Construct an isomorphism between categorical coproducts (indexed by the same type)
from a family of isomorphisms between the factors.
-/
/-
**CategoryTheory.Limits.Sigma.mapIso** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.L
imits.Sigma`。
形式化陈述：{β : Type w} →   {C : Type u} →     [inst : CategoryTheory.Category.{v, u}
 C] →       {f g : β → C} → [inst_1 : CategoryTheory.Limits.HasCoproductsOfShape
 β C] → ((b : β) → f b ≅ g b) → (∐ f ≅ ∐ g)
参数：(b : β) → f b ≅ g b；∐ f ≅ ∐ g。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Construct an isomorphism between categorical coproducts (indexed by the same typ
e)
from a family of isomorphisms between the factors.
-/
def Sigma.mapIso {f g : β → C} [HasCoproductsOfShape β C] (p : ∀ b, f b ≅ g b) : ∐ f ≅ ∐ g :=
  colim.mapIso (Discrete.natIso fun X => p X.as)

@[reassoc (attr := simp)]
/-
**CategoryTheory.Limits.Sigma.** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.Limits`
。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma Sigma.ι_mapIso_hom {f g : β → C} [HasCoproductsOfShape β C] (p : ∀ b, f b ≅ g b) (b : β) :
    ι _ _ ≫ (Sigma.mapIso p).hom = (p b).hom ≫ ι _ _ :=
  ι_colimMap _ _

@[reassoc (attr := simp)]
/-
**CategoryTheory.Limits.Sigma.** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.Limits`
。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma Sigma.ι_mapIso_inv {f g : β → C} [HasCoproductsOfShape β C] (p : ∀ b, f b ≅ g b) (b : β) :
    ι _ _ ≫ (Sigma.mapIso p).inv = (p b).inv ≫ ι _ _ :=
  ι_colimMap _ _
/-
**CategoryTheory.Limits.Sigma.map_isIso** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheor
y.Limits.Sigma`。
形式化陈述：∀ {β : Type w} {C : Type u} [inst : CategoryTheory.Category.{v, u} C] {f g
 : β → C}   [inst_1 : CategoryTheory.Limits.HasCoproductsOfShape β C] (p : (b : 
β) → f b ⟶ g b)   [∀ (b : β), CategoryTheory.IsIso (p b)], CategoryTheory.IsIso 
(CategoryTheory.Limits.Sigma.map p)
参数：p : (b : β) → f b ⟶ g b；b : β；p b；CategoryTheory.Limits.Sigma.map p。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance Sigma.map_isIso {f g : β → C} [HasCoproductsOfShape β C] (p : ∀ b, f b ⟶ g b)
    [∀ b, IsIso <| p b] : IsIso (Sigma.map p) :=
  inferInstanceAs (IsIso (Sigma.mapIso (fun b ↦ asIso (p b))).hom)

section

/- In this section, we provide some API for coproducts when we are given a functor
`Discrete α ⥤ C` instead of a map `α → C`. -/

variable (X : Discrete α ⥤ C) [HasCoproduct (fun j => X.obj (Discrete.mk j))]

/-- A colimit cocone for `X : Discrete α ⥤ C` that is given
by `∐ (fun j => X.obj (Discrete.mk j))`. -/
@[simps]
/-
**CategoryTheory.Limits.Sigma.cocone** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.L
imits.Sigma`。
形式化陈述：{α : Type w₂} →   {C : Type u} →     [inst : CategoryTheory.Category.{v, u
} C] →       (X : CategoryTheory.Functor (CategoryTheory.Discrete α) C) →       
  [CategoryTheory.Limits.HasCoproduct fun j => X.obj { as := j }] → CategoryTheo
ry.Limits.Cocone X
参数：X : CategoryTheory.Functor (CategoryTheory.Discrete α) C。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A colimit cocone for `X : Discrete α ⥤ C` that is given
by `∐ (fun j => X.obj (Discrete.mk j))`.
-/
def Sigma.cocone : Cocone X where
  pt := ∐ (fun j => X.obj (Discrete.mk j))
  ι := Discrete.natTrans (fun _ => Sigma.ι (fun j ↦ X.obj ⟨j⟩) _)

set_option backward.defeqAttrib.useBackward true in
/-- The cocone `Sigma.cocone X` is a colimit cocone. -/
/-
**CategoryTheory.Limits.coproductIsCoproduct'** 是 Mathlib 中的一个定义，位于命名空间 `Categor
yTheory.Limits`。
形式化陈述：coproductIsCoproduct' : IsColimit (Sigma.cocone X) where desc s
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The cocone `Sigma.cocone X` is a colimit cocone.
-/
def coproductIsCoproduct' :
    IsColimit (Sigma.cocone X) where
  desc s := Sigma.desc (fun j => s.ι.app ⟨j⟩)
  fac s := by simp
  uniq s m hm := by
    dsimp
    ext
    simp only [colimit.ι_desc, Cofan.mk_pt, Cofan.mk_ι_app]
    apply hm

variable [HasColimit X]

/-- The isomorphism `∐ (fun j => X.obj (Discrete.mk j)) ≅ colimit X`. -/
/-
**CategoryTheory.Limits.Sigma.isoColimit** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheo
ry.Limits.Sigma`。
形式化陈述：{α : Type w₂} →   {C : Type u} →     [inst : CategoryTheory.Category.{v, u
} C] →       (X : CategoryTheory.Functor (CategoryTheory.Discrete α) C) →       
  [inst_1 : CategoryTheory.Limits.HasCoproduct fun j => X.obj { as := j }] →    
       [inst_2 : CategoryTheory.Limits.HasColimit X] →             (∐ fun j => X
.obj { as := j }) ≅ CategoryTheory.Limits.colimit X
参数：X : CategoryTheory.Functor (CategoryTheory.Discrete α) C；∐ fun j => X.obj { a
s := j }。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The isomorphism `∐ (fun j => X.obj (Discrete.mk j)) ≅ colimit X`.
-/
def Sigma.isoColimit :
    ∐ (fun j => X.obj (Discrete.mk j)) ≅ colimit X :=
  IsColimit.coconePointUniqueUpToIso (coproductIsCoproduct' X) (colimit.isColimit X)

@[reassoc (attr := simp)]
/-
**CategoryTheory.Limits.Sigma.** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.Limits`
。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma Sigma.ι_isoColimit_hom (j : α) :
    Sigma.ι _ j ≫ (Sigma.isoColimit X).hom = colimit.ι _ (Discrete.mk j) :=
  IsColimit.comp_coconePointUniqueUpToIso_hom (coproductIsCoproduct' X) _ _

@[reassoc (attr := simp)]
/-
**CategoryTheory.Limits.Sigma.** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.Limits`
。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma Sigma.ι_isoColimit_inv (j : α) :
    colimit.ι _ ⟨j⟩ ≫ (Sigma.isoColimit X).inv = Sigma.ι (fun j ↦ X.obj ⟨j⟩) _ :=
  IsColimit.comp_coconePointUniqueUpToIso_inv _ _ _

end

/-- Two products which differ by an equivalence in the indexing type,
and up to isomorphism in the factors, are isomorphic.
-/
@[simps]
/-
**CategoryTheory.Limits.Pi.whiskerEquiv** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheor
y.Limits.Pi`。
形式化陈述：{C : Type u} →   [inst : CategoryTheory.Category.{v, u} C] →     {J : Type
 u_1} →       {K : Type u_2} →         {f : J → C} →           {g : K → C} →    
         (e : J ≃ K) →               ((j : J) → g (e j) ≅ f j) →                
 [inst_1 : CategoryTheory.Limits.HasProduct f] →                   [inst_2 : Cat
egoryTheory.Limits.HasProduct g] → ∏ᶜ f ≅ ∏ᶜ g
参数：e : J ≃ K；(j : J) → g (e j) ≅ f j。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s

--- 原说明 ---
Two products which differ by an equivalence in the indexing type,
and up to isomorphism in the factors, are isomorphic.
-/
def Pi.whiskerEquiv {J K : Type*} {f : J → C} {g : K → C} (e : J ≃ K) (w : ∀ j, g (e j) ≅ f j)
    [HasProduct f] [HasProduct g] : ∏ᶜ f ≅ ∏ᶜ g where
  hom := Pi.map' e.symm fun k => (w (e.symm k)).inv ≫ eqToHom (by simp)
  inv := Pi.map' e fun j => (w j).hom

/-- Two coproducts which differ by an equivalence in the indexing type,
and up to isomorphism in the factors, are isomorphic.
-/
@[simps]
/-
**CategoryTheory.Limits.Sigma.whiskerEquiv** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTh
eory.Limits.Sigma`。
形式化陈述：{C : Type u} →   [inst : CategoryTheory.Category.{v, u} C] →     {J : Type
 u_1} →       {K : Type u_2} →         {f : J → C} →           {g : K → C} →    
         (e : J ≃ K) →               ((j : J) → g (e j) ≅ f j) →                
 [inst_1 : CategoryTheory.Limits.HasCoproduct f] →                   [inst_2 : C
ategoryTheory.Limits.HasCoproduct g] → ∐ f ≅ ∐ g
参数：e : J ≃ K；(j : J) → g (e j) ≅ f j。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s

--- 原说明 ---
Two coproducts which differ by an equivalence in the indexing type,
and up to isomorphism in the factors, are isomorphic.
-/
def Sigma.whiskerEquiv {J K : Type*} {f : J → C} {g : K → C} (e : J ≃ K) (w : ∀ j, g (e j) ≅ f j)
    [HasCoproduct f] [HasCoproduct g] : ∐ f ≅ ∐ g where
  hom := Sigma.map' e fun j => (w j).inv
  inv := Sigma.map' e.symm fun k => eqToHom (by simp) ≫ (w (e.symm k)).hom
/-
**CategoryTheory.Limits.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Limits`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {ι : Type*} (f : ι → Type*) (g : (i : ι) → (f i) → C)
    [∀ i, HasProduct (g i)] [HasProduct fun i => ∏ᶜ g i] :
    HasProduct fun p : Σ i, f i => g p.1 p.2 where
  exists_limit := Nonempty.intro
    { cone := Fan.mk (∏ᶜ fun i => ∏ᶜ g i) (fun X => Pi.π (fun i => ∏ᶜ g i) X.1 ≫ Pi.π (g X.1) X.2)
      isLimit := Fan.IsLimit.mk _ (fun s => Pi.lift fun b => Pi.lift fun c => s.proj ⟨b, c⟩)
        (by simp)
        (by intro s (m : _ ⟶ (∏ᶜ fun i ↦ ∏ᶜ g i)) w; aesop (add norm simp Sigma.forall)) }

/-- An iterated product is a product over a sigma type. -/
@[simps]
/-
**CategoryTheory.Limits.piPiIso** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Limits
`。
形式化陈述：piPiIso {ι : Type*} (f : ι -> Type*) (g : (i : ι) -> (f i) -> C) [forall i
, HasProduct (g i)] [HasProduct fun i => ∏ᶜ g i] : (∏ᶜ fun i => ∏ᶜ g i) ≅ (∏ᶜ fu
n p : Σ i, f i => g p.1 p.2) where hom
参数：f : ι -> Type*；g : (i : ι) -> (f i) -> C；g i。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.instHasProductSigmaFstSndOfPiObj`：∀ {C : Type u} [
inst : CategoryTheory.Category.{v, u} C] {ι : Type u_1} (f : ι → Type u_2) (g : 
(i : ι) → f i → C)   [inst_1 : ∀ (i : ι), Ca…

--- 原说明 ---
An iterated product is a product over a sigma type.
-/
def piPiIso {ι : Type*} (f : ι → Type*) (g : (i : ι) → (f i) → C)
    [∀ i, HasProduct (g i)] [HasProduct fun i => ∏ᶜ g i] :
    (∏ᶜ fun i => ∏ᶜ g i) ≅ (∏ᶜ fun p : Σ i, f i => g p.1 p.2) where
  hom := Pi.lift fun ⟨i, x⟩ => Pi.π _ i ≫ Pi.π _ x
  inv := Pi.lift fun i => Pi.lift fun x => Pi.π _ (⟨i, x⟩ : Σ i, f i)
/-
**CategoryTheory.Limits.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Limits`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {ι : Type*} (f : ι → Type*) (g : (i : ι) → (f i) → C)
    [∀ i, HasCoproduct (g i)] [HasCoproduct fun i => ∐ g i] :
    HasCoproduct fun p : Σ i, f i => g p.1 p.2 where
  exists_colimit := Nonempty.intro
    { cocone := Cofan.mk (∐ fun i => ∐ g i)
        (fun X => Sigma.ι (g X.1) X.2 ≫ Sigma.ι (fun i => ∐ g i) X.1)
      isColimit := Cofan.IsColimit.mk _
        (fun s => Sigma.desc fun b => Sigma.desc fun c => s.inj ⟨b, c⟩)
        (by simp)
        (by intro s (m : (∐ fun i ↦ ∐ g i) ⟶ _) w; aesop_cat (add norm simp Sigma.forall)) }

/-- An iterated coproduct is a coproduct over a sigma type. -/
@[simps]
/-
**CategoryTheory.Limits.sigmaSigmaIso** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.
Limits`。
形式化陈述：sigmaSigmaIso {ι : Type*} (f : ι -> Type*) (g : (i : ι) -> (f i) -> C) [fo
rall i, HasCoproduct (g i)] [HasCoproduct fun i => ∐ g i] : (∐ fun i => ∐ g i) ≅
 (∐ fun p : Σ i, f i => g p.1 p.2) where hom
参数：f : ι -> Type*；g : (i : ι) -> (f i) -> C；g i。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.instHasCoproductSigmaFstSndOfSigmaObj`：∀ {C : Type
 u} [inst : CategoryTheory.Category.{v, u} C] {ι : Type u_1} (f : ι → Type u_2) 
(g : (i : ι) → f i → C)   [inst_1 : ∀ (i : ι), Ca…

--- 原说明 ---
An iterated coproduct is a coproduct over a sigma type.
-/
def sigmaSigmaIso {ι : Type*} (f : ι → Type*) (g : (i : ι) → (f i) → C)
    [∀ i, HasCoproduct (g i)] [HasCoproduct fun i => ∐ g i] :
    (∐ fun i => ∐ g i) ≅ (∐ fun p : Σ i, f i => g p.1 p.2) where
  hom := Sigma.desc fun i => Sigma.desc fun x => Sigma.ι (fun p : Σ i, f i => g p.1 p.2) ⟨i, x⟩
  inv := Sigma.desc fun ⟨i, x⟩ => Sigma.ι (g i) x ≫ Sigma.ι (fun i => ∐ g i) i

section Comparison

variable {D : Type u₂} [Category.{v₂} D] (G : C ⥤ D)
variable (f : β → C)

/-- The comparison morphism for the product of `f`. This is an iso iff `G` preserves the product
of `f`, see `PreservesProduct.ofIsoComparison`. -/
/-
**CategoryTheory.Limits.piComparison** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.L
imits`。
形式化陈述：piComparison [HasProduct f] [HasProduct fun b => G.obj (f b)] : G.obj (∏ᶜ 
f) ⟶ ∏ᶜ fun b => G.obj (f b)
参数：f b。
该定义给出了一等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The comparison morphism for the product of `f`. This is an iso iff `G` preserves
 the product
of `f`, see `PreservesProduct.ofIsoComparison`.
-/
def piComparison [HasProduct f] [HasProduct fun b => G.obj (f b)] :
    G.obj (∏ᶜ f) ⟶ ∏ᶜ fun b => G.obj (f b) :=
  Pi.lift fun b => G.map (Pi.π f b)

@[reassoc (attr := simp), elementwise nosimp]
/-
**CategoryTheory.Limits.piComparison_comp_** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTh
eory.Limits`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem piComparison_comp_π [HasProduct f] [HasProduct fun b => G.obj (f b)] (b : β) :
    piComparison G f ≫ Pi.π _ b = G.map (Pi.π f b) :=
  limit.lift_π _ (Discrete.mk b)

@[reassoc (attr := simp)]
/-
**CategoryTheory.Limits.map_lift_piComparison** 是 Mathlib 中的一个定理，位于命名空间 `Categor
yTheory.Limits`。
形式化陈述：map_lift_piComparison [HasProduct f] [HasProduct fun b => G.obj (f b)] (P 
: C) (g : forall j, P ⟶ f j) : G.map (Pi.lift g) ≫ piComparison G f = Pi.lift fu
n j => G.map (g j)
参数：f b；P : C；g : forall j, P ⟶ f j。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.Pi.hom_ext`：∀ {β : Type w} {C : Type u} [inst : Ca
tegoryTheory.Category.{v, u} C] {f : β → C}   [inst_1 : CategoryTheory.Limits.Ha
sProduct f] {X : C} (g…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.Limits.piComparison_comp_π`：piComparison_comp_π [HasProdu
ct f] [HasProduct fun b => G.obj (f b)] (b : β) : piComparison G f ≫ Pi.π _ b = 
G.map (Pi.π f b)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.Functor.map_comp`：∀ {C : Type u₁} [inst : CategoryTheory.
Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]
   (self : CategoryTh…
· 使用定理 `CategoryTheory.Limits.limit.lift_π`：∀ {J : Type u₁} [inst : CategoryTheo
ry.Category.{v₁, u₁} J] {C : Type u} [inst_1 : CategoryTheory.Category.{v, u} C]
   {F : CategoryTheory.F…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem map_lift_piComparison [HasProduct f] [HasProduct fun b => G.obj (f b)] (P : C)
    (g : ∀ j, P ⟶ f j) : G.map (Pi.lift g) ≫ piComparison G f = Pi.lift fun j => G.map (g j) := by
  ext j
  simp only [Category.assoc, piComparison_comp_π, ← G.map_comp,
    limit.lift_π, Fan.mk_π_app]

/-- The comparison morphism for the coproduct of `f`. This is an iso iff `G` preserves the coproduct
of `f`, see `PreservesCoproduct.ofIsoComparison`. -/
/-
**CategoryTheory.Limits.sigmaComparison** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheor
y.Limits`。
形式化陈述：sigmaComparison [HasCoproduct f] [HasCoproduct fun b => G.obj (f b)] : ∐ (
fun b => G.obj (f b)) ⟶ G.obj (∐ f)
参数：f b。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The comparison morphism for the coproduct of `f`. This is an iso iff `G` preserv
es the coproduct
of `f`, see `PreservesCoproduct.ofIsoComparison`.
-/
def sigmaComparison [HasCoproduct f] [HasCoproduct fun b => G.obj (f b)] :
    ∐ (fun b => G.obj (f b)) ⟶ G.obj (∐ f) :=
  Sigma.desc fun b => G.map (Sigma.ι f b)

@[reassoc (attr := simp)]
/-
**CategoryTheory.Limits.** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.Limits`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem ι_comp_sigmaComparison [HasCoproduct f] [HasCoproduct fun b => G.obj (f b)] (b : β) :
    Sigma.ι _ b ≫ sigmaComparison G f = G.map (Sigma.ι f b) :=
  colimit.ι_desc _ (Discrete.mk b)

@[reassoc (attr := simp)]
/-
**CategoryTheory.Limits.sigmaComparison_map_desc** 是 Mathlib 中的一个定理，位于命名空间 `Cate
goryTheory.Limits`。
形式化陈述：sigmaComparison_map_desc [HasCoproduct f] [HasCoproduct fun b => G.obj (f 
b)] (P : C) (g : forall j, f j ⟶ P) : sigmaComparison G f ≫ G.map (Sigma.desc g)
 = Sigma.desc fun j => G.map (g j)
参数：f b；P : C；g : forall j, f j ⟶ P。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.Sigma.hom_ext`：∀ {β : Type w} {C : Type u} [inst :
 CategoryTheory.Category.{v, u} C] {f : β → C}   [inst_1 : CategoryTheory.Limits
.HasCoproduct f] {X : C} …
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Limits.ι_comp_sigmaComparison_assoc`：∀ {β : Type w} {C : 
Type u} [inst : CategoryTheory.Category.{v, u} C] {D : Type u₂}   [inst_1 : Cate
goryTheory.Category.{v₂, u₂} D] (G : Cat…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.Functor.map_comp`：∀ {C : Type u₁} [inst : CategoryTheory.
Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]
   (self : CategoryTh…
· 使用定理 `CategoryTheory.Limits.colimit.ι_desc`：∀ {J : Type u₁} [inst : CategoryTh
eory.Category.{v₁, u₁} J] {C : Type u} [inst_1 : CategoryTheory.Category.{v, u} 
C]   {F : CategoryTheory.F…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem sigmaComparison_map_desc [HasCoproduct f] [HasCoproduct fun b => G.obj (f b)] (P : C)
    (g : ∀ j, f j ⟶ P) :
    sigmaComparison G f ≫ G.map (Sigma.desc g) = Sigma.desc fun j => G.map (g j) := by
  ext j
  simp only [ι_comp_sigmaComparison_assoc, ← G.map_comp, colimit.ι_desc, Cofan.mk_ι_app]

/-- `F.mapCone c` being limiting is the same as the induced fan being limiting. -/
/-
**CategoryTheory.Limits.Fan.isLimitMapConeEquiv** 是 Mathlib 中的一个定义，位于命名空间 `Categ
oryTheory.Limits.Fan`。
形式化陈述：{C : Type u} →   [inst : CategoryTheory.Category.{v, u} C] →     {D : Type
 u₂} →       [inst_1 : CategoryTheory.Category.{v₂, u₂} D] →         (F : Catego
ryTheory.Functor C D) →           {ι : Type u_1} →             (X : ι → C) →    
           (c : CategoryTheory.Limits.Fan X) →                 CategoryTheory.Li
mits.IsLimit (F.mapCone c) ≃                   CategoryTheory.Limits.IsLimit (Ca
tegoryTheory.Limits.Fan.mk (F.obj c.pt) fun i => F.map (c.proj i))
参数：F : CategoryTheory.Functor C D；X : ι → C；c : CategoryTheory.Limits.Fan X；F.ma
pCone c；CategoryTheory.Limits.Fan.mk (F.obj c.pt) fun i => F.map (c.proj i)。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.trans`：Equiv.trans {s t u : Computation α} : s ~ t -> t ~ u -> s ~
 u
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s

--- 原说明 ---
`F.mapCone c` being limiting is the same as the induced fan being limiting.
-/
def Fan.isLimitMapConeEquiv (F : C ⥤ D) {ι : Type*} (X : ι → C) (c : Fan X) :
    IsLimit (F.mapCone c) ≃ IsLimit (Fan.mk _ fun i ↦ F.map (c.proj i)) :=
  (IsLimit.postcomposeHomEquiv Discrete.natIsoFunctor (F.mapCone c)).symm.trans <|
    IsLimit.equivIsoLimit (Cone.ext (Iso.refl _))

/-- `F.mapCocone c` being colimiting is the same as the induced cofan being colimiting. -/
/-
**CategoryTheory.Limits.Cofan.isColimitMapCoconeEquiv** 是 Mathlib 中的一个定义，位于命名空间 
`CategoryTheory.Limits.Cofan`。
形式化陈述：{C : Type u} →   [inst : CategoryTheory.Category.{v, u} C] →     {D : Type
 u₂} →       [inst_1 : CategoryTheory.Category.{v₂, u₂} D] →         (F : Catego
ryTheory.Functor C D) →           {ι : Type u_1} →             (X : ι → C) →    
           (c : CategoryTheory.Limits.Cofan X) →                 CategoryTheory.
Limits.IsColimit (F.mapCocone c) ≃                   CategoryTheory.Limits.IsCol
imit (CategoryTheory.Limits.Cofan.mk (F.obj c.pt) fun i => F.map (c.inj i))
参数：F : CategoryTheory.Functor C D；X : ι → C；c : CategoryTheory.Limits.Cofan X；F.
mapCocone c；CategoryTheory.Limits.Cofan.mk (F.obj c.pt) fun i => F.map (c.inj i)
。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.trans`：Equiv.trans {s t u : Computation α} : s ~ t -> t ~ u -> s ~
 u
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s

--- 原说明 ---
`F.mapCocone c` being colimiting is the same as the induced cofan being colimiti
ng.
-/
def Cofan.isColimitMapCoconeEquiv (F : C ⥤ D) {ι : Type*} (X : ι → C) (c : Cofan X) :
    IsColimit (F.mapCocone c) ≃ IsColimit (Cofan.mk _ fun i ↦ F.map (c.inj i)) :=
  (IsColimit.precomposeHomEquiv Discrete.natIsoFunctor.symm (F.mapCocone c)).symm.trans <|
    IsColimit.equivIsoColimit (Cocone.ext (Iso.refl _))

end Comparison

variable (C)

/-- An abbreviation for `Π J, HasLimitsOfShape (Discrete J) C` -/
/-
**CategoryTheory.Limits.HasProducts** 是 Mathlib 中的一个缩写定义，位于命名空间 `CategoryTheory.
Limits`。
形式化陈述：HasProducts
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An abbreviation for `Π J, HasLimitsOfShape (Discrete J) C`
-/
abbrev HasProducts :=
  ∀ J : Type w, HasLimitsOfShape (Discrete J) C

/-- An abbreviation for `Π J, HasColimitsOfShape (Discrete J) C` -/
/-
**CategoryTheory.Limits.HasCoproducts** 是 Mathlib 中的一个缩写定义，位于命名空间 `CategoryTheor
y.Limits`。
形式化陈述：HasCoproducts
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An abbreviation for `Π J, HasColimitsOfShape (Discrete J) C`
-/
abbrev HasCoproducts :=
  ∀ J : Type w, HasColimitsOfShape (Discrete J) C

variable {C}
/-
**CategoryTheory.Limits.hasProducts_shrink** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTh
eory.Limits`。
形式化陈述：hasProducts_shrink [HasProducts.{max w w'} C] : HasProducts.{w} C
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.hasLimitsOfShape_of_equivalence`：hasLimitsOfShape_
of_equivalence {J' : Type u₂} [Category.{v₂} J'] (e : J ≌ J') [HasLimitsOfShape 
J C] : HasLimitsOfShape J' C
-/
lemma hasProducts_shrink [HasProducts.{max w w'} C] : HasProducts.{w} C := fun J =>
  hasLimitsOfShape_of_equivalence (Discrete.equivalence Equiv.ulift : Discrete (ULift.{w'} J) ≌ _)
/-
**CategoryTheory.Limits.hasCoproducts_shrink** 是 Mathlib 中的一个引理，位于命名空间 `Category
Theory.Limits`。
形式化陈述：hasCoproducts_shrink [HasCoproducts.{max w w'} C] : HasCoproducts.{w} C
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.hasColimitsOfShape_of_equivalence`：hasColimitsOfSh
ape_of_equivalence {J' : Type u₂} [Category.{v₂} J'] (e : J ≌ J') [HasColimitsOf
Shape J C] : HasColimitsOfShape J' C
-/
lemma hasCoproducts_shrink [HasCoproducts.{max w w'} C] : HasCoproducts.{w} C := fun J =>
  hasColimitsOfShape_of_equivalence (Discrete.equivalence Equiv.ulift : Discrete (ULift.{w'} J) ≌ _)
/-
**CategoryTheory.Limits.has_smallest_products_of_hasProducts** 是 Mathlib 中的一个定理，
位于命名空间 `CategoryTheory.Limits`。
形式化陈述：has_smallest_products_of_hasProducts [HasProducts.{w} C] : HasProducts.{0}
 C
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Limits.hasProducts_shrink`：hasProducts_shrink [HasProduct
s.{max w w'} C] : HasProducts.{w} C
-/
theorem has_smallest_products_of_hasProducts [HasProducts.{w} C] : HasProducts.{0} C :=
  hasProducts_shrink
/-
**CategoryTheory.Limits.has_smallest_coproducts_of_hasCoproducts** 是 Mathlib 中的一
个定理，位于命名空间 `CategoryTheory.Limits`。
形式化陈述：has_smallest_coproducts_of_hasCoproducts [HasCoproducts.{w} C] : HasCoprod
ucts.{0} C
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Limits.hasCoproducts_shrink`：hasCoproducts_shrink [HasCop
roducts.{max w w'} C] : HasCoproducts.{w} C
-/
theorem has_smallest_coproducts_of_hasCoproducts [HasCoproducts.{w} C] : HasCoproducts.{0} C :=
  hasCoproducts_shrink
/-
**CategoryTheory.Limits.hasProducts_of_limit_fans** 是 Mathlib 中的一个定理，位于命名空间 `Cat
egoryTheory.Limits`。
形式化陈述：hasProducts_of_limit_fans (lf : forall {J : Type w} (f : J -> C), Fan f) (
lf_isLimit : forall {J : Type w} (f : J -> C), IsLimit (lf f)) : HasProducts.{w}
 C
参数：lf : forall {J : Type w} (f : J -> C), Fan f；lf_isLimit : forall {J : Type w}
 (f : J -> C), IsLimit (lf f)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.HasLimit.mk`：∀ {J : Type u₁} [inst : CategoryTheor
y.Category.{v₁, u₁} J] {C : Type u} [inst_1 : CategoryTheory.Category.{v, u} C] 
  {F : CategoryTheory.F…
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
-/
theorem hasProducts_of_limit_fans (lf : ∀ {J : Type w} (f : J → C), Fan f)
    (lf_isLimit : ∀ {J : Type w} (f : J → C), IsLimit (lf f)) : HasProducts.{w} C :=
  fun _ : Type w =>
  { has_limit := fun F =>
      HasLimit.mk
        ⟨(Cone.postcompose Discrete.natIsoFunctor.inv).obj (lf fun j => F.obj ⟨j⟩),
          (IsLimit.postcomposeInvEquiv _ _).symm (lf_isLimit _)⟩ }
/-
**CategoryTheory.Limits.hasCoproducts_of_colimit_cofans** 是 Mathlib 中的一个定理，位于命名空
间 `CategoryTheory.Limits`。
形式化陈述：hasCoproducts_of_colimit_cofans (cf : forall {J : Type w} (f : J -> C), Co
fan f) (cf_isColimit : forall {J : Type w} (f : J -> C), IsColimit (cf f)) : Has
Coproducts.{w} C
参数：cf : forall {J : Type w} (f : J -> C), Cofan f；cf_isColimit : forall {J : Typ
e w} (f : J -> C), IsColimit (cf f)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.HasColimit.mk`：∀ {J : Type u₁} [inst : CategoryThe
ory.Category.{v₁, u₁} J] {C : Type u} [inst_1 : CategoryTheory.Category.{v, u} C
]   {F : CategoryTheory.F…
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
-/
theorem hasCoproducts_of_colimit_cofans (cf : ∀ {J : Type w} (f : J → C), Cofan f)
    (cf_isColimit : ∀ {J : Type w} (f : J → C), IsColimit (cf f)) : HasCoproducts.{w} C :=
  fun _ : Type w =>
  { has_colimit := fun F =>
      HasColimit.mk
        ⟨(Cocone.precompose Discrete.natIsoFunctor.hom).obj (cf fun j => F.obj ⟨j⟩),
          (IsColimit.precomposeHomEquiv _ _).symm (cf_isColimit _)⟩ }
/-
**CategoryTheory.Limits.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Limits`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 100) hasProductsOfShape_of_hasProducts [HasProducts.{w} C] (J : Type w) :
    HasProductsOfShape J C := inferInstance
/-
**CategoryTheory.Limits.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Limits`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 100) hasCoproductsOfShape_of_hasCoproducts [HasCoproducts.{w} C]
    (J : Type w) : HasCoproductsOfShape J C := inferInstance

open Opposite in
/-- The functor sending `(X, n)` to the product of copies of `X` indexed by `n`. -/
@[implicit_reducible, simps]
/-
**CategoryTheory.Limits.piConst** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Limits
`。
形式化陈述：piConst [Limits.HasProducts.{w} C] : C ⥤ Type wᵒᵖ ⥤ C where obj X
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The functor sending `(X, n)` to the product of copies of `X` indexed by `n`.
-/
def piConst [Limits.HasProducts.{w} C] : C ⥤ Type wᵒᵖ ⥤ C where
  obj X := { obj n := ∏ᶜ fun _ : (unop n :) ↦ X, map f := Limits.Pi.map' f.unop fun _ ↦ 𝟙 _ }
  map f := { app n := Limits.Pi.map fun _ ↦ f }

/-- `n ↦ ∏ₙ X` is left adjoint to `Hom(-, X)`. -/
/-
**CategoryTheory.Limits.piConstAdj** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Lim
its`。
形式化陈述：piConstAdj [Limits.HasProducts.{v} C] (X : C) : (piConst.obj X).rightOp ⊣ 
yoneda.obj X where unit
参数：X : C。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`n ↦ ∏ₙ X` is left adjoint to `Hom(-, X)`.
-/
def piConstAdj [Limits.HasProducts.{v} C] (X : C) :
    (piConst.obj X).rightOp ⊣ yoneda.obj X where
  unit := { app n := ↾fun i ↦ Limits.Pi.π (fun _ : n ↦ X) i }
  counit :=
  { app Y := (Limits.Pi.lift id).op,
    naturality _ _ _ := by apply Quiver.Hom.unop_inj; cat_disch }
  left_triangle_components _ := by apply Quiver.Hom.unop_inj; cat_disch

/-- The functor sending `(X, n)` to the coproduct of copies of `X` indexed by `n`. -/
@[implicit_reducible, simps]
/-
**CategoryTheory.Limits.sigmaConst** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Lim
its`。
形式化陈述：sigmaConst [Limits.HasCoproducts.{w} C] : C ⥤ Type w ⥤ C where obj X
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The functor sending `(X, n)` to the coproduct of copies of `X` indexed by `n`.
-/
def sigmaConst [Limits.HasCoproducts.{w} C] : C ⥤ Type w ⥤ C where
  obj X := { obj n := ∐ fun _ : n ↦ X, map f := Limits.Sigma.map' f fun _ ↦ 𝟙 _ }
  map f := { app n := Limits.Sigma.map fun _ ↦ f }

/-- `n ↦ ∐ₙ X` is left adjoint to `Hom(X, -)`. -/
/-
**CategoryTheory.Limits.sigmaConstAdj** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.
Limits`。
形式化陈述：sigmaConstAdj [Limits.HasCoproducts.{v} C] (X : C) : sigmaConst.obj X ⊣ co
yoneda.obj (Opposite.op X) where unit
参数：X : C。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`n ↦ ∐ₙ X` is left adjoint to `Hom(X, -)`.
-/
def sigmaConstAdj [Limits.HasCoproducts.{v} C] (X : C) :
    sigmaConst.obj X ⊣ coyoneda.obj (Opposite.op X) where
  unit := { app n := ↾fun i ↦ Limits.Sigma.ι (fun _ : n ↦ X) i }
  counit := { app Y := Limits.Sigma.desc id }

/-!
(Co)products over a type with a unique term.
-/


section Unique

/-- The limit cone for the product over an index type with exactly one term. -/
@[simps]
/-
**CategoryTheory.Limits.limitConeOfUnique** 是 Mathlib 中的一个定义，位于命名空间 `CategoryThe
ory.Limits`。
形式化陈述：limitConeOfUnique [Unique β] (f : β -> C) : LimitCone (Discrete.functor f)
 where cone
参数：f : β -> C。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The limit cone for the product over an index type with exactly one term.
-/
def limitConeOfUnique [Unique β] (f : β → C) : LimitCone (Discrete.functor f) where
  cone :=
    { pt := f default
      π := Discrete.natTrans (fun ⟨j⟩ => eqToHom (by
        dsimp
        congr
        subsingleton)) }
  isLimit :=
    { lift := fun s => s.π.app default
      fac := fun s j => by
        obtain rfl := Subsingleton.elim j default
        simp
      uniq := fun s m w => by
        specialize w default
        simpa using w }
/-
**CategoryTheory.Limits.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Limits`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 100) hasProduct_unique [Nonempty β] [Subsingleton β] (f : β → C) :
    HasProduct f :=
  let ⟨_⟩ := nonempty_unique β; HasLimit.mk (limitConeOfUnique f)

/-- A product over an index type with exactly one term is just the object over that term. -/
/-
**CategoryTheory.Limits.productUniqueIso** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheo
ry.Limits`。
形式化陈述：productUniqueIso [Unique β] (f : β -> C) : ∏ᶜ f ≅ f default
参数：f : β -> C。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A product over an index type with exactly one term is just the object over that 
term.
-/
def productUniqueIso [Unique β] (f : β → C) : ∏ᶜ f ≅ f default :=
  IsLimit.conePointUniqueUpToIso (limit.isLimit _) (limitConeOfUnique f).isLimit

@[simp]
/-
**CategoryTheory.Limits.productUniqueIso_hom** 是 Mathlib 中的一个引理，位于命名空间 `Category
Theory.Limits`。
形式化陈述：productUniqueIso_hom [Unique β] (f : β -> C) : (productUniqueIso f).hom = 
Pi.π f default
参数：f : β -> C。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.hasProduct_unique`：∀ {β : Type w} {C : Type u} [in
st : CategoryTheory.Category.{v, u} C] [Nonempty β] [Subsingleton β] (f : β → C)
,   CategoryTheory.Limits.Has…
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `Unique.instSubsingleton`：∀ {α : Sort u_1} [Unique α], Subsingleton α
-/
lemma productUniqueIso_hom [Unique β] (f : β → C) : (productUniqueIso f).hom = Pi.π f default :=
  rfl

@[reassoc (attr := simp)]
/-
**CategoryTheory.Limits.productUniqueIso_inv_** 是 Mathlib 中的一个引理，位于命名空间 `Categor
yTheory.Limits`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma productUniqueIso_inv_π [Unique β] (f : β → C) (b : β) :
    (productUniqueIso f).inv ≫ Pi.π f b = eqToHom (congrArg _ <| Subsingleton.allEq _ _) := by
  obtain rfl := Subsingleton.allEq b default
  simp [Iso.inv_comp_eq]

@[deprecated (since := "2026-06-30")] alias productUniqueIso_inv := productUniqueIso_inv_π

/-- Any isomorphism is the projection from a single object product. -/
/-
**CategoryTheory.Limits.Fan.isLimitMkOfUnique** 是 Mathlib 中的一个定义，位于命名空间 `Categor
yTheory.Limits.Fan`。
形式化陈述：{C : Type u} →   [inst : CategoryTheory.Category.{v, u} C] →     {X Y : C}
 →       (e : X ≅ Y) →         (J : Type u_1) → [Unique J] → CategoryTheory.Limi
ts.IsLimit (CategoryTheory.Limits.Fan.mk X fun x => e.hom)
参数：e : X ≅ Y；J : Type u_1；CategoryTheory.Limits.Fan.mk X fun x => e.hom。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Any isomorphism is the projection from a single object product.
-/
def Fan.isLimitMkOfUnique {X Y : C} (e : X ≅ Y) (J : Type*) [Unique J] :
    IsLimit (Fan.mk X fun _ : J ↦ e.hom) := by
  refine Fan.IsLimit.mk _ (fun s ↦ s.proj default ≫ e.inv) (fun s j ↦ ?_) fun s m hm ↦ ?_
  · obtain rfl : j = default := Subsingleton.elim _ _
    simp
  · simpa [← cancel_mono e.hom] using hm default

/-- The colimit cocone for the coproduct over an index type with exactly one term. -/
@[simps]
/-
**CategoryTheory.Limits.colimitCoconeOfUnique** 是 Mathlib 中的一个定义，位于命名空间 `Categor
yTheory.Limits`。
形式化陈述：colimitCoconeOfUnique [Unique β] (f : β -> C) : ColimitCocone (Discrete.fu
nctor f) where cocone
参数：f : β -> C。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The colimit cocone for the coproduct over an index type with exactly one term.
-/
def colimitCoconeOfUnique [Unique β] (f : β → C) : ColimitCocone (Discrete.functor f) where
  cocone :=
    { pt := f default
      ι := Discrete.natTrans (fun ⟨j⟩ => eqToHom (by
        dsimp
        congr
        subsingleton)) }
  isColimit :=
    { desc := fun s => s.ι.app default
      fac := fun s j => by
        obtain rfl := Subsingleton.elim j default
        apply Category.id_comp
      uniq := fun s m w => by
        specialize w default
        simp_all }
/-
**CategoryTheory.Limits.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Limits`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 100) hasCoproduct_unique [Nonempty β] [Subsingleton β] (f : β → C) :
    HasCoproduct f :=
  let ⟨_⟩ := nonempty_unique β; HasColimit.mk (colimitCoconeOfUnique f)

/-- A coproduct over an index type with exactly one term is just the object over that term. -/
/-
**CategoryTheory.Limits.coproductUniqueIso** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTh
eory.Limits`。
形式化陈述：coproductUniqueIso [Unique β] (f : β -> C) : ∐ f ≅ f default
参数：f : β -> C。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A coproduct over an index type with exactly one term is just the object over tha
t term.
-/
def coproductUniqueIso [Unique β] (f : β → C) : ∐ f ≅ f default :=
  IsColimit.coconePointUniqueUpToIso (colimit.isColimit _) (colimitCoconeOfUnique f).isColimit

@[simp]
/-
**CategoryTheory.Limits.coproductUniqueIso_inv** 是 Mathlib 中的一个引理，位于命名空间 `Catego
ryTheory.Limits`。
形式化陈述：coproductUniqueIso_inv [Unique β] (f : β -> C) : (coproductUniqueIso f).in
v = Sigma.ι f default
参数：f : β -> C。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.hasCoproduct_unique`：∀ {β : Type w} {C : Type u} [
inst : CategoryTheory.Category.{v, u} C] [Nonempty β] [Subsingleton β] (f : β → 
C),   CategoryTheory.Limits.Has…
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `Unique.instSubsingleton`：∀ {α : Sort u_1} [Unique α], Subsingleton α
-/
lemma coproductUniqueIso_inv [Unique β] (f : β → C) :
    (coproductUniqueIso f).inv = Sigma.ι f default :=
  rfl

@[reassoc (attr := simp)]
/-
**CategoryTheory.Limits.** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.Limits`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma ι_coproductUniqueIso_hom [Unique β] (f : β → C) (b : β) :
    Sigma.ι f b ≫ (coproductUniqueIso f).hom = eqToHom (congrArg _ <| Subsingleton.allEq _ _) := by
  obtain rfl := Subsingleton.allEq b default
  symm
  simp [← Iso.comp_inv_eq]

@[deprecated (since := "2026-06-30")] alias coproductUniqueIso_hom := ι_coproductUniqueIso_hom

/-- Any isomorphism is the projection from a single object product. -/
/-
**CategoryTheory.Limits.Cofan.isColimitMkOfUnique** 是 Mathlib 中的一个定义，位于命名空间 `Cat
egoryTheory.Limits.Cofan`。
形式化陈述：{C : Type u} →   [inst : CategoryTheory.Category.{v, u} C] →     {X Y : C}
 →       (e : X ≅ Y) →         (J : Type u_1) → [Unique J] → CategoryTheory.Limi
ts.IsColimit (CategoryTheory.Limits.Cofan.mk Y fun x => e.hom)
参数：e : X ≅ Y；J : Type u_1；CategoryTheory.Limits.Cofan.mk Y fun x => e.hom。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Any isomorphism is the projection from a single object product.
-/
def Cofan.isColimitMkOfUnique {X Y : C} (e : X ≅ Y) (J : Type*) [Unique J] :
    IsColimit (Cofan.mk Y fun _ : J ↦ e.hom) := by
  refine Cofan.IsColimit.mk _ (fun s ↦ e.inv ≫ s.inj default) (fun s j ↦ ?_) fun s m hm ↦ ?_
  · obtain rfl : j = default := Subsingleton.elim _ _
    simp
  · simpa [← cancel_epi e.hom] using hm default

end Unique

section Reindex

variable {γ : Type w'} (ε : β ≃ γ) (f : γ → C)

section

variable [HasProduct f] [HasProduct (f ∘ ε)]

/-- Reindex a categorical product via an equivalence of the index types. -/
/-
**CategoryTheory.Limits.Pi.reindex** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Lim
its.Pi`。
形式化陈述：{β : Type w} →   {C : Type u} →     [inst : CategoryTheory.Category.{v, u}
 C] →       {γ : Type w'} →         (ε : β ≃ γ) →           (f : γ → C) →       
      [inst_1 : CategoryTheory.Limits.HasProduct f] →               [inst_2 : Ca
tegoryTheory.Limits.HasProduct (f ∘ ⇑ε)] → ∏ᶜ f ∘ ⇑ε ≅ ∏ᶜ f
参数：ε : β ≃ γ；f : γ → C；f ∘ ⇑ε。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Reindex a categorical product via an equivalence of the index types.
-/
def Pi.reindex : piObj (f ∘ ε) ≅ piObj f :=
  HasLimit.isoOfEquivalence (Discrete.equivalence ε) (Discrete.natIso fun _ => Iso.refl _)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
/-
**CategoryTheory.Limits.Pi.reindex_hom_** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheor
y.Limits`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem Pi.reindex_hom_π (b : β) : (Pi.reindex ε f).hom ≫ Pi.π f (ε b) = Pi.π (f ∘ ε) b := by
  dsimp [Pi.reindex]
  simp only [HasLimit.isoOfEquivalence_hom_π, Discrete.equivalence_inverse, Discrete.functor_obj,
    Function.comp_apply, Functor.id_obj, Discrete.equivalence_functor, Functor.comp_obj,
    Discrete.natIso_inv_app, Iso.refl_inv, Category.id_comp]
  exact limit.w (Discrete.functor (f ∘ ε)) (Discrete.eqToHom' (ε.symm_apply_apply b))

@[reassoc (attr := simp)]
/-
**CategoryTheory.Limits.Pi.reindex_inv_** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheor
y.Limits`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem Pi.reindex_inv_π (b : β) : (Pi.reindex ε f).inv ≫ Pi.π (f ∘ ε) b = Pi.π f (ε b) := by
  simp [Iso.inv_comp_eq]

variable {f} in
/-- Being a limiting fan is stable under equivalences in the index type. -/
/-
**CategoryTheory.Limits.Fan.isLimitEquivOfEquiv** 是 Mathlib 中的一个定义，位于命名空间 `Categ
oryTheory.Limits.Fan`。
形式化陈述：{β : Type w} →   {C : Type u} →     [inst : CategoryTheory.Category.{v, u}
 C] →       {γ : Type w'} →         (ε : β ≃ γ) →           {f : γ → C} →       
      (c : CategoryTheory.Limits.Fan f) →               CategoryTheory.Limits.Is
Limit c ≃                 CategoryTheory.Limits.IsLimit (CategoryTheory.Limits.F
an.mk c.pt fun i => c.proj (ε i))
参数：ε : β ≃ γ；c : CategoryTheory.Limits.Fan f；CategoryTheory.Limits.Fan.mk c.pt f
un i => c.proj (ε i)。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Being a limiting fan is stable under equivalences in the index type.
-/
def Fan.isLimitEquivOfEquiv (c : Fan f) :
    IsLimit c ≃ IsLimit (Fan.mk _ fun i : β ↦ c.proj (ε i)) :=
  IsLimit.whiskerEquivalenceEquiv (Discrete.equivalence ε)

end

section

variable [HasCoproduct f] [HasCoproduct (f ∘ ε)]

/-- Reindex a categorical coproduct via an equivalence of the index types. -/
/-
**CategoryTheory.Limits.Sigma.reindex** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.
Limits.Sigma`。
形式化陈述：{β : Type w} →   {C : Type u} →     [inst : CategoryTheory.Category.{v, u}
 C] →       {γ : Type w'} →         (ε : β ≃ γ) →           (f : γ → C) →       
      [inst_1 : CategoryTheory.Limits.HasCoproduct f] →               [inst_2 : 
CategoryTheory.Limits.HasCoproduct (f ∘ ⇑ε)] → ∐ f ∘ ⇑ε ≅ ∐ f
参数：ε : β ≃ γ；f : γ → C；f ∘ ⇑ε。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Reindex a categorical coproduct via an equivalence of the index types.
-/
def Sigma.reindex : sigmaObj (f ∘ ε) ≅ sigmaObj f :=
  HasColimit.isoOfEquivalence (Discrete.equivalence ε) (Discrete.natIso fun _ => Iso.refl _)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
/-
**CategoryTheory.Limits.Sigma.** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.Limits`
。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem Sigma.ι_reindex_hom (b : β) :
    Sigma.ι (f ∘ ε) b ≫ (Sigma.reindex ε f).hom = Sigma.ι f (ε b) := by
  dsimp [Sigma.reindex]
  simp only [HasColimit.ι_isoOfEquivalence_hom, Functor.id_obj, Discrete.functor_obj,
    Function.comp_apply, Discrete.equivalence_functor, Discrete.equivalence_inverse,
    Functor.comp_obj, Discrete.natIso_inv_app, Iso.refl_inv, Category.id_comp]
  have h := colimit.w (Discrete.functor f) (Discrete.eqToHom' (ε.apply_symm_apply (ε b)))
  simp only [Discrete.functor_obj] at h
  erw [← h, eqToHom_map, eqToHom_map, eqToHom_trans_assoc]
  all_goals { simp }

@[reassoc (attr := simp)]
/-
**CategoryTheory.Limits.Sigma.** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.Limits`
。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem Sigma.ι_reindex_inv (b : β) :
    Sigma.ι f (ε b) ≫ (Sigma.reindex ε f).inv = Sigma.ι (f ∘ ε) b := by simp [Iso.comp_inv_eq]

variable {f} in
/-- Being a colimiting cofan is stable under equivalences in the index type. -/
/-
**CategoryTheory.Limits.Cofan.isColimitEquivOfEquiv** 是 Mathlib 中的一个定义，位于命名空间 `C
ategoryTheory.Limits.Cofan`。
形式化陈述：{β : Type w} →   {C : Type u} →     [inst : CategoryTheory.Category.{v, u}
 C] →       {γ : Type w'} →         (ε : β ≃ γ) →           {f : γ → C} →       
      (c : CategoryTheory.Limits.Cofan f) →               CategoryTheory.Limits.
IsColimit c ≃                 CategoryTheory.Limits.IsColimit (CategoryTheory.Li
mits.Cofan.mk c.pt fun i => c.inj (ε i))
参数：ε : β ≃ γ；c : CategoryTheory.Limits.Cofan f；CategoryTheory.Limits.Cofan.mk c.
pt fun i => c.inj (ε i)。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Being a colimiting cofan is stable under equivalences in the index type.
-/
def Cofan.isColimitEquivOfEquiv (c : Cofan f) :
    IsColimit c ≃ IsColimit (Cofan.mk _ fun i : β ↦ c.inj (ε i)) :=
  IsColimit.whiskerEquivalenceEquiv (Discrete.equivalence ε)

end

end Reindex

section

variable {J : Type u₂} [Category.{v₂} J] (F : J ⥤ C)

/-
**CategoryTheory.Limits.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Limits`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [HasLimit F] [HasProduct F.obj] : Mono (Pi.lift (limit.π F)) where
  right_cancellation _ _ h := by
    refine limit.hom_ext fun j => ?_
    simpa using h =≫ Pi.π _ j
/-
**CategoryTheory.Limits.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Limits`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [HasColimit F] [HasCoproduct F.obj] : Epi (Sigma.desc (colimit.ι F)) where
  left_cancellation _ _ h := by
    refine colimit.hom_ext fun j => ?_
    simpa using Sigma.ι _ j ≫= h

end

section Thin

variable [Quiver.IsThin C] {J : Type*} [Category* J] {K : J ⥤ C}

/-- If `K : J ⥤ C` is a diagram with `C` thin, a cone for `K` is limiting
if and only if the cone point is the product of the components. -/
/-
**CategoryTheory.Limits.isLimitEquivFanOfIsThin** 是 Mathlib 中的一个定义，位于命名空间 `Categ
oryTheory.Limits`。
形式化陈述：isLimitEquivFanOfIsThin (c : Cone K) : IsLimit c ≃ IsLimit (Fan.mk c.pt c.
π.app) where toFun hc
参数：c : Cone K。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `K : J ⥤ C` is a diagram with `C` thin, a cone for `K` is limiting
if and only if the cone point is the product of the components.
-/
def isLimitEquivFanOfIsThin (c : Cone K) : IsLimit c ≃ IsLimit (Fan.mk c.pt c.π.app) where
  toFun hc := Fan.IsLimit.mk _ (fun s ↦ hc.lift { pt := s.pt, π.app j := s.proj j })
    (by subsingleton) (by subsingleton)
  invFun h := { lift s := Fan.IsLimit.lift h s.π.app }

/-- If `K : J ⥤ C` is a diagram with `C` thin, a cone for `K` is limiting
if and only if the cone point is the product of the components. -/
/-
**CategoryTheory.Limits.isColimitEquivCofanOfIsThin** 是 Mathlib 中的一个定义，位于命名空间 `C
ategoryTheory.Limits`。
形式化陈述：isColimitEquivCofanOfIsThin (c : Cocone K) : IsColimit c ≃ IsColimit (Cofa
n.mk c.pt c.ι.app) where toFun hc
参数：c : Cocone K。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `K : J ⥤ C` is a diagram with `C` thin, a cone for `K` is limiting
if and only if the cone point is the product of the components.
-/
def isColimitEquivCofanOfIsThin (c : Cocone K) :
    IsColimit c ≃ IsColimit (Cofan.mk c.pt c.ι.app) where
  toFun hc := Cofan.IsColimit.mk _ (fun s ↦ hc.desc { pt := s.pt, ι.app j := s.inj j })
    (by subsingleton) (by subsingleton)
  invFun h := { desc s := Cofan.IsColimit.desc h s.ι.app }

end Thin

section Fubini

variable {ι ι' : Type*} {X : ι → ι' → C}

/-- A product over products is a product indexed by a product. -/
/-
**CategoryTheory.Limits.Fan.IsLimit.prod** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheo
ry.Limits.Fan.IsLimit`。
形式化陈述：{C : Type u} →   [inst : CategoryTheory.Category.{v, u} C] →     {ι : Type
 u_1} →       {ι' : Type u_2} →         {X : ι → ι' → C} →           (c : (i : ι
) → CategoryTheory.Limits.Fan fun j => X i j) →             ((i : ι) → CategoryT
heory.Limits.IsLimit (c i)) →               (c' : CategoryTheory.Limits.Fan fun 
i => (c i).pt) →                 CategoryTheory.Limits.IsLimit c' →             
      CategoryTheory.Limits.IsLimit                     (CategoryTheory.Limits.F
an.mk c'.pt fun p =>                       CategoryTheory.CategoryStruct.comp (c
'.proj p.1) ((c p.1).proj p.2))
参数：c : (i : ι) → CategoryTheory.Limits.Fan fun j => X i j；(i : ι) → CategoryTheo
ry.Limits.IsLimit (c i)；c' : CategoryTheory.Limits.Fan fun i => (c i).pt；Categor
yTheory.Limits.Fan.mk c'.pt fun p =>                       CategoryTheory.Catego
ryStruct.comp (c'.proj p.1) ((c p.1).proj p.2)。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A product over products is a product indexed by a product.
-/
def Fan.IsLimit.prod (c : ∀ i : ι, Fan (fun j : ι' ↦ X i j)) (hc : ∀ i : ι, IsLimit (c i))
    (c' : Fan (fun i : ι ↦ (c i).pt)) (hc' : IsLimit c') :
    (IsLimit <| Fan.mk c'.pt fun p : ι × ι' ↦ c'.proj _ ≫ (c p.1).proj p.2) := by
  refine Fan.IsLimit.mk _ (fun t ↦ ?_) ?_ fun t m hm ↦ ?_
  · exact Fan.IsLimit.lift hc' fun i ↦ Fan.IsLimit.lift (hc i) fun j ↦ t.proj (i, j)
  · simp
  · refine Fan.IsLimit.hom_ext hc' _ _ fun i ↦ ?_
    exact Fan.IsLimit.hom_ext (hc i) _ _ fun j ↦ (by simpa using hm (i, j))

/-- A coproduct over coproducts is a coproduct indexed by a product. -/
/-
**CategoryTheory.Limits.Cofan.IsColimit.prod** 是 Mathlib 中的一个定义，位于命名空间 `Category
Theory.Limits.Cofan.IsColimit`。
形式化陈述：{C : Type u} →   [inst : CategoryTheory.Category.{v, u} C] →     {ι : Type
 u_1} →       {ι' : Type u_2} →         {X : ι → ι' → C} →           (c : (i : ι
) → CategoryTheory.Limits.Cofan fun j => X i j) →             ((i : ι) → Categor
yTheory.Limits.IsColimit (c i)) →               (c' : CategoryTheory.Limits.Cofa
n fun i => (c i).pt) →                 CategoryTheory.Limits.IsColimit c' →     
              CategoryTheory.Limits.IsColimit                     (CategoryTheor
y.Limits.Cofan.mk c'.pt fun p =>                       CategoryTheory.CategorySt
ruct.comp ((c p.1).inj p.2) (c'.inj p.1))
参数：c : (i : ι) → CategoryTheory.Limits.Cofan fun j => X i j；(i : ι) → CategoryTh
eory.Limits.IsColimit (c i)；c' : CategoryTheory.Limits.Cofan fun i => (c i).pt；C
ategoryTheory.Limits.Cofan.mk c'.pt fun p =>                       CategoryTheor
y.CategoryStruct.comp ((c p.1).inj p.2) (c'.inj p.1)。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A coproduct over coproducts is a coproduct indexed by a product.
-/
def Cofan.IsColimit.prod (c : ∀ i : ι, Cofan (fun j : ι' ↦ X i j)) (hc : ∀ i : ι, IsColimit (c i))
    (c' : Cofan (fun i : ι ↦ (c i).pt)) (hc' : IsColimit c') :
    (IsColimit <| Cofan.mk c'.pt fun p : ι × ι' ↦ (c p.1).inj p.2 ≫ c'.inj _) := by
  refine Cofan.IsColimit.mk _ (fun t ↦ ?_) ?_ fun t m hm ↦ ?_
  · exact Cofan.IsColimit.desc hc' fun i ↦ Cofan.IsColimit.desc (hc i) fun j ↦ t.inj (i, j)
  · simp
  · refine Cofan.IsColimit.hom_ext hc' _ _ fun i ↦ ?_
    exact Cofan.IsColimit.hom_ext (hc i) _ _ fun j ↦ (by simpa using hm (i, j))

end Fubini

variable (α) in
/-- The functor `(f : α → C) ↦ ∏ᶜ f`. -/
@[simps]
/-
**CategoryTheory.Limits.Pi.functor** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Lim
its.Pi`。
形式化陈述：(α : Type w₂) →   {C : Type u} →     [inst : CategoryTheory.Category.{v, u
} C] →       [CategoryTheory.Limits.HasProductsOfShape α C] → CategoryTheory.Fun
ctor (α → C) C
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The functor `(f : α → C) ↦ ∏ᶜ f`.
-/
noncomputable def Pi.functor [HasProductsOfShape α C] : (α → C) ⥤ C where
  obj f := ∏ᶜ f
  map {f g} t := Pi.map t

set_option backward.defeqAttrib.useBackward true in
/-- The natural transformation induced by `Pi.π`. -/
@[simps]
/-
**CategoryTheory.Limits.Pi.functor** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Lim
its.Pi`。
形式化陈述：(α : Type w₂) →   {C : Type u} →     [inst : CategoryTheory.Category.{v, u
} C] →       [CategoryTheory.Limits.HasProductsOfShape α C] → CategoryTheory.Fun
ctor (α → C) C
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The natural transformation induced by `Pi.π`.
-/
def Pi.functorπ [HasProductsOfShape α C] (a : α) :
    Pi.functor α ⟶ Pi.eval (fun _ ↦ C) a where
  app f := Pi.π f a

set_option backward.defeqAttrib.useBackward true in
variable (α) in
/-- Up to pre-composing with an equivalence of categories, `Pi.functor` is isomorphic to `lim`. -/
@[simps!]
/-
**CategoryTheory.Limits.piEquivalenceFunctorDiscreteCompLim** 是 Mathlib 中的一个定义，位
于命名空间 `CategoryTheory.Limits`。
形式化陈述：piEquivalenceFunctorDiscreteCompLim [HasProductsOfShape α C] : (piEquivale
nceFunctorDiscrete α C).functor ⋙ lim ≅ Pi.functor _
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Up to pre-composing with an equivalence of categories, `Pi.functor` is isomorphi
c to `lim`.
-/
def piEquivalenceFunctorDiscreteCompLim [HasProductsOfShape α C] :
    (piEquivalenceFunctorDiscrete α C).functor ⋙ lim ≅ Pi.functor _ :=
  NatIso.ofComponents fun _ ↦ Iso.refl _

set_option backward.defeqAttrib.useBackward true in
@[reassoc]
/-
**CategoryTheory.Limits.piEquivalenceFunctorDiscreteCompLim_comp_functor** 是 Mat
hlib 中的一个引理，位于命名空间 `CategoryTheory.Limits`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma piEquivalenceFunctorDiscreteCompLim_comp_functorπ [HasProductsOfShape α C] (a : α) :
    (piEquivalenceFunctorDiscreteCompLim (C := C) α).hom ≫ Pi.functorπ a =
      Functor.whiskerLeft _ (lim.π <| Discrete.mk a) ≫
        (piEquivalenceFunctorDiscreteCompEvaluationIso _ _).hom := by
  cat_disch

attribute [local simp] Functor.pi in
/-- The `∏ᶜ` functor composed with the pointwise constant functor `Π i, I i ⥤ (α → C)` is isomorphic
to the constant functor with value `∏ᶜ X`. -/
@[simps!]
/-
**CategoryTheory.Limits.Pi.constCompPiIsoConst** 是 Mathlib 中的一个定义，位于命名空间 `Catego
ryTheory.Limits.Pi`。
形式化陈述：{α : Type w₂} →   {C : Type u} →     [inst : CategoryTheory.Category.{v, u
} C] →       [inst_1 : CategoryTheory.Limits.HasProductsOfShape α C] →         {
I : α → Type u_1} →           [inst_2 : (i : α) → CategoryTheory.Category.{v_1, 
u_1} (I i)] →             (X : α → C) →               (CategoryTheory.Functor.pi
 fun i => (CategoryTheory.Functor.const (I i)).obj (X i)).comp                  
 (CategoryTheory.Limits.Pi.functor α) ≅                 (CategoryTheory.Functor.
const ((i : α) → I i)).obj (∏ᶜ X)
参数：i : α；I i；X : α → C；CategoryTheory.Functor.pi fun i => (CategoryTheory.Functo
r.const (I i)).obj (X i)；CategoryTheory.Limits.Pi.functor α；CategoryTheory.Funct
or.const ((i : α) → I i)；∏ᶜ X。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The `∏ᶜ` functor composed with the pointwise constant functor `Π i, I i ⥤ (α → C
)` is isomorphic
to the constant functor with value `∏ᶜ X`.
-/
noncomputable def Pi.constCompPiIsoConst [HasProductsOfShape α C] {I : α → Type*}
    [∀ i, Category* (I i)] (X : α → C) :
    Functor.pi (fun i ↦ (Functor.const (I i)).obj (X i)) ⋙ Pi.functor α ≅
      (Functor.const _).obj (∏ᶜ X) :=
  NatIso.ofComponents (fun _ ↦ Iso.refl _)

variable (α) in
/-- The functor `(f : α → C) ↦ ∐ f`. -/
@[simps]
/-
**CategoryTheory.Limits.Sigma.functor** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.
Limits.Sigma`。
形式化陈述：(α : Type w₂) →   {C : Type u} →     [inst : CategoryTheory.Category.{v, u
} C] →       [CategoryTheory.Limits.HasCoproductsOfShape α C] → CategoryTheory.F
unctor (α → C) C
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The functor `(f : α → C) ↦ ∐ f`.
-/
noncomputable def Sigma.functor [HasCoproductsOfShape α C] : (α → C) ⥤ C where
  obj f := ∐ f
  map {f g} t := Sigma.map t

set_option backward.defeqAttrib.useBackward true in
/-- The natural transformation induced by `Sigma.ι`. -/
@[simps]
/-
**CategoryTheory.Limits.Sigma.functor** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.
Limits.Sigma`。
形式化陈述：(α : Type w₂) →   {C : Type u} →     [inst : CategoryTheory.Category.{v, u
} C] →       [CategoryTheory.Limits.HasCoproductsOfShape α C] → CategoryTheory.F
unctor (α → C) C
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The natural transformation induced by `Sigma.ι`.
-/
def Sigma.functorι [HasCoproductsOfShape α C] (a : α) :
    Pi.eval (fun _ ↦ C) a ⟶ Sigma.functor α where
  app f := Sigma.ι f a

set_option backward.defeqAttrib.useBackward true in
variable (α) in
/-- Up to pre-composing with an equivalence of categories, `Sigma.functor` is isomorphic
to `colim`. -/
@[simps!]
/-
**CategoryTheory.Limits.piEquivalenceFunctorDiscreteCompColim** 是 Mathlib 中的一个定义
，位于命名空间 `CategoryTheory.Limits`。
形式化陈述：piEquivalenceFunctorDiscreteCompColim [HasCoproductsOfShape α C] : (piEqui
valenceFunctorDiscrete α C).functor ⋙ colim ≅ Sigma.functor _
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Up to pre-composing with an equivalence of categories, `Sigma.functor` is isomor
phic
to `colim`.
-/
def piEquivalenceFunctorDiscreteCompColim [HasCoproductsOfShape α C] :
    (piEquivalenceFunctorDiscrete α C).functor ⋙ colim ≅ Sigma.functor _ :=
  NatIso.ofComponents fun _ ↦ Iso.refl _

set_option backward.defeqAttrib.useBackward true in
@[reassoc]
/-
**CategoryTheory.Limits.piEquivalenceFunctorDiscreteCompColim_comp_functor** 是 M
athlib 中的一个引理，位于命名空间 `CategoryTheory.Limits`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma piEquivalenceFunctorDiscreteCompColim_comp_functorι [HasCoproductsOfShape α C] (a : α) :
    Functor.whiskerLeft _ (colim.ι <| .mk a) ≫ (piEquivalenceFunctorDiscreteCompColim α).hom =
      (piEquivalenceFunctorDiscreteCompEvaluationIso C _).hom ≫ Sigma.functorι a := by
  cat_disch
/-
**CategoryTheory.Limits.piEquivalenceFunctorDiscrete_functor_comp_colim** 是 Math
lib 中的一个引理，位于命名空间 `CategoryTheory.Limits`。
形式化陈述：piEquivalenceFunctorDiscrete_functor_comp_colim [HasCoproductsOfShape α C]
 : (piEquivalenceFunctorDiscrete α C).functor ⋙ colim = Sigma.functor _
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma piEquivalenceFunctorDiscrete_functor_comp_colim [HasCoproductsOfShape α C] :
    (piEquivalenceFunctorDiscrete α C).functor ⋙ colim = Sigma.functor _ :=
  rfl

attribute [local simp] Functor.pi in
/-- The `∐` functor composed with the pointwise constant functor `Π i, I i ⥤ (α → C)` is isomorphic
to the constant functor with value `∐ X`. -/
@[simps!]
/-
**CategoryTheory.Limits.Sigma.constCompSigmaIsoConst** 是 Mathlib 中的一个定义，位于命名空间 `
CategoryTheory.Limits.Sigma`。
形式化陈述：{α : Type w₂} →   {C : Type u} →     [inst : CategoryTheory.Category.{v, u
} C] →       [inst_1 : CategoryTheory.Limits.HasCoproductsOfShape α C] →        
 {I : α → Type u_1} →           [inst_2 : (i : α) → CategoryTheory.Category.{v_1
, u_1} (I i)] →             (X : α → C) →               (CategoryTheory.Functor.
pi fun i => (CategoryTheory.Functor.const (I i)).obj (X i)).comp                
   (CategoryTheory.Limits.Sigma.functor α) ≅                 (CategoryTheory.Fun
ctor.const ((i : α) → I i)).obj (∐ X)
参数：i : α；I i；X : α → C；CategoryTheory.Functor.pi fun i => (CategoryTheory.Functo
r.const (I i)).obj (X i)；CategoryTheory.Limits.Sigma.functor α；CategoryTheory.Fu
nctor.const ((i : α) → I i)；∐ X。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The `∐` functor composed with the pointwise constant functor `Π i, I i ⥤ (α → C)
` is isomorphic
to the constant functor with value `∐ X`.
-/
noncomputable def Sigma.constCompSigmaIsoConst [HasCoproductsOfShape α C] {I : α → Type*}
    [∀ i, Category* (I i)] (X : α → C) :
    Functor.pi (fun i ↦ (Functor.const (I i)).obj (X i)) ⋙ Sigma.functor α ≅
      (Functor.const _).obj (∐ X) :=
  NatIso.ofComponents (fun _ ↦ Iso.refl _)

/-- The functor `C ⥤ (Type w)ᵒᵖ ⥤ C` which sends `X : C` and `α : Type w` to
the product of copies of `X` indexed by `α`. -/
@[simps]
/-
**CategoryTheory.Limits.piFunctor** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Limi
ts`。
形式化陈述：piFunctor [HasProducts.{w} C] : C ⥤ Type wᵒᵖ ⥤ C where obj X
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The functor `C ⥤ (Type w)ᵒᵖ ⥤ C` which sends `X : C` and `α : Type w` to
the product of copies of `X` indexed by `α`.
-/
def piFunctor [HasProducts.{w} C] :
    C ⥤ Type wᵒᵖ ⥤ C where
  obj X :=
    { obj α := ∏ᶜ (fun (t : α.unop) ↦ X)
      map f := Pi.map' f.unop (fun _ ↦ 𝟙 _) }
  map f := { app T := Pi.map (fun _ ↦ f) }

/-- The functor `C ⥤ Type w ⥤ C` which sends `X : C` and `α : Type w` to
the coproduct of copies of `X` indexed by `α`. -/
@[simps]
/-
**CategoryTheory.Limits.sigmaFunctor** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.L
imits`。
形式化陈述：sigmaFunctor [HasCoproducts.{w} C] : C ⥤ Type w ⥤ C where obj X
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The functor `C ⥤ Type w ⥤ C` which sends `X : C` and `α : Type w` to
the coproduct of copies of `X` indexed by `α`.
-/
def sigmaFunctor [HasCoproducts.{w} C] :
    C ⥤ Type w ⥤ C where
  obj X :=
    { obj α := ∐ (fun (t : α) ↦ X)
      map f := Sigma.map' f (fun _ ↦ 𝟙 _) }
  map f := { app T := Sigma.map (fun _ ↦ f) }

end CategoryTheory.Limits

