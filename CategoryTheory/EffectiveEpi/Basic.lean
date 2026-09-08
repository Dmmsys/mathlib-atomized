/-
Copyright (c) 2023 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz
-/
module

public import Mathlib.CategoryTheory.Limits.Shapes.Products
/-!

# Effective epimorphisms

We define the notion of effective epimorphism and effective epimorphic family of morphisms.

A morphism is an *effective epi* if it is a joint coequalizer of all pairs of
morphisms which it coequalizes.

A family of morphisms with fixed target is *effective epimorphic* if it is initial among families
of morphisms with its sources and a general fixed target, coequalizing every pair of morphisms it
coequalizes (here, the pair of morphisms coequalized can have different targets among the sources
of the family).

We have defined the notion of effective epi for morphisms and families of morphisms in such a
way that avoids requiring the existence of pullbacks. However, if the relevant pullbacks exist
then these definitions are equivalent, see the file
`Mathlib/CategoryTheory/EffectiveEpi/RegularEpi.lean`
See [nlab: *Effective Epimorphism*](https://ncatlab.org/nlab/show/effective+epimorphism) and
[Stacks 00WP](https://stacks.math.columbia.edu/tag/00WP) for the standard definitions. Note that
our notion of `EffectiveEpi` is often called "strict epi" in the literature.

## References
- [Elephant]: *Sketches of an Elephant*, P. T. Johnstone: C2.1, Example 2.1.12.
- [nlab: *Effective Epimorphism*](https://ncatlab.org/nlab/show/effective+epimorphism) and
- [Stacks 00WP](https://stacks.math.columbia.edu/tag/00WP) for the standard definitions.

-/

@[expose] public section

namespace CategoryTheory

open Limits Category

variable {C : Type*} [Category* C]

/--
This structure encodes the data required for a morphism to be an effective epimorphism.
-/
/-
**CategoryTheory.EffectiveEpiStruct** 是 Mathlib 中的一个归纳类型，位于命名空间 `CategoryTheory`
。
形式化陈述：{C : Type u_1} → [inst : CategoryTheory.Category.{v_1, u_1} C] → {X Y : C}
 → (Y ⟶ X) → Type (max u_1 v_1)
参数：Y ⟶ X；max u_1 v_1。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
This structure encodes the data required for a morphism to be an effective epimo
rphism.
-/
structure EffectiveEpiStruct {X Y : C} (f : Y ⟶ X) where
  /--
  For every `W` with a morphism `e : Y ⟶ W` that coequalizes every pair of morphisms
  `g₁ g₂ : Z ⟶ Y` which `f` coequalizes, `desc e h` is a morphism `X ⟶ W`...
  -/
  desc : ∀ {W : C} (e : Y ⟶ W),
    (∀ {Z : C} (g₁ g₂ : Z ⟶ Y), g₁ ≫ f = g₂ ≫ f → g₁ ≫ e = g₂ ≫ e) → (X ⟶ W)
  /-- ...factorizing `e` through `f`... -/
  fac : ∀ {W : C} (e : Y ⟶ W)
    (h : ∀ {Z : C} (g₁ g₂ : Z ⟶ Y), g₁ ≫ f = g₂ ≫ f → g₁ ≫ e = g₂ ≫ e),
    f ≫ desc e h = e
  /-- ...and as such, unique. -/
  uniq : ∀ {W : C} (e : Y ⟶ W)
    (h : ∀ {Z : C} (g₁ g₂ : Z ⟶ Y), g₁ ≫ f = g₂ ≫ f → g₁ ≫ e = g₂ ≫ e)
    (m : X ⟶ W), f ≫ m = e → m = desc e h

/--
A morphism `f : Y ⟶ X` is an effective epimorphism provided that `f` exhibits `X` as a colimit
of the diagram of all "relations" `R ⇉ Y`.
If `f` has a kernel pair, then this is equivalent to showing that the corresponding cofork is
a colimit.
-/
/-
**CategoryTheory.EffectiveEpi** 是 Mathlib 中的一个归纳类型，位于命名空间 `CategoryTheory`。
形式化陈述：{C : Type u_1} → [inst : CategoryTheory.Category.{v_1, u_1} C] → {X Y : C}
 → (Y ⟶ X) → Prop
参数：Y ⟶ X。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A morphism `f : Y ⟶ X` is an effective epimorphism provided that `f` exhibits `X
` as a colimit
of the diagram of all "relations" `R ⇉ Y`.
If `f` has a kernel pair, then this is equivalent to showing that the correspond
ing cofork is
a colimit.
-/
class EffectiveEpi {X Y : C} (f : Y ⟶ X) : Prop where
  /-- `f` is an effective epimorphism if there exists an `EffectiveEpiStruct` for `f`. -/
  effectiveEpi : Nonempty (EffectiveEpiStruct f)

/-- Some chosen `EffectiveEpiStruct` associated to an effective epi. -/
noncomputable
/-
**CategoryTheory.EffectiveEpi.getStruct** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheor
y.EffectiveEpi`。
形式化陈述：{C : Type u_1} →   [inst : CategoryTheory.Category.{v_1, u_1} C] →     {X 
Y : C} → (f : Y ⟶ X) → [CategoryTheory.EffectiveEpi f] → CategoryTheory.Effectiv
eEpiStruct f
参数：f : Y ⟶ X。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.EffectiveEpi.effectiveEpi`：∀ {C : Type u_1} {inst : Categ
oryTheory.Category.{v_1, u_1} C} {X Y : C} {f : Y ⟶ X}   [self : CategoryTheory.
EffectiveEpi f], Nonempty (Cat…
-/
def EffectiveEpi.getStruct {X Y : C} (f : Y ⟶ X) [EffectiveEpi f] : EffectiveEpiStruct f :=
  EffectiveEpi.effectiveEpi.some

/-- Descend along an effective epi. -/
noncomputable
/-
**CategoryTheory.EffectiveEpi.desc** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Eff
ectiveEpi`。
形式化陈述：{C : Type u_1} →   [inst : CategoryTheory.Category.{v_1, u_1} C] →     {X 
Y W : C} →       (f : Y ⟶ X) →         [CategoryTheory.EffectiveEpi f] →        
   (e : Y ⟶ W) →             (∀ {Z : C} (g₁ g₂ : Z ⟶ Y),                 Categor
yTheory.CategoryStruct.comp g₁ f = CategoryTheory.CategoryStruct.comp g₂ f →    
               CategoryTheory.CategoryStruct.comp g₁ e = CategoryTheory.Category
Struct.comp g₂ e) →               (X ⟶ W)
参数：f : Y ⟶ X；e : Y ⟶ W；∀ {Z : C} (g₁ g₂ : Z ⟶ Y),                 CategoryTheory
.CategoryStruct.comp g₁ f = CategoryTheory.CategoryStruct.comp g₂ f →           
        CategoryTheory.CategoryStruct.comp g₁ e = CategoryTheory.CategoryStruct.
comp g₂ e；X ⟶ W。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def EffectiveEpi.desc {X Y W : C} (f : Y ⟶ X) [EffectiveEpi f]
    (e : Y ⟶ W) (h : ∀ {Z : C} (g₁ g₂ : Z ⟶ Y), g₁ ≫ f = g₂ ≫ f → g₁ ≫ e = g₂ ≫ e) :
    X ⟶ W := (EffectiveEpi.getStruct f).desc e h

@[reassoc (attr := simp)]
/-
**CategoryTheory.EffectiveEpi.fac** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.Effe
ctiveEpi`。
形式化陈述：∀ {C : Type u_1} [inst : CategoryTheory.Category.{v_1, u_1} C] {X Y W : C}
 (f : Y ⟶ X)   [inst_1 : CategoryTheory.EffectiveEpi f] (e : Y ⟶ W)   (h :     ∀
 {Z : C} (g₁ g₂ : Z ⟶ Y),       CategoryTheory.CategoryStruct.comp g₁ f = Catego
ryTheory.CategoryStruct.comp g₂ f →         CategoryTheory.CategoryStruct.comp g
₁ e = CategoryTheory.CategoryStruct.comp g₂ e),   CategoryTheory.CategoryStruct.
comp f (CategoryTheory.EffectiveEpi.desc f e ⋯) = e
参数：f : Y ⟶ X；e : Y ⟶ W；h :     ∀ {Z : C} (g₁ g₂ : Z ⟶ Y),       CategoryTheory.C
ategoryStruct.comp g₁ f = CategoryTheory.CategoryStruct.comp g₂ f →         Cate
goryTheory.CategoryStruct.comp g₁ e = CategoryTheory.CategoryStruct.comp g₂ e；Ca
tegoryTheory.EffectiveEpi.desc f e ⋯。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.EffectiveEpiStruct.fac`：∀ {C : Type u_1} [inst : Category
Theory.Category.{v_1, u_1} C] {X Y : C} {f : Y ⟶ X}   (self : CategoryTheory.Eff
ectiveEpiStruct f) {W : C} …
-/
lemma EffectiveEpi.fac {X Y W : C} (f : Y ⟶ X) [EffectiveEpi f]
    (e : Y ⟶ W) (h : ∀ {Z : C} (g₁ g₂ : Z ⟶ Y), g₁ ≫ f = g₂ ≫ f → g₁ ≫ e = g₂ ≫ e) :
    f ≫ EffectiveEpi.desc f e h = e :=
  (EffectiveEpi.getStruct f).fac e h
/-
**CategoryTheory.EffectiveEpi.uniq** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.Eff
ectiveEpi`。
形式化陈述：∀ {C : Type u_1} [inst : CategoryTheory.Category.{v_1, u_1} C] {X Y W : C}
 (f : Y ⟶ X)   [inst_1 : CategoryTheory.EffectiveEpi f] (e : Y ⟶ W)   (h :     ∀
 {Z : C} (g₁ g₂ : Z ⟶ Y),       CategoryTheory.CategoryStruct.comp g₁ f = Catego
ryTheory.CategoryStruct.comp g₂ f →         CategoryTheory.CategoryStruct.comp g
₁ e = CategoryTheory.CategoryStruct.comp g₂ e)   (m : X ⟶ W), CategoryTheory.Cat
egoryStruct.comp f m = e → m = CategoryTheory.EffectiveEpi.desc f e ⋯
参数：f : Y ⟶ X；e : Y ⟶ W；h :     ∀ {Z : C} (g₁ g₂ : Z ⟶ Y),       CategoryTheory.C
ategoryStruct.comp g₁ f = CategoryTheory.CategoryStruct.comp g₂ f →         Cate
goryTheory.CategoryStruct.comp g₁ e = CategoryTheory.CategoryStruct.comp g₂ e；m 
: X ⟶ W。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.EffectiveEpiStruct.uniq`：∀ {C : Type u_1} [inst : Categor
yTheory.Category.{v_1, u_1} C] {X Y : C} {f : Y ⟶ X}   (self : CategoryTheory.Ef
fectiveEpiStruct f) {W : C} …
-/
lemma EffectiveEpi.uniq {X Y W : C} (f : Y ⟶ X) [EffectiveEpi f]
    (e : Y ⟶ W) (h : ∀ {Z : C} (g₁ g₂ : Z ⟶ Y), g₁ ≫ f = g₂ ≫ f → g₁ ≫ e = g₂ ≫ e)
    (m : X ⟶ W) (hm : f ≫ m = e) :
    m = EffectiveEpi.desc f e h :=
  (EffectiveEpi.getStruct f).uniq e h _ hm

open EffectiveEpi Category
/-
**CategoryTheory.epi_of_effectiveEpi** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory`。
形式化陈述：epi_of_effectiveEpi {X Y : C} (f : Y ⟶ X) [EffectiveEpi f] : Epi f where l
eft_cancellation m₁ m₂ h
参数：f : Y ⟶ X。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `CategoryTheory.EffectiveEpi.uniq`：∀ {C : Type u_1} [inst : CategoryTheor
y.Category.{v_1, u_1} C] {X Y W : C} (f : Y ⟶ X)   [inst_1 : CategoryTheory.Effe
ctiveEpi f] (e : Y ⟶ W…
-/
instance epi_of_effectiveEpi {X Y : C} (f : Y ⟶ X) [EffectiveEpi f] : Epi f where
  left_cancellation m₁ m₂ h := by
    rw [show m₂ = desc f (f ≫ m₂) (fun _ _ h => by simp [← assoc, h]) from uniq _ _ _ _ rfl]
    exact uniq _ _ _ _ h
/-
**CategoryTheory.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 100) strongEpi_of_effectiveEpi {X Y : C} (f : X ⟶ Y) [EffectiveEpi f] :
    StrongEpi f :=
  StrongEpi.mk' fun A B z hz u v sq ↦
    have : ∀ {Z : C} (g₁ g₂ : Z ⟶ X), g₁ ≫ f = g₂ ≫ f → g₁ ≫ u = g₂ ≫ u := fun _ _ h ↦ by
      simpa [← sq.w, cancel_mono_assoc_iff] using h =≫ v
    CommSq.HasLift.mk' ⟨desc f u this, fac f u this, (cancel_epi f).1 ((by simp [← sq.w]))⟩

/--
This structure encodes the data required for a family of morphisms to be effective epimorphic.
-/
/-
**CategoryTheory.EffectiveEpiFamilyStruct** 是 Mathlib 中的一个归纳类型，位于命名空间 `CategoryT
heory`。
形式化陈述：{C : Type u_1} →   [inst : CategoryTheory.Category.{v_1, u_1} C] →     {B 
: C} → {α : Type u_2} → (X : α → C) → ((a : α) → X a ⟶ B) → Type (max (max u_1 u
_2) v_1)
参数：X : α → C；(a : α) → X a ⟶ B；max (max u_1 u_2) v_1。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
This structure encodes the data required for a family of morphisms to be effecti
ve epimorphic.
-/
structure EffectiveEpiFamilyStruct {B : C} {α : Type*}
    (X : α → C) (π : (a : α) → (X a ⟶ B)) where
  /--
  For every `W` with a family of morphisms `e a : Y a ⟶ W` that coequalizes every pair of morphisms
  `g₁ : Z ⟶ Y a₁`, `g₂ : Z ⟶ Y a₂` which the family `π` coequalizes, `desc e h` is a morphism
  `X ⟶ W`...
  -/
  desc : ∀ {W} (e : (a : α) → (X a ⟶ W)),
      (∀ {Z : C} (a₁ a₂ : α) (g₁ : Z ⟶ X a₁) (g₂ : Z ⟶ X a₂),
      g₁ ≫ π _ = g₂ ≫ π _ → g₁ ≫ e _ = g₂ ≫ e _) → (B ⟶ W)
  /-- ...factorizing the components of `e` through the components of `π`... -/
  fac : ∀ {W} (e : (a : α) → (X a ⟶ W))
          (h : ∀ {Z : C} (a₁ a₂ : α) (g₁ : Z ⟶ X a₁) (g₂ : Z ⟶ X a₂),
            g₁ ≫ π _ = g₂ ≫ π _ → g₁ ≫ e _ = g₂ ≫ e _)
          (a : α), π a ≫ desc e h = e a
  /-- ...and as such, unique. -/
  uniq : ∀ {W} (e : (a : α) → (X a ⟶ W))
          (h : ∀ {Z : C} (a₁ a₂ : α) (g₁ : Z ⟶ X a₁) (g₂ : Z ⟶ X a₂),
            g₁ ≫ π _ = g₂ ≫ π _ → g₁ ≫ e _ = g₂ ≫ e _)
          (m : B ⟶ W), (∀ (a : α), π a ≫ m = e a) → m = desc e h

/--
A family of morphisms `π a : X a ⟶ B` indexed by `α` is effective epimorphic
provided that the `π a` exhibit `B` as a colimit of the diagram of all "relations"
`R → X a₁`, `R ⟶ X a₂` for all `a₁ a₂ : α`.
-/
/-
**CategoryTheory.EffectiveEpiFamily** 是 Mathlib 中的一个归纳类型，位于命名空间 `CategoryTheory`
。
形式化陈述：{C : Type u_1} →   [inst : CategoryTheory.Category.{v_1, u_1} C] → {B : C}
 → {α : Type u_2} → (X : α → C) → ((a : α) → X a ⟶ B) → Prop
参数：X : α → C；(a : α) → X a ⟶ B。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A family of morphisms `π a : X a ⟶ B` indexed by `α` is effective epimorphic
provided that the `π a` exhibit `B` as a colimit of the diagram of all "relation
s"
`R → X a₁`, `R ⟶ X a₂` for all `a₁ a₂ : α`.
-/
class EffectiveEpiFamily {B : C} {α : Type*} (X : α → C) (π : (a : α) → (X a ⟶ B)) : Prop where
  /-- `π` is an effective epimorphic family if there exists an `EffectiveEpiFamilyStruct` for `π` -/
  effectiveEpiFamily : Nonempty (EffectiveEpiFamilyStruct X π)

/-- Some chosen `EffectiveEpiFamilyStruct` associated to an effective epi family. -/
noncomputable
/-
**CategoryTheory.EffectiveEpiFamily.getStruct** 是 Mathlib 中的一个定义，位于命名空间 `Categor
yTheory.EffectiveEpiFamily`。
形式化陈述：{C : Type u_1} →   [inst : CategoryTheory.Category.{v_1, u_1} C] →     {B 
: C} →       {α : Type u_2} →         (X : α → C) →           (π : (a : α) → X a
 ⟶ B) →             [CategoryTheory.EffectiveEpiFamily X π] → CategoryTheory.Eff
ectiveEpiFamilyStruct X π
参数：X : α → C；π : (a : α) → X a ⟶ B。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.EffectiveEpiFamily.effectiveEpiFamily`：∀ {C : Type u_1} {
inst : CategoryTheory.Category.{v_1, u_1} C} {B : C} {α : Type u_2} {X : α → C} 
  {π : (a : α) → X a ⟶ B} [self : Category…
-/
def EffectiveEpiFamily.getStruct {B : C} {α : Type*} (X : α → C) (π : (a : α) → (X a ⟶ B))
    [EffectiveEpiFamily X π] : EffectiveEpiFamilyStruct X π :=
  EffectiveEpiFamily.effectiveEpiFamily.some

/-- Descend along an effective epi family. -/
noncomputable
/-
**CategoryTheory.EffectiveEpiFamily.desc** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheo
ry.EffectiveEpiFamily`。
形式化陈述：{C : Type u_1} →   [inst : CategoryTheory.Category.{v_1, u_1} C] →     {B 
W : C} →       {α : Type u_2} →         (X : α → C) →           (π : (a : α) → X
 a ⟶ B) →             [CategoryTheory.EffectiveEpiFamily X π] →               (e
 : (a : α) → X a ⟶ W) →                 (∀ {Z : C} (a₁ a₂ : α) (g₁ : Z ⟶ X a₁) (
g₂ : Z ⟶ X a₂),                     CategoryTheory.CategoryStruct.comp g₁ (π a₁)
 = CategoryTheory.CategoryStruct.comp g₂ (π a₂) →                       Category
Theory.CategoryStruct.comp g₁ (e a₁) = CategoryTheory.CategoryStruct.comp g₂ (e 
a₂)) →                   (B ⟶ W)
参数：X : α → C；π : (a : α) → X a ⟶ B；e : (a : α) → X a ⟶ W；∀ {Z : C} (a₁ a₂ : α) (
g₁ : Z ⟶ X a₁) (g₂ : Z ⟶ X a₂),                     CategoryTheory.CategoryStruc
t.comp g₁ (π a₁) = CategoryTheory.CategoryStruct.comp g₂ (π a₂) →               
        CategoryTheory.CategoryStruct.comp g₁ (e a₁) = CategoryTheory.CategorySt
ruct.comp g₂ (e a₂)；B ⟶ W。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def EffectiveEpiFamily.desc {B W : C} {α : Type*} (X : α → C) (π : (a : α) → (X a ⟶ B))
    [EffectiveEpiFamily X π] (e : (a : α) → (X a ⟶ W))
    (h : ∀ {Z : C} (a₁ a₂ : α) (g₁ : Z ⟶ X a₁) (g₂ : Z ⟶ X a₂),
      g₁ ≫ π _ = g₂ ≫ π _ → g₁ ≫ e _ = g₂ ≫ e _) : B ⟶ W :=
  (EffectiveEpiFamily.getStruct X π).desc e h

@[reassoc (attr := simp)]
/-
**CategoryTheory.EffectiveEpiFamily.fac** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheor
y.EffectiveEpiFamily`。
形式化陈述：∀ {C : Type u_1} [inst : CategoryTheory.Category.{v_1, u_1} C] {B W : C} {
α : Type u_2} (X : α → C)   (π : (a : α) → X a ⟶ B) [inst_1 : CategoryTheory.Eff
ectiveEpiFamily X π] (e : (a : α) → X a ⟶ W)   (h :     ∀ {Z : C} (a₁ a₂ : α) (g
₁ : Z ⟶ X a₁) (g₂ : Z ⟶ X a₂),       CategoryTheory.CategoryStruct.comp g₁ (π a₁
) = CategoryTheory.CategoryStruct.comp g₂ (π a₂) →         CategoryTheory.Catego
ryStruct.comp g₁ (e a₁) = CategoryTheory.CategoryStruct.comp g₂ (e a₂))   (a : α
), CategoryTheory.CategoryStruct.comp (π a) (CategoryTheory.EffectiveEpiFamily.d
esc X π e ⋯) = e a
参数：X : α → C；π : (a : α) → X a ⟶ B；e : (a : α) → X a ⟶ W；h :     ∀ {Z : C} (a₁ a
₂ : α) (g₁ : Z ⟶ X a₁) (g₂ : Z ⟶ X a₂),       CategoryTheory.CategoryStruct.comp
 g₁ (π a₁) = CategoryTheory.CategoryStruct.comp g₂ (π a₂) →         CategoryTheo
ry.CategoryStruct.comp g₁ (e a₁) = CategoryTheory.CategoryStruct.comp g₂ (e a₂)；
a : α；π a；CategoryTheory.EffectiveEpiFamily.desc X π e ⋯。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.EffectiveEpiFamilyStruct.fac`：∀ {C : Type u_1} [inst : Ca
tegoryTheory.Category.{v_1, u_1} C] {B : C} {α : Type u_2} {X : α → C}   {π : (a
 : α) → X a ⟶ B} (self : Category…
-/
lemma EffectiveEpiFamily.fac {B W : C} {α : Type*} (X : α → C) (π : (a : α) → (X a ⟶ B))
    [EffectiveEpiFamily X π] (e : (a : α) → (X a ⟶ W))
    (h : ∀ {Z : C} (a₁ a₂ : α) (g₁ : Z ⟶ X a₁) (g₂ : Z ⟶ X a₂),
      g₁ ≫ π _ = g₂ ≫ π _ → g₁ ≫ e _ = g₂ ≫ e _) (a : α) :
    π a ≫ EffectiveEpiFamily.desc X π e h = e a :=
  (EffectiveEpiFamily.getStruct X π).fac e h a
/-
**CategoryTheory.EffectiveEpiFamily.uniq** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheo
ry.EffectiveEpiFamily`。
形式化陈述：∀ {C : Type u_1} [inst : CategoryTheory.Category.{v_1, u_1} C] {B W : C} {
α : Type u_2} (X : α → C)   (π : (a : α) → X a ⟶ B) [inst_1 : CategoryTheory.Eff
ectiveEpiFamily X π] (e : (a : α) → X a ⟶ W)   (h :     ∀ {Z : C} (a₁ a₂ : α) (g
₁ : Z ⟶ X a₁) (g₂ : Z ⟶ X a₂),       CategoryTheory.CategoryStruct.comp g₁ (π a₁
) = CategoryTheory.CategoryStruct.comp g₂ (π a₂) →         CategoryTheory.Catego
ryStruct.comp g₁ (e a₁) = CategoryTheory.CategoryStruct.comp g₂ (e a₂))   (m : B
 ⟶ W),   (∀ (a : α), CategoryTheory.CategoryStruct.comp (π a) m = e a) → m = Cat
egoryTheory.EffectiveEpiFamily.desc X π e ⋯
参数：X : α → C；π : (a : α) → X a ⟶ B；e : (a : α) → X a ⟶ W；h :     ∀ {Z : C} (a₁ a
₂ : α) (g₁ : Z ⟶ X a₁) (g₂ : Z ⟶ X a₂),       CategoryTheory.CategoryStruct.comp
 g₁ (π a₁) = CategoryTheory.CategoryStruct.comp g₂ (π a₂) →         CategoryTheo
ry.CategoryStruct.comp g₁ (e a₁) = CategoryTheory.CategoryStruct.comp g₂ (e a₂)；
m : B ⟶ W；∀ (a : α), CategoryTheory.CategoryStruct.comp (π a) m = e a。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.EffectiveEpiFamilyStruct.uniq`：∀ {C : Type u_1} [inst : C
ategoryTheory.Category.{v_1, u_1} C] {B : C} {α : Type u_2} {X : α → C}   {π : (
a : α) → X a ⟶ B} (self : Category…
-/
lemma EffectiveEpiFamily.uniq {B W : C} {α : Type*} (X : α → C) (π : (a : α) → (X a ⟶ B))
    [EffectiveEpiFamily X π] (e : (a : α) → (X a ⟶ W))
    (h : ∀ {Z : C} (a₁ a₂ : α) (g₁ : Z ⟶ X a₁) (g₂ : Z ⟶ X a₂),
      g₁ ≫ π _ = g₂ ≫ π _ → g₁ ≫ e _ = g₂ ≫ e _)
    (m : B ⟶ W) (hm : ∀ a, π a ≫ m = e a) :
    m = EffectiveEpiFamily.desc X π e h :=
  (EffectiveEpiFamily.getStruct X π).uniq e h m hm

-- TODO: Once we have "jointly epimorphic families", we could rephrase this as such a property.
/-
**CategoryTheory.EffectiveEpiFamily.hom_ext** 是 Mathlib 中的一个定理，位于命名空间 `CategoryT
heory.EffectiveEpiFamily`。
形式化陈述：∀ {C : Type u_1} [inst : CategoryTheory.Category.{v_1, u_1} C] {B W : C} {
α : Type u_2} (X : α → C)   (π : (a : α) → X a ⟶ B) [CategoryTheory.EffectiveEpi
Family X π] (m₁ m₂ : B ⟶ W),   (∀ (a : α), CategoryTheory.CategoryStruct.comp (π
 a) m₁ = CategoryTheory.CategoryStruct.comp (π a) m₂) → m₁ = m₂
参数：X : α → C；π : (a : α) → X a ⟶ B；m₁ m₂ : B ⟶ W；∀ (a : α), CategoryTheory.Categ
oryStruct.comp (π a) m₁ = CategoryTheory.CategoryStruct.comp (π a) m₂。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `CategoryTheory.EffectiveEpiFamily.uniq`：∀ {C : Type u_1} [inst : Categor
yTheory.Category.{v_1, u_1} C] {B W : C} {α : Type u_2} (X : α → C)   (π : (a : 
α) → X a ⟶ B) [inst_1 : Cate…
-/
lemma EffectiveEpiFamily.hom_ext {B W : C} {α : Type*} (X : α → C) (π : (a : α) → (X a ⟶ B))
    [EffectiveEpiFamily X π] (m₁ m₂ : B ⟶ W) (h : ∀ a, π a ≫ m₁ = π a ≫ m₂) :
    m₁ = m₂ := by
  have : m₂ = EffectiveEpiFamily.desc X π (fun a => π a ≫ m₂)
      (fun a₁ a₂ g₁ g₂ h => by simp only [← assoc, h]) := by
    apply EffectiveEpiFamily.uniq; intro; rfl
  rw [this]
  exact EffectiveEpiFamily.uniq _ _ _ _ _ h

/--
An `EffectiveEpiFamily` consisting of a single `EffectiveEpi`
-/
noncomputable
/-
**CategoryTheory.effectiveEpiFamilyStructSingletonOfEffectiveEpi** 是 Mathlib 中的一
个定义，位于命名空间 `CategoryTheory`。
形式化陈述：effectiveEpiFamilyStructSingletonOfEffectiveEpi {B X : C} (f : X ⟶ B) [Eff
ectiveEpi f] : EffectiveEpiFamilyStruct (fun () => X) (fun () => f) where desc e
 h
参数：f : X ⟶ B。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def effectiveEpiFamilyStructSingletonOfEffectiveEpi {B X : C} (f : X ⟶ B) [EffectiveEpi f] :
    EffectiveEpiFamilyStruct (fun () ↦ X) (fun () ↦ f) where
  desc e h := EffectiveEpi.desc f (e ()) (fun g₁ g₂ hg ↦ h () () g₁ g₂ hg)
  fac e h := fun _ ↦ EffectiveEpi.fac f (e ()) (fun g₁ g₂ hg ↦ h () () g₁ g₂ hg)
  uniq e h m hm := by apply EffectiveEpi.uniq f (e ()) (h () ()); exact hm ()
/-
**CategoryTheory.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {B X : C} (f : X ⟶ B) [EffectiveEpi f] : EffectiveEpiFamily (fun () ↦ X) (fun () ↦ f) :=
  ⟨⟨effectiveEpiFamilyStructSingletonOfEffectiveEpi f⟩⟩

/--
A single element `EffectiveEpiFamily` consists of an `EffectiveEpi`
-/
noncomputable
/-
**CategoryTheory.effectiveEpiStructOfEffectiveEpiFamilySingleton** 是 Mathlib 中的一
个定义，位于命名空间 `CategoryTheory`。
形式化陈述：effectiveEpiStructOfEffectiveEpiFamilySingleton {B X : C} (f : X ⟶ B) [Eff
ectiveEpiFamily (fun () => X) (fun () => f)] : EffectiveEpiStruct f where desc e
 h
参数：f : X ⟶ B；fun () => X；fun () => f。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def effectiveEpiStructOfEffectiveEpiFamilySingleton {B X : C} (f : X ⟶ B)
    [EffectiveEpiFamily (fun () ↦ X) (fun () ↦ f)] :
    EffectiveEpiStruct f where
  desc e h := EffectiveEpiFamily.desc
    (fun () ↦ X) (fun () ↦ f) (fun () ↦ e) (fun _ _ g₁ g₂ hg ↦ h g₁ g₂ hg)
  fac e h := EffectiveEpiFamily.fac
    (fun () ↦ X) (fun () ↦ f) (fun () ↦ e) (fun _ _ g₁ g₂ hg ↦ h g₁ g₂ hg) ()
  uniq e h m hm := EffectiveEpiFamily.uniq
    (fun () ↦ X) (fun () ↦ f) (fun () ↦ e) (fun _ _ g₁ g₂ hg ↦ h g₁ g₂ hg) m (fun _ ↦ hm)
/-
**CategoryTheory.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {B X : C} (f : X ⟶ B) [EffectiveEpiFamily (fun () ↦ X) (fun () ↦ f)] :
    EffectiveEpi f :=
  ⟨⟨effectiveEpiStructOfEffectiveEpiFamilySingleton f⟩⟩
/-
**CategoryTheory.effectiveEpi_iff_effectiveEpiFamily** 是 Mathlib 中的一个定理，位于命名空间 `
CategoryTheory`。
形式化陈述：effectiveEpi_iff_effectiveEpiFamily {B X : C} (f : X ⟶ B) : EffectiveEpi f
 ↔ EffectiveEpiFamily (fun () => X) (fun () => f)
参数：f : X ⟶ B。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.instEffectiveEpiFamily`：∀ {C : Type u_1} [inst : Category
Theory.Category.{v_1, u_1} C] {B X : C} (f : X ⟶ B) [CategoryTheory.EffectiveEpi
 f],   CategoryTheory.Effec…
· 使用定理 `CategoryTheory.instEffectiveEpiOfEffectiveEpiFamily`：∀ {C : Type u_1} [i
nst : CategoryTheory.Category.{v_1, u_1} C] {B X : C} (f : X ⟶ B)   [CategoryThe
ory.EffectiveEpiFamily (fun x => X) fun x…
-/
theorem effectiveEpi_iff_effectiveEpiFamily {B X : C} (f : X ⟶ B) :
    EffectiveEpi f ↔ EffectiveEpiFamily (fun () ↦ X) (fun () ↦ f) :=
  ⟨fun _ ↦ inferInstance, fun _ ↦ inferInstance⟩

set_option backward.isDefEq.respectTransparency false in
/--
A family of morphisms with the same target inducing an isomorphism from the coproduct to the target
is an `EffectiveEpiFamily`.
-/
noncomputable
/-
**CategoryTheory.effectiveEpiFamilyStructOfIsIsoDesc** 是 Mathlib 中的一个定义，位于命名空间 `
CategoryTheory`。
形式化陈述：effectiveEpiFamilyStructOfIsIsoDesc {B : C} {α : Type*} (X : α -> C) (π : 
(a : α) -> (X a ⟶ B)) [HasCoproduct X] [IsIso (Sigma.desc π)] : EffectiveEpiFami
lyStruct X π where desc e _
参数：X : α -> C；π : (a : α) -> (X a ⟶ B)；Sigma.desc π。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def effectiveEpiFamilyStructOfIsIsoDesc {B : C} {α : Type*} (X : α → C)
    (π : (a : α) → (X a ⟶ B)) [HasCoproduct X] [IsIso (Sigma.desc π)] :
    EffectiveEpiFamilyStruct X π where
  desc e _ := (asIso (Sigma.desc π)).inv ≫ (Sigma.desc e)
  fac e h := by
    intro a
    have : π a = Sigma.ι X a ≫ (asIso (Sigma.desc π)).hom := by simp only [asIso_hom,
      colimit.ι_desc, Cofan.mk_ι_app]
    rw [this, assoc]
    simp only [asIso_hom, asIso_inv, IsIso.hom_inv_id_assoc, colimit.ι_desc,
      Cofan.mk_ι_app]
  uniq e h m hm := by
    simp only [asIso_inv, IsIso.eq_inv_comp]
    ext a
    simp only [colimit.ι_desc_assoc, Discrete.functor_obj, Cofan.mk_ι_app,
      colimit.ι_desc]
    exact hm a
/-
**CategoryTheory.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {B : C} {α : Type*} (X : α → C) (π : (a : α) → (X a ⟶ B)) [HasCoproduct X]
    [IsIso (Sigma.desc π)] : EffectiveEpiFamily X π :=
  ⟨⟨effectiveEpiFamilyStructOfIsIsoDesc X π⟩⟩

/-- Any isomorphism is an effective epi. -/
noncomputable
/-
**CategoryTheory.effectiveEpiStructOfIsIso** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTh
eory`。
形式化陈述：effectiveEpiStructOfIsIso {X Y : C} (f : X ⟶ Y) [IsIso f] : EffectiveEpiSt
ruct f where desc e _
参数：f : X ⟶ Y。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def effectiveEpiStructOfIsIso {X Y : C} (f : X ⟶ Y) [IsIso f] : EffectiveEpiStruct f where
  desc e _ := inv f ≫ e
  fac _ _ := by simp
  uniq _ _ _ h := by simpa using h
/-
**CategoryTheory.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {X Y : C} (f : X ⟶ Y) [IsIso f] : EffectiveEpi f := ⟨⟨effectiveEpiStructOfIsIso f⟩⟩
/-
**CategoryTheory.** 是 Mathlib 中的一个示例，位于命名空间 `CategoryTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
example {X : C} : EffectiveEpiFamily (fun _ => X : Unit → C) (fun _ => 𝟙 X) := inferInstance

/--
Reindex the indexing type of an effective epi family struct.
-/
/-
**CategoryTheory.EffectiveEpiFamilyStruct.reindex** 是 Mathlib 中的一个定义，位于命名空间 `Cat
egoryTheory.EffectiveEpiFamilyStruct`。
形式化陈述：{C : Type u_1} →   [inst : CategoryTheory.Category.{v_1, u_1} C] →     {B 
: C} →       {α : Type u_2} →         {α' : Type u_3} →           (X : α → C) → 
            (π : (a : α) → X a ⟶ B) →               (e : α' ≃ α) →              
   (CategoryTheory.EffectiveEpiFamilyStruct (fun a => X (e a)) fun a => π (e a))
 →                   CategoryTheory.EffectiveEpiFamilyStruct X π
参数：X : α → C；π : (a : α) → X a ⟶ B；e : α' ≃ α；CategoryTheory.EffectiveEpiFamilyS
truct (fun a => X (e a)) fun a => π (e a)。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Reindex the indexing type of an effective epi family struct.
-/
def EffectiveEpiFamilyStruct.reindex
    {B : C} {α α' : Type*}
    (X : α → C)
    (π : (a : α) → (X a ⟶ B))
    (e : α' ≃ α)
    (P : EffectiveEpiFamilyStruct (fun a => X (e a)) (fun a => π (e a))) :
    EffectiveEpiFamilyStruct X π where
  desc := fun f h => P.desc (fun _ => f _) (fun _ _ => h _ _)
  fac _ _ a := by
    obtain ⟨a, rfl⟩ := e.surjective a
    apply P.fac
  uniq _ _ _ hm := P.uniq _ _ _ fun _ => hm _

/--
Reindex the indexing type of an effective epi family.
-/
/-
**CategoryTheory.EffectiveEpiFamily.reindex** 是 Mathlib 中的一个定理，位于命名空间 `CategoryT
heory.EffectiveEpiFamily`。
形式化陈述：∀ {C : Type u_1} [inst : CategoryTheory.Category.{v_1, u_1} C] {B : C} {α 
: Type u_2} {α' : Type u_3} (X : α → C)   (π : (a : α) → X a ⟶ B) (e : α' ≃ α), 
  (CategoryTheory.EffectiveEpiFamily (fun a => X (e a)) fun a => π (e a)) → Cate
goryTheory.EffectiveEpiFamily X π
参数：X : α → C；π : (a : α) → X a ⟶ B；e : α' ≃ α；CategoryTheory.EffectiveEpiFamily 
(fun a => X (e a)) fun a => π (e a)。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Reindex the indexing type of an effective epi family.
-/
lemma EffectiveEpiFamily.reindex
    {B : C} {α α' : Type*}
    (X : α → C)
    (π : (a : α) → (X a ⟶ B))
    (e : α' ≃ α)
    (h : EffectiveEpiFamily (fun a => X (e a)) (fun a => π (e a))) :
    EffectiveEpiFamily X π :=
  .mk <| .intro <| @EffectiveEpiFamily.getStruct _ _ _ _ _ _ h |>.reindex _ _ e

end CategoryTheory

