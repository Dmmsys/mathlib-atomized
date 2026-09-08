/-
Copyright (c) 2020 Markus Himmel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel, Kim Morrison
-/
module

public import Mathlib.CategoryTheory.Limits.Shapes.Kernels

/-!
# The abelian image and coimage.

In an abelian category we usually want the image of a morphism `f` to be defined as
`kernel (cokernel.π f)`, and the coimage to be defined as `cokernel (kernel.ι f)`.

We make these definitions here, as `Abelian.image f` and `Abelian.coimage f`
(without assuming the category is actually abelian),
and later relate these to the usual categorical notions when in an abelian category.

There is a canonical morphism `coimageImageComparison : Abelian.coimage f ⟶ Abelian.image f`.
Later we show that this is always an isomorphism in an abelian category,
and conversely a category with (co)kernels and finite products in which this morphism
is always an isomorphism is an abelian category.
-/

@[expose] public section


noncomputable section

universe v u

open CategoryTheory

open CategoryTheory.Limits

namespace CategoryTheory.Abelian

variable {C : Type u} [Category.{v} C] [HasZeroMorphisms C]
variable {P Q : C} (f : P ⟶ Q)

section Image

variable [HasCokernel f] [HasKernel (cokernel.π f)]

/-- The kernel of the cokernel of `f` is called the (abelian) image of `f`. -/
/-
**CategoryTheory.Abelian.image** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Abelian
`。
形式化陈述：{C : Type u} →   [inst : CategoryTheory.Category.{v, u} C] →     [inst_1 :
 CategoryTheory.Limits.HasZeroMorphisms C] →       {P Q : C} →         (f : P ⟶ 
Q) →           [inst_2 : CategoryTheory.Limits.HasCokernel f] →             [Cat
egoryTheory.Limits.HasKernel (CategoryTheory.Limits.cokernel.π f)] → C
参数：f : P ⟶ Q；CategoryTheory.Limits.cokernel.π f。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The kernel of the cokernel of `f` is called the (abelian) image of `f`.
-/
protected abbrev image : C :=
  kernel (cokernel.π f)

/-- The inclusion of the image into the codomain. -/
/-
**CategoryTheory.Abelian.image.** 是 Mathlib 中的一个缩写定义，位于命名空间 `CategoryTheory.Abel
ian`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The inclusion of the image into the codomain.
-/
protected abbrev image.ι : Abelian.image f ⟶ Q :=
  kernel.ι (cokernel.π f)

/-- There is a canonical epimorphism `p : P ⟶ image f` for every `f`. -/
/-
**CategoryTheory.Abelian.factorThruImage** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheo
ry.Abelian`。
形式化陈述：{C : Type u} →   [inst : CategoryTheory.Category.{v, u} C] →     [inst_1 :
 CategoryTheory.Limits.HasZeroMorphisms C] →       {P Q : C} →         (f : P ⟶ 
Q) →           [inst_2 : CategoryTheory.Limits.HasCokernel f] →             [ins
t_3 : CategoryTheory.Limits.HasKernel (CategoryTheory.Limits.cokernel.π f)] →   
            P ⟶ CategoryTheory.Abelian.image f
参数：f : P ⟶ Q；CategoryTheory.Limits.cokernel.π f。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.cokernel.condition`：∀ {C : Type u} [inst : Categor
yTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Limits.HasZeroMorphisms C] {
X Y : C}   (f : X ⟶ Y) [inst_2…

--- 原说明 ---
There is a canonical epimorphism `p : P ⟶ image f` for every `f`.
-/
protected abbrev factorThruImage : P ⟶ Abelian.image f :=
  kernel.lift (cokernel.π f) f <| cokernel.condition f

/-- `f` factors through its image via the canonical morphism `p`. -/
/-
**CategoryTheory.Abelian.image.fac** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.Abe
lian.image`。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] [inst_1 : Categor
yTheory.Limits.HasZeroMorphisms C] {P Q : C}   (f : P ⟶ Q) [inst_2 : CategoryThe
ory.Limits.HasCokernel f]   [inst_3 : CategoryTheory.Limits.HasKernel (CategoryT
heory.Limits.cokernel.π f)],   CategoryTheory.CategoryStruct.comp (CategoryTheor
y.Abelian.factorThruImage f) (CategoryTheory.Abelian.image.ι f) = f
参数：f : P ⟶ Q；CategoryTheory.Limits.cokernel.π f；CategoryTheory.Abelian.factorThr
uImage f；CategoryTheory.Abelian.image.ι f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.kernel.lift_ι`：∀ {C : Type u} [inst : CategoryTheo
ry.Category.{v, u} C] [inst_1 : CategoryTheory.Limits.HasZeroMorphisms C] {X Y :
 C}   (f : X ⟶ Y) [inst_2…
· 使用定理 `CategoryTheory.Limits.cokernel.condition`：∀ {C : Type u} [inst : Categor
yTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Limits.HasZeroMorphisms C] {
X Y : C}   (f : X ⟶ Y) [inst_2…

--- 原说明 ---
`f` factors through its image via the canonical morphism `p`.
-/
protected theorem image.fac : Abelian.factorThruImage f ≫ image.ι f = f :=
  kernel.lift_ι _ _ _
/-
**CategoryTheory.Abelian.mono_factorThruImage** 是 Mathlib 中的一个实例，位于命名空间 `Categor
yTheory.Abelian`。
形式化陈述：mono_factorThruImage [Mono f] : Mono (Abelian.factorThruImage f)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.mono_of_mono_fac`：∀ {C : Type u} [inst : CategoryTheory.C
ategory.{v, u} C] {X Y Z : C} {f : Y ⟶ X} {g : Z ⟶ Y} {h : Z ⟶ X}   [CategoryThe
ory.Mono h], Category…
· 使用定理 `CategoryTheory.Abelian.image.fac`：∀ {C : Type u} [inst : CategoryTheory.
Category.{v, u} C] [inst_1 : CategoryTheory.Limits.HasZeroMorphisms C] {P Q : C}
   (f : P ⟶ Q) [inst_2…
-/
instance mono_factorThruImage [Mono f] : Mono (Abelian.factorThruImage f) :=
  mono_of_mono_fac <| image.fac f

end Image

section Coimage

variable [HasKernel f] [HasCokernel (kernel.ι f)]

/-- The cokernel of the kernel of `f` is called the (abelian) coimage of `f`. -/
/-
**CategoryTheory.Abelian.coimage** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Abeli
an`。
形式化陈述：{C : Type u} →   [inst : CategoryTheory.Category.{v, u} C] →     [inst_1 :
 CategoryTheory.Limits.HasZeroMorphisms C] →       {P Q : C} →         (f : P ⟶ 
Q) →           [inst_2 : CategoryTheory.Limits.HasKernel f] →             [Categ
oryTheory.Limits.HasCokernel (CategoryTheory.Limits.kernel.ι f)] → C
参数：f : P ⟶ Q；CategoryTheory.Limits.kernel.ι f。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The cokernel of the kernel of `f` is called the (abelian) coimage of `f`.
-/
protected abbrev coimage : C :=
  cokernel (kernel.ι f)

/-- The projection onto the coimage. -/
/-
**CategoryTheory.Abelian.coimage.** 是 Mathlib 中的一个缩写定义，位于命名空间 `CategoryTheory.Ab
elian`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The projection onto the coimage.
-/
protected abbrev coimage.π : P ⟶ Abelian.coimage f :=
  cokernel.π (kernel.ι f)

/-- There is a canonical monomorphism `i : coimage f ⟶ Q`. -/
/-
**CategoryTheory.Abelian.factorThruCoimage** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTh
eory.Abelian`。
形式化陈述：{C : Type u} →   [inst : CategoryTheory.Category.{v, u} C] →     [inst_1 :
 CategoryTheory.Limits.HasZeroMorphisms C] →       {P Q : C} →         (f : P ⟶ 
Q) →           [inst_2 : CategoryTheory.Limits.HasKernel f] →             [inst_
3 : CategoryTheory.Limits.HasCokernel (CategoryTheory.Limits.kernel.ι f)] →     
          CategoryTheory.Abelian.coimage f ⟶ Q
参数：f : P ⟶ Q；CategoryTheory.Limits.kernel.ι f。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.kernel.condition`：∀ {C : Type u} [inst : CategoryT
heory.Category.{v, u} C] [inst_1 : CategoryTheory.Limits.HasZeroMorphisms C] {X 
Y : C}   (f : X ⟶ Y) [inst_2…

--- 原说明 ---
There is a canonical monomorphism `i : coimage f ⟶ Q`.
-/
protected abbrev factorThruCoimage : Abelian.coimage f ⟶ Q :=
  cokernel.desc (kernel.ι f) f <| kernel.condition f

/-- `f` factors through its coimage via the canonical morphism `p`. -/
/-
**CategoryTheory.Abelian.coimage.fac** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.A
belian.coimage`。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] [inst_1 : Categor
yTheory.Limits.HasZeroMorphisms C] {P Q : C}   (f : P ⟶ Q) [inst_2 : CategoryThe
ory.Limits.HasKernel f]   [inst_3 : CategoryTheory.Limits.HasCokernel (CategoryT
heory.Limits.kernel.ι f)],   CategoryTheory.CategoryStruct.comp (CategoryTheory.
Abelian.coimage.π f) (CategoryTheory.Abelian.factorThruCoimage f) =     f
参数：f : P ⟶ Q；CategoryTheory.Limits.kernel.ι f；CategoryTheory.Abelian.coimage.π f
；CategoryTheory.Abelian.factorThruCoimage f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.cokernel.π_desc`：∀ {C : Type u} [inst : CategoryTh
eory.Category.{v, u} C] [inst_1 : CategoryTheory.Limits.HasZeroMorphisms C] {X Y
 : C}   (f : X ⟶ Y) [inst_2…
· 使用定理 `CategoryTheory.Limits.kernel.condition`：∀ {C : Type u} [inst : CategoryT
heory.Category.{v, u} C] [inst_1 : CategoryTheory.Limits.HasZeroMorphisms C] {X 
Y : C}   (f : X ⟶ Y) [inst_2…

--- 原说明 ---
`f` factors through its coimage via the canonical morphism `p`.
-/
protected theorem coimage.fac : coimage.π f ≫ Abelian.factorThruCoimage f = f :=
  cokernel.π_desc _ _ _
/-
**CategoryTheory.Abelian.epi_factorThruCoimage** 是 Mathlib 中的一个实例，位于命名空间 `Catego
ryTheory.Abelian`。
形式化陈述：epi_factorThruCoimage [Epi f] : Epi (Abelian.factorThruCoimage f)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.epi_of_epi_fac`：epi_of_epi_fac {f : X ⟶ Y} {g : Y ⟶ Z} {h
 : X ⟶ Z} [Epi h] (w : f ≫ g = h) : Epi g
· 使用定理 `CategoryTheory.Abelian.coimage.fac`：∀ {C : Type u} [inst : CategoryTheor
y.Category.{v, u} C] [inst_1 : CategoryTheory.Limits.HasZeroMorphisms C] {P Q : 
C}   (f : P ⟶ Q) [inst_2…
-/
instance epi_factorThruCoimage [Epi f] : Epi (Abelian.factorThruCoimage f) :=
  epi_of_epi_fac <| coimage.fac f

end Coimage

section Comparison

variable [HasCokernel f] [HasKernel f] [HasKernel (cokernel.π f)] [HasCokernel (kernel.ι f)]

/-- The canonical map from the abelian coimage to the abelian image.
In any abelian category this is an isomorphism.

Conversely, any additive category with kernels and cokernels and
in which this is always an isomorphism, is abelian. -/
@[stacks 0107]
/-
**CategoryTheory.Abelian.coimageImageComparison** 是 Mathlib 中的一个定义，位于命名空间 `Categ
oryTheory.Abelian`。
形式化陈述：coimageImageComparison : Abelian.coimage f ⟶ Abelian.image f
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The canonical map from the abelian coimage to the abelian image.
In any abelian category this is an isomorphism.

Conversely, any additive category with kernels and cokernels and
in which this is always an isomorphism, is abelian.
-/
def coimageImageComparison : Abelian.coimage f ⟶ Abelian.image f :=
  cokernel.desc (kernel.ι f) (kernel.lift (cokernel.π f) f (by simp)) (by ext; simp)

/-- An alternative formulation of the canonical map from the abelian coimage to the abelian image.
-/
/-
**CategoryTheory.Abelian.coimageImageComparison'** 是 Mathlib 中的一个定义，位于命名空间 `Cate
goryTheory.Abelian`。
形式化陈述：coimageImageComparison' : Abelian.coimage f ⟶ Abelian.image f
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An alternative formulation of the canonical map from the abelian coimage to the 
abelian image.
-/
def coimageImageComparison' : Abelian.coimage f ⟶ Abelian.image f :=
  kernel.lift (cokernel.π f) (cokernel.desc (kernel.ι f) f (by simp)) (by ext; simp)
/-
**CategoryTheory.Abelian.coimageImageComparison_eq_coimageImageComparison'** 是 M
athlib 中的一个定理，位于命名空间 `CategoryTheory.Abelian`。
形式化陈述：coimageImageComparison_eq_coimageImageComparison' : coimageImageComparison
 f = coimageImageComparison' f
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.coequalizer.hom_ext`：∀ {C : Type u} {X Y : C} [ins
t : CategoryTheory.Category.{v, u} C] {f g : X ⟶ Y}   [inst_1 : CategoryTheory.L
imits.HasCoequalizer f g] {W : …
· 使用定理 `CategoryTheory.Limits.equalizer.hom_ext`：∀ {C : Type u} {X Y : C} [inst 
: CategoryTheory.Category.{v, u} C] {f g : X ⟶ Y}   [inst_1 : CategoryTheory.Lim
its.HasEqualizer f g] {W : C}…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CategoryTheory.Limits.cokernel.π_desc`：∀ {C : Type u} [inst : CategoryTh
eory.Category.{v, u} C] [inst_1 : CategoryTheory.Limits.HasZeroMorphisms C] {X Y
 : C}   (f : X ⟶ Y) [inst_2…
· 使用定理 `CategoryTheory.Limits.kernel.lift_ι`：∀ {C : Type u} [inst : CategoryTheo
ry.Category.{v, u} C] [inst_1 : CategoryTheory.Limits.HasZeroMorphisms C] {X Y :
 C}   (f : X ⟶ Y) [inst_2…
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem coimageImageComparison_eq_coimageImageComparison' :
    coimageImageComparison f = coimageImageComparison' f := by
  ext
  simp [coimageImageComparison, coimageImageComparison']

@[reassoc (attr := simp)]
/-
**CategoryTheory.Abelian.coimage_image_factorisation** 是 Mathlib 中的一个定理，位于命名空间 `
CategoryTheory.Abelian`。
形式化陈述：coimage_image_factorisation : coimage.π f ≫ coimageImageComparison f ≫ ima
ge.ι f = f
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Limits.cokernel.π_desc_assoc`：∀ {C : Type u} [inst : Cate
goryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Limits.HasZeroMorphisms C
] {X Y : C}   (f : X ⟶ Y) [inst_2…
· 使用定理 `CategoryTheory.Limits.kernel.lift_ι`：∀ {C : Type u} [inst : CategoryTheo
ry.Category.{v, u} C] [inst_1 : CategoryTheory.Limits.HasZeroMorphisms C] {X Y :
 C}   (f : X ⟶ Y) [inst_2…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem coimage_image_factorisation : coimage.π f ≫ coimageImageComparison f ≫ image.ι f = f := by
  simp [coimageImageComparison]

end Comparison

variable [HasKernels C] [HasCokernels C]

set_option backward.defeqAttrib.useBackward true in
/-- The coimage-image comparison morphism is functorial. -/
@[simps! obj map]
/-
**CategoryTheory.Abelian.coimageImageComparisonFunctor** 是 Mathlib 中的一个定义，位于命名空间
 `CategoryTheory.Abelian`。
形式化陈述：coimageImageComparisonFunctor : Arrow C ⥤ Arrow C where obj f
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The coimage-image comparison morphism is functorial.
-/
def coimageImageComparisonFunctor : Arrow C ⥤ Arrow C where
  obj f := Arrow.mk (coimageImageComparison f.hom)
  map {f g} η := Arrow.homMk
    (cokernel.map _ _ (kernel.map _ _ η.left η.right (by simp)) η.left (by simp))
    (kernel.map _ _ η.right (cokernel.map _ _ η.left η.right (by simp)) (by simp)) (by cat_disch)

end CategoryTheory.Abelian

