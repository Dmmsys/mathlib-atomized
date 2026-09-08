/-
Copyright (c) 2025 Markus Himmel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel
-/
module

public import Mathlib.CategoryTheory.Abelian.Images
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Kernels

/-!
# Preservation of coimage-image comparisons

If a functor preserves kernels and cokernels, then it preserves abelian images, abelian coimages
and coimage-image comparisons.
-/

@[expose] public section

noncomputable section

universe v₁ v₂ u₁ u₂

open CategoryTheory Limits

namespace CategoryTheory.Abelian

variable {C : Type u₁} [Category.{v₁} C] [HasZeroMorphisms C]
variable {D : Type u₂} [Category.{v₂} D] [HasZeroMorphisms D]
variable (F : C ⥤ D) [F.PreservesZeroMorphisms]
variable {X Y : C} (f : X ⟶ Y)

section Images

variable [HasCokernel f] [HasKernel (cokernel.π f)] [PreservesColimit (parallelPair f 0) F]
  [PreservesLimit (parallelPair (cokernel.π f) 0) F] [HasCokernel (F.map f)]
  [HasKernel (cokernel.π (F.map f))]

/-- If a functor preserves kernels and cokernels, it preserves abelian images. -/
/-
**CategoryTheory.Abelian.PreservesImage.iso** 是 Mathlib 中的一个定义，位于命名空间 `CategoryT
heory.Abelian.PreservesImage`。
形式化陈述：{C : Type u₁} →   [inst : CategoryTheory.Category.{v₁, u₁} C] →     [inst_
1 : CategoryTheory.Limits.HasZeroMorphisms C] →       {D : Type u₂} →         [i
nst_2 : CategoryTheory.Category.{v₂, u₂} D] →           [inst_3 : CategoryTheory
.Limits.HasZeroMorphisms D] →             (F : CategoryTheory.Functor C D) →    
           [F.PreservesZeroMorphisms] →                 {X Y : C} →             
      (f : X ⟶ Y) →                     [inst_5 : CategoryTheory.Limits.HasCoker
nel f] →                       [inst_6 : CategoryTheory.Limits.HasKernel (Catego
ryTheory.Limits.cokernel.π f)] →                         [CategoryTheory.Limits.
PreservesColimit (CategoryTheory.Limits.parallelPair f 0) F] →                  
         [CategoryTheory.Limits.PreservesLimit                                 (
CategoryTheory.Limits.parallelPair (CategoryTheory.Limits.cokernel.π f) 0) F] → 
                            [inst_9 : CategoryTheory.Limits.HasCokernel (F.map f
)] →                               [inst_10 : CategoryTheory.Limits.HasKernel (C
ategoryTheory.Limits.cokernel.π (F.map f))] →                                 F.
obj (CategoryTheory.Abelian.image f) ≅ CategoryTheory.Abelian.image (F.map f)
参数：F : CategoryTheory.Functor C D；f : X ⟶ Y；CategoryTheory.Limits.cokernel.π f；C
ategoryTheory.Limits.parallelPair f 0；CategoryTheory.Limits.parallelPair (Catego
ryTheory.Limits.cokernel.π f) 0；F.map f；CategoryTheory.Limits.cokernel.π (F.map 
f)；CategoryTheory.Abelian.image f；F.map f。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If a functor preserves kernels and cokernels, it preserves abelian images.
-/
def PreservesImage.iso : F.obj (Abelian.image f) ≅ Abelian.image (F.map f) :=
  PreservesKernel.iso F _ ≪≫ kernel.mapIso _ _ (Iso.refl _) (PreservesCokernel.iso F _) (by simp)

@[reassoc (attr := simp)]
/-
**CategoryTheory.Abelian.PreservesImage.iso_hom_** 是 Mathlib 中的一个定理，位于命名空间 `Cate
goryTheory.Abelian`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem PreservesImage.iso_hom_ι :
    (PreservesImage.iso F f).hom ≫ Abelian.image.ι (F.map f) = F.map (Abelian.image.ι f) := by
  simp [iso]

@[reassoc (attr := simp)]
/-
**CategoryTheory.Abelian.PreservesImage.factorThruImage_iso_hom** 是 Mathlib 中的一个
定理，位于命名空间 `CategoryTheory.Abelian.PreservesImage`。
形式化陈述：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] [inst_1 : Cate
goryTheory.Limits.HasZeroMorphisms C]   {D : Type u₂} [inst_2 : CategoryTheory.C
ategory.{v₂, u₂} D] [inst_3 : CategoryTheory.Limits.HasZeroMorphisms D]   (F : C
ategoryTheory.Functor C D) [inst_4 : F.PreservesZeroMorphisms] {X Y : C} (f : X 
⟶ Y)   [inst_5 : CategoryTheory.Limits.HasCokernel f]   [inst_6 : CategoryTheory
.Limits.HasKernel (CategoryTheory.Limits.cokernel.π f)]   [inst_7 : CategoryTheo
ry.Limits.PreservesColimit (CategoryTheory.Limits.parallelPair f 0) F]   [inst_8
 :     CategoryTheory.Limits.PreservesLimit (CategoryTheory.Limits.parallelPair 
(CategoryTheory.Limits.cokernel.π f) 0) F]   [inst_9 : CategoryTheory.Limits.Has
Cokernel (F.map f)]   [inst_10 : CategoryTheory.Limits.HasKernel (CategoryTheory
.Limits.cokernel.π (F.map f))],   CategoryTheory.CategoryStruct.comp (F.map (Cat
egoryTheory.Abelian.factorThruImage f))       (CategoryTheory.Abelian.PreservesI
mage.iso F f).hom =     CategoryTheory.Abelian.factorThruImage (F.map f)
参数：F : CategoryTheory.Functor C D；f : X ⟶ Y；CategoryTheory.Limits.cokernel.π f；C
ategoryTheory.Limits.parallelPair f 0；CategoryTheory.Limits.parallelPair (Catego
ryTheory.Limits.cokernel.π f) 0；F.map f；CategoryTheory.Limits.cokernel.π (F.map 
f)；F.map (CategoryTheory.Abelian.factorThruImage f)；CategoryTheory.Abelian.Prese
rvesImage.iso F f；F.map f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.equalizer.hom_ext`：∀ {C : Type u} {X Y : C} [inst 
: CategoryTheory.Category.{v, u} C] {f g : X ⟶ Y}   [inst_1 : CategoryTheory.Lim
its.HasEqualizer f g] {W : C}…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Limits.cokernel.condition`：∀ {C : Type u} [inst : Categor
yTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Limits.HasZeroMorphisms C] {
X Y : C}   (f : X ⟶ Y) [inst_2…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CategoryTheory.Limits.PreservesKernel.iso_hom`：∀ {C : Type u₁} [inst : C
ategoryTheory.Category.{v₁, u₁} C] [inst_1 : CategoryTheory.Limits.HasZeroMorphi
sms C]   {D : Type u₂} [inst_2 : Ca…
· 使用定理 `CategoryTheory.Limits.kernel.mapIso_hom`：∀ {C : Type u} [inst : Category
Theory.Category.{v, u} C] [inst_1 : CategoryTheory.Limits.HasZeroMorphisms C] {X
 Y : C}   (f : X ⟶ Y) [inst_2…
· 使用定理 `CategoryTheory.Limits.map_lift_kernelComparison_assoc`：∀ {C : Type u} [i
nst : CategoryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Limits.HasZeroM
orphisms C] {X Y : C}   (f : X ⟶ Y) {D : Ty…
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.Limits.kernel.lift_ι`：∀ {C : Type u} [inst : CategoryTheo
ry.Category.{v, u} C] [inst_1 : CategoryTheory.Limits.HasZeroMorphisms C] {X Y :
 C}   (f : X ⟶ Y) [inst_2…
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem PreservesImage.factorThruImage_iso_hom :
    F.map (Abelian.factorThruImage f) ≫ (PreservesImage.iso F f).hom =
      Abelian.factorThruImage (F.map f) := by
  ext; simp [iso]

@[reassoc (attr := simp)]
/-
**CategoryTheory.Abelian.PreservesImage.iso_inv_** 是 Mathlib 中的一个定理，位于命名空间 `Cate
goryTheory.Abelian`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem PreservesImage.iso_inv_ι :
    (PreservesImage.iso F f).inv ≫ F.map (Abelian.image.ι f) = Abelian.image.ι (F.map f) := by
  simp [iso]

@[reassoc (attr := simp)]
/-
**CategoryTheory.Abelian.PreservesImage.factorThruImage_iso_inv** 是 Mathlib 中的一个
定理，位于命名空间 `CategoryTheory.Abelian.PreservesImage`。
形式化陈述：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] [inst_1 : Cate
goryTheory.Limits.HasZeroMorphisms C]   {D : Type u₂} [inst_2 : CategoryTheory.C
ategory.{v₂, u₂} D] [inst_3 : CategoryTheory.Limits.HasZeroMorphisms D]   (F : C
ategoryTheory.Functor C D) [inst_4 : F.PreservesZeroMorphisms] {X Y : C} (f : X 
⟶ Y)   [inst_5 : CategoryTheory.Limits.HasCokernel f]   [inst_6 : CategoryTheory
.Limits.HasKernel (CategoryTheory.Limits.cokernel.π f)]   [inst_7 : CategoryTheo
ry.Limits.PreservesColimit (CategoryTheory.Limits.parallelPair f 0) F]   [inst_8
 :     CategoryTheory.Limits.PreservesLimit (CategoryTheory.Limits.parallelPair 
(CategoryTheory.Limits.cokernel.π f) 0) F]   [inst_9 : CategoryTheory.Limits.Has
Cokernel (F.map f)]   [inst_10 : CategoryTheory.Limits.HasKernel (CategoryTheory
.Limits.cokernel.π (F.map f))],   CategoryTheory.CategoryStruct.comp (CategoryTh
eory.Abelian.factorThruImage (F.map f))       (CategoryTheory.Abelian.PreservesI
mage.iso F f).inv =     F.map (CategoryTheory.Abelian.factorThruImage f)
参数：F : CategoryTheory.Functor C D；f : X ⟶ Y；CategoryTheory.Limits.cokernel.π f；C
ategoryTheory.Limits.parallelPair f 0；CategoryTheory.Limits.parallelPair (Catego
ryTheory.Limits.cokernel.π f) 0；F.map f；CategoryTheory.Limits.cokernel.π (F.map 
f)；CategoryTheory.Abelian.factorThruImage (F.map f)；CategoryTheory.Abelian.Prese
rvesImage.iso F f；CategoryTheory.Abelian.factorThruImage f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Abelian.PreservesImage.factorThruImage_iso_hom`：∀ {C : Ty
pe u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] [inst_1 : CategoryTheory.Limi
ts.HasZeroMorphisms C]   {D : Type u₂} [inst_2 : Ca…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem PreservesImage.factorThruImage_iso_inv :
    Abelian.factorThruImage (F.map f) ≫ (PreservesImage.iso F f).inv =
      F.map (Abelian.factorThruImage f) := by
  simp [Iso.comp_inv_eq]

end Images

section Coimages

variable [HasKernel f] [HasCokernel (kernel.ι f)] [PreservesLimit (parallelPair f 0) F]
  [PreservesColimit (parallelPair (kernel.ι f) 0) F] [HasKernel (F.map f)]
  [HasCokernel (kernel.ι (F.map f))]

/-- If a functor preserves kernels and cokernels, it preserves abelian coimages. -/
/-
**CategoryTheory.Abelian.PreservesCoimage.iso** 是 Mathlib 中的一个定义，位于命名空间 `Categor
yTheory.Abelian.PreservesCoimage`。
形式化陈述：{C : Type u₁} →   [inst : CategoryTheory.Category.{v₁, u₁} C] →     [inst_
1 : CategoryTheory.Limits.HasZeroMorphisms C] →       {D : Type u₂} →         [i
nst_2 : CategoryTheory.Category.{v₂, u₂} D] →           [inst_3 : CategoryTheory
.Limits.HasZeroMorphisms D] →             (F : CategoryTheory.Functor C D) →    
           [F.PreservesZeroMorphisms] →                 {X Y : C} →             
      (f : X ⟶ Y) →                     [inst_5 : CategoryTheory.Limits.HasKerne
l f] →                       [inst_6 : CategoryTheory.Limits.HasCokernel (Catego
ryTheory.Limits.kernel.ι f)] →                         [CategoryTheory.Limits.Pr
eservesLimit (CategoryTheory.Limits.parallelPair f 0) F] →                      
     [CategoryTheory.Limits.PreservesColimit                                 (Ca
tegoryTheory.Limits.parallelPair (CategoryTheory.Limits.kernel.ι f) 0) F] →     
                        [inst_9 : CategoryTheory.Limits.HasKernel (F.map f)] →  
                             [inst_10 : CategoryTheory.Limits.HasCokernel (Categ
oryTheory.Limits.kernel.ι (F.map f))] →                                 F.obj (C
ategoryTheory.Abelian.coimage f) ≅ CategoryTheory.Abelian.coimage (F.map f)
参数：F : CategoryTheory.Functor C D；f : X ⟶ Y；CategoryTheory.Limits.kernel.ι f；Cat
egoryTheory.Limits.parallelPair f 0；CategoryTheory.Limits.parallelPair (Category
Theory.Limits.kernel.ι f) 0；F.map f；CategoryTheory.Limits.kernel.ι (F.map f)；Cat
egoryTheory.Abelian.coimage f；F.map f。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If a functor preserves kernels and cokernels, it preserves abelian coimages.
-/
def PreservesCoimage.iso : F.obj (Abelian.coimage f) ≅ Abelian.coimage (F.map f) :=
  PreservesCokernel.iso F _ ≪≫ cokernel.mapIso _ _ (PreservesKernel.iso F _) (Iso.refl _) (by simp)

@[reassoc (attr := simp)]
/-
**CategoryTheory.Abelian.PreservesCoimage.iso_hom_** 是 Mathlib 中的一个定理，位于命名空间 `Ca
tegoryTheory.Abelian`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem PreservesCoimage.iso_hom_π :
    F.map (Abelian.coimage.π f) ≫ (PreservesCoimage.iso F f).hom = Abelian.coimage.π (F.map f) := by
  simp [iso]

@[reassoc (attr := simp)]
/-
**CategoryTheory.Abelian.PreservesCoimage.factorThruCoimage_iso_inv** 是 Mathlib 
中的一个定理，位于命名空间 `CategoryTheory.Abelian.PreservesCoimage`。
形式化陈述：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] [inst_1 : Cate
goryTheory.Limits.HasZeroMorphisms C]   {D : Type u₂} [inst_2 : CategoryTheory.C
ategory.{v₂, u₂} D] [inst_3 : CategoryTheory.Limits.HasZeroMorphisms D]   (F : C
ategoryTheory.Functor C D) [inst_4 : F.PreservesZeroMorphisms] {X Y : C} (f : X 
⟶ Y)   [inst_5 : CategoryTheory.Limits.HasKernel f]   [inst_6 : CategoryTheory.L
imits.HasCokernel (CategoryTheory.Limits.kernel.ι f)]   [inst_7 : CategoryTheory
.Limits.PreservesLimit (CategoryTheory.Limits.parallelPair f 0) F]   [inst_8 :  
   CategoryTheory.Limits.PreservesColimit (CategoryTheory.Limits.parallelPair (C
ategoryTheory.Limits.kernel.ι f) 0) F]   [inst_9 : CategoryTheory.Limits.HasKern
el (F.map f)]   [inst_10 : CategoryTheory.Limits.HasCokernel (CategoryTheory.Lim
its.kernel.ι (F.map f))],   CategoryTheory.CategoryStruct.comp (CategoryTheory.A
belian.PreservesCoimage.iso F f).inv       (F.map (CategoryTheory.Abelian.factor
ThruCoimage f)) =     CategoryTheory.Abelian.factorThruCoimage (F.map f)
参数：F : CategoryTheory.Functor C D；f : X ⟶ Y；CategoryTheory.Limits.kernel.ι f；Cat
egoryTheory.Limits.parallelPair f 0；CategoryTheory.Limits.parallelPair (Category
Theory.Limits.kernel.ι f) 0；F.map f；CategoryTheory.Limits.kernel.ι (F.map f)；Cat
egoryTheory.Abelian.PreservesCoimage.iso F f；F.map (CategoryTheory.Abelian.facto
rThruCoimage f)；F.map f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.coequalizer.hom_ext`：∀ {C : Type u} {X Y : C} [ins
t : CategoryTheory.Category.{v, u} C] {f g : X ⟶ Y}   [inst_1 : CategoryTheory.L
imits.HasCoequalizer f g] {W : …
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Limits.kernel.condition`：∀ {C : Type u} [inst : CategoryT
heory.Category.{v, u} C] [inst_1 : CategoryTheory.Limits.HasZeroMorphisms C] {X 
Y : C}   (f : X ⟶ Y) [inst_2…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CategoryTheory.Limits.cokernel.mapIso_inv`：∀ {C : Type u} [inst : Catego
ryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Limits.HasZeroMorphisms C] 
{X Y : C}   (f : X ⟶ Y) [inst_2…
· 使用定理 `CategoryTheory.Limits.PreservesCokernel.iso_inv`：∀ {C : Type u₁} [inst :
 CategoryTheory.Category.{v₁, u₁} C] [inst_1 : CategoryTheory.Limits.HasZeroMorp
hisms C]   {D : Type u₂} [inst_2 : Ca…
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.Limits.cokernelComparison_map_desc`：cokernelComparison_ma
p_desc [HasCokernel f] [HasCokernel (G.map f)] {Z : C} {h : Y ⟶ Z} (w : f ≫ h = 
0) : cokernelComparison f G ≫ G.map (co…
· 使用定理 `CategoryTheory.Limits.cokernel.π_desc_assoc`：∀ {C : Type u} [inst : Cate
goryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Limits.HasZeroMorphisms C
] {X Y : C}   (f : X ⟶ Y) [inst_2…
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用定理 `CategoryTheory.Limits.cokernel.π_desc`：∀ {C : Type u} [inst : CategoryTh
eory.Category.{v, u} C] [inst_1 : CategoryTheory.Limits.HasZeroMorphisms C] {X Y
 : C}   (f : X ⟶ Y) [inst_2…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem PreservesCoimage.factorThruCoimage_iso_inv :
    (PreservesCoimage.iso F f).inv ≫ F.map (Abelian.factorThruCoimage f) =
      Abelian.factorThruCoimage (F.map f) := by
  ext; simp [iso]

@[reassoc (attr := simp)]
/-
**CategoryTheory.Abelian.PreservesCoimage.factorThruCoimage_iso_hom** 是 Mathlib 
中的一个定理，位于命名空间 `CategoryTheory.Abelian.PreservesCoimage`。
形式化陈述：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] [inst_1 : Cate
goryTheory.Limits.HasZeroMorphisms C]   {D : Type u₂} [inst_2 : CategoryTheory.C
ategory.{v₂, u₂} D] [inst_3 : CategoryTheory.Limits.HasZeroMorphisms D]   (F : C
ategoryTheory.Functor C D) [inst_4 : F.PreservesZeroMorphisms] {X Y : C} (f : X 
⟶ Y)   [inst_5 : CategoryTheory.Limits.HasKernel f]   [inst_6 : CategoryTheory.L
imits.HasCokernel (CategoryTheory.Limits.kernel.ι f)]   [inst_7 : CategoryTheory
.Limits.PreservesLimit (CategoryTheory.Limits.parallelPair f 0) F]   [inst_8 :  
   CategoryTheory.Limits.PreservesColimit (CategoryTheory.Limits.parallelPair (C
ategoryTheory.Limits.kernel.ι f) 0) F]   [inst_9 : CategoryTheory.Limits.HasKern
el (F.map f)]   [inst_10 : CategoryTheory.Limits.HasCokernel (CategoryTheory.Lim
its.kernel.ι (F.map f))],   CategoryTheory.CategoryStruct.comp (CategoryTheory.A
belian.PreservesCoimage.iso F f).hom       (CategoryTheory.Abelian.factorThruCoi
mage (F.map f)) =     F.map (CategoryTheory.Abelian.factorThruCoimage f)
参数：F : CategoryTheory.Functor C D；f : X ⟶ Y；CategoryTheory.Limits.kernel.ι f；Cat
egoryTheory.Limits.parallelPair f 0；CategoryTheory.Limits.parallelPair (Category
Theory.Limits.kernel.ι f) 0；F.map f；CategoryTheory.Limits.kernel.ι (F.map f)；Cat
egoryTheory.Abelian.PreservesCoimage.iso F f；CategoryTheory.Abelian.factorThruCo
image (F.map f)；CategoryTheory.Abelian.factorThruCoimage f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Abelian.PreservesCoimage.factorThruCoimage_iso_inv`：∀ {C 
: Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] [inst_1 : CategoryTheory.
Limits.HasZeroMorphisms C]   {D : Type u₂} [inst_2 : Ca…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem PreservesCoimage.factorThruCoimage_iso_hom :
    (PreservesCoimage.iso F f).hom ≫ Abelian.factorThruCoimage (F.map f) =
      F.map (Abelian.factorThruCoimage f) := by
  simp [← Iso.eq_inv_comp]

@[reassoc (attr := simp)]
/-
**CategoryTheory.Abelian.PreservesCoimage.iso_inv_** 是 Mathlib 中的一个定理，位于命名空间 `Ca
tegoryTheory.Abelian`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem PreservesCoimage.iso_inv_π :
    Abelian.coimage.π (F.map f) ≫ (PreservesCoimage.iso F f).inv = F.map (Abelian.coimage.π f) := by
  simp [Iso.comp_inv_eq]

end Coimages

variable [HasKernel f] [HasCokernel f] [HasKernel (cokernel.π f)] [HasCokernel (kernel.ι f)]
  [PreservesLimit (parallelPair f 0) F] [PreservesColimit (parallelPair f 0) F]
  [PreservesLimit (parallelPair (cokernel.π f) 0) F]
  [PreservesColimit (parallelPair (kernel.ι f) 0) F]
  [HasKernel (cokernel.π (F.map f))] [HasCokernel (kernel.ι (F.map f))]

/-
**CategoryTheory.Abelian.PreservesCoimage.hom_coimageImageComparison** 是 Mathlib
 中的一个定理，位于命名空间 `CategoryTheory.Abelian.PreservesCoimage`。
形式化陈述：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] [inst_1 : Cate
goryTheory.Limits.HasZeroMorphisms C]   {D : Type u₂} [inst_2 : CategoryTheory.C
ategory.{v₂, u₂} D] [inst_3 : CategoryTheory.Limits.HasZeroMorphisms D]   (F : C
ategoryTheory.Functor C D) [inst_4 : F.PreservesZeroMorphisms] {X Y : C} (f : X 
⟶ Y)   [inst_5 : CategoryTheory.Limits.HasKernel f] [inst_6 : CategoryTheory.Lim
its.HasCokernel f]   [inst_7 : CategoryTheory.Limits.HasKernel (CategoryTheory.L
imits.cokernel.π f)]   [inst_8 : CategoryTheory.Limits.HasCokernel (CategoryTheo
ry.Limits.kernel.ι f)]   [inst_9 : CategoryTheory.Limits.PreservesLimit (Categor
yTheory.Limits.parallelPair f 0) F]   [inst_10 : CategoryTheory.Limits.Preserves
Colimit (CategoryTheory.Limits.parallelPair f 0) F]   [inst_11 :     CategoryThe
ory.Limits.PreservesLimit (CategoryTheory.Limits.parallelPair (CategoryTheory.Li
mits.cokernel.π f) 0) F]   [inst_12 :     CategoryTheory.Limits.PreservesColimit
 (CategoryTheory.Limits.parallelPair (CategoryTheory.Limits.kernel.ι f) 0) F]   
[inst_13 : CategoryTheory.Limits.HasKernel (CategoryTheory.Limits.cokernel.π (F.
map f))]   [inst_14 : CategoryTheory.Limits.HasCokernel (CategoryTheory.Limits.k
ernel.ι (F.map f))],   CategoryTheory.CategoryStruct.comp (CategoryTheory.Abelia
n.PreservesCoimage.iso F f).hom       (CategoryTheory.Abelian.coimageImageCompar
ison (F.map f)) =     CategoryTheory.CategoryStruct.comp (F.map (CategoryTheory.
Abelian.coimageImageComparison f))       (CategoryTheory.Abelian.PreservesImage.
iso F f).hom
参数：F : CategoryTheory.Functor C D；f : X ⟶ Y；CategoryTheory.Limits.cokernel.π f；C
ategoryTheory.Limits.kernel.ι f；CategoryTheory.Limits.parallelPair f 0；CategoryT
heory.Limits.parallelPair f 0；CategoryTheory.Limits.parallelPair (CategoryTheory
.Limits.cokernel.π f) 0；CategoryTheory.Limits.parallelPair (CategoryTheory.Limit
s.kernel.ι f) 0；CategoryTheory.Limits.cokernel.π (F.map f)；CategoryTheory.Limits
.kernel.ι (F.map f)；CategoryTheory.Abelian.PreservesCoimage.iso F f；CategoryTheo
ry.Abelian.coimageImageComparison (F.map f)；F.map (CategoryTheory.Abelian.coimag
eImageComparison f)；CategoryTheory.Abelian.PreservesImage.iso F f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.instHasCokernelMapOfPreservesColimitWalkingParalle
lPairParallelPairOfNatHom`：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, 
u₁} C] [inst_1 : CategoryTheory.Limits.HasZeroMorphisms C]   {D : Type u₂} [inst
_2 : Ca…
· 使用定理 `CategoryTheory.Limits.instHasKernelMapOfPreservesLimitWalkingParallelPai
rParallelPairOfNatHom`：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} 
C] [inst_1 : CategoryTheory.Limits.HasZeroMorphisms C]   {D : Type u₂} [inst_2 :
 Ca…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.cancel_mono`：∀ {C : Type u} [inst : CategoryTheory.Catego
ry.{v, u} C] {X Y Z : C} (f : Y ⟶ X) [CategoryTheory.Mono f] {g h : Z ⟶ Y},   Ca
tegoryTheory.Cat…
· 使用定理 `CategoryTheory.Limits.equalizer.ι_mono`：∀ {C : Type u} {X Y : C} [inst :
 CategoryTheory.Category.{v, u} C] {f g : X ⟶ Y}   [inst_1 : CategoryTheory.Limi
ts.HasEqualizer f g], Catego…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.Abelian.PreservesImage.iso_hom_ι`：∀ {C : Type u₁} [inst :
 CategoryTheory.Category.{v₁, u₁} C] [inst_1 : CategoryTheory.Limits.HasZeroMorp
hisms C]   {D : Type u₂} [inst_2 : Ca…
· 使用定理 `CategoryTheory.cancel_epi`：cancel_epi (f : X ⟶ Y) [Epi f] {g h : Y ⟶ Z} 
: f ≫ g = f ≫ h ↔ g = h
· 使用定理 `CategoryTheory.Limits.coequalizer.π_epi`：∀ {C : Type u} {X Y : C} [inst 
: CategoryTheory.Category.{v, u} C] {f g : X ⟶ Y}   [inst_1 : CategoryTheory.Lim
its.HasCoequalizer f g], Cate…
· 使用定理 `CategoryTheory.Abelian.coimage_image_factorisation`：coimage_image_factor
isation : coimage.π f ≫ coimageImageComparison f ≫ image.ι f = f
· 使用定理 `CategoryTheory.Abelian.PreservesCoimage.iso_inv_π_assoc`：∀ {C : Type u₁}
 [inst : CategoryTheory.Category.{v₁, u₁} C] [inst_1 : CategoryTheory.Limits.Has
ZeroMorphisms C]   {D : Type u₂} [inst_2 : Ca…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem PreservesCoimage.hom_coimageImageComparison :
    (PreservesCoimage.iso F f).hom ≫ coimageImageComparison (F.map f) =
      F.map (coimageImageComparison f) ≫ (PreservesImage.iso F f).hom := by
  simp [← Functor.map_comp, ← Iso.eq_inv_comp, ← cancel_epi (Abelian.coimage.π (F.map f)),
    ← cancel_mono (Abelian.image.ι (F.map f))]

/-- If a functor preserves kernels and cokernels, it preserves coimage-image comparisons. -/
@[simps!]
/-
**CategoryTheory.Abelian.PreservesCoimageImageComparison.iso** 是 Mathlib 中的一个定义，
位于命名空间 `CategoryTheory.Abelian.PreservesCoimageImageComparison`。
形式化陈述：{C : Type u₁} →   [inst : CategoryTheory.Category.{v₁, u₁} C] →     [inst_
1 : CategoryTheory.Limits.HasZeroMorphisms C] →       {D : Type u₂} →         [i
nst_2 : CategoryTheory.Category.{v₂, u₂} D] →           [inst_3 : CategoryTheory
.Limits.HasZeroMorphisms D] →             (F : CategoryTheory.Functor C D) →    
           [inst_4 : F.PreservesZeroMorphisms] →                 {X Y : C} →    
               (f : X ⟶ Y) →                     [inst_5 : CategoryTheory.Limits
.HasKernel f] →                       [inst_6 : CategoryTheory.Limits.HasCokerne
l f] →                         [inst_7 : CategoryTheory.Limits.HasKernel (Catego
ryTheory.Limits.cokernel.π f)] →                           [inst_8 : CategoryThe
ory.Limits.HasCokernel (CategoryTheory.Limits.kernel.ι f)] →                    
         [inst_9 : CategoryTheory.Limits.PreservesLimit (CategoryTheory.Limits.p
arallelPair f 0) F] →                               [inst_10 :                  
                 CategoryTheory.Limits.PreservesColimit (CategoryTheory.Limits.p
arallelPair f 0) F] →                                 [CategoryTheory.Limits.Pre
servesLimit                                       (CategoryTheory.Limits.paralle
lPair (CategoryTheory.Limits.cokernel.π f) 0) F] →                              
     [CategoryTheory.Limits.PreservesColimit                                    
     (CategoryTheory.Limits.parallelPair (CategoryTheory.Limits.kernel.ι f) 0) F
] →                                     [inst_13 :                              
           CategoryTheory.Limits.HasKernel (CategoryTheory.Limits.cokernel.π (F.
map f))] →                                       [inst_14 :                     
                      CategoryTheory.Limits.HasCokernel                         
                    (CategoryTheory.Limits.kernel.ι (F.map f))] →               
                          CategoryTheory.Arrow.mk                               
              (F.map (CategoryTheory.Abelian.coimageImageComparison f)) ≅       
                                    CategoryTheory.Arrow.mk                     
                        (CategoryTheory.Abelian.coimageImageComparison (F.map f)
)
参数：F : CategoryTheory.Functor C D；f : X ⟶ Y；CategoryTheory.Limits.cokernel.π f；C
ategoryTheory.Limits.kernel.ι f；CategoryTheory.Limits.parallelPair f 0；CategoryT
heory.Limits.parallelPair f 0；CategoryTheory.Limits.parallelPair (CategoryTheory
.Limits.cokernel.π f) 0；CategoryTheory.Limits.parallelPair (CategoryTheory.Limit
s.kernel.ι f) 0；CategoryTheory.Limits.cokernel.π (F.map f)；CategoryTheory.Limits
.kernel.ι (F.map f)；F.map (CategoryTheory.Abelian.coimageImageComparison f)；Cate
goryTheory.Abelian.coimageImageComparison (F.map f)。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.instHasCokernelMapOfPreservesColimitWalkingParalle
lPairParallelPairOfNatHom`：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, 
u₁} C] [inst_1 : CategoryTheory.Limits.HasZeroMorphisms C]   {D : Type u₂} [inst
_2 : Ca…
· 使用定理 `CategoryTheory.Limits.instHasKernelMapOfPreservesLimitWalkingParallelPai
rParallelPairOfNatHom`：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} 
C] [inst_1 : CategoryTheory.Limits.HasZeroMorphisms C]   {D : Type u₂} [inst_2 :
 Ca…
· 使用定理 `CategoryTheory.Abelian.PreservesCoimage.hom_coimageImageComparison`：∀ {C
 : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] [inst_1 : CategoryTheory
.Limits.HasZeroMorphisms C]   {D : Type u₂} [inst_2 : Ca…

--- 原说明 ---
If a functor preserves kernels and cokernels, it preserves coimage-image compari
sons.
-/
def PreservesCoimageImageComparison.iso :
    Arrow.mk (F.map (coimageImageComparison f)) ≅ Arrow.mk (coimageImageComparison (F.map f)) :=
  Arrow.isoMk' _ _ (PreservesCoimage.iso F f) (PreservesImage.iso F f)
    (PreservesCoimage.hom_coimageImageComparison F f)

end CategoryTheory.Abelian

