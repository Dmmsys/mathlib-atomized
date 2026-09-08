/-
Copyright (c) 2021 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import Mathlib.CategoryTheory.Subobject.Limits

/-!
# Image-to-kernel comparison maps

Whenever `f : A ⟶ B` and `g : B ⟶ C` satisfy `w : f ≫ g = 0`,
we have `image_le_kernel f g w : imageSubobject f ≤ kernelSubobject g`
(assuming the appropriate images and kernels exist).

`imageToKernel f g w` is the corresponding morphism between objects in `C`.

-/

@[expose] public section

universe v u w

open CategoryTheory CategoryTheory.Limits

variable {ι : Type*}
variable {V : Type u} [Category.{v} V] [HasZeroMorphisms V]

noncomputable section

section

variable {A B C : V} (f : A ⟶ B) [HasImage f] (g : B ⟶ C) [HasKernel g]

/-
**image_le_kernel** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：image_le_kernel (w : f ≫ g = 0) : imageSubobject f <= kernelSubobject g
参数：w : f ≫ g = 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.imageSubobject_le_mk`：imageSubobject_le_mk {A B : 
C} {X : C} (g : X ⟶ B) [Mono g] (f : A ⟶ B) [HasImage f] (h : A ⟶ X) (w : h ≫ g 
= f) : imageSubobject f <= Subob…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Limits.kernel.lift_ι`：∀ {C : Type u} [inst : CategoryTheo
ry.Category.{v, u} C] [inst_1 : CategoryTheory.Limits.HasZeroMorphisms C] {X Y :
 C}   (f : X ⟶ Y) [inst_2…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem image_le_kernel (w : f ≫ g = 0) : imageSubobject f ≤ kernelSubobject g :=
  imageSubobject_le_mk _ _ (kernel.lift _ _ w) (by simp)

/-- The canonical morphism `imageSubobject f ⟶ kernelSubobject g` when `f ≫ g = 0`.
-/
/-
**imageToKernel** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：imageToKernel (w : f ≫ g = 0) : (imageSubobject f : V) ⟶ (kernelSubobject 
g : V)
参数：w : f ≫ g = 0。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `image_le_kernel`：image_le_kernel (w : f ≫ g = 0) : imageSubobject f <= k
ernelSubobject g

--- 原说明 ---
The canonical morphism `imageSubobject f ⟶ kernelSubobject g` when `f ≫ g = 0`.
-/
def imageToKernel (w : f ≫ g = 0) : (imageSubobject f : V) ⟶ (kernelSubobject g : V) :=
  Subobject.ofLE _ _ (image_le_kernel _ _ w)
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (w : f ≫ g = 0) : Mono (imageToKernel f g w) := by
  dsimp only [imageToKernel]
  infer_instance

/-- Prefer `imageToKernel`. -/
@[simp]
/-
**subobject_ofLE_as_imageToKernel** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：subobject_ofLE_as_imageToKernel (w : f ≫ g = 0) (h) : Subobject.ofLE (imag
eSubobject f) (kernelSubobject g) h = imageToKernel f g w
参数：w : f ≫ g = 0；h。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Prefer `imageToKernel`.
-/
theorem subobject_ofLE_as_imageToKernel (w : f ≫ g = 0) (h) :
    Subobject.ofLE (imageSubobject f) (kernelSubobject g) h = imageToKernel f g w :=
  rfl

@[reassoc (attr := simp), elementwise (attr := simp)]
/-
**imageToKernel_arrow** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：imageToKernel_arrow (w : f ≫ g = 0) : imageToKernel f g w ≫ (kernelSubobje
ct g).arrow = (imageSubobject f).arrow
参数：w : f ≫ g = 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Subobject.ofLE_arrow`：ofLE_arrow {B : C} {X Y : Subobject
 B} (h : X <= Y) : ofLE X Y h ≫ Y.arrow = X.arrow
· 使用定理 `image_le_kernel`：image_le_kernel (w : f ≫ g = 0) : imageSubobject f <= k
ernelSubobject g
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem imageToKernel_arrow (w : f ≫ g = 0) :
    imageToKernel f g w ≫ (kernelSubobject g).arrow = (imageSubobject f).arrow := by
  simp [imageToKernel]

-- This is less useful as a `simp` lemma than it initially appears,
-- as it "loses" the information the morphism factors through the image.
/-
**factorThruImageSubobject_comp_imageToKernel** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：factorThruImageSubobject_comp_imageToKernel (w : f ≫ g = 0) : factorThruIm
ageSubobject f ≫ imageToKernel f g w = factorThruKernelSubobject g f w
参数：w : f ≫ g = 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Subobject.eq_of_comp_arrow_eq`：eq_of_comp_arrow_eq {X Y :
 C} {P : Subobject Y} {f g : X ⟶ P} (h : f ≫ P.arrow = g ≫ P.arrow) : f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `imageToKernel_arrow`：imageToKernel_arrow (w : f ≫ g = 0) : imageToKernel
 f g w ≫ (kernelSubobject g).arrow = (imageSubobject f).arrow
· 使用定理 `CategoryTheory.Limits.imageSubobject_arrow_comp`：imageSubobject_arrow_co
mp : factorThruImageSubobject f ≫ (imageSubobject f).arrow = f
· 使用定理 `CategoryTheory.Limits.factorThruKernelSubobject_comp_arrow`：factorThruKe
rnelSubobject_comp_arrow {W : C} (h : W ⟶ X) (w : h ≫ f = 0) : factorThruKernelS
ubobject f h w ≫ (kernelSubobject f).arrow = h
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem factorThruImageSubobject_comp_imageToKernel (w : f ≫ g = 0) :
    factorThruImageSubobject f ≫ imageToKernel f g w = factorThruKernelSubobject g f w := by
  ext
  simp

end

section

variable {A B C : V} (f : A ⟶ B) (g : B ⟶ C)

@[simp]
/-
**imageToKernel_zero_left** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：imageToKernel_zero_left [HasKernels V] [HasZeroObject V] {w} : imageToKern
el (0 : A ⟶ B) g w = 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Subobject.eq_of_comp_arrow_eq`：eq_of_comp_arrow_eq {X Y :
 C} {P : Subobject Y} {f g : X ⟶ P} (h : f ≫ P.arrow = g ≫ P.arrow) : f = g
· 使用定理 `CategoryTheory.Limits.HasKernels.has_limit`：∀ {C : Type u} {inst : Categ
oryTheory.Category.{v, u} C} {inst_1 : CategoryTheory.Limits.HasZeroMorphisms C}
   [self : CategoryTheory.Limits…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `imageToKernel_arrow`：imageToKernel_arrow (w : f ≫ g = 0) : imageToKernel
 f g w ≫ (kernelSubobject g).arrow = (imageSubobject f).arrow
· 使用定理 `CategoryTheory.Limits.imageSubobject_zero_arrow`：imageSubobject_zero_arr
ow : (imageSubobject (0 : X ⟶ Y)).arrow = 0
· 使用定理 `CategoryTheory.Limits.zero_comp`：zero_comp [HasZeroMorphisms C] {X : C} 
{Y Z : C} {f : Y ⟶ Z} : (0 : X ⟶ Y) ≫ f = (0 : X ⟶ Z)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem imageToKernel_zero_left [HasKernels V] [HasZeroObject V] {w} :
    imageToKernel (0 : A ⟶ B) g w = 0 := by
  ext
  simp
/-
**imageToKernel_zero_right** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：imageToKernel_zero_right [HasImages V] {w} : imageToKernel f (0 : B ⟶ C) w
 = (imageSubobject f).arrow ≫ inv (kernelSubobject (0 : B ⟶ C)).arrow
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `CategoryTheory.Limits.HasImages.has_image`：∀ {C : Type u} {inst : Catego
ryTheory.Category.{v, u} C} [self : CategoryTheory.Limits.HasImages C] {X Y : C}
   (f : X ⟶ Y), CategoryTheory.…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `imageToKernel_arrow`：imageToKernel_arrow (w : f ≫ g = 0) : imageToKernel
 f g w ≫ (kernelSubobject g).arrow = (imageSubobject f).arrow
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem imageToKernel_zero_right [HasImages V] {w} :
    imageToKernel f (0 : B ⟶ C) w =
      (imageSubobject f).arrow ≫ inv (kernelSubobject (0 : B ⟶ C)).arrow := by
  simp

section

variable [HasKernels V] [HasImages V]

/-
**imageToKernel_comp_right** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：imageToKernel_comp_right {D : V} (h : C ⟶ D) (w : f ≫ g = 0) : imageToKern
el f (g ≫ h) (by simp [reassoc_of% w]) = imageToKernel f g w ≫ Subobject.ofLE _ 
_ (kernelSubobject_comp_le g h)
参数：h : C ⟶ D；w : f ≫ g = 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Subobject.eq_of_comp_arrow_eq`：eq_of_comp_arrow_eq {X Y :
 C} {P : Subobject Y} {f g : X ⟶ P} (h : f ≫ P.arrow = g ≫ P.arrow) : f = g
· 使用定理 `CategoryTheory.Limits.HasImages.has_image`：∀ {C : Type u} {inst : Catego
ryTheory.Category.{v, u} C} [self : CategoryTheory.Limits.HasImages C] {X Y : C}
   (f : X ⟶ Y), CategoryTheory.…
· 使用定理 `CategoryTheory.Limits.HasKernels.has_limit`：∀ {C : Type u} {inst : Categ
oryTheory.Category.{v, u} C} {inst_1 : CategoryTheory.Limits.HasZeroMorphisms C}
   [self : CategoryTheory.Limits…
· 使用定理 `CategoryTheory.Limits.kernelSubobject_comp_le`：kernelSubobject_comp_le (
f : X ⟶ Y) [HasKernel f] {Z : C} (h : Y ⟶ Z) [HasKernel (f ≫ h)] : kernelSubobje
ct f <= kernelSubobject (f ≫ h)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `imageToKernel_arrow`：imageToKernel_arrow (w : f ≫ g = 0) : imageToKernel
 f g w ≫ (kernelSubobject g).arrow = (imageSubobject f).arrow
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.Subobject.ofLE_arrow`：ofLE_arrow {B : C} {X Y : Subobject
 B} (h : X <= Y) : ofLE X Y h ≫ Y.arrow = X.arrow
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem imageToKernel_comp_right {D : V} (h : C ⟶ D) (w : f ≫ g = 0) :
    imageToKernel f (g ≫ h) (by simp [reassoc_of% w]) =
      imageToKernel f g w ≫ Subobject.ofLE _ _ (kernelSubobject_comp_le g h) := by
  ext
  simp
/-
**imageToKernel_comp_left** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：imageToKernel_comp_left {Z : V} (h : Z ⟶ A) (w : f ≫ g = 0) : imageToKerne
l (h ≫ f) g (by simp [w]) = Subobject.ofLE _ _ (imageSubobject_comp_le h f) ≫ im
ageToKernel f g w
参数：h : Z ⟶ A；w : f ≫ g = 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Subobject.eq_of_comp_arrow_eq`：eq_of_comp_arrow_eq {X Y :
 C} {P : Subobject Y} {f g : X ⟶ P} (h : f ≫ P.arrow = g ≫ P.arrow) : f = g
· 使用定理 `CategoryTheory.Limits.HasImages.has_image`：∀ {C : Type u} {inst : Catego
ryTheory.Category.{v, u} C} [self : CategoryTheory.Limits.HasImages C] {X Y : C}
   (f : X ⟶ Y), CategoryTheory.…
· 使用定理 `CategoryTheory.Limits.HasKernels.has_limit`：∀ {C : Type u} {inst : Categ
oryTheory.Category.{v, u} C} {inst_1 : CategoryTheory.Limits.HasZeroMorphisms C}
   [self : CategoryTheory.Limits…
· 使用定理 `CategoryTheory.Limits.imageSubobject_comp_le`：imageSubobject_comp_le {X'
 : C} (h : X' ⟶ X) (f : X ⟶ Y) [HasImage f] [HasImage (h ≫ f)] : imageSubobject 
(h ≫ f) <= imageSubobject f
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `imageToKernel_arrow`：imageToKernel_arrow (w : f ≫ g = 0) : imageToKernel
 f g w ≫ (kernelSubobject g).arrow = (imageSubobject f).arrow
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.Subobject.ofLE_arrow`：ofLE_arrow {B : C} {X Y : Subobject
 B} (h : X <= Y) : ofLE X Y h ≫ Y.arrow = X.arrow
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem imageToKernel_comp_left {Z : V} (h : Z ⟶ A) (w : f ≫ g = 0) :
    imageToKernel (h ≫ f) g (by simp [w]) =
      Subobject.ofLE _ _ (imageSubobject_comp_le h f) ≫ imageToKernel f g w := by
  ext
  simp

@[simp]
/-
**imageToKernel_comp_mono** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：imageToKernel_comp_mono {D : V} (h : C ⟶ D) [Mono h] (w) : imageToKernel f
 (g ≫ h) w = imageToKernel f g ((cancel_mono h).mp (by simpa using w : (f ≫ g) ≫
 h = 0 ≫ h)) ≫ (Subobject.isoOfEq _ _ (kernelSubobject_comp_mono g h)).inv
参数：h : C ⟶ D；w。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Subobject.eq_of_comp_arrow_eq`：eq_of_comp_arrow_eq {X Y :
 C} {P : Subobject Y} {f g : X ⟶ P} (h : f ≫ P.arrow = g ≫ P.arrow) : f = g
· 使用定理 `CategoryTheory.Limits.HasImages.has_image`：∀ {C : Type u} {inst : Catego
ryTheory.Category.{v, u} C} [self : CategoryTheory.Limits.HasImages C] {X Y : C}
   (f : X ⟶ Y), CategoryTheory.…
· 使用定理 `CategoryTheory.Limits.HasKernels.has_limit`：∀ {C : Type u} {inst : Categ
oryTheory.Category.{v, u} C} {inst_1 : CategoryTheory.Limits.HasZeroMorphisms C}
   [self : CategoryTheory.Limits…
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `CategoryTheory.cancel_mono`：∀ {C : Type u} [inst : CategoryTheory.Catego
ry.{v, u} C] {X Y Z : C} (f : Y ⟶ X) [CategoryTheory.Mono f] {g h : Z ⟶ Y},   Ca
tegoryTheory.Cat…
· 使用定理 `CategoryTheory.Limits.kernelSubobject_comp_mono`：kernelSubobject_comp_mo
no (f : X ⟶ Y) [HasKernel f] {Z : C} (h : Y ⟶ Z) [Mono h] : kernelSubobject (f ≫
 h) = kernelSubobject f
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `imageToKernel_arrow`：imageToKernel_arrow (w : f ≫ g = 0) : imageToKernel
 f g w ≫ (kernelSubobject g).arrow = (imageSubobject f).arrow
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CategoryTheory.Subobject.isoOfEq_inv`：∀ {C : Type u₁} [inst : CategoryTh
eory.Category.{v₁, u₁} C] {B : C} (X Y : CategoryTheory.Subobject B) (h : X = Y)
,   (X.isoOfEq Y h).inv = …
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.Subobject.ofLE_arrow`：ofLE_arrow {B : C} {X Y : Subobject
 B} (h : X <= Y) : ofLE X Y h ≫ Y.arrow = X.arrow
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem imageToKernel_comp_mono {D : V} (h : C ⟶ D) [Mono h] (w) :
    imageToKernel f (g ≫ h) w =
      imageToKernel f g ((cancel_mono h).mp (by simpa using w : (f ≫ g) ≫ h = 0 ≫ h)) ≫
        (Subobject.isoOfEq _ _ (kernelSubobject_comp_mono g h)).inv := by
  ext
  simp

@[simp]
/-
**imageToKernel_epi_comp** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：imageToKernel_epi_comp {Z : V} (h : Z ⟶ A) [Epi h] (w) : imageToKernel (h 
≫ f) g w = Subobject.ofLE _ _ (imageSubobject_comp_le h f) ≫ imageToKernel f g (
(cancel_epi h).mp (by simpa using w : h ≫ f ≫ g = h ≫ 0))
参数：h : Z ⟶ A；w。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Subobject.eq_of_comp_arrow_eq`：eq_of_comp_arrow_eq {X Y :
 C} {P : Subobject Y} {f g : X ⟶ P} (h : f ≫ P.arrow = g ≫ P.arrow) : f = g
· 使用定理 `CategoryTheory.Limits.HasImages.has_image`：∀ {C : Type u} {inst : Catego
ryTheory.Category.{v, u} C} [self : CategoryTheory.Limits.HasImages C] {X Y : C}
   (f : X ⟶ Y), CategoryTheory.…
· 使用定理 `CategoryTheory.Limits.HasKernels.has_limit`：∀ {C : Type u} {inst : Categ
oryTheory.Category.{v, u} C} {inst_1 : CategoryTheory.Limits.HasZeroMorphisms C}
   [self : CategoryTheory.Limits…
· 使用定理 `CategoryTheory.Limits.imageSubobject_comp_le`：imageSubobject_comp_le {X'
 : C} (h : X' ⟶ X) (f : X ⟶ Y) [HasImage f] [HasImage (h ≫ f)] : imageSubobject 
(h ≫ f) <= imageSubobject f
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `CategoryTheory.cancel_epi`：cancel_epi (f : X ⟶ Y) [Epi f] {g h : Y ⟶ Z} 
: f ≫ g = f ≫ h ↔ g = h
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `imageToKernel_arrow`：imageToKernel_arrow (w : f ≫ g = 0) : imageToKernel
 f g w ≫ (kernelSubobject g).arrow = (imageSubobject f).arrow
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.Subobject.ofLE_arrow`：ofLE_arrow {B : C} {X Y : Subobject
 B} (h : X <= Y) : ofLE X Y h ≫ Y.arrow = X.arrow
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem imageToKernel_epi_comp {Z : V} (h : Z ⟶ A) [Epi h] (w) :
    imageToKernel (h ≫ f) g w =
      Subobject.ofLE _ _ (imageSubobject_comp_le h f) ≫
        imageToKernel f g ((cancel_epi h).mp (by simpa using w : h ≫ f ≫ g = h ≫ 0)) := by
  ext
  simp

end

@[simp]
/-
**imageToKernel_comp_hom_inv_comp** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：imageToKernel_comp_hom_inv_comp [HasEqualizers V] [HasImages V] {Z : V} {i
 : B ≅ Z} (w) : imageToKernel (f ≫ i.hom) (i.inv ≫ g) w = (imageSubobjectCompIso
 _ _).hom ≫ imageToKernel f g (by simpa using w) ≫ (kernelSubobjectIsoComp i.inv
 g).inv
参数：w。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Subobject.eq_of_comp_arrow_eq`：eq_of_comp_arrow_eq {X Y :
 C} {P : Subobject Y} {f g : X ⟶ P} (h : f ≫ P.arrow = g ≫ P.arrow) : f = g
· 使用定理 `CategoryTheory.Limits.HasImages.has_image`：∀ {C : Type u} {inst : Catego
ryTheory.Category.{v, u} C} [self : CategoryTheory.Limits.HasImages C] {X Y : C}
   (f : X ⟶ Y), CategoryTheory.…
· 使用定理 `CategoryTheory.Iso.isIso_hom`：∀ {C : Type u} [inst : CategoryTheory.Cate
gory.{v, u} C] {X Y : C} (e : X ≅ Y), CategoryTheory.IsIso e.hom
· 使用定理 `CategoryTheory.Iso.isIso_inv`：∀ {C : Type u} [inst : CategoryTheory.Cate
gory.{v, u} C] {X Y : C} (e : X ≅ Y), CategoryTheory.IsIso e.inv
· 使用定理 `CategoryTheory.Limits.HasKernels.has_limit`：∀ {C : Type u} {inst : Categ
oryTheory.Category.{v, u} C} {inst_1 : CategoryTheory.Limits.HasZeroMorphisms C}
   [self : CategoryTheory.Limits…
· 使用定理 `CategoryTheory.Limits.hasKernels_of_hasEqualizers`：∀ (C : Type u) [inst 
: CategoryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Limits.HasZeroMorph
isms C]   [CategoryTheory.Limits.HasEqu…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `imageToKernel_arrow`：imageToKernel_arrow (w : f ≫ g = 0) : imageToKernel
 f g w ≫ (kernelSubobject g).arrow = (imageSubobject f).arrow
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.Limits.kernelSubobjectIsoComp_inv_arrow`：kernelSubobjectI
soComp_inv_arrow {X' : C} (f : X' ⟶ X) [IsIso f] (g : X ⟶ Y) [HasKernel g] : (ke
rnelSubobjectIsoComp f g).inv ≫ (kernelSubob…
· 使用定理 `CategoryTheory.IsIso.Iso.inv_inv`：∀ {C : Type u} [inst : CategoryTheory.
Category.{v, u} C] {X Y : C} (f : X ≅ Y), CategoryTheory.inv f.inv = f.hom
· 使用定理 `imageToKernel_arrow_assoc`：∀ {V : Type u} [inst : CategoryTheory.Categor
y.{v, u} V] [inst_1 : CategoryTheory.Limits.HasZeroMorphisms V] {A B C : V}   (f
 : A ⟶ B) [inst…
· 使用定理 `CategoryTheory.Limits.imageSubobjectCompIso_hom_arrow_assoc`：∀ {C : Type
 u} [inst : CategoryTheory.Category.{v, u} C] {X Y : C} [inst_1 : CategoryTheory
.Limits.HasEqualizers C]   (f : X ⟶ Y) [inst_2 : …
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CategoryTheory.IsIso.Iso.inv_hom`：∀ {C : Type u} [inst : CategoryTheory.
Category.{v, u} C] {X Y : C} (f : X ≅ Y), CategoryTheory.inv f.hom = f.inv
· 使用定理 `CategoryTheory.Iso.inv_hom_id`：∀ {C : Type u} [inst : CategoryTheory.Cat
egory.{v, u} C] {X Y : C} (self : X ≅ Y),   CategoryTheory.CategoryStruct.comp s
elf.inv self.hom = …
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem imageToKernel_comp_hom_inv_comp [HasEqualizers V] [HasImages V] {Z : V} {i : B ≅ Z} (w) :
    imageToKernel (f ≫ i.hom) (i.inv ≫ g) w =
      (imageSubobjectCompIso _ _).hom ≫
        imageToKernel f g (by simpa using w) ≫ (kernelSubobjectIsoComp i.inv g).inv := by
  ext
  simp

open ZeroObject

/-- `imageToKernel` for `A --0--> B --g--> C`, where `g` is a mono is itself an epi
(i.e. the sequence is exact at `B`).
-/
/-
**imageToKernel_epi_of_zero_of_mono** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：imageToKernel_epi_of_zero_of_mono [HasKernels V] [HasZeroObject V] [Mono g
] : Epi (imageToKernel (0 : A ⟶ B) g (by simp))
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.epi_of_target_iso_zero`：epi_of_target_iso_zero {X 
Y : C} (f : X ⟶ Y) (i : Y ≅ 0) : Epi f
· 使用定理 `CategoryTheory.Limits.HasKernels.has_limit`：∀ {C : Type u} {inst : Categ
oryTheory.Category.{v, u} C} {inst_1 : CategoryTheory.Limits.HasZeroMorphisms C}
   [self : CategoryTheory.Limits…

--- 原说明 ---
`imageToKernel` for `A --0--> B --g--> C`, where `g` is a mono is itself an epi
(i.e. the sequence is exact at `B`).
-/
instance imageToKernel_epi_of_zero_of_mono [HasKernels V] [HasZeroObject V] [Mono g] :
    Epi (imageToKernel (0 : A ⟶ B) g (by simp)) :=
  epi_of_target_iso_zero _ (kernelSubobjectIso g ≪≫ kernel.ofMono g)

/-- `imageToKernel` for `A --f--> B --0--> C`, where `g` is an epi is itself an epi
(i.e. the sequence is exact at `B`).
-/
/-
**imageToKernel_epi_of_epi_of_zero** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：imageToKernel_epi_of_epi_of_zero [HasImages V] [Epi f] : Epi (imageToKerne
l f (0 : B ⟶ C) (by simp))
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.HasImages.has_image`：∀ {C : Type u} {inst : Catego
ryTheory.Category.{v, u} C} [self : CategoryTheory.Limits.HasImages C] {X Y : C}
   (f : X ⟶ Y), CategoryTheory.…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `imageToKernel_zero_right`：imageToKernel_zero_right [HasImages V] {w} : i
mageToKernel f (0 : B ⟶ C) w = (imageSubobject f).arrow ≫ inv (kernelSubobject (
0 : B ⟶ C)).ar…
· 使用定理 `CategoryTheory.Limits.epi_image_of_epi`：epi_image_of_epi {X Y : C} (f : 
X ⟶ Y) [HasImage f] [E : Epi f] : Epi (image.ι f)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.Limits.imageSubobject_arrow`：imageSubobject_arrow : (imag
eSubobjectIso f).hom ≫ image.ι f = (imageSubobject f).arrow
· 使用定理 `CategoryTheory.StrongEpi.epi`：∀ {C : Type u} {inst : CategoryTheory.Cate
gory.{v, u} C} {P Q : C} {f : P ⟶ Q} [self : CategoryTheory.StrongEpi f],   Cate
goryTheory.Epi f
· 使用定理 `CategoryTheory.strongEpi_of_isIso`：∀ {C : Type u} [inst : CategoryTheory
.Category.{v, u} C] {P Q : C} (f : P ⟶ Q) [CategoryTheory.IsIso f],   CategoryTh
eory.StrongEpi f
· 使用定理 `CategoryTheory.Iso.isIso_hom`：∀ {C : Type u} [inst : CategoryTheory.Cate
gory.{v, u} C] {X Y : C} (e : X ≅ Y), CategoryTheory.IsIso e.hom

--- 原说明 ---
`imageToKernel` for `A --f--> B --0--> C`, where `g` is an epi is itself an epi
(i.e. the sequence is exact at `B`).
-/
instance imageToKernel_epi_of_epi_of_zero [HasImages V] [Epi f] :
    Epi (imageToKernel f (0 : B ⟶ C) (by simp)) := by
  simp only [imageToKernel_zero_right]
  have := epi_image_of_epi f
  rw [← imageSubobject_arrow]
  infer_instance

end

section imageToKernel'

/-!
We provide a variant `imageToKernel' : image f ⟶ kernel g`,
and use this to give alternative formulas for `homology f g w`.
-/

variable {A B C : V} (f : A ⟶ B) (g : B ⟶ C) (w : f ≫ g = 0) [HasKernels V] [HasImages V]

/-- While `imageToKernel f g w` provides a morphism
`imageSubobject f ⟶ kernelSubobject g`
in terms of the subobject API,
this variant provides a morphism
`image f ⟶ kernel g`,
which is sometimes more convenient.
-/
/-
**imageToKernel'** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：imageToKernel' (w : f ≫ g = 0) : image f ⟶ kernel g
参数：w : f ≫ g = 0。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.HasKernels.has_limit`：∀ {C : Type u} {inst : Categ
oryTheory.Category.{v, u} C} {inst_1 : CategoryTheory.Limits.HasZeroMorphisms C}
   [self : CategoryTheory.Limits…
· 使用定理 `CategoryTheory.Limits.HasImages.has_image`：∀ {C : Type u} {inst : Catego
ryTheory.Category.{v, u} C} [self : CategoryTheory.Limits.HasImages C] {X Y : C}
   (f : X ⟶ Y), CategoryTheory.…

--- 原说明 ---
While `imageToKernel f g w` provides a morphism
`imageSubobject f ⟶ kernelSubobject g`
in terms of the subobject API,
this variant provides a morphism
`image f ⟶ kernel g`,
which is sometimes more convenient.
-/
def imageToKernel' (w : f ≫ g = 0) : image f ⟶ kernel g :=
  kernel.lift g (image.ι f) <| by
    ext
    simpa using w

@[simp]
/-
**imageSubobjectIso_imageToKernel'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：imageSubobjectIso_imageToKernel' (w : f ≫ g = 0) : (imageSubobjectIso f).h
om ≫ imageToKernel' f g w = imageToKernel f g w ≫ (kernelSubobjectIso g).hom
参数：w : f ≫ g = 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.equalizer.hom_ext`：∀ {C : Type u} {X Y : C} [inst 
: CategoryTheory.Category.{v, u} C] {f g : X ⟶ Y}   [inst_1 : CategoryTheory.Lim
its.HasEqualizer f g] {W : C}…
· 使用定理 `CategoryTheory.Limits.HasKernels.has_limit`：∀ {C : Type u} {inst : Categ
oryTheory.Category.{v, u} C} {inst_1 : CategoryTheory.Limits.HasZeroMorphisms C}
   [self : CategoryTheory.Limits…
· 使用定理 `CategoryTheory.Limits.HasImages.has_image`：∀ {C : Type u} {inst : Catego
ryTheory.Category.{v, u} C} [self : CategoryTheory.Limits.HasImages C] {X Y : C}
   (f : X ⟶ Y), CategoryTheory.…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.Limits.kernel.lift_ι`：∀ {C : Type u} [inst : CategoryTheo
ry.Category.{v, u} C] [inst_1 : CategoryTheory.Limits.HasZeroMorphisms C] {X Y :
 C}   (f : X ⟶ Y) [inst_2…
· 使用定理 `CategoryTheory.Limits.imageSubobject_arrow`：imageSubobject_arrow : (imag
eSubobjectIso f).hom ≫ image.ι f = (imageSubobject f).arrow
· 使用定理 `CategoryTheory.Limits.kernelSubobject_arrow`：kernelSubobject_arrow : (ke
rnelSubobjectIso f).hom ≫ kernel.ι f = (kernelSubobject f).arrow
· 使用定理 `imageToKernel_arrow`：imageToKernel_arrow (w : f ≫ g = 0) : imageToKernel
 f g w ≫ (kernelSubobject g).arrow = (imageSubobject f).arrow
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem imageSubobjectIso_imageToKernel' (w : f ≫ g = 0) :
    (imageSubobjectIso f).hom ≫ imageToKernel' f g w =
      imageToKernel f g w ≫ (kernelSubobjectIso g).hom := by
  ext
  simp [imageToKernel']

@[simp]
/-
**imageToKernel'_kernelSubobjectIso** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {V : Type u} [inst : CategoryTheory.Category.{v, u} V] [inst_1 : Categor
yTheory.Limits.HasZeroMorphisms V] {A B C : V}   (f : A ⟶ B) (g : B ⟶ C) [inst_2
 : CategoryTheory.Limits.HasKernels V] [inst_3 : CategoryTheory.Limits.HasImages
 V]   (w : CategoryTheory.CategoryStruct.comp f g = 0),   CategoryTheory.Categor
yStruct.comp (imageToKernel' f g w) (CategoryTheory.Limits.kernelSubobjectIso g)
.inv =     CategoryTheory.CategoryStruct.comp (CategoryTheory.Limits.imageSubobj
ectIso f).inv (imageToKernel f g w)
参数：f : A ⟶ B；g : B ⟶ C；w : CategoryTheory.CategoryStruct.comp f g = 0；imageToKer
nel' f g w；CategoryTheory.Limits.kernelSubobjectIso g；CategoryTheory.Limits.imag
eSubobjectIso f；imageToKernel f g w。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Subobject.eq_of_comp_arrow_eq`：eq_of_comp_arrow_eq {X Y :
 C} {P : Subobject Y} {f g : X ⟶ P} (h : f ≫ P.arrow = g ≫ P.arrow) : f = g
· 使用定理 `CategoryTheory.Limits.HasImages.has_image`：∀ {C : Type u} {inst : Catego
ryTheory.Category.{v, u} C} [self : CategoryTheory.Limits.HasImages C] {X Y : C}
   (f : X ⟶ Y), CategoryTheory.…
· 使用定理 `CategoryTheory.Limits.HasKernels.has_limit`：∀ {C : Type u} {inst : Categ
oryTheory.Category.{v, u} C} {inst_1 : CategoryTheory.Limits.HasZeroMorphisms C}
   [self : CategoryTheory.Limits…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.Limits.kernelSubobject_arrow'`：kernelSubobject_arrow' : (
kernelSubobjectIso f).inv ≫ (kernelSubobject f).arrow = kernel.ι f
· 使用定理 `CategoryTheory.Limits.kernel.lift_ι`：∀ {C : Type u} [inst : CategoryTheo
ry.Category.{v, u} C] [inst_1 : CategoryTheory.Limits.HasZeroMorphisms C] {X Y :
 C}   (f : X ⟶ Y) [inst_2…
· 使用定理 `imageToKernel_arrow`：imageToKernel_arrow (w : f ≫ g = 0) : imageToKernel
 f g w ≫ (kernelSubobject g).arrow = (imageSubobject f).arrow
· 使用定理 `CategoryTheory.Limits.imageSubobject_arrow'`：imageSubobject_arrow' : (im
ageSubobjectIso f).inv ≫ (imageSubobject f).arrow = image.ι f
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem imageToKernel'_kernelSubobjectIso (w : f ≫ g = 0) :
    imageToKernel' f g w ≫ (kernelSubobjectIso g).inv =
      (imageSubobjectIso f).inv ≫ imageToKernel f g w := by
  ext
  simp [imageToKernel']

end imageToKernel'

end

