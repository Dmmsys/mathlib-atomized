/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.CategoryTheory.Comma.StructuredArrow.Basic
public import Mathlib.CategoryTheory.Comma.Over.Basic
public import Mathlib.CategoryTheory.EssentiallySmall

/-!
# Comma categories are locally small

We introduce instances showing that the various comma categories
are locally small when the relevant categories that are
involved are locally small.

-/

public section

universe w v₁ v₂ v₃ u₁ u₂ u₃

namespace CategoryTheory

variable {A : Type u₁} {B : Type u₂} {T : Type u₃}
  [Category.{v₁} A] [Category.{v₂} B] [Category.{v₃} T]

/-
**CategoryTheory.Comma.locallySmall** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.Co
mma`。
形式化陈述：∀ {A : Type u₁} {B : Type u₂} {T : Type u₃} [inst : CategoryTheory.Categor
y.{v₁, u₁} A]   [inst_1 : CategoryTheory.Category.{v₂, u₂} B] [inst_2 : Category
Theory.Category.{v₃, u₃} T]   (L : CategoryTheory.Functor A T) (R : CategoryTheo
ry.Functor B T) [CategoryTheory.LocallySmall.{w, v₁, u₁} A]   [CategoryTheory.Lo
callySmall.{w, v₂, u₂} B],   CategoryTheory.LocallySmall.{w, max v₁ v₂, max (max
 u₂ u₁) v₃} (CategoryTheory.Comma L R)
参数：L : CategoryTheory.Functor A T；R : CategoryTheory.Functor B T；max u₂ u₁；Categ
oryTheory.Comma L R。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `small_of_injective`：small_of_injective {α : Type v} {β : Type w} [Small.
{u} β] {f : α -> β} (hf : Function.Injective f) : Small.{u} α
· 使用定理 `CategoryTheory.instSmallHomOfLocallySmall`：∀ (C : Type u) [inst : Catego
ryTheory.Category.{v, u} C] [CategoryTheory.LocallySmall.{w, v, u} C] (X Y : C),
   Small.{w, v} (X ⟶ Y)
· 使用定理 `Prod.mk.injEq`：∀ {α : Type u} {β : Type v} (fst : α) (snd : β) (fst_1 : 
α) (snd_1 : β),   ((fst, snd) = (fst_1, snd_1)) = (fst = fst_1 ∧ snd = snd_1)
· 使用引理 `CategoryTheory.Comma.hom_ext`：hom_ext (f g : X ⟶ Y) (h₁ : f.left = g.lef
t) (h₂ : f.right = g.right) : f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
instance Comma.locallySmall
    (L : A ⥤ T) (R : B ⥤ T) [LocallySmall.{w} A] [LocallySmall.{w} B] :
    LocallySmall.{w} (Comma L R) where
  hom_small X Y := small_of_injective.{w}
      (f := fun g ↦ (⟨g.left, g.right⟩ : _ × _))
        (fun _ _ _ ↦ by aesop)
/-
**CategoryTheory.StructuredArrow.locallySmall** 是 Mathlib 中的一个定理，位于命名空间 `Categor
yTheory.StructuredArrow`。
形式化陈述：∀ {B : Type u₂} {T : Type u₃} [inst : CategoryTheory.Category.{v₂, u₂} B] 
[inst_1 : CategoryTheory.Category.{v₃, u₃} T]   (S : T) (T_1 : CategoryTheory.Fu
nctor B T) [CategoryTheory.LocallySmall.{w, v₂, u₂} B],   CategoryTheory.Locally
Small.{w, v₂, max u₂ v₃} (CategoryTheory.StructuredArrow S T_1)
参数：S : T；T_1 : CategoryTheory.Functor B T；CategoryTheory.StructuredArrow S T_1。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Comma.locallySmall`：∀ {A : Type u₁} {B : Type u₂} {T : Ty
pe u₃} [inst : CategoryTheory.Category.{v₁, u₁} A]   [inst_1 : CategoryTheory.Ca
tegory.{v₂, u₂} B] [ins…
· 使用定理 `CategoryTheory.locallySmall_of_thin`：∀ {C : Type u} [inst : CategoryTheo
ry.Category.{v, u} C] [Quiver.IsThin C], CategoryTheory.LocallySmall.{w, v, u} C
-/
instance StructuredArrow.locallySmall (S : T) (T : B ⥤ T)
    [LocallySmall.{w} B] :
    LocallySmall.{w} (StructuredArrow S T) :=
  Comma.locallySmall _ _
/-
**CategoryTheory.CostructuredArrow.locallySmall** 是 Mathlib 中的一个定理，位于命名空间 `Categ
oryTheory.CostructuredArrow`。
形式化陈述：∀ {A : Type u₁} {T : Type u₃} [inst : CategoryTheory.Category.{v₁, u₁} A] 
[inst_1 : CategoryTheory.Category.{v₃, u₃} T]   (S : CategoryTheory.Functor A T)
 (X : T) [CategoryTheory.LocallySmall.{w, v₁, u₁} A],   CategoryTheory.LocallySm
all.{w, v₁, max u₁ v₃} (CategoryTheory.CostructuredArrow S X)
参数：S : CategoryTheory.Functor A T；X : T；CategoryTheory.CostructuredArrow S X。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Comma.locallySmall`：∀ {A : Type u₁} {B : Type u₂} {T : Ty
pe u₃} [inst : CategoryTheory.Category.{v₁, u₁} A]   [inst_1 : CategoryTheory.Ca
tegory.{v₂, u₂} B] [ins…
· 使用定理 `CategoryTheory.locallySmall_of_thin`：∀ {C : Type u} [inst : CategoryTheo
ry.Category.{v, u} C] [Quiver.IsThin C], CategoryTheory.LocallySmall.{w, v, u} C
-/
instance CostructuredArrow.locallySmall (S : A ⥤ T) (X : T)
    [LocallySmall.{w} A] :
    LocallySmall.{w} (CostructuredArrow S X) :=
  Comma.locallySmall _ _
/-
**CategoryTheory.Over.locallySmall** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.Ove
r`。
形式化陈述：∀ {T : Type u₃} [inst : CategoryTheory.Category.{v₃, u₃} T] (X : T) [Categ
oryTheory.LocallySmall.{w, v₃, u₃} T],   CategoryTheory.LocallySmall.{w, v₃, max
 u₃ v₃} (CategoryTheory.Over X)
参数：X : T；CategoryTheory.Over X。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.CostructuredArrow.locallySmall`：∀ {A : Type u₁} {T : Type
 u₃} [inst : CategoryTheory.Category.{v₁, u₁} A] [inst_1 : CategoryTheory.Catego
ry.{v₃, u₃} T]   (S : CategoryTheor…
-/
instance Over.locallySmall (X : T) [LocallySmall.{w} T] :
    LocallySmall.{w} (Over X) :=
  CostructuredArrow.locallySmall _ _
/-
**CategoryTheory.Under.locallySmall** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.Un
der`。
形式化陈述：∀ {T : Type u₃} [inst : CategoryTheory.Category.{v₃, u₃} T] (X : T) [Categ
oryTheory.LocallySmall.{w, v₃, u₃} T],   CategoryTheory.LocallySmall.{w, v₃, max
 u₃ v₃} (CategoryTheory.Under X)
参数：X : T；CategoryTheory.Under X。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.StructuredArrow.locallySmall`：∀ {B : Type u₂} {T : Type u
₃} [inst : CategoryTheory.Category.{v₂, u₂} B] [inst_1 : CategoryTheory.Category
.{v₃, u₃} T]   (S : T) (T_1 : Cat…
-/
instance Under.locallySmall (X : T) [LocallySmall.{w} T] :
    LocallySmall.{w} (Under X) :=
  StructuredArrow.locallySmall _ _

end CategoryTheory

