/-
Copyright (c) 2025 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan
-/
module

public import Mathlib.Algebra.Category.Grp.Zero
public import Mathlib.Algebra.FiveLemma
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.EnoughInjectives
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.EnoughProjectives
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.Map
public import Mathlib.CategoryTheory.Preadditive.Injective.Preserves
public import Mathlib.CategoryTheory.Preadditive.Projective.Preserves

/-!

# Bijections Between Ext

In this file, we show that the maps between `Ext` induced
by a fully faithful exact functor `F : C ⥤ D` are bijective when either
1. `F` preserves projective objects and `C` has enough projectives, or
2. `F` preserves injective objects and `C` has enough injectives.

-/

public section

universe w w' v v' u u'

namespace CategoryTheory

open Limits Abelian

variable {C : Type u} [Category.{v} C] [Abelian C]
variable {D : Type u'} [Category.{v'} D] [Abelian D]

variable (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]

attribute [local simp] Ext.mapExactFunctor_comp Ext.mapExactFunctor_mk₀ Ext.mapExactFunctor_extClass

attribute [local instance] Ext.subsingleton_of_projective in
/-
**CategoryTheory.Functor.mapExt_bijective_of_preservesProjectiveObjects** 是 Math
lib 中的一个定理，位于命名空间 `CategoryTheory.Functor`。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] [inst_1 : Categor
yTheory.Abelian C] {D : Type u'}   [inst_2 : CategoryTheory.Category.{v', u'} D]
 [inst_3 : CategoryTheory.Abelian D] (F : CategoryTheory.Functor C D)   [inst_4 
: F.Additive] [inst_5 : CategoryTheory.Limits.PreservesFiniteLimits F]   [inst_6
 : CategoryTheory.Limits.PreservesFiniteColimits F] [F.Full] [F.Faithful] [inst_
9 : CategoryTheory.HasExt C]   [inst_10 : CategoryTheory.HasExt D] [CategoryTheo
ry.EnoughProjectives C] [F.PreservesProjectiveObjects] (X Y : C)   (n : ℕ), Func
tion.Bijective ⇑(F.mapExtAddHom X Y n)
参数：F : CategoryTheory.Functor C D；X Y : C；n : ℕ；F.mapExtAddHom X Y n。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `CategoryTheory.Abelian.Ext.mapExactFunctor₀`：mapExactFunctor₀ [HasExt.{w
} C] [HasExt.{w'} D] (X Y : C) : Ext.mapExactFunctor F (X
· 使用定理 `CategoryTheory.Functor.Faithful.map_injective`：∀ {C : Type u₁} {inst : C
ategoryTheory.Category.{v₁, u₁} C} {D : Type u₂} {inst_1 : CategoryTheory.Catego
ry.{v₂, u₂} D}   {F : CategoryTheor…
· 使用定理 `CategoryTheory.Functor.Full.map_surjective`：∀ {C : Type u₁} {inst : Cate
goryTheory.Category.{v₁, u₁} C} {D : Type u₂} {inst_1 : CategoryTheory.Category.
{v₂, u₂} D}   {F : CategoryTheor…
· 使用定理 `CategoryTheory.EnoughProjectives.presentation`：∀ {C : Type u} {inst : Ca
tegoryTheory.Category.{v, u} C} [self : CategoryTheory.EnoughProjectives C] (X :
 C),   Nonempty (CategoryTheory.Pro…
· 使用定理 `CategoryTheory.Limits.HasKernels.has_limit`：∀ {C : Type u} {inst : Categ
oryTheory.Category.{v, u} C} {inst_1 : CategoryTheory.Limits.HasZeroMorphisms C}
   [self : CategoryTheory.Limits…
· 使用定理 `CategoryTheory.Abelian.has_kernels`：∀ {C : Type u} {inst : CategoryTheor
y.Category.{v, u} C} [self : CategoryTheory.Abelian C],   CategoryTheory.Limits.
HasKernels C
· 使用定理 `CategoryTheory.Limits.kernel.condition`：∀ {C : Type u} [inst : CategoryT
heory.Category.{v, u} C] [inst_1 : CategoryTheory.Limits.HasZeroMorphisms C] {X 
Y : C}   (f : X ⟶ Y) [inst_2…
· 使用定理 `CategoryTheory.Functor.preservesZeroMorphisms_of_additive`：∀ {C : Type u
_1} {D : Type u_2} [inst : CategoryTheory.Category.{v_1, u_1} C]   [inst_1 : Cat
egoryTheory.Category.{v_2, u_2} D] [inst_2 : Ca…
· 使用定理 `CategoryTheory.Functor.PreservesProjectiveObjects.projective_obj`：∀ {C :
 Type u₁} {inst : CategoryTheory.Category.{v₁, u₁} C} {D : Type u₂} {inst_1 : Ca
tegoryTheory.Category.{v₂, u₂} D}   {F : CategoryTheor…
· 使用定理 `CategoryTheory.ProjectivePresentation.projective`：∀ {C : Type u} [inst :
 CategoryTheory.Category.{v, u} C] {X : C} (self : CategoryTheory.ProjectivePres
entation X),   CategoryTheory.Projecti…
· 使用定理 `CategoryTheory.ShortComplex.exact_kernel`：exact_kernel {X Y : C} (f : X 
⟶ Y) : (ShortComplex.mk (kernel.ι f) f (by simp)).Exact
· 使用定理 `CategoryTheory.Limits.equalizer.ι_mono`：∀ {C : Type u} {X Y : C} [inst :
 CategoryTheory.Category.{v, u} C] {f g : X ⟶ Y}   [inst_1 : CategoryTheory.Limi
ts.HasEqualizer f g], Catego…
· 使用定理 `CategoryTheory.ProjectivePresentation.epi`：∀ {C : Type u} [inst : Catego
ryTheory.Category.{v, u} C] {X : C} (self : CategoryTheory.ProjectivePresentatio
n X),   CategoryTheory.Epi self…
· 使用定理 `AddMonoidHom.bijective_of_surjective_of_bijective_of_right_exact`：∀ {M₁ 
: Type u_1} {M₂ : Type u_2} {M₃ : Type u_3} {N₁ : Type u_6} {N₂ : Type u_7} {N₃ 
: Type u_8} [inst : AddGroup M₁]   [inst_1 : AddGroup …
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
· 使用定理 `CategoryTheory.ShortComplex.ShortExact.map`：∀ {C : Type u_1} {D : Type u
_2} [inst : CategoryTheory.Category.{v_1, u_1} C]   [inst_1 : CategoryTheory.Cat
egory.{v_2, u_2} D] [inst_2 : Ca…
· 使用定理 `CategoryTheory.Functor.PreservesHomology.preservesLeftHomologyOf`：∀ {C :
 Type u_1} {D : Type u_2} [inst : CategoryTheory.Category.{v_1, u_1} C]   [inst_
1 : CategoryTheory.Category.{v_2, u_2} D] [inst_2 : Ca…
· 使用定理 `CategoryTheory.Functor.preservesHomologyOfExact`：∀ {C : Type u_1} {D : T
ype u_2} [inst : CategoryTheory.Category.{v_1, u_1} C]   [inst_1 : CategoryTheor
y.Category.{v_2, u_2} D] [inst_2 : Ca…
· 使用定理 `CategoryTheory.Functor.PreservesHomology.preservesRightHomologyOf`：∀ {C 
: Type u_1} {D : Type u_2} [inst : CategoryTheory.Category.{v_1, u_1} C]   [inst
_1 : CategoryTheory.Category.{v_2, u_2} D] [inst_2 : Ca…
· 使用定理 `CategoryTheory.Functor.map_mono`：∀ {C : Type u₁} [inst : CategoryTheory.
Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]
   (F : CategoryTheor…
· 使用定理 `CategoryTheory.Functor.instPreservesMonomorphisms`：∀ {C : Type u_1} {D :
 Type u_2} [inst : CategoryTheory.Category.{v_1, u_1} C]   [inst_1 : CategoryThe
ory.Category.{v_2, u_2} D] (F : Categor…
· 使用定理 `CategoryTheory.Abelian.hasZeroObject`：∀ {C : Type u} [inst : CategoryThe
ory.Category.{v, u} C] [CategoryTheory.Abelian C],   CategoryTheory.Limits.HasZe
roObject C
· 使用定理 `CategoryTheory.Functor.instPreservesEpimorphisms`：∀ {C : Type u_1} {D : 
Type u_2} [inst : CategoryTheory.Category.{v_1, u_1} C]   [inst_1 : CategoryTheo
ry.Category.{v_2, u_2} D] (F : Categor…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CategoryTheory.Abelian.Ext.precomp.congr_simp`：∀ {C : Type u} [inst : Ca
tegoryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Abelian C]   [inst_2 : 
CategoryTheory.HasExt C] {X Y : C} …
（共 47 条，此处仅展示前 30 条）
-/
lemma Functor.mapExt_bijective_of_preservesProjectiveObjects [F.Full] [F.Faithful] [HasExt.{w} C]
    [HasExt.{w'} D] [EnoughProjectives C] [F.PreservesProjectiveObjects] (X Y : C) (n : ℕ) :
    Function.Bijective (F.mapExtAddHom X Y n) := by
  induction n generalizing X with
  | zero => simpa [Ext.mapExactFunctor₀] using ⟨Faithful.map_injective, Full.map_surjective⟩
  | succ n hn =>
    let P : ProjectivePresentation X := Classical.arbitrary _
    let S := ShortComplex.mk _ _ (kernel.condition P.f)
    have : Projective (S.map F).X₂ := Functor.PreservesProjectiveObjects.projective_obj P.projective
    have hS : S.ShortExact := { exact := ShortComplex.exact_kernel P.f }
    exact AddMonoidHom.bijective_of_surjective_of_bijective_of_right_exact _ _ _ _
      (F.mapExtAddHom S.X₂ Y n) (F.mapExtAddHom S.X₁ Y n) (F.mapExtAddHom S.X₃ Y (n + 1))
      (by cat_disch) (by cat_disch)
      ((ShortComplex.ab_exact_iff_function_exact _).1
        (Ext.contravariant_sequence_exact₁' hS Y n (n + 1) (add_comm 1 n)))
      ((ShortComplex.ab_exact_iff_function_exact _).1
        (Ext.contravariant_sequence_exact₁' (hS.map F) (F.obj Y) n (n + 1) (add_comm 1 n)))
      (hn _).surjective (hn _)
      (fun x₃ ↦ Ext.contravariant_sequence_exact₃ hS _ x₃ (by subsingleton) (add_comm 1 n))
      (fun y₃ ↦ Ext.contravariant_sequence_exact₃ (hS.map F) _ y₃ (by subsingleton) (add_comm 1 n))

attribute [local instance] Ext.subsingleton_of_injective in
/-
**CategoryTheory.Functor.mapExt_bijective_of_preservesInjectiveObjects** 是 Mathl
ib 中的一个定理，位于命名空间 `CategoryTheory.Functor`。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] [inst_1 : Categor
yTheory.Abelian C] {D : Type u'}   [inst_2 : CategoryTheory.Category.{v', u'} D]
 [inst_3 : CategoryTheory.Abelian D] (F : CategoryTheory.Functor C D)   [inst_4 
: F.Additive] [inst_5 : CategoryTheory.Limits.PreservesFiniteLimits F]   [inst_6
 : CategoryTheory.Limits.PreservesFiniteColimits F] [F.Full] [F.Faithful] [inst_
9 : CategoryTheory.HasExt C]   [inst_10 : CategoryTheory.HasExt D] [CategoryTheo
ry.EnoughInjectives C] [F.PreservesInjectiveObjects] (X Y : C)   (n : ℕ), Functi
on.Bijective ⇑(F.mapExtAddHom X Y n)
参数：F : CategoryTheory.Functor C D；X Y : C；n : ℕ；F.mapExtAddHom X Y n。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `CategoryTheory.Abelian.Ext.mapExactFunctor₀`：mapExactFunctor₀ [HasExt.{w
} C] [HasExt.{w'} D] (X Y : C) : Ext.mapExactFunctor F (X
· 使用定理 `CategoryTheory.Functor.Faithful.map_injective`：∀ {C : Type u₁} {inst : C
ategoryTheory.Category.{v₁, u₁} C} {D : Type u₂} {inst_1 : CategoryTheory.Catego
ry.{v₂, u₂} D}   {F : CategoryTheor…
· 使用定理 `CategoryTheory.Functor.Full.map_surjective`：∀ {C : Type u₁} {inst : Cate
goryTheory.Category.{v₁, u₁} C} {D : Type u₂} {inst_1 : CategoryTheory.Category.
{v₂, u₂} D}   {F : CategoryTheor…
· 使用定理 `CategoryTheory.EnoughInjectives.presentation`：∀ {C : Type u₁} {inst : Ca
tegoryTheory.Category.{v₁, u₁} C} [self : CategoryTheory.EnoughInjectives C] (X 
: C),   Nonempty (CategoryTheory.I…
· 使用定理 `CategoryTheory.Limits.HasCokernels.has_colimit`：∀ {C : Type u} {inst : C
ategoryTheory.Category.{v, u} C} {inst_1 : CategoryTheory.Limits.HasZeroMorphism
s C}   [self : CategoryTheory.Limits…
· 使用定理 `CategoryTheory.Abelian.has_cokernels`：∀ {C : Type u} {inst : CategoryThe
ory.Category.{v, u} C} [self : CategoryTheory.Abelian C],   CategoryTheory.Limit
s.HasCokernels C
· 使用定理 `CategoryTheory.Limits.cokernel.condition`：∀ {C : Type u} [inst : Categor
yTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Limits.HasZeroMorphisms C] {
X Y : C}   (f : X ⟶ Y) [inst_2…
· 使用定理 `CategoryTheory.Functor.preservesZeroMorphisms_of_additive`：∀ {C : Type u
_1} {D : Type u_2} [inst : CategoryTheory.Category.{v_1, u_1} C]   [inst_1 : Cat
egoryTheory.Category.{v_2, u_2} D] [inst_2 : Ca…
· 使用定理 `CategoryTheory.Functor.PreservesInjectiveObjects.injective_obj`：∀ {C : T
ype u₁} {inst : CategoryTheory.Category.{v₁, u₁} C} {D : Type u₂} {inst_1 : Cate
goryTheory.Category.{v₂, u₂} D}   {F : CategoryTheor…
· 使用定理 `CategoryTheory.InjectivePresentation.injective`：∀ {C : Type u₁} [inst : 
CategoryTheory.Category.{v₁, u₁} C] {X : C} (self : CategoryTheory.InjectivePres
entation X),   CategoryTheory.Inject…
· 使用定理 `CategoryTheory.ShortComplex.exact_cokernel`：exact_cokernel {X Y : C} (f 
: X ⟶ Y) : (ShortComplex.mk f (cokernel.π f) (by simp)).Exact
· 使用定理 `CategoryTheory.InjectivePresentation.mono`：∀ {C : Type u₁} [inst : Categ
oryTheory.Category.{v₁, u₁} C] {X : C} (self : CategoryTheory.InjectivePresentat
ion X),   CategoryTheory.Mono s…
· 使用定理 `CategoryTheory.Limits.coequalizer.π_epi`：∀ {C : Type u} {X Y : C} [inst 
: CategoryTheory.Category.{v, u} C] {f g : X ⟶ Y}   [inst_1 : CategoryTheory.Lim
its.HasCoequalizer f g], Cate…
· 使用定理 `AddMonoidHom.bijective_of_surjective_of_bijective_of_right_exact`：∀ {M₁ 
: Type u_1} {M₂ : Type u_2} {M₃ : Type u_3} {N₁ : Type u_6} {N₂ : Type u_7} {N₃ 
: Type u_8} [inst : AddGroup M₁]   [inst_1 : AddGroup …
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `CategoryTheory.ShortComplex.ShortExact.map`：∀ {C : Type u_1} {D : Type u
_2} [inst : CategoryTheory.Category.{v_1, u_1} C]   [inst_1 : CategoryTheory.Cat
egory.{v_2, u_2} D] [inst_2 : Ca…
· 使用定理 `CategoryTheory.Functor.PreservesHomology.preservesLeftHomologyOf`：∀ {C :
 Type u_1} {D : Type u_2} [inst : CategoryTheory.Category.{v_1, u_1} C]   [inst_
1 : CategoryTheory.Category.{v_2, u_2} D] [inst_2 : Ca…
· 使用定理 `CategoryTheory.Functor.preservesHomologyOfExact`：∀ {C : Type u_1} {D : T
ype u_2} [inst : CategoryTheory.Category.{v_1, u_1} C]   [inst_1 : CategoryTheor
y.Category.{v_2, u_2} D] [inst_2 : Ca…
· 使用定理 `CategoryTheory.Functor.PreservesHomology.preservesRightHomologyOf`：∀ {C 
: Type u_1} {D : Type u_2} [inst : CategoryTheory.Category.{v_1, u_1} C]   [inst
_1 : CategoryTheory.Category.{v_2, u_2} D] [inst_2 : Ca…
· 使用定理 `CategoryTheory.Functor.map_mono`：∀ {C : Type u₁} [inst : CategoryTheory.
Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]
   (F : CategoryTheor…
· 使用定理 `CategoryTheory.Functor.instPreservesMonomorphisms`：∀ {C : Type u_1} {D :
 Type u_2} [inst : CategoryTheory.Category.{v_1, u_1} C]   [inst_1 : CategoryThe
ory.Category.{v_2, u_2} D] (F : Categor…
· 使用定理 `CategoryTheory.Abelian.hasZeroObject`：∀ {C : Type u} [inst : CategoryThe
ory.Category.{v, u} C] [CategoryTheory.Abelian C],   CategoryTheory.Limits.HasZe
roObject C
· 使用定理 `CategoryTheory.Limits.instHasColimitOfHasColimitsOfShape`：∀ {C : Type u}
 [inst : CategoryTheory.Category.{v, u} C] {J : Type u₁} [inst_1 : CategoryTheor
y.Category.{v₁, u₁} J]   [CategoryTheory.Limit…
· 使用定理 `CategoryTheory.Abelian.hasCoequalizers`：∀ {C : Type u} [inst : CategoryT
heory.Category.{v, u} C] [CategoryTheory.Abelian C],   CategoryTheory.Limits.Has
Coequalizers C
· 使用定理 `CategoryTheory.Limits.PreservesColimitsOfShape.preservesColimit`：∀ {C : 
Type u₁} {inst : CategoryTheory.Category.{v₁, u₁} C} {D : Type u₂} {inst_1 : Cat
egoryTheory.Category.{v₂, u₂} D}   {J : Type w} {inst…
· 使用定理 `CategoryTheory.Limits.PreservesFiniteColimits.preservesFiniteColimits`：∀
 {C : Type u₁} {inst : CategoryTheory.Category.{v₁, u₁} C} {D : Type u₂} {inst_1
 : CategoryTheory.Category.{v₂, u₂} D}   {F : CategoryTheor…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
（共 49 条，此处仅展示前 30 条）
-/
lemma Functor.mapExt_bijective_of_preservesInjectiveObjects [F.Full] [F.Faithful] [HasExt.{w} C]
    [HasExt.{w'} D] [EnoughInjectives C] [F.PreservesInjectiveObjects] (X Y : C) (n : ℕ) :
    Function.Bijective (F.mapExtAddHom X Y n) := by
  induction n generalizing Y with
  | zero => simpa [Ext.mapExactFunctor₀] using ⟨Faithful.map_injective, Full.map_surjective⟩
  | succ n hn =>
    let I : InjectivePresentation Y := Classical.arbitrary _
    let S := ShortComplex.mk _ _ (cokernel.condition I.f)
    have : Injective (S.map F).X₂ := Functor.PreservesInjectiveObjects.injective_obj I.injective
    have hS : S.ShortExact := { exact := ShortComplex.exact_cokernel I.f }
    exact AddMonoidHom.bijective_of_surjective_of_bijective_of_right_exact _ _ _ _
      (F.mapExtAddHom X S.X₂ n) (F.mapExtAddHom X S.X₃ n) (F.mapExtAddHom X S.X₁ (n + 1))
      (by cat_disch) (by cat_disch)
      ((ShortComplex.ab_exact_iff_function_exact _).mp
        (Ext.covariant_sequence_exact₃' X hS n (n + 1) rfl))
      ((ShortComplex.ab_exact_iff_function_exact _).mp
        (Ext.covariant_sequence_exact₃' (F.obj X) (hS.map F) n (n + 1) rfl))
      (hn _).surjective (hn _)
      (fun x₁ ↦ Ext.covariant_sequence_exact₁ _ hS x₁ (by subsingleton) rfl)
      (fun y₁ ↦ Ext.covariant_sequence_exact₁ _ (hS.map F) y₁ (by subsingleton) rfl)

end CategoryTheory

